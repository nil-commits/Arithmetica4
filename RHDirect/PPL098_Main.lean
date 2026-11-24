/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# PPL 098 (Erdős Problem #66): Additive Representation Functions, Erdős–Fuchs (1956), and Quantitative Erdős–Sárközy Impossibility

## Honest Scope Statement
**Erdős Problem #66** (`erdosproblems.com/66`, `prizeproblems.org`, $500, proposed by Paul Erdős
in 1956) asks whether there exists a subset `A ⊆ ℕ` such that
`lim_{n → ∞} (1_A * 1_A)(n) / log n` exists and is `≠ 0`, where
`(1_A * 1_A)(n) = #{(a, b) ∈ A × A : a + b = n} = ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card`.

Erdős Problem #66 **remains OPEN** (see `scripts/ppl098_findings.md`). This module does **NOT**
claim to prove or refute the full open conjecture. Instead, it provides a **100% unconditional,
kernel-verified, pure-Mathlib-signature formalization** of:

1. **Exact Combinatorial Identities & Necessary Density Profile for Any Erdős #66 Witness:**
   - `ppl098_sum_rep_sandwich`: `|A ∩ [0, ⌊N/2⌋]|² ≤ ∑_{n ≤ N} r_A(n) ≤ |A ∩ [0, N]|²`.
   - `ppl098_rep_sum_sq_cauchy_schwarz`: Additive energy lower bound
     `|A ∩ [0, ⌊N/2⌋]|⁴ ≤ (∑_{n ≤ N} r_A(n))² ≤ (N + 1) ∑_{n ≤ N} r_A(n)²`.
   - `ppl098_erdos66_cesaro_asymptotic`: If `r_A(n) / log n → c > 0`, then
     `(∑_{n ≤ N} r_A(n)) / (N log N) → c`.
   - `ppl098_erdos66_density_profile` & `ppl098_erdos66_infinite_and_zero_density`: Any Erdős #66
     witness must be infinite, have natural density `0`, and satisfy
     `√c - ε ≤ |A ∩ [0, N]| / √(N log N) ≤ √(2c) + ε` for all sufficiently large `N`.
2. **Reusable Radial Parseval & Triangle-Bump Positivity Engine on the Unit Disk:**
   - `ppl098_radial_parseval`: For any `c : ℕ → ℂ` with `∑' n, ‖c n‖ < ∞`,
     `∫ θ in (-π)..π, ‖∑' n, c n * exp (I * n * θ)‖² = (2 * π) * ∑' n, ‖c n‖²`.
   - `ppl098_triangle_bump_positivity`: For any nonnegative `w : ℕ → ℝ` with `Summable w` and
     `α ∈ (0, π]`, `∫ θ in (-α)..α, ‖∑' n, (w n : ℂ) * exp (I * n * θ)‖² ≥ α * ∑' n, (w n)²`.
3. **The Erdős–Fuchs Theorem (1956):**
   - `ppl098_erdos_fuchs_1956`: For every `A ⊆ ℕ` and `c > 0`,
     `∑_{n ≤ N} r_A(n) = c N + o(N^{1/4} / √(log N))` is impossible.
   - `ppl098_no_eventually_constant_rep`: No `A ⊆ ℕ` has eventually constant `r_A(n) = c > 0`.
4. **Quantitative Erdős–Sárközy Impossibility Barrier for Erdős Problem #66:**
   - `ppl098_erdos_sarkozy_log_quantitative`: For every `A ⊆ ℕ`, `c > 0`, and `η < 1 / √2`,
     it is impossible that eventually `|r_A(n) - c log n| ≤ η √(c log n)`.
   - `ppl098_erdos_sarkozy_log_impossibility`: For every `A ⊆ ℕ` and `c > 0`,
     `|r_A(n) - c log n| = o(√(log n))` is impossible.

Every public theorem signature uses **zero custom or private definitions** (100% native Mathlib).
-/

open Finset BigOperators Filter Topology Real Complex MeasureTheory intervalIntegral

namespace PPL098

noncomputable section

/-! ## Part I: Exact Counting Identities, Additive Energy, and Erdős #66 Density Profile -/

/-- **Exact Counting Sandwich for Additive Representations**:
For every subset `A ⊆ ℕ` and every `N : ℕ`,
`|A ∩ [0, ⌊N/2⌋]|² ≤ ∑_{n=0}^{N} (1_A * 1_A)(n) ≤ |A ∩ [0, N]|²`. -/
theorem ppl098_sum_rep_sandwich (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    ((Finset.range (N / 2 + 1)).filter (· ∈ A)).card ^ 2
      ≤ ∑ n ∈ Finset.range (N + 1),
          ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card
    ∧ ∑ n ∈ Finset.range (N + 1),
          ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card
      ≤ ((Finset.range (N + 1)).filter (· ∈ A)).card ^ 2 := by
  let S := ((Finset.range (N + 1)).filter (· ∈ A))
  let P := (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ N)
  have hsum_eq_P :
      (∑ n ∈ Finset.range (N + 1),
        ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card) = P.card := by
    have hcard_fiber : ∀ n ∈ Finset.range (N + 1),
        ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card =
        (P.filter (fun p => p.1 + p.2 = n)).card := by
      intro n hn
      rw [Finset.mem_range] at hn
      refine Finset.card_bij (fun a _ => (a, n - a)) ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_range] at ha
        rw [Finset.mem_filter]
        refine ⟨?_, by omega⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, by omega⟩
        · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, ha.2.1⟩
        · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, ha.2.2⟩
      · intro a₁ _ a₂ _ h
        exact congrArg Prod.fst h
      · intro p hp
        rw [Finset.mem_filter] at hp
        rcases hp with ⟨hpP, hsum⟩
        rw [Finset.mem_filter, Finset.mem_product] at hpP
        rcases hpP with ⟨⟨hp1, hp2⟩, _⟩
        rw [Finset.mem_filter] at hp1 hp2
        refine ⟨p.1, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, hp1.2, ?_⟩
          have hsub : n - p.1 = p.2 := by omega
          rw [hsub]; exact hp2.2
        · ext
          · dsimp
          · dsimp; omega
    rw [Finset.sum_congr rfl hcard_fiber]
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨n, _, hpP, _⟩; exact hpP
      · intro hpP
        have hle : p.1 + p.2 ≤ N := (Finset.mem_filter.1 hpP).2
        exact ⟨p.1 + p.2, by omega, hpP, rfl⟩
    · intro n₁ _ n₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.symm.trans hp2.2)
  rw [hsum_eq_P]
  constructor
  · let H := (Finset.range (N / 2 + 1)).filter (· ∈ A)
    have hsub : H ×ˢ H ⊆ P := by
      intro p hp
      rw [Finset.mem_product] at hp
      rcases hp with ⟨hp1, hp2⟩
      rw [Finset.mem_filter, Finset.mem_range] at hp1 hp2
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, by omega⟩
      · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp1.2⟩
      · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp2.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_product, ← sq] at hcard
    exact hcard
  · have hsub : P ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_product, ← sq] at hcard
    exact hcard

/-- **Cauchy–Schwarz Additive Energy Lower Bound**:
For every `A ⊆ ℕ` and `N : ℕ`,
`|A ∩ [0, ⌊N/2⌋]|⁴ ≤ (∑_{n ≤ N} r_A(n))² ≤ (N + 1) * ∑_{n ≤ N} r_A(n)²`. -/
theorem ppl098_rep_sum_sq_cauchy_schwarz (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    ((Finset.range (N / 2 + 1)).filter (· ∈ A)).card ^ 4
      ≤ (∑ n ∈ Finset.range (N + 1),
          ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card) ^ 2
    ∧ (∑ n ∈ Finset.range (N + 1),
          ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card) ^ 2
      ≤ (N + 1) * ∑ n ∈ Finset.range (N + 1),
          ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card ^ 2 := by
  constructor
  · have h1 := (ppl098_sum_rep_sandwich A N).1
    have hsq := Nat.pow_le_pow_left h1 2
    simpa [← pow_mul] using hsq
  · let f : ℕ → ℕ := fun n => ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card
    change (∑ n ∈ Finset.range (N + 1), f n) ^ 2 ≤
      (N + 1) * ∑ n ∈ Finset.range (N + 1), f n ^ 2
    zify
    have hnn : (0 : ℤ) ≤ ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((f i : ℤ) - (f j : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp : (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((f i : ℤ) - (f j : ℤ)) ^ 2) =
        2 * ((N : ℤ) + 1) * (∑ i ∈ Finset.range (N + 1), (f i : ℤ) ^ 2) -
        2 * (∑ i ∈ Finset.range (N + 1), (f i : ℤ)) ^ 2 := by
      have hinner : ∀ i : ℕ,
          (∑ j ∈ Finset.range (N + 1), ((f i : ℤ) - (f j : ℤ)) ^ 2) =
          ((N : ℤ) + 1) * (f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (∑ j ∈ Finset.range (N + 1), (f j : ℤ))
            + ∑ j ∈ Finset.range (N + 1), (f j : ℤ) ^ 2 := by
        intro i
        have hrw : ∀ j : ℕ, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
            (f i : ℤ) ^ 2 - (2 * (f i : ℤ)) * (f j : ℤ) + (f j : ℤ) ^ 2 := fun j => by ring
        simp_rw [hrw, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
        push_cast; ring
      have hinner' : ∀ i : ℕ,
          (∑ j ∈ Finset.range (N + 1), ((f i : ℤ) - (f j : ℤ)) ^ 2) =
          ((N : ℤ) + 1) * (f i : ℤ) ^ 2 - (2 * ∑ j ∈ Finset.range (N + 1), (f j : ℤ)) * (f i : ℤ)
            + ∑ j ∈ Finset.range (N + 1), (f j : ℤ) ^ 2 := by
        intro i; linarith [hinner i]
      simp_rw [hinner', Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
      push_cast; ring
    linarith

section CesaroHelpers

private lemma sum_log_div_mul_log_tendsto_one :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- For any δ ∈ (0, 1), split the sum at ⌊δ N⌋:
  -- Lower bound: ∑_{n = ⌊δ N⌋}^{N} log n ≥ (N - ⌊δ N⌋) log(δ N)
  -- Upper bound: ∑_{n = 0}^{N} log n ≤ N log N (since log 0 = log 1 = 0 and log n ≤ log N for 1 ≤ n ≤ N).
  set δ : ℝ := min (ε / 4) (1 / 2)
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ_le_eps : δ ≤ ε / 4 := min_le_left _ _
  -- Choose N₀ large enough that log N > max(1, 4 * |log δ| / ε) and 1 / N < ε / 4.
  have hlog_inf : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hN1 : ∀ᶠ N : ℕ in atTop, max 2 (4 * (|Real.log δ| + 1) / ε) < Real.log (N : ℝ) :=
    (tendsto_atTop.1 hlog_inf (max 2 (4 * (|Real.log δ| + 1) / ε) + 1)).mono fun N hN => by linarith
  have hN2 : ∀ᶠ N : ℕ in atTop, (4 : ℝ) / ε + 4 < (N : ℝ) :=
    (tendsto_atTop.1 tendsto_natCast_atTop_atTop ((4 : ℝ) / ε + 5)).mono fun N hN => by linarith
  have hN3 : ∀ᶠ N : ℕ in atTop, 4 ≤ N := eventually_ge_atTop 4
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hN1.and (hN2.and hN3))
  refine ⟨N₀, fun N hN => ?_⟩
  rcases hN₀ N hN with ⟨hlogN, hNbig, hN4⟩
  have hlogN_pos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hlogN.le)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hdenom_pos : 0 < (N : ℝ) * Real.log (N : ℝ) := mul_pos hN_pos hlogN_pos
  -- Upper bound: ∑_{n ≤ N} log n ≤ N * log N
  have hupper : (∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) ≤ (N : ℝ) * Real.log (N : ℝ) := by
    have hsplit : ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ) =
        Real.log 0 + ∑ k ∈ Finset.range N, Real.log ((k + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    rw [hsplit, Real.log_zero, zero_add]
    calc ∑ k ∈ Finset.range N, Real.log ((k + 1 : ℕ) : ℝ)
        ≤ ∑ _k ∈ Finset.range N, Real.log (N : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_range] at hk
          exact Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 1 ≤ N))
      _ = (N : ℝ) * Real.log (N : ℝ) := by simp
  -- Lower bound: keep n ∈ [M, N] where M = ⌈δ N⌉₊
  set M : ℕ := Nat.ceil (δ * (N : ℝ))
  have hM_ge : δ * (N : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  have hM_lt : (M : ℝ) < δ * (N : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hM_le_N : M ≤ N := by
    have : (M : ℝ) < (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
      have : δ ≤ 1 / 2 := min_le_right _ _
      nlinarith
    exact_mod_cast this.le
  have hM_pos : 1 ≤ M := by
    have : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le (mul_pos hδ_pos hN_pos) hM_ge
    exact_mod_cast (Nat.pos_of_ne_zero (by intro h; simp [h] at this))
  have hlower : ((N - M : ℕ) : ℝ) * Real.log (δ * (N : ℝ)) ≤
      ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ) := by
    have hsub : Finset.Ico M N ⊆ Finset.range (N + 1) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      rw [Finset.mem_range]; omega
    have hnn : ∀ n ∈ Finset.range (N + 1), 0 ≤ Real.log (n : ℝ) := by
      intro n _
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0))
    calc ((N - M : ℕ) : ℝ) * Real.log (δ * (N : ℝ))
        = ∑ _n ∈ Finset.Ico M N, Real.log (δ * (N : ℝ)) := by simp [Nat.card_Ico]
      _ ≤ ∑ n ∈ Finset.Ico M N, Real.log (n : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_Ico] at hn
          refine Real.log_le_log (mul_pos hδ_pos hN_pos) ?_
          exact le_trans hM_ge (by exact_mod_cast hn.1)
      _ ≤ ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnn n hn
  -- Convert lower & upper bounds to distance < ε from 1.
  rw [Real.dist_eq, abs_lt]
  have hU : (∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)) ≤ 1 :=
    (div_le_one hdenom_pos).2 hupper
  constructor
  · have hNM : ((N - M : ℕ) : ℝ) = (N : ℝ) - (M : ℝ) := Nat.cast_sub hM_le_N
    have hNM_ge : (1 - δ) * (N : ℝ) - 1 ≤ ((N - M : ℕ) : ℝ) := by linarith
    have hlog_split : Real.log (δ * (N : ℝ)) = Real.log δ + Real.log (N : ℝ) :=
      Real.log_mul hδ_pos.ne' hN_pos.ne'
    have hlogδ_le : |Real.log δ| / Real.log (N : ℝ) < ε / 4 := by
      rw [div_lt_iff₀ hlogN_pos]
      have h1 : 4 * (|Real.log δ| + 1) / ε < Real.log (N : ℝ) :=
        lt_of_le_of_lt (le_max_right _ _) hlogN
      have h2 : 4 * (|Real.log δ| + 1) < ε * Real.log (N : ℝ) := by
        have := (div_lt_iff₀ hε).1 h1; linarith
      linarith
    have hlogδ_neg : -|Real.log δ| ≤ Real.log δ := neg_abs_le _
    by_cases hε2 : 2 ≤ ε
    · have hsum_nn : 0 ≤ (∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)) := by
        apply div_nonneg _ hdenom_pos.le
        refine Finset.sum_nonneg fun n _ => ?_
        rcases eq_or_ne n 0 with rfl | hn0
        · simp
        · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0))
      linarith
    · push Not at hε2
      have h1N : 1 / (N : ℝ) < ε / 4 := by
        rw [div_lt_iff₀ hN_pos]
        have : 4 / ε < (N : ℝ) := by linarith
        have := (div_lt_iff₀ hε).1 this
        linarith
      have hlow_div :
          (1 - δ - 1 / (N : ℝ)) * (1 - |Real.log δ| / Real.log (N : ℝ))
            ≤ (∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)) := by
        have hstep1 :
            ((1 - δ) * (N : ℝ) - 1) * (Real.log (N : ℝ) - |Real.log δ|)
              ≤ ((N - M : ℕ) : ℝ) * Real.log (δ * (N : ℝ)) := by
          have ha : 0 ≤ (1 - δ) * (N : ℝ) - 1 := by
            have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
            have : δ ≤ 1 / 2 := min_le_right _ _
            nlinarith
          have hb : 0 ≤ Real.log (N : ℝ) - |Real.log δ| := by
            have h1 : |Real.log δ| < (ε / 4) * Real.log (N : ℝ) := (div_lt_iff₀ hlogN_pos).1 hlogδ_le
            nlinarith
          exact mul_le_mul hNM_ge (by linarith) hb (le_trans ha hNM_ge)
        have hcomb := le_trans hstep1 hlower
        rw [le_div_iff₀ hdenom_pos]
        have heq : (1 - δ - 1 / (N : ℝ)) * (1 - |Real.log δ| / Real.log (N : ℝ)) *
              ((N : ℝ) * Real.log (N : ℝ)) =
            ((1 - δ) * (N : ℝ) - 1) * (Real.log (N : ℝ) - |Real.log δ|) := by
          field_simp [hN_pos.ne', hlogN_pos.ne']
        linarith
      have hprod : 1 - ε < (1 - δ - 1 / (N : ℝ)) * (1 - |Real.log δ| / Real.log (N : ℝ)) := by
        have hA : 1 - ε / 2 < 1 - δ - 1 / (N : ℝ) := by linarith
        have hB : 1 - ε / 4 < 1 - |Real.log δ| / Real.log (N : ℝ) := by linarith
        have hA_nn : 0 ≤ 1 - δ - 1 / (N : ℝ) := by
          have : δ ≤ 1 / 2 := min_le_right _ _
          have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
          have : 1 / (N : ℝ) ≤ 1 / 4 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
          linarith
        have hB_nn : 0 ≤ 1 - |Real.log δ| / Real.log (N : ℝ) := by linarith
        have h_nonneg_eps : 0 ≤ (ε / 4) * (1 - δ - 1 / (N : ℝ)) := by positivity
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 2) (by positivity : (0 : ℝ) ≤ ε / 4)]
      linarith
  · linarith

end CesaroHelpers

/-- **Cesàro Cumulative Asymptotic for Any Erdős #66 Witness**:
If `(1_A * 1_A)(n) / log n → c` (`0 < c`), then
`(∑_{n=0}^{N} (1_A * 1_A)(n)) / (N * log N) → c`. -/
theorem ppl098_erdos66_cesaro_asymptotic
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto
      (fun n : ℕ =>
        (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ) / Real.log (n : ℝ))
      atTop (nhds c)) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
          ((N : ℝ) * Real.log (N : ℝ)))
      atTop (nhds c) := by
  let r : ℕ → ℝ := fun n =>
    (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)
  change Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), r n) / ((N : ℝ) * Real.log (N : ℝ)))
    atTop (nhds c)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: Eventually |r n - c log n| ≤ (ε / 4) * log n
  have h1 := (Metric.tendsto_atTop.1 hlim (ε / 4) (by positivity))
  obtain ⟨K₀, hK₀⟩ := h1
  let K : ℕ := max K₀ 2
  have htail : ∀ n ≥ K, |r n - c * Real.log (n : ℝ)| ≤ (ε / 4) * Real.log (n : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hd := hK₀ n (le_trans (le_max_left _ _) hn)
    rw [Real.dist_eq] at hd
    have hmul : |r n / Real.log (n : ℝ) - c| * Real.log (n : ℝ) ≤ (ε / 4) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right hd.le hlog_pos.le
    have heq : (r n / Real.log (n : ℝ) - c) * Real.log (n : ℝ) = r n - c * Real.log (n : ℝ) := by
      field_simp [hlog_pos.ne']
    calc |r n - c * Real.log (n : ℝ)|
        = |(r n / Real.log (n : ℝ) - c) * Real.log (n : ℝ)| := by rw [heq]
      _ = |r n / Real.log (n : ℝ) - c| * Real.log (n : ℝ) := by rw [abs_mul, abs_of_pos hlog_pos]
      _ ≤ (ε / 4) * Real.log (n : ℝ) := hmul
  -- Step 2: Finite head error C = ∑_{n < K} |r n - c log n|
  let C : ℝ := ∑ n ∈ Finset.range K, |r n - c * Real.log (n : ℝ)|
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- Step 3: ∑_{n ≤ N} log n / (N log N) → 1
  have hsum_log := Metric.tendsto_atTop.1 sum_log_div_mul_log_tendsto_one
    (min (ε / (4 * (c + 1))) (1 / 2)) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hsum_log
  -- Step 4: Choose N₂ large enough that C / (N log N) < ε / 4
  have hden_inf : Tendsto (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (tendsto_atTop.1 hden_inf (4 * (C + 1) / ε + 1))
  refine ⟨max K (max N₁ (max N₂ 2)), fun N hN => ?_⟩
  have hNK : K ≤ N := le_trans (le_max_left _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hdenom_pos : 0 < (N : ℝ) * Real.log (N : ℝ) := mul_pos hN_pos hlogN_pos
  set L : ℝ := (∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) / ((N : ℝ) * Real.log (N : ℝ))
  have hL_dist : |L - 1| < min (ε / (4 * (c + 1))) (1 / 2) := by
    simpa [L, Real.dist_eq] using hN₁ N hNN₁
  have hL_le : L ≤ 2 := by
    have : |L - 1| < 1 / 2 := lt_of_lt_of_le hL_dist (min_le_right _ _)
    linarith [(abs_lt.1 this).2]
  have hcL : |c * L - c| < ε / 4 := by
    have h1 : |L - 1| < ε / (4 * (c + 1)) := lt_of_lt_of_le hL_dist (min_le_left _ _)
    have h2 : c * |L - 1| < c * (ε / (4 * (c + 1))) := mul_lt_mul_of_pos_left h1 hc
    have h3 : c * (ε / (4 * (c + 1))) ≤ ε / 4 := by
      have : c / (c + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      calc c * (ε / (4 * (c + 1))) = (c / (c + 1)) * (ε / 4) := by field_simp
        _ ≤ 1 * (ε / 4) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = ε / 4 := one_mul _
    rw [show c * L - c = c * (L - 1) by ring, abs_mul, abs_of_pos hc]
    linarith
  -- Bound |∑ (r n - c log n)| ≤ C + (ε/4) * ∑ log n
  have hdiff_sum :
      |(∑ n ∈ Finset.range (N + 1), r n) - c * ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)|
        ≤ C + (ε / 4) * ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ n ∈ Finset.range (N + 1), (r n - c * Real.log (n : ℝ))|
        ≤ ∑ n ∈ Finset.range (N + 1), |r n - c * Real.log (n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = (∑ n ∈ Finset.range K, |r n - c * Real.log (n : ℝ)|)
          + ∑ n ∈ Finset.Ico K (N + 1), |r n - c * Real.log (n : ℝ)| := by
          rw [← Finset.sum_range_add_sum_Ico _ (by omega : K ≤ N + 1)]
      _ ≤ C + ∑ n ∈ Finset.Ico K (N + 1), (ε / 4) * Real.log (n : ℝ) := by
          refine add_le_add le_rfl ?_
          refine Finset.sum_le_sum fun n hn => htail n (Finset.mem_Ico.1 hn).1
      _ ≤ C + ∑ n ∈ Finset.range (N + 1), (ε / 4) * Real.log (n : ℝ) := by
          refine add_le_add le_rfl ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => ?_)
          · rw [Finset.mem_range]; exact (Finset.mem_Ico.1 hn).2
          · refine mul_nonneg (by positivity) ?_
            rcases eq_or_ne n 0 with rfl | hn0
            · simp
            · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0))
      _ = C + (ε / 4) * ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ) := by
          rw [Finset.mul_sum]
  have hC_div : C / ((N : ℝ) * Real.log (N : ℝ)) < ε / 4 := by
    have hd := hN₂ N hNN₂
    rw [div_lt_iff₀ hdenom_pos]
    have hmul : 4 * (C + 1) ≤ ((N : ℝ) * Real.log (N : ℝ)) * ε :=
      (div_le_iff₀ hε).1 (by linarith : 4 * (C + 1) / ε ≤ (N : ℝ) * Real.log (N : ℝ))
    linarith
  rw [Real.dist_eq]
  have htri :
      |(∑ n ∈ Finset.range (N + 1), r n) / ((N : ℝ) * Real.log (N : ℝ)) - c|
        ≤ |(∑ n ∈ Finset.range (N + 1), r n) / ((N : ℝ) * Real.log (N : ℝ)) - c * L| + |c * L - c| :=
    abs_sub_le _ _ _
  have hfirst :
      |(∑ n ∈ Finset.range (N + 1), r n) / ((N : ℝ) * Real.log (N : ℝ)) - c * L|
        ≤ C / ((N : ℝ) * Real.log (N : ℝ)) + (ε / 4) * L := by
    have heq :
        (∑ n ∈ Finset.range (N + 1), r n) / ((N : ℝ) * Real.log (N : ℝ)) - c * L =
        ((∑ n ∈ Finset.range (N + 1), r n) - c * ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) /
          ((N : ℝ) * Real.log (N : ℝ)) := by
      dsimp only [L]; ring
    rw [heq, abs_div, abs_of_pos hdenom_pos]
    calc |(∑ n ∈ Finset.range (N + 1), r n) - c * ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)| /
          ((N : ℝ) * Real.log (N : ℝ))
        ≤ (C + (ε / 4) * ∑ n ∈ Finset.range (N + 1), Real.log (n : ℝ)) /
            ((N : ℝ) * Real.log (N : ℝ)) :=
          div_le_div_of_nonneg_right hdiff_sum hdenom_pos.le
      _ = C / ((N : ℝ) * Real.log (N : ℝ)) + (ε / 4) * L := by dsimp only [L]; ring
  nlinarith

/-- **Necessary Density Profile for Any Erdős #66 Witness**:
If `(1_A * 1_A)(n) / log n → c > 0`, then for every `ε > 0`, eventually for all large `N : ℕ`:
`(√c - ε) * √(N * log N) ≤ |A ∩ [0, N]| ≤ (√(2c) + ε) * √(N * log N)`. -/
theorem ppl098_erdos66_density_profile
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hlim : Tendsto
      (fun n : ℕ =>
        (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ) / Real.log (n : ℝ))
      atTop (nhds c)) :
    ∀ᶠ N : ℕ in atTop,
      (Real.sqrt c - ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ))
        ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)
      ∧ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)
        ≤ (Real.sqrt (2 * c) + ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by
  have hces := ppl098_erdos66_cesaro_asymptotic A hc hlim
  -- From cesaro: eventually S(N) / (N log N) ∈ (c - δ₁, c + δ₁), and similarly at 2N.
  -- Choose δ₁ > 0 small enough that √(c - δ₁) ≥ √c - ε and √(2 * (c + δ₁) * (1 + δ₂)) ≤ √(2c) + ε.
  have hsqrt_cont : ContinuousAt Real.sqrt c := (Real.continuous_sqrt).continuousAt
  have hlo_cont : ∀ᶠ x in nhds c, Real.sqrt c - ε < Real.sqrt x :=
    hsqrt_cont.eventually (Ioi_mem_nhds (by linarith))
  have hlo_ev : ∀ᶠ N : ℕ in atTop,
      Real.sqrt c - ε <
        Real.sqrt ((∑ n ∈ Finset.range (N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
          ((N : ℝ) * Real.log (N : ℝ))) :=
    hces.eventually hlo_cont
  -- For the upper bound, evaluate Cesàro at 2 * N:
  have hces2 : Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (2 * N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
          (((2 * N : ℕ) : ℝ) * Real.log ((2 * N : ℕ) : ℝ)))
      atTop (nhds c) :=
    hces.comp (tendsto_atTop_atTop_of_monotone (fun a b hab => by omega) fun b => ⟨b, by omega⟩)
  -- And ((2N) * log (2N)) / (N * log N) → 2
  have hratio2 : Tendsto
      (fun N : ℕ => (((2 * N : ℕ) : ℝ) * Real.log ((2 * N : ℕ) : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (nhds 2) := by
    have hlog2 : Tendsto (fun N : ℕ => Real.log 2 / Real.log (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun N : ℕ => 2 * (1 + Real.log 2 / Real.log (N : ℝ))) atTop (nhds 2) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hlog2).const_mul (2 : ℝ)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hN_pos.ne']
    field_simp [hN_pos.ne', hlogN_pos.ne']
    ring
  have hprod2 : Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (2 * N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
          ((N : ℝ) * Real.log (N : ℝ)))
      atTop (nhds (2 * c)) := by
    have hmul := hces2.mul hratio2
    rw [mul_comm] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have h2N_pos : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by positivity
    have hlog2N_pos : 0 < Real.log ((2 * N : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * N))
    have hd_ne : ((2 * N : ℕ) : ℝ) * Real.log ((2 * N : ℕ) : ℝ) ≠ 0 :=
      mul_ne_zero h2N_pos.ne' hlog2N_pos.ne'
    field_simp [hd_ne]
  have hhi_ev : ∀ᶠ N : ℕ in atTop,
      Real.sqrt ((∑ n ∈ Finset.range (2 * N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
          ((N : ℝ) * Real.log (N : ℝ))) < Real.sqrt (2 * c) + ε :=
    hprod2.eventually ((Real.continuous_sqrt).continuousAt.eventually (Iio_mem_nhds (by linarith)))
  filter_upwards [hlo_ev, hhi_ev, eventually_ge_atTop 2] with N hlo hhi hN2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdenom_pos : 0 < (N : ℝ) * Real.log (N : ℝ) := mul_pos hN_pos hlogN_pos
  have hAN_nn : (0 : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) := Nat.cast_nonneg _
  constructor
  · have hsand := (ppl098_sum_rep_sandwich A N).2
    have hsandR :
        (∑ n ∈ Finset.range (N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ))
          ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) ^ 2 := by
      exact_mod_cast hsand
    have hsqrt_le :
        Real.sqrt ((∑ n ∈ Finset.range (N + 1),
          (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
          ((N : ℝ) * Real.log (N : ℝ))) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ))
          ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) := by
      rw [← Real.sqrt_mul (div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hdenom_pos.le),
        div_mul_cancel₀ _ hdenom_pos.ne']
      exact (Real.sqrt_le_iff).2 ⟨hAN_nn, hsandR⟩
    have hmul_lt := mul_le_mul_of_nonneg_right hlo.le (Real.sqrt_nonneg ((N : ℝ) * Real.log (N : ℝ)))
    exact le_trans hmul_lt hsqrt_le
  · have hsand := (ppl098_sum_rep_sandwich A (2 * N)).1
    have hhalf : 2 * N / 2 = N := by omega
    rw [hhalf] at hsand
    have hsandR :
        (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) ^ 2
          ≤ ∑ n ∈ Finset.range (2 * N + 1),
              (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ) := by
      exact_mod_cast hsand
    have hle_sqrt :
        (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)
          ≤ Real.sqrt ((∑ n ∈ Finset.range (2 * N + 1),
              (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) /
              ((N : ℝ) * Real.log (N : ℝ))) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by
      rw [← Real.sqrt_mul (div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hdenom_pos.le),
        div_mul_cancel₀ _ hdenom_pos.ne']
      exact Real.le_sqrt_of_sq_le hsandR
    exact le_trans hle_sqrt (mul_le_mul_of_nonneg_right hhi.le (Real.sqrt_nonneg _))

/-- **Any Erdős #66 Witness Must Be Infinite with Natural Density Zero**:
If `(1_A * 1_A)(n) / log n → c > 0`, then `A.Infinite` and `|A ∩ [0, N]| / N → 0`. -/
theorem ppl098_erdos66_infinite_and_zero_density
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto
      (fun n : ℕ =>
        (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ) / Real.log (n : ℝ))
      atTop (nhds c)) :
    A.Infinite ∧
    Tendsto (fun N : ℕ => (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hprof := ppl098_erdos66_density_profile A hc (ε := Real.sqrt c / 2)
    (by positivity) hlim
  constructor
  · intro hfin
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ a ∈ A, a < M := by
      obtain ⟨s, hs⟩ := hfin.exists_finset_coe
      refine ⟨s.sup id + 1, fun a ha => ?_⟩
      have ha' : a ∈ s := by rw [← Finset.mem_coe, hs]; exact ha
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) ha')
    have hcard_le : ∀ N : ℕ, ((Finset.range (N + 1)).filter (· ∈ A)).card ≤ M := by
      intro N
      have hsub : (Finset.range (N + 1)).filter (· ∈ A) ⊆ Finset.range M := by
        intro a ha
        rw [Finset.mem_range]
        exact hM a (Finset.mem_filter.1 ha).2
      simpa using Finset.card_le_card hsub
    have hgrow : Tendsto (fun N : ℕ => (Real.sqrt c / 2) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)))
        atTop atTop := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) atTop atTop :=
        Filter.Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      have h2 : Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) * Real.log (N : ℝ))) atTop atTop :=
        (tendsto_atTop_atTop.2 fun b => ⟨(max b 0) ^ 2, fun x hx =>
          le_trans (le_max_left b 0) (by simpa [Real.sqrt_sq (le_max_right b 0)] using Real.sqrt_le_sqrt hx)⟩).comp h1
      exact Filter.Tendsto.const_mul_atTop (by positivity) h2
    have hev := hprof.and (tendsto_atTop.1 hgrow ((M : ℝ) + 1))
    obtain ⟨N, ⟨hlo, _⟩, hbig⟩ := hev.exists
    have hle : (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hcard_le N
    linarith
  · -- Squeeze: 0 ≤ |A ∩ [0, N]| / N ≤ (√(2c) + √c/2) * √(log N / N) → 0
    have hlog_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
      have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
        simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      exact h0.comp tendsto_natCast_atTop_atTop
    have hsqrt_zero : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ) / (N : ℝ))) atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hlog_div
      rw [Real.sqrt_zero] at h
      exact h
    have hup : Tendsto
        (fun N : ℕ => (Real.sqrt (2 * c) + Real.sqrt c / 2) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds 0) := by
      simpa using hsqrt_zero.const_mul (Real.sqrt (2 * c) + Real.sqrt c / 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards with N
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · filter_upwards [hprof, eventually_ge_atTop 2] with N ⟨_, hhi⟩ hN2
      have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
      calc (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) / (N : ℝ)
          ≤ ((Real.sqrt (2 * c) + Real.sqrt c / 2) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ))) / (N : ℝ) :=
            div_le_div_of_nonneg_right hhi hN_pos.le
        _ = (Real.sqrt (2 * c) + Real.sqrt c / 2) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) := by
            rw [Real.sqrt_mul hN_pos.le, Real.sqrt_div hlogN_nn]
            have hsqN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN_pos).ne'
            field_simp [hN_pos.ne', hsqN]
            rw [Real.sq_sqrt hN_pos.le]; ring

/-! ## Part II: Radial Parseval & Triangle-Bump Positivity Engine on the Unit Disk -/

section ParsevalHelpers

private lemma norm_exp_I_mul_real (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

private lemma exp_I_nat_mul_conj (n : ℕ) (θ : ℝ) :
    star (Complex.exp (Complex.I * ((n : ℝ) : ℂ) * (θ : ℂ))) =
      Complex.exp (Complex.I * (-(n : ℝ) : ℂ) * (θ : ℂ)) := by
  simp only [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

private lemma integral_exp_I_int_mul (k : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ))) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      Complex.real_smul, mul_one]
    push_cast
    ring
  · have hk_ne : (Complex.I * (k : ℂ)) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.2 hk)
    let F : ℝ → ℂ := fun θ => Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ)) / (Complex.I * (k : ℂ))
    have hderiv : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
        HasDerivAt F (Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ))) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (Complex.I * (k : ℂ)) * (t : ℂ)) (Complex.I * (k : ℂ)) θ := by
        simpa using h1.const_mul (Complex.I * (k : ℂ))
      have h3 : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)))
          (Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ)) * (Complex.I * (k : ℂ))) θ :=
        h2.cexp
      have h4 := h3.div_const (Complex.I * (k : ℂ))
      simpa [F, mul_div_cancel_right₀ _ hk_ne] using h4
    have hint : IntervalIntegrable (fun θ : ℝ => Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ)))
        volume (-Real.pi) Real.pi :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hper : Complex.exp (Complex.I * (k : ℂ) * (Real.pi : ℂ)) =
        Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have hdiff : Complex.I * (k : ℂ) * (Real.pi : ℂ) -
          Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [← sub_eq_zero]
      have hfac : Complex.exp (Complex.I * (k : ℂ) * (Real.pi : ℂ)) -
          Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) =
          Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) *
            (Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 2
        push_cast; ring
      rw [hfac, Complex.exp_int_mul_two_pi_mul_I, sub_self, mul_zero]
    simp only [F, hper, sub_self]

private lemma parseval_finset_sum (c : ℕ → ℂ) (M : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi,
      ‖∑ n ∈ Finset.range M, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2) =
      (2 * Real.pi) * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
  let S : ℝ → ℂ := fun θ => ∑ n ∈ Finset.range M, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))
  have hnorm_sq : ∀ θ : ℝ, (‖S θ‖ ^ 2 : ℝ) = (S θ * star (S θ)).re := by
    intro θ
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hre_int :
      (∫ θ in (-Real.pi)..Real.pi, ‖S θ‖ ^ 2) =
        (∫ θ in (-Real.pi)..Real.pi, S θ * star (S θ)).re := by
    simp_rw [hnorm_sq]
    have hcont : Continuous (fun θ : ℝ => S θ * star (S θ)) := by
      dsimp only [S]
      fun_prop
    simpa [Complex.reCLM_apply] using
      (Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable (-Real.pi) Real.pi))
  rw [hre_int]
  have hexpand : ∀ θ : ℝ, S θ * star (S θ) =
      ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M,
        (c m * star (c n)) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
    intro θ
    dsimp only [S]
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [star_mul, show Complex.I * (n : ℂ) * (θ : ℂ) = Complex.I * ((n : ℝ) : ℂ) * (θ : ℂ) by simp,
      exp_I_nat_mul_conj]
    calc (c m * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) *
          (Complex.exp (Complex.I * (-(n : ℝ) : ℂ) * (θ : ℂ)) * star (c n))
        = (c m * star (c n)) *
            (Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) *
              Complex.exp (Complex.I * (-(n : ℝ) : ℂ) * (θ : ℂ))) := by ring
      _ = (c m * star (c n)) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
          rw [← Complex.exp_add]
          congr 2
          push_cast; ring
  simp_rw [hexpand]
  have hint_inner : ∀ m : ℕ, IntervalIntegrable
      (fun θ : ℝ => ∑ n ∈ Finset.range M,
        (c m * star (c n)) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ)))
      volume (-Real.pi) Real.pi := fun m =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_finsetSum (fun m _ => hint_inner m)]
  have hsum_eval :
      (∑ m ∈ Finset.range M, ∫ θ in (-Real.pi)..Real.pi,
        ∑ n ∈ Finset.range M,
          (c m * star (c n)) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ))) =
        ∑ m ∈ Finset.range M, ((2 * Real.pi : ℝ) : ℂ) * (c m * star (c m)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    have hterm : ∀ n ∈ Finset.range M,
        (∫ θ in (-Real.pi)..Real.pi,
          (c m * star (c n)) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ))) =
          if n = m then ((2 * Real.pi : ℝ) : ℂ) * (c m * star (c m)) else 0 := by
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_exp_I_int_mul]
      by_cases hnm : n = m
      · subst hnm; simp; ring
      · have hne : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
        simp [hnm, hne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range M) m]
    simp [hm]
  rw [hsum_eval, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

private lemma continuous_tsum_fourier (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    Continuous (fun θ : ℝ => ∑' n : ℕ, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))) := by
  refine continuous_tsum (fun n => by fun_prop) hc (fun n θ => ?_)
  rw [norm_mul, show Complex.I * (n : ℂ) * (θ : ℂ) = Complex.I * (((n : ℝ) * θ : ℝ) : ℂ) by push_cast; ring,
    norm_exp_I_mul_real, mul_one]

/-- **Radial Parseval Identity on the Unit Circle** (100% pure Mathlib signature):
For any absolutely summable Fourier sequence `c : ℕ → ℂ` (`Summable (fun n => ‖c n‖)`),
`∫ θ in (-π)..π, ‖∑' n, c n * exp (I * n * θ)‖² = (2 * π) * ∑' n, ‖c n‖²`. -/
theorem ppl098_radial_parseval (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    (∫ θ in (-Real.pi)..Real.pi,
      ‖∑' n : ℕ, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2) =
      (2 * Real.pi) * ∑' n : ℕ, ‖c n‖ ^ 2 := by
  let F : ℝ → ℂ := fun θ => ∑' n : ℕ, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))
  let S : ℕ → ℝ → ℂ := fun M θ => ∑ n ∈ Finset.range M, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))
  let B : ℝ := ∑' n : ℕ, ‖c n‖
  have hB_nn : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  have hterm_norm : ∀ (n : ℕ) (θ : ℝ), ‖c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ = ‖c n‖ := by
    intro n θ
    rw [norm_mul, show Complex.I * (n : ℂ) * (θ : ℂ) = Complex.I * (((n : ℝ) * θ : ℝ) : ℂ) by push_cast; ring,
      norm_exp_I_mul_real, mul_one]
  have hsum_theta : ∀ θ : ℝ, Summable (fun n : ℕ => c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))) := by
    intro θ
    exact Summable.of_norm (by simp_rw [hterm_norm]; exact hc)
  have hF_le : ∀ θ : ℝ, ‖F θ‖ ≤ B := fun θ => by
    calc ‖F θ‖ ≤ ∑' n, ‖c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ :=
          norm_tsum_le_tsum_norm (by simp_rw [hterm_norm]; exact hc)
      _ = B := by simp_rw [hterm_norm]; rfl
  have hS_le : ∀ M θ, ‖S M θ‖ ≤ B := fun M θ => by
    calc ‖S M θ‖ ≤ ∑ n ∈ Finset.range M, ‖c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.range M, ‖c n‖ := by simp_rw [hterm_norm]
      _ ≤ B := hc.sum_le_tsum (Finset.range M) (fun _ _ => norm_nonneg _)
  have hdiff_le : ∀ M θ, ‖F θ - S M θ‖ ≤ B - ∑ n ∈ Finset.range M, ‖c n‖ := by
    intro M θ
    have hsplit : F θ - S M θ = ∑' n : ℕ, c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ)) := by
      have h := (hsum_theta θ).sum_add_tsum_nat_add M
      dsimp only [F, S]; linear_combination -h
    have htail_eq : B - ∑ n ∈ Finset.range M, ‖c n‖ = ∑' n : ℕ, ‖c (n + M)‖ := by
      have h := hc.sum_add_tsum_nat_add M
      dsimp only [B]; linarith
    rw [hsplit, htail_eq]
    have hsum_shift : Summable (fun n : ℕ => ‖c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ))‖) := by
      simp_rw [hterm_norm]
      exact (summable_nat_add_iff M).2 hc
    calc ‖∑' n, c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ))‖
        ≤ ∑' n, ‖c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ))‖ :=
          norm_tsum_le_tsum_norm hsum_shift
      _ = ∑' n, ‖c (n + M)‖ := by simp_rw [hterm_norm]
  -- Left-hand sequence converges to ∫ ‖F θ‖^2
  have hL_tend : Tendsto (fun M : ℕ => ∫ θ in (-Real.pi)..Real.pi, ‖S M θ‖ ^ 2) atTop
      (nhds (∫ θ in (-Real.pi)..Real.pi, ‖F θ‖ ^ 2)) := by
    have htail_zero : Tendsto (fun M : ℕ => (2 * Real.pi) * (2 * B * (B - ∑ n ∈ Finset.range M, ‖c n‖)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun M : ℕ => B - ∑ n ∈ Finset.range M, ‖c n‖) atTop (nhds 0) := by
        simpa [B] using (tendsto_const_nhds (x := B)).sub hc.hasSum.tendsto_sum_nat
      simpa using (h1.const_mul (2 * B)).const_mul (2 * Real.pi)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.1 htail_zero ε hε
    refine ⟨M₀, fun M hM => ?_⟩
    have hF_int : IntervalIntegrable (fun θ => ‖F θ‖ ^ 2) volume (-Real.pi) Real.pi :=
      ((continuous_tsum_fourier c hc).norm.pow 2).intervalIntegrable _ _
    have hS_int : IntervalIntegrable (fun θ => ‖S M θ‖ ^ 2) volume (-Real.pi) Real.pi :=
      (Continuous.intervalIntegrable (by dsimp only [S]; fun_prop) _ _)
    rw [Real.dist_eq, ← intervalIntegral.integral_sub hS_int hF_int]
    have hbd : ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi,
        ‖‖S M θ‖ ^ 2 - ‖F θ‖ ^ 2‖ ≤ 2 * B * (B - ∑ n ∈ Finset.range M, ‖c n‖) := by
      intro θ _
      rw [Real.norm_eq_abs, show ‖S M θ‖ ^ 2 - ‖F θ‖ ^ 2 = (‖S M θ‖ + ‖F θ‖) * (‖S M θ‖ - ‖F θ‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      have hsum_bd : ‖S M θ‖ + ‖F θ‖ ≤ 2 * B := by linarith [hS_le M θ, hF_le θ]
      have hsub_bd : |‖S M θ‖ - ‖F θ‖| ≤ B - ∑ n ∈ Finset.range M, ‖c n‖ := by
        calc |‖S M θ‖ - ‖F θ‖| = |‖F θ‖ - ‖S M θ‖| := abs_sub_comm _ _
          _ ≤ ‖F θ - S M θ‖ := abs_norm_sub_norm_le _ _
          _ ≤ B - ∑ n ∈ Finset.range M, ‖c n‖ := hdiff_le M θ
      exact mul_le_mul hsum_bd hsub_bd (abs_nonneg _) (by positivity)
    have hint_bd := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, sub_neg_eq_add, show Real.pi + Real.pi = 2 * Real.pi by ring,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hint_bd
    have hMbd := hM₀ M hM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
      have hle : ∑ n ∈ Finset.range M, ‖c n‖ ≤ B := hc.sum_le_tsum _ (fun _ _ => norm_nonneg _)
      positivity)] at hMbd
    linarith
  -- Right-hand sequence converges to (2 * π) * ∑' ‖c n‖^2
  have hsq_sum : Summable (fun n : ℕ => ‖c n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) (hc.mul_left B)
    have hn_le : ‖c n‖ ≤ B := hc.le_tsum n (fun _ _ => norm_nonneg _)
    nlinarith [norm_nonneg (c n)]
  have hR_tend : Tendsto (fun M : ℕ => (2 * Real.pi) * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2) atTop
      (nhds ((2 * Real.pi) * ∑' n : ℕ, ‖c n‖ ^ 2)) :=
    hsq_sum.hasSum.tendsto_sum_nat.const_mul (2 * Real.pi)
  have hL_eq : (fun M : ℕ => ∫ θ in (-Real.pi)..Real.pi, ‖S M θ‖ ^ 2) =
      (fun M : ℕ => (2 * Real.pi) * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2) := by
    funext M; exact parseval_finset_sum c M
  rw [hL_eq] at hL_tend
  exact tendsto_nhds_unique hL_tend hR_tend

private lemma integral_triangle_cos_nonneg {α : ℝ} (hα : 0 < α) (k : ℤ) :
    (∫ θ in (-α)..α, (1 - |θ| / α) * Real.cos ((k : ℝ) * θ)) =
      if k = 0 then α else 2 * (1 - Real.cos ((k : ℝ) * α)) / (α * (k : ℝ) ^ 2) := by
  -- Split [-α, α] into [-α, 0] and [0, α]; integrand is even!
  have hcont : Continuous (fun θ : ℝ => (1 - |θ| / α) * Real.cos ((k : ℝ) * θ)) := by fun_prop
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (-α) 0) (hcont.intervalIntegrable 0 α)).symm
  rw [hsplit]
  have heven : (∫ θ in (-α)..0, (1 - |θ| / α) * Real.cos ((k : ℝ) * θ)) =
      ∫ θ in (0 : ℝ)..α, (1 - |θ| / α) * Real.cos ((k : ℝ) * θ) := by
    have hsub := intervalIntegral.integral_comp_neg
      (fun θ : ℝ => (1 - |θ| / α) * Real.cos ((k : ℝ) * θ)) (a := (-α)) (b := 0)
    simp only [neg_neg, neg_zero] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [abs_neg, mul_neg, Real.cos_neg]
  rw [heven, ← two_mul]
  have hpos_congr : (∫ θ in (0 : ℝ)..α, (1 - |θ| / α) * Real.cos ((k : ℝ) * θ)) =
      ∫ θ in (0 : ℝ)..α, (1 - θ / α) * Real.cos ((k : ℝ) * θ) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [Set.uIcc_of_le hα.le] at hθ
    rw [abs_of_nonneg hθ.1]
  rw [hpos_congr]
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one]
    let G : ℝ → ℝ := fun θ => θ - θ ^ 2 / (2 * α)
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) α, HasDerivAt G (1 - θ / α) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => t) 1 θ := hasDerivAt_id θ
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * α)) (2 * θ / (2 * α)) θ := by
        simpa using (hasDerivAt_pow 2 θ).div_const (2 * α)
      refine (h1.sub h2).congr_deriv ?_
      field_simp [hα.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
    dsimp only [G]
    field_simp [hα.ne']
    ring
  · have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
    let G : ℝ → ℝ := fun θ =>
      (1 - θ / α) * (Real.sin ((k : ℝ) * θ) / (k : ℝ)) - Real.cos ((k : ℝ) * θ) / (α * (k : ℝ) ^ 2)
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) α, HasDerivAt G ((1 - θ / α) * Real.cos ((k : ℝ) * θ)) θ := by
      intro θ _
      have hlin : HasDerivAt (fun t : ℝ => 1 - t / α) (-(1 / α)) θ := by
        have h := ((hasDerivAt_id θ).div_const α).const_sub (1 : ℝ)
        exact h.congr_deriv (by ring)
      have hsin : HasDerivAt (fun t : ℝ => Real.sin ((k : ℝ) * t) / (k : ℝ)) (Real.cos ((k : ℝ) * θ)) θ := by
        have h := ((Real.hasDerivAt_sin ((k : ℝ) * θ)).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))).div_const (k : ℝ)
        refine h.congr_deriv ?_
        field_simp [hkR]
      have hcos : HasDerivAt (fun t : ℝ => Real.cos ((k : ℝ) * t) / (α * (k : ℝ) ^ 2))
          (-Real.sin ((k : ℝ) * θ) * (k : ℝ) / (α * (k : ℝ) ^ 2)) θ := by
        have h := ((Real.hasDerivAt_cos ((k : ℝ) * θ)).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))).div_const (α * (k : ℝ) ^ 2)
        refine h.congr_deriv ?_
        ring
      refine ((hlin.mul hsin).sub hcos).congr_deriv ?_
      field_simp [hα.ne', hkR]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
    dsimp only [G]
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, div_self hα.ne', sub_self, zero_mul, zero_div]
    field_simp [hα.ne', hkR]
    ring

private lemma integral_triangle_sin_zero {α : ℝ} (k : ℤ) :
    (∫ θ in (-α)..α, (1 - |θ| / α) * Real.sin ((k : ℝ) * θ)) = 0 := by
  have hodd : ∀ θ : ℝ, (1 - |-θ| / α) * Real.sin ((k : ℝ) * (-θ)) =
      -((1 - |θ| / α) * Real.sin ((k : ℝ) * θ)) := by
    intro θ; simp [abs_neg, mul_neg, Real.sin_neg]
  have hcomp := intervalIntegral.integral_comp_neg
    (fun θ : ℝ => (1 - |θ| / α) * Real.sin ((k : ℝ) * θ)) (a := -α) (b := α)
  simp only [neg_neg] at hcomp
  have h1 : (∫ θ in (-α)..α, (1 - |-θ| / α) * Real.sin ((k : ℝ) * (-θ))) =
      -(∫ θ in (-α)..α, (1 - |θ| / α) * Real.sin ((k : ℝ) * θ)) := by
    simp_rw [hodd, intervalIntegral.integral_neg]
  linarith

private lemma triangle_bump_finset_lower (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    {α : ℝ} (hα : 0 < α) (M : ℕ) :
    α * ∑ n ∈ Finset.range M, w n ^ 2 ≤
      ∫ θ in (-α)..α,
        ‖∑ n ∈ Finset.range M, (w n : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 := by
  let S : ℝ → ℂ := fun θ => ∑ n ∈ Finset.range M, (w n : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))
  have hmono :
      (∫ θ in (-α)..α, (1 - |θ| / α) * ‖S θ‖ ^ 2) ≤ ∫ θ in (-α)..α, ‖S θ‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (Continuous.intervalIntegrable (by dsimp only [S]; fun_prop) _ _)
      (Continuous.intervalIntegrable (by dsimp only [S]; fun_prop) _ _)
      (fun θ hθ => ?_)
    have hle1 : 1 - |θ| / α ≤ 1 := by
      have : 0 ≤ |θ| / α := div_nonneg (abs_nonneg _) hα.le
      linarith
    exact mul_le_of_le_one_left (sq_nonneg _) hle1
  refine le_trans ?_ hmono
  -- Expand (1 - |θ|/α) * ‖S θ‖² as double sum of w m * w n * (1 - |θ|/α) * cos((m-n)θ)
  have hexpand : ∀ θ : ℝ, (1 - |θ| / α) * ‖S θ‖ ^ 2 =
      ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M,
        (w m * w n) * ((1 - |θ| / α) * Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ)) := by
    intro θ
    have hnorm : ‖S θ‖ ^ 2 = (S θ * star (S θ)).re := by
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hnorm]
    have hprod : S θ * star (S θ) =
        ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M,
          ((w m * w n : ℝ) : ℂ) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
      dsimp only [S]
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [star_mul, Complex.star_def, Complex.conj_ofReal,
        show Complex.I * (n : ℂ) * (θ : ℂ) = Complex.I * ((n : ℝ) : ℂ) * (θ : ℂ) by simp,
        ← Complex.star_def, exp_I_nat_mul_conj]
      calc ((w m : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) *
            (Complex.exp (Complex.I * (-(n : ℝ) : ℂ) * (θ : ℂ)) * (w n : ℂ))
          = ((w m * w n : ℝ) : ℂ) *
              (Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) *
                Complex.exp (Complex.I * (-(n : ℝ) : ℂ) * (θ : ℂ))) := by push_cast; ring
        _ = ((w m * w n : ℝ) : ℂ) * Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
            rw [← Complex.exp_add]
            congr 2; push_cast; ring
    rw [hprod, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_ofReal_mul]
    have hre_exp : (Complex.exp (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ))).re =
        Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) := by
      rw [show Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) =
          (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I_re]
    rw [hre_exp]; ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum (fun m _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hinner_int : ∀ m ∈ Finset.range M,
      (∫ θ in (-α)..α, ∑ n ∈ Finset.range M,
        (w m * w n) * ((1 - |θ| / α) * Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ))) =
        ∑ n ∈ Finset.range M,
          (w m * w n) * ∫ θ in (-α)..α, (1 - |θ| / α) * Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) := by
    intro m _
    rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun n _ => intervalIntegral.integral_const_mul _ _
  rw [Finset.sum_congr rfl hinner_int, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hdiag_le : α * w m ^ 2 ≤
      ∑ n ∈ Finset.range M,
        (w m * w n) * ∫ θ in (-α)..α, (1 - |θ| / α) * Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) := by
    have hsingle : α * w m ^ 2 =
        (w m * w m) * ∫ θ in (-α)..α, (1 - |θ| / α) * Real.cos ((((m : ℤ) - (m : ℤ) : ℤ) : ℝ) * θ) := by
      rw [integral_triangle_cos_nonneg hα ((m : ℤ) - (m : ℤ))]
      simp only [sub_self, ↓reduceIte]
      ring
    rw [hsingle]
    refine Finset.single_le_sum
      (f := fun n => (w m * w n) * ∫ θ in (-α)..α, (1 - |θ| / α) * Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ))
      (fun n _ => ?_) hm
    refine mul_nonneg (mul_nonneg (hw m) (hw n)) ?_
    rw [integral_triangle_cos_nonneg hα ((m : ℤ) - (n : ℤ))]
    split_ifs with h0
    · exact hα.le
    · refine div_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
      linarith [Real.cos_le_one ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * α)]
  exact hdiag_le

/-- **Triangle-Bump (Fejér-Dual) Positivity Lower Bound** (100% pure Mathlib signature):
For any nonnegative summable weight sequence `w : ℕ → ℝ` (`∀ n, 0 ≤ w n`, `Summable w`) and
any `α > 0`,
`α * ∑' n, (w n)² ≤ ∫ θ in (-α)..α, ‖∑' n, (w n : ℂ) * exp (I * n * θ)‖²`. -/
theorem ppl098_triangle_bump_positivity (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hsum : Summable w)
    {α : ℝ} (hα : 0 < α) :
    α * ∑' n : ℕ, w n ^ 2 ≤
      ∫ θ in (-α)..α, ‖∑' n : ℕ, (w n : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 := by
  let c : ℕ → ℂ := fun n => (w n : ℂ)
  have hc : Summable (fun n => ‖c n‖) := by
    simpa [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)] using hsum
  let F : ℝ → ℂ := fun θ => ∑' n : ℕ, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))
  let S : ℕ → ℝ → ℂ := fun M θ => ∑ n ∈ Finset.range M, c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))
  let B : ℝ := ∑' n : ℕ, ‖c n‖
  have hB_nn : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  have hterm_norm : ∀ (n : ℕ) (θ : ℝ), ‖c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ = ‖c n‖ := by
    intro n θ
    rw [norm_mul, show Complex.I * (n : ℂ) * (θ : ℂ) = Complex.I * (((n : ℝ) * θ : ℝ) : ℂ) by push_cast; ring,
      norm_exp_I_mul_real, mul_one]
  have hsum_theta : ∀ θ : ℝ, Summable (fun n : ℕ => c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))) :=
    fun θ => Summable.of_norm (by simp_rw [hterm_norm]; exact hc)
  have hF_le : ∀ θ : ℝ, ‖F θ‖ ≤ B := fun θ => by
    calc ‖F θ‖ ≤ ∑' n, ‖c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ :=
          norm_tsum_le_tsum_norm (by simp_rw [hterm_norm]; exact hc)
      _ = B := by simp_rw [hterm_norm]; rfl
  have hS_le : ∀ M θ, ‖S M θ‖ ≤ B := fun M θ => by
    calc ‖S M θ‖ ≤ ∑ n ∈ Finset.range M, ‖c n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.range M, ‖c n‖ := by simp_rw [hterm_norm]
      _ ≤ B := hc.sum_le_tsum (Finset.range M) (fun _ _ => norm_nonneg _)
  have hdiff_le : ∀ M θ, ‖F θ - S M θ‖ ≤ B - ∑ n ∈ Finset.range M, ‖c n‖ := by
    intro M θ
    have hsplit : F θ - S M θ = ∑' n : ℕ, c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ)) := by
      have h := (hsum_theta θ).sum_add_tsum_nat_add M
      dsimp only [F, S]; linear_combination -h
    have htail_eq : B - ∑ n ∈ Finset.range M, ‖c n‖ = ∑' n : ℕ, ‖c (n + M)‖ := by
      have h := hc.sum_add_tsum_nat_add M
      dsimp only [B]; linarith
    rw [hsplit, htail_eq]
    have hsum_shift : Summable (fun n : ℕ => ‖c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ))‖) := by
      simp_rw [hterm_norm]
      exact (summable_nat_add_iff M).2 hc
    calc ‖∑' n, c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ))‖
        ≤ ∑' n, ‖c (n + M) * Complex.exp (Complex.I * ((n + M : ℕ) : ℂ) * (θ : ℂ))‖ :=
          norm_tsum_le_tsum_norm hsum_shift
      _ = ∑' n, ‖c (n + M)‖ := by simp_rw [hterm_norm]
  have hR_tend : Tendsto (fun M : ℕ => ∫ θ in (-α)..α, ‖S M θ‖ ^ 2) atTop
      (nhds (∫ θ in (-α)..α, ‖F θ‖ ^ 2)) := by
    have htail_zero : Tendsto (fun M : ℕ => (2 * α) * (2 * B * (B - ∑ n ∈ Finset.range M, ‖c n‖)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun M : ℕ => B - ∑ n ∈ Finset.range M, ‖c n‖) atTop (nhds 0) := by
        simpa [B] using (tendsto_const_nhds (x := B)).sub hc.hasSum.tendsto_sum_nat
      simpa using (h1.const_mul (2 * B)).const_mul (2 * α)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.1 htail_zero ε hε
    refine ⟨M₀, fun M hM => ?_⟩
    have hF_int : IntervalIntegrable (fun θ => ‖F θ‖ ^ 2) volume (-α) α :=
      ((continuous_tsum_fourier c hc).norm.pow 2).intervalIntegrable _ _
    have hS_int : IntervalIntegrable (fun θ => ‖S M θ‖ ^ 2) volume (-α) α :=
      (Continuous.intervalIntegrable (by dsimp only [S]; fun_prop) _ _)
    rw [Real.dist_eq, ← intervalIntegral.integral_sub hS_int hF_int]
    have hbd : ∀ θ ∈ Set.uIoc (-α) α,
        ‖‖S M θ‖ ^ 2 - ‖F θ‖ ^ 2‖ ≤ 2 * B * (B - ∑ n ∈ Finset.range M, ‖c n‖) := by
      intro θ _
      rw [Real.norm_eq_abs, show ‖S M θ‖ ^ 2 - ‖F θ‖ ^ 2 = (‖S M θ‖ + ‖F θ‖) * (‖S M θ‖ - ‖F θ‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      have hsum_bd : ‖S M θ‖ + ‖F θ‖ ≤ 2 * B := by linarith [hS_le M θ, hF_le θ]
      have hsub_bd : |‖S M θ‖ - ‖F θ‖| ≤ B - ∑ n ∈ Finset.range M, ‖c n‖ := by
        calc |‖S M θ‖ - ‖F θ‖| = |‖F θ‖ - ‖S M θ‖| := abs_sub_comm _ _
          _ ≤ ‖F θ - S M θ‖ := abs_norm_sub_norm_le _ _
          _ ≤ B - ∑ n ∈ Finset.range M, ‖c n‖ := hdiff_le M θ
      exact mul_le_mul hsum_bd hsub_bd (abs_nonneg _) (by positivity)
    have hint_bd := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, sub_neg_eq_add, show α + α = 2 * α by ring,
      abs_of_pos (by positivity : 0 < 2 * α)] at hint_bd
    have hMbd := hM₀ M hM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
      have hle : ∑ n ∈ Finset.range M, ‖c n‖ ≤ B := hc.sum_le_tsum _ (fun _ _ => norm_nonneg _)
      positivity)] at hMbd
    linarith
  have hsq_sum : Summable (fun n : ℕ => w n ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) (hsum.mul_left (∑' k, w k))
    have hn_le : w n ≤ ∑' k, w k := hsum.le_tsum n (fun _ _ => hw _)
    nlinarith [hw n]
  have hL_tend : Tendsto (fun M : ℕ => α * ∑ n ∈ Finset.range M, w n ^ 2) atTop
      (nhds (α * ∑' n : ℕ, w n ^ 2)) :=
    hsq_sum.hasSum.tendsto_sum_nat.const_mul α
  exact le_of_tendsto_of_tendsto hL_tend hR_tend
    (Eventually.of_forall fun M => triangle_bump_finset_lower w hw hα M)

/-- Elementary interval-integral Cauchy–Schwarz for continuous functions on `[a, b]` (`a ≤ b`). -/
private lemma intervalIntegral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    (∫ θ in a..b, u θ * v θ) ^ 2 ≤
      (∫ θ in a..b, u θ ^ 2) * (∫ θ in a..b, v θ ^ 2) := by
  let A : ℝ := ∫ θ in a..b, u θ ^ 2
  let B : ℝ := ∫ θ in a..b, u θ * v θ
  let C : ℝ := ∫ θ in a..b, v θ ^ 2
  have hquad : ∀ t : ℝ, 0 ≤ A * t ^ 2 - 2 * B * t + C := by
    intro t
    have hnn : 0 ≤ ∫ θ in a..b, (t * u θ - v θ) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
    have hexp : (∫ θ in a..b, (t * u θ - v θ) ^ 2) = A * t ^ 2 - 2 * B * t + C := by
      have hrw : (fun θ => (t * u θ - v θ) ^ 2) =
          (fun θ => (t ^ 2 * u θ ^ 2 - (2 * t) * (u θ * v θ)) + v θ ^ 2) := by
        funext θ; ring
      rw [hrw,
        intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      dsimp only [A, B, C]; ring
    linarith
  have hA_nn : 0 ≤ A := intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hA_nn with hA0 | hApos
  · have hB0 : B = 0 := by
      by_contra hBne
      have h1 := hquad ((C + 1) / (2 * B))
      rw [← hA0] at h1
      have : 2 * B * ((C + 1) / (2 * B)) = C + 1 := mul_div_cancel₀ _ (mul_ne_zero two_ne_zero hBne)
      linarith
    dsimp only [A, B] at hA0 hB0
    rw [hB0, ← hA0]
    simp
  · have h1 := hquad (B / A)
    have h2 : A * (A * (B / A) ^ 2 - 2 * B * (B / A) + C) = A * C - B ^ 2 := by
      field_simp [hApos.ne']; ring
    have h3 : 0 ≤ A * (A * (B / A) ^ 2 - 2 * B * (B / A) + C) := mul_nonneg hApos.le h1
    linarith

end ParsevalHelpers

/-! ## Part III: Shared Power-Series & Circle Estimates + The Erdős–Fuchs Theorem (1956) -/

section DiskHelpers

private def rRep (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card

private def indA (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℝ :=
  if n ∈ A then 1 else 0

private lemma indA_nonneg (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : 0 ≤ indA A n := by
  unfold indA; split_ifs <;> norm_num

private lemma indA_le_one (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : indA A n ≤ 1 := by
  unfold indA; split_ifs <;> norm_num

private lemma indA_sq (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : indA A n ^ 2 = indA A n := by
  unfold indA; split_ifs <;> norm_num

private lemma rRep_le_succ (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : rRep A n ≤ n + 1 := by
  unfold rRep
  exact le_trans (Finset.card_filter_le _ _) (by simp)

private lemma sum_indA_conv_eq_rRep (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), (indA A a : ℂ) * (indA A (n - a) : ℂ)) = (rRep A n : ℂ) := by
  unfold rRep indA
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h1 : a ∈ A <;> by_cases h2 : n - a ∈ A <;> simp [h1, h2]

private lemma tendsto_nat_mul_pow_zero {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Tendsto (fun M : ℕ => (M : ℝ) * y ^ M) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hy0 with rfl | hypos
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    simp [zero_pow (by omega : M ≠ 0)]
  · set t : ℝ := (1 - y) / y
    have ht : 0 < t := div_pos (by linarith) hypos
    have h1t : 1 + t = y⁻¹ := by dsimp only [t]; field_simp [hypos.ne']; ring
    have hquad : ∀ M : ℕ, ((M : ℝ) * ((M : ℝ) - 1) / 2) * t ^ 2 ≤ (1 + t) ^ M := by
      intro M
      induction M with
      | zero => simp
      | succ k ih =>
        have hlin : 1 + (k : ℝ) * t ≤ (1 + t) ^ k := by
          have := one_add_mul_le_pow (by linarith : -2 ≤ t) k
          linarith
        have hstep : (1 + t) ^ (k + 1) = (1 + t) ^ k + t * (1 + t) ^ k := by ring
        rw [hstep]
        push_cast
        have ht_nn : 0 ≤ t := ht.le
        nlinarith [sq_nonneg t]
    have hup : Tendsto (fun M : ℕ => 4 / (t ^ 2 * (M : ℝ))) atTop (nhds 0) := by
      have h1 : Tendsto (fun M : ℕ => t ^ 2 * (M : ℝ)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (sq_pos_of_pos ht) tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun M => mul_nonneg (Nat.cast_nonneg M) (pow_nonneg hy0 M)) ?_
    filter_upwards [eventually_ge_atTop 2] with M hM
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hM_pos : (0 : ℝ) < (M : ℝ) := by linarith
    have hpow_pos : 0 < (1 + t) ^ M := by positivity
    have hpow_eq : y ^ M = ((1 + t) ^ M)⁻¹ := by rw [h1t, inv_pow, inv_inv]
    have hdenom : (M : ℝ) ^ 2 * t ^ 2 / 4 ≤ (1 + t) ^ M := by
      have hq := hquad M
      have h1 : (M : ℝ) / 2 ≤ (M : ℝ) - 1 := by linarith
      have h2 : (M : ℝ) ^ 2 / 4 ≤ (M : ℝ) * ((M : ℝ) - 1) / 2 := by nlinarith
      nlinarith [sq_nonneg t]
    rw [hpow_eq, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ hpow_pos (by positivity)]
    nlinarith

private lemma hasSum_nat_mul_pow_complex {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n : ℂ) * z ^ n) (z / (1 - z) ^ 2) := by
  have h1z : 1 - z ≠ 0 := by
    intro h
    have hz1 : z = 1 := (sub_eq_zero.1 h).symm
    rw [hz1, norm_one] at hz
    exact lt_irrefl 1 hz
  have hfin : ∀ M : ℕ,
      (1 - z) ^ 2 * (∑ n ∈ Finset.range M, (n : ℂ) * z ^ n) =
        z - (M : ℂ) * z ^ M + ((M : ℂ) - 1) * z ^ (M + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast; ring
  have hMz : Tendsto (fun M : ℕ => (M : ℂ) * z ^ M) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := tendsto_nat_mul_pow_zero (norm_nonneg z) hz
    refine h.congr fun M => ?_
    simp [norm_pow]
  have hMz1 : Tendsto (fun M : ℕ => ((M : ℂ) - 1) * z ^ (M + 1)) atTop (nhds 0) := by
    have hpow : Tendsto (fun M : ℕ => z ^ M) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
    have h1 : Tendsto (fun M : ℕ => ((M : ℂ) * z ^ M - z ^ M) * z) atTop (nhds ((0 - 0) * z)) :=
      (hMz.sub hpow).mul_const z
    simp only [sub_self, zero_mul] at h1
    refine h1.congr fun M => by ring
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  · have hnum : Tendsto (fun M : ℕ => z - (M : ℂ) * z ^ M + ((M : ℂ) - 1) * z ^ (M + 1))
        atTop (nhds (z - 0 + 0)) :=
      ((tendsto_const_nhds (x := z)).sub hMz).add hMz1
    simp only [sub_zero, add_zero] at hnum
    have hdiv := hnum.div_const ((1 - z) ^ 2)
    refine hdiv.congr fun M => ?_
    rw [← hfin M, mul_div_cancel_left₀ _ (pow_ne_zero 2 h1z)]
  · -- Summable norm: ‖n * z^n‖ = n * ‖z‖^n
    have hbd : ∀ M : ℕ, ∑ n ∈ Finset.range M, ‖(n : ℂ) * z ^ n‖ ≤ 1 / (1 - ‖z‖) ^ 2 := by
      intro M
      have hreal : (1 - ‖z‖) ^ 2 * (∑ n ∈ Finset.range M, (n : ℝ) * ‖z‖ ^ n) =
          ‖z‖ - (M : ℝ) * ‖z‖ ^ M + ((M : ℝ) - 1) * ‖z‖ ^ (M + 1) := by
        induction M with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, mul_add, ih]
          push_cast; ring
      have hle : ∑ n ∈ Finset.range M, (n : ℝ) * ‖z‖ ^ n ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - ‖z‖))]
        rw [mul_comm, hreal]
        have htail : ((M : ℝ) - 1) * ‖z‖ ^ (M + 1) ≤ (M : ℝ) * ‖z‖ ^ M := by
          have h1 : ‖z‖ ^ (M + 1) ≤ ‖z‖ ^ M := by
            rw [pow_succ]
            exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg z) M) hz.le
          have h2 : (M : ℝ) - 1 ≤ (M : ℝ) := by linarith
          rcases eq_or_ne M 0 with rfl | hM0
          · simp [norm_nonneg z]
          · have hM1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
              have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hM0)
              linarith
            exact mul_le_mul h2 h1 (pow_nonneg (norm_nonneg z) (M + 1)) (Nat.cast_nonneg M)
        linarith
      have hnorm_eq : (∑ n ∈ Finset.range M, ‖(n : ℂ) * z ^ n‖) =
          ∑ n ∈ Finset.range M, (n : ℝ) * ‖z‖ ^ n := by
        refine Finset.sum_congr rfl fun n _ => by simp [norm_pow]
      rw [hnorm_eq]
      exact le_trans hle (div_le_div_of_nonneg_right hz.le (sq_nonneg _))
    exact summable_of_sum_range_le (fun _ => norm_nonneg _) hbd

private lemma hasSum_nat_mul_pow_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * x ^ n) (x / (1 - x) ^ 2) := by
  have hz : ‖(x : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  have hc := hasSum_nat_mul_pow_complex hz
  have hre := Complex.reCLM.hasSum hc
  have hlhs : (fun n : ℕ => Complex.reCLM ((n : ℂ) * (x : ℂ) ^ n)) = fun n : ℕ => (n : ℝ) * x ^ n := by
    funext n
    simp only [Complex.reCLM_apply]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hrhs : Complex.reCLM ((x : ℂ) / (1 - (x : ℂ)) ^ 2) = x / (1 - x) ^ 2 := by
    simp only [Complex.reCLM_apply]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rwa [hlhs, hrhs] at hre

private lemma summable_sq_nat_mul_pow_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * x ^ n) ∧
    (∑' n : ℕ, (n : ℝ) ^ 2 * x ^ n) ≤ 3 / (1 - x) ^ 3 := by
  have h1x : 0 < 1 - x := by linarith
  have htele : ∀ M : ℕ,
      (1 - x) * (∑ n ∈ Finset.range (M + 1), (n : ℝ) ^ 2 * x ^ n) + (M : ℝ) ^ 2 * x ^ (M + 1) =
        ∑ n ∈ Finset.range M, (2 * (n : ℝ) + 1) * x ^ (n + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
      conv_lhs => rw [Finset.sum_range_succ (n := k + 1), mul_add]
      conv_rhs => rw [Finset.sum_range_succ (n := k)]
      have hdiff : (1 - x) * (((k + 1 : ℕ) : ℝ) ^ 2 * x ^ (k + 1)) +
          ((k + 1 : ℕ) : ℝ) ^ 2 * x ^ (k + 1 + 1) - (k : ℝ) ^ 2 * x ^ (k + 1) =
          (2 * (k : ℝ) + 1) * x ^ (k + 1) := by
        push_cast; ring
      linarith [ih, hdiff]
  have hgeom := summable_geometric_of_lt_one hx0 hx1
  have hlin := (hasSum_nat_mul_pow_real hx0 hx1)
  have hbd_all : ∀ M : ℕ, ∑ n ∈ Finset.range M, (n : ℝ) ^ 2 * x ^ n ≤ 3 / (1 - x) ^ 3 := by
    intro M
    cases M with
    | zero => simp; positivity
    | succ m =>
      have ht := htele m
      have hnn : 0 ≤ (m : ℝ) ^ 2 * x ^ (m + 1) := by positivity
      have hrhs : ∑ n ∈ Finset.range m, (2 * (n : ℝ) + 1) * x ^ (n + 1) ≤ 3 / (1 - x) ^ 2 := by
        have hsplit : ∑ n ∈ Finset.range m, (2 * (n : ℝ) + 1) * x ^ (n + 1) =
            2 * x * (∑ n ∈ Finset.range m, (n : ℝ) * x ^ n) + x * (∑ n ∈ Finset.range m, x ^ n) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => by ring
        rw [hsplit]
        have h1 : ∑ n ∈ Finset.range m, (n : ℝ) * x ^ n ≤ x / (1 - x) ^ 2 :=
          hlin.summable.sum_le_tsum _ (fun _ _ => by positivity) |>.trans_eq hlin.tsum_eq
        have h2 : ∑ n ∈ Finset.range m, x ^ n ≤ (1 - x)⁻¹ :=
          hgeom.sum_le_tsum _ (fun _ _ => by positivity) |>.trans_eq (tsum_geometric_of_lt_one hx0 hx1)
        have h1' : 2 * x * (∑ n ∈ Finset.range m, (n : ℝ) * x ^ n) ≤ 2 / (1 - x) ^ 2 := by
          calc 2 * x * (∑ n ∈ Finset.range m, (n : ℝ) * x ^ n)
              ≤ 2 * 1 * (1 / (1 - x) ^ 2) := by
                refine mul_le_mul (by linarith) (h1.trans (div_le_div_of_nonneg_right hx1.le (sq_nonneg _)))
                  (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
            _ = 2 / (1 - x) ^ 2 := by ring
        have h2' : x * (∑ n ∈ Finset.range m, x ^ n) ≤ 1 / (1 - x) ^ 2 := by
          have hinv : (1 - x)⁻¹ ≤ 1 / (1 - x) ^ 2 := by
            rw [inv_eq_one_div, div_le_div_iff₀ h1x (sq_pos_of_pos h1x)]
            nlinarith
          calc x * (∑ n ∈ Finset.range m, x ^ n)
              ≤ 1 * (1 / (1 - x) ^ 2) :=
                mul_le_mul hx1.le (h2.trans hinv) (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
            _ = 1 / (1 - x) ^ 2 := one_mul _
        have hsum3 : 2 / (1 - x) ^ 2 + 1 / (1 - x) ^ 2 = 3 / (1 - x) ^ 2 := by ring
        linarith
      have hmul : (1 - x) * (∑ n ∈ Finset.range (m + 1), (n : ℝ) ^ 2 * x ^ n) ≤ 3 / (1 - x) ^ 2 := by
        linarith
      rw [le_div_iff₀ (pow_pos h1x 3)]
      have hstep : (1 - x) ^ 3 * (∑ n ∈ Finset.range (m + 1), (n : ℝ) ^ 2 * x ^ n) =
          (1 - x) ^ 2 * ((1 - x) * (∑ n ∈ Finset.range (m + 1), (n : ℝ) ^ 2 * x ^ n)) := by ring
      have hmul2 := mul_le_mul_of_nonneg_left hmul (sq_nonneg (1 - x))
      rw [mul_div_cancel₀ _ (sq_pos_of_pos h1x).ne'] at hmul2
      linarith
  have hsum := summable_of_sum_range_le (fun _ => by positivity) hbd_all
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hbd_all⟩

private lemma summable_indA_pow (A : Set ℕ) [DecidablePred (· ∈ A)] {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖(indA A n : ℂ) * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (indA_nonneg A n)]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (indA_le_one A n)

private lemma summable_rRep_pow (A : Set ℕ) [DecidablePred (· ∈ A)] {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖(rRep A n : ℂ) * z ^ n‖) := by
  have hlin := (hasSum_nat_mul_pow_real (norm_nonneg z) hz).summable
  have hgeom := summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hlin.add hgeom)
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hle : (rRep A n : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast rRep_le_succ A n
  calc (rRep A n : ℝ) * ‖z‖ ^ n ≤ ((n : ℝ) + 1) * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg (norm_nonneg z) n)
    _ = (n : ℝ) * ‖z‖ ^ n + ‖z‖ ^ n := by ring

private lemma tsum_indA_sq_eq_tsum_rRep (A : Set ℕ) [DecidablePred (· ∈ A)] {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2 = ∑' n : ℕ, (rRep A n : ℂ) * z ^ n := by
  have hA := (summable_indA_pow A hz).of_norm
  have hR := (summable_rRep_pow A hz).of_norm
  have hL : Tendsto (fun M : ℕ => (∑ n ∈ Finset.range M, (indA A n : ℂ) * z ^ n) ^ 2) atTop
      (nhds ((∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2)) :=
    hA.hasSum.tendsto_sum_nat.pow 2
  have hR_t : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, (rRep A n : ℂ) * z ^ n) atTop
      (nhds (∑' n : ℕ, (rRep A n : ℂ) * z ^ n)) :=
    hR.hasSum.tendsto_sum_nat
  -- Difference between (∑_{a < M} indA a z^a)^2 and ∑_{n < M} rRep n z^n vanishes as M → ∞
  have hdiff : Tendsto
      (fun M : ℕ => (∑ n ∈ Finset.range M, (indA A n : ℂ) * z ^ n) ^ 2 -
        ∑ n ∈ Finset.range M, (rRep A n : ℂ) * z ^ n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsum_bd : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖z‖ ^ n) := by
      simpa [add_mul, one_mul] using
        (hasSum_nat_mul_pow_real (norm_nonneg z) hz).summable.add
          (summable_geometric_of_lt_one (norm_nonneg z) hz)
    have htail_zero : Tendsto
        (fun M : ℕ => (∑' n : ℕ, ((n : ℝ) + 1) * ‖z‖ ^ n) -
          ∑ n ∈ Finset.range M, ((n : ℝ) + 1) * ‖z‖ ^ n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := ∑' n : ℕ, ((n : ℝ) + 1) * ‖z‖ ^ n)).sub
        hsum_bd.hasSum.tendsto_sum_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail_zero
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun M => ?_)
    -- Expand (∑_{a < M})^2 as sum over (range M ×ˢ range M), split by p.1 + p.2 < M vs ≥ M.
    let Q := Finset.range M ×ˢ Finset.range M
    have hsq_eq : (∑ n ∈ Finset.range M, (indA A n : ℂ) * z ^ n) ^ 2 =
        ∑ p ∈ Q, (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2) := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun p _ => by rw [pow_add]; ring
    have hlow_eq : (∑ n ∈ Finset.range M, (rRep A n : ℂ) * z ^ n) =
        ∑ p ∈ Q.filter (fun p : ℕ × ℕ => p.1 + p.2 < M),
          (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2) := by
      have hfib : ∀ n ∈ Finset.range M,
          (rRep A n : ℂ) * z ^ n =
            ∑ p ∈ Q.filter (fun p : ℕ × ℕ => p.1 + p.2 = n),
              (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2) := by
        intro n hn
        rw [Finset.mem_range] at hn
        rw [← sum_indA_conv_eq_rRep A n, Finset.sum_mul]
        refine Finset.sum_bij (fun a _ => (a, n - a)) ?_ ?_ ?_ ?_
        · intro a ha
          rw [Finset.mem_range] at ha
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, by omega⟩
        · intro a₁ _ a₂ _ h; exact congrArg Prod.fst h
        · intro p hp
          rw [Finset.mem_filter] at hp
          refine ⟨p.1, Finset.mem_range.2 (by omega), ?_⟩
          ext
          · dsimp
          · dsimp; omega
        · intro a ha
          rw [Finset.mem_range] at ha
          have hadd : a + (n - a) = n := by omega
          rw [hadd]
      rw [Finset.sum_congr rfl hfib, ← Finset.sum_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        constructor
        · rintro ⟨n, hn, hpQ, heq⟩; exact ⟨hpQ, by omega⟩
        · rintro ⟨hpQ, hlt⟩; exact ⟨p.1 + p.2, hlt, hpQ, rfl⟩
      · intro n₁ _ n₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rw [Finset.mem_filter] at hp1 hp2
        exact hne (hp1.2.symm.trans hp2.2)
    rw [hsq_eq, hlow_eq]
    have hsplitQ :
        (∑ p ∈ Q, (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2)) -
        (∑ p ∈ Q.filter (fun p : ℕ × ℕ => p.1 + p.2 < M),
          (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2)) =
        ∑ p ∈ Q.filter (fun p : ℕ × ℕ => ¬(p.1 + p.2 < M)),
          (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2) := by
      have := Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ × ℕ => p.1 + p.2 < M)
        (fun p => (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2))
      linear_combination -this
    rw [hsplitQ]
    calc ‖∑ p ∈ Q.filter (fun p : ℕ × ℕ => ¬(p.1 + p.2 < M)),
            (indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2)‖
        ≤ ∑ p ∈ Q.filter (fun p : ℕ × ℕ => ¬(p.1 + p.2 < M)),
            ‖(indA A p.1 : ℂ) * (indA A p.2 : ℂ) * z ^ (p.1 + p.2)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Q.filter (fun p : ℕ × ℕ => ¬(p.1 + p.2 < M)), ‖z‖ ^ (p.1 + p.2) := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (indA_nonneg A _),
            abs_of_nonneg (indA_nonneg A _)]
          have h1 : indA A p.1 * indA A p.2 ≤ 1 := by
            nlinarith [indA_nonneg A p.1, indA_nonneg A p.2, indA_le_one A p.1, indA_le_one A p.2]
          exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) _) h1
      _ ≤ ∑ n ∈ Finset.Ico M (2 * M), ((n : ℝ) + 1) * ‖z‖ ^ n := by
          have hcov : Q.filter (fun p : ℕ × ℕ => ¬(p.1 + p.2 < M)) ⊆
              (Finset.Ico M (2 * M)).biUnion (fun n => Q.filter (fun p => p.1 + p.2 = n)) := by
            intro p hp
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_biUnion]
            have hp1 : p.1 < M := (Finset.mem_range.1 (Finset.mem_product.1 hp.1).1)
            have hp2 : p.2 < M := (Finset.mem_range.1 (Finset.mem_product.1 hp.1).2)
            exact ⟨p.1 + p.2, Finset.mem_Ico.2 ⟨by omega, by omega⟩, Finset.mem_filter.2 ⟨hp.1, rfl⟩⟩
          have hdisj : Set.PairwiseDisjoint (↑(Finset.Ico M (2 * M)))
              (fun n => Q.filter (fun p => p.1 + p.2 = n)) := by
            intro n₁ _ n₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            rw [Finset.mem_filter] at hp1 hp2
            exact hne (hp1.2.symm.trans hp2.2)
          calc ∑ p ∈ Q.filter (fun p : ℕ × ℕ => ¬(p.1 + p.2 < M)), ‖z‖ ^ (p.1 + p.2)
              ≤ ∑ p ∈ (Finset.Ico M (2 * M)).biUnion (fun n => Q.filter (fun p => p.1 + p.2 = n)),
                  ‖z‖ ^ (p.1 + p.2) :=
                Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => pow_nonneg (norm_nonneg z) _)
            _ = ∑ n ∈ Finset.Ico M (2 * M), ∑ p ∈ Q.filter (fun p => p.1 + p.2 = n), ‖z‖ ^ (p.1 + p.2) :=
                Finset.sum_biUnion hdisj
            _ ≤ ∑ n ∈ Finset.Ico M (2 * M), ((n : ℝ) + 1) * ‖z‖ ^ n := by
                refine Finset.sum_le_sum fun n _ => ?_
                have hcongr : ∑ p ∈ Q.filter (fun p => p.1 + p.2 = n), ‖z‖ ^ (p.1 + p.2) =
                    ((Q.filter (fun p => p.1 + p.2 = n)).card : ℝ) * ‖z‖ ^ n := by
                  rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
                    Finset.sum_const, nsmul_eq_mul]
                rw [hcongr]
                refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) n)
                have hcard_le : (Q.filter (fun p => p.1 + p.2 = n)).card ≤ n + 1 := by
                  have hinj : ∀ p₁ ∈ Q.filter (fun p => p.1 + p.2 = n),
                      ∀ p₂ ∈ Q.filter (fun p => p.1 + p.2 = n), p₁.1 = p₂.1 → p₁ = p₂ := by
                    intro p₁ hp₁ p₂ hp₂ heq
                    rw [Finset.mem_filter] at hp₁ hp₂
                    ext
                    · exact heq
                    · omega
                  have himg : (Q.filter (fun p => p.1 + p.2 = n)).image Prod.fst ⊆ Finset.range (n + 1) := by
                    intro a ha
                    rw [Finset.mem_image] at ha
                    obtain ⟨p, hp, rfl⟩ := ha
                    rw [Finset.mem_filter] at hp
                    rw [Finset.mem_range]; omega
                  calc (Q.filter (fun p => p.1 + p.2 = n)).card
                      = ((Q.filter (fun p => p.1 + p.2 = n)).image Prod.fst).card :=
                        (Finset.card_image_of_injOn hinj).symm
                    _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card himg
                    _ = n + 1 := Finset.card_range _
                exact_mod_cast hcard_le
      _ ≤ (∑' n : ℕ, ((n : ℝ) + 1) * ‖z‖ ^ n) - ∑ n ∈ Finset.range M, ((n : ℝ) + 1) * ‖z‖ ^ n := by
          have h1 : (∑ n ∈ Finset.range M, ((n : ℝ) + 1) * ‖z‖ ^ n) +
              (∑ n ∈ Finset.Ico M (2 * M), ((n : ℝ) + 1) * ‖z‖ ^ n) =
              ∑ n ∈ Finset.range (2 * M), ((n : ℝ) + 1) * ‖z‖ ^ n :=
            Finset.sum_range_add_sum_Ico _ (by omega : M ≤ 2 * M)
          have h2 : ∑ n ∈ Finset.range (2 * M), ((n : ℝ) + 1) * ‖z‖ ^ n ≤
              ∑' n : ℕ, ((n : ℝ) + 1) * ‖z‖ ^ n :=
            hsum_bd.sum_le_tsum _ (fun _ _ => by positivity)
          linarith
  have hsub := hL.sub hR_t
  exact sub_eq_zero.1 (tendsto_nhds_unique hsub hdiff)

private lemma tsum_mul_one_sub_pow (a : ℕ → ℂ) (z : ℂ) (h : ℕ)
    (ha : Summable (fun n : ℕ => a n * z ^ n)) :
    (1 - z ^ h) * (∑' n : ℕ, a n * z ^ n) =
      ∑' n : ℕ, (a n - if h ≤ n then a (n - h) else 0) * z ^ n := by
  let g : ℕ → ℂ := fun n => (if h ≤ n then a (n - h) else 0) * z ^ n
  have hg_shift : (fun n : ℕ => g (n + h)) = fun n : ℕ => z ^ h * (a n * z ^ n) := by
    funext n
    dsimp only [g]
    have hle : h ≤ n + h := Nat.le_add_left h n
    simp only [hle, ↓reduceIte, Nat.add_sub_cancel]
    rw [pow_add]; ring
  have hg_sum : Summable g := by
    rw [← summable_nat_add_iff h, hg_shift]
    exact ha.mul_left (z ^ h)
  have hg_val : (∑' n : ℕ, g n) = z ^ h * ∑' n : ℕ, a n * z ^ n := by
    rw [← hg_sum.sum_add_tsum_nat_add h]
    have hhead : ∑ n ∈ Finset.range h, g n = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_range] at hn
      have hnot : ¬(h ≤ n) := by omega
      simp [g, hnot]
    rw [hhead, zero_add, hg_shift, tsum_mul_left]
  calc (1 - z ^ h) * (∑' n : ℕ, a n * z ^ n)
      = (∑' n : ℕ, a n * z ^ n) - z ^ h * (∑' n : ℕ, a n * z ^ n) := by ring
    _ = (∑' n : ℕ, a n * z ^ n) - ∑' n : ℕ, g n := by rw [hg_val]
    _ = ∑' n : ℕ, (a n * z ^ n - g n) := (ha.tsum_sub hg_sum).symm
    _ = ∑' n : ℕ, (a n - if h ≤ n then a (n - h) else 0) * z ^ n := by
        congr 1; funext n; dsimp only [g]; ring

private lemma norm_one_sub_r_exp_ge {r θ : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1)
    (hθ : |θ| ≤ Real.pi) :
    (1 - r + |θ| / Real.pi) / 2 ≤ ‖1 - (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ ∧
    |θ| / Real.pi ≤ ‖1 - (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ := by
  let w : ℂ := 1 - (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hw_sq : ‖w‖ ^ 2 = (1 - r) ^ 2 + 4 * r * Real.sin (|θ| / 2) ^ 2 := by
    have hre : w.re = 1 - r * Real.cos θ := by
      dsimp only [w]
      rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul,
        show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_re]
    have him : w.im = -(r * Real.sin θ) := by
      dsimp only [w]
      rw [Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul,
        show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_im]
      ring
    have hns : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hns, hre, him]
    have hcos_abs : Real.cos θ = Real.cos |θ| := by
      rcases le_or_gt 0 θ with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, Real.cos_neg]
    have hhalf : Real.cos |θ| = 1 - 2 * Real.sin (|θ| / 2) ^ 2 := by
      have h := Real.cos_two_mul' (|θ| / 2)
      rw [show 2 * (|θ| / 2) = |θ| by ring] at h
      have hsc := Real.sin_sq_add_cos_sq (|θ| / 2)
      linarith
    have hsc0 := Real.sin_sq_add_cos_sq θ
    calc (1 - r * Real.cos θ) ^ 2 + (-(r * Real.sin θ)) ^ 2
        = 1 - 2 * r * Real.cos θ + r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = 1 - 2 * r * Real.cos θ + r ^ 2 := by rw [hsc0, mul_one]
      _ = (1 - r) ^ 2 + 2 * r * (1 - Real.cos |θ|) := by rw [hcos_abs]; ring
      _ = (1 - r) ^ 2 + 4 * r * Real.sin (|θ| / 2) ^ 2 := by rw [hhalf]; ring
  have hsin_ge : |θ| / Real.pi ≤ Real.sin (|θ| / 2) := by
    have h1 := Real.mul_le_sin (x := |θ| / 2) (by positivity) (by linarith)
    calc |θ| / Real.pi = 2 / Real.pi * (|θ| / 2) := by ring
      _ ≤ Real.sin (|θ| / 2) := h1
  have hsin_sq : (|θ| / Real.pi) ^ 2 ≤ Real.sin (|θ| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin_ge 2
  have hsq_ge : (1 - r) ^ 2 + (|θ| / Real.pi) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [hw_sq]
    nlinarith [sq_nonneg (|θ| / Real.pi)]
  constructor
  · have h1 : ((1 - r + |θ| / Real.pi) / 2) ^ 2 ≤ ‖w‖ ^ 2 := by
      have hcs : ((1 - r + |θ| / Real.pi) / 2) ^ 2 ≤ (1 - r) ^ 2 + (|θ| / Real.pi) ^ 2 := by
        nlinarith [sq_nonneg (1 - r - |θ| / Real.pi)]
      linarith
    nlinarith [norm_nonneg w, show (0 : ℝ) ≤ (1 - r + |θ| / Real.pi) / 2 by positivity]
  · have h1 : (|θ| / Real.pi) ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [sq_nonneg (1 - r)]
    nlinarith [norm_nonneg w, show (0 : ℝ) ≤ |θ| / Real.pi by positivity]

private lemma integral_inv_linear {a b α : ℝ} (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) :
    (∫ θ in (0 : ℝ)..α, (a + b * θ)⁻¹) = Real.log (1 + b * α / a) / b := by
  let G : ℝ → ℝ := fun θ => Real.log (a + b * θ) / b
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) α, HasDerivAt G (a + b * θ)⁻¹ θ := by
    intro θ hθ
    rw [Set.uIcc_of_le hα.le] at hθ
    have hpos : 0 < a + b * θ := by nlinarith [hθ.1]
    have hlin : HasDerivAt (fun t : ℝ => a + b * t) b θ := by
      have h := ((hasDerivAt_id θ).const_mul b).const_add a
      simpa using h
    have hlog := (Real.hasDerivAt_log hpos.ne').comp θ hlin
    have hdiv := hlog.div_const b
    refine hdiv.congr_deriv ?_
    field_simp [hb.ne', hpos.ne']
  have hcont : ContinuousOn (fun θ : ℝ => (a + b * θ)⁻¹) (Set.uIcc (0 : ℝ) α) := by
    intro θ hθ
    rw [Set.uIcc_of_le hα.le] at hθ
    have hpos : 0 < a + b * θ := by nlinarith [hθ.1]
    exact ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt.inv₀ hpos.ne').continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  dsimp only [G]
  rw [mul_zero, add_zero, ← sub_div, ← Real.log_div (by positivity) ha.ne']
  congr 2
  field_simp [ha.ne']

private lemma norm_geom_sum_lower {r θ : ℝ} {h : ℕ}
    (hr0 : 0 < r) (hr1 : r < 1) (hh : 1 ≤ h)
    (hrh : 1 / 2 ≤ 1 - (h : ℝ) * (1 - r))
    (hθ : |θ| ≤ 1 / (2 * (h : ℝ))) :
    (h : ℝ) / 4 ≤ ‖∑ j ∈ Finset.range h, ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ^ j‖ := by
  let S : ℂ := ∑ j ∈ Finset.range h, ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ^ j
  refine le_trans ?_ (Complex.re_le_norm S)
  have hre : S.re = ∑ j ∈ Finset.range h, r ^ j * Real.cos ((j : ℝ) * θ) := by
    dsimp only [S]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul, Complex.re_ofReal_mul,
      show (j : ℂ) * (Complex.I * (θ : ℂ)) = (((j : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  rw [hre]
  calc (h : ℝ) / 4 = ∑ _j ∈ Finset.range h, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ j ∈ Finset.range h, r ^ j * Real.cos ((j : ℝ) * θ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hrj : 1 / 2 ≤ r ^ j := by
          have hpow_ge : r ^ h ≤ r ^ j := pow_le_pow_of_le_one hr0.le hr1.le hj.le
          have hbern : 1 - (h : ℝ) * (1 - r) ≤ r ^ h := by
            have h0 := one_add_mul_le_pow (a := -(1 - r)) (by linarith) h
            have hr_eq : 1 + -(1 - r) = r := by ring
            have hlin_eq : 1 + (h : ℝ) * -(1 - r) = 1 - (h : ℝ) * (1 - r) := by ring
            rw [hr_eq, hlin_eq] at h0
            exact h0
          linarith
        have hcos : 1 / 2 ≤ Real.cos ((j : ℝ) * θ) := by
          have habs : |(j : ℝ) * θ| ≤ 1 / 2 := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
            have hjh : (j : ℝ) ≤ (h : ℝ) := by exact_mod_cast hj.le
            have hh_pos : (0 : ℝ) < (h : ℝ) := by positivity
            calc (j : ℝ) * |θ| ≤ (h : ℝ) * (1 / (2 * (h : ℝ))) :=
                  mul_le_mul hjh hθ (abs_nonneg θ) (Nat.cast_nonneg h)
              _ = 1 / 2 := by field_simp [hh_pos.ne']
          have hsq : ((j : ℝ) * θ) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          have hc := Real.one_sub_sq_div_two_le_cos (x := (j : ℝ) * θ)
          linarith
        nlinarith

private lemma avg_one_sub_pow_sq_lower {r θ δ : ℝ} {H : ℕ}
    (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (hH : 1 ≤ H)
    (hδ : 0 < δ) (hθ1 : δ ≤ |θ|) (hθ2 : |θ| ≤ Real.pi) :
    2 - 2 * (H : ℝ) * (1 - r) - 4 * Real.pi / ((H : ℝ) * δ) ≤
      (1 / (H : ℝ)) *
        ∑ h ∈ Finset.Icc 1 H, ‖1 - ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ^ h‖ ^ 2 := by
  let z : ℂ := (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hz_norm : ‖z‖ = r := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      norm_exp_I_mul_real, mul_one]
  have hterm : ∀ h : ℕ, ‖1 - z ^ h‖ ^ 2 = 1 + r ^ (2 * h) - 2 * (z ^ h).re := by
    intro h
    have h1 : ‖1 - z ^ h‖ ^ 2 = ((1 - z ^ h) * star (1 - z ^ h)).re := by
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h1, star_sub, star_one]
    have hmul : (1 - z ^ h) * (1 - star (z ^ h)) = 1 + z ^ h * star (z ^ h) - (z ^ h + star (z ^ h)) := by ring
    rw [hmul, Complex.sub_re, Complex.add_re, Complex.one_re, Complex.add_re,
      Complex.star_def, Complex.conj_re, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
      norm_pow, hz_norm, ← pow_mul, mul_comm h 2]
    ring
  have h1z : ‖1 - z‖ ≥ δ / Real.pi := by
    have hge := (norm_one_sub_r_exp_ge hr1 hr2 hθ2).2
    exact le_trans (div_le_div_of_nonneg_right hθ1 Real.pi_pos.le) hge
  have h1z_ne : 1 - z ≠ 0 := by
    intro h0
    have h0' : ‖1 - z‖ = 0 := by rw [h0, norm_zero]
    have : 0 < δ / Real.pi := div_pos hδ Real.pi_pos
    linarith
  have hgeom_sum : ‖∑ h ∈ Finset.Icc 1 H, z ^ h‖ ≤ 2 * Real.pi / δ := by
    have hshift : ∑ h ∈ Finset.Icc 1 H, z ^ h = z * ∑ j ∈ Finset.range H, z ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun h _ => h - 1) ?_ ?_ ?_ ?_
      · intro h hh; rw [Finset.mem_Icc] at hh; rw [Finset.mem_range]; omega
      · intro h₁ hh₁ h₂ hh₂ heq; rw [Finset.mem_Icc] at hh₁ hh₂; omega
      · intro j hj; rw [Finset.mem_range] at hj
        exact ⟨j + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
      · intro h hh; rw [Finset.mem_Icc] at hh
        have : h = (h - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ']
    have hclosed : (1 - z) * ∑ j ∈ Finset.range H, z ^ j = 1 - z ^ H := by
      have := geom_sum_mul_neg z H
      linear_combination this
    have hnorm_closed : ‖1 - z‖ * ‖∑ h ∈ Finset.Icc 1 H, z ^ h‖ ≤ 2 := by
      rw [hshift, ← norm_mul, show (1 - z) * (z * ∑ j ∈ Finset.range H, z ^ j) =
          z * ((1 - z) * ∑ j ∈ Finset.range H, z ^ j) by ring, hclosed, norm_mul]
      have h1 : ‖1 - z ^ H‖ ≤ 2 := by
        calc ‖1 - z ^ H‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ H‖ := norm_sub_le _ _
          _ = 1 + r ^ H := by rw [norm_one, norm_pow, hz_norm]
          _ ≤ 2 := by linarith [pow_le_one₀ (by linarith : 0 ≤ r) hr2.le (n := H)]
      rw [hz_norm]
      nlinarith [norm_nonneg (1 - z ^ H)]
    have hpos_d : 0 < δ / Real.pi := div_pos hδ Real.pi_pos
    have hmul : (δ / Real.pi) * ‖∑ h ∈ Finset.Icc 1 H, z ^ h‖ ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_right h1z (norm_nonneg _)) hnorm_closed
    rw [le_div_iff₀ hδ]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hmul2 := mul_le_mul_of_nonneg_left hmul hpi.le
    have heq : Real.pi * ((δ / Real.pi) * ‖∑ h ∈ Finset.Icc 1 H, z ^ h‖) =
        ‖∑ h ∈ Finset.Icc 1 H, z ^ h‖ * δ := by field_simp [hpi.ne']
    linarith
  have hsum_ge :
      (H : ℝ) * (2 - 2 * (H : ℝ) * (1 - r)) - 4 * Real.pi / δ ≤
        ∑ h ∈ Finset.Icc 1 H, ‖1 - z ^ h‖ ^ 2 := by
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum]
    have hcard : (Finset.Icc 1 H).card = H := by simp
    have h1 : ∑ _h ∈ Finset.Icc 1 H, (1 : ℝ) = (H : ℝ) := by simp
    have h2 : (H : ℝ) * (1 - 2 * (H : ℝ) * (1 - r)) ≤ ∑ h ∈ Finset.Icc 1 H, r ^ (2 * h) := by
      calc (H : ℝ) * (1 - 2 * (H : ℝ) * (1 - r))
          = ∑ _h ∈ Finset.Icc 1 H, (1 - 2 * (H : ℝ) * (1 - r)) := by simp; ring
        _ ≤ ∑ h ∈ Finset.Icc 1 H, r ^ (2 * h) := by
            refine Finset.sum_le_sum fun h hh => ?_
            rw [Finset.mem_Icc] at hh
            have hbern : 1 - (2 * h : ℕ) * (1 - r) ≤ r ^ (2 * h) := by
              have h0 := one_add_mul_le_pow (a := -(1 - r)) (by linarith) (2 * h)
              have hr_eq : 1 + -(1 - r) = r := by ring
              have hlin_eq : 1 + ((2 * h : ℕ) : ℝ) * -(1 - r) = 1 - ((2 * h : ℕ) : ℝ) * (1 - r) := by ring
              rw [hr_eq, hlin_eq] at h0
              exact h0
            push_cast at hbern
            have hhH : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hh.2
            nlinarith
    have h3 : (∑ h ∈ Finset.Icc 1 H, z ^ h).re ≤ 2 * Real.pi / δ :=
      le_trans (Complex.re_le_norm _) hgeom_sum
    have hsplit : (H : ℝ) * (2 - 2 * (H : ℝ) * (1 - r)) =
        (H : ℝ) + (H : ℝ) * (1 - 2 * (H : ℝ) * (1 - r)) := by ring
    have h4pi : 2 * (2 * Real.pi / δ) = 4 * Real.pi / δ := by ring
    rw [h1]
    linarith
  have hH_pos : (0 : ℝ) < (H : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum_ge (inv_nonneg.2 hH_pos.le)
  have heq : (H : ℝ)⁻¹ * ((H : ℝ) * (2 - 2 * (H : ℝ) * (1 - r)) - 4 * Real.pi / δ) =
      2 - 2 * (H : ℝ) * (1 - r) - 4 * Real.pi / ((H : ℝ) * δ) := by
    field_simp [hH_pos.ne', hδ.ne']
  rw [one_div]
  linarith

private lemma log_le_eight_mul_eighth_root {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  set u : ℝ := Real.sqrt (Real.sqrt (Real.sqrt x))
  have hu_pos : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by linarith)))
  have hu8 : u ^ 8 = x := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt x) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    calc u ^ 8 = ((u ^ 2) ^ 2) ^ 2 := by ring
      _ = x := by rw [h1, h2, h3]
  have hlog : Real.log x = 8 * Real.log u := by
    rw [← hu8, Real.log_pow]; norm_num
  have hlu : Real.log u ≤ u := le_trans (Real.log_le_sub_one_of_pos hu_pos) (by linarith)
  linarith

end DiskHelpers

/-! ### Modular Helpers & Proof of the Erdős–Fuchs Theorem (1956) -/

section ErdosFuchsHelpers

private def sRep (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (rRep A n : ℝ)

private lemma summable_sRep_pow (A : Set ℕ) [DecidablePred (· ∈ A)] {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖(sRep A n : ℂ) * z ^ n‖) := by
  have hsq := (summable_sq_nat_mul_pow_real (norm_nonneg z) hz).1
  have hgeom := summable_geometric_of_lt_one (norm_nonneg z) hz
  have hlin := (hasSum_nat_mul_pow_real (norm_nonneg z) hz).summable
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((hsq.add (hlin.mul_left 2)).add hgeom)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  have hSle : sRep A n ≤ ((n : ℝ) + 1) ^ 2 := by
    calc sRep A n = ∑ k ∈ Finset.range (n + 1), (rRep A k : ℝ) := rfl
      _ ≤ ∑ _k ∈ Finset.range (n + 1), ((n : ℝ) + 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_range] at hk
          have : rRep A k ≤ n + 1 := le_trans (rRep_le_succ A k) (by omega)
          exact_mod_cast this
      _ = ((n : ℝ) + 1) ^ 2 := by simp [sq]; ring
  calc sRep A n * ‖z‖ ^ n ≤ ((n : ℝ) + 1) ^ 2 * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right hSle (pow_nonneg (norm_nonneg z) n)
    _ = (n : ℝ) ^ 2 * ‖z‖ ^ n + 2 * ((n : ℝ) * ‖z‖ ^ n) + ‖z‖ ^ n := by ring

private lemma summable_efErr_pow (A : Set ℕ) [DecidablePred (· ∈ A)] (c : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖((sRep A n - c * (n : ℝ) : ℝ) : ℂ) * z ^ n‖) := by
  have hS := summable_sRep_pow A hz
  have hL := (hasSum_nat_mul_pow_real (norm_nonneg z) hz).summable.mul_left |c|
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hS.add hL)
  have hrew : ((sRep A n - c * (n : ℝ) : ℝ) : ℂ) * z ^ n =
      (sRep A n : ℂ) * z ^ n - (c : ℂ) * (n : ℂ) * z ^ n := by push_cast; ring
  rw [hrew]
  refine le_trans (norm_sub_le _ _) (add_le_add le_rfl ?_)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  ring_nf; rfl

private lemma summable_efDiff_pow (A : Set ℕ) [DecidablePred (· ∈ A)] (c : ℝ) (h : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖((((sRep A n - c * (n : ℝ)) -
      if h ≤ n then (sRep A (n - h) - c * ((n - h : ℕ) : ℝ)) else 0 : ℝ) : ℂ) * z ^ n)‖) := by
  let E : ℕ → ℝ := fun n => sRep A n - c * (n : ℝ)
  have hE1 : Summable (fun n : ℕ => ‖(E n : ℂ) * z ^ n‖) := summable_efErr_pow A c hz
  have hE2 : Summable (fun n : ℕ => ‖((if h ≤ n then E (n - h) else 0 : ℝ) : ℂ) * z ^ n‖) := by
    rw [← summable_nat_add_iff h]
    have heq : (fun n : ℕ => ‖((if h ≤ n + h then E (n + h - h) else 0 : ℝ) : ℂ) * z ^ (n + h)‖) =
        fun n : ℕ => ‖z‖ ^ h * ‖(E n : ℂ) * z ^ n‖ := by
      funext n
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add, norm_mul, norm_pow]
      ring
    rw [heq]; exact hE1.mul_left (‖z‖ ^ h)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hE1.add hE2)
  have hrew : ((E n - if h ≤ n then E (n - h) else 0 : ℝ) : ℂ) * z ^ n =
      (E n : ℂ) * z ^ n - ((if h ≤ n then E (n - h) else 0 : ℝ) : ℂ) * z ^ n := by
    push_cast; ring
  change ‖((E n - if h ≤ n then E (n - h) else 0 : ℝ) : ℂ) * z ^ n‖ ≤ _
  rw [hrew]; exact norm_sub_le _ _

private lemma ef_power_series_ident (A : Set ℕ) [DecidablePred (· ∈ A)] (c : ℝ) (h : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2 * (∑ j ∈ Finset.range h, z ^ j) =
      (∑' n : ℕ, ((((sRep A n - c * (n : ℝ)) -
          if h ≤ n then (sRep A (n - h) - c * ((n - h : ℕ) : ℝ)) else 0 : ℝ) : ℂ) * z ^ n)) +
      (c : ℂ) * z * (∑ j ∈ Finset.range h, z ^ j) / (1 - z) := by
  let E : ℕ → ℝ := fun n => sRep A n - c * (n : ℝ)
  have h1z : 1 - z ≠ 0 := by
    intro h0
    have hz1 : z = 1 := (sub_eq_zero.1 h0).symm
    rw [hz1, norm_one] at hz; exact lt_irrefl 1 hz
  have hS_id : (1 - z) * (∑' n : ℕ, (sRep A n : ℂ) * z ^ n) =
      (∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2 := by
    rw [tsum_indA_sq_eq_tsum_rRep A hz]
    have hsh := tsum_mul_one_sub_pow (fun n => (sRep A n : ℂ)) z 1 (summable_sRep_pow A hz).of_norm
    rw [pow_one] at hsh; rw [hsh]
    congr 1; funext n
    cases n with
    | zero => simp [sRep]
    | succ k =>
      simp only [Nat.succ_le_succ_iff, Nat.zero_le, ↓reduceIte, Nat.add_sub_cancel]
      dsimp only [sRep]; rw [Finset.sum_range_succ]; push_cast; ring
  have hlin_id : (∑' n : ℕ, (c : ℂ) * (n : ℂ) * z ^ n) = (c : ℂ) * z / (1 - z) ^ 2 := by
    have h0 := (hasSum_nat_mul_pow_complex hz).mul_left (c : ℂ)
    have heq : (fun n : ℕ => (c : ℂ) * ((n : ℂ) * z ^ n)) = fun n : ℕ => (c : ℂ) * (n : ℂ) * z ^ n := by
      funext n; ring
    rw [heq] at h0; rw [h0.tsum_eq]; ring
  have hE_id : (∑' n : ℕ, (E n : ℂ) * z ^ n) =
      (∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2 / (1 - z) - (c : ℂ) * z / (1 - z) ^ 2 := by
    have hE_eq : (fun n : ℕ => (E n : ℂ) * z ^ n) =
        fun n : ℕ => (sRep A n : ℂ) * z ^ n - (c : ℂ) * (n : ℂ) * z ^ n := by
      funext n; dsimp only [E]; push_cast; ring
    rw [hE_eq, (summable_sRep_pow A hz).of_norm.tsum_sub
      (((hasSum_nat_mul_pow_complex hz).summable.mul_left (c : ℂ)).congr fun n => by ring)]
    rw [hlin_id]
    have hS_div : (∑' n : ℕ, (sRep A n : ℂ) * z ^ n) =
        (∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2 / (1 - z) := by
      rw [eq_div_iff h1z, mul_comm]; exact hS_id
    rw [hS_div]
  have hg_id : (1 - z ^ h) * (∑' n : ℕ, (E n : ℂ) * z ^ n) =
      ∑' n : ℕ, ((E n - if h ≤ n then E (n - h) else 0 : ℝ) : ℂ) * z ^ n := by
    have hsh := tsum_mul_one_sub_pow (fun n => (E n : ℂ)) z h (summable_efErr_pow A c hz).of_norm
    rw [hsh]; congr 1; funext n; split_ifs <;> simp
  have hgeomH : (1 - z) * (∑ j ∈ Finset.range h, z ^ j) = 1 - z ^ h := by
    have := geom_sum_mul_neg z h; linear_combination this
  change (∑' n : ℕ, (indA A n : ℂ) * z ^ n) ^ 2 * (∑ j ∈ Finset.range h, z ^ j) =
    (∑' n : ℕ, ((E n - if h ≤ n then E (n - h) else 0 : ℝ) : ℂ) * z ^ n) +
    (c : ℂ) * z * (∑ j ∈ Finset.range h, z ^ j) / (1 - z)
  rw [← hg_id, hE_id, ← hgeomH]
  field_simp [h1z]
  ring

private lemma ef_fr2_lower (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c)
    {N₀ N : ℕ} (hN16 : 16 ≤ N)
    (hE_lin : ∀ n ≥ N₀, |sRep A n - c * (n : ℝ)| ≤ (c / 4) * (n : ℝ))
    (hCE_N : 16 * ((∑ n ∈ Finset.range N₀, |sRep A n - c * (n : ℝ)|) + 1) / c ≤ (N : ℝ)) :
    (Real.sqrt c / 2) * Real.sqrt (N : ℝ) ≤
      ∑' n : ℕ, indA A n * ((1 - 1 / (N : ℝ)) ^ 2) ^ n := by
  let E : ℕ → ℝ := fun n => sRep A n - c * (n : ℝ)
  let CE : ℝ := ∑ n ∈ Finset.range N₀, |E n|
  set r : ℝ := 1 - 1 / (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  have hr_ge : 1 / 2 ≤ r := by
    have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos (by linarith)
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have h1mr2_pos : 0 < 1 - r ^ 2 := by linarith
  have hz2 : ‖((r ^ 2 : ℝ) : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr2_pos.le] using hr2_lt1
  have hS_real : (1 - r ^ 2) * (∑' n : ℕ, sRep A n * (r ^ 2) ^ n) =
      (∑' n : ℕ, indA A n * (r ^ 2) ^ n) ^ 2 := by
    have hS_id : (1 - ((r ^ 2 : ℝ) : ℂ)) * (∑' n : ℕ, (sRep A n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) =
        (∑' n : ℕ, (indA A n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) ^ 2 := by
      rw [tsum_indA_sq_eq_tsum_rRep A hz2]
      have hsh := tsum_mul_one_sub_pow (fun n => (sRep A n : ℂ)) ((r ^ 2 : ℝ) : ℂ) 1 (summable_sRep_pow A hz2).of_norm
      rw [pow_one] at hsh; rw [hsh]
      congr 1; funext n
      cases n with
      | zero => simp [sRep]
      | succ k =>
        simp only [Nat.succ_le_succ_iff, Nat.zero_le, ↓reduceIte, Nat.add_sub_cancel]
        dsimp only [sRep]; rw [Finset.sum_range_succ]; push_cast; ring
    have hre := congrArg Complex.re hS_id
    have hf_eq : (∑' n : ℕ, (indA A n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) =
        ((∑' n : ℕ, indA A n * (r ^ 2) ^ n : ℝ) : ℂ) := by
      have hsumR : Summable (fun n : ℕ => indA A n * (r ^ 2) ^ n) :=
        Summable.of_nonneg_of_le (fun _ => mul_nonneg (indA_nonneg A _) (pow_nonneg hr2_pos.le _))
          (fun n => mul_le_of_le_one_left (pow_nonneg hr2_pos.le _) (indA_le_one A n))
          (summable_geometric_of_lt_one hr2_pos.le hr2_lt1)
      simpa [Complex.ofReal_mul, Complex.ofReal_pow] using (Complex.ofRealCLM.map_tsum hsumR).symm
    have hS_eq : (∑' n : ℕ, (sRep A n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) =
        ((∑' n : ℕ, sRep A n * (r ^ 2) ^ n : ℝ) : ℂ) := by
      have hsumR : Summable (fun n : ℕ => sRep A n * (r ^ 2) ^ n) := by
        have h := summable_sRep_pow A hz2
        refine h.congr fun n => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _),
          abs_of_nonneg hr2_pos.le]
      simpa [Complex.ofReal_mul, Complex.ofReal_pow] using (Complex.ofRealCLM.map_tsum hsumR).symm
    rw [hf_eq, hS_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re] at hre
    exact hre
  have hsumE_R : Summable (fun n : ℕ => E n * (r ^ 2) ^ n) := by
    have h := summable_efErr_pow A c hz2
    refine Summable.of_norm (h.congr fun n => ?_)
    dsimp only [E]
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ r), abs_of_nonneg (pow_nonneg hr2_pos.le n)]
  have hsumL_R := hasSum_nat_mul_pow_real hr2_pos.le hr2_lt1
  have hS_split : (∑' n : ℕ, sRep A n * (r ^ 2) ^ n) =
      c * (r ^ 2 / (1 - r ^ 2) ^ 2) + ∑' n : ℕ, E n * (r ^ 2) ^ n := by
    have heq : (fun n : ℕ => sRep A n * (r ^ 2) ^ n) =
        fun n : ℕ => c * ((n : ℝ) * (r ^ 2) ^ n) + E n * (r ^ 2) ^ n := by
      funext n; dsimp only [E]; ring
    rw [heq, (hsumL_R.summable.mul_left c).tsum_add hsumE_R, tsum_mul_left, hsumL_R.tsum_eq]
  have hE_tsum_le : |∑' n : ℕ, E n * (r ^ 2) ^ n| ≤ CE + (c / 4) * (r ^ 2 / (1 - r ^ 2) ^ 2) := by
    have hsn_abs : Summable (fun n : ℕ => |E n| * (r ^ 2) ^ n) := by
      simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr2_pos.le] using hsumE_R.norm
    have h1 : |∑' n : ℕ, E n * (r ^ 2) ^ n| ≤ ∑' n : ℕ, |E n| * (r ^ 2) ^ n := by
      simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr2_pos.le] using
        norm_tsum_le_tsum_norm hsumE_R.norm
    rw [← hsn_abs.sum_add_tsum_nat_add N₀] at h1
    have hhead : ∑ n ∈ Finset.range N₀, |E n| * (r ^ 2) ^ n ≤ CE :=
      Finset.sum_le_sum fun n _ => mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hr2_pos.le hr2_lt1.le)
    have htail : ∑' n : ℕ, |E (n + N₀)| * (r ^ 2) ^ (n + N₀) ≤ (c / 4) * (r ^ 2 / (1 - r ^ 2) ^ 2) := by
      have hle_all := ((summable_nat_add_iff N₀).2 hsn_abs).tsum_le_tsum (fun n => by
        have := hE_lin (n + N₀) (Nat.le_add_left N₀ n)
        nlinarith [pow_nonneg hr2_pos.le (n + N₀)])
        (((summable_nat_add_iff N₀).2 hsumL_R.summable).mul_left (c / 4))
      rw [tsum_mul_left] at hle_all
      have hfull : ∑' n : ℕ, ((n + N₀ : ℕ) : ℝ) * (r ^ 2) ^ (n + N₀) ≤ r ^ 2 / (1 - r ^ 2) ^ 2 := by
        have := hsumL_R.summable.sum_add_tsum_nat_add N₀
        rw [hsumL_R.tsum_eq] at this
        have hnn : 0 ≤ ∑ n ∈ Finset.range N₀, (n : ℝ) * (r ^ 2) ^ n := Finset.sum_nonneg fun _ _ => by positivity
        linarith
      nlinarith
    linarith
  have hr2_ge34 : 3 / 4 ≤ r ^ 2 := by
    have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have : 1 / (N : ℝ) ≤ 1 / 16 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; nlinarith
  have h1mr2_le : 1 - r ^ 2 ≤ 2 / (N : ℝ) := by
    have heq : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [heq, h1mr]
    have h1 : 1 / (N : ℝ) * (1 + r) ≤ 1 / (N : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [show 1 / (N : ℝ) * 2 = 2 / (N : ℝ) by ring]
  have hCE_le : CE ≤ (c / 16) / (1 - r ^ 2) ^ 2 := by
    have h1 : 16 * (CE + 1) ≤ c * (N : ℝ) := by
      have := (div_le_iff₀ hc).1 hCE_N; linarith
    have hsqN : (1 - r ^ 2) ^ 2 ≤ 4 / (N : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ h1mr2_pos.le h1mr2_le 2
      rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
      exact h
    rw [le_div_iff₀ (sq_pos_of_pos h1mr2_pos)]
    have hCE_nn : 0 ≤ CE := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have hNle : 16 * (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hmul : CE * (1 - r ^ 2) ^ 2 ≤ CE * (4 / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsqN hCE_nn
    have h4 : CE * (4 / (N : ℝ) ^ 2) ≤ c / 16 := by
      rw [mul_div_assoc', div_le_iff₀ (sq_pos_of_pos hN_pos)]
      have h256 : 256 * CE ≤ c * (N : ℝ) ^ 2 := by
        have h16 : 16 * CE ≤ c * (N : ℝ) := by linarith
        nlinarith [hc, hNle, h16]
      linarith [h256, hCE_nn]
    linarith
  have hS_ge : (c / 2) / (1 - r ^ 2) ^ 2 ≤ ∑' n : ℕ, sRep A n * (r ^ 2) ^ n := by
    have habs := neg_le_of_abs_le hE_tsum_le
    have hmain : (9 * c / 16) / (1 - r ^ 2) ^ 2 ≤ (3 * c / 4) * (r ^ 2 / (1 - r ^ 2) ^ 2) := by
      have h1 : 9 * c / 16 ≤ (3 * c / 4) * r ^ 2 := by nlinarith
      simpa [mul_div_assoc'] using div_le_div_of_nonneg_right h1 (sq_nonneg (1 - r ^ 2))
    have hsub : (9 * c / 16) / (1 - r ^ 2) ^ 2 - (c / 16) / (1 - r ^ 2) ^ 2 = (c / 2) / (1 - r ^ 2) ^ 2 := by ring
    linarith [hS_split]
  have hfr2_sq : (c / 4) * (N : ℝ) ≤ (∑' n : ℕ, indA A n * (r ^ 2) ^ n) ^ 2 := by
    rw [← hS_real]
    have h1 : (c / 2) / (1 - r ^ 2) ≤ (1 - r ^ 2) * (∑' n : ℕ, sRep A n * (r ^ 2) ^ n) := by
      have hmul := mul_le_mul_of_nonneg_left hS_ge h1mr2_pos.le
      have heq : (1 - r ^ 2) * ((c / 2) / (1 - r ^ 2) ^ 2) = (c / 2) / (1 - r ^ 2) := by
        field_simp [h1mr2_pos.ne']
      linarith
    have h2 : (c / 4) * (N : ℝ) ≤ (c / 2) / (1 - r ^ 2) := by
      rw [le_div_iff₀ h1mr2_pos]
      have hmul := mul_le_mul_of_nonneg_left h1mr2_le (by positivity : 0 ≤ (c / 4) * (N : ℝ))
      have heq : (c / 4) * (N : ℝ) * (2 / (N : ℝ)) = c / 2 := by field_simp [hN_pos.ne']; ring
      linarith
    linarith
  have hfr2_nn : 0 ≤ ∑' n : ℕ, indA A n * (r ^ 2) ^ n :=
    tsum_nonneg fun _ => mul_nonneg (indA_nonneg A _) (pow_nonneg hr2_pos.le _)
  have hsq_eq : ((Real.sqrt c / 2) * Real.sqrt (N : ℝ)) ^ 2 = (c / 4) * (N : ℝ) := by
    rw [mul_pow, div_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hN_pos.le]; ring
  nlinarith [mul_nonneg (div_nonneg (Real.sqrt_nonneg c) (by norm_num : (0 : ℝ) ≤ 2)) (Real.sqrt_nonneg (N : ℝ))]

private lemma ef_main_integral_upper {c α : ℝ} {N h : ℕ}
    (hc : 0 < c) (hN16 : 16 ≤ N) (hα_pos : 0 < α) (hα_le_pi : α ≤ Real.pi) :
    (1 / (2 * Real.pi)) *
      (∫ θ in (-α)..α,
        ‖(c : ℂ) * ((1 - 1 / (N : ℝ) : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (∑ j ∈ Finset.range h, ((1 - 1 / (N : ℝ) : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) ^ j) /
          (1 - ((1 - 1 / (N : ℝ) : ℝ) * Complex.exp (Complex.I * (θ : ℂ))))‖) ≤
      2 * c * (h : ℝ) * Real.log ((N : ℝ) + 1) := by
  set r : ℝ := 1 - 1 / (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  have hr_ge : 1 / 2 ≤ r := by
    have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr_pos : 0 < r := by linarith
  let zθ : ℝ → ℂ := fun θ => (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hzθ_norm : ∀ θ : ℝ, ‖zθ θ‖ = r := fun θ => by
    dsimp only [zθ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_pos.le,
      norm_exp_I_mul_real, mul_one]
  have h1zθ_ne : ∀ θ : ℝ, 1 - zθ θ ≠ 0 := fun θ h0 => by
    have hz1 : zθ θ = 1 := (sub_eq_zero.1 h0).symm
    have := hzθ_norm θ; rw [hz1, norm_one] at this; linarith
  have hmain_cont : Continuous (fun θ : ℝ =>
      ‖(c : ℂ) * zθ θ * (∑ j ∈ Finset.range h, zθ θ ^ j) / (1 - zθ θ)‖) :=
    (Continuous.div (by dsimp only [zθ]; fun_prop) (by dsimp only [zθ]; fun_prop) h1zθ_ne).norm
  have hpt : ∀ θ ∈ Set.Icc (-α) α,
      ‖(c : ℂ) * zθ θ * (∑ j ∈ Finset.range h, zθ θ ^ j) / (1 - zθ θ)‖ ≤
        (2 * c * (h : ℝ)) * (1 - r + |θ| / Real.pi)⁻¹ := by
    intro θ hθ
    have habs_pi : |θ| ≤ Real.pi := le_trans (abs_le.2 hθ) hα_le_pi
    have hden := (norm_one_sub_r_exp_ge hr_ge hr_lt1 habs_pi).1
    have hden_pos : 0 < (1 - r + |θ| / Real.pi) / 2 := by
      have : 0 < 1 - r := by linarith
      positivity
    have hgeom_le : ‖∑ j ∈ Finset.range h, zθ θ ^ j‖ ≤ (h : ℝ) := by
      calc ‖∑ j ∈ Finset.range h, zθ θ ^ j‖
          ≤ ∑ j ∈ Finset.range h, ‖zθ θ ^ j‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.range h, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
            rw [norm_pow, hzθ_norm θ]; exact pow_le_one₀ hr_pos.le hr_lt1.le
        _ = (h : ℝ) := by simp
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, hzθ_norm θ]
    have hnum : c * r * ‖∑ j ∈ Finset.range h, zθ θ ^ j‖ ≤ c * (h : ℝ) := by
      calc c * r * ‖∑ j ∈ Finset.range h, zθ θ ^ j‖ ≤ c * 1 * (h : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr_lt1.le hc.le) hgeom_le (norm_nonneg _) (by positivity)
        _ = c * (h : ℝ) := by ring
    calc c * r * ‖∑ j ∈ Finset.range h, zθ θ ^ j‖ / ‖1 - zθ θ‖
        ≤ (c * (h : ℝ)) / ((1 - r + |θ| / Real.pi) / 2) := div_le_div₀ (by positivity) hnum hden_pos hden
      _ = (2 * c * (h : ℝ)) * (1 - r + |θ| / Real.pi)⁻¹ := by
          have hpos2 : 1 - r + |θ| / Real.pi ≠ 0 := by linarith
          field_simp [hpos2]
  have hcont_inv : Continuous (fun θ : ℝ => (1 - r + |θ| / Real.pi)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun θ => ?_
    have : 0 < 1 - r := by linarith
    have : 0 ≤ |θ| / Real.pi := by positivity
    linarith
  have hint_le : (∫ θ in (-α)..α, ‖(c : ℂ) * zθ θ * (∑ j ∈ Finset.range h, zθ θ ^ j) / (1 - zθ θ)‖) ≤
      (2 * c * (h : ℝ)) * (∫ θ in (-α)..α, (1 - r + |θ| / Real.pi)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith)
      (hmain_cont.intervalIntegrable _ _) ((continuous_const.mul hcont_inv).intervalIntegrable _ _) hpt
  have heven_inv : (∫ θ in (-α)..α, (1 - r + |θ| / Real.pi)⁻¹) =
      2 * ∫ θ in (0 : ℝ)..α, (1 - r + (1 / Real.pi) * θ)⁻¹ := by
    have hsp := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont_inv.intervalIntegrable (-α) 0) (hcont_inv.intervalIntegrable 0 α)).symm
    rw [hsp]
    have hneg : (∫ θ in (-α)..0, (1 - r + |θ| / Real.pi)⁻¹) =
        ∫ θ in (0 : ℝ)..α, (1 - r + |θ| / Real.pi)⁻¹ := by
      have hs := intervalIntegral.integral_comp_neg (fun θ : ℝ => (1 - r + |θ| / Real.pi)⁻¹) (a := -α) (b := 0)
      simp only [neg_neg, neg_zero] at hs
      rw [← hs]; exact intervalIntegral.integral_congr fun θ _ => by simp [abs_neg]
    rw [hneg, ← two_mul]; congr 1
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [Set.uIcc_of_le hα_pos.le] at hθ; rw [abs_of_nonneg hθ.1]; ring
  rw [heven_inv, integral_inv_linear (by linarith) (by positivity) hα_pos] at hint_le
  have hlog_bd : Real.log (1 + 1 / Real.pi * α / (1 - r)) ≤ Real.log ((N : ℝ) + 1) := by
    refine Real.log_le_log (by positivity) ?_
    rw [h1mr]
    have hαpi : 1 / Real.pi * α ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ Real.pi_pos]; linarith
    calc 1 + 1 / Real.pi * α / (1 / (N : ℝ)) = 1 + (1 / Real.pi * α) * (N : ℝ) := by field_simp [hN_pos.ne']
      _ ≤ 1 + 1 * (N : ℝ) := by nlinarith
      _ = (N : ℝ) + 1 := by ring
  have hcalc :
      (1 / (2 * Real.pi)) * ((2 * c * (h : ℝ)) * (2 * (Real.log ((N : ℝ) + 1) / (1 / Real.pi)))) =
        2 * c * (h : ℝ) * Real.log ((N : ℝ) + 1) := by field_simp [Real.pi_pos.ne']
  calc (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖(c : ℂ) * zθ θ * (∑ j ∈ Finset.range h, zθ θ ^ j) / (1 - zθ θ)‖)
      ≤ (1 / (2 * Real.pi)) * ((2 * c * (h : ℝ)) * (2 * (Real.log (1 + 1 / Real.pi * α / (1 - r)) / (1 / Real.pi)))) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * ((2 * c * (h : ℝ)) * (2 * (Real.log ((N : ℝ) + 1) / (1 / Real.pi)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog_bd (by positivity)) (by norm_num))
          (by positivity)) (by positivity)
    _ = 2 * c * (h : ℝ) * Real.log ((N : ℝ) + 1) := hcalc

private lemma ef_err_tsum_bound (E : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    {N₀ N : ℕ} (hN₀2 : 2 ≤ N₀) (hN16 : 16 ≤ N)
    (hE_sq : ∀ n ≥ N₀, E n ^ 2 ≤ ε ^ 2 * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)))
    (hratio2 : 2 * ((∑ n ∈ Finset.range N₀, E n ^ 2) + 1) / (ε ^ 2) ≤
      Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))
    (hratio3 : 4 / Real.log 2 ≤ Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) :
    Summable (fun n : ℕ => E n ^ 2 * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) ∧
    (∑' n : ℕ, E n ^ 2 * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) ≤
      5 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
  set r : ℝ := 1 - 1 / (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  have hr_ge : 1 / 2 ≤ r := by
    have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos (by linarith)
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNp1_pos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hsqrt_sum : Summable (fun k : ℕ => Real.sqrt (k : ℝ) * (r ^ 2) ^ k) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      (((hasSum_nat_mul_pow_real hr2_pos.le hr2_lt1).summable.mul_left (1 / (2 * Real.sqrt (N : ℝ)))).add
        ((summable_geometric_of_lt_one hr2_pos.le hr2_lt1).mul_left (Real.sqrt (N : ℝ) / 2)))
    have hamgm : Real.sqrt (k : ℝ) ≤ (1 / (2 * Real.sqrt (N : ℝ))) * (k : ℝ) + Real.sqrt (N : ℝ) / 2 := by
      have h1 : 2 * Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) ≤ (k : ℝ) + (N : ℝ) := by
        nlinarith [sq_nonneg (Real.sqrt (k : ℝ) - Real.sqrt (N : ℝ)),
          Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt hN_pos.le]
      have hsn : 0 < 2 * Real.sqrt (N : ℝ) := by positivity
      have hdiv := div_le_div_of_nonneg_right h1 hsn.le
      have hL : 2 * Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) / (2 * Real.sqrt (N : ℝ)) = Real.sqrt (k : ℝ) := by
        field_simp [hsn.ne']
      have hR : ((k : ℝ) + (N : ℝ)) / (2 * Real.sqrt (N : ℝ)) =
          (1 / (2 * Real.sqrt (N : ℝ))) * (k : ℝ) + Real.sqrt (N : ℝ) / 2 := by
        have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
        field_simp [(Real.sqrt_pos.2 hN_pos).ne']; nlinarith [hsqN]
      linarith
    have := mul_le_mul_of_nonneg_right hamgm (pow_nonneg hr2_pos.le k)
    linarith
  have hE2_sum : Summable (fun n : ℕ => E n ^ 2 * (r ^ 2) ^ n) := by
    rw [← summable_nat_add_iff N₀]
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (((summable_nat_add_iff N₀).2 hsqrt_sum).mul_left (ε ^ 2 / Real.log 2))
    have hlog_ge : Real.log 2 ≤ Real.log ((n + N₀ : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n + N₀))
    have h1 := hE_sq (n + N₀) (Nat.le_add_left N₀ n)
    have h2 : Real.sqrt ((n + N₀ : ℕ) : ℝ) / Real.log ((n + N₀ : ℕ) : ℝ) ≤
        Real.sqrt ((n + N₀ : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hlog2_pos hlog_ge
    calc E (n + N₀) ^ 2 * (r ^ 2) ^ (n + N₀)
        ≤ (ε ^ 2 * (Real.sqrt ((n + N₀ : ℕ) : ℝ) / Real.log 2)) * (r ^ 2) ^ (n + N₀) :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg ε))) (pow_nonneg hr2_pos.le _)
      _ = (ε ^ 2 / Real.log 2) * (Real.sqrt ((n + N₀ : ℕ) : ℝ) * (r ^ 2) ^ (n + N₀)) := by ring
  refine ⟨hE2_sum, ?_⟩
  set M : ℕ := max N₀ (Nat.ceil (Real.sqrt (N : ℝ)))
  rw [← hE2_sum.sum_add_tsum_nat_add M]
  have hsplitM : ∑ n ∈ Finset.range M, E n ^ 2 * (r ^ 2) ^ n =
      (∑ n ∈ Finset.range N₀, E n ^ 2 * (r ^ 2) ^ n) +
      ∑ n ∈ Finset.Ico N₀ M, E n ^ 2 * (r ^ 2) ^ n :=
    (Finset.sum_range_add_sum_Ico _ (le_max_left N₀ _)).symm
  have hpart1 : ∑ n ∈ Finset.range N₀, E n ^ 2 * (r ^ 2) ^ n ≤
      (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
    have h1 : ∑ n ∈ Finset.range N₀, E n ^ 2 * (r ^ 2) ^ n ≤ ∑ n ∈ Finset.range N₀, E n ^ 2 :=
      Finset.sum_le_sum fun n _ => mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hr2_pos.le hr2_lt1.le)
    have h2 : ∑ n ∈ Finset.range N₀, E n ^ 2 ≤ (1 / 2) * ε ^ 2 * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hratio2 (by positivity : 0 ≤ ε ^ 2 / 2)
      have heq1 : (ε ^ 2 / 2) * (2 * ((∑ n ∈ Finset.range N₀, E n ^ 2) + 1) / ε ^ 2) =
          (∑ n ∈ Finset.range N₀, E n ^ 2) + 1 := by field_simp [hε.ne']
      have heq2 : (ε ^ 2 / 2) * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) =
          (1 / 2) * ε ^ 2 * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by ring
      linarith
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    calc ∑ n ∈ Finset.range N₀, E n ^ 2 * (r ^ 2) ^ n
        ≤ (1 / 2) * ε ^ 2 * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := le_trans h1 h2
      _ ≤ (N : ℝ) * ((1 / 2) * ε ^ 2 * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) :=
          le_mul_of_one_le_left (by positivity) hN1
      _ = (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by ring
  have hpart2 : ∑ n ∈ Finset.Ico N₀ M, E n ^ 2 * (r ^ 2) ^ n ≤
      (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
    by_cases hM_eq : M ≤ N₀
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity
    · push Not at hM_eq
      have hM_eq2 : M = Nat.ceil (Real.sqrt (N : ℝ)) := max_eq_right (by omega)
      have hsq4 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
        simpa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)] using
          Real.sqrt_le_sqrt this
      have hM_le : (M : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
        rw [hM_eq2]; linarith [Nat.ceil_lt_add_one (Real.sqrt_nonneg (N : ℝ))]
      have hterm_le : ∀ n ∈ Finset.Ico N₀ M,
          E n ^ 2 * (r ^ 2) ^ n ≤ ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2) := by
        intro n hn; rw [Finset.mem_Ico] at hn
        have hlog_ge : Real.log 2 ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n))
        have hn_le_N : (n : ℝ) ≤ (N : ℝ) := by
          have h1 : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn.2.le
          have h2 : 2 * Real.sqrt (N : ℝ) ≤ (N : ℝ) := by nlinarith [Real.sq_sqrt hN_pos.le]
          linarith
        calc E n ^ 2 * (r ^ 2) ^ n
            ≤ E n ^ 2 := mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hr2_pos.le hr2_lt1.le)
          _ ≤ ε ^ 2 * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)) := hE_sq n hn.1
          _ ≤ ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2) :=
              mul_le_mul_of_nonneg_left (div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hn_le_N) hlog2_pos hlog_ge)
                (sq_nonneg ε)
      calc ∑ n ∈ Finset.Ico N₀ M, E n ^ 2 * (r ^ 2) ^ n
          ≤ ∑ _n ∈ Finset.Ico N₀ M, ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2) := Finset.sum_le_sum hterm_le
        _ = ((M - N₀ : ℕ) : ℝ) * (ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2)) := by simp [Nat.card_Ico]
        _ ≤ (M : ℝ) * (ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le M N₀) (by positivity)
        _ ≤ (2 * Real.sqrt (N : ℝ)) * (ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2)) :=
            mul_le_mul_of_nonneg_right hM_le (by positivity)
        _ = (2 / Real.log 2) * ε ^ 2 * (N : ℝ) := by
            rw [show (2 * Real.sqrt (N : ℝ)) * (ε ^ 2 * (Real.sqrt (N : ℝ) / Real.log 2)) =
              (2 / Real.log 2) * ε ^ 2 * (Real.sqrt (N : ℝ) ^ 2) by ring, Real.sq_sqrt hN_pos.le]
        _ ≤ (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
            have hmul := mul_le_mul_of_nonneg_left hratio3 (by positivity : 0 ≤ (1 / 2) * ε ^ 2 * (N : ℝ))
            have heq1 : (1 / 2) * ε ^ 2 * (N : ℝ) * (4 / Real.log 2) = (2 / Real.log 2) * ε ^ 2 * (N : ℝ) := by ring
            have heq2 : (1 / 2) * ε ^ 2 * (N : ℝ) * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) =
                (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by ring
            linarith
  have hsqrt_tsum_le : ∑' k : ℕ, Real.sqrt (k : ℝ) * (r ^ 2) ^ k ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
    have hle := hsqrt_sum.tsum_le_tsum (fun k => by
      have h1 : 2 * Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) ≤ (k : ℝ) + (N : ℝ) := by
        nlinarith [sq_nonneg (Real.sqrt (k : ℝ) - Real.sqrt (N : ℝ)),
          Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt hN_pos.le]
      have hsn : 0 < 2 * Real.sqrt (N : ℝ) := by positivity
      have hdiv := div_le_div_of_nonneg_right h1 hsn.le
      have hL : 2 * Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) / (2 * Real.sqrt (N : ℝ)) = Real.sqrt (k : ℝ) := by
        field_simp [hsn.ne']
      have hR : ((k : ℝ) + (N : ℝ)) / (2 * Real.sqrt (N : ℝ)) =
          (1 / (2 * Real.sqrt (N : ℝ))) * (k : ℝ) + Real.sqrt (N : ℝ) / 2 := by
        have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
        field_simp [(Real.sqrt_pos.2 hN_pos).ne']; nlinarith [hsqN]
      have := mul_le_mul_of_nonneg_right (by linarith : Real.sqrt (k : ℝ) ≤
        (1 / (2 * Real.sqrt (N : ℝ))) * (k : ℝ) + Real.sqrt (N : ℝ) / 2) (pow_nonneg hr2_pos.le k)
      linarith)
      (((hasSum_nat_mul_pow_real hr2_pos.le hr2_lt1).summable.mul_left (1 / (2 * Real.sqrt (N : ℝ)))).add
        ((summable_geometric_of_lt_one hr2_pos.le hr2_lt1).mul_left (Real.sqrt (N : ℝ) / 2)))
    rw [((hasSum_nat_mul_pow_real hr2_pos.le hr2_lt1).summable.mul_left _).tsum_add
        ((summable_geometric_of_lt_one hr2_pos.le hr2_lt1).mul_left _),
      tsum_mul_left, tsum_mul_left, (hasSum_nat_mul_pow_real hr2_pos.le hr2_lt1).tsum_eq,
      tsum_geometric_of_lt_one hr2_pos.le hr2_lt1] at hle
    have h1mr2_ge : 1 / (N : ℝ) ≤ 1 - r ^ 2 := by
      have : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
      rw [this, h1mr]; nlinarith
    have hinv_le : (1 - r ^ 2)⁻¹ ≤ (N : ℝ) := by
      rw [inv_le_comm₀ (by linarith) hN_pos]; simpa [one_div] using h1mr2_ge
    have hlin_le : r ^ 2 / (1 - r ^ 2) ^ 2 ≤ (N : ℝ) ^ 2 := by
      calc r ^ 2 / (1 - r ^ 2) ^ 2 ≤ 1 / (1 - r ^ 2) ^ 2 := div_le_div_of_nonneg_right hr2_lt1.le (sq_nonneg _)
        _ = ((1 - r ^ 2)⁻¹) ^ 2 := by rw [one_div, inv_pow]
        _ ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 (by linarith)) hinv_le 2
    have hterm1 : (1 / (2 * Real.sqrt (N : ℝ))) * (r ^ 2 / (1 - r ^ 2) ^ 2) ≤ (N : ℝ) * Real.sqrt (N : ℝ) / 2 := by
      calc (1 / (2 * Real.sqrt (N : ℝ))) * (r ^ 2 / (1 - r ^ 2) ^ 2)
          ≤ (1 / (2 * Real.sqrt (N : ℝ))) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hlin_le (by positivity)
        _ = (N : ℝ) * Real.sqrt (N : ℝ) / 2 := by
            have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
            field_simp [(Real.sqrt_pos.2 hN_pos).ne']; nlinarith [hsqN]
    have hterm2 : (Real.sqrt (N : ℝ) / 2) * (1 - r ^ 2)⁻¹ ≤ (N : ℝ) * Real.sqrt (N : ℝ) / 2 := by
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    linarith
  have hpart3 : ∑' n : ℕ, E (n + M) ^ 2 * (r ^ 2) ^ (n + M) ≤
      4 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
    have hlog_tail : ∀ n : ℕ, Real.log ((N : ℝ) + 1) / 4 ≤ Real.log ((n + M : ℕ) : ℝ) := by
      intro n
      have hge_sqrt : Real.sqrt (N : ℝ) ≤ ((n + M : ℕ) : ℝ) := by
        have h1 : Real.sqrt (N : ℝ) ≤ (Nat.ceil (Real.sqrt (N : ℝ)) : ℝ) := Nat.le_ceil _
        have h2 : Nat.ceil (Real.sqrt (N : ℝ)) ≤ n + M := le_trans (le_max_right N₀ _) (Nat.le_add_left M n)
        exact le_trans h1 (by exact_mod_cast h2)
      have hlog1 := Real.log_le_log (Real.sqrt_pos.2 hN_pos) hge_sqrt
      rw [Real.log_sqrt hN_pos.le] at hlog1
      have hlogNp1 : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
        have hle : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by
          have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
          nlinarith
        have := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at this; norm_num at this; linarith
      linarith
    have hstep := ((summable_nat_add_iff M).2 hE2_sum).tsum_le_tsum (fun n => by
      have hnM : N₀ ≤ n + M := le_trans (le_max_left _ _) (Nat.le_add_left M n)
      have hsq := hE_sq (n + M) hnM
      have hdiv : Real.sqrt ((n + M : ℕ) : ℝ) / Real.log ((n + M : ℕ) : ℝ) ≤
          Real.sqrt ((n + M : ℕ) : ℝ) / (Real.log ((N : ℝ) + 1) / 4) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (hlog_tail n)
      have hrew : ε ^ 2 * (Real.sqrt ((n + M : ℕ) : ℝ) / (Real.log ((N : ℝ) + 1) / 4)) * (r ^ 2) ^ (n + M) =
          (4 * ε ^ 2 / Real.log ((N : ℝ) + 1)) * (Real.sqrt ((n + M : ℕ) : ℝ) * (r ^ 2) ^ (n + M)) := by ring
      calc E (n + M) ^ 2 * (r ^ 2) ^ (n + M)
          ≤ (ε ^ 2 * (Real.sqrt ((n + M : ℕ) : ℝ) / Real.log ((n + M : ℕ) : ℝ))) * (r ^ 2) ^ (n + M) :=
            mul_le_mul_of_nonneg_right hsq (pow_nonneg hr2_pos.le _)
        _ ≤ (ε ^ 2 * (Real.sqrt ((n + M : ℕ) : ℝ) / (Real.log ((N : ℝ) + 1) / 4))) * (r ^ 2) ^ (n + M) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv (sq_nonneg ε)) (pow_nonneg hr2_pos.le _)
        _ = (4 * ε ^ 2 / Real.log ((N : ℝ) + 1)) * (Real.sqrt ((n + M : ℕ) : ℝ) * (r ^ 2) ^ (n + M)) := hrew)
      (((summable_nat_add_iff M).2 hsqrt_sum).mul_left (4 * ε ^ 2 / Real.log ((N : ℝ) + 1)))
    rw [tsum_mul_left] at hstep
    have htail_le : ∑' n : ℕ, Real.sqrt ((n + M : ℕ) : ℝ) * (r ^ 2) ^ (n + M) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
      have := hsqrt_sum.sum_add_tsum_nat_add M
      have hnn : 0 ≤ ∑ k ∈ Finset.range M, Real.sqrt (k : ℝ) * (r ^ 2) ^ k := Finset.sum_nonneg fun _ _ => by positivity
      linarith
    calc ∑' n : ℕ, E (n + M) ^ 2 * (r ^ 2) ^ (n + M)
        ≤ (4 * ε ^ 2 / Real.log ((N : ℝ) + 1)) * ((N : ℝ) * Real.sqrt (N : ℝ)) :=
          le_trans hstep (mul_le_mul_of_nonneg_left htail_le (by positivity))
      _ = 4 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by ring
  have h5 : (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) +
      (1 / 2) * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) +
      4 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) =
      5 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by ring
  linarith [hsplitM]

private lemma tendsto_sqrt_div_log_succ_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) atTop atTop := by
  have h1 : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))) atTop atTop := by
    have hs : Tendsto Real.sqrt atTop atTop := tendsto_atTop_atTop.2 fun b =>
      ⟨(max b 0) ^ 2, fun x hx => le_trans (le_max_left b 0)
        (by simpa [Real.sqrt_sq (le_max_right b 0)] using Real.sqrt_le_sqrt hx)⟩
    exact hs.comp (hs.comp (hs.comp tendsto_natCast_atTop_atTop))
  refine tendsto_atTop_mono' atTop ?_ (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 16) h1)
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog_le := log_le_eight_mul_eighth_root (by linarith : (1 : ℝ) ≤ (N : ℝ) + 1)
  have hN16 : Real.sqrt (Real.sqrt (Real.sqrt ((N : ℝ) + 1))) ≤
      2 * Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ))) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have h2le : (N : ℝ) + 1 ≤ 2 ^ 8 * (N : ℝ) := by linarith
    have hr : Real.sqrt (Real.sqrt (Real.sqrt (2 ^ 8 * (N : ℝ)))) =
        2 * Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ))) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_mul (Real.sqrt_nonneg _)]
      have h28 : Real.sqrt (Real.sqrt (Real.sqrt (2 ^ 8 : ℝ))) = 2 := by
        have : (2 ^ 8 : ℝ) = ((2 ^ 2) ^ 2) ^ 2 := by norm_num
        rw [this, Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
      rw [h28]
    exact (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h2le))).trans_eq hr
  have hlog_pos : 0 < Real.log ((N : ℝ) + 1) := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  set u : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))
  have hu4 : u ^ 4 = Real.sqrt (N : ℝ) := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (N : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = Real.sqrt (N : ℝ) := by rw [h1, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have h1_u : (1 : ℝ) ≤ u := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have h2 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h1
    have h3 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (N : ℝ)) := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h2
    have h4 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_one] at h4
    exact h4
  rw [le_div_iff₀ hlog_pos]
  have hlog16 : Real.log ((N : ℝ) + 1) ≤ 16 * u := by linarith
  have hu2 : u ^ 2 ≤ u ^ 4 := by
    have hu12 : u ≤ u ^ 2 := by nlinarith
    nlinarith [sq_nonneg u]
  calc (1 / 16) * u * Real.log ((N : ℝ) + 1)
      ≤ (1 / 16) * u * (16 * u) := mul_le_mul_of_nonneg_left hlog16 (by positivity)
    _ = u ^ 2 := by ring
    _ ≤ Real.sqrt (N : ℝ) := by linarith [hu4]

end ErdosFuchsHelpers

/-- **The Erdős–Fuchs Theorem (1956)** (100% unconditional, pure Mathlib signature):
For every subset `A ⊆ ℕ` and every real constant `c > 0`, it is impossible that
`∑_{n=0}^{N} (1_A * 1_A)(n) = c * N + o(N^{1/4} / √(log N))`. -/
theorem ppl098_erdos_fuchs_1956
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c) :
    ¬ Tendsto
        (fun N : ℕ =>
          ((∑ n ∈ Finset.range (N + 1),
              (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ))
            - c * (N : ℝ)) /
          (((N : ℝ) ^ ((1 : ℝ) / 4)) / Real.sqrt (Real.log (N : ℝ))))
        atTop (nhds 0) := by
  intro hlim
  let E : ℕ → ℝ := fun N => sRep A N - c * (N : ℝ)
  set δ : ℝ := 1 / (128 * Real.pi * Real.sqrt c)
  have hδ_pos : 0 < δ := by positivity
  set ε : ℝ := Real.sqrt c / (128 * Real.pi * (2 * Real.sqrt (5 / (Real.pi * δ)) + 1))
  have hε_pos : 0 < ε := by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε₁ : ℝ := min ε ((c / 4) * Real.sqrt (Real.log 2))
  obtain ⟨N₀', hN₀'⟩ := Metric.tendsto_atTop.1 hlim ε₁ (lt_min hε_pos (by positivity))
  set N₀ : ℕ := max N₀' 2
  have hE_bd : ∀ n ≥ N₀,
      E n ^ 2 ≤ ε ^ 2 * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ∧ |E n| ≤ (c / 4) * (n : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hlogn_ge : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hlogn_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlog2_pos hlogn_ge
    have hscale_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ)) :=
      div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.sqrt_pos.2 hlogn_pos)
    have hd := hN₀' n (le_trans (le_max_left _ _) hn)
    rw [Real.dist_eq, sub_zero] at hd
    have hbd1 : |E n| ≤ ε₁ * ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) := by
      have hmul : |E n / ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ)))| *
          ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) ≤
          ε₁ * ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hd.le hscale_pos.le
      have hdiv : |E n / ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ)))| *
          ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) = |E n| := by
        rw [abs_div, abs_of_pos hscale_pos, div_mul_cancel₀ _ hscale_pos.ne']
      linarith
    constructor
    · have hbd : |E n| ≤ ε * ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) :=
        le_trans hbd1 (mul_le_mul_of_nonneg_right (min_le_left _ _) hscale_pos.le)
      have hsq : E n ^ 2 ≤ ε ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) ^ 2 := by
        rw [← sq_abs, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hbd 2
      have hsc_sq : ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) ^ 2 =
          Real.sqrt (n : ℝ) / Real.log (n : ℝ) := by
        rw [div_pow, Real.sq_sqrt hlogn_pos.le,
          ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul (Nat.cast_nonneg n),
          show ((1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
      rwa [hsc_sq] at hsq
    · have hrpow_le : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num : (1 : ℝ) / 4 ≤ 1)
      calc |E n| ≤ ((c / 4) * Real.sqrt (Real.log 2)) *
              ((n : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (n : ℝ))) :=
            le_trans hbd1 (mul_le_mul_of_nonneg_right (min_le_right _ _) hscale_pos.le)
        _ ≤ ((c / 4) * Real.sqrt (Real.log 2)) * ((n : ℝ) / Real.sqrt (Real.log 2)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div₀ (Nat.cast_nonneg n) hrpow_le (Real.sqrt_pos.2 hlog2_pos) (Real.sqrt_le_sqrt hlogn_ge))
              (by positivity)
        _ = (c / 4) * (n : ℝ) := by field_simp [(Real.sqrt_pos.2 hlog2_pos).ne']
  let CE : ℝ := ∑ n ∈ Finset.range N₀, |E n|
  let CE2 : ℝ := ∑ n ∈ Finset.range N₀, E n ^ 2
  have hcond1 := tendsto_atTop.1 tendsto_sqrt_div_log_succ_atTop
    (max (2 / δ) (max (2 * (CE2 + 1) / (ε ^ 2)) (4 / Real.log 2)))
  have hcond2 := eventually_ge_atTop (max (max N₀ 16) (Nat.ceil (4 * δ ^ 2 + 16 * (CE + 1) / c + 1)))
  obtain ⟨N, hC1, hC2⟩ := (hcond1.and hcond2).exists
  have hN16 : 16 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogNp1_pos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  set r : ℝ := 1 - 1 / (N : ℝ)
  have hr_pos : 0 < r := by
    have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  set h : ℕ := Nat.floor (δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))
  have hh_le_real : (h : ℝ) ≤ δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := Nat.floor_le (by positivity)
  have hh_ge2 : 2 ≤ δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := by
    have hmul := mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) hC1) hδ_pos.le
    have : δ * (2 / δ) = 2 := by field_simp [hδ_pos.ne']
    linarith [show δ * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) =
      δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) by ring]
  have hh_pos_nat : 1 ≤ h := by
    have h2 : 2 ≤ h := Nat.le_floor (by exact_mod_cast hh_ge2)
    omega
  have hh_ge_half : (δ / 2) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) ≤ (h : ℝ) := by
    have hlt := Nat.lt_floor_add_one (δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))
    have hhalf : (δ / 2) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) =
        (δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) / 2 := by ring
    linarith
  have hN_ceil : 4 * δ ^ 2 + 16 * (CE + 1) / c + 1 ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hC2)
  have hh_le_halfN : (h : ℝ) ≤ (N : ℝ) / 2 := by
    have hCE_nn : 0 ≤ CE := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hN_big : 4 * δ ^ 2 ≤ (N : ℝ) := by
      have : 0 ≤ 16 * (CE + 1) / c := by positivity
      linarith
    have hlog1 : 1 ≤ Real.log ((N : ℝ) + 1) := by
      have : Real.exp 1 ≤ (N : ℝ) + 1 := by
        have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
        linarith
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
    have hδ_le : δ * Real.sqrt (N : ℝ) ≤ (N : ℝ) / 2 := by
      have hsq : (δ * Real.sqrt (N : ℝ)) ^ 2 ≤ ((N : ℝ) / 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hN_pos.le]; nlinarith
      nlinarith [mul_nonneg hδ_pos.le (Real.sqrt_nonneg (N : ℝ))]
    calc (h : ℝ) ≤ δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1) := hh_le_real
      _ ≤ δ * Real.sqrt (N : ℝ) / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one hlog1
      _ ≤ (N : ℝ) / 2 := by rw [div_one]; exact hδ_le
  set α : ℝ := 1 / (2 * (h : ℝ))
  have hα_pos : 0 < α := by positivity
  have hα_le_pi : α ≤ Real.pi := by
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos_nat
    have : α ≤ 1 / 2 := by dsimp only [α]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith [Real.pi_gt_three]
  -- Assemble the 3 bounds from modular helpers
  let zθ : ℝ → ℂ := fun θ => (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hzθ_norm : ∀ θ : ℝ, ‖zθ θ‖ = r := fun θ => by
    dsimp only [zθ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_pos.le, norm_exp_I_mul_real, mul_one]
  let f : ℂ → ℂ := fun z => ∑' n : ℕ, (indA A n : ℂ) * z ^ n
  let geomH : ℂ → ℂ := fun z => ∑ j ∈ Finset.range h, z ^ j
  let d : ℕ → ℝ := fun n => E n - if h ≤ n then E (n - h) else 0
  let g : ℂ → ℂ := fun z => ∑' n : ℕ, (d n : ℂ) * z ^ n
  have hf_cont : Continuous (fun θ : ℝ => f (zθ θ)) := by
    have hsum_w : Summable (fun n : ℕ => ‖((indA A n * r ^ n : ℝ) : ℂ)‖) := by
      have h0 := summable_indA_pow A (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
      refine h0.congr fun n => ?_; simp [norm_pow, Complex.norm_real, abs_of_nonneg hr_pos.le]
    refine (continuous_tsum_fourier (fun n => ((indA A n * r ^ n : ℝ) : ℂ)) hsum_w).congr fun θ => ?_
    dsimp only [f, zθ]; congr 1; funext n; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
  have hg_cont : Continuous (fun θ : ℝ => g (zθ θ)) := by
    have hsum_d : Summable (fun n : ℕ => ‖((d n * r ^ n : ℝ) : ℂ)‖) := by
      have h0 := summable_efDiff_pow A c h (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
      refine h0.congr fun n => ?_; simp [d, E, norm_pow, Complex.norm_real, abs_of_nonneg hr_pos.le]
    refine (continuous_tsum_fourier (fun n => ((d n * r ^ n : ℝ) : ℂ)) hsum_d).congr fun θ => ?_
    dsimp only [g, zθ]; congr 1; funext n; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
  -- 1. Lower bound on J = (1/(2π)) ∫_{-α}^{α} ‖f‖^2 * ‖geomH‖
  have hfr2_ge := ef_fr2_lower A hc hN16 (fun n hn => (hE_bd n hn).2) (by linarith [sq_nonneg δ])
  set J : ℝ := (1 / (2 * Real.pi)) * ∫ θ in (-α)..α, ‖f (zθ θ)‖ ^ 2 * ‖geomH (zθ θ)‖
  have hJ_lower : (Real.sqrt c / (32 * Real.pi)) * Real.sqrt (N : ℝ) ≤ J := by
    have hgeomH_cont : Continuous (fun θ : ℝ => geomH (zθ θ)) := by dsimp only [geomH, zθ]; fun_prop
    have hint_ge : ((h : ℝ) / 4) * (∫ θ in (-α)..α, ‖f (zθ θ)‖ ^ 2) ≤
        ∫ θ in (-α)..α, ‖f (zθ θ)‖ ^ 2 * ‖geomH (zθ θ)‖ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.mul (hf_cont.norm.pow 2)).intervalIntegrable _ _)
        (((hf_cont.norm.pow 2).mul hgeomH_cont.norm).intervalIntegrable _ _)
        fun θ hθ => ?_
      have hhr : 1 / 2 ≤ 1 - (h : ℝ) * (1 - r) := by
        rw [h1mr]; have : (h : ℝ) * (1 / (N : ℝ)) ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ hN_pos]; linarith
        linarith
      have hlow := norm_geom_sum_lower hr_pos hr_lt1 hh_pos_nat hhr (abs_le.2 hθ)
      calc (h : ℝ) / 4 * ‖f (zθ θ)‖ ^ 2 = ‖f (zθ θ)‖ ^ 2 * ((h : ℝ) / 4) := mul_comm _ _
        _ ≤ ‖f (zθ θ)‖ ^ 2 * ‖geomH (zθ θ)‖ := mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
    let w : ℕ → ℝ := fun n => indA A n * r ^ n
    have hw_nn : ∀ n, 0 ≤ w n := fun n => mul_nonneg (indA_nonneg A n) (pow_nonneg hr_pos.le n)
    have hw_sum : Summable w := Summable.of_nonneg_of_le hw_nn
      (fun n => mul_le_of_le_one_left (pow_nonneg hr_pos.le n) (indA_le_one A n))
      (summable_geometric_of_lt_one hr_pos.le hr_lt1)
    have htb := ppl098_triangle_bump_positivity w hw_nn hw_sum hα_pos
    have htb_eq : (∫ θ in (-α)..α, ‖∑' n : ℕ, (w n : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2) =
        ∫ θ in (-α)..α, ‖f (zθ θ)‖ ^ 2 :=
      intervalIntegral.integral_congr fun θ _ => by
        congr 2; dsimp only [f, zθ, w]; congr 1; funext n; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
    have hwsq_eq : (∑' n : ℕ, w n ^ 2) = ∑' n : ℕ, indA A n * (r ^ 2) ^ n := by
      congr 1; funext n; dsimp only [w]; rw [mul_pow, indA_sq, ← pow_mul, mul_comm n 2, pow_mul]
    rw [htb_eq, hwsq_eq] at htb
    have hJ1 : (1 / (2 * Real.pi)) * (((h : ℝ) / 4) * (α * ((Real.sqrt c / 2) * Real.sqrt (N : ℝ)))) ≤ J := by
      refine mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left
        (le_trans (mul_le_mul_of_nonneg_left hfr2_ge hα_pos.le) htb) (by positivity)) hint_ge) (by positivity)
    have hconst : (1 / (2 * Real.pi)) * (((h : ℝ) / 4) * (α * ((Real.sqrt c / 2) * Real.sqrt (N : ℝ)))) =
        (Real.sqrt c / (32 * Real.pi)) * Real.sqrt (N : ℝ) := by
      dsimp only [α]; field_simp [(by positivity : (h : ℝ) ≠ 0), Real.pi_pos.ne']; ring
    linarith
  -- 2. Split J ≤ Terr + Tmain
  have h1zθ_ne : ∀ θ : ℝ, 1 - zθ θ ≠ 0 := fun θ h0 => by
    have hz1 : zθ θ = 1 := (sub_eq_zero.1 h0).symm
    have := hzθ_norm θ; rw [hz1, norm_one] at this; linarith
  have hmain_cont : Continuous (fun θ : ℝ => ‖(c : ℂ) * zθ θ * geomH (zθ θ) / (1 - zθ θ)‖) :=
    (Continuous.div (by dsimp only [geomH, zθ]; fun_prop) (by dsimp only [zθ]; fun_prop) h1zθ_ne).norm
  have hgeomH_cont2 : Continuous (fun θ : ℝ => geomH (zθ θ)) := by dsimp only [geomH, zθ]; fun_prop
  have hJ_split : J ≤ (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖g (zθ θ)‖) +
      (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖(c : ℂ) * zθ θ * geomH (zθ θ) / (1 - zθ θ)‖) := by
    dsimp only [J]
    rw [← mul_add, ← intervalIntegral.integral_add (hg_cont.norm.intervalIntegrable _ _) (hmain_cont.intervalIntegrable _ _)]
    refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on (by linarith)
      (((hf_cont.norm.pow 2).mul hgeomH_cont2.norm).intervalIntegrable _ _)
      ((hg_cont.norm.add hmain_cont).intervalIntegrable _ _) fun θ _ => ?_) (by positivity)
    have hzlt : ‖zθ θ‖ < 1 := by rw [hzθ_norm θ]; exact hr_lt1
    have hnorm : ‖f (zθ θ)‖ ^ 2 * ‖geomH (zθ θ)‖ = ‖f (zθ θ) ^ 2 * geomH (zθ θ)‖ := by rw [norm_mul, norm_pow]
    rw [hnorm, ef_power_series_ident A c h hzlt]
    exact norm_add_le _ _
  -- 3. Main-term upper bound ≤ (√c / (64π)) √N
  have hTmain_le : (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖(c : ℂ) * zθ θ * geomH (zθ θ) / (1 - zθ θ)‖) ≤
      (Real.sqrt c / (64 * Real.pi)) * Real.sqrt (N : ℝ) := by
    have h1 := ef_main_integral_upper (h := h) hc hN16 hα_pos hα_le_pi
    have h2 : 2 * c * (h : ℝ) * Real.log ((N : ℝ) + 1) ≤ (Real.sqrt c / (64 * Real.pi)) * Real.sqrt (N : ℝ) := by
      calc 2 * c * (h : ℝ) * Real.log ((N : ℝ) + 1)
          ≤ 2 * c * (δ * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) * Real.log ((N : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh_le_real (by positivity)) hlogNp1_pos.le
        _ = 2 * c * δ * Real.sqrt (N : ℝ) := by field_simp [hlogNp1_pos.ne']
        _ = (Real.sqrt c / (64 * Real.pi)) * Real.sqrt (N : ℝ) := by
            dsimp only [δ]; have hsc : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
            field_simp [Real.pi_pos.ne', hsc]; nlinarith [Real.mul_self_sqrt hc.le]
    exact le_trans h1 h2
  -- 4. Error-term upper bound < (√c / (64π)) √N
  have hE2_bd := ef_err_tsum_bound E hε_pos (le_max_right _ _) hN16 (fun n hn => (hE_bd n hn).1)
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC1)
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC1)
  have hTerr_lt : (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖g (zθ θ)‖) <
      (Real.sqrt c / (64 * Real.pi)) * Real.sqrt (N : ℝ) := by
    have hcs := intervalIntegral_cauchy_schwarz (a := -α) (b := α) (by linarith)
      (u := fun _ => (1 : ℝ)) (v := fun θ => ‖g (zθ θ)‖) continuous_const hg_cont.norm
    simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_neg_eq_add] at hcs
    have hsub_int : (∫ θ in (-α)..α, ‖g (zθ θ)‖ ^ 2) ≤ ∫ θ in (-Real.pi)..Real.pi, ‖g (zθ θ)‖ ^ 2 := by
      have hcont2 : Continuous (fun θ : ℝ => ‖g (zθ θ)‖ ^ 2) := hg_cont.norm.pow 2
      have h1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont2.intervalIntegrable (-Real.pi) (-α)) (hcont2.intervalIntegrable (-α) α)).symm
      have h2 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont2.intervalIntegrable (-Real.pi) α) (hcont2.intervalIntegrable α Real.pi)).symm
      have hnn1 : 0 ≤ ∫ θ in (-Real.pi)..(-α), ‖g (zθ θ)‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
      have hnn2 : 0 ≤ ∫ θ in α..Real.pi, ‖g (zθ θ)‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
      linarith
    have hsum_d : Summable (fun n : ℕ => ‖((d n * r ^ n : ℝ) : ℂ)‖) := by
      have h0 := summable_efDiff_pow A c h (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
      refine h0.congr fun n => ?_; simp [d, E, norm_pow, Complex.norm_real, abs_of_nonneg hr_pos.le]
    have hpars_eq : (∫ θ in (-Real.pi)..Real.pi, ‖g (zθ θ)‖ ^ 2) =
        (2 * Real.pi) * ∑' n : ℕ, d n ^ 2 * (r ^ 2) ^ n := by
      have hL : (∫ θ in (-Real.pi)..Real.pi, ‖g (zθ θ)‖ ^ 2) =
          ∫ θ in (-Real.pi)..Real.pi,
            ‖∑' n : ℕ, ((d n * r ^ n : ℝ) : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 :=
        intervalIntegral.integral_congr fun θ _ => by
          congr 2; dsimp only [g, zθ]; congr 1; funext n; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
      rw [hL, ppl098_radial_parseval _ hsum_d]
      congr 1; congr 1; funext n
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
    have hr2_lt1 : r ^ 2 < 1 := by nlinarith
    have hd2_le : (∑' n : ℕ, d n ^ 2 * (r ^ 2) ^ n) ≤ 4 * ∑' n : ℕ, E n ^ 2 * (r ^ 2) ^ n := by
      have hshift_sum : Summable (fun n : ℕ => (if h ≤ n then E (n - h) else 0) ^ 2 * (r ^ 2) ^ n) := by
        rw [← summable_nat_add_iff h]
        have heq : (fun n : ℕ => (if h ≤ n + h then E (n + h - h) else 0) ^ 2 * (r ^ 2) ^ (n + h)) =
            fun n : ℕ => (r ^ 2) ^ h * (E n ^ 2 * (r ^ 2) ^ n) := by
          funext n; simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]; ring
        rw [heq]; exact hE2_bd.1.mul_left _
      have hd2_sum : Summable (fun n : ℕ => d n ^ 2 * (r ^ 2) ^ n) :=
        Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
          dsimp only [d]; nlinarith [sq_nonneg (E n + if h ≤ n then E (n - h) else 0), pow_nonneg hr2_pos.le n])
          ((hE2_bd.1.mul_left 2).add (hshift_sum.mul_left 2))
      have hshift_val : (∑' n : ℕ, (if h ≤ n then E (n - h) else 0) ^ 2 * (r ^ 2) ^ n) =
          (r ^ 2) ^ h * ∑' n : ℕ, E n ^ 2 * (r ^ 2) ^ n := by
        rw [← hshift_sum.sum_add_tsum_nat_add h]
        have h0 : ∑ n ∈ Finset.range h, (if h ≤ n then E (n - h) else 0) ^ 2 * (r ^ 2) ^ n = 0 :=
          Finset.sum_eq_zero fun n hn => by have : ¬(h ≤ n) := by rw [Finset.mem_range] at hn; omega
                                            simp [this]
        rw [h0, zero_add]
        have heq : (fun n : ℕ => (if h ≤ n + h then E (n + h - h) else 0) ^ 2 * (r ^ 2) ^ (n + h)) =
            fun n : ℕ => (r ^ 2) ^ h * (E n ^ 2 * (r ^ 2) ^ n) := by
          funext n; simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]; ring
        rw [heq, tsum_mul_left]
      have hstep := hd2_sum.tsum_le_tsum (fun n => by
        dsimp only [d]; nlinarith [sq_nonneg (E n + if h ≤ n then E (n - h) else 0), pow_nonneg hr2_pos.le n])
        ((hE2_bd.1.mul_left 2).add (hshift_sum.mul_left 2))
      rw [(hE2_bd.1.mul_left 2).tsum_add (hshift_sum.mul_left 2), tsum_mul_left, tsum_mul_left, hshift_val] at hstep
      have hE2_nn : 0 ≤ ∑' n : ℕ, E n ^ 2 * (r ^ 2) ^ n := tsum_nonneg fun _ => by positivity
      nlinarith [pow_le_one₀ hr2_pos.le hr2_lt1.le (n := h)]
    have hα_le : α ≤ Real.log ((N : ℝ) + 1) / (δ * Real.sqrt (N : ℝ)) := by
      dsimp only [α]; rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmul := mul_le_mul_of_nonneg_left hh_ge_half (by positivity : 0 ≤ 2 * Real.log ((N : ℝ) + 1))
      have heq : 2 * Real.log ((N : ℝ) + 1) * ((δ / 2) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) =
          δ * Real.sqrt (N : ℝ) := by field_simp [hlogNp1_pos.ne']
      linarith
    have hsq_err : ((1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖g (zθ θ)‖)) ^ 2 ≤
        (4 * (5 / (Real.pi * δ)) * ε ^ 2) * (N : ℝ) := by
      have h1 : (∫ θ in (-α)..α, ‖g (zθ θ)‖) ^ 2 ≤
          (2 * α) * ((2 * Real.pi) * (4 * (5 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)))) :=
        calc (∫ θ in (-α)..α, ‖g (zθ θ)‖) ^ 2
            ≤ (α + α) * (∫ θ in (-α)..α, ‖g (zθ θ)‖ ^ 2) := hcs
          _ = (2 * α) * (∫ θ in (-α)..α, ‖g (zθ θ)‖ ^ 2) := by ring
          _ ≤ (2 * α) * (∫ θ in (-Real.pi)..Real.pi, ‖g (zθ θ)‖ ^ 2) := mul_le_mul_of_nonneg_left hsub_int (by positivity)
          _ = (2 * α) * ((2 * Real.pi) * ∑' n : ℕ, d n ^ 2 * (r ^ 2) ^ n) := by rw [hpars_eq]
          _ ≤ (2 * α) * ((2 * Real.pi) * (4 * ∑' n : ℕ, E n ^ 2 * (r ^ 2) ^ n)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd2_le (by positivity)) (by positivity)
          _ ≤ (2 * α) * ((2 * Real.pi) * (4 * (5 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hE2_bd.2 (by norm_num)) (by positivity)) (by positivity)
      rw [mul_pow]
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (1 / (2 * Real.pi)))
      have h3 : (1 / (2 * Real.pi)) ^ 2 *
            ((2 * α) * ((2 * Real.pi) * (4 * (5 * ε ^ 2 * (N : ℝ) * Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))))) =
          (4 * (5 / Real.pi) * ε ^ 2) * (α * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))) * (N : ℝ) := by
        field_simp [Real.pi_pos.ne', hlogNp1_pos.ne']
      have h4 : α * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) ≤ 1 / δ := by
        calc α * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))
            ≤ (Real.log ((N : ℝ) + 1) / (δ * Real.sqrt (N : ℝ))) * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hα_le (by positivity)
          _ = 1 / δ := by field_simp [hlogNp1_pos.ne', hδ_pos.ne', (Real.sqrt_pos.2 hN_pos).ne']
      calc (1 / (2 * Real.pi)) ^ 2 * (∫ θ in (-α)..α, ‖g (zθ θ)‖) ^ 2
          ≤ (4 * (5 / Real.pi) * ε ^ 2) * (α * (Real.sqrt (N : ℝ) / Real.log ((N : ℝ) + 1))) * (N : ℝ) := by linarith
        _ ≤ (4 * (5 / Real.pi) * ε ^ 2) * (1 / δ) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by positivity)) hN_pos.le
        _ = (4 * (5 / (Real.pi * δ)) * ε ^ 2) * (N : ℝ) := by ring
    have hTerr_le : (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖g (zθ θ)‖) ≤
        (2 * Real.sqrt (5 / (Real.pi * δ)) * ε) * Real.sqrt (N : ℝ) := by
      have hsqR : ((2 * Real.sqrt (5 / (Real.pi * δ)) * ε) * Real.sqrt (N : ℝ)) ^ 2 =
          (4 * (5 / (Real.pi * δ)) * ε ^ 2) * (N : ℝ) := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hN_pos.le]; ring
      have hnnL : 0 ≤ (1 / (2 * Real.pi)) * (∫ θ in (-α)..α, ‖g (zθ θ)‖) :=
        mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _)
      nlinarith [show 0 ≤ (2 * Real.sqrt (5 / (Real.pi * δ)) * ε) * Real.sqrt (N : ℝ) by positivity]
    have hε_strict : 2 * Real.sqrt (5 / (Real.pi * δ)) * ε < Real.sqrt c / (64 * Real.pi) := by
      dsimp only [ε]
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
      have hscpi : 0 < Real.sqrt c * Real.pi := mul_pos (Real.sqrt_pos.2 hc) Real.pi_pos
      have hsqnn : 0 ≤ Real.sqrt (5 / (Real.pi * δ)) := Real.sqrt_nonneg _
      nlinarith
    exact lt_of_le_of_lt hTerr_le (mul_lt_mul_of_pos_right hε_strict (Real.sqrt_pos.2 hN_pos))
  have hsum32 : (Real.sqrt c / (64 * Real.pi)) * Real.sqrt (N : ℝ) +
      (Real.sqrt c / (64 * Real.pi)) * Real.sqrt (N : ℝ) =
      (Real.sqrt c / (32 * Real.pi)) * Real.sqrt (N : ℝ) := by ring
  linarith

/-- **Corollary (No Eventually Constant Representation Function)**:
For every `A ⊆ ℕ` and every `c > 0`, it is impossible that `(1_A * 1_A)(n) = c` for all
sufficiently large `n`. -/
theorem ppl098_no_eventually_constant_rep
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c) :
    ¬ (∀ᶠ n : ℕ in atTop,
        (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ) = c) := by
  intro hev
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  apply ppl098_erdos_fuchs_1956 A hc
  let C : ℝ := (∑ n ∈ Finset.range N₀, (rRep A n : ℝ)) - c * ((N₀ : ℝ) - 1)
  have hdiff_eq : ∀ N ≥ N₀,
      (∑ n ∈ Finset.range (N + 1),
        (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)) - c * (N : ℝ) = C := by
    intro N hN
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : N₀ ≤ N + 1)]
    have htail : ∑ n ∈ Finset.Ico N₀ (N + 1),
        (((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ) =
        ((N + 1 - N₀ : ℕ) : ℝ) * c := by
      rw [Finset.sum_congr rfl fun n hn => hN₀ n (Finset.mem_Ico.1 hn).1]
      simp [Nat.card_Ico]
    rw [htail, Nat.cast_sub (by omega : N₀ ≤ N + 1)]
    push_cast; dsimp only [C, rRep]; ring
  have hscale_inf : Tendsto (fun N : ℕ => ((N : ℝ) ^ ((1 : ℝ) / 4)) / Real.sqrt (Real.log (N : ℝ)))
      atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))) atTop atTop := by
      have hs : Tendsto Real.sqrt atTop atTop := tendsto_atTop_atTop.2 fun b =>
        ⟨(max b 0) ^ 2, fun x hx => le_trans (le_max_left b 0)
          (by simpa [Real.sqrt_sq (le_max_right b 0)] using Real.sqrt_le_sqrt hx)⟩
      exact hs.comp (hs.comp (hs.comp tendsto_natCast_atTop_atTop))
    refine tendsto_atTop_mono' atTop ?_ (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 8) h1)
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlog_le := log_le_eight_mul_eighth_root hN1
    set u : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))
    have hu1 : 1 ≤ u := by
      have h2 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
      have h3 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (N : ℝ)) := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h2
      have h4 := Real.sqrt_le_sqrt h3
      rw [Real.sqrt_one] at h4
      exact h4
    have hsqrt_le : Real.sqrt (Real.log (N : ℝ)) ≤ 8 * u := by
      have h1 : Real.log (N : ℝ) ≤ (8 * u) ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))
    have hrpow_eq : (N : ℝ) ^ ((1 : ℝ) / 4) = u ^ 2 := by
      have hu2 : u ^ 2 = Real.sqrt (Real.sqrt (N : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
      rw [hu2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    rw [hrpow_eq, le_div_iff₀ (Real.sqrt_pos.2 hlog_pos)]
    calc (1 / 8) * u * Real.sqrt (Real.log (N : ℝ))
        ≤ (1 / 8) * u * (8 * u) := mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
      _ = u ^ 2 := by ring
  refine (tendsto_const_nhds (x := C)).div_atTop hscale_inf |>.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [hdiff_eq N hN]

/-! ## Part IV: Quantitative Erdős–Sárközy Impossibility Barrier for Erdős Problem #66 -/

section ErdosSarkozyHelpers

private lemma es_S1_lower {N : ℕ} (hN64 : 64 ≤ N) :
    Summable (fun n : ℕ => Real.log (n : ℝ) * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) ∧
    (1 / 64) * (N : ℝ) * Real.log (N : ℝ) ≤
      ∑' n : ℕ, Real.log (n : ℝ) * ((1 - 1 / (N : ℝ)) ^ 2) ^ n := by
  set r : ℝ := 1 - 1 / (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hr_pos : 0 < r := by
    have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have hS1_sum : Summable (fun n : ℕ => Real.log (n : ℝ) * (r ^ 2) ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (hasSum_nat_mul_pow_real hr2_pos.le hr2_lt1).summable
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0)))
          (pow_nonneg hr2_pos.le n)
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · exact mul_le_mul_of_nonneg_right
          (le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)) (pow_nonneg hr2_pos.le n)
  refine ⟨hS1_sum, ?_⟩
  have hlow_sum : ∑ n ∈ Finset.Ico (N / 2) N, Real.log (n : ℝ) * (r ^ 2) ^ n ≤
      ∑' n : ℕ, Real.log (n : ℝ) * (r ^ 2) ^ n := by
    have hsub : Finset.Ico (N / 2) N ⊆ Finset.range N := fun n hn =>
      Finset.mem_range.2 (Finset.mem_Ico.1 hn).2
    have hnn : ∀ n : ℕ, 0 ≤ Real.log (n : ℝ) * (r ^ 2) ^ n := fun n => by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0)))
          (pow_nonneg hr2_pos.le n)
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hnn _)
      (hS1_sum.sum_le_tsum _ fun _ _ => hnn _)
  have hr2N_ge : (1 / 16 : ℝ) ≤ (r ^ 2) ^ N := by
    have h1 : Real.exp (-(5 / (4 * (N : ℝ)))) ≤ r := by
      have he := Real.add_one_le_exp (5 / (4 * (N : ℝ)))
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hr_pos]
      dsimp only [r]
      have hN64R : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
      have hinv : (1 - 1 / (N : ℝ))⁻¹ ≤ 5 / (4 * (N : ℝ)) + 1 := by
        rw [inv_le_iff_one_le_mul₀ (by positivity), mul_comm]
        have hmul : (1 - 1 / (N : ℝ)) * (5 / (4 * (N : ℝ)) + 1) =
            1 + (1 - 5 / (N : ℝ)) / (4 * (N : ℝ)) := by field_simp [hN_pos.ne']; ring
        rw [hmul]
        have : 5 / (N : ℝ) ≤ 1 := (div_le_one hN_pos).2 (by linarith)
        have : 0 ≤ (1 - 5 / (N : ℝ)) / (4 * (N : ℝ)) := div_nonneg (by linarith) (by positivity)
        linarith
      linarith
    have h2 := pow_le_pow_left₀ (Real.exp_pos _).le h1 (2 * N)
    rw [← Real.exp_nat_mul, show ((2 * N : ℕ) : ℝ) * -(5 / (4 * (N : ℝ))) = -(5 / 2) by
      push_cast; field_simp [hN_pos.ne']; ring, show r ^ (2 * N) = (r ^ 2) ^ N by rw [pow_mul]] at h2
    have hexp52 : (1 / 16 : ℝ) ≤ Real.exp (-(5 / 2 : ℝ)) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos _)]
      have hsq : (Real.exp (5 / 2 : ℝ)) ^ 2 ≤ 16 ^ 2 := by
        rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (5 / 2) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
        have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have h5 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 5
        linarith [show (2.72 : ℝ) ^ 5 < 16 ^ 2 by norm_num]
      nlinarith [Real.exp_pos (5 / 2 : ℝ)]
    linarith
  have hterm_ge : ∀ n ∈ Finset.Ico (N / 2) N,
      (Real.log (N : ℝ) / 2) * (1 / 16) ≤ Real.log (n : ℝ) * (r ^ 2) ^ n := by
    intro n hn; rw [Finset.mem_Ico] at hn
    have hlog_ge : Real.log (N : ℝ) / 2 ≤ Real.log (n : ℝ) := by
      have hN_le : (N : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h1 : (N : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast (by omega : N ≤ 2 * n + 1)
        have h2 : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 32 ≤ n)
        nlinarith
      have h := Real.log_le_log hN_pos hN_le
      rw [Real.log_pow] at h; norm_num at h; linarith
    exact mul_le_mul hlog_ge (le_trans hr2N_ge (pow_le_pow_of_le_one hr2_pos.le hr2_lt1.le hn.2.le))
      (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  have hcard : (N : ℝ) / 2 ≤ ((N - N / 2 : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ 2 * ((N - N / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ 2 * (N - N / 2))
    linarith
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  calc (1 / 64) * (N : ℝ) * Real.log (N : ℝ)
      = ((N : ℝ) / 2) * ((Real.log (N : ℝ) / 2) * (1 / 16)) := by ring
    _ ≤ ((N - N / 2 : ℕ) : ℝ) * ((Real.log (N : ℝ) / 2) * (1 / 16)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ _n ∈ Finset.Ico (N / 2) N, (Real.log (N : ℝ) / 2) * (1 / 16) := by simp [Nat.card_Ico]
    _ ≤ ∑ n ∈ Finset.Ico (N / 2) N, Real.log (n : ℝ) * (r ^ 2) ^ n := Finset.sum_le_sum hterm_ge
    _ ≤ ∑' n : ℕ, Real.log (n : ℝ) * (r ^ 2) ^ n := hlow_sum

private lemma es_log2_sq_upper {N : ℕ} (hN64 : 64 ≤ N) :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 2) ^ 2 * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) ∧
    (∑' n : ℕ, Real.log ((n : ℝ) + 2) ^ 2 * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) ≤
      12 * (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  set r : ℝ := 1 - 1 / (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  have hr_pos : 0 < r := by
    have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have hpt : ∀ n : ℕ, Real.log ((n : ℝ) + 2) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 + 4 * ((n : ℝ) / (N : ℝ)) ^ 2 := by
    intro n
    have hlog_le : Real.log ((n : ℝ) + 2) ≤ Real.log (N : ℝ) + (n : ℝ) / (N : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < ((n : ℝ) + 2) / (N : ℝ))
      rw [Real.log_div (by positivity) hN_pos.ne', add_div] at h1
      have h2 : 2 / (N : ℝ) ≤ 1 := (div_le_one hN_pos).2 (by exact_mod_cast (by omega : 2 ≤ N))
      linarith
    have hsq := pow_le_pow_left₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])) hlog_le 2
    nlinarith [sq_nonneg (Real.log (N : ℝ) - (n : ℝ) / (N : ℝ))]
  have hgeom := summable_geometric_of_lt_one hr2_pos.le hr2_lt1
  have hsqN := summable_sq_nat_mul_pow_real hr2_pos.le hr2_lt1
  have hsum : Summable (fun n : ℕ => Real.log ((n : ℝ) + 2) ^ 2 * (r ^ 2) ^ n) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
      have := mul_le_mul_of_nonneg_right (hpt n) (pow_nonneg hr2_pos.le n)
      calc Real.log ((n : ℝ) + 2) ^ 2 * (r ^ 2) ^ n
          ≤ (4 * Real.log (N : ℝ) ^ 2 + 4 * ((n : ℝ) / (N : ℝ)) ^ 2) * (r ^ 2) ^ n := this
        _ = 4 * Real.log (N : ℝ) ^ 2 * (r ^ 2) ^ n + 4 / (N : ℝ) ^ 2 * ((n : ℝ) ^ 2 * (r ^ 2) ^ n) := by
            rw [div_pow]; ring)
      ((hgeom.mul_left (4 * Real.log (N : ℝ) ^ 2)).add (hsqN.1.mul_left (4 / (N : ℝ) ^ 2)))
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum (fun n => by
    have := mul_le_mul_of_nonneg_right (hpt n) (pow_nonneg hr2_pos.le n)
    calc Real.log ((n : ℝ) + 2) ^ 2 * (r ^ 2) ^ n
        ≤ (4 * Real.log (N : ℝ) ^ 2 + 4 * ((n : ℝ) / (N : ℝ)) ^ 2) * (r ^ 2) ^ n := this
      _ = 4 * Real.log (N : ℝ) ^ 2 * (r ^ 2) ^ n + 4 / (N : ℝ) ^ 2 * ((n : ℝ) ^ 2 * (r ^ 2) ^ n) := by
          rw [div_pow]; ring)
    ((hgeom.mul_left (4 * Real.log (N : ℝ) ^ 2)).add (hsqN.1.mul_left (4 / (N : ℝ) ^ 2)))
  rw [(hgeom.mul_left _).tsum_add (hsqN.1.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hr2_pos.le hr2_lt1] at hle
  have h1mr2_ge : 1 / (N : ℝ) ≤ 1 - r ^ 2 := by
    have : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [this, h1mr]; nlinarith
  have hinv_le : (1 - r ^ 2)⁻¹ ≤ (N : ℝ) := by
    rw [inv_le_comm₀ (by linarith) hN_pos]; simpa [one_div] using h1mr2_ge
  have hcube_le : 3 / (1 - r ^ 2) ^ 3 ≤ 3 * (N : ℝ) ^ 3 := by
    have h1 := pow_le_pow_left₀ (inv_nonneg.2 (by linarith : 0 ≤ 1 - r ^ 2)) hinv_le 3
    rw [div_eq_mul_inv, ← inv_pow]; nlinarith
  have h1 : 4 * Real.log (N : ℝ) ^ 2 * (1 - r ^ 2)⁻¹ ≤ 4 * (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ))]
  have h2 : 4 / (N : ℝ) ^ 2 * (∑' n : ℕ, (n : ℝ) ^ 2 * (r ^ 2) ^ n) ≤ 12 * (N : ℝ) := by
    calc 4 / (N : ℝ) ^ 2 * (∑' n : ℕ, (n : ℝ) ^ 2 * (r ^ 2) ^ n)
        ≤ 4 / (N : ℝ) ^ 2 * (3 * (N : ℝ) ^ 3) := mul_le_mul_of_nonneg_left (hsqN.2.trans hcube_le) (by positivity)
      _ = 12 * (N : ℝ) := by field_simp [hN_pos.ne']; ring
  have hlog2_ge : 2 ≤ Real.log (N : ℝ) ^ 2 := by
    have h64 : Real.exp 2 ≤ (N : ℝ) := by
      have h1e : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h2e : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h3 : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
      nlinarith [Real.exp_pos 1]
    have hlog2N : 2 ≤ Real.log (N : ℝ) := by simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) h64
    nlinarith
  nlinarith

private lemma es_fr2_lower (A : Set ℕ) [DecidablePred (· ∈ A)] {c ν : ℝ} {N₁ N : ℕ}
    (hc : 0 < c) (hν_pos : 0 < ν) (hν_le : ν ≤ 1 / 4) (hN64 : 64 ≤ N)
    (hrRep_lower : ∀ n ≥ N₁, (1 - ν / 2) * c * Real.log (n : ℝ) ≤ (rRep A n : ℝ))
    (hC_small : (∑ n ∈ Finset.range N₁, c * Real.log ((n : ℝ) + 2)) ≤
      (ν / 2) * c * (∑' n : ℕ, Real.log (n : ℝ) * ((1 - 1 / (N : ℝ)) ^ 2) ^ n)) :
    (1 - ν) * Real.sqrt (c * ∑' n : ℕ, Real.log (n : ℝ) * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) ≤
      ∑' n : ℕ, indA A n * ((1 - 1 / (N : ℝ)) ^ 2) ^ n := by
  set r : ℝ := 1 - 1 / (N : ℝ)
  set S₁ : ℝ := ∑' n : ℕ, Real.log (n : ℝ) * (r ^ 2) ^ n
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hr_pos : 0 < r := by
    have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have hS1 := es_S1_lower hN64
  have hS1_pos : 0 < S₁ := lt_of_lt_of_le (by
    have : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    positivity) hS1.2
  have hz2 : ‖((r ^ 2 : ℝ) : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr2_pos.le] using hr2_lt1
  have hsumR : Summable (fun n : ℕ => (rRep A n : ℝ) * (r ^ 2) ^ n) := by
    have h := summable_rRep_pow A hz2
    refine h.congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr2_pos.le]
  have hsq_eq : (∑' n : ℕ, indA A n * (r ^ 2) ^ n) ^ 2 = ∑' n : ℕ, (rRep A n : ℝ) * (r ^ 2) ^ n := by
    have hid := tsum_indA_sq_eq_tsum_rRep A hz2
    have hre := congrArg Complex.re hid
    have hsumA : Summable (fun n : ℕ => indA A n * (r ^ 2) ^ n) :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (indA_nonneg A n) (pow_nonneg hr2_pos.le n))
        (fun n => mul_le_of_le_one_left (pow_nonneg hr2_pos.le n) (indA_le_one A n))
        (summable_geometric_of_lt_one hr2_pos.le hr2_lt1)
    have hL : (∑' n : ℕ, (indA A n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) =
        ((∑' n : ℕ, indA A n * (r ^ 2) ^ n : ℝ) : ℂ) := by
      simpa [Complex.ofReal_mul, Complex.ofReal_pow] using (Complex.ofRealCLM.map_tsum hsumA).symm
    have hR : (∑' n : ℕ, (rRep A n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) =
        ((∑' n : ℕ, (rRep A n : ℝ) * (r ^ 2) ^ n : ℝ) : ℂ) := by
      simpa [Complex.ofReal_mul, Complex.ofReal_pow] using (Complex.ofRealCLM.map_tsum hsumR).symm
    rw [hL, hR, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re] at hre
    exact hre
  have htail_ge : (1 - ν / 2) * c * S₁ - (∑ n ∈ Finset.range N₁, c * Real.log ((n : ℝ) + 2)) ≤
      ∑' n : ℕ, (rRep A n : ℝ) * (r ^ 2) ^ n := by
    rw [← hsumR.sum_add_tsum_nat_add N₁]
    have hS1_split : S₁ = (∑ n ∈ Finset.range N₁, Real.log (n : ℝ) * (r ^ 2) ^ n) +
        ∑' n : ℕ, Real.log ((n + N₁ : ℕ) : ℝ) * (r ^ 2) ^ (n + N₁) :=
      (hS1.1.sum_add_tsum_nat_add N₁).symm
    rw [hS1_split]
    have hhead_nn : 0 ≤ ∑ n ∈ Finset.range N₁, (rRep A n : ℝ) * (r ^ 2) ^ n :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hS1_head : (1 - ν / 2) * c * (∑ n ∈ Finset.range N₁, Real.log (n : ℝ) * (r ^ 2) ^ n) ≤
        ∑ n ∈ Finset.range N₁, c * Real.log ((n : ℝ) + 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n _ => ?_
      have hlog_le : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp; exact Real.log_nonneg (by norm_num)
        · exact Real.log_le_log (by positivity) (by linarith)
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp
        · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0))
      have h2 : Real.log (n : ℝ) * (r ^ 2) ^ n ≤ Real.log ((n : ℝ) + 2) :=
        le_trans (mul_le_of_le_one_right hlog_nn (pow_le_one₀ hr2_pos.le hr2_lt1.le)) hlog_le
      have h0 : 0 ≤ Real.log (n : ℝ) * (r ^ 2) ^ n := mul_nonneg hlog_nn (pow_nonneg hr2_pos.le n)
      have h1 : (1 - ν / 2) * (Real.log (n : ℝ) * (r ^ 2) ^ n) ≤ Real.log ((n : ℝ) + 2) := by nlinarith
      nlinarith [hc]
    have htail_cmp : (1 - ν / 2) * c * (∑' n : ℕ, Real.log ((n + N₁ : ℕ) : ℝ) * (r ^ 2) ^ (n + N₁)) ≤
        ∑' n : ℕ, (rRep A (n + N₁) : ℝ) * (r ^ 2) ^ (n + N₁) := by
      rw [← tsum_mul_left]
      refine (((summable_nat_add_iff N₁).2 hS1.1).mul_left ((1 - ν / 2) * c)).tsum_le_tsum (fun n => by
        have := hrRep_lower (n + N₁) (Nat.le_add_left N₁ n)
        nlinarith [pow_nonneg hr2_pos.le (n + N₁)]) ((summable_nat_add_iff N₁).2 hsumR)
    linarith
  have hsq_ge : (1 - ν) ^ 2 * (c * S₁) ≤ (∑' n : ℕ, indA A n * (r ^ 2) ^ n) ^ 2 := by
    rw [hsq_eq]
    have h1 : (1 - ν) ^ 2 ≤ 1 - ν := by nlinarith
    nlinarith [mul_pos hc hS1_pos]
  have hsqL : ((1 - ν) * Real.sqrt (c * S₁)) ^ 2 = (1 - ν) ^ 2 * (c * S₁) := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hS1_pos).le]
  have hnnR : 0 ≤ ∑' n : ℕ, indA A n * (r ^ 2) ^ n :=
    tsum_nonneg fun n => mul_nonneg (indA_nonneg A n) (pow_nonneg hr2_pos.le n)
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ν) (Real.sqrt_nonneg (c * S₁))]

private lemma u_pow_bounds {u : ℝ} (hu : 16 ≤ u) :
    u ≤ u ^ 2 ∧ 2 ≤ u ^ 4 ∧ u ≤ u ^ 4 ∧ 2 ≤ u ^ 6 ∧ u ≤ u ^ 6 / 2 ∧
    u ^ 4 ≤ u ^ 6 / 4 ∧ u ^ 4 ≤ u ^ 6 / 2 ∧ u ≤ u ^ 8 ∧ 2 * u ^ 6 + 2 ≤ u ^ 8 := by
  have hu2 : 16 * u ≤ u ^ 2 := by nlinarith
  have hu2_ge : 256 ≤ u ^ 2 := by nlinarith
  have hu4 : 256 * u ^ 2 ≤ u ^ 4 := by nlinarith
  have hu4_ge : 65536 ≤ u ^ 4 := by nlinarith
  have hu6 : 256 * u ^ 4 ≤ u ^ 6 := by nlinarith
  have hu8 : 256 * u ^ 6 ≤ u ^ 8 := by nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

private lemma es_shift_parseval_bound (A : Set ℕ) [DecidablePred (· ∈ A)]
    {c η τ K : ℝ} {N₀ N h : ℕ}
    (hc : 0 < c) (hη0 : 0 ≤ η) (hτ_pos : 0 < τ) (hK_pos : 0 < K)
    (hN₀3 : 3 ≤ N₀) (hN64 : 64 ≤ N) (hh1 : 1 ≤ h)
    (hu_ge16 : 16 ≤ Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ))))
    (hh_le_u4 : (h : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ))) ^ 4)
    (hu_head : 300000 * (K ^ 2 + 1) / (τ * c) + (N₀ : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ))))
    (hu_dr : 6400 * (1 + 1 / τ) * c / τ ≤ Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ))))
    (hN₀_bd : ∀ n ≥ N₀, |(rRep A n : ℝ) - c * Real.log (n : ℝ)| ≤ η * Real.sqrt (c * Real.log (n : ℝ)))
    (hrRep_le_K : ∀ n : ℕ, (rRep A n : ℝ) ≤ K * Real.log ((n : ℝ) + 2)) :
    (1 / (2 * Real.pi)) *
      (∫ θ in (-Real.pi)..Real.pi,
        ‖1 - ((1 - 1 / (N : ℝ) : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) ^ h‖ ^ 2 *
          ‖∑' n : ℕ, (indA A n : ℂ) * ((1 - 1 / (N : ℝ) : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) ^ n‖ ^ 4) ≤
      (4 * (1 + τ) * η ^ 2 + τ) *
        (c * ∑' n : ℕ, Real.log (n : ℝ) * ((1 - 1 / (N : ℝ)) ^ 2) ^ n) := by
  set u : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))
  set r : ℝ := 1 - 1 / (N : ℝ)
  set S₁ : ℝ := ∑' n : ℕ, Real.log (n : ℝ) * (r ^ 2) ^ n
  have hu_pos : 0 < u := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  have hr_pos : 0 < r := by
    have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have hu8 : u ^ 8 = (N : ℝ) := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (N : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (Real.sqrt (N : ℝ))) ^ 2 = Real.sqrt (N : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
    calc u ^ 8 = ((u ^ 2) ^ 2) ^ 2 := by ring
      _ = (N : ℝ) := by rw [h1, h2, h3]
  have hlogN_ge1 : 1 ≤ Real.log (N : ℝ) := by
    have : Real.exp 1 ≤ (N : ℝ) := by
      have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
      linarith
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
  have hS1 := es_S1_lower hN64
  have hlog2_sq := es_log2_sq_upper hN64
  let zθ : ℝ → ℂ := fun θ => (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hzθ_norm : ∀ θ : ℝ, ‖zθ θ‖ = r := fun θ => by
    dsimp only [zθ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_pos.le, norm_exp_I_mul_real, mul_one]
  let dh : ℕ → ℝ := fun n => (rRep A n : ℝ) - if h ≤ n then (rRep A (n - h) : ℝ) else 0
  have hdh_sum : Summable (fun n : ℕ => ‖((dh n * r ^ n : ℝ) : ℂ)‖) := by
    have hr1 := summable_rRep_pow A (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
    have hr2 : Summable (fun n : ℕ => ‖((if h ≤ n then (rRep A (n - h) : ℝ) else 0 : ℝ) : ℂ) * (r : ℂ) ^ n‖) := by
      rw [← summable_nat_add_iff h]
      have heq : (fun n : ℕ => ‖((if h ≤ n + h then (rRep A (n + h - h) : ℝ) else 0 : ℝ) : ℂ) * (r : ℂ) ^ (n + h)‖) =
          fun n : ℕ => r ^ h * ‖(rRep A n : ℂ) * (r : ℂ) ^ n‖ := by
        funext n
        simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add, norm_mul, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_pos.le, Complex.norm_natCast,
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
        ring
      rw [heq]; exact hr1.mul_left (r ^ h)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hr1.add hr2)
    have hrew : ((dh n * r ^ n : ℝ) : ℂ) =
        (rRep A n : ℂ) * (r : ℂ) ^ n - ((if h ≤ n then (rRep A (n - h) : ℝ) else 0 : ℝ) : ℂ) * (r : ℂ) ^ n := by
      dsimp only [dh]; push_cast; ring
    rw [hrew]; exact norm_sub_le _ _
  have hpars_h :
      (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖∑' n : ℕ, (indA A n : ℂ) * zθ θ ^ n‖ ^ 4) =
      ∑' n : ℕ, dh n ^ 2 * (r ^ 2) ^ n := by
    have hL_eq : (∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖∑' n : ℕ, (indA A n : ℂ) * zθ θ ^ n‖ ^ 4) =
        ∫ θ in (-Real.pi)..Real.pi,
          ‖∑' n : ℕ, ((dh n * r ^ n : ℝ) : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hzlt : ‖zθ θ‖ < 1 := by rw [hzθ_norm θ]; exact hr_lt1
      have hsh := tsum_mul_one_sub_pow (fun n => (rRep A n : ℂ)) (zθ θ) h (summable_rRep_pow A hzlt).of_norm
      have hfz : (1 - zθ θ ^ h) * (∑' n : ℕ, (indA A n : ℂ) * zθ θ ^ n) ^ 2 =
          ∑' n : ℕ, ((dh n * r ^ n : ℝ) : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)) := by
        rw [tsum_indA_sq_eq_tsum_rRep A hzlt, hsh]
        congr 1; funext n; dsimp only [dh, zθ]; rw [mul_pow, ← Complex.exp_nat_mul]
        split_ifs <;> (push_cast; ring)
      rw [← hfz, norm_mul, norm_pow]; ring
    rw [hL_eq, ppl098_radial_parseval _ hdh_sum, one_div, inv_mul_cancel_left₀ (by positivity)]
    congr 1; funext n
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
  change (1 / (2 * Real.pi)) *
      (∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖∑' n : ℕ, (indA A n : ℂ) * zθ θ ^ n‖ ^ 4) ≤
    (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁)
  rw [hpars_h]
  set M : ℕ := max (N₀ + h) (Nat.floor (u ^ 6))
  have hdh2_sum : Summable (fun n : ℕ => dh n ^ 2 * (r ^ 2) ^ n) := by
    have hR2 : Summable (fun n : ℕ => (rRep A n : ℝ) ^ 2 * (r ^ 2) ^ n) :=
      Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
        have h1 : (rRep A n : ℝ) ^ 2 ≤ K ^ 2 * Real.log ((n : ℝ) + 2) ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hrRep_le_K n) 2
        nlinarith [pow_nonneg hr2_pos.le n]) (hlog2_sq.1.mul_left (K ^ 2))
    have hR2s : Summable (fun n : ℕ => (if h ≤ n then (rRep A (n - h) : ℝ) else 0) ^ 2 * (r ^ 2) ^ n) := by
      rw [← summable_nat_add_iff h]
      have heq : (fun n : ℕ => (if h ≤ n + h then (rRep A (n + h - h) : ℝ) else 0) ^ 2 * (r ^ 2) ^ (n + h)) =
          fun n : ℕ => (r ^ 2) ^ h * ((rRep A n : ℝ) ^ 2 * (r ^ 2) ^ n) := by
        funext n; simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]; ring
      rw [heq]; exact hR2.mul_left _
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) ((hR2.mul_left 2).add (hR2s.mul_left 2))
    dsimp only [dh]
    nlinarith [sq_nonneg ((rRep A n : ℝ) + if h ≤ n then (rRep A (n - h) : ℝ) else 0), pow_nonneg hr2_pos.le n]
  rw [← hdh2_sum.sum_add_tsum_nat_add M]
  have hup := u_pow_bounds hu_ge16
  have hM_le : (M : ℝ) ≤ 2 * u ^ 6 := by
    have hN0_le_u : (N₀ : ℝ) ≤ u := by
      have : 0 ≤ 300000 * (K ^ 2 + 1) / (τ * c) := by positivity
      linarith
    have h1 : ((N₀ + h : ℕ) : ℝ) ≤ 2 * u ^ 6 := by push_cast; linarith [hup.2.2.2.2.1, hup.2.2.2.2.2.2.1]
    have h2 : (Nat.floor (u ^ 6) : ℝ) ≤ 2 * u ^ 6 := by
      linarith [Nat.floor_le (by positivity : 0 ≤ u ^ 6), show 0 ≤ u ^ 6 by positivity]
    dsimp only [M]; rw [Nat.cast_max]; exact max_le h1 h2
  have hM_ge : u ^ 6 / 2 ≤ (M : ℝ) := by
    have h1 : (Nat.floor (u ^ 6) : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_right (N₀ + h) _
    have h2 := Nat.lt_floor_add_one (u ^ 6)
    linarith [hup.2.2.2.1]
  have hhead_le : ∑ n ∈ Finset.range M, dh n ^ 2 * (r ^ 2) ^ n ≤ (τ / 2) * (c * S₁) := by
    have hlog_16 : Real.log (N : ℝ) ≤ 16 * Real.sqrt u := by
      have hsq : Real.sqrt u ^ 16 = (N : ℝ) := by
        calc Real.sqrt u ^ 16 = (Real.sqrt u ^ 2) ^ 8 := by ring
          _ = u ^ 8 := by rw [Real.sq_sqrt hu_pos.le]
          _ = (N : ℝ) := hu8
      have hlu := le_trans (Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hu_pos)) (by linarith)
      rw [← hsq, Real.log_pow]; norm_num; linarith
    have hlogM_le : Real.log ((M : ℝ) + 2) ≤ 16 * Real.sqrt u := by
      have hM2_le_N : (M : ℝ) + 2 ≤ (N : ℝ) := by rw [← hu8]; linarith [hup.2.2.2.2.2.2.2.2]
      exact le_trans (Real.log_le_log (by positivity) hM2_le_N) hlog_16
    have hterm_le : ∀ n ∈ Finset.range M, dh n ^ 2 * (r ^ 2) ^ n ≤ 4 * K ^ 2 * (16 * Real.sqrt u) ^ 2 := by
      intro n hn; rw [Finset.mem_range] at hn
      have h1 : (rRep A n : ℝ) ≤ K * (16 * Real.sqrt u) :=
        calc (rRep A n : ℝ) ≤ K * Real.log ((n : ℝ) + 2) := hrRep_le_K n
          _ ≤ K * Real.log ((M : ℝ) + 2) :=
              mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n + 2 ≤ M + 2))) hK_pos.le
          _ ≤ K * (16 * Real.sqrt u) := mul_le_mul_of_nonneg_left hlogM_le hK_pos.le
      have h2 : (if h ≤ n then (rRep A (n - h) : ℝ) else 0) ≤ K * (16 * Real.sqrt u) := by
        split_ifs
        · exact calc (rRep A (n - h) : ℝ) ≤ K * Real.log (((n - h : ℕ) : ℝ) + 2) := hrRep_le_K (n - h)
            _ ≤ K * Real.log ((M : ℝ) + 2) :=
                mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n - h + 2 ≤ M + 2))) hK_pos.le
            _ ≤ K * (16 * Real.sqrt u) := mul_le_mul_of_nonneg_left hlogM_le hK_pos.le
        · positivity
      have habs : |dh n| ≤ 2 * K * (16 * Real.sqrt u) := by
        dsimp only [dh]
        have hnn1 : 0 ≤ (rRep A n : ℝ) := Nat.cast_nonneg _
        have hnn2 : 0 ≤ (if h ≤ n then (rRep A (n - h) : ℝ) else 0) := by split_ifs <;> positivity
        rw [abs_le]; constructor <;> linarith
      have hsq : dh n ^ 2 ≤ 4 * K ^ 2 * (16 * Real.sqrt u) ^ 2 := by
        rw [← sq_abs]; have := pow_le_pow_left₀ (abs_nonneg _) habs 2; linarith
      exact le_trans (mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hr2_pos.le hr2_lt1.le)) hsq
    have hK_bd : 262144 * K ^ 2 ≤ u * (τ * c) := by
      have h1 : 300000 * (K ^ 2 + 1) / (τ * c) ≤ u := by
        linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ (N₀ : ℝ))]
      have h2 : 300000 * (K ^ 2 + 1) ≤ u * (τ * c) := (div_le_iff₀ (by positivity)).1 h1
      nlinarith [sq_nonneg K]
    calc ∑ n ∈ Finset.range M, dh n ^ 2 * (r ^ 2) ^ n
        ≤ ∑ _n ∈ Finset.range M, (4 * K ^ 2 * (16 * Real.sqrt u) ^ 2) := Finset.sum_le_sum hterm_le
      _ = (M : ℝ) * (4 * K ^ 2 * (16 * Real.sqrt u) ^ 2) := by simp
      _ ≤ (2 * u ^ 6) * (4 * K ^ 2 * (16 * Real.sqrt u) ^ 2) := mul_le_mul_of_nonneg_right hM_le (by positivity)
      _ = 2048 * K ^ 2 * u ^ 7 := by rw [mul_pow, Real.sq_sqrt hu_pos.le]; ring
      _ ≤ (τ / 2) * (c * ((1 / 64) * (N : ℝ) * Real.log (N : ℝ))) := by
          have h1 : 2048 * K ^ 2 ≤ (τ / 128) * c * u := by linarith
          have hstep : 2048 * K ^ 2 * u ^ 7 ≤ (τ / 128) * c * u ^ 8 := by
            have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ u ^ 7)
            linarith [show (τ / 128) * c * u * u ^ 7 = (τ / 128) * c * u ^ 8 by ring]
          rw [hu8] at hstep
          have := le_mul_of_one_le_right (by positivity : 0 ≤ (τ / 128) * c * (N : ℝ)) hlogN_ge1
          linarith
      _ ≤ (τ / 2) * (c * S₁) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS1.2 hc.le) (by positivity)
  have htail_le : ∑' n : ℕ, dh (n + M) ^ 2 * (r ^ 2) ^ (n + M) ≤
      (4 * (1 + τ) * η ^ 2 + τ / 2) * (c * S₁) := by
    have hterm_tail : ∀ n : ℕ,
        dh (n + M) ^ 2 ≤
          (4 * (1 + τ) * η ^ 2) * (c * Real.log ((n + M : ℕ) : ℝ)) + (1 + 1 / τ) * (4 * c / u ^ 2) ^ 2 := by
      intro n; set k : ℕ := n + M
      have hk_ge_M : M ≤ k := Nat.le_add_left M n
      have hk_ge_N0h : N₀ + h ≤ k := le_trans (le_max_left _ _) hk_ge_M
      have hh_le_k : h ≤ k := by omega
      have hbd1 := hN₀_bd k (by omega)
      have hbd2 := hN₀_bd (k - h) (by omega)
      have hkh_pos : (0 : ℝ) < ((k - h : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k - h)
      have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
      have hkh_ge : u ^ 6 / 4 ≤ ((k - h : ℕ) : ℝ) := by
        have hkM : u ^ 6 / 2 ≤ (k : ℝ) := le_trans hM_ge (by exact_mod_cast hk_ge_M)
        rw [Nat.cast_sub hh_le_k]; linarith [hup.2.2.2.2.2.1]
      have hdrift : 0 ≤ c * (Real.log (k : ℝ) - Real.log ((k - h : ℕ) : ℝ)) ∧
          c * (Real.log (k : ℝ) - Real.log ((k - h : ℕ) : ℝ)) ≤ 4 * c / u ^ 2 := by
        constructor
        · have := Real.log_le_log hkh_pos (by exact_mod_cast Nat.sub_le k h : ((k - h : ℕ) : ℝ) ≤ (k : ℝ))
          nlinarith [hc]
        · have hlog_diff : Real.log (k : ℝ) - Real.log ((k - h : ℕ) : ℝ) ≤ (h : ℝ) / ((k - h : ℕ) : ℝ) := by
            rw [← Real.log_div hk_pos.ne' hkh_pos.ne']
            have h1 := Real.log_le_sub_one_of_pos (div_pos hk_pos hkh_pos)
            have hne : (k : ℝ) - (h : ℝ) ≠ 0 := by rw [← Nat.cast_sub hh_le_k]; exact hkh_pos.ne'
            have h2 : (k : ℝ) / ((k - h : ℕ) : ℝ) - 1 = (h : ℝ) / ((k - h : ℕ) : ℝ) := by
              rw [Nat.cast_sub hh_le_k]; field_simp [hne]; ring
            linarith
          have hfrac : (h : ℝ) / ((k - h : ℕ) : ℝ) ≤ 4 / u ^ 2 :=
            calc (h : ℝ) / ((k - h : ℕ) : ℝ) ≤ u ^ 4 / (u ^ 6 / 4) :=
                  div_le_div₀ (by positivity) hh_le_u4 (by positivity) hkh_ge
              _ = 4 / u ^ 2 := by field_simp [hu_pos.ne']
          have := mul_le_mul_of_nonneg_left (le_trans hlog_diff hfrac) hc.le
          linarith [show c * (4 / u ^ 2) = 4 * c / u ^ 2 by ring]
      have hsq_mono : Real.sqrt (c * Real.log ((k - h : ℕ) : ℝ)) ≤ Real.sqrt (c * Real.log (k : ℝ)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Real.log_le_log hkh_pos (by exact_mod_cast Nat.sub_le k h)) hc.le)
      have hdh_abs : |dh k| ≤ 2 * η * Real.sqrt (c * Real.log (k : ℝ)) + 4 * c / u ^ 2 := by
        dsimp only [dh]; simp only [hh_le_k, ↓reduceIte]
        have hrew : (rRep A k : ℝ) - (rRep A (k - h) : ℝ) =
            ((rRep A k : ℝ) - c * Real.log (k : ℝ)) -
            ((rRep A (k - h) : ℝ) - c * Real.log ((k - h : ℕ) : ℝ)) +
            c * (Real.log (k : ℝ) - Real.log ((k - h : ℕ) : ℝ)) := by ring
        rw [hrew]
        have h1 := abs_add_le
          (((rRep A k : ℝ) - c * Real.log (k : ℝ)) - ((rRep A (k - h) : ℝ) - c * Real.log ((k - h : ℕ) : ℝ)))
          (c * (Real.log (k : ℝ) - Real.log ((k - h : ℕ) : ℝ)))
        have h2 := abs_sub ((rRep A k : ℝ) - c * Real.log (k : ℝ))
          ((rRep A (k - h) : ℝ) - c * Real.log ((k - h : ℕ) : ℝ))
        rw [abs_of_nonneg hdrift.1] at h1
        nlinarith [hbd1, hbd2, hsq_mono, hdrift.2]
      have hsq_ab : (2 * η * Real.sqrt (c * Real.log (k : ℝ)) + 4 * c / u ^ 2) ^ 2 ≤
          (1 + τ) * (2 * η * Real.sqrt (c * Real.log (k : ℝ))) ^ 2 + (1 + 1 / τ) * (4 * c / u ^ 2) ^ 2 := by
        have hsq_gen : ∀ a b : ℝ, (a + b) ^ 2 ≤ (1 + τ) * a ^ 2 + (1 + 1 / τ) * b ^ 2 := by
          intro a b
          have hdiv : 0 ≤ (τ * a - b) ^ 2 / τ := div_nonneg (sq_nonneg _) hτ_pos.le
          have heq : (1 + τ) * a ^ 2 + (1 + 1 / τ) * b ^ 2 - (a + b) ^ 2 = (τ * a - b) ^ 2 / τ := by
            field_simp [hτ_pos.ne']; ring
          linarith
        exact hsq_gen _ _
      have hsq_k : (2 * η * Real.sqrt (c * Real.log (k : ℝ))) ^ 2 = 4 * η ^ 2 * (c * Real.log (k : ℝ)) := by
        have hlog_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hc.le hlog_nn)]; ring
      have hdh2 : dh k ^ 2 ≤ (2 * η * Real.sqrt (c * Real.log (k : ℝ)) + 4 * c / u ^ 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdh_abs 2
      rw [hsq_k] at hsq_ab
      have hassoc : (1 + τ) * (4 * η ^ 2 * (c * Real.log (k : ℝ))) =
          4 * (1 + τ) * η ^ 2 * (c * Real.log (k : ℝ)) := by ring
      linarith
    have hgeom := summable_geometric_of_lt_one hr2_pos.le hr2_lt1
    have htsum_le := ((summable_nat_add_iff M).2 hdh2_sum).tsum_le_tsum (fun n => by
      have := mul_le_mul_of_nonneg_right (hterm_tail n) (pow_nonneg hr2_pos.le (n + M))
      linarith)
      ((((summable_nat_add_iff M).2 hS1.1).mul_left ((4 * (1 + τ) * η ^ 2) * c)).add
        (((summable_nat_add_iff M).2 hgeom).mul_left ((1 + 1 / τ) * (4 * c / u ^ 2) ^ 2)))
    rw [(((summable_nat_add_iff M).2 hS1.1).mul_left _).tsum_add (((summable_nat_add_iff M).2 hgeom).mul_left _),
      tsum_mul_left, tsum_mul_left] at htsum_le
    have hS1_tail : ∑' n : ℕ, Real.log ((n + M : ℕ) : ℝ) * (r ^ 2) ^ (n + M) ≤ S₁ := by
      have := hS1.1.sum_add_tsum_nat_add M
      have hnn : 0 ≤ ∑ n ∈ Finset.range M, Real.log (n : ℝ) * (r ^ 2) ^ n :=
        Finset.sum_nonneg fun n _ => by
          rcases eq_or_ne n 0 with rfl | hn0
          · simp
          · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hn0)))
              (pow_nonneg hr2_pos.le n)
      linarith
    have hgeom_tail : ∑' n : ℕ, (r ^ 2) ^ (n + M) ≤ (N : ℝ) := by
      have := hgeom.sum_add_tsum_nat_add M
      rw [tsum_geometric_of_lt_one hr2_pos.le hr2_lt1] at this
      have hnn : 0 ≤ ∑ n ∈ Finset.range M, (r ^ 2) ^ n := Finset.sum_nonneg fun _ _ => by positivity
      have h1mr2_ge : 1 / (N : ℝ) ≤ 1 - r ^ 2 := by
        have : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
        rw [this, h1mr]; nlinarith
      have hinv_le : (1 - r ^ 2)⁻¹ ≤ (N : ℝ) := by
        rw [inv_le_comm₀ (by linarith) hN_pos]; simpa [one_div] using h1mr2_ge
      linarith
    have hconst_small : (1 + 1 / τ) * (4 * c / u ^ 2) ^ 2 * (N : ℝ) ≤ (τ / 2) * (c * S₁) := by
      have h1 : 6400 * (1 + 1 / τ) * c ≤ u * τ := (div_le_iff₀ hτ_pos).1 hu_dr
      have h1a : 2048 * (1 + 1 / τ) * c ≤ u ^ 4 * τ := by
        have hpos1 : 0 ≤ (1 + 1 / τ) * c := by positivity
        nlinarith [hup.2.2.1, hτ_pos]
      have h2 : (1 + 1 / τ) * (16 * c ^ 2 / u ^ 4) ≤ (τ / 128) * c := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        have hmul := mul_le_mul_of_nonneg_right h1a hc.le
        linarith [show 2048 * (1 + 1 / τ) * c * c = 128 * ((1 + 1 / τ) * (16 * c ^ 2)) by ring,
          show u ^ 4 * τ * c = 128 * ((τ / 128) * c * u ^ 4) by ring]
      have h3 : (1 + 1 / τ) * (4 * c / u ^ 2) ^ 2 * (N : ℝ) ≤ (τ / 128) * c * (N : ℝ) * Real.log (N : ℝ) := by
        have heq : (4 * c / u ^ 2) ^ 2 = 16 * c ^ 2 / u ^ 4 := by ring
        rw [heq]
        have h3a := mul_le_mul_of_nonneg_right h2 hN_pos.le
        have h3b := le_mul_of_one_le_right (by positivity : 0 ≤ (τ / 128) * c * (N : ℝ)) hlogN_ge1
        linarith
      have h4 := mul_le_mul_of_nonneg_left hS1.2 (by positivity : 0 ≤ (τ / 2) * c)
      linarith [show (τ / 2) * c * ((1 / 64) * (N : ℝ) * Real.log (N : ℝ)) =
        (τ / 128) * c * (N : ℝ) * Real.log (N : ℝ) by ring,
        show (τ / 2) * c * S₁ = (τ / 2) * (c * S₁) by ring]
    have hterm1_le := mul_le_mul_of_nonneg_left hS1_tail (by positivity : 0 ≤ (4 * (1 + τ) * η ^ 2) * c)
    have hterm2_le := le_trans (mul_le_mul_of_nonneg_left hgeom_tail (by positivity)) hconst_small
    linarith
  linarith

end ErdosSarkozyHelpers

/-- **Quantitative Erdős–Sárközy Impossibility Barrier for Erdős Problem #66** (100% pure Mathlib signature):
For every subset `A ⊆ ℕ`, every `c > 0`, and every `η < 1 / √2`, it is impossible that eventually
for all sufficiently large `n : ℕ`:
`|(1_A * 1_A)(n) - c * log n| ≤ η * √(c * log n)`. -/
theorem ppl098_erdos_sarkozy_log_quantitative
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c η : ℝ} (hc : 0 < c) (hη : η < 1 / Real.sqrt 2) :
    ¬ (∀ᶠ n : ℕ in atTop,
        |(((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)
          - c * Real.log (n : ℝ)|
          ≤ η * Real.sqrt (c * Real.log (n : ℝ))) := by
  intro hev
  obtain ⟨N₀', hN₀'⟩ := eventually_atTop.1 hev
  by_cases hη0 : η < 0
  · have h := hN₀' (max N₀' 2) (le_max_left _ _)
    have hlog_pos : 0 < Real.log ((max N₀' 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < max N₀' 2))
    have hneg : η * Real.sqrt (c * Real.log ((max N₀' 2 : ℕ) : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos hη0 (Real.sqrt_pos.2 (mul_pos hc hlog_pos))
    linarith [abs_nonneg ((((Finset.range (max N₀' 2 + 1)).filter (fun a => a ∈ A ∧ max N₀' 2 - a ∈ A)).card : ℝ)
      - c * Real.log ((max N₀' 2 : ℕ) : ℝ))]
  push Not at hη0
  set N₀ : ℕ := max N₀' 3
  have hN₀_bd : ∀ n ≥ N₀, |(rRep A n : ℝ) - c * Real.log (n : ℝ)| ≤ η * Real.sqrt (c * Real.log (n : ℝ)) :=
    fun n hn => hN₀' n (le_trans (le_max_left _ _) hn)
  have h2η_lt1 : 2 * η ^ 2 < 1 := by
    have hsq2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hlt := pow_lt_pow_left₀ hη hη0 (by norm_num : 2 ≠ 0)
    linarith
  set ρ : ℝ := (1 + 2 * η ^ 2) / 2
  have hρ_gt : 2 * η ^ 2 < ρ := by dsimp only [ρ]; linarith
  have hρ_lt1 : ρ < 1 := by dsimp only [ρ]; linarith
  have hρ_pos : 0 < ρ := by dsimp only [ρ]; positivity
  have hsqrtρ_lt1 : Real.sqrt ρ < 1 := (Real.sqrt_lt' zero_lt_one).2 (by simpa using hρ_lt1)
  set ν : ℝ := (1 - Real.sqrt ρ) / 4
  have hν_pos : 0 < ν := by dsimp only [ν]; linarith
  have hν_le : ν ≤ 1 / 4 := by dsimp only [ν]; linarith [Real.sqrt_nonneg ρ]
  set τ : ℝ := min (1 / 2) ((ρ - 2 * η ^ 2) / (4 * η ^ 2 + 3))
  have hτ_pos : 0 < τ := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hτ_le_half : τ ≤ 1 / 2 := min_le_left _ _
  have hτ_ratio : (4 * (1 + τ) * η ^ 2 + τ) / (2 - τ) ≤ ρ := by
    rw [div_le_iff₀ (by linarith)]
    have h2 : τ * (4 * η ^ 2 + 3) ≤ ρ - 2 * η ^ 2 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith [hρ_lt1]
  -- Global upper bound rRep A n ≤ K * log(n + 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := max (c + η * Real.sqrt c + 1) ((N₀ : ℝ) + 2) / Real.log 2
  have hK_pos : 0 < K := by positivity
  have hrRep_le_K : ∀ n : ℕ, (rRep A n : ℝ) ≤ K * Real.log ((n : ℝ) + 2) := by
    intro n
    have hlog2_le : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    by_cases hn : N₀ ≤ n
    · have hbd := hN₀_bd n hn
      have hlogn_ge1 : 1 ≤ Real.log (n : ℝ) := by
        have h3 : Real.exp 1 ≤ (n : ℝ) := by
          have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
          have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hn : 3 ≤ n)
          linarith
        simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
      have hsq_le : Real.sqrt (c * Real.log (n : ℝ)) ≤ Real.sqrt c * Real.log (n : ℝ) := by
        rw [Real.sqrt_mul hc.le]
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (n : ℝ)), Real.sqrt_nonneg (Real.log (n : ℝ))])
          (Real.sqrt_nonneg c)
      have hle_K : c + η * Real.sqrt c ≤ K := by
        dsimp only [K]; rw [le_div_iff₀ hlog2_pos]
        have hlog2_lt1 : Real.log 2 < 1 := by
          simpa [Real.log_exp] using Real.log_lt_log (by norm_num) (lt_trans (by norm_num) Real.exp_one_gt_d9)
        have h1 : c + η * Real.sqrt c ≤ max (c + η * Real.sqrt c + 1) ((N₀ : ℝ) + 2) :=
          le_trans (by linarith) (le_max_left _ _)
        nlinarith [show 0 ≤ c + η * Real.sqrt c by positivity]
      calc (rRep A n : ℝ) ≤ c * Real.log (n : ℝ) + η * Real.sqrt (c * Real.log (n : ℝ)) := by linarith [(abs_le.1 hbd).2]
        _ ≤ (c + η * Real.sqrt c) * Real.log (n : ℝ) := by nlinarith
        _ ≤ K * Real.log ((n : ℝ) + 2) :=
            mul_le_mul hle_K (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)) (by linarith) hK_pos.le
    · push Not at hn
      have h1 : (rRep A n : ℝ) ≤ (N₀ : ℝ) + 2 := by exact_mod_cast le_trans (rRep_le_succ A n) (by omega)
      calc (rRep A n : ℝ) ≤ max (c + η * Real.sqrt c + 1) ((N₀ : ℝ) + 2) := le_trans h1 (le_max_right _ _)
        _ = K * Real.log 2 := by dsimp only [K]; field_simp [hlog2_pos.ne']
        _ ≤ K * Real.log ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left hlog2_le hK_pos.le
  -- Choose N₁ ≥ N₀ for lower bound rRep A n ≥ (1 - ν/2) * c * log n
  obtain ⟨N₁', hN₁'⟩ := eventually_atTop.1 (tendsto_atTop.1
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) ((2 * η / (ν * Real.sqrt c)) ^ 2 + 1))
  set N₁ : ℕ := max N₀ N₁'
  have hrRep_lower : ∀ n ≥ N₁, (1 - ν / 2) * c * Real.log (n : ℝ) ≤ (rRep A n : ℝ) := by
    intro n hn
    have hbd := hN₀_bd n (le_trans (le_max_left _ _) hn)
    have hlog_ge : (2 * η / (ν * Real.sqrt c)) ^ 2 + 1 ≤ Real.log (n : ℝ) := hN₁' n (le_trans (le_max_right _ _) hn)
    have hlog_pos : 0 < Real.log (n : ℝ) := by linarith [sq_nonneg (2 * η / (ν * Real.sqrt c))]
    have h1 : η * Real.sqrt (c * Real.log (n : ℝ)) ≤ (ν / 2) * c * Real.log (n : ℝ) := by
      have hsq : (η * Real.sqrt (c * Real.log (n : ℝ))) ^ 2 ≤ ((ν / 2) * c * Real.log (n : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hc.le hlog_pos.le)]
        have hstep : (2 * η / (ν * Real.sqrt c)) ^ 2 ≤ Real.log (n : ℝ) := by linarith
        rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hc.le] at hstep
        have hmul := (div_le_iff₀ (by positivity : 0 < ν ^ 2 * c)).1 hstep
        have hmul2 := mul_le_mul_of_nonneg_right hmul (mul_nonneg hc.le hlog_pos.le)
        linarith [show (2 ^ 2 * η ^ 2) * (c * Real.log (n : ℝ)) = 4 * (η ^ 2 * (c * Real.log (n : ℝ))) by ring,
          show Real.log (n : ℝ) * (ν ^ 2 * c) * (c * Real.log (n : ℝ)) = 4 * ((ν / 2 * c * Real.log (n : ℝ)) ^ 2) by ring]
      nlinarith [mul_nonneg hη0 (Real.sqrt_nonneg (c * Real.log (n : ℝ))),
        show 0 ≤ (ν / 2) * c * Real.log (n : ℝ) by positivity]
    linarith [(abs_le.1 hbd).1]
  -- Pick a single sufficiently large N : ℕ
  let C_head : ℝ := ∑ n ∈ Finset.range N₁, c * Real.log ((n : ℝ) + 2)
  have hu_inf : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))) atTop atTop := by
    have hs : Tendsto Real.sqrt atTop atTop := tendsto_atTop_atTop.2 fun b =>
      ⟨(max b 0) ^ 2, fun x hx => le_trans (le_max_left b 0)
        (by simpa [Real.sqrt_sq (le_max_right b 0)] using Real.sqrt_le_sqrt hx)⟩
    exact hs.comp (hs.comp (hs.comp tendsto_natCast_atTop_atTop))
  set B_u : ℝ := max (max 16 (32 * Real.pi / τ))
    (max (max (128 * (C_head + 1) / (ν * c)) (3000 * K ^ 2 / (ν ^ 2 * c)))
      (max (300000 * (K ^ 2 + 1) / (τ * c) + (N₀ : ℝ))
        (6400 * (1 + 1 / τ) * c / τ)))
  obtain ⟨N, hN_u, hN_ge⟩ := ((tendsto_atTop.1 hu_inf B_u).and (eventually_ge_atTop (max N₁ 64))).exists
  set u : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N : ℝ)))
  have hu_ge16 : 16 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN_u
  have hu_pos : 0 < u := by linarith
  have hN64 : 64 ≤ N := le_trans (le_max_right _ _) hN_ge
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hu4 : u ^ 4 = Real.sqrt (N : ℝ) := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (N : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = Real.sqrt (N : ℝ) := by rw [h1, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hu8 : u ^ 8 = (N : ℝ) := by calc u ^ 8 = (u ^ 4) ^ 2 := by ring
                                       _ = (N : ℝ) := by rw [hu4, Real.sq_sqrt hN_pos.le]
  have hlogN_ge1 : 1 ≤ Real.log (N : ℝ) := by
    have : Real.exp 1 ≤ (N : ℝ) := by
      have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
      linarith
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
  set r : ℝ := 1 - 1 / (N : ℝ)
  have h1mr : 1 - r = 1 / (N : ℝ) := by dsimp only [r]; ring
  have hr_ge : 1 / 2 ≤ r := by
    have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
    have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hN_pos (by norm_num)]; linarith
    dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith [div_pos one_pos hN_pos]
  have hr_pos : 0 < r := by linarith
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have hr2_lt1 : r ^ 2 < 1 := by nlinarith
  have hup := u_pow_bounds hu_ge16
  set H : ℕ := Nat.floor (Real.sqrt (N : ℝ))
  have hH_le : (H : ℝ) ≤ u ^ 4 := by rw [hu4]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hH_ge : u ^ 4 / 2 ≤ (H : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.sqrt (N : ℝ))
    linarith [hu4, hup.2.1]
  have hH_pos : 1 ≤ H := by
    have : (1 : ℝ) ≤ (H : ℝ) := by linarith [hup.2.1]
    exact_mod_cast this
  set δ : ℝ := 1 / u ^ 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt_pi : δ < Real.pi := by
    have : δ ≤ 1 := by dsimp only [δ]; rw [div_le_one (by positivity)]; nlinarith [hu_ge16]
    linarith [Real.pi_gt_three]
  set S₁ : ℝ := ∑' n : ℕ, Real.log (n : ℝ) * (r ^ 2) ^ n
  have hS1 := es_S1_lower hN64
  have hS1_pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS1.2
  have hlog2_sq := es_log2_sq_upper hN64
  let zθ : ℝ → ℂ := fun θ => (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hzθ_norm : ∀ θ : ℝ, ‖zθ θ‖ = r := fun θ => by
    dsimp only [zθ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_pos.le, norm_exp_I_mul_real, mul_one]
  let f : ℂ → ℂ := fun z => ∑' n : ℕ, (indA A n : ℂ) * z ^ n
  have hf_cont : Continuous (fun θ : ℝ => f (zθ θ)) := by
    have hsum_w : Summable (fun n : ℕ => ‖((indA A n * r ^ n : ℝ) : ℂ)‖) := by
      have h := summable_indA_pow A (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
      refine h.congr fun n => ?_; simp [norm_pow, Complex.norm_real, abs_of_nonneg hr_pos.le]
    refine (continuous_tsum_fourier (fun n => ((indA A n * r ^ n : ℝ) : ℂ)) hsum_w).congr fun θ => ?_
    dsimp only [f, zθ]; congr 1; funext n; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
  -- 1. Radial L² lower bound: (1/(2π)) ∫_{-π}^{π} ‖f‖^2 = f(r^2) ≥ (1 - ν) √(c S₁)
  have hpars_f : (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ)‖ ^ 2) =
      ∑' n : ℕ, indA A n * (r ^ 2) ^ n := by
    have hsum_w : Summable (fun n : ℕ => ‖((indA A n * r ^ n : ℝ) : ℂ)‖) := by
      have h := summable_indA_pow A (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
      refine h.congr fun n => ?_; simp [norm_pow, Complex.norm_real, abs_of_nonneg hr_pos.le]
    have hL : (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ)‖ ^ 2) =
        ∫ θ in (-Real.pi)..Real.pi,
          ‖∑' n : ℕ, ((indA A n * r ^ n : ℝ) : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 :=
      intervalIntegral.integral_congr fun θ _ => by
        congr 2; dsimp only [f, zθ]; congr 1; funext n; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
    rw [hL, ppl098_radial_parseval _ hsum_w, one_div, inv_mul_cancel_left₀ (by positivity)]
    congr 1; funext n
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, indA_sq, ← pow_mul, mul_comm n 2, pow_mul]
  have hfr2_lower : (1 - ν) * Real.sqrt (c * S₁) ≤ ∑' n : ℕ, indA A n * (r ^ 2) ^ n := by
    refine es_fr2_lower A hc hν_pos hν_le hN64 hrRep_lower ?_
    have hu_C : 128 * (C_head + 1) / (ν * c) ≤ u :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hN_u)
    have h1 : 128 * (C_head + 1) ≤ u * (ν * c) := (div_le_iff₀ (by positivity)).1 hu_C
    have hu_le_N : u ≤ (N : ℝ) := by rw [← hu8]; exact hup.2.2.2.2.2.2.2.1
    have hNlog_ge : u ≤ (N : ℝ) * Real.log (N : ℝ) := le_trans hu_le_N (le_mul_of_one_le_right hN_pos.le hlogN_ge1)
    have h2 : 128 * C_head ≤ (N : ℝ) * Real.log (N : ℝ) * (ν * c) := by
      have := mul_le_mul_of_nonneg_right hNlog_ge (mul_nonneg hν_pos.le hc.le)
      linarith
    have h3 := mul_le_mul_of_nonneg_left hS1.2 (by positivity : 0 ≤ (ν / 2) * c)
    linarith [show (ν / 2) * c * ((1 / 64) * (N : ℝ) * Real.log (N : ℝ)) =
      ((N : ℝ) * Real.log (N : ℝ) * (ν * c)) / 128 by ring]
  -- 2. Major arc (-δ..δ) upper bound ≤ ν √(c S₁)
  have hmajor_le : (1 / (2 * Real.pi)) * (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2) ≤ ν * Real.sqrt (c * S₁) := by
    have hcs := intervalIntegral_cauchy_schwarz (a := -δ) (b := δ) (by linarith)
      (u := fun _ => (1 : ℝ)) (v := fun θ => ‖f (zθ θ)‖ ^ 2) continuous_const (hf_cont.norm.pow 2)
    simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_neg_eq_add] at hcs
    have hsub_int : (∫ θ in (-δ)..δ, (‖f (zθ θ)‖ ^ 2) ^ 2) ≤ ∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ) ^ 2‖ ^ 2 := by
      have hcont4 : Continuous (fun θ : ℝ => ‖f (zθ θ) ^ 2‖ ^ 2) := (hf_cont.pow 2).norm.pow 2
      have h1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont4.intervalIntegrable (-Real.pi) (-δ)) (hcont4.intervalIntegrable (-δ) δ)).symm
      have h2 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont4.intervalIntegrable (-Real.pi) δ) (hcont4.intervalIntegrable δ Real.pi)).symm
      have hnn1 : 0 ≤ ∫ θ in (-Real.pi)..(-δ), ‖f (zθ θ) ^ 2‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
      have hnn2 : 0 ≤ ∫ θ in δ..Real.pi, ‖f (zθ θ) ^ 2‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
      have heq : (∫ θ in (-δ)..δ, (‖f (zθ θ)‖ ^ 2) ^ 2) = ∫ θ in (-δ)..δ, ‖f (zθ θ) ^ 2‖ ^ 2 :=
        intervalIntegral.integral_congr fun θ _ => by rw [norm_pow]
      linarith
    have hpars4 : (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ) ^ 2‖ ^ 2) =
        (2 * Real.pi) * ∑' n : ℕ, (rRep A n : ℝ) ^ 2 * (r ^ 2) ^ n := by
      have hsum_r : Summable (fun n : ℕ => ‖((rRep A n * r ^ n : ℝ) : ℂ)‖) := by
        have h := summable_rRep_pow A (z := (r : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hr_pos.le] using hr_lt1)
        refine h.congr fun n => ?_; simp [norm_pow, Complex.norm_real, abs_of_nonneg hr_pos.le]
      have hL : (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ) ^ 2‖ ^ 2) =
          ∫ θ in (-Real.pi)..Real.pi,
            ‖∑' n : ℕ, ((rRep A n * r ^ n : ℝ) : ℂ) * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 :=
        intervalIntegral.integral_congr fun θ _ => by
          have hzlt : ‖zθ θ‖ < 1 := by rw [hzθ_norm θ]; exact hr_lt1
          dsimp only [f]; rw [tsum_indA_sq_eq_tsum_rRep A hzlt]
          congr 2; congr 1; funext n; dsimp only [zθ]; rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring
      rw [hL, ppl098_radial_parseval _ hsum_r]
      congr 1; congr 1; funext n
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    have hr2_sq_le : (∑' n : ℕ, (rRep A n : ℝ) ^ 2 * (r ^ 2) ^ n) ≤
        12 * K ^ 2 * (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
      have hsumR2 : Summable (fun n : ℕ => (rRep A n : ℝ) ^ 2 * (r ^ 2) ^ n) :=
        Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
          have h1 : (rRep A n : ℝ) ^ 2 ≤ K ^ 2 * Real.log ((n : ℝ) + 2) ^ 2 := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hrRep_le_K n) 2
          nlinarith [pow_nonneg hr2_pos.le n]) (hlog2_sq.1.mul_left (K ^ 2))
      have hle := hsumR2.tsum_le_tsum (fun n => by
        have h1 : (rRep A n : ℝ) ^ 2 ≤ K ^ 2 * Real.log ((n : ℝ) + 2) ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hrRep_le_K n) 2
        nlinarith [pow_nonneg hr2_pos.le n]) (hlog2_sq.1.mul_left (K ^ 2))
      rw [tsum_mul_left] at hle; nlinarith [hlog2_sq.2, sq_nonneg K]
    have hsq_major : ((1 / (2 * Real.pi)) * (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2)) ^ 2 ≤ ν ^ 2 * (c * S₁) := by
      have h1 : ((1 / (2 * Real.pi)) * (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2)) ^ 2 ≤
          (δ / Real.pi) * (12 * K ^ 2 * (N : ℝ) * Real.log (N : ℝ) ^ 2) := by
        rw [mul_pow]
        have h2 : (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2) ^ 2 ≤
            (2 * δ) * ((2 * Real.pi) * (12 * K ^ 2 * (N : ℝ) * Real.log (N : ℝ) ^ 2)) :=
          calc (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2) ^ 2
              ≤ (δ + δ) * (∫ θ in (-δ)..δ, (‖f (zθ θ)‖ ^ 2) ^ 2) := hcs
            _ = (2 * δ) * (∫ θ in (-δ)..δ, (‖f (zθ θ)‖ ^ 2) ^ 2) := by ring
            _ ≤ (2 * δ) * (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ) ^ 2‖ ^ 2) := mul_le_mul_of_nonneg_left hsub_int (by positivity)
            _ = (2 * δ) * ((2 * Real.pi) * ∑' n : ℕ, (rRep A n : ℝ) ^ 2 * (r ^ 2) ^ n) := by rw [hpars4]
            _ ≤ (2 * δ) * ((2 * Real.pi) * (12 * K ^ 2 * (N : ℝ) * Real.log (N : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2_sq_le (by positivity)) (by positivity)
        have hmul := mul_le_mul_of_nonneg_left h2 (sq_nonneg (1 / (2 * Real.pi)))
        have heq : (1 / (2 * Real.pi)) ^ 2 * ((2 * δ) * ((2 * Real.pi) * (12 * K ^ 2 * (N : ℝ) * Real.log (N : ℝ) ^ 2))) =
            (δ / Real.pi) * (12 * K ^ 2 * (N : ℝ) * Real.log (N : ℝ) ^ 2) := by field_simp [Real.pi_pos.ne']
        linarith
      have h2 : 2048 * K ^ 2 ≤ u * (ν ^ 2 * c) := by
        have h1' : 3000 * K ^ 2 / (ν ^ 2 * c) ≤ u :=
          le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hN_u)
        have := (div_le_iff₀ (by positivity)).1 h1'
        nlinarith [sq_nonneg K]
      have hlog8 : Real.log (N : ℝ) ≤ 8 * u := log_le_eight_mul_eighth_root (by exact_mod_cast (by omega : 1 ≤ N))
      have h3 : (δ / Real.pi) * (12 * K ^ 2 * Real.log (N : ℝ)) ≤ (1 / 64) * (ν ^ 2 * c) := by
        dsimp only [δ]
        have h12 : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
        calc (1 / u ^ 2 / Real.pi) * (12 * K ^ 2 * Real.log (N : ℝ))
            = (12 / Real.pi) * K ^ 2 * (Real.log (N : ℝ) / u ^ 2) := by ring
          _ ≤ 4 * K ^ 2 * (8 * u / u ^ 2) :=
              mul_le_mul (mul_le_mul_of_nonneg_right h12 (sq_nonneg K))
                (div_le_div_of_nonneg_right hlog8 (sq_nonneg u)) (by positivity) (by positivity)
          _ = 32 * K ^ 2 / u := by field_simp [hu_pos.ne']; ring
          _ ≤ (1 / 64) * (ν ^ 2 * c) := by rw [div_le_iff₀ hu_pos]; linarith
      calc ((1 / (2 * Real.pi)) * (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2)) ^ 2
          ≤ ((δ / Real.pi) * (12 * K ^ 2 * Real.log (N : ℝ))) * ((N : ℝ) * Real.log (N : ℝ)) := by linarith
        _ ≤ ((1 / 64) * (ν ^ 2 * c)) * ((N : ℝ) * Real.log (N : ℝ)) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ν ^ 2 * c * ((1 / 64) * (N : ℝ) * Real.log (N : ℝ)) := by ring
        _ ≤ ν ^ 2 * (c * S₁) := by nlinarith [hS1.2, hc, sq_nonneg ν]
    have hnnL : 0 ≤ (1 / (2 * Real.pi)) * (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2) :=
      mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _)
    have hsqR : (ν * Real.sqrt (c * S₁)) ^ 2 = ν ^ 2 * (c * S₁) := by rw [mul_pow, Real.sq_sqrt (mul_pos hc hS1_pos).le]
    nlinarith [mul_nonneg hν_pos.le (Real.sqrt_nonneg (c * S₁))]
  -- 3. Minor-arc L⁴ bound ≤ ρ (c S₁) via averaged shift multiplier + es_shift_parseval_bound
  set I_L : ℝ := ∫ θ in (-Real.pi)..(-δ), ‖f (zθ θ)‖ ^ 4
  set I_R : ℝ := ∫ θ in δ..Real.pi, ‖f (zθ θ)‖ ^ 4
  have hIL_nn : 0 ≤ I_L := intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
  have hIR_nn : 0 ≤ I_R := intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
  have hminor4_le : (1 / (2 * Real.pi)) * (I_L + I_R) ≤ ρ * (c * S₁) := by
    have hmult_ge : ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
        2 - τ ≤ (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2 := by
      intro θ hθ1 hθ2
      have havg := avg_one_sub_pow_sq_lower hr_ge hr_lt1 hH_pos hδ_pos hθ1 hθ2
      have hu_tau : 32 * Real.pi ≤ u * τ :=
        (div_le_iff₀ hτ_pos).1 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN_u)
      have hterm1 : 2 * (H : ℝ) * (1 - r) ≤ τ / 2 := by
        rw [h1mr]
        have h2 : 4 ≤ u ^ 4 * τ := by nlinarith [hup.2.2.1, Real.pi_gt_three, hτ_pos]
        calc 2 * (H : ℝ) * (1 / (N : ℝ)) ≤ 2 * u ^ 4 * (1 / u ^ 8) := by
              rw [← hu8]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH_le (by norm_num)) (by positivity)
          _ = 2 / u ^ 4 := by field_simp [hu_pos.ne']
          _ ≤ τ / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
      have hterm2 : 4 * Real.pi / ((H : ℝ) * δ) ≤ τ / 2 := by
        have hHδ : u ^ 2 / 2 ≤ (H : ℝ) * δ := by
          dsimp only [δ]
          have := mul_le_mul_of_nonneg_right hH_ge (by positivity : 0 ≤ 1 / u ^ 2)
          have heq : u ^ 4 / 2 * (1 / u ^ 2) = u ^ 2 / 2 := by field_simp [hu_pos.ne']
          linarith
        calc 4 * Real.pi / ((H : ℝ) * δ) ≤ 4 * Real.pi / (u ^ 2 / 2) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hHδ
          _ = 8 * Real.pi / u ^ 2 := by field_simp [hu_pos.ne']; ring
          _ ≤ τ / 2 := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith [hup.1, Real.pi_pos, hτ_pos]
      linarith
    have hcont_mult : Continuous (fun θ : ℝ => (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) := by
      dsimp only [zθ]; fun_prop
    have hcont_sum : Continuous (fun θ : ℝ =>
        ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4) :=
      hcont_mult.mul (hf_cont.norm.pow 4)
    have havg_int : (2 - τ) * (I_L + I_R) ≤
        (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H,
          ∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4 := by
      have hL_le : (2 - τ) * I_L ≤
          ∫ θ in (-Real.pi)..(-δ), ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4 := by
        dsimp only [I_L]; rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on (by linarith)
          ((continuous_const.mul (hf_cont.norm.pow 4)).intervalIntegrable _ _) (hcont_sum.intervalIntegrable _ _)
          fun θ hθ => mul_le_mul_of_nonneg_right
            (hmult_ge θ (by rw [abs_of_nonpos (by linarith [hθ.2])]; linarith [hθ.2])
              (by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2])) (by positivity)
      have hR_le : (2 - τ) * I_R ≤
          ∫ θ in δ..Real.pi, ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4 := by
        dsimp only [I_R]; rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on (by linarith)
          ((continuous_const.mul (hf_cont.norm.pow 4)).intervalIntegrable _ _) (hcont_sum.intervalIntegrable _ _)
          fun θ hθ => mul_le_mul_of_nonneg_right
            (hmult_ge θ (by rw [abs_of_nonneg (by linarith [hθ.1])]; linarith [hθ.1])
              (by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2])) (by positivity)
      have hfull_ge :
          (∫ θ in (-Real.pi)..(-δ), ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4) +
          (∫ θ in δ..Real.pi, ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4) ≤
          ∫ θ in (-Real.pi)..Real.pi, ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4 := by
        have h1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hcont_sum.intervalIntegrable (-Real.pi) (-δ)) (hcont_sum.intervalIntegrable (-δ) δ)).symm
        have h2 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hcont_sum.intervalIntegrable (-Real.pi) δ) (hcont_sum.intervalIntegrable δ Real.pi)).symm
        have hmid : 0 ≤ ∫ θ in (-δ)..δ, ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4 :=
          intervalIntegral.integral_nonneg (by linarith) fun _ _ =>
            mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by positivity)
        linarith
      have hcomm :
          (∫ θ in (-Real.pi)..Real.pi, ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4) =
          (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H,
            ∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4 := by
        have hrw : (fun θ : ℝ => ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, ‖1 - zθ θ ^ h‖ ^ 2) * ‖f (zθ θ)‖ ^ 4) =
            fun θ => (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H, (‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4) := by
          funext θ; rw [mul_assoc, Finset.sum_mul]
        rw [hrw, intervalIntegral.integral_const_mul]
        congr 1
        refine intervalIntegral.integral_finsetSum (fun h _ => ?_)
        have hz_cont : Continuous zθ := by dsimp only [zθ]; fun_prop
        exact (((continuous_const.sub (hz_cont.pow h)).norm.pow 2).mul (hf_cont.norm.pow 4)).intervalIntegrable _ _
      linarith
    have hshift_each : ∀ h ∈ Finset.Icc 1 H,
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4) ≤
          (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁) := fun h hh => by
      rw [Finset.mem_Icc] at hh
      exact es_shift_parseval_bound A hc hη0 hτ_pos hK_pos (le_max_right _ _) hN64 hh.1 hu_ge16
        (le_trans (by exact_mod_cast hh.2) hH_le)
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hN_u))
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hN_u))
        hN₀_bd hrRep_le_K
    have havg_upper :
        (1 / (2 * Real.pi)) * ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H,
          ∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4) ≤
        (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁) := by
      have hrw : (1 / (2 * Real.pi)) * ((1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H,
          ∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4) =
          (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H,
            ((1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => by ring
      rw [hrw]
      calc (1 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 H,
            ((1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, ‖1 - zθ θ ^ h‖ ^ 2 * ‖f (zθ θ)‖ ^ 4)
          ≤ (1 / (H : ℝ)) * ∑ _h ∈ Finset.Icc 1 H, ((4 * (1 + τ) * η ^ 2 + τ) * (c * S₁)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hshift_each) (by positivity)
        _ = (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁) := by
            simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
            field_simp [(by positivity : (H : ℝ) ≠ 0)]
    have hcomb : (2 - τ) * ((1 / (2 * Real.pi)) * (I_L + I_R)) ≤ (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁) := by
      have := mul_le_mul_of_nonneg_left havg_int (by positivity : 0 ≤ 1 / (2 * Real.pi))
      linarith
    have hdiv := (le_div_iff₀ (by linarith : 0 < 2 - τ)).2
      (by linarith : ((1 / (2 * Real.pi)) * (I_L + I_R)) * (2 - τ) ≤ (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁))
    have hdiv_eq : (4 * (1 + τ) * η ^ 2 + τ) * (c * S₁) / (2 - τ) =
        ((4 * (1 + τ) * η ^ 2 + τ) / (2 - τ)) * (c * S₁) := by ring
    calc (1 / (2 * Real.pi)) * (I_L + I_R)
        ≤ ((4 * (1 + τ) * η ^ 2 + τ) / (2 - τ)) * (c * S₁) := by linarith [hdiv, hdiv_eq]
      _ ≤ ρ * (c * S₁) := mul_le_mul_of_nonneg_right hτ_ratio (mul_pos hc hS1_pos).le
  -- 4. Cauchy–Schwarz on minor arcs → minor L² ≤ √ρ * √(c S₁), contradicting ν = (1 - √ρ) / 4
  have hminor2_le :
      (1 / (2 * Real.pi)) * ((∫ θ in (-Real.pi)..(-δ), ‖f (zθ θ)‖ ^ 2) + (∫ θ in δ..Real.pi, ‖f (zθ θ)‖ ^ 2)) ≤
        Real.sqrt ρ * Real.sqrt (c * S₁) := by
    have hcsL := intervalIntegral_cauchy_schwarz (a := -Real.pi) (b := -δ) (by linarith)
      (u := fun _ => (1 : ℝ)) (v := fun θ => ‖f (zθ θ)‖ ^ 2) continuous_const (hf_cont.norm.pow 2)
    have hcsR := intervalIntegral_cauchy_schwarz (a := δ) (b := Real.pi) (by linarith)
      (u := fun _ => (1 : ℝ)) (v := fun θ => ‖f (zθ θ)‖ ^ 2) continuous_const (hf_cont.norm.pow 2)
    simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_neg_eq_add] at hcsL hcsR
    have hpow4 : ∀ θ : ℝ, (‖f (zθ θ)‖ ^ 2) ^ 2 = ‖f (zθ θ)‖ ^ 4 := fun θ => by ring
    simp_rw [hpow4] at hcsL hcsR
    set J_L : ℝ := ∫ θ in (-Real.pi)..(-δ), ‖f (zθ θ)‖ ^ 2
    set J_R : ℝ := ∫ θ in δ..Real.pi, ‖f (zθ θ)‖ ^ 2
    have hJL_nn : 0 ≤ J_L := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    have hJR_nn : 0 ≤ J_R := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    have hsq_sum : (J_L + J_R) ^ 2 ≤ (2 * Real.pi) * (I_L + I_R) := by
      have h1 : (J_L + J_R) ^ 2 ≤ 2 * (J_L ^ 2 + J_R ^ 2) := by nlinarith [sq_nonneg (J_L - J_R)]
      have h2 : J_L ^ 2 + J_R ^ 2 ≤ (Real.pi - δ) * (I_L + I_R) := by
        have hL' : J_L ^ 2 ≤ (Real.pi - δ) * I_L := by linarith [hcsL]
        have hR' : J_R ^ 2 ≤ (Real.pi - δ) * I_R := by linarith [hcsR]
        linarith
      nlinarith [add_nonneg hIL_nn hIR_nn]
    have hsq_div : ((1 / (2 * Real.pi)) * (J_L + J_R)) ^ 2 ≤ ρ * (c * S₁) := by
      rw [mul_pow]
      have hmul := mul_le_mul_of_nonneg_left hsq_sum (sq_nonneg (1 / (2 * Real.pi)))
      have heq : (1 / (2 * Real.pi)) ^ 2 * ((2 * Real.pi) * (I_L + I_R)) =
          (1 / (2 * Real.pi)) * (I_L + I_R) := by field_simp [Real.pi_pos.ne']
      linarith [hminor4_le]
    have hsqR : (Real.sqrt ρ * Real.sqrt (c * S₁)) ^ 2 = ρ * (c * S₁) := by
      rw [mul_pow, Real.sq_sqrt hρ_pos.le, Real.sq_sqrt (mul_pos hc hS1_pos).le]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi)) (add_nonneg hJL_nn hJR_nn),
      mul_nonneg (Real.sqrt_nonneg ρ) (Real.sqrt_nonneg (c * S₁))]
  have hsplit_full :
      (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ)‖ ^ 2) =
        (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2) +
        ((∫ θ in (-Real.pi)..(-δ), ‖f (zθ θ)‖ ^ 2) + (∫ θ in δ..Real.pi, ‖f (zθ θ)‖ ^ 2)) := by
    have hcont2 : Continuous (fun θ : ℝ => ‖f (zθ θ)‖ ^ 2) := hf_cont.norm.pow 2
    have h1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont2.intervalIntegrable (-Real.pi) (-δ)) (hcont2.intervalIntegrable (-δ) δ)).symm
    have h2 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont2.intervalIntegrable (-Real.pi) δ) (hcont2.intervalIntegrable δ Real.pi)).symm
    linarith
  have hfinal : (1 - ν) * Real.sqrt (c * S₁) ≤ (ν + Real.sqrt ρ) * Real.sqrt (c * S₁) := by
    have h1 : (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi)..Real.pi, ‖f (zθ θ)‖ ^ 2) =
        (1 / (2 * Real.pi)) * (∫ θ in (-δ)..δ, ‖f (zθ θ)‖ ^ 2) +
        (1 / (2 * Real.pi)) * ((∫ θ in (-Real.pi)..(-δ), ‖f (zθ θ)‖ ^ 2) + (∫ θ in δ..Real.pi, ‖f (zθ θ)‖ ^ 2)) := by
      rw [hsplit_full]; ring
    linarith [hpars_f, hfr2_lower, hmajor_le, hminor2_le]
  have hcontra : 1 - ν ≤ ν + Real.sqrt ρ := le_of_mul_le_mul_right hfinal (Real.sqrt_pos.2 (mul_pos hc hS1_pos))
  dsimp only [ν] at hcontra
  linarith [hsqrtρ_lt1]

/-- **Erdős–Sárközy `o(√(log n))` Impossibility Corollary for Erdős Problem #66** (100% pure Mathlib signature):
For every `A ⊆ ℕ` and every `c > 0`, it is impossible that
`((1_A * 1_A)(n) - c * log n) / √(log n) → 0`. -/
theorem ppl098_erdos_sarkozy_log_impossibility
    (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c) :
    ¬ Tendsto
        (fun n : ℕ =>
          ((((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card : ℝ)
            - c * Real.log (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)))
        atTop (nhds 0) := by
  intro hlim
  apply ppl098_erdos_sarkozy_log_quantitative A hc (η := 1 / 2)
    (by
      have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have h2lt : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
      rw [div_lt_div_iff₀ (by norm_num) (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      linarith)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hlim ((1 / 2) * Real.sqrt c) (by positivity)
  refine eventually_atTop.2 ⟨max N₀ 2, fun n hn => ?_⟩
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsq_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.2 hlog_pos
  have hd := hN₀ n (le_trans (le_max_left _ _) hn)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hsq_pos, div_lt_iff₀ hsq_pos] at hd
  rw [Real.sqrt_mul hc.le]
  linarith

end
end PPL098
