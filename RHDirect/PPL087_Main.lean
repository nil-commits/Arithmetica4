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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic
import RHDirect.Arith4Ext_AnalyticNT
import RHDirect.Arith4Ext_SieveCharacters

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 087 (Zhi-Wei Sun's Conjecture — Simultaneous Primes `n + k` and `n + k²`)

## Honest Scope & Open Status
**PPL 087 (Zhi-Wei Sun's Conjecture, OEIS `A185636`, $100) REMAINS OPEN.**
Conjecture: For every integer `n > 1`, there exists `k` with `0 ≤ k < n` such that both
`n + k` and `n + k²` are prime.

This file does **not** claim to prove or refute PPL 087. Instead, it establishes a 100%
unconditional, pure-Mathlib-signature formalization (`0` `sorry`, `0` custom axioms,
`0` `native_decide`, `0` custom/private definitions in any public theorem signature), built on
targeted Mathlib imports and the audited Tier A libraries `RHDirect.Arith4Ext_AnalyticNT` and
`RHDirect.Arith4Ext_SieveCharacters`:

1. **Universal Local Admissibility & Exact Local Root-Count Law (`Section 1`)**:
   - Exact blocked-residue cardinalities for `p = 2` (`1`), `p = 3` (`2` iff `n ≡ 2 mod 3`, else `1`),
     and every odd prime `p` (`1` if `p ∣ n`, `2` if `p ∣ n + 1`, `2 + (-n / p)` otherwise).
   - Universal local admissibility `1 ≤ |B(n, p)| ≤ min (p - 1) 3 < p` for every `n` and prime `p`,
     plus multi-prime CRT simultaneous admissibility (ruling out any finite-modulus obstruction).
   - Exact witness congruence laws: parity lock (`k % 2 ≠ n % 2` for `n > 2`), mod-3 obstruction
     law, mod-6 witness pin for `n ≡ 2 (mod 3)`, and local admissibility of fixed-`k` families.
2. **Exact Infinite Witness Families, `Ω(X / log X)` Verified Density, & Kernel-Certified Initial
   Range (`Section 2`)**:
   - Exact infinite witness families (`n = p` via `k = 0`, `n = p - 1` via `k = 1`, twin/Polignac
     prime-pair shifts `n = p - k` via `k ≥ 2`).
   - Explicit disjoint-union lower bound `≥ 2 π(X) - 2` and explicit `Ω(X / log X)` verified
     density bounds for all `X ≥ 2` and `X ≥ 4`.
   - Kernel-certified initial range `2 ≤ n ≤ 500` with `0` `native_decide`.
3. **Unconditional Selberg Sieve Upper Bounds (`Section 3`)**:
   - Pointwise Brun–Titchmarsh bound `S(n) ≤ 9 n / log n` and pointwise quadratic Selberg sieve
     upper bound on `S(n)` using the exact local root-count density `ν_n(p) / p`.
   - Unconditional dimension-2 Brun–Selberg upper bound `≤ 450 (2m / φ(2m))² N / (log N)²` for
     prime pairs `(p, p + 2m)` in any interval `(M, M + N]` (`N ≥ 2`, `m ≥ 1`).
   - Fixed-witness sparsity (`≤ 450 (k(k-1) / φ(k(k-1)))² X / (log X)²` for each `k ≥ 2`),
     fourth-moment Euler totient bound `∑_{k ≤ X} (k / φ(k))⁴ ≤ exp(64) X`, and sharp-order
     cumulative pair-count upper bound `∑_{2 ≤ n ≤ X} S(n) ≤ (450 exp(64) + 20) X² / (log X)²`.
4. **Exact Reductions, Irreducibility, & Selberg Parity Barrier (`Section 4`)**:
   - Exact equivalence `PPL 087 ↔ ∀ n > 1, 1 ≤ S(n)` and exact reduction to composite pairs
     `(n, n + 1)` with witnesses `2 ≤ k < n`.
   - Irreducibility of the quadratic factor `X² + n` in `ℚ[X]` for every `n ≥ 1`.
   - Exact combinatorial Selberg parity barrier on the divisor lattice of any squarefree product `P`
     of distinct primes: parity-separated nonnegative weights (`a` on even `ω`, `b` on odd `ω`
     vanishing on all prime pairs) have identical divisor sums for every proper divisor `d ∣ P`.
-/

namespace PPL087

open Finset Real
open scoped BigOperators

/-! ## Section 1: Universal Local Admissibility & Exact Local Root-Count Law -/

private lemma zmod_two_sq (k : ZMod 2) : k ^ 2 = k := by
  fin_cases k <;> rfl

/-- Exact blocked residue count for `p = 2`: for every `n`, exactly `1` residue `k : ZMod 2`
satisfies `n + k = 0 ∨ n + k² = 0` (since `k² = k` in `ZMod 2`). -/
theorem ppl087_blocked_residues_card_two (n : ℕ) :
    ((Finset.univ : Finset (ZMod 2)).filter
      (fun k => (n : ZMod 2) + k = 0 ∨ (n : ZMod 2) + k ^ 2 = 0)).card = 1 := by
  have hfilt : (Finset.univ : Finset (ZMod 2)).filter
      (fun k => (n : ZMod 2) + k = 0 ∨ (n : ZMod 2) + k ^ 2 = 0) = {-(n : ZMod 2)} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      zmod_two_sq, or_self]
    constructor
    · intro h
      exact eq_neg_of_add_eq_zero_right h
    · intro h
      rw [h, add_neg_cancel]
  rw [hfilt, Finset.card_singleton]

/-- Exact blocked residue count for `p = 3`: for every `n`, the blocked set has size `2` if
`n % 3 = 2`, and size `1` otherwise (hence always `≤ 2 < 3`). -/
theorem ppl087_blocked_residues_card_three (n : ℕ) :
    ((Finset.univ : Finset (ZMod 3)).filter
      (fun k => (n : ZMod 3) + k = 0 ∨ (n : ZMod 3) + k ^ 2 = 0)).card =
      if n % 3 = 2 then 2 else 1 := by
  have hmod : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by
    rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3 <;> decide

private lemma zmod_two_ne_zero_of_odd_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hp_prime : p.Prime := Fact.out
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := hp_prime.two_le
  omega

/-- Exact blocked residue count for any prime `p` dividing `n`: the blocked set is `{0}`,
of cardinality `1`. -/
theorem ppl087_blocked_residues_card_of_dvd (n p : ℕ) [Fact p.Prime] (hdvd : p ∣ n) :
    ((Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card = 1 := by
  have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hdvd
  have hfilt : (Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0) = {0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hn0, zero_add]
    constructor
    · rintro (h | h)
      · exact h
      · exact sq_eq_zero_iff.mp h
    · intro h
      left; exact h
  rw [hfilt, Finset.card_singleton]

/-- Exact blocked residue count for any odd prime `p` dividing `n + 1`: the blocked set is
`{1, -1}` (since `k = 1` is a shared root of `n + k = 0` and `n + k² = 0`), of cardinality `2`. -/
theorem ppl087_blocked_residues_card_of_dvd_succ (n p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hdvd : p ∣ n + 1) :
    ((Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card = 2 := by
  have hn1 : (n : ZMod p) = -1 := by
    have h0 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + 1) p).mpr hdvd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h1ne : (1 : ZMod p) ≠ -1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := by
        calc (1 : ZMod p) + 1 = 1 + (-(-1 : ZMod p)) := by simp
          _ = 0 := by rw [← h]; ring
      simpa [one_add_one_eq_two] using this
    exact zmod_two_ne_zero_of_odd_prime hp2 h2
  have hfilt : (Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0) = {1, -1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hn1]
    constructor
    · rintro (h | h)
      · left; exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using h)
      · have hsq : k ^ 2 = (1 : ZMod p) ^ 2 := by
          rw [one_pow]
          exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using h)
        exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    · rintro (rfl | rfl)
      · left; ring
      · right; ring
  rw [hfilt, Finset.card_pair h1ne]

/-- Exact Legendre-symbol formula for the blocked residue count for every odd prime `p`
not dividing `n` or `n + 1`: `|B(n, p)| = 2 + (-n / p)`. -/
theorem ppl087_blocked_residues_card_odd_prime_exact (n p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hnd0 : ¬ p ∣ n) (hnd1 : ¬ p ∣ n + 1) :
    (((Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card : ℤ) =
      2 + legendreSym p (-(n : ℤ)) := by
  have hn0 : (n : ZMod p) ≠ 0 := by
    intro h; exact hnd0 ((ZMod.natCast_eq_zero_iff n p).mp h)
  have hn1 : (n : ZMod p) + 1 ≠ 0 := by
    intro h
    have h' : ((n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h
    exact hnd1 ((ZMod.natCast_eq_zero_iff (n + 1) p).mp h')
  have hnegn0 : ((-(n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact neg_ne_zero.mpr hn0
  by_cases hsq : IsSquare (-(n : ZMod p))
  · rcases hsq with ⟨r, hr⟩
    have hr_sq : r ^ 2 = -(n : ZMod p) := by rw [sq]; exact hr.symm
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at hr_sq
      exact neg_ne_zero.mpr hn0 hr_sq.symm
    have hr_ne_neg : r ≠ -r := by
      intro h
      have h2r : (2 : ZMod p) * r = 0 := by
        calc (2 : ZMod p) * r = r + r := two_mul r
          _ = r + (-r) := by nth_rw 2 [h]
          _ = 0 := add_neg_cancel r
      rcases mul_eq_zero.mp h2r with h2 | hr0'
      · exact zmod_two_ne_zero_of_odd_prime hp2 h2
      · exact hr0 hr0'
    have hnegn_ne_r : -(n : ZMod p) ≠ r := by
      intro h
      have hsq_eq : (-(n : ZMod p)) ^ 2 = -(n : ZMod p) := by
        calc (-(n : ZMod p)) ^ 2 = r ^ 2 := by rw [h]
          _ = -(n : ZMod p) := hr_sq
      have hfac : (n : ZMod p) * ((n : ZMod p) + 1) = 0 := by
        calc (n : ZMod p) * ((n : ZMod p) + 1)
            = (-(n : ZMod p)) ^ 2 - (-(n : ZMod p)) := by ring
          _ = 0 := sub_eq_zero.mpr hsq_eq
      rcases mul_eq_zero.mp hfac with h0 | h1
      · exact hn0 h0
      · exact hn1 h1
    have hnegn_ne_negr : -(n : ZMod p) ≠ -r := by
      intro h
      have hsq_eq : (-(n : ZMod p)) ^ 2 = -(n : ZMod p) := by
        calc (-(n : ZMod p)) ^ 2 = (-r) ^ 2 := by rw [h]
          _ = r ^ 2 := neg_sq r
          _ = -(n : ZMod p) := hr_sq
      have hfac : (n : ZMod p) * ((n : ZMod p) + 1) = 0 := by
        calc (n : ZMod p) * ((n : ZMod p) + 1)
            = (-(n : ZMod p)) ^ 2 - (-(n : ZMod p)) := by ring
          _ = 0 := sub_eq_zero.mpr hsq_eq
      rcases mul_eq_zero.mp hfac with h0 | h1
      · exact hn0 h0
      · exact hn1 h1
    have hfilt : (Finset.univ : Finset (ZMod p)).filter
        (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0) = {-(n : ZMod p), r, -r} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · left; exact eq_neg_of_add_eq_zero_right h
        · right
          have hk_sq : k ^ 2 = r ^ 2 := by
            rw [hr_sq]
            exact eq_neg_of_add_eq_zero_right h
          exact sq_eq_sq_iff_eq_or_eq_neg.mp hk_sq
      · rintro (rfl | rfl | rfl)
        · left; exact add_neg_cancel _
        · right; rw [hr_sq, add_neg_cancel]
        · right; rw [neg_sq, hr_sq, add_neg_cancel]
    have hcard : ((Finset.univ : Finset (ZMod p)).filter
        (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card = 3 := by
      rw [hfilt, Finset.card_insert_of_notMem, Finset.card_pair hr_ne_neg]
      simp [hnegn_ne_r, hnegn_ne_negr]
    have hleg : legendreSym p (-(n : ℤ)) = 1 := by
      rw [legendreSym.eq_one_iff p hnegn0]
      exact ⟨r, by push_cast; exact hr⟩
    rw [hcard, hleg]
    norm_num
  · have hfilt : (Finset.univ : Finset (ZMod p)).filter
        (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0) = {-(n : ZMod p)} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact eq_neg_of_add_eq_zero_right h
        · exfalso
          apply hsq
          refine ⟨k, ?_⟩
          rw [← sq]
          exact (eq_neg_of_add_eq_zero_right h).symm
      · rintro rfl
        left; exact add_neg_cancel _
    have hcard : ((Finset.univ : Finset (ZMod p)).filter
        (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card = 1 := by
      rw [hfilt, Finset.card_singleton]
    have hleg : legendreSym p (-(n : ℤ)) = -1 := by
      rw [legendreSym.eq_neg_one_iff p]
      intro hs
      apply hsq
      simpa using hs
    rw [hcard, hleg]
    norm_num

/-- **Universal Local Admissibility Theorem for PPL 087**: For every `n : ℕ` and every prime `p`,
the blocked residue count `ν_n(p) = |{k : ZMod p | n + k = 0 ∨ n + k² = 0}|` satisfies:
`1 ≤ ν_n(p)`, `ν_n(p) < p`, and `ν_n(p) ≤ min (p - 1) 3` (in particular `≤ 1` for `p = 2`,
`≤ 2` for `p = 3`, and `≤ 3` for `p ≥ 5`), ruling out any local obstruction. -/
theorem ppl087_universal_local_admissibility (n p : ℕ) [Fact p.Prime] :
    1 ≤ ((Finset.univ : Finset (ZMod p)).filter
          (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card ∧
    ((Finset.univ : Finset (ZMod p)).filter
          (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card < p ∧
    ((Finset.univ : Finset (ZMod p)).filter
          (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card ≤ min (p - 1) 3 := by
  have hp_prime : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    rw [ppl087_blocked_residues_card_two n]
    omega
  · by_cases hp3 : p = 3
    · subst hp3
      rw [ppl087_blocked_residues_card_three n]
      split_ifs <;> omega
    · have hp5 : 5 ≤ p := by
        have h2 := hp_prime.two_le
        have h4 : p ≠ 4 := fun h => by subst h; norm_num at hp_prime
        omega
      by_cases hd0 : p ∣ n
      · rw [ppl087_blocked_residues_card_of_dvd n p hd0]; omega
      · by_cases hd1 : p ∣ n + 1
        · rw [ppl087_blocked_residues_card_of_dvd_succ n p hp2 hd1]; omega
        · have hex := ppl087_blocked_residues_card_odd_prime_exact n p hp2 hd0 hd1
          have hleg_cases := legendreSym.eq_one_or_neg_one (p := p) (a := -(n : ℤ)) (by
            push_cast
            exact neg_ne_zero.mpr (fun h => hd0 ((ZMod.natCast_eq_zero_iff n p).mp h)))
          rcases hleg_cases with h1 | hm1
          · rw [h1] at hex
            have hcard : ((Finset.univ : Finset (ZMod p)).filter
                (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card = 3 := by omega
            rw [hcard]; omega
          · rw [hm1] at hex
            have hcard : ((Finset.univ : Finset (ZMod p)).filter
                (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card = 1 := by omega
            rw [hcard]; omega

/-- For every `n : ℕ` and every prime `p`, there exists an admissible residue `k : ZMod p`
avoiding both `n + k = 0` and `n + k² = 0`. -/
theorem ppl087_exists_admissible_residue (n p : ℕ) [Fact p.Prime] :
    ∃ k : ZMod p, (n : ZMod p) + k ≠ 0 ∧ (n : ZMod p) + k ^ 2 ≠ 0 := by
  have hlt := (ppl087_universal_local_admissibility n p).2.1
  have hlt_univ : ((Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0)).card <
      (Finset.univ : Finset (ZMod p)).card := by
    simpa [ZMod.card p] using hlt
  have hssub : (Finset.univ : Finset (ZMod p)).filter
      (fun k => (n : ZMod p) + k = 0 ∨ (n : ZMod p) + k ^ 2 = 0) ⊂
      (Finset.univ : Finset (ZMod p)) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun heq => by
      rw [heq] at hlt_univ; exact lt_irrefl _ hlt_univ⟩
  rcases Finset.exists_of_ssubset hssub with ⟨k, _, hnot⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hnot
  exact ⟨k, hnot⟩

/-- **Multi-Prime CRT Simultaneous Admissibility**: For every `n : ℕ` and every finite set `S` of
primes, there exists `k < ∏ p ∈ S, p` such that no `p ∈ S` divides `n + k` or `n + k²`. -/
theorem ppl087_crt_simultaneous_admissibility (n : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    ∃ k < ∏ p ∈ S, p, ∀ p ∈ S, ¬ p ∣ (n + k) ∧ ¬ p ∣ (n + k ^ 2) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨0, by simp, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | @insert q s hqs ih =>
    have hq_prime : Nat.Prime q := hS q (Finset.mem_insert_self q s)
    have hs_prime : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rcases ih hs_prime with ⟨k₁, hk₁_lt, hk₁⟩
    have : Fact q.Prime := ⟨hq_prime⟩
    rcases ppl087_exists_admissible_residue n q with ⟨r, hr1, hr2⟩
    set M := ∏ p ∈ s, p
    have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hs_prime p hp).pos
    have hcop : Nat.Coprime q M := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hq_prime (hs_prime p hp)).mpr (fun h => hqs (h ▸ hp))
    set crt := Nat.chineseRemainder hcop r.val k₁
    set k := crt.val % (q * M)
    have hqM_pos : 0 < q * M := Nat.mul_pos hq_prime.pos hM_pos
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.prod_insert hqs]
      exact Nat.mod_lt crt.val hqM_pos
    · intro p hp
      have hk_mod_q : k ≡ r.val [MOD q] := by
        have h1 : k ≡ crt.val [MOD q] :=
          (Nat.mod_modEq crt.val (q * M)).of_dvd (dvd_mul_right q M)
        exact h1.trans crt.property.1
      have hk_mod_M : k ≡ k₁ [MOD M] := by
        have h1 : k ≡ crt.val [MOD M] :=
          (Nat.mod_modEq crt.val (q * M)).of_dvd (dvd_mul_left M q)
        exact h1.trans crt.property.2
      rcases Finset.mem_insert.mp hp with hpq | hps
      · subst hpq
        have hcast_k : (k : ZMod p) = r := by
          have h1 : (k : ZMod p) = (r.val : ZMod p) :=
            (ZMod.natCast_eq_natCast_iff k r.val p).mpr hk_mod_q
          simpa [ZMod.natCast_zmod_val] using h1
        constructor
        · intro hdvd
          have h0 : ((n + k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + k) p).mpr hdvd
          push_cast at h0
          rw [hcast_k] at h0
          exact hr1 h0
        · intro hdvd
          have h0 : ((n + k ^ 2 : ℕ) : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff (n + k ^ 2) p).mpr hdvd
          push_cast at h0
          rw [hcast_k] at h0
          exact hr2 h0
      · have hpM : p ∣ M := Finset.dvd_prod_of_mem _ hps
        have hk_mod_p : k ≡ k₁ [MOD p] := hk_mod_M.of_dvd hpM
        have hnk : n + k ≡ n + k₁ [MOD p] := Nat.ModEq.add_left n hk_mod_p
        have hnk2 : n + k ^ 2 ≡ n + k₁ ^ 2 [MOD p] := Nat.ModEq.add_left n (hk_mod_p.pow 2)
        exact ⟨fun h => (hk₁ p hps).1 ((Nat.ModEq.dvd_iff hnk dvd_rfl).mp h),
               fun h => (hk₁ p hps).2 ((Nat.ModEq.dvd_iff hnk2 dvd_rfl).mp h)⟩

/-- **Parity Lock**: For every `n > 2` and every `k : ℕ`, if `n + k` and `n + k²` are both prime,
then `n + k` is odd (equivalently `k % 2 ≠ n % 2`). -/
theorem ppl087_parity_lock {n k : ℕ} (hn : 2 < n)
    (h1 : Nat.Prime (n + k)) (_h2 : Nat.Prime (n + k ^ 2)) :
    (n + k) % 2 = 1 ∧ k % 2 ≠ n % 2 := by
  have hodd : (n + k) % 2 = 1 := by
    have hndvd : ¬ 2 ∣ (n + k) := by
      intro hd
      have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two h1).mp hd
      omega
    omega
  exact ⟨hodd, by omega⟩

/-- **Mod-3 Obstruction Law**: For every `n > 3` and every `k : ℕ`, if `n + k` and `n + k²` are
both prime, then:
- `n % 3 = 0 → k % 3 ≠ 0`,
- `n % 3 = 1 → k % 3 ≠ 2`,
- `n % 3 = 2 → k % 3 = 0`. -/
theorem ppl087_mod_three_obstruction_law {n k : ℕ} (hn : 3 < n)
    (h1 : Nat.Prime (n + k)) (h2 : Nat.Prime (n + k ^ 2)) :
    (n % 3 = 0 → k % 3 ≠ 0) ∧
    (n % 3 = 1 → k % 3 ≠ 2) ∧
    (n % 3 = 2 → k % 3 = 0) := by
  have hnd1 : ¬ 3 ∣ (n + k) := by
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h1).mp hd
    omega
  have hnd2 : ¬ 3 ∣ (n + k ^ 2) := by
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).mp hd
    omega
  have hk_sq : (k ^ 2) % 3 = (k % 3) * (k % 3) % 3 := by
    rw [sq, Nat.mul_mod]
  refine ⟨?_, ?_, ?_⟩
  · intro hn0 hk0
    apply hnd1
    omega
  · intro hn1 hk2
    apply hnd1
    omega
  · intro hn2
    have hlt : k % 3 < 3 := Nat.mod_lt k (by norm_num)
    interval_cases hk : k % 3
    · rfl
    · exfalso; apply hnd1; omega
    · exfalso; apply hnd2
      have hk2_mod : (k ^ 2) % 3 = 1 := by omega
      omega

/-- **Mod-6 Witness Pin**: For every `n > 3` with `n % 3 = 2`, every witness `k` with `n + k`
and `n + k²` prime is pinned to a unique residue class modulo `6`:
`k % 6 = 3` when `n % 6 = 2`, and `k % 6 = 0` when `n % 6 = 5`. -/
theorem ppl087_mod_six_witness_pin {n k : ℕ} (hn : 3 < n) (hn3 : n % 3 = 2)
    (h1 : Nat.Prime (n + k)) (h2 : Nat.Prime (n + k ^ 2)) :
    (n % 6 = 2 → k % 6 = 3) ∧ (n % 6 = 5 → k % 6 = 0) := by
  have hpar := (ppl087_parity_lock (by omega) h1 h2).2
  have hmod3 := (ppl087_mod_three_obstruction_law hn h1 h2).2.2 hn3
  constructor <;> intro h <;> omega

/-- **Fixed-`k` Multi-Witness Family Admissibility**: For every fixed `k : ℕ` and every prime `p`,
the blocked `n`-residue count `|{n : ZMod p | n + k = 0 ∨ n + k² = 0}|` equals `1` if
`p ∣ k * (k - 1)` (in particular ALWAYS `1` for `p = 2`) and `2` otherwise, hence is always `< p`. -/
theorem ppl087_fixed_k_family_admissible (k p : ℕ) [Fact p.Prime] :
    ((Finset.univ : Finset (ZMod p)).filter
      (fun n => n + (k : ZMod p) = 0 ∨ n + (k : ZMod p) ^ 2 = 0)).card =
      (if p ∣ k * (k - 1) then 1 else 2) ∧
    ((Finset.univ : Finset (ZMod p)).filter
      (fun n => n + (k : ZMod p) = 0 ∨ n + (k : ZMod p) ^ 2 = 0)).card < p := by
  have hp_prime : p.Prime := Fact.out
  have hfilt : (Finset.univ : Finset (ZMod p)).filter
      (fun n => n + (k : ZMod p) = 0 ∨ n + (k : ZMod p) ^ 2 = 0) =
      {-(k : ZMod p), -((k : ZMod p) ^ 2)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; exact eq_neg_of_add_eq_zero_left h
      · right; exact eq_neg_of_add_eq_zero_left h
    · rintro (rfl | rfl)
      · left; exact neg_add_cancel _
      · right; exact neg_add_cancel _
  have heq_iff : (-(k : ZMod p) = -((k : ZMod p) ^ 2)) ↔ p ∣ k * (k - 1) := by
    rw [neg_inj]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      have hsub : ((m + 1 : ℕ) : ZMod p) ^ 2 - ((m + 1 : ℕ) : ZMod p) =
          (((m + 1) * m : ℕ) : ZMod p) := by
        push_cast; ring
      constructor
      · intro h
        have h0 : (((m + 1) * m : ℕ) : ZMod p) = 0 := by
          rw [← hsub, ← h, sub_self]
        exact (ZMod.natCast_eq_zero_iff ((m + 1) * m) p).mp h0
      · intro hdvd
        have h0 : (((m + 1) * m : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff ((m + 1) * m) p).mpr hdvd
        rw [← hsub] at h0
        exact (sub_eq_zero.mp h0).symm
  have h2dvd : 2 ∣ k * (k - 1) := by
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(t + t + 1) * t, by ring⟩
      · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
  by_cases hdvd : p ∣ k * (k - 1)
  · have hEq : -(k : ZMod p) = -((k : ZMod p) ^ 2) := heq_iff.mpr hdvd
    rw [hfilt, hEq, Finset.pair_eq_singleton, Finset.card_singleton, if_pos hdvd]
    exact ⟨rfl, hp_prime.one_lt⟩
  · have hNe : -(k : ZMod p) ≠ -((k : ZMod p) ^ 2) := fun h => hdvd (heq_iff.mp h)
    have hp2 : p ≠ 2 := fun h => hdvd (h ▸ h2dvd)
    have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
    rw [hfilt, Finset.card_pair hNe, if_neg hdvd]
    exact ⟨rfl, by omega⟩

/-! ## Section 2: Infinite Witness Families, `Ω(X / log X)` Verified Density, and Kernel-Certified `2 ≤ n ≤ 500` -/

/-- Exact infinite witness family `n = p` (`p` prime): `k = 0 < n` works immediately. -/
theorem ppl087_holds_for_prime {p : ℕ} (hp : Nat.Prime p) :
    ∃ k < p, Nat.Prime (p + k) ∧ Nat.Prime (p + k ^ 2) :=
  ⟨0, hp.pos, by simpa using hp, by simpa using hp⟩

/-- Exact infinite witness family `n = p - 1` (`p ≥ 3` prime): `k = 1 < n` works immediately. -/
theorem ppl087_holds_for_prime_pred {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    ∃ k < p - 1, Nat.Prime ((p - 1) + k) ∧ Nat.Prime ((p - 1) + k ^ 2) := by
  refine ⟨1, by omega, ?_, ?_⟩
  · simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using hp
  · simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using hp

/-- Exact witness family from twin primes `(p, p + 2)` (`p ≥ 5`): `n = p - 2` has witness `k = 2`. -/
theorem ppl087_holds_for_twin_prime_shift {p : ℕ} (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hp5 : 5 ≤ p) :
    ∃ k < p - 2, Nat.Prime ((p - 2) + k) ∧ Nat.Prime ((p - 2) + k ^ 2) := by
  refine ⟨2, by omega, ?_, ?_⟩
  · rw [show p - 2 + 2 = p by omega]; exact hp
  · rw [show p - 2 + 2 ^ 2 = p + 2 by omega]; exact hp2

/-- General prime-pair shift witness family: for any `k ≥ 1` and any prime pair
`(p, p + k * (k - 1))` with `2 * k < p`, `n = p - k` satisfies PPL 087 with witness `k`. -/
theorem ppl087_holds_for_general_prime_pair_shift {k p : ℕ} (hk : 1 ≤ k) (hpk : 2 * k < p)
    (hp : Nat.Prime p) (hp2 : Nat.Prime (p + k * (k - 1))) :
    ∃ j < p - k, Nat.Prime ((p - k) + j) ∧ Nat.Prime ((p - k) + j ^ 2) := by
  refine ⟨k, by omega, ?_, ?_⟩
  · rw [show p - k + k = p by omega]; exact hp
  · have hsq : p - k + k ^ 2 = p + k * (k - 1) := by
      have hk_le : k ≤ k ^ 2 := by nlinarith
      have hmul : k * (k - 1) + k = k ^ 2 := by
        cases k with
        | zero => omega
        | succ m => simp only [Nat.add_sub_cancel]; ring
      omega
    rw [hsq]
    exact hp2

/-- Disjoint union lower bound combining the `k = 0` (`n = p`) and `k = 1` (`n = p - 1`)
infinite witness families: for every `X ≥ 4`, at least `2 π(X) - 2` integers `n ∈ [2, X]`
satisfy PPL 087. -/
theorem ppl087_verified_count_ge_two_pi_sub_two {X : ℕ} (hX : 4 ≤ X) :
    2 * ((Finset.Icc 1 X).filter Nat.Prime).card - 2 ≤
      ((Finset.Icc 2 X).filter (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card := by
  classical
  set P := (Finset.Icc 1 X).filter Nat.Prime
  set P5 := (Finset.Icc 5 X).filter Nat.Prime
  set S₂ := P5.image (fun p => p - 1)
  set V := (Finset.Icc 2 X).filter (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))
  have hS1_sub : P ⊆ V := by
    intro p hp
    simp only [P, V, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.2.two_le, hp.1.2⟩, ppl087_holds_for_prime hp.2⟩
  have hS2_sub : S₂ ⊆ V := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
    simp only [P5, Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [V, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ppl087_holds_for_prime_pred hp.2 (by omega)⟩
  have hdisj : Disjoint P S₂ := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rcases Finset.mem_image.mp hn2 with ⟨p, hp, rfl⟩
    simp only [P, Finset.mem_filter, Finset.mem_Icc] at hn1
    simp only [P5, Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_odd : p % 2 = 1 := by
      rcases hp.2.eq_two_or_odd with h2 | hodd
      · omega
      · exact hodd
    have hpred_even : 2 ∣ (p - 1) := by omega
    have hpred_eq2 : p - 1 = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hn1.2).mp hpred_even).symm
    omega
  have hS2_card : S₂.card = P5.card := by
    apply Finset.card_image_of_injOn
    intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_coe, P5, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
    dsimp only at heq
    omega
  have hP_eq : P = insert 2 (insert 3 P5) := by
    ext p
    simp only [P, P5, Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_, hpX⟩, hp⟩
      by_cases h5 : 5 ≤ p
      · exact Or.inr (Or.inr ⟨⟨h5, hpX⟩, hp⟩)
      · have h2 := hp.two_le
        interval_cases p
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exfalso; norm_num at hp
    · rintro (rfl | rfl | ⟨⟨_, hpX⟩, hp⟩)
      · exact ⟨⟨by norm_num, by omega⟩, Nat.prime_two⟩
      · exact ⟨⟨by norm_num, by omega⟩, Nat.prime_three⟩
      · exact ⟨⟨hp.one_le, hpX⟩, hp⟩
  have h3not : 3 ∉ P5 := by
    simp only [P5, Finset.mem_filter, Finset.mem_Icc]; omega
  have h2not : 2 ∉ insert 3 P5 := by
    simp only [Finset.mem_insert, P5, Finset.mem_filter, Finset.mem_Icc]; omega
  have hP_card : P.card = P5.card + 2 := by
    rw [hP_eq, Finset.card_insert_of_notMem h2not, Finset.card_insert_of_notMem h3not]
  have hunion : P ∪ S₂ ⊆ V := Finset.union_subset hS1_sub hS2_sub
  have hcard : P.card + S₂.card ≤ V.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  rw [hS2_card] at hcard
  omega

/-- **Unconditional `Ω(X / log X)` Verified Density Theorem (All `X ≥ 2`)**:
Using `RHDirect.Arith4Ext_AnalyticNT.primePi_ge_explicit`, for every `X ≥ 2`,
`(log 2 / 4) · X / log X ≤ #{n ∈ [2, X] : PPL 087 holds for n}`. -/
theorem ppl087_verified_density_omega_x_div_log_x {X : ℕ} (hX : 2 ≤ X) :
    (Real.log 2 / 4) * (X : ℝ) / Real.log (X : ℝ) ≤
      (((Finset.Icc 2 X).filter
        (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) := by
  have hpi := Arith4Ext.AnalyticNT.primePi_ge_explicit (x := (X : ℝ)) (by exact_mod_cast hX)
  have hpi_eq : Arith4Ext.AnalyticNT.primePi (X : ℝ) = ((Finset.Icc 1 X).filter Nat.Prime).card := by
    simp [Arith4Ext.AnalyticNT.primePi]
  rw [hpi_eq] at hpi
  have hsub : (Finset.Icc 1 X).filter Nat.Prime ⊆
      (Finset.Icc 2 X).filter (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.2.two_le, hp.1.2⟩, ppl087_holds_for_prime hp.2⟩
  have hcard_r : (((Finset.Icc 1 X).filter Nat.Prime).card : ℝ) ≤
      (((Finset.Icc 2 X).filter
        (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hpi.trans hcard_r

/-- **Sharpened `Ω(X / log X)` Verified Density Theorem (`X ≥ 4`)** from the disjoint `k = 0`
and `k = 1` families:
`(log 2 / 2) · X / log X - 2 ≤ #{n ∈ [2, X] : PPL 087 holds for n}`. -/
theorem ppl087_verified_density_two_families {X : ℕ} (hX : 4 ≤ X) :
    (Real.log 2 / 2) * (X : ℝ) / Real.log (X : ℝ) - 2 ≤
      (((Finset.Icc 2 X).filter
        (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) := by
  have hpi := Arith4Ext.AnalyticNT.primePi_ge_explicit (x := (X : ℝ))
    (by exact_mod_cast (by omega : 2 ≤ X))
  have hpi_eq : Arith4Ext.AnalyticNT.primePi (X : ℝ) = ((Finset.Icc 1 X).filter Nat.Prime).card := by
    simp [Arith4Ext.AnalyticNT.primePi]
  rw [hpi_eq] at hpi
  have h2 := ppl087_verified_count_ge_two_pi_sub_two hX
  have hpi_ge2 : 2 ≤ ((Finset.Icc 1 X).filter Nat.Prime).card := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ (Finset.Icc 1 X).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_filter, Finset.mem_Icc]
      rcases hp with rfl | rfl
      · exact ⟨⟨by norm_num, by omega⟩, Nat.prime_two⟩
      · exact ⟨⟨by norm_num, by omega⟩, Nat.prime_three⟩
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  have h2_r : 2 * (((Finset.Icc 1 X).filter Nat.Prime).card : ℝ) - 2 ≤
      (((Finset.Icc 2 X).filter
        (fun n => ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) := by
    have hcast : ((2 * ((Finset.Icc 1 X).filter Nat.Prime).card - 2 : ℕ) : ℝ) =
        2 * (((Finset.Icc 1 X).filter Nat.Prime).card : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * ((Finset.Icc 1 X).filter Nat.Prime).card)]
      push_cast; ring
    rw [← hcast]
    exact_mod_cast h2
  have hmul : (Real.log 2 / 2) * (X : ℝ) / Real.log (X : ℝ) =
      2 * ((Real.log 2 / 4) * (X : ℝ) / Real.log (X : ℝ)) := by ring
  linarith

/-! ### Kernel-Certified Initial Range (`2 ≤ n ≤ 500`, ZERO `native_decide`) -/

private def noOddDivFrom (m d : ℕ) : ℕ → Bool
  | 0 => false
  | fuel + 1 =>
    if m < d * d then true
    else if m % d == 0 then false
    else noOddDivFrom m (d + 2) fuel

private lemma noOddDivFrom_sound (m d fuel : ℕ) (hd_odd : d % 2 = 1) (hd3 : 3 ≤ d)
    (hok : noOddDivFrom m d fuel = true) :
    ∀ q, d ≤ q → q % 2 = 1 → q * q ≤ m → ¬ q ∣ m := by
  induction fuel generalizing d with
  | zero => simp [noOddDivFrom] at hok
  | succ fuel ih =>
    unfold noOddDivFrom at hok
    by_cases hlt : m < d * d
    · intro q hqd _ hqsq _
      have : d * d ≤ q * q := Nat.mul_le_mul hqd hqd
      omega
    · rw [if_neg hlt] at hok
      by_cases hmod : m % d = 0
      · simp [hmod] at hok
      · have hmodb : (m % d == 0) = false := beq_false_of_ne hmod
        rw [hmodb] at hok
        simp only [Bool.false_eq_true, ↓reduceIte] at hok
        intro q hqd hqodd hqsq hqdvd
        by_cases hqe : q = d
        · subst hqe
          exact hmod (Nat.mod_eq_zero_of_dvd hqdvd)
        · have hqd2 : d + 2 ≤ q := by omega
          exact ih (d + 2) (by omega) (by omega) hok q hqd2 hqodd hqsq hqdvd

private def isPrimeFast (m : ℕ) : Bool :=
  if m < 2 then false
  else if m == 2 then true
  else if m % 2 == 0 then false
  else noOddDivFrom m 3 m

private lemma isPrimeFast_sound {m : ℕ} (hm : isPrimeFast m = true) : Nat.Prime m := by
  unfold isPrimeFast at hm
  by_cases hlt2 : m < 2
  · simp [hlt2] at hm
  · rw [if_neg hlt2] at hm
    by_cases heq2 : m = 2
    · rw [heq2]; exact Nat.prime_two
    · have heq2b : (m == 2) = false := beq_false_of_ne heq2
      rw [heq2b] at hm
      simp only [Bool.false_eq_true, ↓reduceIte] at hm
      by_cases heven : m % 2 = 0
      · simp [heven] at hm
      · have hevenb : (m % 2 == 0) = false := beq_false_of_ne heven
        rw [hevenb] at hm
        simp only [Bool.false_eq_true, ↓reduceIte] at hm
        have hm3 : 3 ≤ m := by omega
        have hnodiv := noOddDivFrom_sound m 3 m (by norm_num) le_rfl hm
        rw [Nat.prime_def_minFac]
        refine ⟨by omega, ?_⟩
        by_contra hne
        have hmf_prime : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
        have hmf_dvd : m.minFac ∣ m := Nat.minFac_dvd m
        have hmf_sq : m.minFac * m.minFac ≤ m := by
          simpa [sq] using Nat.minFac_sq_le_self (by omega) (fun h => hne (Nat.Prime.minFac_eq h))
        have hmf_ne2 : m.minFac ≠ 2 := by
          intro h2
          rw [h2] at hmf_dvd
          exact heven (Nat.mod_eq_zero_of_dvd hmf_dvd)
        have hmf_odd : m.minFac % 2 = 1 := by
          rcases hmf_prime.eq_two_or_odd with h2 | hodd
          · exact absurd h2 hmf_ne2
          · exact hodd
        have hmf_ge3 : 3 ≤ m.minFac := by have := hmf_prime.two_le; omega
        exact hnodiv m.minFac hmf_ge3 hmf_odd hmf_sq hmf_dvd

private def checkWitnessList (a : ℕ) : List ℕ → Bool
  | [] => true
  | k :: ks => decide (k < a) && isPrimeFast (a + k) && isPrimeFast (a + k * k) &&
      checkWitnessList (a + 1) ks

private lemma checkWitnessList_sound (a : ℕ) (L : List ℕ) (hok : checkWitnessList a L = true) :
    ∀ i < L.length, ∃ k < a + i, Nat.Prime ((a + i) + k) ∧ Nat.Prime ((a + i) + k ^ 2) := by
  induction L generalizing a with
  | nil => intro i hi; simp at hi
  | cons k ks ih =>
    simp only [checkWitnessList, Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨hka, hp1⟩, hp2⟩, hrest⟩
    intro i hi
    cases i with
    | zero =>
      refine ⟨k, by omega, isPrimeFast_sound hp1, ?_⟩
      simpa [sq] using isPrimeFast_sound hp2
    | succ j =>
      simp only [List.length_cons] at hi
      have hrec := ih (a + 1) hrest j (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

private def witnessChunk1 : List ℕ :=
  [0,0,1,0,1,0,3,2,1,0,1,0,3,2,1,0,1,0,3,16,1,0,7,4,15,
   2,1,0,1,0,9,8,3,6,1,0,3,2,1,0,1,0,3,8,1,0,5,10,3,10,
   1,0,5,4,15,2,1,0,1,0,21,4,3,6,1,0,15,2,1,0,1,0,33,8,25,
   6,1,0,3,16,1,0,5,4,15,14,1,0,7,6,9,4,3,6,1,0,3,2,1,0]

private def witnessChunk2 : List ℕ :=
  [1,0,3,2,1,0,1,0,27,16,1,0,13,22,21,14,9,12,11,6,15,4,7,12,1,
   0,3,8,1,0,5,4,15,2,1,0,1,0,33,10,7,6,7,6,21,2,1,0,1,0,
   21,14,3,18,1,0,9,8,19,6,1,0,3,8,1,0,5,10,3,10,1,0,5,4,15,
   2,1,0,1,0,9,10,7,42,5,6,3,2,1,0,1,0,33,2,1,0,1,0,27,26]

private def witnessChunk3 : List ℕ :=
  [9,30,23,6,21,4,15,30,1,0,21,10,13,12,11,10,15,8,3,6,1,0,3,2,1,
   0,1,0,3,10,1,0,7,4,15,2,1,0,1,0,15,8,7,6,5,4,3,8,1,0,
   5,4,3,22,1,0,5,10,3,20,1,0,7,4,15,2,1,0,1,0,9,8,3,6,1,
   0,15,2,1,0,1,0,27,8,21,24,5,18,27,16,1,0,13,12,15,10,9,12,7,6]

private def witnessChunk4 : List ℕ :=
  [9,8,3,12,1,0,3,2,1,0,1,0,45,16,1,0,13,12,27,10,15,30,7,22,105,
   20,3,18,1,0,15,4,13,12,1,0,9,10,7,120,5,4,3,2,1,0,1,0,3,16,
   1,0,5,12,45,10,1,0,7,6,27,4,3,24,1,0,15,20,3,96,1,0,15,8,111,
   12,1,0,3,80,1,0,5,4,45,10,1,0,7,10,39,4,7,6,1,0,21,10,1,0]

private def witnessChunk5 : List ℕ :=
  [17,6,63,4,15,24,1,0,9,20,7,6,5,4,15,2,1,0,1,0,9,8,25,6,65,
   4,15,2,1,0,1,0,15,8,21,24,1,0,3,26,1,0,13,4,21,10,1,0,7,6,
   15,26,3,6,1,0,3,2,1,0,1,0,27,14,1,0,19,10,21,16,7,6,5,4,15,
   10,1,0,11,40,9,4,15,6,1,0,21,58,1,0,7,10,15,14,45,12,1,0,3]

private lemma chunk1_ok : witnessChunk1.length = 100 ∧ checkWitnessList 2 witnessChunk1 = true :=
  by decide
private lemma chunk2_ok : witnessChunk2.length = 100 ∧ checkWitnessList 102 witnessChunk2 = true :=
  by decide
private lemma chunk3_ok : witnessChunk3.length = 100 ∧ checkWitnessList 202 witnessChunk3 = true :=
  by decide
private lemma chunk4_ok : witnessChunk4.length = 100 ∧ checkWitnessList 302 witnessChunk4 = true :=
  by decide
private lemma chunk5_ok : witnessChunk5.length = 99 ∧ checkWitnessList 402 witnessChunk5 = true :=
  by decide

/-- **Kernel-Certified Initial Range (`2 ≤ n ≤ 500`, `0` `native_decide`)**:
Zhi-Wei Sun's conjecture holds for every integer `2 ≤ n ≤ 500`. -/
theorem ppl087_initial_range_500 :
    ∀ n : ℕ, 2 ≤ n → n ≤ 500 → ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2) := by
  intro n hn2 hn500
  by_cases h1 : n ≤ 101
  · have h := checkWitnessList_sound 2 witnessChunk1 chunk1_ok.2 (n - 2) (by rw [chunk1_ok.1]; omega)
    simpa [show 2 + (n - 2) = n by omega] using h
  · by_cases h2 : n ≤ 201
    · have h := checkWitnessList_sound 102 witnessChunk2 chunk2_ok.2 (n - 102)
        (by rw [chunk2_ok.1]; omega)
      simpa [show 102 + (n - 102) = n by omega] using h
    · by_cases h3 : n ≤ 301
      · have h := checkWitnessList_sound 202 witnessChunk3 chunk3_ok.2 (n - 202)
          (by rw [chunk3_ok.1]; omega)
        simpa [show 202 + (n - 202) = n by omega] using h
      · by_cases h4 : n ≤ 401
        · have h := checkWitnessList_sound 302 witnessChunk4 chunk4_ok.2 (n - 302)
            (by rw [chunk4_ok.1]; omega)
          simpa [show 302 + (n - 302) = n by omega] using h
        · have h := checkWitnessList_sound 402 witnessChunk5 chunk5_ok.2 (n - 402)
            (by rw [chunk5_ok.1]; omega)
          simpa [show 402 + (n - 402) = n by omega] using h

/-! ## Section 3: Unconditional Selberg Sieve Upper Bounds -/

/-! ### Generic Polynomial-Sequence Selberg Sieve Infrastructure (Private) -/

private def polyRootCount (F : ℕ → ℕ) (d : ℕ) : ℕ :=
  ((Finset.range d).filter (fun r => d ∣ F r)).card

private lemma polyRootCount_le (F : ℕ → ℕ) (d : ℕ) : polyRootCount F d ≤ d := by
  unfold polyRootCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range d)

private lemma polyRootCount_one (F : ℕ → ℕ) : polyRootCount F 1 = 1 := by
  unfold polyRootCount
  have h : (Finset.range 1).filter (fun r => 1 ∣ F r) = {0} := by
    ext r; simp
  rw [h, Finset.card_singleton]

private lemma poly_dvd_mod_iff {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d]) (d x : ℕ) :
    d ∣ F x ↔ d ∣ F (x % d) := by
  have hmod : F x ≡ F (x % d) [MOD d] := hF d x (x % d) (Nat.mod_modEq x d).symm
  exact Nat.ModEq.dvd_iff hmod dvd_rfl

private lemma polyRootCount_mul {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d]) {a b : ℕ} (hab : Nat.Coprime a b) :
    polyRootCount F (a * b) = polyRootCount F a * polyRootCount F b := by
  unfold polyRootCount
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
  rw [← Finset.card_product]
  refine Finset.card_bij (fun r _ => (r % a, r % b)) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt r ha_pos, (poly_dvd_mod_iff hF a r).mp ((dvd_mul_right a b).trans hr.2)⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt r hb_pos, (poly_dvd_mod_iff hF b r).mp ((dvd_mul_left b a).trans hr.2)⟩
  · intro r₁ hr₁ r₂ hr₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    have hma : r₁ ≡ r₂ [MOD a] := congr_arg Prod.fst heq
    have hmb : r₁ ≡ r₂ [MOD b] := congr_arg Prod.snd heq
    rcases le_total r₁ r₂ with hle | hle
    · have hda : a ∣ (r₂ - r₁) := (Nat.modEq_iff_dvd' hle).mp hma
      have hdb : b ∣ (r₂ - r₁) := (Nat.modEq_iff_dvd' hle).mp hmb
      have hdab : a * b ∣ (r₂ - r₁) := hab.mul_dvd_of_dvd_of_dvd hda hdb
      have h0 : r₂ - r₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdab (by omega)
      omega
    · have hda : a ∣ (r₁ - r₂) := (Nat.modEq_iff_dvd' hle).mp hma.symm
      have hdb : b ∣ (r₁ - r₂) := (Nat.modEq_iff_dvd' hle).mp hmb.symm
      have hdab : a * b ∣ (r₁ - r₂) := hab.mul_dvd_of_dvd_of_dvd hda hdb
      have h0 : r₁ - r₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdab (by omega)
      omega
  · rintro ⟨r₁, r₂⟩ hpair
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hpair
    set crt := Nat.chineseRemainder hab r₁ r₂
    set r := crt.val % (a * b)
    have hr_lt : r < a * b := Nat.mod_lt crt.val (Nat.mul_pos ha_pos hb_pos)
    have hma : r ≡ r₁ [MOD a] :=
      ((Nat.mod_modEq crt.val (a * b)).of_dvd (dvd_mul_right a b)).trans crt.property.1
    have hmb : r ≡ r₂ [MOD b] :=
      ((Nat.mod_modEq crt.val (a * b)).of_dvd (dvd_mul_left b a)).trans crt.property.2
    have hmod_a : r % a = r₁ := by
      have : r % a = r₁ % a := hma
      rw [this, Nat.mod_eq_of_lt hpair.1.1]
    have hmod_b : r % b = r₂ := by
      have : r % b = r₂ % b := hmb
      rw [this, Nat.mod_eq_of_lt hpair.2.1]
    have hda : a ∣ F r := (poly_dvd_mod_iff hF a r).mpr (by rw [hmod_a]; exact hpair.1.2)
    have hdb : b ∣ F r := (poly_dvd_mod_iff hF b r).mpr (by rw [hmod_b]; exact hpair.2.2)
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr_lt,
      hab.mul_dvd_of_dvd_of_dvd hda hdb⟩, Prod.ext hmod_a hmod_b⟩

private lemma poly_density_isMult {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d]) :
    Arith4Ext.SieveCharacters.IsMultDensity (fun d => (polyRootCount F d : ℝ) / (d : ℝ)) := by
  refine ⟨by simp [polyRootCount_one], fun a b hab => ?_⟩
  dsimp only
  rw [polyRootCount_mul hF hab]
  push_cast
  ring

private lemma poly_block_card {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d]) (a d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ico a (a + d)).filter (fun k => d ∣ F k)).card = polyRootCount F d := by
  unfold polyRootCount
  refine Finset.card_bij (fun k _ => k % d) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hk ⊢
    exact ⟨Nat.mod_lt k (by omega), (poly_dvd_mod_iff hF d k).mp hk.2⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk₁ hk₂
    have hmod : k₁ ≡ k₂ [MOD d] := heq
    rcases le_total k₁ k₂ with hle | hle
    · have hdvd : d ∣ (k₂ - k₁) := (Nat.modEq_iff_dvd' hle).mp hmod
      have h0 : k₂ - k₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : d ∣ (k₁ - k₂) := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have h0 : k₁ - k₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    set off := (r + d - a % d) % d
    set k := a + off
    have hoff_lt : off < d := Nat.mod_lt _ (by omega)
    have hk_mod : k % d = r := by
      have ha_lt : a % d < d := Nat.mod_lt a (by omega)
      calc (a + off) % d
          = (a % d + off % d) % d := Nat.add_mod a off d
        _ = (a % d + (r + d - a % d) % d) % d := by rw [Nat.mod_eq_of_lt hoff_lt]
        _ = (a % d + (r + d - a % d)) % d := by rw [Nat.add_mod_mod]
        _ = (r + d) % d := by congr 1; omega
        _ = r % d := Nat.add_mod_right r d
        _ = r := Nat.mod_eq_of_lt hr.1
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
      (poly_dvd_mod_iff hF d k).mpr (by rw [hk_mod]; exact hr.2)⟩, hk_mod⟩

private lemma poly_multiples_qblocks {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d]) (M d q : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ico M (M + q * d)).filter (fun k => d ∣ F k)).card = q * polyRootCount F d := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hunion : (Finset.Ico M (M + (q + 1) * d)).filter (fun k => d ∣ F k) =
        (Finset.Ico M (M + q * d)).filter (fun k => d ∣ F k) ∪
          (Finset.Ico (M + q * d) (M + q * d + d)).filter (fun k => d ∣ F k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union]
      have hmul : (q + 1) * d = q * d + d := by ring
      rw [hmul]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hlt : k < M + q * d
        · exact Or.inl ⟨⟨h1, hlt⟩, h3⟩
        · exact Or.inr ⟨⟨by omega, by omega⟩, h3⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, by omega⟩, h3⟩
        · exact ⟨⟨by omega, by omega⟩, h3⟩
    have hdisj : Disjoint ((Finset.Ico M (M + q * d)).filter (fun k => d ∣ F k))
        ((Finset.Ico (M + q * d) (M + q * d + d)).filter (fun k => d ∣ F k)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_filter, Finset.mem_Ico] at hk1 hk2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj, ih, poly_block_card hF (M + q * d) d hd]
    ring

private lemma abs_poly_remainder_le {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d]) (M N d : ℕ) (hd : 1 ≤ d) :
    |(((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).card : ℝ) -
        (N : ℝ) * ((polyRootCount F d : ℝ) / (d : ℝ))| ≤ (polyRootCount F d : ℝ) := by
  set q := N / d
  have hqd_le : q * d ≤ N := Nat.div_mul_le_self N d
  have hN_lt : N < (q + 1) * d := by
    have h1 := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
    change N < q * d + d at h1
    linarith
  have hsub1 : (Finset.Ico M (M + q * d)).filter (fun k => d ∣ F k) ⊆
      (Finset.Ico M (M + N)).filter (fun k => d ∣ F k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    exact ⟨⟨hk.1.1, by omega⟩, hk.2⟩
  have hsub2 : (Finset.Ico M (M + N)).filter (fun k => d ∣ F k) ⊆
      (Finset.Ico M (M + (q + 1) * d)).filter (fun k => d ∣ F k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    exact ⟨⟨hk.1.1, by omega⟩, hk.2⟩
  have hlo_nat : q * polyRootCount F d ≤ ((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).card := by
    rw [← poly_multiples_qblocks hF M d q hd]
    exact Finset.card_le_card hsub1
  have hhi_nat : ((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).card ≤
      (q + 1) * polyRootCount F d := by
    rw [← poly_multiples_qblocks hF M d (q + 1) hd]
    exact Finset.card_le_card hsub2
  have hlo : (q : ℝ) * (polyRootCount F d : ℝ) ≤
      (((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).card : ℝ) := by exact_mod_cast hlo_nat
  have hhi : (((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).card : ℝ) ≤
      ((q : ℝ) + 1) * (polyRootCount F d : ℝ) := by exact_mod_cast hhi_nat
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hq_le_div : (q : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]; exact_mod_cast hqd_le
  have hdiv_lt_q1 : (N : ℝ) / (d : ℝ) < (q : ℝ) + 1 := by
    rw [div_lt_iff₀ hd_pos]; exact_mod_cast hN_lt
  have hrc_nn : (0 : ℝ) ≤ (polyRootCount F d : ℝ) := Nat.cast_nonneg _
  have hmul_lo : ((N : ℝ) / (d : ℝ) - 1) * (polyRootCount F d : ℝ) ≤
      (q : ℝ) * (polyRootCount F d : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hrc_nn
  have hmul_hi : ((q : ℝ) + 1) * (polyRootCount F d : ℝ) ≤
      ((N : ℝ) / (d : ℝ) + 1) * (polyRootCount F d : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hrc_nn
  have hrew : (N : ℝ) * ((polyRootCount F d : ℝ) / (d : ℝ)) =
      ((N : ℝ) / (d : ℝ)) * (polyRootCount F d : ℝ) := by ring
  rw [hrew, abs_le]
  constructor <;> linarith

private lemma poly_selberg_sieve_Ico {F : ℕ → ℕ}
    (hF : ∀ d x y, x ≡ y [MOD d] → F x ≡ F y [MOD d])
    {M N z D : ℕ} (hFinj : Set.InjOn F (Finset.Ico M (M + N) : Set ℕ))
    (hD : 1 ≤ D)
    (h01 : ∀ p ∈ (Arith4Ext.SieveCharacters.primorial z).primeFactors,
      0 < (polyRootCount F p : ℝ) / (p : ℝ) ∧ (polyRootCount F p : ℝ) / (p : ℝ) < 1) :
    (((Finset.Ico M (M + N)).filter
        (fun k => Nat.Coprime (F k) (Arith4Ext.SieveCharacters.primorial z))).card : ℝ) ≤
      (N : ℝ) / Arith4Ext.SieveCharacters.selbergG
        (fun d => (polyRootCount F d : ℝ) / (d : ℝ))
        (Arith4Ext.SieveCharacters.primorial z) D + (D : ℝ) ^ 4 := by
  classical
  set P := Arith4Ext.SieveCharacters.primorial z
  set A := (Finset.Ico M (M + N)).image F
  set g : ℕ → ℝ := fun d => (polyRootCount F d : ℝ) / (d : ℝ)
  have hP_sq : Squarefree P := Arith4Ext.SieveCharacters.primorial_squarefree z
  have hP_pos : 0 < P := Arith4Ext.SieveCharacters.primorial_pos z
  have hsel := Arith4Ext.SieveCharacters.selberg_upper_bound_sieve_simplified A
    (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) hP_sq hD (N : ℝ) (poly_density_isMult hF) h01
  have hsift_eq : Arith4Ext.SieveCharacters.siftedSum A (fun _ => (1 : ℝ)) P =
      (((Finset.Ico M (M + N)).filter (fun k => Nat.Coprime (F k) P)).card : ℝ) := by
    unfold Arith4Ext.SieveCharacters.siftedSum
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have hfilt : A.filter (fun m => Nat.Coprime m P) =
        ((Finset.Ico M (M + N)).filter (fun k => Nat.Coprime (F k) P)).image F := by
      ext m
      simp only [A, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hcop⟩; exact ⟨k, ⟨hk, hcop⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hcop⟩, rfl⟩; exact ⟨⟨k, hk, rfl⟩, hcop⟩
    rw [hfilt]
    exact Finset.card_image_of_injOn (hFinj.mono (by
      intro k hk; exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1))
  have hmult_eq : ∀ d : ℕ, Arith4Ext.SieveCharacters.multiplesSum A (fun _ => (1 : ℝ)) d =
      (((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).card : ℝ) := by
    intro d
    unfold Arith4Ext.SieveCharacters.multiplesSum
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have hfilt : A.filter (d ∣ ·) = ((Finset.Ico M (M + N)).filter (fun k => d ∣ F k)).image F := by
      ext m
      simp only [A, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hd⟩; exact ⟨k, ⟨hk, hd⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hd⟩, rfl⟩; exact ⟨⟨k, hk, rfl⟩, hd⟩
    rw [hfilt]
    exact Finset.card_image_of_injOn (hFinj.mono (by
      intro k hk; exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1))
  rw [hsift_eq] at hsel
  have herr : ∑ d₁ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
        ∑ d₂ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
          |Arith4Ext.SieveCharacters.sieveRemainder A (fun _ => (1 : ℝ)) (N : ℝ) g
            (Nat.lcm d₁ d₂)| ≤ (D : ℝ) ^ 4 := by
    have hcard_le : (Arith4Ext.SieveCharacters.sieveDivisors P D).card ≤ D := by
      have hsub : Arith4Ext.SieveCharacters.sieveDivisors P D ⊆ Finset.Icc 1 D := by
        intro d hd
        have hd_mem := (Arith4Ext.SieveCharacters.mem_sieveDivisors hP_pos.ne').mp hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd_mem.1 hP_pos, hd_mem.2⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    have hterm : ∀ d₁ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
        ∀ d₂ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
          |Arith4Ext.SieveCharacters.sieveRemainder A (fun _ => (1 : ℝ)) (N : ℝ) g
            (Nat.lcm d₁ d₂)| ≤ (D : ℝ) ^ 2 := by
      intro d₁ hd₁ d₂ hd₂
      have hm1 := (Arith4Ext.SieveCharacters.mem_sieveDivisors hP_pos.ne').mp hd₁
      have hm2 := (Arith4Ext.SieveCharacters.mem_sieveDivisors hP_pos.ne').mp hd₂
      have hd1_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hm1.1 hP_pos
      have hd2_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hm2.1 hP_pos
      have hlcm_pos : 1 ≤ Nat.lcm d₁ d₂ := Nat.lcm_pos hd1_pos hd2_pos
      have hlcm_le : Nat.lcm d₁ d₂ ≤ d₁ * d₂ :=
        Nat.le_of_dvd (Nat.mul_pos hd1_pos hd2_pos)
          (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
      have hrc_le : polyRootCount F (Nat.lcm d₁ d₂) ≤ D * D :=
        (polyRootCount_le F _).trans (hlcm_le.trans (Nat.mul_le_mul hm1.2 hm2.2))
      unfold Arith4Ext.SieveCharacters.sieveRemainder
      rw [hmult_eq]
      calc |(((Finset.Ico M (M + N)).filter (fun k => Nat.lcm d₁ d₂ ∣ F k)).card : ℝ) -
              (N : ℝ) * g (Nat.lcm d₁ d₂)|
          ≤ (polyRootCount F (Nat.lcm d₁ d₂) : ℝ) := abs_poly_remainder_le hF M N _ hlcm_pos
        _ ≤ (D : ℝ) ^ 2 := by
            have hcast : ((D * D : ℕ) : ℝ) = (D : ℝ) ^ 2 := by push_cast; ring
            rw [← hcast]
            exact_mod_cast hrc_le
    calc ∑ d₁ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
          ∑ d₂ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
            |Arith4Ext.SieveCharacters.sieveRemainder A (fun _ => (1 : ℝ)) (N : ℝ) g
              (Nat.lcm d₁ d₂)|
        ≤ ∑ _d₁ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D,
            ∑ _d₂ ∈ Arith4Ext.SieveCharacters.sieveDivisors P D, (D : ℝ) ^ 2 :=
          Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂
      _ = ((Arith4Ext.SieveCharacters.sieveDivisors P D).card : ℝ) ^ 2 * (D : ℝ) ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (D : ℝ) ^ 2 * (D : ℝ) ^ 2 := by
          have hc : ((Arith4Ext.SieveCharacters.sieveDivisors P D).card : ℝ) ≤ (D : ℝ) := by
            exact_mod_cast hcard_le
          have hsq : ((Arith4Ext.SieveCharacters.sieveDivisors P D).card : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
          exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (D : ℝ) ^ 4 := by ring
  linarith

/-! ### Section 3A: Pointwise Brun–Titchmarsh & Quadratic Selberg Sieve Bounds on `S(n)` -/

/-- **Pointwise Brun–Titchmarsh Upper Bound on `S(n)`**:
For every `n ≥ 2`, the simultaneous prime pair count
`S(n) = #{0 ≤ k < n : Prime(n + k) ∧ Prime(n + k²)}` satisfies `S(n) ≤ 9 n / log n`. -/
theorem ppl087_single_n_brun_titchmarsh_bound {n : ℕ} (hn : 2 ≤ n) :
    (((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) ≤
      9 * (n : ℝ) / Real.log (n : ℝ) := by
  have hbt := Arith4Ext.SieveCharacters.brun_titchmarsh_interval (n - 1) n hn
  have hcard : ((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card ≤
      ((Finset.Icc ((n - 1) + 1) ((n - 1) + n)).filter Nat.Prime).card := by
    have himg : (((Finset.range n).filter
        (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).image (fun k => n + k)) ⊆
        (Finset.Icc ((n - 1) + 1) ((n - 1) + n)).filter Nat.Prime := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hk.2.1⟩
    calc ((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card
        = (((Finset.range n).filter
            (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).image (fun k => n + k)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => by omega)).symm
      _ ≤ ((Finset.Icc ((n - 1) + 1) ((n - 1) + n)).filter Nat.Prime).card :=
          Finset.card_le_card himg
  exact (by exact_mod_cast hcard : _ ≤ _).trans hbt

private lemma quadPoly_modEq (n d x y : ℕ) (hxy : x ≡ y [MOD d]) :
    (n + x) * (n + x ^ 2) ≡ (n + y) * (n + y ^ 2) [MOD d] :=
  (Nat.ModEq.add_left n hxy).mul (Nat.ModEq.add_left n (hxy.pow 2))

private lemma quadPoly_rootCount_prime (n p : ℕ) [Fact p.Prime] :
    polyRootCount (fun k => (n + k) * (n + k ^ 2)) p =
      ((Finset.univ : Finset (ZMod p)).filter
        (fun r => (n : ZMod p) + r = 0 ∨ (n : ZMod p) + r ^ 2 = 0)).card := by
  have hp_prime : p.Prime := Fact.out
  unfold polyRootCount
  refine Finset.card_bij (fun r _ => (r : ZMod p)) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hp_prime.dvd_mul.mp hr.2 with h1 | h2
    · left
      have h0 : ((n + r : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + r) p).mpr h1
      simpa using h0
    · right
      have h0 : ((n + r ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + r ^ 2) p).mpr h2
      simpa using h0
  · intro r₁ hr₁ r₂ hr₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    have hmod : r₁ ≡ r₂ [MOD p] := (ZMod.natCast_eq_natCast_iff r₁ r₂ p).mp heq
    have h1 : r₁ % p = r₁ := Nat.mod_eq_of_lt hr₁.1
    have h2 : r₂ % p = r₂ := Nat.mod_eq_of_lt hr₂.1
    change r₁ % p = r₂ % p at hmod
    omega
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨z.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt z), ?_⟩,
      ZMod.natCast_zmod_val z⟩
    rcases hz with h1 | h2
    · have h0 : ((n + z.val : ℕ) : ZMod p) = 0 := by simpa [ZMod.natCast_zmod_val] using h1
      exact dvd_mul_of_dvd_left ((ZMod.natCast_eq_zero_iff (n + z.val) p).mp h0) _
    · have h0 : ((n + z.val ^ 2 : ℕ) : ZMod p) = 0 := by simpa [ZMod.natCast_zmod_val] using h2
      exact dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff (n + z.val ^ 2) p).mp h0) _

/-- **Pointwise Quadratic Selberg Sieve Upper Bound on `S(n)`**:
For every `n`, `D ≥ 1`, and `z < n`, applying Selberg's upper-bound sieve directly to
`F_n(k) = (n + k)(n + k²)` with its exact local root-count density `ν_n(p) / p` yields:
`S(n) ≤ n / (∑_{m ∣ P(z), m ≤ D} ∏_{p ∣ m} ν_n(p) / (p - ν_n(p))) + D⁴`,
where `ν_n(p) = #{0 ≤ r < p : p ∣ n + r ∨ p ∣ n + r²}`. -/
theorem ppl087_single_n_selberg_quadratic_sieve_bound {n z D : ℕ}
    (hD : 1 ≤ D) (hzn : z < n) :
    (((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) ≤
      (n : ℝ) /
        (∑ m ∈ (∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, p).divisors.filter (· ≤ D),
          ∏ p ∈ m.primeFactors,
            (((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card : ℝ) /
              ((p : ℝ) -
                (((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card : ℝ))) +
        (D : ℝ) ^ 4 := by
  set F : ℕ → ℕ := fun k => (n + k) * (n + k ^ 2)
  set P := Arith4Ext.SieveCharacters.primorial z
  have hFinj : Set.InjOn F (Finset.Ico 0 (0 + n) : Set ℕ) := by
    intro k₁ _ k₂ _ heq
    dsimp only [F] at heq
    rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
    · have h1 : n + k₁ < n + k₂ := by omega
      have h2 : n + k₁ ^ 2 < n + k₂ ^ 2 := by nlinarith
      have : (n + k₁) * (n + k₁ ^ 2) < (n + k₂) * (n + k₂ ^ 2) :=
        Nat.mul_lt_mul_of_lt_of_lt h1 h2
      omega
    · rfl
    · have h1 : n + k₂ < n + k₁ := by omega
      have h2 : n + k₂ ^ 2 < n + k₁ ^ 2 := by nlinarith
      have : (n + k₂) * (n + k₂ ^ 2) < (n + k₁) * (n + k₁ ^ 2) :=
        Nat.mul_lt_mul_of_lt_of_lt h1 h2
      omega
  have hrc_eq_or : ∀ p : ℕ, Nat.Prime p →
      polyRootCount F p = ((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card := by
    intro p hp
    unfold polyRootCount
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, F, hp.dvd_mul]
  have h01 : ∀ p ∈ P.primeFactors,
      0 < (polyRootCount F p : ℝ) / (p : ℝ) ∧ (polyRootCount F p : ℝ) / (p : ℝ) < 1 := by
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hp_prime⟩
    rw [quadPoly_rootCount_prime n p]
    have hadm := ppl087_universal_local_admissibility n p
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hnu_pos : (0 : ℝ) < (((Finset.univ : Finset (ZMod p)).filter
        (fun r => (n : ZMod p) + r = 0 ∨ (n : ZMod p) + r ^ 2 = 0)).card : ℝ) := by
      exact_mod_cast (by omega : 0 < _)
    have hnu_lt : (((Finset.univ : Finset (ZMod p)).filter
        (fun r => (n : ZMod p) + r = 0 ∨ (n : ZMod p) + r ^ 2 = 0)).card : ℝ) < (p : ℝ) := by
      exact_mod_cast hadm.2.1
    exact ⟨div_pos hnu_pos hp_pos, (div_lt_one hp_pos).mpr hnu_lt⟩
  have hsub : (Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2)) ⊆
      (Finset.Ico 0 (0 + n)).filter (fun k => Nat.Coprime (F k) P) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, zero_add] at hk ⊢
    refine ⟨⟨Nat.zero_le k, hk.1⟩, ?_⟩
    dsimp only [F]
    refine Nat.Coprime.mul_left ?_ ?_
    · rw [hk.2.1.coprime_iff_not_dvd]
      intro hdvd
      have hle : n + k ≤ z := (Arith4Ext.SieveCharacters.prime_dvd_primorial_iff hk.2.1).mp hdvd
      omega
    · rw [hk.2.2.coprime_iff_not_dvd]
      intro hdvd
      have hle : n + k ^ 2 ≤ z := (Arith4Ext.SieveCharacters.prime_dvd_primorial_iff hk.2.2).mp hdvd
      omega
  have hcard_le : (((Finset.range n).filter
      (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) ≤
      (((Finset.Ico 0 (0 + n)).filter (fun k => Nat.Coprime (F k) P)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hsel := poly_selberg_sieve_Ico (quadPoly_modEq n) hFinj hD h01
  have hG_eq : Arith4Ext.SieveCharacters.selbergG
      (fun d => (polyRootCount F d : ℝ) / (d : ℝ)) P D =
      ∑ m ∈ (∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, p).divisors.filter (· ≤ D),
        ∏ p ∈ m.primeFactors,
          (((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card : ℝ) /
            ((p : ℝ) -
              (((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card : ℝ)) := by
    unfold Arith4Ext.SieveCharacters.selbergG Arith4Ext.SieveCharacters.sieveDivisors
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_dvd : m ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm).1).1
    have hm_sq : Squarefree m := (Arith4Ext.SieveCharacters.primorial_squarefree z).squarefree_of_dvd hm_dvd
    rw [Arith4Ext.SieveCharacters.selbergH_eq_prod_primeFactors (poly_density_isMult (quadPoly_modEq n)) hm_sq,
      ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hp_prime⟩
    have hadm := ppl087_universal_local_admissibility n p
    have hnu_eq : ((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card =
        ((Finset.univ : Finset (ZMod p)).filter
          (fun r => (n : ZMod p) + r = 0 ∨ (n : ZMod p) + r ^ 2 = 0)).card := by
      rw [← hrc_eq_or p hp_prime, quadPoly_rootCount_prime n p]
    rw [hrc_eq_or p hp_prime]
    have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
    have hnu_ne : (((Finset.range p).filter (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card : ℝ) ≠ 0 := by
      rw [hnu_eq]; exact_mod_cast (by omega : _ ≠ 0)
    have hsub_ne : (p : ℝ) - (((Finset.range p).filter
        (fun r => p ∣ n + r ∨ p ∣ n + r ^ 2)).card : ℝ) ≠ 0 := by
      rw [hnu_eq]
      have hlt : (((Finset.univ : Finset (ZMod p)).filter
          (fun r => (n : ZMod p) + r = 0 ∨ (n : ZMod p) + r ^ 2 = 0)).card : ℝ) < (p : ℝ) := by
        exact_mod_cast hadm.2.1
      linarith
    field_simp [hp_ne, hnu_ne, hsub_ne]
  rw [hG_eq] at hsel
  linarith

/-! ### Section 3B: Unconditional Dimension-2 Brun–Selberg Sieve for Even-Shift Prime Pairs -/

private lemma pairPoly_modEq (h d x y : ℕ) (hxy : x ≡ y [MOD d]) :
    x * (x + h) ≡ y * (y + h) [MOD d] :=
  hxy.mul (Nat.ModEq.add_right h hxy)

private lemma pairPoly_rootCount_prime (h p : ℕ) (hp : Nat.Prime p) :
    polyRootCount (fun x => x * (x + h)) p = if p ∣ h then 1 else 2 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold polyRootCount
  have hbij : ((Finset.range p).filter (fun r => p ∣ r * (r + h))).card =
      ((Finset.univ : Finset (ZMod p)).filter
        (fun r => r = 0 ∨ r + (h : ZMod p) = 0)).card := by
    refine Finset.card_bij (fun r _ => (r : ZMod p)) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp.dvd_mul.mp hr.2 with h1 | h2
      · left; exact (ZMod.natCast_eq_zero_iff r p).mpr h1
      · right; simpa using (ZMod.natCast_eq_zero_iff (r + h) p).mpr h2
    · intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
      have hmod : r₁ ≡ r₂ [MOD p] := (ZMod.natCast_eq_natCast_iff r₁ r₂ p).mp heq
      change r₁ % p = r₂ % p at hmod
      rw [Nat.mod_eq_of_lt hr₁.1, Nat.mod_eq_of_lt hr₂.1] at hmod
      exact hmod
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨z.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt z), ?_⟩,
        ZMod.natCast_zmod_val z⟩
      rcases hz with h1 | h2
      · have h0 : (z.val : ZMod p) = 0 := by simpa [ZMod.natCast_zmod_val] using h1
        exact dvd_mul_of_dvd_left ((ZMod.natCast_eq_zero_iff z.val p).mp h0) _
      · have h0 : ((z.val + h : ℕ) : ZMod p) = 0 := by simpa [ZMod.natCast_zmod_val] using h2
        exact dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff (z.val + h) p).mp h0) _
  rw [hbij]
  have hfilt : (Finset.univ : Finset (ZMod p)).filter (fun r => r = 0 ∨ r + (h : ZMod p) = 0) =
      {0, -(h : ZMod p)} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl h1
      · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (neg_add_cancel _)
  rw [hfilt]
  by_cases hdvd : p ∣ h
  · have h0 : (h : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff h p).mpr hdvd
    rw [h0, neg_zero, Finset.pair_eq_singleton, Finset.card_singleton, if_pos hdvd]
  · have hne : (0 : ZMod p) ≠ -(h : ZMod p) := by
      intro heq
      have h0 : (h : ZMod p) = 0 := neg_eq_zero.mp heq.symm
      exact hdvd ((ZMod.natCast_eq_zero_iff h p).mp h0)
    rw [Finset.card_pair hne, if_neg hdvd]

private lemma sum_inv_pow_Icc0_le {p M : ℕ} (hp : Nat.Prime p) :
    ∑ k ∈ Finset.Icc 0 M, ((p : ℝ) ^ k)⁻¹ ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hIcc : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : 0 ∉ Finset.Icc 1 M := by simp
  rw [hIcc, Finset.sum_insert hnot, pow_zero, inv_one]
  have h1 := Arith4Ext.SieveCharacters.sum_inv_pow_Icc_le (D := M) hp
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsub : (p : ℝ) - 1 ≠ 0 := by linarith
  have heq : 1 + ((p : ℝ) - 1)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    field_simp [hsub]; ring
  linarith

private lemma sum_inv_pair_pow_le {p M : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    ∑ x ∈ ((Finset.Icc 0 M ×ˢ Finset.Icc 0 M).filter (fun x => x ≠ (0, 0))),
        ((p : ℝ) ^ x.1)⁻¹ * ((p : ℝ) ^ x.2)⁻¹ ≤ 2 / ((p : ℝ) - 2) := by
  have h00 : (0, 0) ∈ Finset.Icc 0 M ×ˢ Finset.Icc 0 M := by simp
  have hfilt : (Finset.Icc 0 M ×ˢ Finset.Icc 0 M).filter (fun x => x ≠ (0, 0)) =
      (Finset.Icc 0 M ×ˢ Finset.Icc 0 M).erase (0, 0) := by
    ext x; simp [and_comm]
  rw [hfilt, Finset.sum_erase_eq_sub h00]
  simp only [pow_zero, inv_one, mul_one]
  rw [Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum]
  have h1 := sum_inv_pow_Icc0_le (M := M) hp
  have hnn : 0 ≤ ∑ k ∈ Finset.Icc 0 M, ((p : ℝ) ^ k)⁻¹ :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hsq : (∑ k ∈ Finset.Icc 0 M, ((p : ℝ) ^ k)⁻¹) * (∑ k ∈ Finset.Icc 0 M, ((p : ℝ) ^ k)⁻¹) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    rw [sq]; exact mul_le_mul h1 h1 hnn (by
      have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      exact div_nonneg (by linarith) (by linarith))
  have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hdiff : ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1 ≤ 2 / ((p : ℝ) - 2) := by
    have h1ne : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2pos : 0 < (p : ℝ) - 2 := by linarith
    have h1pos : 0 < ((p : ℝ) - 1) ^ 2 := by positivity
    rw [div_pow, sub_le_iff_le_add]
    have hlhs : (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 - 1 =
        (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
      field_simp [h1ne]; ring
    have hstep : (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 ≤ 2 / ((p : ℝ) - 2) := by
      rw [div_le_div_iff₀ h1pos h2pos]
      nlinarith
    linarith
  linarith

private lemma sum_inv_pair_primeFactors_eq_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ 3 ≤ p) (M : ℕ) :
    ∑ x ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun x => (x.1 * x.2).primeFactors = S),
        (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ ≤ ∏ p ∈ S, (2 : ℝ) / ((p : ℝ) - 2) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun x => (x.1 * x.2).primeFactors = ∅) ⊆ {(1, 1)} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
      simp only [Finset.mem_singleton]
      have hprod_pos : 0 < x.1 * x.2 := Nat.mul_pos (by omega) (by omega)
      have hprod1 : x.1 * x.2 = 1 := by
        by_contra hne1
        rcases Nat.exists_prime_and_dvd hne1 with ⟨p, hp, hpd⟩
        have hmem : p ∈ (x.1 * x.2).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, hpd, hprod_pos.ne'⟩
        rw [hx.2] at hmem
        exact Finset.notMem_empty p hmem
      have h1 : x.1 = 1 := Nat.eq_one_of_mul_eq_one_right hprod1
      have h2 : x.2 = 1 := Nat.eq_one_of_mul_eq_one_left hprod1
      exact Prod.ext h1 h2
    calc ∑ x ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
            (fun x => (x.1 * x.2).primeFactors = ∅), (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹
        ≤ ∑ x ∈ ({(1, 1)} : Finset (ℕ × ℕ)), (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := (hS a (Finset.mem_insert_self a s)).1
    have ha_3 : 3 ≤ a := (hS a (Finset.mem_insert_self a s)).2
    have hs_p : ∀ p ∈ s, Nat.Prime p ∧ 3 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha]
    set F := (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun x => (x.1 * x.2).primeFactors = insert a s)
    set K := (Finset.Icc 0 M ×ˢ Finset.Icc 0 M).filter (fun k => k ≠ (0, 0))
    set R := (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun r => (r.1 * r.2).primeFactors = s)
    set φ : (ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) := fun x =>
      ((x.1.factorization a, x.2.factorization a),
       (x.1 / a ^ (x.1.factorization a), x.2 / a ^ (x.2.factorization a)))
    have hφ_mem : ∀ x ∈ F, φ x ∈ K ×ˢ R := by
      intro x hx
      simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
      have hx1_pos : 0 < x.1 := by omega
      have hx2_pos : 0 < x.2 := by omega
      set k₁ := x.1.factorization a
      set k₂ := x.2.factorization a
      have hk1_le : k₁ ≤ M := by
        by_cases h0 : k₁ = 0
        · omega
        · have h1 : k₁ < a ^ k₁ := Nat.lt_pow_self ha_p.one_lt
          have h2 : a ^ k₁ ≤ x.1 := Nat.le_of_dvd hx1_pos (Nat.ordProj_dvd x.1 a)
          omega
      have hk2_le : k₂ ≤ M := by
        by_cases h0 : k₂ = 0
        · omega
        · have h1 : k₂ < a ^ k₂ := Nat.lt_pow_self ha_p.one_lt
          have h2 : a ^ k₂ ≤ x.2 := Nat.le_of_dvd hx2_pos (Nat.ordProj_dvd x.2 a)
          omega
      have hk_ne00 : (k₁, k₂) ≠ (0, 0) := by
        intro h00
        have hk10 : k₁ = 0 := congr_arg Prod.fst h00
        have hk20 : k₂ = 0 := congr_arg Prod.snd h00
        have ha_mem : a ∈ (x.1 * x.2).primeFactors := by
          rw [hx.2]; exact Finset.mem_insert_self a s
        have ha_dvd : a ∣ x.1 * x.2 := Nat.dvd_of_mem_primeFactors ha_mem
        rcases ha_p.dvd_mul.mp ha_dvd with h1 | h2
        · have := Nat.Prime.factorization_pos_of_dvd ha_p hx1_pos.ne' h1; omega
        · have := Nat.Prime.factorization_pos_of_dvd ha_p hx2_pos.ne' h2; omega
      set r₁ := x.1 / a ^ k₁
      set r₂ := x.2 / a ^ k₂
      have hmul1 : a ^ k₁ * r₁ = x.1 := Nat.mul_div_cancel' (Nat.ordProj_dvd x.1 a)
      have hmul2 : a ^ k₂ * r₂ = x.2 := Nat.mul_div_cancel' (Nat.ordProj_dvd x.2 a)
      have hr1_pos : 1 ≤ r₁ := by
        by_contra h0
        have hr0 : r₁ = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
        rw [hr0, mul_zero] at hmul1
        exact hx1_pos.ne' hmul1.symm
      have hr2_pos : 1 ≤ r₂ := by
        by_contra h0
        have hr0 : r₂ = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
        rw [hr0, mul_zero] at hmul2
        exact hx2_pos.ne' hmul2.symm
      have hr1_le : r₁ ≤ M := (Nat.div_le_self x.1 _).trans hx.1.1.2
      have hr2_le : r₂ ≤ M := (Nat.div_le_self x.2 _).trans hx.1.2.2
      have hna1 : ¬ a ∣ r₁ := by
        intro hd
        have hpow : a ^ (k₁ + 1) ∣ x.1 := by rw [pow_succ, ← hmul1]; exact mul_dvd_mul_left _ hd
        have := (ha_p.pow_dvd_iff_le_factorization hx1_pos.ne').mp hpow
        omega
      have hna2 : ¬ a ∣ r₂ := by
        intro hd
        have hpow : a ^ (k₂ + 1) ∣ x.2 := by rw [pow_succ, ← hmul2]; exact mul_dvd_mul_left _ hd
        have := (ha_p.pow_dvd_iff_le_factorization hx2_pos.ne').mp hpow
        omega
      have hna_prod : ¬ a ∣ r₁ * r₂ := fun hd => by
        rcases ha_p.dvd_mul.mp hd with h1 | h2
        · exact hna1 h1
        · exact hna2 h2
      have hprod_eq : x.1 * x.2 = a ^ (k₁ + k₂) * (r₁ * r₂) := by
        rw [← hmul1, ← hmul2, pow_add]; ring
      have hk12_pos : k₁ + k₂ ≠ 0 := by
        intro h0; apply hk_ne00; exact Prod.ext (by omega) (by omega)
      have hr_pf : (r₁ * r₂).primeFactors = s := by
        have hpf : (x.1 * x.2).primeFactors = {a} ∪ (r₁ * r₂).primeFactors := by
          rw [hprod_eq, Nat.primeFactors_mul (pow_ne_zero _ ha_p.ne_zero)
            (Nat.mul_pos hr1_pos hr2_pos).ne', Nat.primeFactors_pow a hk12_pos, ha_p.primeFactors]
        rw [hx.2] at hpf
        ext p
        constructor
        · intro hp
          have hp_in : p ∈ insert a s := by rw [hpf]; exact Finset.mem_union_right _ hp
          rcases Finset.mem_insert.mp hp_in with rfl | hps
          · exact absurd (Nat.dvd_of_mem_primeFactors hp) hna_prod
          · exact hps
        · intro hp
          have hp_in : p ∈ ({a} : Finset ℕ) ∪ (r₁ * r₂).primeFactors := by
            rw [← hpf]; exact Finset.mem_insert_of_mem hp
          rcases Finset.mem_union.mp hp_in with hpa | hpr
          · rw [Finset.mem_singleton.mp hpa] at hp; exact absurd hp ha
          · exact hpr
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk1_le⟩, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk2_le⟩⟩,
          hk_ne00⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hr1_pos, hr1_le⟩, Finset.mem_Icc.mpr ⟨hr2_pos, hr2_le⟩⟩, hr_pf⟩⟩
    have hφ_inj : Set.InjOn φ ↑F := by
      intro x₁ _ x₂ _ heq
      have h1a : a ^ (x₁.1.factorization a) * (x₁.1 / a ^ (x₁.1.factorization a)) = x₁.1 :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd x₁.1 a)
      have h1b : a ^ (x₁.2.factorization a) * (x₁.2 / a ^ (x₁.2.factorization a)) = x₁.2 :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd x₁.2 a)
      have h2a : a ^ (x₂.1.factorization a) * (x₂.1 / a ^ (x₂.1.factorization a)) = x₂.1 :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd x₂.1 a)
      have h2b : a ^ (x₂.2.factorization a) * (x₂.2 / a ^ (x₂.2.factorization a)) = x₂.2 :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd x₂.2 a)
      have hk1 := congr_arg (fun z => z.1.1) heq
      have hk2 := congr_arg (fun z => z.1.2) heq
      have hr1 := congr_arg (fun z => z.2.1) heq
      have hr2 := congr_arg (fun z => z.2.2) heq
      dsimp [φ] at hk1 hk2 hr1 hr2
      exact Prod.ext (by rw [← h1a, ← h2a, hr1, hk1]) (by rw [← h1b, ← h2b, hr2, hk2])
    have hsum_le : ∑ x ∈ F, (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ ≤
        ∑ y ∈ K ×ˢ R, (((a : ℝ) ^ y.1.1)⁻¹ * ((a : ℝ) ^ y.1.2)⁻¹) *
          ((y.2.1 : ℝ)⁻¹ * (y.2.2 : ℝ)⁻¹) := by
      calc ∑ x ∈ F, (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹
          = ∑ x ∈ F, (((a : ℝ) ^ (φ x).1.1)⁻¹ * ((a : ℝ) ^ (φ x).1.2)⁻¹) *
              (((φ x).2.1 : ℝ)⁻¹ * ((φ x).2.2 : ℝ)⁻¹) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            have h1 : a ^ (x.1.factorization a) * (x.1 / a ^ (x.1.factorization a)) = x.1 :=
              Nat.mul_div_cancel' (Nat.ordProj_dvd x.1 a)
            have h2 : a ^ (x.2.factorization a) * (x.2 / a ^ (x.2.factorization a)) = x.2 :=
              Nat.mul_div_cancel' (Nat.ordProj_dvd x.2 a)
            dsimp [φ]
            conv_lhs => rw [← h1, ← h2]
            push_cast
            rw [mul_inv, mul_inv]
            ring
        _ = ∑ y ∈ F.image φ, (((a : ℝ) ^ y.1.1)⁻¹ * ((a : ℝ) ^ y.1.2)⁻¹) *
              ((y.2.1 : ℝ)⁻¹ * (y.2.2 : ℝ)⁻¹) :=
            (Finset.sum_image (f := fun y : (ℕ × ℕ) × (ℕ × ℕ) =>
              (((a : ℝ) ^ y.1.1)⁻¹ * ((a : ℝ) ^ y.1.2)⁻¹) *
                ((y.2.1 : ℝ)⁻¹ * (y.2.2 : ℝ)⁻¹)) hφ_inj).symm
        _ ≤ ∑ y ∈ K ×ˢ R, (((a : ℝ) ^ y.1.1)⁻¹ * ((a : ℝ) ^ y.1.2)⁻¹) *
              ((y.2.1 : ℝ)⁻¹ * (y.2.2 : ℝ)⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
            exact hφ_mem x hx
    rw [Finset.sum_product] at hsum_le
    dsimp only at hsum_le
    rw [← Finset.sum_mul_sum] at hsum_le
    have ha2_nn : (0 : ℝ) ≤ (2 : ℝ) / ((a : ℝ) - 2) := by
      have : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_3
      exact div_nonneg (by norm_num) (by linarith)
    calc ∑ x ∈ F, (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹
        ≤ (∑ k ∈ K, ((a : ℝ) ^ k.1)⁻¹ * ((a : ℝ) ^ k.2)⁻¹) *
            (∑ r ∈ R, (r.1 : ℝ)⁻¹ * (r.2 : ℝ)⁻¹) := hsum_le
      _ ≤ ((2 : ℝ) / ((a : ℝ) - 2)) * ∏ p ∈ s, (2 : ℝ) / ((p : ℝ) - 2) :=
          mul_le_mul (sum_inv_pair_pow_le ha_p ha_3) (ih hs_p)
            (Finset.sum_nonneg fun _ _ => by positivity) ha2_nn

private lemma sum_inv_smooth_le (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (M : ℕ) :
    ∑ u ∈ (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ S), (u : ℝ)⁻¹ ≤
      ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ ∅) ⊆ {1} := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.subset_empty] at hu
      simp only [Finset.mem_singleton]
      by_contra hne1
      rcases Nat.exists_prime_and_dvd hne1 with ⟨p, hp, hpd⟩
      have hmem : p ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
      rw [hu.2] at hmem
      exact Finset.notMem_empty p hmem
    calc ∑ u ∈ (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ ∅), (u : ℝ)⁻¹
        ≤ ∑ u ∈ ({1} : Finset ℕ), (u : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hS a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha]
    set F := (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ insert a s)
    set R := (Finset.Icc 1 M).filter (fun r => r.primeFactors ⊆ s)
    set φ : ℕ → ℕ × ℕ := fun u => (u.factorization a, u / a ^ (u.factorization a))
    have hφ_mem : ∀ u ∈ F, φ u ∈ Finset.Icc 0 M ×ˢ R := by
      intro u hu
      simp only [F, Finset.mem_filter, Finset.mem_Icc] at hu
      have hu_pos : 0 < u := by omega
      set k := u.factorization a
      have hk_le : k ≤ M := by
        by_cases h0 : k = 0
        · omega
        · have h1 : k < a ^ k := Nat.lt_pow_self ha_p.one_lt
          have h2 : a ^ k ≤ u := Nat.le_of_dvd hu_pos (Nat.ordProj_dvd u a)
          omega
      set r := u / a ^ k
      have hmul : a ^ k * r = u := Nat.mul_div_cancel' (Nat.ordProj_dvd u a)
      have hr_pos : 1 ≤ r := by
        by_contra h0
        have hr0 : r = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
        rw [hr0, mul_zero] at hmul
        exact hu_pos.ne' hmul.symm
      have hr_le : r ≤ M := (Nat.div_le_self u _).trans hu.1.2
      have hna : ¬ a ∣ r := by
        intro hd
        have hpow : a ^ (k + 1) ∣ u := by rw [pow_succ, ← hmul]; exact mul_dvd_mul_left _ hd
        have := (ha_p.pow_dvd_iff_le_factorization hu_pos.ne').mp hpow
        omega
      have hr_sub : r.primeFactors ⊆ s := by
        intro p hp
        have hp_dvd_u : p ∣ u := (Nat.dvd_of_mem_primeFactors hp).trans (by rw [← hmul]; exact dvd_mul_left r _)
        have hp_mem : p ∈ u.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hp_dvd_u, hu_pos.ne'⟩
        rcases Finset.mem_insert.mp (hu.2 hp_mem) with rfl | hps
        · exact absurd (Nat.dvd_of_mem_primeFactors hp) hna
        · exact hps
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk_le⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr_pos, hr_le⟩, hr_sub⟩⟩
    have hφ_inj : Set.InjOn φ ↑F := by
      intro u₁ _ u₂ _ heq
      have h1 : a ^ (u₁.factorization a) * (u₁ / a ^ (u₁.factorization a)) = u₁ :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd u₁ a)
      have h2 : a ^ (u₂.factorization a) * (u₂ / a ^ (u₂.factorization a)) = u₂ :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd u₂ a)
      have hk := congr_arg Prod.fst heq
      have hr := congr_arg Prod.snd heq
      dsimp [φ] at hk hr
      rw [← h1, ← h2, hr, hk]
    have hsum_le : ∑ u ∈ F, (u : ℝ)⁻¹ ≤
        ∑ y ∈ Finset.Icc 0 M ×ˢ R, ((a : ℝ) ^ y.1)⁻¹ * (y.2 : ℝ)⁻¹ := by
      calc ∑ u ∈ F, (u : ℝ)⁻¹
          = ∑ u ∈ F, ((a : ℝ) ^ (φ u).1)⁻¹ * ((φ u).2 : ℝ)⁻¹ := by
            refine Finset.sum_congr rfl fun u _ => ?_
            have hmul : a ^ (u.factorization a) * (u / a ^ (u.factorization a)) = u :=
              Nat.mul_div_cancel' (Nat.ordProj_dvd u a)
            dsimp [φ]
            conv_lhs => rw [← hmul]
            push_cast; rw [mul_inv]
        _ = ∑ y ∈ F.image φ, ((a : ℝ) ^ y.1)⁻¹ * (y.2 : ℝ)⁻¹ :=
            (Finset.sum_image (f := fun y : ℕ × ℕ => ((a : ℝ) ^ y.1)⁻¹ * (y.2 : ℝ)⁻¹) hφ_inj).symm
        _ ≤ ∑ y ∈ Finset.Icc 0 M ×ˢ R, ((a : ℝ) ^ y.1)⁻¹ * (y.2 : ℝ)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
            exact hφ_mem u hu
    rw [Finset.sum_product] at hsum_le
    dsimp only at hsum_le
    rw [← Finset.sum_mul_sum] at hsum_le
    have ha_pos : (0 : ℝ) ≤ (a : ℝ) / ((a : ℝ) - 1) := by
      have : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha_p.one_lt
      positivity
    calc ∑ u ∈ F, (u : ℝ)⁻¹
        ≤ (∑ k ∈ Finset.Icc 0 M, ((a : ℝ) ^ k)⁻¹) * (∑ r ∈ R, (r : ℝ)⁻¹) := hsum_le
      _ ≤ ((a : ℝ) / ((a : ℝ) - 1)) * ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) :=
          mul_le_mul (sum_inv_pow_Icc0_le ha_p) (ih hs_p)
            (Finset.sum_nonneg fun _ _ => by positivity) ha_pos

private lemma nat_div_totient_eq_prod {h : ℕ} (hh : 0 < h) :
    (h : ℝ) / (Nat.totient h : ℝ) = ∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have htot := Nat.totient_eq_mul_prod_factors h
  have htot_r : (Nat.totient h : ℝ) =
      (h : ℝ) * ∏ p ∈ h.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    have hq : ((Nat.totient h : ℚ) : ℝ) =
        (((h : ℚ) * ∏ p ∈ h.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by
      exact_mod_cast htot
    simpa [Rat.cast_prod, Rat.cast_sub, Rat.cast_inv] using hq
  have hprod_eq : ∏ p ∈ h.primeFactors, (1 - ((p : ℝ))⁻¹) =
      ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) / (p : ℝ) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp [hp_ne]
  have hh_ne : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have htot_ne : (Nat.totient h : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hh).ne'
  have hprod_ne : ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) / (p : ℝ) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
    exact div_ne_zero (by linarith) (by linarith)
  rw [htot_r, hprod_eq]
  rw [div_eq_iff (mul_ne_zero hh_ne hprod_ne)]
  calc (h : ℝ) = (h : ℝ) * 1 := (mul_one _).symm
    _ = (h : ℝ) * ((∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
          (∏ p ∈ h.primeFactors, ((p : ℝ) - 1) / (p : ℝ))) := by
        congr 1
        rw [← Finset.prod_mul_distrib]
        symm
        refine Finset.prod_eq_one fun p hp => ?_
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
        field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
    _ = (∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
          ((h : ℝ) * ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) / (p : ℝ)) := by ring

private lemma coprime_harmonic_lower_bound {h M : ℕ} (hh : 0 < h) :
    ((Nat.totient h : ℝ) / (h : ℝ)) * Real.log ((M : ℝ) + 1) ≤
      ∑ a ∈ (Finset.Icc 1 M).filter (fun a => Nat.Coprime a h), (a : ℝ)⁻¹ := by
  classical
  set S := h.primeFactors
  set U := (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ S)
  set C := (Finset.Icc 1 M).filter (fun a => Nat.Coprime a h)
  set split : ℕ → ℕ × ℕ := fun n =>
    (∏ p ∈ S, p ^ (n.factorization p), n / (∏ p ∈ S, p ^ (n.factorization p)))
  have hsplit_dvd : ∀ n ∈ Finset.Icc 1 M, (∏ p ∈ S, p ^ (n.factorization p)) ∣ n := by
    intro n hn
    have hn_ne : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn_ne]
    rw [Finsupp.prod, Nat.support_factorization]
    have hsplit_prod : ∏ p ∈ S, p ^ (n.factorization p) =
        ∏ p ∈ S ∩ n.primeFactors, p ^ (n.factorization p) := by
      symm
      refine Finset.prod_subset Finset.inter_subset_left fun p hp hnp => ?_
      have hnp2 : p ∉ n.primeFactors := fun h => hnp (Finset.mem_inter.mpr ⟨hp, h⟩)
      have h0 : n.factorization p = 0 := by
        by_contra hne
        exact hnp2 (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors (by exact hp),
           (Nat.Prime.dvd_iff_one_le_factorization (Nat.prime_of_mem_primeFactors hp) hn_ne).mpr (by omega),
           hn_ne⟩)
      simp [h0]
    rw [hsplit_prod]
    exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
  have hsplit_mem : ∀ n ∈ Finset.Icc 1 M, split n ∈ U ×ˢ C := by
    intro n hn
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hn_le : n ≤ M := (Finset.mem_Icc.mp hn).2
    set u := ∏ p ∈ S, p ^ (n.factorization p)
    have hu_pos : 0 < u := Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
    have hu_dvd : u ∣ n := hsplit_dvd n hn
    have hu_le : u ≤ M := (Nat.le_of_dvd hn_pos hu_dvd).trans hn_le
    have hu_pf : u.primeFactors ⊆ S := by
      intro q hq
      have hq_prime := Nat.prime_of_mem_primeFactors hq
      have hq_dvd : q ∣ ∏ p ∈ S, p ^ (n.factorization p) := Nat.dvd_of_mem_primeFactors hq
      rcases (hq_prime.prime.dvd_finsetProd_iff _).mp hq_dvd with ⟨p, hp, hqp⟩
      have hqp1 : q ∣ p := hq_prime.dvd_of_dvd_pow hqp
      have hpeq : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime (Nat.prime_of_mem_primeFactors hp)).mp hqp1
      rw [hpeq]; exact hp
    set a := n / u
    have hmul : u * a = n := Nat.mul_div_cancel' hu_dvd
    have ha_pos : 1 ≤ a := by
      by_contra h0
      have ha0 : a = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
      rw [ha0, mul_zero] at hmul
      exact hn_pos.ne' hmul.symm
    have ha_le : a ≤ M := (Nat.div_le_self n u).trans hn_le
    have ha_cop : Nat.Coprime a h := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne1
      rcases Nat.exists_prime_and_dvd hne1 with ⟨p, hp, hpg⟩
      have hpa : p ∣ a := hpg.trans (Nat.gcd_dvd_left a h)
      have hph : p ∣ h := hpg.trans (Nat.gcd_dvd_right a h)
      have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp, hph, hh.ne'⟩
      have hpow_u : p ^ (n.factorization p) ∣ u := Finset.dvd_prod_of_mem _ hpS
      have hpow_n : p ^ (n.factorization p + 1) ∣ n := by
        calc p ^ (n.factorization p + 1) = p ^ (n.factorization p) * p := pow_succ _ _
          _ ∣ u * a := mul_dvd_mul hpow_u hpa
          _ = n := hmul
      have := (hp.pow_dvd_iff_le_factorization hn_pos.ne').mp hpow_n
      omega
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu_pos, hu_le⟩, hu_pf⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha_pos, ha_le⟩, ha_cop⟩⟩
  have hsplit_inj : Set.InjOn split ↑(Finset.Icc 1 M) := by
    intro n₁ hn₁ n₂ hn₂ heq
    have h1 := Nat.mul_div_cancel' (hsplit_dvd n₁ (Finset.mem_coe.mp hn₁))
    have h2 := Nat.mul_div_cancel' (hsplit_dvd n₂ (Finset.mem_coe.mp hn₂))
    have hu := congr_arg Prod.fst heq
    have ha := congr_arg Prod.snd heq
    dsimp [split] at hu ha
    rw [← h1, ← h2, ha, hu]
  have hharm_le : ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ ≤
      (∑ u ∈ U, (u : ℝ)⁻¹) * (∑ a ∈ C, (a : ℝ)⁻¹) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    calc ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹
        = ∑ n ∈ Finset.Icc 1 M, ((split n).1 : ℝ)⁻¹ * ((split n).2 : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hmul := Nat.mul_div_cancel' (hsplit_dvd n hn)
          dsimp [split]
          conv_lhs => rw [← hmul]
          push_cast; rw [mul_inv]
      _ = ∑ y ∈ (Finset.Icc 1 M).image split, (y.1 : ℝ)⁻¹ * (y.2 : ℝ)⁻¹ :=
          (Finset.sum_image (f := fun y : ℕ × ℕ => (y.1 : ℝ)⁻¹ * (y.2 : ℝ)⁻¹) hsplit_inj).symm
      _ ≤ ∑ y ∈ U ×ˢ C, (y.1 : ℝ)⁻¹ * (y.2 : ℝ)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
          exact hsplit_mem n hn
  have hU_le : ∑ u ∈ U, (u : ℝ)⁻¹ ≤ (h : ℝ) / (Nat.totient h : ℝ) := by
    rw [nat_div_totient_eq_prod hh]
    exact sum_inv_smooth_le S (fun _ hp => Nat.prime_of_mem_primeFactors hp) M
  have hlog_le : Real.log ((M : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ :=
    Arith4Ext.SieveCharacters.harmonic_ge_log_succ M
  have hC_nn : 0 ≤ ∑ a ∈ C, (a : ℝ)⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
  have hlog_le2 : Real.log ((M : ℝ) + 1) ≤ ((h : ℝ) / (Nat.totient h : ℝ)) * (∑ a ∈ C, (a : ℝ)⁻¹) :=
    hlog_le.trans (hharm_le.trans (mul_le_mul_of_nonneg_right hU_le hC_nn))
  have hh_pos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have htot_pos : (0 : ℝ) < (Nat.totient h : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hh)
  calc ((Nat.totient h : ℝ) / (h : ℝ)) * Real.log ((M : ℝ) + 1)
      ≤ ((Nat.totient h : ℝ) / (h : ℝ)) *
          (((h : ℝ) / (Nat.totient h : ℝ)) * (∑ a ∈ C, (a : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hlog_le2 (by positivity)
    _ = ∑ a ∈ C, (a : ℝ)⁻¹ := by
        field_simp [hh_pos.ne', htot_pos.ne']

private lemma selbergG_pair_lower_bound {m D : ℕ} (hm : 1 ≤ m) (_hD : 1 ≤ D) :
    (((Nat.totient (2 * m) : ℝ) / (2 * m : ℝ)) * Real.log ((Nat.sqrt D : ℝ) + 1)) ^ 2 ≤
      Arith4Ext.SieveCharacters.selbergG
        (fun d => (polyRootCount (fun x => x * (x + 2 * m)) d : ℝ) / (d : ℝ))
        (Arith4Ext.SieveCharacters.primorial D) D := by
  classical
  set h := 2 * m
  set M₀ := Nat.sqrt D
  set C := (Finset.Icc 1 M₀).filter (fun a => Nat.Coprime a h)
  set P := Arith4Ext.SieveCharacters.primorial D
  set g : ℕ → ℝ := fun d => (polyRootCount (fun x => x * (x + h)) d : ℝ) / (d : ℝ)
  have hh_pos : 0 < h := by omega
  have hP_sq : Squarefree P := Arith4Ext.SieveCharacters.primorial_squarefree D
  have hP_ne : P ≠ 0 := Arith4Ext.SieveCharacters.primorial_ne_zero D
  have hC_ge := coprime_harmonic_lower_bound (h := h) (M := M₀) hh_pos
  have hlhs_nn : 0 ≤ ((Nat.totient h : ℝ) / (h : ℝ)) * Real.log ((M₀ : ℝ) + 1) := by
    have hlog_nn : 0 ≤ Real.log ((M₀ : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₀])
    positivity
  have hsq_le : (((Nat.totient h : ℝ) / (h : ℝ)) * Real.log ((M₀ : ℝ) + 1)) ^ 2 ≤
      (∑ a ∈ C, (a : ℝ)⁻¹) ^ 2 :=
    pow_le_pow_left₀ hlhs_nn hC_ge 2
  have hsq_eq : (∑ a ∈ C, (a : ℝ)⁻¹) ^ 2 =
      ∑ x ∈ C ×ˢ C, (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hmaps : ∀ x ∈ C ×ˢ C,
      Arith4Ext.SieveCharacters.rad (x.1 * x.2) ∈
        (Arith4Ext.SieveCharacters.sieveDivisors P D).filter (fun d => Nat.Coprime d h) := by
    intro x hx
    simp only [Finset.mem_product, C, Finset.mem_filter, Finset.mem_Icc] at hx
    have hx_pos : 0 < x.1 * x.2 := Nat.mul_pos (by omega) (by omega)
    have hrad_le : Arith4Ext.SieveCharacters.rad (x.1 * x.2) ≤ D := by
      calc Arith4Ext.SieveCharacters.rad (x.1 * x.2) ≤ x.1 * x.2 :=
            Arith4Ext.SieveCharacters.rad_le_self hx_pos
        _ ≤ M₀ * M₀ := Nat.mul_le_mul hx.1.1.2 hx.2.1.2
        _ ≤ D := Nat.sqrt_le D
    have hrad_dvd_P : Arith4Ext.SieveCharacters.rad (x.1 * x.2) ∣ P :=
      Arith4Ext.SieveCharacters.squarefree_dvd_primorial
        (Arith4Ext.SieveCharacters.rad_squarefree _) hrad_le
    have hrad_cop : Nat.Coprime (Arith4Ext.SieveCharacters.rad (x.1 * x.2)) h := by
      have hcop12 : Nat.Coprime (x.1 * x.2) h := hx.1.2.mul_left hx.2.2
      exact hcop12.coprime_dvd_left (Arith4Ext.SieveCharacters.rad_dvd_self hx_pos.ne')
    exact Finset.mem_filter.mpr
      ⟨(Arith4Ext.SieveCharacters.mem_sieveDivisors hP_ne).mpr ⟨hrad_dvd_P, hrad_le⟩, hrad_cop⟩
  have hfiber_sum : ∑ x ∈ C ×ˢ C, (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ ≤
      ∑ d ∈ (Arith4Ext.SieveCharacters.sieveDivisors P D).filter (fun d => Nat.Coprime d h),
        (Arith4Ext.SieveCharacters.selbergH g d)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd_mem := Finset.mem_filter.mp hd
    have hd_dvd : d ∣ P := ((Arith4Ext.SieveCharacters.mem_sieveDivisors hP_ne).mp hd_mem.1).1
    have hd_sq : Squarefree d := hP_sq.squarefree_of_dvd hd_dvd
    have hd_cop : Nat.Coprime d h := hd_mem.2
    have hdp_ge3 : ∀ p ∈ d.primeFactors, Nat.Prime p ∧ 3 ≤ p := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_ndvd : ¬ p ∣ h := fun hph => by
        have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
        exact hp_prime.not_dvd_one (hd_cop.gcd_eq_one ▸ Nat.dvd_gcd hpd hph)
      have hp_ne2 : p ≠ 2 := fun h2 => hp_ndvd (h2 ▸ dvd_mul_right 2 m)
      have h2le := hp_prime.two_le
      exact ⟨hp_prime, by omega⟩
    have hH_eq : (Arith4Ext.SieveCharacters.selbergH g d)⁻¹ =
        ∏ p ∈ d.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) := by
      rw [Arith4Ext.SieveCharacters.selbergH_eq_prod_primeFactors (poly_density_isMult (pairPoly_modEq h)) hd_sq,
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_prime := (hdp_ge3 p hp).1
      have hp_3 := (hdp_ge3 p hp).2
      have hp_ndvd : ¬ p ∣ h := fun hph =>
        hp_prime.not_dvd_one (hd_cop.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hph)
      rw [pairPoly_rootCount_prime h p hp_prime, if_neg hp_ndvd]
      have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_3
      push_cast
      field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith]
    rw [hH_eq]
    have hsub : (C ×ˢ C).filter (fun x => Arith4Ext.SieveCharacters.rad (x.1 * x.2) = d) ⊆
        (Finset.Icc 1 M₀ ×ˢ Finset.Icc 1 M₀).filter
          (fun x => (x.1 * x.2).primeFactors = d.primeFactors) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_product, C, Finset.mem_Icc] at hx ⊢
      refine ⟨⟨hx.1.1.1, hx.1.2.1⟩, ?_⟩
      have hx_ne : x.1 * x.2 ≠ 0 := (Nat.mul_pos (by omega) (by omega)).ne'
      rw [← Arith4Ext.SieveCharacters.rad_primeFactors hx_ne, hx.2]
    calc ∑ x ∈ (C ×ˢ C).filter (fun x => Arith4Ext.SieveCharacters.rad (x.1 * x.2) = d),
            (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹
        ≤ ∑ x ∈ (Finset.Icc 1 M₀ ×ˢ Finset.Icc 1 M₀).filter
            (fun x => (x.1 * x.2).primeFactors = d.primeFactors),
            (x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ ∏ p ∈ d.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) :=
          sum_inv_pair_primeFactors_eq_le d.primeFactors hdp_ge3 M₀
  have hG_ge : ∑ d ∈ (Arith4Ext.SieveCharacters.sieveDivisors P D).filter (fun d => Nat.Coprime d h),
        (Arith4Ext.SieveCharacters.selbergH g d)⁻¹ ≤
      Arith4Ext.SieveCharacters.selbergG g P D := by
    unfold Arith4Ext.SieveCharacters.selbergG
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d hd _ => ?_
    have hd_dvd : d ∣ P := ((Arith4Ext.SieveCharacters.mem_sieveDivisors hP_ne).mp hd).1
    have hd_sq : Squarefree d := hP_sq.squarefree_of_dvd hd_dvd
    have h01 : ∀ p ∈ d.primeFactors, 0 < g p ∧ g p < 1 := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      dsimp only [g]
      rw [pairPoly_rootCount_prime h p hp_prime]
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
      split_ifs with hph
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
        exact ⟨by positivity, (div_lt_one hp_pos).mpr (by push_cast; linarith)⟩
      · have hp_ne2 : p ≠ 2 := fun h2 => hph (h2 ▸ dvd_mul_right 2 m)
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by have := hp_prime.two_le; exact_mod_cast (by omega : 3 ≤ p)
        exact ⟨by positivity, (div_lt_one hp_pos).mpr (by push_cast; linarith)⟩
    exact inv_nonneg.mpr (Arith4Ext.SieveCharacters.selbergH_pos
      (poly_density_isMult (pairPoly_modEq h)) hd_sq h01).le
  have hcast_h : (h : ℝ) = (2 * m : ℝ) := by dsimp [h]; push_cast; ring
  rw [hcast_h] at hsq_le
  linarith

private lemma two_le_even_div_totient {m : ℕ} (hm : 1 ≤ m) :
    (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) / (Nat.totient (2 * m) : ℝ) := by
  have hh : 0 < 2 * m := by omega
  rw [nat_div_totient_eq_prod hh]
  have h2mem : 2 ∈ (2 * m).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 m, hh.ne'⟩
  have hsplit := Finset.mul_prod_erase (2 * m).primeFactors (fun p => (p : ℝ) / ((p : ℝ) - 1)) h2mem
  rw [← hsplit]
  have h2val : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
  rw [h2val]
  have hrest : 1 ≤ ∏ p ∈ (2 * m).primeFactors.erase 2, (p : ℝ) / ((p : ℝ) - 1) := by
    have hge1 : ∀ p ∈ (2 * m).primeFactors.erase 2, (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
      rw [one_le_div (by linarith)]
      linarith
    have hgen : ∀ S : Finset ℕ, (∀ p ∈ S, (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1)) →
        (1 : ℝ) ≤ ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
      intro S
      classical
      induction S using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s ha ih =>
        intro hs
        rw [Finset.prod_insert ha]
        have h1 := hs a (Finset.mem_insert_self a s)
        have h2 := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
        nlinarith
    exact hgen _ hge1
  linarith

/-- **Unconditional Dimension-2 Brun–Selberg Prime-Pair Upper Bound (All `M`, All `N ≥ 2`, All `m ≥ 1`)**:
For every interval `(M, M + N]` (`N ≥ 2`) and every even shift `2m ≥ 2`,
`#{p ∈ (M, M + N] : Prime(p) ∧ Prime(p + 2m)} ≤ 450 · (2m / φ(2m))² · N / (log N)²`. -/
theorem ppl087_selberg_even_shift_prime_pair_upper_bound (M N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (((Finset.Icc (M + 1) (M + N)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card : ℝ) ≤
      450 * (((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hrat_ge2 : (2 : ℝ) ≤ (2 * m : ℝ) / (Nat.totient (2 * m) : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_ofNat] using two_le_even_div_totient hm
  have hrat_sq_ge4 : (4 : ℝ) ≤ ((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2 := by nlinarith
  by_cases hN1024 : N < 1024
  · have hcard_le : (((Finset.Icc (M + 1) (M + N)).filter
        (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card : ℝ) ≤ (N : ℝ) := by
      have h1 : ((Finset.Icc (M + 1) (M + N)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card ≤ (Finset.Icc (M + 1) (M + N)).card :=
        Finset.card_filter_le _ _
      have h2 : (Finset.Icc (M + 1) (M + N)).card = N := by simp
      rw [h2] at h1
      exact_mod_cast h1
    have hlog2_lt1 : Real.log 2 < 1 := by
      have h2e : (2 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
      calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2e
        _ = 1 := Real.log_exp 1
    have hlogN_lt10 : Real.log (N : ℝ) < 10 := by
      have hN_lt : (N : ℝ) < (2 : ℝ) ^ 10 := by
        have : N < 2 ^ 10 := by omega
        exact_mod_cast this
      calc Real.log (N : ℝ) < Real.log ((2 : ℝ) ^ 10) := Real.log_lt_log hN_pos hN_lt
        _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ < 10 := by linarith
    have hlogN_sq_le : (Real.log (N : ℝ)) ^ 2 ≤ 100 := by nlinarith
    have hN_le_rhs : (N : ℝ) ≤ 100 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (pow_pos hlogN_pos 2)]
      nlinarith
    have hdiv_nn : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by positivity
    calc (((Finset.Icc (M + 1) (M + N)).filter
            (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card : ℝ)
        ≤ (N : ℝ) := hcard_le
      _ ≤ 100 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := hN_le_rhs
      _ ≤ 450 * (((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2) *
            ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by nlinarith
  · push Not at hN1024
    set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 5)
    have hx_pos : 0 < x := Real.rpow_pos_of_pos hN_pos _
    have hx5 : x ^ 5 = (N : ℝ) := by
      dsimp [x]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
    have hx_ge4 : 4 ≤ x := by
      have h45 : (4 : ℝ) ^ 5 ≤ x ^ 5 := by
        rw [hx5]; norm_num; exact_mod_cast hN1024
      by_contra hlt; push Not at hlt
      have : x ^ 5 < (4 : ℝ) ^ 5 := pow_lt_pow_left₀ hlt hx_pos.le (by norm_num)
      linarith
    set D : ℕ := Nat.floor x
    have hD_ge4 : 4 ≤ D := Nat.le_floor hx_ge4
    have hD_ge1 : 1 ≤ D := by omega
    have hD_le : (D : ℝ) ≤ x := Nat.floor_le hx_pos.le
    have hx_lt_D1 : x < (D : ℝ) + 1 := Nat.lt_floor_add_one x
    set M₀ := Nat.sqrt D
    have hM0_sq : D < (M₀ + 1) ^ 2 := by
      simpa [sq] using Nat.lt_succ_sqrt D
    have hM0_pow20 : (N : ℝ) < ((M₀ : ℝ) + 1) ^ 20 := by
      have hD_gt_sqrt : Real.sqrt x < (D : ℝ) := by
        have h1 : (3 : ℝ) / 4 * x < (D : ℝ) := by linarith
        have h2 : Real.sqrt x ≤ (3 : ℝ) / 4 * x := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
        linarith
      have hM0_gt_sqrt : Real.sqrt x < ((M₀ : ℝ) + 1) ^ 2 := by
        have hcast : (D : ℝ) < ((M₀ : ℝ) + 1) ^ 2 := by exact_mod_cast hM0_sq
        linarith
      have h4 : x < ((M₀ : ℝ) + 1) ^ 4 := by
        have hsq := pow_lt_pow_left₀ hM0_gt_sqrt (Real.sqrt_nonneg x) (by norm_num : 2 ≠ 0)
        rw [Real.sq_sqrt hx_pos.le] at hsq
        simpa [← pow_mul] using hsq
      have h20 := pow_lt_pow_left₀ h4 hx_pos.le (by norm_num : 5 ≠ 0)
      rw [hx5] at h20
      simpa [← pow_mul] using h20
    have hlog_M0 : Real.log (N : ℝ) / 20 ≤ Real.log ((M₀ : ℝ) + 1) := by
      have hlog := Real.log_lt_log hN_pos hM0_pow20
      rw [Real.log_pow] at hlog
      push_cast at hlog
      linarith
    have hIcc_eq : Finset.Icc (M + 1) (M + N) = Finset.Ico (M + 1) (M + 1 + N) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    set F : ℕ → ℕ := fun p => p * (p + 2 * m)
    have hFinj : Set.InjOn F (Finset.Ico (M + 1) (M + 1 + N) : Set ℕ) := by
      intro p₁ _ p₂ _ heq
      dsimp only [F] at heq
      rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
      · have : p₁ * (p₁ + 2 * m) < p₂ * (p₂ + 2 * m) := by nlinarith
        omega
      · rfl
      · have : p₂ * (p₂ + 2 * m) < p₁ * (p₁ + 2 * m) := by nlinarith
        omega
    have h01 : ∀ p ∈ (Arith4Ext.SieveCharacters.primorial D).primeFactors,
        0 < (polyRootCount F p : ℝ) / (p : ℝ) ∧ (polyRootCount F p : ℝ) / (p : ℝ) < 1 := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      dsimp only [F]
      rw [pairPoly_rootCount_prime (2 * m) p hp_prime]
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
      split_ifs with hph
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
        exact ⟨by positivity, (div_lt_one hp_pos).mpr (by push_cast; linarith)⟩
      · have hp_ne2 : p ≠ 2 := fun h2 => hph (h2 ▸ dvd_mul_right 2 m)
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by have := hp_prime.two_le; exact_mod_cast (by omega : 3 ≤ p)
        exact ⟨by positivity, (div_lt_one hp_pos).mpr (by push_cast; linarith)⟩
    have hsub : (Finset.Icc (M + 1) (M + N)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m)) ⊆
        Finset.Icc 1 D ∪
          (Finset.Ico (M + 1) (M + 1 + N)).filter
            (fun p => Nat.Coprime (F p) (Arith4Ext.SieveCharacters.primorial D)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      by_cases hle : p ≤ D
      · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hp.2.1.one_le, hle⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hp.1.1, by omega⟩, ?_⟩)
        dsimp only [F]
        refine Nat.Coprime.mul_left ?_ ?_
        · rw [hp.2.1.coprime_iff_not_dvd, Arith4Ext.SieveCharacters.prime_dvd_primorial_iff hp.2.1]
          exact hle
        · rw [hp.2.2.coprime_iff_not_dvd, Arith4Ext.SieveCharacters.prime_dvd_primorial_iff hp.2.2]
          omega
    have hcard_split : (((Finset.Icc (M + 1) (M + N)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card : ℝ) ≤
        (D : ℝ) + (((Finset.Ico (M + 1) (M + 1 + N)).filter
          (fun p => Nat.Coprime (F p) (Arith4Ext.SieveCharacters.primorial D))).card : ℝ) := by
      have h1 : ((Finset.Icc (M + 1) (M + N)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card ≤
          D + ((Finset.Ico (M + 1) (M + 1 + N)).filter
            (fun p => Nat.Coprime (F p) (Arith4Ext.SieveCharacters.primorial D))).card := by
        calc _ ≤ (Finset.Icc 1 D ∪ (Finset.Ico (M + 1) (M + 1 + N)).filter
                (fun p => Nat.Coprime (F p) (Arith4Ext.SieveCharacters.primorial D))).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.Icc 1 D).card + _ := Finset.card_union_le _ _
          _ = D + _ := by simp
      exact_mod_cast h1
    have hsel := poly_selberg_sieve_Ico (pairPoly_modEq (2 * m)) hFinj hD_ge1 h01
    have hG_lb := selbergG_pair_lower_bound hm hD_ge1
    have htot_pos : (0 : ℝ) < (Nat.totient (2 * m) : ℝ) := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < 2 * m))
    have h2m_pos : (0 : ℝ) < (2 * m : ℝ) := by positivity
    have hG_lb2 : (((Nat.totient (2 * m) : ℝ) / (2 * m : ℝ)) * (Real.log (N : ℝ) / 20)) ^ 2 ≤
        Arith4Ext.SieveCharacters.selbergG
          (fun d => (polyRootCount F d : ℝ) / (d : ℝ))
          (Arith4Ext.SieveCharacters.primorial D) D := by
      have h1 : (((Nat.totient (2 * m) : ℝ) / (2 * m : ℝ)) * (Real.log (N : ℝ) / 20)) ^ 2 ≤
          (((Nat.totient (2 * m) : ℝ) / (2 * m : ℝ)) * Real.log ((M₀ : ℝ) + 1)) ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        exact mul_le_mul_of_nonneg_left hlog_M0 (by positivity)
      exact h1.trans hG_lb
    have hmain_le : (N : ℝ) / Arith4Ext.SieveCharacters.selbergG
          (fun d => (polyRootCount F d : ℝ) / (d : ℝ))
          (Arith4Ext.SieveCharacters.primorial D) D ≤
        400 * (((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      have hden_pos : 0 < (((Nat.totient (2 * m) : ℝ) / (2 * m : ℝ)) * (Real.log (N : ℝ) / 20)) ^ 2 := by
        positivity
      calc (N : ℝ) / Arith4Ext.SieveCharacters.selbergG
              (fun d => (polyRootCount F d : ℝ) / (d : ℝ))
              (Arith4Ext.SieveCharacters.primorial D) D
          ≤ (N : ℝ) / (((Nat.totient (2 * m) : ℝ) / (2 * m : ℝ)) * (Real.log (N : ℝ) / 20)) ^ 2 :=
            div_le_div_of_nonneg_left hN_pos.le hden_pos hG_lb2
        _ = 400 * (((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2) *
              ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
            field_simp [htot_pos.ne', h2m_pos.ne', hlogN_pos.ne']
            ring
    have hlogN_le_10sqrt : Real.log (N : ℝ) ≤ 10 * Real.sqrt x := by
      have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx_pos)
      have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow hx_pos]; ring
      have h3 : Real.log (N : ℝ) = 5 * Real.log x := by
        rw [← hx5, Real.log_pow]; norm_num
      linarith
    have hlogN_sq_le : (Real.log (N : ℝ)) ^ 2 ≤ 100 * x := by
      calc (Real.log (N : ℝ)) ^ 2 ≤ (10 * Real.sqrt x) ^ 2 :=
            pow_le_pow_left₀ hlogN_pos.le hlogN_le_10sqrt 2
        _ = 100 * (Real.sqrt x) ^ 2 := by ring
        _ = 100 * x := by rw [Real.sq_sqrt hx_pos.le]
    have herr_le : (D : ℝ) + (D : ℝ) ^ 4 ≤
        50 * (((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      have hD_le_D4 : (D : ℝ) ≤ (D : ℝ) ^ 4 := by
        have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge1
        have h2 : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
        have h4 : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 4 := by nlinarith
        linarith
      have hD4_le_x4 : (D : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg D) hD_le 4
      have h2x4 : 2 * x ^ 4 ≤ 200 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (pow_pos hlogN_pos 2)]
        calc 2 * x ^ 4 * (Real.log (N : ℝ)) ^ 2
            ≤ 2 * x ^ 4 * (100 * x) :=
              mul_le_mul_of_nonneg_left hlogN_sq_le (by positivity)
          _ = 200 * x ^ 5 := by ring
          _ = 200 * (N : ℝ) := by rw [hx5]
      have hdiv_nn : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by positivity
      calc (D : ℝ) + (D : ℝ) ^ 4 ≤ 2 * x ^ 4 := by linarith
        _ ≤ 200 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := h2x4
        _ ≤ 50 * (((2 * m : ℝ) / (Nat.totient (2 * m) : ℝ)) ^ 2) *
              ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by nlinarith
    linarith

/-! ### Section 3C: Fixed-Witness Sparsity, Totient Fourth Moment, & Sharp-Order Cumulative Bound -/

/-- **Fixed-Witness Sparsity Theorem**: For every fixed witness `k ≥ 2` and every `X ≥ 2`,
the number of `n ∈ [k + 1, X]` for which both `n + k` and `n + k²` are prime satisfies
`#{n ∈ [k + 1, X] : Prime(n + k) ∧ Prime(n + k²)} ≤ 450 (k(k-1) / φ(k(k-1)))² X / (log X)²`. -/
theorem ppl087_fixed_witness_upper_bound {k X : ℕ} (hk : 2 ≤ k) (hX : 2 ≤ X) :
    (((Finset.Icc (k + 1) X).filter (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) ≤
      450 * ((((k * (k - 1) : ℕ) : ℝ) / (Nat.totient (k * (k - 1)) : ℝ)) ^ 2) *
        ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := by
  have heven : 2 ∣ k * (k - 1) := by
    cases k with
    | zero => omega
    | succ r =>
      simp only [Nat.add_sub_cancel]
      rcases Nat.even_or_odd r with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(t + t + 1) * t, by ring⟩
      · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
  rcases heven with ⟨m, hm_eq⟩
  have hm1 : 1 ≤ m := by
    have hpos : 2 ≤ k * (k - 1) := by
      have : 1 ≤ k - 1 := by omega
      nlinarith
    omega
  have hbt := ppl087_selberg_even_shift_prime_pair_upper_bound k X m hX hm1
  have hcard : ((Finset.Icc (k + 1) X).filter (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card ≤
      ((Finset.Icc (k + 1) (k + X)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m))).card := by
    have himg : ((Finset.Icc (k + 1) X).filter
        (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).image (fun n => n + k) ⊆
        (Finset.Icc (k + 1) (k + X)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2 * m)) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      refine ⟨⟨by omega, by omega⟩, hn.2.1, ?_⟩
      have hsq : n + k + 2 * m = n + k ^ 2 := by
        rw [← hm_eq]
        have hmul : k * (k - 1) + k = k ^ 2 := by
          cases k with
          | zero => omega
          | succ r => simp only [Nat.add_sub_cancel]; ring
        omega
      rw [hsq]
      exact hn.2.2
    calc ((Finset.Icc (k + 1) X).filter (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card
        = (((Finset.Icc (k + 1) X).filter
            (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).image (fun n => n + k)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => by omega)).symm
      _ ≤ _ := Finset.card_le_card himg
  have hcast_eq : ((k * (k - 1) : ℕ) : ℝ) = (2 * m : ℝ) := by
    rw [hm_eq]; push_cast; ring
  rw [hcast_eq, hm_eq]
  exact (by exact_mod_cast hcard : _ ≤ _).trans hbt

private lemma prod_one_add_eq_sum_squarefree_divisors (f : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∏ p ∈ k.primeFactors, (1 + f p) =
      ∑ d ∈ k.divisors.filter Squarefree, ∏ p ∈ d.primeFactors, f p := by
  classical
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p) ?_ ?_ ?_ ?_
  · intro S hS
    have hS_sub : S ⊆ k.primeFactors := Finset.mem_powerset.mp hS
    have hS_primes : ∀ p ∈ S, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hS_sub hp)
    have hsq : Squarefree (∏ p ∈ S, p) := Arith4Ext.SieveCharacters.squarefree_prod_primes S hS_primes
    have hdvd : (∏ p ∈ S, p) ∣ k := by
      have hrad : (∏ p ∈ S, p) ∣ Arith4Ext.SieveCharacters.rad k :=
        Finset.prod_dvd_prod_of_subset _ _ _ hS_sub
      exact hrad.trans (Arith4Ext.SieveCharacters.rad_dvd_self (by omega))
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, by omega⟩, hsq⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    have h1 : ∀ p ∈ S₁, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS₁ hp)
    have h2 : ∀ p ∈ S₂, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS₂ hp)
    ext p
    constructor
    · intro hp
      have hp_prime := h1 p hp
      have hpd : p ∣ ∏ q ∈ S₂, q := heq ▸ Finset.dvd_prod_of_mem _ hp
      rcases (hp_prime.prime.dvd_finsetProd_iff _).mp hpd with ⟨q, hq, hpq⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hp_prime (h2 q hq)).mp hpq]
    · intro hp
      have hp_prime := h2 p hp
      have hpd : p ∣ ∏ q ∈ S₁, q := heq.symm ▸ Finset.dvd_prod_of_mem _ hp
      rcases (hp_prime.prime.dvd_finsetProd_iff _).mp hpd with ⟨q, hq, hpq⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hp_prime (h1 q hq)).mp hpq]
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr
      (Nat.primeFactors_mono hd.1.1 hd.1.2),
      (Arith4Ext.SieveCharacters.squarefree_eq_prod_primeFactors hd.2).symm⟩
  · intro S hS
    have hS_primes : ∀ p ∈ S, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
    have hpf : (∏ p ∈ S, p).primeFactors = S := by
      ext p
      rw [Nat.mem_primeFactors]
      have hpos : ∏ q ∈ S, q ≠ 0 := (Finset.prod_pos fun q hq => (hS_primes q hq).pos).ne'
      constructor
      · rintro ⟨hp_prime, hpd, _⟩
        rcases (hp_prime.prime.dvd_finsetProd_iff _).mp hpd with ⟨q, hq, hpq⟩
        rwa [(Nat.prime_dvd_prime_iff_eq hp_prime (hS_primes q hq)).mp hpq]
      · intro hp
        exact ⟨hS_primes p hp, Finset.dvd_prod_of_mem _ hp, hpos⟩
    rw [hpf]

private lemma sum_inv_sq_Icc2_le (X : ℕ) :
    ∑ m ∈ Finset.Icc 2 X, (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 1 := by
  have hterm : ∀ m ∈ Finset.Icc 2 X,
      (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - 1)
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm1_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
    rw [div_le_iff₀ (pow_pos hm_pos 2)]
    field_simp [hm1_pos.ne', hm_pos.ne']
    rw [hm1_cast]
    nlinarith
  have htel : ∀ M : ℕ, 1 ≤ M →
      ∑ m ∈ Finset.Icc 2 M, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) = 1 - 1 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      have hIcc : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot : M + 1 ∉ Finset.Icc 2 M := by simp
      rw [hIcc, Finset.sum_insert hnot, ih]
      simp only [Nat.add_sub_cancel]
      ring
  by_cases hX1 : 1 ≤ X
  · calc ∑ m ∈ Finset.Icc 2 X, (1 : ℝ) / ((m : ℝ) ^ 2)
        ≤ ∑ m ∈ Finset.Icc 2 X, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 1 - 1 / (X : ℝ) := htel X hX1
      _ ≤ 1 := by linarith [show (0 : ℝ) ≤ 1 / (X : ℝ) by positivity]
  · have hX0 : X = 0 := by omega
    simp [hX0]

/-- **Fourth-Moment Euler Totient Linear Upper Bound**:
For every `X : ℕ`, `∑_{k = 1}^X (k / φ(k))⁴ ≤ exp(64) · X`. -/
theorem ppl087_totient_fourth_moment_linear_bound (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, ((k : ℝ) / (Nat.totient k : ℝ)) ^ 4 ≤ Real.exp 64 * (X : ℝ) := by
  classical
  set f : ℕ → ℝ := fun p => ((p : ℝ) / ((p : ℝ) - 1)) ^ 4 - 1
  have hf_nn : ∀ p : ℕ, Nat.Prime p → 0 ≤ f p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have h1 : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := (one_le_div (by linarith)).mpr (by linarith)
    have h4 : (1 : ℝ) ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 4 := one_le_pow₀ h1
    dsimp [f]; linarith
  have hf_le : ∀ p : ℕ, Nat.Prime p → f p / (p : ℝ) ≤ 64 / ((p : ℝ) ^ 2) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hpow4 : ((p : ℝ) / 2) ^ 4 ≤ ((p : ℝ) - 1) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hhalf 4
    have hnum : (p : ℝ) ^ 4 - ((p : ℝ) - 1) ^ 4 ≤ 4 * (p : ℝ) ^ 3 := by
      have h1 : (p : ℝ) ^ 4 - ((p : ℝ) - 1) ^ 4 =
          4 * (p : ℝ) ^ 3 - 6 * (p : ℝ) ^ 2 + 4 * (p : ℝ) - 1 := by ring
      nlinarith
    have hfeq : f p = ((p : ℝ) ^ 4 - ((p : ℝ) - 1) ^ 4) / ((p : ℝ) - 1) ^ 4 := by
      dsimp [f]; rw [div_pow]; field_simp [hp1_pos.ne']
    rw [hfeq, div_div, div_le_div_iff₀ (mul_pos (pow_pos hp1_pos 4) hp_pos) (pow_pos hp_pos 2)]
    have h16 : (p : ℝ) ^ 4 ≤ 16 * ((p : ℝ) - 1) ^ 4 := by linarith [show ((p : ℝ) / 2) ^ 4 = (p : ℝ) ^ 4 / 16 by ring]
    have hmul1 : ((p : ℝ) ^ 4 - ((p : ℝ) - 1) ^ 4) * (p : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 5 := by
      nlinarith
    have hmul2 : 4 * (p : ℝ) ^ 5 ≤ 64 * (((p : ℝ) - 1) ^ 4 * (p : ℝ)) := by
      have : 4 * (p : ℝ) ^ 5 = 4 * (p : ℝ) * (p : ℝ) ^ 4 := by ring
      nlinarith
    linarith
  have hterm_eq : ∀ k ∈ Finset.Icc 1 X,
      ((k : ℝ) / (Nat.totient k : ℝ)) ^ 4 =
        ∑ d ∈ k.divisors.filter Squarefree, ∏ p ∈ d.primeFactors, f p := by
    intro k hk
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    rw [nat_div_totient_eq_prod hk_pos, ← Finset.prod_pow]
    have h1 : ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 4 =
        ∏ p ∈ k.primeFactors, (1 + f p) := by
      refine Finset.prod_congr rfl fun p _ => by dsimp [f]; ring
    rw [h1, prod_one_add_eq_sum_squarefree_divisors f hk_pos]
  rw [Finset.sum_congr rfl hterm_eq]
  set Dset := (Finset.Icc 1 X).filter Squarefree
  have hswap : ∑ k ∈ Finset.Icc 1 X, ∑ d ∈ k.divisors.filter Squarefree, ∏ p ∈ d.primeFactors, f p =
      ∑ d ∈ Dset, (((Finset.Icc 1 X).filter (d ∣ ·)).card : ℝ) * ∏ p ∈ d.primeFactors, f p := by
    have hinner : ∀ k ∈ Finset.Icc 1 X,
        ∑ d ∈ k.divisors.filter Squarefree, ∏ p ∈ d.primeFactors, f p =
          ∑ d ∈ Dset, if d ∣ k then ∏ p ∈ d.primeFactors, f p else 0 := by
      intro k hk
      have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
      have hk_le : k ≤ X := (Finset.mem_Icc.mp hk).2
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Dset, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdk, _⟩, hsq⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdk hk_pos, (Nat.le_of_dvd hk_pos hdk).trans hk_le⟩, hsq⟩, hdk⟩
      · rintro ⟨⟨_, hsq⟩, hdk⟩
        exact ⟨⟨hdk, hk_pos.ne'⟩, hsq⟩
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  have hmult_le : ∀ d ∈ Dset, (((Finset.Icc 1 X).filter (d ∣ ·)).card : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
    intro d hd
    have hd_pos : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hcard := Arith4Ext.SieveCharacters.card_multiples_Icc_eq 0 X d hd_pos
    simp only [zero_add, Nat.zero_div, Nat.sub_zero] at hcard
    rw [hcard]
    exact Nat.cast_div_le
  have hsum_le : ∑ d ∈ Dset, (((Finset.Icc 1 X).filter (d ∣ ·)).card : ℝ) * ∏ p ∈ d.primeFactors, f p ≤
      (X : ℝ) * ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (f p / (p : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2
    have hprod_nn : 0 ≤ ∏ p ∈ d.primeFactors, f p :=
      Finset.prod_nonneg fun p hp => hf_nn p (Nat.prime_of_mem_primeFactors hp)
    have h1 := mul_le_mul_of_nonneg_right (hmult_le d hd) hprod_nn
    have hd_eq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      conv_lhs => rw [Arith4Ext.SieveCharacters.squarefree_eq_prod_primeFactors hd_sq]
      rw [Nat.cast_prod]
    have hrew : (X : ℝ) / (d : ℝ) * ∏ p ∈ d.primeFactors, f p =
        (X : ℝ) * ∏ p ∈ d.primeFactors, (f p / (p : ℝ)) := by
      rw [Finset.prod_div_distrib, ← hd_eq]; ring
    linarith
  set Pset := (Finset.Icc 1 X).filter Nat.Prime
  have hD_le_prod : ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (f p / (p : ℝ)) ≤
      ∏ p ∈ Pset, (1 + f p / (p : ℝ)) := by
    rw [Finset.prod_one_add]
    have hinj : Set.InjOn Nat.primeFactors ↑Dset := by
      intro d₁ hd₁ d₂ hd₂ heq
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hd₁)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hd₂)).2
      rw [Arith4Ext.SieveCharacters.squarefree_eq_prod_primeFactors h1,
        Arith4Ext.SieveCharacters.squarefree_eq_prod_primeFactors h2, heq]
    have himg_sub : Dset.image Nat.primeFactors ⊆ Pset.powerset := by
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨d, hd, rfl⟩
      rw [Finset.mem_powerset]
      intro p hp
      have hd_mem := Finset.mem_filter.mp hd
      have hd_pos : 0 < d := (Finset.mem_Icc.mp hd_mem.1).1
      have hd_le : d ≤ X := (Finset.mem_Icc.mp hd_mem.1).2
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_le, (Nat.le_of_dvd hd_pos (Nat.dvd_of_mem_primeFactors hp)).trans hd_le⟩,
         hp_prime⟩
    calc ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (f p / (p : ℝ))
        = ∑ S ∈ Dset.image Nat.primeFactors, ∏ p ∈ S, (f p / (p : ℝ)) :=
          (Finset.sum_image (f := fun S => ∏ p ∈ S, (f p / (p : ℝ))) hinj).symm
      _ ≤ ∑ S ∈ Pset.powerset, ∏ p ∈ S, (f p / (p : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun S hS _ => ?_
          refine Finset.prod_nonneg fun p hp => ?_
          have hp_prime := (Finset.mem_filter.mp (Finset.mem_powerset.mp hS hp)).2
          exact div_nonneg (hf_nn p hp_prime) (Nat.cast_nonneg p)
  have hprod_le_exp : ∏ p ∈ Pset, (1 + f p / (p : ℝ)) ≤ Real.exp 64 := by
    calc ∏ p ∈ Pset, (1 + f p / (p : ℝ))
        ≤ ∏ p ∈ Pset, Real.exp (f p / (p : ℝ)) := by
          refine Finset.prod_le_prod ?_ fun p hp => ?_
          · intro p hp
            have hp_prime := (Finset.mem_filter.mp hp).2
            linarith [div_nonneg (hf_nn p hp_prime) (Nat.cast_nonneg p)]
          · linarith [Real.add_one_le_exp (f p / (p : ℝ))]
      _ = Real.exp (∑ p ∈ Pset, f p / (p : ℝ)) := (Real.exp_sum Pset _).symm
      _ ≤ Real.exp 64 := by
          apply Real.exp_le_exp.mpr
          calc ∑ p ∈ Pset, f p / (p : ℝ)
              ≤ ∑ p ∈ Pset, 64 / ((p : ℝ) ^ 2) :=
                Finset.sum_le_sum fun p hp => hf_le p (Finset.mem_filter.mp hp).2
            _ ≤ ∑ m ∈ Finset.Icc 2 X, 64 / ((m : ℝ) ^ 2) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
                intro p hp
                simp only [Pset, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
                exact ⟨hp.2.two_le, hp.1.2⟩
            _ = 64 * ∑ m ∈ Finset.Icc 2 X, (1 : ℝ) / ((m : ℝ) ^ 2) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
            _ ≤ 64 * 1 := mul_le_mul_of_nonneg_left (sum_inv_sq_Icc2_le X) (by norm_num)
            _ = 64 := mul_one 64
  calc ∑ d ∈ Dset, (((Finset.Icc 1 X).filter (d ∣ ·)).card : ℝ) * ∏ p ∈ d.primeFactors, f p
      ≤ (X : ℝ) * ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (f p / (p : ℝ)) := hsum_le
    _ ≤ (X : ℝ) * ∏ p ∈ Pset, (1 + f p / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hD_le_prod (Nat.cast_nonneg X)
    _ ≤ (X : ℝ) * Real.exp 64 :=
        mul_le_mul_of_nonneg_left hprod_le_exp (Nat.cast_nonneg X)
    _ = Real.exp 64 * (X : ℝ) := mul_comm _ _

/-- **Sharp-Order Cumulative Pair-Count Upper Bound**:
For every `X ≥ 2`, the cumulative count of PPL 087 simultaneous prime pairs
`∑_{n = 2}^X S(n) = ∑_{n = 2}^X #{0 ≤ k < n : Prime(n + k) ∧ Prime(n + k²)}`
satisfies the sharp-order bound `∑_{n = 2}^X S(n) ≤ (450 exp(64) + 20) · X² / (log X)²`. -/
theorem ppl087_cumulative_pair_count_upper_bound {X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 2 X,
      (((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ)) ≤
      (450 * Real.exp 64 + 20) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlogX_le_X : Real.log (X : ℝ) ≤ (X : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hX_pos]
  -- Swap the double sum over `(n, k)` with `2 ≤ n ≤ X` and `0 ≤ k < n`
  have hswap :
      (∑ n ∈ Finset.Icc 2 X,
        (((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ)) =
      (((Finset.Icc 2 X).filter Nat.Prime).card : ℝ) +
      (((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).card : ℝ) +
      ∑ k ∈ Finset.Icc 2 (X - 1),
        (((Finset.Icc (k + 1) X).filter
          (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) := by
    have hsplit_n : ∀ n ∈ Finset.Icc 2 X,
        (((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) =
        (if Nat.Prime n then (1 : ℝ) else 0) +
        (if Nat.Prime (n + 1) then (1 : ℝ) else 0) +
        ∑ k ∈ Finset.Icc 2 (X - 1),
          if k < n ∧ Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2) then (1 : ℝ) else 0 := by
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hcard_sum :
          (((Finset.range n).filter (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) =
          ∑ k ∈ Finset.range n, if Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2) then (1 : ℝ) else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hcard_sum]
      have hrange : Finset.range n = insert 0 (insert 1 (Finset.Icc 2 (n - 1))) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      have h0not : 0 ∉ insert 1 (Finset.Icc 2 (n - 1)) := by simp
      have h1not : 1 ∉ Finset.Icc 2 (n - 1) := by simp
      rw [hrange, Finset.sum_insert h0not, Finset.sum_insert h1not]
      simp only [add_zero, zero_pow (by norm_num : 2 ≠ 0), one_pow, and_self]
      have htail :
          (∑ k ∈ Finset.Icc 2 (n - 1),
            if Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2) then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.Icc 2 (X - 1),
            if k < n ∧ Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2) then (1 : ℝ) else 0 := by
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hk2, hkn⟩, hpr⟩
          exact ⟨⟨hk2, by omega⟩, by omega, hpr⟩
        · rintro ⟨⟨hk2, _⟩, hkn, hpr⟩
          exact ⟨⟨hk2, by omega⟩, hpr⟩
      rw [htail, add_assoc]
    rw [Finset.sum_congr rfl hsplit_n, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h0_eq : (∑ n ∈ Finset.Icc 2 X, if Nat.Prime n then (1 : ℝ) else 0) =
        (((Finset.Icc 2 X).filter Nat.Prime).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1_eq : (∑ n ∈ Finset.Icc 2 X, if Nat.Prime (n + 1) then (1 : ℝ) else 0) =
        (((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2_eq : (∑ n ∈ Finset.Icc 2 X, ∑ k ∈ Finset.Icc 2 (X - 1),
          if k < n ∧ Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2) then (1 : ℝ) else 0) =
        ∑ k ∈ Finset.Icc 2 (X - 1),
          (((Finset.Icc (k + 1) X).filter
            (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hnX⟩, hkn, hpr⟩
        exact ⟨⟨by omega, hnX⟩, hpr⟩
      · rintro ⟨⟨hkn, hnX⟩, hpr⟩
        exact ⟨⟨by omega, hnX⟩, by omega, hpr⟩
    rw [h0_eq, h1_eq, h2_eq]
  rw [hswap]
  -- Bound the `k = 0` and `k = 1` terms by `20 * X^2 / (log X)^2`
  have hk0_le : (((Finset.Icc 2 X).filter Nat.Prime).card : ℝ) ≤ 9 * (X : ℝ) / Real.log (X : ℝ) := by
    have hbt := Arith4Ext.SieveCharacters.brun_titchmarsh_interval 0 X hX
    have hsub : (Finset.Icc 2 X).filter Nat.Prime ⊆ (Finset.Icc (0 + 1) (0 + X)).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨by omega, by omega⟩, hp.2⟩
    exact (by exact_mod_cast Finset.card_le_card hsub : _ ≤ _).trans hbt
  have hk1_le : (((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).card : ℝ) ≤
      9 * (X : ℝ) / Real.log (X : ℝ) := by
    have hbt := Arith4Ext.SieveCharacters.brun_titchmarsh_interval 1 X hX
    have hcard : ((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).card ≤
        ((Finset.Icc (1 + 1) (1 + X)).filter Nat.Prime).card := by
      have himg : ((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).image (· + 1) ⊆
          (Finset.Icc (1 + 1) (1 + X)).filter Nat.Prime := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        exact ⟨⟨by omega, by omega⟩, hn.2⟩
      calc ((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).card
          = (((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).image (· + 1)).card :=
            (Finset.card_image_of_injective _ (fun _ _ h => by omega)).symm
        _ ≤ _ := Finset.card_le_card himg
    exact (by exact_mod_cast hcard : _ ≤ _).trans hbt
  have hx_div_log_le : (X : ℝ) / Real.log (X : ℝ) ≤ (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
    rw [div_le_div_iff₀ hlogX_pos (pow_pos hlogX_pos 2)]
    have hprod_pos : 0 < (X : ℝ) * Real.log (X : ℝ) := mul_pos hX_pos hlogX_pos
    nlinarith
  have hk01_le : (((Finset.Icc 2 X).filter Nat.Prime).card : ℝ) +
      (((Finset.Icc 2 X).filter (fun n => Nat.Prime (n + 1))).card : ℝ) ≤
      20 * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
    have h1 : 9 * (X : ℝ) / Real.log (X : ℝ) = 9 * ((X : ℝ) / Real.log (X : ℝ)) := by ring
    linarith
  -- Bound the `k ≥ 2` sum via fixed-witness sparsity + AM-GM + totient 4th moment
  have hkge2_le :
      ∑ k ∈ Finset.Icc 2 (X - 1),
        (((Finset.Icc (k + 1) X).filter
          (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) ≤
      (450 * Real.exp 64) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
    have hstep1 :
        ∑ k ∈ Finset.Icc 2 (X - 1),
          (((Finset.Icc (k + 1) X).filter
            (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ) ≤
        450 * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) *
          ∑ k ∈ Finset.Icc 2 (X - 1),
            (((k * (k - 1) : ℕ) : ℝ) / (Nat.totient (k * (k - 1)) : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hfw := ppl087_fixed_witness_upper_bound hk2 hX
      linarith
    have htot_sum :
        ∑ k ∈ Finset.Icc 2 (X - 1),
          (((k * (k - 1) : ℕ) : ℝ) / (Nat.totient (k * (k - 1)) : ℝ)) ^ 2 ≤
        ∑ j ∈ Finset.Icc 1 X, ((j : ℝ) / (Nat.totient j : ℝ)) ^ 4 := by
      have hterm : ∀ k ∈ Finset.Icc 2 (X - 1),
          (((k * (k - 1) : ℕ) : ℝ) / (Nat.totient (k * (k - 1)) : ℝ)) ^ 2 ≤
          ((k : ℝ) / (Nat.totient k : ℝ)) ^ 4 / 2 +
            (((k - 1 : ℕ) : ℝ) / (Nat.totient (k - 1) : ℝ)) ^ 4 / 2 := by
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hcop : Nat.Coprime k (k - 1) := by
          cases k with
          | zero => omega
          | succ r => simp [Nat.coprime_self_add_left]
        rw [Nat.totient_mul hcop]
        push_cast
        set a := (k : ℝ) / (Nat.totient k : ℝ)
        set b := ((k - 1 : ℕ) : ℝ) / (Nat.totient (k - 1) : ℝ)
        have heq : ((k : ℝ) * ((k - 1 : ℕ) : ℝ) / ((Nat.totient k : ℝ) * (Nat.totient (k - 1) : ℝ))) ^ 2 =
            a ^ 2 * b ^ 2 := by dsimp [a, b]; ring
        rw [heq]
        nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
      have h1 := Finset.sum_le_sum hterm
      rw [Finset.sum_add_distrib] at h1
      have hleft : ∑ k ∈ Finset.Icc 2 (X - 1), ((k : ℝ) / (Nat.totient k : ℝ)) ^ 4 / 2 ≤
          (∑ j ∈ Finset.Icc 1 X, ((j : ℝ) / (Nat.totient j : ℝ)) ^ 4) / 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      have hright : ∑ k ∈ Finset.Icc 2 (X - 1),
            (((k - 1 : ℕ) : ℝ) / (Nat.totient (k - 1) : ℝ)) ^ 4 / 2 ≤
          (∑ j ∈ Finset.Icc 1 X, ((j : ℝ) / (Nat.totient j : ℝ)) ^ 4) / 2 := by
        have hshift : ∑ k ∈ Finset.Icc 2 (X - 1),
              (((k - 1 : ℕ) : ℝ) / (Nat.totient (k - 1) : ℝ)) ^ 4 / 2 =
            ∑ j ∈ Finset.Icc 1 (X - 2), ((j : ℝ) / (Nat.totient j : ℝ)) ^ 4 / 2 := by
          refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
          · intro k₁ hk₁ k₂ hk₂ heq; simp only [Finset.mem_Icc] at hk₁ hk₂; omega
          · intro j hj; simp only [Finset.mem_Icc] at hj
            exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k _; rfl
        rw [hshift, Finset.sum_div]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      linarith
    have hmom := ppl087_totient_fourth_moment_linear_bound X
    have hcoeff_nn : 0 ≤ 450 * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := by positivity
    calc ∑ k ∈ Finset.Icc 2 (X - 1),
            (((Finset.Icc (k + 1) X).filter
              (fun n => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card : ℝ)
        ≤ 450 * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) *
            ∑ k ∈ Finset.Icc 2 (X - 1),
              (((k * (k - 1) : ℕ) : ℝ) / (Nat.totient (k * (k - 1)) : ℝ)) ^ 2 := hstep1
      _ ≤ 450 * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) * (Real.exp 64 * (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (htot_sum.trans hmom) hcoeff_nn
      _ = (450 * Real.exp 64) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by ring
  linarith

/-! ## Section 4: Exact Reductions, Irreducibility, & Selberg Parity Barrier -/

/-- Exact equivalence between PPL 087 and positivity of the simultaneous pair count `S(n) ≥ 1`. -/
theorem ppl087_iff_pair_count_pos :
    (∀ n > 1, ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2)) ↔
    (∀ n > 1, 1 ≤ ((Finset.range n).filter
      (fun k => Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2))).card) := by
  constructor
  · intro h n hn
    rcases h n hn with ⟨k, hkn, hp1, hp2⟩
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkn, hp1, hp2⟩⟩
  · intro h n hn
    rcases Finset.card_pos.mp (h n hn) with ⟨k, hk⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k, hk.1, hk.2⟩

/-- **Exact Composite-Gap Reduction**: Because `k = 0` resolves all prime `n` and `k = 1`
resolves all `n` with `n + 1` prime, PPL 087 is equivalent to finding a witness `2 ≤ k < n`
(giving two distinct primes `n + k < n + k²`) whenever both `n` and `n + 1` are composite. -/
theorem ppl087_composite_gap_reduction :
    (∀ n > 1, ∃ k < n, Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2)) ↔
    (∀ n > 1, ¬ Nat.Prime n → ¬ Nat.Prime (n + 1) →
      ∃ k, 2 ≤ k ∧ k < n ∧ Nat.Prime (n + k) ∧ Nat.Prime (n + k ^ 2)) := by
  constructor
  · intro h n hn hnp0 hnp1
    rcases h n hn with ⟨k, hkn, hp1, hp2⟩
    refine ⟨k, ?_, hkn, hp1, hp2⟩
    by_contra hlt2
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · exact hnp0 (by simpa using hp1)
    · exact hnp1 hp1
  · intro h n hn
    by_cases hp0 : Nat.Prime n
    · exact ppl087_holds_for_prime hp0
    · by_cases hp1 : Nat.Prime (n + 1)
      · exact ⟨1, by omega, hp1, by simpa using hp1⟩
      · rcases h n hn hp0 hp1 with ⟨k, _, hkn, hp1', hp2'⟩
        exact ⟨k, hkn, hp1', hp2'⟩

/-- **Irreducibility of the Quadratic Factor `X² + n` (Schinzel Hypothesis H / Bunyakovsky
Precondition)**: For every `n ≥ 1`, `X² + n` is irreducible in `ℚ[X]`. Together with
`ppl087_universal_local_admissibility`, the pair `(X + n, X² + n)` satisfies all hypotheses of
Schinzel's Hypothesis H and Bateman–Horn for every `n ≥ 1`. -/
theorem ppl087_quadratic_factor_irreducible {n : ℕ} (hn : 1 ≤ n) :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (n : ℚ) : Polynomial ℚ) := by
  set P : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (n : ℚ)
  have hdegP : P.natDegree = 2 := by
    dsimp [P]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  have hPne : P ≠ 0 := by
    intro h0; rw [h0] at hdegP; simp at hdegP
  refine ⟨?_, ?_⟩
  · intro hunit
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b hab
    have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at hab; exact hPne hab
    have hb0 : b ≠ 0 := fun h => by rw [h, mul_zero] at hab; exact hPne hab
    have hsum : a.natDegree + b.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hdegP]
    by_cases ha_deg : a.natDegree = 0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero ha_deg]
      have hc0 : a.coeff 0 ≠ 0 := fun h => ha0 (by rw [Polynomial.eq_C_of_natDegree_eq_zero ha_deg, h, map_zero])
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
    · by_cases hb_deg : b.natDegree = 0
      · right
        rw [Polynomial.eq_C_of_natDegree_eq_zero hb_deg]
        have hc0 : b.coeff 0 ≠ 0 := fun h => hb0 (by rw [Polynomial.eq_C_of_natDegree_eq_zero hb_deg, h, map_zero])
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
      · exfalso
        have ha1 : a.natDegree = 1 := by omega
        have hlc : a.coeff 1 ≠ 0 := by
          have := Polynomial.leadingCoeff_ne_zero.mpr ha0
          rwa [Polynomial.leadingCoeff, ha1] at this
        have ha_eq : a = Polynomial.C (a.coeff 1) * Polynomial.X + Polynomial.C (a.coeff 0) := by
          ext i
          rcases i with _ | _ | k
          · simp
          · simp
          · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
              Polynomial.coeff_C]
            have hge : a.natDegree < k + 2 := by omega
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt hge]
            simp
        set r : ℚ := -(a.coeff 0) / (a.coeff 1)
        have har : a.eval r = 0 := by
          rw [ha_eq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, r]
          field_simp [hlc]
          ring
        have hPr : P.eval r = 0 := by
          rw [hab, Polynomial.eval_mul, har, zero_mul]
        have hPr_eq : P.eval r = r ^ 2 + (n : ℚ) := by
          dsimp [P]; simp
        have hnr : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        have hsq_nn : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
        linarith

/-- **Selberg Parity Barrier (Exact Divisor-Lattice Indistinguishability Theorem)**:
For every squarefree product `P` of distinct primes and every linear sieve weight function
`c : ℕ → ℝ` supported on proper divisors of `P` (`c P = 0`), the parity-separated nonnegative
weights `a(m) = 1_{ω(m) even}` and `b(m) = 1_{ω(m) odd}` satisfy:
1. `b(p * q) = 0` and `a(p * q) = 1` for every pair of distinct primes `p ≠ q` (in particular
   `b` assigns zero weight to every simultaneous prime pair `(n + k)(n + k²)` with `k ≥ 2`),
2. `∑_{m ∣ P, d ∣ m} a(m) = ∑_{m ∣ P, d ∣ m} b(m)` for every proper divisor `d ∣ P` (`d ≠ P`),
3. Every linear sieve functional `∑_{d ∣ P} c(d) A_d` supported on proper divisors of `P`
   assigns the exact same value to `a` and `b`. -/
theorem ppl087_selberg_parity_barrier {P : ℕ} (hP : Squarefree P) (c : ℕ → ℝ) (hcP : c P = 0) :
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
      (if (p * q).primeFactors.card % 2 = 0 then (1 : ℝ) else 0) = 1 ∧
      (if (p * q).primeFactors.card % 2 = 1 then (1 : ℝ) else 0) = 0) ∧
    (∀ d ∈ P.divisors, d ≠ P →
      ∑ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 0 then (1 : ℝ) else 0) =
      ∑ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 1 then (1 : ℝ) else 0)) ∧
    (∑ d ∈ P.divisors, c d *
        (∑ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 0 then (1 : ℝ) else 0)) =
     ∑ d ∈ P.divisors, c d *
        (∑ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 1 then (1 : ℝ) else 0))) := by
  have hpart1 : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
      (if (p * q).primeFactors.card % 2 = 0 then (1 : ℝ) else 0) = 1 ∧
      (if (p * q).primeFactors.card % 2 = 1 then (1 : ℝ) else 0) = 0 := by
    intro p q hp hq hpq
    have hpf : (p * q).primeFactors = {p, q} := by
      rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]
      ext r; simp
    rw [hpf, Finset.card_pair hpq]
    simp
  have hpart2 : ∀ d ∈ P.divisors, d ≠ P →
      ∑ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 0 then (1 : ℝ) else 0) =
      ∑ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 1 then (1 : ℝ) else 0) := by
    intro d hd hdne
    have hP0 : P ≠ 0 := hP.ne_zero
    have hd_dvd : d ∣ P := (Nat.mem_divisors.mp hd).1
    have hd0 : d ≠ 0 := (hP.squarefree_of_dvd hd_dvd).ne_zero
    set Q := P / d
    have hPdQ : d * Q = P := Nat.mul_div_cancel' hd_dvd
    have hQ_gt1 : 1 < Q := by
      have hQ0 : Q ≠ 0 := fun h0 => hP0 (by rw [← hPdQ, h0, mul_zero])
      have hQ1 : Q ≠ 1 := fun h1 => hdne (by rw [← hPdQ, h1, mul_one])
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hQ0, hQ1⟩
    have hcop_dQ : Nat.Coprime d Q := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne1
      rcases Nat.exists_prime_and_dvd hne1 with ⟨p, hp, hpg⟩
      have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d Q)
      have hpQ : p ∣ Q := hpg.trans (Nat.gcd_dvd_right d Q)
      have hsq : p * p ∣ P := by rw [← hPdQ]; exact mul_dvd_mul hpd hpQ
      exact hp.not_isUnit (hP p hsq)
    have hQ_sq : Squarefree Q := hP.squarefree_of_dvd (by rw [← hPdQ]; exact dvd_mul_left Q d)
    have hdiff_zero :
        (∑ m ∈ P.divisors.filter (d ∣ ·),
            (if m.primeFactors.card % 2 = 0 then (1 : ℝ) else 0)) -
        (∑ m ∈ P.divisors.filter (d ∣ ·),
            (if m.primeFactors.card % 2 = 1 then (1 : ℝ) else 0)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ m ∈ P.divisors.filter (d ∣ ·),
          (if m.primeFactors.card % 2 = 0 then (1 : ℝ) else 0) -
            (if m.primeFactors.card % 2 = 1 then (1 : ℝ) else 0) =
          ((-1 : ℝ) ^ m.primeFactors.card) := by
        intro m _
        rcases Nat.mod_two_eq_zero_or_one m.primeFactors.card with h0 | h1
        · simp only [h0, ↓reduceIte, zero_ne_one, sub_zero]
          have heven : Even m.primeFactors.card := Nat.even_iff.mpr h0
          exact (Even.neg_one_pow heven).symm
        · simp only [h1, one_ne_zero, ↓reduceIte, zero_sub]
          have hodd : Odd m.primeFactors.card := Nat.odd_iff.mpr h1
          exact (Odd.neg_one_pow hodd).symm
      rw [Finset.sum_congr rfl hterm]
      have hbij : P.divisors.filter (d ∣ ·) = Q.divisors.image (d * ·) := by
        ext m
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
        constructor
        · rintro ⟨⟨hmP, _⟩, ⟨e, rfl⟩⟩
          refine ⟨e, ⟨?_, by omega⟩, rfl⟩
          rw [← hPdQ] at hmP
          exact (mul_dvd_mul_iff_left hd0).mp hmP
        · rintro ⟨e, ⟨heQ, _⟩, rfl⟩
          exact ⟨⟨by rw [← hPdQ]; exact mul_dvd_mul_left d heQ, hP0⟩, dvd_mul_right d e⟩
      rw [hbij, Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h)]
      have hsplit_pow : ∀ e ∈ Q.divisors,
          (-1 : ℝ) ^ (d * e).primeFactors.card =
            (-1 : ℝ) ^ d.primeFactors.card * (-1 : ℝ) ^ e.primeFactors.card := by
        intro e he
        have heQ : e ∣ Q := (Nat.mem_divisors.mp he).1
        have he0 : e ≠ 0 := (hQ_sq.squarefree_of_dvd heQ).ne_zero
        have hcop_de : Nat.Coprime d e := hcop_dQ.coprime_dvd_right heQ
        have hdisj : Disjoint d.primeFactors e.primeFactors := by
          rw [Finset.disjoint_left]
          intro p hpd hpe
          have hp := Nat.prime_of_mem_primeFactors hpd
          exact hp.not_dvd_one (hcop_de.gcd_eq_one ▸ Nat.dvd_gcd
            (Nat.dvd_of_mem_primeFactors hpd) (Nat.dvd_of_mem_primeFactors hpe))
        rw [Nat.primeFactors_mul hd0 he0, Finset.card_union_of_disjoint hdisj, pow_add]
      rw [Finset.sum_congr rfl hsplit_pow, ← Finset.mul_sum]
      have hsum_mu : ∑ e ∈ Q.divisors, (-1 : ℝ) ^ e.primeFactors.card = 0 := by
        have hprod := prod_one_add_eq_sum_squarefree_divisors (fun _ => (-1 : ℝ)) (by omega : 1 ≤ Q)
        have hfilt_eq : Q.divisors.filter Squarefree = Q.divisors := by
          ext e
          simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro he
          exact hQ_sq.squarefree_of_dvd (Nat.mem_divisors.mp he).1
        rw [hfilt_eq] at hprod
        have hrhs_eq : ∑ e ∈ Q.divisors, ∏ _p ∈ e.primeFactors, (-1 : ℝ) =
            ∑ e ∈ Q.divisors, (-1 : ℝ) ^ e.primeFactors.card := by
          refine Finset.sum_congr rfl fun e _ => by rw [Finset.prod_const]
        rw [hrhs_eq] at hprod
        rw [← hprod]
        rcases Nat.exists_prime_and_dvd (by omega : Q ≠ 1) with ⟨q, hq, hqQ⟩
        have hq_mem : q ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqQ, by omega⟩
        exact Finset.prod_eq_zero hq_mem (by norm_num)
      rw [hsum_mu, mul_zero]
    linarith
  have hpart3 :
      ∑ d ∈ P.divisors, c d *
          (∑ m ∈ P.divisors.filter (d ∣ ·),
            (if m.primeFactors.card % 2 = 0 then (1 : ℝ) else 0)) =
      ∑ d ∈ P.divisors, c d *
          (∑ m ∈ P.divisors.filter (d ∣ ·),
            (if m.primeFactors.card % 2 = 1 then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hdP : d = P
    · subst hdP; rw [hcP, zero_mul, zero_mul]
    · rw [hpart2 d hd hdP]
  exact ⟨hpart1, hpart2, hpart3⟩

end PPL087
