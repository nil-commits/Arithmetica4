/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.DFA
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic
import RHDirect.Arith4Ext_AutomataCombinatorics
import RHDirect.Stage8ExplicitPrimeBounds

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 073 (Shallit Open Problem #13): Decidability of Prime Acceptance by a Base-`k` DFA

## Honest Scope & Literature Status
This file formalizes a pure-Mathlib theorem suite (`0` `sorry`, `0` `admit`, `0` `native_decide`,
`0` custom or `private` definitions in any public theorem signature) for **PPL 073 / Shallit
Open Problem #13** (£50, **OPEN** on `prizeproblems.org` and Jeffrey Shallit's open-problems list):
> *Is it decidable whether a given base-`k` deterministic finite automaton (DFA) accepts the
> base-`k` representation of at least one prime number?*

**Shallit Open Problem #13 REMAINS OPEN.** This file does **not** claim to decide the general
base-`k` DFA prime-acceptance problem. Instead, it formally proves four core pillars in Lean 4:

1. **Minsky–Papert Non-Regularity & Quantitative Prime-Soundness Ceiling (`∀ k ≥ 2`):**
   - `ppl073_prime_sound_no_leading_zero_bound_msd`: Every `m`-state base-`k` DFA whose accepted
     words have no leading zeros and represent only primes satisfies `val(w) ≤ k ^ m` for every
     `w ∈ M.accepts` (via pumping + Fermat's Little Theorem on geometric sums).
   - `ppl073_no_infinite_prime_dfa_msd`: No finite DFA with no-leading-zero words accepts infinitely
     many primes and only primes.
   - `ppl073_minsky_papert_msd_canonical`, `ppl073_minsky_papert_msd_all`,
     `ppl073_minsky_papert_lsd_all`, `ppl073_minsky_papert_lsd_canonical`: Unconditional
     non-regularity of the base-`k` prime language in both MSD-first and LSD-first conventions,
     both with and without leading/trailing zeros.
   - `ppl073_msd_lsd_prime_acceptance_equiv`: Formal equivalence of MSD and LSD prime acceptance
     via DFA reversal closure.

2. **Explicit Modular & Periodic-Suffix Decidable Subclasses (Dirichlet's Theorem in AP):**
   - `ppl073_mod_dfa_msd`: Exact `M`-state MSD-first DFA recognizing `n ≡ r [MOD M]`.
   - `ppl073_mod_dfa_lsd`: Exact `M * M`-state LSD-first DFA recognizing `n ≡ r [MOD M]`.
   - `ppl073_coprime_residue_infinitely_many_primes_msd`: Every DFA accepting a coprime residue
     class `r (mod M)` accepts infinitely many primes.
   - `ppl073_coprime_suffix_dfa_infinitely_many_primes_msd`: Explicit suffix DFA for `Σ_k^* · u`
     and proof that any coprime suffix `u` (`Nat.Coprime (val u) k`) yields infinitely many primes.
   - `ppl073_finite_dfa_prime_iff_bounded`: Exact decidability reduction for finite-language DFAs
     (`M` accepts a prime ↔ `M` accepts a prime word of length `< m`).
   - `ppl073_congruence_dfa_prime_iff` & `ppl073_congruence_dfa_dichotomy`: Exact finite-checkable
     necessary and sufficient prime-acceptance criterion and finite-vs-infinite dichotomy for
     congruence-closed DFAs.

3. **Leading-Prefix / Short-Interval Prime Acceptance (`w · Σ_k^*`, Tier A PNT Short Intervals):**
   - `ppl073_prefix_dfa_exists`: Explicit `(w.length + 2)`-state DFA recognizing `w · Σ_k^*`.
   - `ppl073_prefix_eventually_has_prime`: For every `k ≥ 2` and nonzero base-`k` prefix `w`, for
     all sufficiently large `t`, there is a prime of length `w.length + t` starting with `w`
     (via `RHDirect.Stage8ExplicitPrimeBounds.exists_prime_in_Ioc_polylog`).
   - `ppl073_prefix_infinitely_many_primes`: Every DFA whose language contains `w · Σ_k^*` for
     any nonzero base-`k` prefix `w` accepts infinitely many primes.

4. **Explicit Sparse-Automaton Barriers (Fermat, Mersenne, Repunit & Missing-Digit DFAs):**
   - `ppl073_repunit_barrier_dfa`: Explicit `(n₀ + 3)`-state base-`k` DFA (`3` states at `n₀ = 0`)
     accepting `{(k^n - 1)/(k - 1) | n > n₀}`, with exact prime-acceptance equivalence.
   - `ppl073_mersenne_barrier_dfa`: Explicit `(n₀ + 3)`-state base-2 DFA (`3` states at `n₀ = 0`)
     accepting `{2^n - 1 | n > n₀}`, tying prime acceptance to Mersenne prime infinitude.
   - `ppl073_repunit_prime_exponent_prime`: Prime repunit `(k^n - 1)/(k - 1)` (`n ≥ 2`) forces
     `n` prime (specializing to Mersenne primes at `k = 2`).
   - `ppl073_fermat_barrier_dfa`: Explicit `(n₀ + 4)`-state base-2 DFA (`4` states at `n₀ = 0`)
     accepting `1 0^{n₀} 0^* 1 = {2^n + 1 | n > n₀}`, with exact equivalence to
     `∃ m, n₀ < 2 ^ m ∧ Nat.Prime (2 ^ (2 ^ m) + 1)`.
   - `ppl073_sixth_fermat_prime_dfa`: Explicit **20-state** base-2 DFA whose prime acceptance is
     provably equivalent to the existence of a sixth Fermat prime (`m ≥ 5`).
   - `ppl073_missing_digit_dfa_prime_dichotomy`: Explicit 2-state missing-digit DFA, proving
     prime acceptance for all `k ≥ 3` and every forbidden digit `d : Fin k` (and exact `k = 2`
     dichotomy).
-/

namespace PPL073

open Filter Finset
open Arith4Ext.AutomataCombinatorics

/-! ### Private Base-`k` Digit & DFA Helper Lemmas -/

private lemma ofDigits_append_lsd (k : ℕ) (u v : List ℕ) :
    Nat.ofDigits k (u ++ v) = Nat.ofDigits k u + k ^ u.length * Nat.ofDigits k v := by
  induction u with
  | nil => simp [Nat.ofDigits]
  | cons d u ih =>
    simp only [List.cons_append, Nat.ofDigits, List.length_cons, ih, pow_succ]
    ring

private lemma ofDigits_append_msd (k : ℕ) (u v : List (Fin k)) :
    Nat.ofDigits k ((u ++ v).reverse.map Fin.val) =
      Nat.ofDigits k (v.reverse.map Fin.val) +
        k ^ v.length * Nat.ofDigits k (u.reverse.map Fin.val) := by
  rw [List.reverse_append, List.map_append, ofDigits_append_lsd]
  simp only [List.length_map, List.length_reverse]

private lemma ofDigits_cons_msd (k : ℕ) (d : Fin k) (w : List (Fin k)) :
    Nat.ofDigits k ((d :: w).reverse.map Fin.val) =
      Nat.ofDigits k (w.reverse.map Fin.val) + k ^ w.length * d.val := by
  simpa [Nat.ofDigits] using ofDigits_append_msd k [d] w

private lemma ofDigits_concat_msd (k : ℕ) (w : List (Fin k)) (d : Fin k) :
    Nat.ofDigits k ((w ++ [d]).reverse.map Fin.val) =
      d.val + k * Nat.ofDigits k (w.reverse.map Fin.val) := by
  rw [ofDigits_append_msd]
  simp

private lemma ofDigits_lt_pow_lsd {k : ℕ} (w : List (Fin k)) :
    Nat.ofDigits k (w.map Fin.val) < k ^ w.length := by
  induction w with
  | nil => simp
  | cons d w ih =>
    simp only [List.map_cons, Nat.ofDigits, List.length_cons, pow_succ]
    have hd : d.val + 1 ≤ k := d.isLt
    have hw : Nat.ofDigits k (w.map Fin.val) + 1 ≤ k ^ w.length := ih
    nlinarith

private lemma ofDigits_lt_pow_msd {k : ℕ} (w : List (Fin k)) :
    Nat.ofDigits k (w.reverse.map Fin.val) < k ^ w.length := by
  have h := ofDigits_lt_pow_lsd w.reverse
  simpa [List.length_reverse] using h

private lemma ofDigits_pos_of_head_ne_zero {k : ℕ} (hk : 1 ≤ k) (w : List (Fin k))
    (hne : w ≠ []) (hhead : ∀ d ∈ w.head?, d.val ≠ 0) :
    0 < Nat.ofDigits k (w.reverse.map Fin.val) := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons d tl =>
    rw [ofDigits_cons_msd]
    have hd : 0 < d.val := Nat.pos_of_ne_zero (hhead d rfl)
    have hpow : 0 < k ^ tl.length := pow_pos (by omega) _
    exact Nat.add_pos_right _ (Nat.mul_pos hpow hd)

private lemma exists_fixed_len_digits_msd {k : ℕ} (hk : 2 ≤ k) :
    ∀ (t r : ℕ), r < k ^ t →
      ∃ v : List (Fin k), v.length = t ∧ Nat.ofDigits k (v.reverse.map Fin.val) = r
  | 0, r, hr => by
    have hr0 : r = 0 := by simpa using hr
    exact ⟨[], rfl, by simp [hr0]⟩
  | t + 1, r, hr => by
    have hq : r / k < k ^ t := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [pow_succ] using hr
    obtain ⟨v, hv_len, hv_val⟩ := exists_fixed_len_digits_msd hk t (r / k) hq
    refine ⟨v ++ [⟨r % k, Nat.mod_lt r (by omega)⟩], by simp [hv_len], ?_⟩
    rw [ofDigits_concat_msd, hv_val]
    exact Nat.mod_add_div r k

private lemma exists_canonical_digits_msd {k : ℕ} (hk : 2 ≤ k) :
    ∀ (n : ℕ), 1 ≤ n →
      ∃ w : List (Fin k),
        (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.ofDigits k (w.reverse.map Fin.val) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hlt : n < k
    · refine ⟨[⟨n, hlt⟩], ?_, ?_⟩
      · intro d hd
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
        subst hd
        dsimp only
        omega
      · simp
    · push Not at hlt
      have hq_pos : 1 ≤ n / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hlt)
      have hq_lt : n / k < n := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨w, hw_head, hw_val⟩ := ih (n / k) hq_lt hq_pos
      have hw_ne : w ≠ [] := by
        intro hnil
        rw [hnil] at hw_val
        simp at hw_val
        omega
      refine ⟨w ++ [⟨n % k, Nat.mod_lt n (by omega)⟩], ?_, ?_⟩
      · intro d hd
        cases w with
        | nil => exact (hw_ne rfl).elim
        | cons a tl =>
          simp only [List.cons_append, List.head?_cons] at hd
          exact hw_head d hd
      · rw [ofDigits_concat_msd, hw_val]
        exact Nat.mod_add_div n k

private lemma exists_canonical_digits_with_suffix_msd {k : ℕ} (hk : 2 ≤ k)
    (u : List (Fin k)) (n : ℕ) (hn : k ^ u.length ≤ n)
    (hmod : n ≡ Nat.ofDigits k (u.reverse.map Fin.val) [MOD k ^ u.length]) :
    ∃ v : List (Fin k),
      (∀ d ∈ (v ++ u).head?, d.val ≠ 0) ∧
      Nat.ofDigits k ((v ++ u).reverse.map Fin.val) = n := by
  set M := k ^ u.length with hM_def
  have hM_pos : 0 < M := pow_pos (by omega) _
  have hr_lt : Nat.ofDigits k (u.reverse.map Fin.val) < M :=
    ofDigits_lt_pow_msd u
  have hrem : n % M = Nat.ofDigits k (u.reverse.map Fin.val) := by
    rw [Nat.ModEq] at hmod
    rw [hmod, Nat.mod_eq_of_lt hr_lt]
  have hq_pos : 1 ≤ n / M := (Nat.le_div_iff_mul_le hM_pos).mpr (by simpa using hn)
  obtain ⟨v, hv_head, hv_val⟩ := exists_canonical_digits_msd hk (n / M) hq_pos
  have hv_ne : v ≠ [] := by
    intro hnil
    rw [hnil] at hv_val
    simp at hv_val
    omega
  refine ⟨v, ?_, ?_⟩
  · intro d hd
    cases v with
    | nil => exact (hv_ne rfl).elim
    | cons a tl =>
      simp only [List.cons_append, List.head?_cons] at hd
      exact hv_head d hd
  · rw [ofDigits_append_msd, hv_val, ← hrem]
    exact Nat.mod_add_div n M

private lemma ofDigits_replicate_one_mul (k : ℕ) (hk : 2 ≤ k) :
    ∀ n : ℕ, (k - 1) * Nat.ofDigits k (List.replicate n 1) = k ^ n - 1
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, Nat.ofDigits, Nat.cast_one, mul_add, mul_one, ← mul_assoc,
      mul_comm (k - 1) k, mul_assoc, ofDigits_replicate_one_mul k hk n]
    have h1 : 1 ≤ k ^ n := Nat.one_le_pow n k (by omega)
    have h2 : k ≤ k ^ (n + 1) := by
      rw [pow_succ']
      exact Nat.le_mul_of_pos_right k h1
    have h3 : k * (k ^ n - 1) = k ^ (n + 1) - k := by
      rw [Nat.mul_sub_left_distrib, mul_one, pow_succ']
    rw [h3]
    omega

private lemma ofDigits_replicate_one_eq (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.ofDigits k (List.replicate n 1) = (k ^ n - 1) / (k - 1) := by
  have hne : k - 1 ≠ 0 := by omega
  exact Nat.eq_div_of_mul_eq_right hne (ofDigits_replicate_one_mul k hk n)

private lemma dfa_evalFrom_append_aux {α Q : Type*} (M : DFA α Q) (q : Q) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  simp [DFA.evalFrom]

private lemma dfa_evalFrom_cons_aux {α Q : Type*} (M : DFA α Q) (q : Q) (a : α) (u : List α) :
    M.evalFrom q (a :: u) = M.evalFrom (M.step q a) u := rfl

/-! ### Section 1: Minsky–Papert Non-Regularity & Quantitative Prime-Soundness Ceiling -/

private lemma pumped_prefix_step (k : ℕ) (x y : List (Fin k)) (n : ℕ) :
    Nat.ofDigits k ((x ++ (List.replicate (n + 1) y).flatten).reverse.map Fin.val) =
      Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) * k ^ y.length +
        Nat.ofDigits k (y.reverse.map Fin.val) := by
  have hrep : (List.replicate (n + 1) y).flatten = (List.replicate n y).flatten ++ y := by
    induction n with
    | zero => simp
    | succ m ih =>
      calc (List.replicate (m + 1 + 1) y).flatten
          = y ++ (List.replicate (m + 1) y).flatten := by
            rw [List.replicate_succ, List.flatten_cons]
        _ = y ++ ((List.replicate m y).flatten ++ y) := by rw [ih]
        _ = (y ++ (List.replicate m y).flatten) ++ y := by rw [List.append_assoc]
        _ = (List.replicate (m + 1) y).flatten ++ y := by
            rw [List.replicate_succ, List.flatten_cons]
  rw [hrep, ← List.append_assoc, ofDigits_append_msd]
  ring

private lemma pumped_prefix_diff (k : ℕ) (hk : 1 ≤ k) (x y : List (Fin k)) :
    ∀ n : ℕ,
      Nat.ofDigits k ((x ++ (List.replicate (n + 1) y).flatten).reverse.map Fin.val) =
        Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) +
          (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
            Nat.ofDigits k (y.reverse.map Fin.val)) * (k ^ y.length) ^ n
  | 0 => by
    rw [pumped_prefix_step]
    simp only [List.replicate_zero, List.flatten_nil, List.append_nil, pow_zero, mul_one]
    have h1 : 1 ≤ k ^ y.length := Nat.one_le_pow y.length k (by omega)
    set A := Nat.ofDigits k (x.reverse.map Fin.val)
    set B := Nat.ofDigits k (y.reverse.map Fin.val)
    set r := k ^ y.length
    have hr : A * (r - 1) + A = A * r := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have : A ≤ A * r := Nat.le_mul_of_pos_right A (by omega)
      omega
    omega
  | n + 1 => by
    have hstep : Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) *
        k ^ y.length + Nat.ofDigits k (y.reverse.map Fin.val) =
        Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) +
          (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
            Nat.ofDigits k (y.reverse.map Fin.val)) * (k ^ y.length) ^ n :=
      (pumped_prefix_step k x y n).symm.trans (pumped_prefix_diff k hk x y n)
    rw [pumped_prefix_step k x y (n + 1), pumped_prefix_diff k hk x y n]
    calc (Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) +
            (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
              Nat.ofDigits k (y.reverse.map Fin.val)) * (k ^ y.length) ^ n) * k ^ y.length +
            Nat.ofDigits k (y.reverse.map Fin.val)
        = (Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) *
            k ^ y.length + Nat.ofDigits k (y.reverse.map Fin.val)) +
          (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
            Nat.ofDigits k (y.reverse.map Fin.val)) * (k ^ y.length) ^ (n + 1) := by
          rw [pow_succ]; ring
      _ = Nat.ofDigits k ((x ++ (List.replicate n y).flatten).reverse.map Fin.val) +
            (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
              Nat.ofDigits k (y.reverse.map Fin.val)) * (k ^ y.length) ^ n +
            (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
              Nat.ofDigits k (y.reverse.map Fin.val)) * (k ^ y.length) ^ (n + 1) := by
          rw [hstep]

private lemma pumped_prefix_sum (k : ℕ) (hk : 1 ≤ k) (x y : List (Fin k)) :
    ∀ m : ℕ, 1 ≤ m →
      Nat.ofDigits k ((x ++ (List.replicate m y).flatten).reverse.map Fin.val) =
        Nat.ofDigits k ((x ++ y).reverse.map Fin.val) +
          (Nat.ofDigits k (x.reverse.map Fin.val) * (k ^ y.length - 1) +
            Nat.ofDigits k (y.reverse.map Fin.val)) *
            ∑ j ∈ Finset.Ico 1 m, (k ^ y.length) ^ j := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    rw [pumped_prefix_diff k hk x y m, ih]
    have hIco : Finset.Ico 1 (m + 1) = insert m (Finset.Ico 1 m) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnot : m ∉ Finset.Ico 1 m := by simp
    rw [hIco, Finset.sum_insert hnot]
    ring

private lemma geom_sum_Ico_one_mul (r : ℕ) (hr : 1 ≤ r) :
    ∀ p : ℕ, 1 ≤ p → (r - 1) * (∑ j ∈ Finset.Ico 1 p, r ^ j) + r = r ^ p := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
    have hIco : Finset.Ico 1 (p + 1) = insert p (Finset.Ico 1 p) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnot : p ∉ Finset.Ico 1 p := by simp
    rw [hIco, Finset.sum_insert hnot, mul_add]
    have hstep : (r - 1) * r ^ p + r ^ p = r ^ (p + 1) := by
      rw [Nat.sub_mul, one_mul, pow_succ']
      have : r ^ p ≤ r * r ^ p := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega

/-- **Quantitative Minsky–Papert / Hartmanis–Shank Prime-Soundness Ceiling:**
For any base `k ≥ 2`, any `m : ℕ`, and any `m`-state DFA `M : DFA (Fin k) (Fin m)`:
if every word accepted by `M` has no leading zero and represents a prime (MSD-first),
then **every** accepted word `w ∈ M.accepts` has numeric value at most `k ^ m`. -/
theorem ppl073_prime_sound_no_leading_zero_bound_msd (k m : ℕ) (hk : 2 ≤ k)
    (M : DFA (Fin k) (Fin m))
    (hsound : ∀ w ∈ M.accepts,
      (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) :
    ∀ w ∈ M.accepts, Nat.ofDigits k (w.reverse.map Fin.val) ≤ k ^ m := by
  intro w hw
  by_contra hgt
  push Not at hgt
  set p := Nat.ofDigits k (w.reverse.map Fin.val) with hp_def
  have hp_prime : Nat.Prime p := (hsound w hw).2
  have hw_head : ∀ d ∈ w.head?, d.val ≠ 0 := (hsound w hw).1
  have hlen : m ≤ w.length := by
    have hlt := ofDigits_lt_pow_msd w
    by_contra hwm
    push Not at hwm
    have hpow : k ^ w.length ≤ k ^ m := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hwm)
    omega
  obtain ⟨x, y, z, hw_eq, hxy_le, hy_pos, hpump⟩ := dfa_pumping_lemma M w hw hlen
  have hxy_ne : x ++ y ≠ [] := by
    intro hnil
    have hln := congrArg List.length hnil
    rw [List.length_append, List.length_nil] at hln
    omega
  have hxy_head : ∀ d ∈ (x ++ y).head?, d.val ≠ 0 := by
    intro d hd
    have h1 : (x ++ y ++ z).head? = (x ++ y).head? := by
      cases h : x ++ y with
      | nil => exact (hxy_ne h).elim
      | cons a tl => simp
    rw [← hw_eq] at h1
    exact hw_head d (h1.symm ▸ hd)
  have hxy_pos : 0 < Nat.ofDigits k ((x ++ y).reverse.map Fin.val) :=
    ofDigits_pos_of_head_ne_zero (by omega) (x ++ y) hxy_ne hxy_head
  set r := k ^ y.length with hr_def
  have hr_ge_2 : 2 ≤ r := by
    calc 2 ≤ k := hk
      _ = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ y.length := Nat.pow_le_pow_right (by omega) hy_pos
  set D := Nat.ofDigits k (x.reverse.map Fin.val) * (r - 1) +
    Nat.ofDigits k (y.reverse.map Fin.val) with hD_def
  have hD_pos : 0 < D := by
    rw [ofDigits_append_msd] at hxy_pos
    by_cases hx0 : Nat.ofDigits k (x.reverse.map Fin.val) = 0
    · rw [hx0, mul_zero, add_zero] at hxy_pos
      omega
    · have : 1 ≤ Nat.ofDigits k (x.reverse.map Fin.val) * (r - 1) :=
        Nat.mul_pos (Nat.pos_of_ne_zero hx0) (by omega)
      omega
  set wp := x ++ (List.replicate p y).flatten ++ z with hwp_def
  have hwp_acc : wp ∈ M.accepts := hpump p
  have hwp_prime : Nat.Prime (Nat.ofDigits k (wp.reverse.map Fin.val)) := (hsound wp hwp_acc).2
  set S := ∑ j ∈ Finset.Ico 1 p, r ^ j with hS_def
  have hwp_val : Nat.ofDigits k (wp.reverse.map Fin.val) = p + k ^ z.length * (D * S) := by
    have h1 : Nat.ofDigits k (wp.reverse.map Fin.val) =
        Nat.ofDigits k (z.reverse.map Fin.val) +
          k ^ z.length * Nat.ofDigits k ((x ++ (List.replicate p y).flatten).reverse.map Fin.val) := by
      rw [hwp_def, ofDigits_append_msd]
    have h2 : p = Nat.ofDigits k (z.reverse.map Fin.val) +
        k ^ z.length * Nat.ofDigits k ((x ++ y).reverse.map Fin.val) := by
      rw [hp_def, hw_eq, ofDigits_append_msd]
    have h3 : Nat.ofDigits k ((x ++ (List.replicate p y).flatten).reverse.map Fin.val) =
        Nat.ofDigits k ((x ++ y).reverse.map Fin.val) + D * S :=
      pumped_prefix_sum k (by omega) x y p hp_prime.one_le
    calc Nat.ofDigits k (wp.reverse.map Fin.val)
        = Nat.ofDigits k (z.reverse.map Fin.val) +
            k ^ z.length * (Nat.ofDigits k ((x ++ y).reverse.map Fin.val) + D * S) := by
          rw [h1, h3]
      _ = (Nat.ofDigits k (z.reverse.map Fin.val) +
            k ^ z.length * Nat.ofDigits k ((x ++ y).reverse.map Fin.val)) +
          k ^ z.length * (D * S) := by ring
      _ = p + k ^ z.length * (D * S) := by rw [← h2]
  have hS_pos : 0 < S := by
    have h1_mem : 1 ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨le_rfl, hp_prime.one_lt⟩
    have hle : r ^ 1 ≤ S := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h1_mem
    rw [pow_one] at hle
    omega
  have hwp_gt_p : p < Nat.ofDigits k (wp.reverse.map Fin.val) := by
    rw [hwp_val]
    have hkz : 0 < k ^ z.length := pow_pos (by omega) _
    have : 0 < k ^ z.length * (D * S) := Nat.mul_pos hkz (Nat.mul_pos hD_pos hS_pos)
    omega
  have hr_sub_lt_p : r - 1 < p := by
    have hy_le_m : y.length ≤ m := by omega
    have hr_le : r ≤ k ^ m := Nat.pow_le_pow_right (by omega) hy_le_m
    have hp_gt : k ^ m < p := hgt
    omega
  have hp_dvd_S : p ∣ S := by
    let : Fact p.Prime := ⟨hp_prime⟩
    have hgeom := geom_sum_Ico_one_mul r (by omega) p hp_prime.one_le
    have hcast : (((r - 1) * S + r : ℕ) : ZMod p) = ((r ^ p : ℕ) : ZMod p) :=
      congrArg (Nat.cast : ℕ → ZMod p) hgeom
    push_cast at hcast
    have hfermat : (r : ZMod p) ^ p = (r : ZMod p) := ZMod.pow_card (r : ZMod p)
    rw [hfermat] at hcast
    have hmul0 : ((r - 1 : ℕ) : ZMod p) * (S : ZMod p) = 0 := by
      linear_combination hcast
    have hr1_ne0 : ((r - 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : p ∣ (r - 1) := (ZMod.natCast_eq_zero_iff (r - 1) p).mp hz
      have hpos : 0 < r - 1 := by omega
      have hle : p ≤ r - 1 := Nat.le_of_dvd hpos hdvd
      omega
    have hS0 : (S : ZMod p) = 0 := (mul_eq_zero.mp hmul0).resolve_left hr1_ne0
    exact (ZMod.natCast_eq_zero_iff S p).mp hS0
  have hp_dvd_wp : p ∣ Nat.ofDigits k (wp.reverse.map Fin.val) := by
    rw [hwp_val]
    exact dvd_add dvd_rfl (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hp_dvd_S D) _)
  rcases hwp_prime.eq_one_or_self_of_dvd p hp_dvd_wp with h1 | h2
  · exact hp_prime.ne_one h1
  · omega

/-- **Strong Minsky–Papert / Hartmanis–Shank Theorem:**
No finite DFA over `Fin k` (`k ≥ 2`) whose accepted words have no leading zeros and represent
only primes can accept infinitely many distinct primes. -/
theorem ppl073_no_infinite_prime_dfa_msd (k m : ℕ) (hk : 2 ≤ k) (M : DFA (Fin k) (Fin m))
    (hsound : ∀ w ∈ M.accepts,
      (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) :
    ({ p : ℕ | ∃ w ∈ M.accepts, Nat.ofDigits k (w.reverse.map Fin.val) = p }).Finite := by
  refine (Set.finite_le_nat (k ^ m)).subset ?_
  rintro p ⟨w, hw, rfl⟩
  exact ppl073_prime_sound_no_leading_zero_bound_msd k m hk M hsound w hw

/-- **Minsky–Papert Non-Regularity Theorem (Canonical MSD-First, `∀ k ≥ 2`):**
The canonical base-`k` MSD prime language (no leading zeros) is not regular. -/
theorem ppl073_minsky_papert_msd_canonical (k m : ℕ) (hk : 2 ≤ k) (M : DFA (Fin k) (Fin m)) :
    M.accepts ≠
      { w : List (Fin k) |
        (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)) } := by
  intro heq
  have hsound : ∀ w ∈ M.accepts,
      (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)) := by
    intro w hw
    rw [heq] at hw
    exact hw
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (k ^ m + 1)
  obtain ⟨w, hw_head, hw_val⟩ := exists_canonical_digits_msd hk p hp_prime.one_le
  have hw_acc : w ∈ M.accepts := by
    rw [heq]
    exact ⟨hw_head, hw_val.symm ▸ hp_prime⟩
  have hle := ppl073_prime_sound_no_leading_zero_bound_msd k m hk M hsound w hw_acc
  omega

/-- **Minsky–Papert Non-Regularity Theorem (Arbitrary-Leading-Zero MSD-First, `∀ k ≥ 2`):**
Even allowing arbitrary leading zeros, the base-`k` MSD prime language is not regular. -/
theorem ppl073_minsky_papert_msd_all (k m : ℕ) (hk : 2 ≤ k) (M : DFA (Fin k) (Fin m)) :
    M.accepts ≠ { w : List (Fin k) | Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)) } := by
  intro heq
  -- 3-state DFA recognizing all words with no leading zero: `∀ d ∈ w.head?, d.val ≠ 0`.
  let Dnz : DFA (Fin k) (Fin 3) := {
    step := fun q d =>
      if q.val = 0 then
        if d.val = 0 then ⟨2, by omega⟩ else ⟨1, by omega⟩
      else q
    start := ⟨0, by omega⟩
    accept := {⟨0, by omega⟩, ⟨1, by omega⟩}
  }
  have hDnz_stay : ∀ (q : Fin 3) (u : List (Fin k)), q.val ≠ 0 → Dnz.evalFrom q u = q := by
    intro q u hq
    induction u with
    | nil => rfl
    | cons a tl ih =>
      change Dnz.evalFrom (Dnz.step q a) tl = q
      have hs : Dnz.step q a = q := by simp [Dnz, hq]
      rw [hs]
      exact ih
  have hDnz_acc : ∀ w : List (Fin k), w ∈ Dnz.accepts ↔ (∀ d ∈ w.head?, d.val ≠ 0) := by
    intro w
    cases w with
    | nil =>
      change Dnz.evalFrom Dnz.start [] ∈ Dnz.accept ↔ _
      simp [Dnz, DFA.evalFrom]
    | cons d tl =>
      change Dnz.evalFrom (Dnz.step ⟨0, by omega⟩ d) tl ∈ Dnz.accept ↔
        (∀ a ∈ (d :: tl).head?, a.val ≠ 0)
      by_cases hd0 : d.val = 0
      · have hs : Dnz.step ⟨0, by omega⟩ d = ⟨2, by omega⟩ := by simp [Dnz, hd0]
        rw [hs, hDnz_stay ⟨2, by omega⟩ tl (by norm_num)]
        simp [Dnz, hd0]
      · have hs : Dnz.step ⟨0, by omega⟩ d = ⟨1, by omega⟩ := by simp [Dnz, hd0]
        rw [hs, hDnz_stay ⟨1, by omega⟩ tl (by norm_num)]
        simp [Dnz, hd0]
  obtain ⟨P, hP⟩ := dfa_inter_closure M Dnz
  apply ppl073_minsky_papert_msd_canonical k (m * 3) hk P
  ext w
  rw [hP, heq, hDnz_acc]
  change (Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)) ∧ (∀ d ∈ w.head?, d.val ≠ 0)) ↔
    ((∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)))
  tauto

/-- **MSD ↔ LSD Prime-Acceptance Equivalence (`∀ k ≥ 2`):**
For every `m`-state base-`k` DFA `M`, there exists a `(2 ^ m)`-state DFA `D` whose LSD-first
prime acceptance is equivalent to `M`'s MSD-first prime acceptance (and symmetrically). -/
theorem ppl073_msd_lsd_prime_acceptance_equiv (k m : ℕ) (M : DFA (Fin k) (Fin m)) :
    (∃ D : DFA (Fin k) (Fin (2 ^ m)),
      (∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) ↔
      (∃ w ∈ D.accepts, Nat.Prime (Nat.ofDigits k (w.map Fin.val)))) ∧
    (∃ D : DFA (Fin k) (Fin (2 ^ m)),
      (∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits k (w.map Fin.val))) ↔
      (∃ w ∈ D.accepts, Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)))) := by
  obtain ⟨D, hD⟩ := dfa_reversal_closure M
  refine ⟨⟨D, ?_⟩, ⟨D, ?_⟩⟩
  · constructor
    · rintro ⟨w, hw, hp⟩
      exact ⟨w.reverse, (hD w.reverse).mpr (by simpa using hw), hp⟩
    · rintro ⟨w, hw, hp⟩
      exact ⟨w.reverse, (hD w).mp hw, by simpa using hp⟩
  · constructor
    · rintro ⟨w, hw, hp⟩
      exact ⟨w.reverse, (hD w.reverse).mpr (by simpa using hw), by simpa using hp⟩
    · rintro ⟨w, hw, hp⟩
      exact ⟨w.reverse, (hD w).mp hw, hp⟩

/-- **Minsky–Papert Non-Regularity Theorem (Arbitrary-Trailing-Zero LSD-First, `∀ k ≥ 2`):**
The base-`k` LSD-first prime language is not regular. -/
theorem ppl073_minsky_papert_lsd_all (k m : ℕ) (hk : 2 ≤ k) (M : DFA (Fin k) (Fin m)) :
    M.accepts ≠ { w : List (Fin k) | Nat.Prime (Nat.ofDigits k (w.map Fin.val)) } := by
  intro heq
  obtain ⟨D, hD⟩ := dfa_reversal_closure M
  apply ppl073_minsky_papert_msd_all k (2 ^ m) hk D
  ext w
  rw [hD, heq]
  rfl

/-- **Minsky–Papert Non-Regularity Theorem (Canonical LSD-First, `∀ k ≥ 2`):**
The canonical (no trailing zero) base-`k` LSD-first prime language is not regular. -/
theorem ppl073_minsky_papert_lsd_canonical (k m : ℕ) (hk : 2 ≤ k) (M : DFA (Fin k) (Fin m)) :
    M.accepts ≠
      { w : List (Fin k) |
        (∀ d ∈ w.getLast?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.map Fin.val)) } := by
  intro heq
  obtain ⟨D, hD⟩ := dfa_reversal_closure M
  apply ppl073_minsky_papert_msd_canonical k (2 ^ m) hk D
  ext w
  rw [hD, heq]
  change ((∀ d ∈ w.reverse.getLast?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) ↔
    ((∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)))
  rw [List.getLast?_reverse]

/-! ### Section 2: Explicit Modular & Periodic-Suffix Decidable Subclasses (Dirichlet AP) -/

/-- **Exact `M`-State MSD-First Modular DFA:**
For every base `k ≥ 2`, modulus `M ≥ 1`, and residue `r : Fin M`, there exists an exact
`M`-state base-`k` DFA accepting `{ w | val_msd(w) ≡ r [MOD M] }`. -/
theorem ppl073_mod_dfa_msd (k M : ℕ) (hM : 1 ≤ M) (r : Fin M) :
    ∃ D : DFA (Fin k) (Fin M),
      ∀ w : List (Fin k),
        w ∈ D.accepts ↔ Nat.ofDigits k (w.reverse.map Fin.val) ≡ r.val [MOD M] := by
  let D : DFA (Fin k) (Fin M) := {
    step := fun q d => ⟨(k * q.val + d.val) % M, Nat.mod_lt _ (by omega)⟩
    start := ⟨0, by omega⟩
    accept := {r}
  }
  have heval : ∀ (w : List (Fin k)) (q : Fin M),
      (D.evalFrom q w).val =
        (q.val * k ^ w.length + Nat.ofDigits k (w.reverse.map Fin.val)) % M := by
    intro w
    induction w with
    | nil =>
      intro q
      simp [DFA.evalFrom, Nat.mod_eq_of_lt q.isLt]
    | cons d tl ih =>
      intro q
      rw [dfa_evalFrom_cons_aux, ih, ofDigits_cons_msd]
      change (((k * q.val + d.val) % M) * k ^ tl.length +
        Nat.ofDigits k (tl.reverse.map Fin.val)) % M =
        (q.val * k ^ (tl.length + 1) +
          (Nat.ofDigits k (tl.reverse.map Fin.val) + k ^ tl.length * d.val)) % M
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      congr 1
      rw [pow_succ']
      ring
  refine ⟨D, fun w => ?_⟩
  change D.evalFrom D.start w ∈ ({r} : Set (Fin M)) ↔ _
  rw [Set.mem_singleton_iff, Fin.ext_iff, heval w D.start]
  simp only [D, zero_mul, zero_add, Nat.ModEq, Nat.mod_eq_of_lt r.isLt]

/-- **Exact `(M * M)`-State LSD-First Modular DFA:**
For every base `k ≥ 2`, modulus `M ≥ 1`, and residue `r : Fin M`, there exists an `(M * M)`-state
base-`k` DFA accepting `{ w | val_lsd(w) ≡ r [MOD M] }` by tracking `(rem, k^i mod M)`. -/
theorem ppl073_mod_dfa_lsd (k M : ℕ) (hM : 1 ≤ M) (r : Fin M) :
    ∃ D : DFA (Fin k) (Fin (M * M)),
      ∀ w : List (Fin k),
        w ∈ D.accepts ↔ Nat.ofDigits k (w.map Fin.val) ≡ r.val [MOD M] := by
  let e := finProdFinEquiv (m := M) (n := M)
  let Dp : DFA (Fin k) (Fin M × Fin M) := {
    step := fun qp d =>
      (⟨(qp.1.val + d.val * qp.2.val) % M, Nat.mod_lt _ (by omega)⟩,
       ⟨(qp.2.val * k) % M, Nat.mod_lt _ (by omega)⟩)
    start := (⟨0, by omega⟩, ⟨1 % M, Nat.mod_lt _ (by omega)⟩)
    accept := { qp | qp.1 = r }
  }
  have heval : ∀ (w : List (Fin k)) (qp : Fin M × Fin M),
      (Dp.evalFrom qp w).1.val =
        (qp.1.val + qp.2.val * Nat.ofDigits k (w.map Fin.val)) % M := by
    intro w
    induction w with
    | nil =>
      intro qp
      simp [DFA.evalFrom, Nat.mod_eq_of_lt qp.1.isLt]
    | cons d tl ih =>
      intro qp
      rw [dfa_evalFrom_cons_aux, ih]
      change (((qp.1.val + d.val * qp.2.val) % M) +
        ((qp.2.val * k) % M) * Nat.ofDigits k (tl.map Fin.val)) % M =
        (qp.1.val + qp.2.val * (d.val + k * Nat.ofDigits k (tl.map Fin.val))) % M
      rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      congr 1
      ring
  let D : DFA (Fin k) (Fin (M * M)) := {
    step := fun s d => e (Dp.step (e.symm s) d)
    start := e Dp.start
    accept := e '' Dp.accept
  }
  have hD_eval : ∀ (w : List (Fin k)) (qp : Fin M × Fin M),
      D.evalFrom (e qp) w = e (Dp.evalFrom qp w) := by
    intro w
    induction w with
    | nil => intro qp; rfl
    | cons d tl ih =>
      intro qp
      rw [dfa_evalFrom_cons_aux, dfa_evalFrom_cons_aux]
      change D.evalFrom (e (Dp.step (e.symm (e qp)) d)) tl = _
      rw [Equiv.symm_apply_apply]
      exact ih (Dp.step qp d)
  refine ⟨D, fun w => ?_⟩
  change D.evalFrom (e Dp.start) w ∈ e '' Dp.accept ↔ _
  rw [hD_eval w Dp.start, e.injective.mem_set_image]
  change (Dp.evalFrom Dp.start w).1 = r ↔ _
  rw [Fin.ext_iff, heval w Dp.start]
  simp only [Dp, zero_add, Nat.ModEq, Nat.mod_eq_of_lt r.isLt]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, one_mul]

/-- **Dirichlet Coprime Residue Class Infinitely-Many-Primes Theorem:**
For any base `k ≥ 2`, modulus `M ≥ 1`, residue `r` coprime to `M`, and any DFA `D` that accepts
every canonical base-`k` word congruent to `r (mod M)`, `D` accepts infinitely many distinct
primes (with canonical base-`k` MSD representations). -/
theorem ppl073_coprime_residue_infinitely_many_primes_msd (k m M r : ℕ) (hk : 2 ≤ k)
    (hM : 1 ≤ M) (hcop : Nat.Coprime r M) (D : DFA (Fin k) (Fin m))
    (hsub : ∀ w : List (Fin k),
      (∀ d ∈ w.head?, d.val ≠ 0) →
      Nat.ofDigits k (w.reverse.map Fin.val) ≡ r [MOD M] →
      w ∈ D.accepts) :
    { p : ℕ | Nat.Prime p ∧
      ∃ w ∈ D.accepts,
        (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.ofDigits k (w.reverse.map Fin.val) = p }.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  have hM_ne : M ≠ 0 := by omega
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N hM_ne hcop
  obtain ⟨w, hw_head, hw_val⟩ := exists_canonical_digits_msd hk p hp_prime.one_le
  have hw_acc : w ∈ D.accepts := hsub w hw_head (hw_val.symm ▸ hp_mod)
  exact ⟨p, ⟨hp_prime, w, hw_acc, hw_head, hw_val⟩, hp_gt⟩

/-- **Explicit Prefix DFA (`w.length + 2` states):**
For any alphabet `Fin k` and word `w : List (Fin k)`, there exists a `(w.length + 2)`-state DFA
recognizing `w · Σ_k^* = { u | ∃ v, u = w ++ v }`. -/
theorem ppl073_prefix_dfa_exists (k : ℕ) (w : List (Fin k)) :
    ∃ D : DFA (Fin k) (Fin (w.length + 2)),
      ∀ u : List (Fin k), u ∈ D.accepts ↔ ∃ v : List (Fin k), u = w ++ v := by
  let D : DFA (Fin k) (Fin (w.length + 2)) := {
    step := fun q d =>
      if q.val = w.length then ⟨w.length, by omega⟩
      else if h : q.val < w.length then
        if d = w[q.val] then ⟨q.val + 1, by omega⟩ else ⟨w.length + 1, by omega⟩
      else ⟨w.length + 1, by omega⟩
    start := ⟨0, by omega⟩
    accept := {⟨w.length, by omega⟩}
  }
  have hsink_acc : ∀ v : List (Fin k),
      D.evalFrom ⟨w.length, by omega⟩ v = ⟨w.length, by omega⟩ := by
    intro v
    induction v with
    | nil => rfl
    | cons a tl ih =>
      rw [dfa_evalFrom_cons_aux]
      have hs : D.step ⟨w.length, by omega⟩ a = ⟨w.length, by omega⟩ := by simp [D]
      rw [hs]
      exact ih
  have hsink_dead : ∀ v : List (Fin k),
      D.evalFrom ⟨w.length + 1, by omega⟩ v = ⟨w.length + 1, by omega⟩ := by
    intro v
    induction v with
    | nil => rfl
    | cons a tl ih =>
      rw [dfa_evalFrom_cons_aux]
      have hs : D.step ⟨w.length + 1, by omega⟩ a = ⟨w.length + 1, by omega⟩ := by
        simp [D]
      rw [hs]
      exact ih
  have heval_iff : ∀ (u : List (Fin k)) (i : ℕ) (hi : i ≤ w.length),
      D.evalFrom ⟨i, by omega⟩ u = ⟨w.length, by omega⟩ ↔ ∃ v : List (Fin k), u = w.drop i ++ v := by
    intro u
    induction u with
    | nil =>
      intro i hi
      simp only [DFA.evalFrom, List.foldl_nil, Fin.ext_iff]
      constructor
      · intro h
        refine ⟨[], ?_⟩
        rw [List.append_nil, h, List.drop_length]
      · rintro ⟨v, hv⟩
        have hlen := congrArg List.length hv
        simp only [List.length_nil, List.length_append, List.length_drop] at hlen
        omega
    | cons a tl ih =>
      intro i hi
      by_cases heq : i = w.length
      · subst heq
        rw [hsink_acc]
        simp only [List.drop_length, List.nil_append, true_iff]
        exact ⟨a :: tl, rfl⟩
      · have hlt : i < w.length := by omega
        rw [dfa_evalFrom_cons_aux]
        have hdrop : w.drop i = w[i] :: w.drop (i + 1) := List.drop_eq_getElem_cons hlt
        by_cases ha : a = w[i]
        · have hs : D.step ⟨i, by omega⟩ a = ⟨i + 1, by omega⟩ := by
            simp [D, heq, hlt, ha]
          rw [hs, ih (i + 1) (by omega), ha, hdrop]
          constructor
          · rintro ⟨v, rfl⟩
            exact ⟨v, rfl⟩
          · rintro ⟨v, hv⟩
            simp only [List.cons_append, List.cons.injEq] at hv
            exact ⟨v, hv.2⟩
        · have hs : D.step ⟨i, by omega⟩ a = ⟨w.length + 1, by omega⟩ := by
            simp [D, heq, hlt, ha]
          rw [hs, hsink_dead, hdrop]
          constructor
          · intro h
            have := congrArg Fin.val h
            simp at this
          · rintro ⟨v, hv⟩
            simp only [List.cons_append, List.cons.injEq] at hv
            exact (ha hv.1).elim
  refine ⟨D, fun u => ?_⟩
  change D.evalFrom ⟨0, by omega⟩ u ∈ ({⟨w.length, by omega⟩} : Set _) ↔ _
  rw [Set.mem_singleton_iff, heval_iff u 0 (Nat.zero_le _), List.drop_zero]

/-- **Periodic-Suffix DFA & Coprime-Suffix Infinitely-Many-Primes Theorem (`Σ_k^* · u`):**
For any base `k ≥ 2` and suffix `u : List (Fin k)` with `Nat.Coprime (val_msd u) k`:
1. There exists an explicit `(2 ^ (u.length + 2))`-state DFA `D` recognizing `Σ_k^* · u`;
2. Every DFA whose language contains `Σ_k^* · u` accepts infinitely many distinct primes
   (with canonical base-`k` MSD representations). -/
theorem ppl073_coprime_suffix_dfa_infinitely_many_primes_msd (k : ℕ) (hk : 2 ≤ k)
    (u : List (Fin k))
    (hcop : Nat.Coprime (Nat.ofDigits k (u.reverse.map Fin.val)) k) :
    (∃ D : DFA (Fin k) (Fin (2 ^ (u.length + 2))),
      ∀ w : List (Fin k), w ∈ D.accepts ↔ ∃ v : List (Fin k), w = v ++ u) ∧
    (∀ (m : ℕ) (M : DFA (Fin k) (Fin m)),
      (∀ v : List (Fin k), v ++ u ∈ M.accepts) →
      { p : ℕ | Nat.Prime p ∧
        ∃ w ∈ M.accepts,
          (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.ofDigits k (w.reverse.map Fin.val) = p }.Infinite) := by
  constructor
  · have hex : ∃ D : DFA (Fin k) (Fin (2 ^ (u.reverse.length + 2))),
        ∀ w : List (Fin k), w ∈ D.accepts ↔ ∃ v : List (Fin k), w = v ++ u := by
      obtain ⟨P, hP⟩ := ppl073_prefix_dfa_exists k u.reverse
      obtain ⟨D, hD⟩ := dfa_reversal_closure P
      refine ⟨D, fun w => ?_⟩
      rw [hD, hP]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v.reverse, ?_⟩
        have := congrArg List.reverse hv
        simpa [List.reverse_append] using this
      · rintro ⟨v, hv⟩
        refine ⟨v.reverse, ?_⟩
        rw [hv, List.reverse_append]
    have hrev : u.reverse.length = u.length := List.length_reverse
    rw [← hrev]
    exact hex
  · intro m M hsub
    rw [Set.infinite_iff_exists_gt]
    intro N
    set Q := k ^ u.length with hQ_def
    have hQ_ne : Q ≠ 0 := (pow_pos (by omega : 0 < k) u.length).ne'
    have hcopQ : Nat.Coprime (Nat.ofDigits k (u.reverse.map Fin.val)) Q :=
      hcop.pow_right u.length
    obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq (max N Q) hQ_ne hcopQ
    have hp_ge_Q : Q ≤ p := le_trans (le_max_right N Q) (Nat.le_of_lt hp_gt)
    obtain ⟨v, hv_head, hv_val⟩ := exists_canonical_digits_with_suffix_msd hk u p hp_ge_Q hp_mod
    exact ⟨p, ⟨hp_prime, v ++ u, hsub v, hv_head, hv_val⟩, lt_of_le_of_lt (le_max_left N Q) hp_gt⟩

/-- **Exact Bounded-Length Decidability Reduction for Finite-Language DFAs:**
If `M : DFA (Fin k) (Fin m)` accepts a finite language (`M.accepts.Finite`), then every word
in `M.accepts` has length `< m`. Hence `M` accepts a prime if and only if `M` accepts a prime
word of length `< m` (reducing prime acceptance to a finite check over words of length `< m`). -/
theorem ppl073_finite_dfa_prime_iff_bounded (k m : ℕ) (M : DFA (Fin k) (Fin m))
    (hfin : M.accepts.Finite) :
    (∀ w ∈ M.accepts, w.length < m) ∧
    ((∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) ↔
      (∃ w : List (Fin k), w.length < m ∧ w ∈ M.accepts ∧
        Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val)))) := by
  have hbound : ∀ w ∈ M.accepts, w.length < m := by
    intro w hw
    by_contra hge
    push Not at hge
    obtain ⟨x, y, z, _, _, hy_pos, hpump⟩ := dfa_pumping_lemma M w hw hge
    have hinj : Function.Injective (fun n : ℕ => x ++ (List.replicate n y).flatten ++ z) := by
      intro a b hab
      have hlen := congrArg List.length hab
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul] at hlen
      have hmul : a * y.length = b * y.length := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) hmul
    have hinf : (Set.range (fun n : ℕ => x ++ (List.replicate n y).flatten ++ z)).Infinite :=
      Set.infinite_range_of_injective hinj
    have hsub : Set.range (fun n : ℕ => x ++ (List.replicate n y).flatten ++ z) ⊆ M.accepts := by
      rintro _ ⟨n, rfl⟩
      exact hpump n
    exact hinf (hfin.subset hsub)
  refine ⟨hbound, ?_⟩
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hbound w hw, hw, hp⟩
  · rintro ⟨w, _, hw, hp⟩
    exact ⟨w, hw, hp⟩

/-- **Exact Finite-Checkable Decidability Criterion for Congruence-Closed DFAs:**
Suppose `k ≥ 2`, `q ≥ 1`, and `M : DFA (Fin k) (Fin m)` is congruence-closed modulo `q` on
canonical base-`k` words via a residue set `S : Finset (Fin q)`. Then `M` accepts a canonical
prime **if and only if** either:
- some residue `r ∈ S` is coprime to `q` (in which case `M` accepts infinitely many primes), or
- some prime divisor `p ∈ Finset.Icc 2 q` of `q` has `p % q ∈ S`. -/
theorem ppl073_congruence_dfa_prime_iff (k m q : ℕ) (hk : 2 ≤ k) (hq : 1 ≤ q)
    (M : DFA (Fin k) (Fin m)) (S : Finset (Fin q))
    (hcong : ∀ w : List (Fin k), (∀ d ∈ w.head?, d.val ≠ 0) →
      (w ∈ M.accepts ↔
        ⟨Nat.ofDigits k (w.reverse.map Fin.val) % q, Nat.mod_lt _ (by omega)⟩ ∈ S)) :
    (∃ w ∈ M.accepts,
      (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) ↔
      ((∃ r ∈ S, Nat.Coprime r.val q) ∨
        (∃ p ∈ Finset.Icc 2 q, Nat.Prime p ∧ p ∣ q ∧ ⟨p % q, Nat.mod_lt p (by omega)⟩ ∈ S)) := by
  constructor
  · rintro ⟨w, hw_acc, hw_head, hp⟩
    set p := Nat.ofDigits k (w.reverse.map Fin.val)
    have hr_mem : (⟨p % q, Nat.mod_lt p (by omega)⟩ : Fin q) ∈ S := (hcong w hw_head).mp hw_acc
    by_cases hdvd : p ∣ q
    · right
      refine ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_of_dvd (by omega) hdvd⟩, hp, hdvd, hr_mem⟩
    · left
      have hcop_pq : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr hdvd
      have hcop_mod : Nat.Coprime (p % q) q := by
        rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hcop_pq
      exact ⟨⟨p % q, Nat.mod_lt p (by omega)⟩, hr_mem, hcop_mod⟩
  · rintro (⟨r, hrS, hcop⟩ | ⟨p, _, hp, _, hpS⟩)
    · have hq_ne : q ≠ 0 := by omega
      obtain ⟨p, _, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hq_ne hcop
      obtain ⟨w, hw_head, hw_val⟩ := exists_canonical_digits_msd hk p hp.one_le
      have hrem : (⟨Nat.ofDigits k (w.reverse.map Fin.val) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = r := by
        apply Fin.ext
        dsimp only
        rw [hw_val]
        rw [Nat.ModEq] at hmod
        rw [hmod, Nat.mod_eq_of_lt r.isLt]
      have hw_acc : w ∈ M.accepts := (hcong w hw_head).mpr (hrem ▸ hrS)
      exact ⟨w, hw_acc, hw_head, hw_val.symm ▸ hp⟩
    · obtain ⟨w, hw_head, hw_val⟩ := exists_canonical_digits_msd hk p hp.one_le
      have hrem : (⟨Nat.ofDigits k (w.reverse.map Fin.val) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) =
          ⟨p % q, Nat.mod_lt p (by omega)⟩ := by
        apply Fin.ext
        dsimp only
        rw [hw_val]
      have hw_acc : w ∈ M.accepts := (hcong w hw_head).mpr (hrem ▸ hpS)
      exact ⟨w, hw_acc, hw_head, hw_val.symm ▸ hp⟩

/-- **Finite-vs-Infinite Prime Dichotomy for Congruence-Closed DFAs:**
Under the same congruence-closed hypothesis modulo `q`, the set of canonical primes accepted by
`M` is **infinite** if and only if `S` contains a residue coprime to `q`. -/
theorem ppl073_congruence_dfa_dichotomy (k m q : ℕ) (hk : 2 ≤ k) (hq : 1 ≤ q)
    (M : DFA (Fin k) (Fin m)) (S : Finset (Fin q))
    (hcong : ∀ w : List (Fin k), (∀ d ∈ w.head?, d.val ≠ 0) →
      (w ∈ M.accepts ↔
        ⟨Nat.ofDigits k (w.reverse.map Fin.val) % q, Nat.mod_lt _ (by omega)⟩ ∈ S)) :
    { p : ℕ | Nat.Prime p ∧
      ∃ w ∈ M.accepts,
        (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.ofDigits k (w.reverse.map Fin.val) = p }.Infinite ↔
      (∃ r ∈ S, Nat.Coprime r.val q) := by
  constructor
  · intro hinf
    by_contra hno
    push Not at hno
    have hsub :
        { p : ℕ | Nat.Prime p ∧
          ∃ w ∈ M.accepts,
            (∀ d ∈ w.head?, d.val ≠ 0) ∧ Nat.ofDigits k (w.reverse.map Fin.val) = p } ⊆
          { p : ℕ | p ≤ q } := by
      rintro p ⟨hp, w, hw_acc, hw_head, hw_val⟩
      have hr_mem : (⟨p % q, Nat.mod_lt p (by omega)⟩ : Fin q) ∈ S := by
        have h := (hcong w hw_head).mp hw_acc
        have hrem : (⟨Nat.ofDigits k (w.reverse.map Fin.val) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) =
            ⟨p % q, Nat.mod_lt p (by omega)⟩ := by
          apply Fin.ext
          dsimp only
          rw [hw_val]
        exact hrem ▸ h
      have hnotcop : ¬ Nat.Coprime (p % q) q := hno ⟨p % q, Nat.mod_lt p (by omega)⟩ hr_mem
      have hnotcop_pq : ¬ Nat.Coprime p q := by
        intro hc
        apply hnotcop
        rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hc
      have hdvd : p ∣ q := by
        by_contra hndvd
        exact hnotcop_pq ((hp.coprime_iff_not_dvd).mpr hndvd)
      exact Nat.le_of_dvd (by omega) hdvd
    exact hinf ((Set.finite_le_nat q).subset hsub)
  · rintro ⟨r, hrS, hcop⟩
    apply ppl073_coprime_residue_infinitely_many_primes_msd k m q r.val hk hq hcop M
    intro w hw_head hmod
    apply (hcong w hw_head).mpr
    have heq : (⟨Nat.ofDigits k (w.reverse.map Fin.val) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = r := by
      apply Fin.ext
      dsimp only
      rw [Nat.ModEq] at hmod
      rw [hmod, Nat.mod_eq_of_lt r.isLt]
    rw [heq]
    exact hrS

/-! ### Section 3: Leading-Prefix / Short-Interval Prime Acceptance (`w · Σ_k^*`) -/

/-- **Leading-Prefix Eventual Prime Existence (`w · Σ_k^*`, via Tier A PNT Short Intervals):**
For every base `k ≥ 2` and every base-`k` prefix `w` representing a nonzero integer, for all
sufficiently large extension lengths `t`, there exists a suffix `v` of length `t` such that
`w ++ v` represents a prime number (and inherits no-leading-zero from `w`). -/
theorem ppl073_prefix_eventually_has_prime (k : ℕ) (hk : 2 ≤ k) (w : List (Fin k))
    (hw_nz : Nat.ofDigits k (w.reverse.map Fin.val) ≠ 0) :
    ∀ᶠ t : ℕ in atTop,
      ∃ v : List (Fin k), v.length = t ∧
        Nat.Prime (Nat.ofDigits k ((w ++ v).reverse.map Fin.val)) := by
  set N := Nat.ofDigits k (w.reverse.map Fin.val) with hN_def
  have hN_pos : 1 ≤ N := Nat.pos_of_ne_zero hw_nz
  have hN_rpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  obtain ⟨X₀, hshort⟩ := RHDirect.Stage8ExplicitPrimeBounds.exists_prime_in_Ioc_polylog 1 zero_lt_one
  set B : ℝ := max (max X₀ (Real.exp (2 * (N : ℝ)))) 4 with hB_def
  -- Since `k ≥ 2`, `k ^ t ≥ t + 1`, so `N * k ^ t ≥ t + 1`.
  let T₀ : ℕ := Nat.ceil B + 1
  rw [Filter.eventually_atTop]
  refine ⟨T₀, fun t ht => ?_⟩
  have hkt_ge : t + 1 ≤ k ^ t := by
    calc t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
      _ ≤ k ^ t := Nat.pow_le_pow_left hk t
  have hx_ge_B : B ≤ ((N * k ^ t : ℕ) : ℝ) := by
    have hceil : B ≤ (T₀ : ℝ) := by
      have h1 : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
      have h2 : (Nat.ceil B : ℝ) ≤ (T₀ : ℝ) := by
        simp only [T₀, Nat.cast_add, Nat.cast_one]
        linarith
      linarith
    have hnat : T₀ ≤ N * k ^ t := by
      calc T₀ ≤ t := ht
        _ ≤ t + 1 := Nat.le_succ t
        _ ≤ k ^ t := hkt_ge
        _ = 1 * k ^ t := (one_mul _).symm
        _ ≤ N * k ^ t := Nat.mul_le_mul_right _ hN_pos
    exact hceil.trans (by exact_mod_cast hnat)
  set x : ℝ := ((N * k ^ t : ℕ) : ℝ) with hx_def
  have hx_ge_X0 : X₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx_ge_B
  have hx_ge_exp : Real.exp (2 * (N : ℝ)) ≤ x :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hx_ge_B
  obtain ⟨p, hp_prime, hxp, hp_le⟩ := hshort x hx_ge_X0
  have hlog_ge : 2 * (N : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp (2 * (N : ℝ))]
    exact Real.log_le_log (Real.exp_pos _) hx_ge_exp
  have hlog_pos : 0 < Real.log x := by linarith
  have hdiv_lt : x / (Real.log x) ^ (1 : ℝ) < ((k ^ t : ℕ) : ℝ) := by
    rw [Real.rpow_one, div_lt_iff₀ hlog_pos]
    have hx_eq : x = (N : ℝ) * ((k ^ t : ℕ) : ℝ) := by
      rw [hx_def, Nat.cast_mul]
    have hkt_pos : (0 : ℝ) < ((k ^ t : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (by omega : 0 < k) t
    have hN_lt_log : (N : ℝ) < Real.log x := by linarith
    calc x = (N : ℝ) * ((k ^ t : ℕ) : ℝ) := hx_eq
      _ < Real.log x * ((k ^ t : ℕ) : ℝ) := mul_lt_mul_of_pos_right hN_lt_log hkt_pos
      _ = ((k ^ t : ℕ) : ℝ) * Real.log x := mul_comm _ _
  have hp_lt_real : (p : ℝ) < (((N + 1) * k ^ t : ℕ) : ℝ) := by
    have hrhs : (((N + 1) * k ^ t : ℕ) : ℝ) = x + ((k ^ t : ℕ) : ℝ) := by
      rw [hx_def]
      push_cast
      ring
    linarith
  have hp_ge_nat : N * k ^ t ≤ p := by
    have hlt_r : ((N * k ^ t : ℕ) : ℝ) < (p : ℝ) := hxp
    exact Nat.le_of_lt (by exact_mod_cast hlt_r)
  have hp_lt_nat : p < (N + 1) * k ^ t := by exact_mod_cast hp_lt_real
  set r := p - N * k ^ t with hr_def
  have hr_lt : r < k ^ t := by
    have : (N + 1) * k ^ t = N * k ^ t + k ^ t := by ring
    omega
  obtain ⟨v, hv_len, hv_val⟩ := exists_fixed_len_digits_msd hk t r hr_lt
  refine ⟨v, hv_len, ?_⟩
  have hval : Nat.ofDigits k ((w ++ v).reverse.map Fin.val) = p := by
    rw [ofDigits_append_msd, hv_len, hv_val, ← hN_def, mul_comm (k ^ t) N]
    omega
  rwa [hval]

/-- **Leading-Prefix Infinitely-Many-Primes Theorem (`w · Σ_k^*`):**
For every base `k ≥ 2`, every nonzero base-`k` prefix `w`, and every DFA `M` whose accepted
language contains `w · Σ_k^*`, `M` accepts infinitely many distinct primes. -/
theorem ppl073_prefix_infinitely_many_primes (k m : ℕ) (hk : 2 ≤ k) (w : List (Fin k))
    (hw_nz : Nat.ofDigits k (w.reverse.map Fin.val) ≠ 0)
    (M : DFA (Fin k) (Fin m)) (hsub : ∀ v : List (Fin k), w ++ v ∈ M.accepts) :
    { p : ℕ | Nat.Prime p ∧
      ∃ u ∈ M.accepts, Nat.ofDigits k (u.reverse.map Fin.val) = p }.Infinite := by
  have hev := ppl073_prefix_eventually_has_prime k hk w hw_nz
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  rw [Set.infinite_iff_exists_gt]
  intro B
  let t := max T₀ B
  obtain ⟨v, hv_len, hv_prime⟩ := hT₀ t (le_max_left T₀ B)
  set p := Nat.ofDigits k ((w ++ v).reverse.map Fin.val) with hp_def
  have hp_gt : B < p := by
    have hval_ge : k ^ t ≤ p := by
      rw [hp_def, ofDigits_append_msd, hv_len]
      have hN1 : 1 ≤ Nat.ofDigits k (w.reverse.map Fin.val) := Nat.pos_of_ne_zero hw_nz
      calc k ^ t = k ^ t * 1 := (mul_one _).symm
        _ ≤ k ^ t * Nat.ofDigits k (w.reverse.map Fin.val) := Nat.mul_le_mul_left _ hN1
        _ ≤ Nat.ofDigits k (v.reverse.map Fin.val) +
            k ^ t * Nat.ofDigits k (w.reverse.map Fin.val) := Nat.le_add_left _ _
    have hkt_gt : t < k ^ t := by
      calc t < 2 ^ t := Nat.lt_two_pow_self
        _ ≤ k ^ t := Nat.pow_le_pow_left hk t
    have hBt : B ≤ t := le_max_right T₀ B
    omega
  exact ⟨p, ⟨hv_prime, w ++ v, hsub v, rfl⟩, hp_gt⟩

/-! ### Section 4: Explicit Sparse-Automaton Barriers (Repunit, Mersenne, Fermat & Missing-Digit DFAs) -/

/-- **General Base-`k` Repunit Barrier DFA (`(n₀ + 3)` states; `3` states at `n₀ = 0`):**
For every base `k ≥ 2` and cutoff `n₀ : ℕ`, there exists an `(n₀ + 3)`-state base-`k` DFA `M`
accepting `{ 1^n | n > n₀ }`, whose prime acceptance is **provably equivalent** to the existence
of a base-`k` repunit prime `(k^n - 1) / (k - 1)` with `n > n₀`. -/
theorem ppl073_repunit_barrier_dfa (k n₀ : ℕ) (hk : 2 ≤ k) :
    ∃ M : DFA (Fin k) (Fin (n₀ + 3)),
      (∀ w : List (Fin k),
        w ∈ M.accepts ↔ ∃ n : ℕ, n₀ < n ∧ w = List.replicate n ⟨1, by omega⟩) ∧
      ((∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) ↔
        (∃ n : ℕ, n₀ < n ∧ Nat.Prime ((k ^ n - 1) / (k - 1)))) := by
  let one : Fin k := ⟨1, by omega⟩
  let M : DFA (Fin k) (Fin (n₀ + 3)) := {
    step := fun q d =>
      if d = one then
        if hq : q.val ≤ n₀ then ⟨q.val + 1, by omega⟩
        else if q.val = n₀ + 1 then ⟨n₀ + 1, by omega⟩
        else ⟨n₀ + 2, by omega⟩
      else ⟨n₀ + 2, by omega⟩
    start := ⟨0, by omega⟩
    accept := {⟨n₀ + 1, by omega⟩}
  }
  have hdead : ∀ u : List (Fin k),
      M.evalFrom ⟨n₀ + 2, by omega⟩ u = ⟨n₀ + 2, by omega⟩ := by
    intro u
    induction u with
    | nil => rfl
    | cons a tl ih =>
      rw [dfa_evalFrom_cons_aux]
      have hs : M.step ⟨n₀ + 2, by omega⟩ a = ⟨n₀ + 2, by omega⟩ := by
        dsimp only [M]
        split_ifs <;> first | rfl | omega
      rw [hs]
      exact ih
  have heval_iff : ∀ (u : List (Fin k)) (i : ℕ) (hi : i ≤ n₀ + 1),
      M.evalFrom ⟨i, by omega⟩ u = ⟨n₀ + 1, by omega⟩ ↔
        ∃ m : ℕ, n₀ + 1 - i ≤ m ∧ u = List.replicate m one := by
    intro u
    induction u with
    | nil =>
      intro i hi
      simp only [DFA.evalFrom, List.foldl_nil, Fin.ext_iff]
      constructor
      · intro h
        exact ⟨0, by omega, rfl⟩
      · rintro ⟨m, hm, heq⟩
        have hlen := congrArg List.length heq
        simp at hlen
        omega
    | cons a tl ih =>
      intro i hi
      rw [dfa_evalFrom_cons_aux]
      by_cases ha : a = one
      · subst ha
        by_cases hle : i ≤ n₀
        · have hs : M.step ⟨i, by omega⟩ one = ⟨i + 1, by omega⟩ := by
            simp [M, hle]
          rw [hs, ih (i + 1) (by omega)]
          constructor
          · rintro ⟨m, hm, rfl⟩
            exact ⟨m + 1, by omega, by rw [List.replicate_succ]⟩
          · rintro ⟨m, hm, hrep⟩
            cases m with
            | zero => simp at hrep
            | succ m' =>
              rw [List.replicate_succ, List.cons.injEq] at hrep
              exact ⟨m', by omega, hrep.2⟩
        · have hi_eq : i = n₀ + 1 := by omega
          subst hi_eq
          have hs : M.step ⟨n₀ + 1, by omega⟩ one = ⟨n₀ + 1, by omega⟩ := by
            simp [M]
          rw [hs, ih (n₀ + 1) le_rfl]
          constructor
          · rintro ⟨m, _, rfl⟩
            exact ⟨m + 1, by omega, by rw [List.replicate_succ]⟩
          · rintro ⟨m, _, hrep⟩
            cases m with
            | zero => simp at hrep
            | succ m' =>
              rw [List.replicate_succ, List.cons.injEq] at hrep
              exact ⟨m', by omega, hrep.2⟩
      · have hs : M.step ⟨i, by omega⟩ a = ⟨n₀ + 2, by omega⟩ := by
          simp [M, ha]
        rw [hs, hdead]
        constructor
        · intro h
          have := congrArg Fin.val h
          simp at this
        · rintro ⟨m, _, hrep⟩
          cases m with
          | zero => simp at hrep
          | succ m' =>
            rw [List.replicate_succ, List.cons.injEq] at hrep
            exact (ha hrep.1).elim
  have hlang : ∀ w : List (Fin k),
      w ∈ M.accepts ↔ ∃ n : ℕ, n₀ < n ∧ w = List.replicate n one := by
    intro w
    change M.evalFrom ⟨0, by omega⟩ w ∈ ({⟨n₀ + 1, by omega⟩} : Set _) ↔ _
    rw [Set.mem_singleton_iff, heval_iff w 0 (Nat.zero_le _)]
    constructor
    · rintro ⟨n, hn, hw⟩
      exact ⟨n, by omega, hw⟩
    · rintro ⟨n, hn, hw⟩
      exact ⟨n, by omega, hw⟩
  refine ⟨M, hlang, ?_⟩
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨n, hn, rfl⟩ := (hlang w).mp hw
    refine ⟨n, hn, ?_⟩
    have hval : Nat.ofDigits k ((List.replicate n one).reverse.map Fin.val) =
        (k ^ n - 1) / (k - 1) := by
      rw [List.reverse_replicate, List.map_replicate]
      exact ofDigits_replicate_one_eq k hk n
    rwa [hval] at hp
  · rintro ⟨n, hn, hp⟩
    refine ⟨List.replicate n one, (hlang _).mpr ⟨n, hn, rfl⟩, ?_⟩
    rw [List.reverse_replicate, List.map_replicate, ofDigits_replicate_one_eq k hk n]
    exact hp

/-- **Mersenne Barrier DFA (`(n₀ + 3)` states; `3` states at `n₀ = 0`):**
For every cutoff `n₀ : ℕ`, there exists an `(n₀ + 3)`-state base-2 DFA accepting
`{ 1^n | n > n₀ }`, whose prime acceptance is **provably equivalent** to the existence of a
Mersenne prime `2 ^ n - 1` with `n > n₀`. -/
theorem ppl073_mersenne_barrier_dfa (n₀ : ℕ) :
    ∃ M : DFA (Fin 2) (Fin (n₀ + 3)),
      (∀ w : List (Fin 2),
        w ∈ M.accepts ↔ ∃ n : ℕ, n₀ < n ∧ w = List.replicate n ⟨1, by decide⟩) ∧
      ((∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits 2 (w.reverse.map Fin.val))) ↔
        (∃ n : ℕ, n₀ < n ∧ Nat.Prime (2 ^ n - 1))) := by
  obtain ⟨M, hlang, hprime⟩ := ppl073_repunit_barrier_dfa 2 n₀ le_rfl
  refine ⟨M, hlang, ?_⟩
  simpa using hprime

/-- **Repunit & Mersenne Prime Exponent Theorem:**
For any base `k ≥ 2` and `n ≥ 2`, if the base-`k` repunit `(k ^ n - 1) / (k - 1)` is prime,
then `n` itself must be prime (specializing at `k = 2` to: `2 ^ n - 1` prime implies `n` prime). -/
theorem ppl073_repunit_prime_exponent_prime (k n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hp : Nat.Prime ((k ^ n - 1) / (k - 1))) : Nat.Prime n := by
  by_contra hcomp
  have h1 : n ≠ 1 := by omega
  obtain ⟨a, ha_dvd, ha_gt1, ha_lt⟩ : ∃ a : ℕ, a ∣ n ∧ 1 < a ∧ a < n := by
    have hmp := Nat.minFac_prime h1
    have hle : n.minFac ≤ n := Nat.minFac_le (by omega)
    have hlt : n.minFac < n := lt_of_le_of_ne hle (fun heq => hcomp (heq ▸ hmp))
    exact ⟨n.minFac, Nat.minFac_dvd n, hmp.one_lt, hlt⟩
  rcases ha_dvd with ⟨b, rfl⟩
  have hb_gt1 : 1 < b := by
    by_contra hb
    push Not at hb
    interval_cases b <;> omega
  set R_a := (k ^ a - 1) / (k - 1)
  set R_ab := (k ^ (a * b) - 1) / (k - 1)
  have hRa_mul : (k - 1) * R_a = k ^ a - 1 := by
    dsimp only [R_a]
    rw [← ofDigits_replicate_one_eq k hk a]
    exact ofDigits_replicate_one_mul k hk a
  have hRab_mul : (k - 1) * R_ab = k ^ (a * b) - 1 := by
    dsimp only [R_ab]
    rw [← ofDigits_replicate_one_eq k hk (a * b)]
    exact ofDigits_replicate_one_mul k hk (a * b)
  have hgeom : (k ^ a - 1) * (∑ j ∈ Finset.range b, (k ^ a) ^ j) = k ^ (a * b) - 1 := by
    have hpow_ge : 1 ≤ k ^ a := Nat.one_le_pow a k (by omega)
    have hrec : ∀ m : ℕ, (k ^ a - 1) * (∑ j ∈ Finset.range m, (k ^ a) ^ j) = (k ^ a) ^ m - 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        have hstep : (k ^ a - 1) * (k ^ a) ^ m = (k ^ a) ^ (m + 1) - (k ^ a) ^ m := by
          rw [Nat.sub_mul, one_mul, pow_succ']
        have h1m : 1 ≤ (k ^ a) ^ m := Nat.one_le_pow m _ (by omega)
        have h2m : (k ^ a) ^ m ≤ (k ^ a) ^ (m + 1) := by
          rw [pow_succ']
          exact Nat.le_mul_of_pos_left _ (by omega)
        rw [hstep]
        omega
    simpa [pow_mul] using hrec b
  have hdvd : R_a ∣ R_ab := by
    refine ⟨∑ j ∈ Finset.range b, (k ^ a) ^ j, ?_⟩
    have hmul : (k - 1) * R_ab = (k - 1) * (R_a * ∑ j ∈ Finset.range b, (k ^ a) ^ j) := by
      rw [hRab_mul, ← mul_assoc, hRa_mul, hgeom]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < k - 1) hmul
  have hRa_gt1 : 1 < R_a := by
    have hka : k ^ 2 ≤ k ^ a := Nat.pow_le_pow_right (by omega) ha_gt1
    have hsq : (k - 1) * 2 + 1 ≤ k ^ 2 := by
      have hk2 : k ^ 2 = k * k := sq k
      have hk1 : k - 1 + 1 = k := by omega
      nlinarith
    have hle : (k - 1) * 2 ≤ (k - 1) * R_a := by omega
    have h2 : 2 ≤ R_a := Nat.le_of_mul_le_mul_left hle (by omega)
    omega
  have hRa_lt : R_a < R_ab := by
    have hpow_lt : k ^ a < k ^ (a * b) := Nat.pow_lt_pow_right (by omega) ha_lt
    have h1 : 1 ≤ k ^ a := Nat.one_le_pow a k (by omega)
    have hmul_lt : (k - 1) * R_a < (k - 1) * R_ab := by
      rw [hRa_mul, hRab_mul]
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  rcases hp.eq_one_or_self_of_dvd R_a hdvd with h_eq1 | h_eqself
  · omega
  · omega

private lemma exists_two_pow_mul_odd :
    ∀ n : ℕ, 1 ≤ n → ∃ m u : ℕ, Odd u ∧ n = 2 ^ m * u := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases heven : 2 ∣ n
    · rcases heven with ⟨q, rfl⟩
      have hq_pos : 1 ≤ q := by omega
      have hq_lt : q < 2 * q := by omega
      obtain ⟨m, u, hu, hq_eq⟩ := ih q hq_lt hq_pos
      exact ⟨m + 1, u, hu, by rw [hq_eq, pow_succ']; ring⟩
    · refine ⟨0, n, ?_, by simp⟩
      exact Nat.odd_iff.mpr (by omega)

private lemma prime_two_pow_add_one_is_fermat (n : ℕ) (hn : 1 ≤ n)
    (hp : Nat.Prime (2 ^ n + 1)) : ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨m, u, hu_odd, rfl⟩ := exists_two_pow_mul_odd n hn
  by_cases hu1 : u = 1
  · exact ⟨m, by simp [hu1]⟩
  · exfalso
    have hu_ge3 : 3 ≤ u := by
      rcases hu_odd with ⟨j, rfl⟩
      omega
    set d := 2 ^ (2 ^ m) + 1 with hd_def
    have hd_gt1 : 1 < d := by
      have : 1 ≤ 2 ^ (2 ^ m) := Nat.one_le_pow _ 2 (by decide)
      omega
    have hd_lt : d < 2 ^ (2 ^ m * u) + 1 := by
      have hlt : 2 ^ m < 2 ^ m * u := lt_mul_of_one_lt_right (pow_pos (by decide) m) (by omega)
      have := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
      omega
    have hd_dvd : d ∣ 2 ^ (2 ^ m * u) + 1 := by
      have hmod : (((2 ^ (2 ^ m) : ℕ) : ZMod d)) = -1 := by
        have h0 : ((d : ℕ) : ZMod d) = 0 := ZMod.natCast_self d
        rw [hd_def, Nat.cast_add, Nat.cast_one] at h0
        linear_combination h0
      have hcast : ((2 ^ (2 ^ m * u) + 1 : ℕ) : ZMod d) = 0 := by
        rw [pow_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hmod, hu_odd.neg_one_pow]
        ring
      exact (ZMod.natCast_eq_zero_iff _ d).mp hcast
    rcases hp.eq_one_or_self_of_dvd d hd_dvd with h1 | h2
    · omega
    · omega

/-- **Fermat Barrier DFA (`(n₀ + 4)` states; `4` states at `n₀ = 0`):**
For every cutoff `n₀ : ℕ`, there exists an `(n₀ + 4)`-state base-2 DFA `M` accepting
`1 0^{n₀} 0^* 1` (exact base-2 representations of `{ 2 ^ n + 1 | n > n₀ }`), whose prime
acceptance is **provably equivalent** to the existence of a Fermat prime `2 ^ (2 ^ m) + 1`
with `n₀ < 2 ^ m`. -/
theorem ppl073_fermat_barrier_dfa (n₀ : ℕ) :
    ∃ M : DFA (Fin 2) (Fin (n₀ + 4)),
      (∀ w : List (Fin 2),
        w ∈ M.accepts ↔
          ∃ j : ℕ, n₀ ≤ j ∧
            w = ⟨1, by decide⟩ :: (List.replicate j ⟨0, by decide⟩ ++ [⟨1, by decide⟩])) ∧
      ((∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits 2 (w.reverse.map Fin.val))) ↔
        (∃ m : ℕ, n₀ < 2 ^ m ∧ Nat.Prime (2 ^ (2 ^ m) + 1))) := by
  let z0 : Fin 2 := ⟨0, by decide⟩
  let z1 : Fin 2 := ⟨1, by decide⟩
  let M : DFA (Fin 2) (Fin (n₀ + 4)) := {
    step := fun q d =>
      if q.val = 0 then
        if d = z1 then ⟨1, by omega⟩ else ⟨n₀ + 3, by omega⟩
      else if hq : q.val ≤ n₀ then
        if d = z0 then ⟨q.val + 1, by omega⟩ else ⟨n₀ + 3, by omega⟩
      else if q.val = n₀ + 1 then
        if d = z0 then ⟨n₀ + 1, by omega⟩ else ⟨n₀ + 2, by omega⟩
      else ⟨n₀ + 3, by omega⟩
    start := ⟨0, by omega⟩
    accept := {⟨n₀ + 2, by omega⟩}
  }
  have hdead : ∀ u : List (Fin 2),
      M.evalFrom ⟨n₀ + 3, by omega⟩ u = ⟨n₀ + 3, by omega⟩ := by
    intro u
    induction u with
    | nil => rfl
    | cons a tl ih =>
      rw [dfa_evalFrom_cons_aux]
      have hs : M.step ⟨n₀ + 3, by omega⟩ a = ⟨n₀ + 3, by omega⟩ := by
        dsimp only [M]
        rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega)]
      rw [hs]
      exact ih
  have hfin2_cases : ∀ a : Fin 2, a = z0 ∨ a = z1 := by
    intro a
    fin_cases a <;> simp [z0, z1]
  have hacc_from_accept : ∀ u : List (Fin 2),
      M.evalFrom ⟨n₀ + 2, by omega⟩ u = ⟨n₀ + 2, by omega⟩ ↔ u = [] := by
    intro u
    cases u with
    | nil => simp [DFA.evalFrom]
    | cons a tl =>
      rw [dfa_evalFrom_cons_aux]
      have hs : M.step ⟨n₀ + 2, by omega⟩ a = ⟨n₀ + 3, by omega⟩ := by
        dsimp only [M]
        rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega)]
      rw [hs, hdead]
      constructor
      · intro h
        have := congrArg Fin.val h
        simp at this
      · intro h; simp at h
  have hmid : ∀ (u : List (Fin 2)) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n₀ + 1),
      M.evalFrom ⟨i, by omega⟩ u = ⟨n₀ + 2, by omega⟩ ↔
        ∃ j : ℕ, n₀ + 1 - i ≤ j ∧ u = List.replicate j z0 ++ [z1] := by
    intro u
    induction u with
    | nil =>
      intro i hi1 hi2
      simp only [DFA.evalFrom, List.foldl_nil, Fin.ext_iff]
      constructor
      · intro h; omega
      · rintro ⟨j, _, heq⟩
        have hlen := congrArg List.length heq
        simp at hlen
    | cons a tl ih =>
      intro i hi1 hi2
      rw [dfa_evalFrom_cons_aux]
      by_cases hle : i ≤ n₀
      · rcases hfin2_cases a with rfl | rfl
        · have hs : M.step ⟨i, by omega⟩ z0 = ⟨i + 1, by omega⟩ := by
            have hi0 : i ≠ 0 := by omega
            simp [M, hi0, hle]
          rw [hs, ih (i + 1) (by omega) (by omega)]
          constructor
          · rintro ⟨j, hj, rfl⟩
            exact ⟨j + 1, by omega, by rw [List.replicate_succ, List.cons_append]⟩
          · rintro ⟨j, hj, hrep⟩
            cases j with
            | zero =>
              simp only [List.replicate_zero, List.nil_append, List.cons.injEq] at hrep
              have := hrep.1
              simp [z0, z1] at this
            | succ j' =>
              rw [List.replicate_succ, List.cons_append, List.cons.injEq] at hrep
              exact ⟨j', by omega, hrep.2⟩
        · have hs : M.step ⟨i, by omega⟩ z1 = ⟨n₀ + 3, by omega⟩ := by
            have hi0 : i ≠ 0 := by omega
            have hne : z1 ≠ z0 := by decide
            simp [M, hi0, hle, hne]
          rw [hs, hdead]
          constructor
          · intro h
            have := congrArg Fin.val h
            simp at this
          · rintro ⟨j, hj, hrep⟩
            cases j with
            | zero => omega
            | succ j' =>
              rw [List.replicate_succ, List.cons_append, List.cons.injEq] at hrep
              have := hrep.1
              simp [z0, z1] at this
      · have hi_eq : i = n₀ + 1 := by omega
        subst hi_eq
        rcases hfin2_cases a with rfl | rfl
        · have hs : M.step ⟨n₀ + 1, by omega⟩ z0 = ⟨n₀ + 1, by omega⟩ := by
            simp [M]
          rw [hs, ih (n₀ + 1) (by omega) le_rfl]
          constructor
          · rintro ⟨j, _, rfl⟩
            exact ⟨j + 1, by omega, by rw [List.replicate_succ, List.cons_append]⟩
          · rintro ⟨j, _, hrep⟩
            cases j with
            | zero =>
              simp only [List.replicate_zero, List.nil_append, List.cons.injEq] at hrep
              have := hrep.1
              simp [z0, z1] at this
            | succ j' =>
              rw [List.replicate_succ, List.cons_append, List.cons.injEq] at hrep
              exact ⟨j', by omega, hrep.2⟩
        · have hs : M.step ⟨n₀ + 1, by omega⟩ z1 = ⟨n₀ + 2, by omega⟩ := by
            have hne : z1 ≠ z0 := by decide
            simp [M, hne]
          rw [hs, hacc_from_accept]
          constructor
          · intro htl
            subst htl
            exact ⟨0, by omega, rfl⟩
          · rintro ⟨j, _, hrep⟩
            cases j with
            | zero =>
              simp only [List.replicate_zero, List.nil_append, List.cons.injEq] at hrep
              exact hrep.2
            | succ j' =>
              rw [List.replicate_succ, List.cons_append, List.cons.injEq] at hrep
              have := hrep.1
              simp [z0, z1] at this
  have hlang : ∀ w : List (Fin 2),
      w ∈ M.accepts ↔
        ∃ j : ℕ, n₀ ≤ j ∧ w = z1 :: (List.replicate j z0 ++ [z1]) := by
    intro w
    change M.evalFrom ⟨0, by omega⟩ w ∈ ({⟨n₀ + 2, by omega⟩} : Set _) ↔ _
    rw [Set.mem_singleton_iff]
    cases w with
    | nil =>
      simp only [DFA.evalFrom, List.foldl_nil, Fin.ext_iff]
      constructor
      · intro h; omega
      · rintro ⟨j, _, h⟩; simp at h
    | cons a tl =>
      rw [dfa_evalFrom_cons_aux]
      rcases hfin2_cases a with rfl | rfl
      · have hs : M.step ⟨0, by omega⟩ z0 = ⟨n₀ + 3, by omega⟩ := by
          have hne : z0 ≠ z1 := by decide
          simp [M, hne]
        rw [hs, hdead]
        constructor
        · intro h
          have := congrArg Fin.val h
          simp at this
        · rintro ⟨j, _, h⟩
          simp only [List.cons.injEq] at h
          have := h.1
          simp [z0, z1] at this
      · have hs : M.step ⟨0, by omega⟩ z1 = ⟨1, by omega⟩ := by simp [M]
        rw [hs, hmid tl 1 le_rfl (by omega)]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, by omega, rfl⟩
        · rintro ⟨j, hj, h⟩
          simp only [List.cons.injEq] at h
          exact ⟨j, by omega, h.2⟩
  have hval_fermat : ∀ j : ℕ,
      Nat.ofDigits 2 ((z1 :: (List.replicate j z0 ++ [z1])).reverse.map Fin.val) =
        2 ^ (j + 1) + 1 := by
    intro j
    rw [ofDigits_cons_msd, ofDigits_concat_msd]
    have hzeros : Nat.ofDigits 2 ((List.replicate j z0).reverse.map Fin.val) = 0 := by
      rw [List.reverse_replicate, List.map_replicate]
      induction j with
      | zero => rfl
      | succ j' ih =>
        rw [List.replicate_succ, Nat.ofDigits, ih]
        rfl
    rw [hzeros]
    simp [z1]
    ring
  refine ⟨M, hlang, ?_⟩
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨j, hj, rfl⟩ := (hlang w).mp hw
    rw [hval_fermat j] at hp
    obtain ⟨m, hm⟩ := prime_two_pow_add_one_is_fermat (j + 1) (by omega) hp
    refine ⟨m, by omega, ?_⟩
    rwa [← hm]
  · rintro ⟨m, hm, hp⟩
    have h2m_pos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    set j := 2 ^ m - 1
    have hj_ge : n₀ ≤ j := by omega
    have hj_succ : j + 1 = 2 ^ m := by omega
    refine ⟨z1 :: (List.replicate j z0 ++ [z1]), (hlang _).mpr ⟨j, hj_ge, rfl⟩, ?_⟩
    rw [hval_fermat j, hj_succ]
    exact hp

/-- **Exact 20-State Sixth Fermat Prime Barrier DFA:**
There exists an explicit **20-state** base-2 DFA `M : DFA (Fin 2) (Fin 20)` (recognizing
`1 0^16 0^* 1`) whose prime acceptance is **provably equivalent** to the open conjecture
of whether there exists a sixth Fermat prime `F_m = 2 ^ (2 ^ m) + 1` with `m ≥ 5`. -/
theorem ppl073_sixth_fermat_prime_dfa :
    ∃ M : DFA (Fin 2) (Fin 20),
      (∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits 2 (w.reverse.map Fin.val))) ↔
        (∃ m : ℕ, 5 ≤ m ∧ Nat.Prime (2 ^ (2 ^ m) + 1)) := by
  obtain ⟨M, _, hiff⟩ := ppl073_fermat_barrier_dfa 16
  refine ⟨M, hiff.trans ?_⟩
  constructor
  · rintro ⟨m, hm, hp⟩
    refine ⟨m, ?_, hp⟩
    by_contra hlt
    push Not at hlt
    interval_cases m <;> norm_num at hm
  · rintro ⟨m, hm, hp⟩
    refine ⟨m, ?_, hp⟩
    calc 16 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm

/-- **2-State Missing-Digit DFA & Exact Prime-Acceptance Dichotomy (`k ≥ 3` vs `k = 2`):**
For every base `k ≥ 2` and forbidden digit `d : Fin k`:
1. There exists an explicit 2-state DFA `M : DFA (Fin k) (Fin 2)` accepting `{ w | d ∉ w }`.
2. Whenever `k ≥ 3`, `M` ALWAYS accepts at least one prime (with explicit small witness `2`, `3`,
   or `111_3 = 13`), in contrast to proving *infinitely many* primes (Maynard 2019 for `k = 10`).
3. At `k = 2`, forbidding `1` leaves `0^*` (zero primes), while forbidding `0` leaves `1^*`
   (the Mersenne repunits, accepting `3 = 11_2`). -/
theorem ppl073_missing_digit_dfa_prime_dichotomy (k : ℕ) (hk : 2 ≤ k) (d : Fin k) :
    ∃ M : DFA (Fin k) (Fin 2),
      (∀ w : List (Fin k), w ∈ M.accepts ↔ d ∉ w) ∧
      (3 ≤ k → ∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) ∧
      (k = 2 → d.val = 1 → ¬ ∃ w ∈ M.accepts, Nat.Prime (Nat.ofDigits k (w.reverse.map Fin.val))) := by
  let M : DFA (Fin k) (Fin 2) := {
    step := fun q a => if q.val = 0 ∧ a ≠ d then ⟨0, by decide⟩ else ⟨1, by decide⟩
    start := ⟨0, by decide⟩
    accept := {⟨0, by decide⟩}
  }
  have hdead : ∀ u : List (Fin k), M.evalFrom ⟨1, by decide⟩ u = ⟨1, by decide⟩ := by
    intro u
    induction u with
    | nil => rfl
    | cons a tl ih =>
      rw [dfa_evalFrom_cons_aux]
      have hs : M.step ⟨1, by decide⟩ a = ⟨1, by decide⟩ := by simp [M]
      rw [hs]
      exact ih
  have hlang : ∀ w : List (Fin k), w ∈ M.accepts ↔ d ∉ w := by
    intro w
    change M.evalFrom ⟨0, by decide⟩ w ∈ ({⟨0, by decide⟩} : Set (Fin 2)) ↔ d ∉ w
    rw [Set.mem_singleton_iff]
    induction w with
    | nil => simp [DFA.evalFrom]
    | cons a tl ih =>
      rw [dfa_evalFrom_cons_aux]
      by_cases ha : a = d
      · subst ha
        have hs : M.step ⟨0, by decide⟩ a = ⟨1, by decide⟩ := by simp [M]
        rw [hs, hdead]
        simp
      · have hs : M.step ⟨0, by decide⟩ a = ⟨0, by decide⟩ := by simp [M, ha]
        rw [hs, ih]
        simp [Ne.symm ha]
  refine ⟨M, hlang, ?_, ?_⟩
  · intro hk3
    by_cases hd2 : d.val = 2
    · by_cases hk4 : 4 ≤ k
      · refine ⟨[⟨3, by omega⟩], (hlang _).mpr ?_, ?_⟩
        · simp only [List.mem_singleton]
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        · simpa [Nat.ofDigits] using Nat.prime_three
      · have hk_eq : k = 3 := by omega
        subst hk_eq
        refine ⟨[⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩], (hlang _).mpr ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | h | h) <;> (have := congrArg Fin.val h; simp at this; omega)
        · have h13 : Nat.ofDigits 3
              (([⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩] : List (Fin 3)).reverse.map Fin.val) = 13 := by
            decide
          rw [h13]
          norm_num
    · refine ⟨[⟨2, by omega⟩], (hlang _).mpr ?_, ?_⟩
      · simp only [List.mem_singleton]
        intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      · simpa [Nat.ofDigits] using Nat.prime_two
  · intro hk2 hd1
    rintro ⟨w, hw, hp⟩
    have hnot : d ∉ w := (hlang w).mp hw
    have hzero : ∀ l : List (Fin k), d ∉ l → Nat.ofDigits k (l.map Fin.val) = 0 := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a tl ih =>
        intro hna
        simp only [List.mem_cons, not_or] at hna
        have ha0 : a.val = 0 := by
          have ha_lt : a.val < 2 := hk2 ▸ a.isLt
          have hne : a.val ≠ d.val := fun h => hna.1 (Fin.ext h.symm)
          omega
        simp [Nat.ofDigits, ha0, ih hna.2]
    have hval0 : Nat.ofDigits k (w.reverse.map Fin.val) = 0 :=
      hzero w.reverse (by simpa using hnot)
    rw [hval0] at hp
    exact Nat.not_prime_zero hp

end PPL073
