/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 096, PPL 112 & PPL 125 — Wolfram Rule 30 Prize Problems: Structural, Periodicity, Algebraic, and Density Foundations

## Honest Scope & Live Status
The three **Wolfram Rule 30 Prize Problems** (`rule30prize.org`, `prizeproblems.org`, $10,000 each,
$30,000 total) concern the central column `c(t) = a(t, 0)` of the single-seed Rule 30 spacetime
`a : ℕ → ℤ → Bool`, defined by `a 0 i = decide (i = 0)` and
`a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))`:
- **PPL 096 (`rule30prize.org` Problem 3, $10,000, VERIFIED OPEN):** Does computing the `n`-th
  center-column cell `a n 0` necessarily require at least `O(n)` computational effort?
- **PPL 112 (`rule30prize.org` Problem 2, $10,000, VERIFIED OPEN):** Do `0` and `1` occur with
  asymptotically equal frequency `1/2` in the center column `a t 0`?
- **PPL 125 (`rule30prize.org` Problem 1, $10,000, VERIFIED OPEN):** Is the center column `a t 0`
  non-periodic (not eventually periodic)?

**This file does NOT claim to solve any of the three open $10,000 Wolfram Rule 30 prizes.**
Instead, it provides a complete, self-contained, 100%-pure-Mathlib Lean 4 formalization (`0` `sorry`,
`0` `admit`, `0` custom `axiom`, `0` `native_decide`, `0` custom or `private` definitions in ANY
public theorem signature) of the core structural theory surrounding PPL 096, PPL 112, and PPL 125:

1. **Spacetime Foundations & Exact Diagonal Laws:** Existence & uniqueness of `a`, light-cone
   support (`|i| > t → a t i = false`), exact left/right edges, exact closed forms for right
   diagonals `m = 1, 2, 3` and left diagonals `m = 1, 2, 3, 4`, and **Universal Power-of-2
   Right-Diagonal Periodicity** (`∀ m t, a (t + 2^m) (t + 2^m - m) = a t (t - m)`).
2. **Local Left-Inversion, Left-Cone Reconstruction, & Jen's Periodicity Obstructions (PPL 125):**
   Local left-inversion, column-pair left-cone reconstruction/injectivity, periodic-pair propagation
   with zero threshold shift, **Jen's Adjacent-Column Aperiodicity Theorem (1990)** (no two adjacent
   columns can both be eventually periodic), **Unconditional Elimination of Eventual Period `P = 1`**
   in every single column `k : ℤ` (hence every column takes both `true` and `false` infinitely
   often), **Unconditional Eventual Period-2 Structural Lock** (golden-mean constraint on `k + 1`,
   odd-step `true` lock on `k - 1`, even-step `false` lock on `k - 4`), and **No Spatial Periodicity**.
3. **Exact Finite Prefix & Pure-Period Rule-Out (`1 ≤ P ≤ 16`, Zero `native_decide`):** Kernel-checked
   exact prefix of `a t 0` for `0 ≤ t ≤ 20` and pure-periodicity refutation for all `1 ≤ P ≤ 16`.
4. **Exact 4-to-1 Preimage Counting, Global Surjectivity, & Finite-Cylinder Dichotomy:** Constructive
   4-to-1 block preimage bijection, global surjectivity (no Garden of Eden) and non-injectivity on
   `ℤ → Bool`, and universal non-injectivity & non-surjectivity on every finite ring `ZMod n` (`n ≥ 1`).
5. **Exact ANF Degree Lower Bound (`deg ≥ t + 1`) & Left-Edge Separability (PPL 096):** Left-edge
   separability, exact `(t + 1)`-th order Boolean derivative non-vanishing on an explicit `(t + 1)`-set,
   and an unconditional `MvPolynomial ℤ (ZMod 2)` total-degree lower bound `deg(P) ≥ t + 1` ruling out
   all bounded-degree `𝔽₂`-polynomial representations of `t`-step Rule 30.
6. **Exact Anti-Periodic Discrepancy & Cesàro Density Limits (PPL 112):** General `O(P)` discrepancy
   and `Filter.Tendsto ... (nhds (1 / 2))` theorem for anti-periodic sequences, yielding exact
   asymptotic density `1 / 2` on right diagonals `m = 1, 2, 3` and left diagonal `m = 3`, plus
   unconditional active-row weight bounds (`3 ≤ W(t) ≤ 2t` for `t ≥ 2`, `4 ≤ W(t) ≤ 2t` for `t ≥ 4`).
-/

namespace PPL096

open scoped BigOperators
open Filter Topology

/-! ### Section 1: Spacetime Foundations, Light-Cone Support, & Exact Diagonal Laws -/

/-- The canonical single-seed Rule 30 spacetime defined via `Nat.rec`. -/
private def r30Seed : ℕ → ℤ → Bool :=
  Nat.rec (fun i => decide (i = 0))
    (fun _ row i => xor (row (i - 1)) (row i || row (i + 1)))

private lemma r30Seed_zero (i : ℤ) : r30Seed 0 i = decide (i = 0) := rfl

private lemma r30Seed_succ (t : ℕ) (i : ℤ) :
    r30Seed (t + 1) i = xor (r30Seed t (i - 1)) (r30Seed t i || r30Seed t (i + 1)) := rfl

/-- **Theorem 1 (Existence & Uniqueness of Single-Seed Rule 30 Spacetime):**
There exists a unique spacetime `a : ℕ → ℤ → Bool` satisfying the single-seed initial condition
`a 0 i = decide (i = 0)` and the Rule 30 local update rule. -/
theorem ppl096_spacetime_exists_unique :
    ∃! a : ℕ → ℤ → Bool,
      (∀ i : ℤ, a 0 i = decide (i = 0)) ∧
      (∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) := by
  refine ⟨r30Seed, ⟨r30Seed_zero, r30Seed_succ⟩, ?_⟩
  rintro b ⟨hb0, hbstep⟩
  funext t i
  induction t generalizing i with
  | zero => rw [hb0, r30Seed_zero]
  | succ t ih => rw [hbstep, r30Seed_succ, ih (i - 1), ih i, ih (i + 1)]

/-- **Theorem 2 (Light-Cone Support):**
In single-seed Rule 30, every cell strictly outside `[-t, t]` is `false`. -/
theorem ppl096_light_cone_support (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, ∀ i : ℤ, (t : ℤ) < |i| → a t i = false := by
  intro t
  induction t with
  | zero =>
    intro i hi
    rw [h0]
    have hne : i ≠ 0 := by
      intro h
      subst h
      simp at hi
    simp [hne]
  | succ t ih =>
    intro i hi
    rw [hstep]
    have h1 : (t : ℤ) < |i - 1| := by
      have := abs_sub_abs_le_abs_sub i 1
      simp only [abs_one] at this
      omega
    have h2 : (t : ℤ) < |i| := by omega
    have h3 : (t : ℤ) < |i + 1| := by
      have := abs_sub_abs_le_abs_sub i (-1)
      simp only [sub_neg_eq_add, abs_neg, abs_one] at this
      omega
    rw [ih (i - 1) h1, ih i h2, ih (i + 1) h3]
    rfl

private lemma light_cone_left (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (t : ℕ) (i : ℤ) (hi : i < -(t : ℤ)) : a t i = false := by
  apply ppl096_light_cone_support a h0 hstep t i
  rw [abs_of_neg (by omega)]
  omega

private lemma light_cone_right (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (t : ℕ) (i : ℤ) (hi : (t : ℤ) < i) : a t i = false := by
  apply ppl096_light_cone_support a h0 hstep t i
  rw [abs_of_pos (by omega)]
  omega

/-- **Theorem 3 (Exact Left Edge):** `a t (-t) = true` for all `t : ℕ`. -/
theorem ppl096_left_edge (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, a t (-(t : ℤ)) = true := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rw [hstep]
    have h1 : a t (-((t + 1 : ℕ) : ℤ) - 1) = false :=
      light_cone_left a h0 hstep t _ (by push_cast; omega)
    have h2 : a t (-((t + 1 : ℕ) : ℤ)) = false :=
      light_cone_left a h0 hstep t _ (by push_cast; omega)
    have h3 : -((t + 1 : ℕ) : ℤ) + 1 = -(t : ℤ) := by push_cast; omega
    rw [h1, h2, h3, ih]
    rfl

/-- **Theorem 4 (Exact Right Edge):** `a t t = true` for all `t : ℕ`. -/
theorem ppl096_right_edge (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, a t (t : ℤ) = true := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rw [hstep]
    have h1 : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by push_cast; omega
    have h2 : a t ((t + 1 : ℕ) : ℤ) = false :=
      light_cone_right a h0 hstep t _ (by push_cast; omega)
    have h3 : a t (((t + 1 : ℕ) : ℤ) + 1) = false :=
      light_cone_right a h0 hstep t _ (by push_cast; omega)
    rw [h1, ih, h2, h3]
    rfl

/-- **Theorem 5 (Exact Right Diagonal `m = 1`):** `a t (t - 1) = decide (t % 2 = 1)` for all `t`. -/
theorem ppl096_right_diag_one (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, a t ((t : ℤ) - 1) = decide (t % 2 = 1) := by
  intro t
  induction t with
  | zero =>
    rw [h0]
    decide
  | succ t ih =>
    have heq : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by push_cast; omega
    rw [heq, hstep]
    have hre : a t (t : ℤ) = true := ppl096_right_edge a h0 hstep t
    have hrt : a t ((t : ℤ) + 1) = false := light_cone_right a h0 hstep t _ (by omega)
    rw [ih, hre, hrt]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [Nat.add_mod, h]

/-- **Theorem 6 (Exact Right Diagonal `m = 2`):** `a t (t - 2) = decide (t % 2 = 1)` for all `t`. -/
theorem ppl096_right_diag_two (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, a t ((t : ℤ) - 2) = decide (t % 2 = 1) := by
  intro t
  induction t with
  | zero =>
    rw [h0]
    decide
  | succ t ih =>
    have heq : ((t + 1 : ℕ) : ℤ) - 2 = (t : ℤ) - 1 := by push_cast; omega
    rw [heq, hstep]
    have h1 : (t : ℤ) - 1 - 1 = (t : ℤ) - 2 := by omega
    have h2 : (t : ℤ) - 1 + 1 = (t : ℤ) := by omega
    rw [h1, h2, ih, ppl096_right_edge a h0 hstep t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [Nat.add_mod, h]

/-- **Theorem 7 (Exact Right Diagonal `m = 3`):**
`a t (t - 3) = decide (t % 4 = 2 ∨ t % 4 = 3)` for all `t : ℕ`. -/
theorem ppl096_right_diag_three (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, a t ((t : ℤ) - 3) = decide (t % 4 = 2 ∨ t % 4 = 3) := by
  intro t
  induction t with
  | zero =>
    rw [h0]
    decide
  | succ t ih =>
    have heq : ((t + 1 : ℕ) : ℤ) - 3 = (t : ℤ) - 2 := by push_cast; omega
    rw [heq, hstep]
    have h1 : (t : ℤ) - 2 - 1 = (t : ℤ) - 3 := by omega
    have h2 : (t : ℤ) - 2 + 1 = (t : ℤ) - 1 := by omega
    rw [h1, h2, ih, ppl096_right_diag_two a h0 hstep t, ppl096_right_diag_one a h0 hstep t]
    have hmod : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
    rcases hmod with h | h | h | h
    · have h2m : t % 2 = 0 := by omega
      have hs : (t + 1) % 4 = 1 := by omega
      simp [h, h2m, hs]
    · have h2m : t % 2 = 1 := by omega
      have hs : (t + 1) % 4 = 2 := by omega
      simp [h, h2m, hs]
    · have h2m : t % 2 = 0 := by omega
      have hs : (t + 1) % 4 = 3 := by omega
      simp [h, h2m, hs]
    · have h2m : t % 2 = 1 := by omega
      have hs : (t + 1) % 4 = 0 := by omega
      simp [h, h2m, hs]

/-- **Theorem 8 (Exact Left Diagonal `m = 1`):** `a t (-t + 1) = true` for all `t ≥ 1`. -/
theorem ppl096_left_diag_one (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, 1 ≤ t → a t (-(t : ℤ) + 1) = true := by
  intro t ht
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  have heq : -((s + 1 : ℕ) : ℤ) + 1 = -(s : ℤ) := by push_cast; omega
  rw [heq, hstep]
  have h1 : a s (-(s : ℤ) - 1) = false := light_cone_left a h0 hstep s _ (by omega)
  have h2 : a s (-(s : ℤ)) = true := ppl096_left_edge a h0 hstep s
  rw [h1, h2]
  rfl

/-- **Theorem 9 (Exact Left Diagonal `m = 2`):** `a t (-t + 2) = false` for all `t ≥ 2`. -/
theorem ppl096_left_diag_two (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, 2 ≤ t → a t (-(t : ℤ) + 2) = false := by
  intro t ht
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ t by omega)
  have hs1 : 1 ≤ s := by omega
  have heq : -((s + 1 : ℕ) : ℤ) + 2 = -(s : ℤ) + 1 := by push_cast; omega
  rw [heq, hstep]
  have h1 : -(s : ℤ) + 1 - 1 = -(s : ℤ) := by omega
  rw [h1, ppl096_left_edge a h0 hstep s, ppl096_left_diag_one a h0 hstep s hs1]
  rfl

/-- **Theorem 10 (Exact Left Diagonal `m = 3`):**
`a t (-t + 3) = decide (t % 2 = 1)` for all `t ≥ 3`. -/
theorem ppl096_left_diag_three (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, 3 ≤ t → a t (-(t : ℤ) + 3) = decide (t % 2 = 1) := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' ht
  clear ht
  induction k with
  | zero =>
    change a 3 0 = true
    have h2m1 : a 2 (-1) = true := by
      have := ppl096_left_diag_one a h0 hstep 2 (by omega)
      simpa using this
    have h20 : a 2 0 = false := by
      have := ppl096_left_diag_two a h0 hstep 2 le_rfl
      simpa using this
    have h21 : a 2 1 = false := by
      have := ppl096_right_diag_one a h0 hstep 2
      simpa using this
    rw [hstep 2 0]
    norm_num
    rw [h2m1, h20, h21]
    decide
  | succ k ih =>
    have hge2 : 2 ≤ k + 3 := by omega
    have hge1 : 1 ≤ k + 3 := by omega
    have heq : -((k + 1 + 3 : ℕ) : ℤ) + 3 = -((k + 3 : ℕ) : ℤ) + 2 := by push_cast; omega
    have hstep_idx : k + 1 + 3 = (k + 3) + 1 := by omega
    rw [heq, hstep_idx, hstep]
    have h1 : -((k + 3 : ℕ) : ℤ) + 2 - 1 = -((k + 3 : ℕ) : ℤ) + 1 := by omega
    have h2 : -((k + 3 : ℕ) : ℤ) + 2 + 1 = -((k + 3 : ℕ) : ℤ) + 3 := by omega
    rw [h1, h2, ppl096_left_diag_one a h0 hstep (k + 3) hge1,
      ppl096_left_diag_two a h0 hstep (k + 3) hge2, ih]
    rcases Nat.mod_two_eq_zero_or_one (k + 3) with h | h <;> simp [Nat.add_mod, h]

/-- **Theorem 11 (Exact Left Diagonal `m = 4`):** `a t (-t + 4) = true` for all `t ≥ 4`. -/
theorem ppl096_left_diag_four (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, 4 ≤ t → a t (-(t : ℤ) + 4) = true := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' ht
  clear ht
  induction k with
  | zero =>
    change a 4 0 = true
    have h3m1 : a 3 (-1) = false := by
      have := ppl096_left_diag_two a h0 hstep 3 (by omega)
      simpa using this
    have h30 : a 3 0 = true := by
      have := ppl096_left_diag_three a h0 hstep 3 le_rfl
      simpa using this
    rw [hstep 3 0]
    norm_num
    rw [h3m1, h30]
    simp
  | succ k ih =>
    have hge2 : 2 ≤ k + 4 := by omega
    have heq : -((k + 1 + 4 : ℕ) : ℤ) + 4 = -((k + 4 : ℕ) : ℤ) + 3 := by push_cast; omega
    have hstep_idx : k + 1 + 4 = (k + 4) + 1 := by omega
    rw [heq, hstep_idx, hstep]
    have h1 : -((k + 4 : ℕ) : ℤ) + 3 - 1 = -((k + 4 : ℕ) : ℤ) + 2 := by omega
    have h2 : -((k + 4 : ℕ) : ℤ) + 3 + 1 = -((k + 4 : ℕ) : ℤ) + 4 := by omega
    rw [h1, h2, ppl096_left_diag_two a h0 hstep (k + 4) hge2, ih]
    simp

/-- Helper: cumulative XOR over a window of length `n` starting at `t`. -/
private def xorWin (g : ℕ → Bool) (t : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => xor (xorWin g t n) (g (t + n))

private lemma xorWin_shift_left (g : ℕ → Bool) (t n : ℕ) :
    xorWin g t (n + 1) = xor (g t) (xorWin g (t + 1) n) := by
  induction n with
  | zero =>
    simp [xorWin]
  | succ n ih =>
    change xor (xorWin g t (n + 1)) (g (t + (n + 1))) =
      xor (g t) (xor (xorWin g (t + 1) n) (g (t + 1 + n)))
    rw [ih, Bool.xor_assoc, show t + (n + 1) = t + 1 + n by omega]

private lemma xorWin_periodic_const (g : ℕ → Bool) (P : ℕ)
    (hP : ∀ t : ℕ, g (t + P) = g t) :
    ∀ t : ℕ, xorWin g t P = xorWin g 0 P := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : xorWin g t (P + 1) = xor (xorWin g t P) (g (t + P)) := rfl
    have h2 : xorWin g t (P + 1) = xor (g t) (xorWin g (t + 1) P) := xorWin_shift_left g t P
    rw [hP t] at h1
    have h3 : xor (g t) (xorWin g (t + 1) P) = xor (g t) (xorWin g t P) := by
      rw [← h2, h1, Bool.xor_comm]
    have h4 : xorWin g (t + 1) P = xorWin g t P := by
      have := congrArg (xor (g t)) h3
      simpa [Bool.xor_assoc] using this
    rw [h4, ih]

private lemma xor_integrator_step (r g : ℕ → Bool)
    (hrec : ∀ t : ℕ, r (t + 1) = xor (r t) (g t)) :
    ∀ t n : ℕ, r (t + n) = xor (r t) (xorWin g t n) := by
  intro t n
  induction n with
  | zero => simp [xorWin]
  | succ n ih =>
    rw [← Nat.add_assoc, hrec, ih]
    simp [xorWin]

private lemma right_diag_pow2_strong (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ m : ℕ, ∀ j ≤ m, ∀ t : ℕ,
      a (t + 2 ^ m) (((t + 2 ^ m : ℕ) : ℤ) - (j : ℤ)) = a t ((t : ℤ) - (j : ℤ)) := by
  intro m
  induction m with
  | zero =>
    intro j hj t
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [Nat.pow_zero, Nat.cast_zero, sub_zero]
    rw [ppl096_right_edge a h0 hstep (t + 1), ppl096_right_edge a h0 hstep t]
  | succ m ih =>
    intro j hj t
    by_cases hjm : j ≤ m
    · have h2 : t + 2 ^ (m + 1) = (t + 2 ^ m) + 2 ^ m := by ring
      rw [h2, ih j hjm (t + 2 ^ m), ih j hjm t]
    · have hj_eq : j = m + 1 := by omega
      subst hj_eq
      cases m with
      | zero =>
        simp only [Nat.zero_add, Nat.pow_one, Nat.cast_one]
        rw [ppl096_right_diag_one a h0 hstep (t + 2), ppl096_right_diag_one a h0 hstep t]
        simp
      | succ k =>
        let r : ℕ → Bool := fun s => a s ((s : ℤ) - ((k + 2 : ℕ) : ℤ))
        let g : ℕ → Bool := fun s =>
          a s ((s : ℤ) - ((k + 1 : ℕ) : ℤ)) || a s ((s : ℤ) - (k : ℤ))
        have hrec : ∀ s : ℕ, r (s + 1) = xor (r s) (g s) := by
          intro s
          simp only [r, g]
          have hs1 : ((s + 1 : ℕ) : ℤ) - ((k + 2 : ℕ) : ℤ) = (s : ℤ) - ((k + 1 : ℕ) : ℤ) := by
            push_cast; omega
          rw [hs1, hstep]
          congr 1
          · congr 1; push_cast; omega
          · congr 1; congr 1; push_cast; omega
        have hgP : ∀ s : ℕ, g (s + 2 ^ (k + 1)) = g s := by
          intro s
          simp only [g]
          rw [ih (k + 1) le_rfl s, ih k (by omega) s]
        have hhalf : ∀ s : ℕ, r (s + 2 ^ (k + 1)) = xor (r s) (xorWin g 0 (2 ^ (k + 1))) := by
          intro s
          rw [xor_integrator_step r g hrec s (2 ^ (k + 1)),
            xorWin_periodic_const g (2 ^ (k + 1)) hgP s]
        have hfull : r (t + 2 ^ (k + 2)) = r t := by
          have h2 : t + 2 ^ (k + 2) = (t + 2 ^ (k + 1)) + 2 ^ (k + 1) := by ring
          rw [h2, hhalf (t + 2 ^ (k + 1)), hhalf t]
          simp
        exact hfull

/-- **Theorem 12 (Universal Power-of-2 Right-Diagonal Periodicity):**
For **every** `m : ℕ` and **every** `t : ℕ`, the `m`-th right diagonal `t ↦ a t (t - m)` is purely
periodic from `t = 0` with period dividing `2 ^ m` (zero transient!). -/
theorem ppl096_right_diag_power_of_two_periodic (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ m t : ℕ, a (t + 2 ^ m) (((t + 2 ^ m : ℕ) : ℤ) - (m : ℤ)) = a t ((t : ℤ) - (m : ℤ)) :=
  fun m t => right_diag_pow2_strong a h0 hstep m m le_rfl t

/-! ### Section 2: Local Left-Inversion, Left-Cone Reconstruction, & Jen's Periodicity Obstructions -/

/-- **Theorem 13 (Local Left-Inversion / Left-Permutivity):**
In any Rule 30 spacetime, `a t (i - 1)` is uniquely determined by `(a (t + 1) i, a t i, a t (i + 1))`. -/
theorem ppl096_local_left_inversion (a : ℕ → ℤ → Bool)
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, ∀ i : ℤ, a t (i - 1) = xor (a (t + 1) i) (a t i || a t (i + 1)) := by
  intro t i
  rw [hstep t i]
  cases a t (i - 1) <;> cases a t i <;> cases a t (i + 1) <;> rfl

/-- **Theorem 14 (Column-Pair Left-Cone Reconstruction / Injectivity):**
If two Rule 30 spacetimes agree on two adjacent columns `k` and `k + 1` for all `t ≥ T`, then they
agree on the entire left half-plane `i ≤ k` for all `t ≥ T`. -/
theorem ppl096_column_pair_left_reconstruction (a b : ℕ → ℤ → Bool)
    (ha : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (hb : ∀ t : ℕ, ∀ i : ℤ, b (t + 1) i = xor (b t (i - 1)) (b t i || b t (i + 1)))
    (k : ℤ) (T : ℕ)
    (hk : ∀ t ≥ T, a t k = b t k)
    (hk1 : ∀ t ≥ T, a t (k + 1) = b t (k + 1)) :
    ∀ i : ℤ, i ≤ k → ∀ t ≥ T, a t i = b t i := by
  have hshift : ∀ m : ℕ, (∀ t ≥ T, a t (k - m) = b t (k - m)) ∧
      (∀ t ≥ T, a t (k - m + 1) = b t (k - m + 1)) := by
    intro m
    induction m with
    | zero =>
      simpa using ⟨hk, hk1⟩
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · intro t ht
        have heq : k - ((m + 1 : ℕ) : ℤ) = (k - (m : ℤ)) - 1 := by push_cast; omega
        rw [heq, ppl096_local_left_inversion a ha, ppl096_local_left_inversion b hb]
        rw [ih.1 (t + 1) (by omega), ih.1 t ht, ih.2 t ht]
      · intro t ht
        have heq : k - ((m + 1 : ℕ) : ℤ) + 1 = k - (m : ℤ) := by push_cast; omega
        rw [heq]
        exact ih.1 t ht
  intro i hi t ht
  set m : ℕ := (k - i).toNat
  have hm : k - (m : ℤ) = i := by omega
  rw [← hm]
  exact (hshift m).1 t ht

/-- **Theorem 15 (Periodic Column Pair Forces Periodic Left Half-Plane with Zero Threshold Shift):**
In any Rule 30 spacetime, if columns `k` and `k + 1` are eventually periodic of period `P` from
time `T`, then EVERY column `i ≤ k` is eventually periodic of the SAME period `P` from the SAME
threshold `T`. -/
theorem ppl096_periodic_pair_forces_periodic_left_cone (a : ℕ → ℤ → Bool)
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (k : ℤ) (T P : ℕ)
    (hk : ∀ t ≥ T, a (t + P) k = a t k)
    (hk1 : ∀ t ≥ T, a (t + P) (k + 1) = a t (k + 1)) :
    ∀ i : ℤ, i ≤ k → ∀ t ≥ T, a (t + P) i = a t i := by
  let b : ℕ → ℤ → Bool := fun t i => a (t + P) i
  have hb : ∀ t : ℕ, ∀ i : ℤ, b (t + 1) i = xor (b t (i - 1)) (b t i || b t (i + 1)) := by
    intro t i
    show a (t + 1 + P) i = xor (a (t + P) (i - 1)) (a (t + P) i || a (t + P) (i + 1))
    rw [show t + 1 + P = (t + P) + 1 by omega]
    exact hstep (t + P) i
  exact ppl096_column_pair_left_reconstruction b a hb hstep k T hk hk1

private lemma periodic_mul (f : ℕ → Bool) (T P q : ℕ)
    (h : ∀ t ≥ T, f (t + P) = f t) :
    ∀ t ≥ T, f (t + q * P) = f t := by
  induction q with
  | zero => intro t _; simp
  | succ q ih =>
    intro t ht
    have h1 : t + (q + 1) * P = (t + q * P) + P := by ring
    rw [h1, h (t + q * P) (by omega), ih t ht]

/-- **Theorem 16 (Jen's Adjacent-Column Aperiodicity Theorem, 1990):**
In single-seed Rule 30, NO two adjacent columns `(k, k + 1)` can BOTH be eventually periodic
(for ANY periods `P₁, P₂ ≥ 1` and ANY transients `T₁, T₂ : ℕ`). -/
theorem ppl096_no_adjacent_eventually_periodic_columns (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (k : ℤ) (T₁ T₂ P₁ P₂ : ℕ) (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) :
    ¬ ((∀ t ≥ T₁, a (t + P₁) k = a t k) ∧ (∀ t ≥ T₂, a (t + P₂) (k + 1) = a t (k + 1))) := by
  rintro ⟨h1, h2⟩
  set T : ℕ := max T₁ T₂
  set P : ℕ := P₁ * P₂
  have hP : 1 ≤ P := Nat.mul_pos hP₁ hP₂
  have hk : ∀ t ≥ T, a (t + P) k = a t k := by
    intro t ht
    have hmul := periodic_mul (fun s => a s k) T₁ P₁ P₂ h1 t (le_trans (le_max_left _ _) ht)
    simpa [P, Nat.mul_comm] using hmul
  have hk1 : ∀ t ≥ T, a (t + P) (k + 1) = a t (k + 1) := by
    intro t ht
    have hmul := periodic_mul (fun s => a s (k + 1)) T₂ P₂ P₁ h2 t (le_trans (le_max_right _ _) ht)
    simpa [P] using hmul
  have hleft := ppl096_periodic_pair_forces_periodic_left_cone a hstep k T P hk hk1
  set t : ℕ := T + k.natAbs
  set i : ℤ := -((t + P : ℕ) : ℤ)
  have hi_le : i ≤ k := by
    have hk_bound : -(k.natAbs : ℤ) ≤ k := by
      rcases Int.natAbs_eq k with h | h <;> omega
    have hT0 : (0 : ℤ) ≤ (T : ℤ) := Nat.cast_nonneg T
    have hP0 : (0 : ℤ) ≤ (P : ℤ) := Nat.cast_nonneg P
    have hi_eq : i = -((T : ℤ) + (k.natAbs : ℤ) + (P : ℤ)) := by
      dsimp only [i, t]
      push_cast
      ring
    linarith
  have heq := hleft i hi_le t (by omega)
  have hlhs : a (t + P) i = true := ppl096_left_edge a h0 hstep (t + P)
  have hrhs : a t i = false := light_cone_left a h0 hstep t i (by simp only [i]; push_cast; omega)
  rw [hlhs, hrhs] at heq
  exact Bool.noConfusion heq

/-- **Theorem 17 (Unconditional Elimination of Eventual Period `P = 1` in Every Column):**
In single-seed Rule 30, NO fixed column `k : ℤ` (in particular, the central column `k = 0`) can
ever become eventually constant (`a (t + 1) k = a t k` for all `t ≥ T`). -/
theorem ppl096_no_eventually_constant_column (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (k : ℤ) (T : ℕ) :
    ¬ (∀ t ≥ T, a (t + 1) k = a t k) := by
  intro hconst
  have hall : ∀ t ≥ T, a t k = a T k := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← Nat.add_assoc, hconst (T + d) (by omega), ih (by omega)]
  cases hval : a T k
  · -- Case 1: column k is eventually constant `false`.
    -- Then column `k + 1` satisfies `a (t + 1) (k + 1) = a t (k + 1) || a t (k + 2)`,
    -- hence is monotone non-decreasing and therefore eventually constant!
    have hmono : ∀ t ≥ T, a t (k + 1) = true → a (t + 1) (k + 1) = true := by
      intro t ht htrue
      rw [hstep t (k + 1)]
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub, hall t ht, hval, htrue]
      rfl
    by_cases hex : ∃ t₀ ≥ T, a t₀ (k + 1) = true
    · obtain ⟨t₀, ht₀, htrue⟩ := hex
      have hall1 : ∀ t ≥ t₀, a t (k + 1) = true := by
        intro t ht
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
        induction d with
        | zero => simpa using htrue
        | succ d ih =>
          rw [← Nat.add_assoc]
          exact hmono (t₀ + d) (by omega) (ih (by omega))
      have hper1 : ∀ t ≥ t₀, a (t + 1) (k + 1) = a t (k + 1) := by
        intro t ht
        rw [hall1 (t + 1) (by omega), hall1 t ht]
      exact ppl096_no_adjacent_eventually_periodic_columns a h0 hstep k T t₀ 1 1 le_rfl le_rfl
        ⟨hconst, hper1⟩
    · push Not at hex
      have hper1 : ∀ t ≥ T, a (t + 1) (k + 1) = a t (k + 1) := by
        intro t ht
        have hf1 : a (t + 1) (k + 1) = false := Bool.eq_false_iff.mpr (hex (t + 1) (by omega))
        have hf0 : a t (k + 1) = false := Bool.eq_false_iff.mpr (hex t ht)
        rw [hf1, hf0]
      exact ppl096_no_adjacent_eventually_periodic_columns a h0 hstep k T T 1 1 le_rfl le_rfl
        ⟨hconst, hper1⟩
  · -- Case 2: column k is eventually constant `true`.
    -- By local left-inversion, column `k - 1` is forced to be eventually constant `false`!
    have hleft_false : ∀ t ≥ T, a t (k - 1) = false := by
      intro t ht
      rw [ppl096_local_left_inversion a hstep t k, hall (t + 1) (by omega), hall t ht, hval]
      simp
    have hper_left : ∀ t ≥ T, a (t + 1) (k - 1) = a t (k - 1) := by
      intro t ht
      rw [hleft_false (t + 1) (by omega), hleft_false t ht]
    have hk_eq : (k - 1) + 1 = k := by omega
    have hconst' : ∀ t ≥ T, a (t + 1) ((k - 1) + 1) = a t ((k - 1) + 1) := by
      simpa [hk_eq] using hconst
    exact ppl096_no_adjacent_eventually_periodic_columns a h0 hstep (k - 1) T T 1 1 le_rfl le_rfl
      ⟨hper_left, hconst'⟩

/-- **Theorem 18 (Every Column Takes Both Values Infinitely Often):**
In single-seed Rule 30, every fixed column `k : ℤ` (in particular, the central column `k = 0`)
contains infinitely many `true`s and infinitely many `false`s. -/
theorem ppl096_column_infinitely_many_true_and_false (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (k : ℤ) (N : ℕ) :
    (∃ t ≥ N, a t k = true) ∧ (∃ t ≥ N, a t k = false) := by
  constructor
  · by_contra h
    push Not at h
    apply ppl096_no_eventually_constant_column a h0 hstep k N
    intro t ht
    rw [Bool.eq_false_iff.mpr (h (t + 1) (by omega)), Bool.eq_false_iff.mpr (h t ht)]
  · by_contra h
    push Not at h
    have htrue : ∀ s ≥ N, a s k = true := by
      intro s hs
      cases hx : a s k
      · exact absurd hx (h s hs)
      · rfl
    apply ppl096_no_eventually_constant_column a h0 hstep k N
    intro t ht
    rw [htrue (t + 1) (by omega), htrue t ht]

/-- **Theorem 19 (Unconditional Eventual Period-2 Structural Lock):**
In any Rule 30 spacetime, if a single column `k` eventually alternates `false, true, false, true, ...`
from time `T`, then for ALL `n : ℕ`:
1. The even subsequence `u_n = a (T + 2*n) (k + 1)` of column `k + 1` obeys the golden-mean
   exclusion `u_n = true → u_{n+1} = false` (no two consecutive `true`s),
2. Column `k - 1` is locked to `true` on every odd step `T + 2*n + 1`, and
3. Column `k - 4` is locked to `false` on every even step `T + 2*n`. -/
theorem ppl096_period_two_structural_lock (a : ℕ → ℤ → Bool)
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (k : ℤ) (T : ℕ)
    (heven : ∀ n : ℕ, a (T + 2 * n) k = false)
    (hodd : ∀ n : ℕ, a (T + 2 * n + 1) k = true) :
    (∀ n : ℕ, a (T + 2 * n) (k + 1) = true → a (T + 2 * (n + 1)) (k + 1) = false) ∧
    (∀ n : ℕ, a (T + 2 * n + 1) (k - 1) = true) ∧
    (∀ n : ℕ, a (T + 2 * n) (k - 4) = false) := by
  have hu_no11 : ∀ n : ℕ, a (T + 2 * n) (k + 1) = true → a (T + 2 * (n + 1)) (k + 1) = false := by
    intro n hu
    have hv : a (T + 2 * n + 1) (k + 1) = true := by
      rw [hstep (T + 2 * n) (k + 1)]
      have hs : k + 1 - 1 = k := by omega
      rw [hs, heven n, hu]
      rfl
    have ht2 : T + 2 * (n + 1) = (T + 2 * n + 1) + 1 := by omega
    rw [ht2, hstep (T + 2 * n + 1) (k + 1)]
    have hs : k + 1 - 1 = k := by omega
    rw [hs, hodd n, hv]
    rfl
  have hkm1_even : ∀ n : ℕ, a (T + 2 * n) (k - 1) = !(a (T + 2 * n) (k + 1)) := by
    intro n
    rw [ppl096_local_left_inversion a hstep (T + 2 * n) k, hodd n, heven n]
    cases a (T + 2 * n) (k + 1) <;> rfl
  have hkm1_odd : ∀ n : ℕ, a (T + 2 * n + 1) (k - 1) = true := by
    intro n
    rw [ppl096_local_left_inversion a hstep (T + 2 * n + 1) k]
    have ht2 : (T + 2 * n + 1) + 1 = T + 2 * (n + 1) := by omega
    rw [ht2, heven (n + 1), hodd n]
    rfl
  have hkm2_even : ∀ n : ℕ, a (T + 2 * n) (k - 2) = a (T + 2 * n) (k + 1) := by
    intro n
    have hidx : k - 2 = (k - 1) - 1 := by omega
    have hidx2 : (k - 1) + 1 = k := by omega
    rw [hidx, ppl096_local_left_inversion a hstep (T + 2 * n) (k - 1), hidx2,
      hkm1_odd n, hkm1_even n, heven n]
    cases a (T + 2 * n) (k + 1) <;> rfl
  have hkm2_odd : ∀ n : ℕ, a (T + 2 * n + 1) (k - 2) = a (T + 2 * (n + 1)) (k + 1) := by
    intro n
    have hidx : k - 2 = (k - 1) - 1 := by omega
    have hidx2 : (k - 1) + 1 = k := by omega
    have ht2 : (T + 2 * n + 1) + 1 = T + 2 * (n + 1) := by omega
    rw [hidx, ppl096_local_left_inversion a hstep (T + 2 * n + 1) (k - 1), hidx2,
      ht2, hkm1_even (n + 1), hkm1_odd n, hodd n]
    cases a (T + 2 * (n + 1)) (k + 1) <;> rfl
  have hkm3_even : ∀ n : ℕ, a (T + 2 * n) (k - 3) = !(a (T + 2 * (n + 1)) (k + 1)) := by
    intro n
    have hidx : k - 3 = (k - 2) - 1 := by omega
    have hidx2 : (k - 2) + 1 = k - 1 := by omega
    rw [hidx, ppl096_local_left_inversion a hstep (T + 2 * n) (k - 2), hidx2,
      hkm2_odd n, hkm2_even n, hkm1_even n]
    cases a (T + 2 * n) (k + 1) <;> cases a (T + 2 * (n + 1)) (k + 1) <;> rfl
  have hkm3_odd : ∀ n : ℕ, a (T + 2 * n + 1) (k - 3) = !(a (T + 2 * (n + 1)) (k + 1)) := by
    intro n
    have hidx : k - 3 = (k - 2) - 1 := by omega
    have hidx2 : (k - 2) + 1 = k - 1 := by omega
    have ht2 : (T + 2 * n + 1) + 1 = T + 2 * (n + 1) := by omega
    rw [hidx, ppl096_local_left_inversion a hstep (T + 2 * n + 1) (k - 2), hidx2,
      ht2, hkm2_even (n + 1), hkm2_odd n, hkm1_odd n]
    cases a (T + 2 * (n + 1)) (k + 1) <;> rfl
  have hkm4_even : ∀ n : ℕ, a (T + 2 * n) (k - 4) = false := by
    intro n
    have hidx : k - 4 = (k - 3) - 1 := by omega
    have hidx2 : (k - 3) + 1 = k - 2 := by omega
    rw [hidx, ppl096_local_left_inversion a hstep (T + 2 * n) (k - 3), hidx2,
      hkm3_odd n, hkm3_even n, hkm2_even n]
    cases h0v : a (T + 2 * n) (k + 1)
    · cases a (T + 2 * (n + 1)) (k + 1) <;> rfl
    · have h1v := hu_no11 n h0v
      rw [h1v]
      rfl
  exact ⟨hu_no11, hkm1_odd, hkm4_even⟩

/-- **Theorem 20 (No Spatial Periodicity Inside the Active Cone):**
In single-seed Rule 30, for every `t : ℕ`, every `I₀ ≤ (t : ℤ)`, and every spatial period `P ≥ 1`,
row `t` is NOT spatially periodic of period `P` on `[I₀, ∞)` (and in particular, NO row `t` is
globally spatially periodic on `ℤ`). -/
theorem ppl096_no_spatial_periodicity (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (t : ℕ) (I₀ : ℤ) (hI₀ : I₀ ≤ (t : ℤ)) (P : ℕ) (hP : 1 ≤ P) :
    ¬ (∀ i : ℤ, I₀ ≤ i → a t (i + (P : ℤ)) = a t i) := by
  intro hper
  have h1 := hper (t : ℤ) hI₀
  have hlhs : a t ((t : ℤ) + (P : ℤ)) = false := light_cone_right a h0 hstep t _ (by omega)
  have hrhs : a t (t : ℤ) = true := ppl096_right_edge a h0 hstep t
  rw [hlhs, hrhs] at h1
  exact Bool.noConfusion h1

/-! ### Section 3: Exact Finite Prefix Evaluation & Pure-Period Rule-Out (`1 ≤ P ≤ 16`, Zero `native_decide`) -/

/-- Linear-time sliding-window row step on `List Bool` representing `[-t, t]`. -/
private def r30NextAux : Bool → Bool → List Bool → List Bool
  | l, c, [] => [xor l c, c]
  | l, c, r :: rest => xor l (c || r) :: r30NextAux c r rest

private def r30Row : ℕ → List Bool
  | 0 => [true]
  | t + 1 => r30NextAux false false (r30Row t)

private def r30RowGet (l : List Bool) (t : ℕ) (i : ℤ) : Bool :=
  if -(t : ℤ) ≤ i ∧ i ≤ (t : ℤ) then
    l.getD (i + (t : ℤ)).toNat false
  else
    false

private lemma r30NextAux_length (l c : Bool) (xs : List Bool) :
    (r30NextAux l c xs).length = xs.length + 2 := by
  induction xs generalizing l c with
  | nil => rfl
  | cons r rest ih =>
    simp [r30NextAux, ih]

private lemma r30Row_length (t : ℕ) : (r30Row t).length = 2 * t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [r30Row, r30NextAux_length, ih]
    omega

private lemma r30NextAux_getD (l c : Bool) (xs : List Bool) (k : ℕ) :
    (r30NextAux l c xs).getD k false =
      xor (if k = 0 then l else if k = 1 then c else xs.getD (k - 2) false)
          ((if k = 0 then c else xs.getD (k - 1) false) || xs.getD k false) := by
  induction xs generalizing l c k with
  | nil =>
    rcases k with _ | _ | k <;> simp [r30NextAux]
  | cons r rest ih =>
    cases k with
    | zero =>
      simp [r30NextAux]
    | succ k =>
      simp only [r30NextAux, List.getD_cons_succ]
      rw [ih c r k]
      cases k with
      | zero => simp
      | succ k =>
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, List.getD_cons_succ]
        cases k with
        | zero => simp
        | succ k => simp

private lemma r30RowGet_eq (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    ∀ t : ℕ, ∀ i : ℤ, a t i = r30RowGet (r30Row t) t i := by
  intro t
  induction t with
  | zero =>
    intro i
    rw [h0]
    unfold r30RowGet r30Row
    by_cases hi : i = 0
    · subst hi; simp
    · simp only [Nat.cast_zero, neg_zero]
      rw [if_neg (by omega)]
      simp [hi]
  | succ t ih =>
    intro i
    by_cases hrange : -((t + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((t + 1 : ℕ) : ℤ)
    · rw [hstep, ih (i - 1), ih i, ih (i + 1)]
      unfold r30RowGet
      rw [if_pos hrange]
      simp only [r30Row, r30NextAux_getD]
      set k : ℕ := (i + ((t + 1 : ℕ) : ℤ)).toNat
      have hk_eq : (k : ℤ) = i + (t : ℤ) + 1 := by
        simp only [k]; push_cast; omega
      have hlen : (r30Row t).length = 2 * t + 1 := r30Row_length t
      have hL : (if -(t : ℤ) ≤ i - 1 ∧ i - 1 ≤ (t : ℤ) then
          (r30Row t).getD (i - 1 + (t : ℤ)).toNat false else false) =
          (if k = 0 then false else if k = 1 then false else (r30Row t).getD (k - 2) false) := by
        split_ifs with h1 hk0 hk1
        · omega
        · omega
        · congr 1; omega
        · rfl
        · rfl
        · symm
          simp [List.getD, List.getElem?_eq_none (show (r30Row t).length ≤ k - 2 by rw [hlen]; omega)]
      have hC : (if -(t : ℤ) ≤ i ∧ i ≤ (t : ℤ) then
          (r30Row t).getD (i + (t : ℤ)).toNat false else false) =
          (if k = 0 then false else (r30Row t).getD (k - 1) false) := by
        split_ifs with h1 hk0
        · omega
        · congr 1; omega
        · rfl
        · symm
          simp [List.getD, List.getElem?_eq_none (show (r30Row t).length ≤ k - 1 by rw [hlen]; omega)]
      have hR : (if -(t : ℤ) ≤ i + 1 ∧ i + 1 ≤ (t : ℤ) then
          (r30Row t).getD (i + 1 + (t : ℤ)).toNat false else false) =
          (r30Row t).getD k false := by
        split_ifs with h1
        · congr 1; omega
        · symm
          simp [List.getD, List.getElem?_eq_none (show (r30Row t).length ≤ k by rw [hlen]; omega)]
      rw [hL, hC, hR]
    · have hgt : ((t + 1 : ℕ) : ℤ) < |i| := by
        rcases le_or_gt 0 i with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_neg h]; omega
      rw [ppl096_light_cone_support a h0 hstep (t + 1) i hgt]
      unfold r30RowGet
      rw [if_neg hrange]

private def r30Center (t : ℕ) : Bool := (r30Row t).getD t false

private lemma r30Center_eq (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (t : ℕ) : a t 0 = r30Center t := by
  rw [r30RowGet_eq a h0 hstep t 0]
  unfold r30RowGet r30Center
  have hr : -(t : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (t : ℤ) := by omega
  rw [if_pos hr]
  simp

private lemma r30Center_prefix_decide :
    (List.range 21).map r30Center =
      [true, true, false, true, true, true, false, false, true, true,
       false, false, false, true, false, true, true, false, false, true, false] := by
  decide

private lemma r30Center_not_pure_period_decide :
    ∀ P : Fin 17, 1 ≤ P.1 → ∃ t : Fin 5, r30Center (t.1 + P.1) ≠ r30Center t.1 := by
  decide

/-- **Theorem 21 (Exact Certified Central Column Prefix `0 ≤ t ≤ 20`, Zero `native_decide`):**
Certifies the first 21 bits of `c(t) = a t 0` directly in the Lean kernel (`110111001100010110010`). -/
theorem ppl096_center_prefix_values (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    (List.range 21).map (fun t => a t 0) =
      [true, true, false, true, true, true, false, false, true, true,
       false, false, false, true, false, true, true, false, false, true, false] := by
  have hcongr : (List.range 21).map (fun t => a t 0) = (List.range 21).map r30Center := by
    apply List.map_congr_left
    intro t _
    exact r30Center_eq a h0 hstep t
  rw [hcongr]
  exact r30Center_prefix_decide

/-- **Theorem 22 (Pure-Period Rule-Out for `1 ≤ P ≤ 16`, Zero `native_decide`):**
For every `1 ≤ P ≤ 16`, the central column `t ↦ a t 0` is NOT purely periodic of period `P`
(explicit witness `t ≤ 4` with `a (t + P) 0 ≠ a t 0`). -/
theorem ppl096_center_not_purely_periodic_le_16 (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (P : ℕ) (hP1 : 1 ≤ P) (hP16 : P ≤ 16) :
    ¬ (∀ t : ℕ, a (t + P) 0 = a t 0) := by
  intro hper
  obtain ⟨t, ht⟩ := r30Center_not_pure_period_decide ⟨P, by omega⟩ hP1
  apply ht
  rw [← r30Center_eq a h0 hstep (t.1 + P), ← r30Center_eq a h0 hstep t.1]
  exact hper t.1

/-! ### Section 4: Exact 4-to-1 Preimages, Global Surjectivity, & Finite-Cylinder Dichotomy -/

/-- Right-to-left constructive preimage builder for a target block `y : Fin m → Bool` given
right boundary bits `(b₀, b₁)`. -/
private def r30PreimageWord : ∀ {m : ℕ}, (Fin m → Bool) → Bool → Bool → Fin (m + 2) → Bool
  | 0, _, b₀, b₁ => fun j => if j.1 = 0 then b₀ else b₁
  | m + 1, y, b₀, b₁ =>
    let tail : Fin (m + 2) → Bool := r30PreimageWord (fun i : Fin m => y i.succ) b₀ b₁
    let x0 : Bool := xor (y 0) (tail 0 || tail 1)
    fun j =>
      if h : j.1 = 0 then x0 else tail ⟨j.1 - 1, by omega⟩

private lemma r30PreimageWord_right0 :
    ∀ {m : ℕ} (y : Fin m → Bool) (b₀ b₁ : Bool),
      r30PreimageWord y b₀ b₁ ⟨m, by omega⟩ = b₀
  | 0, _, _, _ => rfl
  | m + 1, y, b₀, b₁ => by
    simp only [r30PreimageWord, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
    exact r30PreimageWord_right0 (fun i : Fin m => y i.succ) b₀ b₁

private lemma r30PreimageWord_right1 :
    ∀ {m : ℕ} (y : Fin m → Bool) (b₀ b₁ : Bool),
      r30PreimageWord y b₀ b₁ ⟨m + 1, by omega⟩ = b₁
  | 0, _, _, _ => rfl
  | m + 1, y, b₀, b₁ => by
    simp only [r30PreimageWord, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
    exact r30PreimageWord_right1 (fun i : Fin m => y i.succ) b₀ b₁

private lemma r30PreimageWord_spec :
    ∀ {m : ℕ} (y : Fin m → Bool) (b₀ b₁ : Bool) (i : Fin m),
      let x := r30PreimageWord y b₀ b₁
      xor (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩ || x ⟨i.1 + 2, by omega⟩) = y i
  | 0, _, _, _, i => Fin.elim0 i
  | m + 1, y, b₀, b₁, i => by
    cases i using Fin.cases with
    | zero =>
      simp only [r30PreimageWord, Fin.val_zero, ↓reduceDIte, zero_add, one_ne_zero,
        Nat.sub_self, Nat.reduceEqDiff]
      have h1 : (⟨0, by omega⟩ : Fin (m + 2)) = 0 := rfl
      have h2 : (⟨1, by omega⟩ : Fin (m + 2)) = 1 := rfl
      rw [h1, h2]
      cases y 0 <;> cases r30PreimageWord (fun i : Fin m => y i.succ) b₀ b₁ 0 <;>
        cases r30PreimageWord (fun i : Fin m => y i.succ) b₀ b₁ 1 <;> rfl
    | succ j =>
      simp only [r30PreimageWord, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceDIte, Nat.add_sub_cancel]
      exact r30PreimageWord_spec (fun i : Fin m => y i.succ) b₀ b₁ j

private lemma r30PreimageWord_unique :
    ∀ {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool),
      (∀ i : Fin m, xor (x ⟨i.1, by omega⟩)
        (x ⟨i.1 + 1, by omega⟩ || x ⟨i.1 + 2, by omega⟩) = y i) →
      x = r30PreimageWord y (x ⟨m, by omega⟩) (x ⟨m + 1, by omega⟩)
  | 0, y, x, _ => by
    funext ⟨jv, hjlt⟩
    have hj : jv = 0 ∨ jv = 1 := by omega
    rcases hj with rfl | rfl <;> rfl
  | m + 1, y, x, hx => by
    let x' : Fin (m + 2) → Bool := fun j => x ⟨j.1 + 1, by omega⟩
    have hx' : ∀ i : Fin m, xor (x' ⟨i.1, by omega⟩)
        (x' ⟨i.1 + 1, by omega⟩ || x' ⟨i.1 + 2, by omega⟩) = y i.succ := by
      intro i
      simpa [x'] using hx i.succ
    have ih := r30PreimageWord_unique (fun i : Fin m => y i.succ) x' hx'
    funext ⟨jv, hjlt⟩
    simp only [r30PreimageWord]
    split_ifs with hj
    · subst hj
      have h0 := hx 0
      simp only [Fin.val_zero, zero_add] at h0
      have ht0 : r30PreimageWord (fun i : Fin m => y i.succ)
          (x ⟨m + 1, by omega⟩) (x ⟨m + 2, by omega⟩) 0 = x ⟨1, by omega⟩ := by
        have := congrFun ih.symm 0
        simpa [x'] using this
      have ht1 : r30PreimageWord (fun i : Fin m => y i.succ)
          (x ⟨m + 1, by omega⟩) (x ⟨m + 2, by omega⟩) 1 = x ⟨2, by omega⟩ := by
        have := congrFun ih.symm 1
        simpa [x'] using this
      rw [ht0, ht1, ← h0]
      cases x ⟨0, by omega⟩ <;> cases x ⟨1, by omega⟩ <;> cases x ⟨2, by omega⟩ <;> rfl
    · have := congrFun ih ⟨jv - 1, by omega⟩
      have hj_eq : (⟨jv - 1 + 1, by omega⟩ : Fin (m + 3)) = ⟨jv, hjlt⟩ := Fin.ext (by dsimp; omega)
      simpa [x', hj_eq] using this

/-- **Theorem 23 (Exact 4-to-1 Finite-Block Preimage Count):**
For every `m : ℕ` and every target word `y : Fin m → Bool`, there are **exact `4`** preimage words
`x : Fin (m + 2) → Bool` mapping to `y` under Rule 30. -/
theorem ppl096_finite_block_four_preimages (m : ℕ) (y : Fin m → Bool) :
    (Finset.univ.filter fun x : Fin (m + 2) → Bool =>
      ∀ i : Fin m, xor (x ⟨i.1, by omega⟩)
        (x ⟨i.1 + 1, by omega⟩ || x ⟨i.1 + 2, by omega⟩) = y i).card = 4 := by
  have hbij :
      (Finset.univ.filter fun x : Fin (m + 2) → Bool =>
        ∀ i : Fin m, xor (x ⟨i.1, by omega⟩)
          (x ⟨i.1 + 1, by omega⟩ || x ⟨i.1 + 2, by omega⟩) = y i).card =
      (Finset.univ : Finset (Bool × Bool)).card := by
    refine Finset.card_bij (fun x _ => (x ⟨m, by omega⟩, x ⟨m + 1, by omega⟩)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 := (Finset.mem_filter.mp hx₁).2
      have h2 := (Finset.mem_filter.mp hx₂).2
      have hb0 : x₁ ⟨m, by omega⟩ = x₂ ⟨m, by omega⟩ := congrArg Prod.fst heq
      have hb1 : x₁ ⟨m + 1, by omega⟩ = x₂ ⟨m + 1, by omega⟩ := congrArg Prod.snd heq
      rw [r30PreimageWord_unique y x₁ h1, r30PreimageWord_unique y x₂ h2, hb0, hb1]
    · rintro ⟨b₀, b₁⟩ _
      refine ⟨r30PreimageWord y b₀ b₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        r30PreimageWord_spec y b₀ b₁⟩, ?_⟩
      exact Prod.ext (r30PreimageWord_right0 y b₀ b₁) (r30PreimageWord_right1 y b₀ b₁)
  rw [hbij]
  decide

/-- **Theorem 24 (Global Surjectivity / No Garden of Eden & Global Non-Injectivity on `ℤ → Bool`):**
The global Rule 30 map `F : (ℤ → Bool) → (ℤ → Bool)` is **surjective** (every bi-infinite
configuration has a preimage; proved via finite-block 4-preimages + Tychonoff compactness of
`ℤ → Bool`) and **not injective** (`const false` and `const true` both map to `const false`). -/
theorem ppl096_global_surjective_and_noninjective :
    Function.Surjective (fun (x : ℤ → Bool) (i : ℤ) => xor (x (i - 1)) (x i || x (i + 1))) ∧
    ¬ Function.Injective (fun (x : ℤ → Bool) (i : ℤ) => xor (x (i - 1)) (x i || x (i + 1))) := by
  constructor
  · intro y
    let K : ℕ → Set (ℤ → Bool) := fun N =>
      {x : ℤ → Bool | ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ (N : ℤ) →
        xor (x (i - 1)) (x i || x (i + 1)) = y i}
    have hK_closed : ∀ N : ℕ, IsClosed (K N) := by
      intro N
      have heq : K N = ⋂ i ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) : Set ℤ),
          {x : ℤ → Bool | xor (x (i - 1)) (x i || x (i + 1)) = y i} := by
        ext x
        simp [K]
      rw [heq]
      refine isClosed_biInter fun i _ => ?_
      exact isClosed_singleton.preimage (by
        have h1 : Continuous (fun x : ℤ → Bool => x (i - 1)) := continuous_apply (i - 1)
        have h2 : Continuous (fun x : ℤ → Bool => x i) := continuous_apply i
        have h3 : Continuous (fun x : ℤ → Bool => x (i + 1)) := continuous_apply (i + 1)
        let f : Bool × Bool × Bool → Bool := fun p => xor p.1 (p.2.1 || p.2.2)
        have hf : Continuous f := continuous_of_discreteTopology
        exact hf.comp (h1.prodMk (h2.prodMk h3)))
    have hK_compact : ∀ N : ℕ, IsCompact (K N) := fun N => (hK_closed N).isCompact
    have hK_anti : ∀ N : ℕ, K (N + 1) ⊆ K N := by
      intro N x hx i hi1 hi2
      exact hx i (by push_cast; omega) (by push_cast; omega)
    have hK_nonempty : ∀ N : ℕ, (K N).Nonempty := by
      intro N
      let yfin : Fin (2 * N + 1) → Bool := fun j => y ((j.1 : ℤ) - (N : ℤ))
      let w : Fin (2 * N + 3) → Bool := r30PreimageWord yfin false false
      let x : ℤ → Bool := fun j =>
        if h : -((N : ℤ) + 1) ≤ j ∧ j ≤ (N : ℤ) + 1 then
          w ⟨(j + (N : ℤ) + 1).toNat, by omega⟩
        else false
      refine ⟨x, ?_⟩
      intro i hi1 hi2
      have h1 : -((N : ℤ) + 1) ≤ i - 1 ∧ i - 1 ≤ (N : ℤ) + 1 := by omega
      have h2 : -((N : ℤ) + 1) ≤ i ∧ i ≤ (N : ℤ) + 1 := by omega
      have h3 : -((N : ℤ) + 1) ≤ i + 1 ∧ i + 1 ≤ (N : ℤ) + 1 := by omega
      set k : ℕ := (i + (N : ℤ)).toNat
      have hk_lt : k < 2 * N + 1 := by omega
      have hspec := r30PreimageWord_spec yfin false false ⟨k, hk_lt⟩
      have hx1 : x (i - 1) = w ⟨k, by omega⟩ := by
        simp only [x, dif_pos h1]; congr 1; exact Fin.ext (by dsimp [k]; omega)
      have hx2 : x i = w ⟨k + 1, by omega⟩ := by
        simp only [x, dif_pos h2]; congr 1; exact Fin.ext (by dsimp [k]; omega)
      have hx3 : x (i + 1) = w ⟨k + 2, by omega⟩ := by
        simp only [x, dif_pos h3]; congr 1; exact Fin.ext (by dsimp [k]; omega)
      have hy : yfin ⟨k, hk_lt⟩ = y i := by
        simp only [yfin]; congr 1; omega
      rw [hx1, hx2, hx3, hspec, hy]
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hK_anti hK_nonempty (hK_compact 0) hK_closed
    refine ⟨x, ?_⟩
    funext i
    have hxN : x ∈ K i.natAbs := Set.mem_iInter.mp hx i.natAbs
    exact hxN i (by rcases Int.natAbs_eq i with h | h <;> omega)
      (by rcases Int.natAbs_eq i with h | h <;> omega)
  · intro hinj
    have heq : (fun (x : ℤ → Bool) (i : ℤ) => xor (x (i - 1)) (x i || x (i + 1))) (fun _ => false) =
        (fun (x : ℤ → Bool) (i : ℤ) => xor (x (i - 1)) (x i || x (i + 1))) (fun _ => true) := by
      funext i; rfl
    have hft := congrFun (@hinj (fun _ => false) (fun _ => true) heq) 0
    exact Bool.noConfusion hft

/-- **Theorem 25 (Universal Finite-Cylinder Non-Injectivity & Non-Surjectivity):**
Contrast with Theorem 24: on **every** finite ring `ZMod n` (`n ≥ 1`), the cylindrical Rule 30 map
is **neither injective nor surjective** (since `const false ≠ const true` collide on `const false`). -/
theorem ppl096_cylinder_not_injective_not_surjective (n : ℕ) [NeZero n] :
    ¬ Function.Injective (fun (x : ZMod n → Bool) (i : ZMod n) =>
        xor (x (i - 1)) (x i || x (i + 1))) ∧
    ¬ Function.Surjective (fun (x : ZMod n → Bool) (i : ZMod n) =>
        xor (x (i - 1)) (x i || x (i + 1))) := by
  let F : (ZMod n → Bool) → (ZMod n → Bool) :=
    fun x i => xor (x (i - 1)) (x i || x (i + 1))
  have hninj : ¬ Function.Injective F := by
    intro hinj
    have heq : F (fun _ => false) = F (fun _ => true) := by
      funext i; rfl
    have h0 := congrFun (@hinj (fun _ => false) (fun _ => true) heq) 0
    exact Bool.noConfusion h0
  exact ⟨hninj, fun hsurj => hninj (Finite.injective_iff_surjective.mpr hsurj)⟩

/-! ### Section 5: Left-Edge Separability & Exact ANF Degree Lower Bound (`deg ≥ t + 1`) (PPL 096) -/

/-- General `t`-step Rule 30 evolution from arbitrary initial configuration `x : ℤ → Bool`. -/
private def r30Evol (x : ℤ → Bool) : ℕ → ℤ → Bool :=
  Nat.rec x (fun _ row i => xor (row (i - 1)) (row i || row (i + 1)))

private lemma r30Evol_locality (x y : ℤ → Bool) :
    ∀ t : ℕ, ∀ i : ℤ,
      (∀ j : ℤ, i - (t : ℤ) ≤ j → j ≤ i + (t : ℤ) → x j = y j) →
      r30Evol x t i = r30Evol y t i := by
  intro t
  induction t with
  | zero =>
    intro i hxy
    exact hxy i (by omega) (by omega)
  | succ t ih =>
    intro i hxy
    change xor (r30Evol x t (i - 1)) (r30Evol x t i || r30Evol x t (i + 1)) =
      xor (r30Evol y t (i - 1)) (r30Evol y t i || r30Evol y t (i + 1))
    rw [ih (i - 1) (fun j h1 h2 => hxy j (by push_cast at *; omega) (by push_cast at *; omega)),
      ih i (fun j h1 h2 => hxy j (by push_cast at *; omega) (by push_cast at *; omega)),
      ih (i + 1) (fun j h1 h2 => hxy j (by push_cast at *; omega) (by push_cast at *; omega))]

private def flipBit (x : ℤ → Bool) (j₀ : ℤ) : ℤ → Bool :=
  fun j => if j = j₀ then !(x j) else x j

private lemma r30Evol_flip_left_edge (x : ℤ → Bool) :
    ∀ t : ℕ, ∀ i : ℤ, r30Evol (flipBit x (i - (t : ℤ))) t i = !(r30Evol x t i) := by
  intro t
  induction t with
  | zero =>
    intro i
    simp [r30Evol, flipBit]
  | succ t ih =>
    intro i
    change xor (r30Evol (flipBit x (i - ((t + 1 : ℕ) : ℤ))) t (i - 1))
        (r30Evol (flipBit x (i - ((t + 1 : ℕ) : ℤ))) t i ||
         r30Evol (flipBit x (i - ((t + 1 : ℕ) : ℤ))) t (i + 1)) =
      !(xor (r30Evol x t (i - 1)) (r30Evol x t i || r30Evol x t (i + 1)))
    have hleft_idx : i - ((t + 1 : ℕ) : ℤ) = (i - 1) - (t : ℤ) := by push_cast; omega
    have hL : r30Evol (flipBit x (i - ((t + 1 : ℕ) : ℤ))) t (i - 1) = !(r30Evol x t (i - 1)) := by
      rw [hleft_idx]; exact ih (i - 1)
    have hC : r30Evol (flipBit x (i - ((t + 1 : ℕ) : ℤ))) t i = r30Evol x t i := by
      apply r30Evol_locality
      intro j h1 _
      simp only [flipBit]
      rw [if_neg (by push_cast; omega)]
    have hR : r30Evol (flipBit x (i - ((t + 1 : ℕ) : ℤ))) t (i + 1) = r30Evol x t (i + 1) := by
      apply r30Evol_locality
      intro j h1 _
      simp only [flipBit]
      rw [if_neg (by push_cast; omega)]
    rw [hL, hC, hR]
    cases r30Evol x t (i - 1) <;> cases (r30Evol x t i || r30Evol x t (i + 1)) <;> rfl

/-- **Theorem 26 (Exact Left-Edge Separability / Linearity of `t`-Step Rule 30):**
For any two Rule 30 spacetimes `a, b` whose initial rows agree everywhere except at the leftmost
light-cone cell `i - t`, `b t i = !(a t i)` unconditionally (for all `t : ℕ`, `i : ℤ`). -/
theorem ppl096_left_edge_separability (a b : ℕ → ℤ → Bool)
    (ha : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1)))
    (hb : ∀ t : ℕ, ∀ i : ℤ, b (t + 1) i = xor (b t (i - 1)) (b t i || b t (i + 1)))
    (t : ℕ) (i : ℤ)
    (hflip : b 0 (i - (t : ℤ)) = !(a 0 (i - (t : ℤ))))
    (hrest : ∀ j : ℤ, j ≠ i - (t : ℤ) → b 0 j = a 0 j) :
    b t i = !(a t i) := by
  have ha_eq : ∀ s j, a s j = r30Evol (a 0) s j := by
    intro s; induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro j; rw [ha]; change xor (a s (j - 1)) (a s j || a s (j + 1)) =
        xor (r30Evol (a 0) s (j - 1)) (r30Evol (a 0) s j || r30Evol (a 0) s (j + 1))
      rw [ih, ih, ih]
  have hb_eq : ∀ s j, b s j = r30Evol (b 0) s j := by
    intro s; induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro j; rw [hb]; change xor (b s (j - 1)) (b s j || b s (j + 1)) =
        xor (r30Evol (b 0) s (j - 1)) (r30Evol (b 0) s j || r30Evol (b 0) s (j + 1))
      rw [ih, ih, ih]
  have hb0_eq : b 0 = flipBit (a 0) (i - (t : ℤ)) := by
    funext j
    simp only [flipBit]
    split_ifs with hj
    · subst hj; exact hflip
    · exact hrest j hj
  rw [hb_eq, ha_eq, hb0_eq]
  exact r30Evol_flip_left_edge (a 0) t i

/-- Convert `Bool` to `ZMod 2`. -/
private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma b2z_xor (u v : Bool) : b2z (xor u v) = b2z u + b2z v := by
  cases u <;> cases v <;> decide

private lemma b2z_not (u : Bool) : b2z (!u) = 1 + b2z u := by
  cases u <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- Explicit `(t + 1)`-element witness set `S_t(i)` for the `(t + 1)`-th Boolean derivative of
`r30Evol · t i`. Defined recursively: `S_1(i) = {i, i + 1}`, `S_{t+1}(i) = insert (i - t) (S_t(i + 1))`. -/
private def derivSet : ℕ → ℤ → Finset ℤ
  | 0, i => {i}
  | 1, i => {i, i + 1}
  | t + 2, i => insert (i - ((t + 1 : ℕ) : ℤ)) (derivSet (t + 1) (i + 1))

private lemma derivSet_mem_bounds :
    ∀ t : ℕ, 1 ≤ t → ∀ i : ℤ, ∀ j ∈ derivSet t i, i - (t : ℤ) + 1 ≤ j ∧ j ≤ i + (t : ℤ)
  | 0, ht, _, _, _ => by omega
  | 1, _, i, j, hj => by
    simp only [derivSet, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> omega
  | t + 2, _, i, j, hj => by
    simp only [derivSet, Finset.mem_insert] at hj
    rcases hj with rfl | hj'
    · push_cast; omega
    · have hb := derivSet_mem_bounds (t + 1) (by omega) (i + 1) j hj'
      push_cast at *; omega

private lemma derivSet_contains_right :
    ∀ t : ℕ, 1 ≤ t → ∀ i : ℤ, i + (t : ℤ) ∈ derivSet t i
  | 0, ht, _ => by omega
  | 1, _, i => by simp [derivSet]
  | t + 2, _, i => by
    simp only [derivSet, Finset.mem_insert]
    right
    have := derivSet_contains_right (t + 1) (by omega) (i + 1)
    convert this using 1
    push_cast; omega

private lemma derivSet_not_mem_left (t : ℕ) (ht : 1 ≤ t) (i : ℤ) :
    i - (t : ℤ) ∉ derivSet t (i + 1) := by
  intro hmem
  have hb := derivSet_mem_bounds t ht (i + 1) (i - (t : ℤ)) hmem
  omega

private lemma derivSet_card :
    ∀ t : ℕ, 1 ≤ t → ∀ i : ℤ, (derivSet t i).card = t + 1
  | 0, ht, _ => by omega
  | 1, _, i => by
    simp only [derivSet]
    rw [Finset.card_pair (by omega)]
  | t + 2, _, i => by
    simp only [derivSet]
    rw [Finset.card_insert_of_notMem (derivSet_not_mem_left (t + 1) (by omega) i),
      derivSet_card (t + 1) (by omega) (i + 1)]

/-- Helper: XOR-shift a configuration `x` by a finite subset `T : Finset ℤ`. -/
private def xorConfig (x : ℤ → Bool) (T : Finset ℤ) : ℤ → Bool :=
  fun j => if j ∈ T then !(x j) else x j

private lemma xorConfig_insert (x : ℤ → Bool) (a : ℤ) (T : Finset ℤ) (ha : a ∉ T) :
    xorConfig x (insert a T) = flipBit (xorConfig x T) a := by
  funext j
  simp only [xorConfig, flipBit, Finset.mem_insert]
  by_cases hj : j = a
  · subst hj; simp [ha]
  · simp [hj]

/-- Splitting a powerset sum over `insert a S` (with `a ∉ S`) into `T ⊆ S` and `insert a T`. -/
private lemma sum_powerset_insert {β : Type*} [AddCommMonoid β]
    (a : ℤ) (S : Finset ℤ) (ha : a ∉ S) (f : Finset ℤ → β) :
    ∑ T ∈ (insert a S).powerset, f T =
      ∑ T ∈ S.powerset, (f T + f (insert a T)) := by
  rw [Finset.powerset_insert, Finset.sum_union, Finset.sum_image, Finset.sum_add_distrib]
  · intro T₁ hT₁ T₂ hT₂ heq
    have h1 : a ∉ T₁ := fun h => ha (Finset.mem_powerset.mp hT₁ h)
    have h2 : a ∉ T₂ := fun h => ha (Finset.mem_powerset.mp hT₂ h)
    ext j
    by_cases hj : j = a
    · subst hj; simp [h1, h2]
    · have := Finset.ext_iff.mp heq j
      simpa [hj] using this
  · rw [Finset.disjoint_left]
    intro T hT hTim
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hTim
    exact ha (Finset.mem_powerset.mp hT (Finset.mem_insert_self a U))

/-- If `f : (ℤ → Bool) → ZMod 2` does not depend on coordinate `a ∈ S`, then its `S`-th Boolean
derivative vanishes identically. -/
private lemma sum_powerset_eq_zero_of_indep (S : Finset ℤ) (a : ℤ) (ha : a ∈ S)
    (x : ℤ → Bool) (f : (ℤ → Bool) → ZMod 2)
    (hind : ∀ y : ℤ → Bool, f (flipBit y a) = f y) :
    ∑ T ∈ S.powerset, f (xorConfig x T) = 0 := by
  have hS : S = insert a (S.erase a) := (Finset.insert_erase ha).symm
  rw [hS, sum_powerset_insert a (S.erase a) (Finset.notMem_erase a S)]
  refine Finset.sum_eq_zero fun T hT => ?_
  have haT : a ∉ T := fun h => (Finset.notMem_erase a S) (Finset.mem_powerset.mp hT h)
  rw [xorConfig_insert x a T haT, hind (xorConfig x T), zmod2_add_self]

/-- Exact `(t + 1)`-th order Boolean derivative of `t`-step Rule 30 on `derivSet t i` is `1 : ZMod 2`. -/
private lemma r30Evol_deriv_eq_one :
    ∀ t : ℕ, 1 ≤ t → ∀ (i : ℤ) (x : ℤ → Bool),
      ∑ T ∈ (derivSet t i).powerset, b2z (r30Evol (xorConfig x T) t i) = 1
  | 0, ht, _, _ => by omega
  | 1, _, i, x => by
    have hne : i ∉ ({i + 1} : Finset ℤ) := by simp
    change ∑ T ∈ (insert i ({i + 1} : Finset ℤ)).powerset, b2z (r30Evol (xorConfig x T) 1 i) = 1
    rw [sum_powerset_insert i {i + 1} hne]
    have hS1 : ({i + 1} : Finset ℤ).powerset = {∅, {i + 1}} := by
      ext T; simp [Finset.subset_singleton_iff]
    rw [hS1, Finset.sum_pair (by simp)]
    have h0 : r30Evol (xorConfig x ∅) 1 i = xor (x (i - 1)) (x i || x (i + 1)) := by
      simp [r30Evol, xorConfig]
    have h1 : r30Evol (xorConfig x (insert i ∅)) 1 i =
        xor (x (i - 1)) ((!(x i)) || x (i + 1)) := by
      simp [r30Evol, xorConfig, show i - 1 ≠ i by omega, show i + 1 ≠ i by omega]
    have h2 : r30Evol (xorConfig x {i + 1}) 1 i =
        xor (x (i - 1)) (x i || !(x (i + 1))) := by
      simp [r30Evol, xorConfig, show i - 1 ≠ i + 1 by omega, show i ≠ i + 1 by omega]
    have h3 : r30Evol (xorConfig x (insert i {i + 1})) 1 i =
        xor (x (i - 1)) ((!(x i)) || !(x (i + 1))) := by
      simp [r30Evol, xorConfig, show i - 1 ≠ i by omega, show i - 1 ≠ i + 1 by omega,
        show i ≠ i + 1 by omega, show i + 1 ≠ i by omega]
    rw [h0, h1, h2, h3]
    cases x (i - 1) <;> cases x i <;> cases x (i + 1) <;> decide
  | t + 2, _, i, x => by
    let a0 : ℤ := i - ((t + 1 : ℕ) : ℤ)
    let S : Finset ℤ := derivSet (t + 1) (i + 1)
    have ha0 : a0 ∉ S := derivSet_not_mem_left (t + 1) (by omega) i
    change ∑ T ∈ (insert a0 S).powerset, b2z (r30Evol (xorConfig x T) (t + 2) i) = 1
    rw [sum_powerset_insert a0 S ha0]
    -- Compute the directional derivative along `a0 = i - (t + 1)` at each `T ∈ S.powerset`.
    have hdiff : ∀ T ∈ S.powerset,
        b2z (r30Evol (xorConfig x T) (t + 2) i) +
          b2z (r30Evol (xorConfig x (insert a0 T)) (t + 2) i) =
        (b2z (r30Evol (xorConfig x T) (t + 1) (i - 1)) +
          b2z (r30Evol (flipBit (xorConfig x T) a0) (t + 1) (i - 1))) +
        1 + b2z (r30Evol (xorConfig x T) (t + 1) (i + 1)) := by
      intro T hT
      have haT : a0 ∉ T := fun h => ha0 (Finset.mem_powerset.mp hT h)
      rw [xorConfig_insert x a0 T haT]
      let y := xorConfig x T
      have hC : r30Evol (flipBit y a0) (t + 1) i = !(r30Evol y (t + 1) i) :=
        r30Evol_flip_left_edge y (t + 1) i
      have hR : r30Evol (flipBit y a0) (t + 1) (i + 1) = r30Evol y (t + 1) (i + 1) := by
        apply r30Evol_locality
        intro j hj1 _
        simp only [flipBit, a0]
        rw [if_neg (by push_cast; omega)]
      change b2z (xor (r30Evol y (t + 1) (i - 1)) (r30Evol y (t + 1) i || r30Evol y (t + 1) (i + 1))) +
        b2z (xor (r30Evol (flipBit y a0) (t + 1) (i - 1))
          (r30Evol (flipBit y a0) (t + 1) i || r30Evol (flipBit y a0) (t + 1) (i + 1))) = _
      rw [hC, hR]
      cases r30Evol y (t + 1) (i - 1) <;> cases r30Evol (flipBit y a0) (t + 1) (i - 1) <;>
        cases r30Evol y (t + 1) i <;> cases r30Evol y (t + 1) (i + 1) <;> decide
    rw [Finset.sum_congr rfl hdiff, Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- Term 1 vanishes because `r30Evol · (t + 1) (i - 1)` is independent of `i + (t + 2) ∈ S`!
    have hr_mem : (i + 1) + ((t + 1 : ℕ) : ℤ) ∈ S := derivSet_contains_right (t + 1) (by omega) (i + 1)
    have hterm1 : ∑ T ∈ S.powerset,
        (b2z (r30Evol (xorConfig x T) (t + 1) (i - 1)) +
          b2z (r30Evol (flipBit (xorConfig x T) a0) (t + 1) (i - 1))) = 0 := by
      apply sum_powerset_eq_zero_of_indep S ((i + 1) + ((t + 1 : ℕ) : ℤ)) hr_mem x
        (fun y => b2z (r30Evol y (t + 1) (i - 1)) + b2z (r30Evol (flipBit y a0) (t + 1) (i - 1)))
      intro y
      have h1 : r30Evol (flipBit y ((i + 1) + ((t + 1 : ℕ) : ℤ))) (t + 1) (i - 1) =
          r30Evol y (t + 1) (i - 1) := by
        apply r30Evol_locality
        intro j _ hj2
        simp only [flipBit]
        rw [if_neg (by push_cast; omega)]
      have h2 : r30Evol (flipBit (flipBit y ((i + 1) + ((t + 1 : ℕ) : ℤ))) a0) (t + 1) (i - 1) =
          r30Evol (flipBit y a0) (t + 1) (i - 1) := by
        apply r30Evol_locality
        intro j _ hj2
        simp only [flipBit, a0]
        by_cases hja : j = i - ((t + 1 : ℕ) : ℤ)
        · rw [if_pos hja, if_pos hja, if_neg (by push_cast; omega)]
        · rw [if_neg hja, if_neg hja, if_neg (by push_cast; omega)]
      rw [h1, h2]
    -- Term 2 vanishes because `S` is nonempty (so `|S.powerset|` is even)!
    have hterm2 : ∑ _T ∈ S.powerset, (1 : ZMod 2) = 0 := by
      have hS1 : S = insert ((i + 1) + ((t + 1 : ℕ) : ℤ)) (S.erase ((i + 1) + ((t + 1 : ℕ) : ℤ))) :=
        (Finset.insert_erase hr_mem).symm
      rw [hS1, sum_powerset_insert _ _ (Finset.notMem_erase _ _)]
      exact Finset.sum_eq_zero fun _ _ => zmod2_add_self 1
    -- Term 3 is `1` by induction hypothesis!
    have hterm3 : ∑ T ∈ S.powerset, b2z (r30Evol (xorConfig x T) (t + 1) (i + 1)) = 1 :=
      r30Evol_deriv_eq_one (t + 1) (by omega) (i + 1) x
    rw [hterm1, hterm2, hterm3]
    simp

/-- Any `MvPolynomial ℤ (ZMod 2)` of total degree `< S.card` has vanishing `S`-th Boolean derivative. -/
private lemma mvpoly_deriv_eq_zero_of_lt_card (P : MvPolynomial ℤ (ZMod 2)) (S : Finset ℤ)
    (hdeg : P.totalDegree < S.card) :
    ∑ T ∈ S.powerset, MvPolynomial.eval (fun j => if j ∈ T then (1 : ZMod 2) else 0) P = 0 := by
  have hmon : ∀ d ∈ P.support,
      ∑ T ∈ S.powerset, MvPolynomial.eval (fun j => if j ∈ T then (1 : ZMod 2) else 0)
        (MvPolynomial.monomial d (P.coeff d)) = 0 := by
    intro d hd
    have hcard_le : d.support.card ≤ P.totalDegree := by
      have h1 : d.support.card ≤ d.sum (fun _ e => e) := by
        rw [Finsupp.sum]
        calc d.support.card = ∑ _j ∈ d.support, (1 : ℕ) := by simp
          _ ≤ ∑ j ∈ d.support, d j := Finset.sum_le_sum fun j hj =>
              Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
      have h2 : d.sum (fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hd
      exact le_trans h1 h2
    have hlt : d.support.card < S.card := lt_of_le_of_lt hcard_le hdeg
    obtain ⟨a, haS, had⟩ : ∃ a ∈ S, a ∉ d.support := by
      by_contra hall
      push Not at hall
      have hsub : S ⊆ d.support := fun a ha => hall a ha
      exact absurd (Finset.card_le_card hsub) (not_le_of_gt hlt)
    have hda : d a = 0 := Finsupp.notMem_support_iff.mp had
    have hS : S = insert a (S.erase a) := (Finset.insert_erase haS).symm
    rw [hS, sum_powerset_insert a (S.erase a) (Finset.notMem_erase a S)]
    refine Finset.sum_eq_zero fun T hT => ?_
    have heq : MvPolynomial.eval (fun j => if j ∈ insert a T then (1 : ZMod 2) else 0)
        (MvPolynomial.monomial d (P.coeff d)) =
        MvPolynomial.eval (fun j => if j ∈ T then (1 : ZMod 2) else 0)
        (MvPolynomial.monomial d (P.coeff d)) := by
      simp only [MvPolynomial.eval_monomial, Finsupp.prod]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have hja : j ≠ a := fun h => had (h ▸ hj)
      simp [hja]
    rw [heq, zmod2_add_self]
  conv_lhs => arg 2; ext T; rw [P.as_sum, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero hmon

/-- **Theorem 27 (Exact ANF Degree Lower Bound `deg_ANF ≥ t + 1` over `𝔽₂`, PPL 096 Barrier):**
For every `t ≥ 1`, every `i : ℤ`, and every multivariate polynomial `P : MvPolynomial ℤ (ZMod 2)`
of total degree `P.totalDegree ≤ t`, `P` CANNOT compute the `t`-step Rule 30 map `x ↦ a_x(t, i)`!
In particular, any algebraic representation over `𝔽₂` of `t`-step Rule 30 requires degree `≥ t + 1`
(unbounded linear degree growth in `t`). -/
theorem ppl096_anf_degree_lower_bound (t : ℕ) (ht : 1 ≤ t) (i : ℤ)
    (P : MvPolynomial ℤ (ZMod 2)) (hdeg : P.totalDegree ≤ t) :
    ∃ x : ℤ → Bool,
      MvPolynomial.eval (fun j => if x j then (1 : ZMod 2) else 0) P ≠
        (if (Nat.rec (motive := fun _ => ℤ → Bool) x
            (fun _ row j => xor (row (j - 1)) (row j || row (j + 1))) t i)
          then (1 : ZMod 2) else 0) := by
  by_contra hall
  push Not at hall
  let S := derivSet t i
  have hcard : S.card = t + 1 := derivSet_card t ht i
  have hlt : P.totalDegree < S.card := by omega
  have hP0 := mvpoly_deriv_eq_zero_of_lt_card P S hlt
  have hR1 := r30Evol_deriv_eq_one t ht i (fun _ => false)
  have hagree : ∀ T ∈ S.powerset,
      MvPolynomial.eval (fun j => if j ∈ T then (1 : ZMod 2) else 0) P =
        b2z (r30Evol (xorConfig (fun _ => false) T) t i) := by
    intro T _
    let xT : ℤ → Bool := fun j => decide (j ∈ T)
    have hxT : xorConfig (fun _ => false) T = xT := by
      funext j; by_cases hj : j ∈ T <;> simp [xorConfig, xT, hj]
    have hev : (fun j => if xT j then (1 : ZMod 2) else 0) =
        (fun j => if j ∈ T then (1 : ZMod 2) else 0) := by
      funext j; by_cases hj : j ∈ T <;> simp [xT, hj]
    rw [hxT, ← hev]
    exact hall xT
  rw [Finset.sum_congr rfl hagree, hR1] at hP0
  exact one_ne_zero hP0

/-! ### Section 6: Exact Anti-Periodic Discrepancy, Cesàro Density Limits (`1/2`), & Row Weight Bounds (PPL 112) -/

private lemma antiperiodic_pair_sum (f : ℕ → Bool) (P : ℕ)
    (hanti : ∀ t : ℕ, f (t + P) = !(f t)) (k : ℕ) :
    ∑ t ∈ Finset.range (2 * P), (if f (k + t) then (1 : ℤ) else 0) = (P : ℤ) := by
  have hsplit : 2 * P = P + P := by omega
  rw [hsplit, Finset.sum_range_add, ← Finset.sum_add_distrib]
  have hpair : ∀ t ∈ Finset.range P,
      (if f (k + t) then (1 : ℤ) else 0) + (if f (k + (P + t)) then (1 : ℤ) else 0) = 1 := by
    intro t _
    have heq : k + (P + t) = (k + t) + P := by omega
    rw [heq, hanti (k + t)]
    cases f (k + t) <;> norm_num
  rw [Finset.sum_congr rfl hpair]
  simp

private lemma antiperiodic_discrepancy_int (f : ℕ → Bool) (P : ℕ) (hP : 1 ≤ P)
    (hanti : ∀ t : ℕ, f (t + P) = !(f t)) (N : ℕ) :
    |(2 : ℤ) * (∑ t ∈ Finset.range N, if f t then (1 : ℤ) else 0) - (N : ℤ)| ≤ (P : ℤ) := by
  have h2P : 0 < 2 * P := by omega
  set q := N / (2 * P)
  set r := N % (2 * P)
  have hN : N = q * (2 * P) + r := by
    have := Nat.div_add_mod N (2 * P)
    dsimp [q, r]
    linarith
  have hr : r < 2 * P := Nat.mod_lt N h2P
  have hfull : ∀ m : ℕ,
      ∑ t ∈ Finset.range (m * (2 * P)), (if f t then (1 : ℤ) else 0) = (m : ℤ) * (P : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : (m + 1) * (2 * P) = m * (2 * P) + 2 * P := by ring
      rw [h1, Finset.sum_range_add, ih, antiperiodic_pair_sum f P hanti (m * (2 * P))]
      push_cast; ring
  rw [hN, Finset.sum_range_add, hfull q]
  have hcancel : (2 : ℤ) * ((q : ℤ) * (P : ℤ) +
      ∑ t ∈ Finset.range r, (if f (q * (2 * P) + t) then (1 : ℤ) else 0)) -
      ((q * (2 * P) + r : ℕ) : ℤ) =
      (2 : ℤ) * (∑ t ∈ Finset.range r, if f (q * (2 * P) + t) then (1 : ℤ) else 0) - (r : ℤ) := by
    push_cast; ring
  rw [hcancel]
  by_cases hrP : r ≤ P
  · have hnonneg : (0 : ℤ) ≤ ∑ t ∈ Finset.range r, if f (q * (2 * P) + t) then (1 : ℤ) else 0 :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hle : ∑ t ∈ Finset.range r, (if f (q * (2 * P) + t) then (1 : ℤ) else 0) ≤ (r : ℤ) := by
      calc ∑ t ∈ Finset.range r, (if f (q * (2 * P) + t) then (1 : ℤ) else 0)
          ≤ ∑ _t ∈ Finset.range r, (1 : ℤ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
        _ = (r : ℤ) := by simp
    rw [abs_le]
    constructor <;> omega
  · -- When P < r < 2 * P, write r = P + s with s < P; the first `P` pairs with `[P, P+s)` leave `P - s` unpaired terms.
    set s := r - P
    have hrs : r = P + s := by omega
    have hsP : s < P := by omega
    rw [hrs, Finset.sum_range_add]
    have hsplitP : ∑ t ∈ Finset.range P, (if f (q * (2 * P) + t) then (1 : ℤ) else 0) =
        (∑ t ∈ Finset.range s, (if f (q * (2 * P) + t) then (1 : ℤ) else 0)) +
        (∑ t ∈ Finset.range (P - s), (if f (q * (2 * P) + (s + t)) then (1 : ℤ) else 0)) := by
      have hP_eq : P = s + (P - s) := by omega
      conv_lhs => arg 1; rw [hP_eq]
      rw [Finset.sum_range_add]
    have hpair_s :
        (∑ t ∈ Finset.range s, (if f (q * (2 * P) + t) then (1 : ℤ) else 0)) +
        (∑ t ∈ Finset.range s, (if f (q * (2 * P) + (P + t)) then (1 : ℤ) else 0)) = (s : ℤ) := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ t ∈ Finset.range s,
          (if f (q * (2 * P) + t) then (1 : ℤ) else 0) +
          (if f (q * (2 * P) + (P + t)) then (1 : ℤ) else 0) = 1 := by
        intro t _
        have heq : q * (2 * P) + (P + t) = (q * (2 * P) + t) + P := by omega
        rw [heq, hanti (q * (2 * P) + t)]
        cases f (q * (2 * P) + t) <;> norm_num
      rw [Finset.sum_congr rfl hterm]
      simp
    have hrem_nonneg : (0 : ℤ) ≤ ∑ t ∈ Finset.range (P - s),
        (if f (q * (2 * P) + (s + t)) then (1 : ℤ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hrem_le : ∑ t ∈ Finset.range (P - s),
        (if f (q * (2 * P) + (s + t)) then (1 : ℤ) else 0) ≤ ((P - s : ℕ) : ℤ) := by
      calc ∑ t ∈ Finset.range (P - s), (if f (q * (2 * P) + (s + t)) then (1 : ℤ) else 0)
          ≤ ∑ _t ∈ Finset.range (P - s), (1 : ℤ) :=
            Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
        _ = ((P - s : ℕ) : ℤ) := by simp
    have hsum_eq :
        (∑ t ∈ Finset.range P, (if f (q * (2 * P) + t) then (1 : ℤ) else 0)) +
        (∑ t ∈ Finset.range s, (if f (q * (2 * P) + (P + t)) then (1 : ℤ) else 0)) =
        (s : ℤ) + ∑ t ∈ Finset.range (P - s),
          (if f (q * (2 * P) + (s + t)) then (1 : ℤ) else 0) := by
      rw [hsplitP]
      linarith
    rw [hsum_eq]
    rw [abs_le]
    have hPs : ((P - s : ℕ) : ℤ) = (P : ℤ) - (s : ℤ) := by omega
    rw [hPs] at hrem_le
    push_cast
    constructor <;> linarith

/-- **Theorem 28 (Exact Half-Density & Discrepancy Bound for Anti-Periodic Sequences):**
Every anti-periodic Boolean sequence (`∀ t, f (t + P) = !(f t)`, `P ≥ 1`) satisfies the exact
discrepancy bound `|2 * S(N) - N| ≤ P` for all `N : ℕ` and has exact Cesàro density `1 / 2`. -/
theorem ppl096_antiperiodic_density_half (f : ℕ → Bool) (P : ℕ) (hP : 1 ≤ P)
    (hanti : ∀ t : ℕ, f (t + P) = !(f t)) :
    (∀ N : ℕ, |(2 : ℤ) * (∑ t ∈ Finset.range N, if f t then (1 : ℤ) else 0) - (N : ℤ)| ≤ (P : ℤ)) ∧
    Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, if f t then (1 : ℝ) else 0) / (N : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hdisc := antiperiodic_discrepancy_int f P hP hanti
  refine ⟨hdisc, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((P : ℝ) / (2 * ε))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  rw [Real.dist_eq]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 N₀) hN))
  have hcast_sum : (∑ t ∈ Finset.range N, if f t then (1 : ℝ) else 0) =
      ((∑ t ∈ Finset.range N, if f t then (1 : ℤ) else 0 : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  have hdisc_real : |(2 : ℝ) * (∑ t ∈ Finset.range N, if f t then (1 : ℝ) else 0) - (N : ℝ)| ≤ (P : ℝ) := by
    rw [hcast_sum]
    exact_mod_cast hdisc N
  have hdiv_eq : (∑ t ∈ Finset.range N, if f t then (1 : ℝ) else 0) / (N : ℝ) - 1 / 2 =
      ((2 : ℝ) * (∑ t ∈ Finset.range N, if f t then (1 : ℝ) else 0) - (N : ℝ)) / (2 * (N : ℝ)) := by
    field_simp
  rw [hdiv_eq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * (N : ℝ))]
  calc |(2 : ℝ) * (∑ t ∈ Finset.range N, if f t then (1 : ℝ) else 0) - (N : ℝ)| / (2 * (N : ℝ))
      ≤ (P : ℝ) / (2 * (N : ℝ)) := div_le_div_of_nonneg_right hdisc_real (by linarith)
    _ < ε := by
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (N : ℝ))]
        have hN_ge : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right 1 N₀) hN
        have hP_lt : (P : ℝ) < 2 * ε * (N₀ : ℝ) := by
          have := (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * ε)).mp hN₀
          linarith
        nlinarith

/-- **Theorem 29 (Exact Cesàro Density Limits on Rule 30 Diagonals, PPL 112 Contrast):**
In single-seed Rule 30:
1. Right edge `m = 0`: exact Cesàro density `→ 1`,
2. Right diagonals `m = 1, 2, 3`: exact Cesàro density `→ 1 / 2`,
3. Left diagonal `m = 3` (shifted to `t + 3`): exact Cesàro density `→ 1 / 2`. -/
theorem ppl096_right_diag_density_limits (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, if a t (t : ℤ) then (1 : ℝ) else 0) / (N : ℝ))
      atTop (nhds (1 : ℝ)) ∧
    Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, if a t ((t : ℤ) - 1) then (1 : ℝ) else 0) / (N : ℝ))
      atTop (nhds (1 / 2 : ℝ)) ∧
    Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, if a t ((t : ℤ) - 2) then (1 : ℝ) else 0) / (N : ℝ))
      atTop (nhds (1 / 2 : ℝ)) ∧
    Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, if a t ((t : ℤ) - 3) then (1 : ℝ) else 0) / (N : ℝ))
      atTop (nhds (1 / 2 : ℝ)) ∧
    Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, if a (t + 3) (-((t + 3 : ℕ) : ℤ) + 3) then (1 : ℝ) else 0) / (N : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Right edge `m = 0`: identically `1` for `N ≥ 1`.
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum : ∑ t ∈ Finset.range N, (if a t (t : ℤ) then (1 : ℝ) else 0) = (N : ℝ) := by
      have hterm : ∀ t ∈ Finset.range N, (if a t (t : ℤ) then (1 : ℝ) else 0) = 1 := by
        intro t _; rw [ppl096_right_edge a h0 hstep t]; simp
      rw [Finset.sum_congr rfl hterm]; simp
    rw [hsum, div_self (by exact_mod_cast (by omega : N ≠ 0))]
  · -- Right diagonal `m = 1`: anti-periodic of half-period `P = 1`.
    refine (ppl096_antiperiodic_density_half (fun t => a t ((t : ℤ) - 1)) 1 le_rfl ?_).2
    intro t
    rw [ppl096_right_diag_one a h0 hstep (t + 1), ppl096_right_diag_one a h0 hstep t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [Nat.add_mod, h]
  · -- Right diagonal `m = 2`: anti-periodic of half-period `P = 1`.
    refine (ppl096_antiperiodic_density_half (fun t => a t ((t : ℤ) - 2)) 1 le_rfl ?_).2
    intro t
    rw [ppl096_right_diag_two a h0 hstep (t + 1), ppl096_right_diag_two a h0 hstep t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [Nat.add_mod, h]
  · -- Right diagonal `m = 3`: anti-periodic of half-period `P = 2`.
    refine (ppl096_antiperiodic_density_half (fun t => a t ((t : ℤ) - 3)) 2 (by omega) ?_).2
    intro t
    rw [ppl096_right_diag_three a h0 hstep (t + 2), ppl096_right_diag_three a h0 hstep t]
    have hmod : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
    rcases hmod with h | h | h | h
    · simp [h, show (t + 2) % 4 = 2 by omega]
    · simp [h, show (t + 2) % 4 = 3 by omega]
    · simp [h, show (t + 2) % 4 = 0 by omega]
    · simp [h, show (t + 2) % 4 = 1 by omega]
  · -- Left diagonal `m = 3`: anti-periodic of half-period `P = 1`.
    refine (ppl096_antiperiodic_density_half
      (fun t => a (t + 3) (-((t + 3 : ℕ) : ℤ) + 3)) 1 le_rfl ?_).2
    intro t
    rw [ppl096_left_diag_three a h0 hstep (t + 1 + 3) (by omega),
      ppl096_left_diag_three a h0 hstep (t + 3) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one (t + 3) with h | h
    · simp [h, show (t + 1 + 3) % 2 = 1 by omega]
    · simp [h, show (t + 1 + 3) % 2 = 0 by omega]

/-- **Theorem 30 (Unconditional Active-Row Weight Bounds):**
In single-seed Rule 30, letting `W(t) = |{i ∈ [-t, t] | a t i = true}|`:
- For all `t ≥ 1`: `3 ≤ W(t)`,
- For all `t ≥ 2`: `W(t) ≤ 2 * t` (strictly less than the active width `2 * t + 1`),
- For all `t ≥ 4`: `4 ≤ W(t) ≤ 2 * t`. -/
theorem ppl096_row_weight_bounds (a : ℕ → ℤ → Bool)
    (h0 : ∀ i : ℤ, a 0 i = decide (i = 0))
    (hstep : ∀ t : ℕ, ∀ i : ℤ, a (t + 1) i = xor (a t (i - 1)) (a t i || a t (i + 1))) :
    (∀ t : ℕ, 1 ≤ t → 3 ≤ ((Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true)).card) ∧
    (∀ t : ℕ, 2 ≤ t → ((Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true)).card ≤ 2 * t) ∧
    (∀ t : ℕ, 4 ≤ t → 4 ≤ ((Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true)).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hsub : ({-(t : ℤ), -(t : ℤ) + 1, (t : ℤ)} : Finset ℤ) ⊆
        (Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, Finset.mem_Icc]
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨le_rfl, by omega⟩, ppl096_left_edge a h0 hstep t⟩
      · exact ⟨⟨by omega, by omega⟩, ppl096_left_diag_one a h0 hstep t ht⟩
      · exact ⟨⟨by omega, le_rfl⟩, ppl096_right_edge a h0 hstep t⟩
    have hcard : ({-(t : ℤ), -(t : ℤ) + 1, (t : ℤ)} : Finset ℤ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_pair (by omega)]
    linarith [Finset.card_le_card hsub]
  · intro t ht
    have hmem : -(t : ℤ) + 2 ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) := by
      rw [Finset.mem_Icc]; omega
    have hnot : -(t : ℤ) + 2 ∉ (Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true) := by
      rw [Finset.mem_filter]
      rintro ⟨_, htrue⟩
      rw [ppl096_left_diag_two a h0 hstep t ht] at htrue
      exact Bool.noConfusion htrue
    have hsub : (Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true) ⊆
        (Finset.Icc (-(t : ℤ)) (t : ℤ)).erase (-(t : ℤ) + 2) := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨fun h => hnot (h ▸ hx), (Finset.mem_filter.mp hx).1⟩
    have hcard : ((Finset.Icc (-(t : ℤ)) (t : ℤ)).erase (-(t : ℤ) + 2)).card = 2 * t := by
      rw [Finset.card_erase_of_mem hmem, Int.card_Icc]
      omega
    linarith [Finset.card_le_card hsub]
  · intro t ht
    have hsub : ({-(t : ℤ), -(t : ℤ) + 1, -(t : ℤ) + 4, (t : ℤ)} : Finset ℤ) ⊆
        (Finset.Icc (-(t : ℤ)) (t : ℤ)).filter (fun i => a t i = true) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, Finset.mem_Icc]
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨⟨le_rfl, by omega⟩, ppl096_left_edge a h0 hstep t⟩
      · exact ⟨⟨by omega, by omega⟩, ppl096_left_diag_one a h0 hstep t (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, ppl096_left_diag_four a h0 hstep t ht⟩
      · exact ⟨⟨by omega, le_rfl⟩, ppl096_right_edge a h0 hstep t⟩
    have hcard : ({-(t : ℤ), -(t : ℤ) + 1, -(t : ℤ) + 4, (t : ℤ)} : Finset ℤ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_pair (by omega)]
    linarith [Finset.card_le_card hsub]

end PPL096
