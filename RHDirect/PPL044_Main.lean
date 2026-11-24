/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 044 — Kimberling #1: Five Oldenburger–Kolakoski Sequence Questions

## Honest Scope Statement
This module formalizes the foundational structural theory, forbidden patterns, Carpi (1994)
cube-freeness, unconditional Chvátal-style density bounds, Dekking (1979/1997) `C^∞` smooth-word
symmetry equivalences, and the exact parity-vs-non-parity contrast (`{2a, 2b}` vs `{1, 3}` vs
`{1, 2}`) surrounding Clark Kimberling's five **LIVE-VERIFIED OPEN** Oldenburger–Kolakoski
questions (PPL 044, `$200`, `prizeproblems.org`):
- **Q1 (Formula):** Closed-form formula for `K(n)` (OPEN).
- **Q2 (Recurrence):** Does every factor of `K` recur infinitely often? (OPEN).
- **Q3 (Reversal closure):** If `w` occurs in `K`, does `w.reverse` occur in `K`? (OPEN).
- **Q4 (Swap closure):** If `w` occurs in `K`, does `w.map (3 - ·)` occur in `K`? (OPEN).
- **Q5 (Limiting frequency):** Does `lim_{N → ∞} freq_1(N) = 1/2`? (OPEN).

This module makes **no claim** to resolve any of Q1–Q5 in full generality. Instead, it delivers
a **100% unconditional, kernel-verified, pure-Mathlib-signature** formalization built completely
from scratch (`0` custom/private/`Arith4Ext` definitions exposed in any public theorem signature,
`0` `sorry`, `0` custom axioms, `0` `native_decide`).
-/

namespace PPL044

open Finset Filter Topology

/-! ## Section 1: Existence, Uniqueness & Run-Length Self-Description of `K` -/

section KolakoskiCore

private def expandFrom : ℕ → List ℕ → List ℕ
  | _, [] => []
  | b, x :: xs => List.replicate x b ++ expandFrom (3 - b) xs

private lemma swap_involution {b : ℕ} (hb : b = 1 ∨ b = 2) : 3 - (3 - b) = b := by
  rcases hb with rfl | rfl <;> rfl

private lemma swap_mem {b : ℕ} (hb : b = 1 ∨ b = 2) : 3 - b = 1 ∨ 3 - b = 2 := by
  rcases hb with rfl | rfl <;> simp

private lemma swap_ne {b : ℕ} (hb : b = 1 ∨ b = 2) : 3 - b ≠ b := by
  rcases hb with rfl | rfl <;> decide

private lemma expandFrom_eq_zipIdx_aux (b : ℕ) (hb : b = 1 ∨ b = 2) :
    ∀ (u : List ℕ) (n : ℕ),
      expandFrom (if n % 2 = 0 then b else 3 - b) u =
        (u.zipIdx n).flatMap (fun p => List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b))
  | [], _ => rfl
  | x :: xs, n => by
    simp only [expandFrom, List.zipIdx_cons, List.flatMap_cons]
    congr 1
    have hstep : 3 - (if n % 2 = 0 then b else 3 - b) =
        if (n + 1) % 2 = 0 then b else 3 - b := by
      rcases hb with rfl | rfl <;> split_ifs <;> omega
    rw [hstep]
    exact expandFrom_eq_zipIdx_aux b hb xs (n + 1)

private lemma expandFrom_eq_zipIdx (b : ℕ) (hb : b = 1 ∨ b = 2) (u : List ℕ) :
    expandFrom b u =
      u.zipIdx.flatMap (fun p => List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b)) := by
  simpa using expandFrom_eq_zipIdx_aux b hb u 0

private lemma expandFrom_append (b : ℕ) (hb : b = 1 ∨ b = 2) :
    ∀ (u v : List ℕ),
      expandFrom b (u ++ v) =
        expandFrom b u ++ expandFrom (if u.length % 2 = 0 then b else 3 - b) v
  | [], v => by simp [expandFrom]
  | x :: xs, v => by
    simp only [List.cons_append, expandFrom, List.append_assoc, List.length_cons]
    congr 1
    rw [expandFrom_append (3 - b) (swap_mem hb) xs v]
    congr 1
    have hflip : (if xs.length % 2 = 0 then 3 - b else 3 - (3 - b)) =
        if (xs.length + 1) % 2 = 0 then b else 3 - b := by
      rcases hb with rfl | rfl <;> split_ifs <;> omega
    rw [hflip]

private lemma expandFrom_length : ∀ (b : ℕ) (u : List ℕ), (expandFrom b u).length = u.sum
  | _, [] => rfl
  | b, x :: xs => by
    simp [expandFrom, expandFrom_length (3 - b) xs]

private lemma expandFrom_prefix {b : ℕ} (hb : b = 1 ∨ b = 2) {u v : List ℕ} (h : u <+: v) :
    expandFrom b u <+: expandFrom b v := by
  rcases h with ⟨t, rfl⟩
  rw [expandFrom_append b hb]
  exact ⟨_, rfl⟩

private lemma expandFrom_infix {b : ℕ} (hb : b = 1 ∨ b = 2) {u v : List ℕ} (h : u <:+: v) :
    ∃ b', (b' = 1 ∨ b' = 2) ∧ expandFrom b' u <:+: expandFrom b v := by
  rcases h with ⟨p, s, rfl⟩
  let b' := if p.length % 2 = 0 then b else 3 - b
  have hb' : b' = 1 ∨ b' = 2 := by unfold b'; split_ifs; exact hb; exact swap_mem hb
  rw [List.append_assoc, expandFrom_append b hb, expandFrom_append b' hb']
  exact ⟨b', hb', ⟨expandFrom b p, expandFrom (if u.length % 2 = 0 then b' else 3 - b') s,
    by simp [List.append_assoc]⟩⟩

private lemma list_ofFn_sum (f : ℕ → ℕ) (m : ℕ) :
    (List.ofFn (fun j : Fin m => f j)).sum = ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]

private lemma expandFrom_mem :
    ∀ (b : ℕ), (b = 1 ∨ b = 2) → ∀ (u : List ℕ) (x : ℕ), x ∈ expandFrom b u → x = 1 ∨ x = 2
  | _, _, [], _, hx => by simp [expandFrom] at hx
  | b, hb, a :: xs, x, hx => by
    simp only [expandFrom, List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · exact hb
    · exact expandFrom_mem (3 - b) (swap_mem hb) xs x hx

private lemma expandFrom_map_swap :
    ∀ (b : ℕ), (b = 1 ∨ b = 2) → ∀ (u : List ℕ),
      (expandFrom b u).map (fun x => 3 - x) = expandFrom (3 - b) u
  | _, _, [] => rfl
  | b, hb, a :: xs => by
    simp only [expandFrom, List.map_append, List.map_replicate]
    rw [expandFrom_map_swap (3 - b) (swap_mem hb) xs, swap_involution hb]

private lemma expandFrom_reverse (b : ℕ) (hb : b = 1 ∨ b = 2) :
    ∀ (u : List ℕ),
      (expandFrom b u).reverse =
        expandFrom (if u.length % 2 = 0 then 3 - b else b) u.reverse
  | [] => rfl
  | a :: xs => by
    simp only [expandFrom, List.reverse_append, List.reverse_replicate, List.reverse_cons,
      List.length_cons]
    rw [expandFrom_append (if (xs.length + 1) % 2 = 0 then 3 - b else b)
      (by split_ifs; exact swap_mem hb; exact hb)]
    rw [expandFrom_reverse (3 - b) (swap_mem hb) xs]
    have h1 : (if xs.length % 2 = 0 then 3 - (3 - b) else 3 - b) =
        if (xs.length + 1) % 2 = 0 then 3 - b else b := by
      rcases hb with rfl | rfl <;> split_ifs <;> omega
    have h2 : (if xs.reverse.length % 2 = 0 then
          (if (xs.length + 1) % 2 = 0 then 3 - b else b)
        else 3 - (if (xs.length + 1) % 2 = 0 then 3 - b else b)) = b := by
      rw [List.length_reverse]
      rcases hb with rfl | rfl <;> split_ifs <;> omega
    rw [h1, h2]
    simp [expandFrom]

private lemma expandFrom_getElem_run (b : ℕ) (hb : b = 1 ∨ b = 2) (u : List ℕ)
    (k : ℕ) (hk : k < u.length) (j : ℕ) (hj : j < u[k]) :
    ∃ hlt : (u.take k).sum + j < (expandFrom b u).length,
      (expandFrom b u)[(u.take k).sum + j]'hlt = if k % 2 = 0 then b else 3 - b := by
  have hsplit : u = u.take k ++ u[k] :: u.drop (k + 1) := by
    have h1 := (List.take_append_drop k u).symm
    have h2 : u.drop k = u[k] :: u.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    exact h1
  have hlen_take : (u.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have hexp : expandFrom b u =
      expandFrom b (u.take k) ++
        (List.replicate u[k] (if k % 2 = 0 then b else 3 - b) ++
          expandFrom (3 - (if k % 2 = 0 then b else 3 - b)) (u.drop (k + 1))) := by
    conv_lhs => rw [hsplit]
    rw [expandFrom_append b hb, hlen_take]
    rfl
  have hlt_rep : j < (List.replicate u[k] (if k % 2 = 0 then b else 3 - b)).length := by
    simpa using hj
  have hlt : (u.take k).sum + j < (expandFrom b u).length := by
    rw [hexp, List.length_append, expandFrom_length, List.length_append]
    omega
  refine ⟨hlt, ?_⟩
  have hget : (expandFrom b u)[(u.take k).sum + j]'hlt =
      (expandFrom b (u.take k) ++
        (List.replicate u[k] (if k % 2 = 0 then b else 3 - b) ++
          expandFrom (3 - (if k % 2 = 0 then b else 3 - b)) (u.drop (k + 1))))[(u.take k).sum + j]'(by
            rwa [← hexp]) := by
    simp [hexp]
  rw [hget]
  have hle : (expandFrom b (u.take k)).length ≤ (u.take k).sum + j := by
    rw [expandFrom_length]; omega
  rw [List.getElem_append_right hle]
  have hidx : (u.take k).sum + j - (expandFrom b (u.take k)).length = j := by
    rw [expandFrom_length]; omega
  simp only [hidx]
  rw [List.getElem_append_left hlt_rep]
  simp

private def kolPrefix : ℕ → List ℕ
  | 0 => [1, 2]
  | m + 1 => expandFrom 1 (kolPrefix m)

private lemma kolPrefix_mem : ∀ m x, x ∈ kolPrefix m → x = 1 ∨ x = 2
  | 0, x, hx => by simp [kolPrefix] at hx; exact hx
  | m + 1, x, hx => expandFrom_mem 1 (Or.inl rfl) (kolPrefix m) x hx

private lemma kolPrefix_prefix_succ : ∀ m, kolPrefix m <+: kolPrefix (m + 1)
  | 0 => ⟨[2], by rfl⟩
  | m + 1 => expandFrom_prefix (Or.inl rfl) (kolPrefix_prefix_succ m)

private lemma kolPrefix_prefix_le {m n : ℕ} (h : m ≤ n) : kolPrefix m <+: kolPrefix n := by
  induction h with
  | refl => exact List.prefix_refl _
  | @step k _ ih => exact ih.trans (kolPrefix_prefix_succ k)

private lemma list_sum_ge_length : ∀ (l : List ℕ), (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum
  | [], _ => le_refl 0
  | x :: xs, h => by
    have hx : 1 ≤ x := h x (List.mem_cons_self ..)
    have hxs : xs.length ≤ xs.sum :=
      list_sum_ge_length xs (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.length_cons, List.sum_cons]
    omega

private lemma kolPrefix_length_ge : ∀ m, m + 2 ≤ (kolPrefix m).length
  | 0 => by decide
  | m + 1 => by
    have ih := kolPrefix_length_ge m
    have hpre : [1, 2] <+: kolPrefix m := kolPrefix_prefix_le (Nat.zero_le m)
    rcases hpre with ⟨t, ht⟩
    have hpos : ∀ x ∈ t, 1 ≤ x := by
      intro x hx
      have hmem : x ∈ kolPrefix m := by rw [← ht]; simp [hx]
      rcases kolPrefix_mem m x hmem with rfl | rfl <;> omega
    have htsum := list_sum_ge_length t hpos
    have hlen_m : (kolPrefix m).length = 2 + t.length := by
      rw [← ht]; simp; omega
    have hsum_m : (kolPrefix m).sum = 3 + t.sum := by
      rw [← ht]; simp; omega
    simp only [kolPrefix, expandFrom_length]
    omega

private def kolSeq (n : ℕ) : ℕ :=
  (kolPrefix n)[n]'(by have := kolPrefix_length_ge n; omega)

private lemma kolPrefix_getElem {m n : ℕ} (hn : n < (kolPrefix m).length) :
    (kolPrefix m)[n]'hn = kolSeq n := by
  unfold kolSeq
  rcases le_total m n with hle | hle
  · have hpre := kolPrefix_prefix_le hle
    exact List.IsPrefix.getElem hpre hn
  · have hpre := kolPrefix_prefix_le hle
    exact (List.IsPrefix.getElem hpre (by have := kolPrefix_length_ge n; omega)).symm

private lemma kolSeq_mem (n : ℕ) : kolSeq n = 1 ∨ kolSeq n = 2 := by
  apply kolPrefix_mem n
  exact List.getElem_mem _

private lemma kolSeq_pos (n : ℕ) : 1 ≤ kolSeq n := by
  rcases kolSeq_mem n with h | h <;> omega

private lemma kolPrefix_take_sum (m k : ℕ) (hk : k ≤ (kolPrefix m).length) :
    ((kolPrefix m).take k).sum = ∑ i ∈ Finset.range k, kolSeq i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : k < (kolPrefix m).length := by omega
    rw [List.take_succ_eq_append_getElem hlt, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, ih (by omega), kolPrefix_getElem hlt]

private lemma kolSeq_run_spec (k j : ℕ) (hj : j < kolSeq k) :
    kolSeq ((∑ i ∈ Finset.range k, kolSeq i) + j) = if k % 2 = 0 then 1 else 2 := by
  have hk : k < (kolPrefix k).length := by have := kolPrefix_length_ge k; omega
  have hj' : j < (kolPrefix k)[k]'hk := by rwa [kolPrefix_getElem hk]
  obtain ⟨hlt, hget⟩ := expandFrom_getElem_run 1 (Or.inl rfl) (kolPrefix k) k hk j hj'
  have hsum := kolPrefix_take_sum k k (Nat.le_of_lt hk)
  have hlt' : (∑ i ∈ Finset.range k, kolSeq i) + j < (kolPrefix (k + 1)).length := by
    simpa [kolPrefix, hsum] using hlt
  rw [← kolPrefix_getElem hlt']
  simpa [kolPrefix, hsum] using hget

private lemma kol_run_spec_zero {K : ℕ → ℕ}
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k → K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    K 0 = 1 := by
  simpa using hspec 0 0 (hpos 0)

private lemma kol_run_spec_one {K : ℕ → ℕ}
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k → K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    K 1 = 2 := by
  have h0 := kol_run_spec_zero hpos hspec
  have h1 := hspec 1 0 (hpos 1)
  simpa [Finset.sum_range_one, h0] using h1

private lemma kol_run_spec_two {K : ℕ → ℕ}
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k → K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    K 2 = 2 := by
  have h0 := kol_run_spec_zero hpos hspec
  have h1 := kol_run_spec_one hpos hspec
  have h2 := hspec 1 1 (by omega)
  simpa [Finset.sum_range_one, h0] using h2

private lemma sum_ge_self_of_pos {K : ℕ → ℕ} (hpos : ∀ n, 1 ≤ K n) :
    ∀ k, k ≤ ∑ i ∈ Finset.range k, K i
  | 0 => le_refl 0
  | k + 1 => by
    rw [Finset.sum_range_succ]
    have := sum_ge_self_of_pos hpos k
    have := hpos k
    omega

private lemma sum_strict_mono_of_pos {K : ℕ → ℕ} (hpos : ∀ n, 1 ≤ K n) :
    StrictMono (fun k => ∑ i ∈ Finset.range k, K i) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  rw [Finset.sum_range_succ]
  have := hpos k
  omega

private lemma exists_run_index {K : ℕ → ℕ} (hpos : ∀ n, 1 ≤ K n) (n : ℕ) :
    ∃ k, (∑ i ∈ Finset.range k, K i) ≤ n ∧ n < ∑ i ∈ Finset.range (k + 1), K i := by
  have hreach : ∃ m, n < ∑ i ∈ Finset.range m, K i :=
    ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (sum_ge_self_of_pos hpos (n + 1))⟩
  let m := Nat.find hreach
  have hm : n < ∑ i ∈ Finset.range m, K i := Nat.find_spec hreach
  have hm0 : m ≠ 0 := by
    intro h0
    simp [h0] at hm
  refine ⟨m - 1, ?_, ?_⟩
  · have hlt : m - 1 < m := Nat.sub_lt (Nat.pos_of_ne_zero hm0) Nat.one_pos
    have hnot := Nat.find_min hreach hlt
    omega
  · rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]

private lemma sum_ge_succ_of_two {K : ℕ → ℕ}
    (hpos : ∀ n, 1 ≤ K n) (h0 : K 0 = 1) (h1 : K 1 = 2) :
    ∀ k, 2 ≤ k → k + 1 ≤ ∑ i ∈ Finset.range k, K i := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with heq | hlt
    · have hk1 : k = 1 := by omega
      subst hk1
      simp [Finset.sum_range_succ, h0, h1]
    · rw [Finset.sum_range_succ]
      have := ih (by omega)
      have := hpos k
      omega

private lemma kol_unique {K : ℕ → ℕ}
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k → K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    K = kolSeq := by
  have h0 := kol_run_spec_zero hpos hspec
  have h1 := kol_run_spec_one hpos hspec
  have h2 := kol_run_spec_two hpos hspec
  have h0' := kol_run_spec_zero kolSeq_pos kolSeq_run_spec
  have h1' := kol_run_spec_one kolSeq_pos kolSeq_run_spec
  have h2' := kol_run_spec_two kolSeq_pos kolSeq_run_spec
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · interval_cases n <;> omega
    · obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos n
      have hS2 : ∑ i ∈ Finset.range 2, K i = 3 := by
        simp [Finset.sum_range_succ, h0, h1]
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk_le : k + 1 ≤ 2 := by omega
        have hmono : ∑ i ∈ Finset.range (k + 1), K i ≤ ∑ i ∈ Finset.range 2, K i :=
          (sum_strict_mono_of_pos hpos).monotone hk_le
        omega
      have hk_lt_n : k < n := by
        have := sum_ge_succ_of_two hpos h0 h1 k hk2
        omega
      have hsum_eq : ∑ i ∈ Finset.range k, K i = ∑ i ∈ Finset.range k, kolSeq i := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        exact ih i (lt_trans (Finset.mem_range.mp hi) hk_lt_n)
      have hKk_eq : K k = kolSeq k := ih k hk_lt_n
      let j := n - ∑ i ∈ Finset.range k, K i
      have hj_lt : j < K k := by
        rw [Finset.sum_range_succ] at hhi
        omega
      have hn_eq : (∑ i ∈ Finset.range k, K i) + j = n := Nat.add_sub_of_le hlo
      have hLHS : K n = if k % 2 = 0 then 1 else 2 := by
        rw [← hn_eq]
        exact hspec k j hj_lt
      have hRHS : kolSeq n = if k % 2 = 0 then 1 else 2 := by
        rw [← hn_eq, hsum_eq]
        exact kolSeq_run_spec k j (by omega)
      rw [hLHS, hRHS]

private lemma kolPrefix7_val :
    kolPrefix 7 =
      [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2,
       1, 1, 2, 1] := rfl

private lemma kolSeq_first30 :
    List.ofFn (fun i : Fin 30 => kolSeq i) =
      [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2] := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_ofFn] at hi1
    rw [List.getElem_ofFn]
    have hlt : i < (kolPrefix 7).length := by rw [kolPrefix7_val]; simp; omega
    rw [← kolPrefix_getElem hlt]
    have hEq : (kolPrefix 7).take 30 =
        [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2] := rfl
    have h1 : (kolPrefix 7)[i]'hlt = ((kolPrefix 7).take 30)[i]'(by rw [hEq]; exact hi2) := by
      simp [List.getElem_take]
    rw [h1]
    simp [hEq]

end KolakoskiCore

/-- **Theorem 1.1 (Existence & Uniqueness of the Classical Kolakoski Sequence).**
There exists a unique sequence `K : ℕ → ℕ` of positive integers whose `k`-th alternating run
over `{1, 2}` has length `K k` (starting with `1` at `k = 0`). -/
theorem ppl044_kolakoski_exists_unique :
    ∃! K : ℕ → ℕ,
      (∀ n, 1 ≤ K n) ∧
      (∀ k j, j < K k →
        K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) := by
  refine ⟨kolSeq, ⟨kolSeq_pos, kolSeq_run_spec⟩, ?_⟩
  rintro K ⟨hpos, hspec⟩
  exact kol_unique hpos hspec

/-- **Theorem 1.2 (Alphabet `{1, 2}` & Kernel-Certified First 30 Values).**
Every sequence satisfying the Kolakoski run-length self-description takes values strictly in
`{1, 2}`, satisfies `K 0 = 1, K 1 = 2`, and agrees with the exact first 30 terms of OEIS A000002
(certified by kernel reduction with `0` `native_decide`). -/
theorem ppl044_kolakoski_values_and_alphabet (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    K 0 = 1 ∧ K 1 = 2 ∧ (∀ n, K n = 1 ∨ K n = 2) ∧
    List.ofFn (fun i : Fin 30 => K i) =
      [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2] := by
  have hK := kol_unique hpos hspec; subst hK
  exact ⟨kol_run_spec_zero kolSeq_pos kolSeq_run_spec,
    kol_run_spec_one kolSeq_pos kolSeq_run_spec,
    kolSeq_mem, kolSeq_first30⟩

/-- **Theorem 1.3 (Maximal Run Boundaries of `K`).**
Every run `[S(k), S(k+1))` of the Kolakoski sequence `K` is maximal: the symbol immediately
after `S(k+1)` (and immediately before `S(k)` for `k > 0`) strictly differs from the `k`-th run
symbol. -/
theorem ppl044_kolakoski_run_maximality (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    (∀ k, K (∑ i ∈ Finset.range (k + 1), K i) ≠ if k % 2 = 0 then 1 else 2) ∧
    (∀ k, 0 < k → K ((∑ i ∈ Finset.range k, K i) - 1) ≠ if k % 2 = 0 then 1 else 2) := by
  constructor
  · intro k
    have hnext := hspec (k + 1) 0 (hpos (k + 1))
    simp only [add_zero] at hnext
    rw [hnext]
    split_ifs <;> omega
  · intro k hk
    have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    have hprev := hspec (k - 1) (K (k - 1) - 1) (Nat.sub_lt (hpos (k - 1)) Nat.one_pos)
    have hidx : (∑ i ∈ Finset.range (k - 1), K i) + (K (k - 1) - 1) =
        (∑ i ∈ Finset.range k, K i) - 1 := by
      conv_rhs => rw [hk', Finset.sum_range_succ]
      have := hpos (k - 1)
      omega
    rw [hidx] at hprev
    rw [hprev]
    split_ifs <;> omega

/-- **Theorem 1.4 (Exact Prefix Self-Description under Run-Length Expansion).**
For every `m : ℕ`, the prefix `K[0 .. ∑_{j < m} K(j))` is identically the run-length expansion
of the prefix `K[0 .. m)`. -/
theorem ppl044_kolakoski_prefix_expansion (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2)
    (m : ℕ) :
    List.ofFn (fun i : Fin (∑ j ∈ Finset.range m, K j) => K i) =
      (List.ofFn (fun j : Fin m => K j)).zipIdx.flatMap
        (fun p => List.replicate p.1 (if p.2 % 2 = 0 then 1 else 2)) := by
  have hK := kol_unique hpos hspec; subst hK
  rw [← expandFrom_eq_zipIdx 1 (Or.inl rfl)]
  have hsum_ofFn : (List.ofFn (fun j : Fin m => kolSeq j)).sum =
      ∑ j ∈ Finset.range m, kolSeq j := list_ofFn_sum kolSeq m
  apply List.ext_getElem
  · rw [List.length_ofFn, expandFrom_length, hsum_ofFn]
  · intro n hn1 hn2
    rw [List.length_ofFn] at hn1
    rw [List.getElem_ofFn]
    obtain ⟨k, hlo, hhi⟩ := exists_run_index kolSeq_pos n
    have hkm : k < m := by
      by_contra hge
      have hle : ∑ j ∈ Finset.range m, kolSeq j ≤ ∑ j ∈ Finset.range k, kolSeq j :=
        (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
      omega
    let u := List.ofFn (fun j : Fin m => kolSeq j)
    have hku : k < u.length := by simpa [u] using hkm
    have hj : n - ∑ j ∈ Finset.range k, kolSeq j < u[k]'hku := by
      rw [Finset.sum_range_succ] at hhi
      simp only [u, List.getElem_ofFn]
      omega
    have htake : (u.take k).sum = ∑ j ∈ Finset.range k, kolSeq j := by
      have ht : u.take k = List.ofFn (fun j : Fin k => kolSeq j) := by
        apply List.ext_getElem
        · simp [u, Nat.le_of_lt hkm]
        · intro i hi1 hi2
          simp [u]
      rw [ht]
      exact list_ofFn_sum kolSeq k
    obtain ⟨hlt, hget⟩ := expandFrom_getElem_run 1 (Or.inl rfl) u k hku
      (n - ∑ j ∈ Finset.range k, kolSeq j) hj
    have hn_eq : (u.take k).sum + (n - ∑ j ∈ Finset.range k, kolSeq j) = n := by
      rw [htake]; exact Nat.add_sub_of_le hlo
    have hK := kolSeq_run_spec k (n - ∑ j ∈ Finset.range k, kolSeq j) (by
      simpa [u, List.getElem_ofFn] using hj)
    rw [Nat.add_sub_of_le hlo] at hK
    rw [hK]
    have hRHS : (expandFrom 1 u)[n]'hn2 = (expandFrom 1 u)[(u.take k).sum + (n - ∑ j ∈ Finset.range k, kolSeq j)]'hlt := by
      congr 1; exact hn_eq.symm
    rw [hRHS, hget]

/-- **Theorem 1.5 (Shifted `{2, 1}` Self-Description).**
Deleting the initial `K 0 = 1` yields the shifted sequence `n ↦ K (n + 1)` starting `2, 2, 1, 1, ...`,
which is self-describing with alternating run symbols `2, 1, 2, 1, ...`. -/
theorem ppl044_kolakoski_shift_self_describing (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    (∀ n, K (n + 1) = 1 ∨ K (n + 1) = 2) ∧
    (∀ k j, j < K (k + 1) →
      K (((∑ i ∈ Finset.range k, K (i + 1)) + j) + 1) = if k % 2 = 0 then 2 else 1) := by
  have h0 := kol_run_spec_zero hpos hspec
  have hK := kol_unique hpos hspec; subst hK
  refine ⟨fun n => kolSeq_mem (n + 1), fun k j hj => ?_⟩
  have hsum : ∑ i ∈ Finset.range (k + 1), kolSeq i =
      1 + ∑ i ∈ Finset.range k, kolSeq (i + 1) := by
    rw [Finset.sum_range_succ', h0, add_comm]
  have hrun := kolSeq_run_spec (k + 1) j hj
  rw [hsum] at hrun
  have hidx : 1 + (∑ i ∈ Finset.range k, kolSeq (i + 1)) + j =
      ((∑ i ∈ Finset.range k, kolSeq (i + 1)) + j) + 1 := by omega
  rw [hidx] at hrun
  rw [hrun]
  split_ifs <;> omega

/-! ## Section 2: Local Forbidden Patterns, Derivative Invariance & Carpi (1994) Cube-Freeness -/

section ForbiddenAndCarpi

private lemma run_index_unique {K : ℕ → ℕ} (hpos : ∀ n, 1 ≤ K n) {k₁ k₂ n : ℕ}
    (h1lo : ∑ i ∈ Finset.range k₁, K i ≤ n) (h1hi : n < ∑ i ∈ Finset.range (k₁ + 1), K i)
    (h2lo : ∑ i ∈ Finset.range k₂, K i ≤ n) (h2hi : n < ∑ i ∈ Finset.range (k₂ + 1), K i) :
    k₁ = k₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : ∑ i ∈ Finset.range (k₁ + 1), K i ≤ ∑ i ∈ Finset.range k₂, K i :=
      (sum_strict_mono_of_pos hpos).monotone hlt
    omega
  · have hle : ∑ i ∈ Finset.range (k₂ + 1), K i ≤ ∑ i ∈ Finset.range k₁, K i :=
      (sum_strict_mono_of_pos hpos).monotone hgt
    omega

private lemma kolSeq_run_value (k n : ℕ)
    (hlo : ∑ i ∈ Finset.range k, kolSeq i ≤ n)
    (hhi : n < ∑ i ∈ Finset.range (k + 1), kolSeq i) :
    kolSeq n = if k % 2 = 0 then 1 else 2 := by
  have hj : n - ∑ i ∈ Finset.range k, kolSeq i < kolSeq k := by
    rw [Finset.sum_range_succ] at hhi; omega
  have h := kolSeq_run_spec k (n - ∑ i ∈ Finset.range k, kolSeq i) hj
  rwa [Nat.add_sub_of_le hlo] at h

private lemma kolSeq_no_triple (i : ℕ) :
    ¬ (kolSeq i = kolSeq (i + 1) ∧ kolSeq (i + 1) = kolSeq (i + 2)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨k, hlo, hhi⟩ := exists_run_index kolSeq_pos i
  have hval_i := kolSeq_run_value k i hlo hhi
  have hle2 : kolSeq k ≤ 2 := by rcases kolSeq_mem k with h | h <;> omega
  rw [Finset.sum_range_succ] at hhi
  have hS1_eq : ∑ j ∈ Finset.range (k + 1), kolSeq j =
      (∑ j ∈ Finset.range k, kolSeq j) + kolSeq k := Finset.sum_range_succ _ _
  have hnext : kolSeq (∑ j ∈ Finset.range (k + 1), kolSeq j) ≠ if k % 2 = 0 then 1 else 2 := by
    have hn := kolSeq_run_spec (k + 1) 0 (kolSeq_pos (k + 1))
    simp only [add_zero] at hn
    rw [hn]; split_ifs <;> omega
  have hgap : (∑ j ∈ Finset.range (k + 1), kolSeq j) = i + 1 ∨
      (∑ j ∈ Finset.range (k + 1), kolSeq j) = i + 2 := by omega
  rcases hgap with hg | hg
  · rw [hg, ← h1, hval_i] at hnext; exact hnext rfl
  · rw [hg, ← h2, ← h1, hval_i] at hnext; exact hnext rfl

private lemma kolSeq_singleton_run {i : ℕ}
    (hL : kolSeq i ≠ kolSeq (i + 1)) (hR : kolSeq (i + 1) ≠ kolSeq (i + 2)) :
    ∃ k, ∑ j ∈ Finset.range k, kolSeq j = i + 1 ∧ kolSeq k = 1 := by
  obtain ⟨k, hlo, hhi⟩ := exists_run_index kolSeq_pos (i + 1)
  have hval := kolSeq_run_value k (i + 1) hlo hhi
  have hstart : ∑ j ∈ Finset.range k, kolSeq j = i + 1 := by
    by_contra hne
    have hlo_i : ∑ j ∈ Finset.range k, kolSeq j ≤ i := by omega
    have hhi_i : i < ∑ j ∈ Finset.range (k + 1), kolSeq j := by omega
    have hval_i := kolSeq_run_value k i hlo_i hhi_i
    exact hL (hval_i.trans hval.symm)
  have hlen : kolSeq k = 1 := by
    rcases kolSeq_mem k with h1 | h2
    · exact h1
    · exfalso
      have hlo2 : ∑ j ∈ Finset.range k, kolSeq j ≤ i + 2 := by omega
      have hhi2 : i + 2 < ∑ j ∈ Finset.range (k + 1), kolSeq j := by
        rw [Finset.sum_range_succ, hstart, h2]; omega
      have hval2 := kolSeq_run_value k (i + 2) hlo2 hhi2
      exact hR (hval.trans hval2.symm)
  exact ⟨k, hstart, hlen⟩

private lemma kolSeq_no_alt5 (i : ℕ) :
    List.ofFn (fun j : Fin 5 => kolSeq (i + j)) ≠ [1, 2, 1, 2, 1] ∧
    List.ofFn (fun j : Fin 5 => kolSeq (i + j)) ≠ [2, 1, 2, 1, 2] := by
  have hgen : ∀ a b : ℕ, a ≠ b →
      List.ofFn (fun j : Fin 5 => kolSeq (i + j)) ≠ [a, b, a, b, a] := by
    intro a b hab heq
    have hget : ∀ m (hm : m < 5), kolSeq (i + m) = ([a, b, a, b, a])[m] := by
      intro m hm
      have h1 := congrArg (fun l => l[m]?) heq
      rw [List.getElem?_eq_getElem (by simp; exact hm), List.getElem_ofFn,
          List.getElem?_eq_getElem (by simp; exact hm)] at h1
      exact Option.some.inj h1
    have h0 := hget 0 (by omega)
    have h1 := hget 1 (by omega)
    have h2 := hget 2 (by omega)
    have h3 := hget 3 (by omega)
    have h4 := hget 4 (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, add_zero] at h0 h1 h2 h3 h4
    obtain ⟨k1, hs1, hl1⟩ := kolSeq_singleton_run (i := i)
      (by rw [h0, h1]; exact hab) (by rw [h1, h2]; exact hab.symm)
    obtain ⟨k2, hs2, hl2⟩ := kolSeq_singleton_run (i := i + 1)
      (by rw [h1, h2]; exact hab.symm) (by rw [h2, h3]; exact hab)
    obtain ⟨k3, hs3, hl3⟩ := kolSeq_singleton_run (i := i + 2)
      (by rw [h2, h3]; exact hab) (by rw [h3, h4]; exact hab.symm)
    have hk2 : k2 = k1 + 1 := by
      have hnext : ∑ j ∈ Finset.range (k1 + 1), kolSeq j = i + 2 := by
        rw [Finset.sum_range_succ, hs1, hl1]
      exact (sum_strict_mono_of_pos kolSeq_pos).injective (by omega)
    have hk3 : k3 = k1 + 2 := by
      have hnext : ∑ j ∈ Finset.range (k2 + 1), kolSeq j = i + 3 := by
        rw [Finset.sum_range_succ, hs2, hl2]
      have : k3 = k2 + 1 := (sum_strict_mono_of_pos kolSeq_pos).injective (by omega)
      omega
    rw [hk2] at hl2
    rw [hk3] at hl3
    exact kolSeq_no_triple k1 ⟨by omega, by omega⟩
  exact ⟨hgen 1 2 (by decide), hgen 2 1 (by decide)⟩

private lemma kolSeq_double_run {i : ℕ} (heq : kolSeq i = kolSeq (i + 1)) :
    ∃ k, ∑ j ∈ Finset.range k, kolSeq j = i ∧ kolSeq k = 2 := by
  obtain ⟨k, hlo, hhi⟩ := exists_run_index kolSeq_pos i
  have hval := kolSeq_run_value k i hlo hhi
  have hlen2 : kolSeq k = 2 := by
    rcases kolSeq_mem k with h1 | h2
    · exfalso
      have hnext : ∑ j ∈ Finset.range (k + 1), kolSeq j = i + 1 := by
        rw [Finset.sum_range_succ] at hhi ⊢; omega
      have hval1 := kolSeq_run_spec (k + 1) 0 (kolSeq_pos (k + 1))
      simp only [add_zero, hnext] at hval1
      rw [hval, hval1] at heq
      split_ifs at heq <;> omega
    · exact h2
  have hstart : ∑ j ∈ Finset.range k, kolSeq j = i := by
    by_contra hne
    have hhi1 : ∑ j ∈ Finset.range (k + 1), kolSeq j = i + 1 := by
      rw [Finset.sum_range_succ] at hhi ⊢; omega
    have hval1 := kolSeq_run_spec (k + 1) 0 (kolSeq_pos (k + 1))
    simp only [add_zero, hhi1] at hval1
    rw [hval, hval1] at heq
    split_ifs at heq <;> omega
  exact ⟨k, hstart, hlen2⟩

private lemma kolSeq_no_double_triple (i : ℕ) :
    List.ofFn (fun j : Fin 6 => kolSeq (i + j)) ≠ [1, 1, 2, 2, 1, 1] ∧
    List.ofFn (fun j : Fin 6 => kolSeq (i + j)) ≠ [2, 2, 1, 1, 2, 2] := by
  have hgen : ∀ a b : ℕ, a ≠ b →
      List.ofFn (fun j : Fin 6 => kolSeq (i + j)) ≠ [a, a, b, b, a, a] := by
    intro a b _ heq
    have hget : ∀ m (hm : m < 6), kolSeq (i + m) = ([a, a, b, b, a, a])[m] := by
      intro m hm
      have h1 := congrArg (fun l => l[m]?) heq
      rw [List.getElem?_eq_getElem (by simp; exact hm), List.getElem_ofFn,
          List.getElem?_eq_getElem (by simp; exact hm)] at h1
      exact Option.some.inj h1
    have h0 := hget 0 (by omega)
    have h1 := hget 1 (by omega)
    have h2 := hget 2 (by omega)
    have h3 := hget 3 (by omega)
    have h4 := hget 4 (by omega)
    have h5 := hget 5 (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, add_zero] at h0 h1 h2 h3 h4 h5
    obtain ⟨k1, hs1, hl1⟩ := kolSeq_double_run (i := i) (by omega)
    obtain ⟨k2, hs2, hl2⟩ := kolSeq_double_run (i := i + 2) (by
      have : i + 2 + 1 = i + 3 := by omega
      rw [this]; omega)
    obtain ⟨k3, hs3, hl3⟩ := kolSeq_double_run (i := i + 4) (by
      have : i + 4 + 1 = i + 5 := by omega
      rw [this]; omega)
    have hk2 : k2 = k1 + 1 := by
      have : ∑ j ∈ Finset.range (k1 + 1), kolSeq j = i + 2 := by
        rw [Finset.sum_range_succ, hs1, hl1]
      exact (sum_strict_mono_of_pos kolSeq_pos).injective (by omega)
    have hk3 : k3 = k1 + 2 := by
      have : ∑ j ∈ Finset.range (k2 + 1), kolSeq j = i + 4 := by
        rw [Finset.sum_range_succ, hs2, hl2]
      have : k3 = k2 + 1 := (sum_strict_mono_of_pos kolSeq_pos).injective (by omega)
      omega
    rw [hk2] at hl2
    rw [hk3] at hl3
    exact kolSeq_no_triple k1 ⟨by omega, by omega⟩
  exact ⟨hgen 1 2 (by decide), hgen 2 1 (by decide)⟩

/-! ### Exact Block-Derivative & Carpi (1994) Period-Defect Descent -/

private lemma kolSeq_three_sum_ge4 (k : ℕ) :
    4 ≤ kolSeq k + kolSeq (k + 1) + kolSeq (k + 2) := by
  have h0 := kolSeq_mem k
  have h1 := kolSeq_mem (k + 1)
  have h2 := kolSeq_mem (k + 2)
  have hnt := kolSeq_no_triple k
  omega

private lemma kolSeq_three_sum_le5 (k : ℕ) :
    kolSeq k + kolSeq (k + 1) + kolSeq (k + 2) ≤ 5 := by
  have h0 := kolSeq_mem k
  have h1 := kolSeq_mem (k + 1)
  have h2 := kolSeq_mem (k + 2)
  have hnt := kolSeq_no_triple k
  omega

private lemma kolSeq_sum_ge_of_ge6 (k m : ℕ) (hm : 6 ≤ m) :
    8 ≤ ∑ j ∈ Finset.range m, kolSeq (k + j) := by
  have hsub : Finset.range 6 ⊆ Finset.range m := Finset.range_mono hm
  have hle : ∑ j ∈ Finset.range 6, kolSeq (k + j) ≤ ∑ j ∈ Finset.range m, kolSeq (k + j) :=
    Finset.sum_le_sum_of_subset hsub
  have h6 : ∑ j ∈ Finset.range 6, kolSeq (k + j) =
      (kolSeq k + kolSeq (k + 1) + kolSeq (k + 2)) +
      (kolSeq (k + 3) + kolSeq (k + 4) + kolSeq (k + 5)) := by
    simp [Finset.sum_range_succ]; ring
  have ha := kolSeq_three_sum_ge4 k
  have hb := kolSeq_three_sum_ge4 (k + 3)
  have e4 : k + 3 + 1 = k + 4 := by omega
  have e5 : k + 3 + 2 = k + 5 := by omega
  rw [e4, e5] at hb
  omega

private lemma kolSeq_sum_le14_of_le8 (k q : ℕ) (hq : q ≤ 8) :
    ∑ j ∈ Finset.range q, kolSeq (k + j) ≤ 14 := by
  have hle : ∑ j ∈ Finset.range q, kolSeq (k + j) ≤ ∑ j ∈ Finset.range 8, kolSeq (k + j) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hq)
  have h8 : ∑ j ∈ Finset.range 8, kolSeq (k + j) =
      (kolSeq k + kolSeq (k + 1) + kolSeq (k + 2)) +
      (kolSeq (k + 3) + kolSeq (k + 4) + kolSeq (k + 5)) +
      kolSeq (k + 6) + kolSeq (k + 7) := by
    simp [Finset.sum_range_succ]; ring
  have ha := kolSeq_three_sum_le5 k
  have hb := kolSeq_three_sum_le5 (k + 3)
  have e4 : k + 3 + 1 = k + 4 := by omega
  have e5 : k + 3 + 2 = k + 5 := by omega
  rw [e4, e5] at hb
  have h6 : kolSeq (k + 6) ≤ 2 := by rcases kolSeq_mem (k + 6) with h | h <;> omega
  have h7 : kolSeq (k + 7) ≤ 2 := by rcases kolSeq_mem (k + 7) with h | h <;> omega
  omega

private lemma kolSeq_sum_gt_len_of_ge3 (k q : ℕ) (hq : 3 ≤ q) :
    q < ∑ j ∈ Finset.range q, kolSeq (k + j) := by
  have hsplit : ∑ j ∈ Finset.range q, kolSeq (k + j) =
      ∑ j ∈ Finset.range 3, kolSeq (k + j) + ∑ j ∈ Finset.Ico 3 q, kolSeq (k + j) := by
    rw [← Finset.sum_union]
    · congr 1
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2
      omega
  have h3 : ∑ j ∈ Finset.range 3, kolSeq (k + j) =
      kolSeq k + kolSeq (k + 1) + kolSeq (k + 2) := by
    simp [Finset.sum_range_succ]
  have hge4 := kolSeq_three_sum_ge4 k
  have htail : q - 3 ≤ ∑ j ∈ Finset.Ico 3 q, kolSeq (k + j) := by
    calc q - 3 = (Finset.Ico 3 q).card := by simp
      _ = ∑ _j ∈ Finset.Ico 3 q, 1 := by simp
      _ ≤ ∑ j ∈ Finset.Ico 3 q, kolSeq (k + j) := Finset.sum_le_sum (fun j _ => kolSeq_pos _)
  omega

private def kolS (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, kolSeq i

private lemma kolS_add (k q : ℕ) :
    kolS (k + q) = kolS k + ∑ j ∈ Finset.range q, kolSeq (k + j) := by
  induction q with
  | zero => simp [kolS]
  | succ q ih =>
    simp only [kolS, ← add_assoc] at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, add_assoc]

private lemma kolSeq_run_boundary_iff {n : ℕ} (hn : 0 < n) :
    kolSeq (n - 1) ≠ kolSeq n ↔ ∃ k, kolS k = n := by
  constructor
  · intro hne
    obtain ⟨k, hlo, hhi⟩ := exists_run_index kolSeq_pos n
    refine ⟨k, ?_⟩
    by_contra hlt
    have hlo' : kolS k ≤ n - 1 := by unfold kolS at *; omega
    have hhi' : n - 1 < kolS (k + 1) := by unfold kolS at *; omega
    have h1 := kolSeq_run_value k (n - 1) hlo' hhi'
    have h2 := kolSeq_run_value k n hlo hhi
    exact hne (h1.trans h2.symm)
  · rintro ⟨k, rfl⟩
    have hk0 : 0 < k := by
      by_contra h0
      have hk : k = 0 := by omega
      subst hk; simp [kolS] at hn
    have h1 : kolSeq (kolS k) = if k % 2 = 0 then 1 else 2 := by
      simpa [kolS] using kolSeq_run_spec k 0 (kolSeq_pos k)
    have h2 := kolSeq_run_spec (k - 1) (kolSeq (k - 1) - 1)
      (Nat.sub_lt (kolSeq_pos (k - 1)) Nat.one_pos)
    have hSk_eq : kolS k = (∑ i ∈ Finset.range (k - 1), kolSeq i) + kolSeq (k - 1) := by
      unfold kolS
      have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk0).symm
      conv_lhs => rw [hk', Finset.sum_range_succ]
    have hidx : (∑ i ∈ Finset.range (k - 1), kolSeq i) + (kolSeq (k - 1) - 1) = kolS k - 1 := by
      have := kolSeq_pos (k - 1)
      omega
    rw [hidx] at h2
    rw [h2, h1]
    split_ifs <;> omega

private lemma kolSeq_run_match_step {a p L r r' : ℕ}
    (hper : ∀ i < L, kolSeq (a + i) = kolSeq (a + i + p))
    (hge : a ≤ kolS r) (hlt : kolS (r + 1) < a + L)
    (hS : kolS r' = kolS r + p) :
    kolSeq r' = kolSeq r := by
  have hS1 : kolS (r + 1) = kolS r + kolSeq r := Finset.sum_range_succ _ _
  have hS_lt : kolS r < kolS (r + 1) := by have := kolSeq_pos r; omega
  have hbnd_end : kolSeq (kolS (r + 1) + p - 1) ≠ kolSeq (kolS (r + 1) + p) := by
    have hb := (kolSeq_run_boundary_iff (by omega : 0 < kolS (r + 1))).mpr ⟨r + 1, rfl⟩
    have h1 := hper (kolS (r + 1) - 1 - a) (by omega)
    have h2 := hper (kolS (r + 1) - a) (by omega)
    have e1 : a + (kolS (r + 1) - 1 - a) = kolS (r + 1) - 1 := by omega
    have e2 : kolS (r + 1) - 1 + p = kolS (r + 1) + p - 1 := by omega
    have e3 : a + (kolS (r + 1) - a) = kolS (r + 1) := by omega
    rw [e1, e2] at h1
    rw [e3] at h2
    rwa [← h1, ← h2]
  have hno_inner : ∀ t < kolSeq r, kolSeq (kolS r' + t) = kolSeq (kolS r') := by
    intro t ht
    have hpt := hper (kolS r + t - a) (by omega)
    have hp0 := hper (kolS r - a) (by omega)
    have e1 : a + (kolS r + t - a) = kolS r + t := by omega
    have e2 : kolS r + t + p = kolS r' + t := by omega
    have e3 : a + (kolS r - a) = kolS r := by omega
    have e4 : kolS r + p = kolS r' := by omega
    rw [e1, e2] at hpt
    rw [e3, e4] at hp0
    have hsame : kolSeq (kolS r + t) = kolSeq (kolS r) := by
      have ht1 := kolSeq_run_spec r t ht
      have h0 := kolSeq_run_spec r 0 (kolSeq_pos r)
      simp only [add_zero] at h0
      unfold kolS; rw [ht1, h0]
    exact hpt.symm.trans (hsame.trans hp0)
  rcases kolSeq_mem r with hr1 | hr2
  · rcases kolSeq_mem r' with hr'1 | hr'2
    · omega
    · exfalso
      have hsame : kolSeq (kolS r') = kolSeq (kolS r' + 1) := by
        have h0 := kolSeq_run_spec r' 0 (by omega)
        have h1 := kolSeq_run_spec r' 1 (by omega)
        unfold kolS; simp only [add_zero] at h0; rw [h0, h1]
      have hidx1 : kolS (r + 1) + p - 1 = kolS r' := by omega
      have hidx2 : kolS (r + 1) + p = kolS r' + 1 := by omega
      rw [hidx1, hidx2] at hbnd_end
      exact hbnd_end hsame
  · rcases kolSeq_mem r' with hr'1 | hr'2
    · exfalso
      have hsame := hno_inner 1 (by omega)
      have hdiff : kolSeq (kolS r') ≠ kolSeq (kolS r' + 1) := by
        have h0 := kolSeq_run_spec r' 0 (by omega)
        have h1 := kolSeq_run_spec (r' + 1) 0 (kolSeq_pos _)
        have hnxt : kolS (r' + 1) = kolS r' + 1 := by
          unfold kolS; rw [Finset.sum_range_succ, hr'1]
        unfold kolS at hnxt ⊢; simp only [add_zero] at h0 h1
        rw [← hnxt, h0, h1]; split_ifs <;> omega
      exact hdiff hsame.symm
    · omega

/-- Exact Carpi Period-Defect Descent: any factor of `kolSeq` of period `p ≥ 15` and length
`3 * p - 7` induces a factor of `kolSeq` of strictly smaller EVEN period `q` with
`10 ≤ q < p` and length `3 * q - 7`. -/
private lemma carpi_period_defect_descent {a p : ℕ} (hp : 15 ≤ p)
    (hper : ∀ i < 2 * p - 7, kolSeq (a + i) = kolSeq (a + i + p)) :
    ∃ (k' q : ℕ), 10 ≤ q ∧ q < p ∧ q % 2 = 0 ∧
      ∀ j < 2 * q - 7, kolSeq (k' + j) = kolSeq (k' + j + q) := by
  obtain ⟨k0, hk0_lo, hk0_hi⟩ := exists_run_index kolSeq_pos a
  let k := k0 + 1
  let δ := kolS k - a
  have hk0_le2 : kolSeq k0 ≤ 2 := by rcases kolSeq_mem k0 with h | h <;> omega
  have hSk0_succ : kolS k = kolS k0 + kolSeq k0 := Finset.sum_range_succ _ _
  have hSk0_lo : kolS k0 ≤ a := hk0_lo
  have hSk_hi : a < kolS k := hk0_hi
  have hδ_pos : 1 ≤ δ := by unfold δ; omega
  have hδ_le2 : δ ≤ 2 := by unfold δ; omega
  have hSk : kolS k = a + δ := by unfold δ; omega
  -- `a + δ` is a run boundary, so `a + δ + p` is also a run boundary `kolS (k + q)`
  have hbnd1 : kolSeq (a + δ - 1) ≠ kolSeq (a + δ) := by
    rw [kolSeq_run_boundary_iff (by omega)]
    exact ⟨k, hSk⟩
  have hbnd2 : kolSeq (a + δ + p - 1) ≠ kolSeq (a + δ + p) := by
    have h1 := hper (δ - 1) (by omega)
    have h2 := hper δ (by omega)
    have e1 : a + (δ - 1) = a + δ - 1 := by omega
    have e2 : a + δ - 1 + p = a + δ + p - 1 := by omega
    rw [e1, e2] at h1
    rwa [← h1, ← h2]
  obtain ⟨k2, hk2⟩ := (kolSeq_run_boundary_iff (by omega)).mp hbnd2
  have hk_lt_k2 : k < k2 := by
    by_contra hge
    have hle : kolS k2 ≤ kolS k := (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
    omega
  let q := k2 - k
  have hk2_eq : k2 = k + q := (Nat.add_sub_of_le (Nat.le_of_lt hk_lt_k2)).symm
  rw [hk2_eq] at hk2
  have hq_sum : ∑ j ∈ Finset.range q, kolSeq (k + j) = p := by
    have := kolS_add k q
    omega
  have hq_even : q % 2 = 0 := by
    have h1 := kolSeq_run_spec k 0 (kolSeq_pos k)
    have h2 := kolSeq_run_spec (k + q) 0 (kolSeq_pos (k + q))
    simp only [add_zero] at h1 h2
    have heq : kolSeq (kolS k) = kolSeq (kolS (k + q)) := by
      rw [hSk, hk2]
      exact hper δ (by omega)
    unfold kolS at heq
    rw [h1, h2] at heq
    split_ifs at heq <;> omega
  have hq_ge10 : 10 ≤ q := by
    by_contra hlt
    have hle8 : q ≤ 8 := by omega
    have hsum14 := kolSeq_sum_le14_of_le8 k q hle8
    omega
  have hq_lt_p : q < p := by
    have := kolSeq_sum_gt_len_of_ge3 k q (by omega)
    omega
  -- `δ ≤ kolSeq (k + q - 1)` because `[a + p, a + p + δ)` is constant!
  have hδ_le_last : δ ≤ kolSeq (k + q - 1) := by
    rcases Nat.eq_or_lt_of_le hδ_pos with h1 | hgt1
    · have := kolSeq_pos (k + q - 1); omega
    · have hδ2 : δ = 2 := by omega
      have h01 : kolSeq a = kolSeq (a + 1) := by
        have hlo1 : kolS k0 ≤ a + 1 := by omega
        have hhi1 : a + 1 < kolS k := by omega
        exact (kolSeq_run_value k0 a hk0_lo hk0_hi).trans
          (kolSeq_run_value k0 (a + 1) hlo1 hhi1).symm
      have hp01 : kolSeq (a + p) = kolSeq (a + p + 1) := by
        have ha0 := hper 0 (by omega)
        have ha1 := hper 1 (by omega)
        have : a + 1 + p = a + p + 1 := by omega
        rw [this] at ha1
        simpa [add_zero] using ha0.symm.trans (h01.trans ha1)
      obtain ⟨r, hr_s, hr_l⟩ := kolSeq_double_run hp01
      have hnext : kolS (r + 1) = a + p + 2 := by
        unfold kolS; rw [Finset.sum_range_succ, hr_s, hr_l]
      have hr_eq : r + 1 = k + q :=
        (sum_strict_mono_of_pos kolSeq_pos).injective (by unfold kolS at hk2 hnext; omega)
      have hr_eq' : r = k + q - 1 := by omega
      rw [← hr_eq', hr_l]
      omega
  have hmatch : ∀ j, kolS (k + j + 1) < a + 2 * p - 7 →
      kolS (k + q + j) = kolS (k + j) + p ∧ kolSeq (k + q + j) = kolSeq (k + j) := by
    intro j
    induction j with
    | zero =>
      intro hlt
      have hbase : kolS (k + q + 0) = kolS (k + 0) + p := by simp [hSk, hk2]
      refine ⟨hbase, ?_⟩
      exact kolSeq_run_match_step hper (by simp [hSk]) (by simp only [add_zero] at hlt ⊢; omega) hbase
    | succ j ih =>
      intro hlt
      have hlt_prev : kolS (k + j + 1) < a + 2 * p - 7 := by
        have : kolS (k + j + 1) < kolS (k + (j + 1) + 1) :=
          sum_strict_mono_of_pos kolSeq_pos (by omega)
        omega
      obtain ⟨hprev_S, hprev_K⟩ := ih hlt_prev
      have hcur_S : kolS (k + q + (j + 1)) = kolS (k + (j + 1)) + p := by
        have h1 : kolS (k + q + (j + 1)) = kolS (k + q + j) + kolSeq (k + q + j) :=
          Finset.sum_range_succ _ _
        have h2 : kolS (k + (j + 1)) = kolS (k + j) + kolSeq (k + j) :=
          Finset.sum_range_succ _ _
        omega
      have hge_cur : a ≤ kolS (k + (j + 1)) := by
        have : kolS k ≤ kolS (k + (j + 1)) := (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
        omega
      exact ⟨hcur_S, kolSeq_run_match_step hper hge_cur (by omega) hcur_S⟩
  have hfirst_q : ∀ j < q, kolSeq (k + q + j) = kolSeq (k + j) := by
    intro j hj
    have hle : kolS (k + j + 1) ≤ kolS (k + q) :=
      (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
    exact (hmatch j (by omega)).2
  have hS2q : kolS (k + 2 * q) = a + δ + 2 * p := by
    have h1 : kolS (k + 2 * q) = kolS (k + q) + ∑ j ∈ Finset.range q, kolSeq (k + q + j) := by
      have : k + 2 * q = (k + q) + q := by omega
      rw [this, kolS_add]
    have hsum2 : ∑ j ∈ Finset.range q, kolSeq (k + q + j) = p := by
      rw [Finset.sum_congr rfl (fun j hj => hfirst_q j (Finset.mem_range.mp hj)), hq_sum]
    omega
  have hK_last : kolSeq (k + 2 * q - 1) = kolSeq (k + q - 1) := by
    have := hfirst_q (q - 1) (by omega)
    have h1 : k + q + (q - 1) = k + 2 * q - 1 := by omega
    have h2 : k + (q - 1) = k + q - 1 := by omega
    rwa [h1, h2] at this
  have hS_bound : kolS (k + (2 * q - 7)) < a + 2 * p - 7 := by
    have hsplit : kolS (k + 2 * q - 1) =
        kolS (k + (2 * q - 7)) + ∑ j ∈ Finset.range 6, kolSeq (k + (2 * q - 7) + j) := by
      have : k + 2 * q - 1 = (k + (2 * q - 7)) + 6 := by omega
      rw [this, kolS_add]
    have hlast : kolS (k + 2 * q) = kolS (k + 2 * q - 1) + kolSeq (k + 2 * q - 1) := by
      have : k + 2 * q = (k + 2 * q - 1) + 1 := by omega
      conv_lhs => rw [this]
      exact Finset.sum_range_succ _ _
    have hge8 := kolSeq_sum_ge_of_ge6 (k + (2 * q - 7)) 6 (le_refl 6)
    omega
  refine ⟨k, q, hq_ge10, hq_lt_p, hq_even, fun j hj => ?_⟩
  have hle : kolS (k + j + 1) ≤ kolS (k + (2 * q - 7)) :=
    (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
  have heq := (hmatch j (lt_of_le_of_lt hle hS_bound)).2
  have : k + j + q = k + q + j := by omega
  rw [this, heq]

/-! ### Computable Run-Length Derivative `deriv` on Factors of `kolSeq` -/

private def rleAux (cur cnt : ℕ) : List ℕ → List ℕ
  | [] => [cnt]
  | x :: xs => if x = cur then rleAux cur (cnt + 1) xs else cnt :: rleAux x 1 xs

private def rle : List ℕ → List ℕ
  | [] => []
  | x :: xs => rleAux x 1 xs

private def dropFirstOne : List ℕ → List ℕ
  | 1 :: xs => xs
  | xs => xs

private def dropLastOne (l : List ℕ) : List ℕ :=
  (dropFirstOne l.reverse).reverse

private def deriv (w : List ℕ) : List ℕ :=
  dropLastOne (dropFirstOne (rle w))

private def noTripleBool : List ℕ → Bool
  | a :: b :: c :: rest =>
    if a == b && b == c then false else noTripleBool (b :: c :: rest)
  | _ => true

private def isValidWord (w : List ℕ) : Bool :=
  w.all (fun x => x == 1 || x == 2) && noTripleBool w

private lemma noTripleBool_eq_true_of_no_triple :
    ∀ (w : List ℕ), (∀ i (h : i + 2 < w.length), ¬ (w[i] = w[i + 1] ∧ w[i + 1] = w[i + 2])) →
      noTripleBool w = true
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | a :: b :: c :: rest, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0
    have hne : (a == b && b == c) = false := by
      cases hab : (a == b) <;> cases hbc : (b == c) <;> simp_all
    simp only [noTripleBool, hne, Bool.false_eq_true, ↓reduceIte]
    apply noTripleBool_eq_true_of_no_triple (b :: c :: rest)
    intro i hi
    have hi' := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc] using hi'

private lemma kolSeq_slice_isValid (a n : ℕ) :
    isValidWord (List.ofFn (fun i : Fin n => kolSeq (a + i))) = true := by
  unfold isValidWord
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    rcases kolSeq_mem (a + i) with h | h <;> simp [h]
  · apply noTripleBool_eq_true_of_no_triple
    intro i hi
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn]
    have h1 : a + (i + 1) = (a + i) + 1 := by omega
    have h2 : a + (i + 2) = (a + i) + 2 := by omega
    rw [h1, h2]
    exact kolSeq_no_triple (a + i)

private lemma rleAux_append_same (cur cnt : ℕ) :
    ∀ (m : ℕ) (xs : List ℕ),
      rleAux cur cnt (List.replicate m cur ++ xs) = rleAux cur (cnt + m) xs
  | 0, xs => by simp
  | m + 1, xs => by
    simp only [List.replicate_succ, List.cons_append, rleAux, ↓reduceIte]
    rw [rleAux_append_same cur (cnt + 1) m xs]
    congr 1; omega

private lemma rle_expandFrom_aux (b : ℕ) (hb : b = 1 ∨ b = 2) :
    ∀ (u : List ℕ), (∀ x ∈ u, 1 ≤ x) →
      ∀ (cnt : ℕ), rleAux b cnt (expandFrom (3 - b) u) =
        if u = [] then [cnt] else cnt :: u
  | [], _, cnt => by simp [expandFrom, rleAux]
  | x :: xs, hpos, cnt => by
    have hx : 1 ≤ x := hpos x (List.mem_cons_self ..)
    have hne : 3 - b ≠ b := swap_ne hb
    have hrep : List.replicate x (3 - b) = (3 - b) :: List.replicate (x - 1) (3 - b) := by
      cases x with
      | zero => omega
      | succ x' => rfl
    simp only [expandFrom, List.cons_ne_nil, ↓reduceIte]
    rw [hrep, List.cons_append, rleAux, if_neg hne, rleAux_append_same]
    have hcnt : 1 + (x - 1) = x := by omega
    rw [hcnt, swap_involution hb]
    have ih := rle_expandFrom_aux (3 - b) (swap_mem hb) xs
      (fun y hy => hpos y (List.mem_cons_of_mem x hy)) x
    rw [swap_involution hb] at ih
    rw [ih]
    cases xs <;> simp

private lemma rle_expandFrom (b : ℕ) (hb : b = 1 ∨ b = 2) (u : List ℕ) (hpos : ∀ x ∈ u, 1 ≤ x) :
    rle (expandFrom b u) = u := by
  cases u with
  | nil => rfl
  | cons x xs =>
    have hx : 1 ≤ x := hpos x (List.mem_cons_self ..)
    have hrep : List.replicate x b = b :: List.replicate (x - 1) b := by
      cases x with
      | zero => omega
      | succ x' => rfl
    simp only [expandFrom]
    rw [hrep, List.cons_append, rle, rleAux_append_same]
    have hcnt : 1 + (x - 1) = x := by omega
    rw [hcnt, rle_expandFrom_aux b hb xs (fun y hy => hpos y (List.mem_cons_of_mem x hy)) x]
    cases xs <;> simp

private lemma kolSeq_slice_eq_expandFrom (c d : ℕ) (hcd : c ≤ d) :
    List.ofFn (fun i : Fin (kolS d - kolS c) => kolSeq (kolS c + i)) =
      expandFrom (if c % 2 = 0 then 1 else 2)
        (List.ofFn (fun j : Fin (d - c) => kolSeq (c + j))) := by
  have hb : (if c % 2 = 0 then 1 else 2) = 1 ∨ (if c % 2 = 0 then 1 else 2) = 2 := by
    split_ifs <;> simp
  have hlen : (List.ofFn (fun j : Fin (d - c) => kolSeq (c + j))).sum = kolS d - kolS c := by
    rw [list_ofFn_sum (fun j => kolSeq (c + j)) (d - c)]
    have h := kolS_add c (d - c)
    rw [Nat.add_sub_of_le hcd] at h
    omega
  apply List.ext_getElem
  · rw [List.length_ofFn, expandFrom_length, hlen]
  · intro idx h1 h2
    rw [List.length_ofFn] at h1
    rw [List.getElem_ofFn]
    obtain ⟨k, hlo, hhi⟩ := exists_run_index kolSeq_pos (kolS c + idx)
    have hkc : c ≤ k := by
      by_contra hlt
      have hle : kolS (k + 1) ≤ kolS c := (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
      change kolS k ≤ kolS c + idx at hlo
      change kolS c + idx < kolS (k + 1) at hhi
      omega
    have hkd : k < d := by
      by_contra hge
      have hle : kolS d ≤ kolS k := (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
      change kolS k ≤ kolS c + idx at hlo
      have hSc_le : kolS c ≤ kolS d := (sum_strict_mono_of_pos kolSeq_pos).monotone hcd
      omega
    let u := List.ofFn (fun j : Fin (d - c) => kolSeq (c + j))
    have hku : k - c < u.length := by simp [u]; omega
    have hj : kolS c + idx - kolS k < u[k - c]'hku := by
      simp only [u, List.getElem_ofFn, Nat.add_sub_of_le hkc]
      unfold kolS at *; rw [Finset.sum_range_succ] at hhi; omega
    have htake : (u.take (k - c)).sum = kolS k - kolS c := by
      have ht : u.take (k - c) = List.ofFn (fun j : Fin (k - c) => kolSeq (c + j)) := by
        apply List.ext_getElem
        · simp [u]; omega
        · intro i hi1 hi2; simp [u]
      rw [ht, list_ofFn_sum (fun j => kolSeq (c + j)) (k - c)]
      have h := kolS_add c (k - c)
      rw [Nat.add_sub_of_le hkc] at h
      omega
    obtain ⟨hlt, hget⟩ := expandFrom_getElem_run (if c % 2 = 0 then 1 else 2) hb u
      (k - c) hku (kolS c + idx - kolS k) hj
    have hS_le : kolS c ≤ kolS k := (sum_strict_mono_of_pos kolSeq_pos).monotone hkc
    have hidx_eq : (u.take (k - c)).sum + (kolS c + idx - kolS k) = idx := by
      rw [htake]; unfold kolS at hlo hS_le ⊢; omega
    have hval := kolSeq_run_value k (kolS c + idx) hlo hhi
    rw [hval]
    have hRHS : (expandFrom (if c % 2 = 0 then 1 else 2) u)[idx]'h2 =
        (expandFrom (if c % 2 = 0 then 1 else 2) u)[(u.take (k - c)).sum + (kolS c + idx - kolS k)]'hlt := by
      congr 1; exact hidx_eq.symm
    rw [hRHS, hget]
    split_ifs <;> omega

private lemma kolSeq_slice_deriv_is_slice (a n : ℕ) :
    ∃ (c m : ℕ), deriv (List.ofFn (fun i : Fin n => kolSeq (a + i))) =
      List.ofFn (fun j : Fin m => kolSeq (c + j)) := by
  cases n with
  | zero => exact ⟨0, 0, rfl⟩
  | succ n' =>
    obtain ⟨kL, hkL_lo, hkL_hi⟩ := exists_run_index kolSeq_pos a
    obtain ⟨kR, hkR_lo, hkR_hi⟩ := exists_run_index kolSeq_pos (a + n')
    have hkLR : kL ≤ kR := by
      by_contra hlt
      have hle : kolS (kR + 1) ≤ kolS kL := (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
      unfold kolS at hle; omega
    -- Length of the first run inside `[a, a + n']` and last run inside `[a, a + n']`
    rcases eq_or_lt_of_le hkLR with rfl | hlt_LR
    · -- Single run of length `n' + 1 ∈ {1, 2}`
      have hlen_le2 : n' + 1 ≤ 2 := by
        have h2 : kolSeq kL ≤ 2 := by rcases kolSeq_mem kL with h | h <;> omega
        rw [Finset.sum_range_succ] at hkR_hi; omega
      have hconst : List.ofFn (fun i : Fin (n' + 1) => kolSeq (a + i)) =
          List.replicate (n' + 1) (if kL % 2 = 0 then 1 else 2) := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          simp only [List.length_ofFn] at hi1
          rw [List.getElem_ofFn, List.getElem_replicate]
          exact kolSeq_run_value kL (a + i) (by omega) (by omega)
      rw [hconst]
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_succ (Nat.zero_le n')) with h1 | h2
      · have hn0 : n' = 0 := by omega
        subst hn0
        exact ⟨0, 0, by simp [deriv, rle, rleAux, dropFirstOne, dropLastOne]⟩
      · have hn1 : n' = 1 := by omega
        subst hn1
        have hKkL : kolSeq kL = 2 := by
          have hle2 : kolSeq kL ≤ 2 := by rcases kolSeq_mem kL with h | h <;> omega
          rw [Finset.sum_range_succ] at hkR_hi; omega
        refine ⟨kL, 1, ?_⟩
        simp only [deriv, rle, List.replicate_succ, List.replicate_zero, rleAux, ↓reduceIte,
          dropFirstOne, dropLastOne, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.ofFn_succ, List.ofFn_zero, Fin.val_zero, add_zero, hKkL]
    · -- Multiple runs `kL < kR`: `w = expandFrom bL (rL :: middle ++ [rR])`
      let rL := kolS (kL + 1) - a
      let rR := a + n' + 1 - kolS kR
      have hrL_pos : 1 ≤ rL := by unfold rL kolS; omega
      have hrL_le : rL ≤ kolSeq kL := by
        unfold rL kolS; rw [Finset.sum_range_succ]; omega
      have hrR_pos : 1 ≤ rR := by unfold rR kolS; omega
      have hrR_le : rR ≤ kolSeq kR := by
        unfold rR kolS; rw [Finset.sum_range_succ] at hkR_hi; omega
      let mid := List.ofFn (fun j : Fin (kR - (kL + 1)) => kolSeq ((kL + 1) + j))
      let runLens := (rL :: mid) ++ [rR]
      have hrun_pos : ∀ x ∈ runLens, 1 ≤ x := by
        intro x hx
        simp only [runLens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with (rfl | hx) | rfl
        · exact hrL_pos
        · rw [List.mem_ofFn] at hx; rcases hx with ⟨j, rfl⟩; exact kolSeq_pos _
        · exact hrR_pos
      have hbL : (if kL % 2 = 0 then 1 else 2) = 1 ∨ (if kL % 2 = 0 then 1 else 2) = 2 := by
        split_ifs <;> simp
      have hw_eq : List.ofFn (fun i : Fin (n' + 1) => kolSeq (a + i)) =
          expandFrom (if kL % 2 = 0 then 1 else 2) runLens := by
        have hfull := kolSeq_slice_eq_expandFrom kL (kR + 1) (by omega)
        have hmid_len : mid.length = kR - (kL + 1) := List.length_ofFn
        have hmid_sum : mid.sum = kolS kR - kolS (kL + 1) := by
          unfold mid
          rw [list_ofFn_sum (fun j => kolSeq ((kL + 1) + j)) (kR - (kL + 1))]
          have h := kolS_add (kL + 1) (kR - (kL + 1))
          rw [Nat.add_sub_of_le (by omega)] at h; omega
        have hS_le : kolS (kL + 1) ≤ kolS kR :=
          (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
        have hrun_sum : runLens.sum = n' + 1 := by
          simp only [runLens, List.sum_append, List.sum_cons, List.sum_nil, add_zero, hmid_sum]
          unfold rL rR kolS at *; omega
        have hrun_full : List.ofFn (fun j : Fin (kR + 1 - kL) => kolSeq (kL + j)) =
            (kolSeq kL :: mid) ++ [kolSeq kR] := by
          apply List.ext_getElem
          · simp [mid]; omega
          · intro j hj1 hj2
            simp only [List.length_ofFn] at hj1
            rw [List.getElem_ofFn]
            cases j with
            | zero => simp
            | succ j' =>
              change kolSeq (kL + (j' + 1)) = (kolSeq kL :: (mid ++ [kolSeq kR]))[j' + 1]'hj2
              rw [List.getElem_cons_succ]
              rcases lt_or_ge j' mid.length with hjm | hjm
              · rw [List.getElem_append_left hjm]
                simp only [mid, List.getElem_ofFn]
                congr 1; omega
              · rw [List.getElem_append_right hjm]
                have hjeq : j' - mid.length = 0 := by simp [mid] at hjm ⊢; omega
                simp only [hjeq, List.getElem_singleton]
                congr 1; simp [mid] at hjm; omega
        have hpre_rep : List.replicate (kolSeq kL) (if kL % 2 = 0 then 1 else 2) =
            List.replicate (a - kolS kL) (if kL % 2 = 0 then 1 else 2) ++
            List.replicate rL (if kL % 2 = 0 then 1 else 2) := by
          rw [← List.replicate_add]
          congr 1
          have hSkL : kolS (kL + 1) = kolS kL + kolSeq kL := Finset.sum_range_succ _ _
          have hloL : kolS kL ≤ a := hkL_lo
          have hhiL : a < kolS (kL + 1) := hkL_hi
          unfold rL; omega
        have hpar : (if (mid.length + 1) % 2 = 0 then (if kL % 2 = 0 then 1 else 2)
            else 3 - (if kL % 2 = 0 then 1 else 2)) = if kR % 2 = 0 then 1 else 2 := by
          rw [hmid_len]; split_ifs <;> omega
        have hsuf_rep : List.replicate (kolSeq kR) (if kR % 2 = 0 then 1 else 2) =
            List.replicate rR (if kR % 2 = 0 then 1 else 2) ++
            List.replicate (kolS (kR + 1) - (a + n' + 1)) (if kR % 2 = 0 then 1 else 2) := by
          rw [← List.replicate_add]
          congr 1
          have hSkR : kolS (kR + 1) = kolS kR + kolSeq kR := Finset.sum_range_succ _ _
          have hloR : kolS kR ≤ a + n' := hkR_lo
          have hhiR : a + n' < kolS (kR + 1) := hkR_hi
          unfold rR; omega
        have hexp_full : expandFrom (if kL % 2 = 0 then 1 else 2) ((kolSeq kL :: mid) ++ [kolSeq kR]) =
            List.replicate (a - kolS kL) (if kL % 2 = 0 then 1 else 2) ++
            expandFrom (if kL % 2 = 0 then 1 else 2) runLens ++
            List.replicate (kolS (kR + 1) - (a + n' + 1)) (if kR % 2 = 0 then 1 else 2) := by
          dsimp only [runLens]
          rw [expandFrom_append _ hbL, expandFrom_append _ hbL]
          simp only [List.length_cons, hpar, expandFrom, List.append_nil, hpre_rep, hsuf_rep]
          simp only [List.append_assoc]
        rw [hrun_full, hexp_full] at hfull
        apply List.ext_getElem
        · rw [List.length_ofFn, expandFrom_length, hrun_sum]
        · intro i hi1 hi2
          rw [List.length_ofFn] at hi1
          rw [List.getElem_ofFn]
          have hidx_full : (a - kolS kL) + i < kolS (kR + 1) - kolS kL := by
            unfold kolS at *; omega
          have hget_f := congrArg (fun l => l[(a - kolS kL) + i]?) hfull
          rw [List.getElem?_eq_getElem (by simpa using hidx_full)] at hget_f
          rw [List.getElem_ofFn] at hget_f
          have hadd_eq : kolS kL + ((a - kolS kL) + i) = a + i := by unfold kolS at *; omega
          rw [hadd_eq] at hget_f
          have hlt_rhs : (a - kolS kL) + i <
              (List.replicate (a - kolS kL) (if kL % 2 = 0 then 1 else 2) ++
                expandFrom (if kL % 2 = 0 then 1 else 2) runLens ++
                List.replicate (kolS (kR + 1) - (a + n' + 1)) (if kR % 2 = 0 then 1 else 2)).length := by
            simp [expandFrom_length, hrun_sum]; omega
          rw [List.getElem?_eq_getElem hlt_rhs] at hget_f
          have hget_rhs : (List.replicate (a - kolS kL) (if kL % 2 = 0 then 1 else 2) ++
                expandFrom (if kL % 2 = 0 then 1 else 2) runLens ++
                List.replicate (kolS (kR + 1) - (a + n' + 1)) (if kR % 2 = 0 then 1 else 2))[(a - kolS kL) + i]'hlt_rhs =
              (expandFrom (if kL % 2 = 0 then 1 else 2) runLens)[i]'hi2 := by
            rw [List.getElem_append_left (by simp [expandFrom_length, hrun_sum]; omega)]
            rw [List.getElem_append_right (by simp)]
            simp
          rw [hget_rhs] at hget_f
          exact Option.some.inj hget_f
      rw [hw_eq]
      unfold deriv
      rw [rle_expandFrom _ hbL runLens hrun_pos]
      have hKL2 : kolSeq kL ≤ 2 := by rcases kolSeq_mem kL with h | h <;> omega
      have hKR2 : kolSeq kR ≤ 2 := by rcases kolSeq_mem kR with h | h <;> omega
      have hrL_cases : rL = 1 ∨ (rL = 2 ∧ kolSeq kL = 2) := by omega
      have hrR_cases : rR = 1 ∨ (rR = 2 ∧ kolSeq kR = 2) := by omega
      have hdropL : dropFirstOne runLens =
          if rL = 1 then mid ++ [rR] else kolSeq kL :: mid ++ [rR] := by
        rcases hrL_cases with h1 | ⟨h2, hk2⟩
        · simp [runLens, dropFirstOne, h1]
        · simp [runLens, dropFirstOne, h2, hk2]
      rw [hdropL]
      have hdropR_aux : ∀ (pre : List ℕ),
          dropLastOne (pre ++ [rR]) = if rR = 1 then pre else pre ++ [kolSeq kR] := by
        intro pre
        unfold dropLastOne
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
        rcases hrR_cases with h1 | ⟨h2, hk2⟩
        · simp [dropFirstOne, h1]
        · simp [dropFirstOne, h2, hk2]
      split_ifs with h1
      · rw [hdropR_aux]
        split_ifs with h2
        · exact ⟨kL + 1, kR - (kL + 1), rfl⟩
        · refine ⟨kL + 1, kR + 1 - (kL + 1), ?_⟩
          have heq : kR + 1 - (kL + 1) = (kR - (kL + 1)) + 1 := by omega
          rw [heq, List.ofFn_succ', List.concat_eq_append]
          simp only [mid, Fin.val_castSucc, Fin.val_last]
          congr 1
          congr 1
          congr 1; omega
      · have hcons_app : kolSeq kL :: mid ++ [rR] = (kolSeq kL :: mid) ++ [rR] := rfl
        rw [hcons_app, hdropR_aux]
        split_ifs with h2
        · refine ⟨kL, kR - kL, ?_⟩
          have heq : kR - kL = (kR - (kL + 1)) + 1 := by omega
          rw [heq, List.ofFn_succ]
          simp only [Fin.val_zero, add_zero, Fin.val_succ, mid]
          congr 1
          apply List.ext_getElem
          · simp
          · intro i hi1 hi2
            simp only [List.getElem_ofFn]
            congr 1; omega
        · refine ⟨kL, kR + 1 - kL, ?_⟩
          apply List.ext_getElem
          · simp [mid]; omega
          · intro j hj1 hj2
            simp only [List.length_ofFn] at hj2
            rw [List.getElem_ofFn]
            cases j with
            | zero => simp
            | succ j' =>
              change (kolSeq kL :: (mid ++ [kolSeq kR]))[j' + 1]'hj1 = kolSeq (kL + (j' + 1))
              rw [List.getElem_cons_succ]
              rcases lt_or_ge j' mid.length with hjm | hjm
              · rw [List.getElem_append_left hjm]
                simp only [mid, List.getElem_ofFn]; congr 1; omega
              · rw [List.getElem_append_right hjm]
                have hjeq : j' - mid.length = 0 := by simp [mid] at hjm ⊢; omega
                simp only [hjeq, List.getElem_singleton]; congr 1; simp [mid] at hjm; omega

private lemma kolSeq_slice_iter_deriv_isValid (k a n : ℕ) :
    isValidWord (deriv^[k] (List.ofFn (fun i : Fin n => kolSeq (a + i)))) = true := by
  induction k generalizing a n with
  | zero => exact kolSeq_slice_isValid a n
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨c, m, hcm⟩ := kolSeq_slice_deriv_is_slice a n
    rw [hcm]
    exact ih c m

/-! ### Pruned Backtracking Completeness Engine for Carpi Base Cases (0 `native_decide`) -/

private def headForbidden : List ℕ → Bool
  | 1 :: 1 :: 1 :: _ => true
  | 2 :: 2 :: 2 :: _ => true
  | 1 :: 2 :: 1 :: 2 :: 1 :: _ => true
  | 2 :: 1 :: 2 :: 1 :: 2 :: _ => true
  | 1 :: 1 :: 2 :: 2 :: 1 :: 1 :: _ => true
  | 2 :: 2 :: 1 :: 1 :: 2 :: 2 :: _ => true
  | _ => false

private def checkLocalValidRec : ℕ → List ℕ → (List ℕ → Bool) → Bool
  | 0, acc, pred => pred acc.reverse
  | rem + 1, acc, pred =>
    (if headForbidden (1 :: acc) then true else checkLocalValidRec rem (1 :: acc) pred) &&
    (if headForbidden (2 :: acc) then true else checkLocalValidRec rem (2 :: acc) pred)

private def isLocalValidSlice (w : List ℕ) : Prop :=
  (∀ x ∈ w, x = 1 ∨ x = 2) ∧
  ∀ k ≤ w.length, headForbidden (w.take k).reverse = false

private lemma kolSeq_slice_headForbidden_false (a n : ℕ) :
    headForbidden (List.ofFn (fun i : Fin n => kolSeq (a + i))).reverse = false := by
  cases h : headForbidden (List.ofFn (fun i : Fin n => kolSeq (a + i))).reverse with
  | false => rfl
  | true =>
    exfalso
    let w := List.ofFn (fun i : Fin n => kolSeq (a + i))
    change headForbidden w.reverse = true at h
    have hpat : ∃ pat : List ℕ, pat <+: w.reverse ∧
        (pat = [1, 1, 1] ∨ pat = [2, 2, 2] ∨ pat = [1, 2, 1, 2, 1] ∨
         pat = [2, 1, 2, 1, 2] ∨ pat = [1, 1, 2, 2, 1, 1] ∨ pat = [2, 2, 1, 1, 2, 2]) := by
      generalize w.reverse = l at h
      unfold headForbidden at h
      split at h
      · exact ⟨[1, 1, 1], ⟨_, rfl⟩, Or.inl rfl⟩
      · exact ⟨[2, 2, 2], ⟨_, rfl⟩, Or.inr (Or.inl rfl)⟩
      · exact ⟨[1, 2, 1, 2, 1], ⟨_, rfl⟩, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨[2, 1, 2, 1, 2], ⟨_, rfl⟩, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨[1, 1, 2, 2, 1, 1], ⟨_, rfl⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
      · exact ⟨[2, 2, 1, 1, 2, 2], ⟨_, rfl⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
      · exact (Bool.false_ne_true h).elim
    rcases hpat with ⟨pat, ⟨rest, hrest⟩, hcases⟩
    have hpal : pat.reverse = pat := by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hw_eq : w = rest.reverse ++ pat := by
      have := congrArg List.reverse hrest
      simp only [List.reverse_reverse, List.reverse_append, hpal] at this
      exact this.symm
    have hlen : n = rest.length + pat.length := by
      have := congrArg List.length hw_eq
      simpa [w] using this
    have hslice : List.ofFn (fun j : Fin pat.length => kolSeq ((a + rest.length) + j)) = pat := by
      apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        simp only [List.length_ofFn] at hj1
        rw [List.getElem_ofFn]
        have hidx : rest.length + j < n := by omega
        have hget := congrArg (fun l => l[rest.length + j]?) hw_eq
        rw [List.getElem?_eq_getElem (by simp [w]; exact hidx)] at hget
        rw [List.getElem?_eq_getElem (by simp; omega)] at hget
        simp only [w, List.getElem_ofFn, List.getElem_append_right (by simp : rest.reverse.length ≤ rest.length + j),
          List.length_reverse, Nat.add_sub_cancel_left] at hget
        have hadd : (a + rest.length) + j = a + (rest.length + j) := by omega
        rw [hadd]
        exact Option.some.inj hget
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · have h0 := congrArg (fun l => l[0]?) hslice
      have h1 := congrArg (fun l => l[1]?) hslice
      have h2 := congrArg (fun l => l[2]?) hslice
      simp at h0 h1 h2
      exact kolSeq_no_triple (a + rest.length) ⟨by omega, by omega⟩
    · have h0 := congrArg (fun l => l[0]?) hslice
      have h1 := congrArg (fun l => l[1]?) hslice
      have h2 := congrArg (fun l => l[2]?) hslice
      simp at h0 h1 h2
      exact kolSeq_no_triple (a + rest.length) ⟨by omega, by omega⟩
    · exact (kolSeq_no_alt5 (a + rest.length)).1 hslice
    · exact (kolSeq_no_alt5 (a + rest.length)).2 hslice
    · exact (kolSeq_no_double_triple (a + rest.length)).1 hslice
    · exact (kolSeq_no_double_triple (a + rest.length)).2 hslice

private lemma kolSeq_slice_isLocalValid (a n : ℕ) :
    isLocalValidSlice (List.ofFn (fun i : Fin n => kolSeq (a + i))) := by
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · rw [List.mem_ofFn] at hx; rcases hx with ⟨i, rfl⟩; exact kolSeq_mem _
  · simp only [List.length_ofFn] at hk
    have htake : (List.ofFn (fun i : Fin n => kolSeq (a + i))).take k =
        List.ofFn (fun i : Fin k => kolSeq (a + i)) := by
      apply List.ext_getElem
      · simp [hk]
      · intro i hi1 hi2; simp
    rw [htake]
    exact kolSeq_slice_headForbidden_false a k

private lemma checkLocalValidRec_sound :
    ∀ (rem : ℕ) (acc : List ℕ) (pred : List ℕ → Bool),
      checkLocalValidRec rem acc pred = true →
      ∀ (tail : List ℕ), tail.length = rem →
        (∀ x ∈ tail, x = 1 ∨ x = 2) →
        (∀ k, 1 ≤ k → k ≤ tail.length → headForbidden ((tail.take k).reverse ++ acc) = false) →
        pred (acc.reverse ++ tail) = true
  | 0, acc, pred, hchk, tail, hlen, _, _ => by
    cases tail with
    | nil => simpa [checkLocalValidRec] using hchk
    | cons _ _ => simp at hlen
  | rem + 1, acc, pred, hchk, tail, hlen, hmem, hforb => by
    cases tail with
    | nil => simp at hlen
    | cons x xs =>
      simp only [checkLocalValidRec, Bool.and_eq_true] at hchk
      have hx : x = 1 ∨ x = 2 := hmem x (List.mem_cons_self ..)
      have hxs_len : xs.length = rem := by simp at hlen; omega
      have hxs_mem : ∀ y ∈ xs, y = 1 ∨ y = 2 := fun y hy => hmem y (List.mem_cons_of_mem x hy)
      have hx_ok : headForbidden (x :: acc) = false := by
        simpa using hforb 1 (le_refl 1) (by simp)
      have hxs_forb : ∀ k, 1 ≤ k → k ≤ xs.length →
          headForbidden ((xs.take k).reverse ++ (x :: acc)) = false := by
        intro k hk1 hk2
        have h := hforb (k + 1) (by omega) (by simp; omega)
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using h
      have heq_app : acc.reverse ++ x :: xs = (x :: acc).reverse ++ xs := by
        simp [List.reverse_cons, List.append_assoc]
      rw [heq_app]
      rcases hx with rfl | rfl
      · have h1 := hchk.1
        rw [hx_ok] at h1
        exact checkLocalValidRec_sound rem (1 :: acc) pred (by simpa using h1) xs hxs_len hxs_mem hxs_forb
      · have h2 := hchk.2
        rw [hx_ok] at h2
        exact checkLocalValidRec_sound rem (2 :: acc) pred (by simpa using h2) xs hxs_len hxs_mem hxs_forb

private def periodicWord (u : List ℕ) (L : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin L => u.getD (i.1 % u.length) 0)

private def failsDerivBy : ℕ → List ℕ → Bool
  | 0, w => !isValidWord w
  | k + 1, w => !isValidWord w || failsDerivBy k (deriv w)

private lemma failsDerivBy_sound :
    ∀ (k : ℕ) (w : List ℕ), failsDerivBy k w = true →
      ∃ j ≤ k, isValidWord (deriv^[j] w) = false
  | 0, w, h => by
    simp only [failsDerivBy, Bool.not_eq_true'] at h
    exact ⟨0, le_refl 0, h⟩
  | k + 1, w, h => by
    simp only [failsDerivBy, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h0 | hk
    · exact ⟨0, Nat.zero_le _, h0⟩
    · obtain ⟨j, hj, hfail⟩ := failsDerivBy_sound k (deriv w) hk
      refine ⟨j + 1, by omega, ?_⟩
      rwa [Function.iterate_succ_apply]

private lemma kolSeq_no_periodic_of_check (p L maxK : ℕ) (hp : 0 < p) (hpL : p ≤ L)
    (hchk : checkLocalValidRec p [] (fun u => failsDerivBy maxK (periodicWord u L)) = true) :
    ¬ ∃ a : ℕ, ∀ i < L - p, kolSeq (a + i) = kolSeq (a + i + p) := by
  rintro ⟨a, hper⟩
  let u := List.ofFn (fun i : Fin p => kolSeq (a + i))
  have hu_len : u.length = p := List.length_ofFn
  have hu_valid := kolSeq_slice_isLocalValid a p
  have hpred : failsDerivBy maxK (periodicWord u L) = true := by
    have h := checkLocalValidRec_sound p [] (fun u => failsDerivBy maxK (periodicWord u L))
      hchk u hu_len hu_valid.1 (fun k _ hk => by simpa using hu_valid.2 k hk)
    simpa using h
  -- Show `periodicWord u L = List.ofFn (fun i : Fin L => kolSeq (a + i))`!
  have hper_mod : ∀ i < L, kolSeq (a + i) = kolSeq (a + i % p) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      rcases lt_or_ge i p with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
      · have hstep := hper (i - p) (by omega)
        have h1 : a + (i - p) + p = a + i := by omega
        rw [h1] at hstep
        have hmod : (i - p) % p = i % p := by
          have : i = (i - p) + p := by omega
          conv_rhs => rw [this, Nat.add_mod_right]
        rw [← hstep, ih (i - p) (by omega) (by omega), hmod]
  have hpw_eq : periodicWord u L = List.ofFn (fun i : Fin L => kolSeq (a + i)) := by
    apply List.ext_getElem
    · simp [periodicWord]
    · intro i hi1 hi2
      simp only [periodicWord, List.length_ofFn] at hi1
      simp only [periodicWord, List.getElem_ofFn, hu_len]
      have hmod_lt : i % p < u.length := by rw [hu_len]; exact Nat.mod_lt i hp
      have hgetD : u.getD (i % p) 0 = kolSeq (a + i % p) := by
        simp [List.getD, List.getElem?_eq_getElem hmod_lt, u]
      rw [hgetD]
      exact (hper_mod i hi1).symm
  rw [hpw_eq] at hpred
  obtain ⟨j, _, hfail⟩ := failsDerivBy_sound maxK _ hpred
  have hok := kolSeq_slice_iter_deriv_isValid j a L
  rw [hfail] at hok
  exact Bool.false_ne_true hok

/-! ### Kernel-Certified Carpi (1994) Base Cases & Full Cube-Freeness (`0` `native_decide`) -/

private lemma kolSeq_no_defect7_even_base :
    ∀ p ∈ ([10, 12, 14] : List ℕ),
      ¬ ∃ a : ℕ, ∀ i < 2 * p - 7, kolSeq (a + i) = kolSeq (a + i + p) := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact kolSeq_no_periodic_of_check 10 23 3 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 12 29 4 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 14 35 2 (by decide) (by decide) (by decide)

private lemma kolSeq_no_defect7_ge10 :
    ∀ p : ℕ, 10 ≤ p → (p ≥ 15 ∨ p % 2 = 0) →
      ¬ ∃ a : ℕ, ∀ i < 2 * p - 7, kolSeq (a + i) = kolSeq (a + i + p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp10 hcond hex
    rcases lt_or_ge p 15 with hlt | hge
    · have hev : p % 2 = 0 := by rcases hcond with h | h <;> omega
      have hmem : p ∈ ([10, 12, 14] : List ℕ) := by
        have : p = 10 ∨ p = 12 ∨ p = 14 := by omega
        rcases this with rfl | rfl | rfl <;> simp
      exact kolSeq_no_defect7_even_base p hmem hex
    · rcases hex with ⟨a, hper⟩
      obtain ⟨k', q, hq10, hqlt, hqev, hqper⟩ := carpi_period_defect_descent hge hper
      exact ih q hqlt hq10 (Or.inr hqev) ⟨k', hqper⟩

private lemma kolSeq_no_cube_small :
    ∀ p : ℕ, 1 ≤ p → p ≤ 14 →
      ¬ ∃ a : ℕ, ∀ i < 2 * p, kolSeq (a + i) = kolSeq (a + i + p) := by
  intro p hp1 hp14
  interval_cases p
  · exact kolSeq_no_periodic_of_check 1 3 0 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 2 6 1 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 3 9 2 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 4 12 1 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 5 15 1 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 6 18 2 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 7 21 1 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 8 24 3 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 9 27 3 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 10 30 3 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 11 33 2 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 12 36 4 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 13 39 2 (by decide) (by decide) (by decide)
  · exact kolSeq_no_periodic_of_check 14 42 2 (by decide) (by decide) (by decide)

private lemma kolSeq_cube_free (a p : ℕ) (hp : 0 < p) :
    ¬ (∀ i < 2 * p, kolSeq (a + i) = kolSeq (a + i + p)) := by
  intro hper
  rcases le_or_gt p 14 with hle | hgt
  · exact kolSeq_no_cube_small p hp hle ⟨a, hper⟩
  · exact kolSeq_no_defect7_ge10 p (by omega) (Or.inl (by omega))
      ⟨a, fun i hi => hper i (by omega)⟩

end ForbiddenAndCarpi

/-- **Theorem 2.1 (No `111` or `222` Runs in `K`).**
The classical Kolakoski sequence contains no three consecutive equal symbols. -/
theorem ppl044_kolakoski_no_triple (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    ∀ i, ¬ (K i = K (i + 1) ∧ K (i + 1) = K (i + 2)) := by
  have hK := kol_unique hpos hspec; subst hK
  exact kolSeq_no_triple

/-- **Theorem 2.2 (No `12121` or `21212` Alternating Factors in `K`).**
The classical Kolakoski sequence contains neither `[1, 2, 1, 2, 1]` nor `[2, 1, 2, 1, 2]`. -/
theorem ppl044_kolakoski_no_alternating_five (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    ∀ i, List.ofFn (fun j : Fin 5 => K (i + j)) ≠ [1, 2, 1, 2, 1] ∧
         List.ofFn (fun j : Fin 5 => K (i + j)) ≠ [2, 1, 2, 1, 2] := by
  have hK := kol_unique hpos hspec; subst hK
  exact kolSeq_no_alt5

/-- **Theorem 2.3 (No `112211` or `221122` Double-Run Triples in `K`).**
The classical Kolakoski sequence contains neither `[1, 1, 2, 2, 1, 1]` nor `[2, 2, 1, 1, 2, 2]`. -/
theorem ppl044_kolakoski_no_double_triple (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    ∀ i, List.ofFn (fun j : Fin 6 => K (i + j)) ≠ [1, 1, 2, 2, 1, 1] ∧
         List.ofFn (fun j : Fin 6 => K (i + j)) ≠ [2, 2, 1, 1, 2, 2] := by
  have hK := kol_unique hpos hspec; subst hK
  exact kolSeq_no_double_triple

/-- **Theorem 2.4 (Exact Block-Derivative Lifting of Every Factor of `K`).**
Every finite factor `w = K[a .. a + n)` of `K` lifts to an exact contiguous factor `K[c .. c + m)`
of `K` whose run-length expansion contains `w` with at most `1` overhanging symbol on each side. -/
theorem ppl044_kolakoski_block_derivative_invariance (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2)
    (a n : ℕ) :
    ∃ (c m b : ℕ) (p s : List ℕ),
      (b = 1 ∨ b = 2) ∧ p.length ≤ 1 ∧ s.length ≤ 1 ∧
      p ++ List.ofFn (fun i : Fin n => K (a + i)) ++ s =
        (List.ofFn (fun j : Fin m => K (c + j))).zipIdx.flatMap
          (fun q => List.replicate q.1 (if q.2 % 2 = 0 then b else 3 - b)) := by
  have hK := kol_unique hpos hspec; subst hK
  cases n with
  | zero =>
    exact ⟨0, 0, 1, [], [], Or.inl rfl, by simp, by simp, rfl⟩
  | succ n' =>
    obtain ⟨kL, hkL_lo, hkL_hi⟩ := exists_run_index kolSeq_pos a
    obtain ⟨kR, hkR_lo, hkR_hi⟩ := exists_run_index kolSeq_pos (a + n')
    have hkLR : kL ≤ kR := by
      by_contra hlt
      have hle : kolS (kR + 1) ≤ kolS kL := (sum_strict_mono_of_pos kolSeq_pos).monotone (by omega)
      unfold kolS at hle; omega
    have hb : (if kL % 2 = 0 then 1 else 2) = 1 ∨ (if kL % 2 = 0 then 1 else 2) = 2 := by
      split_ifs <;> simp
    refine ⟨kL, kR + 1 - kL, if kL % 2 = 0 then 1 else 2,
      List.ofFn (fun i : Fin (a - kolS kL) => kolSeq (kolS kL + i)),
      List.ofFn (fun i : Fin (kolS (kR + 1) - (a + n' + 1)) => kolSeq ((a + n' + 1) + i)),
      hb, ?_, ?_, ?_⟩
    · rw [List.length_ofFn]
      have h2 : kolSeq kL ≤ 2 := by rcases kolSeq_mem kL with h | h <;> omega
      unfold kolS; rw [Finset.sum_range_succ] at hkL_hi; omega
    · rw [List.length_ofFn]
      have h2 : kolSeq kR ≤ 2 := by rcases kolSeq_mem kR with h | h <;> omega
      unfold kolS; rw [Finset.sum_range_succ] at hkR_hi ⊢; omega
    · rw [← expandFrom_eq_zipIdx _ hb, ← kolSeq_slice_eq_expandFrom kL (kR + 1) (by omega)]
      apply List.ext_getElem
      · simp only [List.length_append, List.length_ofFn]
        unfold kolS at *; omega
      · intro idx hi1 hi2
        rw [List.length_ofFn] at hi2
        rw [List.getElem_ofFn]
        simp only [List.length_append, List.length_ofFn] at hi1
        rcases lt_or_ge idx (a - kolS kL) with hlt1 | hge1
        · rw [List.getElem_append_left (by simp; omega)]
          rw [List.getElem_append_left (by simp; exact hlt1)]
          simp
        · rcases lt_or_ge idx ((a - kolS kL) + (n' + 1)) with hlt2 | hge2
          · rw [List.getElem_append_left (by simp; omega)]
            rw [List.getElem_append_right (by simp; omega)]
            simp only [List.length_ofFn, List.getElem_ofFn]
            congr 1; unfold kolS at *; omega
          · rw [List.getElem_append_right (by simp; exact hge2)]
            simp only [List.length_append, List.length_ofFn, List.getElem_ofFn]
            congr 1; unfold kolS at *; omega

/-- **Theorem 2.5 (Carpi 1994 — Full Cube-Freeness of the Classical Kolakoski Sequence).**
The classical Kolakoski sequence `K` is cube-free: there is no starting index `a : ℕ` and
positive period `p > 0` such that `K[a .. a + p) = K[a + p .. a + 2p) = K[a + 2p .. a + 3p)`. -/
theorem ppl044_kolakoski_cube_free (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    ∀ a p : ℕ, 0 < p → ¬ (∀ i < 2 * p, K (a + i) = K (a + i + p)) := by
  have hK := kol_unique hpos hspec; subst hK
  exact kolSeq_cube_free

/-- **Theorem 2.6 (Non-Ultimate Periodicity of `K`).**
As an immediate corollary of Carpi cube-freeness, the classical Kolakoski sequence `K` is not
ultimately periodic. -/
theorem ppl044_kolakoski_not_ultimately_periodic (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    ¬ ∃ N p : ℕ, 0 < p ∧ ∀ i ≥ N, K (i + p) = K i := by
  rintro ⟨N, p, hp, hper⟩
  exact ppl044_kolakoski_cube_free K hpos hspec N p hp (fun i _ => (hper (N + i) (by omega)).symm)

/-! ## Section 3: Unconditional Explicit Density Bounds (Chvátal / Dekking Smooth-Word Transducer) -/

section ChvatalDensity

private def expandIter : ℕ → List ℕ → List ℕ
  | 0, w => w
  | d + 1, w => expandFrom 1 (expandIter d w)

private lemma expandIter_succ_right (d : ℕ) (w : List ℕ) :
    expandIter (d + 1) w = expandIter d (expandFrom 1 w) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change expandFrom 1 (expandIter (d + 1) w) = expandFrom 1 (expandIter d (expandFrom 1 w))
    rw [ih]

private lemma kolSeq_iterS_prefix (d m : ℕ) :
    List.ofFn (fun i : Fin (kolS^[d] m) => kolSeq i) =
      expandIter d (List.ofFn (fun j : Fin m => kolSeq j)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', expandIter, ← ih]
    have hexp := ppl044_kolakoski_prefix_expansion kolSeq kolSeq_pos kolSeq_run_spec (kolS^[d] m)
    rw [← expandFrom_eq_zipIdx 1 (Or.inl rfl)] at hexp
    exact hexp

private lemma kolS_iter_strict_mono (d : ℕ) : StrictMono (kolS^[d]) := by
  induction d with
  | zero => exact strictMono_id
  | succ d ih =>
    rw [Function.iterate_succ']
    exact (sum_strict_mono_of_pos kolSeq_pos).comp ih

private lemma kolS_iter_zero (d : ℕ) : kolS^[d] 0 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [kolS]

private lemma kolS_iter_ge_self (d m : ℕ) : m ≤ kolS^[d] m := by
  induction d with
  | zero => exact le_refl m
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (sum_ge_self_of_pos kolSeq_pos _)

private def expandWithPar : List Bool → List ℕ → List Bool × List ℕ
  | [], w => ([], w)
  | p :: ps, w =>
    let b := if p then 2 else 1
    let p' := if w.length % 2 = 0 then p else !p
    let w' := expandFrom b w
    let res := expandWithPar ps w'
    (p' :: res.1, res.2)

private lemma expandWithPar_fst_length :
    ∀ (ps : List Bool) (w : List ℕ), (expandWithPar ps w).1.length = ps.length
  | [], _ => rfl
  | _ :: ps, w => by
    simp only [expandWithPar, List.length_cons]
    rw [expandWithPar_fst_length ps]

private lemma expandWithPar_append :
    ∀ (ps : List Bool) (u v : List ℕ),
      expandWithPar ps (u ++ v) =
        ((expandWithPar (expandWithPar ps u).1 v).1,
         (expandWithPar ps u).2 ++ (expandWithPar (expandWithPar ps u).1 v).2)
  | [], u, v => rfl
  | p :: ps, u, v => by
    have hb : (if p then 2 else 1) = 1 ∨ (if p then 2 else 1) = 2 := by
      cases p <;> simp
    have hpar_b : (if (if u.length % 2 = 0 then p else !p) then 2 else 1) =
        if u.length % 2 = 0 then (if p then 2 else 1) else 3 - (if p then 2 else 1) := by
      cases p <;> by_cases h : u.length % 2 = 0 <;> simp [h]
    have hexp : expandFrom (if p then 2 else 1) (u ++ v) =
        expandFrom (if p then 2 else 1) u ++
        expandFrom (if (if u.length % 2 = 0 then p else !p) then 2 else 1) v := by
      rw [expandFrom_append _ hb, hpar_b]
    have hp2 : (if (u ++ v).length % 2 = 0 then p else !p) =
        if v.length % 2 = 0 then (if u.length % 2 = 0 then p else !p)
        else !(if u.length % 2 = 0 then p else !p) := by
      rw [List.length_append]
      cases p <;> split_ifs <;> simp_all <;> omega
    simp only [expandWithPar, hexp, hp2]
    have ih := expandWithPar_append ps
      (expandFrom (if p then 2 else 1) u)
      (expandFrom (if (if u.length % 2 = 0 then p else !p) then 2 else 1) v)
    simp only [ih]

private lemma expandWithPar_replicate_false :
    ∀ (d : ℕ) (w : List ℕ),
      (expandWithPar (List.replicate d false) w).2 = expandIter d w
  | 0, w => rfl
  | d + 1, w => by
    simp only [List.replicate_succ, expandWithPar, Bool.false_eq_true, ↓reduceIte]
    rw [expandWithPar_replicate_false d (expandFrom 1 w), ← expandIter_succ_right]

private def flipLast : List Bool → List Bool
  | [] => []
  | [p] => [!p]
  | p :: q :: qs => p :: flipLast (q :: qs)

private lemma flipLast_length : ∀ (ps : List Bool), (flipLast ps).length = ps.length
  | [] => rfl
  | [_] => rfl
  | _ :: q :: qs => by simp [flipLast, flipLast_length (q :: qs)]

private lemma flipLast_cons_of_ne_nil (p : Bool) {ps : List Bool} (hps : ps ≠ []) :
    flipLast (p :: ps) = p :: flipLast ps := by
  cases ps with
  | nil => exact (hps rfl).elim
  | cons q qs => rfl

private lemma expandWithPar_flipLast :
    ∀ (ps : List Bool), ps ≠ [] → ∀ (w : List ℕ),
      (expandWithPar (flipLast ps) w).1 = flipLast (expandWithPar ps w).1 ∧
      (expandWithPar (flipLast ps) w).2 = (expandWithPar ps w).2.map (fun x => 3 - x)
  | [], h, _ => (h rfl).elim
  | [p], _, w => by
    have hb : (if p then 2 else 1) = 1 ∨ (if p then 2 else 1) = 2 := by cases p <;> simp
    have hbf : (if !p then 2 else 1) = 3 - (if p then 2 else 1) := by cases p <;> rfl
    have hpf : (if w.length % 2 = 0 then !p else !!p) = !(if w.length % 2 = 0 then p else !p) := by
      cases p <;> split_ifs <;> rfl
    simp only [flipLast, expandWithPar, hpf, hbf]
    exact ⟨trivial, (expandFrom_map_swap _ hb w).symm⟩
  | p :: q :: qs, _, w => by
    have ih := expandWithPar_flipLast (q :: qs) (List.cons_ne_nil q qs)
      (expandFrom (if p then 2 else 1) w)
    have hne : (expandWithPar (q :: qs) (expandFrom (if p then 2 else 1) w)).1 ≠ [] := by
      intro hemp
      have hlen := expandWithPar_fst_length (q :: qs) (expandFrom (if p then 2 else 1) w)
      rw [hemp] at hlen
      simp at hlen
    change ((if w.length % 2 = 0 then p else !p) ::
              (expandWithPar (flipLast (q :: qs)) (expandFrom (if p then 2 else 1) w)).1 =
            flipLast ((if w.length % 2 = 0 then p else !p) ::
              (expandWithPar (q :: qs) (expandFrom (if p then 2 else 1) w)).1)) ∧
           (expandWithPar (flipLast (q :: qs)) (expandFrom (if p then 2 else 1) w)).2 =
            (expandWithPar (q :: qs) (expandFrom (if p then 2 else 1) w)).2.map (fun x => 3 - x)
    rw [flipLast_cons_of_ne_nil _ hne]
    exact ⟨congrArg (List.cons _) ih.1, ih.2⟩

private lemma expandWithPar_mem :
    ∀ (ps : List Bool), ps ≠ [] → ∀ (w : List ℕ) (x : ℕ),
      x ∈ (expandWithPar ps w).2 → x = 1 ∨ x = 2
  | [], h, _, _, _ => (h rfl).elim
  | [p], _, w, x, hx => by
    have hb : (if p then 2 else 1) = 1 ∨ (if p then 2 else 1) = 2 := by cases p <;> simp
    exact expandFrom_mem _ hb w x hx
  | p :: q :: qs, _, w, x, hx =>
    expandWithPar_mem (q :: qs) (List.cons_ne_nil q qs) _ x hx

private lemma expandWithPar_length_le :
    ∀ (ps : List Bool) (w : List ℕ), (∀ x ∈ w, x ≤ 2) →
      (expandWithPar ps w).2.length ≤ 2 ^ ps.length * w.length
  | [], w, _ => by simp [expandWithPar]
  | p :: ps, w, hw => by
    have hb : (if p then 2 else 1) = 1 ∨ (if p then 2 else 1) = 2 := by cases p <;> simp
    have hw' : ∀ x ∈ expandFrom (if p then 2 else 1) w, x ≤ 2 := by
      intro x hx
      rcases expandFrom_mem _ hb w x hx with rfl | rfl <;> omega
    have hsum : w.sum ≤ 2 * w.length := by
      clear hb hw' ps p
      induction w with
      | nil => simp
      | cons a xs ih =>
        have ha : a ≤ 2 := hw a (List.mem_cons_self ..)
        have hxs := ih (fun y hy => hw y (List.mem_cons_of_mem a hy))
        simp only [List.sum_cons, List.length_cons]
        omega
    have ih := expandWithPar_length_le ps (expandFrom (if p then 2 else 1) w) hw'
    simp only [expandWithPar, List.length_cons, pow_succ]
    rw [expandFrom_length] at ih
    calc (expandWithPar ps (expandFrom (if p then 2 else 1) w)).2.length
        ≤ 2 ^ ps.length * w.sum := ih
      _ ≤ 2 ^ ps.length * (2 * w.length) := Nat.mul_le_mul_left _ hsum
      _ = 2 ^ ps.length * 2 * w.length := by ring

private lemma count_swap_eq_sub :
    ∀ (w : List ℕ), (∀ x ∈ w, x = 1 ∨ x = 2) →
      (w.map (fun x => 3 - x)).count 1 + w.count 1 = w.length
  | [], _ => rfl
  | a :: xs, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := count_swap_eq_sub xs (fun y hy => h y (List.mem_cons_of_mem a hy))
    simp only [List.map_cons, List.count_cons, List.length_cons]
    rcases ha with rfl | rfl <;> simp <;> omega

private lemma kolSeq_prefix_count1 (N : ℕ) :
    ((Finset.range N).filter (fun i => kolSeq i = 1)).card =
      (List.ofFn (fun i : Fin N => kolSeq i)).count 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append, List.count_singleton,
      Finset.range_add_one, Finset.filter_insert]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases h1 : kolSeq N = 1
    · simp [h1, Finset.card_insert_of_notMem, ih]
    · simp [h1, ih]

/-- Encode a parity vector `ps` of length `d` as an integer in `[0, 2^d)`. -/
private def parToNat : List Bool → ℕ
  | [] => 0
  | p :: ps => (if p then 1 else 0) + 2 * parToNat ps

private def natToPar : ℕ → ℕ → List Bool
  | 0, _ => []
  | d + 1, n => (n % 2 == 1) :: natToPar d (n / 2)

private lemma natToPar_length : ∀ d n, (natToPar d n).length = d
  | 0, _ => rfl
  | d + 1, n => by simp [natToPar, natToPar_length d]

private lemma parToNat_lt : ∀ (ps : List Bool), parToNat ps < 2 ^ ps.length
  | [] => by simp [parToNat]
  | p :: ps => by
    have ih := parToNat_lt ps
    simp only [parToNat, List.length_cons, pow_succ]
    cases p <;> simp <;> omega

private lemma natToPar_parToNat : ∀ (ps : List Bool), natToPar ps.length (parToNat ps) = ps
  | [] => rfl
  | p :: ps => by
    simp only [List.length_cons, parToNat, natToPar]
    cases p
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      have hmod : (2 * parToNat ps) % 2 = 0 := by omega
      have hdiv : (2 * parToNat ps) / 2 = parToNat ps := by omega
      simp [hmod, hdiv, natToPar_parToNat ps]
    · simp only [↓reduceIte]
      have hmod : (1 + 2 * parToNat ps) % 2 = 1 := by omega
      have hdiv : (1 + 2 * parToNat ps) / 2 = parToNat ps := by omega
      simp [hmod, hdiv, natToPar_parToNat ps]

/-- General Telescoping Density Bound Theorem for a Depth-`d` Chvátal Transducer with
`2`-letter suffix memory (avoiding `111`/`222`). Given a potential `φ : List Bool → ℕ → ℕ → ℤ`
bounded by `|φ| ≤ M`, if every valid transition `(ps, a, b) --x--> (ps', b, x)` satisfies
`numLo * L ≤ den * C1 + φ ps' b x - φ ps a b`, then `K` satisfies explicit non-asymptotic and
asymptotic bounds `|freq_1(N) - 1/2| ≤ (den - 2 * numLo) / (2 * den) + C / N`! -/
private lemma chvatal_transducer_density_bound
    (d : ℕ) (hd : 1 ≤ d) (numLo den : ℤ) (hden : 0 < den) (hlo_le : 2 * numLo ≤ den)
    (_hlo_nn : 0 ≤ numLo)
    (φ : List Bool → ℕ → ℕ → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hφ_bound : ∀ ps a b, ps.length = d → (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) → |φ ps a b| ≤ M)
    (hstep : ∀ (ps : List Bool) (a b x : ℕ),
      ps.length = d → (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) → (x = 1 ∨ x = 2) →
      ¬ (a = b ∧ b = x) →
      let res := expandWithPar ps [x]
      numLo * (res.2.length : ℤ) ≤ den * (res.2.count 1 : ℤ) + φ res.1 b x - φ ps a b) :
    let C : ℝ := ((2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ) : ℤ) : ℝ) / (den : ℝ)
    (∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        ((den - 2 * numLo : ℤ) : ℝ) / (2 * (den : ℝ)) + C / (N : ℝ)) := by
  intro C
  -- Track parity trajectory `parAt m = (expandWithPar (replicate d false) (kolSeq[0..m))).1`
  let parAt : ℕ → List Bool := fun m =>
    (expandWithPar (List.replicate d false) (List.ofFn (fun i : Fin m => kolSeq i))).1
  have hpar_len : ∀ m, (parAt m).length = d := by
    intro m; simp [parAt, expandWithPar_fst_length]
  have hpar_step : ∀ m,
      expandWithPar (List.replicate d false) (List.ofFn (fun i : Fin (m + 1) => kolSeq i)) =
      ((expandWithPar (parAt m) [kolSeq m]).1,
       (expandWithPar (List.replicate d false) (List.ofFn (fun i : Fin m => kolSeq i))).2 ++
       (expandWithPar (parAt m) [kolSeq m]).2) := by
    intro m
    rw [List.ofFn_succ', List.concat_eq_append, expandWithPar_append]
    simp [parAt]
  have hout_eq : ∀ m,
      (expandWithPar (List.replicate d false) (List.ofFn (fun i : Fin m => kolSeq i))).2 =
      List.ofFn (fun i : Fin (kolS^[d] m) => kolSeq i) := by
    intro m
    rw [expandWithPar_replicate_false, ← kolSeq_iterS_prefix]
  -- Both lower and upper telescoping inequalities for `m ≥ 2`
  have htel_both : ∀ m, 2 ≤ m →
      numLo * ((kolS^[d] m : ℤ) - (kolS^[d] 2 : ℤ)) ≤
        den * ((((Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1)).card : ℤ) -
               (((Finset.range (kolS^[d] 2)).filter (fun i => kolSeq i = 1)).card : ℤ)) +
        φ (parAt m) (kolSeq (m - 2)) (kolSeq (m - 1)) -
        φ (parAt 2) (kolSeq 0) (kolSeq 1) ∧
      den * ((((Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1)).card : ℤ) -
             (((Finset.range (kolS^[d] 2)).filter (fun i => kolSeq i = 1)).card : ℤ)) +
        (- φ (flipLast (parAt m)) (kolSeq (m - 2)) (kolSeq (m - 1))) -
        (- φ (flipLast (parAt 2)) (kolSeq 0) (kolSeq 1)) ≤
        (den - numLo) * ((kolS^[d] m : ℤ) - (kolS^[d] 2 : ℤ)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases eq_or_lt_of_le hm with heq | hgt
      · have hm1 : m = 1 := by omega
        subst hm1
        simp
      · obtain ⟨ih_lo, ih_hi⟩ := ih (by omega)
        have hstep_m := hpar_step m
        have hpar_succ : parAt (m + 1) = (expandWithPar (parAt m) [kolSeq m]).1 := by
          unfold parAt; rw [hstep_m]
        have hout_succ : List.ofFn (fun i : Fin (kolS^[d] (m + 1)) => kolSeq i) =
            List.ofFn (fun i : Fin (kolS^[d] m) => kolSeq i) ++
            (expandWithPar (parAt m) [kolSeq m]).2 := by
          rw [← hout_eq (m + 1), hstep_m, hout_eq m]
        have hlen_succ : kolS^[d] (m + 1) = kolS^[d] m + (expandWithPar (parAt m) [kolSeq m]).2.length := by
          have := congrArg List.length hout_succ
          simpa only [List.length_ofFn, List.length_append] using this
        have hcnt_succ :
            ((Finset.range (kolS^[d] (m + 1))).filter (fun i => kolSeq i = 1)).card =
            ((Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1)).card +
            (expandWithPar (parAt m) [kolSeq m]).2.count 1 := by
          rw [kolSeq_prefix_count1, kolSeq_prefix_count1, hout_succ, List.count_append]
        have hno3 : ¬ (kolSeq (m - 2) = kolSeq (m - 1) ∧ kolSeq (m - 1) = kolSeq m) := by
          have h1 : m - 1 = (m - 2) + 1 := by omega
          have h2 : m = (m - 2) + 2 := by omega
          rw [h1, h2]; exact kolSeq_no_triple (m - 2)
        have hidx1 : (m + 1) - 2 = m - 1 := by omega
        have hidx2 : (m + 1) - 1 = m := by omega
        have hstep_lo := hstep (parAt m) (kolSeq (m - 2)) (kolSeq (m - 1)) (kolSeq m)
          (hpar_len m) (kolSeq_mem _) (kolSeq_mem _) (kolSeq_mem _) hno3
        -- Dual step via `flipLast` for the upper bound!
        have hne : parAt m ≠ [] := by
          intro h0; have := hpar_len m; rw [h0] at this; simp at this; omega
        have hfl_len : (flipLast (parAt m)).length = d := by
          rw [flipLast_length, hpar_len]
        have hstep_dual := hstep (flipLast (parAt m)) (kolSeq (m - 2)) (kolSeq (m - 1)) (kolSeq m)
          hfl_len (kolSeq_mem _) (kolSeq_mem _) (kolSeq_mem _) hno3
        have hfl := expandWithPar_flipLast (parAt m) hne [kolSeq m]
        have hswap_cnt : ((expandWithPar (parAt m) [kolSeq m]).2.map (fun x => 3 - x)).count 1 +
            (expandWithPar (parAt m) [kolSeq m]).2.count 1 =
            (expandWithPar (parAt m) [kolSeq m]).2.length :=
          count_swap_eq_sub _ (expandWithPar_mem (parAt m) hne [kolSeq m])
        have hstep_hi :
            den * ((expandWithPar (parAt m) [kolSeq m]).2.count 1 : ℤ) +
              (- φ (flipLast (parAt (m + 1))) (kolSeq (m - 1)) (kolSeq m)) -
              (- φ (flipLast (parAt m)) (kolSeq (m - 2)) (kolSeq (m - 1))) ≤
            (den - numLo) * ((expandWithPar (parAt m) [kolSeq m]).2.length : ℤ) := by
          dsimp only at hstep_dual
          rw [hfl.1, hfl.2, List.length_map, ← hpar_succ] at hstep_dual
          have hcntZ : (((expandWithPar (parAt m) [kolSeq m]).2.map (fun x => 3 - x)).count 1 : ℤ) =
              ((expandWithPar (parAt m) [kolSeq m]).2.length : ℤ) -
              ((expandWithPar (parAt m) [kolSeq m]).2.count 1 : ℤ) := by omega
          rw [hcntZ] at hstep_dual
          linarith
        dsimp only at hstep_lo
        rw [← hpar_succ] at hstep_lo
        rw [hidx1, hidx2]
        have hlenZ : (kolS^[d] (m + 1) : ℤ) = (kolS^[d] m : ℤ) +
            ((expandWithPar (parAt m) [kolSeq m]).2.length : ℤ) := by exact_mod_cast hlen_succ
        have hcntZ : (((Finset.range (kolS^[d] (m + 1))).filter (fun i => kolSeq i = 1)).card : ℤ) =
            (((Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1)).card : ℤ) +
            ((expandWithPar (parAt m) [kolSeq m]).2.count 1 : ℤ) := by exact_mod_cast hcnt_succ
        rw [hlenZ, hcntZ]
        exact ⟨by linarith, by linarith⟩
  -- Deduce uniform bound at every `N ≥ 1` by interpolating `kolS^[d] m ≤ N < kolS^[d] (m + 1)`
  intro N hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hreach : ∃ m, N < kolS^[d] m :=
    ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N) (kolS_iter_ge_self d (N + 1))⟩
  let m1 := Nat.find hreach
  have hm1_spec : N < kolS^[d] m1 := Nat.find_spec hreach
  have hm1_ne0 : m1 ≠ 0 := by intro h0; rw [h0, kolS_iter_zero] at hm1_spec; omega
  let m := m1 - 1
  have hm_lo : kolS^[d] m ≤ N := by
    have hlt : m < m1 := Nat.sub_lt (Nat.pos_of_ne_zero hm1_ne0) Nat.one_pos
    have := Nat.find_min hreach hlt
    omega
  have hm_hi : N < kolS^[d] (m + 1) := by
    have : m + 1 = m1 := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm1_ne0)
    rwa [this]
  have hstep_gap : kolS^[d] (m + 1) - kolS^[d] m ≤ 2 ^ d := by
    have hout_succ : List.ofFn (fun i : Fin (kolS^[d] (m + 1)) => kolSeq i) =
        List.ofFn (fun i : Fin (kolS^[d] m) => kolSeq i) ++
        (expandWithPar (parAt m) [kolSeq m]).2 := by
      rw [← hout_eq (m + 1), hpar_step m, hout_eq m]
    have hlen_succ : kolS^[d] (m + 1) = kolS^[d] m + (expandWithPar (parAt m) [kolSeq m]).2.length := by
      have := congrArg List.length hout_succ
      simpa only [List.length_ofFn, List.length_append] using this
    have hle : (expandWithPar (parAt m) [kolSeq m]).2.length ≤ 2 ^ d * 1 := by
      have h1 := expandWithPar_length_le (parAt m) [kolSeq m] (by
        intro x hx; simp at hx; subst hx; rcases kolSeq_mem m with h | h <;> omega)
      simpa [hpar_len m] using h1
    omega
  -- Count at `N` vs count at `kolS^[d] m`
  let cntN : ℕ := ((Finset.range N).filter (fun i => kolSeq i = 1)).card
  let cntM : ℕ := ((Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1)).card
  have hcnt_lo : cntM ≤ cntN :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hm_lo))
  have hcnt_hi : cntN ≤ cntM + (N - kolS^[d] m) := by
    have hsub : (Finset.range N).filter (fun i => kolSeq i = 1) ⊆
        (Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1) ∪ Finset.Ico (kolS^[d] m) N := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hx ⊢
      by_cases hxM : x < kolS^[d] m
      · exact Or.inl ⟨hxM, hx.2⟩
      · exact Or.inr ⟨by omega, hx.1⟩
    calc cntN ≤ ((Finset.range (kolS^[d] m)).filter (fun i => kolSeq i = 1) ∪
          Finset.Ico (kolS^[d] m) N).card := Finset.card_le_card hsub
      _ ≤ cntM + (Finset.Ico (kolS^[d] m) N).card := Finset.card_union_le _ _
      _ = cntM + (N - kolS^[d] m) := by rw [Nat.card_Ico]
  -- Bounds on `den * cntM` whether `m < 2` or `2 ≤ m`
  have hB_bounds :
      numLo * (kolS^[d] m : ℤ) - (2 * M + den * (kolS^[d] 2 : ℤ)) ≤ den * (cntM : ℤ) ∧
      den * (cntM : ℤ) ≤ (den - numLo) * (kolS^[d] m : ℤ) + (2 * M + den * (kolS^[d] 2 : ℤ)) := by
    rcases lt_or_ge m 2 with hm2 | hm2
    · have hS_le : kolS^[d] m ≤ kolS^[d] 2 := (kolS_iter_strict_mono d).monotone (by omega)
      have hcntM_le : cntM ≤ kolS^[d] m := by
        calc cntM ≤ (Finset.range (kolS^[d] m)).card := Finset.card_filter_le _ _
          _ = kolS^[d] m := Finset.card_range _
      have hnum_le_den : numLo ≤ den := by linarith
      constructor
      · nlinarith
      · nlinarith
    · obtain ⟨hlo, hhi⟩ := htel_both m hm2
      have hφ1 : |φ (parAt m) (kolSeq (m - 2)) (kolSeq (m - 1))| ≤ M :=
        hφ_bound _ _ _ (hpar_len m) (kolSeq_mem _) (kolSeq_mem _)
      have hφ2 : |φ (parAt 2) (kolSeq 0) (kolSeq 1)| ≤ M :=
        hφ_bound _ _ _ (hpar_len 2) (kolSeq_mem _) (kolSeq_mem _)
      have hφ3 : |φ (flipLast (parAt m)) (kolSeq (m - 2)) (kolSeq (m - 1))| ≤ M :=
        hφ_bound _ _ _ (by rw [flipLast_length, hpar_len]) (kolSeq_mem _) (kolSeq_mem _)
      have hφ4 : |φ (flipLast (parAt 2)) (kolSeq 0) (kolSeq 1)| ≤ M :=
        hφ_bound _ _ _ (by rw [flipLast_length, hpar_len]) (kolSeq_mem _) (kolSeq_mem _)
      rw [abs_le] at hφ1 hφ2 hφ3 hφ4
      have hcnt2_le : ((Finset.range (kolS^[d] 2)).filter (fun i => kolSeq i = 1)).card ≤ kolS^[d] 2 := by
        calc _ ≤ (Finset.range (kolS^[d] 2)).card := Finset.card_filter_le _ _
          _ = kolS^[d] 2 := Finset.card_range _
      have hcnt2_nn : (0 : ℤ) ≤ (((Finset.range (kolS^[d] 2)).filter (fun i => kolSeq i = 1)).card : ℤ) :=
        Nat.cast_nonneg _
      have hcnt2_leZ : (((Finset.range (kolS^[d] 2)).filter (fun i => kolSeq i = 1)).card : ℤ) ≤
          (kolS^[d] 2 : ℤ) := by exact_mod_cast hcnt2_le
      have hnum_le_den : numLo ≤ den := by linarith
      constructor <;> nlinarith
  -- Transfer from `kolS^[d] m` to `N`
  have hN_bounds :
      numLo * (N : ℤ) - (2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ)) ≤ den * (cntN : ℤ) ∧
      den * (cntN : ℤ) ≤ (den - numLo) * (N : ℤ) + (2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ)) := by
    have hgapZ : (N : ℤ) - (kolS^[d] m : ℤ) ≤ (2 ^ d : ℤ) := by
      have : N - kolS^[d] m ≤ 2 ^ d := by omega
      have h1 : ((N - kolS^[d] m : ℕ) : ℤ) ≤ (2 ^ d : ℤ) := by exact_mod_cast this
      have h2 : ((N - kolS^[d] m : ℕ) : ℤ) + (kolS^[d] m : ℤ) = (N : ℤ) := by
        exact_mod_cast Nat.sub_add_cancel hm_lo
      linarith
    have hgap_nn : (0 : ℤ) ≤ (N : ℤ) - (kolS^[d] m : ℤ) := by
      have : (kolS^[d] m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm_lo
      linarith
    have hcnt_loZ : (cntM : ℤ) ≤ (cntN : ℤ) := by exact_mod_cast hcnt_lo
    have hcnt_hiZ : (cntN : ℤ) ≤ (cntM : ℤ) + ((N : ℤ) - (kolS^[d] m : ℤ)) := by
      have h1 : (cntN : ℤ) ≤ (cntM : ℤ) + ((N - kolS^[d] m : ℕ) : ℤ) := by exact_mod_cast hcnt_hi
      have h2 : ((N - kolS^[d] m : ℕ) : ℤ) + (kolS^[d] m : ℤ) = (N : ℤ) := by
        exact_mod_cast Nat.sub_add_cancel hm_lo
      linarith
    have hnum_le_den : numLo ≤ den := by linarith
    constructor <;> nlinarith [hB_bounds.1, hB_bounds.2]
  -- Cast to ℝ and conclude `|cntN / N - 1/2| ≤ (den - 2*numLo)/(2*den) + C / N`
  have hloR : (numLo : ℝ) * (N : ℝ) - ((2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ) : ℤ) : ℝ) ≤
      (den : ℝ) * (cntN : ℝ) := by exact_mod_cast hN_bounds.1
  have hhiR : (den : ℝ) * (cntN : ℝ) ≤
      ((den - numLo : ℤ) : ℝ) * (N : ℝ) + ((2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hN_bounds.2
  have hsub_cast1 : ((den - numLo : ℤ) : ℝ) = (den : ℝ) - (numLo : ℝ) := by push_cast; ring
  have hsub_cast2 : ((den - 2 * numLo : ℤ) : ℝ) = (den : ℝ) - 2 * (numLo : ℝ) := by push_cast; ring
  rw [hsub_cast1] at hhiR
  rw [hsub_cast2, abs_le]
  have hC_eq : C * (den : ℝ) = ((2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ) : ℤ) : ℝ) := by
    unfold C; field_simp
  constructor
  · have h1 : (numLo : ℝ) / (den : ℝ) - C / (N : ℝ) ≤ (cntN : ℝ) / (N : ℝ) := by
      rw [div_sub_div _ _ (ne_of_gt hden_pos) (ne_of_gt hN_pos)]
      rw [div_le_div_iff₀ (mul_pos hden_pos hN_pos) hN_pos]
      nlinarith
    have h2 : (1 / 2 : ℝ) - ((den : ℝ) - 2 * (numLo : ℝ)) / (2 * (den : ℝ)) = (numLo : ℝ) / (den : ℝ) := by
      field_simp; ring
    linarith
  · have h1 : (cntN : ℝ) / (N : ℝ) ≤ ((den : ℝ) - (numLo : ℝ)) / (den : ℝ) + C / (N : ℝ) := by
      rw [div_add_div _ _ (ne_of_gt hden_pos) (ne_of_gt hN_pos)]
      rw [div_le_div_iff₀ hN_pos (mul_pos hden_pos hN_pos)]
      nlinarith
    have h2 : (1 / 2 : ℝ) + ((den : ℝ) - 2 * (numLo : ℝ)) / (2 * (den : ℝ)) =
        ((den : ℝ) - (numLo : ℝ)) / (den : ℝ) := by
      field_simp; ring
    linarith

private def lookupPhi (table : List ℤ) (ps : List Bool) (a b : ℕ) : ℤ :=
  table.getD (parToNat ps * 4 + (a - 1) * 2 + (b - 1)) 0

private def checkChvatalTable (d : ℕ) (numLo den M : ℤ) (table : List ℤ) : Bool :=
  (List.range (2 ^ d)).all fun pIdx =>
    let ps := natToPar d pIdx
    ([1, 2] : List ℕ).all fun a =>
      ([1, 2] : List ℕ).all fun b =>
        let phiU := lookupPhi table ps a b
        (decide (-M ≤ phiU) && decide (phiU ≤ M)) &&
        ([1, 2] : List ℕ).all fun x =>
          if a == b && b == x then true
          else
            let res := expandWithPar ps [x]
            let phiV := lookupPhi table res.1 b x
            decide (numLo * (res.2.length : ℤ) ≤ den * (res.2.count 1 : ℤ) + phiV - phiU)

private lemma chvatal_of_table_check
    (d : ℕ) (hd : 1 ≤ d) (numLo den M : ℤ)
    (hden : 0 < den) (hlo_le : 2 * numLo ≤ den) (hlo_nn : 0 ≤ numLo) (hM : 0 ≤ M)
    (table : List ℤ) (hchk : checkChvatalTable d numLo den M table = true) :
    let C : ℝ := ((2 * M + den * (kolS^[d] 2 : ℤ) + den * (2 ^ d : ℤ) : ℤ) : ℝ) / (den : ℝ)
    ∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        ((den - 2 * numLo : ℤ) : ℝ) / (2 * (den : ℝ)) + C / (N : ℝ) := by
  have hmem12 : ∀ z : ℕ, (z = 1 ∨ z = 2) → z ∈ ([1, 2] : List ℕ) := by
    intro z hz; rcases hz with rfl | rfl <;> simp
  have hall := List.all_eq_true.mp hchk
  apply chvatal_transducer_density_bound d hd numLo den hden hlo_le hlo_nn
    (lookupPhi table) M hM
  · intro ps a b hlen ha hb
    have hpIdx : parToNat ps ∈ List.range (2 ^ d) := by
      rw [List.mem_range, ← hlen]; exact parToNat_lt ps
    have h1 := List.all_eq_true.mp (hall (parToNat ps) hpIdx) a (hmem12 a ha)
    have h2 := List.all_eq_true.mp h1 b (hmem12 b hb)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have hps_eq : natToPar d (parToNat ps) = ps := by rw [← hlen, natToPar_parToNat]
    rw [hps_eq] at h2
    exact abs_le.mpr ⟨h2.1.1, h2.1.2⟩
  · intro ps a b x hlen ha hb hx hno3
    have hpIdx : parToNat ps ∈ List.range (2 ^ d) := by
      rw [List.mem_range, ← hlen]; exact parToNat_lt ps
    have h1 := List.all_eq_true.mp (hall (parToNat ps) hpIdx) a (hmem12 a ha)
    have h2 := List.all_eq_true.mp h1 b (hmem12 b hb)
    simp only [Bool.and_eq_true] at h2
    have h3 := List.all_eq_true.mp h2.2 x (hmem12 x hx)
    have hps_eq : natToPar d (parToNat ps) = ps := by rw [← hlen, natToPar_parToNat]
    rw [hps_eq] at h3
    have hcond : ¬ ((a == b) = true ∧ (b == x) = true) := by
      intro ⟨h1', h2'⟩
      simp only [beq_iff_eq] at h1' h2'
      exact hno3 ⟨h1', h2'⟩
    rw [if_neg hcond] at h3
    simpa only [decide_eq_true_eq] using h3

private def chvatalPhi4 : List ℤ :=
  [26, 22, 22, 24, 15, 17, 1, 10, 11, 36, 27, 32, 27, 25, 29, 21,
    9, 19, 25, 14, 26, 30, 35, 28, 22, 3, 17, 3, 19, 19, 12, 28,
    0, 1, 8, 0, 8, 12, 17, 8, 4, 0, 0, 0, 1, 2, 0, 11,
    9, 7, 5, 7, 0, 0, 0, 0, 10, 19, 10, 15, 10, 8, 12, 0]

private lemma chvatalPhi4_valid : checkChvatalTable 4 11 23 36 chvatalPhi4 = true := by decide

private lemma kolS_le_two_mul (m : ℕ) : kolS m ≤ 2 * m := by
  unfold kolS
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h2 : kolSeq m ≤ 2 := by rcases kolSeq_mem m with h | h <;> omega
    omega

private lemma kolS_iter_le (d m : ℕ) : kolS^[d] m ≤ 2 ^ d * m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have := kolS_le_two_mul (kolS^[d] m)
    nlinarith

end ChvatalDensity

/-- **Theorem 3.1 (Baseline `[1/3, 2/3]` Density Bounds for `K`).**
Because `K` avoids `111` and `222`, every `3`-term block contains either `1` or `2` ones,
yielding explicit non-asymptotic bounds `|freq_1(N) - 1/2| ≤ 1/6 + 2 / N` for all `N ≥ 1`.
(Strictly sharpened by Theorem 3.2 via the Chvátal smooth-word transducer.) -/
theorem ppl044_kolakoski_trivial_density_bounds (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    ∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => K i = 1)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        (1 / 6 : ℝ) + (2 : ℝ) / (N : ℝ) := by
  have hK := kol_unique hpos hspec; subst hK
  have htriple_card : ∀ a : ℕ,
      1 ≤ ((Finset.Ico a (a + 3)).filter (fun i => kolSeq i = 1)).card ∧
      ((Finset.Ico a (a + 3)).filter (fun i => kolSeq i = 1)).card ≤ 2 := by
    intro a
    have hIco : Finset.Ico a (a + 3) = {a, a + 1, a + 2} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]; omega
    have h0 := kolSeq_mem a
    have h1 := kolSeq_mem (a + 1)
    have h2 := kolSeq_mem (a + 2)
    have hnt := kolSeq_no_triple a
    rw [hIco]
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso; exact hnt ⟨by omega, by omega⟩
    · simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · exfalso; exact hnt ⟨by omega, by omega⟩
  have hmul3 : ∀ q : ℕ,
      q ≤ ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1)).card ∧
      ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1)).card ≤ 2 * q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have hsplit : Finset.range (3 * (q + 1)) = Finset.range (3 * q) ∪ Finset.Ico (3 * q) (3 * q + 3) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (3 * q)) (Finset.Ico (3 * q) (3 * q + 3)) := by
        rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; omega
      rw [hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
      have ht := htriple_card (3 * q)
      omega
  intro N hN
  let q := N / 3
  have h3q_le : 3 * q ≤ N := Nat.mul_div_le N 3
  have hgap : N - 3 * q ≤ 2 := by unfold q; omega
  have hlo_c : ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1)).card ≤
      ((Finset.range N).filter (fun i => kolSeq i = 1)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h3q_le))
  have hhi_c : ((Finset.range N).filter (fun i => kolSeq i = 1)).card ≤
      ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1)).card + (N - 3 * q) := by
    have hsub : (Finset.range N).filter (fun i => kolSeq i = 1) ⊆
        (Finset.range (3 * q)).filter (fun i => kolSeq i = 1) ∪ Finset.Ico (3 * q) N := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hx ⊢
      by_cases h : x < 3 * q
      · exact Or.inl ⟨h, hx.2⟩
      · exact Or.inr ⟨by omega, hx.1⟩
    calc _ ≤ ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1) ∪ Finset.Ico (3 * q) N).card :=
          Finset.card_le_card hsub
      _ ≤ ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1)).card + (Finset.Ico (3 * q) N).card :=
          Finset.card_union_le _ _
      _ = ((Finset.range (3 * q)).filter (fun i => kolSeq i = 1)).card + (N - 3 * q) := by
          rw [Nat.card_Ico]
  obtain ⟨hq1, hq2⟩ := hmul3 q
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcnt_lo : (N : ℝ) - 2 ≤ 3 * (((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) := by
    have hnat : N ≤ 3 * ((Finset.range N).filter (fun i => kolSeq i = 1)).card + 2 := by omega
    have : (N : ℝ) ≤ 3 * (((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) + 2 := by
      exact_mod_cast hnat
    linarith
  have hcnt_hi : 3 * (((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) ≤ 2 * (N : ℝ) + 6 := by
    have hnat : 3 * ((Finset.range N).filter (fun i => kolSeq i = 1)).card ≤ 2 * N + 6 := by omega
    exact_mod_cast hnat
  rw [abs_le]
  constructor
  · have h1 : (1 / 3 : ℝ) - 2 / (N : ℝ) ≤
        (((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) / (N : ℝ) := by
      rw [div_sub_div _ _ (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hN_pos)]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (N : ℝ)) hN_pos]
      nlinarith
    linarith
  · have h1 : (((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) / (N : ℝ) ≤
        (2 / 3 : ℝ) + 2 / (N : ℝ) := by
      rw [div_add_div _ _ (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hN_pos)]
      rw [div_le_div_iff₀ hN_pos (by positivity : (0 : ℝ) < 3 * (N : ℝ))]
      nlinarith
    linarith

/-- **Theorem 3.2 (Unconditional Explicit Chvátal / Dekking Smooth-Word Density Bound).**
Using the depth-`4` smooth-word parity transducer (`64` states) and a kernel-certified integer
Bellman–Ford potential (`0` `native_decide`), the frequency of `1`s in the classical Kolakoski
sequence `K` strictly sharpens the trivial `[1/3, 2/3]` (`1/6 ≈ 0.1667`) bound by `> 7.6×`
down to `[11/23, 12/23]` (`1/46 ≈ 0.02174`):
1. **Non-asymptotic (all `N ≥ 1`):** `|freq_1(N) - 1/2| ≤ 1 / 46 + 52 / N`.
2. **Asymptotic:** `∀ᶠ N in atTop, 47 / 100 ≤ freq_1(N) ∧ freq_1(N) ≤ 53 / 100` (and
   `|freq_1(N) - 1/2| ≤ 1 / 45`). -/
theorem ppl044_kolakoski_chvatal_density_bound (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    (∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => K i = 1)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        (1 / 46 : ℝ) + (52 : ℝ) / (N : ℝ)) ∧
    (∀ᶠ N : ℕ in Filter.atTop,
      |(((Finset.range N).filter (fun i => K i = 1)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        (1 / 45 : ℝ)) := by
  have hK := kol_unique hpos hspec; subst hK
  have hraw := chvatal_of_table_check 4 (by decide) 11 23 36
    (by decide) (by decide) (by decide) (by decide) chvatalPhi4 chvatalPhi4_valid
  have hS4_le : kolS^[4] 2 ≤ 32 := by
    have := kolS_iter_le 4 2
    omega
  have hC_le : (((2 * (36 : ℤ) + 23 * (kolS^[4] 2 : ℤ) + 23 * (2 ^ 4 : ℤ) : ℤ) : ℝ) / ((23 : ℤ) : ℝ)) ≤ 52 := by
    have hZ : (2 * (36 : ℤ) + 23 * (kolS^[4] 2 : ℤ) + 23 * (2 ^ 4 : ℤ)) ≤ 23 * 52 := by
      have hS4Z : (kolS^[4] 2 : ℤ) ≤ 32 := by exact_mod_cast hS4_le
      linarith
    have hR : ((2 * (36 : ℤ) + 23 * (kolS^[4] 2 : ℤ) + 23 * (2 ^ 4 : ℤ) : ℤ) : ℝ) ≤ (23 * 52 : ℝ) := by
      exact_mod_cast hZ
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < ((23 : ℤ) : ℝ))]
    norm_num at hR ⊢
    linarith
  have hnonasymp : ∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => kolSeq i = 1)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        (1 / 46 : ℝ) + (52 : ℝ) / (N : ℝ) := by
    intro N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 := hraw N hN
    have hdiv : (((23 - 2 * 11 : ℤ) : ℝ) / (2 * ((23 : ℤ) : ℝ))) = (1 / 46 : ℝ) := by norm_num
    rw [hdiv] at h1
    have hCdiv : (((2 * (36 : ℤ) + 23 * (kolS^[4] 2 : ℤ) + 23 * (2 ^ 4 : ℤ) : ℤ) : ℝ) / ((23 : ℤ) : ℝ)) / (N : ℝ) ≤
        (52 : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right hC_le (le_of_lt hN_pos)
    linarith
  refine ⟨hnonasymp, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (107640 : ℕ)] with N hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNR : (107640 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 := hnonasymp N (by omega)
  have h52 : (52 : ℝ) / (N : ℝ) ≤ (1 / 2070 : ℝ) := by
    rw [div_le_div_iff₀ hN_pos (by norm_num : (0 : ℝ) < 2070)]
    linarith
  linarith

/-! ## Section 4: `C^∞` Smooth Word Language & Dekking Symmetry Equivalences -/

section SmoothWords

/-- Private alias for the pure-Mathlib `C^∞` smooth-word predicate (Dekking 1979/1997).
Always unfolded in public theorem signatures (`0` custom/private defs exposed). -/
private def IsCInf (w : List ℕ) : Prop :=
  (∀ x ∈ w, x = 1 ∨ x = 2) ∧
  ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w ∧
    (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
    (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
      f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
        List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b)))

private lemma kolSeq_prefix_isInfix_expand (m : ℕ) :
    List.ofFn (fun i : Fin m => kolSeq i) <:+:
      expandFrom 1 (List.ofFn (fun i : Fin m => kolSeq i)) := by
  have hexp := ppl044_kolakoski_prefix_expansion kolSeq kolSeq_pos kolSeq_run_spec m
  rw [← expandFrom_eq_zipIdx 1 (Or.inl rfl)] at hexp
  rw [← hexp]
  have hle : m ≤ ∑ j ∈ Finset.range m, kolSeq j := sum_ge_self_of_pos kolSeq_pos m
  refine ⟨[], List.ofFn (fun i : Fin ((∑ j ∈ Finset.range m, kolSeq j) - m) => kolSeq (m + i)), ?_⟩
  simp only [List.nil_append]
  apply List.ext_getElem
  · simp [hle]
  · intro idx hi1 hi2
    simp only [List.length_ofFn] at hi2
    rw [List.getElem_ofFn]
    rcases lt_or_ge idx m with hlt | hge
    · rw [List.getElem_append_left (by simp; exact hlt)]; simp
    · rw [List.getElem_append_right (by simp; exact hge)]
      simp only [List.length_ofFn, List.getElem_ofFn]
      congr 1; omega

private lemma kolSeq_factor_isCInf (a m : ℕ) :
    IsCInf (List.ofFn (fun i : Fin m => kolSeq (a + i))) := by
  refine ⟨fun x hx => ?_, fun n => ?_⟩
  · rw [List.mem_ofFn] at hx; rcases hx with ⟨i, rfl⟩; exact kolSeq_mem _
  · let P := List.ofFn (fun i : Fin (a + m) => kolSeq i)
    have hwP : List.ofFn (fun i : Fin m => kolSeq (a + i)) <:+: P := by
      refine ⟨List.ofFn (fun i : Fin a => kolSeq i), [], ?_⟩
      simp only [List.append_nil]
      apply List.ext_getElem
      · simp [P]
      · intro idx hi1 hi2
        simp only [P, List.length_ofFn] at hi2
        rw [List.getElem_ofFn]
        rcases lt_or_ge idx a with hlt | hge
        · rw [List.getElem_append_left (by simp; exact hlt)]; simp
        · rw [List.getElem_append_right (by simp; exact hge)]
          simp only [List.length_ofFn, List.getElem_ofFn]; congr 1; omega
    have hPP : P <:+: expandFrom 1 P := kolSeq_prefix_isInfix_expand (a + m)
    refine ⟨fun k => if k = 0 then List.ofFn (fun i : Fin m => kolSeq (a + i)) else P,
      rfl, ?_, ?_⟩
    · intro k _ x hx
      dsimp only at hx
      split_ifs at hx
      · rw [List.mem_ofFn] at hx; rcases hx with ⟨i, rfl⟩; exact kolSeq_mem _
      · rw [List.mem_ofFn] at hx; rcases hx with ⟨i, rfl⟩; exact kolSeq_mem _
    · intro k _
      refine ⟨1, Or.inl rfl, ?_⟩
      rw [← expandFrom_eq_zipIdx 1 (Or.inl rfl)]
      cases k with
      | zero => simpa using hwP.trans hPP
      | succ k' => simpa using hPP

private lemma isCInf_infix {u w : List ℕ} (hu : u <:+: w) (hw : IsCInf w) : IsCInf u := by
  rcases hw with ⟨hw_mem, hw_lift⟩
  refine ⟨fun x hx => hw_mem x (hu.subset hx), fun n => ?_⟩
  obtain ⟨f, hf0, hf_mem, hf_step⟩ := hw_lift n
  refine ⟨fun k => if k = 0 then u else f k, rfl, ?_, ?_⟩
  · intro k hk x hx
    dsimp only at hx
    split_ifs at hx
    · exact hw_mem x (hu.subset hx)
    · exact hf_mem k hk x hx
  · intro k hk
    obtain ⟨b, hb, hstep⟩ := hf_step k hk
    refine ⟨b, hb, ?_⟩
    cases k with
    | zero =>
      simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      rw [hf0] at hstep
      exact hu.trans hstep
    | succ k' =>
      simpa using hstep

private lemma isCInf_swap {w : List ℕ} (hw : IsCInf w) : IsCInf (w.map (fun x => 3 - x)) := by
  rcases hw with ⟨hw_mem, hw_lift⟩
  refine ⟨fun x hx => ?_, fun n => ?_⟩
  · rw [List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact swap_mem (hw_mem y hy)
  · obtain ⟨f, hf0, hf_mem, hf_step⟩ := hw_lift n
    refine ⟨fun k => if k = 0 then w.map (fun x => 3 - x) else f k, rfl, ?_, ?_⟩
    · intro k hk x hx
      dsimp only at hx
      split_ifs at hx
      · rw [List.mem_map] at hx; rcases hx with ⟨y, hy, rfl⟩; exact swap_mem (hw_mem y hy)
      · exact hf_mem k hk x hx
    · intro k hk
      obtain ⟨b, hb, hstep⟩ := hf_step k hk
      cases k with
      | zero =>
        refine ⟨3 - b, swap_mem hb, ?_⟩
        simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
        rw [← expandFrom_eq_zipIdx (3 - b) (swap_mem hb), ← expandFrom_map_swap b hb]
        rw [hf0, ← expandFrom_eq_zipIdx b hb] at hstep
        rcases hstep with ⟨p, s, hps⟩
        refine ⟨p.map (fun x => 3 - x), s.map (fun x => 3 - x), ?_⟩
        rw [← List.map_append, ← List.map_append, hps]
      | succ k' =>
        exact ⟨b, hb, by simpa using hstep⟩

private lemma isCInf_reverse {w : List ℕ} (hw : IsCInf w) : IsCInf w.reverse := by
  rcases hw with ⟨hw_mem, hw_lift⟩
  refine ⟨fun x hx => hw_mem x (List.mem_reverse.mp hx), fun n => ?_⟩
  obtain ⟨f, hf0, hf_mem, hf_step⟩ := hw_lift n
  refine ⟨fun k => (f k).reverse, by dsimp only; rw [hf0], ?_, ?_⟩
  · intro k hk x hx
    exact hf_mem k hk x (List.mem_reverse.mp hx)
  · intro k hk
    obtain ⟨b, hb, hstep⟩ := hf_step k hk
    let b' := if (f (k + 1)).length % 2 = 0 then 3 - b else b
    have hb' : b' = 1 ∨ b' = 2 := by unfold b'; split_ifs; exact swap_mem hb; exact hb
    refine ⟨b', hb', ?_⟩
    rw [← expandFrom_eq_zipIdx b' hb']
    rw [← expandFrom_eq_zipIdx b hb] at hstep
    rw [← expandFrom_reverse b hb (f (k + 1))]
    rcases hstep with ⟨p, s, hps⟩
    refine ⟨s.reverse, p.reverse, ?_⟩
    rw [← List.reverse_append, ← List.reverse_append, ← List.append_assoc, hps]

private lemma expandFrom_no_triple (b : ℕ) (hb : b = 1 ∨ b = 2) (u : List ℕ)
    (hu : ∀ x ∈ u, x = 1 ∨ x = 2) :
    ∀ (a : ℕ), ¬ ([a, a, a] <:+: expandFrom b u) := by
  intro a htri
  -- No 3 equal consecutive elements exist in `expandFrom b u` when all run lengths are ≤ 2!
  have hno : ∀ (c : ℕ) (hc : c = 1 ∨ c = 2) (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2)
      (i : ℕ) (hi : i + 2 < (expandFrom c v).length),
      ¬ ((expandFrom c v)[i] = (expandFrom c v)[i + 1] ∧
         (expandFrom c v)[i + 1] = (expandFrom c v)[i + 2]) := by
    intro c hc v hv
    induction v generalizing c with
    | nil => intro i hi; simp [expandFrom] at hi
    | cons x xs ih =>
      have hx := hv x (List.mem_cons_self ..)
      have hxs : ∀ y ∈ xs, y = 1 ∨ y = 2 := fun y hy => hv y (List.mem_cons_of_mem x hy)
      intro i hi ⟨he1, he2⟩
      simp only [expandFrom] at hi he1 he2
      rcases hx with rfl | rfl
      · -- `x = 1`: `c :: expandFrom (3 - c) xs`
        cases i with
        | zero =>
          simp only [List.replicate_one, List.singleton_append, List.getElem_cons_zero,
            List.getElem_cons_succ] at he1
          -- `expandFrom (3 - c) xs` starts with `3 - c ≠ c` (if nonempty)
          cases xs with
          | nil => simp [expandFrom] at hi
          | cons y ys =>
            have hy := hxs y (List.mem_cons_self ..)
            have h0 : (expandFrom (3 - c) (y :: ys))[0]'(by
                simp only [expandFrom_length, List.sum_cons]; rcases hy with rfl | rfl <;> omega) =
                3 - c := by
              rcases hy with rfl | rfl <;> simp [expandFrom]
            have hne := swap_ne hc
            rw [h0] at he1; exact hne he1.symm
        | succ i' =>
          simp only [List.replicate_one, List.singleton_append, List.length_cons,
            List.getElem_cons_succ] at hi he1 he2
          exact ih (3 - c) (swap_mem hc) hxs i' (by omega) ⟨he1, he2⟩
      · -- `x = 2`: `c :: c :: expandFrom (3 - c) xs`
        cases i with
        | zero =>
          simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
            List.getElem_cons_zero, List.getElem_cons_succ] at he1 he2
          cases xs with
          | nil => simp [expandFrom] at hi
          | cons y ys =>
            have hy := hxs y (List.mem_cons_self ..)
            have h0 : (expandFrom (3 - c) (y :: ys))[0]'(by
                simp only [expandFrom_length, List.sum_cons]; rcases hy with rfl | rfl <;> omega) =
                3 - c := by
              rcases hy with rfl | rfl <;> simp [expandFrom]
            have hne := swap_ne hc
            rw [h0] at he2; exact hne he2.symm
        | succ i' =>
          cases i' with
          | zero =>
            simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
              List.getElem_cons_zero, List.getElem_cons_succ] at he1 he2
            cases xs with
            | nil => simp [expandFrom] at hi
            | cons y ys =>
              have hy := hxs y (List.mem_cons_self ..)
              have h0 : (expandFrom (3 - c) (y :: ys))[0]'(by
                  simp only [expandFrom_length, List.sum_cons]; rcases hy with rfl | rfl <;> omega) =
                  3 - c := by
                rcases hy with rfl | rfl <;> simp [expandFrom]
              have hne := swap_ne hc
              rw [h0] at he1; exact hne he1.symm
          | succ i'' =>
            simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
              List.length_cons, List.getElem_cons_succ] at hi he1 he2
            exact ih (3 - c) (swap_mem hc) hxs i'' (by omega) ⟨he1, he2⟩
  rcases htri with ⟨p, s, hps⟩
  have hi : p.length + 2 < (expandFrom b u).length := by
    rw [← hps]; simp
  refine hno b hb u hu p.length hi ⟨?_, ?_⟩
  · have h0 : (expandFrom b u)[p.length]'(by omega) = a := by
      have := congrArg (fun l => l[p.length]?) hps.symm
      rw [List.getElem?_eq_getElem (by omega)] at this
      simp at this; exact this
    have h1 : (expandFrom b u)[p.length + 1]'(by omega) = a := by
      have := congrArg (fun l => l[p.length + 1]?) hps.symm
      rw [List.getElem?_eq_getElem (by omega)] at this
      simp at this; exact this
    rw [h0, h1]
  · have h1 : (expandFrom b u)[p.length + 1]'(by omega) = a := by
      have := congrArg (fun l => l[p.length + 1]?) hps.symm
      rw [List.getElem?_eq_getElem (by omega)] at this
      simp at this; exact this
    have h2 : (expandFrom b u)[p.length + 2]'(by omega) = a := by
      have := congrArg (fun l => l[p.length + 2]?) hps.symm
      rw [List.getElem?_eq_getElem (by omega)] at this
      simp at this; exact this
    rw [h1, h2]

private lemma isCInf_no_triple {w : List ℕ} (hw : IsCInf w) (a : ℕ) : ¬ ([a, a, a] <:+: w) := by
  obtain ⟨f, hf0, hf_mem, hf_step⟩ := hw.2 1
  obtain ⟨b, hb, hstep⟩ := hf_step 0 (by omega)
  rw [hf0, ← expandFrom_eq_zipIdx b hb] at hstep
  intro htri
  exact expandFrom_no_triple b hb (f 1) (hf_mem 1 (by omega)) a (htri.trans hstep)

end SmoothWords

/-- **Theorem 4.1 (Every Factor of `K` is `C^∞`).**
Every finite factor of the classical Kolakoski sequence `K` belongs to Dekking's infinitely
differentiable (`C^∞`) smooth-word language. -/
theorem ppl044_kolakoski_factor_is_Cinf (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2)
    (a m : ℕ) :
    let w := List.ofFn (fun i : Fin m => K (a + i))
    (∀ x ∈ w, x = 1 ∨ x = 2) ∧
    ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w ∧
      (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
      (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
        f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
          List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b))) := by
  have hK := kol_unique hpos hspec; subst hK
  exact kolSeq_factor_isCInf a m

/-- **Theorem 4.2 (Closure of `C^∞` under `1 ↔ 2` Swap).**
If a finite word `w` is `C^∞`, then its symbol-swap `w.map (3 - ·)` is also `C^∞`. -/
theorem ppl044_Cinf_closed_under_swap (w : List ℕ)
    (hw : (∀ x ∈ w, x = 1 ∨ x = 2) ∧
      ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w ∧
        (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
        (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
          f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
            List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b)))) :
    (∀ x ∈ w.map (fun x => 3 - x), x = 1 ∨ x = 2) ∧
    ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w.map (fun x => 3 - x) ∧
      (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
      (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
        f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
          List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b))) :=
  isCInf_swap hw

/-- **Theorem 4.3 (Closure of `C^∞` under Reversal).**
If a finite word `w` is `C^∞`, then its mirror reversal `w.reverse` is also `C^∞`. -/
theorem ppl044_Cinf_closed_under_reverse (w : List ℕ)
    (hw : (∀ x ∈ w, x = 1 ∨ x = 2) ∧
      ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w ∧
        (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
        (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
          f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
            List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b)))) :
    (∀ x ∈ w.reverse, x = 1 ∨ x = 2) ∧
    ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w.reverse ∧
      (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
      (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
        f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
          List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b))) :=
  isCInf_reverse hw

/-- **Theorem 4.4 (`C^∞` Words Avoid `111` and `222`).**
No `C^∞` word contains three consecutive equal symbols. -/
theorem ppl044_Cinf_no_triple (w : List ℕ)
    (hw : (∀ x ∈ w, x = 1 ∨ x = 2) ∧
      ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w ∧
        (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
        (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
          f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
            List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b)))) :
    ∀ a : ℕ, ¬ ([a, a, a] <:+: w) :=
  isCInf_no_triple hw

/-- **Theorem 4.5 (Dekking's Implication: Kimberling Q3 ⇒ Kimberling Q2).**
For any infinite sequence `K : ℕ → ℕ`, if the factor language of `K` is closed under reversal
(Kimberling Q3), then every factor of `K` recurs at arbitrarily large positions (Kimberling Q2). -/
theorem ppl044_reversal_implies_recurrence (K : ℕ → ℕ)
    (hQ3 : ∀ (a m : ℕ), ∃ b : ℕ,
      (List.ofFn (fun i : Fin m => K (a + i))).reverse = List.ofFn (fun i : Fin m => K (b + i))) :
    ∀ (a m N : ℕ), ∃ b : ℕ, N ≤ b ∧
      List.ofFn (fun i : Fin m => K (a + i)) = List.ofFn (fun i : Fin m => K (b + i)) := by
  intro a m N
  obtain ⟨p, hp⟩ := hQ3 a m
  let M := p + m + N
  obtain ⟨q, hq⟩ := hQ3 0 M
  refine ⟨q + N, by omega, ?_⟩
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_ofFn] at hi1
    rw [List.getElem_ofFn, List.getElem_ofFn]
    have hq_get := congrArg (fun l => l[N + i]?) hq
    rw [List.getElem?_eq_getElem (by simp [M]; omega),
        List.getElem?_eq_getElem (by simp [M]; omega)] at hq_get
    have hq_eq : (List.ofFn (fun j : Fin M => K (0 + j))).reverse[N + i]'(by simp [M]; omega) =
        K (q + (N + i)) := by
      simpa using Option.some.inj hq_get
    rw [List.getElem_reverse] at hq_eq
    simp only [List.length_ofFn, List.getElem_ofFn, zero_add] at hq_eq
    have hp_get := congrArg (fun l => l[m - 1 - i]?) hp
    rw [List.getElem?_eq_getElem (by simp; omega),
        List.getElem?_eq_getElem (by simp; omega)] at hp_get
    have hp_eq : (List.ofFn (fun j : Fin m => K (a + j))).reverse[m - 1 - i]'(by simp; omega) =
        K (p + (m - 1 - i)) := by
      simpa using Option.some.inj hp_get
    rw [List.getElem_reverse] at hp_eq
    simp only [List.length_ofFn, List.getElem_ofFn] at hp_eq
    have hidx1 : m - 1 - (m - 1 - i) = i := by omega
    have hidx2 : M - 1 - (N + i) = p + (m - 1 - i) := by unfold M; omega
    have hidx3 : q + (N + i) = (q + N) + i := by omega
    rw [hidx1] at hp_eq
    rw [hidx2, hidx3] at hq_eq
    exact hp_eq.trans hq_eq

/-- **Theorem 4.6 (Dekking's Open `C^∞` Conjecture Implies Kimberling Q2, Q3, and Q4).**
If every `C^∞` word occurs as a factor of the classical Kolakoski sequence `K`, then:
- **Q2 (Recurrence):** every factor of `K` occurs at arbitrarily large positions `b ≥ N`,
- **Q3 (Reversal closure):** every factor's mirror reversal occurs in `K`,
- **Q4 (`1 ↔ 2` swap closure):** every factor's symbol-swap occurs in `K`. -/
theorem ppl044_dekking_conjecture_implies_Q2_Q3_Q4 (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2)
    (hDekking : ∀ w : List ℕ,
      ((∀ x ∈ w, x = 1 ∨ x = 2) ∧
        ∀ n : ℕ, ∃ f : ℕ → List ℕ, f 0 = w ∧
          (∀ k ≤ n, ∀ x ∈ f k, x = 1 ∨ x = 2) ∧
          (∀ k < n, ∃ b : ℕ, (b = 1 ∨ b = 2) ∧
            f k <:+: ((f (k + 1)).zipIdx.flatMap fun p =>
              List.replicate p.1 (if p.2 % 2 = 0 then b else 3 - b)))) →
      ∃ b : ℕ, w = List.ofFn (fun i : Fin w.length => K (b + i))) :
    (∀ a m N : ℕ, ∃ b : ℕ, N ≤ b ∧
      List.ofFn (fun i : Fin m => K (a + i)) = List.ofFn (fun i : Fin m => K (b + i))) ∧
    (∀ a m : ℕ, ∃ b : ℕ,
      (List.ofFn (fun i : Fin m => K (a + i))).reverse = List.ofFn (fun i : Fin m => K (b + i))) ∧
    (∀ a m : ℕ, ∃ b : ℕ,
      (List.ofFn (fun i : Fin m => K (a + i))).map (fun x => 3 - x) =
        List.ofFn (fun i : Fin m => K (b + i))) := by
  have hQ3 : ∀ a m : ℕ, ∃ b : ℕ,
      (List.ofFn (fun i : Fin m => K (a + i))).reverse =
        List.ofFn (fun i : Fin m => K (b + i)) := by
    intro a m
    have hC := ppl044_Cinf_closed_under_reverse _ (ppl044_kolakoski_factor_is_Cinf K hpos hspec a m)
    obtain ⟨b, hb⟩ := hDekking _ hC
    refine ⟨b, ?_⟩
    simpa [List.length_reverse, List.length_ofFn] using hb
  have hQ4 : ∀ a m : ℕ, ∃ b : ℕ,
      (List.ofFn (fun i : Fin m => K (a + i))).map (fun x => 3 - x) =
        List.ofFn (fun i : Fin m => K (b + i)) := by
    intro a m
    have hC := ppl044_Cinf_closed_under_swap _ (ppl044_kolakoski_factor_is_Cinf K hpos hspec a m)
    obtain ⟨b, hb⟩ := hDekking _ hC
    refine ⟨b, ?_⟩
    simpa [List.length_map, List.length_ofFn] using hb
  exact ⟨ppl044_reversal_implies_recurrence K hQ3, hQ3, hQ4⟩

/-! ## Section 5: Generalized `{2a, 2b}` & `{1, 3}` Kolakoski Sequences and the `{1, 2}` Parity Barrier -/

section GeneralizedKolakoski

private def expandAB (u v : ℕ) : Bool → List ℕ → List ℕ
  | _, [] => []
  | b, x :: xs => List.replicate x (if b then u else v) ++ expandAB u v (!b) xs

private lemma expandAB_length (u v : ℕ) :
    ∀ (b : Bool) (w : List ℕ), (expandAB u v b w).length = w.sum
  | _, [] => rfl
  | b, x :: xs => by simp [expandAB, expandAB_length u v (!b) xs]

private lemma expandAB_append (u v : ℕ) :
    ∀ (b : Bool) (w₁ w₂ : List ℕ),
      expandAB u v b (w₁ ++ w₂) =
        expandAB u v b w₁ ++ expandAB u v (if w₁.length % 2 = 0 then b else !b) w₂
  | b, [], w₂ => by simp [expandAB]
  | b, x :: xs, w₂ => by
    simp only [List.cons_append, expandAB, List.append_assoc, List.length_cons]
    congr 1
    rw [expandAB_append u v (!b) xs w₂]
    congr 1
    cases b <;> split_ifs <;> simp_all <;> omega

private lemma expandAB_prefix (u v : ℕ) (b : Bool) {w₁ w₂ : List ℕ} (h : w₁ <+: w₂) :
    expandAB u v b w₁ <+: expandAB u v b w₂ := by
  rcases h with ⟨t, rfl⟩
  rw [expandAB_append]
  exact ⟨_, rfl⟩

private lemma expandAB_mem (u v : ℕ) :
    ∀ (b : Bool) (w : List ℕ) (x : ℕ), x ∈ expandAB u v b w → x = u ∨ x = v
  | _, [], _, hx => by simp [expandAB] at hx
  | b, a :: xs, x, hx => by
    simp only [expandAB, List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · cases b <;> simp
    · exact expandAB_mem u v (!b) xs x hx

private lemma expandAB_getElem_run (u v : ℕ) (b : Bool) (w : List ℕ)
    (k : ℕ) (hk : k < w.length) (j : ℕ) (hj : j < w[k]) :
    ∃ hlt : (w.take k).sum + j < (expandAB u v b w).length,
      (expandAB u v b w)[(w.take k).sum + j]'hlt =
        if (if k % 2 = 0 then b else !b) then u else v := by
  have hsplit : w = w.take k ++ w[k] :: w.drop (k + 1) := by
    have h1 := (List.take_append_drop k w).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen_take : (w.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have hexp : expandAB u v b w =
      expandAB u v b (w.take k) ++
        (List.replicate w[k] (if (if k % 2 = 0 then b else !b) then u else v) ++
          expandAB u v (!(if k % 2 = 0 then b else !b)) (w.drop (k + 1))) := by
    conv_lhs => rw [hsplit]
    rw [expandAB_append, hlen_take]
    rfl
  have hlt_rep : j < (List.replicate w[k] (if (if k % 2 = 0 then b else !b) then u else v)).length := by
    simpa using hj
  have hlt : (w.take k).sum + j < (expandAB u v b w).length := by
    rw [hexp, List.length_append, expandAB_length, List.length_append]; omega
  refine ⟨hlt, ?_⟩
  have hget : (expandAB u v b w)[(w.take k).sum + j]'hlt =
      (expandAB u v b (w.take k) ++
        (List.replicate w[k] (if (if k % 2 = 0 then b else !b) then u else v) ++
          expandAB u v (!(if k % 2 = 0 then b else !b)) (w.drop (k + 1))))[(w.take k).sum + j]'(by
            rwa [← hexp]) := by
    simp [hexp]
  rw [hget]
  have hle : (expandAB u v b (w.take k)).length ≤ (w.take k).sum + j := by
    rw [expandAB_length]; omega
  rw [List.getElem_append_right hle]
  have hidx : (w.take k).sum + j - (expandAB u v b (w.take k)).length = j := by
    rw [expandAB_length]; omega
  simp only [hidx]
  rw [List.getElem_append_left hlt_rep]
  simp

private def genPrefix (u v : ℕ) : ℕ → List ℕ
  | 0 => if u = 1 then [1, v] else [u]
  | m + 1 => expandAB u v true (genPrefix u v m)

private lemma genPrefix_mem (u v : ℕ) :
    ∀ m x, x ∈ genPrefix u v m → x = u ∨ x = v
  | 0, x, hx => by
    unfold genPrefix at hx
    split_ifs at hx with h
    · subst h; simp at hx; exact hx
    · simp at hx; exact Or.inl hx
  | m + 1, x, hx => expandAB_mem u v true (genPrefix u v m) x hx

private lemma genPrefix_prefix_succ (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v) :
    ∀ m, genPrefix u v m <+: genPrefix u v (m + 1)
  | 0 => by
    have h0 : genPrefix u v 0 = if u = 1 then [1, v] else [u] := rfl
    have h1 : genPrefix u v 1 = expandAB u v true (genPrefix u v 0) := rfl
    rw [h1, h0]
    split_ifs with h
    · subst h
      have hv2 : 2 ≤ v := by omega
      have hrep : List.replicate v v = v :: List.replicate (v - 1) v := by
        cases v with
        | zero => omega
        | succ v' => rfl
      refine ⟨List.replicate (v - 1) v, ?_⟩
      simp [expandAB, hrep]
    · have hu2 : 2 ≤ u := by omega
      have hrep : List.replicate u u = u :: List.replicate (u - 1) u := by
        cases u with
        | zero => omega
        | succ u' => rfl
      refine ⟨List.replicate (u - 1) u, ?_⟩
      simp [expandAB, hrep]
  | m + 1 => expandAB_prefix u v true (genPrefix_prefix_succ u v hu hv huv m)

private lemma genPrefix_prefix_le (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v)
    {m n : ℕ} (h : m ≤ n) : genPrefix u v m <+: genPrefix u v n := by
  induction h with
  | refl => exact List.prefix_refl _
  | @step k _ ih => exact ih.trans (genPrefix_prefix_succ u v hu hv huv k)

private lemma genPrefix_length_ge (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v) :
    ∀ m, m + 1 ≤ (genPrefix u v m).length
  | 0 => by unfold genPrefix; split_ifs <;> simp
  | m + 1 => by
    have ih := genPrefix_length_ge u v hu hv huv m
    have hpre := genPrefix_prefix_le u v hu hv huv (Nat.zero_le m)
    rcases hpre with ⟨t, ht⟩
    have hpos : ∀ x ∈ t, 1 ≤ x := by
      intro x hx
      have hmem : x ∈ genPrefix u v m := by rw [← ht]; simp [hx]
      rcases genPrefix_mem u v m x hmem with rfl | rfl <;> omega
    have htsum := list_sum_ge_length t hpos
    have h0 : genPrefix u v 0 = if u = 1 then [1, v] else [u] := rfl
    rw [h0] at ht
    simp only [genPrefix, expandAB_length]
    split_ifs at ht with h
    · have hv2 : 2 ≤ v := by omega
      have hlen : (genPrefix u v m).length = 2 + t.length := by rw [← ht]; simp; omega
      have hsum : (genPrefix u v m).sum = 1 + v + t.sum := by rw [← ht]; simp; omega
      omega
    · have hu2 : 2 ≤ u := by omega
      have hlen : (genPrefix u v m).length = 1 + t.length := by rw [← ht]; simp; omega
      have hsum : (genPrefix u v m).sum = u + t.sum := by rw [← ht]; simp
      omega

private def genKolSeq (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v) (n : ℕ) : ℕ :=
  (genPrefix u v n)[n]'(by have := genPrefix_length_ge u v hu hv huv n; omega)

private lemma genPrefix_getElem {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v)
    {m n : ℕ} (hn : n < (genPrefix u v m).length) :
    (genPrefix u v m)[n]'hn = genKolSeq u v hu hv huv n := by
  unfold genKolSeq
  rcases le_total m n with hle | hle
  · exact List.IsPrefix.getElem (genPrefix_prefix_le u v hu hv huv hle) hn
  · exact (List.IsPrefix.getElem (genPrefix_prefix_le u v hu hv huv hle)
      (by have := genPrefix_length_ge u v hu hv huv n; omega)).symm

private lemma genKolSeq_mem {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v) (n : ℕ) :
    genKolSeq u v hu hv huv n = u ∨ genKolSeq u v hu hv huv n = v :=
  genPrefix_mem u v n _ (List.getElem_mem _)

private lemma genKolSeq_pos {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v) (n : ℕ) :
    1 ≤ genKolSeq u v hu hv huv n := by
  rcases genKolSeq_mem hu hv huv n with h | h <;> omega

private lemma genPrefix_take_sum {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v)
    (m k : ℕ) (hk : k ≤ (genPrefix u v m).length) :
    ((genPrefix u v m).take k).sum = ∑ i ∈ Finset.range k, genKolSeq u v hu hv huv i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : k < (genPrefix u v m).length := by omega
    rw [List.take_succ_eq_append_getElem hlt, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, ih (by omega), genPrefix_getElem hu hv huv hlt]

private lemma genKolSeq_run_spec {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v)
    (k j : ℕ) (hj : j < genKolSeq u v hu hv huv k) :
    genKolSeq u v hu hv huv ((∑ i ∈ Finset.range k, genKolSeq u v hu hv huv i) + j) =
      if k % 2 = 0 then u else v := by
  have hk : k < (genPrefix u v k).length := by
    have := genPrefix_length_ge u v hu hv huv k; omega
  have hj' : j < (genPrefix u v k)[k]'hk := by rwa [genPrefix_getElem hu hv huv hk]
  obtain ⟨hlt, hget⟩ := expandAB_getElem_run u v true (genPrefix u v k) k hk j hj'
  have hsum := genPrefix_take_sum hu hv huv k k (Nat.le_of_lt hk)
  have hlt' : (∑ i ∈ Finset.range k, genKolSeq u v hu hv huv i) + j <
      (genPrefix u v (k + 1)).length := by
    simpa [genPrefix, hsum] using hlt
  rw [← genPrefix_getElem hu hv huv hlt']
  have hget' : (genPrefix u v (k + 1))[(∑ i ∈ Finset.range k, genKolSeq u v hu hv huv i) + j]'hlt' =
      if (if k % 2 = 0 then true else !true) then u else v := by
    simpa [genPrefix, hsum] using hget
  rw [hget']
  by_cases hk0 : k % 2 = 0 <;> simp [hk0]

private lemma genKol_unique {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v)
    {K : ℕ → ℕ} (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then u else v) :
    K = genKolSeq u v hu hv huv := by
  have h0 : K 0 = u := by simpa using hspec 0 0 (hpos 0)
  have h0' : genKolSeq u v hu hv huv 0 = u := by
    simpa using genKolSeq_run_spec hu hv huv 0 0 (genKolSeq_pos hu hv huv 0)
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_lt_of_le hu with rfl | hu2
    · -- `u = 1`, so `v ≥ 2`, `K 0 = 1`, `K 1 = v ≥ 2`, `S(2) = 1 + v ≥ 3`
      have h1 : K 1 = v := by
        have := hspec 1 0 (hpos 1)
        simpa [Finset.sum_range_one, h0] using this
      have h1' : genKolSeq 1 v hu hv huv 1 = v := by
        have := genKolSeq_run_spec hu hv huv 1 0 (genKolSeq_pos hu hv huv 1)
        simpa [Finset.sum_range_one, h0'] using this
      rcases lt_or_ge n (1 + v) with hlt | hge
      · rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn0
        · rw [h0, h0']
        · have hj : n - 1 < K 1 := by omega
          have hj' : n - 1 < genKolSeq 1 v hu hv huv 1 := by omega
          have hL := hspec 1 (n - 1) hj
          have hR := genKolSeq_run_spec hu hv huv 1 (n - 1) hj'
          have hidx : 1 + (n - 1) = n := by omega
          simp only [Finset.sum_range_one, h0, h0', hidx] at hL hR
          rw [hL, hR]
      · obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos n
        have hS2 : ∑ i ∈ Finset.range 2, K i = 1 + v := by
          simp [Finset.sum_range_succ, h0, h1]
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have hle : ∑ i ∈ Finset.range (k + 1), K i ≤ ∑ i ∈ Finset.range 2, K i :=
            (sum_strict_mono_of_pos hpos).monotone (by omega)
          omega
        have hSk_gt : k + 1 ≤ ∑ i ∈ Finset.range k, K i := by
          have hv2 : 2 ≤ v := by omega
          clear ih hlo hhi hge
          induction k with
          | zero => omega
          | succ k ihk =>
            rcases eq_or_lt_of_le hk2 with heq2 | hgt
            · have hk1 : k = 1 := by omega
              subst hk1; simp [Finset.sum_range_succ, h0, h1]; omega
            · rw [Finset.sum_range_succ]
              have := ihk (by omega)
              have := hpos k
              omega
        have hk_lt : k < n := by omega
        have hsum_eq : ∑ i ∈ Finset.range k, K i =
            ∑ i ∈ Finset.range k, genKolSeq 1 v hu hv huv i :=
          Finset.sum_congr rfl (fun i hi => ih i (lt_trans (Finset.mem_range.mp hi) hk_lt))
        have hKk_eq : K k = genKolSeq 1 v hu hv huv k := ih k hk_lt
        have hj : n - ∑ i ∈ Finset.range k, K i < K k := by
          rw [Finset.sum_range_succ] at hhi; omega
        have hL := hspec k (n - ∑ i ∈ Finset.range k, K i) hj
        have hR := genKolSeq_run_spec hu hv huv k (n - ∑ i ∈ Finset.range k, K i) (by omega)
        rw [Nat.add_sub_of_le hlo] at hL
        rw [← hsum_eq, Nat.add_sub_of_le hlo] at hR
        rw [hL, hR]
    · -- `u ≥ 2`, so `S(1) = u ≥ 2`, and `S(k) ≥ k + 1` for all `k ≥ 1`
      rcases lt_or_ge n u with hlt | hge
      · have hL := hspec 0 n (by omega)
        have hR := genKolSeq_run_spec hu hv huv 0 n (by omega)
        simp only [Finset.sum_range_zero, zero_add] at hL hR
        rw [hL, hR]
      · obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos n
        have hS1 : ∑ i ∈ Finset.range 1, K i = u := by simp [h0]
        have hk1 : 1 ≤ k := by
          by_contra hlt
          have hk0 : k = 0 := by omega
          subst hk0; rw [Finset.sum_range_one, h0] at hhi; omega
        have hSk_gt : k + 1 ≤ ∑ i ∈ Finset.range k, K i := by
          clear ih hlo hhi hge
          induction k with
          | zero => omega
          | succ k ihk =>
            rcases eq_or_lt_of_le hk1 with heq1 | hgt
            · have hk0 : k = 0 := by omega
              subst hk0; simp [h0]; omega
            · rw [Finset.sum_range_succ]
              have := ihk (by omega)
              have := hpos k
              omega
        have hk_lt : k < n := by omega
        have hsum_eq : ∑ i ∈ Finset.range k, K i =
            ∑ i ∈ Finset.range k, genKolSeq u v hu hv huv i :=
          Finset.sum_congr rfl (fun i hi => ih i (lt_trans (Finset.mem_range.mp hi) hk_lt))
        have hKk_eq : K k = genKolSeq u v hu hv huv k := ih k hk_lt
        have hj : n - ∑ i ∈ Finset.range k, K i < K k := by
          rw [Finset.sum_range_succ] at hhi; omega
        have hL := hspec k (n - ∑ i ∈ Finset.range k, K i) hj
        have hR := genKolSeq_run_spec hu hv huv k (n - ∑ i ∈ Finset.range k, K i) (by omega)
        rw [Nat.add_sub_of_le hlo] at hL
        rw [← hsum_eq, Nat.add_sub_of_le hlo] at hR
        rw [hL, hR]

/-! ### Part 5A: Even-Alphabet `{2a, 2b}` Kolakoski Sequences Have Exact Frequency `1/2` -/

private lemma kolEven_even_sum {a b : ℕ} {K : ℕ → ℕ}
    (hmem : ∀ n, K n = 2 * a ∨ K n = 2 * b) (k : ℕ) :
    (∑ i ∈ Finset.range k, K i) % 2 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases hmem k with h | h <;> omega

private lemma kolEven_pair_eq {a b : ℕ} (_ha : 1 ≤ a) (_hb : 1 ≤ b) {K : ℕ → ℕ}
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 2 * a else 2 * b)
    (m : ℕ) :
    K (2 * m) = K (2 * m + 1) := by
  have hmem : ∀ n, K n = 2 * a ∨ K n = 2 * b := by
    intro n
    obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos n
    have hj : n - ∑ i ∈ Finset.range k, K i < K k := by
      rw [Finset.sum_range_succ] at hhi; omega
    have h := hspec k (n - ∑ i ∈ Finset.range k, K i) hj
    rw [Nat.add_sub_of_le hlo] at h
    rw [h]; split_ifs <;> simp
  obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos (2 * m)
  have hev0 := kolEven_even_sum hmem k
  have hev1 := kolEven_even_sum hmem (k + 1)
  have hlo1 : ∑ i ∈ Finset.range k, K i ≤ 2 * m + 1 := by omega
  have hhi1 : 2 * m + 1 < ∑ i ∈ Finset.range (k + 1), K i := by omega
  have hj0 : 2 * m - ∑ i ∈ Finset.range k, K i < K k := by
    rw [Finset.sum_range_succ] at hhi; omega
  have hj1 : (2 * m + 1) - ∑ i ∈ Finset.range k, K i < K k := by
    rw [Finset.sum_range_succ] at hhi1; omega
  have h0 := hspec k (2 * m - ∑ i ∈ Finset.range k, K i) hj0
  have h1 := hspec k ((2 * m + 1) - ∑ i ∈ Finset.range k, K i) hj1
  rw [Nat.add_sub_of_le hlo] at h0
  rw [Nat.add_sub_of_le hlo1] at h1
  rw [h0, h1]

private lemma kolEven_count_at_even_run {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b)
    {K : ℕ → ℕ} (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 2 * a else 2 * b)
    (m : ℕ) :
    2 * ((Finset.range (∑ i ∈ Finset.range (2 * m), K i)).filter (fun i => K i = 2 * a)).card =
      ∑ i ∈ Finset.range (2 * m), K i := by
  induction m with
  | zero => simp
  | succ m ih =>
    let S0 := ∑ i ∈ Finset.range (2 * m), K i
    let S1 := ∑ i ∈ Finset.range (2 * m + 1), K i
    let S2 := ∑ i ∈ Finset.range (2 * (m + 1)), K i
    have hpair : K (2 * m) = K (2 * m + 1) := kolEven_pair_eq ha hb hpos hspec m
    have hS1 : S1 = S0 + K (2 * m) := Finset.sum_range_succ _ _
    have hS2 : S2 = S1 + K (2 * m + 1) := by
      have : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      unfold S2; rw [this, Finset.sum_range_succ]
    have hsplit : Finset.range S2 = Finset.range S0 ∪ Finset.Ico S0 S1 ∪ Finset.Ico S1 S2 := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj1 : Disjoint (Finset.range S0) (Finset.Ico S0 S1) := by
      rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; omega
    have hdisj2 : Disjoint (Finset.range S0 ∪ Finset.Ico S0 S1) (Finset.Ico S1 S2) := by
      rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; omega
    have hcard1 : ((Finset.Ico S0 S1).filter (fun i => K i = 2 * a)).card = K (2 * m) := by
      have hall : (Finset.Ico S0 S1).filter (fun i => K i = 2 * a) = Finset.Ico S0 S1 := by
        rw [Finset.filter_eq_self]
        intro x hx
        rw [Finset.mem_Ico] at hx
        have h := hspec (2 * m) (x - S0) (by omega)
        have : S0 + (x - S0) = x := Nat.add_sub_of_le hx.1
        rw [this] at h
        simpa using h
      rw [hall, Nat.card_Ico]; omega
    have hcard2 : ((Finset.Ico S1 S2).filter (fun i => K i = 2 * a)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [Finset.mem_Ico] at hx
      have h := hspec (2 * m + 1) (x - S1) (by omega)
      have : S1 + (x - S1) = x := Nat.add_sub_of_le hx.1
      rw [this] at h
      have hne : (if (2 * m + 1) % 2 = 0 then 2 * a else 2 * b) = 2 * b := by
        split_ifs <;> omega
      rw [hne] at h
      omega
    have htot : ((Finset.range S2).filter (fun i => K i = 2 * a)).card =
        ((Finset.range S0).filter (fun i => K i = 2 * a)).card + K (2 * m) := by
      rw [hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj2),
        Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj1),
        hcard1, hcard2, add_zero]
    change 2 * ((Finset.range S2).filter (fun i => K i = 2 * a)).card = S2
    rw [htot]
    change 2 * ((Finset.range S0).filter (fun i => K i = 2 * a)).card = S0 at ih
    omega

/-! ### Part 5B: Odd-Alphabet `{1, 3}` Kolakoski Sequence & Exact Pisot Frequency `(3 - θ) / 2` -/

private def kol13Seq : ℕ → ℕ :=
  genKolSeq 1 3 (by decide) (by decide) (by decide)

private def sub13 : Fin 3 → List (Fin 3)
  | ⟨0, _⟩ => [⟨1, by decide⟩]
  | ⟨1, _⟩ => [⟨1, by decide⟩, ⟨2, by decide⟩]
  | ⟨2, _⟩ => [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

private def iter13 : ℕ → Fin 3 → List (Fin 3)
  | 0, s => [s]
  | n + 1, s => (iter13 n s).flatMap sub13

private def decode13Sym : Fin 3 → List ℕ
  | ⟨0, _⟩ => [1, 1]
  | ⟨1, _⟩ => [1, 3]
  | ⟨2, _⟩ => [3, 3]

private def decode13 (w : List (Fin 3)) : List ℕ :=
  w.flatMap decode13Sym

private lemma iter13_succ_eq_flatMap (n : ℕ) (s : Fin 3) :
    iter13 (n + 1) s = (sub13 s).flatMap (iter13 n) := by
  induction n with
  | zero => simp [iter13]
  | succ n ih =>
    simp only [iter13] at ih ⊢
    rw [ih, List.flatMap_assoc]

private lemma decode13_append (u v : List (Fin 3)) :
    decode13 (u ++ v) = decode13 u ++ decode13 v :=
  List.flatMap_append

private lemma decode13_length (w : List (Fin 3)) :
    (decode13 w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons s ws ih =>
    simp only [decode13, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have hs : (decode13Sym s).length = 2 := by fin_cases s <;> rfl
    omega

private lemma expandAB13_decode13 (w : List (Fin 3)) :
    expandAB 1 3 true (decode13 w) = decode13 (w.flatMap sub13) := by
  induction w with
  | nil => rfl
  | cons s ws ih =>
    simp only [decode13, List.flatMap_cons] at ih ⊢
    rw [expandAB_append]
    have hs_len : (decode13Sym s).length % 2 = 0 := by fin_cases s <;> rfl
    rw [hs_len, if_pos rfl, ih]
    fin_cases s <;> rfl

private lemma genPrefix13_eq_decode_iter (n : ℕ) :
    genPrefix 1 3 n = decode13 (iter13 n ⟨1, by decide⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [genPrefix, iter13, ih, expandAB13_decode13]

private def count1Sym : Fin 3 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

private def count1List (w : List (Fin 3)) : ℕ :=
  (w.map count1Sym).sum

private lemma count1List_append (u v : List (Fin 3)) :
    count1List (u ++ v) = count1List u + count1List v := by
  simp [count1List]

private lemma decode13_count1 (w : List (Fin 3)) :
    (decode13 w).count 1 = count1List w := by
  induction w with
  | nil => rfl
  | cons s ws ih =>
    simp only [decode13, List.flatMap_cons, List.count_append, count1List, List.map_cons,
      List.sum_cons] at ih ⊢
    have hs : (decode13Sym s).count 1 = count1Sym s := by fin_cases s <;> decide
    omega

private lemma exists_unique_pisot_root :
    ∃! θ : ℝ, 2 < θ ∧ θ ^ 3 = 2 * θ ^ 2 + 1 := by
  let f : ℝ → ℝ := fun x => x ^ 3 - 2 * x ^ 2 - 1
  have hcont : ContinuousOn f (Set.Icc (2 : ℝ) (5 / 2 : ℝ)) := by fun_prop
  have hf2 : f 2 = -1 := by unfold f; norm_num
  have hf52 : f (5 / 2) = 17 / 8 := by unfold f; norm_num
  have h0_mem : (0 : ℝ) ∈ Set.Icc (f 2) (f (5 / 2)) := by rw [hf2, hf52]; constructor <;> norm_num
  obtain ⟨θ, ⟨hθ_lo, hθ_hi⟩, hθ_eq⟩ := intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 5 / 2) hcont h0_mem
  have hθ_gt2 : 2 < θ := by
    rcases eq_or_lt_of_le hθ_lo with rfl | hlt
    · unfold f at hθ_eq; norm_num at hθ_eq
    · exact hlt
  have hθ_cub : θ ^ 3 = 2 * θ ^ 2 + 1 := by unfold f at hθ_eq; linarith
  refine ⟨θ, ⟨hθ_gt2, hθ_cub⟩, ?_⟩
  rintro x ⟨hx2, hxcub⟩
  by_contra hne
  have hdiff : (x - θ) * (x ^ 2 + x * θ + θ ^ 2 - 2 * (x + θ)) = 0 := by
    linear_combination hxcub - hθ_cub
  have hpos : 0 < x ^ 2 + x * θ + θ ^ 2 - 2 * (x + θ) := by nlinarith
  have hxθ : x - θ = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact h
    · linarith
  exact hne (sub_eq_zero.mp hxθ)

private lemma pisot_root_lt_five_halves {θ : ℝ} (h2 : 2 < θ) (hθ : θ ^ 3 = 2 * θ ^ 2 + 1) :
    θ < 5 / 2 := by
  by_contra hge
  push Not at hge
  have h1 : θ ^ 2 * (θ - 2) = 1 := by linarith
  have h2' : (25 / 4 : ℝ) * (1 / 2) ≤ θ ^ 2 * (θ - 2) := by nlinarith
  linarith

private lemma pisot_root_gt_eleven_fifths {θ : ℝ} (h2 : 2 < θ) (hθ : θ ^ 3 = 2 * θ ^ 2 + 1) :
    (11 / 5 : ℝ) < θ := by
  by_contra hle
  push Not at hle
  have h1 : θ ^ 2 * (θ - 2) = 1 := by linarith
  have h2' : θ ^ 2 * (θ - 2) ≤ (11 / 5 : ℝ) ^ 2 * (11 / 5 - 2) := by nlinarith
  norm_num at h2'
  linarith

private def disc13 (θ : ℝ) (w : List (Fin 3)) : ℝ :=
  (count1List w : ℝ) - (3 - θ) * (w.length : ℝ)

private lemma disc13_append (θ : ℝ) (u v : List (Fin 3)) :
    disc13 θ (u ++ v) = disc13 θ u + disc13 θ v := by
  unfold disc13
  rw [count1List_append, List.length_append]
  push_cast
  ring

private lemma disc13_iter_bound {θ : ℝ} (h2 : 2 < θ) (hθ : θ ^ 3 = 2 * θ ^ 2 + 1) :
    ∀ (n : ℕ) (s : Fin 3), |disc13 θ (iter13 n s)| ≤ 8 * ((3 / 4 : ℝ) ^ n) := by
  have hlt : θ < 5 / 2 := pisot_root_lt_five_halves h2 hθ
  let x : ℕ → ℝ := fun n => disc13 θ (iter13 n ⟨0, by decide⟩)
  let y : ℕ → ℝ := fun n => disc13 θ (iter13 n ⟨1, by decide⟩)
  let z : ℕ → ℝ := fun n => disc13 θ (iter13 n ⟨2, by decide⟩)
  have hx0 : x 0 = θ - 1 := by
    simp [x, disc13, iter13, count1List, count1Sym]; ring
  have hy0 : y 0 = θ - 2 := by
    simp [y, disc13, iter13, count1List, count1Sym]; ring
  have hz0 : z 0 = θ - 3 := by
    simp [z, disc13, iter13, count1List, count1Sym]
  have hx_step : ∀ n, x (n + 1) = y n := by
    intro n; simp [x, y, iter13_succ_eq_flatMap, sub13]
  have hy_step : ∀ n, y (n + 1) = y n + z n := by
    intro n
    simp only [y, z, iter13_succ_eq_flatMap, sub13, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact disc13_append θ _ _
  have hz_step : ∀ n, z (n + 1) = x n + y n + z n := by
    intro n
    simp only [x, y, z, iter13_succ_eq_flatMap, sub13, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [disc13_append, disc13_append]; ring
  -- Exact orthogonality to right Perron–Frobenius eigenvector: `x n + θ*(θ-1)*y n + θ*z n = 0`
  have horth : ∀ n, x n + θ * (θ - 1) * y n + θ * z n = 0 := by
    intro n
    induction n with
    | zero =>
      rw [hx0, hy0, hz0]
      linear_combination hθ
    | succ n ih =>
      rw [hx_step, hy_step, hz_step]
      linear_combination θ * ih - y n * hθ
  -- Exact quadratic Lyapunov contraction: `θ * Q(x(n+1), y(n+1)) = Q(x n, y n)`
  let Q : ℝ → ℝ → ℝ := fun a b => a ^ 2 + θ * b ^ 2 + θ * (θ - 2) * a * b
  have hQ_step : ∀ n, θ * Q (x (n + 1)) (y (n + 1)) = Q (x n) (y n) := by
    intro n
    have hyn1 : θ * y (n + 1) = - x n - θ * (θ - 2) * y n := by
      have h1 := horth n
      rw [hy_step]
      linear_combination h1
    have hxn1 : x (n + 1) = y n := hx_step n
    unfold Q
    rw [hxn1]
    have h_expand : θ * (y n ^ 2 + θ * y (n + 1) ^ 2 + θ * (θ - 2) * y n * y (n + 1)) =
        θ * y n ^ 2 + (θ * y (n + 1)) ^ 2 + θ * (θ - 2) * y n * (θ * y (n + 1)) := by ring
    rw [h_expand, hyn1]
    ring
  have hQ_pos : ∀ a b : ℝ, (1 / 4 : ℝ) * (a ^ 2 + b ^ 2) ≤ Q a b := by
    intro a b
    unfold Q
    have hb_lo : (0 : ℝ) < θ * (θ - 2) := by nlinarith
    have hb_hi : θ * (θ - 2) < 5 / 4 := by nlinarith
    have hsq : 0 ≤ (3 / 4 : ℝ) * (a + (2 / 3 : ℝ) * (θ * (θ - 2)) * b) ^ 2 := by positivity
    have hcoeff : 0 ≤ (θ - 1 / 4 - (1 / 3 : ℝ) * (θ * (θ - 2)) ^ 2) * b ^ 2 := by
      apply mul_nonneg _ (sq_nonneg b)
      nlinarith
    nlinarith
  have hQ0 : Q (x 0) (y 0) ≤ 4 := by
    unfold Q; rw [hx0, hy0]; nlinarith
  have hQ_decay : ∀ n, Q (x n) (y n) ≤ 4 / (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa using hQ0
    | succ n ih =>
      have hQ_nonneg : 0 ≤ Q (x (n + 1)) (y (n + 1)) := by
        have := hQ_pos (x (n + 1)) (y (n + 1))
        nlinarith [sq_nonneg (x (n + 1)), sq_nonneg (y (n + 1))]
      have h1 : 2 * Q (x (n + 1)) (y (n + 1)) ≤ θ * Q (x (n + 1)) (y (n + 1)) := by nlinarith
      rw [hQ_step] at h1
      have h2pow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
      rw [h2pow]
      have : Q (x (n + 1)) (y (n + 1)) ≤ (4 / (2 : ℝ) ^ n) / 2 := by linarith
      calc Q (x (n + 1)) (y (n + 1)) ≤ (4 / (2 : ℝ) ^ n) / 2 := this
        _ = 4 / (2 * (2 : ℝ) ^ n) := by ring
  have hxy_bound : ∀ n, |x n| ≤ 4 * (3 / 4 : ℝ) ^ n ∧ |y n| ≤ 4 * (3 / 4 : ℝ) ^ n := by
    intro n
    have hsq : x n ^ 2 + y n ^ 2 ≤ 16 / (2 : ℝ) ^ n := by
      have hqp := hQ_pos (x n) (y n)
      have hqd := hQ_decay n
      have h4 : 4 * (4 / (2 : ℝ) ^ n) = 16 / (2 : ℝ) ^ n := by ring
      linarith
    have hhalf : (1 / 2 : ℝ) ^ n ≤ ((3 / 4 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm n 2, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h16 : 16 / (2 : ℝ) ^ n ≤ (4 * (3 / 4 : ℝ) ^ n) ^ 2 := by
      have hpow : 16 / (2 : ℝ) ^ n = 16 * (1 / 2 : ℝ) ^ n := by
        rw [one_div, inv_pow, div_eq_mul_inv]
      rw [hpow]
      nlinarith
    have hnonneg : 0 ≤ 4 * (3 / 4 : ℝ) ^ n := by positivity
    constructor
    · rw [abs_le]
      have hx2 : x n ^ 2 ≤ (4 * (3 / 4 : ℝ) ^ n) ^ 2 := by nlinarith [sq_nonneg (y n)]
      exact abs_le.mp (sq_le_sq.mp hx2 |>.trans (le_of_eq (abs_of_nonneg hnonneg)))
    · rw [abs_le]
      have hy2 : y n ^ 2 ≤ (4 * (3 / 4 : ℝ) ^ n) ^ 2 := by nlinarith [sq_nonneg (x n)]
      exact abs_le.mp (sq_le_sq.mp hy2 |>.trans (le_of_eq (abs_of_nonneg hnonneg)))
  intro n s
  fin_cases s
  · have := (hxy_bound n).1
    have hnonneg : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
    change |x n| ≤ 8 * (3 / 4 : ℝ) ^ n
    linarith
  · have := (hxy_bound n).2
    have hnonneg : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
    change |y n| ≤ 8 * (3 / 4 : ℝ) ^ n
    linarith
  · change |z n| ≤ 8 * (3 / 4 : ℝ) ^ n
    have hzn : z n = y (n + 1) - y n := by linarith [hy_step n]
    rw [hzn]
    have h1 := (hxy_bound (n + 1)).2
    have h2 := (hxy_bound n).2
    have h3 : (3 / 4 : ℝ) ^ (n + 1) ≤ (3 / 4 : ℝ) ^ n := by
      rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) n]
    have htri : |y (n + 1) - y n| ≤ |y (n + 1)| + |y n| := abs_sub _ _
    linarith

private lemma disc13_take_bound {θ : ℝ} (h2 : 2 < θ) (hθ : θ ^ 3 = 2 * θ ^ 2 + 1) :
    ∀ (n : ℕ) (s : Fin 3) (m : ℕ),
      |disc13 θ ((iter13 n s).take m)| ≤ ∑ k ∈ Finset.range (n + 1), 24 * (3 / 4 : ℝ) ^ k := by
  intro n
  induction n with
  | zero =>
    intro s m
    simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one]
    cases m with
    | zero =>
      simp only [disc13, List.take_zero, List.length_nil, count1List, List.map_nil, List.sum_nil]
      norm_num
    | succ m' =>
      have htake : (iter13 0 s).take (m' + 1) = iter13 0 s := by simp [iter13]
      rw [htake]
      have hb := disc13_iter_bound h2 hθ 0 s
      simp only [pow_zero, mul_one] at hb
      linarith
  | succ n ih =>
    intro s m
    rw [Finset.sum_range_succ, iter13_succ_eq_flatMap]
    have hstep1 : ∀ (u v : List (Fin 3)) (m : ℕ),
        |disc13 θ ((u ++ v).take m)| ≤
          max |disc13 θ (u.take m)| (|disc13 θ u| + |disc13 θ (v.take (m - u.length))|) := by
      intro u v m
      rw [List.take_append]
      rcases le_or_gt m u.length with hle | hgt
      · have h0 : m - u.length = 0 := by omega
        rw [h0, List.take_zero, List.append_nil]
        exact le_max_left _ _
      · rw [List.take_of_length_le (Nat.le_of_lt hgt), disc13_append]
        exact (abs_add_le _ _).trans (le_max_right _ _)
    have hnonneg : (0 : ℝ) ≤ 24 * (3 / 4 : ℝ) ^ (n + 1) := by positivity
    have h8_le : 8 * (3 / 4 : ℝ) ^ n ≤ 24 * (3 / 4 : ℝ) ^ (n + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) n]
    have h16_le : 16 * (3 / 4 : ℝ) ^ n ≤ 24 * (3 / 4 : ℝ) ^ (n + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) n]
    fin_cases s
    · simp only [sub13, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      linarith [ih ⟨1, by decide⟩ m]
    · simp only [sub13, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hm := hstep1 (iter13 n ⟨1, by decide⟩) (iter13 n ⟨2, by decide⟩) m
      have ha := ih ⟨1, by decide⟩ m
      have hb := disc13_iter_bound h2 hθ n ⟨1, by decide⟩
      have hc := ih ⟨2, by decide⟩ (m - (iter13 n ⟨1, by decide⟩).length)
      rcases le_total |disc13 θ ((iter13 n ⟨1, by decide⟩).take m)|
        (|disc13 θ (iter13 n ⟨1, by decide⟩)| +
         |disc13 θ ((iter13 n ⟨2, by decide⟩).take (m - (iter13 n ⟨1, by decide⟩).length))|) with h | h
      · rw [max_eq_right h] at hm; linarith
      · rw [max_eq_left h] at hm; linarith
    · simp only [sub13, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      let u0 := iter13 n ⟨0, by decide⟩
      let u1 := iter13 n ⟨1, by decide⟩
      let u2 := iter13 n ⟨2, by decide⟩
      have h1 := hstep1 u0 (u1 ++ u2) m
      have ha0 := ih ⟨0, by decide⟩ m
      have hb0 := disc13_iter_bound h2 hθ n ⟨0, by decide⟩
      have h2' := hstep1 u1 u2 (m - u0.length)
      have ha1 := ih ⟨1, by decide⟩ (m - u0.length)
      have hb1 := disc13_iter_bound h2 hθ n ⟨1, by decide⟩
      have ha2 := ih ⟨2, by decide⟩ (m - u0.length - u1.length)
      have hinner : |disc13 θ ((u1 ++ u2).take (m - u0.length))| ≤
          8 * (3 / 4 : ℝ) ^ n + ∑ k ∈ Finset.range (n + 1), 24 * (3 / 4 : ℝ) ^ k := by
        rcases le_total |disc13 θ (u1.take (m - u0.length))|
          (|disc13 θ u1| + |disc13 θ (u2.take (m - u0.length - u1.length))|) with h | h
        · rw [max_eq_right h] at h2'; linarith
        · rw [max_eq_left h] at h2'
          have hpos8 : (0 : ℝ) ≤ 8 * (3 / 4 : ℝ) ^ n := by positivity
          linarith
      rcases le_total |disc13 θ (u0.take m)|
        (|disc13 θ u0| + |disc13 θ ((u1 ++ u2).take (m - u0.length))|) with h | h
      · rw [max_eq_right h] at h1; linarith
      · rw [max_eq_left h] at h1; linarith

private lemma geom_sum_three_fourths_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (24 : ℝ) * (3 / 4 : ℝ) ^ k ≤ 96 := by
  have htel : ∀ m, ∑ k ∈ Finset.range m, (24 : ℝ) * (3 / 4 : ℝ) ^ k =
      96 * (1 - (3 / 4 : ℝ) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [htel]
  have hnonneg : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
  linarith

private lemma kol13Seq_count_eq_list_count (N : ℕ) :
    ((Finset.range N).filter (fun i => kol13Seq i = 1)).card =
      ((genPrefix 1 3 N).take N).count 1 := by
  have hlen : N ≤ (genPrefix 1 3 N).length := by
    have := genPrefix_length_ge 1 3 (by decide) (by decide) (by decide) N; omega
  have htake_eq : (genPrefix 1 3 N).take N = List.ofFn (fun i : Fin N => kol13Seq i) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi1 hi2
      simp only [List.length_ofFn] at hi2
      rw [List.getElem_take, List.getElem_ofFn]
      exact genPrefix_getElem (by decide) (by decide) (by decide) (by omega)
  rw [htake_eq]
  clear hlen htake_eq
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append, List.count_singleton,
      Finset.range_add_one, Finset.filter_insert]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases h1 : kol13Seq N = 1
    · simp [h1, Finset.card_insert_of_notMem, ih]
    · simp [h1, ih]

private lemma kol13Seq_discrepancy_bounded {θ : ℝ} (h2 : 2 < θ) (hθ : θ ^ 3 = 2 * θ ^ 2 + 1) :
    ∀ N : ℕ,
      |(((Finset.range N).filter (fun i => kol13Seq i = 1)).card : ℝ) -
        ((3 - θ) / 2) * (N : ℝ)| ≤ 98 := by
  have hlt : θ < 5 / 2 := pisot_root_lt_five_halves h2 hθ
  intro N
  let M := N / 2
  have hlen : N ≤ (genPrefix 1 3 N).length := by
    have := genPrefix_length_ge 1 3 (by decide) (by decide) (by decide) N; omega
  have hdec : genPrefix 1 3 N = decode13 (iter13 N ⟨1, by decide⟩) := genPrefix13_eq_decode_iter N
  have htake_even : (genPrefix 1 3 N).take (2 * M) =
      decode13 ((iter13 N ⟨1, by decide⟩).take M) := by
    rw [hdec]
    have htake_dec : ∀ (w : List (Fin 3)) (k : ℕ),
        (decode13 w).take (2 * k) = decode13 (w.take k) := by
      intro w k
      induction w generalizing k with
      | nil => simp [decode13]
      | cons s ws ih =>
        cases k with
        | zero => simp [decode13]
        | succ k' =>
          have hs : (decode13Sym s).length = 2 := by fin_cases s <;> rfl
          simp only [decode13, List.flatMap_cons, List.take_succ_cons]
          have h2k : 2 * (k' + 1) = (decode13Sym s).length + 2 * k' := by omega
          rw [h2k, List.take_append, List.take_of_length_le (by omega),
            Nat.add_sub_cancel_left]
          congr 1
          exact ih k'
    exact htake_dec _ M
  have hM_le : M ≤ (iter13 N ⟨1, by decide⟩).length := by
    have hlen' : (genPrefix 1 3 N).length = 2 * (iter13 N ⟨1, by decide⟩).length := by
      rw [hdec, decode13_length]
    omega
  have htake_len : ((iter13 N ⟨1, by decide⟩).take M).length = M :=
    List.length_take_of_le hM_le
  have hdisc_even : |(((genPrefix 1 3 N).take (2 * M)).count 1 : ℝ) -
      ((3 - θ) / 2) * (2 * M : ℝ)| ≤ 96 := by
    rw [htake_even, decode13_count1]
    have h96 : |disc13 θ ((iter13 N ⟨1, by decide⟩).take M)| ≤ 96 :=
      (disc13_take_bound h2 hθ N ⟨1, by decide⟩ M).trans (geom_sum_three_fourths_le (N + 1))
    have heq : disc13 θ ((iter13 N ⟨1, by decide⟩).take M) =
        (count1List ((iter13 N ⟨1, by decide⟩).take M) : ℝ) - ((3 - θ) / 2) * (2 * M : ℝ) := by
      unfold disc13
      rw [htake_len]
      ring
    rwa [heq] at h96
  rw [kol13Seq_count_eq_list_count]
  rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h2M : 2 * M = N := by unfold M; omega
    rw [h2M] at hdisc_even
    have : (2 * M : ℝ) = (N : ℝ) := by exact_mod_cast h2M
    rw [this] at hdisc_even
    linarith
  · have h2M : 2 * M + 1 = N := by unfold M; omega
    have htake_split : (genPrefix 1 3 N).take N =
        (genPrefix 1 3 N).take (2 * M) ++ [(genPrefix 1 3 N)[2 * M]'(by omega)] := by
      have h := List.take_succ_eq_append_getElem (l := genPrefix 1 3 N) (i := 2 * M) (by omega)
      rw [h2M] at h
      exact h
    rw [htake_split, List.count_append]
    have hlast_le1 : [(genPrefix 1 3 N)[2 * M]'(by omega)].count 1 ≤ 1 := by
      rw [List.count_singleton]; split_ifs <;> omega
    have hN_cast : (N : ℝ) = (2 * M : ℝ) + 1 := by exact_mod_cast h2M.symm
    rw [hN_cast]
    push_cast
    have hlast_real : (0 : ℝ) ≤ ([(genPrefix 1 3 N)[2 * M]'(by omega)].count 1 : ℝ) ∧
        ([(genPrefix 1 3 N)[2 * M]'(by omega)].count 1 : ℝ) ≤ 1 := by
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast hlast_le1⟩
    rw [abs_le] at hdisc_even ⊢
    constructor <;> linarith

end GeneralizedKolakoski

/-- **Theorem 5.1 (Existence & Uniqueness of Even-Alphabet `{2a, 2b}` Kolakoski Sequences).**
For any distinct positive integers `a ≠ b`, there is a unique self-describing sequence over
`{2a, 2b}` (including the classical even-alphabet `{2, 4}` Kolakoski sequence). -/
theorem ppl044_kolakoski_even_exists_unique (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) :
    ∃! K : ℕ → ℕ,
      (∀ n, 1 ≤ K n) ∧
      (∀ k j, j < K k →
        K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 2 * a else 2 * b) := by
  have h2a : 1 ≤ 2 * a := by omega
  have h2b : 1 ≤ 2 * b := by omega
  have hne : 2 * a ≠ 2 * b := by omega
  refine ⟨genKolSeq (2 * a) (2 * b) h2a h2b hne,
    ⟨genKolSeq_pos h2a h2b hne, genKolSeq_run_spec h2a h2b hne⟩, ?_⟩
  rintro K ⟨hpos, hspec⟩
  exact genKol_unique h2a h2b hne hpos hspec

/-- **Theorem 5.2 (Even-Alphabet `{2a, 2b}` Kolakoski Sequences Have Exact Frequency `1/2`).**
Because every run of `K_{2a, 2b}` has even length, consecutive pairs `(2k, 2k+1)` satisfy
`K(2k) = K(2k+1)`, yielding exact `O(1/N)` balance and limiting frequency identically `1/2`
(including `{2, 4}` as `a = 1, b = 2`). -/
theorem ppl044_kolakoski_even_freq_half (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b)
    (K : ℕ → ℕ) (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 2 * a else 2 * b) :
    (∀ m, K (2 * m) = K (2 * m + 1)) ∧
    (∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        (2 * max a b : ℝ) / (N : ℝ)) ∧
    Filter.Tendsto
      (fun N : ℕ => (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hmem : ∀ n, K n = 2 * a ∨ K n = 2 * b := by
    intro n
    obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos n
    have hj : n - ∑ i ∈ Finset.range k, K i < K k := by
      rw [Finset.sum_range_succ] at hhi; omega
    have h := hspec k (n - ∑ i ∈ Finset.range k, K i) hj
    rw [Nat.add_sub_of_le hlo] at h
    rw [h]; split_ifs <;> simp
  have hpair : ∀ m, K (2 * m) = K (2 * m + 1) := kolEven_pair_eq ha hb hpos hspec
  have hbound : ∀ N : ℕ, 1 ≤ N →
      |(((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) / (N : ℝ) - 1 / 2| ≤
        (2 * max a b : ℝ) / (N : ℝ) := by
    intro N hN
    obtain ⟨k, hlo, hhi⟩ := exists_run_index hpos N
    let m := k / 2
    let S0 := ∑ i ∈ Finset.range (2 * m), K i
    let S2 := ∑ i ∈ Finset.range (2 * (m + 1)), K i
    have hS0_le : S0 ≤ N := by
      have hle : S0 ≤ ∑ i ∈ Finset.range k, K i :=
        (sum_strict_mono_of_pos hpos).monotone (by omega)
      omega
    have hN_lt : N < S2 := by
      have hle : ∑ i ∈ Finset.range (k + 1), K i ≤ S2 :=
        (sum_strict_mono_of_pos hpos).monotone (by omega)
      omega
    have hgap : S2 - S0 ≤ 4 * max a b := by
      have h1 : S2 = S0 + K (2 * m) + K (2 * m + 1) := by
        have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        unfold S2 S0
        rw [h2, Finset.sum_range_succ, Finset.sum_range_succ]
      have hm1 : K (2 * m) ≤ 2 * max a b := by
        rcases hmem (2 * m) with h | h <;> omega
      have hm2 : K (2 * m + 1) ≤ 2 * max a b := by
        rcases hmem (2 * m + 1) with h | h <;> omega
      omega
    have hbal := kolEven_count_at_even_run ha hb hab hpos hspec m
    have hcnt_lo : ((Finset.range S0).filter (fun i => K i = 2 * a)).card ≤
        ((Finset.range N).filter (fun i => K i = 2 * a)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hS0_le))
    have hcnt_hi : ((Finset.range N).filter (fun i => K i = 2 * a)).card ≤
        ((Finset.range S0).filter (fun i => K i = 2 * a)).card + (N - S0) := by
      have hsub : (Finset.range N).filter (fun i => K i = 2 * a) ⊆
          (Finset.range S0).filter (fun i => K i = 2 * a) ∪ Finset.Ico S0 N := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hx ⊢
        by_cases hxS : x < S0
        · exact Or.inl ⟨hxS, hx.2⟩
        · exact Or.inr ⟨by omega, hx.1⟩
      calc ((Finset.range N).filter (fun i => K i = 2 * a)).card
          ≤ ((Finset.range S0).filter (fun i => K i = 2 * a) ∪ Finset.Ico S0 N).card :=
            Finset.card_le_card hsub
        _ ≤ ((Finset.range S0).filter (fun i => K i = 2 * a)).card + (Finset.Ico S0 N).card :=
            Finset.card_union_le _ _
        _ = ((Finset.range S0).filter (fun i => K i = 2 * a)).card + (N - S0) := by
            rw [Nat.card_Ico]
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h2diff : |2 * (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) - (N : ℝ)| ≤
        (4 * max a b : ℝ) := by
      have hbalR : 2 * (((Finset.range S0).filter (fun i => K i = 2 * a)).card : ℝ) = (S0 : ℝ) := by
        exact_mod_cast hbal
      have hloR : (((Finset.range S0).filter (fun i => K i = 2 * a)).card : ℝ) ≤
          (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) := by
        exact_mod_cast hcnt_lo
      have hhiR : (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) ≤
          (((Finset.range S0).filter (fun i => K i = 2 * a)).card : ℝ) + ((N : ℝ) - (S0 : ℝ)) := by
        have h1 : (N - S0 : ℕ) + S0 = N := Nat.sub_add_cancel hS0_le
        have h2 : ((N - S0 : ℕ) : ℝ) = (N : ℝ) - (S0 : ℝ) := by
          have : ((N - S0 : ℕ) : ℝ) + (S0 : ℝ) = (N : ℝ) := by exact_mod_cast h1
          linarith
        have h3 : (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) ≤
            (((Finset.range S0).filter (fun i => K i = 2 * a)).card : ℝ) + ((N - S0 : ℕ) : ℝ) := by
          exact_mod_cast hcnt_hi
        linarith
      have hgapR : (N : ℝ) - (S0 : ℝ) ≤ (4 * max a b : ℝ) := by
        have h1 : N - S0 ≤ 4 * max a b := by omega
        have h2 : ((N - S0 : ℕ) : ℝ) ≤ (4 * max a b : ℝ) := by exact_mod_cast h1
        have h3 : ((N - S0 : ℕ) : ℝ) + (S0 : ℝ) = (N : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel hS0_le
        linarith
      rw [abs_le]
      constructor <;> linarith
    have heq : (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) / (N : ℝ) - 1 / 2 =
        (2 * (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) - (N : ℝ)) / (2 * (N : ℝ)) := by
      field_simp
    rw [heq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * (N : ℝ))]
    calc |2 * (((Finset.range N).filter (fun i => K i = 2 * a)).card : ℝ) - (N : ℝ)| / (2 * (N : ℝ))
        ≤ (4 * max a b : ℝ) / (2 * (N : ℝ)) :=
          div_le_div_of_nonneg_right h2diff (by linarith)
      _ = (2 * max a b : ℝ) / (N : ℝ) := by ring
  refine ⟨hpair, hbound, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (a := fun N : ℕ => (2 * max a b : ℝ) / (N : ℝ)) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    simpa [Real.norm_eq_abs] using hbound N hN
  · simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * max a b : ℝ)

/-- **Theorem 5.3 (Existence & Uniqueness of the Odd-Alphabet `{1, 3}` Kolakoski Sequence).**
There exists a unique self-describing sequence `K_{1,3} : ℕ → ℕ` over `{1, 3}` starting with `1`
(`1, 3, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3, ...`). -/
theorem ppl044_kolakoski13_exists_unique :
    ∃! K : ℕ → ℕ,
      (∀ n, 1 ≤ K n) ∧
      (∀ k j, j < K k →
        K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 3) := by
  refine ⟨kol13Seq, ⟨genKolSeq_pos _ _ _, genKolSeq_run_spec _ _ _⟩, ?_⟩
  rintro K ⟨hpos, hspec⟩
  exact genKol_unique (by decide) (by decide) (by decide) hpos hspec

/-- **Theorem 5.4 (Odd-Alphabet `{1, 3}` Parity Preservation & Exact Pisot Limiting Frequency).**
For the unique `{1, 3}` Kolakoski sequence `K_{1,3}`:
1. **Even 2-block parity preservation:** `∑_{i < 2k} K_{1,3}(i)` is ALWAYS even (`% 2 = 0`),
   enabling its exact 3-letter primitive Pisot substitution `A → B, B → BD, D → ABD`.
2. **Exact algebraic limiting frequency:** Letting `θ > 2` be the unique real Pisot root of
   `θ^3 = 2 θ^2 + 1` (`θ ≈ 2.20557`), the `1`-discrepancy is **uniformly bounded**
   (`|#{i < N | K_{1,3}(i) = 1} - ((3 - θ) / 2) N| ≤ 98` for all `N`), hence the limiting
   frequency of `1`s **exists** and equals `(3 - θ) / 2 < 2 / 5 < 1 / 2` (refuting the folklore
   `1/2` guess for `{1, 3}` while showing how same-parity alphabets yield pure morphic limits!). -/
theorem ppl044_kolakoski13_exact_limiting_freq (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 3) :
    (∀ k, (∑ i ∈ Finset.range (2 * k), K i) % 2 = 0) ∧
    ∃ θ : ℝ, 2 < θ ∧ θ ^ 3 = 2 * θ ^ 2 + 1 ∧ (3 - θ) / 2 < 2 / 5 ∧
      (∀ N : ℕ,
        |(((Finset.range N).filter (fun i => K i = 1)).card : ℝ) - ((3 - θ) / 2) * (N : ℝ)| ≤ 98) ∧
      Filter.Tendsto
        (fun N : ℕ => (((Finset.range N).filter (fun i => K i = 1)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds ((3 - θ) / 2)) := by
  have hEq : K = kol13Seq := genKol_unique (by decide) (by decide) (by decide) hpos hspec
  subst hEq
  constructor
  · intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h2k : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h2k, Finset.sum_range_succ, Finset.sum_range_succ]
      rcases genKolSeq_mem (u := 1) (v := 3) (by decide) (by decide) (by decide) (2 * k) with h1 | h1 <;>
      rcases genKolSeq_mem (u := 1) (v := 3) (by decide) (by decide) (by decide) (2 * k + 1) with h2 | h2 <;>
      change _ % 2 = 0 <;> unfold kol13Seq at * <;> omega
  · obtain ⟨θ, ⟨h2, hθ⟩, _⟩ := exists_unique_pisot_root
    have hgt115 : (11 / 5 : ℝ) < θ := pisot_root_gt_eleven_fifths h2 hθ
    have hdisc := kol13Seq_discrepancy_bounded h2 hθ
    refine ⟨θ, h2, hθ, by linarith, hdisc, ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' (a := fun N : ℕ => (98 : ℝ) / (N : ℝ)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hdiv : (((Finset.range N).filter (fun i => kol13Seq i = 1)).card : ℝ) / (N : ℝ) -
          (3 - θ) / 2 =
          ((((Finset.range N).filter (fun i => kol13Seq i = 1)).card : ℝ) -
            ((3 - θ) / 2) * (N : ℝ)) / (N : ℝ) := by
        field_simp
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, hdiv, abs_div, abs_of_pos hN_pos]
      exact div_le_div_of_nonneg_right (hdisc N) (le_of_lt hN_pos)
    · simpa using tendsto_const_div_atTop_nhds_zero_nat (98 : ℝ)

/-- **Theorem 5.5 (The Non-Parity-Preserving Barrier of Classical `{1, 2}` Kolakoski `K`).**
Unlike `{2a, 2b}` (every run length even) and `{1, 3}` (every 2-run sum `S(2k)` even), the
classical `{1, 2}` Kolakoski sequence `K` violates both parity invariants:
`K 0 = 1` is odd, `∑_{i < 2} K(i) = 3` is odd, and `∑_{i < 4} K(i) = 6` is even — obstructing
any fixed-modulus block-substitution reduction. -/
theorem ppl044_kolakoski12_parity_barrier (K : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ K n)
    (hspec : ∀ k j, j < K k →
      K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2) :
    K 0 % 2 = 1 ∧
    (∑ i ∈ Finset.range 2, K i) % 2 = 1 ∧
    (∑ i ∈ Finset.range 4, K i) % 2 = 0 := by
  have hK := kol_unique hpos hspec; subst hK
  have h30 := kolSeq_first30
  have hget : ∀ m (hm : m < 30), kolSeq m =
      ([1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2])[m] := by
    intro m hm
    have h1 := congrArg (fun l => l[m]?) h30
    rw [List.getElem?_eq_getElem (by simp; exact hm), List.getElem_ofFn,
        List.getElem?_eq_getElem (by simp; exact hm)] at h1
    exact Option.some.inj h1
  have h0 : kolSeq 0 = 1 := hget 0 (by decide)
  have h1 : kolSeq 1 = 2 := hget 1 (by decide)
  have h2 : kolSeq 2 = 2 := hget 2 (by decide)
  have h3 : kolSeq 3 = 1 := hget 3 (by decide)
  simp [Finset.sum_range_succ, h0, h1, h2, h3]

end PPL044
