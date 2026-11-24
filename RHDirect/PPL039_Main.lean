/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# PPL 039 (Erdős Problem #564): 3-Uniform Hypergraph Ramsey Bounds, Stepping-Up Lemmas & Barrier

## Scope & Honest Labeling
**Erdős Problem #564 (PPL 039, $500, VERIFIED OPEN since 1965)** asks whether there exists a
constant `c > 0` such that the 2-color 3-uniform diagonal hypergraph Ramsey number satisfies
`R_3(n) ≥ 2 ^ (2 ^ (c * n))`.

This file does **NOT** solve the open `$500` conjecture `R_3(n) ≥ 2 ^ (2 ^ (c * n))`. Instead, it
provides a complete, self-contained, zero-`sorry`, pure-Mathlib Lean 4 formalization of the
entire theoretical landscape surrounding Erdős #564 (0 custom or `private` definitions in any
public theorem signature, 0 `native_decide`):

1. **`ppl039_cfs_tree_upper_bound` & `ppl039_erdos_rado_double_exp_upper_bound`:**
   Conlon–Fox–Sudakov (2010) vertex-online binary tree upper bound (strictly sharpening Erdős–Rado
   1952 from `2^{2^{4n}}` down to `2^{2^{2n + O(log n)}}`):
   for all `s, t ≥ 3`,
   `R_3(s, t) ≤ (choose (s + t - 4) (s - 2) + 1) * 2 ^ ((s + t - 6) * choose (s + t - 4) (s - 2) + 1)`,
   with diagonal corollary `R_3(n) ≤ 2 ^ (2 ^ (3 * n))` for all `n ≥ 3`.
2. **`ppl039_erdos_hajnal_lower_bound`:**
   Sharp probabilistic counting lower bound (Erdős–Hajnal–Rado 1965):
   for all `n ≥ 3`, `R_3(n) > 2 ^ ((n - 1) * (n - 2) / 6)` (achieving the exact leading exponent `1/6`).
3. **`ppl039_stepping_up_2_to_3_four_color` & `ppl039_stepping_up_four_color_r3`:**
   Erdős–Hajnal Stepping-Up Lemma for **4-colored 3-uniform hypergraphs**:
   `R_3(m + 1; 4) > 2 ^ (R_2(m) - 1)`, yielding `R_3(n; 4) > 2 ^ (2 ^ ((n - 2) / 2))` for all `n ≥ 4`.
4. **`ppl039_stepping_up_3_to_4_two_color` & `ppl039_stepping_up_two_color_r4`:**
   Erdős–Hajnal Stepping-Up Lemma for **2-colored 4-uniform hypergraphs**:
   `R_4(2 * m - 1) > 2 ^ (R_3(m) - 1)`, yielding
   `R_4(n) > 2 ^ (2 ^ (((n - 1) / 2) * ((n - 3) / 2) / 6))` for all `n ≥ 5`.
5. **`ppl039_two_color_stepping_up_barrier`:**
   **Exact 16-Case Two-Color Stepping-Up No-Go Theorem** pinpointing the parity obstruction of
   Erdős #564: for every `n ≥ 2`, `N ≥ n ^ 2`, base 2-coloring `φ`, and *every* Boolean projection
   `f : Bool → Bool → Bool`, the stepped-up 2-coloring on `Fin (2 ^ N)` given by
   `f (decide (δ x y < δ y z)) (φ {δ x y, δ y z})` (with `δ x y = Nat.log 2 (x ^^^ y)`) ALWAYS
   contains a monochromatic `n`-subset. Thus no 2-color projection of Erdős–Hajnal stepping-up can
   surpass `2 ^ (n ^ 2 - 1)`.
6. **`ppl039_r3_four_gt_twelve`:**
   Explicit 12-vertex witness proving `R_3(4) > 12` (matching Isbell 1969 / McKay–Radziszowski 1991
   `R_3(4) = 13`), verified directly in the Lean kernel with zero `native_decide`.
-/

namespace PPL039

/-! ### Section 1: Bit-Difference Ultrametric `δ x y = Nat.log 2 (x ^^^ y)` -/

section BitDelta

private lemma eq_of_xor_eq_zero {x y : ℕ} (h : x ^^^ y = 0) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi : (x ^^^ y).testBit i = false := by rw [h]; simp
  rw [Nat.testBit_xor] at hi
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

private lemma xor_ne_zero_of_ne {x y : ℕ} (h : x ≠ y) : x ^^^ y ≠ 0 :=
  fun hz => h (eq_of_xor_eq_zero hz)

private lemma delta_comm (x y : ℕ) : Nat.log 2 (x ^^^ y) = Nat.log 2 (y ^^^ x) := by
  rw [Nat.xor_comm]

private lemma add_eq_xor_of_and_zero : ∀ a b : ℕ, a &&& b = 0 → a + b = a ^^^ b := by
  have hmain : ∀ s a b : ℕ, a + b = s → a &&& b = 0 → a + b = a ^^^ b := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a b hsum hand
      by_cases ha0 : a = 0
      · subst ha0; simp
      · by_cases hb0 : b = 0
        · subst hb0; simp
        · have htb : ∀ n k : ℕ, n.testBit (k + 1) = (n / 2).testBit k := by
            intro n k
            rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
              Nat.div_div_eq_div_mul, ← pow_succ']
          have hbit0 : (a % 2) * (b % 2) = 0 := by
            have h0 : (a &&& b).testBit 0 = false := by rw [hand]; exact Nat.zero_testBit 0
            rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero] at h0
            have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
            have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
            rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;> simp_all
          have hand_div : (a / 2) &&& (b / 2) = 0 := by
            apply Nat.eq_of_testBit_eq
            intro i
            rw [Nat.testBit_and, Nat.zero_testBit, ← htb a i, ← htb b i]
            have hi : (a &&& b).testBit (i + 1) = false := by rw [hand]; exact Nat.zero_testBit _
            rwa [Nat.testBit_and] at hi
          have hlt : a / 2 + b / 2 < s := by omega
          have hrec : a / 2 + b / 2 = (a / 2) ^^^ (b / 2) :=
            ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl hand_div
          apply Nat.eq_of_testBit_eq
          intro i
          cases i with
          | zero =>
            rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
            have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
            have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
            rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;> simp_all <;> omega
          | succ j =>
            have hdiv_add : (a + b) / 2 = a / 2 + b / 2 := by
              have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
              have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
              rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;> simp_all <;> omega
            rw [htb (a + b) j, hdiv_add, hrec, Nat.testBit_xor, ← htb a j, ← htb b j,
              Nat.testBit_xor]
  exact fun a b h => hmain (a + b) a b rfl h

private lemma delta_lt_of_lt_two_pow {x y N : ℕ} (hx : x < 2 ^ N) (hy : y < 2 ^ N) (hxy : x ≠ y) :
    Nat.log 2 (x ^^^ y) < N :=
  Nat.log_lt_of_lt_pow (xor_ne_zero_of_ne hxy) (Nat.xor_lt_two_pow hx hy)

private lemma div_pow_succ_eq_of_delta {x y : ℕ} (_hxy : x ≠ y) :
    x / 2 ^ (Nat.log 2 (x ^^^ y) + 1) = y / 2 ^ (Nat.log 2 (x ^^^ y) + 1) := by
  set k := Nat.log 2 (x ^^^ y)
  have hlt : x ^^^ y < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (x ^^^ y)
  have hdiv0 : (x ^^^ y) / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt hlt
  have hsr : (x >>> (k + 1)) ^^^ (y >>> (k + 1)) = 0 := by
    rw [← Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow, hdiv0]
  have heq : x >>> (k + 1) = y >>> (k + 1) := eq_of_xor_eq_zero hsr
  simpa [Nat.shiftRight_eq_div_pow] using heq

private lemma div_pow_eq_one_of_bounds {v k : ℕ} (hlo : 2 ^ k ≤ v) (hhi : v < 2 ^ (k + 1)) :
    v / 2 ^ k = 1 := by
  have hpos : 0 < 2 ^ k := by positivity
  have h1 : 1 ≤ v / 2 ^ k := (Nat.le_div_iff_mul_le hpos).mpr (by simpa using hlo)
  have h2 : v / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr (by
    simpa [pow_succ, Nat.mul_comm] using hhi)
  omega

private lemma div_pow_xor_eq_one_of_delta {x y : ℕ} (hxy : x ≠ y) :
    (x / 2 ^ Nat.log 2 (x ^^^ y)) ^^^ (y / 2 ^ Nat.log 2 (x ^^^ y)) = 1 := by
  set k := Nat.log 2 (x ^^^ y)
  have hne : x ^^^ y ≠ 0 := xor_ne_zero_of_ne hxy
  have hdiv1 : (x ^^^ y) / 2 ^ k = 1 :=
    div_pow_eq_one_of_bounds (Nat.pow_log_le_self 2 hne)
      (Nat.lt_pow_succ_log_self (by norm_num) (x ^^^ y))
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_xor_distrib,
    Nat.shiftRight_eq_div_pow, hdiv1]

private lemma testBit_delta_of_lt {x y : ℕ} (hxy : x < y) :
    x.testBit (Nat.log 2 (x ^^^ y)) = false ∧ y.testBit (Nat.log 2 (x ^^^ y)) = true := by
  set k := Nat.log 2 (x ^^^ y)
  have hne : x ≠ y := Nat.ne_of_lt hxy
  have hdiv_succ := div_pow_succ_eq_of_delta hne
  have hxor1 := div_pow_xor_eq_one_of_delta hne
  have hle : x / 2 ^ k ≤ y / 2 ^ k := Nat.div_le_div_right (Nat.le_of_lt hxy)
  have hdiv2 : (x / 2 ^ k) / 2 = (y / 2 ^ k) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    simpa [pow_succ] using hdiv_succ
  have hne_div : x / 2 ^ k ≠ y / 2 ^ k := by
    intro heq
    rw [heq, Nat.xor_self] at hxor1
    omega
  have hmodx : (x / 2 ^ k) % 2 = 0 := by omega
  have hmody : (y / 2 ^ k) % 2 = 1 := by omega
  constructor
  · rw [Nat.testBit_eq_decide_div_mod_eq, hmodx]; rfl
  · rw [Nat.testBit_eq_decide_div_mod_eq, hmody]; rfl

private lemma delta_ne_of_lt_lt {x y z : ℕ} (hxy : x < y) (hyz : y < z) :
    Nat.log 2 (x ^^^ y) ≠ Nat.log 2 (y ^^^ z) := by
  intro heq
  have h1 := (testBit_delta_of_lt hxy).2
  have h2 := (testBit_delta_of_lt hyz).1
  rw [heq] at h1
  rw [h1] at h2
  exact Bool.noConfusion h2

private lemma delta_eq_max_of_lt_lt {x y z : ℕ} (hxy : x < y) (hyz : y < z) :
    Nat.log 2 (x ^^^ z) = max (Nat.log 2 (x ^^^ y)) (Nat.log 2 (y ^^^ z)) := by
  set a := Nat.log 2 (x ^^^ y)
  set b := Nat.log 2 (y ^^^ z)
  set m := max a b
  have hab : a ≠ b := delta_ne_of_lt_lt hxy hyz
  have hxz_eq : x ^^^ z = (x ^^^ y) ^^^ (y ^^^ z) := by
    rw [Nat.xor_assoc, ← Nat.xor_assoc y y z, Nat.xor_self, Nat.zero_xor]
  have hxy_lt : x ^^^ y < 2 ^ (m + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right (le_max_left a b) 1))
  have hyz_lt : y ^^^ z < 2 ^ (m + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right (le_max_right a b) 1))
  have hxz_lt : x ^^^ z < 2 ^ (m + 1) := by
    rw [hxz_eq]; exact Nat.xor_lt_two_pow hxy_lt hyz_lt
  have hdiv_pos : (x ^^^ z) / 2 ^ m = 1 := by
    rw [hxz_eq, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hm : m = b := max_eq_right (Nat.le_of_lt hlt)
      rw [hm]
      have h1 : (x ^^^ y) / 2 ^ b = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
          (Nat.pow_le_pow_right (by norm_num) hlt))
      have h2 : (y ^^^ z) / 2 ^ b = 1 :=
        div_pow_eq_one_of_bounds (Nat.pow_log_le_self 2 (xor_ne_zero_of_ne (Nat.ne_of_lt hyz)))
          (Nat.lt_pow_succ_log_self (by norm_num) _)
      rw [h1, h2]; rfl
    · have hm : m = a := max_eq_left (Nat.le_of_lt hgt)
      rw [hm]
      have h2 : (y ^^^ z) / 2 ^ a = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
          (Nat.pow_le_pow_right (by norm_num) hgt))
      have h1 : (x ^^^ y) / 2 ^ a = 1 :=
        div_pow_eq_one_of_bounds (Nat.pow_log_le_self 2 (xor_ne_zero_of_ne (Nat.ne_of_lt hxy)))
          (Nat.lt_pow_succ_log_self (by norm_num) _)
      rw [h1, h2]; rfl
  have hxz_ge : 2 ^ m ≤ x ^^^ z := by
    have hpos : 0 < 2 ^ m := by positivity
    have h1 : 1 * 2 ^ m ≤ x ^^^ z := (Nat.le_div_iff_mul_le hpos).mp (by omega)
    simpa using h1
  have hle : m ≤ Nat.log 2 (x ^^^ z) := Nat.le_log_of_pow_le (by norm_num) hxz_ge
  have hlt : Nat.log 2 (x ^^^ z) < m + 1 :=
    Nat.log_lt_of_lt_pow (xor_ne_zero_of_ne (Nat.ne_of_lt (lt_trans hxy hyz))) hxz_lt
  omega

private lemma strictMono_of_step {k : ℕ} {g : ℕ → ℕ}
    (hstep : ∀ i, i + 1 < k → g i < g (i + 1)) :
    ∀ u v, u < v → v < k → g u < g v := by
  intro u v huv hvk
  have hd : ∀ d u v, v - u = d → u < v → v < k → g u < g v := by
    intro d
    induction d with
    | zero => intro u v h huv; omega
    | succ d ih =>
      intro u v h huv hvk
      cases d with
      | zero =>
        have hv : v = u + 1 := by omega
        subst hv
        exact hstep u hvk
      | succ d' =>
        exact lt_trans (hstep u (by omega)) (ih (u + 1) v (by omega) (by omega) hvk)
  exact hd (v - u) u v rfl huv hvk

private lemma strictAnti_of_step {k : ℕ} {g : ℕ → ℕ}
    (hstep : ∀ i, i + 1 < k → g (i + 1) < g i) :
    ∀ u v, u < v → v < k → g v < g u := by
  intro u v huv hvk
  have hd : ∀ d u v, v - u = d → u < v → v < k → g v < g u := by
    intro d
    induction d with
    | zero => intro u v h huv; omega
    | succ d ih =>
      intro u v h huv hvk
      cases d with
      | zero =>
        have hv : v = u + 1 := by omega
        subst hv
        exact hstep u hvk
      | succ d' =>
        exact lt_trans (ih (u + 1) v (by omega) (by omega) hvk) (hstep u (by omega))
  exact hd (v - u) u v rfl huv hvk

private lemma delta_strictMono_chain {k : ℕ} {x : ℕ → ℕ}
    (hx : ∀ i j, i < j → j ≤ k → x i < x j)
    (hinc : ∀ i, i + 2 ≤ k → Nat.log 2 (x i ^^^ x (i + 1)) < Nat.log 2 (x (i + 1) ^^^ x (i + 2)))
    {a b : ℕ} (hab : a < b) (hbk : b ≤ k) :
    Nat.log 2 (x a ^^^ x b) = Nat.log 2 (x (b - 1) ^^^ x b) := by
  have hd : ∀ d a b, b - a = d → a < b → b ≤ k →
      Nat.log 2 (x a ^^^ x b) = Nat.log 2 (x (b - 1) ^^^ x b) := by
    intro d
    induction d with
    | zero => intro a b h hab; omega
    | succ d ih =>
      intro a b h hab hbk
      cases d with
      | zero =>
        have ha : a = b - 1 := by omega
        rw [ha]
      | succ d' =>
        have h1 : x a < x (a + 1) := hx a (a + 1) (by omega) (by omega)
        have h2 : x (a + 1) < x b := hx (a + 1) b (by omega) hbk
        rw [delta_eq_max_of_lt_lt h1 h2, ih (a + 1) b (by omega) (by omega) hbk]
        have hlt := strictMono_of_step (k := k) (g := fun i => Nat.log 2 (x i ^^^ x (i + 1)))
          (fun i hi => hinc i (by omega)) a (b - 1) (by omega) (by omega)
        have hb1 : b - 1 + 1 = b := by omega
        rw [hb1] at hlt
        exact max_eq_right (Nat.le_of_lt hlt)
  exact hd (b - a) a b rfl hab hbk

private lemma delta_strictAnti_chain {k : ℕ} {x : ℕ → ℕ}
    (hx : ∀ i j, i < j → j ≤ k → x i < x j)
    (hdec : ∀ i, i + 2 ≤ k → Nat.log 2 (x (i + 1) ^^^ x (i + 2)) < Nat.log 2 (x i ^^^ x (i + 1)))
    {a b : ℕ} (hab : a < b) (hbk : b ≤ k) :
    Nat.log 2 (x a ^^^ x b) = Nat.log 2 (x a ^^^ x (a + 1)) := by
  have hd : ∀ d a b, b - a = d → a < b → b ≤ k →
      Nat.log 2 (x a ^^^ x b) = Nat.log 2 (x a ^^^ x (a + 1)) := by
    intro d
    induction d with
    | zero => intro a b h hab; omega
    | succ d ih =>
      intro a b h hab hbk
      cases d with
      | zero =>
        have hb : b = a + 1 := by omega
        rw [hb]
      | succ d' =>
        have h1 : x a < x (a + 1) := hx a (a + 1) (by omega) (by omega)
        have h2 : x (a + 1) < x b := hx (a + 1) b (by omega) hbk
        rw [delta_eq_max_of_lt_lt h1 h2, ih (a + 1) b (by omega) (by omega) hbk]
        have hlt : Nat.log 2 (x (a + 1) ^^^ x (a + 1 + 1)) < Nat.log 2 (x a ^^^ x (a + 1)) :=
          hdec a (by omega)
        exact max_eq_left (Nat.le_of_lt hlt)
  exact hd (b - a) a b rfl hab hbk

private lemma orderEmbOfFin_triple {N : ℕ} {x y z : Fin N} (hxy : x < y) (hyz : y < z)
    {e : Finset (Fin N)} (he : e = {x, y, z}) (hc : e.card = 3) :
    e.orderEmbOfFin hc 0 = x ∧ e.orderEmbOfFin hc 1 = y ∧ e.orderEmbOfFin hc 2 = z := by
  set f := e.orderEmbOfFin hc
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have hmem : ∀ i : Fin 3, f i = x ∨ f i = y ∨ f i = z := by
    intro i
    have hm : f i ∈ ({x, y, z} : Finset (Fin N)) := by
      have h0 := Finset.orderEmbOfFin_mem e hc i
      exact he ▸ h0
    simpa [Finset.mem_insert, Finset.mem_singleton] using hm
  have h0 := hmem 0
  have h1 := hmem 1
  have h2 := hmem 2
  have hx : x.val < y.val := hxy
  have hy : y.val < z.val := hyz
  have hf01 : (f 0).val < (f 1).val := h01
  have hf12 : (f 1).val < (f 2).val := h12
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    simp_all [Fin.ext_iff] <;> omega

private lemma orderEmbOfFin_quad {N : ℕ} {a b c d : Fin N}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    {e : Finset (Fin N)} (he : e = {a, b, c, d}) (hc : e.card = 4) :
    e.orderEmbOfFin hc 0 = a ∧ e.orderEmbOfFin hc 1 = b ∧
    e.orderEmbOfFin hc 2 = c ∧ e.orderEmbOfFin hc 3 = d := by
  set f := e.orderEmbOfFin hc
  have hf01 : (f 0).val < (f 1).val := f.strictMono (by decide)
  have hf12 : (f 1).val < (f 2).val := f.strictMono (by decide)
  have hf23 : (f 2).val < (f 3).val := f.strictMono (by decide)
  have hmem : ∀ i : Fin 4, (f i).val = a.val ∨ (f i).val = b.val ∨ (f i).val = c.val ∨ (f i).val = d.val := by
    intro i
    have hm : f i ∈ ({a, b, c, d} : Finset (Fin N)) := he ▸ Finset.orderEmbOfFin_mem e hc i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h <;> simp [h]
  have ha : a.val < b.val := hab
  have hb : b.val < c.val := hbc
  have hc' : c.val < d.val := hcd
  have h0_ge : a.val ≤ (f 0).val := by rcases hmem 0 with h | h | h | h <;> omega
  have h1_ge : b.val ≤ (f 1).val := by rcases hmem 1 with h | h | h | h <;> omega
  have h2_ge : c.val ≤ (f 2).val := by rcases hmem 2 with h | h | h | h <;> omega
  have h3_ge : d.val ≤ (f 3).val := by rcases hmem 3 with h | h | h | h <;> omega
  have h3_le : (f 3).val ≤ d.val := by rcases hmem 3 with h | h | h | h <;> omega
  have h2_le : (f 2).val ≤ c.val := by rcases hmem 2 with h | h | h | h <;> omega
  have h1_le : (f 1).val ≤ b.val := by rcases hmem 1 with h | h | h | h <;> omega
  have h0_le : (f 0).val ≤ a.val := by rcases hmem 0 with h | h | h | h <;> omega
  exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩

end BitDelta

/-! ### Section 2: General Probabilistic Counting Lower Bound & Erdős–Hajnal `R_3(n) > 2^{c n^2}` -/

section ProbabilisticLowerBound

private lemma exists_coloring_no_mono (k n N : ℕ)
    (hbound : 2 * Nat.choose N n < 2 ^ Nat.choose n k) :
    ∃ c : Finset (Fin N) → Bool,
      ∀ S : Finset (Fin N), S.card = n →
        ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = k → c e = b := by
  classical
  let E : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard k
  have hEcard : E.card = Nat.choose N k := by
    simp [E, Finset.card_powersetCard]
  let badOf : Finset (Fin N) → Bool → Finset (E → Bool) := fun S b =>
    Finset.univ.filter (fun c : E → Bool => ∀ e : E, e.1 ⊆ S → c e = b)
  let allBad : Finset (E → Bool) :=
    ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion
      (fun S => badOf S true ∪ badOf S false)
  by_cases hnN : n ≤ N
  · have hbad_card : ∀ S : Finset (Fin N), S.card = n → ∀ b : Bool,
        (badOf S b).card ≤ 2 ^ (E.card - Nat.choose n k) := by
      intro S hS b
      let Rest := {e : E // ¬ e.1 ⊆ S}
      have hinj : Function.Injective (fun c : badOf S b => fun r : Rest => c.1 r.1) := by
        intro c₁ c₂ hEq
        apply Subtype.ext
        funext e
        by_cases he : e.1 ⊆ S
        · have h1 := (Finset.mem_filter.mp c₁.2).2 e he
          have h2 := (Finset.mem_filter.mp c₂.2).2 e he
          rw [h1, h2]
        · exact congrFun hEq ⟨e, he⟩
      have hcard_le : (badOf S b).card ≤ Fintype.card (Rest → Bool) := by
        simpa [Fintype.card_coe] using Fintype.card_le_of_injective _ hinj
      have hRest_card : Fintype.card Rest = E.card - Nat.choose n k := by
        have hsub : S.powersetCard k ⊆ E := by
          intro e he
          rw [Finset.mem_powersetCard] at he ⊢
          exact ⟨Finset.subset_univ _, he.2⟩
        have hEq : (Finset.univ.filter (fun e : E => ¬ e.1 ⊆ S)).card = (E \ S.powersetCard k).card := by
          refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
          · intro e he
            have hne := (Finset.mem_filter.mp he).2
            refine Finset.mem_sdiff.mpr ⟨e.2, fun hmem => hne (Finset.mem_powersetCard.mp hmem).1⟩
          · intro e₁ _ e₂ _ h; exact Subtype.ext h
          · intro e he
            rcases Finset.mem_sdiff.mp he with ⟨heE, heS⟩
            refine ⟨⟨e, heE⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hsubS => heS ?_⟩, rfl⟩
            exact Finset.mem_powersetCard.mpr ⟨hsubS, (Finset.mem_powersetCard.mp heE).2⟩
        have hSc : (S.powersetCard k).card = Nat.choose n k := by
          rw [Finset.card_powersetCard, hS]
        rw [Fintype.card_subtype, hEq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hSc]
      simpa [Fintype.card_fun, Fintype.card_bool, hRest_card] using hcard_le
    have hallBad_le : allBad.card ≤ (2 * Nat.choose N n) * 2 ^ (E.card - Nat.choose n k) := by
      calc allBad.card
          ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
              (badOf S true ∪ badOf S false).card := Finset.card_biUnion_le
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
              ((badOf S true).card + (badOf S false).card) :=
            Finset.sum_le_sum fun S _ => Finset.card_union_le _ _
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
              (2 * 2 ^ (E.card - Nat.choose n k)) := by
            refine Finset.sum_le_sum fun S hS => ?_
            have hScard := (Finset.mem_powersetCard.mp hS).2
            have h1 := hbad_card S hScard true
            have h2 := hbad_card S hScard false
            omega
        _ = Nat.choose N n * (2 * 2 ^ (E.card - Nat.choose n k)) := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul]
        _ = (2 * Nat.choose N n) * 2 ^ (E.card - Nat.choose n k) := by ring
    have hchoose_le : Nat.choose n k ≤ E.card := by
      rw [hEcard]; exact Nat.choose_le_choose k hnN
    have hallBad_lt : allBad.card < Fintype.card (E → Bool) := by
      have htot : Fintype.card (E → Bool) = 2 ^ Nat.choose n k * 2 ^ (E.card - Nat.choose n k) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, ← pow_add,
          Nat.add_sub_cancel' hchoose_le]
      rw [htot]
      exact lt_of_le_of_lt hallBad_le
        (Nat.mul_lt_mul_of_pos_right hbound (by positivity))
    have hne : (Finset.univ \ allBad).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      omega
    obtain ⟨c₀, hc₀⟩ := hne
    have hc₀_not : c₀ ∉ allBad := (Finset.mem_sdiff.mp hc₀).2
    refine ⟨fun e => if h : e ∈ E then c₀ ⟨e, h⟩ else false, ?_⟩
    intro S hS ⟨b, hb⟩
    apply hc₀_not
    rw [Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
    cases b
    · apply Finset.mem_union_right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun e he => ?_⟩
      have h := hb e.1 he (Finset.mem_powersetCard.mp e.2).2
      simpa [e.2] using h
    · apply Finset.mem_union_left
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun e he => ?_⟩
      have h := hb e.1 he (Finset.mem_powersetCard.mp e.2).2
      simpa [e.2] using h
  · refine ⟨fun _ => false, fun S hS _ => ?_⟩
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    omega

private lemma choose_mul_fact_le_pow (N n : ℕ) : Nat.choose N n * n.factorial ≤ N ^ n := by
  rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow N n

private lemma erdos_1947_graph_lower_bound (m : ℕ) (hm : 3 ≤ m) :
    ∃ c : Finset (Fin (2 ^ ((m - 1) / 2))) → Bool,
      ∀ S : Finset (Fin (2 ^ ((m - 1) / 2))), S.card = m →
        ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 2 → c e = b := by
  apply exists_coloring_no_mono 2 m (2 ^ ((m - 1) / 2))
  set N := 2 ^ ((m - 1) / 2)
  have hfact : 6 ≤ m.factorial := by
    have h3 : (3 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
    simpa [Nat.factorial] using h3
  have hpow : N ^ m ≤ 2 ^ Nat.choose m 2 := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [Nat.choose_two_right, Nat.mul_comm]
    exact Nat.mul_div_le_mul_div_assoc m (m - 1) 2
  have hcm := choose_mul_fact_le_pow N m
  have h2 : 2 * Nat.choose N m * 3 ≤ Nat.choose N m * m.factorial := by
    calc 2 * Nat.choose N m * 3 = Nat.choose N m * 6 := by ring
      _ ≤ Nat.choose N m * m.factorial := Nat.mul_le_mul_left _ hfact
  have hpos : 0 < 2 ^ Nat.choose m 2 := by positivity
  omega

/-- **Erdős–Hajnal–Rado (1965) Sharp Probabilistic Lower Bound for `R_3(n)`:**
For every `n ≥ 3`, there exists a 2-coloring of the 3-element subsets of
`Fin (2 ^ ((n - 1) * (n - 2) / 6))` with no monochromatic `n`-subset, establishing
`R_3(n) > 2 ^ ⌊(n - 1)(n - 2) / 6⌋ = 2 ^ ((1/6 - o(1)) n^2)`. -/
theorem ppl039_erdos_hajnal_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ c : Finset (Fin (2 ^ ((n - 1) * (n - 2) / 6))) → Bool,
      ∀ S : Finset (Fin (2 ^ ((n - 1) * (n - 2) / 6))), S.card = n →
        ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 3 → c e = b := by
  apply exists_coloring_no_mono 3 n (2 ^ ((n - 1) * (n - 2) / 6))
  set N := 2 ^ ((n - 1) * (n - 2) / 6)
  have hfact : 6 ≤ n.factorial := by
    have h3 : (3 : ℕ).factorial ≤ n.factorial := Nat.factorial_le hn
    simpa [Nat.factorial] using h3
  have hchoose3 : Nat.choose n 3 = n * ((n - 1) * (n - 2)) / 6 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 3
    have hd : n.descFactorial 3 = n * ((n - 1) * (n - 2)) := by
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
      ring
    have hf : (3 : ℕ).factorial = 6 := by decide
    rw [hd, hf] at h
    omega
  have hpow : N ^ n ≤ 2 ^ Nat.choose n 3 := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [hchoose3, Nat.mul_comm]
    exact Nat.mul_div_le_mul_div_assoc n ((n - 1) * (n - 2)) 6
  have hcm := choose_mul_fact_le_pow N n
  have h2 : 2 * Nat.choose N n * 3 ≤ Nat.choose N n * n.factorial := by
    calc 2 * Nat.choose N n * 3 = Nat.choose N n * 6 := by ring
      _ ≤ Nat.choose N n * n.factorial := Nat.mul_le_mul_left _ hfact
  have hpos : 0 < 2 ^ Nat.choose n 3 := by positivity
  omega

end ProbabilisticLowerBound

/-! ### Section 3: Erdős–Szekeres Graph Ramsey Upper Bound -/

section ErdosSzekeres

private lemma erdos_szekeres_graph {α : Type*} [DecidableEq α] :
    ∀ k s t, s + t = k → 1 ≤ s → 1 ≤ t →
      ∀ (V : Finset α), Nat.choose (s + t - 2) (s - 1) ≤ V.card →
      ∀ (φ : Finset α → Bool),
        (∃ S ⊆ V, S.card = s ∧ ∀ e ⊆ S, e.card = 2 → φ e = true) ∨
        (∃ T ⊆ V, T.card = t ∧ ∀ e ⊆ T, e.card = 2 → φ e = false) := by
  intro k
  induction k with
  | zero => intro s t hst hs; omega
  | succ k ih =>
    intro s t hst hs ht V hV φ
    by_cases hs1 : s = 1
    · subst hs1
      have hpos : 0 < V.card := by
        have hch : Nat.choose (1 + t - 2) 0 = 1 := Nat.choose_zero_right _
        rw [hch] at hV; omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      left
      refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, Finset.card_singleton v, ?_⟩
      intro e he hcard
      have := Finset.card_le_card he
      simp [hcard] at this
    · by_cases ht1 : t = 1
      · subst ht1
        have hpos : 0 < V.card := by
          have hch : Nat.choose (s + 1 - 2) (s - 1) = 1 := by
            have hEq : s + 1 - 2 = s - 1 := by omega
            rw [hEq, Nat.choose_self]
          rw [hch] at hV; omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        right
        refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, Finset.card_singleton v, ?_⟩
        intro e he hcard
        have := Finset.card_le_card he
        simp [hcard] at this
      · have hs2 : 2 ≤ s := by omega
        have ht2 : 2 ≤ t := by omega
        have hpas : Nat.choose (s + t - 2) (s - 1) =
            Nat.choose (s + t - 3) (s - 2) + Nat.choose (s + t - 3) (s - 1) := by
          have h1 : s + t - 2 = (s + t - 3) + 1 := by omega
          have h2 : s - 1 = (s - 2) + 1 := by omega
          rw [h1, h2, Nat.choose_succ_succ]
        have hpos : 0 < V.card := by
          have hc : 1 ≤ Nat.choose (s + t - 2) (s - 1) :=
            Nat.choose_pos (by omega)
          omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        let R := (V.erase v).filter (fun u => φ {v, u} = true)
        let B := (V.erase v).filter (fun u => φ {v, u} = false)
        have hRB : R.card + B.card = V.card - 1 := by
          have hun : R ∪ B = V.erase v := by
            ext u
            simp only [R, B, Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
            · intro hu
              cases h : φ {v, u}
              · exact Or.inr ⟨hu, rfl⟩
              · exact Or.inl ⟨hu, rfl⟩
          have hdisj : Disjoint R B := by
            rw [Finset.disjoint_left]
            intro u huR huB
            have h1 := (Finset.mem_filter.mp huR).2
            have h2 := (Finset.mem_filter.mp huB).2
            rw [h1] at h2; exact Bool.noConfusion h2
          rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_erase_of_mem hv]
        by_cases hR : Nat.choose (s + t - 3) (s - 2) ≤ R.card
        · have hrec := ih (s - 1) t (by omega) (by omega) ht R (by
            have h1 : s - 1 + t - 2 = s + t - 3 := by omega
            have h2 : s - 1 - 1 = s - 2 := by omega
            rw [h1, h2]; exact hR) φ
          rcases hrec with ⟨S, hSR, hScard, hScol⟩ | ⟨T, hTR, hTcard, hTcol⟩
          · left
            have hvS : v ∉ S := fun hv' => (Finset.mem_erase.mp (Finset.mem_filter.mp (hSR hv')).1).1 rfl
            refine ⟨insert v S, ?_, by rw [Finset.card_insert_of_notMem hvS, hScard]; omega, ?_⟩
            · intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hxS
              · exact hv
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hSR hxS)).1
            · intro e he hcard
              by_cases hve : v ∈ e
              · obtain ⟨u, hu, heEq⟩ : ∃ u ∈ S, e = {v, u} := by
                  have h1 : (e.erase v).card = 1 := by rw [Finset.card_erase_of_mem hve, hcard]
                  obtain ⟨u, huEq⟩ := Finset.card_eq_one.mp h1
                  have hue : u ∈ e.erase v := by rw [huEq]; simp
                  have huv : u ≠ v := (Finset.mem_erase.mp hue).1
                  have huS : u ∈ S := by
                    have := he (Finset.mem_of_mem_erase hue)
                    rcases Finset.mem_insert.mp this with rfl | h
                    · exact absurd rfl huv
                    · exact h
                  refine ⟨u, huS, ?_⟩
                  ext x
                  by_cases hxv : x = v
                  · subst hxv; simp [hve]
                  · constructor
                    · intro hx
                      have : x ∈ e.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
                      rw [huEq] at this
                      simp [Finset.mem_singleton.mp this]
                    · intro hx
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with rfl | rfl
                      · exact hve
                      · exact Finset.mem_of_mem_erase hue
                rw [heEq]
                exact (Finset.mem_filter.mp (hSR hu)).2
              · apply hScol e _ hcard
                intro x hx
                rcases Finset.mem_insert.mp (he hx) with rfl | hxS
                · exact absurd hx hve
                · exact hxS
          · right
            refine ⟨T, fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTR hx)).1, hTcard, hTcol⟩
        · have hB : Nat.choose (s + t - 3) (s - 1) ≤ B.card := by omega
          have hrec := ih s (t - 1) (by omega) hs (by omega) B (by
            have h1 : s + (t - 1) - 2 = s + t - 3 := by omega
            rw [h1]; exact hB) φ
          rcases hrec with ⟨S, hSB, hScard, hScol⟩ | ⟨T, hTB, hTcard, hTcol⟩
          · left
            refine ⟨S, fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.mp (hSB hx)).1, hScard, hScol⟩
          · right
            have hvT : v ∉ T := fun hv' => (Finset.mem_erase.mp (Finset.mem_filter.mp (hTB hv')).1).1 rfl
            refine ⟨insert v T, ?_, by rw [Finset.card_insert_of_notMem hvT, hTcard]; omega, ?_⟩
            · intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hxT
              · exact hv
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTB hxT)).1
            · intro e he hcard
              by_cases hve : v ∈ e
              · obtain ⟨u, hu, heEq⟩ : ∃ u ∈ T, e = {v, u} := by
                  have h1 : (e.erase v).card = 1 := by rw [Finset.card_erase_of_mem hve, hcard]
                  obtain ⟨u, huEq⟩ := Finset.card_eq_one.mp h1
                  have hue : u ∈ e.erase v := by rw [huEq]; simp
                  have huv : u ≠ v := (Finset.mem_erase.mp hue).1
                  have huT : u ∈ T := by
                    have := he (Finset.mem_of_mem_erase hue)
                    rcases Finset.mem_insert.mp this with rfl | h
                    · exact absurd rfl huv
                    · exact h
                  refine ⟨u, huT, ?_⟩
                  ext x
                  by_cases hxv : x = v
                  · subst hxv; simp [hve]
                  · constructor
                    · intro hx
                      have : x ∈ e.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
                      rw [huEq] at this
                      simp [Finset.mem_singleton.mp this]
                    · intro hx
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with rfl | rfl
                      · exact hve
                      · exact Finset.mem_of_mem_erase hue
                rw [heEq]
                exact (Finset.mem_filter.mp (hTB hu)).2
              · apply hTcol e _ hcard
                intro x hx
                rcases Finset.mem_insert.mp (he hx) with rfl | hxT
                · exact absurd hx hve
                · exact hxT

end ErdosSzekeres

/-! ### Section 4: Conlon–Fox–Sudakov (2010) Binary-Tree Upper Bound for `R_3(s, t)` -/

section CFSTreeUpperBound

private def treeStrings : ℕ → ℕ → Finset (List Bool)
  | 0, 0 => {[]}
  | a + 1, 0 => insert [] ((treeStrings a 0).image (List.cons true))
  | 0, b + 1 => insert [] ((treeStrings 0 b).image (List.cons false))
  | a + 1, b + 1 =>
      insert [] (((treeStrings a (b + 1)).image (List.cons true)) ∪
                 ((treeStrings (a + 1) b).image (List.cons false)))

private lemma mem_treeStrings_iff : ∀ a b (σ : List Bool),
    σ ∈ treeStrings a b ↔ σ.count true ≤ a ∧ σ.count false ≤ b
  | 0, 0, σ => by
    cases σ with
    | nil => simp [treeStrings]
    | cons d r =>
      cases d <;> simp [treeStrings]
  | a + 1, 0, σ => by
    cases σ with
    | nil => simp [treeStrings]
    | cons d r =>
      cases d with
      | false => simp [treeStrings]
      | true =>
        simp only [treeStrings, Finset.mem_insert, Finset.mem_image, List.cons.injEq,
          List.count_cons_self, reduceCtorEq, false_or, true_and]
        have hcf : (true :: r).count false = r.count false :=
          List.count_cons_of_ne (by decide)
        rw [hcf]
        constructor
        · rintro ⟨r', hr', rfl⟩
          have := (mem_treeStrings_iff a 0 r').mp hr'
          omega
        · intro h
          refine ⟨r, (mem_treeStrings_iff a 0 r).mpr ⟨by omega, h.2⟩, rfl⟩
  | 0, b + 1, σ => by
    cases σ with
    | nil => simp [treeStrings]
    | cons d r =>
      cases d with
      | true => simp [treeStrings]
      | false =>
        simp only [treeStrings, Finset.mem_insert, Finset.mem_image, List.cons.injEq,
          List.count_cons_self, reduceCtorEq, false_or, true_and]
        have hct : (false :: r).count true = r.count true :=
          List.count_cons_of_ne (by decide)
        rw [hct]
        constructor
        · rintro ⟨r', hr', rfl⟩
          have := (mem_treeStrings_iff 0 b r').mp hr'
          omega
        · intro h
          refine ⟨r, (mem_treeStrings_iff 0 b r).mpr ⟨h.1, by omega⟩, rfl⟩
  | a + 1, b + 1, σ => by
    cases σ with
    | nil => simp [treeStrings]
    | cons d r =>
      cases d with
      | true =>
        simp only [treeStrings, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          List.cons.injEq, List.count_cons_self, reduceCtorEq, false_or, true_and, false_and,
          and_false, exists_false, or_false]
        have hcf : (true :: r).count false = r.count false :=
          List.count_cons_of_ne (by decide)
        rw [hcf]
        constructor
        · rintro ⟨r', hr', rfl⟩
          have := (mem_treeStrings_iff a (b + 1) r').mp hr'
          omega
        · intro h
          refine ⟨r, (mem_treeStrings_iff a (b + 1) r).mpr ⟨by omega, h.2⟩, rfl⟩
      | false =>
        simp only [treeStrings, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          List.cons.injEq, List.count_cons_self, reduceCtorEq, false_or, true_and, false_and,
          and_false, exists_false]
        have hct : (false :: r).count true = r.count true :=
          List.count_cons_of_ne (by decide)
        rw [hct]
        constructor
        · rintro ⟨r', hr', rfl⟩
          have := (mem_treeStrings_iff (a + 1) b r').mp hr'
          omega
        · intro h
          refine ⟨r, (mem_treeStrings_iff (a + 1) b r).mpr ⟨h.1, by omega⟩, rfl⟩

private lemma card_treeStrings : ∀ a b : ℕ,
    (treeStrings a b).card + 1 = Nat.choose (a + b + 2) (a + 1)
  | 0, 0 => by simp [treeStrings]
  | a + 1, 0 => by
    have hnot : ([] : List Bool) ∉ (treeStrings a 0).image (List.cons true) := by simp
    have hinj : Function.Injective (List.cons true) := fun _ _ h => (List.cons.inj h).2
    rw [treeStrings, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj]
    have ih := card_treeStrings a 0
    have h1 : a + 1 + 0 + 2 = (a + 2) + 1 := by omega
    have h0 : a + 0 + 2 = a + 2 := by omega
    rw [h0] at ih
    rw [h1, Nat.choose_succ_succ, Nat.choose_self]
    omega
  | 0, b + 1 => by
    have hnot : ([] : List Bool) ∉ (treeStrings 0 b).image (List.cons false) := by simp
    have hinj : Function.Injective (List.cons false) := fun _ _ h => (List.cons.inj h).2
    rw [treeStrings, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj]
    have ih := card_treeStrings 0 b
    have h1 : 0 + (b + 1) + 2 = (0 + b + 2) + 1 := by omega
    rw [h1, Nat.choose_succ_succ, Nat.choose_zero_right]
    have hsucc : Nat.choose (0 + b + 2) (Nat.succ 0) = Nat.choose (0 + b + 2) (0 + 1) := rfl
    rw [hsucc]
    omega
  | a + 1, b + 1 => by
    have hdisj : Disjoint ((treeStrings a (b + 1)).image (List.cons true))
        ((treeStrings (a + 1) b).image (List.cons false)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨_, _, h⟩
      exact Bool.noConfusion (List.cons.inj h).1
    have hnot : ([] : List Bool) ∉ ((treeStrings a (b + 1)).image (List.cons true)) ∪
        ((treeStrings (a + 1) b).image (List.cons false)) := by simp
    have hinjT : Function.Injective (List.cons true) := fun _ _ h => (List.cons.inj h).2
    have hinjF : Function.Injective (List.cons false) := fun _ _ h => (List.cons.inj h).2
    rw [treeStrings, Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hinjT, Finset.card_image_of_injective _ hinjF]
    have ih1 := card_treeStrings a (b + 1)
    have ih2 := card_treeStrings (a + 1) b
    have h1 : a + 1 + (b + 1) + 2 = (a + (b + 1) + 2) + 1 := by omega
    have h2 : a + 1 + b + 2 = a + (b + 1) + 2 := by omega
    rw [h2] at ih2
    rw [h1, Nat.choose_succ_succ]
    change (treeStrings a (b + 1)).card + (treeStrings (a + 1) b).card + 1 + 1 =
      (a + (b + 1) + 2).choose (a + 1) + (a + (b + 1) + 2).choose (a + 1 + 1)
    omega

private lemma list_bool_length_eq_count (σ : List Bool) :
    σ.length = σ.count true + σ.count false := by
  induction σ with
  | nil => simp
  | cons d r ih =>
    cases d <;> simp [ih] <;> omega

private lemma length_le_of_mem_treeStrings {a b : ℕ} {σ : List Bool} (h : σ ∈ treeStrings a b) :
    σ.length ≤ a + b := by
  have hc := (mem_treeStrings_iff a b σ).mp h
  rw [list_bool_length_eq_count]
  omega

private lemma list_exists_snoc {α : Type*} {l : List α} (hl : l ≠ []) :
    ∃ l₀ x, l = l₀ ++ [x] := by
  cases h : l.reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp h) hl
  | cons x r =>
    refine ⟨r.reverse, x, ?_⟩
    have := congrArg List.reverse h
    simpa [List.reverse_cons] using this

/-- Strict prefix relation: `τ` is a prefix of `σ` with next bit `d`. -/
private def IsPrefixBit (τ : List Bool) (d : Bool) (σ : List Bool) : Prop :=
  ∃ r : List Bool, σ = τ ++ d :: r

private lemma isPrefixBit_length_lt {τ σ : List Bool} {d : Bool} (h : IsPrefixBit τ d σ) :
    τ.length < σ.length := by
  rcases h with ⟨r, rfl⟩
  simp

/-- Collect all proper prefixes of `σ` whose next bit equals `d`. -/
private def prefixesWithBit (d : Bool) : List Bool → Finset (List Bool)
  | [] => ∅
  | b :: r =>
      let rest := (prefixesWithBit d r).image (List.cons b)
      if b = d then insert [] rest else rest

private lemma mem_prefixesWithBit_iff (d : Bool) : ∀ (σ τ : List Bool),
    τ ∈ prefixesWithBit d σ ↔ IsPrefixBit τ d σ
  | [], τ => by
    simp only [prefixesWithBit, Finset.notMem_empty, false_iff]
    rintro ⟨r, h⟩
    cases τ <;> simp at h
  | b :: r, τ => by
    simp only [prefixesWithBit]
    cases τ with
    | nil =>
      by_cases hbd : b = d
      · subst hbd
        simp [IsPrefixBit]
      · simp only [hbd, ↓reduceIte, Finset.mem_image, reduceCtorEq, and_false, exists_false,
          false_iff]
        rintro ⟨r', h⟩
        exact hbd (List.cons.inj h).1
    | cons b' τ' =>
      by_cases hbd : b = d
      · subst hbd
        simp only [↓reduceIte, Finset.mem_insert, reduceCtorEq, Finset.mem_image, List.cons.injEq,
          false_or]
        constructor
        · rintro ⟨τ'', hτ'', rfl, rfl⟩
          rcases (mem_prefixesWithBit_iff b r τ'').mp hτ'' with ⟨r', hr'⟩
          exact ⟨r', by simp [hr']⟩
        · rintro ⟨r', hr'⟩
          have hb : b = b' := (List.cons.inj hr').1
          have hr : r = τ' ++ b :: r' := (List.cons.inj hr').2
          subst hb
          exact ⟨τ', (mem_prefixesWithBit_iff b r τ').mpr ⟨r', hr⟩, rfl, rfl⟩
      · simp only [hbd, ↓reduceIte, Finset.mem_image, List.cons.injEq]
        constructor
        · rintro ⟨τ'', hτ'', rfl, rfl⟩
          rcases (mem_prefixesWithBit_iff d r τ'').mp hτ'' with ⟨r', hr'⟩
          exact ⟨r', by simp [hr']⟩
        · rintro ⟨r', hr'⟩
          have hb : b = b' := (List.cons.inj hr').1
          have hr : r = τ' ++ d :: r' := (List.cons.inj hr').2
          subst hb
          exact ⟨τ', (mem_prefixesWithBit_iff d r τ').mpr ⟨r', hr⟩, rfl, rfl⟩

private lemma card_prefixesWithBit (d : Bool) : ∀ (σ : List Bool),
    (prefixesWithBit d σ).card = σ.count d
  | [] => by simp [prefixesWithBit]
  | b :: r => by
    simp only [prefixesWithBit]
    have hinj : Function.Injective (List.cons b) := fun _ _ h => (List.cons.inj h).2
    have hnot : ([] : List Bool) ∉ (prefixesWithBit d r).image (List.cons b) := by simp
    by_cases hbd : b = d
    · subst hbd
      rw [if_pos rfl, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
        card_prefixesWithBit b r, List.count_cons_self]
    · rw [if_neg hbd, Finset.card_image_of_injective _ hinj, card_prefixesWithBit d r,
        List.count_cons_of_ne hbd]

private lemma isPrefixBit_total_of_both {τ₁ τ₂ σ : List Bool} {d₁ d₂ : Bool}
    (h1 : IsPrefixBit τ₁ d₁ σ) (h2 : IsPrefixBit τ₂ d₂ σ) (hne : τ₁ ≠ τ₂) :
    IsPrefixBit τ₁ d₁ τ₂ ∨ IsPrefixBit τ₂ d₂ τ₁ := by
  rcases h1 with ⟨r₁, hr₁⟩
  rcases h2 with ⟨r₂, hr₂⟩
  have hEq : τ₁ ++ d₁ :: r₁ = τ₂ ++ d₂ :: r₂ := hr₁.symm.trans hr₂
  rcases lt_or_gt_of_ne (fun hlen => hne (List.append_inj_left hEq hlen)) with hlt | hgt
  · left
    have htake : τ₁ = τ₂.take τ₁.length := by
      have := congrArg (List.take τ₁.length) hEq
      simp only [List.take_left, List.take_append_of_le_length (Nat.le_of_lt hlt)] at this
      exact this
    have hdrop : d₁ :: r₁ = τ₂.drop τ₁.length ++ d₂ :: r₂ := by
      have := congrArg (List.drop τ₁.length) hEq
      simp only [List.drop_left, List.drop_append_of_le_length (Nat.le_of_lt hlt)] at this
      exact this
    cases hτ₂ : τ₂.drop τ₁.length with
    | nil =>
      have := @List.length_drop _ τ₁.length τ₂
      rw [hτ₂] at this
      simp at this; omega
    | cons d' r' =>
      rw [hτ₂, List.cons_append] at hdrop
      have hd : d₁ = d' := (List.cons.inj hdrop).1
      subst hd
      refine ⟨r', ?_⟩
      conv_lhs => rw [← List.take_append_drop τ₁.length τ₂, ← htake, hτ₂]
  · right
    have hEq' : τ₂ ++ d₂ :: r₂ = τ₁ ++ d₁ :: r₁ := hEq.symm
    have htake : τ₂ = τ₁.take τ₂.length := by
      have := congrArg (List.take τ₂.length) hEq'
      simp only [List.take_left, List.take_append_of_le_length (Nat.le_of_lt hgt)] at this
      exact this
    have hdrop : d₂ :: r₂ = τ₁.drop τ₂.length ++ d₁ :: r₁ := by
      have := congrArg (List.drop τ₂.length) hEq'
      simp only [List.drop_left, List.drop_append_of_le_length (Nat.le_of_lt hgt)] at this
      exact this
    cases hτ₁ : τ₁.drop τ₂.length with
    | nil =>
      have := @List.length_drop _ τ₂.length τ₁
      rw [hτ₁] at this
      simp at this; omega
    | cons d' r' =>
      rw [hτ₁, List.cons_append] at hdrop
      have hd : d₂ = d' := (List.cons.inj hdrop).1
      subst hd
      refine ⟨r', ?_⟩
      conv_lhs => rw [← List.take_append_drop τ₂.length τ₁, ← htake, hτ₁]

/-- Walk a vertex `v` down the occupied tree `dom` by majority halving. -/
private lemma walk_down_tree {α : Type*} [DecidableEq α]
    (a b : ℕ) (c : Finset α → Bool)
    (dom : Finset (List Bool)) (hdom_sub : dom ⊆ treeStrings a b)
    (vert : List Bool → α)
    (v : α) (V_rem E_rem : ℕ) (hE : a + b + 1 ≤ E_rem) :
    ∀ (steps : ℕ) (σ : List Bool) (S : Finset α),
      σ.length + steps = a + b + 1 →
      (∀ τ d, IsPrefixBit τ d σ → τ ∈ dom) →
      (∀ τ d, IsPrefixBit τ d σ → ∀ w ∈ S, c {vert τ, v, w} = d) →
      V_rem * 2 ^ (E_rem - σ.length) ≤ S.card →
      ∃ (σ' : List Bool) (S' : Finset α),
        σ' ∉ dom ∧
        S' ⊆ S ∧
        σ'.length ≤ a + b + 1 ∧
        (∀ τ d, IsPrefixBit τ d σ' → τ ∈ dom) ∧
        (∀ τ d, IsPrefixBit τ d σ' → ∀ w ∈ S', c {vert τ, v, w} = d) ∧
        (σ' ∉ treeStrings a b → σ'.count true = a + 1 ∨ σ'.count false = b + 1) ∧
        V_rem * 2 ^ (E_rem - σ'.length) ≤ S'.card := by
  intro steps
  induction steps with
  | zero =>
    intro σ S hlen hpref hcol hS
    have hnot : σ ∉ dom := by
      intro hmem
      have := length_le_of_mem_treeStrings (hdom_sub hmem)
      omega
    refine ⟨σ, S, hnot, Finset.Subset.refl _, by omega, hpref, hcol, ?_, hS⟩
    intro hnotT
    have hne : σ ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    obtain ⟨σ₀, d, rfl⟩ := list_exists_snoc hne
    have hσ₀_dom : σ₀ ∈ dom := hpref σ₀ d ⟨[], by simp⟩
    have hσ₀_c := (mem_treeStrings_iff a b σ₀).mp (hdom_sub hσ₀_dom)
    have hc_not := (mem_treeStrings_iff a b (σ₀ ++ [d])).not.mp hnotT
    cases d
    · simp only [List.count_append, List.count_cons_self,
        List.count_cons_of_ne (by decide : false ≠ true), List.count_nil] at hc_not ⊢
      omega
    · simp only [List.count_append, List.count_cons_self,
        List.count_cons_of_ne (by decide : true ≠ false), List.count_nil] at hc_not ⊢
      omega
  | succ steps ih =>
    intro σ S hlen hpref hcol hS
    by_cases hσ : σ ∈ dom
    · have hσ_len : σ.length ≤ a + b := length_le_of_mem_treeStrings (hdom_sub hσ)
      let ST := S.filter (fun w => c {vert σ, v, w} = true)
      let SF := S.filter (fun w => c {vert σ, v, w} = false)
      have hsum : ST.card + SF.card = S.card := by
        have hun : ST ∪ SF = S := by
          ext w
          simp only [ST, SF, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
          · intro hw
            cases h : c {vert σ, v, w}
            · exact Or.inr ⟨hw, rfl⟩
            · exact Or.inl ⟨hw, rfl⟩
        have hdisj : Disjoint ST SF := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          have h1 := (Finset.mem_filter.mp hw1).2
          have h2 := (Finset.mem_filter.mp hw2).2
          rw [h1] at h2; exact Bool.noConfusion h2
        rw [← Finset.card_union_of_disjoint hdisj, hun]
      have hpow_split : V_rem * 2 ^ (E_rem - σ.length) =
          V_rem * 2 ^ (E_rem - (σ.length + 1)) + V_rem * 2 ^ (E_rem - (σ.length + 1)) := by
        have : E_rem - σ.length = (E_rem - (σ.length + 1)) + 1 := by omega
        rw [this, pow_succ]
        ring
      have hhalf : V_rem * 2 ^ (E_rem - (σ.length + 1)) ≤ ST.card ∨
                   V_rem * 2 ^ (E_rem - (σ.length + 1)) ≤ SF.card := by
        rw [hpow_split] at hS
        omega
      have hstep : ∀ (d : Bool) (Sd : Finset α),
          Sd ⊆ S →
          (∀ w ∈ Sd, c {vert σ, v, w} = d) →
          V_rem * 2 ^ (E_rem - (σ.length + 1)) ≤ Sd.card →
          ∃ (σ' : List Bool) (S' : Finset α),
            σ' ∉ dom ∧
            S' ⊆ S ∧
            σ'.length ≤ a + b + 1 ∧
            (∀ τ d', IsPrefixBit τ d' σ' → τ ∈ dom) ∧
            (∀ τ d', IsPrefixBit τ d' σ' → ∀ w ∈ S', c {vert τ, v, w} = d') ∧
            (σ' ∉ treeStrings a b → σ'.count true = a + 1 ∨ σ'.count false = b + 1) ∧
            V_rem * 2 ^ (E_rem - σ'.length) ≤ S'.card := by
        intro d Sd hSdS hSdcol hSdcard
        have hpref' : ∀ τ d', IsPrefixBit τ d' (σ ++ [d]) → τ ∈ dom := by
          intro τ d' ⟨r, hr⟩
          cases hrev : r.reverse with
          | nil =>
            have hr0 : r = [] := List.reverse_eq_nil_iff.mp hrev
            subst hr0
            have hEq := List.append_inj_left' hr (by simp)
            subst hEq
            exact hσ
          | cons last init =>
            have hr' : r = init.reverse ++ [last] := by
              simpa [List.reverse_cons] using congrArg List.reverse hrev
            rw [hr', ← List.cons_append, ← List.append_assoc] at hr
            have hEq := List.append_inj_left' hr (by simp)
            exact hpref τ d' ⟨init.reverse, hEq⟩
        have hcol' : ∀ τ d', IsPrefixBit τ d' (σ ++ [d]) → ∀ w ∈ Sd, c {vert τ, v, w} = d' := by
          intro τ d' ⟨r, hr⟩ w hw
          cases hrev : r.reverse with
          | nil =>
            have hr0 : r = [] := List.reverse_eq_nil_iff.mp hrev
            subst hr0
            have hEq := List.append_inj_left' hr (by simp)
            have hdEq : d' = d := by
              have := List.append_inj_right' hr (by simp)
              exact (List.cons.inj this).1.symm
            subst hEq; subst hdEq
            exact hSdcol w hw
          | cons last init =>
            have hr' : r = init.reverse ++ [last] := by
              simpa [List.reverse_cons] using congrArg List.reverse hrev
            rw [hr', ← List.cons_append, ← List.append_assoc] at hr
            have hEq := List.append_inj_left' hr (by simp)
            exact hcol τ d' ⟨init.reverse, hEq⟩ w (hSdS hw)
        obtain ⟨σ', S', h1, h2, h3, h4, h5, h6, h7⟩ :=
          ih (σ ++ [d]) Sd (by simp; omega) hpref' hcol' (by simp; exact hSdcard)
        exact ⟨σ', S', h1, Finset.Subset.trans h2 hSdS, h3, h4, h5, h6, h7⟩
      rcases hhalf with hT | hF
      · exact hstep true ST (Finset.filter_subset _ _) (fun w hw => (Finset.mem_filter.mp hw).2) hT
      · exact hstep false SF (Finset.filter_subset _ _) (fun w hw => (Finset.mem_filter.mp hw).2) hF
    · refine ⟨σ, S, hσ, Finset.Subset.refl _, by omega, hpref, hcol, ?_, hS⟩
      intro hnotT
      by_cases hnil : σ = []
      · subst hnil
        exact absurd ((mem_treeStrings_iff a b []).mpr ⟨Nat.zero_le _, Nat.zero_le _⟩) hnotT
      · obtain ⟨σ₀, d, rfl⟩ := list_exists_snoc hnil
        have hσ₀_dom : σ₀ ∈ dom := hpref σ₀ d ⟨[], by simp⟩
        have hσ₀_c := (mem_treeStrings_iff a b σ₀).mp (hdom_sub hσ₀_dom)
        have hc_not := (mem_treeStrings_iff a b (σ₀ ++ [d])).not.mp hnotT
        cases d
        · simp only [List.count_append, List.count_cons_self,
            List.count_cons_of_ne (by decide : false ≠ true), List.count_nil] at hc_not ⊢
          omega
        · simp only [List.count_append, List.count_cons_self,
            List.count_cons_of_ne (by decide : true ≠ false), List.count_nil] at hc_not ⊢
          omega

/-- Extract a monochromatic 3-uniform clique of color `d` and size `σ.count d + 2` from a leaf `σ`. -/
private lemma extract_mono_clique {α : Type*} [DecidableEq α]
    (c : Finset α → Bool) (dom : Finset (List Bool)) (vert : List Bool → α)
    (S_pool : Finset α)
    (hvert_inj : Set.InjOn vert dom)
    (hvert_pool : ∀ σ ∈ dom, ∀ w ∈ S_pool, vert σ ≠ w)
    (hdom_col : ∀ τ₁ d₁ τ₂ d₂ σ', τ₁ ∈ dom → τ₂ ∈ dom → σ' ∈ dom →
      IsPrefixBit τ₁ d₁ τ₂ → IsPrefixBit τ₂ d₂ σ' → c {vert τ₁, vert τ₂, vert σ'} = d₁)
    (hdom_pool : ∀ τ d σ', τ ∈ dom → σ' ∈ dom → IsPrefixBit τ d σ' →
      ∀ w ∈ S_pool, c {vert τ, vert σ', w} = d)
    (v w : α) (hv : v ∈ S_pool) (hw : w ∈ S_pool) (hvw : v ≠ w)
    (σ : List Bool) (d : Bool)
    (hpref : ∀ τ d', IsPrefixBit τ d' σ → τ ∈ dom)
    (hvcol : ∀ τ d', IsPrefixBit τ d' σ → c {vert τ, v, w} = d') :
    ∃ K : Finset α, K.card = σ.count d + 2 ∧ ∀ e ⊆ K, e.card = 3 → c e = d := by
  let P := prefixesWithBit d σ
  have hP_sub : P ⊆ dom := fun τ hτ => hpref τ d ((mem_prefixesWithBit_iff d σ τ).mp hτ)
  let A := P.image vert
  have hA_card : A.card = σ.count d := by
    rw [Finset.card_image_of_injOn (hvert_inj.mono hP_sub), card_prefixesWithBit]
  have hvA : v ∉ A := by
    intro h
    rcases Finset.mem_image.mp h with ⟨τ, hτ, hEq⟩
    exact hvert_pool τ (hP_sub hτ) v hv hEq
  have hwA : w ∉ A := by
    intro h
    rcases Finset.mem_image.mp h with ⟨τ, hτ, hEq⟩
    exact hvert_pool τ (hP_sub hτ) w hw hEq
  refine ⟨insert v (insert w A), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hvw, hvA]),
      Finset.card_insert_of_notMem hwA, hA_card]
  · intro e he hcard
    have htriple : ∃ x y z, x ∈ e ∧ y ∈ e ∧ z ∈ e ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ e = {x, y, z} := by
      rcases Finset.card_eq_three.mp hcard with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
      exact ⟨x, y, z, by simp, by simp, by simp, hxy, hxz, hyz, rfl⟩
    have hA_triple : ∀ τ₁ ∈ P, ∀ τ₂ ∈ P, ∀ τ₃ ∈ P, τ₁ ≠ τ₂ → τ₁ ≠ τ₃ → τ₂ ≠ τ₃ →
        c {vert τ₁, vert τ₂, vert τ₃} = d := by
      intro τ₁ h₁ τ₂ h₂ τ₃ h₃ h12 h13 h23
      have hp1 := (mem_prefixesWithBit_iff d σ τ₁).mp h₁
      have hp2 := (mem_prefixesWithBit_iff d σ τ₂).mp h₂
      have hp3 := (mem_prefixesWithBit_iff d σ τ₃).mp h₃
      have hpair : ∀ u₁ u₂ u₃, u₁ ∈ P → u₂ ∈ P → u₃ ∈ P →
          IsPrefixBit u₁ d u₂ → IsPrefixBit u₂ d u₃ →
          c {vert u₁, vert u₂, vert u₃} = d :=
        fun u₁ u₂ u₃ hu₁ hu₂ hu₃ h12' h23' =>
          hdom_col u₁ d u₂ d u₃ (hP_sub hu₁) (hP_sub hu₂) (hP_sub hu₃) h12' h23'
      rcases isPrefixBit_total_of_both hp1 hp2 h12 with h12' | h21'
      · rcases isPrefixBit_total_of_both hp2 hp3 h23 with h23' | h32'
        · exact hpair τ₁ τ₂ τ₃ h₁ h₂ h₃ h12' h23'
        · rcases isPrefixBit_total_of_both hp1 hp3 h13 with h13' | h31'
          · have : ({vert τ₁, vert τ₂, vert τ₃} : Finset α) = {vert τ₁, vert τ₃, vert τ₂} := by
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
            rw [this]; exact hpair τ₁ τ₃ τ₂ h₁ h₃ h₂ h13' h32'
          · have : ({vert τ₁, vert τ₂, vert τ₃} : Finset α) = {vert τ₃, vert τ₁, vert τ₂} := by
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
            rw [this]; exact hpair τ₃ τ₁ τ₂ h₃ h₁ h₂ h31' h12'
      · rcases isPrefixBit_total_of_both hp1 hp3 h13 with h13' | h31'
        · have : ({vert τ₁, vert τ₂, vert τ₃} : Finset α) = {vert τ₂, vert τ₁, vert τ₃} := by
            ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hpair τ₂ τ₁ τ₃ h₂ h₁ h₃ h21' h13'
        · rcases isPrefixBit_total_of_both hp2 hp3 h23 with h23' | h32'
          · have : ({vert τ₁, vert τ₂, vert τ₃} : Finset α) = {vert τ₂, vert τ₃, vert τ₁} := by
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
            rw [this]; exact hpair τ₂ τ₃ τ₁ h₂ h₃ h₁ h23' h31'
          · have : ({vert τ₁, vert τ₂, vert τ₃} : Finset α) = {vert τ₃, vert τ₂, vert τ₁} := by
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
            rw [this]; exact hpair τ₃ τ₂ τ₁ h₃ h₂ h₁ h32' h21'
    have hA_pair_pool : ∀ τ₁ ∈ P, ∀ τ₂ ∈ P, τ₁ ≠ τ₂ → ∀ u ∈ S_pool,
        c {vert τ₁, vert τ₂, u} = d := by
      intro τ₁ h₁ τ₂ h₂ h12 u hu
      have hp1 := (mem_prefixesWithBit_iff d σ τ₁).mp h₁
      have hp2 := (mem_prefixesWithBit_iff d σ τ₂).mp h₂
      rcases isPrefixBit_total_of_both hp1 hp2 h12 with h12' | h21'
      · exact hdom_pool τ₁ d τ₂ (hP_sub h₁) (hP_sub h₂) h12' u hu
      · have : ({vert τ₁, vert τ₂, u} : Finset α) = {vert τ₂, vert τ₁, u} := by
          ext x; simp [or_left_comm, or_comm]
        rw [this]
        exact hdom_pool τ₂ d τ₁ (hP_sub h₂) (hP_sub h₁) h21' u hu
    by_cases hve : v ∈ e
    · by_cases hwe : w ∈ e
      · have h1 : ((e.erase v).erase w).card = 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvw.symm, hwe⟩),
            Finset.card_erase_of_mem hve, hcard]
        obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp h1
        have hxmem : x ∈ (e.erase v).erase w := by rw [hxEq]; simp
        have hxw : x ≠ w := (Finset.mem_erase.mp hxmem).1
        have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hxmem)).1
        have hxe : x ∈ e := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxmem)
        have hxA : x ∈ A := by
          have := he hxe
          simp only [Finset.mem_insert] at this
          rcases this with rfl | rfl | h
          · exact absurd rfl hxv
          · exact absurd rfl hxw
          · exact h
        obtain ⟨τ, hτP, rfl⟩ := Finset.mem_image.mp hxA
        have heEq : e = {vert τ, v, w} := by
          ext y
          by_cases hyv : y = v
          · subst hyv; simp [hve]
          · by_cases hyw : y = w
            · subst hyw; simp [hwe]
            · constructor
              · intro hy
                have : y ∈ (e.erase v).erase w :=
                  Finset.mem_erase.mpr ⟨hyw, Finset.mem_erase.mpr ⟨hyv, hy⟩⟩
                rw [hxEq] at this
                simp [Finset.mem_singleton.mp this]
              · intro hy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                rcases hy with rfl | rfl | rfl
                · exact hxe
                · exact hve
                · exact hwe
        rw [heEq]
        exact hvcol τ d ((mem_prefixesWithBit_iff d σ τ).mp hτP)
      · have h2 : (e.erase v).card = 2 := by rw [Finset.card_erase_of_mem hve, hcard]
        obtain ⟨x, y, hxy, hEq2⟩ := Finset.card_eq_two.mp h2
        have hxA : x ∈ A := by
          have hxm : x ∈ e.erase v := by rw [hEq2]; simp
          have hxv := (Finset.mem_erase.mp hxm).1
          have hxe := Finset.mem_of_mem_erase hxm
          rcases Finset.mem_insert.mp (he hxe) with rfl | h'
          · exact absurd rfl hxv
          · rcases Finset.mem_insert.mp h' with rfl | hxA'
            · exact absurd hxe hwe
            · exact hxA'
        have hyA : y ∈ A := by
          have hym : y ∈ e.erase v := by rw [hEq2]; simp
          have hyv := (Finset.mem_erase.mp hym).1
          have hye := Finset.mem_of_mem_erase hym
          rcases Finset.mem_insert.mp (he hye) with rfl | h'
          · exact absurd rfl hyv
          · rcases Finset.mem_insert.mp h' with rfl | hyA'
            · exact absurd hye hwe
            · exact hyA'
        obtain ⟨τ₁, h₁, rfl⟩ := Finset.mem_image.mp hxA
        obtain ⟨τ₂, h₂, rfl⟩ := Finset.mem_image.mp hyA
        have heEq : e = {vert τ₁, vert τ₂, v} := by
          ext u
          by_cases huv : u = v
          · subst huv; simp [hve]
          · constructor
            · intro hu
              have : u ∈ e.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
              rw [hEq2] at this
              simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
              rcases this with rfl | rfl <;> simp
            · intro hu
              simp only [Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with rfl | rfl | rfl
              · exact Finset.mem_of_mem_erase (by rw [hEq2]; simp)
              · exact Finset.mem_of_mem_erase (by rw [hEq2]; simp)
              · exact hve
        rw [heEq]
        exact hA_pair_pool τ₁ h₁ τ₂ h₂ (fun h => hxy (congrArg vert h)) v hv
    · by_cases hwe : w ∈ e
      · have h2 : (e.erase w).card = 2 := by rw [Finset.card_erase_of_mem hwe, hcard]
        obtain ⟨x, y, hxy, hEq2⟩ := Finset.card_eq_two.mp h2
        have hxA : x ∈ A := by
          have hxm : x ∈ e.erase w := by rw [hEq2]; simp
          have hxw := (Finset.mem_erase.mp hxm).1
          have hxe := Finset.mem_of_mem_erase hxm
          rcases Finset.mem_insert.mp (he hxe) with rfl | h'
          · exact absurd hxe hve
          · rcases Finset.mem_insert.mp h' with rfl | hxA'
            · exact absurd rfl hxw
            · exact hxA'
        have hyA : y ∈ A := by
          have hym : y ∈ e.erase w := by rw [hEq2]; simp
          have hyw := (Finset.mem_erase.mp hym).1
          have hye := Finset.mem_of_mem_erase hym
          rcases Finset.mem_insert.mp (he hye) with rfl | h'
          · exact absurd hye hve
          · rcases Finset.mem_insert.mp h' with rfl | hyA'
            · exact absurd rfl hyw
            · exact hyA'
        obtain ⟨τ₁, h₁, rfl⟩ := Finset.mem_image.mp hxA
        obtain ⟨τ₂, h₂, rfl⟩ := Finset.mem_image.mp hyA
        have heEq : e = {vert τ₁, vert τ₂, w} := by
          ext u
          by_cases huw : u = w
          · subst huw; simp [hwe]
          · constructor
            · intro hu
              have : u ∈ e.erase w := Finset.mem_erase.mpr ⟨huw, hu⟩
              rw [hEq2] at this
              simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
              rcases this with rfl | rfl <;> simp
            · intro hu
              simp only [Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with rfl | rfl | rfl
              · exact Finset.mem_of_mem_erase (by rw [hEq2]; simp)
              · exact Finset.mem_of_mem_erase (by rw [hEq2]; simp)
              · exact hwe
        rw [heEq]
        exact hA_pair_pool τ₁ h₁ τ₂ h₂ (fun h => hxy (congrArg vert h)) w hw
      · rcases htriple with ⟨x, y, z, hxe, hye, hze, hxy, hxz, hyz, rfl⟩
        have hsubA : ∀ u ∈ ({x, y, z} : Finset α), u ∈ A := by
          intro u hu
          rcases Finset.mem_insert.mp (he hu) with rfl | h'
          · exact absurd hu hve
          · rcases Finset.mem_insert.mp h' with rfl | huA
            · exact absurd hu hwe
            · exact huA
        obtain ⟨τ₁, h₁, rfl⟩ := Finset.mem_image.mp (hsubA x hxe)
        obtain ⟨τ₂, h₂, rfl⟩ := Finset.mem_image.mp (hsubA y hye)
        obtain ⟨τ₃, h₃, rfl⟩ := Finset.mem_image.mp (hsubA z hze)
        exact hA_triple τ₁ h₁ τ₂ h₂ τ₃ h₃
          (fun h => hxy (congrArg vert h))
          (fun h => hxz (congrArg vert h))
          (fun h => hyz (congrArg vert h))

/-- Main recursive driver for the Conlon–Fox–Sudakov (2010) binary-tree upper bound on `R_3(s, t)`. -/
private lemma cfs_tree_ind {α : Type*} [DecidableEq α] (a b : ℕ) (c : Finset α → Bool) :
    ∀ (k : ℕ) (dom : Finset (List Bool)) (vert : List Bool → α) (pool : Finset α),
      dom ⊆ treeStrings a b →
      (treeStrings a b \ dom).card = k →
      (∀ σ ∈ dom, ∀ τ d, IsPrefixBit τ d σ → τ ∈ dom) →
      Set.InjOn vert dom →
      (∀ σ ∈ dom, ∀ w ∈ pool, vert σ ≠ w) →
      (∀ τ₁ d₁ τ₂ d₂ σ', τ₁ ∈ dom → τ₂ ∈ dom → σ' ∈ dom →
        IsPrefixBit τ₁ d₁ τ₂ → IsPrefixBit τ₂ d₂ σ' → c {vert τ₁, vert τ₂, vert σ'} = d₁) →
      (∀ τ d σ', τ ∈ dom → σ' ∈ dom → IsPrefixBit τ d σ' →
        ∀ w ∈ pool, c {vert τ, vert σ', w} = d) →
      (k + 2) * 2 ^ ((a + b) * k + (a + b + 1)) ≤ pool.card →
      (∃ S : Finset α, S.card = a + 3 ∧ ∀ e ⊆ S, e.card = 3 → c e = true) ∨
      (∃ T : Finset α, T.card = b + 3 ∧ ∀ e ⊆ T, e.card = 3 → c e = false) := by
  intro k
  induction k with
  | zero =>
    intro dom vert pool hsub hk hclosed hinj hdisj hcol hpool hcard
    have hdom_eq : dom = treeStrings a b := by
      have hemp : treeStrings a b \ dom = ∅ := Finset.card_eq_zero.mp hk
      exact Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp hemp)
    have hpool_pos : 0 < pool.card :=
      lt_of_lt_of_le (by positivity) hcard
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpool_pos
    let S₀ := pool.erase v
    have hS₀_card : 1 * 2 ^ (a + b + 1) ≤ S₀.card := by
      rw [Finset.card_erase_of_mem hv]
      have hpos2 : 0 < 2 ^ (a + b + 1) := by positivity
      simp only [Nat.mul_zero, Nat.zero_add, one_mul] at hcard ⊢
      omega
    obtain ⟨σ', S', hnotdom, hS'sub, hσ'len, hpref', hvcol', hleaf, hS'card⟩ :=
      walk_down_tree a b c dom hsub vert v 1 (a + b + 1) (le_refl _)
        (a + b + 1) [] S₀ (by simp)
        (fun τ d ⟨r, hr⟩ => by cases τ <;> simp at hr)
        (fun τ d ⟨r, hr⟩ => by cases τ <;> simp at hr)
        (by simpa using hS₀_card)
    have hS'_pos : 0 < S'.card := lt_of_lt_of_le (by positivity) hS'card
    obtain ⟨w, hwS'⟩ := Finset.card_pos.mp hS'_pos
    have hwS₀ : w ∈ S₀ := hS'sub hwS'
    have hvw : v ≠ w := (Finset.mem_erase.mp hwS₀).1.symm
    have hw_pool : w ∈ pool := Finset.mem_of_mem_erase hwS₀
    have hnotT : σ' ∉ treeStrings a b := by rwa [← hdom_eq]
    rcases hleaf hnotT with hT | hF
    · left
      obtain ⟨K, hKcard, hKcol⟩ := extract_mono_clique c dom vert pool hinj hdisj hcol hpool
        v w hv hw_pool hvw σ' true hpref' (fun τ d hp => hvcol' τ d hp w hwS')
      exact ⟨K, by omega, hKcol⟩
    · right
      obtain ⟨K, hKcard, hKcol⟩ := extract_mono_clique c dom vert pool hinj hdisj hcol hpool
        v w hv hw_pool hvw σ' false hpref' (fun τ d hp => hvcol' τ d hp w hwS')
      exact ⟨K, by omega, hKcol⟩
  | succ k ih =>
    intro dom vert pool hsub hk hclosed hinj hdisj hcol hpool hcard
    set E_rem := (a + b) * (k + 1) + (a + b + 1)
    have hE_ge : a + b + 1 ≤ E_rem := by omega
    have hpool_pos : 0 < pool.card := lt_of_lt_of_le (by positivity) hcard
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpool_pos
    let S₀ := pool.erase v
    have hS₀_card : (k + 2) * 2 ^ E_rem ≤ S₀.card := by
      rw [Finset.card_erase_of_mem hv]
      have hpos2 : 0 < 2 ^ E_rem := by positivity
      have h1 : (k + 1 + 2) * 2 ^ E_rem = (k + 2) * 2 ^ E_rem + 2 ^ E_rem := by ring
      omega
    obtain ⟨σ', S', hnotdom, hS'sub, hσ'len, hpref', hvcol', hleaf, hS'card⟩ :=
      walk_down_tree a b c dom hsub vert v (k + 2) E_rem hE_ge
        (a + b + 1) [] S₀ (by simp)
        (fun τ d ⟨r, hr⟩ => by cases τ <;> simp at hr)
        (fun τ d ⟨r, hr⟩ => by cases τ <;> simp at hr)
        (by simpa using hS₀_card)
    by_cases hσ'T : σ' ∈ treeStrings a b
    · let dom' := insert σ' dom
      let vert' : List Bool → α := fun τ => if τ = σ' then v else vert τ
      have hsub' : dom' ⊆ treeStrings a b := Finset.insert_subset hσ'T hsub
      have hk' : (treeStrings a b \ dom').card = k := by
        have hEq : treeStrings a b \ dom' = (treeStrings a b \ dom).erase σ' := by
          ext τ; simp [dom', Finset.mem_sdiff, Finset.mem_erase]; tauto
        rw [hEq, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hσ'T, hnotdom⟩), hk]
        omega
      have hclosed' : ∀ σ ∈ dom', ∀ τ d, IsPrefixBit τ d σ → τ ∈ dom' := by
        intro σ hσ τ d hp
        rcases Finset.mem_insert.mp hσ with hEq | hσd
        · subst hEq; exact Finset.mem_insert_of_mem (hpref' τ d hp)
        · exact Finset.mem_insert_of_mem (hclosed σ hσd τ d hp)
      have hinj' : Set.InjOn vert' dom' := by
        intro τ₁ h₁ τ₂ h₂ hEq
        rcases Finset.mem_insert.mp h₁ with h1eq | h1d <;>
        rcases Finset.mem_insert.mp h₂ with h2eq | h2d
        · rw [h1eq, h2eq]
        · have hne : τ₂ ≠ σ' := fun h => hnotdom (h ▸ h2d)
          simp only [vert', h1eq, hne, ↓reduceIte] at hEq
          exact absurd hEq.symm (hdisj τ₂ h2d v hv)
        · have hne : τ₁ ≠ σ' := fun h => hnotdom (h ▸ h1d)
          simp only [vert', h2eq, hne, ↓reduceIte] at hEq
          exact absurd hEq (hdisj τ₁ h1d v hv)
        · have hne1 : τ₁ ≠ σ' := fun h => hnotdom (h ▸ h1d)
          have hne2 : τ₂ ≠ σ' := fun h => hnotdom (h ▸ h2d)
          simp only [vert', hne1, hne2, ↓reduceIte] at hEq
          exact hinj h1d h2d hEq
      have hdisj' : ∀ σ ∈ dom', ∀ w ∈ S', vert' σ ≠ w := by
        intro σ hσ w hw
        have hwS₀ : w ∈ S₀ := hS'sub hw
        have hw_pool : w ∈ pool := Finset.mem_of_mem_erase hwS₀
        have hwv : w ≠ v := (Finset.mem_erase.mp hwS₀).1
        rcases Finset.mem_insert.mp hσ with hEq | hσd
        · simp [vert', hEq, hwv.symm]
        · have hne : σ ≠ σ' := fun h => hnotdom (h ▸ hσd)
          simp only [vert', hne, ↓reduceIte]
          exact hdisj σ hσd w hw_pool
      have hcol' : ∀ τ₁ d₁ τ₂ d₂ σ₂, τ₁ ∈ dom' → τ₂ ∈ dom' → σ₂ ∈ dom' →
          IsPrefixBit τ₁ d₁ τ₂ → IsPrefixBit τ₂ d₂ σ₂ →
          c {vert' τ₁, vert' τ₂, vert' σ₂} = d₁ := by
        intro τ₁ d₁ τ₂ d₂ σ₂ h₁ h₂ h₃ hp12 hp23
        have hτ₁_ne : τ₁ ≠ σ' := by
          intro hEq
          have hσ'_in : σ' ∈ dom := by
            rcases Finset.mem_insert.mp h₂ with h2eq | h2d
            · rw [hEq, h2eq] at hp12
              exact absurd (isPrefixBit_length_lt hp12) (lt_irrefl _)
            · rw [hEq] at hp12
              exact hclosed τ₂ h2d σ' d₁ hp12
          exact hnotdom hσ'_in
        have hτ₂_ne : τ₂ ≠ σ' := by
          intro hEq
          rcases Finset.mem_insert.mp h₃ with h3eq | h3d
          · rw [hEq, h3eq] at hp23
            exact absurd (isPrefixBit_length_lt hp23) (lt_irrefl _)
          · rw [hEq] at hp23
            exact hnotdom (hclosed σ₂ h3d σ' d₂ hp23)
        have hτ₁_dom : τ₁ ∈ dom := by
          rcases Finset.mem_insert.mp h₁ with h | h; exact absurd h hτ₁_ne; exact h
        have hτ₂_dom : τ₂ ∈ dom := by
          rcases Finset.mem_insert.mp h₂ with h | h; exact absurd h hτ₂_ne; exact h
        rcases Finset.mem_insert.mp h₃ with h3eq | h3d
        · simp only [vert', hτ₁_ne, hτ₂_ne, h3eq, ↓reduceIte]
          exact hpool τ₁ d₁ τ₂ hτ₁_dom hτ₂_dom hp12 v hv
        · have hσ₂_ne : σ₂ ≠ σ' := fun h => hnotdom (h ▸ h3d)
          simp only [vert', hτ₁_ne, hτ₂_ne, hσ₂_ne, ↓reduceIte]
          exact hcol τ₁ d₁ τ₂ d₂ σ₂ hτ₁_dom hτ₂_dom h3d hp12 hp23
      have hpool' : ∀ τ d σ₂, τ ∈ dom' → σ₂ ∈ dom' → IsPrefixBit τ d σ₂ →
          ∀ w ∈ S', c {vert' τ, vert' σ₂, w} = d := by
        intro τ d σ₂ hτ hσ₂ hp w hw
        have hw_pool : w ∈ pool := Finset.mem_of_mem_erase (hS'sub hw)
        have hτ_ne : τ ≠ σ' := by
          intro hEq
          rcases Finset.mem_insert.mp hσ₂ with h2eq | h2d
          · rw [hEq, h2eq] at hp
            exact absurd (isPrefixBit_length_lt hp) (lt_irrefl _)
          · rw [hEq] at hp
            exact hnotdom (hclosed σ₂ h2d σ' d hp)
        have hτ_dom : τ ∈ dom := by
          rcases Finset.mem_insert.mp hτ with h | h; exact absurd h hτ_ne; exact h
        rcases Finset.mem_insert.mp hσ₂ with h2eq | h2d
        · simp only [vert', hτ_ne, h2eq, ↓reduceIte]
          rw [h2eq] at hp
          exact hvcol' τ d hp w hw
        · have hσ₂_ne : σ₂ ≠ σ' := fun h => hnotdom (h ▸ h2d)
          simp only [vert', hτ_ne, hσ₂_ne, ↓reduceIte]
          exact hpool τ d σ₂ hτ_dom h2d hp w hw_pool
      have hS'_budget : (k + 2) * 2 ^ ((a + b) * k + (a + b + 1)) ≤ S'.card := by
        have hlen_ab : σ'.length ≤ a + b := length_le_of_mem_treeStrings hσ'T
        have hE_eq : E_rem = (a + b) * k + (a + b + 1) + (a + b) := by
          dsimp only [E_rem]; ring
        have hexp : (a + b) * k + (a + b + 1) ≤ E_rem - σ'.length := by omega
        exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp)) hS'card
      exact ih dom' vert' S' hsub' hk' hclosed' hinj' hdisj' hcol' hpool' hS'_budget
    · have hS'_pos : 0 < S'.card := lt_of_lt_of_le (by positivity) hS'card
      obtain ⟨w, hwS'⟩ := Finset.card_pos.mp hS'_pos
      have hwS₀ : w ∈ S₀ := hS'sub hwS'
      have hvw : v ≠ w := (Finset.mem_erase.mp hwS₀).1.symm
      have hw_pool : w ∈ pool := Finset.mem_of_mem_erase hwS₀
      rcases hleaf hσ'T with hT | hF
      · left
        obtain ⟨K, hKcard, hKcol⟩ := extract_mono_clique c dom vert pool hinj hdisj hcol hpool
          v w hv hw_pool hvw σ' true hpref' (fun τ d hp => hvcol' τ d hp w hwS')
        exact ⟨K, by omega, hKcol⟩
      · right
        obtain ⟨K, hKcard, hKcol⟩ := extract_mono_clique c dom vert pool hinj hdisj hcol hpool
          v w hv hw_pool hvw σ' false hpref' (fun τ d hp => hvcol' τ d hp w hwS')
        exact ⟨K, by omega, hKcol⟩

/-- **Conlon–Fox–Sudakov (2010) Vertex On-Line Binary Tree Upper Bound for `R_3(s, t)`:**
Strictly sharpens the classical Erdős–Rado (1952) bound `2 ^ choose(R_2(s-1, t-1), 2)`
(which gives `2 ^ 2 ^ (4n - O(log n))` on the diagonal) down to `2 ^ 2 ^ (2n + O(log n))`.
For all `s, t ≥ 3`, every 2-coloring of the 3-subsets of
`Fin ((choose (s + t - 4) (s - 2) + 1) * 2 ^ ((s + t - 6) * choose (s + t - 4) (s - 2) + 1))`
contains a red `s`-subset or a blue `t`-subset. -/
theorem ppl039_cfs_tree_upper_bound (s t : ℕ) (hs : 3 ≤ s) (ht : 3 ≤ t)
    (c : Finset (Fin ((Nat.choose (s + t - 4) (s - 2) + 1) *
        2 ^ ((s + t - 6) * Nat.choose (s + t - 4) (s - 2) + 1))) → Bool) :
    (∃ S : Finset (Fin ((Nat.choose (s + t - 4) (s - 2) + 1) *
        2 ^ ((s + t - 6) * Nat.choose (s + t - 4) (s - 2) + 1))),
        S.card = s ∧ ∀ e ⊆ S, e.card = 3 → c e = true) ∨
    (∃ T : Finset (Fin ((Nat.choose (s + t - 4) (s - 2) + 1) *
        2 ^ ((s + t - 6) * Nat.choose (s + t - 4) (s - 2) + 1))),
        T.card = t ∧ ∀ e ⊆ T, e.card = 3 → c e = false) := by
  set a := s - 3
  set b := t - 3
  have ha : a + 3 = s := by omega
  have hb : b + 3 = t := by omega
  have hts := card_treeStrings a b
  have h1 : a + b + 2 = s + t - 4 := by omega
  have h2 : a + 1 = s - 2 := by omega
  have h3 : a + b = s + t - 6 := by omega
  have hV : (treeStrings a b).card + 1 = Nat.choose (s + t - 4) (s - 2) := by
    rwa [h1, h2] at hts
  have hE : (a + b) * (treeStrings a b).card + (a + b + 1) =
      (s + t - 6) * Nat.choose (s + t - 4) (s - 2) + 1 := by
    rw [← hV, h3]; ring
  have hres := cfs_tree_ind a b c (treeStrings a b).card ∅ (fun _ => ⟨0, by positivity⟩)
    Finset.univ (Finset.empty_subset _) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by
      rw [Finset.card_univ, Fintype.card_fin, hE]
      have hcard_eq : (treeStrings a b).card + 2 = Nat.choose (s + t - 4) (s - 2) + 1 := by omega
      rw [hcard_eq])
  rw [ha, hb] at hres
  exact hres

/-- **Erdős–Rado (1952) / Conlon–Fox–Sudakov (2010) Double-Exponential Diagonal Upper Bound:**
For every `n ≥ 3`, every 2-coloring of the 3-element subsets of `Fin (2 ^ (2 ^ (3 * n)))`
contains a monochromatic `n`-subset, proving `R_3(n) ≤ 2 ^ (2 ^ (3 * n))`. -/
theorem ppl039_erdos_rado_double_exp_upper_bound (n : ℕ) (hn : 3 ≤ n)
    (c : Finset (Fin (2 ^ (2 ^ (3 * n)))) → Bool) :
    ∃ S : Finset (Fin (2 ^ (2 ^ (3 * n)))), S.card = n ∧
      ∃ b : Bool, ∀ e ⊆ S, e.card = 3 → c e = b := by
  set M := (Nat.choose (n + n - 4) (n - 2) + 1) *
      2 ^ ((n + n - 6) * Nat.choose (n + n - 4) (n - 2) + 1)
  have hM_le : M ≤ 2 ^ (2 ^ (3 * n)) := by
    have hch : Nat.choose (n + n - 4) (n - 2) ≤ 2 ^ (2 * n - 4) := by
      have : n + n - 4 = 2 * n - 4 := by omega
      rw [this]
      exact Nat.choose_le_two_pow _ _
    have hV1 : Nat.choose (n + n - 4) (n - 2) + 1 ≤ 2 ^ (2 * n - 3) := by
      have hpow : 2 ^ (2 * n - 3) = 2 ^ (2 * n - 4) + 2 ^ (2 * n - 4) := by
        have : 2 * n - 3 = (2 * n - 4) + 1 := by omega
        rw [this, pow_succ]; ring
      have hpos : 0 < 2 ^ (2 * n - 4) := by positivity
      omega
    have hprod : M ≤ 2 ^ ((2 * n - 3) + ((n + n - 6) * Nat.choose (n + n - 4) (n - 2) + 1)) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ hV1
    refine le_trans hprod (Nat.pow_le_pow_right (by norm_num) ?_)
    have hlin : ∀ m, 3 ≤ m → 2 * m - 2 ≤ 2 ^ m := by
      intro m hm
      induction m with
      | zero => omega
      | succ k ih =>
        by_cases hk : 3 ≤ k
        · have h1 := ih hk
          have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
          omega
        · interval_cases k <;> decide
    have hlin_n := hlin n hn
    have h1 : (2 * n - 3) + ((n + n - 6) * Nat.choose (n + n - 4) (n - 2) + 1)
        ≤ (2 * n - 2) * 2 ^ (2 * n - 4) := by
      have hmul : (n + n - 6) * Nat.choose (n + n - 4) (n - 2) ≤ (2 * n - 6) * 2 ^ (2 * n - 4) := by
        have : n + n - 6 = 2 * n - 6 := by omega
        rw [this]
        exact Nat.mul_le_mul_left _ hch
      have h2n : 2 * n - 2 ≤ 4 * 2 ^ (2 * n - 4) := by
        have hpow_le : 2 ^ n ≤ 4 * 2 ^ (2 * n - 4) := by
          have : 4 * 2 ^ (2 * n - 4) = 2 ^ (2 * n - 2) := by
            have h2 : 2 * n - 2 = (2 * n - 4) + 2 := by omega
            rw [h2, pow_add]; ring
          rw [this]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hsplit : (2 * n - 2) * 2 ^ (2 * n - 4) =
          (2 * n - 6) * 2 ^ (2 * n - 4) + 4 * 2 ^ (2 * n - 4) := by
        have : 2 * n - 2 = (2 * n - 6) + 4 := by omega
        rw [this, add_mul]
      omega
    calc (2 * n - 3) + ((n + n - 6) * Nat.choose (n + n - 4) (n - 2) + 1)
        ≤ (2 * n - 2) * 2 ^ (2 * n - 4) := h1
      _ ≤ 2 ^ n * 2 ^ (2 * n - 4) := Nat.mul_le_mul_right _ hlin_n
      _ = 2 ^ (n + (2 * n - 4)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let emb : Fin M ↪ Fin (2 ^ (2 ^ (3 * n))) :=
    ⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 hM_le⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  let c' : Finset (Fin M) → Bool := fun e => c (e.map emb)
  rcases ppl039_cfs_tree_upper_bound n n hn hn c' with ⟨S, hScard, hScol⟩ | ⟨T, hTcard, hTcol⟩
  · refine ⟨S.map emb, by rw [Finset.card_map, hScard], true, ?_⟩
    intro e he hcard
    obtain ⟨e', he'S, rfl⟩ : ∃ e' ⊆ S, e'.map emb = e := by
      refine ⟨S.filter (fun x => emb x ∈ e), Finset.filter_subset _ _, ?_⟩
      ext y
      simp only [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hxe⟩, rfl⟩; exact hxe
      · intro hy
        rcases Finset.mem_map.mp (he hy) with ⟨x, hxS, rfl⟩
        exact ⟨x, ⟨hxS, hy⟩, rfl⟩
    exact hScol e' he'S (by simpa [Finset.card_map] using hcard)
  · refine ⟨T.map emb, by rw [Finset.card_map, hTcard], false, ?_⟩
    intro e he hcard
    obtain ⟨e', he'T, rfl⟩ : ∃ e' ⊆ T, e'.map emb = e := by
      refine ⟨T.filter (fun x => emb x ∈ e), Finset.filter_subset _ _, ?_⟩
      ext y
      simp only [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hxe⟩, rfl⟩; exact hxe
      · intro hy
        rcases Finset.mem_map.mp (he hy) with ⟨x, hxT, rfl⟩
        exact ⟨x, ⟨hxT, hy⟩, rfl⟩
    exact hTcol e' he'T (by simpa [Finset.card_map] using hcard)

end CFSTreeUpperBound

/-! ### Section 5: Erdős–Hajnal Stepping-Up Lemmas (`R_3(n; 4)` & `R_4(n)`) & 16-Case Barrier -/

section SteppingUpAndBarrier

/-- **Erdős–Hajnal Stepping-Up Transfer (`k = 2 → 3`, 4 colors):**
If `Fin N` admits a 2-coloring of pairs with no monochromatic `m`-subset, then `Fin (2 ^ N)`
admits a 4-coloring of triples with no monochromatic `(m + 1)`-subset (`R_3(m + 1; 4) > 2 ^ N`). -/
theorem ppl039_stepping_up_2_to_3_four_color (N m : ℕ) (hm : 2 ≤ m)
    (φ : Finset (Fin N) → Bool)
    (hφ : ∀ S : Finset (Fin N), S.card = m → ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 2 → φ e = b) :
    ∃ c : Finset (Fin (2 ^ N)) → Fin 4,
      ∀ S : Finset (Fin (2 ^ N)), S.card = m + 1 →
        ¬ ∃ q : Fin 4, ∀ e ⊆ S, e.card = 3 → c e = q := by
  let col : Finset (Fin (2 ^ N)) → Fin 4 := fun e =>
    if h : e.card = 3 then
      let f := e.orderEmbOfFin h
      let d1 : Fin N := ⟨Nat.log 2 ((f 0).1 ^^^ (f 1).1),
        delta_lt_of_lt_two_pow (f 0).2 (f 1).2 (ne_of_lt (f.strictMono (by decide)))⟩
      let d2 : Fin N := ⟨Nat.log 2 ((f 1).1 ^^^ (f 2).1),
        delta_lt_of_lt_two_pow (f 1).2 (f 2).2 (ne_of_lt (f.strictMono (by decide)))⟩
      ⟨(if d1.1 < d2.1 then 2 else 0) + (if φ {d1, d2} then 1 else 0), by split_ifs <;> omega⟩
    else 0
  refine ⟨col, ?_⟩
  intro S hScard ⟨q, hq⟩
  set f := S.orderEmbOfFin hScard
  have hf_lt : ∀ (i j : ℕ) (_hij : i < j) (_hjm : j ≤ m), (f ⟨i, by omega⟩).1 < (f ⟨j, by omega⟩).1 := by
    intro i j hij hjm
    exact f.strictMono (show (⟨i, by omega⟩ : Fin (m + 1)) < ⟨j, by omega⟩ by exact hij)
  let δ : ℕ → Fin N := fun i =>
    if h : i < m then
      ⟨Nat.log 2 ((f ⟨i, by omega⟩).1 ^^^ (f ⟨i + 1, by omega⟩).1),
        delta_lt_of_lt_two_pow (f ⟨i, by omega⟩).2 (f ⟨i + 1, by omega⟩).2
          (ne_of_lt (hf_lt i (i + 1) (by omega) (by omega)))⟩
    else ⟨0, by
      have : 0 < N := by
        by_contra h0
        have hN0 : N = 0 := by omega
        subst hN0
        have := Finset.card_le_univ S
        rw [Fintype.card_fin] at this
        omega
      exact this⟩
  have htriple_val : ∀ (a b c : ℕ) (hab : a < b) (hbc : b < c) (hcm : c ≤ m),
      let d1 : Fin N := ⟨Nat.log 2 ((f ⟨a, by omega⟩).1 ^^^ (f ⟨b, by omega⟩).1),
        delta_lt_of_lt_two_pow (f ⟨a, by omega⟩).2 (f ⟨b, by omega⟩).2
          (ne_of_lt (hf_lt a b hab (by omega)))⟩
      let d2 : Fin N := ⟨Nat.log 2 ((f ⟨b, by omega⟩).1 ^^^ (f ⟨c, by omega⟩).1),
        delta_lt_of_lt_two_pow (f ⟨b, by omega⟩).2 (f ⟨c, by omega⟩).2
          (ne_of_lt (hf_lt b c hbc hcm))⟩
      ((if d1.1 < d2.1 then 2 else 0) + (if φ {d1, d2} then 1 else 0)) = q.1 := by
    intro a b c hab hbc hcm
    let x := f ⟨a, by omega⟩
    let y := f ⟨b, by omega⟩
    let z := f ⟨c, by omega⟩
    have hxy : x < y := hf_lt a b hab (by omega)
    have hyz : y < z := hf_lt b c hbc hcm
    let e : Finset (Fin (2 ^ N)) := {x, y, z}
    have heS : e ⊆ S := by
      intro u hu
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem S hScard _
    have hec : e.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ne_of_lt hyz]
      · simp [ne_of_lt hxy, ne_of_lt (lt_trans hxy hyz)]
    have hce := hq e heS hec
    have hord := orderEmbOfFin_triple hxy hyz (e := e) rfl hec
    have hval := congrArg Fin.val hce
    simp only [col, hec, ↓reduceDIte] at hval
    have hfn1 : (⟨Nat.log 2 ((e.orderEmbOfFin hec 0).1 ^^^ (e.orderEmbOfFin hec 1).1),
        delta_lt_of_lt_two_pow (e.orderEmbOfFin hec 0).2 (e.orderEmbOfFin hec 1).2
          (ne_of_lt ((e.orderEmbOfFin hec).strictMono (by decide)))⟩ : Fin N) =
        ⟨Nat.log 2 (x.1 ^^^ y.1), delta_lt_of_lt_two_pow x.2 y.2 (ne_of_lt hxy)⟩ := by
      apply Fin.ext
      change Nat.log 2 ((e.orderEmbOfFin hec 0).1 ^^^ (e.orderEmbOfFin hec 1).1) = Nat.log 2 (x.1 ^^^ y.1)
      rw [hord.1, hord.2.1]
    have hfn2 : (⟨Nat.log 2 ((e.orderEmbOfFin hec 1).1 ^^^ (e.orderEmbOfFin hec 2).1),
        delta_lt_of_lt_two_pow (e.orderEmbOfFin hec 1).2 (e.orderEmbOfFin hec 2).2
          (ne_of_lt ((e.orderEmbOfFin hec).strictMono (by decide)))⟩ : Fin N) =
        ⟨Nat.log 2 (y.1 ^^^ z.1), delta_lt_of_lt_two_pow y.2 z.2 (ne_of_lt hyz)⟩ := by
      apply Fin.ext
      change Nat.log 2 ((e.orderEmbOfFin hec 1).1 ^^^ (e.orderEmbOfFin hec 2).1) = Nat.log 2 (y.1 ^^^ z.1)
      rw [hord.2.1, hord.2.2]
    have hcongr : ∀ a₁ a₂ b₁ b₂ : Fin N, a₁ = a₂ → b₁ = b₂ →
        ((if a₁.1 < b₁.1 then 2 else 0) + (if φ {a₁, b₁} then 1 else 0)) =
        ((if a₂.1 < b₂.1 then 2 else 0) + (if φ {a₂, b₂} then 1 else 0)) := by
      rintro _ _ _ _ rfl rfl; rfl
    exact (hcongr _ _ _ _ hfn1 hfn2).symm.trans hval
  have hδ_ne : ∀ i, i + 1 < m → (δ i).1 ≠ (δ (i + 1)).1 := by
    intro i hi
    simp only [δ, hi, show i < m by omega, ↓reduceDIte]
    exact delta_ne_of_lt_lt (hf_lt i (i + 1) (by omega) (by omega))
      (hf_lt (i + 1) (i + 2) (by omega) (by omega))
  have hcongr2 : ∀ a₁ a₂ b₁ b₂ : Fin N, a₁ = a₂ → b₁ = b₂ →
      ((if a₁.1 < b₁.1 then 2 else 0) + (if φ {a₁, b₁} then 1 else 0)) =
      ((if a₂.1 < b₂.1 then 2 else 0) + (if φ {a₂, b₂} then 1 else 0)) := by
    rintro _ _ _ _ rfl rfl; rfl
  -- Check whether q.1 / 2 = 1 (strictly increasing) or q.1 / 2 = 0 (strictly decreasing)
  by_cases hdir : 2 ≤ q.1
  · have hinc : ∀ i, i + 1 < m → (δ i).1 < (δ (i + 1)).1 := by
      intro i hi
      have hv := htriple_val i (i + 1) (i + 2) (by omega) (by omega) (by omega)
      simp only [δ, hi, show i < m by omega, ↓reduceDIte]
      by_contra hnot
      simp only [hnot, ↓reduceIte] at hv
      split_ifs at hv <;> omega
    have hmono := strictMono_of_step (k := m) (g := fun i => (δ i).1) hinc
    let T : Finset (Fin N) := (Finset.range m).image δ
    have hinj : Set.InjOn δ (Finset.range m) := by
      intro i hi j hj hEq
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_lt (hmono i j hlt hj') (congrArg Fin.val hEq)
      · exact ne_of_gt (hmono j i hgt hi') (congrArg Fin.val hEq)
    have hTcard : T.card = m := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    apply hφ T hTcard
    refine ⟨decide (q.1 % 2 = 1), ?_⟩
    intro e he hcard
    rcases Finset.card_eq_two.mp hcard with ⟨u, v, huv, rfl⟩
    obtain ⟨a, ha, haEq⟩ := Finset.mem_image.mp (he (by simp : u ∈ ({u, v} : Finset (Fin N))))
    obtain ⟨b, hb, hbEq⟩ := Finset.mem_image.mp (he (by simp : v ∈ ({u, v} : Finset (Fin N))))
    subst haEq; subst hbEq
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have hab_ne : a ≠ b := fun h => huv (congrArg δ h)
    have hpair : ∀ i j, i < j → j < m → φ {δ i, δ j} = decide (q.1 % 2 = 1) := by
      intro i j hij hjm
      have hv := htriple_val i (i + 1) (j + 1) (by omega) (by omega) (by omega)
      have hch := delta_strictMono_chain (k := m) (x := fun t => if ht : t ≤ m then (f ⟨t, by omega⟩).1 else 0)
        (fun p r hpr hrm => by simp only [hrm, show p ≤ m by omega, ↓reduceDIte]; exact hf_lt p r hpr hrm)
        (fun p hp => by
          have hp1 : p + 1 < m := by omega
          have hp2 := hinc p hp1
          simp only [δ, hp1, show p < m by omega, ↓reduceDIte] at hp2
          simpa [show p ≤ m by omega, show p + 1 ≤ m by omega, show p + 2 ≤ m by omega] using hp2)
        (a := i + 1) (b := j + 1) (by omega) (by omega)
      simp only [show i + 1 ≤ m by omega, show j + 1 ≤ m by omega, show j + 1 - 1 = j by omega,
        show j ≤ m by omega, ↓reduceDIte] at hch
      have hd1 : (⟨Nat.log 2 ((f ⟨i, by omega⟩).1 ^^^ (f ⟨i + 1, by omega⟩).1),
          delta_lt_of_lt_two_pow (f ⟨i, by omega⟩).2 (f ⟨i + 1, by omega⟩).2
            (ne_of_lt (hf_lt i (i + 1) (by omega) (by omega)))⟩ : Fin N) = δ i := by
        apply Fin.ext; simp [δ, show i < m by omega]
      have hd2 : (⟨Nat.log 2 ((f ⟨i + 1, by omega⟩).1 ^^^ (f ⟨j + 1, by omega⟩).1),
          delta_lt_of_lt_two_pow (f ⟨i + 1, by omega⟩).2 (f ⟨j + 1, by omega⟩).2
            (ne_of_lt (hf_lt (i + 1) (j + 1) (by omega) (by omega)))⟩ : Fin N) = δ j := by
        apply Fin.ext; simp only [δ, hjm, ↓reduceDIte]; exact hch
      have hv' : ((if (δ i).1 < (δ j).1 then 2 else 0) + (if φ {δ i, δ j} then 1 else 0)) = q.1 :=
        (hcongr2 _ _ _ _ hd1 hd2).symm.trans hv
      have hlt_ij : (δ i).1 < (δ j).1 := hmono i j hij hjm
      simp only [hlt_ij, ↓reduceIte] at hv'
      cases hφv : φ {δ i, δ j}
      · simp only [hφv, Bool.false_eq_true, ↓reduceIte, add_zero] at hv'
        have hmod : q.1 % 2 = 0 := by omega
        simp [hmod]
      · simp only [hφv, ↓reduceIte] at hv'
        have hmod : q.1 % 2 = 1 := by omega
        simp [hmod]
    rcases lt_or_gt_of_ne hab_ne with hlt | hgt
    · exact hpair a b hlt hb'
    · rw [Finset.pair_comm]; exact hpair b a hgt ha'
  · have hdec : ∀ i, i + 1 < m → (δ (i + 1)).1 < (δ i).1 := by
      intro i hi
      have hv := htriple_val i (i + 1) (i + 2) (by omega) (by omega) (by omega)
      have hne := hδ_ne i hi
      have hd0 : (⟨Nat.log 2 ((f ⟨i, by omega⟩).1 ^^^ (f ⟨i + 1, by omega⟩).1),
          delta_lt_of_lt_two_pow (f ⟨i, by omega⟩).2 (f ⟨i + 1, by omega⟩).2
            (ne_of_lt (hf_lt i (i + 1) (by omega) (by omega)))⟩ : Fin N) = δ i := by
        apply Fin.ext; simp [δ, show i < m by omega]
      have hd1 : (⟨Nat.log 2 ((f ⟨i + 1, by omega⟩).1 ^^^ (f ⟨i + 2, by omega⟩).1),
          delta_lt_of_lt_two_pow (f ⟨i + 1, by omega⟩).2 (f ⟨i + 2, by omega⟩).2
            (ne_of_lt (hf_lt (i + 1) (i + 2) (by omega) (by omega)))⟩ : Fin N) = δ (i + 1) := by
        apply Fin.ext; simp [δ, hi]
      have hv' : ((if (δ i).1 < (δ (i + 1)).1 then 2 else 0) + (if φ {δ i, δ (i + 1)} then 1 else 0)) = q.1 :=
        (hcongr2 _ _ _ _ hd0 hd1).symm.trans hv
      by_contra hnot
      have hlt : (δ i).1 < (δ (i + 1)).1 := by omega
      simp only [hlt, ↓reduceIte] at hv'
      split_ifs at hv' <;> omega
    have hanti := strictAnti_of_step (k := m) (g := fun i => (δ i).1) hdec
    let T : Finset (Fin N) := (Finset.range m).image δ
    have hinj : Set.InjOn δ (Finset.range m) := by
      intro i hi j hj hEq
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_gt (hanti i j hlt hj') (congrArg Fin.val hEq)
      · exact ne_of_lt (hanti j i hgt hi') (congrArg Fin.val hEq)
    have hTcard : T.card = m := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    apply hφ T hTcard
    refine ⟨decide (q.1 % 2 = 1), ?_⟩
    intro e he hcard
    rcases Finset.card_eq_two.mp hcard with ⟨u, v, huv, rfl⟩
    obtain ⟨a, ha, haEq⟩ := Finset.mem_image.mp (he (by simp : u ∈ ({u, v} : Finset (Fin N))))
    obtain ⟨b, hb, hbEq⟩ := Finset.mem_image.mp (he (by simp : v ∈ ({u, v} : Finset (Fin N))))
    subst haEq; subst hbEq
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have hab_ne : a ≠ b := fun h => huv (congrArg δ h)
    have hpair : ∀ i j, i < j → j < m → φ {δ i, δ j} = decide (q.1 % 2 = 1) := by
      intro i j hij hjm
      have hv := htriple_val i j (j + 1) hij (by omega) (by omega)
      have hch := delta_strictAnti_chain (k := m) (x := fun t => if ht : t ≤ m then (f ⟨t, by omega⟩).1 else 0)
        (fun p r hpr hrm => by simp only [hrm, show p ≤ m by omega, ↓reduceDIte]; exact hf_lt p r hpr hrm)
        (fun p hp => by
          have hp1 : p + 1 < m := by omega
          have hp2 := hdec p hp1
          simp only [δ, hp1, show p < m by omega, ↓reduceDIte] at hp2
          simpa [show p ≤ m by omega, show p + 1 ≤ m by omega, show p + 2 ≤ m by omega] using hp2)
        (a := i) (b := j) hij (by omega)
      simp only [show i ≤ m by omega, show i + 1 ≤ m by omega, show j ≤ m by omega, ↓reduceDIte] at hch
      have hd1 : (⟨Nat.log 2 ((f ⟨i, by omega⟩).1 ^^^ (f ⟨j, by omega⟩).1),
          delta_lt_of_lt_two_pow (f ⟨i, by omega⟩).2 (f ⟨j, by omega⟩).2
            (ne_of_lt (hf_lt i j hij (by omega)))⟩ : Fin N) = δ i := by
        apply Fin.ext; simp only [δ, show i < m by omega, ↓reduceDIte]; exact hch
      have hd2 : (⟨Nat.log 2 ((f ⟨j, by omega⟩).1 ^^^ (f ⟨j + 1, by omega⟩).1),
          delta_lt_of_lt_two_pow (f ⟨j, by omega⟩).2 (f ⟨j + 1, by omega⟩).2
            (ne_of_lt (hf_lt j (j + 1) (by omega) (by omega)))⟩ : Fin N) = δ j := by
        apply Fin.ext; simp [δ, hjm]
      have hv' : ((if (δ i).1 < (δ j).1 then 2 else 0) + (if φ {δ i, δ j} then 1 else 0)) = q.1 :=
        (hcongr2 _ _ _ _ hd1 hd2).symm.trans hv
      have hnotlt : ¬ (δ i).1 < (δ j).1 := not_lt.mpr (Nat.le_of_lt (hanti i j hij hjm))
      simp only [hnotlt, ↓reduceIte, zero_add] at hv'
      cases hφv : φ {δ i, δ j}
      · simp only [hφv, Bool.false_eq_true, ↓reduceIte] at hv'
        have hmod : q.1 % 2 = 0 := by omega
        simp [hmod]
      · simp only [hφv, ↓reduceIte] at hv'
        have hmod : q.1 % 2 = 1 := by omega
        simp [hmod]
    rcases lt_or_gt_of_ne hab_ne with hlt | hgt
    · exact hpair a b hlt hb'
    · rw [Finset.pair_comm]; exact hpair b a hgt ha'

/-- **Erdős–Hajnal–Máté–Rado (1984) Double-Exponential Lower Bound for 4-Colored 3-Graphs:**
For every `n ≥ 4`, there exists a 4-coloring of the 3-element subsets of
`Fin (2 ^ (2 ^ ((n - 2) / 2)))` with no monochromatic `n`-subset, establishing
`R_3(n; 4) > 2 ^ (2 ^ ⌊(n - 2) / 2⌋)`. -/
theorem ppl039_stepping_up_four_color_r3 (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : Finset (Fin (2 ^ (2 ^ ((n - 2) / 2)))) → Fin 4,
      ∀ S : Finset (Fin (2 ^ (2 ^ ((n - 2) / 2)))), S.card = n →
        ¬ ∃ q : Fin 4, ∀ e ⊆ S, e.card = 3 → c e = q := by
  have hm : 3 ≤ n - 1 := by omega
  have hEq1 : (n - 1 - 1) / 2 = (n - 2) / 2 := rfl
  have hEq2 : n - 1 + 1 = n := by omega
  rw [← hEq1]
  obtain ⟨φ, hφ⟩ := erdos_1947_graph_lower_bound (n - 1) hm
  have h := ppl039_stepping_up_2_to_3_four_color (2 ^ ((n - 1 - 1) / 2)) (n - 1) (by omega) φ hφ
  rwa [hEq2] at h

/-- Pure combinatorial unimodality lemma: a sequence of `2 * m - 2` adjacent-distinct natural
numbers avoiding either local minima or local maxima contains a contiguous strictly monotone
block of length `m`. -/
private lemma unimodal_monotone_block (m : ℕ) (hm : 3 ≤ m) (d : ℕ → ℕ)
    (hne : ∀ i, i + 1 < 2 * m - 2 → d i ≠ d (i + 1))
    (huni : (∀ i, i + 2 < 2 * m - 2 → d (i + 1) < d i → d (i + 2) < d (i + 1)) ∨
            (∀ i, i + 2 < 2 * m - 2 → d i < d (i + 1) → d (i + 1) < d (i + 2))) :
    ∃ L, L + m ≤ 2 * m - 2 ∧
      ((∀ i, i + 1 < m → d (L + i) < d (L + i + 1)) ∨
       (∀ i, i + 1 < m → d (L + i + 1) < d (L + i))) := by
  rcases huni with hno_min | hno_max
  · by_cases hfirst : ∀ i, i + 1 < m → d i < d (i + 1)
    · exact ⟨0, by omega, Or.inl (by simpa using hfirst)⟩
    · push Not at hfirst
      obtain ⟨i₀, hi₀, hle⟩ := hfirst
      have hdrop0 : d (i₀ + 1) < d i₀ := by
        have := hne i₀ (by omega); omega
      have hdrop_all : ∀ k, i₀ + k + 1 < 2 * m - 2 → d (i₀ + k + 1) < d (i₀ + k) := by
        intro k
        induction k with
        | zero => intro _; exact hdrop0
        | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          exact hno_min (i₀ + k) (by omega) hprev
      refine ⟨i₀, by omega, Or.inr (fun j hj => hdrop_all j (by omega))⟩
  · by_cases hfirst : ∀ i, i + 1 < m → d (i + 1) < d i
    · exact ⟨0, by omega, Or.inr (by simpa using hfirst)⟩
    · push Not at hfirst
      obtain ⟨i₀, hi₀, hle⟩ := hfirst
      have hrise0 : d i₀ < d (i₀ + 1) := by
        have := hne i₀ (by omega); omega
      have hrise_all : ∀ k, i₀ + k + 1 < 2 * m - 2 → d (i₀ + k) < d (i₀ + k + 1) := by
        intro k
        induction k with
        | zero => intro _; exact hrise0
        | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          exact hno_max (i₀ + k) (by omega) hprev
      refine ⟨i₀, by omega, Or.inl (fun j hj => hrise_all j (by omega))⟩

/-- Helper combining three consecutive `ℕ` bit-difference values for `k = 3 → 4` stepping-up. -/
private def step34Color (g : ℕ → ℕ → ℕ → Bool) (d0 d1 d2 : ℕ) : Bool :=
  if (d0 < d1 ∧ d1 < d2) ∨ (d1 < d0 ∧ d2 < d1) then
    g d0 d1 d2
  else if d0 < d1 then
    true
  else
    false

/-- **Erdős–Hajnal Stepping-Up Transfer (`k = 3 → 4`, 2 colors):**
If `Fin N` admits a 2-coloring of triples with no monochromatic `m`-subset (`m ≥ 3`), then
`Fin (2 ^ N)` admits a 2-coloring of 4-element subsets with no monochromatic `(2 * m - 1)`-subset
(`R_4(2 * m - 1) > 2 ^ N`). -/
theorem ppl039_stepping_up_3_to_4_two_color (N m : ℕ) (hm : 3 ≤ m)
    (φ : Finset (Fin N) → Bool)
    (hφ : ∀ S : Finset (Fin N), S.card = m → ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 3 → φ e = b) :
    ∃ c : Finset (Fin (2 ^ N)) → Bool,
      ∀ S : Finset (Fin (2 ^ N)), S.card = 2 * m - 1 →
        ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 4 → c e = b := by
  by_cases hN0 : N = 0
  · subst hN0
    refine ⟨fun _ => false, fun S hScard _ => ?_⟩
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  let toFin : ℕ → Fin N := fun k => if h : k < N then ⟨k, h⟩ else ⟨0, hNpos⟩
  let g : ℕ → ℕ → ℕ → Bool := fun a b c => φ {toFin a, toFin b, toFin c}
  let col : Finset (Fin (2 ^ N)) → Bool := fun e =>
    if h : e.card = 4 then
      let f := e.orderEmbOfFin h
      step34Color g
        (Nat.log 2 ((f 0).1 ^^^ (f 1).1))
        (Nat.log 2 ((f 1).1 ^^^ (f 2).1))
        (Nat.log 2 ((f 2).1 ^^^ (f 3).1))
    else false
  refine ⟨col, ?_⟩
  intro S hScard ⟨b, hb⟩
  set f := S.orderEmbOfFin hScard
  let x : ℕ → ℕ := fun i => if h : i < 2 * m - 1 then (f ⟨i, h⟩).1 else 0
  have hx_lt_pow : ∀ i, i < 2 * m - 1 → x i < 2 ^ N := fun i hi => by
    simp only [x, hi, ↓reduceDIte]; exact (f ⟨i, hi⟩).2
  have hx_lt : ∀ i j, i < j → j < 2 * m - 1 → x i < x j := fun i j hij hjm => by
    simp only [x, hjm, show i < 2 * m - 1 by omega, ↓reduceDIte]
    exact f.strictMono (show (⟨i, by omega⟩ : Fin (2 * m - 1)) < ⟨j, hjm⟩ by exact hij)
  let δ : ℕ → ℕ := fun i => Nat.log 2 (x i ^^^ x (i + 1))
  have hδ_lt_N : ∀ i, i + 1 < 2 * m - 1 → δ i < N := fun i hi =>
    delta_lt_of_lt_two_pow (hx_lt_pow i (by omega)) (hx_lt_pow (i + 1) hi)
      (ne_of_lt (hx_lt i (i + 1) (by omega) hi))
  have hquad_val : ∀ i₀ i₁ i₂ i₃ : ℕ, i₀ < i₁ → i₁ < i₂ → i₂ < i₃ → i₃ < 2 * m - 1 →
      step34Color g (Nat.log 2 (x i₀ ^^^ x i₁)) (Nat.log 2 (x i₁ ^^^ x i₂))
        (Nat.log 2 (x i₂ ^^^ x i₃)) = b := by
    intro i₀ i₁ i₂ i₃ h01 h12 h23 h3
    let v0 := f ⟨i₀, by omega⟩
    let v1 := f ⟨i₁, by omega⟩
    let v2 := f ⟨i₂, by omega⟩
    let v3 := f ⟨i₃, h3⟩
    have hv01 : v0 < v1 := f.strictMono (show (⟨i₀, by omega⟩ : Fin (2 * m - 1)) < ⟨i₁, by omega⟩ by exact h01)
    have hv12 : v1 < v2 := f.strictMono (show (⟨i₁, by omega⟩ : Fin (2 * m - 1)) < ⟨i₂, by omega⟩ by exact h12)
    have hv23 : v2 < v3 := f.strictMono (show (⟨i₂, by omega⟩ : Fin (2 * m - 1)) < ⟨i₃, h3⟩ by exact h23)
    let e : Finset (Fin (2 ^ N)) := {v0, v1, v2, v3}
    have heS : e ⊆ S := by
      intro u hu
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem S hScard _
    have hec : e.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ne_of_lt hv23]
      · simp [ne_of_lt hv12, ne_of_lt (lt_trans hv12 hv23)]
      · simp [ne_of_lt hv01, ne_of_lt (lt_trans hv01 hv12),
          ne_of_lt (lt_trans hv01 (lt_trans hv12 hv23))]
    have hce := hb e heS hec
    have hord := orderEmbOfFin_quad hv01 hv12 hv23 (e := e) rfl hec
    simp only [col, hec, ↓reduceDIte] at hce
    rw [hord.1, hord.2.1, hord.2.2.1, hord.2.2.2] at hce
    have hx0 : x i₀ = v0.1 := by simp [x, v0, show i₀ < 2 * m - 1 by omega]
    have hx1 : x i₁ = v1.1 := by simp [x, v1, show i₁ < 2 * m - 1 by omega]
    have hx2 : x i₂ = v2.1 := by simp [x, v2, show i₂ < 2 * m - 1 by omega]
    have hx3 : x i₃ = v3.1 := by simp [x, v3, h3]
    rw [hx0, hx1, hx2, hx3]
    exact hce
  have hδ_ne : ∀ i, i + 1 < 2 * m - 2 → δ i ≠ δ (i + 1) := fun i hi =>
    delta_ne_of_lt_lt (hx_lt i (i + 1) (by omega) (by omega))
      (hx_lt (i + 1) (i + 2) (by omega) (by omega))
  have huni : (∀ i, i + 2 < 2 * m - 2 → δ (i + 1) < δ i → δ (i + 2) < δ (i + 1)) ∨
      (∀ i, i + 2 < 2 * m - 2 → δ i < δ (i + 1) → δ (i + 1) < δ (i + 2)) := by
    cases b with
    | true =>
      left
      intro i hi hdrop
      have hne2 : δ (i + 1) ≠ δ (i + 2) := hδ_ne (i + 1) (by omega)
      by_contra hnot
      have hrise : δ (i + 1) < δ (i + 2) := by omega
      have hq : step34Color g (δ i) (δ (i + 1)) (δ (i + 2)) = true :=
        hquad_val i (i + 1) (i + 2) (i + 3) (by omega) (by omega) (by omega) (by omega)
      unfold step34Color at hq
      have hcond1 : ¬ ((δ i < δ (i + 1) ∧ δ (i + 1) < δ (i + 2)) ∨
          (δ (i + 1) < δ i ∧ δ (i + 2) < δ (i + 1))) := by omega
      have hcond2 : ¬ (δ i < δ (i + 1)) := by omega
      rw [if_neg hcond1, if_neg hcond2] at hq
      exact Bool.noConfusion hq
    | false =>
      right
      intro i hi hrise
      have hne2 : δ (i + 1) ≠ δ (i + 2) := hδ_ne (i + 1) (by omega)
      by_contra hnot
      have hdrop : δ (i + 2) < δ (i + 1) := by omega
      have hq : step34Color g (δ i) (δ (i + 1)) (δ (i + 2)) = false :=
        hquad_val i (i + 1) (i + 2) (i + 3) (by omega) (by omega) (by omega) (by omega)
      unfold step34Color at hq
      have hcond1 : ¬ ((δ i < δ (i + 1) ∧ δ (i + 1) < δ (i + 2)) ∨
          (δ (i + 1) < δ i ∧ δ (i + 2) < δ (i + 1))) := by omega
      rw [if_neg hcond1, if_pos hrise] at hq
      exact Bool.noConfusion hq
  obtain ⟨L, hLm, hblock⟩ := unimodal_monotone_block m hm δ hδ_ne huni
  let γN : ℕ → ℕ := fun t => δ (L + t)
  let γ : ℕ → Fin N := fun t => toFin (γN t)
  have hγ_val : ∀ t, t < m → (γ t).1 = γN t := fun t ht => by
    simp [γ, toFin, γN, hδ_lt_N (L + t) (by omega)]
  let T : Finset (Fin N) := (Finset.range m).image γ
  rcases hblock with hinc | hdec
  · have hmono := strictMono_of_step (k := m) (g := γN) (fun t ht => by
      simpa [γN, Nat.add_assoc] using hinc t ht)
    have hinj : Set.InjOn γ (Finset.range m) := by
      intro i hi j hj hEq
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hv : γN i = γN j := by
        rw [← hγ_val i hi', ← hγ_val j hj', hEq]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_lt (hmono i j hlt hj') hv
      · exact ne_of_gt (hmono j i hgt hi') hv
    have hTcard : T.card = m := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    apply hφ T hTcard
    refine ⟨b, ?_⟩
    intro e he hcard
    rcases Finset.card_eq_three.mp hcard with ⟨u, v, w, huv, huw, hvw, rfl⟩
    obtain ⟨i, hi, hiEq⟩ := Finset.mem_image.mp (he (by simp : u ∈ ({u, v, w} : Finset (Fin N))))
    obtain ⟨j, hj, hjEq⟩ := Finset.mem_image.mp (he (by simp : v ∈ ({u, v, w} : Finset (Fin N))))
    obtain ⟨r, hr, hrEq⟩ := Finset.mem_image.mp (he (by simp : w ∈ ({u, v, w} : Finset (Fin N))))
    subst hiEq; subst hjEq; subst hrEq
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hr' := Finset.mem_range.mp hr
    have hij_ne : i ≠ j := fun h => huv (congrArg γ h)
    have hir_ne : i ≠ r := fun h => huw (congrArg γ h)
    have hjr_ne : j ≠ r := fun h => hvw (congrArg γ h)
    have hy_lt : ∀ p q', p < q' → q' ≤ m → x (L + p) < x (L + q') := fun p q' hpq hqm =>
      hx_lt (L + p) (L + q') (by omega) (by omega)
    have hy_inc : ∀ p, p + 2 ≤ m →
        Nat.log 2 (x (L + p) ^^^ x (L + (p + 1))) <
        Nat.log 2 (x (L + (p + 1)) ^^^ x (L + (p + 2))) := fun p hp => by
      simpa [δ, Nat.add_assoc] using hinc p (by omega)
    have hord3 : ∀ a₁ a₂ a₃, a₁ < a₂ → a₂ < a₃ → a₃ < m → φ {γ a₁, γ a₂, γ a₃} = b := by
      intro a₁ a₂ a₃ h12 h23 h3m
      have hq := hquad_val (L + a₁) (L + a₁ + 1) (L + a₂ + 1) (L + a₃ + 1)
        (by omega) (by omega) (by omega) (by omega)
      have hch1 : Nat.log 2 (x (L + a₁ + 1) ^^^ x (L + a₂ + 1)) = γN a₂ := by
        have h := delta_strictMono_chain (x := fun t => x (L + t)) hy_lt hy_inc
          (a := a₁ + 1) (b := a₂ + 1) (by omega) (by omega)
        simpa [γN, δ, Nat.add_assoc] using h
      have hch2 : Nat.log 2 (x (L + a₂ + 1) ^^^ x (L + a₃ + 1)) = γN a₃ := by
        have h := delta_strictMono_chain (x := fun t => x (L + t)) hy_lt hy_inc
          (a := a₂ + 1) (b := a₃ + 1) (by omega) (by omega)
        simpa [γN, δ, Nat.add_assoc] using h
      rw [hch1, hch2] at hq
      change step34Color g (γN a₁) (γN a₂) (γN a₃) = b at hq
      unfold step34Color at hq
      have hlt1 : γN a₁ < γN a₂ := hmono a₁ a₂ h12 (by omega)
      have hlt2 : γN a₂ < γN a₃ := hmono a₂ a₃ h23 h3m
      rw [if_pos (Or.inl ⟨hlt1, hlt2⟩)] at hq
      exact hq
    rcases lt_or_gt_of_ne hij_ne with h12 | h21
    · rcases lt_or_gt_of_ne hjr_ne with h23 | h32
      · exact hord3 i j r h12 h23 hr'
      · rcases lt_or_gt_of_ne hir_ne with h13 | h31
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ i, γ r, γ j} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 i r j h13 h32 hj'
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ r, γ i, γ j} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 r i j h31 h12 hj'
    · rcases lt_or_gt_of_ne hir_ne with h13 | h31
      · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ j, γ i, γ r} := by
          ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [this]; exact hord3 j i r h21 h13 hr'
      · rcases lt_or_gt_of_ne hjr_ne with h23 | h32
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ j, γ r, γ i} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 j r i h23 h31 hi'
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ r, γ j, γ i} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 r j i h32 h21 hi'
  · have hanti := strictAnti_of_step (k := m) (g := γN) (fun t ht => by
      simpa [γN, Nat.add_assoc] using hdec t ht)
    have hinj : Set.InjOn γ (Finset.range m) := by
      intro i hi j hj hEq
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hv : γN i = γN j := by
        rw [← hγ_val i hi', ← hγ_val j hj', hEq]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_gt (hanti i j hlt hj') hv
      · exact ne_of_lt (hanti j i hgt hi') hv
    have hTcard : T.card = m := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    apply hφ T hTcard
    refine ⟨b, ?_⟩
    intro e he hcard
    rcases Finset.card_eq_three.mp hcard with ⟨u, v, w, huv, huw, hvw, rfl⟩
    obtain ⟨i, hi, hiEq⟩ := Finset.mem_image.mp (he (by simp : u ∈ ({u, v, w} : Finset (Fin N))))
    obtain ⟨j, hj, hjEq⟩ := Finset.mem_image.mp (he (by simp : v ∈ ({u, v, w} : Finset (Fin N))))
    obtain ⟨r, hr, hrEq⟩ := Finset.mem_image.mp (he (by simp : w ∈ ({u, v, w} : Finset (Fin N))))
    subst hiEq; subst hjEq; subst hrEq
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hr' := Finset.mem_range.mp hr
    have hij_ne : i ≠ j := fun h => huv (congrArg γ h)
    have hir_ne : i ≠ r := fun h => huw (congrArg γ h)
    have hjr_ne : j ≠ r := fun h => hvw (congrArg γ h)
    have hy_lt : ∀ p q', p < q' → q' ≤ m → x (L + p) < x (L + q') := fun p q' hpq hqm =>
      hx_lt (L + p) (L + q') (by omega) (by omega)
    have hy_dec : ∀ p, p + 2 ≤ m →
        Nat.log 2 (x (L + (p + 1)) ^^^ x (L + (p + 2))) <
        Nat.log 2 (x (L + p) ^^^ x (L + (p + 1))) := fun p hp => by
      simpa [δ, Nat.add_assoc] using hdec p (by omega)
    have hord3 : ∀ a₁ a₂ a₃, a₁ < a₂ → a₂ < a₃ → a₃ < m → φ {γ a₁, γ a₂, γ a₃} = b := by
      intro a₁ a₂ a₃ h12 h23 h3m
      have hq := hquad_val (L + a₁) (L + a₂) (L + a₃) (L + a₃ + 1)
        (by omega) (by omega) (by omega) (by omega)
      have hch0 : Nat.log 2 (x (L + a₁) ^^^ x (L + a₂)) = γN a₁ := by
        have h := delta_strictAnti_chain (x := fun t => x (L + t)) hy_lt hy_dec
          (a := a₁) (b := a₂) h12 (by omega)
        simpa [γN, δ, Nat.add_assoc] using h
      have hch1 : Nat.log 2 (x (L + a₂) ^^^ x (L + a₃)) = γN a₂ := by
        have h := delta_strictAnti_chain (x := fun t => x (L + t)) hy_lt hy_dec
          (a := a₂) (b := a₃) h23 (by omega)
        simpa [γN, δ, Nat.add_assoc] using h
      rw [hch0, hch1] at hq
      change step34Color g (γN a₁) (γN a₂) (γN a₃) = b at hq
      unfold step34Color at hq
      have hgt1 : γN a₂ < γN a₁ := hanti a₁ a₂ h12 (by omega)
      have hgt2 : γN a₃ < γN a₂ := hanti a₂ a₃ h23 h3m
      rw [if_pos (Or.inr ⟨hgt1, hgt2⟩)] at hq
      exact hq
    rcases lt_or_gt_of_ne hij_ne with h12 | h21
    · rcases lt_or_gt_of_ne hjr_ne with h23 | h32
      · exact hord3 i j r h12 h23 hr'
      · rcases lt_or_gt_of_ne hir_ne with h13 | h31
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ i, γ r, γ j} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 i r j h13 h32 hj'
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ r, γ i, γ j} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 r i j h31 h12 hj'
    · rcases lt_or_gt_of_ne hir_ne with h13 | h31
      · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ j, γ i, γ r} := by
          ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [this]; exact hord3 j i r h21 h13 hr'
      · rcases lt_or_gt_of_ne hjr_ne with h23 | h32
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ j, γ r, γ i} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 j r i h23 h31 hi'
        · have : ({γ i, γ j, γ r} : Finset (Fin N)) = {γ r, γ j, γ i} := by
            ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this]; exact hord3 r j i h32 h21 hi'

/-- **Erdős–Hajnal (1972) Double-Exponential Lower Bound for 2-Colored 4-Graphs:**
For every `n ≥ 5`, there exists a 2-coloring of the 4-element subsets of
`Fin (2 ^ (2 ^ (((n - 1) / 2) * ((n - 3) / 2) / 6)))` with no monochromatic `n`-subset,
establishing `R_4(n) > 2 ^ (2 ^ Ω(n^2)) ≫ 2 ^ (2 ^ (c * n))`. -/
theorem ppl039_stepping_up_two_color_r4 (n : ℕ) (hn : 5 ≤ n) :
    ∃ c : Finset (Fin (2 ^ (2 ^ (((n - 1) / 2) * ((n - 3) / 2) / 6)))) → Bool,
      ∀ S : Finset (Fin (2 ^ (2 ^ (((n - 1) / 2) * ((n - 3) / 2) / 6)))), S.card = n →
        ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 4 → c e = b := by
  set m := (n + 1) / 2
  have hm : 3 ≤ m := by omega
  have h2m : 2 * m - 1 ≤ n := by omega
  have hm1 : m - 1 = (n - 1) / 2 := by omega
  have hm2 : m - 2 = (n - 3) / 2 := by omega
  rw [← hm1, ← hm2]
  obtain ⟨φ, hφ⟩ := ppl039_erdos_hajnal_lower_bound m hm
  obtain ⟨c, hc⟩ := ppl039_stepping_up_3_to_4_two_color
    (2 ^ ((m - 1) * (m - 2) / 6)) m hm φ hφ
  refine ⟨c, ?_⟩
  intro S hScard ⟨b, hb⟩
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq (by omega : 2 * m - 1 ≤ S.card)
  exact hc S' hS'card ⟨b, fun e he hcard => hb e (Finset.Subset.trans he hS'sub) hcard⟩

/-! #### Exact 16-Case Two-Color Stepping-Up Barrier Helpers -/

private lemma testBit_lt_of_supported {A : Finset ℕ} {x r : ℕ}
    (hsupp : ∀ j, x.testBit j = true → j ∈ A)
    (hA : ∀ j ∈ A, j < r) : x < 2 ^ r := by
  by_contra hge
  push Not at hge
  have hxne : x ≠ 0 := by
    have : 0 < 2 ^ r := by positivity
    omega
  set k := Nat.log 2 x
  have hkr : r ≤ k := Nat.le_log_of_pow_le (by norm_num) hge
  have hk_bit : x.testBit k = true := by
    have hdiv1 := div_pow_eq_one_of_bounds (Nat.pow_log_le_self 2 hxne)
      (Nat.lt_pow_succ_log_self (by norm_num) x)
    rw [Nat.testBit_eq_decide_div_mod_eq, hdiv1]; rfl
  have hkA := hsupp k hk_bit
  have := hA k hkA
  omega

private lemma xor_add_two_pow_eq {x y r : ℕ} (hx : x < 2 ^ r) (hy : y < 2 ^ r) :
    (x + 2 ^ r) ^^^ (y + 2 ^ r) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hbit : ∀ z, z < 2 ^ r → (z + 2 ^ r).testBit j = (z.testBit j != decide (j = r)) := by
    intro z hz
    have hxor : z + 2 ^ r = z ^^^ 2 ^ r := by
      apply add_eq_xor_of_and_zero
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hir : i = r
      · subst hir
        have hzf : z.testBit i = false := Nat.testBit_lt_two_pow hz
        simp [hzf]
      · simp [Ne.symm hir]
    rw [hxor, Nat.testBit_xor, Nat.testBit_two_pow]
    simp [eq_comm]
  rw [Nat.testBit_xor, Nat.testBit_xor, hbit x hx, hbit y hy]
  cases x.testBit j <;> cases y.testBit j <;> cases decide (j = r) <;> rfl

private lemma delta_lt_two_pow_add_two_pow {x y r : ℕ} (hx : x < 2 ^ r) (hy : y < 2 ^ r) :
    Nat.log 2 (x ^^^ (y + 2 ^ r)) = r := by
  have hy_lt : y + 2 ^ r < 2 ^ (r + 1) := by rw [pow_succ]; omega
  have hx_lt : x < 2 ^ (r + 1) := lt_trans hx (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hlt : x ^^^ (y + 2 ^ r) < 2 ^ (r + 1) := Nat.xor_lt_two_pow hx_lt hy_lt
  have hdiv : (x ^^^ (y + 2 ^ r)) / 2 ^ r = 1 := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt hx]
    have h1 : (y + 2 ^ r) / 2 ^ r = 1 := by
      rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hy]
    rw [h1]; rfl
  have hge : 2 ^ r ≤ x ^^^ (y + 2 ^ r) := by
    have hpos : 0 < 2 ^ r := by positivity
    have h1 : 1 * 2 ^ r ≤ x ^^^ (y + 2 ^ r) := (Nat.le_div_iff_mul_le hpos).mp (by omega)
    simpa using h1
  have h1 := Nat.le_log_of_pow_le (by norm_num) hge
  have h2 := Nat.log_lt_of_lt_pow (xor_ne_zero_of_ne (by omega)) hlt
  omega

/-- Inductive splitting-tree lemma for XOR / XNOR projections: for ANY `A : Finset ℕ` and ANY
graph coloring `φ`, there is a monochromatic set `S` of size `A.card + 1` supported on `A`. -/
private lemma xor_splitting_tree_clique (φ : Finset ℕ → Bool) (f : Bool → Bool → Bool)
    (target_L b₀ : Bool) (hL : f true target_L = b₀) (hR : f false (!target_L) = b₀) :
    ∀ (A : Finset ℕ),
      ∃ S : Finset ℕ, S.card = A.card + 1 ∧
        (∀ x ∈ S, ∀ j, x.testBit j = true → j ∈ A) ∧
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z →
          f (decide (Nat.log 2 (x ^^^ y) < Nat.log 2 (y ^^^ z)))
            (φ {Nat.log 2 (x ^^^ y), Nat.log 2 (y ^^^ z)}) = b₀) := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hA : A.Nonempty
    · let r := A.max' hA
      have hrA : r ∈ A := Finset.max'_mem A hA
      let A' := A.erase r
      have hA'_lt : ∀ j ∈ A', j < r := fun j hj =>
        lt_of_le_of_ne (Finset.le_max' A j (Finset.mem_of_mem_erase hj)) (Finset.mem_erase.mp hj).1
      let AL := A'.filter (fun i => φ {i, r} = target_L)
      let AR := A'.filter (fun i => φ {i, r} ≠ target_L)
      have hAL_ssub : AL ⊂ A := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.Subset.trans (Finset.filter_subset _ _) (Finset.erase_subset _ _), ?_⟩
        intro hEq
        have := (Finset.mem_erase.mp (Finset.mem_filter.mp (hEq ▸ hrA)).1).1
        exact this rfl
      have hAR_ssub : AR ⊂ A := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.Subset.trans (Finset.filter_subset _ _) (Finset.erase_subset _ _), ?_⟩
        intro hEq
        have := (Finset.mem_erase.mp (Finset.mem_filter.mp (hEq ▸ hrA)).1).1
        exact this rfl
      have hcard_split : AL.card + AR.card = A'.card := by
        have hun : AL ∪ AR = A' := by
          ext i; simp only [AL, AR, Finset.mem_union, Finset.mem_filter]; tauto
        have hdisj : Disjoint AL AR := by
          rw [Finset.disjoint_left]
          intro i h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        rw [← Finset.card_union_of_disjoint hdisj, hun]
      obtain ⟨L, hLcard, hLsupp, hLcol⟩ := ih AL hAL_ssub
      obtain ⟨R, hRcard, hRsupp, hRcol⟩ := ih AR hAR_ssub
      let R' := R.image (· + 2 ^ r)
      have hL_lt : ∀ x ∈ L, x < 2 ^ r := fun x hx =>
        testBit_lt_of_supported (hLsupp x hx) (fun j hj => hA'_lt j (Finset.mem_filter.mp hj).1)
      have hR_lt : ∀ y ∈ R, y < 2 ^ r := fun y hy =>
        testBit_lt_of_supported (hRsupp y hy) (fun j hj => hA'_lt j (Finset.mem_filter.mp hj).1)
      have hdisjLR : Disjoint L R' := by
        rw [Finset.disjoint_left]
        intro x hxL hxR
        rcases Finset.mem_image.mp hxR with ⟨y, _, rfl⟩
        have := hL_lt (y + 2 ^ r) hxL
        omega
      have hinj_add : Function.Injective (fun y : ℕ => y + 2 ^ r) := fun _ _ h => Nat.add_right_cancel h
      refine ⟨L ∪ R', ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisjLR, Finset.card_image_of_injective _ hinj_add,
          hLcard, hRcard]
        have hA'card : A'.card = A.card - 1 := Finset.card_erase_of_mem hrA
        have hApos : 1 ≤ A.card := Finset.card_pos.mpr hA
        omega
      · intro x hx j hbit
        rcases Finset.mem_union.mp hx with hxL | hxR'
        · exact hAL_ssub.1 (hLsupp x hxL j hbit)
        · rcases Finset.mem_image.mp hxR' with ⟨y, hyR, rfl⟩
          by_cases hjr : j = r
          · subst hjr; exact hrA
          · have hy_lt := hR_lt y hyR
            have hxor : y + 2 ^ r = y ^^^ 2 ^ r := by
              apply add_eq_xor_of_and_zero
              apply Nat.eq_of_testBit_eq; intro i
              rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
              by_cases hir : i = r
              · subst hir; simp [Nat.testBit_lt_two_pow hy_lt]
              · simp [Ne.symm hir]
            rw [hxor, Nat.testBit_xor, Nat.testBit_two_pow] at hbit
            simp only [show r ≠ j from Ne.symm hjr, decide_false, Bool.bne_false] at hbit
            exact hAR_ssub.1 (hRsupp y hyR j hbit)
      · intro x hx y hy z hz hxy hyz
        have hR'_ge : ∀ u ∈ R', 2 ^ r ≤ u := by
          intro u hu; rcases Finset.mem_image.mp hu with ⟨u₀, _, rfl⟩; omega
        rcases Finset.mem_union.mp hx with hxL | hxR' <;>
        rcases Finset.mem_union.mp hy with hyL | hyR' <;>
        rcases Finset.mem_union.mp hz with hzL | hzR'
        · exact hLcol x hxL y hyL z hzL hxy hyz
        · -- x, y ∈ L, z ∈ R'
          rcases Finset.mem_image.mp hzR' with ⟨z₀, hz₀, rfl⟩
          have hd_yz : Nat.log 2 (y ^^^ (z₀ + 2 ^ r)) = r :=
            delta_lt_two_pow_add_two_pow (hL_lt y hyL) (hR_lt z₀ hz₀)
          have hd_xy_in : Nat.log 2 (x ^^^ y) ∈ AL :=
            hLsupp y hyL _ (testBit_delta_of_lt hxy).2
          have hd_xy_lt : Nat.log 2 (x ^^^ y) < r :=
            hA'_lt _ (Finset.mem_filter.mp hd_xy_in).1
          rw [hd_yz]
          simp only [hd_xy_lt, decide_true]
          rw [(Finset.mem_filter.mp hd_xy_in).2]
          exact hL
        · exfalso; have := hL_lt z hzL; have := hR'_ge y hyR'; omega
        · -- x ∈ L, y, z ∈ R'
          rcases Finset.mem_image.mp hyR' with ⟨y₀, hy₀, rfl⟩
          rcases Finset.mem_image.mp hzR' with ⟨z₀, hz₀, rfl⟩
          have hd_xy : Nat.log 2 (x ^^^ (y₀ + 2 ^ r)) = r :=
            delta_lt_two_pow_add_two_pow (hL_lt x hxL) (hR_lt y₀ hy₀)
          have hd_yz_eq : Nat.log 2 ((y₀ + 2 ^ r) ^^^ (z₀ + 2 ^ r)) = Nat.log 2 (y₀ ^^^ z₀) := by
            rw [xor_add_two_pow_eq (hR_lt y₀ hy₀) (hR_lt z₀ hz₀)]
          have hyz₀ : y₀ < z₀ := by omega
          have hd_yz_in : Nat.log 2 (y₀ ^^^ z₀) ∈ AR :=
            hRsupp z₀ hz₀ _ (testBit_delta_of_lt hyz₀).2
          have hd_yz_lt : Nat.log 2 (y₀ ^^^ z₀) < r :=
            hA'_lt _ (Finset.mem_filter.mp hd_yz_in).1
          rw [hd_xy, hd_yz_eq]
          have hnotlt : ¬ r < Nat.log 2 (y₀ ^^^ z₀) := by omega
          simp only [hnotlt, decide_false]
          have hne_col : φ {Nat.log 2 (y₀ ^^^ z₀), r} ≠ target_L :=
            (Finset.mem_filter.mp hd_yz_in).2
          have hcol_eq : φ {r, Nat.log 2 (y₀ ^^^ z₀)} = !target_L := by
            rw [Finset.pair_comm]
            cases hc : φ {Nat.log 2 (y₀ ^^^ z₀), r} <;> cases target_L <;> simp_all
          rw [hcol_eq]
          exact hR
        · exfalso; have := hL_lt y hyL; have := hR'_ge x hxR'; omega
        · exfalso; have := hL_lt y hyL; have := hR'_ge x hxR'; omega
        · exfalso; have := hL_lt z hzL; have := hR'_ge x hxR'; omega
        · -- x, y, z ∈ R'
          rcases Finset.mem_image.mp hxR' with ⟨x₀, hx₀, rfl⟩
          rcases Finset.mem_image.mp hyR' with ⟨y₀, hy₀, rfl⟩
          rcases Finset.mem_image.mp hzR' with ⟨z₀, hz₀, rfl⟩
          rw [xor_add_two_pow_eq (hR_lt x₀ hx₀) (hR_lt y₀ hy₀),
            xor_add_two_pow_eq (hR_lt y₀ hy₀) (hR_lt z₀ hz₀)]
          exact hRcol x₀ hx₀ y₀ hy₀ z₀ hz₀ (by omega) (by omega)
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      refine ⟨{0}, by simp, ?_, ?_⟩
      · intro x hx j hbit
        simp only [Finset.mem_singleton] at hx
        subst hx; simp at hbit
      · intro x hx y hy z hz hxy
        simp only [Finset.mem_singleton] at hx hy
        omega

/-- Binary sum encoding `B ↦ ∑ i ∈ B, 2 ^ i` has bit `j` equal to `decide (j ∈ B)`. -/
private lemma testBit_sum_two_pow (B : Finset ℕ) :
    ∀ j : ℕ, (∑ i ∈ B, 2 ^ i).testBit j = decide (j ∈ B) := by
  induction B using Finset.induction_on with
  | empty => intro j; simp
  | insert a s ha ih =>
    intro j
    rw [Finset.sum_insert ha]
    have hxor : 2 ^ a + ∑ i ∈ s, 2 ^ i = (2 ^ a) ^^^ (∑ i ∈ s, 2 ^ i) := by
      apply add_eq_xor_of_and_zero
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_two_pow, ih k, Nat.zero_testBit]
      by_cases hka : a = k
      · subst hka; simp [ha]
      · simp [hka]
    rw [hxor, Nat.testBit_xor, Nat.testBit_two_pow, ih j]
    by_cases hja : j = a
    · subst hja; simp [ha]
    · simp [hja, Ne.symm hja]

private lemma sum_two_pow_lt_two_pow {B : Finset ℕ} {N : ℕ} (hB : ∀ i ∈ B, i < N) :
    ∑ i ∈ B, 2 ^ i < 2 ^ N := by
  apply testBit_lt_of_supported (A := B) _ hB
  intro j hj
  rw [testBit_sum_two_pow] at hj
  exact of_decide_eq_true hj

/-- **Exact 16-Case Two-Color Stepping-Up No-Go Theorem:**
For every `n ≥ 2`, every `N ≥ n ^ 2`, every base graph 2-coloring `φ : Finset ℕ → Bool`, and
**every** Boolean projection rule `f : Bool → Bool → Bool`, the stepped-up 2-coloring of triples
on `Fin (2 ^ N)` given by
`f (decide (Nat.log 2 (x ^^^ y) < Nat.log 2 (y ^^^ z))) (φ {Nat.log 2 (x ^^^ y), Nat.log 2 (y ^^^ z)})`
ALWAYS contains a monochromatic `n`-subset.

This formally characterizes the exact parity barrier of Erdős Problem #564: no 2-color projection
of the Erdős–Hajnal stepping-up coloring can ever beat `2 ^ (n ^ 2 - 1)`, in sharp contrast to
4-colored 3-graphs (`ppl039_stepping_up_four_color_r3`) and 2-colored 4-graphs
(`ppl039_stepping_up_two_color_r4`). -/
theorem ppl039_two_color_stepping_up_barrier (n N : ℕ) (hn : 2 ≤ n) (hN : n ^ 2 ≤ N)
    (φ : Finset ℕ → Bool) (f : Bool → Bool → Bool) :
    ∃ S : Finset (Fin (2 ^ N)), S.card = n ∧
      ∃ b : Bool, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z →
        f (decide (Nat.log 2 (x.val ^^^ y.val) < Nat.log 2 (y.val ^^^ z.val)))
          (φ {Nat.log 2 (x.val ^^^ y.val), Nat.log 2 (y.val ^^^ z.val)}) = b := by
  have hN_ge_n : n ≤ N := by nlinarith
  -- Branch 1: 8 rules constant on `dir = false`
  by_cases hfF : f false false = f false true
  · -- Strictly decreasing δ-chain: x_k = 2^N - 2^(N - k) for k = 0..n-1
    let g : ℕ → Fin (2 ^ N) := fun k =>
      ⟨2 ^ N - 2 ^ (N - k), by
        have hpos : 0 < 2 ^ (N - k) := by positivity
        have hle : 2 ^ (N - k) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega⟩
    have hg_mono : ∀ a b, a < b → b ≤ N → (g a).1 < (g b).1 := by
      intro a b hab hbN
      have h1 : 2 ^ (N - b) < 2 ^ (N - a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (N - a) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      dsimp only [g]; omega
    have hg_step : ∀ k, k < N → Nat.log 2 ((g k).1 ^^^ (g (k + 1)).1) = N - 1 - k := by
      intro k hk
      have hdiff : (g (k + 1)).1 = (g k).1 + 2 ^ (N - 1 - k) := by
        dsimp only [g]
        have hsub : N - (k + 1) = N - 1 - k := by omega
        rw [hsub]
        have h1 : 2 ^ (N - k) = 2 ^ (N - 1 - k) + 2 ^ (N - 1 - k) := by
          have : N - k = (N - 1 - k) + 1 := by omega
          rw [this, pow_succ]; ring
        have hle : 2 ^ (N - k) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle1 : 2 ^ (N - 1 - k) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hxor : (g k).1 ^^^ (g (k + 1)).1 = 2 ^ (N - 1 - k) := by
        rw [hdiff]
        have hmul : 2 ^ (N - k) ∣ (g k).1 := by
          dsimp only [g]
          have h1 : 2 ^ (N - k) ∣ 2 ^ N := Nat.pow_dvd_pow 2 (by omega)
          exact Nat.dvd_sub h1 (dvd_refl _)
        have hsum : (g k).1 + 2 ^ (N - 1 - k) = (g k).1 ^^^ 2 ^ (N - 1 - k) := by
          apply add_eq_xor_of_and_zero
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hi : N - 1 - k = i
          · subst hi
            have h0 : (g k).1.testBit (N - 1 - k) = false := by
              rcases hmul with ⟨q, hq⟩
              rw [hq]
              have hdiv : 2 ^ (N - k) * q / 2 ^ (N - 1 - k) = 2 * q := by
                have h2 : 2 ^ (N - k) = 2 ^ (N - 1 - k) * 2 := by
                  have : N - k = (N - 1 - k) + 1 := by omega
                  rw [this, pow_succ]
                rw [h2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
              rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]; simp
            simp [h0]
          · simp [hi]
        rw [hsum, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [hxor, Nat.log_pow (by norm_num)]
    let S := (Finset.range n).image g
    have hinj : Set.InjOn g (Finset.range n) := by
      intro i hi j hj hEq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_lt (hg_mono i j hlt (by have := Finset.mem_range.mp hj; omega)) (congrArg Fin.val hEq)
      · exact ne_of_gt (hg_mono j i hgt (by have := Finset.mem_range.mp hi; omega)) (congrArg Fin.val hEq)
    refine ⟨S, by rw [Finset.card_image_of_injOn hinj, Finset.card_range], f false false, ?_⟩
    intro x hx y hy z hz hxy hyz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have hc' := Finset.mem_range.mp hc
    have hab : a < b := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hba
      · exact lt_irrefl _ hxy
      · exact lt_asymm hxy (hg_mono b a hba (by omega))
    have hbc : b < c := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hcb
      · exact lt_irrefl _ hyz
      · exact lt_asymm hyz (hg_mono c b hcb (by omega))
    have hdec : ∀ i, i + 2 ≤ N →
        Nat.log 2 ((g (i + 1)).1 ^^^ (g (i + 2)).1) < Nat.log 2 ((g i).1 ^^^ (g (i + 1)).1) := by
      intro i hi; rw [hg_step i (by omega), hg_step (i + 1) (by omega)]; omega
    have h1 := delta_strictAnti_chain hg_mono hdec hab (by omega)
    have h2 := delta_strictAnti_chain hg_mono hdec hbc (by omega)
    rw [h1, h2, hg_step a (by omega), hg_step b (by omega)]
    have hnot : ¬ (N - 1 - a < N - 1 - b) := by omega
    simp only [hnot, decide_false]
    cases φ {N - 1 - a, N - 1 - b}
    · rfl
    · exact hfF.symm
  -- Branch 2: 4 remaining rules constant on `dir = true`
  · by_cases hfT : f true false = f true true
    · -- Strictly increasing δ-chain: x_0 = 0, x_{k+1} = 2^k for k = 0..n-2
      let g' : ℕ → Fin (2 ^ N) := fun k =>
        ⟨if k = 0 then 0 else 2 ^ (min (k - 1) (N - 1)), by
          split_ifs
          · positivity
          · exact Nat.pow_lt_pow_right (by norm_num) (by omega)⟩
      have hg'_val : ∀ k, k < n → (g' k).1 = if k = 0 then 0 else 2 ^ (k - 1) := by
        intro k hk
        dsimp only [g']
        split_ifs with h0
        · rfl
        · congr 1; omega
      have hg'_mono : ∀ a b, a < b → b < n → (g' a).1 < (g' b).1 := by
        intro a b hab hbn
        rw [hg'_val a (by omega), hg'_val b hbn]
        split_ifs with ha0 hb0
        · omega
        · positivity
        · omega
        · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hg'_delta : ∀ a b, a < b → b < n → Nat.log 2 ((g' a).1 ^^^ (g' b).1) = b - 1 := by
        intro a b hab hbn
        rw [hg'_val a (by omega), hg'_val b hbn]
        have hb0 : b ≠ 0 := by omega
        simp only [hb0, ↓reduceIte]
        by_cases ha0 : a = 0
        · simp [ha0, Nat.log_pow (by norm_num : 1 < 2)]
        · simp only [ha0, ↓reduceIte]
          have hlt : 2 ^ (a - 1) < 2 ^ (b - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          have hge : 2 ^ (b - 1) ≤ 2 ^ (a - 1) ^^^ 2 ^ (b - 1) := by
            have hxor_eq := delta_lt_two_pow_add_two_pow (x := 2 ^ (a - 1)) (y := 0) (r := b - 1)
              hlt (by positivity)
            simp only [Nat.zero_add] at hxor_eq
            have h1 := Nat.pow_log_le_self 2 (xor_ne_zero_of_ne (ne_of_lt hlt))
            rwa [hxor_eq] at h1
          have hhi : 2 ^ (a - 1) ^^^ 2 ^ (b - 1) < 2 ^ (b - 1 + 1) :=
            Nat.xor_lt_two_pow (lt_trans hlt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
              (Nat.pow_lt_pow_right (by norm_num) (by omega))
          have h1 := Nat.le_log_of_pow_le (by norm_num) hge
          have h2 := Nat.log_lt_of_lt_pow (xor_ne_zero_of_ne (ne_of_lt hlt)) hhi
          omega
      let S := (Finset.range n).image g'
      have hinj : Set.InjOn g' (Finset.range n) := by
        intro i hi j hj hEq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ne_of_lt (hg'_mono i j hlt (Finset.mem_range.mp hj)) (congrArg Fin.val hEq)
        · exact ne_of_gt (hg'_mono j i hgt (Finset.mem_range.mp hi)) (congrArg Fin.val hEq)
      refine ⟨S, by rw [Finset.card_image_of_injOn hinj, Finset.card_range], f true false, ?_⟩
      intro x hx y hy z hz hxy hyz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      have hc' := Finset.mem_range.mp hc
      have hab : a < b := by
        by_contra hge
        rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hba
        · exact lt_irrefl _ hxy
        · exact lt_asymm hxy (hg'_mono b a hba ha')
      have hbc : b < c := by
        by_contra hge
        rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hcb
        · exact lt_irrefl _ hyz
        · exact lt_asymm hyz (hg'_mono c b hcb hb')
      rw [hg'_delta a b hab hb', hg'_delta b c hbc hc']
      have hlt : b - 1 < c - 1 := by omega
      simp only [hlt, decide_true]
      cases φ {b - 1, c - 1}
      · rfl
      · exact hfT.symm
    -- Remaining 4 rules: f(F, F) ≠ f(F, T) and f(T, F) ≠ f(T, T)
    · by_cases hxor : f true true = f false false
      · -- Branch 3a: XNOR (`f true true = f false false`) -> splitting-tree gives size N + 1 ≥ n!
        obtain ⟨S₀, hS₀card, hS₀supp, hS₀col⟩ :=
          xor_splitting_tree_clique φ f true (f true true) rfl hxor.symm (Finset.range N)
        have hS₀_lt : ∀ x ∈ S₀, x < 2 ^ N := fun x hx =>
          testBit_lt_of_supported (hS₀supp x hx) (fun j hj => Finset.mem_range.mp hj)
        obtain ⟨S₁, hS₁sub, hS₁card⟩ := Finset.exists_subset_card_eq
          (by rw [hS₀card, Finset.card_range]; omega : n ≤ S₀.card)
        let S : Finset (Fin (2 ^ N)) := S₁.attach.image (fun x => ⟨x.1, hS₀_lt x.1 (hS₁sub x.2)⟩)
        have hinj : Function.Injective (fun x : {x // x ∈ S₁} => (⟨x.1, hS₀_lt x.1 (hS₁sub x.2)⟩ : Fin (2 ^ N))) :=
          fun a b h => Subtype.ext (congrArg Fin.val h)
        refine ⟨S, by rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hS₁card],
          f true true, ?_⟩
        intro x hx y hy z hz hxy hyz
        rcases Finset.mem_image.mp hx with ⟨⟨x₀, hx₀⟩, _, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨⟨y₀, hy₀⟩, _, rfl⟩
        rcases Finset.mem_image.mp hz with ⟨⟨z₀, hz₀⟩, _, rfl⟩
        exact hS₀col x₀ (hS₁sub hx₀) y₀ (hS₁sub hy₀) z₀ (hS₁sub hz₀) hxy hyz
      · by_cases hxnor : f true false = f false true
        · -- Branch 3b: XOR (`f true false = f false true`) -> splitting-tree gives size N + 1 ≥ n!
          obtain ⟨S₀, hS₀card, hS₀supp, hS₀col⟩ :=
            xor_splitting_tree_clique φ f false (f true false) rfl hxnor.symm (Finset.range N)
          have hS₀_lt : ∀ x ∈ S₀, x < 2 ^ N := fun x hx =>
            testBit_lt_of_supported (hS₀supp x hx) (fun j hj => Finset.mem_range.mp hj)
          obtain ⟨S₁, hS₁sub, hS₁card⟩ := Finset.exists_subset_card_eq
            (by rw [hS₀card, Finset.card_range]; omega : n ≤ S₀.card)
          let S : Finset (Fin (2 ^ N)) := S₁.attach.image (fun x => ⟨x.1, hS₀_lt x.1 (hS₁sub x.2)⟩)
          have hinj : Function.Injective (fun x : {x // x ∈ S₁} => (⟨x.1, hS₀_lt x.1 (hS₁sub x.2)⟩ : Fin (2 ^ N))) :=
            fun a b h => Subtype.ext (congrArg Fin.val h)
          refine ⟨S, by rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hS₁card],
            f true false, ?_⟩
          intro x hx y hy z hz hxy hyz
          rcases Finset.mem_image.mp hx with ⟨⟨x₀, hx₀⟩, _, rfl⟩
          rcases Finset.mem_image.mp hy with ⟨⟨y₀, hy₀⟩, _, rfl⟩
          rcases Finset.mem_image.mp hz with ⟨⟨z₀, hz₀⟩, _, rfl⟩
          exact hS₀col x₀ (hS₁sub hx₀) y₀ (hS₁sub hy₀) z₀ (hS₁sub hz₀) hxy hyz
        · -- Branch 4: Remaining 2 rules are `dir`-independent (`f true c = f false c` for all `c`)!
          have hindep : ∀ d c, f d c = f true c := by
            intro d c
            cases d <;> cases c
            · cases h00 : f false false <;> cases h01 : f false true <;>
              cases h10 : f true false <;> cases h11 : f true true <;> simp_all
            · cases h00 : f false false <;> cases h01 : f false true <;>
              cases h10 : f true false <;> cases h11 : f true true <;> simp_all
            · rfl
            · rfl
          set m := Nat.clog 2 n
          have hm1 : 1 ≤ m := by
            have : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
            omega
          have hn_le_2m : n ≤ 2 ^ m := Nat.le_pow_clog (by norm_num) n
          have h2m1_lt : 2 ^ (m - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
          have hchoose_le : Nat.choose (m + m - 2) (m - 1) ≤ N := by
            have h1 : Nat.choose (m + m - 2) (m - 1) ≤ 2 ^ (m + m - 2) := Nat.choose_le_two_pow _ _
            have h2 : 2 ^ (m + m - 2) = (2 ^ (m - 1)) ^ 2 := by
              rw [sq, ← pow_add]; congr 1; omega
            have h3 : (2 ^ (m - 1)) ^ 2 < n ^ 2 := Nat.pow_lt_pow_left h2m1_lt (by norm_num)
            omega
          have hes := erdos_szekeres_graph (m + m) m m rfl hm1 hm1 (Finset.range N)
            (by rw [Finset.card_range]; exact hchoose_le) φ
          have hsubcube : ∀ (A : Finset ℕ) (c₀ : Bool),
              A ⊆ Finset.range N → A.card = m → (∀ e ⊆ A, e.card = 2 → φ e = c₀) →
              ∃ S : Finset (Fin (2 ^ N)), S.card = n ∧
                ∃ b : Bool, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z →
                  f (decide (Nat.log 2 (x.val ^^^ y.val) < Nat.log 2 (y.val ^^^ z.val)))
                    (φ {Nat.log 2 (x.val ^^^ y.val), Nat.log 2 (y.val ^^^ z.val)}) = b := by
            intro A c₀ hA_sub hAcard hAcol
            let Q : Finset (Fin (2 ^ N)) :=
              A.powerset.attach.image (fun B =>
                ⟨∑ i ∈ B.1, 2 ^ i, sum_two_pow_lt_two_pow
                  (fun i hi => Finset.mem_range.mp (hA_sub (Finset.mem_powerset.mp B.2 hi)))⟩)
            have hinjQ : Function.Injective (fun B : {B // B ∈ A.powerset} =>
                (⟨∑ i ∈ B.1, 2 ^ i, sum_two_pow_lt_two_pow
                  (fun i hi => Finset.mem_range.mp (hA_sub (Finset.mem_powerset.mp B.2 hi)))⟩ : Fin (2 ^ N))) := by
              intro B₁ B₂ hEq
              apply Subtype.ext
              ext j
              have hval := congrArg (fun u : Fin (2 ^ N) => u.val.testBit j) hEq
              simp only [testBit_sum_two_pow, decide_eq_decide] at hval
              exact hval
            have hQcard : Q.card = 2 ^ m := by
              rw [Finset.card_image_of_injective _ hinjQ, Finset.card_attach,
                Finset.card_powerset, hAcard]
            obtain ⟨S, hSQ, hScard⟩ := Finset.exists_subset_card_eq (by omega : n ≤ Q.card)
            refine ⟨S, hScard, f true c₀, ?_⟩
            intro x hx y hy z hz hxy hyz
            rcases Finset.mem_image.mp (hSQ hy) with ⟨⟨By, hBy⟩, _, hyEq⟩
            rcases Finset.mem_image.mp (hSQ hz) with ⟨⟨Bz, hBz⟩, _, hzEq⟩
            have hd1_in : Nat.log 2 (x.val ^^^ y.val) ∈ A := by
              have hyval : y.val = ∑ i ∈ By, 2 ^ i := congrArg Fin.val hyEq.symm
              have hb : (∑ i ∈ By, 2 ^ i).testBit (Nat.log 2 (x.val ^^^ y.val)) = true :=
                hyval ▸ (testBit_delta_of_lt hxy).2
              rw [testBit_sum_two_pow, decide_eq_true_eq] at hb
              exact Finset.mem_powerset.mp hBy hb
            have hd2_in : Nat.log 2 (y.val ^^^ z.val) ∈ A := by
              have hzval : z.val = ∑ i ∈ Bz, 2 ^ i := congrArg Fin.val hzEq.symm
              have hb : (∑ i ∈ Bz, 2 ^ i).testBit (Nat.log 2 (y.val ^^^ z.val)) = true :=
                hzval ▸ (testBit_delta_of_lt hyz).2
              rw [testBit_sum_two_pow, decide_eq_true_eq] at hb
              exact Finset.mem_powerset.mp hBz hb
            have hne_d : Nat.log 2 (x.val ^^^ y.val) ≠ Nat.log 2 (y.val ^^^ z.val) :=
              delta_ne_of_lt_lt hxy hyz
            have hpair_sub : ({Nat.log 2 (x.val ^^^ y.val), Nat.log 2 (y.val ^^^ z.val)} : Finset ℕ) ⊆ A := by
              intro u hu
              simp only [Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with rfl | rfl <;> assumption
            have hpair_card : ({Nat.log 2 (x.val ^^^ y.val), Nat.log 2 (y.val ^^^ z.val)} : Finset ℕ).card = 2 :=
              Finset.card_pair hne_d
            rw [hindep, hAcol _ hpair_sub hpair_card]
          rcases hes with ⟨A, hAsub, hAcard, hAcol⟩ | ⟨A, hAsub, hAcard, hAcol⟩
          · exact hsubcube A true hAsub hAcard hAcol
          · exact hsubcube A false hAsub hAcard hAcol

end SteppingUpAndBarrier

/-! ### Section 6: Exact Witness `R_3(4) > 12` (Zero `native_decide`) -/

section ExactWitnessR34

/-- Direct ordered triple 2-coloring on `Fin 12` with zero monochromatic 4-subsets
(matching Isbell 1969 / McKay–Radziszowski 1991 `R_3(4) = 13`), using pure `Nat.beq` for
millisecond kernel verification without `native_decide`. -/
private def col12Ord (a b c : ℕ) : Bool :=
  match a, b with
  | 0, 1 => c == 4 || c == 5 || c == 6 || c == 10
  | 0, 2 => c == 3 || c == 4 || c == 6 || c == 8 || c == 9 || c == 11
  | 0, 3 => c == 5 || c == 8 || c == 9 || c == 10
  | 0, 4 => c == 6 || c == 7 || c == 8
  | 0, 5 => c == 6 || c == 9
  | 0, 6 => c == 10 || c == 11
  | 0, 7 => c == 8 || c == 9 || c == 10 || c == 11
  | 0, 8 => c == 10
  | 0, 9 => c == 11
  | 0, 10 => c == 11
  | 1, 2 => c == 3 || c == 4 || c == 6 || c == 7 || c == 8
  | 1, 3 => c == 4 || c == 5 || c == 7 || c == 11
  | 1, 4 => c == 5 || c == 8
  | 1, 5 => c == 9 || c == 11
  | 1, 6 => c == 7 || c == 9
  | 1, 7 => c == 10 || c == 11
  | 1, 8 => c == 9 || c == 10 || c == 11
  | 1, 9 => c == 11
  | 1, 10 => c == 11
  | 2, 3 => c == 5 || c == 6 || c == 10
  | 2, 4 => c == 7 || c == 9 || c == 11
  | 2, 5 => c == 6 || c == 7 || c == 9 || c == 10
  | 2, 6 => c == 8
  | 2, 7 => c == 8 || c == 10 || c == 11
  | 2, 8 => c == 9
  | 2, 9 => c == 10
  | 2, 10 => c == 11
  | 3, 4 => c == 6 || c == 8 || c == 11
  | 3, 5 => c == 7 || c == 8
  | 3, 6 => c == 7 || c == 8 || c == 10
  | 3, 7 => c == 9 || c == 10
  | 3, 8 => c == 11
  | 3, 9 => c == 10 || c == 11
  | 4, 5 => c == 8 || c == 9 || c == 10 || c == 11
  | 4, 6 => c == 7 || c == 10 || c == 11
  | 4, 7 => c == 9 || c == 10
  | 4, 8 => c == 10
  | 4, 9 => c == 10 || c == 11
  | 5, 6 => c == 8 || c == 9 || c == 10 || c == 11
  | 5, 7 => c == 8 || c == 9
  | 5, 8 => c == 11
  | 5, 10 => c == 11
  | 6, 7 => c == 9 || c == 11
  | 6, 8 => c == 9 || c == 10
  | 6, 9 => c == 11
  | 7, 8 => c == 11
  | 8, 9 => c == 10
  | 9, 10 => c == 11
  | _, _ => false

private def checkQuad12 (a b c d : ℕ) : Bool :=
  let c1 := col12Ord a b c
  let c2 := col12Ord a b d
  let c3 := col12Ord a c d
  let c4 := col12Ord b c d
  !(c1 == c2 && c1 == c3 && c1 == c4)

private def allIco (p : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, k + 1 => p lo && allIco p (lo + 1) k

private lemma allIco_true (p : ℕ → Bool) : ∀ k lo x, allIco p lo k = true → lo ≤ x → x < lo + k → p x = true
  | 0, _, _, _, h1, h2 => by omega
  | k + 1, lo, x, h, h1, h2 => by
    simp only [allIco, Bool.and_eq_true] at h
    by_cases hxeq : x = lo
    · subst hxeq; exact h.1
    · exact allIco_true p k (lo + 1) x h.2 (by omega) (by omega)

private def quads12ForA (a : ℕ) : Bool :=
  allIco (fun b =>
    allIco (fun c =>
      allIco (fun d => checkQuad12 a b c d) (c + 1) (11 - c))
      (b + 1) (10 - b))
    (a + 1) (9 - a)

private lemma quads12ForA_0 : quads12ForA 0 = true := by decide
private lemma quads12ForA_1 : quads12ForA 1 = true := by decide
private lemma quads12ForA_2 : quads12ForA 2 = true := by decide
private lemma quads12ForA_3 : quads12ForA 3 = true := by decide
private lemma quads12ForA_4 : quads12ForA 4 = true := by decide
private lemma quads12ForA_5 : quads12ForA 5 = true := by decide
private lemma quads12ForA_6 : quads12ForA 6 = true := by decide
private lemma quads12ForA_7 : quads12ForA 7 = true := by decide
private lemma quads12ForA_8 : quads12ForA 8 = true := by decide

private lemma checkQuad12_of_lt {a b c d : ℕ} (ha : a < 12) (hb : b < 12) (hc : c < 12)
    (hd : d < 12) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    checkQuad12 a b c d = true := by
  have ha9 : a < 9 := by omega
  have hA : quads12ForA a = true := by
    interval_cases a
    · exact quads12ForA_0
    · exact quads12ForA_1
    · exact quads12ForA_2
    · exact quads12ForA_3
    · exact quads12ForA_4
    · exact quads12ForA_5
    · exact quads12ForA_6
    · exact quads12ForA_7
    · exact quads12ForA_8
  have hB := allIco_true _ (9 - a) (a + 1) b hA (by omega) (by omega)
  have hC := allIco_true _ (10 - b) (b + 1) c hB (by omega) (by omega)
  exact allIco_true _ (11 - c) (c + 1) d hC (by omega) (by omega)

/-- **Exact Small-`n` Witness `R_3(4) > 12` (Isbell 1969 / McKay–Radziszowski 1991):**
There exists a 2-coloring of the 3-element subsets of `Fin 12` with no monochromatic 4-subset,
verified directly in the Lean 4 kernel with zero `native_decide`. -/
theorem ppl039_r3_four_gt_twelve :
    ∃ c : Finset (Fin 12) → Bool,
      ∀ S : Finset (Fin 12), S.card = 4 →
        ¬ ∃ b : Bool, ∀ e ⊆ S, e.card = 3 → c e = b := by
  let col : Finset (Fin 12) → Bool := fun e =>
    if h : e.card = 3 then
      let f := e.orderEmbOfFin h
      col12Ord (f 0).1 (f 1).1 (f 2).1
    else false
  refine ⟨col, ?_⟩
  intro S hScard ⟨col_val, hmono⟩
  set f := S.orderEmbOfFin hScard
  let a := f 0
  let b := f 1
  let c := f 2
  let d := f 3
  have hab : a < b := f.strictMono (by decide)
  have hbc : b < c := f.strictMono (by decide)
  have hcd : c < d := f.strictMono (by decide)
  have htri : ∀ x y z : Fin 12, x ∈ S → y ∈ S → z ∈ S → x < y → y < z →
      col12Ord x.1 y.1 z.1 = col_val := by
    intro x y z hx hy hz hxy hyz
    let e : Finset (Fin 12) := {x, y, z}
    have heS : e ⊆ S := by
      intro u hu
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hec : e.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ne_of_lt hyz]
      · simp [ne_of_lt hxy, ne_of_lt (lt_trans hxy hyz)]
    have hce := hmono e heS hec
    have hord := orderEmbOfFin_triple hxy hyz rfl hec
    simp only [col, hec, ↓reduceDIte] at hce
    rw [hord.1, hord.2.1, hord.2.2] at hce
    exact hce
  have haS : a ∈ S := Finset.orderEmbOfFin_mem S hScard 0
  have hbS : b ∈ S := Finset.orderEmbOfFin_mem S hScard 1
  have hcS : c ∈ S := Finset.orderEmbOfFin_mem S hScard 2
  have hdS : d ∈ S := Finset.orderEmbOfFin_mem S hScard 3
  have hc1 := htri a b c haS hbS hcS hab hbc
  have hc2 := htri a b d haS hbS hdS hab (lt_trans hbc hcd)
  have hc3 := htri a c d haS hcS hdS (lt_trans hab hbc) hcd
  have hc4 := htri b c d hbS hcS hdS hbc hcd
  have hok := checkQuad12_of_lt a.2 b.2 c.2 d.2 hab hbc hcd
  simp only [checkQuad12, hc1, hc2, hc3, hc4, beq_self_eq_true, Bool.and_self, Bool.not_true] at hok
  exact Bool.noConfusion hok

end ExactWitnessR34

end PPL039
