/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import RHDirect.Arith4Ext_LargeSieveDiophantine

set_option linter.unusedSectionVars false

/-!
# PPL 034 — Kimberling Open Problem #23: Homogeneous Linear Recurrences in Beatty Sequences

**Problem (PPL 034 / Kimberling Unsolved Problem #23, $50, OPEN):**
Characterize the real numbers `r > 1` whose Beatty sequence `B_r = {⌊n r⌋ : n ≥ 1}` contains
a strictly increasing subsequence satisfying a nontrivial homogeneous linear recurrence with
integer constant coefficients.

**Honest Scope:**
PPL 034 remains OPEN in full generality. This file formalizes 100%-unconditional structural,
positive, negative, topological, and transcendence results with pure-Mathlib public signatures
(`0` custom/private definitions in any public theorem signature, `0` `sorry`, `0` custom axioms):

1. **Section 1 — Beatty–Rayleigh Complementarity, Sturmian Gaps, Fractional-Part Law & Density:**
   - Strict monotonicity (`Nat.floor` and `Int.floor`), exact Sturmian gap characterization and
     dichotomy, universal fractional-part membership law `m ∈ B_r ↔ Int.fract (-m / r) < 1 / r`,
     full Beatty–Rayleigh complementarity partition (`1 / r + 1 / s = 1`, `Irrational r`),
     exact `O(1)` counting bounds, and exact asymptotic density `1 / r`.
2. **Section 2 — Complete Rational vs. Irrational Arithmetic-Progression Classification:**
   - Every rational `r > 1` contains an infinite arithmetic progression `c k` (and order-2
     recurrence `u (k + 2) = 2 u (k + 1) - u k`).
   - Every irrational `r > 1` contains NO infinite arithmetic progression `{c k + d : k ≥ 1}` of
     ANY step `c ≥ 1` (and misses every AP infinitely often), proved unconditionally via
     `Arith4Ext.LargeSieveDiophantine.kronecker_dense_fract`.
   - Complete `↔` classification: `B_r` contains an infinite AP iff `r` is rational.
3. **Section 3 — Quadratic Pisot Numbers, Metallic Means, Golden Ratio & Topological Density:**
   - General Quadratic Pisot Theorem: EVERY quadratic Pisot number `r > 1` (`r^2 = a r + b`,
     `|a - r| < 1`) has a strictly increasing order-2 homogeneous linear recurrence in `B_r`.
   - Explicit instantiations for the golden ratio `φ` (even-Fibonacci order-2 recurrence AND
     Wythoff order-4 recurrence), all metallic means `r_m = (m + √(m^2 + 4)) / 2` (`m ≥ 1`),
     and all positive-conjugate quadratic Pisot units `ρ_a = (a + √(a^2 - 4)) / 2` (`a ≥ 3`).
   - Sharp Conjugate-Sign Obstruction: for EVERY metallic mean `r_m` (including `φ`), `B_{r_m}`
     contains NO nonzero sequence satisfying the unbisected recurrence `u(k+2) = m u(k+1) + u(k)`.
   - Scaling invariance `B_{q r} ⊆ B_r`, rational-denominator quadratic Pisot numbers, and
     **topological density** in `(1, ∞)` (and infinitude) of irrational solutions to PPL 034.
4. **Section 4 — Uncountable Cantor Family & Explicit Transcendental Solution:**
   - Exact base-`b` geometric progression characterization `b^k ∈ B_r`.
   - Uncountable Cantor family of real `r ∈ (1, 3/2]` whose Beatty sequence contains `{4^k}`
     (order-1 homogeneous linear recurrence `u(k + 1) = 4 u(k)`).
   - Explicit transcendental real `r > 1` (`r = (1 - ∑_{n=0}^∞ 4^{-(n+1)!})^{-1}`) whose Beatty
     sequence contains `{4^k}`, proved via `Arith4Ext.LargeSieveDiophantine.transcendental_of_liouville_approx`.
5. **Section 5 — General Arbitrary-Order Structural Criteria:**
   - Exact fractional-part reformulation and error-recurrence criterion for order-`d` recurrences,
     plus a general Pisot-type sufficient convergence criterion (`e_k → 0`, `e_k ≥ 0`).
-/

open Finset Filter
open scoped BigOperators

namespace PPL034

noncomputable section

/-! ## Section 1: Beatty–Rayleigh Complementarity, Sturmian Gap Laws, & Exact Density -/

/-- For every real `r ≥ 1`, the Beatty sequence `n ↦ ⌊n r⌋₊` is strictly increasing on `ℕ`. -/
theorem ppl034_beatty_strictMono {r : ℝ} (hr : 1 ≤ r) :
    StrictMono (fun n : ℕ => Nat.floor ((n : ℝ) * r)) := by
  intro m n hmn
  have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
  have hm0 : 0 ≤ (m : ℝ) * r := by positivity
  have h1 : (Nat.floor ((m : ℝ) * r) : ℝ) + 1 ≤ (n : ℝ) * r := by
    have hfl : (Nat.floor ((m : ℝ) * r) : ℝ) ≤ (m : ℝ) * r := Nat.floor_le hm0
    nlinarith
  have h2 : Nat.floor ((m : ℝ) * r) + 1 ≤ Nat.floor ((n : ℝ) * r) := by
    rw [Nat.le_floor_iff (by positivity)]
    push_cast
    exact h1
  dsimp only
  omega

/-- For every real `r ≥ 1`, the integer-indexed Beatty sequence `n ↦ ⌊n r⌋` is strictly
increasing on `ℤ`. -/
theorem ppl034_beatty_int_strictMono {r : ℝ} (hr : 1 ≤ r) :
    StrictMono (fun n : ℤ => Int.floor ((n : ℝ) * r)) := by
  intro m n hmn
  have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
  have hfl : (Int.floor ((m : ℝ) * r) : ℝ) ≤ (m : ℝ) * r := Int.floor_le _
  have h1 : ((Int.floor ((m : ℝ) * r) + 1 : ℤ) : ℝ) ≤ (n : ℝ) * r := by
    push_cast; nlinarith
  have h2 : Int.floor ((m : ℝ) * r) + 1 ≤ Int.floor ((n : ℝ) * r) := Int.le_floor.mpr h1
  dsimp only
  omega

/-- **Exact Sturmian Gap Law (`Nat.floor`):** for `r ≥ 0` and `n : ℕ`, the consecutive Beatty gap
`⌊(n + 1) r⌋₊ - ⌊n r⌋₊` equals `⌊r⌋₊` iff `fract(n r) + fract(r) < 1`, and equals `⌊r⌋₊ + 1`
iff `1 ≤ fract(n r) + fract(r)`. -/
theorem ppl034_beatty_gap_iff {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (Nat.floor (((n + 1 : ℕ) : ℝ) * r) - Nat.floor ((n : ℝ) * r) = Nat.floor r ↔
        Int.fract ((n : ℝ) * r) + Int.fract r < 1) ∧
    (Nat.floor (((n + 1 : ℕ) : ℝ) * r) - Nat.floor ((n : ℝ) * r) = Nat.floor r + 1 ↔
        1 ≤ Int.fract ((n : ℝ) * r) + Int.fract r) := by
  have hnr_nn : 0 ≤ (n : ℝ) * r := by positivity
  have hnr1_nn : 0 ≤ ((n + 1 : ℕ) : ℝ) * r := by positivity
  have hfl_nr : (Int.floor ((n : ℝ) * r) : ℝ) = (Nat.floor ((n : ℝ) * r) : ℝ) := by
    have h : Int.floor ((n : ℝ) * r) = (Nat.floor ((n : ℝ) * r) : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by exact_mod_cast Nat.floor_le hnr_nn,
        by exact_mod_cast Nat.lt_floor_add_one _⟩
    exact_mod_cast h
  have hfl_r : (Int.floor r : ℝ) = (Nat.floor r : ℝ) := by
    have h : Int.floor r = (Nat.floor r : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by exact_mod_cast Nat.floor_le hr,
        by exact_mod_cast Nat.lt_floor_add_one _⟩
    exact_mod_cast h
  have hdecomp : ((n + 1 : ℕ) : ℝ) * r =
      ((Nat.floor ((n : ℝ) * r) + Nat.floor r : ℕ) : ℝ) +
        (Int.fract ((n : ℝ) * r) + Int.fract r) := by
    have h1 : (n : ℝ) * r = (Int.floor ((n : ℝ) * r) : ℝ) + Int.fract ((n : ℝ) * r) := by
      linarith [Int.fract_add_floor ((n : ℝ) * r)]
    have h2 : r = (Int.floor r : ℝ) + Int.fract r := by
      linarith [Int.fract_add_floor r]
    push_cast
    linarith
  have hsum_nn : 0 ≤ Int.fract ((n : ℝ) * r) + Int.fract r :=
    add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)
  have hsum_lt2 : Int.fract ((n : ℝ) * r) + Int.fract r < 2 := by
    linarith [Int.fract_lt_one ((n : ℝ) * r), Int.fract_lt_one r]
  have hcase1 : Int.fract ((n : ℝ) * r) + Int.fract r < 1 →
      Nat.floor (((n + 1 : ℕ) : ℝ) * r) = Nat.floor ((n : ℝ) * r) + Nat.floor r := by
    intro hlt
    rw [Nat.floor_eq_iff hnr1_nn]
    constructor <;> linarith
  have hcase2 : 1 ≤ Int.fract ((n : ℝ) * r) + Int.fract r →
      Nat.floor (((n + 1 : ℕ) : ℝ) * r) = Nat.floor ((n : ℝ) * r) + Nat.floor r + 1 := by
    intro hge
    rw [Nat.floor_eq_iff hnr1_nn]
    push_cast at hdecomp ⊢
    constructor <;> linarith
  constructor
  · constructor
    · intro heq
      by_contra hnot
      have hge : 1 ≤ Int.fract ((n : ℝ) * r) + Int.fract r := le_of_not_gt hnot
      have h2 := hcase2 hge
      omega
    · intro hlt
      have h1 := hcase1 hlt
      omega
  · constructor
    · intro heq
      by_contra hnot
      have hlt : Int.fract ((n : ℝ) * r) + Int.fract r < 1 := lt_of_not_ge hnot
      have h1 := hcase1 hlt
      omega
    · intro hge
      have h2 := hcase2 hge
      omega

/-- **Sturmian Gap Dichotomy (`Nat.floor`):** for `r ≥ 0` and every `n : ℕ`,
`⌊(n + 1) r⌋₊ - ⌊n r⌋₊ ∈ {⌊r⌋₊, ⌊r⌋₊ + 1}`. -/
theorem ppl034_beatty_gap_dichotomy {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    Nat.floor (((n + 1 : ℕ) : ℝ) * r) - Nat.floor ((n : ℝ) * r) = Nat.floor r ∨
    Nat.floor (((n + 1 : ℕ) : ℝ) * r) - Nat.floor ((n : ℝ) * r) = Nat.floor r + 1 := by
  rcases lt_or_ge (Int.fract ((n : ℝ) * r) + Int.fract r) 1 with hlt | hge
  · exact Or.inl ((ppl034_beatty_gap_iff hr n).1.mpr hlt)
  · exact Or.inr ((ppl034_beatty_gap_iff hr n).2.mpr hge)

/-- **Sturmian Gap Dichotomy (`Int.floor`):** for any real `r` and integer `n`,
`⌊(n + 1) r⌋ - ⌊n r⌋ ∈ {⌊r⌋, ⌊r⌋ + 1}`. -/
theorem ppl034_beatty_int_gap_dichotomy (r : ℝ) (n : ℤ) :
    Int.floor (((n + 1 : ℤ) : ℝ) * r) - Int.floor ((n : ℝ) * r) = Int.floor r ∨
    Int.floor (((n + 1 : ℤ) : ℝ) * r) - Int.floor ((n : ℝ) * r) = Int.floor r + 1 := by
  have h1 : (n : ℝ) * r = (Int.floor ((n : ℝ) * r) : ℝ) + Int.fract ((n : ℝ) * r) := by
    linarith [Int.fract_add_floor ((n : ℝ) * r)]
  have h2 : r = (Int.floor r : ℝ) + Int.fract r := by
    linarith [Int.fract_add_floor r]
  have hdecomp : ((n + 1 : ℤ) : ℝ) * r =
      ((Int.floor ((n : ℝ) * r) + Int.floor r : ℤ) : ℝ) +
        (Int.fract ((n : ℝ) * r) + Int.fract r) := by
    push_cast; linarith
  have hnn : 0 ≤ Int.fract ((n : ℝ) * r) + Int.fract r :=
    add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)
  have hlt2 : Int.fract ((n : ℝ) * r) + Int.fract r < 2 := by
    linarith [Int.fract_lt_one ((n : ℝ) * r), Int.fract_lt_one r]
  rcases lt_or_ge (Int.fract ((n : ℝ) * r) + Int.fract r) 1 with hlt | hge
  · left
    have hfl : Int.floor (((n + 1 : ℤ) : ℝ) * r) = Int.floor ((n : ℝ) * r) + Int.floor r := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega
  · right
    have hfl : Int.floor (((n + 1 : ℤ) : ℝ) * r) = Int.floor ((n : ℝ) * r) + Int.floor r + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega

/-- **Universal Fractional-Part Characterization of Beatty Sequences:**
For EVERY real `r > 1` (rational or irrational) and every positive integer `m ≥ 1`,
`m` lies in the Beatty sequence `{⌊n r⌋₊ : n ≥ 1}` if and only if `Int.fract (-(m / r)) < 1 / r`. -/
theorem ppl034_beatty_mem_iff_neg_fract {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) :
    (∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ↔
      Int.fract (-((m : ℝ) / r)) < 1 / r := by
  have hr_pos : 0 < r := by linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hx_pos : 0 < (m : ℝ) / r := div_pos hm_pos hr_pos
  have hfract_eq : Int.fract (-((m : ℝ) / r)) = (Int.ceil ((m : ℝ) / r) : ℝ) - (m : ℝ) / r := by
    show -((m : ℝ) / r) - (Int.floor (-((m : ℝ) / r)) : ℝ) = _
    rw [Int.floor_neg]
    push_cast
    ring
  rw [hfract_eq]
  constructor
  · rintro ⟨n, _, hfl⟩
    have hnr_nn : 0 ≤ (n : ℝ) * r := by positivity
    have hbounds := (Nat.floor_eq_iff hnr_nn).mp hfl
    have hle : (m : ℝ) / r ≤ (n : ℝ) := (div_le_iff₀ hr_pos).mpr hbounds.1
    have hlt : (n : ℝ) < ((m : ℝ) + 1) / r := (lt_div_iff₀ hr_pos).mpr hbounds.2
    have hceil_le : (Int.ceil ((m : ℝ) / r) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Int.ceil_le.mpr (by exact_mod_cast hle) : Int.ceil ((m : ℝ) / r) ≤ (n : ℤ))
    have hadd : ((m : ℝ) + 1) / r = (m : ℝ) / r + 1 / r := by ring
    linarith
  · intro hlt
    set n : ℕ := Nat.ceil ((m : ℝ) / r)
    have hn_pos : 1 ≤ n := by
      have : 0 < n := Nat.ceil_pos.mpr hx_pos
      omega
    have hceil_cast : (Int.ceil ((m : ℝ) / r) : ℝ) = (n : ℝ) := by
      have h1 : Int.ceil ((m : ℝ) / r) = (n : ℤ) := by
        rw [Int.ceil_eq_iff]
        refine ⟨?_, by exact_mod_cast Nat.le_ceil ((m : ℝ) / r)⟩
        have hsub : ((n : ℤ) - 1 : ℝ) = ((n - 1 : ℕ) : ℝ) := by
          have hn' : (n - 1 : ℕ) + 1 = n := by omega
          have h2 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn'
          push_cast; linarith
        rw [hsub]
        exact (Nat.lt_ceil).mp (by omega : n - 1 < n)
      exact_mod_cast h1
    rw [hceil_cast] at hlt
    have hle_n : (m : ℝ) / r ≤ (n : ℝ) := Nat.le_ceil _
    have hmul1 : (m : ℝ) ≤ (n : ℝ) * r := (div_le_iff₀ hr_pos).mp hle_n
    have hlt_n : (n : ℝ) < ((m : ℝ) + 1) / r := by
      have hadd : ((m : ℝ) + 1) / r = (m : ℝ) / r + 1 / r := by ring
      linarith
    have hmul2 : (n : ℝ) * r < (m : ℝ) + 1 := (lt_div_iff₀ hr_pos).mp hlt_n
    refine ⟨n, hn_pos, ?_⟩
    exact (Nat.floor_eq_iff (by positivity)).mpr ⟨hmul1, hmul2⟩

private lemma fract_neg_of_not_int {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    Int.fract (-x) = 1 - Int.fract x := by
  have hpos : 0 < Int.fract x := by
    rcases eq_or_lt_of_le (Int.fract_nonneg x) with h0 | hpos
    · exfalso
      have hfl : x = (Int.floor x : ℝ) := by
        have : Int.fract x = x - (Int.floor x : ℝ) := rfl
        linarith
      exact hx (Int.floor x) hfl
    · exact hpos
  have hlt1 : Int.fract x < 1 := Int.fract_lt_one x
  have hfl_neg : Int.floor (-x) = -(Int.floor x) - 1 := by
    rw [Int.floor_eq_iff]
    have hdef : Int.fract x = x - (Int.floor x : ℝ) := rfl
    push_cast
    constructor <;> linarith
  show -x - (Int.floor (-x) : ℝ) = 1 - (x - (Int.floor x : ℝ))
  rw [hfl_neg]
  push_cast
  ring

private lemma nat_div_irrational_ne_int {r : ℝ} (hr : Irrational r) {m : ℕ} (hm : 1 ≤ m) (k : ℤ) :
    (m : ℝ) / r ≠ (k : ℝ) := by
  intro heq
  have hr_ne : r ≠ 0 := hr.ne_zero
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hk_ne : (k : ℝ) ≠ 0 := by
    intro hk0
    rw [hk0] at heq
    exact (div_ne_zero hm_ne hr_ne) heq
  have hrat : ((m : ℚ) / (k : ℚ) : ℝ) = r := by
    push_cast
    have hmul : (m : ℝ) = (k : ℝ) * r := (div_eq_iff hr_ne).mp heq
    rw [hmul, mul_div_cancel_left₀ r hk_ne]
  exact hr ⟨(m : ℚ) / (k : ℚ), by simpa using hrat⟩

/-- **Irrational Fractional-Part Equivalences:** for `r > 1` irrational and `m ≥ 1`,
`m ∈ B_r` iff `1 - 1 / r < Int.fract (m / r)` iff `Int.fract ((m + 1) / r) < 1 / r`. -/
theorem ppl034_beatty_mem_iff_fract_irrational {r : ℝ} (hr : 1 < r) (hirr : Irrational r)
    {m : ℕ} (hm : 1 ≤ m) :
    ((∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ↔ 1 - 1 / r < Int.fract ((m : ℝ) / r)) ∧
    ((∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ↔ Int.fract (((m + 1 : ℕ) : ℝ) / r) < 1 / r) := by
  have hneg := ppl034_beatty_mem_iff_neg_fract hr hm
  have hnotint := nat_div_irrational_ne_int hirr hm
  have hfn : Int.fract (-((m : ℝ) / r)) = 1 - Int.fract ((m : ℝ) / r) :=
    fract_neg_of_not_int hnotint
  have h1 : (∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ↔ 1 - 1 / r < Int.fract ((m : ℝ) / r) := by
    rw [hneg, hfn]
    constructor <;> intro h <;> linarith
  have h2 : (∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ↔
      Int.fract (((m + 1 : ℕ) : ℝ) / r) < 1 / r := by
    rw [h1]
    have hadd : ((m + 1 : ℕ) : ℝ) / r = (m : ℝ) / r + 1 / r := by push_cast; ring
    rw [hadd]
    have hfl_eq : (m : ℝ) / r + 1 / r =
        (Int.floor ((m : ℝ) / r) : ℝ) + (Int.fract ((m : ℝ) / r) + 1 / r) := by
      have : Int.fract ((m : ℝ) / r) = (m : ℝ) / r - (Int.floor ((m : ℝ) / r) : ℝ) := rfl
      linarith
    have hinv_pos : 0 < 1 / r := one_div_pos.mpr (by linarith)
    have hinv_lt1 : 1 / r < 1 := by
      rw [div_lt_one (by linarith)]; exact hr
    have hfr_nn : 0 ≤ Int.fract ((m : ℝ) / r) := Int.fract_nonneg _
    have hfr_lt1 : Int.fract ((m : ℝ) / r) < 1 := Int.fract_lt_one _
    have hnot_eq : Int.fract ((m : ℝ) / r) + 1 / r ≠ 1 := by
      intro heq
      have hint : ((m + 1 : ℕ) : ℝ) / r = ((Int.floor ((m : ℝ) / r) + 1 : ℤ) : ℝ) := by
        rw [hadd, hfl_eq, heq]; push_cast; ring
      exact nat_div_irrational_ne_int hirr (by omega : 1 ≤ m + 1) (Int.floor ((m : ℝ) / r) + 1) hint
    constructor
    · intro hgt
      have hge1 : 1 ≤ Int.fract ((m : ℝ) / r) + 1 / r := by linarith
      have hfl_sum : Int.floor ((m : ℝ) / r + 1 / r) = Int.floor ((m : ℝ) / r) + 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      have hfr_sum : Int.fract ((m : ℝ) / r + 1 / r) = Int.fract ((m : ℝ) / r) + 1 / r - 1 := by
        show ((m : ℝ) / r + 1 / r) - (Int.floor ((m : ℝ) / r + 1 / r) : ℝ) = _
        rw [hfl_sum]; push_cast; linarith
      linarith
    · intro hlt
      by_contra hle
      have hle' : Int.fract ((m : ℝ) / r) + 1 / r ≤ 1 := by linarith
      have hlt1 : Int.fract ((m : ℝ) / r) + 1 / r < 1 := lt_of_le_of_ne hle' hnot_eq
      have hfl_sum : Int.floor ((m : ℝ) / r + 1 / r) = Int.floor ((m : ℝ) / r) := by
        rw [Int.floor_eq_iff]; constructor <;> linarith
      have hfr_sum : Int.fract ((m : ℝ) / r + 1 / r) = Int.fract ((m : ℝ) / r) + 1 / r := by
        show ((m : ℝ) / r + 1 / r) - (Int.floor ((m : ℝ) / r + 1 / r) : ℝ) = _
        rw [hfl_sum]; linarith
      have hfr_pos : 0 < Int.fract ((m : ℝ) / r) := by
        rcases eq_or_lt_of_le hfr_nn with h0 | hp
        · exfalso
          exact hnotint (Int.floor ((m : ℝ) / r)) (by
            have : Int.fract ((m : ℝ) / r) = (m : ℝ) / r - (Int.floor ((m : ℝ) / r) : ℝ) := rfl
            linarith)
        · exact hp
      linarith
  exact ⟨h1, h2⟩

/-- **Beatty–Rayleigh Complementarity Theorem:**
If `r, s > 1` with `Irrational r` and `1 / r + 1 / s = 1`, then the Beatty sequences
`{⌊n r⌋₊ : n ≥ 1}` and `{⌊n s⌋₊ : n ≥ 1}` partition the positive integers `ℕ_{≥ 1}`
(every `m ≥ 1` belongs to at least one and never to both). -/
theorem ppl034_beatty_rayleigh_partition {r s : ℝ} (hr : 1 < r) (hs : 1 < s)
    (hirr : Irrational r) (hcomp : 1 / r + 1 / s = 1) :
    ∀ m : ℕ, 1 ≤ m →
      ((∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ∨
       (∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * s) = m)) ∧
      ¬ ((∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m) ∧
         (∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * s) = m)) := by
  have hirr_s : Irrational s := by
    rintro ⟨q, hq⟩
    have hq_ne : q ≠ 0 := by
      intro h0; rw [h0, Rat.cast_zero] at hq; linarith
    have hq_ne1 : q ≠ 1 := by
      intro h1; rw [h1, Rat.cast_one] at hq; linarith
    have hr_rat : ((q / (q - 1) : ℚ) : ℝ) = r := by
      have hs_ne : s ≠ 0 := by linarith
      have hr_ne : r ≠ 0 := by linarith
      have hs1_ne : s - 1 ≠ 0 := by linarith
      push_cast
      rw [hq]
      have h1 : 1 / r = (s - 1) / s := by
        have : 1 / r = 1 - 1 / s := by linarith
        rw [this]; field_simp [hs_ne]
      have h2 : r = s / (s - 1) := by
        have := congrArg (fun x => x⁻¹) h1
        simpa [one_div, inv_div] using this
      exact h2.symm
    exact hirr ⟨q / (q - 1), hr_rat⟩
  intro m hm
  have hmem_r := (ppl034_beatty_mem_iff_fract_irrational hr hirr hm).1
  have hmem_s := (ppl034_beatty_mem_iff_fract_irrational hs hirr_s hm).1
  have hsum_int : (m : ℝ) / s = (m : ℝ) - (m : ℝ) / r := by
    have : (m : ℝ) / r + (m : ℝ) / s = (m : ℝ) := by
      calc (m : ℝ) / r + (m : ℝ) / s = (m : ℝ) * (1 / r + 1 / s) := by ring
        _ = (m : ℝ) * 1 := by rw [hcomp]
        _ = (m : ℝ) := mul_one _
    linarith
  have hfract_s : Int.fract ((m : ℝ) / s) = 1 - Int.fract ((m : ℝ) / r) := by
    rw [hsum_int]
    have hsub : (m : ℝ) - (m : ℝ) / r = -((m : ℝ) / r) + ((m : ℤ) : ℝ) := by push_cast; ring
    rw [hsub, Int.fract_add_intCast]
    exact fract_neg_of_not_int (nat_div_irrational_ne_int hirr hm)
  have hne : Int.fract ((m : ℝ) / r) ≠ 1 / s := by
    intro heq
    have h1 : (m : ℝ) / r - (Int.floor ((m : ℝ) / r) : ℝ) = 1 - 1 / r := by
      show Int.fract ((m : ℝ) / r) = 1 - 1 / r
      linarith
    have h2 : ((m + 1 : ℕ) : ℝ) / r = ((Int.floor ((m : ℝ) / r) + 1 : ℤ) : ℝ) := by
      push_cast
      have : ((m : ℝ) + 1) / r = (m : ℝ) / r + 1 / r := by ring
      linarith
    exact nat_div_irrational_ne_int hirr (by omega : 1 ≤ m + 1) (Int.floor ((m : ℝ) / r) + 1) h2
  rw [hmem_r, hmem_s, hfract_s]
  constructor
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · right; linarith
    · left; linarith
  · rintro ⟨h1, h2⟩
    linarith

/-- **Exact `O(1)` Beatty Counting Function Bounds:**
For every `r > 1` and `N : ℕ`, the number of Beatty elements `⌊n r⌋₊` (`n ≥ 1`) in `{1, ..., N}`
lies in `[(N + 1)/r - 1, (N + 1)/r)`. -/
theorem ppl034_beatty_count_bounds {r : ℝ} (hr : 1 < r) (N : ℕ) :
    ((N : ℝ) + 1) / r - 1 ≤
      (Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ N ∧ ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m} : ℝ) ∧
    (Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ N ∧ ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m} : ℝ) <
      ((N : ℝ) + 1) / r := by
  have hr_pos : 0 < r := by linarith
  set K : ℕ := Nat.ceil (((N : ℝ) + 1) / r) - 1
  have hx_pos : 0 < ((N : ℝ) + 1) / r := by positivity
  have hceil_pos : 1 ≤ Nat.ceil (((N : ℝ) + 1) / r) := Nat.ceil_pos.mpr hx_pos
  have hK_lt : (K : ℝ) < ((N : ℝ) + 1) / r := by
    have h1 : K < Nat.ceil (((N : ℝ) + 1) / r) := by omega
    exact (Nat.lt_ceil).mp h1
  have hK1_ge : ((N : ℝ) + 1) / r ≤ (K : ℝ) + 1 := by
    have h1 : K + 1 = Nat.ceil (((N : ℝ) + 1) / r) := by omega
    have h2 : ((N : ℝ) + 1) / r ≤ (Nat.ceil (((N : ℝ) + 1) / r) : ℝ) := Nat.le_ceil _
    rw [← h1] at h2
    exact_mod_cast h2
  have hset_eq :
      {m : ℕ | 1 ≤ m ∧ m ≤ N ∧ ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m} =
        (fun n : ℕ => Nat.floor ((n : ℝ) * r)) '' Set.Icc (1 : ℕ) K := by
    ext m
    constructor
    · rintro ⟨hm1, hmN, n, hn1, rfl⟩
      refine ⟨n, ⟨hn1, ?_⟩, rfl⟩
      have hlt_N1 : (n : ℝ) * r < (N : ℝ) + 1 := by
        have h1 : (n : ℝ) * r < (Nat.floor ((n : ℝ) * r) : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : (Nat.floor ((n : ℝ) * r) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
        linarith
      have hn_lt : (n : ℝ) < ((N : ℝ) + 1) / r := (lt_div_iff₀ hr_pos).mpr hlt_N1
      have hn_lt_K1 : n < K + 1 := by
        have : (n : ℝ) < (K : ℝ) + 1 := lt_of_lt_of_le hn_lt hK1_ge
        exact_mod_cast this
      omega
    · rintro ⟨n, ⟨hn1, hnK⟩, rfl⟩
      have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hge1 : 1 ≤ Nat.floor ((n : ℝ) * r) := by
        rw [Nat.le_floor_iff (by positivity)]
        push_cast; nlinarith
      have hnr_lt : (n : ℝ) * r < (N : ℝ) + 1 := by
        have hn_le_K : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnK
        have hn_lt : (n : ℝ) < ((N : ℝ) + 1) / r := lt_of_le_of_lt hn_le_K hK_lt
        exact (lt_div_iff₀ hr_pos).mp hn_lt
      have hleN : Nat.floor ((n : ℝ) * r) ≤ N := by
        have hlt : Nat.floor ((n : ℝ) * r) < N + 1 :=
          (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast hnr_lt)
        omega
      exact ⟨hge1, hleN, n, hn1, rfl⟩
  have hcard : Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ N ∧ ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m} = K := by
    rw [hset_eq, Set.ncard_image_of_injective _ (ppl034_beatty_strictMono hr.le).injective]
    have hIcc : Set.Icc (1 : ℕ) K = (Finset.Icc 1 K : Set ℕ) := by ext x; simp
    rw [hIcc, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  rw [hcard]
  exact ⟨by linarith, hK_lt⟩

/-- **Exact Asymptotic Density of a Beatty Sequence:**
For every `r > 1`, the natural density of `{⌊n r⌋₊ : n ≥ 1}` equals `1 / r`. -/
theorem ppl034_beatty_density_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto
      (fun N : ℕ =>
        (Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ N ∧ ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m} : ℝ) /
          (N : ℝ))
      atTop (nhds (1 / r)) := by
  have hlo : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / r - 1) / (N : ℝ)) atTop (nhds (1 / r)) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h1 : Tendsto (fun N : ℕ => 1 / r + (1 / r - 1) * ((1 : ℝ) / (N : ℝ))) atTop
        (nhds (1 / r + (1 / r - 1) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    rw [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hr_ne : r ≠ 0 := by linarith
    field_simp [hNpos, hr_ne]
    ring
  have hhi : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / r) / (N : ℝ)) atTop (nhds (1 / r)) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h1 : Tendsto (fun N : ℕ => 1 / r + (1 / r) * ((1 : ℝ) / (N : ℝ))) atTop
        (nhds (1 / r + (1 / r) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    rw [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hr_ne : r ≠ 0 := by linarith
    field_simp [hNpos, hr_ne]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact div_le_div_of_nonneg_right (ppl034_beatty_count_bounds hr N).1 hNpos.le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact div_le_div_of_nonneg_right (ppl034_beatty_count_bounds hr N).2.le hNpos.le

/-! ## Section 2: Rational vs. Irrational No-Arithmetic-Progression Dichotomy -/

/-- Every rational `r > 1` has a Beatty sequence containing an infinite arithmetic progression
`c * k` (`k ≥ 1`). -/
theorem ppl034_rational_contains_ap {r : ℝ} (hr : 1 < r) (hrat : ¬ Irrational r) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = c * k := by
  have hq : ∃ q : ℚ, (q : ℝ) = r := by
    by_contra hnot
    exact hrat (by simpa [Irrational, Set.mem_range] using hnot)
  rcases hq with ⟨q, rfl⟩
  have hq_pos : (0 : ℚ) < q := by exact_mod_cast (show (0 : ℝ) < (q : ℝ) by linarith)
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
  set p : ℕ := q.num.toNat
  have hp_pos : 1 ≤ p := by omega
  have hp_eq : (p : ℤ) = q.num := Int.toNat_of_nonneg hnum_pos.le
  have hden_pos : 0 < q.den := q.pos
  have hr_eq : (q : ℝ) = (p : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def, ← hp_eq]
    simp
  refine ⟨p, hp_pos, fun k hk => ?_⟩
  refine ⟨q.den * k, by nlinarith, ?_⟩
  have hden_ne : (q.den : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
  have hmul : ((q.den * k : ℕ) : ℝ) * (q : ℝ) = ((p * k : ℕ) : ℝ) := by
    rw [hr_eq]
    push_cast
    field_simp [hden_ne]
  rw [hmul, Nat.floor_natCast]

/-- Every rational `r > 1` has a Beatty sequence containing a strictly increasing order-2
homogeneous linear recurrence (`u (k + 2) = 2 u (k + 1) - u k`). -/
theorem ppl034_rational_contains_recurrence {r : ℝ} (hr : 1 < r) (hrat : ¬ Irrational r) :
    ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
      StrictMono u ∧
      c 0 = -1 ∧ c 1 = 2 ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
      (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  rcases ppl034_rational_contains_ap hr hrat with ⟨p, hp, hap⟩
  refine ⟨fun k => p * (k + 1), fun j => if j = 0 then -1 else 2, ?_, by simp, by simp, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  · intro k
    exact hap (k + 1) (by omega)
  · intro k
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, add_zero, ↓reduceIte, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one]
    push_cast
    ring

/-- **Unconditional Irrational No-Arithmetic-Progression Theorem:**
For EVERY irrational `r > 1`, EVERY step `c ≥ 1`, and EVERY offset `d : ℕ`, the Beatty sequence
`⌊n r⌋₊` does NOT contain the arithmetic progression `{c * k + d : k ≥ 1}`.
Proved via `Arith4Ext.LargeSieveDiophantine.kronecker_dense_fract`. -/
theorem ppl034_irrational_no_ap {r : ℝ} (hr : 1 < r) (hirr : Irrational r)
    (c d : ℕ) (hc : 1 ≤ c) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, Nat.floor ((n : ℝ) * r) ≠ c * k + d := by
  set α : ℝ := -((c : ℝ) / r)
  set β : ℝ := -((d : ℝ) / r)
  have hα_irr : Irrational α := by
    rintro ⟨q, hq⟩
    have hr_ne : r ≠ 0 := by linarith
    have hc_ne : (c : ℝ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by omega)
    have hq_ne : (q : ℝ) ≠ 0 := by
      rw [hq]
      exact neg_ne_zero.mpr (div_ne_zero hc_ne hr_ne)
    have hr_rat : ((-(c : ℚ) / q : ℚ) : ℝ) = r := by
      push_cast
      rw [hq]
      simp only [α]
      field_simp [hr_ne, hc_ne]
    exact hirr ⟨-(c : ℚ) / q, hr_rat⟩
  set γ : ℝ := Int.fract β
  have hγ_nn : 0 ≤ γ := Int.fract_nonneg β
  have hγ_lt1 : γ < 1 := Int.fract_lt_one β
  have hinv_pos : 0 < 1 / r := one_div_pos.mpr (by linarith)
  have hinv_lt1 : 1 / r < 1 := (div_lt_one (by linarith)).mpr hr
  have hex : ∃ k : ℕ, 1 ≤ k ∧ 1 / r ≤ Int.fract ((k : ℝ) * α + β) := by
    rcases lt_or_ge γ (1 / r) with hlt | hge
    · set a : ℝ := 1 / r - γ
      set b : ℝ := 1 - γ
      have ha_pos : 0 < a := by linarith
      have hab : a < b := by linarith
      have hb : b ≤ 1 := by linarith
      rcases Arith4Ext.LargeSieveDiophantine.kronecker_dense_fract α hα_irr ha_pos.le hab hb with
        ⟨k, hk1, hk2⟩
      have hk_pos : 1 ≤ k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        subst hk0
        simp at hk1
        linarith
      refine ⟨k, hk_pos, ?_⟩
      have hdecomp : (k : ℝ) * α + β =
          (Int.fract ((k : ℝ) * α) + γ) + ((Int.floor ((k : ℝ) * α) + Int.floor β : ℤ) : ℝ) := by
        have h1 : (k : ℝ) * α = Int.fract ((k : ℝ) * α) + (Int.floor ((k : ℝ) * α) : ℝ) := by
          linarith [Int.fract_add_floor ((k : ℝ) * α)]
        have h2 : β = γ + (Int.floor β : ℝ) := by
          linarith [Int.fract_add_floor β]
        push_cast; linarith
      rw [hdecomp, Int.fract_add_intCast]
      have hfr_eq : Int.fract (Int.fract ((k : ℝ) * α) + γ) = Int.fract ((k : ℝ) * α) + γ := by
        exact Int.fract_eq_self.mpr ⟨by linarith [Int.fract_nonneg ((k : ℝ) * α)], by linarith⟩
      rw [hfr_eq]
      linarith
    · set a : ℝ := (1 - γ) / 2
      set b : ℝ := 1 - γ
      have ha_pos : 0 < a := by simp only [a]; linarith
      have hab : a < b := by simp only [a, b]; linarith
      have hb : b ≤ 1 := by simp only [b]; linarith
      rcases Arith4Ext.LargeSieveDiophantine.kronecker_dense_fract α hα_irr ha_pos.le hab hb with
        ⟨k, hk1, hk2⟩
      have hk_pos : 1 ≤ k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        subst hk0
        simp at hk1
        linarith
      refine ⟨k, hk_pos, ?_⟩
      have hdecomp : (k : ℝ) * α + β =
          (Int.fract ((k : ℝ) * α) + γ) + ((Int.floor ((k : ℝ) * α) + Int.floor β : ℤ) : ℝ) := by
        have h1 : (k : ℝ) * α = Int.fract ((k : ℝ) * α) + (Int.floor ((k : ℝ) * α) : ℝ) := by
          linarith [Int.fract_add_floor ((k : ℝ) * α)]
        have h2 : β = γ + (Int.floor β : ℝ) := by
          linarith [Int.fract_add_floor β]
        push_cast; linarith
      rw [hdecomp, Int.fract_add_intCast]
      have hfr_eq : Int.fract (Int.fract ((k : ℝ) * α) + γ) = Int.fract ((k : ℝ) * α) + γ := by
        exact Int.fract_eq_self.mpr ⟨by linarith [Int.fract_nonneg ((k : ℝ) * α)], by linarith⟩
      rw [hfr_eq]
      linarith
  rcases hex with ⟨k, hk_pos, hge_fr⟩
  refine ⟨k, hk_pos, fun n hn => ?_⟩
  have hm_pos : 1 ≤ c * k + d := by nlinarith
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    simp at hn
    omega
  have hlt_fr := (ppl034_beatty_mem_iff_neg_fract hr hm_pos).mp ⟨n, hn_pos, hn⟩
  have harg : -(((c * k + d : ℕ) : ℝ) / r) = (k : ℝ) * α + β := by
    simp only [α, β]
    push_cast
    ring
  rw [harg] at hlt_fr
  linarith

/-- For every irrational `r > 1`, every arithmetic progression `{c * k + d}` (`c ≥ 1`) misses
the Beatty sequence `⌊n r⌋₊` infinitely often. -/
theorem ppl034_irrational_ap_misses_infinitely_often {r : ℝ} (hr : 1 < r) (hirr : Irrational r)
    (c d : ℕ) (hc : 1 ≤ c) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ ∀ n : ℕ, Nat.floor ((n : ℝ) * r) ≠ c * k + d := by
  rcases ppl034_irrational_no_ap hr hirr c (c * K + d) hc with ⟨k, hk1, hmiss⟩
  refine ⟨K + k, by omega, fun n => ?_⟩
  have heq : c * (K + k) + d = c * k + (c * K + d) := by ring
  rw [heq]
  exact hmiss n

/-- **Complete Classification of AP-Containing Beatty Sequences:**
For every `r > 1`, the Beatty sequence `{⌊n r⌋₊ : n ≥ 1}` contains an infinite arithmetic
progression `{c * k + d : k ≥ 1}` (`c ≥ 1`) if and only if `r` is rational. -/
theorem ppl034_contains_ap_iff_rational {r : ℝ} (hr : 1 < r) :
    (∃ c d : ℕ, 1 ≤ c ∧ ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = c * k + d) ↔
      ¬ Irrational r := by
  constructor
  · rintro ⟨c, d, hc, hap⟩ hirr
    rcases ppl034_irrational_no_ap hr hirr c d hc with ⟨k, hk1, hmiss⟩
    rcases hap k hk1 with ⟨n, _, hn⟩
    exact hmiss n hn
  · intro hrat
    rcases ppl034_rational_contains_ap hr hrat with ⟨c, hc, hap⟩
    exact ⟨c, 0, hc, fun k hk => by simpa using hap k hk⟩

/-! ## Section 3: Quadratic Pisot Numbers, Metallic Means, Golden Ratio, & Topological Density -/

private def quadRec (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => a * quadRec a b (k + 1) + b * quadRec a b k

private lemma quadRec_binet {a b : ℤ} {r s : ℝ} (hrs : r + s = (a : ℝ))
    (hprod : r * s = -(b : ℝ)) (hne : r ≠ s) (k : ℕ) :
    (quadRec a b k : ℝ) = (r ^ k - s ^ k) / (r - s) := by
  have hsub_ne : r - s ≠ 0 := sub_ne_zero.mpr hne
  have hr2 : r ^ 2 = (a : ℝ) * r + (b : ℝ) := by linear_combination r * hrs - hprod
  have hs2 : s ^ 2 = (a : ℝ) * s + (b : ℝ) := by linear_combination s * hrs - hprod
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [quadRec]
    | 1 =>
      simp only [quadRec, Int.cast_one, pow_one]
      exact (div_self hsub_ne).symm
    | k + 2 =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      simp only [quadRec, Int.cast_add, Int.cast_mul, h1, h0]
      field_simp [hsub_ne]
      calc (a : ℝ) * (r ^ (k + 1) - s ^ (k + 1)) + (b : ℝ) * (r ^ k - s ^ k)
          = r ^ k * ((a : ℝ) * r + (b : ℝ)) - s ^ k * ((a : ℝ) * s + (b : ℝ)) := by ring
        _ = r ^ k * r ^ 2 - s ^ k * s ^ 2 := by rw [hr2, hs2]
        _ = r ^ (k + 2) - s ^ (k + 2) := by ring

private lemma quadRec_mul_sub {a b : ℤ} {r s : ℝ} (hrs : r + s = (a : ℝ))
    (hprod : r * s = -(b : ℝ)) (hne : r ≠ s) (k : ℕ) :
    (quadRec a b k : ℝ) * r - (quadRec a b (k + 1) : ℝ) = -(s ^ k) := by
  have hsub_ne : r - s ≠ 0 := sub_ne_zero.mpr hne
  rw [quadRec_binet hrs hprod hne k, quadRec_binet hrs hprod hne (k + 1)]
  field_simp [hsub_ne]
  ring

private lemma quadRec_bisect {a b : ℤ} (k : ℕ) :
    quadRec a b (k + 4) = (a ^ 2 + 2 * b) * quadRec a b (k + 2) - b ^ 2 * quadRec a b k := by
  have h4 : quadRec a b (k + 4) = a * quadRec a b (k + 3) + b * quadRec a b (k + 2) := rfl
  have h3 : quadRec a b (k + 3) = a * quadRec a b (k + 2) + b * quadRec a b (k + 1) := rfl
  have h2 : quadRec a b (k + 2) = a * quadRec a b (k + 1) + b * quadRec a b k := rfl
  linear_combination h4 + a * h3 - b * h2

/-- **General Quadratic Pisot Theorem:**
For EVERY quadratic Pisot number `r > 1` — i.e., every `r > 1` satisfying `r^2 = a * r + b`
(`a, b : ℤ`) whose Galois conjugate `s = a - r` satisfies `|s| < 1` — the Beatty sequence
`{⌊n r⌋₊ : n ≥ 1}` contains a strictly increasing order-2 homogeneous linear recurrence. -/
theorem ppl034_quadratic_pisot_contains_recurrence {r : ℝ} (hr : 1 < r) {a b : ℤ}
    (hquad : r ^ 2 = (a : ℝ) * r + (b : ℝ)) (hpisot : |(a : ℝ) - r| < 1) :
    ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
      StrictMono u ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
      (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  set s : ℝ := (a : ℝ) - r
  have hrs : r + s = (a : ℝ) := by simp [s]
  have hprod : r * s = -(b : ℝ) := by simp only [s]; linarith
  have hs_abs : |s| < 1 := hpisot
  have hs_lt1 : s < 1 := (abs_lt.mp hs_abs).2
  have hs_gt_neg1 : -1 < s := (abs_lt.mp hs_abs).1
  have hne : r ≠ s := by linarith
  have hrs_pos : 0 < r - s := by linarith
  rcases lt_trichotomy s 0 with hs_neg | hs_zero | hs_pos
  · -- Case 1: `-1 < s < 0` — bisected sequence `u j = quadRec a b (2*j + 2)`
    have hG_odd_pos : ∀ j : ℕ, 1 ≤ quadRec a b (2 * j + 1) := by
      intro j
      have hval := quadRec_binet hrs hprod hne (2 * j + 1)
      have hr_pow : 1 < r ^ (2 * j + 1) := one_lt_pow₀ hr (by omega)
      have hs_pow_neg : s ^ (2 * j + 1) < 0 := Odd.pow_neg ⟨j, rfl⟩ hs_neg
      have hpos : (0 : ℝ) < (quadRec a b (2 * j + 1) : ℝ) := by
        rw [hval]; exact div_pos (by linarith) hrs_pos
      have hint : (0 : ℤ) < quadRec a b (2 * j + 1) := by exact_mod_cast hpos
      omega
    have hG_even_pos : ∀ j : ℕ, 1 ≤ quadRec a b (2 * j + 2) := by
      intro j
      have hval := quadRec_binet hrs hprod hne (2 * j + 2)
      have hr_pow : 1 < r ^ (2 * j + 2) := one_lt_pow₀ hr (by omega)
      have hs_pow_lt1 : s ^ (2 * j + 2) < 1 := by
        have h1 : |s ^ (2 * j + 2)| = |s| ^ (2 * j + 2) := abs_pow s _
        have h2 : |s| ^ (2 * j + 2) < 1 := pow_lt_one₀ (abs_nonneg s) hs_abs (by omega)
        linarith [le_abs_self (s ^ (2 * j + 2))]
      have hpos : (0 : ℝ) < (quadRec a b (2 * j + 2) : ℝ) := by
        rw [hval]; exact div_pos (by linarith) hrs_pos
      have hint : (0 : ℤ) < quadRec a b (2 * j + 2) := by exact_mod_cast hpos
      omega
    let u : ℕ → ℕ := fun j => (quadRec a b (2 * j + 2)).toNat
    have hu_cast : ∀ j : ℕ, (u j : ℤ) = quadRec a b (2 * j + 2) := fun j =>
      Int.toNat_of_nonneg (by linarith [hG_even_pos j])
    refine ⟨u, fun i => if i = 0 then -(b ^ 2) else a ^ 2 + 2 * b, ?_, ?_, ?_⟩
    · refine strictMono_nat_of_lt_succ fun j => ?_
      have hlt_R : (quadRec a b (2 * j + 2) : ℝ) < (quadRec a b (2 * (j + 1) + 2) : ℝ) := by
        rw [quadRec_binet hrs hprod hne (2 * j + 2), quadRec_binet hrs hprod hne (2 * (j + 1) + 2)]
        rw [div_lt_div_iff_of_pos_right hrs_pos]
        have hr_pow_pos : 0 < r ^ (2 * j + 2) := pow_pos (by linarith) _
        have hr2_gt1 : 1 < r ^ 2 := by nlinarith
        have hs2_lt1 : s ^ 2 < 1 := by nlinarith
        have hs_even_nn : 0 ≤ s ^ (2 * j + 2) := Even.pow_nonneg ⟨j + 1, by omega⟩ s
        have hdiff : (r ^ (2 * (j + 1) + 2) - s ^ (2 * (j + 1) + 2)) -
            (r ^ (2 * j + 2) - s ^ (2 * j + 2)) =
            r ^ (2 * j + 2) * (r ^ 2 - 1) + s ^ (2 * j + 2) * (1 - s ^ 2) := by
          have h1 : 2 * (j + 1) + 2 = (2 * j + 2) + 2 := by omega
          rw [h1, pow_add, pow_add]; ring
        nlinarith
      have hlt_Z : quadRec a b (2 * j + 2) < quadRec a b (2 * (j + 1) + 2) := by
        exact_mod_cast hlt_R
      have : (u j : ℤ) < (u (j + 1) : ℤ) := by rw [hu_cast, hu_cast]; exact hlt_Z
      exact_mod_cast this
    · intro j
      let n : ℕ := (quadRec a b (2 * j + 1)).toNat
      have hn_cast : (n : ℤ) = quadRec a b (2 * j + 1) :=
        Int.toNat_of_nonneg (by linarith [hG_odd_pos j])
      have hn_pos : 1 ≤ n := by
        have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_cast]; exact hG_odd_pos j
        exact_mod_cast this
      refine ⟨n, hn_pos, ?_⟩
      have hmul := quadRec_mul_sub hrs hprod hne (2 * j + 1)
      have hnr : (n : ℝ) * r = (u j : ℝ) + (-(s ^ (2 * j + 1))) := by
        have hnR : (n : ℝ) = (quadRec a b (2 * j + 1) : ℝ) := by exact_mod_cast hn_cast
        have huR : (u j : ℝ) = (quadRec a b (2 * j + 2) : ℝ) := by exact_mod_cast hu_cast j
        rw [hnR, huR]
        linarith
      have herr_pos : 0 < -(s ^ (2 * j + 1)) := by
        have : s ^ (2 * j + 1) < 0 := Odd.pow_neg ⟨j, rfl⟩ hs_neg
        linarith
      have herr_lt1 : -(s ^ (2 * j + 1)) < 1 := by
        have h1 : |s ^ (2 * j + 1)| < 1 := by
          rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg s) hs_abs (by omega)
        linarith [(abs_lt.mp h1).1]
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> linarith
    · intro j
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, add_zero, ↓reduceIte, Fin.one_eq_zero_iff,
        OfNat.ofNat_ne_one]
      rw [hu_cast (j + 2), hu_cast j, hu_cast (j + 1)]
      have hbis := quadRec_bisect (a := a) (b := b) (2 * j + 2)
      have hidx1 : 2 * (j + 2) + 2 = (2 * j + 2) + 4 := by omega
      have hidx2 : 2 * (j + 1) + 2 = (2 * j + 2) + 2 := by omega
      rw [hidx1, hidx2, hbis]
      ring
  · -- Case 2: `s = 0`, so `r = a` is an integer `≥ 2`
    have hr_rat : ¬ Irrational r := by
      intro hirr
      exact hirr ⟨a, by simp [show r = (a : ℝ) by linarith]⟩
    rcases ppl034_rational_contains_recurrence hr hr_rat with ⟨u, c, hmono, _, _, hmem, hrec⟩
    exact ⟨u, c, hmono, hmem, hrec⟩
  · -- Case 3: `0 < s < 1` — unbisected shifted difference `H k = quadRec a b (k+1) - quadRec a b k`
    let H : ℕ → ℤ := fun k => quadRec a b (k + 1) - quadRec a b k
    have hH_binet : ∀ k : ℕ, (H k : ℝ) = ((r - 1) * r ^ k + (1 - s) * s ^ k) / (r - s) := by
      intro k
      simp only [H, Int.cast_sub]
      rw [quadRec_binet hrs hprod hne (k + 1), quadRec_binet hrs hprod hne k]
      field_simp [hrs_pos.ne']
      ring
    have hH_pos : ∀ k : ℕ, 1 ≤ H k := by
      intro k
      have hrp : 0 < r ^ k := pow_pos (by linarith) k
      have hsp : 0 < s ^ k := pow_pos hs_pos k
      have hpos : (0 : ℝ) < (H k : ℝ) := by
        rw [hH_binet]; exact div_pos (by nlinarith) hrs_pos
      have hint : (0 : ℤ) < H k := by exact_mod_cast hpos
      omega
    have hH_mul : ∀ k : ℕ, (H k : ℝ) * r - (H (k + 1) : ℝ) = (1 - s) * s ^ k := by
      intro k
      simp only [H, Int.cast_sub]
      have h1 := quadRec_mul_sub hrs hprod hne (k + 1)
      have h0 := quadRec_mul_sub hrs hprod hne k
      calc ((quadRec a b (k + 1) : ℝ) - (quadRec a b k : ℝ)) * r -
              ((quadRec a b (k + 2) : ℝ) - (quadRec a b (k + 1) : ℝ))
          = ((quadRec a b (k + 1) : ℝ) * r - (quadRec a b (k + 2) : ℝ)) -
              ((quadRec a b k : ℝ) * r - (quadRec a b (k + 1) : ℝ)) := by ring
        _ = -(s ^ (k + 1)) - -(s ^ k) := by rw [h1, h0]
        _ = (1 - s) * s ^ k := by ring
    have hH_rec : ∀ k : ℕ, H (k + 2) = a * H (k + 1) + b * H k := by
      intro k
      simp only [H]
      have h3 : quadRec a b (k + 3) = a * quadRec a b (k + 2) + b * quadRec a b (k + 1) := rfl
      have h2 : quadRec a b (k + 2) = a * quadRec a b (k + 1) + b * quadRec a b k := rfl
      linarith
    -- Find `k₀` such that `(1 - s)^2 < (r - 1)^2 * r^{k₀}` so `H` is strictly increasing for `k ≥ k₀`
    have hex_k0 : ∃ k₀ : ℕ, (1 - s) ^ 2 < (r - 1) ^ 2 * r ^ k₀ := by
      have h1 : 0 < (r - 1) ^ 2 := sq_pos_of_pos (by linarith)
      have hev := (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop
        ((1 - s) ^ 2 / (r - 1) ^ 2)
      rcases Filter.eventually_atTop.mp hev with ⟨k₀, hk₀⟩
      refine ⟨k₀, ?_⟩
      have := (div_lt_iff₀ h1).mp (hk₀ k₀ le_rfl)
      linarith
    rcases hex_k0 with ⟨k₀, hk₀⟩
    let u : ℕ → ℕ := fun j => (H (j + k₀ + 1)).toNat
    have hu_cast : ∀ j : ℕ, (u j : ℤ) = H (j + k₀ + 1) := fun j =>
      Int.toNat_of_nonneg (by linarith [hH_pos (j + k₀ + 1)])
    refine ⟨u, fun i => if i = 0 then b else a, ?_, ?_, ?_⟩
    · refine strictMono_nat_of_lt_succ fun j => ?_
      have hlt_R : (H (j + k₀ + 1) : ℝ) < (H (j + 1 + k₀ + 1) : ℝ) := by
        have hidx : j + 1 + k₀ + 1 = (j + k₀ + 1) + 1 := by omega
        rw [hidx, hH_binet (j + k₀ + 1), hH_binet ((j + k₀ + 1) + 1)]
        rw [div_lt_div_iff_of_pos_right hrs_pos]
        have hdiff : ((r - 1) * r ^ ((j + k₀ + 1) + 1) + (1 - s) * s ^ ((j + k₀ + 1) + 1)) -
            ((r - 1) * r ^ (j + k₀ + 1) + (1 - s) * s ^ (j + k₀ + 1)) =
            (r - 1) ^ 2 * r ^ (j + k₀ + 1) - (1 - s) ^ 2 * s ^ (j + k₀ + 1) := by
          rw [pow_succ, pow_succ]; ring
        have hr_ge : r ^ k₀ ≤ r ^ (j + k₀ + 1) :=
          pow_le_pow_right₀ hr.le (by omega)
        have hs_le1 : s ^ (j + k₀ + 1) ≤ 1 :=
          pow_le_one₀ hs_pos.le hs_lt1.le
        have hterm1 : (1 - s) ^ 2 < (r - 1) ^ 2 * r ^ (j + k₀ + 1) :=
          lt_of_lt_of_le hk₀ (mul_le_mul_of_nonneg_left hr_ge (sq_nonneg _))
        have hterm2 : (1 - s) ^ 2 * s ^ (j + k₀ + 1) ≤ (1 - s) ^ 2 := by
          nlinarith [sq_nonneg (1 - s)]
        linarith
      have hlt_Z : H (j + k₀ + 1) < H (j + 1 + k₀ + 1) := by exact_mod_cast hlt_R
      have : (u j : ℤ) < (u (j + 1) : ℤ) := by rw [hu_cast, hu_cast]; exact hlt_Z
      exact_mod_cast this
    · intro j
      let n : ℕ := (H (j + k₀)).toNat
      have hn_cast : (n : ℤ) = H (j + k₀) :=
        Int.toNat_of_nonneg (by linarith [hH_pos (j + k₀)])
      have hn_pos : 1 ≤ n := by
        have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_cast]; exact hH_pos (j + k₀)
        exact_mod_cast this
      refine ⟨n, hn_pos, ?_⟩
      have hmul := hH_mul (j + k₀)
      have hnr : (n : ℝ) * r = (u j : ℝ) + (1 - s) * s ^ (j + k₀) := by
        have hnR : (n : ℝ) = (H (j + k₀) : ℝ) := by exact_mod_cast hn_cast
        have huR : (u j : ℝ) = (H (j + k₀ + 1) : ℝ) := by exact_mod_cast hu_cast j
        rw [hnR, huR]
        linarith
      have herr_nn : 0 ≤ (1 - s) * s ^ (j + k₀) :=
        mul_nonneg (by linarith) (pow_nonneg hs_pos.le _)
      have herr_lt1 : (1 - s) * s ^ (j + k₀) < 1 := by
        have hs_le1 : s ^ (j + k₀) ≤ 1 := pow_le_one₀ hs_pos.le hs_lt1.le
        nlinarith
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> linarith
    · intro j
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, add_zero, ↓reduceIte, Fin.one_eq_zero_iff,
        OfNat.ofNat_ne_one]
      rw [hu_cast (j + 2), hu_cast j, hu_cast (j + 1)]
      have hidx1 : j + 2 + k₀ + 1 = (j + k₀ + 1) + 2 := by omega
      have hidx2 : j + 1 + k₀ + 1 = (j + k₀ + 1) + 1 := by omega
      rw [hidx1, hidx2, hH_rec (j + k₀ + 1)]
      ring

private lemma not_isSquare_add_four {m : ℕ} (hm : 1 ≤ m) :
    ¬ IsSquare (m ^ 2 + 4) := by
  rintro ⟨k, hk⟩
  have h1 : m * m < k * k := by nlinarith
  have h2 : m < k := by nlinarith
  rcases eq_or_lt_of_le hm with rfl | hm2
  · have : k * k = 5 := by linarith
    have hk_le : k ≤ 2 := by nlinarith
    have hk2 : k = 2 := by omega
    subst hk2
    norm_num at hk
  · have h3 : k * k < (m + 1) * (m + 1) := by nlinarith
    have h4 : k < m + 1 := by nlinarith
    omega

/-- Every metallic mean `r_m = (m + √(m^2 + 4)) / 2` (`m ≥ 1`) is irrational. -/
theorem ppl034_metallic_mean_irrational {m : ℕ} (hm : 1 ≤ m) :
    Irrational (((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 + 4)) / 2) := by
  have hsq : Irrational (Real.sqrt ((m ^ 2 + 4 : ℕ) : ℝ)) := by
    rw [irrational_sqrt_natCast_iff]
    exact not_isSquare_add_four hm
  have hcast : ((m ^ 2 + 4 : ℕ) : ℝ) = (m : ℝ) ^ 2 + 4 := by push_cast; ring
  rw [hcast] at hsq
  rintro ⟨q, hq⟩
  have hrat : ((2 * q - (m : ℚ) : ℚ) : ℝ) = Real.sqrt ((m : ℝ) ^ 2 + 4) := by
    push_cast
    linarith
  exact hsq ⟨2 * q - (m : ℚ), hrat⟩

private lemma metallic_mean_props {m : ℕ} (hm : 1 ≤ m) :
    let r : ℝ := ((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 + 4)) / 2
    (m : ℝ) < r ∧ r < (m : ℝ) + 1 ∧ 1 < r ∧
    r ^ 2 = (m : ℝ) * r + 1 ∧
    |(m : ℝ) - r| < 1 := by
  intro r
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnn : (0 : ℝ) ≤ (m : ℝ) ^ 2 + 4 := by positivity
  have hsq : Real.sqrt ((m : ℝ) ^ 2 + 4) ^ 2 = (m : ℝ) ^ 2 + 4 := Real.sq_sqrt hnn
  have hrt_gt : (m : ℝ) < Real.sqrt ((m : ℝ) ^ 2 + 4) := by
    rw [Real.lt_sqrt (by linarith)]; linarith
  have hrt_lt : Real.sqrt ((m : ℝ) ^ 2 + 4) < (m : ℝ) + 2 := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  have hr_gt : (m : ℝ) < r := by simp only [r]; linarith
  have hr_lt : r < (m : ℝ) + 1 := by simp only [r]; linarith
  have hr1 : 1 < r := by linarith
  have hquad : r ^ 2 = (m : ℝ) * r + 1 := by
    simp only [r]
    nlinarith [hsq]
  have habs : |(m : ℝ) - r| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  exact ⟨hr_gt, hr_lt, hr1, hquad, habs⟩

/-- **Metallic Means Positive Recurrence Theorem:**
For every `m ≥ 1`, letting `r_m = (m + √(m^2 + 4)) / 2`, the Beatty sequence `{⌊n r_m⌋₊ : n ≥ 1}`
contains a strictly increasing bisected metallic-Fibonacci sequence `u` with `u 0 = m`,
`u 1 = m^3 + 2 m`, satisfying the order-2 homogeneous linear recurrence
`u (k + 2) = (m^2 + 2) * u (k + 1) - u k`. -/
theorem ppl034_metallic_mean_contains_bisected_recurrence {m : ℕ} (hm : 1 ≤ m) :
    let r : ℝ := ((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 + 4)) / 2
    ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
      StrictMono u ∧
      u 0 = m ∧
      u 1 = m ^ 3 + 2 * m ∧
      c 0 = -1 ∧ c 1 = (m : ℤ) ^ 2 + 2 ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
      (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  intro r
  obtain ⟨hr_gt, hr_lt, hr1, hquad, habs⟩ := metallic_mean_props hm
  change (m : ℝ) < r at hr_gt
  change r < (m : ℝ) + 1 at hr_lt
  change 1 < r at hr1
  change r ^ 2 = (m : ℝ) * r + 1 at hquad
  set s : ℝ := (m : ℝ) - r
  have hrs : r + s = ((m : ℤ) : ℝ) := by simp [s]
  have hprod : r * s = -((1 : ℤ) : ℝ) := by simp only [s]; push_cast; linarith
  have hs_neg : s < 0 := by simp only [s]; linarith
  have hs_abs : |s| < 1 := habs
  have hne : r ≠ s := by linarith
  have hrs_pos : 0 < r - s := by linarith
  have hG_odd_pos : ∀ j : ℕ, 1 ≤ quadRec (m : ℤ) 1 (2 * j + 1) := by
    intro j
    have hval := quadRec_binet hrs hprod hne (2 * j + 1)
    have hr_pow : 1 < r ^ (2 * j + 1) := one_lt_pow₀ hr1 (by omega)
    have hs_pow_neg : s ^ (2 * j + 1) < 0 := Odd.pow_neg ⟨j, rfl⟩ hs_neg
    have hpos : (0 : ℝ) < (quadRec (m : ℤ) 1 (2 * j + 1) : ℝ) := by
      rw [hval]; exact div_pos (by linarith) hrs_pos
    have hint : (0 : ℤ) < quadRec (m : ℤ) 1 (2 * j + 1) := by exact_mod_cast hpos
    omega
  have hG_even_pos : ∀ j : ℕ, 1 ≤ quadRec (m : ℤ) 1 (2 * j + 2) := by
    intro j
    have hval := quadRec_binet hrs hprod hne (2 * j + 2)
    have hr_pow : 1 < r ^ (2 * j + 2) := one_lt_pow₀ hr1 (by omega)
    have hs_pow_lt1 : s ^ (2 * j + 2) < 1 := by
      have h1 : |s ^ (2 * j + 2)| < 1 := by
        rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg s) hs_abs (by omega)
      linarith [le_abs_self (s ^ (2 * j + 2))]
    have hpos : (0 : ℝ) < (quadRec (m : ℤ) 1 (2 * j + 2) : ℝ) := by
      rw [hval]; exact div_pos (by linarith) hrs_pos
    have hint : (0 : ℤ) < quadRec (m : ℤ) 1 (2 * j + 2) := by exact_mod_cast hpos
    omega
  let u : ℕ → ℕ := fun j => (quadRec (m : ℤ) 1 (2 * j + 2)).toNat
  have hu_cast : ∀ j : ℕ, (u j : ℤ) = quadRec (m : ℤ) 1 (2 * j + 2) := fun j =>
    Int.toNat_of_nonneg (by linarith [hG_even_pos j])
  have hu0 : u 0 = m := by
    have : (u 0 : ℤ) = (m : ℤ) := by rw [hu_cast 0]; simp [quadRec]
    exact_mod_cast this
  have hu1 : u 1 = m ^ 3 + 2 * m := by
    have : (u 1 : ℤ) = ((m ^ 3 + 2 * m : ℕ) : ℤ) := by
      rw [hu_cast 1]; simp [quadRec]; ring
    exact_mod_cast this
  refine ⟨u, fun i => if i = 0 then -1 else (m : ℤ) ^ 2 + 2, ?_, hu0, hu1, by simp, by simp, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun j => ?_
    have hlt_R : (quadRec (m : ℤ) 1 (2 * j + 2) : ℝ) < (quadRec (m : ℤ) 1 (2 * (j + 1) + 2) : ℝ) := by
      rw [quadRec_binet hrs hprod hne (2 * j + 2), quadRec_binet hrs hprod hne (2 * (j + 1) + 2)]
      rw [div_lt_div_iff_of_pos_right hrs_pos]
      have hr_pow_pos : 0 < r ^ (2 * j + 2) := pow_pos (by linarith) _
      have hr2_gt1 : 1 < r ^ 2 := by nlinarith
      have hs2_lt1 : s ^ 2 < 1 := by
        have h1 : |s| < 1 := hs_abs
        nlinarith [(abs_lt.mp h1).1, (abs_lt.mp h1).2]
      have hs_even_nn : 0 ≤ s ^ (2 * j + 2) := Even.pow_nonneg ⟨j + 1, by omega⟩ s
      have hdiff : (r ^ (2 * (j + 1) + 2) - s ^ (2 * (j + 1) + 2)) -
          (r ^ (2 * j + 2) - s ^ (2 * j + 2)) =
          r ^ (2 * j + 2) * (r ^ 2 - 1) + s ^ (2 * j + 2) * (1 - s ^ 2) := by
        have h1 : 2 * (j + 1) + 2 = (2 * j + 2) + 2 := by omega
        rw [h1, pow_add, pow_add]; ring
      nlinarith
    have hlt_Z : quadRec (m : ℤ) 1 (2 * j + 2) < quadRec (m : ℤ) 1 (2 * (j + 1) + 2) := by
      exact_mod_cast hlt_R
    have : (u j : ℤ) < (u (j + 1) : ℤ) := by rw [hu_cast, hu_cast]; exact hlt_Z
    exact_mod_cast this
  · intro j
    let n : ℕ := (quadRec (m : ℤ) 1 (2 * j + 1)).toNat
    have hn_cast : (n : ℤ) = quadRec (m : ℤ) 1 (2 * j + 1) :=
      Int.toNat_of_nonneg (by linarith [hG_odd_pos j])
    have hn_pos : 1 ≤ n := by
      have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_cast]; exact hG_odd_pos j
      exact_mod_cast this
    refine ⟨n, hn_pos, ?_⟩
    have hmul := quadRec_mul_sub hrs hprod hne (2 * j + 1)
    have hnr : (n : ℝ) * r = (u j : ℝ) + (-(s ^ (2 * j + 1))) := by
      have hnR : (n : ℝ) = (quadRec (m : ℤ) 1 (2 * j + 1) : ℝ) := by exact_mod_cast hn_cast
      have huR : (u j : ℝ) = (quadRec (m : ℤ) 1 (2 * j + 2) : ℝ) := by exact_mod_cast hu_cast j
      rw [hnR, huR]
      linarith
    have herr_pos : 0 < -(s ^ (2 * j + 1)) := by
      have : s ^ (2 * j + 1) < 0 := Odd.pow_neg ⟨j, rfl⟩ hs_neg
      linarith
    have herr_lt1 : -(s ^ (2 * j + 1)) < 1 := by
      have h1 : |s ^ (2 * j + 1)| < 1 := by
        rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg s) hs_abs (by omega)
      linarith [(abs_lt.mp h1).1]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  · intro j
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, add_zero, ↓reduceIte, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one]
    rw [hu_cast (j + 2), hu_cast j, hu_cast (j + 1)]
    have hbis := quadRec_bisect (a := (m : ℤ)) (b := 1) (2 * j + 2)
    have hidx1 : 2 * (j + 2) + 2 = (2 * j + 2) + 4 := by omega
    have hidx2 : 2 * (j + 1) + 2 = (2 * j + 2) + 2 := by omega
    rw [hidx1, hidx2, hbis]
    ring

/-- **Sharp Conjugate-Sign Obstruction for Metallic Means:**
For EVERY `m ≥ 1` and `r_m = (m + √(m^2 + 4)) / 2`, NO nonzero sequence `u : ℕ → ℕ`
satisfying the unbisected recurrence `u (k + 2) = m * u (k + 1) + u k` can be contained in
the Beatty sequence `{⌊n r_m⌋₊ : n ≥ 1}` (even starting from `k ≥ 1`). Because `s_m = -1 / r_m < 0`,
`fract(-u_k / r_m)` alternates between `(0, 1 / r_m)` and `(1 - ε, 1)`. -/
theorem ppl034_metallic_mean_no_unbisected_recurrence {m : ℕ} (hm : 1 ≤ m) (u : ℕ → ℕ)
    (hne0 : ∃ k : ℕ, 0 < u k) (hrec : ∀ k : ℕ, u (k + 2) = m * u (k + 1) + u k) :
    let r : ℝ := ((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 + 4)) / 2
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, 1 ≤ n → Nat.floor ((n : ℝ) * r) ≠ u k := by
  intro r
  obtain ⟨hr_gt, hr_lt, hr1, hquad, habs⟩ := metallic_mean_props hm
  change (m : ℝ) < r at hr_gt
  change r < (m : ℝ) + 1 at hr_lt
  change 1 < r at hr1
  change r ^ 2 = (m : ℝ) * r + 1 at hquad
  have hirr : Irrational r := ppl034_metallic_mean_irrational hm
  set s : ℝ := (m : ℝ) - r
  have hs_eq : s = -(1 / r) := by
    have hr_ne : r ≠ 0 := by linarith
    have hprod : r * s = -1 := by simp only [s]; linarith
    field_simp [hr_ne]
    linarith
  have hs_neg : s < 0 := by simp only [s]; linarith
  have hs_abs : |s| < 1 := habs
  have hs_irr : Irrational s := by
    rintro ⟨q, hq⟩
    exact hirr ⟨(m : ℚ) - q, by push_cast; rw [hq]; simp [s]⟩
  set γ : ℝ := (u 0 : ℝ) * s + (u 1 : ℝ) - (m : ℝ) * (u 0 : ℝ)
  have hmod : ∀ k : ℕ, ∃ z : ℤ, (u k : ℝ) * s = (z : ℝ) + γ * s ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 =>
        refine ⟨(m : ℤ) * (u 0 : ℤ) - (u 1 : ℤ), ?_⟩
        simp only [γ, pow_zero, mul_one, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        ring
      | 1 =>
        refine ⟨-(u 0 : ℤ), ?_⟩
        have hs2 : s ^ 2 = (m : ℝ) * s + 1 := by simp only [s]; nlinarith
        simp only [γ, pow_one, Int.cast_neg, Int.cast_natCast]
        nlinarith [hs2]
      | k + 2 =>
        rcases ih (k + 1) (by omega) with ⟨z1, hz1⟩
        rcases ih k (by omega) with ⟨z0, hz0⟩
        refine ⟨(m : ℤ) * z1 + z0, ?_⟩
        have hs2 : s ^ 2 = (m : ℝ) * s + 1 := by simp only [s]; nlinarith
        have hrecR : (u (k + 2) : ℝ) = (m : ℝ) * (u (k + 1) : ℝ) + (u k : ℝ) := by
          exact_mod_cast hrec k
        push_cast
        calc (u (k + 2) : ℝ) * s
            = (m : ℝ) * ((u (k + 1) : ℝ) * s) + (u k : ℝ) * s := by rw [hrecR]; ring
          _ = (m : ℝ) * ((z1 : ℝ) + γ * s ^ (k + 1)) + ((z0 : ℝ) + γ * s ^ k) := by rw [hz1, hz0]
          _ = ((m : ℝ) * (z1 : ℝ) + (z0 : ℝ)) + γ * s ^ k * ((m : ℝ) * s + 1) := by
              rw [pow_succ]; ring
          _ = ((m : ℝ) * (z1 : ℝ) + (z0 : ℝ)) + γ * s ^ k * s ^ 2 := by rw [← hs2]
          _ = ((m : ℝ) * (z1 : ℝ) + (z0 : ℝ)) + γ * s ^ (k + 2) := by
              rw [pow_add]; ring
  -- Prove `u 0 ≠ 0 ∨ u 1 ≠ 0`
  have hu01 : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra hboth
    push Not at hboth
    have hall0 : ∀ k : ℕ, u k = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        match k with
        | 0 => exact hboth.1
        | 1 => exact hboth.2
        | k + 2 => rw [hrec k, ih (k + 1) (by omega), ih k (by omega)]; simp
    rcases hne0 with ⟨k, hk⟩
    have := hall0 k
    omega
  -- Prove `γ ≠ 0`
  have hγ_ne : γ ≠ 0 := by
    intro h0
    rcases hu01 with h0ne | h1ne
    · have hu0_ne : (u 0 : ℝ) ≠ 0 := by exact_mod_cast h0ne
      refine hs_irr ⟨(((m : ℤ) * (u 0 : ℤ) - (u 1 : ℤ) : ℤ) : ℚ) / ((u 0 : ℤ) : ℚ), ?_⟩
      push_cast
      have hmul : (u 0 : ℝ) * s = (m : ℝ) * (u 0 : ℝ) - (u 1 : ℝ) := by
        simp only [γ] at h0; linarith
      rw [← hmul, mul_div_cancel_left₀ s hu0_ne]
    · by_cases hu0z : u 0 = 0
      · simp only [γ, hu0z, Nat.cast_zero, zero_mul, zero_add, mul_zero, sub_zero] at h0
        have : u 1 = 0 := by exact_mod_cast h0
        exact h1ne this
      · have hu0_ne : (u 0 : ℝ) ≠ 0 := by exact_mod_cast hu0z
        refine hs_irr ⟨(((m : ℤ) * (u 0 : ℤ) - (u 1 : ℤ) : ℤ) : ℚ) / ((u 0 : ℤ) : ℚ), ?_⟩
        push_cast
        have hmul : (u 0 : ℝ) * s = (m : ℝ) * (u 0 : ℝ) - (u 1 : ℝ) := by
          simp only [γ] at h0; linarith
        rw [← hmul, mul_div_cancel_left₀ s hu0_ne]
  -- For `k ≥ 2`, `u k ≥ 1`
  have hu_pos2 : ∀ k : ℕ, 2 ≤ k → 1 ≤ u k := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => omega
      | 1 => omega
      | 2 =>
        have h2 : u 2 = m * u 1 + u 0 := hrec 0
        rcases hu01 with h0ne | h1ne
        · have : 1 ≤ u 0 := Nat.pos_of_ne_zero h0ne; omega
        · have : 1 ≤ m * u 1 := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero h1ne); omega
      | 3 =>
        have h3 : u 3 = m * u 2 + u 1 := hrec 1
        have h2 : u 2 = m * u 1 + u 0 := hrec 0
        rcases hu01 with h0ne | h1ne
        · have hu2 : 1 ≤ u 2 := by have : 1 ≤ u 0 := Nat.pos_of_ne_zero h0ne; omega
          have : 1 ≤ m * u 2 := Nat.mul_pos (by omega) hu2
          omega
        · have : 1 ≤ u 1 := Nat.pos_of_ne_zero h1ne; omega
      | k + 4 =>
        have h4 : u (k + 4) = m * u (k + 3) + u (k + 2) := hrec (k + 2)
        have hih := ih (k + 3) (by omega) (by omega)
        have : 1 ≤ m * u (k + 3) := Nat.mul_pos (by omega) hih
        omega
  -- Choose `K ≥ 2` such that `|γ| * |s| ^ K < 1 - 1 / r`
  have hgap_pos : 0 < 1 - 1 / r := by
    have : 1 / r < 1 := (div_lt_one (by linarith)).mpr hr1
    linarith
  have htend : Tendsto (fun k : ℕ => |γ| * |s| ^ k) atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg s) hs_abs
    simpa using h1.const_mul |γ|
  have hev := (Metric.tendsto_atTop.mp htend) (1 - 1 / r) hgap_pos
  rcases hev with ⟨K₀, hK₀⟩
  set K : ℕ := max K₀ 2
  -- Pick `k ∈ {K, K + 1}` such that `γ * s ^ k < 0`
  have hex_neg : ∃ k : ℕ, K ≤ k ∧ γ * s ^ k < 0 := by
    rcases lt_or_gt_of_ne hγ_ne with hγ_neg | hγ_pos
    · by_cases hK_even : Even K
      · refine ⟨K, le_rfl, ?_⟩
        have hs_pos : 0 < s ^ K := by
          rcases hK_even with ⟨t, ht⟩
          rw [ht, show t + t = 2 * t by omega, pow_mul, sq]
          exact pow_pos (mul_pos_of_neg_of_neg hs_neg hs_neg) t
        exact mul_neg_of_neg_of_pos hγ_neg hs_pos
      · refine ⟨K + 1, by omega, ?_⟩
        have hK1_even : Even (K + 1) := by
          rw [Nat.not_even_iff_odd] at hK_even
          exact hK_even.add_one
        have hs_pos : 0 < s ^ (K + 1) := by
          rcases hK1_even with ⟨t, ht⟩
          rw [ht, show t + t = 2 * t by omega, pow_mul, sq]
          exact pow_pos (mul_pos_of_neg_of_neg hs_neg hs_neg) t
        exact mul_neg_of_neg_of_pos hγ_neg hs_pos
    · by_cases hK_odd : Odd K
      · refine ⟨K, le_rfl, ?_⟩
        exact mul_neg_of_pos_of_neg hγ_pos (hK_odd.pow_neg hs_neg)
      · refine ⟨K + 1, by omega, ?_⟩
        have hK1_odd : Odd (K + 1) := by
          rw [Nat.not_odd_iff_even] at hK_odd
          exact hK_odd.add_one
        exact mul_neg_of_pos_of_neg hγ_pos (hK1_odd.pow_neg hs_neg)
  rcases hex_neg with ⟨k, hk_ge, hneg_term⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right K₀ 2) hk_ge
  have hk1 : 1 ≤ k := by omega
  have hsmall : |γ| * |s| ^ k < 1 - 1 / r := by
    have hdist := hK₀ k (le_trans (le_max_left K₀ 2) hk_ge)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))] at hdist
    exact hdist
  have hsmall_term : -(1 - 1 / r) < γ * s ^ k := by
    have hab : |γ * s ^ k| = |γ| * |s| ^ k := by rw [abs_mul, abs_pow]
    linarith [(abs_lt.mp (by rw [hab]; exact hsmall)).1]
  refine ⟨k, hk1, fun n hn hfl => ?_⟩
  have hmem_fr := (ppl034_beatty_mem_iff_neg_fract hr1 (hu_pos2 k hk2)).mp ⟨n, hn, hfl⟩
  have harg : -((u k : ℝ) / r) = (u k : ℝ) * s := by
    rw [hs_eq]; ring
  rw [harg] at hmem_fr
  rcases hmod k with ⟨z, hz⟩
  rw [hz, add_comm, Int.fract_add_intCast] at hmem_fr
  -- Since `-(1 - 1/r) < γ * s^k < 0`, `Int.fract (γ * s^k) = γ * s^k + 1 > 1 / r`!
  have hfl_neg1 : Int.floor (γ * s ^ k) = -1 := by
    rw [Int.floor_eq_iff]
    push_cast
    have hinv_pos : 0 < 1 / r := one_div_pos.mpr (by linarith)
    constructor <;> linarith
  have hfr_val : Int.fract (γ * s ^ k) = γ * s ^ k + 1 := by
    show γ * s ^ k - (Int.floor (γ * s ^ k) : ℝ) = _
    rw [hfl_neg1]; push_cast; ring
  rw [hfr_val] at hmem_fr
  linarith

/-- **Golden Ratio (`φ = (1 + √5) / 2`) Even-Fibonacci Recurrence Theorem:**
`φ` is irrational and `{⌊n φ⌋₊ : n ≥ 1}` contains the strictly increasing even-Fibonacci
sequence `1, 3, 8, 21, 55, ...` satisfying `u (k + 2) = 3 * u (k + 1) - u k`. -/
theorem ppl034_golden_ratio_even_fib_recurrence :
    let φ : ℝ := (1 + Real.sqrt 5) / 2
    Irrational φ ∧
    ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
      StrictMono u ∧
      u 0 = 1 ∧ u 1 = 3 ∧
      c 0 = -1 ∧ c 1 = 3 ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * φ) = u k) ∧
      (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  have h5 : ((1 : ℕ) : ℝ) ^ 2 + 4 = (5 : ℝ) := by norm_num
  have hphi : (((1 : ℕ) : ℝ) + Real.sqrt (((1 : ℕ) : ℝ) ^ 2 + 4)) / 2 = (1 + Real.sqrt 5) / 2 := by
    rw [h5]; norm_num
  refine ⟨?_, ?_⟩
  · simpa only [hphi] using ppl034_metallic_mean_irrational (m := 1) (le_refl 1)
  · rcases ppl034_metallic_mean_contains_bisected_recurrence (m := 1) (le_refl 1) with
      ⟨u, c, hmono, hu0, hu1, hc0, hc1, hmem, hrec⟩
    rw [hphi] at hmem
    exact ⟨u, c, hmono, hu0, by norm_num at hu1; exact hu1, hc0, by norm_num at hc1; exact hc1,
      hmem, hrec⟩

/-- **Golden Ratio Wythoff Order-4 Recurrence Theorem:**
The full shifted Wythoff-Fibonacci Beatty sequence `v k = ⌊F_{k+2} φ⌋₊` (`1, 3, 4, 8, 12, 21, ...`)
is strictly increasing, contained in `{⌊n φ⌋₊ : n ≥ 1}`, and satisfies the order-4 homogeneous
linear recurrence `v (k + 4) = v (k + 3) + 2 v (k + 2) - v (k + 1) - v k`. -/
theorem ppl034_golden_ratio_wythoff_order4_recurrence :
    let φ : ℝ := (1 + Real.sqrt 5) / 2
    ∃ (v : ℕ → ℕ) (c : Fin 4 → ℤ),
      StrictMono v ∧
      v 0 = 1 ∧ v 1 = 3 ∧ v 2 = 4 ∧ v 3 = 8 ∧
      c 0 = -1 ∧ c 1 = -1 ∧ c 2 = 2 ∧ c 3 = 1 ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * φ) = v k) ∧
      (∀ k : ℕ, (v (k + 4) : ℤ) = ∑ j : Fin 4, c j * (v (k + j) : ℤ)) := by
  intro φ
  set s : ℝ := 1 - φ
  have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hphi_gt1 : 1 < φ := by
    have : 1 < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    simp only [φ]; linarith
  have hphi_lt2 : φ < 2 := by
    have : Real.sqrt 5 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    simp only [φ]; linarith
  have hquad : φ ^ 2 = φ + 1 := by simp only [φ]; nlinarith [hsq5]
  have hrs : φ + s = ((1 : ℤ) : ℝ) := by simp [s]
  have hprod : φ * s = -((1 : ℤ) : ℝ) := by simp only [s]; push_cast; linarith
  have hs_neg : s < 0 := by simp only [s]; linarith
  have hs_gt_neg1 : -1 < s := by simp only [s]; linarith
  have hs_abs : |s| < 1 := abs_lt.mpr ⟨hs_gt_neg1, by linarith⟩
  have hne : φ ≠ s := by linarith
  have hF_pos : ∀ k : ℕ, 1 ≤ k → 1 ≤ quadRec 1 1 k := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => omega
      | 1 => simp [quadRec]
      | 2 => simp [quadRec]
      | k + 3 =>
        have h1 := ih (k + 2) (by omega) (by omega)
        have h2 := ih (k + 1) (by omega) (by omega)
        have : quadRec 1 1 (k + 3) = 1 * quadRec 1 1 (k + 2) + 1 * quadRec 1 1 (k + 1) := rfl
        linarith
  have hF_ge2 : ∀ k : ℕ, 3 ≤ k → 2 ≤ quadRec 1 1 k := by
    intro k hk
    match k with
    | 0 | 1 | 2 => omega
    | k + 3 =>
      have h1 := hF_pos (k + 2) (by omega)
      have h2 := hF_pos (k + 1) (by omega)
      have : quadRec 1 1 (k + 3) = 1 * quadRec 1 1 (k + 2) + 1 * quadRec 1 1 (k + 1) := rfl
      linarith
  let v : ℕ → ℕ := fun k => Nat.floor (((quadRec 1 1 (k + 2)).toNat : ℝ) * φ)
  have hv_formula : ∀ k : ℕ,
      (v k : ℤ) = quadRec 1 1 (k + 3) - if Even k then 1 else 0 := by
    intro k
    have hFk2_cast : ((quadRec 1 1 (k + 2)).toNat : ℤ) = quadRec 1 1 (k + 2) :=
      Int.toNat_of_nonneg (by linarith [hF_pos (k + 2) (by omega)])
    have hFk2_R : ((quadRec 1 1 (k + 2)).toNat : ℝ) = (quadRec 1 1 (k + 2) : ℝ) := by
      exact_mod_cast hFk2_cast
    have hmul := quadRec_mul_sub hrs hprod hne (k + 2)
    have hpow_abs : |s ^ (k + 2)| < 1 := by
      rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg s) hs_abs (by omega)
    by_cases hev : Even k
    · rw [if_pos hev]
      have hpow_pos : 0 < s ^ (k + 2) := by
        rcases hev with ⟨t, rfl⟩
        rw [show t + t + 2 = 2 * (t + 1) by omega, pow_mul, sq]
        exact pow_pos (mul_pos_of_neg_of_neg hs_neg hs_neg) (t + 1)
      have hpow_lt1 : s ^ (k + 2) < 1 := (abs_lt.mp hpow_abs).2
      have hFk3_ge1 : 1 ≤ quadRec 1 1 (k + 3) := hF_pos (k + 3) (by omega)
      have hfl_nat : v k = (quadRec 1 1 (k + 3) - 1).toNat := by
        simp only [v]
        rw [Nat.floor_eq_iff (by positivity), hFk2_R]
        have hcast : ((quadRec 1 1 (k + 3) - 1).toNat : ℝ) = (quadRec 1 1 (k + 3) : ℝ) - 1 := by
          have : ((quadRec 1 1 (k + 3) - 1).toNat : ℤ) = quadRec 1 1 (k + 3) - 1 :=
            Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [hcast]
        constructor <;> linarith
      rw [hfl_nat]
      exact Int.toNat_of_nonneg (by omega)
    · rw [if_neg hev]
      have hodd : Odd (k + 2) := by
        rw [Nat.not_even_iff_odd] at hev
        rcases hev with ⟨t, rfl⟩
        exact ⟨t + 1, by omega⟩
      have hpow_neg : s ^ (k + 2) < 0 := hodd.pow_neg hs_neg
      have hpow_gt_neg1 : -1 < s ^ (k + 2) := (abs_lt.mp hpow_abs).1
      have hFk3_ge1 : 1 ≤ quadRec 1 1 (k + 3) := hF_pos (k + 3) (by omega)
      have hfl_nat : v k = (quadRec 1 1 (k + 3)).toNat := by
        simp only [v]
        rw [Nat.floor_eq_iff (by positivity), hFk2_R]
        have hcast : ((quadRec 1 1 (k + 3)).toNat : ℝ) = (quadRec 1 1 (k + 3) : ℝ) := by
          have : ((quadRec 1 1 (k + 3)).toNat : ℤ) = quadRec 1 1 (k + 3) :=
            Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [hcast]
        constructor <;> linarith
      rw [hfl_nat, sub_zero]
      exact Int.toNat_of_nonneg (by omega)
  let c : Fin 4 → ℤ := fun j =>
    if j = 0 then -1 else if j = 1 then -1 else if j = 2 then 2 else 1
  refine ⟨v, c, ?_, ?_, ?_, ?_, ?_, by simp [c], by simp [c], by simp [c], by simp [c], ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have hlt_Z : (v k : ℤ) < (v (k + 1) : ℤ) := by
      rw [hv_formula k, hv_formula (k + 1)]
      have hstep : quadRec 1 1 (k + 4) = 1 * quadRec 1 1 (k + 3) + 1 * quadRec 1 1 (k + 2) := rfl
      by_cases hev : Even k
      · have hnot : ¬ Even (k + 1) := by
          rcases hev with ⟨t, rfl⟩; intro ⟨u, hu⟩; omega
        rw [if_pos hev, if_neg hnot]
        have hpos := hF_pos (k + 2) (by omega)
        linarith
      · have hev1 : Even (k + 1) := by
          rw [Nat.not_even_iff_odd] at hev; exact hev.add_one
        rw [if_neg hev, if_pos hev1]
        have hk1 : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          rw [hk0] at hev
          exact hev ⟨0, rfl⟩
        have hge2 := hF_ge2 (k + 2) (by omega)
        linarith
    exact_mod_cast hlt_Z
  · have : (v 0 : ℤ) = 1 := by
      have h0 : Even (0 : ℕ) := ⟨0, rfl⟩
      rw [hv_formula 0, if_pos h0]
      simp [quadRec]
    exact_mod_cast this
  · have : (v 1 : ℤ) = 3 := by
      rw [hv_formula 1, if_neg (by rintro ⟨t, ht⟩; omega)]
      simp [quadRec]
    exact_mod_cast this
  · have : (v 2 : ℤ) = 4 := by
      have h2 : Even (2 : ℕ) := ⟨1, rfl⟩
      rw [hv_formula 2, if_pos h2]
      simp [quadRec]
    exact_mod_cast this
  · have : (v 3 : ℤ) = 8 := by
      rw [hv_formula 3, if_neg (by rintro ⟨t, ht⟩; omega)]
      simp [quadRec]
    exact_mod_cast this
  · intro k
    refine ⟨(quadRec 1 1 (k + 2)).toNat, ?_, rfl⟩
    have h1 := hF_pos (k + 2) (by omega)
    omega
  · intro k
    rw [Fin.sum_univ_four]
    have h3val : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [c, Fin.val_zero, Fin.val_one, Fin.val_two, h3val, add_zero, ↓reduceIte,
      Fin.isValue, Fin.reduceEq]
    rw [hv_formula (k + 4), hv_formula k, hv_formula (k + 1), hv_formula (k + 2), hv_formula (k + 3)]
    rw [show k + 4 + 3 = k + 7 by omega, show k + 3 + 3 = k + 6 by omega,
        show k + 2 + 3 = k + 5 by omega, show k + 1 + 3 = k + 4 by omega]
    have hF7 : quadRec 1 1 (k + 7) = 1 * quadRec 1 1 (k + 6) + 1 * quadRec 1 1 (k + 5) := rfl
    have hF5 : quadRec 1 1 (k + 5) = 1 * quadRec 1 1 (k + 4) + 1 * quadRec 1 1 (k + 3) := rfl
    have hp4 : Even (k + 4) ↔ Even k := by
      constructor <;> rintro ⟨t, ht⟩
      · exact ⟨t - 2, by omega⟩
      · exact ⟨t + 2, by omega⟩
    have hp2 : Even (k + 2) ↔ Even k := by
      constructor <;> rintro ⟨t, ht⟩
      · exact ⟨t - 1, by omega⟩
      · exact ⟨t + 1, by omega⟩
    have hp3 : Even (k + 3) ↔ Even (k + 1) := by
      constructor <;> rintro ⟨t, ht⟩
      · exact ⟨t - 1, by omega⟩
      · exact ⟨t + 1, by omega⟩
    simp only [hp4, hp2, hp3]
    by_cases hev : Even k <;> by_cases hev1 : Even (k + 1) <;>
      simp only [hev, hev1, ↓reduceIte] <;> linarith

private lemma not_isSquare_sub_four {a : ℕ} (ha : 3 ≤ a) :
    ¬ IsSquare (a ^ 2 - 4) := by
  rintro ⟨k, hk⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hsq : k * k = (3 + b) ^ 2 - 4 := hk.symm
  have hge4 : 4 ≤ (3 + b) ^ 2 := by nlinarith
  have hk_eq : k * k + 4 = (3 + b) ^ 2 := by omega
  have h1 : (2 + b) * (2 + b) < k * k := by nlinarith
  have h2 : k * k < (3 + b) * (3 + b) := by nlinarith
  have hk_gt : 2 + b < k := by nlinarith
  have hk_lt : k < 3 + b := by nlinarith
  omega

/-- **Positive-Conjugate Quadratic Pisot Unit Family:**
For every `a ≥ 3`, `ρ_a = (a + √(a^2 - 4)) / 2` is irrational (`ρ_a > 1`, conjugate
`σ_a = 1 / ρ_a ∈ (0, 1)`), and `{⌊n ρ_a⌋₊ : n ≥ 1}` directly contains an unbisected
strictly increasing order-2 homogeneous linear recurrence `u (k + 2) = a * u (k + 1) - u k`. -/
theorem ppl034_pos_conj_pisot_contains_recurrence {a : ℕ} (ha : 3 ≤ a) :
    let ρ : ℝ := ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 4)) / 2
    Irrational ρ ∧
    ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
      StrictMono u ∧
      c 0 = -1 ∧ c 1 = (a : ℤ) ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * ρ) = u k) ∧
      (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  intro ρ
  have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hnn : (0 : ℝ) ≤ (a : ℝ) ^ 2 - 4 := by nlinarith
  have hsq : Real.sqrt ((a : ℝ) ^ 2 - 4) ^ 2 = (a : ℝ) ^ 2 - 4 := Real.sq_sqrt hnn
  have hirr : Irrational ρ := by
    have hsqrt : Irrational (Real.sqrt ((a ^ 2 - 4 : ℕ) : ℝ)) := by
      rw [irrational_sqrt_natCast_iff]
      exact not_isSquare_sub_four ha
    have hcast : ((a ^ 2 - 4 : ℕ) : ℝ) = (a : ℝ) ^ 2 - 4 := by
      have hge4 : 4 ≤ a ^ 2 := by nlinarith
      rw [Nat.cast_sub hge4]; push_cast; ring
    rw [hcast] at hsqrt
    rintro ⟨q, hq⟩
    simp only [ρ] at hq
    exact hsqrt ⟨2 * q - (a : ℚ), by push_cast; linarith⟩
  have hrt_gt : (a : ℝ) - 2 < Real.sqrt ((a : ℝ) ^ 2 - 4) := by
    rw [Real.lt_sqrt (by linarith)]; nlinarith
  have hrt_lt : Real.sqrt ((a : ℝ) ^ 2 - 4) < (a : ℝ) := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  have hρ_gt : (a : ℝ) - 1 < ρ := by simp only [ρ]; linarith
  have hρ_lt : ρ < (a : ℝ) := by simp only [ρ]; linarith
  have hρ1 : 1 < ρ := by linarith
  have hquad : ρ ^ 2 = (a : ℝ) * ρ - 1 := by simp only [ρ]; nlinarith [hsq]
  set σ : ℝ := (a : ℝ) - ρ
  have hrs : ρ + σ = ((a : ℤ) : ℝ) := by simp [σ]
  have hprod : ρ * σ = -((-1 : ℤ) : ℝ) := by simp only [σ]; push_cast; linarith
  have hσ_pos : 0 < σ := by simp only [σ]; linarith
  have hσ_lt1 : σ < 1 := by simp only [σ]; linarith
  have hne : ρ ≠ σ := by linarith
  have hrs_pos : 0 < ρ - σ := by linarith
  let H : ℕ → ℤ := fun k => quadRec (a : ℤ) (-1) (k + 1) - quadRec (a : ℤ) (-1) k
  have hH_binet : ∀ k : ℕ, (H k : ℝ) = ((ρ - 1) * ρ ^ k + (1 - σ) * σ ^ k) / (ρ - σ) := by
    intro k
    simp only [H, Int.cast_sub]
    rw [quadRec_binet hrs hprod hne (k + 1), quadRec_binet hrs hprod hne k]
    field_simp [hrs_pos.ne']
    ring
  have hH_pos : ∀ k : ℕ, 1 ≤ H k := by
    intro k
    have hrp : 0 < ρ ^ k := pow_pos (by linarith) k
    have hsp : 0 < σ ^ k := pow_pos hσ_pos k
    have hpos : (0 : ℝ) < (H k : ℝ) := by
      rw [hH_binet]; exact div_pos (by nlinarith) hrs_pos
    have hint : (0 : ℤ) < H k := by exact_mod_cast hpos
    omega
  have hH_mul : ∀ k : ℕ, (H k : ℝ) * ρ - (H (k + 1) : ℝ) = (1 - σ) * σ ^ k := by
    intro k
    simp only [H, Int.cast_sub]
    have h1 := quadRec_mul_sub hrs hprod hne (k + 1)
    have h0 := quadRec_mul_sub hrs hprod hne k
    calc ((quadRec (a : ℤ) (-1) (k + 1) : ℝ) - (quadRec (a : ℤ) (-1) k : ℝ)) * ρ -
            ((quadRec (a : ℤ) (-1) (k + 2) : ℝ) - (quadRec (a : ℤ) (-1) (k + 1) : ℝ))
        = ((quadRec (a : ℤ) (-1) (k + 1) : ℝ) * ρ - (quadRec (a : ℤ) (-1) (k + 2) : ℝ)) -
            ((quadRec (a : ℤ) (-1) k : ℝ) * ρ - (quadRec (a : ℤ) (-1) (k + 1) : ℝ)) := by ring
      _ = -(σ ^ (k + 1)) - -(σ ^ k) := by rw [h1, h0]
      _ = (1 - σ) * σ ^ k := by ring
  have hH_rec : ∀ k : ℕ, H (k + 2) = (a : ℤ) * H (k + 1) - H k := by
    intro k
    simp only [H]
    have h3 : quadRec (a : ℤ) (-1) (k + 3) = (a : ℤ) * quadRec (a : ℤ) (-1) (k + 2) + (-1) * quadRec (a : ℤ) (-1) (k + 1) := rfl
    have h2 : quadRec (a : ℤ) (-1) (k + 2) = (a : ℤ) * quadRec (a : ℤ) (-1) (k + 1) + (-1) * quadRec (a : ℤ) (-1) k := rfl
    linarith
  -- Since `ρ > 2` (as `a ≥ 3` gives `ρ > a - 1 ≥ 2`), `(ρ - 1)^2 > 1 > (1 - σ)^2`, so `H` is strictly increasing from `k = 0`!
  let u : ℕ → ℕ := fun k => (H (k + 1)).toNat
  have hu_cast : ∀ k : ℕ, (u k : ℤ) = H (k + 1) := fun k =>
    Int.toNat_of_nonneg (by linarith [hH_pos (k + 1)])
  refine ⟨hirr, u, fun i => if i = 0 then -1 else (a : ℤ), ?_, by simp, by simp, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have hlt_R : (H (k + 1) : ℝ) < (H (k + 2) : ℝ) := by
      rw [hH_binet (k + 1), hH_binet (k + 2), div_lt_div_iff_of_pos_right hrs_pos]
      have hdiff : ((ρ - 1) * ρ ^ (k + 2) + (1 - σ) * σ ^ (k + 2)) -
          ((ρ - 1) * ρ ^ (k + 1) + (1 - σ) * σ ^ (k + 1)) =
          (ρ - 1) ^ 2 * ρ ^ (k + 1) - (1 - σ) ^ 2 * σ ^ (k + 1) := by
        rw [pow_succ, pow_succ]; ring
      have hρ_ge1 : 1 ≤ ρ ^ (k + 1) := one_le_pow₀ hρ1.le
      have hσ_le1 : σ ^ (k + 1) ≤ 1 := pow_le_one₀ hσ_pos.le hσ_lt1.le
      have h1 : (1 - σ) ^ 2 < 1 := by nlinarith
      have h2 : 1 < (ρ - 1) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (1 - σ)]
    have hlt_Z : H (k + 1) < H (k + 2) := by exact_mod_cast hlt_R
    have : (u k : ℤ) < (u (k + 1) : ℤ) := by rw [hu_cast, hu_cast]; exact hlt_Z
    exact_mod_cast this
  · intro k
    let n : ℕ := (H k).toNat
    have hn_cast : (n : ℤ) = H k := Int.toNat_of_nonneg (by linarith [hH_pos k])
    have hn_pos : 1 ≤ n := by
      have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_cast]; exact hH_pos k
      exact_mod_cast this
    refine ⟨n, hn_pos, ?_⟩
    have hmul := hH_mul k
    have hnr : (n : ℝ) * ρ = (u k : ℝ) + (1 - σ) * σ ^ k := by
      have hnR : (n : ℝ) = (H k : ℝ) := by exact_mod_cast hn_cast
      have huR : (u k : ℝ) = (H (k + 1) : ℝ) := by exact_mod_cast hu_cast k
      rw [hnR, huR]; linarith
    have herr_nn : 0 ≤ (1 - σ) * σ ^ k := mul_nonneg (by linarith) (pow_nonneg hσ_pos.le _)
    have herr_lt1 : (1 - σ) * σ ^ k < 1 := by
      have hσ_le1 : σ ^ k ≤ 1 := pow_le_one₀ hσ_pos.le hσ_lt1.le
      nlinarith
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  · intro k
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, add_zero, ↓reduceIte, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one]
    rw [hu_cast (k + 2), hu_cast k, hu_cast (k + 1)]
    have := hH_rec (k + 1)
    linarith

/-- **Scaling Invariance (`B_{q r} ⊆ B_r`):**
For every `r : ℝ` and positive integer `q ≥ 1`, every element of the Beatty sequence of `q * r`
belongs to the Beatty sequence of `r`. -/
theorem ppl034_beatty_subset_nat_mul {r : ℝ} {q m : ℕ} (hq : 1 ≤ q)
    (hmem : ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * ((q : ℝ) * r)) = m) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = m := by
  rcases hmem with ⟨n, hn, hfl⟩
  refine ⟨n * q, by nlinarith, ?_⟩
  have heq : ((n * q : ℕ) : ℝ) * r = (n : ℝ) * ((q : ℝ) * r) := by push_cast; ring
  rw [heq, hfl]

/-- **Rational-Denominator Quadratic Pisot Theorem:**
For every `r > 1`, `q ≥ 1`, and `a, b : ℤ` such that `q * r^2 = a * r + b` and `|a - q * r| < 1`
(i.e. `q * r` is a quadratic Pisot number), the Beatty sequence `{⌊n r⌋₊ : n ≥ 1}` contains a
strictly increasing order-2 homogeneous linear recurrence. -/
theorem ppl034_rational_denom_quadratic_pisot {r : ℝ} (hr : 1 < r) {q : ℕ} (hq : 1 ≤ q)
    {a b : ℤ} (hquad : (q : ℝ) * r ^ 2 = (a : ℝ) * r + (b : ℝ))
    (hpisot : |(a : ℝ) - (q : ℝ) * r| < 1) :
    ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
      StrictMono u ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
      (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqr1 : 1 < (q : ℝ) * r := by nlinarith
  have hquad_qr : ((q : ℝ) * r) ^ 2 = (a : ℝ) * ((q : ℝ) * r) + ((q : ℤ) * b : ℤ) := by
    push_cast
    nlinarith [hquad]
  rcases ppl034_quadratic_pisot_contains_recurrence hqr1 hquad_qr hpisot with
    ⟨u, c, hmono, hmem, hrec⟩
  exact ⟨u, c, hmono, fun k => ppl034_beatty_subset_nat_mul hq (hmem k), hrec⟩

/-- **Topological Density of Irrational PPL 034 Solutions in `(1, ∞)`:**
Every nonempty open interval `(x, y) ⊆ (1, ∞)` contains an IRRATIONAL real `r` whose Beatty
sequence `{⌊n r⌋₊ : n ≥ 1}` contains a strictly increasing order-2 homogeneous linear recurrence. -/
theorem ppl034_irrational_solutions_dense {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) :
    ∃ r : ℝ, x < r ∧ r < y ∧ Irrational r ∧
      ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
        StrictMono u ∧
        (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
        (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ)) := by
  set q : ℕ := Nat.floor (2 / (y - x)) + 1
  have hq_pos : 1 ≤ q := by omega
  have hq_R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have h2q_lt : 2 / (q : ℝ) < y - x := by
    have hlt : 2 / (y - x) < (q : ℝ) := by
      simp only [q]; push_cast; exact Nat.lt_floor_add_one _
    have hyx : 0 < y - x := by linarith
    have hmul : 2 < (q : ℝ) * (y - x) := (div_lt_iff₀ hyx).mp hlt
    exact (div_lt_iff₀ hq_R).mpr (by linarith)
  set m : ℕ := Nat.floor (x * (q : ℝ)) + 1
  have hm_pos : 1 ≤ m := by omega
  have hx_lt_m : x * (q : ℝ) < (m : ℝ) := by
    simp only [m]; push_cast; exact Nat.lt_floor_add_one _
  have hm1_le : (m : ℝ) + 1 ≤ x * (q : ℝ) + 2 := by
    have hfl : (Nat.floor (x * (q : ℝ)) : ℝ) ≤ x * (q : ℝ) :=
      Nat.floor_le (by positivity)
    simp only [m]; push_cast; linarith
  set α : ℝ := ((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 + 4)) / 2
  set r : ℝ := α / (q : ℝ)
  obtain ⟨hα_gt, hα_lt, _, _, _⟩ := metallic_mean_props hm_pos
  change (m : ℝ) < α at hα_gt
  change α < (m : ℝ) + 1 at hα_lt
  have hα_irr : Irrational α := ppl034_metallic_mean_irrational hm_pos
  have hr_gt_x : x < r := by
    simp only [r]
    rw [lt_div_iff₀ hq_R]
    linarith
  have hr_lt_y : r < y := by
    simp only [r]
    rw [div_lt_iff₀ hq_R]
    have h2 : 2 < (y - x) * (q : ℝ) := (div_lt_iff₀ hq_R).mp h2q_lt
    linarith
  have hr_irr : Irrational r := by
    rintro ⟨t, ht⟩
    have hrat : ((t * (q : ℚ) : ℚ) : ℝ) = α := by
      push_cast; rw [ht]; simp only [r]; field_simp [hq_R.ne']
    exact hα_irr ⟨t * (q : ℚ), hrat⟩
  rcases ppl034_metallic_mean_contains_bisected_recurrence hm_pos with
    ⟨u, c, hmono, _, _, _, _, hmem, hrec⟩
  have hqr_eq : (q : ℝ) * r = α := mul_div_cancel₀ α hq_R.ne'
  refine ⟨r, hr_gt_x, hr_lt_y, hr_irr, u, c, hmono, ?_, hrec⟩
  intro k
  apply ppl034_beatty_subset_nat_mul hq_pos
  rw [hqr_eq]
  exact hmem k

/-- **Infinitely Many Irrational Solutions to PPL 034:**
The set of irrational `r > 1` whose Beatty sequence contains a strictly increasing order-2
homogeneous linear recurrence is infinite. -/
theorem ppl034_infinitely_many_irrationals :
    Set.Infinite {r : ℝ | 1 < r ∧ Irrational r ∧
      ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
        StrictMono u ∧
        (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
        (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ))} := by
  let f : ℕ → ℝ := fun m => (((m + 1 : ℕ) : ℝ) + Real.sqrt (((m + 1 : ℕ) : ℝ) ^ 2 + 4)) / 2
  have hf_inj : Function.Injective f := by
    intro a b hab
    have ha := metallic_mean_props (m := a + 1) (by omega)
    have hb := metallic_mean_props (m := b + 1) (by omega)
    have hlt1 : ((a + 1 : ℕ) : ℝ) < ((b + 1 : ℕ) : ℝ) + 1 := by
      have : f a = f b := hab; simp only [f] at this; linarith [ha.1, hb.2.1]
    have hlt2 : ((b + 1 : ℕ) : ℝ) < ((a + 1 : ℕ) : ℝ) + 1 := by
      have : f a = f b := hab; simp only [f] at this; linarith [hb.1, ha.2.1]
    have h1 : a + 1 < b + 2 := by exact_mod_cast hlt1
    have h2 : b + 1 < a + 2 := by exact_mod_cast hlt2
    omega
  have hf_mem : Set.range f ⊆ {r : ℝ | 1 < r ∧ Irrational r ∧
      ∃ (u : ℕ → ℕ) (c : Fin 2 → ℤ),
        StrictMono u ∧
        (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
        (∀ k : ℕ, (u (k + 2) : ℤ) = ∑ j : Fin 2, c j * (u (k + j) : ℤ))} := by
    rintro _ ⟨m, rfl⟩
    have hp := metallic_mean_props (m := m + 1) (by omega)
    have hirr := ppl034_metallic_mean_irrational (m := m + 1) (by omega)
    rcases ppl034_metallic_mean_contains_bisected_recurrence (m := m + 1) (by omega) with
      ⟨u, c, hmono, _, _, _, _, hmem, hrec⟩
    exact ⟨hp.2.2.1, hirr, u, c, hmono, hmem, hrec⟩
  exact (Set.infinite_range_of_injective hf_inj).mono hf_mem

/-! ## Section 4: Uncountable Cantor Family & Explicit Transcendental Solution -/

/-- **Base-`b` Geometric Progression Criterion:**
For every `r > 1` and integer base `b ≥ 2`, the geometric progression `{b^k : k ∈ ℕ}`
lies inside the Beatty sequence `{⌊n r⌋₊ : n ≥ 1}` if and only if
`Int.fract (b^k * (1 - 1 / r)) < 1 / r` for every `k : ℕ`. -/
theorem ppl034_geom_prog_iff_fract {r : ℝ} (hr : 1 < r) {b : ℕ} (hb : 2 ≤ b) :
    (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = b ^ k) ↔
      ∀ k : ℕ, Int.fract ((b : ℝ) ^ k * (1 - 1 / r)) < 1 / r := by
  constructor
  · intro h k
    have hbk_pos : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
    have hfr := (ppl034_beatty_mem_iff_neg_fract hr hbk_pos).mp (h k)
    have heq : (b : ℝ) ^ k * (1 - 1 / r) = -(((b ^ k : ℕ) : ℝ) / r) + ((b ^ k : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, Int.fract_add_intCast]
    exact hfr
  · intro h k
    have hbk_pos : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
    rw [ppl034_beatty_mem_iff_neg_fract hr hbk_pos]
    have hfr := h k
    have heq : (b : ℝ) ^ k * (1 - 1 / r) = -(((b ^ k : ℕ) : ℝ) / r) + ((b ^ k : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, Int.fract_add_intCast] at hfr
    exact hfr

private lemma summable_inv_four_pow : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ j) := by
  have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ j) = fun j : ℕ => ((1 : ℝ) / 4) ^ j := by
    funext j; rw [one_div_pow]
  rw [h]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

private lemma tsum_inv_four_pow : ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ j = 4 / 3 := by
  have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ j) = fun j : ℕ => ((1 : ℝ) / 4) ^ j := by
    funext j; rw [one_div_pow]
  rw [h, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

private lemma tsum_inv_four_pow_succ : ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ (j + 1) = 1 / 3 := by
  have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) =
      fun j : ℕ => (1 / 4 : ℝ) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
    funext j; rw [pow_succ]; ring
  rw [h, tsum_mul_left, tsum_inv_four_pow]
  norm_num

private lemma tsum_inv_four_pow_shift (m : ℕ) :
    ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ (j + m) = (4 / 3 : ℝ) / (4 : ℝ) ^ m := by
  have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + m)) =
      fun j : ℕ => (1 / (4 : ℝ) ^ m) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
    funext j; rw [pow_add]; ring
  rw [h, tsum_mul_left, tsum_inv_four_pow]
  ring

private lemma fract_of_base4_bits (g : ℕ → ℕ) (hg : ∀ j, g j ≤ 1) (hg0 : g 0 = 1) :
    let ξ : ℝ := ∑' j : ℕ, (g j : ℝ) / (4 : ℝ) ^ (j + 1)
    1 / 4 ≤ ξ ∧ ξ ≤ 1 / 3 ∧
    ∀ k : ℕ, Int.fract ((4 : ℝ) ^ k * ξ) ≤ 1 / 3 := by
  intro ξ
  have hterm_nn : ∀ j : ℕ, 0 ≤ (g j : ℝ) / (4 : ℝ) ^ (j + 1) := fun j => by positivity
  have hterm_le : ∀ j : ℕ, (g j : ℝ) / (4 : ℝ) ^ (j + 1) ≤ (1 : ℝ) / (4 : ℝ) ^ (j + 1) := by
    intro j
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hg j
  have hdom_sum : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) := by
    have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) =
        fun j : ℕ => (1 / 4 : ℝ) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
      funext j; rw [pow_succ]; ring
    rw [h]; exact summable_inv_four_pow.mul_left _
  have hsum : Summable (fun j : ℕ => (g j : ℝ) / (4 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le hterm_nn hterm_le hdom_sum
  have hξ_ge : 1 / 4 ≤ ξ := by
    have h0 : (g 0 : ℝ) / (4 : ℝ) ^ (0 + 1) ≤ ξ :=
      hsum.le_tsum 0 (fun j _ => hterm_nn j)
    rw [hg0] at h0; norm_num at h0; exact h0
  have hξ_le : ξ ≤ 1 / 3 := by
    calc ξ ≤ ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ (j + 1) := hsum.tsum_le_tsum hterm_le hdom_sum
      _ = 1 / 3 := tsum_inv_four_pow_succ
  refine ⟨hξ_ge, hξ_le, fun k => ?_⟩
  have hsplit := hsum.sum_add_tsum_nat_add k
  have hmul_eq : (4 : ℝ) ^ k * ξ =
      ((∑ j ∈ Finset.range k, g j * 4 ^ (k - (j + 1)) : ℕ) : ℝ) +
      ∑' j : ℕ, (g (j + k) : ℝ) / (4 : ℝ) ^ (j + 1) := by
    show (4 : ℝ) ^ k * (∑' j : ℕ, (g j : ℝ) / (4 : ℝ) ^ (j + 1)) = _
    rw [← hsplit, mul_add]
    congr 1
    · rw [Finset.mul_sum, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      push_cast
      have hpow : (4 : ℝ) ^ k = (4 : ℝ) ^ (k - (j + 1)) * (4 : ℝ) ^ (j + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hj]
      rw [hpow]
      have hne : (4 : ℝ) ^ (j + 1) ≠ 0 := by positivity
      field_simp [hne]
    · rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      have hpow : (4 : ℝ) ^ (j + k + 1) = (4 : ℝ) ^ k * (4 : ℝ) ^ (j + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have hne : (4 : ℝ) ^ k ≠ 0 := by positivity
      field_simp [hne]
  set tail : ℝ := ∑' j : ℕ, (g (j + k) : ℝ) / (4 : ℝ) ^ (j + 1)
  have htail_sum : Summable (fun j : ℕ => (g (j + k) : ℝ) / (4 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hg (j + k)) (by positivity)) hdom_sum
  have htail_nn : 0 ≤ tail := tsum_nonneg (fun j => by positivity)
  have htail_le : tail ≤ 1 / 3 := by
    calc tail ≤ ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ (j + 1) :=
          htail_sum.tsum_le_tsum
            (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hg (j + k)) (by positivity))
            hdom_sum
      _ = 1 / 3 := tsum_inv_four_pow_succ
  rw [hmul_eq, add_comm]
  have hcast_int : ((∑ j ∈ Finset.range k, g j * 4 ^ (k - (j + 1)) : ℕ) : ℝ) =
      (((∑ j ∈ Finset.range k, g j * 4 ^ (k - (j + 1)) : ℕ) : ℤ) : ℝ) := by simp
  rw [hcast_int, Int.fract_add_intCast]
  rw [Int.fract_eq_self.mpr ⟨htail_nn, by linarith⟩]
  exact htail_le

private def bit4 (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | j + 1 => if f j then 1 else 0

/-- **Uncountable Cantor Family of Order-1 PPL 034 Solutions:**
The set of real numbers `r > 1` whose Beatty sequence `{⌊n r⌋₊ : n ≥ 1}` contains the
geometric progression `{4^k : k ∈ ℕ}` (and thus a strictly increasing order-1 homogeneous
linear recurrence `u (k + 1) = 4 * u k`) is **UNCOUNTABLE**. -/
theorem ppl034_uncountable_order1_solutions :
    ¬ Set.Countable {r : ℝ | 1 < r ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = 4 ^ k) ∧
      ∃ (u : ℕ → ℕ) (c : Fin 1 → ℤ),
        StrictMono u ∧
        (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
        (∀ k : ℕ, (u (k + 1) : ℤ) = ∑ j : Fin 1, c j * (u (k + j) : ℤ))} := by
  let ξ : (ℕ → Bool) → ℝ := fun f => ∑' j : ℕ, (bit4 f j : ℝ) / (4 : ℝ) ^ (j + 1)
  let R : (ℕ → Bool) → ℝ := fun f => 1 / (1 - ξ f)
  have hbit_le : ∀ f j, bit4 f j ≤ 1 := by
    intro f j; cases j with
    | zero => simp [bit4]
    | succ j => simp only [bit4]; split_ifs <;> omega
  have hξ_props : ∀ f, 1 / 4 ≤ ξ f ∧ ξ f ≤ 1 / 3 ∧ ∀ k, Int.fract ((4 : ℝ) ^ k * ξ f) ≤ 1 / 3 :=
    fun f => fract_of_base4_bits (bit4 f) (hbit_le f) rfl
  -- Prove `R` is injective by first-differing-digit argument
  have hR_inj : Function.Injective R := by
    intro f g hfg
    have hξ_eq : ξ f = ξ g := by
      have h1 : 1 - ξ f > 0 := by linarith [(hξ_props f).2.1]
      have h2 : 1 - ξ g > 0 := by linarith [(hξ_props g).2.1]
      have hinv : (1 - ξ f)⁻¹ = (1 - ξ g)⁻¹ := by simpa [R, one_div] using hfg
      have := inv_injective hinv
      linarith
    by_contra hne
    have hex_diff : ∃ j : ℕ, f j ≠ g j := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨j₀, hj₀_ne, hj₀_min⟩ : ∃ j₀ : ℕ, f j₀ ≠ g j₀ ∧ ∀ j < j₀, f j = g j := by
      classical
      exact ⟨Nat.find hex_diff, Nat.find_spec hex_diff, fun j hj => by
        by_contra h; exact Nat.find_min hex_diff hj h⟩
    have hdom : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) := by
      have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) =
          fun j : ℕ => (1 / 4 : ℝ) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
        funext j; rw [pow_succ]; ring
      rw [h]; exact summable_inv_four_pow.mul_left _
    have hsum_f : Summable (fun j : ℕ => (bit4 f j : ℝ) / (4 : ℝ) ^ (j + 1)) :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hbit_le f j) (by positivity)) hdom
    have hsum_g : Summable (fun j : ℕ => (bit4 g j : ℝ) / (4 : ℝ) ^ (j + 1)) :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hbit_le g j) (by positivity)) hdom
    have htail_sum_abs : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 3))) := by
      have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 3))) =
          fun j : ℕ => (1 / (4 : ℝ) ^ (j₀ + 3)) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
        funext j; rw [pow_add]; ring
      rw [h]; exact summable_inv_four_pow.mul_left _
    have htail_dom : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1)) := by
      have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1)) =
          fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 3)) := by
        funext j; congr 2
      rw [h]; exact htail_sum_abs
    have htail_f : Summable (fun j : ℕ => (bit4 f (j + (j₀ + 2)) : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1)) :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hbit_le f (j + (j₀ + 2))) (by positivity))
        htail_dom
    have htail_g : Summable (fun j : ℕ => (bit4 g (j + (j₀ + 2)) : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1)) :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hbit_le g (j + (j₀ + 2))) (by positivity))
        htail_dom
    have hdiff_eq : ξ f - ξ g =
        ((bit4 f (j₀ + 1) : ℝ) - (bit4 g (j₀ + 1) : ℝ)) / (4 : ℝ) ^ (j₀ + 2) +
        ∑' j : ℕ, ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
          (4 : ℝ) ^ (j + (j₀ + 2) + 1) := by
      have hsf := hsum_f.sum_add_tsum_nat_add (j₀ + 2)
      have hsg := hsum_g.sum_add_tsum_nat_add (j₀ + 2)
      have hprefix : ∑ j ∈ Finset.range (j₀ + 1), (bit4 f j : ℝ) / (4 : ℝ) ^ (j + 1) =
          ∑ j ∈ Finset.range (j₀ + 1), (bit4 g j : ℝ) / (4 : ℝ) ^ (j + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        cases j with
        | zero => rfl
        | succ m =>
          simp only [bit4, hj₀_min m (by omega)]
      have hsplit_f : ∑ j ∈ Finset.range (j₀ + 2), (bit4 f j : ℝ) / (4 : ℝ) ^ (j + 1) =
          (∑ j ∈ Finset.range (j₀ + 1), (bit4 f j : ℝ) / (4 : ℝ) ^ (j + 1)) +
            (bit4 f (j₀ + 1) : ℝ) / (4 : ℝ) ^ (j₀ + 2) := Finset.sum_range_succ _ _
      have hsplit_g : ∑ j ∈ Finset.range (j₀ + 2), (bit4 g j : ℝ) / (4 : ℝ) ^ (j + 1) =
          (∑ j ∈ Finset.range (j₀ + 1), (bit4 g j : ℝ) / (4 : ℝ) ^ (j + 1)) +
            (bit4 g (j₀ + 1) : ℝ) / (4 : ℝ) ^ (j₀ + 2) := Finset.sum_range_succ _ _
      have htsum_sub :
          (∑' j : ℕ, (bit4 f (j + (j₀ + 2)) : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1)) -
          (∑' j : ℕ, (bit4 g (j + (j₀ + 2)) : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1)) =
          ∑' j : ℕ, ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
            (4 : ℝ) ^ (j + (j₀ + 2) + 1) := by
        rw [← htail_f.tsum_sub htail_g]
        apply tsum_congr; intro j; ring
      show (∑' j : ℕ, (bit4 f j : ℝ) / (4 : ℝ) ^ (j + 1)) -
           (∑' j : ℕ, (bit4 g j : ℝ) / (4 : ℝ) ^ (j + 1)) = _
      rw [← hsf, ← hsg, hsplit_f, hsplit_g, hprefix]
      have hsub_div : (bit4 f (j₀ + 1) : ℝ) / (4 : ℝ) ^ (j₀ + 2) -
          (bit4 g (j₀ + 1) : ℝ) / (4 : ℝ) ^ (j₀ + 2) =
          ((bit4 f (j₀ + 1) : ℝ) - (bit4 g (j₀ + 1) : ℝ)) / (4 : ℝ) ^ (j₀ + 2) := by ring
      linarith [htsum_sub, hsub_div]
    -- Bound the tail `|tail| ≤ (1 / 3) / 4 ^ (j₀ + 2)`
    have htail_diff_sum : Summable (fun j : ℕ =>
        ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
          (4 : ℝ) ^ (j + (j₀ + 2) + 1)) := by
      have heq : (fun j : ℕ => ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
          (4 : ℝ) ^ (j + (j₀ + 2) + 1)) =
        fun j : ℕ => (bit4 f (j + (j₀ + 2)) : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1) -
          (bit4 g (j + (j₀ + 2)) : ℝ) / (4 : ℝ) ^ (j + (j₀ + 2) + 1) := by
        funext j; ring
      rw [heq]; exact htail_f.sub htail_g
    have htail_bound :
        |∑' j : ℕ, ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
          (4 : ℝ) ^ (j + (j₀ + 2) + 1)| ≤ (1 / 3 : ℝ) / (4 : ℝ) ^ (j₀ + 2) := by
      have hterm_abs : ∀ j : ℕ,
          |((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
            (4 : ℝ) ^ (j + (j₀ + 2) + 1)| ≤ (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 3)) := by
        intro j
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (4 : ℝ) ^ (j + (j₀ + 2) + 1))]
        have hbf : (bit4 f (j + (j₀ + 2)) : ℝ) ≤ 1 := by exact_mod_cast hbit_le f (j + (j₀ + 2))
        have hbg : (bit4 g (j + (j₀ + 2)) : ℝ) ≤ 1 := by exact_mod_cast hbit_le g (j + (j₀ + 2))
        have hbf0 : (0 : ℝ) ≤ (bit4 f (j + (j₀ + 2)) : ℝ) := by positivity
        have hbg0 : (0 : ℝ) ≤ (bit4 g (j + (j₀ + 2)) : ℝ) := by positivity
        have habs : |(bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)| ≤ 1 :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        have hidx : j + (j₀ + 2) + 1 = j + (j₀ + 3) := by omega
        rw [hidx]
        exact div_le_div_of_nonneg_right habs (by positivity)
      calc |∑' j : ℕ, ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
              (4 : ℝ) ^ (j + (j₀ + 2) + 1)|
          ≤ ∑' j : ℕ, |((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
              (4 : ℝ) ^ (j + (j₀ + 2) + 1)| := by
              simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail_diff_sum.norm
        _ ≤ ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ (j + (j₀ + 3)) :=
            (by simpa only [Real.norm_eq_abs] using htail_diff_sum.norm :
              Summable (fun j : ℕ => |((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
                (4 : ℝ) ^ (j + (j₀ + 2) + 1)|)).tsum_le_tsum hterm_abs htail_sum_abs
        _ = (4 / 3 : ℝ) / (4 : ℝ) ^ (j₀ + 3) := tsum_inv_four_pow_shift (j₀ + 3)
        _ = (1 / 3 : ℝ) / (4 : ℝ) ^ (j₀ + 2) := by rw [pow_succ]; ring
    have hlead : |((bit4 f (j₀ + 1) : ℝ) - (bit4 g (j₀ + 1) : ℝ)) / (4 : ℝ) ^ (j₀ + 2)| =
        1 / (4 : ℝ) ^ (j₀ + 2) := by
      simp only [bit4]
      cases hf0 : f j₀ <;> cases hg0 : g j₀
      · exact absurd (hf0.trans hg0.symm) hj₀_ne
      · simp [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (4 : ℝ) ^ (j₀ + 2))]
      · simp
      · exact absurd (hf0.trans hg0.symm) hj₀_ne
    have h0 : ξ f - ξ g = 0 := sub_eq_zero.mpr hξ_eq
    have hpos_pow : (0 : ℝ) < 1 / (4 : ℝ) ^ (j₀ + 2) := by positivity
    rw [h0] at hdiff_eq
    have hneg_eq : ((bit4 f (j₀ + 1) : ℝ) - (bit4 g (j₀ + 1) : ℝ)) / (4 : ℝ) ^ (j₀ + 2) =
        -(∑' j : ℕ, ((bit4 f (j + (j₀ + 2)) : ℝ) - (bit4 g (j + (j₀ + 2)) : ℝ)) /
          (4 : ℝ) ^ (j + (j₀ + 2) + 1)) := by linarith
    have habs_eq : 1 / (4 : ℝ) ^ (j₀ + 2) ≤ (1 / 3 : ℝ) / (4 : ℝ) ^ (j₀ + 2) := by
      rw [← hlead, hneg_eq, abs_neg]
      exact htail_bound
    have : (1 : ℝ) / (4 : ℝ) ^ (j₀ + 2) = 3 * ((1 / 3 : ℝ) / (4 : ℝ) ^ (j₀ + 2)) := by ring
    linarith
  -- Every `R f` belongs to the target set `S`
  have hR_mem : ∀ f : ℕ → Bool, R f ∈ {r : ℝ | 1 < r ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = 4 ^ k) ∧
      ∃ (u : ℕ → ℕ) (c : Fin 1 → ℤ),
        StrictMono u ∧
        (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
        (∀ k : ℕ, (u (k + 1) : ℤ) = ∑ j : Fin 1, c j * (u (k + j) : ℤ))} := by
    intro f
    obtain ⟨hξ_ge, hξ_le, hfr⟩ := hξ_props f
    have h1m_pos : 0 < 1 - ξ f := by linarith
    have h1m_lt1 : 1 - ξ f < 1 := by linarith
    have hR_gt1 : 1 < R f := by
      simp only [R]; exact (one_lt_div h1m_pos).mpr h1m_lt1
    have hinv_R : 1 / R f = 1 - ξ f := by
      simp only [R]; field_simp [h1m_pos.ne']
    have h4k : ∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * R f) = 4 ^ k := by
      rw [ppl034_geom_prog_iff_fract hR_gt1 (by omega : 2 ≤ 4)]
      intro k
      rw [hinv_R]
      have hsub : 1 - (1 - ξ f) = ξ f := by ring
      rw [hsub]
      calc Int.fract ((4 : ℝ) ^ k * ξ f) ≤ 1 / 3 := hfr k
        _ < 1 - ξ f := by linarith
    refine ⟨hR_gt1, h4k, fun k => 4 ^ k, fun _ => 4, ?_, h4k, ?_⟩
    · intro a b hab; exact Nat.pow_lt_pow_right (by omega) hab
    · intro k
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, add_zero]
      push_cast; rw [pow_succ]; ring
  -- Cantor diagonalization: `ℕ → Bool` is not countable
  intro hcount
  have hrange_count : (Set.range R).Countable := hcount.mono (by rintro _ ⟨f, rfl⟩; exact hR_mem f)
  have : Countable (Set.range R) := hrange_count.to_subtype
  have hcomp_inj : Function.Injective (fun f : ℕ → Bool => (⟨R f, ⟨f, rfl⟩⟩ : Set.range R)) := by
    intro f g h; exact hR_inj (congrArg Subtype.val h)
  have : Countable (ℕ → Bool) := Function.Injective.countable hcomp_inj
  rcases exists_surjective_nat (ℕ → Bool) with ⟨e, he⟩
  rcases he (fun n => !(e n n)) with ⟨m, hm⟩
  have hcontra := congrFun hm m
  cases hval : e m m <;> simp [hval] at hcontra

/-- **Explicit Transcendental Solution to PPL 034:**
There exists a TRANSCENDENTAL real number `r > 1` (`Transcendental ℚ r`, explicitly
`r = (1 - ∑_{n=0}^∞ 4^{-(n+1)!})^{-1}`) whose Beatty sequence `{⌊n r⌋₊ : n ≥ 1}` contains
the geometric progression `{4^k : k ∈ ℕ}` (order-1 homogeneous linear recurrence `u(k+1) = 4 u(k)`).
Proved via `Arith4Ext.LargeSieveDiophantine.transcendental_of_liouville_approx`. -/
theorem ppl034_exists_transcendental_order1_solution :
    ∃ r : ℝ, 1 < r ∧ Transcendental ℚ r ∧
      (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = 4 ^ k) ∧
      ∃ (u : ℕ → ℕ) (c : Fin 1 → ℤ),
        StrictMono u ∧
        (∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
        (∀ k : ℕ, (u (k + 1) : ℤ) = ∑ j : Fin 1, c j * (u (k + j) : ℤ)) := by
  classical
  -- Indicator bit sequence `g j = 1` iff `j + 1 = (n + 1)!` for some `n : ℕ`
  let g : ℕ → ℕ := fun j => if ∃ n : ℕ, (n + 1).factorial = j + 1 then 1 else 0
  have hg_le : ∀ j, g j ≤ 1 := fun j => by simp only [g]; split_ifs <;> omega
  have hg0 : g 0 = 1 := by
    simp only [g, zero_add]
    rw [if_pos ⟨0, rfl⟩]
  -- Define `ξ` directly as `∑' j, g j / 4 ^ (j + 1)` AND show it equals `∑' n, 1 / 4 ^ (n + 1)!`
  let ξ : ℝ := ∑' j : ℕ, (g j : ℝ) / (4 : ℝ) ^ (j + 1)
  obtain ⟨hξ_ge, hξ_le, hξ_fr⟩ := fract_of_base4_bits g hg_le hg0
  have hfac_strict : StrictMono (fun n : ℕ => (n + 1).factorial) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    rw [Nat.factorial_succ (n + 1)]
    have hpos : 0 < (n + 1).factorial := Nat.factorial_pos (n + 1)
    nlinarith
  have hfac_ge : ∀ n : ℕ, n + 1 ≤ (n + 1).factorial := fun n => Nat.self_le_factorial (n + 1)
  have hdom : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) := by
    have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + 1)) =
        fun j : ℕ => (1 / 4 : ℝ) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
      funext j; rw [pow_succ]; ring
    rw [h]; exact summable_inv_four_pow.mul_left _
  have hsum_g : Summable (fun j : ℕ => (g j : ℝ) / (4 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hg_le j) (by positivity)) hdom
  -- For any `N ≥ 1`, let `M = (N + 1)!`, `q = 4^M`, `p = ∑_{j < M} g j * 4^{M - (j + 1)}`:
  -- Then `0 < ξ - p / q ≤ (4/3) / 4^{(N + 2)!} = (4/3) / q^{N + 2}`!
  have happrox_N : ∀ N : ℕ, 1 ≤ N →
      ∃ (p : ℤ) (q : ℕ), 0 < q ∧ q = 4 ^ (N + 1).factorial ∧
        0 < ξ - (p : ℝ) / (q : ℝ) ∧
        ξ - (p : ℝ) / (q : ℝ) ≤ (4 / 3 : ℝ) / (q : ℝ) ^ (N + 2) := by
    intro N hN
    set M : ℕ := (N + 1).factorial
    set q : ℕ := 4 ^ M
    have hq_pos : 0 < q := by positivity
    have hq_R : (q : ℝ) = (4 : ℝ) ^ M := by simp [q]
    set p_nat : ℕ := ∑ j ∈ Finset.range M, g j * 4 ^ (M - (j + 1))
    have hsplit := hsum_g.sum_add_tsum_nat_add M
    have hpref_eq : ∑ j ∈ Finset.range M, (g j : ℝ) / (4 : ℝ) ^ (j + 1) = (p_nat : ℝ) / (q : ℝ) := by
      rw [hq_R, Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      push_cast
      have hpow : (4 : ℝ) ^ M = (4 : ℝ) ^ (M - (j + 1)) * (4 : ℝ) ^ (j + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hj]
      rw [hpow]
      have h1 : (4 : ℝ) ^ (M - (j + 1)) ≠ 0 := by positivity
      have h2 : (4 : ℝ) ^ (j + 1) ≠ 0 := by positivity
      field_simp [h1, h2]
    have htail_eq : ξ - (p_nat : ℝ) / (q : ℝ) =
        ∑' j : ℕ, (g (j + M) : ℝ) / (4 : ℝ) ^ (j + M + 1) := by
      rw [← hpref_eq]
      show (∑' j : ℕ, (g j : ℝ) / (4 : ℝ) ^ (j + 1)) - _ = _
      linarith [hsplit]
    have htail_sum : Summable (fun j : ℕ => (g (j + M) : ℝ) / (4 : ℝ) ^ (j + M + 1)) :=
      hsum_g.comp_injective (add_left_injective M)
    -- Next nonzero term is at index `M₂ - 1 = (N + 2)! - 1`
    set M₂ : ℕ := (N + 2).factorial
    have hM_lt_M2 : M < M₂ := hfac_strict (by omega)
    have hM2_eq : M₂ = (N + 2) * M := Nat.factorial_succ (N + 1)
    have htail_pos : 0 < ∑' j : ℕ, (g (j + M) : ℝ) / (4 : ℝ) ^ (j + M + 1) := by
      set j₁ : ℕ := M₂ - 1 - M
      have hj1_eq : j₁ + M + 1 = M₂ := by omega
      have hterm_pos : 0 < (g (j₁ + M) : ℝ) / (4 : ℝ) ^ (j₁ + M + 1) := by
        have hg1 : g (j₁ + M) = 1 := by
          simp only [g, hj1_eq]
          rw [if_pos ⟨N + 1, rfl⟩]
        rw [hg1]; positivity
      have hle := htail_sum.le_tsum j₁ (fun j _ => by positivity)
      linarith
    -- Every `j` with `j + M + 1 < M₂` has `g (j + M) = 0`
    have hzero_below : ∀ j : ℕ, j < M₂ - 1 - M → g (j + M) = 0 := by
      intro j hj
      simp only [g]
      rw [if_neg]
      rintro ⟨n, hn⟩
      rcases lt_or_ge n (N + 1) with hlt | hge
      · have hle : (n + 1).factorial ≤ M := hfac_strict.monotone (by omega)
        omega
      · have hge2 : M₂ ≤ (n + 1).factorial := hfac_strict.monotone hge
        omega
    -- Split off the leading zeros `j < M₂ - 1 - M`
    have htail_shift :
        ∑' j : ℕ, (g (j + M) : ℝ) / (4 : ℝ) ^ (j + M + 1) =
        ∑' j : ℕ, (g (j + (M₂ - 1)) : ℝ) / (4 : ℝ) ^ (j + M₂) := by
      have hsp := htail_sum.sum_add_tsum_nat_add (M₂ - 1 - M)
      have hpref0 : ∑ j ∈ Finset.range (M₂ - 1 - M), (g (j + M) : ℝ) / (4 : ℝ) ^ (j + M + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hzero_below j hj]; simp
      rw [hpref0, zero_add] at hsp
      rw [← hsp]
      apply tsum_congr
      intro j
      have h1 : j + (M₂ - 1 - M) + M = j + (M₂ - 1) := by omega
      have h2 : j + (M₂ - 1) + 1 = j + M₂ := by omega
      rw [h1, h2]
    have htail_le : ∑' j : ℕ, (g (j + (M₂ - 1)) : ℝ) / (4 : ℝ) ^ (j + M₂) ≤
        (4 / 3 : ℝ) / (q : ℝ) ^ (N + 2) := by
      have hdom2 : Summable (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + M₂)) := by
        have h : (fun j : ℕ => (1 : ℝ) / (4 : ℝ) ^ (j + M₂)) =
            fun j : ℕ => (1 / (4 : ℝ) ^ M₂) * ((1 : ℝ) / (4 : ℝ) ^ j) := by
          funext j; rw [pow_add]; ring
        rw [h]; exact summable_inv_four_pow.mul_left _
      have hsum2 : Summable (fun j : ℕ => (g (j + (M₂ - 1)) : ℝ) / (4 : ℝ) ^ (j + M₂)) :=
        Summable.of_nonneg_of_le (fun j => by positivity)
          (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hg_le _) (by positivity)) hdom2
      calc ∑' j : ℕ, (g (j + (M₂ - 1)) : ℝ) / (4 : ℝ) ^ (j + M₂)
          ≤ ∑' j : ℕ, (1 : ℝ) / (4 : ℝ) ^ (j + M₂) :=
            hsum2.tsum_le_tsum
              (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hg_le _) (by positivity)) hdom2
        _ = (4 / 3 : ℝ) / (4 : ℝ) ^ M₂ := tsum_inv_four_pow_shift M₂
        _ = (4 / 3 : ℝ) / (q : ℝ) ^ (N + 2) := by
            rw [hq_R, hM2_eq, mul_comm, pow_mul]
    refine ⟨(p_nat : ℤ), q, hq_pos, rfl, ?_, ?_⟩
    · simp only [Int.cast_natCast]; rw [htail_eq]; exact htail_pos
    · simp only [Int.cast_natCast]; rw [htail_eq, htail_shift]; exact htail_le
  -- Prove `Irrational ξ` from `happrox_N`
  have hξ_irr : Irrational ξ := by
    rintro ⟨a, ha⟩
    set b : ℕ := a.den
    have hb_pos : 0 < b := a.pos
    have hb_R : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    set N : ℕ := max 1 (2 * b)
    rcases happrox_N N (le_max_left 1 (2 * b)) with ⟨p, q, hq_pos, hq_eq, hpos, hle⟩
    have hq_R_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have ha_eq : ξ = (a.num : ℝ) / (b : ℝ) := by rw [← ha, Rat.cast_def]
    have hdiff_eq : (b : ℝ) * (q : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) =
        ((a.num * (q : ℤ) - (b : ℤ) * p : ℤ) : ℝ) := by
      rw [ha_eq]; push_cast; field_simp [hb_R.ne', hq_R_pos.ne']
    have hint_pos : (0 : ℤ) < a.num * (q : ℤ) - (b : ℤ) * p := by
      have : (0 : ℝ) < ((a.num * (q : ℤ) - (b : ℤ) * p : ℤ) : ℝ) := by
        rw [← hdiff_eq]; exact mul_pos (mul_pos hb_R hq_R_pos) hpos
      exact_mod_cast this
    have hint_ge1 : (1 : ℝ) ≤ ((a.num * (q : ℤ) - (b : ℤ) * p : ℤ) : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ a.num * (q : ℤ) - (b : ℤ) * p by omega)
    have hq_ge : (2 * b + 1 : ℝ) ≤ (q : ℝ) := by
      have hN_le_fac : N + 1 ≤ (N + 1).factorial := hfac_ge N
      have h4_ge : (N + 1 : ℕ) ≤ 4 ^ (N + 1).factorial := by
        calc N + 1 ≤ (N + 1).factorial := hN_le_fac
          _ ≤ 2 ^ (N + 1).factorial := Nat.le_of_lt (Nat.lt_two_pow_self)
          _ ≤ 4 ^ (N + 1).factorial := Nat.pow_le_pow_left (by omega) _
      have hq_nat : 2 * b + 1 ≤ q := by
        rw [hq_eq]
        have : 2 * b + 1 ≤ N + 1 := by have := le_max_right 1 (2 * b); omega
        exact le_trans this h4_ge
      exact_mod_cast hq_nat
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb_pos
    have hq_ge2 : (2 : ℝ) ≤ (q : ℝ) := by linarith
    have hq_pow_ge : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ (N + 1) :=
      pow_le_pow_right₀ (by linarith) (by have := le_max_left 1 (2 * b); omega)
    have hupper : (b : ℝ) * (q : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) < 1 := by
      calc (b : ℝ) * (q : ℝ) * (ξ - (p : ℝ) / (q : ℝ))
          ≤ (b : ℝ) * (q : ℝ) * ((4 / 3 : ℝ) / (q : ℝ) ^ (N + 2)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (4 / 3 : ℝ) * (b : ℝ) / (q : ℝ) ^ (N + 1) := by
            rw [pow_succ]; field_simp [hq_R_pos.ne']
        _ ≤ (4 / 3 : ℝ) * (b : ℝ) / (q : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hq_pow_ge
        _ < 1 := by
            rw [div_lt_one (by positivity)]
            nlinarith
    linarith
  -- Prove `Transcendental ℚ ξ` via `Arith4Ext.LargeSieveDiophantine.transcendental_of_liouville_approx`
  have hξ_trans : Transcendental ℚ ξ := by
    apply Arith4Ext.LargeSieveDiophantine.transcendental_of_liouville_approx hξ_irr
    intro d hd c hc
    set K : ℕ := Nat.ceil (2 / c) + 1
    set N : ℕ := max d K
    have hN1 : 1 ≤ N := le_trans hd (le_max_left d K)
    rcases happrox_N N hN1 with ⟨p, q, hq_pos, hq_eq, hpos, hle⟩
    have hq_R_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have hq_ge_K : (K : ℝ) ≤ (q : ℝ) := by
      have h1 : K ≤ N := le_max_right d K
      have h2 : N + 1 ≤ (N + 1).factorial := hfac_ge N
      have h3 : (N + 1).factorial ≤ 4 ^ (N + 1).factorial :=
        le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega) _)
      exact_mod_cast (show K ≤ q by rw [hq_eq]; omega)
    have h2c_lt_q : 2 / c < (q : ℝ) := by
      have h1 : 2 / c ≤ (Nat.ceil (2 / c) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (2 / c) : ℝ) + 1 = (K : ℝ) := by simp [K]
      linarith
    have h43_lt : (4 / 3 : ℝ) / (q : ℝ) < c := by
      rw [div_lt_iff₀ hq_R_pos]
      have hmul : 2 < c * (q : ℝ) := by
        have := (div_lt_iff₀ hc).mp h2c_lt_q; linarith
      linarith
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pos
    have hpow_ge : (q : ℝ) ^ (d + 1) ≤ (q : ℝ) ^ (N + 2) :=
      pow_le_pow_right₀ hq_ge1 (by have := le_max_left d K; omega)
    refine ⟨p, q, hq_pos, ?_⟩
    rw [abs_of_pos hpos]
    calc ξ - (p : ℝ) / (q : ℝ)
        ≤ (4 / 3 : ℝ) / (q : ℝ) ^ (N + 2) := hle
      _ ≤ (4 / 3 : ℝ) / (q : ℝ) ^ (d + 1) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow_ge
      _ = ((4 / 3 : ℝ) / (q : ℝ)) / (q : ℝ) ^ d := by rw [pow_succ]; ring
      _ < c / (q : ℝ) ^ d := div_lt_div_of_pos_right h43_lt (by positivity)
  -- Set `r = 1 / (1 - ξ)` and transfer transcendence via explicit polynomial transformation
  set r : ℝ := 1 / (1 - ξ)
  have h1m_pos : 0 < 1 - ξ := by linarith
  have h1m_lt1 : 1 - ξ < 1 := by linarith
  have hr_gt1 : 1 < r := (one_lt_div h1m_pos).mpr h1m_lt1
  have hr_trans : Transcendental ℚ r := by
    rintro ⟨P, hP_ne, hP_root⟩
    set d : ℕ := P.natDegree
    let Q : Polynomial ℚ :=
      ∑ k ∈ Finset.range (d + 1), Polynomial.C (P.coeff k) * (1 - Polynomial.X) ^ (d - k)
    have hQ_eval1 : Q.eval 1 = P.coeff d := by
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, sub_self]
      rw [Finset.sum_eq_single d]
      · simp
      · intro k hk hkd
        rw [Finset.mem_range] at hk
        have hpos : d - k ≠ 0 := by omega
        simp [zero_pow hpos]
      · intro hd_not
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) hd_not
    have hQ_ne : Q ≠ 0 := by
      intro h0
      have hld : P.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
      rw [← hQ_eval1, h0, Polynomial.eval_zero] at hld
      exact hld rfl
    have hQ_root : Polynomial.aeval ξ Q = 0 := by
      have hP_sum : Polynomial.aeval r P =
          ∑ k ∈ Finset.range (d + 1), algebraMap ℚ ℝ (P.coeff k) * r ^ k := by
        conv_lhs => rw [Polynomial.as_sum_range' P (d + 1) (Nat.lt_succ_self d)]
        simp only [map_sum, Polynomial.aeval_monomial]
      have hQ_sum : Polynomial.aeval ξ Q =
          ∑ k ∈ Finset.range (d + 1), algebraMap ℚ ℝ (P.coeff k) * (1 - ξ) ^ (d - k) := by
        simp only [Q, map_sum, map_mul, map_pow, map_sub, map_one, Polynomial.aeval_C,
          Polynomial.aeval_X]
      rw [hQ_sum]
      have hterm : ∀ k ∈ Finset.range (d + 1),
          algebraMap ℚ ℝ (P.coeff k) * (1 - ξ) ^ (d - k) =
            (1 - ξ) ^ d * (algebraMap ℚ ℝ (P.coeff k) * r ^ k) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hprod1 : (1 - ξ) * r = 1 := by simp only [r]; field_simp [h1m_pos.ne']
        have hsplit : (1 - ξ) ^ d = (1 - ξ) ^ (d - k) * (1 - ξ) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp hk)]
        calc algebraMap ℚ ℝ (P.coeff k) * (1 - ξ) ^ (d - k)
            = algebraMap ℚ ℝ (P.coeff k) * (1 - ξ) ^ (d - k) * ((1 - ξ) * r) ^ k := by
                rw [hprod1, one_pow, mul_one]
          _ = (1 - ξ) ^ (d - k) * (1 - ξ) ^ k * (algebraMap ℚ ℝ (P.coeff k) * r ^ k) := by
                rw [mul_pow]; ring
          _ = (1 - ξ) ^ d * (algebraMap ℚ ℝ (P.coeff k) * r ^ k) := by rw [← hsplit]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hP_sum, hP_root, mul_zero]
    exact hξ_trans ⟨Q, hQ_ne, hQ_root⟩
  have hinv_r : 1 / r = 1 - ξ := by simp only [r]; field_simp [h1m_pos.ne']
  have h4k : ∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = 4 ^ k := by
    rw [ppl034_geom_prog_iff_fract hr_gt1 (by omega : 2 ≤ 4)]
    intro k
    rw [hinv_r, show 1 - (1 - ξ) = ξ by ring]
    calc Int.fract ((4 : ℝ) ^ k * ξ) ≤ 1 / 3 := hξ_fr k
      _ < 1 - ξ := by linarith
  refine ⟨r, hr_gt1, hr_trans, h4k, fun k => 4 ^ k, fun _ => 4, ?_, h4k, ?_⟩
  · intro a b hab; exact Nat.pow_lt_pow_right (by omega) hab
  · intro k
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, add_zero]
    push_cast; rw [pow_succ]; ring

/-! ## Section 5: General Arbitrary-Order Structural Criteria -/

/-- **Exact Fractional-Part Reformulation of PPL 034 for Arbitrary Order `d`:**
For any `r > 1`, `d : ℕ`, `c : Fin d → ℤ`, and `u : ℕ → ℕ` with `∀ k, 1 ≤ u k`,
`u` lies in `{⌊n r⌋₊ : n ≥ 1}` and satisfies the order-`d` homogeneous linear recurrence `c`
if and only if `Int.fract (-(u k / r)) < 1 / r` for all `k` and `u` satisfies `c`. -/
theorem ppl034_recurrence_iff_fract {r : ℝ} (hr : 1 < r) {d : ℕ} (c : Fin d → ℤ)
    (u : ℕ → ℕ) (hu : ∀ k : ℕ, 1 ≤ u k) :
    ((∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Nat.floor ((n : ℝ) * r) = u k) ∧
      (∀ k : ℕ, (u (k + d) : ℤ) = ∑ j : Fin d, c j * (u (k + j) : ℤ))) ↔
    ((∀ k : ℕ, Int.fract (-((u k : ℝ) / r)) < 1 / r) ∧
      (∀ k : ℕ, (u (k + d) : ℤ) = ∑ j : Fin d, c j * (u (k + j) : ℤ))) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun k => ?_, h2⟩
  · exact (ppl034_beatty_mem_iff_neg_fract hr (hu k)).mp (h1 k)
  · exact (ppl034_beatty_mem_iff_neg_fract hr (hu k)).mpr (h1 k)

/-- **Error-Recurrence Criterion for Coupled Index-Value Recurrences:**
If both index sequence `n : ℕ → ℕ` and value sequence `u : ℕ → ℕ` satisfy the same order-`d`
homogeneous linear recurrence `c : Fin d → ℤ`, then the approximation error
`e k = (n k : ℝ) * r - (u k : ℝ)` satisfies the exact same recurrence over `ℝ`, and
`∀ k, ⌊(n k) * r⌋₊ = u k` holds iff `0 ≤ e k < 1` for all `k`. -/
theorem ppl034_error_recurrence_criterion {r : ℝ} (hr : 0 ≤ r) {d : ℕ} (c : Fin d → ℤ)
    (n u : ℕ → ℕ)
    (hn_rec : ∀ k : ℕ, (n (k + d) : ℤ) = ∑ j : Fin d, c j * (n (k + j) : ℤ))
    (hu_rec : ∀ k : ℕ, (u (k + d) : ℤ) = ∑ j : Fin d, c j * (u (k + j) : ℤ)) :
    (∀ k : ℕ,
      ((n (k + d) : ℝ) * r - (u (k + d) : ℝ)) =
        ∑ j : Fin d, (c j : ℝ) * ((n (k + j) : ℝ) * r - (u (k + j) : ℝ))) ∧
    ((∀ k : ℕ, Nat.floor ((n k : ℝ) * r) = u k) ↔
      ∀ k : ℕ, 0 ≤ (n k : ℝ) * r - (u k : ℝ) ∧ (n k : ℝ) * r - (u k : ℝ) < 1) := by
  constructor
  · intro k
    have hnR : (n (k + d) : ℝ) = ∑ j : Fin d, (c j : ℝ) * (n (k + j) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (hn_rec k)
      simpa [Int.cast_sum, Int.cast_mul] using this
    have huR : (u (k + d) : ℝ) = ∑ j : Fin d, (c j : ℝ) * (u (k + j) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (hu_rec k)
      simpa [Int.cast_sum, Int.cast_mul] using this
    rw [hnR, huR, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · constructor
    · intro h k
      have hb := (Nat.floor_eq_iff (by positivity : 0 ≤ (n k : ℝ) * r)).mp (h k)
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    · intro h k
      rw [Nat.floor_eq_iff (by positivity : 0 ≤ (n k : ℝ) * r)]
      exact ⟨by linarith [(h k).1], by linarith [(h k).2]⟩

/-- **General Pisot-Type Sufficient Tail Criterion:**
For any `r ≥ 0`, `d : ℕ`, `c : Fin d → ℤ`, and sequences `n, u : ℕ → ℕ` such that `u` is
strictly increasing, `n k ≥ 1`, `u` satisfies the order-`d` recurrence `c`, the error
`e k = (n k : ℝ) * r - (u k : ℝ)` is nonnegative and tends to `0`, there exists a tail shift
`k₀ : ℕ` such that `u' k = u (k + k₀)` is a strictly increasing order-`d` homogeneous linear
recurrence contained in `{⌊m r⌋₊ : m ≥ 1}`. -/
theorem ppl034_recurrence_of_error_tendsto_zero {r : ℝ} (hr : 0 ≤ r) {d : ℕ} (c : Fin d → ℤ)
    (n u : ℕ → ℕ) (hmono : StrictMono u) (hn_pos : ∀ k : ℕ, 1 ≤ n k)
    (hu_rec : ∀ k : ℕ, (u (k + d) : ℤ) = ∑ j : Fin d, c j * (u (k + j) : ℤ))
    (herr_nn : ∀ k : ℕ, 0 ≤ (n k : ℝ) * r - (u k : ℝ))
    (herr_zero : Tendsto (fun k : ℕ => (n k : ℝ) * r - (u k : ℝ)) atTop (nhds 0)) :
    ∃ k₀ : ℕ,
      StrictMono (fun k : ℕ => u (k + k₀)) ∧
      (∀ k : ℕ, ∃ m : ℕ, 1 ≤ m ∧ Nat.floor ((m : ℝ) * r) = u (k + k₀)) ∧
      (∀ k : ℕ, (u (k + d + k₀) : ℤ) = ∑ j : Fin d, c j * (u (k + j + k₀) : ℤ)) := by
  rcases (Metric.tendsto_atTop.mp herr_zero) 1 one_pos with ⟨k₀, hk₀⟩
  refine ⟨k₀, fun a b hab => hmono (by omega), fun k => ?_, fun k => ?_⟩
  · refine ⟨n (k + k₀), hn_pos (k + k₀), ?_⟩
    have hdist := hk₀ (k + k₀) (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (herr_nn (k + k₀))] at hdist
    rw [Nat.floor_eq_iff (by positivity)]
    exact ⟨by linarith [herr_nn (k + k₀)], by linarith⟩
  · have h1 : k + d + k₀ = (k + k₀) + d := by omega
    rw [h1, hu_rec (k + k₀)]
    apply Finset.sum_congr rfl
    intro j _
    rw [show k + (j : ℕ) + k₀ = k + k₀ + (j : ℕ) by omega]

end
end PPL034
