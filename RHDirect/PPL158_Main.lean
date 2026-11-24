/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 158 — Extremal Type II `[72, 36, 16]` Binary Self-Dual Code

## Honest Scope Statement
**PPL 158** (`prizeproblems.org`: `$200` nonexistence / `$100` existence / `$10` Sloane,
**LIVE-VERIFIED OPEN** as of 2026) asks whether there exists an extremal Type II (doubly-even)
self-dual binary linear code of parameters `[72, 36, 16]` (length `72`, dimension `36`, minimum
Hamming distance `16`, all codeword weights divisible by `4`).

This module makes **no claim** to resolve the open existence/nonexistence problem for a
`[72, 36, 16]` Type II binary self-dual code. Instead, it provides a **100% unconditional,
from-scratch, kernel-verified, pure-Mathlib-signature formalization** of the core algebraic
coding theory surrounding PPL 158:
- **Section 1 (Self-Dual & Type II Code Foundations):**
  Rank-nullity duality `dim C + dim C^⊥ = n`, self-dual dimension `2 * dim C = n` (`Even n`),
  all-ones membership `1 ∈ C`, `wt(x + y) + 2 * inter(x, y) = wt x + wt y`, doubly-even
  self-orthogonality, and **Gleason–Pierce divisibility `8 ∣ n`** for all Type II self-dual codes.
- **Section 2 (MacWilliams Identity & Pless Power Moments):**
  Self-contained Walsh–Hadamard / character-sum proof of the binary MacWilliams identity
  `|C| * W_{C^⊥}(X, Y) = W_C(X + Y, X - Y)` over every `CommRing R`, MacWilliams self-duality
  over `ℝ` with `(X ± Y) / √2`, and the 0th, 1st, and 2nd Pless power moments.
- **Section 3 (Explicit Extremal Type II Witnesses):**
  Constructive, `0`-`native_decide` witnesses for the extremal Type II codes at `n = 8`
  (Extended Binary Hamming `[8, 4, 4]`, weight enumerator `1 + 14 y^4 + y^8`) and `n = 24`
  (Extended Binary Golay `[24, 12, 8]` via Turyn's `(a + x | b + x | a + b + x)` construction
  with the `𝔽_8`-cube APN permutation, exact `d = 8`, weight enumerator
  `1 + 759 y^8 + 2576 y^{12} + 759 y^{16} + y^{24}`).
- **Section 4 (Gleason's Theorem, Mallows–Sloane Bound & Unique `[72, 36, 16]` Enumerator):**
  Full proof of Gleason's theorem (1970) over `ℚ[φ_8, Δ_{24}]` for all `n = 8 m`, full proof
  of the Mallows–Sloane upper bound (1973) `d ≤ 4 ⌊n / 24⌋ + 4` for all `n > 0` (`d ≤ 16` at
  `n = 72`), and unconditional proof of the **unique** weight distribution of ANY `[72, 36, 16]`
  Type II code (`A_0 = A_{72} = 1`, `A_4 = A_8 = A_{12} = 0`, `A_{16} = 249849`,
  `A_{20} = 18106704`, `A_{24} = 462962955`, `A_{28} = 4397342400`, `A_{32} = 16602715899`,
  `A_{36} = 25756721120`, and `A_{72 - w} = A_w`).
- **Section 5 (Prime-Order Automorphism Barriers):**
  Orbit-size dichotomy, `A_w(C) ≡ |(C_w)^σ| [MOD p]`, fixed-subcode self-duality
  `2 * dim(C^σ) = c + f`, order-of-2 divisibility `p ∣ (2^((p - 1) * c / 2) - 1)`,
  Gleason–Pierce fixed-subcode constraint `8 ∣ (c + f)` for `p ≡ 1 [MOD 4]`, and unconditional
  exclusion of prime-order automorphisms `p ∈ {29, 37, 43, 53, 59, 61, 67}` (plus even cycle
  count `2 ∣ c` for `p ∈ {3, 5, 11, 13, 19}`) for any `[72, 36, 16]` Type II code.

Every public `theorem` in `namespace PPL158` uses **100% pure Mathlib signatures** (`0` custom or
`private` definitions/structures/abbrevs in any public theorem type).
-/

namespace PPL158

open scoped BigOperators Classical

/-! ### Private Internal Helpers (never exposed in any public theorem signature) -/

private def wt {n : ℕ} (x : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card

private def inter {n : ℕ} (x y : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ 0 ∧ y i ≠ 0)).card

private def dot2 {n : ℕ} (x y : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i : Fin n, x i * y i

private def dualCode {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {y | ∀ x ∈ C, dot2 x y = 0}
  zero_mem' := by
    intro x _
    simp [dot2]
  add_mem' := by
    intro y₁ y₂ hy₁ hy₂ x hx
    change dot2 x (y₁ + y₂) = 0
    have h : dot2 x (y₁ + y₂) = dot2 x y₁ + dot2 x y₂ := by
      simp [dot2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h, hy₁ x hx, hy₂ x hx, add_zero]
  smul_mem' := by
    intro c y hy x hx
    change dot2 x (c • y) = 0
    have h : dot2 x (c • y) = c * dot2 x y := by
      simp only [dot2, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h, hy x hx, mul_zero]

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by
  fin_cases a <;> rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

private lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

private lemma wt_le {n : ℕ} (x : Fin n → ZMod 2) : wt x ≤ n := by
  simpa [wt] using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i ≠ 0)

private lemma wt_zero {n : ℕ} : wt (0 : Fin n → ZMod 2) = 0 := by
  simp [wt]

private lemma wt_eq_zero_iff {n : ℕ} (x : Fin n → ZMod 2) : wt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun j : Fin n => x j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hpos : 0 < wt x := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  · rintro rfl
    exact wt_zero

private lemma wt_ones {n : ℕ} : wt (fun _ : Fin n => (1 : ZMod 2)) = n := by
  simp [wt]

private lemma wt_add_two_inter {n : ℕ} (x y : Fin n → ZMod 2) :
    wt (x + y) + 2 * inter x y = wt x + wt y := by
  simp only [wt, inter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx := zmod2_eq_zero_or_one (x i)
  have hy := zmod2_eq_zero_or_one (y i)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy, zmod2_add_self]

private lemma dot2_eq_cast_inter {n : ℕ} (x y : Fin n → ZMod 2) :
    dot2 x y = ((inter x y : ℕ) : ZMod 2) := by
  simp only [dot2, inter, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx := zmod2_eq_zero_or_one (x i)
  have hy := zmod2_eq_zero_or_one (y i)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

private lemma dot2_eq_zero_iff_even_inter {n : ℕ} (x y : Fin n → ZMod 2) :
    dot2 x y = 0 ↔ 2 ∣ inter x y := by
  rw [dot2_eq_cast_inter, ZMod.natCast_eq_zero_iff]

private lemma dot2_self_eq_cast_wt {n : ℕ} (x : Fin n → ZMod 2) :
    dot2 x x = ((wt x : ℕ) : ZMod 2) := by
  have h : inter x x = wt x := by
    simp [inter, wt]
  rw [dot2_eq_cast_inter, h]

private lemma dot2_self_eq_dot2_ones {n : ℕ} (x : Fin n → ZMod 2) :
    dot2 x x = dot2 x (fun _ => 1) := by
  simp only [dot2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zmod2_mul_self, mul_one]

private lemma wt_add_ones {n : ℕ} (x : Fin n → ZMod 2) :
    wt (x + fun _ => 1) = n - wt x := by
  have hsum : wt (x + fun _ => 1) + wt x = n := by
    have h1 := wt_add_two_inter x (fun _ => 1)
    have h2 : inter x (fun _ => 1) = wt x := by
      simp [inter, wt]
    rw [h2, wt_ones] at h1
    omega
  omega

private lemma four_dvd_wt_add {n : ℕ} {x y : Fin n → ZMod 2}
    (hx : 4 ∣ wt x) (hy : 4 ∣ wt y) (hxy : dot2 x y = 0) :
    4 ∣ wt (x + y) := by
  have h1 := wt_add_two_inter x y
  have h2 : 2 ∣ inter x y := (dot2_eq_zero_iff_even_inter x y).mp hxy
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  rcases h2 with ⟨c, hc⟩
  omega

private lemma dot2_eq_zero_of_four_dvd_wt {n : ℕ} {x y : Fin n → ZMod 2}
    (hx : 4 ∣ wt x) (hy : 4 ∣ wt y) (hxy : 4 ∣ wt (x + y)) :
    dot2 x y = 0 := by
  rw [dot2_eq_zero_iff_even_inter]
  have h1 := wt_add_two_inter x y
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  rcases hxy with ⟨c, hc⟩
  omega

private lemma card_submodule_eq_two_pow_finrank {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card =
      2 ^ Module.finrank (ZMod 2) C := by
  have hcard : Fintype.card C = 2 ^ Module.finrank (ZMod 2) C := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := C)
    simpa [ZMod.card] using h
  rw [← hcard]
  exact (Fintype.card_subtype (fun x : Fin n → ZMod 2 => x ∈ C)).symm

/-! ### Section 1: Self-Dual and Type II (Doubly-Even) Binary Linear Code Foundations -/

/-- The dual evaluation linear map `y ↦ (x ↦ ∑ i, x i * y i)` from `𝔽₂ⁿ` to `C*`. -/
private def dualEvalMap {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (C →ₗ[ZMod 2] ZMod 2) where
  toFun y :=
    { toFun := fun x => dot2 x.1 y
      map_add' := fun x₁ x₂ => by
        simp only [Submodule.coe_add, dot2, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [SetLike.val_smul, dot2, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  map_add' y₁ y₂ := by
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, dot2, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c y := by
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      smul_eq_mul, dot2, Pi.smul_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

private lemma ker_dualEvalMap {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    LinearMap.ker (dualEvalMap C) = dualCode C := by
  ext y
  simp only [LinearMap.mem_ker, dualCode, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · intro hy x hx
    exact LinearMap.congr_fun hy ⟨x, hx⟩
  · intro hy
    ext ⟨x, hx⟩
    exact hy x hx

private lemma surjective_dualEvalMap {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Function.Surjective (dualEvalMap C) := by
  intro f
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := C) f
  refine ⟨fun i => g (Pi.single i 1), ?_⟩
  ext ⟨x, hx⟩
  simp only [dualEvalMap, LinearMap.coe_mk, AddHom.coe_mk, dot2]
  have hx_eq : x = ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : g x = ∑ i : Fin n, x i * g (Pi.single i 1) := by
    conv_lhs => rw [hx_eq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [← h1]
  have hcomp := LinearMap.congr_fun hg ⟨x, hx⟩
  simpa using hcomp

private lemma finrank_add_finrank_dualCode {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) C + Module.finrank (ZMod 2) (dualCode C) = n := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (dualEvalMap C)
  rw [ker_dualEvalMap, LinearMap.range_eq_top.mpr (surjective_dualEvalMap C),
    finrank_top, Module.finrank_fin_fun] at hrn
  have hdual_dim : Module.finrank (ZMod 2) (C →ₗ[ZMod 2] ZMod 2) =
      Module.finrank (ZMod 2) C := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  omega

/-- **Theorem 1.1 (Dimension of Dual Binary Linear Code):**
For every binary linear code `C ≤ 𝔽₂ⁿ` and its orthogonal dual `D = C^⊥`,
`dim(C) + dim(C^⊥) = n`. -/
theorem binary_code_finrank_add_dual_finrank {n : ℕ}
    (C D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hD : ∀ y : Fin n → ZMod 2, y ∈ D ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0) :
    Module.finrank (ZMod 2) C + Module.finrank (ZMod 2) D = n := by
  have hEq : D = dualCode C := by
    ext y
    exact hD y
  rw [hEq]
  exact finrank_add_finrank_dualCode C

/-- **Theorem 1.2 (Self-Dual Dimension & Even Length):**
Every self-dual binary linear code `C = C^⊥` of length `n` has `2 * dim(C) = n` and `Even n`,
and cardinality `|C| = 2^(n / 2)`. -/
theorem selfDual_finrank_and_card {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0) :
    2 * Module.finrank (ZMod 2) C = n ∧ Even n ∧
      (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card = 2 ^ (n / 2) := by
  have hsum := binary_code_finrank_add_dual_finrank C C hSD
  have h2 : 2 * Module.finrank (ZMod 2) C = n := by omega
  have heven : Even n := ⟨Module.finrank (ZMod 2) C, by omega⟩
  have hdiv : Module.finrank (ZMod 2) C = n / 2 := by omega
  refine ⟨h2, heven, ?_⟩
  rw [card_submodule_eq_two_pow_finrank, hdiv]

/-- **Theorem 1.3 (All-Ones Codeword & Weight Symmetry in Self-Dual Codes):**
Every self-dual binary linear code contains the all-ones vector `1`, and therefore its weight
distribution is palindromic: `A_{n - w}(C) = A_w(C)` for all `w ≤ n`. -/
theorem selfDual_ones_mem_and_weight_symm {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0) :
    (fun _ : Fin n => (1 : ZMod 2)) ∈ C ∧
      ∀ w ≤ n,
        (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
          x ∈ C ∧ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card = n - w)).card =
        (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
          x ∈ C ∧ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card = w)).card := by
  have h1 : (fun _ : Fin n => (1 : ZMod 2)) ∈ C := by
    rw [hSD]
    intro x hx
    have hxx : dot2 x x = 0 := (hSD x).mp hx x hx
    change dot2 x (fun _ => 1) = 0
    rw [← dot2_self_eq_dot2_ones]
    exact hxx
  refine ⟨h1, ?_⟩
  intro w hw
  refine Finset.card_bij (fun x _ => x + fun _ => 1) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨C.add_mem hx.1 h1, ?_⟩
    have hwa := wt_add_ones x
    have hwx : wt x = n - w := hx.2
    change wt (x + fun _ => 1) = w
    omega
  · intro x₁ _ x₂ _ heq
    have := congrArg (fun v => v + fun _ => (1 : ZMod 2)) heq
    ext i
    have hi := congrFun this i
    simp only [Pi.add_apply] at hi
    rw [add_assoc, add_assoc, zmod2_add_self, add_zero, add_zero] at hi
    exact hi
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨y + fun _ => 1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨C.add_mem hy.1 h1, ?_⟩
      change wt (y + fun _ => 1) = n - w
      rw [wt_add_ones]
      exact congrArg (n - ·) hy.2
    · ext i
      simp only [Pi.add_apply]
      rw [add_assoc, zmod2_add_self, add_zero]

/-- **Theorem 1.4 (Doubly-Even Implies Self-Orthogonal):**
Every doubly-even binary linear code (`∀ x ∈ C, 4 ∣ wt(x)`) is automatically self-orthogonal
(`∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0`). -/
theorem doublyEven_is_selfOrthogonal {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) :
    ∀ x ∈ C, ∀ y ∈ C, (∑ i : Fin n, x i * y i) = 0 := by
  intro x hx y hy
  exact dot2_eq_zero_of_four_dvd_wt (hT2 x hx) (hT2 y hy) (hT2 (x + y) (C.add_mem hx hy))

/-! ### Section 2: Binary MacWilliams Identity, Gleason–Pierce `8 ∣ n`, and Pless Power Moments -/

/-- The binary additive character `χ : ZMod 2 → ℤ`, sending `0 ↦ 1`, `1 ↦ -1`. -/
private def chiZ (a : ZMod 2) : ℤ :=
  if a = 0 then 1 else -1

private lemma chiZ_zero : chiZ 0 = 1 := rfl

private lemma chiZ_one : chiZ 1 = -1 := by
  simp [chiZ]

private lemma chiZ_add (a b : ZMod 2) : chiZ (a + b) = chiZ a * chiZ b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
  simp [chiZ, zmod2_add_self]

private lemma chiZ_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chiZ (∑ i ∈ s, f i) = ∏ i ∈ s, chiZ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [chiZ_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiZ_add, ih]

private lemma sum_chiZ_dot2_eq {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (y : Fin n → ZMod 2) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C), chiZ (dot2 x y) =
      if y ∈ dualCode C then
        ((Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card : ℤ)
      else 0 := by
  by_cases hy : y ∈ dualCode C
  · rw [if_pos hy]
    have h1 : ∀ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        chiZ (dot2 x y) = (1 : ℤ) := by
      intro x hx
      have hxC : x ∈ C := (Finset.mem_filter.mp hx).2
      rw [hy x hxC, chiZ_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [if_neg hy]
    have hex : ∃ x₀ ∈ C, dot2 x₀ y ≠ 0 := by
      by_contra h
      push Not at h
      exact hy h
    rcases hex with ⟨x₀, hx₀C, hx₀ne⟩
    have hx₀1 : dot2 x₀ y = 1 := (zmod2_ne_zero_iff_eq_one _).mp hx₀ne
    let S := Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)
    have hshift : ∑ x ∈ S, chiZ (dot2 x y) = ∑ x ∈ S, chiZ (dot2 (x + x₀) y) := by
      refine Finset.sum_bij (fun x _ => x + x₀) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact C.add_mem hx hx₀C
      · intro x₁ _ x₂ _ heq
        ext i
        have hi := congrFun (congrArg (· + x₀) heq) i
        simp only [Pi.add_apply] at hi
        rw [add_assoc, add_assoc, zmod2_add_self, add_zero, add_zero] at hi
        exact hi
      · intro x hx
        refine ⟨x + x₀, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact C.add_mem hx hx₀C
        · ext i
          simp only [Pi.add_apply]
          rw [add_assoc, zmod2_add_self, add_zero]
      · intro x _
        have hxx : x + x₀ + x₀ = x := by
          ext i; simp only [Pi.add_apply]; rw [add_assoc, zmod2_add_self, add_zero]
        rw [hxx]
    have hneg : ∑ x ∈ S, chiZ (dot2 (x + x₀) y) = - ∑ x ∈ S, chiZ (dot2 x y) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hdot : dot2 (x + x₀) y = dot2 x y + dot2 x₀ y := by
        simp [dot2, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [hdot, chiZ_add, hx₀1, chiZ_one]
      ring
    linarith

private lemma prod_ite_eq_pow_wt {n : ℕ} {R : Type*} [CommRing R]
    (x : Fin n → ZMod 2) (X Y : R) :
    (∏ i : Fin n, (if x i = 0 then X else Y)) = X ^ (n - wt x) * Y ^ (wt x) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter (fun i : Fin n => ¬ x i = 0)).card = wt x := rfl
  have h2 : (Finset.univ.filter (fun i : Fin n => x i = 0)).card = n - wt x := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => x i = 0)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    change (Finset.univ.filter (fun i : Fin n => x i = 0)).card + wt x = n at hsum
    omega
  rw [h1, h2]

private lemma hadamard_weight_transform {n : ℕ} {R : Type*} [CommRing R]
    (x : Fin n → ZMod 2) (X Y : R) :
    ∑ y : Fin n → ZMod 2, (chiZ (dot2 x y) : R) * (X ^ (n - wt y) * Y ^ (wt y)) =
      (X + Y) ^ (n - wt x) * (X - Y) ^ (wt x) := by
  have hstep1 : ∀ y : Fin n → ZMod 2,
      (chiZ (dot2 x y) : R) * (X ^ (n - wt y) * Y ^ (wt y)) =
        ∏ i : Fin n, ((chiZ (x i * y i) : R) * (if y i = 0 then X else Y)) := by
    intro y
    rw [dot2, chiZ_sum, Int.cast_prod, ← prod_ite_eq_pow_wt y X Y, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun y _ => hstep1 y]
  rw [← Fintype.prod_sum (fun i a => (chiZ (x i * a) : R) * (if a = 0 then X else Y))]
  have hinner : ∀ i : Fin n,
      (∑ a : ZMod 2, (chiZ (x i * a) : R) * (if a = 0 then X else Y)) =
        if x i = 0 then X + Y else X - Y := by
    intro i
    have h01 : (∑ a : ZMod 2, (chiZ (x i * a) : R) * (if a = 0 then X else Y)) =
        ((chiZ (x i * 0) : R) * (if (0 : ZMod 2) = 0 then X else Y)) +
        ((chiZ (x i * 1) : R) * (if (1 : ZMod 2) = 0 then X else Y)) :=
      Fin.sum_univ_two (fun a : ZMod 2 => (chiZ (x i * a) : R) * (if a = 0 then X else Y))
    rw [h01]
    have hxi := zmod2_eq_zero_or_one (x i)
    rcases hxi with hx | hx
    · simp [hx, chiZ_zero]
    · simp [hx, chiZ_zero, chiZ_one, sub_eq_add_neg]
  rw [Finset.prod_congr rfl fun i _ => hinner i]
  exact prod_ite_eq_pow_wt x (X + Y) (X - Y)

/-- **Theorem 2.1 (Binary MacWilliams Weight-Enumerator Identity over Any Commutative Ring):**
For every binary linear code `C ≤ 𝔽₂ⁿ`, its orthogonal dual `D = C^⊥`, and any `X, Y` in a
commutative ring `R`,
`|C| * W_{C^⊥}(X, Y) = W_C(X + Y, X - Y)`. -/
theorem macwilliams_identity_ring {n : ℕ} {R : Type*} [CommRing R]
    (C D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hD : ∀ y : Fin n → ZMod 2, y ∈ D ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0)
    (X Y : R) :
    ((Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card : R) *
      ∑ y ∈ Finset.univ.filter (fun y : Fin n → ZMod 2 => y ∈ D),
        X ^ (n - (Finset.univ.filter (fun i : Fin n => y i ≠ 0)).card) *
        Y ^ (Finset.univ.filter (fun i : Fin n => y i ≠ 0)).card =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        (X + Y) ^ (n - (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) *
        (X - Y) ^ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card := by
  have hDeq : D = dualCode C := by
    ext y; exact hD y
  subst hDeq
  let SC := Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)
  let SD := Finset.univ.filter (fun y : Fin n → ZMod 2 => y ∈ dualCode C)
  have hrhs :
      ∑ x ∈ SC, (X + Y) ^ (n - wt x) * (X - Y) ^ (wt x) =
        ∑ x ∈ SC, ∑ y : Fin n → ZMod 2,
          (chiZ (dot2 x y) : R) * (X ^ (n - wt y) * Y ^ (wt y)) := by
    refine Finset.sum_congr rfl fun x _ => (hadamard_weight_transform x X Y).symm
  rw [show (∑ x ∈ SC, (X + Y) ^ (n - (Finset.univ.filter (fun i => x i ≠ 0)).card) *
      (X - Y) ^ (Finset.univ.filter (fun i => x i ≠ 0)).card) =
      ∑ x ∈ SC, (X + Y) ^ (n - wt x) * (X - Y) ^ (wt x) from rfl]
  rw [hrhs, Finset.sum_comm]
  have hinner : ∀ y : Fin n → ZMod 2,
      ∑ x ∈ SC, (chiZ (dot2 x y) : R) * (X ^ (n - wt y) * Y ^ (wt y)) =
        (if y ∈ dualCode C then (SC.card : R) else 0) * (X ^ (n - wt y) * Y ^ (wt y)) := by
    intro y
    rw [← Finset.sum_mul]
    congr 1
    have hZ := sum_chiZ_dot2_eq C y
    have hR := congrArg (Int.cast (R := R)) hZ
    push_cast at hR
    simpa [SC] using hR
  rw [Finset.sum_congr rfl fun y _ => hinner y]
  have hfilter :
      ∑ y : Fin n → ZMod 2,
        (if y ∈ dualCode C then (SC.card : R) else 0) * (X ^ (n - wt y) * Y ^ (wt y)) =
      ∑ y ∈ SD, (SC.card : R) * (X ^ (n - wt y) * Y ^ (wt y)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  rw [hfilter, ← Finset.mul_sum]
  rfl

/-- **Theorem 2.2 (Binary MacWilliams Identity over a Field of Characteristic Zero):**
`W_{C^⊥}(X, Y) = (|C| : K)⁻¹ * W_C(X + Y, X - Y)`. -/
theorem macwilliams_identity_field {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (C D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hD : ∀ y : Fin n → ZMod 2, y ∈ D ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0)
    (X Y : K) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin n → ZMod 2 => y ∈ D),
        X ^ (n - (Finset.univ.filter (fun i : Fin n => y i ≠ 0)).card) *
        Y ^ (Finset.univ.filter (fun i : Fin n => y i ≠ 0)).card =
      ((Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card : K)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        (X + Y) ^ (n - (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) *
        (X - Y) ^ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card := by
  have hring := macwilliams_identity_ring (R := K) C D hD X Y
  have hpos : 0 < (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, C.zero_mem⟩⟩
  have hne : ((Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  rw [← hring, inv_mul_cancel_left₀ hne]

/-- **Theorem 2.3 (MacWilliams Self-Duality Invariance over `ℝ`):**
For every self-dual binary code `C = C^⊥` and all `X, Y : ℝ`,
`W_C((X + Y) / √2, (X - Y) / √2) = W_C(X, Y)`. -/
theorem macwilliams_selfDual_real {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0)
    (X Y : ℝ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        ((X + Y) / Real.sqrt 2) ^ (n - (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) *
        ((X - Y) / Real.sqrt 2) ^ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        X ^ (n - (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) *
        Y ^ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card := by
  obtain ⟨h2dim, heven, hcard⟩ := selfDual_finrank_and_card C hSD
  have hmw := macwilliams_identity_ring (R := ℝ) C C hSD X Y
  have hsqrt_pow : (Real.sqrt 2) ^ n = (2 : ℝ) ^ (n / 2) := by
    rcases heven with ⟨k, rfl⟩
    have hk : (k + k) / 2 = k := by omega
    rw [hk, ← two_mul, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt_ne : (Real.sqrt 2) ^ n ≠ 0 := by
    rw [hsqrt_pow]
    positivity
  have hterm : ∀ x : Fin n → ZMod 2,
      ((X + Y) / Real.sqrt 2) ^ (n - wt x) * ((X - Y) / Real.sqrt 2) ^ (wt x) =
        ((Real.sqrt 2) ^ n)⁻¹ * ((X + Y) ^ (n - wt x) * (X - Y) ^ (wt x)) := by
    intro x
    have hle := wt_le x
    rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.sub_add_cancel hle, div_eq_inv_mul]
  calc
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        ((X + Y) / Real.sqrt 2) ^ (n - wt x) * ((X - Y) / Real.sqrt 2) ^ (wt x)
      = ((Real.sqrt 2) ^ n)⁻¹ *
          ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
            (X + Y) ^ (n - wt x) * (X - Y) ^ (wt x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => hterm x
    _ = ((2 : ℝ) ^ (n / 2))⁻¹ *
          (((Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card : ℝ) *
            ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
              X ^ (n - wt x) * Y ^ (wt x)) := by
          change ((Real.sqrt 2) ^ n)⁻¹ *
            ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
              (X + Y) ^ (n - (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) *
              (X - Y) ^ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card = _
          rw [hsqrt_pow, ← hmw]
          rfl
    _ = ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
          X ^ (n - wt x) * Y ^ (wt x) := by
          rw [hcard]
          push_cast
          have h2ne : ((2 : ℝ) ^ (n / 2)) ≠ 0 := by positivity
          rw [inv_mul_cancel_left₀ h2ne]

/-- **Theorem 2.4 (Gleason–Pierce Divisibility `8 ∣ n` for Type II Self-Dual Codes):**
Every doubly-even (Type II) self-dual binary linear code of length `n` has `8 ∣ n`.
Proved from the MacWilliams identity evaluated at `(1, i) ∈ ℂ²`. -/
theorem gleason_pierce_eight_dvd_length {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) :
    8 ∣ n := by
  have h1mem : (fun _ : Fin n => (1 : ZMod 2)) ∈ C :=
    (selfDual_ones_mem_and_weight_symm C hSD).1
  have h4n : 4 ∣ n := by
    have h := hT2 _ h1mem
    simpa [wt_ones] using h
  rcases h4n with ⟨m, rfl⟩
  obtain ⟨_, _, hcard⟩ := selfDual_finrank_and_card C hSD
  have hmw := macwilliams_identity_ring (R := ℂ) C C hSD (1 : ℂ) Complex.I
  let SC := Finset.univ.filter (fun x : Fin (4 * m) → ZMod 2 => x ∈ C)
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    have h : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
    rw [h, Complex.I_sq]
    norm_num
  have hnegI4 : (-Complex.I : ℂ) ^ 4 = 1 := by
    have h : (-Complex.I) ^ 4 = ((-Complex.I) ^ 2) ^ 2 := by ring
    rw [h]
    simp [Complex.I_sq]
  have hL : ∑ x ∈ SC, (1 : ℂ) ^ (4 * m - wt x) * Complex.I ^ (wt x) = (SC.card : ℂ) := by
    have hterm : ∀ x ∈ SC, (1 : ℂ) ^ (4 * m - wt x) * Complex.I ^ (wt x) = 1 := by
      intro x hx
      rcases hT2 x (Finset.mem_filter.mp hx).2 with ⟨k, hk⟩
      change wt x = 4 * k at hk
      rw [one_pow, one_mul, hk, pow_mul, hI4, one_pow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hR : ∑ x ∈ SC, (1 + Complex.I) ^ (4 * m - wt x) * (1 - Complex.I) ^ (wt x) =
      (SC.card : ℂ) * (1 + Complex.I) ^ (4 * m) := by
    have hsub : (1 - Complex.I : ℂ) = (-Complex.I) * (1 + Complex.I) := by
      linear_combination Complex.I_sq
    have hterm : ∀ x ∈ SC,
        (1 + Complex.I) ^ (4 * m - wt x) * (1 - Complex.I) ^ (wt x) =
          (1 + Complex.I) ^ (4 * m) := by
      intro x hx
      have hle := wt_le x
      rcases hT2 x (Finset.mem_filter.mp hx).2 with ⟨k, hk⟩
      change wt x = 4 * k at hk
      rw [hsub, mul_pow, hk, pow_mul, hnegI4, one_pow, one_mul, ← pow_add, ← hk,
        Nat.sub_add_cancel hle]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  change (SC.card : ℂ) * ∑ x ∈ SC, (1 : ℂ) ^ (4 * m - wt x) * Complex.I ^ (wt x) =
    ∑ x ∈ SC, (1 + Complex.I) ^ (4 * m - wt x) * (1 - Complex.I) ^ (wt x) at hmw
  rw [hL, hR] at hmw
  have hcard_ne : (SC.card : ℂ) ≠ 0 := by
    have hpos : 0 < SC.card :=
      Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, C.zero_mem⟩⟩
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  have heq : (SC.card : ℂ) = (1 + Complex.I) ^ (4 * m) :=
    mul_left_cancel₀ hcard_ne hmw
  have h1pI4 : (1 + Complex.I : ℂ) ^ 4 = -4 := by
    have h : (1 + Complex.I : ℂ) ^ 2 = 2 * Complex.I := by
      have hi := Complex.I_sq
      linear_combination hi
    calc
      (1 + Complex.I : ℂ) ^ 4 = ((1 + Complex.I : ℂ) ^ 2) ^ 2 := by ring
      _ = (2 * Complex.I) ^ 2 := by rw [h]
      _ = 4 * Complex.I ^ 2 := by ring
      _ = -4 := by rw [Complex.I_sq]; norm_num
  have h4m_half : (4 * m) / 2 = 2 * m := by omega
  have hcard_val : (SC.card : ℂ) = (4 : ℂ) ^ m := by
    change ((Finset.univ.filter (fun x : Fin (4 * m) → ZMod 2 => x ∈ C)).card : ℂ) = (4 : ℂ) ^ m
    rw [hcard, h4m_half]
    push_cast
    rw [pow_mul]
    norm_num
  rw [hcard_val, pow_mul, h1pI4] at heq
  have hneg4 : (-4 : ℂ) ^ m = (-1 : ℂ) ^ m * (4 : ℂ) ^ m := by
    rw [← mul_pow]
    norm_num
  rw [hneg4] at heq
  have h4ne : (4 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hsign : (-1 : ℂ) ^ m = 1 := by
    have hmul : (1 : ℂ) * (4 : ℂ) ^ m = (-1 : ℂ) ^ m * (4 : ℂ) ^ m := by
      rw [one_mul]; exact heq
    exact (mul_right_cancel₀ h4ne hmul).symm
  have heven_m : Even m := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hneg1 : (-1 : ℂ) ^ m = -1 := Odd.neg_one_pow hodd
    rw [hneg1] at hsign
    norm_num at hsign
  rcases heven_m with ⟨k, rfl⟩
  exact ⟨k, by ring⟩

/-! #### Pless Power Moments (0th, 1st, and 2nd Moments) -/

private lemma coeff_one_add_X_pow_mul_one_sub_X_pow_zero (a b : ℕ) :
    (((1 + Polynomial.X : Polynomial ℚ) ^ a * (1 - Polynomial.X : Polynomial ℚ) ^ b).coeff 0) = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp

private lemma coeff_one_add_X_pow_one (a : ℕ) :
    ((1 + Polynomial.X : Polynomial ℚ) ^ a).coeff 1 = (a : ℚ) := by
  induction a with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X, ih,
      Polynomial.coeff_zero_eq_eval_zero]
    simp [add_comm]

private lemma coeff_one_sub_X_pow_one (b : ℕ) :
    ((1 - Polynomial.X : Polynomial ℚ) ^ b).coeff 1 = -(b : ℚ) := by
  induction b with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ, mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_mul_X, ih,
      Polynomial.coeff_zero_eq_eval_zero]
    simp
    ring

private lemma coeff_one_add_X_pow_two (a : ℕ) :
    2 * ((1 + Polynomial.X : Polynomial ℚ) ^ a).coeff 2 = (a : ℚ) * ((a : ℚ) - 1) := by
  induction a with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X,
      coeff_one_add_X_pow_one]
    push_cast
    linarith

private lemma coeff_one_sub_X_pow_two (b : ℕ) :
    2 * ((1 - Polynomial.X : Polynomial ℚ) ^ b).coeff 2 = (b : ℚ) * ((b : ℚ) - 1) := by
  induction b with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ, mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
      coeff_one_sub_X_pow_one]
    push_cast
    linarith

private lemma coeff_krawtchouk_two (n w : ℕ) (hw : w ≤ n) :
    2 * (((1 + Polynomial.X : Polynomial ℚ) ^ (n - w) *
      (1 - Polynomial.X : Polynomial ℚ) ^ w).coeff 2) =
      4 * (w : ℚ) ^ 2 - 4 * (n : ℚ) * (w : ℚ) + (n : ℚ) * ((n : ℚ) - 1) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => ((1 + Polynomial.X : Polynomial ℚ) ^ (n - w)).coeff i *
      ((1 - Polynomial.X : Polynomial ℚ) ^ w).coeff j) 2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have h0a : ((1 + Polynomial.X : Polynomial ℚ) ^ (n - w)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; simp
  have h0b : ((1 - Polynomial.X : Polynomial ℚ) ^ w).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; simp
  have h1a := coeff_one_add_X_pow_one (n - w)
  have h1b := coeff_one_sub_X_pow_one w
  have h2a := coeff_one_add_X_pow_two (n - w)
  have h2b := coeff_one_sub_X_pow_two w
  rw [h0a, h0b, h1a, h1b, one_mul, mul_one]
  have hsub : ((n - w : ℕ) : ℚ) = (n : ℚ) - (w : ℚ) := Nat.cast_sub hw
  rw [hsub] at h1a h2a ⊢
  linarith

/-- **Theorem 2.5 (Pless Power Moments — 0th, 1st, and 2nd Moments for Self-Dual Codes):**
For every self-dual binary linear code `C = C^⊥` of length `n`:
1. 0th moment: `∑_{x ∈ C} 1 = 2^(n / 2)`.
2. 1st moment: `2 * ∑_{x ∈ C} wt(x) = n * 2^(n / 2)` (equivalently `∑ wt(x) = (n / 2) * 2^(n / 2)`).
3. 2nd moment (when minimum distance `d(C) ≥ 3`):
   `4 * ∑_{x ∈ C} wt(x)^2 = n * (n + 1) * 2^(n / 2)`. -/
theorem pless_power_moments_selfDual {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0) :
    (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).card = 2 ^ (n / 2) ∧
    (2 * ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
        (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card = n * 2 ^ (n / 2)) ∧
    ((∀ x ∈ C, x ≠ 0 → 3 ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) →
      4 * ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C),
          (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card ^ 2 =
        n * (n + 1) * 2 ^ (n / 2)) := by
  obtain ⟨h2dim, heven, hcard⟩ := selfDual_finrank_and_card C hSD
  have h1mem := (selfDual_ones_mem_and_weight_symm C hSD).1
  let SC := Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)
  -- 1st moment via the involution x ↦ x + 1
  have hm1 : 2 * ∑ x ∈ SC, wt x = n * 2 ^ (n / 2) := by
    have hshift : ∑ x ∈ SC, wt (x + fun _ => 1) = ∑ x ∈ SC, wt x := by
      refine Finset.sum_bij (fun x _ => x + fun _ => 1) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact C.add_mem hx h1mem
      · intro x₁ _ x₂ _ heq
        ext i
        have hi := congrFun (congrArg (· + fun _ => (1 : ZMod 2)) heq) i
        simp only [Pi.add_apply] at hi
        rw [add_assoc, add_assoc, zmod2_add_self, add_zero, add_zero] at hi
        exact hi
      · intro x hx
        refine ⟨x + fun _ => 1, ?_, ?_⟩
        · simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact C.add_mem hx h1mem
        · ext i
          simp only [Pi.add_apply]
          rw [add_assoc, zmod2_add_self, add_zero]
      · intro x _; rfl
    have hpair : ∑ x ∈ SC, wt x + ∑ x ∈ SC, wt (x + fun _ => 1) = ∑ x ∈ SC, n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [wt_add_ones]
      have hle := wt_le x
      omega
    rw [hshift, Finset.sum_const, smul_eq_mul] at hpair
    change SC.card = 2 ^ (n / 2) at hcard
    rw [hcard, mul_comm] at hpair
    linarith
  refine ⟨hcard, hm1, ?_⟩
  -- 2nd moment via MacWilliams over Polynomial ℚ at X = 1, Y = Polynomial.X
  intro hd3
  have hmw := macwilliams_identity_ring (R := Polynomial ℚ) C C hSD (1 : Polynomial ℚ) Polynomial.X
  have hcoeff2 := congrArg (fun p : Polynomial ℚ => 2 * p.coeff 2) hmw
  -- LHS coeff 2 is 0 since no codeword has weight 2
  have hL0 : (∑ y ∈ SC, (1 : Polynomial ℚ) ^ (n - wt y) * Polynomial.X ^ (wt y)).coeff 2 = 0 := by
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [one_pow, one_mul, Polynomial.coeff_X_pow]
    rw [if_neg]
    intro h2
    have hyC : y ∈ C := (Finset.mem_filter.mp hy).2
    have hyne : y ≠ 0 := by
      intro h0
      rw [h0, wt_zero] at h2
      omega
    have hge := hd3 y hyC hyne
    change 3 ≤ wt y at hge
    omega
  have hL : 2 * (((SC.card : Polynomial ℚ) *
      ∑ y ∈ SC, (1 : Polynomial ℚ) ^ (n - wt y) * Polynomial.X ^ (wt y)).coeff 2) = 0 := by
    rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul, hL0, mul_zero, mul_zero]
  have hR : 2 * (∑ x ∈ SC, (1 + Polynomial.X : Polynomial ℚ) ^ (n - wt x) *
      (1 - Polynomial.X : Polynomial ℚ) ^ (wt x)).coeff 2 =
      4 * ∑ x ∈ SC, ((wt x : ℚ) ^ 2) - 4 * (n : ℚ) * ∑ x ∈ SC, (wt x : ℚ) +
        (n : ℚ) * ((n : ℚ) - 1) * (SC.card : ℚ) := by
    rw [Polynomial.finsetSum_coeff, Finset.mul_sum]
    have hterm : ∀ x ∈ SC,
        2 * (((1 + Polynomial.X : Polynomial ℚ) ^ (n - wt x) *
          (1 - Polynomial.X : Polynomial ℚ) ^ (wt x)).coeff 2) =
          4 * (wt x : ℚ) ^ 2 - 4 * (n : ℚ) * (wt x : ℚ) + (n : ℚ) * ((n : ℚ) - 1) :=
      fun x _ => coeff_krawtchouk_two n (wt x) (wt_le x)
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    ring
  change 2 * (((SC.card : Polynomial ℚ) *
      ∑ y ∈ SC, (1 : Polynomial ℚ) ^ (n - wt y) * Polynomial.X ^ (wt y)).coeff 2) =
    2 * (∑ x ∈ SC, (1 + Polynomial.X : Polynomial ℚ) ^ (n - wt x) *
      (1 - Polynomial.X : Polynomial ℚ) ^ (wt x)).coeff 2 at hcoeff2
  rw [hL, hR] at hcoeff2
  have hm1Q : (2 : ℚ) * ∑ x ∈ SC, (wt x : ℚ) = (n : ℚ) * (2 : ℚ) ^ (n / 2) := by
    exact_mod_cast hm1
  have hcardQ : (SC.card : ℚ) = (2 : ℚ) ^ (n / 2) := by
    exact_mod_cast hcard
  have hm2Q : (4 : ℚ) * ∑ x ∈ SC, (wt x : ℚ) ^ 2 = (n : ℚ) * ((n : ℚ) + 1) * (2 : ℚ) ^ (n / 2) := by
    rw [hcardQ] at hcoeff2
    linear_combination -hcoeff2 + 2 * (n : ℚ) * hm1Q
  exact_mod_cast hm2Q

/-! ### Section 3: Explicit Extremal Type II Witnesses (`[8, 4, 4]` Hamming & `[24, 12, 8]` Golay) -/

/-- The `RM(1, 3)` linear encoding map `𝔽₂⁴ → 𝔽₂⁸` generating the Extended Hamming `[8, 4, 4]`
code. Coordinate `i ∈ Fin 8` corresponds to the binary triple `(i % 2, (i / 2) % 2, (i / 4) % 2)`. -/
private def hamming8Map : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun u i :=
    u 0 + u 1 * ((i.val % 2 : ℕ) : ZMod 2) +
    u 2 * (((i.val / 2) % 2 : ℕ) : ZMod 2) +
    u 3 * (((i.val / 4) % 2 : ℕ) : ZMod 2)
  map_add' u v := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private lemma hamming8Map_injective : Function.Injective hamming8Map := by
  intro u v huv
  have h0 := congrFun huv 0
  have h1 := congrFun huv 1
  have h2 := congrFun huv 2
  have h4 := congrFun huv 4
  simp only [hamming8Map, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.zero_mod, Nat.zero_div, Nat.cast_zero, mul_zero, add_zero,
    Nat.one_mod, Nat.cast_one, mul_one] at h0 h1 h2 h4
  have h1' : u 1 = v 1 := by
    have : u 0 + u 1 = v 0 + v 1 := by simpa using h1
    rw [h0] at this
    exact add_left_cancel this
  have h2' : u 2 = v 2 := by
    have : u 0 + u 2 = v 0 + v 2 := by simpa using h2
    rw [h0] at this
    exact add_left_cancel this
  have h3' : u 3 = v 3 := by
    have : u 0 + u 3 = v 0 + v 3 := by simpa using h4
    rw [h0] at this
    exact add_left_cancel this
  ext j
  fin_cases j
  · exact h0
  · exact h1'
  · exact h2'
  · exact h3'

private lemma wt_hamming8Map (u : Fin 4 → ZMod 2) :
    wt (hamming8Map u) =
      if u 1 = 0 ∧ u 2 = 0 ∧ u 3 = 0 then (if u 0 = 0 then 0 else 8) else 4 := by
  have hsum : wt (hamming8Map u) =
      ∑ i : Fin 8, if hamming8Map u i ≠ 0 then 1 else 0 := by
    simp [wt, Finset.card_filter]
  rw [hsum, Fin.sum_univ_eight]
  simp only [hamming8Map, LinearMap.coe_mk, AddHom.coe_mk]
  rcases zmod2_eq_zero_or_one (u 0) with h0 | h0 <;>
  rcases zmod2_eq_zero_or_one (u 1) with h1 | h1 <;>
  rcases zmod2_eq_zero_or_one (u 2) with h2 | h2 <;>
  rcases zmod2_eq_zero_or_one (u 3) with h3 | h3 <;>
  simp [h0, h1, h2, h3, zmod2_add_self]

private def hamming8Code : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
  LinearMap.range hamming8Map

private lemma hamming8Code_finrank : Module.finrank (ZMod 2) hamming8Code = 4 := by
  rw [hamming8Code, LinearMap.finrank_range_of_inj hamming8Map_injective, Module.finrank_fin_fun]

private lemma hamming8Code_typeII : ∀ x ∈ hamming8Code, 4 ∣ wt x := by
  intro x hx
  rcases hx with ⟨u, rfl⟩
  rw [wt_hamming8Map]
  split_ifs <;> decide

private lemma hamming8Code_selfDual :
    ∀ y : Fin 8 → ZMod 2, y ∈ hamming8Code ↔ ∀ x ∈ hamming8Code, dot2 x y = 0 := by
  have hle : hamming8Code ≤ dualCode hamming8Code := by
    intro y hy x hx
    exact doublyEven_is_selfOrthogonal hamming8Code hamming8Code_typeII x hx y hy
  have hdim_dual : Module.finrank (ZMod 2) (dualCode hamming8Code) = 4 := by
    have h := finrank_add_finrank_dualCode hamming8Code
    rw [hamming8Code_finrank] at h
    omega
  have heq : hamming8Code = dualCode hamming8Code :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hamming8Code_finrank, hdim_dual])
  intro y
  conv_lhs => rw [heq]
  rfl

private lemma card_weight_eq_of_selfDual_range {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (w : ℕ) :
    (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C ∧ wt x = w)).card =
      ((Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C)).filter (fun x => wt x = w)).card := by
  congr 1
  ext x
  simp

/-- **Theorem 3.1 (Explicit Extremal Type II `[8, 4, 4]` Extended Binary Hamming Code):**
There exists a binary linear code `C ≤ 𝔽₂⁸` that is:
1. Self-dual (`C = C^⊥`), of dimension `4`;
2. Type II / doubly-even (`∀ x ∈ C, 4 ∣ wt(x)`);
3. Of exact minimum Hamming distance `4`;
4. With exact weight enumerator `W_C(X, Y) = X^8 + 14 X^4 Y^4 + Y^8` over every commutative ring `R`
   (equivalently `A_0 = 1`, `A_4 = 14`, `A_8 = 1`, and `A_w = 0` for all `w ∉ {0, 4, 8}`). -/
theorem exists_extremal_typeII_hamming8 :
    ∃ C : Submodule (ZMod 2) (Fin 8 → ZMod 2),
      Module.finrank (ZMod 2) C = 4 ∧
      (∀ y : Fin 8 → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin 8, x i * y i) = 0) ∧
      (∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card) ∧
      (∀ x ∈ C, x ≠ 0 → 4 ≤ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card) ∧
      (∃ x ∈ C, x ≠ 0 ∧ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card = 4) ∧
      (Finset.univ.filter (fun x : Fin 8 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card = 0)).card = 1 ∧
      (Finset.univ.filter (fun x : Fin 8 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card = 4)).card = 14 ∧
      (Finset.univ.filter (fun x : Fin 8 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card = 8)).card = 1 ∧
      (∀ (R : Type) [CommRing R] (X Y : R),
        ∑ x ∈ Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ C),
          X ^ (8 - (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card) *
          Y ^ (Finset.univ.filter (fun i : Fin 8 => x i ≠ 0)).card =
        X ^ 8 + 14 * X ^ 4 * Y ^ 4 + Y ^ 8) := by
  refine ⟨hamming8Code, hamming8Code_finrank, hamming8Code_selfDual, hamming8Code_typeII,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- d ≥ 4
    intro x hx hne
    have h4 := hamming8Code_typeII x hx
    have hpos : 0 < wt x := by
      by_contra h0
      have hwx : wt x = 0 := by omega
      exact hne ((wt_eq_zero_iff x).mp hwx)
    rcases h4 with ⟨k, hk⟩
    change wt x = 4 * k at hk
    change 4 ≤ wt x
    omega
  · -- witness of weight 4
    refine ⟨hamming8Map (Pi.single 1 1), ⟨Pi.single 1 1, rfl⟩, ?_, ?_⟩
    · intro h0
      have := hamming8Map_injective (by simpa using h0 : hamming8Map (Pi.single 1 1) = hamming8Map 0)
      have h1 := congrFun this 1
      simp at h1
    · change wt (hamming8Map (Pi.single 1 1)) = 4
      rw [wt_hamming8Map]
      simp
  · -- A_0 = 1
    have hset : Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (wt_eq_zero_iff x).mp h.2
      · rintro rfl; exact ⟨hamming8Code.zero_mem, wt_zero⟩
    change (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0)).card = 1
    rw [hset, Finset.card_singleton]
  · -- A_4 = 14
    have hcard := (selfDual_finrank_and_card hamming8Code hamming8Code_selfDual).2.2
    have hA0 : (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0)).card = 1 := by
      have hset : Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0) = {0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; exact (wt_eq_zero_iff x).mp h.2
        · rintro rfl; exact ⟨hamming8Code.zero_mem, wt_zero⟩
      rw [hset, Finset.card_singleton]
    have hA8 : (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 8)).card = 1 := by
      have hsym := (selfDual_ones_mem_and_weight_symm hamming8Code hamming8Code_selfDual).2 0 (by omega)
      simpa [wt] using hsym.trans hA0
    have hpart :
        (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code)).card =
          (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0)).card +
          (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 4)).card +
          (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 8)).card := by
      have hunion :
          Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code) =
            (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0) ∪
             Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 4)) ∪
            Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 8) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hx
          have h4 := hamming8Code_typeII x hx
          have hle := wt_le x
          rcases h4 with ⟨k, hk⟩
          have hk2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
          rcases hk2 with rfl | rfl | rfl <;> simp [hx, hk]
        · rintro ((h | h) | h) <;> exact h.1
      rw [hunion, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        omega
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        rcases hx1 with h | h <;> omega
    change (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 4)).card = 14
    omega
  · -- A_8 = 1
    have hA0 : (Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0)).card = 1 := by
      have hset : Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0) = {0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; exact (wt_eq_zero_iff x).mp h.2
        · rintro rfl; exact ⟨hamming8Code.zero_mem, wt_zero⟩
      rw [hset, Finset.card_singleton]
    have hsym := (selfDual_ones_mem_and_weight_symm hamming8Code hamming8Code_selfDual).2 0 (by omega)
    simpa [wt] using hsym.trans hA0
  · -- Weight enumerator over any CommRing R
    intro R _ X Y
    let S0 := Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 0)
    let S4 := Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 4)
    let S8 := Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code ∧ wt x = 8)
    have hA0 : S0.card = 1 := by
      have hset : S0 = {0} := by
        ext x
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => (wt_eq_zero_iff x).mp h.2, by rintro rfl; exact ⟨hamming8Code.zero_mem, wt_zero⟩⟩
      rw [hset, Finset.card_singleton]
    have hA8 : S8.card = 1 := by
      have hsym := (selfDual_ones_mem_and_weight_symm hamming8Code hamming8Code_selfDual).2 0 (by omega)
      simpa [S8, S0, wt] using hsym.trans hA0
    have hunion :
        Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code) = (S0 ∪ S4) ∪ S8 := by
      ext x
      simp only [S0, S4, S8, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        rcases hamming8Code_typeII x hx with ⟨k, hk⟩
        have hle := wt_le x
        have hk2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk2 with rfl | rfl | rfl <;> simp [hx, hk]
      · rintro ((h | h) | h) <;> exact h.1
    have hdisj04 : Disjoint S0 S4 := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [S0, S4, Finset.mem_filter] at hx1 hx2; omega
    have hdisj048 : Disjoint (S0 ∪ S4) S8 := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [S0, S4, S8, Finset.mem_union, Finset.mem_filter] at hx1 hx2
      rcases hx1 with h | h <;> omega
    have hA4 : S4.card = 14 := by
      have hcard := (selfDual_finrank_and_card hamming8Code hamming8Code_selfDual).2.2
      rw [hunion, Finset.card_union_of_disjoint hdisj048, Finset.card_union_of_disjoint hdisj04] at hcard
      omega
    change ∑ x ∈ Finset.univ.filter (fun x : Fin 8 → ZMod 2 => x ∈ hamming8Code),
        X ^ (8 - wt x) * Y ^ (wt x) = X ^ 8 + 14 * X ^ 4 * Y ^ 4 + Y ^ 8
    rw [hunion, Finset.sum_union hdisj048, Finset.sum_union hdisj04]
    have hsum0 : ∑ x ∈ S0, X ^ (8 - wt x) * Y ^ (wt x) = X ^ 8 := by
      have h1 : ∀ x ∈ S0, X ^ (8 - wt x) * Y ^ (wt x) = X ^ 8 := by
        intro x hx; rw [(Finset.mem_filter.mp hx).2.2]; simp
      rw [Finset.sum_congr rfl h1, Finset.sum_const, hA0, one_nsmul]
    have hsum4 : ∑ x ∈ S4, X ^ (8 - wt x) * Y ^ (wt x) = 14 * X ^ 4 * Y ^ 4 := by
      have h1 : ∀ x ∈ S4, X ^ (8 - wt x) * Y ^ (wt x) = X ^ 4 * Y ^ 4 := by
        intro x hx; rw [(Finset.mem_filter.mp hx).2.2]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, hA4, nsmul_eq_mul]
      ring
    have hsum8 : ∑ x ∈ S8, X ^ (8 - wt x) * Y ^ (wt x) = Y ^ 8 := by
      have h1 : ∀ x ∈ S8, X ^ (8 - wt x) * Y ^ (wt x) = Y ^ 8 := by
        intro x hx; rw [(Finset.mem_filter.mp hx).2.2]; simp
      rw [Finset.sum_congr rfl h1, Finset.sum_const, hA8, one_nsmul]
    rw [hsum0, hsum4, hsum8]

/-! #### Explicit `[24, 12, 8]` Extended Binary Golay Code via Turyn's APN Construction -/

/-- The `𝔽₈`-cube APN permutation `(2 3 4 5 6 7)` on `Fin 8`, fixing `0` and `1`. -/
private def apnPerm : Equiv.Perm (Fin 8) where
  toFun
    | ⟨0, _⟩ => ⟨0, by decide⟩
    | ⟨1, _⟩ => ⟨1, by decide⟩
    | ⟨2, _⟩ => ⟨3, by decide⟩
    | ⟨3, _⟩ => ⟨4, by decide⟩
    | ⟨4, _⟩ => ⟨5, by decide⟩
    | ⟨5, _⟩ => ⟨6, by decide⟩
    | ⟨6, _⟩ => ⟨7, by decide⟩
    | ⟨7, _⟩ => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => ⟨0, by decide⟩
    | ⟨1, _⟩ => ⟨1, by decide⟩
    | ⟨2, _⟩ => ⟨7, by decide⟩
    | ⟨3, _⟩ => ⟨2, by decide⟩
    | ⟨4, _⟩ => ⟨3, by decide⟩
    | ⟨5, _⟩ => ⟨4, by decide⟩
    | ⟨6, _⟩ => ⟨5, by decide⟩
    | ⟨7, _⟩ => ⟨6, by decide⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private lemma wt_comp_perm {n : ℕ} (x : Fin n → ZMod 2) (σ : Equiv.Perm (Fin n)) :
    wt (x ∘ σ) = wt x := by
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
    exact hi
  · intro i₁ _ i₂ _ h
    exact σ.injective h
  · intro j hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply] at hj ⊢
    exact hj

/-- Zero-case-split linear-algebra proof that `H₈ ∩ σ(H₈) = {0, 1}`. -/
private lemma hamming8_inter_apn_const {u v : Fin 4 → ZMod 2}
    (h : hamming8Map u = hamming8Map v ∘ apnPerm) :
    u 1 = 0 ∧ u 2 = 0 ∧ u 3 = 0 := by
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  have e6 := congrFun h 6
  simp only [hamming8Map, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, apnPerm,
    Equiv.coe_fn_mk] at e0 e1 e2 e3 e4 e5 e6
  norm_num at e0 e1 e2 e3 e4 e5 e6
  -- e0 : u 0 = v 0
  -- e1 : u 0 + u 1 = v 0 + v 1
  -- e2 : u 0 + u 2 = v 0 + v 1 + v 2
  -- e3 : u 0 + u 1 + u 2 = v 0 + v 3
  -- e4 : u 0 + u 3 = v 0 + v 1 + v 3
  -- e5 : u 0 + u 1 + u 3 = v 0 + v 2 + v 3
  -- e6 : u 0 + u 2 + u 3 = v 0 + v 1 + v 2 + v 3
  have hv1 : v 1 = u 1 := by
    rw [← e0] at e1; exact (add_left_cancel e1).symm
  have hv2 : v 2 = u 1 + u 2 := by
    have : u 0 + u 2 = u 0 + (u 1 + v 2) := by rw [← e0, hv1] at e2; linear_combination e2
    have h12 : u 2 = u 1 + v 2 := add_left_cancel this
    have hadd := congrArg (u 1 + ·) h12
    rw [← add_assoc, zmod2_add_self, zero_add] at hadd
    exact hadd.symm
  have hv3 : v 3 = u 1 + u 3 := by
    have : u 0 + u 3 = u 0 + (u 1 + v 3) := by rw [← e0, hv1] at e4; linear_combination e4
    have h13 : u 3 = u 1 + v 3 := add_left_cancel this
    have hadd := congrArg (u 1 + ·) h13
    rw [← add_assoc, zmod2_add_self, zero_add] at hadd
    exact hadd.symm
  have hu23 : u 2 = u 3 := by
    rw [← e0, hv3] at e3
    have : (u 0 + u 1) + u 2 = (u 0 + u 1) + u 3 := by linear_combination e3
    exact add_left_cancel this
  have hu1_eq_0 : u 1 = 0 := by
    rw [← e0, hv1, hv2, hv3] at e6
    have : (u 0 + u 2 + u 3) + 0 = (u 0 + u 2 + u 3) + u 1 := by
      have h11 := zmod2_add_self (u 1)
      linear_combination e6 + h11
    exact (add_left_cancel this).symm
  have hu3_eq_0 : u 3 = 0 := by
    rw [← e0, hv2, hv3, hu1_eq_0, zero_add, zero_add, add_zero] at e5
    have : (u 0 + u 3) + 0 = (u 0 + u 3) + u 2 := by linear_combination e5
    have hu2_eq_0 : u 2 = 0 := (add_left_cancel this).symm
    rw [← hu23, hu2_eq_0]
  exact ⟨hu1_eq_0, hu23.trans hu3_eq_0, hu3_eq_0⟩

private def concat3 (u v w : Fin 8 → ZMod 2) : Fin 24 → ZMod 2 :=
  fun i =>
    if h1 : i.val < 8 then u ⟨i.val, h1⟩
    else if h2 : i.val < 16 then v ⟨i.val - 8, by omega⟩
    else w ⟨i.val - 16, by omega⟩

private lemma concat3_add (u₁ v₁ w₁ u₂ v₂ w₂ : Fin 8 → ZMod 2) :
    concat3 (u₁ + u₂) (v₁ + v₂) (w₁ + w₂) = concat3 u₁ v₁ w₁ + concat3 u₂ v₂ w₂ := by
  ext i
  simp only [concat3, Pi.add_apply]
  split_ifs <;> rfl

private lemma concat3_smul (c : ZMod 2) (u v w : Fin 8 → ZMod 2) :
    concat3 (c • u) (c • v) (c • w) = c • concat3 u v w := by
  ext i
  simp only [concat3, Pi.smul_apply]
  split_ifs <;> rfl

private lemma concat3_eq_zero_iff (u v w : Fin 8 → ZMod 2) :
    concat3 u v w = 0 ↔ u = 0 ∧ v = 0 ∧ w = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · ext j
      have hj := congrFun h ⟨j.val, by omega⟩
      simpa [concat3, j.isLt] using hj
    · ext j
      have hj := congrFun h ⟨j.val + 8, by omega⟩
      have h1 : ¬ (j.val + 8 < 8) := by omega
      have h2 : j.val + 8 < 16 := by omega
      simp [concat3, h1, h2] at hj
      exact hj
    · ext j
      have hj := congrFun h ⟨j.val + 16, by omega⟩
      have h1 : ¬ (j.val + 16 < 8) := by omega
      have h2 : ¬ (j.val + 16 < 16) := by omega
      simp [concat3, h1, h2] at hj
      exact hj
  · rintro ⟨rfl, rfl, rfl⟩
    ext i
    simp only [concat3, Pi.zero_apply]
    split_ifs <;> rfl

private lemma wt_concat3 (u v w : Fin 8 → ZMod 2) :
    wt (concat3 u v w) = wt u + wt v + wt w := by
  let e : Fin 24 ≃ Fin 8 ⊕ Fin 8 ⊕ Fin 8 :=
    { toFun := fun i =>
        if h1 : i.val < 8 then Sum.inl ⟨i.val, h1⟩
        else if h2 : i.val < 16 then Sum.inr (Sum.inl ⟨i.val - 8, by omega⟩)
        else Sum.inr (Sum.inr ⟨i.val - 16, by omega⟩)
      invFun := fun s => match s with
        | Sum.inl j => ⟨j.val, by omega⟩
        | Sum.inr (Sum.inl j) => ⟨j.val + 8, by omega⟩
        | Sum.inr (Sum.inr j) => ⟨j.val + 16, by omega⟩
      left_inv := fun i => by
        dsimp only
        split_ifs with h1 h2 <;> ext <;> simp <;> omega
      right_inv := fun s => by
        rcases s with j | (j | j)
        · simp [j.isLt]
        · have h1 : ¬ (j.val + 8 < 8) := by omega
          have h2 : j.val + 8 < 16 := by omega
          simp [h1, h2]
        · have h1 : ¬ (j.val + 16 < 8) := by omega
          have h2 : ¬ (j.val + 16 < 16) := by omega
          simp [h1, h2] }
  simp only [wt, Finset.card_filter]
  rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∀ j : Fin 8, (if concat3 u v w (e.symm (Sum.inl j)) ≠ 0 then 1 else 0) =
      if u j ≠ 0 then 1 else 0 := by
    intro j; simp [e, concat3, j.isLt]
  have h2 : ∀ j : Fin 8, (if concat3 u v w (e.symm (Sum.inr (Sum.inl j))) ≠ 0 then 1 else 0) =
      if v j ≠ 0 then 1 else 0 := by
    intro j
    have ha : ¬ (j.val + 8 < 8) := by omega
    have hb : j.val + 8 < 16 := by omega
    simp [e, concat3, ha, hb]
  have h3 : ∀ j : Fin 8, (if concat3 u v w (e.symm (Sum.inr (Sum.inr j))) ≠ 0 then 1 else 0) =
      if w j ≠ 0 then 1 else 0 := by
    intro j
    have ha : ¬ (j.val + 16 < 8) := by omega
    have hb : ¬ (j.val + 16 < 16) := by omega
    simp [e, concat3, ha, hb]
  simp only [h1, h2, h3]
  omega

/-- Turyn's linear encoding `(u, v, w) ↦ (H(u) + B(w), H(v) + B(w), H(u) + H(v) + B(w))`
generating the Extended Binary Golay `[24, 12, 8]` code. -/
private def golay24Map :
    ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun t :=
    let a := hamming8Map t.1
    let b := hamming8Map t.2.1
    let x := hamming8Map t.2.2 ∘ apnPerm
    concat3 (a + x) (b + x) (a + b + x)
  map_add' t₁ t₂ := by
    dsimp only
    rw [Prod.fst_add, Prod.snd_add, Prod.fst_add, Prod.snd_add,
      map_add, map_add, map_add]
    have hcomp : (hamming8Map t₁.2.2 + hamming8Map t₂.2.2) ∘ apnPerm =
        hamming8Map t₁.2.2 ∘ apnPerm + hamming8Map t₂.2.2 ∘ apnPerm := by
      ext i; rfl
    rw [hcomp, ← concat3_add]
    congr 1 <;> abel
  map_smul' c t := by
    dsimp only [RingHom.id_apply]
    rw [Prod.smul_fst, Prod.smul_snd, Prod.smul_fst, Prod.smul_snd,
      map_smul, map_smul, map_smul]
    have hcomp : (c • hamming8Map t.2.2) ∘ apnPerm = c • (hamming8Map t.2.2 ∘ apnPerm) := by
      ext i; rfl
    rw [hcomp, ← concat3_smul]
    congr 1 <;> simp [smul_add]

private lemma golay24Map_injective : Function.Injective golay24Map := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨u, v, w⟩ h
  simp only [golay24Map, LinearMap.coe_mk, AddHom.coe_mk, concat3_eq_zero_iff] at h
  rcases h with ⟨h1, h2, h3⟩
  have hx0 : hamming8Map w ∘ apnPerm = 0 := by
    ext i
    have hi1 := congrFun h1 i
    have hi2 := congrFun h2 i
    have hi3 := congrFun h3 i
    simp only [Pi.add_apply, Pi.zero_apply] at hi1 hi2 hi3 ⊢
    linear_combination hi1 + hi2 - hi3
  have hw : w = 0 := by
    have hhw : hamming8Map w = 0 := by
      ext j
      have := congrFun hx0 (apnPerm.symm j)
      simpa using this
    exact hamming8Map_injective (by simpa using hhw)
  rw [hx0, add_zero] at h1 h2
  have hu : u = 0 := hamming8Map_injective (by simpa using h1)
  have hv : v = 0 := hamming8Map_injective (by simpa using h2)
  simp [hu, hv, hw]

private def golay24Code : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  LinearMap.range golay24Map

private lemma golay24Code_finrank : Module.finrank (ZMod 2) golay24Code = 12 := by
  rw [golay24Code, LinearMap.finrank_range_of_inj golay24Map_injective,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun]

private lemma two_dvd_turyn_inter (a b x : Fin 8 → ZMod 2) :
    2 ∣ (inter a x + inter b x + inter (a + b) x) := by
  have hsum : inter a x + inter b x + inter (a + b) x =
      ∑ i : Fin 8,
        ((if a i ≠ 0 ∧ x i ≠ 0 then 1 else 0) +
         (if b i ≠ 0 ∧ x i ≠ 0 then 1 else 0) +
         (if (a + b) i ≠ 0 ∧ x i ≠ 0 then 1 else 0)) := by
    simp only [inter, Finset.card_filter, Finset.sum_add_distrib]
  rw [hsum]
  refine Finset.dvd_sum fun i _ => ?_
  simp only [Pi.add_apply]
  rcases zmod2_eq_zero_or_one (a i) with ha | ha <;>
  rcases zmod2_eq_zero_or_one (b i) with hb | hb <;>
  rcases zmod2_eq_zero_or_one (x i) with hx | hx <;>
  simp [ha, hb, hx, zmod2_add_self]

private lemma golay24Code_typeII : ∀ c ∈ golay24Code, 4 ∣ wt c := by
  rintro c ⟨⟨u, v, w⟩, rfl⟩
  simp only [golay24Map, LinearMap.coe_mk, AddHom.coe_mk, wt_concat3]
  set a := hamming8Map u
  set b := hamming8Map v
  set x := hamming8Map w ∘ apnPerm
  have hwa : 4 ∣ wt a := hamming8Code_typeII a ⟨u, rfl⟩
  have hwb : 4 ∣ wt b := hamming8Code_typeII b ⟨v, rfl⟩
  have hwab : 4 ∣ wt (a + b) := hamming8Code_typeII (a + b) ⟨u + v, map_add _ _ _⟩
  have hwx : 4 ∣ wt x := by
    rw [wt_comp_perm]
    exact hamming8Code_typeII (hamming8Map w) ⟨w, rfl⟩
  have h1 := wt_add_two_inter a x
  have h2 := wt_add_two_inter b x
  have h3 := wt_add_two_inter (a + b) x
  have hev := two_dvd_turyn_inter a b x
  rcases hwa with ⟨k1, hk1⟩
  rcases hwb with ⟨k2, hk2⟩
  rcases hwab with ⟨k3, hk3⟩
  rcases hwx with ⟨k4, hk4⟩
  rcases hev with ⟨k5, hk5⟩
  omega

private lemma golay24Code_selfDual :
    ∀ y : Fin 24 → ZMod 2, y ∈ golay24Code ↔ ∀ x ∈ golay24Code, dot2 x y = 0 := by
  have hle : golay24Code ≤ dualCode golay24Code := by
    intro y hy x hx
    exact doublyEven_is_selfOrthogonal golay24Code golay24Code_typeII x hx y hy
  have hdim_dual : Module.finrank (ZMod 2) (dualCode golay24Code) = 12 := by
    have h := finrank_add_finrank_dualCode golay24Code
    rw [golay24Code_finrank] at h
    omega
  have heq : golay24Code = dualCode golay24Code :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [golay24Code_finrank, hdim_dual])
  intro y
  conv_lhs => rw [heq]
  rfl

private lemma golay24Code_minDist_ge_eight : ∀ c ∈ golay24Code, c ≠ 0 → 8 ≤ wt c := by
  rintro c ⟨⟨u, v, w⟩, rfl⟩ hne
  have h4 := golay24Code_typeII _ ⟨⟨u, v, w⟩, rfl⟩
  have hpos : 0 < wt (golay24Map (u, v, w)) := by
    by_contra h0
    exact hne ((wt_eq_zero_iff _).mp (by omega))
  suffices hne4 : wt (golay24Map (u, v, w)) ≠ 4 by
    rcases h4 with ⟨k, hk⟩
    omega
  intro hwt4
  simp only [golay24Map, LinearMap.coe_mk, AddHom.coe_mk, wt_concat3] at hwt4
  set a := hamming8Map u
  set b := hamming8Map v
  set x := hamming8Map w ∘ apnPerm
  have even_add : ∀ p q : Fin 8 → ZMod 2, 4 ∣ wt p → 4 ∣ wt q → 2 ∣ wt (p + q) := by
    intro p q hp hq
    have h := wt_add_two_inter p q
    rcases hp with ⟨k1, hk1⟩; rcases hq with ⟨k2, hk2⟩; omega
  have hwa : 4 ∣ wt a := hamming8Code_typeII a ⟨u, rfl⟩
  have hwb : 4 ∣ wt b := hamming8Code_typeII b ⟨v, rfl⟩
  have hwab : 4 ∣ wt (a + b) := hamming8Code_typeII (a + b) ⟨u + v, map_add _ _ _⟩
  have hwx : 4 ∣ wt x := by rw [wt_comp_perm]; exact hamming8Code_typeII _ ⟨w, rfl⟩
  have he1 : 2 ∣ wt (a + x) := even_add a x hwa hwx
  have he2 : 2 ∣ wt (b + x) := even_add b x hwb hwx
  have he3 : 2 ∣ wt (a + b + x) := even_add (a + b) x hwab hwx
  -- Three even natural numbers summing to 4 must include at least one 0
  have hzero : wt (a + x) = 0 ∨ wt (b + x) = 0 ∨ wt (a + b + x) = 0 := by
    rcases he1 with ⟨e1, he1⟩
    rcases he2 with ⟨e2, he2⟩
    rcases he3 with ⟨e3, he3⟩
    omega
  -- Helper: if x = hamming8Map r, then wt x ∈ {0, 8}
  have hx_const : ∀ r : Fin 4 → ZMod 2, hamming8Map r = x → wt x = 0 ∨ wt x = 8 := by
    intro r hr
    have hc := hamming8_inter_apn_const hr
    have hwr : wt (hamming8Map r) = if r 0 = 0 then 0 else 8 := by
      rw [wt_hamming8Map, if_pos hc]
    rw [← hr, hwr]
    split_ifs <;> simp
  rcases hzero with h0 | h0 | h0
  · have hax : a + x = 0 := (wt_eq_zero_iff _).mp h0
    have hxa : a = x := by
      ext i
      have hi := congrFun hax i
      simp only [Pi.add_apply, Pi.zero_apply] at hi
      have hadd := congrArg (· + x i) hi
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
      exact hadd
    have hwx08 := hx_const u hxa
    have h1 : a + b + x = b := by
      ext i; simp only [Pi.add_apply, hxa]; rw [add_comm (x i), add_assoc, zmod2_add_self, add_zero]
    have h2 : b + x = hamming8Map (v + u) := by
      rw [map_add, ← hxa]
    have hwbx : 4 ∣ wt (b + x) := by rw [h2]; exact hamming8Code_typeII _ ⟨v + u, rfl⟩
    rw [h0, zero_add, h1] at hwt4
    rcases hwbx with ⟨k1, hk1⟩
    rcases hwb with ⟨k2, hk2⟩
    have hcases : (wt (b + x) = 0 ∧ wt b = 4) ∨ (wt (b + x) = 4 ∧ wt b = 0) := by omega
    rcases hcases with ⟨hbx0, hb4⟩ | ⟨hbx4, hb0⟩
    · have hbx : b + x = 0 := (wt_eq_zero_iff _).mp hbx0
      have hxb : b = x := by
        ext i; have hi := congrFun hbx i; simp only [Pi.add_apply, Pi.zero_apply] at hi
        have hadd := congrArg (· + x i) hi
        rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd; exact hadd
      rw [hxb] at hb4; omega
    · have hb0' : b = 0 := (wt_eq_zero_iff _).mp hb0
      rw [hb0', zero_add] at hbx4; omega
  · have hbx : b + x = 0 := (wt_eq_zero_iff _).mp h0
    have hxb : b = x := by
      ext i; have hi := congrFun hbx i; simp only [Pi.add_apply, Pi.zero_apply] at hi
      have hadd := congrArg (· + x i) hi
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd; exact hadd
    have hwx08 := hx_const v hxb
    have h1 : a + b + x = a := by
      ext i; simp only [Pi.add_apply, hxb]; rw [add_assoc, zmod2_add_self, add_zero]
    have h2 : a + x = hamming8Map (u + v) := by
      rw [map_add, ← hxb]
    have hwax : 4 ∣ wt (a + x) := by rw [h2]; exact hamming8Code_typeII _ ⟨u + v, rfl⟩
    rw [h0, add_zero, h1] at hwt4
    rcases hwax with ⟨k1, hk1⟩
    rcases hwa with ⟨k2, hk2⟩
    have hcases : (wt (a + x) = 0 ∧ wt a = 4) ∨ (wt (a + x) = 4 ∧ wt a = 0) := by omega
    rcases hcases with ⟨hax0, ha4⟩ | ⟨hax4, ha0⟩
    · have hax : a + x = 0 := (wt_eq_zero_iff _).mp hax0
      have hxa : a = x := by
        ext i; have hi := congrFun hax i; simp only [Pi.add_apply, Pi.zero_apply] at hi
        have hadd := congrArg (· + x i) hi
        rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd; exact hadd
      rw [hxa] at ha4; omega
    · have ha0' : a = 0 := (wt_eq_zero_iff _).mp ha0
      rw [ha0', zero_add] at hax4; omega
  · have habx : a + b + x = 0 := (wt_eq_zero_iff _).mp h0
    have hxab : hamming8Map (u + v) = x := by
      rw [map_add]
      ext i; have hi := congrFun habx i; simp only [Pi.add_apply, Pi.zero_apply] at hi
      have hadd := congrArg (· + x i) hi
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd; exact hadd
    have hwx08 := hx_const (u + v) hxab
    have h1 : a + x = b := by
      ext i; simp only [Pi.add_apply, ← hxab, map_add]
      rw [← add_assoc, zmod2_add_self, zero_add]
    have h2 : b + x = a := by
      ext i; simp only [Pi.add_apply, ← hxab, map_add]
      rw [add_comm (hamming8Map u i), ← add_assoc, zmod2_add_self, zero_add]
    rw [h0, add_zero, h1, h2] at hwt4
    rcases hwa with ⟨k1, hk1⟩
    rcases hwb with ⟨k2, hk2⟩
    have hcases : (wt b = 0 ∧ wt a = 4) ∨ (wt b = 4 ∧ wt a = 0) := by omega
    rcases hcases with ⟨hb0, ha4⟩ | ⟨hb4, ha0⟩
    · have hb0' : b = 0 := (wt_eq_zero_iff _).mp hb0
      have hxa : x = a := by rw [← hxab, map_add, show hamming8Map v = 0 from hb0', add_zero]
      rw [hxa] at hwx08; omega
    · have ha0' : a = 0 := (wt_eq_zero_iff _).mp ha0
      have hxb : x = b := by rw [← hxab, map_add, show hamming8Map u = 0 from ha0', zero_add]
      rw [hxb] at hwx08; omega

/-- **Theorem 3.2 (Explicit Extremal Type II `[24, 12, 8]` Extended Binary Golay Code):**
There exists a binary linear code `C ≤ 𝔽₂²⁴` (constructed algebraically via Turyn's APN
construction, with zero `native_decide`) that is:
1. Self-dual (`C = C^⊥`), of dimension `12`;
2. Type II / doubly-even (`∀ x ∈ C, 4 ∣ wt(x)`);
3. Of exact minimum Hamming distance `8`;
4. With exact weight counts `A_0 = 1`, `A_4 = 0`, `A_8 = 759`, `A_{12} = 2576`, `A_{16} = 759`,
   `A_{20} = 0`, `A_{24} = 1`, and exact weight enumerator
   `W_C(X, Y) = X^{24} + 759 X^{16} Y^8 + 2576 X^{12} Y^{12} + 759 X^8 Y^{16} + Y^{24}`
   over every commutative ring `R`. -/
theorem exists_extremal_typeII_golay24 :
    ∃ C : Submodule (ZMod 2) (Fin 24 → ZMod 2),
      Module.finrank (ZMod 2) C = 12 ∧
      (∀ y : Fin 24 → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin 24, x i * y i) = 0) ∧
      (∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card) ∧
      (∀ x ∈ C, x ≠ 0 → 8 ≤ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card) ∧
      (∃ x ∈ C, x ≠ 0 ∧ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card = 8) ∧
      (Finset.univ.filter (fun x : Fin 24 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card = 0)).card = 1 ∧
      (Finset.univ.filter (fun x : Fin 24 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card = 8)).card = 759 ∧
      (Finset.univ.filter (fun x : Fin 24 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card = 12)).card = 2576 ∧
      (Finset.univ.filter (fun x : Fin 24 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card = 16)).card = 759 ∧
      (Finset.univ.filter (fun x : Fin 24 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card = 24)).card = 1 ∧
      (∀ (R : Type) [CommRing R] (X Y : R),
        ∑ x ∈ Finset.univ.filter (fun x : Fin 24 → ZMod 2 => x ∈ C),
          X ^ (24 - (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card) *
          Y ^ (Finset.univ.filter (fun i : Fin 24 => x i ≠ 0)).card =
        X ^ 24 + 759 * X ^ 16 * Y ^ 8 + 2576 * X ^ 12 * Y ^ 12 +
          759 * X ^ 8 * Y ^ 16 + Y ^ 24) := by
  let S (w : ℕ) := Finset.univ.filter (fun x : Fin 24 → ZMod 2 => x ∈ golay24Code ∧ wt x = w)
  have hA0 : (S 0).card = 1 := by
    have hset : S 0 = {0} := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => (wt_eq_zero_iff x).mp h.2, by rintro rfl; exact ⟨golay24Code.zero_mem, wt_zero⟩⟩
    rw [hset, Finset.card_singleton]
  have hA24 : (S 24).card = 1 := by
    have hsym := (selfDual_ones_mem_and_weight_symm golay24Code golay24Code_selfDual).2 0 (by omega)
    simpa [S, wt] using hsym.trans hA0
  have hA4 : (S 4).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    have hne : x ≠ 0 := by intro h0; rw [h0, wt_zero] at hx; omega
    have hge := golay24Code_minDist_ge_eight x hx.1 hne
    omega
  have hA20 : (S 20).card = 0 := by
    have hsym := (selfDual_ones_mem_and_weight_symm golay24Code golay24Code_selfDual).2 4 (by omega)
    simpa [S, wt] using hsym.trans hA4
  have hA16_eq : (S 16).card = (S 8).card := by
    have hsym := (selfDual_ones_mem_and_weight_symm golay24Code golay24Code_selfDual).2 8 (by omega)
    simpa [S, wt] using hsym
  -- Partition golay24Code into S 0, S 8, S 12, S 16, S 24
  have hunion : Finset.univ.filter (fun x : Fin 24 → ZMod 2 => x ∈ golay24Code) =
      (((S 0 ∪ S 8) ∪ S 12) ∪ S 16) ∪ S 24 := by
    ext x
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rcases golay24Code_typeII x hx with ⟨k, hk⟩
      have hle := wt_le x
      have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [hx, hk]
      · exfalso
        have hmem : x ∈ S 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, by omega⟩
        rw [Finset.card_eq_zero.mp hA4] at hmem; exact Finset.notMem_empty x hmem
      · simp [hx, hk]
      · simp [hx, hk]
      · simp [hx, hk]
      · exfalso
        have hmem : x ∈ S 20 := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, by omega⟩
        rw [Finset.card_eq_zero.mp hA20] at hmem; exact Finset.notMem_empty x hmem
      · simp [hx, hk]
    · rintro ((((h | h) | h) | h) | h) <;> exact h.1
  have hdisj : ∀ a b : ℕ, a ≠ b → Disjoint (S a) (S b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [S, Finset.mem_filter] at hx1 hx2
    omega
  have hd08 : Disjoint (S 0) (S 8) := hdisj 0 8 (by omega)
  have hd0812 : Disjoint (S 0 ∪ S 8) (S 12) :=
    Finset.disjoint_union_left.mpr ⟨hdisj 0 12 (by omega), hdisj 8 12 (by omega)⟩
  have hd081216 : Disjoint ((S 0 ∪ S 8) ∪ S 12) (S 16) :=
    Finset.disjoint_union_left.mpr ⟨
      Finset.disjoint_union_left.mpr ⟨hdisj 0 16 (by omega), hdisj 8 16 (by omega)⟩,
      hdisj 12 16 (by omega)⟩
  have hdall : Disjoint (((S 0 ∪ S 8) ∪ S 12) ∪ S 16) (S 24) :=
    Finset.disjoint_union_left.mpr ⟨
      Finset.disjoint_union_left.mpr ⟨
        Finset.disjoint_union_left.mpr ⟨hdisj 0 24 (by omega), hdisj 8 24 (by omega)⟩,
        hdisj 12 24 (by omega)⟩,
      hdisj 16 24 (by omega)⟩
  -- Solve for A_8 and A_12 from 0th and 2nd Pless moments
  obtain ⟨hcard, _, hm2_imp⟩ := pless_power_moments_selfDual golay24Code golay24Code_selfDual
  have hm2 : 4 * ∑ x ∈ Finset.univ.filter (fun x : Fin 24 → ZMod 2 => x ∈ golay24Code),
      wt x ^ 2 = 24 * 25 * 2 ^ 12 := by
    have h := hm2_imp (fun x hx hne => by
      have hge := golay24Code_minDist_ge_eight x hx hne
      change 3 ≤ wt x; omega)
    simpa [wt] using h
  have hsum_card : (S 0).card + (S 8).card + (S 12).card + (S 16).card + (S 24).card = 4096 := by
    rw [hunion, Finset.card_union_of_disjoint hdall, Finset.card_union_of_disjoint hd081216,
      Finset.card_union_of_disjoint hd0812, Finset.card_union_of_disjoint hd08] at hcard
    simpa using hcard
  have hsum_sq :
      ∑ x ∈ Finset.univ.filter (fun x : Fin 24 → ZMod 2 => x ∈ golay24Code), wt x ^ 2 =
        0 * (S 0).card + 64 * (S 8).card + 144 * (S 12).card +
        256 * (S 16).card + 576 * (S 24).card := by
    rw [hunion, Finset.sum_union hdall, Finset.sum_union hd081216,
      Finset.sum_union hd0812, Finset.sum_union hd08]
    have hSw : ∀ w : ℕ, ∑ x ∈ S w, wt x ^ 2 = w ^ 2 * (S w).card := by
      intro w
      have hconst : ∀ x ∈ S w, wt x ^ 2 = w ^ 2 := fun x hx => by
        rw [(Finset.mem_filter.mp hx).2.2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    simp only [hSw]
    ring
  rw [hsum_sq] at hm2
  have hA8 : (S 8).card = 759 := by omega
  have hA12 : (S 12).card = 2576 := by omega
  have hA16 : (S 16).card = 759 := by omega
  refine ⟨golay24Code, golay24Code_finrank, golay24Code_selfDual, golay24Code_typeII,
    golay24Code_minDist_ge_eight, ?_, hA0, hA8, hA12, hA16, hA24, ?_⟩
  · -- Witness of weight 8: golay24Map (Pi.single 1 1, 0, 0) = concat3 a 0 a
    refine ⟨golay24Map (Pi.single 1 1, 0, 0), ⟨(Pi.single 1 1, 0, 0), rfl⟩, ?_, ?_⟩
    · intro h0
      have hinj := golay24Map_injective (by simpa using h0 : golay24Map (Pi.single 1 1, 0, 0) = golay24Map 0)
      have h1 := congrFun (congrArg Prod.fst hinj) 1
      simp at h1
    · change wt (golay24Map (Pi.single 1 1, 0, 0)) = 8
      simp only [golay24Map, LinearMap.coe_mk, AddHom.coe_mk, map_zero, wt_concat3]
      have hcomp0 : (0 : Fin 8 → ZMod 2) ∘ apnPerm = 0 := rfl
      rw [hcomp0, add_zero, zero_add, add_zero, wt_zero, wt_hamming8Map]
      simp
  · -- Exact weight enumerator over any CommRing R
    intro R _ X Y
    change ∑ x ∈ Finset.univ.filter (fun x : Fin 24 → ZMod 2 => x ∈ golay24Code),
        X ^ (24 - wt x) * Y ^ (wt x) =
      X ^ 24 + 759 * X ^ 16 * Y ^ 8 + 2576 * X ^ 12 * Y ^ 12 +
        759 * X ^ 8 * Y ^ 16 + Y ^ 24
    rw [hunion, Finset.sum_union hdall, Finset.sum_union hd081216,
      Finset.sum_union hd0812, Finset.sum_union hd08]
    have hSw : ∀ w : ℕ, ∑ x ∈ S w, X ^ (24 - wt x) * Y ^ (wt x) =
        ((S w).card : R) * (X ^ (24 - w) * Y ^ w) := by
      intro w
      have hconst : ∀ x ∈ S w, X ^ (24 - wt x) * Y ^ (wt x) = X ^ (24 - w) * Y ^ w :=
        fun x hx => by rw [(Finset.mem_filter.mp hx).2.2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    simp only [hSw, hA0, hA8, hA12, hA16, hA24]
    push_cast
    ring

/-! ### Section 4: Gleason's Theorem (1970), Mallows–Sloane Bound (1973), and Unique `[72, 36, 16]` Enumerator -/

private noncomputable def mwTransform (N : ℕ) (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (N + 1),
    Polynomial.C (p.coeff j) * (1 + Polynomial.X) ^ (N - j) * (1 - Polynomial.X) ^ j

private noncomputable def phi8U : Polynomial ℚ :=
  1 + 14 * Polynomial.X + Polynomial.X ^ 2

private noncomputable def delta24U : Polynomial ℚ :=
  Polynomial.X * (1 - Polynomial.X) ^ 4

private noncomputable def phi8 : Polynomial ℚ :=
  phi8U.comp (Polynomial.X ^ 4)

private noncomputable def delta24 : Polynomial ℚ :=
  delta24U.comp (Polynomial.X ^ 4)

private lemma phi8_eq : phi8 = 1 + 14 * Polynomial.X ^ 4 + Polynomial.X ^ 8 := by
  simp only [phi8, phi8U, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.one_comp,
    Polynomial.ofNat_comp, Polynomial.X_comp, Polynomial.pow_comp]
  ring

private lemma delta24_eq : delta24 = Polynomial.X ^ 4 * (1 - Polynomial.X ^ 4) ^ 4 := by
  simp only [delta24, delta24U, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp,
    Polynomial.one_comp, Polynomial.X_comp]

private lemma mwTransform_add (N : ℕ) (p q : Polynomial ℚ) :
    mwTransform N (p + q) = mwTransform N p + mwTransform N q := by
  simp only [mwTransform, Polynomial.coeff_add, map_add, add_mul, Finset.sum_add_distrib]

private lemma mwTransform_sub (N : ℕ) (p q : Polynomial ℚ) :
    mwTransform N (p - q) = mwTransform N p - mwTransform N q := by
  simp only [mwTransform, Polynomial.coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

private lemma mwTransform_C_mul (N : ℕ) (c : ℚ) (p : Polynomial ℚ) :
    mwTransform N (Polynomial.C c * p) = Polynomial.C c * mwTransform N p := by
  simp only [mwTransform, Polynomial.coeff_C_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma mwTransform_sum {ι : Type*} (N : ℕ) (s : Finset ι) (f : ι → Polynomial ℚ) :
    mwTransform N (∑ i ∈ s, f i) = ∑ i ∈ s, mwTransform N (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [mwTransform]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, mwTransform_add, ih]

private lemma mwTransform_C_mul_X_pow (N j : ℕ) (hj : j ≤ N) (c : ℚ) :
    mwTransform N (Polynomial.C c * Polynomial.X ^ j) =
      Polynomial.C c * (1 + Polynomial.X) ^ (N - j) * (1 - Polynomial.X) ^ j := by
  unfold mwTransform
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj'
    exfalso
    exact hj' (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

private lemma poly_eq_sum_range_of_coeff_eq_zero {N : ℕ} {p : Polynomial ℚ}
    (hp : ∀ k, N < k → p.coeff k = 0) :
    p = ∑ j ∈ Finset.range (N + 1), Polynomial.C (p.coeff j) * Polynomial.X ^ j := by
  ext k
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ N
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro hk'; exfalso; exact hk' (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · push Not at hk
    rw [hp k hk]
    symm
    refine Finset.sum_eq_zero fun b hb => ?_
    have hlt : b < N + 1 := Finset.mem_range.mp hb
    have hne : k ≠ b := by omega
    simp [hne]

private lemma mwTransform_mul {N₁ N₂ : ℕ} {p q : Polynomial ℚ}
    (hp : ∀ k, N₁ < k → p.coeff k = 0) (hq : ∀ k, N₂ < k → q.coeff k = 0) :
    mwTransform (N₁ + N₂) (p * q) = mwTransform N₁ p * mwTransform N₂ q := by
  conv_lhs =>
    rw [poly_eq_sum_range_of_coeff_eq_zero hp, poly_eq_sum_range_of_coeff_eq_zero hq]
  rw [Finset.sum_mul]
  rw [mwTransform_sum]
  have hL : ∀ i ∈ Finset.range (N₁ + 1),
      mwTransform (N₁ + N₂)
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i *
          ∑ j ∈ Finset.range (N₂ + 1), Polynomial.C (q.coeff j) * Polynomial.X ^ j) =
      (Polynomial.C (p.coeff i) * (1 + Polynomial.X) ^ (N₁ - i) * (1 - Polynomial.X) ^ i) *
        mwTransform N₂ q := by
    intro i hi
    have hi_le : i ≤ N₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Finset.mul_sum, mwTransform_sum, mwTransform, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ N₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hterm : Polynomial.C (p.coeff i) * Polynomial.X ^ i *
        (Polynomial.C (q.coeff j) * Polynomial.X ^ j) =
        Polynomial.C (p.coeff i * q.coeff j) * Polynomial.X ^ (i + j) := by
      rw [map_mul, pow_add]; ring
    rw [hterm, mwTransform_C_mul_X_pow (N₁ + N₂) (i + j) (by omega), map_mul]
    have hsub : N₁ + N₂ - (i + j) = (N₁ - i) + (N₂ - j) := by omega
    rw [hsub, pow_add, pow_add]
    ring
  rw [Finset.sum_congr rfl hL, ← Finset.sum_mul]
  rfl

private lemma mwTransform_phi8 : mwTransform 8 phi8 = 16 * phi8 := by
  have hdecomp : phi8 =
      Polynomial.C 1 * Polynomial.X ^ 0 +
      Polynomial.C 14 * Polynomial.X ^ 4 +
      Polynomial.C 1 * Polynomial.X ^ 8 := by
    rw [phi8_eq]; simp only [map_one, map_ofNat, pow_zero, mul_one, one_mul]
  conv_lhs => rw [hdecomp]
  rw [mwTransform_add, mwTransform_add,
    mwTransform_C_mul_X_pow 8 0 (by omega),
    mwTransform_C_mul_X_pow 8 4 (by omega),
    mwTransform_C_mul_X_pow 8 8 (by omega),
    phi8_eq]
  simp only [map_one, map_ofNat]
  ring

private lemma mwTransform_delta24 : mwTransform 24 delta24 = 4096 * delta24 := by
  have hdecomp : delta24 =
      Polynomial.C 1 * Polynomial.X ^ 4 +
      Polynomial.C (-4) * Polynomial.X ^ 8 +
      Polynomial.C 6 * Polynomial.X ^ 12 +
      Polynomial.C (-4) * Polynomial.X ^ 16 +
      Polynomial.C 1 * Polynomial.X ^ 20 := by
    rw [delta24_eq]
    simp only [map_one, map_neg, map_ofNat]
    ring
  conv_lhs => rw [hdecomp]
  rw [mwTransform_add, mwTransform_add, mwTransform_add, mwTransform_add,
    mwTransform_C_mul_X_pow 24 4 (by omega),
    mwTransform_C_mul_X_pow 24 8 (by omega),
    mwTransform_C_mul_X_pow 24 12 (by omega),
    mwTransform_C_mul_X_pow 24 16 (by omega),
    mwTransform_C_mul_X_pow 24 20 (by omega),
    delta24_eq]
  simp only [map_one, map_neg, map_ofNat]
  ring

private lemma phi8_coeff_eq_zero_gt (k : ℕ) (hk : 8 < k) : phi8.coeff k = 0 := by
  rw [phi8_eq]
  have hdeg : (1 + 14 * Polynomial.X ^ 4 + Polynomial.X ^ 8 : Polynomial ℚ).natDegree ≤ 8 := by
    compute_degree!
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk)

private lemma delta24_coeff_eq_zero_gt (k : ℕ) (hk : 24 < k) : delta24.coeff k = 0 := by
  rw [delta24_eq]
  have hdeg : (Polynomial.X ^ 4 * (1 - Polynomial.X ^ 4) ^ 4 : Polynomial ℚ).natDegree ≤ 24 := by
    compute_degree!
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk)

private lemma coeff_pow_eq_zero_gt {N : ℕ} {p : Polynomial ℚ}
    (hp : ∀ k, N < k → p.coeff k = 0) (m : ℕ) :
    ∀ k, m * N < k → (p ^ m).coeff k = 0 := by
  induction m with
  | zero =>
    intro k hk
    simp only [zero_mul, pow_zero] at hk ⊢
    rw [Polynomial.coeff_one, if_neg (by omega)]
  | succ m ih =>
    intro k hk
    rw [pow_succ, Polynomial.coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    have hsum : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
    by_cases h1 : m * N < ij.1
    · rw [ih ij.1 h1, zero_mul]
    · have h2 : N < ij.2 := by nlinarith
      rw [hp ij.2 h2, mul_zero]

private lemma mwTransform_phi8_pow (m : ℕ) :
    mwTransform (8 * m) (phi8 ^ m) = (16 : Polynomial ℚ) ^ m * phi8 ^ m := by
  induction m with
  | zero =>
    simp [mwTransform]
  | succ m ih =>
    have heq : 8 * (m + 1) = 8 * m + 8 := by ring
    rw [heq, pow_succ,
      mwTransform_mul (N₁ := 8 * m) (N₂ := 8)
        (by simpa [mul_comm] using coeff_pow_eq_zero_gt phi8_coeff_eq_zero_gt m)
        phi8_coeff_eq_zero_gt,
      ih, mwTransform_phi8]
    ring

private lemma coeff_comp_X_pow_four (g : Polynomial ℚ) (k : ℕ) :
    (g.comp (Polynomial.X ^ 4)).coeff k = if 4 ∣ k then g.coeff (k / 4) else 0 := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add]
    split_ifs <;> ring
  | monomial n a =>
    rw [Polynomial.monomial_comp, ← pow_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_monomial]
    by_cases hdiv : 4 ∣ k
    · rw [if_pos hdiv]
      rcases hdiv with ⟨q, rfl⟩
      have hq : (4 * q) / 4 = q := by omega
      rw [hq]
      by_cases hnq : n = q
      · subst hnq; simp
      · have hne : 4 * q ≠ 4 * n := by omega
        simp [hne, hnq]
    · rw [if_neg hdiv, if_neg]
      intro heq
      exact hdiv ⟨n, heq⟩

private lemma exists_comp_X_pow_four_of_four_dvd {p : Polynomial ℚ}
    (h4 : ∀ k, ¬ 4 ∣ k → p.coeff k = 0) :
    ∃ g : Polynomial ℚ, p = g.comp (Polynomial.X ^ 4) := by
  refine ⟨∑ j ∈ Finset.range (p.natDegree / 4 + 1),
    Polynomial.C (p.coeff (4 * j)) * Polynomial.X ^ j, ?_⟩
  ext k
  rw [coeff_comp_X_pow_four]
  by_cases hdiv : 4 ∣ k
  · rw [if_pos hdiv, Polynomial.finsetSum_coeff]
    rcases hdiv with ⟨q, rfl⟩
    have hq : (4 * q) / 4 = q := by omega
    rw [hq]
    by_cases hle : q ≤ p.natDegree / 4
    · rw [Finset.sum_eq_single q]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hq'; exfalso; exact hq' (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    · have hgt : p.natDegree < 4 * q := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
      symm
      refine Finset.sum_eq_zero fun b hb => ?_
      have hblt : b < p.natDegree / 4 + 1 := Finset.mem_range.mp hb
      have hne : q ≠ b := by omega
      simp [hne]
  · rw [if_neg hdiv]
    exact h4 k hdiv

private lemma dvd_of_one_sub_X_pow_dvd_mul_cyc4 :
    ∀ k : ℕ, ∀ f : Polynomial ℚ,
      (1 - Polynomial.X) ^ k ∣ (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) * f →
      (1 - Polynomial.X) ^ k ∣ f
  | 0, _, _ => one_dvd _
  | k + 1, f, h => by
    have h1 : (1 - Polynomial.X) ∣
        (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) * f :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) h
    have hev : ((1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) * f).eval 1 = 0 := by
      rcases h1 with ⟨q, hq⟩
      rw [hq]
      simp
    have hf1 : f.eval 1 = 0 := by
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_X, Polynomial.eval_pow] at hev
      linarith
    have hXsub1 : (Polynomial.X - 1 : Polynomial ℚ) ∣ f := by
      rw [← Polynomial.C_1, Polynomial.dvd_iff_isRoot]
      exact hf1
    have h1subX : (1 - Polynomial.X : Polynomial ℚ) ∣ f := by
      rcases hXsub1 with ⟨q, hq⟩
      refine ⟨-q, ?_⟩
      rw [hq]; ring
    rcases h1subX with ⟨f', rfl⟩
    have hne : (1 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval 0) h0
      simp at this
    have h' : (1 - Polynomial.X) ^ k ∣
        (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) * f' := by
      rcases h with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply mul_left_cancel₀ hne
      have hpow : (1 - Polynomial.X : Polynomial ℚ) ^ (k + 1) =
          (1 - Polynomial.X) * (1 - Polynomial.X) ^ k := by
        rw [pow_succ']
      linear_combination hq + q * hpow
    rw [pow_succ']
    exact mul_dvd_mul_left (1 - Polynomial.X) (dvd_of_one_sub_X_pow_dvd_mul_cyc4 k f' h')

private lemma one_sub_X_pow_dvd_of_comp_X_pow_four :
    ∀ k : ℕ, ∀ g : Polynomial ℚ,
      (1 - Polynomial.X) ^ k ∣ g.comp (Polynomial.X ^ 4) →
      (1 - Polynomial.X) ^ k ∣ g
  | 0, _, _ => one_dvd _
  | k + 1, g, h => by
    have h1 : (1 - Polynomial.X) ∣ g.comp (Polynomial.X ^ 4) :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) h
    have hg1 : g.eval 1 = 0 := by
      rcases h1 with ⟨q, hq⟩
      have hev := congrArg (Polynomial.eval 1) hq
      simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
        Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, sub_self, zero_mul] at hev
      exact hev
    have h1subX : (1 - Polynomial.X : Polynomial ℚ) ∣ g := by
      have hXsub1 : (Polynomial.X - 1 : Polynomial ℚ) ∣ g := by
        rw [← Polynomial.C_1, Polynomial.dvd_iff_isRoot]; exact hg1
      rcases hXsub1 with ⟨q, hq⟩
      exact ⟨-q, by rw [hq]; ring⟩
    rcases h1subX with ⟨g', rfl⟩
    have hcomp : ((1 - Polynomial.X) * g').comp (Polynomial.X ^ 4) =
        (1 - Polynomial.X) * ((1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) *
          g'.comp (Polynomial.X ^ 4)) := by
      rw [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
      ring
    rw [hcomp, pow_succ'] at h
    have hne : (1 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval 0) h0
      simp at this
    have hcancel : (1 - Polynomial.X) ^ k ∣
        (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) * g'.comp (Polynomial.X ^ 4) := by
      rcases h with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply mul_left_cancel₀ hne
      linear_combination hq
    have hdiv_g' := dvd_of_one_sub_X_pow_dvd_mul_cyc4 k (g'.comp (Polynomial.X ^ 4)) hcancel
    rw [pow_succ']
    exact mul_dvd_mul_left (1 - Polynomial.X) (one_sub_X_pow_dvd_of_comp_X_pow_four k g' hdiv_g')

private lemma mwTransform_top_coeff {m : ℕ} {p : Polynomial ℚ}
    (h4 : ∀ k, ¬ 4 ∣ k → p.coeff k = 0) :
    (mwTransform (8 * m) p).coeff (8 * m) = ∑ j ∈ Finset.range (8 * m + 1), p.coeff j := by
  unfold mwTransform
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj_le : j ≤ 8 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hdiv : 4 ∣ j
  · rcases hdiv with ⟨t, rfl⟩
    have h1 : (1 + Polynomial.X : Polynomial ℚ) = Polynomial.X + Polynomial.C 1 := by
      simp [add_comm]
    have h2 : (1 - Polynomial.X : Polynomial ℚ) ^ (4 * t) =
        (Polynomial.X - Polynomial.C 1 : Polynomial ℚ) ^ (4 * t) := by
      have hsq : (1 - Polynomial.X : Polynomial ℚ) ^ 4 = (Polynomial.X - Polynomial.C 1) ^ 4 := by
        simp only [map_one]; ring
      rw [pow_mul, pow_mul, hsq]
    have hdeg1 : ((1 + Polynomial.X : Polynomial ℚ) ^ (8 * m - 4 * t)).natDegree = 8 * m - 4 * t := by
      rw [h1, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
    have hdeg2 : ((1 - Polynomial.X : Polynomial ℚ) ^ (4 * t)).natDegree = 4 * t := by
      rw [h2, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    have hlc1 : ((1 + Polynomial.X : Polynomial ℚ) ^ (8 * m - 4 * t)).leadingCoeff = 1 := by
      rw [h1, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X_add_C, one_pow]
    have hlc2 : ((1 - Polynomial.X : Polynomial ℚ) ^ (4 * t)).leadingCoeff = 1 := by
      rw [h2, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X_sub_C, one_pow]
    have hne1 : ((1 + Polynomial.X : Polynomial ℚ) ^ (8 * m - 4 * t)) ≠ 0 := by
      rw [h1]; exact pow_ne_zero _ (Polynomial.X_add_C_ne_zero 1)
    have hne2 : ((1 - Polynomial.X : Polynomial ℚ) ^ (4 * t)) ≠ 0 := by
      rw [h2]; exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)
    rw [mul_assoc, Polynomial.coeff_C_mul]
    have hcoeff_prod :
        ((1 + Polynomial.X : Polynomial ℚ) ^ (8 * m - 4 * t) *
          (1 - Polynomial.X : Polynomial ℚ) ^ (4 * t)).coeff (8 * m) = 1 := by
      have hsum_deg : ((1 + Polynomial.X : Polynomial ℚ) ^ (8 * m - 4 * t) *
          (1 - Polynomial.X : Polynomial ℚ) ^ (4 * t)).natDegree = 8 * m := by
        rw [Polynomial.natDegree_mul hne1 hne2, hdeg1, hdeg2]; omega
      conv_lhs => arg 2; rw [← hsum_deg]
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul, hlc1, hlc2, mul_one]
    rw [hcoeff_prod, mul_one]
  · rw [h4 j hdiv, map_zero, zero_mul, zero_mul, Polynomial.coeff_zero]

private lemma gleason_poly_decomp :
    ∀ m : ℕ, ∀ p : Polynomial ℚ,
      (∀ k, 8 * m < k → p.coeff k = 0) →
      (∀ k, ¬ 4 ∣ k → p.coeff k = 0) →
      mwTransform (8 * m) p = Polynomial.C ((16 : ℚ) ^ m) * p →
      ∃ a : Fin (m / 3 + 1) → ℚ,
        p = ∑ k : Fin (m / 3 + 1),
          Polynomial.C (a k) * phi8 ^ (m - 3 * k.val) * delta24 ^ k.val := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro p hp_deg hp_4 hp_mw
    let c0 : ℚ := p.coeff 0
    let q : Polynomial ℚ := p - Polynomial.C c0 * phi8 ^ m
    have hphi_deg : ∀ k, 8 * m < k → (phi8 ^ m).coeff k = 0 := by
      simpa [mul_comm] using coeff_pow_eq_zero_gt phi8_coeff_eq_zero_gt m
    have hphi_4 : ∀ k, ¬ 4 ∣ k → (phi8 ^ m).coeff k = 0 := by
      intro k hk
      have hcomp : phi8 ^ m = (phi8U ^ m).comp (Polynomial.X ^ 4) := by
        rw [phi8, Polynomial.pow_comp]
      rw [hcomp, coeff_comp_X_pow_four, if_neg hk]
    have hq_deg : ∀ k, 8 * m < k → q.coeff k = 0 := by
      intro k hk
      simp only [q, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hp_deg k hk, hphi_deg k hk,
        mul_zero, sub_zero]
    have hq_4 : ∀ k, ¬ 4 ∣ k → q.coeff k = 0 := by
      intro k hk
      simp only [q, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hp_4 k hk, hphi_4 k hk,
        mul_zero, sub_zero]
    have hq_mw : mwTransform (8 * m) q = Polynomial.C ((16 : ℚ) ^ m) * q := by
      simp only [q, mwTransform_sub, mwTransform_C_mul, hp_mw, mwTransform_phi8_pow]
      have h16 : (16 : Polynomial ℚ) ^ m = Polynomial.C ((16 : ℚ) ^ m) := by
        rw [map_pow, map_ofNat]
      rw [h16]
      ring
    have hq0 : q.coeff 0 = 0 := by
      have hphi0 : (phi8 ^ m).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, phi8_eq]
        simp
      simp [q, c0, hphi0]
    -- Show q.coeff (8 * m) = 0 by comparing eval 0 and coeff (8 * m) of mwTransform (8 * m) q
    have hq_top : q.coeff (8 * m) = 0 := by
      have hev0 := congrArg (Polynomial.eval 0) hq_mw
      have hmw0 : (mwTransform (8 * m) q).eval 0 = ∑ j ∈ Finset.range (8 * m + 1), q.coeff j := by
        simp [mwTransform, Polynomial.eval_finsetSum]
      rw [hmw0, Polynomial.eval_mul, Polynomial.eval_C, ← Polynomial.coeff_zero_eq_eval_zero,
        hq0, mul_zero] at hev0
      have htop := congrArg (fun f : Polynomial ℚ => f.coeff (8 * m)) hq_mw
      rw [mwTransform_top_coeff hq_4, hev0, Polynomial.coeff_C_mul] at htop
      have h16ne : (16 : ℚ) ^ m ≠ 0 := by positivity
      exact (mul_eq_zero.mp htop.symm).resolve_left h16ne
    -- Since q = g.comp (X^4) and q.coeff 0 = 0, q.coeff (8 * m) = 0:
    obtain ⟨g, hg⟩ := exists_comp_X_pow_four_of_four_dvd hq_4
    have hg0 : g.coeff 0 = 0 := by
      have h0 := congrArg (fun f : Polynomial ℚ => f.coeff 0) hg
      rw [hq0, coeff_comp_X_pow_four] at h0
      simpa using h0.symm
    have hg_deg : ∀ j, 2 * m ≤ j → g.coeff j = 0 := by
      intro j hj
      have hj4 := congrArg (fun f : Polynomial ℚ => f.coeff (4 * j)) hg
      rw [coeff_comp_X_pow_four, if_pos (dvd_mul_right 4 j)] at hj4
      have hdiv4 : (4 * j) / 4 = j := by omega
      rw [hdiv4] at hj4
      rw [← hj4]
      by_cases heq : 4 * j = 8 * m
      · rw [heq]; exact hq_top
      · exact hq_deg (4 * j) (by omega)
    -- If m < 3, then q = 0!
    -- First show X ∣ g (so X^4 ∣ q) and (1 - X)^4 ∣ g
    have hX_dvd_g : Polynomial.X ∣ g := by
      rw [Polynomial.X_dvd_iff]; exact hg0
    rcases hX_dvd_g with ⟨g₁, hg₁⟩
    -- Express q = X^4 * r where r = g₁.comp (X^4)
    let r : Polynomial ℚ := g₁.comp (Polynomial.X ^ 4)
    have hq_eq_X4r : q = Polynomial.X ^ 4 * r := by
      rw [hg, hg₁, Polynomial.mul_comp, Polynomial.X_comp]
    -- Show (1 - X)^4 ∣ q using mwTransform (8 * m) (X^4 * r) = (1 - X)^4 * mwTransform (8 * m - 4) r
    have h1subX4_dvd_q : (1 - Polynomial.X) ^ 4 ∣ q := by
      by_cases hm0 : m = 0
      · subst hm0
        have hq_zero : q = 0 := by
          ext k
          by_cases hk : k = 0
          · subst hk; exact hq0
          · exact hq_deg k (by omega)
        rw [hq_zero]; exact dvd_zero _
      · have hr_deg : ∀ k, 8 * m - 4 < k → r.coeff k = 0 := by
          intro k hk
          have h4k := congrArg (fun f : Polynomial ℚ => f.coeff (k + 4)) hq_eq_X4r
          have hcoeff_mul : (Polynomial.X ^ 4 * r).coeff (k + 4) = r.coeff k := by
            rw [mul_comm, Polynomial.coeff_mul_X_pow]
          rw [hcoeff_mul] at h4k
          rw [← h4k]
          exact hq_deg (k + 4) (by omega)
        have hsplit : 8 * m = 4 + (8 * m - 4) := by omega
        have hX4_deg : ∀ k, 4 < k → (Polynomial.X ^ 4 : Polynomial ℚ).coeff k = 0 := by
          intro k hk
          rw [Polynomial.coeff_X_pow, if_neg (by omega)]
        have hmw_q := hq_mw
        rw [hq_eq_X4r] at hmw_q
        rw [hsplit] at hmw_q
        rw [mwTransform_mul hX4_deg hr_deg] at hmw_q
        have hmwX4 : mwTransform 4 (Polynomial.X ^ 4) = (1 - Polynomial.X) ^ 4 := by
          have h := mwTransform_C_mul_X_pow 4 4 (le_refl 4) 1
          simpa using h
        rw [hmwX4, ← hq_eq_X4r] at hmw_q
        refine ⟨Polynomial.C (((16 : ℚ) ^ m)⁻¹) * mwTransform (8 * m - 4) r, ?_⟩
        have h16ne : (16 : ℚ) ^ m ≠ 0 := by positivity
        have hinv : Polynomial.C (((16 : ℚ) ^ m)⁻¹) * Polynomial.C ((16 : ℚ) ^ m) = 1 := by
          rw [← map_mul, inv_mul_cancel₀ h16ne, map_one]
        calc
          q = 1 * q := (one_mul q).symm
          _ = Polynomial.C (((16 : ℚ) ^ m)⁻¹) * (Polynomial.C ((16 : ℚ) ^ m) * q) := by
                rw [← mul_assoc, hinv]
          _ = Polynomial.C (((16 : ℚ) ^ m)⁻¹) * ((1 - Polynomial.X) ^ 4 * mwTransform (8 * m - 4) r) := by
                rw [← hmw_q]
          _ = (1 - Polynomial.X) ^ 4 * (Polynomial.C (((16 : ℚ) ^ m)⁻¹) * mwTransform (8 * m - 4) r) := by
                ring
    -- Hence (1 - X)^4 ∣ g, and since (1 - X)^4 ∣ X * g₁ and X ∤ (1 - X), (1 - X)^4 ∣ g₁!
    have h1subX4_dvd_g : (1 - Polynomial.X) ^ 4 ∣ g := by
      rw [hg] at h1subX4_dvd_q
      exact one_sub_X_pow_dvd_of_comp_X_pow_four 4 g h1subX4_dvd_q
    have h1subX4_dvd_g1 : (1 - Polynomial.X) ^ 4 ∣ g₁ := by
      -- Since X and (1 - X)^4 are coprime: induction on k for (1 - X)^k ∣ X * f → (1 - X)^k ∣ f
      have hcop : ∀ k : ℕ, ∀ f : Polynomial ℚ,
          (1 - Polynomial.X) ^ k ∣ Polynomial.X * f → (1 - Polynomial.X) ^ k ∣ f := by
        intro k
        induction k with
        | zero => intro f _; exact one_dvd _
        | succ k ihk =>
          intro f hf
          have hf1 : f.eval 1 = 0 := by
            have h1 : (1 - Polynomial.X) ∣ Polynomial.X * f :=
              dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) hf
            rcases h1 with ⟨u, hu⟩
            have hev := congrArg (Polynomial.eval 1) hu
            simp at hev
            exact hev
          have h1sub : (1 - Polynomial.X : Polynomial ℚ) ∣ f := by
            have hX1 : (Polynomial.X - 1 : Polynomial ℚ) ∣ f := by
              rw [← Polynomial.C_1, Polynomial.dvd_iff_isRoot]; exact hf1
            rcases hX1 with ⟨u, hu⟩; exact ⟨-u, by rw [hu]; ring⟩
          rcases h1sub with ⟨f', rfl⟩
          have hne : (1 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
            intro h0; have := congrArg (Polynomial.eval 0) h0; simp at this
          have h' : (1 - Polynomial.X) ^ k ∣ Polynomial.X * f' := by
            rcases hf with ⟨u, hu⟩
            refine ⟨u, ?_⟩
            apply mul_left_cancel₀ hne
            rw [pow_succ'] at hu
            linear_combination hu
          rw [pow_succ']
          exact mul_dvd_mul_left (1 - Polynomial.X) (ihk f' h')
      rw [hg₁] at h1subX4_dvd_g
      exact hcop 4 g₁ h1subX4_dvd_g
    rcases h1subX4_dvd_g1 with ⟨hU, hhU⟩
    -- Thus g = delta24U * hU, and q = delta24 * s where s = hU.comp (X^4)!
    have hg_eq : g = delta24U * hU := by
      rw [hg₁, hhU, delta24U]; ring
    let s : Polynomial ℚ := hU.comp (Polynomial.X ^ 4)
    have hq_eq : q = delta24 * s := by
      rw [hg, hg_eq, Polynomial.mul_comp, delta24]
    -- Case split: m < 3 vs 3 ≤ m
    by_cases hm3 : m < 3
    · -- Degree of g is < 2 * m ≤ 4 < 5 = deg delta24U, so hU = 0, q = 0!
      have hhU0 : hU = 0 := by
        by_contra hne
        have hdeg_delta : delta24U.natDegree = 5 := by
          have h : delta24U = Polynomial.X - 4 * Polynomial.X ^ 2 + 6 * Polynomial.X ^ 3 -
              4 * Polynomial.X ^ 4 + Polynomial.X ^ 5 := by rw [delta24U]; ring
          rw [h]; compute_degree!
        have hdelta_ne : delta24U ≠ 0 := by
          intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg_delta; omega
        have hdeg_g : g.natDegree = 5 + hU.natDegree := by
          rw [hg_eq, Polynomial.natDegree_mul hdelta_ne hne, hdeg_delta]
        have hg_lt : g.natDegree < 2 * m := by
          by_cases hg0' : g = 0
          · rw [hg0'] at hg_eq
            exact absurd ((mul_eq_zero.mp hg_eq.symm).resolve_left hdelta_ne) hne
          · by_contra hge
            push Not at hge
            have hlc := hg_deg g.natDegree hge
            exact Polynomial.leadingCoeff_ne_zero.mpr hg0' hlc
        omega
      have hq0' : q = 0 := by rw [hq_eq, show s = 0 by simp [s, hhU0], mul_zero]
      have hp_eq : p = Polynomial.C c0 * phi8 ^ m := sub_eq_zero.mp hq0'
      have hdiv3 : m / 3 = 0 := Nat.div_eq_of_lt hm3
      refine ⟨fun _ => c0, ?_⟩
      have hsum : (∑ k : Fin (m / 3 + 1),
          Polynomial.C c0 * phi8 ^ (m - 3 * k.val) * delta24 ^ k.val) =
          Polynomial.C c0 * phi8 ^ m := by
        have hfin : ∀ k : Fin (m / 3 + 1), k = ⟨0, by omega⟩ := fun k => by ext; omega
        rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (m / 3 + 1))]
        · simp
        · intro k _ hk; exact absurd (hfin k) hk
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      rw [hsum, hp_eq]
    · -- 3 ≤ m: apply strong induction to m' = m - 3 and s!
      push Not at hm3
      have hs_deg : ∀ k, 8 * (m - 3) < k → s.coeff k = 0 := by
        -- From g = delta24U * hU and g.coeff j = 0 for j ≥ 2 * m, show hU.coeff j = 0 for j > 2 * (m - 3)
        have hhU_deg : ∀ j, 2 * (m - 3) < j → hU.coeff j = 0 := by
          intro j hj
          by_cases hhU0 : hU = 0
          · rw [hhU0, Polynomial.coeff_zero]
          · have hdeg_delta : delta24U.natDegree = 5 := by
              have h : delta24U = Polynomial.X - 4 * Polynomial.X ^ 2 + 6 * Polynomial.X ^ 3 -
                  4 * Polynomial.X ^ 4 + Polynomial.X ^ 5 := by rw [delta24U]; ring
              rw [h]; compute_degree!
            have hdelta_ne : delta24U ≠ 0 := by
              intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg_delta; omega
            have hdeg_g : g.natDegree = 5 + hU.natDegree := by
              rw [hg_eq, Polynomial.natDegree_mul hdelta_ne hhU0, hdeg_delta]
            have hg_lt : g.natDegree < 2 * m := by
              have hg_ne : g ≠ 0 := by rw [hg_eq]; exact mul_ne_zero hdelta_ne hhU0
              by_contra hge; push Not at hge
              exact Polynomial.leadingCoeff_ne_zero.mpr hg_ne (hg_deg g.natDegree hge)
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        intro k hk
        rw [show s = hU.comp (Polynomial.X ^ 4) from rfl, coeff_comp_X_pow_four]
        split_ifs with hdiv
        · exact hhU_deg (k / 4) (by omega)
        · rfl
      have hs_4 : ∀ k, ¬ 4 ∣ k → s.coeff k = 0 := by
        intro k hk
        rw [show s = hU.comp (Polynomial.X ^ 4) from rfl, coeff_comp_X_pow_four, if_neg hk]
      have hs_mw : mwTransform (8 * (m - 3)) s = Polynomial.C ((16 : ℚ) ^ (m - 3)) * s := by
        have hsplit : 8 * m = 24 + 8 * (m - 3) := by omega
        have hmw := hq_mw
        rw [hq_eq, hsplit, mwTransform_mul delta24_coeff_eq_zero_gt hs_deg,
          mwTransform_delta24] at hmw
        have h4096 : (4096 : Polynomial ℚ) = Polynomial.C ((16 : ℚ) ^ 3) := by
          rw [map_pow, map_ofNat]; norm_num
        have h16pow : (16 : ℚ) ^ m = (16 : ℚ) ^ 3 * (16 : ℚ) ^ (m - 3) := by
          rw [← pow_add, show 3 + (m - 3) = m by omega]
        have hdelta_ne : (4096 : Polynomial ℚ) * delta24 ≠ 0 := by
          have hd_ne : delta24 ≠ 0 := by
            intro h0
            have h2 := congrArg (fun f : Polynomial ℚ => f.coeff 4) h0
            rw [delta24_eq] at h2
            have hexp : (Polynomial.X ^ 4 * (1 - Polynomial.X ^ 4) ^ 4 : Polynomial ℚ) =
                Polynomial.X ^ 4 - 4 * Polynomial.X ^ 8 + 6 * Polynomial.X ^ 12 -
                4 * Polynomial.X ^ 16 + Polynomial.X ^ 20 := by ring
            rw [hexp] at h2
            simp [Polynomial.coeff_X_pow] at h2
          exact mul_ne_zero (by norm_num) hd_ne
        apply mul_left_cancel₀ hdelta_ne
        rw [← mul_assoc] at hmw
        rw [hmw, h4096, h16pow, map_mul]
        ring
      obtain ⟨b, hb⟩ := ih (m - 3) (by omega) s hs_deg hs_4 hs_mw
      -- Assemble a : Fin (m / 3 + 1) → ℚ with a 0 = c0 and a (k + 1) = b k
      let a : Fin (m / 3 + 1) → ℚ := fun k =>
        if hk : k.val = 0 then c0 else b ⟨k.val - 1, by omega⟩
      refine ⟨a, ?_⟩
      have hp_eq : p = Polynomial.C c0 * phi8 ^ m + delta24 * s := by
        rw [← hq_eq]; simp [q]
      rw [hp_eq, hb, Finset.mul_sum]
      have hsplit_sum :
          ∑ k : Fin (m / 3 + 1),
            Polynomial.C (a k) * phi8 ^ (m - 3 * k.val) * delta24 ^ k.val =
          Polynomial.C (a ⟨0, by omega⟩) * phi8 ^ (m - 3 * 0) * delta24 ^ 0 +
          ∑ j : Fin ((m - 3) / 3 + 1),
            Polynomial.C (a ⟨j.val + 1, by omega⟩) *
              phi8 ^ (m - 3 * (j.val + 1)) * delta24 ^ (j.val + 1) := by
        have heq_sum := Fin.sum_univ_succ (n := m / 3)
          (f := fun k : Fin (m / 3 + 1) =>
            Polynomial.C (a k) * phi8 ^ (m - 3 * k.val) * delta24 ^ k.val)
        rw [heq_sum]
        congr 1
        refine Fintype.sum_equiv (finCongr (by omega : m / 3 = (m - 3) / 3 + 1)) _ _ fun k => by
          have hsucc : k.succ = ⟨(finCongr (by omega : m / 3 = (m - 3) / 3 + 1) k).val + 1, by omega⟩ := by
            ext; simp
          rw [hsucc]
      rw [hsplit_sum]
      congr 1
      · simp [a]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have ha_succ : a ⟨j.val + 1, by omega⟩ = b j := by
          simp [a]
        rw [ha_succ, show m - 3 * (j.val + 1) = m - 3 - 3 * j.val by omega, pow_succ]
        ring

/-- **Theorem 4.1 (Gleason's Theorem (1970) for Type II Self-Dual Binary Codes):**
For every Type II (doubly-even) self-dual binary linear code `C` of length `8 * m`,
its univariate weight enumerator `∑_{x ∈ C} X^{wt(x)} ∈ ℚ[X]` lies in the Gleason ring
`ℚ[φ_8, Δ_{24}]`: there exist rational coefficients `a_0, ..., a_{⌊m/3⌋}` such that
`∑_{x ∈ C} X^{wt(x)} = ∑_{k=0}^{⌊m/3⌋} a_k · (1 + 14 X^4 + X^8)^{m - 3k} · (X^4 (1 - X^4)^4)^k`. -/
theorem gleason_theorem_typeII {m : ℕ}
    (C : Submodule (ZMod 2) (Fin (8 * m) → ZMod 2))
    (hSD : ∀ y : Fin (8 * m) → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin (8 * m), x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin (8 * m) => x i ≠ 0)).card) :
    ∃ a : Fin (m / 3 + 1) → ℚ,
      (∑ x ∈ Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C),
        (Polynomial.X : Polynomial ℚ) ^ (Finset.univ.filter (fun i : Fin (8 * m) => x i ≠ 0)).card) =
      ∑ k : Fin (m / 3 + 1),
        Polynomial.C (a k) *
          (1 + 14 * Polynomial.X ^ 4 + Polynomial.X ^ 8) ^ (m - 3 * k.val) *
          (Polynomial.X ^ 4 * (1 - Polynomial.X ^ 4) ^ 4) ^ k.val := by
  let SC := Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C)
  let p : Polynomial ℚ := ∑ x ∈ SC, Polynomial.X ^ (wt x)
  have hp_deg : ∀ k, 8 * m < k → p.coeff k = 0 := by
    intro k hk
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Polynomial.coeff_X_pow, if_neg]
    have hle := wt_le x
    omega
  have hp_4 : ∀ k, ¬ 4 ∣ k → p.coeff k = 0 := by
    intro k hk
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Polynomial.coeff_X_pow, if_neg]
    intro heq
    have h4 := hT2 x (Finset.mem_filter.mp hx).2
    change 4 ∣ wt x at h4
    exact hk (heq ▸ h4)
  have hp_mw : mwTransform (8 * m) p = Polynomial.C ((16 : ℚ) ^ m) * p := by
    have hmw := macwilliams_identity_ring (R := Polynomial ℚ) C C hSD (1 : Polynomial ℚ) Polynomial.X
    obtain ⟨_, _, hcard⟩ := selfDual_finrank_and_card C hSD
    have hcard_eq : (SC.card : Polynomial ℚ) = Polynomial.C ((16 : ℚ) ^ m) := by
      change ((Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C)).card : Polynomial ℚ) = _
      rw [hcard, show (8 * m) / 2 = 4 * m by omega, ← Polynomial.C_eq_natCast]
      congr 1
      push_cast
      rw [pow_mul]
      norm_num
    have hL : ((SC.card : Polynomial ℚ) *
        ∑ y ∈ SC, (1 : Polynomial ℚ) ^ (8 * m - wt y) * Polynomial.X ^ (wt y)) =
        Polynomial.C ((16 : ℚ) ^ m) * p := by
      rw [hcard_eq]
      congr 1
      refine Finset.sum_congr rfl fun y _ => by simp
    have hR : mwTransform (8 * m) p =
        ∑ x ∈ SC, (1 + Polynomial.X : Polynomial ℚ) ^ (8 * m - wt x) *
          (1 - Polynomial.X : Polynomial ℚ) ^ (wt x) := by
      rw [show p = ∑ x ∈ SC, Polynomial.C 1 * Polynomial.X ^ (wt x) by simp [p],
        mwTransform_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mwTransform_C_mul_X_pow (8 * m) (wt x) (wt_le x) 1]
      simp
    rw [hR, ← hL]
    exact hmw.symm
  obtain ⟨a, ha⟩ := gleason_poly_decomp m p hp_deg hp_4 hp_mw
  refine ⟨a, ?_⟩
  rw [← phi8_eq, ← delta24_eq]
  exact ha

/-! #### Mallows–Sloane Upper Bound `d ≤ 4 ⌊n / 24⌋ + 4` via Pure-Polynomial Residue Identity -/

private lemma coeff_X_mul_deriv_sub (L : ℕ) (V : Polynomial ℚ) :
    (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V).coeff L = 0 := by
  cases L with
  | zero =>
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Nat.cast_zero, zero_mul, sub_zero,
      Polynomial.coeff_zero_eq_eval_zero]
    simp
  | succ k =>
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative]
    push_cast
    ring

private lemma X_pow_dvd_of_coeff_zero {r : ℕ} {f : Polynomial ℚ}
    (hf : ∀ j, j < r → f.coeff j = 0) :
    Polynomial.X ^ r ∣ f := by
  rw [Polynomial.X_pow_dvd_iff]
  exact hf

private lemma coeff_eq_zero_of_X_pow_dvd {r j : ℕ} {f : Polynomial ℚ}
    (hdvd : Polynomial.X ^ r ∣ f) (hj : j < r) :
    f.coeff j = 0 :=
  (Polynomial.X_pow_dvd_iff.mp hdvd) j hj

private lemma geom_poly_mul_one_sub (r : ℕ) :
    (∑ j ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ j) * (1 - Polynomial.X) =
      1 - Polynomial.X ^ r := by
  induction r with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

private lemma X_pow_dvd_geom_pow_mul_one_sub_pow_sub_one (r M : ℕ) :
    Polynomial.X ^ r ∣
      (∑ j ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ j) ^ M *
        (1 - Polynomial.X) ^ M - 1 := by
  rw [← mul_pow, geom_poly_mul_one_sub]
  induction M with
  | zero => simp
  | succ k ih =>
    have hsplit : (1 - Polynomial.X ^ r : Polynomial ℚ) ^ (k + 1) - 1 =
        ((1 - Polynomial.X ^ r) ^ k - 1) * (1 - Polynomial.X ^ r) - Polynomial.X ^ r := by
      rw [pow_succ]; ring
    rw [hsplit]
    exact dvd_sub (dvd_mul_of_dvd_left ih _) (dvd_refl _)

private lemma geom_pow_coeff_nonneg (r M j : ℕ) :
    0 ≤ ((∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i) ^ M).coeff j := by
  induction M generalizing j with
  | zero =>
    rw [pow_zero, Polynomial.coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Polynomial.coeff_mul]
    refine Finset.sum_nonneg fun ab _ => mul_nonneg (ih ab.1) ?_
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Polynomial.coeff_X_pow]
    split_ifs <;> norm_num

private lemma geom_pow_coeff_ge_one (r M : ℕ) (hM : 1 ≤ M) (j : ℕ) (hj : j < r) :
    1 ≤ ((∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i) ^ M).coeff j := by
  induction M with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      rw [pow_one, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_X_pow, if_pos rfl]
      · intro b _ hb; rw [Polynomial.coeff_X_pow, if_neg hb.symm]
      · intro hj'; exact absurd (Finset.mem_range.mpr hj) hj'
    | succ k' =>
      rw [pow_succ, Polynomial.coeff_mul]
      have hmem : (j, 0) ∈ Finset.antidiagonal j := Finset.mem_antidiagonal.mpr (add_zero j)
      have hterm : 1 ≤
          ((∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i) ^ (k' + 1)).coeff j *
          (∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i).coeff 0 := by
        have h1 := ih (by omega)
        have h0 : (∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i).coeff 0 = 1 := by
          rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; rw [Polynomial.coeff_X_pow, if_neg (Ne.symm hb)]
          · intro h0'; exact absurd (Finset.mem_range.mpr (by omega)) h0'
        rw [h0, mul_one]; exact h1
      calc
        (1 : ℚ) ≤ _ := hterm
        _ ≤ ∑ ab ∈ Finset.antidiagonal j,
              ((∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i) ^ (k' + 1)).coeff ab.1 *
              (∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i).coeff ab.2 := by
            refine Finset.single_le_sum (f := fun ab : ℕ × ℕ =>
              ((∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i) ^ (k' + 1)).coeff ab.1 *
              (∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℚ) ^ i).coeff ab.2) ?_ hmem
            intro ab _
            refine mul_nonneg (geom_pow_coeff_nonneg r (k' + 1) ab.1) ?_
            simpa using geom_pow_coeff_nonneg r 1 ab.2

private lemma poly_nonneg_mul {f g : Polynomial ℚ}
    (hf : ∀ j, 0 ≤ f.coeff j) (hg : ∀ j, 0 ≤ g.coeff j) :
    ∀ j, 0 ≤ (f * g).coeff j := by
  intro j
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun ab _ => mul_nonneg (hf ab.1) (hg ab.2)

private lemma poly_nonneg_pow {f : Polynomial ℚ} (hf : ∀ j, 0 ≤ f.coeff j) (e : ℕ) :
    ∀ j, 0 ≤ (f ^ e).coeff j := by
  induction e with
  | zero =>
    intro j; rw [pow_zero, Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]; exact poly_nonneg_mul ih hf

private lemma mallows_sloane_core {m : ℕ} (hm : 1 ≤ m)
    (a : Fin (m / 3 + 1) → ℚ)
    (g : Polynomial ℚ)
    (hg_eq : g = ∑ k : Fin (m / 3 + 1),
      Polynomial.C (a k) * phi8U ^ (m - 3 * k.val) * delta24U ^ k.val)
    (hg0 : g.coeff 0 = 1)
    (hg_vanish : ∀ j, 1 ≤ j → j ≤ m / 3 + 1 → g.coeff j = 0) : False := by
  let r : ℕ := m / 3 + 1
  have hr_pos : 1 ≤ r := by omega
  let e : ℕ := 3 * r - m - 1
  have he_eq : m + e + 1 = 3 * r := by omega
  let P : Polynomial ℚ := phi8U
  let R : Polynomial ℚ := (1 - Polynomial.X) ^ 4
  let S1 : Polynomial ℚ := ∑ i ∈ Finset.range r, Polynomial.X ^ i
  let S : Polynomial ℚ := S1 ^ (4 * r)
  let D : Polynomial ℚ := (Polynomial.derivative g * P - Polynomial.C (m : ℚ) * g * Polynomial.derivative P) * P ^ e
  -- Step 1: From g - 1 divisible by X^(r+1), show (D * S).coeff (r - 1) < 0
  have hXg_sub : Polynomial.X ^ (r + 1) ∣ (g - 1) := by
    apply X_pow_dvd_of_coeff_zero
    intro j hj
    rw [Polynomial.coeff_sub, Polynomial.coeff_one]
    by_cases hj0 : j = 0
    · subst hj0; simp [hg0]
    · rw [if_neg hj0, sub_zero]
      exact hg_vanish j (by omega) (by omega)
  have hD_neg : (D * S).coeff (r - 1) < 0 := by
    rcases hXg_sub with ⟨Q, hQ⟩
    have hg_form : g = 1 + Polynomial.X ^ (r + 1) * Q := by linear_combination hQ
    have hderiv_g : Polynomial.derivative g =
        Polynomial.X ^ r * (Polynomial.C ((r + 1 : ℕ) : ℚ) * Q + Polynomial.X * Polynomial.derivative Q) := by
      rw [hg_form, map_add, Polynomial.derivative_one, zero_add, Polynomial.derivative_mul,
        Polynomial.derivative_X_pow, Nat.add_sub_cancel]
      have hpow : (Polynomial.X : Polynomial ℚ) ^ (r + 1) = Polynomial.X ^ r * Polynomial.X :=
        pow_succ _ _
      rw [hpow]
      ring
    have hXr_dvd : Polynomial.X ^ r ∣ (D * S + Polynomial.C (m : ℚ) * Polynomial.derivative P * P ^ e * S) := by
      have hdiff : D + Polynomial.C (m : ℚ) * Polynomial.derivative P * P ^ e =
          Polynomial.X ^ r * ((Polynomial.C ((r + 1 : ℕ) : ℚ) * Q + Polynomial.X * Polynomial.derivative Q) *
            P ^ (e + 1) - Polynomial.C (m : ℚ) * Polynomial.X * Q * Polynomial.derivative P * P ^ e) := by
        simp only [D]
        rw [hderiv_g, hg_form, pow_succ]
        ring
      refine ⟨((Polynomial.C ((r + 1 : ℕ) : ℚ) * Q + Polynomial.X * Polynomial.derivative Q) *
        P ^ (e + 1) - Polynomial.C (m : ℚ) * Polynomial.X * Q * Polynomial.derivative P * P ^ e) * S, ?_⟩
      linear_combination hdiff * S
    have hcoeff0 := coeff_eq_zero_of_X_pow_dvd hXr_dvd (j := r - 1) (by omega)
    rw [Polynomial.coeff_add] at hcoeff0
    -- Show (C m * P' * P^e * S).coeff (r - 1) > 0
    have hP'_eq : Polynomial.derivative P = 14 + 2 * Polynomial.X := by
      simp only [P, phi8U, map_add, Polynomial.derivative_one, zero_add,
        Polynomial.derivative_X_pow]
      have h14x : Polynomial.derivative (14 * Polynomial.X : Polynomial ℚ) = 14 := by
        rw [show (14 : Polynomial ℚ) = Polynomial.C 14 from (map_ofNat Polynomial.C 14).symm,
          Polynomial.derivative_C_mul, Polynomial.derivative_X, mul_one, map_ofNat]
      rw [h14x]
      simp only [Nat.cast_ofNat, map_ofNat]
      ring
    have hP'_nn : ∀ j, 0 ≤ (Polynomial.derivative P).coeff j := by
      intro j
      rw [hP'_eq]
      have h14 : (14 : Polynomial ℚ) = Polynomial.C 14 := rfl
      have h2 : (2 : Polynomial ℚ) = Polynomial.C 2 := rfl
      rw [Polynomial.coeff_add, h14, Polynomial.coeff_C, h2, Polynomial.coeff_C_mul,
        Polynomial.coeff_X]
      split_ifs <;> norm_num
    have hP_nn : ∀ j, 0 ≤ P.coeff j := by
      intro j
      simp only [P, phi8U, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      have h14 : (14 * Polynomial.X : Polynomial ℚ) = Polynomial.C 14 * Polynomial.X := rfl
      rw [h14, Polynomial.coeff_C_mul, Polynomial.coeff_X]
      split_ifs <;> norm_num
    have hPe_nn : ∀ j, 0 ≤ (P ^ e).coeff j := poly_nonneg_pow hP_nn e
    have hProd_nn : ∀ j, 0 ≤ (Polynomial.derivative P * P ^ e).coeff j :=
      poly_nonneg_mul hP'_nn hPe_nn
    have hProd_0 : (Polynomial.derivative P * P ^ e).coeff 0 = 14 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, hP'_eq, Polynomial.eval_pow]
      simp [P, phi8U]
    have hS_pos : 1 ≤ S.coeff (r - 1) := geom_pow_coeff_ge_one r (4 * r) (by omega) (r - 1) (by omega)
    have hpos : 0 < (Polynomial.C (m : ℚ) * Polynomial.derivative P * P ^ e * S).coeff (r - 1) := by
      rw [mul_assoc (Polynomial.C (m : ℚ)), mul_assoc (Polynomial.C (m : ℚ)),
        Polynomial.coeff_C_mul]
      have hm_pos : (0 : ℚ) < (m : ℚ) := Nat.cast_pos.mpr (by omega)
      refine mul_pos hm_pos ?_
      rw [Polynomial.coeff_mul]
      have hmem : (0, r - 1) ∈ Finset.antidiagonal (r - 1) := Finset.mem_antidiagonal.mpr (zero_add _)
      have hterm : (0 : ℚ) < (Polynomial.derivative P * P ^ e).coeff 0 * S.coeff (r - 1) := by
        rw [hProd_0]; linarith
      calc
        (0 : ℚ) < _ := hterm
        _ ≤ ∑ ab ∈ Finset.antidiagonal (r - 1),
              (Polynomial.derivative P * P ^ e).coeff ab.1 * S.coeff ab.2 := by
            refine Finset.single_le_sum (f := fun ab : ℕ × ℕ =>
              (Polynomial.derivative P * P ^ e).coeff ab.1 * S.coeff ab.2) ?_ hmem
            intro ab _
            exact mul_nonneg (hProd_nn ab.1) (geom_pow_coeff_nonneg r (4 * r) ab.2)
    linarith
  -- Step 2: Show (D * S).coeff (r - 1) = 0 term-by-term from the Gleason expansion of g!
  have hD_zero : (D * S).coeff (r - 1) = 0 := by
    have hD_sum : D = ∑ k : Fin (m / 3 + 1),
        Polynomial.C (a k) *
          (Polynomial.derivative (P ^ (m - 3 * k.val) * delta24U ^ k.val) * P -
           Polynomial.C (m : ℚ) * (P ^ (m - 3 * k.val) * delta24U ^ k.val) * Polynomial.derivative P) *
          P ^ e := by
      simp only [D, hg_eq, map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, Polynomial.derivative_C_mul]
      ring
    rw [hD_sum, Finset.sum_mul, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun k _ => ?_
    -- For k = 0, the derivative term vanishes identically!
    by_cases hk0 : k.val = 0
    · have hterm0 :
          (Polynomial.derivative (P ^ (m - 3 * k.val) * delta24U ^ k.val) * P -
           Polynomial.C (m : ℚ) * (P ^ (m - 3 * k.val) * delta24U ^ k.val) * Polynomial.derivative P) = 0 := by
        rw [hk0, mul_zero, Nat.sub_zero, pow_zero, mul_one, Polynomial.derivative_pow]
        cases m with
        | zero => omega
        | succ m' =>
          have hpow : P ^ (m' + 1) = P ^ m' * P := pow_succ _ _
          rw [hpow]; push_cast; ring
      rw [hterm0, mul_zero, zero_mul, zero_mul, Polynomial.coeff_zero]
    · -- For 1 ≤ k < r, let L = r - k ≥ 1 and use V_k = P^(3L) * S1^(4L)
      set L : ℕ := r - k.val
      have hL_pos : 1 ≤ L := by omega
      have hk_pos : 1 ≤ k.val := by omega
      have h3L : m - 3 * k.val + e = 3 * L - 1 := by omega
      -- Express the k-th term using (X * R) = delta24U
      have hdk :
          (Polynomial.derivative (P ^ (m - 3 * k.val) * delta24U ^ k.val) * P -
           Polynomial.C (m : ℚ) * (P ^ (m - 3 * k.val) * delta24U ^ k.val) * Polynomial.derivative P) * P ^ e =
          Polynomial.C (k.val : ℚ) * P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
            (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_pow]
        have hPsplit : P ^ (m - 3 * k.val) * P ^ e = P ^ (3 * L - 1) := by
          rw [← pow_add, h3L]
        have hDsplit : delta24U ^ k.val = delta24U ^ (k.val - 1) * delta24U := by
          rw [← pow_succ, Nat.sub_add_cancel hk_pos]
        -- Handle both m - 3*k = 0 and m - 3*k > 0 cleanly
        have hcast : ((m - 3 * k.val : ℕ) : ℚ) - (m : ℚ) = -3 * (k.val : ℚ) := by
          have hle : 3 * k.val ≤ m := by omega
          rw [Nat.cast_sub hle]; push_cast; ring
        by_cases hmz : m - 3 * k.val = 0
        · have hmQ : (m : ℚ) = 3 * (k.val : ℚ) := by
            have hm3k : m = 3 * k.val := by omega
            exact_mod_cast hm3k
          have hmC : Polynomial.C (m : ℚ) = 3 * Polynomial.C (k.val : ℚ) := by
            rw [hmQ, map_mul, map_ofNat]
          rw [hmz, pow_zero, one_mul, Nat.cast_zero, map_zero, zero_mul, zero_mul, zero_mul,
            zero_add, hDsplit, show e = 3 * L - 1 by omega, hmC]
          ring
        · have hP1 : P ^ (m - 3 * k.val) = P ^ (m - 3 * k.val - 1) * P := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          have hcore :
              (Polynomial.C ((m - 3 * k.val : ℕ) : ℚ) * P ^ (m - 3 * k.val - 1) *
                  Polynomial.derivative P * delta24U ^ k.val +
                P ^ (m - 3 * k.val) * (Polynomial.C (k.val : ℚ) * delta24U ^ (k.val - 1) *
                  Polynomial.derivative delta24U)) * P -
                Polynomial.C (m : ℚ) * (P ^ (m - 3 * k.val) * delta24U ^ k.val) *
                  Polynomial.derivative P =
              Polynomial.C (k.val : ℚ) * P ^ (m - 3 * k.val) * delta24U ^ (k.val - 1) *
                (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) := by
            have hstep1 :
                (Polynomial.C ((m - 3 * k.val : ℕ) : ℚ) * P ^ (m - 3 * k.val - 1) *
                    Polynomial.derivative P * delta24U ^ k.val +
                  P ^ (m - 3 * k.val) * (Polynomial.C (k.val : ℚ) * delta24U ^ (k.val - 1) *
                    Polynomial.derivative delta24U)) * P -
                  Polynomial.C (m : ℚ) * (P ^ (m - 3 * k.val) * delta24U ^ k.val) *
                    Polynomial.derivative P =
                Polynomial.C (((m - 3 * k.val : ℕ) : ℚ) - (m : ℚ)) *
                  P ^ (m - 3 * k.val) * Polynomial.derivative P * delta24U ^ k.val +
                Polynomial.C (k.val : ℚ) * P ^ (m - 3 * k.val) * P *
                  delta24U ^ (k.val - 1) * Polynomial.derivative delta24U := by
              rw [map_sub]
              linear_combination -Polynomial.C ((m - 3 * k.val : ℕ) : ℚ) *
                Polynomial.derivative P * delta24U ^ k.val * hP1
            rw [hstep1, hcast, hDsplit]
            simp only [map_mul, map_neg, map_ofNat]
            ring
          rw [hcore]
          linear_combination Polynomial.C (k.val : ℚ) * delta24U ^ (k.val - 1) *
            (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * hPsplit
      -- Wait: simplify using `hdk_clean` right below instead of calc!
      -- Now use V = P^(3*L) * S1^(4*L) and V * R^L = P^(3*L) + X^r * E
      let V : Polynomial ℚ := P ^ (3 * L) * S1 ^ (4 * L)
      have hVR_dvd : Polynomial.X ^ r ∣ (V * R ^ L - P ^ (3 * L)) := by
        have h1 : V * R ^ L - P ^ (3 * L) = P ^ (3 * L) * (S1 ^ (4 * L) * (1 - Polynomial.X) ^ (4 * L) - 1) := by
          simp only [V, R]; rw [← pow_mul]; ring
        rw [h1]
        exact dvd_mul_of_dvd_right (X_pow_dvd_geom_pow_mul_one_sub_pow_sub_one r (4 * L)) _
      rcases hVR_dvd with ⟨E, hE⟩
      have hVR : V * R ^ L = P ^ (3 * L) + Polynomial.X ^ r * E := by linear_combination hE
      -- Differentiate hVR
      have hVR_d := congrArg Polynomial.derivative hVR
      simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, map_add] at hVR_d
      -- Combine X * R * hVR_d - L * (X * R)' * hVR to cancel R'!
      have hderiv_delta : Polynomial.derivative delta24U = R + Polynomial.X * Polynomial.derivative R := by
        simp only [delta24U, R, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
      have hP3L : P ^ (3 * L) = P ^ (3 * L - 1) * P := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have hRL : R ^ L = R ^ (L - 1) * R := by
        rw [← pow_succ, Nat.sub_add_cancel hL_pos]
      have hXr_cancel : Polynomial.X ^ r ∣
          ((Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V) * R ^ (L + 1) +
           Polynomial.C (L : ℚ) * P ^ (3 * L - 1) *
             (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U)) := by
        have hXr_pow : (Polynomial.X : Polynomial ℚ) * Polynomial.X ^ (r - 1) = Polynomial.X ^ r := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hr_pos]
        refine ⟨R * (Polynomial.C (r : ℚ) * E + Polynomial.X * Polynomial.derivative E) -
          Polynomial.C (L : ℚ) * Polynomial.derivative delta24U * E, ?_⟩
        have h3Lcast : Polynomial.C ((3 * L : ℕ) : ℚ) = 3 * Polynomial.C (L : ℚ) := by
          push_cast; simp only [map_mul, map_ofNat]
        rw [h3Lcast, Polynomial.derivative_X, mul_one] at hVR_d
        have hkey := congrArg (fun t => Polynomial.X * R * t) hVR_d
        have hkey2 := congrArg (fun t => Polynomial.C (L : ℚ) * Polynomial.derivative delta24U * t) hVR
        have hsub := congrArg₂ (· - ·) hkey hkey2
        rw [hderiv_delta] at hsub ⊢
        rw [delta24U, pow_succ R L]
        have hRL' : R ^ (L - 1) * R = R ^ L := hRL.symm
        linear_combination hsub -
          Polynomial.C (L : ℚ) * Polynomial.X * V * Polynomial.derivative R * hRL' -
          Polynomial.C (L : ℚ) * (R + Polynomial.X * Polynomial.derivative R) * hP3L +
          Polynomial.C (r : ℚ) * R * E * hXr_pow
      -- Multiply by delta24U^(k-1) / R^(k-1) ... i.e. by X^(k-1) * R^(k-1) * S
      have hRS_dvd : Polynomial.X ^ r ∣ (R ^ r * S - 1) := by
        have h1 : R ^ r * S - 1 = S1 ^ (4 * r) * (1 - Polynomial.X) ^ (4 * r) - 1 := by
          simp only [R, S]; rw [← pow_mul]; ring
        rw [h1]
        exact X_pow_dvd_geom_pow_mul_one_sub_pow_sub_one r (4 * r)
      have hcomb_dvd : Polynomial.X ^ r ∣
          (Polynomial.X ^ (k.val - 1) * (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V) +
           Polynomial.C (L : ℚ) * P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
             (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S) := by
        have h1 := dvd_mul_of_dvd_left hXr_cancel (Polynomial.X ^ (k.val - 1) * R ^ (k.val - 1) * S)
        have h2 := dvd_mul_of_dvd_left hRS_dvd
          (Polynomial.X ^ (k.val - 1) * (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V))
        have hRpow : R ^ (L + 1) * R ^ (k.val - 1) = R ^ r := by
          rw [← pow_add, show L + 1 + (k.val - 1) = r by omega]
        have hDpow : Polynomial.X ^ (k.val - 1) * R ^ (k.val - 1) = delta24U ^ (k.val - 1) := by
          rw [← mul_pow]; rfl
        have hdiff := dvd_sub h1 h2
        have hident :
            ((Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V) * R ^ (L + 1) +
              Polynomial.C (L : ℚ) * P ^ (3 * L - 1) *
                (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U)) *
              (Polynomial.X ^ (k.val - 1) * R ^ (k.val - 1) * S) -
            (R ^ r * S - 1) *
              (Polynomial.X ^ (k.val - 1) * (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V)) =
            Polynomial.X ^ (k.val - 1) * (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V) +
            Polynomial.C (L : ℚ) * P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
              (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S := by
          linear_combination
            (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V) *
              Polynomial.X ^ (k.val - 1) * S * hRpow +
            Polynomial.C (L : ℚ) * P ^ (3 * L - 1) *
              (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S * hDpow
        rw [← hident]
        exact hdiff
      have hc0 := coeff_eq_zero_of_X_pow_dvd hcomb_dvd (j := r - 1) (by omega)
      rw [Polynomial.coeff_add] at hc0
      have hfirst0 : (Polynomial.X ^ (k.val - 1) *
          (Polynomial.X * Polynomial.derivative V - Polynomial.C (L : ℚ) * V)).coeff (r - 1) = 0 := by
        rw [show r - 1 = L + (k.val - 1) by omega, mul_comm, Polynomial.coeff_mul_X_pow]
        exact coeff_X_mul_deriv_sub L V
      have hc0_factor :
          Polynomial.C (L : ℚ) * P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
            (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S =
          Polynomial.C (L : ℚ) * (P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
            (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S) := by
        ring
      rw [hfirst0, zero_add, hc0_factor, Polynomial.coeff_C_mul] at hc0
      have hLne : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hmain0 : (P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
          (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S).coeff (r - 1) = 0 :=
        (mul_eq_zero.mp hc0).resolve_left hLne
      have hrew :
          Polynomial.C (a k) *
            (Polynomial.derivative (P ^ (m - 3 * k.val) * delta24U ^ k.val) * P -
             Polynomial.C (m : ℚ) * (P ^ (m - 3 * k.val) * delta24U ^ k.val) * Polynomial.derivative P) *
            P ^ e * S =
          Polynomial.C (a k * (k.val : ℚ)) *
            (P ^ (3 * L - 1) * delta24U ^ (k.val - 1) *
              (P * Polynomial.derivative delta24U - 3 * Polynomial.derivative P * delta24U) * S) := by
        rw [Polynomial.C_mul]
        linear_combination Polynomial.C (a k) * S * hdk
      rw [hrew, Polynomial.coeff_C_mul, hmain0, mul_zero]
  linarith

/-- **Theorem 4.2 (Mallows–Sloane Upper Bound (1973) `d ≤ 4 ⌊n / 24⌋ + 4`):**
Every Type II (doubly-even) self-dual binary linear code `C` of positive length `n > 0`
contains a nonzero codeword of Hamming weight at most `4 * (n / 24) + 4`.
In particular, at `n = 72`, every Type II self-dual code has minimum distance `d ≤ 16`. -/
theorem mallows_sloane_bound {n : ℕ} (hn : 0 < n)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card) :
    ∃ x ∈ C, x ≠ 0 ∧
      (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card ≤ 4 * (n / 24) + 4 := by
  obtain ⟨m, rfl⟩ := gleason_pierce_eight_dvd_length C hSD hT2
  have hm : 1 ≤ m := by omega
  by_contra hno
  push Not at hno
  obtain ⟨a, ha⟩ := gleason_theorem_typeII C hSD hT2
  let SC := Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C)
  let p : Polynomial ℚ := ∑ x ∈ SC, Polynomial.X ^ (wt x)
  let g : Polynomial ℚ := ∑ k : Fin (m / 3 + 1),
    Polynomial.C (a k) * phi8U ^ (m - 3 * k.val) * delta24U ^ k.val
  have hp_eq : p = g.comp (Polynomial.X ^ 4) := by
    have hg_comp : g.comp (Polynomial.X ^ 4) =
        ∑ k : Fin (m / 3 + 1),
          Polynomial.C (a k) * phi8 ^ (m - 3 * k.val) * delta24 ^ k.val := by
      have hsum_comp : ∀ (s : Finset (Fin (m / 3 + 1))) (f : Fin (m / 3 + 1) → Polynomial ℚ),
          (∑ k ∈ s, f k).comp (Polynomial.X ^ 4) = ∑ k ∈ s, (f k).comp (Polynomial.X ^ 4) := by
        intro s f
        induction s using Finset.cons_induction with
        | empty => simp
        | cons x s hx ih => rw [Finset.sum_cons, Finset.sum_cons, Polynomial.add_comp, ih]
      rw [show g = ∑ k : Fin (m / 3 + 1),
        Polynomial.C (a k) * phi8U ^ (m - 3 * k.val) * delta24U ^ k.val from rfl, hsum_comp]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp]
      rfl
    rw [hg_comp]
    simpa [p, SC, wt, phi8_eq, delta24_eq] using ha
  have hp_coeff : ∀ w : ℕ, p.coeff w =
      ((Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C ∧ wt x = w)).card : ℚ) := by
    intro w
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ C
    · by_cases hw : wt x = w
      · simp [hx, hw]
      · simp [hx, hw, Ne.symm hw]
    · simp [hx]
  have hg_coeff : ∀ j : ℕ, g.coeff j = p.coeff (4 * j) := by
    intro j
    rw [hp_eq, coeff_comp_X_pow_four, if_pos (dvd_mul_right 4 j), show (4 * j) / 4 = j by omega]
  have hg0 : g.coeff 0 = 1 := by
    rw [hg_coeff 0, mul_zero, hp_coeff 0]
    have hset : Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C ∧ wt x = 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => (wt_eq_zero_iff x).mp h.2, by rintro rfl; exact ⟨C.zero_mem, wt_zero⟩⟩
    rw [hset, Finset.card_singleton, Nat.cast_one]
  have hg_vanish : ∀ j, 1 ≤ j → j ≤ m / 3 + 1 → g.coeff j = 0 := by
    intro j hj1 hj2
    rw [hg_coeff j, hp_coeff (4 * j)]
    have hempty : Finset.univ.filter (fun x : Fin (8 * m) → ZMod 2 => x ∈ C ∧ wt x = 4 * j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      have hne : x ≠ 0 := by intro h0; rw [h0, wt_zero] at hx; omega
      have hgt := hno x hx.1 hne
      change 4 * ((8 * m) / 24) + 4 < wt x at hgt
      have hdiv : (8 * m) / 24 = m / 3 := by omega
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  exact mallows_sloane_core hm a g rfl hg0 hg_vanish

/-- **Corollary 4.3 (Mallows–Sloane Extremality Threshold at `n = 72`):**
Every Type II self-dual binary linear code of length `72` has minimum distance `d ≤ 16`. -/
theorem mallows_sloane_72
    (C : Submodule (ZMod 2) (Fin 72 → ZMod 2))
    (hSD : ∀ y : Fin 72 → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin 72, x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card) :
    ∃ x ∈ C, x ≠ 0 ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card ≤ 16 := by
  simpa using mallows_sloane_bound (by omega : 0 < 72) C hSD hT2

/-! #### Forced Unique Weight Enumerator of ANY `[72, 36, 16]` Type II Self-Dual Code -/

private noncomputable def extremal72PolyU : Polynomial ℚ :=
  1 + 249849 * Polynomial.X ^ 4 + 18106704 * Polynomial.X ^ 5 +
  462962955 * Polynomial.X ^ 6 + 4397342400 * Polynomial.X ^ 7 +
  16602715899 * Polynomial.X ^ 8 + 25756721120 * Polynomial.X ^ 9 +
  16602715899 * Polynomial.X ^ 10 + 4397342400 * Polynomial.X ^ 11 +
  462962955 * Polynomial.X ^ 12 + 18106704 * Polynomial.X ^ 13 +
  249849 * Polynomial.X ^ 14 + Polynomial.X ^ 18

private lemma extremal72PolyU_eq_gleason :
    phi8U ^ 9 - 126 * phi8U ^ 6 * delta24U + 3015 * phi8U ^ 3 * delta24U ^ 2 -
      4398 * delta24U ^ 3 = extremal72PolyU := by
  simp only [phi8U, delta24U, extremal72PolyU]
  ring

private lemma gleason72_coeffs_unique (a0 a1 a2 a3 : ℚ)
    (h : let g : Polynomial ℚ :=
        Polynomial.C a0 * phi8U ^ 9 + Polynomial.C a1 * phi8U ^ 6 * delta24U +
        Polynomial.C a2 * phi8U ^ 3 * delta24U ^ 2 + Polynomial.C a3 * delta24U ^ 3
      g.coeff 0 = 1 ∧ g.coeff 1 = 0 ∧ g.coeff 2 = 0 ∧ g.coeff 3 = 0) :
    a0 = 1 ∧ a1 = -126 ∧ a2 = 3015 ∧ a3 = -4398 := by
  dsimp only at h
  rcases h with ⟨h0, h1, h2, h3⟩
  let g : Polynomial ℚ :=
    Polynomial.C a0 * phi8U ^ 9 + Polynomial.C a1 * phi8U ^ 6 * delta24U +
    Polynomial.C a2 * phi8U ^ 3 * delta24U ^ 2 + Polynomial.C a3 * delta24U ^ 3
  let d : Polynomial ℚ := g - extremal72PolyU
  have hd_form : d =
      Polynomial.C (a0 - 1) * phi8U ^ 9 +
      Polynomial.C (a1 + 126) * phi8U ^ 6 * delta24U +
      Polynomial.C (a2 - 3015) * phi8U ^ 3 * delta24U ^ 2 +
      Polynomial.C (a3 + 4398) * delta24U ^ 3 := by
    simp only [d, g, ← extremal72PolyU_eq_gleason, map_sub, map_add, map_one, map_ofNat]
    ring
  have hext_coeff : extremal72PolyU.coeff 0 = 1 ∧ extremal72PolyU.coeff 1 = 0 ∧
      extremal72PolyU.coeff 2 = 0 ∧ extremal72PolyU.coeff 3 = 0 := by
    have hsplit : extremal72PolyU = 1 + Polynomial.X ^ 4 *
        (249849 + 18106704 * Polynomial.X + 462962955 * Polynomial.X ^ 2 +
         4397342400 * Polynomial.X ^ 3 + 16602715899 * Polynomial.X ^ 4 +
         25756721120 * Polynomial.X ^ 5 + 16602715899 * Polynomial.X ^ 6 +
         4397342400 * Polynomial.X ^ 7 + 462962955 * Polynomial.X ^ 8 +
         18106704 * Polynomial.X ^ 9 + 249849 * Polynomial.X ^ 10 + Polynomial.X ^ 14) := by
      simp only [extremal72PolyU]; ring
    rw [hsplit]
    have hX4 : ∀ j, j < 4 → (Polynomial.X ^ 4 *
        (249849 + 18106704 * Polynomial.X + 462962955 * Polynomial.X ^ 2 +
         4397342400 * Polynomial.X ^ 3 + 16602715899 * Polynomial.X ^ 4 +
         25756721120 * Polynomial.X ^ 5 + 16602715899 * Polynomial.X ^ 6 +
         4397342400 * Polynomial.X ^ 7 + 462962955 * Polynomial.X ^ 8 +
         18106704 * Polynomial.X ^ 9 + 249849 * Polynomial.X ^ 10 + Polynomial.X ^ 14 : Polynomial ℚ)).coeff j = 0 :=
      fun j hj => coeff_eq_zero_of_X_pow_dvd (dvd_mul_right _ _) hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, hX4 0 (by omega), add_zero]
    · rw [Polynomial.coeff_add, Polynomial.coeff_one, if_neg (by omega), hX4 1 (by omega), add_zero]
    · rw [Polynomial.coeff_add, Polynomial.coeff_one, if_neg (by omega), hX4 2 (by omega), add_zero]
    · rw [Polynomial.coeff_add, Polynomial.coeff_one, if_neg (by omega), hX4 3 (by omega), add_zero]
  have hd0 : d.coeff 0 = 0 := by rw [Polynomial.coeff_sub, h0, hext_coeff.1, sub_self]
  have hd1 : d.coeff 1 = 0 := by rw [Polynomial.coeff_sub, h1, hext_coeff.2.1, sub_self]
  have hd2 : d.coeff 2 = 0 := by rw [Polynomial.coeff_sub, h2, hext_coeff.2.2.1, sub_self]
  have hd3 : d.coeff 3 = 0 := by rw [Polynomial.coeff_sub, h3, hext_coeff.2.2.2, sub_self]
  have hX_dvd_d : ∀ k : ℕ, Polynomial.X ^ k ∣ delta24U ^ k := fun k => by
    rw [delta24U, mul_pow]; exact dvd_mul_right _ _
  have hX1_dvd : Polynomial.X ^ 1 ∣ delta24U := by
    rw [← pow_one delta24U]; exact hX_dvd_d 1
  -- Step 1: a0 = 1 from coeff 0
  have ha0 : a0 = 1 := by
    rw [hd_form] at hd0
    simp only [Polynomial.coeff_add] at hd0
    have hphi0 : (Polynomial.C (a0 - 1) * phi8U ^ 9).coeff 0 = a0 - 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]; simp [phi8U]
    have ht1 : (Polynomial.C (a1 + 126) * phi8U ^ 6 * delta24U).coeff 0 = 0 :=
      coeff_eq_zero_of_X_pow_dvd (dvd_mul_of_dvd_right hX1_dvd _) (by omega)
    have ht2 : (Polynomial.C (a2 - 3015) * phi8U ^ 3 * delta24U ^ 2).coeff 0 = 0 :=
      coeff_eq_zero_of_X_pow_dvd (dvd_mul_of_dvd_right (hX_dvd_d 2) _) (by omega)
    have ht3 : (Polynomial.C (a3 + 4398) * delta24U ^ 3).coeff 0 = 0 :=
      coeff_eq_zero_of_X_pow_dvd (dvd_mul_of_dvd_right (hX_dvd_d 3) _) (by omega)
    rw [hphi0, ht1, ht2, ht3] at hd0
    linarith
  -- Step 2: a1 = -126 from coeff 1
  have ha1 : a1 = -126 := by
    rw [hd_form, ha0, sub_self, map_zero, zero_mul, zero_add] at hd1
    simp only [Polynomial.coeff_add] at hd1
    have ht1 : (Polynomial.C (a1 + 126) * phi8U ^ 6 * delta24U).coeff 1 = a1 + 126 := by
      have hrew : Polynomial.C (a1 + 126) * phi8U ^ 6 * delta24U =
          (Polynomial.C (a1 + 126) * phi8U ^ 6 * (1 - Polynomial.X) ^ 4) * Polynomial.X := by
        rw [delta24U]; ring
      rw [hrew, Polynomial.coeff_mul_X, Polynomial.coeff_zero_eq_eval_zero]
      simp [phi8U]
    have ht2 : (Polynomial.C (a2 - 3015) * phi8U ^ 3 * delta24U ^ 2).coeff 1 = 0 :=
      coeff_eq_zero_of_X_pow_dvd (dvd_mul_of_dvd_right (hX_dvd_d 2) _) (by omega)
    have ht3 : (Polynomial.C (a3 + 4398) * delta24U ^ 3).coeff 1 = 0 :=
      coeff_eq_zero_of_X_pow_dvd (dvd_mul_of_dvd_right (hX_dvd_d 3) _) (by omega)
    rw [ht1, ht2, ht3] at hd1
    linarith
  -- Step 3: a2 = 3015 from coeff 2
  have ha2 : a2 = 3015 := by
    rw [hd_form, ha0, ha1] at hd2
    simp only [sub_self, neg_add_cancel, map_zero, zero_mul, zero_add] at hd2
    simp only [Polynomial.coeff_add] at hd2
    have ht2 : (Polynomial.C (a2 - 3015) * phi8U ^ 3 * delta24U ^ 2).coeff 2 = a2 - 3015 := by
      have hrew : Polynomial.C (a2 - 3015) * phi8U ^ 3 * delta24U ^ 2 =
          (Polynomial.C (a2 - 3015) * phi8U ^ 3 * (1 - Polynomial.X) ^ 8) * Polynomial.X ^ 2 := by
        rw [delta24U]; ring
      rw [hrew, show (2 : ℕ) = 0 + 2 from rfl, Polynomial.coeff_mul_X_pow,
        Polynomial.coeff_zero_eq_eval_zero]
      simp [phi8U]
    have ht3 : (Polynomial.C (a3 + 4398) * delta24U ^ 3).coeff 2 = 0 :=
      coeff_eq_zero_of_X_pow_dvd (dvd_mul_of_dvd_right (hX_dvd_d 3) _) (by omega)
    rw [ht2, ht3] at hd2
    linarith
  -- Step 4: a3 = -4398 from coeff 3
  have ha3 : a3 = -4398 := by
    rw [hd_form, ha0, ha1, ha2] at hd3
    simp only [sub_self, neg_add_cancel, map_zero, zero_mul, zero_add] at hd3
    have ht3 : (Polynomial.C (a3 + 4398) * delta24U ^ 3).coeff 3 = a3 + 4398 := by
      have hrew : Polynomial.C (a3 + 4398) * delta24U ^ 3 =
          (Polynomial.C (a3 + 4398) * (1 - Polynomial.X) ^ 12) * Polynomial.X ^ 3 := by
        rw [delta24U]; ring
      rw [hrew, show (3 : ℕ) = 0 + 3 from rfl, Polynomial.coeff_mul_X_pow,
        Polynomial.coeff_zero_eq_eval_zero]
      simp
    rw [ht3] at hd3
    linarith
  exact ⟨ha0, ha1, ha2, ha3⟩

private lemma extremal72PolyU_coeff (j : ℕ) :
    extremal72PolyU.coeff j =
      match j with
      | 0 => 1
      | 4 => 249849
      | 5 => 18106704
      | 6 => 462962955
      | 7 => 4397342400
      | 8 => 16602715899
      | 9 => 25756721120
      | 10 => 16602715899
      | 11 => 4397342400
      | 12 => 462962955
      | 13 => 18106704
      | 14 => 249849
      | 18 => 1
      | _ => 0 := by
  unfold extremal72PolyU
  have h1 : (1 : Polynomial ℚ).coeff j = if j = 0 then 1 else 0 := by
    rw [Polynomial.coeff_one]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  rw [h1]
  have hmul : ∀ (n : ℕ) (k : ℕ), ((n : Polynomial ℚ) * Polynomial.X ^ k).coeff j =
      if j = k then (n : ℚ) else 0 := by
    intro n k
    rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul_X_pow]
  simp only [show (249849 : Polynomial ℚ) = ((249849 : ℕ) : Polynomial ℚ) from rfl,
    show (18106704 : Polynomial ℚ) = ((18106704 : ℕ) : Polynomial ℚ) from rfl,
    show (462962955 : Polynomial ℚ) = ((462962955 : ℕ) : Polynomial ℚ) from rfl,
    show (4397342400 : Polynomial ℚ) = ((4397342400 : ℕ) : Polynomial ℚ) from rfl,
    show (16602715899 : Polynomial ℚ) = ((16602715899 : ℕ) : Polynomial ℚ) from rfl,
    show (25756721120 : Polynomial ℚ) = ((25756721120 : ℕ) : Polynomial ℚ) from rfl, hmul]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
    j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨
    j = 17 ∨ j = 18 ∨ 19 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | hj
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hne : ∀ k ≤ 18, j ≠ k := fun k hk => by omega
    simp [hne 0 (by omega), hne 4 (by omega), hne 5 (by omega), hne 6 (by omega),
      hne 7 (by omega), hne 8 (by omega), hne 9 (by omega), hne 10 (by omega),
      hne 11 (by omega), hne 12 (by omega), hne 13 (by omega), hne 14 (by omega),
      hne 18 (by omega)]

/-- **Theorem 4.4 (Forced Unique Weight Distribution of ANY `[72, 36, 16]` Type II Code):**
If `C ≤ 𝔽₂⁷²` is ANY Type II (doubly-even) self-dual binary linear code with minimum Hamming
distance `d ≥ 16`, then its dimension is `36`, its minimum distance is **exactly** `16`, and
every single weight count `A_w(C)` is unconditionally and uniquely forced:
- `A_0 = A_{72} = 1`, `A_4 = A_8 = A_{12} = A_{60} = A_{64} = A_{68} = 0`,
- `A_{16} = A_{56} = 249849`,
- `A_{20} = A_{52} = 18106704`,
- `A_{24} = A_{48} = 462962955`,
- `A_{28} = A_{44} = 4397342400`,
- `A_{32} = A_{40} = 16602715899`,
- `A_{36} = 25756721120`,
and `A_w = 0` for every other weight `w`. -/
theorem ppl158_unique_weight_enumerator
    (C : Submodule (ZMod 2) (Fin 72 → ZMod 2))
    (hSD : ∀ y : Fin 72 → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin 72, x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card)
    (hd16 : ∀ x ∈ C, x ≠ 0 → 16 ≤ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card) :
    Module.finrank (ZMod 2) C = 36 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 0)).card = 1 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 4)).card = 0 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 8)).card = 0 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 12)).card = 0 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 16)).card = 249849 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 20)).card = 18106704 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 24)).card = 462962955 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 28)).card = 4397342400 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 32)).card = 16602715899 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 36)).card = 25756721120 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 40)).card = 16602715899 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 44)).card = 4397342400 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 48)).card = 462962955 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 52)).card = 18106704 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 56)).card = 249849 ∧
    (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
      x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 72)).card = 1 := by
  have hdim : Module.finrank (ZMod 2) C = 36 := by
    have h2 := (selfDual_finrank_and_card C hSD).1
    omega
  obtain ⟨a, ha⟩ := gleason_theorem_typeII (m := 9) C hSD hT2
  let SC := Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C)
  let p : Polynomial ℚ := ∑ x ∈ SC, Polynomial.X ^ (wt x)
  let g : Polynomial ℚ :=
    Polynomial.C (a 0) * phi8U ^ 9 +
    Polynomial.C (a 1) * phi8U ^ 6 * delta24U +
    Polynomial.C (a 2) * phi8U ^ 3 * delta24U ^ 2 +
    Polynomial.C (a 3) * delta24U ^ 3
  have hp_eq : p = g.comp (Polynomial.X ^ 4) := by
    have hsum4 :
        (∑ k : Fin (9 / 3 + 1),
          Polynomial.C (a k) *
            (1 + 14 * Polynomial.X ^ 4 + Polynomial.X ^ 8) ^ (9 - 3 * k.val) *
            (Polynomial.X ^ 4 * (1 - Polynomial.X ^ 4) ^ 4) ^ k.val) =
        g.comp (Polynomial.X ^ 4) := by
      rw [Fin.sum_univ_four]
      simp only [g, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.pow_comp]
      change _ = Polynomial.C (a 0) * phi8 ^ 9 + Polynomial.C (a 1) * phi8 ^ 6 * delta24 +
        Polynomial.C (a 2) * phi8 ^ 3 * delta24 ^ 2 + Polynomial.C (a 3) * delta24 ^ 3
      rw [phi8_eq, delta24_eq]
      simp
    exact ha.trans hsum4
  have hp_coeff : ∀ w : ℕ, p.coeff w =
      ((Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C ∧ wt x = w)).card : ℚ) := by
    intro w
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ C
    · by_cases hw : wt x = w
      · simp [hx, hw]
      · simp [hx, hw, Ne.symm hw]
    · simp [hx]
  have hg_coeff : ∀ j : ℕ, g.coeff j =
      ((Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C ∧ wt x = 4 * j)).card : ℚ) := by
    intro j
    rw [← hp_coeff (4 * j), hp_eq, coeff_comp_X_pow_four, if_pos (dvd_mul_right 4 j),
      show (4 * j) / 4 = j by omega]
  have hg0 : g.coeff 0 = 1 := by
    rw [hg_coeff 0, mul_zero]
    have hset : Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C ∧ wt x = 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => (wt_eq_zero_iff x).mp h.2, by rintro rfl; exact ⟨C.zero_mem, wt_zero⟩⟩
    rw [hset, Finset.card_singleton, Nat.cast_one]
  have hvan : ∀ j, 1 ≤ j → j ≤ 3 → g.coeff j = 0 := by
    intro j hj1 hj3
    rw [hg_coeff j]
    have hempty : Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C ∧ wt x = 4 * j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      have hne : x ≠ 0 := by intro h0; rw [h0, wt_zero] at hx; omega
      have hge := hd16 x hx.1 hne
      change 16 ≤ wt x at hge
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  obtain ⟨ha0, ha1, ha2, ha3⟩ :=
    gleason72_coeffs_unique (a 0) (a 1) (a 2) (a 3)
      ⟨hg0, hvan 1 (by omega) (by omega), hvan 2 (by omega) (by omega), hvan 3 (by omega) (by omega)⟩
  have hg_exact : g = extremal72PolyU := by
    simp only [g, ha0, ha1, ha2, ha3, ← extremal72PolyU_eq_gleason]
    simp only [map_one, map_neg, map_ofNat]
    ring
  have hA : ∀ j : ℕ,
      ((Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C ∧ wt x = 4 * j)).card : ℚ) =
        extremal72PolyU.coeff j := by
    intro j
    rw [← hg_coeff j, hg_exact]
  have hAnat : ∀ j v : ℕ, extremal72PolyU.coeff j = (v : ℚ) →
      (Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 4 * j)).card = v := by
    intro j v hv
    have hq : ((Finset.univ.filter (fun x : Fin 72 → ZMod 2 => x ∈ C ∧ wt x = 4 * j)).card : ℚ) = (v : ℚ) :=
      (hA j).trans hv
    exact_mod_cast hq
  refine ⟨hdim,
    hAnat 0 1 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 1 0 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 2 0 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 3 0 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 4 249849 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 5 18106704 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 6 462962955 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 7 4397342400 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 8 16602715899 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 9 25756721120 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 10 16602715899 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 11 4397342400 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 12 462962955 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 13 18106704 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 14 249849 (by rw [extremal72PolyU_coeff]; norm_num),
    hAnat 18 1 (by rw [extremal72PolyU_coeff]; norm_num)⟩

/-! ### Section 5: Prime-Order Automorphism Barriers for `[72, 36, 16]` Type II Codes -/

/-- Prime-order orbit partition lemma: for any finite set `S` invariant under a permutation `f`
with `f ^ p = 1` (`p` prime), the number of non-fixed elements of `S` is divisible by `p`,
and hence `S.card ≡ (S.filter (fun a => f a = a)).card [MOD p]`. -/
private lemma prime_perm_nonfix_dvd {α : Type*} [Fintype α]
    {p : ℕ} (hp : Nat.Prime p) (f : Equiv.Perm α) (hfp : f ^ p = 1)
    (S : Finset α) (hS : ∀ a ∈ S, f a ∈ S) :
    p ∣ (S.filter (fun a => f a ≠ a)).card := by
  have hfp_apply : ∀ a : α, (f ^ p) a = a := fun a => by rw [hfp]; rfl
  have hfpow_mem : ∀ k : ℕ, ∀ a ∈ S, (f ^ k) a ∈ S := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      rw [pow_succ']
      exact hS _ (ih a ha)
  have hfpow_mod : ∀ k : ℕ, ∀ a : α, (f ^ k) a = (f ^ (k % p)) a := by
    intro k a
    conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, hfp, one_pow, one_mul]
  let S_nf := S.filter (fun a => f a ≠ a)
  let orb (a : α) : Finset α := (Finset.univ : Finset (Fin p)).image (fun k => (f ^ k.val) a)
  have horb_mem_nf : ∀ a ∈ S_nf, ∀ b ∈ orb a, b ∈ S_nf := by
    intro a ha b hb
    rcases Finset.mem_filter.mp ha with ⟨haS, haf⟩
    rcases Finset.mem_image.mp hb with ⟨k, _, rfl⟩
    refine Finset.mem_filter.mpr ⟨hfpow_mem k.val a haS, ?_⟩
    intro hfix
    have hcomm : f ((f ^ k.val) a) = (f ^ k.val) (f a) := by
      have : f * f ^ k.val = f ^ k.val * f := by rw [← pow_succ', ← pow_succ]
      exact congrArg (fun g : Equiv.Perm α => g a) this
    rw [hcomm] at hfix
    exact haf ((f ^ k.val).injective hfix)
  have horb_card : ∀ a ∈ S_nf, (orb a).card = p := by
    intro a ha
    have haf : f a ≠ a := (Finset.mem_filter.mp ha).2
    rw [Finset.card_image_of_injective _ _, Finset.card_univ, Fintype.card_fin]
    intro j k hjk
    by_contra hne
    have hlt_or : j.val < k.val ∨ k.val < j.val := lt_or_gt_of_ne (fun h => hne (Fin.ext h))
    have hdiff_fix : ∃ d : ℕ, 0 < d ∧ d < p ∧ (f ^ d) a = a := by
      rcases hlt_or with hlt | hlt
      · refine ⟨k.val - j.val, by omega, by omega, ?_⟩
        apply (f ^ j.val).injective
        change (f ^ j.val * f ^ (k.val - j.val)) a = (f ^ j.val) a
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
        exact hjk.symm
      · refine ⟨j.val - k.val, by omega, by omega, ?_⟩
        apply (f ^ k.val).injective
        change (f ^ k.val * f ^ (j.val - k.val)) a = (f ^ k.val) a
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
        exact hjk
    rcases hdiff_fix with ⟨d, hd0, hdp, hda⟩
    -- Use Bezout in ZMod p: there exists u < p with (d * u) % p = 1
    have hgcd : ∃ u : ℕ, (d * u) % p = 1 := by
      have : Fact (Nat.Prime p) := ⟨hp⟩
      have hd_ne : (d : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt hd0 hdp
      refine ⟨((d : ZMod p)⁻¹).val, ?_⟩
      have hmul : ((d * ((d : ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_inv_cancel₀ hd_ne]
      have hval := congrArg ZMod.val hmul
      rw [ZMod.val_natCast, ZMod.val_one] at hval
      exact hval
    rcases hgcd with ⟨u, hu⟩
    have hfpow_d : ∀ t : ℕ, (f ^ (d * t)) a = a := by
      intro t
      rw [pow_mul]
      induction t with
      | zero => rfl
      | succ t' ih =>
        rw [pow_succ']
        change (f ^ d) (((f ^ d) ^ t') a) = a
        rw [ih, hda]
    have hfdu := hfpow_d u
    rw [hfpow_mod, hu, pow_one] at hfdu
    exact haf hfdu
  have horb_eq_or_disj : ∀ a b : α, orb a = orb b ∨ Disjoint (orb a) (orb b) := by
    intro a b
    by_cases hdisj : Disjoint (orb a) (orb b)
    · exact Or.inr hdisj
    · left
      rw [Finset.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨c, hca, hcb⟩
      rcases Finset.mem_image.mp hca with ⟨j, _, rfl⟩
      rcases Finset.mem_image.mp hcb with ⟨k, _, hkj⟩
      -- (f^k) b = (f^j) a, so b = (f^(j + (p - k))) a
      have hb_eq : b = (f ^ (j.val + (p - k.val))) a := by
        apply (f ^ k.val).injective
        change (f ^ k.val) b = (f ^ k.val * f ^ (j.val + (p - k.val))) a
        rw [← pow_add, show k.val + (j.val + (p - k.val)) = p + j.val by omega,
          pow_add, hfp, one_mul]
        exact hkj
      ext x
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨t, rfl⟩
        let shift := j.val + (p - k.val)
        refine ⟨⟨(t.val + (p - shift % p)) % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
        rw [hb_eq]
        change (f ^ ((t.val + (p - shift % p)) % p) * f ^ shift) a = (f ^ t.val) a
        rw [← pow_add, hfpow_mod]
        congr 1
        have hlt1 : shift % p < p := Nat.mod_lt _ hp.pos
        have hdiv : p * (shift / p) + shift % p = shift := Nat.div_add_mod shift p
        have hmod : ((t.val + (p - shift % p)) % p + shift) % p = t.val % p := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show t.val + (p - shift % p) + shift = t.val + p * (1 + shift / p) by
              have : p * (1 + shift / p) = p + p * (shift / p) := by ring
              omega,
            Nat.add_mul_mod_self_left]
        rw [hmod, Nat.mod_eq_of_lt t.isLt]
      · rintro ⟨t, rfl⟩
        rw [hb_eq]
        refine ⟨⟨(t.val + (j.val + (p - k.val))) % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
        change (f ^ ((t.val + (j.val + (p - k.val))) % p)) a =
          (f ^ t.val * f ^ (j.val + (p - k.val))) a
        rw [← pow_add, hfpow_mod (t.val + (j.val + (p - k.val))) a]
  let orbits := S_nf.image orb
  have hbiUnion : S_nf = orbits.biUnion id := by
    ext a
    simp only [orbits, Finset.mem_biUnion, Finset.mem_image, id_eq]
    constructor
    · intro ha
      refine ⟨orb a, ⟨a, ha, rfl⟩, Finset.mem_image.mpr ⟨⟨0, hp.pos⟩, Finset.mem_univ _, rfl⟩⟩
    · rintro ⟨O, ⟨b, hb, rfl⟩, haO⟩
      exact horb_mem_nf b hb a haO
  have hpw : (orbits : Set (Finset α)).PairwiseDisjoint id := by
    intro O₁ hO₁ O₂ hO₂ hne
    rcases Finset.mem_image.mp hO₁ with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hO₂ with ⟨b, _, rfl⟩
    exact (horb_eq_or_disj a b).resolve_left hne
  rw [show (S.filter (fun a => f a ≠ a)).card = S_nf.card from rfl, hbiUnion,
    Finset.card_biUnion hpw]
  have hconst : ∀ O ∈ orbits, (id O).card = p := by
    intro O hO
    rcases Finset.mem_image.mp hO with ⟨a, ha, rfl⟩
    exact horb_card a ha
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  exact dvd_mul_left p orbits.card

private lemma prime_perm_card_modEq {α : Type*} [Fintype α]
    {p : ℕ} (hp : Nat.Prime p) (f : Equiv.Perm α) (hfp : f ^ p = 1)
    (S : Finset α) (hS : ∀ a ∈ S, f a ∈ S) :
    S.card ≡ (S.filter (fun a => f a = a)).card [MOD p] := by
  have hsum := Finset.card_filter_add_card_filter_not (s := S) (p := fun a => f a = a)
  have hdvd := prime_perm_nonfix_dvd hp f hfp S hS
  rcases hdvd with ⟨q, hq⟩
  rw [Nat.ModEq, ← hsum, hq, Nat.add_mul_mod_self_left]

/-- **Theorem 5.1 (Prime-Order Automorphism Weight-Count Congruence):**
Let `C ≤ 𝔽₂ⁿ` be a binary linear code and `σ ∈ S_n` a coordinate-permutation automorphism
of prime order `p` (`σ ^ p = 1`). Then:
1. The number of fixed coordinates `f = |{i | σ i = i}|` satisfies `p ∣ (n - f)` (i.e. `p * c + f = n`).
2. For every weight `w`, the weight count satisfies `A_w(C) ≡ |(C_w)^σ| [MOD p]`.
   In particular, if `¬ (p ∣ A_w(C))`, then `C` contains a `σ`-fixed codeword of weight `w`. -/
theorem prime_aut_orbit_and_weight_modEq {n p : ℕ} (hp : Nat.Prime p)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (σ : Equiv.Perm (Fin n)) (hσp : σ ^ p = 1)
    (hAut : ∀ x ∈ C, (x ∘ σ) ∈ C) :
    (∃ c : ℕ, p * c + (Finset.univ.filter (fun i : Fin n => σ i = i)).card = n) ∧
    (∀ w : ℕ,
      (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card = w)).card ≡
      (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
        x ∈ C ∧ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card = w ∧ x ∘ σ = x)).card
      [MOD p]) := by
  constructor
  · have hdvd := prime_perm_nonfix_dvd hp σ hσp Finset.univ (fun _ _ => Finset.mem_univ _)
    rcases hdvd with ⟨c, hc⟩
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => σ i = i)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have hc' : (Finset.univ.filter (fun i : Fin n => ¬ σ i = i)).card = p * c := by
      convert hc
    exact ⟨c, by omega⟩
  · intro w
    let F : Equiv.Perm (Fin n → ZMod 2) :=
      { toFun := fun x => x ∘ σ
        invFun := fun x => x ∘ σ.symm
        left_inv := fun x => by ext i; simp
        right_inv := fun x => by ext i; simp }
    have hFp_apply : ∀ k : ℕ, ∀ x : Fin n → ZMod 2, (F ^ k) x = x ∘ ⇑(σ ^ k) := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih =>
        intro x
        rw [pow_succ', pow_succ]
        change F ((F ^ k) x) = _
        rw [ih x]
        ext i
        rfl
    have hFp : F ^ p = 1 := by
      ext x i
      rw [hFp_apply p x, hσp]
      rfl
    let Sw := Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C ∧ wt x = w)
    have hSw : ∀ x ∈ Sw, F x ∈ Sw := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨_, hxC, hwx⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAut x hxC, ?_⟩
      change wt (x ∘ σ) = w
      rw [wt_comp_perm, hwx]
    have hmod := prime_perm_card_modEq hp F hFp Sw hSw
    have hfilt : (Sw.filter (fun a => F a = a)).card =
        (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ C ∧ wt x = w ∧ x ∘ σ = x)).card := by
      congr 1
      ext x
      simp only [Sw, F, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_fn_mk, and_assoc]
    convert hmod using 1
    · rfl
    · convert hfilt.symm using 1
      · congr 1
      · congr 1; ext x; simp

/-! #### Odd-Prime Fixed-Subcode Self-Duality, Order-of-2 Obstruction & `p ≡ 1 [MOD 4]` Divisibility -/

private lemma odd_prime_fixed_subcode_structure {n p : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, dot2 x y = 0)
    (σ : Equiv.Perm (Fin n)) (hσp : σ ^ p = 1)
    (hAut : ∀ x ∈ C, (x ∘ σ) ∈ C)
    (c f : ℕ) (hf : f = (Finset.univ.filter (fun i : Fin n => σ i = i)).card)
    (hcf : p * c + f = n) :
    -- 1. There exists a self-dual contracted code of length c + f
    (∃ D : Submodule (ZMod 2) (Fin (c + f) → ZMod 2),
      (∀ y : Fin (c + f) → ZMod 2, y ∈ D ↔ ∀ x ∈ D, dot2 x y = 0) ∧
      ((∀ x ∈ C, 4 ∣ wt x) → p % 4 = 1 → ∀ y ∈ D, 4 ∣ wt y)) ∧
    -- 2. The fixed subcode C^σ has 2 * finrank = c + f, and p ∣ (2^((p - 1) * c / 2) - 1)
    (∃ Cfix : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ x, x ∈ Cfix ↔ x ∈ C ∧ x ∘ σ = x) ∧
      2 * Module.finrank (ZMod 2) Cfix = c + f) ∧
    (p ∣ (2 ^ ((p - 1) * c / 2) - 1)) := by
  have hp_odd_mod2 : (p : ZMod 2) = 1 := by
    have h2 : p % 2 = 1 := by
      have := hp.eq_two_or_odd
      omega
    rw [← ZMod.natCast_mod, h2, Nat.cast_one]
  -- Define the orbits of σ on Fin n
  let orb (i : Fin n) : Finset (Fin n) :=
    (Finset.univ : Finset (Fin p)).image (fun k => (σ ^ k.val) i)
  have hσp_apply : ∀ i : Fin n, (σ ^ p) i = i := fun i => by rw [hσp]; rfl
  have hσpow_mod : ∀ k : ℕ, ∀ i : Fin n, (σ ^ k) i = (σ ^ (k % p)) i := by
    intro k i
    conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, hσp, one_pow, one_mul]
  have horb_self : ∀ i : Fin n, i ∈ orb i := fun i =>
    Finset.mem_image.mpr ⟨⟨0, hp.pos⟩, Finset.mem_univ _, rfl⟩
  have horb_eq_or_disj : ∀ i j : Fin n, orb i = orb j ∨ Disjoint (orb i) (orb j) := by
    intro i j
    by_cases hdisj : Disjoint (orb i) (orb j)
    · exact Or.inr hdisj
    · left
      rw [Finset.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨a, hai, haj⟩
      rcases Finset.mem_image.mp hai with ⟨k₁, _, rfl⟩
      rcases Finset.mem_image.mp haj with ⟨k₂, _, hk2⟩
      have hj_eq : j = (σ ^ (k₁.val + (p - k₂.val))) i := by
        apply (σ ^ k₂.val).injective
        change (σ ^ k₂.val) j = (σ ^ k₂.val * σ ^ (k₁.val + (p - k₂.val))) i
        rw [← pow_add, show k₂.val + (k₁.val + (p - k₂.val)) = p + k₁.val by omega,
          pow_add, hσp, one_mul]
        exact hk2
      ext x
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨t, rfl⟩
        let shift := k₁.val + (p - k₂.val)
        refine ⟨⟨(t.val + (p - shift % p)) % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
        rw [hj_eq]
        change (σ ^ ((t.val + (p - shift % p)) % p) * σ ^ shift) i = (σ ^ t.val) i
        rw [← pow_add, hσpow_mod]
        congr 1
        have hlt1 : shift % p < p := Nat.mod_lt _ hp.pos
        have hdiv : p * (shift / p) + shift % p = shift := Nat.div_add_mod shift p
        have hmod : ((t.val + (p - shift % p)) % p + shift) % p = t.val % p := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show t.val + (p - shift % p) + shift = t.val + p * (1 + shift / p) by
              have : p * (1 + shift / p) = p + p * (shift / p) := by ring
              omega,
            Nat.add_mul_mod_self_left]
        rw [hmod, Nat.mod_eq_of_lt t.isLt]
      · rintro ⟨t, rfl⟩
        rw [hj_eq]
        refine ⟨⟨(t.val + (k₁.val + (p - k₂.val))) % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
        change (σ ^ ((t.val + (k₁.val + (p - k₂.val))) % p)) i =
          (σ ^ t.val * σ ^ (k₁.val + (p - k₂.val))) i
        rw [← pow_add, hσpow_mod (t.val + (k₁.val + (p - k₂.val))) i]
  have horb_card_fix : ∀ i : Fin n, σ i = i → (orb i).card = 1 := by
    intro i hi
    have hpow : ∀ k : ℕ, (σ ^ k) i = i := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ']; change σ ((σ ^ k) i) = i; rw [ih, hi]
    have hset : orb i = {i} := by
      ext j
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨by rintro ⟨k, rfl⟩; exact hpow k.val, fun h => ⟨⟨0, hp.pos⟩, h.symm⟩⟩
    rw [hset, Finset.card_singleton]
  have horb_card_nonfix : ∀ i : Fin n, σ i ≠ i → (orb i).card = p := by
    intro i hi
    rw [Finset.card_image_of_injective _ _, Finset.card_univ, Fintype.card_fin]
    intro j k hjk
    by_contra hne
    have hlt_or : j.val < k.val ∨ k.val < j.val := lt_or_gt_of_ne (fun h => hne (Fin.ext h))
    have hdiff_fix : ∃ d : ℕ, 0 < d ∧ d < p ∧ (σ ^ d) i = i := by
      rcases hlt_or with hlt | hlt
      · refine ⟨k.val - j.val, by omega, by omega, ?_⟩
        apply (σ ^ j.val).injective
        change (σ ^ j.val * σ ^ (k.val - j.val)) i = (σ ^ j.val) i
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]; exact hjk.symm
      · refine ⟨j.val - k.val, by omega, by omega, ?_⟩
        apply (σ ^ k.val).injective
        change (σ ^ k.val * σ ^ (j.val - k.val)) i = (σ ^ k.val) i
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]; exact hjk
    rcases hdiff_fix with ⟨d, hd0, hdp, hdi⟩
    have hgcd : ∃ u : ℕ, (d * u) % p = 1 := by
      have : Fact (Nat.Prime p) := ⟨hp⟩
      have hd_ne : (d : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt hd0 hdp
      refine ⟨((d : ZMod p)⁻¹).val, ?_⟩
      have hmul : ((d * ((d : ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_inv_cancel₀ hd_ne]
      have hval := congrArg ZMod.val hmul
      rw [ZMod.val_natCast, ZMod.val_one] at hval
      exact hval
    rcases hgcd with ⟨u, hu⟩
    have hfpow_d : ∀ t : ℕ, (σ ^ (d * t)) i = i := by
      intro t
      rw [pow_mul]
      induction t with
      | zero => rfl
      | succ t' ih => rw [pow_succ']; change (σ ^ d) (((σ ^ d) ^ t') i) = i; rw [ih, hdi]
    have hfdu := hfpow_d u
    rw [hσpow_mod, hu, pow_one] at hfdu
    exact hi hfdu
  -- Count orbits = c + f!
  let allOrbs : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).image orb
  let fixOrbs := (Finset.univ.filter (fun i : Fin n => σ i = i)).image orb
  let nfOrbs := (Finset.univ.filter (fun i : Fin n => σ i ≠ i)).image orb
  have hall_union : allOrbs = fixOrbs ∪ nfOrbs := by
    ext O
    simp only [allOrbs, fixOrbs, nfOrbs, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases h : σ i = i
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr ⟨i, h, rfl⟩
    · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> exact ⟨i, rfl⟩
  have hdisj_orbs : Disjoint fixOrbs nfOrbs := by
    rw [Finset.disjoint_left]
    intro O hO1 hO2
    rcases Finset.mem_image.mp hO1 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hO2 with ⟨j, hj, hji⟩
    have hc1 := horb_card_fix i (Finset.mem_filter.mp hi).2
    have hc2 := horb_card_nonfix j (Finset.mem_filter.mp hj).2
    rw [hji] at hc2
    have := hp.one_lt
    omega
  have hfix_card : fixOrbs.card = f := by
    rw [hf]
    refine Finset.card_image_of_injOn ?_
    intro i hi j hj hij
    have hi' : σ i = i := (Finset.mem_filter.mp hi).2
    have hj' : σ j = j := (Finset.mem_filter.mp hj).2
    have h1 : orb i = {i} := by
      have hc := horb_card_fix i hi'
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨horb_self i, fun x hx =>
        Finset.card_le_one.mp (le_of_eq hc) x hx i (horb_self i)⟩
    have h2 : orb j = {j} := by
      have hc := horb_card_fix j hj'
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨horb_self j, fun x hx =>
        Finset.card_le_one.mp (le_of_eq hc) x hx j (horb_self j)⟩
    rw [h1, h2] at hij
    exact Finset.singleton_injective hij
  have hnf_card : nfOrbs.card = c := by
    let Snf := Finset.univ.filter (fun i : Fin n => σ i ≠ i)
    have hbi : Snf = nfOrbs.biUnion id := by
      ext i
      simp only [Snf, nfOrbs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, id_eq]
      constructor
      · intro hi; exact ⟨orb i, ⟨i, hi, rfl⟩, horb_self i⟩
      · rintro ⟨O, ⟨j, hj, rfl⟩, hij⟩
        rcases Finset.mem_image.mp hij with ⟨k, _, rfl⟩
        intro hfix
        have hcomm : σ ((σ ^ k.val) j) = (σ ^ k.val) (σ j) := by
          have : σ * σ ^ k.val = σ ^ k.val * σ := by rw [← pow_succ', ← pow_succ]
          exact congrArg (fun g : Equiv.Perm (Fin n) => g j) this
        rw [hcomm] at hfix
        exact hj ((σ ^ k.val).injective hfix)
    have hpw : (nfOrbs : Set (Finset (Fin n))).PairwiseDisjoint id := by
      intro O₁ hO₁ O₂ hO₂ hne
      rcases Finset.mem_image.mp hO₁ with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp hO₂ with ⟨j, _, rfl⟩
      exact (horb_eq_or_disj i j).resolve_left hne
    have hSnf_card : Snf.card = nfOrbs.card * p := by
      rw [hbi, Finset.card_biUnion hpw]
      have hconst : ∀ O ∈ nfOrbs, (id O).card = p := by
        intro O hO
        rcases Finset.mem_image.mp hO with ⟨j, hj, rfl⟩
        exact horb_card_nonfix j (Finset.mem_filter.mp hj).2
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => σ i = i)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have hSnf_def : (Finset.univ.filter (fun i : Fin n => ¬ σ i = i)).card = Snf.card := rfl
    have hSnf_eq : Snf.card = p * c := by omega
    have hpos : 0 < p := hp.pos
    nlinarith
  have hall_card : allOrbs.card = c + f := by
    rw [hall_union, Finset.card_union_of_disjoint hdisj_orbs, hfix_card, hnf_card, add_comm]
  -- Every orbit has size 1 or p, and allOrbs partitions Fin n
  have hall_pw : (allOrbs : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro O₁ hO₁ O₂ hO₂ hne
    rcases Finset.mem_image.mp hO₁ with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hO₂ with ⟨j, _, rfl⟩
    exact (horb_eq_or_disj i j).resolve_left hne
  have hall_cover : (Finset.univ : Finset (Fin n)) = allOrbs.biUnion id := by
    ext i
    simp only [allOrbs, Finset.mem_univ, Finset.mem_biUnion, Finset.mem_image, true_and,
      id_eq, true_iff]
    exact ⟨orb i, ⟨i, rfl⟩, horb_self i⟩
  have horb_card_cases : ∀ O ∈ allOrbs, O.card = 1 ∨ O.card = p := by
    intro O hO
    rcases Finset.mem_image.mp hO with ⟨i, _, rfl⟩
    by_cases h : σ i = i
    · exact Or.inl (horb_card_fix i h)
    · exact Or.inr (horb_card_nonfix i h)
  -- Enumerate orbits via e : Fin (c + f) ≃ {O // O ∈ allOrbs}
  let e : Fin (c + f) ≃ {O : Finset (Fin n) // O ∈ allOrbs} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hall_card])).symm
  -- Lift map: Fin (c + f) → ZMod 2  ↪  Fin n → ZMod 2 (constant on each orbit!)
  let lift : (Fin (c + f) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun v i => v (e.symm ⟨orb i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      map_add' := fun v₁ v₂ => by ext i; rfl
      map_smul' := fun a v => by ext i; rfl }
  have hlift_fixed : ∀ v : Fin (c + f) → ZMod 2, lift v ∘ σ = lift v := by
    intro v
    ext i
    simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    congr 2
    apply Subtype.ext
    have hmem : σ i ∈ orb i :=
      Finset.mem_image.mpr ⟨⟨1, hp.one_lt⟩, Finset.mem_univ _, by simp⟩
    exact (horb_eq_or_disj (σ i) i).resolve_right
      (Finset.not_disjoint_iff.mpr ⟨σ i, horb_self (σ i), hmem⟩)
  have hlift_surj_fixed : ∀ x : Fin n → ZMod 2, x ∘ σ = x → ∃ v, lift v = x := by
    intro x hx
    have hpow : ∀ k : ℕ, ∀ i : Fin n, x ((σ ^ k) i) = x i := by
      intro k
      induction k with
      | zero => intro i; rfl
      | succ k ih =>
        intro i; rw [pow_succ']; change (x ∘ σ) ((σ ^ k) i) = x i; rw [hx, ih]
    -- For each orbit O ∈ allOrbs, pick a representative (using Classical.choose)
    have hnonempty : ∀ O : {O : Finset (Fin n) // O ∈ allOrbs}, O.1.Nonempty := by
      rintro ⟨O, hO⟩
      rcases Finset.mem_image.mp hO with ⟨i, _, rfl⟩
      exact ⟨i, horb_self i⟩
    let v : Fin (c + f) → ZMod 2 := fun j => x (hnonempty (e j)).choose
    refine ⟨v, ?_⟩
    ext i
    simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, v]
    have hrep_mem : (hnonempty (e (e.symm ⟨orb i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩))).choose ∈
        orb i := by
      have h := (hnonempty (e (e.symm ⟨orb i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩))).choose_spec
      simpa using h
    rcases Finset.mem_image.mp hrep_mem with ⟨k, _, hk⟩
    rw [← hk, hpow]
  have hlift_inj : Function.Injective lift := by
    intro v₁ v₂ hv
    ext j
    rcases Finset.mem_image.mp (e j).2 with ⟨i, _, hi⟩
    have hvi := congrFun hv i
    simp only [lift, LinearMap.coe_mk, AddHom.coe_mk] at hvi
    have heq : (⟨orb i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ :
        {O : Finset (Fin n) // O ∈ allOrbs}) = e j := Subtype.ext hi
    rw [heq, Equiv.symm_apply_apply] at hvi
    exact hvi
  -- Dot product preservation: dot2 (lift u) (lift v) = dot2 u v!
  have hlift_dot : ∀ u v : Fin (c + f) → ZMod 2, dot2 (lift u) (lift v) = dot2 u v := by
    intro u v
    unfold dot2
    rw [hall_cover, Finset.sum_biUnion hall_pw, ← Finset.sum_coe_sort allOrbs, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hconst : ∀ i ∈ (e j).1, lift u i * lift v i = u j * v j := by
      intro i hi
      have horb_eq : orb i = (e j).1 := by
        rcases Finset.mem_image.mp (e j).2 with ⟨a, _, ha⟩
        rw [← ha] at hi ⊢
        exact (horb_eq_or_disj i a).resolve_right
          (Finset.not_disjoint_iff.mpr ⟨i, horb_self i, hi⟩)
      simp only [lift, LinearMap.coe_mk, AddHom.coe_mk]
      have hsub : (⟨orb i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ :
          {O : Finset (Fin n) // O ∈ allOrbs}) = e j := Subtype.ext horb_eq
      rw [hsub, Equiv.symm_apply_apply]
    change ∑ i ∈ (e j).1, lift u i * lift v i = u j * v j
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard_one : ((e j).1.card : ZMod 2) = 1 := by
      rcases horb_card_cases (e j).1 (e j).2 with hc1 | hcp
      · rw [hc1, Nat.cast_one]
      · rw [hcp, hp_odd_mod2]
    rw [hcard_one, one_mul]
  -- Weight mod 4 preservation when p % 4 = 1!
  have hlift_wt_mod4 : p % 4 = 1 → ∀ v : Fin (c + f) → ZMod 2, wt (lift v) % 4 = wt v % 4 := by
    intro hp4 v
    have hL : wt (lift v) = ∑ j : Fin (c + f), (e j).1.card * (if v j ≠ 0 then 1 else 0) := by
      simp only [wt, Finset.card_filter]
      rw [hall_cover, Finset.sum_biUnion hall_pw, ← Finset.sum_coe_sort allOrbs,
        ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hconst : ∀ i ∈ (e j).1, (if lift v i ≠ 0 then 1 else 0) = if v j ≠ 0 then 1 else 0 := by
        intro i hi
        have horb_eq : orb i = (e j).1 := by
          rcases Finset.mem_image.mp (e j).2 with ⟨a, _, ha⟩
          rw [← ha] at hi ⊢
          exact (horb_eq_or_disj i a).resolve_right
            (Finset.not_disjoint_iff.mpr ⟨i, horb_self i, hi⟩)
        simp only [lift, LinearMap.coe_mk, AddHom.coe_mk]
        have hsub : (⟨orb i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ :
            {O : Finset (Fin n) // O ∈ allOrbs}) = e j := Subtype.ext horb_eq
        simp only [hsub, Equiv.symm_apply_apply]
      change ∑ i ∈ (e j).1, (if lift v i ≠ 0 then 1 else 0) = _
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    have hR : wt v = ∑ j : Fin (c + f), (if v j ≠ 0 then 1 else 0) := by
      simp [wt, Finset.card_filter]
    rw [hL, hR]
    -- Show equality in ZMod 4
    have hZ4 : ((∑ j : Fin (c + f), (e j).1.card * (if v j ≠ 0 then 1 else 0) : ℕ) : ZMod 4) =
        ((∑ j : Fin (c + f), (if v j ≠ 0 then 1 else 0) : ℕ) : ZMod 4) := by
      rw [Nat.cast_sum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_mul]
      have hcard1 : ((e j).1.card : ZMod 4) = 1 := by
        rcases horb_card_cases (e j).1 (e j).2 with hc1 | hcp
        · rw [hc1, Nat.cast_one]
        · rw [hcp, ← ZMod.natCast_mod, hp4, Nat.cast_one]
      rw [hcard1, one_mul]
    have hval := congrArg ZMod.val hZ4
    rw [ZMod.val_natCast, ZMod.val_natCast] at hval
    exact hval
  -- Trace projection π(x) = ∑ k : Fin p, x ∘ σ^k
  let trMap : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun x i => ∑ k : Fin p, x ((σ ^ k.val) i)
      map_add' := fun x y => by ext i; simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by ext i; simp [Finset.mul_sum] }
  have htr_mem_C : ∀ x ∈ C, trMap x ∈ C := by
    intro x hx
    have hpow_mem : ∀ k : ℕ, (x ∘ ⇑(σ ^ k)) ∈ C := by
      intro k; induction k with
      | zero => exact hx
      | succ k ih =>
        rw [pow_succ]
        exact hAut (x ∘ ⇑(σ ^ k)) ih
    have hsum : trMap x = ∑ k : Fin p, (x ∘ ⇑(σ ^ k.val)) := by
      ext i; simp [trMap, Finset.sum_apply]
    rw [hsum]
    exact C.sum_mem fun k _ => hpow_mem k.val
  have htr_fixed : ∀ x : Fin n → ZMod 2, trMap x ∘ σ = trMap x := by
    intro x
    ext i
    simp only [trMap, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    refine Fintype.sum_equiv
      { toFun := fun k => ⟨(k.val + 1) % p, Nat.mod_lt _ hp.pos⟩
        invFun := fun k => ⟨(k.val + (p - 1)) % p, Nat.mod_lt _ hp.pos⟩
        left_inv := fun k => by
          ext; dsimp only
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show k.val + 1 + (p - 1) = k.val + p by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt k.isLt]
        right_inv := fun k => by
          ext; dsimp only
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show k.val + (p - 1) + 1 = k.val + p by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt k.isLt] } _ _ fun k => ?_
    change x (((σ ^ k.val) * σ) i) = x ((σ ^ ((k.val + 1) % p)) i)
    rw [← pow_succ, hσpow_mod]
  have htr_id_on_fixed : ∀ x : Fin n → ZMod 2, x ∘ σ = x → trMap x = x := by
    intro x hx
    have hpow : ∀ k : ℕ, ∀ i : Fin n, x ((σ ^ k) i) = x i := by
      intro k; induction k with
      | zero => intro i; rfl
      | succ k ih => intro i; rw [pow_succ']; change (x ∘ σ) ((σ ^ k) i) = x i; rw [hx, ih]
    ext i
    simp only [trMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_congr rfl (fun k _ => hpow k.val i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hp_odd_mod2, one_mul]
  have htr_selfAdj : ∀ x y : Fin n → ZMod 2, dot2 (trMap x) y = dot2 x (trMap y) := by
    intro x y
    simp only [dot2, trMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Fintype.sum_equiv
      { toFun := fun k => ⟨(p - k.val) % p, Nat.mod_lt _ hp.pos⟩
        invFun := fun k => ⟨(p - k.val) % p, Nat.mod_lt _ hp.pos⟩
        left_inv := fun k => by
          ext; dsimp only
          by_cases hk : k.val = 0
          · simp [hk]
          · rw [Nat.mod_eq_of_lt (by omega : p - k.val < p),
              show p - (p - k.val) = k.val by omega, Nat.mod_eq_of_lt k.isLt]
        right_inv := fun k => by
          ext; dsimp only
          by_cases hk : k.val = 0
          · simp [hk]
          · rw [Nat.mod_eq_of_lt (by omega : p - k.val < p),
              show p - (p - k.val) = k.val by omega, Nat.mod_eq_of_lt k.isLt] } _ _ fun k => ?_
    simp only [Equiv.coe_fn_mk]
    rw [← Equiv.sum_comp (σ ^ k.val) (fun i => x i * y ((σ ^ ((p - k.val) % p)) i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    change y i = y (((σ ^ ((p - k.val) % p)) * (σ ^ k.val)) i)
    rw [← pow_add, hσpow_mod]
    have h0 : ((p - k.val) % p + k.val) % p = 0 := by
      by_cases hk : k.val = 0
      · simp [hk]
      · rw [Nat.mod_eq_of_lt (by omega : p - k.val < p), Nat.sub_add_cancel (le_of_lt k.isLt),
          Nat.mod_self]
    rw [h0, pow_zero]; rfl
  -- Define D = C.comap lift (contracted fixed subcode!) and Cfix = D.map lift
  let D : Submodule (ZMod 2) (Fin (c + f) → ZMod 2) := C.comap lift
  have hD_selfDual : ∀ y : Fin (c + f) → ZMod 2, y ∈ D ↔ ∀ x ∈ D, dot2 x y = 0 := by
    intro y
    constructor
    · intro hy x hx
      rw [← hlift_dot]
      exact (hSD (lift y)).mp hy (lift x) hx
    · intro horth
      change lift y ∈ C
      rw [hSD]
      intro x hx
      have htr_fix := htr_fixed x
      obtain ⟨u, hu⟩ := hlift_surj_fixed (trMap x) htr_fix
      have huD : u ∈ D := by
        change lift u ∈ C
        rw [hu]
        exact htr_mem_C x hx
      have h1 : dot2 x (lift y) = dot2 (trMap x) (lift y) := by
        calc
          dot2 x (lift y) = dot2 x (trMap (lift y)) := by
            rw [htr_id_on_fixed (lift y) (hlift_fixed y)]
          _ = dot2 (trMap x) (lift y) := (htr_selfAdj x (lift y)).symm
      rw [h1, ← hu, hlift_dot]
      exact horth u huD
  have hD_typeII : (∀ x ∈ C, 4 ∣ wt x) → p % 4 = 1 → ∀ y ∈ D, 4 ∣ wt y := by
    intro hT2 hp4 y hy
    have h4 : 4 ∣ wt (lift y) := hT2 (lift y) hy
    have hmod := hlift_wt_mod4 hp4 y
    omega
  let Cfix : Submodule (ZMod 2) (Fin n → ZMod 2) := D.map lift
  have hCfix_mem : ∀ x, x ∈ Cfix ↔ x ∈ C ∧ x ∘ σ = x := by
    intro x
    constructor
    · rintro ⟨v, hvD, rfl⟩
      exact ⟨hvD, hlift_fixed v⟩
    · rintro ⟨hxC, hxfix⟩
      obtain ⟨v, rfl⟩ := hlift_surj_fixed x hxfix
      exact ⟨v, hxC, rfl⟩
  have hCfix_dim : 2 * Module.finrank (ZMod 2) Cfix = c + f := by
    have hD_dim := (selfDual_finrank_and_card D hD_selfDual).1
    have hCfix_range : Cfix = LinearMap.range (lift.comp D.subtype) := by
      ext x
      simp [Cfix]
    have hmap : Module.finrank (ZMod 2) Cfix = Module.finrank (ZMod 2) D := by
      rw [hCfix_range]
      exact LinearMap.finrank_range_of_inj (hlift_inj.comp Subtype.val_injective)
    rw [hmap]
    exact hD_dim
  -- Now define E = ker(trMap|_C) and compute dim(E) = (p - 1) * c / 2, and p ∣ (2^(dim E) - 1)!
  let trC : C →ₗ[ZMod 2] Cfix :=
    { toFun := fun x => ⟨trMap x.1, (hCfix_mem _).mpr ⟨htr_mem_C x.1 x.2, htr_fixed x.1⟩⟩
      map_add' := fun x y => Subtype.ext (map_add trMap x.1 y.1)
      map_smul' := fun a x => Subtype.ext (map_smul trMap a x.1) }
  have htrC_surj : Function.Surjective trC := by
    rintro ⟨y, hy⟩
    rcases (hCfix_mem y).mp hy with ⟨hyC, hyfix⟩
    refine ⟨⟨y, hyC⟩, Subtype.ext ?_⟩
    exact htr_id_on_fixed y hyfix
  let Esub : Submodule (ZMod 2) (Fin n → ZMod 2) := (LinearMap.ker trC).map C.subtype
  have hEsub_dim : Module.finrank (ZMod 2) Esub = (p - 1) * c / 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker trC
    rw [LinearMap.range_eq_top.mpr htrC_surj, finrank_top] at hrn
    have hC_dim := (selfDual_finrank_and_card C hSD).1
    have hE_range : Esub = LinearMap.range (C.subtype.comp (LinearMap.ker trC).subtype) := by
      ext x
      simp [Esub]
    have hE_eq : Module.finrank (ZMod 2) Esub = Module.finrank (ZMod 2) (LinearMap.ker trC) := by
      rw [hE_range]
      exact LinearMap.finrank_range_of_inj (Subtype.val_injective.comp Subtype.val_injective)
    rw [hE_eq]
    have h2E : 2 * Module.finrank (ZMod 2) (LinearMap.ker trC) = (p - 1) * c := by
      have hp1 : 1 ≤ p := hp.one_lt.le
      have hmul : (p - 1) * c + c = p * c := by
        rw [← add_one_mul, Nat.sub_add_cancel hp1]
      omega
    omega
  -- Apply prime_perm_nonfix_dvd to S = Esub \ {0} under x ↦ x ∘ σ!
  have hdvd_pow : p ∣ (2 ^ ((p - 1) * c / 2) - 1) := by
    let F : Equiv.Perm (Fin n → ZMod 2) :=
      { toFun := fun x => x ∘ σ
        invFun := fun x => x ∘ σ.symm
        left_inv := fun x => by ext i; simp
        right_inv := fun x => by ext i; simp }
    have hFp_apply : ∀ k : ℕ, ∀ x : Fin n → ZMod 2, (F ^ k) x = x ∘ ⇑(σ ^ k) := by
      intro k; induction k with
      | zero => intro x; rfl
      | succ k ih =>
        intro x; rw [pow_succ', pow_succ]; change F ((F ^ k) x) = _; rw [ih x]; ext i; rfl
    have hFp : F ^ p = 1 := by ext x i; rw [hFp_apply p x, hσp]; rfl
    let SE := (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ Esub)).erase 0
    have hSE_mem : ∀ x, x ∈ SE ↔ x ∈ C ∧ trMap x = 0 ∧ x ≠ 0 := by
      intro x
      simp only [SE, Esub, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
      constructor
      · rintro ⟨hne, ⟨⟨y, hyC⟩, hker, rfl⟩⟩
        exact ⟨hyC, congrArg Subtype.val hker, hne⟩
      · rintro ⟨hxC, htr0, hne⟩
        exact ⟨hne, ⟨⟨x, hxC⟩, Subtype.ext htr0, rfl⟩⟩
    have hSE_inv : ∀ x ∈ SE, F x ∈ SE := by
      intro x hx
      rcases (hSE_mem x).mp hx with ⟨hxC, htr0, hne⟩
      rw [hSE_mem]
      refine ⟨hAut x hxC, ?_, ?_⟩
      · -- trMap (x ∘ σ) = trMap x ∘ σ = 0
        have hcomm : trMap (x ∘ σ) = trMap x ∘ σ := by
          ext i
          simp only [trMap, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : σ * σ ^ k.val = σ ^ k.val * σ := by rw [← pow_succ', ← pow_succ]
          exact congrArg x (congrArg (fun g : Equiv.Perm (Fin n) => g i) h1)
        change trMap (x ∘ σ) = 0
        rw [hcomm, htr0]; rfl
      · intro h0
        apply hne
        ext i
        have := congrFun h0 (σ.symm i)
        simpa [F] using this
    have hSE_nofix : SE.filter (fun a => F a ≠ a) = SE := by
      rw [Finset.filter_true_of_mem]
      intro x hx hfix
      rcases (hSE_mem x).mp hx with ⟨_, htr0, hne⟩
      have hid := htr_id_on_fixed x hfix
      rw [htr0] at hid
      exact hne hid.symm
    have hdvd := prime_perm_nonfix_dvd hp F hFp SE hSE_inv
    have hdvd' : p ∣ SE.card := by
      convert hdvd using 1
      convert (congrArg Finset.card hSE_nofix).symm
    have hSE_card : SE.card = 2 ^ ((p - 1) * c / 2) - 1 := by
      have h0mem : (0 : Fin n → ZMod 2) ∈ Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ Esub) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ 0, Esub.zero_mem⟩
      rw [Finset.card_erase_of_mem h0mem, card_submodule_eq_two_pow_finrank, hEsub_dim]
    rw [hSE_card] at hdvd'
    exact hdvd'
  exact ⟨⟨D, hD_selfDual, hD_typeII⟩, ⟨Cfix, hCfix_mem, hCfix_dim⟩, hdvd_pow⟩

/-- **Theorem 5.2 (Odd-Prime Automorphism Obstructions for Type II Self-Dual Codes):**
Let `C ≤ 𝔽₂ⁿ` be a Type II self-dual binary linear code and `σ ∈ S_n` an automorphism of odd
prime order `p` (`p ≠ 2`, `σ ^ p = 1`) with `f` fixed points and `c` `p`-cycles (`p * c + f = n`).
Then:
1. **Order-of-2 Obstruction:** `p ∣ (2 ^ ((p - 1) * c / 2) - 1)`.
2. **Gleason–Pierce Fixed-Subcode Divisibility:** If `p % 4 = 1`, then `8 ∣ (c + f)`. -/
theorem odd_prime_aut_obstructions {n p c : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hSD : ∀ y : Fin n → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin n, x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card)
    (σ : Equiv.Perm (Fin n)) (hσp : σ ^ p = 1)
    (hAut : ∀ x ∈ C, (x ∘ σ) ∈ C)
    (hcf : p * c + (Finset.univ.filter (fun i : Fin n => σ i = i)).card = n) :
    p ∣ (2 ^ ((p - 1) * c / 2) - 1) ∧
    (p % 4 = 1 → 8 ∣ (c + (Finset.univ.filter (fun i : Fin n => σ i = i)).card)) := by
  obtain ⟨⟨D, hD_sd, hD_t2⟩, _, hdvd⟩ :=
    odd_prime_fixed_subcode_structure hp hp_odd C hSD σ hσp hAut c
      (Finset.univ.filter (fun i : Fin n => σ i = i)).card rfl hcf
  refine ⟨hdvd, fun hp4 => ?_⟩
  exact gleason_pierce_eight_dvd_length D hD_sd (hD_t2 hT2 hp4)

/-- Polymorphic helper: if `σ` has prime order `p > w` and fixes a codeword `x` of weight `w`,
then `supp(x)` lies entirely inside the fixed points of `σ`, hence `w ≤ f`. -/
private lemma fixed_wt_le_fixed_coords {n p w : ℕ} (hp : Nat.Prime p) (hpw : w < p)
    (σ : Equiv.Perm (Fin n)) (hσp : σ ^ p = 1)
    (x : Fin n → ZMod 2) (hwx : wt x = w) (hxfix : x ∘ σ = x) :
    w ≤ (Finset.univ.filter (fun i : Fin n => σ i = i)).card := by
  have hsub : Finset.univ.filter (fun i : Fin n => x i ≠ 0) ⊆
      Finset.univ.filter (fun i : Fin n => σ i = i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra hne
    have hpow_x : ∀ k : ℕ, x ((σ ^ k) i) = x i := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ']; change (x ∘ σ) ((σ ^ k) i) = x i; rw [hxfix, ih]
    let orb := (Finset.univ : Finset (Fin p)).image (fun k => (σ ^ k.val) i)
    have horb_sub : orb ⊆ Finset.univ.filter (fun j : Fin n => x j ≠ 0) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hpow_x]; exact hi⟩
    have horb_card : orb.card = p := by
      have hdvd_i := prime_perm_nonfix_dvd hp σ hσp orb (by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩
        refine Finset.mem_image.mpr ⟨⟨(k.val + 1) % p, Nat.mod_lt _ hp.pos⟩, Finset.mem_univ _, ?_⟩
        change (σ ^ ((k.val + 1) % p)) i = (σ * σ ^ k.val) i
        rw [← pow_succ']
        conv_rhs => rw [← Nat.div_add_mod (k.val + 1) p, pow_add, pow_mul, hσp, one_pow, one_mul])
      have hnf_eq : (orb.filter (fun j => σ j ≠ j)).card = orb.card := by
        congr 1
        rw [Finset.filter_true_of_mem]
        intro j hj hfixj
        rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩
        have hcomm : σ ((σ ^ k.val) i) = (σ ^ k.val) (σ i) := by
          have : σ * σ ^ k.val = σ ^ k.val * σ := by rw [← pow_succ', ← pow_succ]
          exact congrArg (fun g : Equiv.Perm (Fin n) => g i) this
        rw [hcomm] at hfixj
        exact hne ((σ ^ k.val).injective hfixj)
      have hdvd_i' : p ∣ orb.card := by
        convert hdvd_i using 1
        convert hnf_eq.symm
      have hpos_orb : 0 < orb.card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_image.mpr ⟨⟨0, hp.pos⟩, Finset.mem_univ _, rfl⟩⟩
      have hle_orb : orb.card ≤ p := by
        calc orb.card ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_image_le
          _ = p := by simp
      have hge_orb : p ≤ orb.card := Nat.le_of_dvd hpos_orb hdvd_i'
      omega
    have hlew : p ≤ w := by
      rw [← horb_card, ← hwx]
      exact Finset.card_le_card horb_sub
    omega
  have hle := Finset.card_le_card hsub
  change wt x ≤ _ at hle
  omega

/-- **Theorem 5.3 (PPL 158 Prime-Order Automorphism Exclusions & Even-Cycle Barrier):**
For ANY extremal Type II `[72, 36, 16]` binary self-dual code `C ≤ 𝔽₂⁷²` and any non-identity
automorphism `σ ∈ S_{72}` of prime order `p` (`σ ^ p = 1`, `σ ≠ 1`):
1. **`p ∉ {29, 37, 43, 53, 59, 61, 67}`** (all seven prime orders are unconditionally ruled out!).
2. For **`p ∈ {3, 5, 11, 13, 19}`**, the number of `p`-cycles `c` in `σ` MUST be **even** (`2 ∣ c`). -/
theorem ppl158_prime_automorphism_barriers
    (C : Submodule (ZMod 2) (Fin 72 → ZMod 2))
    (hSD : ∀ y : Fin 72 → ZMod 2, y ∈ C ↔ ∀ x ∈ C, (∑ i : Fin 72, x i * y i) = 0)
    (hT2 : ∀ x ∈ C, 4 ∣ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card)
    (hd16 : ∀ x ∈ C, x ≠ 0 → 16 ≤ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card)
    {p : ℕ} (hp : Nat.Prime p)
    (σ : Equiv.Perm (Fin 72)) (hσp : σ ^ p = 1) (hσne : σ ≠ 1)
    (hAut : ∀ x ∈ C, (x ∘ σ) ∈ C) :
    (p ≠ 29 ∧ p ≠ 37 ∧ p ≠ 43 ∧ p ≠ 53 ∧ p ≠ 59 ∧ p ≠ 61 ∧ p ≠ 67) ∧
    ((p = 3 ∨ p = 5 ∨ p = 11 ∨ p = 13 ∨ p = 19) →
      ∃ c : ℕ, 2 ∣ c ∧ p * c + (Finset.univ.filter (fun i : Fin 72 => σ i = i)).card = 72) := by
  obtain ⟨⟨c, hcf⟩, hmod_all⟩ := prime_aut_orbit_and_weight_modEq hp C σ hσp hAut
  set f := (Finset.univ.filter (fun i : Fin 72 => σ i = i)).card
  have hc_pos : 1 ≤ c := by
    by_contra h0
    have hc0 : c = 0 := by omega
    rw [hc0, mul_zero, zero_add] at hcf
    apply hσne
    ext i
    have hall : Finset.univ.filter (fun j : Fin 72 => σ j = j) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa [f] using hcf)
    have hi : i ∈ Finset.univ.filter (fun j : Fin 72 => σ j = j) := by
      rw [hall]; exact Finset.mem_univ i
    exact congrArg Fin.val (Finset.mem_filter.mp hi).2
  -- Helper: if p ∣ (2^k - 1), then 2^k % p = 1
  have hdvd_to_mod : ∀ q k : ℕ, Nat.Prime q → q ∣ (2 ^ k - 1) → (2 ^ k) % q = 1 := by
    intro q k hq hdvd
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    rcases hdvd with ⟨t, ht⟩
    have heq : 2 ^ k = 1 + q * t := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq.one_lt]
  -- Helper: when p > 16 and p ∤ 249849, there exists a σ-fixed codeword of weight 16, hence 16 ≤ f!
  have hfix16_le_f : 16 < p → ¬ p ∣ 249849 → 16 ≤ f := by
    intro hp16 hndvd
    obtain ⟨_, _, _, _, _, hA16, _⟩ := ppl158_unique_weight_enumerator C hSD hT2 hd16
    have hmod16 := hmod_all 16
    rw [hA16] at hmod16
    have hex : ∃ x : Fin 72 → ZMod 2, x ∈ C ∧ wt x = 16 ∧ x ∘ σ = x := by
      by_contra hno
      have hempty : Finset.univ.filter (fun x : Fin 72 → ZMod 2 =>
          x ∈ C ∧ (Finset.univ.filter (fun i : Fin 72 => x i ≠ 0)).card = 16 ∧ x ∘ σ = x) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ hx
        exact hno ⟨x, hx⟩
      rw [hempty, Finset.card_empty] at hmod16
      exact hndvd (Nat.dvd_of_mod_eq_zero hmod16)
    rcases hex with ⟨x, _, hwx, hxfix⟩
    exact fixed_wt_le_fixed_coords hp hp16 σ hσp x hwx hxfix
  -- Part 1: Rule out p ∈ {29, 37, 43, 53, 59, 61, 67}
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- p ≠ 29
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc12 : c = 1 ∨ c = 2 := by omega
    rcases hc12 with rfl | rfl
    · simp at hdvd
    · have hf14 : f = 14 := by omega
      have hge16 : 16 ≤ f := hfix16_le_f (by omega) (by norm_num)
      omega
  · -- p ≠ 37
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc1 : c = 1 := by omega
    subst hc1
    simp at hdvd
  · -- p ≠ 43
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc1 : c = 1 := by omega
    subst hc1
    simp at hdvd
  · -- p ≠ 53
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc1 : c = 1 := by omega
    subst hc1
    simp at hdvd
  · -- p ≠ 59
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc1 : c = 1 := by omega
    subst hc1
    simp at hdvd
  · -- p ≠ 61
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc1 : c = 1 := by omega
    subst hc1
    simp at hdvd
  · -- p ≠ 67
    rintro rfl
    obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
    have hc1 : c = 1 := by omega
    subst hc1
    simp at hdvd
  · -- Part 2: For p ∈ {3, 5, 11, 13, 19}, 2 ∣ c!
    intro hpcases
    refine ⟨c, ?_, hcf⟩
    -- In each case, q ∣ (2^((q-1)/2) + 1), so 2^((q-1)/2) ≡ -1 (mod q), forcing 2 ∣ c!
    have heven_of_neg_one : ∀ q : ℕ, Nat.Prime q → 2 < q →
        q ∣ (2 ^ ((q - 1) / 2) + 1) → q ∣ (2 ^ ((q - 1) * c / 2) - 1) → 2 ∣ c := by
      intro q hq hq2 hneg_nat hdvd
      have hneg : (2 : ZMod q) ^ ((q - 1) / 2) = -1 := by
        have h0 : ((2 ^ ((q - 1) / 2) + 1 : ℕ) : ZMod q) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hneg_nat
        push_cast at h0
        exact eq_neg_of_add_eq_zero_left h0
      have hmod := hdvd_to_mod q ((q - 1) * c / 2) hq hdvd
      have hqodd : q % 2 = 1 := by have := hq.eq_two_or_odd; omega
      have hdiv_eq : (q - 1) * c / 2 = ((q - 1) / 2) * c := by
        have h2q : 2 ∣ (q - 1) := by omega
        rcases h2q with ⟨k, hk⟩
        rw [hk, show 2 * k * c = 2 * (k * c) by ring, Nat.mul_div_cancel_left _ (by omega),
          Nat.mul_div_cancel_left _ (by omega)]
      have hZ : (2 : ZMod q) ^ (((q - 1) / 2) * c) = 1 := by
        have hcast : ((2 ^ ((q - 1) * c / 2) : ℕ) : ZMod q) = 1 := by
          rw [← ZMod.natCast_mod, hmod, Nat.cast_one]
        rw [hdiv_eq] at hcast
        simpa using hcast
      rw [pow_mul, hneg] at hZ
      by_contra hnot2
      have hodd : Odd c := Nat.not_even_iff_odd.mp (by intro ⟨k, hk⟩; exact hnot2 ⟨k, by omega⟩)
      rw [Odd.neg_one_pow hodd] at hZ
      -- -1 = 1 in ZMod q implies (2 : ZMod q) = 0, contradicting q > 2!
      have h20 : ((2 : ℕ) : ZMod q) = 0 := by
        rw [Nat.cast_ofNat]
        linear_combination -hZ
      rw [ZMod.natCast_eq_zero_iff] at h20
      have := Nat.le_of_dvd (by omega) h20
      omega
    rcases hpcases with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
      exact heven_of_neg_one 3 hp (by omega) (by norm_num) hdvd
    · obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
      exact heven_of_neg_one 5 hp (by omega) (by norm_num) hdvd
    · obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
      exact heven_of_neg_one 11 hp (by omega) (by norm_num) hdvd
    · obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
      exact heven_of_neg_one 13 hp (by omega) (by norm_num) hdvd
    · obtain ⟨hdvd, _⟩ := odd_prime_aut_obstructions hp (by omega) C hSD hT2 σ hσp hAut hcf
      exact heven_of_neg_one 19 hp (by omega) (by norm_num) hdvd

end PPL158
