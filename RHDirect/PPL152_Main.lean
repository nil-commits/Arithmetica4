/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# PPL 152 (KCIK #4 — Existence of NPT Bound Entanglement / Undistillable NPT Quantum States)

## Honest Scope Statement
**KCIK Problem #4** (`openquantumproblems.com`, `prizeproblems.org`, `≈€2,026`,
**LIVE-VERIFIED OPEN** as of 2026) asks whether there exist **undistillable NPT quantum states**
(i.e. NPT bound entanglement): does there exist a finite dimension `d` and a bipartite density
matrix `ρ` on `ℂ^d ⊗ ℂ^d` such that `ρ^{T_B}` is NOT positive semidefinite (NPT), yet `ρ` is
`n`-copy undistillable for ALL `n ≥ 1`?

This module makes **no claim** to resolve the open KCIK #4 problem. Instead, it provides a
**100% unconditional, kernel-verified, pure-Mathlib-signature formalization** of the complete
mathematical theory surrounding NPT bound entanglement and the DiVincenzo–Shor–Smolin–Terhal–
Thapliyal (DSS 2000) / Dür–Cirac–Lewenstein–Briegel (DCLB 2000) / Watrous (2004) Werner-state
framework:

1. **Section 1 — Bipartite Partial Transpose & Peres–Horodecki (1996) PPT Criterion:**
   - `ppl152_partialTranspose_involutive`, `ppl152_partialTranspose_trace`,
     `ppl152_partialTranspose_isHermitian`.
   - `ppl152_product_expectation_partialTranspose` & `ppl152_schmidt_rank_one_nonneg`:
     Schmidt rank 1 never witnesses NPT or distillability.
   - `ppl152_peres_horodecki_separable_ppt` & `ppl152_npt_implies_entangled`:
     every separable state is PPT, so NPT unconditionally implies entanglement.
2. **Section 2 — Tensor Powers, 2-Qubit SLOCC Equivalence & Horodecki (1998) Undistillability:**
   - `ppl152_tensorPower_posSemidef`, `ppl152_tensorPower_partialTranspose_and_trace`,
     `ppl152_ppt_tensorPower_ppt`.
   - `ppl152_slocc_2qubit_iff_schmidt_rank_two`: exact equivalence between 2-qubit SLOCC
     projection to an NPT state and negative expectation of `M^{T_B}` on a Schmidt-rank-`≤ 2`
     vector.
   - `ppl152_horodecki_ppt_undistillable`: every PPT state is `n`-copy undistillable for all `n`.
   - `ppl152_distillable_monotone_copies`: `n`-copy distillability implies `m`-copy distillability
     for all `m ≥ n`.
3. **Section 3 — Exact 1-Parameter Werner State Family `W_d(α)` (`d ≥ 2`):**
   - `ppl152_werner_posSemidef_iff` & `ppl152_werner_isState`: exact Hermiticity, `trace = 1`,
     and exact positivity range `α ∈ [-1, 1]`.
   - `ppl152_werner_unitary_invariant`: exact `U ⊗ U` invariance for all unitary `U`.
   - `ppl152_werner_partialTranspose_formula`: exact formula `W_d(α)^{T_B}` in terms of
     `|Φ⁺⟩⟨Φ⁺|`.
   - `ppl152_werner_ppt_iff`: exact PPT/NPT threshold `PosSemidef W_d(α)^{T_B} ↔ α ≤ 1/d`.
4. **Section 4 — DCLB / DSS (2000) Exact 1-Copy Undistillability & `d = 2` vs `d ≥ 3` Dichotomy:**
   - `ppl152_schmidt_rank_two_phiPlus_bound`: sharp rank-`≤ 2` overlap bound
     `‖∑_i ψ(i,i)‖² ≤ 2 ∑_{i,j} ‖ψ(i,j)‖²`.
   - `ppl152_werner_oneCopy_undistillable_iff`: exact 1-copy undistillability threshold `α ≤ 1/2`.
   - `ppl152_werner_d2_npt_iff_oneCopy_distillable`: in `d = 2`, every NPT Werner state is
     1-copy distillable.
   - `ppl152_werner_d_ge_3_npt_oneCopy_undistillable`: for every `d ≥ 3`, every `α ∈ (1/d, 1/2]`
     gives a strictly NPT, entangled, yet strictly 1-copy undistillable Werner state.
5. **Section 5 — Multi-Copy (`n ≥ 1`) Tensor-Power Undistillability & Exact DSS / KCIK #4 Barrier:**
   - `ppl152_werner_nCopy_subset_undistillable`: for every `n ≥ 1`, `d ≥ 2`, and `α ∈ [0, 1]`
     satisfying `(1 + α)^n - (1 - α)^n ≤ 1`, `W_d(α)` is `n`-copy undistillable.
   - `ppl152_nCopy_undistillable_npt_exists`: for every `n ≥ 1`, every `d > 3 * n`, and every
     `α ∈ (1/d, 1/(3*n)]`, `W_d(α)` is strictly NPT yet `k`-copy undistillable for all `1 ≤ k ≤ n`
     (exact `∀ n, ∃ d, ∃ ρ` Watrous/DSS phenomenon, contrasted with the open `∃ d, ∃ ρ, ∀ n`
     quantifier order of KCIK #4).
   - `ppl152_werner_nCopy_negative_sector_and_barrier`: `(W_d(α)^{⊗ n})^{T_B}` is strictly
     negative on the odd-`Φ⁺` sector for every `n ≥ 1` whenever `α > 1/d`, while
     `(1 + α)^n - (1 - α)^n → ∞` for fixed `α > 0`, formalizing the odd-vs-even subset
     cancellation barrier of KCIK #4.

Every public `theorem` in `namespace PPL152` uses **100% pure Mathlib signatures** (`0` custom or
`private` definitions/structures/abbrevs in any public theorem type).
-/

namespace PPL152

open Matrix BigOperators Finset Complex
open scoped ComplexOrder

/-! ### Private Helpers (never referenced in any public theorem signature) -/

private lemma re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma im_star_mul_self (z : ℂ) : (star z * z).im = 0 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  simp

private lemma star_mul_self_nonneg_re (z : ℂ) : 0 ≤ (star z * z).re := by
  rw [re_star_mul_self]
  positivity

private lemma star_dot_mulVec_of_isHermitian_im_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hH : M.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have hconj : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    calc
      star (star x ⬝ᵥ M *ᵥ x)
          = ∑ i, ∑ j, star (star (x i) * (M i j * x j)) := by
              simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ i, ∑ j, star (x j) * (M j i * x i) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              have hij : star (M i j) = M j i := by
                simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hH j) i
              simp [hij]
              ring
      _ = ∑ j, ∑ i, star (x j) * (M j i * x i) := Finset.sum_comm
      _ = star x ⬝ᵥ M *ᵥ x := by
              simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have h1 : (star (star x ⬝ᵥ M *ᵥ x)).im = (star x ⬝ᵥ M *ᵥ x).im := congr_arg Complex.im hconj
  simp at h1
  linarith

private lemma posSemidef_iff_isHermitian_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    M.PosSemidef ↔ M.IsHermitian ∧ ∀ x : ι → ℂ, 0 ≤ (star x ⬝ᵥ M *ᵥ x).re := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hH, hpos⟩
    refine ⟨hH, fun x => (Complex.le_def.mp (hpos x)).1⟩
  · rintro ⟨hH, hre⟩
    refine ⟨hH, fun x => ?_⟩
    rw [Complex.le_def]
    refine ⟨hre x, ?_⟩
    rw [Complex.zero_im, star_dot_mulVec_of_isHermitian_im_zero hH x]

private lemma posSemidef_rankOne {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.PosSemidef (Matrix.of (fun i j => v i * star (v j))) := by
  rw [posSemidef_iff_isHermitian_re]
  refine ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, mul_comm]
  · intro x
    have hval : star x ⬝ᵥ Matrix.of (fun i j => v i * star (v j)) *ᵥ x =
        star (∑ j, star (v j) * x j) * (∑ j, star (v j) * x j) := by
      have h1 : star (∑ j, star (v j) * x j) * (∑ j, star (v j) * x j) =
          ∑ i, ∑ j, star (x i) * (v i * star (v j) * x j) := by
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [star_mul', star_star]
        ring
      rw [h1]
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hval]
    exact star_mul_self_nonneg_re _

private lemma posSemidef_smul_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c) (hM : M.PosSemidef) :
    ((c : ℂ) • M).PosSemidef := by
  rw [posSemidef_iff_isHermitian_re] at hM ⊢
  refine ⟨?_, ?_⟩
  · ext i j
    have hij : star (M j i) = M i j := by
      simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hM.1 i) j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.star_def, hij, mul_comm]
  · intro x
    have hmul : star x ⬝ᵥ ((c : ℂ) • M) *ᵥ x = (c : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_assoc]
    rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hc (hM.2 x)

private lemma posSemidef_finset_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset κ) (f : κ → Matrix ι ι ℂ) (hf : ∀ k ∈ s, (f k).PosSemidef) :
    (∑ k ∈ s, f k).PosSemidef := by
  rw [posSemidef_iff_isHermitian_re]
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, star_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hH := (hf k hk).isHermitian
    simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hH i) j
  · intro x
    have hsum : star x ⬝ᵥ (∑ k ∈ s, f k) *ᵥ x = ∑ k ∈ s, star x ⬝ᵥ (f k) *ᵥ x := by
      calc
        star x ⬝ᵥ (∑ k ∈ s, f k) *ᵥ x
          = ∑ i, ∑ j, ∑ k ∈ s, star (x i) * (f k i j * x j) := by
              simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Pi.star_apply,
                Finset.sum_mul, Finset.mul_sum]
        _ = ∑ i, ∑ k ∈ s, ∑ j, star (x i) * (f k i j * x j) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ k ∈ s, ∑ i, ∑ j, star (x i) * (f k i j * x j) := Finset.sum_comm
        _ = ∑ k ∈ s, star x ⬝ᵥ (f k) *ᵥ x := by
              simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hsum, Complex.re_sum]
    exact Finset.sum_nonneg fun k hk => ((posSemidef_iff_isHermitian_re (f k)).mp (hf k hk)).2 x

/-- Elementary Cauchy–Schwarz inequality for complex finite sums:
`‖∑ i, u i * v i‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2)`. -/
private lemma complex_cauchy_schwarz_sq {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖∑ i : ι, u i * v i‖ ^ 2 ≤ (∑ i : ι, ‖u i‖ ^ 2) * (∑ i : ι, ‖v i‖ ^ 2) := by
  have htri : ‖∑ i : ι, u i * v i‖ ≤ ∑ i : ι, ‖u i‖ * ‖v i‖ := by
    calc
      ‖∑ i : ι, u i * v i‖ ≤ ∑ i : ι, ‖u i * v i‖ := norm_sum_le _ _
      _ = ∑ i : ι, ‖u i‖ * ‖v i‖ := by simp
  have hsq : ‖∑ i : ι, u i * v i‖ ^ 2 ≤ (∑ i : ι, ‖u i‖ * ‖v i‖) ^ 2 := by
    have h0 : 0 ≤ ‖∑ i : ι, u i * v i‖ := norm_nonneg _
    nlinarith
  exact le_trans hsq (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖))

/-- Master Rank-`≤ 2` Partial-Trace Overlap Bound (zero square roots, zero SVD):
For any finite types `A, B` and any Schmidt-rank-`≤ 2` vector `ψ = a₁ ⊗ b₁ + a₂ ⊗ b₂` on
`(A × B) × (A × B)`, contracting the `A`-system against `|Φ⁺_A⟩` yields at most `2 ‖ψ‖²`. -/
private lemma schmidt_rank_two_partial_trace_bound {A B : Type*} [Fintype A] [Fintype B]
    (a₁ a₂ b₁ b₂ : A × B → ℂ) :
    ∑ u : B, ∑ v : B,
      ‖∑ x : A, (a₁ (x, u) * b₁ (x, v) + a₂ (x, u) * b₂ (x, v))‖ ^ 2 ≤
    2 * ∑ p : A × B, ∑ q : A × B, ‖a₁ p * b₁ q + a₂ p * b₂ q‖ ^ 2 := by
  let N₁ : ℝ := ∑ p : A × B, ‖a₁ p‖ ^ 2
  have hN₁_nonneg : 0 ≤ N₁ := Finset.sum_nonneg fun p _ => sq_nonneg _
  by_cases hN₁ : N₁ = 0
  · have ha₁ : ∀ p : A × B, a₁ p = 0 := by
      intro p
      have hle : ‖a₁ p‖ ^ 2 ≤ N₁ :=
        Finset.single_le_sum (fun q _ => sq_nonneg ‖a₁ q‖) (Finset.mem_univ p)
      have hsq : ‖a₁ p‖ ^ 2 = 0 := le_antisymm (hN₁ ▸ hle) (sq_nonneg _)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    have h1 : ∑ u : B, ∑ v : B,
        ‖∑ x : A, (a₁ (x, u) * b₁ (x, v) + a₂ (x, u) * b₂ (x, v))‖ ^ 2 ≤
        (∑ p : A × B, ‖a₂ p‖ ^ 2) * (∑ q : A × B, ‖b₂ q‖ ^ 2) := by
      calc
        ∑ u : B, ∑ v : B,
            ‖∑ x : A, (a₁ (x, u) * b₁ (x, v) + a₂ (x, u) * b₂ (x, v))‖ ^ 2
          = ∑ u : B, ∑ v : B, ‖∑ x : A, a₂ (x, u) * b₂ (x, v)‖ ^ 2 := by
              simp [ha₁]
        _ ≤ ∑ u : B, ∑ v : B, (∑ x : A, ‖a₂ (x, u)‖ ^ 2) * (∑ x : A, ‖b₂ (x, v)‖ ^ 2) := by
              refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
              exact complex_cauchy_schwarz_sq (fun x => a₂ (x, u)) (fun x => b₂ (x, v))
        _ = (∑ u : B, ∑ x : A, ‖a₂ (x, u)‖ ^ 2) * (∑ v : B, ∑ x : A, ‖b₂ (x, v)‖ ^ 2) := by
              simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
        _ = (∑ p : A × B, ‖a₂ p‖ ^ 2) * (∑ q : A × B, ‖b₂ q‖ ^ 2) := by
              rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
    have h2 : ∑ p : A × B, ∑ q : A × B, ‖a₁ p * b₁ q + a₂ p * b₂ q‖ ^ 2 =
        (∑ p : A × B, ‖a₂ p‖ ^ 2) * (∑ q : A × B, ‖b₂ q‖ ^ 2) := by
      simp_rw [ha₁, zero_mul, zero_add, norm_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    have hnn : 0 ≤ (∑ p : A × B, ‖a₂ p‖ ^ 2) * (∑ q : A × B, ‖b₂ q‖ ^ 2) := by
      positivity
    linarith
  · have hN₁_pos : 0 < N₁ := lt_of_le_of_ne hN₁_nonneg (Ne.symm hN₁)
    let c : ℂ := (∑ p : A × B, star (a₁ p) * a₂ p) / (N₁ : ℂ)
    let w : A × B → ℂ := fun p => a₂ p - c * a₁ p
    let d₁ : A × B → ℂ := fun q => b₁ q + c * b₂ q
    have hdecomp : ∀ p q : A × B, a₁ p * b₁ q + a₂ p * b₂ q = a₁ p * d₁ q + w p * b₂ q := by
      intro p q; simp only [w, d₁]; ring
    have horth : ∑ p : A × B, star (a₁ p) * w p = 0 := by
      have hsum_a₁ : ∑ p : A × B, star (a₁ p) * a₁ p = (N₁ : ℂ) := by
        apply Complex.ext
        · simp only [Complex.re_sum, re_star_mul_self, Complex.ofReal_re, N₁]
        · simp only [Complex.im_sum, im_star_mul_self, Finset.sum_const_zero, Complex.ofReal_im]
      calc
        ∑ p : A × B, star (a₁ p) * w p
          = (∑ p : A × B, star (a₁ p) * a₂ p) - c * (∑ p : A × B, star (a₁ p) * a₁ p) := by
              simp only [w, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl fun p _ => by ring
        _ = (∑ p : A × B, star (a₁ p) * a₂ p) - c * (N₁ : ℂ) := by rw [hsum_a₁]
        _ = 0 := by
              have hN1c : (N₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hN₁_pos)
              simp only [c]
              rw [div_mul_cancel₀ _ hN1c, sub_self]
    have horth' : ∑ p : A × B, star (w p) * a₁ p = 0 := by
      have hstar := congr_arg star horth
      simp only [star_sum, star_mul', star_star, star_zero] at hstar
      simpa [mul_comm] using hstar
    have hnorm_sq : ∑ p : A × B, ∑ q : A × B, ‖a₁ p * b₁ q + a₂ p * b₂ q‖ ^ 2 =
        (∑ p : A × B, ‖a₁ p‖ ^ 2) * (∑ q : A × B, ‖d₁ q‖ ^ 2) +
        (∑ p : A × B, ‖w p‖ ^ 2) * (∑ q : A × B, ‖b₂ q‖ ^ 2) := by
      have hterm : ∀ p q : A × B,
          (‖a₁ p * b₁ q + a₂ p * b₂ q‖ ^ 2 : ℝ) =
            (‖a₁ p‖ ^ 2 * ‖d₁ q‖ ^ 2 + ‖w p‖ ^ 2 * ‖b₂ q‖ ^ 2) +
            (star (a₁ p) * w p * (star (d₁ q) * b₂ q)).re +
            (star (w p) * a₁ p * (star (b₂ q) * d₁ q)).re := by
        intro p q
        rw [hdecomp p q, ← re_star_mul_self]
        have hexp : star (a₁ p * d₁ q + w p * b₂ q) * (a₁ p * d₁ q + w p * b₂ q) =
            (star (a₁ p) * a₁ p) * (star (d₁ q) * d₁ q) +
            (star (w p) * w p) * (star (b₂ q) * b₂ q) +
            star (a₁ p) * w p * (star (d₁ q) * b₂ q) +
            star (w p) * a₁ p * (star (b₂ q) * d₁ q) := by
          simp only [star_add, star_mul']
          ring
        have hm : ∀ u v : ℂ, (star u * u * (star v * v)).re = ‖u‖ ^ 2 * ‖v‖ ^ 2 := fun u v => by
          rw [Complex.mul_re, re_star_mul_self, re_star_mul_self, im_star_mul_self, zero_mul,
            sub_zero]
        rw [hexp, Complex.add_re, Complex.add_re, Complex.add_re, hm, hm]
      simp_rw [hterm, Finset.sum_add_distrib]
      have hcross1 : ∑ p : A × B, ∑ q : A × B, (star (a₁ p) * w p * (star (d₁ q) * b₂ q)).re = 0 := by
        have : ∑ p : A × B, ∑ q : A × B, star (a₁ p) * w p * (star (d₁ q) * b₂ q) = 0 := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul, horth, zero_mul]
        simpa [Complex.re_sum] using congr_arg Complex.re this
      have hcross2 : ∑ p : A × B, ∑ q : A × B, (star (w p) * a₁ p * (star (b₂ q) * d₁ q)).re = 0 := by
        have : ∑ p : A × B, ∑ q : A × B, star (w p) * a₁ p * (star (b₂ q) * d₁ q) = 0 := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul, horth', zero_mul]
        simpa [Complex.re_sum] using congr_arg Complex.re this
      rw [hcross1, hcross2, add_zero, add_zero]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hnorm_sq]
    calc
      ∑ u : B, ∑ v : B,
          ‖∑ x : A, (a₁ (x, u) * b₁ (x, v) + a₂ (x, u) * b₂ (x, v))‖ ^ 2
        = ∑ u : B, ∑ v : B,
            ‖(∑ x : A, a₁ (x, u) * d₁ (x, v)) + (∑ x : A, w (x, u) * b₂ (x, v))‖ ^ 2 := by
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            congr 2
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun x _ => hdecomp (x, u) (x, v)
      _ ≤ ∑ u : B, ∑ v : B,
            (2 * ‖∑ x : A, a₁ (x, u) * d₁ (x, v)‖ ^ 2 +
             2 * ‖∑ x : A, w (x, u) * b₂ (x, v)‖ ^ 2) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            have hle := norm_add_le (∑ x : A, a₁ (x, u) * d₁ (x, v)) (∑ x : A, w (x, u) * b₂ (x, v))
            have hnn : 0 ≤ ‖(∑ x : A, a₁ (x, u) * d₁ (x, v)) + (∑ x : A, w (x, u) * b₂ (x, v))‖ :=
              norm_nonneg _
            nlinarith [sq_nonneg (‖∑ x : A, a₁ (x, u) * d₁ (x, v)‖ - ‖∑ x : A, w (x, u) * b₂ (x, v)‖)]
      _ ≤ ∑ u : B, ∑ v : B,
            (2 * ((∑ x : A, ‖a₁ (x, u)‖ ^ 2) * (∑ x : A, ‖d₁ (x, v)‖ ^ 2)) +
             2 * ((∑ x : A, ‖w (x, u)‖ ^ 2) * (∑ x : A, ‖b₂ (x, v)‖ ^ 2))) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            have hcs1 := complex_cauchy_schwarz_sq (fun x => a₁ (x, u)) (fun x => d₁ (x, v))
            have hcs2 := complex_cauchy_schwarz_sq (fun x => w (x, u)) (fun x => b₂ (x, v))
            linarith
      _ = 2 * ((∑ p : A × B, ‖a₁ p‖ ^ 2) * (∑ q : A × B, ‖d₁ q‖ ^ 2) +
               (∑ p : A × B, ‖w p‖ ^ 2) * (∑ q : A × B, ‖b₂ q‖ ^ 2)) := by
            simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
            rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right,
              Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
            ring

private lemma one_add_pow_le_one_add_two_mul {x : ℝ} (hx : 0 ≤ x) :
    ∀ m : ℕ, (m : ℝ) * x ≤ 1 / 2 → (1 + x) ^ m ≤ 1 + 2 * (m : ℝ) * x := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : (k : ℝ) * x ≤ 1 / 2 := by
        have : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
        nlinarith
      have hih := ih hk'
      rw [pow_succ]
      push_cast
      nlinarith [mul_nonneg hx (show (0 : ℝ) ≤ 1 - 2 * (k : ℝ) * x by linarith)]

private lemma one_sub_mul_le_one_sub_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ m : ℕ, 1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      push_cast
      have h1x : 0 ≤ 1 - x := by linarith
      have hkx : 0 ≤ (k : ℝ) * x := by positivity
      nlinarith

/-! ### Section 1: Bipartite Partial Transpose, Product States & Peres–Horodecki (1996) -/

/-- Partial transpose on system `B` is an involution on `Matrix (α × β) (α × β) ℂ`. -/
theorem ppl152_partialTranspose_involutive {α β : Type*} (ρ : Matrix (α × β) (α × β) ℂ) :
    Matrix.of (fun (p q : α × β) =>
      (Matrix.of (fun (u v : α × β) => ρ (u.1, v.2) (v.1, u.2))) (p.1, q.2) (q.1, p.2)) =
      ρ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rfl

/-- Partial transpose preserves matrix trace. -/
theorem ppl152_partialTranspose_trace {α β : Type*} [Fintype α] [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) :
    Matrix.trace (Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2))) = Matrix.trace ρ := by
  simp [Matrix.trace, Matrix.diag]

/-- Partial transpose preserves Hermiticity. -/
theorem ppl152_partialTranspose_isHermitian {α β : Type*}
    {ρ : Matrix (α × β) (α × β) ℂ} (hH : ρ.IsHermitian) :
    Matrix.IsHermitian (Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2))) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hH (i, l)) (k, j)

/-- On every product vector `a ⊗ b` (Schmidt rank 1), the expectation of `ρ^{T_B}` equals
the expectation of `ρ` on `a ⊗ star b`. -/
theorem ppl152_product_expectation_partialTranspose {α β : Type*} [Fintype α] [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) (a : α → ℂ) (b : β → ℂ) :
    star (fun p : α × β => a p.1 * b p.2) ⬝ᵥ
      Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2)) *ᵥ (fun p : α × β => a p.1 * b p.2) =
    star (fun p : α × β => a p.1 * star (b p.2)) ⬝ᵥ
      ρ *ᵥ (fun p : α × β => a p.1 * star (b p.2)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_mul', star_star,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    ∑ j : β, ∑ k : α, ∑ l : β,
        star (a i) * star (b j) * (ρ (i, l) (k, j) * (a k * b l))
      = ∑ k : α, ∑ j : β, ∑ l : β,
          star (a i) * star (b j) * (ρ (i, l) (k, j) * (a k * b l)) := Finset.sum_comm
    _ = ∑ k : α, ∑ l : β, ∑ j : β,
          star (a i) * star (b j) * (ρ (i, l) (k, j) * (a k * b l)) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l : β, ∑ k : α, ∑ j : β,
          star (a i) * star (b j) * (ρ (i, l) (k, j) * (a k * b l)) := Finset.sum_comm
    _ = ∑ l : β, ∑ k : α, ∑ j : β,
          star (a i) * b l * (ρ (i, l) (k, j) * (a k * star (b j))) := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun j _ => by ring

/-- Every positive semidefinite bipartite state `ρ` (even if NPT!) has nonnegative expectation
of `ρ^{T_B}` on every product vector `a ⊗ b` (Schmidt rank 1). Thus Schmidt rank 1 never
witnesses NPT or distillability. -/
theorem ppl152_schmidt_rank_one_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef) (a : α → ℂ) (b : β → ℂ) :
    0 ≤ (star (fun p : α × β => a p.1 * b p.2) ⬝ᵥ
      Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2)) *ᵥ
      (fun p : α × β => a p.1 * b p.2)).re := by
  rw [ppl152_product_expectation_partialTranspose]
  exact ((posSemidef_iff_isHermitian_re ρ).mp hρ).2 _

/-- **Peres–Horodecki (1996) PPT Criterion for Separable States:**
Every finite nonnegative linear combination (in particular every convex combination) of product
pure states `|a_r⟩⟨a_r| ⊗ |b_r⟩⟨b_r|` has a positive semidefinite partial transpose `ρ^{T_B}`. -/
theorem ppl152_peres_horodecki_separable_ppt {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ)
    (hsep : ∃ (m : ℕ) (p : Fin m → ℝ) (a : Fin m → α → ℂ) (b : Fin m → β → ℂ),
      (∀ r, 0 ≤ p r) ∧
      ρ = ∑ r : Fin m, (p r : ℂ) •
        Matrix.of (fun (u v : α × β) => a r u.1 * star (a r v.1) * (b r u.2 * star (b r v.2)))) :
    Matrix.PosSemidef (Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2))) := by
  rcases hsep with ⟨m, p, a, b, hp, hρ⟩
  have hpt : Matrix.of (fun (u v : α × β) => ρ (u.1, v.2) (v.1, u.2)) =
      ∑ r : Fin m, (p r : ℂ) •
        Matrix.of (fun (u v : α × β) =>
          (a r u.1 * star (b r u.2)) * star (a r v.1 * star (b r v.2))) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [hρ]
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
      star_star]
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hpt]
  refine posSemidef_finset_sum Finset.univ _ fun r _ => ?_
  exact posSemidef_smul_real (hp r) (posSemidef_rankOne (fun u : α × β => a r u.1 * star (b r u.2)))

/-- **Peres–Horodecki Entanglement Witness (Contrapositive):**
Any bipartite state whose partial transpose is not positive semidefinite (NPT) is unconditionally
entangled (cannot be written as a convex combination of product pure states). -/
theorem ppl152_npt_implies_entangled {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {ρ : Matrix (α × β) (α × β) ℂ}
    (hnpt : ¬ Matrix.PosSemidef (Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2)))) :
    ¬ ∃ (m : ℕ) (p : Fin m → ℝ) (a : Fin m → α → ℂ) (b : Fin m → β → ℂ),
      (∀ r, 0 ≤ p r) ∧ (∑ r, p r = 1) ∧
      ρ = ∑ r : Fin m, (p r : ℂ) •
        Matrix.of (fun (u v : α × β) => a r u.1 * star (a r v.1) * (b r u.2 * star (b r v.2))) := by
  rintro ⟨m, p, a, b, hp, _, hρ⟩
  exact hnpt (ppl152_peres_horodecki_separable_ppt ρ ⟨m, p, a, b, hp, hρ⟩)

/-! ### Section 2: Tensor Powers, 2-Qubit SLOCC Equivalence & Horodecki (1998) Undistillability -/

/-- Any `n`-fold tensor power of a positive semidefinite matrix is positive semidefinite. -/
theorem ppl152_tensorPower_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (n : ℕ) :
    Matrix.PosSemidef (Matrix.of (fun (p q : Fin n → ι) => ∏ t : Fin n, M (p t) (q t))) := by
  have hS_exists : ∃ S : Matrix ι ι ℂ, M = Sᴴ * S := by
    let U : Matrix ι ι ℂ := (hM.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun k => ((Real.sqrt (hM.isHermitian.eigenvalues k) : ℝ) : ℂ))
    refine ⟨D * Uᴴ, ?_⟩
    have hDD : Dᴴ * D = Matrix.diagonal (RCLike.ofReal ∘ hM.isHermitian.eigenvalues) := by
      ext i j
      simp only [D, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        rw [Finset.sum_eq_single i]
        · simp only [↓reduceIte, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
            Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
        · intro k _ hki; simp [hki]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [hij, ↓reduceIte]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hki : k = i
        · subst hki; simp [hij]
        · simp [hki]
    calc
      M = ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hM.isHermitian.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ hM.isHermitian.eigenvalues)) :=
          hM.isHermitian.spectral_theorem
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hM.isHermitian.eigenvalues) * Uᴴ := rfl
      _ = U * (Dᴴ * D) * Uᴴ := by rw [hDD]
      _ = (D * Uᴴ)ᴴ * (D * Uᴴ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rcases hS_exists with ⟨S, hS⟩
  let R : Matrix (Fin n → ι) (Fin n → ι) ℂ := Matrix.of (fun f p => ∏ t : Fin n, S (f t) (p t))
  have hEq : Matrix.of (fun (p q : Fin n → ι) => ∏ t : Fin n, M (p t) (q t)) = Rᴴ * R := by
    ext p q
    simp only [R, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_prod]
    calc
      ∏ t : Fin n, M (p t) (q t)
        = ∏ t : Fin n, ∑ w : ι, star (S w (p t)) * S w (q t) := by
            refine Finset.prod_congr rfl fun t _ => ?_
            have ht := congr_fun (congr_fun hS (p t)) (q t)
            simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using ht
      _ = ∑ f : Fin n → ι, ∏ t : Fin n, (star (S (f t) (p t)) * S (f t) (q t)) :=
            Fintype.prod_sum (fun t w => star (S w (p t)) * S w (q t))
      _ = ∑ f : Fin n → ι, (∏ t : Fin n, star (S (f t) (p t))) * ∏ t : Fin n, S (f t) (q t) := by
            refine Finset.sum_congr rfl fun f _ => Finset.prod_mul_distrib
  rw [hEq]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- Partial transpose commutes with `n`-copy tensor powers, and trace is multiplicative. -/
theorem ppl152_tensorPower_partialTranspose_and_trace {α β : Type*} [Fintype α] [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) (n : ℕ) :
    Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
      (Matrix.of (fun (u v : (Fin n → α) × (Fin n → β)) =>
        ∏ t : Fin n, ρ (u.1 t, u.2 t) (v.1 t, v.2 t))) (p.1, q.2) (q.1, p.2)) =
    Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
      ∏ t : Fin n, (Matrix.of (fun (u v : α × β) => ρ (u.1, v.2) (v.1, u.2)))
        (p.1 t, p.2 t) (q.1 t, q.2 t)) ∧
    Matrix.trace (Matrix.of (fun (u v : (Fin n → α) × (Fin n → β)) =>
      ∏ t : Fin n, ρ (u.1 t, u.2 t) (v.1 t, v.2 t))) = (Matrix.trace ρ) ^ n := by
  refine ⟨rfl, ?_⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  let e : (Fin n → α) × (Fin n → β) ≃ (Fin n → α × β) :=
    { toFun := fun p t => (p.1 t, p.2 t)
      invFun := fun f => (fun t => (f t).1, fun t => (f t).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    ∑ p : (Fin n → α) × (Fin n → β), ∏ t : Fin n, ρ (p.1 t, p.2 t) (p.1 t, p.2 t)
      = ∑ f : Fin n → α × β, ∏ t : Fin n, ρ (f t) (f t) := by
          exact Fintype.sum_equiv e _ _ fun p => rfl
    _ = ∏ _t : Fin n, ∑ x : α × β, ρ x x := (Fintype.prod_sum (fun _ x => ρ x x)).symm
    _ = (∑ x : α × β, ρ x x) ^ n := by simp

/-- Every `n`-copy tensor power of a PPT state is PPT. -/
theorem ppl152_ppt_tensorPower_ppt {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {ρ : Matrix (α × β) (α × β) ℂ}
    (hppt : Matrix.PosSemidef (Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2)))) (n : ℕ) :
    Matrix.PosSemidef (Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
      ∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t))) := by
  have h1 := ppl152_tensorPower_posSemidef hppt n
  let e : (Fin n → α) × (Fin n → β) ≃ (Fin n → α × β) :=
    { toFun := fun p t => (p.1 t, p.2 t)
      invFun := fun f => (fun t => (f t).1, fun t => (f t).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [posSemidef_iff_isHermitian_re] at h1 ⊢
  refine ⟨?_, ?_⟩
  · ext ⟨a, b⟩ ⟨a', b'⟩
    have hH := congr_fun (congr_fun h1.1 (e (a, b))) (e (a', b'))
    simpa [Matrix.conjTranspose_apply, e] using hH
  · intro x
    let y : (Fin n → α × β) → ℂ := fun f => x (e.symm f)
    have heq : star x ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
          ∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ x =
        star y ⬝ᵥ Matrix.of (fun (p q : Fin n → α × β) =>
          ∏ t : Fin n, ρ ((p t).1, (q t).2) ((q t).1, (p t).2)) *ᵥ y := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Fintype.sum_equiv e _ _ fun p => ?_
      refine Fintype.sum_equiv e _ _ fun q => ?_
      simp [y, e]
    rw [heq]
    exact h1.2 y

/-- **Operational–Algebraic Distillability Equivalence (Horodecki 1998):**
For any Hermitian bipartite operator `M` on `α × β`, there exist local 2-qubit SLOCC filters
`A : Matrix α (Fin 2) ℂ` and `B : Matrix β (Fin 2) ℂ` such that the projected 2-qubit operator
`((A ⊗ B)ᴴ * M * (A ⊗ B))^{T_B}` is NOT positive semidefinite **if and only if** there exists a
Schmidt-rank-`≤ 2` vector `ψ = a₁ ⊗ b₁ + a₂ ⊗ b₂` with `(star ψ ⬝ᵥ M^{T_B} *ᵥ ψ).re < 0`. -/
theorem ppl152_slocc_2qubit_iff_schmidt_rank_two {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {M : Matrix (α × β) (α × β) ℂ} (hH : M.IsHermitian) :
    (∃ (A : Matrix α (Fin 2) ℂ) (B : Matrix β (Fin 2) ℂ),
      ¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin 2 × Fin 2) =>
        ((Matrix.of (fun (u : α × β) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))ᴴ * M *
         Matrix.of (fun (u : α × β) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))
        (p.1, q.2) (q.1, p.2))))
    ↔
    (∃ (a₁ a₂ : α → ℂ) (b₁ b₂ : β → ℂ),
      (star (fun u : α × β => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) ⬝ᵥ
        Matrix.of (fun (u v : α × β) => M (u.1, v.2) (v.1, u.2)) *ᵥ
        (fun u : α × β => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2)).re < 0) := by
  have hSLOCC : ∀ (A : Matrix α (Fin 2) ℂ) (B : Matrix β (Fin 2) ℂ) (v : Fin 2 × Fin 2 → ℂ),
      star v ⬝ᵥ
        Matrix.of (fun (p q : Fin 2 × Fin 2) =>
          ((Matrix.of (fun (u : α × β) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))ᴴ * M *
           Matrix.of (fun (u : α × β) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))
          (p.1, q.2) (q.1, p.2)) *ᵥ v =
      star (fun u : α × β => ∑ r : Fin 2 × Fin 2, A u.1 r.1 * star (B u.2 r.2) * v r) ⬝ᵥ
        Matrix.of (fun (u v' : α × β) => M (u.1, v'.2) (v'.1, u.2)) *ᵥ
        (fun u : α × β => ∑ r : Fin 2 × Fin 2, A u.1 r.1 * star (B u.2 r.2) * v r) := by
    intro A B v
    let K : Matrix (α × β) (Fin 2 × Fin 2) ℂ := Matrix.of (fun u r => A u.1 r.1 * B u.2 r.2)
    let L : Matrix (α × β) (Fin 2 × Fin 2) ℂ := Matrix.of (fun u r => A u.1 r.1 * star (B u.2 r.2))
    have hmat : Matrix.of (fun (p q : Fin 2 × Fin 2) => (Kᴴ * M * K) (p.1, q.2) (q.1, p.2)) =
        Lᴴ * Matrix.of (fun (u v' : α × β) => M (u.1, v'.2) (v'.1, u.2)) * L := by
      ext ⟨r, s⟩ ⟨u, w⟩
      simp only [K, L, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_mul',
        star_star, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc
        ∑ l : β, ∑ i : α, ∑ j : β,
            star (A i r) * star (B j w) * M (i, j) (k, l) * (A k u * B l s)
          = ∑ i : α, ∑ l : β, ∑ j : β,
              star (A i r) * star (B j w) * M (i, j) (k, l) * (A k u * B l s) := Finset.sum_comm
        _ = ∑ i : α, ∑ j : β, ∑ l : β,
              star (A i r) * star (B j w) * M (i, j) (k, l) * (A k u * B l s) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ j : β, ∑ i : α, ∑ l : β,
              star (A i r) * star (B j w) * M (i, j) (k, l) * (A k u * B l s) := Finset.sum_comm
        _ = ∑ j : β, ∑ i : α, ∑ l : β,
              star (A i r) * B l s * M (i, j) (k, l) * (A k u * star (B j w)) := by
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun l _ => by ring
    change star v ⬝ᵥ Matrix.of (fun (p q : Fin 2 × Fin 2) => (Kᴴ * M * K) (p.1, q.2) (q.1, p.2)) *ᵥ v = _
    rw [hmat]
    have hLv : (L *ᵥ v) = fun u : α × β => ∑ r : Fin 2 × Fin 2, A u.1 r.1 * star (B u.2 r.2) * v r := by
      ext u; rfl
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star, hLv]
  constructor
  · rintro ⟨A, B, hnpt⟩
    have hHerm : Matrix.IsHermitian (Matrix.of (fun (p q : Fin 2 × Fin 2) =>
        ((Matrix.of (fun (u : α × β) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))ᴴ * M *
         Matrix.of (fun (u : α × β) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))
        (p.1, q.2) (q.1, p.2))) := by
      refine ppl152_partialTranspose_isHermitian ?_
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
    rw [posSemidef_iff_isHermitian_re] at hnpt
    push Not at hnpt
    rcases hnpt hHerm with ⟨v, hv⟩
    rw [hSLOCC A B v] at hv
    refine ⟨fun i => A i 0, fun i => A i 1,
      fun j => ∑ s : Fin 2, star (B j s) * v (0, s),
      fun j => ∑ s : Fin 2, star (B j s) * v (1, s), ?_⟩
    have hvec : (fun u : α × β => ∑ r : Fin 2 × Fin 2, A u.1 r.1 * star (B u.2 r.2) * v r) =
        (fun u : α × β =>
          A u.1 0 * (∑ s : Fin 2, star (B u.2 s) * v (0, s)) +
          A u.1 1 * (∑ s : Fin 2, star (B u.2 s) * v (1, s))) := by
      ext ⟨i, j⟩
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
      ring
    rwa [hvec] at hv
  · rintro ⟨a₁, a₂, b₁, b₂, hneg⟩
    let A : Matrix α (Fin 2) ℂ := Matrix.of (fun i r => if r = 0 then a₁ i else a₂ i)
    let B : Matrix β (Fin 2) ℂ := Matrix.of (fun j s => if s = 0 then star (b₁ j) else star (b₂ j))
    refine ⟨A, B, fun hpsd => ?_⟩
    let v : Fin 2 × Fin 2 → ℂ := fun r => if r.1 = r.2 then 1 else 0
    have hnonneg := ((posSemidef_iff_isHermitian_re _).mp hpsd).2 v
    rw [hSLOCC A B v] at hnonneg
    have hvec : (fun u : α × β => ∑ r : Fin 2 × Fin 2, A u.1 r.1 * star (B u.2 r.2) * v r) =
        (fun u : α × β => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) := by
      ext ⟨i, j⟩
      simp [A, B, v, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hvec] at hnonneg
    linarith

/-- **Horodecki–Horodecki–Horodecki (1998) PPT Undistillability Theorem:**
Every PPT bipartite state (`PosSemidef ρ^{T_B}`) is `n`-copy undistillable for ALL `n : ℕ`:
both algebraically (nonnegative expectation on every Schmidt-rank-`≤ 2` vector on `n` copies)
and operationally (every 2-qubit SLOCC projection of `ρ^{⊗ n}` is PPT). -/
theorem ppl152_horodecki_ppt_undistillable {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {ρ : Matrix (α × β) (α × β) ℂ}
    (hppt : Matrix.PosSemidef (Matrix.of (fun (p q : α × β) => ρ (p.1, q.2) (q.1, p.2))))
    (n : ℕ) :
    (∀ (a₁ a₂ : (Fin n → α) → ℂ) (b₁ b₂ : (Fin n → β) → ℂ),
      0 ≤ (star (fun u : (Fin n → α) × (Fin n → β) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
          ∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ
        (fun u : (Fin n → α) × (Fin n → β) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2)).re) ∧
    (∀ (A : Matrix (Fin n → α) (Fin 2) ℂ) (B : Matrix (Fin n → β) (Fin 2) ℂ),
      Matrix.PosSemidef (Matrix.of (fun (p q : Fin 2 × Fin 2) =>
        ((Matrix.of (fun (u : (Fin n → α) × (Fin n → β)) (r : Fin 2 × Fin 2) =>
            A u.1 r.1 * B u.2 r.2))ᴴ *
         Matrix.of (fun (u v : (Fin n → α) × (Fin n → β)) =>
            ∏ t : Fin n, ρ (u.1 t, u.2 t) (v.1 t, v.2 t)) *
         Matrix.of (fun (u : (Fin n → α) × (Fin n → β)) (r : Fin 2 × Fin 2) =>
            A u.1 r.1 * B u.2 r.2))
        (p.1, q.2) (q.1, p.2)))) := by
  have hnppt := ppl152_ppt_tensorPower_ppt hppt n
  have h1 : ∀ (a₁ a₂ : (Fin n → α) → ℂ) (b₁ b₂ : (Fin n → β) → ℂ),
      0 ≤ (star (fun u : (Fin n → α) × (Fin n → β) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
          ∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ
        (fun u : (Fin n → α) × (Fin n → β) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2)).re :=
    fun a₁ a₂ b₁ b₂ => ((posSemidef_iff_isHermitian_re _).mp hnppt).2 _
  refine ⟨h1, fun A B => ?_⟩
  have hρH : ρ.IsHermitian := by
    have h2 := ppl152_partialTranspose_isHermitian hppt.isHermitian
    have hinv : Matrix.of (fun (p q : α × β) =>
        (Matrix.of (fun (u v : α × β) => ρ (u.1, v.2) (v.1, u.2))) (p.1, q.2) (q.1, p.2)) = ρ :=
      ppl152_partialTranspose_involutive ρ
    rwa [hinv] at h2
  have hnH : Matrix.IsHermitian (Matrix.of (fun (u v : (Fin n → α) × (Fin n → β)) =>
      ∏ t : Fin n, ρ (u.1 t, u.2 t) (v.1 t, v.2 t))) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hρH (a t, b t)) (a' t, b' t)
  by_contra hnot
  have hEx : ∃ (A : Matrix (Fin n → α) (Fin 2) ℂ) (B : Matrix (Fin n → β) (Fin 2) ℂ),
      ¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin 2 × Fin 2) =>
        ((Matrix.of (fun (u : (Fin n → α) × (Fin n → β)) (r : Fin 2 × Fin 2) =>
            A u.1 r.1 * B u.2 r.2))ᴴ *
         Matrix.of (fun (u v : (Fin n → α) × (Fin n → β)) =>
            ∏ t : Fin n, ρ (u.1 t, u.2 t) (v.1 t, v.2 t)) *
         Matrix.of (fun (u : (Fin n → α) × (Fin n → β)) (r : Fin 2 × Fin 2) =>
            A u.1 r.1 * B u.2 r.2))
        (p.1, q.2) (q.1, p.2))) := ⟨A, B, hnot⟩
  rcases (ppl152_slocc_2qubit_iff_schmidt_rank_two hnH).mp hEx with ⟨a₁, a₂, b₁, b₂, hneg⟩
  simp only [Matrix.of_apply] at hneg
  linarith [h1 a₁ a₂ b₁ b₂]

/-- **Copy-Monotonicity of Distillability:**
For any bipartite density matrix `ρ` (`ρ.PosSemidef`, `ρ.trace = 1`) and `n ≤ m`,
if `ρ` is `n`-copy distillable, then `ρ` is `m`-copy distillable. -/
theorem ppl152_distillable_monotone_copies {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ = 1)
    {n m : ℕ} (hnm : n ≤ m)
    (hdist : ∃ (a₁ a₂ : (Fin n → α) → ℂ) (b₁ b₂ : (Fin n → β) → ℂ),
      (star (fun u : (Fin n → α) × (Fin n → β) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
          ∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ
        (fun u : (Fin n → α) × (Fin n → β) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2)).re < 0) :
    ∃ (a₁' a₂' : (Fin m → α) → ℂ) (b₁' b₂' : (Fin m → β) → ℂ),
      (star (fun u : (Fin m → α) × (Fin m → β) => a₁' u.1 * b₁' u.2 + a₂' u.1 * b₂' u.2) ⬝ᵥ
        Matrix.of (fun (p q : (Fin m → α) × (Fin m → β)) =>
          ∏ t : Fin m, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ
        (fun u : (Fin m → α) × (Fin m → β) => a₁' u.1 * b₁' u.2 + a₂' u.1 * b₂' u.2)).re < 0 := by
  have hdiag : ∃ x₀ : α × β, 0 < (ρ x₀ x₀).re := by
    by_contra hall
    push Not at hall
    have hsum : (∑ x : α × β, (ρ x x).re) ≤ 0 := Finset.sum_nonpos fun x _ => hall x
    have htr_re : (Matrix.trace ρ).re = 1 := by rw [htr]; simp
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum] at htr_re
    linarith
  rcases hdiag with ⟨⟨i₀, j₀⟩, hpos⟩
  have him0 : (ρ (i₀, j₀) (i₀, j₀)).im = 0 := by
    have hH := congr_fun (congr_fun hρ.isHermitian (i₀, j₀)) (i₀, j₀)
    have h1 : (star (ρ (i₀, j₀) (i₀, j₀))).im = (ρ (i₀, j₀) (i₀, j₀)).im :=
      congr_arg Complex.im hH
    simp at h1
    linarith
  have hc_eq : ρ (i₀, j₀) (i₀, j₀) = ((ρ (i₀, j₀) (i₀, j₀)).re : ℂ) :=
    Complex.ext rfl (by simp [him0])
  rcases hdist with ⟨a₁, a₂, b₁, b₂, hneg⟩
  let restrictA : (Fin m → α) → (Fin n → α) := fun f t => f ⟨t.1, lt_of_lt_of_le t.2 hnm⟩
  let restrictB : (Fin m → β) → (Fin n → β) := fun f t => f ⟨t.1, lt_of_lt_of_le t.2 hnm⟩
  let tailA : (Fin m → α) → ℂ := fun f => if ∀ t : Fin m, n ≤ t.1 → f t = i₀ then 1 else 0
  let tailB : (Fin m → β) → ℂ := fun f => if ∀ t : Fin m, n ≤ t.1 → f t = j₀ then 1 else 0
  refine ⟨fun f => a₁ (restrictA f) * tailA f, fun f => a₂ (restrictA f) * tailA f,
    fun g => b₁ (restrictB g) * tailB g, fun g => b₂ (restrictB g) * tailB g, ?_⟩
  let ψn : (Fin n → α) × (Fin n → β) → ℂ := fun u => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2
  let ψm : (Fin m → α) × (Fin m → β) → ℂ := fun u =>
    a₁ (restrictA u.1) * tailA u.1 * (b₁ (restrictB u.2) * tailB u.2) +
    a₂ (restrictA u.1) * tailA u.1 * (b₂ (restrictB u.2) * tailB u.2)
  have hψm : ∀ u : (Fin m → α) × (Fin m → β),
      ψm u = if (∀ t : Fin m, n ≤ t.1 → u.1 t = i₀) ∧ (∀ t : Fin m, n ≤ t.1 → u.2 t = j₀)
        then ψn (restrictA u.1, restrictB u.2) else 0 := by
    rintro ⟨f, g⟩
    simp only [ψm, ψn, tailA, tailB]
    by_cases hf : ∀ t : Fin m, n ≤ t.1 → f t = i₀
    · by_cases hg : ∀ t : Fin m, n ≤ t.1 → g t = j₀
      · rw [if_pos hf, if_pos hg, if_pos ⟨hf, hg⟩]; ring
      · rw [if_pos hf, if_neg hg, if_neg (fun h => hg h.2)]; ring
    · rw [if_neg hf, if_neg (fun h : (∀ t : Fin m, n ≤ t.1 → f t = i₀) ∧
        (∀ t : Fin m, n ≤ t.1 → g t = j₀) => hf h.1)]
      ring
  let extA : (Fin n → α) → (Fin m → α) := fun f t => if h : t.1 < n then f ⟨t.1, h⟩ else i₀
  let extB : (Fin n → β) → (Fin m → β) := fun g t => if h : t.1 < n then g ⟨t.1, h⟩ else j₀
  have hcollapse : ∀ (F : (Fin m → α) × (Fin m → β) → ℂ),
      (∀ p, ¬ ((∀ t : Fin m, n ≤ t.1 → p.1 t = i₀) ∧ (∀ t : Fin m, n ≤ t.1 → p.2 t = j₀)) → F p = 0) →
      ∑ p : (Fin m → α) × (Fin m → β), F p =
      ∑ p : (Fin n → α) × (Fin n → β), F (extA p.1, extB p.2) := by
    intro F hF
    rw [← Finset.sum_filter_of_ne (p := fun x => (∀ t : Fin m, n ≤ t.1 → x.1 t = i₀) ∧
      (∀ t : Fin m, n ≤ t.1 → x.2 t = j₀)) (fun x _ hx => by
        by_contra hnot; exact hx (hF x hnot))]
    symm
    refine Finset.sum_nbij (fun p : (Fin n → α) × (Fin n → β) => (extA p.1, extB p.2))
      ?_ ?_ ?_ (fun _ _ => rfl)
    · intro p _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro t ht; simp [extA, not_lt.mpr ht]
      · intro t ht; simp [extB, not_lt.mpr ht]
    · rintro ⟨f₁, g₁⟩ _ ⟨f₂, g₂⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      ext t
      · have := congr_fun heq.1 ⟨t.1, lt_of_lt_of_le t.2 hnm⟩
        simpa [extA, t.2] using this
      · have := congr_fun heq.2 ⟨t.1, lt_of_lt_of_le t.2 hnm⟩
        simpa [extB, t.2] using this
    · intro p hp
      have hcond := (Finset.mem_filter.mp hp).2
      refine ⟨(restrictA p.1, restrictB p.2), Finset.mem_univ _, ?_⟩
      ext t
      · by_cases ht : t.1 < n
        · simp [extA, restrictA, ht]
        · simp [extA, ht, hcond.1 t (Nat.le_of_not_lt ht)]
      · by_cases ht : t.1 < n
        · simp [extB, restrictB, ht]
        · simp [extB, ht, hcond.2 t (Nat.le_of_not_lt ht)]
  have hfactor : star ψm ⬝ᵥ
      Matrix.of (fun (p q : (Fin m → α) × (Fin m → β)) =>
        ∏ t : Fin m, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψm =
      (star ψn ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → α) × (Fin n → β)) =>
          ∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψn) *
      (ρ (i₀, j₀) (i₀, j₀)) ^ (m - n) := by
    have houter : star ψm ⬝ᵥ
        Matrix.of (fun (p q : (Fin m → α) × (Fin m → β)) =>
          ∏ t : Fin m, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψm =
        ∑ p : (Fin m → α) × (Fin m → β), ∑ q : (Fin m → α) × (Fin m → β),
          star (ψm p) * ((∏ t : Fin m, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) * ψm q) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [houter, hcollapse _ (fun p hp => by
      have h0 : ψm p = 0 := by rw [hψm p]; exact if_neg hp
      simp [h0])]
    have hinner : ∀ p : (Fin n → α) × (Fin n → β),
        ∑ q : (Fin m → α) × (Fin m → β),
          star (ψm (extA p.1, extB p.2)) *
            ((∏ t : Fin m, ρ ((extA p.1) t, q.2 t) (q.1 t, (extB p.2) t)) * ψm q) =
        ∑ q : (Fin n → α) × (Fin n → β),
          star (ψn p) * ((∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) * ψn q) *
            (ρ (i₀, j₀) (i₀, j₀)) ^ (m - n) := by
      intro p
      rw [hcollapse _ (fun q hq => by
        have h0 : ψm q = 0 := by rw [hψm q]; exact if_neg hq
        simp [h0])]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hext_val : ∀ r : (Fin n → α) × (Fin n → β), ψm (extA r.1, extB r.2) = ψn r := by
        intro r
        rw [hψm]
        have hc : (∀ t : Fin m, n ≤ t.1 → extA r.1 t = i₀) ∧
            (∀ t : Fin m, n ≤ t.1 → extB r.2 t = j₀) :=
          ⟨fun t ht => by simp [extA, not_lt.mpr ht], fun t ht => by simp [extB, not_lt.mpr ht]⟩
        rw [if_pos hc]
        have hr1 : restrictA (extA r.1) = r.1 := by ext t; simp [restrictA, extA, t.2]
        have hr2 : restrictB (extB r.2) = r.2 := by ext t; simp [restrictB, extB, t.2]
        rw [hr1, hr2]
      have hprod : ∏ t : Fin m, ρ (extA p.1 t, extB q.2 t) (extA q.1 t, extB p.2 t) =
          (∏ t : Fin n, ρ (p.1 t, q.2 t) (q.1 t, p.2 t)) * (ρ (i₀, j₀) (i₀, j₀)) ^ (m - n) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun t : Fin m => t.1 < n)]
        congr 1
        · symm
          refine Finset.prod_nbij (fun t : Fin n => (⟨t.1, lt_of_lt_of_le t.2 hnm⟩ : Fin m))
            ?_ ?_ ?_ ?_
          · intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩
          · intro t₁ _ t₂ _ heq
            exact Fin.ext (by simpa using congr_arg Fin.val heq)
          · intro t ht
            have hlt : t.1 < n := (Finset.mem_filter.mp ht).2
            exact ⟨⟨t.1, hlt⟩, Finset.mem_univ _, rfl⟩
          · intro t _
            simp [extA, extB, t.2]
        · have hcard : (Finset.univ.filter (fun t : Fin m => ¬ t.1 < n)).card = m - n := by
            have hcompl := Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset (Fin m))) (p := fun t : Fin m => t.1 < n)
            have hlt_card : (Finset.univ.filter (fun t : Fin m => t.1 < n)).card =
                (Finset.univ : Finset (Fin n)).card := by
              symm
              refine Finset.card_nbij (fun t : Fin n => (⟨t.1, lt_of_lt_of_le t.2 hnm⟩ : Fin m))
                ?_ ?_ ?_
              · intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩
              · intro t₁ _ t₂ _ heq
                exact Fin.ext (by simpa using congr_arg Fin.val heq)
              · intro t ht
                exact ⟨⟨t.1, (Finset.mem_filter.mp ht).2⟩, Finset.mem_univ _, rfl⟩
            simp only [Finset.card_univ, Fintype.card_fin] at hcompl hlt_card
            omega
          calc
            ∏ t ∈ Finset.univ.filter (fun t : Fin m => ¬ t.1 < n),
                ρ (extA p.1 t, extB q.2 t) (extA q.1 t, extB p.2 t)
              = ∏ _t ∈ Finset.univ.filter (fun t : Fin m => ¬ t.1 < n), ρ (i₀, j₀) (i₀, j₀) := by
                  refine Finset.prod_congr rfl fun t ht => ?_
                  have hge : ¬ t.1 < n := (Finset.mem_filter.mp ht).2
                  simp [extA, extB, hge]
            _ = (ρ (i₀, j₀) (i₀, j₀)) ^ (m - n) := by rw [Finset.prod_const, hcard]
      rw [hext_val p, hext_val q, hprod]
      ring
    simp_rw [hinner, ← Finset.sum_mul]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  change (star ψm ⬝ᵥ _ *ᵥ ψm).re < 0
  rw [hfactor, hc_eq, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos hneg (pow_pos hpos (m - n))

/-! ### Section 3: Exact 1-Parameter Werner State Family `W_d(α)` (`d ≥ 2`) -/

/-- Exact positivity characterization of `I - α F` on `Fin d × Fin d` (`d ≥ 2`):
`PosSemidef (I - α • F) ↔ -1 ≤ α ∧ α ≤ 1`. -/
theorem ppl152_werner_posSemidef_iff {d : ℕ} (hd : 2 ≤ d) (α : ℝ) :
    Matrix.PosSemidef
      ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
       (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
         if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0)) ↔
    -1 ≤ α ∧ α ≤ 1 := by
  let F : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of (fun p q => if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0)
  have hH : ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • F).IsHermitian := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, F, Matrix.of_apply, map_sub, map_mul, Complex.star_def, Complex.conj_ofReal]
    have h1 : (starRingEnd ℂ) (if (k, l) = (i, j) then (1 : ℂ) else 0) =
        if (i, j) = (k, l) then 1 else 0 := by
      by_cases h : (i, j) = (k, l)
      · simp [h]
      · simp [h, Ne.symm h]
    have h2 : (starRingEnd ℂ) (if k = j ∧ l = i then (1 : ℂ) else 0) =
        if i = l ∧ j = k then 1 else 0 := by
      by_cases h : i = l ∧ j = k
      · rcases h with ⟨rfl, rfl⟩; simp
      · have h' : ¬ (k = j ∧ l = i) := fun ⟨hk, hl⟩ => h ⟨hl.symm, hk.symm⟩
        simp [h, h']
    rw [h1, h2]
  have hquad : ∀ x : Fin d × Fin d → ℂ,
      (star x ⬝ᵥ ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • F) *ᵥ x).re =
      (∑ p : Fin d × Fin d, ‖x p‖ ^ 2) -
      α * (∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)).re := by
    intro x
    have h1 : star x ⬝ᵥ ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • F) *ᵥ x =
        (∑ p : Fin d × Fin d, star (x p) * x p) -
        (α : ℂ) * (∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)) := by
      have hlin : ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • F) *ᵥ x =
          x - (α : ℂ) • (F *ᵥ x) := by
        ext p; simp [Matrix.sub_mulVec, Matrix.smul_mulVec]
      rw [hlin, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      congr 1
      · congr 1
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, F, Matrix.of_apply]
        refine Finset.sum_congr rfl fun ⟨i, j⟩ _ => ?_
        congr 1
        rw [Finset.sum_eq_single (j, i)]
        · simp
        · rintro ⟨k, l⟩ _ hne
          have hcond : ¬ (i = l ∧ j = k) := fun ⟨hi, hj⟩ => hne (Prod.ext hj.symm hi.symm)
          simp [hcond]
        · intro habs; exact absurd (Finset.mem_univ _) habs
    rw [h1, Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simp_rw [re_star_mul_self]
  rw [posSemidef_iff_isHermitian_re]
  constructor
  · rintro ⟨_, hre⟩
    have h0 : 0 < d := by omega
    have h1 : 1 < d := by omega
    let i0 : Fin d := ⟨0, h0⟩
    let i1 : Fin d := ⟨1, h1⟩
    have hne : i0 ≠ i1 := fun h => by
      have hv := congr_arg Fin.val h
      simp [i0, i1] at hv
    have hp : (i0, i1) ≠ (i1, i0) := fun h => hne (congr_arg Prod.fst h)
    constructor
    · -- Test antisymmetric vector |01⟩ - |10⟩
      let x : Fin d × Fin d → ℂ := fun p =>
        if p = (i0, i1) then 1 else if p = (i1, i0) then -1 else 0
      have hx := hre x
      rw [hquad x] at hx
      have hnorm : ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 = 2 := by
        rw [Finset.sum_eq_add (i0, i1) (i1, i0) hp]
        · simp [x, hp.symm]; norm_num
        · rintro p _ ⟨hp1, hp2⟩; simp [x, hp1, hp2]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro h; exact absurd (Finset.mem_univ _) h
      have hsw : (∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)).re = -2 := by
        have hsum : ∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1) = -2 := by
          rw [Finset.sum_eq_add (i0, i1) (i1, i0) hp]
          · simp [x, hp.symm]; norm_num
          · rintro p _ ⟨hp1, hp2⟩; simp [x, hp1, hp2]
          · intro h; exact absurd (Finset.mem_univ _) h
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum]; norm_num
      rw [hnorm, hsw] at hx
      linarith
    · -- Test symmetric vector |00⟩
      let x : Fin d × Fin d → ℂ := fun p => if p = (i0, i0) then 1 else 0
      have hx := hre x
      rw [hquad x] at hx
      have hnorm : ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single (i0, i0)]
        · simp [x]
        · intro p _ hp'; simp [x, hp']
        · intro h; exact absurd (Finset.mem_univ _) h
      have hsw : (∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)).re = 1 := by
        have hsum : ∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1) = 1 := by
          rw [Finset.sum_eq_single (i0, i0)]
          · simp [x]
          · intro p _ hp'; simp [x, hp']
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum]; norm_num
      rw [hnorm, hsw] at hx
      linarith
  · rintro ⟨hα1, hα2⟩
    refine ⟨hH, fun x => ?_⟩
    rw [hquad x]
    have hcs : |(∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)).re| ≤
        ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 := by
      have hswap_norm : ∑ p : Fin d × Fin d, ‖x (p.2, p.1)‖ ^ 2 =
          ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 := by
        let e : Fin d × Fin d ≃ Fin d × Fin d := Equiv.prodComm (Fin d) (Fin d)
        exact Fintype.sum_equiv e _ _ fun p => rfl
      have habs : |(∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)).re| ≤
          ‖∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)‖ :=
        Complex.abs_re_le_norm _
      have hsq := complex_cauchy_schwarz_sq (fun p : Fin d × Fin d => star (x p))
        (fun p : Fin d × Fin d => x (p.2, p.1))
      simp only [norm_star] at hsq
      rw [hswap_norm] at hsq
      have hnn : 0 ≤ ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 :=
        Finset.sum_nonneg fun p _ => sq_nonneg _
      have hnorm_le : ‖∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1)‖ ≤
          ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 := by
        nlinarith [norm_nonneg (∑ p : Fin d × Fin d, star (x p) * x (p.2, p.1))]
      exact le_trans habs hnorm_le
    have hlow := (abs_le.mp hcs).1
    have hhigh := (abs_le.mp hcs).2
    nlinarith

/-- **Exact Validity of the Werner State Family `W_d(α)` (`d ≥ 2`, `α ∈ [-1, 1]`):**
Every `W_d(α) = (d (d - α))⁻¹ (I - α F)` is Hermitian, positive semidefinite, and has trace `1`. -/
theorem ppl152_werner_isState {d : ℕ} (hd : 2 ≤ d) {α : ℝ} (hα1 : -1 ≤ α) (hα2 : α ≤ 1) :
    let W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
         (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
           if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0))
    W.IsHermitian ∧ W.PosSemidef ∧ Matrix.trace W = 1 := by
  intro W
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden_pos : 0 < (d : ℝ) * ((d : ℝ) - α) := by
    have _ := hα1
    nlinarith
  have hden_ne : ((d : ℂ) * ((d : ℂ) - (α : ℂ))) ≠ 0 := by
    exact_mod_cast ne_of_gt hden_pos
  have hpsd_raw := (ppl152_werner_posSemidef_iff hd α).mpr ⟨hα1, hα2⟩
  have hW_eq : W = ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) •
      ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
       (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
         if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0)) := by
    simp only [W]
    congr 1
    push_cast
    rfl
  have hpsd : W.PosSemidef := by
    rw [hW_eq]
    exact posSemidef_smul_real (inv_nonneg.mpr (le_of_lt hden_pos)) hpsd_raw
  refine ⟨hpsd.isHermitian, hpsd, ?_⟩
  have htr_F : Matrix.trace (Matrix.of (fun (p q : Fin d × Fin d) =>
      if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0)) = (d : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
    have hrow : ∀ i : Fin d, ∑ j : Fin d, (if i = j ∧ j = i then (1 : ℂ) else 0) = 1 := by
      intro i
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [hji]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp [hrow]
  have htr_1 : Matrix.trace (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) = (d : ℂ) * (d : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Fintype.card_prod]
  simp only [W, Matrix.trace_smul, Matrix.trace_sub, htr_1, htr_F, smul_eq_mul]
  have : (d : ℂ) * (d : ℂ) - (α : ℂ) * (d : ℂ) = (d : ℂ) * ((d : ℂ) - (α : ℂ)) := by ring
  rw [this, inv_mul_cancel₀ hden_ne]

/-- **Exact `U ⊗ U` Symmetry of Werner States:**
For every unitary `U : Matrix (Fin d) (Fin d) ℂ` (`U * Uᴴ = 1`), `W_d(α)` commutes with `U ⊗ U`,
i.e. `(U ⊗ U) * W_d(α) * (U ⊗ U)ᴴ = W_d(α)`. -/
theorem ppl152_werner_unitary_invariant {d : ℕ} (α : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U * Uᴴ = 1) :
    let K : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      Matrix.of (fun p q => U p.1 q.1 * U p.2 q.2)
    let W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
         (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
           if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0))
    K * W * Kᴴ = W := by
  intro K W
  have hU_entry : ∀ i k : Fin d, ∑ a : Fin d, U i a * star (U k a) = if i = k then 1 else 0 := by
    intro i k
    have h := congr_fun (congr_fun hU i) k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hKK : K * Kᴴ = 1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      star_mul', Fintype.sum_prod_type]
    calc
      ∑ a : Fin d, ∑ b : Fin d, U i a * U j b * (star (U k a) * star (U l b))
        = (∑ a : Fin d, U i a * star (U k a)) * (∑ b : Fin d, U j b * star (U l b)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
      _ = (if i = k then 1 else 0) * (if j = l then 1 else 0) := by rw [hU_entry, hU_entry]
      _ = if (i, j) = (k, l) then 1 else 0 := by
            by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj]
  let F : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of (fun p q => if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0)
  have hKFK : K * F * Kᴴ = F := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hKF : ∀ a b : Fin d, (K * F) (i, j) (a, b) = U i b * U j a := by
      intro a b
      simp only [K, F, Matrix.mul_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (b, a)]
      · simp
      · rintro ⟨x, y⟩ _ hne
        have : ¬ (x = b ∧ y = a) := fun ⟨hx, hy⟩ => hne (Prod.ext hx hy)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, hKF, K, Matrix.conjTranspose_apply,
      Matrix.of_apply, star_mul']
    calc
      ∑ a : Fin d, ∑ b : Fin d, U i b * U j a * (star (U k a) * star (U l b))
        = (∑ b : Fin d, U i b * star (U l b)) * (∑ a : Fin d, U j a * star (U k a)) := by
            rw [Finset.sum_comm, Finset.sum_mul]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
      _ = (if i = l then 1 else 0) * (if j = k then 1 else 0) := by rw [hU_entry, hU_entry]
      _ = F (i, j) (k, l) := by
            simp only [F, Matrix.of_apply]
            by_cases hi : i = l <;> by_cases hj : j = k <;> simp [hi, hj]
  change K * (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • F)) * Kᴴ =
    ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • F)
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    hKK, hKFK]

/-- **Exact Partial Transpose of the Werner State `W_d(α)`:**
`W_d(α)^{T_B} = (d (d - α))⁻¹ (I - α |Φ⁺⟩⟨Φ⁺|)`. -/
theorem ppl152_werner_partialTranspose_formula {d : ℕ} (α : ℝ) :
    Matrix.of (fun (p q : Fin d × Fin d) =>
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
         (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
           if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
      (p.1, q.2) (q.1, p.2)) =
    ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
      ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
       (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
         if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  congr 1
  have h1 : (if (i, l) = (k, j) then (1 : ℂ) else 0) = if (i, j) = (k, l) then 1 else 0 := by
    by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj, eq_comm]
  have h2 : (if i = j ∧ l = k then (1 : ℂ) else 0) = if i = j ∧ k = l then 1 else 0 := by
    by_cases h1' : i = j <;> by_cases h2' : k = l <;> simp [h1', h2', eq_comm]
  rw [h1, h2]

private lemma phiPlus_quad_re {d : ℕ} (α : ℝ) (x : Fin d × Fin d → ℂ) :
    (star x ⬝ᵥ
      ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
       (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
         if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)) *ᵥ x).re =
    (∑ p : Fin d × Fin d, ‖x p‖ ^ 2) - α * ‖∑ i : Fin d, x (i, i)‖ ^ 2 := by
  let P : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of (fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)
  have hP_eval : star x ⬝ᵥ P *ᵥ x =
      star (∑ i : Fin d, x (i, i)) * (∑ i : Fin d, x (i, i)) := by
    have hmul : ∀ i j : Fin d, (P *ᵥ x) (i, j) = if i = j then ∑ k : Fin d, x (k, k) else 0 := by
      intro i j
      simp only [Matrix.mulVec, dotProduct, P, Matrix.of_apply, Fintype.sum_prod_type]
      by_cases hij : i = j
      · simp only [hij, true_and, ↓reduceIte]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single k]
        · simp
        · intro l _ hlk; simp [Ne.symm hlk]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp [hij]
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, hmul]
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Ne.symm hji]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : star x ⬝ᵥ ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • P) *ᵥ x =
      (∑ p : Fin d × Fin d, star (x p) * x p) - (α : ℂ) * (star x ⬝ᵥ P *ᵥ x) := by
    have hlin : ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • P) *ᵥ x =
        x - (α : ℂ) • (P *ᵥ x) := by
      ext p; simp [Matrix.sub_mulVec, Matrix.smul_mulVec]
    rw [hlin, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rfl
  rw [h1, hP_eval, Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, re_star_mul_self]
  simp_rw [re_star_mul_self]

/-- **Exact PPT / NPT Threshold of Werner States `W_d(α)` (`d ≥ 2`, `α ∈ [-1, 1]`):**
`W_d(α)` is PPT (`PosSemidef W_d(α)^{T_B}`) **if and only if** `α ≤ 1 / d`. -/
theorem ppl152_werner_ppt_iff {d : ℕ} (hd : 2 ≤ d) {α : ℝ} (hα1 : -1 ≤ α) (hα2 : α ≤ 1) :
    Matrix.PosSemidef (Matrix.of (fun (p q : Fin d × Fin d) =>
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
         (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
           if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
      (p.1, q.2) (q.1, p.2))) ↔
    α ≤ (d : ℝ)⁻¹ := by
  rw [ppl152_werner_partialTranspose_formula]
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hden_pos : 0 < (d : ℝ) * ((d : ℝ) - α) := by
    have _ := hα1
    nlinarith
  let M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
    (α : ℂ) • Matrix.of (fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)
  have hM_H : M.IsHermitian := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [M, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, map_sub, map_mul, Complex.star_def,
      Complex.conj_ofReal]
    have h1 : (starRingEnd ℂ) (if (k, l) = (i, j) then (1 : ℂ) else 0) =
        if (i, j) = (k, l) then 1 else 0 := by
      by_cases h : (i, j) = (k, l) <;> simp [h, eq_comm]
    have h2 : (starRingEnd ℂ) (if k = l ∧ i = j then (1 : ℂ) else 0) =
        if i = j ∧ k = l then 1 else 0 := by
      by_cases h1' : i = j <;> by_cases h2' : k = l <;> simp [h1', h2']
    rw [h1, h2]
  have hscale : (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ • M).PosSemidef ↔ M.PosSemidef := by
    let denR : ℝ := (d : ℝ) * ((d : ℝ) - α)
    have hcast : ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ = ((denR⁻¹ : ℝ) : ℂ) := by
      simp only [denR]; push_cast; rfl
    rw [hcast]
    constructor
    · intro h
      have h2 := posSemidef_smul_real (le_of_lt hden_pos) h
      have hmul : ((denR : ℂ) * ((denR⁻¹ : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hden_pos), Complex.ofReal_one]
      rw [smul_smul, hmul, one_smul] at h2
      exact h2
    · exact posSemidef_smul_real (inv_nonneg.mpr (le_of_lt hden_pos))
  change (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ • M).PosSemidef ↔ _
  rw [hscale, posSemidef_iff_isHermitian_re]
  constructor
  · rintro ⟨_, hre⟩
    let φ : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
    have hφ := hre φ
    rw [phiPlus_quad_re α φ] at hφ
    have hsum1 : ∑ p : Fin d × Fin d, ‖φ p‖ ^ 2 = (d : ℝ) := by
      simp only [Fintype.sum_prod_type, φ]
      have hrow : ∀ i : Fin d, ∑ j : Fin d, ‖if i = j then (1 : ℂ) else 0‖ ^ 2 = 1 := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Ne.symm hji]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp [hrow]
    have hsum2 : ‖∑ i : Fin d, φ (i, i)‖ ^ 2 = (d : ℝ) ^ 2 := by
      simp [φ]
    rw [hsum1, hsum2] at hφ
    have hle : α * (d : ℝ) ≤ 1 := by nlinarith
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hd_pos).mpr hle
  · intro hαd
    refine ⟨hM_H, fun x => ?_⟩
    rw [phiPlus_quad_re α x]
    by_cases hα0 : α ≤ 0
    · have h1 : 0 ≤ ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : 0 ≤ -α * ‖∑ i : Fin d, x (i, i)‖ ^ 2 := by
        exact mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    · push Not at hα0
      have hcs := complex_cauchy_schwarz_sq (fun _ : Fin d => (1 : ℂ)) (fun i : Fin d => x (i, i))
      simp only [one_mul, norm_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at hcs
      have hdiag_le : ∑ i : Fin d, ‖x (i, i)‖ ^ 2 ≤ ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x (i, j)‖) (Finset.mem_univ i)
      have hαd_le : α * (d : ℝ) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hαd (le_of_lt hd_pos)
        rwa [inv_mul_cancel₀ (ne_of_gt hd_pos)] at this
      have hnn : 0 ≤ ∑ p : Fin d × Fin d, ‖x p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith

/-! ### Section 4: DCLB / DSS (2000) Exact 1-Copy Undistillability & `d = 2` vs `d ≥ 3` Dichotomy -/

/-- **Sharp Schmidt-Rank-`≤ 2` Overlap Bound with `|Φ⁺⟩`:**
For every dimension `d` and every Schmidt-rank-`≤ 2` vector `ψ = a₁ ⊗ b₁ + a₂ ⊗ b₂` on
`Fin d × Fin d`, `‖∑ i, ψ (i, i)‖² ≤ 2 ∑_{p} ‖ψ p‖²`. -/
theorem ppl152_schmidt_rank_two_phiPlus_bound {d : ℕ}
    (a₁ a₂ b₁ b₂ : Fin d → ℂ) :
    ‖∑ i : Fin d, (a₁ i * b₁ i + a₂ i * b₂ i)‖ ^ 2 ≤
    2 * ∑ p : Fin d × Fin d, ‖a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2‖ ^ 2 := by
  have h := schmidt_rank_two_partial_trace_bound (A := Fin d) (B := Unit)
    (fun p => a₁ p.1) (fun p => a₂ p.1) (fun p => b₁ p.1) (fun p => b₂ p.1)
  simp only [Fintype.sum_unique] at h
  have hrhs : ∑ p : Fin d × Unit, ∑ q : Fin d × Unit,
      ‖a₁ p.1 * b₁ q.1 + a₂ p.1 * b₂ q.1‖ ^ 2 =
      ∑ p : Fin d × Fin d, ‖a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2‖ ^ 2 := by
    simp [Fintype.sum_prod_type]
  rwa [hrhs] at h

/-- **Exact 1-Copy Undistillability Threshold of Werner States `W_d(α)` (`d ≥ 2`, `α ∈ [-1, 1]`):**
`W_d(α)` is 1-copy undistillable (`∀` Schmidt-rank-`≤ 2` `ψ`, `0 ≤ Re ⟨ψ | W_d(α)^{T_B} | ψ⟩`)
**if and only if** `α ≤ 1 / 2`. -/
theorem ppl152_werner_oneCopy_undistillable_iff {d : ℕ} (hd : 2 ≤ d)
    {α : ℝ} (hα1 : -1 ≤ α) (hα2 : α ≤ 1) :
    (∀ a₁ a₂ b₁ b₂ : Fin d → ℂ,
      0 ≤ (star (fun p : Fin d × Fin d => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2) ⬝ᵥ
        Matrix.of (fun (p q : Fin d × Fin d) =>
          (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
            ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
             (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
               if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
          (p.1, q.2) (q.1, p.2)) *ᵥ
        (fun p : Fin d × Fin d => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2)).re) ↔
    α ≤ 1 / 2 := by
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden_pos : 0 < (d : ℝ) * ((d : ℝ) - α) := by
    have _ := hα1
    nlinarith
  have hquad_W : ∀ x : Fin d × Fin d → ℂ,
      (star x ⬝ᵥ
        Matrix.of (fun (p q : Fin d × Fin d) =>
          (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
            ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
             (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
               if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
          (p.1, q.2) (q.1, p.2)) *ᵥ x).re =
      ((d : ℝ) * ((d : ℝ) - α))⁻¹ *
        ((∑ p : Fin d × Fin d, ‖x p‖ ^ 2) - α * ‖∑ i : Fin d, x (i, i)‖ ^ 2) := by
    intro x
    rw [ppl152_werner_partialTranspose_formula]
    have hsmul : star x ⬝ᵥ
        ((((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
           (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
             if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0))) *ᵥ x) =
        ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) *
        (star x ⬝ᵥ ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
           (α : ℂ) • Matrix.of (fun (p q : Fin d × Fin d) =>
             if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)) *ᵥ x) := by
      have hcast : ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ = ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) := by
        push_cast; rfl
      rw [hcast, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hsmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      phiPlus_quad_re]
  constructor
  · intro hall
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    have hne : i0 ≠ i1 := fun h => by
      have hv := congr_arg Fin.val h
      simp [i0, i1] at hv
    have hp : (i0, i0) ≠ (i1, i1) := fun h => hne (congr_arg Prod.fst h)
    let e0 : Fin d → ℂ := fun i => if i = i0 then 1 else 0
    let e1 : Fin d → ℂ := fun i => if i = i1 then 1 else 0
    have htest := hall e0 e1 e0 e1
    rw [hquad_W] at htest
    have hnorm : ∑ p : Fin d × Fin d, ‖e0 p.1 * e0 p.2 + e1 p.1 * e1 p.2‖ ^ 2 = 2 := by
      rw [Finset.sum_eq_add (i0, i0) (i1, i1) hp]
      · simp [e0, e1, hne, hne.symm]; norm_num
      · rintro ⟨i, j⟩ _ ⟨hp1, hp2⟩
        have h1 : e0 i * e0 j = 0 := by
          by_cases hi : i = i0 <;> by_cases hj : j = i0
          · exact absurd (Prod.ext hi hj) hp1
          · simp [e0, hj]
          · simp [e0, hi]
          · simp [e0, hi]
        have h2 : e1 i * e1 j = 0 := by
          by_cases hi : i = i1 <;> by_cases hj : j = i1
          · exact absurd (Prod.ext hi hj) hp2
          · simp [e1, hj]
          · simp [e1, hi]
          · simp [e1, hi]
        simp [h1, h2]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro h; exact absurd (Finset.mem_univ _) h
    have hphi : ‖∑ i : Fin d, (e0 i * e0 i + e1 i * e1 i)‖ ^ 2 = 4 := by
      have hsum : ∑ i : Fin d, (e0 i * e0 i + e1 i * e1 i) = (2 : ℂ) := by
        rw [Finset.sum_eq_add i0 i1 hne]
        · simp [e0, e1, hne, hne.symm]; norm_num
        · rintro i _ ⟨h1, h2⟩; simp [e0, e1, h1, h2]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]; norm_num
    rw [hnorm, hphi] at htest
    have hpos_inv : 0 < ((d : ℝ) * ((d : ℝ) - α))⁻¹ := inv_pos.mpr hden_pos
    have h2 : 0 ≤ 2 - α * 4 := by nlinarith
    linarith
  · intro hαhalf a₁ a₂ b₁ b₂
    rw [hquad_W]
    refine mul_nonneg (inv_nonneg.mpr (le_of_lt hden_pos)) ?_
    by_cases hα0 : α ≤ 0
    · have h1 : 0 ≤ ∑ p : Fin d × Fin d, ‖a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : 0 ≤ -α * ‖∑ i : Fin d, (a₁ i * b₁ i + a₂ i * b₂ i)‖ ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    · push Not at hα0
      have hbd := ppl152_schmidt_rank_two_phiPlus_bound a₁ a₂ b₁ b₂
      nlinarith

/-- **Sharp `d = 2` Dichotomy:**
In `d = 2` (two-qubit Werner states `W_2(α)`), the PPT threshold (`α = 1/2`) and the 1-copy
distillability threshold (`α = 1/2`) coincide: EVERY 2-qubit NPT Werner state is 1-copy
distillable! -/
theorem ppl152_werner_d2_npt_iff_oneCopy_distillable {α : ℝ} (hα1 : -1 ≤ α) (hα2 : α ≤ 1) :
    (¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin 2 × Fin 2) =>
      (((2 : ℂ) * ((2 : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
         (α : ℂ) • Matrix.of (fun (u v : Fin 2 × Fin 2) =>
           if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
      (p.1, q.2) (q.1, p.2)))) ↔
    (∃ a₁ a₂ b₁ b₂ : Fin 2 → ℂ,
      (star (fun p : Fin 2 × Fin 2 => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2) ⬝ᵥ
        Matrix.of (fun (p q : Fin 2 × Fin 2) =>
          (((2 : ℂ) * ((2 : ℂ) - (α : ℂ)))⁻¹ •
            ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
             (α : ℂ) • Matrix.of (fun (u v : Fin 2 × Fin 2) =>
               if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
          (p.1, q.2) (q.1, p.2)) *ᵥ
        (fun p : Fin 2 × Fin 2 => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2)).re < 0) := by
  have hppt := ppl152_werner_ppt_iff (d := 2) (le_refl 2) hα1 hα2
  have hund := ppl152_werner_oneCopy_undistillable_iff (d := 2) (le_refl 2) hα1 hα2
  have hcast : ((2 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
  have hcastC : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
  rw [hcast, hcastC] at hppt
  rw [hcastC] at hund
  constructor
  · intro hnpt
    have hnot_und : ¬ ∀ a₁ a₂ b₁ b₂ : Fin 2 → ℂ,
        0 ≤ (star (fun p : Fin 2 × Fin 2 => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2) ⬝ᵥ
          Matrix.of (fun (p q : Fin 2 × Fin 2) =>
            (((2 : ℂ) * ((2 : ℂ) - (α : ℂ)))⁻¹ •
              ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
               (α : ℂ) • Matrix.of (fun (u v : Fin 2 × Fin 2) =>
                 if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
            (p.1, q.2) (q.1, p.2)) *ᵥ
          (fun p : Fin 2 × Fin 2 => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2)).re := by
      intro h; exact hnpt (hppt.mpr (hund.mp h))
    push Not at hnot_und
    exact hnot_und
  · rintro ⟨a₁, a₂, b₁, b₂, hneg⟩ hppt'
    have hund' := hund.mpr (hppt.mp hppt')
    linarith [hund' a₁ a₂ b₁ b₂]

/-- **DCLB / DSS (2000) Continuous Family of Strictly NPT, 1-Copy Undistillable Werner States (`d ≥ 3`):**
For every dimension `d ≥ 3` and every `α` in the non-empty open-closed interval `(1 / d, 1 / 2]`,
the Werner state `W_d(α)` is:
1. A valid bipartite density matrix (`PosSemidef`, `trace = 1`),
2. **Strictly NPT** (`¬ PosSemidef W_d(α)^{T_B}`), hence **entangled** by Peres–Horodecki,
3. **Strictly 1-copy undistillable** (both algebraically on every Schmidt-rank-`≤ 2` vector and
   operationally on every 2-qubit SLOCC filter). -/
theorem ppl152_werner_d_ge_3_npt_oneCopy_undistillable {d : ℕ} (hd : 3 ≤ d)
    {α : ℝ} (hα_low : (d : ℝ)⁻¹ < α) (hα_high : α ≤ 1 / 2) :
    let W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
         (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
           if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0))
    W.PosSemidef ∧ Matrix.trace W = 1 ∧
    (¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin d × Fin d) => W (p.1, q.2) (q.1, p.2)))) ∧
    (∀ a₁ a₂ b₁ b₂ : Fin d → ℂ,
      0 ≤ (star (fun p : Fin d × Fin d => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2) ⬝ᵥ
        Matrix.of (fun (p q : Fin d × Fin d) => W (p.1, q.2) (q.1, p.2)) *ᵥ
        (fun p : Fin d × Fin d => a₁ p.1 * b₁ p.2 + a₂ p.1 * b₂ p.2)).re) ∧
    (∀ (A : Matrix (Fin d) (Fin 2) ℂ) (B : Matrix (Fin d) (Fin 2) ℂ),
      Matrix.PosSemidef (Matrix.of (fun (p q : Fin 2 × Fin 2) =>
        ((Matrix.of (fun (u : Fin d × Fin d) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))ᴴ * W *
         Matrix.of (fun (u : Fin d × Fin d) (r : Fin 2 × Fin 2) => A u.1 r.1 * B u.2 r.2))
        (p.1, q.2) (q.1, p.2)))) := by
  intro W
  have hd2 : 2 ≤ d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hα1 : -1 ≤ α := by
    have : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hd_pos
    linarith
  have hα2 : α ≤ 1 := by linarith
  have hst := ppl152_werner_isState hd2 hα1 hα2
  have hnpt : ¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin d × Fin d) => W (p.1, q.2) (q.1, p.2))) := by
    rw [ppl152_werner_ppt_iff hd2 hα1 hα2]
    linarith
  have hund := (ppl152_werner_oneCopy_undistillable_iff hd2 hα1 hα2).mpr hα_high
  refine ⟨hst.2.1, hst.2.2, hnpt, hund, fun A B => ?_⟩
  by_contra hnot
  rcases (ppl152_slocc_2qubit_iff_schmidt_rank_two hst.1).mp ⟨A, B, hnot⟩ with ⟨a₁, a₂, b₁, b₂, hneg⟩
  linarith [hund a₁ a₂ b₁ b₂]

/-! ### Section 5: Multi-Copy (`n ≥ 1`) Tensor-Power Undistillability & Exact DSS / KCIK #4 Barrier -/

private lemma subset_odd_sum_eq (n : ℕ) (α : ℝ) :
    2 * ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => Odd S.card), α ^ S.card =
    (1 + α) ^ n - (1 - α) ^ n := by
  have hplus : (1 + α) ^ n = ∑ S : Finset (Fin n), α ^ S.card := by
    calc
      (1 + α) ^ n = ∏ _t : Fin n, (α + 1) := by simp [add_comm]
      _ = ∑ S : Finset (Fin n), ∏ _t ∈ S, α := by
            simpa using (Finset.prod_add (fun _ : Fin n => α) (fun _ : Fin n => (1 : ℝ)) Finset.univ)
      _ = ∑ S : Finset (Fin n), α ^ S.card := by
            refine Finset.sum_congr rfl fun S _ => by simp
  have hminus : (1 - α) ^ n = ∑ S : Finset (Fin n), (-α) ^ S.card := by
    calc
      (1 - α) ^ n = ∏ _t : Fin n, ((-α) + 1) := by simp [sub_eq_add_neg, add_comm]
      _ = ∑ S : Finset (Fin n), ∏ _t ∈ S, (-α) := by
            simpa using (Finset.prod_add (fun _ : Fin n => -α) (fun _ : Fin n => (1 : ℝ)) Finset.univ)
      _ = ∑ S : Finset (Fin n), (-α) ^ S.card := by
            refine Finset.sum_congr rfl fun S _ => by simp
  rw [hplus, hminus, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset (Fin n) => Odd S.card)]
  have heven : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ Odd S.card),
      (α ^ S.card - (-α) ^ S.card) = 0 := by
    refine Finset.sum_eq_zero fun S hS => ?_
    have hev : Even S.card := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hS).2
    rw [hev.neg_pow, sub_self]
  have hodd : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Odd S.card),
      (α ^ S.card - (-α) ^ S.card) =
      2 * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Odd S.card), α ^ S.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have ho : Odd S.card := (Finset.mem_filter.mp hS).2
    rw [ho.neg_pow]
    ring
  rw [heven, add_zero, hodd]

/-- **Multi-Copy Subset-Projection Undistillability Criterion for Werner States:**
For every `n ≥ 1`, `d ≥ 2`, and `α ∈ [0, 1]` satisfying `(1 + α)^n - (1 - α)^n ≤ 1`,
the Werner state `W_d(α)` is unconditionally `n`-copy undistillable (nonnegative expectation on
every Schmidt-rank-`≤ 2` vector on `n` copies). -/
theorem ppl152_werner_nCopy_subset_undistillable {n d : ℕ} (hd : 2 ≤ d)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcond : (1 + α) ^ n - (1 - α) ^ n ≤ 1)
    (a₁ a₂ b₁ b₂ : (Fin n → Fin d) → ℂ) :
    0 ≤ (star (fun u : (Fin n → Fin d) × (Fin n → Fin d) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) ⬝ᵥ
      Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
        ∏ t : Fin n,
          (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
            ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
             (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
               if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
          (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ
      (fun u : (Fin n → Fin d) × (Fin n → Fin d) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2)).re := by
  let ψ : (Fin n → Fin d) × (Fin n → Fin d) → ℂ := fun u => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden_pos : 0 < (d : ℝ) * ((d : ℝ) - α) := by
    have _ := hα1
    nlinarith
  let M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
    (α : ℂ) • Matrix.of (fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)
  have hentry : ∀ (p q : (Fin n → Fin d) × (Fin n → Fin d)),
      (∏ t : Fin n,
        (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
           (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
             if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
        (p.1 t, q.2 t) (q.1 t, p.2 t)) =
      ((((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n : ℝ) : ℂ) *
      ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t) := by
    intro p q
    have hpt := ppl152_werner_partialTranspose_formula (d := d) α
    have hpt_at : ∀ t : Fin n,
        (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
           (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
             if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
        (p.1 t, q.2 t) (q.1 t, p.2 t) =
        ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) * M (p.1 t, p.2 t) (q.1 t, q.2 t) := by
      intro t
      have ht := congr_fun (congr_fun hpt (p.1 t, p.2 t)) (q.1 t, q.2 t)
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at ht ⊢
      rw [ht]
      simp only [M]
      push_cast
      rfl
    simp_rw [hpt_at, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rfl
  have hfactor_re : (star ψ ⬝ᵥ
      Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
        ∏ t : Fin n,
          (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
            ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
             (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
               if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
          (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψ).re =
      (((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n) *
      (star ψ ⬝ᵥ Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
        ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t)) *ᵥ ψ).re := by
    have hC : star ψ ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
          ∏ t : Fin n,
            (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
              ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
               (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
                 if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
            (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψ =
        ((((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n : ℝ) : ℂ) *
        (star ψ ⬝ᵥ Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
          ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t)) *ᵥ ψ) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, hentry, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hC, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 ≤ (star ψ ⬝ᵥ _ *ᵥ ψ).re
  rw [hfactor_re]
  refine mul_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hden_pos)) n) ?_
  let δI : (Fin d × Fin d) → (Fin d × Fin d) → ℂ := fun u v => if u = v then 1 else 0
  let δΦ : (Fin d × Fin d) → (Fin d × Fin d) → ℂ := fun u v =>
    if u.1 = u.2 ∧ v.1 = v.2 then 1 else 0
  let Q : Finset (Fin n) → ℝ := fun S =>
    (∑ p : (Fin n → Fin d) × (Fin n → Fin d), ∑ q : (Fin n → Fin d) × (Fin n → Fin d),
      star (ψ p) *
        ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
         (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q)).re
  have hexpand : (star ψ ⬝ᵥ Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
        ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t)) *ᵥ ψ).re =
      ∑ S : Finset (Fin n), (-α) ^ S.card * Q S := by
    have hprod_expand : ∀ p q : (Fin n → Fin d) × (Fin n → Fin d),
        ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t) =
        ∑ S : Finset (Fin n), ((-α : ℂ) ^ S.card) *
          ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
           (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t))) := by
      intro p q
      have hM_eq : ∀ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t) =
          (-α : ℂ) * δΦ (p.1 t, p.2 t) (q.1 t, q.2 t) + δI (p.1 t, p.2 t) (q.1 t, q.2 t) := by
        intro t
        simp only [M, δI, δΦ, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.of_apply]
        ring
      simp_rw [hM_eq]
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.sdiff_eq_inter_compl,
        Finset.univ_inter]
      ring
    have hC : star ψ ⬝ᵥ Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
        ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t)) *ᵥ ψ =
        ∑ S : Finset (Fin n), (((-α) ^ S.card : ℝ) : ℂ) *
          ∑ p : (Fin n → Fin d) × (Fin n → Fin d), ∑ q : (Fin n → Fin d) × (Fin n → Fin d),
            star (ψ p) *
              ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
               (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q) := by
      calc
        star ψ ⬝ᵥ Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
            ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t)) *ᵥ ψ
          = ∑ p, ∑ q, ∑ S : Finset (Fin n),
              (((-α) ^ S.card : ℝ) : ℂ) *
                (star (ψ p) * ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
                 (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q)) := by
              simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, hprod_expand,
                Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
                Finset.sum_congr rfl fun S _ => by push_cast; ring
        _ = ∑ p, ∑ S : Finset (Fin n), ∑ q,
              (((-α) ^ S.card : ℝ) : ℂ) *
                (star (ψ p) * ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
                 (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q)) := by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
        _ = ∑ S : Finset (Fin n), ∑ p, ∑ q,
              (((-α) ^ S.card : ℝ) : ℂ) *
                (star (ψ p) * ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
                 (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q)) := Finset.sum_comm
        _ = ∑ S : Finset (Fin n), (((-α) ^ S.card : ℝ) : ℂ) *
              ∑ p, ∑ q, star (ψ p) * ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
               (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q) := by
              refine Finset.sum_congr rfl fun S _ => by simp only [Finset.mul_sum]
    rw [hC, Complex.re_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hQ_eval : ∀ S : Finset (Fin n),
      0 ≤ Q S ∧ Q S ≤ 2 * ∑ p : (Fin n → Fin d) × (Fin n → Fin d), ‖ψ p‖ ^ 2 := by
    intro S
    let A := {t : Fin n // t ∈ S} → Fin d
    let B := {t : Fin n // t ∉ S} → Fin d
    let split : (Fin n → Fin d) ≃ A × B :=
      { toFun := fun f => (fun t => f t.1, fun t => f t.1)
        invFun := fun ab t => if h : t ∈ S then ab.1 ⟨t, h⟩ else ab.2 ⟨t, h⟩
        left_inv := fun f => funext fun t => by by_cases h : t ∈ S <;> simp [h]
        right_inv := fun ⟨a, b⟩ => Prod.ext
          (funext fun t => by simp [t.2])
          (funext fun t => by simp [t.2]) }
    have hsplit_eq : ∀ f g : Fin n → Fin d,
        (∀ t ∈ S, f t = g t) ↔ (split f).1 = (split g).1 := by
      intro f g
      constructor
      · intro h; exact funext fun ⟨t, ht⟩ => h t ht
      · intro h t ht; exact congr_fun h ⟨t, ht⟩
    have hsplit_compl : ∀ f g : Fin n → Fin d,
        (∀ t ∈ Sᶜ, f t = g t) ↔ (split f).2 = (split g).2 := by
      intro f g
      constructor
      · intro h; exact funext fun ⟨t, ht⟩ => h t (Finset.mem_compl.mpr ht)
      · intro h t ht; exact congr_fun h ⟨t, Finset.mem_compl.mp ht⟩
    have hprod_char : ∀ p q : (Fin n → Fin d) × (Fin n → Fin d),
        (∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
        (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) =
        if (split p.1).1 = (split p.2).1 ∧ (split q.1).1 = (split q.2).1 ∧
           (split p.1).2 = (split q.1).2 ∧ (split p.2).2 = (split q.2).2
        then 1 else 0 := by
      intro p q
      have hS_prod : ∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t) =
          if (split p.1).1 = (split p.2).1 ∧ (split q.1).1 = (split q.2).1 then 1 else 0 := by
        by_cases h : (split p.1).1 = (split p.2).1 ∧ (split q.1).1 = (split q.2).1
        · rw [if_pos h]
          refine Finset.prod_eq_one fun t ht => ?_
          have h1 := (hsplit_eq p.1 p.2).mpr h.1 t ht
          have h2 := (hsplit_eq q.1 q.2).mpr h.2 t ht
          simp [δΦ, h1, h2]
        · rw [if_neg h]
          have hex : ∃ t ∈ S, ¬ (p.1 t = p.2 t ∧ q.1 t = q.2 t) := by
            by_contra hall
            push Not at hall
            exact h ⟨(hsplit_eq p.1 p.2).mp fun t ht => (hall t ht).1,
              (hsplit_eq q.1 q.2).mp fun t ht => (hall t ht).2⟩
          rcases hex with ⟨t₀, ht₀, hne⟩
          refine Finset.prod_eq_zero ht₀ ?_
          simp [δΦ, hne]
      have hSc_prod : ∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t) =
          if (split p.1).2 = (split q.1).2 ∧ (split p.2).2 = (split q.2).2 then 1 else 0 := by
        by_cases h : (split p.1).2 = (split q.1).2 ∧ (split p.2).2 = (split q.2).2
        · rw [if_pos h]
          refine Finset.prod_eq_one fun t ht => ?_
          have h1 := (hsplit_compl p.1 q.1).mpr h.1 t ht
          have h2 := (hsplit_compl p.2 q.2).mpr h.2 t ht
          simp [δI, h1, h2]
        · rw [if_neg h]
          have hex : ∃ t ∈ Sᶜ, ¬ (p.1 t = q.1 t ∧ p.2 t = q.2 t) := by
            by_contra hall
            push Not at hall
            exact h ⟨(hsplit_compl p.1 q.1).mp fun t ht => (hall t ht).1,
              (hsplit_compl p.2 q.2).mp fun t ht => (hall t ht).2⟩
          rcases hex with ⟨t₀, ht₀, hne⟩
          refine Finset.prod_eq_zero ht₀ ?_
          have : (p.1 t₀, p.2 t₀) ≠ (q.1 t₀, q.2 t₀) := fun heq =>
            hne ⟨congr_arg Prod.fst heq, congr_arg Prod.snd heq⟩
          simp [δI, this]
      rw [hS_prod, hSc_prod]
      by_cases h1 : (split p.1).1 = (split p.2).1 ∧ (split q.1).1 = (split q.2).1 <;>
      by_cases h2 : (split p.1).2 = (split q.1).2 ∧ (split p.2).2 = (split q.2).2 <;>
      simp [h1, h2]
    let e2 : (Fin n → Fin d) × (Fin n → Fin d) ≃ (A × B) × (A × B) :=
      Equiv.prodCongr split split
    have hQ_eq : Q S = ∑ u : B, ∑ v : B,
        ‖∑ x : A, ψ (split.symm (x, u), split.symm (x, v))‖ ^ 2 := by
      have hC : ∑ p : (Fin n → Fin d) × (Fin n → Fin d),
          ∑ q : (Fin n → Fin d) × (Fin n → Fin d),
            star (ψ p) *
              ((∏ t ∈ S, δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
               (∏ t ∈ Sᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q) =
          ∑ u : B, ∑ v : B,
            star (∑ x : A, ψ (split.symm (x, u), split.symm (x, v))) *
            (∑ y : A, ψ (split.symm (y, u), split.symm (y, v))) := by
        simp_rw [hprod_char]
        trans ∑ p : (A × B) × (A × B), ∑ q : (A × B) × (A × B),
            star (ψ (split.symm p.1, split.symm p.2)) *
              ((if p.1.1 = p.2.1 ∧ q.1.1 = q.2.1 ∧ p.1.2 = q.1.2 ∧ p.2.2 = q.2.2 then (1 : ℂ) else 0) *
                ψ (split.symm q.1, split.symm q.2))
        · refine Fintype.sum_equiv e2 _ _ fun p => Fintype.sum_equiv e2 _ _ fun q => ?_
          simp [e2]
        · simp only [Fintype.sum_prod_type]
          trans ∑ x : A, ∑ u : B, ∑ v : B, ∑ y : A,
              star (ψ (split.symm (x, u), split.symm (x, v))) *
                ψ (split.symm (y, u), split.symm (y, v))
          · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sum_eq_single x]
            · refine Finset.sum_congr rfl fun v _ => ?_
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.sum_eq_single u]
              · rw [Finset.sum_eq_single y]
                · rw [Finset.sum_eq_single v]
                  · simp
                  · intro v' _ hv; simp [Ne.symm hv]
                  · intro h; exact absurd (Finset.mem_univ _) h
                · intro y' _ hy; simp [Ne.symm hy]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro u' _ hu; simp [Ne.symm hu]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro x' _ hx; simp [Ne.symm hx]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext u
              rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            rw [star_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
      simp only [Q]
      rw [hC, Complex.re_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun v _ => re_star_mul_self _
    rw [hQ_eq]
    refine ⟨Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _, ?_⟩
    have hbd := schmidt_rank_two_partial_trace_bound (A := A) (B := B)
      (fun ab => a₁ (split.symm ab)) (fun ab => a₂ (split.symm ab))
      (fun ab => b₁ (split.symm ab)) (fun ab => b₂ (split.symm ab))
    have hrhs : ∑ p : A × B, ∑ q : A × B,
        ‖a₁ (split.symm p) * b₁ (split.symm q) + a₂ (split.symm p) * b₂ (split.symm q)‖ ^ 2 =
        ∑ p : (Fin n → Fin d) × (Fin n → Fin d), ‖ψ p‖ ^ 2 := by
      have hprod : ∑ p : A × B, ∑ q : A × B,
          ‖a₁ (split.symm p) * b₁ (split.symm q) + a₂ (split.symm p) * b₂ (split.symm q)‖ ^ 2 =
          ∑ r : (A × B) × (A × B), ‖ψ (split.symm r.1, split.symm r.2)‖ ^ 2 :=
        (Fintype.sum_prod_type (fun r : (A × B) × (A × B) =>
          ‖ψ (split.symm r.1, split.symm r.2)‖ ^ 2)).symm
      rw [hprod]
      symm
      exact Fintype.sum_equiv e2 _ _ fun p => by simp [e2, ψ]
    rw [hrhs] at hbd
    exact hbd
  have hQ_empty : Q ∅ = ∑ p : (Fin n → Fin d) × (Fin n → Fin d), ‖ψ p‖ ^ 2 := by
    have hC : ∑ p : (Fin n → Fin d) × (Fin n → Fin d),
        ∑ q : (Fin n → Fin d) × (Fin n → Fin d),
          star (ψ p) *
            ((∏ t ∈ (∅ : Finset (Fin n)), δΦ (p.1 t, p.2 t) (q.1 t, q.2 t)) *
             (∏ t ∈ (∅ : Finset (Fin n))ᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q) =
        ∑ p : (Fin n → Fin d) × (Fin n → Fin d), star (ψ p) * ψ p := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_eq_single p]
      · simp [δI]
      · intro q _ hqp
        have hex : ∃ t : Fin n, (p.1 t, p.2 t) ≠ (q.1 t, q.2 t) := by
          by_contra hall
          push Not at hall
          apply hqp
          exact Prod.ext
            (funext fun t => (congr_arg Prod.fst (hall t)).symm)
            (funext fun t => (congr_arg Prod.snd (hall t)).symm)
        rcases hex with ⟨t₀, ht₀⟩
        have hzero : ∏ t ∈ (∅ : Finset (Fin n))ᶜ, δI (p.1 t, p.2 t) (q.1 t, q.2 t) = 0 :=
          Finset.prod_eq_zero (Finset.mem_compl.mpr (Finset.notMem_empty t₀)) (by simp [δI, ht₀])
        rw [hzero]
        simp
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [Q]
    rw [hC, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => re_star_mul_self _
  rw [hexpand]
  let Nψ : ℝ := ∑ p : (Fin n → Fin d) × (Fin n → Fin d), ‖ψ p‖ ^ 2
  have hNψ : 0 ≤ Nψ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset (Fin n) => Odd S.card)]
  have heven_ge : Nψ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ Odd S.card),
      (-α) ^ S.card * Q S := by
    have hmem : (∅ : Finset (Fin n)) ∈
        Finset.univ.filter (fun S : Finset (Fin n) => ¬ Odd S.card) := by
      simp
    have hsingle := Finset.single_le_sum (f := fun S : Finset (Fin n) => (-α) ^ S.card * Q S)
      (fun S hS => by
        have hev : Even S.card := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hS).2
        rw [hev.neg_pow]
        exact mul_nonneg (pow_nonneg hα0 _) (hQ_eval S).1)
      hmem
    simpa [hQ_empty, Nψ] using hsingle
  have hodd_ge : -((1 + α) ^ n - (1 - α) ^ n) * Nψ ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Odd S.card),
        (-α) ^ S.card * Q S := by
    rw [← subset_odd_sum_eq n α]
    have h1 : -(2 * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Odd S.card),
          α ^ S.card) * Nψ =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Odd S.card),
          -(α ^ S.card * (2 * Nψ)) := by
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
      ring
    rw [h1]
    refine Finset.sum_le_sum fun S hS => ?_
    have ho : Odd S.card := (Finset.mem_filter.mp hS).2
    rw [ho.neg_pow]
    have hle := (hQ_eval S).2
    have hαpow : 0 ≤ α ^ S.card := pow_nonneg hα0 _
    nlinarith
  nlinarith

/-- **Multi-Copy Watrous / DSS Phenomenon (`∀ n ≥ 1, ∃` Strictly NPT, `n`-Copy Undistillable States):**
For EVERY copy number `n ≥ 1`, EVERY local dimension `d > 3 * n`, and EVERY `α` in the non-empty
continuous interval `(1 / d, 1 / (3 * n)]`, the Werner state `W_d(α)` is:
1. A valid bipartite density matrix (`PosSemidef`, `trace = 1`),
2. **Strictly NPT** (`¬ PosSemidef W_d(α)^{T_B}`), hence **entangled**, AND
3. **Strictly `k`-copy undistillable for EVERY `1 ≤ k ≤ n`** (nonnegative expectation on every
   Schmidt-rank-`≤ 2` vector on `k` copies).

*Honest scope note:* This proves `∀ n ≥ 1, ∃ d, ∃ ρ, NPT(ρ) ∧ Undistillable_n(ρ)`. The open
KCIK #4 problem asks for the reversed quantifier order `∃ d, ∃ ρ, NPT(ρ) ∧ ∀ n ≥ 1, Undistillable_n(ρ)`. -/
theorem ppl152_nCopy_undistillable_npt_exists {n d : ℕ} (hn : 1 ≤ n) (hd : 3 * n < d)
    {α : ℝ} (hα_low : (d : ℝ)⁻¹ < α) (hα_high : α ≤ (3 * n : ℝ)⁻¹) :
    let W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      ((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
         (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
           if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0))
    W.PosSemidef ∧ Matrix.trace W = 1 ∧
    (¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin d × Fin d) => W (p.1, q.2) (q.1, p.2)))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ a₁ a₂ b₁ b₂ : (Fin k → Fin d) → ℂ,
        0 ≤ (star (fun u : (Fin k → Fin d) × (Fin k → Fin d) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2) ⬝ᵥ
          Matrix.of (fun (p q : (Fin k → Fin d) × (Fin k → Fin d)) =>
            ∏ t : Fin k, W (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ
          (fun u : (Fin k → Fin d) × (Fin k → Fin d) => a₁ u.1 * b₁ u.2 + a₂ u.1 * b₂ u.2)).re) := by
  intro W
  have hd2 : 2 ≤ d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hα0 : 0 ≤ α := le_of_lt (lt_trans (inv_pos.mpr hd_pos) hα_low)
  have hα1 : α ≤ 1 := by
    have h3n : (1 : ℝ) ≤ 3 * (n : ℝ) := by linarith
    have : (3 * (n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h3n
    linarith
  have hst := ppl152_werner_isState hd2 (by linarith) hα1
  have hnpt : ¬ Matrix.PosSemidef (Matrix.of (fun (p q : Fin d × Fin d) => W (p.1, q.2) (q.1, p.2))) := by
    rw [ppl152_werner_ppt_iff hd2 (by linarith) hα1]
    linarith
  refine ⟨hst.2.1, hst.2.2, hnpt, fun k _ hkn a₁ a₂ b₁ b₂ => ?_⟩
  have h3n_pos : (0 : ℝ) < 3 * (n : ℝ) := by linarith
  have hkα : (k : ℝ) * α ≤ 1 / 3 := by
    have hk_le : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have h3nα : 3 * (n : ℝ) * α ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hα_high (le_of_lt h3n_pos)
      rwa [mul_inv_cancel₀ (ne_of_gt h3n_pos)] at this
    nlinarith
  have hup := one_add_pow_le_one_add_two_mul hα0 k (by linarith)
  have hlo := one_sub_mul_le_one_sub_pow hα0 hα1 k
  have hcond : (1 + α) ^ k - (1 - α) ^ k ≤ 1 := by linarith
  exact ppl152_werner_nCopy_subset_undistillable hd2 hα0 hα1 hcond a₁ a₂ b₁ b₂

/-- **Exact `n`-Copy NPT Negative Sector & DSS Cancellation Barrier:**
1. For every `n ≥ 1`, `d ≥ 2`, and `α ∈ (1 / d, 1]`, the `n`-copy tensor power `W_d(α)^{⊗ n}` is
   strictly NPT (explicitly witnessed by `|Φ⁺⟩ ⊗ |01⟩^{⊗ (n - 1)}` with negative expectation
   `(1 - d α) / (d (d - α))^n < 0`).
2. For any fixed `α > 0`, the odd-subset bound `(1 + α)^n - (1 - α)^n` is unbounded as `n → ∞`,
   showing why dropping the positive even-`|S|` terms in `(I - α |Φ⁺⟩⟨Φ⁺|)^{⊗ n}` cannot by itself
   close the reversed-quantifier KCIK #4 problem (`∃ d, ∃ ρ, NPT(ρ) ∧ ∀ n ≥ 1, Undistillable_n(ρ)`). -/
theorem ppl152_werner_nCopy_negative_sector_and_barrier {d : ℕ} (hd : 2 ≤ d)
    {α : ℝ} (hα_low : (d : ℝ)⁻¹ < α) (hα_high : α ≤ 1) :
    (∀ n : ℕ, 1 ≤ n →
      ¬ Matrix.PosSemidef (Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
        ∏ t : Fin n,
          (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
            ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
             (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
               if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
          (p.1 t, q.2 t) (q.1 t, p.2 t)))) ∧
    (∀ B : ℝ, ∃ n : ℕ, B < (1 + α) ^ n - (1 - α) ^ n) := by
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hα_pos : 0 < α := lt_trans (inv_pos.mpr hd_pos) hα_low
  have hden_pos : 0 < (d : ℝ) * ((d : ℝ) - α) := by nlinarith
  have hdα_gt : 1 < (d : ℝ) * α := by
    have := mul_lt_mul_of_pos_left hα_low hd_pos
    rwa [mul_inv_cancel₀ (ne_of_gt hd_pos)] at this
  constructor
  · intro n hn hpsd
    let t0 : Fin n := ⟨0, by omega⟩
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    have hne : i0 ≠ i1 := fun h => by
      have hv := congr_arg Fin.val h
      simp [i0, i1] at hv
    let ψ : (Fin n → Fin d) × (Fin n → Fin d) → ℂ := fun p =>
      if p.1 t0 = p.2 t0 ∧ (∀ t : Fin n, t ≠ t0 → p.1 t = i0 ∧ p.2 t = i1) then 1 else 0
    have hnonneg := ((posSemidef_iff_isHermitian_re _).mp hpsd).2 ψ
    let M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
      (α : ℂ) • Matrix.of (fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0)
    have hpt := ppl152_werner_partialTranspose_formula (d := d) α
    have hpt_at : ∀ (u v : Fin d × Fin d),
        (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
           (α : ℂ) • Matrix.of (fun (a b : Fin d × Fin d) =>
             if a.1 = b.2 ∧ a.2 = b.1 then (1 : ℂ) else 0)))
        (u.1, v.2) (v.1, u.2) =
        ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) * M u v := by
      intro u v
      have ht := congr_fun (congr_fun hpt u) v
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at ht ⊢
      rw [ht]; simp only [M]; push_cast; rfl
    let embed : Fin d → (Fin n → Fin d) × (Fin n → Fin d) := fun c =>
      (fun t => if t = t0 then c else i0, fun t => if t = t0 then c else i1)
    have hcollapse : ∀ F : (Fin n → Fin d) × (Fin n → Fin d) → ℂ,
        (∀ p, ¬ (p.1 t0 = p.2 t0 ∧ ∀ t : Fin n, t ≠ t0 → p.1 t = i0 ∧ p.2 t = i1) → F p = 0) →
        ∑ p : (Fin n → Fin d) × (Fin n → Fin d), F p = ∑ c : Fin d, F (embed c) := by
      intro F hF
      rw [← Finset.sum_filter_of_ne (p := fun p => p.1 t0 = p.2 t0 ∧
        ∀ t : Fin n, t ≠ t0 → p.1 t = i0 ∧ p.2 t = i1)
        (fun p _ hp => by by_contra hnot; exact hp (hF p hnot))]
      symm
      refine Finset.sum_nbij embed ?_ ?_ ?_ (fun _ _ => rfl)
      · intro c _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · simp [embed]
        · intro t ht; simp [embed, ht]
      · intro c₁ _ c₂ _ heq
        have := congr_fun (congr_arg Prod.fst heq) t0
        simpa [embed] using this
      · intro p hp
        have hcond := (Finset.mem_filter.mp hp).2
        refine ⟨p.1 t0, Finset.mem_univ _, ?_⟩
        ext t
        · by_cases ht : t = t0
          · subst ht; simp [embed]
          · simp [embed, ht, (hcond.2 t ht).1]
        · by_cases ht : t = t0
          · subst ht; simp [embed, hcond.1]
          · simp [embed, ht, (hcond.2 t ht).2]
    have hM_01 : M (i0, i1) (i0, i1) = 1 := by
      simp [M, hne]
    have hM_diag : ∀ c₁ c₂ : Fin d, M (c₁, c₁) (c₂, c₂) = (if c₁ = c₂ then 1 else 0) - (α : ℂ) := by
      intro c₁ c₂
      simp only [M, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.of_apply, true_and, ↓reduceIte, mul_one]
      by_cases h : c₁ = c₂ <;> simp [h]
    have hval : star ψ ⬝ᵥ
        Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
          ∏ t : Fin n,
            (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
              ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
               (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
                 if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
            (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψ =
        ((((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n * ((d : ℝ) * (1 - (d : ℝ) * α)) : ℝ) : ℂ) := by
      have houter : star ψ ⬝ᵥ
          Matrix.of (fun (p q : (Fin n → Fin d) × (Fin n → Fin d)) =>
            ∏ t : Fin n,
              (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
                ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
                 (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
                   if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
              (p.1 t, q.2 t) (q.1 t, p.2 t)) *ᵥ ψ =
          ((((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n : ℝ) : ℂ) *
          ∑ p : (Fin n → Fin d) × (Fin n → Fin d), ∑ q : (Fin n → Fin d) × (Fin n → Fin d),
            star (ψ p) * ((∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t)) * ψ q) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        have hpr : ∏ t : Fin n,
            (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹ •
              ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
               (α : ℂ) • Matrix.of (fun (u v : Fin d × Fin d) =>
                 if u.1 = v.2 ∧ u.2 = v.1 then (1 : ℂ) else 0)))
            (p.1 t, q.2 t) (q.1 t, p.2 t) =
            ((((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n : ℝ) : ℂ) *
            ∏ t : Fin n, M (p.1 t, p.2 t) (q.1 t, q.2 t) := by
          simp_rw [hpt_at (p.1 _, p.2 _) (q.1 _, q.2 _), Finset.prod_mul_distrib,
            Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          push_cast; rfl
        rw [hpr]; ring
      rw [houter]
      rw [hcollapse _ (fun p hp => by simp [ψ, hp])]
      have hinner : ∀ c₁ : Fin d,
          ∑ q : (Fin n → Fin d) × (Fin n → Fin d),
            star (ψ (embed c₁)) *
              ((∏ t : Fin n, M ((embed c₁).1 t, (embed c₁).2 t) (q.1 t, q.2 t)) * ψ q) =
          1 - (d : ℂ) * (α : ℂ) := by
        intro c₁
        rw [hcollapse _ (fun q hq => by simp [ψ, hq])]
        have hψ_emb : ∀ c : Fin d, ψ (embed c) = 1 := by
          intro c
          have h1 : (embed c).1 t0 = (embed c).2 t0 := by simp [embed]
          have h2 : ∀ t : Fin n, t ≠ t0 → (embed c).1 t = i0 ∧ (embed c).2 t = i1 :=
            fun t ht => by simp [embed, ht]
          exact if_pos ⟨h1, h2⟩
        have hprod_emb : ∀ c₂ : Fin d,
            ∏ t : Fin n, M ((embed c₁).1 t, (embed c₁).2 t) ((embed c₂).1 t, (embed c₂).2 t) =
            (if c₁ = c₂ then 1 else 0) - (α : ℂ) := by
          intro c₂
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t0)]
          have hrest : ∏ t ∈ Finset.univ.erase t0,
              M ((embed c₁).1 t, (embed c₁).2 t) ((embed c₂).1 t, (embed c₂).2 t) = 1 := by
            refine Finset.prod_eq_one fun t ht => ?_
            have hne_t : t ≠ t0 := (Finset.mem_erase.mp ht).1
            simp [embed, hne_t, hM_01]
          rw [hrest, mul_one]
          simpa [embed] using hM_diag c₁ c₂
        simp_rw [hψ_emb, hprod_emb]
        simp [Finset.sum_sub_distrib]
      simp_rw [hinner]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [hval, Complex.ofReal_re] at hnonneg
    have hneg : ((d : ℝ) * ((d : ℝ) - α))⁻¹ ^ n * ((d : ℝ) * (1 - (d : ℝ) * α)) < 0 := by
      refine mul_neg_of_pos_of_neg (pow_pos (inv_pos.mpr hden_pos) n) ?_
      nlinarith
    linarith
  · intro B
    obtain ⟨n, hn⟩ := exists_nat_gt ((max B 0 + 1) / α)
    refine ⟨n, ?_⟩
    have hpow1 : 1 + (n : ℝ) * α ≤ (1 + α) ^ n := by
      simpa using one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ α) n
    have hpow2 : (1 - α) ^ n ≤ 1 := by
      have h0 : 0 ≤ 1 - α := by linarith
      have h1 : 1 - α ≤ 1 := by linarith
      exact pow_le_one₀ h0 h1
    have hgt : max B 0 + 1 < (n : ℝ) * α := (div_lt_iff₀ hα_pos).mp hn
    have hB : B ≤ max B 0 := le_max_left B 0
    linarith

end PPL152
