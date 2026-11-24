/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 145 (KCIK #1 — SIC-POVM Dimensions / Zauner's Conjecture):
# Gerzon Bound, Complex Projective 2-Design Tightness, Weyl–Heisenberg Covariance & Exact SIC-POVMs

## Honest Scope & Live 2026 Status
- **Problem Statement (KCIK #1, Golden KCIK Award `≈€2,026`, OPEN):**
  *Give an infinite sequence of dimensions with explicit symmetric informationally complete
  generalized quantum measurements (SIC-POVMs), or prove that only finitely many such dimensions
  exist.*
- **Zauner's Conjecture (1999, OPEN):** For every finite dimension `d ≥ 1`, there exists a
  Weyl–Heisenberg covariant SIC-POVM in `ℂ^d` (in fact with order-3 Zauner symmetry).
- **Honest Scope:** Neither Zauner's conjecture nor KCIK #1 (existence in infinitely many
  dimensions) is claimed solved here. Unconditional existence for infinitely many dimensions
  remains open (note: unrefereed preprint `arXiv:2601.13475` was explicitly flagged in its arXiv
  record as containing an incorrect proof).

## Formalized Results (`namespace PPL145`)
Every public theorem below has a **100% pure-Mathlib signature** (`0` custom or `private`
definitions referenced in any public theorem type), `0` `sorry`, `0` `native_decide`, `0` custom
axioms, and `leanchecker: PASS`:
1. **Gerzon Upper Bound (`ppl145_gerzon_upper_bound`):** Any `m` equiangular unit vectors in `ℂ^d`
   (`α < 1`) satisfy `m ≤ d^2`.
2. **1-Design & 2-Design Frame Potential Bounds and Welch Tightness:**
   `ppl145_frame_potential_one_design_bound`, `ppl145_welch_equiangular_lower_bound`,
   `ppl145_frame_potential_two_design_bound`, `ppl145_sic_povm_tightness_characterization`.
3. **Weyl–Heisenberg (`ZMod d`) & Multi-Qubit Pauli (`Fin n → ZMod 2`) Covariance Frameworks:**
   `ppl145_weyl_heisenberg_relations`, `ppl145_weyl_heisenberg_fiducial_generates_sic`,
   `ppl145_multiqubit_pauli_fiducial_generates_sic`.
4. **Explicit Kernel-Certified Exact SIC-POVMs (`0` `native_decide`):**
   - `d = 1` (`ppl145_sic_povm_dim1`),
   - `d = 2` tetrahedral Bloch Weyl–Heisenberg SIC (`ppl145_sic_povm_dim2`),
   - `d = 3` Hesse Weyl–Heisenberg SIC from `(0, 1, -1)/√2` (`ppl145_sic_povm_dim3`),
   - `d = 8` Hoggar 64-line 3-qubit Pauli SIC from `(1+i, 1, 1, 0, 1, 0, 0, i)/√6`
     (`ppl145_sic_povm_dim8_hoggar`),
   - Unified summary (`ppl145_sic_povm_exists_dims_1_2_3_8`).
-/

namespace PPL145

open scoped Matrix BigOperators ComplexConjugate

/-! ### Private Helpers: Rank-1 Projectors, Inner Products, and Hermitian Coordinates -/

private lemma norm_sq_eq_sum_norm_sq {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 = ∑ a : ι, ‖x a‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]

private lemma inner_eq_sum_star_mul {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    @inner ℂ _ _ x y = ∑ a : ι, star (x a) * y a := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_comm]

private lemma norm_sq_complex_eq_re_mul_star (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private def projMat {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => x a * star (x b)

private lemma projMat_isHermitian {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) :
    (projMat x).IsHermitian := by
  ext a b
  simp [projMat, Matrix.conjTranspose_apply, mul_comm]

private lemma trace_projMat {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) :
    (projMat x).trace = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, norm_sq_eq_sum_norm_sq]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag_apply, projMat, Matrix.of_apply]
  rw [← norm_sq_complex_eq_re_mul_star]
  push_cast; rfl

private lemma trace_projMat_mul_projMat {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    (projMat x * projMat y).trace = ((‖@inner ℂ _ _ x y‖ ^ 2 : ℝ) : ℂ) := by
  have hinner := inner_eq_sum_star_mul x y
  rw [norm_sq_complex_eq_re_mul_star, hinner]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, projMat, Matrix.of_apply]
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [star_mul', star_star]
  ring

private lemma trace_sq_hermitian_eq_sum_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (A * A).trace = ((∑ a : ι, ∑ b : ι, ‖A a b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hba : A b a = star (A a b) := by
    have := congr_fun (congr_fun hA b) a
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [hba, ← norm_sq_complex_eq_re_mul_star]
  push_cast; rfl

/-- Real-linear coordinate extraction `M_d(ℂ) →ₗ[ℝ] (Fin d × Fin d → ℝ)` injective on Hermitian
matrices: takes `Re(A_{a,b})` for `a ≤ b` and `Im(A_{a,b})` for `b < a`. -/
private noncomputable def hermCoords (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] (Fin d × Fin d → ℝ) where
  toFun A p := if p.1 ≤ p.2 then (A p.1 p.2).re else (A p.1 p.2).im
  map_add' A B := by
    ext ⟨a, b⟩
    by_cases h : a ≤ b <;> simp [h]
  map_smul' r A := by
    ext ⟨a, b⟩
    by_cases h : a ≤ b <;> simp [h]

private lemma hermCoords_inj_of_isHermitian {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (h0 : hermCoords d A = 0) : A = 0 := by
  ext a b
  have hconj : ∀ i j, A j i = star (A i j) := fun i j => by
    have := congr_fun (congr_fun hA j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  have hcoord : ∀ i j, (if i ≤ j then (A i j).re else (A i j).im) = 0 := fun i j => by
    have := congr_fun h0 (i, j)
    simpa [hermCoords] using this
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hre : (A a b).re = 0 := by simpa [le_of_lt hab] using hcoord a b
    have him' : (A b a).im = 0 := by simpa [not_le.mpr hab] using hcoord b a
    have him : (A a b).im = 0 := by
      have := congr_arg Complex.im (hconj a b)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext hre him
  · have hre : (A a a).re = 0 := by simpa using hcoord a a
    have him : (A a a).im = 0 := by
      have := congr_arg Complex.im (hconj a a)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext hre him
  · have hre' : (A b a).re = 0 := by simpa [le_of_lt hba] using hcoord b a
    have him : (A a b).im = 0 := by simpa [not_le.mpr hba] using hcoord a b
    have hre : (A a b).re = 0 := by
      have := congr_arg Complex.re (hconj b a)
      simp only [Complex.star_def, Complex.conj_re] at this
      linarith
    exact Complex.ext hre him

private lemma real_lincomb_isHermitian {d m : ℕ} (c : Fin m → ℝ)
    (P : Fin m → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, (P i).IsHermitian) :
    (∑ i : Fin m, (c i : ℝ) • P i).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := congr_fun (congr_fun (hP i) a) b
  simp only [Matrix.conjTranspose_apply, Complex.star_def] at hi
  rw [hi, mul_comm]

private lemma equiangular_projMat_linearIndependent {d m : ℕ} {α : ℝ}
    (hα : α < 1) (hα0 : 0 ≤ α)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hequi : ∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = α) :
    LinearIndependent ℝ (fun i : Fin m => hermCoords d (projMat (v i))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let S : Matrix (Fin d) (Fin d) ℂ := ∑ i : Fin m, (c i : ℝ) • projMat (v i)
  have hS_herm : S.IsHermitian := real_lincomb_isHermitian c (fun i => projMat (v i))
    (fun i => projMat_isHermitian (v i))
  have hS_coord : hermCoords d S = 0 := by
    simpa [S, map_sum, map_smul] using hc
  have hS_zero : S = 0 := hermCoords_inj_of_isHermitian hS_herm hS_coord
  have htr0 : ((S * S).trace).re = 0 := by simp [hS_zero]
  have htr_expand : (S * S).trace =
      (((1 - α) * (∑ i : Fin m, c i ^ 2) + α * (∑ i : Fin m, c i) ^ 2 : ℝ) : ℂ) := by
    have hmul : S * S = ∑ i : Fin m, ∑ j : Fin m,
        ((c i * c j : ℝ) : ℂ) • (projMat (v i) * projMat (v j)) := by
      simp only [S]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext a b
      simp only [Matrix.mul_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    rw [hmul, Matrix.trace_sum]
    simp_rw [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, trace_projMat_mul_projMat]
    have hpair : ∀ i j : Fin m,
        ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = (if i = j then 1 else α) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
        simp [hnorm i]
      · rw [if_neg hij, hequi i j hij]
    simp_rw [hpair]
    have hreal : ∑ i : Fin m, ∑ j : Fin m,
        ((c i * c j : ℝ) : ℂ) * (((if i = j then (1 : ℝ) else α) : ℝ) : ℂ) =
        ((∑ i : Fin m, ∑ j : Fin m, c i * c j * (if i = j then (1 : ℝ) else α) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hreal]
    congr 1
    have hsplit : ∀ i j : Fin m,
        c i * c j * (if i = j then (1 : ℝ) else α) =
        (if i = j then (1 - α) * (c i ^ 2) else 0) + α * (c i * c j) := by
      intro i j
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij]; ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hdiag : ∑ i : Fin m, ∑ j : Fin m, (if i = j then (1 - α) * c i ^ 2 else 0) =
        (1 - α) * ∑ i : Fin m, c i ^ 2 := by
      simp [Finset.mul_sum]
    have hoff : ∑ i : Fin m, ∑ j : Fin m, α * (c i * c j) = α * (∑ i : Fin m, c i) ^ 2 := by
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [hdiag, hoff]
  rw [htr_expand, Complex.ofReal_re] at htr0
  have hsum_sq_nonneg : 0 ≤ ∑ i : Fin m, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq_nonneg : 0 ≤ α * (∑ i : Fin m, c i) ^ 2 := mul_nonneg hα0 (sq_nonneg _)
  have h1α : 0 < 1 - α := sub_pos.mpr hα
  have hsum_sq_zero : ∑ i : Fin m, c i ^ 2 = 0 := by nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp hsum_sq_zero i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

/-! ## Part I: Gerzon Upper Bound & Complex Projective 1-Design / 2-Design Tightness -/

/-- **Gerzon's Upper Bound (`m ≤ d^2`):** Every collection of `m` equiangular unit vectors in `ℂ^d`
with pairwise squared overlap `α < 1` satisfies `m ≤ d^2`. -/
theorem ppl145_gerzon_upper_bound {d m : ℕ} {α : ℝ}
    (hα : α < 1)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hequi : ∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = α) :
    m ≤ d ^ 2 := by
  by_cases hm : m ≤ 1
  · by_cases hm0 : m = 0
    · omega
    · have hm1 : m = 1 := by omega
      subst hm1
      by_cases hd0 : d = 0
      · subst hd0
        have hv0 : v 0 = 0 := Subsingleton.elim _ _
        have h1 := hnorm 0
        rw [hv0, norm_zero] at h1
        norm_num at h1
      · exact Nat.one_le_pow 2 d (Nat.pos_of_ne_zero hd0)
  · have h2 : 2 ≤ m := by omega
    have hα0 : 0 ≤ α := by
      let i0 : Fin m := ⟨0, by omega⟩
      let i1 : Fin m := ⟨1, by omega⟩
      have hne : i0 ≠ i1 := by intro h; simp [i0, i1] at h
      rw [← hequi i0 i1 hne]
      exact sq_nonneg _
    have hli := equiangular_projMat_linearIndependent hα hα0 v hnorm hequi
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi, Fintype.card_prod] at hcard
    simpa [sq] using hcard

/-- **1-Design Frame Potential Bound & Tightness Characterization:** For any `m` unit vectors
in `ℂ^d` (`d > 0`), `∑_{i,j} ‖⟨v_i, v_j⟩‖^2 ≥ m^2 / d`, with equality if and only if the rank-1
projectors `v_i v_i^*` sum to `(m / d) I_d`. -/
theorem ppl145_frame_potential_one_design_bound {d m : ℕ} (hd : 0 < d)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1) :
    ((m : ℝ) ^ 2 / (d : ℝ) ≤ ∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2) ∧
    (∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = (m : ℝ) ^ 2 / (d : ℝ) ↔
      ∑ i : Fin m, Matrix.of (fun a b : Fin d => v i a * star (v i b)) =
        ((m : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  let P : Matrix (Fin d) (Fin d) ℂ := ∑ i : Fin m, projMat (v i)
  let c : ℝ := (m : ℝ) / (d : ℝ)
  let S : Matrix (Fin d) (Fin d) ℂ := P - (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
  have hP_herm : P.IsHermitian := by
    simpa [P] using real_lincomb_isHermitian (fun _ : Fin m => (1 : ℝ))
      (fun i => projMat (v i)) (fun i => projMat_isHermitian (v i))
  have hS_herm : S.IsHermitian := by
    ext a b
    have hPab := congr_fun (congr_fun hP_herm a) b
    simp only [Matrix.conjTranspose_apply, Complex.star_def] at hPab
    by_cases hab : a = b
    · subst hab
      simp [S, Matrix.conjTranspose_apply, hPab]
    · simp [S, Matrix.conjTranspose_apply, hab, Ne.symm hab, hPab]
  have htrP : P.trace = (m : ℂ) := by
    simp only [P, Matrix.trace_sum, trace_projMat, hnorm, one_pow, Complex.ofReal_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have htrPP : (P * P).trace =
      ((∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [P]
    rw [Finset.sum_mul, Matrix.trace_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [trace_projMat_mul_projMat]
    push_cast; rfl
  have htrSS : (S * S).trace =
      ((∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 - (m : ℝ) ^ 2 / (d : ℝ) : ℝ) : ℂ) := by
    have hSS : S * S = P * P - (2 * (c : ℂ)) • P + ((c : ℂ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      simp only [S, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_smul, two_mul, add_smul, sq]
      abel
    rw [hSS, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, htrPP, htrP, Matrix.trace_one, Fintype.card_fin]
    have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    push_cast [c]
    field_simp [hd_ne]
    ring
  have hnorm_id : ∑ a : Fin d, ∑ b : Fin d, ‖S a b‖ ^ 2 =
      ∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 - (m : ℝ) ^ 2 / (d : ℝ) := by
    have h1 := trace_sq_hermitian_eq_sum_norm_sq S hS_herm
    rw [htrSS] at h1
    exact Complex.ofReal_injective h1.symm
  have hnonneg : 0 ≤ ∑ a : Fin d, ∑ b : Fin d, ‖S a b‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  constructor
  · linarith
  · constructor
    · intro heq
      have hzero : ∑ a : Fin d, ∑ b : Fin d, ‖S a b‖ ^ 2 = 0 := by linarith
      have hS0 : S = 0 := by
        ext a b
        have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
          Finset.sum_nonneg fun j _ => sq_nonneg (‖S i j‖))).mp hzero a (Finset.mem_univ a)
        have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          sq_nonneg (‖S a j‖))).mp ha b (Finset.mem_univ b)
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
      have hPe : P = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := sub_eq_zero.mp hS0
      simpa [P, projMat, c] using hPe
    · intro hPe
      have hS0 : S = 0 := by
        apply sub_eq_zero.mpr
        simpa [P, projMat, c] using hPe
      have hzero : ∑ a : Fin d, ∑ b : Fin d, ‖S a b‖ ^ 2 = 0 := by simp [hS0]
      linarith

/-- **Welch's Equiangular Lower Bound:** For `m ≥ 2` equiangular unit vectors in `ℂ^d` (`d > 0`),
the common squared overlap satisfies `α ≥ (m - d) / (d (m - 1))`. -/
theorem ppl145_welch_equiangular_lower_bound {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) {α : ℝ}
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hequi : ∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = α) :
    ((m : ℝ) - (d : ℝ)) / ((d : ℝ) * ((m : ℝ) - 1)) ≤ α := by
  have h1 := (ppl145_frame_potential_one_design_bound hd v hnorm).1
  have hsum : ∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 =
      (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * α := by
    have hpair : ∀ i j : Fin m,
        ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = (if i = j then (1 : ℝ) else α) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
        simp [hnorm i]
      · rw [if_neg hij, hequi i j hij]
    simp_rw [hpair]
    have hinner_sum : ∀ i : Fin m,
        ∑ j : Fin m, (if i = j then (1 : ℝ) else α) = 1 + ((m : ℝ) - 1) * α := by
      intro i
      have hsplit : ∀ j : Fin m, (if i = j then (1 : ℝ) else α) =
          (if i = j then 1 - α else 0) + α := by
        intro j; by_cases hij : i = j <;> simp [hij]
      simp_rw [hsplit, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    simp_rw [hinner_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at h1
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmul := (div_le_iff₀ hd_pos).mp h1
  rw [div_le_iff₀ (mul_pos hd_pos hm1_pos)]
  nlinarith

/-- **Complex Projective 2-Design Frame Potential Bound & Exact Characterization:**
For any `m` unit vectors in `ℂ^d` (`d > 0`),
`∑_{i,j} ‖⟨v_i, v_j⟩‖^4 ≥ 2 m^2 / (d (d + 1))`,
with equality if and only if the vectors satisfy the exact symmetric-subspace 2-design tensor
identity `∑_i (v_i)_a (v_i)_b conj((v_i)_c) conj((v_i)_e) = (m / (d(d+1))) (δ_{ac}δ_{be} + δ_{ae}δ_{bc})`. -/
theorem ppl145_frame_potential_two_design_bound {d m : ℕ} (hd : 0 < d)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1) :
    ((2 * (m : ℝ) ^ 2) / ((d : ℝ) * ((d : ℝ) + 1)) ≤
      ∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4) ∧
    (∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 =
      (2 * (m : ℝ) ^ 2) / ((d : ℝ) * ((d : ℝ) + 1)) ↔
      ∀ a b c e : Fin d,
        ∑ i : Fin m, v i a * v i b * star (v i c) * star (v i e) =
          ((m : ℂ) / ((d : ℂ) * ((d : ℂ) + 1))) *
            ((if a = c ∧ b = e then (1 : ℂ) else 0) +
             (if a = e ∧ b = c then (1 : ℂ) else 0))) := by
  let A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of fun p q => ∑ i : Fin m, v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2)
  let Psym : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of fun p q =>
      ((1 : ℂ) / 2) * ((if p.1 = q.1 ∧ p.2 = q.2 then 1 else 0) +
                       (if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0))
  let c : ℝ := (2 * (m : ℝ)) / ((d : ℝ) * ((d : ℝ) + 1))
  let T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := A - (c : ℂ) • Psym
  have hA_herm : A.IsHermitian := by
    ext ⟨a, b⟩ ⟨e, f⟩
    simp only [A, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hPsym_herm : Psym.IsHermitian := by
    ext ⟨a, b⟩ ⟨e, f⟩
    simp only [Psym, Matrix.conjTranspose_apply, Matrix.of_apply]
    have h1 : (e = a ∧ f = b) ↔ (a = e ∧ b = f) := by tauto
    have h2 : (e = b ∧ f = a) ↔ (a = f ∧ b = e) := by tauto
    simp [h1, h2]
  have hT_herm : T.IsHermitian := by
    ext p q
    have hA_pq := congr_fun (congr_fun hA_herm p) q
    have hP_pq := congr_fun (congr_fun hPsym_herm p) q
    simp only [Matrix.conjTranspose_apply] at hA_pq hP_pq
    simp [T, Matrix.conjTranspose_apply, hA_pq, hP_pq]
  have htrAA : (A * A).trace =
      ((∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 : ℝ) : ℂ) := by
    have h4 : ∀ i j : Fin m, ((‖@inner ℂ _ _ (v i) (v j)‖ : ℂ) ^ 4) =
        (@inner ℂ _ _ (v i) (v j) * star (@inner ℂ _ _ (v i) (v j))) ^ 2 := by
      intro i j
      have h2 := norm_sq_complex_eq_re_mul_star (@inner ℂ _ _ (v i) (v j))
      have h2' : ((‖@inner ℂ _ _ (v i) (v j)‖ : ℂ) ^ 2) =
          @inner ℂ _ _ (v i) (v j) * star (@inner ℂ _ _ (v i) (v j)) := by
        simpa using h2
      rw [← h2']; ring
    have hterm : ∀ i j : Fin m,
        ((‖@inner ℂ _ _ (v i) (v j)‖ : ℂ) ^ 4) =
        ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
          (v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2)) *
          (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) := by
      intro i j
      rw [h4, inner_eq_sum_star_mul]
      have hfactor :
          ((∑ a : Fin d, star (v i a) * v j a) * star (∑ a : Fin d, star (v i a) * v j a)) ^ 2 =
          (∑ c : Fin d, v i c * star (v j c)) *
          ((∑ e : Fin d, v i e * star (v j e)) *
          ((∑ a : Fin d, star (v i a) * v j a) * (∑ b : Fin d, star (v i b) * v j b))) := by
        have hst : star (∑ a : Fin d, star (v i a) * v j a) = ∑ a : Fin d, v i a * star (v j a) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [mul_comm]
        rw [hst]; ring
      rw [hfactor]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring
    push_cast
    simp_rw [hterm]
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, A, Matrix.of_apply]
    have hmul_expand : ∀ p q : Fin d × Fin d,
        (∑ i : Fin m, v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2)) *
        (∑ j : Fin m, v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) =
        ∑ i : Fin m, ∑ j : Fin m,
          v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2) *
            (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) := by
      intro p q
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    simp_rw [hmul_expand]
    calc ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, ∑ i : Fin m, ∑ j : Fin m,
            v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2) *
              (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2))
        = ∑ p : Fin d × Fin d, ∑ i : Fin m, ∑ q : Fin d × Fin d, ∑ j : Fin m,
            v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2) *
              (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ i : Fin m, ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, ∑ j : Fin m,
            v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2) *
              (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) := Finset.sum_comm
      _ = ∑ i : Fin m, ∑ p : Fin d × Fin d, ∑ j : Fin m, ∑ q : Fin d × Fin d,
            v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2) *
              (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
            v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2) *
              (v j q.1 * v j q.2 * star (v j p.1) * star (v j p.2)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have htrAP : (A * Psym).trace = (m : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, A, Psym, Matrix.of_apply]
    have hinner : ∀ p : Fin d × Fin d,
        ∑ q : Fin d × Fin d,
          (∑ i : Fin m, v i p.1 * v i p.2 * star (v i q.1) * star (v i q.2)) *
          ((1 : ℂ) / 2 * ((if q.1 = p.1 ∧ q.2 = p.2 then 1 else 0) +
                          (if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0))) =
        ∑ i : Fin m, v i p.1 * v i p.2 * star (v i p.1) * star (v i p.2) := by
      intro ⟨a, b⟩
      have hsum1 : ∑ q : Fin d × Fin d,
          (∑ i : Fin m, v i a * v i b * star (v i q.1) * star (v i q.2)) *
            ((1 : ℂ) / 2 * (if q.1 = a ∧ q.2 = b then 1 else 0)) =
          ((1 : ℂ) / 2) * ∑ i : Fin m, v i a * v i b * star (v i a) * star (v i b) := by
        rw [Finset.sum_eq_single (a, b)]
        · simp [mul_comm]
        · intro ⟨q1, q2⟩ _ hne
          have : ¬(q1 = a ∧ q2 = b) := by intro ⟨h1, h2⟩; exact hne (Prod.ext h1 h2)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hsum2 : ∑ q : Fin d × Fin d,
          (∑ i : Fin m, v i a * v i b * star (v i q.1) * star (v i q.2)) *
            ((1 : ℂ) / 2 * (if q.1 = b ∧ q.2 = a then 1 else 0)) =
          ((1 : ℂ) / 2) * ∑ i : Fin m, v i a * v i b * star (v i a) * star (v i b) := by
        rw [Finset.sum_eq_single (b, a)]
        · simp only [true_and, ↓reduceIte, mul_one]
          rw [mul_comm]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
        · intro ⟨q1, q2⟩ _ hne
          have : ¬(q1 = b ∧ q2 = a) := by intro ⟨h1, h2⟩; exact hne (Prod.ext h1 h2)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      calc ∑ q : Fin d × Fin d,
              (∑ i : Fin m, v i a * v i b * star (v i q.1) * star (v i q.2)) *
                ((1 : ℂ) / 2 * ((if q.1 = a ∧ q.2 = b then 1 else 0) +
                                (if q.1 = b ∧ q.2 = a then 1 else 0)))
          = ∑ q : Fin d × Fin d,
              ((∑ i : Fin m, v i a * v i b * star (v i q.1) * star (v i q.2)) *
                ((1 : ℂ) / 2 * (if q.1 = a ∧ q.2 = b then 1 else 0)) +
               (∑ i : Fin m, v i a * v i b * star (v i q.1) * star (v i q.2)) *
                ((1 : ℂ) / 2 * (if q.1 = b ∧ q.2 = a then 1 else 0))) := by
            refine Finset.sum_congr rfl fun q _ => by ring
        _ = _ := by rw [Finset.sum_add_distrib, hsum1, hsum2]; ring
    simp_rw [hinner]
    rw [Finset.sum_comm]
    have hvi : ∀ i : Fin m,
        ∑ p : Fin d × Fin d, v i p.1 * v i p.2 * star (v i p.1) * star (v i p.2) = 1 := by
      intro i
      rw [Fintype.sum_prod_type]
      have hfactor : ∀ a b : Fin d,
          v i a * v i b * star (v i a) * star (v i b) =
          (v i a * star (v i a)) * (v i b * star (v i b)) := fun a b => by ring
      simp_rw [hfactor, ← Finset.mul_sum, ← Finset.sum_mul]
      have h1 : ∑ a : Fin d, v i a * star (v i a) = 1 := by
        have htr := trace_projMat (v i)
        simpa [Matrix.trace, projMat, hnorm i] using htr
      rw [h1, mul_one]
    simp_rw [hvi]
    simp
  have htrPA : (Psym * A).trace = (m : ℂ) := by
    rw [Matrix.trace_mul_comm, htrAP]
  have hPsym_idem : Psym * Psym = Psym := by
    ext ⟨a, b⟩ ⟨e, f⟩
    simp only [Matrix.mul_apply, Psym, Matrix.of_apply]
    have hsplit : ∀ q : Fin d × Fin d,
        ((1 : ℂ) / 2 * ((if a = q.1 ∧ b = q.2 then 1 else 0) +
                        (if a = q.2 ∧ b = q.1 then 1 else 0))) *
        ((1 : ℂ) / 2 * ((if q.1 = e ∧ q.2 = f then 1 else 0) +
                        (if q.1 = f ∧ q.2 = e then 1 else 0))) =
        ((1 : ℂ) / 4) *
          ((if a = q.1 ∧ b = q.2 then 1 else 0) * ((if q.1 = e ∧ q.2 = f then 1 else 0) +
                                                   (if q.1 = f ∧ q.2 = e then 1 else 0)) +
           (if a = q.2 ∧ b = q.1 then 1 else 0) * ((if q.1 = e ∧ q.2 = f then 1 else 0) +
                                                   (if q.1 = f ∧ q.2 = e then 1 else 0))) := fun q => by ring
    simp_rw [hsplit, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hs1 : ∑ q : Fin d × Fin d,
        (if a = q.1 ∧ b = q.2 then (1 : ℂ) else 0) *
          ((if q.1 = e ∧ q.2 = f then 1 else 0) + (if q.1 = f ∧ q.2 = e then 1 else 0)) =
        (if a = e ∧ b = f then 1 else 0) + (if a = f ∧ b = e then 1 else 0) := by
      rw [Finset.sum_eq_single (a, b)]
      · simp
      · intro ⟨q1, q2⟩ _ hne
        have : ¬(a = q1 ∧ b = q2) := by intro ⟨h1, h2⟩; exact hne (Prod.ext h1.symm h2.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hs2 : ∑ q : Fin d × Fin d,
        (if a = q.2 ∧ b = q.1 then (1 : ℂ) else 0) *
          ((if q.1 = e ∧ q.2 = f then 1 else 0) + (if q.1 = f ∧ q.2 = e then 1 else 0)) =
        (if a = e ∧ b = f then 1 else 0) + (if a = f ∧ b = e then 1 else 0) := by
      rw [Finset.sum_eq_single (b, a)]
      · simp only [true_and, ↓reduceIte, one_mul]
        have h1 : (b = e ∧ a = f) ↔ (a = f ∧ b = e) := by tauto
        have h2 : (b = f ∧ a = e) ↔ (a = e ∧ b = f) := by tauto
        simp [h1, h2, add_comm]
      · intro ⟨q1, q2⟩ _ hne
        have : ¬(a = q2 ∧ b = q1) := by intro ⟨h1, h2⟩; exact hne (Prod.ext h2.symm h1.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hs1, hs2]; ring
  have htrP : Psym.trace = ((d : ℂ) * ((d : ℂ) + 1)) / 2 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Psym, Matrix.of_apply, true_and, ↓reduceIte]
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have h1 : ∑ _ : Fin d × Fin d, (1 : ℂ) = (d : ℂ) * (d : ℂ) := by
      simp [Fintype.card_prod]
    have h2 : ∑ p : Fin d × Fin d, (if p.1 = p.2 ∧ p.2 = p.1 then (1 : ℂ) else 0) = (d : ℂ) := by
      rw [Fintype.sum_prod_type]
      have : ∀ a b : Fin d, (if a = b ∧ b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 := by
        intro a b; by_cases h : a = b <;> simp [h]
      simp [this]
    rw [h1, h2]; ring
  have htrTT : (T * T).trace =
      ((∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 -
        (2 * (m : ℝ) ^ 2) / ((d : ℝ) * ((d : ℝ) + 1)) : ℝ) : ℂ) := by
    have hTT : T * T = A * A - (c : ℂ) • (A * Psym) - (c : ℂ) • (Psym * A) + ((c : ℂ) ^ 2) • Psym := by
      simp only [T, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPsym_idem, sq]
      abel
    rw [hTT, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, htrAA, htrAP, htrPA, htrP]
    have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hd1_ne : (d : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    push_cast [c]
    field_simp [hd_ne, hd1_ne]
    ring
  have hnorm_id : ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, ‖T p q‖ ^ 2 =
      ∑ i : Fin m, ∑ j : Fin m, ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 -
        (2 * (m : ℝ) ^ 2) / ((d : ℝ) * ((d : ℝ) + 1)) := by
    have h1 := trace_sq_hermitian_eq_sum_norm_sq T hT_herm
    rw [htrTT] at h1
    exact Complex.ofReal_injective h1.symm
  have hnonneg : 0 ≤ ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, ‖T p q‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _
  constructor
  · linarith
  · constructor
    · intro heq a b c' e
      have hzero : ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, ‖T p q‖ ^ 2 = 0 := by linarith
      have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
        Finset.sum_nonneg fun q _ => sq_nonneg (‖T p q‖))).mp hzero (a, b) (Finset.mem_univ _)
      have hq := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ =>
        sq_nonneg (‖T (a, b) q‖))).mp hp (c', e) (Finset.mem_univ _)
      have hT0 : T (a, b) (c', e) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hq)
      have hAe : A (a, b) (c', e) = (c : ℂ) * Psym (a, b) (c', e) := by
        simpa [T, sub_eq_zero] using hT0
      simp only [A, Psym, Matrix.of_apply, c] at hAe
      push_cast at hAe
      rw [hAe]; ring
    · intro h2des
      have hT0 : T = 0 := by
        ext ⟨a, b⟩ ⟨c', e⟩
        simp only [T, A, Psym, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
          Matrix.zero_apply, smul_eq_mul, c]
        rw [h2des a b c' e]
        push_cast; ring
      have hzero : ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, ‖T p q‖ ^ 2 = 0 := by simp [hT0]
      linarith

/-- **SIC-POVM Tightness & Complex Projective 2-Design Theorem:**
If `d^2` equiangular unit vectors exist in `ℂ^d` (`d ≥ 2`, common squared overlap `α < 1`), then:
1. `α = 1 / (d + 1)` (forced equality in the Welch bound),
2. `(1 / d) ∑_i v_i v_i^* = I_d` (exact POVM resolution of the identity / tight 1-design),
3. `∑_{i,j} ‖⟨v_i, v_j⟩‖^2 = d^3` (exact minimal 1-design frame potential),
4. `∑_{i,j} ‖⟨v_i, v_j⟩‖^4 = 2 d^3 / (d + 1)` (exact minimal 2-design frame potential),
5. `v` satisfies the exact complex projective 2-design symmetric tensor identity. -/
theorem ppl145_sic_povm_tightness_characterization {d : ℕ} (hd : 2 ≤ d) {α : ℝ}
    (hα : α < 1)
    (v : Fin (d ^ 2) → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hequi : ∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = α) :
    (α = 1 / ((d : ℝ) + 1)) ∧
    (((1 : ℂ) / (d : ℂ)) •
      ∑ i : Fin (d ^ 2), Matrix.of (fun a b : Fin d => v i a * star (v i b)) =
        (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
    (∑ i : Fin (d ^ 2), ∑ j : Fin (d ^ 2), ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = (d : ℝ) ^ 3) ∧
    (∑ i : Fin (d ^ 2), ∑ j : Fin (d ^ 2), ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 =
      (2 * (d : ℝ) ^ 3) / ((d : ℝ) + 1)) ∧
    (∀ a b c e : Fin d,
      ∑ i : Fin (d ^ 2), v i a * v i b * star (v i c) * star (v i e) =
        ((d : ℂ) / ((d : ℂ) + 1)) *
          ((if a = c ∧ b = e then (1 : ℂ) else 0) +
           (if a = e ∧ b = c then (1 : ℂ) else 0))) := by
  have hd_pos : 0 < d := by omega
  have hα0 : 0 ≤ α := by
    let i0 : Fin (d ^ 2) := ⟨0, by nlinarith⟩
    let i1 : Fin (d ^ 2) := ⟨1, by nlinarith⟩
    have hne : i0 ≠ i1 := by intro h; simp [i0, i1] at h
    rw [← hequi i0 i1 hne]
    exact sq_nonneg _
  have hli := equiangular_projMat_linearIndependent hα hα0 v hnorm hequi
  have htop : Submodule.span ℝ (Set.range (fun i : Fin (d ^ 2) => hermCoords d (projMat (v i)))) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli]
    simp [Fintype.card_prod, sq]
  have hmem : hermCoords d (1 : Matrix (Fin d) (Fin d) ℂ) ∈
      Submodule.span ℝ (Set.range (fun i : Fin (d ^ 2) => hermCoords d (projMat (v i)))) := by
    rw [htop]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  rcases hmem with ⟨c, hc⟩
  have hI_eq : ∑ i : Fin (d ^ 2), (c i : ℝ) • projMat (v i) = (1 : Matrix (Fin d) (Fin d) ℂ) := by
    apply sub_eq_zero.mp
    apply hermCoords_inj_of_isHermitian
    · have h1 := real_lincomb_isHermitian c (fun i => projMat (v i)) (fun i => projMat_isHermitian (v i))
      ext a b
      have h1ab := congr_fun (congr_fun h1 a) b
      simp only [Matrix.conjTranspose_apply] at h1ab
      by_cases hab : a = b
      · subst hab; simp [Matrix.conjTranspose_apply, h1ab]
      · simp [Matrix.conjTranspose_apply, hab, Ne.symm hab, h1ab]
    · simp only [map_sub, map_sum, map_smul, hc, sub_self]
  have htr_j : ∀ j : Fin (d ^ 2), (1 : ℝ) = (1 - α) * c j + α * ∑ i : Fin (d ^ 2), c i := by
    intro j
    have hmul : projMat (v j) * (∑ i : Fin (d ^ 2), (c i : ℝ) • projMat (v i)) = projMat (v j) := by
      rw [hI_eq, Matrix.mul_one]
    have htr := congr_arg Matrix.trace hmul
    rw [trace_projMat, hnorm j, one_pow, Complex.ofReal_one, Finset.mul_sum, Matrix.trace_sum] at htr
    have hterm : ∀ i : Fin (d ^ 2),
        (projMat (v j) * (c i : ℝ) • projMat (v i)).trace =
        (c i : ℂ) * (((if j = i then (1 : ℝ) else α) : ℝ) : ℂ) := by
      intro i
      have hsm : projMat (v j) * (c i : ℝ) • projMat (v i) =
          (c i : ℂ) • (projMat (v j) * projMat (v i)) := by
        ext a b
        simp only [Matrix.mul_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsm, Matrix.trace_smul, smul_eq_mul, trace_projMat_mul_projMat]
      by_cases hij : j = i
      · subst hij; rw [if_pos rfl, inner_self_eq_norm_sq_to_K]; simp [hnorm j]
      · rw [if_neg hij, hequi j i hij]
    simp_rw [hterm] at htr
    have htr_re := congr_arg Complex.re htr
    have hre_sum : (∑ i : Fin (d ^ 2), (c i : ℂ) * (((if j = i then (1 : ℝ) else α) : ℝ) : ℂ)).re =
        ∑ i : Fin (d ^ 2), c i * (if j = i then (1 : ℝ) else α) := by
      have : ∑ i : Fin (d ^ 2), (c i : ℂ) * (((if j = i then (1 : ℝ) else α) : ℝ) : ℂ) =
          ((∑ i : Fin (d ^ 2), c i * (if j = i then (1 : ℝ) else α) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [this, Complex.ofReal_re]
    rw [hre_sum, Complex.one_re] at htr_re
    have hsplit : ∀ i : Fin (d ^ 2),
        c i * (if j = i then (1 : ℝ) else α) = (if j = i then (1 - α) * c i else 0) + α * c i := by
      intro i; by_cases hij : j = i <;> simp [hij] <;> ring
    simp_rw [hsplit] at htr_re
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ j),
      ← Finset.mul_sum] at htr_re
    exact htr_re.symm
  have hsum_c : ∑ i : Fin (d ^ 2), c i = (d : ℝ) := by
    have htr := congr_arg Matrix.trace hI_eq
    rw [Matrix.trace_one, Fintype.card_fin, Matrix.trace_sum] at htr
    have htr_i : ∀ i : Fin (d ^ 2), ((c i : ℝ) • projMat (v i)).trace = (c i : ℂ) := by
      intro i
      have hsm : (c i : ℝ) • projMat (v i) = (c i : ℂ) • projMat (v i) := by
        ext a b; simp [Complex.real_smul]
      rw [hsm, Matrix.trace_smul, smul_eq_mul, trace_projMat, hnorm i]
      simp
    simp_rw [htr_i] at htr
    have : ∑ i : Fin (d ^ 2), (c i : ℂ) = ((∑ i : Fin (d ^ 2), c i : ℝ) : ℂ) := by push_cast; rfl
    rw [this] at htr
    exact Complex.ofReal_injective htr
  have hc_const : ∀ j : Fin (d ^ 2), c j = 1 / (d : ℝ) := by
    have h1α : (1 - α) ≠ 0 := (sub_pos.mpr hα).ne'
    have h0 : ∀ j₁ j₂ : Fin (d ^ 2), c j₁ = c j₂ := by
      intro j₁ j₂
      have h1 := htr_j j₁
      have h2 := htr_j j₂
      have hdiff : (1 - α) * (c j₁ - c j₂) = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left h1α)
    intro j
    have hsum' : ∑ i : Fin (d ^ 2), c i = (d ^ 2 : ℝ) * c j := by
      have : ∀ i : Fin (d ^ 2), c i = c j := fun i => h0 i j
      simp [this, sq]
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    rw [hsum_c] at hsum'
    have hfac : (d : ℝ) * (c j * (d : ℝ) - 1) = 0 := by nlinarith
    have hcj : c j * (d : ℝ) = 1 := by linarith [(mul_eq_zero.mp hfac).resolve_left hd_ne]
    field_simp [hd_ne]
    exact hcj
  have hα_eq : α = 1 / ((d : ℝ) + 1) := by
    let j0 : Fin (d ^ 2) := ⟨0, by nlinarith⟩
    have h1 := htr_j j0
    rw [hc_const j0, hsum_c] at h1
    have hd_pos_r : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
    have hd1_pos_r : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have hd_gt1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
    have hmul : (d : ℝ) = (1 - α) + α * (d : ℝ) ^ 2 := by
      have := congr_arg (· * (d : ℝ)) h1
      field_simp [hd_pos_r.ne'] at this
      linarith
    have hfac : (α * ((d : ℝ) + 1) - 1) * ((d : ℝ) - 1) = 0 := by nlinarith
    have hαd1 : α * ((d : ℝ) + 1) = 1 := by
      have hne : (d : ℝ) - 1 ≠ 0 := by linarith
      linarith [(mul_eq_zero.mp hfac).resolve_right hne]
    field_simp [hd1_pos_r.ne']
    linarith
  have hPOVM : ((1 : ℂ) / (d : ℂ)) •
      ∑ i : Fin (d ^ 2), Matrix.of (fun a b : Fin d => v i a * star (v i b)) =
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
    have hI' : ∑ i : Fin (d ^ 2), (((1 : ℝ) / (d : ℝ)) : ℂ) • projMat (v i) = 1 := by
      convert hI_eq using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc_const i]
      ext a b
      simp [Complex.real_smul]
    rw [← Finset.smul_sum] at hI'
    simpa [projMat] using hI'
  have hpair : ∀ i j : Fin (d ^ 2),
      ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = (if i = j then (1 : ℝ) else 1 / ((d : ℝ) + 1)) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, inner_self_eq_norm_sq_to_K]; simp [hnorm i]
    · rw [if_neg hij, hequi i j hij, hα_eq]
  have hd1_ne : (d : ℝ) + 1 ≠ 0 := by positivity
  have hfp1 : ∑ i : Fin (d ^ 2), ∑ j : Fin (d ^ 2), ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = (d : ℝ) ^ 3 := by
    simp_rw [hpair]
    have hinner : ∀ i : Fin (d ^ 2),
        ∑ j : Fin (d ^ 2), (if i = j then (1 : ℝ) else 1 / ((d : ℝ) + 1)) = (d : ℝ) := by
      intro i
      have hsplit : ∀ j : Fin (d ^ 2),
          (if i = j then (1 : ℝ) else 1 / ((d : ℝ) + 1)) =
          (if i = j then 1 - 1 / ((d : ℝ) + 1) else 0) + 1 / ((d : ℝ) + 1) := by
        intro j; by_cases hij : i = j <;> simp [hij]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp [hd1_ne]
      ring
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hfp2 : ∑ i : Fin (d ^ 2), ∑ j : Fin (d ^ 2), ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 =
      (2 * (d : ℝ) ^ 3) / ((d : ℝ) + 1) := by
    have hpair4 : ∀ i j : Fin (d ^ 2),
        ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 =
        (if i = j then (1 : ℝ) else (1 / ((d : ℝ) + 1)) ^ 2) := by
      intro i j
      have h2 := hpair i j
      have : ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 = (‖@inner ℂ _ _ (v i) (v j)‖ ^ 2) ^ 2 := by ring
      rw [this, h2]
      by_cases hij : i = j <;> simp [hij]
    simp_rw [hpair4]
    have hinner : ∀ i : Fin (d ^ 2),
        ∑ j : Fin (d ^ 2), (if i = j then (1 : ℝ) else (1 / ((d : ℝ) + 1)) ^ 2) =
          (2 * (d : ℝ)) / ((d : ℝ) + 1) := by
      intro i
      have hsplit : ∀ j : Fin (d ^ 2),
          (if i = j then (1 : ℝ) else (1 / ((d : ℝ) + 1)) ^ 2) =
          (if i = j then 1 - (1 / ((d : ℝ) + 1)) ^ 2 else 0) + (1 / ((d : ℝ) + 1)) ^ 2 := by
        intro j; by_cases hij : i = j <;> simp [hij]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp [hd1_ne]
      ring
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp [hd1_ne]
  have h2des : ∀ a b c' e : Fin d,
      ∑ i : Fin (d ^ 2), v i a * v i b * star (v i c') * star (v i e) =
        ((d : ℂ) / ((d : ℂ) + 1)) *
          ((if a = c' ∧ b = e then (1 : ℂ) else 0) +
           (if a = e ∧ b = c' then (1 : ℂ) else 0)) := by
    have hiff := (ppl145_frame_potential_two_design_bound hd_pos v hnorm).2
    have hfp2' : ∑ i : Fin (d ^ 2), ∑ j : Fin (d ^ 2), ‖@inner ℂ _ _ (v i) (v j)‖ ^ 4 =
        (2 * ((d ^ 2 : ℕ) : ℝ) ^ 2) / ((d : ℝ) * ((d : ℝ) + 1)) := by
      rw [hfp2]
      have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
      push_cast
      field_simp [hd_ne, hd1_ne]
    have hraw := hiff.mp hfp2'
    intro a b c' e
    have h := hraw a b c' e
    have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hd1_ne_c : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast hd1_ne
    rw [h]
    push_cast
    field_simp [hd_ne, hd1_ne_c]
  exact ⟨hα_eq, hPOVM, hfp1, hfp2, h2des⟩

/-! ## Part II: Weyl–Heisenberg (`ZMod d`) & Multi-Qubit Pauli (`Fin n → ZMod 2`) Frameworks -/

private noncomputable def whPhase (d : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (d : ℂ))

private lemma whPhase_add (d : ℕ) (k₁ k₂ : ℤ) :
    whPhase d (k₁ + k₂) = whPhase d k₁ * whPhase d k₂ := by
  simp only [whPhase, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma whPhase_neg (d : ℕ) (k : ℤ) :
    whPhase d (-k) = star (whPhase d k) := by
  simp only [whPhase, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_natCast]
  push_cast; ring

private lemma whPhase_norm (d : ℕ) (k : ℤ) : ‖whPhase d k‖ = 1 := by
  have harg : 2 * Real.pi * Complex.I * (k : ℂ) / (d : ℂ) =
      (((2 * Real.pi * (k : ℝ) / (d : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [whPhase, harg, Complex.norm_exp_ofReal_mul_I]

private lemma whPhase_mul_d (d : ℕ) (hd : 0 < d) (m : ℤ) :
    whPhase d (m * (d : ℤ)) = 1 := by
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have harg : 2 * Real.pi * Complex.I * ((m * (d : ℤ) : ℤ) : ℂ) / (d : ℂ) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp [hd_ne]
  rw [whPhase, harg, Complex.exp_int_mul_two_pi_mul_I]

private lemma whPhase_eq_of_zmod_eq {d : ℕ} (hd : 0 < d) {k₁ k₂ : ℕ}
    (h : (k₁ : ZMod d) = (k₂ : ZMod d)) :
    whPhase d (k₁ : ℤ) = whPhase d (k₂ : ℤ) := by
  have hmod : k₁ ≡ k₂ [MOD d] := (ZMod.natCast_eq_natCast_iff k₁ k₂ d).mp h
  have hdvd : (d : ℤ) ∣ ((k₁ : ℤ) - (k₂ : ℤ)) :=
    Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod.symm)
  rcases hdvd with ⟨m, hm⟩
  have hk1 : (k₁ : ℤ) = (k₂ : ℤ) + m * (d : ℤ) := by linarith
  rw [hk1, whPhase_add, whPhase_mul_d d hd m, mul_one]

private lemma fin_zmod_eq_iff {d : ℕ} (i j : Fin d) :
    (i : ZMod d) = (j : ZMod d) ↔ i = j := by
  constructor
  · intro h
    have hmod : (i : ℕ) ≡ (j : ℕ) [MOD d] := (ZMod.natCast_eq_natCast_iff i.val j.val d).mp h
    rw [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
    exact Fin.ext hmod
  · intro h; subst h; rfl

private lemma wh_X_pow_entry {d : ℕ} (hd : 0 < d) {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : ∀ i j : Fin d, X i j = if (i : ZMod d) = (j : ZMod d) + 1 then 1 else 0)
    (a : ℕ) (i j : Fin d) :
    (X ^ a) i j = if (i : ZMod d) = (j : ZMod d) + (a : ZMod d) then 1 else 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  induction a generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Nat.cast_zero, add_zero]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : (i : ZMod d) ≠ (j : ZMod d) := fun h => hij ((fin_zmod_eq_iff i j).mp h)
      simp [hij, hne]
  | succ a ih =>
    rw [pow_succ, Matrix.mul_apply]
    let k0 : Fin d := ⟨((j : ZMod d) + 1).val, ZMod.val_lt _⟩
    have hk0 : (k0 : ZMod d) = (j : ZMod d) + 1 := ZMod.natCast_zmod_val _
    rw [Finset.sum_eq_single k0]
    · rw [ih i k0, hX k0 j, hk0, if_pos rfl, mul_one]
      have hadd : (j : ZMod d) + 1 + (a : ZMod d) = (j : ZMod d) + ((a + 1 : ℕ) : ZMod d) := by
        push_cast; ring
      rw [hadd]
    · intro k _ hne
      have hk_ne : (k : ZMod d) ≠ (j : ZMod d) + 1 := by
        intro hk
        rw [← hk0] at hk
        exact hne ((fin_zmod_eq_iff k k0).mp hk)
      rw [hX k j, if_neg hk_ne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma wh_Z_pow_entry {d : ℕ} {Z : Matrix (Fin d) (Fin d) ℂ}
    (hZ : ∀ i j : Fin d, Z i j = if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (d : ℂ)) else 0)
    (b : ℕ) (i j : Fin d) :
    (Z ^ b) i j = if i = j then whPhase d ((b * i.val : ℕ) : ℤ) else 0 := by
  induction b generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, zero_mul, Nat.cast_zero, Int.cast_zero, whPhase,
      mul_zero, zero_div, Complex.exp_zero]
  | succ b ih =>
    rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · rw [ih i j, hZ j j, if_pos rfl]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        have hz : Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (d : ℂ)) = whPhase d (i.val : ℤ) := by
          simp [whPhase]
        rw [hz, ← whPhase_add]
        congr 1; push_cast; ring
      · simp [hij]
    · intro k _ hne
      rw [hZ k j, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma unitary_inner_mulVec {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℂ _ _ (WithLp.toLp 2 (U.mulVec x.ofLp)) (WithLp.toLp 2 (U.mulVec y.ofLp)) =
      @inner ℂ _ _ x y := by
  rw [inner_eq_sum_star_mul, inner_eq_sum_star_mul]
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul']
  have h1 : ∑ a : Fin d, (∑ k : Fin d, star (U a k) * star (x.ofLp k)) *
      (∑ l : Fin d, U a l * y.ofLp l) =
      ∑ k : Fin d, ∑ l : Fin d, ((Uᴴ * U) k l) * (star (x.ofLp k) * y.ofLp l) := by
    have hexp : ∀ a : Fin d,
        (∑ k : Fin d, star (U a k) * star (x.ofLp k)) * (∑ l : Fin d, U a l * y.ofLp l) =
        ∑ k : Fin d, ∑ l : Fin d, (star (U a k) * U a l) * (star (x.ofLp k) * y.ofLp l) := by
      intro a
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [h1, hU]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma unitary_norm_mulVec {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (x : EuclideanSpace ℂ (Fin d)) :
    ‖WithLp.toLp 2 (U.mulVec x.ofLp)‖ = ‖x‖ := by
  have hsq : ‖WithLp.toLp 2 (U.mulVec x.ofLp)‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := unitary_inner_mulVec U hU x x
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    exact Complex.ofReal_injective (by simpa using h)
  have h1 : 0 ≤ ‖WithLp.toLp 2 (U.mulVec x.ofLp)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

private lemma inner_mulVec_adj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℂ _ _ (WithLp.toLp 2 (U.mulVec x.ofLp)) y =
      @inner ℂ _ _ x (WithLp.toLp 2 (Uᴴ.mulVec y.ofLp)) := by
  rw [inner_eq_sum_star_mul, inner_eq_sum_star_mul]
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul',
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring

/-- **Weyl–Heisenberg Discrete Shift & Clock Unitary Relations (`ZMod d`):**
For every `d ≥ 1`, the shift matrix `X` (`(X v)_i = v_{i-1}`) and clock matrix `Z`
(`(Z v)_i = ω^i v_i`, `ω = exp(2πi/d)`) are unitary, have order `d`, and satisfy the exact
projective commutation relation `X^a Z^b = ω^{-ab} Z^b X^a` for all `a, b : ℕ` (and `ZMod d`). -/
theorem ppl145_weyl_heisenberg_relations {d : ℕ} (hd : 0 < d)
    (X Z : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j : Fin d, X i j = if (i : ZMod d) = (j : ZMod d) + 1 then 1 else 0)
    (hZ : ∀ i j : Fin d, Z i j = if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (d : ℂ)) else 0) :
    (Xᴴ * X = 1 ∧ X * Xᴴ = 1) ∧
    (Zᴴ * Z = 1 ∧ Z * Zᴴ = 1) ∧
    (X ^ d = 1 ∧ Z ^ d = 1) ∧
    (∀ a b : ℕ,
      X ^ a * Z ^ b =
        Complex.exp (-(2 * Real.pi * Complex.I * ((a * b : ℕ) : ℂ) / (d : ℂ))) •
          (Z ^ b * X ^ a)) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hX_unit : Xᴴ * X = 1 ∧ X * Xᴴ = 1 := by
    constructor
    · ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      let k0 : Fin d := ⟨((i : ZMod d) + 1).val, ZMod.val_lt _⟩
      have hk0 : (k0 : ZMod d) = (i : ZMod d) + 1 := ZMod.natCast_zmod_val _
      rw [Finset.sum_eq_single k0]
      · simp only [Matrix.conjTranspose_apply, hX, hk0]
        by_cases hij : i = j
        · subst hij; simp
        · have hne : (i : ZMod d) + 1 ≠ (j : ZMod d) + 1 := by
            intro h; exact hij ((fin_zmod_eq_iff i j).mp (add_right_cancel h))
          simp [hij, hne]
      · intro k _ hne
        have hk_ne : (k : ZMod d) ≠ (i : ZMod d) + 1 := by
          intro h; rw [← hk0] at h; exact hne ((fin_zmod_eq_iff k k0).mp h)
        simp [Matrix.conjTranspose_apply, hX, hk_ne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      let k0 : Fin d := ⟨((i : ZMod d) - 1).val, ZMod.val_lt _⟩
      have hk0 : (k0 : ZMod d) + 1 = (i : ZMod d) := by
        rw [ZMod.natCast_zmod_val]; ring
      rw [Finset.sum_eq_single k0]
      · simp only [Matrix.conjTranspose_apply, hX, hk0]
        by_cases hij : i = j
        · subst hij; simp
        · have hne : (j : ZMod d) ≠ (i : ZMod d) := fun h => hij ((fin_zmod_eq_iff j i).mp h).symm
          simp [hij, hne]
      · intro k _ hne
        have hk_ne : (i : ZMod d) ≠ (k : ZMod d) + 1 := by
          intro h
          have hk : (k : ZMod d) = (k0 : ZMod d) := by
            have : (k : ZMod d) + 1 = (k0 : ZMod d) + 1 := by rw [← h, hk0]
            exact add_right_cancel this
          exact hne ((fin_zmod_eq_iff k k0).mp hk)
        simp [hX, hk_ne]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hZ_unit : Zᴴ * Z = 1 ∧ Z * Zᴴ = 1 := by
    constructor
    · ext i j
      rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single j]
      · simp only [Matrix.conjTranspose_apply, hZ]
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte]
          have h1 : Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (d : ℂ)) = whPhase d (i.val : ℤ) := rfl
          rw [h1, ← whPhase_neg, ← whPhase_add]
          simp [whPhase]
        · simp [hij, Ne.symm hij]
      · intro k _ hne; simp [hZ, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · ext i j
      rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single i]
      · simp only [Matrix.conjTranspose_apply, hZ]
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte]
          have h1 : Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (d : ℂ)) = whPhase d (i.val : ℤ) := rfl
          rw [h1, ← whPhase_neg, ← whPhase_add]
          simp [whPhase]
        · simp [hij, Ne.symm hij]
      · intro k _ hne; simp [hZ, Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hord : X ^ d = 1 ∧ Z ^ d = 1 := by
    constructor
    · ext i j
      rw [wh_X_pow_entry hd hX d i j, Matrix.one_apply]
      simp only [ZMod.natCast_self, add_zero]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : (i : ZMod d) ≠ (j : ZMod d) := fun h => hij ((fin_zmod_eq_iff i j).mp h)
        simp [hij, hne]
    · ext i j
      rw [wh_Z_pow_entry hZ d i j, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        have hcast : ((d * i.val : ℕ) : ℤ) = (i.val : ℤ) * (d : ℤ) := by push_cast; ring
        rw [hcast, whPhase_mul_d d hd]
      · simp [hij]
  have hcomm : ∀ a b : ℕ,
      X ^ a * Z ^ b =
        Complex.exp (-(2 * Real.pi * Complex.I * ((a * b : ℕ) : ℂ) / (d : ℂ))) •
          (Z ^ b * X ^ a) := by
    intro a b
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
    · rw [wh_X_pow_entry hd hX a i j, wh_Z_pow_entry hZ b j j, wh_Z_pow_entry hZ b i i,
        if_pos rfl, if_pos rfl]
      by_cases hij : (i : ZMod d) = (j : ZMod d) + (a : ZMod d)
      · rw [if_pos hij, one_mul, mul_one]
        have hbi : ((b * i.val : ℕ) : ZMod d) = ((b * j.val + a * b : ℕ) : ZMod d) := by
          push_cast; rw [hij]; ring
        have hph := whPhase_eq_of_zmod_eq hd hbi
        have hneg : Complex.exp (-(2 * Real.pi * Complex.I * ((a * b : ℕ) : ℂ) / (d : ℂ))) =
            whPhase d (-((a * b : ℕ) : ℤ)) := by
          simp only [whPhase]; congr 1; push_cast; ring
        rw [hneg, hph, ← whPhase_add]
        congr 1; push_cast; ring
      · simp [hij]
    · intro k _ hne; rw [wh_Z_pow_entry hZ b i k, if_neg (Ne.symm hne), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro k _ hne; rw [wh_Z_pow_entry hZ b k j, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact ⟨hX_unit, hZ_unit, hord, hcomm⟩

/-- **Weyl–Heisenberg Covariant SIC-POVM Generation Theorem:**
If `ψ ∈ ℂ^d` (`d ≥ 1`) is a unit fiducial vector whose `d^2 - 1` nontrivial Weyl–Heisenberg
overlaps satisfy `‖⟨ψ, X^a Z^b ψ⟩‖^2 = 1 / (d + 1)` for all `(a, b) ∈ ZMod d × ZMod d` with
`(a, b) ≠ (0, 0)`, then the Weyl–Heisenberg orbit `{X^a Z^b ψ}` forms a `d^2`-element SIC-POVM
in `ℂ^d`. -/
theorem ppl145_weyl_heisenberg_fiducial_generates_sic {d : ℕ} (hd : 0 < d)
    (X Z : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j : Fin d, X i j = if (i : ZMod d) = (j : ZMod d) + 1 then 1 else 0)
    (hZ : ∀ i j : Fin d, Z i j = if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (d : ℂ)) else 0)
    (ψ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1)
    (hfid : ∀ a b : ZMod d, (a, b) ≠ (0, 0) →
      ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ a.val * Z ^ b.val).mulVec ψ.ofLp))‖ ^ 2 =
        1 / ((d : ℝ) + 1)) :
    ∃ v : Fin (d ^ 2) → EuclideanSpace ℂ (Fin d),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((d : ℝ) + 1)) := by
  have : NeZero d := ⟨hd.ne'⟩
  have ⟨hXu, hZu, hord, hcomm⟩ := ppl145_weyl_heisenberg_relations hd X Z hX hZ
  have hX_pow_mod : ∀ k₁ k₂ : ℕ, (k₁ : ZMod d) = (k₂ : ZMod d) → X ^ k₁ = X ^ k₂ := by
    intro k₁ k₂ hk
    ext i j
    rw [wh_X_pow_entry hd hX k₁ i j, wh_X_pow_entry hd hX k₂ i j, hk]
  have hZ_pow_mod : ∀ k₁ k₂ : ℕ, (k₁ : ZMod d) = (k₂ : ZMod d) → Z ^ k₁ = Z ^ k₂ := by
    intro k₁ k₂ hk
    ext i j
    rw [wh_Z_pow_entry hZ k₁ i j, wh_Z_pow_entry hZ k₂ i j]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      apply whPhase_eq_of_zmod_eq hd
      push_cast; rw [hk]
    · simp [hij]
  have hX_pow_unit : ∀ a : ℕ, (X ^ a)ᴴ * X ^ a = 1 := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [pow_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (X ^ a)ᴴ,
        ih, Matrix.one_mul, hXu.1]
  have hZ_pow_unit : ∀ b : ℕ, (Z ^ b)ᴴ * Z ^ b = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      rw [pow_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Z ^ b)ᴴ,
        ih, Matrix.one_mul, hZu.1]
  have hD_unit : ∀ a b : ZMod d,
      (X ^ a.val * Z ^ b.val)ᴴ * (X ^ a.val * Z ^ b.val) = 1 := by
    intro a b
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (X ^ a.val)ᴴ,
      hX_pow_unit, Matrix.one_mul, hZ_pow_unit]
  have hX_adj : ∀ a : ZMod d, (X ^ a.val)ᴴ = X ^ (-a).val := by
    intro a
    have hmul : X ^ (-a).val * X ^ a.val = 1 := by
      rw [← pow_add]
      have hz : (((-a).val + a.val : ℕ) : ZMod d) = ((0 : ℕ) : ZMod d) := by
        push_cast; simp
      rw [hX_pow_mod _ 0 hz, pow_zero]
    calc (X ^ a.val)ᴴ = 1 * (X ^ a.val)ᴴ := (Matrix.one_mul _).symm
      _ = (X ^ (-a).val * X ^ a.val) * (X ^ a.val)ᴴ := by rw [hmul]
      _ = X ^ (-a).val * (X ^ a.val * (X ^ a.val)ᴴ) := Matrix.mul_assoc _ _ _
      _ = X ^ (-a).val := by
        have hright : X ^ a.val * (X ^ a.val)ᴴ = 1 := by
          have : ∀ k, X ^ k * (X ^ k)ᴴ = 1 := by
            intro k; induction k with
            | zero => simp
            | succ k ih =>
              rw [pow_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc X,
                hXu.2, Matrix.one_mul, ih]
          exact this a.val
        rw [hright, Matrix.mul_one]
  have hZ_adj : ∀ b : ZMod d, (Z ^ b.val)ᴴ = Z ^ (-b).val := by
    intro b
    have hmul : Z ^ (-b).val * Z ^ b.val = 1 := by
      rw [← pow_add]
      have hz : (((-b).val + b.val : ℕ) : ZMod d) = ((0 : ℕ) : ZMod d) := by
        push_cast; simp
      rw [hZ_pow_mod _ 0 hz, pow_zero]
    calc (Z ^ b.val)ᴴ = 1 * (Z ^ b.val)ᴴ := (Matrix.one_mul _).symm
      _ = (Z ^ (-b).val * Z ^ b.val) * (Z ^ b.val)ᴴ := by rw [hmul]
      _ = Z ^ (-b).val * (Z ^ b.val * (Z ^ b.val)ᴴ) := Matrix.mul_assoc _ _ _
      _ = Z ^ (-b).val := by
        have hright : Z ^ b.val * (Z ^ b.val)ᴴ = 1 := by
          have : ∀ k, Z ^ k * (Z ^ k)ᴴ = 1 := by
            intro k; induction k with
            | zero => simp
            | succ k ih =>
              rw [pow_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Z,
                hZu.2, Matrix.one_mul, ih]
          exact this b.val
        rw [hright, Matrix.mul_one]
  -- Canonical bijection `Fin (d ^ 2) ≃ ZMod d × ZMod d`
  have hcard : Fintype.card (Fin (d ^ 2)) = Fintype.card (ZMod d × ZMod d) := by
    simp [ZMod.card, sq]
  let e : Fin (d ^ 2) ≃ ZMod d × ZMod d := Fintype.equivOfCardEq hcard
  refine ⟨fun i => WithLp.toLp 2 ((X ^ (e i).1.val * Z ^ (e i).2.val).mulVec ψ.ofLp), ?_, ?_⟩
  · intro i
    rw [unitary_norm_mulVec _ (hD_unit (e i).1 (e i).2) ψ, hψ]
  · intro i j hij
    have he_ne : e i ≠ e j := fun h => hij (e.injective h)
    let a₁ := (e i).1; let b₁ := (e i).2
    let a₂ := (e j).1; let b₂ := (e j).2
    have hdiff_ne : (a₂ - a₁, b₂ - b₁) ≠ (0, 0) := by
      intro h
      have ha : a₂ - a₁ = 0 := congr_arg Prod.fst h
      have hb : b₂ - b₁ = 0 := congr_arg Prod.snd h
      exact he_ne (Prod.ext (sub_eq_zero.mp ha).symm (sub_eq_zero.mp hb).symm)
    rw [inner_mulVec_adj]
    have hcomp :
        (X ^ a₁.val * Z ^ b₁.val)ᴴ.mulVec ((X ^ a₂.val * Z ^ b₂.val).mulVec ψ.ofLp) =
        ((X ^ a₁.val * Z ^ b₁.val)ᴴ * (X ^ a₂.val * Z ^ b₂.val)).mulVec ψ.ofLp := by
      rw [Matrix.mulVec_mulVec]
    rw [hcomp]
    have hprod :
        (X ^ a₁.val * Z ^ b₁.val)ᴴ * (X ^ a₂.val * Z ^ b₂.val) =
        whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) •
          (X ^ (a₂ - a₁).val * Z ^ (b₂ - b₁).val) := by
      rw [Matrix.conjTranspose_mul, hX_adj, hZ_adj]
      have hXcomb : X ^ (-a₁).val * X ^ a₂.val = X ^ (a₂ - a₁).val := by
        rw [← pow_add]
        apply hX_pow_mod
        push_cast; simp; ring
      have hZcomb : Z ^ (-b₁).val * Z ^ b₂.val = Z ^ (b₂ - b₁).val := by
        rw [← pow_add]
        apply hZ_pow_mod
        push_cast; simp; ring
      have hswap : Z ^ (-b₁).val * X ^ (a₂ - a₁).val =
          whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) •
            (X ^ (a₂ - a₁).val * Z ^ (-b₁).val) := by
        have hc := hcomm (a₂ - a₁).val (-b₁).val
        have hc' := congr_arg (fun M => whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) • M) hc
        simp only [smul_smul] at hc'
        have h1 : whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) *
            Complex.exp (-(2 * Real.pi * Complex.I * (((a₂ - a₁).val * (-b₁).val : ℕ) : ℂ) / (d : ℂ))) = 1 := by
          have hneg : Complex.exp (-(2 * Real.pi * Complex.I * (((a₂ - a₁).val * (-b₁).val : ℕ) : ℂ) / (d : ℂ))) =
              whPhase d (-(((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) := by
            simp only [whPhase]; congr 1; push_cast; ring
          rw [hneg, ← whPhase_add]; simp [whPhase]
        rw [h1, one_smul] at hc'
        exact hc'.symm
      calc Z ^ (-b₁).val * X ^ (-a₁).val * (X ^ a₂.val * Z ^ b₂.val)
          = Z ^ (-b₁).val * (X ^ (-a₁).val * X ^ a₂.val) * Z ^ b₂.val := by
            simp only [Matrix.mul_assoc]
        _ = (Z ^ (-b₁).val * X ^ (a₂ - a₁).val) * Z ^ b₂.val := by rw [hXcomb]
        _ = (whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) •
              (X ^ (a₂ - a₁).val * Z ^ (-b₁).val)) * Z ^ b₂.val := by rw [hswap]
        _ = whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) •
              (X ^ (a₂ - a₁).val * (Z ^ (-b₁).val * Z ^ b₂.val)) := by
            rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = _ := by rw [hZcomb]
    rw [hprod, Matrix.smul_mulVec]
    have htoLp : WithLp.toLp 2 (whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) •
          (X ^ (a₂ - a₁).val * Z ^ (b₂ - b₁).val).mulVec ψ.ofLp) =
        whPhase d ((((a₂ - a₁).val * (-b₁).val : ℕ) : ℤ)) •
          WithLp.toLp 2 ((X ^ (a₂ - a₁).val * Z ^ (b₂ - b₁).val).mulVec ψ.ofLp) := rfl
    rw [htoLp, inner_smul_right, norm_mul, whPhase_norm, one_mul]
    exact hfid (a₂ - a₁) (b₂ - b₁) hdiff_ne

private def zmod2Sign (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

private lemma zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  by_cases h : x.val = 0
  · left
    exact (ZMod.val_eq_zero x).mp h
  · right
    have h1 : x.val = 1 := by omega
    rw [← ZMod.natCast_zmod_val x, h1]; rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
  · rfl
  · simp at h
  · simp at h
  · rfl

private lemma zmod2Sign_add (x y : ZMod 2) :
    zmod2Sign (x + y) = zmod2Sign x * zmod2Sign y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [zmod2Sign, zmod2_add_self]

private lemma zmod2Sign_star (x : ZMod 2) : star (zmod2Sign x) = zmod2Sign x := by
  rcases zmod2_cases x with rfl | rfl <;> simp [zmod2Sign]

private lemma zmod2Sign_norm (x : ZMod 2) : ‖zmod2Sign x‖ = 1 := by
  rcases zmod2_cases x with rfl | rfl <;> simp [zmod2Sign]

/-- **Multi-Qubit Pauli (`(ZMod 2)^n × (ZMod 2)^n`) Covariant SIC-POVM Generation Theorem:**
If `ψ ∈ ℂ^{(ZMod 2)^n}` is a unit fiducial vector whose `4^n - 1` nontrivial `n`-qubit Pauli
overlaps all have squared norm `1 / (2^n + 1)`, then its `n`-qubit Pauli orbit generates a
`(2^n)^2`-element SIC-POVM in `ℂ^{2^n}`. (This framework produces Hoggar's 64 lines for `n = 3`.) -/
theorem ppl145_multiqubit_pauli_fiducial_generates_sic {n : ℕ}
    (ψ : EuclideanSpace ℂ (Fin n → ZMod 2))
    (hψ : ‖ψ‖ = 1)
    (hfid : ∀ a b : Fin n → ZMod 2, (a, b) ≠ (0, 0) →
      ‖∑ j : Fin n → ZMod 2,
          star (ψ j) * (if ∑ r : Fin n, b r * (j r + a r) = 0 then (1 : ℂ) else -1) *
            ψ (j + a)‖ ^ 2 =
        1 / ((2 ^ n : ℝ) + 1)) :
    ∃ v : Fin ((2 ^ n) ^ 2) → EuclideanSpace ℂ (Fin (2 ^ n)),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((2 ^ n : ℝ) + 1)) := by
  let V := Fin n → ZMod 2
  have hcardV : Fintype.card (Fin (2 ^ n)) = Fintype.card V := by
    simp [V, ZMod.card]
  let eV : Fin (2 ^ n) ≃ V := Fintype.equivOfCardEq hcardV
  have hcardP : Fintype.card (Fin ((2 ^ n) ^ 2)) = Fintype.card (V × V) := by
    simp [V, ZMod.card, sq]
  let eP : Fin ((2 ^ n) ^ 2) ≃ V × V := Fintype.equivOfCardEq hcardP
  let orbit : V × V → EuclideanSpace ℂ (Fin (2 ^ n)) := fun p =>
    WithLp.toLp 2 fun k =>
      zmod2Sign (∑ r : Fin n, p.2 r * ((eV k) r + p.1 r)) * ψ (eV k + p.1)
  refine ⟨fun i => orbit (eP i), ?_, ?_⟩
  · intro i
    have hsq : ‖orbit (eP i)‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sum_norm_sq]
      simp only [orbit, norm_mul, zmod2Sign_norm, one_mul]
      rw [Fintype.sum_equiv eV (fun k => ‖ψ (eV k + (eP i).1)‖ ^ 2)
        (fun x => ‖ψ (x + (eP i).1)‖ ^ 2) (fun _ => rfl)]
      rw [Fintype.sum_equiv (Equiv.addRight (eP i).1) (fun x => ‖ψ (x + (eP i).1)‖ ^ 2)
        (fun y => ‖ψ y‖ ^ 2) (fun _ => rfl)]
      rw [← norm_sq_eq_sum_norm_sq, hψ, one_pow]
    have h0 : 0 ≤ ‖orbit (eP i)‖ := norm_nonneg _
    nlinarith
  · intro i j hij
    have hp_ne : eP i ≠ eP j := fun h => hij (eP.injective h)
    let a₁ := (eP i).1; let b₁ := (eP i).2
    let a₂ := (eP j).1; let b₂ := (eP j).2
    have hdiff_ne : (a₁ + a₂, b₁ + b₂) ≠ (0, 0) := by
      intro h
      have ha : a₁ + a₂ = 0 := congr_arg Prod.fst h
      have hb : b₁ + b₂ = 0 := congr_arg Prod.snd h
      have ha' : a₁ = a₂ := funext fun r => zmod2_eq_of_add_eq_zero (congr_fun ha r)
      have hb' : b₁ = b₂ := funext fun r => zmod2_eq_of_add_eq_zero (congr_fun hb r)
      exact hp_ne (Prod.ext ha' hb')
    have hinner : @inner ℂ _ _ (orbit (eP i)) (orbit (eP j)) =
        zmod2Sign (∑ r : Fin n, b₁ r * (a₁ r + a₂ r)) *
        ∑ x : V, star (ψ x) * zmod2Sign (∑ r : Fin n, (b₁ + b₂) r * (x r + (a₁ + a₂) r)) *
          ψ (x + (a₁ + a₂)) := by
      rw [inner_eq_sum_star_mul]
      simp only [orbit]
      rw [Fintype.sum_equiv eV _ (fun y =>
        star (zmod2Sign (∑ r : Fin n, b₁ r * (y r + a₁ r)) * ψ (y + a₁)) *
        (zmod2Sign (∑ r : Fin n, b₂ r * (y r + a₂ r)) * ψ (y + a₂))) (fun _ => rfl)]
      rw [Fintype.sum_equiv (Equiv.addRight a₁)
        (fun y =>
          star (zmod2Sign (∑ r : Fin n, b₁ r * (y r + a₁ r)) * ψ (y + a₁)) *
          (zmod2Sign (∑ r : Fin n, b₂ r * (y r + a₂ r)) * ψ (y + a₂)))
        (fun x =>
          star (zmod2Sign (∑ r : Fin n, b₁ r * x r) * ψ x) *
          (zmod2Sign (∑ r : Fin n, b₂ r * (x r + a₁ r + a₂ r)) * ψ (x + (a₁ + a₂)))) ?_]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [star_mul', zmod2Sign_star]
        have hexp :
            (∑ r : Fin n, b₁ r * x r) + (∑ r : Fin n, b₂ r * (x r + a₁ r + a₂ r)) =
            (∑ r : Fin n, b₁ r * (a₁ r + a₂ r)) +
              (∑ r : Fin n, (b₁ + b₂) r * (x r + (a₁ + a₂) r)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          change b₁ r * x r + b₂ r * (x r + a₁ r + a₂ r) =
            b₁ r * (a₁ r + a₂ r) + (b₁ r + b₂ r) * (x r + (a₁ r + a₂ r))
          calc b₁ r * x r + b₂ r * (x r + a₁ r + a₂ r)
              = b₁ r * x r + b₂ r * (x r + a₁ r + a₂ r) +
                  (b₁ r * (a₁ r + a₂ r) + b₁ r * (a₁ r + a₂ r)) := by
                rw [zmod2_add_self, add_zero]
            _ = b₁ r * (a₁ r + a₂ r) + (b₁ r + b₂ r) * (x r + (a₁ r + a₂ r)) := by ring
        have hsign :
            zmod2Sign (∑ r : Fin n, b₁ r * x r) * zmod2Sign (∑ r : Fin n, b₂ r * (x r + a₁ r + a₂ r)) =
            zmod2Sign (∑ r : Fin n, b₁ r * (a₁ r + a₂ r)) *
              zmod2Sign (∑ r : Fin n, (b₁ + b₂) r * (x r + (a₁ + a₂) r)) := by
          rw [← zmod2Sign_add, ← zmod2Sign_add, hexp]
        calc zmod2Sign (∑ r : Fin n, b₁ r * x r) * star (ψ x) *
              (zmod2Sign (∑ r : Fin n, b₂ r * (x r + a₁ r + a₂ r)) * ψ (x + (a₁ + a₂)))
            = (zmod2Sign (∑ r : Fin n, b₁ r * x r) * zmod2Sign (∑ r : Fin n, b₂ r * (x r + a₁ r + a₂ r))) *
              (star (ψ x) * ψ (x + (a₁ + a₂))) := by ring
          _ = (zmod2Sign (∑ r : Fin n, b₁ r * (a₁ r + a₂ r)) *
                zmod2Sign (∑ r : Fin n, (b₁ + b₂) r * (x r + (a₁ + a₂) r))) *
              (star (ψ x) * ψ (x + (a₁ + a₂))) := by rw [hsign]
          _ = zmod2Sign (∑ r : Fin n, b₁ r * (a₁ r + a₂ r)) *
              (star (ψ x) * zmod2Sign (∑ r : Fin n, (b₁ + b₂) r * (x r + (a₁ + a₂) r)) *
                ψ (x + (a₁ + a₂))) := by ring
      · intro y
        have hy2 : (y + a₁) + (a₁ + a₂) = y + a₂ := by
          funext r
          change y r + a₁ r + (a₁ r + a₂ r) = y r + a₂ r
          calc y r + a₁ r + (a₁ r + a₂ r) = y r + (a₁ r + a₁ r) + a₂ r := by ring
            _ = y r + a₂ r := by rw [zmod2_add_self, add_zero]
        have hy3 : ∀ r, (y + a₁) r + a₁ r + a₂ r = y r + a₂ r := fun r => by
          change y r + a₁ r + a₁ r + a₂ r = y r + a₂ r
          calc y r + a₁ r + a₁ r + a₂ r = y r + (a₁ r + a₁ r) + a₂ r := by ring
            _ = y r + a₂ r := by rw [zmod2_add_self, add_zero]
        change star (zmod2Sign (∑ r : Fin n, b₁ r * (y r + a₁ r)) * ψ (y + a₁)) *
            (zmod2Sign (∑ r : Fin n, b₂ r * (y r + a₂ r)) * ψ (y + a₂)) =
          star (zmod2Sign (∑ r : Fin n, b₁ r * (y + a₁) r) * ψ (y + a₁)) *
            (zmod2Sign (∑ r : Fin n, b₂ r * ((y + a₁) r + a₁ r + a₂ r)) * ψ ((y + a₁) + (a₁ + a₂)))
        simp only [hy2, hy3]
        rfl
    rw [hinner, norm_mul, zmod2Sign_norm, one_mul]
    simpa [zmod2Sign] using hfid (a₁ + a₂) (b₁ + b₂) hdiff_ne

/-! ## Part III: Explicit Kernel-Certified Exact SIC-POVMs (`d = 1, 2, 3, 8`; `0` `native_decide`) -/

/-- **Exact SIC-POVM in `d = 1`:** Single unit vector `(1) ∈ ℂ^1` satisfying the POVM identity. -/
theorem ppl145_sic_povm_dim1 :
    ∃ v : Fin (1 ^ 2) → EuclideanSpace ℂ (Fin 1),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((1 : ℝ) + 1)) ∧
      ((1 : ℂ) / (1 : ℂ)) •
        ∑ i : Fin (1 ^ 2), Matrix.of (fun a b : Fin 1 => v i a * star (v i b)) =
          (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨fun _ => WithLp.toLp 2 (fun _ => (1 : ℂ)), ?_, ?_, ?_⟩
  · intro i
    have hsq : ‖WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sum_norm_sq]; simp
    have h0 : 0 ≤ ‖WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))‖ := norm_nonneg _
    nlinarith
  · intro i j hij
    exact absurd (Fin.ext (by omega : i.val = j.val)) hij
  · ext a b
    fin_cases a; fin_cases b
    simp

/-- **Exact Tetrahedral Bloch Weyl–Heisenberg SIC-POVM in `d = 2`:**
Certified from the explicit algebraic fiducial `ψ = (√((3+√3)/6), √((3-√3)/12) * (1 + i))`
under the `d = 2` Weyl–Heisenberg (Pauli) group `{I, Z, X, XZ}`, yielding 4 equiangular unit
vectors in `ℂ^2` with pairwise squared overlap `1/3` and exact POVM resolution of the identity. -/
theorem ppl145_sic_povm_dim2 :
    ∃ v : Fin (2 ^ 2) → EuclideanSpace ℂ (Fin 2),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((2 : ℝ) + 1)) ∧
      ((1 : ℂ) / (2 : ℂ)) •
        ∑ i : Fin (2 ^ 2), Matrix.of (fun a b : Fin 2 => v i a * star (v i b)) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  let X : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => if ((i : ℕ) : ZMod 2) = ((j : ℕ) : ZMod 2) + 1 then 1 else 0
  let Z : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (2 : ℂ)) else 0
  have hX : ∀ i j : Fin 2, X i j = if ((i : ℕ) : ZMod 2) = ((j : ℕ) : ZMod 2) + 1 then 1 else 0 :=
    fun _ _ => rfl
  have hZ : ∀ i j : Fin 2, Z i j = if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (2 : ℂ)) else 0 :=
    fun _ _ => rfl
  let a : ℝ := Real.sqrt ((3 + Real.sqrt 3) / 6)
  let b : ℝ := Real.sqrt ((3 - Real.sqrt 3) / 12)
  have hs3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3_le3 : Real.sqrt 3 ≤ 3 := by nlinarith
  have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
  have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (3 + Real.sqrt 3) / 6 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (3 - Real.sqrt 3) / 12 := Real.sq_sqrt (by linarith)
  have hab : a * b = Real.sqrt 3 / 6 := by
    have hsq : (a * b) ^ 2 = (Real.sqrt 3 / 6) ^ 2 := by
      calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
        _ = ((3 + Real.sqrt 3) / 6) * ((3 - Real.sqrt 3) / 12) := by rw [ha2, hb2]
        _ = (9 - Real.sqrt 3 ^ 2) / 72 := by ring
        _ = (9 - 3) / 72 := by rw [hs3_sq]
        _ = 3 / 36 := by norm_num
        _ = Real.sqrt 3 ^ 2 / 36 := by rw [hs3_sq]
        _ = (Real.sqrt 3 / 6) ^ 2 := by ring
    have h0 : 0 ≤ a * b := mul_nonneg ha_nonneg hb_nonneg
    have h1 : 0 ≤ Real.sqrt 3 / 6 := by linarith
    nlinarith
  let ψ : EuclideanSpace ℂ (Fin 2) :=
    WithLp.toLp 2 ![((a : ℂ)), ((b : ℂ) * (1 + Complex.I))]
  have h1I_norm_sq : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; norm_num
  have hψ_norm : ‖ψ‖ = 1 := by
    have hsq : ‖ψ‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sum_norm_sq, Fin.sum_univ_two]
      simp only [ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h1I_norm_sq]
      rw [ha2, hb2]; ring
    have h0 : 0 ≤ ‖ψ‖ := norm_nonneg _
    nlinarith
  have hZ0 : Complex.exp (2 * Real.pi * Complex.I * ((0 : Fin 2) : ℂ) / (2 : ℂ)) = 1 := by
    simp
  have hZ1 : Complex.exp (2 * Real.pi * Complex.I * ((1 : Fin 2) : ℂ) / (2 : ℂ)) = -1 := by
    have harg : 2 * Real.pi * Complex.I * ((1 : Fin 2) : ℂ) / (2 : ℂ) = Real.pi * Complex.I := by
      simp; ring
    rw [harg, Complex.exp_pi_mul_I]
  have hX_ent : ∀ i j : Fin 2, X i j = if i = j then 0 else 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> (simp [X]; try decide)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hfid : ∀ x y : ZMod 2, (x, y) ≠ (0, 0) →
      ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ x.val * Z ^ y.val).mulVec ψ.ofLp))‖ ^ 2 =
        1 / ((2 : ℝ) + 1) := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd rfl hxy
    · -- (0, 1): Z
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 0 * Z ^ 1).mulVec ψ.ofLp)) =
          ((Real.sqrt 3 / 3 : ℝ) : ℂ) := by
        rw [inner_eq_sum_star_mul, Fin.sum_univ_two]
        simp only [pow_zero, pow_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Z, Matrix.of_apply, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          ↓reduceIte, Fin.isValue, Fin.zero_ne_one, h10,
          zero_mul, add_zero, zero_add, hZ0, hZ1, one_mul, neg_mul, star_mul', Complex.star_def,
          Complex.conj_ofReal, map_add, map_one, Complex.conj_I]
        have hcalc : (a : ℂ) * (a : ℂ) + (b : ℂ) * (1 + -Complex.I) * -((b : ℂ) * (1 + Complex.I)) =
            (((a ^ 2 - 2 * b ^ 2 : ℝ) : ℂ)) := by
          push_cast
          ring_nf
          rw [Complex.I_sq]
          ring
        rw [hcalc]
        congr 1; rw [ha2, hb2]; ring
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 0 * Z ^ 1).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((2 : ℝ) + 1)
      rw [hv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc (Real.sqrt 3 / 3) ^ 2 = Real.sqrt 3 ^ 2 / 9 := by ring
        _ = 3 / 9 := by rw [hs3_sq]
        _ = 1 / ((2 : ℝ) + 1) := by norm_num
    · -- (1, 0): X
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 0).mulVec ψ.ofLp)) =
          ((Real.sqrt 3 / 3 : ℝ) : ℂ) := by
        rw [inner_eq_sum_star_mul, Fin.sum_univ_two]
        simp only [pow_zero, pow_one, Matrix.mul_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          hX_ent, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          ↓reduceIte, Fin.isValue, Fin.zero_ne_one, h10,
          zero_mul, one_mul, add_zero, zero_add, star_mul', Complex.star_def,
          Complex.conj_ofReal, map_add, map_one, Complex.conj_I]
        have hcalc : (a : ℂ) * ((b : ℂ) * (1 + Complex.I)) + (b : ℂ) * (1 + -Complex.I) * (a : ℂ) =
            (((2 * (a * b) : ℝ) : ℂ)) := by
          push_cast; ring
        rw [hcalc]
        congr 1; rw [hab]; ring
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 0).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((2 : ℝ) + 1)
      rw [hv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc (Real.sqrt 3 / 3) ^ 2 = Real.sqrt 3 ^ 2 / 9 := by ring
        _ = 3 / 9 := by rw [hs3_sq]
        _ = 1 / ((2 : ℝ) + 1) := by norm_num
    · -- (1, 1): X * Z
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 1).mulVec ψ.ofLp)) =
          (-((Real.sqrt 3 / 3 : ℝ) : ℂ)) * Complex.I := by
        rw [inner_eq_sum_star_mul, Fin.sum_univ_two]
        simp only [pow_one, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two,
          hX_ent, Z, Matrix.of_apply, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          ↓reduceIte, Fin.isValue, Fin.zero_ne_one, h10,
          zero_mul, one_mul, add_zero, zero_add, hZ0, hZ1, neg_mul,
          star_mul', Complex.star_def, Complex.conj_ofReal, map_add, map_one, Complex.conj_I]
        have hcalc : (a : ℂ) * -((b : ℂ) * (1 + Complex.I)) + (b : ℂ) * (1 + -Complex.I) * (a : ℂ) =
            (-(((2 * (a * b) : ℝ) : ℂ))) * Complex.I := by
          push_cast; ring
        rw [hcalc, hab]
        push_cast; ring
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 1).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((2 : ℝ) + 1)
      rw [hv, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc (Real.sqrt 3 / 3) ^ 2 = Real.sqrt 3 ^ 2 / 9 := by ring
        _ = 3 / 9 := by rw [hs3_sq]
        _ = 1 / ((2 : ℝ) + 1) := by norm_num
  obtain ⟨v, hv_norm, hv_equi⟩ :=
    ppl145_weyl_heisenberg_fiducial_generates_sic (by norm_num : 0 < 2) X Z hX hZ ψ hψ_norm hfid
  have htight := ppl145_sic_povm_tightness_characterization (by norm_num : 2 ≤ 2)
    (by norm_num : (1 : ℝ) / ((2 : ℝ) + 1) < 1) v hv_norm hv_equi
  exact ⟨v, hv_norm, hv_equi, htight.2.1⟩

/-- **Exact Hesse Weyl–Heisenberg SIC-POVM in `d = 3`:**
Certified from the classic Hesse fiducial `ψ = (0, 1, -1) / √2` under the `d = 3` Weyl–Heisenberg
group `⟨X, Z⟩`, yielding 9 equiangular unit vectors in `ℂ^3` with pairwise squared overlap `1/4`
and exact POVM resolution of the identity. -/
theorem ppl145_sic_povm_dim3 :
    ∃ v : Fin (3 ^ 2) → EuclideanSpace ℂ (Fin 3),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((3 : ℝ) + 1)) ∧
      ((1 : ℂ) / (3 : ℂ)) •
        ∑ i : Fin (3 ^ 2), Matrix.of (fun a b : Fin 3 => v i a * star (v i b)) =
          (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  let X : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.of fun i j => if ((i : ℕ) : ZMod 3) = ((j : ℕ) : ZMod 3) + 1 then 1 else 0
  let Z : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.of fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (3 : ℂ)) else 0
  have hX : ∀ i j : Fin 3, X i j = if ((i : ℕ) : ZMod 3) = ((j : ℕ) : ZMod 3) + 1 then 1 else 0 :=
    fun _ _ => rfl
  have hZ : ∀ i j : Fin 3, Z i j = if i = j then Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (3 : ℂ)) else 0 :=
    fun _ _ => rfl
  let ω : ℂ := whPhase 3 1
  have hω_norm : ‖ω‖ = 1 := whPhase_norm 3 1
  have hω_pow : ∀ k : ℕ, whPhase 3 (k : ℤ) = ω ^ k := by
    intro k
    induction k with
    | zero => simp [whPhase]
    | succ k ih =>
      rw [pow_succ, ← ih, ← whPhase_add]
      congr 1
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω_pow 3]
    simpa using whPhase_mul_d 3 (by norm_num) 1
  have hω_ne1 : ω ≠ 1 := by
    intro h
    have hre := congr_arg Complex.re h
    have hω_re : ω.re = -(1 / 2 : ℝ) := by
      have harg : ω = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
        simp only [ω, whPhase]; congr 1; push_cast; ring_nf
      rw [harg, Complex.exp_ofReal_mul_I_re]
      have h23 : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
      rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [hω_re, Complex.one_re] at hre
    norm_num at hre
  have hω_sum : ω + ω ^ 2 = -1 := by
    have hfac : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by
      calc (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 := by ring
        _ = 0 := by rw [hω3, sub_self]
    have h0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hω_ne1)
    linear_combination h0
  let s : ℝ := 1 / Real.sqrt 2
  have hs2 : s ^ 2 = 1 / 2 := by
    simp only [s, one_div, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let ψ : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![0, (s : ℂ), -(s : ℂ)]
  have hψ_norm : ‖ψ‖ = 1 := by
    have hsq : ‖ψ‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sum_norm_sq, Fin.sum_univ_three]
      simp only [ψ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_add, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs2]
      norm_num
    have h0 : 0 ≤ ‖ψ‖ := norm_nonneg _
    nlinarith
  have hmulVec_entry : ∀ a b : ℕ, ∀ i : Fin 3,
      ((X ^ a * Z ^ b).mulVec ψ.ofLp) i =
        ∑ j : Fin 3, (if i.val % 3 = (j.val + a) % 3 then (1 : ℂ) else 0) *
          (ω ^ (b * j.val) * ψ.ofLp j) := by
    intro a b i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [wh_X_pow_entry (by norm_num : 0 < 3) hX a i j, wh_Z_pow_entry hZ b j j, if_pos rfl,
        hω_pow]
      have hiff : (((i : ℕ) : ZMod 3) = ((j : ℕ) : ZMod 3) + (a : ZMod 3)) ↔
          i.val % 3 = (j.val + a) % 3 := by
        rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
        rfl
      rw [if_congr hiff rfl rfl]
      ring
    · intro k _ hne; rw [wh_Z_pow_entry hZ b k j, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hinner_eval : ∀ a b : ℕ,
      @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ a * Z ^ b).mulVec ψ.ofLp)) =
      ∑ i : Fin 3, star (ψ.ofLp i) *
        ∑ j : Fin 3, (if i.val % 3 = (j.val + a) % 3 then (1 : ℂ) else 0) *
          (ω ^ (b * j.val) * ψ.ofLp j) := by
    intro a b
    rw [inner_eq_sum_star_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change star (ψ.ofLp i) * ((X ^ a * Z ^ b).mulVec ψ.ofLp) i = _
    rw [hmulVec_entry a b i]
  have hs2c : (s : ℂ) * (s : ℂ) = 1 / 2 := by
    have : ((s ^ 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := congr_arg ((↑) : ℝ → ℂ) hs2
    simpa [sq] using this
  have hfid : ∀ x y : ZMod 3, (x, y) ≠ (0, 0) →
      ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ x.val * Z ^ y.val).mulVec ψ.ofLp))‖ ^ 2 =
        1 / ((3 : ℝ) + 1) := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd rfl hxy
    · -- (0, 1)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 0 * Z ^ 1).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) := by
        rw [hinner_eval 0 1, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination (1 / 2 : ℂ) * hω_sum + (ω + ω ^ 2) * hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 0 * Z ^ 1).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv]; norm_num
    · -- (0, 2)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 0 * Z ^ 2).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) := by
        rw [hinner_eval 0 2, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        have hω4 : ω ^ 4 = ω := by calc ω ^ 4 = ω ^ 3 * ω := by ring
          _ = ω := by rw [hω3, one_mul]
        linear_combination (1 / 2 : ℂ) * hω_sum + (1 / 2 : ℂ) * hω4 + (ω ^ 2 + ω ^ 4) * hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 0 * Z ^ 2).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv]; norm_num
    · -- (1, 0)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 0).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) := by
        rw [hinner_eval 1 0, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 0).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv]; norm_num
    · -- (1, 1)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 1).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) * ω := by
        rw [hinner_eval 1 1, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination ω * hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 1).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv, norm_mul, hω_norm, mul_one]; norm_num
    · -- (1, 2)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 2).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) * ω ^ 2 := by
        rw [hinner_eval 1 2, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination (ω ^ 2) * hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 1 * Z ^ 2).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv, norm_mul, norm_pow, hω_norm, one_pow, mul_one]; norm_num
    · -- (2, 0)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 2 * Z ^ 0).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) := by
        rw [hinner_eval 2 0, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 2 * Z ^ 0).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv]; norm_num
    · -- (2, 1)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 2 * Z ^ 1).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) * ω ^ 2 := by
        rw [hinner_eval 2 1, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination (ω ^ 2) * hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 2 * Z ^ 1).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv, norm_mul, norm_pow, hω_norm, one_pow, mul_one]; norm_num
    · -- (2, 2)
      have hv : @inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 2 * Z ^ 2).mulVec ψ.ofLp)) = -(1 / 2 : ℂ) * ω ^ 4 := by
        rw [hinner_eval 2 2, Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, ψ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, zero_add,
          star_neg, Complex.star_def, Complex.conj_ofReal]
        norm_num
        linear_combination (ω ^ 4) * hs2c
      change ‖@inner ℂ _ _ ψ (WithLp.toLp 2 ((X ^ 2 * Z ^ 2).mulVec ψ.ofLp))‖ ^ 2 = 1 / ((3 : ℝ) + 1)
      rw [hv, norm_mul, norm_pow, hω_norm, one_pow, mul_one]; norm_num
  obtain ⟨v, hv_norm, hv_equi⟩ :=
    ppl145_weyl_heisenberg_fiducial_generates_sic (by norm_num : 0 < 3) X Z hX hZ ψ hψ_norm hfid
  have htight := ppl145_sic_povm_tightness_characterization (by norm_num : 2 ≤ 3)
    (by norm_num : (1 : ℝ) / ((3 : ℝ) + 1) < 1) v hv_norm hv_equi
  exact ⟨v, hv_norm, hv_equi, htight.2.1⟩

private def hoggarWt (x : Fin 3 → ZMod 2) : ℕ :=
  (if x 0 = 0 then 0 else 1) + (if x 1 = 0 then 0 else 1) + (if x 2 = 0 then 0 else 1)

private def hoggarRe (x : Fin 3 → ZMod 2) : ℤ :=
  if hoggarWt x ≤ 1 then 1 else 0

private def hoggarIm (x : Fin 3 → ZMod 2) : ℤ :=
  if hoggarWt x = 0 ∨ hoggarWt x = 3 then 1 else 0

private def hoggarSignInt (s : ZMod 2) : ℤ := if s = 0 then 1 else -1

private def hoggarOvRe (a b : Fin 3 → ZMod 2) : ℤ :=
  ∑ j : Fin 3 → ZMod 2,
    hoggarSignInt (∑ r : Fin 3, b r * (j r + a r)) *
      (hoggarRe j * hoggarRe (j + a) + hoggarIm j * hoggarIm (j + a))

private def hoggarOvIm (a b : Fin 3 → ZMod 2) : ℤ :=
  ∑ j : Fin 3 → ZMod 2,
    hoggarSignInt (∑ r : Fin 3, b r * (j r + a r)) *
      (hoggarRe j * hoggarIm (j + a) - hoggarIm j * hoggarRe (j + a))

private lemma hoggar_norm_int :
    ∑ j : Fin 3 → ZMod 2, (hoggarRe j ^ 2 + hoggarIm j ^ 2) = 6 := by
  decide

private lemma hoggar_overlap_int :
    ∀ a b : Fin 3 → ZMod 2, (a, b) ≠ (0, 0) →
      hoggarOvRe a b ^ 2 + hoggarOvIm a b ^ 2 = 4 := by
  decide

/-- **Exact Hoggar 64-Line SIC-POVM in `d = 8` (`0` `native_decide`):**
Certified from the `S_3`-symmetric Gaussian-integer Hamming-weight fiducial
`ψ = (1+i, 1, 1, 0, 1, 0, 0, i) / √6` on `(ZMod 2)^3` under the 3-qubit Pauli group
`(ZMod 2)^3 × (ZMod 2)^3`, yielding 64 equiangular unit vectors in `ℂ^8` with pairwise squared
overlap `1/9` and exact POVM resolution of the identity. -/
theorem ppl145_sic_povm_dim8_hoggar :
    ∃ v : Fin (8 ^ 2) → EuclideanSpace ℂ (Fin 8),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((8 : ℝ) + 1)) ∧
      ((1 : ℂ) / (8 : ℂ)) •
        ∑ i : Fin (8 ^ 2), Matrix.of (fun a b : Fin 8 => v i a * star (v i b)) =
          (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  let s : ℝ := 1 / Real.sqrt 6
  have hs2 : s ^ 2 = 1 / 6 := by
    simp only [s, one_div, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  let ψ : EuclideanSpace ℂ (Fin 3 → ZMod 2) :=
    WithLp.toLp 2 fun x => ((s : ℂ)) * ((hoggarRe x : ℂ) + (hoggarIm x : ℂ) * Complex.I)
  have hψ_norm : ‖ψ‖ = 1 := by
    have hsq : ‖ψ‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sum_norm_sq]
      have hterm : ∀ x : Fin 3 → ZMod 2,
          ‖ψ x‖ ^ 2 = (1 / 6 : ℝ) * (((hoggarRe x ^ 2 + hoggarIm x ^ 2 : ℤ) : ℝ)) := by
        intro x
        simp only [ψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hs2,
          Complex.sq_norm, Complex.normSq_apply]
        simp; ring
      simp_rw [hterm, ← Finset.mul_sum]
      have hint : ∑ x : Fin 3 → ZMod 2, (((hoggarRe x ^ 2 + hoggarIm x ^ 2 : ℤ) : ℝ)) = 6 := by
        exact_mod_cast hoggar_norm_int
      rw [hint]; norm_num
    have h0 : 0 ≤ ‖ψ‖ := norm_nonneg _
    nlinarith
  have hfid : ∀ a b : Fin 3 → ZMod 2, (a, b) ≠ (0, 0) →
      ‖∑ j : Fin 3 → ZMod 2,
          star (ψ j) * (if ∑ r : Fin 3, b r * (j r + a r) = 0 then (1 : ℂ) else -1) *
            ψ (j + a)‖ ^ 2 =
        1 / ((2 ^ 3 : ℝ) + 1) := by
    intro a b hab
    have hsum_eq :
        ∑ j : Fin 3 → ZMod 2,
          star (ψ j) * (if ∑ r : Fin 3, b r * (j r + a r) = 0 then (1 : ℂ) else -1) *
            ψ (j + a) =
        ((1 / 6 : ℝ) : ℂ) * ((hoggarOvRe a b : ℂ) + (hoggarOvIm a b : ℂ) * Complex.I) := by
      have hs2c : (s : ℂ) * (s : ℂ) = (1 / 6 : ℂ) := by
        have : ((s ^ 2 : ℝ) : ℂ) = ((1 / 6 : ℝ) : ℂ) := congr_arg ((↑) : ℝ → ℂ) hs2
        simpa [sq] using this
      simp only [hoggarOvRe, hoggarOvIm]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsign : (if ∑ r : Fin 3, b r * (j r + a r) = 0 then (1 : ℂ) else -1) =
          (hoggarSignInt (∑ r : Fin 3, b r * (j r + a r)) : ℂ) := by
        by_cases h : ∑ r : Fin 3, b r * (j r + a r) = 0 <;> simp [hoggarSignInt, h]
      rw [hsign]
      simp only [ψ, star_mul', Complex.star_def, Complex.conj_ofReal, map_add, map_mul,
        map_intCast, Complex.conj_I]
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination
        ((hoggarSignInt (∑ r : Fin 3, b r * (j r + a r)) : ℂ) *
          (((hoggarRe j : ℂ) * (hoggarRe (j + a) : ℂ) + (hoggarIm j : ℂ) * (hoggarIm (j + a) : ℂ)) +
           ((hoggarRe j : ℂ) * (hoggarIm (j + a) : ℂ) - (hoggarIm j : ℂ) * (hoggarRe (j + a) : ℂ)) *
             Complex.I)) * hs2c -
        ((s : ℂ) * (s : ℂ) * (hoggarSignInt (∑ r : Fin 3, b r * (j r + a r)) : ℂ) *
          (hoggarIm j : ℂ) * (hoggarIm (j + a) : ℂ)) * hI2
    rw [hsum_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.intCast_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    have hint : ((hoggarOvRe a b : ℝ) ^ 2 + (hoggarOvIm a b : ℝ) ^ 2) = 4 := by
      exact_mod_cast hoggar_overlap_int a b hab
    have hsq2 : (hoggarOvRe a b : ℝ) * (hoggarOvRe a b : ℝ) +
        (hoggarOvIm a b : ℝ) * (hoggarOvIm a b : ℝ) = 4 := by
      simpa [sq] using hint
    rw [hsq2]; norm_num
  obtain ⟨v, hv_norm, hv_equi⟩ := ppl145_multiqubit_pauli_fiducial_generates_sic ψ hψ_norm hfid
  have hv_equi' : ∀ i j : Fin (8 ^ 2), i ≠ j →
      ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((8 : ℝ) + 1) := by
    intro i j hij
    have h := hv_equi i j hij
    norm_num at h ⊢
    exact h
  have htight := ppl145_sic_povm_tightness_characterization (by norm_num : 2 ≤ 8)
    (by norm_num : (1 : ℝ) / ((8 : ℝ) + 1) < 1) v hv_norm hv_equi'
  exact ⟨v, hv_norm, hv_equi', htight.2.1⟩

/-- **Unified Exact SIC-POVM Existence Theorem for `d ∈ {1, 2, 3, 8}`:**
Kernel-certified explicit SIC-POVMs with exact POVM resolution of the identity in dimensions
`1`, `2` (tetrahedral Bloch), `3` (Hesse), and `8` (Hoggar 64 lines), with `0` `native_decide`. -/
theorem ppl145_sic_povm_exists_dims_1_2_3_8 :
    ∀ d ∈ ({1, 2, 3, 8} : Finset ℕ),
      ∃ v : Fin (d ^ 2) → EuclideanSpace ℂ (Fin d),
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i j, i ≠ j → ‖@inner ℂ _ _ (v i) (v j)‖ ^ 2 = 1 / ((d : ℝ) + 1)) ∧
        ((1 : ℂ) / (d : ℂ)) •
          ∑ i : Fin (d ^ 2), Matrix.of (fun a b : Fin d => v i a * star (v i b)) =
            (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · simpa using ppl145_sic_povm_dim1
  · simpa using ppl145_sic_povm_dim2
  · simpa using ppl145_sic_povm_dim3
  · simpa using ppl145_sic_povm_dim8_hoggar

end PPL145
