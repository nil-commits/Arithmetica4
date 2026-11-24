/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# `Arith4Ext.QuantumLinearAlgebra`: Reusable Tier A Quantum Linear Algebra & Frame Theory Engine

Pure-Mathlib, zero-sorry, zero-custom-axiom library extending `Arithmetica4` with:
1. **Gram Matrices, Welch Bound & Gerzon Bounds:**
   - Gram matrix `G(v)_{ij} = ⟨v_i, v_j⟩` and frame operator `S(v) = ∑_i |v_i⟩⟨v_i|` (`PosSemidef`).
   - Exact frame potential duality `Tr(G^2) = Tr(S^2)` and **Welch Bound**
     `m^2 / d ≤ ∑_{i,j} |⟨v_i, v_j⟩|^2` plus max off-diagonal `|⟨v_i, v_j⟩|^2 ≥ (m - d)/(d(m - 1))`
     and Equiangular Tight Frame (ETF) equality characterization.
   - **Complex Gerzon Bound** (`m ≤ d^2`) and **Real Gerzon Bound** (`m ≤ d(d + 1)/2`) for
     equiangular unit vectors via linear independence of rank-1 projectors.
2. **Matrix Positivity, Hilbert–Schmidt Cauchy–Schwarz & Trace Inequalities:**
   - Spectral rank-1 decomposition for `PosSemidef` matrices over `ℂ`.
   - Hilbert–Schmidt Cauchy–Schwarz `‖Tr(Aᴴ B)‖^2 ≤ Tr(Aᴴ A) Tr(Bᴴ B)`.
   - **Schur Product Theorem** (`A.PosSemidef → B.PosSemidef → (hadamard A B).PosSemidef`).
   - Trace positivity `0 ≤ (A * B).trace.re` and upper bound `(A * B).trace.re ≤ Tr(A) Tr(B)`.
3. **Kronecker Product, Partial Transpose & Peres–Horodecki PPT Criterion:**
   - `posSemidef_kronecker`, `posSemidef_transpose`, partial transpose involution/trace/Hermiticity,
     `partialTranspose_kronecker`, and **Peres–Horodecki Theorem** (`separable ⇒ PPT`).
4. **Weyl–Heisenberg Clock / Shift Operators (`ZMod d`):**
   - Unitary shift `X` and clock `Z`, exact Weyl commutation `Z X = ω X Z`, and exact
     trace-orthogonality of the `d^2` displacement operators `D_{p,q} = X^p Z^q`.
-/

namespace Arith4Ext.QuantumLinearAlgebra

noncomputable section

open scoped BigOperators Matrix ComplexOrder

private lemma complex_sum_re {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-!
## 1. Gram Matrices, Frame Operators, Welch Bound & Gerzon Bounds
-/

section GramWelchGerzon

/-- Standard `ℂ`-linear inner product `⟨u, w⟩ = ∑ k, conj(u k) * w k` on `Fin d → ℂ`. -/
def cInner {d : ℕ} (u w : Fin d → ℂ) : ℂ :=
  ∑ k : Fin d, star (u k) * w k

/-- Squared Euclidean norm `‖u‖^2 = ∑ k, normSq (u k)` on `Fin d → ℂ`. -/
def cNormSq {d : ℕ} (u : Fin d → ℂ) : ℝ :=
  ∑ k : Fin d, Complex.normSq (u k)

theorem cInner_self_eq_cNormSq {d : ℕ} (u : Fin d → ℂ) :
    cInner u u = (cNormSq u : ℂ) := by
  dsimp only [cInner, cNormSq]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

theorem cNormSq_nonneg {d : ℕ} (u : Fin d → ℂ) : 0 ≤ cNormSq u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem cInner_conj_symm {d : ℕ} (u w : Fin d → ℂ) :
    star (cInner u w) = cInner w u := by
  dsimp only [cInner]
  rw [star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul, star_star, mul_comm]

/-- Gram matrix `G_{ij} = ⟨v_i, v_j⟩` of a family `v : Fin m → (Fin d → ℂ)`. -/
def gramMatrix {m d : ℕ} (v : Fin m → (Fin d → ℂ)) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => cInner (v i) (v j)

/-- Rank-1 outer product `|u⟩⟨u|` as a `d × d` complex matrix. -/
def rankOne {d : ℕ} (u : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => u a * star (u b)

/-- Frame operator `S = ∑_i |v_i⟩⟨v_i|` of a family `v : Fin m → (Fin d → ℂ)`. -/
def frameOp {m d : ℕ} (v : Fin m → (Fin d → ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i : Fin m, rankOne (v i)

private def vecMatrix {m d : ℕ} (v : Fin m → (Fin d → ℂ)) : Matrix (Fin d) (Fin m) ℂ :=
  Matrix.of fun k j => v j k

theorem gramMatrix_eq_conjTranspose_mul_self {m d : ℕ} (v : Fin m → (Fin d → ℂ)) :
    gramMatrix v = (vecMatrix v)ᴴ * vecMatrix v := by
  ext i j
  simp only [gramMatrix, vecMatrix, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, cInner]

theorem frameOp_eq_mul_conjTranspose {m d : ℕ} (v : Fin m → (Fin d → ℂ)) :
    frameOp v = vecMatrix v * (vecMatrix v)ᴴ := by
  ext a b
  simp only [frameOp, rankOne, Matrix.sum_apply, Matrix.of_apply, Matrix.mul_apply,
    vecMatrix, Matrix.conjTranspose_apply]

theorem gramMatrix_posSemidef {m d : ℕ} (v : Fin m → (Fin d → ℂ)) :
    (gramMatrix v).PosSemidef := by
  rw [gramMatrix_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self (vecMatrix v)

theorem frameOp_posSemidef {m d : ℕ} (v : Fin m → (Fin d → ℂ)) :
    (frameOp v).PosSemidef := by
  rw [frameOp_eq_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose (vecMatrix v)

theorem rankOne_posSemidef {d : ℕ} (u : Fin d → ℂ) : (rankOne u).PosSemidef := by
  let U : Matrix (Fin d) (Fin 1) ℂ := Matrix.of fun a _ => u a
  have h : rankOne u = U * Uᴴ := by
    ext a b
    simp [U, rankOne, Matrix.mul_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose U

theorem rankOne_trace_mul {d : ℕ} (u w : Fin d → ℂ) :
    (rankOne u * rankOne w).trace = (Complex.normSq (cInner u w) : ℂ) := by
  calc
    (rankOne u * rankOne w).trace
      = ∑ a : Fin d, ∑ b : Fin d, (u a * star (u b)) * (w b * star (w a)) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOne, Matrix.of_apply]
    _ = (∑ b : Fin d, star (u b) * w b) * (∑ a : Fin d, u a * star (w a)) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = cInner u w * star (cInner u w) := by
        dsimp only [cInner]
        congr 1
        rw [star_sum]
        refine Finset.sum_congr rfl fun a _ => by rw [star_mul, star_star, mul_comm]
    _ = (Complex.normSq (cInner u w) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj]

theorem trace_frameOp_eq {m d : ℕ} (v : Fin m → (Fin d → ℂ)) :
    (frameOp v).trace = ∑ i : Fin m, (cNormSq (v i) : ℂ) := by
  dsimp only [frameOp]
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    (rankOne (v i)).trace = ∑ a : Fin d, v i a * star (v i a) := by
      simp [Matrix.trace, rankOne]
    _ = (cNormSq (v i) : ℂ) := by
      rw [← cInner_self_eq_cNormSq]; dsimp only [cInner]
      refine Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem trace_frameOp_sq_eq_sum_normSq {m d : ℕ} (v : Fin m → (Fin d → ℂ)) :
    (frameOp v * frameOp v).trace =
      ∑ i : Fin m, ∑ j : Fin m, (Complex.normSq (cInner (v i) (v j)) : ℂ) := by
  dsimp only [frameOp]
  simp_rw [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, rankOne_trace_mul]

/-- Frobenius norm squared trace identity for any Hermitian `d × d` matrix `A`:
`(Aᴴ * A).trace.re = ∑ a b, ‖A a b‖^2`. -/
theorem trace_conjTranspose_mul_self_re {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) :
    (Aᴴ * A).trace.re = ∑ i : Fin m, ∑ j : Fin d, ‖A i j‖ ^ 2 := by
  calc
    (Aᴴ * A).trace.re = (∑ j : Fin d, ∑ i : Fin m, star (A i j) * A i j).re := by
      simp [Matrix.trace, Matrix.mul_apply]
    _ = ∑ j : Fin d, ∑ i : Fin m, (star (A i j) * A i j).re := by
      simp_rw [complex_sum_re]
    _ = ∑ i : Fin m, ∑ j : Fin d, ‖A i j‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Core Frobenius-Trace Cauchy–Schwarz / Welch inequality for any Hermitian `d × d` matrix `S`
(`d ≥ 1`): `(S.trace.re)^2 / d ≤ (S * S).trace.re`, with equality iff `S = (Tr(S)/d) • 1`. -/
theorem hermitian_trace_sq_div_le_trace_mul_self {d : ℕ} (hd : 1 ≤ d)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S.IsHermitian) :
    (S.trace.re) ^ 2 / (d : ℝ) ≤ (S * S).trace.re ∧
      ((S * S).trace.re = (S.trace.re) ^ 2 / (d : ℝ) ↔
        S = ((S.trace.re / (d : ℝ) : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  set t : ℝ := S.trace.re / (d : ℝ)
  set T : Matrix (Fin d) (Fin d) ℂ := S - (t : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hS_tr_im : S.trace.im = 0 := by
    have htr : star S.trace = S.trace := by
      conv_lhs => rw [← Matrix.trace_conjTranspose, hS.eq]
    have him := congrArg Complex.im htr
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith
  have hS_tr_eq : S.trace = (S.trace.re : ℂ) := Complex.ext rfl (by simp [hS_tr_im])
  have hT_herm : T.IsHermitian := by
    dsimp only [T]
    refine Matrix.IsHermitian.sub hS ?_
    ext a b
    by_cases h : a = b
    · subst h; simp
    · simp [h, eq_comm]
  have hT_sq : (Tᴴ * T).trace.re = (S * S).trace.re - (S.trace.re) ^ 2 / (d : ℝ) := by
    have hmul : Tᴴ * T = S * S - (2 * (t : ℂ)) • S + ((t : ℂ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [hT_herm.eq]
      dsimp only [T]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h1 : ((2 * (t : ℂ)) • S).trace.re = 2 * t * S.trace.re := by
      rw [Matrix.trace_smul, smul_eq_mul, hS_tr_eq]; norm_cast
    have h2 : (((t : ℂ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℂ)).trace.re = t ^ 2 * (d : ℝ) := by
      rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]; norm_cast
    rw [hmul, Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, h1, h2]
    dsimp only [t]
    field_simp [hd_ne]
    ring
  have hT_nonneg : 0 ≤ (Tᴴ * T).trace.re := by
    rw [trace_conjTranspose_mul_self_re]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : (S.trace.re) ^ 2 / (d : ℝ) ≤ (S * S).trace.re := by linarith
  refine ⟨hbound, ⟨fun heq => ?_, fun hS_eq => ?_⟩⟩
  · have hsum0 : ∑ a : Fin d, ∑ b : Fin d, ‖T a b‖ ^ 2 = 0 := by
      rw [← trace_conjTranspose_mul_self_re, hT_sq, heq, sub_self]
    have hT0 : T = 0 := by
      ext a b
      have ha : ∑ b : Fin d, ‖T a b‖ ^ 2 = 0 :=
        Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          |>.mp hsum0 a (Finset.mem_univ a)
      have hb : ‖T a b‖ ^ 2 = 0 :=
        Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)
          |>.mp ha b (Finset.mem_univ b)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
    exact sub_eq_zero.mp hT0
  · have hT0 : T = 0 := sub_eq_zero.mpr hS_eq
    have h0 : (Tᴴ * T).trace.re = 0 := by rw [hT0, Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re]
    linarith

/-- **Welch Frame Potential Bound:** for any `d ≥ 1` and any unit vectors `v : Fin m → (Fin d → ℂ)`:
`m^2 / d ≤ ∑_{i, j} ‖⟨v_i, v_j⟩‖^2`. -/
theorem welch_frame_potential_bound {m d : ℕ} (hd : 1 ≤ d) {v : Fin m → (Fin d → ℂ)}
    (hunit : ∀ i : Fin m, cNormSq (v i) = 1) :
    (m : ℝ) ^ 2 / (d : ℝ) ≤ ∑ i : Fin m, ∑ j : Fin m, ‖cInner (v i) (v j)‖ ^ 2 := by
  have htr : (frameOp v).trace.re = (m : ℝ) := by
    rw [trace_frameOp_eq]
    simp only [hunit, Complex.ofReal_one, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      mul_one, Complex.natCast_re]
  have hsq : ((frameOp v) * (frameOp v)).trace.re =
      ∑ i : Fin m, ∑ j : Fin m, ‖cInner (v i) (v j)‖ ^ 2 := by
    rw [trace_frameOp_sq_eq_sum_normSq]
    simp_rw [complex_sum_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hS := (hermitian_trace_sq_div_le_trace_mul_self hd (frameOp_posSemidef v).isHermitian).1
  rwa [htr, hsq] at hS

/-- **Equiangular Tight Frame (ETF) Equality Characterization:** equality holds in the Welch
frame potential bound iff `frameOp v = (m / d) • 1`. -/
theorem welch_etf_iff_frameOp_eq {m d : ℕ} (hd : 1 ≤ d) {v : Fin m → (Fin d → ℂ)}
    (hunit : ∀ i : Fin m, cNormSq (v i) = 1) :
    (∑ i : Fin m, ∑ j : Fin m, ‖cInner (v i) (v j)‖ ^ 2 = (m : ℝ) ^ 2 / (d : ℝ)) ↔
      frameOp v = (((m : ℝ) / (d : ℝ) : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have htr : (frameOp v).trace.re = (m : ℝ) := by
    rw [trace_frameOp_eq]
    simp only [hunit, Complex.ofReal_one, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      mul_one, Complex.natCast_re]
  have hsq : ((frameOp v) * (frameOp v)).trace.re =
      ∑ i : Fin m, ∑ j : Fin m, ‖cInner (v i) (v j)‖ ^ 2 := by
    rw [trace_frameOp_sq_eq_sum_normSq]
    simp_rw [complex_sum_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have heq := (hermitian_trace_sq_div_le_trace_mul_self hd (frameOp_posSemidef v).isHermitian).2
  rwa [htr, hsq] at heq

/-- **Welch Bound (Off-Diagonal Coherence Form):** for any `m > d ≥ 1` and unit vectors
`v : Fin m → (Fin d → ℂ)`, every uniform off-diagonal bound `M` satisfies
`(m - d) / (d * (m - 1)) ≤ M`, and there exists `i ≠ j` with `(m - d)/(d(m-1)) ≤ ‖⟨v_i, v_j⟩‖^2`. -/
theorem welch_bound {m d : ℕ} (hd : 1 ≤ d) (hmd : d < m) {v : Fin m → (Fin d → ℂ)}
    (hunit : ∀ i : Fin m, cNormSq (v i) = 1) :
    (∀ M : ℝ, (∀ i j : Fin m, i ≠ j → ‖cInner (v i) (v j)‖ ^ 2 ≤ M) →
      ((m : ℝ) - (d : ℝ)) / ((d : ℝ) * ((m : ℝ) - 1)) ≤ M) ∧
    (∃ i j : Fin m, i ≠ j ∧
      ((m : ℝ) - (d : ℝ)) / ((d : ℝ) * ((m : ℝ) - 1)) ≤ ‖cInner (v i) (v j)‖ ^ 2) := by
  have hm2 : 2 ≤ m := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hdiag : ∀ i : Fin m, ‖cInner (v i) (v i)‖ ^ 2 = 1 := by
    intro i
    rw [cInner_self_eq_cNormSq, hunit i, Complex.ofReal_one, norm_one, one_pow]
  have hsplit : ∑ i : Fin m, ∑ j : Fin m, ‖cInner (v i) (v j)‖ ^ 2 =
      (m : ℝ) + ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (· ≠ i), ‖cInner (v i) (v j)‖ ^ 2 := by
    have hrow : ∀ i : Fin m, ∑ j : Fin m, ‖cInner (v i) (v j)‖ ^ 2 =
        1 + ∑ j ∈ Finset.univ.filter (· ≠ i), ‖cInner (v i) (v j)‖ ^ 2 := by
      intro i
      have huniv : (Finset.univ : Finset (Fin m)) = insert i (Finset.univ.filter (· ≠ i)) := by
        ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
          true_iff]; exact eq_or_ne j i
      have hnot : i ∉ Finset.univ.filter (· ≠ i) := by simp
      conv_lhs => rw [huniv, Finset.sum_insert hnot, hdiag i]
    simp_rw [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      mul_one]
  have hfp := welch_frame_potential_bound hd hunit
  rw [hsplit] at hfp
  have hcard_off : ∀ i : Fin m, (Finset.univ.filter (· ≠ i)).card = m - 1 := by
    intro i
    have huniv : (Finset.univ : Finset (Fin m)) = insert i (Finset.univ.filter (· ≠ i)) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
        true_iff]; exact eq_or_ne j i
    have hnot : i ∉ Finset.univ.filter (· ≠ i) := by simp
    have hc := congrArg Finset.card huniv
    rw [Finset.card_fin, Finset.card_insert_of_notMem hnot] at hc
    omega
  have hmain : ∀ M : ℝ, (∀ i j : Fin m, i ≠ j → ‖cInner (v i) (v j)‖ ^ 2 ≤ M) →
      ((m : ℝ) - (d : ℝ)) / ((d : ℝ) * ((m : ℝ) - 1)) ≤ M := by
    intro M hM
    have hoff : ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (· ≠ i), ‖cInner (v i) (v j)‖ ^ 2 ≤
        (m : ℝ) * ((m : ℝ) - 1) * M := by
      calc
        ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (· ≠ i), ‖cInner (v i) (v j)‖ ^ 2
          ≤ ∑ i : Fin m, ∑ _j ∈ Finset.univ.filter (· ≠ i), M := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
            exact hM i j (Finset.mem_filter.mp hj).2.symm
        _ = ∑ _i : Fin m, ((m - 1 : ℕ) : ℝ) * M := by
            refine Finset.sum_congr rfl fun i _ => by rw [Finset.sum_const, hcard_off i, nsmul_eq_mul]
        _ = (m : ℝ) * ((m : ℝ) - 1) * M := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m),
              Nat.cast_one]
            ring
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have hcomb : (m : ℝ) ^ 2 / (d : ℝ) ≤ (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * M := by linarith
    rw [div_le_iff₀ (mul_pos hd_pos hm1_pos)]
    have h1 : (m : ℝ) * ((m : ℝ) - (d : ℝ)) ≤ (m : ℝ) * ((d : ℝ) * ((m : ℝ) - 1) * M) := by
      have hmul := mul_le_mul_of_nonneg_left hcomb hd_pos.le
      rw [mul_div_cancel₀ _ hd_pos.ne'] at hmul
      linarith
    have h2 : (m : ℝ) - (d : ℝ) ≤ (d : ℝ) * ((m : ℝ) - 1) * M :=
      le_of_mul_le_mul_left h1 hm_pos
    linarith
  refine ⟨hmain, ?_⟩
  by_contra hnone
  push Not at hnone
  set S_off : Finset (Fin m × Fin m) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hS_ne : S_off.Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Fin.ext_iff]⟩⟩
  set M₀ : ℝ := S_off.sup' hS_ne fun p => ‖cInner (v p.1) (v p.2)‖ ^ 2
  have hM₀_lt : M₀ < ((m : ℝ) - (d : ℝ)) / ((d : ℝ) * ((m : ℝ) - 1)) := by
    rw [Finset.sup'_lt_iff]
    intro p hp
    exact hnone p.1 p.2 (Finset.mem_filter.mp hp).2
  have hM₀_ub : ∀ i j : Fin m, i ≠ j → ‖cInner (v i) (v j)‖ ^ 2 ≤ M₀ := by
    intro i j hij
    have hmem : (i, j) ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    exact Finset.le_sup' (fun p : Fin m × Fin m => ‖cInner (v p.1) (v p.2)‖ ^ 2) hmem
  linarith [hmain M₀ hM₀_ub]

/-- Coordinate embedding `Hermitian d×d ℂ →ₗ[ℝ] (Fin d × Fin d → ℝ)` (diagonal + upper real +
strictly-lower imag). -/
private def hermitianEmbed (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] (Fin d × Fin d → ℝ) where
  toFun A p := if p.1 ≤ p.2 then (A p.1 p.2).re else (A p.1 p.2).im
  map_add' A B := by
    ext p
    by_cases h : p.1 ≤ p.2 <;> simp [h]
  map_smul' c A := by
    ext p
    by_cases h : p.1 ≤ p.2 <;> simp [h]

private lemma hermitianEmbed_inj_of_isHermitian {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (h0 : hermitianEmbed d A = 0) : A = 0 := by
  ext a b
  have he : ∀ p : Fin d × Fin d,
      (if p.1 ≤ p.2 then (A p.1 p.2).re else (A p.1 p.2).im) = 0 := fun p => congrFun h0 p
  have hherm : ∀ x y : Fin d, star (A y x) = A x y := fun x y => by
    have := congrFun (congrFun hA.eq x) y
    simpa [Matrix.conjTranspose_apply] using this
  apply Complex.ext
  · simp only [Matrix.zero_apply, Complex.zero_re]
    rcases le_total a b with hab | hba
    · simpa [hab] using he (a, b)
    · have hre_ba : (A b a).re = 0 := by simpa [hba] using he (b, a)
      have hre_eq : (A a b).re = (A b a).re := by
        simpa [Complex.star_def, Complex.conj_re] using (congrArg Complex.re (hherm a b)).symm
      rw [hre_eq, hre_ba]
  · simp only [Matrix.zero_apply, Complex.zero_im]
    rcases lt_trichotomy a b with hab | rfl | hba
    · have him_ba : (A b a).im = 0 := by
        have hnot : ¬ b ≤ a := not_le_of_gt hab
        simpa [hnot] using he (b, a)
      have him_eq : (A a b).im = -(A b a).im := by
        simpa [Complex.star_def, Complex.conj_im] using (congrArg Complex.im (hherm a b)).symm
      rw [him_eq, him_ba, neg_zero]
    · have him_eq : (A a a).im = -(A a a).im := by
        simpa [Complex.star_def, Complex.conj_im] using (congrArg Complex.im (hherm a a)).symm
      linarith
    · have hnot : ¬ a ≤ b := not_le_of_gt hba
      simpa [hnot] using he (a, b)

/-- **Complex Gerzon Bound (`m ≤ d^2`):** any family of `m` equiangular unit vectors in `ℂ^d`
(`‖⟨v_i, v_j⟩‖^2 = α < 1` for all `i ≠ j`) satisfies `m ≤ d^2`. -/
theorem gerzon_complex_bound {m d : ℕ} {v : Fin m → (Fin d → ℂ)}
    (hunit : ∀ i : Fin m, cNormSq (v i) = 1)
    {α : ℝ} (hα : α < 1) (hequi : ∀ i j : Fin m, i ≠ j → ‖cInner (v i) (v j)‖ ^ 2 = α) :
    m ≤ d ^ 2 := by
  by_cases hm0 : m = 0
  · subst hm0; exact Nat.zero_le _
  have hd_pos : 1 ≤ d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    subst hd_eq
    have h0 := hunit ⟨0, Nat.pos_of_ne_zero hm0⟩
    simp [cNormSq] at h0
  by_cases hm1 : m = 1
  · subst hm1; exact Nat.one_le_pow 2 d hd_pos
  have hα_nn : 0 ≤ α := by
    have hm2 : 2 ≤ m := by omega
    have := hequi ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    linarith [sq_nonneg ‖cInner (v ⟨0, by omega⟩) (v ⟨1, by omega⟩)‖]
  have hli : LinearIndependent ℝ (fun i : Fin m => hermitianEmbed d (rankOne (v i))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set M_c : Matrix (Fin d) (Fin d) ℂ := ∑ i : Fin m, (c i : ℂ) • rankOne (v i)
    have hMc_herm : M_c.IsHermitian := by
      dsimp only [M_c]
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      congr 1
      exact (rankOne_posSemidef (v i)).isHermitian.eq
    have hMc_zero : M_c = 0 := by
      apply hermitianEmbed_inj_of_isHermitian hMc_herm
      have hmap : hermitianEmbed d M_c = ∑ i : Fin m, c i • hermitianEmbed d (rankOne (v i)) := by
        dsimp only [M_c]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsmul : ((c i : ℂ) • rankOne (v i)) = (c i : ℝ) • rankOne (v i) := by
          ext a b; simp [Complex.real_smul]
        rw [hsmul, (hermitianEmbed d).map_smul]
      rw [hmap, hc]
    have htr_zero : (M_c * M_c).trace.re = 0 := by
      rw [hMc_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
    have htr_eq : (M_c * M_c).trace.re =
        (1 - α) * (∑ i : Fin m, c i ^ 2) + α * (∑ i : Fin m, c i) ^ 2 := by
      have hexp : M_c * M_c =
          ∑ i : Fin m, ∑ j : Fin m, ((c i * c j : ℝ) : ℂ) • (rankOne (v i) * rankOne (v j)) := by
        dsimp only [M_c]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        norm_cast
      rw [hexp, Matrix.trace_sum]
      simp_rw [Matrix.trace_sum, Matrix.trace_smul, rankOne_trace_mul, smul_eq_mul,
        complex_sum_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.normSq_eq_norm_sq, zero_mul, sub_zero]
      have hdiag_term : ∀ i : Fin m, ‖cInner (v i) (v i)‖ ^ 2 = 1 := fun i => by
        rw [cInner_self_eq_cNormSq, hunit i, Complex.ofReal_one, norm_one, one_pow]
      calc
        ∑ i : Fin m, ∑ j : Fin m, c i * c j * ‖cInner (v i) (v j)‖ ^ 2
          = ∑ i : Fin m, ∑ j : Fin m,
              ((if i = j then (1 - α) * (c i * c j) else 0) + α * (c i * c j)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            by_cases hij : i = j
            · subst hij; rw [if_pos rfl, hdiag_term i]; ring
            · rw [if_neg hij, hequi i j hij]; ring
        _ = (∑ i : Fin m, ∑ j : Fin m, if i = j then (1 - α) * (c i * c j) else 0) +
              ∑ i : Fin m, ∑ j : Fin m, α * (c i * c j) := by
            simp_rw [Finset.sum_add_distrib]
        _ = (1 - α) * (∑ i : Fin m, c i ^ 2) + α * (∑ i : Fin m, c i) ^ 2 := by
            congr 1
            · have hs1 : (∑ i : Fin m, ∑ j : Fin m, if i = j then (1 - α) * (c i * c j) else 0) =
                  (1 - α) * ∑ i : Fin m, c i ^ 2 := by
                have hinner : ∀ i : Fin m,
                    (∑ j : Fin m, if i = j then (1 - α) * (c i * c j) else 0) =
                      (1 - α) * c i ^ 2 := fun i => by
                  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i), sq]
                rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.mul_sum]
              exact hs1
            · rw [sq, Finset.sum_mul, Finset.mul_sum]
              simp_rw [Finset.mul_sum]
    have hsq0 : ∑ i : Fin m, c i ^ 2 = 0 := by
      have h1_pos : 0 < 1 - α := by linarith
      have h2_nn : 0 ≤ α * (∑ i : Fin m, c i) ^ 2 := mul_nonneg hα_nn (sq_nonneg _)
      have h3_nn : 0 ≤ (1 - α) * (∑ i : Fin m, c i ^ 2) :=
        mul_nonneg h1_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hprod0 : (1 - α) * (∑ i : Fin m, c i ^ 2) = 0 := by linarith
      exact (mul_eq_zero.mp hprod0).resolve_left h1_pos.ne'
    intro i
    exact sq_eq_zero_iff.mp
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _) |>.mp hsq0 i (Finset.mem_univ i))
  have hcard_le := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] at hcard_le
  simpa [sq] using hcard_le

/-- Real Euclidean inner product on `Fin d → ℝ`. -/
def rInner {d : ℕ} (u w : Fin d → ℝ) : ℝ :=
  ∑ k : Fin d, u k * w k

/-- **Real Gerzon Bound (`m ≤ d(d + 1)/2`):** any family of `m` equiangular unit vectors in `ℝ^d`
(`(rInner (v i) (v j))^2 = α < 1` for `i ≠ j`) satisfies `m ≤ d * (d + 1) / 2`. -/
theorem gerzon_real_bound {m d : ℕ} {v : Fin m → (Fin d → ℝ)}
    (hunit : ∀ i : Fin m, rInner (v i) (v i) = 1)
    {α : ℝ} (hα : α < 1) (hequi : ∀ i j : Fin m, i ≠ j → (rInner (v i) (v j)) ^ 2 = α) :
    m ≤ d * (d + 1) / 2 := by
  by_cases hm0 : m = 0
  · subst hm0; exact Nat.zero_le _
  have hd_pos : 1 ≤ d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    subst hd_eq
    have h0 := hunit ⟨0, Nat.pos_of_ne_zero hm0⟩
    simp [rInner] at h0
  by_cases hm1 : m = 1
  · subst hm1
    have h2 : 2 ≤ d * (d + 1) := by nlinarith
    exact Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
  have hα_nn : 0 ≤ α := by
    have hm2 : 2 ≤ m := by omega
    have := hequi ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    linarith [sq_nonneg (rInner (v ⟨0, by omega⟩) (v ⟨1, by omega⟩))]
  let upperIdx := { p : Fin d × Fin d // p.1 ≤ p.2 }
  let P_real : Fin m → (upperIdx → ℝ) := fun i p => v i p.1.1 * v i p.1.2
  have hli : LinearIndependent ℝ P_real := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsym_zero : ∀ a b : Fin d, ∑ i : Fin m, c i * (v i a * v i b) = 0 := by
      intro a b
      rcases le_total a b with hab | hba
      · have h := congrFun hc ⟨(a, b), hab⟩
        simpa [P_real] using h
      · have h := congrFun hc ⟨(b, a), hba⟩
        simpa [P_real, mul_comm] using h
    have hnorm_zero :
        (1 - α) * (∑ i : Fin m, c i ^ 2) + α * (∑ i : Fin m, c i) ^ 2 = 0 := by
      have hmat : ∑ a : Fin d, ∑ b : Fin d, (∑ i : Fin m, c i * (v i a * v i b)) ^ 2 = 0 := by
        simp [hsym_zero]
      have hexp : ∑ a : Fin d, ∑ b : Fin d, (∑ i : Fin m, c i * (v i a * v i b)) ^ 2 =
          ∑ i : Fin m, ∑ j : Fin m, c i * c j * (rInner (v i) (v j)) ^ 2 := by
        have h1 : ∀ a b : Fin d, (∑ i : Fin m, c i * (v i a * v i b)) ^ 2 =
            ∑ i : Fin m, ∑ j : Fin m, c i * c j * (v i a * v j a) * (v i b * v j b) := by
          intro a b
          rw [sq, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        simp_rw [h1]
        have hswap1 : ∀ a : Fin d,
            ∑ b : Fin d, ∑ i : Fin m, ∑ j : Fin m,
                c i * c j * (v i a * v j a) * (v i b * v j b) =
              ∑ i : Fin m, ∑ j : Fin m, ∑ b : Fin d,
                c i * c j * (v i a * v j a) * (v i b * v j b) := by
          intro a
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        simp_rw [hswap1]
        rw [Finset.sum_comm]
        have hswap2 :
            ∑ i : Fin m, ∑ a : Fin d, ∑ j : Fin m, ∑ b : Fin d,
                c i * c j * (v i a * v j a) * (v i b * v j b) =
              ∑ i : Fin m, ∑ j : Fin m, ∑ a : Fin d, ∑ b : Fin d,
                c i * c j * (v i a * v j a) * (v i b * v j b) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
        rw [hswap2]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        dsimp only [rInner]
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [Finset.mul_sum, mul_assoc]
      rw [hexp] at hmat
      have hid : ∑ i : Fin m, ∑ j : Fin m, c i * c j * (rInner (v i) (v j)) ^ 2 =
          (1 - α) * (∑ i : Fin m, c i ^ 2) + α * (∑ i : Fin m, c i) ^ 2 := by
        calc
          ∑ i : Fin m, ∑ j : Fin m, c i * c j * (rInner (v i) (v j)) ^ 2
            = ∑ i : Fin m, ∑ j : Fin m,
                ((if i = j then (1 - α) * (c i * c j) else 0) + α * (c i * c j)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              by_cases hij : i = j
              · subst hij; rw [if_pos rfl, hunit i, one_pow]; ring
              · rw [if_neg hij, hequi i j hij]; ring
          _ = (1 - α) * (∑ i : Fin m, c i ^ 2) + α * (∑ i : Fin m, c i) ^ 2 := by
              simp_rw [Finset.sum_add_distrib]
              congr 1
              · have hs1 : (∑ i : Fin m, ∑ j : Fin m, if i = j then (1 - α) * (c i * c j) else 0) =
                    (1 - α) * ∑ i : Fin m, c i ^ 2 := by
                  have hinner : ∀ i : Fin m,
                      (∑ j : Fin m, if i = j then (1 - α) * (c i * c j) else 0) =
                        (1 - α) * c i ^ 2 := fun i => by
                    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i), sq]
                  rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.mul_sum]
                exact hs1
              · rw [sq, Finset.sum_mul, Finset.mul_sum]
                simp_rw [Finset.mul_sum]
      linarith
    have hsq0 : ∑ i : Fin m, c i ^ 2 = 0 := by
      have h1_pos : 0 < 1 - α := by linarith
      have h2_nn : 0 ≤ α * (∑ i : Fin m, c i) ^ 2 := mul_nonneg hα_nn (sq_nonneg _)
      have h3_nn : 0 ≤ (1 - α) * (∑ i : Fin m, c i ^ 2) :=
        mul_nonneg h1_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hprod0 : (1 - α) * (∑ i : Fin m, c i ^ 2) = 0 := by linarith
      exact (mul_eq_zero.mp hprod0).resolve_left h1_pos.ne'
    intro i
    exact sq_eq_zero_iff.mp
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _) |>.mp hsq0 i (Finset.mem_univ i))
  have hcard_le := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_pi] at hcard_le
  have hupper_card : Fintype.card upperIdx = d * (d + 1) / 2 := by
    have hcard_eq : Fintype.card upperIdx =
        ∑ a : Fin d, (Finset.univ.filter (fun b : Fin d => a ≤ b)).card := by
      rw [Fintype.card_subtype]
      have hset : Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≤ p.2) =
          (Finset.univ.sigma (fun a : Fin d => Finset.univ.filter (fun b : Fin d => a ≤ b))).map
            (⟨fun x => (x.1, x.2), fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h => by cases h; rfl⟩ :
              (Σ _ : Fin d, Fin d) ↪ Fin d × Fin d) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_sigma,
          Sigma.exists]
        exact ⟨fun hab => ⟨a, b, hab, rfl⟩, by
          rintro ⟨a₁, b₁, hab, hEq⟩
          cases hEq
          exact hab⟩
      rw [hset, Finset.card_map, Finset.card_sigma]
    rw [hcard_eq]
    have hrow_card : ∀ a : Fin d, (Finset.univ.filter (fun b : Fin d => a ≤ b)).card = d - a := by
      intro a
      have hbij : Finset.univ.filter (fun b : Fin d => a ≤ b) =
          (Finset.univ : Finset (Fin (d - a.val))).map
            ⟨fun k => ⟨a.val + k.val, by rw [Nat.add_comm]; exact Nat.add_lt_of_lt_sub k.isLt⟩,
              fun _ _ h => Fin.ext (Nat.add_left_cancel (Fin.mk.inj h))⟩ := by
        ext ⟨b, hb⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.le_def]
        constructor
        · intro hab
          refine ⟨⟨b - a.val, by omega⟩, Fin.ext ?_⟩
          change a.val + (b - a.val) = b
          omega
        · rintro ⟨⟨k, hk⟩, hEq⟩
          have hval := congrArg Fin.val hEq
          change a.val + k = b at hval
          omega
      rw [hbij, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    simp_rw [hrow_card]
    rw [Fin.sum_univ_eq_sum_range]
    have htri : ∀ n : ℕ, ∑ x ∈ Finset.range n, (n - x) = n * (n + 1) / 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hsplit : ∑ x ∈ Finset.range (n + 1), (n + 1 - x) =
            (n + 1) + ∑ x ∈ Finset.range n, (n - x) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.sub_zero]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          omega
        rw [hsplit, ih]
        have hdiv2 : 2 * (n + 1) + n * (n + 1) = (n + 1) * (n + 1 + 1) := by ring
        omega
    exact htri d
  omega

end GramWelchGerzon

/-!
## 2. Spectral Decomposition, Hilbert–Schmidt Cauchy–Schwarz, Schur Product & Trace Inequalities
-/

section MatrixPositivity

/-- Hilbert–Schmidt inner product `⟨A, B⟩_{HS} = Tr(Aᴴ B)`. -/
def hsInner {m d : ℕ} (A B : Matrix (Fin m) (Fin d) ℂ) : ℂ :=
  (Aᴴ * B).trace

/-- **Hilbert–Schmidt Cauchy–Schwarz Inequality:**
`‖Tr(Aᴴ B)‖^2 ≤ Tr(Aᴴ A).re · Tr(Bᴴ B).re`. -/
theorem hsInner_cauchy_schwarz {m d : ℕ} (A B : Matrix (Fin m) (Fin d) ℂ) :
    ‖hsInner A B‖ ^ 2 ≤ (Aᴴ * A).trace.re * (Bᴴ * B).trace.re := by
  have htr : hsInner A B = ∑ i : Fin m, ∑ j : Fin d, star (A i j) * B i j := by
    simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    exact Finset.sum_comm
  rw [htr]
  have hnorm : ‖∑ i : Fin m, ∑ j : Fin d, star (A i j) * B i j‖ ≤
      ∑ i : Fin m, ∑ j : Fin d, ‖A i j‖ * ‖B i j‖ := by
    calc
      ‖∑ i : Fin m, ∑ j : Fin d, star (A i j) * B i j‖
        ≤ ∑ i : Fin m, ‖∑ j : Fin d, star (A i j) * B i j‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin m, ∑ j : Fin d, ‖star (A i j) * B i j‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ = ∑ i : Fin m, ∑ j : Fin d, ‖A i j‖ * ‖B i j‖ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_star]
  have hsq : ‖∑ i : Fin m, ∑ j : Fin d, star (A i j) * B i j‖ ^ 2 ≤
      (∑ i : Fin m, ∑ j : Fin d, ‖A i j‖ * ‖B i j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin d))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  have heq_sum : (∑ p : Fin m × Fin d, ‖A p.1 p.2‖ * ‖B p.1 p.2‖) =
      ∑ i : Fin m, ∑ j : Fin d, ‖A i j‖ * ‖B i j‖ := Fintype.sum_prod_type _
  have heq_A : (∑ p : Fin m × Fin d, ‖A p.1 p.2‖ ^ 2) =
      (Aᴴ * A).trace.re := by
    rw [Fintype.sum_prod_type, trace_conjTranspose_mul_self_re]
  have heq_B : (∑ p : Fin m × Fin d, ‖B p.1 p.2‖ ^ 2) =
      (Bᴴ * B).trace.re := by
    rw [Fintype.sum_prod_type, trace_conjTranspose_mul_self_re]
  rw [heq_sum, heq_A, heq_B] at hcs
  exact hsq.trans hcs

/-- Every eigenvalue of a `PosSemidef` Hermitian matrix is nonnegative. -/
theorem posSemidef_eigenvalues_nonneg {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (k : Fin d) :
    0 ≤ hA.isHermitian.eigenvalues k := by
  let b := hA.isHermitian.eigenvectorBasis
  let u : Fin d → ℂ := (b k).ofLp
  have hnorm1 : star u ⬝ᵥ u = 1 := by
    have h := b.orthonormal.1 k
    have hsq : ∑ i : Fin d, ‖(b k).ofLp i‖ ^ 2 = 1 := by
      have h1 := EuclideanSpace.norm_sq_eq (b k)
      rw [h, one_pow] at h1
      exact h1.symm
    have hdot : star u ⬝ᵥ u = ((∑ i : Fin d, ‖(b k).ofLp i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, u, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hdot, hsq, Complex.ofReal_one]
  have hmul : A.mulVec u = ((hA.isHermitian.eigenvalues k : ℝ) : ℂ) • u :=
    hA.isHermitian.mulVec_eigenvectorBasis k
  have hquad := hA.re_dotProduct_nonneg u
  rw [hmul, dotProduct_smul, hnorm1, smul_eq_mul, mul_one] at hquad
  simpa using hquad

/-- **Spectral Rank-1 Decomposition:** any Hermitian `A : Matrix (Fin d) (Fin d) ℂ` equals
`∑ k, (λ_k : ℂ) • rankOne (b k)`. -/
theorem isHermitian_eq_sum_rankOne {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) :
    A = ∑ k : Fin d, ((hA.eigenvalues k : ℝ) : ℂ) • rankOne ((hA.eigenvectorBasis k).ofLp) := by
  let b := hA.eigenvectorBasis
  ext a c
  let ec : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (Pi.single c 1)
  have hrepr : ec = ∑ k : Fin d, inner ℂ (b k) ec • b k := (b.sum_repr' ec).symm
  have hmul_ec : A.mulVec ec.ofLp =
      ∑ k : Fin d, inner ℂ (b k) ec • (A.mulVec (b k).ofLp) := by
    have hvec : ec.ofLp = ∑ k : Fin d, inner ℂ (b k) ec • (b k).ofLp := by
      simpa using congrArg WithLp.ofLp hrepr
    rw [hvec, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul]
  have hlhs : (A.mulVec ec.ofLp) a = A a c := by
    simp [ec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hrhs : (∑ k : Fin d, inner ℂ (b k) ec • (A.mulVec (b k).ofLp)) a =
      ∑ k : Fin d, ((hA.eigenvalues k : ℝ) : ℂ) *
        ((hA.eigenvectorBasis k).ofLp a * star ((hA.eigenvectorBasis k).ofLp c)) := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hinner : inner ℂ (b k) ec = star ((b k).ofLp c) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [ec, dotProduct, Pi.single_apply]
    have hmv : A.mulVec (b k).ofLp = ((hA.eigenvalues k : ℝ) : ℂ) • (b k).ofLp :=
      hA.mulVec_eigenvectorBasis k
    simp only [Pi.smul_apply, hinner, hmv, smul_eq_mul]
    dsimp only [b]
    ring
  rw [← hlhs, hmul_ec, hrhs]
  simp only [Matrix.sum_apply, Matrix.smul_apply, rankOne, Matrix.of_apply, smul_eq_mul]

/-- Hadamard (entrywise) product `(A ∘ B)_{ij} = A_{ij} * B_{ij}`. -/
def hadamard {m d : ℕ} (A B : Matrix (Fin m) (Fin d) ℂ) : Matrix (Fin m) (Fin d) ℂ :=
  Matrix.of fun i j => A i j * B i j

private lemma ofReal_nonneg_complex {x : ℝ} (hx : 0 ≤ x) : (0 : ℂ) ≤ (x : ℂ) := by
  simpa [Complex.le_def] using hx

private lemma posSemidef_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin d) (Fin d) ℂ) (hf : ∀ i ∈ s, (f i).PosSemidef) :
    (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Schur Product Theorem:** the Hadamard (entrywise) product of two `PosSemidef` matrices
is `PosSemidef`. -/
theorem posSemidef_hadamard {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (hadamard A B).PosSemidef := by
  let bA := hA.isHermitian.eigenvectorBasis
  let bB := hB.isHermitian.eigenvectorBasis
  have hA_eq := isHermitian_eq_sum_rankOne hA.isHermitian
  have hB_eq := isHermitian_eq_sum_rankOne hB.isHermitian
  have hhad : hadamard A B =
      ∑ k : Fin d, ∑ l : Fin d,
        ((hA.isHermitian.eigenvalues k * hB.isHermitian.eigenvalues l : ℝ) : ℂ) •
          rankOne (fun a => (bA k).ofLp a * (bB l).ofLp a) := by
    ext i j
    have hAi := congrFun (congrFun hA_eq i) j
    have hBi := congrFun (congrFun hB_eq i) j
    simp only [hadamard, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, rankOne,
      smul_eq_mul] at hAi hBi ⊢
    rw [hAi, hBi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    rw [star_mul]
    ring
  rw [hhad]
  refine posSemidef_finset_sum Finset.univ _ fun k _ => ?_
  refine posSemidef_finset_sum Finset.univ _ fun l _ => ?_
  have hkl : 0 ≤ hA.isHermitian.eigenvalues k * hB.isHermitian.eigenvalues l :=
    mul_nonneg (posSemidef_eigenvalues_nonneg hA k) (posSemidef_eigenvalues_nonneg hB l)
  exact (rankOne_posSemidef _).smul (ofReal_nonneg_complex hkl)

/-- **Trace Positivity:** if `A, B : Matrix (Fin d) (Fin d) ℂ` are `PosSemidef`, then
`0 ≤ (A * B).trace.re`. -/
theorem trace_mul_nonneg_of_posSemidef {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let bA := hA.isHermitian.eigenvectorBasis
  have hA_eq := isHermitian_eq_sum_rankOne hA.isHermitian
  have htr : (A * B).trace =
      ∑ k : Fin d, ((hA.isHermitian.eigenvalues k : ℝ) : ℂ) *
        (star (bA k).ofLp ⬝ᵥ B.mulVec (bA k).ofLp) := by
    conv_lhs => rw [hA_eq]
    rw [Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    simp [Matrix.trace, Matrix.mul_apply, rankOne, dotProduct, Matrix.mulVec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [bA]
    ring
  rw [htr, complex_sum_re]
  refine Finset.sum_nonneg fun k _ => ?_
  have hlam := posSemidef_eigenvalues_nonneg hA k
  have hquad := hB.re_dotProduct_nonneg (bA k).ofLp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hlam hquad

/-- **Trace Product Upper Bound:** for `PosSemidef` matrices `A, B`,
`(A * B).trace.re ≤ A.trace.re * B.trace.re`. -/
theorem trace_mul_le_trace_mul_trace_of_posSemidef {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace.re ≤ A.trace.re * B.trace.re := by
  let bA := hA.isHermitian.eigenvectorBasis
  have hA_tr : A.trace.re = ∑ k : Fin d, hA.isHermitian.eigenvalues k := by
    have htr := hA.isHermitian.trace_eq_sum_eigenvalues
    have hre := congrArg Complex.re htr
    rw [complex_sum_re] at hre
    exact hre.trans (Finset.sum_congr rfl fun k _ => Complex.ofReal_re _)
  have hlam_le : ∀ k : Fin d, hA.isHermitian.eigenvalues k ≤ A.trace.re := by
    intro k
    rw [hA_tr]
    exact Finset.single_le_sum (fun j _ => posSemidef_eigenvalues_nonneg hA j) (Finset.mem_univ k)
  have hdiff_psd : ((A.trace.re : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef := by
    have h1_eq : (1 : Matrix (Fin d) (Fin d) ℂ) =
        ∑ k : Fin d, rankOne ((bA k).ofLp) := by
      ext a c
      let ec : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (Pi.single c 1)
      have hrepr : ec = ∑ k : Fin d, inner ℂ (bA k) ec • bA k := (bA.sum_repr' ec).symm
      have heval : (1 : Matrix (Fin d) (Fin d) ℂ) a c = ec.ofLp a := by
        simp [ec, Matrix.one_apply, Pi.single_apply]
      rw [heval]
      have hvec : ec.ofLp = ∑ k : Fin d, inner ℂ (bA k) ec • (bA k).ofLp := by
        simpa using congrArg WithLp.ofLp hrepr
      rw [hvec, Finset.sum_apply]
      simp only [Matrix.sum_apply, rankOne, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hinner : inner ℂ (bA k) ec = star ((bA k).ofLp c) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [ec, dotProduct, Pi.single_apply]
      rw [hinner, mul_comm]
    have hsub_eq : (A.trace.re : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A =
        ∑ k : Fin d, ((A.trace.re - hA.isHermitian.eigenvalues k : ℝ) : ℂ) •
          rankOne ((bA k).ofLp) := by
      have h1s : (A.trace.re : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) =
          (A.trace.re : ℂ) • ∑ k : Fin d, rankOne ((bA k).ofLp) := congrArg _ h1_eq
      have hAs : A = ∑ k : Fin d, ((hA.isHermitian.eigenvalues k : ℝ) : ℂ) • rankOne ((bA k).ofLp) :=
        isHermitian_eq_sum_rankOne hA.isHermitian
      rw [h1s]
      conv_lhs => rhs; rw [hAs]
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.ofReal_sub, sub_smul]
    rw [hsub_eq]
    refine posSemidef_finset_sum Finset.univ _ fun k _ => ?_
    exact (rankOne_posSemidef _).smul (ofReal_nonneg_complex (sub_nonneg.mpr (hlam_le k)))
  have hnonneg := trace_mul_nonneg_of_posSemidef hdiff_psd hB
  have hB_tr_im : B.trace.im = 0 := by
    have htr : star B.trace = B.trace := by
      conv_lhs => rw [← Matrix.trace_conjTranspose, hB.isHermitian.eq]
    have him := congrArg Complex.im htr
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith
  have hB_tr_eq : B.trace = (B.trace.re : ℂ) := Complex.ext rfl (by simp [hB_tr_im])
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, Complex.sub_re] at hnonneg
  have hmul_re : ((A.trace.re : ℂ) * B.trace).re = A.trace.re * B.trace.re := by
    rw [hB_tr_eq]; norm_cast
  rw [hmul_re] at hnonneg
  linarith

end MatrixPositivity

/-!
## 3. Kronecker Product, Partial Transpose & Peres–Horodecki Criterion
-/

section KroneckerPartialTranspose

/-- Kronecker tensor product `A ⊗ B` on `Fin d₁ × Fin d₂`. -/
def kronecker {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ :=
  Matrix.of fun p q => A p.1 q.1 * B p.2 q.2

/-- Partial transpose `ρ^{T_B}` on `Fin d₁ × Fin d₂`: swaps the second-subsystem indices. -/
def partialTranspose {d₁ d₂ : ℕ} (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ :=
  Matrix.of fun p q => ρ (p.1, q.2) (q.1, p.2)

@[simp]
theorem partialTranspose_involutive {d₁ d₂ : ℕ}
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    partialTranspose (partialTranspose ρ) = ρ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [partialTranspose]

theorem partialTranspose_trace {d₁ d₂ : ℕ}
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    (partialTranspose ρ).trace = ρ.trace := by
  simp [Matrix.trace, partialTranspose]

theorem partialTranspose_add {d₁ d₂ : ℕ}
    (ρ₁ ρ₂ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    partialTranspose (ρ₁ + ρ₂) = partialTranspose ρ₁ + partialTranspose ρ₂ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [partialTranspose]

theorem partialTranspose_smul {d₁ d₂ : ℕ} (c : ℂ)
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    partialTranspose (c • ρ) = c • partialTranspose ρ := by
  ext ⟨a, b⟩ ⟨e, f⟩
  simp [partialTranspose]

theorem partialTranspose_isHermitian {d₁ d₂ : ℕ}
    {ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ} (hρ : ρ.IsHermitian) :
    (partialTranspose ρ).IsHermitian := by
  ext ⟨a, b⟩ ⟨c, d⟩
  have h1 := congrFun (congrFun hρ.eq (a, d)) (c, b)
  simpa [partialTranspose, Matrix.conjTranspose_apply] using h1

theorem partialTranspose_kronecker {d₁ d₂ : ℕ}
    (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    partialTranspose (kronecker A B) = kronecker A Bᵀ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [partialTranspose, kronecker, Matrix.transpose_apply]

theorem kronecker_trace {d₁ d₂ : ℕ}
    (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (kronecker A B).trace = A.trace * B.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, kronecker, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm

/-- Transpose preserves `PosSemidef` for complex matrices. -/
theorem posSemidef_transpose {d : ℕ} {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) :
    Bᵀ.PosSemidef := by
  let bB := hB.isHermitian.eigenvectorBasis
  have hB_eq := isHermitian_eq_sum_rankOne hB.isHermitian
  have hBT_eq : Bᵀ =
      ∑ k : Fin d, ((hB.isHermitian.eigenvalues k : ℝ) : ℂ) •
        rankOne (fun a => star ((bB k).ofLp a)) := by
    ext i j
    have hij := congrFun (congrFun hB_eq j) i
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, rankOne,
      Matrix.of_apply, smul_eq_mul, star_star] at hij ⊢
    rw [hij]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hBT_eq]
  exact posSemidef_finset_sum Finset.univ _ fun k _ =>
    (rankOne_posSemidef _).smul (ofReal_nonneg_complex (posSemidef_eigenvalues_nonneg hB k))

private theorem posSemidef_finset_sum_prod {d₁ d₂ : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) (hf : ∀ i ∈ s, (f i).PosSemidef) :
    (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Kronecker Positivity Theorem:** if `A` and `B` are `PosSemidef`, then `A ⊗ B` is
`PosSemidef`. -/
theorem posSemidef_kronecker {d₁ d₂ : ℕ} {A : Matrix (Fin d₁) (Fin d₁) ℂ}
    {B : Matrix (Fin d₂) (Fin d₂) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (kronecker A B).PosSemidef := by
  let bA := hA.isHermitian.eigenvectorBasis
  let bB := hB.isHermitian.eigenvectorBasis
  have hA_eq := isHermitian_eq_sum_rankOne hA.isHermitian
  have hB_eq := isHermitian_eq_sum_rankOne hB.isHermitian
  have hK_eq : kronecker A B =
      ∑ k : Fin d₁, ∑ l : Fin d₂,
        ((hA.isHermitian.eigenvalues k * hB.isHermitian.eigenvalues l : ℝ) : ℂ) •
          Matrix.of (fun (p q : Fin d₁ × Fin d₂) =>
            ((bA k).ofLp p.1 * (bB l).ofLp p.2) * star ((bA k).ofLp q.1 * (bB l).ofLp q.2)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    have hAi := congrFun (congrFun hA_eq i₁) j₁
    have hBi := congrFun (congrFun hB_eq i₂) j₂
    simp only [kronecker, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, rankOne,
      smul_eq_mul] at hAi hBi ⊢
    rw [hAi, hBi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    rw [star_mul]
    ring
  rw [hK_eq]
  refine posSemidef_finset_sum_prod Finset.univ _ fun k _ => ?_
  refine posSemidef_finset_sum_prod Finset.univ _ fun l _ => ?_
  have hkl : 0 ≤ hA.isHermitian.eigenvalues k * hB.isHermitian.eigenvalues l :=
    mul_nonneg (posSemidef_eigenvalues_nonneg hA k) (posSemidef_eigenvalues_nonneg hB l)
  have hrk : (Matrix.of (fun (p q : Fin d₁ × Fin d₂) =>
      ((bA k).ofLp p.1 * (bB l).ofLp p.2) *
        star ((bA k).ofLp q.1 * (bB l).ofLp q.2))).PosSemidef := by
    let U : Matrix (Fin d₁ × Fin d₂) (Fin 1) ℂ :=
      Matrix.of fun p _ => (bA k).ofLp p.1 * (bB l).ofLp p.2
    have hcol : Matrix.of (fun (p q : Fin d₁ × Fin d₂) =>
          ((bA k).ofLp p.1 * (bB l).ofLp p.2) *
            star ((bA k).ofLp q.1 * (bB l).ofLp q.2)) =
        U * Uᴴ := by
      ext p q
      simp [U, Matrix.mul_apply]
    rw [hcol]
    exact Matrix.posSemidef_self_mul_conjTranspose U
  exact hrk.smul (ofReal_nonneg_complex hkl)

/-- **Peres–Horodecki (1996) Separable ⇒ PPT Criterion:** every separable bipartite state
`ρ = ∑ r ∈ s, w_r • (A_r ⊗ B_r)` (`w_r ≥ 0`, `A_r, B_r` `PosSemidef`) satisfies
`(partialTranspose ρ).PosSemidef`. -/
theorem peres_horodecki_separable_ppt {d₁ d₂ : ℕ} {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (A : ι → Matrix (Fin d₁) (Fin d₁) ℂ) (B : ι → Matrix (Fin d₂) (Fin d₂) ℂ)
    (hw : ∀ r ∈ s, 0 ≤ w r)
    (hA : ∀ r ∈ s, (A r).PosSemidef) (hB : ∀ r ∈ s, (B r).PosSemidef) :
    (partialTranspose (∑ r ∈ s, (w r : ℂ) • kronecker (A r) (B r))).PosSemidef := by
  have hpt : partialTranspose (∑ r ∈ s, (w r : ℂ) • kronecker (A r) (B r)) =
      ∑ r ∈ s, (w r : ℂ) • kronecker (A r) (B r)ᵀ := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [partialTranspose, kronecker, Matrix.transpose_apply, Matrix.sum_apply]
  rw [hpt]
  refine posSemidef_finset_sum_prod s _ fun r hr => ?_
  exact (posSemidef_kronecker (hA r hr) (posSemidef_transpose (hB r hr))).smul
    (ofReal_nonneg_complex (hw r hr))

end KroneckerPartialTranspose

/-!
## 4. Weyl–Heisenberg Clock / Shift Operators (`ZMod d`)
-/

section WeylHeisenberg

/-- Primitive `d`-th root of unity `ω = exp(2πi / d)`. -/
def weylOmega (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

/-- Discrete Weyl shift matrix `X` on `ZMod d` (`X_{i, j} = 1` iff `i = j + 1`). -/
def weylShift (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

/-- Discrete Weyl clock matrix `Z = diag(ω^0, ω^1, ..., ω^{d-1})` on `ZMod d`. -/
def weylClock (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal fun j : ZMod d => (weylOmega d) ^ j.val

/-- Weyl–Heisenberg displacement operator `D_{p, q} = X^{p.val} Z^{q.val}`. -/
def weylDisplace (d : ℕ) [NeZero d] (p q : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (weylShift d) ^ p.val * (weylClock d) ^ q.val

theorem weylOmega_pow_ne_zero (d : ℕ) (k : ℕ) : (weylOmega d) ^ k ≠ 0 := by
  dsimp only [weylOmega]
  exact pow_ne_zero k (Complex.exp_ne_zero _)

theorem weylOmega_pow_self {d : ℕ} [NeZero d] : (weylOmega d) ^ d = 1 := by
  dsimp only [weylOmega]
  rw [← Complex.exp_nat_mul]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [mul_div_cancel₀ _ hd, Complex.exp_two_pi_mul_I]

theorem weylOmega_normSq_eq_one (d : ℕ) : Complex.normSq (weylOmega d) = 1 := by
  dsimp only [weylOmega]
  rw [show (2 * Real.pi * Complex.I / (d : ℂ)) = ((2 * Real.pi / (d : ℝ) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem star_weylOmega (d : ℕ) : star (weylOmega d) = (weylOmega d)⁻¹ := by
  have h1 : weylOmega d * star (weylOmega d) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, weylOmega_normSq_eq_one, Complex.ofReal_one]
  exact eq_inv_of_mul_eq_one_right h1

theorem weylOmega_pow_eq_of_modeq {d : ℕ} [NeZero d] {a b : ℕ} (h : a ≡ b [MOD d]) :
    (weylOmega d) ^ a = (weylOmega d) ^ b := by
  have hmod : ∀ n : ℕ, (weylOmega d) ^ n = (weylOmega d) ^ (n % d) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul, weylOmega_pow_self, one_pow, one_mul]
  rw [hmod a, hmod b, h]

theorem weylOmega_pow_val_add_one {d : ℕ} [NeZero d] (k : ZMod d) :
    (weylOmega d) ^ (k + 1).val = weylOmega d * (weylOmega d) ^ k.val := by
  have hmod : (k + 1).val ≡ k.val + 1 [MOD d] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    simp
  rw [weylOmega_pow_eq_of_modeq hmod, pow_succ']

theorem weylOmega_pow_ne_one {d r : ℕ} [NeZero d] (hr0 : 0 < r) (hrd : r < d) :
    (weylOmega d) ^ r ≠ 1 := by
  intro h1
  dsimp only [weylOmega] at h1
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h1
  rcases h1 with ⟨k, hk⟩
  have hd_ne : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have h2pi_ne : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdiv : (r : ℂ) / (d : ℂ) = (k : ℂ) := by
    have hmul : (r : ℂ) * (2 * Real.pi * Complex.I / (d : ℂ)) =
        (k : ℂ) * (2 * Real.pi * Complex.I) := hk
    have : ((r : ℂ) / (d : ℂ) - (k : ℂ)) * (2 * Real.pi * Complex.I) = 0 := by
      calc
        ((r : ℂ) / (d : ℂ) - (k : ℂ)) * (2 * Real.pi * Complex.I)
          = (r : ℂ) * (2 * Real.pi * Complex.I / (d : ℂ)) -
              (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2pi_ne)
  have hmul_c : (r : ℂ) = (k : ℂ) * (d : ℂ) := (div_eq_iff hd_ne).mp hdiv
  have hmul_z : (r : ℤ) = k * (d : ℤ) := by exact_mod_cast hmul_c
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk_le : k ≤ 0 := by omega
    have hkd : k * (d : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk_le (by omega)
    omega
  have hkd_ge : (d : ℤ) ≤ k * (d : ℤ) := le_mul_of_one_le_left (by omega) hk_pos
  omega

theorem weylShift_unitary (d : ℕ) [NeZero d] :
    weylShift d * (weylShift d)ᴴ = 1 ∧ (weylShift d)ᴴ * weylShift d = 1 := by
  constructor
  · ext i j
    simp only [Matrix.mul_apply, weylShift, Matrix.of_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply]
    have hterm : ∀ k : ZMod d,
        (if i = k + 1 then (1 : ℂ) else 0) * star (if j = k + 1 then (1 : ℂ) else 0) =
          if k = i - 1 then (if i = j then 1 else 0) else 0 := by
      intro k
      by_cases hk : k = i - 1
      · have hik : i = k + 1 := eq_add_of_sub_eq hk.symm
        by_cases hij : i = j
        · have hjk : j = k + 1 := hij ▸ hik
          rw [if_pos hk, if_pos hik, if_pos hjk, if_pos hij, star_one, mul_one]
        · have hnjk : j ≠ k + 1 := fun h => hij (hik.trans h.symm)
          rw [if_pos hk, if_pos hik, if_neg hnjk, if_neg hij, star_zero, mul_zero]
      · have hnik : i ≠ k + 1 := fun h => hk (eq_sub_of_add_eq h.symm)
        rw [if_neg hk, if_neg hnik, zero_mul]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  · ext i j
    simp only [Matrix.mul_apply, weylShift, Matrix.of_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply]
    have hterm : ∀ k : ZMod d,
        star (if k = i + 1 then (1 : ℂ) else 0) * (if k = j + 1 then (1 : ℂ) else 0) =
          if k = i + 1 then (if i = j then 1 else 0) else 0 := by
      intro k
      by_cases hk : k = i + 1
      · by_cases hij : i = j
        · have hkj : k = j + 1 := hk.trans (by rw [hij])
          rw [if_pos hk, if_pos hkj, if_pos hk, if_pos hij, star_one, mul_one]
        · have hnkj : k ≠ j + 1 := fun h => hij (add_right_cancel (hk.symm.trans h))
          rw [if_pos hk, if_neg hnkj, if_pos hk, if_neg hij, mul_zero]
      · rw [if_neg hk, if_neg hk, star_zero, zero_mul]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem weylClock_unitary (d : ℕ) [NeZero d] :
    weylClock d * (weylClock d)ᴴ = 1 ∧ (weylClock d)ᴴ * weylClock d = 1 := by
  constructor
  · ext i j
    simp only [weylClock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply, star_pow, star_weylOmega]
    split_ifs with h
    · rw [inv_pow, mul_inv_cancel₀ (weylOmega_pow_ne_zero d i.val)]
    · rfl
  · ext i j
    simp only [weylClock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply, star_pow, star_weylOmega]
    split_ifs with h
    · rw [inv_pow, inv_mul_cancel₀ (weylOmega_pow_ne_zero d i.val)]
    · rfl

/-- Exact Weyl commutation law `Z * X = ω • (X * Z)`. -/
theorem weyl_commutation {d : ℕ} [NeZero d] :
    weylClock d * weylShift d = (weylOmega d) • (weylShift d * weylClock d) := by
  ext i j
  simp only [weylClock, weylShift, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with hij
  · rw [hij, mul_one, one_mul, weylOmega_pow_val_add_one]
  · simp

theorem weylShift_pow_apply (d : ℕ) [NeZero d] (p : ℕ) (i j : ZMod d) :
    ((weylShift d) ^ p) i j = if i = j + (p : ZMod d) then 1 else 0 := by
  induction p generalizing i j with
  | zero =>
    simp [Matrix.one_apply]
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply]
    have hterm : ∀ k : ZMod d,
        ((weylShift d) ^ p) i k * weylShift d k j =
          if k = j + 1 then (if i = j + ((p + 1 : ℕ) : ZMod d) then 1 else 0) else 0 := by
      intro k
      rw [ih i k]
      simp only [weylShift, Matrix.of_apply]
      by_cases hk : k = j + 1
      · have heq : (i = k + (p : ZMod d)) ↔ (i = j + ((p + 1 : ℕ) : ZMod d)) := by
          rw [hk]; push_cast; simp only [add_assoc, add_comm 1 (p : ZMod d)]
        rw [if_pos hk, if_pos hk, mul_one]
        by_cases h1 : i = k + (p : ZMod d)
        · rw [if_pos h1, if_pos (heq.mp h1)]
        · rw [if_neg h1, if_neg (fun h => h1 (heq.mpr h))]
      · rw [if_neg hk, if_neg hk, mul_zero]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem weylClock_pow_eq (d : ℕ) [NeZero d] (q : ℕ) :
    (weylClock d) ^ q = Matrix.diagonal fun j : ZMod d => ((weylOmega d) ^ (q * j.val)) := by
  dsimp only [weylClock]
  rw [Matrix.diagonal_pow]
  ext i j
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · rw [Pi.pow_apply, ← pow_mul, mul_comm]
  · rfl

/-- General power Weyl commutation `Z^q * X^p = ω^{pq} • (X^p * Z^q)`. -/
theorem weyl_pow_commutation {d : ℕ} [NeZero d] (p q : ℕ) :
    (weylClock d) ^ q * (weylShift d) ^ p =
      ((weylOmega d) ^ (p * q)) • ((weylShift d) ^ p * (weylClock d) ^ q) := by
  ext i j
  rw [weylClock_pow_eq]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    weylShift_pow_apply]
  split_ifs with hij
  · rw [hij, mul_one, one_mul, ← pow_add]
    refine weylOmega_pow_eq_of_modeq ?_
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    simp
    ring
  · simp

private lemma unitary_mul {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Matrix α α ℂ} (hA : A * Aᴴ = 1 ∧ Aᴴ * A = 1) (hB : B * Bᴴ = 1 ∧ Bᴴ * B = 1) :
    (A * B) * (A * B)ᴴ = 1 ∧ (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  constructor
  · calc A * B * (Bᴴ * Aᴴ) = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.mul_assoc]
      _ = A * 1 * Aᴴ := by rw [hB.1]
      _ = 1 := by simpa using hA.1
  · calc Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp [Matrix.mul_assoc]
      _ = Bᴴ * 1 * B := by rw [hA.2]
      _ = 1 := by simpa using hB.2

private lemma unitary_pow {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℂ} (hA : A * Aᴴ = 1 ∧ Aᴴ * A = 1) (k : ℕ) :
    A ^ k * (A ^ k)ᴴ = 1 ∧ (A ^ k)ᴴ * A ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact unitary_mul ih hA

theorem weylDisplace_unitary (d : ℕ) [NeZero d] (p q : ZMod d) :
    weylDisplace d p q * (weylDisplace d p q)ᴴ = 1 ∧
      (weylDisplace d p q)ᴴ * weylDisplace d p q = 1 :=
  unitary_mul (unitary_pow (weylShift_unitary d) p.val)
    (unitary_pow (weylClock_unitary d) q.val)

theorem weylDisplace_apply {d : ℕ} [NeZero d] (p q i j : ZMod d) :
    weylDisplace d p q i j = if i = j + p then (weylOmega d) ^ (q.val * j.val) else 0 := by
  dsimp only [weylDisplace]
  rw [weylClock_pow_eq, Matrix.mul_diagonal, weylShift_pow_apply, ZMod.natCast_zmod_val]
  split_ifs <;> simp

/-- **Weyl–Heisenberg Trace Orthogonality:**
`Tr(D_{p₁, q₁}ᴴ D_{p₂, q₂}) = d` if `(p₁, q₁) = (p₂, q₂)` and `0` otherwise. -/
theorem weylDisplace_trace_ortho {d : ℕ} [NeZero d] (p₁ q₁ p₂ q₂ : ZMod d) :
    ((weylDisplace d p₁ q₁)ᴴ * weylDisplace d p₂ q₂).trace =
      if p₁ = p₂ ∧ q₁ = q₂ then (d : ℂ) else 0 := by
  have htr : ((weylDisplace d p₁ q₁)ᴴ * weylDisplace d p₂ q₂).trace =
      ∑ i : ZMod d, ∑ j : ZMod d,
        star (weylDisplace d p₁ q₁ j i) * weylDisplace d p₂ q₂ j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [htr]
  by_cases hp : p₁ = p₂
  · subst hp
    have hinner : ∀ i : ZMod d,
        ∑ j : ZMod d, star (weylDisplace d p₁ q₁ j i) * weylDisplace d p₁ q₂ j i =
          (weylOmega d) ^ ((q₂ - q₁).val * i.val) := by
      intro i
      have hterm : ∀ j : ZMod d,
          star (weylDisplace d p₁ q₁ j i) * weylDisplace d p₁ q₂ j i =
            if j = i + p₁ then
              star ((weylOmega d) ^ (q₁.val * i.val)) * (weylOmega d) ^ (q₂.val * i.val)
            else 0 := by
        intro j
        rw [weylDisplace_apply, weylDisplace_apply]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      have hmodeq : q₂.val * i.val ≡ (q₂ - q₁).val * i.val + q₁.val * i.val [MOD d] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        simp only [ZMod.natCast_zmod_val]
        ring
      rw [weylOmega_pow_eq_of_modeq hmodeq, pow_add, ← mul_assoc]
      have hcancel : star ((weylOmega d) ^ (q₁.val * i.val)) *
          (weylOmega d) ^ ((q₂ - q₁).val * i.val) * (weylOmega d) ^ (q₁.val * i.val) =
          (weylOmega d) ^ ((q₂ - q₁).val * i.val) := by
        have h1 : star ((weylOmega d) ^ (q₁.val * i.val)) *
            (weylOmega d) ^ (q₁.val * i.val) = 1 := by
          rw [star_pow, star_weylOmega, inv_pow, inv_mul_cancel₀ (weylOmega_pow_ne_zero d _)]
        calc
          star ((weylOmega d) ^ (q₁.val * i.val)) *
              (weylOmega d) ^ ((q₂ - q₁).val * i.val) * (weylOmega d) ^ (q₁.val * i.val)
            = (star ((weylOmega d) ^ (q₁.val * i.val)) * (weylOmega d) ^ (q₁.val * i.val)) *
                (weylOmega d) ^ ((q₂ - q₁).val * i.val) := by ring
          _ = (weylOmega d) ^ ((q₂ - q₁).val * i.val) := by rw [h1, one_mul]
      exact hcancel
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    by_cases hq : q₁ = q₂
    · subst hq
      simp only [sub_self, ZMod.val_zero, zero_mul, pow_zero, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul, mul_one, true_and, ↓reduceIte]
    · simp only [true_and, hq, ↓reduceIte]
      have hreidx : ∑ i : ZMod d, (weylOmega d) ^ ((q₂ - q₁).val * i.val) =
          ∑ k ∈ Finset.range d, ((weylOmega d) ^ (q₂ - q₁).val) ^ k := by
        have heq_sum : ∑ i : ZMod d, (weylOmega d) ^ ((q₂ - q₁).val * i.val) =
            ∑ k : Fin d, ((weylOmega d) ^ (q₂ - q₁).val) ^ (k : ℕ) := by
          let eFin : ZMod d ≃ Fin d :=
            ⟨fun i => ⟨i.val, ZMod.val_lt i⟩, fun k => (k : ZMod d),
              fun i => by simp,
              fun k => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt])⟩
          refine Fintype.sum_equiv eFin _ _ fun i => ?_
          rw [← pow_mul]
          rfl
        rw [heq_sum, Fin.sum_univ_eq_sum_range]
      rw [hreidx]
      have hr0 : 0 < (q₂ - q₁).val := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        apply hq
        have hsub0 : q₂ - q₁ = 0 := by
          rw [← ZMod.natCast_zmod_val (q₂ - q₁), h0, Nat.cast_zero]
        exact (sub_eq_zero.mp hsub0).symm
      have hrd : (q₂ - q₁).val < d := ZMod.val_lt _
      have hne1 : (weylOmega d) ^ (q₂ - q₁).val - 1 ≠ 0 :=
        sub_ne_zero.mpr (weylOmega_pow_ne_one hr0 hrd)
      have hgeom : ((weylOmega d) ^ (q₂ - q₁).val - 1) *
          ∑ k ∈ Finset.range d, ((weylOmega d) ^ (q₂ - q₁).val) ^ k = 0 := by
        have htel : ∀ M : ℕ, ((weylOmega d) ^ (q₂ - q₁).val - 1) *
            ∑ k ∈ Finset.range M, ((weylOmega d) ^ (q₂ - q₁).val) ^ k =
            ((weylOmega d) ^ (q₂ - q₁).val) ^ M - 1 := by
          intro M
          induction M with
          | zero => simp
          | succ M ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
        rw [htel d, ← pow_mul, mul_comm, pow_mul, weylOmega_pow_self, one_pow, sub_self]
      exact (mul_eq_zero.mp hgeom).resolve_left hne1
  · simp only [hp, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [weylDisplace_apply, weylDisplace_apply]
    split_ifs with h1 h2
    · exact False.elim (hp (add_left_cancel (h1.symm.trans h2)))
    · simp
    · simp
    · simp

end WeylHeisenberg

end

end Arith4Ext.QuantumLinearAlgebra
