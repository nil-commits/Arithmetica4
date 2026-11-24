import RHDirect.ArakelovCovolume
import RHDirect.UnitaryMassFormula
import RHDirect.SiegelWeilCore
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# RHDirect.Stage2SiegelReduction

Compact, self-contained, 0-`sorry`, 0-`axiom` Lean 4 formalization of the **Minkowski / Hermite
Lattice Reduction, Finite Lattice-Point Counting & Siegel Fundamental-Domain Bounds** core
underneath `RHDirect.ArakelovCovolume`, `RHDirect.UnitaryMassFormula`, and `RHDirect.SiegelWeilCore`.

## Contents

1. **Gram–Schmidt / Iwasawa `KAN` Orthogonalization & Hadamard Covolume Identity**:
   - Recursive Gram–Schmidt orthogonalization `gsVec` and upper-triangular unipotent coefficients
     `gsCoeff`, proving unconditional pairwise orthogonality (`gsVec_orthogonal`), expansion
     (`gs_expansion`), Pythagorean norm identity (`norm_sq_eq_sum_gsVec`), exact Gram determinant
     product (`det_gram_eq_prod_gsVec_norm_sq`), exact Iwasawa covolume formula
     (`covol_eq_prod_gsVec`), Hadamard's inequality (`hadamard_det_gram_le`, `covol_le_prod_norm`),
     and the orthogonal-projection lower bound on nonzero lattice combinations
     (`norm_ge_gsVec_of_max_nonzero`).

2. **Covolume Bridge, Minkowski's Convex-Body / Linear-Forms Theorem & Hermite First Minimum**:
   - Coordinate transport of any discrete `ℤ`-lattice `L : Submodule ℤ E` (`L ≠ ⊥`) in any
     finite-dimensional real inner product space `E` to a full-rank `IsZLattice ℝ` in `Fin (rk L) → ℝ`
     with exact equality `ArakelovCovolume.covol L = ZLattice.covolume L' volume`.
   - Direct application of Mathlib's `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
     to prove:
     * **Minkowski's Linear Forms Theorem** (strict & closed: `minkowski_linear_forms_strict`,
       `minkowski_linear_forms`),
     * **Minkowski's `L^∞` First-Minimum Theorem** (`minkowski_first_minimum_linf`,
       `minkowski_linf_pi`: `∃ v ∈ L \ {0}, ‖v‖_∞ ≤ covol(L)^(1/n)`),
     * **Euclidean Hermite First-Minimum Theorem** (`hermite_first_minimum`:
       `∃ v ∈ L \ {0}, ‖v‖₂ ≤ √r · covol(L)^(1/r)`).

3. **Shortest Nonzero Vector `lambda1`, Finiteness & Quantitative Ball/Siegel-Box Counting**:
   - Antilipschitz finiteness of `(L : Set E) ∩ Metric.closedBall 0 R` (`lattice_inter_closedBall_finite`)
     and Siegel boxes (`lattice_inter_box_finite`).
   - Existence of a shortest nonzero lattice vector (`exists_shortest_nonzero_vector`) attaining
     `lambda1 L`, with `0 < lambda1 L ≤ √(rk L) · covol(L)^(1 / rk L)`.
   - Exact integer box count (`card_int_box_eq`) and universal Haar-packing bounds:
     * Euclidean ball counting: `#(L ∩ B̄(0, R)) ≤ (1 + 2 R / λ₁(L))^(rk L)` (`ncard_lattice_closedBall_le`),
     * Siegel box counting: `#{v ∈ L | ∀ i, |⟨e_i, v⟩| ≤ B_i} ≤ ∏ i, (1 + 2 B_i / δ)`
       (`ncard_lattice_box_le`).

4. **Siegel Reduction & Successive-Minima Two-Sided Inequalities**:
   - `(C_diag, C_unip)`-Siegel-reduced bases (`IsSiegelReduced`), telescoping Iwasawa heights
     (`siegelReduced_gsNorm_telescope`), first-minimum lower bound
     (`siegelReduced_first_minimum_ge`), and orthogonality-defect bound
     (`siegelReduced_prod_norm_le_covol`).
   - Successive minima `succMin L k` (`k : Fin (rk L)`): monotonicity (`succMin_mono`),
     Hadamard lower bound `covol L ≤ ∏ k, succMin L k` (`covol_le_prod_succMin`), and two-sided
     Siegel-reduced equivalence between `‖b*_k‖`, `succMin L k`, and `covol L`
     (`siegelReduced_gsNorm_le_succMin`, `siegelReduced_prod_succMin_le_covol`).

5. **Bridges to `ArakelovCovolume`, `BostSlopeFiber`, `SiegelSetEnvelope` & `UnitaryMassFormula`**:
   - Minkowski lower bound on maximal slope (`neg_log_lambda1_le_muMax`,
     `slope_sub_half_log_rk_le_neg_log_lambda1`).
   - `BostSlopeFiber` covolume / first-minimum / Siegel-height comparison theorems
     (`bostSlopeFiber_lambda1_upper_of_slopeIneq`, `bostSlopeFiber_covolume_of_siegelReduced`).
   - Direct construction of `SiegelWeilCore.SiegelSetEnvelope` from lattice-reduction heights
     (`siegelSetEnvelope_of_lattice_height`) and theta-kernel integrability from lattice-ball
     counting (`thetaKernel_integrable_of_lattice_ball_bound`).
   - Automorphism-ball lower bound on `UnitaryMassFormula.genusMass` and fundamental-domain
     covolume (`genusMass_ge_of_lattice_ball_embed`, `measure_fd_ge_of_lattice_ball_embed`).
-/

open Module Submodule Finset Real MeasureTheory
open scoped BigOperators Matrix ENNReal

namespace RHDirect.Stage2SiegelReduction

noncomputable section

/-! ## Section 1: Gram–Schmidt / Iwasawa `KAN` Orthogonalization & Hadamard Covolume Identity -/

section GramSchmidt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Recursive Gram–Schmidt orthogonalization `v*_j` of a finite family `v : Fin r → E`. -/
def gsVec {r : ℕ} (v : Fin r → E) (j : Fin r) : E :=
  v j - ∑ i : Fin j.1,
    let ui := gsVec v ⟨i.1, lt_trans i.2 j.2⟩
    (inner ℝ ui (v j) / ‖ui‖ ^ 2) • ui
termination_by j.1
decreasing_by exact i.2

/-- Upper-triangular unit-diagonal Gram–Schmidt coefficient matrix `μ_{i, j}` (`gsCoeff v i j`). -/
def gsCoeff {r : ℕ} (v : Fin r → E) (i j : Fin r) : ℝ :=
  if i < j then inner ℝ (gsVec v i) (v j) / ‖gsVec v i‖ ^ 2
  else if i = j then 1
  else 0

lemma gsCoeff_self {r : ℕ} (v : Fin r → E) (j : Fin r) : gsCoeff v j j = 1 := by
  simp [gsCoeff]

lemma gsCoeff_of_lt {r : ℕ} (v : Fin r → E) {i j : Fin r} (h : i < j) :
    gsCoeff v i j = inner ℝ (gsVec v i) (v j) / ‖gsVec v i‖ ^ 2 := by
  simp [gsCoeff, h]

lemma gsCoeff_of_gt {r : ℕ} (v : Fin r → E) {i j : Fin r} (h : j < i) :
    gsCoeff v i j = 0 := by
  have h1 : ¬ i < j := not_lt.mpr h.le
  have h2 : i ≠ j := ne_of_gt h
  simp [gsCoeff, h1, h2]

/-- Explicit Gram–Schmidt expansion `v_j = v*_j + ∑_{i < j} μ_{ij} v*_i`. -/
theorem gs_expansion_lt {r : ℕ} (v : Fin r → E) (j : Fin r) :
    v j = gsVec v j + ∑ i : Fin j.1,
      gsCoeff v ⟨i.1, lt_trans i.2 j.2⟩ j • gsVec v ⟨i.1, lt_trans i.2 j.2⟩ := by
  have hdef : gsVec v j = v j - ∑ i : Fin j.1,
      (inner ℝ (gsVec v ⟨i.1, lt_trans i.2 j.2⟩) (v j) /
        ‖gsVec v ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2) • gsVec v ⟨i.1, lt_trans i.2 j.2⟩ := by
    rw [gsVec]
  have hsum : ∑ i : Fin j.1,
      gsCoeff v ⟨i.1, lt_trans i.2 j.2⟩ j • gsVec v ⟨i.1, lt_trans i.2 j.2⟩ =
      ∑ i : Fin j.1,
        (inner ℝ (gsVec v ⟨i.1, lt_trans i.2 j.2⟩) (v j) /
          ‖gsVec v ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2) • gsVec v ⟨i.1, lt_trans i.2 j.2⟩ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gsCoeff_of_lt v (show (⟨i.1, lt_trans i.2 j.2⟩ : Fin r) < j from i.2)]
  rw [hsum, hdef, sub_add_cancel]

/-- Full-sum upper-triangular Gram–Schmidt expansion `v_j = ∑_i μ_{ij} v*_i`. -/
theorem gs_expansion {r : ℕ} (v : Fin r → E) (j : Fin r) :
    v j = ∑ i : Fin r, gsCoeff v i j • gsVec v i := by
  rw [gs_expansion_lt v j]
  have hsplit : ∑ i : Fin r, gsCoeff v i j • gsVec v i =
      (∑ i ∈ Finset.univ.filter (fun i : Fin r => i < j), gsCoeff v i j • gsVec v i) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin r => ¬ i < j), gsCoeff v i j • gsVec v i) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin r => i < j), gsCoeff v i j • gsVec v i =
      ∑ i : Fin j.1, gsCoeff v ⟨i.1, lt_trans i.2 j.2⟩ j • gsVec v ⟨i.1, lt_trans i.2 j.2⟩ := by
    refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a _ b _ h; exact Fin.ext (Fin.mk.inj h)
    · intro b _
      refine ⟨⟨b.1, lt_trans b.2 j.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, by ext; rfl⟩
    · intro _ _; rfl
  have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin r => ¬ i < j), gsCoeff v i j • gsVec v i =
      gsVec v j := by
    rw [Finset.sum_eq_single j]
    · simp [gsCoeff_self]
    · intro i hi hij
      have hnotlt : ¬ i < j := (Finset.mem_filter.mp hi).2
      have hgt : j < i := lt_of_le_of_ne (not_lt.mp hnotlt) hij.symm
      simp [gsCoeff_of_gt v hgt]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_irrefl j⟩) h
  rw [h1, h2, add_comm]

/-- Unconditional pairwise orthogonality of Gram–Schmidt vectors `⟨v*_i, v*_j⟩ = 0` for `i ≠ j`. -/
theorem gsVec_orthogonal {r : ℕ} (v : Fin r → E) :
    ∀ {i j : Fin r}, i ≠ j → inner ℝ (gsVec v i) (gsVec v j) = 0 := by
  have hlt : ∀ n : ℕ, ∀ i j : Fin r, j.1 < n → i < j → inner ℝ (gsVec v i) (gsVec v j) = 0 := by
    intro n
    induction n with
    | zero => intro _ _ h; omega
    | succ n ih =>
      intro i j hj hij
      have hdef : gsVec v j = v j - ∑ k : Fin j.1,
          (inner ℝ (gsVec v ⟨k.1, lt_trans k.2 j.2⟩) (v j) /
            ‖gsVec v ⟨k.1, lt_trans k.2 j.2⟩‖ ^ 2) • gsVec v ⟨k.1, lt_trans k.2 j.2⟩ := by
        rw [gsVec]
      rw [hdef, inner_sub_right, inner_sum]
      have hterm : ∑ k : Fin j.1,
          inner ℝ (gsVec v i) ((inner ℝ (gsVec v ⟨k.1, lt_trans k.2 j.2⟩) (v j) /
            ‖gsVec v ⟨k.1, lt_trans k.2 j.2⟩‖ ^ 2) • gsVec v ⟨k.1, lt_trans k.2 j.2⟩) =
          (inner ℝ (gsVec v i) (v j) / ‖gsVec v i‖ ^ 2) * ‖gsVec v i‖ ^ 2 := by
        let i' : Fin j.1 := ⟨i.1, hij⟩
        rw [Finset.sum_eq_single i']
        · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        · intro k _ hki
          rw [real_inner_smul_right]
          have hne : (⟨k.1, lt_trans k.2 j.2⟩ : Fin r) ≠ i := by
            intro h; apply hki; exact Fin.ext (Fin.mk.inj h)
          have horth : inner ℝ (gsVec v i) (gsVec v ⟨k.1, lt_trans k.2 j.2⟩) = 0 := by
            rcases lt_or_gt_of_ne hne with hlt' | hgt'
            · rw [real_inner_comm]
              exact ih _ i (lt_of_lt_of_le hij (Nat.le_of_lt_succ hj)) hlt'
            · exact ih i _ (lt_of_lt_of_le k.2 (Nat.le_of_lt_succ hj)) hgt'
          rw [horth, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i') h
      rw [hterm]
      by_cases h0 : gsVec v i = 0
      · simp [h0]
      · have hn0 : ‖gsVec v i‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
        rw [div_mul_cancel₀ _ hn0, sub_self]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt (j.1 + 1) i j (Nat.lt_succ_self _) h
  · rw [real_inner_comm]
    exact hlt (i.1 + 1) j i (Nat.lt_succ_self _) h

/-- Each Gram–Schmidt vector `v*_j` lies in `span_ℝ {v_0, ..., v_j}`, and `v*_j - v_j` lies in
`span_ℝ {v_0, ..., v_{j-1}}`. -/
lemma gsVec_sub_mem_span_lt {r : ℕ} (v : Fin r → E) :
    ∀ j : Fin r, gsVec v j - v j ∈ Submodule.span ℝ {x | ∃ i : Fin r, i < j ∧ v i = x} := by
  have hmain : ∀ n : ℕ, ∀ j : Fin r, j.1 < n →
      gsVec v j - v j ∈ Submodule.span ℝ {x | ∃ i : Fin r, i < j ∧ v i = x} := by
    intro n
    induction n with
    | zero => intro _ h; omega
    | succ n ih =>
      intro j hj
      have hdef : gsVec v j - v j = -(∑ k : Fin j.1,
          (inner ℝ (gsVec v ⟨k.1, lt_trans k.2 j.2⟩) (v j) /
            ‖gsVec v ⟨k.1, lt_trans k.2 j.2⟩‖ ^ 2) • gsVec v ⟨k.1, lt_trans k.2 j.2⟩) := by
        conv_lhs => rw [gsVec]
        abel
      rw [hdef]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
      let k' : Fin r := ⟨k.1, lt_trans k.2 j.2⟩
      have hk_sub := ih k' (lt_of_lt_of_le k.2 (Nat.le_of_lt_succ hj))
      have hmono : Submodule.span ℝ {x | ∃ i : Fin r, i < k' ∧ v i = x} ≤
          Submodule.span ℝ {x | ∃ i : Fin r, i < j ∧ v i = x} :=
        Submodule.span_mono fun x ⟨i, hik, hix⟩ => ⟨i, lt_trans hik k.2, hix⟩
      have hvk : v k' ∈ Submodule.span ℝ {x | ∃ i : Fin r, i < j ∧ v i = x} :=
        Submodule.subset_span ⟨k', k.2, rfl⟩
      have hsum : (gsVec v k' - v k') + v k' = gsVec v k' := sub_add_cancel _ _
      rw [← hsum]
      exact Submodule.add_mem _ (hmono hk_sub) hvk
  intro j
  exact hmain (j.1 + 1) j (Nat.lt_succ_self _)

/-- Linear independence of `v` guarantees every Gram–Schmidt vector `v*_j` is nonzero. -/
theorem gsVec_ne_zero_of_linearIndependent {r : ℕ} {v : Fin r → E}
    (hv : LinearIndependent ℝ v) (j : Fin r) : gsVec v j ≠ 0 := by
  intro h0
  have hmem := gsVec_sub_mem_span_lt v j
  rw [h0, zero_sub] at hmem
  have hvj : v j ∈ Submodule.span ℝ {x | ∃ i : Fin r, i < j ∧ v i = x} := by
    simpa using Submodule.neg_mem _ hmem
  have hsub : {x | ∃ i : Fin r, i < j ∧ v i = x} ⊆ v '' (Set.univ \ {j}) := by
    rintro x ⟨i, hij, rfl⟩
    exact ⟨i, ⟨Set.mem_univ i, ne_of_lt hij⟩, rfl⟩
  have hmem2 : v j ∈ Submodule.span ℝ (v '' (Set.univ \ {j})) :=
    Submodule.span_mono hsub hvj
  exact (linearIndependent_iff_notMem_span.mp hv j) hmem2

/-- Pythagorean expansion `‖v_j‖² = ‖v*_j‖² + ∑_{i < j} μ_{ij}² ‖v*_i‖²`. -/
theorem norm_sq_eq_sum_gsVec {r : ℕ} (v : Fin r → E) (j : Fin r) :
    ‖v j‖ ^ 2 = ‖gsVec v j‖ ^ 2 +
      ∑ i : Fin j.1, (gsCoeff v ⟨i.1, lt_trans i.2 j.2⟩ j) ^ 2 *
        ‖gsVec v ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, gs_expansion v j, sum_inner]
  have hsum : ∑ i : Fin r, inner ℝ (gsCoeff v i j • gsVec v i) (∑ k : Fin r, gsCoeff v k j • gsVec v k) =
      ∑ i : Fin r, (gsCoeff v i j) ^ 2 * ‖gsVec v i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
    · intro k _ hki
      rw [real_inner_smul_left, real_inner_smul_right, gsVec_orthogonal v hki.symm, mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsum]
  have hsplit : ∑ i : Fin r, (gsCoeff v i j) ^ 2 * ‖gsVec v i‖ ^ 2 =
      (∑ i ∈ Finset.univ.filter (fun i : Fin r => i < j), (gsCoeff v i j) ^ 2 * ‖gsVec v i‖ ^ 2) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin r => ¬ i < j), (gsCoeff v i j) ^ 2 * ‖gsVec v i‖ ^ 2) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin r => i < j), (gsCoeff v i j) ^ 2 * ‖gsVec v i‖ ^ 2 =
      ∑ i : Fin j.1, (gsCoeff v ⟨i.1, lt_trans i.2 j.2⟩ j) ^ 2 *
        ‖gsVec v ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2 := by
    refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a _ b _ h; exact Fin.ext (Fin.mk.inj h)
    · intro b _
      refine ⟨⟨b.1, lt_trans b.2 j.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, by ext; rfl⟩
    · intro _ _; rfl
  have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin r => ¬ i < j), (gsCoeff v i j) ^ 2 * ‖gsVec v i‖ ^ 2 =
      ‖gsVec v j‖ ^ 2 := by
    rw [Finset.sum_eq_single j]
    · simp [gsCoeff_self]
    · intro i hi hij
      have hgt : j < i := lt_of_le_of_ne (not_lt.mp (Finset.mem_filter.mp hi).2) hij.symm
      simp [gsCoeff_of_gt v hgt]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_irrefl j⟩) h
  rw [h1, h2, add_comm]

/-- Gram–Schmidt contraction: `‖v*_j‖ ≤ ‖v_j‖`. -/
theorem gsVec_norm_le {r : ℕ} (v : Fin r → E) (j : Fin r) : ‖gsVec v j‖ ≤ ‖v j‖ := by
  have hsq : ‖gsVec v j‖ ^ 2 ≤ ‖v j‖ ^ 2 := by
    rw [norm_sq_eq_sum_gsVec v j]
    have hnn : 0 ≤ ∑ i : Fin j.1, (gsCoeff v ⟨i.1, lt_trans i.2 j.2⟩ j) ^ 2 *
        ‖gsVec v ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  nlinarith [norm_nonneg (gsVec v j), norm_nonneg (v j)]

/-- **Exact Iwasawa / Gram–Schmidt Determinant Identity**:
`det(Gram v) = ∏ j, ‖v*_j‖²`. -/
theorem det_gram_eq_prod_gsVec_norm_sq {r : ℕ} (v : Fin r → E) :
    (Matrix.gram ℝ v).det = ∏ j : Fin r, ‖gsVec v j‖ ^ 2 := by
  let U : Matrix (Fin r) (Fin r) ℝ := Matrix.of (fun i j => gsCoeff v i j)
  have hvU : v = fun j => ∑ i, U i j • gsVec v i := funext (gs_expansion v)
  have hU_tri : U.BlockTriangular id := by
    intro i j hij
    exact gsCoeff_of_gt v hij
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_tri]
    exact Finset.prod_eq_one fun i _ => gsCoeff_self v i
  have hGdiag : Matrix.gram ℝ (gsVec v) = Matrix.diagonal (fun j => ‖gsVec v j‖ ^ 2) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; exact real_inner_self_eq_norm_sq _
    · exact gsVec_orthogonal v h
  conv_lhs => rw [hvU]
  rw [RHDirect.ArakelovCovolume.gram_sum_smul_eq_transpose_mul (gsVec v) U,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUdet, hGdiag, Matrix.det_diagonal]
  ring

/-- **Hadamard's Inequality**: `√(det Gram v) ≤ ∏ j, ‖v_j‖`. -/
theorem hadamard_det_gram_le {r : ℕ} (v : Fin r → E) :
    Real.sqrt (Matrix.gram ℝ v).det ≤ ∏ j : Fin r, ‖v j‖ := by
  rw [det_gram_eq_prod_gsVec_norm_sq v,
    show (∏ j : Fin r, ‖gsVec v j‖ ^ 2) = (∏ j : Fin r, ‖gsVec v j‖) ^ 2 by rw [Finset.prod_pow],
    Real.sqrt_sq (Finset.prod_nonneg fun j _ => norm_nonneg _)]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => gsVec_norm_le v j)

/-- **Exact Iwasawa Diagonal-Height Covolume Formula**:
for any `ℤ`-basis `b` of a discrete lattice `L ⊂ E`, `covol L = ∏ j, ‖b*_j‖`. -/
theorem covol_eq_prod_gsVec [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) :
    RHDirect.ArakelovCovolume.covol L = ∏ j : Fin r, ‖gsVec (fun i => (b i : E)) j‖ := by
  rw [RHDirect.ArakelovCovolume.covol_eq_sqrt_det_gram L b, det_gram_eq_prod_gsVec_norm_sq,
    show (∏ j : Fin r, ‖gsVec (fun i => (b i : E)) j‖ ^ 2) =
      (∏ j : Fin r, ‖gsVec (fun i => (b i : E)) j‖) ^ 2 by rw [Finset.prod_pow],
    Real.sqrt_sq (Finset.prod_nonneg fun j _ => norm_nonneg _)]

/-- **Hadamard Lattice Covolume Upper Bound**:
any `rk L` `ℝ`-linearly independent vectors `x` in `L` satisfy `covol L ≤ ∏ j, ‖x_j‖`. -/
theorem covol_le_prod_norm [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (x : Fin r → E) (hxL : ∀ i, x i ∈ L) (hli : LinearIndependent ℝ x)
    (hr : r = RHDirect.ArakelovCovolume.rk L) :
    RHDirect.ArakelovCovolume.covol L ≤ ∏ j : Fin r, ‖x j‖ :=
  (RHDirect.ArakelovCovolume.covol_le_sqrt_det_gram x hxL hli (by simpa using hr)).trans
    (hadamard_det_gram_le x)

/-- **Orthogonal-Projection Lower Bound on Linear Combinations**:
if `k` is the top nonzero index (`∀ j > k, c j = 0`), then `|c k| * ‖v*_k‖ ≤ ‖∑ j, c j • v j‖`. -/
theorem norm_ge_gsVec_of_max_nonzero {r : ℕ} (v : Fin r → E) (c : Fin r → ℝ) (k : Fin r)
    (htop : ∀ j : Fin r, k < j → c j = 0) :
    |c k| * ‖gsVec v k‖ ≤ ‖∑ j : Fin r, c j • v j‖ := by
  by_cases h0 : gsVec v k = 0
  · simp [h0, norm_nonneg]
  have hinner : inner ℝ (gsVec v k) (∑ j : Fin r, c j • v j) = c k * ‖gsVec v k‖ ^ 2 := by
    rw [inner_sum, Finset.sum_eq_single k]
    · rw [real_inner_smul_right, gs_expansion v k, inner_sum, Finset.sum_eq_single k]
      · rw [gsCoeff_self, one_smul, real_inner_self_eq_norm_sq]
      · intro i _ hik
        rw [real_inner_smul_right, gsVec_orthogonal v hik.symm, mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with hlt | hgt
      · rw [real_inner_smul_right, gs_expansion v j, inner_sum]
        have hzero : ∑ i : Fin r, inner ℝ (gsVec v k) (gsCoeff v i j • gsVec v i) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hik : i = k
          · subst hik
            rw [gsCoeff_of_gt v hlt, zero_smul, inner_zero_right]
          · rw [real_inner_smul_right, gsVec_orthogonal v (Ne.symm hik), mul_zero]
        rw [hzero, mul_zero]
      · rw [htop j hgt, zero_smul, inner_zero_right]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hcs : |inner ℝ (gsVec v k) (∑ j : Fin r, c j • v j)| ≤
      ‖gsVec v k‖ * ‖∑ j : Fin r, c j • v j‖ := abs_real_inner_le_norm _ _
  rw [hinner, abs_mul, abs_of_nonneg (sq_nonneg ‖gsVec v k‖)] at hcs
  have hpos : 0 < ‖gsVec v k‖ := norm_pos_iff.mpr h0
  nlinarith

/-- Every nonzero vector in a discrete lattice `L` with basis `b` has norm at least `‖b*_k‖` for
its top nonzero coordinate index `k`. -/
theorem exists_gsVec_norm_le_of_mem_ne_zero {r : ℕ} {L : Submodule ℤ E} (b : Basis (Fin r) ℤ L)
    {v : E} (hvL : v ∈ L) (hv0 : v ≠ 0) :
    ∃ k : Fin r, ‖gsVec (fun i => (b i : E)) k‖ ≤ ‖v‖ := by
  let c : Fin r → ℤ := fun i => b.repr ⟨v, hvL⟩ i
  have hne : ∃ i : Fin r, c i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv0
    have h1 := congrArg Subtype.val (b.sum_repr ⟨v, hvL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    exact Finset.sum_eq_zero fun i _ => by simp [c, hall i]
  let S : Finset (Fin r) := Finset.univ.filter fun i => c i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let k : Fin r := S.max' hS
  have hk_mem : k ∈ S := Finset.max'_mem S hS
  have hck : c k ≠ 0 := (Finset.mem_filter.mp hk_mem).2
  have htop : ∀ j : Fin r, k < j → (c j : ℝ) = 0 := by
    intro j hj
    by_contra hcj
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, by exact_mod_cast hcj⟩
    exact not_lt.mpr (Finset.le_max' S j hjS) hj
  have hv_eq : v = ∑ j : Fin r, (c j : ℝ) • (b j : E) := by
    have h1 := congrArg Subtype.val (b.sum_repr ⟨v, hvL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  have hge := norm_ge_gsVec_of_max_nonzero (fun i => (b i : E)) (fun i => (c i : ℝ)) k htop
  rw [← hv_eq] at hge
  have h1 : (1 : ℝ) ≤ |(c k : ℝ)| := by
    have : (1 : ℤ) ≤ |c k| := Int.one_le_abs hck
    exact_mod_cast this
  exact ⟨k, le_trans (le_mul_of_one_le_left (norm_nonneg _) h1) hge⟩

end GramSchmidt

/-! ## Section 2: Covolume Bridge, Minkowski's Convex-Body Theorem & Hermite First Minimum -/

section MinkowskiPi

/-- **Strict Minkowski Linear-Forms Theorem on `Fin n → ℝ`** (directly via Mathlib's
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`):
for any full-rank `ℤ`-lattice `L ⊂ Fin n → ℝ` and positive box half-widths `a : Fin n → ℝ`
with `ZLattice.covolume L volume < ∏ i, a i`, there exists `v ∈ L \ {0}` with `∀ i, |v i| < a i`. -/
theorem minkowski_linear_forms_pi_strict {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hcov : ZLattice.covolume L volume < ∏ i : Fin n, a i) :
    ∃ v : Fin n → ℝ, v ∈ L ∧ v ≠ 0 ∧ ∀ i : Fin n, |v i| < a i := by
  have hrk : Module.finrank ℤ L = n := by
    rw [ZLattice.rank ℝ L, Module.finrank_fin_fun]
  let b : Basis (Fin n) ℤ L := (Module.finBasis ℤ L).reindex (finCongr hrk)
  let F : Set (Fin n → ℝ) := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L b)
  have hF : IsAddFundamentalDomain (↥L) F volume := ZLattice.isAddFundamentalDomain b volume
  have hF_fin : volume F ≠ ⊤ := by
    have hbd : Bornology.IsBounded F :=
      ZSpan.fundamentalDomain_isBounded (Module.Basis.ofZLatticeBasis ℝ L b)
    exact hbd.measure_lt_top.ne
  have hcov_eq : volume F = ENNReal.ofReal (ZLattice.covolume L volume) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF, Measure.real,
      ENNReal.ofReal_toReal hF_fin]
  have : Countable (↥L.toAddSubgroup) :=
    Function.Injective.countable (f := fun x : ↥L.toAddSubgroup => b.equivFun x)
      (fun x y h => b.equivFun.injective h)
  let s : Set (Fin n → ℝ) := Set.univ.pi fun i => Set.Ioo (-a i) (a i)
  have hsym : ∀ x ∈ s, -x ∈ s := by
    intro x hx i _
    have hi : -a i < x i ∧ x i < a i := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, Pi.neg_apply]
    exact ⟨by linarith, by linarith⟩
  have hconv : Convex ℝ s := convex_pi fun i _ => convex_Ioo (-a i) (a i)
  have hvol_s : volume s = ENNReal.ofReal (∏ i : Fin n, a i) * 2 ^ n := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    have hterm : ∀ i : Fin n, volume (Set.Ioo (-a i) (a i)) = ENNReal.ofReal (2 * a i) := by
      intro i
      rw [Real.volume_Ioo]
      congr 1
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_mul (by positivity), mul_comm, ENNReal.ofReal_pow (by norm_num)]
    simp
  have hlt : volume F * 2 ^ Module.finrank ℝ (Fin n → ℝ) < volume s := by
    rw [Module.finrank_fin_fun, hcov_eq, hvol_s]
    have h2ne0 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have h2netop : (2 : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    have hprod_pos : 0 < ∏ i : Fin n, a i := Finset.prod_pos fun i _ => ha i
    simpa [mul_comm] using
      ENNReal.mul_lt_mul_right h2ne0 h2netop ((ENNReal.ofReal_lt_ofReal_iff hprod_pos).mpr hcov)
  have hF' : IsAddFundamentalDomain (↥L.toAddSubgroup) F volume := hF
  obtain ⟨⟨v, hvL⟩, hv0, hvs⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF' hsym hconv hlt
  refine ⟨v, hvL, fun h => hv0 (Subtype.ext h), fun i => ?_⟩
  have hi := hvs i (Set.mem_univ i)
  exact abs_lt.mpr hi

/-- Finiteness of a discrete lattice intersected with any closed ball `Metric.closedBall 0 R`,
proved directly from antilipschitzness of the `ℤ`-basis coordinate map. -/
theorem lattice_inter_closedBall_finite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (R : ℝ) :
    ((L : Set E) ∩ Metric.closedBall (0 : E) R).Finite := by
  let b := Module.finBasis ℤ L
  let r := Module.finrank ℤ L
  have hli : LinearIndependent ℝ (fun i : Fin r => (b i : E)) :=
    RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b
  let S : (Fin r → ℝ) →ₗ[ℝ] E :=
    { toFun := fun c => ∑ i, c i • (b i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hc i
  obtain ⟨K, _, hK⟩ := S.exists_antilipschitzWith hSinj
  let M : ℤ := ⌈(K : ℝ) * max R 0⌉
  let box : Finset (Fin r → ℤ) := Fintype.piFinset fun _ : Fin r => Finset.Icc (-M) M
  refine (box.finite_toSet.image (fun n : Fin r → ℤ => ∑ i, n i • (b i : E))).subset ?_
  rintro v ⟨hvL, hvR⟩
  let n : Fin r → ℤ := fun i => b.repr ⟨v, hvL⟩ i
  have hv_eq : ∑ i, n i • (b i : E) = v := by
    have h1 := congrArg Subtype.val (b.sum_repr ⟨v, hvL⟩)
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  refine ⟨n, ?_, hv_eq⟩
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hSn : S (fun j => (n j : ℝ)) = v := by
    change ∑ j, (n j : ℝ) • (b j : E) = v
    simpa only [Int.cast_smul_eq_zsmul] using hv_eq
  have hnorm_le : ‖(fun j => (n j : ℝ))‖ ≤ (K : ℝ) * ‖v‖ := by
    have h1 := hK.le_mul_dist (fun j => (n j : ℝ)) 0
    simpa [dist_eq_norm, hSn] using h1
  have hcoord : |(n i : ℝ)| ≤ (K : ℝ) * max R 0 := by
    have h1 : |(n i : ℝ)| ≤ ‖(fun j => (n j : ℝ))‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun j => (n j : ℝ)) i
    have hvR' : ‖v‖ ≤ max R 0 := (mem_closedBall_zero_iff.mp hvR).trans (le_max_left R 0)
    exact h1.trans (hnorm_le.trans (mul_le_mul_of_nonneg_left hvR' K.2))
  have hM : (K : ℝ) * max R 0 ≤ (M : ℝ) := Int.le_ceil _
  have habs : |(n i : ℝ)| ≤ (M : ℝ) := hcoord.trans hM
  have hbounds := abs_le.mp habs
  exact ⟨by exact_mod_cast hbounds.1, by exact_mod_cast hbounds.2⟩

/-- Finiteness of a discrete lattice in `Fin n → ℝ` intersected with any bounded box
`{v | ∀ i, |v i| ≤ B i}`. -/
lemma lattice_pi_inter_box_finite {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (B : Fin n → ℝ) :
    {v : Fin n → ℝ | v ∈ L ∧ ∀ i : Fin n, |v i| ≤ B i}.Finite := by
  let b := Module.finBasis ℤ L
  let r := Module.finrank ℤ L
  have hli : LinearIndependent ℝ (fun i : Fin r => (b i : Fin n → ℝ)) := by
    let e := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
    let L' : Submodule ℤ (EuclideanSpace ℝ (Fin n)) := L.map (e.symm.toLinearMap.restrictScalars ℤ)
    have hcont : Continuous (fun x : L' => e (x : EuclideanSpace ℝ (Fin n))) :=
      e.toContinuousLinearEquiv.continuous.comp continuous_subtype_val
    let fBack : L' → L := fun x => ⟨e (x : EuclideanSpace ℝ (Fin n)), by
      rcases x.2 with ⟨y, hy, hyx⟩
      have : e (x : EuclideanSpace ℝ (Fin n)) = y := by rw [← hyx]; exact e.apply_symm_apply y
      rwa [this]⟩
    have : DiscreteTopology L' :=
      DiscreteTopology.of_continuous_injective (f := fBack) (Continuous.subtype_mk hcont _)
        (fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)))
    let eL : L ≃ₗ[ℤ] L' :=
      { toFun := fun x => ⟨e.symm x.1, ⟨x.1, x.2, rfl⟩⟩
        invFun := fBack
        map_add' := fun x y => Subtype.ext (e.symm.map_add x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_zsmul e.symm c x.1)
        left_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
        right_inv := fun y => Subtype.ext (e.symm_apply_apply y.1) }
    have hli' := RHDirect.ArakelovCovolume.linearIndependent_coe_basis L' (b.map eL)
    have hcomp : (fun i => (b i : Fin n → ℝ)) =
        e ∘ (fun i => ((b.map eL i : L') : EuclideanSpace ℝ (Fin n))) := by
      funext i
      change (b i : Fin n → ℝ) = e (e.symm (b i : Fin n → ℝ))
      exact (e.apply_symm_apply _).symm
    rw [hcomp]
    exact hli'.map' e.toLinearMap e.ker
  let S : (Fin r → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun c => ∑ i, c i • (b i : Fin n → ℝ)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hc i
  obtain ⟨K, _, hK⟩ := S.exists_antilipschitzWith hSinj
  let R : ℝ := ∑ i : Fin n, max (B i) 0
  let M : ℤ := ⌈(K : ℝ) * R⌉
  let box : Finset (Fin r → ℤ) := Fintype.piFinset fun _ : Fin r => Finset.Icc (-M) M
  refine (box.finite_toSet.image (fun m : Fin r → ℤ => ∑ i, m i • (b i : Fin n → ℝ))).subset ?_
  rintro v ⟨hvL, hvB⟩
  let m : Fin r → ℤ := fun i => b.repr ⟨v, hvL⟩ i
  have hv_eq : ∑ i, m i • (b i : Fin n → ℝ) = v := by
    have h1 := congrArg Subtype.val (b.sum_repr ⟨v, hvL⟩)
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  refine ⟨m, ?_, hv_eq⟩
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hSn : S (fun j => (m j : ℝ)) = v := by
    change ∑ j, (m j : ℝ) • (b j : Fin n → ℝ) = v
    simpa only [Int.cast_smul_eq_zsmul] using hv_eq
  have hvR : ‖v‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => le_max_right _ _)]
    intro j
    have hj1 : ‖v j‖ ≤ max (B j) 0 := by
      rw [Real.norm_eq_abs]; exact (hvB j).trans (le_max_left _ _)
    exact hj1.trans (Finset.single_le_sum (fun k _ => le_max_right (B k) 0) (Finset.mem_univ j))
  have hnorm_le : ‖(fun j => (m j : ℝ))‖ ≤ (K : ℝ) * R := by
    have h1 := hK.le_mul_dist (fun j => (m j : ℝ)) 0
    have h2 : ‖(fun j => (m j : ℝ))‖ ≤ (K : ℝ) * ‖v‖ := by simpa [dist_eq_norm, hSn] using h1
    exact h2.trans (mul_le_mul_of_nonneg_left hvR K.2)
  have hcoord : |(m i : ℝ)| ≤ (M : ℝ) := by
    have h1 : |(m i : ℝ)| ≤ ‖(fun j => (m j : ℝ))‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun j => (m j : ℝ)) i
    exact h1.trans (hnorm_le.trans (Int.le_ceil _))
  have hbounds := abs_le.mp hcoord
  exact ⟨by exact_mod_cast hbounds.1, by exact_mod_cast hbounds.2⟩

/-- **Closed (Non-Strict) Minkowski Linear-Forms Theorem on `Fin n → ℝ`**:
for any full-rank `ℤ`-lattice `L ⊂ Fin n → ℝ` (`0 < n`) and positive `a : Fin n → ℝ` with
`ZLattice.covolume L volume ≤ ∏ i, a i`, there exists `v ∈ L \ {0}` with `∀ i, |v i| ≤ a i`. -/
theorem minkowski_linear_forms_pi {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hcov : ZLattice.covolume L volume ≤ ∏ i : Fin n, a i) :
    ∃ v : Fin n → ℝ, v ∈ L ∧ v ≠ 0 ∧ ∀ i : Fin n, |v i| ≤ a i := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let S : Set (Fin n → ℝ) := {v | v ∈ L ∧ v ≠ 0 ∧ ∀ i : Fin n, |v i| ≤ 2 * a i}
  have hSfin : S.Finite :=
    (lattice_pi_inter_box_finite L (fun i => 2 * a i)).subset fun v hv => ⟨hv.1, hv.2.2⟩
  by_contra hnone
  push Not at hnone
  have hex_gt : ∀ v ∈ S, ∃ i : Fin n, 1 < |v i| / a i := by
    intro v hv
    obtain ⟨i, hi⟩ := hnone v hv.1 hv.2.1
    exact ⟨i, (one_lt_div (ha i)).mpr hi⟩
  let ratio : (Fin n → ℝ) → ℝ := fun v =>
    (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty (fun i => |v i| / a i)
  have hratio_gt : ∀ v ∈ S, 1 < ratio v := by
    intro v hv
    obtain ⟨i, hi⟩ := hex_gt v hv
    exact lt_of_lt_of_le hi (Finset.le_sup' (f := fun j => |v j| / a j) (Finset.mem_univ i))
  let t : ℝ :=
    if hne : hSfin.toFinset.Nonempty then
      min (3 / 2) ((1 + hSfin.toFinset.inf' hne ratio) / 2)
    else 3 / 2
  have ht1 : 1 < t := by
    dsimp only [t]
    split_ifs with hne
    · have hinf : 1 < hSfin.toFinset.inf' hne ratio :=
        (Finset.lt_inf'_iff hne).mpr fun v hv => hratio_gt v (hSfin.mem_toFinset.mp hv)
      exact lt_min (by norm_num) (by linarith)
    · norm_num
  have ht2 : t < 2 := by
    dsimp only [t]
    split_ifs with hne
    · linarith [min_le_left (3 / 2 : ℝ) ((1 + hSfin.toFinset.inf' hne ratio) / 2)]
    · norm_num
  have hcov_lt : ZLattice.covolume L volume < ∏ i : Fin n, (t * a i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have htn : 1 < t ^ n := one_lt_pow₀ ht1 hn.ne'
    have hprod_pos : 0 < ∏ i : Fin n, a i := Finset.prod_pos fun i _ => ha i
    nlinarith
  obtain ⟨v, hvL, hv0, hvt⟩ :=
    minkowski_linear_forms_pi_strict L (fun i => t * a i) (fun i => mul_pos (by linarith) (ha i))
      hcov_lt
  have hvS : v ∈ S := ⟨hvL, hv0, fun i => (hvt i).le.trans (by nlinarith [ha i])⟩
  have hvfin : v ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr hvS
  have hne : hSfin.toFinset.Nonempty := ⟨v, hvfin⟩
  have hratio_lt : ratio v < t := by
    rw [Finset.sup'_lt_iff]
    intro i _
    exact (div_lt_iff₀ (ha i)).mpr (hvt i)
  have ht_le : t < hSfin.toFinset.inf' hne ratio := by
    have hinf : 1 < hSfin.toFinset.inf' hne ratio :=
      (Finset.lt_inf'_iff hne).mpr fun w hw => hratio_gt w (hSfin.mem_toFinset.mp hw)
    have ht_eq : t = min (3 / 2) ((1 + hSfin.toFinset.inf' hne ratio) / 2) := dif_pos hne
    rw [ht_eq]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hinf_le : hSfin.toFinset.inf' hne ratio ≤ ratio v := Finset.inf'_le ratio hvfin
  linarith

/-- **Minkowski's `L^∞` First-Minimum Theorem on `Fin n → ℝ`**:
`∃ v ∈ L \ {0}, ‖v‖ ≤ (ZLattice.covolume L volume) ^ (1 / n)`. -/
theorem minkowski_linf_pi {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : Fin n → ℝ, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ (ZLattice.covolume L volume) ^ (1 / (n : ℝ)) := by
  have hcov_pos : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos L volume
  set R : ℝ := (ZLattice.covolume L volume) ^ (1 / (n : ℝ))
  have hR_pos : 0 < R := Real.rpow_pos_of_pos hcov_pos _
  have hprod : ∏ _i : Fin n, R = ZLattice.covolume L volume := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul hcov_pos.le, one_div_mul_cancel (by exact_mod_cast hn.ne'), Real.rpow_one]
  obtain ⟨v, hvL, hv0, hvR⟩ :=
    minkowski_linear_forms_pi hn L (fun _ => R) (fun _ => hR_pos) (le_of_eq hprod.symm)
  refine ⟨v, hvL, hv0, ?_⟩
  rw [pi_norm_le_iff_of_nonneg hR_pos.le]
  intro i
  simpa [Real.norm_eq_abs] using hvR i

end MinkowskiPi

section MinkowskiInnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coordinate transport of a discrete lattice `L ⊂ E` along an orthonormal basis `e` of
`V = span_ℝ(L)` to a full-rank `IsZLattice ℝ` inside `Fin (rk L) → ℝ`, preserving covolume
(`ZLattice.covolume L' volume = ArakelovCovolume.covol L`). -/
private lemma covol_eq_zlattice_covolume_coord (L : Submodule ℤ E) [DiscreteTopology L]
    (e : OrthonormalBasis (Fin (RHDirect.ArakelovCovolume.rk L)) ℝ (Submodule.span ℝ (L : Set E))) :
    let V := Submodule.span ℝ (L : Set E)
    let Φ : V →ₗ[ℝ] (Fin (RHDirect.ArakelovCovolume.rk L) → ℝ) :=
      { toFun := fun x i => inner ℝ (e i) x
        map_add' := fun x y => by funext i; exact inner_add_right _ _ _
        map_smul' := fun c x => by funext i; exact real_inner_smul_right _ _ _ }
    let L' : Submodule ℤ (Fin (RHDirect.ArakelovCovolume.rk L) → ℝ) :=
      (L.comap (V.subtype.restrictScalars ℤ)).map (Φ.restrictScalars ℤ)
    ∃ (_ : DiscreteTopology L') (_ : IsZLattice ℝ L'),
      ZLattice.covolume L' volume = RHDirect.ArakelovCovolume.covol L ∧
      (∀ w ∈ L', ∃ v ∈ L, (∀ i, w i = inner ℝ (e i : E) v) ∧ (w ≠ 0 → v ≠ 0)) := by
  let r := RHDirect.ArakelovCovolume.rk L
  let V := Submodule.span ℝ (L : Set E)
  let Φ : V →ₗ[ℝ] (Fin r → ℝ) :=
    { toFun := fun x i => inner ℝ (e i) x
      map_add' := fun x y => by funext i; exact inner_add_right _ _ _
      map_smul' := fun c x => by funext i; exact real_inner_smul_right _ _ _ }
  let Ψ : (Fin r → ℝ) →ₗ[ℝ] V :=
    { toFun := fun c => ∑ i, c i • e i
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hΦΨ : ∀ c : Fin r → ℝ, Φ (Ψ c) = c := by
    intro c
    funext i
    simp only [Φ, Ψ, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, real_inner_smul_right,
      orthonormal_iff_ite.mp e.orthonormal]
    simp
  have hΨΦ : ∀ x : V, Ψ (Φ x) = x := by
    intro x
    simpa [Φ, Ψ] using e.sum_repr' x
  let L₀ : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let L' : Submodule ℤ (Fin r → ℝ) := L₀.map (Φ.restrictScalars ℤ)
  have hΨcont : Continuous Ψ := by
    change Continuous fun c : Fin r → ℝ => ∑ i, c i • e i
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  let fBack : L' → L := fun w => ⟨(Ψ w.1 : E), by
    rcases w.2 with ⟨x, hx, hxw⟩
    have hxEq : Ψ w.1 = x := by rw [← hxw]; exact hΨΦ x
    rw [hxEq]; exact hx⟩
  have hfBack_cont : Continuous fBack :=
    Continuous.subtype_mk (continuous_subtype_val.comp (hΨcont.comp continuous_subtype_val)) _
  have hfBack_inj : Function.Injective fBack := by
    intro w₁ w₂ h
    apply Subtype.ext
    have hV : Ψ w₁.1 = Ψ w₂.1 :=
      Subtype.ext (show (Ψ w₁.1 : E) = (Ψ w₂.1 : E) from congrArg (fun x : L => (x : E)) h)
    have h1 := congrArg Φ hV
    simpa [hΦΨ] using h1
  have hDisc' : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective hfBack_cont hfBack_inj
  have hSpanL' : Submodule.span ℝ (L' : Set (Fin r → ℝ)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro c
    have hmem : Ψ c ∈ Submodule.span ℝ (L₀ : Set V) := by
      have h1 : (Submodule.span ℝ (L₀ : Set V)) = ⊤ := Submodule.span_span_coe_preimage
      rw [h1]; trivial
    have hmap : Submodule.map Φ (Submodule.span ℝ (L₀ : Set V)) =
        Submodule.span ℝ (L' : Set (Fin r → ℝ)) := by
      rw [Submodule.map_span]
      rfl
    have : Φ (Ψ c) ∈ Submodule.span ℝ (L' : Set (Fin r → ℝ)) := by
      rw [← hmap]; exact ⟨Ψ c, hmem, rfl⟩
    rwa [hΦΨ] at this
  have hZL' : IsZLattice ℝ L' := ⟨hSpanL'⟩
  let eL : L ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨Φ ⟨x.1, Submodule.subset_span x.2⟩, ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
      invFun := fBack
      map_add' := fun x y => Subtype.ext (by funext i; exact inner_add_right _ _ _)
      map_smul' := fun n x => Subtype.ext (by
        funext i
        change inner ℝ (e i) (n • (⟨x.1, Submodule.subset_span x.2⟩ : V)) =
          n • inner ℝ (e i) (⟨x.1, Submodule.subset_span x.2⟩ : V)
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
          smul_eq_mul])
      left_inv := fun x => Subtype.ext (by
        change (Ψ (Φ ⟨x.1, Submodule.subset_span x.2⟩) : E) = x.1
        rw [hΨΦ])
      right_inv := fun w => Subtype.ext (by
        change Φ (Ψ w.1) = w.1
        exact hΦΨ w.1) }
  let b : Basis (Fin r) ℤ L := Module.finBasis ℤ L
  let b' : Basis (Fin r) ℤ L' := b.map eL
  have hcov_det : ZLattice.covolume L' volume = |(Matrix.of (Subtype.val ∘ b')).det| :=
    ZLattice.covolume_eq_det L' b'
  let A : Matrix (Fin r) (Fin r) ℝ := Matrix.of (Subtype.val ∘ b')
  have hgram : Matrix.gram ℝ (fun j => (b j : E)) = A * A.transpose := by
    ext j k
    rw [Matrix.gram_apply, Matrix.mul_apply]
    have hparseval : inner ℝ (⟨(b j : E), Submodule.subset_span (b j).2⟩ : V)
        (⟨(b k : E), Submodule.subset_span (b k).2⟩ : V) =
        ∑ i : Fin r, inner ℝ (e i) (⟨(b j : E), Submodule.subset_span (b j).2⟩ : V) *
          inner ℝ (e i) (⟨(b k : E), Submodule.subset_span (b k).2⟩ : V) := by
      have hj := (hΨΦ ⟨(b j : E), Submodule.subset_span (b j).2⟩).symm
      have hk := (hΨΦ ⟨(b k : E), Submodule.subset_span (b k).2⟩).symm
      conv_lhs => rw [hj, hk]
      simp only [Ψ, Φ, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_comm]
    change inner ℝ (⟨(b j : E), Submodule.subset_span (b j).2⟩ : V)
        (⟨(b k : E), Submodule.subset_span (b k).2⟩ : V) =
      ∑ i : Fin r, A j i * A.transpose i k
    rw [hparseval]
    refine Finset.sum_congr rfl fun i _ => rfl
  have hcov_eq : ZLattice.covolume L' volume = RHDirect.ArakelovCovolume.covol L := by
    rw [RHDirect.ArakelovCovolume.covol_eq_sqrt_det_gram L b, hgram, Matrix.det_mul,
      Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs, hcov_det]
  refine ⟨hDisc', hZL', hcov_eq, ?_⟩
  intro w hw
  rcases hw with ⟨x, hx, rfl⟩
  refine ⟨(x : E), hx, fun i => rfl, ?_⟩
  intro hw0 hx0
  apply hw0
  funext i
  change inner ℝ (e i : E) (x : E) = 0
  rw [hx0, inner_zero_right]

/-- **Minkowski's Linear Forms Theorem (Strict)** on any discrete `ℤ`-lattice `L ⊂ E` (`L ≠ ⊥`). -/
theorem minkowski_linear_forms_strict (L : Submodule ℤ E) [DiscreteTopology L]
    (e : OrthonormalBasis (Fin (RHDirect.ArakelovCovolume.rk L)) ℝ (Submodule.span ℝ (L : Set E)))
    (a : Fin (RHDirect.ArakelovCovolume.rk L) → ℝ) (ha : ∀ i, 0 < a i)
    (hcov : RHDirect.ArakelovCovolume.covol L < ∏ i, a i) :
    ∃ v ∈ L, v ≠ 0 ∧ ∀ i, |inner ℝ (e i : E) v| < a i := by
  obtain ⟨hDisc', hZL', hcov_eq, hback⟩ := covol_eq_zlattice_covolume_coord L e
  obtain ⟨w, hwL', hw0, hwa⟩ := minkowski_linear_forms_pi_strict _ a ha (hcov_eq.trans_lt hcov)
  obtain ⟨v, hvL, hcoord, hv0⟩ := hback w hwL'
  exact ⟨v, hvL, hv0 hw0, fun i => by rw [← hcoord i]; exact hwa i⟩

/-- **Minkowski's Linear Forms Theorem (Closed)** on any discrete `ℤ`-lattice `L ⊂ E` (`L ≠ ⊥`):
for any positive box half-widths `a` with `covol L ≤ ∏ i, a i`, there exists `v ∈ L \ {0}` with
`∀ i, |⟨e_i, v⟩| ≤ a i`. -/
theorem minkowski_linear_forms (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (e : OrthonormalBasis (Fin (RHDirect.ArakelovCovolume.rk L)) ℝ (Submodule.span ℝ (L : Set E)))
    (a : Fin (RHDirect.ArakelovCovolume.rk L) → ℝ) (ha : ∀ i, 0 < a i)
    (hcov : RHDirect.ArakelovCovolume.covol L ≤ ∏ i, a i) :
    ∃ v ∈ L, v ≠ 0 ∧ ∀ i, |inner ℝ (e i : E) v| ≤ a i := by
  have hrpos : 0 < RHDirect.ArakelovCovolume.rk L :=
    RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  obtain ⟨hDisc', hZL', hcov_eq, hback⟩ := covol_eq_zlattice_covolume_coord L e
  obtain ⟨w, hwL', hw0, hwa⟩ := minkowski_linear_forms_pi hrpos _ a ha (hcov_eq.trans_le hcov)
  obtain ⟨v, hvL, hcoord, hv0⟩ := hback w hwL'
  exact ⟨v, hvL, hv0 hw0, fun i => by rw [← hcoord i]; exact hwa i⟩

/-- **Minkowski's `L^∞` First-Minimum Theorem** for any discrete `ℤ`-lattice `L ⊂ E` (`L ≠ ⊥`):
relative to any orthonormal basis `e` of `span_ℝ(L)`, there exists `v ∈ L \ {0}` with
`∀ i, |⟨e_i, v⟩| ≤ covol(L)^(1 / rk L)`. -/
theorem minkowski_first_minimum_linf (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (e : OrthonormalBasis (Fin (RHDirect.ArakelovCovolume.rk L)) ℝ (Submodule.span ℝ (L : Set E))) :
    ∃ v ∈ L, v ≠ 0 ∧
      ∀ i, |inner ℝ (e i : E) v| ≤
        (RHDirect.ArakelovCovolume.covol L) ^ (1 / (RHDirect.ArakelovCovolume.rk L : ℝ)) := by
  have hrpos : 0 < RHDirect.ArakelovCovolume.rk L :=
    RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  set R : ℝ := (RHDirect.ArakelovCovolume.covol L) ^ (1 / (RHDirect.ArakelovCovolume.rk L : ℝ))
  have hprod : ∏ _i : Fin (RHDirect.ArakelovCovolume.rk L), R = RHDirect.ArakelovCovolume.covol L := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul hcov_pos.le, one_div_mul_cancel (by exact_mod_cast hrpos.ne'), Real.rpow_one]
  exact minkowski_linear_forms L hL0 e (fun _ => R)
    (fun _ => Real.rpow_pos_of_pos hcov_pos _) (le_of_eq hprod.symm)

/-- **Euclidean Hermite First-Minimum Theorem (Basis-Free)**:
every nonzero discrete `ℤ`-lattice `L ⊂ E` contains a nonzero vector `v ∈ L \ {0}` with
`‖v‖ ≤ √(rk L) · covol(L)^(1 / rk L)`. -/
theorem hermite_first_minimum (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ v ∈ L, v ≠ 0 ∧
      ‖v‖ ≤ Real.sqrt (RHDirect.ArakelovCovolume.rk L : ℝ) *
        (RHDirect.ArakelovCovolume.covol L) ^ (1 / (RHDirect.ArakelovCovolume.rk L : ℝ)) := by
  let r := RHDirect.ArakelovCovolume.rk L
  let V := Submodule.span ℝ (L : Set E)
  have hdim : Module.finrank ℝ V = r :=
    (RHDirect.ArakelovCovolume.finrank_int_eq_finrank_real_span L).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdim]))
  obtain ⟨v, hvL, hv0, hlinf⟩ := minkowski_first_minimum_linf L hL0 e
  refine ⟨v, hvL, hv0, ?_⟩
  set R : ℝ := (RHDirect.ArakelovCovolume.covol L) ^ (1 / (r : ℝ))
  have hR_nn : 0 ≤ R := Real.rpow_nonneg (RHDirect.ArakelovCovolume.covol_pos L).le _
  have hparseval : ‖v‖ ^ 2 = ∑ i : Fin r, (inner ℝ (e i : E) v) ^ 2 := by
    let vV : V := ⟨v, Submodule.subset_span hvL⟩
    have hv_sum : vV = ∑ i : Fin r, inner ℝ (e i) vV • e i := (e.sum_repr' vV).symm
    have hsq : ‖vV‖ ^ 2 = ∑ i : Fin r, (inner ℝ (e i) vV) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hv_sum]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum, Finset.sum_eq_single i]
      · rw [real_inner_smul_left, real_inner_smul_right,
          orthonormal_iff_ite.mp e.orthonormal i i]; simp [sq]
      · intro j _ hji
        rw [real_inner_smul_left, real_inner_smul_right,
          orthonormal_iff_ite.mp e.orthonormal i j, if_neg hji.symm, mul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    exact hsq
  have hsq_le : ‖v‖ ^ 2 ≤ (r : ℝ) * R ^ 2 := by
    rw [hparseval]
    calc ∑ i : Fin r, (inner ℝ (e i : E) v) ^ 2
        ≤ ∑ _i : Fin r, R ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hlinf i) 2
      _ = (r : ℝ) * R ^ 2 := by simp [nsmul_eq_mul]
  have htarget : (Real.sqrt (r : ℝ) * R) ^ 2 = (r : ℝ) * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
  have hnn : 0 ≤ Real.sqrt (r : ℝ) * R := mul_nonneg (Real.sqrt_nonneg _) hR_nn
  nlinarith [norm_nonneg v]

end MinkowskiInnerProduct

/-! ## Section 3: First Minimum `lambda1`, Finiteness & Quantitative Ball / Siegel-Box Counting -/

section LatticeCounting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Finiteness of a discrete lattice `L ⊂ E` inside any orthogonal Siegel box
`{v ∈ L | ∀ i, |⟨e_i, v⟩| ≤ B_i}`. -/
theorem lattice_inter_box_finite (L : Submodule ℤ E) [DiscreteTopology L]
    (e : OrthonormalBasis (Fin (RHDirect.ArakelovCovolume.rk L)) ℝ (Submodule.span ℝ (L : Set E)))
    (B : Fin (RHDirect.ArakelovCovolume.rk L) → ℝ) :
    {v : E | v ∈ L ∧ ∀ i, |inner ℝ (e i : E) v| ≤ B i}.Finite := by
  let r := RHDirect.ArakelovCovolume.rk L
  let V := Submodule.span ℝ (L : Set E)
  let R : ℝ := Real.sqrt (∑ i : Fin r, (max (B i) 0) ^ 2)
  refine (lattice_inter_closedBall_finite L R).subset ?_
  rintro v ⟨hvL, hvB⟩
  refine ⟨hvL, mem_closedBall_zero_iff.mpr ?_⟩
  have hparseval : ‖v‖ ^ 2 = ∑ i : Fin r, (inner ℝ (e i : E) v) ^ 2 := by
    let vV : V := ⟨v, Submodule.subset_span hvL⟩
    have hv_sum : vV = ∑ i : Fin r, inner ℝ (e i) vV • e i := (e.sum_repr' vV).symm
    change ‖vV‖ ^ 2 = ∑ i : Fin r, (inner ℝ (e i) vV) ^ 2
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [hv_sum]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right,
        orthonormal_iff_ite.mp e.orthonormal i i]; simp [sq]
    · intro j _ hji
      rw [real_inner_smul_left, real_inner_smul_right,
        orthonormal_iff_ite.mp e.orthonormal i j, if_neg hji.symm, mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hsq : ‖v‖ ^ 2 ≤ ∑ i : Fin r, (max (B i) 0) ^ 2 := by
    rw [hparseval]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hvB i).trans (le_max_left _ _)) 2
  have hRsq : R ^ 2 = ∑ i : Fin r, (max (B i) 0) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  nlinarith [norm_nonneg v]

/-- First successive minimum `λ_1(L) = inf { ‖v‖ | v ∈ L \ {0} }`. -/
def lambda1 (L : Submodule ℤ E) : ℝ :=
  sInf { t : ℝ | ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ = t }

/-- Every nonzero discrete lattice `L ⊂ E` admits a shortest nonzero vector attaining `lambda1 L`. -/
theorem exists_shortest_nonzero_vector (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ v₀ ∈ L, v₀ ≠ 0 ∧ ∀ v ∈ L, v ≠ 0 → ‖v₀‖ ≤ ‖v‖ := by
  obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  let S : Set E := {v ∈ (L : Set E) | v ≠ 0 ∧ ‖v‖ ≤ ‖w‖}
  have hSfin : S.Finite :=
    (lattice_inter_closedBall_finite L ‖w‖).subset fun v hv =>
      ⟨hv.1, mem_closedBall_zero_iff.mpr hv.2.2⟩
  have hwS : w ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr ⟨hwL, hw0, le_rfl⟩
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := hSfin.toFinset.exists_min_image (fun v : E => ‖v‖) ⟨w, hwS⟩
  have hv₀ := hSfin.mem_toFinset.mp hv₀mem
  refine ⟨v₀, hv₀.1, hv₀.2.1, fun v hvL hv0 => ?_⟩
  by_cases hvw : ‖v‖ ≤ ‖w‖
  · exact hv₀min v (hSfin.mem_toFinset.mpr ⟨hvL, hv0, hvw⟩)
  · exact hv₀.2.2.trans (le_of_not_ge hvw)

theorem exists_norm_eq_lambda1 (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ v₀ ∈ L, v₀ ≠ 0 ∧ ‖v₀‖ = lambda1 L := by
  obtain ⟨v₀, hv₀L, hv₀0, hv₀min⟩ := exists_shortest_nonzero_vector L hL0
  refine ⟨v₀, hv₀L, hv₀0, le_antisymm ?_ ?_⟩
  · exact le_csInf ⟨‖v₀‖, v₀, hv₀L, hv₀0, rfl⟩ (by rintro _ ⟨v, hvL, hv0, rfl⟩; exact hv₀min v hvL hv0)
  · exact csInf_le ⟨0, by rintro _ ⟨v, _, _, rfl⟩; exact norm_nonneg v⟩ ⟨v₀, hv₀L, hv₀0, rfl⟩

theorem lambda1_pos (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    0 < lambda1 L := by
  obtain ⟨v₀, _, hv₀0, heq⟩ := exists_norm_eq_lambda1 L hL0
  rw [← heq]
  exact norm_pos_iff.mpr hv₀0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lambda1_le_norm (L : Submodule ℤ E) {v : E} (hvL : v ∈ L) (hv0 : v ≠ 0) :
    lambda1 L ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, _, _, rfl⟩; exact norm_nonneg w⟩ ⟨v, hvL, hv0, rfl⟩

/-- **Hermite First-Minimum Inequality**: `λ_1(L) ≤ √(rk L) · covol(L)^(1 / rk L)`. -/
theorem lambda1_le_hermite (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    lambda1 L ≤ Real.sqrt (RHDirect.ArakelovCovolume.rk L : ℝ) *
      (RHDirect.ArakelovCovolume.covol L) ^ (1 / (RHDirect.ArakelovCovolume.rk L : ℝ)) := by
  obtain ⟨v, hvL, hv0, hvbound⟩ := hermite_first_minimum L hL0
  exact (lambda1_le_norm L hvL hv0).trans hvbound

/-- Exact integer box count: `#{m : Fin n → ℤ | ∀ i, |m i| ≤ B i} = ∏ i, (2 * ⌊B i⌋₊ + 1)`
for `∀ i, 0 ≤ B i`. -/
theorem card_int_box_eq {n : ℕ} (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) :
    ({m : Fin n → ℤ | ∀ i, |(m i : ℝ)| ≤ B i}).ncard = ∏ i : Fin n, (2 * ⌊B i⌋₊ + 1) := by
  let S : Finset (Fin n → ℤ) :=
    Fintype.piFinset fun i : Fin n => Finset.Icc (-(⌊B i⌋₊ : ℤ)) (⌊B i⌋₊ : ℤ)
  have hEq : {m : Fin n → ℤ | ∀ i, |(m i : ℝ)| ≤ B i} = (S : Set (Fin n → ℤ)) := by
    ext m
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, S, Fintype.mem_piFinset, Finset.mem_Icc]
    refine forall_congr' fun i => ?_
    rw [abs_le]
    have h1 : (m i : ℝ) ≤ B i ↔ m i ≤ (⌊B i⌋₊ : ℤ) := by
      constructor
      · intro h
        by_cases hm : 0 ≤ m i
        · lift m i to ℕ using hm with k
          exact_mod_cast (Nat.le_floor (by exact_mod_cast h))
        · exact le_trans (by omega) (Nat.cast_nonneg _)
      · intro h
        exact (show (m i : ℝ) ≤ (⌊B i⌋₊ : ℝ) by exact_mod_cast h).trans (Nat.floor_le (hB i))
    have h2 : -B i ≤ (m i : ℝ) ↔ -(⌊B i⌋₊ : ℤ) ≤ m i := by
      constructor
      · intro h
        have h' : -(m i : ℝ) ≤ B i := by linarith
        have h'' : -m i ≤ (⌊B i⌋₊ : ℤ) := by
          by_cases hm : 0 ≤ -m i
          · lift (-m i) to ℕ using hm with k hk
            have hkB : (k : ℝ) ≤ B i := by
              rw [← Int.cast_natCast, hk, Int.cast_neg]
              exact h'
            exact_mod_cast Nat.le_floor hkB
          · exact le_trans (by omega) (Nat.cast_nonneg _)
        omega
      · intro h
        have h' : (-(⌊B i⌋₊ : ℤ) : ℝ) ≤ (m i : ℝ) := by exact_mod_cast h
        have hfl : (⌊B i⌋₊ : ℝ) ≤ B i := Nat.floor_le (hB i)
        push_cast at h'
        linarith
    exact ⟨fun ⟨hl, hr⟩ => ⟨h2.mp hl, h1.mp hr⟩, fun ⟨hl, hr⟩ => ⟨h2.mpr hl, h1.mpr hr⟩⟩
  rw [hEq, Set.ncard_coe_finset, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Icc]
  omega

/-- **Universal Euclidean Ball Lattice-Point Counting Bound** (Haar ball-packing):
for any nonzero discrete lattice `L ⊂ E` and `0 ≤ R`,
`#(L ∩ B̄(0, R)) ≤ (1 + 2 R / λ_1(L)) ^ (rk L)`. -/
theorem ncard_lattice_closedBall_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {R : ℝ} (hR : 0 ≤ R) :
    (((L : Set E) ∩ Metric.closedBall (0 : E) R).ncard : ℝ) ≤
      (1 + 2 * R / lambda1 L) ^ (RHDirect.ArakelovCovolume.rk L) := by
  classical
  let r := RHDirect.ArakelovCovolume.rk L
  let V := Submodule.span ℝ (L : Set E)
  have hdim : Module.finrank ℝ V = r :=
    (RHDirect.ArakelovCovolume.finrank_int_eq_finrank_real_span L).symm
  have hrpos : 0 < r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (hdim.symm ▸ hrpos)
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hfin := lattice_inter_closedBall_finite L R
  let S : Finset V :=
    hfin.toFinset.attach.image fun x =>
      ⟨x.1, Submodule.subset_span (hfin.mem_toFinset.mp x.2).1⟩
  have hcard : S.card = ((L : Set E) ∩ Metric.closedBall (0 : E) R).ncard := by
    rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro a b hab; exact Subtype.ext (Subtype.mk.inj hab)
  rw [← hcard]
  set δ : ℝ := lambda1 L / 2
  have hlam_pos : 0 < lambda1 L := lambda1_pos L hL0
  have hδpos : 0 < δ := half_pos hlam_pos
  have hdisj : Set.PairwiseDisjoint (S : Set V) fun x => Metric.ball x δ := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    have hxL : (x : E) ∈ L := by
      rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
      exact (hfin.mem_toFinset.mp a.2).1
    have hyL : (y : E) ∈ L := by
      rcases Finset.mem_image.mp hy with ⟨b, _, rfl⟩
      exact (hfin.mem_toFinset.mp b.2).1
    have hne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr (fun h => hxy (Subtype.ext h))
    have hge : lambda1 L ≤ ‖(x : E) - (y : E)‖ :=
      lambda1_le_norm L (L.sub_mem hxL hyL) hne
    have hlt : ‖x - y‖ < lambda1 L := by
      have h1 : dist x z < δ := by rwa [dist_comm]
      have h2 : dist z y < δ := hzy
      have h3 : dist x y < δ + δ := lt_of_le_of_lt (dist_triangle x z y) (add_lt_add h1 h2)
      simpa [dist_eq_norm, δ, add_halves] using h3
    exact not_lt.mpr hge hlt
  have hsub : (⋃ x ∈ S, Metric.ball x δ) ⊆ Metric.ball (0 : V) (R + δ) := by
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨x, hx, hzx⟩
    have hxR : ‖x‖ ≤ R := by
      rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
      exact mem_closedBall_zero_iff.mp (hfin.mem_toFinset.mp a.2).2
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at hzx
    calc ‖z‖ = ‖(z - x) + x‖ := by abel_nf
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < δ + R := add_lt_add_of_lt_of_le hzx hxR
      _ = R + δ := add_comm _ _
  have hmeas : ∑ x ∈ S, μ (Metric.ball x δ) ≤ μ (Metric.ball (0 : V) (R + δ)) := by
    rw [← measure_biUnion_finset hdisj (fun _ _ => Metric.isOpen_ball.measurableSet)]
    exact measure_mono hsub
  have hball_eq : ∀ x : V, μ (Metric.ball x δ) = ENNReal.ofReal (δ ^ r) * μ (Metric.ball (0 : V) 1) := by
    intro x
    rw [Measure.addHaar_ball μ x hδpos.le, hdim]
  have hbig_eq : μ (Metric.ball (0 : V) (R + δ)) =
      ENNReal.ofReal ((R + δ) ^ r) * μ (Metric.ball (0 : V) 1) := by
    rw [Measure.addHaar_ball μ 0 (by linarith), hdim]
  simp_rw [hball_eq] at hmeas
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hbig_eq] at hmeas
  have hB1_pos : 0 < μ (Metric.ball (0 : V) 1) :=
    Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr zero_lt_one)
  have hB1_top : μ (Metric.ball (0 : V) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hcancel : (S.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ r) ≤ ENNReal.ofReal ((R + δ) ^ r) :=
    (ENNReal.mul_le_mul_iff_left hB1_pos.ne' hB1_top).mp hmeas
  have hreal : (S.card : ℝ) * δ ^ r ≤ (R + δ) ^ r := by
    have h1 : ENNReal.ofReal ((S.card : ℝ) * δ ^ r) ≤ ENNReal.ofReal ((R + δ) ^ r) := by
      rwa [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) r)).mp h1
  have hdiv : (S.card : ℝ) ≤ ((R + δ) / δ) ^ r := by
    rw [div_pow, le_div_iff₀ (pow_pos hδpos r)]
    exact hreal
  have hsimp : (R + δ) / δ = 1 + 2 * R / lambda1 L := by
    dsimp only [δ]
    field_simp [hlam_pos.ne']
    ring
  rwa [hsimp] at hdiv

/-- **Quantitative Siegel-Box Lattice-Point Counting Bound** (cube-packing):
if `L ⊂ E` has `L^∞`-minimum `δ > 0` relative to an orthonormal basis `e` of `span_ℝ(L)`
(in particular, `δ = lambda1 L / √(rk L)` always works!), then for `∀ i, 0 ≤ B i`,
`#{v ∈ L | ∀ i, |⟨e_i, v⟩| ≤ B i} ≤ ∏ i, (1 + 2 * B i / δ)`. -/
theorem ncard_lattice_box_le (L : Submodule ℤ E) [DiscreteTopology L]
    (e : OrthonormalBasis (Fin (RHDirect.ArakelovCovolume.rk L)) ℝ (Submodule.span ℝ (L : Set E)))
    (B : Fin (RHDirect.ArakelovCovolume.rk L) → ℝ) (hB : ∀ i, 0 ≤ B i)
    {δ : ℝ} (hδ : 0 < δ)
    (hmin : ∀ v ∈ L, v ≠ 0 → ∃ i, δ ≤ |inner ℝ (e i : E) v|) :
    (({v : E | v ∈ L ∧ ∀ i, |inner ℝ (e i : E) v| ≤ B i}).ncard : ℝ) ≤
      ∏ i, (1 + 2 * B i / δ) := by
  classical
  let r := RHDirect.ArakelovCovolume.rk L
  have hfin := lattice_inter_box_finite L e B
  let coord : E → (Fin r → ℝ) := fun v i => inner ℝ (e i : E) v
  let S : Finset (Fin r → ℝ) := hfin.toFinset.image coord
  have hcoord_inj : Set.InjOn coord (hfin.toFinset : Set E) := by
    intro u hu v hv huv
    have huL : u ∈ L := (hfin.mem_toFinset.mp hu).1
    have hvL : v ∈ L := (hfin.mem_toFinset.mp hv).1
    by_contra hne
    obtain ⟨i, hi⟩ := hmin (u - v) (L.sub_mem huL hvL) (sub_ne_zero.mpr hne)
    have h0 : inner ℝ (e i : E) (u - v) = 0 := by
      rw [inner_sub_right]
      exact sub_eq_zero.mpr (congrFun huv i)
    rw [h0, abs_zero] at hi
    linarith
  have hcard : S.card = ({v : E | v ∈ L ∧ ∀ i, |inner ℝ (e i : E) v| ≤ B i}).ncard := by
    rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
    exact Finset.card_image_of_injOn hcoord_inj
  rw [← hcard]
  let cube : (Fin r → ℝ) → Set (Fin r → ℝ) := fun x =>
    Set.univ.pi fun i => Set.Ioo (x i - δ / 2) (x i + δ / 2)
  have hdisj : Set.PairwiseDisjoint (S : Set (Fin r → ℝ)) cube := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    have huv : u ≠ v := fun h => hxy (congrArg coord h)
    obtain ⟨i, hi⟩ := hmin (u - v) (L.sub_mem (hfin.mem_toFinset.mp hu).1 (hfin.mem_toFinset.mp hv).1)
      (sub_ne_zero.mpr huv)
    rw [inner_sub_right] at hi
    have h1 : coord u i - δ / 2 < z i ∧ z i < coord u i + δ / 2 := hzx i (Set.mem_univ i)
    have h2 : coord v i - δ / 2 < z i ∧ z i < coord v i + δ / 2 := hzy i (Set.mem_univ i)
    have hlt : |coord u i - coord v i| < δ := by
      rw [abs_lt]
      exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    exact not_lt.mpr hi hlt
  let bigBox : Set (Fin r → ℝ) :=
    Set.univ.pi fun i => Set.Ioo (-(B i + δ / 2)) (B i + δ / 2)
  have hsub : (⋃ x ∈ S, cube x) ⊆ bigBox := by
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨x, hx, hzx⟩
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    intro i _
    have huB := abs_le.mp ((hfin.mem_toFinset.mp hu).2 i)
    have hz1 : coord u i - δ / 2 < z i ∧ z i < coord u i + δ / 2 := hzx i (Set.mem_univ i)
    exact ⟨by linarith [huB.1, hz1.1], by linarith [huB.2, hz1.2]⟩
  have hcube_meas : ∀ x : Fin r → ℝ, MeasurableSet (cube x) :=
    fun x => MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hmeas : ∑ x ∈ S, volume (cube x) ≤ volume bigBox := by
    rw [← measure_biUnion_finset hdisj (fun x _ => hcube_meas x)]
    exact measure_mono hsub
  have hvol_cube : ∀ x : Fin r → ℝ, volume (cube x) = ENNReal.ofReal (δ ^ r) := by
    intro x
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    have hterm : ∀ i : Fin r, volume (Set.Ioo (x i - δ / 2) (x i + δ / 2)) = ENNReal.ofReal δ := by
      intro i
      rw [Real.volume_Ioo]
      congr 1; ring
    simp_rw [hterm]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hδ.le]
  have hvol_big : volume bigBox = ENNReal.ofReal (∏ i : Fin r, (2 * B i + δ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    have hterm : ∀ i : Fin r,
        volume (Set.Ioo (-(B i + δ / 2)) (B i + δ / 2)) = ENNReal.ofReal (2 * B i + δ) := by
      intro i
      rw [Real.volume_Ioo]
      congr 1; ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [hB i])]
  simp_rw [hvol_cube] at hmeas
  rw [Finset.sum_const, nsmul_eq_mul, hvol_big] at hmeas
  have hreal : (S.card : ℝ) * δ ^ r ≤ ∏ i : Fin r, (2 * B i + δ) := by
    have h1 : ENNReal.ofReal ((S.card : ℝ) * δ ^ r) ≤ ENNReal.ofReal (∏ i : Fin r, (2 * B i + δ)) := by
      rwa [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_le_ofReal_iff (Finset.prod_nonneg fun i _ => by linarith [hB i])).mp h1
  have hdiv : (S.card : ℝ) ≤ (∏ i : Fin r, (2 * B i + δ)) / δ ^ r :=
    (le_div_iff₀ (pow_pos hδ r)).mpr hreal
  have hprod_div : (∏ i : Fin r, (2 * B i + δ)) / δ ^ r = ∏ i : Fin r, (1 + 2 * B i / δ) := by
    rw [show δ ^ r = ∏ _i : Fin r, δ by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
      ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp [hδ.ne']
    ring
  rwa [hprod_div] at hdiv

end LatticeCounting

/-! ## Section 4: Siegel Reduction & Successive-Minima Two-Sided Inequalities -/

section SiegelReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A `ℤ`-basis `b : Basis (Fin r) ℤ L` is **`(C_diag, C_unip)`-Siegel-reduced** (Iwasawa `KAN`
Siegel domain condition, e.g. `C_diag = 2 / √3`, `C_unip = 1 / 2` for LLL/Siegel reduction) when:
1. Unipotent size-reduction: `|μ_{i, j}| ≤ C_unip` for all `i < j`.
2. Torus cone condition: `‖b*_j‖ ≤ C_diag * ‖b*_{j+1}‖` for all `j + 1 < r`. -/
structure IsSiegelReduced {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L)
    (C_diag C_unip : ℝ) : Prop where
  C_diag_ge_one : 1 ≤ C_diag
  C_unip_nonneg : 0 ≤ C_unip
  size_reduced : ∀ i j : Fin r, i < j → |gsCoeff (fun k => (b k : E)) i j| ≤ C_unip
  height_ratio : ∀ (j : Fin r) (h : j.1 + 1 < r),
    ‖gsVec (fun k => (b k : E)) j‖ ≤ C_diag * ‖gsVec (fun k => (b k : E)) ⟨j.1 + 1, h⟩‖

omit [FiniteDimensional ℝ E] in
/-- Telescoping Siegel-cone inequality: for `i ≤ j`, `‖b*_i‖ ≤ C_diag^(j - i) * ‖b*_j‖`. -/
theorem IsSiegelReduced.gsNorm_telescope {L : Submodule ℤ E} {r : ℕ} {b : Basis (Fin r) ℤ L}
    {C_diag C_unip : ℝ} (hS : IsSiegelReduced b C_diag C_unip) :
    ∀ {i j : Fin r}, i ≤ j →
      ‖gsVec (fun k => (b k : E)) i‖ ≤ C_diag ^ (j.1 - i.1) * ‖gsVec (fun k => (b k : E)) j‖ := by
  have hstep : ∀ d : ℕ, ∀ i j : Fin r, j.1 = i.1 + d →
      ‖gsVec (fun k => (b k : E)) i‖ ≤ C_diag ^ d * ‖gsVec (fun k => (b k : E)) j‖ := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have hEq : i = j := Fin.ext (by omega)
      subst hEq
      simp
    | succ d ih =>
      intro i j hij
      have hm_lt : i.1 + d < r := by omega
      let m : Fin r := ⟨i.1 + d, hm_lt⟩
      have hm_val : m.1 = i.1 + d := rfl
      have h1 := ih i m hm_val
      have hm1_lt : m.1 + 1 < r := by omega
      have h2 := hS.height_ratio m hm1_lt
      have hjEq : (⟨m.1 + 1, hm1_lt⟩ : Fin r) = j := Fin.ext (show m.1 + 1 = j.1 by omega)
      rw [hjEq] at h2
      calc ‖gsVec (fun k => (b k : E)) i‖
          ≤ C_diag ^ d * ‖gsVec (fun k => (b k : E)) m‖ := h1
        _ ≤ C_diag ^ d * (C_diag * ‖gsVec (fun k => (b k : E)) j‖) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith [hS.C_diag_ge_one]) d)
        _ = C_diag ^ (d + 1) * ‖gsVec (fun k => (b k : E)) j‖ := by rw [pow_succ]; ring
  intro i j hij
  exact hstep (j.1 - i.1) i j (by omega)

/-- **Siegel-Reduced First-Minimum Lower Bound**:
in a `(C_diag, C_unip)`-Siegel-reduced basis of `L` (`r = rk L > 0`),
`‖b*_0‖ ≤ C_diag ^ (r - 1) * λ_1(L)`. -/
theorem IsSiegelReduced.first_minimum_ge {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (hr : 0 < r) {b : Basis (Fin r) ℤ L} {C_diag C_unip : ℝ}
    (hS : IsSiegelReduced b C_diag C_unip) :
    ‖gsVec (fun k => (b k : E)) ⟨0, hr⟩‖ ≤ C_diag ^ (r - 1) * lambda1 L := by
  have hL0 : L ≠ ⊥ := by
    intro hbot
    have h0 : (b ⟨0, hr⟩ : E) = 0 :=
      (Submodule.mem_bot ℤ).mp (hbot ▸ (b ⟨0, hr⟩).2)
    exact (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero ⟨0, hr⟩ h0
  obtain ⟨v₀, hv₀L, hv₀0, hv₀eq⟩ := exists_norm_eq_lambda1 L hL0
  obtain ⟨k, hk⟩ := exists_gsVec_norm_le_of_mem_ne_zero b hv₀L hv₀0
  have htel := hS.gsNorm_telescope (i := ⟨0, hr⟩) (j := k) (Nat.zero_le k.1)
  have hpow : C_diag ^ (k.1 - 0) ≤ C_diag ^ (r - 1) :=
    pow_le_pow_right₀ hS.C_diag_ge_one (by omega)
  calc ‖gsVec (fun j => (b j : E)) ⟨0, hr⟩‖
      ≤ C_diag ^ (k.1 - 0) * ‖gsVec (fun j => (b j : E)) k‖ := htel
    _ ≤ C_diag ^ (r - 1) * ‖gsVec (fun j => (b j : E)) k‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ C_diag ^ (r - 1) * ‖v₀‖ :=
        mul_le_mul_of_nonneg_left hk (pow_nonneg (by linarith [hS.C_diag_ge_one]) _)
    _ = C_diag ^ (r - 1) * lambda1 L := by rw [hv₀eq]

omit [FiniteDimensional ℝ E] in
/-- Uniform Siegel-reduced basis vector norm bound:
`‖b_j‖ ≤ √(1 + r * C_unip² * C_diag^(2 r)) * ‖b*_j‖`. -/
theorem IsSiegelReduced.norm_le_gsNorm {L : Submodule ℤ E} {r : ℕ} {b : Basis (Fin r) ℤ L}
    {C_diag C_unip : ℝ} (hS : IsSiegelReduced b C_diag C_unip) (j : Fin r) :
    ‖(b j : E)‖ ≤
      Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
        ‖gsVec (fun k => (b k : E)) j‖ := by
  have hsq := norm_sq_eq_sum_gsVec (fun k => (b k : E)) j
  have hterm : ∀ i : Fin j.1,
      (gsCoeff (fun k => (b k : E)) ⟨i.1, lt_trans i.2 j.2⟩ j) ^ 2 *
        ‖gsVec (fun k => (b k : E)) ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2 ≤
      C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by
    intro i
    let i' : Fin r := ⟨i.1, lt_trans i.2 j.2⟩
    have hμ : |gsCoeff (fun k => (b k : E)) i' j| ≤ C_unip := hS.size_reduced i' j i.2
    have hμsq : (gsCoeff (fun k => (b k : E)) i' j) ^ 2 ≤ C_unip ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hμ 2
    have htel := hS.gsNorm_telescope (i := i') (j := j) (le_of_lt i.2)
    have htel_sq : ‖gsVec (fun k => (b k : E)) i'‖ ^ 2 ≤
        C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by
      have h1 : ‖gsVec (fun k => (b k : E)) i'‖ ^ 2 ≤
          (C_diag ^ (j.1 - i'.1) * ‖gsVec (fun k => (b k : E)) j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htel 2
      rw [mul_pow, ← pow_mul] at h1
      have hpow : C_diag ^ ((j.1 - i'.1) * 2) ≤ C_diag ^ (2 * r) :=
        pow_le_pow_right₀ hS.C_diag_ge_one (by omega)
      exact h1.trans (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))
    calc (gsCoeff (fun k => (b k : E)) i' j) ^ 2 * ‖gsVec (fun k => (b k : E)) i'‖ ^ 2
        ≤ C_unip ^ 2 * (C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2) :=
          mul_le_mul hμsq htel_sq (sq_nonneg _) (sq_nonneg _)
      _ = C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by ring
  have hsum_le : ∑ i : Fin j.1,
      (gsCoeff (fun k => (b k : E)) ⟨i.1, lt_trans i.2 j.2⟩ j) ^ 2 *
        ‖gsVec (fun k => (b k : E)) ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2 ≤
      (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by
    calc ∑ i : Fin j.1,
          (gsCoeff (fun k => (b k : E)) ⟨i.1, lt_trans i.2 j.2⟩ j) ^ 2 *
            ‖gsVec (fun k => (b k : E)) ⟨i.1, lt_trans i.2 j.2⟩‖ ^ 2
        ≤ ∑ _i : Fin j.1, C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (j.1 : ℝ) * (C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2) := by
          simp [nsmul_eq_mul]
      _ ≤ (r : ℝ) * (C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast j.2.le) ?_
          have hCd0 : 0 ≤ C_diag := by linarith [hS.C_diag_ge_one]
          positivity
      _ = (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by ring
  have htotal : ‖(b j : E)‖ ^ 2 ≤
      (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by
    linarith
  have hfac_nn : 0 ≤ 1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r) := by
    have hCd0 : 0 ≤ C_diag := by linarith [hS.C_diag_ge_one]
    positivity
  have hsq_rhs : (Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
      ‖gsVec (fun k => (b k : E)) j‖) ^ 2 =
      (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) * ‖gsVec (fun k => (b k : E)) j‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hfac_nn]
  have hrhs_nn : 0 ≤ Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
      ‖gsVec (fun k => (b k : E)) j‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (b j : E)]

/-- **Siegel–Hermite Orthogonality-Defect Bound**:
for any `(C_diag, C_unip)`-Siegel-reduced basis `b` of a discrete lattice `L`,
`covol L ≤ ∏ j, ‖b_j‖ ≤ (1 + r * C_unip² * C_diag^(2 r))^(r / 2) * covol L`. -/
theorem IsSiegelReduced.prod_norm_le_covol {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} {b : Basis (Fin r) ℤ L} {C_diag C_unip : ℝ}
    (hS : IsSiegelReduced b C_diag C_unip) :
    RHDirect.ArakelovCovolume.covol L ≤ ∏ j : Fin r, ‖(b j : E)‖ ∧
    ∏ j : Fin r, ‖(b j : E)‖ ≤
      (Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r))) ^ r *
        RHDirect.ArakelovCovolume.covol L := by
  have hcov_eq := covol_eq_prod_gsVec b
  refine ⟨?_, ?_⟩
  · rw [hcov_eq]
    exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => gsVec_norm_le _ j)
  · rw [hcov_eq, show (Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r))) ^ r =
      ∏ _j : Fin r, Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hS.norm_le_gsNorm j)

/-- The `(k + 1)`-th **successive minimum** `λ_{k+1}(L)` (`k : Fin (rk L)`):
`inf { R ≥ 0 | ∃ (v : Fin (k + 1) → E), (∀ i, v i ∈ L) ∧ LinearIndependent ℝ v ∧ ∀ i, ‖v i‖ ≤ R }`. -/
def succMin (L : Submodule ℤ E) (k : Fin (RHDirect.ArakelovCovolume.rk L)) : ℝ :=
  sInf { R : ℝ | 0 ≤ R ∧ ∃ v : Fin (k.1 + 1) → E,
    (∀ i, v i ∈ L) ∧ LinearIndependent ℝ v ∧ ∀ i, ‖v i‖ ≤ R }

private lemma succMin_set_nonempty (L : Submodule ℤ E) [DiscreteTopology L]
    (k : Fin (RHDirect.ArakelovCovolume.rk L)) :
    { R : ℝ | 0 ≤ R ∧ ∃ v : Fin (k.1 + 1) → E,
      (∀ i, v i ∈ L) ∧ LinearIndependent ℝ v ∧ ∀ i, ‖v i‖ ≤ R }.Nonempty := by
  have hk_lt : k.1 < Module.finrank ℤ L := k.2
  let b := Module.finBasis ℤ L
  let v : Fin (k.1 + 1) → E := fun i => (b ⟨i.1, by omega⟩ : E)
  have hli : LinearIndependent ℝ v := by
    have hli0 := RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b
    have hinj : Function.Injective
        (fun i : Fin (k.1 + 1) => (⟨i.1, by omega⟩ : Fin (Module.finrank ℤ L))) :=
      fun a c hac => Fin.ext (Fin.mk.inj hac)
    exact hli0.comp _ hinj
  let R : ℝ := ∑ i : Fin (k.1 + 1), ‖v i‖
  refine ⟨R, Finset.sum_nonneg fun i _ => norm_nonneg _, v, fun i => (b ⟨i.1, by omega⟩).2, hli, ?_⟩
  intro i
  exact Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] in
private lemma succMin_set_bddBelow (L : Submodule ℤ E) (k : Fin (RHDirect.ArakelovCovolume.rk L)) :
    BddBelow { R : ℝ | 0 ≤ R ∧ ∃ v : Fin (k.1 + 1) → E,
      (∀ i, v i ∈ L) ∧ LinearIndependent ℝ v ∧ ∀ i, ‖v i‖ ≤ R } :=
  ⟨0, fun _ h => h.1⟩

/-- Monotonicity of successive minima: `k₁ ≤ k₂ → λ_{k₁+1}(L) ≤ λ_{k₂+1}(L)`. -/
theorem succMin_mono (L : Submodule ℤ E) [DiscreteTopology L]
    {k₁ k₂ : Fin (RHDirect.ArakelovCovolume.rk L)} (h : k₁ ≤ k₂) :
    succMin L k₁ ≤ succMin L k₂ := by
  apply csInf_le_csInf (succMin_set_bddBelow L k₁) (succMin_set_nonempty L k₂)
  rintro R ⟨hR0, v, hvL, hvli, hvR⟩
  refine ⟨hR0, fun i => v ⟨i.1, by omega⟩, fun i => hvL _, ?_, fun i => hvR _⟩
  exact hvli.comp (fun i : Fin (k₁.1 + 1) => (⟨i.1, by omega⟩ : Fin (k₂.1 + 1)))
    (fun a b hab => Fin.ext (Fin.mk.inj hab))

/-- The first successive minimum `succMin L 0` equals `lambda1 L`. -/
theorem succMin_zero_eq_lambda1 (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    succMin L ⟨0, RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0⟩ = lambda1 L := by
  apply le_antisymm
  · obtain ⟨v₀, hv₀L, hv₀0, hv₀eq⟩ := exists_norm_eq_lambda1 L hL0
    rw [← hv₀eq]
    refine csInf_le (succMin_set_bddBelow L _)
      ⟨norm_nonneg v₀, fun _ => v₀, fun _ => hv₀L, ?_, fun _ => le_rfl⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    fin_cases i
    have hc' : c 0 • v₀ = 0 := by
      have h1 : ∑ j : Fin 1, c j • v₀ = 0 := hc
      rwa [Fin.sum_univ_one] at h1
    exact (smul_eq_zero.mp hc').resolve_right hv₀0
  · refine le_csInf (succMin_set_nonempty L _) ?_
    rintro R ⟨_, v, hvL, hvli, hvR⟩
    exact (lambda1_le_norm L (hvL 0) (hvli.ne_zero 0)).trans (hvR 0)

theorem succMin_pos (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (k : Fin (RHDirect.ArakelovCovolume.rk L)) :
    0 < succMin L k := by
  have h0 : (⟨0, RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0⟩ :
      Fin (RHDirect.ArakelovCovolume.rk L)) ≤ k := Nat.zero_le k.1
  calc 0 < lambda1 L := lambda1_pos L hL0
    _ = succMin L ⟨0, RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0⟩ :=
        (succMin_zero_eq_lambda1 L hL0).symm
    _ ≤ succMin L k := succMin_mono L h0

/-- Attainment of each successive minimum `succMin L k` by `k + 1` linearly independent lattice
vectors inside `closedBall 0 (succMin L k)`. -/
theorem exists_vecs_attaining_succMin (L : Submodule ℤ E) [DiscreteTopology L]
    (k : Fin (RHDirect.ArakelovCovolume.rk L)) :
    ∃ v : Fin (k.1 + 1) → E, (∀ i, v i ∈ L) ∧ LinearIndependent ℝ v ∧
      ∀ i, ‖v i‖ ≤ succMin L k := by
  classical
  set lamk := succMin L k
  have h1 : lamk < lamk + 1 := by linarith
  obtain ⟨R₀, ⟨_, v₀, hv₀L, hv₀li, hv₀R⟩, hR₀⟩ :=
    exists_lt_of_csInf_lt (succMin_set_nonempty L k) h1
  let Bfin := lattice_inter_closedBall_finite L (lamk + 1)
  by_contra hnone
  push Not at hnone
  let tuples : Finset (Fin (k.1 + 1) → E) :=
    (Fintype.piFinset fun _ : Fin (k.1 + 1) => Bfin.toFinset).filter fun v =>
      LinearIndependent ℝ v
  have hv₀_mem : v₀ ∈ tuples := by
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => Bfin.mem_toFinset.mpr ⟨hv₀L i, mem_closedBall_zero_iff.mpr ((hv₀R i).trans hR₀.le)⟩,
      hv₀li⟩
  let maxNorm : (Fin (k.1 + 1) → E) → ℝ := fun v =>
    (Finset.univ : Finset (Fin (k.1 + 1))).sup' Finset.univ_nonempty (fun i => ‖v i‖)
  obtain ⟨v_min, hv_min_mem, hv_min_le⟩ := tuples.exists_min_image maxNorm ⟨v₀, hv₀_mem⟩
  have hv_min_f := Finset.mem_filter.mp hv_min_mem
  have hv_min_L : ∀ i, v_min i ∈ L := fun i =>
    (Bfin.mem_toFinset.mp ((Fintype.mem_piFinset.mp hv_min_f.1) i)).1
  obtain ⟨i₀, hi₀⟩ := hnone v_min hv_min_L hv_min_f.2
  have hMgt : lamk < maxNorm v_min :=
    lt_of_lt_of_le hi₀ (Finset.le_sup' (f := fun i => ‖v_min i‖) (Finset.mem_univ i₀))
  have hlt : lamk < min (lamk + 1) (maxNorm v_min) := lt_min h1 hMgt
  obtain ⟨R₁, ⟨_, v₁, hv₁L, hv₁li, hv₁R⟩, hR₁⟩ :=
    exists_lt_of_csInf_lt (succMin_set_nonempty L k) hlt
  have hv₁_mem : v₁ ∈ tuples := by
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => Bfin.mem_toFinset.mpr
      ⟨hv₁L i, mem_closedBall_zero_iff.mpr ((hv₁R i).trans (lt_of_lt_of_le hR₁ (min_le_left _ _)).le)⟩,
      hv₁li⟩
  have hmax1 : maxNorm v₁ ≤ R₁ := Finset.sup'_le _ _ fun i _ => hv₁R i
  have hmin_le : maxNorm v_min ≤ maxNorm v₁ := hv_min_le v₁ hv₁_mem
  have hR₁_lt : R₁ < maxNorm v_min := lt_of_lt_of_le hR₁ (min_le_right _ _)
  linarith

/-- Greedy basis extraction from attaining successive-minima tuples: there exist `r = rk L`
linearly independent vectors `w : Fin r → E` in `L` with `‖w k‖ ≤ succMin L k` for every `k`. -/
theorem exists_independent_le_succMin (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ w : Fin (RHDirect.ArakelovCovolume.rk L) → E,
      (∀ k, w k ∈ L) ∧ LinearIndependent ℝ w ∧ ∀ k, ‖w k‖ ≤ succMin L k := by
  let r := RHDirect.ArakelovCovolume.rk L
  have hrec : ∀ m : ℕ, (hm : m ≤ r) →
      ∃ w : Fin m → E, (∀ k : Fin m, w k ∈ L) ∧ LinearIndependent ℝ w ∧
        ∀ k : Fin m, ‖w k‖ ≤ succMin L ⟨k.1, lt_of_lt_of_le k.2 hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun k => k.elim0, linearIndependent_empty_type, fun k => k.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨w, hwL, hwli, hwb⟩ := ih (Nat.le_of_succ_le hm)
      let k : Fin r := ⟨m, hm⟩
      obtain ⟨v, hvL, hvli, hvb⟩ := exists_vecs_attaining_succMin L k
      have hex : ∃ i : Fin (m + 1), v i ∉ Submodule.span ℝ (Set.range w) := by
        by_contra hall
        push Not at hall
        have hsub : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range w) :=
          Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
        have hdim_v : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = m + 1 := by
          rw [finrank_span_eq_card hvli, Fintype.card_fin]
        have hdim_w : Module.finrank ℝ (Submodule.span ℝ (Set.range w)) = m := by
          rw [finrank_span_eq_card hwli, Fintype.card_fin]
        have hle := Submodule.finrank_mono hsub
        omega
      obtain ⟨i₀, hi₀⟩ := hex
      let w' : Fin (m + 1) → E := Fin.snoc w (v i₀)
      refine ⟨w', ?_, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simpa [w'] using hvL i₀
        · intro j'; simpa [w'] using hwL j'
      · rw [Fintype.linearIndependent_iff]
        intro c hc
        have hsplit : ∑ j : Fin (m + 1), c j • w' j =
            (∑ j : Fin m, c j.castSucc • w j) + c (Fin.last m) • v i₀ := by
          rw [Fin.sum_univ_castSucc]
          simp [w']
        rw [hsplit] at hc
        have hclast : c (Fin.last m) = 0 := by
          by_contra hc0
          have hmem : v i₀ ∈ Submodule.span ℝ (Set.range w) := by
            have h1 : v i₀ = -(c (Fin.last m))⁻¹ • ∑ j : Fin m, c j.castSucc • w j := by
              have h2 : c (Fin.last m) • v i₀ = -(∑ j : Fin m, c j.castSucc • w j) :=
                eq_neg_of_add_eq_zero_right hc
              calc v i₀ = (c (Fin.last m))⁻¹ • (c (Fin.last m) • v i₀) :=
                    (inv_smul_smul₀ hc0 _).symm
                _ = (c (Fin.last m))⁻¹ • -(∑ j : Fin m, c j.castSucc • w j) := by rw [h2]
                _ = -(c (Fin.last m))⁻¹ • ∑ j : Fin m, c j.castSucc • w j := by rw [smul_neg, neg_smul]
            rw [h1]
            exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
          exact hi₀ hmem
        rw [hclast, zero_smul, add_zero] at hc
        have hcrest := Fintype.linearIndependent_iff.mp hwli (fun j => c j.castSucc) hc
        intro j
        exact Fin.lastCases hclast hcrest j
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simpa [w', k] using hvb i₀
        · intro j'; simpa [w'] using hwb j'
  exact hrec r le_rfl

/-- **Hadamard Lower Bound on the Product of Successive Minima**:
for every discrete lattice `L ⊂ E`, `covol L ≤ ∏ k : Fin (rk L), succMin L k`. -/
theorem covol_le_prod_succMin (L : Submodule ℤ E) [DiscreteTopology L] :
    RHDirect.ArakelovCovolume.covol L ≤ ∏ k : Fin (RHDirect.ArakelovCovolume.rk L), succMin L k := by
  obtain ⟨w, hwL, hwli, hwb⟩ := exists_independent_le_succMin L
  exact (covol_le_prod_norm w hwL hwli rfl).trans
    (Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hwb k))

/-- **Siegel-Reduced Lower Bound on Every Successive Minimum**:
in a `(C_diag, C_unip)`-Siegel-reduced basis `b : Basis (Fin (rk L)) ℤ L`,
`‖b*_k‖ ≤ C_diag ^ (rk L - 1) * succMin L k` for every `k : Fin (rk L)`. -/
theorem IsSiegelReduced.gsNorm_le_succMin {L : Submodule ℤ E} [DiscreteTopology L]
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L} {C_diag C_unip : ℝ}
    (hS : IsSiegelReduced b C_diag C_unip) (k : Fin (RHDirect.ArakelovCovolume.rk L)) :
    ‖gsVec (fun i => (b i : E)) k‖ ≤
      C_diag ^ (RHDirect.ArakelovCovolume.rk L - 1) * succMin L k := by
  classical
  let r := RHDirect.ArakelovCovolume.rk L
  obtain ⟨v, hvL, hvli, hvb⟩ := exists_vecs_attaining_succMin L k
  have hex : ∃ t : Fin (k.1 + 1), ∃ j : Fin r, k ≤ j ∧
      ‖gsVec (fun i => (b i : E)) j‖ ≤ ‖v t‖ := by
    by_contra hall
    push Not at hall
    have hsub : Submodule.span ℝ (Set.range v) ≤
        Submodule.span ℝ (Set.range fun i : Fin k.1 => (b ⟨i.1, lt_trans i.2 k.2⟩ : E)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨t, rfl⟩
      let c : Fin r → ℤ := fun i => b.repr ⟨v t, hvL t⟩ i
      have hvt_eq : v t = ∑ j : Fin r, (c j : ℝ) • (b j : E) := by
        have h1 := congrArg Subtype.val (b.sum_repr ⟨v t, hvL t⟩)
        rw [Submodule.coe_sum] at h1
        change ∑ j : Fin r, ((c j • b j : L) : E) = v t at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Submodule.coe_smul]
        exact (Int.cast_smul_eq_zsmul ℝ (c j) (b j : E)).symm
      have hzero_ge : ∀ j : Fin r, k ≤ j → c j = 0 := by
        by_contra hnz
        push Not at hnz
        let S : Finset (Fin r) := Finset.univ.filter fun j => c j ≠ 0
        obtain ⟨j₀, hj₀k, hj₀nz⟩ := hnz
        have hS : S.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀nz⟩⟩
        let jmax : Fin r := S.max' hS
        have hjmax_ge : k ≤ jmax := le_trans hj₀k (Finset.le_max' S j₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀nz⟩))
        have hcjmax : c jmax ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
        have htop : ∀ j : Fin r, jmax < j → (c j : ℝ) = 0 := by
          intro j hj
          by_contra hc0
          exact not_lt.mpr (Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, by exact_mod_cast hc0⟩)) hj
        have hge := norm_ge_gsVec_of_max_nonzero (fun i => (b i : E)) (fun i => (c i : ℝ)) jmax htop
        rw [← hvt_eq] at hge
        have h1 : (1 : ℝ) ≤ |(c jmax : ℝ)| := by
          have : (1 : ℤ) ≤ |c jmax| := Int.one_le_abs hcjmax
          exact_mod_cast this
        have hle := le_trans (le_mul_of_one_le_left (norm_nonneg _) h1) hge
        exact not_le.mpr (hall t jmax hjmax_ge) hle
      rw [hvt_eq]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hjk : j < k
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.1, hjk⟩, rfl⟩)
      · rw [hzero_ge j (not_lt.mp hjk), Int.cast_zero, zero_smul]
        exact Submodule.zero_mem _
    have hdim_v : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = k.1 + 1 := by
      rw [finrank_span_eq_card hvli, Fintype.card_fin]
    have hdim_b : Module.finrank ℝ
        (Submodule.span ℝ (Set.range fun i : Fin k.1 => (b ⟨i.1, lt_trans i.2 k.2⟩ : E))) ≤ k.1 := by
      have : Fintype (Set.range fun i : Fin k.1 => (b ⟨i.1, lt_trans i.2 k.2⟩ : E)) :=
        Set.fintypeRange _
      exact (finrank_span_le_card _).trans (by
        simpa [Fintype.card_fin] using Finset.card_image_le
          (f := fun i : Fin k.1 => (b ⟨i.1, lt_trans i.2 k.2⟩ : E)) (s := Finset.univ))
    have hle := Submodule.finrank_mono hsub
    omega
  obtain ⟨t, j, hkj, hj_le⟩ := hex
  have htel := hS.gsNorm_telescope hkj
  have hpow : C_diag ^ (j.1 - k.1) ≤ C_diag ^ (r - 1) :=
    pow_le_pow_right₀ hS.C_diag_ge_one (by omega)
  calc ‖gsVec (fun i => (b i : E)) k‖
      ≤ C_diag ^ (j.1 - k.1) * ‖gsVec (fun i => (b i : E)) j‖ := htel
    _ ≤ C_diag ^ (r - 1) * ‖gsVec (fun i => (b i : E)) j‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ C_diag ^ (r - 1) * ‖v t‖ :=
        mul_le_mul_of_nonneg_left hj_le (pow_nonneg (by linarith [hS.C_diag_ge_one]) _)
    _ ≤ C_diag ^ (r - 1) * succMin L k :=
        mul_le_mul_of_nonneg_left (hvb t) (pow_nonneg (by linarith [hS.C_diag_ge_one]) _)

/-- **Siegel-Reduced Upper Bound on Every Successive Minimum & Product of Successive Minima**:
in a `(C_diag, C_unip)`-Siegel-reduced basis `b` of `L`:
1. `succMin L k ≤ √(1 + r * C_unip² * C_diag^(2 r)) * C_diag^k * ‖b*_k‖` for every `k : Fin r`,
2. `∏ k, succMin L k ≤ (√(1 + r * C_unip² * C_diag^(2 r)) * C_diag^r)^r * covol L`. -/
theorem IsSiegelReduced.succMin_le_gsNorm {L : Submodule ℤ E} [DiscreteTopology L]
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L} {C_diag C_unip : ℝ}
    (hS : IsSiegelReduced b C_diag C_unip) (k : Fin (RHDirect.ArakelovCovolume.rk L)) :
    succMin L k ≤
      Real.sqrt (1 + (RHDirect.ArakelovCovolume.rk L : ℝ) * C_unip ^ 2 *
        C_diag ^ (2 * RHDirect.ArakelovCovolume.rk L)) *
        C_diag ^ k.1 * ‖gsVec (fun i => (b i : E)) k‖ := by
  let r := RHDirect.ArakelovCovolume.rk L
  set M : ℝ := Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
      C_diag ^ k.1 * ‖gsVec (fun i => (b i : E)) k‖
  have hCd0 : 0 ≤ C_diag := by linarith [hS.C_diag_ge_one]
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hCd0 _)) (norm_nonneg _)
  let v : Fin (k.1 + 1) → E := fun i => (b ⟨i.1, by omega⟩ : E)
  have hvli : LinearIndependent ℝ v :=
    (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).comp
      (fun i : Fin (k.1 + 1) => (⟨i.1, by omega⟩ : Fin r))
      (fun a c hac => Fin.ext (Fin.mk.inj hac))
  refine csInf_le (succMin_set_bddBelow L k) ⟨hM0, v, fun i => (b ⟨i.1, by omega⟩).2, hvli, ?_⟩
  intro i
  let i' : Fin r := ⟨i.1, by omega⟩
  have hi'le : i' ≤ k := Nat.le_of_lt_succ i.2
  have h1 := hS.norm_le_gsNorm i'
  have h2 := hS.gsNorm_telescope hi'le
  have hpow : C_diag ^ (k.1 - i'.1) ≤ C_diag ^ k.1 :=
    pow_le_pow_right₀ hS.C_diag_ge_one (Nat.sub_le k.1 i'.1)
  calc ‖v i‖ = ‖(b i' : E)‖ := rfl
    _ ≤ Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
          ‖gsVec (fun j => (b j : E)) i'‖ := h1
    _ ≤ Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
          (C_diag ^ (k.1 - i'.1) * ‖gsVec (fun j => (b j : E)) k‖) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) *
          (C_diag ^ k.1 * ‖gsVec (fun j => (b j : E)) k‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = M := by ring

theorem IsSiegelReduced.prod_succMin_le_covol {L : Submodule ℤ E} [DiscreteTopology L]
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L} {C_diag C_unip : ℝ}
    (hS : IsSiegelReduced b C_diag C_unip) :
    RHDirect.ArakelovCovolume.covol L ≤ ∏ k : Fin (RHDirect.ArakelovCovolume.rk L), succMin L k ∧
    ∏ k : Fin (RHDirect.ArakelovCovolume.rk L), succMin L k ≤
      (Real.sqrt (1 + (RHDirect.ArakelovCovolume.rk L : ℝ) * C_unip ^ 2 *
        C_diag ^ (2 * RHDirect.ArakelovCovolume.rk L)) *
        C_diag ^ RHDirect.ArakelovCovolume.rk L) ^ RHDirect.ArakelovCovolume.rk L *
        RHDirect.ArakelovCovolume.covol L := by
  let r := RHDirect.ArakelovCovolume.rk L
  refine ⟨covol_le_prod_succMin L, ?_⟩
  rw [covol_eq_prod_gsVec b]
  set A : ℝ := Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) * C_diag ^ r
  rw [show A ^ r = ∏ _k : Fin r, A by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun k _ => le_csInf (succMin_set_nonempty L k) fun _ h => h.1) fun k _ => ?_
  have h1 := hS.succMin_le_gsNorm k
  have hpow : C_diag ^ k.1 ≤ C_diag ^ r := pow_le_pow_right₀ hS.C_diag_ge_one k.2.le
  calc succMin L k
      ≤ Real.sqrt (1 + (r : ℝ) * C_unip ^ 2 * C_diag ^ (2 * r)) * C_diag ^ k.1 *
          ‖gsVec (fun i => (b i : E)) k‖ := h1
    _ ≤ A * ‖gsVec (fun i => (b i : E)) k‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)

end SiegelReduction

/-! ## Section 5: Bridges to `ArakelovCovolume`, `BostSlopeFiber`, `SiegelSetEnvelope` & `UnitaryMassFormula` -/

section Bridges

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **First-Minimum Lower Bound on Maximal Arakelov Slope**:
`-log λ_1(L) ≤ μ_max(L)`. -/
theorem neg_log_lambda1_le_muMax (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    -Real.log (lambda1 L) ≤ RHDirect.ArakelovCovolume.muMax L := by
  obtain ⟨v₀, hv₀L, hv₀0, hv₀eq⟩ := exists_norm_eq_lambda1 L hL0
  let N : Submodule ℤ E := Submodule.span ℤ ({v₀} : Set E)
  have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ rfl; exact hv₀L)
  have hN0 : N ≠ ⊥ := by
    intro h0
    have hm : v₀ ∈ N := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at hm
    exact hv₀0 hm
  rw [← hv₀eq, ← RHDirect.ArakelovCovolume.slope_span_singleton hv₀0]
  exact RHDirect.ArakelovCovolume.slope_le_muMax L N hNL hN0

/-- **Minkowski–Hermite Slope-Gap Inequality**:
`slope L - (1 / 2) * log (rk L) ≤ -log λ_1(L) ≤ μ_max(L)`. -/
theorem slope_sub_half_log_rk_le_neg_log_lambda1 (L : Submodule ℤ E) [DiscreteTopology L]
    (hL0 : L ≠ ⊥) :
    RHDirect.ArakelovCovolume.slope L - (1 / 2) * Real.log (RHDirect.ArakelovCovolume.rk L : ℝ) ≤
      -Real.log (lambda1 L) := by
  have hrpos : (0 : ℝ) < (RHDirect.ArakelovCovolume.rk L : ℝ) :=
    Nat.cast_pos.mpr (RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0)
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  have hlam_pos : 0 < lambda1 L := lambda1_pos L hL0
  have hH := lambda1_le_hermite L hL0
  have hlog := Real.log_le_log hlam_pos hH
  rw [Real.log_mul (Real.sqrt_pos.mpr hrpos).ne' (Real.rpow_pos_of_pos hcov_pos _).ne',
    Real.log_sqrt hrpos.le, Real.log_rpow hcov_pos] at hlog
  unfold RHDirect.ArakelovCovolume.slope RHDirect.ArakelovCovolume.degAr
  have hdiv : -Real.log (RHDirect.ArakelovCovolume.covol L) / (RHDirect.ArakelovCovolume.rk L : ℝ) =
      -(1 / (RHDirect.ArakelovCovolume.rk L : ℝ) * Real.log (RHDirect.ArakelovCovolume.covol L)) := by
    ring
  linarith

/-- **Bost–Minkowski First-Minimum Ceiling on a `BostSlopeFiber`**:
if a discrete lattice `L` (`L ≠ ⊥`) represents the common dual fiber `CC` (`B.muCC = slope L`)
and `B.SlopeIneq` holds, then Minkowski–Hermite yields an explicit upper bound on `lambda1 L`:
`lambda1 L ≤ √(rk L) * exp (-(B.s - log |W| - loss(B)))`. -/
theorem bostSlopeFiber_lambda1_upper_of_slopeIneq (B : RHDirect.BostSlopeFiber)
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η) (he0 : 0 ≤ B.e) (he4 : B.e ≤ 1 / 4)
    (hHH_ge : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hmuCC : B.muCC = RHDirect.ArakelovCovolume.slope L) :
    lambda1 L ≤ Real.sqrt (RHDirect.ArakelovCovolume.rk L : ℝ) *
      Real.exp (-(B.s - Real.log (B.cardW : ℝ) -
        (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
          (B.η + 4 * Real.sqrt B.e) * B.HH))) := by
  have hrpos : (0 : ℝ) < (RHDirect.ArakelovCovolume.rk L : ℝ) :=
    Nat.cast_pos.mpr (RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0)
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  have hS := hSlope hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos
  rw [hmuCC] at hS
  set RHS := B.s - Real.log (B.cardW : ℝ) -
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH)
  have hcov_rpow : (RHDirect.ArakelovCovolume.covol L) ^ (1 / (RHDirect.ArakelovCovolume.rk L : ℝ)) ≤
      Real.exp (-RHS) := by
    rw [Real.rpow_def_of_pos hcov_pos]
    apply Real.exp_le_exp.mpr
    unfold RHDirect.ArakelovCovolume.slope RHDirect.ArakelovCovolume.degAr at hS
    rw [le_div_iff₀ hrpos] at hS
    have hmul : Real.log (RHDirect.ArakelovCovolume.covol L) *
        (1 / (RHDirect.ArakelovCovolume.rk L : ℝ)) ≤ -RHS := by
      rw [mul_one_div, div_le_iff₀ hrpos]
      linarith
    exact hmul
  exact (lambda1_le_hermite L hL0).trans
    (mul_le_mul_of_nonneg_left hcov_rpow (Real.sqrt_nonneg _))

/-- **Siegel-Reduced Covolume Comparison on a `BostSlopeFiber`**:
if `L` admits a `(C_diag, C_unip)`-Siegel-reduced basis `b` whose Iwasawa heights satisfy
`0 < h_min ≤ ‖b*_j‖` for all `j`, then `covol L ≥ h_min ^ (rk L)`, `slope L ≤ -log h_min`,
and `B.SlopeIneq` immediately bounds `B.s` by `-log h_min + log |W| + loss(B)`. -/
theorem bostSlopeFiber_covolume_of_siegelReduced (B : RHDirect.BostSlopeFiber)
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L} {C_diag C_unip h_min : ℝ}
    (_hS : IsSiegelReduced b C_diag C_unip)
    (hhpos : 0 < h_min) (hh : ∀ j, h_min ≤ ‖gsVec (fun i => (b i : E)) j‖)
    (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η) (he0 : 0 ≤ B.e) (he4 : B.e ≤ 1 / 4)
    (hHH_ge : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hmuCC : B.muCC ≤ RHDirect.ArakelovCovolume.slope L) :
    h_min ^ (RHDirect.ArakelovCovolume.rk L) ≤ RHDirect.ArakelovCovolume.covol L ∧
    RHDirect.ArakelovCovolume.slope L ≤ -Real.log h_min ∧
    B.s ≤ -Real.log h_min + Real.log (B.cardW : ℝ) +
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) := by
  have hrpos : (0 : ℝ) < (RHDirect.ArakelovCovolume.rk L : ℝ) :=
    Nat.cast_pos.mpr (RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0)
  have hcov_ge : h_min ^ (RHDirect.ArakelovCovolume.rk L) ≤ RHDirect.ArakelovCovolume.covol L := by
    rw [covol_eq_prod_gsVec b,
      show h_min ^ (RHDirect.ArakelovCovolume.rk L) =
        ∏ _j : Fin (RHDirect.ArakelovCovolume.rk L), h_min by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    exact Finset.prod_le_prod (fun _ _ => hhpos.le) (fun j _ => hh j)
  have hslope_le : RHDirect.ArakelovCovolume.slope L ≤ -Real.log h_min := by
    have hlog := Real.log_le_log (pow_pos hhpos _) hcov_ge
    rw [Real.log_pow] at hlog
    unfold RHDirect.ArakelovCovolume.slope RHDirect.ArakelovCovolume.degAr
    rw [div_le_iff₀ hrpos]
    linarith
  have hBost := RHDirect.ArakelovCovolume.bostSlopeFiber_covolume_comparison B (-Real.log h_min)
    hSlope hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos (hmuCC.trans hslope_le)
  exact ⟨hcov_ge, hslope_le, hBost⟩

/-- **Siegel-Set Envelope Construction from Lattice-Reduction First-Minimum Heights**:
given a measurable family of lattices `L : X → Submodule ℤ E` on `(X, μ)` whose Siegel height
`H(x) = max 1 (lambda1 (L x))⁻¹` (the reciprocal of the first minimum, capped below at `1`)
satisfies the polynomial Siegel-set volume integrability `∫ H(x)^(-critExp) dμ < ∞`, we obtain
a concrete `RHDirect.SiegelWeilCore.SiegelSetEnvelope μ`! -/
def siegelSetEnvelope_of_lattice_height {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : X → Submodule ℤ E) (critExp : ℝ)
    (hmeas : AEStronglyMeasurable (fun x => max (1 : ℝ) (lambda1 (L x))⁻¹) μ)
    (hint : Integrable (fun x => (max (1 : ℝ) (lambda1 (L x))⁻¹) ^ (-critExp)) μ) :
    RHDirect.SiegelWeilCore.SiegelSetEnvelope μ where
  H := fun x => max (1 : ℝ) (lambda1 (L x))⁻¹
  H_meas := hmeas
  H_ge_one := Filter.Eventually.of_forall fun _ => le_max_left _ _
  critExp := critExp
  vol_integrable := hint

/-- **Theta-Kernel Integrability from Lattice-Ball Counting + Siegel-Set Envelope**:
if a theta kernel `θ : X → ℂ` on a Siegel fundamental domain `(X, μ)` is dominated pointwise by
`C * #(L(x) ∩ B̄(0, R)) * H(x)^(-decayExp)` where `L(x)` has constant rank `r`, `0 ≤ R`, and
`decayExp ≥ critExp + r`, then our ball-counting bound `#(L(x) ∩ B̄(0, R)) ≤ (1 + 2 R / λ₁(L x))^r
≤ (1 + 2 R)^r * H(x)^r` combines with `SiegelWeilCore.thetaKernel_integrable_of_siegel_envelope`
to prove that `θ` is Bochner integrable with an explicit `L¹` norm bound! -/
theorem thetaKernel_integrable_of_lattice_ball_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (L : X → Submodule ℤ E) [∀ x, DiscreteTopology (L x)]
    (hL0 : ∀ x, L x ≠ ⊥) {r : ℕ} (hrk : ∀ x, RHDirect.ArakelovCovolume.rk (L x) = r)
    {critExp decayExp R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (hExp : critExp + (r : ℝ) ≤ decayExp)
    (hmeas : AEStronglyMeasurable (fun x => max (1 : ℝ) (lambda1 (L x))⁻¹) μ)
    (hint : Integrable (fun x => (max (1 : ℝ) (lambda1 (L x))⁻¹) ^ (-critExp)) μ)
    {θ : X → ℂ} (hθm : AEStronglyMeasurable θ μ)
    (hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * (((L x : Set E) ∩ Metric.closedBall (0 : E) R).ncard : ℝ) *
      (max (1 : ℝ) (lambda1 (L x))⁻¹) ^ (-decayExp)) :
    Integrable θ μ ∧
      ‖∫ x, θ x ∂μ‖ ≤
        (C * (1 + 2 * R) ^ r) * ∫ x, (max (1 : ℝ) (lambda1 (L x))⁻¹) ^ (-critExp) ∂μ := by
  let Env := siegelSetEnvelope_of_lattice_height μ L critExp hmeas hint
  have hC' : 0 ≤ C * (1 + 2 * R) ^ r := mul_nonneg hC (pow_nonneg (by linarith) r)
  have hExp' : Env.critExp ≤ decayExp - (r : ℝ) := by dsimp [Env, siegelSetEnvelope_of_lattice_height]; linarith
  have hdom : ∀ᵐ x ∂μ, ‖θ x‖ ≤ (C * (1 + 2 * R) ^ r) * (Env.H x) ^ (-(decayExp - (r : ℝ))) := by
    filter_upwards [hθb] with x hx
    set Hx : ℝ := max (1 : ℝ) (lambda1 (L x))⁻¹
    have hHx1 : 1 ≤ Hx := le_max_left _ _
    have hHxpos : 0 < Hx := lt_of_lt_of_le zero_lt_one hHx1
    have hinv_le : (lambda1 (L x))⁻¹ ≤ Hx := le_max_right _ _
    have hcnt : (((L x : Set E) ∩ Metric.closedBall (0 : E) R).ncard : ℝ) ≤
        (1 + 2 * R) ^ r * Hx ^ r := by
      have h1 := ncard_lattice_closedBall_le (L x) (hL0 x) hR
      rw [hrk x] at h1
      have hbase : 1 + 2 * R / lambda1 (L x) ≤ (1 + 2 * R) * Hx := by
        rw [div_eq_mul_inv]
        nlinarith [hHx1, hinv_le, hR]
      have hnn : 0 ≤ 1 + 2 * R / lambda1 (L x) :=
        add_nonneg zero_le_one (div_nonneg (by linarith) (lambda1_pos (L x) (hL0 x)).le)
      exact h1.trans (by rw [← mul_pow]; exact pow_le_pow_left₀ hnn hbase r)
    have hpow_combine : Hx ^ r * Hx ^ (-decayExp) = Hx ^ (-(decayExp - (r : ℝ))) := by
      rw [← Real.rpow_natCast Hx r, ← Real.rpow_add hHxpos]
      congr 1
      ring
    calc ‖θ x‖
        ≤ C * (((L x : Set E) ∩ Metric.closedBall (0 : E) R).ncard : ℝ) * Hx ^ (-decayExp) := hx
      _ ≤ C * ((1 + 2 * R) ^ r * Hx ^ r) * Hx ^ (-decayExp) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcnt hC) (Real.rpow_nonneg hHxpos.le _)
      _ = (C * (1 + 2 * R) ^ r) * (Hx ^ r * Hx ^ (-decayExp)) := by ring
      _ = (C * (1 + 2 * R) ^ r) * Hx ^ (-(decayExp - (r : ℝ))) := by rw [hpow_combine]
  have hres := RHDirect.SiegelWeilCore.thetaKernel_integrable_of_siegel_envelope Env hC' hExp' hθm hdom
  exact ⟨hres.1, hres.2.2⟩

/-- **Automorphism-Ball Lower Bound on `UnitaryMassFormula.genusMass`**:
if each genus representative `g i` has its discrete automorphism group `Aut(L_i) = Γ ∩ g_i K g_i⁻¹`
injecting into the Euclidean lattice ball `(L i : Set E) ∩ B̄(0, R i)` (for instance, via its
faithful action on a short generating vector/frame of norm `≤ R i`), then every `Aut(L_i)` is
automatically finite and `genusMass Γ K g` satisfies the explicit strictly positive lower bound
`∑ i, ((1 + 2 * R i / λ₁(L i)) ^ (rk (L i)))⁻¹ ≤ genusMass Γ K g`. -/
theorem genusMass_ge_of_lattice_ball_embed {G : Type*} [Group G] {Γ K : Subgroup G}
    {ι : Type*} [Fintype ι] (g : ι → G)
    (L : ι → Submodule ℤ E) [∀ i, DiscreteTopology (L i)] (hL0 : ∀ i, L i ≠ ⊥)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i)
    (embed : ∀ i, RHDirect.UnitaryMassFormula.genusAut Γ K (g i) →
      ↥((L i : Set E) ∩ Metric.closedBall (0 : E) (R i)))
    (hembed : ∀ i, Function.Injective (embed i)) :
    (∀ i, (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)).Finite) ∧
    ∑ i : ι, ((1 + 2 * R i / lambda1 (L i)) ^ (RHDirect.ArakelovCovolume.rk (L i)))⁻¹ ≤
      RHDirect.UnitaryMassFormula.genusMass Γ K g := by
  have hfin : ∀ i, (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)).Finite := by
    intro i
    have : Finite ↥((L i : Set E) ∩ Metric.closedBall (0 : E) (R i)) :=
      (lattice_inter_closedBall_finite (L i) (R i)).to_subtype
    have : Finite (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)) :=
      Finite.of_injective (embed i) (hembed i)
    exact Set.toFinite _
  refine ⟨hfin, ?_⟩
  unfold RHDirect.UnitaryMassFormula.genusMass
  refine Finset.sum_le_sum fun i _ => ?_
  have : Finite ↥((L i : Set E) ∩ Metric.closedBall (0 : E) (R i)) :=
    (lattice_inter_closedBall_finite (L i) (R i)).to_subtype
  have : Finite (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)) := (hfin i).to_subtype
  have : Nonempty (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)) :=
    ⟨⟨1, RHDirect.UnitaryMassFormula.one_mem_genusAut Γ K (g i)⟩⟩
  have hcard_pos : (0 : ℝ) < (Nat.card (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)) : ℝ) :=
    Nat.cast_pos.mpr Nat.card_pos
  have hcard_le_nat : Nat.card (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)) ≤
      ((L i : Set E) ∩ Metric.closedBall (0 : E) (R i)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (embed i) (hembed i)
  have hcard_le : (Nat.card (RHDirect.UnitaryMassFormula.genusAut Γ K (g i)) : ℝ) ≤
      (1 + 2 * R i / lambda1 (L i)) ^ (RHDirect.ArakelovCovolume.rk (L i)) :=
    (by exact_mod_cast hcard_le_nat : (Nat.card _ : ℝ) ≤ _).trans
      (ncard_lattice_closedBall_le (L i) (hL0 i) (hR i))
  exact inv_anti₀ hcard_pos hcard_le

/-- **Siegel Fundamental-Domain Volume Lower Bound** combining `UnitaryMassFormula.measure_fd_toReal_eq_mul_genusMass`
with lattice-ball automorphism bounds. -/
theorem measure_fd_ge_of_lattice_ball_embed {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKfin : μ K ≠ ⊤)
    {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (L : ι → Submodule ℤ E) [∀ i, DiscreteTopology (L i)] (hL0 : ∀ i, L i ≠ ⊥)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i)
    (embed : ∀ i, RHDirect.UnitaryMassFormula.genusAut Γ K (g i) →
      ↥((L i : Set E) ∩ Metric.closedBall (0 : E) (R i)))
    (hembed : ∀ i, Function.Injective (embed i)) :
    (μ K).toReal *
        ∑ i : ι, ((1 + 2 * R i / lambda1 (L i)) ^ (RHDirect.ArakelovCovolume.rk (L i)))⁻¹ ≤
      (μ 𝓕).toReal := by
  obtain ⟨hfin, hmass_ge⟩ := genusMass_ge_of_lattice_ball_embed g L hL0 R hR embed hembed
  rw [RHDirect.UnitaryMassFormula.measure_fd_toReal_eq_mul_genusMass μ hK hKfin g hcov hdisj hfin h𝓕]
  exact mul_le_mul_of_nonneg_left hmass_ge ENNReal.toReal_nonneg

end Bridges

end

end RHDirect.Stage2SiegelReduction
