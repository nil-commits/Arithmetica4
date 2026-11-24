import RHDirect.Stage2SiegelReduction
import RHDirect.Stage10GeometryOfNumbers
import Mathlib.Algebra.Order.Round

/-!
# RHDirect.Stage11LLLSiegelReduction

Unconditional, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of **Exact Gram–Schmidt
Orthogonalization, Unconditional Lovász LLL-Reduced Basis Existence, Sharp LLL Bounds, and Direct
Discharge of `Stage2SiegelReduction.IsSiegelReduced` & `Stage3ThetaSiegelFiberWitness`** in pure
Mathlib `v4.33.1`.

## Contents

1. **Exact Gram–Schmidt Orthogonalization for Any Basis `b : Basis (Fin n) ℝ E`**:
   - Definitions `gramSchmidtVec`, `gramSchmidtOrtho`, `gsMu`, and `μ` (`j < i`).
   - Exact pairwise orthogonality (`gramSchmidtOrtho_orthogonal`), nonvanishing
     (`gramSchmidtOrtho_ne_zero`), upper-triangular expansion (`gramSchmidt_triangular`,
     `gramSchmidt_expansion_full`), Pythagorean norm identity (`gramSchmidt_norm_sq`),
     Gram determinant identity (`gramSchmidt_det_gram`), orthonormal/Euclidean determinant
     invariance (`gramSchmidt_abs_det_orthonormal`, `gramSchmidt_abs_det_euclidean`),
     and lattice covolume invariance (`gramSchmidt_covol_eq_prod`,
     `gramSchmidt_zlattice_covolume_eq_prod`).
   - Span-projection uniqueness characterization (`gramSchmidtVec_unique`) and prefix stability
     (`gramSchmidtVec_prefix_eq`).

2. **Unconditional Lovász LLL-Reduced Basis Existence Theorem**:
   - Definitions `IsSizeReducedVec`, `SatisfiesLovaszVec`, `IsLLLReducedVec`, `IsLLLReduced`,
     and `IsLLLReducedBasis` for any parameter `δ`.
   - Unimodular elementary shearing (`shearBasis`) preserving all Gram–Schmidt vectors and
     full size-reduction (`exists_sizeReduced_same_gsVec`).
   - Adjacent-swap transformation (`swapBasis`) and exact Lovász potential
     `lovaszPotential b = ∏_{k=1}^{n-1} (∏_{j=0}^{k-1} ‖b*_j‖²)`.
   - Uniform Minkowski–Hermite positive lower bound on `lovaszPotential` over ALL `ℤ`-bases
     (`lovaszPotentialMin_pos`, `lovaszPotentialMin_le_lovaszPotential`), strict geometric
     potential drop under a Lovász-violating swap (`lovaszPotential_swap_lt`), and unconditional
     existence of a `δ`-LLL-reduced `ℤ`-basis for ANY discrete lattice `L ⊂ E`
     (`exists_lll_reduced_basis`) and ANY full-rank lattice `Λ ⊂ ℝ^n`
     (`exists_lll_reduced_basis_euclidean`) for all `0 < δ < 1` (in particular `δ = 3/4`).

3. **Unconditional LLL Bounds & Direct `Stage2SiegelReduction.IsSiegelReduced` Discharge**:
   - For any `(δ = 3/4)`-LLL-reduced basis:
     * Telescoping Gram–Schmidt norm inequality (`lll_gsNorm_sq_le`):
       `‖b*_j‖² ≤ 2^{i - j} ‖b*_i‖²` (`j ≤ i`).
     * Basis vector norm bound (`lll_norm_sq_le`): `‖b_i‖² ≤ 2^i ‖b*_i‖²`.
     * Sharp orthogonality-defect / Hadamard product bound (`lll_prod_norm_le_prod_gsNorm`,
       `lll_prod_norm_le_covol`, `lll_prod_norm_le_zlattice_covolume`):
       `∏_i ‖b_i‖ ≤ 2^{n(n-1)/4} * ∏_i ‖b*_i‖ = 2^{n(n-1)/4} * covol(Λ)`.
     * Shortest-vector approximation (`lll_first_vec_le_lambda1`, `lll_first_vec_le_shortestNorm`):
       `‖b_0‖ ≤ 2^{(n-1)/2} * λ₁(Λ)`, plus the LLL Hermite factor bound
       `‖b_0‖ ≤ 2^{(n-1)/4} * covol(Λ)^{1/n}` (`lll_first_vec_le_hermite_covol`).
     * Direct unconditional bridge to `Stage2SiegelReduction.IsSiegelReduced` with sharp constant
       `C_diag = √2, C_unip = 1/2` (`IsLLLReduced.toIsSiegelReduced_sqrt2`) and explicit rational
       constants `C_diag = 2, C_unip = 1/2` (`IsLLLReduced.toIsSiegelReduced`), as well as general
       `1/4 < δ < 1` (`IsLLLReduced.toIsSiegelReduced_general`).
     * Exact average log-norm upper bound (`lll_log_prod_norm_div_rk_le`,
       `lll_log_prod_norm_div_rk_le_neg_slope`):
       `log(∏_j ‖b_j‖) / n ≤ log(covol Λ) / n + ((n - 1) / 4) * log 2`,
       and master unconditional existence theorem (`exists_siegelReduced_lll_basis_for_stage3`)
       directly feeding `Stage3ThetaSiegelFiberWitness.bM_siegel` and `bM_prod_norm_le`.
-/

open Module Submodule Finset Real MeasureTheory
open scoped BigOperators Matrix ENNReal

namespace RHDirect.Stage11LLLSiegelReduction

noncomputable section

/-! ## Section 1: Exact Gram–Schmidt Orthogonalization & Span-Projection Uniqueness -/

section GramSchmidt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gram–Schmidt orthogonalization `v*_i` of any finite family `v : Fin n → E`,
matching `RHDirect.Stage2SiegelReduction.gsVec` definitionally. -/
def gramSchmidtVec {n : ℕ} (v : Fin n → E) (i : Fin n) : E :=
  RHDirect.Stage2SiegelReduction.gsVec v i

/-- Gram–Schmidt orthogonalization `b*_i` of any `ℝ`-basis `b : Basis (Fin n) ℝ E`. -/
def gramSchmidtOrtho {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) : E :=
  gramSchmidtVec (fun k => b k) i

/-- Gram–Schmidt projection coefficient `μ_{i, j}` (`j < i` nontrivial, `μ_{i, i} = 1`,
`μ_{i, j} = 0` for `i < j`) for any finite family `v : Fin n → E`. -/
def gsMu {n : ℕ} (v : Fin n → E) (i j : Fin n) : ℝ :=
  RHDirect.Stage2SiegelReduction.gsCoeff v j i

/-- Gram–Schmidt projection coefficient `μ b i j` (`j < i`) for a basis `b : Basis (Fin n) ℝ E`. -/
def μ {n : ℕ} (b : Basis (Fin n) ℝ E) (i j : Fin n) : ℝ :=
  gsMu (fun k => b k) i j

lemma gsMu_self {n : ℕ} (v : Fin n → E) (i : Fin n) : gsMu v i i = 1 :=
  RHDirect.Stage2SiegelReduction.gsCoeff_self v i

lemma gsMu_of_lt {n : ℕ} (v : Fin n → E) {i j : Fin n} (h : j < i) :
    gsMu v i j = inner ℝ (v i) (gramSchmidtVec v j) / ‖gramSchmidtVec v j‖ ^ 2 := by
  rw [gsMu, RHDirect.Stage2SiegelReduction.gsCoeff_of_lt v h, real_inner_comm]
  rfl

lemma gsMu_of_gt {n : ℕ} (v : Fin n → E) {i j : Fin n} (h : i < j) :
    gsMu v i j = 0 :=
  RHDirect.Stage2SiegelReduction.gsCoeff_of_gt v h

lemma μ_self {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) : μ b i i = 1 :=
  gsMu_self (fun k => b k) i

lemma μ_of_lt {n : ℕ} (b : Basis (Fin n) ℝ E) {i j : Fin n} (h : j < i) :
    μ b i j = inner ℝ (b i) (gramSchmidtOrtho b j) / ‖gramSchmidtOrtho b j‖ ^ 2 :=
  gsMu_of_lt (fun k => b k) h

lemma μ_of_gt {n : ℕ} (b : Basis (Fin n) ℝ E) {i j : Fin n} (h : i < j) :
    μ b i j = 0 :=
  gsMu_of_gt (fun k => b k) h

/-- The `0`-th Gram–Schmidt vector equals the `0`-th input vector: `v*_0 = v_0`. -/
lemma gramSchmidtVec_zero {n : ℕ} (hn : 0 < n) (v : Fin n → E) :
    gramSchmidtVec v ⟨0, hn⟩ = v ⟨0, hn⟩ := by
  unfold gramSchmidtVec
  rw [RHDirect.Stage2SiegelReduction.gsVec]
  simp

/-- The `0`-th Gram–Schmidt vector of a basis `b` equals `b 0`. -/
lemma gramSchmidtOrtho_zero {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ E) :
    gramSchmidtOrtho b ⟨0, hn⟩ = b ⟨0, hn⟩ :=
  gramSchmidtVec_zero hn (fun k => b k)

/-- Exact pairwise orthogonality of Gram–Schmidt vectors for any finite family. -/
theorem gramSchmidtVec_orthogonal {n : ℕ} (v : Fin n → E) {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (gramSchmidtVec v i) (gramSchmidtVec v j) = 0 :=
  RHDirect.Stage2SiegelReduction.gsVec_orthogonal v hij

/-- Exact pairwise orthogonality `⟪b*_i, b*_j⟫ = 0` (`i ≠ j`) for any basis `b`. -/
theorem gramSchmidtOrtho_orthogonal {n : ℕ} (b : Basis (Fin n) ℝ E) {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (gramSchmidtOrtho b i) (gramSchmidtOrtho b j) = 0 :=
  gramSchmidtVec_orthogonal (fun k => b k) hij

/-- Every Gram–Schmidt vector of a basis `b : Basis (Fin n) ℝ E` is nonzero. -/
theorem gramSchmidtOrtho_ne_zero {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    gramSchmidtOrtho b i ≠ 0 :=
  RHDirect.Stage2SiegelReduction.gsVec_ne_zero_of_linearIndependent b.linearIndependent i

/-- Every Gram–Schmidt vector of a basis `b : Basis (Fin n) ℝ E` has strictly positive norm. -/
theorem gramSchmidtOrtho_norm_pos {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    0 < ‖gramSchmidtOrtho b i‖ :=
  norm_pos_iff.mpr (gramSchmidtOrtho_ne_zero b i)

/-- Exact triangular expansion `v_i = v*_i + ∑_{j < i} μ_{i, j} • v*_j`. -/
theorem gramSchmidtVec_triangular {n : ℕ} (v : Fin n → E) (i : Fin n) :
    v i = gramSchmidtVec v i +
      ∑ j : Fin i.1, gsMu v i ⟨j.1, lt_trans j.2 i.2⟩ • gramSchmidtVec v ⟨j.1, lt_trans j.2 i.2⟩ :=
  RHDirect.Stage2SiegelReduction.gs_expansion_lt v i

/-- Exact triangular expansion `b_i = b*_i + ∑_{j < i} μ_{i, j} • b*_j` for any basis `b`. -/
theorem gramSchmidt_triangular {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    b i = gramSchmidtOrtho b i +
      ∑ j : Fin i.1, μ b i ⟨j.1, lt_trans j.2 i.2⟩ • gramSchmidtOrtho b ⟨j.1, lt_trans j.2 i.2⟩ :=
  gramSchmidtVec_triangular (fun k => b k) i

/-- Full-sum triangular expansion `b_i = ∑_j μ_{i, j} • b*_j`. -/
theorem gramSchmidt_expansion_full {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    b i = ∑ j : Fin n, μ b i j • gramSchmidtOrtho b j :=
  RHDirect.Stage2SiegelReduction.gs_expansion (fun k => b k) i

/-- Exact Pythagorean norm formula `‖v_i‖² = ‖v*_i‖² + ∑_{j < i} μ_{i, j}² ‖v*_j‖²`. -/
theorem gramSchmidtVec_norm_sq {n : ℕ} (v : Fin n → E) (i : Fin n) :
    ‖v i‖ ^ 2 = ‖gramSchmidtVec v i‖ ^ 2 +
      ∑ j : Fin i.1, (gsMu v i ⟨j.1, lt_trans j.2 i.2⟩) ^ 2 *
        ‖gramSchmidtVec v ⟨j.1, lt_trans j.2 i.2⟩‖ ^ 2 :=
  RHDirect.Stage2SiegelReduction.norm_sq_eq_sum_gsVec v i

/-- Exact Pythagorean norm formula `‖b_i‖² = ‖b*_i‖² + ∑_{j < i} μ_{i, j}² ‖b*_j‖²`
for any basis `b : Basis (Fin n) ℝ E`. -/
theorem gramSchmidt_norm_sq {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ‖b i‖ ^ 2 = ‖gramSchmidtOrtho b i‖ ^ 2 +
      ∑ j : Fin i.1, (μ b i ⟨j.1, lt_trans j.2 i.2⟩) ^ 2 *
        ‖gramSchmidtOrtho b ⟨j.1, lt_trans j.2 i.2⟩‖ ^ 2 :=
  gramSchmidtVec_norm_sq (fun k => b k) i

/-- Exact Gram determinant invariance: `det(Gram b) = ∏_i ‖b*_i‖²`. -/
theorem gramSchmidt_det_gram {n : ℕ} (b : Basis (Fin n) ℝ E) :
    (Matrix.gram ℝ (fun i => b i)).det = ∏ i : Fin n, ‖gramSchmidtOrtho b i‖ ^ 2 :=
  RHDirect.Stage2SiegelReduction.det_gram_eq_prod_gsVec_norm_sq (fun i => b i)

/-- **Determinant Invariance Relative to Any Orthonormal Basis**:
for any `e : OrthonormalBasis (Fin n) ℝ E` and `b : Basis (Fin n) ℝ E`,
`|e.toBasis.det b| = ∏_i ‖b*_i‖`. -/
theorem gramSchmidt_abs_det_orthonormal {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ E) (b : Basis (Fin n) ℝ E) :
    |e.toBasis.det b| = ∏ i : Fin n, ‖gramSchmidtOrtho b i‖ := by
  let P : Matrix (Fin n) (Fin n) ℝ := e.toBasis.toMatrix b
  have hbP : (fun i => b i) = fun j => ∑ k : Fin n, P k j • e k := by
    funext j
    have h1 := e.toBasis.sum_repr (b j)
    simpa [P, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis] using h1.symm
  have hGramE : Matrix.gram ℝ (fun k : Fin n => e k) = 1 := by
    ext i j
    rw [Matrix.gram_apply, Matrix.one_apply, orthonormal_iff_ite.mp e.orthonormal i j]
  have hdet_sq : P.det ^ 2 = (∏ i : Fin n, ‖gramSchmidtOrtho b i‖) ^ 2 := by
    have h1 : (Matrix.gram ℝ (fun i => b i)).det = P.det ^ 2 := by
      rw [hbP, RHDirect.ArakelovCovolume.gram_sum_smul_eq_transpose_mul (fun k => e k) P,
        hGramE, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose, sq]
    rw [← h1, gramSchmidt_det_gram b, Finset.prod_pow]
  have hsqrt := congrArg Real.sqrt hdet_sq
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg _)] at hsqrt
  simpa [P, Module.Basis.det_apply] using hsqrt

/-- **Determinant Invariance in `ℝ^n` (`EuclideanSpace ℝ (Fin n)`)**:
for any basis `b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))`,
`|det(b_i)_j| = ∏_i ‖b*_i‖`. -/
theorem gramSchmidt_abs_det_euclidean {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    |(Matrix.of (fun i j : Fin n => b i j)).det| = ∏ i : Fin n, ‖gramSchmidtOrtho b i‖ := by
  let e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  have h := gramSchmidt_abs_det_orthonormal e b
  have hdet : e.toBasis.det b = (Matrix.of (fun i j : Fin n => b i j)).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  rwa [hdet] at h

/-- **Lattice Covolume Invariance** in any finite-dimensional real inner product space `E`:
`covol(L) = ∏_i ‖b*_i‖`. -/
theorem gramSchmidt_covol_eq_prod [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) :
    RHDirect.ArakelovCovolume.covol L = ∏ i : Fin r, ‖gramSchmidtVec (fun k => (b k : E)) i‖ :=
  RHDirect.Stage2SiegelReduction.covol_eq_prod_gsVec b

/-- **Full-Rank `ZLattice` Covolume Invariance in `ℝ^n`**:
`ZLattice.covolume Λ volume = ∏_i ‖b*_i‖`. -/
theorem gramSchmidt_zlattice_covolume_eq_prod {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ) :
    ZLattice.covolume Λ volume =
      ∏ i : Fin n, ‖gramSchmidtVec (fun k => (b k : EuclideanSpace ℝ (Fin n))) i‖ := by
  rw [RHDirect.Stage10GeometryOfNumbers.covolume_eq_abs_det Λ b]
  let bR : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := b.ofZLatticeBasis ℝ
  have hbR : ∀ i, bR i = (b i : EuclideanSpace ℝ (Fin n)) := fun i =>
    Basis.ofZLatticeBasis_apply ℝ Λ b i
  have h := gramSchmidt_abs_det_euclidean bR
  have hmat : Matrix.of (fun i j : Fin n => bR i j) =
      Matrix.of (fun i j : Fin n => (b i : EuclideanSpace ℝ (Fin n)) j) := by
    ext i j; simp [hbR]
  rw [hmat] at h
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold gramSchmidtOrtho
  congr 2
  funext k
  exact hbR k

/-! ### Span-Projection Uniqueness & Auxiliary Gram–Schmidt Identities -/

lemma gramSchmidtVec_sub_mem_span_lt {n : ℕ} (v : Fin n → E) (m : Fin n) :
    v m - gramSchmidtVec v m ∈ Submodule.span ℝ {x | ∃ t : Fin n, t < m ∧ v t = x} := by
  have h := RHDirect.Stage2SiegelReduction.gsVec_sub_mem_span_lt v m
  have hneg : -(RHDirect.Stage2SiegelReduction.gsVec v m - v m) = v m - gramSchmidtVec v m := by
    unfold gramSchmidtVec; abel
  rw [← hneg]
  exact Submodule.neg_mem _ h

lemma gramSchmidtVec_mem_span_le {n : ℕ} (v : Fin n → E) (m : Fin n) :
    gramSchmidtVec v m ∈ Submodule.span ℝ {x | ∃ t : Fin n, t ≤ m ∧ v t = x} := by
  have h1 := RHDirect.Stage2SiegelReduction.gsVec_sub_mem_span_lt v m
  have hmono : Submodule.span ℝ {x | ∃ t : Fin n, t < m ∧ v t = x} ≤
      Submodule.span ℝ {x | ∃ t : Fin n, t ≤ m ∧ v t = x} :=
    Submodule.span_mono fun x ⟨t, htm, htx⟩ => ⟨t, le_of_lt htm, htx⟩
  have hvm : v m ∈ Submodule.span ℝ {x | ∃ t : Fin n, t ≤ m ∧ v t = x} :=
    Submodule.subset_span ⟨m, le_rfl, rfl⟩
  have heq : (RHDirect.Stage2SiegelReduction.gsVec v m - v m) + v m = gramSchmidtVec v m := by
    unfold gramSchmidtVec; exact sub_add_cancel _ _
  rw [← heq]
  exact Submodule.add_mem _ (hmono h1) hvm

lemma inner_gramSchmidtVec_vec_eq_zero_of_lt {n : ℕ} (v : Fin n → E) {j k : Fin n} (hjk : j < k) :
    inner ℝ (gramSchmidtVec v k) (v j) = 0 := by
  unfold gramSchmidtVec
  rw [RHDirect.Stage2SiegelReduction.gs_expansion v j, inner_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases htk : t = k
  · subst htk
    rw [RHDirect.Stage2SiegelReduction.gsCoeff_of_gt v hjk, zero_smul, inner_zero_right]
  · rw [real_inner_smul_right, RHDirect.Stage2SiegelReduction.gsVec_orthogonal v (Ne.symm htk),
      mul_zero]

lemma inner_vec_gramSchmidtVec_eq_zero {n : ℕ} (v : Fin n → E) {t m : Fin n} (htm : t < m) :
    inner ℝ (v t) (gramSchmidtVec v m) = 0 := by
  rw [real_inner_comm]
  exact inner_gramSchmidtVec_vec_eq_zero_of_lt v htm

lemma inner_gramSchmidtVec_self_vec {n : ℕ} (v : Fin n → E) (j : Fin n) :
    inner ℝ (gramSchmidtVec v j) (v j) = ‖gramSchmidtVec v j‖ ^ 2 := by
  unfold gramSchmidtVec
  rw [RHDirect.Stage2SiegelReduction.gs_expansion v j, inner_sum, Finset.sum_eq_single j]
  · rw [RHDirect.Stage2SiegelReduction.gsCoeff_self, one_smul, real_inner_self_eq_norm_sq]
  · intro t _ htj
    rw [real_inner_smul_right, RHDirect.Stage2SiegelReduction.gsVec_orthogonal v htj.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Span-Projection Uniqueness of Gram–Schmidt Vectors**:
if `v m - u ∈ span_ℝ {v t | t < m}` and `u ⊥ v t` for all `t < m`, then `u = gramSchmidtVec v m`. -/
theorem gramSchmidtVec_unique {n : ℕ} (v : Fin n → E) (m : Fin n) (u : E)
    (hmem : v m - u ∈ Submodule.span ℝ {x | ∃ t : Fin n, t < m ∧ v t = x})
    (horth : ∀ t : Fin n, t < m → inner ℝ (v t) u = 0) :
    u = gramSchmidtVec v m := by
  let S : Submodule ℝ E := Submodule.span ℝ {x | ∃ t : Fin n, t < m ∧ v t = x}
  have hdiff_mem : gramSchmidtVec v m - u ∈ S := by
    have heq : gramSchmidtVec v m - u = (v m - u) - (v m - gramSchmidtVec v m) := by abel
    rw [heq]
    exact Submodule.sub_mem S hmem (gramSchmidtVec_sub_mem_span_lt v m)
  have hdiff_orth : ∀ w ∈ S, inner ℝ w (gramSchmidtVec v m - u) = 0 := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro x ⟨t, htm, rfl⟩
      rw [inner_sub_right, inner_vec_gramSchmidtVec_eq_zero v htm, horth t htm, sub_self]
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [real_inner_smul_left, hx, mul_zero]
  have h0 : inner ℝ (gramSchmidtVec v m - u) (gramSchmidtVec v m - u) = 0 :=
    hdiff_orth _ hdiff_mem
  have hsub0 : gramSchmidtVec v m - u = 0 := inner_self_eq_zero.mp h0
  exact (sub_eq_zero.mp hsub0).symm

/-- **Prefix Stability of Gram–Schmidt**: restricting `v : Fin n → E` to its first `k ≤ n` vectors
produces the exact same Gram–Schmidt vectors on indices `< k`. -/
theorem gramSchmidtVec_prefix_eq {n k : ℕ} (hk : k ≤ n) (v : Fin n → E) :
    ∀ j : Fin k,
      gramSchmidtVec (fun i : Fin k => v ⟨i.1, lt_of_lt_of_le i.2 hk⟩) j =
        gramSchmidtVec v ⟨j.1, lt_of_lt_of_le j.2 hk⟩ := by
  let w : Fin k → E := fun i => v ⟨i.1, lt_of_lt_of_le i.2 hk⟩
  intro j
  refine (gramSchmidtVec_unique w j (gramSchmidtVec v ⟨j.1, lt_of_lt_of_le j.2 hk⟩) ?_ ?_).symm
  · have hmem := gramSchmidtVec_sub_mem_span_lt v ⟨j.1, lt_of_lt_of_le j.2 hk⟩
    have hset : {x | ∃ t : Fin n, t < ⟨j.1, lt_of_lt_of_le j.2 hk⟩ ∧ v t = x} =
        {x | ∃ t : Fin k, t < j ∧ w t = x} := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t.1, lt_trans ht j.2⟩, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t.1, lt_of_lt_of_le t.2 hk⟩, ht, rfl⟩
    rw [← hset]
    exact hmem
  · intro t ht
    exact inner_vec_gramSchmidtVec_eq_zero v (t := ⟨t.1, lt_of_lt_of_le t.2 hk⟩)
      (m := ⟨j.1, lt_of_lt_of_le j.2 hk⟩) ht

end GramSchmidt

/-! ## Section 2: Unconditional Lovász LLL-Reduced Basis Existence Theorem -/

section LLLDefinitionsAndOperations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Size-reduction condition: `|μ_{i, j}| ≤ 1/2` for all `j < i`. -/
def IsSizeReducedVec {n : ℕ} (v : Fin n → E) : Prop :=
  ∀ i j : Fin n, j < i → |gsMu v i j| ≤ 1 / 2

/-- Lovász condition with parameter `δ`:
`δ ‖v*_k‖² ≤ ‖v*_{k+1}‖² + μ_{k+1, k}² ‖v*_k‖²` for all `k + 1 < n`. -/
def SatisfiesLovaszVec {n : ℕ} (v : Fin n → E) (δ : ℝ) : Prop :=
  ∀ (k : Fin n) (hk : k.1 + 1 < n),
    δ * ‖gramSchmidtVec v k‖ ^ 2 ≤
      ‖gramSchmidtVec v ⟨k.1 + 1, hk⟩‖ ^ 2 +
        (gsMu v ⟨k.1 + 1, hk⟩ k) ^ 2 * ‖gramSchmidtVec v k‖ ^ 2

/-- Equivalent predecessor-indexed form of the Lovász condition:
`δ ‖v*_{k-1}‖² ≤ ‖v*_k‖² + μ_{k, k-1}² ‖v*_{k-1}‖²` for all `0 < k`. -/
theorem satisfiesLovaszVec_iff_pred {n : ℕ} (v : Fin n → E) (δ : ℝ) :
    SatisfiesLovaszVec v δ ↔
      ∀ (k : Fin n) (hk : 0 < k.1),
        δ * ‖gramSchmidtVec v ⟨k.1 - 1, by omega⟩‖ ^ 2 ≤
          ‖gramSchmidtVec v k‖ ^ 2 +
            (gsMu v k ⟨k.1 - 1, by omega⟩) ^ 2 * ‖gramSchmidtVec v ⟨k.1 - 1, by omega⟩‖ ^ 2 := by
  constructor
  · intro h k hk
    have hk' : (⟨k.1 - 1, by omega⟩ : Fin n).1 + 1 < n := by dsimp; omega
    have h1 := h ⟨k.1 - 1, by omega⟩ hk'
    have heq : (⟨(⟨k.1 - 1, by omega⟩ : Fin n).1 + 1, hk'⟩ : Fin n) = k :=
      Fin.ext (by dsimp; omega)
    rwa [heq] at h1
  · intro h k hk
    have hpos : 0 < (⟨k.1 + 1, hk⟩ : Fin n).1 := Nat.succ_pos _
    have h1 := h ⟨k.1 + 1, hk⟩ hpos
    have heq : (⟨(⟨k.1 + 1, hk⟩ : Fin n).1 - 1, by omega⟩ : Fin n) = k :=
      Fin.ext (by simp)
    rwa [heq] at h1

/-- A finite family `v : Fin n → E` is `δ`-LLL-reduced when it is size-reduced and satisfies
the Lovász condition with parameter `δ`. -/
def IsLLLReducedVec {n : ℕ} (v : Fin n → E) (δ : ℝ) : Prop :=
  IsSizeReducedVec v ∧ SatisfiesLovaszVec v δ

/-- A `ℤ`-basis `b : Basis (Fin r) ℤ L` of a lattice `L ⊂ E` is `δ`-LLL-reduced. -/
def IsLLLReduced {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L) (δ : ℝ) : Prop :=
  IsLLLReducedVec (fun i => (b i : E)) δ

/-- An `ℝ`-basis `b : Basis (Fin n) ℝ E` is `δ`-LLL-reduced. -/
def IsLLLReducedBasis {n : ℕ} (b : Basis (Fin n) ℝ E) (δ : ℝ) : Prop :=
  IsLLLReducedVec (fun i => b i) δ

/-- Elementary unimodular shearing of a `ℤ`-basis `b : Basis (Fin r) ℤ L`:
replaces `b i` by `b i - q • b j` (`j ≠ i`) and fixes every other basis vector. -/
def shearBasis {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L)
    (i j : Fin r) (hij : j ≠ i) (q : ℤ) : Basis (Fin r) ℤ L :=
  let φ : L ≃ₗ[ℤ] L :=
    { toFun := fun x => x - (q * b.repr x i) • b j
      invFun := fun x => x + (q * b.repr x i) • b j
      map_add' := fun x y => by
        simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          smul_sub, smul_smul]
        congr 2
        ring
      left_inv := fun x => by
        dsimp only
        have hrepr : b.repr (x - (q * b.repr x i) • b j) i = b.repr x i := by
          simp [hij]
        rw [hrepr, sub_add_cancel]
      right_inv := fun x => by
        dsimp only
        have hrepr : b.repr (x + (q * b.repr x i) • b j) i = b.repr x i := by
          simp [hij]
        rw [hrepr, add_sub_cancel_right] }
  b.map φ

omit [InnerProductSpace ℝ E] in
lemma shearBasis_apply_self {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L)
    (i j : Fin r) (hij : j ≠ i) (q : ℤ) :
    shearBasis b i j hij q i = b i - q • b j := by
  simp [shearBasis]

omit [InnerProductSpace ℝ E] in
lemma shearBasis_apply_ne {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L)
    (i j : Fin r) (hij : j ≠ i) (q : ℤ) {m : Fin r} (hm : m ≠ i) :
    shearBasis b i j hij q m = b m := by
  simp [shearBasis, hm]

/-- Shearing `v i ↦ v i - q • v j` with `j < i` preserves EVERY Gram–Schmidt vector `v*_m`. -/
lemma gramSchmidtVec_shear_eq {n : ℕ} (v : Fin n → E) (i j : Fin n) (hji : j < i) (q : ℝ) :
    let v' : Fin n → E := fun m => if m = i then v i - q • v j else v m
    ∀ m : Fin n, gramSchmidtVec v' m = gramSchmidtVec v m := by
  intro v' m
  have hspan : Submodule.span ℝ {x | ∃ t : Fin n, t < m ∧ v' t = x} =
      Submodule.span ℝ {x | ∃ t : Fin n, t < m ∧ v t = x} := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨t, htm, rfl⟩
      by_cases hti : t = i
      · subst hti
        simp only [v', ↓reduceIte]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨t, htm, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, lt_trans hji htm, rfl⟩))
      · simp only [v', hti, ↓reduceIte]
        exact Submodule.subset_span ⟨t, htm, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨t, htm, rfl⟩
      by_cases hti : t = i
      · subst hti
        have hvi : v t = v' t + q • v' j := by
          have hjne : j ≠ t := ne_of_lt hji
          simp only [v', ↓reduceIte, hjne]
          abel
        rw [hvi]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨t, htm, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, lt_trans hji htm, rfl⟩))
      · have hvt : v t = v' t := by simp [v', hti]
        rw [hvt]
        exact Submodule.subset_span ⟨t, htm, rfl⟩
  refine (gramSchmidtVec_unique v' m (gramSchmidtVec v m) ?_ ?_).symm
  · rw [hspan]
    by_cases hmi : m = i
    · subst hmi
      simp only [v', ↓reduceIte]
      have heq : (v m - q • v j) - gramSchmidtVec v m = (v m - gramSchmidtVec v m) - q • v j := by
        abel
      rw [heq]
      exact Submodule.sub_mem _ (gramSchmidtVec_sub_mem_span_lt v m)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hji, rfl⟩))
    · simp only [v', hmi, ↓reduceIte]
      exact gramSchmidtVec_sub_mem_span_lt v m
  · intro t htm
    by_cases hti : t = i
    · subst hti
      simp only [v', ↓reduceIte]
      rw [inner_sub_left, real_inner_smul_left,
        inner_vec_gramSchmidtVec_eq_zero v htm,
        inner_vec_gramSchmidtVec_eq_zero v (lt_trans hji htm), mul_zero, sub_zero]
    · simp only [v', hti, ↓reduceIte]
      exact inner_vec_gramSchmidtVec_eq_zero v htm

/-- Effect of shearing `b i ↦ b i - q • b j` (`j < i`) on Gram–Schmidt vectors and coefficients:
1. All Gram–Schmidt vectors `b*_m` are unchanged.
2. `μ'_{i, j} = μ_{i, j} - q`.
3. `μ'_{i, k} = μ_{i, k}` for all `j < k < i`.
4. All rows `m ≠ i` are completely unchanged. -/
lemma shearBasis_gs_and_mu [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (i j : Fin r) (hji : j < i) (q : ℤ) :
    let b' := shearBasis b i j (ne_of_lt hji) q
    (∀ m : Fin r, gramSchmidtVec (fun k => (b' k : E)) m = gramSchmidtVec (fun k => (b k : E)) m) ∧
    gsMu (fun k => (b' k : E)) i j = gsMu (fun k => (b k : E)) i j - (q : ℝ) ∧
    (∀ k : Fin r, j < k → k < i →
      gsMu (fun t => (b' t : E)) i k = gsMu (fun t => (b t : E)) i k) := by
  intro b'
  have hv' : (fun m => (b' m : E)) =
      fun m => if m = i then (b i : E) - (q : ℝ) • (b j : E) else (b m : E) := by
    funext m
    by_cases hmi : m = i
    · subst hmi
      simp [b', shearBasis_apply_self, Int.cast_smul_eq_zsmul]
    · simp [b', shearBasis_apply_ne, hmi]
  have hgs : ∀ m : Fin r,
      gramSchmidtVec (fun k => (b' k : E)) m = gramSchmidtVec (fun k => (b k : E)) m := by
    rw [hv']
    exact gramSchmidtVec_shear_eq (fun k => (b k : E)) i j hji (q : ℝ)
  have hne0 : gramSchmidtVec (fun k => (b k : E)) j ≠ 0 :=
    RHDirect.Stage2SiegelReduction.gsVec_ne_zero_of_linearIndependent
      (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b) j
  have hnsq_ne : ‖gramSchmidtVec (fun k => (b k : E)) j‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hne0)
  have hv'_i : (b' i : E) = (b i : E) - (q : ℝ) • (b j : E) := by
    simp [b', shearBasis_apply_self, Int.cast_smul_eq_zsmul]
  refine ⟨hgs, ?_, ?_⟩
  · rw [gsMu_of_lt _ hji, gsMu_of_lt _ hji, hgs j, hv'_i]
    rw [inner_sub_left, real_inner_smul_left,
      real_inner_comm (gramSchmidtVec (fun k => (b k : E)) j) (b j : E),
      inner_gramSchmidtVec_self_vec, sub_div, mul_div_cancel_right₀ _ hnsq_ne]
  · intro k hjk hki
    rw [gsMu_of_lt _ hki, gsMu_of_lt _ hki, hgs k, hv'_i]
    rw [inner_sub_left, real_inner_smul_left,
      inner_vec_gramSchmidtVec_eq_zero (fun t => (b t : E)) hjk, mul_zero, sub_zero]

/-- **Unconditional Full Size-Reduction Preserving All Gram–Schmidt Vectors**:
for any `ℤ`-basis `b` of a discrete lattice `L ⊂ E`, there exists a `ℤ`-basis `b'` of `L` with
the exact same Gram–Schmidt orthogonalization (`b'*_m = b*_m` for all `m`) that is size-reduced
(`|μ'_{i, j}| ≤ 1 / 2` for all `j < i`). -/
theorem exists_sizeReduced_same_gsVec [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] {r : ℕ} (b : Basis (Fin r) ℤ L) :
    ∃ b' : Basis (Fin r) ℤ L,
      (∀ m : Fin r,
        gramSchmidtVec (fun k => (b' k : E)) m = gramSchmidtVec (fun k => (b k : E)) m) ∧
      IsSizeReducedVec (fun k => (b' k : E)) := by
  -- Step 1: Size-reduce a single row `i` without changing any other row or any `b*_m`.
  have hrow : ∀ (i : Fin r) (b₀ : Basis (Fin r) ℤ L) (s : ℕ), s ≤ i.1 →
      ∃ b₁ : Basis (Fin r) ℤ L,
        (∀ m : Fin r,
          gramSchmidtVec (fun k => (b₁ k : E)) m = gramSchmidtVec (fun k => (b₀ k : E)) m) ∧
        (∀ m : Fin r, m ≠ i → b₁ m = b₀ m) ∧
        (∀ j : Fin r, i.1 - s ≤ j.1 → j < i → |gsMu (fun k => (b₁ k : E)) i j| ≤ 1 / 2) := by
    intro i b₀ s
    induction s with
    | zero =>
      intro _
      exact ⟨b₀, fun _ => rfl, fun _ _ => rfl, fun j h1 h2 => by
        have : j.1 < i.1 := h2
        omega⟩
    | succ s ih =>
      intro hs
      obtain ⟨b₁, hgs1, hfix1, hred1⟩ := ih (Nat.le_of_succ_le hs)
      let j₀ : Fin r := ⟨i.1 - (s + 1), by omega⟩
      have hj₀_lt : j₀ < i := by show i.1 - (s + 1) < i.1; omega
      let q : ℤ := round (gsMu (fun k => (b₁ k : E)) i j₀)
      let b₂ : Basis (Fin r) ℤ L := shearBasis b₁ i j₀ (ne_of_lt hj₀_lt) q
      obtain ⟨hgs2, hmu_j₀, hmu_gt⟩ := shearBasis_gs_and_mu b₁ i j₀ hj₀_lt q
      refine ⟨b₂, fun m => (hgs2 m).trans (hgs1 m), fun m hm => ?_, fun j hj_ge hj_lt => ?_⟩
      · exact (shearBasis_apply_ne b₁ i j₀ (ne_of_lt hj₀_lt) q hm).trans (hfix1 m hm)
      · by_cases hjeq : j = j₀
        · subst hjeq
          rw [hmu_j₀]
          exact abs_sub_round _
        · have hj₀_lt_j : j₀ < j := by
            show j₀.1 < j.1
            have : j.1 ≠ j₀.1 := fun h => hjeq (Fin.ext h)
            dsimp [j₀] at this ⊢
            omega
          have hj_ge_s : i.1 - s ≤ j.1 := by
            have hj₀_val : j₀.1 = i.1 - (s + 1) := rfl
            have hj_gt : j₀.1 < j.1 := hj₀_lt_j
            omega
          rw [hmu_gt j hj₀_lt_j hj_lt]
          exact hred1 j hj_ge_s hj_lt
  -- Step 2: Outer induction over rows `0, ..., t - 1`.
  have houter : ∀ t : ℕ, t ≤ r →
      ∃ b' : Basis (Fin r) ℤ L,
        (∀ m : Fin r,
          gramSchmidtVec (fun k => (b' k : E)) m = gramSchmidtVec (fun k => (b k : E)) m) ∧
        (∀ i j : Fin r, i.1 < t → j < i → |gsMu (fun k => (b' k : E)) i j| ≤ 1 / 2) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨b, fun _ => rfl, fun i _ hi => by omega⟩
    | succ t ih =>
      intro ht
      obtain ⟨b₁, hgs1, hred1⟩ := ih (Nat.le_of_succ_le ht)
      let i₀ : Fin r := ⟨t, ht⟩
      obtain ⟨b₂, hgs2, hfix2, hrow2⟩ := hrow i₀ b₁ t (le_refl t)
      refine ⟨b₂, fun m => (hgs2 m).trans (hgs1 m), fun i j hit hji => ?_⟩
      by_cases hi : i.1 < t
      · have hine : i ≠ i₀ := fun h => by
          have : i.1 = t := congrArg Fin.val h
          omega
        have hmu_eq : gsMu (fun k => (b₂ k : E)) i j = gsMu (fun k => (b₁ k : E)) i j := by
          rw [gsMu_of_lt _ hji, gsMu_of_lt _ hji, hfix2 i hine, hgs2 j]
        rw [hmu_eq]
        exact hred1 i j hi hji
      · have hieq : i = i₀ := Fin.ext (by dsimp [i₀]; omega)
        subst hieq
        exact hrow2 j (by simp [i₀]) hji
  obtain ⟨b', hgs, hred⟩ := houter r le_rfl
  exact ⟨b', hgs, fun i j hji => hred i j i.2 hji⟩

/-! ### Adjacent Swap, Lovász Potential & Unconditional LLL Existence -/

/-- Prefix Gram determinant `d_k(v) = ∏_{j < k} ‖v*_j‖²`. -/
def prefixGramDet {n : ℕ} (v : Fin n → E) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.1 < k), ‖gramSchmidtVec v j‖ ^ 2

/-- **Lovász Potential**: `D(v) = ∏_{k = 1}^{n - 1} d_k(v) = ∏_{k=1}^{n-1} (∏_{j=0}^{k-1} ‖v*_j‖²)`. -/
def lovaszPotential {n : ℕ} (v : Fin n → E) : ℝ :=
  ∏ k ∈ Finset.Ico 1 n, prefixGramDet v k

lemma prefixGramDet_pos [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (k : ℕ) :
    0 < prefixGramDet (fun i => (b i : E)) k := by
  refine Finset.prod_pos fun j _ => sq_pos_of_pos (norm_pos_iff.mpr ?_)
  exact RHDirect.Stage2SiegelReduction.gsVec_ne_zero_of_linearIndependent
    (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b) j

lemma lovaszPotential_pos [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) :
    0 < lovaszPotential (fun i => (b i : E)) :=
  Finset.prod_pos fun k _ => prefixGramDet_pos b k

lemma lovaszPotential_congr {n : ℕ} {v w : Fin n → E}
    (h : ∀ m : Fin n, gramSchmidtVec v m = gramSchmidtVec w m) :
    lovaszPotential v = lovaszPotential w := by
  unfold lovaszPotential prefixGramDet
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun j _ => ?_
  rw [h j]

/-- Exact transformation of Gram–Schmidt vectors under swapping adjacent basis vectors `b_k`
and `b_{k+1}` (`b' = b.reindex (Equiv.swap k k1)`):
1. `b'*_m = b*_m` for all `m ≠ k, k+1`.
2. `b'*_k = b*_{k+1} + μ_{k+1, k} • b*_k`, hence `‖b'*_k‖² = ‖b*_{k+1}‖² + μ_{k+1, k}² ‖b*_k‖²`.
3. `‖b'*_k‖² * ‖b'*_{k+1}‖² = ‖b*_k‖² * ‖b*_{k+1}‖²`. -/
lemma swap_gsVec_properties [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (k : Fin r) (hk : k.1 + 1 < r) :
    let k1 : Fin r := ⟨k.1 + 1, hk⟩
    let b' : Basis (Fin r) ℤ L := b.reindex (Equiv.swap k k1)
    let v : Fin r → E := fun m => (b m : E)
    let v' : Fin r → E := fun m => (b' m : E)
    (∀ m : Fin r, m ≠ k → m ≠ k1 → gramSchmidtVec v' m = gramSchmidtVec v m) ∧
    ‖gramSchmidtVec v' k‖ ^ 2 =
      ‖gramSchmidtVec v k1‖ ^ 2 + (gsMu v k1 k) ^ 2 * ‖gramSchmidtVec v k‖ ^ 2 ∧
    ‖gramSchmidtVec v' k‖ ^ 2 * ‖gramSchmidtVec v' k1‖ ^ 2 =
      ‖gramSchmidtVec v k‖ ^ 2 * ‖gramSchmidtVec v k1‖ ^ 2 := by
  intro k1 b' v v'
  have hkk1 : k ≠ k1 := fun h => by
    have : k.1 = k.1 + 1 := congrArg Fin.val h
    omega
  have hv'_apply : ∀ m : Fin r, v' m = v (Equiv.swap k k1 m) := fun m => by
    simp [v', v, b', Equiv.symm_swap]
  have hv'_k : v' k = v k1 := by rw [hv'_apply, Equiv.swap_apply_left]
  have hv'_k1 : v' k1 = v k := by rw [hv'_apply, Equiv.swap_apply_right]
  have hv'_other : ∀ m : Fin r, m ≠ k → m ≠ k1 → v' m = v m := fun m h1 h2 => by
    rw [hv'_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hspan_le_k : ∀ m : Fin r, m ≤ k →
      Submodule.span ℝ {x | ∃ t : Fin r, t < m ∧ v' t = x} =
      Submodule.span ℝ {x | ∃ t : Fin r, t < m ∧ v t = x} := by
    intro m hm
    congr 1; ext x
    refine exists_congr fun t => and_congr_right fun htm => ?_
    have htk : t ≠ k := ne_of_lt (lt_of_lt_of_le htm hm)
    have htk1 : t ≠ k1 := fun h => by
      have : t.1 = k.1 + 1 := congrArg Fin.val h
      have : t.1 < m.1 := htm
      have : m.1 ≤ k.1 := hm
      omega
    rw [hv'_other t htk htk1]
  have hspan_gt_k1 : ∀ m : Fin r, k1 < m →
      Submodule.span ℝ {x | ∃ t : Fin r, t < m ∧ v' t = x} =
      Submodule.span ℝ {x | ∃ t : Fin r, t < m ∧ v t = x} := by
    intro m hm
    congr 1; ext x
    constructor
    · rintro ⟨t, htm, rfl⟩
      refine ⟨Equiv.swap k k1 t, ?_, (hv'_apply t).symm⟩
      by_cases h1 : t = k
      · subst h1; rwa [Equiv.swap_apply_left]
      · by_cases h2 : t = k1
        · subst h2
          rw [Equiv.swap_apply_right]
          exact lt_trans (show k < k1 from Nat.lt_succ_self k.1) hm
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rintro ⟨t, htm, rfl⟩
      refine ⟨Equiv.swap k k1 t, ?_, ?_⟩
      · by_cases h1 : t = k
        · subst h1; rwa [Equiv.swap_apply_left]
        · by_cases h2 : t = k1
          · subst h2
            rw [Equiv.swap_apply_right]
            exact lt_trans (show k < k1 from Nat.lt_succ_self k.1) hm
          · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
      · rw [hv'_apply, Equiv.swap_apply_self]
  have hother : ∀ m : Fin r, m ≠ k → m ≠ k1 → gramSchmidtVec v' m = gramSchmidtVec v m := by
    intro m hmk hmk1
    have hcases : m < k ∨ k1 < m := by
      have h1 : m.1 ≠ k.1 := fun h => hmk (Fin.ext h)
      have h2 : m.1 ≠ k.1 + 1 := fun h => hmk1 (Fin.ext h)
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · exact Or.inl hlt
      · exact Or.inr (show k.1 + 1 < m.1 by omega)
    rcases hcases with hlt | hgt
    · refine (gramSchmidtVec_unique v' m (gramSchmidtVec v m) ?_ ?_).symm
      · rw [hspan_le_k m (le_of_lt hlt), hv'_other m hmk hmk1]
        exact gramSchmidtVec_sub_mem_span_lt v m
      · intro t htm
        have htk : t ≠ k := ne_of_lt (lt_trans htm hlt)
        have htk1 : t ≠ k1 := fun h => by
          have : t.1 = k.1 + 1 := congrArg Fin.val h
          have : t.1 < m.1 := htm
          have : m.1 < k.1 := hlt
          omega
        rw [hv'_other t htk htk1]
        exact inner_vec_gramSchmidtVec_eq_zero v htm
    · refine (gramSchmidtVec_unique v' m (gramSchmidtVec v m) ?_ ?_).symm
      · rw [hspan_gt_k1 m hgt, hv'_other m hmk hmk1]
        exact gramSchmidtVec_sub_mem_span_lt v m
      · intro t htm
        rw [hv'_apply t]
        have hswap_lt : Equiv.swap k k1 t < m := by
          by_cases h1 : t = k
          · subst h1; rwa [Equiv.swap_apply_left]
          · by_cases h2 : t = k1
            · subst h2
              rw [Equiv.swap_apply_right]
              exact lt_trans (show k < k1 from Nat.lt_succ_self k.1) hgt
            · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact inner_vec_gramSchmidtVec_eq_zero v hswap_lt
  have hvk_eq : gramSchmidtVec v' k =
      gramSchmidtVec v k1 + gsMu v k1 k • gramSchmidtVec v k := by
    let u : E := gramSchmidtVec v k1 + gsMu v k1 k • gramSchmidtVec v k
    refine (gramSchmidtVec_unique v' k u ?_ ?_).symm
    · rw [hspan_le_k k le_rfl, hv'_k]
      have hexp := gramSchmidtVec_triangular v k1
      have hsplit : ∑ j : Fin k1.1,
          gsMu v k1 ⟨j.1, lt_trans j.2 k1.2⟩ • gramSchmidtVec v ⟨j.1, lt_trans j.2 k1.2⟩ =
          (∑ j : Fin k.1,
            gsMu v k1 ⟨j.1, lt_trans j.2 k.2⟩ • gramSchmidtVec v ⟨j.1, lt_trans j.2 k.2⟩) +
          gsMu v k1 k • gramSchmidtVec v k := by
        change ∑ j : Fin (k.1 + 1), _ = _
        rw [Fin.sum_univ_castSucc]
        rfl
      have hdiff : v k1 - u = ∑ j : Fin k.1,
          gsMu v k1 ⟨j.1, lt_trans j.2 k.2⟩ • gramSchmidtVec v ⟨j.1, lt_trans j.2 k.2⟩ := by
        dsimp [u]
        rw [hexp, hsplit]
        abel
      rw [hdiff]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      have hmem_le := gramSchmidtVec_mem_span_le v ⟨j.1, lt_trans j.2 k.2⟩
      have hmono : Submodule.span ℝ {x | ∃ t : Fin r, t ≤ ⟨j.1, lt_trans j.2 k.2⟩ ∧ v t = x} ≤
          Submodule.span ℝ {x | ∃ t : Fin r, t < k ∧ v t = x} :=
        Submodule.span_mono fun x ⟨t, htj, htx⟩ => ⟨t, lt_of_le_of_lt htj j.2, htx⟩
      exact hmono hmem_le
    · intro t htk
      have htk_ne : t ≠ k := ne_of_lt htk
      have htk1_ne : t ≠ k1 := fun h => by
        have : t.1 = k.1 + 1 := congrArg Fin.val h
        have : t.1 < k.1 := htk
        omega
      rw [hv'_other t htk_ne htk1_ne]
      dsimp [u]
      rw [inner_add_right, real_inner_smul_right,
        inner_vec_gramSchmidtVec_eq_zero v (lt_trans htk (show k < k1 from Nat.lt_succ_self k.1)),
        inner_vec_gramSchmidtVec_eq_zero v htk, mul_zero, add_zero]
  have hvk_norm_sq : ‖gramSchmidtVec v' k‖ ^ 2 =
      ‖gramSchmidtVec v k1‖ ^ 2 + (gsMu v k1 k) ^ 2 * ‖gramSchmidtVec v k‖ ^ 2 := by
    rw [hvk_eq, norm_add_sq_real, real_inner_smul_right,
      gramSchmidtVec_orthogonal v hkk1.symm, mul_zero, mul_zero, add_zero,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hprod_eq : ‖gramSchmidtVec v' k‖ ^ 2 * ‖gramSchmidtVec v' k1‖ ^ 2 =
      ‖gramSchmidtVec v k‖ ^ 2 * ‖gramSchmidtVec v k1‖ ^ 2 := by
    have hcov_v : RHDirect.ArakelovCovolume.covol L = ∏ m : Fin r, ‖gramSchmidtVec v m‖ :=
      gramSchmidt_covol_eq_prod b
    have hcov_v' : RHDirect.ArakelovCovolume.covol L = ∏ m : Fin r, ‖gramSchmidtVec v' m‖ :=
      gramSchmidt_covol_eq_prod b'
    have htot : ∏ m : Fin r, ‖gramSchmidtVec v' m‖ ^ 2 = ∏ m : Fin r, ‖gramSchmidtVec v m‖ ^ 2 := by
      rw [Finset.prod_pow, Finset.prod_pow, ← hcov_v', ← hcov_v]
    let rest : Finset (Fin r) := (Finset.univ.erase k).erase k1
    have hk1_mem : k1 ∈ Finset.univ.erase k :=
      Finset.mem_erase.mpr ⟨hkk1.symm, Finset.mem_univ k1⟩
    have hsplit_v : ∏ m : Fin r, ‖gramSchmidtVec v m‖ ^ 2 =
        ‖gramSchmidtVec v k‖ ^ 2 * ‖gramSchmidtVec v k1‖ ^ 2 *
          ∏ m ∈ rest, ‖gramSchmidtVec v m‖ ^ 2 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase (Finset.univ.erase k) _ hk1_mem, mul_assoc]
    have hsplit_v' : ∏ m : Fin r, ‖gramSchmidtVec v' m‖ ^ 2 =
        ‖gramSchmidtVec v' k‖ ^ 2 * ‖gramSchmidtVec v' k1‖ ^ 2 *
          ∏ m ∈ rest, ‖gramSchmidtVec v' m‖ ^ 2 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase (Finset.univ.erase k) _ hk1_mem, mul_assoc]
    have hrest_eq : ∏ m ∈ rest, ‖gramSchmidtVec v' m‖ ^ 2 =
        ∏ m ∈ rest, ‖gramSchmidtVec v m‖ ^ 2 := by
      refine Finset.prod_congr rfl fun m hm => ?_
      have hm1 : m ≠ k1 := (Finset.mem_erase.mp hm).1
      have hm2 : m ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      rw [hother m hm2 hm1]
    have hrest_pos : 0 < ∏ m ∈ rest, ‖gramSchmidtVec v m‖ ^ 2 :=
      Finset.prod_pos fun m _ => sq_pos_of_pos (norm_pos_iff.mpr
        (RHDirect.Stage2SiegelReduction.gsVec_ne_zero_of_linearIndependent
          (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b) m))
    rw [hsplit_v', hsplit_v, hrest_eq] at htot
    exact mul_right_cancel₀ hrest_pos.ne' htot
  exact ⟨hother, hvk_norm_sq, hprod_eq⟩

/-- **Strict Potential Drop Under a Lovász-Violating Swap**:
if `‖b*_{k+1}‖² + μ_{k+1,k}² ‖b*_k‖² < δ ‖b*_k‖²`, then swapping `b_k` and `b_{k+1}` strictly
reduces the Lovász potential by a factor `< δ`: `D(b') < δ * D(b)`. -/
theorem lovaszPotential_swap_lt [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (k : Fin r) (hk : k.1 + 1 < r) {δ : ℝ}
    (hfail : ‖gramSchmidtVec (fun i => (b i : E)) ⟨k.1 + 1, hk⟩‖ ^ 2 +
        (gsMu (fun i => (b i : E)) ⟨k.1 + 1, hk⟩ k) ^ 2 *
          ‖gramSchmidtVec (fun i => (b i : E)) k‖ ^ 2 <
        δ * ‖gramSchmidtVec (fun i => (b i : E)) k‖ ^ 2) :
    let k1 : Fin r := ⟨k.1 + 1, hk⟩
    lovaszPotential (fun i => (b.reindex (Equiv.swap k k1) i : E)) <
      δ * lovaszPotential (fun i => (b i : E)) := by
  intro k1
  let b' : Basis (Fin r) ℤ L := b.reindex (Equiv.swap k k1)
  let v : Fin r → E := fun i => (b i : E)
  let v' : Fin r → E := fun i => (b' i : E)
  obtain ⟨hother, hvk_sq, hpair_sq⟩ := swap_gsVec_properties b k hk
  have hkk1 : k ≠ k1 := fun h => by
    have : k.1 = k.1 + 1 := congrArg Fin.val h
    omega
  -- Check each factor `prefixGramDet v' m` for `m ∈ Finset.Ico 1 r`.
  have hprefix_other : ∀ m ∈ (Finset.Ico 1 r).erase (k.1 + 1),
      prefixGramDet v' m = prefixGramDet v m := by
    intro m hm
    have hm_ne : m ≠ k.1 + 1 := (Finset.mem_erase.mp hm).1
    unfold prefixGramDet
    rcases lt_or_gt_of_ne hm_ne with hlt | hgt
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hjlt : j.1 < m := (Finset.mem_filter.mp hj).2
      have hjk : j ≠ k := fun h => by have := congrArg Fin.val h; omega
      have hjk1 : j ≠ k1 := fun h => by have := congrArg Fin.val h; dsimp [k1] at this; omega
      rw [hother j hjk hjk1]
    · let S : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => j.1 < m)
      have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, by omega⟩
      have hk1S : k1 ∈ S.erase k :=
        Finset.mem_erase.mpr ⟨hkk1.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ k1, hgt⟩⟩
      rw [← Finset.mul_prod_erase S _ hkS, ← Finset.mul_prod_erase (S.erase k) _ hk1S,
        ← Finset.mul_prod_erase S _ hkS, ← Finset.mul_prod_erase (S.erase k) _ hk1S,
        ← mul_assoc, ← mul_assoc, hpair_sq]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have h1 : j ≠ k1 := (Finset.mem_erase.mp hj).1
      have h2 : j ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      rw [hother j h2 h1]
  have hprefix_k1 : prefixGramDet v' (k.1 + 1) < δ * prefixGramDet v (k.1 + 1) := by
    unfold prefixGramDet
    let Sk : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => j.1 < k.1)
    let Sk1 : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => j.1 < k.1 + 1)
    have hSk1_eq : Sk1 = insert k Sk := by
      ext j
      simp only [Sk1, Sk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hjk : j.1 = k.1
        · exact Or.inl (Fin.ext hjk)
        · exact Or.inr (by omega)
      · rintro (rfl | h) <;> omega
    have hk_not : k ∉ Sk := by simp [Sk]
    have hSk_eq : ∏ j ∈ Sk, ‖gramSchmidtVec v' j‖ ^ 2 = ∏ j ∈ Sk, ‖gramSchmidtVec v j‖ ^ 2 := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjlt : j.1 < k.1 := (Finset.mem_filter.mp hj).2
      have hjk : j ≠ k := fun h => by have := congrArg Fin.val h; omega
      have hjk1 : j ≠ k1 := fun h => by have := congrArg Fin.val h; dsimp [k1] at this; omega
      rw [hother j hjk hjk1]
    have hSk_pos : 0 < ∏ j ∈ Sk, ‖gramSchmidtVec v j‖ ^ 2 := prefixGramDet_pos b k.1
    change ∏ j ∈ Sk1, ‖gramSchmidtVec v' j‖ ^ 2 < δ * ∏ j ∈ Sk1, ‖gramSchmidtVec v j‖ ^ 2
    rw [hSk1_eq, Finset.prod_insert hk_not, Finset.prod_insert hk_not, hSk_eq, ← mul_assoc]
    have hlt_k : ‖gramSchmidtVec v' k‖ ^ 2 < δ * ‖gramSchmidtVec v k‖ ^ 2 := by
      rw [hvk_sq]; exact hfail
    exact mul_lt_mul_of_pos_right hlt_k hSk_pos
  have hk1_mem : k.1 + 1 ∈ Finset.Ico 1 r := Finset.mem_Ico.mpr ⟨Nat.succ_pos _, hk⟩
  unfold lovaszPotential
  rw [← Finset.mul_prod_erase (Finset.Ico 1 r) _ hk1_mem,
    ← Finset.mul_prod_erase (Finset.Ico 1 r) _ hk1_mem,
    Finset.prod_congr rfl hprefix_other, ← mul_assoc]
  have hrest_pos : 0 < ∏ m ∈ (Finset.Ico 1 r).erase (k.1 + 1), prefixGramDet v m :=
    Finset.prod_pos fun m _ => prefixGramDet_pos b m
  exact mul_lt_mul_of_pos_right hprefix_k1 hrest_pos

/-- Uniform positive Minkowski–Hermite lower bound on the Lovász potential over ALL `ℤ`-bases
of a discrete lattice `L ⊂ E`:
`D_min(L) = ∏_{k = 1}^{rk L - 1} (λ₁(L)² / k)^k`. -/
def lovaszPotentialMin [FiniteDimensional ℝ E] (L : Submodule ℤ E) : ℝ :=
  ∏ k ∈ Finset.Ico 1 (RHDirect.ArakelovCovolume.rk L),
    ((RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 / (k : ℝ)) ^ k

lemma lovaszPotentialMin_pos [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (hL0 : L ≠ ⊥) :
    0 < lovaszPotentialMin L := by
  have hlam : 0 < RHDirect.Stage2SiegelReduction.lambda1 L :=
    RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
  refine Finset.prod_pos fun k hk => pow_pos (div_pos (sq_pos_of_pos hlam) ?_) k
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  exact_mod_cast (by omega : 0 < k)

/-- **Uniform Minkowski–Hermite Lower Bound on the Lovász Potential**:
for EVERY `ℤ`-basis `b : Basis (Fin (rk L)) ℤ L` of a nonzero discrete lattice `L ⊂ E`,
`0 < lovaszPotentialMin L ≤ lovaszPotential b`. -/
theorem lovaszPotentialMin_le_lovaszPotential [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L) :
    lovaszPotentialMin L ≤ lovaszPotential (fun i => (b i : E)) := by
  let r := RHDirect.ArakelovCovolume.rk L
  have hlam_pos : 0 < RHDirect.Stage2SiegelReduction.lambda1 L :=
    RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
  unfold lovaszPotentialMin lovaszPotential
  refine Finset.prod_le_prod (fun k hk => ?_) (fun k hk => ?_)
  · have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    exact pow_nonneg (div_nonneg (sq_nonneg _) hkpos.le) k
  · have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkr : k < r := (Finset.mem_Ico.mp hk).2
    have hkle : k ≤ r := le_of_lt hkr
    -- Build the rank-`k` prefix sublattice `N_k = span_ℤ {b_0, ..., b_{k-1}} ≤ L`.
    let w : Fin k → E := fun j => (b ⟨j.1, lt_of_lt_of_le j.2 hkle⟩ : E)
    let N : Submodule ℤ E := Submodule.span ℤ (Set.range w)
    have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact (b _).2)
    have : DiscreteTopology N := RHDirect.ArakelovCovolume.discreteTopology_of_le hNL
    have hwliR : LinearIndependent ℝ w :=
      (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).comp
        (fun j : Fin k => (⟨j.1, lt_of_lt_of_le j.2 hkle⟩ : Fin r))
        (fun a c hac => Fin.ext (Fin.mk.inj hac))
    have hwliZ : LinearIndependent ℤ (fun j : Fin k =>
        (⟨w j, Submodule.subset_span ⟨j, rfl⟩⟩ : N)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      have h1 : ∑ t : Fin k, ((g t : ℤ) : ℝ) • w t = 0 := by
        have := congrArg Subtype.val hg
        simpa [Submodule.coe_sum, Int.cast_smul_eq_zsmul] using this
      exact_mod_cast Fintype.linearIndependent_iff.mp hwliR (fun t => (g t : ℝ)) h1 j
    have hspN : ⊤ ≤ Submodule.span ℤ (Set.range fun j : Fin k =>
        (⟨w j, Submodule.subset_span ⟨j, rfl⟩⟩ : N)) := by
      intro y _
      have hy : (y : E) ∈ Submodule.span ℤ (Set.range w) := y.2
      rw [Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      have hyeq : y = ∑ j : Fin k, c j • (⟨w j, Submodule.subset_span ⟨j, rfl⟩⟩ : N) :=
        Subtype.ext (by simpa [Submodule.coe_sum] using hc.symm)
      rw [hyeq]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    let bN : Basis (Fin k) ℤ N := Basis.mk hwliZ hspN
    have hrkN : RHDirect.ArakelovCovolume.rk N = k := by
      show Module.finrank ℤ N = k
      rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
    have hN0 : N ≠ ⊥ := by
      intro hbot
      have h0 : w ⟨0, hk1⟩ ∈ N := Submodule.subset_span ⟨⟨0, hk1⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at h0
      exact hwliR.ne_zero ⟨0, hk1⟩ h0
    -- Identify `prefixGramDet b k = (covol N)^2`.
    have hcovN_sq : prefixGramDet (fun i => (b i : E)) k =
        (RHDirect.ArakelovCovolume.covol N) ^ 2 := by
      rw [gramSchmidt_covol_eq_prod bN, ← Finset.prod_pow]
      have hbN_coe : (fun j : Fin k => (bN j : E)) = w := by
        funext j; simp [bN]
      rw [hbN_coe]
      unfold prefixGramDet
      refine Finset.prod_bij (fun j hj => ⟨j.1, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ c _ h; exact Fin.ext (Fin.mk.inj h)
      · intro j _
        exact ⟨⟨j.1, lt_of_lt_of_le j.2 hkle⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩, by ext; rfl⟩
      · intro j hj
        have hpre := gramSchmidtVec_prefix_eq hkle (fun i => (b i : E))
          ⟨j.1, (Finset.mem_filter.mp hj).2⟩
        have hjeq : (⟨j.1, lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hkle⟩ : Fin r) = j :=
          Fin.ext rfl
        rw [hjeq] at hpre
        rw [hpre]
    -- Apply Minkowski–Hermite to `N`: `λ₁(L) ≤ λ₁(N) ≤ √k · covol(N)^(1/k)`.
    have hlam_le : RHDirect.Stage2SiegelReduction.lambda1 L ≤
        RHDirect.Stage2SiegelReduction.lambda1 N := by
      obtain ⟨v₀, hv₀N, hv₀0, hv₀eq⟩ :=
        RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 N hN0
      rw [← hv₀eq]
      exact RHDirect.Stage2SiegelReduction.lambda1_le_norm L (hNL hv₀N) hv₀0
    have hherm := RHDirect.Stage2SiegelReduction.lambda1_le_hermite N hN0
    rw [hrkN] at hherm
    have hbound := hlam_le.trans hherm
    have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol N :=
      RHDirect.ArakelovCovolume.covol_pos N
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hsq : (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 ≤
        (k : ℝ) * ((RHDirect.ArakelovCovolume.covol N) ^ (1 / (k : ℝ))) ^ 2 := by
      have h1 := pow_le_pow_left₀ hlam_pos.le hbound 2
      rwa [mul_pow, Real.sq_sqrt hkpos.le] at h1
    have hdiv : (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 / (k : ℝ) ≤
        ((RHDirect.ArakelovCovolume.covol N) ^ (1 / (k : ℝ))) ^ 2 :=
      (div_le_iff₀ hkpos).mpr (by linarith)
    have hpow := pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hkpos.le) hdiv k
    have hrhs : (((RHDirect.ArakelovCovolume.covol N) ^ (1 / (k : ℝ))) ^ 2) ^ k =
        (RHDirect.ArakelovCovolume.covol N) ^ 2 := by
      have hinner : ((RHDirect.ArakelovCovolume.covol N) ^ (1 / (k : ℝ))) ^ k =
          RHDirect.ArakelovCovolume.covol N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcov_pos.le, one_div_mul_cancel hkpos.ne',
          Real.rpow_one]
      rw [← pow_mul, mul_comm 2 k, pow_mul, hinner]
    rw [hrhs] at hpow
    rwa [hcovN_sq]

/-- **Unconditional Lovász LLL-Reduced Basis Existence Theorem** (General Inner Product Space):
for ANY discrete `ℤ`-lattice `L` in ANY finite-dimensional real inner product space `E`, and ANY
Lovász parameter `δ` with `0 < δ < 1` (in particular `δ = 3 / 4`), there unconditionally exists
a `δ`-LLL-reduced `ℤ`-basis `b : Basis (Fin (rk L)) ℤ L`. -/
theorem exists_lll_reduced_basis [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L, IsLLLReduced b δ := by
  by_cases hL0 : L = ⊥
  · subst hL0
    let b0 : Basis (Fin (RHDirect.ArakelovCovolume.rk (⊥ : Submodule ℤ E))) ℤ
        (⊥ : Submodule ℤ E) := Module.finBasis ℤ (⊥ : Submodule ℤ E)
    have hrk0 : RHDirect.ArakelovCovolume.rk (⊥ : Submodule ℤ E) = 0 := by
      simp [RHDirect.ArakelovCovolume.rk]
    refine ⟨b0, ?_, ?_⟩
    · intro i; exact absurd i.2 (by omega)
    · intro k; exact absurd k.2 (by omega)
  · by_contra hnone
    push Not at hnone
    -- Every basis can be size-reduced (same potential) and then swapped (strict drop `< δ`).
    have hstep : ∀ b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L,
        ∃ b' : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L,
          lovaszPotential (fun i => (b' i : E)) < δ * lovaszPotential (fun i => (b i : E)) := by
      intro b
      obtain ⟨b₁, hgs1, hsr1⟩ := exists_sizeReduced_same_gsVec b
      have hnot_lll : ¬ IsLLLReduced b₁ δ := hnone b₁
      have hnot_lov : ¬ SatisfiesLovaszVec (fun i => (b₁ i : E)) δ := fun hlov =>
        hnot_lll ⟨hsr1, hlov⟩
      unfold SatisfiesLovaszVec at hnot_lov
      push Not at hnot_lov
      obtain ⟨k, hk, hfail⟩ := hnot_lov
      let k1 : Fin (RHDirect.ArakelovCovolume.rk L) := ⟨k.1 + 1, hk⟩
      refine ⟨b₁.reindex (Equiv.swap k k1), ?_⟩
      have hdrop := lovaszPotential_swap_lt b₁ k hk hfail
      rwa [lovaszPotential_congr hgs1] at hdrop
    -- Iterate `N` steps from `b₀ = Module.finBasis ℤ L`: `D(b_N) ≤ δ^N * D(b₀)`.
    let b₀ : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L := Module.finBasis ℤ L
    have hiter : ∀ N : ℕ, ∃ bN : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L,
        lovaszPotential (fun i => (bN i : E)) ≤ δ ^ N * lovaszPotential (fun i => (b₀ i : E)) := by
      intro N
      induction N with
      | zero => exact ⟨b₀, by simp⟩
      | succ N ih =>
        obtain ⟨bN, hbN⟩ := ih
        obtain ⟨bN1, hbN1⟩ := hstep bN
        refine ⟨bN1, ?_⟩
        calc lovaszPotential (fun i => (bN1 i : E))
            ≤ δ * lovaszPotential (fun i => (bN i : E)) := hbN1.le
          _ ≤ δ * (δ ^ N * lovaszPotential (fun i => (b₀ i : E))) :=
              mul_le_mul_of_nonneg_left hbN hδ0.le
          _ = δ ^ (N + 1) * lovaszPotential (fun i => (b₀ i : E)) := by rw [pow_succ]; ring
    have hDmin_pos : 0 < lovaszPotentialMin L := lovaszPotentialMin_pos L hL0
    have hD0_pos : 0 < lovaszPotential (fun i => (b₀ i : E)) := lovaszPotential_pos b₀
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hDmin_pos hD0_pos) hδ1
    obtain ⟨bN, hbN⟩ := hiter N
    have hlb : lovaszPotentialMin L ≤ lovaszPotential (fun i => (bN i : E)) :=
      lovaszPotentialMin_le_lovaszPotential L hL0 bN
    have hub : δ ^ N * lovaszPotential (fun i => (b₀ i : E)) < lovaszPotentialMin L :=
      (lt_div_iff₀ hD0_pos).mp hN
    linarith

private lemma isLLLReducedVec_finCongr {m n : ℕ} (h : m = n) {v : Fin m → E} {δ : ℝ}
    (hLLL : IsLLLReducedVec v δ) :
    IsLLLReducedVec (fun i : Fin n => v (finCongr h.symm i)) δ := by
  subst h
  simpa using hLLL

/-- **Unconditional Lovász LLL-Reduced Basis Existence Theorem in `ℝ^n`**:
for ANY full-rank discrete lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)` and ANY `0 < δ < 1`
(in particular `δ = 3 / 4`), there unconditionally exists a `δ`-LLL-reduced `ℤ`-basis
`b : Basis (Fin n) ℤ Λ`. -/
theorem exists_lll_reduced_basis_euclidean {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ b : Basis (Fin n) ℤ Λ, IsLLLReduced b δ := by
  have hrk : RHDirect.ArakelovCovolume.rk Λ = n := by
    unfold RHDirect.ArakelovCovolume.rk
    rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  obtain ⟨b, hb⟩ := exists_lll_reduced_basis Λ hδ0 hδ1
  let e : Fin (RHDirect.ArakelovCovolume.rk Λ) ≃ Fin n := finCongr hrk
  let b' : Basis (Fin n) ℤ Λ := b.reindex e
  refine ⟨b', ?_⟩
  have hfun : (fun i : Fin n => (b' i : EuclideanSpace ℝ (Fin n))) =
      fun i : Fin n => (b (finCongr hrk.symm i) : EuclideanSpace ℝ (Fin n)) := by
    funext i
    simp [b', e]
  unfold IsLLLReduced
  rw [hfun]
  exact isLLLReducedVec_finCongr hrk hb

end LLLDefinitionsAndOperations

/-! ## Section 3: Unconditional LLL Bounds & Direct `Stage2SiegelReduction.IsSiegelReduced` Discharge -/

section LLLBoundsAndSiegelDischarge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- General single-step Lovász Gram–Schmidt norm inequality for `1 / 4 < δ`:
`(δ - 1 / 4) * ‖v*_k‖² ≤ ‖v*_{k+1}‖²`. -/
theorem lll_gsNorm_sq_step_general {n : ℕ} {v : Fin n → E} {δ : ℝ}
    (hLLL : IsLLLReducedVec v δ) (k : Fin n) (hk : k.1 + 1 < n) :
    (δ - 1 / 4) * ‖gramSchmidtVec v k‖ ^ 2 ≤ ‖gramSchmidtVec v ⟨k.1 + 1, hk⟩‖ ^ 2 := by
  have hlov := hLLL.2 k hk
  have hsr := hLLL.1 ⟨k.1 + 1, hk⟩ k (Nat.lt_succ_self k.1)
  have hmusq : (gsMu v ⟨k.1 + 1, hk⟩ k) ^ 2 ≤ 1 / 4 := by
    have h1 : |gsMu v ⟨k.1 + 1, hk⟩ k| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hsr 2
    rw [sq_abs] at h1
    linarith
  nlinarith [sq_nonneg ‖gramSchmidtVec v k‖]

/-- Single-step `(δ = 3/4)`-LLL Gram–Schmidt norm inequality:
`‖v*_k‖² ≤ 2 * ‖v*_{k+1}‖²`. -/
theorem lll_gsNorm_sq_step {n : ℕ} {v : Fin n → E}
    (hLLL : IsLLLReducedVec v (3 / 4)) (k : Fin n) (hk : k.1 + 1 < n) :
    ‖gramSchmidtVec v k‖ ^ 2 ≤ 2 * ‖gramSchmidtVec v ⟨k.1 + 1, hk⟩‖ ^ 2 := by
  have h := lll_gsNorm_sq_step_general hLLL k hk
  linarith

/-- **Telescoping `(δ = 3/4)`-LLL Gram–Schmidt Inequality**:
for all `j ≤ i`, `‖v*_j‖² ≤ 2^{i - j} * ‖v*_i‖²`. -/
theorem lll_gsNorm_sq_le {n : ℕ} {v : Fin n → E}
    (hLLL : IsLLLReducedVec v (3 / 4)) {j i : Fin n} (hji : j ≤ i) :
    ‖gramSchmidtVec v j‖ ^ 2 ≤ (2 : ℝ) ^ (i.1 - j.1) * ‖gramSchmidtVec v i‖ ^ 2 := by
  have hstep : ∀ d : ℕ, ∀ j i : Fin n, i.1 = j.1 + d →
      ‖gramSchmidtVec v j‖ ^ 2 ≤ (2 : ℝ) ^ d * ‖gramSchmidtVec v i‖ ^ 2 := by
    intro d
    induction d with
    | zero =>
      intro j i hij
      have heq : j = i := Fin.ext (by omega)
      subst heq; simp
    | succ d ih =>
      intro j i hij
      have hm_lt : j.1 + d < n := by omega
      let m : Fin n := ⟨j.1 + d, hm_lt⟩
      have h1 := ih j m rfl
      have hm1_lt : m.1 + 1 < n := by dsimp [m]; omega
      have h2 := lll_gsNorm_sq_step hLLL m hm1_lt
      have hieq : (⟨m.1 + 1, hm1_lt⟩ : Fin n) = i := Fin.ext (by dsimp [m]; omega)
      rw [hieq] at h2
      calc ‖gramSchmidtVec v j‖ ^ 2
          ≤ (2 : ℝ) ^ d * ‖gramSchmidtVec v m‖ ^ 2 := h1
        _ ≤ (2 : ℝ) ^ d * (2 * ‖gramSchmidtVec v i‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (2 : ℝ) ^ (d + 1) * ‖gramSchmidtVec v i‖ ^ 2 := by rw [pow_succ]; ring
  exact hstep (i.1 - j.1) j i (by omega)

/-- Exact finite geometric sum `∑_{j < i} 2^{i - j} = 2 * 2^i - 2` for all `i : ℕ`. -/
private lemma sum_two_pow_sub_eq (i : ℕ) :
    ∑ j : Fin i, (2 : ℝ) ^ (i - j.1) = 2 * (2 : ℝ) ^ i - 2 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Fin.sum_univ_castSucc]
    have hcast : ∑ j : Fin i, (2 : ℝ) ^ (i + 1 - j.castSucc.1) =
        2 * ∑ j : Fin i, (2 : ℝ) ^ (i - j.1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsub : i + 1 - j.1 = (i - j.1) + 1 := by omega
      simp only [Fin.val_castSucc, hsub, pow_succ]
      ring
    rw [hcast, ih]
    have hlast : i + 1 - (Fin.last i).1 = 1 := by simp
    rw [hlast, pow_one, pow_succ]
    ring

/-- **Sharp `(δ = 3/4)`-LLL Basis Vector Norm Bound**:
for every `i : Fin n`, `‖v_i‖² ≤ 2^i * ‖v*_i‖²`. -/
theorem lll_norm_sq_le {n : ℕ} {v : Fin n → E}
    (hLLL : IsLLLReducedVec v (3 / 4)) (i : Fin n) :
    ‖v i‖ ^ 2 ≤ (2 : ℝ) ^ i.1 * ‖gramSchmidtVec v i‖ ^ 2 := by
  rw [gramSchmidtVec_norm_sq v i]
  have hsum : ∑ j : Fin i.1,
      (gsMu v i ⟨j.1, lt_trans j.2 i.2⟩) ^ 2 *
        ‖gramSchmidtVec v ⟨j.1, lt_trans j.2 i.2⟩‖ ^ 2 ≤
      ((1 / 4 : ℝ) * ∑ j : Fin i.1, (2 : ℝ) ^ (i.1 - j.1)) *
        ‖gramSchmidtVec v i‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    let j' : Fin n := ⟨j.1, lt_trans j.2 i.2⟩
    have hsr : |gsMu v i j'| ≤ 1 / 2 := hLLL.1 i j' j.2
    have hmusq : (gsMu v i j') ^ 2 ≤ 1 / 4 := by
      have h1 : |gsMu v i j'| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hsr 2
      rw [sq_abs] at h1
      linarith
    have hgs := lll_gsNorm_sq_le hLLL (j := j') (i := i) (le_of_lt j.2)
    have hmul := mul_le_mul hmusq hgs (sq_nonneg _) (by norm_num)
    simpa only [mul_assoc, j'] using hmul
  rw [sum_two_pow_sub_eq i.1] at hsum
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ i.1 := one_le_pow₀ (by norm_num)
  nlinarith [sq_nonneg ‖gramSchmidtVec v i‖]

private lemma two_mul_sum_fin_val (n : ℕ) :
    2 * ∑ i : Fin n, i.1 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, mul_add]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring

private lemma sum_fin_val_cast_real (n : ℕ) :
    (∑ i : Fin n, (i.1 : ℝ)) = ((n : ℝ) * ((n : ℝ) - 1)) / 2 := by
  have hnat : 2 * ∑ i : Fin n, i.1 = n * (n - 1) := two_mul_sum_fin_val n
  cases n with
  | zero => simp
  | succ m =>
    have hcast : (2 : ℝ) * ∑ i : Fin (m + 1), (i.1 : ℝ) = ((m : ℝ) + 1) * (m : ℝ) := by
      have h1 : ((2 * ∑ i : Fin (m + 1), i.1 : ℕ) : ℝ) = (((m + 1) * m : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at h1
      exact h1
    push_cast
    linarith

/-- **Sharp LLL Orthogonality-Defect / Hadamard Product Bound**:
for any `(δ = 3/4)`-LLL-reduced family `v : Fin n → E`,
`∏_i ‖v_i‖ ≤ 2^{n(n-1)/4} * ∏_i ‖v*_i‖`. -/
theorem lll_prod_norm_le_prod_gsNorm {n : ℕ} {v : Fin n → E}
    (hLLL : IsLLLReducedVec v (3 / 4)) :
    ∏ i : Fin n, ‖v i‖ ≤
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) * ∏ i : Fin n, ‖gramSchmidtVec v i‖ := by
  have hsq : (∏ i : Fin n, ‖v i‖) ^ 2 ≤
      ((2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) * ∏ i : Fin n, ‖gramSchmidtVec v i‖) ^ 2 := by
    rw [← Finset.prod_pow, mul_pow, ← Finset.prod_pow]
    have hpow2 : ((2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4)) ^ 2 =
        ∏ i : Fin n, (2 : ℝ) ^ i.1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Finset.prod_pow_eq_pow_sum, ← Real.rpow_natCast]
      congr 1
      have hsum := sum_fin_val_cast_real n
      push_cast
      linarith
    rw [hpow2, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => lll_norm_sq_le hLLL i)
  have hnn1 : 0 ≤ ∏ i : Fin n, ‖v i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hnn2 : 0 ≤ (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) * ∏ i : Fin n, ‖gramSchmidtVec v i‖ :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  nlinarith

/-- **Sharp LLL Orthogonality-Defect Bound in Terms of Lattice Covolume** (General Inner Product Space):
`∏_i ‖b_i‖ ≤ 2^{r(r-1)/4} * covol(L)`. -/
theorem lll_prod_norm_le_covol [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} {b : Basis (Fin r) ℤ L} (hLLL : IsLLLReduced b (3 / 4)) :
    ∏ i : Fin r, ‖(b i : E)‖ ≤
      (2 : ℝ) ^ (((r : ℝ) * ((r : ℝ) - 1)) / 4) * RHDirect.ArakelovCovolume.covol L := by
  rw [gramSchmidt_covol_eq_prod b]
  exact lll_prod_norm_le_prod_gsNorm hLLL

/-- **Sharp LLL Orthogonality-Defect Bound in `ℝ^n`**:
`∏_i ‖b_i‖ ≤ 2^{n(n-1)/4} * ZLattice.covolume Λ volume`. -/
theorem lll_prod_norm_le_zlattice_covolume {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : Basis (Fin n) ℤ Λ} (hLLL : IsLLLReduced b (3 / 4)) :
    ∏ i : Fin n, ‖(b i : EuclideanSpace ℝ (Fin n))‖ ≤
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) * ZLattice.covolume Λ volume := by
  rw [gramSchmidt_zlattice_covolume_eq_prod Λ b]
  exact lll_prod_norm_le_prod_gsNorm hLLL

/-- **Unconditional LLL Shortest-Vector Approximation** (General Inner Product Space):
for any `(δ = 3/4)`-LLL-reduced `ℤ`-basis `b` of a discrete lattice `L ⊂ E` (`r > 0`),
`‖b_0‖ ≤ 2^{(r-1)/2} * λ₁(L)`. -/
theorem lll_first_vec_le_lambda1 [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (hr : 0 < r) {b : Basis (Fin r) ℤ L} (hLLL : IsLLLReduced b (3 / 4)) :
    ‖(b ⟨0, hr⟩ : E)‖ ≤
      (2 : ℝ) ^ (((r : ℝ) - 1) / 2) * RHDirect.Stage2SiegelReduction.lambda1 L := by
  have hL0 : L ≠ ⊥ := by
    intro hbot
    have h0 : (b ⟨0, hr⟩ : E) = 0 :=
      (Submodule.mem_bot ℤ).mp (hbot ▸ (b ⟨0, hr⟩).2)
    exact (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero ⟨0, hr⟩ h0
  obtain ⟨v₀, hv₀L, hv₀0, hv₀eq⟩ :=
    RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 L hL0
  obtain ⟨k, hk⟩ :=
    RHDirect.Stage2SiegelReduction.exists_gsVec_norm_le_of_mem_ne_zero b hv₀L hv₀0
  have hb0_eq : gramSchmidtVec (fun i => (b i : E)) ⟨0, hr⟩ = (b ⟨0, hr⟩ : E) :=
    gramSchmidtVec_zero hr (fun i => (b i : E))
  have htel := lll_gsNorm_sq_le hLLL (j := ⟨0, hr⟩) (i := k) (Nat.zero_le k.1)
  rw [hb0_eq] at htel
  have hpow_le : (2 : ℝ) ^ (k.1 - 0) ≤ (2 : ℝ) ^ (r - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hksq : ‖gramSchmidtVec (fun i => (b i : E)) k‖ ^ 2 ≤ ‖v₀‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hk 2
  have hsq : ‖(b ⟨0, hr⟩ : E)‖ ^ 2 ≤ ((2 : ℝ) ^ (((r : ℝ) - 1) / 2) * ‖v₀‖) ^ 2 := by
    have hpow2 : ((2 : ℝ) ^ (((r : ℝ) - 1) / 2)) ^ 2 = (2 : ℝ) ^ (r - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hexp : ((r : ℝ) - 1) / 2 * (2 : ℕ) = ((r - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hr]; push_cast; ring
      rw [hexp, Real.rpow_natCast]
    rw [mul_pow, hpow2]
    calc ‖(b ⟨0, hr⟩ : E)‖ ^ 2
        ≤ (2 : ℝ) ^ (k.1 - 0) * ‖gramSchmidtVec (fun i => (b i : E)) k‖ ^ 2 := htel
      _ ≤ (2 : ℝ) ^ (r - 1) * ‖gramSchmidtVec (fun i => (b i : E)) k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hpow_le (sq_nonneg _)
      _ ≤ (2 : ℝ) ^ (r - 1) * ‖v₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hksq (by positivity)
  rw [← hv₀eq]
  have hrhs_nn : 0 ≤ (2 : ℝ) ^ (((r : ℝ) - 1) / 2) * ‖v₀‖ :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _)
  nlinarith [norm_nonneg (b ⟨0, hr⟩ : E)]

/-- **Unconditional LLL Shortest-Vector Approximation in `ℝ^n`**
(directly matching `Stage10GeometryOfNumbers.shortestNorm`):
`‖b_0‖ ≤ 2^{(n-1)/2} * shortestNorm Λ`. -/
theorem lll_first_vec_le_shortestNorm {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : Basis (Fin n) ℤ Λ} (hLLL : IsLLLReduced b (3 / 4)) :
    ‖(b ⟨0, hn⟩ : EuclideanSpace ℝ (Fin n))‖ ≤
      (2 : ℝ) ^ (((n : ℝ) - 1) / 2) * RHDirect.Stage10GeometryOfNumbers.shortestNorm Λ := by
  exact lll_first_vec_le_lambda1 hn hLLL

/-- **Unconditional LLL Hermite Factor Bound**:
for any `(δ = 3/4)`-LLL-reduced `ℤ`-basis `b` of a discrete lattice `L ⊂ E` (`r > 0`),
`‖b_0‖ ≤ 2^{(r-1)/4} * covol(L)^{1/r}`. -/
theorem lll_first_vec_le_hermite_covol [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] {r : ℕ} (hr : 0 < r) {b : Basis (Fin r) ℤ L}
    (hLLL : IsLLLReduced b (3 / 4)) :
    ‖(b ⟨0, hr⟩ : E)‖ ≤
      (2 : ℝ) ^ (((r : ℝ) - 1) / 4) * (RHDirect.ArakelovCovolume.covol L) ^ (1 / (r : ℝ)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  have hb0_eq : gramSchmidtVec (fun i => (b i : E)) ⟨0, hr⟩ = (b ⟨0, hr⟩ : E) :=
    gramSchmidtVec_zero hr (fun i => (b i : E))
  have hprod : ∏ i : Fin r, ‖(b ⟨0, hr⟩ : E)‖ ^ 2 ≤
      (∏ i : Fin r, (2 : ℝ) ^ i.1) * ∏ i : Fin r, ‖gramSchmidtVec (fun j => (b j : E)) i‖ ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun i _ => ?_
    have h1 := lll_gsNorm_sq_le hLLL (j := ⟨0, hr⟩) (i := i) (Nat.zero_le i.1)
    simpa [hb0_eq] using h1
  have hlhs : ∏ _i : Fin r, ‖(b ⟨0, hr⟩ : E)‖ ^ 2 = (‖(b ⟨0, hr⟩ : E)‖ ^ 2) ^ r := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcov_sq : ∏ i : Fin r, ‖gramSchmidtVec (fun j => (b j : E)) i‖ ^ 2 =
      (RHDirect.ArakelovCovolume.covol L) ^ 2 := by
    rw [Finset.prod_pow, gramSchmidt_covol_eq_prod b]
  have hpow2 : ∏ i : Fin r, (2 : ℝ) ^ i.1 = (2 : ℝ) ^ (((r : ℝ) * ((r : ℝ) - 1)) / 2) := by
    rw [Finset.prod_pow_eq_pow_sum, ← Real.rpow_natCast]
    congr 1
    simpa using sum_fin_val_cast_real r
  rw [hlhs, hcov_sq, hpow2] at hprod
  have h2r : (‖(b ⟨0, hr⟩ : E)‖) ^ (2 * r) ≤
      ((2 : ℝ) ^ (((r : ℝ) - 1) / 4) * (RHDirect.ArakelovCovolume.covol L) ^ (1 / (r : ℝ))) ^ (2 * r) := by
    have hpowA : ((2 : ℝ) ^ (((r : ℝ) - 1) / 4)) ^ (2 * r) =
        (2 : ℝ) ^ (((r : ℝ) * ((r : ℝ) - 1)) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    have hpowB : ((RHDirect.ArakelovCovolume.covol L) ^ (1 / (r : ℝ))) ^ (2 * r) =
        (RHDirect.ArakelovCovolume.covol L) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcov_pos.le]
      have h2 : (1 / (r : ℝ)) * ((2 * r : ℕ) : ℝ) = (2 : ℕ) := by
        push_cast; field_simp [hrpos.ne']
      rw [h2, Real.rpow_natCast]
    rw [mul_pow, hpowA, hpowB]
    rwa [pow_mul]
  have h2r_pos : 0 < 2 * r := by omega
  have hrhs_nn : 0 ≤ (2 : ℝ) ^ (((r : ℝ) - 1) / 4) *
      (RHDirect.ArakelovCovolume.covol L) ^ (1 / (r : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hcov_pos.le _)
  exact le_of_pow_le_pow_left₀ h2r_pos.ne' hrhs_nn h2r

/-! ### Direct Unconditional Bridge to `Stage2SiegelReduction.IsSiegelReduced` & `Stage3ThetaSiegelFiberWitness` -/

/-- **General LLL → Siegel-Reduced Bridge**:
any `δ`-LLL-reduced basis (`1 / 4 < δ < 1`) is unconditionally
`(√((δ - 1/4)⁻¹), 1/2)`-Siegel-reduced (`Stage2SiegelReduction.IsSiegelReduced`). -/
theorem IsLLLReduced.toIsSiegelReduced_general {L : Submodule ℤ E} {r : ℕ}
    {b : Basis (Fin r) ℤ L} {δ : ℝ} (hδ_gt : 1 / 4 < δ) (hδ_lt : δ < 1)
    (hLLL : IsLLLReduced b δ) :
    RHDirect.Stage2SiegelReduction.IsSiegelReduced b (Real.sqrt (δ - 1 / 4)⁻¹) (1 / 2) where
  C_diag_ge_one := by
    have hpos : 0 < δ - 1 / 4 := by linarith
    have hle1 : δ - 1 / 4 ≤ 1 := by linarith
    have hinv : 1 ≤ (δ - 1 / 4)⁻¹ := (one_le_inv₀ hpos).mpr hle1
    have hsq := Real.sqrt_le_sqrt hinv
    rwa [Real.sqrt_one] at hsq
  C_unip_nonneg := by norm_num
  size_reduced := fun i j hij => hLLL.1 j i hij
  height_ratio := fun j hj => by
    have hpos : 0 < δ - 1 / 4 := by linarith
    have hstep := lll_gsNorm_sq_step_general hLLL j hj
    have hsq : ‖gramSchmidtVec (fun k => (b k : E)) j‖ ^ 2 ≤
        (Real.sqrt (δ - 1 / 4)⁻¹ * ‖gramSchmidtVec (fun k => (b k : E)) ⟨j.1 + 1, hj⟩‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hpos.le)]
      have h1 := mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hpos.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h1
    have hrhs_nn : 0 ≤ Real.sqrt (δ - 1 / 4)⁻¹ *
        ‖gramSchmidtVec (fun k => (b k : E)) ⟨j.1 + 1, hj⟩‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    change ‖gramSchmidtVec (fun k => (b k : E)) j‖ ≤
      Real.sqrt (δ - 1 / 4)⁻¹ * ‖gramSchmidtVec (fun k => (b k : E)) ⟨j.1 + 1, hj⟩‖
    nlinarith [norm_nonneg (gramSchmidtVec (fun k => (b k : E)) j)]

/-- **Sharp `(δ = 3/4)`-LLL → `(√2, 1/2)`-Siegel-Reduced Bridge**. -/
theorem IsLLLReduced.toIsSiegelReduced_sqrt2 {L : Submodule ℤ E} {r : ℕ}
    {b : Basis (Fin r) ℤ L} (hLLL : IsLLLReduced b (3 / 4)) :
    RHDirect.Stage2SiegelReduction.IsSiegelReduced b (Real.sqrt 2) (1 / 2) := by
  have h := hLLL.toIsSiegelReduced_general (by norm_num) (by norm_num)
  have h2 : ((3 / 4 : ℝ) - 1 / 4)⁻¹ = 2 := by norm_num
  rwa [h2] at h

/-- **Explicit Rational `(δ = 3/4)`-LLL → `(2, 1/2)`-Siegel-Reduced Bridge**:
every `(3/4)`-LLL-reduced basis satisfies `Stage2SiegelReduction.IsSiegelReduced` with explicit
constants `C_diag = 2` and `C_unip = 1 / 2`! -/
theorem IsLLLReduced.toIsSiegelReduced {L : Submodule ℤ E} {r : ℕ}
    {b : Basis (Fin r) ℤ L} (hLLL : IsLLLReduced b (3 / 4)) :
    RHDirect.Stage2SiegelReduction.IsSiegelReduced b 2 (1 / 2) where
  C_diag_ge_one := by norm_num
  C_unip_nonneg := by norm_num
  size_reduced := fun i j hij => hLLL.1 j i hij
  height_ratio := fun j hj => by
    have h := (hLLL.toIsSiegelReduced_sqrt2).height_ratio j hj
    have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
      have h1 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right hsqrt2_le (norm_nonneg _))

/-- **Exact Average Log-Norm Upper Bound for `Stage3ThetaSiegelFiberWitness.bM_prod_norm_le`**:
for any `(3/4)`-LLL-reduced `ℤ`-basis `b` of a nonzero discrete lattice `L ⊂ E` (`r = rk L`),
`log (∏_j ‖b_j‖) / r ≤ log (covol L) / r + ((r - 1) / 4) * log 2`. -/
theorem lll_log_prod_norm_div_rk_le [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L}
    (hLLL : IsLLLReduced b (3 / 4)) :
    Real.log (∏ j : Fin (RHDirect.ArakelovCovolume.rk L), ‖(b j : E)‖) /
        (RHDirect.ArakelovCovolume.rk L : ℝ) ≤
      Real.log (RHDirect.ArakelovCovolume.covol L) / (RHDirect.ArakelovCovolume.rk L : ℝ) +
        (((RHDirect.ArakelovCovolume.rk L : ℝ) - 1) / 4) * Real.log 2 := by
  let r := RHDirect.ArakelovCovolume.rk L
  have hrpos : (0 : ℝ) < (r : ℝ) :=
    Nat.cast_pos.mpr (RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0)
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  have hprod_pos : 0 < ∏ j : Fin r, ‖(b j : E)‖ :=
    Finset.prod_pos fun j _ =>
      norm_pos_iff.mpr ((RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero j)
  have hbound := lll_prod_norm_le_covol hLLL
  have hlog := Real.log_le_log hprod_pos hbound
  rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num) _).ne' hcov_pos.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog hrpos.le
  have hrhs : (((r : ℝ) * ((r : ℝ) - 1)) / 4 * Real.log 2 +
      Real.log (RHDirect.ArakelovCovolume.covol L)) / (r : ℝ) =
      Real.log (RHDirect.ArakelovCovolume.covol L) / (r : ℝ) +
        (((r : ℝ) - 1) / 4) * Real.log 2 := by
    field_simp [hrpos.ne']
    ring
  rwa [hrhs] at hdiv

/-- Slope-form rewrite of `lll_log_prod_norm_div_rk_le`:
`log (∏_j ‖b_j‖) / rk L ≤ -slope L + ((rk L - 1) / 4) * log 2`. -/
theorem lll_log_prod_norm_div_rk_le_neg_slope [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L}
    (hLLL : IsLLLReduced b (3 / 4)) :
    Real.log (∏ j : Fin (RHDirect.ArakelovCovolume.rk L), ‖(b j : E)‖) /
        (RHDirect.ArakelovCovolume.rk L : ℝ) ≤
      -RHDirect.ArakelovCovolume.slope L +
        (((RHDirect.ArakelovCovolume.rk L : ℝ) - 1) / 4) * Real.log 2 := by
  have h := lll_log_prod_norm_div_rk_le hL0 hLLL
  have hslope : -RHDirect.ArakelovCovolume.slope L =
      Real.log (RHDirect.ArakelovCovolume.covol L) / (RHDirect.ArakelovCovolume.rk L : ℝ) := by
    unfold RHDirect.ArakelovCovolume.slope RHDirect.ArakelovCovolume.degAr
    ring
  rwa [← hslope] at h

/-- **Master Unconditional LLL & Siegel-Reduced Basis Existence Theorem for Stage 3**:
for ANY nonzero discrete `ℤ`-lattice `L` in ANY finite-dimensional real inner product space `E`,
there unconditionally exists a `ℤ`-basis `b : Basis (Fin (rk L)) ℤ L` that simultaneously:
1. is `(3/4)`-LLL-reduced (`IsLLLReduced b (3 / 4)`),
2. satisfies `Stage2SiegelReduction.IsSiegelReduced b 2 (1 / 2)`
   (directly discharging `Stage3ThetaSiegelFiberWitness.bM_siegel`),
3. satisfies the sharp Siegel condition `Stage2SiegelReduction.IsSiegelReduced b (Real.sqrt 2) (1 / 2)`,
4. satisfies the sharp orthogonality-defect bound
   `∏_j ‖b_j‖ ≤ 2^{rk(L)(rk(L)-1)/4} * covol(L)`,
5. satisfies the average log-norm ceiling
   `log(∏_j ‖b_j‖) / rk(L) ≤ log(covol L) / rk(L) + ((rk(L) - 1) / 4) * log 2`
   (directly feeding `Stage3ThetaSiegelFiberWitness.bM_prod_norm_le`), and
6. satisfies the two-sided first-minimum approximation
   `λ₁(L) ≤ ‖b_0‖ ≤ 2^{(rk(L) - 1) / 2} * λ₁(L)`. -/
theorem exists_siegelReduced_lll_basis_for_stage3 [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L,
      IsLLLReduced b (3 / 4) ∧
      RHDirect.Stage2SiegelReduction.IsSiegelReduced b 2 (1 / 2) ∧
      RHDirect.Stage2SiegelReduction.IsSiegelReduced b (Real.sqrt 2) (1 / 2) ∧
      (∏ j : Fin (RHDirect.ArakelovCovolume.rk L), ‖(b j : E)‖ ≤
        (2 : ℝ) ^ (((RHDirect.ArakelovCovolume.rk L : ℝ) *
          ((RHDirect.ArakelovCovolume.rk L : ℝ) - 1)) / 4) *
          RHDirect.ArakelovCovolume.covol L) ∧
      (Real.log (∏ j : Fin (RHDirect.ArakelovCovolume.rk L), ‖(b j : E)‖) /
          (RHDirect.ArakelovCovolume.rk L : ℝ) ≤
        Real.log (RHDirect.ArakelovCovolume.covol L) / (RHDirect.ArakelovCovolume.rk L : ℝ) +
          (((RHDirect.ArakelovCovolume.rk L : ℝ) - 1) / 4) * Real.log 2) ∧
      (RHDirect.Stage2SiegelReduction.lambda1 L ≤
        ‖(b ⟨0, RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0⟩ : E)‖ ∧
       ‖(b ⟨0, RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0⟩ : E)‖ ≤
        (2 : ℝ) ^ (((RHDirect.ArakelovCovolume.rk L : ℝ) - 1) / 2) *
          RHDirect.Stage2SiegelReduction.lambda1 L) := by
  obtain ⟨b, hLLL⟩ := exists_lll_reduced_basis L (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have hrpos := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  have hb0_ne : (b ⟨0, hrpos⟩ : E) ≠ 0 :=
    (RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero ⟨0, hrpos⟩
  exact ⟨b,
    hLLL,
    hLLL.toIsSiegelReduced,
    hLLL.toIsSiegelReduced_sqrt2,
    lll_prod_norm_le_covol hLLL,
    lll_log_prod_norm_div_rk_le hL0 hLLL,
    ⟨RHDirect.Stage2SiegelReduction.lambda1_le_norm L (b ⟨0, hrpos⟩).2 hb0_ne,
     lll_first_vec_le_lambda1 hrpos hLLL⟩⟩

end LLLBoundsAndSiegelDischarge

end

end RHDirect.Stage11LLLSiegelReduction
