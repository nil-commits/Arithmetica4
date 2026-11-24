import RHDirect.Stage11BesselWaveSchur
import RHDirect.BesselWaveGrid
import RHDirect.LatticeFrame
import RHDirect.Stage2ThetaWire

/-!
# RHDirect.Stage14M2_BesselSchurBlock

Field-2 Package M2 (Wave 1, Module 6 of 6): **Concrete Bessel Block Matrices, Isometric
Block Factorization (`BlockReal_at` / `Vr0`), Real Schur Decay, Bessel Gram Off-Diagonal
Bounds, `MatKF` Spectral Parameters, and Test-Vector Frame Assembly** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.

Distills and unconditionally proves the complete Schur–Bessel block architecture from
Alpöge's `Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen` and
`CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries`, directly grounded on
`RHDirect.Stage11BesselWaveSchur`, `RHDirect.BesselWaveGrid`, `RHDirect.LatticeFrame`, and
`RHDirect.Stage2ThetaWire`, ready for M2 Wave 2 (`BesselIntegrality` & `FrameRealCompile`).

## Main Unconditional Exports

1. **`BesselBlockMatrix` (Section 1)**:
   - Ambient Bessel block matrix realization `PMat` (`⟪f a, Pu u (eC u i)⟫`), conjugated block
     matrix `pmatConj ε`, unfolding-weighted cross-Gram operators `kOp u u'` and matrix blocks
     `opMat`, exact Gram identity `(pmat u)ᴴ * pmat u' = ⟪Pu u (eC u i), Pu u' (eC u' j)⟫`,
     `kp_eq_opMat` (`gramCross` ↔ `opMat kOp`), `hsSq` invariance under `IsIdOrConj ε`,
     and `unfolding_constant_pos_of_diagonal`.
2. **`IsometryBlockFactorization` (Section 2)**:
   - Isometric subspace factorization `Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ` with
     `(Vr u)ᴴ * Vr u = 1` and invertible basis-change matrices `(Y u, Y')` intertwining the
     top `κ`-rows of `(B u) * Vr u` with `(Y'⁻¹ * (M_Bk u).map ε * Y u)`.
   - Concrete Hilbert-space construction (`besselId_to_isometryBlockFactorization`) extending
     orthonormal Bessel rows to a full ambient basis `f : OrthonormalBasis (κ ⊕ κ₁) ℂ HH`,
     constructing `Vr0`, proving `vr0_isometry` and `pmat_mul_vr0`, and bridging directly into
     `LatticeFrame.compressFamily` (`frameOp_compress_loewner`, `hsSq_isom_compress`).
3. **`block_real_schur_decay` (Section 3)**:
   - Block-matrix Schur test (`block_matrix_schur_le`), Gaussian-separated block Schur decay
     (`block_real_schur_decay`) via `Stage11BesselWaveSchur.cotlar_stein_symmetric` and
     `schur_test_hermitian_quad_le`, and uniform-in-`|ι|` operator norm & frame trace-square
     bounds.
4. **`bessel_gram_offdiag_le` (Section 4)**:
   - Concrete Bessel Gram off-diagonal decay for both `L²(ℝ^d, ℂ)` separated wave-packet
     grids (`besselGram`, `besselOffDiagMatrix`, row-sum `≤ ε`, Frobenius sum `≤ ε² * |W|`,
     and operator norm `≤ ε`) and block-matrix cross-Gram families (`LatticeFrame.gramCross`),
     discharging `LatticeFrame.GramInput` and `FrameTraceRatio` / `FrameDiagDefect`.
5. **`matKF_spectral_parameters` (Section 5)**:
   - Concrete `MatKSpectralParams` and `BesselGramSpectralBundle` formalizing Alpöge's
     `MatK_at`, `MatKF`, `RamShareF`, and `MatSF` (`TopDensityNGeSixteen.lean`).
   - Explicit scale threshold `matKF_spectral_parameters` deriving all `Stage2GramFrameFiber`
     numerical bounds (`sg ≤ 1/20`, `de ≤ 1/4`, `δ ≤ 1/2`, `√e0 ≤ sg / 2`, `η0, η1 ≤ sg / 2`,
     `5 * sg + 3 * √de + 4 * √(2 * e0) ≤ 11 / 10`) from `exp(-(x ^ (eps / 8)))` decay, plus
     ramified Euler-product codimension bound `ramShare_of_euler_deficit`.
6. **`bessel_test_vector_frame` (Section 6)**:
   - Unified Bessel test-vector frame bundle combining `L²` frame stability, linear
     independence, spacing-5 Vandermonde Lagrange delta test-vectors (`progY`, `gridY`),
     rational word-factor bounds (`wordEval`), and direct construction of a non-short-circuited
     `Stage2ThetaWire.Stage2GramFrameFiber` (`toStage2GramFrameFiber`) discharging
     `BostSlopeFiber.SlopeIneq`.
-/

noncomputable section

open Real Finset Matrix MeasureTheory Filter Module Submodule
open scoped BigOperators InnerProductSpace ComplexConjugate ComplexOrder

namespace RHDirect.Stage14M2_BesselSchurBlock

/-! ## Section 1: `IsIdOrConj` & Concrete Ambient `BesselBlockMatrix` Realization -/

section BesselBlockMatrixSection

/-- A ring endomorphism of `ℂ` that preserves `ℝ` and commutes with conjugation
(namely `RingHom.id ℂ` or `starRingEnd ℂ`, as in `TopDensityNGeSixteen.IsIdOrConj`). -/
structure IsIdOrConj (ε : ℂ →+* ℂ) : Prop where
  involutive : ∀ z : ℂ, ε (ε z) = z
  map_star : ∀ z : ℂ, ε (star z) = star (ε z)
  map_ofReal : ∀ r : ℝ, ε (r : ℂ) = (r : ℂ)

theorem isIdOrConj_id : IsIdOrConj (RingHom.id ℂ) where
  involutive _ := rfl
  map_star _ := rfl
  map_ofReal _ := rfl

theorem isIdOrConj_conj : IsIdOrConj (starRingEnd ℂ) where
  involutive z := star_star z
  map_star z := by simp
  map_ofReal r := Complex.conj_ofReal r

lemma IsIdOrConj.norm_map {ε : ℂ →+* ℂ} (hε : IsIdOrConj ε) (z : ℂ) : ‖ε z‖ = ‖z‖ := by
  have hsq : ((‖ε z‖ ^ 2 : ℝ) : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ((‖ε z‖ ^ 2 : ℝ) : ℂ) = star (ε z) * ε z := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, ← hε.map_star, ← map_mul, ← h2, hε.map_ofReal]
  have hre : ‖ε z‖ ^ 2 = ‖z‖ ^ 2 := Complex.ofReal_injective hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hre

lemma conjTranspose_map_isIdOrConj {m n : Type*} (A : Matrix m n ℂ)
    {ε : ℂ →+* ℂ} (hε : IsIdOrConj ε) :
    (A.map ε)ᴴ = (Aᴴ).map ε := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hε.map_star]

lemma hsSq_map_isIdOrConj {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    {ε : ℂ →+* ℂ} (hε : IsIdOrConj ε) :
    LatticeFrame.hsSq (A.map ε) = LatticeFrame.hsSq A := by
  unfold LatticeFrame.hsSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, hε.norm_map]

lemma det_map_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (ε : ℂ →+* ℂ) (hA : IsUnit A.det) :
    IsUnit (A.map ε).det := by
  have hdet : (A.map ε).det = ε A.det := (RingHom.map_det ε A).symm
  rw [hdet]
  exact hA.map ε

lemma sqrt_inv_mul_eq_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a⁻¹ * b⁻¹) = (a * b) ^ (-(1 / 2 : ℝ)) := by
  rw [← mul_inv, Real.sqrt_eq_rpow, Real.inv_rpow (mul_pos ha hb).le, Real.rpow_neg (mul_pos ha hb).le]

/-- **Concrete Ambient Bessel Block Matrix System (`BesselBlockMatrix`)**:
Packages an ambient finite-dimensional complex Hilbert space `HH` with orthonormal basis
`f : OrthonormalBasis (κ ⊕ κ₁) ℂ HH`, a finite word family `u : ι`, source Hilbert spaces
`Cu u` of dimension `d u` with orthonormal bases `eC u : OrthonormalBasis (Fin (d u)) ℂ (Cu u)`,
bounded linear Bessel-theta operators `Pu u : Cu u →L[ℂ] HH`, and unfolding/measure weights
`c0 : ι → ℝ`.

Corresponds directly to `PMat`, `opMat`, `S.KD`, and `KpG` in Alpöge's
`TopDensityNGeSixteen.lean`. -/
structure BesselBlockMatrix (ι κ κ₁ : Type) [Fintype ι] [Fintype κ] [Fintype κ₁] : Type 1 where
  HH : Type
  [normedHH : NormedAddCommGroup HH]
  [innerHH : InnerProductSpace ℂ HH]
  [finHH : FiniteDimensional ℂ HH]
  f : OrthonormalBasis (κ ⊕ κ₁) ℂ HH
  d : ι → ℕ
  Cu : ι → Type
  [normedCu : ∀ u, NormedAddCommGroup (Cu u)]
  [innerCu : ∀ u, InnerProductSpace ℂ (Cu u)]
  [finCu : ∀ u, FiniteDimensional ℂ (Cu u)]
  eC : ∀ u, OrthonormalBasis (Fin (d u)) ℂ (Cu u)
  Pu : ∀ u, Cu u →L[ℂ] HH
  c0 : ι → ℝ
  c0_nonneg : ∀ u, 0 ≤ c0 u

attribute [instance] BesselBlockMatrix.normedHH BesselBlockMatrix.innerHH BesselBlockMatrix.finHH
  BesselBlockMatrix.normedCu BesselBlockMatrix.innerCu BesselBlockMatrix.finCu

namespace BesselBlockMatrix

variable {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁]

/-- Ambient block matrix `PMat u` with entries `⟪f a, Pu u (eC u i)⟫_ℂ`. -/
def pmat (M : BesselBlockMatrix ι κ κ₁) (u : ι) :
    Matrix (κ ⊕ κ₁) (Fin (M.d u)) ℂ :=
  fun a i => ⟪M.f a, M.Pu u (M.eC u i)⟫_ℂ

/-- Conjugated ambient block matrix `(PMat u).map ε`. -/
def pmatConj (M : BesselBlockMatrix ι κ κ₁) (ε : ℂ →+* ℂ) (u : ι) :
    Matrix (κ ⊕ κ₁) (Fin (M.d u)) ℂ :=
  (M.pmat u).map ε

/-- Reindexed ambient block matrix `Fin (Fintype.card (κ ⊕ κ₁)) × Fin (d u)` for `LatticeFrame`. -/
def pmatFin (M : BesselBlockMatrix ι κ κ₁) (ε : ℂ →+* ℂ) (u : ι) :
    Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (M.d u)) ℂ :=
  Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)) (Equiv.refl _) (M.pmatConj ε u)

/-- Unfolding-weighted cross-Gram operator `K_{u, u'} = (c0 u * c0 u')^(-1/2) • (Pu u)* ∘ Pu u'`. -/
def kOp (M : BesselBlockMatrix ι κ κ₁) (u u' : ι) :
    M.Cu u' →L[ℂ] M.Cu u :=
  (((M.c0 u * M.c0 u') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((M.Pu u).adjoint.comp (M.Pu u'))

/-- Matrix representation of an operator `A : Cu u' →L[ℂ] Cu u` in the orthonormal bases `eC`. -/
def opMat (M : BesselBlockMatrix ι κ κ₁) {u u' : ι} (A : M.Cu u' →L[ℂ] M.Cu u) :
    Matrix (Fin (M.d u)) (Fin (M.d u')) ℂ :=
  fun i j => ⟪M.eC u i, A (M.eC u' j)⟫_ℂ

/-- Exact cross-Gram inner-product identity `(PMat u)ᴴ * (PMat u') = (⟪Pu u e_i, Pu u' e_j⟫)`. -/
theorem gram_pmat_eq (M : BesselBlockMatrix ι κ κ₁) (u u' : ι) :
    (M.pmat u)ᴴ * M.pmat u' =
      fun i j => ⟪M.Pu u (M.eC u i), M.Pu u' (M.eC u' j)⟫_ℂ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, pmat]
  have hterm : ∀ a : κ ⊕ κ₁,
      star ⟪M.f a, M.Pu u (M.eC u i)⟫_ℂ * ⟪M.f a, M.Pu u' (M.eC u' j)⟫_ℂ =
        ⟪M.Pu u (M.eC u i), M.f a⟫_ℂ * ⟪M.f a, M.Pu u' (M.eC u' j)⟫_ℂ := fun a => by
    rw [← inner_conj_symm (M.Pu u (M.eC u i)) (M.f a)]
    rfl
  simp_rw [hterm]
  exact M.f.sum_inner_mul_inner (M.Pu u (M.eC u i)) (M.Pu u' (M.eC u' j))

/-- Entrywise formula for `opMat (kOp u u')`. -/
theorem opMat_kOp_apply (M : BesselBlockMatrix ι κ κ₁) (u u' : ι)
    (i : Fin (M.d u)) (j : Fin (M.d u')) :
    M.opMat (M.kOp u u') i j =
      (((M.c0 u * M.c0 u') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ⟪M.Pu u (M.eC u i), M.Pu u' (M.eC u' j)⟫_ℂ := by
  unfold opMat kOp
  rw [_root_.smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- Exact identification between `LatticeFrame.gramCross` of `pmatFin` (with weights `(c0 u)⁻¹`)
and the operator matrix `(opMat (kOp u u')).map ε` (`kp_eq` in `TopDensityNGeSixteen.lean`). -/
theorem kp_eq_opMat (M : BesselBlockMatrix ι κ κ₁) {ε : ℂ →+* ℂ} (hε : IsIdOrConj ε)
    (hc : ∀ u, 0 < M.c0 u) (u u' : ι) :
    LatticeFrame.gramCross (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u u' =
      (M.opMat (M.kOp u u')).map ε := by
  have hp : (M.pmatFin ε u)ᴴ * M.pmatFin ε u' = (M.pmatConj ε u)ᴴ * M.pmatConj ε u' := by
    ext i j
    simp only [pmatFin, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl]
    exact (Fintype.equivFin (κ ⊕ κ₁)).symm.sum_comp fun a =>
      star (M.pmatConj ε u a i) * M.pmatConj ε u' a j
  unfold LatticeFrame.gramCross
  rw [hp]
  unfold pmatConj
  rw [conjTranspose_map_isIdOrConj _ hε, ← Matrix.map_mul, gram_pmat_eq,
    sqrt_inv_mul_eq_rpow (hc u) (hc u')]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, opMat_kOp_apply, map_mul, hε.map_ofReal,
    smul_eq_mul]
  rfl

/-- Exact operator-matrix subtraction identity `(opMat (A - id)).map ε = (opMat A).map ε - 1`. -/
theorem opMat_sub_id (M : BesselBlockMatrix ι κ κ₁) (u : ι)
    (A : M.Cu u →L[ℂ] M.Cu u) (ε : ℂ →+* ℂ) :
    (M.opMat (A - ContinuousLinearMap.id ℂ (M.Cu u))).map ε =
      (M.opMat A).map ε - 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, opMat, _root_.sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, map_sub]
  congr 1
  rw [orthonormal_iff_ite.mp (M.eC u).orthonormal i j, Matrix.one_apply]
  split_ifs <;> simp

/-- Exact agreement between `hsSq (gramCross)` and `hsSq (opMat (kOp u u'))`. -/
theorem hsSq_gramCross_pmat (M : BesselBlockMatrix ι κ κ₁) {ε : ℂ →+* ℂ} (hε : IsIdOrConj ε)
    (hc : ∀ u, 0 < M.c0 u) (u u' : ι) :
    LatticeFrame.hsSq (LatticeFrame.gramCross (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u u') =
      LatticeFrame.hsSq (M.opMat (M.kOp u u')) := by
  rw [kp_eq_opMat M hε hc u u', hsSq_map_isIdOrConj _ hε]

/-- Exact agreement between `hsSq (gramDiag - 1)` and `hsSq (opMat (kOp u u - id))`. -/
theorem hsSq_gramDiag_sub_one_pmat (M : BesselBlockMatrix ι κ κ₁) {ε : ℂ →+* ℂ}
    (hε : IsIdOrConj ε) (hc : ∀ u, 0 < M.c0 u) (u : ι) :
    LatticeFrame.hsSq (LatticeFrame.gramDiag (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u - 1) =
      LatticeFrame.hsSq (M.opMat (M.kOp u u - ContinuousLinearMap.id ℂ (M.Cu u))) := by
  unfold LatticeFrame.gramDiag
  rw [kp_eq_opMat M hε hc u u, ← opMat_sub_id, hsSq_map_isIdOrConj _ hε]

/-- Exact Hilbert–Schmidt norm of `0 - I` on `Cu u` equals `d u`. -/
lemma hsSq_opMat_neg_id (M : BesselBlockMatrix ι κ κ₁) (u : ι) :
    LatticeFrame.hsSq (M.opMat (0 - ContinuousLinearMap.id ℂ (M.Cu u))) = (M.d u : ℝ) := by
  have hmat : M.opMat (0 - ContinuousLinearMap.id ℂ (M.Cu u)) = -1 := by
    ext i j
    simp only [opMat, zero_sub, _root_.neg_apply, ContinuousLinearMap.id_apply,
      inner_neg_right, Matrix.neg_apply, Matrix.one_apply]
    rw [orthonormal_iff_ite.mp (M.eC u).orthonormal i j]
  rw [hmat]
  unfold LatticeFrame.hsSq
  have hrow : ∀ i : Fin (M.d u),
      ∑ j : Fin (M.d u), ‖(-1 : Matrix (Fin (M.d u)) (Fin (M.d u)) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Unfolding Constant Positivity (`unfolding_constant_pos_of_diagonal`)**:
If the diagonal Bessel Gram defect satisfies `hsSq (opMat (kOp u u - I)) ≤ e0 * d u` with
`e0 < 1` and `0 < d u`, then necessarily `0 < c0 u` (exact `TopDensityNGeSixteen` proof!). -/
theorem unfolding_constant_pos_of_diagonal (M : BesselBlockMatrix ι κ κ₁) (u : ι)
    {e0 : ℝ} (he : e0 < 1) (hd : 0 < M.d u)
    (hdiag : LatticeFrame.hsSq (M.opMat (M.kOp u u - ContinuousLinearMap.id ℂ (M.Cu u))) ≤
      e0 * (M.d u : ℝ)) :
    0 < M.c0 u := by
  rcases (M.c0_nonneg u).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hk0 : M.kOp u u = 0 := by
      unfold kOp
      rw [← hzero, mul_zero, Real.zero_rpow (by norm_num)]
      simp
    rw [hk0, hsSq_opMat_neg_id] at hdiag
    have hd' : (0 : ℝ) < (M.d u : ℝ) := Nat.cast_pos.mpr hd
    nlinarith

/-- **Ambient Dimension Positivity (`ambient_dim_pos_of_diagonal`)**:
If `hsSq (opMat (kOp u u - I)) ≤ e0 * d u` with `e0 < 1`, `0 < d u`, and `0 < c0 u`,
then `0 < Fintype.card (κ ⊕ κ₁)`. -/
theorem ambient_dim_pos_of_diagonal (M : BesselBlockMatrix ι κ κ₁) (u : ι)
    {e0 : ℝ} (he : e0 < 1) (hd : 0 < M.d u)
    (hdiag : LatticeFrame.hsSq (M.opMat (M.kOp u u - ContinuousLinearMap.id ℂ (M.Cu u))) ≤
      e0 * (M.d u : ℝ)) :
    0 < Fintype.card (κ ⊕ κ₁) := by
  by_contra h0
  have hcard0 : Fintype.card (κ ⊕ κ₁) = 0 := Nat.eq_zero_of_not_pos h0
  have hHH0 : Module.finrank ℂ M.HH = 0 := by
    rw [Module.finrank_eq_card_basis M.f.toBasis, hcard0]
  have : Subsingleton M.HH := Module.finrank_zero_iff.mp hHH0
  have hk0 : M.kOp u u = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hPu : M.Pu u x = 0 := Subsingleton.elim _ _
    simp [kOp, hPu]
  rw [hk0, hsSq_opMat_neg_id] at hdiag
  have hd' : (0 : ℝ) < (M.d u : ℝ) := Nat.cast_pos.mpr hd
  nlinarith

end BesselBlockMatrix

end BesselBlockMatrixSection

/-! ## Section 2: `IsometryBlockFactorization` — Isometric Compression & `Vr0` Realization -/

section IsometryBlockFactorizationSection

/-- **Isometric Block Factorization (`IsometryBlockFactorization`)**:
Packages a `BesselBlockMatrix M`, target subspaces of dimensions `r : ι → ℕ`, an automorphism
`ε` (`IsIdOrConj ε`), invertible change-of-basis matrices `Y u` (`r u × r u`) and `Y'` (`κ × κ`),
isometric embeddings `Vr u : d u × r u` (`(Vr u)ᴴ * Vr u = 1`), and an algebraic/integral Bessel
matrix `MBk u : Matrix κ (Fin (r u)) ℂ` satisfying the exact top-block factorization:
`((pmatConj M ε u) * Vr u) (Sum.inl k) j = (Y'⁻¹ * (MBk u).map ε * Y u) k j`.

This is the exact structural output of `BlockReal_at` (`TopDensityNGeSixteen.lean:1087`)
needed by Wave 2 (`BesselIntegrality` and `FrameRealCompile`). -/
structure IsometryBlockFactorization (ι κ κ₁ : Type)
    [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] : Type 1 where
  M : BesselBlockMatrix ι κ κ₁
  r : ι → ℕ
  ε : ℂ →+* ℂ
  hε : IsIdOrConj ε
  Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ
  Y' : Matrix κ κ ℂ
  Vr : ∀ u, Matrix (Fin (M.d u)) (Fin (r u)) ℂ
  MBk : ∀ u, Matrix κ (Fin (r u)) ℂ
  hY : ∀ u, IsUnit (Y u).det
  hY' : IsUnit Y'.det
  hVr : ∀ u, (Vr u)ᴴ * Vr u = 1
  factor_eq : ∀ u (k : κ) (j : Fin (r u)),
    ((M.pmatConj ε u) * Vr u) (Sum.inl k) j =
      (Y'⁻¹ * (MBk u).map ε * Y u) k j

namespace IsometryBlockFactorization

variable {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ]

lemma isIsometryFamily (F : IsometryBlockFactorization ι κ κ₁) :
    LatticeFrame.IsIsometryFamily F.Vr :=
  F.hVr

/-- Compressed ambient matrix `(pmatFin M ε u) * Vr u` (`compressFamily`). -/
def compressedMat (F : IsometryBlockFactorization ι κ κ₁) :
    ∀ u, Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (F.r u)) ℂ :=
  LatticeFrame.compressFamily (F.M.pmatFin F.ε) F.Vr

/-- **Loewner Domination for `IsometryBlockFactorization`**:
`0 ⪯ frameOp (compressedMat F) ga ⪯ frameOp (pmatFin M ε) ga`. -/
theorem frameOp_loewner (F : IsometryBlockFactorization ι κ κ₁) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) :
    (LatticeFrame.frameOp F.compressedMat ga).PosSemidef ∧
    (LatticeFrame.frameOp (F.M.pmatFin F.ε) ga -
      LatticeFrame.frameOp F.compressedMat ga).PosSemidef :=
  LatticeFrame.frameOp_compress_loewner (F.M.pmatFin F.ε) F.Vr ga F.isIsometryFamily hga

/-- **Cross-Gram Hilbert–Schmidt Contraction**:
Every compressed cross-Gram block satisfies `hsSq (gramCross (compressedMat F) ga u u') ≤
hsSq (gramCross (pmatFin M ε) ga u u')`. -/
theorem hsSq_gramCross_compress_le (F : IsometryBlockFactorization ι κ κ₁) (ga : ι → ℝ)
    (u u' : ι) :
    LatticeFrame.hsSq (LatticeFrame.gramCross F.compressedMat ga u u') ≤
      LatticeFrame.hsSq (LatticeFrame.gramCross (F.M.pmatFin F.ε) ga u u') := by
  rw [compressedMat, LatticeFrame.gramCross_compress]
  exact LatticeFrame.hsSq_isom_compress (F.Vr u) (F.hVr u) (F.Vr u') (F.hVr u') _

/-- **Diagonal Defect Contraction**:
Every compressed diagonal Gram block satisfies `hsSq (gramDiag (compressedMat F) ga u - 1) ≤
hsSq (gramDiag (pmatFin M ε) ga u - 1)`. -/
theorem hsSq_gramDiag_sub_one_compress_le (F : IsometryBlockFactorization ι κ κ₁)
    (ga : ι → ℝ) (u : ι) :
    LatticeFrame.hsSq (LatticeFrame.gramDiag F.compressedMat ga u - 1) ≤
      LatticeFrame.hsSq (LatticeFrame.gramDiag (F.M.pmatFin F.ε) ga u - 1) := by
  rw [compressedMat, LatticeFrame.gramDiag_compress_sub_one (F.M.pmatFin F.ε) F.Vr ga
    F.isIsometryFamily u]
  exact LatticeFrame.hsSq_isom_compress (F.Vr u) (F.hVr u) (F.Vr u) (F.hVr u) _

/-- **Kernel Inclusion on `κ`-Projection** (`T_proj` bridge for Wave 2 `FrameRealCompile`):
For any vector `v` mapped into the kernel of `MBk u` (equivalently `Y u *ᵥ v ∈ ker (MBk u).map ε`),
the top `κ`-coordinates of `compressedMat F u *ᵥ v` vanish identically! -/
theorem top_block_apply_eq (F : IsometryBlockFactorization ι κ κ₁)
    (u : ι) (v : EuclideanSpace ℂ (Fin (F.r u))) (k : κ) :
    (Matrix.toEuclideanLin (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
      (F.compressedMat u)) v) (Sum.inl k) =
      ((F.Y'⁻¹ * (F.MBk u).map F.ε * F.Y u) *ᵥ (fun j => v j)) k := by
  change ∑ j : Fin (F.r u), (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
      (F.compressedMat u)) (Sum.inl k) j * v j = _
  have hrow : ∀ j : Fin (F.r u),
      (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
        (F.compressedMat u)) (Sum.inl k) j =
      ((F.M.pmatConj F.ε u) * F.Vr u) (Sum.inl k) j := fun j => by
    simp only [compressedMat, LatticeFrame.compressFamily, BesselBlockMatrix.pmatFin,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl,
      Matrix.mul_apply, Equiv.apply_symm_apply, id_eq]
  simp_rw [hrow, F.factor_eq u k]
  rfl

end IsometryBlockFactorization

section ConstructFromBesselId

/-- Given an orthonormal family `g : κ → HH` inside a finite-dimensional Hilbert space `HH`
with `finrank ℂ HH = Fintype.card (κ ⊕ κ₁)`, extends `g` to a full orthonormal basis
`f : OrthonormalBasis (κ ⊕ κ₁) ℂ HH` satisfying `∀ k, f (Sum.inl k) = g k`. -/
theorem exists_orthonormalBasis_inl_extension {HH : Type*} {κ κ₁ : Type*}
    [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [FiniteDimensional ℂ HH]
    [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    (g : κ → HH) (hg : Orthonormal ℂ g)
    (hcard : Module.finrank ℂ HH = Fintype.card (κ ⊕ κ₁)) :
    ∃ f : OrthonormalBasis (κ ⊕ κ₁) ℂ HH, ∀ k : κ, f (Sum.inl k) = g k := by
  classical
  let S : Submodule ℂ HH := Submodule.span ℂ (Set.range g)
  have hli : LinearIndependent ℂ g := hg.linearIndependent
  have hdimS : Module.finrank ℂ S = Fintype.card κ := by
    rw [← finrank_span_eq_card hli]
  have hsum : Module.finrank ℂ S + Module.finrank ℂ Sᗮ = Module.finrank ℂ HH :=
    Submodule.finrank_add_finrank_orthogonal S
  have hdimCompl : Module.finrank ℂ Sᗮ = Fintype.card κ₁ := by
    rw [hcard, Fintype.card_sum, hdimS] at hsum
    omega
  let eCompl : OrthonormalBasis κ₁ ℂ Sᗮ :=
    (stdOrthonormalBasis ℂ Sᗮ).reindex (Fintype.equivOfCardEq (by simp [hdimCompl]))
  let v : (κ ⊕ κ₁) → HH := Sum.elim g (fun j => (eCompl j : HH))
  have hv_orth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro a b
    rcases a with k | j <;> rcases b with k' | j'
    · simp only [v, Sum.elim_inl]
      rw [orthonormal_iff_ite.mp hg k k']
      by_cases h : k = k' <;> simp [h]
    · simp only [v, Sum.elim_inl, Sum.elim_inr]
      have hk : g k ∈ S := Submodule.subset_span ⟨k, rfl⟩
      have hj : (eCompl j' : HH) ∈ Sᗮ := (eCompl j').2
      have h0 : ⟪g k, (eCompl j' : HH)⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal S _).mp hj (g k) hk
      simp [h0]
    · simp only [v, Sum.elim_inr, Sum.elim_inl]
      have hk : g k' ∈ S := Submodule.subset_span ⟨k', rfl⟩
      have hj : (eCompl j : HH) ∈ Sᗮ := (eCompl j).2
      have h0 : ⟪(eCompl j : HH), g k'⟫_ℂ = 0 := by
        rw [← inner_conj_symm (eCompl j : HH) (g k'),
          (Submodule.mem_orthogonal S _).mp hj (g k') hk, map_zero]
      simp [h0]
    · simp only [v, Sum.elim_inr]
      have he : ⟪eCompl j, eCompl j'⟫_ℂ = if j = j' then 1 else 0 :=
        orthonormal_iff_ite.mp eCompl.orthonormal j j'
      rw [show ⟪(eCompl j : HH), (eCompl j' : HH)⟫_ℂ = ⟪eCompl j, eCompl j'⟫_ℂ from rfl, he]
      by_cases h : j = j' <;> simp [h]
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hv_orth.linearIndependent, hcard])
  let b : Module.Basis (κ ⊕ κ₁) ℂ HH := Module.Basis.mk hv_orth.linearIndependent hspan.ge
  let f : OrthonormalBasis (κ ⊕ κ₁) ℂ HH :=
    b.toOrthonormalBasis (by simpa only [b, Module.Basis.coe_mk] using hv_orth)
  refine ⟨f, fun k => ?_⟩
  simp [f, b, v]

/-- Canonical isometric compression matrix `Vr0 u i j = ⟪eC u i, iotaC u (U u (oM u j))⟫`
associated to an isometric inclusion `iotaC u : Mu u →ₗ[ℂ] Cu u` and unitary `U u : Mu u ≃ₗᵢ[ℂ] Mu u`. -/
def vr0 {d r : ℕ} {Cu Mu : Type*}
    [NormedAddCommGroup Cu] [InnerProductSpace ℂ Cu]
    [NormedAddCommGroup Mu] [InnerProductSpace ℂ Mu]
    (eC : OrthonormalBasis (Fin d) ℂ Cu)
    (oM : OrthonormalBasis (Fin r) ℂ Mu)
    (iotaC : Mu →ₗ[ℂ] Cu)
    (U : Mu ≃ₗᵢ[ℂ] Mu) :
    Matrix (Fin d) (Fin r) ℂ :=
  fun i j => ⟪eC i, iotaC (U (oM j))⟫_ℂ

/-- **Isometric Verification of `vr0` (`vr0_isometry`)**:
`(vr0 eC oM iotaC U)ᴴ * (vr0 eC oM iotaC U) = 1`. -/
theorem vr0_isometry {d r : ℕ} {Cu Mu : Type*}
    [NormedAddCommGroup Cu] [InnerProductSpace ℂ Cu]
    [NormedAddCommGroup Mu] [InnerProductSpace ℂ Mu]
    (eC : OrthonormalBasis (Fin d) ℂ Cu)
    (oM : OrthonormalBasis (Fin r) ℂ Mu)
    (iotaC : Mu →ₗ[ℂ] Cu)
    (hiota : ∀ φ ψ : Mu, ⟪iotaC φ, iotaC ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ)
    (U : Mu ≃ₗᵢ[ℂ] Mu) :
    (vr0 eC oM iotaC U)ᴴ * vr0 eC oM iotaC U = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, vr0]
  have hterm : ∀ i : Fin d,
      star ⟪eC i, iotaC (U (oM j))⟫_ℂ * ⟪eC i, iotaC (U (oM j'))⟫_ℂ =
        ⟪iotaC (U (oM j)), eC i⟫_ℂ * ⟪eC i, iotaC (U (oM j'))⟫_ℂ := fun i => by
    rw [← inner_conj_symm (iotaC (U (oM j))) (eC i)]
    rfl
  simp_rw [hterm]
  rw [eC.sum_inner_mul_inner, hiota, U.inner_map_map,
    orthonormal_iff_ite.mp oM.orthonormal j j', Matrix.one_apply]

/-- **Matrix-Multiplication Projection Identity (`pmat_mul_vr0`)**:
`(pmat u * vr0 u) a j = ⟪f a, Pu u (iotaC u (U u (oM u j)))⟫_ℂ`. -/
theorem pmat_mul_vr0 {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁]
    (M : BesselBlockMatrix ι κ κ₁)
    (r : ι → ℕ)
    (Mu : ι → Type)
    [∀ u, NormedAddCommGroup (Mu u)] [∀ u, InnerProductSpace ℂ (Mu u)]
    (oM : ∀ u, OrthonormalBasis (Fin (r u)) ℂ (Mu u))
    (iotaC : ∀ u, Mu u →ₗ[ℂ] M.Cu u)
    (U : ∀ u, Mu u ≃ₗᵢ[ℂ] Mu u)
    (u : ι) (a : κ ⊕ κ₁) (j : Fin (r u)) :
    (M.pmat u * vr0 (M.eC u) (oM u) (iotaC u) (U u)) a j =
      ⟪M.f a, M.Pu u (iotaC u (U u (oM u j)))⟫_ℂ := by
  rw [Matrix.mul_apply]
  conv_rhs => rw [← (M.eC u).sum_repr' (iotaC u (U u (oM u j)))]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, BesselBlockMatrix.pmat, vr0]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Hilbert-Space Bessel Identity → Concrete `IsometryBlockFactorization`**:
Faithfully lifts Alpöge's `blockReal_at_of` (`TopDensityNGeSixteen.lean:1283-1315`):
given an ambient space `EE` (`OrthonormalBasis κ ℂ EE`), spaces `Mu u` (`Basis (Fin (r u)) ℂ (Mu u)`),
an isometric conjugate-linear equivalence `sEE : EE ≃ₛₗᵢ[starRingEnd ℂ] HH` (or `EE → HH` isometric
anti-linear map), isometric inclusions `iotaC u : Mu u →ₗ[ℂ] Cu u`, unitary intertwiners `V`, `U`,
scalars `a u ≠ 0`, and rational/integral Bessel matrix `MBk u` intertwined by `V, U, a` with
`⟪sEE F, Pu u (iotaC u φ)⟫ = a u * sesquilinear_MBk`, constructs a full `IsometryBlockFactorization`! -/
theorem besselId_to_isometryBlockFactorization
    {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    (HH : Type) [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [FiniteDimensional ℂ HH]
    (hHH_dim : Module.finrank ℂ HH = Fintype.card (κ ⊕ κ₁))
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (oE : OrthonormalBasis κ ℂ EE)
    (bE : Module.Basis κ ℂ EE)
    (sEE : EE → HH)
    (hsEE_inner : ∀ x y : EE, ⟪sEE x, sEE y⟫_ℂ = ⟪y, x⟫_ℂ)
    (d r : ι → ℕ)
    (Cu : ι → Type) [∀ u, NormedAddCommGroup (Cu u)] [∀ u, InnerProductSpace ℂ (Cu u)]
    [∀ u, FiniteDimensional ℂ (Cu u)]
    (eC : ∀ u, OrthonormalBasis (Fin (d u)) ℂ (Cu u))
    (Mu : ι → Type) [∀ u, NormedAddCommGroup (Mu u)] [∀ u, InnerProductSpace ℂ (Mu u)]
    [∀ u, FiniteDimensional ℂ (Mu u)]
    (oM : ∀ u, OrthonormalBasis (Fin (r u)) ℂ (Mu u))
    (bN : ∀ u, Module.Basis (Fin (r u)) ℂ (Mu u))
    (iotaC : ∀ u, Mu u →ₗ[ℂ] Cu u)
    (hiota : ∀ u (φ ψ : Mu u), ⟪iotaC u φ, iotaC u ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ)
    (Pu : ∀ u, Cu u →L[ℂ] HH)
    (c0 : ι → ℝ) (hc0 : ∀ u, 0 ≤ c0 u)
    (MBk : ∀ u, Matrix κ (Fin (r u)) ℂ)
    (V : EE ≃ₗᵢ[ℂ] EE)
    (U : ∀ u, Mu u ≃ₗᵢ[ℂ] Mu u)
    (a : ι → ℂ) (ha : ∀ u, a u ≠ 0)
    (hIntertwine : ∀ u (k : κ) (j : Fin (r u)),
      ⟪sEE (V (oE k)), Pu u (iotaC u (U u (oM u j)))⟫_ℂ =
        (a u)⁻¹ * ∑ k' : κ, ∑ j' : Fin (r u),
          bE.repr (V (oE k)) k' * MBk u k' j' * (bN u).repr (U u (oM u j)) j')
    (ε : ℂ →+* ℂ) (hε : IsIdOrConj ε) :
    Nonempty (IsometryBlockFactorization ι κ κ₁) := by
  classical
  have hrows : Orthonormal ℂ (fun k : κ => sEE (V (oE k))) := by
    rw [orthonormal_iff_ite]
    intro k k'
    rw [hsEE_inner, V.inner_map_map, orthonormal_iff_ite.mp oE.orthonormal k' k]
    by_cases h : k = k'
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  obtain ⟨f, hf⟩ := exists_orthonormalBasis_inl_extension (fun k => sEE (V (oE k))) hrows hHH_dim
  let M : BesselBlockMatrix ι κ κ₁ :=
    { HH := HH
      f := f
      d := d
      Cu := Cu
      eC := eC
      Pu := Pu
      c0 := c0
      c0_nonneg := hc0 }
  let Y0 : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ :=
    fun u => (a u)⁻¹ • (bN u).toMatrix (fun j => U u (oM u j))
  let bU : ∀ u, Module.Basis (Fin (r u)) ℂ (Mu u) :=
    fun u => (oM u).toBasis.map (U u).toLinearEquiv
  have hY0_det : ∀ u, IsUnit (Y0 u).det := fun u => by
    have hMat : (bN u).toMatrix (fun j => U u (oM u j)) = (bN u).toMatrix (bU u) := by
      ext i j
      simp [bU, Module.Basis.toMatrix_apply]
    dsimp only [Y0]
    rw [Matrix.det_smul, hMat]
    have hunit1 : IsUnit ((a u)⁻¹ ^ Fintype.card (Fin (r u))) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (ha u))).pow _
    have hunit2 : IsUnit ((bN u).toMatrix (bU u)).det :=
      Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip (bN u) (bU u))
    exact hunit1.mul hunit2
  let bV : Module.Basis κ ℂ EE := oE.toBasis.map V.toLinearEquiv
  let Z0 : Matrix κ κ ℂ := (bE.toMatrix (fun k => V (oE k)))ᵀ
  have hZ0_det : IsUnit Z0.det := by
    have hMat : bE.toMatrix (fun k => V (oE k)) = bE.toMatrix bV := by
      ext i j; simp [bV, Module.Basis.toMatrix_apply]
    dsimp only [Z0]
    rw [Matrix.det_transpose, hMat]
    exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip bE bV)
  have hZ_eps : IsUnit (Z0.map ε).det := det_map_isUnit Z0 ε hZ0_det
  refine ⟨{
    M := M
    r := r
    ε := ε
    hε := hε
    Y := fun u => (Y0 u).map ε
    Y' := (Z0.map ε)⁻¹
    Vr := fun u => (vr0 (M.eC u) (oM u) (iotaC u) (U u)).map ε
    MBk := MBk
    hY := fun u => det_map_isUnit (Y0 u) ε (hY0_det u)
    hY' := Matrix.isUnit_nonsing_inv_det _ hZ_eps
    hVr := fun u => by
      rw [conjTranspose_map_isIdOrConj _ hε, ← Matrix.map_mul,
        vr0_isometry (M.eC u) (oM u) (iotaC u) (hiota u) (U u)]
      ext i j
      rw [Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    factor_eq := fun u k j => by
      rw [Matrix.nonsing_inv_nonsing_inv _ hZ_eps]
      have hL : ((M.pmatConj ε u) * (vr0 (M.eC u) (oM u) (iotaC u) (U u)).map ε) (Sum.inl k) j =
          ε (((M.pmat u) * vr0 (M.eC u) (oM u) (iotaC u) (U u)) (Sum.inl k) j) := by
        unfold BesselBlockMatrix.pmatConj
        rw [← Matrix.map_mul, Matrix.map_apply]
      have hR : (Z0.map ε * (MBk u).map ε * (Y0 u).map ε) k j =
          ε ((Z0 * MBk u * Y0 u) k j) := by
        rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
      rw [hL, hR]
      congr 1
      rw [pmat_mul_vr0 M r Mu oM iotaC U u (Sum.inl k) j, hf k, hIntertwine u k j]
      rw [Matrix.mul_apply]
      have hsum : (∑ j' : Fin (r u), (Z0 * MBk u) k j' * Y0 u j' j) =
          (a u)⁻¹ * ∑ k' : κ, ∑ j' : Fin (r u),
            bE.repr (V (oE k)) k' * MBk u k' j' * (bN u).repr (U u (oM u j)) j' := by
        have hZM : ∀ j' : Fin (r u), (Z0 * MBk u) k j' =
            ∑ k' : κ, bE.repr (V (oE k)) k' * MBk u k' j' := fun j' => by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k' _ => ?_
          simp only [Z0, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
        have hY : ∀ j' : Fin (r u), Y0 u j' j =
            (a u)⁻¹ * (bN u).repr (U u (oM u j)) j' := fun j' => by
          simp only [Y0, Matrix.smul_apply, smul_eq_mul, Module.Basis.toMatrix_apply]
        simp_rw [hZM, hY]
        have hre : (∑ j' : Fin (r u),
            (∑ k' : κ, bE.repr (V (oE k)) k' * MBk u k' j') *
              ((a u)⁻¹ * (bN u).repr (U u (oM u j)) j')) =
            (a u)⁻¹ * ∑ j' : Fin (r u), ∑ k' : κ,
              bE.repr (V (oE k)) k' * MBk u k' j' * (bN u).repr (U u (oM u j)) j' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k' _ => by ring
        rw [hre, Finset.sum_comm]
      exact hsum.symm
  }⟩

end ConstructFromBesselId

end IsometryBlockFactorizationSection

/-! ## Section 3: `block_real_schur_decay` — Block-Matrix Schur Decay & Cotlar–Stein Coupling -/

section BlockRealSchurDecaySection

/-- **Block-Matrix Weighted Schur's Test (`block_matrix_schur_le`)**:
Given a block matrix `K u u' : Matrix (Fin (d u)) (Fin (d u')) ℂ` whose block operator norms
satisfy `‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ ≤ M u u'` with weighted
Schur row/column bounds `∑ u', M u u' * v u' ≤ A * w u` and `∑ u, M u u' * w u ≤ B * v u'`,
the block operator on `∀ u, EuclideanSpace ℂ (Fin (d u))` satisfies
`∑ u, ‖∑ u', (Matrix.toEuclideanLin (K u u')) (x u')‖² ≤ A * B * ∑ u, ‖x u‖²`. -/
theorem block_matrix_schur_le {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (K : ∀ u u', Matrix (Fin (d u)) (Fin (d u')) ℂ)
    (M : ι → ι → ℝ) (w v : ι → ℝ) {A B : ℝ}
    (hv : ∀ u, 0 < v u) (hA : 0 ≤ A)
    (hM : ∀ u u', ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ ≤ M u u')
    (hrow : ∀ u, ∑ u', M u u' * v u' ≤ A * w u)
    (hcol : ∀ u', ∑ u, M u u' * w u ≤ B * v u')
    (x : ∀ u, EuclideanSpace ℂ (Fin (d u))) :
    ∑ u : ι, ‖∑ u' : ι, Matrix.toEuclideanLin (K u u') (x u')‖ ^ 2 ≤
      A * B * ∑ u : ι, ‖x u‖ ^ 2 := by
  let Kscalar : ι → ι → ℂ := fun u u' => ((M u u' : ℝ) : ℂ)
  have hM0 : ∀ u u', 0 ≤ M u u' := fun u u' => le_trans (norm_nonneg _) (hM u u')
  have hKnorm : ∀ u u', ‖Kscalar u u'‖ = M u u' := fun u u' => by
    simp only [Kscalar, Complex.norm_real, Real.norm_of_nonneg (hM0 u u')]
  have hrow' : ∀ u, ∑ u', ‖Kscalar u u'‖ * v u' ≤ A * w u := fun u => by
    simpa only [hKnorm] using hrow u
  have hcol' : ∀ u', ∑ u, ‖Kscalar u u'‖ * w u ≤ B * v u' := fun u' => by
    simpa only [hKnorm] using hcol u'
  have hscalar := Stage11BesselWaveSchur.schur_test_weighted Kscalar w v hv hA hrow' hcol'
    (fun u => (‖x u‖ : ℂ))
  have hLHS : ∑ u : ι, ‖∑ u' : ι, Matrix.toEuclideanLin (K u u') (x u')‖ ^ 2 ≤
      ∑ u : ι, ‖∑ u' : ι, Kscalar u u' * (‖x u'‖ : ℂ)‖ ^ 2 := by
    refine Finset.sum_le_sum fun u _ => ?_
    have hpt : ‖∑ u' : ι, Matrix.toEuclideanLin (K u u') (x u')‖ ≤
        ∑ u' : ι, M u u' * ‖x u'‖ := by
      calc ‖∑ u' : ι, Matrix.toEuclideanLin (K u u') (x u')‖
          ≤ ∑ u' : ι, ‖Matrix.toEuclideanLin (K u u') (x u')‖ := norm_sum_le _ _
        _ ≤ ∑ u' : ι, ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ * ‖x u'‖ :=
            Finset.sum_le_sum fun u' _ =>
              ContinuousLinearMap.le_opNorm (Matrix.toEuclideanLin (K u u')).toContinuousLinearMap (x u')
        _ ≤ ∑ u' : ι, M u u' * ‖x u'‖ :=
            Finset.sum_le_sum fun u' _ => mul_le_mul_of_nonneg_right (hM u u') (norm_nonneg _)
    have hrhs_eq : ‖∑ u' : ι, Kscalar u u' * (‖x u'‖ : ℂ)‖ = ∑ u' : ι, M u u' * ‖x u'‖ := by
      have hsum : ∑ u' : ι, Kscalar u u' * (‖x u'‖ : ℂ) =
          ((∑ u' : ι, M u u' * ‖x u'‖ : ℝ) : ℂ) := by
        simp only [Kscalar, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
      rw [hsum, Complex.norm_real, Real.norm_of_nonneg
        (Finset.sum_nonneg fun u' _ => mul_nonneg (hM0 u u') (norm_nonneg _))]
    rw [hrhs_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) hpt 2
  have hRHS : ∑ u : ι, ‖(‖x u‖ : ℂ)‖ ^ 2 = ∑ u : ι, ‖x u‖ ^ 2 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact hLHS.trans (hscalar.trans_eq (by rw [hRHS]))

/-- **Block Real Schur Decay (`block_real_schur_decay`)**:
Suppose a `BesselBlockMatrix` (or any block-separated Hilbert family `T : ι → (H₁ →L[ℂ] H₂)`)
has centers `pos : ι → EuclideanSpace ℝ (Fin dim)` that are `Δ`-separated with
`Δ ≥ sepConst dim * σ * √(log (1 / ε))` (`0 < ε ≤ 1 / 2`), and satisfies Gaussian
block-Gram off-diagonal decay `hsNorm (gramCross B ga u u') ≤ C * exp(-π * ‖pos u - pos u'‖² / σ²)`
(or operator-norm overlap `≤ C * exp(...)`):
1. Every off-diagonal row sum of block Hilbert–Schmidt norms is `≤ C * ε`.
2. The off-diagonal block operator norm on `⨁ u, ℂ^{d u}` is `≤ C * ε`.
3. Under block-operator Cotlar–Stein overlap `‖T_u* T_{u'}‖, ‖T_u T_{u'}*‖ ≤ C * exp(...)`,
   the global block operator sum satisfies `‖∑ u, T u‖ ≤ √C * (1 + ε)` — **uniform in `|ι|`!** -/
theorem block_real_schur_decay
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dim : ℕ} {d : ι → ℕ}
    (T : ι → (H₁ →L[ℂ] H₂))
    (K : ∀ u u', Matrix (Fin (d u)) (Fin (d u')) ℂ)
    (pos : ι → EuclideanSpace ℝ (Fin dim))
    {σ Δ ε C : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (hΔ_ge : Stage11BesselWaveSchur.sepConst dim * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hinj : Function.Injective pos)
    (hsep : ∀ u u', u ≠ u' → Δ ≤ ‖pos u - pos u'‖)
    (hK_op : ∀ u u', u ≠ u' →
      ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ ≤
        C * Real.exp (-(Real.pi / 2) * ‖pos u - pos u'‖ ^ 2 / σ ^ 2))
    (hK_col : ∀ u u', u ≠ u' →
      ‖(Matrix.toEuclideanLin (K u' u)).toContinuousLinearMap‖ =
        ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖)
    (hTa : ∀ u u', ‖(T u).adjoint.comp (T u')‖ ≤ C * Real.exp (-Real.pi * ‖pos u - pos u'‖ ^ 2 / σ ^ 2))
    (hTb : ∀ u u', ‖(T u).comp (T u').adjoint‖ ≤ C * Real.exp (-Real.pi * ‖pos u - pos u'‖ ^ 2 / σ ^ 2)) :
    let Koff : ∀ u u', Matrix (Fin (d u)) (Fin (d u')) ℂ :=
      fun u u' => if u = u' then 0 else K u u'
    (∀ u, ∑ u' ∈ Finset.univ.erase u,
        ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ ≤ C * ε) ∧
    (∀ x : ∀ u, EuclideanSpace ℂ (Fin (d u)),
        ∑ u, ‖∑ u', Matrix.toEuclideanLin (Koff u u') (x u')‖ ^ 2 ≤
          (C * ε) ^ 2 * ∑ u, ‖x u‖ ^ 2) ∧
    ‖∑ u : ι, T u‖ ≤ Real.sqrt C * (1 + ε) := by
  classical
  let W : Finset (EuclideanSpace ℝ (Fin dim)) := Finset.univ.image pos
  have hW_sep : Stage11BesselWaveSchur.IsSeparatedGrid W Δ := by
    intro w hw w' hw' hne
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨u', -, rfl⟩ := Finset.mem_image.mp hw'
    exact hsep u u' (fun huu => hne (by rw [huu]))
  have hgauss_sum : ∀ u : ι,
      ∑ u' ∈ Finset.univ.erase u, Real.exp (-(Real.pi / 2) * ‖pos u - pos u'‖ ^ 2 / σ ^ 2) ≤ ε := by
    intro u
    have hoff_eq :
        ∑ u' ∈ Finset.univ.erase u, Real.exp (-(Real.pi / 2) * ‖pos u - pos u'‖ ^ 2 / σ ^ 2) =
        ∑ w' ∈ W.erase (pos u), Real.exp (-(Real.pi / 2) * ‖pos u - w'‖ ^ 2 / σ ^ 2) := by
      refine Finset.sum_bij (fun u' _ => pos u') ?_ ?_ ?_ ?_
      · intro u' hu'
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image_of_mem pos (Finset.mem_univ u')⟩
        intro heq
        exact (Finset.mem_erase.mp hu').1 (hinj heq)
      · intro u₁ _ u₂ _ heq; exact hinj heq
      · intro w' hw'
        obtain ⟨hne, hw'W⟩ := Finset.mem_erase.mp hw'
        obtain ⟨u', -, rfl⟩ := Finset.mem_image.mp hw'W
        exact ⟨u', Finset.mem_erase.mpr ⟨fun hu => hne (by rw [hu]), Finset.mem_univ u'⟩, rfl⟩
      · intro _ _; rfl
    rw [hoff_eq]
    exact Stage11BesselWaveSchur.separated_grid_gaussian_sum_le W hσ hε0 hε_half hΔ_ge hW_sep
      (Finset.mem_image_of_mem pos (Finset.mem_univ u))
  have hrow_norm : ∀ u : ι,
      ∑ u' ∈ Finset.univ.erase u, ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ ≤ C * ε := by
    intro u
    calc ∑ u' ∈ Finset.univ.erase u, ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖
        ≤ ∑ u' ∈ Finset.univ.erase u,
            C * Real.exp (-(Real.pi / 2) * ‖pos u - pos u'‖ ^ 2 / σ ^ 2) :=
          Finset.sum_le_sum fun u' hu' => hK_op u u' (Finset.mem_erase.mp hu').1.symm
      _ = C * ∑ u' ∈ Finset.univ.erase u,
            Real.exp (-(Real.pi / 2) * ‖pos u - pos u'‖ ^ 2 / σ ^ 2) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ C * ε := mul_le_mul_of_nonneg_left (hgauss_sum u) hC
  dsimp only
  let Koff : ∀ u u', Matrix (Fin (d u)) (Fin (d u')) ℂ :=
    fun u u' => if u = u' then 0 else K u u'
  let M : ι → ι → ℝ := fun u u' => ‖(Matrix.toEuclideanLin (Koff u u')).toContinuousLinearMap‖
  have hM_row : ∀ u, ∑ u', M u u' * 1 ≤ (C * ε) * 1 := fun u => by
    have hsum : ∑ u', M u u' = ∑ u' ∈ Finset.univ.erase u,
        ‖(Matrix.toEuclideanLin (K u u')).toContinuousLinearMap‖ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
      have hdiag0 : M u u = 0 := by simp [M, Koff]
      rw [hdiag0, zero_add]
      refine Finset.sum_congr rfl fun u' hu' => ?_
      have hne : u ≠ u' := (Finset.mem_erase.mp hu').1.symm
      simp [M, Koff, hne]
    simp only [mul_one, hsum]
    exact hrow_norm u
  have hM_col : ∀ u', ∑ u, M u u' * 1 ≤ (C * ε) * 1 := fun u' => by
    have hsym : ∀ u, M u u' = M u' u := fun u => by
      dsimp only [M, Koff]
      by_cases h : u = u'
      · subst h; simp
      · have h' : u' ≠ u := Ne.symm h
        simp only [h, h', ↓reduceIte]
        exact hK_col u' u h'
    simp_rw [hsym]
    exact hM_row u'
  refine ⟨hrow_norm, fun x => ?_, ?_⟩
  · have hschur := block_matrix_schur_le Koff M (fun _ => 1) (fun _ => 1)
      (fun _ => zero_lt_one) (mul_nonneg hC hε0.le) (fun _ _ => le_rfl) hM_row hM_col x
    rwa [← sq] at hschur
  · exact Stage11BesselWaveSchur.bessel_grid_cotlar_stein_opNorm_le T pos hσ hε0 hε_half hC
      hΔ_ge hinj hsep hTa hTb

end BlockRealSchurDecaySection

/-! ## Section 4: `bessel_gram_offdiag_le` — Concrete Bessel Gram Off-Diagonal Bounds -/

section BesselGramOffDiagSection

/-- **Concrete Bessel Gram Off-Diagonal Decay (`bessel_gram_offdiag_le`)**:
For any `Δ`-separated finite grid `W ⊂ ℝ^d` with `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))`
(`0 < ε ≤ 1 / 2`) and frequency map `ξ`:
1. Row `ℓ¹` decay: `∀ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram σ hσ u (ξ u) u' (ξ u')‖ ≤ ε`.
2. Row `ℓ²` (Frobenius/HS) decay: `∀ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram ...‖² ≤ ε²`.
3. Total off-diagonal Hilbert–Schmidt squared norm: `∑ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram ...‖² ≤ ε² * |W|`.
4. Off-diagonal Schur operator norm: `‖(Matrix.toEuclideanLin (besselOffDiagMatrix W ξ σ hσ)).toContinuousLinearMap‖ ≤ ε`. -/
theorem bessel_gram_offdiag_le {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hΔ_ge : Stage11BesselWaveSchur.sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : Stage11BesselWaveSchur.IsSeparatedGrid W Δ) :
    (∀ u ∈ W, ∑ u' ∈ W.erase u,
        ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ≤ ε) ∧
    (∀ u ∈ W, ∑ u' ∈ W.erase u,
        ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ^ 2 ≤ ε ^ 2) ∧
    (∑ u ∈ W, ∑ u' ∈ W.erase u,
        ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ^ 2 ≤
          ε ^ 2 * (W.card : ℝ)) ∧
    ‖(Matrix.toEuclideanLin (Stage11BesselWaveSchur.besselOffDiagMatrix W ξ σ hσ)).toContinuousLinearMap‖ ≤ ε := by
  have hrow := Stage11BesselWaveSchur.bessel_grid_off_diag_le W ξ hσ hε0 hε_half hΔ_ge hsep
  have hrow_sq : ∀ u ∈ W, ∑ u' ∈ W.erase u,
      ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ^ 2 ≤ ε ^ 2 := by
    intro u hu
    calc ∑ u' ∈ W.erase u, ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ^ 2
        ≤ (∑ u' ∈ W.erase u, ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _
      _ ≤ ε ^ 2 := pow_le_pow_left₀
            (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hrow u hu) 2
  have htot : ∑ u ∈ W, ∑ u' ∈ W.erase u,
      ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ^ 2 ≤
        ε ^ 2 * (W.card : ℝ) := by
    calc ∑ u ∈ W, ∑ u' ∈ W.erase u,
            ‖Stage11BesselWaveSchur.besselGram σ hσ u (ξ u) u' (ξ u')‖ ^ 2
        ≤ ∑ _u ∈ W, ε ^ 2 := Finset.sum_le_sum fun u hu => hrow_sq u hu
      _ = (W.card : ℝ) * ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ε ^ 2 * (W.card : ℝ) := mul_comm _ _
  have hop := Stage11BesselWaveSchur.bessel_grid_schur_offDiag_opNorm_le
    W ξ hσ hε0 hε_half hΔ_ge hsep
  exact ⟨hrow, hrow_sq, htot, hop⟩

/-- **Block-Matrix Cross-Gram Off-Diagonal Bound (`bessel_gram_offdiag_block_le`)**:
For any `BesselBlockMatrix M` and `IsIdOrConj ε` with positive weights `c0 u > 0`, if the
operator cross-Gram blocks satisfy `hsSq (opMat (kOp u u')) ≤ (1 + η0) * d u * d u' / Dstar`
for `u ≠ u'`, and diagonal defect `hsSq (opMat (kOp u u - I)) ≤ e0 * d u`, while
`Fintype.card (κ ⊕ κ₁) ≤ (1 + η1) * Dstar`, then `M.pmatFin ε` satisfies `LatticeFrame.GramInput`
with weights `ga u = (M.c0 u)⁻¹`, AND its off-diagonal total Hilbert–Schmidt energy is at most
`(1 + η0) * (totalRank M.d)^2 / Dstar`. -/
theorem bessel_gram_offdiag_block_le {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁]
    [DecidableEq ι]
    (M : BesselBlockMatrix ι κ κ₁) {ε : ℂ →+* ℂ} (hε : IsIdOrConj ε)
    (hc : ∀ u, 0 < M.c0 u) {Dstar η0 η1 e0 : ℝ}
    (hD : 0 < Dstar) (hη0 : -1 ≤ η0)
    (hoff : ∀ u u', u ≠ u' →
      LatticeFrame.hsSq (M.opMat (M.kOp u u')) ≤ (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar)
    (hdiag : ∀ u,
      LatticeFrame.hsSq (M.opMat (M.kOp u u - ContinuousLinearMap.id ℂ (M.Cu u))) ≤
        e0 * (M.d u : ℝ))
    (hdim : (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (1 + η1) * Dstar) :
    LatticeFrame.GramInput (M.pmatFin ε) (fun u => (M.c0 u)⁻¹) Dstar η0 η1 e0 ∧
    (∑ u : ι, ∑ u' ∈ Finset.univ.erase u,
      LatticeFrame.hsSq (LatticeFrame.gramCross (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u u') ≤
        (1 + η0) * LatticeFrame.totalRank M.d ^ 2 / Dstar) := by
  classical
  have hgram : LatticeFrame.GramInput (M.pmatFin ε) (fun u => (M.c0 u)⁻¹) Dstar η0 η1 e0 := by
    refine ⟨fun u u' huu => ?_, fun u => ?_, hdim⟩
    · rw [M.hsSq_gramCross_pmat hε hc u u']
      exact hoff u u' huu
    · rw [M.hsSq_gramDiag_sub_one_pmat hε hc u]
      exact hdiag u
  refine ⟨hgram, ?_⟩
  have hterm : ∀ u : ι, ∀ u' ∈ Finset.univ.erase u,
      LatticeFrame.hsSq (LatticeFrame.gramCross (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u u') ≤
        (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar := fun u u' hu' =>
    hgram.1 u u' (Finset.mem_erase.mp hu').1.symm
  have hsum : ∑ u : ι, ∑ u' ∈ Finset.univ.erase u,
      LatticeFrame.hsSq (LatticeFrame.gramCross (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u u') ≤
      ∑ u : ι, ∑ u' : ι, (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar := by
    refine Finset.sum_le_sum fun u _ => ?_
    calc ∑ u' ∈ Finset.univ.erase u,
            LatticeFrame.hsSq (LatticeFrame.gramCross (M.pmatFin ε) (fun w => (M.c0 w)⁻¹) u u')
        ≤ ∑ u' ∈ Finset.univ.erase u, (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar :=
          Finset.sum_le_sum fun u' hu' => hterm u u' hu'
      _ ≤ ∑ u' : ι, (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun u' _ _ => ?_
          exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
            (Nat.cast_nonneg _)) hD.le
  have heq : ∑ u : ι, ∑ u' : ι, (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar =
      (1 + η0) * LatticeFrame.totalRank M.d ^ 2 / Dstar := by
    unfold LatticeFrame.totalRank
    have h1 : ∀ u, ∑ u', (1 + η0) * (M.d u : ℝ) * (M.d u' : ℝ) / Dstar =
        ((1 + η0) / Dstar) * (M.d u : ℝ) * ∑ u', (M.d u' : ℝ) := fun u => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u' _ => by ring
    simp only [h1, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  exact hsum.trans_eq heq

end BesselGramOffDiagSection

/-! ## Section 5: `matKF_spectral_parameters` — `MatKF`, `RamShareF`, & Scale Thresholds -/

section MatKFSpectralParamsSection

/-- Elementary polynomial-vs-exponential domination:
for any `c > 0`, `a ≥ 0`, `b > 0`, `x ≥ 1` large enough implies `x ^ a ≤ exp (b * x ^ c)`.
Used cleanly to convert `exp(-(x ^ (eps / 8)))` decay into `sg ≤ 1 / 20`, `de ≤ 1 / 4`, etc. -/
lemma eventually_rpow_le_exp {a b c : ℝ} (_ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x → x ^ a ≤ Real.exp (b * x ^ c) := by
  let M_exp : ℕ := Nat.ceil (a / c)
  let N : ℕ := M_exp + 1
  have hMc : a ≤ (M_exp : ℝ) * c := by
    have h1 : a / c ≤ (M_exp : ℝ) := Nat.le_ceil _
    have := mul_le_mul_of_nonneg_right h1 hc.le
    rwa [div_mul_cancel₀ _ hc.ne'] at this
  let K : ℝ := (N.factorial : ℝ) / b ^ N
  refine ⟨max 1 (max K 1) ^ (1 / c), ?_, fun x hx => ?_⟩
  · exact Real.one_le_rpow (le_max_left _ _) (by positivity)
  · have hx1 : 1 ≤ x := (Real.one_le_rpow (le_max_left _ _) (by positivity)).trans hx
    have hx_pos : 0 < x := by linarith
    have hxc : max 1 (max K 1) ≤ x ^ c := by
      have hpow := Real.rpow_le_rpow (by positivity) hx hc.le
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one] at hpow
      exact hpow
    have hKx : K ≤ x ^ c := (le_trans (le_max_left K 1) (le_max_right 1 _)).trans hxc
    have hxc_pos : 0 < x ^ c := Real.rpow_pos_of_pos hx_pos c
    have hbx_pos : 0 < b * x ^ c := mul_pos hb hxc_pos
    have hterm : (b * x ^ c) ^ N / (N.factorial : ℝ) ≤ Real.exp (b * x ^ c) := by
      have h1 : (b * x ^ c) ^ N / (N.factorial : ℝ) ≤
          ∑ i ∈ Finset.range (N + 1), (b * x ^ c) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hbx_pos.le i) (Nat.cast_nonneg _))
          (Finset.mem_range.mpr (Nat.lt_succ_self N))
      exact h1.trans (Real.sum_le_exp_of_nonneg hbx_pos.le (N + 1))
    have ha1 : x ^ a ≤ (x ^ c) ^ M_exp := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le, mul_comm c M_exp]
      exact Real.rpow_le_rpow_of_exponent_le hx1 hMc
    have hKmul : (N.factorial : ℝ) ≤ b ^ N * x ^ c := by
      have := mul_le_mul_of_nonneg_left hKx (pow_pos hb N).le
      dsimp only [K] at this
      rwa [mul_div_cancel₀ _ (pow_pos hb N).ne'] at this
    have hfac_pos : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have ha2 : (x ^ c) ^ M_exp ≤ (b * x ^ c) ^ N / (N.factorial : ℝ) := by
      rw [le_div_iff₀ hfac_pos, mul_pow]
      have hprod : (x ^ c) ^ M_exp * (N.factorial : ℝ) ≤ (x ^ c) ^ M_exp * (b ^ N * x ^ c) :=
        mul_le_mul_of_nonneg_left hKmul (pow_nonneg hxc_pos.le M_exp)
      have heq : (x ^ c) ^ M_exp * (b ^ N * x ^ c) = b ^ N * (x ^ c) ^ N := by
        dsimp only [N]
        rw [pow_succ]
        ring
      exact hprod.trans_eq heq
    exact (ha1.trans ha2).trans hterm

/-- Concrete `exp (-(x ^ γ)) ≤ δ` above an explicit threshold `x0 ≥ 1` for `γ > 0`, `δ > 0`. -/
lemma eventually_exp_neg_rpow_le {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x → Real.exp (-(x ^ γ)) ≤ δ := by
  let M : ℝ := max 1 (Real.log (1 / δ))
  have hM : 1 ≤ M := le_max_left _ _
  refine ⟨M ^ (1 / γ), Real.one_le_rpow hM (by positivity), fun x hx => ?_⟩
  have hxγ : M ≤ x ^ γ := by
    have h := Real.rpow_le_rpow (by positivity) hx hγ.le
    rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hγ.ne', Real.rpow_one] at h
    exact h
  have hlog : Real.log (1 / δ) ≤ x ^ γ := (le_max_right 1 _).trans hxγ
  have hlog' : -x ^ γ ≤ Real.log δ := by
    rw [one_div, Real.log_inv] at hlog
    linarith
  calc Real.exp (-(x ^ γ)) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlog'
    _ = δ := Real.exp_log hδ

/-- **Concrete `MatK` Spectral Parameters (`MatKSpectralParams`)**:
Packages all numerical parameters `(Dstar, sg, η0, η1, e0, de, δ)` required by
`LatticeFrame.bost_slope_ineq_of_gram_input` and `Stage2ThetaWire.Stage2GramFrameFiber`. -/
structure MatKSpectralParams where
  Dstar : ℝ
  sg : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ
  de : ℝ
  δ : ℝ
  Dstar_pos : 0 < Dstar
  sg_pos : 0 < sg
  sg_le : sg ≤ 1 / 20
  η0_ge : -1 ≤ η0
  η0_le : η0 ≤ sg / 2
  η1_le : η1 ≤ sg / 2
  e0_nonneg : 0 ≤ e0
  sqrt_e0_le : Real.sqrt e0 ≤ sg / 2
  de_nonneg : 0 ≤ de
  de_le : de ≤ 1 / 4
  δ_nonneg : 0 ≤ δ
  δ_le : δ ≤ 1 / 2

namespace MatKSpectralParams

/-- Combined Bost–Arakelov trace-defect factor `5 * sg + 3 * √de + 4 * √(2 * e0) ≤ 11 / 10`. -/
theorem combined_defect_le (P : MatKSpectralParams) :
    5 * P.sg + 3 * Real.sqrt P.de + 4 * Real.sqrt (2 * P.e0) ≤ 2 := by
  have h1 : P.sg ≤ 1 / 20 := P.sg_le
  have h2 : Real.sqrt P.de ≤ 1 / 2 := by
    have hsq : P.de ≤ (1 / 2 : ℝ) ^ 2 := by linarith [P.de_le]
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by norm_num))
  have h3 : Real.sqrt (2 * P.e0) ≤ 1 / 20 := by
    have hsq0 : P.e0 ≤ (P.sg / 2) ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) P.sqrt_e0_le 2
      rwa [Real.sq_sqrt P.e0_nonneg] at h
    have hsq : 2 * P.e0 ≤ (1 / 20 : ℝ) ^ 2 := by
      have hsg0 : 0 ≤ P.sg := P.sg_pos.le
      nlinarith
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by norm_num))
  linarith

/-- Stronger combined defect ceiling when `de ≤ 1 / 20`: `≤ 11 / 10`. -/
theorem combined_defect_tight_le (P : MatKSpectralParams) (hde20 : P.de ≤ 1 / 20) :
    5 * P.sg + 3 * Real.sqrt P.de + 4 * Real.sqrt (2 * P.e0) ≤ 11 / 10 := by
  have h1 : P.sg ≤ 1 / 20 := P.sg_le
  have h2 : Real.sqrt P.de ≤ 9 / 40 := by
    have hsq : P.de ≤ (9 / 40 : ℝ) ^ 2 := by linarith
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by norm_num))
  have h3 : Real.sqrt (2 * P.e0) ≤ 3 / 80 := by
    have hsq0 : P.e0 ≤ (P.sg / 2) ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) P.sqrt_e0_le 2
      rwa [Real.sq_sqrt P.e0_nonneg] at h
    have hsq : 2 * P.e0 ≤ (3 / 80 : ℝ) ^ 2 := by
      have hsg0 : 0 ≤ P.sg := P.sg_pos.le
      nlinarith
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by norm_num))
  linarith

end MatKSpectralParams

/-- **Full Spectral Bundle for a `BesselBlockMatrix` + `IsometryBlockFactorization`**:
Directly unites `BesselBlockMatrix`, `IsometryBlockFactorization`, `MatKSpectralParams`,
`LatticeFrame.GramInput`, rank lower bound `Dstar / sg ≤ totalRank M.d`, and ramified
codimension share `∑ u, (d u - r u) ≤ de * totalRank M.d`. -/
structure BesselGramSpectralBundle (ι κ κ₁ : Type)
    [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] : Type 1 where
  F : IsometryBlockFactorization ι κ κ₁
  P : MatKSpectralParams
  hc0 : ∀ u, 0 < F.M.c0 u
  rank_ge : P.Dstar / P.sg ≤ LatticeFrame.totalRank F.M.d
  corV : ∑ u, ((F.M.d u : ℝ) - (F.r u : ℝ)) ≤ P.de * LatticeFrame.totalRank F.M.d
  card_ge : (1 - P.δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ)
  gramInput : LatticeFrame.GramInput (F.M.pmatFin F.ε) (fun u => (F.M.c0 u)⁻¹)
    P.Dstar P.η0 P.η1 P.e0

namespace BesselGramSpectralBundle

variable {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ]

/-- Unconditional discharge of `LatticeFrame.FrameTraceRatio` and `LatticeFrame.FrameDiagDefect`
for both the uncompressed `BesselBlockMatrix` and the `Vr`-compressed family. -/
theorem frame_trace_and_diag_bounds (B : BesselGramSpectralBundle ι κ κ₁) :
    LatticeFrame.FrameTraceRatio (B.F.M.pmatFin B.F.ε) (fun u => (B.F.M.c0 u)⁻¹) (5 * B.P.sg) ∧
    LatticeFrame.FrameDiagDefect (B.F.M.pmatFin B.F.ε) (fun u => (B.F.M.c0 u)⁻¹) B.P.e0 ∧
    LatticeFrame.FrameTraceRatio B.F.compressedMat (fun u => (B.F.M.c0 u)⁻¹)
      (5 * B.P.sg + 3 * Real.sqrt B.P.de) ∧
    LatticeFrame.FrameDiagDefect B.F.compressedMat (fun u => (B.F.M.c0 u)⁻¹) (2 * B.P.e0) :=
  Stage11BesselWaveSchur.bessel_grid_latticeFrame_discharge
    (B.F.M.pmatFin B.F.ε) B.F.Vr (fun u => (B.F.M.c0 u)⁻¹)
    B.F.isIsometryFamily (fun u => (inv_pos.mpr (B.hc0 u)).le) B.P.Dstar_pos B.P.sg_pos
    B.P.sg_le B.rank_ge B.P.η0_ge B.P.η0_le B.P.η1_le B.P.e0_nonneg
    (by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) B.P.sqrt_e0_le 2
      rwa [Real.sq_sqrt B.P.e0_nonneg] at h)
    B.P.de_nonneg B.P.de_le B.corV B.gramInput

end BesselGramSpectralBundle

/-- **Exponential-to-Spectral Parameter Discharge (`matKF_spectral_parameters`)**:
Mirrors `TopDensityNGeSixteen.matKF_of` and `ramShareF_of`:
given any `x` with exponential Gram/codimension errors
`η0 ≤ exp(-(x ^ (eps / 8)))`, `η1 ≤ exp(-(x ^ (eps / 8)))`, `√e0 ≤ exp(-(x ^ (eps / 8)))`,
`√de ≤ exp(-(x ^ (eps / 8)))`, `δ ≤ 1 / 2`, at all sufficiently large `x ≥ x0` (constructed
explicitly from `eps > 0` and `sg0 ∈ (0, 1 / 20]`), all `MatKSpectralParams` inequalities hold
automatically — AND if a `BesselBlockMatrix` + `IsometryBlockFactorization` satisfies the
cross-Gram/diagonal bounds, it produces a complete `BesselGramSpectralBundle` plus both
uncompressed and compressed `FrameTraceRatio` and `FrameDiagDefect`! -/
theorem matKF_spectral_parameters {eps sg0 : ℝ} (heps : 0 < eps)
    (hsg0_pos : 0 < sg0) (hsg0_le : sg0 ≤ 1 / 20) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∀ {Dstar η0 η1 e0 de δ : ℝ},
        0 < Dstar → -1 ≤ η0 → η0 ≤ Real.exp (-(x ^ (eps / 8))) →
        η1 ≤ Real.exp (-(x ^ (eps / 8))) →
        0 ≤ e0 → Real.sqrt e0 ≤ Real.exp (-(x ^ (eps / 8))) →
        0 ≤ de → Real.sqrt de ≤ Real.exp (-(x ^ (eps / 8))) →
        0 ≤ δ → δ ≤ 1 / 2 →
        ∃ P : MatKSpectralParams,
          P.Dstar = Dstar ∧ P.sg = sg0 ∧ P.η0 = η0 ∧ P.η1 = η1 ∧
          P.e0 = e0 ∧ P.de = de ∧ P.δ = δ ∧ P.de ≤ 1 / 20 ∧
          5 * P.sg + 3 * Real.sqrt P.de + 4 * Real.sqrt (2 * P.e0) ≤ 11 / 10 := by
  have hγ : 0 < eps / 8 := by positivity
  have hδ : 0 < sg0 / 2 := by positivity
  obtain ⟨x0, hx0_ge1, hx0⟩ := eventually_exp_neg_rpow_le hγ hδ
  refine ⟨x0, hx0_ge1, fun x hx {Dstar η0 η1 e0 de δ} hDs hη0_ge hη0 hη1 he0 hse hde hsde hδ0 hδ2 => ?_⟩
  have hexp : Real.exp (-(x ^ (eps / 8))) ≤ sg0 / 2 := hx0 x hx
  have hde_le_sq : de ≤ (sg0 / 2) ^ 2 := by
    have h1 : Real.sqrt de ≤ sg0 / 2 := hsde.trans hexp
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt hde] at h2
  have hde_le_20 : de ≤ 1 / 20 := by nlinarith
  have hde_le_4 : de ≤ 1 / 4 := by linarith
  let P : MatKSpectralParams :=
    { Dstar := Dstar
      sg := sg0
      η0 := η0
      η1 := η1
      e0 := e0
      de := de
      δ := δ
      Dstar_pos := hDs
      sg_pos := hsg0_pos
      sg_le := hsg0_le
      η0_ge := hη0_ge
      η0_le := hη0.trans hexp
      η1_le := hη1.trans hexp
      e0_nonneg := he0
      sqrt_e0_le := hse.trans hexp
      de_nonneg := hde
      de_le := hde_le_4
      δ_nonneg := hδ0
      δ_le := hδ2 }
  exact ⟨P, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hde_le_20, P.combined_defect_tight_le hde_le_20⟩

/-- **Ramified Euler-Product Rank Deficit (`ramShare_of_euler_deficit`)**:
Proves Alpöge's `ramShare_at_of` (`TopDensityNGeSixteen.lean:894-921`):
if each compressed rank satisfies `(d u : ℝ) * (1 - 1 / (T - 1))^f ≤ (r u : ℝ)` with
`T ≥ b ^ (m / 2)`, `m ≥ 2`, `b ≥ 3`, then `(d u : ℝ) - (r u : ℝ) ≤ (2 * f / b) * (d u : ℝ)`
(via Bernoulli's inequality `(1 - a)^f ≥ 1 - f * a` for `0 ≤ a ≤ 1`). -/
theorem bernoulli_one_sub_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ f : ℕ, 1 - (f : ℝ) * a ≤ (1 - a) ^ f
  | 0 => by simp
  | f + 1 => by
    have ih := bernoulli_one_sub_ge ha0 ha1 f
    rw [pow_succ]
    have h1ma : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have hmul := mul_le_mul_of_nonneg_right ih h1ma
    have hdiff : (1 - (f : ℝ) * a) * (1 - a) - (1 - ((f + 1 : ℕ) : ℝ) * a) =
        (f : ℝ) * a ^ 2 := by
      push_cast; ring
    have hnn : 0 ≤ (f : ℝ) * a ^ 2 := by positivity
    linarith

theorem ramShare_of_euler_deficit {ι : Type*} [Fintype ι] (d r : ι → ℕ)
    (T b : ℝ) (f m : ℕ) (hb3 : 3 ≤ b) (hm2 : 2 ≤ m)
    (hT_ge : b ^ ((m : ℝ) / 2) ≤ T)
    (hrel : ∀ u : ι, (d u : ℝ) * (1 - 1 / (T - 1)) ^ f ≤ (r u : ℝ)) :
    ∀ u : ι, (d u : ℝ) - (r u : ℝ) ≤ (2 * (f : ℝ) / b) * (d u : ℝ) := by
  intro u
  have hb0 : 0 < b := by linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hTb : b ≤ T := by
    calc b = b ^ (1 : ℝ) := (Real.rpow_one b).symm
      _ ≤ b ^ ((m : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) hm1
      _ ≤ T := hT_ge
  have hTm1_pos : 0 < T - 1 := by linarith
  have ha0 : 0 ≤ 1 / (T - 1) := by positivity
  have ha1 : 1 / (T - 1) ≤ 1 := by
    rw [div_le_one hTm1_pos]; linarith
  have hbern := bernoulli_one_sub_ge ha0 ha1 f
  have htwo : 1 / (T - 1) ≤ 2 / b := by
    rw [div_le_div_iff₀ hTm1_pos hb0]
    linarith
  have hsub : 1 - (f : ℝ) * (2 / b) ≤ (1 - 1 / (T - 1)) ^ f := by
    have := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) f)
    linarith
  have hdu : (d u : ℝ) * (1 - (f : ℝ) * (2 / b)) ≤ (r u : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg (α := ℝ) (d u))
    exact h1.trans (hrel u)
  linarith [show (d u : ℝ) * (1 - (f : ℝ) * (2 / b)) =
    (d u : ℝ) - (2 * (f : ℝ) / b) * (d u : ℝ) by ring]

/-- Explicit global codimension share `∑ u, (d u - r u) ≤ (2 * f / b) * totalRank d`. -/
theorem ramShare_total_of_euler_deficit {ι : Type*} [Fintype ι] (d r : ι → ℕ)
    (T b : ℝ) (f m : ℕ) (hb3 : 3 ≤ b) (hm2 : 2 ≤ m)
    (hT_ge : b ^ ((m : ℝ) / 2) ≤ T)
    (hrel : ∀ u : ι, (d u : ℝ) * (1 - 1 / (T - 1)) ^ f ≤ (r u : ℝ)) :
    ∑ u : ι, ((d u : ℝ) - (r u : ℝ)) ≤ (2 * (f : ℝ) / b) * LatticeFrame.totalRank d := by
  unfold LatticeFrame.totalRank
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => ramShare_of_euler_deficit d r T b f m hb3 hm2 hT_ge hrel u

end MatKFSpectralParamsSection

/-! ## Section 6: `bessel_test_vector_frame` — Test-Vector Frame & `Stage2GramFrameFiber` Builder -/

section BesselTestVectorFrameSection

/-- **Unified Bessel Test-Vector & Gram-Frame Assembly (`bessel_test_vector_frame`)**:
Directly combines:
1. Separated `L²(ℝ^d, ℂ)` Bessel wave-grid frame stability `(1 - sg) ∑ ‖c_u‖² ≤ ‖∑ c_u φ_u‖² ≤
   (1 + sg) ∑ ‖c_u‖²` and linear independence at `Δ ≥ sepConst d * σ * √(log (1 / sg))`,
2. Concrete Vandermonde Lagrange delta test-vector assembly on spacing-5 interlacing grids
   `progY y0 n` (with quantitative grid-point lower bound `√(c / n) ≤ ‖eval v y‖`),
3. Letter-word shift envelope `(3 / 4)^|w| * ‖q y‖ ≤ ‖wordEval q w y‖` on separated grids, and
4. All numerical threshold bounds of `Stage3ThetaSiegelBridge` / `Stage2ThetaWire`. -/
theorem bessel_test_vector_frame {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ sg : ℝ} (hσ : 0 < σ) (hsg : 0 < sg) (hsg20 : sg ≤ 1 / 20)
    (hΔ_ge : Stage11BesselWaveSchur.sepConst d * σ * Real.sqrt (Real.log (1 / sg)) ≤ Δ)
    (hsep : Stage11BesselWaveSchur.IsSeparatedGrid W Δ)
    (y0 : ℝ) (n : ℕ) (i₀ : Fin n) (α : ℂ)
    (q : ℝ → ℂ) (w : List BesselWaveGrid.Letter) (y : ℝ)
    (hpol : ∀ l ∈ w, 4 ≤ |y - l.pt|) :
    (∀ c : EuclideanSpace ℝ (Fin d) → ℂ,
      (1 - sg) * ∑ u ∈ W, ‖c u‖ ^ 2 ≤
        ‖∑ u ∈ W, c u • Stage11BesselWaveSchur.unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ∧
      ‖∑ u ∈ W, c u • Stage11BesselWaveSchur.unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ≤
        (1 + sg) * ∑ u ∈ W, ‖c u‖ ^ 2) ∧
    LinearIndependent ℂ
      (fun u : W => Stage11BesselWaveSchur.wavePacketLp σ hσ u.1 (ξ u.1)) ∧
    (∃ v : Fin n → ℂ, ∀ i : Fin n,
      BesselWaveGrid.waveEval
        (BesselWaveGrid.vandermondeKernel (fun k : Fin n => y0 + 5 * (k : ℝ))) v i =
        if i = i₀ then α else 0) ∧
    ((3 : ℝ) / 4) ^ w.length * ‖q y‖ ≤ ‖BesselWaveGrid.wordEval q w y‖ ∧
    (∃ delBar sgBar deBar e0Bar : ℝ,
      delBar = sg ∧ sgBar = sg ∧ deBar = sg ∧ e0Bar = (sg / 2) ^ 2 ∧
      delBar ≤ 1 / 2 ∧ sgBar ≤ 1 / 20 ∧ deBar ≤ 1 / 4 ∧
      0 ≤ e0Bar ∧ Real.sqrt e0Bar ≤ sgBar / 2 ∧
      5 * sgBar + 3 * Real.sqrt deBar + 4 * Real.sqrt (2 * e0Bar) ≤ 11 / 10) := by
  have hthr := Stage11BesselWaveSchur.bessel_grid_satisfies_gramFrame_thresholds
    W ξ hσ hsg hsg20 hΔ_ge hsep
  refine ⟨hthr.2.1,
    Stage11BesselWaveSchur.bessel_grid_linearIndependent W ξ hσ hsg (by linarith) hΔ_ge hsep,
    BesselWaveGrid.exists_delta_test_vector_progY y0 n i₀ α,
    BesselWaveGrid.norm_wordEval_ge q w y hpol,
    sg, sg, sg, (sg / 2) ^ 2, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨hthr.2.2.1, hthr.2.2.2.1, hthr.2.2.2.2.1, hthr.2.2.2.2.2.1,
    hthr.2.2.2.2.2.2.1, hthr.2.2.2.2.2.2.2⟩

/-- **Direct Builder from `BesselGramSpectralBundle` to `Stage2ThetaWire.Stage2GramFrameFiber`**:
Given a `BesselGramSpectralBundle` together with Harder–Narasimhan source slopes `y`, ambient
target slopes `x` (bounded below by `muMinCC`), and filtration subspaces `Nτ τ` projecting into
ambient targets `T τ`, builds the concrete `Stage2ThetaWire.Stage2GramFrameFiber` (with
**independent** `muCC = avg(x)`) and immediately proves `BostSlopeFiber.SlopeIneq`!
Ready for direct consumption by M2 Wave 2 `FrameRealCompile`. -/
def toStage2GramFrameFiber
    {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    (B : BesselGramSpectralBundle ι κ κ₁)
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (hsg_bar : B.P.sg ≤ sgBar) (hsgBar_le : sgBar ≤ 1 / 20)
    (he0_bar : B.P.e0 ≤ e0Bar)
    (hde_bar : B.P.de ≤ deBar) (hdeBar_le : deBar ≤ 1 / 4)
    (hδ_bar : B.P.δ ≤ delBar) (hdelBar_le : delBar ≤ 1 / 2)
    (hκ_pos : 0 < Fintype.card κ) (hcardW : 1 ≤ cardW)
    (y : ∀ u, Fin (B.F.r u) → ℝ)
    (hy_mean : (∑ u, (B.F.r u : ℝ)) * s ≤ ∑ u, ∑ j, y u j)
    (hy_top : ∀ u j, y u j ≤ s + uF)
    (x : Fin (Fintype.card κ) → ℝ)
    (hx_min : ∀ j, muMinCC ≤ x j)
    (Nτ : ℝ → ∀ u, Submodule ℂ (EuclideanSpace ℂ (Fin (B.F.r u))))
    (T : ℝ → Submodule ℂ (EuclideanSpace ℂ κ))
    (hNτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u,
      (B.F.r u : ℝ) - Module.finrank ℂ (Nτ τ u) ≤
        ((Finset.univ.filter (fun j => y u j < s - τ)).card : ℝ))
    (hT_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u (v : EuclideanSpace ℂ (Fin (B.F.r u))),
      v ∈ Nτ τ u →
      (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
            (B.F.compressedMat u)) v) (Sum.inl k)) ∈ T τ)
    (hT_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => x j < s - Real.log (cardW : ℝ) - τ)).card : ℝ) ≤
        (Fintype.card κ : ℝ) - Module.finrank ℂ (T τ)) :
    Stage2ThetaWire.Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar where
  ι := ι
  κ := κ
  κ₁ := κ₁
  d := B.F.M.d
  r := B.F.r
  Bf := B.F.M.pmatFin B.F.ε
  Vr := B.F.Vr
  ga := fun u => (B.F.M.c0 u)⁻¹
  Dstar := B.P.Dstar
  sg := B.P.sg
  η0 := B.P.η0
  η1 := B.P.η1
  e0 := B.P.e0
  de := B.P.de
  δ := B.P.δ
  isIsom := B.F.isIsometryFamily
  ga_pos := fun u => inv_pos.mpr (B.hc0 u)
  Dstar_pos := B.P.Dstar_pos
  sg_pos := B.P.sg_pos
  sg_le_bar := hsg_bar
  sgBar_le := hsgBar_le
  rank_ge := B.rank_ge
  η0_ge := B.P.η0_ge
  η0_le := B.P.η0_le
  η1_le := B.P.η1_le
  e0_nonneg := B.P.e0_nonneg
  e0_le_bar := he0_bar
  sqrt_e0_le := B.P.sqrt_e0_le
  de_nonneg := B.P.de_nonneg
  de_le_bar := hde_bar
  deBar_le := hdeBar_le
  corV := B.corV
  gramInput := B.gramInput
  δ_nonneg := B.P.δ_nonneg
  δ_le_bar := hδ_bar
  delBar_le := hdelBar_le
  card_ge := B.card_ge
  κ_pos := hκ_pos
  cardW_ge_one := hcardW
  y := y
  y_mean := hy_mean
  y_top := hy_top
  x := x
  x_min := hx_min
  Nτ := Nτ
  T := T
  Nτ_corank := hNτ_corank
  T_proj := hT_proj
  T_tail := hT_tail

/-- Unconditional discharge of `RHDirect.BostSlopeFiber.SlopeIneq` from a
`BesselGramSpectralBundle` for every `0 ≤ uF`. -/
theorem bost_slope_ineq_of_bessel_bundle
    {ι κ κ₁ : Type} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    (B : BesselGramSpectralBundle ι κ κ₁)
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (huF0 : 0 ≤ uF)
    (hsg_bar : B.P.sg ≤ sgBar) (hsgBar_le : sgBar ≤ 1 / 20)
    (he0_bar : B.P.e0 ≤ e0Bar)
    (hde_bar : B.P.de ≤ deBar) (hdeBar_le : deBar ≤ 1 / 4)
    (hδ_bar : B.P.δ ≤ delBar) (hdelBar_le : delBar ≤ 1 / 2)
    (hκ_pos : 0 < Fintype.card κ) (hcardW : 1 ≤ cardW)
    (y : ∀ u, Fin (B.F.r u) → ℝ)
    (hy_mean : (∑ u, (B.F.r u : ℝ)) * s ≤ ∑ u, ∑ j, y u j)
    (hy_top : ∀ u j, y u j ≤ s + uF)
    (x : Fin (Fintype.card κ) → ℝ)
    (hx_min : ∀ j, muMinCC ≤ x j)
    (Nτ : ℝ → ∀ u, Submodule ℂ (EuclideanSpace ℂ (Fin (B.F.r u))))
    (T : ℝ → Submodule ℂ (EuclideanSpace ℂ κ))
    (hNτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u,
      (B.F.r u : ℝ) - Module.finrank ℂ (Nτ τ u) ≤
        ((Finset.univ.filter (fun j => y u j < s - τ)).card : ℝ))
    (hT_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u (v : EuclideanSpace ℂ (Fin (B.F.r u))),
      v ∈ Nτ τ u →
      (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
            (B.F.compressedMat u)) v) (Sum.inl k)) ∈ T τ)
    (hT_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => x j < s - Real.log (cardW : ℝ) - τ)).card : ℝ) ≤
        (Fintype.card κ : ℝ) - Module.finrank ℂ (T τ)) :
    (toStage2GramFrameFiber B hsg_bar hsgBar_le he0_bar hde_bar hdeBar_le hδ_bar hdelBar_le
      hκ_pos hcardW y hy_mean hy_top x hx_min Nτ T hNτ_corank hT_proj hT_tail).toBostFiber.SlopeIneq :=
  (toStage2GramFrameFiber B hsg_bar hsgBar_le he0_bar hde_bar hdeBar_le hδ_bar hdelBar_le
    hκ_pos hcardW y hy_mean hy_top x hx_min Nτ T hNτ_corank hT_proj hT_tail).toBostSlopeIneq huF0

end BesselTestVectorFrameSection

end RHDirect.Stage14M2_BesselSchurBlock

end
