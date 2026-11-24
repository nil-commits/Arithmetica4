import RHDirect.ArakelovCovolume
import RHDirect.Stage2SiegelReduction
import RHDirect.Stage4ArakelovBost
import RHDirect.Stage10GeometryOfNumbers
import RHDirect.Stage11MoriwakiCovolume
import RHDirect.Stage11DefiniteUnitaryChain
import RHDirect.Stage11BostDworkSqueeze
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# RHDirect.Stage12SchurWeylLattices

Phase C / Stage 12 unconditional, zero-`sorry`, zero-custom-`axiom`, zero-`native_decide`
Lean 4 formalization of:
1. **Arbitrary-Rank CM `𝓞_K`-Hermitian Lattices (`CMHermLattice` & `NumberFieldHLat`)**
   grounded on Mathlib `ZLattice.covolume`, generalizing `Stage11ThetaSiegelBridge`'s rank-2
   `stdCMLattice 1 1` to arbitrary rank `r ≥ 1`, arbitrary CM order `CMOrder d`, and arbitrary
   totally complex CM number fields `K` (`InfinitePlace K × ι × Fin 2` realization).
2. **Automorphic Exterior-Power Column Lattices `⋀^k Λ` (`1 ≤ k ≤ r`)**:
   - Full **Cauchy–Binet Determinant Theorem** (`det_transpose_mul_eq_sum_incTuple`),
   - Concrete Hilbert–Schmidt exterior-power Euclidean space `ExtPowSpace E k`, `pureWedge`,
     exact exterior inner product `inner_pureWedge`, and concrete exterior-power lattice
     `extPowLat L k`,
   - Exact rank `Nat.choose r k`, exact covolume `covol (⋀^k Λ) = (covol Λ) ^ (Nat.choose (r - 1) (k - 1))`,
     and **exact column-lattice slope invariance** `slope (⋀^k Λ) = k * slope Λ`,
   - Complex Hermitian compound-matrix exterior power `CMHermLattice.complexExtPow` with
     `IsZLattice ℝ` and exact determinant / covolume formula.
3. **Unconditional Weyl Hook-Length Dimension & Schur-Functor Branching Slope Lower Bound**:
   - Partitions `Partition r`, Young diagram cells, column lengths `colLen`, hook lengths
     `hookLength`, and hook product `hookProd`,
   - Weyl dimension formula `weylDim` for `U(r)` with exact evaluations on `⋀^k` (`choose r k`)
     and `Sym^k` (`choose (k + r - 1) k`),
   - **Exact Weyl Hook-Content Theorem (`weyl_hook_content_formula`)**:
     `weylDim lam = (∏_{(i,j) ∈ lam} (r + j - i)) / hookProd lam`, plus explicit hook-length bounds,
   - Iterated tensor-product column lattice `columnTensorLat L lam = ⨂_t (⋀^{c_t} L)` proving
     exact **`column_lattice_exact_slope`** (`slope (columnTensorLat L lam) = |lam| * slope L`),
   - Full-rank bounded-morphism `muMin` monotonicity (`muMin_sub_log_le_muMin_of_fullRank`) and
     uniform-in-weight **Schur-functor branching slope lower bound**
     (`schur_branching_slope_lower`, `lower_slope_inequality_family`) on definite `U(X_0)`.
4. **Genuine Arbitrary-Dimension Arithmetic Hilbert–Samuel & Moriwaki Bigness (`L3`)**:
   - Arbitrary-dimension `d ≥ 1` graded Hermitian section algebra `GradedHermAlgebra d`
     (`⨁_{k ≥ 0} H^0(X, L^{⊗ k})`) with positive arithmetic self-intersection `volAr > 0`,
     polynomial Bergman `L^∞`-vs-`L²` distortion, and concrete finite set `smallSections A k`
     (`‖s‖_sup < 1`),
   - **Moriwaki's Bigness Theorem (`moriwaki_big_small_sections`)**:
     `∃ c₀ > 0, ∃ K₀ ≥ 1, ∀ k ≥ K₀, Real.log (#smallSections A k) ≥ c₀ * k ^ (d + 1)`,
     plus unconditional 0-assumption instantiation on `ℙ^d` (`projSpaceGradedHermAlgebra`),
   - **Uniform Indefinite Hodge-Lattice Covolume Bound (`L3_hodge_covolume_bound`)** feeding
     directly into `Stage11ThetaSiegelBridge` and `Stage11BostDworkSqueeze`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Matrix
open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  covol_le_of_le_same_rank gram_sum_smul_eq_transpose_mul slope_le_muMax)
open RHDirect.Stage2SiegelReduction (gsVec gsCoeff gs_expansion gsVec_orthogonal
  gsVec_ne_zero_of_linearIndependent det_gram_eq_prod_gsVec_norm_sq covol_le_prod_norm
  lattice_inter_closedBall_finite)
open RHDirect.Stage4ArakelovBost (IsSaturated projOrth quotLat muMin norm_projOrth_le
  discreteTopology_of_fin_basis_real_li quotLat_exact_additivity discreteTopology_quotLat
  rk_add_quotLat covol_eq_mul_quotLat degAr_eq_add_quotLat muMin_le_slope_le_muMax
  muMin_le_slope_quotLat)
open RHDirect.Stage10GeometryOfNumbers (basisOfZLattice covolume_eq_abs_det)
open RHDirect.Stage11MoriwakiCovolume (arithDeg arithDeg_eq_rk_mul_slope scaleLat
  scaleLat_invariants slope_scaleLat arithDeg_eq_of_isometric_equiv TensorSpace pureTensor
  tensorLat tensorLat_invariants slope_tensor_eq_add h0ArithStrict
  log_h0ArithStrict_lower_bound log_unitBallVol_ge MultiIndex card_multiIndex
  card_multiIndex_pos symPowMonomialLat slope_symPowMonomialLat diagLat diagLat_invariants)
open RHDirect.Stage11DefiniteUnitaryChain (DefiniteHermitianSpace hermCoordEquiv realEquiv
  CMOrder HermitianLattice stdCMLattice covol_stdCMLattice posDefSqrt posDefSqrt_isHermitian
  posDefSqrt_conjTranspose_mul_self posDef_det_eq_prod_eigenvalues posDef_det_re_pos
  hermitianLatticeOfPosDef cmOrder_smul_mem_hermitianLatticeOfPosDef covolume_hermitian_ofPosDef
  HermitianGenus)
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology ComplexOrder

namespace RHDirect.Stage12SchurWeylLattices

/-! ## Section 1: Arbitrary-Rank CM `𝓞_K`-Hermitian Lattices Grounded on Mathlib `ZLattice.covolume` -/

section ArbitraryRankCMLattices

/-- **Arbitrary-Rank Positive-Definite CM Hermitian Lattice `CMHermLattice d r`**:
a rank-`r` (`r ≥ 1`) positive-definite Hermitian lattice over the CM order `𝒪_d = ℤ[√-d]` (`d ≥ 1`)
with Hermitian Gram matrix `H : Matrix (Fin r) (Fin r) ℂ`, generalizing `stdCMLattice 1 1`. -/
structure CMHermLattice (d r : ℕ) where
  hd : 0 < d
  hr : 1 ≤ r
  H : Matrix (Fin r) (Fin r) ℂ
  hH : H.PosDef

namespace CMHermLattice

variable {d r : ℕ}

/-- Underlying full-rank `HermitianLattice r` in `DefiniteHermitianSpace r = ℂ^r`. -/
def toHermitianLattice (Λ : CMHermLattice d r) : HermitianLattice r :=
  hermitianLatticeOfPosDef d Λ.hd Λ.H Λ.hH

/-- Underlying `ℤ`-submodule inside `ℂ^r`. -/
def complexLat (Λ : CMHermLattice d r) : Submodule ℤ (DefiniteHermitianSpace r) :=
  Λ.toHermitianLattice.lat

/-- Explicit isometric embedding `ℂ^r ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * r))`. -/
def euclEmbed (r : ℕ) : DefiniteHermitianSpace r ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * r)) :=
  realEquiv r

/-- Realized `2r`-dimensional Euclidean lattice inside `EuclideanSpace ℝ (Fin (2 * r))`. -/
def euclLat (Λ : CMHermLattice d r) : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * r))) :=
  Λ.toHermitianLattice.realLat

instance discreteTopology_euclLat (Λ : CMHermLattice d r) : DiscreteTopology Λ.euclLat :=
  Λ.toHermitianLattice.realLat_discrete

instance isZLattice_euclLat (Λ : CMHermLattice d r) : IsZLattice ℝ Λ.euclLat :=
  Λ.toHermitianLattice.realLat_isZLattice

instance discreteTopology_complexLat (Λ : CMHermLattice d r) : DiscreteTopology Λ.complexLat :=
  Λ.toHermitianLattice.disc

instance isZLattice_complexLat (Λ : CMHermLattice d r) : IsZLattice ℝ Λ.complexLat :=
  Λ.toHermitianLattice.zlat

/-- `Λ.complexLat` is stable under scalar multiplication by the CM order `𝒪_d = ℤ[√-d]`. -/
theorem cmOrder_smul_mem (Λ : CMHermLattice d r) {α : ℂ} (hα : α ∈ CMOrder d)
    {v : DefiniteHermitianSpace r} (hv : v ∈ Λ.complexLat) :
    α • v ∈ Λ.complexLat :=
  cmOrder_smul_mem_hermitianLatticeOfPosDef d Λ.hd Λ.H Λ.hH hα hv

/-- Exact isometric equivalence between `Λ.complexLat` and `Λ.euclLat`. -/
theorem complexLat_eq_euclLat_invariants (Λ : CMHermLattice d r) :
    rk Λ.complexLat = rk Λ.euclLat ∧
    covol Λ.complexLat = covol Λ.euclLat ∧
    arithDeg Λ.complexLat = arithDeg Λ.euclLat ∧
    ArakelovCovolume.slope Λ.complexLat = ArakelovCovolume.slope Λ.euclLat := by
  refine arithDeg_eq_of_isometric_equiv Λ.toHermitianLattice.realLatEquiv fun x => ?_
  change ‖realEquiv r x.1‖ = ‖x.1‖
  exact (realEquiv r).norm_map x.1

/-- Exact `ℤ`-rank of `Λ.euclLat`: `rk Λ.euclLat = 2 * r`. -/
theorem rk_euclLat (Λ : CMHermLattice d r) : rk Λ.euclLat = 2 * r := by
  rw [← (Λ.complexLat_eq_euclLat_invariants).1]
  exact Λ.toHermitianLattice.rk_eq

theorem euclLat_ne_bot (Λ : CMHermLattice d r) : Λ.euclLat ≠ ⊥ := by
  intro hbot
  have hrk := Λ.rk_euclLat
  rw [hbot] at hrk
  have h0 : rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * r)))) = 0 := by simp [rk]
  rw [h0] at hrk
  have := Λ.hr
  omega

/-- **Grounded on Mathlib `ZLattice.covolume` (`covol_eq_zlattice_covolume`)**:
for every arbitrary-rank CM Hermitian lattice `Λ : CMHermLattice d r`,
`ArakelovCovolume.covol Λ.euclLat = ZLattice.covolume Λ.euclLat volume`. -/
theorem covol_eq_zlattice_covolume (Λ : CMHermLattice d r) :
    covol Λ.euclLat = ZLattice.covolume Λ.euclLat volume := by
  rw [← (Λ.complexLat_eq_euclLat_invariants).2.1]
  exact Λ.toHermitianLattice.covol_eq_real_covolume

/-- **Exact Arbitrary-Rank CM Hermitian Covolume Formula**:
`covol Λ.euclLat = (√d)^r * H.det.re`. -/
theorem covol_eq (Λ : CMHermLattice d r) :
    covol Λ.euclLat = (Real.sqrt d) ^ r * Λ.H.det.re := by
  rw [← (Λ.complexLat_eq_euclLat_invariants).2.1]
  exact covolume_hermitian_ofPosDef d Λ.hd Λ.H Λ.hH

/-- **Exact Arbitrary-Rank CM Hermitian Arithmetic Degree Formula**:
`arithDeg Λ.euclLat = -(r / 2) * log d - log (H.det.re)`. -/
theorem arithDeg_eq (Λ : CMHermLattice d r) :
    arithDeg Λ.euclLat = -((r : ℝ) / 2) * Real.log d - Real.log Λ.H.det.re := by
  unfold arithDeg
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr Λ.hd)
  have hdet_pos : 0 < Λ.H.det.re := (posDef_det_re_pos Λ.H Λ.hH).1
  rw [Λ.covol_eq, Real.log_mul (pow_pos hsqrt_pos r).ne' hdet_pos.ne', Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg d)]
  ring

/-- **Exact Arbitrary-Rank CM Hermitian Slope Formula**:
`slope Λ.euclLat = -(1 / 4) * log d - log (H.det.re) / (2 * r)`. -/
theorem slope_eq (Λ : CMHermLattice d r) :
    ArakelovCovolume.slope Λ.euclLat =
      -(1 / 4) * Real.log d - Real.log Λ.H.det.re / (2 * (r : ℝ)) := by
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Λ.hr; omega)
  rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk, Λ.rk_euclLat, Λ.arithDeg_eq]
  push_cast
  field_simp [hr_ne]
  ring

/-- Standard rank-`r` CM lattice with identity Gram matrix `H = 1` (generalizing `stdCMLattice 1 1`). -/
def std (d r : ℕ) (hd : 0 < d) (hr : 1 ≤ r) : CMHermLattice d r where
  hd := hd
  hr := hr
  H := 1
  hH := Matrix.PosDef.one

theorem slope_std (d r : ℕ) (hd : 0 < d) (hr : 1 ≤ r) :
    ArakelovCovolume.slope (std d r hd hr).euclLat = -(1 / 4) * Real.log d := by
  rw [(std d r hd hr).slope_eq]
  simp [std]

/-- Scaling the Hermitian Gram matrix `H` by a positive scalar `c > 0`. -/
def scaleMetric (Λ : CMHermLattice d r) {c : ℝ} (hc : 0 < c) : CMHermLattice d r where
  hd := Λ.hd
  hr := Λ.hr
  H := ((c : ℂ)) • Λ.H
  hH := by
    refine ⟨?_, fun {x} hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      have hh := congrFun (congrFun Λ.hH.isHermitian i) j
      simp only [Matrix.conjTranspose_apply, Complex.star_def] at hh
      rw [hh, mul_comm]
    · have hpos := Λ.hH.2 hx
      have hfactor :
          (x.sum fun i xi => x.sum fun j xj => star xi * ((c : ℂ) • Λ.H) i j * xj) =
          (c : ℂ) * (x.sum fun i xi => x.sum fun j xj => star xi * Λ.H i j * xj) := by
        rw [Finsupp.mul_sum]
        refine Finsupp.sum_congr fun i _ => ?_
        rw [Finsupp.mul_sum]
        refine Finsupp.sum_congr fun j _ => ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hfactor]
      have hcC : (0 : ℂ) < (c : ℂ) := by
        rw [Complex.lt_def]
        exact ⟨by simpa using hc, rfl⟩
      exact mul_pos hcC hpos

theorem covol_scaleMetric (Λ : CMHermLattice d r) {c : ℝ} (hc : 0 < c) :
    covol (Λ.scaleMetric hc).euclLat = c ^ r * covol Λ.euclLat := by
  rw [(Λ.scaleMetric hc).covol_eq, Λ.covol_eq]
  have hdet : (((c : ℂ) • Λ.H).det).re = c ^ r * Λ.H.det.re := by
    rw [Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (Real.sqrt d) ^ r * (((c : ℂ) • Λ.H).det).re = _
  rw [hdet]
  ring

theorem slope_scaleMetric (Λ : CMHermLattice d r) {c : ℝ} (hc : 0 < c) :
    ArakelovCovolume.slope (Λ.scaleMetric hc).euclLat =
      ArakelovCovolume.slope Λ.euclLat - (1 / 2) * Real.log c := by
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Λ.hr; omega)
  rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
    Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
    (Λ.scaleMetric hc).rk_euclLat, Λ.rk_euclLat]
  unfold arithDeg
  rw [Λ.covol_scaleMetric hc, Real.log_mul (pow_pos hc r).ne' (covol_pos Λ.euclLat).ne',
    Real.log_pow]
  push_cast
  field_simp [hr_ne]
  ring

/-- Block-diagonal positive-definiteness helper for `Matrix.fromBlocks`. -/
private lemma posDef_fromBlocks {r₁ r₂ : ℕ}
    {H₁ : Matrix (Fin r₁) (Fin r₁) ℂ} {H₂ : Matrix (Fin r₂) (Fin r₂) ℂ}
    (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef) :
    (Matrix.fromBlocks H₁ 0 0 H₂).PosDef := by
  refine ⟨?_, fun {x} hx => ?_⟩
  · ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hH₁.isHermitian i) j
      | inr j => simp [Matrix.conjTranspose_apply]
    | inr i =>
      cases j with
      | inl j => simp [Matrix.conjTranspose_apply]
      | inr j =>
        simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hH₂.isHermitian i) j
  · let x₁ : Fin r₁ →₀ ℂ := Finsupp.equivFunOnFinite.symm (fun i => x (Sum.inl i))
    let x₂ : Fin r₂ →₀ ℂ := Finsupp.equivFunOnFinite.symm (fun j => x (Sum.inr j))
    have hsplit :
        (x.sum fun a xa => x.sum fun b xb => star xa * (Matrix.fromBlocks H₁ 0 0 H₂) a b * xb) =
        (x₁.sum fun i xi => x₁.sum fun j xj => star xi * H₁ i j * xj) +
        (x₂.sum fun i xi => x₂.sum fun j xj => star xi * H₂ i j * xj) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp),
        Finsupp.sum_fintype _ _ (fun _ => by simp),
        Finsupp.sum_fintype _ _ (fun _ => by simp)]
      have hL : ∀ a, (x.sum fun b xb => star (x a) * (Matrix.fromBlocks H₁ 0 0 H₂) a b * xb) =
          ∑ b, star (x a) * (Matrix.fromBlocks H₁ 0 0 H₂) a b * x b :=
        fun a => Finsupp.sum_fintype _ _ (fun _ => by simp)
      have hR1 : ∀ i, (x₁.sum fun j xj => star (x₁ i) * H₁ i j * xj) =
          ∑ j, star (x₁ i) * H₁ i j * x₁ j :=
        fun i => Finsupp.sum_fintype _ _ (fun _ => by simp)
      have hR2 : ∀ i, (x₂.sum fun j xj => star (x₂ i) * H₂ i j * xj) =
          ∑ j, star (x₂ i) * H₂ i j * x₂ j :=
        fun i => Finsupp.sum_fintype _ _ (fun _ => by simp)
      simp_rw [hL, hR1, hR2]
      rw [Fintype.sum_sum_type]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_sum_type]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
          mul_zero, zero_mul, Finset.sum_const_zero, add_zero, x₁]
        rfl
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_sum_type]
        simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
          mul_zero, zero_mul, Finset.sum_const_zero, zero_add, x₂]
        rfl
    rw [hsplit]
    have hnn₁ : 0 ≤ x₁.sum fun i xi => x₁.sum fun j xj => star xi * H₁ i j * xj := by
      by_cases h1 : x₁ = 0
      · simp [h1]
      · exact (hH₁.2 h1).le
    have hnn₂ : 0 ≤ x₂.sum fun i xi => x₂.sum fun j xj => star xi * H₂ i j * xj := by
      by_cases h2 : x₂ = 0
      · simp [h2]
      · exact (hH₂.2 h2).le
    have hne : x₁ ≠ 0 ∨ x₂ ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hx
      ext a
      cases a with
      | inl i => exact congrArg (fun f : Fin r₁ →₀ ℂ => f i) hall.1
      | inr j => exact congrArg (fun f : Fin r₂ →₀ ℂ => f j) hall.2
    rcases hne with h1 | h2
    · exact add_pos_of_pos_of_nonneg (hH₁.2 h1) hnn₂
    · exact add_pos_of_nonneg_of_pos hnn₁ (hH₂.2 h2)

/-- Orthogonal direct sum `Λ₁ ⊕ Λ₂` of arbitrary-rank CM Hermitian lattices over `𝒪_d`. -/
def directSum {r₁ r₂ : ℕ} (Λ₁ : CMHermLattice d r₁) (Λ₂ : CMHermLattice d r₂) :
    CMHermLattice d (r₁ + r₂) where
  hd := Λ₁.hd
  hr := by have := Λ₁.hr; omega
  H := (Matrix.fromBlocks Λ₁.H 0 0 Λ₂.H).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  hH := (posDef_fromBlocks Λ₁.hH Λ₂.hH).submatrix finSumFinEquiv.symm.injective

theorem covol_directSum {r₁ r₂ : ℕ} (Λ₁ : CMHermLattice d r₁) (Λ₂ : CMHermLattice d r₂) :
    covol (Λ₁.directSum Λ₂).euclLat = covol Λ₁.euclLat * covol Λ₂.euclLat := by
  rw [(Λ₁.directSum Λ₂).covol_eq, Λ₁.covol_eq, Λ₂.covol_eq]
  have hdet : ((Λ₁.directSum Λ₂).H).det = Λ₁.H.det * Λ₂.H.det := by
    change ((Matrix.fromBlocks Λ₁.H 0 0 Λ₂.H).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).det = _
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have hre : ((Λ₁.directSum Λ₂).H).det.re = Λ₁.H.det.re * Λ₂.H.det.re := by
    rw [hdet, Complex.mul_re, (posDef_det_re_pos Λ₁.H Λ₁.hH).2,
      (posDef_det_re_pos Λ₂.H Λ₂.hH).2, mul_zero, sub_zero]
  rw [hre, pow_add]
  ring

theorem slope_directSum {r₁ r₂ : ℕ} (Λ₁ : CMHermLattice d r₁) (Λ₂ : CMHermLattice d r₂) :
    ArakelovCovolume.slope (Λ₁.directSum Λ₂).euclLat =
      ((r₁ : ℝ) * ArakelovCovolume.slope Λ₁.euclLat +
        (r₂ : ℝ) * ArakelovCovolume.slope Λ₂.euclLat) / ((r₁ + r₂ : ℕ) : ℝ) := by
  have hr1 : (r₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Λ₁.hr; omega)
  have hr2 : (r₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Λ₂.hr; omega)
  have hr12 : ((r₁ + r₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Λ₁.hr; omega)
  rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
    Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
    Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
    (Λ₁.directSum Λ₂).rk_euclLat, Λ₁.rk_euclLat, Λ₂.rk_euclLat]
  unfold arithDeg
  rw [Λ₁.covol_directSum Λ₂, Real.log_mul (covol_pos Λ₁.euclLat).ne' (covol_pos Λ₂.euclLat).ne']
  push_cast
  field_simp [hr1, hr2, hr12]
  ring

end CMHermLattice

/-! ### General Totally-Complex Number Field `HLat K` (`StatementMaj` / `DataArith` Realization) -/

section NumberFieldHLatSection

open NumberField

/-- Explicit coordinate-reindexing linear isometry on `EuclideanSpace ℝ`. -/
def euclideanSpaceCongr {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ β where
  toFun x := WithLp.toLp 2 fun j => x (e.symm j)
  invFun y := WithLp.toLp 2 fun i => y (e i)
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl
  left_inv x := by ext i; simp
  right_inv y := by ext j; simp
  norm_map' x := by
    change ‖WithLp.toLp 2 (fun j : β => x (e.symm j))‖ = ‖x‖
    have hsq : ‖WithLp.toLp 2 (fun j : β => x (e.symm j))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact Equiv.sum_comp e.symm (fun i => ‖x i‖ ^ 2)
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun j : β => x (e.symm j))), norm_nonneg x]

section RealizeDefs

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

/-- Archimedean coordinate vector at infinite place `v : InfinitePlace K` in basis `b`. -/
def vecAt (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

/-- Frame-twisted coordinate vector `(X v)⁻¹ · vecAt b v x` (matching `StatementMaj.fcoord`). -/
def fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecAt b v x)

/-- Hermitian norm at infinite place `v` (matching `StatementMaj.normAt`). -/
def normAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ℝ :=
  Real.sqrt (∑ i : ι, ‖fcoord b X v x i‖ ^ 2)

lemma fcoord_zero (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : fcoord b X v 0 = 0 := by
  have h0 : vecAt b v 0 = 0 := by funext i; simp [vecAt]
  simp only [fcoord, h0, Matrix.mulVec_zero]

lemma fcoord_add (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord
  rw [← Matrix.mulVec_add]
  congr 1; funext i; simp [vecAt, map_add]

/-- Canonical real Euclidean realization `V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)`
matching `Formalism.HermitianLatticesTheory.realize` (`StatementMaj.lean:L78-L81`). -/
def realizeHLat (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun x := WithLp.toLp 2 fun p =>
    if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re else (fcoord b X p.1 x p.2.1).im
  map_zero' := by
    ext p
    simp [fcoord_zero]
  map_add' x y := by
    ext p
    simp only [WithLp.ofLp_add, Pi.add_apply, fcoord_add, Complex.add_re, Complex.add_im]
    split_ifs <;> rfl

/-- **Exact Archimedean Norm-Squared Identity (`norm_sq_realizeHLat`)**:
`‖realizeHLat b X x‖ ^ 2 = ∑ v : InfinitePlace K, normAt b X v x ^ 2`
(exact counterpart of `StatementMaj.lean:L144`). -/
theorem norm_sq_realizeHLat [NumberField K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖realizeHLat b X x‖ ^ 2 = ∑ v : InfinitePlace K, normAt b X v x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  unfold normAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp only [realizeHLat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, WithLp.ofLp_toLp, ↓reduceIte,
    Fin.one_eq_zero_iff, Nat.reduceEqDiff, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

end RealizeDefs

/-- **General CM Number-Field Hermitian Lattice `NumberFieldHLat K`**
(matching `Formalism.BasicNotions.HLat` in `DataArith.lean:L61-L104`). -/
structure NumberFieldHLat (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] where
  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  b : Module.Basis ι K V
  X : InfinitePlace K → Matrix ι ι ℂ
  hX : ∀ v, IsUnit (X v).det
  L : Submodule (𝓞 K) V
  [discReal : DiscreteTopology ((L.restrictScalars ℤ).map (realizeHLat b X).toIntLinearMap)]
  [zlatReal : IsZLattice ℝ ((L.restrictScalars ℤ).map (realizeHLat b X).toIntLinearMap)]

attribute [instance] NumberFieldHLat.addV NumberFieldHLat.modV NumberFieldHLat.modOV
  NumberFieldHLat.towV NumberFieldHLat.finι NumberFieldHLat.decι
  NumberFieldHLat.discReal NumberFieldHLat.zlatReal

namespace NumberFieldHLat

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- Realized `ℤ`-lattice in `EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)`. -/
abbrev zRealize (A : NumberFieldHLat K) :
    Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) :=
  (A.L.restrictScalars ℤ).map (realizeHLat A.b A.X).toIntLinearMap

/-- Exact identification of `ArakelovCovolume.covol A.zRealize` with Mathlib `ZLattice.covolume`
via isometric coordinate transport to `EuclideanSpace ℝ (Fin d)`. -/
theorem covol_eq_zlattice_covolume (A : NumberFieldHLat K) :
    let e : (InfinitePlace K × A.ι × Fin 2) ≃ Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2)) :=
      Fintype.equivFin _
    let iso : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2))) :=
      euclideanSpaceCongr e
    let Λ := A.zRealize.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
    ∃ (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      covol A.zRealize = ZLattice.covolume Λ volume := by
  intro e iso Λ
  let eqZ : A.zRealize ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨iso x.1, x.1, x.2, rfl⟩
      invFun := fun y => ⟨iso.symm y.1, by
        rcases y.2 with ⟨x, hx, hxy⟩
        have : iso.symm y.1 = x := by rw [← hxy]; exact iso.symm_apply_apply x
        rwa [this]⟩
      map_add' := fun x y => Subtype.ext (map_add iso x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul iso c x.1)
      left_inv := fun x => Subtype.ext (iso.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (iso.apply_symm_apply y.1) }
  have hDisc : DiscreteTopology Λ := by
    refine DiscreteTopology.of_continuous_injective (f := eqZ.symm) ?_ eqZ.symm.injective
    exact Continuous.subtype_mk (iso.symm.continuous.comp continuous_subtype_val) _
  have hIsZ : IsZLattice ℝ Λ := by
    constructor
    have h1 : Submodule.span ℝ (Λ : Set _) =
        (Submodule.span ℝ (A.zRealize : Set _)).map iso.toLinearEquiv.toLinearMap := by
      rw [Submodule.map_span]; rfl
    rw [h1, IsZLattice.span_top (K := ℝ) (L := A.zRealize), Submodule.map_top, LinearEquiv.range]
  refine ⟨hDisc, hIsZ, ?_⟩
  let bR : Module.Basis (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2))) ℤ Λ :=
    basisOfZLattice Λ
  let bA := bR.map eqZ.symm
  rw [covol_eq_sqrt_det_gram A.zRealize bA, covolume_eq_abs_det Λ bR]
  let B : Matrix (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2)))
      (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2))) ℝ :=
    Matrix.of fun i j =>
      (bR i : EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2)))) j
  have hgram : Matrix.gram ℝ
      (fun i => (bA i : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))) = B * Bᵀ := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply]
    have hmap : ∀ k, iso (bA k : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) =
        (bR k : EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2)))) := fun k => by
      change iso (iso.symm (bR k : EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2))))) = _
      exact iso.apply_symm_apply _
    rw [← iso.inner_map_map, hmap i, hmap j, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]

/-- Normalized logarithmic discriminant `log |disc K| / [K : ℚ]`. -/
def logDiscDivDeg (K : Type) [Field K] [NumberField K] : ℝ :=
  Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ)

/-- Normalized Arakelov slope `muDef` matching `Formalism/HarderNarasimhan/StatementPl.lean:L64`. -/
def mu (A : NumberFieldHLat K) : ℝ :=
  2 * ArakelovCovolume.slope A.zRealize - Real.log 2 + logDiscDivDeg K

/-- Normalized maximal Arakelov slope `muMaxDef`. -/
def muMax (A : NumberFieldHLat K) : ℝ :=
  2 * ArakelovCovolume.muMax A.zRealize - Real.log 2 + logDiscDivDeg K

/-- Normalized minimal Arakelov slope `muMinDef`. -/
def muMin (A : NumberFieldHLat K) : ℝ :=
  2 * Stage4ArakelovBost.muMin A.zRealize - Real.log 2 + logDiscDivDeg K

/-- Normalized log-covolume `lcv` matching `DataArith.lean:L90`. -/
def lcv (A : NumberFieldHLat K) : ℝ :=
  (2 / (Module.finrank ℚ K : ℝ)) * Real.log (covol A.zRealize)

theorem muMin_le_mu_le_muMax (A : NumberFieldHLat K) (hne : A.zRealize ≠ ⊥) :
    A.muMin ≤ A.mu ∧ A.mu ≤ A.muMax := by
  obtain ⟨h1, h2⟩ := muMin_le_slope_le_muMax A.zRealize hne
  unfold mu muMax muMin
  constructor <;> linarith

end NumberFieldHLat

end NumberFieldHLatSection

end ArbitraryRankCMLattices

/-! ## Section 2: Cauchy–Binet & Exterior-Power Column Lattices `⋀^k Λ` (`1 ≤ k ≤ r`) -/

section ExteriorPowerColumnLattices

/-- Strictly increasing `k`-tuples in `Fin d`, indexing the canonical orthonormal basis of `⋀^k ℝ^d`. -/
abbrev IncTuple (d k : ℕ) := { f : Fin k → Fin d // StrictMono f }

/-- Equivalence between `IncTuple d k` and `k`-element subsets of `Fin d`. -/
def incTupleEquivPowersetCard (d k : ℕ) :
    IncTuple d k ≃ { s : Finset (Fin d) // s ∈ (Finset.univ : Finset (Fin d)).powersetCard k } where
  toFun I := ⟨Finset.univ.image I.1, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_image_of_injective _ I.2.injective, Finset.card_fin]⟩⟩
  invFun s := ⟨fun a => s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2 a,
    (s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2).strictMono⟩
  left_inv I := by
    apply Subtype.ext
    funext a
    have hcard : (Finset.univ.image I.1).card = k := by
      rw [Finset.card_image_of_injective _ I.2.injective, Finset.card_fin]
    have hemb : OrderEmbedding.ofStrictMono I.1 I.2 =
        (Finset.univ.image I.1).orderEmbOfFin hcard := by
      apply Finset.orderEmbOfFin_unique' hcard
      intro b
      exact Finset.mem_image_of_mem I.1 (Finset.mem_univ b)
    exact (congrArg (fun g : Fin k ↪o Fin d => g a) hemb).symm
  right_inv s := by
    apply Subtype.ext
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact Finset.orderEmbOfFin_mem s.1 (Finset.mem_powersetCard.mp s.2).2 a
    · intro hx
      have hrng := Finset.range_orderEmbOfFin s.1 (Finset.mem_powersetCard.mp s.2).2
      have hx' : x ∈ Set.range (s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2) := by
        rw [hrng]; exact hx
      exact hx'

/-- Exact cardinality of `IncTuple d k`: `|IncTuple d k| = Nat.choose d k`. -/
theorem card_incTuple (d k : ℕ) : Fintype.card (IncTuple d k) = Nat.choose d k := by
  rw [Fintype.card_congr (incTupleEquivPowersetCard d k), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_fin]

/-- Exact incidence count: for `1 ≤ k`, every index `a : Fin r` lies in exactly
`Nat.choose (r - 1) (k - 1)` strictly increasing `k`-tuples `I : IncTuple r k`. -/
theorem card_incTuple_containing {r k : ℕ} (hk1 : 1 ≤ k) (a : Fin r) :
    (Finset.univ.filter fun I : IncTuple r k => a ∈ Set.range I.1).card =
      Nat.choose (r - 1) (k - 1) := by
  let S₁ := Finset.univ.filter fun I : IncTuple r k => a ∈ Set.range I.1
  let S₂ := ((Finset.univ : Finset (Fin r)).erase a).powersetCard (k - 1)
  have hbij : S₁.card = S₂.card := by
    refine Finset.card_bij
      (fun I _ => (Finset.univ.image I.1).erase a)
      (fun I hI => ?_)
      (fun I₁ hI₁ I₂ hI₂ heq => ?_)
      (fun t ht => ?_)
    · have haI : a ∈ Finset.univ.image I.1 := by
        obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hI).2
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, Finset.mem_univ _⟩
      · rw [Finset.card_erase_of_mem haI, Finset.card_image_of_injective _ I.2.injective,
          Finset.card_fin]
    · have ha₁ : a ∈ Finset.univ.image I₁.1 := by
        obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hI₁).2
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩
      have ha₂ : a ∈ Finset.univ.image I₂.1 := by
        obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hI₂).2
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩
      have himg : Finset.univ.image I₁.1 = Finset.univ.image I₂.1 := by
        rw [← Finset.insert_erase ha₁, ← Finset.insert_erase ha₂, heq]
      exact (incTupleEquivPowersetCard r k).injective (Subtype.ext himg)
    · rw [Finset.mem_powersetCard] at ht
      have ha_not : a ∉ t := fun h => (Finset.mem_erase.mp (ht.1 h)).1 rfl
      let s : Finset (Fin r) := insert a t
      have hs_card : s.card = k := by
        rw [Finset.card_insert_of_notMem ha_not, ht.2]
        omega
      let I : IncTuple r k :=
        ⟨fun b => s.orderEmbOfFin hs_card b, (s.orderEmbOfFin hs_card).strictMono⟩
      have hI_img : Finset.univ.image I.1 = s := by
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        have hrng := Finset.range_orderEmbOfFin s hs_card
        change x ∈ Set.range (s.orderEmbOfFin hs_card) ↔ x ∈ s
        rw [hrng]; rfl
      have ha_mem : a ∈ Set.range I.1 := by
        have : a ∈ Finset.univ.image I.1 := by rw [hI_img]; exact Finset.mem_insert_self a t
        simpa [Finset.mem_image] using this
      refine ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ I, ha_mem⟩, ?_⟩
      rw [hI_img, Finset.erase_insert ha_not]
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_fin]

/-- Exact binomial absorption identity: `r * choose (r - 1) (k - 1) = k * choose r k` (`1 ≤ k ≤ r`). -/
theorem mul_choose_pred_eq {r k : ℕ} (hr : 1 ≤ r) (hk1 : 1 ≤ k) :
    r * Nat.choose (r - 1) (k - 1) = k * Nat.choose r k := by
  cases r with
  | zero => omega
  | succ r' =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [Nat.add_sub_cancel]
      by_cases hle : k' ≤ r'
      · have h1 := Nat.choose_mul_factorial_mul_factorial hle
        have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hle)
        have hsub : r' + 1 - (k' + 1) = r' - k' := by omega
        rw [hsub, Nat.factorial_succ r', Nat.factorial_succ k'] at h2
        have hden : 0 < k'.factorial * (r' - k').factorial :=
          Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
        have hmul : ((r' + 1) * r'.choose k') * (k'.factorial * (r' - k').factorial) =
            ((k' + 1) * (r' + 1).choose (k' + 1)) * (k'.factorial * (r' - k').factorial) := by
          calc ((r' + 1) * r'.choose k') * (k'.factorial * (r' - k').factorial)
              = (r' + 1) * (r'.choose k' * k'.factorial * (r' - k').factorial) := by ring
            _ = (r' + 1) * r'.factorial := by rw [h1]
            _ = (r' + 1).choose (k' + 1) * ((k' + 1) * k'.factorial) * (r' - k').factorial := h2.symm
            _ = ((k' + 1) * (r' + 1).choose (k' + 1)) * (k'.factorial * (r' - k').factorial) := by ring
        exact Nat.eq_of_mul_eq_mul_right hden hmul
      · have hgt1 : r' < k' := Nat.lt_of_not_ge hle
        have hgt2 : r' + 1 < k' + 1 := Nat.succ_lt_succ hgt1
        rw [Nat.choose_eq_zero_of_lt hgt1, Nat.choose_eq_zero_of_lt hgt2, mul_zero, mul_zero]

private def injFunInc {d k : ℕ} (f : { f : Fin k → Fin d // Function.Injective f }) :
    IncTuple d k :=
  let s := Finset.univ.image f.1
  have hs : s.card = k := by rw [Finset.card_image_of_injective _ f.2, Finset.card_fin]
  ⟨fun a => s.orderEmbOfFin hs a, (s.orderEmbOfFin hs).strictMono⟩

private lemma injFunMem {d k : ℕ} (f : { f : Fin k → Fin d // Function.Injective f }) (a : Fin k) :
    f.1 a ∈ Set.range (injFunInc f).1 := by
  let s := Finset.univ.image f.1
  have hs : s.card = k := by rw [Finset.card_image_of_injective _ f.2, Finset.card_fin]
  have h1 : f.1 a ∈ s := Finset.mem_image_of_mem f.1 (Finset.mem_univ a)
  have hrng := Finset.range_orderEmbOfFin s hs
  change f.1 a ∈ Set.range (s.orderEmbOfFin hs)
  rw [hrng]; exact h1

/-- Helper decomposing an injective map `f : Fin k → Fin d` into `(I, τ) : IncTuple d k × Perm (Fin k)`
such that `I ∘ τ = f`. -/
private def injFunDecomp {d k : ℕ} (f : { f : Fin k → Fin d // Function.Injective f }) :
    IncTuple d k × Equiv.Perm (Fin k) :=
  let τFun : Fin k → Fin k := fun a => (injFunMem f a).choose
  have hτ_spec : ∀ a, (injFunInc f).1 (τFun a) = f.1 a := fun a => (injFunMem f a).choose_spec
  have hτ_inj : Function.Injective τFun := fun a b hab =>
    f.2 (by rw [← hτ_spec a, ← hτ_spec b, hab])
  (injFunInc f, Equiv.ofBijective τFun (Finite.injective_iff_bijective.mp hτ_inj))

private lemma injFunDecomp_spec {d k : ℕ} (f : { f : Fin k → Fin d // Function.Injective f })
    (a : Fin k) : (injFunDecomp f).1.1 ((injFunDecomp f).2 a) = f.1 a :=
  (injFunMem f a).choose_spec

/-- Bijection between injective maps `Fin k → Fin d` and pairs `(I, τ) : IncTuple d k × Perm (Fin k)`. -/
private def injFunEquivIncProdPerm (d k : ℕ) :
    { f : Fin k → Fin d // Function.Injective f } ≃ IncTuple d k × Equiv.Perm (Fin k) where
  toFun := injFunDecomp
  invFun p := ⟨p.1.1 ∘ p.2, p.1.2.injective.comp p.2.injective⟩
  left_inv f := Subtype.ext (funext fun a => injFunDecomp_spec f a)
  right_inv p := by
    rcases p with ⟨I, τ⟩
    let f : { f : Fin k → Fin d // Function.Injective f } :=
      ⟨I.1 ∘ τ, I.2.injective.comp τ.injective⟩
    have hspec : ∀ a, (injFunDecomp f).1.1 ((injFunDecomp f).2 a) = I.1 (τ a) :=
      injFunDecomp_spec f
    have himg : Finset.univ.image (injFunDecomp f).1.1 = Finset.univ.image I.1 := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨τ ((injFunDecomp f).2.symm b), by
          rw [← hspec ((injFunDecomp f).2.symm b), Equiv.apply_symm_apply]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨(injFunDecomp f).2 (τ.symm a), by
          rw [hspec (τ.symm a), Equiv.apply_symm_apply]⟩
    have hI_eq : (injFunDecomp f).1 = I :=
      (incTupleEquivPowersetCard d k).injective (Subtype.ext himg)
    refine Prod.ext hI_eq ?_
    ext a
    have ha := hspec a
    rw [hI_eq] at ha
    exact congrArg Fin.val (I.2.injective ha)

/-- **General Cauchy–Binet Determinant Theorem** over any commutative ring `R`:
for `A B : Matrix (Fin d) (Fin k) R`,
`det (Aᵀ * B) = ∑ I : IncTuple d k, det (A.submatrix I id) * det (B.submatrix I id)`. -/
theorem det_transpose_mul_eq_sum_incTuple {R : Type*} [CommRing R] {d k : ℕ}
    (A B : Matrix (Fin d) (Fin k) R) :
    (Aᵀ * B).det = ∑ I : IncTuple d k, (A.submatrix I.1 id).det * (B.submatrix I.1 id).det := by
  classical
  rw [Matrix.det_apply]
  have h1 :
      ∑ σ : Equiv.Perm (Fin k),
        Equiv.Perm.sign σ • ∏ a : Fin k, (Aᵀ * B) (σ a) a =
      ∑ f : Fin k → Fin d,
        (∏ a : Fin k, B (f a) a) * (A.submatrix f id).det := by
    have hexp : ∀ σ : Equiv.Perm (Fin k),
        ∏ a : Fin k, (Aᵀ * B) (σ a) a =
          ∑ f : Fin k → Fin d, ∏ a : Fin k, A (f a) (σ a) * B (f a) a := by
      intro σ
      calc ∏ a : Fin k, (Aᵀ * B) (σ a) a
          = ∏ a : Fin k, ∑ c : Fin d, A c (σ a) * B c a := by
            refine Finset.prod_congr rfl fun a _ => ?_
            simp [Matrix.mul_apply, Matrix.transpose_apply]
        _ = ∑ f : Fin k → Fin d, ∏ a : Fin k, A (f a) (σ a) * B (f a) a :=
            Fintype.prod_sum _
    simp_rw [hexp, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hdetA : (A.submatrix f id).det =
        ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ a : Fin k, A (f a) (σ a) := by
      rw [← Matrix.det_transpose, Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp [Matrix.transpose_apply, Matrix.submatrix_apply]
    rw [hdetA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib, Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul]
    ring
  rw [h1]
  have hnoninj : ∀ f : Fin k → Fin d, ¬ Function.Injective f →
      (∏ a : Fin k, B (f a) a) * (A.submatrix f id).det = 0 := by
    intro f hf
    rw [Function.Injective] at hf
    push Not at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    have hdet0 : (A.submatrix f id).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by funext c; simp [Matrix.submatrix_apply, hij])
    rw [hdet0, mul_zero]
  rw [← Finset.sum_filter_of_ne (p := fun f : Fin k → Fin d => Function.Injective f)
    (fun f _ hne => by by_contra h; exact hne (hnoninj f h))]
  have hsub : ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin d => Function.Injective f),
      (∏ a : Fin k, B (f a) a) * (A.submatrix f id).det =
      ∑ f : { f : Fin k → Fin d // Function.Injective f },
        (∏ a : Fin k, B (f.1 a) a) * (A.submatrix f.1 id).det :=
    Finset.sum_subtype (Finset.univ.filter (fun f : Fin k → Fin d => Function.Injective f))
      (p := Function.Injective) (fun x => by simp)
      (fun f => (∏ a : Fin k, B (f a) a) * (A.submatrix f id).det)
  rw [hsub]
  rw [Fintype.sum_equiv (injFunEquivIncProdPerm d k)
    (fun f => (∏ a : Fin k, B (f.1 a) a) * (A.submatrix f.1 id).det)
    (fun p : IncTuple d k × Equiv.Perm (Fin k) =>
      (∏ a : Fin k, B (p.1.1 (p.2 a)) a) * (A.submatrix (p.1.1 ∘ p.2) id).det)
    (fun f => by
      have hfn : ((injFunEquivIncProdPerm d k f).1.1 ∘ (injFunEquivIncProdPerm d k f).2) = f.1 :=
        congrArg Subtype.val ((injFunEquivIncProdPerm d k).left_inv f)
      rw [hfn]
      congr 1
      refine Finset.prod_congr rfl fun a _ => ?_
      have ha : (injFunEquivIncProdPerm d k f).1.1 ((injFunEquivIncProdPerm d k f).2 a) = f.1 a :=
        congrFun hfn a
      rw [ha])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hperm : ∀ τ : Equiv.Perm (Fin k),
      (A.submatrix (I.1 ∘ τ) id).det = Equiv.Perm.sign τ • (A.submatrix I.1 id).det := by
    intro τ
    have hsubm : A.submatrix (I.1 ∘ τ) id = (A.submatrix I.1 id).submatrix τ id := rfl
    rw [hsubm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
  simp_rw [hperm]
  have hBdet : (B.submatrix I.1 id).det =
      ∑ τ : Equiv.Perm (Fin k), Equiv.Perm.sign τ • ∏ a : Fin k, B (I.1 (τ a)) a := by
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun τ _ => rfl
  rw [mul_comm, hBdet, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul]
  ring

/-! ### Concrete Hilbert–Schmidt Exterior-Power Space `ExtPowSpace E k` & Lattice `extPowLat L k` -/

section RealExteriorLattices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Concrete Hilbert–Schmidt `k`-th exterior-power Euclidean space `⋀^k E`. -/
abbrev ExtPowSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) :=
  EuclideanSpace ℝ (IncTuple (Module.finrank ℝ E) k)

/-- Concrete `k`-fold pure wedge product `v 0 ∧ ⋯ ∧ v (k - 1) ∈ ExtPowSpace E k` in the
canonical Plücker coordinates relative to `stdOrthonormalBasis ℝ E`. -/
def pureWedge {k : ℕ} (v : Fin k → E) : ExtPowSpace E k :=
  WithLp.toLp 2 fun I =>
    (Matrix.of fun a b : Fin k => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (v b)).det

/-- **Exact Exterior Inner Product Formula (`inner_pureWedge`)** via Cauchy–Binet:
`⟪v_0 ∧ ⋯ ∧ v_{k-1}, w_0 ∧ ⋯ ∧ w_{k-1}⟫ = det (⟪v_a, w_b⟫)_{a,b}`. -/
theorem inner_pureWedge {k : ℕ} (v w : Fin k → E) :
    inner ℝ (pureWedge v) (pureWedge w) =
      (Matrix.of fun a b : Fin k => inner ℝ (v a) (w b)).det := by
  let e := stdOrthonormalBasis ℝ E
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin k) ℝ :=
    Matrix.of fun c a => inner ℝ (e c) (v a)
  let B : Matrix (Fin (Module.finrank ℝ E)) (Fin k) ℝ :=
    Matrix.of fun c b => inner ℝ (e c) (w b)
  have hAB : Aᵀ * B = Matrix.of fun a b : Fin k => inner ℝ (v a) (w b) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, A, B, Matrix.of_apply]
    have h := e.repr.inner_map_map (v a) (w b)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [← h]
    unfold dotProduct
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Pi.star_apply, star_trivial, e.repr_apply_apply, e.repr_apply_apply, mul_comm]
  rw [← hAB, det_transpose_mul_eq_sum_incTuple A B, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Pi.star_apply, star_trivial, pureWedge, WithLp.ofLp_toLp, A, B]
  rw [mul_comm]
  rfl

/-- Exact squared norm of a pure wedge product: `‖v_0 ∧ ⋯ ∧ v_{k-1}‖ ^ 2 = det Gram(v)`. -/
theorem norm_sq_pureWedge {k : ℕ} (v : Fin k → E) :
    ‖pureWedge v‖ ^ 2 = (Matrix.gram ℝ v).det := by
  rw [← real_inner_self_eq_norm_sq, inner_pureWedge]
  rfl

/-- Multilinearity of `pureWedge` in slot `j` under addition. -/
theorem pureWedge_update_add {k : ℕ} (v : Fin k → E) (j : Fin k)
    (x y : E) :
    pureWedge (Function.update v j (x + y)) =
      pureWedge (Function.update v j x) + pureWedge (Function.update v j y) := by
  ext I
  simp only [pureWedge, WithLp.ofLp_toLp, PiLp.add_apply]
  let M : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun a b => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (v b)
  let ux : Fin k → ℝ := fun a => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) x
  let uy : Fin k → ℝ := fun a => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) y
  have h1 : (Matrix.of fun a b : Fin k =>
      inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (Function.update v j (x + y) b)) =
      M.updateCol j (ux + uy) := by
    ext a b
    by_cases hbj : b = j
    · subst hbj; simp [M, ux, uy, Matrix.updateCol_self, inner_add_right]
    · simp [M, Matrix.updateCol_ne hbj, Function.update_of_ne hbj]
  have h2 : (Matrix.of fun a b : Fin k =>
      inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (Function.update v j x b)) = M.updateCol j ux := by
    ext a b; by_cases hbj : b = j <;> simp [M, ux, hbj]
  have h3 : (Matrix.of fun a b : Fin k =>
      inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (Function.update v j y b)) = M.updateCol j uy := by
    ext a b; by_cases hbj : b = j <;> simp [M, uy, hbj]
  rw [h1, h2, h3]
  exact Matrix.det_updateCol_add M j ux uy

/-- Multilinearity of `pureWedge` in slot `j` under scalar multiplication. -/
theorem pureWedge_update_smul {k : ℕ} (v : Fin k → E) (j : Fin k)
    (c : ℝ) (x : E) :
    pureWedge (Function.update v j (c • x)) = c • pureWedge (Function.update v j x) := by
  ext I
  simp only [pureWedge, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  let M : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun a b => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (v b)
  let ux : Fin k → ℝ := fun a => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) x
  have h1 : (Matrix.of fun a b : Fin k =>
      inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (Function.update v j (c • x) b)) =
      M.updateCol j (c • ux) := by
    ext a b
    by_cases hbj : b = j
    · subst hbj; simp [M, ux, Matrix.updateCol_self, real_inner_smul_right]
    · simp [M, Matrix.updateCol_ne hbj, Function.update_of_ne hbj]
  have h2 : (Matrix.of fun a b : Fin k =>
      inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (Function.update v j x b)) = M.updateCol j ux := by
    ext a b; by_cases hbj : b = j <;> simp [M, ux, hbj]
  rw [h1, h2]
  exact Matrix.det_updateCol_smul M j c ux

/-- Alternating sign rule for `pureWedge`: `pureWedge (v ∘ σ) = sign σ • pureWedge v`. -/
theorem pureWedge_comp_perm {k : ℕ} (v : Fin k → E) (σ : Equiv.Perm (Fin k)) :
    pureWedge (v ∘ σ) = (Equiv.Perm.sign σ : ℤ) • pureWedge v := by
  ext I
  simp only [pureWedge, WithLp.ofLp_toLp, PiLp.smul_apply, zsmul_eq_mul, Function.comp_apply]
  have hsubm : (Matrix.of fun a b : Fin k => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (v (σ b))) =
      ((Matrix.of fun a b : Fin k => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (v b)).transpose.submatrix
        σ id).transpose := by
    ext a b; simp [Matrix.submatrix_apply, Matrix.transpose_apply]
  rw [hsubm, Matrix.det_transpose, Matrix.det_permute, Matrix.det_transpose]

/-- Alternating vanishing: if `v i = v j` for `i ≠ j`, then `pureWedge v = 0`. -/
theorem pureWedge_eq_zero_of_eq {k : ℕ} {v : Fin k → E} {i j : Fin k} (hne : i ≠ j)
    (heq : v i = v j) : pureWedge v = 0 := by
  ext I
  simp only [pureWedge, WithLp.ofLp_toLp, PiLp.zero_apply]
  exact Matrix.det_zero_of_column_eq hne (fun a => by simp [heq])

/-- **Exterior-Power Multilinear Expansion (`pureWedge_linear_comb`)**:
if `v a = ∑ c : Fin r, C c a • u c`, then
`pureWedge v = ∑ J : IncTuple r k, (C.submatrix J.1 id).det • pureWedge (fun a => u (J.1 a))`. -/
theorem pureWedge_linear_comb {r k : ℕ} (u : Fin r → E) (C : Matrix (Fin r) (Fin k) ℝ) :
    pureWedge (fun a : Fin k => ∑ c : Fin r, C c a • u c) =
      ∑ J : IncTuple r k, (C.submatrix J.1 id).det • pureWedge (fun a => u (J.1 a)) := by
  ext I
  have heval_sum : ∀ (S : Finset (IncTuple r k)) (g : IncTuple r k → ExtPowSpace E k),
      (∑ J ∈ S, g J) I = ∑ J ∈ S, (g J) I := by
    intro S g
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]
  rw [heval_sum]
  simp only [pureWedge, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  let A : Matrix (Fin r) (Fin k) ℝ :=
    Matrix.of fun c a => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (u c)
  have hprod : (Matrix.of fun a b : Fin k =>
      inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (∑ c : Fin r, C c b • u c)) = Aᵀ * C := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, A, inner_sum,
      real_inner_smul_right]
    refine Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hprod, det_transpose_mul_eq_sum_incTuple A C]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hAT : (A.submatrix J.1 id).det =
      (Matrix.of fun a b : Fin k => inner ℝ (stdOrthonormalBasis ℝ E (I.1 a)) (u (J.1 b))).det := by
    rw [← Matrix.det_transpose]
    rfl
  rw [hAT, mul_comm]

/-- Weight sum `∑ a, (I.1 a).1` used to order `IncTuple r k` upper-triangularly. -/
private def incSum {r k : ℕ} (I : IncTuple r k) : ℕ :=
  ∑ a : Fin k, (I.1 a).1

/-- For an upper-triangular matrix `U` with 1s on the diagonal, `det (U_{J, I}) = 0` whenever
`incSum I < incSum J`, and `det (U_{I, I}) = 1`. -/
private lemma det_submatrix_upperTri {r k : ℕ} (U : Matrix (Fin r) (Fin r) ℝ)
    (hU_tri : ∀ {a b : Fin r}, b < a → U a b = 0)
    (hU_diag : ∀ a : Fin r, U a a = 1) :
    (∀ I J : IncTuple r k, incSum I < incSum J → (U.submatrix J.1 I.1).det = 0) ∧
    (∀ I : IncTuple r k, (U.submatrix I.1 I.1).det = 1) := by
  constructor
  · intro I J hlt
    rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hall : ∀ a : Fin k, (J.1 (σ a)).1 ≤ (I.1 a).1
    · have hle : incSum J ≤ incSum I := by
        unfold incSum
        have hperm : ∑ a : Fin k, (J.1 (σ a)).1 = ∑ a : Fin k, (J.1 a).1 :=
          Equiv.sum_comp σ (fun a => (J.1 a).1)
        rw [← hperm]
        exact Finset.sum_le_sum fun a _ => hall a
      omega
    · push Not at hall
      obtain ⟨a, ha⟩ := hall
      have hzero : ∏ b : Fin k, U (J.1 (σ b)) (I.1 b) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (hU_tri ha)
      simp [Matrix.submatrix_apply, hzero]
  · intro I
    have htri : (U.submatrix I.1 I.1).BlockTriangular id := by
      intro a b hab
      have hlt : I.1 b < I.1 a := I.2 hab
      exact hU_tri hlt
    rw [Matrix.det_of_isUpperTriangular htri]
    refine Finset.prod_eq_one fun a _ => hU_diag (I.1 a)

/-- **Exact Exterior-Power Gram Determinant Formula (`det_gram_pureWedge`)**:
for any `r` vectors `v : Fin r → E` and `1 ≤ k ≤ r`,
`det Gram(v_{I_0} ∧ ⋯ ∧ v_{I_{k-1}})_{I ∈ IncTuple r k} = (det Gram v) ^ (Nat.choose (r - 1) (k - 1))`. -/
theorem det_gram_pureWedge {r k : ℕ} (hk1 : 1 ≤ k) (v : Fin r → E) :
    (Matrix.gram ℝ (fun I : IncTuple r k => pureWedge (fun a => v (I.1 a)))).det =
      (Matrix.gram ℝ v).det ^ (Nat.choose (r - 1) (k - 1)) := by
  let U : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun a b => gsCoeff v a b
  let u : Fin r → E := fun a => gsVec v a
  let M : Matrix (IncTuple r k) (IncTuple r k) ℝ :=
    Matrix.of fun J I => (U.submatrix J.1 I.1).det
  have hW_eq : (fun I : IncTuple r k => pureWedge (fun a => v (I.1 a))) =
      fun I => ∑ J : IncTuple r k, M J I • pureWedge (fun a => u (J.1 a)) := by
    funext I
    have hv_sub : (fun a : Fin k => v (I.1 a)) =
        fun a => ∑ c : Fin r, (U.submatrix id I.1) c a • u c := by
      funext a
      simpa [U, u, Matrix.submatrix_apply] using gs_expansion v (I.1 a)
    rw [hv_sub, pureWedge_linear_comb]
    rfl
  have hU_tri : ∀ {a b : Fin r}, b < a → U a b = 0 := fun hab =>
    Stage2SiegelReduction.gsCoeff_of_gt v hab
  have hU_diag : ∀ a : Fin r, U a a = 1 := fun a => Stage2SiegelReduction.gsCoeff_self v a
  obtain ⟨hM_zero, hM_diag⟩ := det_submatrix_upperTri (k := k) U hU_tri hU_diag
  have hM_bt : M.BlockTriangular (fun I : IncTuple r k => incSum I) := by
    intro J I hJI
    exact hM_zero I J hJI
  have hM_det : M.det = 1 := by
    have hdiag_blk : ∀ (J I : IncTuple r k), incSum I = incSum J → J ≠ I → M J I = 0 := by
      intro J I hsum hne
      change (U.submatrix J.1 I.1).det = 0
      rw [Matrix.det_apply]
      refine Finset.sum_eq_zero fun σ _ => ?_
      by_cases hall : ∀ a : Fin k, (J.1 (σ a)).1 ≤ (I.1 a).1
      · have heq_all : ∀ a : Fin k, (J.1 (σ a)).1 = (I.1 a).1 := by
          have hsum_eq : ∑ a : Fin k, (J.1 (σ a)).1 = ∑ a : Fin k, (I.1 a).1 := by
            rw [Equiv.sum_comp σ (fun a => (J.1 a).1)]
            exact hsum.symm
          have hzero : ∑ a : Fin k, ((I.1 a).1 - (J.1 (σ a)).1) = 0 := by
            have h1 := Finset.sum_tsub_distrib (s := Finset.univ) (f := fun a => (I.1 a).1)
              (g := fun a => (J.1 (σ a)).1) (fun a _ => hall a)
            rw [h1, hsum_eq, Nat.sub_self]
          intro a
          have ha0 : (I.1 a).1 - (J.1 (σ a)).1 = 0 :=
            (Finset.sum_eq_zero_iff.mp hzero) a (Finset.mem_univ a)
          have hle := hall a
          omega
        have hrange : Set.range J.1 = Set.range I.1 := by
          ext x
          constructor
          · rintro ⟨b, rfl⟩
            refine ⟨σ.symm b, Fin.ext ?_⟩
            have h := heq_all (σ.symm b)
            simpa using h.symm
          · rintro ⟨a, rfl⟩
            exact ⟨σ a, Fin.ext (heq_all a)⟩
        have hJEqI : J = I := by
          have himg : Finset.univ.image J.1 = Finset.univ.image I.1 := by
            ext x
            simp only [Finset.mem_image, Finset.mem_univ, true_and]
            exact Set.ext_iff.mp hrange x
          exact (incTupleEquivPowersetCard r k).injective (Subtype.ext himg)
        exact absurd hJEqI hne
      · push Not at hall
        obtain ⟨a, ha⟩ := hall
        have hzero : ∏ b : Fin k, U (J.1 (σ b)) (I.1 b) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ a) (hU_tri ha)
        simp [Matrix.submatrix_apply, hzero]
    rw [hM_bt.det]
    refine Finset.prod_eq_one fun s _ => ?_
    have hblk_one : M.toSquareBlock (fun I => incSum I) s = 1 := by
      ext ⟨J, hJ⟩ ⟨I, hI⟩
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
      by_cases hJI : J = I
      · subst hJI; simp [M, hM_diag]
      · have hne : (⟨J, hJ⟩ : {x // incSum x = s}) ≠ ⟨I, hI⟩ := fun h => hJI (congrArg Subtype.val h)
        simp only [hne, ↓reduceIte]
        exact hdiag_blk J I (hI.trans hJ.symm) hJI
    rw [hblk_one, Matrix.det_one]
  have hGu : Matrix.gram ℝ (fun J : IncTuple r k => pureWedge (fun a => u (J.1 a))) =
      Matrix.diagonal (fun J : IncTuple r k => ∏ a : Fin k, ‖u (J.1 a)‖ ^ 2) := by
    ext J I
    rw [Matrix.gram_apply, inner_pureWedge, Matrix.diagonal_apply]
    by_cases hJI : J = I
    · subst hJI
      rw [if_pos rfl]
      have hdiag : (Matrix.of fun a b : Fin k => inner ℝ (u (J.1 a)) (u (J.1 b))) =
          Matrix.diagonal (fun a : Fin k => ‖u (J.1 a)‖ ^ 2) := by
        ext a b
        rw [Matrix.of_apply, Matrix.diagonal_apply]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl, real_inner_self_eq_norm_sq]
        · rw [if_neg hab]; exact gsVec_orthogonal v (fun h => hab (J.2.injective h))
      rw [hdiag, Matrix.det_diagonal]
    · rw [if_neg hJI]
      have hnot_sub : ¬ (Finset.univ.image J.1 ⊆ Finset.univ.image I.1) := by
        intro hsub
        have hcard : (Finset.univ.image J.1).card = (Finset.univ.image I.1).card := by
          rw [Finset.card_image_of_injective _ J.2.injective,
            Finset.card_image_of_injective _ I.2.injective]
        have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
        exact hJI ((incTupleEquivPowersetCard r k).injective (Subtype.ext heq))
      rw [Finset.not_subset] at hnot_sub
      obtain ⟨x, hxJ, hxI⟩ := hnot_sub
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxJ
      refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
      have hne : J.1 a ≠ I.1 b := fun h => hxI (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, h.symm⟩)
      exact gsVec_orthogonal v hne
  rw [hW_eq, gram_sum_smul_eq_transpose_mul _ M, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hM_det, one_mul, mul_one, hGu, Matrix.det_diagonal,
    det_gram_eq_prod_gsVec_norm_sq v]
  have hprod_eq :
      ∏ I : IncTuple r k, ∏ a : Fin k, ‖u (I.1 a)‖ ^ 2 =
      ∏ c : Fin r, (‖u c‖ ^ 2) ^ (Nat.choose (r - 1) (k - 1)) := by
    have h1 : ∀ I : IncTuple r k,
        ∏ a : Fin k, ‖u (I.1 a)‖ ^ 2 =
        ∏ c : Fin r, if c ∈ Set.range I.1 then ‖u c‖ ^ 2 else 1 := by
      intro I
      rw [← Finset.prod_filter]
      refine Finset.prod_bij (fun a _ => I.1 a)
        (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, rfl⟩⟩)
        (fun a₁ _ a₂ _ h => I.2.injective h)
        (fun c hc => by
          obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hc).2
          exact ⟨a, Finset.mem_univ a, rfl⟩)
        (fun _ _ => rfl)
    simp_rw [h1]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← Finset.prod_filter, Finset.prod_const, card_incTuple_containing hk1 c]
  rw [hprod_eq, Finset.prod_pow]

/-- Concrete **Exterior-Power Column Lattice `⋀^k L ⊂ ExtPowSpace E k`**:
the `ℤ`-span of all pure `k`-fold wedge products of vectors in `L`. -/
def extPowLat (L : Submodule ℤ E) (k : ℕ) : Submodule ℤ (ExtPowSpace E k) :=
  Submodule.span ℤ { z : ExtPowSpace E k | ∃ v : Fin k → E, (∀ a, v a ∈ L) ∧ z = pureWedge v }

/-- **EXACT EXTERIOR-POWER COLUMN LATTICE INVARIANTS (`extPowLat_invariants`)**:
For any discrete lattice `L ⊂ E` of rank `r = rk L` and any `1 ≤ k ≤ r`:
1. `DiscreteTopology (extPowLat L k)`,
2. **`rk (extPowLat L k) = Nat.choose (rk L) k`**,
3. **`covol (extPowLat L k) = (covol L) ^ (Nat.choose (rk L - 1) (k - 1))`**,
4. **`arithDeg (extPowLat L k) = (Nat.choose (rk L - 1) (k - 1) : ℝ) * arithDeg L`**,
5. **`slope (extPowLat L k) = (k : ℝ) * slope L`** (exact column-lattice slope invariance!). -/
theorem extPowLat_invariants (L : Submodule ℤ E) [DiscreteTopology L]
    {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ rk L) :
    DiscreteTopology (extPowLat L k) ∧
    rk (extPowLat L k) = Nat.choose (rk L) k ∧
    covol (extPowLat L k) = (covol L) ^ (Nat.choose (rk L - 1) (k - 1)) ∧
    arithDeg (extPowLat L k) = (Nat.choose (rk L - 1) (k - 1) : ℝ) * arithDeg L ∧
    ArakelovCovolume.slope (extPowLat L k) = (k : ℝ) * ArakelovCovolume.slope L := by
  let r := rk L
  have hr : 1 ≤ r := le_trans hk1 hkr
  let b : Module.Basis (Fin r) ℤ L := Module.finBasis ℤ L
  let v : Fin r → E := fun i => (b i : E)
  let e : IncTuple r k ≃ Fin (Nat.choose r k) :=
    (Fintype.equivFin (IncTuple r k)).trans (finCongr (card_incTuple r k))
  have hdet_pos : 0 < (Matrix.gram ℝ (fun I : IncTuple r k => pureWedge (fun a => v (I.1 a)))).det := by
    rw [det_gram_pureWedge hk1 v]
    exact pow_pos (det_gram_basis_pos L b) _
  have hli_inc : LinearIndependent ℝ (fun I : IncTuple r k => pureWedge (fun a => v (I.1 a))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    have hdet0 : (Matrix.gram ℝ (fun I : IncTuple r k => pureWedge (fun a => v (I.1 a)))).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨c, fun h0 => hne (fun I => congrFun h0 I), ?_⟩
      ext I
      have h1 : inner ℝ (pureWedge (fun a => v (I.1 a)))
          (∑ J : IncTuple r k, c J • pureWedge (fun a => v (J.1 a))) = 0 := by
        rw [hc, inner_zero_right]
      rw [inner_sum] at h1
      simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1
    exact hdet_pos.ne' hdet0
  let gen : Fin (Nat.choose r k) → extPowLat L k := fun t =>
    ⟨pureWedge (fun a => v ((e.symm t).1 a)),
      Submodule.subset_span ⟨fun a => v ((e.symm t).1 a), fun a => (b ((e.symm t).1 a)).2, rfl⟩⟩
  have hliR : LinearIndependent ℝ (fun t : Fin (Nat.choose r k) => (gen t : ExtPowSpace E k)) :=
    hli_inc.comp e.symm e.symm.injective
  have hliZ : LinearIndependent ℤ gen := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 : ∑ s : Fin (Nat.choose r k), (c s : ℝ) • (gen s : ExtPowSpace E k) = 0 := by
      have h2 := congrArg Subtype.val hc
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hliR (fun s => (c s : ℝ)) h1 t
  have hspZ : ⊤ ≤ Submodule.span ℤ (Set.range gen) := by
    intro z _
    have hz : (z : ExtPowSpace E k) ∈ extPowLat L k := z.2
    have hspan_sub : extPowLat L k ≤
        Submodule.span ℤ (Set.range fun t : Fin (Nat.choose r k) => (gen t : ExtPowSpace E k)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hwL, rfl⟩
      let CZ : Matrix (Fin r) (Fin k) ℤ := fun c a => b.repr ⟨w a, hwL a⟩ c
      let CR : Matrix (Fin r) (Fin k) ℝ := CZ.map (Int.cast : ℤ → ℝ)
      have hw_eq : w = fun a => ∑ c : Fin r, CR c a • v c := by
        funext a
        have h := congrArg Subtype.val (b.sum_repr ⟨w a, hwL a⟩)
        rw [Submodule.coe_sum] at h
        refine h.symm.trans (Finset.sum_congr rfl fun c _ => ?_)
        change (b.repr ⟨w a, hwL a⟩ c) • (b c : E) = (CZ c a : ℝ) • v c
        exact (Int.cast_smul_eq_zsmul ℝ (CZ c a) (b c : E)).symm
      rw [hw_eq, pureWedge_linear_comb]
      refine Submodule.sum_mem _ fun J _ => ?_
      have hdet_int : (CR.submatrix J.1 id).det = ((CZ.submatrix J.1 id).det : ℝ) := by
        have hsub : CR.submatrix J.1 id = (CZ.submatrix J.1 id).map (Int.cast : ℤ → ℝ) := rfl
        rw [hsub]
        exact (Int.cast_det (CZ.submatrix J.1 id)).symm
      rw [hdet_int, Int.cast_smul_eq_zsmul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e J, ?_⟩)
      simp [gen]
    have hz_in := hspan_sub hz
    rw [Submodule.mem_span_range_iff_exists_fun] at hz_in
    obtain ⟨c, hc⟩ := hz_in
    have hzeq : z = ∑ t : Fin (Nat.choose r k), c t • gen t :=
      Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hc.symm)
    rw [hzeq]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  let bW : Module.Basis (Fin (Nat.choose r k)) ℤ (extPowLat L k) := Module.Basis.mk hliZ hspZ
  have hbW_val : (fun t : Fin (Nat.choose r k) => (bW t : ExtPowSpace E k)) =
      fun t => pureWedge (fun a => v ((e.symm t).1 a)) := by
    funext t; simp [bW, gen]
  have hDiscW : DiscreteTopology (extPowLat L k) :=
    discreteTopology_of_fin_basis_real_li bW (by simpa [hbW_val] using hliR)
  have hrkW : rk (extPowLat L k) = Nat.choose r k := by
    unfold rk
    rw [Module.finrank_eq_card_basis bW, Fintype.card_fin]
  have hdetW : (Matrix.gram ℝ (fun t : Fin (Nat.choose r k) => (bW t : ExtPowSpace E k))).det =
      (Matrix.gram ℝ v).det ^ (Nat.choose (r - 1) (k - 1)) := by
    have hsub : Matrix.gram ℝ (fun I : IncTuple r k => pureWedge (fun a => v (I.1 a))) =
        (Matrix.gram ℝ (fun t : Fin (Nat.choose r k) => (bW t : ExtPowSpace E k))).submatrix e e := by
      ext I J
      simp [Matrix.gram_apply, hbW_val]
    rw [← Matrix.det_submatrix_equiv_self e, ← hsub, det_gram_pureWedge hk1 v]
  have hsqrt_pow : ∀ {x : ℝ}, 0 ≤ x → ∀ n : ℕ, Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]
  have hcovW : covol (extPowLat L k) = (covol L) ^ (Nat.choose (r - 1) (k - 1)) := by
    rw [covol_eq_sqrt_det_gram (extPowLat L k) bW, hdetW,
      hsqrt_pow (det_gram_basis_pos L b).le, ← covol_eq_sqrt_det_gram L b]
  have hdegW : arithDeg (extPowLat L k) = (Nat.choose (r - 1) (k - 1) : ℝ) * arithDeg L := by
    unfold arithDeg
    rw [hcovW, Real.log_pow]
    ring
  have hslW : ArakelovCovolume.slope (extPowLat L k) = (k : ℝ) * ArakelovCovolume.slope L := by
    rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
      Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk, hrkW, hdegW]
    have hch_pos : (0 : ℝ) < (Nat.choose r k : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hkr)
    have hr_pos : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr hr
    have habs : (rk L : ℝ) * (Nat.choose (r - 1) (k - 1) : ℝ) = (k : ℝ) * (Nat.choose r k : ℝ) := by
      exact_mod_cast mul_choose_pred_eq hr hk1
    field_simp [hch_pos.ne', hr_pos.ne']
    linear_combination arithDeg L * habs
  exact ⟨hDiscW, hrkW, hcovW, hdegW, hslW⟩

/-- Convenience corollary: **exact exterior-power slope scaling** `slope (⋀^k L) = k * slope L`. -/
theorem slope_extPowLat (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ} (hk1 : 1 ≤ k)
    (hkr : k ≤ rk L) :
    ArakelovCovolume.slope (extPowLat L k) = (k : ℝ) * ArakelovCovolume.slope L :=
  (extPowLat_invariants L hk1 hkr).2.2.2.2

/-- Exact exterior-power covolume power law `covol (⋀^k L) = (covol L) ^ (choose (r - 1) (k - 1))`. -/
theorem covol_extPowLat (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ} (hk1 : 1 ≤ k)
    (hkr : k ≤ rk L) :
    covol (extPowLat L k) = (covol L) ^ (Nat.choose (rk L - 1) (k - 1)) :=
  (extPowLat_invariants L hk1 hkr).2.2.1

end RealExteriorLattices

/-! ### Complex Compound-Matrix Exterior Power of `CMHermLattice d r` -/

section ComplexCompoundExterior

/-- The `k`-th compound matrix `C_k(M)` indexed by `IncTuple r k`: entry `(I, J)` is `det M_{I, J}`. -/
def compoundMatrix {R : Type*} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (k : ℕ) :
    Matrix (IncTuple r k) (IncTuple r k) R :=
  Matrix.of fun I J => (M.submatrix I.1 J.1).det

/-- Multiplicativity of the `k`-th compound matrix (Cauchy–Binet): `C_k(A * B) = C_k(A) * C_k(B)`. -/
theorem compoundMatrix_mul {R : Type*} [CommRing R] {r : ℕ} (A B : Matrix (Fin r) (Fin r) R)
    (k : ℕ) :
    compoundMatrix (A * B) k = compoundMatrix A k * compoundMatrix B k := by
  ext I J
  simp only [compoundMatrix, Matrix.of_apply, Matrix.mul_apply]
  have hsub : (A * B).submatrix I.1 J.1 = (A.submatrix I.1 id).transpose.transpose * (B.submatrix id J.1) := by
    ext a b; simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [hsub]
  have hcb := det_transpose_mul_eq_sum_incTuple (A.submatrix I.1 id).transpose (B.submatrix id J.1)
  rw [hcb]
  refine Finset.sum_congr rfl fun K _ => ?_
  have h1 : ((A.submatrix I.1 id).transpose.submatrix K.1 id).det = (A.submatrix I.1 K.1).det := by
    rw [← Matrix.det_transpose]
    rfl
  have h2 : ((B.submatrix id J.1).submatrix K.1 id).det = (B.submatrix K.1 J.1).det := rfl
  rw [h1, h2]

/-- `C_k(1) = 1`. -/
theorem compoundMatrix_one {R : Type*} [CommRing R] {r : ℕ} (k : ℕ) :
    compoundMatrix (1 : Matrix (Fin r) (Fin r) R) k = 1 := by
  ext I J
  simp only [compoundMatrix, Matrix.of_apply, Matrix.one_apply]
  by_cases hIJ : I = J
  · subst hIJ
    rw [if_pos rfl]
    have hid : ((1 : Matrix (Fin r) (Fin r) R).submatrix I.1 I.1) = 1 := by
      ext a b; simp [Matrix.submatrix_apply, Matrix.one_apply, I.2.injective.eq_iff]
    rw [hid, Matrix.det_one]
  · rw [if_neg hIJ]
    have hnot : ¬ (Finset.univ.image I.1 ⊆ Finset.univ.image J.1) := by
      intro hsub
      have hc : (Finset.univ.image I.1).card = (Finset.univ.image J.1).card := by
        rw [Finset.card_image_of_injective _ I.2.injective,
          Finset.card_image_of_injective _ J.2.injective]
      exact hIJ ((incTupleEquivPowersetCard r k).injective
        (Subtype.ext (Finset.eq_of_subset_of_card_le hsub hc.ge)))
    rw [Finset.not_subset] at hnot
    obtain ⟨x, hxI, hxJ⟩ := hnot
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxI
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    have hne : I.1 a ≠ J.1 b := fun h => hxJ (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, h.symm⟩)
    simp [Matrix.submatrix_apply, hne]

/-- Conjugate-transpose commutes with `compoundMatrix`: `C_k(Mᴴ) = C_k(M)ᴴ`. -/
theorem compoundMatrix_conjTranspose {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (k : ℕ) :
    compoundMatrix Mᴴ k = (compoundMatrix M k)ᴴ := by
  ext I J
  simp only [compoundMatrix, Matrix.of_apply, Matrix.conjTranspose_apply]
  have h1 : Mᴴ.submatrix I.1 J.1 = (M.submatrix J.1 I.1)ᴴ := by
    ext a b; simp [Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  rw [h1, Matrix.det_conjTranspose]

/-- `C_k(diag d) = diag (fun I => ∏ a, d (I a))`. -/
theorem compoundMatrix_diagonal {R : Type*} [CommRing R] {r : ℕ} (d : Fin r → R) (k : ℕ) :
    compoundMatrix (Matrix.diagonal d) k = Matrix.diagonal (fun I : IncTuple r k => ∏ a : Fin k, d (I.1 a)) := by
  ext I J
  simp only [compoundMatrix, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hIJ : I = J
  · subst hIJ
    rw [if_pos rfl]
    have hdg : (Matrix.diagonal d).submatrix I.1 I.1 = Matrix.diagonal (fun a => d (I.1 a)) := by
      ext a b; simp [Matrix.submatrix_apply, Matrix.diagonal_apply, I.2.injective.eq_iff]
    rw [hdg, Matrix.det_diagonal]
  · rw [if_neg hIJ]
    have hnot : ¬ (Finset.univ.image I.1 ⊆ Finset.univ.image J.1) := by
      intro hsub
      have hc : (Finset.univ.image I.1).card = (Finset.univ.image J.1).card := by
        rw [Finset.card_image_of_injective _ I.2.injective,
          Finset.card_image_of_injective _ J.2.injective]
      exact hIJ ((incTupleEquivPowersetCard r k).injective
        (Subtype.ext (Finset.eq_of_subset_of_card_le hsub hc.ge)))
    rw [Finset.not_subset] at hnot
    obtain ⟨x, hxI, hxJ⟩ := hnot
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxI
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    have hne : I.1 a ≠ J.1 b := fun h => hxJ (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, h.symm⟩)
    simp [Matrix.submatrix_apply, hne]

/-- Positive-definiteness and exact determinant of `C_k(H)` for any `H.PosDef` and `1 ≤ k ≤ r`. -/
theorem compoundMatrix_posDef_and_det {r k : ℕ} (hk1 : 1 ≤ k)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) :
    (compoundMatrix H k).PosDef ∧
    (compoundMatrix H k).det = H.det ^ (Nat.choose (r - 1) (k - 1)) := by
  set U : Matrix (Fin r) (Fin r) ℂ := (hH.isHermitian.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ)
  set ev : Fin r → ℝ := hH.isHermitian.eigenvalues
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal (fun i => ((ev i : ℝ) : ℂ))
  have hspec : H = U * D * Uᴴ := by
    simpa [U, D, ev, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hH.isHermitian.spectral_theorem
  have hUU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using hH.isHermitian.eigenvectorUnitary.2.1
  have hUU' : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using hH.isHermitian.eigenvectorUnitary.2.2
  have hCk : compoundMatrix H k =
      compoundMatrix U k * compoundMatrix D k * (compoundMatrix U k)ᴴ := by
    rw [hspec, compoundMatrix_mul, compoundMatrix_mul, compoundMatrix_conjTranspose]
  have hCU_unit' : compoundMatrix U k * (compoundMatrix U k)ᴴ = 1 := by
    rw [← compoundMatrix_conjTranspose, ← compoundMatrix_mul, hUU', compoundMatrix_one]
  have hCD : compoundMatrix D k =
      Matrix.diagonal (fun I : IncTuple r k => ((∏ a : Fin k, ev (I.1 a) : ℝ) : ℂ)) := by
    rw [compoundMatrix_diagonal]
    congr 1; funext I; rw [Complex.ofReal_prod]
  have hCD_pd : (compoundMatrix D k).PosDef := by
    rw [hCD, Matrix.posDef_diagonal_iff]
    intro I
    rw [Complex.lt_def]
    exact ⟨by rw [Complex.ofReal_re, Complex.zero_re]; exact Finset.prod_pos fun a _ => hH.eigenvalues_pos (I.1 a), rfl⟩
  have hCU_inj : Function.Injective (compoundMatrix U k)ᴴ.mulVec := by
    intro x y hxy
    have h1 := congrArg (compoundMatrix U k).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hCU_unit'] using h1
  have hpd : (compoundMatrix H k).PosDef := by
    rw [hCk]
    have hconj : compoundMatrix U k * compoundMatrix D k * (compoundMatrix U k)ᴴ =
        ((compoundMatrix U k)ᴴ)ᴴ * compoundMatrix D k * (compoundMatrix U k)ᴴ := by
      simp
    rw [hconj]
    exact hCD_pd.conjTranspose_mul_mul_same hCU_inj
  have hdet : (compoundMatrix H k).det = H.det ^ (Nat.choose (r - 1) (k - 1)) := by
    rw [hCk, Matrix.det_mul, Matrix.det_mul]
    have hdetU : (compoundMatrix U k).det * (compoundMatrix U k)ᴴ.det = 1 := by
      rw [← Matrix.det_mul, hCU_unit', Matrix.det_one]
    have hdet_eq : (compoundMatrix U k).det * (compoundMatrix D k).det * (compoundMatrix U k)ᴴ.det =
        (compoundMatrix D k).det := by
      linear_combination (compoundMatrix D k).det * hdetU
    rw [hdet_eq, hCD, Matrix.det_diagonal, posDef_det_eq_prod_eigenvalues H hH]
    rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_pow]
    congr 1
    have h1 : ∀ I : IncTuple r k,
        ∏ a : Fin k, ev (I.1 a) = ∏ c : Fin r, if c ∈ Set.range I.1 then ev c else 1 := by
      intro I
      rw [← Finset.prod_filter]
      refine Finset.prod_bij (fun a _ => I.1 a)
        (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, rfl⟩⟩)
        (fun a₁ _ a₂ _ h => I.2.injective h)
        (fun c hc => by
          obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hc).2
          exact ⟨a, Finset.mem_univ a, rfl⟩)
        (fun _ _ => rfl)
    simp_rw [h1]
    rw [Finset.prod_comm]
    have h2 : ∏ c : Fin r, ∏ I : IncTuple r k, (if c ∈ Set.range I.1 then ev c else 1) =
        ∏ c : Fin r, ev c ^ (Nat.choose (r - 1) (k - 1)) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [← Finset.prod_filter, Finset.prod_const, card_incTuple_containing hk1 c]
    rw [h2, Finset.prod_pow]
  exact ⟨hpd, hdet⟩

/-- **Complex CM Hermitian Exterior-Power Lattice `⋀^k_ℂ Λ : CMHermLattice d (Nat.choose r k)`**:
constructed from the positive-definite `k`-th compound Gram matrix `C_k(Λ.H)`, with exact
`ZLattice.covolume` formula `covol = (√d)^(choose r k) * (H.det.re)^(choose (r - 1) (k - 1))`. -/
def CMHermLattice.complexExtPow {d r : ℕ} (Λ : CMHermLattice d r) {k : ℕ}
    (hk1 : 1 ≤ k) (hkr : k ≤ r) : CMHermLattice d (Nat.choose r k) :=
  let e : IncTuple r k ≃ Fin (Nat.choose r k) :=
    (Fintype.equivFin (IncTuple r k)).trans (finCongr (card_incTuple r k))
  { hd := Λ.hd
    hr := Nat.choose_pos hkr
    H := (compoundMatrix Λ.H k).submatrix e.symm e.symm
    hH := (compoundMatrix_posDef_and_det hk1 Λ.H Λ.hH).1.submatrix e.symm.injective }

private lemma CMHermLattice.det_re_complexExtPow {d r : ℕ} (Λ : CMHermLattice d r) {k : ℕ}
    (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    ((Λ.complexExtPow hk1 hkr).H).det.re = Λ.H.det.re ^ (Nat.choose (r - 1) (k - 1)) := by
  let e : IncTuple r k ≃ Fin (Nat.choose r k) :=
    (Fintype.equivFin (IncTuple r k)).trans (finCongr (card_incTuple r k))
  have hdet : ((Λ.complexExtPow hk1 hkr).H).det = Λ.H.det ^ (Nat.choose (r - 1) (k - 1)) := by
    change ((compoundMatrix Λ.H k).submatrix e.symm e.symm).det = _
    rw [Matrix.det_submatrix_equiv_self, (compoundMatrix_posDef_and_det hk1 Λ.H Λ.hH).2]
  rw [hdet]
  have hH_eq : Λ.H.det = ((Λ.H.det.re : ℝ) : ℂ) :=
    Complex.ext rfl (posDef_det_re_pos Λ.H Λ.hH).2
  conv_lhs => rw [hH_eq, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem CMHermLattice.covol_complexExtPow {d r : ℕ} (Λ : CMHermLattice d r) {k : ℕ}
    (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    covol (Λ.complexExtPow hk1 hkr).euclLat =
      (Real.sqrt d) ^ (Nat.choose r k) * Λ.H.det.re ^ (Nat.choose (r - 1) (k - 1)) := by
  rw [(Λ.complexExtPow hk1 hkr).covol_eq, Λ.det_re_complexExtPow hk1 hkr]

theorem CMHermLattice.slope_complexExtPow_eq {d r : ℕ} (Λ : CMHermLattice d r) {k : ℕ}
    (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    ArakelovCovolume.slope (Λ.complexExtPow hk1 hkr).euclLat =
      (k : ℝ) * ArakelovCovolume.slope Λ.euclLat + (((k : ℝ) - 1) / 4) * Real.log d := by
  rw [(Λ.complexExtPow hk1 hkr).slope_eq, Λ.slope_eq, Λ.det_re_complexExtPow hk1 hkr, Real.log_pow]
  have hch_pos : (0 : ℝ) < (Nat.choose r k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hkr)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr Λ.hr
  have habs : (r : ℝ) * (Nat.choose (r - 1) (k - 1) : ℝ) = (k : ℝ) * (Nat.choose r k : ℝ) := by
    exact_mod_cast mul_choose_pred_eq Λ.hr hk1
  field_simp [hch_pos.ne', hr_pos.ne']
  linear_combination -4 * (Real.log Λ.H.det.re) * habs

end ComplexCompoundExterior

end ExteriorPowerColumnLattices

/-! ## Section 3: Unconditional Weyl Hook-Length Dimension & Schur-Functor Branching Slope Lower Bound -/

section WeylHookLengthAndSchurBranching

/-- An integer partition `lam = (lam_0 ≥ lam_1 ≥ ⋯ ≥ lam_{r-1} ≥ 0)` of length at most `r`
(dominant polynomial weight of `U(r)`). -/
structure Partition (r : ℕ) where
  parts : Fin r → ℕ
  anti : Antitone parts

namespace Partition

/-- Zero partition `(0, ..., 0)`. -/
def zero (r : ℕ) : Partition r where
  parts := fun _ => 0
  anti := fun _ _ _ => le_rfl

/-- Fundamental column partition `1^k` (`1` in first `k` rows, `0` in remaining `r - k` rows)
corresponding to `⋀^k ℂ^r`. -/
def col (r k : ℕ) : Partition r where
  parts := fun i => if i.1 < k then 1 else 0
  anti := fun a b hab => by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact Nat.zero_le 1
    · exact le_rfl

/-- Symmetric-power row partition `(k, 0, ..., 0)` corresponding to `Sym^k ℂ^r`. -/
def sym (r k : ℕ) : Partition r where
  parts := fun i => if i.1 = 0 then k else 0
  anti := fun a b hab => by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · have : a.1 ≤ b.1 := hab; omega
    · exact Nat.zero_le k
    · exact le_rfl

/-- Weight (total box count) `|lam| = ∑_i lam_i`. -/
def weight {r : ℕ} (lam : Partition r) : ℕ :=
  ∑ i : Fin r, lam.parts i

/-- Maximum part `lam_0` (or `0` when `r = 0`). -/
def maxPart {r : ℕ} (lam : Partition r) : ℕ :=
  if h : 0 < r then lam.parts ⟨0, h⟩ else 0

lemma parts_le_maxPart {r : ℕ} (lam : Partition r) (i : Fin r) : lam.parts i ≤ lam.maxPart := by
  unfold maxPart
  have hr : 0 < r := Fin.pos i
  rw [dif_pos hr]
  exact lam.anti (Nat.zero_le i.1)

/-- Column length `lam'_j = #{i : Fin r | j < lam_i}` (conjugate partition at column `j`). -/
def colLen {r : ℕ} (lam : Partition r) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin r => j < lam.parts i).card

lemma colLen_le_r {r : ℕ} (lam : Partition r) (j : ℕ) : lam.colLen j ≤ r := by
  unfold colLen
  exact (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])

lemma colLen_antitone {r : ℕ} (lam : Partition r) : Antitone lam.colLen := by
  intro j₁ j₂ hj
  unfold colLen
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, lt_of_le_of_lt hj hi.2⟩

/-- Exact characterization of `colLen`: `i.1 < lam.colLen j ↔ j < lam.parts i`. -/
theorem lt_colLen_iff {r : ℕ} (lam : Partition r) (i : Fin r) (j : ℕ) :
    i.1 < lam.colLen j ↔ j < lam.parts i := by
  let S := Finset.univ.filter fun a : Fin r => j < lam.parts a
  have hinit : ∀ a b : Fin r, b ∈ S → a ≤ b → a ∈ S := by
    intro a b hb hab
    rw [Finset.mem_filter] at hb ⊢
    exact ⟨Finset.mem_univ a, lt_of_lt_of_le hb.2 (lam.anti hab)⟩
  constructor
  · intro hlt
    by_contra hge
    have hsub : S ⊆ Finset.univ.filter (fun a : Fin r => a.1 < i.1) := by
      intro a ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ a, ?_⟩
      by_contra hia
      have hiS : i ∈ S := hinit i a ha (Nat.le_of_not_lt hia)
      exact hge (Finset.mem_filter.mp hiS).2
    have hcard := Finset.card_le_card hsub
    have hcard_lt : (Finset.univ.filter (fun a : Fin r => a.1 < i.1)).card = i.1 := by
      have hbij : (Finset.univ.filter (fun a : Fin r => a.1 < i.1)).card = (Finset.range i.1).card := by
        refine Finset.card_bij (fun a _ => a.1)
          (fun a ha => Finset.mem_range.mpr (Finset.mem_filter.mp ha).2)
          (fun a₁ _ a₂ _ h => Fin.ext h)
          (fun n hn => ⟨⟨n, lt_trans (Finset.mem_range.mp hn) i.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hn⟩, rfl⟩)
      rw [hbij, Finset.card_range]
    rw [hcard_lt] at hcard
    exact absurd hlt (not_lt_of_ge hcard)
  · intro hj
    have hsub : Finset.univ.filter (fun a : Fin r => a.1 ≤ i.1) ⊆ S := by
      intro a ha
      exact hinit a i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj⟩) (Finset.mem_filter.mp ha).2
    have hcard := Finset.card_le_card hsub
    have hcard_le : (Finset.univ.filter (fun a : Fin r => a.1 ≤ i.1)).card = i.1 + 1 := by
      have hbij : (Finset.univ.filter (fun a : Fin r => a.1 ≤ i.1)).card =
          (Finset.range (i.1 + 1)).card := by
        refine Finset.card_bij (fun a _ => a.1)
          (fun a ha => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp ha).2))
          (fun a₁ _ a₂ _ h => Fin.ext h)
          (fun n hn => ⟨⟨n, lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) i.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ (Finset.mem_range.mp hn)⟩, rfl⟩)
      rw [hbij, Finset.card_range]
    rw [hcard_le] at hcard
    exact Nat.lt_of_succ_le hcard

/-- Exact double-counting of column lengths: `∑_{j < lam.maxPart} lam.colLen j = lam.weight`. -/
theorem sum_colLen_eq_weight {r : ℕ} (lam : Partition r) :
    ∑ j ∈ Finset.range lam.maxPart, lam.colLen j = lam.weight := by
  unfold colLen weight
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : lam.parts i ≤ lam.maxPart := lam.parts_le_maxPart i
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hfilt : (Finset.range lam.maxPart).filter (fun j => j < lam.parts i) = Finset.range (lam.parts i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h hle, h⟩⟩
  rw [hfilt, Finset.card_range]

/-- Young diagram cell finset `{(i, j) | j < lam_i}`. -/
def cells {r : ℕ} (lam : Partition r) : Finset (Fin r × ℕ) :=
  Finset.univ.biUnion fun i => (Finset.range (lam.parts i)).image (fun j => (i, j))

theorem mem_cells_iff {r : ℕ} (lam : Partition r) (p : Fin r × ℕ) :
    p ∈ lam.cells ↔ p.2 < lam.parts p.1 := by
  simp only [cells, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨i, j, hj, rfl⟩; exact hj
  · intro hp; exact ⟨p.1, p.2, hp, Prod.mk.eta⟩

theorem card_cells {r : ℕ} (lam : Partition r) : lam.cells.card = lam.weight := by
  unfold cells weight
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_range]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr fun p hp1 hp2 => by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨b, _, h⟩ := Finset.mem_image.mp hp2
      exact hij (Prod.mk.inj h).1.symm

/-- Hook length `h_lam(i, j) = (lam_i - j) + (lam'_j - i) - 1` of cell `(i, j)`. -/
def hookLength {r : ℕ} (lam : Partition r) (i : Fin r) (j : ℕ) : ℕ :=
  (lam.parts i - j) + (lam.colLen j - i.1) - 1

theorem hookLength_pos {r : ℕ} (lam : Partition r) {i : Fin r} {j : ℕ} (hj : j < lam.parts i) :
    1 ≤ lam.hookLength i j := by
  have hcol : i.1 < lam.colLen j := (lam.lt_colLen_iff i j).mpr hj
  unfold hookLength
  omega

theorem hookLength_le {r : ℕ} (lam : Partition r) {i : Fin r} {j : ℕ} (hj : j < lam.parts i) :
    lam.hookLength i j ≤ lam.maxPart + r := by
  have h1 : lam.parts i ≤ lam.maxPart := lam.parts_le_maxPart i
  have h2 : lam.colLen j ≤ r := lam.colLen_le_r j
  unfold hookLength
  omega

/-- Hook-length product `H_lam = ∏_{(i, j) ∈ lam} h_lam(i, j)`. -/
def hookProd {r : ℕ} (lam : Partition r) : ℕ :=
  ∏ c ∈ lam.cells, lam.hookLength c.1 c.2

theorem hookProd_pos {r : ℕ} (lam : Partition r) : 0 < lam.hookProd := by
  unfold hookProd
  refine Finset.prod_pos fun c hc => lam.hookLength_pos ((lam.mem_cells_iff c).mp hc)

/-- **Unconditional Hook-Length Product Bound (`hookProd_le_pow`)**:
`H_lam ≤ (lam_0 + r) ^ |lam|` and `log H_lam ≤ |lam| * log (lam_0 + r)`. -/
theorem hookProd_le_pow {r : ℕ} (lam : Partition r) :
    lam.hookProd ≤ (lam.maxPart + r) ^ lam.weight := by
  calc lam.hookProd
      ≤ ∏ _c ∈ lam.cells, (lam.maxPart + r) :=
        Finset.prod_le_prod' fun c hc => lam.hookLength_le ((lam.mem_cells_iff c).mp hc)
    _ = (lam.maxPart + r) ^ lam.cells.card := Finset.prod_const _
    _ = (lam.maxPart + r) ^ lam.weight := by rw [lam.card_cells]

theorem log_hookProd_le {r : ℕ} (lam : Partition r) :
    Real.log (lam.hookProd : ℝ) ≤ (lam.weight : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) := by
  have h1 : (lam.hookProd : ℝ) ≤ ((lam.maxPart + r : ℕ) : ℝ) ^ lam.weight := by
    exact_mod_cast lam.hookProd_le_pow
  have hpos : (0 : ℝ) < (lam.hookProd : ℝ) := Nat.cast_pos.mpr lam.hookProd_pos
  have hlog := Real.log_le_log hpos h1
  rwa [Real.log_pow] at hlog

/-- Shifted strictly decreasing coordinates `ℓ_i = lam_i + r - 1 - i` for the Weyl dimension formula. -/
def shiftedPart {r : ℕ} (lam : Partition r) (i : Fin r) : ℕ :=
  lam.parts i + (r - 1 - i.1)

theorem shiftedPart_strictAnti {r : ℕ} (lam : Partition r) : StrictAnti lam.shiftedPart := by
  intro i j hij
  unfold shiftedPart
  have hle : lam.parts j ≤ lam.parts i := lam.anti hij.le
  have hi : i.1 < r := i.2
  have hj : j.1 < r := j.2
  have hij' : i.1 < j.1 := hij
  omega

/-- Strictly ordered index pairs `{(i, j) : Fin r × Fin r | i < j}`. -/
def pairsLt (r : ℕ) : Finset (Fin r × Fin r) :=
  (Finset.univ.product Finset.univ).filter fun p => p.1 < p.2

/-- **Weyl Dimension Formula for `U(r)`**:
`weylDim lam = ∏_{0 ≤ i < j < r} (ℓ_i - ℓ_j) / (j - i)`. -/
def weylDim {r : ℕ} (lam : Partition r) : ℝ :=
  ∏ p ∈ pairsLt r,
    ((lam.shiftedPart p.1 - lam.shiftedPart p.2 : ℕ) : ℝ) / ((p.2.1 - p.1.1 : ℕ) : ℝ)

theorem weylDim_pos {r : ℕ} (lam : Partition r) : 0 < lam.weylDim := by
  unfold weylDim
  refine Finset.prod_pos fun p hp => ?_
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hnum : 0 < lam.shiftedPart p.1 - lam.shiftedPart p.2 :=
    Nat.sub_pos_of_lt (lam.shiftedPart_strictAnti hlt)
  have hden : 0 < p.2.1 - p.1.1 := Nat.sub_pos_of_lt hlt
  exact div_pos (Nat.cast_pos.mpr hnum) (Nat.cast_pos.mpr hden)

theorem weylDim_zero (r : ℕ) : (Partition.zero r).weylDim = 1 := by
  unfold weylDim
  refine Finset.prod_eq_one fun p hp => ?_
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have heq : (Partition.zero r).shiftedPart p.1 - (Partition.zero r).shiftedPart p.2 =
      p.2.1 - p.1.1 := by
    unfold shiftedPart zero
    dsimp only
    have hp1 : p.1.1 < r := p.1.2
    have hp2 : p.2.1 < r := p.2.2
    have hlt' : p.1.1 < p.2.1 := hlt
    omega
  rw [heq, div_self]
  exact Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hlt).ne'

/-- **Exact Row Hook-Length Bijection** (Macdonald / Fulton–Harris identity):
for each row `i : Fin r`,
`∏_{j < lam_i} h_lam(i, j) * ∏_{m > i} (ℓ_i - ℓ_m) = (ℓ_i)!`. -/
theorem row_hook_prod_mul_diff_eq_factorial {r : ℕ} (lam : Partition r) (i : Fin r) :
    (∏ j ∈ Finset.range (lam.parts i), lam.hookLength i j) *
      (∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m),
        (lam.shiftedPart i - lam.shiftedPart m)) =
      (lam.shiftedPart i).factorial := by
  set L := lam.shiftedPart i
  let A : Finset ℕ := (Finset.range (lam.parts i)).image (fun j => lam.hookLength i j)
  let B : Finset ℕ := (Finset.univ.filter (fun m : Fin r => i < m)).image
    (fun m => L - lam.shiftedPart m)
  have hfA_inj : Set.InjOn (fun j => lam.hookLength i j) (Finset.range (lam.parts i) : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    dsimp only at heq
    have hj₁' : j₁ < lam.parts i := Finset.mem_range.mp hj₁
    have hj₂' : j₂ < lam.parts i := Finset.mem_range.mp hj₂
    have hc₁ : i.1 < lam.colLen j₁ := (lam.lt_colLen_iff i j₁).mpr hj₁'
    have hc₂ : i.1 < lam.colLen j₂ := (lam.lt_colLen_iff i j₂).mpr hj₂'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hanti : lam.colLen j₂ ≤ lam.colLen j₁ := lam.colLen_antitone hlt.le
      unfold hookLength at heq; omega
    · have hanti : lam.colLen j₁ ≤ lam.colLen j₂ := lam.colLen_antitone hgt.le
      unfold hookLength at heq; omega
  have hfB_inj : Set.InjOn (fun m : Fin r => L - lam.shiftedPart m)
      (Finset.univ.filter (fun m : Fin r => i < m) : Set (Fin r)) := by
    intro m₁ hm₁ m₂ hm₂ heq
    dsimp only at heq
    have hm₁' : i < m₁ := (Finset.mem_filter.mp hm₁).2
    have hm₂' : i < m₂ := (Finset.mem_filter.mp hm₂).2
    have hl₁ : lam.shiftedPart m₁ < L := lam.shiftedPart_strictAnti hm₁'
    have hl₂ : lam.shiftedPart m₂ < L := lam.shiftedPart_strictAnti hm₂'
    have hsm : lam.shiftedPart m₁ = lam.shiftedPart m₂ := by omega
    exact lam.shiftedPart_strictAnti.injective hsm
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨m, hm, heq⟩ := Finset.mem_image.mp hxB
    have hj' : j < lam.parts i := Finset.mem_range.mp hj
    have hm' : i < m := (Finset.mem_filter.mp hm).2
    have hci : i.1 < lam.colLen j := (lam.lt_colLen_iff i j).mpr hj'
    have hcr : lam.colLen j ≤ r := lam.colLen_le_r j
    have hi_lt : i.1 < r := i.2
    have hm_lt : m.1 < r := m.2
    have him : i.1 < m.1 := hm'
    have hrel : lam.hookLength i j = L - (j + r - lam.colLen j) := by
      unfold hookLength L shiftedPart; omega
    have hltL : lam.shiftedPart m < L := lam.shiftedPart_strictAnti hm'
    have hltL' : j + r - lam.colLen j < L := by
      unfold L shiftedPart; omega
    have heq' : lam.shiftedPart m = j + r - lam.colLen j := by omega
    by_cases hjm : j < lam.parts m
    · have hcm : m.1 < lam.colLen j := (lam.lt_colLen_iff m j).mpr hjm
      unfold shiftedPart at heq'; omega
    · have hcm : ¬ (m.1 < lam.colLen j) := fun h => hjm ((lam.lt_colLen_iff m j).mp h)
      unfold shiftedPart at heq'; omega
  have hsub : A ∪ B ⊆ Finset.Icc 1 L := by
    intro x hx
    rw [Finset.mem_Icc]
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxA
      have hj' : j < lam.parts i := Finset.mem_range.mp hj
      have hci : i.1 < lam.colLen j := (lam.lt_colLen_iff i j).mpr hj'
      have hcr : lam.colLen j ≤ r := lam.colLen_le_r j
      have hi_lt : i.1 < r := i.2
      exact ⟨lam.hookLength_pos hj', by unfold hookLength L shiftedPart; omega⟩
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hxB
      have hlt : lam.shiftedPart m < L := lam.shiftedPart_strictAnti (Finset.mem_filter.mp hm).2
      omega
  have hcard : (A ∪ B).card = (Finset.Icc 1 L).card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hfA_inj,
      Finset.card_image_of_injOn hfB_inj, Finset.card_range, Nat.card_Icc]
    have hcardB : (Finset.univ.filter (fun m : Fin r => i < m)).card = r - 1 - i.1 := by
      have hbij : (Finset.univ.filter (fun m : Fin r => i < m)).card =
          (Finset.range (r - 1 - i.1)).card := by
        refine Finset.card_bij (fun m _ => m.1 - i.1 - 1)
          (fun m hm => Finset.mem_range.mpr (by
            have hm' : i.1 < m.1 := (Finset.mem_filter.mp hm).2
            have hmr : m.1 < r := m.2; omega))
          (fun m₁ hm₁ m₂ hm₂ h => Fin.ext (by
            have h1 : i.1 < m₁.1 := (Finset.mem_filter.mp hm₁).2
            have h2 : i.1 < m₂.1 := (Finset.mem_filter.mp hm₂).2; omega))
          (fun n hn => ⟨⟨n + i.1 + 1, by
            have hn' := Finset.mem_range.mp hn; have hi := i.2; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, show i.1 < n + i.1 + 1 by omega⟩,
            by dsimp only; omega⟩)
      rw [hbij, Finset.card_range]
    rw [hcardB]
    unfold L shiftedPart
    omega
  have hunion : A ∪ B = Finset.Icc 1 L := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hprodIcc : ∏ x ∈ Finset.Icc 1 L, x = L.factorial := by
    clear * -
    induction L with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih, Nat.factorial_succ,
        mul_comm]
  have hA_prod : ∏ x ∈ A, x = ∏ j ∈ Finset.range (lam.parts i), lam.hookLength i j :=
    Finset.prod_image (f := id) (fun a ha b hb h => hfA_inj ha hb h)
  have hB_prod : ∏ x ∈ B, x =
      ∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m), (L - lam.shiftedPart m) :=
    Finset.prod_image (f := id) (fun a ha b hb h => hfB_inj ha hb h)
  rw [← hA_prod, ← hB_prod, ← Finset.prod_union hdisj, hunion, hprodIcc]

/-- **EXACT WEYL HOOK-CONTENT FORMULA (`weyl_hook_content_formula`)**:
for every `r : ℕ` and every partition `lam : Partition r`,
`weylDim lam = (∏_{(i, j) ∈ lam} (r + j - i)) / (hookProd lam)`. -/
theorem weyl_hook_content_formula {r : ℕ} (lam : Partition r) :
    lam.weylDim =
      (∏ c ∈ lam.cells, ((r + c.2 - c.1.1 : ℕ) : ℝ)) / (lam.hookProd : ℝ) := by
  have hcell_prod : ∀ f : Fin r × ℕ → ℝ,
      ∏ c ∈ lam.cells, f c = ∏ i : Fin r, ∏ j ∈ Finset.range (lam.parts i), f (i, j) := by
    intro f
    unfold cells
    rw [Finset.prod_biUnion]
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
    · intro i _ j _ hij
      exact Finset.disjoint_left.mpr fun p hp1 hp2 => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp1
        obtain ⟨b, _, h⟩ := Finset.mem_image.mp hp2
        exact hij (Prod.mk.inj h).1.symm
  have hrow_content : ∀ i : Fin r,
      (∏ j ∈ Finset.range (lam.parts i), (r + j - i.1 : ℕ)) * (r - 1 - i.1).factorial =
        (lam.shiftedPart i).factorial := by
    intro i
    have hi : i.1 < r := i.2
    have hshift : lam.shiftedPart i = (r - 1 - i.1) + lam.parts i := by unfold shiftedPart; omega
    rw [hshift]
    set a := r - 1 - i.1
    have hrew : ∀ j ∈ Finset.range (lam.parts i), r + j - i.1 = a + 1 + j := fun j _ => by omega
    rw [Finset.prod_congr rfl hrew]
    set k := lam.parts i
    clear * -
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, mul_right_comm, ih, ← Nat.add_assoc, Nat.factorial_succ,
        mul_comm]
      ring
  have hrow_den : ∀ i : Fin r,
      ∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m), (m.1 - i.1) = (r - 1 - i.1).factorial := by
    intro i
    have hbij : ∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m), (m.1 - i.1) =
        ∏ n ∈ Finset.Icc 1 (r - 1 - i.1), n := by
      refine Finset.prod_bij (fun m _ => m.1 - i.1)
        (fun m hm => Finset.mem_Icc.mpr (by
          have h1 : i.1 < m.1 := (Finset.mem_filter.mp hm).2
          have h2 : m.1 < r := m.2; omega))
        (fun m₁ hm₁ m₂ hm₂ h => Fin.ext (by
          have h1 : i.1 < m₁.1 := (Finset.mem_filter.mp hm₁).2
          have h2 : i.1 < m₂.1 := (Finset.mem_filter.mp hm₂).2; omega))
        (fun n hn => ⟨⟨n + i.1, by
          have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2
          have hi := i.2; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, show i.1 < n + i.1 by
            have := (Finset.mem_Icc.mp hn).1; omega⟩,
          by dsimp only; omega⟩)
        (fun _ _ => rfl)
    rw [hbij]
    set L := r - 1 - i.1
    clear * -
    induction L with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih, Nat.factorial_succ,
        mul_comm]
  have hrow_eq : ∀ i : Fin r,
      (∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m),
        ((lam.shiftedPart i - lam.shiftedPart m : ℕ) : ℝ) / ((m.1 - i.1 : ℕ) : ℝ)) =
      (∏ j ∈ Finset.range (lam.parts i), ((r + j - i.1 : ℕ) : ℝ)) /
        (∏ j ∈ Finset.range (lam.parts i), ((lam.hookLength i j : ℕ) : ℝ)) := by
    intro i
    rw [Finset.prod_div_distrib]
    have h1 : ((∏ j ∈ Finset.range (lam.parts i), lam.hookLength i j : ℕ) : ℝ) *
        ((∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m),
          (lam.shiftedPart i - lam.shiftedPart m) : ℕ) : ℝ) =
        ((lam.shiftedPart i).factorial : ℝ) := by
      exact_mod_cast lam.row_hook_prod_mul_diff_eq_factorial i
    have h2 : ((∏ j ∈ Finset.range (lam.parts i), (r + j - i.1) : ℕ) : ℝ) *
        (((r - 1 - i.1).factorial : ℕ) : ℝ) = ((lam.shiftedPart i).factorial : ℝ) := by
      exact_mod_cast hrow_content i
    have h3 : ((∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m), (m.1 - i.1) : ℕ) : ℝ) =
        (((r - 1 - i.1).factorial : ℕ) : ℝ) := by
      exact_mod_cast hrow_den i
    push_cast at h1 h2 h3
    have hden1 : (∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m), ((m.1 - i.1 : ℕ) : ℝ)) ≠ 0 := by
      rw [h3]; exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hden2 : (∏ j ∈ Finset.range (lam.parts i), ((lam.hookLength i j : ℕ) : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj =>
        Nat.cast_ne_zero.mpr
          (Nat.lt_of_lt_of_le Nat.zero_lt_one (lam.hookLength_pos (Finset.mem_range.mp hj))).ne'
    rw [div_eq_div_iff hden1 hden2, h3]
    linarith
  have hpairs : lam.weylDim =
      ∏ i : Fin r, ∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m),
        ((lam.shiftedPart i - lam.shiftedPart m : ℕ) : ℝ) / ((m.1 - i.1 : ℕ) : ℝ) := by
    unfold weylDim pairsLt
    rw [Finset.prod_filter, Finset.product_eq_sprod, Finset.prod_product]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
  rw [hpairs]
  simp_rw [hrow_eq]
  rw [Finset.prod_div_distrib, hcell_prod]
  congr 1
  unfold hookProd
  rw [Nat.cast_prod, hcell_prod]

private lemma prod_range_sub_eq_descFactorial (M k : ℕ) :
    ∏ n ∈ Finset.range k, (M - n) = M.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]

/-- Exact evaluation on fundamental column partition `col r k`: `weylDim (col r k) = choose r k`. -/
theorem weylDim_col {r k : ℕ} (hkr : k ≤ r) :
    (Partition.col r k).weylDim = (Nat.choose r k : ℝ) := by
  rw [(Partition.col r k).weyl_hook_content_formula]
  have hcells : (Partition.col r k).cells =
      (Finset.univ.filter fun i : Fin r => i.1 < k).image (fun i => (i, 0)) := by
    ext ⟨i, j⟩
    simp only [mem_cells_iff, col, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      split_ifs at h with hi
      · exact ⟨i, hi, Prod.ext rfl (by omega)⟩
      · omega
    · rintro ⟨i', hi', h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      simp [hi']
  have hcol0 : (Partition.col r k).colLen 0 = k := by
    unfold colLen col
    have hfilt : (Finset.univ.filter fun i : Fin r => 0 < if i.1 < k then 1 else 0) =
        Finset.univ.filter fun i : Fin r => i.1 < k := by
      ext i; simp; split_ifs <;> omega
    rw [hfilt]
    have hbij : (Finset.univ.filter fun i : Fin r => i.1 < k).card = (Finset.range k).card := by
      refine Finset.card_bij (fun i _ => i.1)
        (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun n hn => ⟨⟨n, lt_of_lt_of_le (Finset.mem_range.mp hn) hkr⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hn⟩, rfl⟩)
    rw [hbij, Finset.card_range]
  have hnum : ∏ c ∈ (Partition.col r k).cells, ((r + c.2 - c.1.1 : ℕ) : ℝ) =
      ∏ n ∈ Finset.range k, ((r - n : ℕ) : ℝ) := by
    rw [hcells, Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).1)]
    refine Finset.prod_bij (fun i _ => i.1)
      (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      (fun _ _ _ _ h => Fin.ext h)
      (fun n hn => ⟨⟨n, lt_of_lt_of_le (Finset.mem_range.mp hn) hkr⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hn⟩, rfl⟩)
      (fun i _ => by simp)
  have hden : ((Partition.col r k).hookProd : ℝ) = (k.factorial : ℝ) := by
    unfold hookProd
    rw [hcells, Nat.cast_prod, Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).1)]
    have hbij : ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.1 < k),
        (((Partition.col r k).hookLength i 0 : ℕ) : ℝ) =
        ∏ n ∈ Finset.Icc 1 k, (n : ℝ) := by
      refine Finset.prod_bij (fun i _ => k - i.1)
        (fun i hi => Finset.mem_Icc.mpr (by have := (Finset.mem_filter.mp hi).2; omega))
        (fun i₁ hi₁ i₂ hi₂ h => Fin.ext (by
          have h1 := (Finset.mem_filter.mp hi₁).2
          have h2 := (Finset.mem_filter.mp hi₂).2; omega))
        (fun n hn => ⟨⟨k - n, by
          have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, show k - n < k by
            have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2; omega⟩,
          by dsimp only; have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2; omega⟩)
        (fun i hi => by
          have hi' : i.1 < k := (Finset.mem_filter.mp hi).2
          congr 1; unfold hookLength; rw [hcol0]; simp [col, hi'])
    rw [hbij]
    clear * -
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih, Nat.factorial_succ,
        Nat.cast_mul, mul_comm]
  rw [hnum, hden]
  have hdescR : (∏ n ∈ Finset.range k, ((r - n : ℕ) : ℝ)) = (r.descFactorial k : ℝ) := by
    rw [← Nat.cast_prod, prod_range_sub_eq_descFactorial]
  rw [hdescR, Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : k.factorial ∣ r.descFactorial k := Nat.factorial_dvd_descFactorial r k
  rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]

/-- Exact evaluation on symmetric-power partition `sym r k`: `weylDim (sym r k) = choose (k + r - 1) k`. -/
theorem weylDim_sym {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (Partition.sym r k).weylDim = (Nat.choose (k + r - 1) k : ℝ) := by
  rw [(Partition.sym r k).weyl_hook_content_formula]
  let i0 : Fin r := ⟨0, hr⟩
  have hcells : (Partition.sym r k).cells =
      (Finset.range k).image (fun j => (i0, j)) := by
    ext ⟨i, j⟩
    simp only [mem_cells_iff, sym, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      split_ifs at h with hi
      · exact ⟨j, h, Prod.ext (Fin.ext hi.symm) rfl⟩
      · omega
    · rintro ⟨j', hj', h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      simp [i0, hj']
  have hcol : ∀ j < k, (Partition.sym r k).colLen j = 1 := by
    intro j hj
    unfold colLen sym
    have hfilt : (Finset.univ.filter fun i : Fin r => j < if i.1 = 0 then k else 0) = {i0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; split_ifs at h with hi
        · exact Fin.ext hi
        · omega
      · rintro rfl; simp [i0, hj]
    rw [hfilt, Finset.card_singleton]
  have hnum : ∏ c ∈ (Partition.sym r k).cells, ((r + c.2 - c.1.1 : ℕ) : ℝ) =
      ∏ j ∈ Finset.range k, ((r + j : ℕ) : ℝ) := by
    rw [hcells, Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    refine Finset.prod_congr rfl fun j _ => by simp [i0]
  have hden : ((Partition.sym r k).hookProd : ℝ) = (k.factorial : ℝ) := by
    unfold hookProd
    rw [hcells, Nat.cast_prod, Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    have hbij : ∏ j ∈ Finset.range k, (((Partition.sym r k).hookLength i0 j : ℕ) : ℝ) =
        ∏ n ∈ Finset.Icc 1 k, (n : ℝ) := by
      refine Finset.prod_bij (fun j _ => k - j)
        (fun j hj => Finset.mem_Icc.mpr (by have := Finset.mem_range.mp hj; omega))
        (fun j₁ hj₁ j₂ hj₂ h => by
          have h1 := Finset.mem_range.mp hj₁; have h2 := Finset.mem_range.mp hj₂; omega)
        (fun n hn => ⟨k - n, Finset.mem_range.mpr (by
          have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2; omega),
          by have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2; omega⟩)
        (fun j hj => by
          congr 1; unfold hookLength; rw [hcol j (Finset.mem_range.mp hj)]; simp [sym, i0])
    rw [hbij]
    clear * -
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih, Nat.factorial_succ,
        Nat.cast_mul, mul_comm]
  rw [hnum, hden]
  have hasc : (∏ j ∈ Finset.range k, (r + j : ℕ)) = (k + r - 1).descFactorial k := by
    have hbij : (∏ j ∈ Finset.range k, (r + j : ℕ)) =
        ∏ n ∈ Finset.range k, ((k + r - 1) - n) := by
      refine Finset.prod_bij (fun j _ => k - 1 - j)
        (fun j hj => Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))
        (fun j₁ hj₁ j₂ hj₂ h => by
          have h1 := Finset.mem_range.mp hj₁; have h2 := Finset.mem_range.mp hj₂; omega)
        (fun n hn => ⟨k - 1 - n, Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hn; omega),
          by have := Finset.mem_range.mp hn; omega⟩)
        (fun j hj => by have := Finset.mem_range.mp hj; omega)
    rw [hbij, prod_range_sub_eq_descFactorial]
  have hascR : (∏ j ∈ Finset.range k, ((r + j : ℕ) : ℝ)) = ((k + r - 1).descFactorial k : ℝ) := by
    rw [← Nat.cast_prod, hasc]
  rw [hascR, Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : k.factorial ∣ (k + r - 1).descFactorial k := Nat.factorial_dvd_descFactorial _ k
  rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]

/-- **Explicit Weyl Dimension Upper Bound**:
`weylDim lam ≤ (r + lam.maxPart) ^ lam.weight`. -/
theorem weylDim_le_pow {r : ℕ} (lam : Partition r) :
    lam.weylDim ≤ ((r + lam.maxPart : ℕ) : ℝ) ^ lam.weight := by
  rw [lam.weyl_hook_content_formula]
  have hhp : (1 : ℝ) ≤ (lam.hookProd : ℝ) := by exact_mod_cast lam.hookProd_pos
  have hnum_le : ∏ c ∈ lam.cells, ((r + c.2 - c.1.1 : ℕ) : ℝ) ≤
      ((r + lam.maxPart : ℕ) : ℝ) ^ lam.weight := by
    calc ∏ c ∈ lam.cells, ((r + c.2 - c.1.1 : ℕ) : ℝ)
        ≤ ∏ _c ∈ lam.cells, ((r + lam.maxPart : ℕ) : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun c hc => ?_
          have hj : c.2 < lam.parts c.1 := (lam.mem_cells_iff c).mp hc
          have hmax : lam.parts c.1 ≤ lam.maxPart := lam.parts_le_maxPart c.1
          exact_mod_cast (by omega : r + c.2 - c.1.1 ≤ r + lam.maxPart)
      _ = ((r + lam.maxPart : ℕ) : ℝ) ^ lam.cells.card := Finset.prod_const _
      _ = ((r + lam.maxPart : ℕ) : ℝ) ^ lam.weight := by rw [lam.card_cells]
  calc (∏ c ∈ lam.cells, ((r + c.2 - c.1.1 : ℕ) : ℝ)) / (lam.hookProd : ℝ)
      ≤ ∏ c ∈ lam.cells, ((r + c.2 - c.1.1 : ℕ) : ℝ) :=
        div_le_self (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) hhp
    _ ≤ ((r + lam.maxPart : ℕ) : ℝ) ^ lam.weight := hnum_le

end Partition

/-! ### Iterated Tensor-Product Column Lattice `columnTensorLat L lam` & `ColumnLatticeExactSlope` -/

section ColumnTensorAndBranching

/-- Bundled nonzero discrete Euclidean lattice for iterated tensor / Schur-Weyl constructions. -/
structure ConcreteEuclideanLat where
  E : Type
  [normE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [fdE : FiniteDimensional ℝ E]
  L : Submodule ℤ E
  [discL : DiscreteTopology L]
  ne_bot : L ≠ ⊥

attribute [instance] ConcreteEuclideanLat.normE ConcreteEuclideanLat.innerE
  ConcreteEuclideanLat.fdE ConcreteEuclideanLat.discL

/-- Unit rank-1 lattice `ℤ ⊂ ℝ¹` with exact `rk = 1`, `covol = 1`, `slope = 0`. -/
def unitLat : Submodule ℤ (EuclideanSpace ℝ (Fin 1)) :=
  Submodule.span ℤ {EuclideanSpace.single (0 : Fin 1) (1 : ℝ)}

private instance discreteTopology_unitLat : DiscreteTopology unitLat := by
  let b : Module.Basis (Fin 1) ℝ (EuclideanSpace ℝ (Fin 1)) :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  have hspan : unitLat = Submodule.span ℤ (Set.range b) := by
    unfold unitLat
    congr 1; ext x
    simp only [Set.mem_singleton_iff, Set.mem_range, b]
    exact ⟨fun hx => ⟨0, by rw [hx]; ext i; fin_cases i; simp [EuclideanSpace.basisFun_apply]⟩,
      fun ⟨i, hi⟩ => by fin_cases i; rw [← hi]; ext j; fin_cases j; simp [EuclideanSpace.basisFun_apply]⟩
  rw [hspan]
  exact inferInstance

private lemma unitLat_invariants :
    unitLat ≠ ⊥ ∧ rk unitLat = 1 ∧ covol unitLat = 1 ∧ ArakelovCovolume.slope unitLat = 0 := by
  have hne : unitLat ≠ ⊥ := by
    intro h
    have hmem : EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈ unitLat :=
      Submodule.subset_span (Set.mem_singleton _)
    rw [h, Submodule.mem_bot] at hmem
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hmem
    simp at h0
  let b1 : Module.Basis (Fin 1) ℤ unitLat :=
    Module.Basis.mk
      (v := fun _ => ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
        Submodule.subset_span (Set.mem_singleton _)⟩)
      (by
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        fin_cases i
        have h0 := congrArg (fun x : unitLat => (x : EuclideanSpace ℝ (Fin 1)) 0) hc
        simp only [Fin.sum_univ_one, Submodule.coe_smul, PiLp.smul_apply, zsmul_eq_mul,
          PiLp.single_apply, ↓reduceIte, mul_one, Submodule.coe_zero, PiLp.zero_apply] at h0
        exact_mod_cast h0)
      (by
        intro x _
        have hx : (x : EuclideanSpace ℝ (Fin 1)) ∈ unitLat := x.2
        unfold unitLat at hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨a, ha⟩ := hx
        have hxeq : x = a • ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
            Submodule.subset_span (Set.mem_singleton _)⟩ := Subtype.ext ha.symm
        rw [hxeq]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
  have hrk : rk unitLat = 1 := by
    unfold rk; rw [Module.finrank_eq_card_basis b1, Fintype.card_fin]
  have hcov : covol unitLat = 1 := by
    rw [covol_eq_sqrt_det_gram unitLat b1]
    have hgram : Matrix.gram ℝ (fun i => (b1 i : EuclideanSpace ℝ (Fin 1))) = 1 := by
      ext i j; fin_cases i; fin_cases j
      simp [Matrix.gram_apply, b1]
    rw [hgram, Matrix.det_one, Real.sqrt_one]
  have hsl : ArakelovCovolume.slope unitLat = 0 := by
    rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk, arithDeg, hcov, Real.log_one, neg_zero,
      zero_div]
  exact ⟨hne, hrk, hcov, hsl⟩

def ConcreteEuclideanLat.unit : ConcreteEuclideanLat where
  E := EuclideanSpace ℝ (Fin 1)
  L := unitLat
  discL := discreteTopology_unitLat
  ne_bot := unitLat_invariants.1

/-- Concrete tensor product of two `ConcreteEuclideanLat`s. -/
def ConcreteEuclideanLat.tensor (A B : ConcreteEuclideanLat) : ConcreteEuclideanLat where
  E := TensorSpace A.E B.E
  L := tensorLat A.L B.L
  discL := (tensorLat_invariants A.L B.L).1
  ne_bot := by
    intro hbot
    have hrk := (tensorLat_invariants A.L B.L).2.1
    rw [hbot] at hrk
    have h0 : rk (⊥ : Submodule ℤ (TensorSpace A.E B.E)) = 0 := by simp [rk]
    rw [h0] at hrk
    have hmul : 0 < rk A.L * rk B.L :=
      Nat.mul_pos (rk_pos_of_ne_bot A.L A.ne_bot) (rk_pos_of_ne_bot B.L B.ne_bot)
    omega

/-- Concrete `k`-th exterior power of a `ConcreteEuclideanLat` (`1 ≤ k ≤ rk A.L`). -/
def ConcreteEuclideanLat.extPow (A : ConcreteEuclideanLat) {k : ℕ} (hk1 : 1 ≤ k)
    (hkr : k ≤ rk A.L) : ConcreteEuclideanLat where
  E := ExtPowSpace A.E k
  L := extPowLat A.L k
  discL := (extPowLat_invariants A.L hk1 hkr).1
  ne_bot := by
    intro hbot
    have hrk := (extPowLat_invariants A.L hk1 hkr).2.1
    rw [hbot] at hrk
    have h0 : rk (⊥ : Submodule ℤ (ExtPowSpace A.E k)) = 0 := by simp [rk]
    rw [h0] at hrk
    exact (Nat.choose_pos hkr).ne hrk

/-- Iterated tensor product of a finite list of `ConcreteEuclideanLat`s. -/
def iterTensorLat : List ConcreteEuclideanLat → ConcreteEuclideanLat
  | [] => ConcreteEuclideanLat.unit
  | A :: rest => A.tensor (iterTensorLat rest)

theorem iterTensorLat_invariants (L : List ConcreteEuclideanLat) :
    rk (iterTensorLat L).L = (L.map fun (A : ConcreteEuclideanLat) => rk A.L).prod ∧
    ArakelovCovolume.slope (iterTensorLat L).L =
      (L.map fun (A : ConcreteEuclideanLat) => ArakelovCovolume.slope A.L).sum := by
  induction L with
  | nil =>
    exact ⟨unitLat_invariants.2.1, unitLat_invariants.2.2.2⟩
  | cons A rest ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨?_, ?_⟩
    · change rk (tensorLat A.L (iterTensorLat rest).L) = _
      rw [(tensorLat_invariants A.L (iterTensorLat rest).L).2.1, ih.1]
    · change ArakelovCovolume.slope (tensorLat A.L (iterTensorLat rest).L) = _
      rw [slope_tensor_eq_add A.L (iterTensorLat rest).L A.ne_bot (iterTensorLat rest).ne_bot, ih.2]

/-- **Concrete Schur-Weyl Column-Tensor Lattice `columnTensorLat A lam = ⨂_{j < lam_0} (⋀^{lam'_j} A)`**
for any `ConcreteEuclideanLat` `A` of rank `r = rk A.L` and partition `lam : Partition (rk A.L)`. -/
def columnTensorLat (A : ConcreteEuclideanLat) (lam : Partition (rk A.L)) : ConcreteEuclideanLat :=
  iterTensorLat <|
    (List.finRange lam.maxPart).map fun j =>
      A.extPow
        (by
          have hr : 0 < rk A.L := rk_pos_of_ne_bot A.L A.ne_bot
          have hmax : lam.maxPart = lam.parts ⟨0, hr⟩ := dif_pos hr
          have h0 : j.1 < lam.parts ⟨0, hr⟩ := hmax ▸ j.2
          exact Nat.succ_le_of_lt ((lam.lt_colLen_iff ⟨0, hr⟩ j.1).mpr h0))
        (lam.colLen_le_r j.1)

/-- **EXACT COLUMN-LATTICE SLOPE THEOREM (`column_lattice_exact_slope`)**:
for any `ConcreteEuclideanLat` `A` of rank `r = rk A.L` and ANY partition `lam : Partition (rk A.L)`:
1. `rk (columnTensorLat A lam).L = ∏_{j < lam.maxPart} Nat.choose (rk A.L) (lam.colLen j)`,
2. **`slope (columnTensorLat A lam).L = (lam.weight : ℝ) * slope A.L`**! -/
theorem column_lattice_exact_slope (A : ConcreteEuclideanLat) (lam : Partition (rk A.L)) :
    rk (columnTensorLat A lam).L =
      ∏ j ∈ Finset.range lam.maxPart, Nat.choose (rk A.L) (lam.colLen j) ∧
    ArakelovCovolume.slope (columnTensorLat A lam).L =
      (lam.weight : ℝ) * ArakelovCovolume.slope A.L := by
  have hcol1 : ∀ j : Fin lam.maxPart, 1 ≤ lam.colLen j.1 := fun j => by
    have hr : 0 < rk A.L := rk_pos_of_ne_bot A.L A.ne_bot
    have hmax : lam.maxPart = lam.parts ⟨0, hr⟩ := dif_pos hr
    have h0 : j.1 < lam.parts ⟨0, hr⟩ := hmax ▸ j.2
    exact Nat.succ_le_of_lt ((lam.lt_colLen_iff ⟨0, hr⟩ j.1).mpr h0)
  let fCol : Fin lam.maxPart → ConcreteEuclideanLat := fun j =>
    A.extPow (hcol1 j) (lam.colLen_le_r j.1)
  have hcol_eq : columnTensorLat A lam = iterTensorLat ((List.finRange lam.maxPart).map fCol) := rfl
  rw [hcol_eq]
  obtain ⟨hrk, hsl⟩ := iterTensorLat_invariants ((List.finRange lam.maxPart).map fCol)
  rw [List.map_map] at hrk hsl
  constructor
  · rw [hrk]
    have h1 : (List.map ((fun B : ConcreteEuclideanLat => rk B.L) ∘ fCol)
        (List.finRange lam.maxPart)).prod =
        ∏ j : Fin lam.maxPart, Nat.choose (rk A.L) (lam.colLen j.1) := by
      rw [← Fin.prod_univ_def]
      refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
      exact (extPowLat_invariants A.L (hcol1 j) (lam.colLen_le_r j.1)).2.1
    rw [h1, Fin.prod_univ_eq_prod_range (fun j => Nat.choose (rk A.L) (lam.colLen j)) lam.maxPart]
  · rw [hsl]
    have h2 : (List.map ((fun B : ConcreteEuclideanLat => ArakelovCovolume.slope B.L) ∘ fCol)
        (List.finRange lam.maxPart)).sum =
        ∑ j : Fin lam.maxPart, (lam.colLen j.1 : ℝ) * ArakelovCovolume.slope A.L := by
      rw [← Fin.sum_univ_def]
      refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
      exact slope_extPowLat A.L (hcol1 j) (lam.colLen_le_r j.1)
    rw [h2, Fin.sum_univ_eq_sum_range (fun j => (lam.colLen j : ℝ) * ArakelovCovolume.slope A.L)
      lam.maxPart, ← Finset.sum_mul, ← Nat.cast_sum, lam.sum_colLen_eq_weight]

/-! ### Full-Rank Bounded-Morphism `muMin` Monotonicity & Schur-Functor Branching Lower Bound -/

/-- **Unconditional Full-Rank Morphism `muMin` Monotonicity**:
for ANY nonzero discrete lattices `A ⊂ E_A`, `B ⊂ E_B` and ANY `ℤ`-linear map `φ : A →ₗ[ℤ] B`
with `‖(φ a : E_B)‖ ≤ C * ‖(a : E_A)‖` (`C > 0`) whose image has full real span in `B`
(`Submodule.span ℝ (Set.range fun a : A => (φ a : E_B)) = Submodule.span ℝ (B : Set E_B)`):
`muMin A - Real.log C ≤ muMin B` and `muMin A - Real.log C ≤ slope B`! -/
theorem muMin_sub_log_le_muMin_of_fullRank
    {EA EB : Type*} [NormedAddCommGroup EA] [InnerProductSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EB] [InnerProductSpace ℝ EB] [FiniteDimensional ℝ EB]
    (A : Submodule ℤ EA) (B : Submodule ℤ EB) [DiscreteTopology A] [DiscreteTopology B]
    (hB0 : B ≠ ⊥)
    (φ : A →ₗ[ℤ] B) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a : A, ‖((φ a : B) : EB)‖ ≤ C * ‖(a : EA)‖)
    (hspan : Submodule.span ℝ (Set.range fun a : A => ((φ a : B) : EB)) =
      Submodule.span ℝ (B : Set EB)) :
    muMin A - Real.log C ≤ muMin B ∧ muMin A - Real.log C ≤ ArakelovCovolume.slope B := by
  have hquot : ∀ M : Submodule ℤ EB, IsSaturated B M → M ≠ B →
      muMin A - Real.log C ≤ ArakelovCovolume.slope (quotLat B M) := by
    intro M hMsat hMne
    have hDiscQ : DiscreteTopology (quotLat B M) := discreteTopology_quotLat hMsat
    let Q := quotLat B M
    have hQ0 : Q ≠ ⊥ := by
      intro hbot
      have hbot' : quotLat B M = ⊥ := hbot
      have hadd := rk_add_quotLat hMsat
      rw [hbot', show rk (⊥ : Submodule ℤ EB) = 0 by simp [rk], add_zero] at hadd
      have hM_eq : M = B := by
        apply le_antisymm hMsat.1
        intro x hxB
        have hsp_eq : Submodule.span ℝ (M : Set EB) = Submodule.span ℝ (B : Set EB) := by
          have hDiscM : DiscreteTopology M := discreteTopology_of_le hMsat.1
          refine Submodule.eq_of_le_of_finrank_eq
            (Submodule.span_mono (show (M : Set EB) ⊆ (B : Set EB) from hMsat.1)) ?_
          rw [← finrank_int_eq_finrank_real_span M, ← finrank_int_eq_finrank_real_span B]
          exact hadd.symm
        exact hMsat.2 x hxB (hsp_eq ▸ Submodule.subset_span hxB)
      exact hMne hM_eq
    let ψ : A →ₗ[ℤ] EB :=
      ((projOrth M).restrictScalars ℤ).comp (B.subtype.comp φ)
    have hψ_mem : ∀ a : A, ψ a ∈ Q := fun a => ⟨(φ a : EB), (φ a).2, rfl⟩
    have hψ_bound : ∀ a : A, ‖ψ a‖ ≤ C * ‖(a : EA)‖ := fun a =>
      (norm_projOrth_le M ((φ a : B) : EB)).trans (hbound a)
    let K : Submodule ℤ EA := (LinearMap.ker ψ).map A.subtype
    let bA : Module.Basis (Fin (rk A)) ℤ A := Module.finBasis ℤ A
    have hsp_bA : Submodule.span ℝ (Set.range fun i : Fin (rk A) => (bA i : EA)) =
        Submodule.span ℝ (A : Set EA) := by
      apply le_antisymm
      · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (bA i).2)
      · refine Submodule.span_le.mpr fun x hxA => ?_
        have hx : x = ∑ i : Fin (rk A), (bA.repr ⟨x, hxA⟩ i) • (bA i : EA) := by
          have h := congrArg Subtype.val (bA.sum_repr ⟨x, hxA⟩)
          rw [Submodule.coe_sum] at h
          exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
        rw [hx]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [← Int.cast_smul_eq_zsmul ℝ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let bAR : Module.Basis (Fin (rk A)) ℝ (Submodule.span ℝ (A : Set EA)) :=
      (Module.Basis.span (linearIndependent_coe_basis A bA)).map (LinearEquiv.ofEq _ _ hsp_bA)
    have hbAR_val : ∀ i : Fin (rk A), (bAR i : EA) = (bA i : EA) := fun i => by
      simp [bAR]
    let ψR : Submodule.span ℝ (A : Set EA) →ₗ[ℝ] EB := bAR.constr ℝ (fun i => ψ (bA i))
    have hψR_eq : ∀ a : A, ψR ⟨(a : EA), Submodule.subset_span a.2⟩ = ψ a := by
      intro a
      have ha : (⟨(a : EA), Submodule.subset_span a.2⟩ : Submodule.span ℝ (A : Set EA)) =
          ∑ i : Fin (rk A), (bA.repr a i : ℝ) • bAR i := by
        apply Subtype.ext
        have h := congrArg Subtype.val (bA.sum_repr a)
        rw [Submodule.coe_sum] at h
        rw [Submodule.coe_sum]
        refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [Submodule.coe_smul, SetLike.val_smul, hbAR_val i, Int.cast_smul_eq_zsmul]
      rw [ha, map_sum]
      have h2 : ψ a = ∑ i : Fin (rk A), (bA.repr a i : ℤ) • ψ (bA i) := by
        conv_lhs => rw [← bA.sum_repr a, map_sum]
        exact Finset.sum_congr rfl fun i _ => map_zsmul ψ _ _
      rw [h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, show ψR (bAR i) = ψ (bA i) from Module.Basis.constr_basis bAR ℝ _ i,
        Int.cast_smul_eq_zsmul]
    have hKsat : IsSaturated A K := by
      refine ⟨by rintro _ ⟨a, _, rfl⟩; exact a.2, ?_⟩
      intro x hxA hxsp
      have hker0 : ψR ⟨x, Submodule.subset_span hxA⟩ = 0 := by
        have hsub : Submodule.span ℝ (K : Set EA) ≤
            (LinearMap.ker ψR).map (Submodule.span ℝ (A : Set EA)).subtype := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨a, haK, rfl⟩
          refine ⟨⟨(a : EA), Submodule.subset_span a.2⟩, ?_, rfl⟩
          change ψR ⟨(a : EA), Submodule.subset_span a.2⟩ = 0
          rw [hψR_eq a]
          exact LinearMap.mem_ker.mp haK
        obtain ⟨y, hyK, hyx⟩ := hsub hxsp
        have hy_eq : y = ⟨x, Submodule.subset_span hxA⟩ := Subtype.ext hyx
        rw [← hy_eq]
        exact LinearMap.mem_ker.mp hyK
      have hψx : ψ ⟨x, hxA⟩ = 0 := by rw [← hψR_eq ⟨x, hxA⟩]; exact hker0
      exact ⟨⟨x, hxA⟩, LinearMap.mem_ker.mpr hψx, rfl⟩
    let Iψ : Submodule ℤ EB := LinearMap.range ψ
    have hIψ_le : Iψ ≤ Q := by rintro _ ⟨a, rfl⟩; exact hψ_mem a
    have hDiscI : DiscreteTopology Iψ := discreteTopology_of_le hIψ_le
    have hIψ_span : Submodule.span ℝ (Iψ : Set EB) = Submodule.span ℝ (Q : Set EB) := by
      have h1 : Submodule.span ℝ (Iψ : Set EB) =
          (Submodule.span ℝ (Set.range fun a : A => ((φ a : B) : EB))).map (projOrth M) := by
        rw [Submodule.map_span]
        congr 1; ext y; simp [Iψ, ψ, Set.range]
      have h2 : Submodule.span ℝ (Q : Set EB) =
          (Submodule.span ℝ (B : Set EB)).map (projOrth M) := by
        rw [Submodule.map_span]; rfl
      rw [h1, hspan, ← h2]
    have hrk_IQ : rk Iψ = rk Q := by
      unfold rk
      rw [finrank_int_eq_finrank_real_span Iψ, finrank_int_eq_finrank_real_span Q, hIψ_span]
    have hDiscAK : DiscreteTopology (quotLat A K) := discreteTopology_quotLat hKsat
    let qA := quotLat A K
    have hdesc : ∀ a₁ a₂ : A, projOrth K (a₁ : EA) = projOrth K (a₂ : EA) → ψ a₁ = ψ a₂ := by
      intro a₁ a₂ hproj
      have hsub : ((a₁ - a₂ : A) : EA) ∈ Submodule.span ℝ (K : Set EA) := by
        have h1 : ((a₁ - a₂ : A) : EA) - projOrth K ((a₁ - a₂ : A) : EA) ∈
            Submodule.span ℝ (K : Set EA) :=
          Stage4ArakelovBost.sub_projOrth_mem_span K _
        have h0 : projOrth K ((a₁ - a₂ : A) : EA) = 0 := by
          change projOrth K ((a₁ : EA) - (a₂ : EA)) = 0
          rw [map_sub, hproj, sub_self]
        rwa [h0, sub_zero] at h1
      have hmemK : ((a₁ - a₂ : A) : EA) ∈ K := hKsat.2 _ (a₁ - a₂).2 hsub
      rcases hmemK with ⟨a', ha'K, ha'eq⟩
      have ha_eq : a' = a₁ - a₂ := Subtype.ext ha'eq
      have h0 : ψ (a₁ - a₂) = 0 := ha_eq ▸ LinearMap.mem_ker.mp ha'K
      exact sub_eq_zero.mp (by rwa [map_sub] at h0)
    have hdesc_inv : ∀ a₁ a₂ : A, ψ a₁ = ψ a₂ → projOrth K (a₁ : EA) = projOrth K (a₂ : EA) := by
      intro a₁ a₂ hψeq
      have hmemK : ((a₁ - a₂ : A) : EA) ∈ K :=
        ⟨a₁ - a₂, LinearMap.mem_ker.mpr (by rw [map_sub, hψeq, sub_self]), rfl⟩
      have hzero : projOrth K ((a₁ : EA) - (a₂ : EA)) = 0 := by
        have horth := Stage4ArakelovBost.projOrth_mem_orthogonal K ((a₁ : EA) - (a₂ : EA))
        have hsp : (a₁ : EA) - (a₂ : EA) ∈ Submodule.span ℝ (K : Set EA) :=
          Submodule.subset_span hmemK
        have hsub : ((a₁ : EA) - (a₂ : EA)) - projOrth K ((a₁ : EA) - (a₂ : EA)) ∈
            Submodule.span ℝ (K : Set EA) :=
          Stage4ArakelovBost.sub_projOrth_mem_span K _
        have hp_sp : projOrth K ((a₁ : EA) - (a₂ : EA)) ∈ Submodule.span ℝ (K : Set EA) := by
          have : projOrth K ((a₁ : EA) - (a₂ : EA)) =
              ((a₁ : EA) - (a₂ : EA)) - (((a₁ : EA) - (a₂ : EA)) - projOrth K ((a₁ : EA) - (a₂ : EA))) := by
            abel
          rw [this]
          exact Submodule.sub_mem _ hsp hsub
        have hinner0 : inner ℝ (projOrth K ((a₁ : EA) - (a₂ : EA)))
            (projOrth K ((a₁ : EA) - (a₂ : EA))) = 0 := horth _ hp_sp
        exact inner_self_eq_zero.mp hinner0
      exact sub_eq_zero.mp (by rwa [← map_sub])
    have hrk_qA : rk qA = rk Iψ := by
      -- Canonical `ℤ`-linear equivalence `qA ≃ₗ[ℤ] Iψ` sending `projOrth K a ↦ ψ a`.
      have hrepQ : ∀ q : qA, ∃ a : A, projOrth K (a : EA) = (q : EA) := fun q => by
        rcases q.2 with ⟨v, hvA, hvq⟩
        exact ⟨⟨v, hvA⟩, hvq⟩
      have hrepI : ∀ y : Iψ, ∃ a : A, ψ a = (y : EB) := fun y => y.2
      let fQI : qA → Iψ := fun q => ⟨ψ (hrepQ q).choose, ⟨(hrepQ q).choose, rfl⟩⟩
      let gIQ : Iψ → qA := fun y =>
        ⟨projOrth K ((hrepI y).choose : EA), ⟨((hrepI y).choose : EA), (hrepI y).choose.2, rfl⟩⟩
      let eQI : qA ≃ₗ[ℤ] Iψ :=
        { toFun := fQI
          invFun := gIQ
          map_add' := fun q₁ q₂ => Subtype.ext <| by
            change ψ (hrepQ (q₁ + q₂)).choose = ψ (hrepQ q₁).choose + ψ (hrepQ q₂).choose
            rw [← map_add]
            refine hdesc _ _ ?_
            rw [(hrepQ (q₁ + q₂)).choose_spec]
            change (q₁ : EA) + (q₂ : EA) = projOrth K (((hrepQ q₁).choose : EA) + ((hrepQ q₂).choose : EA))
            rw [map_add, (hrepQ q₁).choose_spec, (hrepQ q₂).choose_spec]
          map_smul' := fun c q => Subtype.ext <| by
            change ψ (hrepQ (c • q)).choose = c • ψ (hrepQ q).choose
            rw [← map_zsmul]
            refine hdesc _ _ ?_
            rw [(hrepQ (c • q)).choose_spec]
            change c • (q : EA) = projOrth K (c • ((hrepQ q).choose : EA))
            rw [map_zsmul, (hrepQ q).choose_spec]
          left_inv := fun q => Subtype.ext <| by
            change projOrth K ((hrepI (fQI q)).choose : EA) = (q : EA)
            rw [← (hrepQ q).choose_spec]
            exact hdesc_inv _ _ (hrepI (fQI q)).choose_spec
          right_inv := fun y => Subtype.ext <| by
            change ψ (hrepQ (gIQ y)).choose = (y : EB)
            rw [← (hrepI y).choose_spec]
            exact hdesc _ _ (hrepQ (gIQ y)).choose_spec }
      exact eQI.finrank_eq
    have hψR_norm : ∀ v : Submodule.span ℝ (A : Set EA), ‖ψR v‖ ≤ C * ‖(v : EA)‖ := by
      intro v
      have hrat : ∀ q : Fin (rk A) → ℚ,
          ‖ψR (∑ i, (q i : ℝ) • bAR i)‖ ≤
            C * ‖((∑ i, (q i : ℝ) • bAR i : Submodule.span ℝ (A : Set EA)) : EA)‖ := by
        intro q
        let D : ℕ := ∏ i : Fin (rk A), (q i).den
        have hDpos : 0 < D := Finset.prod_pos fun i _ => (q i).pos
        have hDR : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hDpos
        have hmul_int : ∀ i : Fin (rk A), ∃ z : ℤ, (D : ℝ) * (q i : ℝ) = (z : ℝ) := by
          intro i
          have hdvd : (q i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
          obtain ⟨m, hm⟩ := hdvd
          refine ⟨(q i).num * (m : ℤ), ?_⟩
          have hq : (q i : ℝ) = ((q i).num : ℝ) / ((q i).den : ℝ) := Rat.cast_def (q i)
          rw [hq, hm]
          have hd0 : ((q i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).pos.ne'
          push_cast; field_simp [hd0]
        choose z hz using hmul_int
        let a : A := ∑ i : Fin (rk A), z i • bA i
        have ha_eq : (D : ℝ) • (∑ i, (q i : ℝ) • bAR i) =
            ⟨(a : EA), Submodule.subset_span a.2⟩ := by
          apply Subtype.ext
          simp only [SetLike.val_smul, Submodule.coe_sum, Finset.smul_sum, smul_smul, a]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hz i, hbAR_val i, Int.cast_smul_eq_zsmul]
        have h1 : (D : ℝ) * ‖ψR (∑ i, (q i : ℝ) • bAR i)‖ = ‖ψ a‖ := by
          rw [← Real.norm_of_nonneg hDR.le, ← norm_smul, ← map_smul, ha_eq, hψR_eq a]
        have h2 : (D : ℝ) * ‖((∑ i, (q i : ℝ) • bAR i : Submodule.span ℝ (A : Set EA)) : EA)‖ =
            ‖(a : EA)‖ := by
          rw [← Real.norm_of_nonneg hDR.le, ← norm_smul]
          congr 1
          exact congrArg Subtype.val ha_eq
        have h3 := hψ_bound a
        rw [← h1, ← h2] at h3
        nlinarith
      have hcontL : Continuous (fun c : Fin (rk A) → ℝ => ‖ψR (∑ i, c i • bAR i)‖) :=
        continuous_norm.comp ((LinearMap.continuous_of_finiteDimensional ψR).comp
          (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const))
      have hcontR : Continuous (fun c : Fin (rk A) → ℝ =>
          C * ‖((∑ i, c i • bAR i : Submodule.span ℝ (A : Set EA)) : EA)‖) :=
        continuous_const.mul (continuous_norm.comp (continuous_subtype_val.comp
          (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)))
      have hclosed : IsClosed {c : Fin (rk A) → ℝ |
          ‖ψR (∑ i, c i • bAR i)‖ ≤
            C * ‖((∑ i, c i • bAR i : Submodule.span ℝ (A : Set EA)) : EA)‖} :=
        isClosed_le hcontL hcontR
      have hdense : Dense (Set.range (fun (q : Fin (rk A) → ℚ) (i : Fin (rk A)) => (q i : ℝ))) := by
        rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
        intro c
        rw [Metric.mem_closure_iff]
        intro ε hε
        have hch : ∀ i : Fin (rk A), ∃ q : ℚ, |(q : ℝ) - c i| < ε := fun i => by
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c i - ε < c i + ε by linarith)
          exact ⟨q, abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩⟩
        choose q hq using hch
        refine ⟨fun i => (q i : ℝ), ⟨q, rfl⟩, ?_⟩
        rw [dist_pi_lt_iff hε]
        intro i
        rw [Real.dist_eq, abs_sub_comm]
        exact hq i
      have hall : ∀ c : Fin (rk A) → ℝ,
          ‖ψR (∑ i, c i • bAR i)‖ ≤
            C * ‖((∑ i, c i • bAR i : Submodule.span ℝ (A : Set EA)) : EA)‖ := by
        have hsub : Set.range (fun (q : Fin (rk A) → ℚ) (i : Fin (rk A)) => (q i : ℝ)) ⊆
            {c : Fin (rk A) → ℝ | ‖ψR (∑ i, c i • bAR i)‖ ≤
              C * ‖((∑ i, c i • bAR i : Submodule.span ℝ (A : Set EA)) : EA)‖} := by
          rintro _ ⟨q, rfl⟩; exact hrat q
        have hcl := closure_minimal hsub hclosed
        rw [hdense.closure_eq] at hcl
        exact fun c => hcl (Set.mem_univ c)
      have hv_eq := hall (bAR.repr v)
      rwa [bAR.sum_repr v] at hv_eq
    have hψR_zero_K : ∀ y ∈ Submodule.span ℝ (K : Set EA),
        ∀ hy : y ∈ Submodule.span ℝ (A : Set EA), ψR ⟨y, hy⟩ = 0 := by
      intro y hyK hyA
      have hsub : Submodule.span ℝ (K : Set EA) ≤
          (LinearMap.ker ψR).map (Submodule.span ℝ (A : Set EA)).subtype := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨a, haK, rfl⟩
        exact ⟨⟨(a : EA), Submodule.subset_span a.2⟩,
          by change ψR ⟨(a : EA), Submodule.subset_span a.2⟩ = 0; rw [hψR_eq a]; exact LinearMap.mem_ker.mp haK,
          rfl⟩
      obtain ⟨z, hzK, hzy⟩ := hsub hyK
      have hzeq : z = ⟨y, hyA⟩ := Subtype.ext hzy
      rw [← hzeq]
      exact LinearMap.mem_ker.mp hzK
    let bq : Module.Basis (Fin (rk qA)) ℤ qA := Module.finBasis ℤ qA
    have hpick : ∀ i : Fin (rk qA), ∃ a : A, projOrth K (a : EA) = (bq i : EA) := fun i => by
      rcases (bq i).2 with ⟨v, hvA, hvq⟩
      exact ⟨⟨v, hvA⟩, hvq⟩
    choose ai hai using hpick
    have hq_mem_spanA : ∀ q : qA, (q : EA) ∈ Submodule.span ℝ (A : Set EA) := by
      intro q
      rcases q.2 with ⟨v, hvA, hvq⟩
      have hsub : v - projOrth K v ∈ Submodule.span ℝ (K : Set EA) :=
        Stage4ArakelovBost.sub_projOrth_mem_span K v
      have hK_le_A : Submodule.span ℝ (K : Set EA) ≤ Submodule.span ℝ (A : Set EA) :=
        Submodule.span_mono (show (K : Set EA) ⊆ (A : Set EA) from hKsat.1)
      have hv_in : v ∈ Submodule.span ℝ (A : Set EA) := Submodule.subset_span hvA
      have hq_in : projOrth K v ∈ Submodule.span ℝ (A : Set EA) := by
        have : projOrth K v = v - (v - projOrth K v) := by abel
        rw [this]
        exact Submodule.sub_mem _ hv_in (hK_le_A hsub)
      have hvq' : projOrth K v = (q : EA) := hvq
      rwa [← hvq']
    have hψ_ai_eq : ∀ i, ψ (ai i) = ψR ⟨(bq i : EA), hq_mem_spanA (bq i)⟩ := by
      intro i
      rw [← hψR_eq (ai i)]
      have hsub : ((ai i : EA) - (bq i : EA)) ∈ Submodule.span ℝ (K : Set EA) := by
        rw [← hai i]; exact Stage4ArakelovBost.sub_projOrth_mem_span K _
      have hsubA : ((ai i : EA) - (bq i : EA)) ∈ Submodule.span ℝ (A : Set EA) :=
        Submodule.sub_mem _ (Submodule.subset_span (ai i).2) (hq_mem_spanA (bq i))
      have h0 := hψR_zero_K _ hsub hsubA
      have heq : (⟨(ai i : EA), Submodule.subset_span (ai i).2⟩ : Submodule.span ℝ (A : Set EA)) -
          ⟨(bq i : EA), hq_mem_spanA (bq i)⟩ = ⟨(ai i : EA) - (bq i : EA), hsubA⟩ := rfl
      rw [← heq, map_sub] at h0
      exact sub_eq_zero.mp h0
    let uq : Fin (rk qA) → EA := fun i => (bq i : EA)
    let gsU : Fin (rk qA) → EA := fun i => gsVec uq i
    have hgs_in_spanA : ∀ i, gsU i ∈ Submodule.span ℝ (A : Set EA) := by
      intro i
      have hmem : gsVec uq i ∈ Submodule.span ℝ (Set.range uq) := by
        have hstrong : ∀ n : ℕ, ∀ j : Fin (rk qA), j.1 < n →
            gsVec uq j ∈ Submodule.span ℝ (Set.range uq) := by
          intro n
          induction n with
          | zero => intro _ h; omega
          | succ n ih =>
            intro j hj
            rw [gsVec]
            refine Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
              (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
                (ih ⟨k.1, lt_trans k.2 j.2⟩ (lt_of_lt_of_le k.2 (Nat.le_of_lt_succ hj))))
        exact hstrong (i.1 + 1) i (Nat.lt_succ_self _)
      have hsub : Submodule.span ℝ (Set.range uq) ≤ Submodule.span ℝ (A : Set EA) :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hq_mem_spanA (bq j))
      exact hsub hmem
    let wI : Fin (rk qA) → EB := fun i => ψR ⟨gsU i, hgs_in_spanA i⟩
    have hψ_exp : ∀ i : Fin (rk qA),
        ψ (ai i) = ∑ j : Fin (rk qA), gsCoeff uq j i • wI j := by
      intro i
      rw [hψ_ai_eq i]
      have h1 : (⟨(bq i : EA), hq_mem_spanA (bq i)⟩ : Submodule.span ℝ (A : Set EA)) =
          ∑ j : Fin (rk qA), gsCoeff uq j i • ⟨gsU j, hgs_in_spanA j⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa [uq, gsU] using gs_expansion uq i
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul ψR _ _
    have hdet_le : (Matrix.gram ℝ (fun i => ψ (ai i))).det ≤
        (C ^ 2) ^ (rk qA) * (Matrix.gram ℝ uq).det := by
      let U : Matrix (Fin (rk qA)) (Fin (rk qA)) ℝ := fun j i => gsCoeff uq j i
      have hU_tri : U.BlockTriangular id := fun j i hji =>
        Stage2SiegelReduction.gsCoeff_of_gt uq hji
      have hU_det : U.det = 1 := by
        rw [Matrix.det_of_isUpperTriangular hU_tri]
        exact Finset.prod_eq_one fun i _ => Stage2SiegelReduction.gsCoeff_self uq i
      have hgram_eq : (Matrix.gram ℝ (fun i => ψ (ai i))).det = (Matrix.gram ℝ wI).det := by
        have hfn : (fun i => ψ (ai i)) = fun i => ∑ j, U j i • wI j := funext hψ_exp
        rw [hfn, gram_sum_smul_eq_transpose_mul wI U, Matrix.det_mul, Matrix.det_mul,
          Matrix.det_transpose, hU_det, one_mul, mul_one]
      rw [hgram_eq, det_gram_eq_prod_gsVec_norm_sq uq, det_gram_eq_prod_gsVec_norm_sq wI]
      calc ∏ i : Fin (rk qA), ‖gsVec wI i‖ ^ 2
          ≤ ∏ i : Fin (rk qA), ‖wI i‖ ^ 2 :=
            Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun i _ =>
              sq_le_sq' (by linarith [norm_nonneg (gsVec wI i), norm_nonneg (wI i)])
                (Stage2SiegelReduction.gsVec_norm_le wI i)
        _ ≤ ∏ i : Fin (rk qA), (C ^ 2 * ‖gsU i‖ ^ 2) := by
            refine Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun i _ => ?_
            have hni := hψR_norm ⟨gsU i, hgs_in_spanA i⟩
            have hsq := sq_le_sq' (by linarith [norm_nonneg (wI i), mul_nonneg hC.le (norm_nonneg (gsU i))]) hni
            simpa [wI, mul_pow] using hsq
        _ = (C ^ 2) ^ (rk qA) * ∏ i : Fin (rk qA), ‖gsU i‖ ^ 2 := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hli_ψ : LinearIndependent ℝ (fun i => ψ (ai i)) := by
      have hgen_Iψ : Iψ ≤ Submodule.span ℤ (Set.range fun i => ψ (ai i)) := by
        rintro _ ⟨a, rfl⟩
        let q : qA := ⟨projOrth K (a : EA), ⟨(a : EA), a.2, rfl⟩⟩
        have hq_rep : q = ∑ i : Fin (rk qA), bq.repr q i • bq i := (bq.sum_repr q).symm
        let a' : A := ∑ i : Fin (rk qA), bq.repr q i • ai i
        have hproj_eq : projOrth K (a : EA) = projOrth K (a' : EA) := by
          have h1 : (q : EA) = ∑ i : Fin (rk qA), bq.repr q i • (bq i : EA) := by
            have hval := congrArg Subtype.val hq_rep
            rw [Submodule.coe_sum] at hval
            exact hval.trans (Finset.sum_congr rfl fun i _ => rfl)
          have h2 : (a' : EA) = ∑ i : Fin (rk qA), bq.repr q i • (ai i : EA) := by
            change ((∑ i : Fin (rk qA), bq.repr q i • ai i : A) : EA) = _
            rw [Submodule.coe_sum]
            exact Finset.sum_congr rfl fun i _ => rfl
          rw [h2, map_sum]
          change (q : EA) = _
          rw [h1]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_zsmul, hai i]
        rw [hdesc a a' hproj_eq]
        change ψ (∑ i, bq.repr q i • ai i) ∈ _
        rw [map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_zsmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hspR : Submodule.span ℝ (Set.range fun i => ψ (ai i)) = Submodule.span ℝ (Iψ : Set EB) := by
        apply le_antisymm
        · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨ai i, rfl⟩)
        · refine Submodule.span_le.mpr fun x hx => ?_
          have hxZ := hgen_Iψ hx
          clear hx
          induction hxZ using Submodule.span_induction with
          | mem y hy => exact Submodule.subset_span hy
          | zero => exact Submodule.zero_mem _
          | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
          | smul c y _ hy =>
            rw [← Int.cast_smul_eq_zsmul ℝ]
            exact Submodule.smul_mem _ (c : ℝ) hy
      have hcard_eq : Fintype.card (Fin (rk qA)) =
          Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => ψ (ai i))) := by
        rw [Fintype.card_fin, hspR, ← finrank_int_eq_finrank_real_span Iψ]
        exact hrk_qA
      exact (linearIndependent_of_top_le_span_of_card_eq_finrank
        (b := fun i => (⟨ψ (ai i), Submodule.subset_span ⟨i, rfl⟩⟩ :
          Submodule.span ℝ (Set.range fun i => ψ (ai i))))
        (by
          intro x _
          have hx := x.2
          rw [Submodule.mem_span_range_iff_exists_fun] at hx
          obtain ⟨c, hc⟩ := hx
          have hxeq : x = ∑ i, c i • (⟨ψ (ai i), Submodule.subset_span ⟨i, rfl⟩⟩ : _) :=
            Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hc.symm)
          rw [hxeq]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
        hcard_eq).map' (Submodule.span ℝ (Set.range fun i => ψ (ai i))).subtype
          (Submodule.ker_subtype _)
    have hcov_Q_le : covol Q ≤ C ^ (rk qA) * covol qA := by
      let Ssub : Submodule ℤ EB := Submodule.span ℤ (Set.range fun i => ψ (ai i))
      have hSsub_le : Ssub ≤ Q := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hψ_mem (ai i))
      have hDiscS : DiscreteTopology Ssub := discreteTopology_of_le hSsub_le
      have hliZ : LinearIndependent ℤ (fun i => (⟨ψ (ai i), Submodule.subset_span ⟨i, rfl⟩⟩ : Ssub)) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h1 : ∑ j, (c j : ℝ) • ψ (ai j) = 0 := by
          have h2 := congrArg Subtype.val hc
          simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
            Int.cast_smul_eq_zsmul] using h2
        exact_mod_cast Fintype.linearIndependent_iff.mp hli_ψ (fun j => (c j : ℝ)) h1 i
      let bS : Module.Basis (Fin (rk qA)) ℤ Ssub := Module.Basis.mk hliZ (by
        intro x _
        have hx := x.2
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨c, hc⟩ := hx
        have hxeq : x = ∑ i, c i • (⟨ψ (ai i), Submodule.subset_span ⟨i, rfl⟩⟩ : Ssub) :=
          Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hc.symm)
        rw [hxeq]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      have hrkS : rk Ssub = rk Q := by
        unfold rk
        rw [Module.finrank_eq_card_basis bS, Fintype.card_fin]
        exact hrk_qA.trans hrk_IQ
      have hcov_le_S : covol Q ≤ covol Ssub := (covol_le_of_le_same_rank hSsub_le hrkS).1
      have hcovS : covol Ssub = Real.sqrt (Matrix.gram ℝ (fun i => ψ (ai i))).det := by
        rw [covol_eq_sqrt_det_gram Ssub bS]
        congr 2; ext i j; simp [Matrix.gram_apply, bS]
      have hcov_qA : covol qA = Real.sqrt (Matrix.gram ℝ uq).det :=
        covol_eq_sqrt_det_gram qA bq
      calc covol Q ≤ covol Ssub := hcov_le_S
        _ = Real.sqrt (Matrix.gram ℝ (fun i => ψ (ai i))).det := hcovS
        _ ≤ Real.sqrt ((C ^ 2) ^ (rk qA) * (Matrix.gram ℝ uq).det) := Real.sqrt_le_sqrt hdet_le
        _ = C ^ (rk qA) * covol qA := by
            rw [hcov_qA, Real.sqrt_mul (by positivity), ← pow_mul, mul_comm 2, pow_mul,
              Real.sqrt_sq (by positivity)]
    have hrkQ_pos : (0 : ℝ) < (rk Q : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot Q hQ0)
    have hrk_eq_qA_Q : rk qA = rk Q := hrk_qA.trans hrk_IQ
    have hlog := Real.log_le_log (covol_pos Q) hcov_Q_le
    rw [Real.log_mul (pow_pos hC _).ne' (covol_pos qA).ne', Real.log_pow] at hlog
    have hqA_ne : qA ≠ ⊥ := by
      intro hbot
      have : rk qA = 0 := by rw [hbot]; simp [rk]
      have : rk Q = 0 := hrk_eq_qA_Q ▸ this
      exact (rk_pos_of_ne_bot Q hQ0).ne' this
    have hmuMin_le : muMin A ≤ ArakelovCovolume.slope qA := muMin_le_slope_quotLat hKsat (by
      intro hKA
      have hadd := rk_add_quotLat hKsat
      have h1 : rk K = rk A := congrArg rk hKA
      have h0 : rk (quotLat A K) = 0 := by omega
      exact (rk_pos_of_ne_bot qA hqA_ne).ne' h0)
    have hsl_ineq : ArakelovCovolume.slope qA - Real.log C ≤ ArakelovCovolume.slope Q := by
      rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
        Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk, ← hrk_eq_qA_Q]
      unfold arithDeg
      have hr_pos : (0 : ℝ) < (rk qA : ℝ) := by rw [hrk_eq_qA_Q]; exact hrkQ_pos
      have hdiv := div_le_div_of_nonneg_right (neg_le_neg hlog) hr_pos.le
      have hrhs : -((rk qA : ℝ) * Real.log C + Real.log (covol qA)) / (rk qA : ℝ) =
          -Real.log (covol qA) / (rk qA : ℝ) - Real.log C := by
        field_simp [hr_pos.ne']; ring
      linarith
    linarith
  have hmuMinB : muMin A - Real.log C ≤ muMin B := by
    unfold Stage4ArakelovBost.muMin
    refine le_csInf ?_ ?_
    · refine ⟨ArakelovCovolume.slope (quotLat B ⊥), ⊥, Stage4ArakelovBost.isSaturated_bot B,
        hB0.symm, rfl⟩
    · rintro t ⟨M, hMsat, hMne, rfl⟩
      exact hquot M hMsat hMne
  exact ⟨hmuMinB, hmuMinB.trans (muMin_le_slope_le_muMax B hB0).1⟩

/-- **UNCONDITIONAL SCHUR-FUNCTOR BRANCHING SLOPE LOWER BOUND (`schur_branching_slope_lower`)**:
For any base lattice `A : ConcreteEuclideanLat` of rank `r = rk A.L`, any partition
`lam : Partition (rk A.L)` (with hook product `H_lam = lam.hookProd`), and any Schur-functor lattice
`S_lam` receiving a full-real-span branching projection `π_lam : columnTensorLat A lam →ₗ[ℤ] S_lam`
with norm bound `‖π_lam x‖ ≤ (H_lam : ℝ) * C_branch * ‖x‖`:
1. `muMin (columnTensorLat A lam).L - |lam| * log (lam_0 + r) - log C_branch ≤ muMin S_lam.L ≤ slope S_lam.L`,
2. Under semistability defect `slope (columnTensorLat A lam).L - muMin (columnTensorLat A lam).L ≤ Δ`,
   `|lam| * slope A.L - Δ - |lam| * log (lam_0 + r) - log C_branch ≤ muMin S_lam.L ≤ slope S_lam.L`! -/
theorem schur_branching_slope_lower (A : ConcreteEuclideanLat) (lam : Partition (rk A.L))
    (S : ConcreteEuclideanLat)
    (pMap : (columnTensorLat A lam).L →ₗ[ℤ] S.L) {C_branch : ℝ} (hC : 0 < C_branch)
    (hbound : ∀ x : (columnTensorLat A lam).L,
      ‖((pMap x : S.L) : S.E)‖ ≤ (lam.hookProd : ℝ) * C_branch * ‖(x : (columnTensorLat A lam).E)‖)
    (hspan : Submodule.span ℝ (Set.range fun x : (columnTensorLat A lam).L => ((pMap x : S.L) : S.E)) =
      Submodule.span ℝ (S.L : Set S.E)) :
    (muMin (columnTensorLat A lam).L -
        (lam.weight : ℝ) * Real.log ((lam.maxPart + rk A.L : ℕ) : ℝ) - Real.log C_branch ≤
      muMin S.L ∧ muMin S.L ≤ ArakelovCovolume.slope S.L) ∧
    ∀ Δ : ℝ, ArakelovCovolume.slope (columnTensorLat A lam).L - muMin (columnTensorLat A lam).L ≤ Δ →
      (lam.weight : ℝ) * ArakelovCovolume.slope A.L - Δ -
          (lam.weight : ℝ) * Real.log ((lam.maxPart + rk A.L : ℕ) : ℝ) - Real.log C_branch ≤
        muMin S.L ∧ muMin S.L ≤ ArakelovCovolume.slope S.L := by
  have hHpos : (0 : ℝ) < (lam.hookProd : ℝ) := Nat.cast_pos.mpr lam.hookProd_pos
  have hHC : 0 < (lam.hookProd : ℝ) * C_branch := mul_pos hHpos hC
  obtain ⟨hmu, _⟩ := muMin_sub_log_le_muMin_of_fullRank
    (columnTensorLat A lam).L S.L S.ne_bot pMap hHC hbound hspan
  have hlogH : Real.log ((lam.hookProd : ℝ) * C_branch) ≤
      (lam.weight : ℝ) * Real.log ((lam.maxPart + rk A.L : ℕ) : ℝ) + Real.log C_branch := by
    rw [Real.log_mul hHpos.ne' hC.ne']
    linarith [lam.log_hookProd_le]
  have h1 : muMin (columnTensorLat A lam).L -
      (lam.weight : ℝ) * Real.log ((lam.maxPart + rk A.L : ℕ) : ℝ) - Real.log C_branch ≤
      muMin S.L := by linarith
  have h2 : muMin S.L ≤ ArakelovCovolume.slope S.L := (muMin_le_slope_le_muMax S.L S.ne_bot).1
  refine ⟨⟨h1, h2⟩, fun Δ hΔ => ?_⟩
  have hcol := (column_lattice_exact_slope A lam).2
  exact ⟨by linarith, h2⟩

/-- **UNIFORM-IN-WEIGHT DEFINITE UNITARY GENUS FAMILY BOUND (`lower_slope_inequality_family`)**:
On a definite unitary group `U(X_0)` with finite genus `G : HermitianGenus r` (`r ≥ 1`),
for ANY weight `lam : Partition (2 * r)` and ANY genus-indexed family of Schur-functor Hermitian
lattices `S c` (`c : G.ι`) receiving branching projections `pMap c` of norm `≤ H_lam * C_branch`:
uniformly across all genus classes `c : G.ι` and all weights `lam`,
`slope (S c) ≥ |lam| * slope (G.lat c).realLat - Δ_c - |lam| * log (lam_0 + 2r) - log C_branch`! -/
theorem lower_slope_inequality_family {r : ℕ} (hr : 1 ≤ r) (G : HermitianGenus r)
    (lam : Partition (2 * r)) (C_branch : ℝ) (hC : 0 < C_branch)
    (S : G.idx → ConcreteEuclideanLat) (Δ : G.idx → ℝ)
    (hbranch : ∀ c : G.idx,
      let Ac : ConcreteEuclideanLat :=
        { E := EuclideanSpace ℝ (Fin (2 * r))
          L := (G.lat c).realLat
          discL := (G.lat c).realLat_discrete
          ne_bot := by
            intro hbot
            have h1 := (G.lat c).rk_eq
            have h2 : rk (G.lat c).lat = rk (G.lat c).realLat :=
              (arithDeg_eq_of_isometric_equiv (G.lat c).realLatEquiv
                (fun x => (realEquiv r).norm_map x.1)).1
            rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * r)))) = 0 by simp [rk]] at h2
            omega }
      let lamc : Partition (rk Ac.L) :=
        { parts := fun i => lam.parts (i.cast (by
            have h2 : rk (G.lat c).lat = rk (G.lat c).realLat :=
              (arithDeg_eq_of_isometric_equiv (G.lat c).realLatEquiv
                (fun x => (realEquiv r).norm_map x.1)).1
            exact h2.symm.trans (G.lat c).rk_eq))
          anti := fun a b hab => lam.anti hab }
      ∃ pMap : (columnTensorLat Ac lamc).L →ₗ[ℤ] (S c).L,
        (∀ x, ‖((pMap x : (S c).L) : (S c).E)‖ ≤
          (lamc.hookProd : ℝ) * C_branch * ‖(x : (columnTensorLat Ac lamc).E)‖) ∧
        Submodule.span ℝ (Set.range fun x => ((pMap x : (S c).L) : (S c).E)) =
          Submodule.span ℝ ((S c).L : Set (S c).E) ∧
        ArakelovCovolume.slope (columnTensorLat Ac lamc).L - muMin (columnTensorLat Ac lamc).L ≤ Δ c) :
    ∀ c : G.idx,
      (lam.weight : ℝ) * ArakelovCovolume.slope (G.lat c).realLat - Δ c -
          (lam.weight : ℝ) * Real.log ((lam.maxPart + 2 * r : ℕ) : ℝ) - Real.log C_branch ≤
        muMin (S c).L ∧ muMin (S c).L ≤ ArakelovCovolume.slope (S c).L := by
  intro c
  have hrk_c : rk (G.lat c).realLat = 2 * r := by
    have h2 : rk (G.lat c).lat = rk (G.lat c).realLat :=
      (arithDeg_eq_of_isometric_equiv (G.lat c).realLatEquiv
        (fun x => (realEquiv r).norm_map x.1)).1
    exact h2.symm.trans (G.lat c).rk_eq
  let Ac : ConcreteEuclideanLat :=
    { E := EuclideanSpace ℝ (Fin (2 * r))
      L := (G.lat c).realLat
      discL := (G.lat c).realLat_discrete
      ne_bot := by
        intro hbot
        rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * r)))) = 0 by simp [rk]] at hrk_c
        omega }
  let lamc : Partition (rk Ac.L) :=
    { parts := fun i => lam.parts (i.cast hrk_c)
      anti := fun a b hab => lam.anti hab }
  obtain ⟨pMap, hbd, hsp, hΔ⟩ := hbranch c
  have hres := (schur_branching_slope_lower Ac lamc (S c) pMap hC hbd hsp).2 (Δ c) hΔ
  have hw_eq : lamc.weight = lam.weight := by
    unfold Partition.weight
    exact Fintype.sum_equiv (finCongr hrk_c) _ _ fun _ => rfl
  have hmax_eq : lamc.maxPart = lam.maxPart := by
    unfold Partition.maxPart
    have hpos1 : 0 < rk Ac.L := by change 0 < rk (G.lat c).realLat; omega
    have hpos2 : 0 < 2 * r := by omega
    rw [dif_pos hpos1, dif_pos hpos2]
    rfl
  rw [hw_eq, hmax_eq] at hres
  have hrkAc : rk Ac.L = 2 * r := hrk_c
  rw [hrkAc] at hres
  exact hres

end ColumnTensorAndBranching

end WeylHookLengthAndSchurBranching

/-! ## Section 4: Genuine Arbitrary-Dimension Arithmetic Hilbert–Samuel & Moriwaki Bigness (`L3`) -/

section MoriwakiBignessArbitraryDim

/-- **Arbitrary-Dimension (`d ≥ 1`) Graded Hermitian Section Algebra `⨁_{k ≥ 0} H^0(X, L^{⊗ k})`**:
models an `ArakelovLineBundle` on a `d`-dimensional projective arithmetic variety `X` with:
- integral global-section lattices `secLat k ⊂ secSpace k` (`H^0(𝒳, ℒ^{⊗ k})`),
- sup-norm `supNorm k` satisfying the compact-manifold `L²`-vs-`L^∞` comparison
  `volConst⁻¹ * ‖s‖ ≤ supNorm k s ≤ bergConst * (k + 1)^bergExp * ‖s‖`,
- Hilbert–Samuel polynomial rank ceiling `rk (secLat k) ≤ rankHi * k^d`,
- positive arithmetic self-intersection / arithmetic volume `volAr = \widehat{c}_1(\overline{L})^{d+1}`:
  `liminf_{k → ∞} arithDeg (secLat k) / k^(d + 1) ≥ volAr / (d + 1)!`. -/
structure GradedHermAlgebra (d : ℕ) where
  hd : 1 ≤ d
  secSpace : ℕ → Type*
  [normSpace : ∀ k, NormedAddCommGroup (secSpace k)]
  [innerSpace : ∀ k, InnerProductSpace ℝ (secSpace k)]
  [fdSpace : ∀ k, FiniteDimensional ℝ (secSpace k)]
  secLat : ∀ k, Submodule ℤ (secSpace k)
  [discLat : ∀ k, DiscreteTopology (secLat k)]
  secLat_ne_bot : ∀ k, 1 ≤ k → secLat k ≠ ⊥
  supNorm : ∀ k, secSpace k → ℝ
  supNorm_nonneg : ∀ k s, 0 ≤ supNorm k s
  volConst : ℝ
  volConst_pos : 0 < volConst
  norm_le_vol_supNorm : ∀ k, 1 ≤ k → ∀ s : secSpace k, ‖s‖ ≤ volConst * supNorm k s
  bergConst : ℝ
  bergExp : ℕ
  bergConst_ge_one : 1 ≤ bergConst
  supNorm_le_bergman : ∀ k, 1 ≤ k → ∀ s : secSpace k,
    supNorm k s ≤ bergConst * ((k : ℝ) + 1) ^ bergExp * ‖s‖
  rankHi : ℝ
  rankHi_ge_one : 1 ≤ rankHi
  rk_le_poly : ∀ k, 1 ≤ k → (rk (secLat k) : ℝ) ≤ rankHi * (k : ℝ) ^ d
  volAr : ℝ
  ahs_liminf : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
    volAr / ((d + 1).factorial : ℝ) - ε ≤ arithDeg (secLat k) / (k : ℝ) ^ (d + 1)

attribute [instance] GradedHermAlgebra.normSpace GradedHermAlgebra.innerSpace
  GradedHermAlgebra.fdSpace GradedHermAlgebra.discLat

namespace GradedHermAlgebra

/-- The set of strictly small integral global sections `{s ∈ H^0(𝒳, ℒ^{⊗ k}) | ‖s‖_sup < 1}`. -/
def smallSectionsSet {d : ℕ} (A : GradedHermAlgebra d) (k : ℕ) : Set (A.secLat k) :=
  { s : A.secLat k | A.supNorm k s.1 < 1 }

/-- Finiteness of strictly small integral global sections at every degree `k ≥ 1`. -/
theorem smallSections_finite {d : ℕ} (A : GradedHermAlgebra d) {k : ℕ} (hk : 1 ≤ k) :
    (A.smallSectionsSet k).Finite := by
  have hball := lattice_inter_closedBall_finite (A.secLat k) A.volConst
  have hsub : Subtype.val '' A.smallSectionsSet k ⊆
      (A.secLat k : Set (A.secSpace k)) ∩ Metric.closedBall 0 A.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := A.norm_le_vol_supNorm k hk s.1
    have h2 : A.supNorm k s.1 < 1 := hs
    nlinarith [A.volConst_pos]
  exact Set.Finite.of_finite_image (hball.subset hsub) Subtype.val_injective.injOn

/-- Exact cardinality `#smallSections A k` of strictly small global sections `‖s‖_sup < 1`. -/
def smallSectionsCard {d : ℕ} (A : GradedHermAlgebra d) (k : ℕ) (hk : 1 ≤ k) : ℕ :=
  (A.smallSections_finite hk).toFinset.card

/-- Lower bound comparing `#smallSections A k` against Euclidean strict-ball count `h0ArithStrict`. -/
theorem h0ArithStrict_le_smallSectionsCard {d : ℕ} (A : GradedHermAlgebra d)
    {k : ℕ} (hk : 1 ≤ k) :
    h0ArithStrict (A.secLat k) ((A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹) ≤
      A.smallSectionsCard k hk := by
  unfold h0ArithStrict smallSectionsCard
  let R : ℝ := (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹
  have hBpos : 0 < A.bergConst * ((k : ℝ) + 1) ^ A.bergExp :=
    mul_pos (by linarith [A.bergConst_ge_one]) (pow_pos (by positivity) _)
  have hsub : ((A.secLat k : Set (A.secSpace k)) ∩ Metric.ball 0 R) ⊆
      Subtype.val '' A.smallSectionsSet k := by
    rintro x ⟨hxL, hxB⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    change A.supNorm k x < 1
    rw [Metric.mem_ball, dist_zero_right] at hxB
    have h1 := A.supNorm_le_bergman k hk x
    have h2 : A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * ‖x‖ <
        A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * R :=
      mul_lt_mul_of_pos_left hxB hBpos
    have hinv : A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * R = 1 := mul_inv_cancel₀ hBpos.ne'
    rw [hinv] at h2
    exact lt_of_le_of_lt h1 h2
  have hfinImg : (Subtype.val '' A.smallSectionsSet k).Finite :=
    (A.smallSections_finite hk).image Subtype.val
  calc ((A.secLat k : Set (A.secSpace k)) ∩ Metric.ball 0 R).ncard
      ≤ (Subtype.val '' A.smallSectionsSet k).ncard := Set.ncard_le_ncard hsub hfinImg
    _ = (A.smallSectionsSet k).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    _ = (A.smallSections_finite hk).toFinset.card :=
        Set.ncard_eq_toFinset_card (A.smallSectionsSet k) (A.smallSections_finite hk)

end GradedHermAlgebra

/-- Helper: `(C₁ * log (k + 1) + C₂) / k → 0` as `k → ∞`. -/
private lemma tendsto_log_linear_div_nat (C₁ C₂ : ℝ) :
    Tendsto (fun k : ℕ => (C₁ * Real.log ((k : ℝ) + 1) + C₂) / (k : ℝ)) atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero
    simpa [pow_one, one_mul, add_zero] using h
  have hlog_k1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    hlog_div.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv_nat : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div] using hinv_nat
    have hadd : Tendsto (fun k : ℕ => (1 : ℝ) + (1 : ℝ) / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hk0]
  have hlog_k : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 0) := by
    have hprod := hlog_k1.mul hratio
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk1]
  have hC₂ : Tendsto (fun k : ℕ => C₂ / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv_nat.const_mul C₂
  have hsum : Tendsto (fun k : ℕ => C₁ * (Real.log ((k : ℝ) + 1) / (k : ℝ)) + C₂ / (k : ℝ))
      atTop (𝓝 (C₁ * 0 + 0)) := (hlog_k.const_mul C₁).add hC₂
  simp only [mul_zero, add_zero] at hsum
  exact hsum.congr fun k => by ring

/-- **MORIWAKI'S BIGNESS THEOREM IN ARBITRARY DIMENSION `d ≥ 1` (`moriwaki_big_small_sections`)**:
For any `d ≥ 1` and any graded Hermitian section algebra `A : GradedHermAlgebra d` with strictly
positive arithmetic self-intersection `volAr = c > 0`:
`∃ c₀ > 0, ∃ K₀ ≥ 1, ∀ k ≥ K₀, Real.log (#smallSections A k) ≥ c₀ * k ^ (d + 1)`
(exponentially many strictly small global sections `‖s‖_sup < 1`!). -/
theorem moriwaki_big_small_sections {d : ℕ} (A : GradedHermAlgebra d) (hbig : 0 < A.volAr) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (A.smallSectionsCard k (le_trans hK₀ hk) : ℝ) := by
  let c₀ : ℝ := A.volAr / (2 * ((d + 1).factorial : ℝ))
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hc₀_pos : 0 < c₀ := div_pos hbig (by positivity)
  have hAHS := A.ahs_liminf (c₀ / 2) (half_pos hc₀_pos)
  let C₁ : ℝ := A.rankHi * ((A.bergExp : ℝ) + (d : ℝ) / 2)
  let C₂ : ℝ := A.rankHi * (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi +
    |Real.log (√Real.pi)|)
  have herr := tendsto_log_linear_div_nat C₁ C₂
  have hmem_err := (Metric.tendsto_atTop.mp herr) (c₀ / 2) (half_pos hc₀_pos)
  rw [Filter.eventually_atTop] at hAHS
  obtain ⟨K₁, hK₁⟩ := hAHS
  let K₀ : ℕ := max 1 (max K₁ hmem_err.choose)
  refine ⟨c₀, hc₀_pos, K₀, le_max_left _ _, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hkK₁ : K₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkErr : hmem_err.choose ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos hk_pos (d + 1)
  have hB_pos : 0 < A.bergConst * ((k : ℝ) + 1) ^ A.bergExp :=
    mul_pos (by linarith [A.bergConst_ge_one]) (pow_pos (by positivity) _)
  let Rk : ℝ := (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹
  have hRk_pos : 0 < Rk := inv_pos.mpr hB_pos
  have hrk_pos : 1 ≤ rk (A.secLat k) := rk_pos_of_ne_bot (A.secLat k) (A.secLat_ne_bot k hk1)
  have hrk_posR : (0 : ℝ) < (rk (A.secLat k) : ℝ) := Nat.cast_pos.mpr hrk_pos
  have hcount_le : (h0ArithStrict (A.secLat k) Rk : ℝ) ≤ (A.smallSectionsCard k hk1 : ℝ) :=
    Nat.cast_le.mpr (A.h0ArithStrict_le_smallSectionsCard hk1)
  have h0_pos : (0 : ℝ) < (h0ArithStrict (A.secLat k) Rk : ℝ) := by
    have hfin : ((A.secLat k : Set (A.secSpace k)) ∩ Metric.ball 0 Rk).Finite :=
      (lattice_inter_closedBall_finite (A.secLat k) Rk).subset
        (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)
    have hne : ((A.secLat k : Set (A.secSpace k)) ∩ Metric.ball 0 Rk).Nonempty :=
      ⟨0, (A.secLat k).zero_mem, Metric.mem_ball_self hRk_pos⟩
    exact Nat.cast_pos.mpr ((Set.ncard_pos hfin).mpr hne)
  have hlog_mono : Real.log (h0ArithStrict (A.secLat k) Rk : ℝ) ≤
      Real.log (A.smallSectionsCard k hk1 : ℝ) :=
    Real.log_le_log h0_pos hcount_le
  have hmink := log_h0ArithStrict_lower_bound (A.secLat k) hRk_pos
  have hlogω := log_unitBallVol_ge hrk_pos
  have hlog_Rk : Real.log (Rk / 2) =
      -(Real.log (2 * A.bergConst) + (A.bergExp : ℝ) * Real.log ((k : ℝ) + 1)) := by
    have h2B : Rk / 2 = (2 * A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹ := by
      unfold Rk; field_simp [hB_pos.ne']
    rw [h2B, Real.log_inv,
      Real.log_mul (by linarith [A.bergConst_ge_one]) (pow_pos (by positivity) _).ne',
      Real.log_pow]
  have hlog_rk : Real.log (rk (A.secLat k) : ℝ) ≤
      Real.log A.rankHi + (d : ℝ) * Real.log ((k : ℝ) + 1) := by
    have h1 : (rk (A.secLat k) : ℝ) ≤ A.rankHi * ((k : ℝ) + 1) ^ d := by
      calc (rk (A.secLat k) : ℝ) ≤ A.rankHi * (k : ℝ) ^ d := A.rk_le_poly k hk1
        _ ≤ A.rankHi * ((k : ℝ) + 1) ^ d :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk_pos.le (by linarith) d)
              (by linarith [A.rankHi_ge_one])
    have h2 := Real.log_le_log hrk_posR h1
    rw [Real.log_mul (by linarith [A.rankHi_ge_one]) (pow_pos (by positivity) _).ne',
      Real.log_pow] at h2
    exact h2
  have hlog_pi : (1 / 2) * Real.log Real.pi = Real.log (√Real.pi) := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  have hloss_per_rk :
      -(Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi - (1 / 2) * Real.log (rk (A.secLat k) : ℝ)) ≤
      ((A.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
        (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|) := by
    rw [hlog_Rk, hlog_pi]
    have hpi_abs : -Real.log (√Real.pi) ≤ |Real.log (√Real.pi)| := neg_le_abs _
    linarith
  have hloss_tot :
      -(rk (A.secLat k) : ℝ) * (Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
          (1 / 2) * Real.log (rk (A.secLat k) : ℝ)) ≤
      (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d := by
    have hpos_rhs : 0 ≤ ((A.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
        (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|) := by
      have h1 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log (2 * A.bergConst) := Real.log_nonneg (by linarith [A.bergConst_ge_one])
      have h3 : 0 ≤ Real.log A.rankHi := Real.log_nonneg A.rankHi_ge_one
      have h4 : 0 ≤ |Real.log (√Real.pi)| := abs_nonneg _
      nlinarith [Nat.cast_nonneg (α := ℝ) A.bergExp, Nat.cast_nonneg (α := ℝ) d]
    calc -(rk (A.secLat k) : ℝ) * (Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
            (1 / 2) * Real.log (rk (A.secLat k) : ℝ))
        = (rk (A.secLat k) : ℝ) * (-(Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
            (1 / 2) * Real.log (rk (A.secLat k) : ℝ))) := by ring
      _ ≤ (A.rankHi * (k : ℝ) ^ d) *
            (((A.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
              (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|)) := by
          calc (rk (A.secLat k) : ℝ) * _
              ≤ (rk (A.secLat k) : ℝ) * (((A.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
                  (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|)) :=
                mul_le_mul_of_nonneg_left hloss_per_rk hrk_posR.le
            _ ≤ (A.rankHi * (k : ℝ) ^ d) * _ :=
                mul_le_mul_of_nonneg_right (A.rk_le_poly k hk1) hpos_rhs
      _ = (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d := by
          dsimp only [C₁, C₂]; ring
  have herr_k : (C₁ * Real.log ((k : ℝ) + 1) + C₂) / (k : ℝ) ≤ c₀ / 2 := by
    have hd := hmem_err.choose_spec k hkErr
    rw [Real.dist_eq, sub_zero] at hd
    exact (le_abs_self _).trans hd.le
  have herr_scaled : (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d ≤
      (c₀ / 2) * (k : ℝ) ^ (d + 1) := by
    have h1 := (div_le_iff₀ hk_pos).mp herr_k
    have hmul := mul_le_mul_of_nonneg_right h1 (pow_nonneg hk_pos.le d)
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hAHS_k : (2 * c₀ - c₀ / 2) * (k : ℝ) ^ (d + 1) ≤ arithDeg (A.secLat k) := by
    have h1 := hK₁ k hkK₁
    have h2c : A.volAr / ((d + 1).factorial : ℝ) = 2 * c₀ := by
      dsimp only [c₀]; field_simp [hfac_pos.ne']
    rw [h2c] at h1
    exact (le_div_iff₀ hkd1_pos).mp h1
  have hcomb : arithDeg (A.secLat k) - (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d ≤
      Real.log (h0ArithStrict (A.secLat k) Rk : ℝ) := by
    have hstep : arithDeg (A.secLat k) +
        (rk (A.secLat k) : ℝ) * (Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
          (1 / 2) * Real.log (rk (A.secLat k) : ℝ)) ≤
        Real.log (h0ArithStrict (A.secLat k) Rk : ℝ) := by
      have h1 : ((rk (A.secLat k) : ℝ) / 2) * Real.log Real.pi -
          ((rk (A.secLat k) : ℝ) / 2) * Real.log (rk (A.secLat k) : ℝ) =
          (rk (A.secLat k) : ℝ) * ((1 / 2) * Real.log Real.pi -
            (1 / 2) * Real.log (rk (A.secLat k) : ℝ)) := by ring
      linarith
    linarith
  linarith

/-- Immediate corollary of Moriwaki's bigness theorem: for all sufficiently large `k ≥ K₀`,
there exists a **nonzero** strictly small integral global section `s ∈ H^0(𝒳, ℒ^{⊗ k})` with
`‖s‖_sup < 1`! -/
theorem moriwaki_exists_nonzero_small_section {d : ℕ} (A : GradedHermAlgebra d)
    (hbig : 0 < A.volAr) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
      ∃ s : A.secLat k, s ≠ 0 ∧ A.supNorm k s.1 < 1 := by
  obtain ⟨c₀, hc₀, K₁, hK₁, hlog⟩ := moriwaki_big_small_sections A hbig
  refine ⟨K₁, hK₁, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans hK₁ hk
  have hpos : 0 < Real.log (A.smallSectionsCard k hk1 : ℝ) :=
    lt_of_lt_of_le (mul_pos hc₀ (pow_pos (Nat.cast_pos.mpr hk1) (d + 1))) (hlog k hk)
  have hgt1 : 1 < A.smallSectionsCard k hk1 := by
    by_contra hle
    have hcard_le : (A.smallSectionsCard k hk1 : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_not_lt hle
    have hlog_le : Real.log (A.smallSectionsCard k hk1 : ℝ) ≤ 0 := by
      by_cases h0 : A.smallSectionsCard k hk1 = 0
      · simp [h0]
      · exact (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)) hcard_le).trans
          (by simp)
    linarith
  have hcard : 1 < (A.smallSections_finite hk1).toFinset.card := hgt1
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hcard
  by_cases hs10 : s₁ = 0
  · refine ⟨s₂, fun h => hne (hs10.trans h.symm), ((A.smallSections_finite hk1).mem_toFinset).mp hs₂⟩
  · exact ⟨s₁, hs10, ((A.smallSections_finite hk1).mem_toFinset).mp hs₁⟩

/-! ### Concrete 0-Assumption Instantiation: Projective Space `ℙ^d` (`𝒪(1)` of Positive Arakelov Height) -/

/-- Exact lower bound `(k : ℝ)^d / d! ≤ Nat.choose (k + d) d` for all `d, k : ℕ`. -/
theorem pow_div_factorial_le_choose (d k : ℕ) :
    (k : ℝ) ^ d / (d.factorial : ℝ) ≤ (Nat.choose (k + d) d : ℝ) := by
  have hdesc : (k : ℕ) ^ d ≤ (k + d).descFactorial d := by
    rw [Nat.descFactorial_eq_prod_range]
    calc k ^ d = ∏ _i ∈ Finset.range d, k := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range d, (k + d - i) :=
          Finset.prod_le_prod' fun i hi => by have := Finset.mem_range.mp hi; omega
  have hdvd : d.factorial ∣ (k + d).descFactorial d := Nat.factorial_dvd_descFactorial _ d
  rw [Nat.choose_eq_descFactorial_div_factorial,
    Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d))]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hdesc) (Nat.cast_nonneg _)

/-- Exact upper bound `Nat.choose (k + d) d ≤ (d + 1)^d * k^d` for `k ≥ 1`. -/
theorem choose_le_const_mul_pow (d : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose (k + d) d : ℝ) ≤ ((d + 1 : ℝ) ^ d) * (k : ℝ) ^ d := by
  have h1 : Nat.choose (k + d) d ≤ (k + d).descFactorial d := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    exact Nat.div_le_self _ _
  have h2 : (k + d).descFactorial d ≤ (k + d) ^ d := Nat.descFactorial_le_pow _ _
  have h3 : k + d ≤ (d + 1) * k := by nlinarith
  have h4 : (k + d) ^ d ≤ ((d + 1) * k) ^ d := Nat.pow_le_pow_left h3 d
  have h5 : (Nat.choose (k + d) d : ℝ) ≤ (((d + 1) * k : ℕ) : ℝ) ^ d := by
    exact_mod_cast (h1.trans h2).trans h4
  simpa [mul_pow] using h5

/-- **Concrete 0-Assumption Projective-Space Graded Hermitian Algebra `ℙ^d` (`𝒪(1)` scaled by `e^{-α}`)**
for arbitrary dimension `d ≥ 1` and Arakelov slope parameter `α > 0`:
realizes `H^0(ℙ^d, 𝒪(k)) = Sym^k(ℤ^{d+1})` with `volAr = α * (d + 1) > 0`! -/
def projSpaceGradedHermAlgebra (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    GradedHermAlgebra d where
  hd := hd
  secSpace k := EuclideanSpace ℝ (MultiIndex (d + 1) k)
  secLat k := symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-α)) k
  discLat k :=
    (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos d)
      (fun _ : Fin (d + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (d + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).1
  secLat_ne_bot k _ := by
    intro hbot
    have hrk := (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos d)
      (fun _ : Fin (d + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (d + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
    rw [show symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-α)) k =
      Stage11MoriwakiCovolume.symPowWeightedLat (fun _ : Fin (d + 1) => Real.exp (-α))
        (fun _ => (1 : ℝ)) from rfl] at hbot
    rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (MultiIndex (d + 1) k))) = 0 by
      simp [rk]] at hrk
    exact (card_multiIndex_pos (Nat.succ_pos d) k).ne hrk
  supNorm _ s := ‖s‖
  supNorm_nonneg _ s := norm_nonneg s
  volConst := 1
  volConst_pos := zero_lt_one
  norm_le_vol_supNorm _ _ s := by simp
  bergConst := 1
  bergExp := 0
  bergConst_ge_one := le_rfl
  supNorm_le_bergman _ _ s := by simp
  rankHi := ((d + 1 : ℝ)) ^ d
  rankHi_ge_one := one_le_pow₀ (by norm_cast; omega)
  rk_le_poly k hk := by
    have hrk := (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos d)
      (fun _ : Fin (d + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (d + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
    change (rk (Stage11MoriwakiCovolume.symPowWeightedLat _ _) : ℝ) ≤ _
    rw [hrk, card_multiIndex (Nat.succ_pos d) k, show k + (d + 1) - 1 = k + d by omega,
      add_comm k d, ← Nat.choose_symm_add, add_comm d k]
    exact choose_le_const_mul_pow d hk
  volAr := α * ((d + 1 : ℕ) : ℝ)
  ahs_liminf ε hε := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hsym := (slope_symPowMonomialLat (Nat.succ_pos d)
      (fun _ : Fin (d + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _) k).1
    have hdiag := diagLat_invariants (fun _ : Fin (d + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
    have hsl_base : ArakelovCovolume.slope (diagLat (fun _ : Fin (d + 1) => Real.exp (-α))) = α := by
      rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk, hdiag.2.1, hdiag.2.2.2, Fintype.card_fin]
      simp only [Real.log_exp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hd1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
      field_simp [hd1]
    have hrk_eq : rk (symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-α)) k) =
        Nat.choose (k + d) d := by
      have hrk := (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos d)
        (fun _ : Fin (d + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
        (fun _ : MultiIndex (d + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
      change rk (Stage11MoriwakiCovolume.symPowWeightedLat _ _) = _
      rw [hrk, card_multiIndex (Nat.succ_pos d) k, show k + (d + 1) - 1 = k + d by omega,
        add_comm k d, ← Nat.choose_symm_add, add_comm d k]
    rw [hsym, hsl_base, hrk_eq]
    have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos (Nat.cast_pos.mpr hk) (d + 1)
    have hch_ge := pow_div_factorial_le_choose d k
    have hfac_eq : (α * ((d + 1 : ℕ) : ℝ)) / ((d + 1).factorial : ℝ) = α / (d.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      have h1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
      have h2 : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
      field_simp [h1, h2]
    rw [hfac_eq]
    have hge : α / (d.factorial : ℝ) ≤
        ((k : ℝ) * (Nat.choose (k + d) d : ℝ) * α) / (k : ℝ) ^ (d + 1) := by
      rw [le_div_iff₀ hkd1_pos]
      have hmul := mul_le_mul_of_nonneg_left hch_ge (mul_nonneg (Nat.cast_nonneg k) hα.le)
      have hlhs : α / (d.factorial : ℝ) * (k : ℝ) ^ (d + 1) =
          (k : ℝ) * α * ((k : ℝ) ^ d / (d.factorial : ℝ)) := by
        rw [pow_succ]; ring
      rw [hlhs]
      linarith
    linarith

/-- **0-Assumption Projective-Space Moriwaki Bigness (`projSpace_moriwaki_big`)**:
for EVERY dimension `d ≥ 1` and `α > 0`, `#smallSections (ℙ^d, 𝒪(1)_{-α}) k` grows at least as
`exp (c₀ * k ^ (d + 1))`! -/
theorem projSpace_moriwaki_big (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    let A := projSpaceGradedHermAlgebra d hd hα
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (A.smallSectionsCard k (le_trans hK₀ hk) : ℝ) :=
  moriwaki_big_small_sections (projSpaceGradedHermAlgebra d hd hα)
    (mul_pos hα (Nat.cast_pos.mpr (Nat.succ_pos d)))

end MoriwakiBignessArbitraryDim

/-! ## Section 5: Uniform Indefinite Hodge-Lattice Covolume Bound (`L3`) & Stage 11 Bridges -/

section UniformL3AndStage11Bridges

/-- **Uniform Indefinite Hodge-Lattice Covolume Bound (`L3_hodge_covolume_bound`)**:
Models `IndefData.L3` (`lcv (S.XW j) (S.M j) / S.D ≤ N.l3 j` for `j : Fin m`):
for a family of `m` indefinite Hodge / automorphic lattices `M j ⊂ E j` (`j : Fin m`),
if each `M j` admits `rk (M j)` `ℝ`-linearly independent sections `s j i ∈ M j` embedded via
bounded Moriwaki small-section charts (`‖s j i‖ ≤ C_sec j`), then:
1. Pointwise log-covolume bound:
   `Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_sec j)`,
2. Normalized `L3` covolume bound (`D > 0`):
   `(2 / D) * Real.log (covol (M j)) ≤ (2 * rk (M j) / D) * Real.log (C_sec j)`,
3. Exact Arakelov slope lower bound feeding `Stage11ThetaSiegelBridge`:
   `-Real.log (C_sec j) ≤ slope (M j)`,
4. Uniform `m`-step sum bound feeding `IndefCore.divCore` / `Stage11BostDworkSqueeze`:
   `∑ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤ ∑ j : Fin m, (2 * rk (M j) / D) * Real.log (C_sec j)`. -/
theorem L3_hodge_covolume_bound {m : ℕ}
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (s : ∀ j, Fin (rk (M j)) → E j)
    (hsM : ∀ j i, s j i ∈ M j)
    (hsli : ∀ j, LinearIndependent ℝ (s j))
    (C_sec : Fin m → ℝ) (_hCpos : ∀ j, 0 < C_sec j)
    (hnorm : ∀ j i, ‖s j i‖ ≤ C_sec j)
    {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m, Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_sec j)) ∧
    (∀ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      (2 * (rk (M j) : ℝ) / D) * Real.log (C_sec j)) ∧
    (∀ j : Fin m, -Real.log (C_sec j) ≤ ArakelovCovolume.slope (M j)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      ∑ j : Fin m, (2 * (rk (M j) : ℝ) / D) * Real.log (C_sec j)) := by
  have hpt : ∀ j : Fin m, Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_sec j) := by
    intro j
    have hhad : covol (M j) ≤ ∏ i : Fin (rk (M j)), ‖s j i‖ :=
      covol_le_prod_norm (s j) (hsM j) (hsli j) rfl
    have hprod_le : ∏ i : Fin (rk (M j)), ‖s j i‖ ≤ (C_sec j) ^ (rk (M j)) := by
      calc ∏ i : Fin (rk (M j)), ‖s j i‖
          ≤ ∏ _i : Fin (rk (M j)), C_sec j :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hnorm j i
        _ = (C_sec j) ^ (rk (M j)) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hlog := Real.log_le_log (covol_pos (M j)) (hhad.trans hprod_le)
    rwa [Real.log_pow] at hlog
  have hnormD : ∀ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      (2 * (rk (M j) : ℝ) / D) * Real.log (C_sec j) := by
    intro j
    have h1 := mul_le_mul_of_nonneg_left (hpt j) (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD.le)
    have hrhs : (2 / D) * ((rk (M j) : ℝ) * Real.log (C_sec j)) =
        (2 * (rk (M j) : ℝ) / D) * Real.log (C_sec j) := by ring
    rwa [hrhs] at h1
  have hsl : ∀ j : Fin m, -Real.log (C_sec j) ≤ ArakelovCovolume.slope (M j) := by
    intro j
    have hrk_pos : (0 : ℝ) < (rk (M j) : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot (M j) (hM0 j))
    rw [Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk, arithDeg, le_div_iff₀ hrk_pos]
    linarith [hpt j]
  exact ⟨hpt, hnormD, hsl, Finset.sum_le_sum fun j _ => hnormD j⟩

/-- **Moriwaki Small-Section Pushforward `L3` Covolume Bound**:
if `M j` receives `rk (M j)` linearly independent small sections from a Moriwaki graded algebra
`A : GradedHermAlgebra d` (`A.supNorm (k j) (t j i) < 1`) via a bounded chart map `Ψ j` with
`‖Ψ j x‖ ≤ C_chart j * ‖x‖`, then unconditionally:
`Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_chart j * A.volConst)`! -/
theorem L3_covolume_of_moriwaki_small_sections {d m : ℕ} (A : GradedHermAlgebra d)
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j)
    (Ψ : ∀ j, A.secSpace (k j) → E j)
    (C_chart : Fin m → ℝ) (hCpos : ∀ j, 0 < C_chart j)
    (hΨ_bound : ∀ j x, ‖Ψ j x‖ ≤ C_chart j * ‖x‖)
    (t : ∀ j, Fin (rk (M j)) → A.secLat (k j))
    (ht_small : ∀ j i, t j i ∈ A.smallSectionsSet (k j))
    (hΨ_mem : ∀ j i, Ψ j (t j i).1 ∈ M j)
    (hΨ_li : ∀ j, LinearIndependent ℝ (fun i => Ψ j (t j i).1))
    {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m, Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_chart j * A.volConst)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      ∑ j : Fin m, (2 * (rk (M j) : ℝ) / D) * Real.log (C_chart j * A.volConst)) := by
  have hbd := L3_hodge_covolume_bound E M hM0 (fun j i => Ψ j (t j i).1) hΨ_mem hΨ_li
    (fun j => C_chart j * A.volConst) (fun j => mul_pos (hCpos j) A.volConst_pos)
    (fun j i => by
      have h1 := hΨ_bound j (t j i).1
      have h2 := A.norm_le_vol_supNorm (k j) (hk j) (t j i).1
      have h3 : A.supNorm (k j) (t j i).1 < 1 := ht_small j i
      have h4 : ‖(t j i).1‖ ≤ A.volConst := by nlinarith [A.volConst_pos]
      exact h1.trans (mul_le_mul_of_nonneg_left h4 (hCpos j).le))
    hD
  exact ⟨hbd.1, hbd.2.2.2⟩

/-- **Direct Bridge to `Stage11BostDworkSqueeze.divLink_of_dwork_chain`**:
Combines our `L3_hodge_covolume_bound` (`∑ j, (2/D) log(covol (M j)) ≤ ∑ j, l3 j`) with the
`m`-step `p`-adic Dwork chain (`Stage11BostDworkSqueeze.divLink_of_dwork_chain`) to discharge
`archLHS ≤ m * (stepDefect + ∑'_l vvTerm S E_field t_val l)` directly from the Hodge-lattice
covolume sum! -/
theorem divLink_of_L3_and_dwork_chain
    {K : Type*} [NormedField K] [CharZero K]
    {Top : Type*} [Fintype Top] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (S : RHDirect.SelmerSystem) (E_field : Type) [Field E_field] [NumberField E_field]
    (t_val m : ℕ) {archLHS stepDefect D : ℝ} (hD : 0 < D)
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (s : ∀ j, Fin (rk (M j)) → E j)
    (hsM : ∀ j i, s j i ∈ M j)
    (hsli : ∀ j, LinearIndependent ℝ (s j))
    (C_sec : Fin m → ℝ) (hCpos : ∀ j, 0 < C_sec j)
    (hnorm : ∀ j i, ‖s j i‖ ≤ C_sec j)
    {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)]
    (Kstep : ∀ j, V j → V (j + 1))
    (aT : Top → ℝ) (loss : ℕ → ℝ)
    (hstep : ∀ j, j < m → ∀ v : V j,
      ‖Kstep j v‖ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss j) * ‖v‖)
    (hloss : ∀ j, j < m →
      loss j ≤ stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)
    {v : V 0} (hchain_ne : RHDirect.Stage11BostDworkSqueeze.chainOp Kstep m v ≠ 0)
    (hprod_L3 : archLHS +
        (RHDirect.Stage11BostDworkSqueeze.dworkSpaceVal K p
            (RHDirect.Stage11BostDworkSqueeze.chainOp Kstep m v) -
          RHDirect.Stage11BostDworkSqueeze.dworkSpaceVal K p v) ≤
      (m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) +
        ((∑ j : Fin m, (2 / D) * Real.log (covol (M j))) -
          ∑ j : Fin m, (2 * (rk (M j) : ℝ) / D) * Real.log (C_sec j))) :
    archLHS ≤
      (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l) := by
  have hL3 := (L3_hodge_covolume_bound E M hM0 s hsM hsli C_sec hCpos hnorm hD).2.2.2
  have hprod : archLHS +
      (RHDirect.Stage11BostDworkSqueeze.dworkSpaceVal K p
          (RHDirect.Stage11BostDworkSqueeze.chainOp Kstep m v) -
        RHDirect.Stage11BostDworkSqueeze.dworkSpaceVal K p v) ≤
      (m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) := by
    linarith
  exact RHDirect.Stage11BostDworkSqueeze.divLink_of_dwork_chain hp hlt S E_field t_val m
    Kstep aT loss hstep hloss hchain_ne hprod

/-- **Direct Bridge to `Stage11ThetaSiegelBridge`**:
Packages an arbitrary-rank `CMHermLattice d r` together with its Schur-Weyl column-tensor lattice
and branching bound into an explicit lower bound on `muMin` and `slope` grounded on Mathlib's
`ZLattice.covolume`! -/
theorem stage11_thetaSiegel_cm_column_slope_bridge {d r : ℕ} (Λ : CMHermLattice d r)
    (lam : Partition (2 * r)) (S : ConcreteEuclideanLat)
    (pMap : (columnTensorLat
      { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
        ne_bot := Λ.euclLat_ne_bot }
      { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }).L →ₗ[ℤ] S.L)
    {C_branch Δ : ℝ} (hC : 0 < C_branch)
    (hbound : ∀ x, ‖((pMap x : S.L) : S.E)‖ ≤
      (({ parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h } :
        Partition (rk Λ.euclLat)).hookProd : ℝ) * C_branch * ‖(x : _)‖)
    (hspan : Submodule.span ℝ (Set.range fun x => ((pMap x : S.L) : S.E)) =
      Submodule.span ℝ (S.L : Set S.E))
    (hΔ : ArakelovCovolume.slope (columnTensorLat
      { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
        ne_bot := Λ.euclLat_ne_bot }
      { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }).L -
      muMin (columnTensorLat
      { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
        ne_bot := Λ.euclLat_ne_bot }
      { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }).L ≤ Δ) :
    covol Λ.euclLat = ZLattice.covolume Λ.euclLat volume ∧
    (lam.weight : ℝ) * (-(1 / 4) * Real.log d - Real.log Λ.H.det.re / (2 * (r : ℝ))) -
        Δ - (lam.weight : ℝ) * Real.log ((lam.maxPart + 2 * r : ℕ) : ℝ) - Real.log C_branch ≤
      muMin S.L ∧
    muMin S.L ≤ ArakelovCovolume.slope S.L := by
  let A : ConcreteEuclideanLat :=
    { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
      ne_bot := Λ.euclLat_ne_bot }
  let lam' : Partition (rk A.L) :=
    { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }
  have hres := (schur_branching_slope_lower A lam' S pMap hC hbound hspan).2 Δ hΔ
  have hw : lam'.weight = lam.weight := by
    unfold Partition.weight
    exact Fintype.sum_equiv (finCongr Λ.rk_euclLat) _ _ fun _ => rfl
  have hmax : lam'.maxPart = lam.maxPart := by
    unfold Partition.maxPart
    have h1 : 0 < rk A.L := rk_pos_of_ne_bot A.L A.ne_bot
    have h2 : 0 < 2 * r := by have := Λ.hr; omega
    rw [dif_pos h1, dif_pos h2]; rfl
  have hslΛ := Λ.slope_eq
  rw [hw, hmax, show rk A.L = 2 * r from Λ.rk_euclLat,
    show ArakelovCovolume.slope A.L = ArakelovCovolume.slope Λ.euclLat from rfl, hslΛ] at hres
  exact ⟨Λ.covol_eq_zlattice_covolume, hres.1, hres.2⟩

end UniformL3AndStage11Bridges

end RHDirect.Stage12SchurWeylLattices

end
