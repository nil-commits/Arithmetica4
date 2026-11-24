import RHDirect.ThetaSlopeEngine
import RHDirect.Stage2ThetaWire
import RHDirect.Stage3ThetaSiegelBridge
import RHDirect.Stage4ArakelovBost
import RHDirect.Stage10GeometryOfNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# RHDirect.Stage11DefiniteUnitaryChain

Unconditional, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of **Concrete Positive-Definite
Hermitian Unitary Spaces `X_0, ..., X_m`, Finite Definite Unitary Automorphism Groups, Concrete
Finite-Dimensional Automorphic Form Spaces, Theta-Lift Kernel Operators, the `m`-Step Iterated
Theta-Lift Chain `chainOpM`, Exact `ThetaSlopeEngine.RankVal` Realization, and Hermitian Lattice
Covolume / Minkowski–Bost Bridges** in pure Mathlib `v4.33.1`.

## Contents
1. **Concrete Positive-Definite Hermitian Lattice Spaces `(V_j, L_j)` & Finite Unitary Group**:
   - `DefiniteHermitianSpace N := EuclideanSpace ℂ (Fin N)` with exact real Euclidean isometry
     `realEquiv N : DefiniteHermitianSpace N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * N))`.
   - Concrete CM orders `CMOrder d = ℤ[√-d]` (`d = 1` gives `ℤ[i]`), standard CM lattices
     `stdCMLattice N d hd`, positive-definite Hermitian square root `posDefSqrt H hH`, and concrete
     Hermitian lattices `hermitianLatticeOfPosDef d hd H hH` with Gram matrix `H` and exact
     covolume `(√d)^N * H.det.re` (`covolume_hermitian_ofPosDef`).
   - Definite unitary automorphism group `DefiniteUnitaryGroup L = { g ∈ U(N) | g(L) = L }` and
     unconditional finiteness theorem `finite_definiteUnitaryGroup`.
2. **Concrete Finite-Dimensional Automorphic Form Spaces `𝒜(U(V_j))` & Theta-Lift Kernels**:
   - Finite genus `HermitianGenus N`, Petersson weights `peterssonWeight G i = |Aut(L_i)|⁻¹ > 0`,
     and concrete weighted Hilbert space `DefiniteAutomorphicSpace G`.
   - Concrete lattice homomorphism lattice `LatticeHom L M`, unconditional finiteness of bounded
     homomorphisms (`finite_latticeHom_bounded`) and representation sets (`finite_repSet`),
     algebraic representation kernel `thetaRepKernel`, and unconditionally convergent Gaussian
     theta kernel `gaussianThetaKernel` (`summable_gaussianThetaHom`).
   - Concrete theta-lift kernel operator `thetaKernelOp` with exact adjointness
     (`thetaKernelOp_adjoint`), concrete Rallis seesaw positivity (`rallis_seesaw_inner_nonneg`),
     and weighted Schur's test spectral-norm bound (`thetaKernelOp_norm_le_schur`).
3. **Concrete `m`-Step Iterated Chain Operator `chainOpM` & Exact `RankVal` Realization**:
   - Concrete rank tower `chainRank k t j = k + j * (t + 1)`, `DefiniteUnitaryTower m k t`,
     iterated composition `chainOpM`, reversed adjoint chain `chainOpM_rev`, exact adjoint chain
     reversal (`chainOpM_adjoint`), submultiplicative Schur norm bound (`chainOpM_norm_le`),
     unconditional denominator clearing (`chainOpM_clears_denominators`), and exact bridge to
     `ThetaSlopeEngine.IteratedThetaChain` and `RallisSeesaw.RankSteppedChain`.
   - Unconditional `ThetaSlopeEngine.RankVal` realization (`chainRank_realizes_rankVal`) constructing
     explicit `R : ChainRanks` and concrete definite unitary tower matching `R.f, R.m, R.k, R.t, R.n`.
4. **Hermitian Tensor Covolume Scaling & `Stage4ArakelovBost` / `Stage10GeometryOfNumbers` Bridge**:
   - Positive-definiteness and determinant of Hermitian Kronecker tensor products
     (`hermitianTensorMatrix_posDef`, `det_hermitianTensorMatrix`), exact covolume scaling
     (`covolume_hermitian_tensor_eq`), and additive Gaussian Arakelov slope (`slope_hermitian_tensor_eq`).
   - Direct `m`-step chain bridge (`chain_hermitian_minkowski_bost_bridge`) connecting
     `Stage4ArakelovBost` (`slope`, `muMax`) and `Stage10GeometryOfNumbers`
     (`minkowski_second_theorem_upper`, `hermite_minkowski_bound_all_dims`) to every stage `L_j`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder

namespace RHDirect.Stage11DefiniteUnitaryChain

/-! ## Section 1: Concrete Positive-Definite Hermitian Spaces, CM-Order Lattices & Finite Unitary Automorphism Group -/

section HermitianSpacesAndLattices

/-- Concrete positive-definite Hermitian space `V_N = ℂ^N` with standard inner product `⟪u, v⟫_ℂ`. -/
abbrev DefiniteHermitianSpace (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- Index equivalence `Fin N × Fin 2 ≃ Fin (2 * N)` organizing real and imaginary coordinates. -/
def hermCoordEquiv (N : ℕ) : Fin N × Fin 2 ≃ Fin (2 * N) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))

/-- Exact real-linear isometry equivalence between `DefiniteHermitianSpace N` (`ℂ^N`) and the
underlying `2N`-dimensional real Euclidean space `EuclideanSpace ℝ (Fin (2 * N))`. -/
def realEquiv (N : ℕ) : DefiniteHermitianSpace N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * N)) where
  toFun v := WithLp.toLp 2 fun k =>
    let p := (hermCoordEquiv N).symm k
    if p.2 = 0 then (v p.1).re else (v p.1).im
  invFun x := WithLp.toLp 2 fun i =>
    ⟨x (hermCoordEquiv N (i, 0)), x (hermCoordEquiv N (i, 1))⟩
  map_add' u v := by
    ext k
    simp only [WithLp.ofLp_add, Pi.add_apply, Complex.add_re, Complex.add_im]
    split_ifs <;> rfl
  map_smul' c v := by
    ext k
    simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul,
      RingHom.id_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.mul_im, add_zero]
    split_ifs <;> rfl
  left_inv v := by
    ext i
    apply Complex.ext <;> simp
  right_inv x := by
    ext k
    rcases h : (hermCoordEquiv N).symm k with ⟨i, j⟩
    have hk : hermCoordEquiv N (i, j) = k := by
      rw [← h, Equiv.apply_symm_apply]
    fin_cases j
    · simp [← hk]
    · simp [← hk]
  norm_map' v := by
    change ‖WithLp.toLp 2 (fun k : Fin (2 * N) =>
        let p := (hermCoordEquiv N).symm k
        if p.2 = 0 then (v p.1).re else (v p.1).im)‖ = ‖v‖
    have hsq : ‖WithLp.toLp 2 (fun k : Fin (2 * N) =>
        let p := (hermCoordEquiv N).symm k
        if p.2 = 0 then (v p.1).re else (v p.1).im)‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      rw [← (hermCoordEquiv N).sum_comp]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_two]
      simp only [Equiv.symm_apply_apply, ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff,
        Real.norm_eq_abs, sq_abs]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun k : Fin (2 * N) =>
      let p := (hermCoordEquiv N).symm k
      if p.2 = 0 then (v p.1).re else (v p.1).im)), norm_nonneg v]

@[simp]
lemma realEquiv_apply_zero {N : ℕ} (v : DefiniteHermitianSpace N) (i : Fin N) :
    (realEquiv N v).ofLp (hermCoordEquiv N (i, 0)) = (v i).re := by
  change (if ((hermCoordEquiv N).symm (hermCoordEquiv N (i, 0))).2 = 0 then _ else _) = _
  simp

@[simp]
lemma realEquiv_apply_one {N : ℕ} (v : DefiniteHermitianSpace N) (i : Fin N) :
    (realEquiv N v).ofLp (hermCoordEquiv N (i, 1)) = (v i).im := by
  change (if ((hermCoordEquiv N).symm (hermCoordEquiv N (i, 1))).2 = 0 then _ else _) = _
  simp

theorem finrank_definiteHermitianSpace_complex (N : ℕ) :
    Module.finrank ℂ (DefiniteHermitianSpace N) = N := by
  rw [finrank_euclideanSpace_fin]

theorem finrank_definiteHermitianSpace_real (N : ℕ) :
    Module.finrank ℝ (DefiniteHermitianSpace N) = 2 * N := by
  rw [(realEquiv N).toLinearEquiv.finrank_eq, finrank_euclideanSpace_fin]

/-- Helper: `Matrix.toEuclideanLin` preserves matrix multiplication. -/
lemma toEuclideanLin_mul_eq {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin k) ℂ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  ext v i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Helper: `Matrix.toEuclideanLin 1 = LinearMap.id`. -/
lemma toEuclideanLin_one_eq (N : ℕ) :
    Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) = LinearMap.id := by
  ext v i
  simp

/-- Helper: `Real.sqrt (x ^ n) = (Real.sqrt x) ^ n` for `x ≥ 0`. -/
lemma sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]

/-- Imaginary quadratic CM generator `ω_d = √d · i ∈ ℂ`. -/
def cmGen (d : ℕ) : ℂ := ((Real.sqrt d : ℝ) : ℂ) * Complex.I

theorem cmGen_sq (d : ℕ) : cmGen d ^ 2 = -(d : ℂ) := by
  unfold cmGen
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

theorem star_cmGen (d : ℕ) : star (cmGen d) = -cmGen d := by
  unfold cmGen
  simp

/-- Concrete CM order `𝒪_d = ℤ[√(-d)] ⊆ ℂ` (`d = 1` gives the Gaussian integers `ℤ[i]`). -/
def CMOrder (d : ℕ) : Subring ℂ where
  carrier := { z : ℂ | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * cmGen d }
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
    exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  mul_mem' := by
    rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
    refine ⟨a₁ * a₂ - (d : ℤ) * b₁ * b₂, a₁ * b₂ + b₁ * a₂, ?_⟩
    have hsq := cmGen_sq d
    push_cast
    linear_combination ((b₁ : ℂ) * (b₂ : ℂ)) * hsq

theorem star_mem_cmOrder {d : ℕ} {z : ℂ} (hz : z ∈ CMOrder d) : star z ∈ CMOrder d := by
  rcases hz with ⟨a, b, rfl⟩
  refine ⟨a, -b, ?_⟩
  simp [star_cmGen]

theorem cmOrder_one_iff (z : ℂ) :
    z ∈ CMOrder 1 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * Complex.I := by
  simp [CMOrder, cmGen]

/-- A concrete full-rank positive-definite Hermitian lattice `L ⊂ DefiniteHermitianSpace N`. -/
structure HermitianLattice (N : ℕ) where
  lat : Submodule ℤ (DefiniteHermitianSpace N)
  [disc : DiscreteTopology lat]
  [zlat : IsZLattice ℝ lat]

attribute [instance] HermitianLattice.disc HermitianLattice.zlat

/-- Underlying `2N`-dimensional real Euclidean lattice in `EuclideanSpace ℝ (Fin (2 * N))`. -/
def HermitianLattice.realLat {N : ℕ} (L : HermitianLattice N) :
    Submodule ℤ (EuclideanSpace ℝ (Fin (2 * N))) :=
  L.lat.map ((realEquiv N).toLinearEquiv.toLinearMap.restrictScalars ℤ)

/-- `ℤ`-linear equivalence between `L.lat` and `L.realLat`. -/
def HermitianLattice.realLatEquiv {N : ℕ} (L : HermitianLattice N) :
    L.lat ≃ₗ[ℤ] L.realLat where
  toFun x := ⟨realEquiv N x.1, x.1, x.2, rfl⟩
  invFun y := ⟨(realEquiv N).symm y.1, by
    rcases y.2 with ⟨x, hx, hxy⟩
    have : (realEquiv N).symm y.1 = x := by
      rw [← hxy]; exact (realEquiv N).symm_apply_apply x
    rwa [this]⟩
  map_add' x y := Subtype.ext (map_add (realEquiv N) x.1 y.1)
  map_smul' c x := Subtype.ext (map_zsmul (realEquiv N) c x.1)
  left_inv x := Subtype.ext ((realEquiv N).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((realEquiv N).apply_symm_apply y.1)

instance HermitianLattice.realLat_discrete {N : ℕ} (L : HermitianLattice N) :
    DiscreteTopology L.realLat := by
  refine DiscreteTopology.of_continuous_injective (f := L.realLatEquiv.symm) ?_
    L.realLatEquiv.symm.injective
  exact Continuous.subtype_mk ((realEquiv N).symm.continuous.comp continuous_subtype_val) _

instance HermitianLattice.realLat_isZLattice {N : ℕ} (L : HermitianLattice N) :
    IsZLattice ℝ L.realLat := by
  constructor
  have h1 : Submodule.span ℝ (L.realLat : Set (EuclideanSpace ℝ (Fin (2 * N)))) =
      (Submodule.span ℝ (L.lat : Set (DefiniteHermitianSpace N))).map
        (realEquiv N).toLinearEquiv.toLinearMap := by
    rw [Submodule.map_span]
    rfl
  rw [h1, IsZLattice.span_top (K := ℝ) (L := L.lat), Submodule.map_top, LinearEquiv.range]

/-- Every full-rank Hermitian lattice `L ⊂ ℂ^N` has `ℤ`-rank `2 * N`. -/
theorem HermitianLattice.rk_eq {N : ℕ} (L : HermitianLattice N) :
    ArakelovCovolume.rk L.lat = 2 * N := by
  unfold ArakelovCovolume.rk
  rw [ZLattice.rank ℝ L.lat, finrank_definiteHermitianSpace_real]

/-- Canonical `ℤ`-basis of `L.lat` indexed by `Fin (2 * N)`. -/
def HermitianLattice.zBasis {N : ℕ} (L : HermitianLattice N) : Basis (Fin (2 * N)) ℤ L.lat :=
  (Stage10GeometryOfNumbers.basisOfZLattice L.realLat).map L.realLatEquiv.symm

/-- Exact equality between `ArakelovCovolume.covol L.lat` and `ZLattice.covolume L.realLat volume`. -/
theorem HermitianLattice.covol_eq_real_covolume {N : ℕ} (L : HermitianLattice N) :
    ArakelovCovolume.covol L.lat = ZLattice.covolume L.realLat volume := by
  let bR : Basis (Fin (2 * N)) ℤ L.realLat := Stage10GeometryOfNumbers.basisOfZLattice L.realLat
  let bC : Basis (Fin (2 * N)) ℤ L.lat := bR.map L.realLatEquiv.symm
  rw [ArakelovCovolume.covol_eq_sqrt_det_gram L.lat bC,
    Stage10GeometryOfNumbers.covolume_eq_abs_det L.realLat bR]
  let B : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ :=
    Matrix.of fun i j => (bR i : EuclideanSpace ℝ (Fin (2 * N))) j
  have hgram : Matrix.gram ℝ (fun i => (bC i : DefiniteHermitianSpace N)) = B * Bᵀ := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply]
    have hmap : ∀ k, realEquiv N (bC k : DefiniteHermitianSpace N) =
        (bR k : EuclideanSpace ℝ (Fin (2 * N))) := by
      intro k
      change realEquiv N ((realEquiv N).symm (bR k : EuclideanSpace ℝ (Fin (2 * N)))) = _
      exact (realEquiv N).apply_symm_apply _
    rw [← (realEquiv N).inner_map_map, hmap i, hmap j,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]

/-- Standard `ℤ`-basis vectors `{ e_i, √d · i · e_i }` of `(CMOrder d)^N ⊂ ℂ^N`. -/
def stdCMBasisVec (N d : ℕ) (k : Fin (2 * N)) : DefiniteHermitianSpace N :=
  let p := (hermCoordEquiv N).symm k
  EuclideanSpace.single p.1 (if p.2 = 0 then (1 : ℂ) else cmGen d)

theorem stdCMBasisVec_real_linearIndependent (N d : ℕ) (hd : 0 < d) :
    LinearIndependent ℝ (stdCMBasisVec N d) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hsqrt : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  rcases hk : (hermCoordEquiv N).symm k with ⟨i, j⟩
  have hk' : hermCoordEquiv N (i, j) = k := by rw [← hk, Equiv.apply_symm_apply]
  have hcoord := congrArg (fun v : DefiniteHermitianSpace N => v i) hc
  simp only [WithLp.ofLp_zero, Pi.zero_apply] at hcoord
  have hsum : (∑ m : Fin (2 * N), c m • stdCMBasisVec N d m) i =
      ((c (hermCoordEquiv N (i, 0)) : ℝ) : ℂ) +
        ((c (hermCoordEquiv N (i, 1)) : ℝ) : ℂ) * cmGen d := by
    have heval : (∑ m : Fin (2 * N), c m • stdCMBasisVec N d m) i =
        ∑ m : Fin (2 * N), (c m • stdCMBasisVec N d m) i := by
      simp [WithLp.ofLp_sum]
    rw [heval, ← (hermCoordEquiv N).sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · rw [Fin.sum_univ_two]
      simp [stdCMBasisVec, Complex.real_smul]
    · intro i' _ hi'
      refine Finset.sum_eq_zero fun j' _ => ?_
      simp [stdCMBasisVec, hi'.symm]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsum] at hcoord
  have hre := congrArg Complex.re hcoord
  have him := congrArg Complex.im hcoord
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, cmGen, Complex.I_re, mul_zero, add_zero, Complex.zero_re,
    Complex.add_im, Complex.mul_im, Complex.I_im, mul_one, zero_add, Complex.zero_im] at hre him
  fin_cases j
  · rwa [← hk']
  · rw [← hk']
    exact (mul_eq_zero.mp him).resolve_right hsqrt.ne'

theorem stdCMBasisVec_real_span (N d : ℕ) (hd : 0 < d) :
    Submodule.span ℝ (Set.range (stdCMBasisVec N d)) = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [finrank_span_eq_card (stdCMBasisVec_real_linearIndependent N d hd), Fintype.card_fin,
    finrank_definiteHermitianSpace_real]

/-- The `ℝ`-basis `stdCMBasisVec N d` of `DefiniteHermitianSpace N`. -/
def stdCMRealBasis (N d : ℕ) (hd : 0 < d) : Basis (Fin (2 * N)) ℝ (DefiniteHermitianSpace N) :=
  Basis.mk (stdCMBasisVec_real_linearIndependent N d hd) (stdCMBasisVec_real_span N d hd).ge

/-- Standard CM-order lattice `(CMOrder d)^N ⊂ DefiniteHermitianSpace N`. -/
def stdCMLattice (N d : ℕ) (hd : 0 < d) : HermitianLattice N where
  lat := Submodule.span ℤ (Set.range (stdCMRealBasis N d hd))
  disc := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (stdCMRealBasis N d hd))))
  zlat := ⟨ZSpan.span_top (stdCMRealBasis N d hd)⟩

/-- Canonical `ℤ`-basis of `(stdCMLattice N d hd).lat` given by `stdCMBasisVec N d`. -/
def stdCMZBasis (N d : ℕ) (hd : 0 < d) :
    Basis (Fin (2 * N)) ℤ (stdCMLattice N d hd).lat :=
  Basis.mk
    (v := fun k => ⟨stdCMRealBasis N d hd k, Submodule.subset_span ⟨k, rfl⟩⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have hR : ∑ j : Fin (2 * N), (c j : ℝ) • stdCMBasisVec N d j = 0 := by
        have hval := congrArg Subtype.val hc
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
          Int.cast_smul_eq_zsmul, stdCMRealBasis, Basis.mk_apply] using hval
      exact_mod_cast Fintype.linearIndependent_iff.mp
        (stdCMBasisVec_real_linearIndependent N d hd) (fun j => (c j : ℝ)) hR k)
    (by
      intro x _
      have hx : x.1 ∈ Submodule.span ℤ (Set.range (stdCMRealBasis N d hd)) := x.2
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, hc⟩ := hx
      have hxeq : x = ∑ k : Fin (2 * N),
          c k • (⟨stdCMRealBasis N d hd k, Submodule.subset_span ⟨k, rfl⟩⟩ :
            (stdCMLattice N d hd).lat) := by
        apply Subtype.ext
        simpa [Submodule.coe_sum, Submodule.coe_smul] using hc.symm
      rw [hxeq]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

/-- Real inner product on `DefiniteHermitianSpace N` equals the real part of the complex inner
product. -/
lemma real_inner_eq_re_complex_inner {N : ℕ} (u v : DefiniteHermitianSpace N) :
    inner ℝ u v = (inner ℂ u v).re := by
  rw [← (realEquiv N).inner_map_map, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, dotProduct, Complex.re_sum]
  rw [← (hermCoordEquiv N).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp only [star_trivial, realEquiv_apply_zero, realEquiv_apply_one, Pi.star_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact covolume of the standard CM-order lattice `(CMOrder d)^N`: `covol = (√d)^N`. -/
theorem covol_stdCMLattice (N d : ℕ) (hd : 0 < d) :
    ArakelovCovolume.covol (stdCMLattice N d hd).lat = (Real.sqrt d) ^ N := by
  let bZ : Basis (Fin (2 * N)) ℤ (stdCMLattice N d hd).lat := stdCMZBasis N d hd
  rw [ArakelovCovolume.covol_eq_sqrt_det_gram (stdCMLattice N d hd).lat bZ]
  have hgram : Matrix.gram ℝ (fun k => (bZ k : DefiniteHermitianSpace N)) =
      Matrix.diagonal (fun k : Fin (2 * N) =>
        if ((hermCoordEquiv N).symm k).2 = 0 then (1 : ℝ) else (d : ℝ)) := by
    ext k l
    have hbk : (bZ k : DefiniteHermitianSpace N) = stdCMBasisVec N d k := by
      simp [bZ, stdCMZBasis, stdCMRealBasis]
    have hbl : (bZ l : DefiniteHermitianSpace N) = stdCMBasisVec N d l := by
      simp [bZ, stdCMZBasis, stdCMRealBasis]
    rw [Matrix.gram_apply, hbk, hbl, Matrix.diagonal_apply, real_inner_eq_re_complex_inner]
    rcases hk : (hermCoordEquiv N).symm k with ⟨ik, jk⟩
    rcases hl : (hermCoordEquiv N).symm l with ⟨il, jl⟩
    unfold stdCMBasisVec
    rw [hk, hl]
    by_cases hkl : k = l
    · subst hkl
      have heq : il = ik ∧ jl = jk := Prod.mk.inj (hl.symm.trans hk)
      rcases heq with ⟨rfl, rfl⟩
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      fin_cases jl
      · simp
      · have hne : (⟨1, Nat.one_lt_two⟩ : Fin 2) ≠ 0 := by decide
        simp only [hne, ↓reduceIte, PiLp.norm_single, cmGen, norm_mul, Complex.norm_real,
          Complex.norm_I, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        have hsq : (((Real.sqrt d : ℝ) : ℂ) ^ 2).re = (d : ℝ) := by
          rw [← Complex.ofReal_pow, Complex.ofReal_re, Real.sq_sqrt (Nat.cast_nonneg d)]
        simpa using hsq
    · rw [if_neg hkl]
      by_cases hi : ik = il
      · subst hi
        have hj : jk ≠ jl := fun h => hkl ((hermCoordEquiv N).symm.injective (by rw [hk, hl, h]))
        rw [EuclideanSpace.inner_single_left]
        fin_cases jk <;> fin_cases jl
        · exact absurd rfl hj
        · simp [cmGen]
        · simp [cmGen]
        · exact absurd rfl hj
      · rw [EuclideanSpace.inner_single_left]
        simp [Ne.symm hi]
  rw [hgram, Matrix.det_diagonal, ← (hermCoordEquiv N).prod_comp, Fintype.prod_prod_type]
  have hprod : ∏ i : Fin N, ∏ j : Fin 2,
      (if ((hermCoordEquiv N).symm (hermCoordEquiv N (i, j))).2 = 0 then (1 : ℝ) else (d : ℝ)) =
      (d : ℝ) ^ N := by
    simp [Fin.prod_univ_two]
  rw [hprod, sqrt_pow_nat (Nat.cast_nonneg d)]

/-- Membership characterization: `v ∈ (stdCMLattice N d hd).lat` iff every coordinate lies in
`CMOrder d`. -/
theorem mem_stdCMLattice_iff {N d : ℕ} (hd : 0 < d) (v : DefiniteHermitianSpace N) :
    v ∈ (stdCMLattice N d hd).lat ↔ ∀ i : Fin N, v i ∈ CMOrder d := by
  constructor
  · intro hv
    have hspan : (stdCMLattice N d hd).lat = Submodule.span ℤ (Set.range (stdCMBasisVec N d)) := by
      simp [stdCMLattice, stdCMRealBasis]
    rw [hspan] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      intro i
      unfold stdCMBasisVec
      by_cases hi : i = ((hermCoordEquiv N).symm k).1
      · simp only [PiLp.single_apply, hi, ↓reduceIte]
        split_ifs
        · exact (CMOrder d).one_mem
        · exact ⟨0, 1, by simp⟩
      · simp only [PiLp.single_apply, hi, ↓reduceIte]
        exact (CMOrder d).zero_mem
    | zero => intro i; exact (CMOrder d).zero_mem
    | add x y _ _ hx hy => intro i; exact (CMOrder d).add_mem (hx i) (hy i)
    | smul c x _ hx =>
      intro i
      have hc : (c : ℂ) ∈ CMOrder d := ⟨c, 0, by simp⟩
      simpa [zsmul_eq_mul] using (CMOrder d).mul_mem hc (hx i)
  · intro hv
    choose a b hab using hv
    have hveq : v = ∑ i : Fin N,
        (a i • stdCMBasisVec N d (hermCoordEquiv N (i, 0)) +
          b i • stdCMBasisVec N d (hermCoordEquiv N (i, 1))) := by
      ext i
      rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
      · simp [stdCMBasisVec, hab i]
      · intro i' _ hi'
        simp [stdCMBasisVec, hi'.symm]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hveq]
    refine Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hermCoordEquiv N (i, 0), ?_⟩)
      simp [stdCMRealBasis]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hermCoordEquiv N (i, 1), ?_⟩)
      simp [stdCMRealBasis]

/-- `stdCMLattice N d hd` is stable under scalar multiplication by `CMOrder d`. -/
theorem cmOrder_smul_mem_stdCMLattice {N d : ℕ} (hd : 0 < d) {α : ℂ} (hα : α ∈ CMOrder d)
    {v : DefiniteHermitianSpace N} (hv : v ∈ (stdCMLattice N d hd).lat) :
    α • v ∈ (stdCMLattice N d hd).lat := by
  rw [mem_stdCMLattice_iff hd] at hv ⊢
  intro i
  exact (CMOrder d).mul_mem hα (hv i)

/-- Positive-definite Hermitian square root `A = U * diag(√λ) * Uᴴ` of a positive-definite matrix
`H : Matrix (Fin N) (Fin N) ℂ`, satisfying `Aᴴ = A` and `Aᴴ * A = H`. -/
def posDefSqrt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    Matrix (Fin N) (Fin N) ℂ :=
  (hH.isHermitian.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
    Matrix.diagonal (fun i => ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ)) *
    star (hH.isHermitian.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

theorem posDefSqrt_isHermitian {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    (posDefSqrt H hH).IsHermitian := by
  unfold posDefSqrt Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_star]
  have hdiag : Matrix.diagonal (star (fun i : Fin N =>
      ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ))) =
      Matrix.diagonal (fun i : Fin N =>
        ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ)) := by
    congr 1; funext i; simp
  rw [hdiag, Matrix.mul_assoc]

theorem posDefSqrt_conjTranspose_mul_self {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    (posDefSqrt H hH)ᴴ * posDefSqrt H hH = H := by
  rw [(posDefSqrt_isHermitian H hH).eq]
  unfold posDefSqrt
  set U := hH.isHermitian.eigenvectorUnitary
  set D := Matrix.diagonal (fun i : Fin N => ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ))
  have hUU : star (U : Matrix (Fin N) (Fin N) ℂ) * (U : Matrix (Fin N) (Fin N) ℂ) = 1 := U.2.1
  calc ((U : Matrix _ _ ℂ) * D * star (U : Matrix _ _ ℂ)) *
          ((U : Matrix _ _ ℂ) * D * star (U : Matrix _ _ ℂ))
      = (U : Matrix _ _ ℂ) * D * (star (U : Matrix _ _ ℂ) * (U : Matrix _ _ ℂ)) * D *
          star (U : Matrix _ _ ℂ) := by simp only [Matrix.mul_assoc]
    _ = (U : Matrix _ _ ℂ) * (D * D) * star (U : Matrix _ _ ℂ) := by
          rw [hUU, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
    _ = (U : Matrix _ _ ℂ) *
          Matrix.diagonal (RCLike.ofReal ∘ hH.isHermitian.eigenvalues) *
          star (U : Matrix _ _ ℂ) := by
          congr 2
          rw [Matrix.diagonal_mul_diagonal]
          congr 1; funext i
          have hpos : 0 ≤ hH.isHermitian.eigenvalues i := (hH.eigenvalues_pos i).le
          change ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ) *
            ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ) =
            ((hH.isHermitian.eigenvalues i : ℝ) : ℂ)
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]
    _ = H := by
          have hspec := hH.isHermitian.spectral_theorem
          simpa [Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using hspec.symm

theorem posDef_det_eq_prod_eigenvalues {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    H.det = ∏ i : Fin N, ((hH.isHermitian.eigenvalues i : ℝ) : ℂ) := by
  set U := hH.isHermitian.eigenvectorUnitary
  have hspec : H = (U : Matrix _ _ ℂ) *
      (Matrix.diagonal (fun i => ((hH.isHermitian.eigenvalues i : ℝ) : ℂ)) *
        star (U : Matrix _ _ ℂ)) := by
    simpa [U, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hH.isHermitian.spectral_theorem
  have hdet := congrArg Matrix.det hspec
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hU1 : (U : Matrix (Fin N) (Fin N) ℂ).det * (star (U : Matrix (Fin N) (Fin N) ℂ)).det = 1 := by
    have hmul : (U : Matrix (Fin N) (Fin N) ℂ) * star (U : Matrix (Fin N) (Fin N) ℂ) = 1 := U.2.2
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  linear_combination hdet + (∏ i : Fin N, ((hH.isHermitian.eigenvalues i : ℝ) : ℂ)) * hU1

theorem posDef_det_re_pos {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    0 < H.det.re ∧ H.det.im = 0 := by
  rw [posDef_det_eq_prod_eigenvalues H hH, ← Complex.ofReal_prod, Complex.ofReal_re,
    Complex.ofReal_im]
  exact ⟨Finset.prod_pos fun i _ => hH.eigenvalues_pos i, rfl⟩

theorem isUnit_posDefSqrt_det {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    IsUnit (posDefSqrt H hH).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hdet : H.det = (posDefSqrt H hH).det * (posDefSqrt H hH).det := by
    conv_lhs => rw [← posDefSqrt_conjTranspose_mul_self H hH, (posDefSqrt_isHermitian H hH).eq]
    rw [Matrix.det_mul]
  rw [h0, mul_zero] at hdet
  have hpos := (posDef_det_re_pos H hH).1
  rw [hdet, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Invertible `ℂ`-linear equivalence `A = posDefSqrt H hH` on `DefiniteHermitianSpace N`. -/
def posDefSqrtEquiv {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    DefiniteHermitianSpace N ≃ₗ[ℂ] DefiniteHermitianSpace N :=
  LinearEquiv.ofLinearMap
    (Matrix.toEuclideanLin (posDefSqrt H hH))
    (Matrix.toEuclideanLin (posDefSqrt H hH)⁻¹)
    (by
      rw [← toEuclideanLin_mul_eq,
        Matrix.mul_nonsing_inv _ (isUnit_posDefSqrt_det H hH), toEuclideanLin_one_eq])
    (by
      rw [← toEuclideanLin_mul_eq,
        Matrix.nonsing_inv_mul _ (isUnit_posDefSqrt_det H hH), toEuclideanLin_one_eq])

lemma discreteTopology_map_linearEquiv {N : ℕ} (L : HermitianLattice N)
    (T : DefiniteHermitianSpace N ≃ₗ[ℝ] DefiniteHermitianSpace N) :
    DiscreteTopology (L.lat.map (T.toLinearMap.restrictScalars ℤ)) := by
  let eR : DefiniteHermitianSpace N ≃L[ℝ] DefiniteHermitianSpace N := T.toContinuousLinearEquiv
  have hmem : ∀ y : L.lat.map (T.toLinearMap.restrictScalars ℤ), eR.symm y.1 ∈ L.lat := by
    intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    have : eR.symm y.1 = x := by rw [← hxy]; exact T.symm_apply_apply x
    rwa [this]
  refine DiscreteTopology.of_continuous_injective
    (f := fun y : L.lat.map (T.toLinearMap.restrictScalars ℤ) => (⟨eR.symm y.1, hmem y⟩ : L.lat))
    (Continuous.subtype_mk (eR.symm.continuous.comp continuous_subtype_val) hmem)
    (fun _ _ h => Subtype.ext (eR.symm.injective (congrArg Subtype.val h)))

/-- **Concrete Positive-Definite Hermitian Lattice `L(d, H)`** inside `DefiniteHermitianSpace N`
associated to CM order `𝒪_d = ℤ[√-d]` (`d ≥ 1`) and positive-definite Hermitian Gram matrix
`H : Matrix (Fin N) (Fin N) ℂ`. -/
def hermitianLatticeOfPosDef {N : ℕ} (d : ℕ) (hd : 0 < d)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) : HermitianLattice N where
  lat := (stdCMLattice N d hd).lat.map
    (((posDefSqrtEquiv H hH).restrictScalars ℝ).toLinearMap.restrictScalars ℤ)
  disc := discreteTopology_map_linearEquiv (stdCMLattice N d hd)
    ((posDefSqrtEquiv H hH).restrictScalars ℝ)
  zlat := by
    have : DiscreteTopology ((stdCMLattice N d hd).lat.map
        (((posDefSqrtEquiv H hH).restrictScalars ℝ).toLinearMap.restrictScalars ℤ)) :=
      discreteTopology_map_linearEquiv (stdCMLattice N d hd)
        ((posDefSqrtEquiv H hH).restrictScalars ℝ)
    constructor
    have h1 : Submodule.span ℝ
        ((((stdCMLattice N d hd).lat.map
          (((posDefSqrtEquiv H hH).restrictScalars ℝ).toLinearMap.restrictScalars ℤ)) :
          Submodule ℤ _) : Set (DefiniteHermitianSpace N)) =
        (Submodule.span ℝ ((stdCMLattice N d hd).lat : Set (DefiniteHermitianSpace N))).map
          ((posDefSqrtEquiv H hH).restrictScalars ℝ).toLinearMap := by
      rw [Submodule.map_span]; rfl
    rw [h1, IsZLattice.span_top (K := ℝ) (L := (stdCMLattice N d hd).lat), Submodule.map_top,
      LinearEquiv.range]

/-- `hermitianLatticeOfPosDef d hd H hH` is stable under scalar multiplication by `CMOrder d`. -/
theorem cmOrder_smul_mem_hermitianLatticeOfPosDef {N : ℕ} (d : ℕ) (hd : 0 < d)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) {α : ℂ} (hα : α ∈ CMOrder d)
    {v : DefiniteHermitianSpace N} (hv : v ∈ (hermitianLatticeOfPosDef d hd H hH).lat) :
    α • v ∈ (hermitianLatticeOfPosDef d hd H hH).lat := by
  rcases hv with ⟨x, hx, rfl⟩
  refine ⟨α • x, cmOrder_smul_mem_stdCMLattice hd hα hx, ?_⟩
  exact map_smul (posDefSqrtEquiv H hH) α x

/-- The Hermitian Gram matrix of the canonical `𝒪_d`-basis `b_j = A e_j` of `L(d, H)` equals `H`. -/
theorem hermitianLatticeOfPosDef_gram_eq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef)
    (j k : Fin N) :
    inner ℂ (posDefSqrtEquiv H hH (EuclideanSpace.single j 1))
      (posDefSqrtEquiv H hH (EuclideanSpace.single k 1)) = H j k := by
  change inner ℂ (Matrix.toEuclideanLin (posDefSqrt H hH) (EuclideanSpace.single j 1))
    (Matrix.toEuclideanLin (posDefSqrt H hH) (EuclideanSpace.single k 1)) = H j k
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have hcol : ∀ a i, (Matrix.toEuclideanLin (posDefSqrt H hH) (EuclideanSpace.single a 1)) i =
      posDefSqrt H hH i a := by
    intro a i
    simp [Matrix.toLpLin_apply]
  have hsum : ∑ i : Fin N,
      (Matrix.toEuclideanLin (posDefSqrt H hH) (EuclideanSpace.single k 1)) i *
        star ((Matrix.toEuclideanLin (posDefSqrt H hH) (EuclideanSpace.single j 1)) i) =
      ((posDefSqrt H hH)ᴴ * posDefSqrt H hH) j k := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol j i, hcol k i, Matrix.conjTranspose_apply, mul_comm]
  exact hsum.trans (congrFun (congrFun (posDefSqrt_conjTranspose_mul_self H hH) j) k)

/-- Real determinant of a real-linear map induced by `posDefSqrt H hH` equals `H.det.re`. -/
theorem det_restrictScalars_posDefSqrt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    LinearMap.det ((Matrix.toEuclideanLin (posDefSqrt H hH)).restrictScalars ℝ) = H.det.re := by
  set U := hH.isHermitian.eigenvectorUnitary
  set r : Fin N → ℝ := fun i => Real.sqrt (hH.isHermitian.eigenvalues i)
  set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))
  have hfac : (Matrix.toEuclideanLin (posDefSqrt H hH)).restrictScalars ℝ =
      ((Matrix.toEuclideanLin (U : Matrix (Fin N) (Fin N) ℂ)).restrictScalars ℝ).comp
        (((Matrix.toEuclideanLin D).restrictScalars ℝ).comp
          ((Matrix.toEuclideanLin (star (U : Matrix (Fin N) (Fin N) ℂ))).restrictScalars ℝ)) := by
    ext v i
    change (Matrix.toEuclideanLin ((U : Matrix _ _ ℂ) * D * star (U : Matrix _ _ ℂ)) v) i =
      (Matrix.toEuclideanLin (U : Matrix _ _ ℂ)
        (Matrix.toEuclideanLin D (Matrix.toEuclideanLin (star (U : Matrix _ _ ℂ)) v))) i
    rw [toEuclideanLin_mul_eq, toEuclideanLin_mul_eq]
    rfl
  have hUinv : ((Matrix.toEuclideanLin (U : Matrix (Fin N) (Fin N) ℂ)).restrictScalars ℝ).comp
      ((Matrix.toEuclideanLin (star (U : Matrix (Fin N) (Fin N) ℂ))).restrictScalars ℝ) =
      LinearMap.id := by
    ext v i
    change (Matrix.toEuclideanLin (U : Matrix (Fin N) (Fin N) ℂ)
      (Matrix.toEuclideanLin (star (U : Matrix (Fin N) (Fin N) ℂ)) v)) i = v i
    rw [← LinearMap.comp_apply, ← toEuclideanLin_mul_eq, U.2.2,
      toEuclideanLin_one_eq, LinearMap.id_apply]
  have hdetU : LinearMap.det ((Matrix.toEuclideanLin (U : Matrix (Fin N) (Fin N) ℂ)).restrictScalars ℝ) *
      LinearMap.det ((Matrix.toEuclideanLin (star (U : Matrix (Fin N) (Fin N) ℂ))).restrictScalars ℝ) = 1 := by
    rw [← LinearMap.det_comp, hUinv, LinearMap.det_id]
  rw [hfac, LinearMap.det_comp, LinearMap.det_comp]
  have hdet_eq : LinearMap.det ((Matrix.toEuclideanLin (U : Matrix (Fin N) (Fin N) ℂ)).restrictScalars ℝ) *
      (LinearMap.det ((Matrix.toEuclideanLin D).restrictScalars ℝ) *
        LinearMap.det ((Matrix.toEuclideanLin (star (U : Matrix (Fin N) (Fin N) ℂ))).restrictScalars ℝ)) =
      LinearMap.det ((Matrix.toEuclideanLin D).restrictScalars ℝ) := by
    linear_combination LinearMap.det ((Matrix.toEuclideanLin D).restrictScalars ℝ) * hdetU
  rw [hdet_eq]
  let b := stdCMRealBasis N 1 Nat.one_pos
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b ((Matrix.toEuclideanLin D).restrictScalars ℝ) =
      Matrix.diagonal (fun k : Fin (2 * N) => r ((hermCoordEquiv N).symm k).1) := by
    ext k l
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    have hact : ((Matrix.toEuclideanLin D).restrictScalars ℝ) (b l) =
        r ((hermCoordEquiv N).symm l).1 • b l := by
      have hbl : b l = stdCMBasisVec N 1 l := Basis.mk_apply _ _ l
      rw [hbl]
      ext i
      change (Matrix.toEuclideanLin D (stdCMBasisVec N 1 l)) i =
        (r ((hermCoordEquiv N).symm l).1 • stdCMBasisVec N 1 l) i
      simp only [D, Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_diagonal, stdCMBasisVec,
        WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul]
      by_cases hi : i = ((hermCoordEquiv N).symm l).1
      · subst hi; simp
      · simp [hi]
    rw [hact, map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply]
    by_cases hkl : l = k
    · subst hkl; simp
    · simp [hkl, Ne.symm hkl]
  rw [hmat, Matrix.det_diagonal, ← (hermCoordEquiv N).prod_comp, Fintype.prod_prod_type]
  have hprod : ∏ i : Fin N, ∏ _j : Fin 2, r ((hermCoordEquiv N).symm (hermCoordEquiv N (i, _j))).1 =
      ∏ i : Fin N, hH.isHermitian.eigenvalues i := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_two]
    simp only [Equiv.symm_apply_apply, r]
    exact Real.mul_self_sqrt (hH.eigenvalues_pos i).le
  rw [hprod, posDef_det_eq_prod_eigenvalues H hH, ← Complex.ofReal_prod, Complex.ofReal_re]

/-- Scaling of `ArakelovCovolume.covol` under any real-linear equivalence `T : E ≃ₗ[ℝ] E`. -/
theorem covol_map_linearEquiv {N : ℕ} (L : HermitianLattice N)
    (T : DefiniteHermitianSpace N ≃ₗ[ℝ] DefiniteHermitianSpace N) :
    ArakelovCovolume.covol (L.lat.map (T.toLinearMap.restrictScalars ℤ)) =
      |LinearMap.det T.toLinearMap| * ArakelovCovolume.covol L.lat := by
  let L' : Submodule ℤ (DefiniteHermitianSpace N) := L.lat.map (T.toLinearMap.restrictScalars ℤ)
  have : DiscreteTopology L' := discreteTopology_map_linearEquiv L T
  let e := realEquiv N
  let eL0 : DefiniteHermitianSpace N ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * N)) := e.toLinearEquiv
  let T_R : EuclideanSpace ℝ (Fin (2 * N)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * N)) :=
    eL0.symm.trans (T.trans eL0)
  have hdetT : LinearMap.det T_R.toLinearMap = LinearMap.det T.toLinearMap := by
    change LinearMap.det (eL0.toLinearMap.comp (T.toLinearMap.comp eL0.symm.toLinearMap)) = _
    rw [LinearMap.det_conj]
  let b : Basis (Fin (2 * N)) ℤ L.lat := L.zBasis
  let eL : L.lat ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨T x.1, x.1, x.2, rfl⟩
      invFun := fun y => ⟨T.symm y.1, by
        rcases y.2 with ⟨x, hx, hxy⟩
        have : T.symm y.1 = x := by rw [← hxy]; exact T.symm_apply_apply x
        rwa [this]⟩
      map_add' := fun x y => Subtype.ext (map_add T x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul T c x.1)
      left_inv := fun x => Subtype.ext (T.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (T.apply_symm_apply y.1) }
  let b' : Basis (Fin (2 * N)) ℤ L' := b.map eL
  rw [ArakelovCovolume.covol_eq_sqrt_det_gram L' b',
    ArakelovCovolume.covol_eq_sqrt_det_gram L.lat b]
  let bE : Basis (Fin (2 * N)) ℝ (EuclideanSpace ℝ (Fin (2 * N))) :=
    (EuclideanSpace.basisFun (Fin (2 * N)) ℝ).toBasis
  let B : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ :=
    Matrix.of fun i j => (e (b i : DefiniteHermitianSpace N)) j
  let M : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ := LinearMap.toMatrix bE bE T_R.toLinearMap
  have hrep_val : ∀ (x : EuclideanSpace ℝ (Fin (2 * N))) (k : Fin (2 * N)),
      bE.repr x k = x.ofLp k := by
    intro x k
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  have hgram : Matrix.gram ℝ (fun i => (b i : DefiniteHermitianSpace N)) = B * Bᵀ := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply]
    rw [← e.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  have hcoord' : ∀ i j, (e (b' i : DefiniteHermitianSpace N)).ofLp j = (B * Mᵀ) i j := by
    intro i j
    have h1 : e (b' i : DefiniteHermitianSpace N) = T_R (e (b i : DefiniteHermitianSpace N)) := by
      change e (T (b i : DefiniteHermitianSpace N)) = e (T (e.symm (e (b i : DefiniteHermitianSpace N))))
      rw [e.symm_apply_apply]
    rw [h1]
    have hrepr := LinearMap.toMatrix_mulVec_repr bE bE T_R.toLinearMap (e (b i : DefiniteHermitianSpace N))
    have hrep_j := congrFun hrepr j
    simp only [Matrix.mulVec, dotProduct] at hrep_j
    rw [hrep_val] at hrep_j
    change (T_R.toLinearMap (e (b i : DefiniteHermitianSpace N))).ofLp j = (B * Mᵀ) i j
    rw [← hrep_j, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => by
      rw [hrep_val]
      simp [B, M, Matrix.transpose_apply, mul_comm]
  have hgram' : Matrix.gram ℝ (fun i => (b' i : DefiniteHermitianSpace N)) =
      (B * Mᵀ) * (B * Mᵀ)ᵀ := by
    ext i j
    rw [Matrix.gram_apply, ← e.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, star_trivial, hcoord' j k, hcoord' i k, Matrix.transpose_apply, mul_comm]
  rw [hgram', hgram]
  have hlhs : Real.sqrt ((B * Mᵀ) * (B * Mᵀ)ᵀ).det = |B.det * M.det| := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs, Matrix.det_mul,
      Matrix.det_transpose]
  have hrhs : Real.sqrt (B * Bᵀ).det = |B.det| := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  rw [hlhs, hrhs, abs_mul, mul_comm |B.det|, LinearMap.det_toMatrix bE, hdetT]

/-- **Exact Hermitian Lattice Covolume Formula (`covolume_hermitian_ofPosDef`)**:
`covol(L(d, H)) = (√d)^N * det(H).re`. -/
theorem covolume_hermitian_ofPosDef {N : ℕ} (d : ℕ) (hd : 0 < d)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) :
    ArakelovCovolume.covol (hermitianLatticeOfPosDef d hd H hH).lat =
      (Real.sqrt d) ^ N * H.det.re := by
  have hcov := covol_map_linearEquiv (stdCMLattice N d hd) ((posDefSqrtEquiv H hH).restrictScalars ℝ)
  have hdet : LinearMap.det (((posDefSqrtEquiv H hH).restrictScalars ℝ).toLinearMap) = H.det.re :=
    det_restrictScalars_posDefSqrt H hH
  have hpos : 0 < H.det.re := (posDef_det_re_pos H hH).1
  rw [hermitianLatticeOfPosDef, hcov, hdet, abs_of_pos hpos, covol_stdCMLattice N d hd, mul_comm]

/-- Unitary action of `g ∈ U(N)` on `DefiniteHermitianSpace N` as a `ℂ`-linear isometry equivalence. -/
def unitaryAction {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ) :
    DefiniteHermitianSpace N ≃ₗᵢ[ℂ] DefiniteHermitianSpace N where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ))
    (Matrix.toEuclideanLin (star (g : Matrix (Fin N) (Fin N) ℂ)))
    (by rw [← toEuclideanLin_mul_eq, g.2.2, toEuclideanLin_one_eq])
    (by rw [← toEuclideanLin_mul_eq, g.2.1, toEuclideanLin_one_eq])
  norm_map' v := by
    change ‖Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v‖ = ‖v‖
    have hsq : ‖Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v‖ ^ 2 = ‖v‖ ^ 2 := by
      have h1 : inner ℂ (Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v)
          (Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v) = inner ℂ v v := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
        change ((g : Matrix (Fin N) (Fin N) ℂ).mulVec v.ofLp) ⬝ᵥ
            star ((g : Matrix (Fin N) (Fin N) ℂ).mulVec v.ofLp) =
          v.ofLp ⬝ᵥ star v.ofLp
        rw [dotProduct_comm, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
        have hstar : star (g : Matrix (Fin N) (Fin N) ℂ) = (g : Matrix (Fin N) (Fin N) ℂ)ᴴ := rfl
        rw [← hstar, g.2.1, Matrix.vecMul_one, dotProduct_comm]
      have hre := congrArg Complex.re h1
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
      have hre' : ((‖Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v‖ ^ 2 : ℝ) : ℂ).re =
          ((‖v‖ ^ 2 : ℝ) : ℂ).re := by
        simpa [Complex.ofReal_pow] using hre
      simpa only [Complex.ofReal_re] using hre'
    nlinarith [norm_nonneg (Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v),
      norm_nonneg v]

theorem unitaryAction_apply {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ)
    (v : DefiniteHermitianSpace N) :
    unitaryAction g v = Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ) v := rfl

theorem unitaryAction_one {N : ℕ} (v : DefiniteHermitianSpace N) :
    unitaryAction (1 : Matrix.unitaryGroup (Fin N) ℂ) v = v := by
  rw [unitaryAction_apply]
  change Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) v = v
  rw [toEuclideanLin_one_eq, LinearMap.id_apply]

theorem unitaryAction_mul {N : ℕ} (g h : Matrix.unitaryGroup (Fin N) ℂ)
    (v : DefiniteHermitianSpace N) :
    unitaryAction (g * h) v = unitaryAction g (unitaryAction h v) := by
  rw [unitaryAction_apply, unitaryAction_apply, unitaryAction_apply]
  change Matrix.toEuclideanLin ((g : Matrix (Fin N) (Fin N) ℂ) * (h : Matrix (Fin N) (Fin N) ℂ)) v =
    Matrix.toEuclideanLin (g : Matrix (Fin N) (Fin N) ℂ)
      (Matrix.toEuclideanLin (h : Matrix (Fin N) (Fin N) ℂ) v)
  rw [toEuclideanLin_mul_eq, LinearMap.comp_apply]

theorem unitaryAction_inv {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ)
    (v : DefiniteHermitianSpace N) :
    unitaryAction g⁻¹ (unitaryAction g v) = v := by
  rw [← unitaryAction_mul, inv_mul_cancel, unitaryAction_one]

theorem unitaryAction_injective {N : ℕ} :
    Function.Injective (unitaryAction (N := N)) := by
  intro g₁ g₂ h
  apply Subtype.ext
  ext i j
  have hv := congrArg (fun f : DefiniteHermitianSpace N ≃ₗᵢ[ℂ] DefiniteHermitianSpace N =>
    (f (EuclideanSpace.single j 1)) i) h
  simpa only [unitaryAction_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec,
    dotProduct, PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] using hv

/-- **Definite Unitary Automorphism Group `DefiniteUnitaryGroup L = { g ∈ U(N) | g(L) = L }`**. -/
def DefiniteUnitaryGroup {N : ℕ} (L : HermitianLattice N) :
    Subgroup (Matrix.unitaryGroup (Fin N) ℂ) where
  carrier := { g | ∀ v, v ∈ L.lat ↔ unitaryAction g v ∈ L.lat }
  one_mem' := fun v => by simp [unitaryAction_one]
  mul_mem' := fun {g h} hg hh v => by
    rw [unitaryAction_mul, ← hg (unitaryAction h v), ← hh v]
  inv_mem' := fun {g} hg v => by
    have h1 := hg (unitaryAction g⁻¹ v)
    rw [← unitaryAction_mul, mul_inv_cancel, unitaryAction_one] at h1
    exact h1.symm

/-- **Unconditional Finiteness of `DefiniteUnitaryGroup L` (`finite_definiteUnitaryGroup`)**:
For EVERY positive-definite Hermitian lattice `L ⊂ ℂ^N`, its unitary automorphism group
`{ g ∈ U(N) | g(L) = L }` is FINITE! -/
theorem finite_definiteUnitaryGroup {N : ℕ} (L : HermitianLattice N) :
    Finite (DefiniteUnitaryGroup L) := by
  let b : Basis (Fin (2 * N)) ℤ L.lat := L.zBasis
  let R : ℝ := ∑ i : Fin (2 * N), ‖(b i : DefiniteHermitianSpace N)‖
  let S : Set (DefiniteHermitianSpace N) :=
    (L.lat : Set (DefiniteHermitianSpace N)) ∩ Metric.closedBall 0 R
  have hS_fin : S.Finite := by
    have hR_fin : ((L.realLat : Set (EuclideanSpace ℝ (Fin (2 * N)))) ∩
        Metric.closedBall 0 R).Finite :=
      Stage10GeometryOfNumbers.lattice_inter_closedBall_finite L.realLat R
    have hpre : S = (realEquiv N) ⁻¹'
        ((L.realLat : Set (EuclideanSpace ℝ (Fin (2 * N)))) ∩ Metric.closedBall 0 R) := by
      ext v
      simp only [S, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map, SetLike.mem_coe]
      constructor
      · rintro ⟨hv, hnorm⟩
        exact ⟨⟨v, hv, rfl⟩, hnorm⟩
      · rintro ⟨⟨w, hw, hweq⟩, hnorm⟩
        have : w = v := (realEquiv N).injective hweq
        exact ⟨this ▸ hw, hnorm⟩
    rw [hpre]
    exact hR_fin.preimage (realEquiv N).injective.injOn
  have : Finite S := hS_fin.to_subtype
  let φ : DefiniteUnitaryGroup L → (Fin (2 * N) → S) := fun g i =>
    ⟨unitaryAction g.1 (b i : DefiniteHermitianSpace N),
      (g.2 (b i : DefiniteHermitianSpace N)).mp (b i).2, by
        rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
        exact Finset.single_le_sum (fun j _ => norm_nonneg (b j : DefiniteHermitianSpace N))
          (Finset.mem_univ i)⟩
  have hφ_inj : Function.Injective φ := by
    intro g₁ g₂ h
    apply Subtype.ext
    apply unitaryAction_injective
    apply LinearIsometryEquiv.ext
    intro v
    have hspan : Submodule.span ℝ (Set.range fun i : Fin (2 * N) => (b i : DefiniteHermitianSpace N)) = ⊤ := by
      have hZ : Submodule.span ℤ (Set.range fun i : Fin (2 * N) => (b i : DefiniteHermitianSpace N)) = L.lat := by
        have : Set.range (fun i : Fin (2 * N) => (b i : DefiniteHermitianSpace N)) =
            L.lat.subtype '' Set.range b := Set.range_comp _ _
        rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
      rw [← Submodule.span_span_of_tower ℤ ℝ, hZ, IsZLattice.span_top (K := ℝ) (L := L.lat)]
    have hv : v ∈ Submodule.span ℝ (Set.range fun i : Fin (2 * N) => (b i : DefiniteHermitianSpace N)) := by
      rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact congrArg Subtype.val (congrFun h i)
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx =>
      rw [← Complex.coe_smul, map_smul, map_smul, hx]
  exact Finite.of_injective φ hφ_inj

instance instFiniteDefiniteUnitaryGroup {N : ℕ} (L : HermitianLattice N) :
    Finite (DefiniteUnitaryGroup L) :=
  finite_definiteUnitaryGroup L

theorem card_definiteUnitaryGroup_pos {N : ℕ} (L : HermitianLattice N) :
    0 < Nat.card (DefiniteUnitaryGroup L) :=
  Nat.card_pos

end HermitianSpacesAndLattices

/-! ## Section 2: Concrete Finite-Dimensional Automorphic Form Spaces, Theta-Lift Kernels & Schur's Test -/

section AutomorphicSpacesAndThetaKernels

/-- A finite genus `{L_1, ..., L_h}` of positive-definite Hermitian lattices of rank `N`. -/
structure HermitianGenus (N : ℕ) where
  idx : Type
  [finIdx : Fintype idx]
  [decIdx : DecidableEq idx]
  lat : idx → HermitianLattice N

attribute [instance] HermitianGenus.finIdx HermitianGenus.decIdx

/-- Canonical Petersson weight `w_i = 1 / |Aut(L_i)| > 0` on a finite Hermitian genus. -/
def peterssonWeight {N : ℕ} (G : HermitianGenus N) (i : G.idx) : ℝ :=
  ((Nat.card (DefiniteUnitaryGroup (G.lat i)) : ℕ) : ℝ)⁻¹

theorem peterssonWeight_pos {N : ℕ} (G : HermitianGenus N) (i : G.idx) :
    0 < peterssonWeight G i :=
  inv_pos.mpr (Nat.cast_pos.mpr (card_definiteUnitaryGroup_pos (G.lat i)))

/-- Total Siegel–Tamagawa genus mass `∑_i 1 / |Aut(L_i)|`. -/
def genusMass {N : ℕ} (G : HermitianGenus N) : ℝ :=
  ∑ i : G.idx, peterssonWeight G i

theorem genusMass_pos {N : ℕ} (G : HermitianGenus N) [Nonempty G.idx] :
    0 < genusMass G :=
  Finset.sum_pos (fun i _ => peterssonWeight_pos G i) Finset.univ_nonempty

/-- Concrete finite-dimensional automorphic form Hilbert space `𝒜(U(V))` on a finite Hermitian
genus `G`, carrying the Petersson-weighted inner product
`⟨φ, ψ⟩ = ∑_i (1 / |Aut(L_i)|) * star (φ i) * ψ i`. -/
@[ext]
structure DefiniteAutomorphicSpace {N : ℕ} (G : HermitianGenus N) where
  toFun : G.idx → ℂ

namespace DefiniteAutomorphicSpace

variable {N : ℕ} {G : HermitianGenus N}

instance : Zero (DefiniteAutomorphicSpace G) := ⟨⟨0⟩⟩
instance : Add (DefiniteAutomorphicSpace G) := ⟨fun φ ψ => ⟨φ.toFun + ψ.toFun⟩⟩
instance : Neg (DefiniteAutomorphicSpace G) := ⟨fun φ => ⟨-φ.toFun⟩⟩
instance : Sub (DefiniteAutomorphicSpace G) := ⟨fun φ ψ => ⟨φ.toFun - ψ.toFun⟩⟩
instance : SMul ℂ (DefiniteAutomorphicSpace G) := ⟨fun c φ => ⟨c • φ.toFun⟩⟩

@[simp] lemma zero_toFun : (0 : DefiniteAutomorphicSpace G).toFun = 0 := rfl
@[simp] lemma add_toFun (φ ψ : DefiniteAutomorphicSpace G) : (φ + ψ).toFun = φ.toFun + ψ.toFun := rfl
@[simp] lemma neg_toFun (φ : DefiniteAutomorphicSpace G) : (-φ).toFun = -φ.toFun := rfl
@[simp] lemma sub_toFun (φ ψ : DefiniteAutomorphicSpace G) : (φ - ψ).toFun = φ.toFun - ψ.toFun := rfl
@[simp] lemma smul_toFun (c : ℂ) (φ : DefiniteAutomorphicSpace G) : (c • φ).toFun = c • φ.toFun := rfl

instance : AddCommGroup (DefiniteAutomorphicSpace G) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]

instance : Module ℂ (DefiniteAutomorphicSpace G) where
  one_smul a := by ext i; simp
  mul_smul c d a := by ext i; simp [mul_assoc]
  smul_zero c := by ext i; simp
  smul_add c a b := by ext i; simp [mul_add]
  add_smul c d a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- Diagonal Petersson weight isometry `φ ↦ (√w_i · φ_i)` into `EuclideanSpace ℂ G.idx`. -/
def weightedEquiv (G : HermitianGenus N) :
    DefiniteAutomorphicSpace G ≃ₗ[ℂ] EuclideanSpace ℂ G.idx where
  toFun φ := WithLp.toLp 2 fun i => ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) * φ.toFun i
  invFun v := ⟨fun i => ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ)⁻¹ * v i⟩
  map_add' φ ψ := by ext i; simp [mul_add]
  map_smul' c φ := by ext i; simp; ring
  left_inv φ := by
    ext i
    have hne : ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (peterssonWeight_pos G i)).ne'
    simp [inv_mul_cancel_left₀ hne]
  right_inv v := by
    ext i
    have hne : ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (peterssonWeight_pos G i)).ne'
    simp [mul_inv_cancel_left₀ hne]

/-- Petersson inner-product core on `DefiniteAutomorphicSpace G`. -/
@[instance_reducible]
def innerCore (G : HermitianGenus N) :
    InnerProductSpace.Core ℂ (DefiniteAutomorphicSpace G) where
  inner φ ψ := inner ℂ (weightedEquiv G φ) (weightedEquiv G ψ)
  conj_inner_symm φ ψ := inner_conj_symm (weightedEquiv G φ) (weightedEquiv G ψ)
  re_inner_nonneg φ := inner_self_nonneg
  definite φ hφ := (weightedEquiv G).injective (by
    rw [map_zero]
    exact inner_self_eq_zero.mp hφ)
  add_left φ₁ φ₂ ψ := by rw [map_add, inner_add_left]
  smul_left φ ψ c := by rw [map_smul, inner_smul_left]

instance : NormedAddCommGroup (DefiniteAutomorphicSpace G) :=
  (innerCore G).toNormedAddCommGroup

instance : InnerProductSpace ℂ (DefiniteAutomorphicSpace G) :=
  InnerProductSpace.ofCore (innerCore G).toCore

instance : FiniteDimensional ℂ (DefiniteAutomorphicSpace G) :=
  (weightedEquiv G).symm.finiteDimensional

theorem finrank_eq (G : HermitianGenus N) :
    Module.finrank ℂ (DefiniteAutomorphicSpace G) = Fintype.card G.idx := by
  rw [(weightedEquiv G).finrank_eq, finrank_euclideanSpace]

/-- Explicit Petersson inner-product formula on `DefiniteAutomorphicSpace G`. -/
theorem inner_eq (φ ψ : DefiniteAutomorphicSpace G) :
    inner ℂ φ ψ = ∑ i : G.idx, (peterssonWeight G i : ℂ) * star (φ.toFun i) * ψ.toFun i := by
  change inner ℂ (weightedEquiv G φ) (weightedEquiv G ψ) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [weightedEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Pi.star_apply, star_mul', RCLike.star_def, Complex.conj_ofReal]
  have hsq : ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) *
      ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) = (peterssonWeight G i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (peterssonWeight_pos G i).le]
  calc ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) * ψ.toFun i *
          (((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) * starRingEnd ℂ (φ.toFun i))
      = (((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ) *
          ((Real.sqrt (peterssonWeight G i) : ℝ) : ℂ)) * star (φ.toFun i) * ψ.toFun i := by
        rw [Complex.star_def]; ring
    _ = (peterssonWeight G i : ℂ) * star (φ.toFun i) * ψ.toFun i := by rw [hsq]

/-- Exact agreement with `RallisSeesaw.wip`. -/
theorem inner_eq_wip (φ ψ : DefiniteAutomorphicSpace G) :
    inner ℂ φ ψ = RallisSeesaw.wip (fun i => (peterssonWeight G i : ℂ)) φ.toFun ψ.toFun :=
  inner_eq φ ψ

/-- Exact Petersson norm-square formula `‖φ‖² = ∑_i (1 / |Aut(L_i)|) * ‖φ(i)‖²`. -/
theorem norm_sq_eq (φ : DefiniteAutomorphicSpace G) :
    ‖φ‖ ^ 2 = ∑ i : G.idx, peterssonWeight G i * ‖φ.toFun i‖ ^ 2 := by
  have h := congrArg Complex.re (inner_eq φ φ)
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    Complex.ofReal_re] at h
  rw [h, ← RallisSeesaw.wip, RallisSeesaw.wip_self_eq_sum_normSq, Complex.ofReal_re]

end DefiniteAutomorphicSpace

/-- Frobenius norm squared `Tr(Tᴴ * T) = ∑_{i, j} ‖T i j‖²` of a complex matrix. -/
def frobNormSq {N₁ N₂ : ℕ} (T : Matrix (Fin N₂) (Fin N₁) ℂ) : ℝ :=
  ∑ i : Fin N₂, ∑ j : Fin N₁, ‖T i j‖ ^ 2

theorem frobNormSq_nonneg {N₁ N₂ : ℕ} (T : Matrix (Fin N₂) (Fin N₁) ℂ) :
    0 ≤ frobNormSq T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem frobNormSq_eq_trace {N₁ N₂ : ℕ} (T : Matrix (Fin N₂) (Fin N₁) ℂ) :
    frobNormSq T = (Tᴴ * T).trace.re := by
  unfold frobNormSq
  rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Operator-norm bound `‖T v‖ ≤ √(frobNormSq T) * ‖v‖` via Cauchy–Schwarz. -/
theorem norm_toEuclideanLin_le_frob {N₁ N₂ : ℕ} (T : Matrix (Fin N₂) (Fin N₁) ℂ)
    (v : DefiniteHermitianSpace N₁) :
    ‖Matrix.toEuclideanLin T v‖ ≤ Real.sqrt (frobNormSq T) * ‖v‖ := by
  have hsq : ‖Matrix.toEuclideanLin T v‖ ^ 2 ≤ frobNormSq T * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, frobNormSq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
    have htri : ‖∑ j : Fin N₁, T i j * v j‖ ≤ ∑ j : Fin N₁, ‖T i j‖ * ‖v j‖ := by
      calc ‖∑ j : Fin N₁, T i j * v j‖
          ≤ ∑ j : Fin N₁, ‖T i j * v j‖ := norm_sum_le _ _
        _ = ∑ j : Fin N₁, ‖T i j‖ * ‖v j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
    have hcs : (∑ j : Fin N₁, ‖T i j‖ * ‖v j‖) ^ 2 ≤
        (∑ j : Fin N₁, ‖T i j‖ ^ 2) * (∑ j : Fin N₁, ‖v j‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖T i j‖) (fun j => ‖v j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans hcs
  have hrhs : 0 ≤ Real.sqrt (frobNormSq T) * ‖v‖ := by positivity
  have hsq' : ‖Matrix.toEuclideanLin T v‖ ^ 2 ≤ (Real.sqrt (frobNormSq T) * ‖v‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (frobNormSq_nonneg T)]
    exact hsq
  nlinarith [norm_nonneg (Matrix.toEuclideanLin T v)]

/-- Concrete `ℤ`-module of lattice-preserving `ℂ`-linear homomorphisms `L → M` inside
`Matrix (Fin N₂) (Fin N₁) ℂ`. -/
def LatticeHom {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂) :
    Submodule ℤ (Matrix (Fin N₂) (Fin N₁) ℂ) where
  carrier := { T | ∀ v ∈ L.lat, Matrix.toEuclideanLin T v ∈ M.lat }
  zero_mem' := fun v _ => by simp
  add_mem' := fun {S T} hS hT v hv => by
    rw [map_add, LinearMap.add_apply]
    exact M.lat.add_mem (hS v hv) (hT v hv)
  smul_mem' := fun c T hT v hv => by
    have hsm : Matrix.toEuclideanLin (c • T) v = c • Matrix.toEuclideanLin T v := by
      ext i
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, zsmul_eq_mul]
    rw [hsm]
    exact M.lat.smul_mem c (hT v hv)

/-- **Unconditional Finiteness of Bounded Lattice Homomorphisms (`finite_latticeHom_bounded`)**:
For any two positive-definite Hermitian lattices `L, M` and any bound `R : ℝ`, the set
`{ T ∈ Hom(L, M) | Tr(Tᴴ T) ≤ R }` is FINITE! -/
theorem finite_latticeHom_bounded {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂)
    (R : ℝ) :
    { T : Matrix (Fin N₂) (Fin N₁) ℂ | T ∈ LatticeHom L M ∧ frobNormSq T ≤ R }.Finite := by
  let b : Basis (Fin (2 * N₁)) ℤ L.lat := L.zBasis
  let B_L : ℝ := ∑ i : Fin (2 * N₁), ‖(b i : DefiniteHermitianSpace N₁)‖
  let R_M : ℝ := Real.sqrt (max R 0) * B_L
  let S : Set (DefiniteHermitianSpace N₂) :=
    (M.lat : Set (DefiniteHermitianSpace N₂)) ∩ Metric.closedBall 0 R_M
  have hS_fin : S.Finite := by
    have hR_fin : ((M.realLat : Set (EuclideanSpace ℝ (Fin (2 * N₂)))) ∩
        Metric.closedBall 0 R_M).Finite :=
      Stage10GeometryOfNumbers.lattice_inter_closedBall_finite M.realLat R_M
    have hpre : S = (realEquiv N₂) ⁻¹'
        ((M.realLat : Set (EuclideanSpace ℝ (Fin (2 * N₂)))) ∩ Metric.closedBall 0 R_M) := by
      ext v
      simp only [S, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map, SetLike.mem_coe]
      constructor
      · rintro ⟨hv, hnorm⟩; exact ⟨⟨v, hv, rfl⟩, hnorm⟩
      · rintro ⟨⟨w, hw, hweq⟩, hnorm⟩
        exact ⟨(realEquiv N₂).injective hweq ▸ hw, hnorm⟩
    rw [hpre]
    exact hR_fin.preimage (realEquiv N₂).injective.injOn
  have : Finite S := hS_fin.to_subtype
  let Aset := { T : Matrix (Fin N₂) (Fin N₁) ℂ | T ∈ LatticeHom L M ∧ frobNormSq T ≤ R }
  let φ : Aset → (Fin (2 * N₁) → S) := fun T i =>
    ⟨Matrix.toEuclideanLin T.1 (b i : DefiniteHermitianSpace N₁),
      T.2.1 (b i : DefiniteHermitianSpace N₁) (b i).2, by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖Matrix.toEuclideanLin T.1 (b i : DefiniteHermitianSpace N₁)‖
            ≤ Real.sqrt (frobNormSq T.1) * ‖(b i : DefiniteHermitianSpace N₁)‖ :=
              norm_toEuclideanLin_le_frob T.1 _
          _ ≤ Real.sqrt (max R 0) * B_L :=
              mul_le_mul (Real.sqrt_le_sqrt (T.2.2.trans (le_max_left R 0)))
                (Finset.single_le_sum (fun j _ => norm_nonneg (b j : DefiniteHermitianSpace N₁))
                  (Finset.mem_univ i))
                (norm_nonneg _) (Real.sqrt_nonneg _)⟩
  have hφ_inj : Function.Injective φ := by
    intro T₁ T₂ h
    apply Subtype.ext
    have hlin : Matrix.toEuclideanLin T₁.1 = Matrix.toEuclideanLin T₂.1 := by
      ext v i
      have hspan : Submodule.span ℝ (Set.range fun k : Fin (2 * N₁) => (b k : DefiniteHermitianSpace N₁)) = ⊤ := by
        have hZ : Submodule.span ℤ (Set.range fun k : Fin (2 * N₁) => (b k : DefiniteHermitianSpace N₁)) = L.lat := by
          have : Set.range (fun k : Fin (2 * N₁) => (b k : DefiniteHermitianSpace N₁)) =
              L.lat.subtype '' Set.range b := Set.range_comp _ _
          rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
        rw [← Submodule.span_span_of_tower ℤ ℝ, hZ, IsZLattice.span_top (K := ℝ) (L := L.lat)]
      have hv : v ∈ Submodule.span ℝ (Set.range fun k : Fin (2 * N₁) => (b k : DefiniteHermitianSpace N₁)) := by
        rw [hspan]; trivial
      have hveq : Matrix.toEuclideanLin T₁.1 v = Matrix.toEuclideanLin T₂.1 v := by
        induction hv using Submodule.span_induction with
        | mem x hx =>
          rcases hx with ⟨k, rfl⟩
          exact congrArg Subtype.val (congrFun h k)
        | zero => simp
        | add x y _ _ hx hy => simp [hx, hy]
        | smul c x _ hx => rw [← Complex.coe_smul, map_smul, map_smul, hx]
      exact congrArg (fun w : DefiniteHermitianSpace N₂ => w i) hveq
    ext i j
    have hv := congrArg (fun f : DefiniteHermitianSpace N₁ →ₗ[ℂ] DefiniteHermitianSpace N₂ =>
      (f (EuclideanSpace.single j 1)) i) hlin
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
      PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] using hv
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hφ_inj)

/-- Representation set `{ T ∈ Hom(L, M) | Tᴴ * T = Q }` for a target Hermitian matrix `Q`. -/
def RepSet {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂)
    (Q : Matrix (Fin N₁) (Fin N₁) ℂ) : Set (Matrix (Fin N₂) (Fin N₁) ℂ) :=
  { T | T ∈ LatticeHom L M ∧ Tᴴ * T = Q }

/-- **Unconditional Finiteness of Hermitian Representation Sets (`finite_repSet`)**. -/
theorem finite_repSet {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂)
    (Q : Matrix (Fin N₁) (Fin N₁) ℂ) :
    (RepSet L M Q).Finite := by
  refine (finite_latticeHom_bounded L M Q.trace.re).subset ?_
  rintro T ⟨hT, hQ⟩
  exact ⟨hT, by rw [frobNormSq_eq_trace, hQ]⟩

/-- Concrete algebraic theta representation count `r(L, M; Q) = #{ T ∈ Hom(L, M) | Tᴴ * T = Q }`. -/
def repCount {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂)
    (Q : Matrix (Fin N₁) (Fin N₁) ℂ) : ℕ :=
  Nat.card (RepSet L M Q)

/-- Concrete algebraic theta-lift representation kernel `K_Q(L_i, M_j) = r(L_i, M_j; Q)`. -/
def thetaRepKernel {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (Q : Matrix (Fin N₁) (Fin N₁) ℂ) (i : G_V.idx) (j : G_W.idx) : ℂ :=
  (repCount (G_V.lat i) (G_W.lat j) Q : ℂ)

/-- Frobenius isometric embedding `Matrix (Fin N₂) (Fin N₁) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N₂ × Fin N₁)`. -/
def frobEquiv (N₁ N₂ : ℕ) :
    Matrix (Fin N₂) (Fin N₁) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N₂ × Fin N₁) where
  toFun T := WithLp.toLp 2 fun p => T p.1 p.2
  invFun v := Matrix.of fun i j => v (i, j)
  map_add' S T := by ext p; rfl
  map_smul' c T := by ext p; rfl
  left_inv T := by ext i j; rfl
  right_inv v := by ext p; rfl

lemma frobEquiv_norm_sq {N₁ N₂ : ℕ} (T : Matrix (Fin N₂) (Fin N₁) ℂ) :
    ‖frobEquiv N₁ N₂ T‖ ^ 2 = frobNormSq T := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- `LatticeHom L M` transported into the Frobenius Euclidean space `EuclideanSpace ℂ (Fin N₂ × Fin N₁)`. -/
def frobLatticeHom {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂) :
    Submodule ℤ (EuclideanSpace ℂ (Fin N₂ × Fin N₁)) :=
  (LatticeHom L M).map ((frobEquiv N₁ N₂).toLinearMap.restrictScalars ℤ)

/-- `frobLatticeHom L M` is a discrete `ℤ`-lattice in the Frobenius Euclidean space. -/
instance frobLatticeHom_discrete {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂) :
    DiscreteTopology (frobLatticeHom L M) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hfin : ((frobLatticeHom L M : Set (EuclideanSpace ℂ (Fin N₂ × Fin N₁))) ∩
      Metric.closedBall 0 1).Finite := by
    have hpre : ((frobLatticeHom L M : Set (EuclideanSpace ℂ (Fin N₂ × Fin N₁))) ∩
        Metric.closedBall 0 1) =
        (frobEquiv N₁ N₂) '' { T | T ∈ LatticeHom L M ∧ frobNormSq T ≤ 1 } := by
      ext v
      constructor
      · rintro ⟨⟨T, hT, rfl⟩, hball⟩
        refine ⟨T, ⟨hT, ?_⟩, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right] at hball
        change ‖frobEquiv N₁ N₂ T‖ ≤ 1 at hball
        rw [← frobEquiv_norm_sq]
        nlinarith [norm_nonneg (frobEquiv N₁ N₂ T)]
      · rintro ⟨T, ⟨hT, hle⟩, rfl⟩
        refine ⟨⟨T, hT, rfl⟩, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        have hsq : ‖frobEquiv N₁ N₂ T‖ ^ 2 ≤ 1 ^ 2 := by
          rw [frobEquiv_norm_sq]; linarith
        nlinarith [norm_nonneg (frobEquiv N₁ N₂ T)]
    rw [hpre]
    exact (finite_latticeHom_bounded L M 1).image _
  have hfin_nz : (((frobLatticeHom L M : Set (EuclideanSpace ℂ (Fin N₂ × Fin N₁))) ∩
      Metric.closedBall 0 1) \ {0}).Finite := hfin.sdiff
  let U : Set (EuclideanSpace ℂ (Fin N₂ × Fin N₁)) :=
    Metric.ball 0 1 \ (((frobLatticeHom L M : Set (EuclideanSpace ℂ (Fin N₂ × Fin N₁))) ∩
      Metric.closedBall 0 1) \ {0})
  have hU_open : IsOpen U := Metric.isOpen_ball.sdiff hfin_nz.isClosed
  have hpre0 : (Subtype.val : frobLatticeHom L M → EuclideanSpace ℂ (Fin N₂ × Fin N₁)) ⁻¹' U = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, U, Set.mem_sdiff, Metric.mem_ball,
      dist_zero_right, Set.mem_inter_iff, Metric.mem_closedBall, SetLike.mem_coe, not_and, not_not]
    constructor
    · rintro ⟨h1, h2⟩
      exact Subtype.ext (h2 ⟨x.2, h1.le⟩)
    · rintro rfl
      exact ⟨by simp, fun _ => rfl⟩
  rw [← hpre0]
  exact hU_open.preimage continuous_subtype_val

/-- **Unconditional Convergence of the Gaussian Theta Kernel (`summable_gaussianThetaHom`)**:
For every `t > 0` and any two positive-definite Hermitian lattices `L, M`,
`∑_{T ∈ Hom(L, M)} exp(-π t Tr(Tᴴ T))` is unconditionally summable via
`Stage3ThetaSiegelBridge.summable_gaussianTerm`! -/
theorem summable_gaussianThetaHom {N₁ N₂ : ℕ} (L : HermitianLattice N₁) (M : HermitianLattice N₂)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun T : LatticeHom L M => Real.exp (-Real.pi * t * frobNormSq T.1)) := by
  have hsum := Stage3ThetaSiegelBridge.summable_gaussianTerm (L := frobLatticeHom L M) ht
  let e : LatticeHom L M ≃ frobLatticeHom L M :=
    { toFun := fun T => ⟨frobEquiv N₁ N₂ T.1, T.1, T.2, rfl⟩
      invFun := fun v => ⟨(frobEquiv N₁ N₂).symm v.1, by
        rcases v.2 with ⟨T, hT, hTv⟩
        have : (frobEquiv N₁ N₂).symm v.1 = T := by
          rw [← hTv]; exact (frobEquiv N₁ N₂).symm_apply_apply T
        rwa [this]⟩
      left_inv := fun T => Subtype.ext ((frobEquiv N₁ N₂).symm_apply_apply T.1)
      right_inv := fun v => Subtype.ext ((frobEquiv N₁ N₂).apply_symm_apply v.1) }
  have hcomp : (fun T : LatticeHom L M => Real.exp (-Real.pi * t * frobNormSq T.1)) =
      (fun v : frobLatticeHom L M => Stage3ThetaSiegelBridge.gaussianTerm t (v : EuclideanSpace ℂ (Fin N₂ × Fin N₁))) ∘ e := by
    funext T
    change Real.exp (-Real.pi * t * frobNormSq T.1) =
      Real.exp (-Real.pi * t * ‖frobEquiv N₁ N₂ T.1‖ ^ 2)
    rw [frobEquiv_norm_sq]
  rw [hcomp]
  exact hsum.comp_injective e.injective

/-- Concrete convergent Gaussian theta-lift kernel
`K_t(L_i, M_j) = ∑'_{T : L_i → M_j} exp(-π t Tr(Tᴴ T))` for `t > 0`. -/
def gaussianThetaKernel {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (t : ℝ) (i : G_V.idx) (j : G_W.idx) : ℂ :=
  ((∑' T : LatticeHom (G_V.lat i) (G_W.lat j),
      Real.exp (-Real.pi * t * frobNormSq T.1) : ℝ) : ℂ)

theorem gaussianThetaKernel_re_ge_one {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁)
    (G_W : HermitianGenus N₂) {t : ℝ} (ht : 0 < t) (i : G_V.idx) (j : G_W.idx) :
    1 ≤ (gaussianThetaKernel G_V G_W t i j).re := by
  rw [gaussianThetaKernel, Complex.ofReal_re]
  have hsum := summable_gaussianThetaHom (G_V.lat i) (G_W.lat j) ht
  have h0 : (1 : ℝ) = Real.exp (-Real.pi * t * frobNormSq (0 : LatticeHom (G_V.lat i) (G_W.lat j)).1) := by
    simp [frobNormSq]
  rw [h0]
  exact Summable.le_tsum hsum 0 fun T _ => (Real.exp_pos _).le

/-- **Concrete Theta-Lift Kernel Operator `thetaKernelOp`**:
`(thetaKernelOp K φ)(j) = ∑_i (1 / |Aut(L_i)|) * K(i, j) * φ(i)` as a `ℂ`-linear map
`DefiniteAutomorphicSpace G_V →ₗ[ℂ] DefiniteAutomorphicSpace G_W`. -/
def thetaKernelOp {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) :
    DefiniteAutomorphicSpace G_V →ₗ[ℂ] DefiniteAutomorphicSpace G_W where
  toFun φ := ⟨fun j => ∑ i : G_V.idx, (peterssonWeight G_V i : ℂ) * K i j * φ.toFun i⟩
  map_add' φ ψ := by
    ext j
    simp only [DefiniteAutomorphicSpace.add_toFun, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    ext j
    simp only [DefiniteAutomorphicSpace.smul_toFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem thetaKernelOp_apply {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) (φ : DefiniteAutomorphicSpace G_V) (j : G_W.idx) :
    (thetaKernelOp K φ).toFun j = ∑ i : G_V.idx, (peterssonWeight G_V i : ℂ) * K i j * φ.toFun i :=
  rfl

/-- **Exact Adjointness (`thetaKernelOp_adjoint`)**:
`⟨thetaKernelOp K φ, ψ⟩_W = ⟨φ, thetaKernelOp K* ψ⟩_V`. -/
theorem thetaKernelOp_adjoint {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) (φ : DefiniteAutomorphicSpace G_V)
    (ψ : DefiniteAutomorphicSpace G_W) :
    inner ℂ (thetaKernelOp K φ) ψ =
      inner ℂ φ (thetaKernelOp (RallisSeesaw.kerAdj K) ψ) := by
  rw [DefiniteAutomorphicSpace.inner_eq_wip, DefiniteAutomorphicSpace.inner_eq_wip]
  have h1 : (thetaKernelOp K φ).toFun =
      RallisSeesaw.kerOp (fun i => (peterssonWeight G_V i : ℂ)) K φ.toFun := by
    funext j
    simp only [thetaKernelOp_apply, RallisSeesaw.kerOp]
    refine Finset.sum_congr rfl fun i _ => by ring
  have h2 : (thetaKernelOp (RallisSeesaw.kerAdj K) ψ).toFun =
      RallisSeesaw.kerOp (fun j => (peterssonWeight G_W j : ℂ)) (RallisSeesaw.kerAdj K) ψ.toFun := by
    funext i
    simp only [thetaKernelOp_apply, RallisSeesaw.kerOp]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  exact RallisSeesaw.kerOp_adjoint _ _ K φ.toFun ψ.toFun (fun i => Complex.conj_ofReal _)

/-- Identification of the Hilbert adjoint `LinearMap.adjoint (thetaKernelOp K)`. -/
theorem adjoint_thetaKernelOp {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) :
    LinearMap.adjoint (thetaKernelOp K) = thetaKernelOp (RallisSeesaw.kerAdj K) := by
  apply LinearMap.ext
  intro ψ
  refine ext_inner_left ℂ fun φ => ?_
  rw [LinearMap.adjoint_inner_right, thetaKernelOp_adjoint]

/-- Concrete packaging of `thetaKernelOp K` as a `RallisSeesaw.SeesawDualPair`. -/
def thetaKernelSeesawPair {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) :
    RallisSeesaw.SeesawDualPair ℂ (DefiniteAutomorphicSpace G_V) (DefiniteAutomorphicSpace G_W) where
  θ := thetaKernelOp K
  θAdj := thetaKernelOp (RallisSeesaw.kerAdj K)
  adjoint_eq := thetaKernelOp_adjoint K

/-- **Concrete Rallis Seesaw Positivity (`rallis_seesaw_inner_nonneg`)**:
`0 ≤ Re ⟨thetaKernelOp K φ, thetaKernelOp K φ⟩_W`, exact seesaw identity
`⟨φ, K* (K φ)⟩_V = ‖K φ‖² ≥ 0`, and Rallis nonvanishing criterion. -/
theorem rallis_seesaw_inner_nonneg {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) (φ : DefiniteAutomorphicSpace G_V) :
    0 ≤ (inner ℂ (thetaKernelOp K φ) (thetaKernelOp K φ)).re ∧
    (inner ℂ (thetaKernelOp K φ) (thetaKernelOp K φ)).im = 0 ∧
    inner ℂ φ (thetaKernelOp (RallisSeesaw.kerAdj K) (thetaKernelOp K φ)) =
      ((‖thetaKernelOp K φ‖ ^ 2 : ℝ) : ℂ) ∧
    (thetaKernelOp K φ ≠ 0 ↔
      inner ℂ φ (thetaKernelOp (RallisSeesaw.kerAdj K) (thetaKernelOp K φ)) ≠ 0) := by
  let P := thetaKernelSeesawPair K
  have h1 : inner ℂ (thetaKernelOp K φ) (thetaKernelOp K φ) =
      inner ℂ φ (thetaKernelOp (RallisSeesaw.kerAdj K) (thetaKernelOp K φ)) :=
    thetaKernelOp_adjoint K φ (thetaKernelOp K φ)
  have h2 : inner ℂ φ (thetaKernelOp (RallisSeesaw.kerAdj K) (thetaKernelOp K φ)) =
      ((‖thetaKernelOp K φ‖ ^ 2 : ℝ) : ℂ) := P.rallis_pairing_eq_normSq φ
  have h3 := P.rallis_pairing_re_nonneg φ
  have h4 : thetaKernelOp K φ ≠ 0 ↔
      inner ℂ φ (thetaKernelOp (RallisSeesaw.kerAdj K) (thetaKernelOp K φ)) ≠ 0 :=
    P.lift_ne_zero_iff φ
  refine ⟨?_, ?_, h2, h4⟩
  · rw [h1]; exact h3.1
  · rw [h1]; exact h3.2

/-- Weighted row sum `∑_i w_V(i) * ‖K(i, j)‖` for weighted Schur's test. -/
def schurRowSum {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) (j : G_W.idx) : ℝ :=
  ∑ i : G_V.idx, peterssonWeight G_V i * ‖K i j‖

/-- Weighted column sum `∑_j w_W(j) * ‖K(i, j)‖` for weighted Schur's test. -/
def schurColSum {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) (i : G_V.idx) : ℝ :=
  ∑ j : G_W.idx, peterssonWeight G_W j * ‖K i j‖

lemma schurRowSum_nonneg {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) (j : G_W.idx) : 0 ≤ schurRowSum G_V K j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (peterssonWeight_pos G_V i).le (norm_nonneg _)

lemma schurColSum_nonneg {N₁ N₂ : ℕ} {G_V : HermitianGenus N₁} (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) (i : G_V.idx) : 0 ≤ schurColSum G_W K i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (peterssonWeight_pos G_W j).le (norm_nonneg _)

/-- Maximal weighted row sum `max_j ∑_i w_V(i) ‖K(i, j)‖`. -/
def schurMaxRow {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) : ℝ :=
  ((Finset.univ.sup (fun j : G_W.idx => Real.toNNReal (schurRowSum G_V K j)) : NNReal) : ℝ)

/-- Maximal weighted column sum `max_i ∑_j w_W(j) ‖K(i, j)‖`. -/
def schurMaxCol {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) : ℝ :=
  ((Finset.univ.sup (fun i : G_V.idx => Real.toNNReal (schurColSum G_W K i)) : NNReal) : ℝ)

/-- Schur test spectral-norm constant `‖K‖_Schur = √(maxRow * maxCol)`. -/
def schurNorm {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) : ℝ :=
  Real.sqrt (schurMaxRow G_V G_W K * schurMaxCol G_V G_W K)

lemma schurNorm_nonneg {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) : 0 ≤ schurNorm G_V G_W K :=
  Real.sqrt_nonneg _

lemma schurRowSum_le_max {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) (j : G_W.idx) :
    schurRowSum G_V K j ≤ schurMaxRow G_V G_W K := by
  have hle : Real.toNNReal (schurRowSum G_V K j) ≤
      Finset.univ.sup (fun j' : G_W.idx => Real.toNNReal (schurRowSum G_V K j')) :=
    Finset.le_sup (f := fun j' : G_W.idx => Real.toNNReal (schurRowSum G_V K j')) (Finset.mem_univ j)
  have hcast : (Real.toNNReal (schurRowSum G_V K j) : ℝ) ≤ schurMaxRow G_V G_W K := by
    exact_mod_cast hle
  rwa [Real.coe_toNNReal _ (schurRowSum_nonneg G_V K j)] at hcast

lemma schurColSum_le_max {N₁ N₂ : ℕ} (G_V : HermitianGenus N₁) (G_W : HermitianGenus N₂)
    (K : G_V.idx → G_W.idx → ℂ) (i : G_V.idx) :
    schurColSum G_W K i ≤ schurMaxCol G_V G_W K := by
  have hle : Real.toNNReal (schurColSum G_W K i) ≤
      Finset.univ.sup (fun i' : G_V.idx => Real.toNNReal (schurColSum G_W K i')) :=
    Finset.le_sup (f := fun i' : G_V.idx => Real.toNNReal (schurColSum G_W K i')) (Finset.mem_univ i)
  have hcast : (Real.toNNReal (schurColSum G_W K i) : ℝ) ≤ schurMaxCol G_V G_W K := by
    exact_mod_cast hle
  rwa [Real.coe_toNNReal _ (schurColSum_nonneg G_W K i)] at hcast

/-- **Weighted Schur's Test (`thetaKernelOp_norm_le_of_row_col_bounds`)**:
If `∀ j, ∑_i w_V(i) ‖K(i, j)‖ ≤ R` and `∀ i, ∑_j w_W(j) ‖K(i, j)‖ ≤ C`, then
`‖thetaKernelOp K φ‖ ≤ √(R * C) * ‖φ‖`. -/
theorem thetaKernelOp_norm_le_of_row_col_bounds {N₁ N₂ : ℕ}
    {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) {R C : ℝ} (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hRow : ∀ j : G_W.idx, schurRowSum G_V K j ≤ R)
    (hCol : ∀ i : G_V.idx, schurColSum G_W K i ≤ C)
    (φ : DefiniteAutomorphicSpace G_V) :
    ‖thetaKernelOp K φ‖ ≤ Real.sqrt (R * C) * ‖φ‖ := by
  have hsq : ‖thetaKernelOp K φ‖ ^ 2 ≤ R * C * ‖φ‖ ^ 2 := by
    rw [DefiniteAutomorphicSpace.norm_sq_eq, DefiniteAutomorphicSpace.norm_sq_eq]
    have hstep1 : ∀ j : G_W.idx,
        ‖(thetaKernelOp K φ).toFun j‖ ^ 2 ≤
          R * ∑ i : G_V.idx, peterssonWeight G_V i * ‖K i j‖ * ‖φ.toFun i‖ ^ 2 := by
      intro j
      have htri : ‖(thetaKernelOp K φ).toFun j‖ ≤
          ∑ i : G_V.idx, Real.sqrt (peterssonWeight G_V i * ‖K i j‖) *
            (Real.sqrt (peterssonWeight G_V i * ‖K i j‖) * ‖φ.toFun i‖) := by
        rw [thetaKernelOp_apply]
        calc ‖∑ i : G_V.idx, (peterssonWeight G_V i : ℂ) * K i j * φ.toFun i‖
            ≤ ∑ i : G_V.idx, ‖(peterssonWeight G_V i : ℂ) * K i j * φ.toFun i‖ := norm_sum_le _ _
          _ = ∑ i : G_V.idx, Real.sqrt (peterssonWeight G_V i * ‖K i j‖) *
                (Real.sqrt (peterssonWeight G_V i * ‖K i j‖) * ‖φ.toFun i‖) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              have hw : 0 ≤ peterssonWeight G_V i := (peterssonWeight_pos G_V i).le
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, ← mul_assoc,
                Real.mul_self_sqrt (mul_nonneg hw (norm_nonneg _))]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : G_V.idx => Real.sqrt (peterssonWeight G_V i * ‖K i j‖))
        (fun i : G_V.idx => Real.sqrt (peterssonWeight G_V i * ‖K i j‖) * ‖φ.toFun i‖)
      have hleft_sq : (∑ i : G_V.idx, Real.sqrt (peterssonWeight G_V i * ‖K i j‖) ^ 2) =
          schurRowSum G_V K j := by
        unfold schurRowSum
        refine Finset.sum_congr rfl fun i _ =>
          Real.sq_sqrt (mul_nonneg (peterssonWeight_pos G_V i).le (norm_nonneg _))
      have hright_sq : (∑ i : G_V.idx,
            (Real.sqrt (peterssonWeight G_V i * ‖K i j‖) * ‖φ.toFun i‖) ^ 2) =
          ∑ i : G_V.idx, peterssonWeight G_V i * ‖K i j‖ * ‖φ.toFun i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (peterssonWeight_pos G_V i).le (norm_nonneg _))]
      rw [hleft_sq, hright_sq] at hcs
      have hsum_nn : 0 ≤ ∑ i : G_V.idx, peterssonWeight G_V i * ‖K i j‖ * ‖φ.toFun i‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => by
          have := (peterssonWeight_pos G_V i).le
          positivity
      exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
        (hcs.trans (mul_le_mul_of_nonneg_right (hRow j) hsum_nn))
    calc ∑ j : G_W.idx, peterssonWeight G_W j * ‖(thetaKernelOp K φ).toFun j‖ ^ 2
        ≤ ∑ j : G_W.idx, peterssonWeight G_W j *
            (R * ∑ i : G_V.idx, peterssonWeight G_V i * ‖K i j‖ * ‖φ.toFun i‖ ^ 2) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hstep1 j) (peterssonWeight_pos G_W j).le
      _ = R * ∑ i : G_V.idx, peterssonWeight G_V i * ‖φ.toFun i‖ ^ 2 * schurColSum G_W K i := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold schurColSum
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ R * ∑ i : G_V.idx, peterssonWeight G_V i * ‖φ.toFun i‖ ^ 2 * C := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hR0
          exact mul_le_mul_of_nonneg_left (hCol i)
            (mul_nonneg (peterssonWeight_pos G_V i).le (sq_nonneg _))
      _ = R * C * ∑ i : G_V.idx, peterssonWeight G_V i * ‖φ.toFun i‖ ^ 2 := by
          rw [← Finset.sum_mul]; ring
  have hsq' : ‖thetaKernelOp K φ‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖φ‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hR0 hC0)]
    exact hsq
  have hrhs : 0 ≤ Real.sqrt (R * C) * ‖φ‖ := by positivity
  nlinarith [norm_nonneg (thetaKernelOp K φ)]

/-- **Explicit Spectral-Norm Bound via Schur's Test (`thetaKernelOp_norm_le_schur`)**:
`‖thetaKernelOp K φ‖ ≤ ‖K‖_Schur * ‖φ‖`. -/
theorem thetaKernelOp_norm_le_schur {N₁ N₂ : ℕ}
    {G_V : HermitianGenus N₁} {G_W : HermitianGenus N₂}
    (K : G_V.idx → G_W.idx → ℂ) (φ : DefiniteAutomorphicSpace G_V) :
    ‖thetaKernelOp K φ‖ ≤ schurNorm G_V G_W K * ‖φ‖ :=
  thetaKernelOp_norm_le_of_row_col_bounds K
    (show 0 ≤ schurMaxRow G_V G_W K from NNReal.coe_nonneg _)
    (show 0 ≤ schurMaxCol G_V G_W K from NNReal.coe_nonneg _)
    (schurRowSum_le_max G_V G_W K) (schurColSum_le_max G_V G_W K) φ

end AutomorphicSpacesAndThetaKernels

/-! ## Section 3: Concrete `m`-Step Iterated Chain Operator `chainOpM`, Adjoint Reversal & `RankVal` Realization -/

section IteratedChainAndRankVal

/-- Rank sequence `N(j) = k + j * (t + 1)` along the `m`-step definite unitary tower. -/
def chainRank (k t j : ℕ) : ℕ := k + j * (t + 1)

/-- `Fin (m + 1)`-indexed rank sequence `N(j) = k + j * (t + 1)`. -/
def chainRankFin (m k t : ℕ) (j : Fin (m + 1)) : ℕ := chainRank k t j.1

theorem chainRank_eq_chainRanks (R : ChainRanks) (j : ℕ) :
    chainRank R.k R.t j = R.chainRank j := rfl

/-- Concrete `m`-step definite unitary tower `𝒜(U(X_0)) → 𝒜(U(X_1)) → ... → 𝒜(U(X_m))`
with ranks `N(j) = k + j * (t + 1)`. -/
structure DefiniteUnitaryTower (m k t : ℕ) where
  genus : (j : Fin (m + 1)) → HermitianGenus (chainRank k t j.1)
  kernel : (j : Fin m) → (genus j.castSucc).idx → (genus j.succ).idx → ℂ

namespace DefiniteUnitaryTower

/-- Single upward step operator `𝒜(U(X_j)) →ₗ[ℂ] 𝒜(U(X_{j+1}))`. -/
def stepOp {m k t : ℕ} (T : DefiniteUnitaryTower m k t) (j : Fin m) :
    DefiniteAutomorphicSpace (T.genus j.castSucc) →ₗ[ℂ]
      DefiniteAutomorphicSpace (T.genus j.succ) :=
  thetaKernelOp (T.kernel j)

/-- Single downward adjoint step operator `𝒜(U(X_{j+1})) →ₗ[ℂ] 𝒜(U(X_j))`. -/
def stepOpAdj {m k t : ℕ} (T : DefiniteUnitaryTower m k t) (j : Fin m) :
    DefiniteAutomorphicSpace (T.genus j.succ) →ₗ[ℂ]
      DefiniteAutomorphicSpace (T.genus j.castSucc) :=
  thetaKernelOp (RallisSeesaw.kerAdj (T.kernel j))

/-- `r`-step prefix composition along `𝒜(U(X_0)) → ... → 𝒜(U(X_r))` (`r ≤ m`). -/
def chainOpPrefix {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    (r : ℕ) → (hr : r ≤ m) →
    (DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩) →ₗ[ℂ]
      DefiniteAutomorphicSpace (T.genus ⟨r, Nat.lt_succ_of_le hr⟩))
  | 0, _ => LinearMap.id
  | r + 1, hr => (T.stepOp ⟨r, hr⟩).comp (chainOpPrefix T r (Nat.le_of_succ_le hr))

/-- `r`-step reversed adjoint composition along `𝒜(U(X_r)) → ... → 𝒜(U(X_0))` (`r ≤ m`). -/
def chainOpPrefixRev {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    (r : ℕ) → (hr : r ≤ m) →
    (DefiniteAutomorphicSpace (T.genus ⟨r, Nat.lt_succ_of_le hr⟩) →ₗ[ℂ]
      DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩))
  | 0, _ => LinearMap.id
  | r + 1, hr => (chainOpPrefixRev T r (Nat.le_of_succ_le hr)).comp (T.stepOpAdj ⟨r, hr⟩)

/-- **Concrete `m`-Step Iterated Theta-Lift Chain Operator `chainOpM`**:
`𝒜(U(X_0)) →ₗ[ℂ] 𝒜(U(X_m))`. -/
def chainOpM {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩) →ₗ[ℂ]
      DefiniteAutomorphicSpace (T.genus ⟨m, Nat.lt_succ_self m⟩) :=
  chainOpPrefix T m le_rfl

/-- **Reversed Adjoint Chain Operator `chainOpM_rev`**:
`𝒜(U(X_m)) →ₗ[ℂ] 𝒜(U(X_0))`. -/
def chainOpM_rev {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    DefiniteAutomorphicSpace (T.genus ⟨m, Nat.lt_succ_self m⟩) →ₗ[ℂ]
      DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩) :=
  chainOpPrefixRev T m le_rfl

theorem chainOpPrefix_adjoint {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    ∀ (r : ℕ) (hr : r ≤ m),
      LinearMap.adjoint (chainOpPrefix T r hr) = chainOpPrefixRev T r hr
  | 0, _ => by
      simp only [chainOpPrefix, chainOpPrefixRev, LinearMap.adjoint_id]
  | r + 1, hr => by
      simp only [chainOpPrefix, chainOpPrefixRev, LinearMap.adjoint_comp,
        chainOpPrefix_adjoint T r (Nat.le_of_succ_le hr)]
      congr 1
      exact adjoint_thetaKernelOp (T.kernel ⟨r, hr⟩)

/-- **Exact Adjoint Chain Reversal (`chainOpM_adjoint`)**:
`(chainOpM T)* = chainOpM_rev T` and `⟨chainOpM T φ, ψ⟩ = ⟨φ, chainOpM_rev T ψ⟩`. -/
theorem chainOpM_adjoint {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    LinearMap.adjoint T.chainOpM = T.chainOpM_rev :=
  chainOpPrefix_adjoint T m le_rfl

theorem chainOpM_inner_adjoint {m k t : ℕ} (T : DefiniteUnitaryTower m k t)
    (φ : DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩))
    (ψ : DefiniteAutomorphicSpace (T.genus ⟨m, Nat.lt_succ_self m⟩)) :
    inner ℂ (T.chainOpM φ) ψ = inner ℂ φ (T.chainOpM_rev ψ) := by
  rw [← T.chainOpM_adjoint, LinearMap.adjoint_inner_right]

/-- **Iterated Rallis Seesaw Positivity along `chainOpM`**. -/
theorem chainOpM_rallis_nonneg {m k t : ℕ} (T : DefiniteUnitaryTower m k t)
    (φ : DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩)) :
    0 ≤ (inner ℂ φ (T.chainOpM_rev (T.chainOpM φ))).re ∧
    (inner ℂ φ (T.chainOpM_rev (T.chainOpM φ))).im = 0 ∧
    inner ℂ φ (T.chainOpM_rev (T.chainOpM φ)) = ((‖T.chainOpM φ‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : inner ℂ φ (T.chainOpM_rev (T.chainOpM φ)) = ((‖T.chainOpM φ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← T.chainOpM_inner_adjoint, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨sq_nonneg _, rfl, rfl⟩

/-- Prefix submultiplicative Schur norm bound for `r ≤ m`. -/
theorem chainOpPrefix_norm_le {m k t : ℕ} (T : DefiniteUnitaryTower m k t) :
    ∀ (r : ℕ) (hr : r ≤ m) (φ : DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩)),
      ‖chainOpPrefix T r hr φ‖ ≤
        (∏ j : Fin r, schurNorm (T.genus (Fin.castLE hr j).castSucc)
          (T.genus (Fin.castLE hr j).succ) (T.kernel (Fin.castLE hr j))) * ‖φ‖
  | 0, _, φ => by
      change ‖φ‖ ≤ (∏ _j : Fin 0, _) * ‖φ‖
      simp
  | r + 1, hr, φ => by
      simp only [chainOpPrefix, LinearMap.comp_apply]
      have h1 := thetaKernelOp_norm_le_schur (T.kernel ⟨r, hr⟩)
        (chainOpPrefix T r (Nat.le_of_succ_le hr) φ)
      have h2 := chainOpPrefix_norm_le T r (Nat.le_of_succ_le hr) φ
      have hprod : ∏ j : Fin (r + 1), schurNorm (T.genus (Fin.castLE hr j).castSucc)
            (T.genus (Fin.castLE hr j).succ) (T.kernel (Fin.castLE hr j)) =
          (∏ j : Fin r, schurNorm (T.genus (Fin.castLE (Nat.le_of_succ_le hr) j).castSucc)
            (T.genus (Fin.castLE (Nat.le_of_succ_le hr) j).succ)
            (T.kernel (Fin.castLE (Nat.le_of_succ_le hr) j))) *
          schurNorm (T.genus (⟨r, hr⟩ : Fin m).castSucc)
            (T.genus (⟨r, hr⟩ : Fin m).succ) (T.kernel ⟨r, hr⟩) := by
        rw [Fin.prod_univ_castSucc]
        rfl
      rw [hprod]
      calc ‖T.stepOp ⟨r, hr⟩ (chainOpPrefix T r (Nat.le_of_succ_le hr) φ)‖
          ≤ schurNorm (T.genus (⟨r, hr⟩ : Fin m).castSucc)
              (T.genus (⟨r, hr⟩ : Fin m).succ) (T.kernel ⟨r, hr⟩) *
              ‖chainOpPrefix T r (Nat.le_of_succ_le hr) φ‖ := h1
        _ ≤ schurNorm (T.genus (⟨r, hr⟩ : Fin m).castSucc)
              (T.genus (⟨r, hr⟩ : Fin m).succ) (T.kernel ⟨r, hr⟩) *
              ((∏ j : Fin r, schurNorm (T.genus (Fin.castLE (Nat.le_of_succ_le hr) j).castSucc)
                (T.genus (Fin.castLE (Nat.le_of_succ_le hr) j).succ)
                (T.kernel (Fin.castLE (Nat.le_of_succ_le hr) j))) * ‖φ‖) :=
            mul_le_mul_of_nonneg_left h2 (schurNorm_nonneg _ _ _)
        _ = ((∏ j : Fin r, schurNorm (T.genus (Fin.castLE (Nat.le_of_succ_le hr) j).castSucc)
              (T.genus (Fin.castLE (Nat.le_of_succ_le hr) j).succ)
              (T.kernel (Fin.castLE (Nat.le_of_succ_le hr) j))) *
            schurNorm (T.genus (⟨r, hr⟩ : Fin m).castSucc)
              (T.genus (⟨r, hr⟩ : Fin m).succ) (T.kernel ⟨r, hr⟩)) * ‖φ‖ := by ring

/-- **Exact Submultiplicative Schur Norm Bound (`chainOpM_norm_le`)**:
`‖chainOpM T φ‖ ≤ (∏_{j < m} ‖K_j‖_Schur) * ‖φ‖`. -/
theorem chainOpM_norm_le {m k t : ℕ} (T : DefiniteUnitaryTower m k t)
    (φ : DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩)) :
    ‖T.chainOpM φ‖ ≤
      (∏ j : Fin m, schurNorm (T.genus j.castSucc) (T.genus j.succ) (T.kernel j)) * ‖φ‖ := by
  simpa [chainOpM] using chainOpPrefix_norm_le T m le_rfl φ

/-- Universal stabilizer denominator `D_Γ = ∏_{j ≤ m} ∏_{i} |Aut(L_{j,i})| > 0` clearing all
Petersson weights across the entire `m`-step tower. -/
def genusDenom {m k t : ℕ} (T : DefiniteUnitaryTower m k t) : ℕ :=
  ∏ j : Fin (m + 1), ∏ i : (T.genus j).idx, Nat.card (DefiniteUnitaryGroup ((T.genus j).lat i))

theorem genusDenom_pos {m k t : ℕ} (T : DefiniteUnitaryTower m k t) : 0 < T.genusDenom :=
  Finset.prod_pos fun j _ => Finset.prod_pos fun i _ =>
    card_definiteUnitaryGroup_pos ((T.genus j).lat i)

theorem card_stab_dvd_genusDenom {m k t : ℕ} (T : DefiniteUnitaryTower m k t)
    (j : Fin (m + 1)) (i : (T.genus j).idx) :
    Nat.card (DefiniteUnitaryGroup ((T.genus j).lat i)) ∣ T.genusDenom := by
  have h1 : Nat.card (DefiniteUnitaryGroup ((T.genus j).lat i)) ∣
      ∏ i' : (T.genus j).idx, Nat.card (DefiniteUnitaryGroup ((T.genus j).lat i')) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have h2 : (∏ i' : (T.genus j).idx, Nat.card (DefiniteUnitaryGroup ((T.genus j).lat i'))) ∣
      T.genusDenom :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  exact h1.trans h2

/-- **Unconditional Denominator-Clearing Integrality Preservation (`chainOpM_clears_denominators`)**:
If every step kernel entry lies in a subring `S ⊆ ℂ` (e.g., `ℤ` for algebraic representation counts
`thetaRepKernel`) and `φ` takes values in `S`, then `(T.genusDenom)^m * (T.chainOpM φ)(i) ∈ S`! -/
theorem chainOpPrefix_clears_denominators {m k t : ℕ} (T : DefiniteUnitaryTower m k t) (S : Subring ℂ)
    (hK : ∀ (j : Fin m) (a : (T.genus j.castSucc).idx) (b : (T.genus j.succ).idx),
      T.kernel j a b ∈ S)
    (φ : DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩))
    (hφ : ∀ a, φ.toFun a ∈ S) :
    ∀ (r : ℕ) (hr : r ≤ m) (b : (T.genus ⟨r, Nat.lt_succ_of_le hr⟩).idx),
      (T.genusDenom : ℂ) ^ r * (chainOpPrefix T r hr φ).toFun b ∈ S
  | 0, _, b => by
      change (T.genusDenom : ℂ) ^ 0 * φ.toFun b ∈ S
      simpa using hφ b
  | r + 1, hr, b => by
      simp only [chainOpPrefix, LinearMap.comp_apply, stepOp, thetaKernelOp_apply, Finset.mul_sum]
      refine S.sum_mem fun a _ => ?_
      obtain ⟨q, hq⟩ := T.card_stab_dvd_genusDenom (⟨r, hr⟩ : Fin m).castSucc a
      have hpos : (Nat.card (DefiniteUnitaryGroup ((T.genus (⟨r, hr⟩ : Fin m).castSucc).lat a)) : ℂ) ≠ 0 := by
        exact_mod_cast (card_definiteUnitaryGroup_pos _).ne'
      have hwt : (T.genusDenom : ℂ) * (peterssonWeight (T.genus (⟨r, hr⟩ : Fin m).castSucc) a : ℂ) =
          (q : ℂ) := by
        unfold peterssonWeight
        rw [hq]
        push_cast
        field_simp [hpos]
      have hterm : (T.genusDenom : ℂ) ^ (r + 1) *
          ((peterssonWeight (T.genus (⟨r, hr⟩ : Fin m).castSucc) a : ℂ) *
            T.kernel ⟨r, hr⟩ a b *
            (chainOpPrefix T r (Nat.le_of_succ_le hr) φ).toFun a) =
          (q : ℂ) * T.kernel ⟨r, hr⟩ a b *
            ((T.genusDenom : ℂ) ^ r * (chainOpPrefix T r (Nat.le_of_succ_le hr) φ).toFun a) := by
        rw [pow_succ]
        linear_combination (T.genusDenom : ℂ) ^ r * T.kernel ⟨r, hr⟩ a b *
          (chainOpPrefix T r (Nat.le_of_succ_le hr) φ).toFun a * hwt
      rw [hterm]
      exact S.mul_mem (S.mul_mem (natCast_mem S q) (hK ⟨r, hr⟩ a b))
        (chainOpPrefix_clears_denominators T S hK φ hφ r (Nat.le_of_succ_le hr) a)

theorem chainOpM_clears_denominators {m k t : ℕ} (T : DefiniteUnitaryTower m k t) (S : Subring ℂ)
    (hK : ∀ (j : Fin m) (a : (T.genus j.castSucc).idx) (b : (T.genus j.succ).idx),
      T.kernel j a b ∈ S)
    (φ : DefiniteAutomorphicSpace (T.genus ⟨0, Nat.zero_lt_succ m⟩))
    (hφ : ∀ a, φ.toFun a ∈ S)
    (b : (T.genus ⟨m, Nat.lt_succ_self m⟩).idx) :
    (T.genusDenom : ℂ) ^ m * (T.chainOpM φ).toFun b ∈ S :=
  chainOpPrefix_clears_denominators T S hK φ hφ m le_rfl b

/-- Canonical bridge to `RallisSeesaw.RankSteppedChain R` with `X_j = DefiniteHermitianSpace (R.chainRank j)`. -/
def toRankSteppedChain (R : ChainRanks) : RallisSeesaw.RankSteppedChain R where
  E j := DefiniteHermitianSpace (R.chainRank j)
  dim_eq j _ := finrank_definiteHermitianSpace_complex (R.chainRank j)

/-- Canonical bridge of a concrete `DefiniteUnitaryTower R.m R.k R.t` to
`ThetaSlopeEngine.IteratedThetaChain R`. -/
def toIteratedThetaChain (R : ChainRanks) (T : DefiniteUnitaryTower R.m R.k R.t) :
    ThetaSlopeEngine.IteratedThetaChain R where
  cls j := if h : j ≤ R.m then (T.genus ⟨j, Nat.lt_succ_of_le h⟩).idx else PUnit
  clsFin j := by
    dsimp only
    split_ifs with h
    · exact (T.genus ⟨j, Nat.lt_succ_of_le h⟩).finIdx
    · infer_instance
  Y _ := PUnit
  wt j := if h : j ≤ R.m then
      fun c => (peterssonWeight (T.genus ⟨j, Nat.lt_succ_of_le h⟩) (cast (by simp [h]) c) : ℂ)
    else fun _ => 0
  Kmap j := if h : j < R.m then
      fun a b =>
        (T.kernel ⟨j, h⟩ (cast (by simp [Nat.le_of_lt h]) a)
          (cast (by simp [h]) b)) • LinearMap.id
    else fun _ _ => 0

end DefiniteUnitaryTower

/-- Singleton genus built from a single concrete positive-definite Hermitian lattice `L`. -/
def singletonGenus {N : ℕ} (L : HermitianLattice N) : HermitianGenus N where
  idx := PUnit
  lat _ := L

/-- **Canonical Unconditional Gaussian Definite Unitary Tower** on `m + 1` positive-definite
Hermitian spaces `X_j = ℂ^(k + j*(t + 1))` with Gram matrices `H j` and convergent Gaussian theta
kernels `gaussianThetaKernel` (`t_gauss > 0`). -/
def canonicalGaussianTower (m k t d : ℕ) (hd : 0 < d) (t_gauss : ℝ)
    (H : ∀ j : Fin (m + 1), Matrix (Fin (chainRank k t j.1)) (Fin (chainRank k t j.1)) ℂ)
    (hH : ∀ j, (H j).PosDef) : DefiniteUnitaryTower m k t where
  genus j := singletonGenus (hermitianLatticeOfPosDef d hd (H j) (hH j))
  kernel j := gaussianThetaKernel
    (singletonGenus (hermitianLatticeOfPosDef d hd (H j.castSucc) (hH j.castSucc)))
    (singletonGenus (hermitianLatticeOfPosDef d hd (H j.succ) (hH j.succ))) t_gauss

/-- **Canonical Unconditional Algebraic-Representation Definite Unitary Tower** on `m + 1`
positive-definite Hermitian spaces `X_j = ℂ^(k + j*(t + 1))` with algebraic theta kernels
`thetaRepKernel`. -/
def canonicalRepTower (m k t d : ℕ) (hd : 0 < d)
    (H : ∀ j : Fin (m + 1), Matrix (Fin (chainRank k t j.1)) (Fin (chainRank k t j.1)) ℂ)
    (hH : ∀ j, (H j).PosDef)
    (Q : ∀ j : Fin m, Matrix (Fin (chainRank k t j.castSucc.1)) (Fin (chainRank k t j.castSucc.1)) ℂ) :
    DefiniteUnitaryTower m k t where
  genus j := singletonGenus (hermitianLatticeOfPosDef d hd (H j) (hH j))
  kernel j := thetaRepKernel
    (singletonGenus (hermitianLatticeOfPosDef d hd (H j.castSucc) (hH j.castSucc)))
    (singletonGenus (hermitianLatticeOfPosDef d hd (H j.succ) (hH j.succ))) (Q j)

/-- Elementary ceiling-envelope lemma: for every real `u ≥ 1`, `u ≤ ⌈u⌉₊ ≤ 2 * u`. -/
lemma ceil_bounds_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    u ≤ (⌈u⌉₊ : ℝ) ∧ (⌈u⌉₊ : ℝ) ≤ 2 * u := by
  refine ⟨Nat.le_ceil u, ?_⟩
  have hlt : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

/-- **Concrete `ChainRanks` constructor** matching `Stage2ThetaWire.stage2ScaleParams` and
`ThetaSlopeEngine.RankVal` unconditionally! -/
def concreteChainRanks (x eps : ℝ) (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52) :
    ChainRanks :=
  let s := Stage2ThetaWire.stage2ScaleParams x eps hx1 heps heps52
  let n : ℕ := ⌈x ^ (2 + 8 * eps)⌉₊
  let f : ℕ := 2 * n
  let m : ℕ := ⌈Real.sqrt (x * x ^ (-(eps / 8)))⌉₊
  let k : ℕ := ⌈x ^ ((9 : ℝ) / 2 + 10 * eps)⌉₊
  let r : ℕ := k + m - 1
  let R0 : ChainRanks := ⟨n, f, r, k, m, 0⟩
  let t : ℕ := (8 * f - 1) * r + 4 + TOv s * nWv R0 s
  ⟨n, f, r, k, m, t⟩

/-- **Exact `ThetaSlopeEngine.RankVal` & Definite Unitary Tower Realization
(`chainRank_realizes_rankVal`)**:
For every `0 < eps < 1 / 52` and large `x` (`x ≥ 2^100`, `x ≥ 2^(16/(9*eps))`),
`R := concreteChainRanks x eps ...` UNCONDITIONALLY satisfies:
1. `RankVal (stage2ScaleParams x eps ...) R`,
2. all 10 `Stage2ThetaWire.rankVal_discharges_chain_window_bounds` inequalities
   (`R.t ≤ ⌊x ^ 400⌋₊`, `x^(1/2 - eps) ≤ R.m ≤ x^(1/2 + eps/2)`, `x * R.m ≤ R.k ≤ x^5`, etc.),
3. exact rank realization by the concrete definite unitary tower of spaces
   `X_j = DefiniteHermitianSpace (chainRank R.k R.t j.1)` of complex dimension `R.k + j*(R.t + 1)`
   and real dimension `2 * (R.k + j*(R.t + 1))`! -/
theorem chainRank_realizes_rankVal {x eps : ℝ}
    (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52)
    (hx100 : (2 : ℝ) ^ 100 ≤ x)
    (hx16 : (2 : ℝ) ^ (16 / (9 * eps)) ≤ x) :
    let s := Stage2ThetaWire.stage2ScaleParams x eps hx1 heps heps52
    let R := concreteChainRanks x eps hx1 heps heps52
    RankVal s R ∧
    R.f = 2 * R.n ∧
    2 ≤ R.m ∧
    R.m + 3 ≤ R.k ∧
    R.r = R.k + R.m - 1 ∧
    R.t ≤ ⌊x ^ (400 : ℝ)⌋₊ ∧
    ∀ j : Fin (R.m + 1),
      Module.finrank ℂ (DefiniteHermitianSpace (chainRank R.k R.t j.1)) = R.chainRank j.1 ∧
      Module.finrank ℝ (DefiniteHermitianSpace (chainRank R.k R.t j.1)) = 2 * R.chainRank j.1 := by
  set s := Stage2ThetaWire.stage2ScaleParams x eps hx1 heps heps52
  set R := concreteChainRanks x eps hx1 heps heps52
  have hx0 : 0 < x := by linarith
  have hx_ge1 : 1 ≤ x := hx1.le
  have h16 : (16 : ℝ) ≤ x := by
    have : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
    linarith
  have hn_u : 1 ≤ x ^ (2 + 8 * eps) := Real.one_le_rpow hx_ge1 (by linarith)
  have hm_u_eq : Real.sqrt (x * x ^ (-(eps / 8))) = x ^ ((1 : ℝ) / 2 - eps / 16) := by
    rw [Real.sqrt_eq_rpow]
    have hmul : x * x ^ (-(eps / 8)) = x ^ ((1 : ℝ) + -(eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [hmul, ← Real.rpow_mul hx0.le]
    congr 1; ring
  have hm_ge2_real : (2 : ℝ) ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
    rw [hm_u_eq]
    have h2 : (2 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 4) := h2
      _ ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) h16 (by norm_num)
      _ ≤ x ^ ((1 : ℝ) / 2 - eps / 16) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
  have hm_u : 1 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by linarith
  have hk_u : 1 ≤ x ^ ((9 : ℝ) / 2 + 10 * eps) := Real.one_le_rpow hx_ge1 (by linarith)
  have hn_b : x ^ (2 + 8 * eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) :=
    ceil_bounds_of_one_le hn_u
  have hm_b : Real.sqrt (x * x ^ (-(eps / 8))) ≤ (R.m : ℝ) ∧
      (R.m : ℝ) ≤ 2 * Real.sqrt (x * x ^ (-(eps / 8))) :=
    ceil_bounds_of_one_le hm_u
  have hk_b : x ^ ((9 : ℝ) / 2 + 10 * eps) ≤ (R.k : ℝ) ∧
      (R.k : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 2 + 10 * eps) :=
    ceil_bounds_of_one_le hk_u
  have hf_eq : R.f = 2 * R.n := rfl
  have hn_pos : 0 < R.n := by
    have : (1 : ℝ) ≤ (R.n : ℝ) := hn_u.trans hn_b.1
    exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
  have hf_pos : 1 ≤ R.f := by omega
  have hm2 : 2 ≤ R.m := by
    have : (2 : ℝ) ≤ (R.m : ℝ) := hm_ge2_real.trans hm_b.1
    exact_mod_cast this
  have hmk : R.m + 3 ≤ R.k := by
    have hm_le_x : (R.m : ℝ) ≤ 2 * x := by
      calc (R.m : ℝ) ≤ 2 * Real.sqrt (x * x ^ (-(eps / 8))) := hm_b.2
        _ = 2 * x ^ ((1 : ℝ) / 2 - eps / 16) := by rw [hm_u_eq]
        _ ≤ 2 * x ^ (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)) (by norm_num)
        _ = 2 * x := by rw [Real.rpow_one]
    have hx_le_k : 2 * x + 3 ≤ (R.k : ℝ) := by
      have hx2 : 2 * x + 3 ≤ x ^ (2 : ℝ) := by
        rw [Real.rpow_two]; nlinarith
      have hx2k : x ^ (2 : ℝ) ≤ x ^ ((9 : ℝ) / 2 + 10 * eps) :=
        Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
      linarith [hk_b.1]
    have hreal : ((R.m + 3 : ℕ) : ℝ) ≤ (R.k : ℝ) := by push_cast; linarith
    exact_mod_cast hreal
  have hr_eq : R.r = R.k + R.m - 1 := rfl
  have hnWv_eq : nWv R s = nWv ⟨R.n, R.f, R.r, R.k, R.m, 0⟩ s := rfl
  have hbal : R.r + R.t = 8 * R.f * R.r + 4 + TOv s * nWv R s := by
    rw [hnWv_eq]
    change R.r + ((8 * R.f - 1) * R.r + 4 + TOv s * nWv ⟨R.n, R.f, R.r, R.k, R.m, 0⟩ s) = _
    have h8f : 1 ≤ 8 * R.f := by omega
    zify [h8f]
    ring
  have hRV : RankVal s R := ⟨hn_b, hm_b, hk_b, hbal⟩
  have h10 := Stage2ThetaWire.rankVal_discharges_chain_window_bounds hx1 heps heps52 hx100 hx16
    hf_eq hm2 hmk hr_eq hRV
  refine ⟨hRV, hf_eq, hm2, hmk, hr_eq, h10.2.2.1, fun j => ?_⟩
  exact ⟨finrank_definiteHermitianSpace_complex _, finrank_definiteHermitianSpace_real _⟩

end IteratedChainAndRankVal

/-! ## Section 4: Hermitian Tensor Covolume Scaling & `Stage4ArakelovBost` / `Stage10GeometryOfNumbers` Chain Bridge -/

section TensorCovolumeAndMinkowskiBostBridge

/-- Kronecker tensor product of two Hermitian matrices reindexed onto `Fin (N₁ * N₂)`. -/
def hermitianTensorMatrix {N₁ N₂ : ℕ}
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) :
    Matrix (Fin (N₁ * N₂)) (Fin (N₁ * N₂)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker H₁ H₂)

/-- Spectral factorization of `Matrix.kronecker H₁ H₂` via the unitary Kronecker product
`U₁ ⊗ₖ U₂`, simultaneously proving positive-definiteness and the exact determinant identity! -/
private lemma kronecker_spectral_factorization {N₁ N₂ : ℕ}
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (hH₁ : H₁.PosDef)
    (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) (hH₂ : H₂.PosDef) :
    let U₁ : Matrix (Fin N₁) (Fin N₁) ℂ := hH₁.isHermitian.eigenvectorUnitary.1
    let U₂ : Matrix (Fin N₂) (Fin N₂) ℂ := hH₂.isHermitian.eigenvectorUnitary.1
    let U : Matrix (Fin N₁ × Fin N₂) (Fin N₁ × Fin N₂) ℂ := Matrix.kronecker U₁ U₂
    let D : Matrix (Fin N₁ × Fin N₂) (Fin N₁ × Fin N₂) ℂ :=
      Matrix.diagonal (fun p => ((hH₁.isHermitian.eigenvalues p.1 *
        hH₂.isHermitian.eigenvalues p.2 : ℝ) : ℂ))
    Matrix.kronecker H₁ H₂ = U * D * Uᴴ ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 := by
  intro U₁ U₂ U D
  let D₁ : Matrix (Fin N₁) (Fin N₁) ℂ :=
    Matrix.diagonal (fun i => ((hH₁.isHermitian.eigenvalues i : ℝ) : ℂ))
  let D₂ : Matrix (Fin N₂) (Fin N₂) ℂ :=
    Matrix.diagonal (fun j => ((hH₂.isHermitian.eigenvalues j : ℝ) : ℂ))
  have h1 : H₁ = U₁ * D₁ * U₁ᴴ := by
    simpa [U₁, D₁, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using hH₁.isHermitian.spectral_theorem
  have h2 : H₂ = U₂ * D₂ * U₂ᴴ := by
    simpa [U₂, D₂, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using hH₂.isHermitian.spectral_theorem
  have hU_conj : Uᴴ = Matrix.kronecker U₁ᴴ U₂ᴴ := by
    ext p q
    simp [U, Matrix.conjTranspose_apply, star_mul']
  have hUU1 : U₁ * U₁ᴴ = 1 := hH₁.isHermitian.eigenvectorUnitary.2.2
  have hUU2 : U₂ * U₂ᴴ = 1 := hH₂.isHermitian.eigenvectorUnitary.2.2
  have hU1U : U₁ᴴ * U₁ = 1 := hH₁.isHermitian.eigenvectorUnitary.2.1
  have hU2U : U₂ᴴ * U₂ = 1 := hH₂.isHermitian.eigenvectorUnitary.2.1
  have hD : Matrix.kronecker D₁ D₂ = D := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    change D₁ i₁ i₂ * D₂ j₁ j₂ = D (i₁, j₁) (i₂, j₂)
    simp only [D₁, D₂, D, Matrix.diagonal_apply, Prod.mk.injEq]
    by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂
    · subst hi; subst hj; simp
    · subst hi; simp [hj]
    · subst hj; simp [hi]
    · simp [hi]
  have hkmul : ∀ (A B : Matrix (Fin N₁) (Fin N₁) ℂ) (C D : Matrix (Fin N₂) (Fin N₂) ℂ),
      Matrix.kronecker (A * B) (C * D) = Matrix.kronecker A C * Matrix.kronecker B D :=
    fun A B C D => Matrix.mul_kronecker_mul A B C D
  have hkone : Matrix.kronecker (1 : Matrix (Fin N₁) (Fin N₁) ℂ) (1 : Matrix (Fin N₂) (Fin N₂) ℂ) = 1 :=
    Matrix.one_kronecker_one
  refine ⟨?_, ?_, ?_⟩
  · calc Matrix.kronecker H₁ H₂
        = Matrix.kronecker ((U₁ * D₁) * U₁ᴴ) ((U₂ * D₂) * U₂ᴴ) := by rw [← h1, ← h2]
      _ = Matrix.kronecker (U₁ * D₁) (U₂ * D₂) * Matrix.kronecker U₁ᴴ U₂ᴴ :=
            hkmul (U₁ * D₁) U₁ᴴ (U₂ * D₂) U₂ᴴ
      _ = (Matrix.kronecker U₁ U₂ * Matrix.kronecker D₁ D₂) * Matrix.kronecker U₁ᴴ U₂ᴴ := by
            rw [hkmul U₁ D₁ U₂ D₂]
      _ = U * D * Uᴴ := by rw [hD, hU_conj]
  · rw [hU_conj]
    change Matrix.kronecker U₁ U₂ * Matrix.kronecker U₁ᴴ U₂ᴴ = 1
    rw [← hkmul, hUU1, hUU2, hkone]
  · rw [hU_conj]
    change Matrix.kronecker U₁ᴴ U₂ᴴ * Matrix.kronecker U₁ U₂ = 1
    rw [← hkmul, hU1U, hU2U, hkone]

/-- Positive-definiteness of the Hermitian Kronecker tensor product `H₁ ⊗ₖ H₂`. -/
theorem hermitianTensorMatrix_posDef {N₁ N₂ : ℕ}
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (hH₁ : H₁.PosDef)
    (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) (hH₂ : H₂.PosDef) :
    (hermitianTensorMatrix H₁ H₂).PosDef := by
  obtain ⟨hfac, hUU', _⟩ := kronecker_spectral_factorization H₁ hH₁ H₂ hH₂
  set U₁ : Matrix (Fin N₁) (Fin N₁) ℂ := hH₁.isHermitian.eigenvectorUnitary.1
  set U₂ : Matrix (Fin N₂) (Fin N₂) ℂ := hH₂.isHermitian.eigenvectorUnitary.1
  set U : Matrix (Fin N₁ × Fin N₂) (Fin N₁ × Fin N₂) ℂ := Matrix.kronecker U₁ U₂
  set lam : Fin N₁ × Fin N₂ → ℝ := fun p =>
    hH₁.isHermitian.eigenvalues p.1 * hH₂.isHermitian.eigenvalues p.2
  have hlam_pos : ∀ p, 0 < lam p := fun p =>
    mul_pos (hH₁.eigenvalues_pos p.1) (hH₂.eigenvalues_pos p.2)
  have hK_pos : (Matrix.kronecker H₁ H₂).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · rw [Matrix.IsHermitian]
      ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
      change star (H₁ i₂ i₁ * H₂ j₂ j₁) = H₁ i₁ i₂ * H₂ j₁ j₂
      have h1 := congrFun (congrFun hH₁.isHermitian.eq i₁) i₂
      have h2 := congrFun (congrFun hH₂.isHermitian.eq j₁) j₂
      simp only [Matrix.conjTranspose_apply] at h1 h2
      rw [star_mul', h1, h2, mul_comm]
    · intro x hx
      let y : Fin N₁ × Fin N₂ → ℂ := Uᴴ.mulVec x
      have hy_ne : y ≠ 0 := by
        intro hy0
        apply hx
        calc x = (1 : Matrix _ _ ℂ).mulVec x := (Matrix.one_mulVec x).symm
          _ = (U * Uᴴ).mulVec x := by rw [hUU']
          _ = U.mulVec y := (Matrix.mulVec_mulVec x U Uᴴ).symm
          _ = 0 := by rw [hy0, Matrix.mulVec_zero]
      have hsy : star x ᵥ* U = star y := by
        dsimp only [y]
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      have hquad : star x ⬝ᵥ (Matrix.kronecker H₁ H₂).mulVec x =
          ∑ p : Fin N₁ × Fin N₂, ((lam p * ‖y p‖ ^ 2 : ℝ) : ℂ) := by
        rw [hfac, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec, hsy]
        simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
        refine Finset.sum_congr rfl fun p _ => ?_
        dsimp only [lam]
        push_cast
        rw [Complex.star_def, ← mul_assoc, mul_comm (starRingEnd ℂ (y p)), mul_assoc,
          Complex.conj_mul']
      rw [hquad, ← Complex.ofReal_sum, Complex.zero_lt_real]
      have hex : ∃ p₀, y p₀ ≠ 0 := Function.ne_iff.mp hy_ne
      obtain ⟨p₀, hp₀⟩ := hex
      exact Finset.sum_pos' (fun p _ => mul_nonneg (hlam_pos p).le (sq_nonneg _))
        ⟨p₀, Finset.mem_univ p₀, mul_pos (hlam_pos p₀) (sq_pos_of_pos (norm_pos_iff.mpr hp₀))⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hK_pos ⊢
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [hermitianTensorMatrix, Matrix.conjTranspose_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    exact congrFun (congrFun hK_pos.1.eq (finProdFinEquiv.symm i)) (finProdFinEquiv.symm j)
  · intro x hx
    let x' : Fin N₁ × Fin N₂ → ℂ := x ∘ finProdFinEquiv
    have hx' : x' ≠ 0 := fun h0 => hx (funext fun k => by
      have := congrFun h0 (finProdFinEquiv.symm k)
      simpa only [x', Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using this)
    have heq : star x ⬝ᵥ (hermitianTensorMatrix H₁ H₂).mulVec x =
        star x' ⬝ᵥ (Matrix.kronecker H₁ H₂).mulVec x' := by
      simp only [dotProduct, Matrix.mulVec, hermitianTensorMatrix, Matrix.reindex_apply,
        Matrix.submatrix_apply, x', Pi.star_apply, Function.comp_apply]
      rw [← finProdFinEquiv.sum_comp]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [← finProdFinEquiv.sum_comp]
      refine Finset.sum_congr rfl fun q _ => by simp
    rw [heq]
    exact hK_pos.2 hx'

/-- Exact determinant formula for the Hermitian Kronecker tensor product:
`det(H₁ ⊗ₖ H₂) = det(H₁)^N₂ * det(H₂)^N₁`. -/
theorem det_hermitianTensorMatrix {N₁ N₂ : ℕ}
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (hH₁ : H₁.PosDef)
    (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) (hH₂ : H₂.PosDef) :
    (hermitianTensorMatrix H₁ H₂).det = H₁.det ^ N₂ * H₂.det ^ N₁ := by
  obtain ⟨hfac, hUU', _⟩ := kronecker_spectral_factorization H₁ hH₁ H₂ hH₂
  unfold hermitianTensorMatrix
  rw [Matrix.det_reindex_self, hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hU1 : (Matrix.kronecker hH₁.isHermitian.eigenvectorUnitary.1
      hH₂.isHermitian.eigenvectorUnitary.1).det *
      (Matrix.kronecker hH₁.isHermitian.eigenvectorUnitary.1
      hH₂.isHermitian.eigenvectorUnitary.1)ᴴ.det = 1 := by
    rw [← Matrix.det_mul, hUU', Matrix.det_one]
  have hprod : ∏ p : Fin N₁ × Fin N₂,
      ((hH₁.isHermitian.eigenvalues p.1 * hH₂.isHermitian.eigenvalues p.2 : ℝ) : ℂ) =
      H₁.det ^ N₂ * H₂.det ^ N₁ := by
    rw [Fintype.prod_prod_type, posDef_det_eq_prod_eigenvalues H₁ hH₁,
      posDef_det_eq_prod_eigenvalues H₂ hH₂]
    simp only [Complex.ofReal_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow]
  rw [hprod]
  linear_combination (H₁.det ^ N₂ * H₂.det ^ N₁) * hU1

/-- **Concrete Hermitian Lattice Tensor Covolume Scaling (`covolume_hermitian_tensor_eq`)**:
For any CM order `𝒪_d` (`d ≥ 1`) and positive-definite Hermitian Gram matrices `H₁, H₂` of ranks
`N₁, N₂`:
`covol(L(d, H₁ ⊗ₖ H₂)) = (√d)^(N₁ * N₂) * (det H₁).re ^ N₂ * (det H₂).re ^ N₁`. -/
theorem covolume_hermitian_tensor_eq {N₁ N₂ : ℕ} (d : ℕ) (hd : 0 < d)
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (hH₁ : H₁.PosDef)
    (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) (hH₂ : H₂.PosDef) :
    ArakelovCovolume.covol
      (hermitianLatticeOfPosDef d hd (hermitianTensorMatrix H₁ H₂)
        (hermitianTensorMatrix_posDef H₁ hH₁ H₂ hH₂)).lat =
      (Real.sqrt d) ^ (N₁ * N₂) * H₁.det.re ^ N₂ * H₂.det.re ^ N₁ := by
  rw [covolume_hermitian_ofPosDef d hd _ (hermitianTensorMatrix_posDef H₁ hH₁ H₂ hH₂),
    det_hermitianTensorMatrix H₁ hH₁ H₂ hH₂]
  have h1 : H₁.det = (H₁.det.re : ℂ) := Complex.ext rfl (posDef_det_re_pos H₁ hH₁).2
  have h2 : H₂.det = (H₂.det.re : ℂ) := Complex.ext rfl (posDef_det_re_pos H₂ hH₂).2
  have hre : (H₁.det ^ N₂ * H₂.det ^ N₁).re = H₁.det.re ^ N₂ * H₂.det.re ^ N₁ := by
    conv_lhs => rw [h1, h2]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  ring

/-- Gaussian (`d = 1`) pure multiplicative tensor covolume law:
`covol(L(1, H₁ ⊗ₖ H₂)) = covol(L(1, H₁))^N₂ * covol(L(1, H₂))^N₁`. -/
theorem covolume_gaussian_tensor_eq {N₁ N₂ : ℕ}
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (hH₁ : H₁.PosDef)
    (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) (hH₂ : H₂.PosDef) :
    ArakelovCovolume.covol
      (hermitianLatticeOfPosDef 1 Nat.one_pos (hermitianTensorMatrix H₁ H₂)
        (hermitianTensorMatrix_posDef H₁ hH₁ H₂ hH₂)).lat =
      (ArakelovCovolume.covol (hermitianLatticeOfPosDef 1 Nat.one_pos H₁ hH₁).lat) ^ N₂ *
        (ArakelovCovolume.covol (hermitianLatticeOfPosDef 1 Nat.one_pos H₂ hH₂).lat) ^ N₁ := by
  rw [covolume_hermitian_tensor_eq 1 Nat.one_pos H₁ hH₁ H₂ hH₂,
    covolume_hermitian_ofPosDef 1 Nat.one_pos H₁ hH₁,
    covolume_hermitian_ofPosDef 1 Nat.one_pos H₂ hH₂]
  simp

/-- **Exact Additive Arakelov Slope Law under Hermitian Tensor Product (`slope_hermitian_tensor_eq`)**:
For `d = 1` and `N₁, N₂ ≥ 1`:
`slope(L(1, H₁ ⊗ₖ H₂)) = slope(L(1, H₁)) + slope(L(1, H₂))`. -/
theorem slope_hermitian_tensor_eq {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (H₁ : Matrix (Fin N₁) (Fin N₁) ℂ) (hH₁ : H₁.PosDef)
    (H₂ : Matrix (Fin N₂) (Fin N₂) ℂ) (hH₂ : H₂.PosDef) :
    ArakelovCovolume.slope
      (hermitianLatticeOfPosDef 1 Nat.one_pos (hermitianTensorMatrix H₁ H₂)
        (hermitianTensorMatrix_posDef H₁ hH₁ H₂ hH₂)).lat =
      ArakelovCovolume.slope (hermitianLatticeOfPosDef 1 Nat.one_pos H₁ hH₁).lat +
        ArakelovCovolume.slope (hermitianLatticeOfPosDef 1 Nat.one_pos H₂ hH₂).lat := by
  unfold ArakelovCovolume.slope ArakelovCovolume.degAr
  rw [HermitianLattice.rk_eq, HermitianLattice.rk_eq, HermitianLattice.rk_eq,
    covolume_gaussian_tensor_eq H₁ hH₁ H₂ hH₂]
  have hc1 : 0 < ArakelovCovolume.covol (hermitianLatticeOfPosDef 1 Nat.one_pos H₁ hH₁).lat :=
    ArakelovCovolume.covol_pos _
  have hc2 : 0 < ArakelovCovolume.covol (hermitianLatticeOfPosDef 1 Nat.one_pos H₂ hH₂).lat :=
    ArakelovCovolume.covol_pos _
  rw [Real.log_mul (pow_pos hc1 N₂).ne' (pow_pos hc2 N₁).ne', Real.log_pow, Real.log_pow]
  have h1 : (N₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN₁.ne'
  have h2 : (N₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN₂.ne'
  push_cast
  field_simp [h1, h2]
  ring

/-- **Unified `m`-Step Chain Bridge to `Stage4ArakelovBost` & `Stage10GeometryOfNumbers`
(`chain_hermitian_minkowski_bost_bridge`)**:
For EVERY `m`-step family of positive-definite Hermitian lattices `L_0, ..., L_m` of ranks
`N_j = k + j * (t + 1)` (`1 ≤ k`), connects `ArakelovCovolume.slope`, `ArakelovCovolume.muMax`,
`Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1`,
`Stage10GeometryOfNumbers.minkowski_second_theorem_upper`, and
`Stage10GeometryOfNumbers.hermite_minkowski_bound_all_dims` simultaneously at every stage `j`! -/
theorem chain_hermitian_minkowski_bost_bridge {m k t : ℕ} (hk : 1 ≤ k)
    (L : ∀ j : Fin (m + 1), HermitianLattice (chainRank k t j.1)) :
    ∀ j : Fin (m + 1),
      let N := chainRank k t j.1
      have h2N : 0 < 2 * N := by unfold N chainRank; omega
      let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * N))) 1
      let ω := (MeasureTheory.volume B).toReal
      -- 1. Exact rank & covolume identification
      ArakelovCovolume.rk (L j).lat = 2 * N ∧
      ArakelovCovolume.covol (L j).lat = ZLattice.covolume (L j).realLat MeasureTheory.volume ∧
      -- 2. Unconditional Minkowski's Second Theorem Upper Bound
      (∏ i : Fin (2 * N), Stage10GeometryOfNumbers.successiveMinimum B (L j).realLat i) * ω ≤
        (2 : ℝ) ^ (2 * N) * ArakelovCovolume.covol (L j).lat ∧
      -- 3. Unconditional Hermite–Minkowski Bound in dimension 2 * N
      (Stage10GeometryOfNumbers.successiveMinimum B (L j).realLat ⟨0, h2N⟩) ^ 2 ≤
        (4 / ω ^ (2 / ((2 * N : ℕ) : ℝ))) *
          (ArakelovCovolume.covol (L j).lat) ^ (2 / ((2 * N : ℕ) : ℝ)) ∧
      -- 4. Unconditional Arakelov–Bost Slope & Maximal-Slope Equivalence
      ArakelovCovolume.slope (L j).lat ≤ ArakelovCovolume.muMax (L j).lat ∧
      -Real.log (Stage2SiegelReduction.lambda1 (L j).lat) ≤ ArakelovCovolume.muMax (L j).lat ∧
      ArakelovCovolume.muMax (L j).lat ≤
        -Real.log (Stage2SiegelReduction.lambda1 (L j).lat) + (1 / 2) * Real.log (2 * N : ℝ) := by
  intro j
  set N := chainRank k t j.1
  have hN : 0 < N := by unfold N chainRank; omega
  have h2N : 0 < 2 * N := by omega
  set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * N))) 1
  set ω := (MeasureTheory.volume B).toReal
  have hcov : ArakelovCovolume.covol (L j).lat = ZLattice.covolume (L j).realLat MeasureTheory.volume :=
    (L j).covol_eq_real_covolume
  have hrk : ArakelovCovolume.rk (L j).lat = 2 * N := (L j).rk_eq
  have hne : (L j).lat ≠ ⊥ := by
    intro hbot
    have hrk0 : ArakelovCovolume.rk (L j).lat = 0 := by
      rw [hbot]; unfold ArakelovCovolume.rk; simp
    omega
  have h0B : (0 : EuclideanSpace ℝ (Fin (2 * N))) ∈ interior B := by
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hmink := Stage10GeometryOfNumbers.minkowski_second_theorem_upper h2N
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (2 * N))) 1)
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    (isCompact_closedBall 0 1) h0B (L j).realLat
  have hherm := Stage10GeometryOfNumbers.hermite_minkowski_bound_all_dims h2N (L j).realLat
  have hmu_lo := Stage2SiegelReduction.neg_log_lambda1_le_muMax (L j).lat hne
  have hmu_hi := Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1 (L j).lat hne
  rw [hrk] at hmu_hi
  refine ⟨hrk, hcov, ?_, ?_,
    ArakelovCovolume.slope_le_muMax (L := (L j).lat) (N := (L j).lat) le_rfl hne, hmu_lo, ?_⟩
  · rwa [hcov]
  · rwa [hcov]
  · push_cast at hmu_hi; linarith

end TensorCovolumeAndMinkowskiBostBridge

end RHDirect.Stage11DefiniteUnitaryChain
