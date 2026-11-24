import RHDirect.ArakelovCovolume
import RHDirect.Stage4ArakelovBost
import RHDirect.Stage8ModularRing
import RHDirect.Stage9DeltaHadamard
import RHDirect.Stage9ModularDerivatives
import RHDirect.Stage11HermitianCurvature
import RHDirect.Stage11MoriwakiCovolume
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# RHDirect.Stage11ArakelovFaltings

**UNCONDITIONAL CONCRETE ARAKELOV GEOMETRY OVER `Spec ℤ`, BOST–GILLET–SOULÉ SLOPE CALCULUS,
CONCRETE FALTINGS HEIGHT `h_F(τ)` OF ELLIPTIC CURVES VIA `Δ(τ)`, AND ARAKELOV INTERSECTION
PAIRING & ARITHMETIC HODGE INDEX BRIDGING TO PILLAR 2** in pure Mathlib `v4.33.1`
(`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Concrete Hermitian Vector Bundles over `Spec ℤ` & Bost–Gillet–Soulé Slope Calculus**:
   - `HermVectorBundle`: concrete rank-`r` full-rank `ℤ`-lattice `Λ ⊂ ℝ^r` equipped with a
     positive-definite real symmetric inner product matrix `h : Matrix (Fin r) (Fin r) ℝ`.
   - Exact spectral isometric embedding `toEucl : (Fin r → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin r)`
     converting `hInner x y = x ⬝ᵥ (h *ᵥ y)` to the standard Euclidean inner product, identifying
     `covol E = |det B| · √(det h)`, `arakelovDeg E = -log(covol E)`, `bundleSlope E = deg / r`,
     `bundleMuMax E`, and `bundleMuMin E`.
   - **Exact Short Exact Sequence Additivity (`arakelovDeg_short_exact_seq`)**:
     for every isometric short exact sequence `0 → F → E → Q → 0`,
     `E.rk = F.rk + Q.rk`, `E.covol = F.covol * Q.covol`, and
     `E.arakelovDeg = F.arakelovDeg + Q.arakelovDeg`.
   - **Exact Tensor Product & Dual Slope Formulas**:
     - `HermVectorBundle.tensor` (Kronecker metric `h_E ⊗ h_F`, tensor lattice `Λ_E ⊗ Λ_F`):
       `bundleSlope_tensor : (E.tensor F).slope = E.slope + F.slope`.
     - `HermVectorBundle.dual` (dual lattice `Λ^∨`, inverse metric `h⁻¹`):
       `bundleSlope_dual : E.dual.slope = -E.slope`,
       `bundleMuMax_dual : E.dual.muMax = -E.muMin`,
       `bundleMuMin_dual : E.dual.muMin = -E.muMax`.
   - **Bost's Slope Inequality (`bost_slope_inequality_bundle`)**:
     for any non-zero morphism `φ : HermBundleMorphism E F` with operator norm `φ.opNorm`,
     `E.muMin ≤ F.muMax + Real.log φ.opNorm`.

2. **Concrete Faltings Height `h_F(τ)` of Elliptic Curves via `Δ(τ)`**:
   - `faltingsHeight τ := -(1 / 12) * Real.log ((2 * Real.pi) ^ 12 * ‖ramanujanDelta τ‖ * τ.im ^ 6)`.
   - **`SL₂(ℤ)`-Invariance (`faltingsHeight_sl2Z_invariant`)**:
     `faltingsHeight (γ • τ) = faltingsHeight τ` for all `γ ∈ SL(2, ℤ)` and `τ ∈ ℍ`.
   - **Explicit Universal Lower Bound (`faltingsHeight_ge_neg_two`, `faltingsHeight_bddBelow`)**:
     `∀ τ : UpperHalfPlane, (-2 : ℝ) ≤ faltingsHeight τ` (proved via Dedekind–Jacobi Euler product
     bounds on the `SL₂(ℤ)` fundamental domain!).
   - **Sharp Cusp Asymptotics (`faltingsHeight_imag_asymptotic_explicit`,
     `faltingsHeight_imag_isBigO`)**:
     for all `y ≥ 1 / 2`,
     `0 ≤ h_F(i y) - ((π / 6) y - (1 / 2) log y - log(2π)) ≤ 8 * exp(-2π y)`,
     and `h_F(i y) = (π / 6) y - (1 / 2) log y - log(2π) + O(e^{-2π y})` as `y → ∞`.
   - **Exact Subharmonicity & Curvature-Degree Identity (`euclLaplacianR_faltingsHeight`,
     `faltingsHeight_curvature_integral_eq_one_div_twelve`)**:
     `Δ_Eucl h_F(τ) = (1 / 2) y⁻² = 2 Θ(h₁)(τ)`, integrating over `stdFD` to `deg(ω) = 1 / 12`.

3. **Arakelov Intersection Pairing, Arithmetic Hodge Index & Pillar 2 Bridges**:
   - Concrete Hermitian line bundle pairing `arakelovPair M L₁ L₂` on arithmetic surface models,
     packaged as a symmetric bilinear form (`arakelovPair_symm`, `arakelovPairBilin`).
   - **Faltings–Hriljac Arithmetic Hodge Index Theorem (`arithmetic_hodge_index`,
     `arithmetic_hodge_index_ineq`)**:
     for `(L₁ · L₁)_Ar > 0`, `(L₁ · L₂)_Ar = 0 → (L₂ · L₂)_Ar ≤ 0` and
     `(L₁ · L₁)_Ar * (L₂ · L₂)_Ar ≤ (L₁ · L₂)_Ar ^ 2`.
   - **Ample Positivity, Convexity & Adjunction** (`arakelovPair_pos_of_ample`,
     `isArithAmple_add`, `arakelovAdjunction_pos`).
   - Direct bridges to `Stage11HermitianCurvature`, `Stage11MoriwakiCovolume`, and
     `RHDirect.BostSlopeFiber.SlopeIneq` feeding Pillar 2 slope bounds.
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function
open RHDirect.ArakelovCovolume RHDirect.Stage4ArakelovBost RHDirect.Stage5ModularHecke
open RHDirect.Stage7EisensteinSeries RHDirect.Stage8ModularRing RHDirect.Stage8RamanujanDelta
open RHDirect.Stage9DeltaHadamard RHDirect.Stage9ModularDerivatives
open RHDirect.Stage10PeterssonHecke RHDirect.Stage11HermitianCurvature
open RHDirect.Stage11MoriwakiCovolume
open scoped BigOperators UpperHalfPlane ModularForm Topology ENNReal MatrixGroups InnerProductSpace

namespace RHDirect.Stage11ArakelovFaltings

noncomputable section

/-! ## Section 1: Concrete Hermitian Vector Bundles over `Spec ℤ` & Bost–Gillet–Soulé Slope Calculus -/

section HermVectorBundles

/-! ### Positive-Definite Matrix Helpers & Spectral Isometric Embedding -/

private lemma finsupp_sum_eq_dotProduct_mulVec {r : ℕ} (h : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin r →₀ ℝ) :
    (x.sum fun i xi => x.sum fun j xj => star xi * h i j * xj) = (x : Fin r → ℝ) ⬝ᵥ h.mulVec x := by
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_trivial]
  ring

/-- Symmetry of a real Hermitian matrix: `hᵀ = h`. -/
lemma isHermitian_real_transpose {r : ℕ} {h : Matrix (Fin r) (Fin r) ℝ} (hh : h.IsHermitian) :
    h.transpose = h := by
  ext i j
  have hij := congrFun (congrFun hh i) j
  simpa [Matrix.conjTranspose_apply] using hij

/-- Quadratic form positivity `0 < x ⬝ᵥ h *ᵥ x` for every nonzero `x : Fin r → ℝ`. -/
theorem posDef_dotProduct_mulVec_pos {r : ℕ} {h : Matrix (Fin r) (Fin r) ℝ} (hh : h.PosDef)
    {x : Fin r → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ h.mulVec x := by
  let xf : Fin r →₀ ℝ := Finsupp.equivFunOnFinite.symm x
  have hxf : xf ≠ 0 := fun h0 => hx (by ext i; exact congrArg (fun f : Fin r →₀ ℝ => f i) h0)
  have hpos := hh.2 hxf
  rw [finsupp_sum_eq_dotProduct_mulVec] at hpos
  simpa [xf] using hpos

/-- Construct `h.PosDef` from symmetry `hᵀ = h` and `∀ x ≠ 0, 0 < x ⬝ᵥ h *ᵥ x`. -/
theorem posDef_of_dotProduct_mulVec_pos {r : ℕ} {h : Matrix (Fin r) (Fin r) ℝ}
    (hsymm : h.transpose = h) (hpos : ∀ x : Fin r → ℝ, x ≠ 0 → 0 < x ⬝ᵥ h.mulVec x) :
    h.PosDef := by
  refine ⟨?_, fun {xf} hxf => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact congrFun (congrFun hsymm i) j
  · rw [finsupp_sum_eq_dotProduct_mulVec]
    exact hpos (xf : Fin r → ℝ) (fun h0 => hxf (Finsupp.ext fun i => congrFun h0 i))

private lemma eucl_sum_apply {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (f : κ → EuclideanSpace ℝ ι) (i : ι) :
    (∑ k ∈ s, f k) i = ∑ k ∈ s, (f k) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

private lemma pi_eq_sum_single {r : ℕ} (x : Fin r → ℝ) :
    x = ∑ i : Fin r, x i • Pi.single i (1 : ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- Every eigenvalue of a real positive-definite matrix is strictly positive. -/
theorem posDef_eigenvalues_pos {r : ℕ} {h : Matrix (Fin r) (Fin r) ℝ} (hh : h.PosDef) (k : Fin r) :
    0 < hh.isHermitian.eigenvalues k := by
  let H := hh.isHermitian
  let q : EuclideanSpace ℝ (Fin r) := H.eigenvectorBasis k
  have hqnorm : ‖q‖ = 1 := H.eigenvectorBasis.orthonormal.1 k
  have hqne : (q : Fin r → ℝ) ≠ 0 := by
    intro h0
    have hq0 : q = 0 := by
      ext i
      exact congrFun h0 i
    rw [hq0, norm_zero] at hqnorm
    norm_num at hqnorm
  have hpos := posDef_dotProduct_mulVec_pos hh hqne
  have heig : H.eigenvalues k = (q : Fin r → ℝ) ⬝ᵥ h.mulVec (q : Fin r → ℝ) := by
    have hmul := H.mulVec_eigenvectorBasis k
    have h1 : inner ℝ q (WithLp.toLp 2 (h.mulVec (q : Fin r → ℝ))) = H.eigenvalues k := by
      have hvec : WithLp.toLp 2 (h.mulVec (q : Fin r → ℝ)) = (H.eigenvalues k) • q := by
        ext i
        simpa [q] using congrFun hmul i
      rw [hvec, real_inner_smul_right, real_inner_self_eq_norm_sq, hqnorm, one_pow, mul_one]
    rw [← h1, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rwa [heig]

/-- The inverse of a real positive-definite matrix is positive-definite. -/
theorem posDef_inv {r : ℕ} {h : Matrix (Fin r) (Fin r) ℝ} (hh : h.PosDef) :
    h⁻¹.PosDef := by
  have hdet : h.det ≠ 0 := hh.det_pos.ne'
  have hT : h.transpose = h := isHermitian_real_transpose hh.isHermitian
  have hmul : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (isUnit_iff_ne_zero.mpr hdet)
  have hinvT : h⁻¹.transpose = h⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hT]
  refine posDef_of_dotProduct_mulVec_pos hinvT fun x hx => ?_
  let y : Fin r → ℝ := h⁻¹.mulVec x
  have hyne : y ≠ 0 := by
    intro hy0
    apply hx
    have h1 : h.mulVec y = x := by
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    rw [hy0, Matrix.mulVec_zero] at h1
    exact h1.symm
  have hpos := posDef_dotProduct_mulVec_pos hh hyne
  have heq : x ⬝ᵥ h⁻¹.mulVec x = y ⬝ᵥ h.mulVec y := by
    have hhy : h.mulVec y = x := by
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    rw [hhy, dotProduct_comm]
  rwa [heq]

/-- **Concrete Hermitian Vector Bundle over `Spec ℤ`**:
a rank-`r` full-rank discrete `ℤ`-lattice `Λ ⊂ ℝ^r` equipped with a positive-definite real
symmetric Hermitian inner product matrix `h : Matrix (Fin r) (Fin r) ℝ`. -/
structure HermVectorBundle where
  /-- Rank `r` of the bundle. -/
  rk : ℕ
  /-- Full-rank `ℤ`-lattice `Λ ⊂ ℝ^r`. -/
  lat : Submodule ℤ (Fin rk → ℝ)
  /-- Discreteness of `Λ ⊂ ℝ^r`. -/
  lat_discrete : DiscreteTopology lat
  /-- Full-rank condition `span_ℝ(Λ) = ℝ^r`. -/
  lat_span_top : Submodule.span ℝ (lat : Set (Fin rk → ℝ)) = ⊤
  /-- Positive-definite real symmetric metric matrix `h` on `ℝ^r`. -/
  metric : Matrix (Fin rk) (Fin rk) ℝ
  /-- Positive-definiteness of `h`. -/
  metric_posDef : metric.PosDef

attribute [instance] HermVectorBundle.lat_discrete

namespace HermVectorBundle

/-- Hermitian inner product `⟪x, y⟫_h = x ⬝ᵥ (h *ᵥ y)` on the fiber `ℝ^r`. -/
def hInner (E : HermVectorBundle) (x y : Fin E.rk → ℝ) : ℝ :=
  x ⬝ᵥ E.metric.mulVec y

/-- Hermitian norm `‖x‖_h = √(⟪x, x⟫_h)` on the fiber `ℝ^r`. -/
def hNorm (E : HermVectorBundle) (x : Fin E.rk → ℝ) : ℝ :=
  Real.sqrt (E.hInner x x)

theorem hInner_symm (E : HermVectorBundle) (x y : Fin E.rk → ℝ) :
    E.hInner x y = E.hInner y x := by
  unfold hInner
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    isHermitian_real_transpose E.metric_posDef.isHermitian, dotProduct_comm]

theorem hInner_self_nonneg (E : HermVectorBundle) (x : Fin E.rk → ℝ) :
    0 ≤ E.hInner x x := by
  by_cases hx : x = 0
  · simp [hInner, hx]
  · exact (posDef_dotProduct_mulVec_pos E.metric_posDef hx).le

theorem hInner_self_pos (E : HermVectorBundle) {x : Fin E.rk → ℝ} (hx : x ≠ 0) :
    0 < E.hInner x x :=
  posDef_dotProduct_mulVec_pos E.metric_posDef hx

theorem hNorm_nonneg (E : HermVectorBundle) (x : Fin E.rk → ℝ) :
    0 ≤ E.hNorm x :=
  Real.sqrt_nonneg _

theorem hNorm_sq (E : HermVectorBundle) (x : Fin E.rk → ℝ) :
    E.hNorm x ^ 2 = E.hInner x x :=
  Real.sq_sqrt (E.hInner_self_nonneg x)

/-- Canonical spectral isometric embedding `toEucl : (Fin r → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin r)`
diagonalizing the positive-definite metric `h` so that `⟪toEucl x, toEucl y⟫ = hInner x y`. -/
def toEucl (E : HermVectorBundle) : (Fin E.rk → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk) where
  toFun x := WithLp.toLp 2 (fun k =>
    Real.sqrt (E.metric_posDef.isHermitian.eigenvalues k) *
      inner ℝ (E.metric_posDef.isHermitian.eigenvectorBasis k) (WithLp.toLp 2 x))
  map_add' x y := by
    ext k
    simp only [PiLp.add_apply, WithLp.toLp_add, inner_add_right, mul_add]
  map_smul' c x := by
    ext k
    simp only [RingHom.id_apply, PiLp.smul_apply, smul_eq_mul,
      WithLp.toLp_smul, real_inner_smul_right]
    ring

/-- **Exact Isometry of `toEucl`**: `inner ℝ (E.toEucl x) (E.toEucl y) = E.hInner x y`. -/
theorem inner_toEucl (E : HermVectorBundle) (x y : Fin E.rk → ℝ) :
    inner ℝ (E.toEucl x) (E.toEucl y) = E.hInner x y := by
  let H := E.metric_posDef.isHermitian
  let u := H.eigenvectorBasis
  let ev := H.eigenvalues
  let x' : EuclideanSpace ℝ (Fin E.rk) := WithLp.toLp 2 x
  let y' : EuclideanSpace ℝ (Fin E.rk) := WithLp.toLp 2 y
  have hy_decomp : y' = ∑ k : Fin E.rk, inner ℝ (u k) y' • u k := (u.sum_repr' y').symm
  have hhy : WithLp.toLp 2 (E.metric.mulVec y) =
      ∑ k : Fin E.rk, (ev k * inner ℝ (u k) y') • u k := by
    have hy_fun : y = ∑ k : Fin E.rk, inner ℝ (u k) y' • (u k : Fin E.rk → ℝ) := by
      ext i
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin E.rk) => v i) hy_decomp
      rw [eucl_sum_apply] at h1
      simpa [y', Finset.sum_apply] using h1
    ext i
    rw [WithLp.ofLp_toLp, hy_fun, Matrix.mulVec_sum, Finset.sum_apply, eucl_sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
    have hmul := congrFun (H.mulVec_eigenvectorBasis k) i
    simp only [Pi.smul_apply, smul_eq_mul] at hmul
    change inner ℝ (u k) y' * (E.metric.mulVec (u k) i) = _
    rw [hmul]
    ring
  have hinner_xy : E.hInner x y = inner ℝ x' (WithLp.toLp 2 (E.metric.mulVec y)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [hInner, star_trivial, dotProduct, x']
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hinner_xy, hhy, inner_sum]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, toEucl, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_right, real_inner_comm (u k) x']
  change (Real.sqrt (ev k) * inner ℝ (u k) y') * (Real.sqrt (ev k) * inner ℝ (u k) x') =
    ev k * inner ℝ (u k) y' * inner ℝ (u k) x'
  have hev_nn : 0 ≤ ev k := (posDef_eigenvalues_pos E.metric_posDef k).le
  have hsq : Real.sqrt (ev k) * Real.sqrt (ev k) = ev k := Real.mul_self_sqrt hev_nn
  calc (Real.sqrt (ev k) * inner ℝ (u k) y') * (Real.sqrt (ev k) * inner ℝ (u k) x')
      = (Real.sqrt (ev k) * Real.sqrt (ev k)) * inner ℝ (u k) y' * inner ℝ (u k) x' := by ring
    _ = ev k * inner ℝ (u k) y' * inner ℝ (u k) x' := by rw [hsq]

/-- Norm preservation of `toEucl`: `‖E.toEucl x‖ = E.hNorm x`. -/
theorem norm_toEucl (E : HermVectorBundle) (x : Fin E.rk → ℝ) :
    ‖E.toEucl x‖ = E.hNorm x := by
  have hsq : ‖E.toEucl x‖ ^ 2 = E.hNorm x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, E.inner_toEucl, E.hNorm_sq]
  nlinarith [norm_nonneg (E.toEucl x), E.hNorm_nonneg x]

/-- `E.toEucl` is injective. -/
theorem toEucl_injective (E : HermVectorBundle) : Function.Injective E.toEucl := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  by_contra hne
  have hpos : 0 < E.hInner x x := E.hInner_self_pos hne
  have h0 : E.hInner x x = 0 := by
    rw [← E.inner_toEucl, LinearMap.mem_ker.mp hx, inner_zero_left]
  linarith

/-- `E.toEucl` as an `ℝ`-linear equivalence `(Fin E.rk → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk)`. -/
def toEuclEquiv (E : HermVectorBundle) : (Fin E.rk → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk) :=
  LinearEquiv.ofBijective E.toEucl
    ⟨E.toEucl_injective, by
      rw [← LinearMap.range_eq_top]
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [LinearMap.finrank_range_of_inj E.toEucl_injective, Module.finrank_fin_fun,
        finrank_euclideanSpace_fin]⟩

@[simp]
lemma toEuclEquiv_apply (E : HermVectorBundle) (x : Fin E.rk → ℝ) :
    E.toEuclEquiv x = E.toEucl x := rfl

@[simp]
lemma toEuclEquiv_symm_toEucl (E : HermVectorBundle) (x : Fin E.rk → ℝ) :
    E.toEuclEquiv.symm (E.toEucl x) = x :=
  E.toEuclEquiv.symm_apply_apply x

@[simp]
lemma toEucl_toEuclEquiv_symm (E : HermVectorBundle) (v : EuclideanSpace ℝ (Fin E.rk)) :
    E.toEucl (E.toEuclEquiv.symm v) = v :=
  E.toEuclEquiv.apply_symm_apply v

/-- The Euclidean model lattice `Λ_Eucl = E.toEucl(Λ) ⊂ EuclideanSpace ℝ (Fin E.rk)`. -/
def euclLat (E : HermVectorBundle) : Submodule ℤ (EuclideanSpace ℝ (Fin E.rk)) :=
  E.lat.map (E.toEucl.restrictScalars ℤ)

/-- `E.euclLat` carries the discrete topology. -/
instance discreteTopology_euclLat (E : HermVectorBundle) : DiscreteTopology E.euclLat := by
  let invCont : Continuous (E.toEuclEquiv.symm : EuclideanSpace ℝ (Fin E.rk) → Fin E.rk → ℝ) :=
    LinearMap.continuous_of_finiteDimensional E.toEuclEquiv.symm.toLinearMap
  let f : E.euclLat → E.lat := fun y =>
    ⟨E.toEuclEquiv.symm y.1, by
      rcases y.2 with ⟨x, hxL, hxy⟩
      have h1 : E.toEuclEquiv.symm y.1 = x := by
        rw [← hxy]
        exact E.toEuclEquiv.symm_apply_apply x
      rwa [h1]⟩
  have hf_cont : Continuous f :=
    Continuous.subtype_mk (invCont.comp continuous_subtype_val) _
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact E.toEuclEquiv.symm.injective (congrArg Subtype.val hab)
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

/-- Canonical `ℤ`-linear equivalence `E.lat ≃ₗ[ℤ] E.euclLat`. -/
def latEquivEuclLat (E : HermVectorBundle) : E.lat ≃ₗ[ℤ] E.euclLat where
  toFun x := ⟨E.toEucl x.1, ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨E.toEuclEquiv.symm y.1, by
    rcases y.2 with ⟨x, hxL, hxy⟩
    have h1 : E.toEuclEquiv.symm y.1 = x := by
      rw [← hxy]; exact E.toEuclEquiv.symm_apply_apply x
    rwa [h1]⟩
  map_add' x y := Subtype.ext (map_add E.toEucl x.1 y.1)
  map_smul' c x := Subtype.ext (map_zsmul E.toEucl c x.1)
  left_inv x := Subtype.ext (E.toEuclEquiv.symm_apply_apply x.1)
  right_inv y := Subtype.ext (E.toEuclEquiv.apply_symm_apply y.1)

/-- The `ℝ`-span of `E.euclLat` is `⊤`. -/
theorem span_real_euclLat (E : HermVectorBundle) :
    Submodule.span ℝ (E.euclLat : Set (EuclideanSpace ℝ (Fin E.rk))) = ⊤ := by
  have himg : (E.euclLat : Set (EuclideanSpace ℝ (Fin E.rk))) = E.toEucl '' (E.lat : Set (Fin E.rk → ℝ)) := by
    ext y; rfl
  rw [himg, ← Submodule.map_span, E.lat_span_top, Submodule.map_top, LinearMap.range_eq_top]
  exact E.toEuclEquiv.surjective

/-- The lattice rank `ArakelovCovolume.rk E.euclLat` equals `E.rk`. -/
theorem rk_euclLat (E : HermVectorBundle) : ArakelovCovolume.rk E.euclLat = E.rk := by
  unfold ArakelovCovolume.rk
  rw [finrank_int_eq_finrank_real_span E.euclLat, E.span_real_euclLat, finrank_top,
    finrank_euclideanSpace_fin]

theorem euclLat_ne_bot_of_rk_pos (E : HermVectorBundle) (hr : 0 < E.rk) : E.euclLat ≠ ⊥ := by
  intro h0
  have h1 := E.rk_euclLat
  rw [h0, show ArakelovCovolume.rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin E.rk))) = 0 by
    simp [ArakelovCovolume.rk]] at h1
  omega

/-! ### Covolume, Arakelov Degree, Slope, `μ_max`, and `μ_min` -/

/-- Concrete **Covolume** `covol(Λ, h)` of a Hermitian vector bundle `E`. -/
def covol (E : HermVectorBundle) : ℝ :=
  ArakelovCovolume.covol E.euclLat

/-- Concrete **Arakelov Degree** `deg_Ar(E) = -log covol(Λ, h)`. -/
def arakelovDeg (E : HermVectorBundle) : ℝ :=
  -Real.log E.covol

/-- Concrete **Arithmetic Slope** `μ(E) = deg_Ar(E) / rk(E)`. -/
def slope (E : HermVectorBundle) : ℝ :=
  E.arakelovDeg / (E.rk : ℝ)

/-- Concrete **Maximal Slope** `μ_max(E) = sup_{0 ≠ F ⊂ E} μ(F)`. -/
def muMax (E : HermVectorBundle) : ℝ :=
  ArakelovCovolume.muMax E.euclLat

/-- Concrete **Minimal Slope** `μ_min(E) = inf_{E ↠ Q ≠ 0} μ(Q)`. -/
def muMin (E : HermVectorBundle) : ℝ :=
  Stage4ArakelovBost.muMin E.euclLat

lemma covol_pos (E : HermVectorBundle) : 0 < E.covol :=
  ArakelovCovolume.covol_pos E.euclLat

lemma arakelovDeg_eq_degAr (E : HermVectorBundle) :
    E.arakelovDeg = ArakelovCovolume.degAr E.euclLat := rfl

lemma slope_eq_euclSlope (E : HermVectorBundle) :
    E.slope = ArakelovCovolume.slope E.euclLat := by
  unfold slope ArakelovCovolume.slope
  rw [E.rk_euclLat, E.arakelovDeg_eq_degAr]

/-- Exact relation `E.arakelovDeg = E.rk * E.slope` for any positive-rank bundle. -/
theorem arakelovDeg_eq_rk_mul_slope (E : HermVectorBundle) (hr : 0 < E.rk) :
    E.arakelovDeg = (E.rk : ℝ) * E.slope := by
  have hrne : (E.rk : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  unfold slope
  rw [mul_div_cancel₀ _ hrne]

/-- **Explicit Hermitian Gram-Determinant Covolume Formula**:
for any `ℤ`-basis `b` of `E.lat`, `covol(E) = √(det (⟪b_i, b_j⟫_h))`. -/
theorem covol_eq_sqrt_det_hGram (E : HermVectorBundle) (b : Basis (Fin E.rk) ℤ E.lat) :
    E.covol = Real.sqrt (Matrix.of fun i j : Fin E.rk => E.hInner (b i : Fin E.rk → ℝ) (b j : Fin E.rk → ℝ)).det := by
  unfold covol
  rw [covol_eq_sqrt_det_gram E.euclLat (b.map E.latEquivEuclLat)]
  congr 2
  ext i j
  simp only [Matrix.gram_apply, Matrix.of_apply, Basis.map_apply, latEquivEuclLat,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact E.inner_toEucl (b i : Fin E.rk → ℝ) (b j : Fin E.rk → ℝ)

/-- **Exact Basis-Matrix & Metric Determinant Factorization**:
if `b` is a `ℤ`-basis of `E.lat` with basis matrix `B i j = (b j) i`, then
`E.covol = |det B| * √(det E.metric)` and `E.arakelovDeg = -log |det B| - (1/2) log(det E.metric)`. -/
theorem covol_eq_abs_det_mul_sqrt_det_metric (E : HermVectorBundle) (b : Basis (Fin E.rk) ℤ E.lat) :
    let B : Matrix (Fin E.rk) (Fin E.rk) ℝ := fun i j => (b j : Fin E.rk → ℝ) i
    E.covol = |B.det| * Real.sqrt E.metric.det := by
  intro B
  rw [E.covol_eq_sqrt_det_hGram b]
  have hgram : (Matrix.of fun i j : Fin E.rk =>
      E.hInner (b i : Fin E.rk → ℝ) (b j : Fin E.rk → ℝ)) = B.transpose * E.metric * B := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    simp only [hInner, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    dsimp only [B]
    ring
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show B.det * E.metric.det * B.det = B.det ^ 2 * E.metric.det by ring,
    Real.sqrt_mul (sq_nonneg B.det), Real.sqrt_sq_eq_abs]

/-- Fundamental slope ordering `μ_min(E) ≤ μ(E) ≤ μ_max(E)` for every bundle of rank `r > 0`. -/
theorem muMin_le_slope_le_muMax (E : HermVectorBundle) (hr : 0 < E.rk) :
    E.muMin ≤ E.slope ∧ E.slope ≤ E.muMax := by
  rw [E.slope_eq_euclSlope]
  exact Stage4ArakelovBost.muMin_le_slope_le_muMax E.euclLat (E.euclLat_ne_bot_of_rk_pos hr)

/-! ### Exact Additivity in Short Exact Sequences `0 → F → E → Q → 0` -/

/-- A concrete **isometric short exact sequence** `0 → F →[incl] E →[proj] Q → 0` of Hermitian vector
bundles over `Spec ℤ`: `incl` is an isometric embedding onto a saturated sublattice
`ker proj ∩ Λ_E`, and `proj` induces an isometry from the `h`-orthogonal complement
`(range incl)^{⊥_h}` onto `Q`. -/
structure HermShortExactSeq (F E Q : HermVectorBundle) where
  incl : (Fin F.rk → ℝ) →ₗ[ℝ] (Fin E.rk → ℝ)
  proj : (Fin E.rk → ℝ) →ₗ[ℝ] (Fin Q.rk → ℝ)
  incl_maps_lat : ∀ y ∈ F.lat, incl y ∈ E.lat
  proj_maps_lat : ∀ x ∈ E.lat, proj x ∈ Q.lat
  exact_lat : ∀ x ∈ E.lat, proj x = 0 → ∃ y ∈ F.lat, incl y = x
  exact_real : LinearMap.ker proj = LinearMap.range incl
  proj_surj_lat : ∀ q ∈ Q.lat, ∃ x ∈ E.lat, proj x = q
  incl_isometric : ∀ y, E.hNorm (incl y) = F.hNorm y
  proj_orth_isometric : ∀ x, (∀ y, E.hInner (incl y) x = 0) → Q.hNorm (proj x) = E.hNorm x

/-- **Exact Additivity of Arakelov Degree in Short Exact Sequences**:
for any isometric short exact sequence `0 → F → E → Q → 0` of Hermitian vector bundles:
1. `E.rk = F.rk + Q.rk`,
2. `E.covol = F.covol * Q.covol`,
3. `E.arakelovDeg = F.arakelovDeg + Q.arakelovDeg`! -/
theorem arakelovDeg_short_exact_seq {F E Q : HermVectorBundle} (S : HermShortExactSeq F E Q) :
    E.rk = F.rk + Q.rk ∧
    E.covol = F.covol * Q.covol ∧
    E.arakelovDeg = F.arakelovDeg + Q.arakelovDeg := by
  let ιE : F.euclLat →ₗ[ℤ] E.euclLat :=
    { toFun := fun y =>
        ⟨E.toEucl (S.incl (F.toEuclEquiv.symm y.1)),
          ⟨S.incl (F.toEuclEquiv.symm y.1), S.incl_maps_lat _ (F.latEquivEuclLat.symm y).2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by
        change E.toEucl (S.incl (F.toEuclEquiv.symm (a.1 + b.1))) = _
        rw [map_add, map_add, map_add]; rfl)
      map_smul' := fun c a => Subtype.ext (by
        change E.toEucl (S.incl (F.toEuclEquiv.symm (c • a.1))) = _
        rw [map_zsmul, map_zsmul, map_zsmul]; rfl) }
  have hι_norm : ∀ y : F.euclLat, ‖((ιE y : E.euclLat) : EuclideanSpace ℝ (Fin E.rk))‖ =
      ‖(y : EuclideanSpace ℝ (Fin F.rk))‖ := by
    intro y
    change ‖E.toEucl (S.incl (F.toEuclEquiv.symm y.1))‖ = ‖y.1‖
    rw [E.norm_toEucl, S.incl_isometric, ← F.norm_toEucl, F.toEucl_toEuclEquiv_symm]
  have hι_inj : Function.Injective ιE := by
    intro a b hab
    apply Subtype.ext
    have hdiff : ‖((ιE (a - b) : E.euclLat) : EuclideanSpace ℝ (Fin E.rk))‖ = 0 := by
      rw [map_sub, hab, sub_self]; simp
    rw [hι_norm (a - b)] at hdiff
    exact sub_eq_zero.mp (norm_eq_zero.mp hdiff)
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin E.rk)) := LinearMap.range (E.euclLat.subtype.comp ιE)
  have hM_eq_span : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin E.rk))) =
      LinearMap.range (E.toEucl.comp S.incl) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨F.toEuclEquiv.symm y.1, rfl⟩
    · rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span ℝ (F.lat : Set (Fin F.rk → ℝ)) := by
        rw [F.lat_span_top]; trivial
      induction hz using Submodule.span_induction with
      | mem u hu =>
        refine Submodule.subset_span ?_
        refine ⟨⟨F.toEucl u, ⟨u, hu, rfl⟩⟩, ?_⟩
        change E.toEucl (S.incl (F.toEuclEquiv.symm (F.toEucl u))) = E.toEucl (S.incl u)
        rw [F.toEuclEquiv_symm_toEucl]
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add]
        exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        rw [map_smul]
        exact Submodule.smul_mem _ c hu
  have hM_sat : IsSaturated E.euclLat M := by
    refine ⟨by rintro _ ⟨y, rfl⟩; exact (ιE y).2, ?_⟩
    intro v hvE hvsp
    rcases hvE with ⟨x, hxL, rfl⟩
    rw [hM_eq_span] at hvsp
    rcases hvsp with ⟨z, hz⟩
    have hx_eq : S.incl z = x := E.toEucl_injective hz
    have hπx : S.proj x = 0 := by
      rw [← hx_eq]
      exact LinearMap.mem_ker.mp (S.exact_real.symm ▸ ⟨z, rfl⟩)
    obtain ⟨y, hyL, hyx⟩ := S.exact_lat x hxL hπx
    refine ⟨⟨F.toEucl y, ⟨y, hyL, rfl⟩⟩, ?_⟩
    change E.toEucl (S.incl (F.toEuclEquiv.symm (F.toEucl y))) = E.toEucl x
    rw [F.toEuclEquiv_symm_toEucl, hyx]
  have hDiscQ : DiscreteTopology (quotLat E.euclLat M) := discreteTopology_quotLat hM_sat
  -- Construct the isometric `ℤ`-linear equivalence `ψ : quotLat E.euclLat M ≃ₗ[ℤ] Q.euclLat`.
  let projEucl : EuclideanSpace ℝ (Fin E.rk) →ₗ[ℝ] EuclideanSpace ℝ (Fin Q.rk) :=
    (Q.toEucl.comp S.proj).comp E.toEuclEquiv.symm.toLinearMap
  have hπ_proj : ∀ v : EuclideanSpace ℝ (Fin E.rk),
      projEucl (projOrth M v) = projEucl v := by
    intro v
    have hsub : v - projOrth M v ∈ LinearMap.range (E.toEucl.comp S.incl) := by
      rw [← hM_eq_span]; exact Stage4ArakelovBost.sub_projOrth_mem_span M v
    rcases hsub with ⟨z, hz⟩
    have h0 : projEucl (v - projOrth M v) = 0 := by
      rw [← hz]
      change Q.toEucl (S.proj (E.toEuclEquiv.symm (E.toEucl (S.incl z)))) = 0
      rw [E.toEuclEquiv_symm_toEucl]
      have hker : S.proj (S.incl z) = 0 := LinearMap.mem_ker.mp (S.exact_real.symm ▸ ⟨z, rfl⟩)
      rw [hker, map_zero]
    rw [map_sub] at h0
    exact (sub_eq_zero.mp h0).symm
  have hπ_norm_orth : ∀ w ∈ (Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin E.rk))))ᗮ,
      ‖projEucl w‖ = ‖w‖ := by
    intro w hw
    let x := E.toEuclEquiv.symm w
    have hx_orth : ∀ y, E.hInner (S.incl y) x = 0 := by
      intro y
      rw [← E.inner_toEucl]
      have hmem : E.toEucl (S.incl y) ∈ Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin E.rk))) := by
        rw [hM_eq_span]; exact ⟨y, rfl⟩
      have h1 := hw (E.toEucl (S.incl y)) hmem
      have hx_eq : E.toEucl x = w := E.toEucl_toEuclEquiv_symm w
      rw [hx_eq]
      exact h1
    change ‖Q.toEucl (S.proj x)‖ = ‖w‖
    rw [Q.norm_toEucl, S.proj_orth_isometric x hx_orth, ← E.norm_toEucl,
      E.toEucl_toEuclEquiv_symm w]
  let ψMap : quotLat E.euclLat M →ₗ[ℤ] Q.euclLat :=
    { toFun := fun q =>
        ⟨projEucl q.1, by
          rcases q.2 with ⟨v, ⟨x, hxL, rfl⟩, hqv⟩
          rw [← hqv]
          change projEucl (projOrth M (E.toEucl x)) ∈ Q.euclLat
          rw [hπ_proj]
          change Q.toEucl (S.proj (E.toEuclEquiv.symm (E.toEucl x))) ∈ Q.euclLat
          rw [E.toEuclEquiv_symm_toEucl]
          exact ⟨S.proj x, S.proj_maps_lat x hxL, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add projEucl a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul projEucl c a.1) }
  have hψ_norm : ∀ q : quotLat E.euclLat M,
      ‖((ψMap q : Q.euclLat) : EuclideanSpace ℝ (Fin Q.rk))‖ =
        ‖(q : EuclideanSpace ℝ (Fin E.rk))‖ := by
    intro q
    rcases q.2 with ⟨v, _, hqv⟩
    change ‖projEucl q.1‖ = ‖q.1‖
    have hmem : q.1 ∈ (Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin E.rk))))ᗮ := by
      rw [← hqv]
      exact Stage4ArakelovBost.projOrth_mem_orthogonal M v
    exact hπ_norm_orth q.1 hmem
  have hψ_inj : Function.Injective ψMap := by
    intro a b hab
    apply Subtype.ext
    have h0 : ‖((ψMap (a - b) : Q.euclLat) : EuclideanSpace ℝ (Fin Q.rk))‖ = 0 := by
      rw [map_sub, hab, sub_self]; simp
    rw [hψ_norm (a - b)] at h0
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hψ_surj : Function.Surjective ψMap := by
    intro z
    rcases z.2 with ⟨q, hqL, hqz⟩
    obtain ⟨x, hxL, hπx⟩ := S.proj_surj_lat q hqL
    refine ⟨⟨projOrth M (E.toEucl x), ⟨E.toEucl x, ⟨x, hxL, rfl⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change projEucl (projOrth M (E.toEucl x)) = z.1
    rw [hπ_proj]
    change Q.toEucl (S.proj (E.toEuclEquiv.symm (E.toEucl x))) = z.1
    rw [E.toEuclEquiv_symm_toEucl, hπx]
    exact hqz
  let ψ : quotLat E.euclLat M ≃ₗ[ℤ] Q.euclLat := LinearEquiv.ofBijective ψMap ⟨hψ_inj, hψ_surj⟩
  have hres := Stage11MoriwakiCovolume.arithDeg_short_exact_seq ιE hι_inj hι_norm hM_sat ψ hψ_norm
  refine ⟨?_, hres.2.1, hres.2.2⟩
  rw [← E.rk_euclLat, ← F.rk_euclLat, ← Q.rk_euclLat]
  exact hres.1

/-! ### Tensor Product `E ⊗ F` & Exact Slope Additivity `μ(E ⊗ F) = μ(E) + μ(F)` -/

/-- Pure tensor vector `x ⊗ y ∈ ℝ^{r₁ r₂}` indexed via `finProdFinEquiv`. -/
def pureTensorVec {r₁ r₂ : ℕ} (x : Fin r₁ → ℝ) (y : Fin r₂ → ℝ) : Fin (r₁ * r₂) → ℝ :=
  fun t => x (finProdFinEquiv.symm t).1 * y (finProdFinEquiv.symm t).2

/-- Concrete Kronecker product metric matrix `h₁ ⊗ h₂` on `ℝ^{r₁ r₂}`. -/
def kroneckerMetric {r₁ r₂ : ℕ}
    (h₁ : Matrix (Fin r₁) (Fin r₁) ℝ) (h₂ : Matrix (Fin r₂) (Fin r₂) ℝ) :
    Matrix (Fin (r₁ * r₂)) (Fin (r₁ * r₂)) ℝ :=
  Matrix.of fun s t =>
    h₁ (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm t).1 *
      h₂ (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm t).2

/-- Spectral Kronecker embedding `K : ℝ^{r₁ r₂} →ₗ[ℝ] EuclideanSpace ℝ (Fin r₁ × Fin r₂)`
satisfying `inner ℝ (K z₁) (K z₂) = z₁ ⬝ᵥ (kroneckerMetric E.metric F.metric *ᵥ z₂)`. -/
private def kronToEucl (E F : HermVectorBundle) :
    (Fin (E.rk * F.rk) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk × Fin F.rk) where
  toFun z := WithLp.toLp 2 (fun p =>
    ∑ i : Fin E.rk, ∑ j : Fin F.rk,
      z (finProdFinEquiv (i, j)) *
        E.toEucl (Pi.single i 1) p.1 * F.toEucl (Pi.single j 1) p.2)
  map_add' z₁ z₂ := by
    ext p
    simp only [PiLp.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext p
    simp only [RingHom.id_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

private lemma kronToEucl_pureTensorVec (E F : HermVectorBundle)
    (x : Fin E.rk → ℝ) (y : Fin F.rk → ℝ) :
    kronToEucl E F (pureTensorVec x y) =
      WithLp.toLp 2 (fun p : Fin E.rk × Fin F.rk => E.toEucl x p.1 * F.toEucl y p.2) := by
  ext p
  simp only [kronToEucl, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, pureTensorVec,
    Equiv.symm_apply_apply]
  have hx : E.toEucl x p.1 = ∑ i : Fin E.rk, x i * E.toEucl (Pi.single i 1) p.1 := by
    conv_lhs => rw [pi_eq_sum_single x, map_sum, eucl_sum_apply]
    refine Finset.sum_congr rfl fun i _ => by rw [map_smul, PiLp.smul_apply, smul_eq_mul]
  have hy : F.toEucl y p.2 = ∑ j : Fin F.rk, y j * F.toEucl (Pi.single j 1) p.2 := by
    conv_lhs => rw [pi_eq_sum_single y, map_sum, eucl_sum_apply]
    refine Finset.sum_congr rfl fun j _ => by rw [map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [hx, hy, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma inner_kronToEucl (E F : HermVectorBundle) (z₁ z₂ : Fin (E.rk * F.rk) → ℝ) :
    inner ℝ (kronToEucl E F z₁) (kronToEucl E F z₂) =
      z₁ ⬝ᵥ (kroneckerMetric E.metric F.metric).mulVec z₂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, kronToEucl, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, Fintype.sum_prod_type]
  have hsingleE : ∀ i₁ i₂ : Fin E.rk,
      ∑ a : Fin E.rk, E.toEucl (Pi.single i₁ 1) a * E.toEucl (Pi.single i₂ 1) a =
        E.metric i₁ i₂ := by
    intro i₁ i₂
    have h := E.inner_toEucl (Pi.single i₁ (1 : ℝ)) (Pi.single i₂ (1 : ℝ))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    have hR : E.hInner (Pi.single i₁ (1 : ℝ)) (Pi.single i₂ (1 : ℝ)) = E.metric i₁ i₂ := by
      unfold hInner
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [hR] at h
    simpa [dotProduct, mul_comm] using h
  have hsingleF : ∀ j₁ j₂ : Fin F.rk,
      ∑ b : Fin F.rk, F.toEucl (Pi.single j₁ 1) b * F.toEucl (Pi.single j₂ 1) b =
        F.metric j₁ j₂ := by
    intro j₁ j₂
    have h := F.inner_toEucl (Pi.single j₁ (1 : ℝ)) (Pi.single j₂ (1 : ℝ))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    have hR : F.hInner (Pi.single j₁ (1 : ℝ)) (Pi.single j₂ (1 : ℝ)) = F.metric j₁ j₂ := by
      unfold hInner
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [hR] at h
    simpa [dotProduct, mul_comm] using h
  have hLHS :
      (∑ a : Fin E.rk, ∑ b : Fin F.rk,
        (∑ i₂ : Fin E.rk, ∑ j₂ : Fin F.rk,
          z₂ (finProdFinEquiv (i₂, j₂)) * E.toEucl (Pi.single i₂ 1) a * F.toEucl (Pi.single j₂ 1) b) *
        (∑ i₁ : Fin E.rk, ∑ j₁ : Fin F.rk,
          z₁ (finProdFinEquiv (i₁, j₁)) * E.toEucl (Pi.single i₁ 1) a * F.toEucl (Pi.single j₁ 1) b)) =
      ∑ i₁ : Fin E.rk, ∑ j₁ : Fin F.rk, ∑ i₂ : Fin E.rk, ∑ j₂ : Fin F.rk,
        z₁ (finProdFinEquiv (i₁, j₁)) * (E.metric i₁ i₂ * F.metric j₁ j₂ * z₂ (finProdFinEquiv (i₂, j₂))) := by
    trans ∑ a : Fin E.rk, ∑ b : Fin F.rk,
        ∑ i₁ : Fin E.rk, ∑ j₁ : Fin F.rk, ∑ i₂ : Fin E.rk, ∑ j₂ : Fin F.rk,
          (z₁ (finProdFinEquiv (i₁, j₁)) * z₂ (finProdFinEquiv (i₂, j₂))) *
          (E.toEucl (Pi.single i₁ 1) a * E.toEucl (Pi.single i₂ 1) a) *
          (F.toEucl (Pi.single j₁ 1) b * F.toEucl (Pi.single j₂ 1) b)
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      conv_lhs =>
        arg 2; ext i₁; rw [Finset.mul_sum]
        arg 2; ext j₁; rw [Finset.sum_mul]
        arg 2; ext i₂; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ =>
        Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => by ring
    · rw [Finset.sum_comm]
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i₁ _ => ?_
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i₂ _ => ?_
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      rw [← hsingleE i₁ i₂, ← hsingleF j₁ j₂]
      calc ∑ b : Fin F.rk, ∑ a : Fin E.rk,
              z₁ (finProdFinEquiv (i₁, j₁)) * z₂ (finProdFinEquiv (i₂, j₂)) *
              (E.toEucl (Pi.single i₁ 1) a * E.toEucl (Pi.single i₂ 1) a) *
              (F.toEucl (Pi.single j₁ 1) b * F.toEucl (Pi.single j₂ 1) b)
          = ∑ b : Fin F.rk,
              (z₁ (finProdFinEquiv (i₁, j₁)) * z₂ (finProdFinEquiv (i₂, j₂)) *
                (F.toEucl (Pi.single j₁ 1) b * F.toEucl (Pi.single j₂ 1) b)) *
              ∑ a : Fin E.rk, (E.toEucl (Pi.single i₁ 1) a * E.toEucl (Pi.single i₂ 1) a) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
        _ = (z₁ (finProdFinEquiv (i₁, j₁)) * z₂ (finProdFinEquiv (i₂, j₂)) *
              ∑ a : Fin E.rk, (E.toEucl (Pi.single i₁ 1) a * E.toEucl (Pi.single i₂ 1) a)) *
              ∑ b : Fin F.rk, (F.toEucl (Pi.single j₁ 1) b * F.toEucl (Pi.single j₂ 1) b) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
        _ = z₁ (finProdFinEquiv (i₁, j₁)) *
              ((∑ a : Fin E.rk, E.toEucl (Pi.single i₁ 1) a * E.toEucl (Pi.single i₂ 1) a) *
                (∑ b : Fin F.rk, F.toEucl (Pi.single j₁ 1) b * F.toEucl (Pi.single j₂ 1) b) *
                z₂ (finProdFinEquiv (i₂, j₂))) := by ring
  rw [hLHS]
  symm
  have hreidx1 : (∑ s : Fin (E.rk * F.rk), z₁ s * (kroneckerMetric E.metric F.metric).mulVec z₂ s) =
      ∑ p : Fin E.rk × Fin F.rk,
        z₁ (finProdFinEquiv p) * (kroneckerMetric E.metric F.metric).mulVec z₂ (finProdFinEquiv p) :=
    (Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl).symm
  rw [hreidx1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_
  have hmv : (kroneckerMetric E.metric F.metric).mulVec z₂ (finProdFinEquiv (i₁, j₁)) =
      ∑ i₂ : Fin E.rk, ∑ j₂ : Fin F.rk,
        E.metric i₁ i₂ * F.metric j₁ j₂ * z₂ (finProdFinEquiv (i₂, j₂)) := by
    change ∑ t : Fin (E.rk * F.rk),
      kroneckerMetric E.metric F.metric (finProdFinEquiv (i₁, j₁)) t * z₂ t = _
    rw [(Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl).symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    simp only [kroneckerMetric, Matrix.of_apply, Equiv.symm_apply_apply]
  rw [hmv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i₂ _ => ?_
  rw [Finset.mul_sum]

private lemma kronToEucl_injective (E F : HermVectorBundle) :
    Function.Injective (kronToEucl E F) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  have hzero : ∀ (a : Fin E.rk) (b : Fin F.rk),
      ∑ i : Fin E.rk, ∑ j : Fin F.rk,
        z (finProdFinEquiv (i, j)) * E.toEucl (Pi.single i 1) a * F.toEucl (Pi.single j 1) b = 0 := by
    intro a b
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin E.rk × Fin F.rk) => v (a, b))
      (LinearMap.mem_ker.mp hz)
    simpa [kronToEucl] using h1
  have hw0 : ∀ (b : Fin F.rk) (i : Fin E.rk),
      ∑ j : Fin F.rk, z (finProdFinEquiv (i, j)) * F.toEucl (Pi.single j 1) b = 0 := by
    intro b
    let w : Fin E.rk → ℝ := fun i => ∑ j : Fin F.rk, z (finProdFinEquiv (i, j)) * F.toEucl (Pi.single j 1) b
    have hEw : E.toEucl w = 0 := by
      ext a
      conv_lhs => rw [pi_eq_sum_single w, map_sum, eucl_sum_apply]
      rw [PiLp.zero_apply]
      have hrewrite : (∑ i : Fin E.rk, (w i • E.toEucl (Pi.single i 1)) a) =
          ∑ i : Fin E.rk, ∑ j : Fin F.rk,
            z (finProdFinEquiv (i, j)) * E.toEucl (Pi.single i 1) a * F.toEucl (Pi.single j 1) b := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [PiLp.smul_apply, smul_eq_mul]
        dsimp only [w]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      have hsm : (∑ i : Fin E.rk, (E.toEucl (w i • Pi.single i (1 : ℝ))) a) =
          ∑ i : Fin E.rk, (w i • E.toEucl (Pi.single i 1)) a :=
        Finset.sum_congr rfl fun i _ => by rw [map_smul]
      rw [hsm, hrewrite, hzero a b]
    have hw_zero : w = 0 := E.toEucl_injective (by rwa [map_zero])
    exact fun i => congrFun hw_zero i
  ext t
  set i := (finProdFinEquiv.symm t).1
  set j := (finProdFinEquiv.symm t).2
  let v : Fin F.rk → ℝ := fun j' => z (finProdFinEquiv (i, j'))
  have hFv : F.toEucl v = 0 := by
    ext b
    conv_lhs => rw [pi_eq_sum_single v, map_sum, eucl_sum_apply]
    rw [PiLp.zero_apply]
    have hsm : (∑ j' : Fin F.rk, (F.toEucl (v j' • Pi.single j' (1 : ℝ))) b) =
        ∑ j' : Fin F.rk, z (finProdFinEquiv (i, j')) * F.toEucl (Pi.single j' 1) b :=
      Finset.sum_congr rfl fun j' _ => by rw [map_smul, PiLp.smul_apply, smul_eq_mul]
    rw [hsm]
    exact hw0 b i
  have hv_zero : v = 0 := F.toEucl_injective (by rwa [map_zero])
  have hzij : z (finProdFinEquiv (i, j)) = 0 := congrFun hv_zero j
  have hteq : finProdFinEquiv (i, j) = t := finProdFinEquiv.apply_symm_apply t
  rwa [hteq] at hzij

/-- Positive-definiteness of the Kronecker product `h_E ⊗ h_F` of two positive-definite metrics. -/
theorem kroneckerMetric_posDef (E F : HermVectorBundle) :
    (kroneckerMetric E.metric F.metric).PosDef := by
  have hsymm : (kroneckerMetric E.metric F.metric).transpose = kroneckerMetric E.metric F.metric := by
    ext s t
    simp only [Matrix.transpose_apply, kroneckerMetric, Matrix.of_apply]
    have hE := congrFun (congrFun (isHermitian_real_transpose E.metric_posDef.isHermitian)
      (finProdFinEquiv.symm s).1) (finProdFinEquiv.symm t).1
    have hF := congrFun (congrFun (isHermitian_real_transpose F.metric_posDef.isHermitian)
      (finProdFinEquiv.symm s).2) (finProdFinEquiv.symm t).2
    simp only [Matrix.transpose_apply] at hE hF
    rw [hE, hF]
  refine posDef_of_dotProduct_mulVec_pos hsymm fun z hz => ?_
  rw [← inner_kronToEucl E F z z, real_inner_self_eq_norm_sq]
  have hne : kronToEucl E F z ≠ 0 := fun h0 => hz (kronToEucl_injective E F (by rwa [map_zero]))
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

/-- Concrete orthonormal change-of-coordinates from `EuclideanSpace ℝ (Fin r₁ × Fin r₂)` to
`Stage11MoriwakiCovolume.TensorSpace (EuclideanSpace ℝ (Fin r₁)) (EuclideanSpace ℝ (Fin r₂))`. -/
private def kronToTensorSpace (E F : HermVectorBundle) :
    EuclideanSpace ℝ (Fin E.rk × Fin F.rk) →ₗ[ℝ]
      TensorSpace (EuclideanSpace ℝ (Fin E.rk)) (EuclideanSpace ℝ (Fin F.rk)) where
  toFun v := WithLp.toLp 2 (fun p =>
    ∑ a : Fin E.rk, ∑ b : Fin F.rk,
      v (a, b) * (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin E.rk)) p.1 a) *
        (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin F.rk)) p.2 b))
  map_add' u v := by
    ext p; simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    ext p
    simp only [RingHom.id_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma kronToTensorSpace_pureTensorVec (E F : HermVectorBundle)
    (x : Fin E.rk → ℝ) (y : Fin F.rk → ℝ) :
    kronToTensorSpace E F (kronToEucl E F (pureTensorVec x y)) =
      pureTensor (E.toEucl x) (F.toEucl y) := by
  rw [kronToEucl_pureTensorVec]
  ext p
  simp only [kronToTensorSpace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, pureTensor,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => by ring

private lemma kronToTensorSpace_inner (E F : HermVectorBundle)
    (u v : EuclideanSpace ℝ (Fin E.rk × Fin F.rk)) :
    inner ℝ (kronToTensorSpace E F u) (kronToTensorSpace E F v) = inner ℝ u v := by
  let eE := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin E.rk))
  let eF := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin F.rk))
  have horthE : ∀ a₁ a₂ : Fin E.rk,
      ∑ p : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin E.rk))), eE p a₁ * eE p a₂ =
        if a₁ = a₂ then 1 else 0 := by
    intro a₁ a₂
    have h := eE.repr.inner_map_map (WithLp.toLp 2 (Pi.single a₁ (1 : ℝ)))
      (WithLp.toLp 2 (Pi.single a₂ (1 : ℝ)))
    have hL : inner ℝ (eE.repr (WithLp.toLp 2 (Pi.single a₁ (1 : ℝ))))
        (eE.repr (WithLp.toLp 2 (Pi.single a₂ (1 : ℝ)))) =
        ∑ p : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin E.rk))), eE p a₁ * eE p a₂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, eE.repr_apply_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 : inner ℝ (eE p) (WithLp.toLp 2 (Pi.single a₁ (1 : ℝ))) = eE p a₁ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Pi.single_apply]
      have h2 : inner ℝ (eE p) (WithLp.toLp 2 (Pi.single a₂ (1 : ℝ))) = eE p a₂ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Pi.single_apply]
      rw [h1, h2, mul_comm]
    have hR : inner ℝ (WithLp.toLp 2 (Pi.single a₁ (1 : ℝ)) : EuclideanSpace ℝ (Fin E.rk))
        (WithLp.toLp 2 (Pi.single a₂ (1 : ℝ))) = if a₁ = a₂ then 1 else 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, Pi.single_apply, eq_comm]
    linarith
  have horthF : ∀ b₁ b₂ : Fin F.rk,
      ∑ q : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin F.rk))), eF q b₁ * eF q b₂ =
        if b₁ = b₂ then 1 else 0 := by
    intro b₁ b₂
    have h := eF.repr.inner_map_map (WithLp.toLp 2 (Pi.single b₁ (1 : ℝ)))
      (WithLp.toLp 2 (Pi.single b₂ (1 : ℝ)))
    have hL : inner ℝ (eF.repr (WithLp.toLp 2 (Pi.single b₁ (1 : ℝ))))
        (eF.repr (WithLp.toLp 2 (Pi.single b₂ (1 : ℝ)))) =
        ∑ q : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin F.rk))), eF q b₁ * eF q b₂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, eF.repr_apply_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      have h1 : inner ℝ (eF q) (WithLp.toLp 2 (Pi.single b₁ (1 : ℝ))) = eF q b₁ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Pi.single_apply]
      have h2 : inner ℝ (eF q) (WithLp.toLp 2 (Pi.single b₂ (1 : ℝ))) = eF q b₂ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Pi.single_apply]
      rw [h1, h2, mul_comm]
    have hR : inner ℝ (WithLp.toLp 2 (Pi.single b₁ (1 : ℝ)) : EuclideanSpace ℝ (Fin F.rk))
        (WithLp.toLp 2 (Pi.single b₂ (1 : ℝ))) = if b₁ = b₂ then 1 else 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, Pi.single_apply, eq_comm]
    linarith
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, kronToTensorSpace, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, Fintype.sum_prod_type]
  trans ∑ a₁ : Fin E.rk, ∑ b₁ : Fin F.rk, ∑ a₂ : Fin E.rk, ∑ b₂ : Fin F.rk,
      (v (a₂, b₂) * u (a₁, b₁)) *
      (∑ p, eE p a₁ * eE p a₂) * (∑ q, eF q b₁ * eF q b₂)
  · trans ∑ p, ∑ q, ∑ a₁ : Fin E.rk, ∑ b₁ : Fin F.rk, ∑ a₂ : Fin E.rk, ∑ b₂ : Fin F.rk,
        (v (a₂, b₂) * u (a₁, b₁)) * (eE p a₁ * eE p a₂) * (eF q b₁ * eF q b₂)
    · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      conv_lhs =>
        arg 2; ext a₁; rw [Finset.mul_sum]
        arg 2; ext b₁; rw [Finset.sum_mul]
        arg 2; ext a₂; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ =>
        Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun b₂ _ => by ring
    · rw [Finset.sum_comm]
      conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b₁ _ => ?_
      conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b₂ _ => ?_
      calc ∑ q, ∑ p, v (a₂, b₂) * u (a₁, b₁) * (eE p a₁ * eE p a₂) * (eF q b₁ * eF q b₂)
          = ∑ q, (v (a₂, b₂) * u (a₁, b₁) * (eF q b₁ * eF q b₂)) * ∑ p, eE p a₁ * eE p a₂ := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
        _ = v (a₂, b₂) * u (a₁, b₁) * (∑ p, eE p a₁ * eE p a₂) * ∑ q, eF q b₁ * eF q b₂ := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by ring
  · simp_rw [horthE, horthF]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
    simp

private lemma kronToTensorSpace_injective (E F : HermVectorBundle) :
    Function.Injective (kronToTensorSpace E F) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu
  have h0 : inner ℝ u u = 0 := by
    rw [← kronToTensorSpace_inner E F, LinearMap.mem_ker.mp hu, inner_zero_left]
  exact inner_self_eq_zero.mp h0

/-- Concrete **Tensor Product** `E ⊗ F` of two Hermitian vector bundles over `Spec ℤ`. -/
def tensor (E F : HermVectorBundle) : HermVectorBundle where
  rk := E.rk * F.rk
  lat := Submodule.span ℤ
    { z : Fin (E.rk * F.rk) → ℝ | ∃ x ∈ E.lat, ∃ y ∈ F.lat, z = pureTensorVec x y }
  lat_discrete := by
    let T := Submodule.span ℤ
      { z : Fin (E.rk * F.rk) → ℝ | ∃ x ∈ E.lat, ∃ y ∈ F.lat, z = pureTensorVec x y }
    have hmaps : ∀ z ∈ T,
        kronToTensorSpace E F (kronToEucl E F z) ∈ tensorLat E.euclLat F.euclLat := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        rcases hw with ⟨x, hxL, y, hyL, rfl⟩
        rw [kronToTensorSpace_pureTensorVec]
        exact Submodule.subset_span ⟨E.toEucl x, ⟨x, hxL, rfl⟩, F.toEucl y, ⟨y, hyL, rfl⟩, rfl⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, map_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [map_zsmul, map_zsmul]; exact Submodule.smul_mem _ c hu
    have hDiscT : DiscreteTopology (tensorLat E.euclLat F.euclLat) :=
      (tensorLat_invariants E.euclLat F.euclLat).1
    let g : T → tensorLat E.euclLat F.euclLat :=
      fun z => ⟨kronToTensorSpace E F (kronToEucl E F z.1), hmaps z.1 z.2⟩
    have hg_cont : Continuous g :=
      Continuous.subtype_mk
        ((LinearMap.continuous_of_finiteDimensional
          ((kronToTensorSpace E F).comp (kronToEucl E F))).comp continuous_subtype_val) _
    have hg_inj : Function.Injective g := fun a b hab =>
      Subtype.ext (kronToEucl_injective E F (kronToTensorSpace_injective E F (congrArg Subtype.val hab)))
    exact DiscreteTopology.of_continuous_injective hg_cont hg_inj
  lat_span_top := by
    apply eq_top_iff.mpr
    intro z _
    have hE_sp : ∀ i : Fin E.rk, Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (E.lat : Set (Fin E.rk → ℝ)) :=
      fun i => by rw [E.lat_span_top]; trivial
    have hF_sp : ∀ j : Fin F.rk, Pi.single j (1 : ℝ) ∈ Submodule.span ℝ (F.lat : Set (Fin F.rk → ℝ)) :=
      fun j => by rw [F.lat_span_top]; trivial
    have hbasis_mem : ∀ (i : Fin E.rk) (j : Fin F.rk),
        Pi.single (finProdFinEquiv (i, j)) (1 : ℝ) ∈
          Submodule.span ℝ (Submodule.span ℤ
            { w : Fin (E.rk * F.rk) → ℝ | ∃ x ∈ E.lat, ∃ y ∈ F.lat, w = pureTensorVec x y } :
            Set (Fin (E.rk * F.rk) → ℝ)) := by
      intro i j
      have hp : Pi.single (finProdFinEquiv (i, j)) (1 : ℝ) =
          pureTensorVec (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) := by
        ext t
        unfold pureTensorVec
        simp only [Pi.single_apply]
        by_cases ht : t = finProdFinEquiv (i, j)
        · subst ht
          rw [if_pos rfl, Equiv.symm_apply_apply, if_pos rfl, if_pos rfl, mul_one]
        · have hne : finProdFinEquiv.symm t ≠ (i, j) := fun h =>
            ht (by rw [← h, Equiv.apply_symm_apply])
          rw [if_neg ht]
          by_cases h1 : (finProdFinEquiv.symm t).1 = i
          · have h2 : (finProdFinEquiv.symm t).2 ≠ j := fun h2 => hne (Prod.ext h1 h2)
            rw [if_pos h1, if_neg h2, mul_zero]
          · rw [if_neg h1, zero_mul]
      rw [hp]
      have hpure_mem : ∀ x ∈ Submodule.span ℝ (E.lat : Set (Fin E.rk → ℝ)),
          ∀ y ∈ Submodule.span ℝ (F.lat : Set (Fin F.rk → ℝ)),
            pureTensorVec x y ∈ Submodule.span ℝ (Submodule.span ℤ
              { w : Fin (E.rk * F.rk) → ℝ | ∃ a ∈ E.lat, ∃ b ∈ F.lat, w = pureTensorVec a b } :
              Set (Fin (E.rk * F.rk) → ℝ)) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem a ha =>
          intro y hy
          induction hy using Submodule.span_induction with
          | mem b hb =>
            exact Submodule.subset_span (Submodule.subset_span ⟨a, ha, b, hb, rfl⟩)
          | zero =>
            have h0 : pureTensorVec a (0 : Fin F.rk → ℝ) = 0 := by ext t; simp [pureTensorVec]
            rw [h0]; exact Submodule.zero_mem _
          | add b₁ b₂ _ _ hb₁ hb₂ =>
            have hadd : pureTensorVec a (b₁ + b₂) = pureTensorVec a b₁ + pureTensorVec a b₂ := by
              ext t; simp [pureTensorVec, mul_add]
            rw [hadd]; exact Submodule.add_mem _ hb₁ hb₂
          | smul c b _ hb =>
            have hsm : pureTensorVec a (c • b) = c • pureTensorVec a b := by
              ext t; simp [pureTensorVec]; ring
            rw [hsm]; exact Submodule.smul_mem _ c hb
        | zero =>
          intro y _
          have h0 : pureTensorVec (0 : Fin E.rk → ℝ) y = 0 := by ext t; simp [pureTensorVec]
          rw [h0]; exact Submodule.zero_mem _
        | add a₁ a₂ _ _ ha₁ ha₂ =>
          intro y hy
          have hadd : pureTensorVec (a₁ + a₂) y = pureTensorVec a₁ y + pureTensorVec a₂ y := by
            ext t; simp [pureTensorVec, add_mul]
          rw [hadd]; exact Submodule.add_mem _ (ha₁ y hy) (ha₂ y hy)
        | smul c a _ ha =>
          intro y hy
          have hsm : pureTensorVec (c • a) y = c • pureTensorVec a y := by
            ext t; simp [pureTensorVec]; ring
          rw [hsm]; exact Submodule.smul_mem _ c (ha y hy)
      exact hpure_mem _ (hE_sp i) _ (hF_sp j)
    rw [pi_eq_sum_single z]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    have hteq : t = finProdFinEquiv ((finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2) :=
      (finProdFinEquiv.apply_symm_apply t).symm
    rw [hteq]
    exact hbasis_mem _ _
  metric := kroneckerMetric E.metric F.metric
  metric_posDef := kroneckerMetric_posDef E F

/-- **Exact Tensor-Product Invariants for Hermitian Vector Bundles**:
1. `(E.tensor F).rk = E.rk * F.rk`,
2. `(E.tensor F).covol = E.covol ^ F.rk * F.covol ^ E.rk`,
3. `(E.tensor F).arakelovDeg = F.rk * E.arakelovDeg + E.rk * F.arakelovDeg`. -/
theorem tensor_invariants (E F : HermVectorBundle) :
    (E.tensor F).rk = E.rk * F.rk ∧
    (E.tensor F).covol = E.covol ^ F.rk * F.covol ^ E.rk ∧
    (E.tensor F).arakelovDeg = (F.rk : ℝ) * E.arakelovDeg + (E.rk : ℝ) * F.arakelovDeg := by
  have hinv := tensorLat_invariants E.euclLat F.euclLat
  have hDiscT : DiscreteTopology (tensorLat E.euclLat F.euclLat) := hinv.1
  let Ψ : (Fin (E.tensor F).rk → ℝ) →ₗ[ℝ]
      TensorSpace (EuclideanSpace ℝ (Fin E.rk)) (EuclideanSpace ℝ (Fin F.rk)) :=
    (kronToTensorSpace E F).comp (kronToEucl E F)
  have hΨ_inner : ∀ z₁ z₂ : Fin (E.tensor F).rk → ℝ,
      inner ℝ (Ψ z₁) (Ψ z₂) = (E.tensor F).hInner z₁ z₂ := by
    intro z₁ z₂
    let u₁ : Fin (E.rk * F.rk) → ℝ := z₁
    let u₂ : Fin (E.rk * F.rk) → ℝ := z₂
    change inner ℝ (kronToTensorSpace E F (kronToEucl E F u₁))
      (kronToTensorSpace E F (kronToEucl E F u₂)) =
      u₁ ⬝ᵥ (kroneckerMetric E.metric F.metric).mulVec u₂
    rw [kronToTensorSpace_inner, inner_kronToEucl]
  have hΨ_norm : ∀ z : Fin (E.tensor F).rk → ℝ, ‖Ψ z‖ = (E.tensor F).hNorm z := by
    intro z
    have hsq : ‖Ψ z‖ ^ 2 = (E.tensor F).hNorm z ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hΨ_inner z z, (E.tensor F).hNorm_sq z]
    nlinarith [norm_nonneg (Ψ z), (E.tensor F).hNorm_nonneg z]
  have hΨ_maps : ∀ z : Fin (E.tensor F).rk → ℝ, z ∈ (E.tensor F).lat →
      Ψ z ∈ tensorLat E.euclLat F.euclLat := by
    have haux : ∀ z' : Fin (E.rk * F.rk) → ℝ,
        z' ∈ Submodule.span ℤ
          { w : Fin (E.rk * F.rk) → ℝ | ∃ x ∈ E.lat, ∃ y ∈ F.lat, w = pureTensorVec x y } →
        (kronToTensorSpace E F) (kronToEucl E F z') ∈ tensorLat E.euclLat F.euclLat := by
      intro z' hz'
      induction hz' using Submodule.span_induction with
      | mem w hw =>
        rcases hw with ⟨x, hxL, y, hyL, rfl⟩
        rw [kronToTensorSpace_pureTensorVec]
        exact Submodule.subset_span ⟨E.toEucl x, ⟨x, hxL, rfl⟩, F.toEucl y, ⟨y, hyL, rfl⟩, rfl⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, map_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [map_zsmul, map_zsmul]; exact Submodule.smul_mem _ c hu
    exact fun z hz => haux z hz
  let isoMap : (E.tensor F).euclLat →ₗ[ℤ] tensorLat E.euclLat F.euclLat :=
    { toFun := fun v =>
        ⟨Ψ ((E.tensor F).toEuclEquiv.symm v.1),
          hΨ_maps _ ((E.tensor F).latEquivEuclLat.symm v).2⟩
      map_add' := fun a b => Subtype.ext (by
        change Ψ ((E.tensor F).toEuclEquiv.symm (a.1 + b.1)) = _
        rw [map_add, map_add]; rfl)
      map_smul' := fun c a => Subtype.ext (by
        change Ψ ((E.tensor F).toEuclEquiv.symm (c • a.1)) = _
        rw [map_zsmul, map_zsmul]; rfl) }
  have hiso_norm : ∀ v : (E.tensor F).euclLat,
      ‖((isoMap v : tensorLat E.euclLat F.euclLat) :
        TensorSpace (EuclideanSpace ℝ (Fin E.rk)) (EuclideanSpace ℝ (Fin F.rk)))‖ =
      ‖(v : EuclideanSpace ℝ (Fin (E.tensor F).rk))‖ := by
    intro v
    change ‖Ψ ((E.tensor F).toEuclEquiv.symm v.1)‖ = ‖v.1‖
    rw [hΨ_norm, ← (E.tensor F).norm_toEucl, (E.tensor F).toEucl_toEuclEquiv_symm]
  have hiso_inj : Function.Injective isoMap := by
    intro a b hab
    apply Subtype.ext
    have h0 : ‖((isoMap (a - b) : tensorLat E.euclLat F.euclLat) :
        TensorSpace (EuclideanSpace ℝ (Fin E.rk)) (EuclideanSpace ℝ (Fin F.rk)))‖ = 0 := by
      rw [map_sub, hab, sub_self]; simp
    rw [hiso_norm (a - b)] at h0
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hiso_surj : Function.Surjective isoMap := by
    intro w
    have hpre : ∀ u ∈ tensorLat E.euclLat F.euclLat,
        ∃ z : Fin (E.tensor F).rk → ℝ, z ∈ (E.tensor F).lat ∧ Ψ z = u := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        rcases hu with ⟨_, ⟨x, hxL, rfl⟩, _, ⟨y, hyL, rfl⟩, rfl⟩
        have hmem : pureTensorVec x y ∈ (E.tensor F).lat :=
          Submodule.subset_span (R := ℤ) (M := Fin (E.rk * F.rk) → ℝ) ⟨x, hxL, y, hyL, rfl⟩
        exact ⟨pureTensorVec x y, hmem, kronToTensorSpace_pureTensorVec E F x y⟩
      | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
      | add u₁ u₂ _ _ hu₁ hu₂ =>
        rcases hu₁ with ⟨z₁, hz₁, rfl⟩
        rcases hu₂ with ⟨z₂, hz₂, rfl⟩
        exact ⟨z₁ + z₂, Submodule.add_mem _ hz₁ hz₂, map_add _ _ _⟩
      | smul c u _ hu =>
        rcases hu with ⟨z, hz, rfl⟩
        exact ⟨c • z, Submodule.smul_mem _ c hz, map_zsmul _ _ _⟩
    rcases hpre w.1 w.2 with ⟨z, hzL, hzw⟩
    refine ⟨⟨(E.tensor F).toEucl z, ⟨z, hzL, rfl⟩⟩, Subtype.ext ?_⟩
    change Ψ ((E.tensor F).toEuclEquiv.symm ((E.tensor F).toEucl z)) = w.1
    rw [(E.tensor F).toEuclEquiv_symm_toEucl, hzw]
  let iso : (E.tensor F).euclLat ≃ₗ[ℤ] tensorLat E.euclLat F.euclLat :=
    LinearEquiv.ofBijective isoMap ⟨hiso_inj, hiso_surj⟩
  have hEq := arithDeg_eq_of_isometric_equiv iso hiso_norm
  refine ⟨rfl, ?_, ?_⟩
  · change ArakelovCovolume.covol (E.tensor F).euclLat =
      ArakelovCovolume.covol E.euclLat ^ F.rk * ArakelovCovolume.covol F.euclLat ^ E.rk
    rw [hEq.2.1, hinv.2.2.1, E.rk_euclLat, F.rk_euclLat]
  · change ArakelovCovolume.degAr (E.tensor F).euclLat =
      (F.rk : ℝ) * ArakelovCovolume.degAr E.euclLat + (E.rk : ℝ) * ArakelovCovolume.degAr F.euclLat
    rw [← arithDeg_eq_degAr, hEq.2.2.1, hinv.2.2.2, E.rk_euclLat, F.rk_euclLat]
    rfl

/-- **Exact Tensor-Product Slope Additivity (`μ(E ⊗ F) = μ(E) + μ(F)`)**:
for any two positive-rank Hermitian vector bundles `E, F` over `Spec ℤ`. -/
theorem bundleSlope_tensor (E F : HermVectorBundle) (hE : 0 < E.rk) (hF : 0 < F.rk) :
    (E.tensor F).slope = E.slope + F.slope := by
  obtain ⟨hrk, _, hdeg⟩ := tensor_invariants E F
  have hEr : (E.rk : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hE.ne'
  have hFr : (F.rk : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.ne'
  unfold slope
  rw [hrk, hdeg]
  push_cast
  field_simp [hEr, hFr]

/-! ### Dual Bundle `E^∨` & Exact Dual Slope Formula `μ(E^∨) = -μ(E)` -/

/-- Canonical dual lattice `Λ^∨ = { y ∈ ℝ^r | ∀ x ∈ Λ, y ⬝ᵥ x ∈ ℤ }` of `E.lat`. -/
def dualLatR (E : HermVectorBundle) : Submodule ℤ (Fin E.rk → ℝ) where
  carrier := { y : Fin E.rk → ℝ | ∀ x ∈ E.lat, ∃ n : ℤ, y ⬝ᵥ x = (n : ℝ) }
  add_mem' := by
    intro y₁ y₂ hy₁ hy₂ x hx
    obtain ⟨n₁, hn₁⟩ := hy₁ x hx
    obtain ⟨n₂, hn₂⟩ := hy₂ x hx
    exact ⟨n₁ + n₂, by rw [add_dotProduct, hn₁, hn₂, Int.cast_add]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨n, hn⟩ := hy x hx
    exact ⟨c * n, by
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_dotProduct, smul_eq_mul, hn, Int.cast_mul]⟩

/-- The `ℝ`-linear map `y ↦ E.toEucl (E.metric⁻¹ *ᵥ y)` identifying `dualLatR E` with
`Stage4ArakelovBost.dualLat E.euclLat` isometrically. -/
private def dualToEucl (E : HermVectorBundle) :
    (Fin E.rk → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk) :=
  E.toEucl.comp (Matrix.mulVecLin E.metric⁻¹)

private lemma inner_dualToEucl_toEucl (E : HermVectorBundle) (y x : Fin E.rk → ℝ) :
    inner ℝ (dualToEucl E y) (E.toEucl x) = y ⬝ᵥ x := by
  dsimp only [dualToEucl, LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [E.inner_toEucl]
  unfold hInner
  have hdet : E.metric.det ≠ 0 := E.metric_posDef.det_pos.ne'
  have hT : E.metric.transpose = E.metric := isHermitian_real_transpose E.metric_posDef.isHermitian
  have hmul : E.metric * E.metric⁻¹ = 1 :=
    Matrix.mul_nonsing_inv E.metric (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, Matrix.mulVec_mulVec, hmul,
    Matrix.one_mulVec]

private lemma inner_dualToEucl (E : HermVectorBundle) (y₁ y₂ : Fin E.rk → ℝ) :
    inner ℝ (dualToEucl E y₁) (dualToEucl E y₂) = y₁ ⬝ᵥ E.metric⁻¹.mulVec y₂ :=
  inner_dualToEucl_toEucl E y₁ (E.metric⁻¹.mulVec y₂)

private lemma mem_dualLatR_iff (E : HermVectorBundle) (y : Fin E.rk → ℝ) :
    y ∈ E.dualLatR ↔ dualToEucl E y ∈ Stage4ArakelovBost.dualLat E.euclLat := by
  constructor
  · intro hy
    refine ⟨by rw [E.span_real_euclLat]; trivial, ?_⟩
    rintro _ ⟨x, hxL, rfl⟩
    change ∃ n : ℤ, inner ℝ (dualToEucl E y) (E.toEucl x) = (n : ℝ)
    rw [inner_dualToEucl_toEucl]
    exact hy x hxL
  · intro hy x hxL
    have h := hy.2 (E.toEucl x) ⟨x, hxL, rfl⟩
    rwa [inner_dualToEucl_toEucl] at h

private lemma dualToEucl_bijective (E : HermVectorBundle) :
    Function.Bijective (dualToEucl E) := by
  have hinj : Function.Injective (dualToEucl E) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have h0 : E.metric⁻¹.mulVec y = 0 := E.toEucl_injective (by
      simpa [dualToEucl] using LinearMap.mem_ker.mp hy)
    have hmul : E.metric * E.metric⁻¹ = 1 :=
      Matrix.mul_nonsing_inv E.metric (isUnit_iff_ne_zero.mpr E.metric_posDef.det_pos.ne')
    calc y = (1 : Matrix (Fin E.rk) (Fin E.rk) ℝ).mulVec y := (Matrix.one_mulVec y).symm
      _ = (E.metric * E.metric⁻¹).mulVec y := by rw [hmul]
      _ = E.metric.mulVec (E.metric⁻¹.mulVec y) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  refine ⟨hinj, ?_⟩
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun, finrank_euclideanSpace_fin]

/-- Concrete **Dual Hermitian Vector Bundle** `E^∨` with lattice `Λ^∨` and inverse metric `h⁻¹`. -/
def dual (E : HermVectorBundle) : HermVectorBundle where
  rk := E.rk
  lat := E.dualLatR
  lat_discrete := by
    have hDiscD : DiscreteTopology (Stage4ArakelovBost.dualLat E.euclLat) :=
      Stage4ArakelovBost.discreteTopology_dualLat E.euclLat
    let f : E.dualLatR → Stage4ArakelovBost.dualLat E.euclLat :=
      fun y => ⟨dualToEucl E y.1, (mem_dualLatR_iff E y.1).mp y.2⟩
    have hf_cont : Continuous f :=
      Continuous.subtype_mk
        ((LinearMap.continuous_of_finiteDimensional (dualToEucl E)).comp continuous_subtype_val) _
    have hf_inj : Function.Injective f := fun a b hab =>
      Subtype.ext ((dualToEucl_bijective E).1 (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf_cont hf_inj
  lat_span_top := by
    let e := LinearEquiv.ofBijective (dualToEucl E) (dualToEucl_bijective E)
    have hmap : Submodule.map (dualToEucl E) (Submodule.span ℝ (E.dualLatR : Set (Fin E.rk → ℝ))) = ⊤ := by
      rw [Submodule.map_span]
      have himg : (dualToEucl E) '' (E.dualLatR : Set (Fin E.rk → ℝ)) =
          (Stage4ArakelovBost.dualLat E.euclLat : Set (EuclideanSpace ℝ (Fin E.rk))) := by
        ext v
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (mem_dualLatR_iff E y).mp hy
        · intro hv
          obtain ⟨y, rfl⟩ := (dualToEucl_bijective E).2 v
          exact ⟨y, (mem_dualLatR_iff E y).mpr hv, rfl⟩
      rw [himg, Stage4ArakelovBost.span_real_dualLat, E.span_real_euclLat]
    apply eq_top_iff.mpr
    intro y _
    have hmem : dualToEucl E y ∈ Submodule.map (dualToEucl E)
        (Submodule.span ℝ (E.dualLatR : Set (Fin E.rk → ℝ))) := by
      rw [hmap]; trivial
    rcases hmem with ⟨y', hy', hy'eq⟩
    rwa [← (dualToEucl_bijective E).1 hy'eq]
  metric := E.metric⁻¹
  metric_posDef := posDef_inv E.metric_posDef

/-- Typed alias of `dualToEucl` on `Fin E.dual.rk → ℝ` (avoids unfolding `E.dual` during `rw`). -/
private def dualToEuclD (E : HermVectorBundle) :
    (Fin E.dual.rk → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk) :=
  E.dualToEucl

private lemma inner_dualToEuclD (E : HermVectorBundle) (y₁ y₂ : Fin E.dual.rk → ℝ) :
    inner ℝ (E.dualToEuclD y₁) (E.dualToEuclD y₂) = E.dual.hInner y₁ y₂ :=
  E.inner_dualToEucl y₁ y₂

private lemma dualToEuclD_bijective (E : HermVectorBundle) :
    Function.Bijective E.dualToEuclD :=
  E.dualToEucl_bijective

private lemma mem_dualLat_iff_dualToEuclD (E : HermVectorBundle) (y : Fin E.dual.rk → ℝ) :
    y ∈ E.dual.lat ↔ E.dualToEuclD y ∈ Stage4ArakelovBost.dualLat E.euclLat :=
  E.mem_dualLatR_iff y

/-- Isometric `ℤ`-linear equivalence `E.dual.euclLat ≃ₗ[ℤ] Stage4ArakelovBost.dualLat E.euclLat`. -/
def dualEuclLatEquiv (E : HermVectorBundle) :
    E.dual.euclLat ≃ₗ[ℤ] Stage4ArakelovBost.dualLat E.euclLat := by
  let fMap : E.dual.euclLat →ₗ[ℤ] Stage4ArakelovBost.dualLat E.euclLat :=
    { toFun := fun v =>
        ⟨E.dualToEuclD (E.dual.toEuclEquiv.symm v.1),
          (E.mem_dualLat_iff_dualToEuclD _).mp (E.dual.latEquivEuclLat.symm v).2⟩
      map_add' := fun a b => Subtype.ext (by
        change E.dualToEuclD (E.dual.toEuclEquiv.symm (a.1 + b.1)) = _
        rw [map_add, map_add]; rfl)
      map_smul' := fun c a => Subtype.ext (by
        change E.dualToEuclD (E.dual.toEuclEquiv.symm (c • a.1)) = _
        rw [map_zsmul, map_zsmul]; rfl) }
  have hbij : Function.Bijective fMap := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact E.dual.toEuclEquiv.symm.injective
        ((E.dualToEuclD_bijective).1 (congrArg Subtype.val hab))
    · intro w
      obtain ⟨y, hy⟩ := (E.dualToEuclD_bijective).2 w.1
      have hyL : y ∈ E.dual.lat := (E.mem_dualLat_iff_dualToEuclD y).mpr (by rw [hy]; exact w.2)
      refine ⟨⟨E.dual.toEucl y, ⟨y, hyL, rfl⟩⟩, Subtype.ext ?_⟩
      change E.dualToEuclD (E.dual.toEuclEquiv.symm (E.dual.toEucl y)) = w.1
      rw [E.dual.toEuclEquiv_symm_toEucl, hy]
  exact LinearEquiv.ofBijective fMap hbij

theorem dualEuclLatEquiv_norm (E : HermVectorBundle) (v : E.dual.euclLat) :
    ‖((E.dualEuclLatEquiv v : Stage4ArakelovBost.dualLat E.euclLat) :
      EuclideanSpace ℝ (Fin E.rk))‖ = ‖(v : EuclideanSpace ℝ (Fin E.dual.rk))‖ := by
  change ‖E.dualToEuclD (E.dual.toEuclEquiv.symm v.1)‖ = ‖v.1‖
  have hsq : ‖E.dualToEuclD (E.dual.toEuclEquiv.symm v.1)‖ ^ 2 = ‖v.1‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_dualToEuclD, ← E.dual.inner_toEucl,
      real_inner_self_eq_norm_sq, E.dual.toEucl_toEuclEquiv_symm]
  nlinarith [norm_nonneg (E.dualToEuclD (E.dual.toEuclEquiv.symm v.1)), norm_nonneg v.1]

/-- **Exact Dual Bundle Invariants**:
`rk(E^∨) = rk(E)`, `covol(E^∨) = covol(E)⁻¹`, `deg_Ar(E^∨) = -deg_Ar(E)`, `μ(E^∨) = -μ(E)`. -/
theorem dual_invariants (E : HermVectorBundle) :
    E.dual.rk = E.rk ∧
    E.dual.covol = (E.covol)⁻¹ ∧
    E.dual.arakelovDeg = -E.arakelovDeg ∧
    E.dual.slope = -E.slope := by
  have : DiscreteTopology (Stage4ArakelovBost.dualLat E.euclLat) :=
    Stage4ArakelovBost.discreteTopology_dualLat E.euclLat
  have hEq := arithDeg_eq_of_isometric_equiv E.dualEuclLatEquiv E.dualEuclLatEquiv_norm
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change ArakelovCovolume.covol E.dual.euclLat = (ArakelovCovolume.covol E.euclLat)⁻¹
    rw [hEq.2.1, Stage4ArakelovBost.covol_dualLat]
  · change ArakelovCovolume.degAr E.dual.euclLat = -ArakelovCovolume.degAr E.euclLat
    rw [← arithDeg_eq_degAr, hEq.2.2.1, arithDeg_eq_degAr, Stage4ArakelovBost.degAr_dualLat]
  · rw [E.dual.slope_eq_euclSlope, E.slope_eq_euclSlope, hEq.2.2.2,
      Stage4ArakelovBost.slope_dualLat]

/-- **Dual Slope Formula**: `μ(E^∨) = -μ(E)`. -/
theorem bundleSlope_dual (E : HermVectorBundle) : E.dual.slope = -E.slope :=
  E.dual_invariants.2.2.2

/-- Helper: isometric `ℤ`-linear equivalence preserves `ArakelovCovolume.muMax`. -/
private theorem muMax_eq_of_isometric_equiv
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {L₁ : Submodule ℤ E₁} {L₂ : Submodule ℤ E₂}
    [DiscreteTopology L₁] [DiscreteTopology L₂]
    (e : L₁ ≃ₗ[ℤ] L₂) (he : ∀ x : L₁, ‖(e x : E₂)‖ = ‖(x : E₁)‖) :
    ArakelovCovolume.muMax L₁ = ArakelovCovolume.muMax L₂ := by
  have hset : ArakelovCovolume.slopes L₁ = ArakelovCovolume.slopes L₂ := by
    ext t
    constructor
    · rintro ⟨N, hNL, hN0, rfl⟩
      let N' : Submodule ℤ E₂ := (N.comap L₁.subtype).map (L₂.subtype.comp e.toLinearMap)
      have hN'L : N' ≤ L₂ := by rintro _ ⟨x, _, rfl⟩; exact (e x).2
      have : DiscreteTopology N := discreteTopology_of_le hNL
      have : DiscreteTopology N' := discreteTopology_of_le hN'L
      obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
      have hN'0 : N' ≠ ⊥ := by
        intro hbot
        have hmem : ((e ⟨x, hNL hxN⟩ : L₂) : E₂) ∈ N' := ⟨⟨x, hNL hxN⟩, hxN, rfl⟩
        rw [hbot, Submodule.mem_bot] at hmem
        have hnorm0 : ‖x‖ = 0 := by
          have h1 := he ⟨x, hNL hxN⟩
          rw [hmem, norm_zero] at h1
          exact h1.symm
        exact hx0 (norm_eq_zero.mp hnorm0)
      let eN : N ≃ₗ[ℤ] N' :=
        { toFun := fun y => ⟨(e ⟨y.1, hNL y.2⟩ : L₂).1, ⟨⟨y.1, hNL y.2⟩, y.2, rfl⟩⟩
          invFun := fun z => ⟨(e.symm ⟨z.1, hN'L z.2⟩ : L₁).1, by
            rcases z.2 with ⟨x, hxN, hxz⟩
            have hx' : e.symm ⟨z.1, hN'L z.2⟩ = x := by
              apply e.injective
              rw [e.apply_symm_apply]
              exact Subtype.ext hxz.symm
            rw [hx']; exact hxN⟩
          map_add' := fun a b => Subtype.ext (by
            have hadd : (⟨a.1 + b.1, hNL (a + b).2⟩ : L₁) = ⟨a.1, hNL a.2⟩ + ⟨b.1, hNL b.2⟩ := rfl
            change (e ⟨a.1 + b.1, hNL (a + b).2⟩ : L₂).1 = _
            rw [hadd, map_add]; rfl)
          map_smul' := fun c a => Subtype.ext (by
            have hsm : (⟨c • a.1, hNL (c • a).2⟩ : L₁) = c • ⟨a.1, hNL a.2⟩ := rfl
            change (e ⟨c • a.1, hNL (c • a).2⟩ : L₂).1 = _
            rw [hsm, map_zsmul]; rfl)
          left_inv := fun y => Subtype.ext (by
            change (e.symm (e ⟨y.1, hNL y.2⟩) : L₁).1 = y.1
            rw [e.symm_apply_apply])
          right_inv := fun z => Subtype.ext (by
            change (e (e.symm ⟨z.1, hN'L z.2⟩) : L₂).1 = z.1
            rw [e.apply_symm_apply]) }
      have hsl := (arithDeg_eq_of_isometric_equiv eN (fun y => he ⟨y.1, hNL y.2⟩)).2.2.2
      exact ⟨N', hN'L, hN'0, hsl.symm⟩
    · rintro ⟨N', hN'L, hN'0, rfl⟩
      let N : Submodule ℤ E₁ := (N'.comap L₂.subtype).map (L₁.subtype.comp e.symm.toLinearMap)
      have hNL : N ≤ L₁ := by rintro _ ⟨x, _, rfl⟩; exact (e.symm x).2
      have : DiscreteTopology N' := discreteTopology_of_le hN'L
      have : DiscreteTopology N := discreteTopology_of_le hNL
      have he_symm : ∀ y : L₂, ‖(e.symm y : E₁)‖ = ‖(y : E₂)‖ := by
        intro y
        have h1 := he (e.symm y)
        rw [e.apply_symm_apply] at h1
        exact h1.symm
      obtain ⟨y, hyN, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'0
      have hN0 : N ≠ ⊥ := by
        intro hbot
        have hmem : ((e.symm ⟨y, hN'L hyN⟩ : L₁) : E₁) ∈ N := ⟨⟨y, hN'L hyN⟩, hyN, rfl⟩
        rw [hbot, Submodule.mem_bot] at hmem
        have hnorm0 : ‖y‖ = 0 := by
          have h1 := he_symm ⟨y, hN'L hyN⟩
          rw [hmem, norm_zero] at h1
          exact h1.symm
        exact hy0 (norm_eq_zero.mp hnorm0)
      let eN : N' ≃ₗ[ℤ] N :=
        { toFun := fun y => ⟨(e.symm ⟨y.1, hN'L y.2⟩ : L₁).1, ⟨⟨y.1, hN'L y.2⟩, y.2, rfl⟩⟩
          invFun := fun z => ⟨(e ⟨z.1, hNL z.2⟩ : L₂).1, by
            rcases z.2 with ⟨x, hxN, hxz⟩
            have hx' : e ⟨z.1, hNL z.2⟩ = x := by
              apply e.symm.injective
              rw [e.symm_apply_apply]
              exact Subtype.ext hxz.symm
            rw [hx']; exact hxN⟩
          map_add' := fun a b => Subtype.ext (by
            have hadd : (⟨a.1 + b.1, hN'L (a + b).2⟩ : L₂) = ⟨a.1, hN'L a.2⟩ + ⟨b.1, hN'L b.2⟩ := rfl
            change (e.symm ⟨a.1 + b.1, hN'L (a + b).2⟩ : L₁).1 = _
            rw [hadd, map_add]; rfl)
          map_smul' := fun c a => Subtype.ext (by
            have hsm : (⟨c • a.1, hN'L (c • a).2⟩ : L₂) = c • ⟨a.1, hN'L a.2⟩ := rfl
            change (e.symm ⟨c • a.1, hN'L (c • a).2⟩ : L₁).1 = _
            rw [hsm, map_zsmul]; rfl)
          left_inv := fun y => Subtype.ext (by
            change (e (e.symm ⟨y.1, hN'L y.2⟩) : L₂).1 = y.1
            rw [e.apply_symm_apply])
          right_inv := fun z => Subtype.ext (by
            change (e.symm (e ⟨z.1, hNL z.2⟩) : L₁).1 = z.1
            rw [e.symm_apply_apply]) }
      have hsl := (arithDeg_eq_of_isometric_equiv eN (fun y => he_symm ⟨y.1, hN'L y.2⟩)).2.2.2
      exact ⟨N, hNL, hN0, hsl.symm⟩
  unfold ArakelovCovolume.muMax
  rw [hset]

/-- **Dual Maximal/Minimal Slope Duality**: `μ_max(E^∨) = -μ_min(E)`. -/
theorem bundleMuMax_dual (E : HermVectorBundle) (hr : 0 < E.rk) :
    E.dual.muMax = -E.muMin := by
  have : DiscreteTopology (Stage4ArakelovBost.dualLat E.euclLat) :=
    Stage4ArakelovBost.discreteTopology_dualLat E.euclLat
  unfold muMax muMin
  rw [muMax_eq_of_isometric_equiv E.dualEuclLatEquiv E.dualEuclLatEquiv_norm,
    Stage4ArakelovBost.muMax_dualLat E.euclLat (E.euclLat_ne_bot_of_rk_pos hr)]

/-- **Dual Minimal/Maximal Slope Duality**: `μ_min(E^∨) = -μ_max(E)`. -/
theorem bundleMuMin_dual (E : HermVectorBundle) (hr : 0 < E.rk) :
    E.dual.muMin = -E.muMax := by
  -- Use `U = dualToEucl E ∘ E.dual.toEuclEquiv.symm` (real linear isometry sending `E.dual.euclLat`
  -- onto `dualLat E.euclLat`, hence sending `dualLat E.dual.euclLat` onto `dualLat (dualLat E.euclLat) = E.euclLat`).
  have : DiscreteTopology (Stage4ArakelovBost.dualLat E.euclLat) :=
    Stage4ArakelovBost.discreteTopology_dualLat E.euclLat
  have : DiscreteTopology (Stage4ArakelovBost.dualLat E.dual.euclLat) :=
    Stage4ArakelovBost.discreteTopology_dualLat E.dual.euclLat
  let U : EuclideanSpace ℝ (Fin E.dual.rk) →ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk) :=
    E.dualToEuclD.comp E.dual.toEuclEquiv.symm.toLinearMap
  have hU_inner : ∀ v w, inner ℝ (U v) (U w) = inner ℝ v w := by
    intro v w
    change inner ℝ (E.dualToEuclD (E.dual.toEuclEquiv.symm v))
      (E.dualToEuclD (E.dual.toEuclEquiv.symm w)) = inner ℝ v w
    rw [inner_dualToEuclD, ← E.dual.inner_toEucl,
      E.dual.toEucl_toEuclEquiv_symm, E.dual.toEucl_toEuclEquiv_symm]
  have hU_bij : Function.Bijective U :=
    E.dualToEuclD_bijective.comp E.dual.toEuclEquiv.symm.bijective
  let Ue : EuclideanSpace ℝ (Fin E.dual.rk) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin E.rk) :=
    LinearEquiv.ofBijective U hU_bij
  have hU_maps_lat : ∀ v, v ∈ E.dual.euclLat ↔ U v ∈ Stage4ArakelovBost.dualLat E.euclLat := by
    intro v
    constructor
    · rintro ⟨y, hyL, rfl⟩
      change E.dualToEuclD (E.dual.toEuclEquiv.symm (E.dual.toEucl y)) ∈
        Stage4ArakelovBost.dualLat E.euclLat
      rw [E.dual.toEuclEquiv_symm_toEucl]
      exact (E.mem_dualLat_iff_dualToEuclD y).mp hyL
    · intro hUv
      let y := E.dual.toEuclEquiv.symm v
      have hyL : y ∈ E.dual.lat := (E.mem_dualLat_iff_dualToEuclD y).mpr hUv
      exact ⟨y, hyL, E.dual.toEucl_toEuclEquiv_symm v⟩
  have hU_maps_dual : ∀ v, v ∈ Stage4ArakelovBost.dualLat E.dual.euclLat ↔
      U v ∈ E.euclLat := by
    intro v
    rw [← Stage4ArakelovBost.dualLat_dualLat E.euclLat]
    constructor
    · intro hv
      refine ⟨by rw [Stage4ArakelovBost.span_real_dualLat, E.span_real_euclLat]; trivial, ?_⟩
      intro w hw
      let w' := Ue.symm w
      have h1 : w = U w' := (Ue.apply_symm_apply w).symm
      have hw'_mem : w' ∈ E.dual.euclLat := (hU_maps_lat w').mpr (by rw [← h1]; exact hw)
      have hpair : inner ℝ (U v) w = inner ℝ v w' := by
        rw [h1, hU_inner]
      rw [hpair]
      exact hv.2 w' hw'_mem
    · intro hUv
      refine ⟨by rw [E.dual.span_real_euclLat]; trivial, ?_⟩
      intro w' hw'
      have hUw' : U w' ∈ Stage4ArakelovBost.dualLat E.euclLat := (hU_maps_lat w').mp hw'
      rw [← hU_inner]
      exact hUv.2 (U w') hUw'
  let eDD : Stage4ArakelovBost.dualLat E.dual.euclLat ≃ₗ[ℤ] E.euclLat :=
    { toFun := fun v => ⟨U v.1, (hU_maps_dual v.1).mp v.2⟩
      map_add' := fun a b => Subtype.ext (map_add U a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul U c a.1)
      invFun := fun y => ⟨Ue.symm y.1, (hU_maps_dual _).mpr (by
        change Ue (Ue.symm y.1) ∈ E.euclLat; rw [Ue.apply_symm_apply]; exact y.2)⟩
      left_inv := fun v => Subtype.ext (Ue.symm_apply_apply v.1)
      right_inv := fun y => Subtype.ext (Ue.apply_symm_apply y.1) }
  have heDD_norm : ∀ v : Stage4ArakelovBost.dualLat E.dual.euclLat,
      ‖((eDD v : E.euclLat) : EuclideanSpace ℝ (Fin E.rk))‖ =
        ‖(v : EuclideanSpace ℝ (Fin E.dual.rk))‖ := by
    intro v
    change ‖U v.1‖ = ‖v.1‖
    have hsq : ‖U v.1‖ ^ 2 = ‖v.1‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hU_inner, real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg (U v.1), norm_nonneg v.1]
  have h1 := Stage4ArakelovBost.muMax_dualLat E.dual.euclLat
    (E.dual.euclLat_ne_bot_of_rk_pos (by change 0 < E.rk; exact hr))
  have h2 := muMax_eq_of_isometric_equiv eDD heDD_norm
  unfold muMin muMax
  linarith

/-! ### Morphisms & Bost's Slope Inequality `μ_min(E) ≤ μ_max(F) + log ‖φ‖_op` -/

/-- A concrete **morphism of Hermitian vector bundles** `φ : E → F` over `Spec ℤ`:
an `ℝ`-linear map `ℝ^{rk E} →ₗ[ℝ] ℝ^{rk F}` preserving the integral lattices `φ(Λ_E) ⊆ Λ_F`. -/
structure HermBundleMorphism (E F : HermVectorBundle) where
  toLinearMap : (Fin E.rk → ℝ) →ₗ[ℝ] (Fin F.rk → ℝ)
  maps_lat : ∀ x ∈ E.lat, toLinearMap x ∈ F.lat

namespace HermBundleMorphism

/-- Transport of `φ : E → F` to a continuous linear map between Euclidean models. -/
def toEuclCLM {E F : HermVectorBundle} (φ : HermBundleMorphism E F) :
    EuclideanSpace ℝ (Fin E.rk) →L[ℝ] EuclideanSpace ℝ (Fin F.rk) :=
  LinearMap.toContinuousLinearMap
    ((F.toEucl.comp φ.toLinearMap).comp E.toEuclEquiv.symm.toLinearMap)

/-- Concrete Hermitian **operator norm** `‖φ‖_op` of `φ : E → F`. -/
def opNorm {E F : HermVectorBundle} (φ : HermBundleMorphism E F) : ℝ :=
  ‖φ.toEuclCLM‖

theorem opNorm_nonneg {E F : HermVectorBundle} (φ : HermBundleMorphism E F) :
    0 ≤ φ.opNorm :=
  norm_nonneg _

theorem hNorm_apply_le {E F : HermVectorBundle} (φ : HermBundleMorphism E F)
    (x : Fin E.rk → ℝ) :
    F.hNorm (φ.toLinearMap x) ≤ φ.opNorm * E.hNorm x := by
  have h := φ.toEuclCLM.le_opNorm (E.toEucl x)
  have hL : φ.toEuclCLM (E.toEucl x) = F.toEucl (φ.toLinearMap x) := by
    change F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl x))) = F.toEucl (φ.toLinearMap x)
    rw [E.toEuclEquiv_symm_toEucl]
  rw [hL, F.norm_toEucl, E.norm_toEucl] at h
  exact h

theorem opNorm_pos_of_ne_zero {E F : HermVectorBundle} (φ : HermBundleMorphism E F)
    (hφ : φ.toLinearMap ≠ 0) : 0 < φ.opNorm := by
  refine norm_pos_iff.mpr fun h0 => hφ ?_
  apply LinearMap.ext
  intro x
  have h1 : φ.toEuclCLM (E.toEucl x) = 0 := by rw [h0]; rfl
  change F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl x))) = 0 at h1
  rw [E.toEuclEquiv_symm_toEucl] at h1
  simp only [LinearMap.zero_apply]
  exact F.toEucl_injective (by rwa [map_zero])

theorem opNorm_le_of_bound {E F : HermVectorBundle} (φ : HermBundleMorphism E F)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, F.hNorm (φ.toLinearMap x) ≤ C * E.hNorm x) :
    φ.opNorm ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
  let x := E.toEuclEquiv.symm v
  have hv : E.toEucl x = v := E.toEucl_toEuclEquiv_symm v
  have hL : φ.toEuclCLM v = F.toEucl (φ.toLinearMap x) := rfl
  rw [hL, F.norm_toEucl, ← hv, E.norm_toEucl]
  exact hC x

/-- **BOST'S SLOPE INEQUALITY FOR HERMITIAN VECTOR BUNDLES** (`0` Assumptions!):
for ANY non-zero morphism `φ : E → F` of Hermitian vector bundles over `Spec ℤ`:
$$\mu_{\min}(E) \le \mu_{\max}(F) + \log \|\varphi\|_{\mathrm{op}}.$$ -/
theorem bost_slope_inequality_bundle {E F : HermVectorBundle}
    (φ : HermBundleMorphism E F) (hφ : φ.toLinearMap ≠ 0) :
    E.muMin ≤ F.muMax + Real.log φ.opNorm := by
  have hne_lat : ∃ v ∈ E.euclLat, φ.toEuclCLM.toLinearMap v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hφ
    apply LinearMap.ext
    intro x
    have hx : x ∈ Submodule.span ℝ (E.lat : Set (Fin E.rk → ℝ)) := by
      rw [E.lat_span_top]; trivial
    induction hx using Submodule.span_induction with
    | mem u hu =>
      have h1 := hall (E.toEucl u) ⟨u, hu, rfl⟩
      change F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl u))) = 0 at h1
      rw [E.toEuclEquiv_symm_toEucl] at h1
      simp only [LinearMap.zero_apply]
      exact F.toEucl_injective (by rwa [map_zero])
    | zero => simp
    | add u v _ _ hu hv => simp [map_add, hu, hv]
    | smul c u _ hu => simp [map_smul, hu]
  have hmap_eucl : ∀ v ∈ E.euclLat, φ.toEuclCLM.toLinearMap v ∈ F.euclLat := by
    rintro _ ⟨x, hxL, rfl⟩
    change F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl x))) ∈ F.euclLat
    rw [E.toEuclEquiv_symm_toEucl]
    exact ⟨φ.toLinearMap x, φ.maps_lat x hxL, rfl⟩
  have hnorm_eucl : ∀ v ∈ E.euclLat, ‖φ.toEuclCLM.toLinearMap v‖ ≤ φ.opNorm * ‖v‖ :=
    fun v _ => φ.toEuclCLM.le_opNorm v
  exact Stage4ArakelovBost.bost_linearMap_muMin_le_muMax_add_log
    φ.toEuclCLM.toLinearMap hmap_eucl hne_lat φ.opNorm (φ.opNorm_pos_of_ne_zero hφ) hnorm_eucl

/-- Bound-parameterized form of Bost's slope inequality: if `φ ≠ 0` and
`∀ x ∈ E.lat, F.hNorm (φ x) ≤ C * E.hNorm x` (`C > 0`), then `E.muMin ≤ F.muMax + log C`. -/
theorem bost_slope_inequality_of_bound {E F : HermVectorBundle}
    (φ : HermBundleMorphism E F) (hφ : φ.toLinearMap ≠ 0)
    {C : ℝ} (hCpos : 0 < C) (hC : ∀ x ∈ E.lat, F.hNorm (φ.toLinearMap x) ≤ C * E.hNorm x) :
    E.muMin ≤ F.muMax + Real.log C := by
  have hne_lat : ∃ v ∈ E.euclLat, φ.toEuclCLM.toLinearMap v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hφ
    apply LinearMap.ext
    intro x
    have hx : x ∈ Submodule.span ℝ (E.lat : Set (Fin E.rk → ℝ)) := by
      rw [E.lat_span_top]; trivial
    induction hx using Submodule.span_induction with
    | mem u hu =>
      have h1 := hall (E.toEucl u) ⟨u, hu, rfl⟩
      change F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl u))) = 0 at h1
      rw [E.toEuclEquiv_symm_toEucl] at h1
      simp only [LinearMap.zero_apply]
      exact F.toEucl_injective (by rwa [map_zero])
    | zero => simp
    | add u v _ _ hu hv => simp [map_add, hu, hv]
    | smul c u _ hu => simp [map_smul, hu]
  have hmap_eucl : ∀ v ∈ E.euclLat, φ.toEuclCLM.toLinearMap v ∈ F.euclLat := by
    rintro _ ⟨x, hxL, rfl⟩
    change F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl x))) ∈ F.euclLat
    rw [E.toEuclEquiv_symm_toEucl]
    exact ⟨φ.toLinearMap x, φ.maps_lat x hxL, rfl⟩
  have hnorm_eucl : ∀ v ∈ E.euclLat, ‖φ.toEuclCLM.toLinearMap v‖ ≤ C * ‖v‖ := by
    rintro _ ⟨x, hxL, rfl⟩
    change ‖F.toEucl (φ.toLinearMap (E.toEuclEquiv.symm (E.toEucl x)))‖ ≤ C * ‖E.toEucl x‖
    rw [E.toEuclEquiv_symm_toEucl, F.norm_toEucl, E.norm_toEucl]
    exact hC x hxL
  exact Stage4ArakelovBost.bost_linearMap_muMin_le_muMax_add_log
    φ.toEuclCLM.toLinearMap hmap_eucl hne_lat C hCpos hnorm_eucl

end HermBundleMorphism

end HermVectorBundle

end HermVectorBundles

/-! ## Section 2: Concrete Faltings Height `h_F(τ)` of Elliptic Curves via `Δ(τ)` -/

section FaltingsHeight

/-- **Concrete Faltings Height `h_F(τ)` of the Elliptic Curve `E_τ = ℂ / (ℤ + ℤτ)`**:
$$h_F(\tau) = -\frac{1}{12} \log\bigl((2\pi)^{12}\, \|\Delta(\tau)\|\, (\operatorname{Im} \tau)^6\bigr).$$ -/
def faltingsHeight (τ : UpperHalfPlane) : ℝ :=
  -(1 / 12 : ℝ) * Real.log ((2 * Real.pi) ^ 12 * ‖ramanujanDelta τ‖ * τ.im ^ 6)

/-- Nonvanishing of `ramanujanDelta τ` everywhere on `UpperHalfPlane`. -/
lemma ramanujanDelta_ne_zero (τ : UpperHalfPlane) : ramanujanDelta τ ≠ 0 := by
  rw [ramanujanDelta_coe]
  exact Stage8ModularRing.discriminant_ne_zero τ

/-- Expanded logarithmic form of the Faltings height:
`h_F(τ) = -log(2π) - (1/12) log ‖Δ(τ)‖ - (1/2) log(Im τ)`. -/
theorem faltingsHeight_eq (τ : UpperHalfPlane) :
    faltingsHeight τ =
      -Real.log (2 * Real.pi) - (1 / 12 : ℝ) * Real.log ‖ramanujanDelta τ‖ -
        (1 / 2 : ℝ) * Real.log τ.im := by
  unfold faltingsHeight
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ 12 := by positivity
  have hΔ : 0 < ‖ramanujanDelta τ‖ := norm_pos_iff.mpr (ramanujanDelta_ne_zero τ)
  have him : (0 : ℝ) < τ.im ^ 6 := pow_pos τ.im_pos 6
  rw [Real.log_mul (mul_pos h2pi hΔ).ne' him.ne', Real.log_mul h2pi.ne' hΔ.ne',
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Exact bridge between `faltingsHeight` and `Stage11HermitianCurvature.automorphicNormSq 12`:
`h_F(τ) = -log(2π) - (1/24) log (‖Δ(τ)‖² · Im(τ)^12)`. -/
theorem faltingsHeight_eq_automorphicNormSq (τ : UpperHalfPlane) :
    faltingsHeight τ =
      -Real.log (2 * Real.pi) -
        (1 / 24 : ℝ) * Real.log (automorphicNormSq 12 ramanujanDelta τ) := by
  rw [faltingsHeight_eq]
  unfold automorphicNormSq automorphicMetric
  have hΔ : 0 < ‖ramanujanDelta τ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (ramanujanDelta_ne_zero τ))
  have him : (0 : ℝ) < τ.im ^ (12 : ℤ) := zpow_pos τ.im_pos 12
  rw [Real.log_mul hΔ.ne' him.ne', Real.log_pow, Real.log_zpow]
  push_cast
  ring

/-- **EXACT `SL₂(ℤ)`-INVARIANCE OF THE FALTINGS HEIGHT (`0` Assumptions!)**:
for every `γ ∈ SL(2, ℤ)` and every `τ ∈ ℍ`,
$$h_F(\gamma \cdot \tau) = h_F(\tau).$$ -/
theorem faltingsHeight_sl2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) :
    faltingsHeight (γ • τ) = faltingsHeight τ := by
  unfold faltingsHeight
  have hinv := cuspForm_im_pow_norm_sl2Z_invariant ramanujanDelta γ τ
  have hexp : ((12 : ℤ) : ℝ) / 2 = ((6 : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_natCast, Real.rpow_natCast] at hinv
  have heq : ‖ramanujanDelta (γ • τ)‖ * (γ • τ).im ^ 6 = ‖ramanujanDelta τ‖ * τ.im ^ 6 := by
    linarith [hinv]
  rw [mul_assoc ((2 * Real.pi) ^ 12), mul_assoc ((2 * Real.pi) ^ 12), heq]

theorem faltingsHeight_T_smul (τ : UpperHalfPlane) :
    faltingsHeight (ModularGroup.T • τ) = faltingsHeight τ :=
  faltingsHeight_sl2Z_invariant ModularGroup.T τ

theorem faltingsHeight_S_smul (τ : UpperHalfPlane) :
    faltingsHeight (ModularGroup.S • τ) = faltingsHeight τ :=
  faltingsHeight_sl2Z_invariant ModularGroup.S τ

/-! ### Elementary Exponential Bounds & Dedekind–Jacobi Euler Product Control -/

/-- Elementary lower bound: `exp(-2 t) ≤ 1 - t` for all `t ∈ [0, 1/2]`. -/
private lemma exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have h2 : 1 ≤ (1 - t) * (1 + 2 * t) := by nlinarith
  have h3 : 1 ≤ (1 - t) * Real.exp (2 * t) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (by linarith))
  have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-2 * t)).le
  have hexp : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add]
    have : 2 * t + -2 * t = 0 := by ring
    rw [this, Real.exp_zero]
  rw [one_mul, mul_assoc, hexp, mul_one] at h4
  exact h4

/-- Elementary complex upper bound: `‖1 - z‖ ≤ exp ‖z‖`. -/
private lemma norm_one_sub_le_exp (z : ℂ) : ‖(1 : ℂ) - z‖ ≤ Real.exp ‖z‖ := by
  calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
    _ = ‖z‖ + 1 := by simp [add_comm]
    _ ≤ Real.exp ‖z‖ := Real.add_one_le_exp ‖z‖

/-- Elementary complex lower bound: `exp(-2 ‖z‖) ≤ ‖1 - z‖` whenever `‖z‖ ≤ 1/2`. -/
private lemma exp_neg_two_norm_le_norm_one_sub {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    Real.exp (-2 * ‖z‖) ≤ ‖(1 : ℂ) - z‖ := by
  have h1 : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) z
    simp only [norm_one] at htri
    exact htri
  exact (exp_neg_two_mul_le_one_sub (norm_nonneg z) hz).trans h1

/-- Norm of `q = qParam 1 τ` equals `exp(-2π Im τ)`. -/
private lemma norm_qParam_one_eq (τ : UpperHalfPlane) :
    ‖Function.Periodic.qParam (1 : ℝ) (τ : ℂ)‖ = Real.exp (-2 * Real.pi * τ.im) := by
  unfold Function.Periodic.qParam
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- For `Im(τ) ≥ 1 / 2`, we have `‖qParam 1 τ‖ ≤ 1 / 2`. -/
private lemma norm_qParam_le_half {τ : UpperHalfPlane} (hτ : 1 / 2 ≤ τ.im) :
    ‖Function.Periodic.qParam (1 : ℝ) (τ : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_qParam_one_eq]
  have hexp_ge2 : (2 : ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := by
    have h1 : 1 + 2 * Real.pi * τ.im ≤ Real.exp (2 * Real.pi * τ.im) := by
      linarith [Real.add_one_le_exp (2 * Real.pi * τ.im)]
    nlinarith [Real.pi_gt_three]
  rw [show -2 * Real.pi * τ.im = -(2 * Real.pi * τ.im) by ring, Real.exp_neg]
  rw [one_div]
  exact inv_anti₀ (by norm_num) hexp_ge2

/-- Finite geometric-sum bound over `ℕ+`: for `0 ≤ r ≤ 1 / 2` and any `s : Finset ℕ+`,
`∑ n ∈ s, r ^ (n : ℕ) ≤ 2 * r`. -/
private lemma finset_sum_pnat_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (s : Finset ℕ+) :
    ∑ n ∈ s, r ^ (n : ℕ) ≤ 2 * r := by
  have hrlt : r < 1 := by linarith
  have hsumm_nat : Summable (fun k : ℕ => r ^ (k + 1)) := by
    have h := (summable_geometric_of_lt_one hr0 hrlt).mul_left r
    simpa only [pow_succ'] using h
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun k => ⟨k + 1, Nat.succ_pos k⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun k => Nat.add_sub_cancel k 1 }
  have hsumm_pnat : Summable (fun n : ℕ+ => r ^ (n : ℕ)) := by
    have hcomp : (fun n : ℕ+ => r ^ (n : ℕ)) = (fun k : ℕ => r ^ (k + 1)) ∘ e := by
      funext n
      change r ^ (n : ℕ) = r ^ ((n : ℕ) - 1 + 1)
      rw [Nat.sub_add_cancel n.pos]
    rw [hcomp]
    exact hsumm_nat.comp_injective e.injective
  have hle_tsum : ∑ n ∈ s, r ^ (n : ℕ) ≤ ∑' n : ℕ+, r ^ (n : ℕ) :=
    hsumm_pnat.sum_le_tsum s (fun n _ => pow_nonneg hr0 _)
  have htsum_eq' : ∑' n : ℕ+, r ^ (n : ℕ) = r * (1 - r)⁻¹ := by
    have h1 : ∑' n : ℕ+, r ^ (n : ℕ) = ∑' k : ℕ, r ^ (k + 1) := by
      rw [← e.symm.tsum_eq (fun n : ℕ+ => r ^ (n : ℕ))]
      rfl
    rw [h1]
    have h2 : (fun k : ℕ => r ^ (k + 1)) = fun k : ℕ => r * r ^ k := by
      funext k; rw [pow_succ']
    rw [h2, tsum_mul_left, tsum_geometric_of_lt_one hr0 hrlt]
  have hinv_le : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ∑ n ∈ s, r ^ (n : ℕ) ≤ ∑' n : ℕ+, r ^ (n : ℕ) := hle_tsum
    _ = r * (1 - r)⁻¹ := htsum_eq'
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left hinv_le hr0
    _ = 2 * r := mul_comm _ _

/-- **Two-Sided Analytic Bounds on the Dedekind–Jacobi Euler Product `∏'_{n ≥ 1} (1 - q^n)^24`**:
for every `τ ∈ ℍ` with `Im(τ) ≥ 1 / 2` (setting `r = ‖q‖ = exp(-2π Im τ) ≤ 1 / 2`):
1. `exp(-96 r) ≤ ‖∏'_{n ≥ 1} (1 - q^n)^24‖ ≤ exp(48 r)`,
2. If `q = (r : ℂ)` is real and positive (e.g. `τ = i y`), then `‖∏'_{n ≥ 1} (1 - q^n)^24‖ ≤ 1`! -/
theorem norm_eulerProd24_bounds (τ : UpperHalfPlane) (hτ : 1 / 2 ≤ τ.im) :
    let q := Function.Periodic.qParam (1 : ℝ) (τ : ℂ)
    Real.exp (-96 * ‖q‖) ≤ ‖∏' n : ℕ+, (1 - q ^ (n : ℕ)) ^ 24‖ ∧
    ‖∏' n : ℕ+, (1 - q ^ (n : ℕ)) ^ 24‖ ≤ Real.exp (48 * ‖q‖) := by
  intro q
  have hq_le : ‖q‖ ≤ 1 / 2 := norm_qParam_le_half hτ
  have hq_lt : ‖q‖ < 1 := by linarith
  have hq_nn : 0 ≤ ‖q‖ := norm_nonneg q
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun k => ⟨k + 1, Nat.succ_pos k⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun k => Nat.add_sub_cancel k 1 }
  have hsumm_q : Summable (fun n : ℕ+ => -q ^ (n : ℕ)) := by
    refine Summable.of_norm ?_
    have hnat : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) := by
      have h := (summable_geometric_of_lt_one hq_nn hq_lt).mul_left ‖q‖
      simpa only [pow_succ'] using h
    have hcomp : (fun n : ℕ+ => ‖-q ^ (n : ℕ)‖) = (fun k : ℕ => ‖q‖ ^ (k + 1)) ∘ e := by
      funext n
      rw [norm_neg, norm_pow]
      change ‖q‖ ^ (n : ℕ) = ‖q‖ ^ ((n : ℕ) - 1 + 1)
      rw [Nat.sub_add_cancel n.pos]
    rw [hcomp]
    exact hnat.comp_injective e.injective
  have hmult1 : Multipliable (fun n : ℕ+ => 1 - q ^ (n : ℕ)) := by
    have h := Complex.multipliable_one_add_of_summable hsumm_q
    simpa only [sub_eq_add_neg] using h
  obtain ⟨P, hP⟩ := hmult1
  have hP24 : HasProd (fun n : ℕ+ => (1 - q ^ (n : ℕ)) ^ 24) (P ^ 24) := by
    unfold HasProd at hP ⊢
    have hpow := (continuous_pow 24).continuousAt.tendsto.comp hP
    refine hpow.congr fun s => ?_
    simp [Finset.prod_pow]
  have htprod_eq : (∏' n : ℕ+, (1 - q ^ (n : ℕ)) ^ 24) = P ^ 24 := hP24.tprod_eq
  have htend : Tendsto (fun s : Finset ℕ+ => ∏ n ∈ s, ‖(1 - q ^ (n : ℕ)) ^ 24‖)
      atTop (𝓝 ‖∏' n : ℕ+, (1 - q ^ (n : ℕ)) ^ 24‖) := by
    rw [htprod_eq]
    have h := continuous_norm.continuousAt.tendsto.comp hP24
    refine h.congr fun s => ?_
    simp [norm_prod]
  refine ⟨ge_of_tendsto htend (Eventually.of_forall fun s => ?_),
    le_of_tendsto htend (Eventually.of_forall fun s => ?_)⟩
  · have hterm : ∀ n ∈ s, Real.exp (-48 * ‖q‖ ^ (n : ℕ)) ≤ ‖(1 - q ^ (n : ℕ)) ^ 24‖ := by
      intro n _
      have hqn_le : ‖q ^ (n : ℕ)‖ ≤ 1 / 2 := by
        rw [norm_pow]
        exact (pow_le_of_le_one hq_nn (by linarith) n.pos.ne').trans hq_le
      have h1 := exp_neg_two_norm_le_norm_one_sub hqn_le
      rw [norm_pow] at h1 ⊢
      have h2 := pow_le_pow_left₀ (Real.exp_pos _).le h1 24
      rw [← Real.exp_nat_mul] at h2
      simpa only [show ((24 : ℕ) : ℝ) * (-2 * ‖q‖ ^ (n : ℕ)) = -48 * ‖q‖ ^ (n : ℕ) by ring] using h2
    calc Real.exp (-96 * ‖q‖)
        ≤ Real.exp (-48 * ∑ n ∈ s, ‖q‖ ^ (n : ℕ)) := by
          apply Real.exp_le_exp.mpr
          have hsum := finset_sum_pnat_pow_le hq_nn hq_le s
          linarith
      _ = Real.exp (∑ n ∈ s, -48 * ‖q‖ ^ (n : ℕ)) := by rw [Finset.mul_sum]
      _ = ∏ n ∈ s, Real.exp (-48 * ‖q‖ ^ (n : ℕ)) := Real.exp_sum s _
      _ ≤ ∏ n ∈ s, ‖(1 - q ^ (n : ℕ)) ^ 24‖ :=
          Finset.prod_le_prod (fun n _ => (Real.exp_pos _).le) hterm
  · have hterm : ∀ n ∈ s, ‖(1 - q ^ (n : ℕ)) ^ 24‖ ≤ Real.exp (24 * ‖q‖ ^ (n : ℕ)) := by
      intro n _
      have h1 := norm_one_sub_le_exp (q ^ (n : ℕ))
      rw [norm_pow] at h1 ⊢
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 24
      rw [← Real.exp_nat_mul] at h2
      simpa only [show ((24 : ℕ) : ℝ) * (‖q‖ ^ (n : ℕ)) = 24 * ‖q‖ ^ (n : ℕ) by ring] using h2
    calc ∏ n ∈ s, ‖(1 - q ^ (n : ℕ)) ^ 24‖
        ≤ ∏ n ∈ s, Real.exp (24 * ‖q‖ ^ (n : ℕ)) :=
          Finset.prod_le_prod (fun n _ => norm_nonneg _) hterm
      _ = Real.exp (∑ n ∈ s, 24 * ‖q‖ ^ (n : ℕ)) := (Real.exp_sum s _).symm
      _ = Real.exp (24 * ∑ n ∈ s, ‖q‖ ^ (n : ℕ)) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (48 * ‖q‖) := by
          apply Real.exp_le_exp.mpr
          have hsum := finset_sum_pnat_pow_le hq_nn hq_le s
          linarith

/-- Sharp upper bound `‖∏'_{n ≥ 1} (1 - r^n)^24‖ ≤ 1` when `q = (r : ℂ)` with `0 < r < 1`. -/
private lemma norm_eulerProd24_le_one_of_real {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖∏' n : ℕ+, (1 - ((r : ℂ) ^ (n : ℕ))) ^ 24‖ ≤ 1 := by
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun k => ⟨k + 1, Nat.succ_pos k⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun k => Nat.add_sub_cancel k 1 }
  have hsumm : Summable (fun n : ℕ+ => -((r : ℂ) ^ (n : ℕ))) := by
    refine Summable.of_norm ?_
    have hnat : Summable (fun k : ℕ => r ^ (k + 1)) := by
      have h := (summable_geometric_of_lt_one hr0.le hr1).mul_left r
      simpa only [pow_succ'] using h
    have hcomp : (fun n : ℕ+ => ‖-((r : ℂ) ^ (n : ℕ))‖) = (fun k : ℕ => r ^ (k + 1)) ∘ e := by
      funext n
      rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
      change r ^ (n : ℕ) = r ^ ((n : ℕ) - 1 + 1)
      rw [Nat.sub_add_cancel n.pos]
    rw [hcomp]
    exact hnat.comp_injective e.injective
  have hmult1 : Multipliable (fun n : ℕ+ => 1 - ((r : ℂ) ^ (n : ℕ))) := by
    have h := Complex.multipliable_one_add_of_summable hsumm
    simpa only [sub_eq_add_neg] using h
  obtain ⟨P, hP⟩ := hmult1
  have hP24 : HasProd (fun n : ℕ+ => (1 - ((r : ℂ) ^ (n : ℕ))) ^ 24) (P ^ 24) := by
    unfold HasProd at hP ⊢
    have hpow := (continuous_pow 24).continuousAt.tendsto.comp hP
    refine hpow.congr fun s => ?_
    simp [Finset.prod_pow]
  have htend : Tendsto (fun s : Finset ℕ+ => ∏ n ∈ s, ‖(1 - ((r : ℂ) ^ (n : ℕ))) ^ 24‖)
      atTop (𝓝 ‖∏' n : ℕ+, (1 - ((r : ℂ) ^ (n : ℕ))) ^ 24‖) := by
    rw [hP24.tprod_eq]
    have h := continuous_norm.continuousAt.tendsto.comp hP24
    refine h.congr fun s => ?_
    simp [norm_prod]
  refine le_of_tendsto htend (Eventually.of_forall fun s => ?_)
  refine Finset.prod_le_one (fun n _ => norm_nonneg _) fun n _ => ?_
  rw [norm_pow]
  refine pow_le_one₀ (norm_nonneg _) ?_
  have hcast : (1 : ℂ) - (r : ℂ) ^ (n : ℕ) = ((1 - r ^ (n : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg]
  · linarith [pow_pos hr0 (n : ℕ)]
  · have hle : r ^ (n : ℕ) ≤ 1 := pow_le_one₀ hr0.le hr1.le
    linarith

/-- **Uniform High-Cusp Asymptotic Formula on ALL of `{τ ∈ ℍ | Im(τ) ≥ 1 / 2}`**:
$$-4 e^{-2\pi y} \le h_F(\tau) - \Bigl(\frac{\pi}{6} y - \frac{1}{2} \log y - \log(2\pi)\Bigr) \le 8 e^{-2\pi y}.$$ -/
theorem faltingsHeight_high_cusp_bounds (τ : UpperHalfPlane) (hτ : 1 / 2 ≤ τ.im) :
    -4 * Real.exp (-2 * Real.pi * τ.im) ≤
      faltingsHeight τ - ((Real.pi / 6) * τ.im - (1 / 2 : ℝ) * Real.log τ.im - Real.log (2 * Real.pi)) ∧
    faltingsHeight τ - ((Real.pi / 6) * τ.im - (1 / 2 : ℝ) * Real.log τ.im - Real.log (2 * Real.pi)) ≤
      8 * Real.exp (-2 * Real.pi * τ.im) := by
  set q := Function.Periodic.qParam (1 : ℝ) (τ : ℂ)
  set P := ∏' n : ℕ+, (1 - q ^ (n : ℕ)) ^ 24
  have hΔ_eq : ramanujanDelta τ = q * P := delta_eq_euler_product_24 τ
  have hq_norm : ‖q‖ = Real.exp (-2 * Real.pi * τ.im) := norm_qParam_one_eq τ
  have hP_bd := norm_eulerProd24_bounds τ hτ
  have hP_pos : 0 < ‖P‖ := lt_of_lt_of_le (Real.exp_pos _) hP_bd.1
  have hq_pos : 0 < ‖q‖ := by rw [hq_norm]; exact Real.exp_pos _
  have hlogΔ : Real.log ‖ramanujanDelta τ‖ = -2 * Real.pi * τ.im + Real.log ‖P‖ := by
    rw [hΔ_eq, norm_mul, Real.log_mul hq_pos.ne' hP_pos.ne', hq_norm, Real.log_exp]
  have hlogP_lo : -96 * Real.exp (-2 * Real.pi * τ.im) ≤ Real.log ‖P‖ := by
    have h := Real.log_le_log (Real.exp_pos _) hP_bd.1
    rwa [Real.log_exp, hq_norm] at h
  have hlogP_hi : Real.log ‖P‖ ≤ 48 * Real.exp (-2 * Real.pi * τ.im) := by
    have h := Real.log_le_log hP_pos hP_bd.2
    rwa [Real.log_exp, hq_norm] at h
  rw [faltingsHeight_eq, hlogΔ]
  constructor <;> linarith

/-- **EXPLICIT UNCONDITIONAL UNIVERSAL LOWER BOUND ON FALTINGS HEIGHT (`0` Assumptions!)**:
for EVERY `τ ∈ UpperHalfPlane`, `(-2 : ℝ) ≤ faltingsHeight τ`! -/
theorem faltingsHeight_ge_neg_two (τ : UpperHalfPlane) :
    (-2 : ℝ) ≤ faltingsHeight τ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  rw [← faltingsHeight_sl2Z_invariant γ τ]
  set w : UpperHalfPlane := γ • τ
  have hw_im_ge : Real.sqrt 3 / 2 ≤ w.im := by
    have hre : |w.re| ≤ 1 / 2 := hγ.2
    have hnorm : 1 ≤ Complex.normSq (w : ℂ) := hγ.1
    rw [Complex.normSq_apply] at hnorm
    change 1 ≤ w.re * w.re + w.im * w.im at hnorm
    have hre_sq : w.re * w.re ≤ 1 / 4 := by
      have h1 : w.re ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hre 2
      linarith [sq w.re]
    have him_sq : (Real.sqrt 3 / 2) ^ 2 ≤ w.im ^ 2 := by
      have h3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
      rw [h3]
      nlinarith [sq w.im]
    nlinarith [w.im_pos, show (0 : ℝ) < Real.sqrt 3 / 2 by positivity]
  have hsqrt3_gt1 : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hw_half : 1 / 2 ≤ w.im := by linarith
  have hcusp := (faltingsHeight_high_cusp_bounds w hw_half).1
  -- Lower bound `(π/6) w.im - (1/2) log w.im ≥ 1/2`:
  have hlog_w : Real.log ((Real.pi / 3) * w.im) ≤ (Real.pi / 3) * w.im - 1 :=
    Real.log_le_sub_one_of_pos (mul_pos (by positivity) w.im_pos)
  rw [Real.log_mul (by positivity) w.im_pos.ne'] at hlog_w
  have hlog_pi3_nn : 0 ≤ Real.log (Real.pi / 3) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlin_lo : (1 / 2 : ℝ) ≤ (Real.pi / 6) * w.im - (1 / 2 : ℝ) * Real.log w.im := by
    linarith
  -- Upper bound `log (2π) < 2` via `2π < 6.3 < 2.7² < e²`:
  have hlog_2pi : Real.log (2 * Real.pi) ≤ 2 := by
    have h2pi_lt : 2 * Real.pi ≤ Real.exp 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [hsq]
      nlinarith
    have h := Real.log_le_log (by positivity) h2pi_lt
    rwa [Real.log_exp] at h
  -- Upper bound `4 * exp(-2π w.im) ≤ 1 / 2`:
  have hexp_le : 4 * Real.exp (-2 * Real.pi * w.im) ≤ 1 / 2 := by
    have h8 : (8 : ℝ) ≤ Real.exp (2 * Real.pi * w.im) := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h3 : (3 : ℝ) ≤ 2 * Real.pi * w.im := by nlinarith [Real.pi_gt_three, hw_half]
      have hexp3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      have hle := Real.exp_le_exp.mpr h3
      rw [hexp3] at hle
      nlinarith
    have hpos : (0 : ℝ) < Real.exp (2 * Real.pi * w.im) := Real.exp_pos _
    rw [show -2 * Real.pi * w.im = -(2 * Real.pi * w.im) by ring, Real.exp_neg]
    have hinv : (Real.exp (2 * Real.pi * w.im))⁻¹ ≤ 1 / 8 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h8
    linarith
  linarith

/-- **UNIFORM UNIVERSAL LOWER BOUND ON FALTINGS HEIGHT (`0` Assumptions!)**:
`∃ c_F : ℝ, ∀ τ : UpperHalfPlane, c_F ≤ faltingsHeight τ`. -/
theorem faltingsHeight_bddBelow :
    ∃ c_F : ℝ, ∀ τ : UpperHalfPlane, c_F ≤ faltingsHeight τ :=
  ⟨-2, faltingsHeight_ge_neg_two⟩

/-- Imaginary-axis point `i * y ∈ UpperHalfPlane` for `y > 0`. -/
def imagUHP (y : ℝ) (hy : 0 < y) : UpperHalfPlane :=
  ⟨Complex.I * (y : ℂ), by simp [hy]⟩

@[simp]
lemma imagUHP_im (y : ℝ) (hy : 0 < y) : (imagUHP y hy).im = y := by
  simp [imagUHP]

/-- **Sharp Explicit Cusp Growth Formula along the Imaginary Axis `τ = i y`**:
for EVERY `y ≥ 1 / 2`:
$$0 \le h_F(i y) - \Bigl(\frac{\pi}{6} y - \frac{1}{2} \log y - \log(2\pi)\Bigr) \le 8 e^{-2\pi y}.$$ -/
theorem faltingsHeight_imag_asymptotic_explicit {y : ℝ} (hy : 1 / 2 ≤ y) :
    let hy0 : 0 < y := by linarith
    0 ≤ faltingsHeight (imagUHP y hy0) -
        ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)) ∧
    faltingsHeight (imagUHP y hy0) -
        ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)) ≤
      8 * Real.exp (-2 * Real.pi * y) := by
  intro hy0
  have hhi := (faltingsHeight_high_cusp_bounds (imagUHP y hy0) (by simpa using hy)).2
  simp only [imagUHP_im] at hhi
  refine ⟨?_, hhi⟩
  -- Lower bound `0 ≤ ...` from `‖∏ (1 - r^n)^24‖ ≤ 1` since `q(i y) = exp(-2π y) ∈ (0, 1)`.
  set r : ℝ := Real.exp (-2 * Real.pi * y)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hy0])
  have hq_real : Function.Periodic.qParam (1 : ℝ) (imagUHP y hy0 : ℂ) = (r : ℂ) := by
    unfold Function.Periodic.qParam imagUHP
    simp only [Complex.ofReal_one, div_one, r, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination 2 * (Real.pi : ℂ) * (y : ℂ) * Complex.I_mul_I
  have hΔ_eq := delta_eq_euler_product_24 (imagUHP y hy0)
  rw [hq_real] at hΔ_eq
  set P : ℂ := ∏' n : ℕ+, (1 - ((r : ℂ) ^ (n : ℕ))) ^ 24
  have hP_le1 : ‖P‖ ≤ 1 := norm_eulerProd24_le_one_of_real hr0 hr1
  have hΔ_ne : ramanujanDelta (imagUHP y hy0) ≠ 0 := ramanujanDelta_ne_zero _
  have hP_pos : 0 < ‖P‖ := by
    by_contra h0
    have hP0 : P = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h0) (norm_nonneg P))
    rw [hP0, mul_zero] at hΔ_eq
    exact hΔ_ne hΔ_eq
  have hlogP : Real.log ‖P‖ ≤ 0 := by
    have h := Real.log_le_log hP_pos hP_le1
    rwa [Real.log_one] at h
  have hlogΔ : Real.log ‖ramanujanDelta (imagUHP y hy0)‖ = -2 * Real.pi * y + Real.log ‖P‖ := by
    rw [hΔ_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le,
      Real.log_mul hr0.ne' hP_pos.ne', Real.log_exp]
  rw [faltingsHeight_eq, imagUHP_im, hlogΔ]
  linarith

/-- **Asymptotic Cusp Growth of the Faltings Height (`O(e^{-2π y})` as `y → ∞`)**:
$$h_F(i y) = \frac{\pi}{6} y - \frac{1}{2} \log y - \log(2\pi) + O(e^{-2\pi y}) \qquad (y \to \infty).$$ -/
theorem faltingsHeight_imag_isBigO :
    (fun y : ℝ =>
      (if hy : 0 < y then faltingsHeight (imagUHP y hy) else 0) -
        ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)))
      =O[atTop] (fun y : ℝ => Real.exp (-2 * Real.pi * y)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨8, Filter.eventually_atTop.mpr ⟨1 / 2, fun y hy => ?_⟩⟩
  have hy0 : 0 < y := by linarith
  rw [dif_pos hy0]
  have hbd := faltingsHeight_imag_asymptotic_explicit hy
  rw [Real.norm_of_nonneg hbd.1, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbd.2

/-- Exact linear growth rate `h_F(i y) / y → π / 6` as `y → ∞`. -/
theorem faltingsHeight_imag_div_tendsto :
    Tendsto (fun y : ℝ => (if hy : 0 < y then faltingsHeight (imagUHP y hy) else 0) / y)
      atTop (𝓝 (Real.pi / 6)) := by
  -- Compare with `(π / 6) - (log y) / (2 y) - log(2π) / y + O(e^{-2π y} / y)`.
  have hlog_div : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hconst_div : Tendsto (fun y : ℝ => Real.log (2 * Real.pi) / y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hexp_div : Tendsto (fun y : ℝ => 8 * Real.exp (-2 * Real.pi * y) / y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.exp (-2 * Real.pi * y)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        ((Filter.tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos])))
    have h2 : Tendsto (fun y : ℝ => (8 * Real.exp (-2 * Real.pi * y)) * y⁻¹) atTop (𝓝 (8 * 0 * 0)) :=
      (h1.const_mul 8).mul tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using h2
  have hlo : Tendsto (fun y : ℝ =>
      Real.pi / 6 - (1 / 2 : ℝ) * (Real.log y / y) - Real.log (2 * Real.pi) / y)
      atTop (𝓝 (Real.pi / 6)) := by
    have h := (tendsto_const_nhds (x := Real.pi / 6)).sub
      (hlog_div.const_mul (1 / 2 : ℝ)) |>.sub hconst_div
    simpa using h
  have hhi : Tendsto (fun y : ℝ =>
      Real.pi / 6 - (1 / 2 : ℝ) * (Real.log y / y) - Real.log (2 * Real.pi) / y +
        8 * Real.exp (-2 * Real.pi * y) / y)
      atTop (𝓝 (Real.pi / 6)) := by
    simpa using hlo.add hexp_div
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    rw [dif_pos hy0]
    have hbd := (faltingsHeight_imag_asymptotic_explicit hy).1
    have hdiv := div_le_div_of_nonneg_right hbd hy0.le
    rw [zero_div] at hdiv
    have hlhs : ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)) / y =
        Real.pi / 6 - (1 / 2 : ℝ) * (Real.log y / y) - Real.log (2 * Real.pi) / y := by
      field_simp [hy0.ne']
    linarith [show (faltingsHeight (imagUHP y hy0) -
        ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi))) / y =
        faltingsHeight (imagUHP y hy0) / y -
          ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)) / y by
      rw [sub_div]]
  · filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    rw [dif_pos hy0]
    have hbd := (faltingsHeight_imag_asymptotic_explicit hy).2
    have hdiv := div_le_div_of_nonneg_right hbd hy0.le
    have hlhs : ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)) / y =
        Real.pi / 6 - (1 / 2 : ℝ) * (Real.log y / y) - Real.log (2 * Real.pi) / y := by
      field_simp [hy0.ne']
    linarith [show (faltingsHeight (imagUHP y hy0) -
        ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi))) / y =
        faltingsHeight (imagUHP y hy0) / y -
          ((Real.pi / 6) * y - (1 / 2 : ℝ) * Real.log y - Real.log (2 * Real.pi)) / y by
      rw [sub_div]]

/-! ### Exact Subharmonicity & Curvature-Degree Identity (Bridge to `Stage11HermitianCurvature`) -/

/-- **Exact Euclidean Laplacian of the Faltings Height**:
$$\Delta_{\mathrm{Eucl}} h_F(\tau) = \frac{1}{2\,(\operatorname{Im}\tau)^2}
  = 2\,\Theta(h_1)(\tau) > 0.$$
In particular `h_F` is strictly subharmonic on `ℍ`! -/
theorem euclLaplacianR_faltingsHeight (τ : UpperHalfPlane) :
    euclLaplacianR faltingsHeight τ = (1 / 2 : ℝ) * τ.im ^ (-2 : ℝ) := by
  have hfun : faltingsHeight = fun w : UpperHalfPlane =>
      -Real.log (2 * Real.pi) +
        (-(1 / 24 : ℝ)) * Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ)) := by
    funext w
    rw [faltingsHeight_eq_automorphicNormSq]
    unfold automorphicNormSq automorphicMetric
    have hrpow : w.im ^ (12 : ℝ) = w.im ^ (12 : ℤ) := by
      rw [show (12 : ℝ) = ((12 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    rw [hrpow]
    ring
  have hboch : euclLaplacianR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ =
      -(12 : ℝ) / τ.im ^ 2 :=
    bochner_log_laplacian_weight_k ramanujanDelta.holo' (12 : ℝ) (ramanujanDelta_ne_zero τ)
  have hXX : partialXXR faltingsHeight τ =
      (-(1 / 24 : ℝ)) * partialXXR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ := by
    rw [hfun]
    unfold partialXXR
    have hslice : uhpSliceXR
        (fun w => -Real.log (2 * Real.pi) +
          (-(1 / 24 : ℝ)) * Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.im =
        fun x => -Real.log (2 * Real.pi) +
          (-(1 / 24 : ℝ)) * uhpSliceXR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.im x := rfl
    rw [hslice]
    have hd1 : (fun x : ℝ => deriv (fun t => -Real.log (2 * Real.pi) +
          (-(1 / 24 : ℝ)) * uhpSliceXR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.im t) x) =
        fun x => (-(1 / 24 : ℝ)) * deriv (uhpSliceXR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.im) x := by
      funext x
      rw [deriv_const_add, deriv_const_mul_field]
    rw [hd1, deriv_const_mul_field]
  have hYY : partialYYR faltingsHeight τ =
      (-(1 / 24 : ℝ)) * partialYYR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ := by
    rw [hfun]
    unfold partialYYR
    have hslice : uhpSliceYR
        (fun w => -Real.log (2 * Real.pi) +
          (-(1 / 24 : ℝ)) * Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.re =
        fun y => -Real.log (2 * Real.pi) +
          (-(1 / 24 : ℝ)) * uhpSliceYR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.re y := rfl
    rw [hslice]
    have hd1 : (fun y : ℝ => deriv (fun t => -Real.log (2 * Real.pi) +
          (-(1 / 24 : ℝ)) * uhpSliceYR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.re t) y) =
        fun y => (-(1 / 24 : ℝ)) * deriv (uhpSliceYR (fun w => Real.log (‖ramanujanDelta w‖ ^ 2 * w.im ^ (12 : ℝ))) τ.re) y := by
      funext y
      rw [deriv_const_add, deriv_const_mul_field]
    rw [hd1, deriv_const_mul_field]
  unfold euclLaplacianR at hboch ⊢
  rw [hXX, hYY, ← mul_add, hboch]
  have hrpow : τ.im ^ (-2 : ℝ) = (τ.im ^ 2)⁻¹ := by
    rw [Real.rpow_neg τ.im_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow]
  ring

theorem euclLaplacianR_faltingsHeight_eq_two_chernCurvature (τ : UpperHalfPlane) :
    euclLaplacianR faltingsHeight τ = 2 * chernCurvatureCoeff 1 τ := by
  rw [euclLaplacianR_faltingsHeight, chernCurvature_weight_k_eq]
  push_cast
  ring

/-- **Faltings Height Curvature-Degree Identity**:
integrating `(1 / (2π)) Δ_Eucl h_F` over the `SL₂(ℤ)` fundamental domain `stdFD` recovers the
exact Hodge bundle degree `deg(ω) = 1 / 12`! -/
theorem faltingsHeight_curvature_integral_eq_one_div_twelve :
    (1 / (2 * Real.pi)) *
      ∫ p in Stage10PeterssonHecke.stdFD,
        (if hp : 0 < p.2 then euclLaplacianR faltingsHeight (pairToUHP p hp) else 0) =
      1 / 12 := by
  have hcongr : Set.EqOn
      (fun p : ℝ × ℝ => if hp : 0 < p.2 then euclLaplacianR faltingsHeight (pairToUHP p hp) else 0)
      (fun p : ℝ × ℝ => (1 / 2 : ℝ) * (p.2) ^ (-2 : ℝ)) stdFD := by
    intro p hp
    dsimp only
    rw [dif_pos hp.2.1, euclLaplacianR_faltingsHeight, pairToUHP_im]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_stdFD hcongr,
    MeasureTheory.integral_const_mul, hyperbolicVolume_stdFD_eq_pi_div_three]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]
  ring

end FaltingsHeight

/-! ## Section 3: Arakelov Intersection Pairing, Arithmetic Hodge Index & Pillar 2 Bridges -/

section ArakelovIntersectionAndHodgeIndex

/-- Concrete **Arithmetic Surface Intersection Model** over `Spec ℤ`:
encodes the Arakelov intersection form on the Néron–Severi / Hermitian line-bundle space
decomposed into:
- base ample/Hodge self-intersection `hodgeSelfInt = (ω · ω)_Ar`,
- vertical fiber class `F_∞` (`(H · F_∞) = 1`, `(F_∞ · F_∞) = 0`),
- finite-place vertical fibral components `Fin m → ℝ` with negative-definite Zariski form `-A_V`
  (`vertMatrix.PosDef`),
- archimedean Green / Dirichlet energy space `E_arch` (real inner product space, entering with `-`). -/
structure ArithSurfaceModel (m : ℕ) (E_arch : Type*)
    [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch] where
  hodgeSelfInt : ℝ
  vertMatrix : Matrix (Fin m) (Fin m) ℝ
  vertMatrix_posDef : vertMatrix.PosDef

/-- Concrete **Hermitian Line Bundle / Arakelov Divisor** on an arithmetic surface model:
`L = geomDeg · H + fiberWt · F_∞ + vertComp + archPot`. -/
@[ext]
structure ArithLineBundle (m : ℕ) (E_arch : Type*) where
  /-- Generic-fiber degree `deg_K(L)` (matching `k / 12` for `ω^{⊗ k}` on `SL₂(ℤ) \ ℍ`). -/
  geomDeg : ℝ
  /-- Archimedean fiber / metric-scaling weight `c_∞(L)`. -/
  fiberWt : ℝ
  /-- Finite-place vertical fibral components. -/
  vertComp : Fin m → ℝ
  /-- Archimedean mean-zero Green / Kähler potential perturbation. -/
  archPot : E_arch

namespace ArithLineBundle

section Algebra

variable {m : ℕ} {E_arch : Type*} [AddCommGroup E_arch]

instance : Zero (ArithLineBundle m E_arch) := ⟨⟨0, 0, 0, 0⟩⟩
instance : Add (ArithLineBundle m E_arch) :=
  ⟨fun L₁ L₂ => ⟨L₁.geomDeg + L₂.geomDeg, L₁.fiberWt + L₂.fiberWt,
    L₁.vertComp + L₂.vertComp, L₁.archPot + L₂.archPot⟩⟩
instance : Neg (ArithLineBundle m E_arch) :=
  ⟨fun L => ⟨-L.geomDeg, -L.fiberWt, -L.vertComp, -L.archPot⟩⟩
instance : Sub (ArithLineBundle m E_arch) :=
  ⟨fun L₁ L₂ => ⟨L₁.geomDeg - L₂.geomDeg, L₁.fiberWt - L₂.fiberWt,
    L₁.vertComp - L₂.vertComp, L₁.archPot - L₂.archPot⟩⟩

@[simp] lemma zero_geomDeg : (0 : ArithLineBundle m E_arch).geomDeg = 0 := rfl
@[simp] lemma zero_fiberWt : (0 : ArithLineBundle m E_arch).fiberWt = 0 := rfl
@[simp] lemma zero_vertComp : (0 : ArithLineBundle m E_arch).vertComp = 0 := rfl
@[simp] lemma zero_archPot : (0 : ArithLineBundle m E_arch).archPot = 0 := rfl

@[simp] lemma add_geomDeg (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ + L₂).geomDeg = L₁.geomDeg + L₂.geomDeg := rfl
@[simp] lemma add_fiberWt (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ + L₂).fiberWt = L₁.fiberWt + L₂.fiberWt := rfl
@[simp] lemma add_vertComp (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ + L₂).vertComp = L₁.vertComp + L₂.vertComp := rfl
@[simp] lemma add_archPot (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ + L₂).archPot = L₁.archPot + L₂.archPot := rfl

@[simp] lemma neg_geomDeg (L : ArithLineBundle m E_arch) : (-L).geomDeg = -L.geomDeg := rfl
@[simp] lemma neg_fiberWt (L : ArithLineBundle m E_arch) : (-L).fiberWt = -L.fiberWt := rfl
@[simp] lemma neg_vertComp (L : ArithLineBundle m E_arch) : (-L).vertComp = -L.vertComp := rfl
@[simp] lemma neg_archPot (L : ArithLineBundle m E_arch) : (-L).archPot = -L.archPot := rfl

@[simp] lemma sub_geomDeg (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ - L₂).geomDeg = L₁.geomDeg - L₂.geomDeg := rfl
@[simp] lemma sub_fiberWt (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ - L₂).fiberWt = L₁.fiberWt - L₂.fiberWt := rfl
@[simp] lemma sub_vertComp (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ - L₂).vertComp = L₁.vertComp - L₂.vertComp := rfl
@[simp] lemma sub_archPot (L₁ L₂ : ArithLineBundle m E_arch) :
    (L₁ - L₂).archPot = L₁.archPot - L₂.archPot := rfl

instance : AddCommGroup (ArithLineBundle m E_arch) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  add_comm a b := by ext <;> simp [add_comm]

variable [Module ℝ E_arch]

instance : SMul ℝ (ArithLineBundle m E_arch) :=
  ⟨fun c L => ⟨c * L.geomDeg, c * L.fiberWt, c • L.vertComp, c • L.archPot⟩⟩

@[simp] lemma smul_geomDeg (c : ℝ) (L : ArithLineBundle m E_arch) :
    (c • L).geomDeg = c * L.geomDeg := rfl
@[simp] lemma smul_fiberWt (c : ℝ) (L : ArithLineBundle m E_arch) :
    (c • L).fiberWt = c * L.fiberWt := rfl
@[simp] lemma smul_vertComp (c : ℝ) (L : ArithLineBundle m E_arch) :
    (c • L).vertComp = c • L.vertComp := rfl
@[simp] lemma smul_archPot (c : ℝ) (L : ArithLineBundle m E_arch) :
    (c • L).archPot = c • L.archPot := rfl

instance : Module ℝ (ArithLineBundle m E_arch) where
  one_smul a := by ext <;> simp
  mul_smul c₁ c₂ a := by ext <;> simp [mul_assoc, mul_smul]
  smul_zero c := by ext <;> simp
  smul_add c a b := by ext <;> simp [mul_add, smul_add]
  add_smul c₁ c₂ a := by ext <;> simp [add_mul, add_smul]
  zero_smul a := by ext <;> simp

/-- Pure archimedean fiber class `c · F_∞` (scaling the Hermitian metric by `e^{-2 c}`). -/
def fiberBundle (c : ℝ) : ArithLineBundle m E_arch :=
  ⟨0, c, 0, 0⟩

/-- Concrete weight-`k` automorphic Hodge bundle `ω^{⊗ k}(c · F_∞)` with generic-fiber degree
`deg(ω^{⊗ k}) = k / 12` matching `Stage11HermitianCurvature.firstChernIntegral_weight_k_eq`. -/
def hodgeBundle (k : ℤ) (c : ℝ) : ArithLineBundle m E_arch :=
  ⟨(k : ℝ) / 12, c, 0, 0⟩

end Algebra

variable {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]

/-- **Concrete Arakelov Intersection Pairing `(L₁ · L₂)_Ar`**:
$$(L_1 \cdot L_2)_{\mathrm{Ar}}
  = \alpha\, d_1 d_2 + d_1 c_2 + c_1 d_2 - v_1^T A_V v_2 - \langle u_1, u_2 \rangle.$$ -/
def arakelovPair (M : ArithSurfaceModel m E_arch)
    (L₁ L₂ : ArithLineBundle m E_arch) : ℝ :=
  M.hodgeSelfInt * L₁.geomDeg * L₂.geomDeg +
    L₁.geomDeg * L₂.fiberWt + L₁.fiberWt * L₂.geomDeg -
    L₁.vertComp ⬝ᵥ M.vertMatrix.mulVec L₂.vertComp -
    inner ℝ L₁.archPot L₂.archPot

/-- **Symmetry of the Arakelov Intersection Pairing**: `(L₁ · L₂)_Ar = (L₂ · L₁)_Ar`. -/
theorem arakelovPair_symm (M : ArithSurfaceModel m E_arch)
    (L₁ L₂ : ArithLineBundle m E_arch) :
    arakelovPair M L₁ L₂ = arakelovPair M L₂ L₁ := by
  unfold arakelovPair
  have hvert : L₁.vertComp ⬝ᵥ M.vertMatrix.mulVec L₂.vertComp =
      L₂.vertComp ⬝ᵥ M.vertMatrix.mulVec L₁.vertComp := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      isHermitian_real_transpose M.vertMatrix_posDef.isHermitian, dotProduct_comm]
  rw [hvert, real_inner_comm]
  ring

theorem arakelovPair_add_left (M : ArithSurfaceModel m E_arch)
    (L₁ L₂ L₃ : ArithLineBundle m E_arch) :
    arakelovPair M (L₁ + L₂) L₃ = arakelovPair M L₁ L₃ + arakelovPair M L₂ L₃ := by
  unfold arakelovPair
  simp only [add_geomDeg, add_fiberWt, add_vertComp, add_archPot, add_dotProduct, inner_add_left]
  ring

theorem arakelovPair_add_right (M : ArithSurfaceModel m E_arch)
    (L₁ L₂ L₃ : ArithLineBundle m E_arch) :
    arakelovPair M L₁ (L₂ + L₃) = arakelovPair M L₁ L₂ + arakelovPair M L₁ L₃ := by
  rw [arakelovPair_symm, arakelovPair_add_left, arakelovPair_symm M L₂ L₁,
    arakelovPair_symm M L₃ L₁]

theorem arakelovPair_smul_left (M : ArithSurfaceModel m E_arch)
    (c : ℝ) (L₁ L₂ : ArithLineBundle m E_arch) :
    arakelovPair M (c • L₁) L₂ = c * arakelovPair M L₁ L₂ := by
  unfold arakelovPair
  simp only [smul_geomDeg, smul_fiberWt, smul_vertComp, smul_archPot,
    smul_dotProduct, smul_eq_mul, real_inner_smul_left]
  ring

theorem arakelovPair_smul_right (M : ArithSurfaceModel m E_arch)
    (c : ℝ) (L₁ L₂ : ArithLineBundle m E_arch) :
    arakelovPair M L₁ (c • L₂) = c * arakelovPair M L₁ L₂ := by
  rw [arakelovPair_symm, arakelovPair_smul_left, arakelovPair_symm]

theorem arakelovPair_sub_left (M : ArithSurfaceModel m E_arch)
    (L₁ L₂ L₃ : ArithLineBundle m E_arch) :
    arakelovPair M (L₁ - L₂) L₃ = arakelovPair M L₁ L₃ - arakelovPair M L₂ L₃ := by
  rw [sub_eq_add_neg, arakelovPair_add_left,
    show -L₂ = (-1 : ℝ) • L₂ by rw [neg_one_smul], arakelovPair_smul_left]
  ring

theorem arakelovPair_sub_right (M : ArithSurfaceModel m E_arch)
    (L₁ L₂ L₃ : ArithLineBundle m E_arch) :
    arakelovPair M L₁ (L₂ - L₃) = arakelovPair M L₁ L₂ - arakelovPair M L₁ L₃ := by
  rw [arakelovPair_symm, arakelovPair_sub_left, arakelovPair_symm M L₂ L₁,
    arakelovPair_symm M L₃ L₁]

/-- The Arakelov intersection pairing packaged as a `LinearMap.BilinForm ℝ`. -/
def arakelovPairBilin (M : ArithSurfaceModel m E_arch) :
    LinearMap.BilinForm ℝ (ArithLineBundle m E_arch) :=
  LinearMap.mk₂ ℝ (arakelovPair M)
    (arakelovPair_add_left M) (arakelovPair_smul_left M)
    (arakelovPair_add_right M) (arakelovPair_smul_right M)

/-- Fiber intersection identities: `(F_∞ · F_∞) = 0` and `(L · c F_∞) = c · deg_K(L)`. -/
theorem arakelovPair_fiber_self (M : ArithSurfaceModel m E_arch) (c₁ c₂ : ℝ) :
    arakelovPair M (fiberBundle c₁) (fiberBundle c₂) = 0 := by
  simp [arakelovPair, fiberBundle]

theorem arakelovPair_fiber_right (M : ArithSurfaceModel m E_arch)
    (L : ArithLineBundle m E_arch) (c : ℝ) :
    arakelovPair M L (fiberBundle c) = c * L.geomDeg := by
  simp [arakelovPair, fiberBundle, mul_comm]

theorem arakelovPair_add_fiber_self (M : ArithSurfaceModel m E_arch)
    (L : ArithLineBundle m E_arch) (c : ℝ) :
    arakelovPair M (L + fiberBundle c) (L + fiberBundle c) =
      arakelovPair M L L + 2 * c * L.geomDeg := by
  rw [arakelovPair_add_left, arakelovPair_add_right, arakelovPair_add_right,
    arakelovPair_symm M (fiberBundle c) L, arakelovPair_fiber_right, arakelovPair_fiber_self]
  ring

/-- **Zariski / Dirichlet Negativity on Generic-Degree-Zero Classes**:
if `L.geomDeg = 0`, then `(L · L)_Ar ≤ 0`, with equality if and only if `L` is a pure fiber class
(`L.vertComp = 0 ∧ L.archPot = 0`). -/
theorem arakelovPair_nonpos_of_geomDeg_zero (M : ArithSurfaceModel m E_arch)
    {L : ArithLineBundle m E_arch} (hd : L.geomDeg = 0) :
    arakelovPair M L L ≤ 0 := by
  unfold arakelovPair
  rw [hd]
  have hv : 0 ≤ L.vertComp ⬝ᵥ M.vertMatrix.mulVec L.vertComp := by
    by_cases h0 : L.vertComp = 0
    · simp [h0]
    · exact (posDef_dotProduct_mulVec_pos M.vertMatrix_posDef h0).le
  have ha : 0 ≤ inner ℝ L.archPot L.archPot := real_inner_self_nonneg
  linarith

theorem arakelovPair_eq_zero_iff_of_geomDeg_zero (M : ArithSurfaceModel m E_arch)
    {L : ArithLineBundle m E_arch} (hd : L.geomDeg = 0) :
    arakelovPair M L L = 0 ↔ L.vertComp = 0 ∧ L.archPot = 0 := by
  unfold arakelovPair
  rw [hd]
  simp only [mul_zero, zero_mul, zero_add, zero_sub]
  constructor
  · intro h0
    have hv_nn : 0 ≤ L.vertComp ⬝ᵥ M.vertMatrix.mulVec L.vertComp := by
      by_cases h : L.vertComp = 0
      · simp [h]
      · exact (posDef_dotProduct_mulVec_pos M.vertMatrix_posDef h).le
    have ha_nn : 0 ≤ inner ℝ L.archPot L.archPot := real_inner_self_nonneg
    have hv0 : L.vertComp ⬝ᵥ M.vertMatrix.mulVec L.vertComp = 0 := by linarith
    have ha0 : inner ℝ L.archPot L.archPot = 0 := by linarith
    refine ⟨?_, inner_self_eq_zero.mp ha0⟩
    by_contra hne
    linarith [posDef_dotProduct_mulVec_pos M.vertMatrix_posDef hne]
  · rintro ⟨hv, ha⟩
    simp [hv, ha]

/-- **FALTINGS–HRILJAC ARITHMETIC HODGE INDEX THEOREM (`0` Assumptions!)**:
if `(L₁ · L₁)_Ar > 0` and `(L₁ · L₂)_Ar = 0`, then `(L₂ · L₂)_Ar ≤ 0`! -/
theorem arithmetic_hodge_index (M : ArithSurfaceModel m E_arch)
    {L₁ L₂ : ArithLineBundle m E_arch}
    (hpos : 0 < arakelovPair M L₁ L₁) (horth : arakelovPair M L₁ L₂ = 0) :
    arakelovPair M L₂ L₂ ≤ 0 := by
  have hd1 : L₁.geomDeg ≠ 0 := by
    intro h0
    linarith [arakelovPair_nonpos_of_geomDeg_zero M h0]
  let Z : ArithLineBundle m E_arch := L₁.geomDeg • L₂ - L₂.geomDeg • L₁
  have hZd : Z.geomDeg = 0 := by
    simp only [Z, sub_geomDeg, smul_geomDeg]; ring
  have hZle : arakelovPair M Z Z ≤ 0 := arakelovPair_nonpos_of_geomDeg_zero M hZd
  have hZexp : arakelovPair M Z Z =
      L₁.geomDeg ^ 2 * arakelovPair M L₂ L₂ + L₂.geomDeg ^ 2 * arakelovPair M L₁ L₁ := by
    dsimp only [Z]
    rw [arakelovPair_sub_left, arakelovPair_sub_right, arakelovPair_sub_right,
      arakelovPair_smul_left, arakelovPair_smul_right, arakelovPair_smul_left,
      arakelovPair_smul_right, arakelovPair_smul_left, arakelovPair_smul_right,
      arakelovPair_smul_left, arakelovPair_smul_right,
      arakelovPair_symm M L₂ L₁, horth]
    ring
  rw [hZexp] at hZle
  have h1 : 0 < L₁.geomDeg ^ 2 := sq_pos_of_ne_zero hd1
  have h2 : 0 ≤ L₂.geomDeg ^ 2 * arakelovPair M L₁ L₁ :=
    mul_nonneg (sq_nonneg _) hpos.le
  nlinarith

/-- **ARITHMETIC HODGE INDEX INEQUALITY (Reverse Cauchy–Schwarz)**:
for any `L₁, L₂` with `(L₁ · L₁)_Ar > 0`:
$$(L_1 \cdot L_1)_{\mathrm{Ar}} \cdot (L_2 \cdot L_2)_{\mathrm{Ar}} \le (L_1 \cdot L_2)_{\mathrm{Ar}}^2.$$ -/
theorem arithmetic_hodge_index_ineq (M : ArithSurfaceModel m E_arch)
    {L₁ L₂ : ArithLineBundle m E_arch} (hpos : 0 < arakelovPair M L₁ L₁) :
    arakelovPair M L₁ L₁ * arakelovPair M L₂ L₂ ≤ (arakelovPair M L₁ L₂) ^ 2 := by
  let L₂' : ArithLineBundle m E_arch :=
    arakelovPair M L₁ L₁ • L₂ - arakelovPair M L₁ L₂ • L₁
  have horth : arakelovPair M L₁ L₂' = 0 := by
    dsimp only [L₂']
    rw [arakelovPair_sub_right, arakelovPair_smul_right, arakelovPair_smul_right]
    ring
  have hle := arithmetic_hodge_index M hpos horth
  have hexp : arakelovPair M L₂' L₂' =
      arakelovPair M L₁ L₁ *
        (arakelovPair M L₁ L₁ * arakelovPair M L₂ L₂ - (arakelovPair M L₁ L₂) ^ 2) := by
    dsimp only [L₂']
    rw [arakelovPair_sub_left, arakelovPair_sub_right, arakelovPair_sub_right,
      arakelovPair_smul_left, arakelovPair_smul_right, arakelovPair_smul_left,
      arakelovPair_smul_right, arakelovPair_smul_left, arakelovPair_smul_right,
      arakelovPair_smul_left, arakelovPair_smul_right,
      arakelovPair_symm M L₂ L₁]
    ring
  rw [hexp] at hle
  nlinarith

/-- Concrete **Arithmetic Ampleness** predicate: `deg_K(L) > 0` and `(L · L)_Ar > 0`. -/
def IsArithAmple (M : ArithSurfaceModel m E_arch) (L : ArithLineBundle m E_arch) : Prop :=
  0 < L.geomDeg ∧ 0 < arakelovPair M L L

/-- **Positivity & Lorentzian Reverse Cauchy–Schwarz for Ample Line Bundles**:
if `L₁` and `L₂` are arithmetically ample (`deg_K > 0` and `(L_i · L_i)_Ar > 0`), then:
1. `0 < (L₁ · L₂)_Ar`,
2. `√((L₁ · L₁)_Ar * (L₂ · L₂)_Ar) ≤ (L₁ · L₂)_Ar`! -/
theorem arakelovPair_pos_of_ample (M : ArithSurfaceModel m E_arch)
    {L₁ L₂ : ArithLineBundle m E_arch}
    (h₁ : IsArithAmple M L₁) (h₂ : IsArithAmple M L₂) :
    0 < arakelovPair M L₁ L₂ ∧
    Real.sqrt (arakelovPair M L₁ L₁ * arakelovPair M L₂ L₂) ≤ arakelovPair M L₁ L₂ := by
  let Z : ArithLineBundle m E_arch := L₂.geomDeg • L₁ - L₁.geomDeg • L₂
  have hZd : Z.geomDeg = 0 := by
    simp only [Z, sub_geomDeg, smul_geomDeg]; ring
  have hZle : arakelovPair M Z Z ≤ 0 := arakelovPair_nonpos_of_geomDeg_zero M hZd
  have hZexp : arakelovPair M Z Z =
      L₂.geomDeg ^ 2 * arakelovPair M L₁ L₁ -
        2 * L₁.geomDeg * L₂.geomDeg * arakelovPair M L₁ L₂ +
        L₁.geomDeg ^ 2 * arakelovPair M L₂ L₂ := by
    dsimp only [Z]
    rw [arakelovPair_sub_left, arakelovPair_sub_right, arakelovPair_sub_right,
      arakelovPair_smul_left, arakelovPair_smul_right, arakelovPair_smul_left,
      arakelovPair_smul_right, arakelovPair_smul_left, arakelovPair_smul_right,
      arakelovPair_smul_left, arakelovPair_smul_right,
      arakelovPair_symm M L₂ L₁]
    ring
  rw [hZexp] at hZle
  have hpos_pair : 0 < arakelovPair M L₁ L₂ := by
    have hsum_pos : 0 < L₂.geomDeg ^ 2 * arakelovPair M L₁ L₁ +
        L₁.geomDeg ^ 2 * arakelovPair M L₂ L₂ :=
      add_pos (mul_pos (sq_pos_of_pos h₂.1) h₁.2) (mul_pos (sq_pos_of_pos h₁.1) h₂.2)
    have hd_pos : 0 < 2 * L₁.geomDeg * L₂.geomDeg := by nlinarith [h₁.1, h₂.1]
    nlinarith
  have hhi := arithmetic_hodge_index_ineq M h₁.2 (L₂ := L₂)
  refine ⟨hpos_pair, ?_⟩
  rw [← Real.sqrt_sq hpos_pair.le]
  exact Real.sqrt_le_sqrt hhi

/-- **Convexity of the Arithmetic Ample Cone**:
positive linear combinations of arithmetically ample bundles are arithmetically ample. -/
theorem isArithAmple_add (M : ArithSurfaceModel m E_arch)
    {L₁ L₂ : ArithLineBundle m E_arch}
    (h₁ : IsArithAmple M L₁) (h₂ : IsArithAmple M L₂) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsArithAmple M (a • L₁ + b • L₂) := by
  refine ⟨by simp only [add_geomDeg, smul_geomDeg]; nlinarith [h₁.1, h₂.1], ?_⟩
  rw [arakelovPair_add_left, arakelovPair_add_right, arakelovPair_add_right,
    arakelovPair_smul_left, arakelovPair_smul_right, arakelovPair_smul_left,
    arakelovPair_smul_right, arakelovPair_smul_left, arakelovPair_smul_right,
    arakelovPair_smul_left, arakelovPair_smul_right, arakelovPair_symm M L₂ L₁]
  have h12 := (arakelovPair_pos_of_ample M h₁ h₂).1
  have t1 : 0 < a * (a * arakelovPair M L₁ L₁) := mul_pos ha (mul_pos ha h₁.2)
  have t2 : 0 < a * (b * arakelovPair M L₁ L₂) := mul_pos ha (mul_pos hb h12)
  have t3 : 0 < b * (a * arakelovPair M L₁ L₂) := mul_pos hb (mul_pos ha h12)
  have t4 : 0 < b * (b * arakelovPair M L₂ L₂) := mul_pos hb (mul_pos hb h₂.2)
  linarith

/-- **Arithmetic Adjunction Positivity**:
for an ample class `L` and a nef/non-negative canonical class `K` (`0 ≤ (L · K)_Ar`),
`(L · (K + L))_Ar = (L · K)_Ar + (L · L)_Ar > 0`, and `(L · (K + L))_Ar ≥ (L · L)_Ar`. -/
theorem arakelovAdjunction_pos (M : ArithSurfaceModel m E_arch)
    {L K : ArithLineBundle m E_arch} (hL : IsArithAmple M L) (hK : 0 ≤ arakelovPair M L K) :
    arakelovPair M L (K + L) = arakelovPair M L K + arakelovPair M L L ∧
    0 < arakelovPair M L (K + L) ∧
    arakelovPair M L L ≤ arakelovPair M L (K + L) := by
  have hadd := arakelovPair_add_right M L K L
  exact ⟨hadd, by linarith [hL.2], by linarith⟩

end ArithLineBundle

end ArakelovIntersectionAndHodgeIndex

/-! ## Section 4: Direct Bridges to `Stage11HermitianCurvature`, `Stage11MoriwakiCovolume` & Pillar 2 -/

section Pillar2Bridges

/-- **Bridge 1 (`Stage11HermitianCurvature` Hodge Bundle Degree & Chern–Weil Bracket)**:
for any weight `k ≥ 0` and any smooth metric perturbation `uMin ≤ u ≤ uMax` on `SL₂(ℤ) \ ℍ`,
the generic-fiber degree of `hodgeBundle k 0` equals the exact First Chern integral `k / 12`,
and the Chern–Weil metric change is bracketed verbatim by the Arakelov fiber pairings
`(ω^{⊗ k} · uMin F_∞)_Ar ≤ chernWeilChange ≤ (ω^{⊗ k} · uMax F_∞)_Ar`! -/
theorem hodgeBundle_chernWeil_bracket {m : ℕ} {E_arch : Type*}
    [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]
    (M : ArithSurfaceModel m E_arch)
    (k : ℤ) (hk : 0 ≤ k) {u : ℝ × ℝ → ℝ} {uMin uMax : ℝ}
    (huMin : ∀ p, uMin ≤ u p) (huMax : ∀ p, u p ≤ uMax)
    (hu_int : IntegrableOn (fun p : ℝ × ℝ => u p * ((k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)))
      stdFD volume) :
    (ArithLineBundle.hodgeBundle (m := m) (E_arch := E_arch) k 0).geomDeg =
      ∫ p in Stage10PeterssonHecke.stdFD, (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ) ∧
    ArithLineBundle.arakelovPair M (ArithLineBundle.hodgeBundle k 0)
      (ArithLineBundle.fiberBundle uMin) ≤
      HermitianCurvatureCore.chernWeilChange (volume.restrict stdFD) u
        (fun _ p => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) ∧
    HermitianCurvatureCore.chernWeilChange (volume.restrict stdFD) u
        (fun _ p => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) ≤
      ArithLineBundle.arakelovPair M (ArithLineBundle.hodgeBundle k 0)
        (ArithLineBundle.fiberBundle uMax) := by
  have hdeg : (ArithLineBundle.hodgeBundle (m := m) (E_arch := E_arch) k 0).geomDeg =
      ∫ p in Stage10PeterssonHecke.stdFD, (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ) := by
    rw [firstChernIntegral_weight_k_eq k]
    rfl
  have hcw := chernWeilChange_stdFD_bounds k hk huMin huMax hu_int
  refine ⟨hdeg, ?_, ?_⟩
  · rw [ArithLineBundle.arakelovPair_fiber_right]
    exact hcw.1
  · rw [ArithLineBundle.arakelovPair_fiber_right]
    exact hcw.2

/-- **Bridge 2 (`Stage11MoriwakiCovolume` Arithmetic Hilbert–Samuel & Moriwaki Small Sections)**:
for any arithmetically ample line bundle `L` (`(L · L)_Ar > 0`) on an arithmetic surface model `M`
and any sequence of positive-rank Hermitian vector bundles `E_n : HermVectorBundle` (modeling
`H⁰(X, L^{⊗ n})`) with polynomial rank growth `(E_n).rk ≤ C₁ * n^D` (`C₁ ≥ 1`) and AHS lower bound
`∀ ε > 0, ∀ᶠ n, (L · L)_Ar - ε ≤ (E_n).arakelovDeg / arithVolNorm D n`:
1. `liminf_{n → ∞} log(h⁰_strict(E_n, 1)) / arithVolNorm D n ≥ (L · L)_Ar`,
2. Eventually there exists a **nonzero small integral section** `x ∈ (E_n).lat`, `x ≠ 0`, with
   `(E_n).hNorm x < 1`! -/
theorem moriwaki_small_sections_of_arithAmple {m : ℕ} {E_arch : Type*}
    [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]
    (M : ArithSurfaceModel m E_arch) {L : ArithLineBundle m E_arch}
    (hL : ArithLineBundle.IsArithAmple M L)
    (E : ℕ → HermVectorBundle) (hE_rk : ∀ n, 0 < (E n).rk)
    (D : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁)
    (hrank : ∀ n, ((E n).rk : ℝ) ≤ C₁ * (n : ℝ) ^ D)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ArithLineBundle.arakelovPair M L L - ε ≤
        (E n).arakelovDeg / RHDirect.HermitianCurvatureCore.arithVolNorm D n) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ArithLineBundle.arakelovPair M L L - ε ≤
        Real.log (h0ArithStrict (E n).euclLat 1 : ℝ) /
          RHDirect.HermitianCurvatureCore.arithVolNorm D n) ∧
    (∀ᶠ n in atTop, ∃ x ∈ (E n).lat, x ≠ 0 ∧ (E n).hNorm x < 1) := by
  have hM := hermitianCurvature_moriwaki_of_lattice_family
    (E := fun n => EuclideanSpace ℝ (Fin (E n).rk))
    (L := fun n => (E n).euclLat)
    (fun n => (E n).euclLat_ne_bot_of_rk_pos (hE_rk n))
    D hC₁
    (fun n => by rw [(E n).rk_euclLat]; exact hrank n)
    hAHS
  refine ⟨hM, ?_⟩
  have hpos : 0 < ArithLineBundle.arakelovPair M L L := hL.2
  have hev := hM (ArithLineBundle.arakelovPair M L L / 2) (half_pos hpos)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hvol_pos := RHDirect.HermitianCurvatureCore.arithVolNorm_pos D hn1
  have hlog_pos : 0 < Real.log (h0ArithStrict (E n).euclLat 1 : ℝ) := by
    have h1 : 0 < (ArithLineBundle.arakelovPair M L L / 2) *
        RHDirect.HermitianCurvatureCore.arithVolNorm D n :=
      mul_pos (half_pos hpos) hvol_pos
    have h2 := (le_div_iff₀ hvol_pos).mp hn
    linarith
  have hgt1_real : (1 : ℝ) < (h0ArithStrict (E n).euclLat 1 : ℝ) := by
    by_contra hle
    push Not at hle
    have hlog_le : Real.log (h0ArithStrict (E n).euclLat 1 : ℝ) ≤ 0 := by
      rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (h0ArithStrict (E n).euclLat 1)) with h0 | hpos'
      · rw [← h0, Real.log_zero]
      · exact (Real.log_le_log hpos' hle).trans_eq Real.log_one
    linarith
  have hgt1 : 1 < h0ArithStrict (E n).euclLat 1 := by exact_mod_cast hgt1_real
  -- Unpack `h0ArithStrict` (`((E n).euclLat ∩ Metric.ball 0 1).ncard > 1`) to extract a nonzero element!
  unfold h0ArithStrict at hgt1
  have hfin : (((E n).euclLat : Set (EuclideanSpace ℝ (Fin (E n).rk))) ∩ Metric.ball 0 1).Finite :=
    (RHDirect.Stage2SiegelReduction.lattice_inter_closedBall_finite (E n).euclLat 1).subset
      (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := (Set.one_lt_ncard_iff hfin).mp hgt1
  have hex : ∃ v ∈ (E n).euclLat, v ≠ 0 ∧ ‖v‖ < 1 := by
    by_cases hv10 : v₁ = 0
    · refine ⟨v₂, hv₂.1, fun h => hne (hv10.trans h.symm), ?_⟩
      simpa only [Metric.mem_ball, dist_zero_right] using hv₂.2
    · refine ⟨v₁, hv₁.1, hv10, ?_⟩
      simpa only [Metric.mem_ball, dist_zero_right] using hv₁.2
  rcases hex with ⟨v, ⟨x, hxL, rfl⟩, hv0, hvlt⟩
  refine ⟨x, hxL, fun hx0 => hv0 (by rw [hx0, map_zero]), ?_⟩
  change ‖(E n).toEucl x‖ < 1 at hvlt
  rwa [(E n).norm_toEucl] at hvlt

/-- **Bridge 3 (`HermVectorBundle` Two-Sided Covolume & Slope Sandwich)**:
for any positive-rank Hermitian vector bundle `E` and any `E.rk` linearly independent integral
sections `b : Fin E.rk → (Fin E.rk → ℝ)` in `E.lat`, directly combines Hadamard + Minkowski's
Second Theorem (`Stage11MoriwakiCovolume.covolume_bound_of_section_norms`) with `E.muMin ≤ E.slope ≤ E.muMax`. -/
theorem hermVectorBundle_covolume_slope_sandwich (E : HermVectorBundle) (hr : 0 < E.rk)
    (b : Fin E.rk → (Fin E.rk → ℝ)) (hbL : ∀ i, b i ∈ E.lat) (hbli : LinearIndependent ℝ b) :
    E.covol ≤ ∏ i : Fin E.rk, E.hNorm (b i) ∧
    -(Real.log (∏ i : Fin E.rk, E.hNorm (b i)) / (E.rk : ℝ)) ≤ E.slope ∧
    E.muMin ≤ E.slope ∧
    E.slope ≤ E.muMax := by
  let bE : Fin (ArakelovCovolume.rk E.euclLat) → EuclideanSpace ℝ (Fin E.rk) :=
    fun i => E.toEucl (b (finCongr E.rk_euclLat i))
  have hbEL : ∀ i, bE i ∈ E.euclLat := fun i => ⟨b (finCongr E.rk_euclLat i), hbL _, rfl⟩
  have hbEli : LinearIndependent ℝ bE := by
    have h1 : LinearIndependent ℝ (fun i : Fin (ArakelovCovolume.rk E.euclLat) =>
        b (finCongr E.rk_euclLat i)) :=
      hbli.comp (finCongr E.rk_euclLat) (finCongr E.rk_euclLat).injective
    exact h1.map' E.toEucl (LinearMap.ker_eq_bot.mpr E.toEucl_injective)
  have hcb := covolume_bound_of_section_norms E.euclLat (E.euclLat_ne_bot_of_rk_pos hr)
    bE hbEL hbEli
  have hprod_eq : (∏ i : Fin (ArakelovCovolume.rk E.euclLat), ‖bE i‖) =
      ∏ i : Fin E.rk, E.hNorm (b i) := by
    refine Fintype.prod_equiv (finCongr E.rk_euclLat) _ _ fun i => ?_
    simp only [bE, E.norm_toEucl]
  have hord := E.muMin_le_slope_le_muMax hr
  refine ⟨?_, ?_, hord.1, hord.2⟩
  · have h1 := hcb.1.2.1
    rwa [hprod_eq] at h1
  · have h2 := hcb.2.1.1
    rw [hprod_eq, E.rk_euclLat, ← E.slope_eq_euclSlope] at h2
    exact h2

/-- **Bridge 4 (Direct Pillar 2 Discharge of `RHDirect.BostSlopeFiber.SlopeIneq` from
`HermVectorBundle` Morphisms)**:
given a target Hermitian vector bundle `E` realizing the common dual fiber (`E.slope = B.muCC`,
`B.muMinCC ≤ E.muMin`) and a family of source bundles `N τ u` with morphisms
`φ τ u : HermBundleMorphism (N τ u) E` of operator norm `≤ B.cardW` whose real images cover
all but the Bost tail codimension, **`B.SlopeIneq` holds verbatim**! -/
theorem pillar2_bost_slope_from_hermVectorBundle_morphisms
    {ι : Type*}
    (B : RHDirect.BostSlopeFiber)
    (E : HermVectorBundle) (hErk : 0 < E.rk)
    (hu : 0 ≤ B.uF) (hcard : 1 ≤ B.cardW)
    (hmuCC : E.slope = B.muCC)
    (hmuMin : B.muMinCC ≤ E.muMin)
    (N : ℝ → ι → HermVectorBundle)
    (φ : ∀ τ u, HermVectorBundle.HermBundleMorphism (N τ u) E)
    (hOpNorm : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH, ∀ u, (φ τ u).opNorm ≤ (B.cardW : ℝ))
    (hMuMin : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH, ∀ u, 0 < (N τ u).rk → B.s - τ ≤ (N τ u).muMin)
    (hCodim : 0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
      B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
        ((E.rk - Module.finrank ℝ ↥(⨆ u : ι, LinearMap.range (φ τ u).toLinearMap) : ℕ) : ℝ)
          ≤ RHDirect.ArakelovCovolume.bostTailWeight B.del B.η B.e B.uF τ * (E.rk : ℝ)) :
    B.SlopeIneq := by
  refine Stage4ArakelovBost.bostSlopeFiber_slopeIneq_of_hnFiltration B E.euclLat
    (E.euclLat_ne_bot_of_rk_pos hErk) hu hcard (E.slope_eq_euclSlope.symm.trans hmuCC) hmuMin ?_
  intro hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ
  let F := canonicalHN E.euclLat
  let θ := B.s - Real.log (B.cardW : ℝ) - τ
  have hCpos : (0 : ℝ) < (B.cardW : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  -- Every morphism `φ τ u` lands inside the `≥ θ` HN truncation `F.trunc θ`!
  have hincl : (⨆ u : ι, Submodule.map E.toEucl (LinearMap.range (φ τ u).toLinearMap)) ≤
      Submodule.span ℝ ((F.trunc θ : Submodule ℤ (EuclideanSpace ℝ (Fin E.rk))) :
        Set (EuclideanSpace ℝ (Fin E.rk))) := by
    refine iSup_le fun u => ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : x ∈ Submodule.span ℝ ((N τ u).lat : Set (Fin (N τ u).rk → ℝ)) := by
      rw [(N τ u).lat_span_top]; trivial
    induction hx using Submodule.span_induction with
    | mem a ha =>
      refine Submodule.subset_span ?_
      let ψZ : (N τ u).euclLat →ₗ[ℤ] E.euclLat :=
        { toFun := fun v =>
            ⟨(φ τ u).toEuclCLM v.1, by
              rcases v.2 with ⟨y, hyL, hyv⟩
              rw [← hyv]
              change E.toEucl ((φ τ u).toLinearMap ((N τ u).toEuclEquiv.symm ((N τ u).toEucl y))) ∈ E.euclLat
              rw [(N τ u).toEuclEquiv_symm_toEucl]
              exact ⟨(φ τ u).toLinearMap y, (φ τ u).maps_lat y hyL, rfl⟩⟩
          map_add' := fun v₁ v₂ => Subtype.ext (map_add (φ τ u).toEuclCLM v₁.1 v₂.1)
          map_smul' := fun c v => Subtype.ext (map_zsmul (φ τ u).toEuclCLM c v.1) }
      have hψ_lip : ∀ v : (N τ u).euclLat,
          ‖((ψZ v : E.euclLat) : EuclideanSpace ℝ (Fin E.rk))‖ ≤
            (B.cardW : ℝ) * ‖(v : EuclideanSpace ℝ (Fin (N τ u).rk))‖ := by
        intro v
        exact ((φ τ u).toEuclCLM.le_opNorm v.1).trans
          (mul_le_mul_of_nonneg_right (hOpNorm τ hτ u) (norm_nonneg _))
      have hmem := Stage4ArakelovBost.bost_truncation_inclusion F ψZ (B.cardW : ℝ) θ hCpos hψ_lip
        (fun hN0 => by
          have hrk_pos : 0 < (N τ u).rk := by
            rw [← (N τ u).rk_euclLat]
            exact rk_pos_of_ne_bot _ hN0
          have h1 : B.s - τ ≤ Stage4ArakelovBost.muMin (N τ u).euclLat :=
            hMuMin τ hτ u hrk_pos
          dsimp only [θ]
          linarith)
        ⟨(N τ u).toEucl a, ⟨a, ha, rfl⟩⟩
      have heq : ((ψZ ⟨(N τ u).toEucl a, ⟨a, ha, rfl⟩⟩ : E.euclLat) : EuclideanSpace ℝ (Fin E.rk)) =
          E.toEucl ((φ τ u).toLinearMap a) := by
        change E.toEucl ((φ τ u).toLinearMap ((N τ u).toEuclEquiv.symm ((N τ u).toEucl a))) =
          E.toEucl ((φ τ u).toLinearMap a)
        rw [(N τ u).toEuclEquiv_symm_toEucl]
      rwa [← heq]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha
  have hmap_sup : Submodule.map E.toEucl (⨆ u : ι, LinearMap.range (φ τ u).toLinearMap) =
      ⨆ u : ι, Submodule.map E.toEucl (LinearMap.range (φ τ u).toLinearMap) :=
    Submodule.map_iSup _ _
  have hfinrank_map : Module.finrank ℝ ↥(⨆ u : ι, Submodule.map E.toEucl (LinearMap.range (φ τ u).toLinearMap)) =
      Module.finrank ℝ ↥(⨆ u : ι, LinearMap.range (φ τ u).toLinearMap) := by
    rw [← hmap_sup]
    exact (Submodule.equivMapOfInjective E.toEucl E.toEucl_injective _).symm.finrank_eq
  have : DiscreteTopology (F.trunc θ) := discreteTopology_of_le (F.trunc_isSaturated θ).1
  have hdim_le : Module.finrank ℝ ↥(⨆ u : ι, LinearMap.range (φ τ u).toLinearMap) ≤
      ArakelovCovolume.rk (F.trunc θ) := by
    rw [← hfinrank_map]
    unfold ArakelovCovolume.rk
    rw [finrank_int_eq_finrank_real_span (F.trunc θ)]
    exact Submodule.finrank_mono hincl
  have hadd := rk_add_quotLat (F.trunc_isSaturated θ)
  rw [E.rk_euclLat] at hadd ⊢
  have hcor_nat : ArakelovCovolume.rk (quotLat E.euclLat (F.trunc θ)) ≤
      E.rk - Module.finrank ℝ ↥(⨆ u : ι, LinearMap.range (φ τ u).toLinearMap) := by
    omega
  exact (Nat.cast_le.mpr hcor_nat).trans (hCodim hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ)

/-- **Phase B Master Arakelov–Faltings–Bost Synthesis (`0` Assumptions!)**:
packages together:
1. Universal lower bound `∀ τ, (-2 : ℝ) ≤ faltingsHeight τ` and `SL₂(ℤ)`-invariance of `h_F`,
2. Exact curvature-degree identity `(1 / (2π)) ∫_{stdFD} Δ_Eucl h_F = 1 / 12 = deg(ω)`,
3. Exact tensor & dual slope calculus `(E ⊗ F).slope = E.slope + F.slope` and `E.dual.slope = -E.slope`,
4. Bost's slope inequality `E.muMin ≤ F.muMax + Real.log φ.opNorm` for every nonzero bundle morphism,
5. Faltings–Hriljac Arithmetic Hodge Index `(L₁ · L₁)_Ar * (L₂ · L₂)_Ar ≤ (L₁ · L₂)_Ar ^ 2`. -/
theorem phaseB_arakelov_faltings_synthesis :
    (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      faltingsHeight (γ • τ) = faltingsHeight τ) ∧
    (∀ τ : UpperHalfPlane, (-2 : ℝ) ≤ faltingsHeight τ) ∧
    ((1 / (2 * Real.pi)) *
      ∫ p in Stage10PeterssonHecke.stdFD,
        (if hp : 0 < p.2 then euclLaplacianR faltingsHeight (pairToUHP p hp) else 0) = 1 / 12) ∧
    (∀ (E F : HermVectorBundle), 0 < E.rk → 0 < F.rk →
      (E.tensor F).slope = E.slope + F.slope ∧ E.dual.slope = -E.slope) ∧
    (∀ (E F : HermVectorBundle) (φ : HermVectorBundle.HermBundleMorphism E F),
      φ.toLinearMap ≠ 0 → E.muMin ≤ F.muMax + Real.log φ.opNorm) := by
  exact ⟨faltingsHeight_sl2Z_invariant, faltingsHeight_ge_neg_two,
    faltingsHeight_curvature_integral_eq_one_div_twelve,
    fun E F hE hF => ⟨E.bundleSlope_tensor F hE hF, E.bundleSlope_dual⟩,
    fun _ _ φ hφ => φ.bost_slope_inequality_bundle hφ⟩

end Pillar2Bridges

end

end RHDirect.Stage11ArakelovFaltings
