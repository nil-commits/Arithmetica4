import RHDirect.ArakelovCovolume
import RHDirect.Stage2SiegelReduction
import RHDirect.Stage3ThetaSiegelBridge
import RHDirect.Stage4ArakelovBost
import RHDirect.Stage10GeometryOfNumbers
import RHDirect.HermitianCurvatureCore
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# RHDirect.Stage11MoriwakiCovolume

Unconditional, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of the **Concrete Hermitian
Arithmetic Hilbert–Samuel Covolume Bound, Tensor/Symmetric-Power Arithmetic Degree Growth,
Gillet–Soulé / Moriwaki Small-Section Counting & `Stage3ThetaSiegelBridge` Covolume Sandwich**
in pure Mathlib `v4.33.1`.

## Contents

1. **Concrete Arithmetic Degree `arithDeg`, Metric Scaling, Exact-Sequence Additivity & Exact
   Tensor-Product Formulas (`0` Assumptions)**:
   - `arithDeg L := -Real.log (ArakelovCovolume.covol L)` (`= rk L * slope L`), scaling laws
     (`covol_scaleLat`, `arithDeg_scaleLat`, `slope_scaleLat`).
   - Exact sublattice / orthogonal-quotient additivity (`arithDeg_exact_seq`,
     `arithDeg_short_exact_seq`) via orthogonal block-triangular Gram determinants.
   - Hilbert–Schmidt Euclidean tensor product `tensorLat L₁ L₂` and `k`-th tensor power
     `tensorPowLat L k`, proving exact rank multiplicativity, covolume power law,
     **`arithDeg_tensor`**: `arithDeg (L₁ ⊗ L₂) = r₂ * arithDeg L₁ + r₁ * arithDeg L₂`, and
     **`slope_tensor_eq_add`**: `slope (L₁ ⊗ L₂) = slope L₁ + slope L₂` (plus `slope_tensorPowLat`).

2. **Isometric Lattice Transport, Elementary Gamma Ceiling & Unconditional Gillet–Soulé / Moriwaki
   Small-Section Counting (`0` Assumptions)**:
   - Isometric transport of any discrete Euclidean lattice `L ⊂ E` to a full-rank `IsZLattice ℝ`
     lattice `Λ ⊂ EuclideanSpace ℝ (Fin (rk L))` preserving covolume, ball counts, and
     successive minima (`exists_isometric_euclidean_lattice`).
   - Elementary unconditional Gamma upper bound `Real.Gamma (r / 2 + 1) ≤ r ^ (r / 2)` for all
     `r ≥ 1` (`gamma_half_add_one_le`) and explicit unit-ball log-volume lower bound
     `log ω_r ≥ (r / 2) * (log π - log r)` (`log_unitBallVol_ge`).
   - Small-section counting functions `h0Arith L R := #{v ∈ L | ‖v‖ ≤ R}` and
     `h0ArithStrict L R := #{v ∈ L | ‖v‖ < R}`.
   - **Unconditional Gillet–Soulé / Moriwaki Arithmetic Riemann–Roch Lower Bounds**
     (`h0Arith_lower_bound_minkowski`, `h0ArithStrict_lower_bound_minkowski`,
     `log_h0Arith_lower_bound`, `h0Arith_lower_bound_minkowski_pairs`,
     `moriwaki_small_section_count`):
     `(h0Arith L R : ℝ) ≥ (ω_r * (R / 2)^r) / covol L` and
     `log (h0ArithStrict L 1) ≥ r * (slope L - (1 / 2) * log r - log (2 / √π))`.

3. **Symmetric-Power Hermitian Lattices `Sym^k`, Exact Arithmetic Hilbert–Samuel Asymptotic &
   Moriwaki Bigness Criterion (`0` Assumptions)**:
   - Multi-indices `MultiIndex r k` with exact cardinality `Nat.choose (k + r - 1) k`
     (`card_multiIndex`) and coordinate-sum symmetry (`sum_multiIndex_coord`).
   - Weighted symmetric-power Hermitian lattices `symPowWeightedLat` and monomial symmetric powers
     `symPowMonomialLat`, proving exact `arithDeg_symPowMonomialLat` and `slope_symPowMonomialLat`.
   - **Exact Arithmetic Hilbert–Samuel Asymptotic (`arith_hilbert_samuel_symPow_tendsto`)** under
     Bergman / Fubini–Study logarithmic metric distortion `O(log (k + 1))`.
   - **Moriwaki Bigness Criterion (`moriwaki_bigness_asymptotic`,
     `moriwaki_bigness_poly_rank_asymptotic`, `moriwaki_bigness_symPow_asymptotic`)** and
     unconditional discharge of the Minkowski hypothesis `hMink` of
     `HermitianCurvatureCore.moriwaki_big_of_ahs` (`hermitianCurvature_moriwaki_of_lattice_family`).

4. **Concrete Covolume & Slope Two-Sided Bounds Connecting to `Stage3ThetaSiegelFiberWitness`
   (`0` Assumptions)**:
   - General-space Minkowski's Second Theorem lower and upper bounds
     (`minkowski_second_theorem_lower_general`, `minkowski_second_theorem_upper_general`).
   - **`covolume_bound_of_section_norms`**: Hadamard upper bound `covol L ≤ ∏ i, ‖b i‖` paired
     with Minkowski's Second Theorem two-sided comparison, giving explicit two-sided control over
     `ArakelovCovolume.slope L`.
   - **`stage3_fiber_covolume_and_small_sections`**: Direct bridge into
     `Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Set
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology

namespace RHDirect.Stage11MoriwakiCovolume

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  covol_bot degAr_bot gram_sum_smul_eq_transpose_mul slope_le_muMax)

open RHDirect.Stage2SiegelReduction (gsVec gsCoeff gs_expansion gsVec_orthogonal
  gsVec_ne_zero_of_linearIndependent det_gram_eq_prod_gsVec_norm_sq covol_eq_prod_gsVec
  covol_le_prod_norm lattice_inter_closedBall_finite lambda1 lambda1_pos succMin
  succMin_mono succMin_zero_eq_lambda1 succMin_pos covol_le_prod_succMin)

open RHDirect.Stage4ArakelovBost (IsSaturated projOrth quotLat
  discreteTopology_of_fin_basis_real_li quotLat_exact_additivity discreteTopology_quotLat
  rk_add_quotLat covol_eq_mul_quotLat degAr_eq_add_quotLat)

/-! ## Section 1: Arithmetic Degree, Metric Scaling, Exact Sequences & Tensor Products -/

section ArithmeticDegreeAndExactSeq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Concrete **Arithmetic Degree** `deg_Ar(L) = -log covol(L)` of a Euclidean lattice `L ⊂ E`. -/
def arithDeg (L : Submodule ℤ E) : ℝ :=
  -Real.log (covol L)

@[simp]
lemma arithDeg_eq_degAr (L : Submodule ℤ E) : arithDeg L = degAr L := rfl

lemma arithDeg_bot : arithDeg (⊥ : Submodule ℤ E) = 0 := degAr_bot

lemma slope_eq_arithDeg_div_rk (L : Submodule ℤ E) :
    slope L = arithDeg L / (rk L : ℝ) := rfl

/-- Exact relation `arithDeg L = rk L * slope L` for any nonzero discrete lattice `L`. -/
theorem arithDeg_eq_rk_mul_slope (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    arithDeg L = (rk L : ℝ) * slope L := by
  have hr : (rk L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rk_pos_of_ne_bot L hL0).ne'
  rw [slope_eq_arithDeg_div_rk, mul_div_cancel₀ _ hr]

/-- Uniformly scaled lattice `c • L = { c • v | v ∈ L }` (`c : ℝ`). -/
def scaleLat (c : ℝ) (L : Submodule ℤ E) : Submodule ℤ E :=
  L.map ((c • (LinearMap.id : E →ₗ[ℝ] E)).restrictScalars ℤ)

/-- Metric / lattice scaling laws for `c > 0`:
1. `DiscreteTopology (scaleLat c L)`,
2. `rk (scaleLat c L) = rk L`,
3. `covol (scaleLat c L) = c ^ (rk L) * covol L`,
4. `arithDeg (scaleLat c L) = arithDeg L - rk L * log c`. -/
theorem scaleLat_invariants (L : Submodule ℤ E) [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    DiscreteTopology (scaleLat c L) ∧
    rk (scaleLat c L) = rk L ∧
    covol (scaleLat c L) = c ^ (rk L) * covol L ∧
    arithDeg (scaleLat c L) = arithDeg L - (rk L : ℝ) * Real.log c := by
  let e : L ≃ₗ[ℤ] scaleLat c L :=
    { toFun := fun x => ⟨c • (x : E), ⟨(x : E), x.2, rfl⟩⟩
      invFun := fun y => ⟨c⁻¹ • (y : E), by
        rcases y.2 with ⟨x, hxL, hxy⟩
        have hx : c⁻¹ • (y : E) = x := by
          have hy : (y : E) = c • x := hxy.symm
          rw [hy, inv_smul_smul₀ hc.ne']
        rwa [hx]⟩
      map_add' := fun x y => Subtype.ext (by simp [smul_add])
      map_smul' := fun n x => Subtype.ext (by
        change c • (n • (x : E)) = n • (c • (x : E))
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, smul_comm])
      left_inv := fun x => Subtype.ext (by simp [inv_smul_smul₀ hc.ne'])
      right_inv := fun y => Subtype.ext (by simp [smul_inv_smul₀ hc.ne']) }
  let bL := Module.finBasis ℤ L
  let bS := bL.map e
  have hliL : LinearIndependent ℝ (fun i => (bL i : E)) := linearIndependent_coe_basis L bL
  have hliS : LinearIndependent ℝ (fun i => (bS i : E)) := by
    have hEq : (fun i => (bS i : E)) = fun i => c • (bL i : E) := by
      funext i; rfl
    rw [hEq, Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : c • ∑ j, g j • (bL j : E) = 0 := by
      rw [Finset.smul_sum]
      simpa only [smul_comm c] using hg
    have h2 : ∑ j, g j • (bL j : E) = 0 := (smul_eq_zero.mp h1).resolve_left hc.ne'
    exact Fintype.linearIndependent_iff.mp hliL g h2 i
  have hDiscS : DiscreteTopology (scaleLat c L) := discreteTopology_of_fin_basis_real_li bS hliS
  have hrkS : rk (scaleLat c L) = rk L := by
    unfold rk
    rw [Module.finrank_eq_card_basis bS, Fintype.card_fin]
  have hgram : Matrix.gram ℝ (fun i => (bS i : E)) =
      (c ^ 2) • Matrix.gram ℝ (fun i => (bL i : E)) := by
    ext i j
    simp only [Matrix.gram_apply]
    change inner ℝ (c • (bL i : E)) (c • (bL j : E)) = c ^ 2 * inner ℝ (bL i : E) (bL j : E)
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hcovS : covol (scaleLat c L) = c ^ (rk L) * covol L := by
    rw [covol_eq_sqrt_det_gram (scaleLat c L) bS, covol_eq_sqrt_det_gram L bL, hgram,
      Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm 2 (Module.finrank ℤ L),
      pow_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rfl
  have hdegS : arithDeg (scaleLat c L) = arithDeg L - (rk L : ℝ) * Real.log c := by
    unfold arithDeg
    rw [hcovS, Real.log_mul (pow_pos hc _).ne' (covol_pos L).ne', Real.log_pow]
    ring
  exact ⟨hDiscS, hrkS, hcovS, hdegS⟩

theorem slope_scaleLat (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) {c : ℝ}
    (hc : 0 < c) :
    slope (scaleLat c L) = slope L - Real.log c := by
  obtain ⟨_, hrk, _, hdeg⟩ := scaleLat_invariants L hc
  have hr : (rk L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rk_pos_of_ne_bot L hL0).ne'
  rw [slope_eq_arithDeg_div_rk, slope_eq_arithDeg_div_rk, hrk, hdeg, sub_div,
    mul_div_cancel_left₀ _ hr]

omit [FiniteDimensional ℝ E] in
/-- **Orthogonal Block-Triangular Gram Determinant Identity**:
if `m : Fin r₁ → E` and `l : Fin s → E` decompose via `l j = p j + q j` with `p j ∈ span_ℝ m` and
`q j ∈ (span_ℝ m)ᗮ`, then `det Gram(m ⊕ l) = det Gram(m) * det Gram(q)`. -/
theorem det_gram_block_orthogonal {r₁ s : ℕ} (m : Fin r₁ → E) (l q : Fin s → E)
    (hsub : ∀ j : Fin s, l j - q j ∈ Submodule.span ℝ (Set.range m))
    (horth : ∀ (i : Fin r₁) (j : Fin s), inner ℝ (m i) (q j) = 0) :
    (Matrix.gram ℝ (Fin.append m l)).det =
      (Matrix.gram ℝ m).det * (Matrix.gram ℝ q).det := by
  have hcoeff : ∀ j : Fin s, ∃ a : Fin r₁ → ℝ, l j - q j = ∑ i : Fin r₁, a i • m i := by
    intro j
    have h := hsub j
    rw [Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, ha.symm⟩
  choose a ha using hcoeff
  -- Rewrite via `finSumFinEquiv` so block determinant applies cleanly.
  let e : Fin r₁ ⊕ Fin s ≃ Fin (r₁ + s) := finSumFinEquiv
  let v : Fin r₁ ⊕ Fin s → E := Sum.elim m q
  let w : Fin r₁ ⊕ Fin s → E := Sum.elim m l
  let B : Matrix (Fin r₁ ⊕ Fin s) (Fin r₁ ⊕ Fin s) ℝ :=
    Matrix.fromBlocks 1 (Matrix.of fun i j => a j i) 0 1
  have hw_eq : w = fun k => ∑ t : Fin r₁ ⊕ Fin s, B t k • v t := by
    funext k
    cases k with
    | inl i =>
      rw [Fintype.sum_sum_type]
      simp only [w, v, B, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    | inr j =>
      rw [Fintype.sum_sum_type]
      simp only [w, v, B, Sum.elim_inr, Sum.elim_inl, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hl : l j = (l j - q j) + q j := (sub_add_cancel _ _).symm
      rw [hl, ha j]
  have hG_w : (Matrix.gram ℝ (Fin.append m l)).det = (Matrix.gram ℝ w).det := by
    have hsubm : Matrix.gram ℝ w = (Matrix.gram ℝ (Fin.append m l)).submatrix e e := by
      ext x y
      cases x <;> cases y <;> simp [Matrix.gram_apply, w, e, finSumFinEquiv]
    rw [hsubm, Matrix.det_submatrix_equiv_self]
  have hG_v : Matrix.gram ℝ v =
      Matrix.fromBlocks (Matrix.gram ℝ m) 0 0 (Matrix.gram ℝ q) := by
    ext x y
    cases x with
    | inl i =>
      cases y with
      | inl i' => simp [Matrix.gram_apply, v]
      | inr j => simp [Matrix.gram_apply, v, horth i j]
    | inr j =>
      cases y with
      | inl i =>
        simp only [Matrix.gram_apply, v, Sum.elim_inr, Sum.elim_inl, Matrix.fromBlocks_apply₂₁,
          Matrix.zero_apply]
        rw [real_inner_comm]
        exact horth i j
      | inr j' => simp [Matrix.gram_apply, v]
  have hdetB : B.det = 1 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
  rw [hG_w, hw_eq, gram_sum_smul_eq_transpose_mul v B, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hdetB, hG_v, Matrix.det_fromBlocks_zero₂₁]
  ring

/-- **Exact Sublattice / Quotient Additivity (`arithDeg_exact_seq`)**:
for any primitive (saturated) sublattice `M ≤ L` with orthogonal-projection quotient `quotLat L M`:
1. `rk L = rk M + rk (quotLat L M)`,
2. `covol L = covol M * covol (quotLat L M)`,
3. `arithDeg L = arithDeg M + arithDeg (quotLat L M)`. -/
theorem arithDeg_exact_seq {L M : Submodule ℤ E} [DiscreteTopology L]
    (hM : IsSaturated L M) :
    rk L = rk M + rk (quotLat L M) ∧
    covol L = covol M * covol (quotLat L M) ∧
    arithDeg L = arithDeg M + arithDeg (quotLat L M) := by
  obtain ⟨_, hrk, hcov, hdeg⟩ := quotLat_exact_additivity hM
  exact ⟨hrk, hcov, hdeg⟩

/-- **Isometric invariance of `rk`, `covol`, and `arithDeg`**:
if `φ : L₁ ≃ₗ[ℤ] L₂` preserves Euclidean norms (`‖(φ x : E₂)‖ = ‖(x : E₁)‖`), then `L₁` and `L₂`
have identical rank, covolume, arithmetic degree, and slope. -/
theorem arithDeg_eq_of_isometric_equiv
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {L₁ : Submodule ℤ E₁} {L₂ : Submodule ℤ E₂} [DiscreteTopology L₁] [DiscreteTopology L₂]
    (φ : L₁ ≃ₗ[ℤ] L₂) (hnorm : ∀ x : L₁, ‖(φ x : E₂)‖ = ‖(x : E₁)‖) :
    rk L₁ = rk L₂ ∧ covol L₁ = covol L₂ ∧ arithDeg L₁ = arithDeg L₂ ∧ slope L₁ = slope L₂ := by
  have hrk : rk L₁ = rk L₂ := φ.finrank_eq
  let b₁ := Module.finBasis ℤ L₁
  let b₂ := b₁.map φ
  have hinner : ∀ x y : L₁, inner ℝ (φ x : E₂) (φ y : E₂) = inner ℝ (x : E₁) (y : E₁) := by
    intro x y
    have h1 := hnorm (x + y)
    have h2 := hnorm x
    have h3 := hnorm y
    have hsq1 : ‖(φ x : E₂) + (φ y : E₂)‖ ^ 2 = ‖(x : E₁) + (y : E₁)‖ ^ 2 := by
      have : ((φ (x + y) : L₂) : E₂) = (φ x : E₂) + (φ y : E₂) := by simp
      rw [← this]
      have hx : (((x + y : L₁) : E₁)) = (x : E₁) + (y : E₁) := rfl
      rw [← hx, h1]
    rw [norm_add_sq_real, norm_add_sq_real, h2, h3] at hsq1
    linarith
  have hgram : Matrix.gram ℝ (fun i => (b₂ i : E₂)) = Matrix.gram ℝ (fun i => (b₁ i : E₁)) := by
    ext i j
    simp only [Matrix.gram_apply, b₂]
    exact hinner (b₁ i) (b₁ j)
  have hcov : covol L₁ = covol L₂ := by
    rw [covol_eq_sqrt_det_gram L₁ b₁, covol_eq_sqrt_det_gram L₂ b₂, hgram]
  have hdeg : arithDeg L₁ = arithDeg L₂ := by simp [arithDeg, hcov]
  have hsl : slope L₁ = slope L₂ := by
    rw [slope_eq_arithDeg_div_rk, slope_eq_arithDeg_div_rk, hrk, hdeg]
  exact ⟨hrk, hcov, hdeg, hsl⟩

/-- **General Short Exact Sequence Additivity (`arithDeg_short_exact_seq`)**:
given a short exact sequence `0 → L₁ →[ι] L →[π] L₂ → 0` of discrete Euclidean lattices where
`ι` is an isometric embedding onto a saturated sublattice `M = range ι ≤ L` and `π` descends
to an isometry `quotLat L M ≃ L₂`, we have `arithDeg L = arithDeg L₁ + arithDeg L₂`. -/
theorem arithDeg_short_exact_seq
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {L₁ : Submodule ℤ E₁} {L : Submodule ℤ E} {L₂ : Submodule ℤ E₂}
    [DiscreteTopology L₁] [DiscreteTopology L] [DiscreteTopology L₂]
    (ι : L₁ →ₗ[ℤ] L) (hι_inj : Function.Injective ι)
    (hι_norm : ∀ x : L₁, ‖((ι x : L) : E)‖ = ‖(x : E₁)‖)
    (hι_sat : IsSaturated L (LinearMap.range (L.subtype.comp ι)))
    (ψ : quotLat L (LinearMap.range (L.subtype.comp ι)) ≃ₗ[ℤ] L₂)
    (hψ_norm : ∀ q, ‖(ψ q : E₂)‖ = ‖(q : E)‖) :
    rk L = rk L₁ + rk L₂ ∧
    covol L = covol L₁ * covol L₂ ∧
    arithDeg L = arithDeg L₁ + arithDeg L₂ := by
  let M : Submodule ℤ E := LinearMap.range (L.subtype.comp ι)
  have hDiscM : DiscreteTopology M := discreteTopology_of_le hι_sat.1
  have hDiscQ : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hι_sat
  let e₁ : L₁ ≃ₗ[ℤ] M := LinearEquiv.ofInjective (L.subtype.comp ι) (L.injective_subtype.comp hι_inj)
  have h1 := arithDeg_eq_of_isometric_equiv e₁ hι_norm
  have h2 := arithDeg_eq_of_isometric_equiv ψ hψ_norm
  obtain ⟨hrk, hcov, hdeg⟩ := arithDeg_exact_seq hι_sat
  exact ⟨by rw [hrk, h1.1, h2.1], by rw [hcov, h1.2.1, h2.2.1], by rw [hdeg, h1.2.2.1, h2.2.2.1]⟩

end ArithmeticDegreeAndExactSeq

/-! ### Exact Hilbert–Schmidt Tensor Product & Tensor Powers of Euclidean Lattices -/

section TensorProductLattices

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-- Concrete Hilbert–Schmidt Euclidean tensor product space `E₁ ⊗_HS E₂`. -/
abbrev TensorSpace (E₁ E₂ : Type*)
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E₁) × Fin (Module.finrank ℝ E₂))

/-- Concrete pure tensor `x ⊗ y ∈ E₁ ⊗_HS E₂` expressed in `stdOrthonormalBasis`. -/
def pureTensor (x : E₁) (y : E₂) : TensorSpace E₁ E₂ :=
  WithLp.toLp 2 (fun p =>
    inner ℝ (stdOrthonormalBasis ℝ E₁ p.1) x * inner ℝ (stdOrthonormalBasis ℝ E₂ p.2) y)

lemma pureTensor_add_left (x₁ x₂ : E₁) (y : E₂) :
    pureTensor (x₁ + x₂) y = pureTensor x₁ y + pureTensor x₂ y := by
  ext p
  simp [pureTensor, inner_add_right, add_mul]

lemma pureTensor_add_right (x : E₁) (y₁ y₂ : E₂) :
    pureTensor x (y₁ + y₂) = pureTensor x y₁ + pureTensor x y₂ := by
  ext p
  simp [pureTensor, inner_add_right, mul_add]

lemma pureTensor_smul_left (c : ℝ) (x : E₁) (y : E₂) :
    pureTensor (c • x) y = c • pureTensor x y := by
  ext p
  simp [pureTensor, real_inner_smul_right, mul_assoc]

lemma pureTensor_smul_right (c : ℝ) (x : E₁) (y : E₂) :
    pureTensor x (c • y) = c • pureTensor x y := by
  ext p
  simp [pureTensor, real_inner_smul_right]
  ring

lemma pureTensor_zsmul_left (n : ℤ) (x : E₁) (y : E₂) :
    pureTensor (n • x) y = n • pureTensor x y := by
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, pureTensor_smul_left]

lemma pureTensor_zsmul_right (n : ℤ) (x : E₁) (y : E₂) :
    pureTensor x (n • y) = n • pureTensor x y := by
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, pureTensor_smul_right]

lemma pureTensor_sum_left {ι : Type*} (s : Finset ι) (f : ι → E₁) (y : E₂) :
    pureTensor (∑ i ∈ s, f i) y = ∑ i ∈ s, pureTensor (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => ext p; simp [pureTensor]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pureTensor_add_left, ih]

lemma pureTensor_sum_right {ι : Type*} (s : Finset ι) (x : E₁) (g : ι → E₂) :
    pureTensor x (∑ i ∈ s, g i) = ∑ i ∈ s, pureTensor x (g i) := by
  classical
  induction s using Finset.induction with
  | empty => ext p; simp [pureTensor]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pureTensor_add_right, ih]

/-- **Exact Hilbert–Schmidt inner product formula**:
`⟪x₁ ⊗ y₁, x₂ ⊗ y₂⟫ = ⟪x₁, x₂⟫ * ⟪y₁, y₂⟫`. -/
theorem inner_pureTensor (x₁ x₂ : E₁) (y₁ y₂ : E₂) :
    inner ℝ (pureTensor x₁ y₁) (pureTensor x₂ y₂) = inner ℝ x₁ x₂ * inner ℝ y₁ y₂ := by
  let e₁ := stdOrthonormalBasis ℝ E₁
  let e₂ := stdOrthonormalBasis ℝ E₂
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, pureTensor, WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type]
  have hfac : ∀ i : Fin (Module.finrank ℝ E₁),
      ∑ j : Fin (Module.finrank ℝ E₂),
        (inner ℝ (e₁ i) x₂ * inner ℝ (e₂ j) y₂) * (inner ℝ (e₁ i) x₁ * inner ℝ (e₂ j) y₁) =
      (inner ℝ (e₁ i) x₁ * inner ℝ (e₁ i) x₂) *
        ∑ j : Fin (Module.finrank ℝ E₂), inner ℝ (e₂ j) y₁ * inner ℝ (e₂ j) y₂ := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum_eq :
      ∑ i : Fin (Module.finrank ℝ E₁), ∑ j : Fin (Module.finrank ℝ E₂),
        (inner ℝ (e₁ i) x₂ * inner ℝ (e₂ j) y₂) * (inner ℝ (e₁ i) x₁ * inner ℝ (e₂ j) y₁) =
      (∑ i : Fin (Module.finrank ℝ E₁), inner ℝ (e₁ i) x₁ * inner ℝ (e₁ i) x₂) *
        ∑ j : Fin (Module.finrank ℝ E₂), inner ℝ (e₂ j) y₁ * inner ℝ (e₂ j) y₂ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => hfac i
  rw [show (∑ x : Fin (Module.finrank ℝ E₁), ∑ y : Fin (Module.finrank ℝ E₂),
        (inner ℝ (stdOrthonormalBasis ℝ E₁ x) x₂ * inner ℝ (stdOrthonormalBasis ℝ E₂ y) y₂) *
          (inner ℝ (stdOrthonormalBasis ℝ E₁ x) x₁ * inner ℝ (stdOrthonormalBasis ℝ E₂ y) y₁)) =
      (∑ i : Fin (Module.finrank ℝ E₁), inner ℝ (e₁ i) x₁ * inner ℝ (e₁ i) x₂) *
        ∑ j : Fin (Module.finrank ℝ E₂), inner ℝ (e₂ j) y₁ * inner ℝ (e₂ j) y₂ from hsum_eq]
  have hp1 : ∑ i : Fin (Module.finrank ℝ E₁), inner ℝ (e₁ i) x₁ * inner ℝ (e₁ i) x₂ =
      inner ℝ x₁ x₂ := by
    have h := e₁.repr.inner_map_map x₁ x₂
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [← h]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, star_trivial, e₁.repr_apply_apply, e₁.repr_apply_apply, mul_comm]
  have hp2 : ∑ j : Fin (Module.finrank ℝ E₂), inner ℝ (e₂ j) y₁ * inner ℝ (e₂ j) y₂ =
      inner ℝ y₁ y₂ := by
    have h := e₂.repr.inner_map_map y₁ y₂
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [← h]
    unfold dotProduct
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, star_trivial, e₂.repr_apply_apply, e₂.repr_apply_apply, mul_comm]
  rw [hp1, hp2]

/-- Exact cross-norm property: `‖x ⊗ y‖ = ‖x‖ * ‖y‖`. -/
theorem norm_pureTensor (x : E₁) (y : E₂) : ‖pureTensor x y‖ = ‖x‖ * ‖y‖ := by
  have hsq : ‖pureTensor x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_pureTensor, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, mul_pow]
  nlinarith [norm_nonneg (pureTensor x y), mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- Exact Gram determinant formula for tensor products of two finite vector families via
Gram–Schmidt upper-triangular factorization:
`det Gram(v ⊗ w) = (det Gram v) ^ r₂ * (det Gram w) ^ r₁`. -/
theorem det_gram_pureTensor {r₁ r₂ : ℕ} (v : Fin r₁ → E₁) (w : Fin r₂ → E₂) :
    (Matrix.gram ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2))).det =
      (Matrix.gram ℝ v).det ^ r₂ * (Matrix.gram ℝ w).det ^ r₁ := by
  by_cases hr₂ : r₂ = 0
  · subst hr₂
    have : IsEmpty (Fin r₁ × Fin 0) := inferInstance
    simp [Matrix.det_isEmpty]
  have hr₂_pos : 0 < r₂ := Nat.pos_of_ne_zero hr₂
  let e : Fin r₁ × Fin r₂ ≃ Fin (r₁ * r₂) :=
    { toFun := fun p => ⟨p.1.1 * r₂ + p.2.1, by
        have h1 : p.1.1 + 1 ≤ r₁ := p.1.2
        have h2 : p.2.1 < r₂ := p.2.2
        nlinarith⟩
      invFun := fun t => (⟨t.1 / r₂, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t.2 (mul_comm r₁ r₂))⟩,
        ⟨t.1 % r₂, Nat.mod_lt t.1 hr₂_pos⟩)
      left_inv := fun p => by
        ext
        · change (p.1.1 * r₂ + p.2.1) / r₂ = p.1.1
          rw [mul_comm, Nat.mul_add_div hr₂_pos, Nat.div_eq_of_lt p.2.2, add_zero]
        · change (p.1.1 * r₂ + p.2.1) % r₂ = p.2.1
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.2]
      right_inv := fun t => by
        ext
        change (t.1 / r₂) * r₂ + t.1 % r₂ = t.1
        rw [mul_comm]
        exact Nat.div_add_mod t.1 r₂ }
  let T : Fin (r₁ * r₂) → TensorSpace E₁ E₂ :=
    fun t => pureTensor (v (e.symm t).1) (w (e.symm t).2)
  let Tstar : Fin (r₁ * r₂) → TensorSpace E₁ E₂ :=
    fun t => pureTensor (gsVec v (e.symm t).1) (gsVec w (e.symm t).2)
  let U : Matrix (Fin (r₁ * r₂)) (Fin (r₁ * r₂)) ℝ :=
    Matrix.of fun s t =>
      gsCoeff v (e.symm s).1 (e.symm t).1 * gsCoeff w (e.symm s).2 (e.symm t).2
  have hT_eq : T = fun t => ∑ s : Fin (r₁ * r₂), U s t • Tstar s := by
    funext t
    set i := (e.symm t).1
    set j := (e.symm t).2
    have hv : v i = ∑ a : Fin r₁, gsCoeff v a i • gsVec v a := gs_expansion v i
    have hw : w j = ∑ b : Fin r₂, gsCoeff w b j • gsVec w b := gs_expansion w j
    have hsum : pureTensor (v i) (w j) =
        ∑ p : Fin r₁ × Fin r₂,
          (gsCoeff v p.1 i * gsCoeff w p.2 j) • pureTensor (gsVec v p.1) (gsVec w p.2) := by
      rw [hv, hw, pureTensor_sum_left, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [pureTensor_smul_left, pureTensor_sum_right, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [pureTensor_smul_right, smul_smul]
    change pureTensor (v i) (w j) = _
    rw [hsum]
    refine Fintype.sum_equiv e _ _ fun p => ?_
    simp only [U, Tstar, Matrix.of_apply, Equiv.symm_apply_apply, i, j]
  have hU_tri : U.BlockTriangular id := by
    intro s t hst
    have hlt : t.1 < s.1 := hst
    set p := e.symm s
    set q := e.symm t
    have hs_val : s.1 = p.1.1 * r₂ + p.2.1 := by
      have : e p = s := e.apply_symm_apply s
      rw [← this]; rfl
    have ht_val : t.1 = q.1.1 * r₂ + q.2.1 := by
      have : e q = t := e.apply_symm_apply t
      rw [← this]; rfl
    change gsCoeff v p.1 q.1 * gsCoeff w p.2 q.2 = 0
    by_cases h1 : q.1 < p.1
    · rw [Stage2SiegelReduction.gsCoeff_of_gt v h1, zero_mul]
    · have hle : p.1.1 ≤ q.1.1 := Nat.le_of_not_lt h1
      have h2 : q.2 < p.2 := by
        have hp2 : p.2.1 < r₂ := p.2.2
        have hq2 : q.2.1 < r₂ := q.2.2
        have : p.1.1 = q.1.1 := by nlinarith
        exact show q.2.1 < p.2.1 by nlinarith
      rw [Stage2SiegelReduction.gsCoeff_of_gt w h2, mul_zero]
  have hU_det : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_tri]
    refine Finset.prod_eq_one fun s _ => ?_
    change gsCoeff v (e.symm s).1 (e.symm s).1 * gsCoeff w (e.symm s).2 (e.symm s).2 = 1
    rw [Stage2SiegelReduction.gsCoeff_self, Stage2SiegelReduction.gsCoeff_self, mul_one]
  have hGstar : Matrix.gram ℝ Tstar =
      Matrix.diagonal (fun s => ‖gsVec v (e.symm s).1‖ ^ 2 * ‖gsVec w (e.symm s).2‖ ^ 2) := by
    ext s t
    rw [Matrix.gram_apply, Matrix.diagonal_apply]
    change inner ℝ (pureTensor (gsVec v (e.symm s).1) (gsVec w (e.symm s).2))
      (pureTensor (gsVec v (e.symm t).1) (gsVec w (e.symm t).2)) = _
    rw [inner_pureTensor]
    split_ifs with h
    · subst h
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    · have hpq : e.symm s ≠ e.symm t := fun heq => h (e.symm.injective heq)
      by_cases h1 : (e.symm s).1 = (e.symm t).1
      · have h2 : (e.symm s).2 ≠ (e.symm t).2 := fun h2 => hpq (Prod.ext h1 h2)
        rw [gsVec_orthogonal w h2, mul_zero]
      · rw [gsVec_orthogonal v h1, zero_mul]
  have hdet_reidx :
      (Matrix.gram ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2))).det =
        (Matrix.gram ℝ T).det := by
    have hsub : Matrix.gram ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2)) =
        (Matrix.gram ℝ T).submatrix e e := by
      ext p q
      simp [Matrix.gram_apply, T]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  rw [hdet_reidx, hT_eq, gram_sum_smul_eq_transpose_mul Tstar U, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hU_det, one_mul, mul_one, hGstar, Matrix.det_diagonal]
  have hprod :
      ∏ s : Fin (r₁ * r₂), (‖gsVec v (e.symm s).1‖ ^ 2 * ‖gsVec w (e.symm s).2‖ ^ 2) =
      ∏ p : Fin r₁ × Fin r₂, (‖gsVec v p.1‖ ^ 2 * ‖gsVec w p.2‖ ^ 2) :=
    Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  rw [hprod, Fintype.prod_prod_type, det_gram_eq_prod_gsVec_norm_sq v,
    det_gram_eq_prod_gsVec_norm_sq w]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow]

private lemma sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]

/-- Concrete **Euclidean Tensor Product Lattice** `L₁ ⊗ L₂ ⊂ E₁ ⊗_HS E₂`. -/
def tensorLat (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂) : Submodule ℤ (TensorSpace E₁ E₂) :=
  Submodule.span ℤ { z : TensorSpace E₁ E₂ | ∃ x ∈ L₁, ∃ y ∈ L₂, z = pureTensor x y }

/-- **Exact Tensor-Product Lattice Invariants**:
for any two discrete Euclidean lattices `L₁ ⊂ E₁`, `L₂ ⊂ E₂`:
1. `DiscreteTopology (tensorLat L₁ L₂)`,
2. `rk (tensorLat L₁ L₂) = rk L₁ * rk L₂`,
3. `covol (tensorLat L₁ L₂) = (covol L₁) ^ (rk L₂) * (covol L₂) ^ (rk L₁)`,
4. `arithDeg (tensorLat L₁ L₂) = rk L₂ * arithDeg L₁ + rk L₁ * arithDeg L₂`. -/
theorem tensorLat_invariants (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂] :
    DiscreteTopology (tensorLat L₁ L₂) ∧
    rk (tensorLat L₁ L₂) = rk L₁ * rk L₂ ∧
    covol (tensorLat L₁ L₂) = (covol L₁) ^ (rk L₂) * (covol L₂) ^ (rk L₁) ∧
    arithDeg (tensorLat L₁ L₂) =
      (rk L₂ : ℝ) * arithDeg L₁ + (rk L₁ : ℝ) * arithDeg L₂ := by
  let r₁ := rk L₁
  let r₂ := rk L₂
  let b₁ : Basis (Fin r₁) ℤ L₁ := Module.finBasis ℤ L₁
  let b₂ : Basis (Fin r₂) ℤ L₂ := Module.finBasis ℤ L₂
  let e : Fin r₁ × Fin r₂ ≃ Fin (r₁ * r₂) := finProdFinEquiv
  let v : Fin r₁ → E₁ := fun i => (b₁ i : E₁)
  let w : Fin r₂ → E₂ := fun j => (b₂ j : E₂)
  have hdet_pos : 0 < (Matrix.gram ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2))).det := by
    rw [det_gram_pureTensor v w]
    exact mul_pos (pow_pos (det_gram_basis_pos L₁ b₁) r₂) (pow_pos (det_gram_basis_pos L₂ b₂) r₁)
  have hli_prod : LinearIndependent ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    have hdet0 : (Matrix.gram ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2))).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨c, fun h0 => hne (fun p => congrFun h0 p), ?_⟩
      ext p
      have h1 : inner ℝ (pureTensor (v p.1) (w p.2))
          (∑ q : Fin r₁ × Fin r₂, c q • pureTensor (v q.1) (w q.2)) = 0 := by
        rw [hc, inner_zero_right]
      rw [inner_sum] at h1
      simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1
    exact hdet_pos.ne' hdet0
  let gen : Fin (r₁ * r₂) → tensorLat L₁ L₂ := fun t =>
    ⟨pureTensor (v (e.symm t).1) (w (e.symm t).2),
      Submodule.subset_span ⟨v (e.symm t).1, (b₁ (e.symm t).1).2,
        w (e.symm t).2, (b₂ (e.symm t).2).2, rfl⟩⟩
  have hliR : LinearIndependent ℝ (fun t : Fin (r₁ * r₂) => (gen t : TensorSpace E₁ E₂)) := by
    have hcomp : (fun t : Fin (r₁ * r₂) => (gen t : TensorSpace E₁ E₂)) =
        (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2)) ∘ e.symm := rfl
    rw [hcomp]
    exact hli_prod.comp _ e.symm.injective
  have hliZ : LinearIndependent ℤ gen := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 : ∑ s : Fin (r₁ * r₂), (c s : ℝ) • (gen s : TensorSpace E₁ E₂) = 0 := by
      have h2 := congrArg Subtype.val hc
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hliR (fun s => (c s : ℝ)) h1 t
  have hspZ : ⊤ ≤ Submodule.span ℤ (Set.range gen) := by
    intro z _
    have hz : (z : TensorSpace E₁ E₂) ∈ tensorLat L₁ L₂ := z.2
    have hspan_sub : tensorLat L₁ L₂ ≤
        Submodule.span ℤ (Set.range fun t : Fin (r₁ * r₂) => (gen t : TensorSpace E₁ E₂)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hxL₁, y, hyL₂, rfl⟩
      have hx : x = ∑ i : Fin r₁, (b₁.repr ⟨x, hxL₁⟩ i) • v i := by
        have h := congrArg Subtype.val (b₁.sum_repr ⟨x, hxL₁⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
      have hy : y = ∑ j : Fin r₂, (b₂.repr ⟨y, hyL₂⟩ j) • w j := by
        have h := congrArg Subtype.val (b₂.sum_repr ⟨y, hyL₂⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm.trans (Finset.sum_congr rfl fun j _ => rfl)
      rw [hx, hy, pureTensor_sum_left]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [pureTensor_zsmul_left, pureTensor_sum_right]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
      rw [pureTensor_zsmul_right]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (i, j), ?_⟩)
      simp [gen]
    have hz_in := hspan_sub hz
    rw [Submodule.mem_span_range_iff_exists_fun] at hz_in
    obtain ⟨c, hc⟩ := hz_in
    have hzeq : z = ∑ t : Fin (r₁ * r₂), c t • gen t :=
      Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hc.symm)
    rw [hzeq]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  let bT : Basis (Fin (r₁ * r₂)) ℤ (tensorLat L₁ L₂) := Basis.mk hliZ hspZ
  have hbT_val : (fun t : Fin (r₁ * r₂) => (bT t : TensorSpace E₁ E₂)) =
      fun t => pureTensor (v (e.symm t).1) (w (e.symm t).2) := by
    funext t; simp [bT, gen]
  have hDiscT : DiscreteTopology (tensorLat L₁ L₂) :=
    discreteTopology_of_fin_basis_real_li bT (by simpa [hbT_val] using hliR)
  have hrkT : rk (tensorLat L₁ L₂) = r₁ * r₂ := by
    unfold rk
    rw [Module.finrank_eq_card_basis bT, Fintype.card_fin]
  have hdetT : (Matrix.gram ℝ (fun t : Fin (r₁ * r₂) => (bT t : TensorSpace E₁ E₂))).det =
      (Matrix.gram ℝ v).det ^ r₂ * (Matrix.gram ℝ w).det ^ r₁ := by
    have hsub : Matrix.gram ℝ (fun p : Fin r₁ × Fin r₂ => pureTensor (v p.1) (w p.2)) =
        (Matrix.gram ℝ (fun t : Fin (r₁ * r₂) => (bT t : TensorSpace E₁ E₂))).submatrix e e := by
      ext p q
      simp [Matrix.gram_apply, hbT_val]
    rw [← Matrix.det_submatrix_equiv_self e, ← hsub, det_gram_pureTensor v w]
  have hcovT : covol (tensorLat L₁ L₂) = (covol L₁) ^ r₂ * (covol L₂) ^ r₁ := by
    rw [covol_eq_sqrt_det_gram (tensorLat L₁ L₂) bT, hdetT,
      Real.sqrt_mul (pow_nonneg (det_gram_basis_pos L₁ b₁).le r₂),
      sqrt_pow_eq (det_gram_basis_pos L₁ b₁).le,
      sqrt_pow_eq (det_gram_basis_pos L₂ b₂).le,
      ← covol_eq_sqrt_det_gram L₁ b₁, ← covol_eq_sqrt_det_gram L₂ b₂]
  have hdegT : arithDeg (tensorLat L₁ L₂) =
      (r₂ : ℝ) * arithDeg L₁ + (r₁ : ℝ) * arithDeg L₂ := by
    unfold arithDeg
    rw [hcovT, Real.log_mul (pow_pos (covol_pos L₁) r₂).ne' (pow_pos (covol_pos L₂) r₁).ne',
      Real.log_pow, Real.log_pow]
    ring
  exact ⟨hDiscT, hrkT, hcovT, hdegT⟩

/-- **Exact Tensor-Product Arithmetic Degree (`arithDeg_tensor`)**:
`arithDeg (L₁ ⊗ L₂) = rk L₂ * arithDeg L₁ + rk L₁ * arithDeg L₂`. -/
theorem arithDeg_tensor (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂] :
    arithDeg (tensorLat L₁ L₂) =
      (rk L₂ : ℝ) * arithDeg L₁ + (rk L₁ : ℝ) * arithDeg L₂ :=
  (tensorLat_invariants L₁ L₂).2.2.2

/-- **Exact Additivity of Arithmetic Slope under Tensor Products (`slope_tensor_eq_add`)**:
for any two nonzero discrete Euclidean lattices `L₁, L₂`,
`slope (L₁ ⊗ L₂) = slope L₁ + slope L₂`. -/
theorem slope_tensor_eq_add (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂] (hL₁ : L₁ ≠ ⊥) (hL₂ : L₂ ≠ ⊥) :
    slope (tensorLat L₁ L₂) = slope L₁ + slope L₂ := by
  obtain ⟨_, hrk, _, hdeg⟩ := tensorLat_invariants L₁ L₂
  have hr1 : (rk L₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rk_pos_of_ne_bot L₁ hL₁).ne'
  have hr2 : (rk L₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rk_pos_of_ne_bot L₂ hL₂).ne'
  rw [slope_eq_arithDeg_div_rk, slope_eq_arithDeg_div_rk, slope_eq_arithDeg_div_rk, hrk, hdeg]
  push_cast
  field_simp [hr1, hr2]

end TensorProductLattices

section TensorPowerLattices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Concrete `k`-th Hilbert–Schmidt tensor power space `E^{⊗ k}`. -/
abbrev TensorPowSpace (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (k : ℕ) :=
  EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ E))

/-- Concrete `k`-fold pure tensor `v 0 ⊗ ⋯ ⊗ v (k - 1) ∈ E^{⊗ k}`. -/
def pureTensorPow {k : ℕ} (v : Fin k → E) : TensorPowSpace E k :=
  WithLp.toLp 2 (fun f => ∏ j : Fin k, inner ℝ (stdOrthonormalBasis ℝ E (f j)) (v j))

/-- Exact `k`-fold inner product identity:
`⟪v_0 ⊗ ⋯ ⊗ v_{k-1}, w_0 ⊗ ⋯ ⊗ w_{k-1}⟫ = ∏ j, ⟪v j, w j⟫`. -/
theorem inner_pureTensorPow {k : ℕ} (v w : Fin k → E) :
    inner ℝ (pureTensorPow v) (pureTensorPow w) = ∏ j : Fin k, inner ℝ (v j) (w j) := by
  let e := stdOrthonormalBasis ℝ E
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, pureTensorPow, WithLp.ofLp_toLp]
  have hprod_mul : ∀ f : Fin k → Fin (Module.finrank ℝ E),
      (∏ j : Fin k, inner ℝ (e (f j)) (w j)) * (∏ j : Fin k, inner ℝ (e (f j)) (v j)) =
      ∏ j : Fin k, (inner ℝ (e (f j)) (v j) * inner ℝ (e (f j)) (w j)) := by
    intro f
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => mul_comm _ _
  trans ∑ f : Fin k → Fin (Module.finrank ℝ E),
      ∏ j : Fin k, (inner ℝ (e (f j)) (v j) * inner ℝ (e (f j)) (w j))
  · exact Finset.sum_congr rfl fun f _ => hprod_mul f
  rw [← Fintype.prod_sum (fun j i => inner ℝ (e i) (v j) * inner ℝ (e i) (w j))]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h := e.repr.inner_map_map (v j) (w j)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← h]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, star_trivial, e.repr_apply_apply, e.repr_apply_apply, mul_comm]

/-- Concrete `k`-th tensor power lattice `L^{⊗ k} ⊂ E^{⊗ k}`. -/
def tensorPowLat (L : Submodule ℤ E) (k : ℕ) : Submodule ℤ (TensorPowSpace E k) :=
  Submodule.span ℤ { z : TensorPowSpace E k | ∃ v : Fin k → E, (∀ j, v j ∈ L) ∧ z = pureTensorPow v }

/-- Exact `k`-th tensor-power lattice arithmetic degree and slope (`k ≥ 1`):
`rk (L^{⊗ k}) = (rk L)^k`, `covol (L^{⊗ k}) = (covol L)^(k * (rk L)^(k - 1))`,
`arithDeg (L^{⊗ k}) = k * (rk L)^(k - 1) * arithDeg L`, and `slope (L^{⊗ k}) = k * slope L`. -/
theorem tensorPowLat_invariants (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ} (hk : 1 ≤ k) :
    DiscreteTopology (tensorPowLat L k) ∧
    rk (tensorPowLat L k) = (rk L) ^ k ∧
    covol (tensorPowLat L k) = (covol L) ^ (k * (rk L) ^ (k - 1)) ∧
    arithDeg (tensorPowLat L k) =
      (k : ℝ) * ((rk L : ℝ) ^ (k - 1)) * arithDeg L := by
  let r := rk L
  let b : Basis (Fin r) ℤ L := Module.finBasis ℤ L
  let v : Fin r → E := fun i => (b i : E)
  -- Order `Fin k → Fin r` via `Fin (r ^ k)` using the base-`r` lexicographic equivalence!
  -- Rather than constructing an explicit order, prove `det Gram = (det Gram v)^(k * r^(k - 1))`
  -- by induction on `k` using `det_gram_pureTensor`!
  have hgram_pow : ∀ m : ℕ, 1 ≤ m →
      (Matrix.gram ℝ (fun f : Fin m → Fin r => pureTensorPow (fun j => v (f j)))).det =
        (Matrix.gram ℝ v).det ^ (m * r ^ (m - 1)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero =>
        simp only [Nat.sub_self, pow_zero, mul_one, zero_add, pow_one]
        let e1 : (Fin 1 → Fin r) ≃ Fin r := Equiv.funUnique (Fin 1) (Fin r)
        have hsub : Matrix.gram ℝ (fun f : Fin 1 → Fin r => pureTensorPow (fun j => v (f j))) =
            (Matrix.gram ℝ v).submatrix e1 e1 := by
          ext f g
          simp [Matrix.gram_apply, inner_pureTensorPow, e1]
        rw [hsub, Matrix.det_submatrix_equiv_self]
      | succ m' =>
        have hm1 : 1 ≤ m' + 1 := Nat.succ_pos _
        have hih := ih hm1
        -- Split `Fin (m' + 2) → Fin r` as `Fin r × (Fin (m' + 1) → Fin r)` via `Fin.cons`!
        let eSplit : (Fin r × (Fin (m' + 1) → Fin r)) ≃ (Fin (m' + 2) → Fin r) :=
          { toFun := fun p => Fin.cons p.1 p.2
            invFun := fun f => (f 0, fun j => f j.succ)
            left_inv := fun p => Prod.ext (by simp) (funext fun j => by simp)
            right_inv := fun f => funext fun i => Fin.cases (by simp) (fun j => by simp) i }
        let wPrev : (Fin (m' + 1) → Fin r) → TensorPowSpace E (m' + 1) :=
          fun g => pureTensorPow (fun j => v (g j))
        have hgram_eq :
            Matrix.gram ℝ (fun p : Fin r × (Fin (m' + 1) → Fin r) =>
              pureTensor (v p.1) (wPrev p.2)) =
            (Matrix.gram ℝ (fun f : Fin (m' + 2) → Fin r =>
              pureTensorPow (fun j => v (f j)))).submatrix eSplit eSplit := by
          ext p q
          simp only [Matrix.gram_apply, Matrix.submatrix_apply, inner_pureTensor, wPrev,
            inner_pureTensorPow]
          rw [Fin.prod_univ_succ (n := m' + 1)]
          rfl
        have hdet_split :
            (Matrix.gram ℝ (fun f : Fin (m' + 2) → Fin r => pureTensorPow (fun j => v (f j)))).det =
            (Matrix.gram ℝ (fun p : Fin r × (Fin (m' + 1) → Fin r) =>
              pureTensor (v p.1) (wPrev p.2))).det := by
          rw [hgram_eq, Matrix.det_submatrix_equiv_self]
        -- Reindex `Fin (m' + 1) → Fin r` by `Fin (r ^ (m' + 1))` to apply `det_gram_pureTensor`.
        let eCard : Fin (r ^ (m' + 1)) ≃ (Fin (m' + 1) → Fin r) :=
          (Fintype.equivFinOfCardEq (by simp)).symm
        let eProd : (Fin r × Fin (r ^ (m' + 1))) ≃ (Fin r × (Fin (m' + 1) → Fin r)) :=
          Equiv.prodCongr (Equiv.refl _) eCard
        have hdet_reidx :
            (Matrix.gram ℝ (fun p : Fin r × (Fin (m' + 1) → Fin r) =>
              pureTensor (v p.1) (wPrev p.2))).det =
            (Matrix.gram ℝ (fun p : Fin r × Fin (r ^ (m' + 1)) =>
              pureTensor (v p.1) (wPrev (eCard p.2)))).det := by
          have hsub : Matrix.gram ℝ (fun p : Fin r × Fin (r ^ (m' + 1)) =>
              pureTensor (v p.1) (wPrev (eCard p.2))) =
            (Matrix.gram ℝ (fun p : Fin r × (Fin (m' + 1) → Fin r) =>
              pureTensor (v p.1) (wPrev p.2))).submatrix eProd eProd := by
            ext p q; simp [Matrix.gram_apply, eProd]
          rw [hsub, Matrix.det_submatrix_equiv_self]
        have hdet_wPrev : (Matrix.gram ℝ (fun i => wPrev (eCard i))).det =
            (Matrix.gram ℝ wPrev).det := by
          have hsub : Matrix.gram ℝ (fun i => wPrev (eCard i)) =
              (Matrix.gram ℝ wPrev).submatrix eCard eCard := by
            ext i j; simp [Matrix.gram_apply]
          rw [hsub, Matrix.det_submatrix_equiv_self]
        rw [hdet_split, hdet_reidx, det_gram_pureTensor v (fun i => wPrev (eCard i)),
          hdet_wPrev, hih, ← pow_mul, ← pow_add]
        congr 1
        simp only [Nat.add_sub_cancel]
        have hexp : r ^ (m' + 1) + (m' + 1) * r ^ m' * r = (m' + 2) * r ^ (m' + 1) := by
          rw [pow_succ]; ring
        exact hexp
  have hdet_val := hgram_pow k hk
  have hdet_pos : 0 < (Matrix.gram ℝ (fun f : Fin k → Fin r => pureTensorPow (fun j => v (f j)))).det := by
    rw [hdet_val]
    exact pow_pos (det_gram_basis_pos L b) _
  let eIdx : Fin (r ^ k) ≃ (Fin k → Fin r) := (Fintype.equivFinOfCardEq (by simp)).symm
  have hli_f : LinearIndependent ℝ (fun f : Fin k → Fin r => pureTensorPow (fun j => v (f j))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    have hdet0 : (Matrix.gram ℝ (fun f : Fin k → Fin r => pureTensorPow (fun j => v (f j)))).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨c, fun h0 => hne (fun f => congrFun h0 f), ?_⟩
      ext f
      have h1 : inner ℝ (pureTensorPow (fun j => v (f j)))
          (∑ g : Fin k → Fin r, c g • pureTensorPow (fun j => v (g j))) = 0 := by
        rw [hc, inner_zero_right]
      rw [inner_sum] at h1
      simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1
    exact hdet_pos.ne' hdet0
  let gen : Fin (r ^ k) → tensorPowLat L k := fun t =>
    ⟨pureTensorPow (fun j => v (eIdx t j)),
      Submodule.subset_span ⟨fun j => v (eIdx t j), fun j => (b (eIdx t j)).2, rfl⟩⟩
  have hliR : LinearIndependent ℝ (fun t : Fin (r ^ k) => (gen t : TensorPowSpace E k)) :=
    hli_f.comp eIdx eIdx.injective
  have hliZ : LinearIndependent ℤ gen := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 : ∑ s : Fin (r ^ k), (c s : ℝ) • (gen s : TensorPowSpace E k) = 0 := by
      have h2 := congrArg Subtype.val hc
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hliR (fun s => (c s : ℝ)) h1 t
  have hspZ : ⊤ ≤ Submodule.span ℤ (Set.range gen) := by
    intro z _
    have hz : (z : TensorPowSpace E k) ∈ tensorPowLat L k := z.2
    have hspan_sub : tensorPowLat L k ≤
        Submodule.span ℤ (Set.range fun t : Fin (r ^ k) => (gen t : TensorPowSpace E k)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨u, huL, rfl⟩
      -- Expand `pureTensorPow u` as a `ℤ`-linear combination of `pureTensorPow (v ∘ f)`.
      let coeff : Fin k → Fin r → ℤ := fun j i => b.repr ⟨u j, huL j⟩ i
      have hexpand : pureTensorPow u =
          ∑ f : Fin k → Fin r, (∏ j : Fin k, coeff j (f j)) • pureTensorPow (fun j => v (f j)) := by
        ext g
        simp only [pureTensorPow, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
        simp only [WithLp.ofLp_smul, Pi.smul_apply, zsmul_eq_mul, Int.cast_prod]
        have hu_coord : ∀ j : Fin k,
            inner ℝ (stdOrthonormalBasis ℝ E (g j)) (u j) =
              ∑ i : Fin r, (coeff j i : ℝ) * inner ℝ (stdOrthonormalBasis ℝ E (g j)) (v i) := by
          intro j
          have huj : u j = ∑ i : Fin r, (coeff j i : ℝ) • v i := by
            have h := congrArg Subtype.val (b.sum_repr ⟨u j, huL j⟩)
            rw [Submodule.coe_sum] at h
            exact h.symm.trans (Finset.sum_congr rfl fun i _ => by
              rw [Submodule.coe_smul, Int.cast_smul_eq_zsmul])
          rw [huj, inner_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [real_inner_smul_right]
        simp_rw [hu_coord]
        rw [Fintype.prod_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.prod_mul_distrib]
      rw [hexpand]
      refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨eIdx.symm f, by simp [gen]⟩
    have hz_in := hspan_sub hz
    rw [Submodule.mem_span_range_iff_exists_fun] at hz_in
    obtain ⟨c, hc⟩ := hz_in
    have hzeq : z = ∑ t : Fin (r ^ k), c t • gen t :=
      Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hc.symm)
    rw [hzeq]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  let bP : Basis (Fin (r ^ k)) ℤ (tensorPowLat L k) := Basis.mk hliZ hspZ
  have hbP_val : (fun t : Fin (r ^ k) => (bP t : TensorPowSpace E k)) =
      fun t => pureTensorPow (fun j => v (eIdx t j)) := by
    funext t; simp [bP, gen]
  have hDiscP : DiscreteTopology (tensorPowLat L k) :=
    discreteTopology_of_fin_basis_real_li bP (by simpa [hbP_val] using hliR)
  have hrkP : rk (tensorPowLat L k) = r ^ k := by
    unfold rk
    rw [Module.finrank_eq_card_basis bP, Fintype.card_fin]
  have hdetP : (Matrix.gram ℝ (fun t : Fin (r ^ k) => (bP t : TensorPowSpace E k))).det =
      (Matrix.gram ℝ v).det ^ (k * r ^ (k - 1)) := by
    have hsub : Matrix.gram ℝ (fun t : Fin (r ^ k) => (bP t : TensorPowSpace E k)) =
        (Matrix.gram ℝ (fun f : Fin k → Fin r => pureTensorPow (fun j => v (f j)))).submatrix
          eIdx eIdx := by
      ext s t; simp [Matrix.gram_apply, hbP_val]
    rw [hsub, Matrix.det_submatrix_equiv_self, hdet_val]
  have hcovP : covol (tensorPowLat L k) = (covol L) ^ (k * r ^ (k - 1)) := by
    rw [covol_eq_sqrt_det_gram (tensorPowLat L k) bP, hdetP,
      sqrt_pow_eq (det_gram_basis_pos L b).le, ← covol_eq_sqrt_det_gram L b]
  have hdegP : arithDeg (tensorPowLat L k) = (k : ℝ) * ((r : ℝ) ^ (k - 1)) * arithDeg L := by
    unfold arithDeg
    rw [hcovP, Real.log_pow]
    push_cast
    ring
  exact ⟨hDiscP, hrkP, hcovP, hdegP⟩

theorem slope_tensorPowLat (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {k : ℕ} (hk : 1 ≤ k) :
    slope (tensorPowLat L k) = (k : ℝ) * slope L := by
  obtain ⟨_, hrk, _, hdeg⟩ := tensorPowLat_invariants L hk
  have hr : (rk L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rk_pos_of_ne_bot L hL0).ne'
  have hrk_pow : ((rk L : ℝ) ^ k) = (rk L : ℝ) ^ (k - 1) * (rk L : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [slope_eq_arithDeg_div_rk, slope_eq_arithDeg_div_rk, hrk, hdeg]
  push_cast
  rw [hrk_pow]
  have hrp : (rk L : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ hr
  field_simp [hr, hrp]

end TensorPowerLattices

/-! ## Section 2: Isometric Transport, Gamma Ceiling & Unconditional Small-Section Counting -/

section SmallSectionCounting

/-- Exact volume `ω_r = √π ^ r / Γ(r / 2 + 1)` of the unit Euclidean ball in `ℝ^r`. -/
def unitBallVol (r : ℕ) : ℝ :=
  √Real.pi ^ r / Real.Gamma ((r : ℝ) / 2 + 1)

theorem unitBallVol_pos (r : ℕ) : 0 < unitBallVol r := by
  unfold unitBallVol
  have hG : 0 < Real.Gamma ((r : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

theorem volume_closedBall_eq_unitBallVol {r : ℕ} (hr : 0 < r) {R : ℝ} (hR : 0 ≤ R) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R) =
      ENNReal.ofReal (unitBallVol r * R ^ r) := by
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, ← ENNReal.ofReal_pow hR,
    ← ENNReal.ofReal_mul (pow_nonneg hR r), mul_comm]
  rfl

theorem volume_ball_eq_unitBallVol {r : ℕ} (hr : 0 < r) {R : ℝ} (hR : 0 ≤ R) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) R) =
      ENNReal.ofReal (unitBallVol r * R ^ r) := by
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow hR,
    ← ENNReal.ofReal_mul (pow_nonneg hR r), mul_comm]
  rfl

/-- Elementary half-integer Gamma identity:
`Γ(k + 3 / 2) = (√π / 2) * ∏ j ∈ range k, ((j : ℝ) + 3 / 2)`. -/
private lemma gamma_nat_add_three_halves (k : ℕ) :
    Real.Gamma ((k : ℝ) + 3 / 2) =
      (√Real.pi / 2) * ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Finset.range_zero, Finset.prod_empty, mul_one]
    have h : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  | succ k ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ]
    have h : (k : ℝ) + 1 + 3 / 2 = ((k : ℝ) + 3 / 2) + 1 := by ring
    rw [h, Real.Gamma_add_one (by positivity), ih]
    ring

/-- **Unconditional Elementary Gamma Ceiling**:
for EVERY `r ≥ 1`, `Γ(r / 2 + 1) ≤ r ^ (r / 2)`. -/
theorem gamma_half_add_one_le {r : ℕ} (hr : 1 ≤ r) :
    Real.Gamma ((r : ℝ) / 2 + 1) ≤ (r : ℝ) ^ ((r : ℝ) / 2) := by
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 1 ≤ k := by omega
    have hcast : ((k + k : ℕ) : ℝ) / 2 + 1 = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast, Real.Gamma_nat_eq_factorial]
    have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    have hk_le : (k : ℝ) ^ k ≤ ((k + k : ℕ) : ℝ) ^ k := by
      refine pow_le_pow_left₀ (Nat.cast_nonneg k) ?_ k
      push_cast; linarith
    have hrpow : ((k + k : ℕ) : ℝ) ^ (((k + k : ℕ) : ℝ) / 2) = ((k + k : ℕ) : ℝ) ^ k := by
      have he : (((k + k : ℕ) : ℝ) / 2) = (k : ℝ) := by push_cast; ring
      rw [he, Real.rpow_natCast]
    rw [hrpow]
    exact hfac.trans hk_le
  · have hcast : ((2 * k + 1 : ℕ) : ℝ) / 2 + 1 = (k : ℝ) + 3 / 2 := by push_cast; ring
    rw [hcast, gamma_nat_add_three_halves k]
    have hsqrt_le : √Real.pi / 2 ≤ 1 := by
      have hpi4 : Real.pi ≤ 4 := le_trans Real.pi_lt_four.le le_rfl
      have hsq : √Real.pi ≤ 2 := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hpi4
      linarith
    have hprod_le : ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ k := by
      calc ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2)
          ≤ ∏ _j ∈ Finset.range k, ((2 * k + 1 : ℕ) : ℝ) := by
            refine Finset.prod_le_prod (fun j _ => by positivity) fun j hj => ?_
            have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
            have hjkR : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
            push_cast; linarith
        _ = ((2 * k + 1 : ℕ) : ℝ) ^ k := by simp
    have hpow_le : ((2 * k + 1 : ℕ) : ℝ) ^ k ≤
        ((2 * k + 1 : ℕ) : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 2) := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hr) ?_
      push_cast; linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2) :=
      Finset.prod_nonneg fun _ _ => by positivity
    calc (√Real.pi / 2) * ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2)
        ≤ 1 * ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2) :=
          mul_le_mul_of_nonneg_right hsqrt_le hprod_nn
      _ = ∏ j ∈ Finset.range k, ((j : ℝ) + 3 / 2) := one_mul _
      _ ≤ ((2 * k + 1 : ℕ) : ℝ) ^ k := hprod_le
      _ ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 2) := hpow_le

/-- **Explicit Unit-Ball Log-Volume Lower Bound**:
for EVERY `r ≥ 1`,
`((r : ℝ) / 2) * Real.log Real.pi - ((r : ℝ) / 2) * Real.log (r : ℝ) ≤ Real.log (unitBallVol r)`. -/
theorem log_unitBallVol_ge {r : ℕ} (hr : 1 ≤ r) :
    ((r : ℝ) / 2) * Real.log Real.pi - ((r : ℝ) / 2) * Real.log (r : ℝ) ≤
      Real.log (unitBallVol r) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hGpos : 0 < Real.Gamma ((r : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlogG : Real.log (Real.Gamma ((r : ℝ) / 2 + 1)) ≤ ((r : ℝ) / 2) * Real.log (r : ℝ) := by
    have h := Real.log_le_log hGpos (gamma_half_add_one_le hr)
    rwa [Real.log_rpow hrpos] at h
  unfold unitBallVol
  rw [Real.log_div (pow_pos hpi r).ne' hGpos.ne', Real.log_pow, Real.log_sqrt Real.pi_pos.le]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Arakelov **small-section counting function** `h⁰_Ar(L, R) = #{v ∈ L | ‖v‖ ≤ R}`. -/
def h0Arith (L : Submodule ℤ E) (R : ℝ) : ℕ :=
  ((L : Set E) ∩ Metric.closedBall (0 : E) R).ncard

/-- Arakelov **strict small-section counting function** `#{v ∈ L | ‖v‖ < R}`. -/
def h0ArithStrict (L : Submodule ℤ E) (R : ℝ) : ℕ :=
  ((L : Set E) ∩ Metric.ball (0 : E) R).ncard

lemma h0ArithStrict_le_h0Arith (L : Submodule ℤ E) [DiscreteTopology L] (R : ℝ) :
    h0ArithStrict L R ≤ h0Arith L R :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)
    (lattice_inter_closedBall_finite L R)

lemma h0Arith_mono (L : Submodule ℤ E) [DiscreteTopology L] {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    h0Arith L R₁ ≤ h0Arith L R₂ :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hR))
    (lattice_inter_closedBall_finite L R₂)

lemma one_le_h0Arith (L : Submodule ℤ E) [DiscreteTopology L] {R : ℝ} (hR : 0 ≤ R) :
    1 ≤ h0Arith L R := by
  unfold h0Arith
  exact Set.ncard_pos (lattice_inter_closedBall_finite L R) |>.mpr
    ⟨0, L.zero_mem, Metric.mem_closedBall_self hR⟩

lemma one_le_h0ArithStrict (L : Submodule ℤ E) [DiscreteTopology L] {R : ℝ} (hR : 0 < R) :
    1 ≤ h0ArithStrict L R := by
  unfold h0ArithStrict
  have hfin : ((L : Set E) ∩ Metric.ball (0 : E) R).Finite :=
    (lattice_inter_closedBall_finite L R).subset
      (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)
  exact Set.ncard_pos hfin |>.mpr ⟨0, L.zero_mem, Metric.mem_ball_self hR⟩

/-- **Isometric Coordinate Transport to `EuclideanSpace ℝ (Fin (rk L))`**:
Every discrete lattice `L ⊂ E` of rank `r = rk L` is linearly isometric to a full-rank
`IsZLattice ℝ` lattice `Λ ⊂ EuclideanSpace ℝ (Fin r)` with identical covolume, ball counts,
and successive minima! -/
theorem exists_isometric_euclidean_lattice (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (rk L))))
      (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      ZLattice.covolume Λ volume = covol L ∧
      (∀ R : ℝ, h0Arith L R = h0Arith Λ R) ∧
      (∀ R : ℝ, h0ArithStrict L R = h0ArithStrict Λ R) ∧
      (∀ k : Fin (rk L),
        succMin L k =
          RHDirect.Stage10GeometryOfNumbers.successiveMinimum
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1) Λ k) := by
  let r := rk L
  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  have hdimV : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span L).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdimV]))
  let Φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let L₀ : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin r)) :=
    L₀.map (Φ.toLinearMap.restrictScalars ℤ)
  -- Establish `ℤ`-linear equivalence `L ≃ₗ[ℤ] Λ` preserving norms.
  let eLΛ : L ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨Φ ⟨(x : E), Submodule.subset_span x.2⟩,
        ⟨⟨(x : E), Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
      invFun := fun y => ⟨(Φ.symm (y : EuclideanSpace ℝ (Fin r)) : E), by
        rcases y.2 with ⟨v, hvL, hvy⟩
        have hv : Φ.symm (y : EuclideanSpace ℝ (Fin r)) = v := by
          rw [← hvy]; exact Φ.symm_apply_apply v
        rw [hv]; exact hvL⟩
      map_add' := fun x y => Subtype.ext (by
        exact map_add Φ ⟨(x : E), Submodule.subset_span x.2⟩ ⟨(y : E), Submodule.subset_span y.2⟩)
      map_smul' := fun n x => Subtype.ext (by
        change Φ (n • (⟨(x : E), Submodule.subset_span x.2⟩ : V)) =
          n • Φ ⟨(x : E), Submodule.subset_span x.2⟩
        exact map_zsmul Φ.toLinearMap n _)
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  have hnorm_eLΛ : ∀ x : L, ‖(eLΛ x : EuclideanSpace ℝ (Fin r))‖ = ‖(x : E)‖ := by
    intro x
    change ‖Φ ⟨(x : E), Submodule.subset_span x.2⟩‖ = ‖(x : E)‖
    exact Φ.norm_map _
  let bL : Basis (Fin r) ℤ L := Module.finBasis ℤ L
  let bΛ : Basis (Fin r) ℤ Λ := bL.map eLΛ
  have hbΛ_val : ∀ j : Fin r,
      (bΛ j : EuclideanSpace ℝ (Fin r)) = Φ ⟨(bL j : E), Submodule.subset_span (bL j).2⟩ :=
    fun _ => rfl
  have hliL : LinearIndependent ℝ (fun i => (bL i : E)) := linearIndependent_coe_basis L bL
  have hliΛ : LinearIndependent ℝ (fun i => (bΛ i : EuclideanSpace ℝ (Fin r))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hV : ∑ j, c j • (⟨(bL j : E), Submodule.subset_span (bL j).2⟩ : V) = 0 := by
      apply Φ.injective
      rw [map_zero, map_sum]
      simp only [map_smul]
      simpa only [hbΛ_val] using hc
    have hE : ∑ j, c j • (bL j : E) = 0 := by
      have := congrArg Subtype.val hV
      simpa [Submodule.coe_sum, Submodule.coe_smul] using this
    exact Fintype.linearIndependent_iff.mp hliL c hE i
  have hDiscΛ : DiscreteTopology Λ := discreteTopology_of_fin_basis_real_li bΛ hliΛ
  have hIsZΛ : IsZLattice ℝ Λ := by
    constructor
    have hspL₀ : Submodule.span ℝ (L₀ : Set V) = ⊤ := Submodule.span_span_coe_preimage
    have hspΛ : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) =
        (Submodule.span ℝ (L₀ : Set V)).map Φ.toLinearMap := by
      change Submodule.span ℝ ((Φ.toLinearMap '' (L₀ : Set V))) = _
      rw [Submodule.map_span]
    rw [hspΛ, hspL₀, Submodule.map_top, LinearMap.range_eq_top]
    exact Φ.surjective
  -- Exact covolume identity via `M * Mᵀ = Gram(bL)`.
  have hcov : ZLattice.covolume Λ volume = covol L := by
    rw [RHDirect.Stage10GeometryOfNumbers.covolume_eq_abs_det Λ bΛ,
      covol_eq_sqrt_det_gram L bL]
    let M : Matrix (Fin r) (Fin r) ℝ :=
      Matrix.of fun i j => (bΛ i : EuclideanSpace ℝ (Fin r)) j
    have hMMT : M * M.transpose = Matrix.gram ℝ (fun i => (bL i : E)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply, Matrix.gram_apply]
      have h1 : ∑ k : Fin r, (bΛ i : EuclideanSpace ℝ (Fin r)) k *
          (bΛ j : EuclideanSpace ℝ (Fin r)) k =
          inner ℝ (bΛ i : EuclideanSpace ℝ (Fin r)) (bΛ j : EuclideanSpace ℝ (Fin r)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial, dotProduct]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1]
      change inner ℝ (Φ ⟨(bL i : E), Submodule.subset_span (bL i).2⟩)
        (Φ ⟨(bL j : E), Submodule.subset_span (bL j).2⟩) = inner ℝ (bL i : E) (bL j : E)
      exact Φ.inner_map_map _ _
    have hdet : (Matrix.gram ℝ (fun i => (bL i : E))).det = |M.det| ^ 2 := by
      rw [← hMMT, Matrix.det_mul, Matrix.det_transpose, ← sq, sq_abs]
    rw [hdet, Real.sqrt_sq (abs_nonneg _)]
  -- Identical closed-ball and open-ball lattice counts.
  have hball_closed : ∀ R : ℝ, h0Arith L R = h0Arith Λ R := by
    intro R
    unfold h0Arith
    have himg : (fun x : V => Φ x) '' {v : V | (v : E) ∈ L ∧ ‖(v : E)‖ ≤ R} =
        (Λ : Set (EuclideanSpace ℝ (Fin r))) ∩ Metric.closedBall 0 R := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe,
        Metric.mem_closedBall, dist_zero_right]
      constructor
      · rintro ⟨v, ⟨hvL, hvR⟩, rfl⟩
        exact ⟨⟨v, hvL, rfl⟩, by simpa [Φ.norm_map] using hvR⟩
      · rintro ⟨⟨v, hvL, rfl⟩, hvR⟩
        exact ⟨v, ⟨hvL, by simpa [Φ.norm_map] using hvR⟩, rfl⟩
    have himgL : (Subtype.val : V → E) '' {v : V | (v : E) ∈ L ∧ ‖(v : E)‖ ≤ R} =
        (L : Set E) ∩ Metric.closedBall 0 R := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe,
        Metric.mem_closedBall, dist_zero_right]
      constructor
      · rintro ⟨v, ⟨hvL, hvR⟩, rfl⟩; exact ⟨hvL, hvR⟩
      · rintro ⟨hxL, hxR⟩; exact ⟨⟨x, Submodule.subset_span hxL⟩, ⟨hxL, hxR⟩, rfl⟩
    rw [← himg, ← himgL, Set.ncard_image_of_injective _ Φ.injective,
      Set.ncard_image_of_injective _ Subtype.val_injective]
  have hball_open : ∀ R : ℝ, h0ArithStrict L R = h0ArithStrict Λ R := by
    intro R
    unfold h0ArithStrict
    have himg : (fun x : V => Φ x) '' {v : V | (v : E) ∈ L ∧ ‖(v : E)‖ < R} =
        (Λ : Set (EuclideanSpace ℝ (Fin r))) ∩ Metric.ball 0 R := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe,
        Metric.mem_ball, dist_zero_right]
      constructor
      · rintro ⟨v, ⟨hvL, hvR⟩, rfl⟩
        exact ⟨⟨v, hvL, rfl⟩, by simpa [Φ.norm_map] using hvR⟩
      · rintro ⟨⟨v, hvL, rfl⟩, hvR⟩
        exact ⟨v, ⟨hvL, by simpa [Φ.norm_map] using hvR⟩, rfl⟩
    have himgL : (Subtype.val : V → E) '' {v : V | (v : E) ∈ L ∧ ‖(v : E)‖ < R} =
        (L : Set E) ∩ Metric.ball 0 R := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe,
        Metric.mem_ball, dist_zero_right]
      constructor
      · rintro ⟨v, ⟨hvL, hvR⟩, rfl⟩; exact ⟨hvL, hvR⟩
      · rintro ⟨hxL, hxR⟩; exact ⟨⟨x, Submodule.subset_span hxL⟩, ⟨hxL, hxR⟩, rfl⟩
    rw [← himg, ← himgL, Set.ncard_image_of_injective _ Φ.injective,
      Set.ncard_image_of_injective _ Subtype.val_injective]
  -- Identical successive minima `Stage2SiegelReduction.succMin L k = Stage10.successiveMinimum B_r Λ k`.
  have hsucc : ∀ k : Fin r,
      succMin L k =
        RHDirect.Stage10GeometryOfNumbers.successiveMinimum
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1) Λ k := by
    intro k
    unfold succMin RHDirect.Stage10GeometryOfNumbers.successiveMinimum
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ht0, v, hvL, hvli, hvR⟩
      have ht_pos : 0 < t := by
        have h0 : 0 < ‖v 0‖ := norm_pos_iff.mpr (hvli.ne_zero 0)
        exact lt_of_lt_of_le h0 (hvR 0)
      refine ⟨ht_pos, fun j => Φ ⟨v j, Submodule.subset_span (hvL j)⟩,
        fun j => ⟨⟨v j, Submodule.subset_span (hvL j)⟩, hvL j, rfl⟩, ?_, ?_⟩
      · rw [Fintype.linearIndependent_iff]
        intro c hc j
        have hV : ∑ i, c i • (⟨v i, Submodule.subset_span (hvL i)⟩ : V) = 0 := by
          apply Φ.injective
          rw [map_zero, map_sum]
          simpa only [map_smul] using hc
        have hE : ∑ i, c i • v i = 0 := by
          have := congrArg Subtype.val hV
          simpa [Submodule.coe_sum, Submodule.coe_smul] using this
        exact Fintype.linearIndependent_iff.mp hvli c hE j
      · intro j
        refine ⟨t⁻¹ • Φ ⟨v j, Submodule.subset_span (hvL j)⟩, ?_, smul_inv_smul₀ ht_pos.ne' _⟩
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ht_pos), Φ.norm_map]
        change t⁻¹ * ‖v j‖ ≤ 1
        rw [inv_mul_le_iff₀ ht_pos, mul_one]
        exact hvR j
    · rintro ⟨ht_pos, w, hwΛ, hwli, hwBall⟩
      refine ⟨ht_pos.le, fun j => (Φ.symm (w j) : E), ?_, ?_, ?_⟩
      · intro j
        rcases hwΛ j with ⟨v, hvL, hvw⟩
        have hv : Φ.symm (w j) = v := by rw [← hvw]; exact Φ.symm_apply_apply v
        dsimp only
        rw [hv]; exact hvL
      · rw [Fintype.linearIndependent_iff]
        intro c hc j
        have hV : ∑ i, c i • Φ.symm (w i) = 0 :=
          Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hc)
        have hW : ∑ i, c i • w i = 0 := by
          have := congrArg Φ hV
          simpa [map_sum, map_smul] using this
        exact Fintype.linearIndependent_iff.mp hwli c hW j
      · intro j
        rcases Set.mem_smul_set.mp (hwBall j) with ⟨u, hu, huw⟩
        have hnorm_w : ‖w j‖ ≤ t := by
          rw [← huw, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
          have hu1 : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hu
          nlinarith
        change ‖Φ.symm (w j)‖ ≤ t
        rwa [Φ.symm.norm_map]
  exact ⟨Λ, hDiscΛ, hIsZΛ, hcov, hball_closed, hball_open, hsucc⟩

/-- **UNCONDITIONAL GILLET–SOULÉ / MORIWAKI STRICT SMALL-SECTION LOWER BOUND** (via Blichfeldt):
for EVERY discrete Euclidean lattice `L ⊂ E` (`r = rk L`) and EVERY radius `R > 0`:
`(ω_r * (R / 2)^r) / covol L ≤ (h0ArithStrict L R : ℝ)`. -/
theorem h0ArithStrict_lower_bound_minkowski (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) :
    (unitBallVol (rk L) * (R / 2) ^ (rk L)) / covol L ≤ (h0ArithStrict L R : ℝ) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    have hr0 : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [hr0, covol_bot]
    have h1 : (1 : ℝ) ≤ (h0ArithStrict (⊥ : Submodule ℤ E) R : ℝ) := by
      exact_mod_cast one_le_h0ArithStrict (⊥ : Submodule ℤ E) hR
    simpa [unitBallVol] using h1
  have hr_pos : 0 < rk L := rk_pos_of_ne_bot L hL0
  obtain ⟨Λ, hDiscΛ, hIsZΛ, hcov, _, hstrict, _⟩ := exists_isometric_euclidean_lattice L
  rw [hstrict R, ← hcov]
  set N := h0ArithStrict Λ R
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  rw [div_le_iff₀ hcov_pos]
  by_contra hlt
  push Not at hlt
  have hvol_lt :
      (N : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) <
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (rk L))) (R / 2)) := by
    rw [volume_ball_eq_unitBallVol hr_pos (half_pos hR).le, ← ENNReal.ofReal_natCast N,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (unitBallVol_pos (rk L)) (pow_pos (half_pos hR) (rk L)))).mpr hlt
  obtain ⟨x, hx_inj, hx_mem, hx_diff⟩ :=
    RHDirect.Stage10GeometryOfNumbers.blichfeldt_theorem Λ
      Metric.isOpen_ball.measurableSet.nullMeasurableSet hvol_lt
  let v : Fin (N + 1) → EuclideanSpace ℝ (Fin (rk L)) := fun i => x i - x 0
  have hv_inj : Function.Injective v := fun i j hij =>
    hx_inj (sub_left_inj.mp hij)
  have hv_mem : ∀ i : Fin (N + 1),
      v i ∈ (Λ : Set (EuclideanSpace ℝ (Fin (rk L)))) ∩ Metric.ball 0 R := by
    intro i
    refine ⟨hx_diff i 0, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hi : ‖x i‖ < R / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx_mem i
    have h0 : ‖x 0‖ < R / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx_mem 0
    calc ‖x i - x 0‖ ≤ ‖x i‖ + ‖x 0‖ := norm_sub_le (x i) (x 0)
      _ < R / 2 + R / 2 := add_lt_add hi h0
      _ = R := add_halves R
  have hfin : ((Λ : Set (EuclideanSpace ℝ (Fin (rk L)))) ∩ Metric.ball 0 R).Finite :=
    (lattice_inter_closedBall_finite Λ R).subset
      (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)
  have hcard : N + 1 ≤ N := by
    have h1 : (Set.range v).ncard ≤
        ((Λ : Set (EuclideanSpace ℝ (Fin (rk L)))) ∩ Metric.ball 0 R).ncard :=
      Set.ncard_le_ncard (Set.range_subset_iff.mpr hv_mem) hfin
    rw [Set.ncard_range_of_injective hv_inj, Nat.card_fin] at h1
    exact h1
  omega

/-- **UNCONDITIONAL GILLET–SOULÉ / MORIWAKI ARITHMETIC RIEMANN–ROCH LOWER BOUND
(`h0Arith_lower_bound_minkowski`)**:
for EVERY discrete Euclidean lattice `L ⊂ E` (`r = rk L`) and EVERY `R > 0`:
`(ω_r * (R / 2)^r) / covol L ≤ (h0Arith L R : ℝ)`. -/
theorem h0Arith_lower_bound_minkowski (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) :
    (unitBallVol (rk L) * (R / 2) ^ (rk L)) / covol L ≤ (h0Arith L R : ℝ) :=
  (h0ArithStrict_lower_bound_minkowski L hR).trans
    (Nat.cast_le.mpr (h0ArithStrict_le_h0Arith L R))

/-- **Factor-of-2 Sharpened Small-Section Lower Bound via Minkowski's `k`-Pairs Theorem
(`minkowski_convex_body_multiple`)**:
for EVERY discrete Euclidean lattice `L ⊂ E` (`r = rk L`) and EVERY `R > 0`:
`2 * ((ω_r * (R / 2)^r) / covol L) - 1 ≤ (h0Arith L R : ℝ)`. -/
theorem h0Arith_lower_bound_minkowski_pairs (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) :
    2 * ((unitBallVol (rk L) * (R / 2) ^ (rk L)) / covol L) - 1 ≤ (h0Arith L R : ℝ) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    have hr0 : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [hr0, covol_bot]
    have h1 : (1 : ℝ) ≤ (h0Arith (⊥ : Submodule ℤ E) R : ℝ) := by
      exact_mod_cast one_le_h0Arith (⊥ : Submodule ℤ E) hR.le
    have hω0 : unitBallVol 0 = 1 := by simp [unitBallVol]
    rw [hω0, pow_zero, mul_one, div_one]
    linarith
  have hr_pos : 0 < rk L := rk_pos_of_ne_bot L hL0
  obtain ⟨Λ, hDiscΛ, hIsZΛ, hcov, hclosed, _, _⟩ := exists_isometric_euclidean_lattice L
  rw [hclosed R, ← hcov]
  set α : ℝ := (unitBallVol (rk L) * (R / 2) ^ (rk L)) / ZLattice.covolume Λ volume
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  have hα_pos : 0 < α :=
    div_pos (mul_pos (unitBallVol_pos (rk L)) (pow_pos (half_pos hR) (rk L))) hcov_pos
  -- Choose `k` to be the largest integer strictly less than `α` (`k = ⌈α⌉₊ - 1`).
  let k : ℕ := ⌈α⌉₊ - 1
  have hceil_pos : 1 ≤ ⌈α⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hα_pos).ne'
  have hk_lt : (k : ℝ) < α := by
    have h1 : k < ⌈α⌉₊ := Nat.sub_lt hceil_pos Nat.zero_lt_one
    exact (Nat.lt_ceil).mp h1
  have hk_ge : α - 1 ≤ (k : ℝ) := by
    have h1 : α ≤ (⌈α⌉₊ : ℝ) := Nat.le_ceil α
    have h2 : (k : ℝ) = (⌈α⌉₊ : ℝ) - 1 := by
      have : (k : ℝ) + 1 = (⌈α⌉₊ : ℝ) := by exact_mod_cast Nat.sub_add_cancel hceil_pos
      linarith
    linarith
  have hvol_K : (2 ^ (rk L) * k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) <
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) R) := by
    rw [volume_closedBall_eq_unitBallVol hr_pos hR.le]
    have hreal : (2 : ℝ) ^ (rk L) * (k : ℝ) * ZLattice.covolume Λ volume <
        unitBallVol (rk L) * R ^ (rk L) := by
      have h1 : (k : ℝ) * ZLattice.covolume Λ volume < unitBallVol (rk L) * (R / 2) ^ (rk L) :=
        (lt_div_iff₀ hcov_pos).mp hk_lt
      have h2r : (0 : ℝ) < (2 : ℝ) ^ (rk L) := by positivity
      have hpow : (2 : ℝ) ^ (rk L) * (R / 2) ^ (rk L) = R ^ (rk L) := by
        rw [← mul_pow, mul_div_cancel₀ R (two_ne_zero)]
      calc (2 : ℝ) ^ (rk L) * (k : ℝ) * ZLattice.covolume Λ volume
          = (2 : ℝ) ^ (rk L) * ((k : ℝ) * ZLattice.covolume Λ volume) := by ring
        _ < (2 : ℝ) ^ (rk L) * (unitBallVol (rk L) * (R / 2) ^ (rk L)) :=
            mul_lt_mul_of_pos_left h1 h2r
        _ = unitBallVol (rk L) * ((2 : ℝ) ^ (rk L) * (R / 2) ^ (rk L)) := by ring
        _ = unitBallVol (rk L) * R ^ (rk L) := by rw [hpow]
    have hlhs : (2 ^ (rk L) * k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) =
        ENNReal.ofReal ((2 : ℝ) ^ (rk L) * (k : ℝ) * ZLattice.covolume Λ volume) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
    rw [hlhs]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (unitBallVol_pos (rk L)) (pow_pos hR (rk L)))).mpr hreal
  obtain ⟨v, hvK, hvΛ, hv0, hvPairs⟩ :=
    RHDirect.Stage10GeometryOfNumbers.minkowski_convex_body_multiple Λ
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) R)
      (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx) hvol_K
  -- Build an explicit injection `Option (Fin k ⊕ Fin k) → (Λ ∩ closedBall 0 R)` sending
  -- `none ↦ 0`, `some (inl i) ↦ v i`, `some (inr i) ↦ -v i` (giving `2 * k + 1` points!).
  let f : Option (Fin k ⊕ Fin k) → EuclideanSpace ℝ (Fin (rk L)) := fun o =>
    match o with
    | none => 0
    | some (Sum.inl i) => v i
    | some (Sum.inr i) => -v i
  have hf_inj : Function.Injective f := by
    rintro (_ | (i | i)) (_ | (j | j)) h
    · rfl
    · exact absurd h.symm (hv0 j)
    · exact absurd (neg_eq_zero.mp h.symm) (hv0 j)
    · exact absurd h (hv0 i)
    · by_contra hne
      exact (hvPairs i j (fun hij => hne (by rw [hij]))).1 h
    · by_cases hij : i = j
      · subst hij
        exfalso
        change v i = -v i at h
        have h2v : (2 : ℝ) • v i = 0 := by
          rw [two_smul]
          have : v i + v i = 0 := by conv_rhs => rw [← add_neg_cancel (v i)]; rw [← h]
          exact this
        exact hv0 i ((smul_eq_zero.mp h2v).resolve_left (by norm_num))
      · exact absurd h (hvPairs i j hij).2
    · exact absurd (neg_eq_zero.mp h) (hv0 i)
    · by_cases hij : i = j
      · subst hij
        exfalso
        change -v i = v i at h
        have h2v : (2 : ℝ) • v i = 0 := by
          rw [two_smul]
          have : v i + v i = 0 := by conv_rhs => rw [← neg_add_cancel (v i)]; rw [h]
          exact this
        exact hv0 i ((smul_eq_zero.mp h2v).resolve_left (by norm_num))
      · exact absurd (neg_eq_iff_eq_neg.mp h) (hvPairs i j hij).2
    · by_contra hne
      exact (hvPairs i j (fun hij => hne (by rw [hij]))).1 (neg_inj.mp h)
  have hf_mem : ∀ o, f o ∈ (Λ : Set (EuclideanSpace ℝ (Fin (rk L)))) ∩ Metric.closedBall 0 R := by
    rintro (_ | (i | i))
    · exact ⟨Λ.zero_mem, Metric.mem_closedBall_self hR.le⟩
    · exact ⟨(hvΛ i).1, (hvK i).1⟩
    · exact ⟨(hvΛ i).2, (hvK i).2⟩
  have hcard : 2 * k + 1 ≤ h0Arith Λ R := by
    have h1 := Set.ncard_le_ncard (Set.range_subset_iff.mpr hf_mem)
      (lattice_inter_closedBall_finite Λ R)
    rw [Set.ncard_range_of_injective hf_inj] at h1
    have hnc : Nat.card (Option (Fin k ⊕ Fin k)) = 2 * k + 1 := by
      simp [Nat.card_eq_fintype_card]; omega
    rwa [hnc] at h1
  have hcardR : (2 : ℝ) * (k : ℝ) + 1 ≤ (h0Arith Λ R : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Logarithmic Gillet–Soulé / Moriwaki Lower Bound (strict balls `‖v‖ < R`)**:
`arithDeg L + rk L * log (R / 2) + log ω_r ≤ log (h0ArithStrict L R)`. -/
theorem log_h0ArithStrict_lower_bound (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) :
    arithDeg L + (rk L : ℝ) * Real.log (R / 2) + Real.log (unitBallVol (rk L)) ≤
      Real.log (h0ArithStrict L R : ℝ) := by
  have hpos : 0 < (unitBallVol (rk L) * (R / 2) ^ (rk L)) / covol L :=
    div_pos (mul_pos (unitBallVol_pos _) (pow_pos (half_pos hR) _)) (covol_pos L)
  have hlog := Real.log_le_log hpos (h0ArithStrict_lower_bound_minkowski L hR)
  rw [Real.log_div (mul_pos (unitBallVol_pos _) (pow_pos (half_pos hR) _)).ne' (covol_pos L).ne',
    Real.log_mul (unitBallVol_pos _).ne' (pow_pos (half_pos hR) _).ne', Real.log_pow] at hlog
  unfold arithDeg
  linarith

/-- **Logarithmic Gillet–Soulé / Moriwaki Lower Bound (closed balls `‖v‖ ≤ R`)**:
`arithDeg L + rk L * log (R / 2) + log ω_r ≤ log (h0Arith L R)`. -/
theorem log_h0Arith_lower_bound (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) :
    arithDeg L + (rk L : ℝ) * Real.log (R / 2) + Real.log (unitBallVol (rk L)) ≤
      Real.log (h0Arith L R : ℝ) := by
  have hpos : (0 : ℝ) < (h0ArithStrict L R : ℝ) := Nat.cast_pos.mpr (one_le_h0ArithStrict L hR)
  exact (log_h0ArithStrict_lower_bound L hR).trans
    (Real.log_le_log hpos (Nat.cast_le.mpr (h0ArithStrict_le_h0Arith L R)))

/-- **Explicit Slope Form of Moriwaki Small-Section Counting (`moriwaki_small_section_count`)**:
for EVERY nonzero discrete Euclidean lattice `L ⊂ E` of rank `r = rk L`:
`r * (slope L - (1 / 2) * log r - log (2 / √π)) ≤ log (h0ArithStrict L 1) ≤ log (h0Arith L 1)`. -/
theorem moriwaki_small_section_count (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    (rk L : ℝ) * (slope L - (1 / 2) * Real.log (rk L : ℝ) - Real.log (2 / √Real.pi)) ≤
      Real.log (h0ArithStrict L 1 : ℝ) ∧
    Real.log (h0ArithStrict L 1 : ℝ) ≤ Real.log (h0Arith L 1 : ℝ) := by
  have hr : 1 ≤ rk L := rk_pos_of_ne_bot L hL0
  have h1 := log_h0ArithStrict_lower_bound L zero_lt_one
  have h2 := log_unitBallVol_ge hr
  have hdeg := arithDeg_eq_rk_mul_slope L hL0
  have hlog2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hlogC : Real.log (2 / √Real.pi) = Real.log 2 - (1 / 2) * Real.log Real.pi := by
    rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).ne',
      Real.log_sqrt Real.pi_pos.le]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdeg, hlog2] at h1
    rw [hlogC]
    linarith
  · have hpos : (0 : ℝ) < (h0ArithStrict L 1 : ℝ) :=
      Nat.cast_pos.mpr (one_le_h0ArithStrict L zero_lt_one)
    exact Real.log_le_log hpos (Nat.cast_le.mpr (h0ArithStrict_le_h0Arith L 1))

end SmallSectionCounting

/-! ## Section 3: Symmetric-Power Hermitian Lattices, Arithmetic Hilbert–Samuel & Moriwaki Bigness -/

section SymmetricPowerAndAHS

/-- Weak compositions (exponent multi-indices) `α : Fin r → ℕ` of total degree `∑ i, α i = k`. -/
def MultiIndex (r k : ℕ) : Type :=
  { α : Fin r → ℕ // ∑ i : Fin r, α i = k }

instance instDecidableEqMultiIndex (r k : ℕ) : DecidableEq (MultiIndex r k) :=
  Subtype.instDecidableEq

/-- Explicit `Fintype` instance on `MultiIndex r k` via the bounded box `[0, k]^r`. -/
instance instFintypeMultiIndex (r k : ℕ) : Fintype (MultiIndex r k) :=
  Fintype.ofFinset
    ((Fintype.piFinset fun _ : Fin r => Finset.range (k + 1)).filter
      fun α => ∑ i : Fin r, α i = k)
    (fun α => by
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      constructor
      · intro h; exact h.2
      · intro hsum
        refine ⟨fun i => ?_, hsum⟩
        have hle : α i ≤ k := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega)

/-- Exact stars-and-bars cardinality of `MultiIndex (r + 1) k`:
`Fintype.card (MultiIndex (r + 1) k) = Nat.choose (k + r) k`. -/
theorem card_multiIndex_succ :
    ∀ r k : ℕ, Fintype.card (MultiIndex (r + 1) k) = Nat.choose (k + r) k
  | 0, k => by
    have : Unique (MultiIndex 1 k) :=
      { default := ⟨fun _ => k, by simp⟩
        uniq := fun α => Subtype.ext (funext fun i => by
          fin_cases i
          simpa [Fin.sum_univ_one] using α.2) }
    rw [Fintype.card_unique, Nat.add_zero, Nat.choose_self]
  | r + 1, 0 => by
    have : Unique (MultiIndex (r + 2) 0) :=
      { default := ⟨fun _ => 0, by simp⟩
        uniq := fun α => Subtype.ext (funext fun i => by
          have h := Finset.sum_eq_zero_iff.mp α.2 i (Finset.mem_univ i)
          exact h) }
    rw [Fintype.card_unique, Nat.zero_add, Nat.choose_zero_right]
  | r + 1, k + 1 => by
    let e : MultiIndex (r + 2) (k + 1) ≃
        MultiIndex (r + 1) (k + 1) ⊕ MultiIndex (r + 2) k :=
      { toFun := fun α =>
          if h0 : α.1 0 = 0 then
            Sum.inl ⟨fun i => α.1 i.succ, by
              have h := α.2
              rw [Fin.sum_univ_succ, h0, zero_add] at h
              exact h⟩
          else
            Sum.inr ⟨Fin.cons (α.1 0 - 1) (fun i => α.1 i.succ), by
              have h := α.2
              rw [Fin.sum_univ_succ] at h ⊢
              simp only [Fin.cons_zero, Fin.cons_succ]
              omega⟩
        invFun := fun s =>
          match s with
          | Sum.inl β => ⟨Fin.cons 0 β.1, by
              rw [Fin.sum_univ_succ]
              simpa only [Fin.cons_zero, Fin.cons_succ, zero_add] using β.2⟩
          | Sum.inr γ => ⟨Fin.cons (γ.1 0 + 1) (fun i => γ.1 i.succ), by
              have h := γ.2
              rw [Fin.sum_univ_succ] at h ⊢
              simp only [Fin.cons_zero, Fin.cons_succ]
              omega⟩
        left_inv := fun α => by
          by_cases h0 : α.1 0 = 0
          · simp only [dif_pos h0]
            apply Subtype.ext
            funext i
            refine Fin.cases ?_ (fun j => by simp) i
            simp [h0]
          · simp only [dif_neg h0]
            apply Subtype.ext
            funext i
            refine Fin.cases ?_ (fun j => by simp) i
            simp only [Fin.cons_zero]
            omega
        right_inv := fun s => by
          cases s with
          | inl β =>
            simp only [Fin.cons_zero, ↓reduceDIte]
            congr 1
          | inr γ =>
            have hne : γ.1 0 + 1 ≠ 0 := Nat.succ_ne_zero _
            simp only [Fin.cons_zero, dif_neg hne]
            congr 1
            apply Subtype.ext
            funext i
            refine Fin.cases ?_ (fun j => by simp) i
            simp }
    rw [Fintype.card_congr e, Fintype.card_sum, card_multiIndex_succ r (k + 1),
      card_multiIndex_succ (r + 1) k]
    have h1 : k + 1 + (r + 1) = (k + r + 1) + 1 := by omega
    have h2 : k + 1 + r = k + r + 1 := by omega
    have h3 : k + (r + 1) = k + r + 1 := by omega
    rw [h1, Nat.choose_succ_succ, h2, h3, add_comm]

theorem card_multiIndex {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Fintype.card (MultiIndex r k) = Nat.choose (k + r - 1) k := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hr)
  simpa [Nat.add_sub_cancel] using card_multiIndex_succ r' k

theorem card_multiIndex_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    0 < Fintype.card (MultiIndex r k) := by
  rw [card_multiIndex hr k]
  exact Nat.choose_pos (by omega)

/-- **Polynomial Growth Bound on `Sym^k` Rank**:
for `r ≥ 1`, `Fintype.card (MultiIndex r k) ≤ (k + 1) ^ r`. -/
theorem card_multiIndex_le_pow {r : ℕ} (k : ℕ) :
    Fintype.card (MultiIndex r k) ≤ (k + 1) ^ r := by
  let g : MultiIndex r k → (Fin r → Fin (k + 1)) := fun α i =>
    ⟨α.1 i, Nat.lt_succ_of_le
      (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) α.2.le)⟩
  have hg : Function.Injective g := fun α β h =>
    Subtype.ext (funext fun i => congrArg Fin.val (congrFun h i))
  simpa [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective g hg

/-- **Coordinate-Sum Symmetry Identity**:
for every coordinate `i : Fin r`, `r * ∑ α : MultiIndex r k, α.1 i = k * Fintype.card (MultiIndex r k)`. -/
theorem sum_multiIndex_coord {r k : ℕ} (i : Fin r) :
    r * ∑ α : MultiIndex r k, α.1 i = k * Fintype.card (MultiIndex r k) := by
  have hsymm : ∀ j : Fin r, ∑ α : MultiIndex r k, α.1 j = ∑ α : MultiIndex r k, α.1 i := by
    intro j
    let σ : Equiv.Perm (Fin r) := Equiv.swap i j
    let e : MultiIndex r k ≃ MultiIndex r k :=
      { toFun := fun α => ⟨α.1 ∘ σ,
          (Fintype.sum_equiv σ _ _ (fun _ => rfl)).trans α.2⟩
        invFun := fun α => ⟨α.1 ∘ σ,
          (Fintype.sum_equiv σ _ _ (fun _ => rfl)).trans α.2⟩
        left_inv := fun α => Subtype.ext (funext fun t => by simp [σ])
        right_inv := fun α => Subtype.ext (funext fun t => by simp [σ]) }
    refine Fintype.sum_equiv e _ _ fun α => ?_
    change α.1 j = α.1 (σ i)
    simp [σ]
  calc r * ∑ α : MultiIndex r k, α.1 i
      = ∑ j : Fin r, ∑ α : MultiIndex r k, α.1 i := by simp
    _ = ∑ j : Fin r, ∑ α : MultiIndex r k, α.1 j :=
        Finset.sum_congr rfl fun j _ => (hsymm j).symm
    _ = ∑ α : MultiIndex r k, ∑ j : Fin r, α.1 j := Finset.sum_comm
    _ = ∑ _α : MultiIndex r k, k := Finset.sum_congr rfl fun α _ => α.2
    _ = k * Fintype.card (MultiIndex r k) := by simp [mul_comm]

/-- Concrete diagonal/orthogonal Hermitian lattice `diagLat c = ⊕_i ℤ · (c_i e_i)` inside `ℝ^ι`. -/
def diagLat {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range fun i : ι => c i • (EuclideanSpace.single i (1 : ℝ)))

/-- Exact rank, covolume, and arithmetic degree of an orthogonal Hermitian lattice `diagLat c`
with positive basis norms `c i > 0`. -/
theorem diagLat_invariants {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    DiscreteTopology (diagLat c) ∧
    rk (diagLat c) = Fintype.card ι ∧
    covol (diagLat c) = ∏ i : ι, c i ∧
    arithDeg (diagLat c) = -∑ i : ι, Real.log (c i) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let gen : Fin (Fintype.card ι) → diagLat c := fun j =>
    ⟨c (e j) • EuclideanSpace.single (e j) (1 : ℝ), Submodule.subset_span ⟨e j, rfl⟩⟩
  have hliR : LinearIndependent ℝ (fun j : Fin (Fintype.card ι) => (gen j : EuclideanSpace ℝ ι)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hcoord := congrFun (congrArg WithLp.ofLp hg) (e j)
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, gen, EuclideanSpace.single, PiLp.single_apply] at hcoord
    rw [Finset.sum_eq_single j] at hcoord
    · simp only [↓reduceIte, mul_one] at hcoord
      exact (mul_eq_zero.mp hcoord).resolve_right (hc (e j)).ne'
    · intro k _ hkj
      have hne : e j ≠ e k := fun h => hkj (e.injective h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hliZ : LinearIndependent ℤ gen := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : ∑ k, (g k : ℝ) • (gen k : EuclideanSpace ℝ ι) = 0 := by
      have h2 := congrArg Subtype.val hg
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hliR (fun k => (g k : ℝ)) h1 j
  have hspZ : ⊤ ≤ Submodule.span ℤ (Set.range gen) := by
    intro x _
    have hx : (x : EuclideanSpace ℝ ι) ∈
        Submodule.span ℤ (Set.range fun i : ι => c i • (EuclideanSpace.single i (1 : ℝ))) := x.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨a, ha⟩ := hx
    have hxeq : x = ∑ j : Fin (Fintype.card ι), a (e j) • gen j := by
      apply Subtype.ext
      rw [Submodule.coe_sum, ← ha]
      exact (Fintype.sum_equiv e _ _ (fun j => by simp [gen])).symm
    rw [hxeq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b : Basis (Fin (Fintype.card ι)) ℤ (diagLat c) := Basis.mk hliZ hspZ
  have hb_val : ∀ j, (b j : EuclideanSpace ℝ ι) = c (e j) • EuclideanSpace.single (e j) (1 : ℝ) :=
    fun j => by simp [b, gen]
  have hDisc : DiscreteTopology (diagLat c) :=
    discreteTopology_of_fin_basis_real_li b (by
      have hEq : (fun j => (b j : EuclideanSpace ℝ ι)) = fun j => (gen j : EuclideanSpace ℝ ι) :=
        funext hb_val
      rwa [hEq])
  have hrk : rk (diagLat c) = Fintype.card ι := by
    unfold rk
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hgram : Matrix.gram ℝ (fun j => (b j : EuclideanSpace ℝ ι)) =
      Matrix.diagonal (fun j => c (e j) ^ 2) := by
    ext j l
    rw [Matrix.gram_apply, Matrix.diagonal_apply, hb_val j, hb_val l,
      real_inner_smul_left, real_inner_smul_right]
    have hsingle : inner ℝ (EuclideanSpace.single (e j) (1 : ℝ))
        (EuclideanSpace.single (e l) (1 : ℝ)) = if j = l then 1 else 0 := by
      rw [EuclideanSpace.inner_single_left]
      simp only [EuclideanSpace.single, PiLp.single_apply, conj_trivial, one_mul,
        e.injective.eq_iff]
    rw [hsingle]
    split_ifs with h
    · subst h; ring
    · ring
  have hcov : covol (diagLat c) = ∏ i : ι, c i := by
    rw [covol_eq_sqrt_det_gram (diagLat c) b, hgram, Matrix.det_diagonal,
      show (∏ j : Fin (Fintype.card ι), c (e j) ^ 2) = (∏ j : Fin (Fintype.card ι), c (e j)) ^ 2 by
        rw [Finset.prod_pow],
      Real.sqrt_sq (Finset.prod_nonneg fun j _ => (hc (e j)).le)]
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hdeg : arithDeg (diagLat c) = -∑ i : ι, Real.log (c i) := by
    unfold arithDeg
    rw [hcov, Real.log_prod (fun i _ => (hc i).ne')]
  exact ⟨hDisc, hrk, hcov, hdeg⟩

/-- Weighted `k`-th symmetric-power Hermitian lattice `Sym^k_w(diagLat c)` with basis norms
`w α * ∏ i, c i ^ (α.1 i)` (capturing both monomial symmetric powers `w = 1` and Bergman /
Fubini–Study distorted symmetric-power metrics!). -/
def symPowWeightedLat {r : ℕ} (c : Fin r → ℝ) {k : ℕ} (w : MultiIndex r k → ℝ) :
    Submodule ℤ (EuclideanSpace ℝ (MultiIndex r k)) :=
  diagLat (fun α : MultiIndex r k => w α * ∏ i : Fin r, c i ^ (α.1 i))

/-- Monomial `k`-th symmetric-power Hermitian lattice `Sym^k(diagLat c)` (`w ≡ 1`). -/
def symPowMonomialLat {r : ℕ} (c : Fin r → ℝ) (k : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (MultiIndex r k)) :=
  symPowWeightedLat c (fun _ : MultiIndex r k => (1 : ℝ))

/-- **Exact Weighted Symmetric-Power Arithmetic Degree Formula**:
`arithDeg (Sym^k_w(diagLat c)) = k * rk(Sym^k) * slope(diagLat c) - ∑ α, log (w α)`. -/
theorem arithDeg_symPowWeightedLat {r : ℕ} (hr : 1 ≤ r) (c : Fin r → ℝ) (hc : ∀ i, 0 < c i)
    {k : ℕ} (w : MultiIndex r k → ℝ) (hw : ∀ α, 0 < w α) :
    DiscreteTopology (symPowWeightedLat c w) ∧
    rk (symPowWeightedLat c w) = Fintype.card (MultiIndex r k) ∧
    arithDeg (symPowWeightedLat c w) =
      (k : ℝ) * (Fintype.card (MultiIndex r k) : ℝ) * slope (diagLat c) -
        ∑ α : MultiIndex r k, Real.log (w α) := by
  have hnorm_pos : ∀ α : MultiIndex r k, 0 < w α * ∏ i : Fin r, c i ^ (α.1 i) :=
    fun α => mul_pos (hw α) (Finset.prod_pos fun i _ => pow_pos (hc i) _)
  obtain ⟨hDisc, hrk, _, hdeg⟩ := diagLat_invariants _ hnorm_pos
  obtain ⟨_, hrkC, _, hdegC⟩ := diagLat_invariants c hc
  have hsum_log :
      ∑ α : MultiIndex r k, Real.log (w α * ∏ i : Fin r, c i ^ (α.1 i)) =
      (∑ α : MultiIndex r k, Real.log (w α)) +
        ∑ i : Fin r, ((∑ α : MultiIndex r k, α.1 i : ℕ) : ℝ) * Real.log (c i) := by
    have hterm : ∀ α : MultiIndex r k,
        Real.log (w α * ∏ i : Fin r, c i ^ (α.1 i)) =
          Real.log (w α) + ∑ i : Fin r, (α.1 i : ℝ) * Real.log (c i) := by
      intro α
      rw [Real.log_mul (hw α).ne' (Finset.prod_pos fun i _ => pow_pos (hc i) _).ne',
        Real.log_prod (fun i _ => (pow_pos (hc i) _).ne')]
      simp_rw [Real.log_pow]
    simp_rw [hterm, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, Nat.cast_sum]
  have hcoord_real : ∀ i : Fin r,
      ((∑ α : MultiIndex r k, α.1 i : ℕ) : ℝ) =
        ((k : ℝ) * (Fintype.card (MultiIndex r k) : ℝ)) / (r : ℝ) := by
    intro i
    have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
    rw [eq_div_iff hrpos.ne', mul_comm]
    exact_mod_cast sum_multiIndex_coord i
  have hslC : slope (diagLat c) = (-∑ i : Fin r, Real.log (c i)) / (r : ℝ) := by
    rw [slope_eq_arithDeg_div_rk, hrkC, Fintype.card_fin, hdegC]
  refine ⟨hDisc, hrk, ?_⟩
  unfold symPowWeightedLat
  rw [hdeg, hsum_log]
  simp_rw [hcoord_real, ← Finset.mul_sum]
  rw [hslC]
  ring

/-- **Exact Monomial Symmetric-Power Slope Scaling**:
`slope (Sym^k(diagLat c)) = k * slope (diagLat c)`. -/
theorem slope_symPowMonomialLat {r : ℕ} (hr : 1 ≤ r) (c : Fin r → ℝ) (hc : ∀ i, 0 < c i) (k : ℕ) :
    arithDeg (symPowMonomialLat c k) =
      (k : ℝ) * (rk (symPowMonomialLat c k) : ℝ) * slope (diagLat c) ∧
    slope (symPowMonomialLat c k) = (k : ℝ) * slope (diagLat c) := by
  obtain ⟨_, hrk, hdeg⟩ := arithDeg_symPowWeightedLat hr c hc
    (fun _ : MultiIndex r k => (1 : ℝ)) (fun _ => zero_lt_one)
  simp only [Real.log_one, Finset.sum_const_zero, sub_zero] at hdeg
  have hcard_ne : (Fintype.card (MultiIndex r k) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_multiIndex_pos hr k).ne'
  refine ⟨by unfold symPowMonomialLat; rw [hrk]; exact hdeg, ?_⟩
  unfold symPowMonomialLat
  rw [slope_eq_arithDeg_div_rk, hrk, hdeg]
  field_simp [hcard_ne]

/-- Helper: `(C * log (k + 1) + B) / k → 0` as `k → ∞`. -/
private lemma tendsto_log_add_const_div_nat (C B : ℝ) :
    Tendsto (fun k : ℕ => (C * Real.log ((k : ℝ) + 1) + B) / (k : ℝ)) atTop (𝓝 0) := by
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
  have hB : Tendsto (fun k : ℕ => B / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv_nat.const_mul B
  have hsum : Tendsto (fun k : ℕ => C * (Real.log ((k : ℝ) + 1) / (k : ℝ)) + B / (k : ℝ))
      atTop (𝓝 (C * 0 + 0)) := (hlog_k.const_mul C).add hB
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr fun k => ?_
  ring

/-- **EXACT ARITHMETIC HILBERT–SAMUEL ASYMPTOTIC FOR SYMMETRIC POWERS
(`arith_hilbert_samuel_symPow_tendsto`)**:
For any orthogonal Hermitian lattice `diagLat c` (`r ≥ 1`, `c i > 0`) and ANY family of
Bergman / Fubini–Study metric distortions `w k : MultiIndex r k → ℝ` with `w k α > 0` and
`|log (w k α)| ≤ C * log (k + 1) + B`, the normalized arithmetic degree converges exactly:
`arithDeg (Sym^k_{w_k}(diagLat c)) / (k * rk (Sym^k)) → slope (diagLat c)` as `k → ∞`! -/
theorem arith_hilbert_samuel_symPow_tendsto {r : ℕ} (hr : 1 ≤ r) (c : Fin r → ℝ)
    (hc : ∀ i, 0 < c i) (w : ∀ k : ℕ, MultiIndex r k → ℝ) (hw : ∀ k α, 0 < w k α)
    (C B : ℝ) (hdist : ∀ k α, |Real.log (w k α)| ≤ C * Real.log ((k : ℝ) + 1) + B) :
    Tendsto (fun k : ℕ =>
        arithDeg (symPowWeightedLat c (w k)) /
          ((k : ℝ) * (rk (symPowWeightedLat c (w k)) : ℝ)))
      atTop (𝓝 (slope (diagLat c))) := by
  have hzero : Tendsto (fun k : ℕ =>
      (arithDeg (symPowWeightedLat c (w k)) /
        ((k : ℝ) * (rk (symPowWeightedLat c (w k)) : ℝ))) - slope (diagLat c))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_log_add_const_div_nat C B)
    filter_upwards [eventually_ge_atTop 1] with k hk
    obtain ⟨_, hrk, hdeg⟩ := arithDeg_symPowWeightedLat hr c hc (w k) (hw k)
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hcard_pos : (0 : ℝ) < (Fintype.card (MultiIndex r k) : ℝ) :=
      Nat.cast_pos.mpr (card_multiIndex_pos hr k)
    have hdiff :
        arithDeg (symPowWeightedLat c (w k)) /
            ((k : ℝ) * (rk (symPowWeightedLat c (w k)) : ℝ)) - slope (diagLat c) =
          -(∑ α : MultiIndex r k, Real.log (w k α)) /
            ((k : ℝ) * (Fintype.card (MultiIndex r k) : ℝ)) := by
      rw [hrk, hdeg]
      field_simp [hk_pos.ne', hcard_pos.ne']
      ring
    rw [hdiff, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (mul_pos hk_pos hcard_pos)]
    have hsum_le : |∑ α : MultiIndex r k, Real.log (w k α)| ≤
        (Fintype.card (MultiIndex r k) : ℝ) * (C * Real.log ((k : ℝ) + 1) + B) := by
      calc |∑ α : MultiIndex r k, Real.log (w k α)|
          ≤ ∑ α : MultiIndex r k, |Real.log (w k α)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _α : MultiIndex r k, (C * Real.log ((k : ℝ) + 1) + B) :=
            Finset.sum_le_sum fun α _ => hdist k α
        _ = (Fintype.card (MultiIndex r k) : ℝ) * (C * Real.log ((k : ℝ) + 1) + B) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc |∑ α : MultiIndex r k, Real.log (w k α)| /
          ((k : ℝ) * (Fintype.card (MultiIndex r k) : ℝ))
        ≤ ((Fintype.card (MultiIndex r k) : ℝ) * (C * Real.log ((k : ℝ) + 1) + B)) /
            ((k : ℝ) * (Fintype.card (MultiIndex r k) : ℝ)) :=
          div_le_div_of_nonneg_right hsum_le (mul_pos hk_pos hcard_pos).le
      _ = (C * Real.log ((k : ℝ) + 1) + B) / (k : ℝ) := by
          field_simp [hk_pos.ne', hcard_pos.ne']
  simpa using hzero.add_const (slope (diagLat c))

/-- **MORIWAKI BIGNESS CRITERION — POINTWISE SEQUENCE FORM (`moriwaki_bigness_asymptotic`)**:
For ANY sequence of nonzero discrete Hermitian lattices `L_k` with `slope (L_k) ≥ c`, the
logarithmic strict small-section count (`‖v‖ < 1`) satisfies for EVERY `k`:
`rk (L_k) * (c - (1 / 2) * log (rk (L_k)) - log (2 / √π)) ≤ log (h0ArithStrict (L_k) 1) ≤ log (h0Arith (L_k) 1)`. -/
theorem moriwaki_bigness_asymptotic
    {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]
    [∀ k, FiniteDimensional ℝ (E k)]
    (L : ∀ k, Submodule ℤ (E k)) [∀ k, DiscreteTopology (L k)]
    (hL0 : ∀ k, L k ≠ ⊥) {c : ℝ} (hslope : ∀ k, c ≤ slope (L k)) (k : ℕ) :
    (rk (L k) : ℝ) * (c - (1 / 2) * Real.log (rk (L k) : ℝ) - Real.log (2 / √Real.pi)) ≤
      Real.log (h0ArithStrict (L k) 1 : ℝ) ∧
    Real.log (h0ArithStrict (L k) 1 : ℝ) ≤ Real.log (h0Arith (L k) 1 : ℝ) := by
  have hm := moriwaki_small_section_count (L k) (hL0 k)
  have hle :
      (rk (L k) : ℝ) * (c - (1 / 2) * Real.log (rk (L k) : ℝ) - Real.log (2 / √Real.pi)) ≤
      (rk (L k) : ℝ) * (slope (L k) - (1 / 2) * Real.log (rk (L k) : ℝ) - Real.log (2 / √Real.pi)) :=
    mul_le_mul_of_nonneg_left (by linarith [hslope k]) (Nat.cast_nonneg _)
  exact ⟨hle.trans hm.1, hm.2⟩

/-- **MORIWAKI BIGNESS CRITERION — POLYNOMIAL-RANK EXPONENTIAL GROWTH**:
For ANY family of nonzero discrete Hermitian lattices `L_k` whose ranks grow polynomially
(`rk (L_k) ≤ C₁ * (k + 1)^D`, `C₁ ≥ 1`) and whose normalized slopes satisfy
`liminf_{k → ∞} slope (L_k) / k ≥ arithVol`:
1. `∀ ε > 0, ∀ᶠ k in atTop, arithVol - ε ≤ log (h0ArithStrict (L_k) 1) / (k * rk (L_k))`,
2. Whenever `0 < arithVol`, for all sufficiently large `k`:
   `(arithVol / 2) * k * rk (L_k) ≤ log (h0ArithStrict (L_k) 1)` (exponentially many strictly
   small sections `‖v‖ < 1`!). -/
theorem moriwaki_bigness_poly_rank_asymptotic
    {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]
    [∀ k, FiniteDimensional ℝ (E k)]
    (L : ∀ k, Submodule ℤ (E k)) [∀ k, DiscreteTopology (L k)]
    (hL0 : ∀ k, L k ≠ ⊥) (D : ℕ) {C₁ arithVol : ℝ} (hC₁ : 1 ≤ C₁)
    (hrank : ∀ k, (rk (L k) : ℝ) ≤ C₁ * ((k : ℝ) + 1) ^ D)
    (hSlopeLim : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, arithVol - ε ≤ slope (L k) / (k : ℝ)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      arithVol - ε ≤ Real.log (h0ArithStrict (L k) 1 : ℝ) / ((k : ℝ) * (rk (L k) : ℝ))) ∧
    (0 < arithVol → ∀ᶠ k : ℕ in atTop,
      (arithVol / 2) * (k : ℝ) * (rk (L k) : ℝ) ≤ Real.log (h0ArithStrict (L k) 1 : ℝ)) := by
  have hC₁_pos : 0 < C₁ := by linarith
  have hmain : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      arithVol - ε ≤ Real.log (h0ArithStrict (L k) 1 : ℝ) / ((k : ℝ) * (rk (L k) : ℝ)) := by
    intro ε hε
    have h1 := hSlopeLim (ε / 2) (half_pos hε)
    have herr := tendsto_log_add_const_div_nat ((D : ℝ) / 2)
      ((1 / 2) * Real.log C₁ + Real.log (2 / √Real.pi))
    have h2 : ∀ᶠ k : ℕ in atTop,
        (((D : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
          ((1 / 2) * Real.log C₁ + Real.log (2 / √Real.pi))) / (k : ℝ) ≤ ε / 2 := by
      have hmem := (Metric.tendsto_atTop.mp herr) (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop hmem.choose] with k hk
      have hd := hmem.choose_spec k hk
      rw [Real.dist_eq, sub_zero] at hd
      exact (le_abs_self _).trans hd.le
    filter_upwards [h1, h2, eventually_ge_atTop 1] with k hk1 hk2 hk_ge1
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_ge1
    have hrk_pos : (0 : ℝ) < (rk (L k) : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot (L k) (hL0 k))
    have hm := (moriwaki_small_section_count (L k) (hL0 k)).1
    have hlog_rk : Real.log (rk (L k) : ℝ) ≤ Real.log C₁ + (D : ℝ) * Real.log ((k : ℝ) + 1) := by
      have h := Real.log_le_log hrk_pos (hrank k)
      rw [Real.log_mul hC₁_pos.ne' (pow_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1) D).ne',
        Real.log_pow] at h
      exact h
    have hdiv := div_le_div_of_nonneg_right hm (mul_pos hk_pos hrk_pos).le
    have hlhs :
        (rk (L k) : ℝ) * (slope (L k) - (1 / 2) * Real.log (rk (L k) : ℝ) - Real.log (2 / √Real.pi)) /
          ((k : ℝ) * (rk (L k) : ℝ)) =
        slope (L k) / (k : ℝ) -
          ((1 / 2) * Real.log (rk (L k) : ℝ) + Real.log (2 / √Real.pi)) / (k : ℝ) := by
      field_simp [hk_pos.ne', hrk_pos.ne']
      ring
    rw [hlhs] at hdiv
    have hbound :
        ((1 / 2) * Real.log (rk (L k) : ℝ) + Real.log (2 / √Real.pi)) / (k : ℝ) ≤ ε / 2 := by
      calc ((1 / 2) * Real.log (rk (L k) : ℝ) + Real.log (2 / √Real.pi)) / (k : ℝ)
          ≤ (((D : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
              ((1 / 2) * Real.log C₁ + Real.log (2 / √Real.pi))) / (k : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hk_pos.le
            linarith
        _ ≤ ε / 2 := hk2
    linarith
  refine ⟨hmain, fun hpos => ?_⟩
  filter_upwards [hmain (arithVol / 2) (half_pos hpos), eventually_ge_atTop 1] with k hk hk1
  have hden : 0 < (k : ℝ) * (rk (L k) : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hk1) (Nat.cast_pos.mpr (rk_pos_of_ne_bot (L k) (hL0 k)))
  have h1 : arithVol / 2 ≤ Real.log (h0ArithStrict (L k) 1 : ℝ) / ((k : ℝ) * (rk (L k) : ℝ)) := by
    linarith
  have h2 := (le_div_iff₀ hden).mp h1
  linarith

/-- **Complete Symmetric-Power Arithmetic Hilbert–Samuel & Moriwaki Bigness Theorem
(`moriwaki_bigness_symPow_asymptotic`)**:
For any ample orthogonal Hermitian lattice `diagLat c` (`r ≥ 1`, `c i > 0`, `slope (diagLat c) > 0`)
and any Bergman / Fubini–Study distorted symmetric-power family `L_k = Sym^k_{w_k}(diagLat c)`
(`|log (w_k α)| ≤ C * log (k + 1) + B`):
1. Exact AHS limit: `arithDeg (L_k) / (k * rk (L_k)) → slope (diagLat c)`,
2. Exponential strict small-section growth (`‖v‖ < 1`):
   `∀ᶠ k in atTop, (slope (diagLat c) / 2) * k * rk (L_k) ≤ log (h0ArithStrict (L_k) 1)`. -/
theorem moriwaki_bigness_symPow_asymptotic {r : ℕ} (hr : 1 ≤ r) (c : Fin r → ℝ)
    (hc : ∀ i, 0 < c i) (hpos : 0 < slope (diagLat c))
    (w : ∀ k : ℕ, MultiIndex r k → ℝ) (hw : ∀ k α, 0 < w k α)
    (C B : ℝ) (hdist : ∀ k α, |Real.log (w k α)| ≤ C * Real.log ((k : ℝ) + 1) + B) :
    Tendsto (fun k : ℕ =>
        arithDeg (symPowWeightedLat c (w k)) /
          ((k : ℝ) * (rk (symPowWeightedLat c (w k)) : ℝ)))
      atTop (𝓝 (slope (diagLat c))) ∧
    (∀ᶠ k : ℕ in atTop,
      (slope (diagLat c) / 2) * (k : ℝ) * (rk (symPowWeightedLat c (w k)) : ℝ) ≤
        Real.log (h0ArithStrict (symPowWeightedLat c (w k)) 1 : ℝ)) := by
  have hAHS := arith_hilbert_samuel_symPow_tendsto hr c hc w hw C B hdist
  have : ∀ k, DiscreteTopology (symPowWeightedLat c (w k)) :=
    fun k => (arithDeg_symPowWeightedLat hr c hc (w k) (hw k)).1
  have hne : ∀ k, symPowWeightedLat c (w k) ≠ ⊥ := by
    intro k hbot
    have hrk := (arithDeg_symPowWeightedLat hr c hc (w k) (hw k)).2.1
    rw [hbot] at hrk
    have hrk0 : rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (MultiIndex r k))) = 0 := by simp [rk]
    rw [hrk0] at hrk
    exact (card_multiIndex_pos hr k).ne hrk
  have hrank : ∀ k, (rk (symPowWeightedLat c (w k)) : ℝ) ≤ (1 : ℝ) * ((k : ℝ) + 1) ^ r := by
    intro k
    rw [(arithDeg_symPowWeightedLat hr c hc (w k) (hw k)).2.1, one_mul]
    exact_mod_cast card_multiIndex_le_pow (r := r) k
  have hSlopeLim : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      slope (diagLat c) - ε ≤ slope (symPowWeightedLat c (w k)) / (k : ℝ) := by
    intro ε hε
    have hmem := (Metric.tendsto_atTop.mp hAHS) ε hε
    filter_upwards [eventually_ge_atTop hmem.choose, eventually_ge_atTop 1] with k hk hk1
    have hd := hmem.choose_spec k hk
    rw [Real.dist_eq] at hd
    have heq : arithDeg (symPowWeightedLat c (w k)) /
        ((k : ℝ) * (rk (symPowWeightedLat c (w k)) : ℝ)) =
        slope (symPowWeightedLat c (w k)) / (k : ℝ) := by
      rw [slope_eq_arithDeg_div_rk]
      ring
    rw [heq] at hd
    linarith [(abs_lt.mp hd).1]
  have hbig := (moriwaki_bigness_poly_rank_asymptotic (fun k => symPowWeightedLat c (w k)) hne
    r le_rfl hrank hSlopeLim).2 hpos
  exact ⟨hAHS, hbig⟩

/-- **Unconditional Discharge of `HermitianCurvatureCore.moriwaki_big_of_ahs`**:
for ANY sequence of nonzero discrete Hermitian lattices `L_n` with `rk (L_n) ≤ C₁ * n^D` (`C₁ ≥ 1`),
if `arithDeg (L_n) / arithVolNorm D n ≥ selfInt - o(1)`, then our Minkowski small-section lower
bound unconditionally supplies `hMink` and yields
`liminf_{n → ∞} log (h0ArithStrict (L_n) 1) / arithVolNorm D n ≥ selfInt`! -/
theorem hermitianCurvature_moriwaki_of_lattice_family
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
    [∀ n, FiniteDimensional ℝ (E n)]
    (L : ∀ n, Submodule ℤ (E n)) [∀ n, DiscreteTopology (L n)]
    (hL0 : ∀ n, L n ≠ ⊥) (D : ℕ) {C₁ selfInt : ℝ} (hC₁ : 1 ≤ C₁)
    (hrank : ∀ n, (rk (L n) : ℝ) ≤ C₁ * (n : ℝ) ^ D)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      selfInt - ε ≤ arithDeg (L n) / RHDirect.HermitianCurvatureCore.arithVolNorm D n) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      selfInt - ε ≤
        Real.log (h0ArithStrict (L n) 1 : ℝ) / RHDirect.HermitianCurvatureCore.arithVolNorm D n := by
  refine RHDirect.HermitianCurvatureCore.moriwaki_big_of_ahs D
    (fun n => arithDeg (L n)) (fun n => Real.log (h0ArithStrict (L n) 1 : ℝ)) selfInt hAHS ?_
  intro ε hε
  -- Set `C₂ := max 1 (√C₁ * (2 / √π))` so `(1/2) log (rk L n) + log (2 / √π) ≤ log (C₂ * n^(D/2))`.
  let C₂ : ℝ := max 1 (Real.sqrt C₁ * (2 / √Real.pi))
  have hC₂ : 1 ≤ C₂ := le_max_left _ _
  have hC₁_pos : 0 < C₁ := by linarith
  have h2pi_pos : 0 < 2 / √Real.pi := div_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)
  have herr := RHDirect.HermitianCurvatureCore.sup_to_L2_volume_error_tendsto_zero D
    (fun n => rk (L n)) hC₁_pos.le hC₂ hrank
  have hmem := (Metric.tendsto_atTop.mp herr) ε hε
  filter_upwards [eventually_ge_atTop hmem.choose, eventually_ge_atTop 1] with n hn hn1
  have hvol_pos := RHDirect.HermitianCurvatureCore.arithVolNorm_pos D hn1
  have hrk_pos : (0 : ℝ) < (rk (L n) : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot (L n) (hL0 n))
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
  have hdist :
      (1 / 2) * Real.log (rk (L n) : ℝ) + Real.log (2 / √Real.pi) ≤
        Real.log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2)) := by
    have h1 : (rk (L n) : ℝ) ≤ C₁ * (n : ℝ) ^ D := hrank n
    have h2 : Real.sqrt (rk (L n) : ℝ) * (2 / √Real.pi) ≤ C₂ * (n : ℝ) ^ ((D : ℝ) / 2) := by
      have hsq : Real.sqrt (rk (L n) : ℝ) ≤ Real.sqrt C₁ * (n : ℝ) ^ ((D : ℝ) / 2) := by
        calc Real.sqrt (rk (L n) : ℝ)
            ≤ Real.sqrt (C₁ * (n : ℝ) ^ D) := Real.sqrt_le_sqrt h1
          _ = Real.sqrt C₁ * Real.sqrt ((n : ℝ) ^ D) := Real.sqrt_mul hC₁_pos.le _
          _ = Real.sqrt C₁ * (n : ℝ) ^ ((D : ℝ) / 2) := by
              congr 1
              rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
              congr 1; ring
      have hC2_ge : Real.sqrt C₁ * (2 / √Real.pi) ≤ C₂ := le_max_right _ _
      calc Real.sqrt (rk (L n) : ℝ) * (2 / √Real.pi)
          ≤ (Real.sqrt C₁ * (n : ℝ) ^ ((D : ℝ) / 2)) * (2 / √Real.pi) :=
            mul_le_mul_of_nonneg_right hsq h2pi_pos.le
        _ = (Real.sqrt C₁ * (2 / √Real.pi)) * (n : ℝ) ^ ((D : ℝ) / 2) := by ring
        _ ≤ C₂ * (n : ℝ) ^ ((D : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hC2_ge (Real.rpow_nonneg hn_pos.le _)
    have hlog := Real.log_le_log (mul_pos (Real.sqrt_pos.mpr hrk_pos) h2pi_pos) h2
    rw [Real.log_mul (Real.sqrt_pos.mpr hrk_pos).ne' h2pi_pos.ne',
      Real.log_sqrt hrk_pos.le] at hlog
    linarith
  have hm := (moriwaki_small_section_count (L n) (hL0 n)).1
  have hdeg := arithDeg_eq_rk_mul_slope (L n) (hL0 n)
  have hm' : arithDeg (L n) - (rk (L n) : ℝ) * Real.log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2)) ≤
      Real.log (h0ArithStrict (L n) 1 : ℝ) := by
    have hmul : (rk (L n) : ℝ) * ((1 / 2) * Real.log (rk (L n) : ℝ) + Real.log (2 / √Real.pi)) ≤
        (rk (L n) : ℝ) * Real.log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hdist hrk_pos.le
    linarith
  have hd := hmem.choose_spec n hn
  rw [Real.dist_eq, sub_zero] at hd
  have hle_eps : (rk (L n) : ℝ) * Real.log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2)) ≤
      ε * RHDirect.HermitianCurvatureCore.arithVolNorm D n :=
    (div_le_iff₀ hvol_pos).mp ((le_abs_self _).trans hd.le)
  linarith

end SymmetricPowerAndAHS

/-! ## Section 4: Two-Sided Minkowski Covolume Sandwich & `Stage3ThetaSiegelBridge` Integration -/

section CovolumeSandwichAndStage3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Minkowski's Second Theorem — Lower & Upper Bounds for Arbitrary Euclidean Lattices `L ⊂ E`**:
for every nonzero discrete lattice `L ⊂ E` (`r = rk L`):
1. `(2^r / r!) * covol L ≤ (∏ i, succMin L i) * ω_r` (Minkowski lower),
2. `(∏ i, succMin L i) * ω_r ≤ 2^r * covol L` (Minkowski upper). -/
theorem minkowski_second_theorem_general (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ((2 : ℝ) ^ (rk L) / ((rk L).factorial : ℝ)) * covol L ≤
      (∏ i : Fin (rk L), succMin L i) * unitBallVol (rk L) ∧
    (∏ i : Fin (rk L), succMin L i) * unitBallVol (rk L) ≤
      (2 : ℝ) ^ (rk L) * covol L := by
  obtain ⟨Λ, hDiscΛ, hIsZΛ, hcov, _, _, hsucc⟩ := exists_isometric_euclidean_lattice L
  have hr : 0 < rk L := rk_pos_of_ne_bot L hL0
  have h0B : (0 : EuclideanSpace ℝ (Fin (rk L))) ∈
      interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1) := by
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hconv := convex_closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1
  have hsymm : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1,
      -x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1 :=
    fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hcpt := isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1
  have hlo := RHDirect.Stage10GeometryOfNumbers.minkowski_second_theorem_lower hr hconv hsymm hcpt
    h0B Λ
  have hup := RHDirect.Stage10GeometryOfNumbers.minkowski_second_theorem_upper hr hconv hsymm hcpt
    h0B Λ
  have hvol : (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1)).toReal =
      unitBallVol (rk L) :=
    RHDirect.Stage10GeometryOfNumbers.unitBallVolume_eq hr
  rw [hvol, hcov] at hlo hup
  have hprod : ∏ i : Fin (rk L), succMin L i =
      ∏ i : Fin (rk L), RHDirect.Stage10GeometryOfNumbers.successiveMinimum
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1) Λ i :=
    Finset.prod_congr rfl fun i _ => hsucc i
  rw [hprod]
  exact ⟨hlo, hup⟩

/-- **Concrete Two-Sided Covolume & Slope Bound from Linearly Independent Sections
(`covolume_bound_of_section_norms`)**:
For any nonzero discrete Euclidean lattice `L ⊂ E` (`r = rk L`) and any `r` `ℝ`-linearly
independent sections `b : Fin r → E` in `L`:
1. **Two-sided covolume sandwich**:
   `(ω_r / 2^r) * (∏ i, succMin L i) ≤ covol L ≤ ∏ i, ‖b i‖`, and
   `covol L ≤ ∏ i, succMin L i` and `covol L ≤ (r! / 2^r) * ω_r * ∏ i, succMin L i`.
2. **Two-sided Arakelov slope sandwich**:
   `-(log (∏ i, ‖b i‖) / r) ≤ slope L ≤ -(log (∏ i, succMin L i) / r) + log 2 - log ω_r / r`.
3. **Sharp `λ₁`-slope ceiling**:
   `slope L ≤ -log (lambda1 L) + (1 / 2) * log r + log (2 / √π)`. -/
theorem covolume_bound_of_section_norms (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (b : Fin (rk L) → E) (hbL : ∀ i, b i ∈ L) (hbli : LinearIndependent ℝ b) :
    ((unitBallVol (rk L) / (2 : ℝ) ^ (rk L)) * (∏ i : Fin (rk L), succMin L i) ≤ covol L ∧
      covol L ≤ ∏ i : Fin (rk L), ‖b i‖ ∧
      covol L ≤ ∏ i : Fin (rk L), succMin L i ∧
      covol L ≤ (((rk L).factorial : ℝ) / (2 : ℝ) ^ (rk L)) *
        unitBallVol (rk L) * (∏ i : Fin (rk L), succMin L i)) ∧
    (-(Real.log (∏ i : Fin (rk L), ‖b i‖) / (rk L : ℝ)) ≤ slope L ∧
      slope L ≤ -(Real.log (∏ i : Fin (rk L), succMin L i) / (rk L : ℝ)) +
        Real.log 2 - Real.log (unitBallVol (rk L)) / (rk L : ℝ)) ∧
    slope L ≤ -Real.log (lambda1 L) + (1 / 2) * Real.log (rk L : ℝ) +
      Real.log (2 / √Real.pi) := by
  have hr : 1 ≤ rk L := rk_pos_of_ne_bot L hL0
  have hrpos : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr hr
  have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ (rk L) := by positivity
  have hfac_pos : (0 : ℝ) < ((rk L).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hprod_sm_pos : 0 < ∏ i : Fin (rk L), succMin L i :=
    Finset.prod_pos fun i _ => succMin_pos L hL0 i
  have hprod_b_pos : 0 < ∏ i : Fin (rk L), ‖b i‖ :=
    Finset.prod_pos fun i _ => norm_pos_iff.mpr (hbli.ne_zero i)
  obtain ⟨hmink_lo, hmink_up⟩ := minkowski_second_theorem_general L hL0
  have hhad : covol L ≤ ∏ i : Fin (rk L), ‖b i‖ := covol_le_prod_norm b hbL hbli rfl
  have hhad_sm : covol L ≤ ∏ i : Fin (rk L), succMin L i := covol_le_prod_succMin L
  have hcov_lo : (unitBallVol (rk L) / (2 : ℝ) ^ (rk L)) * (∏ i : Fin (rk L), succMin L i) ≤
      covol L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h2r_pos]
    linarith
  have hcov_up_mink : covol L ≤ (((rk L).factorial : ℝ) / (2 : ℝ) ^ (rk L)) *
      unitBallVol (rk L) * (∏ i : Fin (rk L), succMin L i) := by
    have h1 := mul_le_mul_of_nonneg_left hmink_lo (div_nonneg hfac_pos.le h2r_pos.le)
    have hsimp : (((rk L).factorial : ℝ) / (2 : ℝ) ^ (rk L)) *
        (((2 : ℝ) ^ (rk L) / ((rk L).factorial : ℝ)) * covol L) = covol L := by
      field_simp [h2r_pos.ne', hfac_pos.ne']
    rw [hsimp] at h1
    linarith
  have hsl_lo : -(Real.log (∏ i : Fin (rk L), ‖b i‖) / (rk L : ℝ)) ≤ slope L := by
    have hlog := Real.log_le_log (covol_pos L) hhad
    rw [slope_eq_arithDeg_div_rk, arithDeg, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_right hlog hrpos.le)
  have hsl_up : slope L ≤ -(Real.log (∏ i : Fin (rk L), succMin L i) / (rk L : ℝ)) +
      Real.log 2 - Real.log (unitBallVol (rk L)) / (rk L : ℝ) := by
    have hlog := Real.log_le_log
      (mul_pos (div_pos (unitBallVol_pos _) h2r_pos) hprod_sm_pos) hcov_lo
    rw [Real.log_mul (div_pos (unitBallVol_pos _) h2r_pos).ne' hprod_sm_pos.ne',
      Real.log_div (unitBallVol_pos _).ne' h2r_pos.ne', Real.log_pow] at hlog
    rw [slope_eq_arithDeg_div_rk, arithDeg]
    have hdiv := div_le_div_of_nonneg_right (neg_le_neg hlog) hrpos.le
    have hrhs : -((Real.log (unitBallVol (rk L)) - (rk L : ℝ) * Real.log 2) +
        Real.log (∏ i : Fin (rk L), succMin L i)) / (rk L : ℝ) =
        -(Real.log (∏ i : Fin (rk L), succMin L i) / (rk L : ℝ)) +
          Real.log 2 - Real.log (unitBallVol (rk L)) / (rk L : ℝ) := by
      field_simp [hrpos.ne']
      ring
    linarith
  have hsl_lam1 : slope L ≤ -Real.log (lambda1 L) + (1 / 2) * Real.log (rk L : ℝ) +
      Real.log (2 / √Real.pi) := by
    have hlam_le_prod : (lambda1 L) ^ (rk L) ≤ ∏ i : Fin (rk L), succMin L i := by
      calc (lambda1 L) ^ (rk L)
          = ∏ _i : Fin (rk L), lambda1 L := by simp
        _ ≤ ∏ i : Fin (rk L), succMin L i := by
            refine Finset.prod_le_prod (fun _ _ => (lambda1_pos L hL0).le) fun i _ => ?_
            rw [← succMin_zero_eq_lambda1 L hL0]
            exact succMin_mono L (Nat.zero_le i.1)
    have hlog_lam : (rk L : ℝ) * Real.log (lambda1 L) ≤ Real.log (∏ i : Fin (rk L), succMin L i) := by
      have h := Real.log_le_log (pow_pos (lambda1_pos L hL0) (rk L)) hlam_le_prod
      rwa [Real.log_pow] at h
    have hdiv_lam : Real.log (lambda1 L) ≤
        Real.log (∏ i : Fin (rk L), succMin L i) / (rk L : ℝ) := by
      exact (le_div_iff₀ hrpos).mpr (by linarith)
    have hlogω := div_le_div_of_nonneg_right (log_unitBallVol_ge hr) hrpos.le
    have hω_simp : (((rk L : ℝ) / 2) * Real.log Real.pi -
        ((rk L : ℝ) / 2) * Real.log (rk L : ℝ)) / (rk L : ℝ) =
        (1 / 2) * Real.log Real.pi - (1 / 2) * Real.log (rk L : ℝ) := by
      field_simp [hrpos.ne']
    rw [hω_simp] at hlogω
    have hlogC : Real.log (2 / √Real.pi) = Real.log 2 - (1 / 2) * Real.log Real.pi := by
      rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).ne',
        Real.log_sqrt Real.pi_pos.le]
      ring
    linarith
  exact ⟨⟨hcov_lo, hhad, hhad_sm, hcov_up_mink⟩, ⟨hsl_lo, hsl_up⟩, hsl_lam1⟩

/-- **Direct Bridge to `Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness`
(`stage3_fiber_covolume_and_small_sections`)**:
On every fiber `(u0, u)` of a `Stage3ThetaSiegelFiberWitness`, combines our Hadamard +
Minkowski Second Theorem covolume sandwich and Blichfeldt small-section lower bound with the
witness's Siegel-reduced basis `W.bM u0 u` to produce:
1. Two-sided covolume control for `W.latM u0 u`,
2. Exact two-sided slope control feeding `Stage2FiberWitness.slopes`,
3. Explicit strict small-section counting lower bound for `W.latM u0 u` at any radius `R > 0`. -/
theorem stage3_fiber_covolume_and_small_sections
    {S : RHDirect.SelmerSystem} {ψ : RHDirect.PChar} {eL K cHH eps x : ℝ}
    {q d_aux e_page : ℕ} {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (W : RHDirect.Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness
      S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)
    (u0 : W.U0) (u : W.W u0) {R : ℝ} (hR : 0 < R) :
    ((unitBallVol (rk (W.latM u0 u)) / (2 : ℝ) ^ (rk (W.latM u0 u))) *
        (∏ i : Fin (rk (W.latM u0 u)), succMin (W.latM u0 u) i) ≤ covol (W.latM u0 u) ∧
      covol (W.latM u0 u) ≤ ∏ j : Fin (rk (W.latM u0 u)), ‖(W.bM u0 u j : W.EM)‖) ∧
    (-(W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La * (1 + (W.R.m : ℝ) / (W.R.k : ℝ))) ≤
        slope (W.latM u0 u) ∧
      slope (W.latM u0 u) ≤ muMax (W.latM u0 u) ∧
      muMax (W.latM u0 u) ≤ W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La) ∧
    (rk (W.latM u0 u) : ℝ) *
      (-(W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La * (1 + (W.R.m : ℝ) / (W.R.k : ℝ))) +
        Real.log (R / 2) - (1 / 2) * Real.log (rk (W.latM u0 u) : ℝ) +
        (1 / 2) * Real.log Real.pi) ≤
      Real.log (h0ArithStrict (W.latM u0 u) R : ℝ) := by
  let L := W.latM u0 u
  have hL0 : L ≠ ⊥ := W.latM_ne_bot u0 u
  have hr : 1 ≤ rk L := rk_pos_of_ne_bot L hL0
  have hcb := covolume_bound_of_section_norms L hL0
    (fun j => (W.bM u0 u j : W.EM))
    (fun j => (W.bM u0 u j).2)
    (linearIndependent_coe_basis L (W.bM u0 u))
  have hsl_lo : -(W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La *
      (1 + (W.R.m : ℝ) / (W.R.k : ℝ))) ≤ slope L :=
    (neg_le_neg (W.bM_prod_norm_le u0 u)).trans hcb.2.1.1
  have hsl_le_max : slope L ≤ muMax L := slope_le_muMax L L le_rfl hL0
  have hmax_le : muMax L ≤ W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La :=
    (RHDirect.Stage3ThetaSiegelBridge.slope_and_muMax_bounds_of_siegelReduced L hL0
      (W.bM_siegel u0 u)).2.trans (W.bM_first_vec_ge u0 u)
  have hh0 := log_h0ArithStrict_lower_bound L hR
  have hdeg := arithDeg_eq_rk_mul_slope L hL0
  have hlogω := log_unitBallVol_ge hr
  have hh0_final :
      (rk L : ℝ) *
        (-(W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La * (1 + (W.R.m : ℝ) / (W.R.k : ℝ))) +
          Real.log (R / 2) - (1 / 2) * Real.log (rk L : ℝ) + (1 / 2) * Real.log Real.pi) ≤
        Real.log (h0ArithStrict L R : ℝ) := by
    have hmul : (rk L : ℝ) *
        (-(W.cSlope * (Fintype.card W.Top : ℝ) * W.a * W.La * (1 + (W.R.m : ℝ) / (W.R.k : ℝ)))) ≤
        (rk L : ℝ) * slope L :=
      mul_le_mul_of_nonneg_left hsl_lo (Nat.cast_nonneg _)
    linarith
  exact ⟨⟨hcb.1.1, hcb.1.2.1⟩, ⟨hsl_lo, hsl_le_max, hmax_le⟩, hh0_final⟩

end CovolumeSandwichAndStage3

end RHDirect.Stage11MoriwakiCovolume

end
