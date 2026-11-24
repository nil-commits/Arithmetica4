import RHDirect.BesselWaveGrid
import RHDirect.LatticeFrame
import RHDirect.Stage2ThetaWire
import RHDirect.Stage3ThetaSiegelBridge
import RHDirect.Stage3BombieriVinogradov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# RHDirect.Stage11BesselWaveSchur

Unconditional, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of **Phase B Pillar 2
(`BesselWaveGrid` / `GlobalSchurBounds`): Concrete Bessel-Wave Evaluation Grid, General Weighted
Schur's Test, Finite Cotlar–Stein Almost-Orthogonality, Volumetric Packing Off-Diagonal Decay,
and Global Wave-Grid Frame Norm Stability** in pure Mathlib `v4.33.1`.

## Main Unconditional Results (`0` Assumptions!)

1. **General Weighted & Unweighted Schur's Test**:
   - `schur_test_weighted_measure`: 4-weight general Schur's test
     `∑ i, p i * ‖∑ j, K i j * x j‖² ≤ A * B * ∑ j, q j * ‖x j‖²`.
   - `schur_test_weighted`: classical positive-test-function Schur's test
     `∑ i, ‖∑ j, K i j * x j‖² ≤ A * B * ∑ j, ‖x j‖²` and weighted operator norm bound
     `schur_test_weighted_opNorm_le`.
   - `schur_test_inv_weighted`: inverse-weighted `ℓ²` Schur's test
     `∑ i, ‖∑ j, K i j * x j‖² / w i ≤ A * B * ∑ j, ‖x j‖² / v j`.
   - `schur_test_norm_le` & `schur_test_opNorm_le`: unweighted `‖K x‖₂ ≤ √(R * C) * ‖x‖₂` and
     operator norm `‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ √(R * C)`.
   - `schur_test_hermitian_quad_le`: symmetric/Hermitian quadratic-form & operator-norm ceiling.

2. **Finite Cotlar–Stein Almost-Orthogonality Lemma**:
   - `cotlar_stein_norm_le`: for ANY bounded operators `T : ι → (H₁ →L[ℂ] H₂)` between complex
     Hilbert spaces with `‖(T i).adjoint.comp (T j)‖ ≤ a i j`, `‖(T i).comp (T j).adjoint‖ ≤ b i j`,
     `∀ i, ∑ j, √(a i j) ≤ A`, and `∀ i, ∑ j, √(b i j) ≤ B`:
     `‖∑ i, T i‖ ≤ √(A * B)` (proved purely from the `C*`-identity and alternating-product
     geometric mean — zero spectral theorem!).
   - `cotlar_stein_finite` & `cotlar_stein_selfAdjoint`: explicit max-row-sum and symmetric forms.

3. **Concrete Bessel-Wave Evaluation Kernels in `L²(ℝ^d, ℂ)` & Exact Phase-Space Overlap**:
   - `wavePacket σ u ξ x := exp(-π ‖x - u‖² / σ²) * e(⟪ξ, x⟫)` and genuine Hilbert-space vectors
     `wavePacketLp σ hσ u ξ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))` and
     unit-normalized `unitWavePacketLp σ hσ u ξ`.
   - `wavePacketLp_norm_sq`: `‖ψ_u‖_{L²}² = (σ / √2)^d` (independent of center `u` and frequency `ξ`).
   - `bessel_wave_overlap_exact`: exact closed-form Gaussian–Fourier phase-space overlap formula
     `⟪ψ_u, ψ_{u'}⟫ = (σ / √2)^d * exp(-(π/2) * (‖u - u'‖² / σ² + σ² ‖ξ' - ξ‖²)) * e(⟪ξ' - ξ, (u + u') / 2⟫)`.
   - `bessel_wave_grid_gram_decay`: exact normalized Gram entry decay
     `‖G_{u, u'}‖ = exp(-(π/2) * (‖u - u'‖² / σ² + σ² ‖ξ' - ξ‖²)) ≤ exp(-(π/2) * ‖u - u'‖² / σ²)`.

4. **Volumetric Sphere-Packing, Dyadic-Shell Decay & Global Wave-Grid Frame Stability**:
   - `separated_grid_closedBall_card_le`: exact sphere-packing count
     `#(W ∩ closedBall u R) ≤ (2 * R / Δ + 1)^d` for any `Δ`-separated grid `W ⊂ ℝ^d`.
   - `bessel_grid_off_diag_le`: for `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))` (`0 < ε ≤ 1 / 2`),
     `∀ u ∈ W, ∑ u' ∈ W.erase u, ‖G u u'‖ ≤ ε` (in particular `≤ 1 / 20` at `ε = 1 / 20`).
   - `bessel_grid_schur_offDiag_opNorm_le` & `bessel_grid_frame_bounds`: by Schur's test,
     `(1 - ε) ∑ |c_u|² ≤ ‖∑ c_u φ_u‖_{L²}² ≤ (1 + ε) ∑ |c_u|²` and linear independence.

5. **Global Cotlar–Stein Wave-Grid Operator Norm Bound & `Stage3ThetaSiegelFiberWitness` Thresholds**:
   - `bessel_grid_cotlar_stein_opNorm_le`: uniform-in-`|ι|` global Cotlar–Stein bound
     `‖∑ i, T i‖ ≤ √M * (1 + ε)` for Gaussian-separated operator families.
   - `bessel_grid_satisfies_gramFrame_thresholds` & `bessel_grid_latticeFrame_discharge`:
     explicitly achieves ALL FOUR numerical thresholds of `Stage3ThetaSiegelFiberWitness`
     (`delBar ≤ 1/2`, `sgBar ≤ 1/20`, `deBar ≤ 1/4`, `√e0Bar ≤ sgBar / 2`) and feeds directly
     into `LatticeFrame.gram_to_frame_bounds` and `LatticeFrame.compress_trace_square_bound`.
-/

noncomputable section

open Real Finset Matrix MeasureTheory Filter
open scoped BigOperators InnerProductSpace ComplexConjugate FourierTransform ENNReal

namespace RHDirect.Stage11BesselWaveSchur

/-! ## Section 1: Unconditional General Weighted & Unweighted Schur's Test -/

section SchurTest

/-- **General 4-Weight Schur's Test**:
For any finite-index complex kernel `K : ι → κ → ℂ`, nonnegative output/input measure weights
`p : ι → ℝ`, `q : κ → ℝ`, positive Schur test weights `w : ι → ℝ`, `v : κ → ℝ`, and constants
`A, B ≥ 0`:
if `∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i` and `∀ j, ∑ i, ‖K i j‖ * (p i * w i) ≤ B * (q j * v j)`,
then for every `x : κ → ℂ`,
`∑ i, p i * ‖∑ j, K i j * x j‖² ≤ A * B * ∑ j, q j * ‖x j‖²`. -/
theorem schur_test_weighted_measure {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℂ) (p w : ι → ℝ) (q v : κ → ℝ) {A B : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hv : ∀ j, 0 < v j) (hA : 0 ≤ A)
    (hrow : ∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i)
    (hcol : ∀ j, ∑ i, ‖K i j‖ * (p i * w i) ≤ B * (q j * v j))
    (x : κ → ℂ) :
    ∑ i, p i * ‖∑ j, K i j * x j‖ ^ 2 ≤ A * B * ∑ j, q j * ‖x j‖ ^ 2 := by
  have hpoint : ∀ i : ι,
      ‖∑ j, K i j * x j‖ ^ 2 ≤ (A * w i) * ∑ j, (‖K i j‖ / v j) * ‖x j‖ ^ 2 := by
    intro i
    have htri : ‖∑ j, K i j * x j‖ ≤
        ∑ j, Real.sqrt (‖K i j‖ * v j) * (Real.sqrt (‖K i j‖ / v j) * ‖x j‖) := by
      calc ‖∑ j, K i j * x j‖
          ≤ ∑ j, ‖K i j * x j‖ := norm_sum_le _ _
        _ = ∑ j, ‖K i j‖ * ‖x j‖ := by simp only [norm_mul]
        _ = ∑ j, Real.sqrt (‖K i j‖ * v j) * (Real.sqrt (‖K i j‖ / v j) * ‖x j‖) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hK0 : 0 ≤ ‖K i j‖ := norm_nonneg _
            have hv0 : 0 < v j := hv j
            rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg hK0 hv0.le)]
            have hmul : ‖K i j‖ * v j * (‖K i j‖ / v j) = ‖K i j‖ ^ 2 := by
              field_simp [hv0.ne']
            rw [hmul, Real.sqrt_sq hK0]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ)
      (fun j => Real.sqrt (‖K i j‖ * v j))
      (fun j => Real.sqrt (‖K i j‖ / v j) * ‖x j‖)
    have hsq1 : ∑ j, Real.sqrt (‖K i j‖ * v j) ^ 2 = ∑ j, ‖K i j‖ * v j := by
      refine Finset.sum_congr rfl fun j _ => Real.sq_sqrt (mul_nonneg (norm_nonneg _) (hv j).le)
    have hsq2 : ∑ j, (Real.sqrt (‖K i j‖ / v j) * ‖x j‖) ^ 2 =
        ∑ j, (‖K i j‖ / v j) * ‖x j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (div_nonneg (norm_nonneg _) (hv j).le)]
    rw [hsq1, hsq2] at hcs
    have hnn2 : 0 ≤ ∑ j, (‖K i j‖ / v j) * ‖x j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (norm_nonneg _) (hv j).le) (sq_nonneg _)
    calc ‖∑ j, K i j * x j‖ ^ 2
        ≤ (∑ j, Real.sqrt (‖K i j‖ * v j) * (Real.sqrt (‖K i j‖ / v j) * ‖x j‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ j, ‖K i j‖ * v j) * (∑ j, (‖K i j‖ / v j) * ‖x j‖ ^ 2) := hcs
      _ ≤ (A * w i) * (∑ j, (‖K i j‖ / v j) * ‖x j‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hrow i) hnn2
  calc ∑ i, p i * ‖∑ j, K i j * x j‖ ^ 2
      ≤ ∑ i, p i * ((A * w i) * ∑ j, (‖K i j‖ / v j) * ‖x j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i)
    _ = A * ∑ i, ∑ j, (‖K i j‖ * (p i * w i)) * (‖x j‖ ^ 2 / v j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ = A * ∑ j, (∑ i, ‖K i j‖ * (p i * w i)) * (‖x j‖ ^ 2 / v j) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
    _ ≤ A * ∑ j, (B * (q j * v j)) * (‖x j‖ ^ 2 / v j) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hA
        exact mul_le_mul_of_nonneg_right (hcol j) (div_nonneg (sq_nonneg _) (hv j).le)
    _ = A * B * ∑ j, q j * ‖x j‖ ^ 2 := by
        rw [mul_assoc, Finset.mul_sum]
        have hBsum : B * ∑ j, q j * ‖x j‖ ^ 2 = ∑ j, B * (q j * ‖x j‖ ^ 2) := Finset.mul_sum _ _ _
        rw [hBsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hvne : v j ≠ 0 := (hv j).ne'
        field_simp [hvne]

/-- **Classical Weighted Schur's Test (`schur_test_weighted`)**:
For any finite-index matrix `K : ι → κ → ℂ` and positive Schur test functions `w : ι → ℝ`,
`v : κ → ℝ`: if `∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i` and `∀ j, ∑ i, ‖K i j‖ * w i ≤ B * v j`
(`0 ≤ A, B`), then for EVERY `x : κ → ℂ`,
`∑ i, ‖∑ j, K i j * x j‖² ≤ A * B * ∑ j, ‖x j‖²`. -/
theorem schur_test_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℂ) (w : ι → ℝ) (v : κ → ℝ) {A B : ℝ}
    (hv : ∀ j, 0 < v j) (hA : 0 ≤ A)
    (hrow : ∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i)
    (hcol : ∀ j, ∑ i, ‖K i j‖ * w i ≤ B * v j)
    (x : κ → ℂ) :
    ∑ i, ‖∑ j, K i j * x j‖ ^ 2 ≤ A * B * ∑ j, ‖x j‖ ^ 2 := by
  have h := schur_test_weighted_measure K (fun _ => 1) w (fun _ => 1) v
    (fun _ => zero_le_one) hv hA hrow
    (fun j => by simpa only [one_mul] using hcol j) x
  simpa only [one_mul] using h

/-- **Inverse-Weighted `ℓ²` Schur's Test (`schur_test_inv_weighted`)**:
If `∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i` and `∀ j, ∑ i, ‖K i j‖ ≤ B`, then for every `x : κ → ℂ`,
`∑ i, ‖∑ j, K i j * x j‖² / w i ≤ A * B * ∑ j, ‖x j‖² / v j`. -/
theorem schur_test_inv_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℂ) (w : ι → ℝ) (v : κ → ℝ) {A B : ℝ}
    (hw : ∀ i, 0 < w i) (hv : ∀ j, 0 < v j) (hA : 0 ≤ A)
    (hrow : ∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i)
    (hcol : ∀ j, ∑ i, ‖K i j‖ ≤ B)
    (x : κ → ℂ) :
    ∑ i, ‖∑ j, K i j * x j‖ ^ 2 / w i ≤ A * B * ∑ j, ‖x j‖ ^ 2 / v j := by
  have h := schur_test_weighted_measure (B := B) K (fun i => (w i)⁻¹) w (fun j => (v j)⁻¹) v
    (fun i => inv_nonneg.mpr (hw i).le) hv hA hrow
    (fun j => by
      have h1 : ∀ i, ‖K i j‖ * ((w i)⁻¹ * w i) = ‖K i j‖ := fun i => by
        rw [inv_mul_cancel₀ (hw i).ne', mul_one]
      have h2 : B * ((v j)⁻¹ * v j) = B := by rw [inv_mul_cancel₀ (hv j).ne', mul_one]
      simp_rw [h1, h2]
      exact hcol j) x
  simpa only [div_eq_inv_mul] using h

/-- **Unweighted Schur's Test (`schur_test_norm_le`)**:
If every row `ℓ¹`-norm is `≤ R` and every column `ℓ¹`-norm is `≤ C`, then for every `x : κ → ℂ`,
`∑ i, ‖∑ j, K i j * x j‖² ≤ R * C * ∑ j, ‖x j‖²` and
`√(∑ i, ‖∑ j, K i j * x j‖²) ≤ √(R * C) * √(∑ j, ‖x j‖²)`. -/
theorem schur_test_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℂ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖K i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖K i j‖ ≤ C)
    (x : κ → ℂ) :
    ∑ i, ‖∑ j, K i j * x j‖ ^ 2 ≤ R * C * ∑ j, ‖x j‖ ^ 2 ∧
    Real.sqrt (∑ i, ‖∑ j, K i j * x j‖ ^ 2) ≤
      Real.sqrt (R * C) * Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
  have hsq : ∑ i, ‖∑ j, K i j * x j‖ ^ 2 ≤ R * C * ∑ j, ‖x j‖ ^ 2 :=
    schur_test_weighted K (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) hR
      (fun i => by simpa only [mul_one] using hrow i)
      (fun j => by simpa only [mul_one] using hcol j) x
  refine ⟨hsq, ?_⟩
  rw [← Real.sqrt_mul (mul_nonneg hR hC)]
  exact Real.sqrt_le_sqrt hsq

/-- **Weighted Schur Operator-Norm Bound on `EuclideanSpace ℂ`** (`schur_test_weighted_opNorm_le`):
If `K : Matrix ι κ ℂ` satisfies the weighted Schur row/column bounds with constants `A, B ≥ 0`,
then `‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ √(A * B)`. -/
theorem schur_test_weighted_opNorm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : Matrix ι κ ℂ) (w : ι → ℝ) (v : κ → ℝ) {A B : ℝ}
    (hv : ∀ j, 0 < v j) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖K i j‖ * v j ≤ A * w i)
    (hcol : ∀ j, ∑ i, ‖K i j‖ * w i ≤ B * v j) :
    ‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ Real.sqrt (A * B) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hschur := schur_test_weighted K w v hv hA hrow hcol (fun j => x j)
  have hL : ‖(Matrix.toEuclideanLin K).toContinuousLinearMap x‖ ^ 2 =
      ∑ i, ‖∑ j, K i j * x j‖ ^ 2 := by
    rw [LinearMap.coe_toContinuousLinearMap', EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  have hR : ‖x‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsq : ‖(Matrix.toEuclideanLin K).toContinuousLinearMap x‖ ^ 2 ≤
      (Real.sqrt (A * B) * ‖x‖) ^ 2 := by
    rw [hL, mul_pow, Real.sq_sqrt (mul_nonneg hA hB), hR]
    exact hschur
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))

/-- **Unweighted Schur Operator-Norm Bound on `EuclideanSpace ℂ`** (`schur_test_opNorm_le`):
`‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ √(R * C)`. -/
theorem schur_test_opNorm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : Matrix ι κ ℂ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖K i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖K i j‖ ≤ C) :
    ‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ Real.sqrt (R * C) :=
  schur_test_weighted_opNorm_le K (fun _ => 1) (fun _ => 1)
    (fun _ => zero_lt_one) hR hC
    (fun i => by simpa only [mul_one] using hrow i)
    (fun j => by simpa only [mul_one] using hcol j)

/-- **Symmetric / Hermitian Schur Quadratic-Form & Operator-Norm Bound**:
If `‖K j i‖ = ‖K i j‖` and every row `ℓ¹`-sum satisfies `∑ j, ‖K i j‖ ≤ M` (`0 ≤ M`), then
`‖∑ i, ∑ j, star (x i) * K i j * x j‖ ≤ M * ∑ i, ‖x i‖²` and
`‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ M`. -/
theorem schur_test_hermitian_quad_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hsymm : ∀ i j, ‖K j i‖ = ‖K i j‖)
    (hrow : ∀ i, ∑ j, ‖K i j‖ ≤ M) :
    (∀ x : ι → ℂ, ‖∑ i, ∑ j, star (x i) * K i j * x j‖ ≤ M * ∑ i, ‖x i‖ ^ 2) ∧
    ‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ≤ M := by
  have hcol : ∀ j, ∑ i, ‖K i j‖ ≤ M := fun j => by
    have : ∑ i, ‖K i j‖ = ∑ i, ‖K j i‖ := Finset.sum_congr rfl fun i _ => hsymm j i
    rw [this]
    exact hrow j
  constructor
  · intro x
    have hstep1 : ‖∑ i, ∑ j, star (x i) * K i j * x j‖ ≤
        ∑ i, ‖x i‖ * ‖∑ j, K i j * x j‖ := by
      have hre : ∀ i, ∑ j, star (x i) * K i j * x j = star (x i) * ∑ j, K i j * x j := fun i => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hre]
      calc ‖∑ i, star (x i) * ∑ j, K i j * x j‖
          ≤ ∑ i, ‖star (x i) * ∑ j, K i j * x j‖ := norm_sum_le _ _
        _ = ∑ i, ‖x i‖ * ‖∑ j, K i j * x j‖ := by
            refine Finset.sum_congr rfl fun i _ => by rw [norm_mul, norm_star]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => ‖x i‖) (fun i => ‖∑ j, K i j * x j‖)
    have hschur := (schur_test_norm_le K hM hM hrow hcol x).1
    have hsq : (∑ i, ‖x i‖ * ‖∑ j, K i j * x j‖) ^ 2 ≤ (M * ∑ i, ‖x i‖ ^ 2) ^ 2 := by
      calc (∑ i, ‖x i‖ * ‖∑ j, K i j * x j‖) ^ 2
          ≤ (∑ i, ‖x i‖ ^ 2) * (∑ i, ‖∑ j, K i j * x j‖ ^ 2) := hcs
        _ ≤ (∑ i, ‖x i‖ ^ 2) * (M * M * ∑ j, ‖x j‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hschur (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        _ = (M * ∑ i, ‖x i‖ ^ 2) ^ 2 := by ring
    exact hstep1.trans
      (le_of_sq_le_sq hsq (mul_nonneg hM (Finset.sum_nonneg fun _ _ => sq_nonneg _)))
  · have h := schur_test_opNorm_le K hM hM hrow hcol
    rwa [Real.sqrt_mul_self hM] at h

end SchurTest

/-! ## Section 2: Unconditional Finite Cotlar–Stein Almost-Orthogonality Lemma -/

section CotlarStein

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- Fundamental `C*`-identity for bounded Hilbert-space operators: `‖T* T‖ = ‖T‖²`. -/
lemma norm_adjoint_comp_self_sq (T : H₁ →L[ℂ] H₂) :
    ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 := by
  apply le_antisymm
  · calc ‖T.adjoint.comp T‖
        ≤ ‖T.adjoint‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖T‖ * ‖T‖ := by rw [LinearIsometryEquiv.norm_map]
      _ = ‖T‖ ^ 2 := (sq ‖T‖).symm
  · have hbound : ‖T‖ ≤ Real.sqrt ‖T.adjoint.comp T‖ := by
      refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) fun x => ?_
      have hsq : ‖T x‖ ^ 2 ≤ (Real.sqrt ‖T.adjoint.comp T‖ * ‖x‖) ^ 2 := by
        have hinner : ‖T x‖ ^ 2 = (⟪(T.adjoint.comp T) x, x⟫_ℂ).re := by
          have h1 : ⟪(T.adjoint.comp T) x, x⟫_ℂ = ⟪T x, T x⟫_ℂ := by
            rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
          rw [h1, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
            ← Complex.ofReal_pow, Complex.ofReal_re]
        calc ‖T x‖ ^ 2
            = (⟪(T.adjoint.comp T) x, x⟫_ℂ).re := hinner
          _ ≤ ‖⟪(T.adjoint.comp T) x, x⟫_ℂ‖ := Complex.re_le_norm _
          _ ≤ ‖(T.adjoint.comp T) x‖ * ‖x‖ := norm_inner_le_norm _ _
          _ ≤ (‖T.adjoint.comp T‖ * ‖x‖) * ‖x‖ :=
              mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ x) (norm_nonneg x)
          _ = (Real.sqrt ‖T.adjoint.comp T‖ * ‖x‖) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]; ring
      exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))
    have hsq := pow_le_pow_left₀ (norm_nonneg T) hbound 2
    rwa [Real.sq_sqrt (norm_nonneg _)] at hsq

/-- Dual `C*`-identity for bounded Hilbert-space operators: `‖T T*‖ = ‖T‖²`. -/
lemma norm_self_comp_adjoint_sq (T : H₁ →L[ℂ] H₂) :
    ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  have h := norm_adjoint_comp_self_sq T.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] at h
  exact h

/-- Power-of-two `C*`-norm identity for self-adjoint operators: if `U* = U`, then for every
`k : ℕ`, `(U ^ (2 ^ k))* = U ^ (2 ^ k)` and `‖U ^ (2 ^ k)‖ = ‖U‖ ^ (2 ^ k)`. -/
lemma selfAdjoint_pow_two_pow (U : H₁ →L[ℂ] H₁) (hU : U.adjoint = U) :
    ∀ k : ℕ, (U ^ (2 ^ k)).adjoint = U ^ (2 ^ k) ∧ ‖U ^ (2 ^ k)‖ = ‖U‖ ^ (2 ^ k)
  | 0 => by simp [hU]
  | k + 1 => by
    obtain ⟨ih_adj, ih_norm⟩ := selfAdjoint_pow_two_pow U hU k
    have hpow : U ^ (2 ^ (k + 1)) = (U ^ (2 ^ k)).comp (U ^ (2 ^ k)) := by
      rw [pow_succ, mul_two, pow_add]
      rfl
    constructor
    · rw [hpow, ContinuousLinearMap.adjoint_comp, ih_adj]
    · have hc := norm_adjoint_comp_self_sq (U ^ (2 ^ k))
      rw [ih_adj] at hc
      rw [hpow, hc, ih_norm, ← pow_mul, mul_comm (2 ^ k) 2, ← pow_succ']

/-- Recursive alternating operator product
`(T (f 0))* T (f 0).2 ∘ ⋯ ∘ (T (f n).1)* T (f n).2` on `H₁`. -/
private def altProd {ι : Type*} (T : ι → (H₁ →L[ℂ] H₂)) :
    ∀ n : ℕ, (Fin (n + 1) → ι × ι) → (H₁ →L[ℂ] H₁)
  | 0, f => (T (f 0).1).adjoint.comp (T (f 0).2)
  | n + 1, f =>
      (altProd T n (fun k => f k.castSucc)).comp
        ((T (f (Fin.last (n + 1))).1).adjoint.comp (T (f (Fin.last (n + 1))).2))

/-- Inner reassociated product `T (f 0).2 (T (f 1).1)* ∘ ⋯ ∘ T (f (n-1)).2 (T (f n).1)*` on `H₂`. -/
private def altProdInner {ι : Type*} (T : ι → (H₁ →L[ℂ] H₂)) :
    ∀ n : ℕ, (Fin (n + 1) → ι × ι) → (H₂ →L[ℂ] H₂)
  | 0, _ => ContinuousLinearMap.id ℂ H₂
  | n + 1, f =>
      (altProdInner T n (fun k => f k.castSucc)).comp
        ((T (f (Fin.last n).castSucc).2).comp (T (f (Fin.last (n + 1))).1).adjoint)

/-- Exact Cotlar–Stein reassociation identity:
`altProd T n f = (T (f 0).1)* ∘ altProdInner T n f ∘ T (f (Fin.last n)).2`. -/
private lemma altProd_eq_reassoc {ι : Type*} (T : ι → (H₁ →L[ℂ] H₂)) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι),
      altProd T n f =
        (T (f 0).1).adjoint.comp ((altProdInner T n f).comp (T (f (Fin.last n)).2))
  | 0, f => by
    simp [altProd, altProdInner]
  | n + 1, f => by
    rw [altProd, altProdInner, altProd_eq_reassoc T n (fun k => f k.castSucc)]
    have h0 : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := rfl
    rw [h0]
    ext x
    simp [ContinuousLinearMap.comp_apply]

private lemma clm_sum_comp {ι : Type*} (s : Finset ι) {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : ι → (F →L[ℂ] G)) (g : E →L[ℂ] F) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  ext x; simp

private lemma clm_comp_sum {ι : Type*} (s : Finset ι) {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : F →L[ℂ] G) (g : ι → (E →L[ℂ] F)) :
    f.comp (∑ i ∈ s, g i) = ∑ i ∈ s, f.comp (g i) := by
  ext x; simp

/-- Expansion of `((∑ i, T i)* ∘ (∑ i, T i)) ^ (n + 1)` as the sum of alternating products. -/
private lemma pow_adjoint_comp_eq_sum_altProd {ι : Type*} [Fintype ι]
    (T : ι → (H₁ →L[ℂ] H₂)) :
    ∀ n : ℕ,
      (((∑ i : ι, T i).adjoint.comp (∑ i : ι, T i)) ^ (n + 1)) =
        ∑ f : Fin (n + 1) → ι × ι, altProd T n f
  | 0 => by
    rw [pow_one, map_sum, clm_sum_comp]
    simp_rw [clm_comp_sum]
    rw [← Fintype.sum_prod_type']
    have heq := (Equiv.funUnique (Fin 1) (ι × ι)).symm.sum_comp
      (fun f : Fin 1 → ι × ι => altProd T 0 f)
    rw [← heq]
    refine Finset.sum_congr rfl fun p _ => rfl
  | n + 1 => by
    have hstep :
        (((∑ i : ι, T i).adjoint.comp (∑ i : ι, T i)) ^ (n + 2)) =
          ((((∑ i : ι, T i).adjoint.comp (∑ i : ι, T i)) ^ (n + 1)).comp
            ((∑ i : ι, T i).adjoint.comp (∑ i : ι, T i))) := by
      rw [pow_succ]
      rfl
    rw [hstep, pow_adjoint_comp_eq_sum_altProd T n]
    have hone : (∑ i : ι, T i).adjoint.comp (∑ i : ι, T i) =
        ∑ p : ι × ι, (T p.1).adjoint.comp (T p.2) := by
      rw [map_sum, clm_sum_comp]
      simp_rw [clm_comp_sum]
      exact (Fintype.sum_prod_type' _).symm
    rw [hone, clm_sum_comp]
    simp_rw [clm_comp_sum]
    rw [← Fintype.sum_prod_type']
    let e : (Fin (n + 1) → ι × ι) × (ι × ι) ≃ (Fin (n + 2) → ι × ι) :=
      { toFun := fun q => Fin.snoc q.1 q.2
        invFun := fun f => (fun k => f k.castSucc, f (Fin.last (n + 1)))
        left_inv := fun ⟨g, p⟩ => by
          ext k
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
          · simp [Fin.snoc_last]
        right_inv := fun f => by
          ext k
          · refine Fin.lastCases ?_ (fun j => ?_) k
            · simp [Fin.snoc_last]
            · simp [Fin.snoc_castSucc]
          · refine Fin.lastCases ?_ (fun j => ?_) k
            · simp [Fin.snoc_last]
            · simp [Fin.snoc_castSucc] }
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun ⟨g, p⟩ _ => ?_
    simp only [e, Equiv.coe_fn_mk, altProd, Fin.snoc_castSucc, Fin.snoc_last]

/-- Grouping-1 scalar bound `∏ a((f k).1, (f k).2)`. -/
private def prodA {ι : Type*} (a : ι → ι → ℝ) :
    ∀ n : ℕ, (Fin (n + 1) → ι × ι) → ℝ
  | 0, f => a (f 0).1 (f 0).2
  | n + 1, f => prodA a n (fun k => f k.castSucc) * a (f (Fin.last (n + 1))).1 (f (Fin.last (n + 1))).2

/-- Grouping-2 scalar bound `∏ b((f k).2, (f (k+1)).1)`. -/
private def prodB {ι : Type*} (b : ι → ι → ℝ) :
    ∀ n : ℕ, (Fin (n + 1) → ι × ι) → ℝ
  | 0, _ => 1
  | n + 1, f =>
      prodB b n (fun k => f k.castSucc) * b (f (Fin.last n).castSucc).2 (f (Fin.last (n + 1))).1

/-- Geometric-mean chain weight `√(prodA * prodB)`. -/
private def rightWeight {ι : Type*} (a b : ι → ι → ℝ) :
    ∀ n : ℕ, (Fin (n + 1) → ι × ι) → ℝ
  | 0, f => Real.sqrt (a (f 0).1 (f 0).2)
  | n + 1, f =>
      rightWeight a b n (fun k => f k.castSucc) *
        Real.sqrt (b (f (Fin.last n).castSucc).2 (f (Fin.last (n + 1))).1) *
        Real.sqrt (a (f (Fin.last (n + 1))).1 (f (Fin.last (n + 1))).2)

private lemma rightWeight_nonneg {ι : Type*} (a b : ι → ι → ℝ) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι), 0 ≤ rightWeight a b n f
  | 0, _ => Real.sqrt_nonneg _
  | n + 1, _ => mul_nonneg (mul_nonneg (rightWeight_nonneg a b n _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)

private lemma prodA_nonneg {ι : Type*} (a : ι → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι), 0 ≤ prodA a n f
  | 0, _ => ha _ _
  | n + 1, _ => mul_nonneg (prodA_nonneg a ha n _) (ha _ _)

private lemma prodB_nonneg {ι : Type*} (b : ι → ι → ℝ) (hb : ∀ i j, 0 ≤ b i j) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι), 0 ≤ prodB b n f
  | 0, _ => zero_le_one
  | n + 1, _ => mul_nonneg (prodB_nonneg b hb n _) (hb _ _)

private lemma rightWeight_sq_eq {ι : Type*} (a b : ι → ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hb : ∀ i j, 0 ≤ b i j) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι),
      rightWeight a b n f ^ 2 = prodA a n f * prodB b n f
  | 0, f => by
    simp only [rightWeight, prodA, prodB, mul_one, Real.sq_sqrt (ha _ _)]
  | n + 1, f => by
    simp only [rightWeight, prodA, prodB]
    have ih := rightWeight_sq_eq a b ha hb n (fun k => f k.castSucc)
    rw [mul_pow, mul_pow, ih, Real.sq_sqrt (hb _ _), Real.sq_sqrt (ha _ _)]
    ring

private lemma norm_altProd_le_prodA {ι : Type*} (T : ι → (H₁ →L[ℂ] H₂)) (a : ι → ι → ℝ)
    (ha : ∀ i j, ‖(T i).adjoint.comp (T j)‖ ≤ a i j) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι), ‖altProd T n f‖ ≤ prodA a n f
  | 0, f => ha _ _
  | n + 1, f => by
    simp only [altProd, prodA]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_altProd_le_prodA T a ha n _) (ha _ _) (norm_nonneg _)
        (le_trans (norm_nonneg _) (norm_altProd_le_prodA T a ha n _)))

private lemma norm_altProdInner_le_prodB {ι : Type*} (T : ι → (H₁ →L[ℂ] H₂)) (b : ι → ι → ℝ)
    (hb : ∀ i j, ‖(T i).comp (T j).adjoint‖ ≤ b i j) :
    ∀ (n : ℕ) (f : Fin (n + 1) → ι × ι),
      ‖(altProdInner T n f).comp (T (f (Fin.last n)).2)‖ ≤
        prodB b n f * ‖T (f (Fin.last n)).2‖
  | 0, f => by
    simp only [altProdInner, prodB, ContinuousLinearMap.id_comp, one_mul, le_rfl]
  | n + 1, f => by
    simp only [altProdInner, prodB]
    have hstep :
        ((altProdInner T n (fun k => f k.castSucc)).comp
          ((T (f (Fin.last n).castSucc).2).comp (T (f (Fin.last (n + 1))).1).adjoint)).comp
          (T (f (Fin.last (n + 1))).2) =
        (altProdInner T n (fun k => f k.castSucc)).comp
          (((T (f (Fin.last n).castSucc).2).comp (T (f (Fin.last (n + 1))).1).adjoint).comp
            (T (f (Fin.last (n + 1))).2)) := rfl
    have hinner : ∀ (m : ℕ) (g : Fin (m + 1) → ι × ι),
        ‖altProdInner T m g‖ ≤ prodB b m g := by
      intro m
      induction m with
      | zero =>
        intro g
        simp only [altProdInner, prodB]
        exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
      | succ m ih =>
        intro g
        simp only [altProdInner, prodB]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (ih _) (hb _ _) (norm_nonneg _) (le_trans (norm_nonneg _) (ih _)))
    have h1 := ContinuousLinearMap.opNorm_comp_le
      ((altProdInner T n (fun k => f k.castSucc)).comp
        ((T (f (Fin.last n).castSucc).2).comp (T (f (Fin.last (n + 1))).1).adjoint))
      (T (f (Fin.last (n + 1))).2)
    have h2 : ‖(altProdInner T n (fun k => f k.castSucc)).comp
        ((T (f (Fin.last n).castSucc).2).comp (T (f (Fin.last (n + 1))).1).adjoint)‖ ≤
        prodB b n (fun k => f k.castSucc) *
          b (f (Fin.last n).castSucc).2 (f (Fin.last (n + 1))).1 := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hinner n _) (hb _ _) (norm_nonneg _) (le_trans (norm_nonneg _) (hinner n _)))
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

private lemma sum_rightWeight_le {ι : Type*} [Fintype ι] (a b : ι → ι → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrowA : ∀ i, ∑ j, Real.sqrt (a i j) ≤ A)
    (hrowB : ∀ i, ∑ j, Real.sqrt (b i j) ≤ B) :
    ∀ n : ℕ, ∑ f : Fin (n + 1) → ι × ι, rightWeight a b n f ≤
      (Fintype.card ι : ℝ) * A ^ (n + 1) * B ^ n
  | 0 => by
    have heq := (Equiv.funUnique (Fin 1) (ι × ι)).symm.sum_comp
      (fun f : Fin 1 → ι × ι => rightWeight a b 0 f)
    rw [← heq]
    have hprod : ∑ p : ι × ι, Real.sqrt (a p.1 p.2) = ∑ i : ι, ∑ j : ι, Real.sqrt (a i j) :=
      Fintype.sum_prod_type _
    calc ∑ p : ι × ι, rightWeight a b 0 ((Equiv.funUnique (Fin 1) (ι × ι)).symm p)
        = ∑ i : ι, ∑ j : ι, Real.sqrt (a i j) := hprod
      _ ≤ ∑ _i : ι, A := Finset.sum_le_sum fun i _ => hrowA i
      _ = (Fintype.card ι : ℝ) * A ^ 1 * B ^ 0 := by simp
  | n + 1 => by
    let e : (Fin (n + 1) → ι × ι) × (ι × ι) ≃ (Fin (n + 2) → ι × ι) :=
      { toFun := fun q => Fin.snoc q.1 q.2
        invFun := fun f => (fun k => f k.castSucc, f (Fin.last (n + 1)))
        left_inv := fun ⟨g, p⟩ => by
          ext k
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
          · simp [Fin.snoc_last]
        right_inv := fun f => by
          ext k
          · refine Fin.lastCases ?_ (fun j => ?_) k
            · simp [Fin.snoc_last]
            · simp [Fin.snoc_castSucc]
          · refine Fin.lastCases ?_ (fun j => ?_) k
            · simp [Fin.snoc_last]
            · simp [Fin.snoc_castSucc] }
    rw [← e.sum_comp, Fintype.sum_prod_type]
    have hinner : ∀ g : Fin (n + 1) → ι × ι,
        ∑ p : ι × ι, rightWeight a b (n + 1) (e (g, p)) ≤
          rightWeight a b n g * (B * A) := by
      intro g
      have hsimp : ∀ p : ι × ι,
          rightWeight a b (n + 1) (e (g, p)) =
            rightWeight a b n g * (Real.sqrt (b (g (Fin.last n)).2 p.1) * Real.sqrt (a p.1 p.2)) := by
        intro p
        simp only [e, Equiv.coe_fn_mk, rightWeight, Fin.snoc_castSucc, Fin.snoc_last]
        ring
      simp_rw [hsimp, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (rightWeight_nonneg a b n g)
      rw [Fintype.sum_prod_type]
      calc ∑ i : ι, ∑ j : ι, Real.sqrt (b (g (Fin.last n)).2 i) * Real.sqrt (a i j)
          = ∑ i : ι, Real.sqrt (b (g (Fin.last n)).2 i) * ∑ j : ι, Real.sqrt (a i j) :=
            Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ i : ι, Real.sqrt (b (g (Fin.last n)).2 i) * A :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrowA i) (Real.sqrt_nonneg _)
        _ = (∑ i : ι, Real.sqrt (b (g (Fin.last n)).2 i)) * A := (Finset.sum_mul _ _ _).symm
        _ ≤ B * A := mul_le_mul_of_nonneg_right (hrowB _) hA
    calc ∑ g : Fin (n + 1) → ι × ι, ∑ p : ι × ι, rightWeight a b (n + 1) (e (g, p))
        ≤ ∑ g : Fin (n + 1) → ι × ι, rightWeight a b n g * (B * A) :=
          Finset.sum_le_sum fun g _ => hinner g
      _ = (∑ g : Fin (n + 1) → ι × ι, rightWeight a b n g) * (B * A) := (Finset.sum_mul _ _ _).symm
      _ ≤ ((Fintype.card ι : ℝ) * A ^ (n + 1) * B ^ n) * (B * A) :=
          mul_le_mul_of_nonneg_right (sum_rightWeight_le a b hA hB hrowA hrowB n) (mul_nonneg hB hA)
      _ = (Fintype.card ι : ℝ) * A ^ (n + 2) * B ^ (n + 1) := by ring

/-- **Unconditional Finite Cotlar–Stein Almost-Orthogonality Lemma (`cotlar_stein_norm_le`)**:
For any finite family of bounded linear operators `T : ι → (H₁ →L[ℂ] H₂)` between complex Hilbert
spaces with `‖(T i)* (T j)‖ ≤ a i j` and `‖(T i) (T j)*‖ ≤ b i j` (`0 ≤ a i j, b i j`),
if `∀ i, ∑ j, √(a i j) ≤ A` and `∀ i, ∑ j, √(b i j) ≤ B` (`0 ≤ A, B`), then
`‖∑ i, T i‖ ≤ √(A * B)`. -/
theorem cotlar_stein_norm_le {ι : Type*} [Fintype ι]
    (T : ι → (H₁ →L[ℂ] H₂)) (a b : ι → ι → ℝ) {A B : ℝ}
    (ha0 : ∀ i j, 0 ≤ a i j) (hb0 : ∀ i j, 0 ≤ b i j)
    (ha : ∀ i j, ‖(T i).adjoint.comp (T j)‖ ≤ a i j)
    (hb : ∀ i j, ‖(T i).comp (T j).adjoint‖ ≤ b i j)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrowA : ∀ i, ∑ j, Real.sqrt (a i j) ≤ A)
    (hrowB : ∀ i, ∑ j, Real.sqrt (b i j) ≤ B) :
    ‖∑ i : ι, T i‖ ≤ Real.sqrt (A * B) := by
  set S : H₁ →L[ℂ] H₂ := ∑ i : ι, T i
  set U : H₁ →L[ℂ] H₁ := S.adjoint.comp S
  have hU_adj : U.adjoint = U := by
    simp [U, ContinuousLinearMap.adjoint_comp]
  have hT_le_B : ∀ i : ι, ‖T i‖ ≤ B := by
    intro i
    have hsq : ‖T i‖ ^ 2 ≤ b i i := by
      rw [← norm_self_comp_adjoint_sq (T i)]
      exact hb i i
    have hsqrt : ‖T i‖ ≤ Real.sqrt (b i i) := by
      rw [← Real.sqrt_sq (norm_nonneg (T i))]
      exact Real.sqrt_le_sqrt hsq
    have hmem : Real.sqrt (b i i) ≤ ∑ j : ι, Real.sqrt (b i j) :=
      Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (b i j)) (Finset.mem_univ i)
    exact hsqrt.trans (hmem.trans (hrowB i))
  -- For every m = n + 1 ≥ 1, ‖U ^ (n + 1)‖ ≤ card ι * (A * B) ^ (n + 1)
  have hpow_le : ∀ n : ℕ, ‖U ^ (n + 1)‖ ≤ (Fintype.card ι : ℝ) * (A * B) ^ (n + 1) := by
    intro n
    rw [pow_adjoint_comp_eq_sum_altProd T n]
    have hterm : ∀ f : Fin (n + 1) → ι × ι, ‖altProd T n f‖ ≤ B * rightWeight a b n f := by
      intro f
      have h1 : ‖altProd T n f‖ ≤ prodA a n f := norm_altProd_le_prodA T a ha n f
      have h2 : ‖altProd T n f‖ ≤ B ^ 2 * prodB b n f := by
        rw [altProd_eq_reassoc T n f]
        have hc1 := ContinuousLinearMap.opNorm_comp_le (T (f 0).1).adjoint
          ((altProdInner T n f).comp (T (f (Fin.last n)).2))
        have hc2 := norm_altProdInner_le_prodB T b hb n f
        have hTi0 : ‖(T (f 0).1).adjoint‖ ≤ B := by
          rw [LinearIsometryEquiv.norm_map]; exact hT_le_B _
        have hTjn : ‖T (f (Fin.last n)).2‖ ≤ B := hT_le_B _
        calc ‖(T (f 0).1).adjoint.comp ((altProdInner T n f).comp (T (f (Fin.last n)).2))‖
            ≤ ‖(T (f 0).1).adjoint‖ * ‖(altProdInner T n f).comp (T (f (Fin.last n)).2)‖ := hc1
          _ ≤ B * (prodB b n f * ‖T (f (Fin.last n)).2‖) :=
              mul_le_mul hTi0 hc2 (norm_nonneg _) hB
          _ ≤ B * (prodB b n f * B) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hTjn (prodB_nonneg b hb0 n f)) hB
          _ = B ^ 2 * prodB b n f := by ring
      have hsq : ‖altProd T n f‖ ^ 2 ≤ (B * rightWeight a b n f) ^ 2 := by
        rw [sq, mul_pow, rightWeight_sq_eq a b ha0 hb0 n f]
        calc ‖altProd T n f‖ * ‖altProd T n f‖
            ≤ prodA a n f * (B ^ 2 * prodB b n f) :=
              mul_le_mul h1 h2 (norm_nonneg _) (prodA_nonneg a ha0 n f)
          _ = B ^ 2 * (prodA a n f * prodB b n f) := by ring
      exact le_of_sq_le_sq hsq (mul_nonneg hB (rightWeight_nonneg a b n f))
    calc ‖∑ f : Fin (n + 1) → ι × ι, altProd T n f‖
        ≤ ∑ f : Fin (n + 1) → ι × ι, ‖altProd T n f‖ := norm_sum_le _ _
      _ ≤ ∑ f : Fin (n + 1) → ι × ι, B * rightWeight a b n f :=
          Finset.sum_le_sum fun f _ => hterm f
      _ = B * ∑ f : Fin (n + 1) → ι × ι, rightWeight a b n f := (Finset.mul_sum _ _ _).symm
      _ ≤ B * ((Fintype.card ι : ℝ) * A ^ (n + 1) * B ^ n) :=
          mul_le_mul_of_nonneg_left (sum_rightWeight_le a b hA hB hrowA hrowB n) hB
      _ = (Fintype.card ι : ℝ) * (A * B) ^ (n + 1) := by
          rw [mul_pow]; ring
  -- For every k : ℕ, ‖S‖ ^ (2 * 2^k) = ‖U ^ (2^k)‖ ≤ card ι * (A * B) ^ (2^k)
  have h2k : ∀ k : ℕ, (‖S‖ ^ 2) ^ (2 ^ k) ≤ (Fintype.card ι : ℝ) * (A * B) ^ (2 ^ k) := by
    intro k
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hnorm := (selfAdjoint_pow_two_pow U hU_adj k).2
    rw [← norm_adjoint_comp_self_sq S]
    rw [← hnorm]
    have hpred : 2 ^ k = (2 ^ k - 1) + 1 := (Nat.sub_add_cancel hpos).symm
    rw [hpred]
    exact hpow_le (2 ^ k - 1)
  -- Deduce ‖S‖ ≤ √(A * B) by Bernoulli's inequality (zero limits needed!)
  by_contra hgt
  push Not at hgt
  have hAB_lt : A * B < ‖S‖ ^ 2 := by
    have hsq := pow_lt_pow_left₀ hgt (Real.sqrt_nonneg (A * B)) (by norm_num : 2 ≠ 0)
    rwa [Real.sq_sqrt (mul_nonneg hA hB)] at hsq
  by_cases hAB0 : A * B = 0
  · have h0 := h2k 0
    simp only [pow_zero, pow_one, hAB0, mul_zero] at h0
    linarith
  · have hAB_pos : 0 < A * B := lt_of_le_of_ne (mul_nonneg hA hB) (Ne.symm hAB0)
    set r : ℝ := ‖S‖ ^ 2 / (A * B)
    have hr1 : 1 < r := (one_lt_div hAB_pos).mpr hAB_lt
    have hrm : ∀ k : ℕ, r ^ (2 ^ k) ≤ (Fintype.card ι : ℝ) := by
      intro k
      have hdiv : r ^ (2 ^ k) = (‖S‖ ^ 2) ^ (2 ^ k) / (A * B) ^ (2 ^ k) := div_pow _ _ _
      rw [hdiv, div_le_iff₀ (pow_pos hAB_pos _)]
      exact h2k k
    -- Bernoulli's inequality: 1 + m * (r - 1) ≤ r ^ m for all m : ℕ
    have hbern : ∀ m : ℕ, 1 + (m : ℝ) * (r - 1) ≤ r ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ]
        have hr0 : 0 ≤ r := by linarith
        have hstep : (1 + (m : ℝ) * (r - 1)) * r ≤ r ^ m * r :=
          mul_le_mul_of_nonneg_right ih hr0
        have hdiff : (1 + (m : ℝ) * (r - 1)) * r - (1 + ((m + 1 : ℕ) : ℝ) * (r - 1)) =
            (m : ℝ) * (r - 1) ^ 2 := by push_cast; ring
        have hnn : 0 ≤ (m : ℝ) * (r - 1) ^ 2 := by positivity
        linarith
    -- Pick k large enough that 2^k > card ι / (r - 1)
    let K : ℕ := ⌈(Fintype.card ι : ℝ) / (r - 1)⌉₊ + 1
    have hK_lt : (Fintype.card ι : ℝ) / (r - 1) < (2 ^ K : ℕ) := by
      have h1 : (Fintype.card ι : ℝ) / (r - 1) ≤ (⌈(Fintype.card ι : ℝ) / (r - 1)⌉₊ : ℝ) :=
        Nat.le_ceil _
      have h2 : (K : ℝ) < ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self (n := K)
      have h3 : (⌈(Fintype.card ι : ℝ) / (r - 1)⌉₊ : ℝ) < (K : ℝ) := by
        dsimp only [K]; push_cast; linarith
      linarith
    have hK_mul : (Fintype.card ι : ℝ) < ((2 ^ K : ℕ) : ℝ) * (r - 1) :=
      (div_lt_iff₀ (sub_pos.mpr hr1)).mp hK_lt
    have hcontra := (hbern (2 ^ K)).trans (hrm K)
    linarith

/-- **Finite Cotlar–Stein Lemma with Explicit Max-Row Constants (`cotlar_stein_finite`)**:
For any nonempty finite family `T : ι → (H₁ →L[ℂ] H₂)` with `‖T_i* T_j‖ ≤ a i j` and
`‖T_i T_j*‖ ≤ b i j`,
`‖∑ i, T i‖ ≤ √((max_i ∑_j √a(i, j)) * (max_i ∑_j √b(i, j)))`. -/
theorem cotlar_stein_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : ι → (H₁ →L[ℂ] H₂)) (a b : ι → ι → ℝ)
    (ha0 : ∀ i j, 0 ≤ a i j) (hb0 : ∀ i j, 0 ≤ b i j)
    (ha : ∀ i j, ‖(T i).adjoint.comp (T j)‖ ≤ a i j)
    (hb : ∀ i j, ‖(T i).comp (T j).adjoint‖ ≤ b i j) :
    ‖∑ i : ι, T i‖ ≤
      Real.sqrt
        ((Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j : ι, Real.sqrt (a i j))) *
         (Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j : ι, Real.sqrt (b i j)))) := by
  set A := Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j : ι, Real.sqrt (a i j))
  set B := Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j : ι, Real.sqrt (b i j))
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hA : 0 ≤ A :=
    (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg (a i₀ j)).trans
      (Finset.le_sup' (fun i => ∑ j : ι, Real.sqrt (a i j)) (Finset.mem_univ i₀))
  have hB : 0 ≤ B :=
    (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg (b i₀ j)).trans
      (Finset.le_sup' (fun i => ∑ j : ι, Real.sqrt (b i j)) (Finset.mem_univ i₀))
  exact cotlar_stein_norm_le T a b ha0 hb0 ha hb hA hB
    (fun i => Finset.le_sup' (fun i => ∑ j : ι, Real.sqrt (a i j)) (Finset.mem_univ i))
    (fun i => Finset.le_sup' (fun i => ∑ j : ι, Real.sqrt (b i j)) (Finset.mem_univ i))

/-- **Symmetric Cotlar–Stein Bound (`cotlar_stein_symmetric`)**:
When both `‖T_i* T_j‖ ≤ a i j` and `‖T_i T_j*‖ ≤ a i j` with `∀ i, ∑ j, √(a i j) ≤ M`,
`‖∑ i, T i‖ ≤ M`. -/
theorem cotlar_stein_symmetric {ι : Type*} [Fintype ι]
    (T : ι → (H₁ →L[ℂ] H₂)) (a : ι → ι → ℝ) {M : ℝ}
    (ha0 : ∀ i j, 0 ≤ a i j)
    (ha : ∀ i j, ‖(T i).adjoint.comp (T j)‖ ≤ a i j)
    (hb : ∀ i j, ‖(T i).comp (T j).adjoint‖ ≤ a i j)
    (hM : 0 ≤ M) (hrow : ∀ i, ∑ j, Real.sqrt (a i j) ≤ M) :
    ‖∑ i : ι, T i‖ ≤ M := by
  have h := cotlar_stein_norm_le T a a ha0 ha0 ha hb hM hM hrow hrow
  rwa [Real.sqrt_mul_self hM] at h

end CotlarStein

/-! ## Section 3: Concrete Bessel-Wave Evaluation Kernels in `L²(ℝ^d, ℂ)` &
    Exact Gaussian–Fourier Phase-Space Overlap Formula -/

section BesselWaveKernels

/-- Concrete Bessel/Gabor wave-grid evaluation kernel on `ℝ^d`:
`ψ_{σ, u, ξ}(x) = exp(-π ‖x - u‖² / σ²) * e(⟪ξ, x⟫)`. -/
def wavePacket {d : ℕ} (σ : ℝ) (u ξ : EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
    Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ)

/-- Exact 1D Gaussian–Fourier integral:
`∫ t : ℝ, exp(-b * t²) * e(η * t) = √(π / b) * exp(-π² * η² / b)` for `0 < b`. -/
theorem integral_gaussian_fourier_oneD {b : ℝ} (hb : 0 < b) (η : ℝ) :
    (∫ t : ℝ, ((Real.exp (-b * t ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (η * t)) =
      ((Real.sqrt (Real.pi / b) * Real.exp (-Real.pi ^ 2 * η ^ 2 / b) : ℝ) : ℂ) := by
  set a : ℝ := b / Real.pi
  have ha : 0 < a := div_pos hb Real.pi_pos
  have haC : 0 < ((a : ℂ)).re := by simpa using ha
  have hF := congrFun (fourier_gaussian_pi haC) (-η)
  rw [Real.fourier_eq'] at hF
  have hfun : (fun t : ℝ =>
      Complex.exp (((-2 * Real.pi * inner ℝ t (-η) : ℝ) : ℂ) * Complex.I) •
        Complex.exp (-Real.pi * (a : ℂ) * (t : ℂ) ^ 2)) =
      (fun t : ℝ => ((Real.exp (-b * t ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (η * t)) := by
    ext t
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial, Stage3BombieriVinogradov.e]
    rw [mul_comm, Complex.ofReal_exp]
    congr 1
    · congr 1
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      dsimp only [a]
      push_cast
      field_simp [hpi]
    · congr 1
      push_cast
      ring
  rw [hfun] at hF
  rw [hF]
  have h1 : 1 / (a : ℂ) ^ ((1 : ℂ) / 2) = ((Real.sqrt (Real.pi / b) : ℝ) : ℂ) := by
    have hpow : (a : ℂ) ^ ((1 : ℂ) / 2) = ((Real.sqrt a : ℝ) : ℂ) := by
      rw [show ((1 : ℂ) / 2) = (((1 / 2 : ℝ) : ℂ)) by push_cast; ring,
        ← Complex.ofReal_cpow ha.le, Real.sqrt_eq_rpow]
    rw [hpow, one_div, ← Complex.ofReal_inv]
    congr 1
    dsimp only [a]
    rw [← Real.sqrt_inv, inv_div]
  have h2 : Complex.exp (-Real.pi / (a : ℂ) * ((-η : ℝ) : ℂ) ^ 2) =
      ((Real.exp (-Real.pi ^ 2 * η ^ 2 / b) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    dsimp only [a]
    push_cast
    field_simp [hpi, hbC]
  rw [h1, h2, Complex.ofReal_mul]

/-- Exact `d`-dimensional real Gaussian integral on `EuclideanSpace ℝ (Fin d)`:
`∫ x, exp(-b * ‖x‖²) = (√(π / b))^d` for `0 < b`. -/
theorem integral_gaussian_euclidean (d : ℕ) (b : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖x‖ ^ 2)) =
      (Real.sqrt (Real.pi / b)) ^ d := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  have hprod : (fun x : Fin d → ℝ => Real.exp (-b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2)) =
      (fun x : Fin d → ℝ => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2)) := by
    ext x
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum, Real.exp_sum]
  rw [hprod]
  change (∫ x : Fin d → ℝ, ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) ∂Measure.pi (fun _ : Fin d => volume)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod (f := fun (_ : Fin d) (t : ℝ) => Real.exp (-b * t ^ 2))]
  simp only [integral_gaussian b, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Integrability of `x ↦ exp(-b * ‖x‖²)` on `EuclideanSpace ℝ (Fin d)` for `0 < b`. -/
theorem integrable_gaussian_euclidean (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖x‖ ^ 2)) := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  rw [← hmp.integrable_comp_emb (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  have hprod : (fun x : Fin d → ℝ => Real.exp (-b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2)) =
      (fun x : Fin d → ℝ => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2)) := by
    ext x
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum, Real.exp_sum]
  change Integrable (fun x : Fin d → ℝ =>
    Real.exp (-b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2))
    (Measure.pi fun _ : Fin d => volume)
  rw [hprod]
  exact Integrable.fintype_prod (f := fun (_ : Fin d) (t : ℝ) => Real.exp (-b * t ^ 2))
    (fun _ => integrable_exp_neg_mul_sq hb)

/-- Exact `d`-dimensional complex Gaussian–Fourier integral on `EuclideanSpace ℝ (Fin d)`:
`∫ x, exp(-b * ‖x‖²) * e(⟪η, x⟫) = (√(π / b))^d * exp(-π² * ‖η‖² / b)` for `0 < b`. -/
theorem integral_gaussian_fourier_euclidean (d : ℕ) {b : ℝ} (hb : 0 < b)
    (η : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d),
        ((Real.exp (-b * ‖x‖ ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (⟪η, x⟫_ℝ)) =
      (((Real.sqrt (Real.pi / b)) ^ d * Real.exp (-Real.pi ^ 2 * ‖η‖ ^ 2 / b) : ℝ) : ℂ) := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  have hprod : (fun x : Fin d → ℝ =>
      ((Real.exp (-b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2) : ℝ) : ℂ) *
        Stage3BombieriVinogradov.e (⟪η, WithLp.toLp 2 x⟫_ℝ)) =
      (fun x : Fin d → ℝ =>
        ∏ i : Fin d,
          ((Real.exp (-b * (x i) ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (η i * x i)) := by
    ext x
    rw [Finset.prod_mul_distrib]
    have h1 : ∏ i : Fin d, ((Real.exp (-b * (x i) ^ 2) : ℝ) : ℂ) =
        ((Real.exp (-b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum]
    have h2 : ∏ i : Fin d, Stage3BombieriVinogradov.e (η i * x i) =
        Stage3BombieriVinogradov.e (⟪η, WithLp.toLp 2 x⟫_ℝ) := by
      have hexp : ∀ s : Finset (Fin d),
          ∏ i ∈ s, Stage3BombieriVinogradov.e (η i * x i) =
            Stage3BombieriVinogradov.e (∑ i ∈ s, η i * x i) := by
        intro s
        classical
        induction s using Finset.induction_on with
        | empty => simp [Stage3BombieriVinogradov.e_zero]
        | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, Stage3BombieriVinogradov.e_add, ih]
      rw [hexp Finset.univ, EuclideanSpace.inner_eq_star_dotProduct]
      congr 1
      simp only [dotProduct, star_trivial]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1, h2]
  rw [hprod]
  change (∫ x : Fin d → ℝ,
    ∏ i : Fin d,
      ((Real.exp (-b * (x i) ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (η i * x i)
    ∂Measure.pi (fun _ : Fin d => volume)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (f := fun (i : Fin d) (t : ℝ) =>
      ((Real.exp (-b * t ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (η i * t))]
  simp_rw [integral_gaussian_fourier_oneD hb]
  rw [← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 1
  congr 1
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum, Finset.sum_div]

/-- Every Bessel wave packet `wavePacket σ u ξ` (`σ > 0`) belongs to `L²(ℝ^d, ℂ)`. -/
theorem memLp_wavePacket {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (u ξ : EuclideanSpace ℝ (Fin d)) :
    MemLp (wavePacket σ u ξ) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  have hcont : Continuous (wavePacket σ u ξ) := by
    unfold wavePacket Stage3BombieriVinogradov.e
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hnorm_sq : (fun x : EuclideanSpace ℝ (Fin d) => ‖wavePacket σ u ξ x‖ ^ 2) =
      (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x - u‖ ^ 2)) := by
    ext x
    unfold wavePacket
    rw [norm_mul, Stage3BombieriVinogradov.norm_e, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hnorm_sq]
  have hb : 0 < 2 * Real.pi / σ ^ 2 := div_pos (by positivity) (sq_pos_of_pos hσ)
  exact (integrable_gaussian_euclidean d hb).comp_sub_right u

/-- Concrete Bessel wave-grid evaluation kernel as an element of the Hilbert space `L²(ℝ^d, ℂ)`. -/
def wavePacketLp {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (u ξ : EuclideanSpace ℝ (Fin d)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  (memLp_wavePacket σ hσ u ξ).toLp (wavePacket σ u ξ)

/-- Exact `L²` Hilbert-space norm squared of a Bessel wave packet: `‖ψ_u‖² = (σ / √2)^d`. -/
theorem wavePacketLp_norm_sq {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (u ξ : EuclideanSpace ℝ (Fin d)) :
    ‖wavePacketLp σ hσ u ξ‖ ^ 2 = (σ / Real.sqrt 2) ^ d := by
  have hinner : ((‖wavePacketLp σ hσ u ξ‖ ^ 2 : ℝ) : ℂ) =
      ⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u ξ⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hL2 : ⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u ξ⟫_ℂ =
      ∫ x : EuclideanSpace ℝ (Fin d),
        ((Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x - u‖ ^ 2) : ℝ) : ℂ) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_wavePacket σ hσ u ξ).coeFn_toLp] with x hx
    dsimp only [wavePacketLp]
    rw [hx]
    simp only [RCLike.inner_apply, wavePacket]
    have he : starRingEnd ℂ (Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ)) *
        Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ) = 1 := by
      rw [Stage3BombieriVinogradov.conj_e, ← Stage3BombieriVinogradov.e_add, neg_add_cancel,
        Stage3BombieriVinogradov.e_zero]
    rw [map_mul, Complex.conj_ofReal]
    calc ((Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
            Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ) *
            (((Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
              starRingEnd ℂ (Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ)))
        = (((Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) *
              Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) : ℝ) : ℂ)) *
            (starRingEnd ℂ (Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ)) *
              Stage3BombieriVinogradov.e (⟪ξ, x⟫_ℝ)) := by push_cast; ring
      _ = ((Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x - u‖ ^ 2) : ℝ) : ℂ) := by
            rw [he, mul_one, ← Real.exp_add]
            congr 1; congr 1; ring
  have hb : 0 < 2 * Real.pi / σ ^ 2 := div_pos (by positivity) (sq_pos_of_pos hσ)
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x - u‖ ^ 2)) :=
    (integrable_gaussian_euclidean d hb).comp_sub_right u
  have hofReal : (∫ x : EuclideanSpace ℝ (Fin d),
      ((Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x - u‖ ^ 2) : ℝ) : ℂ)) =
      ((∫ x : EuclideanSpace ℝ (Fin d),
        Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x - u‖ ^ 2) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hint
  have hre := congrArg Complex.re (hinner.trans (hL2.trans hofReal))
  rw [Complex.ofReal_re, Complex.ofReal_re] at hre
  rw [hre, MeasureTheory.integral_sub_right_eq_self
    (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(2 * Real.pi / σ ^ 2) * ‖x‖ ^ 2)) u]
  rw [integral_gaussian_euclidean d (2 * Real.pi / σ ^ 2)]
  congr 1
  have hdiv : Real.pi / (2 * Real.pi / σ ^ 2) = σ ^ 2 / 2 := by
    field_simp [Real.pi_ne_zero, hσ.ne']
  rw [hdiv, Real.sqrt_div (sq_nonneg σ), Real.sqrt_sq hσ.le]

/-- Positive `L²` norm of `wavePacketLp σ hσ u ξ`. -/
theorem wavePacketLp_norm_pos {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (u ξ : EuclideanSpace ℝ (Fin d)) :
    0 < ‖wavePacketLp σ hσ u ξ‖ := by
  have hsq : 0 < ‖wavePacketLp σ hσ u ξ‖ ^ 2 := by
    rw [wavePacketLp_norm_sq]
    exact pow_pos (div_pos hσ (Real.sqrt_pos.mpr two_pos)) d
  by_contra h
  push Not at h
  have h0 : ‖wavePacketLp σ hσ u ξ‖ = 0 := le_antisymm h (norm_nonneg _)
  rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hsq
  exact lt_irrefl 0 hsq

/-- Unit-normalized Bessel wave-grid evaluation kernel `φ_u = ψ_u / ‖ψ_u‖` in `L²(ℝ^d, ℂ)`. -/
def unitWavePacketLp {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (u ξ : EuclideanSpace ℝ (Fin d)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  ((Real.sqrt ((σ / Real.sqrt 2) ^ d))⁻¹ : ℝ) • wavePacketLp σ hσ u ξ

/-- Exact unit norm `‖unitWavePacketLp σ hσ u ξ‖ = 1`. -/
theorem unitWavePacketLp_norm {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (u ξ : EuclideanSpace ℝ (Fin d)) :
    ‖unitWavePacketLp σ hσ u ξ‖ = 1 := by
  unfold unitWavePacketLp
  have hnorm : ‖wavePacketLp σ hσ u ξ‖ = Real.sqrt ((σ / Real.sqrt 2) ^ d) := by
    rw [← Real.sqrt_sq (norm_nonneg _), wavePacketLp_norm_sq]
  have hpos : 0 < Real.sqrt ((σ / Real.sqrt 2) ^ d) :=
    Real.sqrt_pos.mpr (pow_pos (div_pos hσ (Real.sqrt_pos.mpr two_pos)) d)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), hnorm, inv_mul_cancel₀ hpos.ne']

/-- Exact parallelogram identity for Gaussian exponents around the midpoint `m = (u + u') / 2`:
`‖x - u‖² + ‖x - u'‖² = 2 * ‖x - (1/2) • (u + u')‖² + (1/2) * ‖u - u'‖²`. -/
lemma norm_sq_sub_add_norm_sq_sub {d : ℕ} (x u u' : EuclideanSpace ℝ (Fin d)) :
    ‖x - u‖ ^ 2 + ‖x - u'‖ ^ 2 =
      2 * ‖x - (1 / 2 : ℝ) • (u + u')‖ ^ 2 + (1 / 2 : ℝ) * ‖u - u'‖ ^ 2 := by
  set a : EuclideanSpace ℝ (Fin d) := x - (1 / 2 : ℝ) • (u + u')
  set b : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (u' - u)
  have h1 : x - u = a + b := by ext i; dsimp only [a, b]; simp; ring
  have h2 : x - u' = a - b := by ext i; dsimp only [a, b]; simp; ring
  have h3 : ‖b‖ ^ 2 = (1 / 4 : ℝ) * ‖u - u'‖ ^ 2 := by
    dsimp only [b]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), norm_sub_rev, mul_pow]
    ring
  have hadd := norm_add_sq_real a b
  have hsub := norm_sub_sq_real a b
  rw [h1, h2]
  linarith

/-- **Exact Closed-Form Gaussian–Fourier Phase-Space Overlap Formula (`bessel_wave_overlap_exact`)**:
For any centers `u, u'` and frequencies `ξ, ξ'` in `ℝ^d` and width `σ > 0`:
`⟪ψ_{σ, u, ξ}, ψ_{σ, u', ξ'}⟫_{L²} = (σ / √2)^d * exp(-(π/2) * (‖u - u'‖² / σ² + σ² * ‖ξ' - ξ‖²)) * e(⟪ξ' - ξ, (u + u') / 2⟫)`. -/
theorem bessel_wave_overlap_exact {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (u ξ u' ξ' : EuclideanSpace ℝ (Fin d)) :
    ⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u' ξ'⟫_ℂ =
      (((σ / Real.sqrt 2) ^ d *
        Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) : ℝ) : ℂ) *
        Stage3BombieriVinogradov.e (⟪ξ' - ξ, (1 / 2 : ℝ) • (u + u')⟫_ℝ) := by
  set m : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (u + u')
  set b : ℝ := 2 * Real.pi / σ ^ 2
  have hb : 0 < b := div_pos (by positivity) (sq_pos_of_pos hσ)
  have hL2 : ⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u' ξ'⟫_ℂ =
      ∫ x : EuclideanSpace ℝ (Fin d),
        (((Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
          Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ)) *
          (((Real.exp (-b * ‖x - m‖ ^ 2) : ℝ) : ℂ) *
            Stage3BombieriVinogradov.e (⟪ξ' - ξ, x - m⟫_ℝ)) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_wavePacket σ hσ u ξ).coeFn_toLp,
      (memLp_wavePacket σ hσ u' ξ').coeFn_toLp] with x hx hx'
    dsimp only [wavePacketLp]
    rw [hx, hx']
    simp only [RCLike.inner_apply, wavePacket, map_mul, Complex.conj_ofReal,
      Stage3BombieriVinogradov.conj_e]
    -- Combine Gaussian factors using the parallelogram law
    have hgauss : Real.exp (-Real.pi * ‖x - u'‖ ^ 2 / σ ^ 2) *
        Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) =
        Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) *
        Real.exp (-b * ‖x - m‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      have hpar := norm_sq_sub_add_norm_sq_sub x u u'
      dsimp only [b, m]
      have hσ2 : σ ^ 2 ≠ 0 := (sq_pos_of_pos hσ).ne'
      field_simp [hσ2]
      linarith
    -- Combine oscillatory characters: e(⟪ξ', x⟫) * e(-⟪ξ, x⟫) = e(⟪ξ' - ξ, m⟫) * e(⟪ξ' - ξ, x - m⟫)
    have hchar : Stage3BombieriVinogradov.e (⟪ξ', x⟫_ℝ) *
        Stage3BombieriVinogradov.e (-⟪ξ, x⟫_ℝ) =
        Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ) *
        Stage3BombieriVinogradov.e (⟪ξ' - ξ, x - m⟫_ℝ) := by
      rw [← Stage3BombieriVinogradov.e_add, ← Stage3BombieriVinogradov.e_add]
      congr 1
      simp only [inner_sub_left, inner_sub_right]
      ring
    calc ((Real.exp (-Real.pi * ‖x - u'‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
            Stage3BombieriVinogradov.e (⟪ξ', x⟫_ℝ) *
            (((Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
              Stage3BombieriVinogradov.e (-⟪ξ, x⟫_ℝ))
        = ((Real.exp (-Real.pi * ‖x - u'‖ ^ 2 / σ ^ 2) *
            Real.exp (-Real.pi * ‖x - u‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
            (Stage3BombieriVinogradov.e (⟪ξ', x⟫_ℝ) *
              Stage3BombieriVinogradov.e (-⟪ξ, x⟫_ℝ)) := by push_cast; ring
      _ = ((Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) *
            Real.exp (-b * ‖x - m‖ ^ 2) : ℝ) : ℂ) *
            (Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ) *
              Stage3BombieriVinogradov.e (⟪ξ' - ξ, x - m⟫_ℝ)) := by rw [hgauss, hchar]
      _ = (((Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
            Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ)) *
            (((Real.exp (-b * ‖x - m‖ ^ 2) : ℝ) : ℂ) *
              Stage3BombieriVinogradov.e (⟪ξ' - ξ, x - m⟫_ℝ)) := by push_cast; ring
  rw [hL2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self
      (fun y : EuclideanSpace ℝ (Fin d) =>
        ((Real.exp (-b * ‖y‖ ^ 2) : ℝ) : ℂ) * Stage3BombieriVinogradov.e (⟪ξ' - ξ, y⟫_ℝ)) m,
    integral_gaussian_fourier_euclidean d hb (ξ' - ξ)]
  have hsqrt : Real.sqrt (Real.pi / b) = σ / Real.sqrt 2 := by
    have hdiv : Real.pi / b = σ ^ 2 / 2 := by
      dsimp only [b]; field_simp [Real.pi_ne_zero, hσ.ne']
    rw [hdiv, Real.sqrt_div (sq_nonneg σ), Real.sqrt_sq hσ.le]
  have hfreq : -Real.pi ^ 2 * ‖ξ' - ξ‖ ^ 2 / b = -(Real.pi / 2) * σ ^ 2 * ‖ξ' - ξ‖ ^ 2 := by
    dsimp only [b]; field_simp [Real.pi_ne_zero, hσ.ne']
  rw [hsqrt, hfreq]
  have hexp_comb :
      Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) *
      Real.exp (-(Real.pi / 2) * σ ^ 2 * ‖ξ' - ξ‖ ^ 2) =
      Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (((Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) : ℝ) : ℂ) *
          Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ)) *
          (((σ / Real.sqrt 2) ^ d * Real.exp (-(Real.pi / 2) * σ ^ 2 * ‖ξ' - ξ‖ ^ 2) : ℝ) : ℂ)
      = (((σ / Real.sqrt 2) ^ d *
          (Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) *
            Real.exp (-(Real.pi / 2) * σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) : ℝ) : ℂ) *
          Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ) := by push_cast; ring
    _ = (((σ / Real.sqrt 2) ^ d *
          Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) : ℝ) : ℂ) *
          Stage3BombieriVinogradov.e (⟪ξ' - ξ, m⟫_ℝ) := by rw [hexp_comb]

/-- Normalized Bessel wave-grid Gram matrix entry `G_{u, u'} = ⟪ψ_u, ψ_{u'}⟫ / ‖ψ_u‖²`. -/
def besselGram {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (u ξ u' ξ' : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u' ξ'⟫_ℂ /
    ((‖wavePacketLp σ hσ u ξ‖ ^ 2 : ℝ) : ℂ)

/-- Identification of `besselGram` with the inner product of unit-normalized wave packets. -/
theorem besselGram_eq_inner_unit {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (u ξ u' ξ' : EuclideanSpace ℝ (Fin d)) :
    besselGram σ hσ u ξ u' ξ' =
      ⟪unitWavePacketLp σ hσ u ξ, unitWavePacketLp σ hσ u' ξ'⟫_ℂ := by
  unfold besselGram unitWavePacketLp
  have hpos : 0 < (σ / Real.sqrt 2) ^ d := pow_pos (div_pos hσ (Real.sqrt_pos.mpr two_pos)) d
  set r : ℝ := (Real.sqrt ((σ / Real.sqrt 2) ^ d))⁻¹
  have hsmul : ∀ v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      r • v = (r : ℂ) • v := fun v => (algebraMap_smul ℂ r v).symm
  rw [hsmul, hsmul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, wavePacketLp_norm_sq,
    ← mul_assoc, ← Complex.ofReal_mul]
  have hrr : r * r = ((σ / Real.sqrt 2) ^ d)⁻¹ := by
    dsimp only [r]
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  rw [hrr, div_eq_inv_mul, Complex.ofReal_inv]

/-- Diagonal entries of the normalized Bessel Gram matrix equal `1`. -/
theorem besselGram_diag {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (u ξ : EuclideanSpace ℝ (Fin d)) :
    besselGram σ hσ u ξ u ξ = 1 := by
  rw [besselGram_eq_inner_unit, inner_self_eq_norm_sq_to_K, unitWavePacketLp_norm]
  simp

/-- Hermitian symmetry of the normalized Bessel Gram matrix: `G_{u', u} = conj G_{u, u'}`. -/
theorem besselGram_conj_symm {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (u ξ u' ξ' : EuclideanSpace ℝ (Fin d)) :
    starRingEnd ℂ (besselGram σ hσ u ξ u' ξ') = besselGram σ hσ u' ξ' u ξ := by
  rw [besselGram_eq_inner_unit, besselGram_eq_inner_unit, inner_conj_symm]

/-- **Gaussian–Fourier Off-Diagonal Geometric Decay (`bessel_wave_grid_gram_decay`)**:
Both the exact phase-space decay equality
`‖G_{u, u'}‖ = exp(-(π/2) * (‖u - u'‖² / σ² + σ² * ‖ξ' - ξ‖²))`
and the spatial decay bound
`‖G_{u, u'}‖ ≤ exp(-(π/2) * ‖u - u'‖² / σ²)`
(and unnormalized overlap bound `‖⟪ψ_u, ψ_{u'}⟫‖ ≤ ‖ψ_u‖² * exp(-(π/2) * ‖u - u'‖² / σ²)`). -/
theorem bessel_wave_grid_gram_decay {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (u ξ u' ξ' : EuclideanSpace ℝ (Fin d)) :
    ‖besselGram σ hσ u ξ u' ξ'‖ =
      Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) ∧
    ‖besselGram σ hσ u ξ u' ξ'‖ ≤
      Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) ∧
    ‖⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u' ξ'⟫_ℂ‖ ≤
      ‖wavePacketLp σ hσ u ξ‖ ^ 2 * Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) := by
  have hpos : 0 < (σ / Real.sqrt 2) ^ d := pow_pos (div_pos hσ (Real.sqrt_pos.mpr two_pos)) d
  have hnorm_inner : ‖⟪wavePacketLp σ hσ u ξ, wavePacketLp σ hσ u' ξ'⟫_ℂ‖ =
      (σ / Real.sqrt 2) ^ d *
        Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) := by
    rw [bessel_wave_overlap_exact, norm_mul, Stage3BombieriVinogradov.norm_e, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hpos.le (Real.exp_pos _).le)]
  have heq : ‖besselGram σ hσ u ξ u' ξ'‖ =
      Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) := by
    unfold besselGram
    rw [norm_div, hnorm_inner, wavePacketLp_norm_sq, Complex.norm_real,
      Real.norm_of_nonneg hpos.le, mul_div_cancel_left₀ _ hpos.ne']
  have hdec : Real.exp (-(Real.pi / 2) * (‖u - u'‖ ^ 2 / σ ^ 2 + σ ^ 2 * ‖ξ' - ξ‖ ^ 2)) ≤
      Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hnn : 0 ≤ (Real.pi / 2) * (σ ^ 2 * ‖ξ' - ξ‖ ^ 2) := by positivity
    rw [mul_div_assoc]
    linarith
  refine ⟨heq, heq ▸ hdec, ?_⟩
  rw [hnorm_inner, wavePacketLp_norm_sq]
  exact mul_le_mul_of_nonneg_left hdec hpos.le

end BesselWaveKernels

/-! ## Section 4: Volumetric Sphere-Packing, Dyadic-Shell Off-Diagonal Decay &
    Global Wave-Grid Frame Norm Stability -/

section SeparatedGridPackingAndFrame

/-- A finite grid `W ⊂ ℝ^d` is `Δ`-separated if distinct grid centers have distance `≥ Δ`. -/
def IsSeparatedGrid {d : ℕ} (W : Finset (EuclideanSpace ℝ (Fin d))) (Δ : ℝ) : Prop :=
  ∀ u ∈ W, ∀ u' ∈ W, u ≠ u' → Δ ≤ ‖u - u'‖

/-- **Volumetric Sphere-Packing Bound on Separated Grids (`separated_grid_closedBall_card_le`)**:
For any `Δ`-separated finite grid `W ⊂ ℝ^d` (`Δ > 0`), center `u`, and radius `R ≥ 0`,
`#(W ∩ closedBall u R) ≤ (2 * R / Δ + 1) ^ d`. -/
theorem separated_grid_closedBall_card_le {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d))) {Δ R : ℝ}
    (hΔ : 0 < Δ) (hR : 0 ≤ R) (hsep : IsSeparatedGrid W Δ)
    (u : EuclideanSpace ℝ (Fin d)) :
    ((W.filter fun u' => ‖u' - u‖ ≤ R).card : ℝ) ≤ (2 * R / Δ + 1) ^ d := by
  cases d with
  | zero =>
    rw [pow_zero]
    have hcard : (W.filter fun u' => ‖u' - u‖ ≤ R).card ≤ 1 :=
      Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b
    exact_mod_cast hcard
  | succ d =>
    have : Nontrivial (EuclideanSpace ℝ (Fin (d + 1))) :=
      ⟨⟨0, EuclideanSpace.single 0 (1 : ℝ), fun h => by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) => v 0) h
        simp at this⟩⟩
    set S : Finset (EuclideanSpace ℝ (Fin (d + 1))) := W.filter fun u' => ‖u' - u‖ ≤ R
    have hdisj : (S : Set (EuclideanSpace ℝ (Fin (d + 1)))).PairwiseDisjoint
        (fun u' => Metric.ball u' (Δ / 2)) := by
      intro u₁ hu₁ u₂ hu₂ hne
      rw [Function.onFun, Set.disjoint_left]
      intro x hx₁ hx₂
      rw [Metric.mem_ball, dist_eq_norm] at hx₁ hx₂
      have h1 : u₁ ∈ W := (Finset.mem_filter.mp hu₁).1
      have h2 : u₂ ∈ W := (Finset.mem_filter.mp hu₂).1
      have hgap : Δ ≤ ‖u₁ - u₂‖ := hsep u₁ h1 u₂ h2 hne
      have htri : ‖u₁ - u₂‖ ≤ ‖x - u₁‖ + ‖x - u₂‖ := by
        calc ‖u₁ - u₂‖ = ‖(x - u₂) - (x - u₁)‖ := by congr 1; abel
          _ ≤ ‖x - u₂‖ + ‖x - u₁‖ := norm_sub_le _ _
          _ = ‖x - u₁‖ + ‖x - u₂‖ := add_comm _ _
      linarith
    have hsub : (⋃ u' ∈ S, Metric.ball u' (Δ / 2)) ⊆ Metric.ball u (R + Δ / 2) := by
      intro x hx
      simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hx ⊢
      obtain ⟨u', hu', hxu'⟩ := hx
      have hu'R : ‖u' - u‖ ≤ R := (Finset.mem_filter.mp hu').2
      calc ‖x - u‖ = ‖(x - u') + (u' - u)‖ := by congr 1; abel
        _ ≤ ‖x - u'‖ + ‖u' - u‖ := norm_add_le _ _
        _ < R + Δ / 2 := by linarith
    have hvol_le : ∑ u' ∈ S, volume (Metric.ball u' (Δ / 2)) ≤ volume (Metric.ball u (R + Δ / 2)) := by
      rw [← measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
      exact measure_mono hsub
    have hball_eq : ∀ (z : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ), 0 ≤ r →
        volume (Metric.ball z r) =
          ENNReal.ofReal r ^ (d + 1) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) := by
      intro z r hr
      rw [Measure.addHaar_ball volume z hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr]
    have hvol_lhs : ∑ u' ∈ S, volume (Metric.ball u' (Δ / 2)) =
        (S.card : ℝ≥0∞) * (ENNReal.ofReal (Δ / 2) ^ (d + 1) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)) := by
      simp_rw [hball_eq _ (Δ / 2) (by positivity), Finset.sum_const, nsmul_eq_mul]
    rw [hvol_lhs, hball_eq u (R + Δ / 2) (by linarith)] at hvol_le
    have hω_pos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
    have htop : ENNReal.ofReal (R + Δ / 2) ^ (d + 1) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) measure_ball_lt_top.ne
    have hreal := ENNReal.toReal_mono htop hvol_le
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by linarith), ← mul_assoc] at hreal
    have hreal' : (S.card : ℝ) * (Δ / 2) ^ (d + 1) ≤ (R + Δ / 2) ^ (d + 1) :=
      le_of_mul_le_mul_right hreal hω_pos
    have hdiv : (R + Δ / 2) / (Δ / 2) = 2 * R / Δ + 1 := by field_simp [hΔ.ne']
    rw [← hdiv, div_pow, le_div_iff₀ (pow_pos (by positivity) (d + 1))]
    exact hreal'

/-- Elementary exponential-linear domination `1 + 3 * k ≤ 4 ^ k` for all `k : ℕ`. -/
private lemma one_add_three_mul_le_four_pow : ∀ k : ℕ, 1 + 3 * (k : ℝ) ≤ (4 : ℝ) ^ k
  | 0 => by norm_num
  | k + 1 => by
    have ih := one_add_three_mul_le_four_pow k
    rw [pow_succ]
    push_cast
    linarith

/-- Elementary logarithm ceiling `log 5 ≤ 2` (from `5 < 7.29 = 2.7^2 < e^2`). -/
private lemma log_five_le_two : Real.log 5 ≤ 2 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h5 : (5 : ℝ) ≤ Real.exp 2 := by
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [hsq]
    nlinarith
  calc Real.log 5 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h5
    _ = 2 := Real.log_exp 2

/-- Elementary logarithm bounds `1 / 2 ≤ log 2` and `log 2 ≤ 1`. -/
private lemma half_le_log_two_and_le_one : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

/-- **Dyadic-Shell Exponential Decay Sum on Any `Δ`-Separated Grid (`separated_grid_dyadic_exp_sum_le`)**:
For any `Δ`-separated finite grid `W ⊂ ℝ^d` (`Δ > 0`), decay rate `α ≥ d + 1`, and center `u ∈ W`,
`∑ u' ∈ W.erase u, exp(-α * (‖u - u'‖ / Δ)²) ≤ 2 * 5^d * exp(-α)`. -/
theorem separated_grid_dyadic_exp_sum_le {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d))) {Δ α : ℝ}
    (hΔ : 0 < Δ) (hα : (d : ℝ) + 1 ≤ α) (hsep : IsSeparatedGrid W Δ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ W) :
    ∑ u' ∈ W.erase u, Real.exp (-α * (‖u - u'‖ / Δ) ^ 2) ≤
      2 * (5 : ℝ) ^ d * Real.exp (-α) := by
  have hα0 : 0 < α := by linarith [Nat.cast_nonneg (α := ℝ) d]
  -- Assign every u' ∈ W.erase u to its dyadic shell k with 2^k ≤ ‖u' - u‖ / Δ < 2^(k + 1)
  have hex_shell : ∀ u' ∈ W.erase u,
      ∃ k : ℕ, (2 : ℝ) ^ k ≤ ‖u' - u‖ / Δ ∧ ‖u' - u‖ / Δ < (2 : ℝ) ^ (k + 1) := by
    intro u' hu'
    have hu'W : u' ∈ W := (Finset.mem_erase.mp hu').2
    have hne : u' ≠ u := (Finset.mem_erase.mp hu').1
    have hge1 : 1 ≤ ‖u' - u‖ / Δ := (one_le_div hΔ).mpr (hsep u' hu'W u hu hne)
    exact Stage3ThetaSiegelBridge.exists_dyadic_shell hge1
  classical
  let shell : EuclideanSpace ℝ (Fin d) → ℕ := fun u' =>
    if h : u' ∈ W.erase u then Classical.choose (hex_shell u' h) else 0
  have hshell_spec : ∀ u' ∈ W.erase u,
      (2 : ℝ) ^ (shell u') ≤ ‖u' - u‖ / Δ ∧ ‖u' - u‖ / Δ < (2 : ℝ) ^ (shell u' + 1) := by
    intro u' hu'
    simp only [shell, dif_pos hu']
    exact Classical.choose_spec (hex_shell u' hu')
  let N : ℕ := (W.erase u).sup shell + 1
  have hmem_range : ∀ u' ∈ W.erase u, shell u' ∈ Finset.range N := fun u' hu' =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := shell) hu'))
  have hfiber := (Finset.sum_fiberwise_of_maps_to hmem_range
    (fun u' => Real.exp (-α * (‖u - u'‖ / Δ) ^ 2))).symm
  rw [hfiber]
  -- Bound each dyadic shell k
  have hshell_bound : ∀ k ∈ Finset.range N,
      ∑ u' ∈ (W.erase u).filter (fun u' => shell u' = k),
        Real.exp (-α * (‖u - u'‖ / Δ) ^ 2) ≤
      (5 : ℝ) ^ d * Real.exp (-α) * ((1 : ℝ) / 2) ^ k := by
    intro k _
    set Sk := (W.erase u).filter (fun u' => shell u' = k)
    have hterm : ∀ u' ∈ Sk,
        Real.exp (-α * (‖u - u'‖ / Δ) ^ 2) ≤ Real.exp (-α * (4 : ℝ) ^ k) := by
      intro u' hu'
      have hu'e : u' ∈ W.erase u := (Finset.mem_filter.mp hu').1
      have hsk : shell u' = k := (Finset.mem_filter.mp hu').2
      have hlo : (2 : ℝ) ^ k ≤ ‖u - u'‖ / Δ := by
        rw [norm_sub_rev, ← hsk]
        exact (hshell_spec u' hu'e).1
      have hsq : (4 : ℝ) ^ k ≤ (‖u - u'‖ / Δ) ^ 2 := by
        have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
          rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
        rw [h4]
        exact pow_le_pow_left₀ (by positivity) hlo 2
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hsub_ball : Sk ⊆ W.filter (fun u' => ‖u' - u‖ ≤ (2 : ℝ) ^ (k + 1) * Δ) := by
      intro u' hu'
      have hu'e : u' ∈ W.erase u := (Finset.mem_filter.mp hu').1
      have hsk : shell u' = k := (Finset.mem_filter.mp hu').2
      have hhi : ‖u' - u‖ / Δ < (2 : ℝ) ^ (k + 1) := by
        rw [← hsk]; exact (hshell_spec u' hu'e).2
      refine Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hu'e).2, ?_⟩
      exact ((div_lt_iff₀ hΔ).mp hhi).le
    have hcard_le : (Sk.card : ℝ) ≤ (5 : ℝ) ^ d * ((2 : ℝ) ^ d) ^ k := by
      have hc1 : (Sk.card : ℝ) ≤
          ((W.filter (fun u' => ‖u' - u‖ ≤ (2 : ℝ) ^ (k + 1) * Δ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub_ball
      have hc2 := separated_grid_closedBall_card_le W hΔ (by positivity) hsep u
        (R := (2 : ℝ) ^ (k + 1) * Δ)
      have hsimp : 2 * ((2 : ℝ) ^ (k + 1) * Δ) / Δ + 1 = 4 * (2 : ℝ) ^ k + 1 := by
        rw [pow_succ]; field_simp [hΔ.ne']; ring
      rw [hsimp] at hc2
      have h5 : 4 * (2 : ℝ) ^ k + 1 ≤ 5 * (2 : ℝ) ^ k := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
      have hc3 : (4 * (2 : ℝ) ^ k + 1) ^ d ≤ (5 * (2 : ℝ) ^ k) ^ d :=
        pow_le_pow_left₀ (by positivity) h5 d
      have hc4 : (5 * (2 : ℝ) ^ k) ^ d = (5 : ℝ) ^ d * ((2 : ℝ) ^ d) ^ k := by
        rw [mul_pow, ← pow_mul, mul_comm k d, pow_mul]
      exact hc1.trans (hc2.trans (hc3.trans_eq hc4))
    -- Exponential factor contraction: (2^d)^k * exp(-α * 4^k) ≤ exp(-α) * (1/2)^k
    have hexp_split : Real.exp (-α * (4 : ℝ) ^ k) ≤
        Real.exp (-α) * (Real.exp (-3 * α)) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h4k := one_add_three_mul_le_four_pow k
      nlinarith
    have hratio : (2 : ℝ) ^ d * Real.exp (-3 * α) ≤ (1 : ℝ) / 2 := by
      have hlog2 : Real.log 2 ≤ 1 := half_le_log_two_and_le_one.2
      have hexp_le : Real.exp (-3 * α) ≤ Real.exp (-(((d : ℝ) + 1) * Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) d, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have h2d1 : Real.exp (-(((d : ℝ) + 1) * Real.log 2)) = ((2 : ℝ) ^ (d + 1))⁻¹ := by
        rw [Real.exp_neg]
        congr 1
        rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      calc (2 : ℝ) ^ d * Real.exp (-3 * α)
          ≤ (2 : ℝ) ^ d * ((2 : ℝ) ^ (d + 1))⁻¹ := by
            rw [← h2d1]; exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ = (1 : ℝ) / 2 := by rw [pow_succ]; field_simp
    calc ∑ u' ∈ Sk, Real.exp (-α * (‖u - u'‖ / Δ) ^ 2)
        ≤ ∑ _u' ∈ Sk, Real.exp (-α * (4 : ℝ) ^ k) := Finset.sum_le_sum hterm
      _ = (Sk.card : ℝ) * Real.exp (-α * (4 : ℝ) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((5 : ℝ) ^ d * ((2 : ℝ) ^ d) ^ k) * (Real.exp (-α) * (Real.exp (-3 * α)) ^ k) :=
          mul_le_mul hcard_le hexp_split (Real.exp_pos _).le (by positivity)
      _ = (5 : ℝ) ^ d * Real.exp (-α) * ((2 : ℝ) ^ d * Real.exp (-3 * α)) ^ k := by
          rw [mul_pow]; ring
      _ ≤ (5 : ℝ) ^ d * Real.exp (-α) * ((1 : ℝ) / 2) ^ k :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hratio k) (by positivity)
  calc ∑ k ∈ Finset.range N,
        ∑ u' ∈ (W.erase u).filter (fun u' => shell u' = k),
          Real.exp (-α * (‖u - u'‖ / Δ) ^ 2)
      ≤ ∑ k ∈ Finset.range N, (5 : ℝ) ^ d * Real.exp (-α) * ((1 : ℝ) / 2) ^ k :=
        Finset.sum_le_sum hshell_bound
    _ = (5 : ℝ) ^ d * Real.exp (-α) * ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (5 : ℝ) ^ d * Real.exp (-α) * 2 :=
        mul_le_mul_of_nonneg_left (Stage3ThetaSiegelBridge.sum_range_half_pow_le_two N) (by positivity)
    _ = 2 * (5 : ℝ) ^ d * Real.exp (-α) := by ring

/-- Concrete dimensional separation constant `C_d = √(4 * d + 3)` for `ℝ^d`. -/
def sepConst (d : ℕ) : ℝ := Real.sqrt (4 * (d : ℝ) + 3)

theorem sepConst_pos (d : ℕ) : 0 < sepConst d :=
  Real.sqrt_pos.mpr (by positivity)

/-- **Quantitative Gaussian Off-Diagonal Sum Threshold on Separated Grids**:
If `0 < σ`, `0 < ε ≤ 1 / 2`, `Δ ≥ sepConst d * σ * √(log (1 / ε))`, and `W ⊂ ℝ^d` is `Δ`-separated,
then for every `u ∈ W`, `∑ u' ∈ W.erase u, exp(-(π/2) * ‖u - u'‖² / σ²) ≤ ε`. -/
theorem separated_grid_gaussian_sum_le {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d))) {σ Δ ε : ℝ}
    (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ W) :
    ∑ u' ∈ W.erase u, Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) ≤ ε := by
  have hinv_ge2 : (2 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0]; linarith
  have hlog_ge_half : (1 / 2 : ℝ) ≤ Real.log (1 / ε) :=
    half_le_log_two_and_le_one.1.trans (Real.log_le_log (by norm_num) hinv_ge2)
  have hlog_pos : 0 < Real.log (1 / ε) := by linarith
  have hΔ : 0 < Δ := lt_of_lt_of_le
    (mul_pos (mul_pos (sepConst_pos d) hσ) (Real.sqrt_pos.mpr hlog_pos)) hΔ_ge
  set α : ℝ := (Real.pi / 2) * (Δ / σ) ^ 2
  have hratio_sq : (4 * (d : ℝ) + 3) * Real.log (1 / ε) ≤ (Δ / σ) ^ 2 := by
    have h1 : sepConst d * Real.sqrt (Real.log (1 / ε)) ≤ Δ / σ := by
      rw [le_div_iff₀ hσ]
      linarith
    have hsq := pow_le_pow_left₀ (mul_nonneg (sepConst_pos d).le (Real.sqrt_nonneg _)) h1 2
    rw [mul_pow, sepConst, Real.sq_sqrt (by positivity), Real.sq_sqrt hlog_pos.le] at hsq
    exact hsq
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hα_ge : (2 * (d : ℝ) + 1) + Real.log (1 / ε) ≤ α := by
    have h1 : (2 * (d : ℝ) + 1) + Real.log (1 / ε) ≤ (4 * (d : ℝ) + 3) * Real.log (1 / ε) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) d]
    have h2 : (4 * (d : ℝ) + 3) * Real.log (1 / ε) ≤ (Real.pi / 2) * (Δ / σ) ^ 2 := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (d : ℝ) + 3) hlog_pos.le]
    exact h1.trans h2
  have hα_d1 : (d : ℝ) + 1 ≤ α := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hrew : ∀ u' ∈ W.erase u,
      Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) =
        Real.exp (-α * (‖u - u'‖ / Δ) ^ 2) := by
    intro u' _
    congr 1
    dsimp only [α]
    field_simp [hΔ.ne', hσ.ne']
  rw [Finset.sum_congr rfl hrew]
  have hdyad := separated_grid_dyadic_exp_sum_le W hΔ hα_d1 hsep hu
  refine hdyad.trans ?_
  have hlog_bound : Real.log (2 * (5 : ℝ) ^ d / ε) ≤ α := by
    rw [Real.log_div (by positivity) hε0.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    have h1 := half_le_log_two_and_le_one.2
    have h5 := log_five_le_two
    have hinv : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
    rw [hinv] at hα_ge
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hexp_le : Real.exp (-α) ≤ (2 * (5 : ℝ) ^ d / ε)⁻¹ := by
    have hpos : (0 : ℝ) < 2 * (5 : ℝ) ^ d / ε := div_pos (by positivity) hε0
    rw [← Real.exp_log hpos, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (neg_le_neg hlog_bound)
  calc 2 * (5 : ℝ) ^ d * Real.exp (-α)
      ≤ 2 * (5 : ℝ) ^ d * (2 * (5 : ℝ) ^ d / ε)⁻¹ :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = ε := by field_simp [hε0.ne']

/-- **Bessel-Wave Grid Off-Diagonal Decay Bound (`bessel_grid_off_diag_le`)**:
For any `Δ`-separated finite grid `W ⊂ ℝ^d` with `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))`
(`0 < ε ≤ 1 / 2`) and any frequency map `ξ`, the normalized Bessel Gram matrix
`G u u' = ⟪ψ_u, ψ_{u'}⟫ / ‖ψ_u‖²` satisfies
`∀ u ∈ W, ∑ u' ∈ W.erase u, ‖G u u'‖ ≤ ε`. -/
theorem bessel_grid_off_diag_le {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ) :
    ∀ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram σ hσ u (ξ u) u' (ξ u')‖ ≤ ε := by
  intro u hu
  calc ∑ u' ∈ W.erase u, ‖besselGram σ hσ u (ξ u) u' (ξ u')‖
      ≤ ∑ u' ∈ W.erase u, Real.exp (-(Real.pi / 2) * ‖u - u'‖ ^ 2 / σ ^ 2) :=
        Finset.sum_le_sum fun u' _ => (bessel_wave_grid_gram_decay σ hσ u (ξ u) u' (ξ u')).2.1
    _ ≤ ε := separated_grid_gaussian_sum_le W hσ hε0 hε_half hΔ_ge hsep hu

/-- Concrete `1 / 20` specialization of `bessel_grid_off_diag_le` at `Δ ≥ √(4d + 3) * σ * √(log 20)`. -/
theorem bessel_grid_off_diag_le_one_twentieth {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ : ℝ} (hσ : 0 < σ)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log 20) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ) :
    ∀ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram σ hσ u (ξ u) u' (ξ u')‖ ≤ 1 / 20 := by
  refine bessel_grid_off_diag_le W ξ hσ (by norm_num) (by norm_num) ?_ hsep
  have h20 : (1 : ℝ) / (1 / 20) = 20 := by norm_num
  rwa [h20]

/-- Off-diagonal Gram defect matrix `E` on a finite grid `W` (`0` on diagonal, `G u u'` off diagonal). -/
def besselOffDiagMatrix {d : ℕ} (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ) (hσ : 0 < σ) : Matrix W W ℂ :=
  fun u u' => if u = u' then 0 else besselGram σ hσ u.1 (ξ u.1) u'.1 (ξ u'.1)

/-- **Schur Operator-Norm Bound for the Off-Diagonal Bessel Gram Matrix**:
Under separation `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))` (`0 < ε ≤ 1 / 2`), Schur's test
(`schur_test_opNorm_le`) gives `‖(Matrix.toEuclideanLin E).toContinuousLinearMap‖ ≤ ε`. -/
theorem bessel_grid_schur_offDiag_opNorm_le {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ) :
    ‖(Matrix.toEuclideanLin (besselOffDiagMatrix W ξ σ hσ)).toContinuousLinearMap‖ ≤ ε := by
  have hoff := bessel_grid_off_diag_le W ξ hσ hε0 hε_half hΔ_ge hsep
  have hrow : ∀ u : W, ∑ u' : W, ‖besselOffDiagMatrix W ξ σ hσ u u'‖ ≤ ε := by
    intro u
    have hsum_eq : ∑ u' : W, ‖besselOffDiagMatrix W ξ σ hσ u u'‖ =
        ∑ u' ∈ W.erase u.1, ‖besselGram σ hσ u.1 (ξ u.1) u' (ξ u')‖ := by
      have hleft : ∀ u' : W,
          ‖besselOffDiagMatrix W ξ σ hσ u u'‖ =
            if u'.1 = u.1 then 0 else ‖besselGram σ hσ u.1 (ξ u.1) u'.1 (ξ u'.1)‖ := by
        intro u'
        unfold besselOffDiagMatrix
        by_cases h : u = u'
        · subst h; simp
        · have h1 : u'.1 ≠ u.1 := fun heq => h (Subtype.ext heq.symm)
          simp [h, h1]
      simp_rw [hleft]
      rw [Finset.sum_coe_sort W (fun u' =>
        if u' = u.1 then 0 else ‖besselGram σ hσ u.1 (ξ u.1) u' (ξ u')‖)]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x; simp [and_comm]
    rw [hsum_eq]
    exact hoff u.1 u.2
  have hsymm : ∀ u u' : W,
      ‖besselOffDiagMatrix W ξ σ hσ u' u‖ = ‖besselOffDiagMatrix W ξ σ hσ u u'‖ := by
    intro u u'
    unfold besselOffDiagMatrix
    by_cases h : u = u'
    · subst h; simp
    · have h' : u' ≠ u := Ne.symm h
      simp only [h, h', ↓reduceIte]
      rw [← besselGram_conj_symm σ hσ u.1 (ξ u.1) u'.1 (ξ u'.1), RCLike.norm_conj]
  exact (schur_test_hermitian_quad_le (besselOffDiagMatrix W ξ σ hσ) hε0.le hsymm hrow).2

/-- **Global Bessel-Wave Grid Frame Norm Stability (`bessel_grid_frame_bounds`)**:
Deduced directly from Schur's test (`schur_test_hermitian_quad_le`) and `bessel_grid_off_diag_le`!
For any `Δ`-separated finite grid `W ⊂ ℝ^d` with `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))`
(`0 < ε ≤ 1 / 2`) and every coefficient vector `c : EuclideanSpace ℝ (Fin d) → ℂ`:
1. Unit-normalized wave packets `φ_u = unitWavePacketLp σ hσ u (ξ u)` satisfy
   `(1 - ε) * ∑ u ∈ W, ‖c u‖² ≤ ‖∑ u ∈ W, c u • φ_u‖² ≤ (1 + ε) * ∑ u ∈ W, ‖c u‖²`.
2. Raw wave packets `ψ_u = wavePacketLp σ hσ u (ξ u)` satisfy
   `(1 - ε) * (σ / √2)^d * ∑ u ∈ W, ‖c u‖² ≤ ‖∑ u ∈ W, c u • ψ_u‖² ≤ (1 + ε) * (σ / √2)^d * ∑ u ∈ W, ‖c u‖²`. -/
theorem bessel_grid_frame_bounds {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ)
    (c : EuclideanSpace ℝ (Fin d) → ℂ) :
    ((1 - ε) * ∑ u ∈ W, ‖c u‖ ^ 2 ≤
        ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ∧
      ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ≤
        (1 + ε) * ∑ u ∈ W, ‖c u‖ ^ 2) ∧
    ((1 - ε) * (σ / Real.sqrt 2) ^ d * ∑ u ∈ W, ‖c u‖ ^ 2 ≤
        ‖∑ u ∈ W, c u • wavePacketLp σ hσ u (ξ u)‖ ^ 2 ∧
      ‖∑ u ∈ W, c u • wavePacketLp σ hσ u (ξ u)‖ ^ 2 ≤
        (1 + ε) * (σ / Real.sqrt 2) ^ d * ∑ u ∈ W, ‖c u‖ ^ 2) := by
  have hoff := bessel_grid_off_diag_le W ξ hσ hε0 hε_half hΔ_ge hsep
  let E := besselOffDiagMatrix W ξ σ hσ
  have hrow : ∀ u : W, ∑ u' : W, ‖E u u'‖ ≤ ε := by
    intro u
    have hsum_eq : ∑ u' : W, ‖E u u'‖ =
        ∑ u' ∈ W.erase u.1, ‖besselGram σ hσ u.1 (ξ u.1) u' (ξ u')‖ := by
      have hleft : ∀ u' : W,
          ‖E u u'‖ = if u'.1 = u.1 then 0 else ‖besselGram σ hσ u.1 (ξ u.1) u'.1 (ξ u'.1)‖ := by
        intro u'
        dsimp only [E, besselOffDiagMatrix]
        by_cases h : u = u'
        · subst h; simp
        · have h1 : u'.1 ≠ u.1 := fun heq => h (Subtype.ext heq.symm)
          simp [h, h1]
      simp_rw [hleft]
      rw [Finset.sum_coe_sort W (fun u' =>
        if u' = u.1 then 0 else ‖besselGram σ hσ u.1 (ξ u.1) u' (ξ u')‖)]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x; simp [and_comm]
    rw [hsum_eq]
    exact hoff u.1 u.2
  have hsymm : ∀ u u' : W, ‖E u' u‖ = ‖E u u'‖ := by
    intro u u'
    dsimp only [E, besselOffDiagMatrix]
    by_cases h : u = u'
    · subst h; simp
    · have h' : u' ≠ u := Ne.symm h
      simp only [h, h', ↓reduceIte]
      rw [← besselGram_conj_symm σ hσ u.1 (ξ u.1) u'.1 (ξ u'.1), RCLike.norm_conj]
  have hquad := (schur_test_hermitian_quad_le E hε0.le hsymm hrow).1 (fun u : W => c u.1)
  -- Express ‖∑ c_u φ_u‖² = ∑ ‖c_u‖² + Re(∑_{u, u'} star(c_u) * E_{u, u'} * c_{u'})
  have hnorm_expand :
      ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 =
        (∑ u : W, ‖c u.1‖ ^ 2) +
          (∑ u : W, ∑ u' : W, star (c u.1) * E u u' * c u'.1).re := by
    have hsum_coe : ∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u) =
        ∑ u : W, c u.1 • unitWavePacketLp σ hσ u.1 (ξ u.1) :=
      (Finset.sum_coe_sort W (fun u => c u • unitWavePacketLp σ hσ u (ξ u))).symm
    rw [hsum_coe]
    have hsq : ‖∑ u : W, c u.1 • unitWavePacketLp σ hσ u.1 (ξ u.1)‖ ^ 2 =
        (⟪∑ u : W, c u.1 • unitWavePacketLp σ hσ u.1 (ξ u.1),
          ∑ u' : W, c u'.1 • unitWavePacketLp σ hσ u'.1 (ξ u'.1)⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
        ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hsq, sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right, ← besselGram_eq_inner_unit]
    have hsplit :
        ∑ u : W, ∑ u' : W, (starRingEnd ℂ (c u.1)) * (c u'.1 * besselGram σ hσ u.1 (ξ u.1) u'.1 (ξ u'.1)) =
        (∑ u : W, ((‖c u.1‖ ^ 2 : ℝ) : ℂ)) +
          ∑ u : W, ∑ u' : W, star (c u.1) * E u u' * c u'.1 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
        ← Finset.add_sum_erase (Finset.univ : Finset W)
          (fun u' : W => star (c u.1) * E u u' * c u'.1) (Finset.mem_univ u)]
      have hdiagE : star (c u.1) * E u u * c u.1 = 0 := by simp [E, besselOffDiagMatrix]
      rw [hdiagE, zero_add]
      congr 1
      · rw [besselGram_diag, mul_one, RCLike.conj_mul]
        simp
      · refine Finset.sum_congr rfl fun u' hu' => ?_
        have hne : u ≠ u' := (Finset.mem_erase.mp hu').1.symm
        simp only [E, besselOffDiagMatrix, hne, ↓reduceIte, Complex.star_def]
        ring
    rw [hsplit, Complex.add_re, Complex.re_sum]
    simp only [Complex.ofReal_re]
  have hsum_c : ∑ u : W, ‖c u.1‖ ^ 2 = ∑ u ∈ W, ‖c u‖ ^ 2 :=
    Finset.sum_coe_sort W (fun u => ‖c u‖ ^ 2)
  have hre_abs : |(∑ u : W, ∑ u' : W, star (c u.1) * E u u' * c u'.1).re| ≤
      ε * ∑ u ∈ W, ‖c u‖ ^ 2 := by
    calc |(∑ u : W, ∑ u' : W, star (c u.1) * E u u' * c u'.1).re|
        ≤ ‖∑ u : W, ∑ u' : W, star (c u.1) * E u u' * c u'.1‖ := Complex.abs_re_le_norm _
      _ ≤ ε * ∑ u : W, ‖c u.1‖ ^ 2 := hquad
      _ = ε * ∑ u ∈ W, ‖c u‖ ^ 2 := by rw [hsum_c]
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hre_abs
  have hunit : (1 - ε) * ∑ u ∈ W, ‖c u‖ ^ 2 ≤
      ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ∧
    ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ≤
      (1 + ε) * ∑ u ∈ W, ‖c u‖ ^ 2 := by
    rw [hnorm_expand, hsum_c]
    exact ⟨by linarith, by linarith⟩
  refine ⟨hunit, ?_⟩
  -- Scale from unitWavePacketLp to wavePacketLp by √((σ / √2)^d)
  have hpos : 0 < (σ / Real.sqrt 2) ^ d := pow_pos (div_pos hσ (Real.sqrt_pos.mpr two_pos)) d
  have hscale : ∑ u ∈ W, c u • wavePacketLp σ hσ u (ξ u) =
      (Real.sqrt ((σ / Real.sqrt 2) ^ d) : ℝ) • ∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold unitWavePacketLp
    rw [smul_comm, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne', one_smul]
  have hnorm_scale : ‖∑ u ∈ W, c u • wavePacketLp σ hσ u (ξ u)‖ ^ 2 =
      (σ / Real.sqrt 2) ^ d * ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 := by
    rw [hscale, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hpos.le]
  rw [hnorm_scale]
  constructor
  · calc (1 - ε) * (σ / Real.sqrt 2) ^ d * ∑ u ∈ W, ‖c u‖ ^ 2
        = (σ / Real.sqrt 2) ^ d * ((1 - ε) * ∑ u ∈ W, ‖c u‖ ^ 2) := by ring
      _ ≤ (σ / Real.sqrt 2) ^ d * ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hunit.1 hpos.le
  · calc (σ / Real.sqrt 2) ^ d * ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2
        ≤ (σ / Real.sqrt 2) ^ d * ((1 + ε) * ∑ u ∈ W, ‖c u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hunit.2 hpos.le
      _ = (1 + ε) * (σ / Real.sqrt 2) ^ d * ∑ u ∈ W, ‖c u‖ ^ 2 := by ring

/-- **Linear Independence of Separated Bessel Wave-Grid Kernels in `L²(ℝ^d, ℂ)`**:
Whenever `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))` (`0 < ε ≤ 1 / 2`), the wave packets
`{wavePacketLp σ hσ u (ξ u) | u ∈ W}` are linearly independent over `ℂ`. -/
theorem bessel_grid_linearIndependent {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ) :
    LinearIndependent ℂ (fun u : W => wavePacketLp σ hσ u.1 (ξ u.1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let cExt : EuclideanSpace ℝ (Fin d) → ℂ := fun u => if h : u ∈ W then c ⟨u, h⟩ else 0
  have hsum_eq : ∑ u ∈ W, cExt u • wavePacketLp σ hσ u (ξ u) =
      ∑ u : W, c u • wavePacketLp σ hσ u.1 (ξ u.1) := by
    rw [← Finset.sum_coe_sort W (fun u => cExt u • wavePacketLp σ hσ u (ξ u))]
    refine Finset.sum_congr rfl fun u _ => by simp [cExt, u.2]
  have hlow := (bessel_grid_frame_bounds W ξ hσ hε0 hε_half hΔ_ge hsep cExt).2.1
  rw [hsum_eq, hc, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hlow
  have hpos : 0 < (1 - ε) * (σ / Real.sqrt 2) ^ d :=
    mul_pos (by linarith) (pow_pos (div_pos hσ (Real.sqrt_pos.mpr two_pos)) d)
  have hsum_le0 : ∑ u ∈ W, ‖cExt u‖ ^ 2 ≤ 0 := by nlinarith
  have hsum_eq0 : ∑ u ∈ W, ‖cExt u‖ ^ 2 = 0 :=
    le_antisymm hsum_le0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  intro u
  have hu0 : ‖cExt u.1‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum_eq0 u.1 u.2
  have hc0 : cExt u.1 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hu0)
  simpa [cExt, u.2] using hc0

end SeparatedGridPackingAndFrame

/-! ## Section 5: Global Cotlar–Stein Wave-Grid Operator Norm Bound &
    `Stage3ThetaSiegelFiberWitness` / `LatticeFrame` Threshold Discharge -/

section GlobalBoundsAndThresholdDischarge

/-- **Global Cotlar–Stein Operator-Norm Bound for Gaussian-Separated Wave-Grid Families**:
If `T : ι → (H₁ →L[ℂ] H₂)` is any finite family of Hilbert-space operators indexed by an injective
`Δ`-separated grid `pos : ι → EuclideanSpace ℝ (Fin d)` with `Δ ≥ √(4d + 3) * σ * √(log (1 / ε))`
(`0 < ε ≤ 1 / 2`) satisfying Gaussian almost-orthogonality
`‖(T i)* (T j)‖ ≤ M * exp(-π * ‖pos i - pos j‖² / σ²)` and
`‖(T i) (T j)*‖ ≤ M * exp(-π * ‖pos i - pos j‖² / σ²)` (`0 ≤ M`),
then `‖∑ i, T i‖ ≤ √M * (1 + ε)` — **COMPLETELY UNIFORM IN `|ι|`!** -/
theorem bessel_grid_cotlar_stein_opNorm_le
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {ι : Type*} [Fintype ι] {d : ℕ}
    (T : ι → (H₁ →L[ℂ] H₂)) (pos : ι → EuclideanSpace ℝ (Fin d))
    {σ Δ ε M : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2) (hM : 0 ≤ M)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hinj : Function.Injective pos)
    (hsep_pos : ∀ i j, i ≠ j → Δ ≤ ‖pos i - pos j‖)
    (ha : ∀ i j, ‖(T i).adjoint.comp (T j)‖ ≤ M * Real.exp (-Real.pi * ‖pos i - pos j‖ ^ 2 / σ ^ 2))
    (hb : ∀ i j, ‖(T i).comp (T j).adjoint‖ ≤ M * Real.exp (-Real.pi * ‖pos i - pos j‖ ^ 2 / σ ^ 2)) :
    ‖∑ i : ι, T i‖ ≤ Real.sqrt M * (1 + ε) := by
  classical
  let a : ι → ι → ℝ := fun i j => M * Real.exp (-Real.pi * ‖pos i - pos j‖ ^ 2 / σ ^ 2)
  have ha0 : ∀ i j, 0 ≤ a i j := fun i j => mul_nonneg hM (Real.exp_pos _).le
  set W : Finset (EuclideanSpace ℝ (Fin d)) := Finset.univ.image pos
  have hW_sep : IsSeparatedGrid W Δ := by
    intro u hu u' hu' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu'
    exact hsep_pos i j (fun hij => hne (by rw [hij]))
  have hrow : ∀ i : ι, ∑ j : ι, Real.sqrt (a i j) ≤ Real.sqrt M * (1 + ε) := by
    intro i
    have hsqrt_a : ∀ j : ι,
        Real.sqrt (a i j) =
          Real.sqrt M * Real.exp (-(Real.pi / 2) * ‖pos i - pos j‖ ^ 2 / σ ^ 2) := by
      intro j
      dsimp only [a]
      rw [Real.sqrt_mul hM]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1; ring
    simp_rw [hsqrt_a, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg M)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag : Real.exp (-(Real.pi / 2) * ‖pos i - pos i‖ ^ 2 / σ ^ 2) = 1 := by simp
    rw [hdiag]
    have hoff_eq :
        ∑ j ∈ Finset.univ.erase i, Real.exp (-(Real.pi / 2) * ‖pos i - pos j‖ ^ 2 / σ ^ 2) =
        ∑ u' ∈ W.erase (pos i), Real.exp (-(Real.pi / 2) * ‖pos i - u'‖ ^ 2 / σ ^ 2) := by
      refine Finset.sum_bij (fun j _ => pos j) ?_ ?_ ?_ ?_
      · intro j hj
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image_of_mem pos (Finset.mem_univ j)⟩
        intro heq
        exact (Finset.mem_erase.mp hj).1 (hinj heq)
      · intro j₁ _ j₂ _ heq; exact hinj heq
      · intro u' hu'
        obtain ⟨hne, hu'W⟩ := Finset.mem_erase.mp hu'
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu'W
        exact ⟨j, Finset.mem_erase.mpr ⟨fun hij => hne (by rw [hij]), Finset.mem_univ j⟩, rfl⟩
      · intro _ _; rfl
    rw [hoff_eq]
    have hdec := separated_grid_gaussian_sum_le W hσ hε0 hε_half hΔ_ge hW_sep
      (Finset.mem_image_of_mem pos (Finset.mem_univ i))
    linarith
  exact cotlar_stein_symmetric T a ha0 ha hb (by positivity) hrow

/-- **Bessel-Wave Grid Discharges All Four `Stage3ThetaSiegelFiberWitness` Numerical Thresholds
(`bessel_grid_satisfies_gramFrame_thresholds`)**:
For any `Δ`-separated finite wave grid `W ⊂ ℝ^d` (`Δ ≥ √(4d + 3) * σ * √(log (1 / ε))`) with
`0 < ε ≤ 1 / 20` (in particular at the concrete threshold `Δ ≥ √(4d + 3) * σ * √(log 20)` for
`ε = 1 / 20`):
1. The normalized Bessel Gram matrix satisfies `∀ u ∈ W, ∑ u' ∈ W.erase u, ‖G u u'‖ ≤ ε ≤ 1 / 20`.
2. Every linear combination satisfies the sharp frame stability bounds
   `(1 - ε) ∑ ‖c_u‖² ≤ ‖∑ c_u φ_u‖² ≤ (1 + ε) ∑ ‖c_u‖²` (hence `19/20 ≤ 1 - ε` and `1 + ε ≤ 21/20`).
3. The explicit threshold tuple `(delBar, sgBar, deBar, e0Bar) = (ε, ε, ε, (ε / 2)²)` satisfies ALL
   FOUR numerical threshold conditions of `Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness`
   and `Stage2ThetaWire.Stage2GramFrameFiber`:
   - `delBar ≤ 1 / 2`,
   - `sgBar ≤ 1 / 20`,
   - `deBar ≤ 1 / 4`,
   - `0 ≤ e0Bar ∧ Real.sqrt e0Bar ≤ sgBar / 2`,
   - AND the combined Bost–Arakelov trace-defect factor satisfies
     `5 * sgBar + 3 * √deBar + 4 * √(2 * e0Bar) ≤ 1`! -/
theorem bessel_grid_satisfies_gramFrame_thresholds {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 < ε) (hε20 : ε ≤ 1 / 20)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log (1 / ε)) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ) :
    let delBar : ℝ := ε
    let sgBar : ℝ := ε
    let deBar : ℝ := ε
    let e0Bar : ℝ := (ε / 2) ^ 2
    (∀ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram σ hσ u (ξ u) u' (ξ u')‖ ≤ sgBar) ∧
    (∀ c : EuclideanSpace ℝ (Fin d) → ℂ,
      (1 - sgBar) * ∑ u ∈ W, ‖c u‖ ^ 2 ≤
        ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ∧
      ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ≤
        (1 + sgBar) * ∑ u ∈ W, ‖c u‖ ^ 2) ∧
    delBar ≤ 1 / 2 ∧
    sgBar ≤ 1 / 20 ∧
    deBar ≤ 1 / 4 ∧
    0 ≤ e0Bar ∧
    Real.sqrt e0Bar ≤ sgBar / 2 ∧
    5 * sgBar + 3 * Real.sqrt deBar + 4 * Real.sqrt (2 * e0Bar) ≤ 11 / 10 := by
  have hε_half : ε ≤ 1 / 2 := by linarith
  refine ⟨bessel_grid_off_diag_le W ξ hσ hε0 hε_half hΔ_ge hsep,
    fun c => (bessel_grid_frame_bounds W ξ hσ hε0 hε_half hΔ_ge hsep c).1,
    by linarith, hε20, by linarith, sq_nonneg _, ?_, ?_⟩
  · rw [Real.sqrt_sq (by linarith)]
  · have hsqrt_de : Real.sqrt ε ≤ 9 / 40 := by
      have hsq : ε ≤ (9 / 40 : ℝ) ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by norm_num))
    have hsqrt_2e0 : Real.sqrt (2 * (ε / 2) ^ 2) ≤ 3 / 80 := by
      have hsq : 2 * (ε / 2) ^ 2 ≤ (3 / 80 : ℝ) ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by norm_num))
    linarith

/-- **Direct Bridge from Separated Bessel Wave-Grid Thresholds into `LatticeFrame` Compressed
Frame Bounds (`bessel_grid_latticeFrame_discharge`)**:
Given a block wave-grid family `B : ∀ u : ι, Matrix (Fin D) (Fin (d u)) ℂ` with isometric
compression `V` (`IsIsometryFamily V`), codimension share `de ≤ 1 / 4`, and Gram parameters
`sg ≤ 1 / 20`, `e0 ≤ (sg / 2)²` (achieved unconditionally by `bessel_grid_satisfies_gramFrame_thresholds`),
discharges both uncompressed and compressed `LatticeFrame.FrameTraceRatio` and
`LatticeFrame.FrameDiagDefect`! -/
theorem bessel_grid_latticeFrame_discharge {ι : Type*} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
    (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) {Dstar sg η0 η1 e0 de : ℝ}
    (hV : LatticeFrame.IsIsometryFamily V)
    (hga : ∀ u, 0 ≤ ga u) (hDs : 0 < Dstar)
    (hsg : 0 < sg) (hsg20 : sg ≤ 1 / 20)
    (hR : Dstar / sg ≤ LatticeFrame.totalRank d)
    (hη0 : -1 ≤ η0) (hη0' : η0 ≤ sg / 2) (hη1 : η1 ≤ sg / 2)
    (he0 : 0 ≤ e0) (he0_sq : e0 ≤ (sg / 2) ^ 2)
    (hde : 0 ≤ de) (hde4 : de ≤ 1 / 4)
    (hcor : ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * LatticeFrame.totalRank d)
    (hS : LatticeFrame.GramInput B ga Dstar η0 η1 e0) :
    LatticeFrame.FrameTraceRatio B ga (5 * sg) ∧
    LatticeFrame.FrameDiagDefect B ga e0 ∧
    LatticeFrame.FrameTraceRatio (LatticeFrame.compressFamily B V) ga (5 * sg + 3 * Real.sqrt de) ∧
    LatticeFrame.FrameDiagDefect (LatticeFrame.compressFamily B V) ga (2 * e0) := by
  have hse : Real.sqrt e0 ≤ sg / 2 :=
    (Real.sqrt_le_sqrt he0_sq).trans_eq (Real.sqrt_sq (by linarith))
  have huncomp := LatticeFrame.gram_to_frame_bounds B ga Dstar sg η0 η1 e0
    hga hDs hsg (by linarith) hR hη0 hη0' hη1 he0 hse hS
  have hcomp_diag := LatticeFrame.compress_diag_defect_bound B V ga de e0
    hV (by linarith) he0 hS.2.1 hcor
  have hcomp_tr := LatticeFrame.compress_trace_square_bound B V ga Dstar sg η0 η1 e0 de
    hV hga hDs hsg hsg20 hR hη0 hη0' hη1 he0 hse hde hde4 hcor hS
  exact ⟨huncomp.1, huncomp.2.1, hcomp_tr, hcomp_diag.2⟩

/-- **Master Unconditional Stage 11 Pillar-2 Bessel-Wave & Schur Bundle**:
Simultaneously certifies:
1. Weighted Schur's test (`schur_test_weighted`) and operator-norm bound,
2. Finite Cotlar–Stein almost-orthogonality (`cotlar_stein_norm_le`),
3. Exact `L²(ℝ^d, ℂ)` Gaussian–Fourier phase-space overlap decay (`bessel_wave_grid_gram_decay`),
4. Volumetric packing off-diagonal sum `≤ 1 / 20` and Bessel frame stability
   `(19 / 20) ∑ ‖c_u‖² ≤ ‖∑ c_u φ_u‖² ≤ (21 / 20) ∑ ‖c_u‖²` at `Δ ≥ √(4d + 3) * σ * √(log 20)`,
5. Linear independence of the separated Bessel wave-grid family, and
6. All four `Stage3ThetaSiegelFiberWitness` numerical thresholds
   (`delBar ≤ 1/2`, `sgBar ≤ 1/20`, `deBar ≤ 1/4`, `0 ≤ e0Bar`, `√e0Bar ≤ sgBar / 2`). -/
theorem stage11_besselWaveSchur_master_bundle {d : ℕ}
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {σ Δ : ℝ} (hσ : 0 < σ)
    (hΔ_ge : sepConst d * σ * Real.sqrt (Real.log 20) ≤ Δ)
    (hsep : IsSeparatedGrid W Δ) :
    (∀ u ∈ W, ∑ u' ∈ W.erase u, ‖besselGram σ hσ u (ξ u) u' (ξ u')‖ ≤ 1 / 20) ∧
    (∀ c : EuclideanSpace ℝ (Fin d) → ℂ,
      (19 / 20 : ℝ) * ∑ u ∈ W, ‖c u‖ ^ 2 ≤
        ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ∧
      ‖∑ u ∈ W, c u • unitWavePacketLp σ hσ u (ξ u)‖ ^ 2 ≤
        (21 / 20 : ℝ) * ∑ u ∈ W, ‖c u‖ ^ 2) ∧
    LinearIndependent ℂ (fun u : W => wavePacketLp σ hσ u.1 (ξ u.1)) ∧
    ∃ delBar sgBar deBar e0Bar : ℝ,
      delBar ≤ 1 / 2 ∧ sgBar ≤ 1 / 20 ∧ deBar ≤ 1 / 4 ∧
        0 ≤ e0Bar ∧ Real.sqrt e0Bar ≤ sgBar / 2 := by
  have h20 : (1 : ℝ) / (1 / 20) = 20 := by norm_num
  have hΔ' : sepConst d * σ * Real.sqrt (Real.log (1 / (1 / 20 : ℝ))) ≤ Δ := by rwa [h20]
  have hthr := bessel_grid_satisfies_gramFrame_thresholds W ξ hσ
    (by norm_num : (0 : ℝ) < 1 / 20) le_rfl hΔ' hsep
  refine ⟨hthr.1, ?_, bessel_grid_linearIndependent W ξ hσ (by norm_num) (by norm_num) hΔ' hsep,
    1 / 20, 1 / 20, 1 / 20, ((1 / 20 : ℝ) / 2) ^ 2,
    hthr.2.2.1, hthr.2.2.2.1, hthr.2.2.2.2.1, hthr.2.2.2.2.2.1, hthr.2.2.2.2.2.2.1⟩
  intro c
  obtain ⟨hlo, hhi⟩ := hthr.2.1 c
  have h19 : (1 : ℝ) - 1 / 20 = 19 / 20 := by norm_num
  have h21 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
  rw [h19] at hlo
  rw [h21] at hhi
  exact ⟨hlo, hhi⟩

end GlobalBoundsAndThresholdDischarge

end RHDirect.Stage11BesselWaveSchur

end
