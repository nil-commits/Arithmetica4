import RHDirect.HermitianCurvatureCore
import RHDirect.BesselWaveGrid
import RHDirect.CapelliCore
import RHDirect.Stage2ThetaWire
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# RHDirect.Stage3ExplicitSpectral

Stage 3 Pillar-2 deep mathematical discharge of **Spectral Multiplicity, Heat-Kernel & Wave-Kernel
Tauberian Smoothing, Bochner–Kodaira–Nakano Curvature Positivity, Spectral Gap & Resolvent Bounds,
and Unified Transfer to `BesselWaveGrid` + `CapelliCore` + `HermitianCurvatureCore` +
`Stage2ThetaWire`**, with **0 `sorry`, 0 custom `axiom`s**.

## Contents

1. **Discrete Spectral Counting `N(Λ)` & Heat-Kernel Tauberian Upper Bounds** (finite & infinite):
   - `specCountFin`, `heatTraceFin`, `DiscreteSpectrum`, `DiscreteSpectrum.specCount`,
     `DiscreteSpectrum.heatTrace`.
   - Automatic summability of spectral counts & finiteness of sublevel sets `{k | λ_k ≤ Λ}` from
     heat-trace convergence at any `t ≥ 0` (`DiscreteSpectrum.summable_specCount_of_heatTrace`,
     `DiscreteSpectrum.finite_sublevel_of_heatTrace`).
   - Sharp **Karamata / Markov Spectral-Counting Upper Bounds**:
     `N(Λ) ≤ exp(t Λ) · Z(t)` for every `t ≥ 0`, and `N(Λ) ≤ e · Z(1 / Λ)` for every `Λ > 0`
     (`karamata_markov_fin`, `karamata_markov_fin_inv`,
     `DiscreteSpectrum.specCount_le_exp_mul_heatTrace`,
     `DiscreteSpectrum.specCount_le_e_mul_heatTrace_inv`).
   - Exact **Weyl-Law Upper Bounds**:
     - Canonical `t = 1 / Λ` bound: `Z(t) ≤ C t^{-d/2} ⇒ N(Λ) ≤ e · C · Λ^{d/2}`
       (`weyl_upper_fin`, `DiscreteSpectrum.weyl_upper_bound`, `DiscreteSpectrum.weyl_upper_bound_all`).
     - Optimized `t = α / Λ` Karamata–Weyl constant `(e / α)^α · C · Λ^α`
       (`weyl_upper_fin_optimal`, `DiscreteSpectrum.weyl_upper_bound_optimal`).
     - Two-term heat-asymptotic Weyl upper bound (`DiscreteSpectrum.weyl_upper_bound_two_term`).
   - Log-convexity (`heatTraceFin_log_convex`) and spectral-gap exponential decay of the heat trace
     (`heatTraceFin_spectral_gap_decay`, `DiscreteSpectrum.heatTrace_gap_decay`), plus exact
     eigenvalue-shift identities (`DiscreteSpectrum.specCount_shift`, `DiscreteSpectrum.heatTrace_shift`).

2. **Spectral Window Localization via Gaussian, Smooth & Lorentzian/Resolvent Wave Kernels**:
   - `windowCountFin`, `gaussWaveTraceFin`, `lorentzWaveTraceFin`, and infinite counterparts
     `DiscreteSpectrum.windowCount`, `DiscreteSpectrum.gaussWaveTrace`,
     `DiscreteSpectrum.lorentzWaveTrace`.
   - Sharp **Gaussian Wave-Kernel Localization**:
     `e^{-1/2} · #{k : |λ_k - Λ| ≤ σ} ≤ ∑_k m_k exp(-(λ_k - Λ)² / (2 σ²))`
     (`gaussWaveTraceFin_ge_exp_neg_half_mul_windowCountFin`,
     `card_window_le_exp_half_mul_gauss_sum`,
     `DiscreteSpectrum.gaussWaveTrace_ge_exp_neg_half_mul_windowCount`).
   - General non-negative wave-kernel localization & Lorentzian/resolvent-trace bound
     (`DiscreteSpectrum.waveKernel_localization`,
     `DiscreteSpectrum.windowCount_le_two_mul_lorentzWaveTrace`).
   - Exact completing-the-square **Gaussian-to-Heat-Trace Comparison**:
     `gaussWaveTrace Λ σ ≤ exp(t Λ + t² σ² / 2) · Z(t)` and short-interval covering partition bound
     (`DiscreteSpectrum.gaussWaveTrace_le_heatTrace`, `DiscreteSpectrum.windowCount_le_heatTrace`,
     `intervalCountFin_le_sum_windows`).

3. **Bochner–Kodaira–Nakano Curvature Positivity, Spectral Gap & Quantitative Resolvent Bounds**:
   - General complex inner product spaces: for `Δ = D* ∘ D + R` with curvature lower bound
     `Re ⟨R u, u⟩ ≥ κ ‖u‖²` (`κ > 0`):
     - Exact Bochner–Kodaira–Nakano energy identity (`bochner_energy_identity`, `bochner_energy_re`),
     - Coercivity `κ ‖u‖ ≤ ‖Δ u‖` (`bochner_coercivity`, `bochner_norm_ge`),
     - **Kodaira Vanishing** `ker Δ = ⊥` (`kodaira_vanishing_ker_eq_bot`) & harmonic rigidity for
       `κ = 0` (`bochner_harmonic_rigidity_nonneg`),
     - **Strict Spectral Gap** `λ_1 ≥ κ` (`bochner_spectral_gap`, `bochner_spectral_gap_symmetric`),
     - **Sharp Distance-to-Spectrum Shifted Resolvent Coercivity**
       `√(max(κ - Re z, 0)² + (Im z)²) · ‖u‖ ≤ ‖(Δ - z I) u‖` (`bochner_shifted_coercivity`),
     - **Quantitative Resolvent Norm Bound** `‖Δ⁻¹‖ ≤ κ⁻¹` (`bochner_resolvent_norm_le`,
       `bochner_finDim_complete`, `bochner_finDim_shifted_resolvent`).
   - Hermitian Matrix & `HermitianCurvatureCore` transfer (`bochnerMatrix D R = Dᴴ * D + R`):
     - Positivity transfer `(R - κ I).PosSemidef ⇒ (Δ - κ I).PosSemidef ∧ Δ.PosDef`,
       `Δ.det ≠ 0`, `∀ i, κ ≤ hH.eigenvalues i`, `‖Matrix.toEuclideanLin Δ⁻¹‖ ≤ κ⁻¹`,
     - Metric-interpolation spectral-gap persistence via
       `HermitianCurvatureCore.hermitian_posSemidef_lerp` (`bochnerMatrix_lerp_spectral_gap`),
     - Direct coupling to Pillar 1 spectral counting & heat-trace gap decay
       (`bochnerMatrix_specCount_eq_zero_below_gap`, `bochnerMatrix_heatTrace_gap_decay`).

4. **Capelli Eigenvalue-Shift & Bessel Wave-Grid Spectral Localization Bridges**:
   - `qdet_two_spectral_shift` (from `CapelliCore.qdet_two_holomorphic_eigenvalue`),
   - `casC_rho_shift_identity` & `casC_shifted_spectral_gap` (from `CapelliCore.casC_eq_sum_shifted`),
   - `waveGram_bochner_enhanced_gap` (additive enhanced gap `(dMin - η) + κ` coupling
     `BesselWaveGrid.gram_frobenius_frame_bound` + `BesselWaveGrid.waveGram` + curvature `R ≥ κ I`,
     paired with Lagrange delta test vectors via `BesselWaveGrid.exists_delta_test_vector_progY`),
   - `waveGrid_multiplicity_budget_of_heatTrace` (matching Karamata–Weyl multiplicity bounds
     against `BesselWaveGrid.rankVal_wave_grid_bounds`).

5. **Unified Stage-3 Explicit Spectral Discharge & Bridge to `Stage2ThetaWire`**:
   - `stage3_explicit_spectral_discharge` (unified discharge combining all three pillars),
   - `stage3_gramFrame_spectral_bost_bridge` (wiring `Stage2ThetaWire.Stage2GramFrameFiber` +
     Bochner curvature spectral gap into `BostSlopeFiber.SlopeIneq`),
   - `SpectralMultiplicityCert`, `Stage3SpectralThetaInputs`, `stage3_thetaSlopeContract`, and
     `stage3_allLevelsWindowBound` feeding `Stage2ThetaWire.stage2_thetaSlopeContract` directly!
-/

open Real Finset Matrix Filter RHDirect RHDirect.Stage2ThetaWire
open scoped BigOperators InnerProductSpace ComplexConjugate ComplexOrder

namespace RHDirect.Stage3ExplicitSpectral

noncomputable section

/-! ## Section 1: Discrete Spectral Counting `N(Λ)` & Heat-Kernel Tauberian Upper Bounds -/

section FiniteHeatTauberian

variable {ι : Type*}

/-- Finite discrete spectral counting function `N_S(Λ) = ∑_{k ∈ S, λ_k ≤ Λ} m_k`. -/
def specCountFin (eig mult : ι → ℝ) (S : Finset ι) (Λ : ℝ) : ℝ :=
  ∑ k ∈ S.filter (fun k => eig k ≤ Λ), mult k

/-- Finite discrete heat trace `Z_S(t) = ∑_{k ∈ S} m_k exp(-t λ_k)`. -/
def heatTraceFin (eig mult : ι → ℝ) (S : Finset ι) (t : ℝ) : ℝ :=
  ∑ k ∈ S, mult k * Real.exp (-t * eig k)

theorem specCountFin_nonneg {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) (Λ : ℝ) :
    0 ≤ specCountFin eig mult S Λ :=
  Finset.sum_nonneg fun k hk => hm k (Finset.mem_filter.mp hk).1

theorem specCountFin_mono {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {Λ₁ Λ₂ : ℝ} (hΛ : Λ₁ ≤ Λ₂) :
    specCountFin eig mult S Λ₁ ≤ specCountFin eig mult S Λ₂ := by
  unfold specCountFin
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k hk _ => hm k (Finset.mem_filter.mp hk).1)
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.trans hΛ⟩

theorem heatTraceFin_nonneg {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) (t : ℝ) :
    0 ≤ heatTraceFin eig mult S t :=
  Finset.sum_nonneg fun k hk => mul_nonneg (hm k hk) (Real.exp_pos _).le

theorem heatTraceFin_antitone {eig mult : ι → ℝ} {S : Finset ι}
    (heig : ∀ k ∈ S, 0 ≤ eig k) (hm : ∀ k ∈ S, 0 ≤ mult k) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    heatTraceFin eig mult S t₂ ≤ heatTraceFin eig mult S t₁ := by
  unfold heatTraceFin
  refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hm k hk)
  exact Real.exp_le_exp.mpr (by nlinarith [heig k hk])

theorem specCountFin_eq_zero_of_lt_gap {eig mult : ι → ℝ} {S : Finset ι} {κ Λ : ℝ}
    (hgap : ∀ k ∈ S, κ ≤ eig k) (hΛ : Λ < κ) :
    specCountFin eig mult S Λ = 0 := by
  unfold specCountFin
  refine Finset.sum_eq_zero fun k hk => ?_
  have ⟨hkS, hkΛ⟩ := Finset.mem_filter.mp hk
  exact absurd (le_trans (hgap k hkS) hkΛ) (not_le.mpr hΛ)

/-- **Sharp Finite Karamata / Markov Spectral-Counting Upper Bound**:
for every `t ≥ 0` and every threshold `Λ : ℝ`,
`N_S(Λ) ≤ exp(t Λ) · Z_S(t)`. -/
theorem karamata_markov_fin {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {t : ℝ} (ht : 0 ≤ t) (Λ : ℝ) :
    specCountFin eig mult S Λ ≤ Real.exp (t * Λ) * heatTraceFin eig mult S t := by
  unfold specCountFin heatTraceFin
  rw [Finset.mul_sum]
  have hsub :
      ∑ k ∈ S.filter (fun k => eig k ≤ Λ), mult k ≤
        ∑ k ∈ S.filter (fun k => eig k ≤ Λ), Real.exp (t * Λ) * (mult k * Real.exp (-t * eig k)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have ⟨hkS, hkΛ⟩ := Finset.mem_filter.mp hk
    have hexp : 1 ≤ Real.exp (t * Λ) * Real.exp (-t * eig k) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hexp (hm k hkS)
    linarith
  refine hsub.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) ?_)
  intro k hk _
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hm k hk) (Real.exp_pos _).le)

/-- **Canonical `t = 1 / Λ` Karamata / Markov Bound**:
for every `Λ > 0`, `N_S(Λ) ≤ e · Z_S(1 / Λ)`. -/
theorem karamata_markov_fin_inv {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {Λ : ℝ} (hΛ : 0 < Λ) :
    specCountFin eig mult S Λ ≤ Real.exp 1 * heatTraceFin eig mult S (1 / Λ) := by
  have h := karamata_markov_fin (eig := eig) hm (div_nonneg zero_le_one hΛ.le) Λ
  have h1 : (1 / Λ) * Λ = 1 := one_div_mul_cancel hΛ.ne'
  rwa [h1] at h

/-- **Exact Finite Weyl-Law Upper Bound**:
if `Z_S(1 / Λ) ≤ C · (1 / Λ)^{-d / 2}`, then `N_S(Λ) ≤ e · C · Λ^{d / 2}` for every `Λ > 0`. -/
theorem weyl_upper_fin {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {C d Λ : ℝ} (hΛ : 0 < Λ)
    (hZ : heatTraceFin eig mult S (1 / Λ) ≤ C * (1 / Λ) ^ (-(d / 2))) :
    specCountFin eig mult S Λ ≤ Real.exp 1 * C * Λ ^ (d / 2) := by
  have hpow : (1 / Λ) ^ (-(d / 2)) = Λ ^ (d / 2) := by
    rw [one_div, Real.inv_rpow hΛ.le, Real.rpow_neg hΛ.le, inv_inv]
  rw [hpow] at hZ
  calc specCountFin eig mult S Λ
      ≤ Real.exp 1 * heatTraceFin eig mult S (1 / Λ) := karamata_markov_fin_inv hm hΛ
    _ ≤ Real.exp 1 * (C * Λ ^ (d / 2)) := mul_le_mul_of_nonneg_left hZ (Real.exp_pos 1).le
    _ = Real.exp 1 * C * Λ ^ (d / 2) := by ring

/-- **Exponent-Optimized Karamata–Weyl Upper Bound**:
evaluating at the optimal scale `t = α / Λ` (`α > 0`) sharpens the Weyl constant from `e` to
`(e / α)^α` whenever `Z_S(α / Λ) ≤ C · (α / Λ)^{-α}`. -/
theorem weyl_upper_fin_optimal {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {C α Λ : ℝ} (hα : 0 < α) (hΛ : 0 < Λ)
    (hZ : heatTraceFin eig mult S (α / Λ) ≤ C * (α / Λ) ^ (-α)) :
    specCountFin eig mult S Λ ≤ (Real.exp 1 / α) ^ α * C * Λ ^ α := by
  have ht : 0 ≤ α / Λ := div_nonneg hα.le hΛ.le
  have hkm := karamata_markov_fin (eig := eig) hm ht Λ
  have hmul : (α / Λ) * Λ = α := div_mul_cancel₀ α hΛ.ne'
  rw [hmul] at hkm
  have hpow : (α / Λ) ^ (-α) = α ^ (-α) * Λ ^ α := by
    rw [Real.div_rpow hα.le hΛ.le, Real.rpow_neg hα.le, Real.rpow_neg hΛ.le, div_inv_eq_mul]
  have hconst : Real.exp α * α ^ (-α) = (Real.exp 1 / α) ^ α := by
    rw [Real.div_rpow (Real.exp_pos 1).le hα.le, ← Real.exp_mul, one_mul,
      Real.rpow_neg hα.le, div_eq_mul_inv]
  calc specCountFin eig mult S Λ
      ≤ Real.exp α * heatTraceFin eig mult S (α / Λ) := hkm
    _ ≤ Real.exp α * (C * (α / Λ) ^ (-α)) := mul_le_mul_of_nonneg_left hZ (Real.exp_pos α).le
    _ = (Real.exp α * α ^ (-α)) * C * Λ ^ α := by rw [hpow]; ring
    _ = (Real.exp 1 / α) ^ α * C * Λ ^ α := by rw [hconst]

/-- **Log-Convexity of the Heat Trace** (via Cauchy–Schwarz):
`Z_S((t₁ + t₂) / 2)² ≤ Z_S(t₁) · Z_S(t₂)` for all `t₁, t₂ : ℝ`. -/
theorem heatTraceFin_log_convex {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) (t₁ t₂ : ℝ) :
    heatTraceFin eig mult S ((t₁ + t₂) / 2) ^ 2 ≤
      heatTraceFin eig mult S t₁ * heatTraceFin eig mult S t₂ := by
  let f : ι → ℝ := fun k => Real.sqrt (mult k) * Real.exp (-(t₁ * eig k) / 2)
  let g : ι → ℝ := fun k => Real.sqrt (mult k) * Real.exp (-(t₂ * eig k) / 2)
  have hfg : ∑ k ∈ S, f k * g k = heatTraceFin eig mult S ((t₁ + t₂) / 2) := by
    unfold heatTraceFin
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp only [f, g]
    have hsq : Real.sqrt (mult k) * Real.sqrt (mult k) = mult k := Real.mul_self_sqrt (hm k hk)
    have hexp : Real.exp (-(t₁ * eig k) / 2) * Real.exp (-(t₂ * eig k) / 2) =
        Real.exp (-((t₁ + t₂) / 2) * eig k) := by
      rw [← Real.exp_add]
      congr 1; ring
    calc (Real.sqrt (mult k) * Real.exp (-(t₁ * eig k) / 2)) *
            (Real.sqrt (mult k) * Real.exp (-(t₂ * eig k) / 2))
        = (Real.sqrt (mult k) * Real.sqrt (mult k)) *
            (Real.exp (-(t₁ * eig k) / 2) * Real.exp (-(t₂ * eig k) / 2)) := by ring
      _ = mult k * Real.exp (-((t₁ + t₂) / 2) * eig k) := by rw [hsq, hexp]
  have hf2 : ∑ k ∈ S, f k ^ 2 = heatTraceFin eig mult S t₁ := by
    unfold heatTraceFin
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt (hm k hk), ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hg2 : ∑ k ∈ S, g k ^ 2 = heatTraceFin eig mult S t₂ := by
    unfold heatTraceFin
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (hm k hk), ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  rw [← hfg, ← hf2, ← hg2]
  exact Finset.sum_mul_sq_le_sq_mul_sq S f g

/-- **Spectral-Gap Exponential Decay of the Heat Trace**:
if `κ ≤ λ_k` for every `k ∈ S`, then `Z_S(t) ≤ exp(-κ (t - t₀)) · Z_S(t₀)` for all `t₀ ≤ t`. -/
theorem heatTraceFin_spectral_gap_decay {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {κ t₀ t : ℝ}
    (hgap : ∀ k ∈ S, κ ≤ eig k) (ht : t₀ ≤ t) :
    heatTraceFin eig mult S t ≤ Real.exp (-κ * (t - t₀)) * heatTraceFin eig mult S t₀ := by
  unfold heatTraceFin
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hexp : Real.exp (-t * eig k) ≤ Real.exp (-κ * (t - t₀)) * Real.exp (-t₀ * eig k) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hgap k hk])
  have hmul := mul_le_mul_of_nonneg_left hexp (hm k hk)
  linarith

end FiniteHeatTauberian

/-! ### Infinite / Countable Discrete Spectrum (`DiscreteSpectrum`) -/

/-- A discrete non-negative spectrum `{λ_k}_{k : ι}` with non-negative multiplicities / spectral
weights `m_k ≥ 0`. -/
structure DiscreteSpectrum (ι : Type*) where
  eig : ι → ℝ
  mult : ι → ℝ
  eig_nonneg : ∀ k, 0 ≤ eig k
  mult_nonneg : ∀ k, 0 ≤ mult k

namespace DiscreteSpectrum

variable {ι : Type*}

/-- Construct a `DiscreteSpectrum` from natural-number multiplicities `m : ι → ℕ`. -/
def ofNatMult (eig : ι → ℝ) (m : ι → ℕ) (heig : ∀ k, 0 ≤ eig k) : DiscreteSpectrum ι where
  eig := eig
  mult := fun k => (m k : ℝ)
  eig_nonneg := heig
  mult_nonneg := fun k => Nat.cast_nonneg (m k)

/-- Infinite spectral counting function `N(Λ) = ∑'_{λ_k ≤ Λ} m_k`. -/
def specCount (D : DiscreteSpectrum ι) (Λ : ℝ) : ℝ :=
  ∑' k : ι, if D.eig k ≤ Λ then D.mult k else 0

/-- Infinite heat trace `Z(t) = ∑'_k m_k exp(-t λ_k)`. -/
def heatTrace (D : DiscreteSpectrum ι) (t : ℝ) : ℝ :=
  ∑' k : ι, D.mult k * Real.exp (-t * D.eig k)

/-- Predicate stating that the heat trace converges at time `t`. -/
def HeatSummable (D : DiscreteSpectrum ι) (t : ℝ) : Prop :=
  Summable fun k : ι => D.mult k * Real.exp (-t * D.eig k)

theorem heatSummable_of_le (D : DiscreteSpectrum ι) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (h1 : D.HeatSummable t₁) : D.HeatSummable t₂ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (D.mult_nonneg k) (Real.exp_pos _).le)
    (fun k => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [D.eig_nonneg k]))
      (D.mult_nonneg k)) h1

/-- Heat-trace convergence at ANY `t ≥ 0` automatically implies summability of the spectral
counting series at every threshold `Λ : ℝ`! -/
theorem summable_specCount_of_heatTrace (D : DiscreteSpectrum ι) {t : ℝ} (ht : 0 ≤ t)
    (hZ : D.HeatSummable t) (Λ : ℝ) :
    Summable fun k : ι => if D.eig k ≤ Λ then D.mult k else 0 := by
  refine Summable.of_nonneg_of_le
    (fun k => by split_ifs <;> [exact D.mult_nonneg k; exact le_rfl]) ?_
    (hZ.mul_left (Real.exp (t * Λ)))
  intro k
  split_ifs with hk
  · have hexp : 1 ≤ Real.exp (t * Λ) * Real.exp (-t * D.eig k) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hexp (D.mult_nonneg k)
    linarith
  · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (D.mult_nonneg k) (Real.exp_pos _).le)

/-- **Compact-Resolvent Discreteness**: if `Z(t)` converges for some `t ≥ 0` and every eigenvalue
carries multiplicity `m_k ≥ 1`, then every sublevel set `{k | λ_k ≤ Λ}` is finite! -/
theorem finite_sublevel_of_heatTrace (D : DiscreteSpectrum ι) {t : ℝ} (ht : 0 ≤ t)
    (hZ : D.HeatSummable t) (hmult : ∀ k, 1 ≤ D.mult k) (Λ : ℝ) :
    {k : ι | D.eig k ≤ Λ}.Finite := by
  have hsum := D.summable_specCount_of_heatTrace ht hZ Λ
  have htend : Tendsto (fun k : ι => if D.eig k ≤ Λ then D.mult k else 0) cofinite (nhds 0) :=
    hsum.tendsto_cofinite_zero
  have hev : ∀ᶠ k : ι in cofinite, (if D.eig k ≤ Λ then D.mult k else 0) < 1 :=
    htend.eventually (Iio_mem_nhds zero_lt_one)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun k hk => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hk ⊢
  rw [if_pos hk]
  exact hmult k

theorem specCount_nonneg (D : DiscreteSpectrum ι) (Λ : ℝ) : 0 ≤ D.specCount Λ :=
  tsum_nonneg fun k => by split_ifs <;> [exact D.mult_nonneg k; exact le_rfl]

theorem heatTrace_nonneg (D : DiscreteSpectrum ι) (t : ℝ) : 0 ≤ D.heatTrace t :=
  tsum_nonneg fun k => mul_nonneg (D.mult_nonneg k) (Real.exp_pos _).le

theorem specCount_eq_zero_of_gap (D : DiscreteSpectrum ι) {κ Λ : ℝ}
    (hgap : ∀ k, κ ≤ D.eig k) (hΛ : Λ < κ) :
    D.specCount Λ = 0 := by
  unfold specCount
  have hz : (fun k : ι => if D.eig k ≤ Λ then D.mult k else 0) = fun _ => (0 : ℝ) :=
    funext fun k => if_neg (not_le.mpr (lt_of_lt_of_le hΛ (hgap k)))
  rw [hz, tsum_zero]

/-- **Sharp Karamata / Markov Spectral-Counting Upper Bound (Infinite Spectrum)**:
for every `t ≥ 0` with `D.HeatSummable t` and every `Λ : ℝ`,
`N(Λ) ≤ exp(t Λ) · Z(t)`. -/
theorem specCount_le_exp_mul_heatTrace (D : DiscreteSpectrum ι) {t : ℝ} (ht : 0 ≤ t)
    (hZ : D.HeatSummable t) (Λ : ℝ) :
    D.specCount Λ ≤ Real.exp (t * Λ) * D.heatTrace t := by
  unfold specCount heatTrace
  rw [← tsum_mul_left]
  refine (D.summable_specCount_of_heatTrace ht hZ Λ).tsum_le_tsum ?_ (hZ.mul_left _)
  intro k
  split_ifs with hk
  · have hexp : 1 ≤ Real.exp (t * Λ) * Real.exp (-t * D.eig k) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hexp (D.mult_nonneg k)
    linarith
  · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (D.mult_nonneg k) (Real.exp_pos _).le)

/-- **Canonical `t = 1 / Λ` Karamata / Markov Bound (Infinite Spectrum)**:
for every `Λ > 0` with `D.HeatSummable (1 / Λ)`,
`N(Λ) ≤ e · Z(1 / Λ)`. -/
theorem specCount_le_e_mul_heatTrace_inv (D : DiscreteSpectrum ι) {Λ : ℝ} (hΛ : 0 < Λ)
    (hZ : D.HeatSummable (1 / Λ)) :
    D.specCount Λ ≤ Real.exp 1 * D.heatTrace (1 / Λ) := by
  have h := D.specCount_le_exp_mul_heatTrace (div_nonneg zero_le_one hΛ.le) hZ Λ
  have h1 : (1 / Λ) * Λ = 1 := one_div_mul_cancel hΛ.ne'
  rwa [h1] at h

/-- **Exact Weyl-Law Upper Bound (Pointwise Scale)**:
if `Z(1 / Λ) ≤ C · (1 / Λ)^{-d / 2}`, then `N(Λ) ≤ e · C · Λ^{d / 2}` for every `Λ > 0`. -/
theorem weyl_upper_bound (D : DiscreteSpectrum ι) {C d Λ : ℝ} (hΛ : 0 < Λ)
    (hZsum : D.HeatSummable (1 / Λ))
    (hZ : D.heatTrace (1 / Λ) ≤ C * (1 / Λ) ^ (-(d / 2))) :
    D.specCount Λ ≤ Real.exp 1 * C * Λ ^ (d / 2) := by
  have hpow : (1 / Λ) ^ (-(d / 2)) = Λ ^ (d / 2) := by
    rw [one_div, Real.inv_rpow hΛ.le, Real.rpow_neg hΛ.le, inv_inv]
  rw [hpow] at hZ
  calc D.specCount Λ
      ≤ Real.exp 1 * D.heatTrace (1 / Λ) := D.specCount_le_e_mul_heatTrace_inv hΛ hZsum
    _ ≤ Real.exp 1 * (C * Λ ^ (d / 2)) := mul_le_mul_of_nonneg_left hZ (Real.exp_pos 1).le
    _ = Real.exp 1 * C * Λ ^ (d / 2) := by ring

/-- **Global Weyl-Law Upper Bound**:
if `Z(t) ≤ C · t^{-d / 2}` for every `t > 0`, then `N(Λ) ≤ e · C · Λ^{d / 2}` for every `Λ > 0`. -/
theorem weyl_upper_bound_all (D : DiscreteSpectrum ι) {C d : ℝ}
    (hZsum : ∀ t > 0, D.HeatSummable t)
    (hZ : ∀ t > 0, D.heatTrace t ≤ C * t ^ (-(d / 2))) :
    ∀ Λ > 0, D.specCount Λ ≤ Real.exp 1 * C * Λ ^ (d / 2) := fun Λ hΛ =>
  D.weyl_upper_bound hΛ (hZsum (1 / Λ) (one_div_pos.mpr hΛ)) (hZ (1 / Λ) (one_div_pos.mpr hΛ))

/-- **Exponent-Optimized Weyl-Law Upper Bound (`t = α / Λ`)**:
if `Z(α / Λ) ≤ C · (α / Λ)^{-α}` (`α > 0`), then `N(Λ) ≤ (e / α)^α · C · Λ^α`. -/
theorem weyl_upper_bound_optimal (D : DiscreteSpectrum ι) {C α Λ : ℝ} (hα : 0 < α) (hΛ : 0 < Λ)
    (hZsum : D.HeatSummable (α / Λ))
    (hZ : D.heatTrace (α / Λ) ≤ C * (α / Λ) ^ (-α)) :
    D.specCount Λ ≤ (Real.exp 1 / α) ^ α * C * Λ ^ α := by
  have hkm := D.specCount_le_exp_mul_heatTrace (div_nonneg hα.le hΛ.le) hZsum Λ
  rw [div_mul_cancel₀ α hΛ.ne'] at hkm
  have hpow : (α / Λ) ^ (-α) = α ^ (-α) * Λ ^ α := by
    rw [Real.div_rpow hα.le hΛ.le, Real.rpow_neg hα.le, Real.rpow_neg hΛ.le, div_inv_eq_mul]
  have hconst : Real.exp α * α ^ (-α) = (Real.exp 1 / α) ^ α := by
    rw [Real.div_rpow (Real.exp_pos 1).le hα.le, ← Real.exp_mul, one_mul,
      Real.rpow_neg hα.le, div_eq_mul_inv]
  calc D.specCount Λ
      ≤ Real.exp α * D.heatTrace (α / Λ) := hkm
    _ ≤ Real.exp α * (C * (α / Λ) ^ (-α)) := mul_le_mul_of_nonneg_left hZ (Real.exp_pos α).le
    _ = (Real.exp α * α ^ (-α)) * C * Λ ^ α := by rw [hpow]; ring
    _ = (Real.exp 1 / α) ^ α * C * Λ ^ α := by rw [hconst]

/-- **Two-Term Heat-Asymptotic Weyl Upper Bound**:
if `Z(t) ≤ C₁ t^{-d/2} + C₂ t^{-(d-1)/2}`, then `N(Λ) ≤ e · (C₁ Λ^{d/2} + C₂ Λ^{(d-1)/2})`. -/
theorem weyl_upper_bound_two_term (D : DiscreteSpectrum ι) {C₁ C₂ d Λ : ℝ} (hΛ : 0 < Λ)
    (hZsum : D.HeatSummable (1 / Λ))
    (hZ : D.heatTrace (1 / Λ) ≤ C₁ * (1 / Λ) ^ (-(d / 2)) + C₂ * (1 / Λ) ^ (-((d - 1) / 2))) :
    D.specCount Λ ≤ Real.exp 1 * (C₁ * Λ ^ (d / 2) + C₂ * Λ ^ ((d - 1) / 2)) := by
  have hpow1 : (1 / Λ) ^ (-(d / 2)) = Λ ^ (d / 2) := by
    rw [one_div, Real.inv_rpow hΛ.le, Real.rpow_neg hΛ.le, inv_inv]
  have hpow2 : (1 / Λ) ^ (-((d - 1) / 2)) = Λ ^ ((d - 1) / 2) := by
    rw [one_div, Real.inv_rpow hΛ.le, Real.rpow_neg hΛ.le, inv_inv]
  rw [hpow1, hpow2] at hZ
  calc D.specCount Λ
      ≤ Real.exp 1 * D.heatTrace (1 / Λ) := D.specCount_le_e_mul_heatTrace_inv hΛ hZsum
    _ ≤ Real.exp 1 * (C₁ * Λ ^ (d / 2) + C₂ * Λ ^ ((d - 1) / 2)) :=
        mul_le_mul_of_nonneg_left hZ (Real.exp_pos 1).le

/-- **Spectral-Gap Exponential Decay of the Infinite Heat Trace**:
if `κ ≤ λ_k` for all `k`, then `Z(t) ≤ exp(-κ (t - t₀)) · Z(t₀)` for all `t₀ ≤ t`. -/
theorem heatTrace_gap_decay (D : DiscreteSpectrum ι) {κ t₀ t : ℝ}
    (hgap : ∀ k, κ ≤ D.eig k) (ht : t₀ ≤ t) (hZ₀ : D.HeatSummable t₀) :
    D.HeatSummable t ∧ D.heatTrace t ≤ Real.exp (-κ * (t - t₀)) * D.heatTrace t₀ := by
  have hsum : D.HeatSummable t := D.heatSummable_of_le ht hZ₀
  refine ⟨hsum, ?_⟩
  unfold heatTrace
  rw [← tsum_mul_left]
  refine hsum.tsum_le_tsum ?_ (hZ₀.mul_left _)
  intro k
  have hexp : Real.exp (-t * D.eig k) ≤ Real.exp (-κ * (t - t₀)) * Real.exp (-t₀ * D.eig k) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hgap k])
  have hmul := mul_le_mul_of_nonneg_left hexp (D.mult_nonneg k)
  linarith

/-- Shifted spectrum `λ'_k = λ_k + c` (`c ≥ 0`), modeling Capelli / Harish-Chandra eigenvalue shifts. -/
def shift (D : DiscreteSpectrum ι) (c : ℝ) (hc : 0 ≤ c) : DiscreteSpectrum ι where
  eig := fun k => D.eig k + c
  mult := D.mult
  eig_nonneg := fun k => add_nonneg (D.eig_nonneg k) hc
  mult_nonneg := D.mult_nonneg

theorem specCount_shift (D : DiscreteSpectrum ι) {c : ℝ} (hc : 0 ≤ c) (Λ : ℝ) :
    (D.shift c hc).specCount Λ = D.specCount (Λ - c) := by
  unfold specCount shift
  congr 1; funext k
  by_cases h : D.eig k + c ≤ Λ
  · have h' : D.eig k ≤ Λ - c := by linarith
    simp [h, h']
  · have h' : ¬ D.eig k ≤ Λ - c := by linarith
    simp [h, h']

theorem heatTrace_shift (D : DiscreteSpectrum ι) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    (D.shift c hc).heatTrace t = Real.exp (-t * c) * D.heatTrace t := by
  unfold heatTrace shift
  rw [← tsum_mul_left]
  congr 1; funext k
  have hexp : Real.exp (-t * (D.eig k + c)) = Real.exp (-t * c) * Real.exp (-t * D.eig k) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]; ring

end DiscreteSpectrum

/-! ## Section 2: Spectral Window Localization via Gaussian, Smooth & Lorentzian Wave Kernels -/

section WaveKernelLocalization

variable {ι : Type*}

/-- Finite short-interval spectral window count `W_S(Λ, σ) = ∑_{k ∈ S, |λ_k - Λ| ≤ σ} m_k`. -/
def windowCountFin (eig mult : ι → ℝ) (S : Finset ι) (Λ σ : ℝ) : ℝ :=
  ∑ k ∈ S.filter (fun k => |eig k - Λ| ≤ σ), mult k

/-- Finite Gaussian wave-smoothed spectral trace
`G_S(Λ, σ) = ∑_{k ∈ S} m_k exp(-(λ_k - Λ)² / (2 σ²))`. -/
def gaussWaveTraceFin (eig mult : ι → ℝ) (S : Finset ι) (Λ σ : ℝ) : ℝ :=
  ∑ k ∈ S, mult k * Real.exp (-(eig k - Λ) ^ 2 / (2 * σ ^ 2))

/-- Finite Lorentzian / resolvent-trace wave smoothing
`L_S(Λ, σ) = ∑_{k ∈ S} m_k · σ² / ((λ_k - Λ)² + σ²)`. -/
def lorentzWaveTraceFin (eig mult : ι → ℝ) (S : Finset ι) (Λ σ : ℝ) : ℝ :=
  ∑ k ∈ S, mult k * (σ ^ 2 / ((eig k - Λ) ^ 2 + σ ^ 2))

/-- Pointwise Gaussian lower bound inside the window `|x - Λ| ≤ σ`:
`exp(-1/2) ≤ exp(-(x - Λ)² / (2 σ²))`. -/
lemma exp_neg_half_le_gauss_of_abs_le {x Λ σ : ℝ} (hσ : 0 < σ) (h : |x - Λ| ≤ σ) :
    Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(x - Λ) ^ 2 / (2 * σ ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have hsq : (x - Λ) ^ 2 ≤ σ ^ 2 := by
    rw [← sq_abs (x - Λ)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hden : 0 < 2 * σ ^ 2 := by positivity
  rw [neg_div, neg_le_neg_iff, div_le_iff₀ hden]
  linarith

/-- **Exact Finite Gaussian Wave-Kernel Localization Lower Bound**:
`e^{-1/2} · W_S(Λ, σ) ≤ ∑_{k ∈ S} m_k exp(-(λ_k - Λ)² / (2 σ²))`. -/
theorem gaussWaveTraceFin_ge_exp_neg_half_mul_windowCountFin {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {Λ σ : ℝ} (hσ : 0 < σ) :
    Real.exp (-(1 / 2 : ℝ)) * windowCountFin eig mult S Λ σ ≤
      gaussWaveTraceFin eig mult S Λ σ := by
  unfold windowCountFin gaussWaveTraceFin
  rw [Finset.mul_sum]
  have hsub :
      ∑ k ∈ S.filter (fun k => |eig k - Λ| ≤ σ), Real.exp (-(1 / 2 : ℝ)) * mult k ≤
        ∑ k ∈ S.filter (fun k => |eig k - Λ| ≤ σ),
          mult k * Real.exp (-(eig k - Λ) ^ 2 / (2 * σ ^ 2)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have ⟨hkS, hwin⟩ := Finset.mem_filter.mp hk
    rw [mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left (exp_neg_half_le_gauss_of_abs_le hσ hwin) (hm k hkS)
  refine hsub.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) ?_)
  intro k hk _
  exact mul_nonneg (hm k hk) (Real.exp_pos _).le

/-- **Short-Interval Multiplicity Upper Bound from Gaussian Wave Trace**:
`W_S(Λ, σ) ≤ e^{1/2} · G_S(Λ, σ)`. -/
theorem windowCountFin_le_exp_half_mul_gaussWaveTraceFin {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {Λ σ : ℝ} (hσ : 0 < σ) :
    windowCountFin eig mult S Λ σ ≤
      Real.exp (1 / 2 : ℝ) * gaussWaveTraceFin eig mult S Λ σ := by
  have h := gaussWaveTraceFin_ge_exp_neg_half_mul_windowCountFin (eig := eig) (Λ := Λ) hm hσ
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (1 / 2 : ℝ)).le
  have hcancel : Real.exp (1 / 2 : ℝ) * (Real.exp (-(1 / 2 : ℝ)) * windowCountFin eig mult S Λ σ) =
      windowCountFin eig mult S Λ σ := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  linarith

/-- **Cardinality Form of Gaussian Wave-Kernel Localization**:
`e^{-1/2} · #{k ∈ S : |λ_k - Λ| ≤ σ} ≤ ∑_{k ∈ S} exp(-(λ_k - Λ)² / (2 σ²))`. -/
theorem card_window_le_exp_half_mul_gauss_sum (eig : ι → ℝ) (S : Finset ι) {Λ σ : ℝ}
    (hσ : 0 < σ) :
    Real.exp (-(1 / 2 : ℝ)) * ((S.filter (fun k => |eig k - Λ| ≤ σ)).card : ℝ) ≤
      ∑ k ∈ S, Real.exp (-(eig k - Λ) ^ 2 / (2 * σ ^ 2)) := by
  have h := gaussWaveTraceFin_ge_exp_neg_half_mul_windowCountFin
    (eig := eig) (mult := fun _ => (1 : ℝ)) (S := S) (Λ := Λ) (fun _ _ => zero_le_one) hσ
  simpa [windowCountFin, gaussWaveTraceFin] using h

/-- **General Non-Negative Wave-Kernel Localization (Finite)**:
for any kernel `K : ℝ → ℝ` with `K ≥ 0` everywhere and `c ≤ K(u)` on `|u| ≤ 1`,
`c · W_S(Λ, σ) ≤ ∑_{k ∈ S} m_k K((λ_k - Λ) / σ)`. -/
theorem waveKernel_localization_fin {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) {K : ℝ → ℝ} {c Λ σ : ℝ} (hσ : 0 < σ)
    (hKnn : ∀ u, 0 ≤ K u) (hKwin : ∀ u, |u| ≤ 1 → c ≤ K u) :
    c * windowCountFin eig mult S Λ σ ≤
      ∑ k ∈ S, mult k * K ((eig k - Λ) / σ) := by
  unfold windowCountFin
  rw [Finset.mul_sum]
  have hsub :
      ∑ k ∈ S.filter (fun k => |eig k - Λ| ≤ σ), c * mult k ≤
        ∑ k ∈ S.filter (fun k => |eig k - Λ| ≤ σ), mult k * K ((eig k - Λ) / σ) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have ⟨hkS, hwin⟩ := Finset.mem_filter.mp hk
    have hu : |(eig k - Λ) / σ| ≤ 1 := by
      rw [abs_div, abs_of_pos hσ, div_le_one hσ]
      exact hwin
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hKwin _ hu) (hm k hkS)
  refine hsub.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) ?_)
  intro k hk _
  exact mul_nonneg (hm k hk) (hKnn _)

/-- **Short-Interval Covering Multiplicity Bound**:
partitioning `[A, A + 2 N σ]` into `N` windows of half-width `σ` bounds the interval spectral
count by `e^{1/2}` times the sum of `N` centered Gaussian wave traces. -/
theorem intervalCountFin_le_sum_windows {eig mult : ι → ℝ} {S : Finset ι}
    (hm : ∀ k ∈ S, 0 ≤ mult k) (A : ℝ) {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ S.filter (fun k => A ≤ eig k ∧ eig k ≤ A + 2 * (N : ℝ) * σ), mult k ≤
      Real.exp (1 / 2 : ℝ) *
        ∑ j ∈ Finset.range N, gaussWaveTraceFin eig mult S (A + (2 * (j : ℝ) + 1) * σ) σ := by
  have hcov :
      ∑ k ∈ S.filter (fun k => A ≤ eig k ∧ eig k ≤ A + 2 * (N : ℝ) * σ), mult k ≤
        ∑ j ∈ Finset.range N, windowCountFin eig mult S (A + (2 * (j : ℝ) + 1) * σ) σ := by
    unfold windowCountFin
    rw [Finset.sum_filter]
    have hrhs :
        ∑ j ∈ Finset.range N,
          ∑ k ∈ S.filter (fun k => |eig k - (A + (2 * (j : ℝ) + 1) * σ)| ≤ σ), mult k =
        ∑ k ∈ S, ∑ j ∈ Finset.range N,
          if |eig k - (A + (2 * (j : ℝ) + 1) * σ)| ≤ σ then mult k else 0 := by
      simp_rw [Finset.sum_filter]
      exact Finset.sum_comm
    rw [hrhs]
    refine Finset.sum_le_sum fun k hk => ?_
    split_ifs with hI
    · have hpos2σ : 0 < 2 * σ := by linarith
      let idx : ℕ := min (N - 1) ⌊(eig k - A) / (2 * σ)⌋₊
      have hidx_lt : idx ∈ Finset.range N := by
        rw [Finset.mem_range]
        have : idx ≤ N - 1 := min_le_left _ _
        omega
      have hwin : |eig k - (A + (2 * (idx : ℝ) + 1) * σ)| ≤ σ := by
        have hq_nn : 0 ≤ (eig k - A) / (2 * σ) := div_nonneg (by linarith [hI.1]) hpos2σ.le
        have hq_le : (eig k - A) / (2 * σ) ≤ (N : ℝ) := by
          rw [div_le_iff₀ hpos2σ]; linarith [hI.2]
        by_cases hlt : ⌊(eig k - A) / (2 * σ)⌋₊ ≤ N - 1
        · have hidx_eq : idx = ⌊(eig k - A) / (2 * σ)⌋₊ := min_eq_right hlt
          rw [hidx_eq]
          have hfl1 : (⌊(eig k - A) / (2 * σ)⌋₊ : ℝ) ≤ (eig k - A) / (2 * σ) :=
            Nat.floor_le hq_nn
          have hfl2 : (eig k - A) / (2 * σ) < (⌊(eig k - A) / (2 * σ)⌋₊ : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          rw [le_div_iff₀ hpos2σ] at hfl1
          rw [div_lt_iff₀ hpos2σ] at hfl2
          rw [abs_le]
          constructor <;> linarith
        · have hgt : N ≤ ⌊(eig k - A) / (2 * σ)⌋₊ := by omega
          have hidx_eq : idx = N - 1 := min_eq_left (by omega)
          rw [hidx_eq]
          have hfl : (N : ℝ) ≤ (eig k - A) / (2 * σ) :=
            le_trans (by exact_mod_cast hgt) (Nat.floor_le hq_nn)
          rw [le_div_iff₀ hpos2σ] at hfl
          have hNcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            rw [Nat.cast_sub (Nat.succ_le_of_lt hN), Nat.cast_one]
          rw [hNcast, abs_le]
          constructor <;> linarith [hI.2]
      calc mult k
          = (if |eig k - (A + (2 * (idx : ℝ) + 1) * σ)| ≤ σ then mult k else 0) := by
              rw [if_pos hwin]
        _ ≤ ∑ j ∈ Finset.range N,
              if |eig k - (A + (2 * (j : ℝ) + 1) * σ)| ≤ σ then mult k else 0 :=
            Finset.single_le_sum
              (f := fun j : ℕ => if |eig k - (A + (2 * (j : ℝ) + 1) * σ)| ≤ σ then mult k else 0)
              (fun j _ => by split_ifs <;> [exact hm k hk; exact le_rfl]) hidx_lt
    · exact Finset.sum_nonneg fun j _ => by split_ifs <;> [exact hm k hk; exact le_rfl]
  calc ∑ k ∈ S.filter (fun k => A ≤ eig k ∧ eig k ≤ A + 2 * (N : ℝ) * σ), mult k
      ≤ ∑ j ∈ Finset.range N, windowCountFin eig mult S (A + (2 * (j : ℝ) + 1) * σ) σ := hcov
    _ ≤ ∑ j ∈ Finset.range N,
          Real.exp (1 / 2 : ℝ) * gaussWaveTraceFin eig mult S (A + (2 * (j : ℝ) + 1) * σ) σ :=
        Finset.sum_le_sum fun j _ => windowCountFin_le_exp_half_mul_gaussWaveTraceFin hm hσ
    _ = Real.exp (1 / 2 : ℝ) *
          ∑ j ∈ Finset.range N, gaussWaveTraceFin eig mult S (A + (2 * (j : ℝ) + 1) * σ) σ :=
        (Finset.mul_sum _ _ _).symm

end WaveKernelLocalization

/-! ### Infinite Wave-Kernel Localization & Completing-the-Square Heat-Trace Comparison -/

namespace DiscreteSpectrum

variable {ι : Type*}

/-- Infinite short-interval spectral window count `W(Λ, σ) = ∑'_{|λ_k - Λ| ≤ σ} m_k`. -/
def windowCount (D : DiscreteSpectrum ι) (Λ σ : ℝ) : ℝ :=
  ∑' k : ι, if |D.eig k - Λ| ≤ σ then D.mult k else 0

/-- Infinite Gaussian wave-smoothed spectral trace
`G(Λ, σ) = ∑'_k m_k exp(-(λ_k - Λ)² / (2 σ²))`. -/
def gaussWaveTrace (D : DiscreteSpectrum ι) (Λ σ : ℝ) : ℝ :=
  ∑' k : ι, D.mult k * Real.exp (-(D.eig k - Λ) ^ 2 / (2 * σ ^ 2))

/-- Infinite Lorentzian / resolvent-trace wave smoothing
`L(Λ, σ) = ∑'_k m_k · σ² / ((λ_k - Λ)² + σ²)`. -/
def lorentzWaveTrace (D : DiscreteSpectrum ι) (Λ σ : ℝ) : ℝ :=
  ∑' k : ι, D.mult k * (σ ^ 2 / ((D.eig k - Λ) ^ 2 + σ ^ 2))

/-- Summability predicate for the Gaussian wave trace. -/
def GaussSummable (D : DiscreteSpectrum ι) (Λ σ : ℝ) : Prop :=
  Summable fun k : ι => D.mult k * Real.exp (-(D.eig k - Λ) ^ 2 / (2 * σ ^ 2))

/-- Exact completing-the-square inequality relating Gaussian wave smoothing to the heat kernel:
`-(x - Λ)² / (2 σ²) ≤ (t Λ + t² σ² / 2) - t x` for all `x, Λ, t : ℝ` and `σ > 0`. -/
lemma gauss_exp_le_heat_exp (x Λ t : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Real.exp (-(x - Λ) ^ 2 / (2 * σ ^ 2)) ≤
      Real.exp (t * Λ + t ^ 2 * σ ^ 2 / 2) * Real.exp (-t * x) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hden : 0 < 2 * σ ^ 2 := by positivity
  have hsq : 0 ≤ (x - Λ - t * σ ^ 2) ^ 2 / (2 * σ ^ 2) := by positivity
  have hid :
      (t * Λ + t ^ 2 * σ ^ 2 / 2 + -t * x) - (-(x - Λ) ^ 2 / (2 * σ ^ 2)) =
        (x - Λ - t * σ ^ 2) ^ 2 / (2 * σ ^ 2) := by
    field_simp [hσ.ne']
    ring
  linarith

/-- **Gaussian-to-Heat-Trace Comparison (Automatic Summability + Explicit Bound)**:
if the heat trace converges at `t`, then the Gaussian wave trace converges at EVERY center `Λ`
and EVERY bandwidth `σ > 0`, and satisfies
`G(Λ, σ) ≤ exp(t Λ + t² σ² / 2) · Z(t)`. -/
theorem gaussWaveTrace_le_heatTrace (D : DiscreteSpectrum ι) (Λ t : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hZ : D.HeatSummable t) :
    D.GaussSummable Λ σ ∧
      D.gaussWaveTrace Λ σ ≤ Real.exp (t * Λ + t ^ 2 * σ ^ 2 / 2) * D.heatTrace t := by
  have hdom : ∀ k : ι,
      D.mult k * Real.exp (-(D.eig k - Λ) ^ 2 / (2 * σ ^ 2)) ≤
        Real.exp (t * Λ + t ^ 2 * σ ^ 2 / 2) * (D.mult k * Real.exp (-t * D.eig k)) := by
    intro k
    have hmul := mul_le_mul_of_nonneg_left (gauss_exp_le_heat_exp (D.eig k) Λ t hσ) (D.mult_nonneg k)
    linarith
  have hGsum : D.GaussSummable Λ σ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (D.mult_nonneg k) (Real.exp_pos _).le)
      hdom (hZ.mul_left _)
  refine ⟨hGsum, ?_⟩
  unfold gaussWaveTrace heatTrace
  rw [← tsum_mul_left]
  exact hGsum.tsum_le_tsum hdom (hZ.mul_left _)

/-- **Exact Infinite Gaussian Wave-Kernel Localization**:
`e^{-1/2} · W(Λ, σ) ≤ G(Λ, σ)` whenever `D.GaussSummable Λ σ` (with automatic summability of `W`). -/
theorem gaussWaveTrace_ge_exp_neg_half_mul_windowCount (D : DiscreteSpectrum ι)
    {Λ σ : ℝ} (hσ : 0 < σ) (hG : D.GaussSummable Λ σ) :
    Summable (fun k : ι => if |D.eig k - Λ| ≤ σ then D.mult k else 0) ∧
      Real.exp (-(1 / 2 : ℝ)) * D.windowCount Λ σ ≤ D.gaussWaveTrace Λ σ := by
  have hdom : ∀ k : ι,
      Real.exp (-(1 / 2 : ℝ)) * (if |D.eig k - Λ| ≤ σ then D.mult k else 0) ≤
        D.mult k * Real.exp (-(D.eig k - Λ) ^ 2 / (2 * σ ^ 2)) := by
    intro k
    split_ifs with hwin
    · rw [mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_left (exp_neg_half_le_gauss_of_abs_le hσ hwin) (D.mult_nonneg k)
    · rw [mul_zero]
      exact mul_nonneg (D.mult_nonneg k) (Real.exp_pos _).le
  have hWsum_scaled :
      Summable (fun k : ι => Real.exp (-(1 / 2 : ℝ)) * (if |D.eig k - Λ| ≤ σ then D.mult k else 0)) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> [exact D.mult_nonneg k; exact le_rfl]))
      hdom hG
  have hWsum : Summable (fun k : ι => if |D.eig k - Λ| ≤ σ then D.mult k else 0) := by
    have h := hWsum_scaled.mul_left (Real.exp (1 / 2 : ℝ))
    refine h.congr fun k => ?_
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  refine ⟨hWsum, ?_⟩
  unfold windowCount gaussWaveTrace
  rw [← tsum_mul_left]
  exact hWsum_scaled.tsum_le_tsum hdom hG

/-- Short-interval multiplicity upper bound `W(Λ, σ) ≤ e^{1/2} · G(Λ, σ)`. -/
theorem windowCount_le_exp_half_mul_gaussWaveTrace (D : DiscreteSpectrum ι)
    {Λ σ : ℝ} (hσ : 0 < σ) (hG : D.GaussSummable Λ σ) :
    D.windowCount Λ σ ≤ Real.exp (1 / 2 : ℝ) * D.gaussWaveTrace Λ σ := by
  have h := (D.gaussWaveTrace_ge_exp_neg_half_mul_windowCount hσ hG).2
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (1 / 2 : ℝ)).le
  have hcancel : Real.exp (1 / 2 : ℝ) * (Real.exp (-(1 / 2 : ℝ)) * D.windowCount Λ σ) =
      D.windowCount Λ σ := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  linarith

/-- **Heat-Trace Short-Interval Multiplicity Bound**:
`W(Λ, σ) ≤ exp(1/2 + t Λ + t² σ² / 2) · Z(t)` for every `t` with `D.HeatSummable t`. -/
theorem windowCount_le_heatTrace (D : DiscreteSpectrum ι) (Λ t : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hZ : D.HeatSummable t) :
    D.windowCount Λ σ ≤ Real.exp (1 / 2 + t * Λ + t ^ 2 * σ ^ 2 / 2) * D.heatTrace t := by
  obtain ⟨hGsum, hG⟩ := D.gaussWaveTrace_le_heatTrace Λ t hσ hZ
  have hW := D.windowCount_le_exp_half_mul_gaussWaveTrace hσ hGsum
  calc D.windowCount Λ σ
      ≤ Real.exp (1 / 2 : ℝ) * D.gaussWaveTrace Λ σ := hW
    _ ≤ Real.exp (1 / 2 : ℝ) * (Real.exp (t * Λ + t ^ 2 * σ ^ 2 / 2) * D.heatTrace t) :=
        mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
    _ = Real.exp (1 / 2 + t * Λ + t ^ 2 * σ ^ 2 / 2) * D.heatTrace t := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **General Non-Negative Wave-Kernel Localization (Infinite)**:
for any kernel `K : ℝ → ℝ` with `K ≥ 0` and `c ≤ K(u)` (`0 < c`) on `|u| ≤ 1`,
`c · W(Λ, σ) ≤ ∑'_k m_k K((λ_k - Λ) / σ)`. -/
theorem waveKernel_localization (D : DiscreteSpectrum ι) {K : ℝ → ℝ} {c Λ σ : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) (hKnn : ∀ u, 0 ≤ K u) (hKwin : ∀ u, |u| ≤ 1 → c ≤ K u)
    (hKsum : Summable fun k : ι => D.mult k * K ((D.eig k - Λ) / σ)) :
    c * D.windowCount Λ σ ≤ ∑' k : ι, D.mult k * K ((D.eig k - Λ) / σ) := by
  have hdom : ∀ k : ι,
      c * (if |D.eig k - Λ| ≤ σ then D.mult k else 0) ≤
        D.mult k * K ((D.eig k - Λ) / σ) := by
    intro k
    split_ifs with hwin
    · have hu : |(D.eig k - Λ) / σ| ≤ 1 := by
        rw [abs_div, abs_of_pos hσ, div_le_one hσ]
        exact hwin
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left (hKwin _ hu) (D.mult_nonneg k)
    · rw [mul_zero]
      exact mul_nonneg (D.mult_nonneg k) (hKnn _)
  have hWsum_scaled :
      Summable (fun k : ι => c * (if |D.eig k - Λ| ≤ σ then D.mult k else 0)) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg hc.le (by split_ifs <;> [exact D.mult_nonneg k; exact le_rfl]))
      hdom hKsum
  unfold windowCount
  rw [← tsum_mul_left]
  exact hWsum_scaled.tsum_le_tsum hdom hKsum

/-- **Lorentzian / Resolvent-Trace Spectral Window Bound**:
`W(Λ, σ) ≤ 2 · ∑'_k m_k · σ² / ((λ_k - Λ)² + σ²)` (directly bounding short-interval multiplicity
by the imaginary part of the resolvent trace `Im Tr((Δ - (Λ + i σ))⁻¹)`). -/
theorem windowCount_le_two_mul_lorentzWaveTrace (D : DiscreteSpectrum ι) {Λ σ : ℝ} (hσ : 0 < σ)
    (hLsum : Summable fun k : ι => D.mult k * (σ ^ 2 / ((D.eig k - Λ) ^ 2 + σ ^ 2))) :
    D.windowCount Λ σ ≤ 2 * D.lorentzWaveTrace Λ σ := by
  let K : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹
  have hKeq : ∀ k : ι,
      D.mult k * K ((D.eig k - Λ) / σ) = D.mult k * (σ ^ 2 / ((D.eig k - Λ) ^ 2 + σ ^ 2)) := by
    intro k
    dsimp only [K]
    congr 1
    have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
    have hden : (D.eig k - Λ) ^ 2 + σ ^ 2 ≠ 0 := by positivity
    field_simp [hσ2, hden]
    ring
  have hKsum : Summable fun k : ι => D.mult k * K ((D.eig k - Λ) / σ) :=
    hLsum.congr fun k => (hKeq k).symm
  have hloc := D.waveKernel_localization (K := K) (c := (1 / 2 : ℝ)) (by norm_num) hσ
    (fun u => inv_nonneg.mpr (by positivity))
    (fun u hu => by
      dsimp only [K]
      rw [one_div]
      refine inv_anti₀ (by positivity) ?_
      have hsq : u ^ 2 ≤ 1 := by
        rw [← sq_abs u]
        nlinarith [abs_nonneg u]
      linarith)
    hKsum
  have htsum : (∑' k : ι, D.mult k * K ((D.eig k - Λ) / σ)) = D.lorentzWaveTrace Λ σ :=
    tsum_congr hKeq
  rw [htsum] at hloc
  linarith

end DiscreteSpectrum

/-! ## Section 3: Bochner–Kodaira–Nakano Curvature Positivity, Spectral Gap & Resolvent Bounds -/

section AbstractBochnerKodairaNakano

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Bochner–Kodaira–Nakano Energy Identity**:
for `Δ = D* ∘ D + R` where `D*` is a formal adjoint of `D` (`⟪D* v, u⟫ = ⟪v, D u⟫`),
`⟪Δ u, u⟫ = ‖D u‖² + ⟪R u, u⟫`. -/
theorem bochner_energy_identity (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H)
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ) (u : H) :
    ⟪(Dstar ∘ₗ D + R) u, u⟫_ℂ = ((‖D u‖ ^ 2 : ℝ) : ℂ) + ⟪R u, u⟫_ℂ := by
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_left, hadj (D u) u,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

/-- Real part of the Bochner–Kodaira–Nakano energy identity:
`Re ⟪(D* ∘ D + R) u, u⟫ = ‖D u‖² + Re ⟪R u, u⟫`. -/
theorem bochner_energy_re (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H)
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ) (u : H) :
    (⟪(Dstar ∘ₗ D + R) u, u⟫_ℂ).re = ‖D u‖ ^ 2 + (⟪R u, u⟫_ℂ).re := by
  rw [bochner_energy_identity D Dstar R hadj u, Complex.add_re, Complex.ofReal_re]

/-- Symmetry of the Bochner–Kodaira–Nakano Laplacian `Δ = D* ∘ D + R` when `R` is Hermitian. -/
theorem bochner_isSymmetric (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H)
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hRsym : ∀ u v, ⟪R u, v⟫_ℂ = ⟪u, R v⟫_ℂ) :
    ∀ u v : H, ⟪(Dstar ∘ₗ D + R) u, v⟫_ℂ = ⟪u, (Dstar ∘ₗ D + R) v⟫_ℂ := by
  intro u v
  have hadjR : ∀ x y, ⟪x, Dstar y⟫_ℂ = ⟪D x, y⟫_ℂ := fun x y => by
    rw [← inner_conj_symm x (Dstar y), hadj y x, inner_conj_symm]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_left, inner_add_right,
    hadj (D u) v, hadjR u (D v), hRsym u v]

/-- **Bochner–Kodaira–Nakano Curvature Coercivity**:
if `Re ⟪R u, u⟫ ≥ κ ‖u‖²`, then `Re ⟪Δ u, u⟫ ≥ κ ‖u‖²` for every `u ∈ H`. -/
theorem bochner_coercivity (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re) (u : H) :
    κ * ‖u‖ ^ 2 ≤ (⟪(Dstar ∘ₗ D + R) u, u⟫_ℂ).re := by
  rw [bochner_energy_re D Dstar R hadj u]
  linarith [sq_nonneg ‖D u‖, hcurv u]

/-- **Quantitative Norm Coercivity** (`κ ‖u‖ ≤ ‖Δ u‖`):
directly deduced from curvature positivity via Cauchy–Schwarz. -/
theorem bochner_norm_ge (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re) (u : H) :
    κ * ‖u‖ ≤ ‖(Dstar ∘ₗ D + R) u‖ := by
  by_cases hu : u = 0
  · subst hu; simp
  · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have h1 : κ * ‖u‖ ^ 2 ≤ ‖(Dstar ∘ₗ D + R) u‖ * ‖u‖ :=
      calc κ * ‖u‖ ^ 2
          ≤ (⟪(Dstar ∘ₗ D + R) u, u⟫_ℂ).re := bochner_coercivity D Dstar R hadj hcurv u
        _ ≤ ‖⟪(Dstar ∘ₗ D + R) u, u⟫_ℂ‖ := Complex.re_le_norm _
        _ ≤ ‖(Dstar ∘ₗ D + R) u‖ * ‖u‖ := norm_inner_le_norm _ _
    have h2 : κ * ‖u‖ * ‖u‖ ≤ ‖(Dstar ∘ₗ D + R) u‖ * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hu_pos

/-- **Kodaira Vanishing Theorem (`ker Δ = ⊥`)**:
strict curvature positivity `κ > 0` forces the harmonic kernel of `Δ = D* ∘ D + R` to vanish! -/
theorem kodaira_vanishing_ker_eq_bot (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hκ : 0 < κ) (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re) :
    LinearMap.ker (Dstar ∘ₗ D + R) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  have h := bochner_norm_ge D Dstar R hadj hcurv u
  rw [hu, norm_zero] at h
  have h0 : ‖u‖ ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg u))

/-- **Harmonic Rigidity for Semipositive Curvature (`κ = 0`)**:
every harmonic vector `Δ u = 0` under `Re ⟪R u, u⟫ ≥ 0` is `D`-closed (`D u = 0`) and
curvature-flat (`Re ⟪R u, u⟫ = 0`). -/
theorem bochner_harmonic_rigidity_nonneg (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H)
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hcurv : ∀ u : H, 0 ≤ (⟪R u, u⟫_ℂ).re) {u : H} (hu : (Dstar ∘ₗ D + R) u = 0) :
    D u = 0 ∧ (⟪R u, u⟫_ℂ).re = 0 := by
  have he := bochner_energy_re D Dstar R hadj u
  rw [hu, inner_zero_left, Complex.zero_re] at he
  have hDu : ‖D u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖D u‖, hcurv u]
  have hRu : (⟪R u, u⟫_ℂ).re = 0 := by linarith
  exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hDu), hRu⟩

/-- **Strict Spectral Gap (`κ ≤ Re λ`)**:
every eigenvalue `λ ∈ ℂ` of `Δ = D* ∘ D + R` satisfies `κ ≤ λ.re`. -/
theorem bochner_spectral_gap (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re)
    {μ : ℂ} {u : H} (hu : u ≠ 0) (heig : (Dstar ∘ₗ D + R) u = μ • u) :
    κ ≤ μ.re := by
  have hcoerc := bochner_coercivity D Dstar R hadj hcurv u
  rw [heig, inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.conj_re] at hcoerc
  have hu2 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  exact le_of_mul_le_mul_right hcoerc hu2

/-- **Real Strict Spectral Gap for Symmetric Curvature (`λ ∈ [κ, ∞)`)**:
when `R` is symmetric, every eigenvalue `μ ∈ ℂ` of `Δ = D* ∘ D + R` is purely real (`μ.im = 0`)
and satisfies `κ ≤ μ.re`. -/
theorem bochner_spectral_gap_symmetric (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hRsym : ∀ u v, ⟪R u, v⟫_ℂ = ⟪u, R v⟫_ℂ)
    (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re)
    {μ : ℂ} {u : H} (hu : u ≠ 0) (heig : (Dstar ∘ₗ D + R) u = μ • u) :
    μ.im = 0 ∧ κ ≤ μ.re := by
  refine ⟨?_, bochner_spectral_gap D Dstar R hadj hcurv hu heig⟩
  have hsym := bochner_isSymmetric D Dstar R hadj hRsym u u
  rw [heig, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at hsym
  have him := congrArg Complex.im hsym
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    Complex.conj_im] at him
  have hu2 : ‖u‖ ^ 2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hu)).ne'
  have hneg : -μ.im = μ.im := mul_right_cancel₀ hu2 (by linarith)
  linarith

/-- **Sharp Distance-to-Spectrum Shifted Resolvent Coercivity**:
for symmetric curvature `R ≥ κ I` and ANY complex spectral parameter `z ∈ ℂ`,
`√(max(κ - Re z, 0)² + (Im z)²) · ‖u‖ ≤ ‖(Δ - z I) u‖`. -/
theorem bochner_shifted_coercivity (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hRsym : ∀ u v, ⟪R u, v⟫_ℂ = ⟪u, R v⟫_ℂ)
    (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re) (z : ℂ) (u : H) :
    Real.sqrt (max (κ - z.re) 0 ^ 2 + z.im ^ 2) * ‖u‖ ≤
      ‖((Dstar ∘ₗ D + R) - z • (LinearMap.id : H →ₗ[ℂ] H)) u‖ := by
  by_cases hu : u = 0
  · subst hu; simp
  · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hu2 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg ‖u‖
    set Δ : H →ₗ[ℂ] H := Dstar ∘ₗ D + R
    set Δz : H →ₗ[ℂ] H := Δ - z • (LinearMap.id : H →ₗ[ℂ] H)
    have hΔsym : ⟪Δ u, u⟫_ℂ = ⟪u, Δ u⟫_ℂ := bochner_isSymmetric D Dstar R hadj hRsym u u
    have hΔim : (⟪Δ u, u⟫_ℂ).im = 0 := by
      have hconj := inner_conj_symm (𝕜 := ℂ) (Δ u) u
      rw [← hΔsym] at hconj
      have him := congrArg Complex.im hconj
      rw [Complex.conj_im] at him
      linarith
    have hΔre : κ * ‖u‖ ^ 2 ≤ (⟪Δ u, u⟫_ℂ).re := bochner_coercivity D Dstar R hadj hcurv u
    have hinner : ⟪Δz u, u⟫_ℂ =
        ⟪Δ u, u⟫_ℂ - starRingEnd ℂ z * ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Δz, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_left,
        inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
        Complex.ofReal_pow]
    have hre_val : (⟪Δz u, u⟫_ℂ).re = (⟪Δ u, u⟫_ℂ).re - z.re * ‖u‖ ^ 2 := by
      rw [hinner, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    have him_val : (⟪Δz u, u⟫_ℂ).im = z.im * ‖u‖ ^ 2 := by
      rw [hinner, Complex.sub_im, hΔim, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
      ring
    have hre_ge : max (κ - z.re) 0 * ‖u‖ ^ 2 ≤ |(⟪Δz u, u⟫_ℂ).re| := by
      rw [hre_val]
      rcases le_total (κ - z.re) 0 with hle | hge
      · rw [max_eq_right hle, zero_mul]
        exact abs_nonneg _
      · rw [max_eq_left hge]
        have hpos : 0 ≤ (⟪Δ u, u⟫_ℂ).re - z.re * ‖u‖ ^ 2 := by nlinarith
        rw [abs_of_nonneg hpos]
        nlinarith
    have hnorm_sq :
        (max (κ - z.re) 0 ^ 2 + z.im ^ 2) * (‖u‖ ^ 2) ^ 2 ≤
          ‖⟪Δz u, u⟫_ℂ‖ ^ 2 := by
      have hre_sq : (max (κ - z.re) 0 * ‖u‖ ^ 2) ^ 2 ≤
          (⟪Δz u, u⟫_ℂ).re ^ 2 := by
        have h := pow_le_pow_left₀ (mul_nonneg (le_max_right _ _) hu2) hre_ge 2
        rwa [sq_abs] at h
      have hCsq : ‖⟪Δz u, u⟫_ℂ‖ ^ 2 =
          (⟪Δz u, u⟫_ℂ).re ^ 2 + (⟪Δz u, u⟫_ℂ).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      rw [hCsq, him_val]
      nlinarith [hre_sq]
    have hcs : ‖⟪Δz u, u⟫_ℂ‖ ≤ ‖Δz u‖ * ‖u‖ := norm_inner_le_norm _ _
    have hsqrt_le :
        Real.sqrt (max (κ - z.re) 0 ^ 2 + z.im ^ 2) * ‖u‖ ^ 2 ≤ ‖Δz u‖ * ‖u‖ := by
      calc Real.sqrt (max (κ - z.re) 0 ^ 2 + z.im ^ 2) * ‖u‖ ^ 2
          = Real.sqrt ((max (κ - z.re) 0 ^ 2 + z.im ^ 2) * (‖u‖ ^ 2) ^ 2) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu2]
        _ ≤ Real.sqrt (‖⟪Δz u, u⟫_ℂ‖ ^ 2) := Real.sqrt_le_sqrt hnorm_sq
        _ = ‖⟪Δz u, u⟫_ℂ‖ := Real.sqrt_sq (norm_nonneg _)
        _ ≤ ‖Δz u‖ * ‖u‖ := hcs
    have hmul : (Real.sqrt (max (κ - z.re) 0 ^ 2 + z.im ^ 2) * ‖u‖) * ‖u‖ ≤
        ‖Δz u‖ * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right hmul hu_pos

/-- **Quantitative Resolvent Operator-Norm Bound (`‖Δ⁻¹‖ ≤ κ⁻¹`)**:
any continuous right inverse `G : H →L[ℂ] H` of `Δ = D* ∘ D + R` satisfies `‖G‖ ≤ κ⁻¹`. -/
theorem bochner_resolvent_norm_le (D : H →ₗ[ℂ] K) (Dstar : K →ₗ[ℂ] H) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hadj : ∀ v u, ⟪Dstar v, u⟫_ℂ = ⟪v, D u⟫_ℂ)
    (hκ : 0 < κ) (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re)
    (G : H →L[ℂ] H) (hinv : ∀ v : H, (Dstar ∘ₗ D + R) (G v) = v) :
    ‖G‖ ≤ κ⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound G (inv_nonneg.mpr hκ.le) fun v => ?_
  have h := bochner_norm_ge D Dstar R hadj hcurv (G v)
  rw [hinv v] at h
  have h1 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hκ.le)
  rw [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul] at h1
  exact h1

/-- **Complete Finite-Dimensional Bochner–Kodaira–Nakano Theorem**:
on any finite-dimensional complex inner product space `H`, `Δ = D* ∘ D + R` with curvature
`Re ⟪R u, u⟫ ≥ κ ‖u‖²` (`κ > 0`) satisfies:
1. Kodaira vanishing `ker Δ = ⊥`,
2. Strict spectral gap `κ ≤ Re λ` for every eigenvalue (and `Im λ = 0` when `R` is symmetric),
3. Invertibility with continuous linear resolvent `G = Δ⁻¹ : H →L[ℂ] H` satisfying `‖G‖ ≤ κ⁻¹`! -/
theorem bochner_finDim_complete [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]
    (D : H →ₗ[ℂ] K) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hκ : 0 < κ) (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re) :
    let Δ : H →ₗ[ℂ] H := LinearMap.adjoint D ∘ₗ D + R
    LinearMap.ker Δ = ⊥ ∧
    (∀ (μ : ℂ) (u : H), u ≠ 0 → Δ u = μ • u → κ ≤ μ.re) ∧
    ∃ G : H →L[ℂ] H, (∀ v, Δ (G v) = v) ∧ (∀ u, G (Δ u) = u) ∧ ‖G‖ ≤ κ⁻¹ := by
  intro Δ
  have hadj : ∀ v u, ⟪LinearMap.adjoint D v, u⟫_ℂ = ⟪v, D u⟫_ℂ := fun v u =>
    LinearMap.adjoint_inner_left D u v
  have hker : LinearMap.ker Δ = ⊥ := kodaira_vanishing_ker_eq_bot D (LinearMap.adjoint D) R hadj hκ hcurv
  have hinj : Function.Injective Δ := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective Δ := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e : H ≃ₗ[ℂ] H := LinearEquiv.ofBijective Δ hbij
  let G : H →L[ℂ] H := e.symm.toLinearMap.toContinuousLinearMap
  have hright : ∀ v : H, Δ (G v) = v := fun v => e.apply_symm_apply v
  have hleft : ∀ u : H, G (Δ u) = u := fun u => e.symm_apply_apply u
  refine ⟨hker,
    fun μ u hu heig => bochner_spectral_gap D (LinearMap.adjoint D) R hadj hcurv hu heig,
    G, hright, hleft,
    bochner_resolvent_norm_le D (LinearMap.adjoint D) R hadj hκ hcurv G hright⟩

/-- **Finite-Dimensional Shifted Resolvent Norm Bound**:
for symmetric curvature `R ≥ κ I` and any `z ∈ ℂ` outside `[κ, ∞)` (i.e., `z.re < κ ∨ z.im ≠ 0`),
`(Δ - z I)⁻¹` exists as a continuous linear map with
`‖(Δ - z I)⁻¹‖ ≤ (√(max(κ - Re z, 0)² + (Im z)²))⁻¹`. -/
theorem bochner_finDim_shifted_resolvent [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]
    (D : H →ₗ[ℂ] K) (R : H →ₗ[ℂ] H) {κ : ℝ}
    (hRsym : ∀ u v, ⟪R u, v⟫_ℂ = ⟪u, R v⟫_ℂ)
    (hcurv : ∀ u : H, κ * ‖u‖ ^ 2 ≤ (⟪R u, u⟫_ℂ).re)
    (z : ℂ) (hz : z.re < κ ∨ z.im ≠ 0) :
    let Δz : H →ₗ[ℂ] H := (LinearMap.adjoint D ∘ₗ D + R) - z • LinearMap.id
    let dist : ℝ := Real.sqrt (max (κ - z.re) 0 ^ 2 + z.im ^ 2)
    0 < dist ∧ ∃ Rz : H →L[ℂ] H, (∀ v, Δz (Rz v) = v) ∧ (∀ u, Rz (Δz u) = u) ∧ ‖Rz‖ ≤ dist⁻¹ := by
  intro Δz dist
  have hadj : ∀ v u, ⟪LinearMap.adjoint D v, u⟫_ℂ = ⟪v, D u⟫_ℂ := fun v u =>
    LinearMap.adjoint_inner_left D u v
  have hdist_pos : 0 < dist := by
    refine Real.sqrt_pos.mpr ?_
    rcases hz with hlt | him
    · have h1 : 0 < max (κ - z.re) 0 := lt_of_lt_of_le (sub_pos.mpr hlt) (le_max_left _ _)
      nlinarith [sq_pos_of_pos h1, sq_nonneg z.im]
    · have h2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
      nlinarith [sq_nonneg (max (κ - z.re) 0)]
  have hcoerc : ∀ u : H, dist * ‖u‖ ≤ ‖Δz u‖ :=
    bochner_shifted_coercivity D (LinearMap.adjoint D) R hadj hRsym hcurv z
  have hinj : Function.Injective Δz := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h := hcoerc u
    rw [hu, norm_zero] at h
    have h0 : ‖u‖ ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg u))
  have hbij : Function.Bijective Δz := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e : H ≃ₗ[ℂ] H := LinearEquiv.ofBijective Δz hbij
  let Rz : H →L[ℂ] H := e.symm.toLinearMap.toContinuousLinearMap
  have hright : ∀ v : H, Δz (Rz v) = v := fun v => e.apply_symm_apply v
  have hleft : ∀ u : H, Rz (Δz u) = u := fun u => e.symm_apply_apply u
  have hnorm : ‖Rz‖ ≤ dist⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound Rz (inv_nonneg.mpr hdist_pos.le) fun v => ?_
    have h := hcoerc (Rz v)
    rw [hright v] at h
    have h1 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hdist_pos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hdist_pos.ne', one_mul] at h1
    exact h1
  exact ⟨hdist_pos, Rz, hright, hleft, hnorm⟩

end AbstractBochnerKodairaNakano

/-! ### Hermitian Matrix Bochner Laplacian & `HermitianCurvatureCore` Transfer -/

section MatrixBochnerCurvature

/-- Matrix Bochner–Kodaira–Nakano Laplacian `Δ = Dᴴ * D + R`. -/
def bochnerMatrix {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) : Matrix n n ℂ :=
  Dᴴ * D + R

theorem bochnerMatrix_sub_kappa_posSemidef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ}
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (bochnerMatrix D R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have heq : bochnerMatrix D R - (κ : ℂ) • (1 : Matrix n n ℂ) =
      Dᴴ * D + (R - (κ : ℂ) • (1 : Matrix n n ℂ)) := by
    unfold bochnerMatrix; abel
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self D).add hR

/-- Matrix Bochner positivity: `(R - κ I).PosSemidef` with `κ > 0` implies `(Dᴴ D + R).PosDef`. -/
theorem bochnerMatrix_posDef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (bochnerMatrix D R).PosDef := by
  have hsub := bochnerMatrix_sub_kappa_posSemidef D R hR
  have hκI : ((κ : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
    have h1 : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
    simpa [Complex.real_smul] using h1.smul hκ
  have heq : bochnerMatrix D R =
      (κ : ℂ) • (1 : Matrix n n ℂ) + (bochnerMatrix D R - (κ : ℂ) • (1 : Matrix n n ℂ)) := by
    abel
  rw [heq]
  exact hκI.add_posSemidef hsub

theorem bochnerMatrix_isHermitian {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ}
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (bochnerMatrix D R).IsHermitian := by
  have hsub := (bochnerMatrix_sub_kappa_posSemidef D R hR).isHermitian
  have hκI : ((κ : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  have heq : bochnerMatrix D R =
      (bochnerMatrix D R - (κ : ℂ) • (1 : Matrix n n ℂ)) + (κ : ℂ) • (1 : Matrix n n ℂ) := by
    abel
  rw [heq]
  exact hsub.add hκI

/-- Matrix Kodaira Vanishing (`det(Dᴴ D + R) ≠ 0`). -/
theorem bochnerMatrix_det_ne_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (bochnerMatrix D R).det ≠ 0 := by
  have hpd := bochnerMatrix_posDef D R hκ hR
  have hpos := hpd.det_pos
  exact fun h0 => by rw [h0] at hpos; exact lt_irrefl 0 hpos

/-- Helper: Euclidean inner product of `Matrix.toEuclideanLin A u` with `u` agrees with
`star u.ofLp ⬝ᵥ A *ᵥ u.ofLp` in real part. -/
private lemma toEuclideanLin_re_inner_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) :
    (⟪u, Matrix.toEuclideanLin A u⟫_ℂ).re = (star u.ofLp ⬝ᵥ A.mulVec u.ofLp).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have heq : (Matrix.toEuclideanLin A u).ofLp ⬝ᵥ star u.ofLp =
      star u.ofLp ⬝ᵥ A.mulVec u.ofLp := by
    rw [dotProduct_comm]
    rfl
  rw [heq]

/-- Helper: for a Hermitian matrix `A`, `Re ⟪toEuclideanLin A u, u⟫ = Re (star u ⬝ᵥ A *ᵥ u)`. -/
private lemma toEuclideanLin_re_inner_left_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) :
    (⟪Matrix.toEuclideanLin A u, u⟫_ℂ).re = (star u.ofLp ⬝ᵥ A.mulVec u.ofLp).re := by
  rw [← inner_conj_symm (Matrix.toEuclideanLin A u) u, Complex.conj_re,
    toEuclideanLin_re_inner_eq]

/-- Helper: `star u.ofLp ⬝ᵥ u.ofLp = ‖u‖²`. -/
private lemma re_star_dotProduct_self {n : Type*} [Fintype n] (u : EuclideanSpace ℂ n) :
    (star u.ofLp ⬝ᵥ u.ofLp).re = ‖u‖ ^ 2 := by
  have h := EuclideanSpace.inner_eq_star_dotProduct u u
  rw [dotProduct_comm] at h
  have hre := congrArg Complex.re h
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    Complex.ofReal_re] at hre
  exact hre.symm

/-- **Hermitian Matrix Curvature Positivity → Euclidean Coercivity**:
uses `HermitianCurvatureCore.hermitian_quad_le_of_posSemidef_sub` directly! -/
theorem bochnerMatrix_euclidean_coercivity {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ}
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (u : EuclideanSpace ℂ n) :
    κ * ‖u‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin (bochnerMatrix D R) u, u⟫_ℂ).re := by
  have hsub := bochnerMatrix_sub_kappa_posSemidef D R hR
  have hle := HermitianCurvatureCore.hermitian_quad_le_of_posSemidef_sub hsub u.ofLp
  rw [toEuclideanLin_re_inner_left_eq]
  have hκ : (star u.ofLp ⬝ᵥ ((κ : ℂ) • (1 : Matrix n n ℂ)).mulVec u.ofLp).re = κ * ‖u‖ ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.re_ofReal_mul, re_star_dotProduct_self]
  linarith

/-- **Strict Matrix Spectral Gap (`∀ i, κ ≤ λ_i`)**:
every eigenvalue of the Hermitian matrix Bochner Laplacian `Δ = Dᴴ * D + R` is `≥ κ`. -/
theorem bochnerMatrix_eigenvalues_ge {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ}
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hH : (bochnerMatrix D R).IsHermitian := bochnerMatrix_isHermitian D R hR) (i : n) :
    κ ≤ hH.eigenvalues i := by
  let v : EuclideanSpace ℂ n := hH.eigenvectorBasis i
  have hv_norm : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have heig : Matrix.toEuclideanLin (bochnerMatrix D R) v = ((hH.eigenvalues i : ℝ) : ℂ) • v := by
    ext j
    have hmul := hH.mulVec_eigenvectorBasis i
    have hj := congrFun hmul j
    simpa [v, Matrix.toLpLin_apply, Pi.smul_apply, smul_eq_mul] using hj
  have hcoerc := bochnerMatrix_euclidean_coercivity D R hR v
  rw [heig, inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, hv_norm, one_pow, Complex.ofReal_one, Complex.conj_ofReal] at hcoerc
  simpa only [mul_one, Complex.ofReal_re] using hcoerc

/-- **Matrix Bochner Resolvent Operator-Norm Bound (`‖(Dᴴ D + R)⁻¹‖ ≤ κ⁻¹`)**:
explicit bound on the Euclidean operator norm of `(bochnerMatrix D R)⁻¹`. -/
theorem bochnerMatrix_resolvent_opNorm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    ‖(Matrix.toEuclideanLin (bochnerMatrix D R)⁻¹).toContinuousLinearMap‖ ≤ κ⁻¹ := by
  have hunit : IsUnit (bochnerMatrix D R).det :=
    isUnit_iff_ne_zero.mpr (bochnerMatrix_det_ne_zero D R hκ hR)
  have hcurv : ∀ u : EuclideanSpace ℂ n,
      κ * ‖u‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin R u, u⟫_ℂ).re := by
    intro u
    have hle := HermitianCurvatureCore.hermitian_quad_le_of_posSemidef_sub hR u.ofLp
    rw [toEuclideanLin_re_inner_left_eq]
    have hκu : (star u.ofLp ⬝ᵥ ((κ : ℂ) • (1 : Matrix n n ℂ)).mulVec u.ofLp).re = κ * ‖u‖ ^ 2 := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
        Complex.re_ofReal_mul, re_star_dotProduct_self]
    linarith
  have hΔeq : LinearMap.adjoint (Matrix.toEuclideanLin D) ∘ₗ Matrix.toEuclideanLin D +
      Matrix.toEuclideanLin R = Matrix.toEuclideanLin (bochnerMatrix D R) := by
    unfold bochnerMatrix
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← Matrix.toLpLin_mul 2 2 2, map_add]
  have hinv : ∀ v : EuclideanSpace ℂ n,
      (LinearMap.adjoint (Matrix.toEuclideanLin D) ∘ₗ Matrix.toEuclideanLin D +
        Matrix.toEuclideanLin R)
        ((Matrix.toEuclideanLin (bochnerMatrix D R)⁻¹).toContinuousLinearMap v) = v := by
    intro v
    rw [hΔeq]
    change (Matrix.toEuclideanLin (bochnerMatrix D R) ∘ₗ
      Matrix.toEuclideanLin (bochnerMatrix D R)⁻¹) v = v
    rw [← Matrix.toLpLin_mul 2 2 2, Matrix.mul_nonsing_inv _ hunit, Matrix.toLpLin_one 2,
      LinearMap.id_apply]
  exact bochner_resolvent_norm_le (Matrix.toEuclideanLin D)
    (LinearMap.adjoint (Matrix.toEuclideanLin D)) (Matrix.toEuclideanLin R)
    (fun v u => LinearMap.adjoint_inner_left (Matrix.toEuclideanLin D) u v) hκ hcurv
    (Matrix.toEuclideanLin (bochnerMatrix D R)⁻¹).toContinuousLinearMap hinv

/-- **Hermitian Metric-Interpolation Spectral-Gap Persistence** (directly using
`HermitianCurvatureCore.hermitian_posSemidef_lerp`):
interpolating `R_t = (1 - t) R₀ + t R₁` (`t ∈ [0, 1]`) between two positive-curvature metrics
with gaps `κ₀, κ₁` yields a uniform Bochner spectral gap `(1 - t) κ₀ + t κ₁` along the path! -/
theorem bochnerMatrix_lerp_spectral_gap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R₀ R₁ : Matrix n n ℂ) {κ₀ κ₁ t : ℝ}
    (hR₀ : (R₀ - (κ₀ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hR₁ : (R₁ - (κ₁ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let Rt : Matrix n n ℂ := (1 - t) • R₀ + t • R₁
    let κt : ℝ := (1 - t) * κ₀ + t * κ₁
    (bochnerMatrix D Rt - (κt : ℂ) • (1 : Matrix n n ℂ)).PosSemidef ∧
    ∀ (hH : (bochnerMatrix D Rt).IsHermitian) (i : n), κt ≤ hH.eigenvalues i := by
  intro Rt κt
  have hlerp := HermitianCurvatureCore.hermitian_posSemidef_lerp hR₀ hR₁ ht0 ht1
  have hRt : Rt - (κt : ℂ) • (1 : Matrix n n ℂ) =
      (1 - t) • (R₀ - (κ₀ : ℂ) • (1 : Matrix n n ℂ)) +
        t • (R₁ - (κ₁ : ℂ) • (1 : Matrix n n ℂ)) := by
    ext i j
    simp only [Rt, κt, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  have hRpos : (Rt - (κt : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by rwa [hRt]
  exact ⟨bochnerMatrix_sub_kappa_posSemidef D Rt hRpos,
    fun hH i => bochnerMatrix_eigenvalues_ge D Rt hRpos hH i⟩

/-- **Kodaira Vanishing in Spectral-Counting Form & Heat-Trace Gap Decay for `bochnerMatrix`**:
connects Pillar 2 directly to Pillar 1's `specCountFin` and `heatTraceFin`! -/
theorem bochnerMatrix_spectral_counting_and_heat_decay
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (R : Matrix n n ℂ) {κ : ℝ}
    (hR : (R - (κ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hH : (bochnerMatrix D R).IsHermitian := bochnerMatrix_isHermitian D R hR) :
    (∀ Λ < κ, specCountFin hH.eigenvalues (fun _ => 1) Finset.univ Λ = 0) ∧
    (∀ t₀ t : ℝ, t₀ ≤ t →
      heatTraceFin hH.eigenvalues (fun _ => 1) Finset.univ t ≤
        Real.exp (-κ * (t - t₀)) * heatTraceFin hH.eigenvalues (fun _ => 1) Finset.univ t₀) := by
  have hgap : ∀ i ∈ (Finset.univ : Finset n), κ ≤ hH.eigenvalues i := fun i _ =>
    bochnerMatrix_eigenvalues_ge D R hR hH i
  exact ⟨fun Λ hΛ => specCountFin_eq_zero_of_lt_gap hgap hΛ,
    fun t₀ t ht => heatTraceFin_spectral_gap_decay (fun _ _ => zero_le_one) hgap ht⟩

end MatrixBochnerCurvature

/-! ## Section 4: Capelli Eigenvalue-Shift & Bessel Wave-Grid Spectral Localization Bridges -/

section CapelliAndBesselBridges

/-- **Capelli 2×2 Quantum-Determinant Spectral Shift & Weight Gap** (directly building on
`CapelliCore.qdet_two_holomorphic_eigenvalue`):
on a holomorphic weight-`k` vector `φ` (`k : ℝ`), the shifted Capelli determinant `-qdet E (1/2)`
acts by the exact positive weight-gap scalar `((k - 1)/2)²`, and `qdet E (u + 1/2)` shifts the
eigenvalue by `u² - ((k - 1)/2)²`. -/
theorem qdet_two_spectral_shift {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E : Fin 2 → Fin 2 → Module.End ℂ V) (hE : CapelliCore.GlRel E) (k : ℝ) (φ : V)
    (h1 : E 0 0 φ + E 1 1 φ = 0)
    (h2 : E 0 1 φ - E 1 0 φ = (Complex.I * (k : ℂ)) • φ)
    (h3 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℝ) :
    CapelliCore.qdet E ((u : ℂ) + 1 / 2) φ =
      ((((u ^ 2 - ((k - 1) / 2) ^ 2 : ℝ) : ℂ)) • φ) ∧
    (-CapelliCore.qdet E (1 / 2) φ) = ((((k - 1) / 2) ^ 2 : ℝ) : ℂ) • φ := by
  have hq := CapelliCore.qdet_two_holomorphic_eigenvalue E hE (k : ℂ) φ h1 h2 h3 (u : ℂ)
  have hq0 := CapelliCore.qdet_two_holomorphic_eigenvalue E hE (k : ℂ) φ h1 h2 h3 (0 : ℂ)
  constructor
  · rw [hq]
    congr 1
    push_cast
    ring
  · rw [zero_add] at hq0
    rw [hq0, ← neg_smul]
    congr 1
    push_cast
    ring

/-- **Harish-Chandra `ρ`-Shift Quadratic Casimir Identity** (directly building on
`CapelliCore.casC_eq_sum_shifted`):
for any real spectral parameter `σ : Fin n → ℝ`,
`Re(casC σ) + ∑_a ((n - 1 - 2 a) / 2)² = ∑_a (σ_a + (n - 1 - 2 a) / 2)² ≥ 0`. -/
theorem casC_rho_shift_identity {n : ℕ} (σ : Fin n → ℝ) :
    (CapelliCore.casC (fun a => (σ a : ℂ))).re +
      ∑ a : Fin n, (((n : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2 =
      ∑ a : Fin n, (σ a + ((n : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2 := by
  rw [CapelliCore.casC_eq_sum_shifted]
  simp only [Complex.add_re, Complex.re_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hre1 : ((σ a : ℂ) ^ 2).re = σ a ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hre2 : ((σ a : ℂ) * ((n : ℂ) - 1 - 2 * (a : ℕ))).re =
      σ a * ((n : ℝ) - 1 - 2 * (a : ℕ)) := by
    have heq : ((n : ℂ) - 1 - 2 * (a : ℕ)) = (((n : ℝ) - 1 - 2 * (a : ℕ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [heq, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre1, hre2]
  ring

/-- **Harish-Chandra Shifted Casimir Spectral Gap**:
for any discrete family of real parameters `σ : ι → Fin n → ℝ`, the `ρ`-shifted Casimir
eigenvalues `λ_k = Re(casC(σ_k)) + ‖ρ_n‖²` are automatically non-negative, and a lower bound
`κ ≤ ∑_a (σ_k a + ρ_a)²` enforces a strict spectral gap `≥ κ` with vanishing spectral count
below `κ`! -/
theorem casC_shifted_spectral_gap {ι : Type*} {n : ℕ} (σ : ι → Fin n → ℝ) :
    let rhoNormSq : ℝ := ∑ a : Fin n, (((n : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2
    let lam : ι → ℝ := fun k => (CapelliCore.casC (fun a => (σ k a : ℂ))).re + rhoNormSq
    (∀ k, 0 ≤ lam k) ∧
    ∀ {κ : ℝ}, (∀ k, κ ≤ ∑ a : Fin n, (σ k a + ((n : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2) →
      (∀ k, κ ≤ lam k) ∧
      ∀ (D : DiscreteSpectrum ι), D.eig = lam → ∀ Λ < κ, D.specCount Λ = 0 := by
  intro rhoNormSq lam
  have hlam_eq : ∀ k, lam k = ∑ a : Fin n, (σ k a + ((n : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2 :=
    fun k => casC_rho_shift_identity (σ k)
  refine ⟨fun k => by rw [hlam_eq k]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _, ?_⟩
  intro κ hκ
  have hgap : ∀ k, κ ≤ lam k := fun k => by rw [hlam_eq k]; exact hκ k
  refine ⟨hgap, fun D hDe Λ hΛ => ?_⟩
  exact D.specCount_eq_zero_of_gap (fun k => by rw [hDe]; exact hgap k) hΛ

/-- **Bessel Wave-Grid Bochner Enhanced Spectral Gap (`BesselWaveGrid` + `HermitianCurvatureCore`)**:
coupling a Bessel wave-grid Gram matrix `BesselWaveGrid.waveGram K = Kᴴ * K` whose columns
satisfy `BesselWaveGrid.gram_frobenius_frame_bound` (with diagonal `≥ dMin` and off-diagonal
Frobenius energy `≤ η²`) with a Hermitian curvature matrix `R ≥ κ I` produces an **additive
enhanced spectral gap `(dMin - η) + κ`** for `Δ_wave = waveGram K + R`, together with:
1. Strict coercivity `((dMin - η) + κ) ‖v‖² ≤ Re ⟪Δ_wave v, v⟫`,
2. Kodaira vanishing `Δ_wave.det ≠ 0` and strict eigenvalue gap `∀ i, (dMin - η) + κ ≤ λ_i`,
3. Quantitative resolvent norm bound `‖Δ_wave⁻¹‖ ≤ ((dMin - η) + κ)⁻¹`, and
4. Exact Lagrange delta test-vector assembly on the spacing-5 grid `progY y0 d`! -/
theorem waveGram_bochner_enhanced_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (K : Matrix ι (Fin d) ℂ) (R : Matrix (Fin d) (Fin d) ℂ)
    {dMin dMax η κ : ℝ} (hη : 0 ≤ η)
    (hdiag_lo : ∀ j : Fin d, dMin ≤ ‖(WithLp.equiv 2 (ι → ℂ)).symm (fun i => K i j)‖ ^ 2)
    (hdiag_hi : ∀ j : Fin d, ‖(WithLp.equiv 2 (ι → ℂ)).symm (fun i => K i j)‖ ^ 2 ≤ dMax)
    (hfrob : ∑ j₁ : Fin d, ∑ j₂ ∈ Finset.univ.erase j₁,
      ‖⟪(WithLp.equiv 2 (ι → ℂ)).symm (fun i => K i j₁),
        (WithLp.equiv 2 (ι → ℂ)).symm (fun i => K i j₂)⟫_ℂ‖ ^ 2 ≤ η ^ 2)
    (hR : (R - (κ : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef)
    (hgap_pos : 0 < (dMin - η) + κ)
    (y0 : ℝ) (i₀ : Fin d) (α : ℂ) :
    let Δw : Matrix (Fin d) (Fin d) ℂ := BesselWaveGrid.waveGram K + R
    (Δw - ((((dMin - η) + κ : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef ∧
    Δw.det ≠ 0 ∧
    (∀ (hH : Δw.IsHermitian) (i : Fin d), (dMin - η) + κ ≤ hH.eigenvalues i) ∧
    ‖(Matrix.toEuclideanLin Δw⁻¹).toContinuousLinearMap‖ ≤ ((dMin - η) + κ)⁻¹ ∧
    ∃ v : Fin d → ℂ, ∀ i : Fin d,
      BesselWaveGrid.waveEval
        (BesselWaveGrid.vandermondeKernel (fun k : Fin d => y0 + 5 * (k : ℝ))) v i =
        if i = i₀ then α else 0 := by
  intro Δw
  let φ : Fin d → EuclideanSpace ℂ ι := fun j => (WithLp.equiv 2 (ι → ℂ)).symm (fun i => K i j)
  -- Step 1: Bessel wave-grid frame lower bound shows `(waveGram K - (dMin - η) I).PosSemidef`
  have hKw_sub_psd :
      (BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
    have hHerm : (BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian := by
      have h1 : (BesselWaveGrid.waveGram K).IsHermitian :=
        (Matrix.posSemidef_conjTranspose_mul_self K).isHermitian
      have h2 : ((((dMin - η : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Complex.star_def, Complex.conj_ofReal]
      exact h1.sub h2
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, fun c => ?_⟩
    have hframe := (BesselWaveGrid.gram_frobenius_frame_bound φ c hη hdiag_lo hdiag_hi hfrob).1
    have hsum_eq : ∑ j : Fin d, c j • φ j = (WithLp.equiv 2 (ι → ℂ)).symm (K *ᵥ c) := by
      ext i
      change (WithLp.ofLp (∑ j : Fin d, c j • φ j)) i = (K *ᵥ c) i
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      unfold Matrix.mulVec dotProduct
      refine Finset.sum_congr rfl fun j _ => ?_
      change c j * K i j = K i j * c j
      exact mul_comm _ _
    have hnorm_eq : ‖∑ j : Fin d, c j • φ j‖ ^ 2 = ∑ i : ι, ‖BesselWaveGrid.waveEval K c i‖ ^ 2 := by
      rw [hsum_eq, EuclideanSpace.norm_sq_eq]
      rfl
    rw [hnorm_eq, BesselWaveGrid.waveEval_energy_eq_gram] at hframe
    have hquad_sub :
        star c ⬝ᵥ (BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • 1).mulVec c =
          star c ⬝ᵥ (BesselWaveGrid.waveGram K).mulVec c -
            (((dMin - η : ℝ) : ℂ)) * (star c ⬝ᵥ c) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
    have hstar_self : star c ⬝ᵥ c = ((∑ j : Fin d, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
      unfold dotProduct
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_pow]
    have hre : 0 ≤ (star c ⬝ᵥ
        (BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • 1).mulVec c).re := by
      rw [hquad_sub, hstar_self, Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re]
      linarith
    have him : (star c ⬝ᵥ
        (BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • 1).mulVec c).im = 0 := by
      set M : Matrix (Fin d) (Fin d) ℂ :=
        BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)
      have hconj : star c ⬝ᵥ M.mulVec c = star (star c ⬝ᵥ M.mulVec c) := by
        conv_lhs => rw [star_dotProduct, Matrix.star_mulVec, hHerm.eq, ← Matrix.dotProduct_mulVec]
      have h' := congrArg Complex.im hconj
      rw [Complex.star_def, Complex.conj_im] at h'
      linarith
    rw [Complex.le_def]
    exact ⟨by simpa using hre, by simpa using him.symm⟩
  -- Step 2: Combine `(waveGram K - (dMin - η) I).PosSemidef` with `(R - κ I).PosSemidef`
  have hΔ_sub :
      (Δw - ((((dMin - η) + κ : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
    have heq : Δw - ((((dMin - η) + κ : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) =
        (BesselWaveGrid.waveGram K - (((dMin - η : ℝ) : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) +
          (R - (κ : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
      ext i j
      simp only [Δw, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_add]
      ring
    rw [heq]
    exact hKw_sub_psd.add hR
  -- Step 3: Treat `Δw = bochnerMatrix 0 Δw` with curvature gap `(dMin - η) + κ`
  have hΔeq : bochnerMatrix (0 : Matrix (Fin 0) (Fin d) ℂ) Δw = Δw := by
    simp [bochnerMatrix]
  have hdet : Δw.det ≠ 0 := by
    simpa [hΔeq] using bochnerMatrix_det_ne_zero (0 : Matrix (Fin 0) (Fin d) ℂ) Δw hgap_pos hΔ_sub
  have heig : ∀ (hH : Δw.IsHermitian) (i : Fin d), (dMin - η) + κ ≤ hH.eigenvalues i := by
    intro hH i
    have h := bochnerMatrix_eigenvalues_ge (0 : Matrix (Fin 0) (Fin d) ℂ) Δw hΔ_sub
      (by simpa [hΔeq] using hH) i
    simpa [hΔeq] using h
  have hres : ‖(Matrix.toEuclideanLin Δw⁻¹).toContinuousLinearMap‖ ≤ ((dMin - η) + κ)⁻¹ := by
    simpa [hΔeq] using bochnerMatrix_resolvent_opNorm_le (0 : Matrix (Fin 0) (Fin d) ℂ) Δw hgap_pos hΔ_sub
  exact ⟨hΔ_sub, hdet, heig, hres, BesselWaveGrid.exists_delta_test_vector_progY y0 d i₀ α⟩

/-- **Wave-Grid Multiplicity Budget Discharge from Heat-Trace Weyl Bound**:
combines `DiscreteSpectrum.weyl_upper_bound` with `BesselWaveGrid.rankVal_wave_grid_bounds`:
whenever `Z(1/Λ) ≤ C (1/Λ)^{-d/2}` and `e · C · Λ^{d/2} ≤ TOv s * nWv R s`, the spectral count
`N(Λ)` fits inside the exact wave-grid rank budget `R.r + R.t`! -/
theorem waveGrid_multiplicity_budget_of_heatTrace {ι : Type*}
    (D : DiscreteSpectrum ι) {s : ScaleParams} {R : ChainRanks} (hR : RankVal s R)
    {C d Λ : ℝ} (hΛ : 0 < Λ) (hZsum : D.HeatSummable (1 / Λ))
    (hZ : D.heatTrace (1 / Λ) ≤ C * (1 / Λ) ^ (-(d / 2)))
    (hcap : Real.exp 1 * C * Λ ^ (d / 2) ≤ ((TOv s * nWv R s : ℕ) : ℝ)) :
    D.specCount Λ ≤ ((R.r + R.t : ℕ) : ℝ) := by
  have hweyl := D.weyl_upper_bound hΛ hZsum hZ
  have hbal : ((TOv s * nWv R s : ℕ) : ℝ) ≤ ((R.r + R.t : ℕ) : ℝ) := by
    exact_mod_cast (BesselWaveGrid.rankVal_wave_grid_bounds hR).1
  exact hweyl.trans (hcap.trans hbal)

end CapelliAndBesselBridges

/-! ## Section 5: Unified Stage-3 Explicit Spectral Discharge & Bridge to `Stage2ThetaWire` -/

section Stage3UnifiedBridge

/-- **Master Unified Stage-3 Explicit Spectral Discharge Theorem**:
combines all three pillars into one end-to-end spectral multiplicity, wave-kernel localization,
Bochner–Kodaira–Nakano curvature gap & Capelli/Bessel/Stage2ThetaWire transfer theorem:
1. **Karamata–Weyl Heat-Kernel Spectral Counting & Gaussian/Lorentzian Wave Localization**
   (`N(Λ) ≤ e · Z(1/Λ) ≤ e · C · Λ^{d/2}` and `W(Λ, σ) ≤ e^{1/2} · G(Λ, σ)`),
2. **Bochner–Kodaira–Nakano Curvature Positivity, Strict Spectral Gap & Resolvent Bound**
   (`Δ = Dᴴ D + R` with `R ≥ κ I` has `det Δ ≠ 0`, `∀ i, κ ≤ λ_i`, `‖Δ⁻¹‖ ≤ κ⁻¹`, and
   vanishing count below `κ`),
3. **Capelli `qdet` + Harish-Chandra `ρ`-Shift + Bessel Wave-Grid Enhanced Gap**
   (from `CapelliCore` & `BesselWaveGrid`), and
4. **Curvature-Covolume Bost Slope Ceiling** (`HermitianCurvatureCore`). -/
theorem stage3_explicit_spectral_discharge
    -- Pillar 1: Discrete spectrum + heat-kernel Weyl & Gaussian wave data
    {ι_s : Type*} (Dspec : DiscreteSpectrum ι_s) {C d Λ σ : ℝ} (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hZsum : Dspec.HeatSummable (1 / Λ))
    (hZweyl : Dspec.heatTrace (1 / Λ) ≤ C * (1 / Λ) ^ (-(d / 2)))
    -- Pillar 2: Bochner–Kodaira–Nakano Hermitian matrix curvature data
    {m_b n_b : Type*} [Fintype m_b] [Fintype n_b] [DecidableEq m_b] [DecidableEq n_b]
    (Db : Matrix m_b n_b ℂ) (Rb : Matrix n_b n_b ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hRb : (Rb - (κ : ℂ) • (1 : Matrix n_b n_b ℂ)).PosSemidef)
    -- Pillar 3a: Capelli 2×2 holomorphic & Harish-Chandra Casimir data
    {V_c : Type*} [AddCommGroup V_c] [Module ℂ V_c]
    (E_c : Fin 2 → Fin 2 → Module.End ℂ V_c) (hEc : CapelliCore.GlRel E_c) (k_c : ℝ) (φ_c : V_c)
    (hc1 : E_c 0 0 φ_c + E_c 1 1 φ_c = 0)
    (hc2 : E_c 0 1 φ_c - E_c 1 0 φ_c = (Complex.I * (k_c : ℂ)) • φ_c)
    (hc3 : E_c 0 0 φ_c - E_c 1 1 φ_c = Complex.I • (E_c 0 1 φ_c + E_c 1 0 φ_c))
    {n_c : ℕ} (σ_c : Fin n_c → ℝ)
    -- Pillar 3b: Bost curvature-covolume fiber
    (B : BostSlopeFiber) (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η)
    (he0 : 0 ≤ B.e) (he1 : B.e ≤ 1 / 4)
    (hHH : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH) {muCap : ℝ}
    (hCurvCap : B.muCC ≤ muCap) :
    -- Conclusions:
    -- (1) Karamata-Weyl upper bound & Gaussian wave localization
    (Dspec.specCount Λ ≤ Real.exp 1 * C * Λ ^ (d / 2) ∧
     Dspec.GaussSummable Λ σ ∧
     Dspec.windowCount Λ σ ≤ Real.exp (1 / 2 : ℝ) * Dspec.gaussWaveTrace Λ σ) ∧
    -- (2) Bochner-Kodaira-Nakano Kodaira vanishing, strict spectral gap & resolvent norm
    ((bochnerMatrix Db Rb).det ≠ 0 ∧
     (∀ (hH : (bochnerMatrix Db Rb).IsHermitian) (i : n_b), κ ≤ hH.eigenvalues i) ∧
     ‖(Matrix.toEuclideanLin (bochnerMatrix Db Rb)⁻¹).toContinuousLinearMap‖ ≤ κ⁻¹) ∧
    -- (3) Capelli qdet weight gap & Harish-Chandra shifted Casimir positivity
    ((-CapelliCore.qdet E_c (1 / 2) φ_c) = ((((k_c - 1) / 2) ^ 2 : ℝ) : ℂ) • φ_c ∧
     0 ≤ (CapelliCore.casC (fun a => (σ_c a : ℂ))).re +
       ∑ a : Fin n_c, (((n_c : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2) ∧
    -- (4) Curvature-covolume Bost slope ceiling
    (B.s - muCap -
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) ≤ Real.log (B.cardW : ℝ)) := by
  have hweyl := Dspec.weyl_upper_bound hΛ hZsum hZweyl
  obtain ⟨hGsum, _⟩ := Dspec.gaussWaveTrace_le_heatTrace Λ (1 / Λ) hσ hZsum
  have hwin := Dspec.windowCount_le_exp_half_mul_gaussWaveTrace hσ hGsum
  have hq := (qdet_two_spectral_shift E_c hEc k_c φ_c hc1 hc2 hc3 0).2
  have hcas : 0 ≤ (CapelliCore.casC (fun a => (σ_c a : ℂ))).re +
      ∑ a : Fin n_c, (((n_c : ℝ) - 1 - 2 * (a : ℕ)) / 2) ^ 2 := by
    rw [casC_rho_shift_identity σ_c]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨⟨hweyl, hGsum, hwin⟩,
    ⟨bochnerMatrix_det_ne_zero Db Rb hκ hRb,
     fun hH i => bochnerMatrix_eigenvalues_ge Db Rb hRb hH i,
     bochnerMatrix_resolvent_opNorm_le Db Rb hκ hRb⟩,
    ⟨hq, hcas⟩,
    HermitianCurvatureCore.bost_slope_from_curvature_volume_bound B hSlope
      hdel0 hdel1 hη he0 he1 hHH hHH_pos hCurvCap⟩

/-- **Stage-3 Gram-Frame + Bochner Spectral-Gap Bost Bridge** (directly feeding
`Stage2ThetaWire.Stage2GramFrameFiber`):
simultaneously discharges `F.toBostFiber.SlopeIneq` AND certifies the coupled Bochner–Kodaira
curvature spectral gap `κ > 0`, Kodaira vanishing `det Δ ≠ 0`, and resolvent norm `‖Δ⁻¹‖ ≤ κ⁻¹`! -/
theorem stage3_gramFrame_spectral_bost_bridge
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar)
    (huF0 : 0 ≤ uF)
    {m_b n_b : Type*} [Fintype m_b] [Fintype n_b] [DecidableEq m_b] [DecidableEq n_b]
    (Db : Matrix m_b n_b ℂ) (Rb : Matrix n_b n_b ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hRb : (Rb - (κ : ℂ) • (1 : Matrix n_b n_b ℂ)).PosSemidef) :
    F.toBostFiber.SlopeIneq ∧
    (bochnerMatrix Db Rb).det ≠ 0 ∧
    (∀ (hH : (bochnerMatrix Db Rb).IsHermitian) (i : n_b), κ ≤ hH.eigenvalues i) ∧
    ‖(Matrix.toEuclideanLin (bochnerMatrix Db Rb)⁻¹).toContinuousLinearMap‖ ≤ κ⁻¹ :=
  ⟨F.toBostSlopeIneq huF0,
   bochnerMatrix_det_ne_zero Db Rb hκ hRb,
   fun hH i => bochnerMatrix_eigenvalues_ge Db Rb hRb hH i,
   bochnerMatrix_resolvent_opNorm_le Db Rb hκ hRb⟩

/-- **Stage-3 Spectral Multiplicity & Curvature Certificate**:
packages a discrete non-negative spectrum with heat-kernel Weyl asymptotics, a wave-grid
rank budget, and a strictly positive Bochner curvature gap `κ > 0` into a self-verifying
Stage-3 spectral certificate. -/
structure SpectralMultiplicityCert (s : ScaleParams) (R : ChainRanks) : Type 1 where
  ι : Type
  spec : DiscreteSpectrum ι
  C_weyl : ℝ
  d_weyl : ℝ
  Λ : ℝ
  σ : ℝ
  Λ_pos : 0 < Λ
  σ_pos : 0 < σ
  heat_summable : spec.HeatSummable (1 / Λ)
  heat_weyl_bound : spec.heatTrace (1 / Λ) ≤ C_weyl * (1 / Λ) ^ (-(d_weyl / 2))
  budget_cap : Real.exp 1 * C_weyl * Λ ^ (d_weyl / 2) ≤ ((TOv s * nWv R s : ℕ) : ℝ)
  m_b : Type
  n_b : Type
  [finM : Fintype m_b]
  [finN : Fintype n_b]
  [decM : DecidableEq m_b]
  [decN : DecidableEq n_b]
  Db : Matrix m_b n_b ℂ
  Rb : Matrix n_b n_b ℂ
  κ : ℝ
  κ_pos : 0 < κ
  curv_pos : (Rb - (κ : ℂ) • (1 : Matrix n_b n_b ℂ)).PosSemidef

attribute [instance] SpectralMultiplicityCert.finM SpectralMultiplicityCert.finN
  SpectralMultiplicityCert.decM SpectralMultiplicityCert.decN

/-- Every `SpectralMultiplicityCert s R` together with `RankVal s R` discharges:
1. Weyl upper bound `specCount Λ ≤ e · C · Λ^{d/2}`,
2. Wave-grid rank budget `specCount Λ ≤ R.r + R.t`,
3. Gaussian wave-kernel short-interval localization `windowCount Λ σ ≤ e^{1/2} · gaussWaveTrace Λ σ`,
4. Kodaira vanishing `det(Dbᴴ Db + Rb) ≠ 0`, strict spectral gap `∀ i, κ ≤ λ_i`, and
   resolvent norm `‖(Dbᴴ Db + Rb)⁻¹‖ ≤ κ⁻¹`! -/
theorem SpectralMultiplicityCert.discharge {s : ScaleParams} {R : ChainRanks}
    (hR : RankVal s R) (M : SpectralMultiplicityCert s R) :
    M.spec.specCount M.Λ ≤ Real.exp 1 * M.C_weyl * M.Λ ^ (M.d_weyl / 2) ∧
    M.spec.specCount M.Λ ≤ ((R.r + R.t : ℕ) : ℝ) ∧
    M.spec.windowCount M.Λ M.σ ≤ Real.exp (1 / 2 : ℝ) * M.spec.gaussWaveTrace M.Λ M.σ ∧
    (bochnerMatrix M.Db M.Rb).det ≠ 0 ∧
    (∀ (hH : (bochnerMatrix M.Db M.Rb).IsHermitian) (i : M.n_b), M.κ ≤ hH.eigenvalues i) ∧
    ‖(Matrix.toEuclideanLin (bochnerMatrix M.Db M.Rb)⁻¹).toContinuousLinearMap‖ ≤ M.κ⁻¹ := by
  have hweyl := M.spec.weyl_upper_bound M.Λ_pos M.heat_summable M.heat_weyl_bound
  have hbud := waveGrid_multiplicity_budget_of_heatTrace M.spec hR M.Λ_pos
    M.heat_summable M.heat_weyl_bound M.budget_cap
  obtain ⟨hGsum, _⟩ := M.spec.gaussWaveTrace_le_heatTrace M.Λ (1 / M.Λ) M.σ_pos M.heat_summable
  have hwin := M.spec.windowCount_le_exp_half_mul_gaussWaveTrace M.σ_pos hGsum
  exact ⟨hweyl, hbud, hwin,
    bochnerMatrix_det_ne_zero M.Db M.Rb M.κ_pos M.curv_pos,
    fun hH i => bochnerMatrix_eigenvalues_ge M.Db M.Rb M.curv_pos hH i,
    bochnerMatrix_resolvent_opNorm_le M.Db M.Rb M.κ_pos M.curv_pos⟩

/-- **Stage-3 Spectral-Enriched Pillar-2 Input Bundle (`Stage3SpectralThetaInputs S`)**:
attaches explicit `SpectralMultiplicityCert` witnesses to `Stage2ThetaWire.Stage2ThetaCoreInputs S`
and compiles directly into `ThetaSlopeContract S` and `AllLevelsWindowBound (3 / 2)`! -/
structure Stage3SpectralThetaInputs (S : SelmerSystem) where
  core : Stage2ThetaCoreInputs S
  spectralCert : PChar → ∀ (eps x : ℝ) (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52)
    (R : ChainRanks), RankVal (stage2ScaleParams x eps hx1 heps heps52) R →
    Nonempty (SpectralMultiplicityCert (stage2ScaleParams x eps hx1 heps heps52) R)

/-- **Direct Stage-3 Export into `Stage2ThetaWire.stage2_thetaSlopeContract`**:
produces `RHDirect.ThetaSlopeContract S` together with certified spectral-multiplicity and
Bochner–Kodaira spectral-gap bounds at every admissible chain rank `R`. -/
theorem stage3_thetaSlopeContract (S : SelmerSystem) (I : Stage3SpectralThetaInputs S) :
    ThetaSlopeContract S ∧
    (PChar → ∀ (eps x : ℝ) (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52)
      (R : ChainRanks), RankVal (stage2ScaleParams x eps hx1 heps heps52) R →
      ∃ M : SpectralMultiplicityCert (stage2ScaleParams x eps hx1 heps heps52) R,
        M.spec.specCount M.Λ ≤ ((R.r + R.t : ℕ) : ℝ) ∧
        M.spec.windowCount M.Λ M.σ ≤ Real.exp (1 / 2 : ℝ) * M.spec.gaussWaveTrace M.Λ M.σ ∧
        (bochnerMatrix M.Db M.Rb).det ≠ 0 ∧
        ‖(Matrix.toEuclideanLin (bochnerMatrix M.Db M.Rb)⁻¹).toContinuousLinearMap‖ ≤ M.κ⁻¹) := by
  refine ⟨stage2_thetaSlopeContract S I.core, fun ψ eps x hx1 heps heps52 R hR => ?_⟩
  obtain ⟨M⟩ := I.spectralCert ψ eps x hx1 heps heps52 R hR
  obtain ⟨_, hbud, hwin, hdet, _, hres⟩ := M.discharge hR
  exact ⟨M, hbud, hwin, hdet, hres⟩

/-- Direct windowed Cesàro von Mangoldt bound `AllLevelsWindowBound (3 / 2)` from
`Stage3SpectralThetaInputs S` and `VWin S`. -/
theorem stage3_allLevelsWindowBound (S : SelmerSystem) (I : Stage3SpectralThetaInputs S)
    (hV : VWin S) :
    AllLevelsWindowBound (3 / 2) :=
  stage2_allLevelsWindowBound S I.core hV

end Stage3UnifiedBridge

end

end RHDirect.Stage3ExplicitSpectral
