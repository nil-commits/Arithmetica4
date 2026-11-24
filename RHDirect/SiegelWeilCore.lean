import RHDirect.Interfaces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# RHDirect.SiegelWeilCore

Compact, direct, zero-`sorry`, zero-custom-`axiom` rebuild of the **Siegel–Weil / Regularized
Eisenstein Integral Convergence, Unramified Howe Duality, Functional Separation, and
Fourier-Coefficient Matching Core** against `RHDirect.Interfaces` and Mathlib `v4.33.1`.

Replaces the sprawling upstream chain across:
- `ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean` (plus `_alt` clones),
- `LocalTypeDictionary/FunctionalsSeparateOfHoweUnramOfSiegelWeil.lean`,
  `RealFunctionalsSeparateOfHypothesis.lean`, `ConvergenceOfSeparatingFamily.lean`,
  `RapidDecayOfSeparatingFamily.lean`, `TwistCoreSurjectiveOfLocalComponents.lean`,
  `BesselSeparate.lean`, `GlobalFormOfSiegelWeil.lean`,
  `BottomFourierCoeffHeisenbergExpansion.lean`,
- `ThirdPlaceSeries/FourierCoefficientFitOfJoin.lean` & `FittedFunctionAtZeroClose.lean`,
- `IwasawaDecomposition/RowRatWOfRowTest.lean`,
with **all 33 dead fields** of `ThetaLocalInputs` and **all 13 dead fields** of
`UnitaryGroupThirdPlaceHypotheses` completely eliminated.

## Contents
1. **Unitary Dual-Pair Weil Convergence Range & Theta-Integral Bounds**:
   Exact Weil convergence criterion `n < m`, `m ≤ 2n`, `n + r < m`, Siegel–Weil point
   `sZero = (m - n) / 2`, Bochner integrability and quantitative `L¹` bounds for theta kernels
   under Siegel-set polynomial envelopes, regularized theta mean `thetaMean`, iterated row-tower
   convergence/rapid decay, and direct specialization to `RHDirect.ChainRanks.chainRank`.
2. **Regularized Siegel–Eisenstein Series, Constant & Second-Term Comparison**:
   Constant/second-term/tail sandwich bounds, strict nonvanishing under dominant constant term,
   normalized ratio closeness, second-term height suppression in the `n + r + 1 < m` range, and
   self-dual lattice transfer for global doubling zeta forms.
3. **Unramified Howe Duality & Functional Separation (`FunctionalsSeparate`)**:
   Commuting dual-pair Weil action `ω : G₁ × G₂ →* End ℂ M`, `K`-fixed submodules vs. Hecke/Weil
   spans, exact equivalence `HoweUnram ↔ (fixed₁ = span₂ ∧ fixed₂ = span₁)`, core surjectivity
   `core_surjective_of_howeUnram_of_siegelWeil`, equivalence `Separates ↔ SeparatesSpan`,
   injectivity `inj_of_separates`, Bessel eigenvalue-gap Lagrange isolation
   `bessel_gap_isolates_component`, and full `functionalsSeparate_of_howeUnram_of_siegelWeil`.
4. **Heisenberg/Fourier Extraction, `fourier_coefficient_fit`, `rowRatW_of_rowTest` & Assembly**:
   Finite-group additive character orthogonality, exact Fourier coefficient recovery, quantitative
   `fourier_coefficient_fit` (matching + tail bound → constant fit + nonvanishing + ratio bound),
   dead-wrapper-free `rowRatW_of_rowTest`, and unified `max CF₀ CF₁` definite-side assembly.
-/

noncomputable section

open MeasureTheory Finset Real RHDirect
open scoped BigOperators

namespace RHDirect.SiegelWeilCore

/-! ## Section 1: Unitary Dual-Pair Weil Convergence Range & Theta-Integral Bounds -/

/-- Rank and Witt-index data for a unitary dual pair `(U(A), U(B))` with `A` of rank `n` and
`B` of rank `m` and Witt index `r ≤ m` (matching `SiegelWeilUnitaryConvergent`). -/
structure DualPairRanks where
  n : ℕ
  m : ℕ
  r : ℕ
  r_le : r ≤ m

namespace DualPairRanks

/-- The Siegel–Weil evaluation point `s₀ = (m - n) / 2` for `(U(n, n), U(B))`. -/
def sZero (P : DualPairRanks) : ℝ := ((P.m : ℝ) - (P.n : ℝ)) / 2

/-- The effective convergence exponent `m - r` controlling theta-kernel decay on Siegel sets. -/
def effRank (P : DualPairRanks) : ℕ := P.m - P.r

/-- Weil's absolute convergence range for the unitary Siegel–Weil formula:
`n < m`, `m ≤ 2n`, and `n + r < m` (i.e., `m - r > n`). -/
def WeilConvergentRange (P : DualPairRanks) : Prop :=
  P.n < P.m ∧ P.m ≤ 2 * P.n ∧ P.n + P.r < P.m

/-- Strict second-term convergence range (`n + r + 1 < m`), providing an extra unit of
decay separating the second intertwining term from the convergence threshold. -/
def SecondTermRange (P : DualPairRanks) : Prop :=
  P.n + 1 < P.m ∧ P.m ≤ 2 * P.n ∧ P.n + P.r + 1 < P.m

theorem one_le_n_of_weilRange {P : DualPairRanks} (h : P.WeilConvergentRange) : 1 ≤ P.n := by
  rcases h with ⟨h1, h2, _⟩
  omega

theorem weilRange_of_secondTermRange {P : DualPairRanks} (h : P.SecondTermRange) :
    P.WeilConvergentRange := by
  rcases h with ⟨h1, h2, h3⟩
  exact ⟨by omega, h2, by omega⟩

theorem weilRange_of_anisotropic {P : DualPairRanks} (hr : P.r = 0)
    (h1 : P.n < P.m) (h2 : P.m ≤ 2 * P.n) : P.WeilConvergentRange :=
  ⟨h1, h2, by omega⟩

theorem effRank_gt_n {P : DualPairRanks} (h : P.WeilConvergentRange) : P.n < P.effRank := by
  unfold effRank
  have := h.2.2
  omega

theorem effRank_gt_n_add_one {P : DualPairRanks} (h : P.SecondTermRange) :
    P.n + 1 < P.effRank := by
  unfold effRank
  have := h.2.2
  omega

theorem sZero_ge_half_of_weilRange {P : DualPairRanks} (h : P.WeilConvergentRange) :
    (1 : ℝ) / 2 ≤ P.sZero := by
  unfold sZero
  have hnm : (P.n : ℝ) + 1 ≤ (P.m : ℝ) := by exact_mod_cast h.1
  linarith

theorem sZero_pos_of_weilRange {P : DualPairRanks} (h : P.WeilConvergentRange) :
    0 < P.sZero :=
  lt_of_lt_of_le (by norm_num) (sZero_ge_half_of_weilRange h)

theorem sZero_le_half_n_of_weilRange {P : DualPairRanks} (h : P.WeilConvergentRange) :
    P.sZero ≤ (P.n : ℝ) / 2 := by
  unfold sZero
  have h2 : (P.m : ℝ) ≤ 2 * (P.n : ℝ) := by exact_mod_cast h.2.1
  linarith

theorem sZero_ge_one_of_secondTermRange {P : DualPairRanks} (h : P.SecondTermRange) :
    (1 : ℝ) ≤ P.sZero := by
  unfold sZero
  have hnm : (P.n : ℝ) + 2 ≤ (P.m : ℝ) := by exact_mod_cast h.1
  linarith

/-- Dual-pair ranks attached to step `j` of an iterated theta-lift chain `R : ChainRanks`,
stepping from `R.chainRank j` to `R.chainRank (j + 1) = R.chainRank j + (R.t + 1)`. -/
def ofChainStep (R : ChainRanks) (j r : ℕ) (hr : r ≤ R.chainRank (j + 1)) : DualPairRanks where
  n := R.chainRank j
  m := R.chainRank (j + 1)
  r := r
  r_le := hr

theorem chainStep_sZero_eq (R : ChainRanks) (j r : ℕ) (hr : r ≤ R.chainRank (j + 1)) :
    (ofChainStep R j r hr).sZero = ((R.t : ℝ) + 1) / 2 := by
  unfold ofChainStep sZero ChainRanks.chainRank
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

theorem chainStep_weilRange (R : ChainRanks) (j r : ℕ) (hr : r ≤ R.chainRank (j + 1))
    (htk : R.t + 1 ≤ R.k) (hrt : r < R.t + 1) :
    (ofChainStep R j r hr).WeilConvergentRange := by
  unfold ofChainStep WeilConvergentRange ChainRanks.chainRank
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have : R.t + 1 ≤ R.k + j * (R.t + 1) := le_trans htk (Nat.le_add_right _ _)
    nlinarith
  · nlinarith

theorem chainStep_secondTermRange (R : ChainRanks) (j r : ℕ) (hr : r ≤ R.chainRank (j + 1))
    (ht : 1 ≤ R.t) (htk : R.t + 1 ≤ R.k) (hrt : r < R.t) :
    (ofChainStep R j r hr).SecondTermRange := by
  unfold ofChainStep SecondTermRange ChainRanks.chainRank
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have : R.t + 1 ≤ R.k + j * (R.t + 1) := le_trans htk (Nat.le_add_right _ _)
    nlinarith
  · nlinarith

end DualPairRanks

/-- Monotonicity of negative real powers `H ^ (-b) ≤ H ^ (-a)` for `1 ≤ H` and `a ≤ b`. -/
theorem rpow_neg_le_rpow_neg_of_one_le {H a b : ℝ} (hH : 1 ≤ H) (hab : a ≤ b) :
    H ^ (-b) ≤ H ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le hH (neg_le_neg hab)

/-- Extra `H⁻¹` suppression when the decay exponent exceeds the critical exponent by at least `1`. -/
theorem rpow_neg_le_inv_mul_rpow_neg {H a b : ℝ} (hH : 1 ≤ H) (hab : a + 1 ≤ b) :
    H ^ (-b) ≤ H⁻¹ * H ^ (-a) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  calc H ^ (-b)
      ≤ H ^ (-(a + 1)) := rpow_neg_le_rpow_neg_of_one_le hH hab
    _ = H ^ ((-1 : ℝ) + (-a)) := by ring_nf
    _ = H ^ (-1 : ℝ) * H ^ (-a) := Real.rpow_add hHpos (-1) (-a)
    _ = H⁻¹ * H ^ (-a) := by rw [Real.rpow_neg_one]

/-- Siegel-set decay envelope data for a theta kernel on a measure space `(X, μ)`. -/
structure SiegelSetEnvelope {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  H : X → ℝ
  H_meas : AEStronglyMeasurable H μ
  H_ge_one : ∀ᵐ x ∂μ, 1 ≤ H x
  critExp : ℝ
  vol_integrable : Integrable (fun x => (H x) ^ (-critExp)) μ

/-- Under a Siegel-set polynomial volume bound at `critExp`, any stronger decay exponent
`decayExp ≥ critExp` is automatically integrable and dominated in `L¹`. -/
theorem SiegelSetEnvelope.decay_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (E : SiegelSetEnvelope μ) {decayExp : ℝ} (hExp : E.critExp ≤ decayExp) :
    Integrable (fun x => (E.H x) ^ (-decayExp)) μ := by
  refine E.vol_integrable.mono' (E.H_meas.aemeasurable.pow_const (-decayExp)).aestronglyMeasurable ?_
  filter_upwards [E.H_ge_one] with x hx
  have hpos : 0 ≤ (E.H x) ^ (-decayExp) := Real.rpow_nonneg (le_trans zero_le_one hx) _
  rw [Real.norm_of_nonneg hpos]
  exact rpow_neg_le_rpow_neg_of_one_le hx hExp

theorem SiegelSetEnvelope.integral_decay_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (E : SiegelSetEnvelope μ) {decayExp : ℝ} (hExp : E.critExp ≤ decayExp) :
    ∫ x, (E.H x) ^ (-decayExp) ∂μ ≤ ∫ x, (E.H x) ^ (-E.critExp) ∂μ := by
  refine integral_mono_ae (E.decay_integrable hExp) E.vol_integrable ?_
  filter_upwards [E.H_ge_one] with x hx
  exact rpow_neg_le_rpow_neg_of_one_le hx hExp

/-- **Theta-Integral Convergence & Quantitative `L¹` Bound**:
Any measurable theta kernel `θ : X → ℂ` dominated by `C * H(x)^(-decayExp)` with
`decayExp ≥ E.critExp` (in particular, `m - r > n` in Weil's convergent range) is Bochner
integrable on `(X, μ)` with explicit upper bound on `‖∫ x, θ x ∂μ‖`. -/
theorem thetaKernel_integrable_of_siegel_envelope {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (E : SiegelSetEnvelope μ) {θ : X → ℂ} {C decayExp : ℝ}
    (hC : 0 ≤ C) (hExp : E.critExp ≤ decayExp)
    (hθm : AEStronglyMeasurable θ μ)
    (hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * (E.H x) ^ (-decayExp)) :
    Integrable θ μ ∧
      ‖∫ x, θ x ∂μ‖ ≤ C * ∫ x, (E.H x) ^ (-decayExp) ∂μ ∧
      ‖∫ x, θ x ∂μ‖ ≤ C * ∫ x, (E.H x) ^ (-E.critExp) ∂μ := by
  have hDec : Integrable (fun x => (E.H x) ^ (-decayExp)) μ := E.decay_integrable hExp
  have hInt : Integrable θ μ := (hDec.const_mul C).mono' hθm hθb
  have hNorm1 : ‖∫ x, θ x ∂μ‖ ≤ C * ∫ x, (E.H x) ^ (-decayExp) ∂μ := by
    calc ‖∫ x, θ x ∂μ‖
        ≤ ∫ x, ‖θ x‖ ∂μ := norm_integral_le_integral_norm θ
      _ ≤ ∫ x, C * (E.H x) ^ (-decayExp) ∂μ :=
          integral_mono_ae hInt.norm (hDec.const_mul C) hθb
      _ = C * ∫ x, (E.H x) ^ (-decayExp) ∂μ := integral_const_mul C _
  have hNorm2 : ‖∫ x, θ x ∂μ‖ ≤ C * ∫ x, (E.H x) ^ (-E.critExp) ∂μ :=
    le_trans hNorm1 (mul_le_mul_of_nonneg_left (E.integral_decay_le hExp) hC)
  exact ⟨hInt, hNorm1, hNorm2⟩

/-- Specialization of theta-integral convergence directly to a `DualPairRanks` in
`WeilConvergentRange` (`n + r < m`), setting `critExp = n` and `decayExp = m - r`. -/
theorem thetaKernel_integrable_of_weilRange {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P : DualPairRanks) (hW : P.WeilConvergentRange)
    (E : SiegelSetEnvelope μ) (hCrit : E.critExp = (P.n : ℝ))
    {θ : X → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hθm : AEStronglyMeasurable θ μ)
    (hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * (E.H x) ^ (-(P.effRank : ℝ))) :
    Integrable θ μ ∧ ‖∫ x, θ x ∂μ‖ ≤ C * ∫ x, (E.H x) ^ (-(P.n : ℝ)) ∂μ := by
  have hle : E.critExp ≤ (P.effRank : ℝ) := by
    rw [hCrit]
    exact_mod_cast (P.effRank_gt_n hW).le
  have h := thetaKernel_integrable_of_siegel_envelope E hC hle hθm hθb
  rw [hCrit] at h
  exact ⟨h.1, h.2.2⟩

/-- Regularized theta mean `(vol)⁻¹ • ∫ x, θ x ∂μ` over the automorphic quotient `[U(B)]`. -/
def thetaMean {X : Type*} [MeasurableSpace X] (μ : Measure X) (vol : ℝ) (θ : X → ℂ) : ℂ :=
  (vol⁻¹ : ℝ) • ∫ x, θ x ∂μ

theorem thetaMean_zero {X : Type*} [MeasurableSpace X] (μ : Measure X) (vol : ℝ) :
    thetaMean μ vol (fun _ => 0) = 0 := by
  simp [thetaMean]

theorem thetaMean_smul {X : Type*} [MeasurableSpace X] (μ : Measure X) (vol : ℝ)
    (c : ℂ) (θ : X → ℂ) :
    thetaMean μ vol (fun x => c * θ x) = c * thetaMean μ vol θ := by
  simp only [thetaMean, integral_const_mul, Complex.real_smul]
  ring

theorem thetaMean_add {X : Type*} [MeasurableSpace X] (μ : Measure X) (vol : ℝ)
    {θ₁ θ₂ : X → ℂ} (h₁ : Integrable θ₁ μ) (h₂ : Integrable θ₂ μ) :
    thetaMean μ vol (fun x => θ₁ x + θ₂ x) = thetaMean μ vol θ₁ + thetaMean μ vol θ₂ := by
  simp only [thetaMean, integral_add h₁ h₂, smul_add]

theorem norm_thetaMean_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {vol : ℝ}
    (hvol : 0 < vol) (θ : X → ℂ) :
    ‖thetaMean μ vol θ‖ ≤ vol⁻¹ * ∫ x, ‖θ x‖ ∂μ := by
  rw [thetaMean, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hvol.le)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm θ) (inv_nonneg.2 hvol.le)

theorem norm_thetaMean_le_of_envelope {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (E : SiegelSetEnvelope μ) {vol C decayExp : ℝ}
    (hvol : 0 < vol) (hC : 0 ≤ C) (hExp : E.critExp ≤ decayExp)
    {θ : X → ℂ} (hθm : AEStronglyMeasurable θ μ)
    (hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * (E.H x) ^ (-decayExp)) :
    Integrable θ μ ∧ ‖thetaMean μ vol θ‖ ≤ vol⁻¹ * C * ∫ x, (E.H x) ^ (-E.critExp) ∂μ := by
  obtain ⟨hInt, _, hBound⟩ := thetaKernel_integrable_of_siegel_envelope E hC hExp hθm hθb
  refine ⟨hInt, ?_⟩
  rw [thetaMean, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hvol.le), mul_assoc]
  exact mul_le_mul_of_nonneg_left hBound (inv_nonneg.2 hvol.le)

/-- Clean finite-depth row-tower data (`ConvergenceOfSeparatingFamily` + `RapidDecayOfSeparatingFamily`),
carrying a Siegel-set envelope and rapid-decay bound at each stage `0 ≤ j ≤ depth`. -/
structure RowTowerEnvelope (depth : ℕ) where
  X : Fin (depth + 1) → Type*
  [mX : ∀ j, MeasurableSpace (X j)]
  μ : ∀ j, Measure (X j)
  env : ∀ j, SiegelSetEnvelope (μ j)
  θ : ∀ j, X j → ℂ
  C : Fin (depth + 1) → ℝ
  decayExp : Fin (depth + 1) → ℝ
  C_nonneg : ∀ j, 0 ≤ C j
  exp_ge : ∀ j, (env j).critExp ≤ decayExp j
  θ_meas : ∀ j, AEStronglyMeasurable (θ j) (μ j)
  θ_bound : ∀ j, ∀ᵐ x ∂(μ j), ‖θ j x‖ ≤ C j * ((env j).H x) ^ (-decayExp j)

attribute [instance] RowTowerEnvelope.mX

/-- Every stage of a `RowTowerEnvelope` converges absolutely with quantitative rapid-decay bound
(distilling `separating_family_converges` and `separating_family_rapid_decay`). -/
theorem RowTowerEnvelope.all_stages_converge {depth : ℕ} (T : RowTowerEnvelope depth) :
    ∀ j : Fin (depth + 1),
      Integrable (T.θ j) (T.μ j) ∧
        ‖∫ x, T.θ j x ∂(T.μ j)‖ ≤ T.C j * ∫ x, ((T.env j).H x) ^ (-(T.env j).critExp) ∂(T.μ j) := by
  intro j
  have h := thetaKernel_integrable_of_siegel_envelope (T.env j) (T.C_nonneg j) (T.exp_ge j)
    (T.θ_meas j) (T.θ_bound j)
  exact ⟨h.1, h.2.2⟩

/-- Product upper bound across all `depth + 1` stages of a convergent row tower. -/
theorem RowTowerEnvelope.prod_integral_le {depth : ℕ} (T : RowTowerEnvelope depth) :
    ∏ j : Fin (depth + 1), ‖∫ x, T.θ j x ∂(T.μ j)‖ ≤
      ∏ j : Fin (depth + 1), (T.C j * ∫ x, ((T.env j).H x) ^ (-(T.env j).critExp) ∂(T.μ j)) := by
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => (T.all_stages_converge j).2)

/-! ## Section 2: Regularized Siegel–Eisenstein Series, Constant & Second-Term Comparison -/

/-- Decomposition of a regularized Siegel–Eisenstein series at `s₀ = (m - n)/2` into its
constant term `c₀`, intertwining second term `c₁`, and non-degenerate Fourier tail `tail`. -/
structure SiegelEisensteinDecomp (G : Type*) where
  c0 : G → ℂ
  c1 : G → ℂ
  tail : G → ℂ

namespace SiegelEisensteinDecomp

def eval {G : Type*} (E : SiegelEisensteinDecomp G) (g : G) : ℂ :=
  E.c0 g + E.c1 g + E.tail g

/-- The Siegel–Weil identity equating the regularized Siegel–Eisenstein value `E.eval g` with
the regularized theta mean `thetaMean μ vol (Θ g)`. -/
def MatchesThetaMean {G X : Type*} [MeasurableSpace X]
    (E : SiegelEisensteinDecomp G) (μ : Measure X) (vol : ℝ) (Θ : G → X → ℂ) : Prop :=
  ∀ g : G, E.eval g = thetaMean μ vol (Θ g)

/-- Two-sided quantitative sandwich comparing `‖E(g)‖` against the constant term `‖c₀(g)‖`
under relative bounds on the second term `c₁` and higher Fourier tail. -/
theorem second_term_sandwich {G : Type*} (E : SiegelEisensteinDecomp G) (g : G)
    {ρ₁ ρ₂ : ℝ} (h1 : ‖E.c1 g‖ ≤ ρ₁ * ‖E.c0 g‖) (h2 : ‖E.tail g‖ ≤ ρ₂ * ‖E.c0 g‖) :
    (1 - (ρ₁ + ρ₂)) * ‖E.c0 g‖ ≤ ‖E.eval g‖ ∧ ‖E.eval g‖ ≤ (1 + (ρ₁ + ρ₂)) * ‖E.c0 g‖ := by
  have hRest : ‖E.c1 g + E.tail g‖ ≤ (ρ₁ + ρ₂) * ‖E.c0 g‖ := by
    calc ‖E.c1 g + E.tail g‖
        ≤ ‖E.c1 g‖ + ‖E.tail g‖ := norm_add_le _ _
      _ ≤ ρ₁ * ‖E.c0 g‖ + ρ₂ * ‖E.c0 g‖ := add_le_add h1 h2
      _ = (ρ₁ + ρ₂) * ‖E.c0 g‖ := by ring
  have hEq : E.eval g = E.c0 g + (E.c1 g + E.tail g) := by simp [eval, add_assoc]
  constructor
  · have hTri : ‖E.c0 g‖ ≤ ‖E.eval g‖ + ‖E.c1 g + E.tail g‖ := by
      have h0 : E.c0 g = E.eval g + (-(E.c1 g + E.tail g)) := by rw [hEq]; ring
      calc ‖E.c0 g‖
          = ‖E.eval g + (-(E.c1 g + E.tail g))‖ := by rw [h0]
        _ ≤ ‖E.eval g‖ + ‖-(E.c1 g + E.tail g)‖ := norm_add_le _ _
        _ = ‖E.eval g‖ + ‖E.c1 g + E.tail g‖ := by rw [norm_neg]
    linarith
  · rw [hEq]
    have hAdd : ‖E.c0 g + (E.c1 g + E.tail g)‖ ≤ ‖E.c0 g‖ + ‖E.c1 g + E.tail g‖ := norm_add_le _ _
    linarith

/-- Strict nonvanishing of the Siegel–Eisenstein series when the constant term dominates
the second term and Fourier tail (`ρ₁ + ρ₂ < 1`). -/
theorem ne_zero_of_dominant_constant {G : Type*} (E : SiegelEisensteinDecomp G) (g : G)
    {ρ₁ ρ₂ : ℝ} (hc0 : E.c0 g ≠ 0) (hρ : ρ₁ + ρ₂ < 1)
    (h1 : ‖E.c1 g‖ ≤ ρ₁ * ‖E.c0 g‖) (h2 : ‖E.tail g‖ ≤ ρ₂ * ‖E.c0 g‖) :
    0 < (1 - (ρ₁ + ρ₂)) * ‖E.c0 g‖ ∧ (1 - (ρ₁ + ρ₂)) * ‖E.c0 g‖ ≤ ‖E.eval g‖ ∧ E.eval g ≠ 0 := by
  have hpos : 0 < (1 - (ρ₁ + ρ₂)) * ‖E.c0 g‖ :=
    mul_pos (sub_pos.2 hρ) (norm_pos_iff.2 hc0)
  have hle := (E.second_term_sandwich g h1 h2).1
  have hne : E.eval g ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hpos hle)
  exact ⟨hpos, hle, hne⟩

/-- Normalized Siegel–Eisenstein ratio `E(g) / c₀(g)` stays within `ρ₁ + ρ₂` of `1`. -/
theorem ratio_close_one {G : Type*} (E : SiegelEisensteinDecomp G) (g : G)
    {ρ₁ ρ₂ : ℝ} (hc0 : E.c0 g ≠ 0)
    (h1 : ‖E.c1 g‖ ≤ ρ₁ * ‖E.c0 g‖) (h2 : ‖E.tail g‖ ≤ ρ₂ * ‖E.c0 g‖) :
    ‖E.eval g / E.c0 g - 1‖ ≤ ρ₁ + ρ₂ := by
  have hEq : E.eval g / E.c0 g - 1 = (E.c1 g + E.tail g) / E.c0 g := by
    unfold eval
    field_simp [hc0]
    ring
  rw [hEq, norm_div, div_le_iff₀ (norm_pos_iff.2 hc0)]
  calc ‖E.c1 g + E.tail g‖
      ≤ ‖E.c1 g‖ + ‖E.tail g‖ := norm_add_le _ _
    _ ≤ ρ₁ * ‖E.c0 g‖ + ρ₂ * ‖E.c0 g‖ := add_le_add h1 h2
    _ = (ρ₁ + ρ₂) * ‖E.c0 g‖ := by ring

/-- Combining the Siegel–Weil identity with constant-term dominance forces nonvanishing of the
regularized theta mean with explicit lower bound. -/
theorem thetaMean_ne_zero_of_siegelWeil {G X : Type*} [MeasurableSpace X]
    (E : SiegelEisensteinDecomp G) (μ : Measure X) (vol : ℝ) (Θ : G → X → ℂ)
    (hSW : E.MatchesThetaMean μ vol Θ) (g : G)
    {ρ₁ ρ₂ : ℝ} (hc0 : E.c0 g ≠ 0) (hρ : ρ₁ + ρ₂ < 1)
    (h1 : ‖E.c1 g‖ ≤ ρ₁ * ‖E.c0 g‖) (h2 : ‖E.tail g‖ ≤ ρ₂ * ‖E.c0 g‖) :
    (1 - (ρ₁ + ρ₂)) * ‖E.c0 g‖ ≤ ‖thetaMean μ vol (Θ g)‖ ∧ thetaMean μ vol (Θ g) ≠ 0 := by
  rw [← hSW g]
  have h := E.ne_zero_of_dominant_constant g hc0 hρ h1 h2
  exact ⟨h.2.1, h.2.2⟩

end SiegelEisensteinDecomp

/-- In the second-term convergence range (`n + r + 1 < m`), the second-term decay is suppressed
by an additional factor `H⁻¹` relative to the critical threshold `H^(-n)`. -/
theorem second_term_height_suppression {P : DualPairRanks} (hST : P.SecondTermRange)
    {H : ℝ} (hH : 1 ≤ H) :
    H ^ (-(P.effRank : ℝ)) ≤ H⁻¹ * H ^ (-(P.n : ℝ)) := by
  have hExp : (P.n : ℝ) + 1 ≤ (P.effRank : ℝ) := by
    exact_mod_cast (P.effRank_gt_n_add_one hST).le
  exact rpow_neg_le_inv_mul_rpow_neg hH hExp

/-- Global doubling zeta form across lattices, modeling `GlobalFormOfSiegelWeil.lean`'s
self-dual lattice transfer (`global_doubling_zeta_form_selfDual_lattice_transfer`). -/
structure DoublingZetaForm (Lat : Type*) where
  IsSelfDual : Lat → Prop
  zetaVal : Lat → ℂ
  transfer_factor : ∀ L₁ L₂, IsSelfDual L₁ → IsSelfDual L₂ → ∃ u : ℂ, u ≠ 0 ∧ zetaVal L₂ = u * zetaVal L₁

/-- Nonvanishing of a doubling zeta form at a canonical self-dual frame lattice transfers to
every self-dual lattice `L`. -/
theorem DoublingZetaForm.ne_zero_of_frameLat {Lat : Type*} (Z : DoublingZetaForm Lat)
    (frameLat : Lat) (hFrame : Z.IsSelfDual frameLat) (hNe : Z.zetaVal frameLat ≠ 0) :
    ∀ L, Z.IsSelfDual L → Z.zetaVal L ≠ 0 := by
  intro L hL
  obtain ⟨u, hu, hEq⟩ := Z.transfer_factor frameLat L hFrame hL
  rw [hEq]
  exact mul_ne_zero hu hNe

/-! ## Section 3: Unramified Howe Duality & Functional Separation (`FunctionalsSeparate`) -/

/-- Local unitary dual pair `(G₁, G₂)` with maximal compact subgroups `(K₁, K₂)` acting via a
Weil representation `ω : G₁ × G₂ →* End ℂ M` on a Fock/Schwartz space `M` with spherical vacuum
`vac` (distilling `HoweUnram.lean`). -/
structure UnramifiedDualPair where
  G₁ : Type
  G₂ : Type
  [grp₁ : Group G₁]
  [grp₂ : Group G₂]
  K₁ : Subgroup G₁
  K₂ : Subgroup G₂
  M : Type
  [addM : AddCommGroup M]
  [modM : Module ℂ M]
  ω : G₁ × G₂ →* Module.End ℂ M
  vac : M
  vac_ne_zero : vac ≠ 0
  vac_K₁_fixed : ∀ k ∈ K₁, ω (k, 1) vac = vac
  vac_K₂_fixed : ∀ k ∈ K₂, ω (1, k) vac = vac

attribute [instance] UnramifiedDualPair.grp₁ UnramifiedDualPair.grp₂
  UnramifiedDualPair.addM UnramifiedDualPair.modM

namespace UnramifiedDualPair

/-- Actions of `G₁` and `G₂` commute inside the product representation `ω : G₁ × G₂ →* End ℂ M`. -/
theorem omega_comm (P : UnramifiedDualPair) (g : P.G₁) (h : P.G₂) (v : P.M) :
    P.ω (g, 1) (P.ω (1, h) v) = P.ω (1, h) (P.ω (g, 1) v) := by
  have h1 : P.ω (g, 1) (P.ω (1, h) v) = P.ω ((g, 1) * (1, h)) v := by
    rw [map_mul]; rfl
  have h2 : P.ω (1, h) (P.ω (g, 1) v) = P.ω ((1, h) * (g, 1)) v := by
    rw [map_mul]; rfl
  rw [h1, h2]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

/-- The submodule of `K₁`-fixed vectors in `P.M`. -/
def fixedSubmodule₁ (P : UnramifiedDualPair) : Submodule ℂ P.M where
  carrier := {w | ∀ k ∈ P.K₁, P.ω (k, 1) w = w}
  add_mem' {a b} ha hb k hk := by rw [map_add, ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c {x} hx k hk := by rw [map_smul, hx k hk]

/-- The submodule of `K₂`-fixed vectors in `P.M`. -/
def fixedSubmodule₂ (P : UnramifiedDualPair) : Submodule ℂ P.M where
  carrier := {w | ∀ k ∈ P.K₂, P.ω (1, k) w = w}
  add_mem' {a b} ha hb k hk := by rw [map_add, ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c {x} hx k hk := by rw [map_smul, hx k hk]

/-- The `ℂ`-span of the `G₂`-orbit of the spherical vacuum `vac`. -/
def heckeSpan₂ (P : UnramifiedDualPair) : Submodule ℂ P.M :=
  Submodule.span ℂ (Set.range fun h : P.G₂ => P.ω (1, h) P.vac)

/-- The `ℂ`-span of the `G₁`-orbit of the spherical vacuum `vac`. -/
def heckeSpan₁ (P : UnramifiedDualPair) : Submodule ℂ P.M :=
  Submodule.span ℂ (Set.range fun g : P.G₁ => P.ω (g, 1) P.vac)

/-- `P.fixedSubmodule₁` is automatically stable under the entire commuting group `G₂`. -/
theorem fixedSubmodule₁_G₂_invariant (P : UnramifiedDualPair) (h : P.G₂)
    {w : P.M} (hw : w ∈ P.fixedSubmodule₁) : P.ω (1, h) w ∈ P.fixedSubmodule₁ := by
  intro k hk
  rw [P.omega_comm k h w, hw k hk]

/-- `P.fixedSubmodule₂` is automatically stable under the entire commuting group `G₁`. -/
theorem fixedSubmodule₂_G₁_invariant (P : UnramifiedDualPair) (g : P.G₁)
    {w : P.M} (hw : w ∈ P.fixedSubmodule₂) : P.ω (g, 1) w ∈ P.fixedSubmodule₂ := by
  intro k hk
  rw [← P.omega_comm g k w, hw k hk]

/-- Unconditionally, the `G₂`-orbit span of the spherical vacuum lies inside `fixedSubmodule₁`. -/
theorem heckeSpan₂_le_fixedSubmodule₁ (P : UnramifiedDualPair) :
    P.heckeSpan₂ ≤ P.fixedSubmodule₁ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, rfl⟩
  exact P.fixedSubmodule₁_G₂_invariant h P.vac_K₁_fixed

/-- Unconditionally, the `G₁`-orbit span of the spherical vacuum lies inside `fixedSubmodule₂`. -/
theorem heckeSpan₁_le_fixedSubmodule₂ (P : UnramifiedDualPair) :
    P.heckeSpan₁ ≤ P.fixedSubmodule₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact P.fixedSubmodule₂_G₁_invariant g P.vac_K₂_fixed

/-- **Unramified Howe Duality** (`HoweUnram.lean`): every `K₁`-fixed vector lies in the
`G₂`-orbit span of the spherical vacuum, and symmetrically for `K₂` and `G₁`. -/
def HoweUnram (P : UnramifiedDualPair) : Prop :=
  P.fixedSubmodule₁ ≤ P.heckeSpan₂ ∧ P.fixedSubmodule₂ ≤ P.heckeSpan₁

theorem howeUnram_iff_eq (P : UnramifiedDualPair) :
    P.HoweUnram ↔ P.fixedSubmodule₁ = P.heckeSpan₂ ∧ P.fixedSubmodule₂ = P.heckeSpan₁ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_antisymm h1 P.heckeSpan₂_le_fixedSubmodule₁,
           le_antisymm h2 P.heckeSpan₁_le_fixedSubmodule₂⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.le, h2.le⟩

/-- Exact image equality under unramified Howe duality: the image of `P.fixedSubmodule₁`
under any `ℂ`-linear theta-lift map `L` equals the `ℂ`-span of the `G₂`-orbit of `L vac`. -/
theorem map_fixedSubmodule₁_eq_orbit_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : UnramifiedDualPair) (hHowe : P.HoweUnram) (L : P.M →ₗ[ℂ] V) :
    Submodule.map L P.fixedSubmodule₁ =
      Submodule.span ℂ (Set.range fun h : P.G₂ => L (P.ω (1, h) P.vac)) := by
  rw [(P.howeUnram_iff_eq.1 hHowe).1, heckeSpan₂, Submodule.map_span, ← Set.range_comp]
  rfl

/-- **Core Surjectivity from Unramified Howe Duality & Siegel–Weil Nonvanishing**
(distilling `TwistCoreSurjectiveOfLocalComponents.lean`):
If `P.HoweUnram` holds and the `ℂ`-linear theta-lift map `L : P.M →ₗ[ℂ] V` maps the `G₂`-orbit
of the spherical vacuum to a spanning set of `V` (supplied by Siegel–Weil convergence + doubling
zeta nonvanishing), then `L` restricted to `P.fixedSubmodule₁` is surjective onto `V`. -/
theorem core_surjective_of_howeUnram {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : UnramifiedDualPair) (hHowe : P.HoweUnram) (L : P.M →ₗ[ℂ] V)
    (hSpan : Submodule.span ℂ (Set.range fun h : P.G₂ => L (P.ω (1, h) P.vac)) = ⊤) :
    ∀ v : V, ∃ w ∈ P.fixedSubmodule₁, L w = v := by
  intro v
  have hv : v ∈ Submodule.map L P.fixedSubmodule₁ := by
    rw [P.map_fixedSubmodule₁_eq_orbit_span hHowe L, hSpan]
    trivial
  exact Submodule.mem_map.1 hv

/-- Conversely, every `K₁`-fixed lift `L w` lies in the `G₂`-orbit span under `HoweUnram`. -/
theorem lift_fixed₁_mem_orbit_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : UnramifiedDualPair) (hHowe : P.HoweUnram) (L : P.M →ₗ[ℂ] V)
    {w : P.M} (hw : w ∈ P.fixedSubmodule₁) :
    L w ∈ Submodule.span ℂ (Set.range fun h : P.G₂ => L (P.ω (1, h) P.vac)) := by
  rw [← P.map_fixedSubmodule₁_eq_orbit_span hHowe L]
  exact Submodule.mem_map_of_mem hw

end UnramifiedDualPair

/-- Abstract Bessel-theta functional pairing family over a multiplicity space `E`, column forms
`Cols ⊆ C`, and Schwartz/Fock test data `Datum` (distilling `LevelPlusSubgroup.lean`). -/
structure FunctionalFamily (E C Datum : Type*) [AddCommGroup E] [Module ℂ E] where
  Cols : Set C
  FConv : C → Datum → E → Prop
  eval : C → Datum → (E →ₗ[ℂ] ℂ)

namespace FunctionalFamily

variable {E C Datum : Type*} [AddCommGroup E] [Module ℂ E]

/-- Pointwise functional separation on a submodule `S ≤ E` (`LevelPlusSubgroup.Separates`). -/
def Separates (F : FunctionalFamily E C Datum) (S : Submodule ℂ E) : Prop :=
  ∀ t ∈ S, t ≠ 0 → ∃ Ψ ∈ F.Cols, ∃ Φ : Datum, F.FConv Ψ Φ t ∧ F.eval Ψ Φ t ≠ 0

/-- Finite-span functional separation (`LevelPlusSubgroup.SeparatesSpan`). -/
def SeparatesSpan (F : FunctionalFamily E C Datum) (S : Submodule ℂ E) : Prop :=
  ∀ t ∈ S, t ≠ 0 → ∃ Ψ ∈ F.Cols, ∃ c : Datum →₀ ℂ,
    (∀ Φ ∈ c.support, F.FConv Ψ Φ t) ∧ (c.sum fun Φ a => a * F.eval Ψ Φ t) ≠ 0

/-- **Exact equivalence `Separates ↔ SeparatesSpan`**: a finite linear combination of converging
test-vector functionals separates `t ≠ 0` iff a single converging test vector does. -/
theorem separates_iff_separatesSpan (F : FunctionalFamily E C Datum) (S : Submodule ℂ E) :
    F.Separates S ↔ F.SeparatesSpan S := by
  constructor
  · intro h t ht hne
    obtain ⟨Ψ, hΨ, Φ, hConv, hVal⟩ := h t ht hne
    refine ⟨Ψ, hΨ, Finsupp.single Φ (1 : ℂ), ?_, ?_⟩
    · intro Φ' hΦ'
      have hEq : Φ' = Φ := by
        have := Finsupp.support_single_subset hΦ'
        simpa using this
      subst hEq
      exact hConv
    · simp [Finsupp.sum_single_index, hVal]
  · intro h t ht hne
    obtain ⟨Ψ, hΨ, c, hConv, hSum⟩ := h t ht hne
    by_contra hAll
    push Not at hAll
    apply hSum
    rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun Φ hΦ => ?_
    have h0 := hAll Ψ hΨ Φ (hConv Φ hΦ)
    simp [h0]

/-- Triviality when the evaluation functional vanishes identically (exact generalization of the
sanity-check `example` in `LevelPlusSubgroup.lean`). -/
theorem eq_bot_of_separates_zero (F : FunctionalFamily E C Datum) (S : Submodule ℂ E)
    (hZero : ∀ Ψ ∈ F.Cols, ∀ Φ, F.eval Ψ Φ = 0) (hSep : F.Separates S) :
    S = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro t ht
  by_contra hne
  obtain ⟨Ψ, hΨ, Φ, -, hVal⟩ := hSep t ht hne
  exact hVal (by simp [hZero Ψ hΨ Φ])

/-- Injectivity of the evaluation map on `S` (`injK_of_separates`, used in
`FittedFunctionAtZeroClose.lean`). -/
theorem inj_of_separates (F : FunctionalFamily E C Datum) (S : Submodule ℂ E)
    (hSep : F.Separates S) {t₁ t₂ : E} (ht₁ : t₁ ∈ S) (ht₂ : t₂ ∈ S)
    (hEq : ∀ Ψ ∈ F.Cols, ∀ Φ, F.eval Ψ Φ t₁ = F.eval Ψ Φ t₂) :
    t₁ = t₂ := by
  by_contra hne
  have hsub : t₁ - t₂ ∈ S := S.sub_mem ht₁ ht₂
  have hsub_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨Ψ, hΨ, Φ, -, hVal⟩ := hSep (t₁ - t₂) hsub hsub_ne
  apply hVal
  rw [map_sub, hEq Ψ hΨ Φ, sub_self]

/-- Characterization of `Separates` via trivial kernel intersection when convergence holds on `S`. -/
theorem separates_iff_ker_inf_eq_bot (F : FunctionalFamily E C Datum) (S : Submodule ℂ E)
    (hConvAll : ∀ Ψ ∈ F.Cols, ∀ Φ, ∀ t ∈ S, F.FConv Ψ Φ t) :
    F.Separates S ↔ (⨅ (Ψ : F.Cols) (Φ : Datum), LinearMap.ker (F.eval Ψ.1 Φ)) ⊓ S = ⊥ := by
  constructor
  · intro hSep
    rw [Submodule.eq_bot_iff]
    intro t ht
    obtain ⟨hKer, htS⟩ := Submodule.mem_inf.1 ht
    by_contra hne
    obtain ⟨Ψ, hΨ, Φ, -, hVal⟩ := hSep t htS hne
    have hmem : t ∈ LinearMap.ker (F.eval Ψ Φ) := by
      rw [Submodule.mem_iInf] at hKer
      have h1 := hKer ⟨Ψ, hΨ⟩
      rw [Submodule.mem_iInf] at h1
      exact h1 Φ
    exact hVal hmem
  · intro hBot t htS hne
    by_contra hAll
    push Not at hAll
    have hKer : t ∈ ⨅ (Ψ : F.Cols) (Φ : Datum), LinearMap.ker (F.eval Ψ.1 Φ) := by
      rw [Submodule.mem_iInf]
      intro Ψ
      rw [Submodule.mem_iInf]
      intro Φ
      exact hAll Ψ.1 Ψ.2 Φ (hConvAll Ψ.1 Ψ.2 Φ t htS)
    have hZero : t = 0 := (Submodule.eq_bot_iff _).1 hBot t (Submodule.mem_inf.2 ⟨hKer, htS⟩)
    exact hne hZero

theorem separates_mono (F : FunctionalFamily E C Datum) {S₁ S₂ : Submodule ℂ E}
    (hle : S₁ ≤ S₂) (hSep : F.Separates S₂) : F.Separates S₁ :=
  fun t ht hne => hSep t (hle ht) hne

end FunctionalFamily

/-- **Bessel Eigenvalue-Gap Component Isolation** (Lagrange spectral projection for `BesselSeparate`):
If a vector `t = ∑ i : Fin k, v i` decomposes into eigenvectors `T (v i) = λ i • v i` of a
Hecke/Bessel operator `T : End ℂ E` with pairwise distinct eigenvalues `λ : Fin k → ℂ`, then the
explicit finite operator product `∏ j ≠ i, (λ i - λ j)⁻¹ • (T - λ j • 1)` isolates `v i` exactly! -/
theorem bessel_gap_isolates_component {E : Type*} [AddCommGroup E] [Module ℂ E]
    {k : ℕ} (T : Module.End ℂ E) (lam : Fin k → ℂ) (v : Fin k → E)
    (hGap : Function.Injective lam)
    (hEig : ∀ i : Fin k, T (v i) = lam i • v i) (i₀ : Fin k) :
    ∃ L : Module.End ℂ E, L (∑ i : Fin k, v i) = v i₀ := by
  classical
  -- Inductively build the spectral projector on any subset `s : Finset (Fin k)` not containing `i₀`.
  have hSub : ∀ s : Finset (Fin k), i₀ ∉ s →
      ∃ L : Module.End ℂ E, L (v i₀) = v i₀ ∧ ∀ j ∈ s, L (v j) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨LinearMap.id, rfl, fun j hj => absurd hj (Finset.notMem_empty j)⟩
    | @insert a s ha ih =>
      intro hi₀
      have hi₀a : i₀ ≠ a := fun h => hi₀ (h ▸ Finset.mem_insert_self a s)
      have hi₀s : i₀ ∉ s := fun h => hi₀ (Finset.mem_insert_of_mem h)
      obtain ⟨L, hLi₀, hLs⟩ := ih hi₀s
      have hdiff : lam i₀ - lam a ≠ 0 := sub_ne_zero.2 fun h => hi₀a (hGap h)
      let step : Module.End ℂ E := (lam i₀ - lam a)⁻¹ • (T - lam a • LinearMap.id)
      refine ⟨L.comp step, ?_, ?_⟩
      · have hStep_i₀ : step (v i₀) = v i₀ := by
          simp only [step, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, hEig i₀]
          rw [← sub_smul, smul_smul, inv_mul_cancel₀ hdiff, one_smul]
        simp only [LinearMap.comp_apply, hStep_i₀, hLi₀]
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hjs
        · have hStep_j : step (v j) = 0 := by
            simp only [step, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, hEig j,
              sub_self, smul_zero]
          simp only [LinearMap.comp_apply, hStep_j, map_zero]
        · have hStep_j : step (v j) = ((lam i₀ - lam a)⁻¹ * (lam j - lam a)) • v j := by
            simp only [step, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, hEig j]
            rw [← sub_smul, smul_smul]
          simp only [LinearMap.comp_apply, hStep_j, map_smul, hLs j hjs, smul_zero]
  obtain ⟨L, hLi₀, hRest⟩ := hSub (Finset.univ.erase i₀) (Finset.notMem_erase i₀ _)
  refine ⟨L, ?_⟩
  rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hLi₀]
  have hZero : ∑ j ∈ Finset.univ.erase i₀, L (v j) = 0 :=
    Finset.sum_eq_zero fun j hj => hRest j hj
  rw [hZero, add_zero]

/-- **Minimal Live Separation Inputs** (strictly omitting ALL 33 dead fields of `ThetaLocalInputs`
and ALL 13 dead fields of `UnitaryGroupThirdPlaceHypotheses`). -/
structure LiveSiegelWeilSeparationData
    (E C Datum : Type*) [AddCommGroup E] [Module ℂ E] where
  pair : UnramifiedDualPair
  V : Type
  [addV : AddCommGroup V]
  [modV : Module ℂ V]
  thetaLift : pair.M →ₗ[ℂ] V
  fam : FunctionalFamily E C Datum
  S : Submodule ℂ E
  /-- Realization of each `K₁`-fixed lift vector as a converging column/datum pair. -/
  realize : pair.M → C × Datum
  realize_mem : ∀ w ∈ pair.fixedSubmodule₁, (realize w).1 ∈ fam.Cols
  realize_conv : ∀ w ∈ pair.fixedSubmodule₁, ∀ t ∈ S, fam.FConv (realize w).1 (realize w).2 t
  /-- Archimedian / real-period pairing factoring through the theta lift `thetaLift`. -/
  periodPairing : V → E → ℂ
  period_agrees : ∀ w ∈ pair.fixedSubmodule₁, ∀ t ∈ S,
    fam.eval (realize w).1 (realize w).2 t = periodPairing (thetaLift w) t
  /-- Archimedean real period nonvanishing (`Branch.periodNe_of_eigen`): every nonzero `t ∈ S`
  is detected by some target vector `v ∈ V`. -/
  realPeriodNonvanishing : ∀ t ∈ S, t ≠ 0 → ∃ v : V, periodPairing v t ≠ 0

attribute [instance] LiveSiegelWeilSeparationData.addV LiveSiegelWeilSeparationData.modV

/-- **`functionalsSeparate_of_howeUnram_of_siegelWeil`** (clean, dead-field-free rebuild of
`LocalTypeDictionary/FunctionalsSeparateOfHoweUnramOfSiegelWeil.lean` +
`RealFunctionalsSeparateOfHypothesis.lean`):
Unramified Howe duality + Siegel–Weil orbit spanning (core surjectivity) + real period
nonvanishing + convergent row realization imply `FunctionalsSeparate` (`fam.Separates S`)
with ZERO dead `ThetaLocalInputs` fields. -/
theorem functionalsSeparate_of_howeUnram_of_siegelWeil
    {E C Datum : Type*} [AddCommGroup E] [Module ℂ E]
    (D : LiveSiegelWeilSeparationData E C Datum)
    (hHowe : D.pair.HoweUnram)
    (hSiegelWeilSpan :
      Submodule.span ℂ (Set.range fun h : D.pair.G₂ => D.thetaLift (D.pair.ω (1, h) D.pair.vac)) = ⊤) :
    D.fam.Separates D.S := by
  intro t htS hne
  obtain ⟨v, hv⟩ := D.realPeriodNonvanishing t htS hne
  obtain ⟨w, hwFixed, hwLift⟩ := D.pair.core_surjective_of_howeUnram hHowe D.thetaLift hSiegelWeilSpan v
  refine ⟨(D.realize w).1, D.realize_mem w hwFixed, (D.realize w).2,
    D.realize_conv w hwFixed t htS, ?_⟩
  rw [D.period_agrees w hwFixed t htS, hwLift]
  exact hv

/-! ## Section 4: Heisenberg/Fourier Extraction, `fourier_coefficient_fit`, `rowRatW_of_rowTest` & Assembly -/

/-- Orthogonality of a nontrivial additive character `χ ≠ 1` on a finite abelian group `A`:
`∑ a : A, χ a = 0`. -/
theorem sum_addChar_eq_zero_of_ne_one {A : Type*} [AddCommGroup A] [Fintype A]
    (χ : AddChar A ℂ) (hχ : χ ≠ 1) :
    ∑ a : A, χ a = 0 := by
  have hEx : ∃ b : A, χ b ≠ 1 := by
    by_contra hAll
    push Not at hAll
    apply hχ
    ext a
    exact hAll a
  obtain ⟨b, hb⟩ := hEx
  have hShift : χ b * ∑ a : A, χ a = ∑ a : A, χ a := by
    rw [Finset.mul_sum]
    calc ∑ a : A, χ b * χ a
        = ∑ a : A, χ (b + a) := by
            refine Finset.sum_congr rfl fun a _ => (AddChar.map_add_eq_mul χ b a).symm
      _ = ∑ a : A, χ a := Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun _ => rfl)
  have hMul : (χ b - 1) * ∑ a : A, χ a = 0 := by linear_combination hShift
  exact (mul_eq_zero.1 hMul).resolve_left (sub_ne_zero.2 hb)

/-- Exact orthogonality of unitary additive characters on a finite abelian group `A`
(`star (χ a) = χ (-a)`). -/
theorem addChar_orthogonality {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq (AddChar A ℂ)]
    (χ₁ χ₂ : AddChar A ℂ) (hU₁ : ∀ a : A, star (χ₁ a) = χ₁ (-a)) :
    ∑ a : A, star (χ₁ a) * χ₂ a = if χ₁ = χ₂ then (Fintype.card A : ℂ) else 0 := by
  by_cases hEq : χ₁ = χ₂
  · subst hEq
    rw [if_pos rfl]
    have hOne : ∀ a : A, star (χ₁ a) * χ₁ a = 1 := fun a => by
      rw [hU₁ a, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc ∑ a : A, star (χ₁ a) * χ₁ a
        = ∑ _a : A, (1 : ℂ) := Finset.sum_congr rfl fun a _ => hOne a
      _ = (Fintype.card A : ℂ) := by simp
  · rw [if_neg hEq]
    let ψ : AddChar A ℂ := (-χ₁) + χ₂
    have hψ_apply : ∀ a : A, ψ a = star (χ₁ a) * χ₂ a := fun a => by
      change (χ₁ (-a)) * χ₂ a = star (χ₁ a) * χ₂ a
      rw [hU₁ a]
    have hψ_ne : ψ ≠ 1 := by
      intro h1
      apply hEq
      ext a
      have ha : ψ a = 1 := by rw [h1]; rfl
      rw [hψ_apply a, hU₁ a] at ha
      calc χ₁ a = χ₁ a * 1 := (mul_one _).symm
        _ = χ₁ a * (χ₁ (-a) * χ₂ a) := by rw [ha]
        _ = (χ₁ a * χ₁ (-a)) * χ₂ a := by ring
        _ = χ₁ (a + -a) * χ₂ a := by rw [AddChar.map_add_eq_mul]
        _ = χ₂ a := by simp [add_neg_cancel]
    calc ∑ a : A, star (χ₁ a) * χ₂ a
        = ∑ a : A, ψ a := Finset.sum_congr rfl fun a _ => (hψ_apply a).symm
      _ = 0 := sum_addChar_eq_zero_of_ne_one ψ hψ_ne

/-- Exact Fourier-coefficient recovery from a finite Heisenberg/character expansion
(algebraic core of `BottomFourierCoeffHeisenbergExpansion.lean`). -/
theorem fourier_coeff_extract {A ι : Type*} [AddCommGroup A] [Fintype A] [Nonempty A]
    [DecidableEq ι] (S : Finset ι) (c : ι → ℂ) (χ : ι → AddChar A ℂ)
    (hInj : Set.InjOn χ (S : Set ι))
    (hUnit : ∀ i ∈ S, ∀ a : A, star (χ i a) = χ i (-a))
    (f : A → ℂ) (hExp : ∀ a : A, f a = ∑ i ∈ S, c i * χ i a)
    {j : ι} (hj : j ∈ S) :
    ((Fintype.card A : ℂ)⁻¹) * ∑ a : A, star (χ j a) * f a = c j := by
  classical
  have hCardNe : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hSum : ∑ a : A, star (χ j a) * f a = (Fintype.card A : ℂ) * c j := by
    calc ∑ a : A, star (χ j a) * f a
        = ∑ a : A, ∑ i ∈ S, c i * (star (χ j a) * χ i a) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hExp a, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ S, c i * ∑ a : A, star (χ j a) * χ i a := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ i ∈ S, c i * (if χ j = χ i then (Fintype.card A : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [addChar_orthogonality (χ j) (χ i) (hUnit j hj)]
      _ = ∑ i ∈ S, (if i = j then c j * (Fintype.card A : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            by_cases hij : i = j
            · subst hij; simp
            · have hne : χ j ≠ χ i := fun h => hij (hInj hi hj h.symm)
              simp [hij, hne]
      _ = c j * (Fintype.card A : ℂ) := by simp [hj]
      _ = (Fintype.card A : ℂ) * c j := mul_comm _ _
  rw [hSum, ← mul_assoc, inv_mul_cancel₀ hCardNe, one_mul]

/-- Quantitative Fourier-coefficient matching data comparing an automorphic expansion `a` against
a Siegel–Weil / theta-lift expansion `b` with leading coefficient `a i₀`
(distilling `FourierCoefficientFitOfJoin.lean` & `FittedFunctionAtZeroClose.lean`). -/
structure FourierFitData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  i₀ : ι
  a : ι → ℂ
  b : ι → ℂ
  lamLow : ℝ
  lamLow_pos : 0 < lamLow
  leading_ge : lamLow ≤ ‖a i₀‖
  δ_loc : ℝ
  δ_loc_nonneg : 0 ≤ δ_loc
  local_match : ∀ i : ι, ‖b i - a i‖ ≤ δ_loc * ‖a i‖
  ε_tail : ℝ
  ε_tail_nonneg : 0 ≤ ε_tail
  tail_bound : ∑ i ∈ Finset.univ.erase i₀, ‖a i‖ ≤ ε_tail * ‖a i₀‖

namespace FourierFitData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation at the origin `∑ i, c i`. -/
def evalAtZero (c : ι → ℂ) : ℂ := ∑ i : ι, c i

/-- Total relative fitting error `ε_tail + δ_loc * (1 + ε_tail)`. -/
def totalError (F : FourierFitData ι) : ℝ := F.ε_tail + F.δ_loc * (1 + F.ε_tail)

theorem leading_ne_zero (F : FourierFitData ι) : F.a F.i₀ ≠ 0 :=
  norm_pos_iff.1 (lt_of_lt_of_le F.lamLow_pos F.leading_ge)

theorem totalError_nonneg (F : FourierFitData ι) : 0 ≤ F.totalError := by
  unfold totalError
  have h1 := F.ε_tail_nonneg
  have h2 := F.δ_loc_nonneg
  nlinarith

/-- **`fourier_coefficient_fit`** (clean, quantitative core of `fourier_coefficient_fit_of_join`):
1. Automorphic evaluation approximates the leading coefficient within `ε_tail * ‖a i₀‖`.
2. Global matching discrepancy `‖evalAtZero b - evalAtZero a‖ ≤ δ_loc * (1 + ε_tail) * ‖a i₀‖`.
3. Constant-function fit at the origin: `‖evalAtZero b - a i₀‖ ≤ totalError * ‖a i₀‖`.
4. Normalized ratio bound: `‖evalAtZero b / a i₀ - 1‖ ≤ totalError`. -/
theorem fourier_coefficient_fit (F : FourierFitData ι) :
    ‖evalAtZero F.a - F.a F.i₀‖ ≤ F.ε_tail * ‖F.a F.i₀‖ ∧
    ‖evalAtZero F.b - evalAtZero F.a‖ ≤ F.δ_loc * (1 + F.ε_tail) * ‖F.a F.i₀‖ ∧
    ‖evalAtZero F.b - F.a F.i₀‖ ≤ F.totalError * ‖F.a F.i₀‖ ∧
    ‖evalAtZero F.b / F.a F.i₀ - 1‖ ≤ F.totalError := by
  have hSplitA : evalAtZero F.a - F.a F.i₀ = ∑ i ∈ Finset.univ.erase F.i₀, F.a i := by
    unfold evalAtZero
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ F.i₀)]
    ring
  have h1 : ‖evalAtZero F.a - F.a F.i₀‖ ≤ F.ε_tail * ‖F.a F.i₀‖ := by
    rw [hSplitA]
    exact le_trans (norm_sum_le _ _) F.tail_bound
  have hSumNormA : ∑ i : ι, ‖F.a i‖ ≤ (1 + F.ε_tail) * ‖F.a F.i₀‖ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ F.i₀)]
    linarith [F.tail_bound]
  have h2 : ‖evalAtZero F.b - evalAtZero F.a‖ ≤ F.δ_loc * (1 + F.ε_tail) * ‖F.a F.i₀‖ := by
    have hSub : evalAtZero F.b - evalAtZero F.a = ∑ i : ι, (F.b i - F.a i) := by
      unfold evalAtZero
      rw [Finset.sum_sub_distrib]
    rw [hSub]
    calc ‖∑ i : ι, (F.b i - F.a i)‖
        ≤ ∑ i : ι, ‖F.b i - F.a i‖ := norm_sum_le _ _
      _ ≤ ∑ i : ι, F.δ_loc * ‖F.a i‖ := Finset.sum_le_sum fun i _ => F.local_match i
      _ = F.δ_loc * ∑ i : ι, ‖F.a i‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ F.δ_loc * ((1 + F.ε_tail) * ‖F.a F.i₀‖) :=
          mul_le_mul_of_nonneg_left hSumNormA F.δ_loc_nonneg
      _ = F.δ_loc * (1 + F.ε_tail) * ‖F.a F.i₀‖ := by ring
  have h3 : ‖evalAtZero F.b - F.a F.i₀‖ ≤ F.totalError * ‖F.a F.i₀‖ := by
    have hTri : evalAtZero F.b - F.a F.i₀ =
        (evalAtZero F.b - evalAtZero F.a) + (evalAtZero F.a - F.a F.i₀) := by ring
    rw [hTri]
    calc ‖(evalAtZero F.b - evalAtZero F.a) + (evalAtZero F.a - F.a F.i₀)‖
        ≤ ‖evalAtZero F.b - evalAtZero F.a‖ + ‖evalAtZero F.a - F.a F.i₀‖ := norm_add_le _ _
      _ ≤ F.δ_loc * (1 + F.ε_tail) * ‖F.a F.i₀‖ + F.ε_tail * ‖F.a F.i₀‖ := add_le_add h2 h1
      _ = F.totalError * ‖F.a F.i₀‖ := by unfold totalError; ring
  have h4 : ‖evalAtZero F.b / F.a F.i₀ - 1‖ ≤ F.totalError := by
    have hne := F.leading_ne_zero
    have hEq : evalAtZero F.b / F.a F.i₀ - 1 = (evalAtZero F.b - F.a F.i₀) / F.a F.i₀ := by
      field_simp [hne]
    rw [hEq, norm_div, div_le_iff₀ (norm_pos_iff.2 hne)]
    exact h3
  exact ⟨h1, h2, h3, h4⟩

/-- Nonvanishing and explicit positive lower bound for `evalAtZero F.b` whenever `totalError < 1`. -/
theorem evalAtZero_ne_zero (F : FourierFitData ι) (hErr : F.totalError < 1) :
    (1 - F.totalError) * F.lamLow ≤ ‖evalAtZero F.b‖ ∧ evalAtZero F.b ≠ 0 := by
  have hFit := F.fourier_coefficient_fit.2.2.1
  have hDiff : ‖F.a F.i₀‖ - ‖evalAtZero F.b‖ ≤ ‖evalAtZero F.b - F.a F.i₀‖ := by
    have := abs_norm_sub_norm_le (F.a F.i₀) (evalAtZero F.b)
    rw [norm_sub_rev] at this
    linarith [(abs_le.1 this).2]
  have hLow : (1 - F.totalError) * ‖F.a F.i₀‖ ≤ ‖evalAtZero F.b‖ := by linarith
  have hLowLam : (1 - F.totalError) * F.lamLow ≤ ‖evalAtZero F.b‖ :=
    le_trans (mul_le_mul_of_nonneg_left F.leading_ge (sub_nonneg.2 hErr.le)) hLow
  have hPos : 0 < (1 - F.totalError) * F.lamLow := mul_pos (sub_pos.2 hErr) F.lamLow_pos
  exact ⟨hLowLam, norm_pos_iff.1 (lt_of_lt_of_le hPos hLowLam)⟩

end FourierFitData

/-- Clean monotonicity / transport predicate replacing the nested `StepW`/`AtDat` wrappers of
`IwasawaDecomposition/RowRatWOfRowTest.lean`. -/
def StepImplies {α : Type*} (P Q : α → Prop) : Prop := ∀ x : α, P x → Q x

theorem StepImplies.trans {α : Type*} {P Q R : α → Prop}
    (h1 : StepImplies P Q) (h2 : StepImplies Q R) : StepImplies P R :=
  fun x hx => h2 x (h1 x hx)

/-- **`rowRatW_of_rowTest`** (direct dead-wrapper-free rebuild of `RowRatWOfRowTest.lean`):
Pointwise `RowTest` over `Pinned` data immediately transports to `RowRat` over `Start` data. -/
theorem rowRatW_of_rowTest {α : Type*} {Start Pinned RowTest RowRat : α → Prop}
    (hPin : StepImplies Start Pinned)
    (hRat : StepImplies RowTest RowRat)
    (hTest : StepImplies Pinned RowTest) :
    StepImplies Start RowRat :=
  (hPin.trans hTest).trans hRat

/-- Unified dead-field-free output of `SiegelEisensteinSecondTermHypotheses` at the joined
threshold `CF = max CF₀ CF₁`. -/
structure DefiniteSideAssembly
    (E C Datum α ι : Type*) [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (D : LiveSiegelWeilSeparationData E C Datum)
    (Start RowRat : α → Prop)
    (F : FourierFitData ι)
    (EvGrid RowFun : ℝ → Prop) : Prop where
  funcSep : D.fam.Separates D.S
  rowRat : StepImplies Start RowRat
  fourierFit : ‖FourierFitData.evalAtZero F.b - F.a F.i₀‖ ≤ F.totalError * ‖F.a F.i₀‖
  fourierNeZero : FourierFitData.evalAtZero F.b ≠ 0
  joinedThreshold : ∃ CF : ℝ, EvGrid CF ∧ RowFun CF

/-- **Unified Siegel–Eisenstein Second-Term Definite-Side Assembly** (clean rebuild of
`SiegelEisensteinSecondTermHypotheses.nonempty_hyps_definite_side_of_closed_bound` without
any `_alt` clones or dead fields):
Combines `functionalsSeparate_of_howeUnram_of_siegelWeil`, `rowRatW_of_rowTest`,
`fourier_coefficient_fit`, and `max CF₀ CF₁` threshold joining into one direct theorem. -/
theorem siegel_eisenstein_second_term_assembly
    {E C Datum α ι : Type*} [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (D : LiveSiegelWeilSeparationData E C Datum)
    (hHowe : D.pair.HoweUnram)
    (hSiegelWeilSpan :
      Submodule.span ℂ (Set.range fun h : D.pair.G₂ => D.thetaLift (D.pair.ω (1, h) D.pair.vac)) = ⊤)
    {Start Pinned RowTest RowRat : α → Prop}
    (hPin : StepImplies Start Pinned)
    (hRat : StepImplies RowTest RowRat)
    (hTestOfSep : D.fam.Separates D.S → StepImplies Pinned RowTest)
    (F : FourierFitData ι) (hErr : F.totalError < 1)
    {EvGrid RowFun : ℝ → Prop}
    (hGrid : D.fam.Separates D.S → ∃ CF₁ : ℝ, ∀ CF ≥ CF₁, EvGrid CF)
    (hFun : ‖FourierFitData.evalAtZero F.b - F.a F.i₀‖ ≤ F.totalError * ‖F.a F.i₀‖ →
      ∃ CF₀ : ℝ, ∀ CF ≥ CF₀, RowFun CF) :
    DefiniteSideAssembly E C Datum α ι D Start RowRat F EvGrid RowFun := by
  have hSep : D.fam.Separates D.S :=
    functionalsSeparate_of_howeUnram_of_siegelWeil D hHowe hSiegelWeilSpan
  have hRow : StepImplies Start RowRat :=
    rowRatW_of_rowTest hPin hRat (hTestOfSep hSep)
  have hFit : ‖FourierFitData.evalAtZero F.b - F.a F.i₀‖ ≤ F.totalError * ‖F.a F.i₀‖ :=
    F.fourier_coefficient_fit.2.2.1
  have hNe : FourierFitData.evalAtZero F.b ≠ 0 :=
    (F.evalAtZero_ne_zero hErr).2
  obtain ⟨CF₁, hCF₁⟩ := hGrid hSep
  obtain ⟨CF₀, hCF₀⟩ := hFun hFit
  exact ⟨hSep, hRow, hFit, hNe, ⟨max CF₀ CF₁,
    hCF₁ (max CF₀ CF₁) (le_max_right _ _),
    hCF₀ (max CF₀ CF₁) (le_max_left _ _)⟩⟩

end RHDirect.SiegelWeilCore

end
