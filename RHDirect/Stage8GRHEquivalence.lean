import RHDirect.Stage8HadamardLFunction
import RHDirect.Stage7VonMangoldtExplicit
import RHDirect.Stage7PNTInAP
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# RHDirect.Stage8GRHEquivalence

Completely **UNCONDITIONAL** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) Stage 8 formalization
directly on Mathlib's actual `DirichletCharacter.LFunction`, `DirichletCharacter.completedLFunction`,
`Stage2DirichletAP.chebyshevPsiAP`, `Stage2DirichletAP.chebyshevThetaAP`, and
`Stage2DirichletAP.chebyshevPsiChar` in pure Mathlib `v4.33.1`.

## Main Results

1. **Unconditional Half-Plane Zero-Free Log-Derivative Bound for Every Dirichlet `L(s, χ)`**:
   - `ZeroFreeHalfPlaneL χ θ`: nonvanishing of `DirichletCharacter.LFunction χ` on `Re(s) > θ`
     (away from `s = 1` when `χ = 1`).
   - `negLogDerivL_bound_of_zeroFree_halfPlane_ne_one` & `negLogDerivL_bound_of_zeroFree_halfPlane`:
     unconditional Borel–Carathéodory bound `‖-L'/L(s, χ)‖ ≤ C * Real.log (|s.im| + 2)` on
     `θ + δ ≤ s.re ≤ 3` (for all `t` when `χ ≠ 1`, and for `|t| ≥ 4` when `χ = 1`).

2. **Unconditional Bidirectional Equivalence: Zero-Free Half-Plane ↔ Character Chebyshev Bound**:
   - `psiChar_rpow_eps_of_zeroFree_halfPlane` (forward, via sharp pole-free Perron contour shift
     from `c = 1 + 1 / log x` to `σ = θ + ε' / 2` with `T = x`).
   - `zeroFreeHalfPlaneL_of_psiChar_rpow_eps` (converse, via Abelian summation / Mellin-integral
     holomorphy of `-L'/L(s, χ)` on `Re(s) > θ` and analytic-order contradiction at any zero).
   - `zeroFreeHalfPlaneL_iff_psiChar_rpow_eps`: exact unconditional `↔` for every non-principal
     `χ ≠ 1` mod `q` and every `0 < θ < 1`.

3. **Unconditional Master `GRH` Equivalences for Arithmetic Progressions**:
   - Exact inverse character orthogonality `chebyshevPsiChar_eq_sum_coprime_psiAP`.
   - `zeroFree_mod_q_iff_psiAP_rpow_eps` & `zeroFree_mod_q_iff_thetaAP_rpow_eps`: modulus-by-modulus
     bidirectional equivalences for every `q ≥ 1` (`[NeZero q]`) and `1 / 2 ≤ θ < 1`.
   - `grh_mod_q_iff_psiAP_sqrt_eps` & `grh_mod_q_iff_thetaAP_sqrt_eps` (`θ = 1 / 2`).
   - Master global `GRH` equivalences directly against `DirichletLZerosOnLine`,
     `DirichletLNonvanishingRightOfHalf`, `PrimitiveDirichletLZerosOnLine`, and `RHDirect.ZeroFreeAll`:
     `grh_iff_psiAP_sqrt_eps`, `grh_iff_thetaAP_sqrt_eps`, `primitiveGRH_iff_psiAP_sqrt_eps`,
     `primitiveGRH_iff_thetaAP_sqrt_eps`, and `grh_iff_psiAP_and_thetaAP_sqrt_eps`.

4. **Unconditional Exact Backlund Formula, `|S(T, χ)| = O(log(q T))`, & Full Riemann–von Mangoldt
   Zero-Count Asymptotic for Every Primitive `completedLFunction χ`**:
   - `lFunctionZeroCount hprim hχ T`: exact multiplicity-weighted zero count `N(T, χ)` in
     `0 < Re(s) < 1, |Im(s)| < T`.
   - `backlund_LFunction_exact_formula`: exact identity
     `N(T, χ) = (T / π) * log q + (2 / π) * dirichletGammaPhase χ T + backlundSChar χ T`.
   - `abs_backlundSChar_le_log`: unconditional Backlund–Jensen bound
     `|backlundSChar χ T| ≤ C * log (q * (T + 2))` via `Stage5JensenHadamard.jensen_zero_count_le`
     and `Stage6LFunctionOrder.norm_LFunction_strip_poly_bound`.
   - `lFunctionZeroCount_asymptotic`: completely unconditional Riemann–von Mangoldt asymptotic
     `|N(T, χ) - (T / π) * log (q * T / (2 * π * e))| ≤ C * log (q * T)` for ALL `T ≥ 2`,
     ALL `q ≥ 1`, and ALL primitive `χ ≠ 1` mod `q` (with ZERO extra hypotheses on `T`!).
-/

noncomputable section

open Complex DirichletCharacter MeasureTheory Set Filter Topology Finset Metric
open scoped BigOperators Real ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage8GRHEquivalence

open RHDirect.Stage2DirichletAP
open RHDirect.Stage3RealAnalyticLandau
open RHDirect.Stage3ZeroFreeRegion
open RHDirect.Stage5ContourExplicit
open RHDirect.Stage5DirichletLZeroFree
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage6LFunctionOrder
open RHDirect.Stage7VonMangoldtExplicit
open RHDirect.Stage8HadamardLFunction

/-! ## Section 1: Half-Plane Zero-Free Predicate & Borel–Carathéodory Log-Derivative Bound -/

/-- Half-plane zero-free predicate for a Dirichlet `L`-function `L(s, χ)`:
`L(s, χ) ≠ 0` throughout `Re(s) > θ` (away from the pole `s = 1` when `χ = 1`). -/
def ZeroFreeHalfPlaneL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- For every non-principal `χ ≠ 1`, `ZeroFreeHalfPlaneL χ θ` is simply `∀ s, θ < s.re → L(χ, s) ≠ 0`. -/
theorem zeroFreeHalfPlaneL_iff_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (θ : ℝ) :
    ZeroFreeHalfPlaneL χ θ ↔ ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction χ s ≠ 0 :=
  ⟨fun h s hs => h s hs (.inl hχ), fun h s hs _ => h s hs⟩

/-- For the principal character `1 mod q` and `0 ≤ θ`, `ZeroFreeHalfPlaneL 1 θ` is equivalent to
zero-freeness of `riemannZeta` on `Re(s) > θ` (`s ≠ 1`). -/
theorem zeroFreeHalfPlaneL_one_iff_zeta (q : ℕ) [NeZero q] {θ : ℝ} (hθ : 0 ≤ θ) :
    ZeroFreeHalfPlaneL (1 : DirichletCharacter ℂ q) θ ↔
      ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  constructor
  · intro h s hs hs1 hz
    have h0 : 0 < s.re := lt_of_le_of_lt hθ hs
    exact h s hs (.inr hs1) ((RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos q h0 hs1).mpr hz)
  · intro h s hs hχs hL
    have hs1 : s ≠ 1 := hχs.resolve_left (not_not.mpr rfl)
    have h0 : 0 < s.re := lt_of_le_of_lt hθ hs
    exact h s hs hs1 ((RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos q h0 hs1).mp hL)

/-- For `0 ≤ θ`, `ZeroFreeHalfPlaneL χ θ` is invariant under passing to the underlying primitive
character `χ.primitiveCharacter`. -/
theorem zeroFreeHalfPlaneL_iff_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ZeroFreeHalfPlaneL χ θ ↔ ZeroFreeHalfPlaneL χ.primitiveCharacter θ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim_ne_iff : χ.primitiveCharacter ≠ 1 ↔ χ ≠ 1 := by
    constructor
    · intro h h1
      apply h
      have h2 : DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter =
          (1 : DirichletCharacter ℂ q) := χ.changeLevel_primitiveCharacter.trans h1
      have h3 : DirichletCharacter.changeLevel χ.conductor_dvd_level (1 : DirichletCharacter ℂ χ.conductor) =
          (1 : DirichletCharacter ℂ q) := map_one _
      exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level (h2.trans h3.symm)
    · intro h h1
      apply h
      rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
  constructor
  · intro h s hs hψs hL
    have hχs : χ ≠ 1 ∨ s ≠ 1 := hψs.imp_left hprim_ne_iff.mp
    have h0 : 0 < s.re := lt_of_le_of_lt hθ hs
    exact h s hs hχs ((RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 hχs).mpr hL)
  · intro h s hs hχs hL
    have hψs : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := hχs.imp_left hprim_ne_iff.mpr
    have h0 : 0 < s.re := lt_of_le_of_lt hθ hs
    exact h s hs hψs ((RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 hχs).mp hL)

/-- Global half-plane zero-freeness at `θ = 1 / 2` is identical to `DirichletLNonvanishingRightOfHalf`,
hence equivalent to `DirichletLZerosOnLine`, `PrimitiveDirichletLZerosOnLine`, and `RHDirect.ZeroFreeAll`. -/
theorem forall_zeroFreeHalfPlaneL_half_iff_dirichletLZerosOnLine :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ZeroFreeHalfPlaneL χ (1 / 2)) ↔
      DirichletLZerosOnLine :=
  RHDirect.dirichletLNonvanishingRightOfHalf_iff_dirichletLZerosOnLine

/-- **Unconditional Borel–Carathéodory Log-Derivative Bound in Any Zero-Free Half-Plane (`χ ≠ 1`)**:
for any `q [NeZero q]`, non-principal `χ ≠ 1`, `0 < θ`, `0 < δ` with `θ + δ < 1`, if
`ZeroFreeHalfPlaneL χ θ`, then there exists `C > 0` such that for ALL `s : ℂ` with
`θ + δ ≤ s.re ≤ 3` (all imaginary parts `s.im : ℝ`!),
`‖-deriv (LFunction χ) s / LFunction χ s‖ ≤ C * Real.log (|s.im| + 2)`. -/
theorem negLogDerivL_bound_of_zeroFree_halfPlane_ne_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ δ : ℝ}
    (hθ0 : 0 < θ) (hδ0 : 0 < δ) (hθδ : θ + δ < 1)
    (hzf : ZeroFreeHalfPlaneL χ θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, θ + δ ≤ s.re → s.re ≤ 3 →
        ‖Stage3ZeroFreeRegion.negLogDerivL χ s‖ ≤ C * Real.log (|s.im| + 2) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  set R_open : ℝ := 3 - θ - δ / 4
  set R : ℝ := 3 - θ - δ / 2
  set r : ℝ := 3 - θ - δ
  have hR_open_pos : 0 < R_open := by dsimp only [R_open]; linarith
  have hR_pos : 0 < R := by dsimp only [R]; linarith
  have hrR : r < R := by dsimp only [r, R]; linarith
  set A_L : ℝ := max (36 * (q : ℝ) / (θ + δ / 2)) 2
  have hA_ge2 : 2 ≤ A_L := le_max_right _ _
  have hA_pos : 0 < A_L := by linarith
  have hlogA_nn : 0 ≤ Real.log A_L := Real.log_nonneg (by linarith)
  set C_M : ℝ := 2 * Real.log A_L + 1
  have hCM_pos : 0 < C_M := by dsimp only [C_M]; linarith
  set C : ℝ := (2 * R / (R - r) ^ 2) * C_M
  have hC_pos : 0 < C := by
    have : 0 < R - r := by dsimp only [R, r]; linarith
    positivity
  refine ⟨C, hC_pos, fun s hre_lo hre_hi => ?_⟩
  set t : ℝ := s.im
  set s₀ : ℂ := (3 : ℂ) + I * (t : ℂ)
  have hs₀_re : s₀.re = 3 := by simp [s₀]
  have hs₀_im : s₀.im = t := by simp [s₀]
  have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)).1
    rw [Complex.sub_re, hs₀_re] at hre
    exact hzf z (by dsimp only [R_open] at hre; linarith) (.inl hχ)
  have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
    Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
  have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
    Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
  have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
    (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
  set L : ℝ := Real.log (|t| + 2)
  have hL_ge_half : (1 / 2 : ℝ) ≤ L :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  have hL_pos : 0 < L := by linarith
  have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ C_M * L := by
    intro z hz
    have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
    have hznz : DirichletCharacter.LFunction χ z ≠ 0 := hball_nz z hz_ball
    have hs₀_nz : DirichletCharacter.LFunction χ s₀ ≠ 0 :=
      hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
    rw [Complex.sub_re, hs₀_re] at hre_diff
    rw [Complex.sub_im, hs₀_im] at him_diff
    have hz_re_lo : θ + δ / 2 ≤ z.re := by dsimp only [R] at hre_diff; linarith
    have hz_re_hi : z.re ≤ 6 := by dsimp only [R] at hre_diff; linarith
    have hz_im_hi : |z.im| ≤ |t| + 3 := by
      have htri : |z.im| ≤ |t| + |z.im - t| := by
        simpa [add_sub_cancel] using abs_add_le t (z.im - t)
      have hR_le3 : R ≤ 3 := by dsimp only [R]; linarith
      linarith [abs_le.mpr him_diff]
    have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤
        (9 * (q : ℝ) / (θ + δ / 2)) * (|t| + 2) := by
      have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
        (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
        (by linarith : 0 < z.re)
      have hnum : z.re + |z.im| ≤ 9 * (|t| + 2) := by linarith [abs_nonneg t]
      calc ‖DirichletCharacter.LFunction χ z‖
          ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
        _ ≤ (q : ℝ) * (9 * (|t| + 2)) / (θ + δ / 2) :=
            div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_left hnum hq_pos.le) (by positivity) hz_re_lo
        _ = (9 * (q : ℝ) / (θ + δ / 2)) * (|t| + 2) := by ring
    have hs₀_lo : (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s₀‖ :=
      Stage6LFunctionOrder.quarter_le_norm_LFunction_of_two_le_re χ (by rw [hs₀_re]; norm_num)
    have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 4 := by
      rw [norm_div, norm_one]
      exact (div_le_iff₀ (norm_pos_iff.mpr hs₀_nz)).mpr (by linarith)
    have hratio_le : ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
        A_L * (|t| + 2) := by
      rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
            DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring,
        norm_mul]
      calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
          ≤ ((9 * (q : ℝ) / (θ + δ / 2)) * (|t| + 2)) * 4 :=
            mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
        _ = (36 * (q : ℝ) / (θ + δ / 2)) * (|t| + 2) := by ring
        _ ≤ A_L * (|t| + 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [abs_nonneg t])
    have hre_eq : (Log z).re =
        Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
      have hexp : Real.exp (Log z).re =
          ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        rw [← Complex.norm_exp, hLog_exp z hz_ball]
      rw [← hexp, Real.log_exp]
    rw [hre_eq]
    calc Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖
        ≤ Real.log (A_L * (|t| + 2)) :=
          Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)) hratio_le
      _ = Real.log A_L + L := Real.log_mul hA_pos.ne' (by linarith [abs_nonneg t])
      _ ≤ (2 * Real.log A_L) * L + L := by nlinarith
      _ = C_M * L := by dsimp only [C_M]; ring
  have hs_dist : ‖s - s₀‖ ≤ r := by
    have hdiff : s - s₀ = (((s.re - 3 : ℝ) : ℂ)) := Complex.ext (by simp [s₀]) (by simp [s₀, t])
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp only [r]; constructor <;> linarith
  have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
  have hs_ball : s ∈ Metric.ball s₀ R_open :=
    hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
  rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
  unfold Stage3ZeroFreeRegion.negLogDerivL
  rw [neg_div, norm_neg]
  calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ (2 * R / (R - r) ^ 2) * (C_M * L) := hbc
    _ = C * L := by dsimp only [C]; ring

/-- Helper: exact Euler-factor logarithmic-derivative difference for the principal character `1 mod q`
on `Re(s) > 0, s ≠ 1, ζ(s) ≠ 0`. -/
private lemma negLogDerivL_one_sub_negLogDerivZeta_bound (q : ℕ) [NeZero q] {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ s : ℂ, σ₀ ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 →
        ‖Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s -
            Stage3ZeroFreeRegion.negLogDerivZeta s‖ ≤ K := by
  have hden_pos : 0 < (2 : ℝ) ^ σ₀ - 1 := by
    have hgt : (1 : ℝ) < (2 : ℝ) ^ σ₀ := Real.one_lt_rpow (by norm_num) hσ₀
    linarith
  set K : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((2 : ℝ) ^ σ₀ - 1)
  have hK_nn : 0 ≤ K := Finset.sum_nonneg fun p hp =>
    div_nonneg (Real.log_natCast_nonneg p) hden_pos.le
  refine ⟨K, hK_nn, fun s hs hs1 hznz => ?_⟩
  have hs0 : 0 < s.re := lt_of_lt_of_le hσ₀ hs
  let P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))
  have hP_ne : P s ≠ 0 := by
    dsimp only [P]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have h1 := RHDirect.eulerFactor_ne_zero_of_re_pos (1 : DirichletCharacter ℂ 1) hpr hs0
    simpa [MulChar.one_apply (isUnit_of_subsingleton _)] using h1
  have hP_diff : DifferentiableAt ℂ P s := by
    dsimp only [P]
    refine DifferentiableAt.fun_finsetProd (u := q.primeFactors)
      (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
    have hEq : (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) =
        fun z : ℂ => 1 - cexp (Complex.log (p : ℂ) * (-z)) :=
      funext fun z => by rw [Complex.cpow_def_of_ne_zero hpC]
    rw [hEq]; fun_prop
  have hev : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => P z * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz1
    have h := DirichletCharacter.LFunction_changeLevel q.one_dvd (1 : DirichletCharacter ℂ 1) (.inr hz1)
    rw [map_one, DirichletCharacter.LFunction_modOne_eq, mul_comm] at h
    rw [h]
    dsimp only [P]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [MulChar.one_apply (isUnit_of_subsingleton _)]
  have hL_val : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s = P s * riemannZeta s :=
    hev.self_of_nhds
  have hZ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL_deriv : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s =
      deriv P s * riemannZeta s + P s * deriv riemannZeta s := by
    rw [hev.deriv_eq, (hP_diff.hasDerivAt.fun_mul hZ_diff.hasDerivAt).deriv]
  have hdiff_eq : Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s -
      Stage3ZeroFreeRegion.negLogDerivZeta s = -(deriv P s / P s) := by
    unfold Stage3ZeroFreeRegion.negLogDerivL Stage3ZeroFreeRegion.negLogDerivZeta
    rw [hL_deriv, hL_val]
    field_simp [hP_ne, hznz]
    ring
  have hP_ld : deriv P s / P s =
      ∑ p ∈ q.primeFactors, ((Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
    have hld := logDeriv_prod (s := q.primeFactors) (f := fun p (z : ℂ) => 1 - (p : ℂ) ^ (-z)) (x := s)
      (fun p hp => by
        have hpr := Nat.prime_of_mem_primeFactors hp
        have h1 := RHDirect.eulerFactor_ne_zero_of_re_pos (1 : DirichletCharacter ℂ 1) hpr hs0
        simpa [MulChar.one_apply (isUnit_of_subsingleton _)] using h1)
      (fun p hp => by
        have hpr := Nat.prime_of_mem_primeFactors hp
        have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
        have hEq : (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) =
            fun z : ℂ => 1 - cexp (Complex.log (p : ℂ) * (-z)) :=
          funext fun z => by rw [Complex.cpow_def_of_ne_zero hpC]
        rw [hEq]; fun_prop)
    change logDeriv P s = _
    dsimp only [P]
    rw [hld]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpr.pos
    have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
    have hEq : (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) =
        fun z : ℂ => 1 - cexp ((Real.log (p : ℝ) : ℂ) * (-z)) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_natCast, Complex.ofReal_log hp0.le]
    have hd : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
        ((Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s)) s := by
      rw [hEq]
      have h1 : HasDerivAt (fun z : ℂ => (Real.log (p : ℝ) : ℂ) * (-z)) (-(Real.log (p : ℝ) : ℂ)) s := by
        simpa using (hasDerivAt_id s).neg.const_mul (Real.log (p : ℝ) : ℂ)
      refine ((hasDerivAt_const s (1 : ℂ)).sub h1.cexp).congr_deriv ?_
      rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hp0.le]
      ring
    rw [logDeriv_apply, hd.deriv]
  rw [hdiff_eq, norm_neg, hP_ld]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have hpow_ne : (p : ℂ) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpC]; exact Complex.exp_ne_zero _
  have hrew : ((Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) =
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1) := by
    have hmul : (p : ℂ) ^ s * (p : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hpC, add_neg_cancel, Complex.cpow_zero]
    have hden1 : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
      have h1 := RHDirect.eulerFactor_ne_zero_of_re_pos (1 : DirichletCharacter ℂ 1) hpr hs0
      simpa [MulChar.one_apply (isUnit_of_subsingleton _)] using h1
    have hden2 : (p : ℂ) ^ s - 1 ≠ 0 := by
      intro h0
      have := sub_eq_zero.mp h0
      have h1 : 1 = (p : ℂ) ^ (-s) := by rw [← hmul, this, one_mul]
      exact hden1 (sub_eq_zero.mpr h1)
    field_simp [hden1, hden2]
    calc (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) * ((p : ℂ) ^ s - 1)
        = (Real.log (p : ℝ) : ℂ) * ((p : ℂ) ^ s * (p : ℂ) ^ (-s) - (p : ℂ) ^ (-s)) := by ring
      _ = (Real.log (p : ℝ) : ℂ) * (1 - (p : ℂ) ^ (-s)) := by rw [hmul]
  rw [hrew, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
  have hden_ge : (2 : ℝ) ^ σ₀ - 1 ≤ ‖(p : ℂ) ^ s - 1‖ := by
    have h1 : (2 : ℝ) ^ σ₀ ≤ (p : ℝ) ^ s.re :=
      (Real.rpow_le_rpow (by norm_num) hp2 hσ₀.le).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hs)
    have htri := norm_sub_norm_le ((p : ℂ) ^ s) (1 : ℂ)
    rw [Complex.norm_natCast_cpow_of_pos hpr.pos, norm_one] at htri
    linarith
  exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hden_pos hden_ge

/-- **UNCONDITIONAL HALF-PLANE ZERO-FREE LOG-DERIVATIVE BOUND FOR EVERY DIRICHLET `L(s, χ)`**
(unified over ALL `q ≥ 1` and ALL characters `χ : DirichletCharacter ℂ q`, principal or non-principal):
if `ZeroFreeHalfPlaneL χ θ` (`0 < θ`, `0 < δ`, `θ + δ < 1`), then there exists `C > 0` such that
`‖-L'/L(s, χ)‖ ≤ C * Real.log (|s.im| + 2)` on `θ + δ ≤ s.re ≤ 3` (for all `t` if `χ ≠ 1`, and for
`|t| ≥ 4` if `χ = 1`). -/
theorem negLogDerivL_bound_of_zeroFree_halfPlane {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {θ δ : ℝ}
    (hθ0 : 0 < θ) (hδ0 : 0 < δ) (hθδ : θ + δ < 1)
    (hzf : ZeroFreeHalfPlaneL χ θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, θ + δ ≤ s.re → s.re ≤ 3 → (χ ≠ 1 ∨ 4 ≤ |s.im|) →
        ‖Stage3ZeroFreeRegion.negLogDerivL χ s‖ ≤ C * Real.log (|s.im| + 2) := by
  by_cases hχ : χ = 1
  · subst hχ
    have hzf_zeta : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
      (zeroFreeHalfPlaneL_one_iff_zeta q hθ0.le).mp hzf
    obtain ⟨C₀, hC₀_pos, hbd_tall, _⟩ :=
      Stage7VonMangoldtExplicit.negLogDerivZeta_bound_of_zeroFree_halfPlane hθ0 hδ0 hθδ hzf_zeta
    obtain ⟨K, hK_nn, hK_bd⟩ := negLogDerivL_one_sub_negLogDerivZeta_bound q (by linarith : 0 < θ + δ)
    refine ⟨C₀ + 2 * K, by positivity, fun s hlo hhi hor => ?_⟩
    have him4 : 4 ≤ |s.im| := hor.resolve_left (not_not.mpr rfl)
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_im, abs_zero] at him4; norm_num at him4
    have hznz : riemannZeta s ≠ 0 := hzf_zeta s (by linarith) hs1
    have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (|s.im| + 2) :=
      (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im]))
    have h1 := hK_bd s hlo hs1 hznz
    have h2 : ‖Stage3ZeroFreeRegion.negLogDerivZeta s‖ ≤ C₀ * Real.log (|s.im| + 2) :=
      hbd_tall s hlo hhi him4
    have htri : ‖Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s‖ ≤
        ‖Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s -
            Stage3ZeroFreeRegion.negLogDerivZeta s‖ +
        ‖Stage3ZeroFreeRegion.negLogDerivZeta s‖ := by
      simpa [sub_add_cancel] using norm_add_le
        (Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s -
            Stage3ZeroFreeRegion.negLogDerivZeta s)
        (Stage3ZeroFreeRegion.negLogDerivZeta s)
    nlinarith
  · obtain ⟨C, hC_pos, hbd⟩ :=
      negLogDerivL_bound_of_zeroFree_halfPlane_ne_one hχ hθ0 hδ0 hθδ hzf
    exact ⟨C, hC_pos, fun s hlo hhi _ => hbd s hlo hhi⟩

/-! ## Section 2: Unconditional Bidirectional Equivalence `ZeroFreeHalfPlaneL χ θ ↔ ψ(x, χ) = O(x^{θ + ε})` -/

/-- Elementary helper: for any `α > 0`, there is `K > 0` such that `(Real.log (x + 2)) ^ 2 ≤ K * x ^ α`
for all `x ≥ 2`. -/
private lemma log_add_two_sq_le_rpow {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → (Real.log (x + 2)) ^ 2 ≤ K * x ^ α := by
  set β : ℝ := α / 2 with hβ_def
  have hβ : 0 < β := by positivity
  refine ⟨(2 / β) ^ 2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (x + 2) ≤ 2 * Real.log x := by
    have hsq : x + 2 ≤ x ^ 2 := by nlinarith
    calc Real.log (x + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hrpow := Real.log_le_rpow_div hx0.le hβ
  have hlin : Real.log (x + 2) ≤ (2 / β) * x ^ β := by
    calc Real.log (x + 2) ≤ 2 * Real.log x := hlog
      _ ≤ 2 * (x ^ β / β) := mul_le_mul_of_nonneg_left hrpow (by norm_num)
      _ = (2 / β) * x ^ β := by ring
  calc (Real.log (x + 2)) ^ 2
      ≤ ((2 / β) * x ^ β) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlin 2
    _ = (2 / β) ^ 2 * (x ^ β * x ^ β) := by ring
    _ = (2 / β) ^ 2 * x ^ α := by rw [← Real.rpow_add hx0, hβ_def, add_halves]

/-- **UNCONDITIONAL FORWARD DIRECTION (`ZeroFreeHalfPlaneL χ θ → ‖ψ(x, χ)‖ = O(x^{θ + ε})`)**:
for EVERY `q [NeZero q]`, EVERY non-principal `χ ≠ 1`, and EVERY `0 < θ < 1`, if
`ZeroFreeHalfPlaneL χ θ`, then for every `ε > 0` there exists `C > 0` such that
`‖chebyshevPsiChar χ x‖ ≤ C * x ^ (θ + ε)` for all `x ≥ 2`, proved directly via
`negLogDerivL_bound_of_zeroFree_halfPlane_ne_one` and the sharp pole-free Perron contour shift! -/
theorem psiChar_rpow_eps_of_zeroFree_halfPlane {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hzf : ZeroFreeHalfPlaneL χ θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C * x ^ (θ + ε) := by
  intro ε hε
  set ε' : ℝ := min ε ((1 - θ) / 2) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by linarith)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_lt : ε' ≤ (1 - θ) / 2 := min_le_right _ _
  set σ : ℝ := θ + ε' / 2 with hσ_def
  have hσ_pos : 0 < σ := by linarith
  have hσ_lt1 : σ < 1 := by linarith
  obtain ⟨C₀, hC₀_pos, hbd⟩ :=
    negLogDerivL_bound_of_zeroFree_halfPlane_ne_one hχ hθ0 (by positivity : 0 < ε' / 2)
      (by linarith) hzf
  obtain ⟨K_log, hK_log_pos, hK_log⟩ := log_add_two_sq_le_rpow (α := ε' / 2) (by positivity)
  set C_main : ℝ := 4800 + C₀ * (2 / σ + 2) + 18 * C₀
  have hC_main_pos : 0 < C_main := by positivity
  set C_large : ℝ := C_main * K_log
  set C_fin : ℝ := max C_large 24
  refine ⟨C_fin, by positivity, fun x hx2 => ?_⟩
  by_cases hx4 : 4 ≤ x
  · have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hlogx_gt1 : 1 < Real.log x := by
      have h4 : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
    have hlogx_pos : 0 < Real.log x := zero_lt_one.trans hlogx_gt1
    set c : ℝ := 1 + 1 / Real.log x with hc_def
    have hc1 : 1 < c := by rw [hc_def]; linarith [div_pos one_pos hlogx_pos]
    have hc2 : c ≤ 2 := by
      rw [hc_def]
      have : 1 / Real.log x ≤ 1 := (div_le_one hlogx_pos).mpr hlogx_gt1.le
      linarith
    have hc3 : c ≤ 3 := by linarith
    have hxc_le : x ^ c ≤ 3 * x := by
      have h1 : x ^ c = x * x ^ (1 / Real.log x) := by
        rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
      have h2 : x ^ (1 / Real.log x) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hlogx_pos.ne']
      rw [h1, h2]
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      nlinarith
    -- Step 1: Sharp Perron truncation at `T = x`
    have hPerron_raw := Stage5ContourExplicit.norm_chebyshevPsiChar_sub_truncatedPerron_le
      χ hx2 (by linarith : 1 ≤ x)
    have hlog_cmp : Real.log x + 1 ≤ 2 * Real.log (x + 2) := by
      have h1 : Real.log x ≤ Real.log (x + 2) := Real.log_le_log hx0 (by linarith)
      linarith
    have hPerron : ‖Stage2DirichletAP.chebyshevPsiChar χ x -
        Stage5ContourExplicit.truncatedPerronPsi χ x c x‖ ≤
        4800 * (Real.log (x + 2)) ^ 2 := by
      have hxx : x / x = 1 := div_self hx0.ne'
      rw [hxx, one_mul] at hPerron_raw
      have hsq : (Real.log x + 1) ^ 2 + (Real.log x + 1) ≤ 2 * (Real.log x + 1) ^ 2 := by nlinarith
      have hsq2 : (Real.log x + 1) ^ 2 ≤ 4 * (Real.log (x + 2)) ^ 2 := by
        calc (Real.log x + 1) ^ 2 ≤ (2 * Real.log (x + 2)) ^ 2 :=
              pow_le_pow_left₀ (by linarith) hlog_cmp 2
          _ = 4 * (Real.log (x + 2)) ^ 2 := by ring
      linarith
    -- Step 2: Pole-free rectangular contour shift of `truncatedPerronPsi χ x c x` to `Re(s) = σ`
    let F : ℂ → ℂ := fun s => Stage3ZeroFreeRegion.negLogDerivL χ s * ((x : ℂ) ^ s / s)
    set U : Set ℂ := {z : ℂ | θ < z.re}
    have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hrect_sub : Stage5ContourExplicit.closedRect σ c (-x) x ⊆ U := fun z hz => by
      change θ < z.re; linarith [hz.1.1]
    have hF_diff_U : DifferentiableOn ℂ F U := by
      have hL_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
        (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
      have hnd_diff : DifferentiableOn ℂ (Stage3ZeroFreeRegion.negLogDerivL χ) U := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        exact (hL_diff.deriv hU_open).neg.div hL_diff fun z hz => hzf z hz (.inl hχ)
      have hW_diff : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s) U := by
        intro s hs
        have hs_pos : 0 < s.re := lt_trans hθ0 hs
        have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_pos; exact lt_irrefl 0 hs_pos
        have hpow : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ w) s := by
          have hEq : (fun w : ℂ => (x : ℂ) ^ w) = fun w : ℂ => cexp (Complex.log (x : ℂ) * w) :=
            funext fun w => Complex.cpow_def_of_ne_zero hxC w
          rw [hEq]; fun_prop
        exact (hpow.div differentiableAt_id hs0).differentiableWithinAt
      exact hnd_diff.mul hW_diff
    have hF_diff : DifferentiableOn ℂ F (Stage5ContourExplicit.closedRect σ c (-x) x) :=
      hF_diff_U.mono hrect_sub
    have hrect0 := Stage5ContourExplicit.rectBoundaryIntegral_eq_zero_of_differentiableOn
      (by linarith : σ ≤ c) (by linarith : -x ≤ x) hF_diff
    have hshift := Stage5ContourExplicit.vertical_contour_shift_of_rectBoundaryIntegral
      (R := 0) (by simpa using hrect0)
    have hperron_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((c : ℂ) + I * (t : ℂ))) =
        Stage5ContourExplicit.truncatedPerronPsi χ x c x := by
      unfold Stage5ContourExplicit.truncatedPerronPsi
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      dsimp only [F]
      rw [mul_div_assoc]
    rw [hperron_eq, zero_add] at hshift
    -- Step 3: Bound left-vertical integral on `Re(s) = σ`
    have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ)))‖ ≤
        C₀ * (2 / σ + 2) * x ^ σ * (Real.log (x + 2)) ^ 2 := by
      have hF_cont : ContinuousOn (fun t : ℝ => F ((σ : ℂ) + I * (t : ℂ))) (Set.uIcc (-x) x) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact hF_diff.continuousOn.comp (by fun_prop) fun t ht => ⟨by simp; linarith, by simpa using ht⟩
      have hinv_cont : Continuous (fun t : ℝ => ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹) := by
        refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
        rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this; linarith
      have hinv_int : ∫ t in (-x)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ (2 / σ + 2) * Real.log (x + 2) := by
        have hmid : ∫ t in (-1 : ℝ)..1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 / σ := by
          have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ σ⁻¹ := fun t _ => by
            have hden : σ ≤ ‖(σ : ℂ) + I * (t : ℂ)‖ := by
              simpa [abs_of_pos hσ_pos] using Complex.abs_re_le_norm ((σ : ℂ) + I * (t : ℂ))
            exact inv_anti₀ hσ_pos hden
          calc ∫ t in (-1 : ℝ)..1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹
              ≤ ∫ _t in (-1 : ℝ)..1, σ⁻¹ :=
                intervalIntegral.integral_mono_on (by norm_num) (hinv_cont.intervalIntegrable _ _)
                  intervalIntegrable_const hpt
            _ = 2 / σ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        have hpos_tail : ∫ t in (1 : ℝ)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log x := by
          have hint_t : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 : ℝ) x := by
            refine (ContinuousOn.inv₀ continuousOn_id fun t ht => ?_).intervalIntegrable
            rw [Set.uIcc_of_le hx1] at ht; dsimp only [id_eq]; linarith [ht.1]
          calc ∫ t in (1 : ℝ)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹
              ≤ ∫ t in (1 : ℝ)..x, t⁻¹ :=
                intervalIntegral.integral_mono_on hx1 (hinv_cont.intervalIntegrable _ _) hint_t fun t ht => by
                  have ht0 : 0 < t := zero_lt_one.trans_le ht.1
                  have hden : t ≤ ‖(σ : ℂ) + I * (t : ℂ)‖ := by
                    simpa [abs_of_pos ht0] using Complex.abs_im_le_norm ((σ : ℂ) + I * (t : ℂ))
                  exact inv_anti₀ ht0 hden
            _ = Real.log x := by rw [integral_inv_of_pos zero_lt_one hx0, div_one]
        have hneg_tail : ∫ t in (-x)..(-1 : ℝ), ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log x := by
          have hcomp : ∫ t in (-x)..(-1 : ℝ), ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ =
              ∫ u in (1 : ℝ)..x, ‖(σ : ℂ) + I * (u : ℂ)‖⁻¹ := by
            have h1 := intervalIntegral.integral_comp_neg
              (f := fun u : ℝ => ‖(σ : ℂ) + I * (u : ℂ)‖⁻¹) (a := -x) (b := -1)
            simp only [neg_neg] at h1
            rw [← h1]
            refine intervalIntegral.integral_congr fun t _ => ?_
            congr 1; rw [← Complex.norm_conj]; congr 1
            apply Complex.ext <;> simp
          rw [hcomp]; exact hpos_tail
        have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
          (hinv_cont.intervalIntegrable (μ := volume) (-x) (-1))
          (hinv_cont.intervalIntegrable (μ := volume) (-1) 1)
        have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
          (hinv_cont.intervalIntegrable (μ := volume) (-x) 1)
          (hinv_cont.intervalIntegrable (μ := volume) 1 x)
        have hlog_le : Real.log x ≤ Real.log (x + 2) := Real.log_le_log hx0 (by linarith)
        have hlog_ge1 : 1 ≤ Real.log (x + 2) := hlogx_gt1.le.trans hlog_le
        have h2σ : 2 / σ ≤ (2 / σ) * Real.log (x + 2) := le_mul_of_one_le_right (by positivity) hlog_ge1
        linarith
      have hpt : ∀ t ∈ Set.Icc (-x) x,
          ‖F ((σ : ℂ) + I * (t : ℂ))‖ ≤
            (C₀ * Real.log (x + 2) * x ^ σ) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
        intro t ht
        have habs_t : |t| ≤ x := abs_le.mpr ht
        have hlog_le : Real.log (|t| + 2) ≤ Real.log (x + 2) :=
          Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
        have hL := hbd ((σ : ℂ) + I * (t : ℂ)) (by simp [σ]) (by simp; linarith)
        have him_eq : ((σ : ℂ) + I * (t : ℂ)).im = t := by simp
        rw [him_eq] at hL
        dsimp only [F]
        rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
        rw [hre, div_eq_mul_inv, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (hL.trans (mul_le_mul_of_nonneg_left hlog_le hC₀_pos.le))
            (Real.rpow_nonneg hx0.le _))
          (inv_nonneg.mpr (norm_nonneg _))
      have hlog_nn : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))‖
          ≤ 1 * ∫ t in (-x)..x, ‖F ((σ : ℂ) + I * (t : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith))
              (norm_nonneg _) zero_le_one
        _ ≤ ∫ t in (-x)..x, (C₀ * Real.log (x + 2) * x ^ σ) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hF_cont.intervalIntegrable.norm
              ((hinv_cont.intervalIntegrable _ _).const_mul _) hpt
        _ = (C₀ * Real.log (x + 2) * x ^ σ) * ∫ t in (-x)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (C₀ * Real.log (x + 2) * x ^ σ) * ((2 / σ + 2) * Real.log (x + 2)) :=
            mul_le_mul_of_nonneg_left hinv_int (by positivity)
        _ = C₀ * (2 / σ + 2) * x ^ σ * (Real.log (x + 2)) ^ 2 := by ring
    -- Step 4: Bound top and bottom horizontal integrals on `Im(s) = ±x`
    have hHoriz_bd : ∀ s_im : ℝ, (s_im = x ∨ s_im = -x) →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (s_im : ℂ)))‖ ≤
          9 * C₀ * Real.log (x + 2) := by
      intro s_im hsim
      have hlog_nn : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
      have habs_sim : |s_im| = x := by rcases hsim with rfl | rfl <;> simp [abs_of_pos hx0]
      have hF_cont : ContinuousOn (fun u : ℝ => F ((u : ℂ) + I * (s_im : ℂ))) (Set.uIcc σ c) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact hF_diff.continuousOn.comp (by fun_prop) fun u hu =>
          ⟨by simpa using hu, by simp [abs_le.mp (le_of_eq habs_sim)]⟩
      have hpt : ∀ u ∈ Set.Icc σ c, ‖F ((u : ℂ) + I * (s_im : ℂ))‖ ≤ 3 * C₀ * Real.log (x + 2) := by
        intro u hu
        have hL := hbd ((u : ℂ) + I * (s_im : ℂ)) (by simpa [σ] using hu.1) (by simp; linarith [hu.2])
        have him_eq : ((u : ℂ) + I * (s_im : ℂ)).im = s_im := by simp
        rw [him_eq, habs_sim] at hL
        have hx_pow : x ^ u ≤ 3 * x := (Real.rpow_le_rpow_of_exponent_le hx1 hu.2).trans hxc_le
        have hden : x ≤ ‖(u : ℂ) + I * (s_im : ℂ)‖ := by
          simpa [habs_sim] using Complex.abs_im_le_norm ((u : ℂ) + I * (s_im : ℂ))
        dsimp only [F]
        rw [norm_mul, norm_div ((x : ℂ) ^ _), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((u : ℂ) + I * (s_im : ℂ)).re = u := by simp
        rw [hre]
        calc ‖Stage3ZeroFreeRegion.negLogDerivL χ ((u : ℂ) + I * (s_im : ℂ))‖ *
              (x ^ u / ‖(u : ℂ) + I * (s_im : ℂ)‖)
            ≤ (C₀ * Real.log (x + 2)) * ((3 * x) / x) :=
              mul_le_mul hL (div_le_div₀ (by positivity) hx_pow hx0 hden) (by positivity) (by positivity)
          _ = 3 * C₀ * Real.log (x + 2) := by field_simp [hx0.ne']
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hlen : c - σ ≤ 3 := by linarith
      calc (2 * Real.pi)⁻¹ * ‖∫ u in σ..c, F ((u : ℂ) + I * (s_im : ℂ))‖
          ≤ 1 * ∫ u in σ..c, ‖F ((u : ℂ) + I * (s_im : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith))
              (norm_nonneg _) zero_le_one
        _ ≤ ∫ _u in σ..c, (3 * C₀ * Real.log (x + 2)) := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hF_cont.intervalIntegrable.norm
              intervalIntegrable_const hpt
        _ = (c - σ) * (3 * C₀ * Real.log (x + 2)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 3 * (3 * C₀ * Real.log (x + 2)) :=
            mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 9 * C₀ * Real.log (x + 2) := by ring
    -- Step 5: Combine all four bounds
    have hbot_eq : (∫ u in σ..c, F ((u : ℂ) - I * (x : ℂ))) =
        ∫ u in σ..c, F ((u : ℂ) + I * ((-x : ℝ) : ℂ)) :=
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
    have hshift_bd :
        ‖Stage5ContourExplicit.truncatedPerronPsi χ x c x‖ ≤
          C₀ * (2 / σ + 2) * x ^ σ * (Real.log (x + 2)) ^ 2 + 18 * C₀ * Real.log (x + 2) := by
      rw [hshift, hbot_eq]
      have ht1 := norm_sub_le
        ((((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ)))) +
          ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (x : ℂ)))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * ((-x : ℝ) : ℂ))))
      have ht2 := norm_add_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (x : ℂ))))
      have htop := hHoriz_bd x (Or.inl rfl)
      have hbot := hHoriz_bd (-x) (Or.inr rfl)
      linarith
    have htri : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage2DirichletAP.chebyshevPsiChar χ x - Stage5ContourExplicit.truncatedPerronPsi χ x c x‖ +
        ‖Stage5ContourExplicit.truncatedPerronPsi χ x c x‖ := by
      simpa [sub_add_cancel] using norm_add_le
        (Stage2DirichletAP.chebyshevPsiChar χ x - Stage5ContourExplicit.truncatedPerronPsi χ x c x)
        (Stage5ContourExplicit.truncatedPerronPsi χ x c x)
    have hxσ_ge1 : 1 ≤ x ^ σ := Real.one_le_rpow hx1 hσ_pos.le
    have hlog_ge1 : 1 ≤ Real.log (x + 2) :=
      hlogx_gt1.le.trans (Real.log_le_log hx0 (by linarith))
    have hlog_le_sq : Real.log (x + 2) ≤ (Real.log (x + 2)) ^ 2 := by nlinarith
    have hcomb : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C_main * x ^ σ * (Real.log (x + 2)) ^ 2 := by
      have h1 : 4800 * (Real.log (x + 2)) ^ 2 ≤ 4800 * x ^ σ * (Real.log (x + 2)) ^ 2 := by
        nlinarith [sq_nonneg (Real.log (x + 2))]
      have h2 : 18 * C₀ * Real.log (x + 2) ≤ 18 * C₀ * x ^ σ * (Real.log (x + 2)) ^ 2 := by
        have ha : Real.log (x + 2) ≤ x ^ σ * (Real.log (x + 2)) ^ 2 := by nlinarith
        nlinarith
      dsimp only [C_main]
      linarith
    have hpow_comb : x ^ σ * x ^ (ε' / 2) = x ^ (θ + ε') := by
      rw [← Real.rpow_add hx0, hσ_def]; congr 1; ring
    have hpow_le : x ^ (θ + ε') ≤ x ^ (θ + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
        ≤ C_main * x ^ σ * (Real.log (x + 2)) ^ 2 := hcomb
      _ ≤ C_main * x ^ σ * (K_log * x ^ (ε' / 2)) :=
          mul_le_mul_of_nonneg_left (hK_log x hx2) (by positivity)
      _ = C_large * (x ^ σ * x ^ (ε' / 2)) := by dsimp only [C_large]; ring
      _ = C_large * x ^ (θ + ε') := by rw [hpow_comb]
      _ ≤ C_large * x ^ (θ + ε) := mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ ≤ C_fin * x ^ (θ + ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  · push Not at hx4
    have hpsi_le : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ RHDirect.chebyshevPsi x := by
      unfold Stage2DirichletAP.chebyshevPsiChar RHDirect.chebyshevPsi
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
    have h6 : RHDirect.chebyshevPsi x ≤ 6 * x :=
      Stage3RealAnalyticLandau.chebyshevPsi_le_six_mul (by linarith)
    have hpow : (1 : ℝ) ≤ x ^ (θ + ε) := Real.one_le_rpow (by linarith) (by positivity)
    have hC24 : 24 ≤ C_fin := le_max_right _ _
    nlinarith

/-- Helper: `stepSum (fun n => χ n * Λ n) x = chebyshevPsiChar χ x`. -/
private lemma stepSum_twist_vonMangoldt_eq_chebyshevPsiChar {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q) * (Λ n : ℂ)) x =
      Stage2DirichletAP.chebyshevPsiChar χ x := by
  unfold Stage3RealAnalyticLandau.stepSum Stage2DirichletAP.chebyshevPsiChar
  have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 ⌊x⌋₊)]
  simp

/-- Pole-free holomorphic logarithmic-derivative zero-free principle on a half-plane `Re(s) > θ`:
if `f` is entire with `f 2 ≠ 0`, `H` is holomorphic on `{s | θ < s.re}` (`θ < 1`), and
`-deriv f s / f s = H s` on `{s | 1 < s.re}` (where `f s ≠ 0`), then `f s ≠ 0` on ALL of
`{s | θ < s.re}`! -/
private lemma zeroFree_entire_of_analytic_logDeriv {θ : ℝ} (hθ : θ < 1)
    {f H : ℂ → ℂ} (hf : Differentiable ℂ f) (hf2 : f 2 ≠ 0)
    (hH : DifferentiableOn ℂ H {s : ℂ | θ < s.re})
    (hEq : ∀ s : ℂ, 1 < s.re → f s ≠ 0 → -deriv f s / f s = H s) :
    ∀ s : ℂ, θ < s.re → f s ≠ 0 := by
  set U : Set ℂ := {s : ℂ | θ < s.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt θ
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  have h2U : (2 : ℂ) ∈ U := by change θ < (2 : ℂ).re; simp; linarith
  have hf_an : AnalyticOnNhd ℂ f U := hf.differentiableOn.analyticOnNhd hU_open
  have hF_an : AnalyticOnNhd ℂ (fun s => -deriv f s) U := fun s hs => (hf_an s hs).deriv.neg
  have hG_an : AnalyticOnNhd ℂ (fun s => f s * H s) U :=
    (hf.differentiableOn.mul hH).analyticOnNhd hU_open
  have hEv : (fun s => -deriv f s) =ᶠ[𝓝 (2 : ℂ)] (fun s => f s * H s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by simp : (1 : ℝ) < (2 : ℂ).re),
      (hf_an 2 h2U).continuousAt.eventually_ne hf2] with s hs1 hfs
    have h := hEq s hs1 hfs
    rw [mul_comm]
    exact (div_eq_iff hfs).mp h
  have hODE : ∀ s ∈ U, -deriv f s = f s * H s :=
    fun s hs => hF_an.eqOn_of_preconnected_of_eventuallyEq hG_an hU_pre h2U hEv hs
  intro ρ hρU hfρ
  have hfρ_an : AnalyticAt ℂ f ρ := hf_an ρ hρU
  have htop : analyticOrderAt f ρ ≠ ⊤ := by
    intro h
    have h0 := analyticOrderAt_eq_top.mp h
    exact hf2 (hf_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_pre hρU h0 h2U)
  obtain ⟨g, hg_an, hgρ, hfg⟩ := hfρ_an.analyticOrderAt_ne_top.mp htop
  set m := analyticOrderNatAt f ρ with hm_def
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hord0 : analyticOrderAt f ρ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop, ← hm_def, hm0']; simp
    exact ((hfρ_an.analyticOrderAt_eq_zero).mp hord0) hfρ
  have hnear : ∀ᶠ z in 𝓝[≠] ρ,
      (m : ℂ) * g z + (z - ρ) * deriv g z = -(z - ρ) * g z * H z := by
    have hU_ev : ∀ᶠ z in 𝓝 ρ, z ∈ U := hU_open.mem_nhds hρU
    have hnhds : ∀ᶠ z in 𝓝 ρ,
        (∀ᶠ w in 𝓝 z, f w = (w - ρ) ^ m • g w) ∧ z ∈ U ∧ AnalyticAt ℂ g z :=
      (Filter.Eventually.eventually_nhds hfg).and (hU_ev.and hg_an.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with z ⟨hz1, hzU, hgz⟩ hzne
    have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    have hdz : HasDerivAt (fun w => (w - ρ) ^ m * g w)
        ((m : ℂ) * (z - ρ) ^ (m - 1) * 1 * g z + (z - ρ) ^ m * deriv g z) z :=
      (((hasDerivAt_id' z).sub_const ρ).pow m).mul hgz.differentiableAt.hasDerivAt
    have hdf : deriv f z = (m : ℂ) * (z - ρ) ^ (m - 1) * g z + (z - ρ) ^ m * deriv g z := by
      have hev' : f =ᶠ[𝓝 z] fun w => (w - ρ) ^ m * g w := by
        filter_upwards [hz1] with w hw; simpa [smul_eq_mul] using hw
      rw [hev'.deriv_eq, hdz.deriv]; ring
    have hfz : f z = (z - ρ) ^ m * g z := by simpa [smul_eq_mul] using hz1.self_of_nhds
    have hode := hODE z hzU
    rw [hdf, hfz] at hode
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hpow_ne : (z - ρ) ^ j ≠ 0 := pow_ne_zero j hzρ
    have hfactor : (z - ρ) ^ j * ((m : ℂ) * g z + (z - ρ) * deriv g z) =
        (z - ρ) ^ j * (-(z - ρ) * g z * H z) := by
      rw [hj, Nat.add_sub_cancel, pow_succ] at hode
      rw [hj]
      linear_combination -hode
    exact mul_left_cancel₀ hpow_ne hfactor
  have hLHS : Tendsto (fun z : ℂ => (m : ℂ) * g z + (z - ρ) * deriv g z) (𝓝[≠] ρ)
      (𝓝 ((m : ℂ) * g ρ + (ρ - ρ) * deriv g ρ)) :=
    (((hg_an.continuousAt.tendsto.const_mul (m : ℂ)).add
      ((tendsto_id.sub_const ρ).mul hg_an.deriv.continuousAt.tendsto))).mono_left nhdsWithin_le_nhds
  have hH_cont : ContinuousAt H ρ :=
    ((hH ρ hρU).differentiableAt (hU_open.mem_nhds hρU)).continuousAt
  have hRHS : Tendsto (fun z : ℂ => -(z - ρ) * g z * H z) (𝓝[≠] ρ)
      (𝓝 (-(ρ - ρ) * g ρ * H ρ)) :=
    ((((tendsto_id.sub_const ρ).neg.mul hg_an.continuousAt.tendsto).mul
      hH_cont.tendsto)).mono_left nhdsWithin_le_nhds
  have heq_lim := tendsto_nhds_unique (hLHS.congr' hnear) hRHS
  simp only [sub_self, zero_mul, neg_zero, add_zero] at heq_lim
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hm_pos.ne') hgρ heq_lim

/-- **UNCONDITIONAL CONVERSE DIRECTION (`‖ψ(x, χ)‖ = O(x^{θ + ε}) → ZeroFreeHalfPlaneL χ θ`)**:
for EVERY `q [NeZero q]`, EVERY non-principal `χ ≠ 1`, and EVERY `θ < 1`, if
`∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, ‖chebyshevPsiChar χ x‖ ≤ C * x ^ (θ + ε)`, then
`-L'/L(s, χ)` continues holomorphically across `Re(s) > θ` via summation by parts on
`∑ Λ(n) χ(n) n^{-s}` and therefore `ZeroFreeHalfPlaneL χ θ` holds! -/
theorem zeroFreeHalfPlaneL_of_psiChar_rpow_eps {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ : ℝ} (_hθ1 : θ < 1)
    (hpsi : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C * x ^ (θ + ε)) :
    ZeroFreeHalfPlaneL χ θ := by
  intro s hs _
  rcases lt_or_ge s.re 1 with hlt1 | hge1
  · set ε : ℝ := (s.re - θ) / 2 with hε_def
    have hε0 : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨C, hC_pos, hCbd⟩ := hpsi ε hε0
    set θ' : ℝ := θ + ε with hθ'_def
    have hθ'_lt1 : θ' < 1 := by rw [hθ'_def, hε_def]; linarith
    have hθ'_lt_s : θ' < s.re := by rw [hθ'_def, hε_def]; linarith
    -- Extend `∀ x ≥ 2` to `∀ x ≥ 1` (on `[1, 2)`, `chebyshevPsiChar χ x = 0`!)
    have hbd1 : ∀ t : ℝ, 1 ≤ t →
        ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q) * (Λ n : ℂ)) t‖ ≤
          C * t ^ θ' := by
      intro t ht1
      rw [stepSum_twist_vonMangoldt_eq_chebyshevPsiChar]
      by_cases ht2 : 2 ≤ t
      · exact hCbd t ht2
      · push Not at ht2
        have hfl : ⌊t⌋₊ = 1 :=
          (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; exact ht1, by norm_num; exact ht2⟩
        have hzero : Stage2DirichletAP.chebyshevPsiChar χ t = 0 := by
          unfold Stage2DirichletAP.chebyshevPsiChar
          rw [hfl]
          simp [Finset.sum_range_succ, ArithmeticFunction.vonMangoldt_apply_one]
        rw [hzero, norm_zero]
        exact mul_nonneg hC_pos.le (Real.rpow_nonneg (by linarith) _)
    let H : ℂ → ℂ := fun z =>
      z * ∫ t in Set.Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q) * (Λ n : ℂ)) t *
          (t : ℂ) ^ (-z - 1)
    have hH_diff : DifferentiableOn ℂ H {z : ℂ | θ' < z.re} := by
      intro z hz
      have hd := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound
        (Stage3RealAnalyticLandau.measurable_stepSum _) hC_pos.le hbd1 hz
      exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt
    have hH_eq : ∀ z : ℂ, 1 < z.re → DirichletCharacter.LFunction χ z ≠ 0 →
        -deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z = H z := by
      intro z hz _
      rw [← RHDirect.LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div χ hz]
      exact Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hbd1
        (lt_trans hθ'_lt1 hz) (χ.LSeriesSummable_twist_vonMangoldt hz)
    exact zeroFree_entire_of_analytic_logDeriv hθ'_lt1
      (DirichletCharacter.differentiable_LFunction hχ)
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp))
      hH_diff hH_eq s hθ'_lt_s
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hge1

/-- **UNCONDITIONAL BIDIRECTIONAL EQUIVALENCE (`ZeroFreeHalfPlaneL χ θ ↔ ψ(x, χ) = O(x^{θ + ε})`)**:
for EVERY modulus `q ≥ 1` (`[NeZero q]`), EVERY non-principal `χ ≠ 1` mod `q`, and EVERY `0 < θ < 1`:
`ZeroFreeHalfPlaneL χ θ ↔ ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, ‖chebyshevPsiChar χ x‖ ≤ C * x ^ (θ + ε)`. -/
theorem zeroFreeHalfPlaneL_iff_psiChar_rpow_eps {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ZeroFreeHalfPlaneL χ θ ↔
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C * x ^ (θ + ε)) :=
  ⟨psiChar_rpow_eps_of_zeroFree_halfPlane hχ hθ0 hθ1,
   zeroFreeHalfPlaneL_of_psiChar_rpow_eps hχ hθ1⟩

/-- Principal-character counterpart of `zeroFreeHalfPlaneL_iff_psiChar_rpow_eps`:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `0 < θ < 1`,
`ZeroFreeHalfPlaneL (1 : DirichletCharacter ℂ q) θ ↔ ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, ‖chebyshevPsiChar 1 x - x‖ ≤ C * x ^ (θ + ε)`. -/
theorem zeroFreeHalfPlaneL_one_iff_psiChar_sub_x_rpow_eps (q : ℕ) [NeZero q]
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ZeroFreeHalfPlaneL (1 : DirichletCharacter ℂ q) θ ↔
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar (1 : DirichletCharacter ℂ q) x - (x : ℂ)‖ ≤
          C * x ^ (θ + ε)) := by
  rw [zeroFreeHalfPlaneL_one_iff_zeta q hθ0.le,
    Stage7VonMangoldtExplicit.zeroFree_halfPlane_iff_psi_rpow_eps hθ0 hθ1]
  have hlog_rpow : ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 2 ≤ x →
      (q.primeFactors.card : ℝ) * Real.log x ≤
        ((q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε) := by
    intro ε hε x hx2
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hlog := Real.log_le_rpow_div hx0.le hε
    have hxθ : (1 : ℝ) ≤ x ^ θ := Real.one_le_rpow hx1 hθ0.le
    have hxe : x ^ ε ≤ x ^ (θ + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc (q.primeFactors.card : ℝ) * Real.log x
        ≤ (q.primeFactors.card : ℝ) * (x ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = ((q.primeFactors.card : ℝ) / ε) * x ^ ε := by ring
      _ ≤ ((q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε) :=
          mul_le_mul_of_nonneg_left hxe (by positivity)
  constructor
  · intro hpsi ε hε
    obtain ⟨C, hC, hbd⟩ := hpsi ε hε
    refine ⟨C + (q.primeFactors.card : ℝ) / ε, by positivity, fun x hx2 => ?_⟩
    rw [Stage2DirichletAP.chebyshevPsiChar_one_eq_coprime, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hcop := Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_bounds (NeZero.pos q)
      (by linarith : 1 ≤ x)
    have h1 := hbd x hx2
    rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi] at h1
    have htri : |Stage2DirichletAP.chebyshevPsiCoprime q x - x| ≤
        |RHDirect.chebyshevPsi x - x| + (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) := by
      have habs := abs_sub_le (Stage2DirichletAP.chebyshevPsiCoprime q x) (RHDirect.chebyshevPsi x) x
      rw [abs_sub_comm (Stage2DirichletAP.chebyshevPsiCoprime q x) (RHDirect.chebyshevPsi x),
        abs_of_nonneg hcop.1] at habs
      linarith
    have h2 := hlog_rpow ε hε x hx2
    nlinarith
  · intro h1 ε hε
    obtain ⟨C, hC, hbd⟩ := h1 ε hε
    refine ⟨C + (q.primeFactors.card : ℝ) / ε, by positivity, fun x hx2 => ?_⟩
    rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
    have hcop := Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_bounds (NeZero.pos q)
      (by linarith : 1 ≤ x)
    have hb := hbd x hx2
    rw [Stage2DirichletAP.chebyshevPsiChar_one_eq_coprime, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at hb
    have htri : |RHDirect.chebyshevPsi x - x| ≤
        (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) +
        |Stage2DirichletAP.chebyshevPsiCoprime q x - x| := by
      have habs := abs_sub_le (RHDirect.chebyshevPsi x) (Stage2DirichletAP.chebyshevPsiCoprime q x) x
      rw [abs_of_nonneg hcop.1] at habs
      linarith
    have h2 := hlog_rpow ε hε x hx2
    nlinarith

/-! ## Section 3: Unconditional Master `GRH` Equivalences for Arithmetic Progressions -/

/-- Exact inverse character-orthogonality decomposition: for EVERY `q ≥ 1` (`[NeZero q]`),
EVERY `χ : DirichletCharacter ℂ q`, and EVERY `x : ℝ`,
`ψ(x, χ) = ∑_{0 ≤ a < q, (a, q) = 1} χ(a) * ψ(x; q, a)`. -/
theorem chebyshevPsiChar_eq_sum_coprime_psiAP {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        χ (a : ZMod q) * (Stage2DirichletAP.chebyshevPsiAP q a x : ℂ) := by
  classical
  have hq0 : 0 < q := NeZero.pos q
  set U : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)
  unfold Stage2DirichletAP.chebyshevPsiChar Stage2DirichletAP.chebyshevPsiAP
  have hrew :
      ∑ a ∈ U, χ (a : ZMod q) *
          ((∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          ∑ a ∈ U, χ (a : ZMod q) *
            ((if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ) := by
    calc ∑ a ∈ U, χ (a : ZMod q) *
            ((∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ)
        = ∑ a ∈ U, ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            χ (a : ZMod q) * ((if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Complex.ofReal_sum, Finset.mul_sum]
      _ = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ∑ a ∈ U,
            χ (a : ZMod q) * ((if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ) := Finset.sum_comm
  rw [hrew]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hcop : Nat.Coprime n q
  · have hrem_mem : n % q ∈ U := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hq0), ?_⟩
      change Nat.gcd (n % q) q = 1
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact hcop
    have huniq : ∀ a ∈ U, a ≠ n % q → ¬ (n ≡ a [MOD q]) := by
      intro a ha hne hmod
      have ha_lt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      apply hne
      have h1 : n % q = a % q := hmod
      rw [Nat.mod_eq_of_lt ha_lt] at h1
      exact h1.symm
    rw [Finset.sum_eq_single (n % q) (fun a ha hne => by rw [if_neg (huniq a ha hne)]; simp)
      (fun hnot => absurd hrem_mem hnot)]
    have hmod_self : n ≡ n % q [MOD q] := (Nat.mod_modEq n q).symm
    have hzmod : ((n % q : ℕ) : ZMod q) = (n : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff (n % q) n q).mpr (Nat.mod_modEq n q)
    rw [if_pos hmod_self, hzmod]
  · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
    rw [MulChar.map_nonunit _ hnu, zero_mul]
    symm
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha_cop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hnot_mod : ¬ (n ≡ a [MOD q]) := by
      intro hmod
      apply hcop
      change Nat.gcd n q = 1
      rw [Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec, Nat.gcd_comm]
      exact ha_cop
    rw [if_neg hnot_mod]; simp

/-- Character sum over reduced residues vanishes for every non-principal `χ ≠ 1`. -/
private lemma sum_coprime_dirichletChar_eq_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), χ (a : ZMod q) = 0 := by
  have hfilt : ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), χ (a : ZMod q) =
      ∑ a ∈ Finset.range q, χ (a : ZMod q) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hcop : Nat.Coprime a q
    · rw [if_pos hcop]
    · rw [if_neg hcop]
      have hnu : ¬ IsUnit (a : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime a q).mp hu)
      exact (MulChar.map_nonunit _ hnu).symm
  rw [hfilt]
  have hIco : Finset.range q = Finset.Ico 0 (0 + q) := by
    ext n; simp
  rw [hIco]
  exact Stage5DirichletLZeroFree.sum_dirichletChar_Ico_period hχ 0

/-- **UNCONDITIONAL MODULUS-BY-MODULUS EQUIVALENCE (`∀ χ mod q, ZeroFreeHalfPlaneL χ θ ↔ ∀ (a, q) = 1, ψ(x; q, a) - x / φ(q) = O(x^{θ + ε})`)**:
for EVERY modulus `q ≥ 1` (`[NeZero q]`) and EVERY `0 < θ < 1` (in particular `1 / 2 ≤ θ < 1`)! -/
theorem zeroFree_mod_q_iff_psiAP_rpow_eps (q : ℕ) [NeZero q] {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∀ χ : DirichletCharacter ℂ q, ZeroFreeHalfPlaneL χ θ) ↔
      (∀ a : ℕ, Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C * x ^ (θ + ε)) := by
  classical
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  constructor
  · -- Forward: zero-free half-plane for all `χ mod q` → `|ψ(x; q, a) - x/φ(q)| = O(x^{θ + ε})`
    intro hzf a hcop ε hε
    have hzeta : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
      (zeroFreeHalfPlaneL_one_iff_zeta q hθ0.le).mp (hzf 1)
    obtain ⟨C_ψ, hC_ψ, hpsi⟩ :=
      Stage7VonMangoldtExplicit.psi_rpow_eps_of_zeroFree_halfPlane hθ0 hθ1 hzeta ε hε
    -- Uniform bound over the finite set of non-principal characters mod `q`
    have hunif : ∀ S : Finset (DirichletCharacter ℂ q), (∀ χ ∈ S, χ ≠ 1) →
        ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ χ ∈ S, ∀ x : ℝ, 2 ≤ x →
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C₂ * x ^ (θ + ε) := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; exact ⟨1, one_pos, fun _ h => absurd h (Finset.notMem_empty _)⟩
      | @insert χ S' hnot ih =>
        intro hS
        have hχ := hS χ (Finset.mem_insert_self _ _)
        obtain ⟨C₁, hC₁, hbd₁⟩ := psiChar_rpow_eps_of_zeroFree_halfPlane hχ hθ0 hθ1 (hzf χ) ε hε
        obtain ⟨C₂, hC₂, hbd₂⟩ := ih fun ψ hψ => hS ψ (Finset.mem_insert_of_mem hψ)
        refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), fun ψ hψ x hx => ?_⟩
        rcases Finset.mem_insert.mp hψ with rfl | hmem
        · exact (hbd₁ x hx).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
        · exact (hbd₂ ψ hmem x hx).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))
    obtain ⟨C_χ, hC_χ, hchar⟩ := hunif (Finset.univ.erase 1) fun χ h => (Finset.mem_erase.mp h).1
    set C_fin : ℝ := C_ψ + (q.primeFactors.card : ℝ) / ε + C_χ
    refine ⟨C_fin, by positivity, fun x hx2 => ?_⟩
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have h1 : |RHDirect.chebyshevPsi x - x| ≤ C_ψ * x ^ (θ + ε) := by
      rw [Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]; exact hpsi x hx2
    have h2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C_χ * x ^ (θ + ε) := fun χ hχ =>
      hchar χ (Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ _⟩) x hx2
    have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop hx1
      (by positivity : 0 ≤ C_χ * x ^ (θ + ε)) h1 h2
    have hlog_bd : (q.primeFactors.card : ℝ) * Real.log x ≤
        ((q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε) := by
      have hlog := Real.log_le_rpow_div hx0.le hε
      have hxe : x ^ ε ≤ x ^ (θ + ε) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      calc (q.primeFactors.card : ℝ) * Real.log x
          ≤ (q.primeFactors.card : ℝ) * (x ^ ε / ε) :=
            mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ = ((q.primeFactors.card : ℝ) / ε) * x ^ ε := by ring
        _ ≤ ((q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε) :=
            mul_le_mul_of_nonneg_left hxe (by positivity)
    have hdiv_le : (C_ψ * x ^ (θ + ε) + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) ≤
        (C_ψ + (q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε) := by
      calc (C_ψ * x ^ (θ + ε) + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ)
          ≤ (C_ψ * x ^ (θ + ε) + ((q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε)) / 1 :=
            div_le_div₀ (by positivity) (by linarith) zero_lt_one hphi_ge1
        _ = (C_ψ + (q.primeFactors.card : ℝ) / ε) * x ^ (θ + ε) := by ring
    dsimp only [C_fin]
    linarith
  · -- Converse: `|ψ(x; q, a) - x/φ(q)| = O(x^{θ + ε})` for all `(a, q) = 1` → `ZeroFreeHalfPlaneL χ θ`
    intro hap χ
    set U : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)
    have hU_card : U.card = q.totient := by
      rw [Nat.totient_eq_card_coprime]
      congr 1; ext a; simp [U, Nat.coprime_comm]
    -- Uniform bound over `a ∈ U` for any `ε > 0`
    have hunif_U : ∀ ε : ℝ, 0 < ε → ∃ C_U : ℝ, 0 < C_U ∧
        ∀ a ∈ U, ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C_U * x ^ (θ + ε) := by
      intro ε hε
      have hgen : ∀ S : Finset ℕ, (∀ a ∈ S, Nat.Coprime a q) →
          ∃ C_S : ℝ, 0 < C_S ∧ ∀ a ∈ S, ∀ x : ℝ, 2 ≤ x →
            |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C_S * x ^ (θ + ε) := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _; exact ⟨1, one_pos, fun _ h => absurd h (Finset.notMem_empty _)⟩
        | @insert a S' hnot ih =>
          intro hS
          obtain ⟨C₁, hC₁, hbd₁⟩ := hap a (hS a (Finset.mem_insert_self _ _)) ε hε
          obtain ⟨C₂, hC₂, hbd₂⟩ := ih fun b hb => hS b (Finset.mem_insert_of_mem hb)
          refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), fun b hb x hx => ?_⟩
          rcases Finset.mem_insert.mp hb with rfl | hmem
          · exact (hbd₁ x hx).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
          · exact (hbd₂ b hmem x hx).trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))
      exact hgen U fun a ha => (Finset.mem_filter.mp ha).2
    by_cases hχ1 : χ = 1
    · subst hχ1
      rw [zeroFreeHalfPlaneL_one_iff_psiChar_sub_x_rpow_eps q hθ0 hθ1]
      intro ε hε
      obtain ⟨C_U, hC_U, hbd_U⟩ := hunif_U ε hε
      refine ⟨(q.totient : ℝ) * C_U, by positivity, fun x hx2 => ?_⟩
      have hsum_eq : Stage2DirichletAP.chebyshevPsiChar (1 : DirichletCharacter ℂ q) x - (x : ℂ) =
          ∑ a ∈ U, (((Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ) : ℝ) : ℂ)) := by
        rw [chebyshevPsiChar_eq_sum_coprime_psiAP]
        have h1 : ∑ a ∈ U, (1 : DirichletCharacter ℂ q) (a : ZMod q) *
              (Stage2DirichletAP.chebyshevPsiAP q a x : ℂ) =
            ∑ a ∈ U, (Stage2DirichletAP.chebyshevPsiAP q a x : ℂ) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
          rw [Stage2DirichletAP.principal_char_apply_nat, if_pos hcop, one_mul]
        have hx_sum : (x : ℂ) = ∑ _a ∈ U, ((x / (q.totient : ℝ) : ℝ) : ℂ) := by
          rw [Finset.sum_const, hU_card, nsmul_eq_mul]
          push_cast
          have hphiC : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hphi_pos.ne'
          field_simp [hphiC]
        rw [h1, hx_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => by push_cast; ring
      rw [hsum_eq]
      calc ‖∑ a ∈ U, (((Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ) : ℝ) : ℂ))‖
          ≤ ∑ a ∈ U, ‖(((Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ) : ℝ) : ℂ))‖ :=
            norm_sum_le _ _
        _ = ∑ a ∈ U, |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| := by
            refine Finset.sum_congr rfl fun a _ => by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ∑ _a ∈ U, C_U * x ^ (θ + ε) := Finset.sum_le_sum fun a ha => hbd_U a ha x hx2
        _ = (q.totient : ℝ) * C_U * x ^ (θ + ε) := by
            rw [Finset.sum_const, hU_card, nsmul_eq_mul]; ring
    · refine zeroFreeHalfPlaneL_of_psiChar_rpow_eps hχ1 hθ1 fun ε hε => ?_
      obtain ⟨C_U, hC_U, hbd_U⟩ := hunif_U ε hε
      refine ⟨(q.totient : ℝ) * C_U, by positivity, fun x hx2 => ?_⟩
      have hsum_zero : ∑ a ∈ U, χ (a : ZMod q) * ((x / (q.totient : ℝ) : ℝ) : ℂ) = 0 := by
        rw [← Finset.sum_mul, sum_coprime_dirichletChar_eq_zero hχ1, zero_mul]
      have hchar_eq : Stage2DirichletAP.chebyshevPsiChar χ x =
          ∑ a ∈ U, χ (a : ZMod q) *
            (((Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ) : ℝ) : ℂ)) := by
        rw [chebyshevPsiChar_eq_sum_coprime_psiAP, ← sub_zero (∑ a ∈ U, _), ← hsum_zero,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => by push_cast; ring
      rw [hchar_eq]
      calc ‖∑ a ∈ U, χ (a : ZMod q) *
              (((Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ) : ℝ) : ℂ))‖
          ≤ ∑ a ∈ U, ‖χ (a : ZMod q) *
              (((Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ) : ℝ) : ℂ))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ a ∈ U, |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)
        _ ≤ ∑ _a ∈ U, C_U * x ^ (θ + ε) := Finset.sum_le_sum fun a ha => hbd_U a ha x hx2
        _ = (q.totient : ℝ) * C_U * x ^ (θ + ε) := by
            rw [Finset.sum_const, hU_card, nsmul_eq_mul]; ring

/-- **Unconditional Equivalence Between `ψ(x; q, a)` and `θ(x; q, a)` Error Bounds**
for any `q, a` and any exponent `1 / 2 ≤ θ` (via `0 ≤ ψ(x; q, a) - θ(x; q, a) ≤ √x log x`). -/
theorem psiAP_rpow_eps_iff_thetaAP_rpow_eps (q a : ℕ) {θ : ℝ} (hθ : 1 / 2 ≤ θ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C * x ^ (θ + ε)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤ C * x ^ (θ + ε)) := by
  have hdiff_rpow : ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 2 ≤ x →
      |Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x| ≤
        (1 / ε) * x ^ (θ + ε) := by
    intro ε hε x hx2
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hle := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a x
    have hup := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a hx1
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have hlog := Real.log_le_rpow_div hx0.le hε
    have hsqrt : Real.sqrt x ≤ x ^ θ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 hθ
    calc Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x
        ≤ Real.sqrt x * Real.log x := hup
      _ ≤ x ^ θ * (x ^ ε / ε) :=
          mul_le_mul hsqrt hlog (Real.log_nonneg hx1) (Real.rpow_nonneg hx0.le _)
      _ = (1 / ε) * (x ^ θ * x ^ ε) := by ring
      _ = (1 / ε) * x ^ (θ + ε) := by rw [← Real.rpow_add hx0]
  constructor
  · intro hpsi ε hε
    obtain ⟨C, hC, hbd⟩ := hpsi ε hε
    refine ⟨C + 1 / ε, by positivity, fun x hx2 => ?_⟩
    have htri : |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
        |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| +
        |Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x| := by
      have h1 := abs_sub_le (Stage2DirichletAP.chebyshevThetaAP q a x)
        (Stage2DirichletAP.chebyshevPsiAP q a x) (x / (q.totient : ℝ))
      rw [abs_sub_comm (Stage2DirichletAP.chebyshevThetaAP q a x)
        (Stage2DirichletAP.chebyshevPsiAP q a x)] at h1
      linarith
    linarith [hbd x hx2, hdiff_rpow ε hε x hx2]
  · intro hth ε hε
    obtain ⟨C, hC, hbd⟩ := hth ε hε
    refine ⟨C + 1 / ε, by positivity, fun x hx2 => ?_⟩
    have htri : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
        |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| +
        |Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x| := by
      have h1 := abs_sub_le (Stage2DirichletAP.chebyshevPsiAP q a x)
        (Stage2DirichletAP.chebyshevThetaAP q a x) (x / (q.totient : ℝ))
      linarith
    linarith [hbd x hx2, hdiff_rpow ε hε x hx2]

/-- **UNCONDITIONAL MODULUS-BY-MODULUS `θ(x; q, a)` EQUIVALENCE**:
for EVERY `q ≥ 1` (`[NeZero q]`) and `1 / 2 ≤ θ < 1`:
`(∀ χ mod q, ZeroFreeHalfPlaneL χ θ) ↔ (∀ (a, q) = 1, ∀ ε > 0, |θ(x; q, a) - x / φ(q)| = O(x^{θ + ε}))`. -/
theorem zeroFree_mod_q_iff_thetaAP_rpow_eps (q : ℕ) [NeZero q] {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    (∀ χ : DirichletCharacter ℂ q, ZeroFreeHalfPlaneL χ θ) ↔
      (∀ a : ℕ, Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤ C * x ^ (θ + ε)) := by
  rw [zeroFree_mod_q_iff_psiAP_rpow_eps q (by linarith) hθ1]
  exact forall₂_congr fun a _ => psiAP_rpow_eps_iff_thetaAP_rpow_eps q a hθ

/-- **MODULUS-BY-MODULUS `GRH` EQUIVALENCE FOR `ψ(x; q, a)`** (`θ = 1 / 2`). -/
theorem grh_mod_q_iff_psiAP_sqrt_eps (q : ℕ) [NeZero q] :
    (∀ χ : DirichletCharacter ℂ q, ZeroFreeHalfPlaneL χ (1 / 2)) ↔
      (∀ a : ℕ, Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
            C * x ^ ((1 : ℝ) / 2 + ε)) :=
  zeroFree_mod_q_iff_psiAP_rpow_eps q (by norm_num) (by norm_num)

/-- **MODULUS-BY-MODULUS `GRH` EQUIVALENCE FOR `θ(x; q, a)`** (`θ = 1 / 2`). -/
theorem grh_mod_q_iff_thetaAP_sqrt_eps (q : ℕ) [NeZero q] :
    (∀ χ : DirichletCharacter ℂ q, ZeroFreeHalfPlaneL χ (1 / 2)) ↔
      (∀ a : ℕ, Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
            C * x ^ ((1 : ℝ) / 2 + ε)) :=
  zeroFree_mod_q_iff_thetaAP_rpow_eps q le_rfl (by norm_num)

/-- **MASTER UNCONDITIONAL GLOBAL `GRH` EQUIVALENCE #1 (`DirichletLZerosOnLine ↔ ψ(x; q, a) - x / φ(q) = O(x^{1/2 + ε})`)**
(0 assumptions, directly on Mathlib's `DirichletCharacter.LFunction`!). -/
theorem grh_iff_psiAP_sqrt_eps :
    DirichletLZerosOnLine ↔
      (∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
            C * x ^ ((1 : ℝ) / 2 + ε)) := by
  rw [← forall_zeroFreeHalfPlaneL_half_iff_dirichletLZerosOnLine]
  exact forall_congr' fun q => forall_congr' fun _ => grh_mod_q_iff_psiAP_sqrt_eps q

/-- **MASTER UNCONDITIONAL GLOBAL `GRH` EQUIVALENCE #2 (`DirichletLZerosOnLine ↔ θ(x; q, a) - x / φ(q) = O(x^{1/2 + ε})`)**
(0 assumptions, directly on Mathlib's `DirichletCharacter.LFunction`!). -/
theorem grh_iff_thetaAP_sqrt_eps :
    DirichletLZerosOnLine ↔
      (∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
            C * x ^ ((1 : ℝ) / 2 + ε)) := by
  rw [← forall_zeroFreeHalfPlaneL_half_iff_dirichletLZerosOnLine]
  exact forall_congr' fun q => forall_congr' fun _ => grh_mod_q_iff_thetaAP_sqrt_eps q

/-- **MASTER UNCONDITIONAL `PrimitiveDirichletLZerosOnLine` EQUIVALENCES** (for `ψ` and `θ`). -/
theorem primitiveGRH_iff_psiAP_sqrt_eps :
    PrimitiveDirichletLZerosOnLine ↔
      (∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
            C * x ^ ((1 : ℝ) / 2 + ε)) :=
  RHDirect.dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine.symm.trans grh_iff_psiAP_sqrt_eps

theorem primitiveGRH_iff_thetaAP_sqrt_eps :
    PrimitiveDirichletLZerosOnLine ↔
      (∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
          |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
            C * x ^ ((1 : ℝ) / 2 + ε)) :=
  RHDirect.dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine.symm.trans grh_iff_thetaAP_sqrt_eps

/-- **COMBINED MASTER `GRH` EQUIVALENCE (`GRH ↔ ψ(x; q, a) - x/φ(q) = O(x^{1/2+ε}) ∧ θ(x; q, a) - x/φ(q) = O(x^{1/2+ε})`)**. -/
theorem grh_iff_psiAP_and_thetaAP_sqrt_eps :
    DirichletLZerosOnLine ↔
      ((∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
            |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
              C * x ^ ((1 : ℝ) / 2 + ε)) ∧
       (∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
            |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
              C * x ^ ((1 : ℝ) / 2 + ε))) :=
  ⟨fun h => ⟨grh_iff_psiAP_sqrt_eps.mp h, grh_iff_thetaAP_sqrt_eps.mp h⟩,
   fun h => grh_iff_psiAP_sqrt_eps.mpr h.1⟩

/-! ## Section 4: Unconditional Non-Trivial Zero Count `N(T, χ)` for Primitive `completedLFunction χ` -/

/-- Exact finite set of critical-strip zeros of a primitive `completedLFunction χ` (`χ ≠ 1`)
with `|ρ.im| < T`. -/
def lFunctionZeroSet {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (T : ℝ) : Finset ℂ :=
  ((Stage8HadamardLFunction.finite_completedLFunction_zeros_le_height hprim hχ
      (le_max_right T 2)).toFinset).filter fun ρ => |ρ.im| < T

/-- **Exact Multiplicity-Weighted Symmetric Zero Count `N(T, χ)`** of `completedLFunction χ`
(equivalently `LFunction χ`) in `0 < Re(s) < 1, |Im(s)| < T`. -/
def lFunctionZeroCount {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (T : ℝ) : ℝ :=
  ∑ ρ ∈ lFunctionZeroSet hprim hχ T,
    (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)

/-- Monotonicity of `lFunctionZeroCount` in `T`. -/
theorem lFunctionZeroCount_mono {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    lFunctionZeroCount hprim hχ T₁ ≤ lFunctionZeroCount hprim hχ T₂ := by
  unfold lFunctionZeroCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
  intro ρ hρ
  simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ ⊢
  exact ⟨⟨hρ.1.1, (hρ.2.le.trans hT).trans (le_max_left T₂ 2)⟩, lt_of_lt_of_le hρ.2 hT⟩

/-- Exact Dirichlet Gamma-factor phase `ϑ_χ(T) = ∫_0^T Re(logDeriv (gammaFactor χ) (1/2 + i t)) dt`. -/
def dirichletGammaPhase {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (logDeriv (DirichletCharacter.gammaFactor χ) ((1 / 2 : ℂ) + I * (t : ℂ))).re

/-- Exact Backlund remainder `S(T, χ)` along `[2 - i T, 2 + i T]` and `[1/2 ± i T, 2 ± i T]`. -/
def backlundSChar {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  (1 / Real.pi) *
    ((∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re) -
     (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im) +
     (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im))

/-- Helper: `logDeriv` of `gammaFactor χ` is holomorphic on `Re(s) > 0`. -/
private lemma differentiableOn_logDeriv_gammaFactor {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DifferentiableOn ℂ (logDeriv (DirichletCharacter.gammaFactor χ)) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  intro s hs
  change 0 < s.re at hs
  rcases χ.even_or_odd with he | ho
  · have hev : logDeriv (DirichletCharacter.gammaFactor χ) =ᶠ[𝓝 s]
        fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (w / 2) := by
      filter_upwards [hopen.mem_nhds hs] with w hw
      rw [logDeriv_apply, Stage8HadamardLFunction.logDeriv_gammaFactor_even he hw]
    have hdig : DifferentiableAt ℂ (fun w : ℂ => Complex.digamma (w / 2)) s := by
      have h1 : DifferentiableAt ℂ Complex.digamma (s / 2) :=
        (Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos (s / 2) (by simp; linarith)).differentiableAt
          (hopen.mem_nhds (by simp; linarith))
      exact h1.comp s (differentiableAt_id.div_const (2 : ℂ))
    exact (((differentiableAt_const _).add ((differentiableAt_const _).mul hdig)).congr_of_eventuallyEq hev).differentiableWithinAt
  · have hev : logDeriv (DirichletCharacter.gammaFactor χ) =ᶠ[𝓝 s]
        fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((w + 1) / 2) := by
      filter_upwards [hopen.mem_nhds hs] with w hw
      rw [logDeriv_apply, Stage8HadamardLFunction.logDeriv_gammaFactor_odd ho hw]
    have hdig : DifferentiableAt ℂ (fun w : ℂ => Complex.digamma ((w + 1) / 2)) s := by
      have h1 : DifferentiableAt ℂ Complex.digamma ((s + 1) / 2) :=
        (Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos ((s + 1) / 2) (by simp; linarith)).differentiableAt
          (hopen.mem_nhds (by simp; linarith))
      exact h1.comp s ((differentiableAt_id.add (differentiableAt_const 1)).div_const (2 : ℂ))
    exact (((differentiableAt_const _).add ((differentiableAt_const _).mul hdig)).congr_of_eventuallyEq hev).differentiableWithinAt

/-- Helper: conjugation symmetry of `logDeriv (gammaFactor χ)` on `Re(s) > 0`. -/
private lemma logDeriv_gammaFactor_conj {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv (DirichletCharacter.gammaFactor χ) (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv (DirichletCharacter.gammaFactor χ) s) := by
  have hs' : 0 < (starRingEnd ℂ s).re := by simpa using hs
  rcases χ.even_or_odd with he | ho
  · rw [logDeriv_apply, logDeriv_apply,
      Stage8HadamardLFunction.logDeriv_gammaFactor_even he hs',
      Stage8HadamardLFunction.logDeriv_gammaFactor_even he hs,
      map_add, map_neg, Complex.conj_ofReal, map_mul, map_div₀, map_one, map_ofNat,
      ← Stage7VonMangoldtExplicit.digamma_conj (by simp; linarith : 0 < (s / 2).re)]
    congr 2; rw [map_div₀, map_ofNat]
  · rw [logDeriv_apply, logDeriv_apply,
      Stage8HadamardLFunction.logDeriv_gammaFactor_odd ho hs',
      Stage8HadamardLFunction.logDeriv_gammaFactor_odd ho hs,
      map_add, map_neg, Complex.conj_ofReal, map_mul, map_div₀, map_one, map_ofNat,
      ← Stage7VonMangoldtExplicit.digamma_conj (by simp; linarith : 0 < ((s + 1) / 2).re)]
    congr 2; rw [map_div₀, map_add, map_one, map_ofNat]

/-- **Exact Half-Contour Argument Principle for Primitive `symmetricCompletedLFunction χ`**:
for every primitive `χ ≠ 1` and every `T > 0` with no zero of `LFunction χ` on `[0, 1] × {±T}`,
`lFunctionZeroCount hprim hχ T = (1 / π) * (∫_{-T}^T Re(logDeriv Λ_sym (2 + i t)) dt - ∫_{1/2}^2 Im(logDeriv Λ_sym (σ + i T)) dσ + ∫_{1/2}^2 Im(logDeriv Λ_sym (σ - i T)) dσ)`. -/
theorem lFunctionZeroCount_eq_half_contour {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {T : ℝ} (hT : 0 < T)
    (hnz : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ)) ≠ 0 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) - I * (T : ℂ)) ≠ 0) :
    let Λsym := Stage6LFunctionOrder.symmetricCompletedLFunction χ
    lFunctionZeroCount hprim hχ T = (1 / Real.pi) *
      ((∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re) -
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im) +
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im)) := by
  classical
  intro Λsym
  have hΛ_diff : Differentiable ℂ Λsym :=
    Stage6LFunctionOrder.differentiable_symmetricCompletedLFunction hχ
  have hΛ_an : AnalyticOnNhd ℂ Λsym Set.univ := hΛ_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hΛ0 : Λsym 0 ≠ 0 :=
    (Stage6LFunctionOrder.symmetricCompletedLFunction_eq_zero_iff χ 0).not.mpr
      (Stage6LFunctionOrder.completedLFunction_zero_ne_zero hprim hχ)
  have hntop : ∀ z : ℂ, analyticOrderAt Λsym z ≠ ⊤ := fun z htop => by
    have h0 := analyticOrderAt_eq_top.mp htop
    exact hΛ0 (hΛ_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ 0))
  set Z : Finset ℂ := lFunctionZeroSet hprim hχ T
  have hZ_rect : ∀ ρ ∈ Z, ρ ∈ Stage5ContourExplicit.openRect (-1) 2 (-T) T := by
    intro ρ hρ
    simp only [Z, lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    obtain ⟨h0, h1, _⟩ :=
      (Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hχ ρ).mp hρ.1.1
    exact ⟨⟨by linarith, by linarith⟩, abs_lt.mp hρ.2⟩
  have hnz_outside : ∀ s ∈ Stage5ContourExplicit.closedRect (-1) 2 (-T) T, s ∉ Z → Λsym s ≠ 0 := by
    intro s hs hsZ h0
    have hc0 : DirichletCharacter.completedLFunction χ s = 0 :=
      (Stage6LFunctionOrder.symmetricCompletedLFunction_eq_zero_iff χ s).mp h0
    obtain ⟨h0re, h1re, hLz⟩ :=
      (Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hχ s).mp hc0
    have habs : |s.im| ≤ T := abs_le.mpr hs.2
    rcases eq_or_lt_of_le habs with hEq | hlt
    · rcases abs_eq hT.le |>.mp hEq with himT | himNeg
      · have hs_eq : s = (s.re : ℂ) + I * (T : ℂ) := Complex.ext (by simp) (by simp [himT])
        rw [hs_eq] at hLz
        exact (hnz s.re ⟨h0re.le, h1re.le⟩).1 hLz
      · have hs_eq : s = (s.re : ℂ) - I * (T : ℂ) := Complex.ext (by simp) (by simp [himNeg])
        rw [hs_eq] at hLz
        exact (hnz s.re ⟨h0re.le, h1re.le⟩).2 hLz
    · apply hsZ
      simp only [Z, lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨⟨hc0, habs.trans (le_max_left T 2)⟩, hlt⟩
  have harg := Stage7VonMangoldtExplicit.rect_argument_principle_holomorphic
    (f := Λsym) (σ₀ := -1) (c := 2) (y₀ := -T) (y₁ := T)
    (by norm_num) (by linarith) Z hZ_rect
    (fun s _ => hΛ_an s (Set.mem_univ s)) (fun z _ => hntop z) hnz_outside
  -- Reflection symmetry: `logDeriv Λsym (1 - conj s) = -conj (logDeriv Λsym s)`
  have hrefl_ld : ∀ s : ℂ, Λsym s ≠ 0 →
      logDeriv Λsym (1 - starRingEnd ℂ s) = -starRingEnd ℂ (logDeriv Λsym s) := fun s hs => by
    rw [logDeriv_apply, logDeriv_apply]
    exact Stage8HadamardLFunction.logDeriv_symmetricCompletedLFunction_one_sub_conj hprim hχ hs
  have hnz_top : ∀ σ ∈ Set.Icc (-1 : ℝ) 2, Λsym ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := fun σ hσ =>
    hnz_outside _ ⟨by simpa using hσ, by simp [hT.le]⟩ fun hz => by
      have := (hZ_rect _ hz).2.2; simp at this
  have hnz_bot : ∀ σ ∈ Set.Icc (-1 : ℝ) 2, Λsym ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 := fun σ hσ =>
    hnz_outside _ ⟨by simpa using hσ, by simp [hT.le]⟩ fun hz => by
      have := (hZ_rect _ hz).2.1; simp at this
  have hnz_right : ∀ t : ℝ, Λsym ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := fun t =>
    (Stage6LFunctionOrder.symmetricCompletedLFunction_eq_zero_iff χ _).not.mpr
      (Stage6LFunctionOrder.completedLFunction_ne_zero_of_one_le_re hχ (by simp))
  -- Continuity of `logDeriv Λsym` on top, bottom, and right sides
  have hcont_top : ContinuousOn (fun σ : ℝ => logDeriv Λsym ((σ : ℂ) + (T : ℂ) * I)) (Set.Icc (-1 : ℝ) 2) := by
    intro σ hσ
    have hld : ContinuousAt (logDeriv Λsym) ((σ : ℂ) + (T : ℂ) * I) :=
      ((hΛ_an _ (Set.mem_univ _)).deriv.continuousAt).div hΛ_diff.continuous.continuousAt (hnz_top σ hσ)
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (T : ℂ) * I) hld (by fun_prop)).continuousWithinAt
  have hcont_bot : ContinuousOn (fun σ : ℝ => logDeriv Λsym ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) (Set.Icc (-1 : ℝ) 2) := by
    intro σ hσ
    have hld : ContinuousAt (logDeriv Λsym) ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) :=
      ((hΛ_an _ (Set.mem_univ _)).deriv.continuousAt).div hΛ_diff.continuous.continuousAt (hnz_bot σ hσ)
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + ((-T : ℝ) : ℂ) * I) hld (by fun_prop)).continuousWithinAt
  have hcont_right : ContinuousOn (fun t : ℝ => logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    intro t _
    have hld : ContinuousAt (logDeriv Λsym) ((2 : ℂ) + (t : ℂ) * I) :=
      ((hΛ_an _ (Set.mem_univ _)).deriv.continuousAt).div hΛ_diff.continuous.continuousAt (hnz_right t)
    exact (ContinuousAt.comp (f := fun y : ℝ => (2 : ℂ) + (y : ℂ) * I) hld (by fun_prop)).continuousWithinAt
  -- Helper for both horizontal sides: `∫_{-1}^2 logDeriv Λsym (σ + y * I) dσ = 2 * I * ∫_{1/2}^2 Im(...)`
  have hhoriz_eval : ∀ y : ℝ,
      (∀ σ ∈ Set.Icc (-1 : ℝ) 2, Λsym ((σ : ℂ) + (y : ℂ) * I) ≠ 0) →
      ContinuousOn (fun σ : ℝ => logDeriv Λsym ((σ : ℂ) + (y : ℂ) * I)) (Set.Icc (-1 : ℝ) 2) →
      ∫ σ in (-1 : ℝ)..2, logDeriv Λsym ((σ : ℂ) + (y : ℂ) * I) =
        2 * I * ((∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + (y : ℂ) * I)).im : ℝ) : ℂ) := by
    intro y hnz_y hcont_y
    have hint_l : IntervalIntegrable (fun σ : ℝ => logDeriv Λsym ((σ : ℂ) + (y : ℂ) * I)) volume (-1) (1 / 2) :=
      (hcont_y.mono (by rw [Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)).intervalIntegrable
    have hint_r : IntervalIntegrable (fun σ : ℝ => logDeriv Λsym ((σ : ℂ) + (y : ℂ) * I)) volume (1 / 2) 2 :=
      (hcont_y.mono (by rw [Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_l hint_r]
    have hrefl_l : ∫ σ in (-1 : ℝ)..(1 / 2 : ℝ), logDeriv Λsym ((σ : ℂ) + (y : ℂ) * I) =
        ∫ u in (1 / 2 : ℝ)..2, -starRingEnd ℂ (logDeriv Λsym ((u : ℂ) + (y : ℂ) * I)) := by
      have h1 := intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => logDeriv Λsym ((x : ℂ) + (y : ℂ) * I)) (1 : ℝ) (a := (1 / 2 : ℝ)) (b := 2)
      norm_num at h1
      rw [← h1]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have harg_eq : (1 : ℂ) - (u : ℂ) + (y : ℂ) * I = 1 - starRingEnd ℂ ((u : ℂ) + (y : ℂ) * I) :=
        Complex.ext (by simp) (by simp)
      rw [harg_eq]
      exact hrefl_ld _ (hnz_y u ⟨by linarith [hu.1], hu.2⟩)
    have hint_rc : IntervalIntegrable (fun u : ℝ => -starRingEnd ℂ (logDeriv Λsym ((u : ℂ) + (y : ℂ) * I)))
        volume (1 / 2) 2 :=
      ((Complex.continuous_conj.neg.comp_continuousOn hcont_y).mono
        (by rw [Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable
    rw [hrefl_l, ← intervalIntegral.integral_add hint_rc hint_r]
    have hpt : ∀ u : ℝ,
        -starRingEnd ℂ (logDeriv Λsym ((u : ℂ) + (y : ℂ) * I)) + logDeriv Λsym ((u : ℂ) + (y : ℂ) * I) =
          (2 * I) * (((logDeriv Λsym ((u : ℂ) + (y : ℂ) * I)).im : ℝ) : ℂ) := fun u => by
      apply Complex.ext <;> simp
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  have htop_eval := hhoriz_eval T hnz_top hcont_top
  have hbot_eval := hhoriz_eval (-T) hnz_bot hcont_bot
  -- Vertical sides: `I * ∫_{-T}^T F(2+it) - I * ∫_{-T}^T F(-1+it) = 2 * I * ∫_{-T}^T Re F(2+it)`
  have hvert_eval :
      I * (∫ t in (-T)..T, logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in (-T)..T, logDeriv Λsym (((-1 : ℝ) : ℂ) + (t : ℂ) * I)) =
      2 * I * ((∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re : ℝ) : ℂ) := by
    have hleft_pt : ∀ t : ℝ,
        logDeriv Λsym (((-1 : ℝ) : ℂ) + (t : ℂ) * I) =
          -starRingEnd ℂ (logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)) := fun t => by
      have harg_eq : ((-1 : ℝ) : ℂ) + (t : ℂ) * I = 1 - starRingEnd ℂ ((2 : ℂ) + (t : ℂ) * I) :=
        Complex.ext (by simp; norm_num) (by simp)
      rw [harg_eq]
      exact hrefl_ld _ (hnz_right t)
    have hint_r : IntervalIntegrable (fun t : ℝ => logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)) volume (-T) T :=
      (hcont_right.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
    have hint_rc : IntervalIntegrable (fun t : ℝ => starRingEnd ℂ (logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)))
        volume (-T) T :=
      ((Complex.continuous_conj.comp_continuousOn hcont_right).mono
        (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
    simp_rw [hleft_pt, intervalIntegral.integral_neg]
    rw [mul_neg, sub_neg_eq_add, ← mul_add, ← intervalIntegral.integral_add hint_r hint_rc]
    have hpt : ∀ t : ℝ,
        logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I) + starRingEnd ℂ (logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)) =
          2 * (((logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)).re : ℝ) : ℂ) := fun t => by
      apply Complex.ext <;> simp
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    have hcomm : ∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + (t : ℂ) * I)).re =
        ∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re :=
      intervalIntegral.integral_congr fun t _ => by rw [mul_comm I (t : ℂ)]
    rw [hcomm]; ring
  -- Combine into `rectBoundaryIntegral` and divide by `2 * π * I`
  have htop_comm : ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + (T : ℂ) * I)).im =
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im :=
    intervalIntegral.integral_congr fun σ _ => by rw [mul_comm I (T : ℂ)]
  have hbot_comm : ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)).im =
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im :=
    intervalIntegral.integral_congr fun σ _ => by congr 2; push_cast; ring
  have hbdry_eval : Stage5ContourExplicit.rectBoundaryIntegral (logDeriv Λsym) (-1) 2 (-T) T =
      2 * I * (((∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im) : ℝ) : ℂ) := by
    unfold Stage5ContourExplicit.rectBoundaryIntegral
    simp only [Complex.ofReal_ofNat]
    have hrew : ((∫ x in (-1 : ℝ)..2, logDeriv Λsym ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          ∫ x in (-1 : ℝ)..2, logDeriv Λsym ((x : ℂ) + (T : ℂ) * I)) +
        I * (∫ y in (-T)..T, logDeriv Λsym ((2 : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in (-T)..T, logDeriv Λsym (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ((∫ x in (-1 : ℝ)..2, logDeriv Λsym ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          ∫ x in (-1 : ℝ)..2, logDeriv Λsym ((x : ℂ) + (T : ℂ) * I)) +
        (I * (∫ y in (-T)..T, logDeriv Λsym ((2 : ℂ) + (y : ℂ) * I)) -
          I * (∫ y in (-T)..T, logDeriv Λsym (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by ring
    rw [hrew, htop_eval, hbot_eval, hvert_eval, htop_comm, hbot_comm]
    push_cast; ring
  rw [hbdry_eval] at harg
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hLHS : (2 * (Real.pi : ℂ) * I)⁻¹ *
      (2 * I * (((∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im) : ℝ) : ℂ)) =
      (((1 / Real.pi) * ((∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im)) : ℝ) : ℂ) := by
    push_cast; field_simp [hpiC, Complex.I_ne_zero]
  have hRHS : (∑ z ∈ Z, (analyticOrderNatAt Λsym z : ℂ)) =
      ((lFunctionZeroCount hprim hχ T : ℝ) : ℂ) := by
    unfold lFunctionZeroCount
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Stage8HadamardLFunction.analyticOrderNatAt_symmetricCompletedLFunction_eq hprim hχ ρ]
    simp
  rw [hLHS, hRHS, Complex.ofReal_inj] at harg
  exact harg.symm

/-- Exact Cauchy evaluation of the `gammaFactor χ` contribution on `[1/2, 2] × [-T, T]`:
identically equal to `2 * dirichletGammaPhase χ T`. -/
theorem half_contour_arg_gammaFactor {q : ℕ} (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + I * (t : ℂ))).re) -
    (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + I * (T : ℂ))).im) +
    (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) - I * (T : ℂ))).im) =
      2 * dirichletGammaPhase χ T := by
  have hdiff : DifferentiableOn ℂ (logDeriv (DirichletCharacter.gammaFactor χ))
      (Stage5ContourExplicit.closedRect (1 / 2) 2 (-T) T) :=
    (differentiableOn_logDeriv_gammaFactor χ).mono fun s hs => lt_of_lt_of_le (by norm_num) hs.1.1
  have hcauchy := Stage5ContourExplicit.rectBoundaryIntegral_eq_zero_of_differentiableOn
    (by norm_num : (1 / 2 : ℝ) ≤ 2) (by linarith : -T ≤ T) hdiff
  have him := congrArg Complex.im hcauchy
  unfold Stage5ContourExplicit.rectBoundaryIntegral at him
  have hcont := hdiff.continuousOn
  have hint_bot : IntervalIntegrable (fun x : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      volume (1 / 2) 2 :=
    (hcont.comp (by fun_prop) fun x hx => by
      rw [Set.uIcc_of_le (by norm_num)] at hx; exact ⟨by simpa using hx, by simp [hT.le]⟩).intervalIntegrable
  have hint_top : IntervalIntegrable (fun x : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (T : ℂ) * I))
      volume (1 / 2) 2 :=
    (hcont.comp (by fun_prop) fun x hx => by
      rw [Set.uIcc_of_le (by norm_num)] at hx; exact ⟨by simpa using hx, by simp [hT.le]⟩).intervalIntegrable
  have hint_r : IntervalIntegrable (fun y : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + (y : ℂ) * I))
      volume (-T) T :=
    (hcont.comp (by fun_prop) fun y hy => by
      rw [Set.uIcc_of_le (by linarith)] at hy; exact ⟨by simp; norm_num, by simpa using hy⟩).intervalIntegrable
  have hint_l : IntervalIntegrable (fun y : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      volume (-T) T :=
    (hcont.comp (by fun_prop) fun y hy => by
      rw [Set.uIcc_of_le (by linarith)] at hy; exact ⟨by simp; norm_num, by simpa using hy⟩).intervalIntegrable
  have hbot_im : (∫ x in (1 / 2 : ℝ)..2, logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + ((-T : ℝ) : ℂ) * I)).im =
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) - I * (T : ℂ))).im := by
    have h1 := Complex.imCLM.intervalIntegral_comp_comm hint_bot
    simp only [Complex.imCLM_apply] at h1
    rw [← h1]
    exact intervalIntegral.integral_congr fun σ _ => by congr 2; push_cast; ring
  have htop_im : (∫ x in (1 / 2 : ℝ)..2, logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (T : ℂ) * I)).im =
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + I * (T : ℂ))).im := by
    have h1 := Complex.imCLM.intervalIntegral_comp_comm hint_top
    simp only [Complex.imCLM_apply] at h1
    rw [← h1]
    exact intervalIntegral.integral_congr fun σ _ => by rw [mul_comm I (T : ℂ)]
  have hr_re : (∫ y in (-T)..T, logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + (y : ℂ) * I)).re =
      ∫ t in (-T)..T, (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + I * (t : ℂ))).re := by
    have h1 := Complex.reCLM.intervalIntegral_comp_comm hint_r
    simp only [Complex.reCLM_apply] at h1
    rw [← h1]
    exact intervalIntegral.integral_congr fun t _ => by rw [mul_comm I (t : ℂ)]
  have hl_re : (∫ y in (-T)..T, logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
      2 * dirichletGammaPhase χ T := by
    have h1 := Complex.reCLM.intervalIntegral_comp_comm hint_l
    simp only [Complex.reCLM_apply] at h1
    rw [← h1]
    have hre_cont : ContinuousOn
        (fun y : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re)
        (Set.Icc (-T) T) :=
      Complex.continuous_re.comp_continuousOn
        (hcont.comp (by fun_prop) fun y hy => ⟨by simp; norm_num, by simpa using hy⟩)
    have hneg : IntervalIntegrable
        (fun y : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re)
        volume (-T) 0 :=
      (hre_cont.mono (by rw [Set.uIcc_of_le (by linarith)]; intro y hy; exact ⟨hy.1, by linarith [hy.2]⟩)).intervalIntegrable
    have hpos : IntervalIntegrable
        (fun y : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re)
        volume 0 T :=
      (hre_cont.mono (by rw [Set.uIcc_of_le hT.le]; intro y hy; exact ⟨by linarith [hy.1], hy.2⟩)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos]
    have heven : ∫ y in (-T)..(0 : ℝ), (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T, (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
      have hc := intervalIntegral.integral_comp_neg
        (f := fun y : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re)
        (a := (0 : ℝ)) (b := T)
      simp only [neg_zero] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr fun y _ => ?_
      have harg_eq : ((1 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I =
          starRingEnd ℂ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := Complex.ext (by simp) (by simp)
      rw [harg_eq, logDeriv_gammaFactor_conj χ (by simp), Complex.conj_re]
    rw [heven]
    unfold dirichletGammaPhase
    have hcomm : ∫ y in (0 : ℝ)..T, (logDeriv (DirichletCharacter.gammaFactor χ) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
        ∫ t in (0 : ℝ)..T, (logDeriv (DirichletCharacter.gammaFactor χ) ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
      intervalIntegral.integral_congr fun t _ => by
        have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
        rw [hcast, mul_comm I (t : ℂ)]
    rw [hcomm]; ring
  simp only [Complex.ofReal_ofNat, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im, hbot_im, htop_im, hr_re, hl_re] at him
  linarith

/-- Pointwise decomposition of `logDeriv (symmetricCompletedLFunction χ)` on `Re(s) > 0`
where `LFunction χ s ≠ 0`. -/
private lemma logDeriv_symmetricCompletedLFunction_decomp {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (Stage6LFunctionOrder.symmetricCompletedLFunction χ) s =
      ((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
      logDeriv (DirichletCharacter.gammaFactor χ) s +
      logDeriv (DirichletCharacter.LFunction χ) s := by
  have hG_ne : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    Stage6LFunctionOrder.gammaFactor_ne_zero_of_re_pos χ hs
  have hc_ne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    rw [Stage6LFunctionOrder.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hs]
    exact mul_ne_zero hL hG_ne
  have hsym := Stage8HadamardLFunction.logDeriv_symmetricCompletedLFunction_eq hχ hc_ne
  have hG_diff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hGammaℝ_diff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Complex.Gammaℝ w := by
      intro w hw
      have hne_neg : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
        intro m heq; have := congrArg Complex.re heq; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hfun : Complex.Gammaℝ =
          fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) * Complex.Gamma (z / 2) := by
        funext z; rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
      rw [hfun]
      have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2))) w := by
        fun_prop
      have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) w :=
        (Complex.differentiableAt_Gamma (w / 2) hne_neg).comp w (differentiableAt_id.div_const 2)
      exact h1.mul h2
    rcases χ.even_or_odd with he | ho
    · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext he.gammaFactor_def
      rw [hfun]; exact hGammaℝ_diff s hs
    · have hfun : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) :=
        funext ho.gammaFactor_def
      rw [hfun]
      exact (hGammaℝ_diff (s + 1) (by simp; linarith)).comp s (differentiableAt_id.add (differentiableAt_const 1))
  have hL_diff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    DirichletCharacter.differentiable_LFunction hχ s
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      fun z => DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z := by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs] with z (hz : 0 < z.re)
    exact Stage6LFunctionOrder.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hz
  have hderiv_eq : deriv (DirichletCharacter.completedLFunction χ) s =
      deriv (DirichletCharacter.LFunction χ) s * DirichletCharacter.gammaFactor χ s +
        DirichletCharacter.LFunction χ s * deriv (DirichletCharacter.gammaFactor χ) s := by
    rw [hev.deriv_eq, (hL_diff.hasDerivAt.fun_mul hG_diff.hasDerivAt).deriv]
  have hlogd_c : deriv (DirichletCharacter.completedLFunction χ) s /
      DirichletCharacter.completedLFunction χ s =
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s +
        deriv (DirichletCharacter.gammaFactor χ) s / DirichletCharacter.gammaFactor χ s := by
    rw [hderiv_eq, Stage6LFunctionOrder.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hs]
    field_simp [hL, hG_ne]
  rw [logDeriv_apply, logDeriv_apply, logDeriv_apply, hsym, hlogd_c]
  ring

/-- **UNCONDITIONAL EXACT BACKLUND FORMULA FOR EVERY PRIMITIVE `completedLFunction χ`**:
for every primitive `χ ≠ 1` mod `q` and every `T > 0` with no zero on `[0, 1] × {±T}`,
`lFunctionZeroCount hprim hχ T = (T / π) * Real.log q + (2 / π) * dirichletGammaPhase χ T + backlundSChar χ T`. -/
theorem backlund_LFunction_exact_formula {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {T : ℝ} (hT : 0 < T)
    (hnz : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ)) ≠ 0 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) - I * (T : ℂ)) ≠ 0) :
    lFunctionZeroCount hprim hχ T =
      (T / Real.pi) * Real.log (q : ℝ) +
      (2 / Real.pi) * dirichletGammaPhase χ T +
      backlundSChar χ T := by
  let Λsym := Stage6LFunctionOrder.symmetricCompletedLFunction χ
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
  have hL_nz_r : ∀ t : ℝ, DirichletCharacter.LFunction χ ((2 : ℂ) + I * (t : ℂ)) ≠ 0 := fun t =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp)
  have hL_nz_t : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ)) ≠ 0 := fun σ hσ => by
    rcases le_or_gt 1 σ with h1 | h1
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [h1])
    · exact (hnz σ ⟨by linarith [hσ.1], h1.le⟩).1
  have hL_nz_b : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) - I * (T : ℂ)) ≠ 0 := fun σ hσ => by
    rcases le_or_gt 1 σ with h1 | h1
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [h1])
    · exact (hnz σ ⟨by linarith [hσ.1], h1.le⟩).2
  -- Continuity of gammaFactor and LFunction log-derivatives on each segment
  have hG_cont_r : ContinuousOn
      (fun t : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + I * (t : ℂ))).re)
      (Set.uIcc (-T) T) :=
    Complex.continuous_re.comp_continuousOn
      ((differentiableOn_logDeriv_gammaFactor χ).continuousOn.comp (by fun_prop) fun t _ => by
        change 0 < ((2 : ℂ) + I * (t : ℂ)).re; simp)
  have hG_cont_t : ContinuousOn
      (fun σ : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + I * (T : ℂ))).im)
      (Set.uIcc (1 / 2) 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact Complex.continuous_im.comp_continuousOn
      ((differentiableOn_logDeriv_gammaFactor χ).continuousOn.comp (by fun_prop) fun σ hσ => by
        change 0 < ((σ : ℂ) + I * (T : ℂ)).re; simp; linarith [hσ.1])
  have hG_cont_b : ContinuousOn
      (fun σ : ℝ => (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) - I * (T : ℂ))).im)
      (Set.uIcc (1 / 2) 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact Complex.continuous_im.comp_continuousOn
      ((differentiableOn_logDeriv_gammaFactor χ).continuousOn.comp (by fun_prop) fun σ hσ => by
        change 0 < ((σ : ℂ) - I * (T : ℂ)).re; simp; linarith [hσ.1])
  have hL_cont_r : ContinuousOn
      (fun t : ℝ => (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re)
      (Set.uIcc (-T) T) :=
    Complex.continuous_re.comp_continuousOn fun t _ => by
      have hld : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) ((2 : ℂ) + I * (t : ℂ)) :=
        ((hL_an _ (Set.mem_univ _)).deriv.continuousAt).div
          (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt (hL_nz_r t)
      exact (ContinuousAt.comp (f := fun y : ℝ => (2 : ℂ) + I * (y : ℂ)) hld (by fun_prop)).continuousWithinAt
  have hL_cont_t : ContinuousOn
      (fun σ : ℝ => (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im)
      (Set.uIcc (1 / 2) 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    refine Complex.continuous_im.comp_continuousOn fun σ hσ => ?_
    have hld : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) ((σ : ℂ) + I * (T : ℂ)) :=
      ((hL_an _ (Set.mem_univ _)).deriv.continuousAt).div
        (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt (hL_nz_t σ hσ)
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + I * (T : ℂ)) hld (by fun_prop)).continuousWithinAt
  have hL_cont_b : ContinuousOn
      (fun σ : ℝ => (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im)
      (Set.uIcc (1 / 2) 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    refine Complex.continuous_im.comp_continuousOn fun σ hσ => ?_
    have hld : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) ((σ : ℂ) - I * (T : ℂ)) :=
      ((hL_an _ (Set.mem_univ _)).deriv.continuousAt).div
        (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt (hL_nz_b σ hσ)
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) - I * (T : ℂ)) hld (by fun_prop)).continuousWithinAt
  -- Split the three integrals
  have hv_split :
      ∫ t in (-T)..T, (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re =
        T * Real.log (q : ℝ) +
        (∫ t in (-T)..T, (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + I * (t : ℂ))).re) +
        (∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re) := by
    have hcongr : ∀ t ∈ Set.uIcc (-T) T,
        (logDeriv Λsym ((2 : ℂ) + I * (t : ℂ))).re =
          Real.log (q : ℝ) / 2 +
          (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + I * (t : ℂ))).re +
          (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re := fun t _ => by
      rw [logDeriv_symmetricCompletedLFunction_decomp hχ (by simp) (hL_nz_r t),
        Complex.add_re, Complex.add_re, Complex.ofReal_re]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add (intervalIntegrable_const.add hG_cont_r.intervalIntegrable)
        hL_cont_r.intervalIntegrable,
      intervalIntegral.integral_add intervalIntegrable_const hG_cont_r.intervalIntegrable,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have ht_split :
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im =
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + I * (T : ℂ))).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im) := by
    have hcongr : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (logDeriv Λsym ((σ : ℂ) + I * (T : ℂ))).im =
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + I * (T : ℂ))).im +
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im := fun σ hσ => by
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      rw [logDeriv_symmetricCompletedLFunction_decomp hχ (by simp; linarith [hσ.1]) (hL_nz_t σ hσ),
        Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add hG_cont_t.intervalIntegrable hL_cont_t.intervalIntegrable]
  have hb_split :
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im =
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) - I * (T : ℂ))).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im) := by
    have hcongr : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (logDeriv Λsym ((σ : ℂ) - I * (T : ℂ))).im =
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) - I * (T : ℂ))).im +
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im := fun σ hσ => by
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      rw [logDeriv_symmetricCompletedLFunction_decomp hχ (by simp; linarith [hσ.1]) (hL_nz_b σ hσ),
        Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add hG_cont_b.intervalIntegrable hL_cont_b.intervalIntegrable]
  rw [lFunctionZeroCount_eq_half_contour hprim hχ hT hnz, hv_split, ht_split, hb_split]
  have hgam := half_contour_arg_gammaFactor χ hT
  unfold backlundSChar
  have hcomb :
      (T * Real.log (q : ℝ) +
        (∫ t in (-T)..T, (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + I * (t : ℂ))).re) +
        (∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re)) -
      ((∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + I * (T : ℂ))).im) +
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im)) +
      ((∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) - I * (T : ℂ))).im) +
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im)) =
      T * Real.log (q : ℝ) + 2 * dirichletGammaPhase χ T +
        ((∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re) -
         (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im) +
         (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im)) := by
    linarith
  rw [hcomb]
  ring

/-- **Unconditional Uniform `O(1)` Stirling Asymptotic for `dirichletGammaPhase χ T`**
(simultaneously covering BOTH even and odd characters with a single universal constant `C > 0`!):
for EVERY `q`, EVERY `χ : DirichletCharacter ℂ q`, and EVERY `T ≥ 1`,
`|dirichletGammaPhase χ T - (T / 2) * Real.log (T / (2 * π * e))| ≤ C`. -/
theorem dirichletGammaPhase_stirling_asymptotic_O1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (T : ℝ), 1 ≤ T →
      |dirichletGammaPhase χ T - (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤ C := by
  obtain ⟨C₀, hC₀_pos, hth0⟩ := Stage7VonMangoldtExplicit.riemannSiegelTheta_stirling_asymptotic_O1
  -- Compare odd phase `∫_0^T ((1/2) Re ψ(3/4 + i t/2) - (1/2) log π)` with `riemannSiegelTheta T`
  let diffInt : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ((Complex.digamma ((3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
      (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re)
  have hdiff_cont : Continuous diffInt := by
    have h1 : Continuous (fun t : ℝ => Complex.digamma ((3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))) :=
      Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos.continuousOn.comp_continuous
        (by fun_prop) fun t => by change (0 : ℝ) < ((3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ)).re; simp
    have h2 : Continuous (fun t : ℝ => Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))) :=
      Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos.continuousOn.comp_continuous
        (by fun_prop) fun t => by change (0 : ℝ) < ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ)).re; simp
    exact continuous_const.mul ((Complex.continuous_re.comp h1).sub (Complex.continuous_re.comp h2))
  set C₁ : ℝ := |∫ t in (0 : ℝ)..(1 : ℝ), diffInt t| + 4
  refine ⟨C₀ + C₁, by positivity, fun q χ T hT => ?_⟩
  rcases χ.even_or_odd with he | ho
  · have hEq : dirichletGammaPhase χ T = Stage7VonMangoldtExplicit.riemannSiegelTheta T := by
      unfold dirichletGammaPhase Stage7VonMangoldtExplicit.riemannSiegelTheta
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [logDeriv_apply, Stage8HadamardLFunction.logDeriv_gammaFactor_even he (by simp)]
      have hdiv : ((1 / 2 : ℂ) + I * (t : ℂ)) / 2 = (1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp; norm_num
      rw [hdiv]
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
        zero_mul, sub_zero]
      ring
    rw [hEq]
    exact (hth0 T hT).trans (by linarith [show 0 ≤ C₁ by positivity])
  · have hEq : dirichletGammaPhase χ T - Stage7VonMangoldtExplicit.riemannSiegelTheta T =
        ∫ t in (0 : ℝ)..T, diffInt t := by
      unfold dirichletGammaPhase Stage7VonMangoldtExplicit.riemannSiegelTheta
      have hcont_odd : Continuous (fun t : ℝ =>
          (logDeriv (DirichletCharacter.gammaFactor χ) ((1 / 2 : ℂ) + I * (t : ℂ))).re) :=
        Complex.continuous_re.comp
          ((differentiableOn_logDeriv_gammaFactor χ).continuousOn.comp_continuous (by fun_prop)
            fun t => by change 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re; simp)
      have hcont_even : Continuous (fun t : ℝ =>
          (1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
            (1 / 2 : ℝ) * Real.log Real.pi) := by
        have hdig : Continuous (fun t : ℝ => Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))) :=
          Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos.continuousOn.comp_continuous
            (by fun_prop) fun t => by change 0 < ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ)).re; simp
        exact (continuous_const.mul (Complex.continuous_re.comp hdig)).sub continuous_const
      rw [← intervalIntegral.integral_sub (hcont_odd.intervalIntegrable _ _)
        (hcont_even.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [logDeriv_apply, Stage8HadamardLFunction.logDeriv_gammaFactor_odd ho (by simp)]
      have hdiv : ((1 / 2 : ℂ) + I * (t : ℂ) + 1) / 2 = (3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · simp; norm_num
        · simp
      rw [hdiv]
      dsimp only [diffInt]
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
        zero_mul, sub_zero]
      ring
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hdiff_cont.intervalIntegrable (μ := volume) 0 1)
      (hdiff_cont.intervalIntegrable (μ := volume) 1 T)
    have htail : |∫ t in (1 : ℝ)..T, diffInt t| ≤ 4 := by
      have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T, |diffInt t| ≤ 4 / t ^ 2 := fun t ht => by
        have ht0 : 0 < t := zero_lt_one.trans_le ht.1
        have h34 := Stage7VonMangoldtExplicit.re_digamma_sub_log_le
          (σ := 3 / 4) (t := t / 2) (by norm_num) (by positivity)
        have h14 := Stage7VonMangoldtExplicit.re_digamma_sub_log_le
          (σ := 1 / 4) (t := t / 2) (by norm_num) (by positivity)
        have hcast34 : ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) := by push_cast; rfl
        have hcast14 : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by push_cast; rfl
        rw [hcast34] at h34
        rw [hcast14] at h14
        dsimp only [diffInt]
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have htri : |(Complex.digamma ((3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
            (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re| ≤
            |(Complex.digamma ((3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re - Real.log (t / 2)| +
            |(Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re - Real.log (t / 2)| := by
          have h := abs_sub_le (Complex.digamma ((3 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re
            (Real.log (t / 2)) (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re
          rw [abs_sub_comm (Real.log (t / 2))] at h
          exact h
        have hsum : ((3 / 4 : ℝ) ^ 2 / 2 + (3 / 4) / 2 + 3 / 8) / (t / 2) ^ 2 +
            ((1 / 4 : ℝ) ^ 2 / 2 + (1 / 4) / 2 + 3 / 8) / (t / 2) ^ 2 ≤ 8 / t ^ 2 := by
          have : ((3 / 4 : ℝ) ^ 2 / 2 + (3 / 4) / 2 + 3 / 8) / (t / 2) ^ 2 +
              ((1 / 4 : ℝ) ^ 2 / 2 + (1 / 4) / 2 + 3 / 8) / (t / 2) ^ 2 = (25 / 4 : ℝ) / t ^ 2 := by
            field_simp [ht0.ne']; ring
          rw [this]
          exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg t)
        have hhalf : (1 / 2 : ℝ) * (8 / t ^ 2) = 4 / t ^ 2 := by ring
        linarith
      have hmaj_cont : ContinuousOn (fun t : ℝ => (4 : ℝ) / t ^ 2) (Set.uIcc 1 T) := by
        rw [Set.uIcc_of_le hT]
        exact continuousOn_const.div (by fun_prop) fun t ht => (pow_pos (zero_lt_one.trans_le ht.1) 2).ne'
      have hint_maj : ∫ t in (1 : ℝ)..T, (4 : ℝ) / t ^ 2 = 4 - 4 / T := by
        have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun u : ℝ => -(4 / u)) (4 / t ^ 2) t := by
          intro t ht
          rw [Set.uIcc_of_le hT] at ht
          have ht0 : 0 < t := zero_lt_one.trans_le ht.1
          have h1 := ((hasDerivAt_inv ht0.ne').const_mul 4).neg
          refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp [div_eq_mul_inv])).congr_deriv ?_
          field_simp [ht0.ne']
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hmaj_cont.intervalIntegrable]
        ring
      calc |∫ t in (1 : ℝ)..T, diffInt t|
          = ‖∫ t in (1 : ℝ)..T, diffInt t‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in (1 : ℝ)..T, ‖diffInt t‖ := intervalIntegral.norm_integral_le_integral_norm hT
        _ ≤ ∫ t in (1 : ℝ)..T, (4 : ℝ) / t ^ 2 :=
            intervalIntegral.integral_mono_on hT (hdiff_cont.intervalIntegrable _ _).norm
              hmaj_cont.intervalIntegrable fun t ht => by rw [Real.norm_eq_abs]; exact hpt t ht
        _ = 4 - 4 / T := hint_maj
        _ ≤ 4 := by linarith [show 0 ≤ 4 / T by positivity]
    have hdiff_bd : |dirichletGammaPhase χ T - Stage7VonMangoldtExplicit.riemannSiegelTheta T| ≤ C₁ := by
      rw [hEq, ← hsplit]
      exact (abs_add_le _ _).trans (by dsimp only [C₁]; linarith)
    have htri := abs_sub_le (dirichletGammaPhase χ T)
      (Stage7VonMangoldtExplicit.riemannSiegelTheta T)
      ((T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1)))
    linarith [hth0 T hT]

/-- **Unconditional Backlund Zero-Count Formula Bound (`O(1) + |S(T, χ)|`)**:
there exists a universal constant `C > 0` such that for every `q [NeZero q]`, every primitive
`χ ≠ 1`, and every `T ≥ 1` with no zero on `[0, 1] × {±T}`,
`|lFunctionZeroCount hprim hχ T - (T / π) * Real.log (q * T / (2 * π * e))| ≤ C + |backlundSChar χ T|`. -/
theorem lFunctionZeroCount_backlund_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
        (T : ℝ), 1 ≤ T →
        (∀ σ ∈ Set.Icc (0 : ℝ) 1,
          DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ)) ≠ 0 ∧
          DirichletCharacter.LFunction χ ((σ : ℂ) - I * (T : ℂ)) ≠ 0) →
        |lFunctionZeroCount hprim hχ T -
            (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          C + |backlundSChar χ T| := by
  obtain ⟨C₀, hC₀_pos, hgam⟩ := dirichletGammaPhase_stirling_asymptotic_O1
  refine ⟨(2 / Real.pi) * C₀, by positivity, fun q _ χ hprim hχ T hT hnz => ?_⟩
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hT_pos : 0 < T := by linarith
  have hlog_split : Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
      Real.log (q : ℝ) + Real.log (T / (2 * Real.pi * Real.exp 1)) := by
    rw [mul_div_assoc, Real.log_mul hq_pos.ne' (by positivity)]
  rw [backlund_LFunction_exact_formula hprim hχ hT_pos hnz, hlog_split]
  have hrew : (T / Real.pi) * Real.log (q : ℝ) + (2 / Real.pi) * dirichletGammaPhase χ T +
        backlundSChar χ T -
      (T / Real.pi) * (Real.log (q : ℝ) + Real.log (T / (2 * Real.pi * Real.exp 1))) =
      (2 / Real.pi) * (dirichletGammaPhase χ T -
        (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))) + backlundSChar χ T := by
    ring
  rw [hrew]
  calc |(2 / Real.pi) * (dirichletGammaPhase χ T -
          (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))) + backlundSChar χ T|
      ≤ |(2 / Real.pi) * (dirichletGammaPhase χ T -
          (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1)))| + |backlundSChar χ T| :=
        abs_add_le _ _
    _ = (2 / Real.pi) * |dirichletGammaPhase χ T -
          (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))| + |backlundSChar χ T| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
    _ ≤ (2 / Real.pi) * C₀ + |backlundSChar χ T| := by
        gcongr
        exact hgam q χ T hT

/-- **Elementary Backlund Argument-Variation Lemma on an Interval with Finitely Many `Re(g) = 0` Zeros**:
if `g : ℝ → ℂ` is `C¹` and nonvanishing on `[a, b]` (`a ≤ b`), and every `x ∈ (a, b)` with
`(g x).re = 0` belongs to `S : Finset ℝ`, then
`|∫ x in a..b, (g' x / g x).im| ≤ ((S.card : ℝ) + 1) * (2 * Real.pi)`. -/
private lemma abs_integral_im_logDeriv_le_of_re_zeros {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg_d : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hg'_cont : ContinuousOn g' (Set.Icc a b))
    (hg_nz : ∀ x ∈ Set.Icc a b, g x ≠ 0)
    (S : Finset ℝ) (hS : ∀ x ∈ Set.Ioo a b, (g x).re = 0 → x ∈ S) :
    |∫ x in a..b, (g' x / g x).im| ≤ ((S.card : ℝ) + 1) * (2 * Real.pi) := by
  classical
  -- Strong induction on the number of zeros strictly inside `(a, b)`
  have hmain : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      (∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x) →
      ContinuousOn g' (Set.Icc a b) →
      (∀ x ∈ Set.Icc a b, g x ≠ 0) →
      ∀ S : Finset ℝ, S.card ≤ n → (∀ x ∈ Set.Ioo a b, (g x).re = 0 → x ∈ S) →
      |∫ x in a..b, (g' x / g x).im| ≤ ((S.card : ℝ) + 1) * (2 * Real.pi) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b hab hgd hg'c hgnz S hSn hS
      have hg_cont : ContinuousOn g (Set.Icc a b) := fun x hx =>
        (hgd x hx).continuousAt.continuousWithinAt
      have hld_cont : ContinuousOn (fun x => (g' x / g x).im) (Set.Icc a b) :=
        Complex.continuous_im.comp_continuousOn (hg'c.div hg_cont hgnz)
      set S_in : Finset ℝ := S.filter fun x => a < x ∧ x < b
      have hSin_le : S_in.card ≤ S.card := Finset.card_filter_le _ _
      by_cases hemp : S_in = ∅
      · -- Base case: `(g x).re ≠ 0` throughout `(a, b)`
        have hstep : |∫ x in a..b, (g' x / g x).im| ≤ 2 * Real.pi := by
          rcases eq_or_lt_of_le hab with rfl | hlt
          · simp; positivity
          · have hre_nz : ∀ x ∈ Set.Ioo a b, (g x).re ≠ 0 := fun x hx h0 => by
              have hmem : x ∈ S_in := Finset.mem_filter.mpr ⟨hS x hx h0, hx⟩
              rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
            -- By IVT, `(g ·).re` has constant strict sign on `(a, b)`
            have hsign : (∀ x ∈ Set.Ioo a b, 0 < (g x).re) ∨ (∀ x ∈ Set.Ioo a b, (g x).re < 0) := by
              set mid : ℝ := (a + b) / 2
              have hmid : mid ∈ Set.Ioo a b := ⟨by dsimp only [mid]; linarith, by dsimp only [mid]; linarith⟩
              have hre_cont : ContinuousOn (fun x => (g x).re) (Set.Ioo a b) :=
                (Complex.continuous_re.comp_continuousOn hg_cont).mono Set.Ioo_subset_Icc_self
              rcases lt_or_gt_of_ne (hre_nz mid hmid) with hneg | hpos
              · right
                intro x hx
                by_contra hge
                have hgt : 0 < (g x).re := lt_of_le_of_ne (not_lt.mp hge) (hre_nz x hx).symm
                have h0mem : (0 : ℝ) ∈ Set.Icc (g mid).re (g x).re := ⟨hneg.le, hgt.le⟩
                have hconn := isPreconnected_Ioo.intermediate_value hmid hx hre_cont
                obtain ⟨z, hz_mem, hz0⟩ := hconn h0mem
                exact hre_nz z hz_mem hz0
              · left
                intro x hx
                by_contra hle
                have hlt' : (g x).re < 0 := lt_of_le_of_ne (not_lt.mp hle) (hre_nz x hx)
                have h0mem : (0 : ℝ) ∈ Set.Icc (g x).re (g mid).re := ⟨hlt'.le, hpos.le⟩
                have hconn := isPreconnected_Ioo.intermediate_value hx hmid hre_cont
                obtain ⟨z, hz_mem, hz0⟩ := hconn h0mem
                exact hre_nz z hz_mem hz0
            -- Auxiliary proof when `0 < (h x).re` on `(a, b)` for `h = g` or `h = -g`
            have hpos_case : ∀ (h h' : ℝ → ℂ),
                (∀ x ∈ Set.Icc a b, HasDerivAt h (h' x) x) →
                (∀ x ∈ Set.Ioo a b, 0 < (h x).re) →
                (∀ x ∈ Set.Ioo a b, (h' x / h x).im = (g' x / g x).im) →
                |∫ x in a..b, (g' x / g x).im| ≤ 2 * Real.pi := by
              intro h h' hhd hhpos hheq
              -- Approximate `[a, b]` from inside by `[a + ε_k, b - ε_k]`
              let ε : ℕ → ℝ := fun k => (b - a) / (3 * ((k : ℝ) + 1))
              have hε_pos : ∀ k : ℕ, 0 < ε k := fun k => by dsimp only [ε]; positivity
              have hε_lt : ∀ k : ℕ, a + ε k < b - ε k := fun k => by
                dsimp only [ε]
                have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
                have h3 : 2 < 3 * ((k : ℝ) + 1) := by linarith
                have hdiv : 2 * ((b - a) / (3 * ((k : ℝ) + 1))) < b - a := by
                  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
                  nlinarith
                linarith
              have hbound_k : ∀ k : ℕ,
                  |∫ x in (a + ε k)..(b - ε k), (g' x / g x).im| ≤ 2 * Real.pi := by
                intro k
                have hsub : Set.Icc (a + ε k) (b - ε k) ⊆ Set.Ioo a b := fun x hx =>
                  ⟨by linarith [hx.1, hε_pos k], by linarith [hx.2, hε_pos k]⟩
                have hderiv_log : ∀ x ∈ Set.uIcc (a + ε k) (b - ε k),
                    HasDerivAt (fun t : ℝ => (Complex.log (h t)).im) (g' x / g x).im x := by
                  intro x hx
                  rw [Set.uIcc_of_le (hε_lt k).le] at hx
                  have hx_oo : x ∈ Set.Ioo a b := hsub hx
                  have hslit : h x ∈ Complex.slitPlane := Or.inl (hhpos x hx_oo)
                  have hclog : HasDerivAt (fun t : ℝ => Complex.log (h t)) (h' x / h x) x := by
                    have hc := HasDerivAt.scomp x (Complex.hasDerivAt_log hslit)
                      (hhd x (Set.Ioo_subset_Icc_self hx_oo))
                    refine hc.congr_deriv ?_
                    simp [smul_eq_mul, div_eq_mul_inv]
                  have him_d : HasDerivAt (fun t : ℝ => (Complex.log (h t)).im) (h' x / h x).im x :=
                    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hclog
                  rwa [hheq x hx_oo] at him_d
                have hint_k : IntervalIntegrable (fun x => (g' x / g x).im) volume (a + ε k) (b - ε k) :=
                  (hld_cont.mono (by
                    rw [Set.uIcc_of_le (hε_lt k).le]
                    exact hsub.trans Set.Ioo_subset_Icc_self)).intervalIntegrable
                rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_log hint_k,
                  Complex.log_im, Complex.log_im]
                calc |Complex.arg (h (b - ε k)) - Complex.arg (h (a + ε k))|
                    ≤ |Complex.arg (h (b - ε k))| + |Complex.arg (h (a + ε k))| := abs_sub _ _
                  _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
                  _ = 2 * Real.pi := by ring
              -- Pass to the limit `k → ∞` using continuity of `t ↦ ∫_a^t (g'/g).im`
              have hε_tend : Tendsto ε atTop (𝓝 0) := by
                have h1 : Tendsto (fun k : ℕ => 3 * ((k : ℝ) + 1)) atTop atTop :=
                  Tendsto.const_mul_atTop (by norm_num)
                    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
                exact tendsto_const_nhds.div_atTop h1
              let F : ℝ → ℝ := fun t => ∫ x in a..t, (g' x / g x).im
              have hF_cont : ContinuousOn F (Set.Icc a b) := by
                intro t ht
                have hint_ab : IntervalIntegrable (fun x => (g' x / g x).im) volume a b :=
                  (hld_cont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
                have hmeas : ∀ s ∈ Set.Icc a b, IntervalIntegrable (fun x => (g' x / g x).im) volume a s :=
                  fun s hs => hint_ab.mono_set (by
                    rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le hab]
                    exact fun y hy => ⟨hy.1, hy.2.trans hs.2⟩)
                -- Uniform bound `M` on `|(g'/g).im|` over `[a, b]`
                obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hld_cont
                rw [Metric.continuousWithinAt_iff]
                intro δ hδ
                refine ⟨δ / (max M 1), by positivity, fun s hs hdist => ?_⟩
                rw [Real.dist_eq] at hdist ⊢
                have hdiff_F : F s - F t = ∫ x in t..s, (g' x / g x).im := by
                  dsimp only [F]
                  have hts := intervalIntegral.integral_add_adjacent_intervals (hmeas t ht)
                    (hint_ab.mono_set (by
                      rw [Set.uIcc_of_le hab]
                      intro y hy
                      rcases le_total t s with hle | hle
                      · rw [Set.uIcc_of_le hle] at hy; exact ⟨ht.1.trans hy.1, hy.2.trans hs.2⟩
                      · rw [Set.uIcc_of_ge hle] at hy; exact ⟨hs.1.trans hy.1, hy.2.trans ht.2⟩))
                  linarith
                rw [hdiff_F]
                have hbd_ts : |∫ x in t..s, (g' x / g x).im| ≤ max M 1 * |s - t| := by
                  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s)
                    (f := fun x => (g' x / g x).im) (C := max M 1) fun x hx => by
                      have hx_mem : x ∈ Set.Icc a b := by
                        rcases le_total t s with hle | hle
                        · rw [Set.uIoc_of_le hle] at hx; exact ⟨ht.1.trans hx.1.le, hx.2.trans hs.2⟩
                        · rw [Set.uIoc_of_ge hle] at hx; exact ⟨hs.1.trans hx.1.le, hx.2.trans ht.2⟩
                      exact (hM x hx_mem).trans (le_max_left M 1)
                  rw [Real.norm_eq_abs] at h1
                  linarith
                have hposM : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
                calc |∫ x in t..s, (g' x / g x).im|
                    ≤ max M 1 * |s - t| := hbd_ts
                  _ < max M 1 * (δ / max M 1) := mul_lt_mul_of_pos_left hdist hposM
                  _ = δ := mul_div_cancel₀ δ hposM.ne'
              have hlim_a : Tendsto (fun k => F (a + ε k)) atTop (𝓝 (F a)) := by
                have harg : Tendsto (fun k => a + ε k) atTop (𝓝[Set.Icc a b] a) := by
                  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
                    (by simpa using hε_tend.const_add a) (Eventually.of_forall fun k => ?_)
                  exact ⟨by linarith [hε_pos k], by linarith [hε_lt k, hε_pos k]⟩
                exact (hF_cont a ⟨le_rfl, hab⟩).tendsto.comp harg
              have hlim_b : Tendsto (fun k => F (b - ε k)) atTop (𝓝 (F b)) := by
                have harg : Tendsto (fun k => b - ε k) atTop (𝓝[Set.Icc a b] b) := by
                  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
                    (by simpa using tendsto_const_nhds.sub hε_tend) (Eventually.of_forall fun k => ?_)
                  exact ⟨by linarith [hε_lt k, hε_pos k], by linarith [hε_pos k]⟩
                exact (hF_cont b ⟨hab, le_rfl⟩).tendsto.comp harg
              have hlim : Tendsto (fun k => |∫ x in (a + ε k)..(b - ε k), (g' x / g x).im|)
                  atTop (𝓝 |∫ x in a..b, (g' x / g x).im|) := by
                have hsub := (hlim_b.sub hlim_a).abs
                have hFa : F a = 0 := intervalIntegral.integral_same
                rw [hFa, sub_zero] at hsub
                refine hsub.congr fun k => ?_
                congr 1
                dsimp only [F]
                have hint_ab : IntervalIntegrable (fun x => (g' x / g x).im) volume a b :=
                  (hld_cont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
                have hint1 : IntervalIntegrable (fun x => (g' x / g x).im) volume a (a + ε k) :=
                  hint_ab.mono_set (by
                    rw [Set.uIcc_of_le (by linarith [hε_pos k]), Set.uIcc_of_le hab]
                    exact fun y hy => ⟨hy.1, by linarith [hy.2, hε_lt k, hε_pos k]⟩)
                have hint2 : IntervalIntegrable (fun x => (g' x / g x).im) volume (a + ε k) (b - ε k) :=
                  hint_ab.mono_set (by
                    rw [Set.uIcc_of_le (hε_lt k).le, Set.uIcc_of_le hab]
                    exact fun y hy => ⟨by linarith [hy.1, hε_pos k], by linarith [hy.2, hε_pos k]⟩)
                linarith [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
              exact le_of_tendsto hlim (Eventually.of_forall hbound_k)
            rcases hsign with hpos | hneg
            · exact hpos_case g g' hgd hpos (fun _ _ => rfl)
            · refine hpos_case (fun x => -g x) (fun x => -g' x)
                (fun x hx => (hgd x hx).neg) (fun x hx => by simp; linarith [hneg x hx]) ?_
              intro x _
              rw [neg_div_neg_eq]
        have hnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        nlinarith [Real.pi_pos]
      · -- Inductive step: split at a zero `c ∈ S_in ⊆ (a, b)`
        obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hc_mem := Finset.mem_filter.mp hc
        have hac : a < c := hc_mem.2.1
        have hcb : c < b := hc_mem.2.2
        set S_L : Finset ℝ := S_in.filter (· < c)
        set S_R : Finset ℝ := S_in.filter (c < ·)
        have hdisj : Disjoint S_L S_R := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
        have hunion : S_L ∪ S_R ⊆ S_in.erase c := by
          intro x hx
          rw [Finset.mem_erase]
          rcases Finset.mem_union.mp hx with hL | hR
          · exact ⟨(Finset.mem_filter.mp hL).2.ne, (Finset.mem_filter.mp hL).1⟩
          · exact ⟨(Finset.mem_filter.mp hR).2.ne', (Finset.mem_filter.mp hR).1⟩
        have hcard_sum : S_L.card + S_R.card + 1 ≤ S_in.card := by
          have h1 : (S_L ∪ S_R).card ≤ (S_in.erase c).card := Finset.card_le_card hunion
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hc] at h1
          have hpos : 0 < S_in.card := Finset.card_pos.mpr ⟨c, hc⟩
          omega
        have hL_lt : S_L.card < n := by omega
        have hR_lt : S_R.card < n := by omega
        have hsub_L : Set.Icc a c ⊆ Set.Icc a b := fun x hx => ⟨hx.1, hx.2.trans hcb.le⟩
        have hsub_R : Set.Icc c b ⊆ Set.Icc a b := fun x hx => ⟨hac.le.trans hx.1, hx.2⟩
        have hbd_L := ih S_L.card hL_lt a c hac.le (fun x hx => hgd x (hsub_L hx))
          (hg'c.mono hsub_L) (fun x hx => hgnz x (hsub_L hx)) S_L le_rfl fun x hx h0 =>
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hS x ⟨hx.1, hx.2.trans hcb⟩ h0,
              hx.1, hx.2.trans hcb⟩, hx.2⟩
        have hbd_R := ih S_R.card hR_lt c b hcb.le (fun x hx => hgd x (hsub_R hx))
          (hg'c.mono hsub_R) (fun x hx => hgnz x (hsub_R hx)) S_R le_rfl fun x hx h0 =>
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hS x ⟨hac.trans hx.1, hx.2⟩ h0,
              hac.trans hx.1, hx.2⟩, hx.1⟩
        have hint_L : IntervalIntegrable (fun x => (g' x / g x).im) volume a c :=
          (hld_cont.mono (by rw [Set.uIcc_of_le hac.le]; exact hsub_L)).intervalIntegrable
        have hint_R : IntervalIntegrable (fun x => (g' x / g x).im) volume c b :=
          (hld_cont.mono (by rw [Set.uIcc_of_le hcb.le]; exact hsub_R)).intervalIntegrable
        rw [← intervalIntegral.integral_add_adjacent_intervals hint_L hint_R]
        have hcardR : (S_L.card : ℝ) + (S_R.card : ℝ) + 1 ≤ (S.card : ℝ) := by
          exact_mod_cast (hcard_sum.trans hSin_le)
        calc |(∫ x in a..c, (g' x / g x).im) + ∫ x in c..b, (g' x / g x).im|
            ≤ |∫ x in a..c, (g' x / g x).im| + |∫ x in c..b, (g' x / g x).im| := abs_add_le _ _
          _ ≤ ((S_L.card : ℝ) + 1) * (2 * Real.pi) + ((S_R.card : ℝ) + 1) * (2 * Real.pi) :=
              add_le_add hbd_L hbd_R
          _ = (((S_L.card : ℝ) + (S_R.card : ℝ) + 1) + 1) * (2 * Real.pi) := by ring
          _ ≤ ((S.card : ℝ) + 1) * (2 * Real.pi) := by gcongr
  exact hmain S.card a b hab hg_d hg'_cont hg_nz S le_rfl hS

/-- Lower bound `1 / 4 ≤ (LFunction χ s).re` on `Re(s) ≥ 2` (for every `q`, every `χ`). -/
private lemma quarter_le_re_LFunction_of_two_le_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 2 ≤ s.re) :
    (1 / 4 : ℝ) ≤ (DirichletCharacter.LFunction χ s).re := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  have hsum : LSeriesSummable (χ ·) s := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hhead : ∑ i ∈ Finset.range 2, LSeries.term (χ ·) s i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, LSeries.term_zero, zero_add,
      LSeries.term_of_ne_zero one_ne_zero]
    simp
  rw [hhead] at hsplit
  have htail_le : ‖∑' k : ℕ, LSeries.term (χ ·) s (k + 2)‖ ≤ 3 / 4 := by
    have hsumm0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
      simp [one_div, Real.summable_nat_pow_inv]
    have hsumm_real : Summable (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) :=
      hsumm0.comp_injective (fun a b h => by omega)
    have hterm : ∀ k : ℕ, ‖LSeries.term (χ ·) s (k + 2)‖ ≤ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      intro k
      have hk_pos : 0 < k + 2 := by omega
      have hk1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.one_le_cast.mpr hk_pos
      rw [LSeries.term_of_ne_zero hk_pos.ne', norm_div, Complex.norm_natCast_cpow_of_pos hk_pos]
      have hpow : ((k + 2 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) ^ s.re := by
        simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hk1 hs
      calc ‖χ ((k + 2 : ℕ) : ZMod q)‖ / ((k + 2 : ℕ) : ℝ) ^ s.re
          ≤ 1 / ((k + 2 : ℕ) : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 1 / ((k + 2 : ℕ) : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hpow
    have hsumm_norm : Summable (fun k : ℕ => ‖LSeries.term (χ ·) s (k + 2)‖) :=
      hsumm_real.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    calc ‖∑' k : ℕ, LSeries.term (χ ·) s (k + 2)‖
        ≤ ∑' k : ℕ, ‖LSeries.term (χ ·) s (k + 2)‖ := norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := hsumm_norm.tsum_le_tsum hterm hsumm_real
      _ ≤ 3 / 4 := Stage6LFunctionOrder.tsum_inv_add_two_sq_le_three_quarters
  have hre_tail : -(3 / 4 : ℝ) ≤ (∑' k : ℕ, LSeries.term (χ ·) s (k + 2)).re := by
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans htail_le)).1
    exact h1
  unfold LSeries
  rw [← hsplit, Complex.add_re, Complex.one_re]
  linarith

/-- **UNCONDITIONAL BACKLUND–JENSEN BOUND ON `|S(T, χ)|`**:
there exists a universal constant `C_S > 0` such that for EVERY `q [NeZero q]`, EVERY primitive
`χ ≠ 1` mod `q`, and EVERY `T ≥ 1` with no zero on `[0, 1] × {±T}`,
`|backlundSChar χ T| ≤ C_S * Real.log (q * (T + 2))`! -/
theorem abs_backlundSChar_le_log :
    ∃ C_S : ℝ, 0 < C_S ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        ∀ (T : ℝ), 1 ≤ T →
        (∀ σ ∈ Set.Icc (0 : ℝ) 1,
          DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ)) ≠ 0 ∧
          DirichletCharacter.LFunction χ ((σ : ℂ) - I * (T : ℂ)) ≠ 0) →
        |backlundSChar χ T| ≤ C_S * Real.log ((q : ℝ) * (T + 2)) := by
  classical
  obtain ⟨K, hK_pos, hpoly⟩ := Stage6LFunctionOrder.norm_LFunction_strip_poly_bound
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C_J : ℝ := (max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) / Real.log 2
  have hCJ_pos : 0 < C_J := by
    dsimp only [C_J]
    exact div_pos (by linarith [le_max_right (Real.log (4 * K * (4 : ℝ) ^ 7)) 0]) hlog2_pos
  set C_S : ℝ := 2 + 4 * (C_J + 1)
  refine ⟨C_S, by positivity, fun q _ χ hprim hχ T hT hnz => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hT_pos : 0 < T := by linarith
  have hlog_ge1 : 1 ≤ Real.log ((q : ℝ) * (T + 2)) := by
    have h4 : (1 : ℝ) < Real.log 4 := by
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    exact h4.le.trans (Real.log_le_log (by norm_num) (by nlinarith))
  -- Part 1: Vertical integral `|∫_{-T}^T Re(L'/L(2 + i t)) dt| ≤ 2 * π`
  have hvert_bd : |∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re| ≤
      2 * Real.pi := by
    have hderiv : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt (fun y : ℝ => (Complex.log (DirichletCharacter.LFunction χ ((2 : ℂ) + I * (y : ℂ)))).im)
          (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re t := by
      intro t _
      have hslit : DirichletCharacter.LFunction χ ((2 : ℂ) + I * (t : ℂ)) ∈ Complex.slitPlane :=
        Or.inl (lt_of_lt_of_le (by norm_num) (quarter_le_re_LFunction_of_two_le_re χ (by simp)))
      have hmap : HasDerivAt (fun y : ℝ => (2 : ℂ) + I * (y : ℂ)) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.const_mul I).const_add (2 : ℂ)
      have hcomp : HasDerivAt (fun y : ℝ => DirichletCharacter.LFunction χ ((2 : ℂ) + I * (y : ℂ)))
          (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ)) * I) t := by
        have hc := HasDerivAt.scomp t (DirichletCharacter.differentiable_LFunction hχ _).hasDerivAt hmap
        refine hc.congr_deriv ?_
        simp [smul_eq_mul, mul_comm]
      have hlog : HasDerivAt
          (fun y : ℝ => Complex.log (DirichletCharacter.LFunction χ ((2 : ℂ) + I * (y : ℂ))))
          (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ)) * I /
            DirichletCharacter.LFunction χ ((2 : ℂ) + I * (t : ℂ))) t := by
        have hc := HasDerivAt.scomp t (Complex.hasDerivAt_log hslit) hcomp
        refine hc.congr_deriv ?_
        simp [smul_eq_mul, div_eq_mul_inv]
      have him_d := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
      refine him_d.congr_deriv ?_
      change (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ)) * I /
          DirichletCharacter.LFunction χ ((2 : ℂ) + I * (t : ℂ))).im = _
      rw [mul_div_right_comm, logDeriv_apply, Complex.mul_im]
      simp
    have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
    have hcont : ContinuousOn
        (fun t : ℝ => (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re)
        (Set.uIcc (-T) T) :=
      Complex.continuous_re.comp_continuousOn fun t _ => by
        have hnz2 : DirichletCharacter.LFunction χ ((2 : ℂ) + I * (t : ℂ)) ≠ 0 :=
          DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp)
        have hld : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) ((2 : ℂ) + I * (t : ℂ)) :=
          ((hL_an _ (Set.mem_univ _)).deriv.continuousAt).div
            (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt hnz2
        exact (ContinuousAt.comp (f := fun y : ℝ => (2 : ℂ) + I * (y : ℂ)) hld (by fun_prop)).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
      Complex.log_im, Complex.log_im]
    calc |Complex.arg _ - Complex.arg _|
        ≤ |Complex.arg _| + |Complex.arg _| := abs_sub _ _
      _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
      _ = 2 * Real.pi := by ring
  -- Part 2: Horizontal integral bound via Jensen on `G_y(z) = (1/2) (L(χ, z + i y) + L(χ⁻¹, z - i y))`
  have hhoriz_bd : ∀ y : ℝ, |y| = T →
      (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, DirichletCharacter.LFunction χ ((σ : ℂ) + I * (y : ℂ)) ≠ 0) →
      |∫ σ in (1 / 2 : ℝ)..2,
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (y : ℂ))).im| ≤
        (C_J * Real.log ((q : ℝ) * (T + 2)) + 1) * (2 * Real.pi) := by
    intro y hy hnz_y
    have hχinv : χ⁻¹ ≠ 1 := Stage6LFunctionOrder.inv_ne_one_of_ne_one hχ
    have hprim_inv : χ⁻¹.IsPrimitive := Stage6LFunctionOrder.isPrimitive_inv hprim
    let G : ℂ → ℂ := fun z =>
      (1 / 2 : ℂ) * (DirichletCharacter.LFunction χ (z + I * (y : ℂ)) +
        DirichletCharacter.LFunction χ⁻¹ (z - I * (y : ℂ)))
    have hG_diff : Differentiable ℂ G := by
      have h1 : Differentiable ℂ (fun z : ℂ => DirichletCharacter.LFunction χ (z + I * (y : ℂ))) :=
        (DirichletCharacter.differentiable_LFunction hχ).comp (differentiable_id.add_const _)
      have h2 : Differentiable ℂ (fun z : ℂ => DirichletCharacter.LFunction χ⁻¹ (z - I * (y : ℂ))) :=
        (DirichletCharacter.differentiable_LFunction hχinv).comp (differentiable_id.sub_const _)
      exact (differentiable_const _).mul (h1.add h2)
    have hG_real : ∀ σ : ℝ, G (σ : ℂ) = ((DirichletCharacter.LFunction χ ((σ : ℂ) + I * (y : ℂ))).re : ℂ) := by
      intro σ
      have hconj_arg : (σ : ℂ) - I * (y : ℂ) = starRingEnd ℂ ((σ : ℂ) + I * (y : ℂ)) :=
        Complex.ext (by simp) (by simp)
      dsimp only [G]
      rw [hconj_arg, RHDirect.LFunction_conj χ (.inl hχ)]
      apply Complex.ext
      · simp; ring
      · simp
    -- Apply Jensen to `f(w) = G(2 + w)` with `r = 2, R = 4`
    let f : ℂ → ℂ := fun w => G ((2 : ℂ) + w)
    have hf_diff : Differentiable ℂ f := hG_diff.comp (differentiable_id.const_add (2 : ℂ))
    have hf0_ge : (1 / 4 : ℝ) ≤ ‖f 0‖ := by
      dsimp only [f]
      rw [add_zero]
      have h2_eq : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
      rw [h2_eq, hG_real 2, Complex.norm_real, Real.norm_eq_abs]
      have hre := quarter_le_re_LFunction_of_two_le_re χ (s := ((2 : ℝ) : ℂ) + I * (y : ℂ)) (by simp)
      exact hre.trans (le_abs_self _)
    have hf0_ne : f 0 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hf0_ge; norm_num at hf0_ge
    set M : ℝ := K * (4 : ℝ) ^ 7 * ((q : ℝ) * (T + 2)) ^ 7
    have hM_bd : ∀ w ∈ Metric.sphere (0 : ℂ) 4, ‖f w‖ ≤ M := by
      intro w hw
      have hw_norm : ‖w‖ = 4 := mem_sphere_zero_iff_norm.mp hw
      have hw_re := abs_le.mp ((Complex.abs_re_le_norm w).trans hw_norm.le)
      have hw_im : |w.im| ≤ 4 := (Complex.abs_im_le_norm w).trans hw_norm.le
      have hre1 : -3 ≤ ((2 : ℂ) + w + I * (y : ℂ)).re := by simp; linarith
      have hre2 : ((2 : ℂ) + w + I * (y : ℂ)).re ≤ 7 := by simp; linarith
      have hre1' : -3 ≤ ((2 : ℂ) + w - I * (y : ℂ)).re := by simp; linarith
      have hre2' : ((2 : ℂ) + w - I * (y : ℂ)).re ≤ 7 := by simp; linarith
      have him1 : |((2 : ℂ) + w + I * (y : ℂ)).im| + 2 ≤ 4 * (T + 2) := by
        have h : ((2 : ℂ) + w + I * (y : ℂ)).im = w.im + y := by simp
        rw [h]; have := abs_add_le w.im y; linarith
      have him2 : |((2 : ℂ) + w - I * (y : ℂ)).im| + 2 ≤ 4 * (T + 2) := by
        have h : ((2 : ℂ) + w - I * (y : ℂ)).im = w.im - y := by simp
        rw [h]; have := abs_sub w.im y; linarith
      have hL1 : ‖DirichletCharacter.LFunction χ ((2 : ℂ) + w + I * (y : ℂ))‖ ≤ M := by
        calc ‖DirichletCharacter.LFunction χ ((2 : ℂ) + w + I * (y : ℂ))‖
            ≤ K * ((q : ℝ) * (|((2 : ℂ) + w + I * (y : ℂ)).im| + 2)) ^ 7 :=
              hpoly q χ hprim hχ _ hre1 hre2
          _ ≤ K * ((q : ℝ) * (4 * (T + 2))) ^ 7 :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left him1 hqR_pos.le) 7)
                hK_pos.le
          _ = M := by dsimp only [M]; rw [show (q : ℝ) * (4 * (T + 2)) = 4 * ((q : ℝ) * (T + 2)) by ring, mul_pow]; ring
      have hL2 : ‖DirichletCharacter.LFunction χ⁻¹ ((2 : ℂ) + w - I * (y : ℂ))‖ ≤ M := by
        calc ‖DirichletCharacter.LFunction χ⁻¹ ((2 : ℂ) + w - I * (y : ℂ))‖
            ≤ K * ((q : ℝ) * (|((2 : ℂ) + w - I * (y : ℂ)).im| + 2)) ^ 7 :=
              hpoly q χ⁻¹ hprim_inv hχinv _ hre1' hre2'
          _ ≤ K * ((q : ℝ) * (4 * (T + 2))) ^ 7 :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left him2 hqR_pos.le) 7)
                hK_pos.le
          _ = M := by dsimp only [M]; rw [show (q : ℝ) * (4 * (T + 2)) = 4 * ((q : ℝ) * (T + 2)) by ring, mul_pow]; ring
      dsimp only [f, G]
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
      calc (1 / 2 : ℝ) * ‖DirichletCharacter.LFunction χ ((2 : ℂ) + w + I * (y : ℂ)) +
              DirichletCharacter.LFunction χ⁻¹ ((2 : ℂ) + w - I * (y : ℂ))‖
          ≤ (1 / 2 : ℝ) * (M + M) :=
            mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hL1 hL2)) (by norm_num)
        _ = M := by ring
    -- Bound on any finite set of real zeros of `(L(σ + i y)).re` in `(1/2, 2)`
    have hcard_le : ∀ S : Finset ℝ,
        (∀ σ ∈ S, σ ∈ Set.Ioo (1 / 2 : ℝ) 2 ∧
          (DirichletCharacter.LFunction χ ((σ : ℂ) + I * (y : ℂ))).re = 0) →
        (S.card : ℝ) ≤ C_J * Real.log ((q : ℝ) * (T + 2)) := by
      intro S hS
      set Z' : Finset ℂ := S.image fun σ => ((σ - 2 : ℝ) : ℂ)
      have hcard_eq : Z'.card = S.card :=
        Finset.card_image_of_injective S fun a b h => by
          have := Complex.ofReal_injective h; linarith
      have hZ'_ball : ∀ w ∈ Z', w ∈ Metric.closedBall (0 : ℂ) 2 := by
        intro w hw
        rcases Finset.mem_image.mp hw with ⟨σ, hσ, rfl⟩
        obtain ⟨⟨h1, h2⟩, _⟩ := hS σ hσ
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have hZ'_zero : ∀ w ∈ Z', f w = 0 := by
        intro w hw
        rcases Finset.mem_image.mp hw with ⟨σ, hσ, rfl⟩
        dsimp only [f]
        have harg : (2 : ℂ) + ((σ - 2 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
        rw [harg, hG_real σ, (hS σ hσ).2, Complex.ofReal_zero]
      have hj := Stage5JensenHadamard.jensen_zero_count_le
        (r := 2) (R := 4) (M := M) (by norm_num) (by norm_num)
        hf_diff.diffContOnCl hf0_ne hM_bd Z' hZ'_ball hZ'_zero
      rw [hcard_eq, show (4 : ℝ) / 2 = 2 by norm_num] at hj
      have hratio : M / ‖f 0‖ ≤ (4 * K * (4 : ℝ) ^ 7) * ((q : ℝ) * (T + 2)) ^ 7 := by
        have h1 : M / ‖f 0‖ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hf0_ge
        refine h1.trans_eq ?_; dsimp only [M]; ring
      have hlog_le : Real.log (M / ‖f 0‖) ≤
          (max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) * Real.log ((q : ℝ) * (T + 2)) := by
        calc Real.log (M / ‖f 0‖)
            ≤ Real.log ((4 * K * (4 : ℝ) ^ 7) * ((q : ℝ) * (T + 2)) ^ 7) :=
              Real.log_le_log (div_pos (by positivity) (norm_pos_iff.mpr hf0_ne)) hratio
          _ = Real.log (4 * K * (4 : ℝ) ^ 7) + 7 * Real.log ((q : ℝ) * (T + 2)) := by
              rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
          _ ≤ max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 * Real.log ((q : ℝ) * (T + 2)) +
                7 * Real.log ((q : ℝ) * (T + 2)) := by
              have h1 := le_max_left (Real.log (4 * K * (4 : ℝ) ^ 7)) 0
              have h2 := le_max_right (Real.log (4 * K * (4 : ℝ) ^ 7)) 0
              nlinarith
          _ = (max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) * Real.log ((q : ℝ) * (T + 2)) := by ring
      calc (S.card : ℝ)
          ≤ Real.log (M / ‖f 0‖) / Real.log 2 := hj
        _ ≤ ((max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) *
              Real.log ((q : ℝ) * (T + 2))) / Real.log 2 :=
            div_le_div_of_nonneg_right hlog_le hlog2_pos.le
        _ = C_J * Real.log ((q : ℝ) * (T + 2)) := by dsimp only [C_J]; ring
    -- Finiteness of `{σ ∈ (1/2, 2) | Re L(σ + i y) = 0}`
    have hfin : {σ : ℝ | σ ∈ Set.Ioo (1 / 2 : ℝ) 2 ∧
        (DirichletCharacter.LFunction χ ((σ : ℂ) + I * (y : ℂ))).re = 0}.Finite := by
      by_contra hinf
      obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf
        (Nat.floor (C_J * Real.log ((q : ℝ) * (T + 2))) + 1)
      have hle := hcard_le S fun σ hσ => hSsub hσ
      have hgt : C_J * Real.log ((q : ℝ) * (T + 2)) < (S.card : ℝ) := by
        rw [hScard]; push_cast; exact Nat.lt_floor_add_one _
      linarith
    set S : Finset ℝ := hfin.toFinset
    have hS_card : (S.card : ℝ) ≤ C_J * Real.log ((q : ℝ) * (T + 2)) :=
      hcard_le S fun σ hσ => hfin.mem_toFinset.mp hσ
    have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
    have hgd : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
        HasDerivAt (fun x : ℝ => DirichletCharacter.LFunction χ ((x : ℂ) + I * (y : ℂ)))
          (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (y : ℂ))) σ := by
      intro σ _
      have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) + I * (y : ℂ)) (1 : ℂ) σ := by
        simpa using (hasDerivAt_id σ).ofReal_comp.add_const (I * (y : ℂ))
      have hc := HasDerivAt.scomp σ
        (DirichletCharacter.differentiable_LFunction hχ _).hasDerivAt hlin
      refine hc.congr_deriv ?_
      simp [smul_eq_mul]
    have hg'_cont : ContinuousOn
        (fun σ : ℝ => deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (y : ℂ)))
        (Set.Icc (1 / 2 : ℝ) 2) := fun σ _ =>
      ((hL_an _ (Set.mem_univ _)).deriv.continuousAt.comp (by fun_prop)).continuousWithinAt
    have hstep := abs_integral_im_logDeriv_le_of_re_zeros (by norm_num : (1 / 2 : ℝ) ≤ 2)
      hgd hg'_cont hnz_y S fun σ hσ h0 => hfin.mem_toFinset.mpr ⟨hσ, h0⟩
    have hcongr : ∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (y : ℂ))).im =
        ∫ σ in (1 / 2 : ℝ)..2,
        (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (y : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + I * (y : ℂ))).im :=
      intervalIntegral.integral_congr fun _ _ => by rw [logDeriv_apply]
    rw [hcongr]
    exact hstep.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  -- Combine vertical + top + bottom horizontal bounds
  have hnz_top : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ)) ≠ 0 := fun σ hσ => by
    rcases le_or_gt 1 σ with h1 | h1
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [h1])
    · exact (hnz σ ⟨by linarith [hσ.1], h1.le⟩).1
  have hnz_bot : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + I * ((-T : ℝ) : ℂ)) ≠ 0 := fun σ hσ => by
    have harg : (σ : ℂ) + I * ((-T : ℝ) : ℂ) = (σ : ℂ) - I * (T : ℂ) := by push_cast; ring
    rw [harg]
    rcases le_or_gt 1 σ with h1 | h1
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [h1])
    · exact (hnz σ ⟨by linarith [hσ.1], h1.le⟩).2
  have htop := hhoriz_bd T (abs_of_pos hT_pos) hnz_top
  have hbot_raw := hhoriz_bd (-T) (by rw [abs_neg, abs_of_pos hT_pos]) hnz_bot
  have hbot_eq : ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * ((-T : ℝ) : ℂ))).im =
      ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im :=
    intervalIntegral.integral_congr fun σ _ => by congr 2; push_cast; ring
  rw [hbot_eq] at hbot_raw
  unfold backlundSChar
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi)]
  have htri :
      |(∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re) -
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im) +
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im)| ≤
      2 * Real.pi + 2 * ((C_J * Real.log ((q : ℝ) * (T + 2)) + 1) * (2 * Real.pi)) := by
    have h1 := abs_add_le
      ((∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re) -
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im))
      (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im)
    have h2 := abs_sub
      (∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re)
      (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im)
    linarith
  calc (1 / Real.pi) *
        |(∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + I * (t : ℂ))).re) -
         (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * (T : ℂ))).im) +
         (∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - I * (T : ℂ))).im)|
      ≤ (1 / Real.pi) * (2 * Real.pi + 2 * ((C_J * Real.log ((q : ℝ) * (T + 2)) + 1) * (2 * Real.pi))) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = 2 + 4 * (C_J * Real.log ((q : ℝ) * (T + 2)) + 1) := by field_simp [Real.pi_pos.ne']; ring
    _ ≤ C_S * Real.log ((q : ℝ) * (T + 2)) := by dsimp only [C_S]; nlinarith

/-- Helper: given any finite set `Z` of complex numbers and any `a < b`, there exists `t ∈ (a, b)`
such that `|ρ.im| ≠ t` for all `ρ ∈ Z`. -/
private lemma exists_zeroFree_height_in_Ioo {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) 1,
        DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) ≠ 0 ∧
        DirichletCharacter.LFunction χ ((σ : ℂ) - I * (t : ℂ)) ≠ 0 := by
  classical
  have hfin := Stage8HadamardLFunction.finite_completedLFunction_zeros_le_height hprim hχ
    (le_max_right b 2)
  set bad : Finset ℝ := hfin.toFinset.image fun ρ => |ρ.im|
  have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  have hne : (Set.Ioo a b \ (bad : Set ℝ)).Nonempty :=
    (hinf.sdiff (Finset.finite_toSet bad)).nonempty
  obtain ⟨t, ht_oo, ht_nbad⟩ := hne
  refine ⟨t, ht_oo.1, ht_oo.2, fun σ hσ => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · have hσ_pos : 0 < σ := by
      rcases eq_or_lt_of_le hσ.1 with rfl | hpos
      · exfalso
        simp only [Complex.ofReal_zero] at hz
        have hc : DirichletCharacter.completedLFunction χ ((0 : ℂ) + I * (t : ℂ)) = 0 := by
          have hne0 : ((0 : ℂ) + I * (t : ℂ)) ≠ 0 := fun h => by
            have := congrArg Complex.im h; simp at this; linarith [ht_oo.1]
          have hG := Stage6LFunctionOrder.completedLFunction_eq_LFunction_mul_gammaFactor χ (.inl hne0)
          have hGne : DirichletCharacter.gammaFactor χ ((0 : ℂ) + I * (t : ℂ)) ≠ 0 := by
            rcases χ.even_or_odd with he | ho
            · rw [he.gammaFactor_def]
              intro hg
              obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
              have him := congrArg Complex.im hn; simp at him; linarith [ht_oo.1]
            · rw [ho.gammaFactor_def]
              exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
          rw [hG hGne, hz, zero_mul]
        exact Stage6LFunctionOrder.completedLFunction_ne_zero_of_re_le_zero hprim hχ (by simp) hc
      · exact hpos
    have hcomp : DirichletCharacter.completedLFunction χ ((σ : ℂ) + I * (t : ℂ)) = 0 :=
      (Stage6LFunctionOrder.completedLFunction_eq_zero_iff_LFunction_of_re_pos χ
        (by simpa using hσ_pos)).mpr hz
    have hmem : ((σ : ℂ) + I * (t : ℂ)) ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr ⟨hcomp, by simp [abs_of_pos (ha.trans ht_oo.1), ht_oo.2.le.trans (le_max_left b 2)]⟩
    apply ht_nbad
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, hmem, by simp [abs_of_pos (ha.trans ht_oo.1)]⟩)
  · have hσ_pos : 0 < σ := by
      rcases eq_or_lt_of_le hσ.1 with rfl | hpos
      · exfalso
        simp only [Complex.ofReal_zero] at hz
        have hc : DirichletCharacter.completedLFunction χ ((0 : ℂ) - I * (t : ℂ)) = 0 := by
          have hne0 : ((0 : ℂ) - I * (t : ℂ)) ≠ 0 := fun h => by
            have := congrArg Complex.im h; simp at this; linarith [ht_oo.1]
          have hGne : DirichletCharacter.gammaFactor χ ((0 : ℂ) - I * (t : ℂ)) ≠ 0 := by
            rcases χ.even_or_odd with he | ho
            · rw [he.gammaFactor_def]
              intro hg
              obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
              have him := congrArg Complex.im hn; simp at him; linarith [ht_oo.1]
            · rw [ho.gammaFactor_def]
              exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
          rw [Stage6LFunctionOrder.completedLFunction_eq_LFunction_mul_gammaFactor χ (.inl hne0) hGne,
            hz, zero_mul]
        exact Stage6LFunctionOrder.completedLFunction_ne_zero_of_re_le_zero hprim hχ (by simp) hc
      · exact hpos
    have hcomp : DirichletCharacter.completedLFunction χ ((σ : ℂ) - I * (t : ℂ)) = 0 :=
      (Stage6LFunctionOrder.completedLFunction_eq_zero_iff_LFunction_of_re_pos χ
        (by simpa using hσ_pos)).mpr hz
    have hmem : ((σ : ℂ) - I * (t : ℂ)) ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr ⟨hcomp, by simp [abs_of_pos (ha.trans ht_oo.1), ht_oo.2.le.trans (le_max_left b 2)]⟩
    apply ht_nbad
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, hmem, by simp [abs_of_pos (ha.trans ht_oo.1)]⟩)

/-- **UNCONDITIONAL FULL RIEMANN–VON MANGOLDT ZERO-COUNT ASYMPTOTIC FOR EVERY PRIMITIVE
`completedLFunction χ` (`0` ASSUMPTIONS, NO ZERO-FREE-LINE HYPOTHESIS ON `T`!)**:
there exists a single universal constant `C > 0` such that for EVERY `q ≥ 1` (`[NeZero q]`),
EVERY primitive `χ : DirichletCharacter ℂ q` with `χ ≠ 1`, and EVERY `T ≥ 2`:
`|lFunctionZeroCount hprim hχ T - (T / π) * Real.log (q * T / (2 * π * e))| ≤ C * Real.log (q * T)`! -/
theorem lFunctionZeroCount_asymptotic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
        (T : ℝ), 2 ≤ T →
        |lFunctionZeroCount hprim hχ T -
            (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          C * Real.log ((q : ℝ) * T) := by
  obtain ⟨C₁, hC₁_pos, hback⟩ := lFunctionZeroCount_backlund_bound
  obtain ⟨C_S, hCS_pos, hS⟩ := abs_backlundSChar_le_log
  set C : ℝ := C₁ + 2 * C_S + 2 with hC_def
  refine ⟨C, by positivity, fun q _ χ hprim hχ T hT => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqT_ge4 : (4 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hlog_ge1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * T) := by
    have h4 : (1 : ℝ) < Real.log 4 := by
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    exact h4.le.trans (Real.log_le_log (by norm_num) hqT_ge4)
  -- Sandwich `T` between two zero-free heights `T₁ ∈ (T - 1, T)` and `T₂ ∈ (T, T + 1)`
  obtain ⟨T₁, hT₁_lo, hT₁_hi, hnz₁⟩ :=
    exists_zeroFree_height_in_Ioo hprim hχ (by linarith : 0 < T - 1) (by linarith : T - 1 < T)
  obtain ⟨T₂, hT₂_lo, hT₂_hi, hnz₂⟩ :=
    exists_zeroFree_height_in_Ioo hprim hχ (by linarith : 0 < T) (by linarith : T < T + 1)
  have hT₁_ge1 : 1 ≤ T₁ := by linarith
  have hT₂_ge1 : 1 ≤ T₂ := by linarith
  have hmono1 : lFunctionZeroCount hprim hχ T₁ ≤ lFunctionZeroCount hprim hχ T :=
    lFunctionZeroCount_mono hprim hχ hT₁_hi.le
  have hmono2 : lFunctionZeroCount hprim hχ T ≤ lFunctionZeroCount hprim hχ T₂ :=
    lFunctionZeroCount_mono hprim hχ hT₂_lo.le
  -- Bound `log(q * (t + 2)) ≤ 2 * log(q * T)` for `t ≤ T + 1`
  have hlog_cmp : ∀ t : ℝ, 1 ≤ t → t ≤ T + 1 →
      Real.log ((q : ℝ) * (t + 2)) ≤ 2 * Real.log ((q : ℝ) * T) := by
    intro t ht1 ht2
    have harg : (q : ℝ) * (t + 2) ≤ ((q : ℝ) * T) ^ 2 := by
      have h1 : t + 2 ≤ 3 * T := by linarith
      calc (q : ℝ) * (t + 2) ≤ (q : ℝ) * (3 * T) := mul_le_mul_of_nonneg_left h1 hqR_pos.le
        _ = 3 * ((q : ℝ) * T) := by ring
        _ ≤ ((q : ℝ) * T) ^ 2 := by nlinarith
    calc Real.log ((q : ℝ) * (t + 2))
        ≤ Real.log (((q : ℝ) * T) ^ 2) := Real.log_le_log (by positivity) harg
      _ = 2 * Real.log ((q : ℝ) * T) := by rw [Real.log_pow]; norm_num
  -- Main-term Lipschitz variation: `|M(t) - M(T)| ≤ 2 * log(q * T)` for `t ∈ [T - 1, T + 1]`
  let M : ℝ → ℝ := fun t => (t / Real.pi) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
  have hM_lip : ∀ t : ℝ, 1 ≤ t → |t - T| ≤ 1 → |M t - M T| ≤ 2 * Real.log ((q : ℝ) * T) := by
    intro t ht1 hdist
    set lo : ℝ := min t T
    set hi : ℝ := max t T
    have hlo1 : 1 ≤ lo := le_min ht1 (by linarith)
    have hhi_le : hi ≤ T + 1 := max_le (by linarith [(abs_le.mp hdist).2]) (by linarith)
    have hlohi : lo ≤ hi := min_le_max
    have hhi_sub_lo : hi - lo ≤ 1 := by
      dsimp only [lo, hi]
      rcases le_total t T with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]; linarith [(abs_le.mp hdist).1]
      · rw [min_eq_right hle, max_eq_left hle]; linarith [(abs_le.mp hdist).2]
    have hderiv : ∀ u ∈ Set.uIcc lo hi,
        HasDerivAt M ((1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))) u := by
      intro u hu
      rw [Set.uIcc_of_le hlohi] at hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (hlo1.trans hu.1)
      have h1 : HasDerivAt (fun x : ℝ => x / Real.pi) (1 / Real.pi) u := by
        simpa using (hasDerivAt_id u).div_const Real.pi
      have h2 : HasDerivAt (fun x : ℝ => Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))) (u⁻¹) u := by
        have hlin : HasDerivAt (fun x : ℝ => (q : ℝ) * x / (2 * Real.pi * Real.exp 1))
            ((q : ℝ) / (2 * Real.pi * Real.exp 1)) u := by
          simpa using ((hasDerivAt_id u).const_mul (q : ℝ)).div_const (2 * Real.pi * Real.exp 1)
        refine (hlin.log (by positivity)).congr_deriv ?_
        field_simp [hqR_pos.ne', hu0.ne', Real.pi_pos.ne', (Real.exp_pos 1).ne']
      refine (h1.mul h2).congr_deriv ?_
      have hlog : Real.log ((q : ℝ) * u / (2 * Real.pi * Real.exp 1)) =
          Real.log ((q : ℝ) * u / (2 * Real.pi)) - 1 := by
        rw [show (q : ℝ) * u / (2 * Real.pi * Real.exp 1) = ((q : ℝ) * u / (2 * Real.pi)) / Real.exp 1 by ring,
          Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
      rw [hlog]
      field_simp [hu0.ne', Real.pi_pos.ne']
      ring
    have hcont : ContinuousOn (fun u : ℝ => (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi)))
        (Set.uIcc lo hi) := by
      rw [Set.uIcc_of_le hlohi]
      refine continuousOn_const.mul (Real.continuousOn_log.comp
        ((continuousOn_const.mul continuousOn_id).div_const _) fun u hu => ?_)
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (hlo1.trans hu.1)
      exact (by positivity : 0 < (q : ℝ) * u / (2 * Real.pi)).ne'
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    have habs_M : |M t - M T| = |M hi - M lo| := by
      dsimp only [lo, hi]
      rcases le_total t T with hle | hle
      · rw [min_eq_left hle, max_eq_right hle, abs_sub_comm]
      · rw [min_eq_right hle, max_eq_left hle]
    rw [habs_M, ← hftc]
    have hpt : ∀ u ∈ Set.Icc lo hi,
        |(1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))| ≤ 2 * Real.log ((q : ℝ) * T) := by
      intro u hu
      have hu1 : 1 ≤ u := hlo1.trans hu.1
      have hu_hi : u ≤ T + 1 := hu.2.trans hhi_le
      have hlog_qu : 0 ≤ Real.log ((q : ℝ) * u) := Real.log_nonneg (by nlinarith)
      have hlog_2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
      have hlog_2pi_le : Real.log (2 * Real.pi) ≤ 2 := by
        have h1 : 2 * Real.pi ≤ Real.exp 2 := by
          have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hsq : (2.7 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he 2
          rw [← Real.exp_nat_mul] at hsq
          norm_num at hsq
          linarith [Real.pi_lt_d2]
        exact (Real.log_le_log (by positivity) h1).trans_eq (Real.log_exp 2)
      have hlog_qu_le : Real.log ((q : ℝ) * u) ≤ 2 * Real.log ((q : ℝ) * T) := by
        have hle : (q : ℝ) * u ≤ (q : ℝ) * (u + 2) := by nlinarith
        exact (Real.log_le_log (by positivity) hle).trans (hlog_cmp u hu1 hu_hi)
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi),
        Real.log_div (by positivity) (by positivity)]
      have habs_diff : |Real.log ((q : ℝ) * u) - Real.log (2 * Real.pi)| ≤
          2 * Real.log ((q : ℝ) * T) + 2 := by
        calc |Real.log ((q : ℝ) * u) - Real.log (2 * Real.pi)|
            ≤ |Real.log ((q : ℝ) * u)| + |Real.log (2 * Real.pi)| := abs_sub _ _
          _ = Real.log ((q : ℝ) * u) + Real.log (2 * Real.pi) := by
              rw [abs_of_nonneg hlog_qu, abs_of_nonneg hlog_2pi]
          _ ≤ 2 * Real.log ((q : ℝ) * T) + 2 := add_le_add hlog_qu_le hlog_2pi_le
      have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
      have hinv_pi : 1 / Real.pi ≤ 1 / 3 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hpi3
      calc (1 / Real.pi) * |Real.log ((q : ℝ) * u) - Real.log (2 * Real.pi)|
          ≤ (1 / 3) * (2 * Real.log ((q : ℝ) * T) + 2) :=
            mul_le_mul hinv_pi habs_diff (abs_nonneg _) (by norm_num)
        _ ≤ 2 * Real.log ((q : ℝ) * T) := by linarith
    calc |∫ u in lo..hi, (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))|
        = ‖∫ u in lo..hi, (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ u in lo..hi, ‖(1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hlohi
      _ ≤ ∫ _u in lo..hi, (2 * Real.log ((q : ℝ) * T)) :=
          intervalIntegral.integral_mono_on hlohi hcont.intervalIntegrable.norm
            intervalIntegrable_const fun u hu => by rw [Real.norm_eq_abs]; exact hpt u hu
      _ = (hi - lo) * (2 * Real.log ((q : ℝ) * T)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 1 * (2 * Real.log ((q : ℝ) * T)) :=
          mul_le_mul_of_nonneg_right hhi_sub_lo (by linarith)
      _ = 2 * Real.log ((q : ℝ) * T) := one_mul _
  -- Apply Backlund + Jensen at `T₁` and `T₂` and squeeze `N(T, χ)`!
  have hb1 : |lFunctionZeroCount hprim hχ T₁ - M T₁| ≤ (C₁ + 2 * C_S) * Real.log ((q : ℝ) * T) := by
    have h1 := hback q χ hprim hχ T₁ hT₁_ge1 hnz₁
    have h2 := hS q χ hprim hχ T₁ hT₁_ge1 hnz₁
    have h3 := hlog_cmp T₁ hT₁_ge1 (by linarith)
    nlinarith
  have hb2 : |lFunctionZeroCount hprim hχ T₂ - M T₂| ≤ (C₁ + 2 * C_S) * Real.log ((q : ℝ) * T) := by
    have h1 := hback q χ hprim hχ T₂ hT₂_ge1 hnz₂
    have h2 := hS q χ hprim hχ T₂ hT₂_ge1 hnz₂
    have h3 := hlog_cmp T₂ hT₂_ge1 hT₂_hi.le
    nlinarith
  have hlip1 := hM_lip T₁ hT₁_ge1 (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hlip2 := hM_lip T₂ hT₂_ge1 (abs_le.mpr ⟨by linarith, by linarith⟩)
  change |lFunctionZeroCount hprim hχ T - M T| ≤ C * Real.log ((q : ℝ) * T)
  rw [abs_le]
  have h1_lo := (abs_le.mp hb1).1
  have h2_hi := (abs_le.mp hb2).2
  have hl1_lo := (abs_le.mp hlip1).1
  have hl2_hi := (abs_le.mp hlip2).2
  dsimp only [C]
  constructor <;> linarith

end RHDirect.Stage8GRHEquivalence

end
