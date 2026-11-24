import RHDirect.Stage3ZeroFreeRegion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# RHDirect.Stage5JensenHadamard

Self-contained, 0-`sorry`, 0-custom-`axiom` Lean 4 formalization of **Jensen's Formula,
Order-1 Zero Counting, Weierstrass–Hadamard Genus-1 Canonical Product Convergence,
Davenport's Real-Part Cancellation Identity, and the Hadamard Log-Derivative Partial-Fraction
Bridge to `Stage3ZeroFreeRegion.HadamardLogDerivPackage`** in pure Mathlib `v4.33.1`.

## Main Contents
1. **Blaschke Factors on `closedBall 0 R`**:
   - `blaschkeFactor R a z = R (z - a) / (R² - conj(a) z)`.
   - Exact modulus identity `‖R (z - a)‖² - ‖R² - conj(a) z‖² = -(R² - ‖a‖²)(R² - ‖z‖²)`,
     yielding `‖B_a(z)‖ = 1` on `‖z‖ = R`, `‖B_a(z)‖ < 1` on `‖z‖ < R`, `B_a(a) = 0`,
     `‖B_a(0)‖ = ‖a‖ / R`, and holomorphicity (`DifferentiableOn` & `AnalyticOnNhd`) on `|z| ≤ R`.
2. **Finite Blaschke Factorization, Jensen's Inequality & Zero-Counting Bounds**:
   - `exists_blaschke_quotient_of_zeros`: iterative `dslope` removal of any finite zero set
     `Z ⊆ ball 0 R` for any `DiffContOnCl ℂ f (ball 0 R)`.
   - `jensen_prod_le`: `∏ a ∈ Z, (R / ‖a‖) ≤ M / ‖f 0‖` via Maximum Modulus on `f / ∏ B_a`.
   - `jensen_zero_count_le`: `(Z.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r)` for
     `0 < r < R` and zeros in `closedBall 0 r` (plus `AnalyticOnNhd` circle-average & divisor
     bridge to Mathlib's `AnalyticOnNhd.circleAverage_log_norm` and `AnalyticOnNhd.sum_divisor_le`).
3. **Order-`≤ 1` Entire Functions & Convergence Exponent**:
   - `order_one_zero_count_le`: `n(r) ≤ C r log(r + 2)` for every entire function satisfying
     `‖f z‖ ≤ exp(A ‖z‖ log(‖z‖ + 2) + B)` and `f 0 ≠ 0`.
   - `summable_rpow_neg_of_zero_counting` & `summable_inv_sq_of_zero_counting`:
     dyadic summation proving `∑' n, ‖ρ n‖ ^ (-σ) < ∞` for every `σ > 1`, and in particular
     `∑' n, (‖ρ n‖ ^ 2)⁻¹ < ∞`.
4. **Weierstrass Genus-1 Elementary Factors & Canonical Product Convergence**:
   - `weierstrassE1 z = (1 - z) exp(z)`, sharp bounds `‖log E_1(z)‖ ≤ ‖z‖² ≤ 2 ‖z‖²` and
     `‖E_1(z) - 1‖ ≤ 2 ‖z‖²` for `‖z‖ ≤ 1/2`.
   - Unconditional convergence (`multipliable_weierstrassE1`), entireness
     (`differentiable_weierstrassProduct`), zero-set characterization
     (`weierstrassProduct_eq_zero_iff`), and term-by-term logarithmic derivative
     (`hasSum_logDeriv_weierstrassProduct`, `logDeriv_weierstrassProduct_eq_tsum`) for any
     sequence `{ρ n}` with `∑ (‖ρ n‖²)⁻¹ < ∞`.
5. **Critical-Strip Positivity, Davenport's Identity & Principal-Character Euler Bound**:
   - Exact real-part positivity `Re(1 / (s - ρ)) > 0`, `Re(1 / (s - ρ) + 1 / (s - (1 - conj ρ))) > 0`,
     and `Re(1 / (s - ρ) + 1 / ρ) > Re(1 / (s - ρ)) > 0` for `0 < Re(ρ) < 1 < Re(s)`.
   - `davenport_re_B_eq_neg_tsum_re_inv`: unconditional derivation of `Re(B) = -∑_ρ Re(1 / ρ)`
     from functional-equation symmetry `ρ ↦ 1 - conj ρ`.
   - `norm_negLogDerivL_one_sub_negLogDerivZeta_le_log`: unconditional Euler-factor bound
     `‖-L'/L(1_q, s) - (-ζ'/ζ(s))‖ ≤ log q` for all `q ≥ 1` and `Re(s) > 1`.
6. **Bridge to `Stage3ZeroFreeRegion.HadamardLogDerivPackage`**:
   - `hadamardLogDerivPackage_of_partialFractionSystem` and direct wiring into
     `zeroFreeRegion_complex_char`, `zeroFreeRegion_real_char_nonreal_zero`,
     `zeroFreeRegion_riemannZeta`, `real_char_at_most_one_exceptional_real_zero`,
     `landau_page_exceptional_zero_isolation`, and `zeroFreeRegion_nonexceptional`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Finset Filter Topology Metric
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage5JensenHadamard

/-! ## Section 1: Blaschke Factors on `closedBall 0 R` -/

/-- Blaschke factor `B_a(z) = R (z - a) / (R² - conj(a) z)` on the disk of radius `R`. -/
def blaschkeFactor (R : ℝ) (a z : ℂ) : ℂ :=
  (R : ℂ) * (z - a) / ((R : ℂ) ^ 2 - starRingEnd ℂ a * z)

/-- The denominator `R² - conj(a) z` of a Blaschke factor never vanishes on `‖z‖ ≤ R`
when `‖a‖ < R`. -/
theorem blaschke_denom_ne_zero {R : ℝ} {a z : ℂ} (hR : 0 < R) (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) :
    (R : ℂ) ^ 2 - starRingEnd ℂ a * z ≠ 0 := by
  intro h
  have heq : (R : ℂ) ^ 2 = starRingEnd ℂ a * z := sub_eq_zero.mp h
  have hnorm : ‖(R : ℂ) ^ 2‖ = ‖starRingEnd ℂ a * z‖ := congrArg norm heq
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul,
    RCLike.norm_conj] at hnorm
  have hlt : ‖a‖ * ‖z‖ < R ^ 2 := by
    rw [sq]
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hz (norm_nonneg a) hR
  linarith

/-- Stronger denominator nonvanishing on an open disk slightly larger than `closedBall 0 R`. -/
lemma blaschke_denom_ne_zero_of_mul_lt {R : ℝ} {a z : ℂ} (hR : 0 < R) (h : ‖a‖ * ‖z‖ < R ^ 2) :
    (R : ℂ) ^ 2 - starRingEnd ℂ a * z ≠ 0 := by
  intro h0
  have heq : (R : ℂ) ^ 2 = starRingEnd ℂ a * z := sub_eq_zero.mp h0
  have hnorm : ‖(R : ℂ) ^ 2‖ = ‖starRingEnd ℂ a * z‖ := congrArg norm heq
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul,
    RCLike.norm_conj] at hnorm
  linarith

/-- Every Blaschke factor vanishes at its zero `a`: `B_a(a) = 0`. -/
@[simp]
theorem blaschkeFactor_self (R : ℝ) (a : ℂ) : blaschkeFactor R a a = 0 := by
  simp [blaschkeFactor]

/-- Evaluation at the origin: `B_a(0) = -a / R` for `R ≠ 0`. -/
theorem blaschkeFactor_zero {R : ℝ} (hR : R ≠ 0) (a : ℂ) :
    blaschkeFactor R a 0 = -a / (R : ℂ) := by
  unfold blaschkeFactor
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  field_simp [hRC]
  ring

/-- Modulus at the origin: `‖B_a(0)‖ = ‖a‖ / R` for `R > 0`. -/
theorem norm_blaschkeFactor_zero {R : ℝ} (hR : 0 < R) (a : ℂ) :
    ‖blaschkeFactor R a 0‖ = ‖a‖ / R := by
  rw [blaschkeFactor_zero hR.ne', norm_div, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hR.le]

/-- A Blaschke factor vanishes nowhere on `‖z‖ ≤ R` except at `z = a`. -/
theorem blaschkeFactor_ne_zero {R : ℝ} {a z : ℂ} (hR : 0 < R) (ha : ‖a‖ < R)
    (hz : ‖z‖ ≤ R) (hne : z ≠ a) : blaschkeFactor R a z ≠ 0 := by
  unfold blaschkeFactor
  refine div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (sub_ne_zero.mpr hne))
    (blaschke_denom_ne_zero hR ha hz)

/-- Fundamental Blaschke norm-squared algebraic identity:
`‖R (z - a)‖² - ‖R² - conj(a) z‖² = -(R² - ‖a‖²) (R² - ‖z‖²)`. -/
theorem blaschke_norm_sq_sub_eq (R : ℝ) (a z : ℂ) :
    ‖(R : ℂ) * (z - a)‖ ^ 2 - ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * z‖ ^ 2 =
      -((R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2)) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    sq]
  ring

/-- On the boundary circle `‖z‖ = R`, every Blaschke factor has unit modulus `‖B_a(z)‖ = 1`. -/
theorem norm_blaschkeFactor_eq_one_of_norm_eq {R : ℝ} {a z : ℂ} (hR : 0 < R) (ha : ‖a‖ < R)
    (hz : ‖z‖ = R) : ‖blaschkeFactor R a z‖ = 1 := by
  have hden : (R : ℂ) ^ 2 - starRingEnd ℂ a * z ≠ 0 := blaschke_denom_ne_zero hR ha hz.le
  have hid := blaschke_norm_sq_sub_eq R a z
  rw [hz, sub_self, mul_zero, neg_zero] at hid
  have hsq : ‖(R : ℂ) * (z - a)‖ ^ 2 = ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * z‖ ^ 2 :=
    sub_eq_zero.mp hid
  have heq : ‖(R : ℂ) * (z - a)‖ = ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * z‖ := by
    nlinarith [norm_nonneg ((R : ℂ) * (z - a)), norm_nonneg ((R : ℂ) ^ 2 - starRingEnd ℂ a * z)]
  unfold blaschkeFactor
  rw [norm_div, heq, div_self (norm_ne_zero_iff.mpr hden)]

/-- Inside the open disk `‖z‖ < R`, every Blaschke factor satisfies `‖B_a(z)‖ < 1`. -/
theorem norm_blaschkeFactor_lt_one_of_norm_lt {R : ℝ} {a z : ℂ} (hR : 0 < R) (ha : ‖a‖ < R)
    (hz : ‖z‖ < R) : ‖blaschkeFactor R a z‖ < 1 := by
  have hden : (R : ℂ) ^ 2 - starRingEnd ℂ a * z ≠ 0 := blaschke_denom_ne_zero hR ha hz.le
  have hden_pos : 0 < ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * z‖ := norm_pos_iff.mpr hden
  have hid := blaschke_norm_sq_sub_eq R a z
  have ha2 : 0 < R ^ 2 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 < R ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hlt_sq : ‖(R : ℂ) * (z - a)‖ ^ 2 < ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * z‖ ^ 2 := by
    nlinarith
  have hlt : ‖(R : ℂ) * (z - a)‖ < ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * z‖ := by
    nlinarith [norm_nonneg ((R : ℂ) * (z - a)), norm_nonneg ((R : ℂ) ^ 2 - starRingEnd ℂ a * z)]
  unfold blaschkeFactor
  rw [norm_div]
  exact (div_lt_one hden_pos).mpr hlt

/-- On the closed disk `‖z‖ ≤ R`, every Blaschke factor satisfies `‖B_a(z)‖ ≤ 1`. -/
theorem norm_blaschkeFactor_le_one_of_norm_le {R : ℝ} {a z : ℂ} (hR : 0 < R) (ha : ‖a‖ < R)
    (hz : ‖z‖ ≤ R) : ‖blaschkeFactor R a z‖ ≤ 1 := by
  rcases hz.lt_or_eq with hlt | heq
  · exact (norm_blaschkeFactor_lt_one_of_norm_lt hR ha hlt).le
  · exact (norm_blaschkeFactor_eq_one_of_norm_eq hR ha heq).le

/-- Each Blaschke factor is differentiable at every point `z` with `‖a‖ * ‖z‖ < R²`. -/
theorem differentiableAt_blaschkeFactor_of_mul_lt {R : ℝ} {a z : ℂ} (hR : 0 < R)
    (h : ‖a‖ * ‖z‖ < R ^ 2) : DifferentiableAt ℂ (blaschkeFactor R a) z := by
  unfold blaschkeFactor
  refine DifferentiableAt.div ?_ ?_ (blaschke_denom_ne_zero_of_mul_lt hR h)
  · exact (differentiableAt_const _).mul (differentiableAt_id.sub (differentiableAt_const _))
  · exact (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)

/-- Each Blaschke factor is holomorphic (`DifferentiableOn`) on `closedBall 0 R`. -/
theorem differentiableOn_blaschkeFactor_closedBall {R : ℝ} {a : ℂ} (hR : 0 < R) (ha : ‖a‖ < R) :
    DifferentiableOn ℂ (blaschkeFactor R a) (closedBall 0 R) := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  have hmul : ‖a‖ * ‖z‖ < R ^ 2 := by
    rw [sq]
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hz (norm_nonneg a) hR
  exact (differentiableAt_blaschkeFactor_of_mul_lt hR hmul).differentiableWithinAt

/-- Each Blaschke factor is analytic (`AnalyticOnNhd`) on `closedBall 0 R`. -/
theorem analyticOnNhd_blaschkeFactor_closedBall {R : ℝ} {a : ℂ} (hR : 0 < R) (ha : ‖a‖ < R) :
    AnalyticOnNhd ℂ (blaschkeFactor R a) (closedBall 0 R) := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  have hmul : ‖a‖ * ‖z‖ < R ^ 2 := by
    rw [sq]
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hz (norm_nonneg a) hR
  set U : Set ℂ := {w : ℂ | ‖a‖ * ‖w‖ < R ^ 2}
  have hU_open : IsOpen U :=
    isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hU_diff : DifferentiableOn ℂ (blaschkeFactor R a) U := fun w hw =>
    (differentiableAt_blaschkeFactor_of_mul_lt hR hw).differentiableWithinAt
  exact hU_diff.analyticAt (hU_open.mem_nhds hmul)

/-! ## Section 2: Finite Blaschke Factorization, Jensen's Inequality & Zero-Counting Bounds -/

private lemma continuousOn_dslope_closedBall {R : ℝ} {a : ℂ} {g : ℂ → ℂ}
    (hR : 0 < R) (ha : a ∈ ball (0 : ℂ) R) (hg : DiffContOnCl ℂ g (ball 0 R)) :
    ContinuousOn (dslope g a) (closedBall 0 R) := by
  have hdiff : DifferentiableOn ℂ (dslope g a) (ball 0 R) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr hg.differentiableOn
  intro z hz
  by_cases hzb : z ∈ ball (0 : ℂ) R
  · exact (hdiff.continuousOn.continuousAt (isOpen_ball.mem_nhds hzb)).continuousWithinAt
  · have hzne : z ≠ a := fun h => hzb (h ▸ ha)
    have hcont_g : ContinuousWithinAt g (closedBall 0 R) z := by
      have hcl : closure (ball (0 : ℂ) R) = closedBall 0 R := closure_ball 0 hR.ne'
      exact (hcl ▸ hg.continuousOn) z hz
    have hcont_quot : ContinuousWithinAt (fun w => (w - a)⁻¹ * (g w - g a)) (closedBall 0 R) z := by
      refine ContinuousWithinAt.mul ?_ (hcont_g.sub continuousWithinAt_const)
      exact (continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.mpr hzne)
    refine hcont_quot.congr_of_eventuallyEq ?_ (by simp [dslope_of_ne, slope_def_field, div_eq_inv_mul, hzne])
    have hne_ev : ∀ᶠ w in nhds z, w ≠ a := isOpen_ne.mem_nhds hzne
    filter_upwards [nhdsWithin_le_nhds hne_ev] with w hw
    simp [dslope_of_ne, slope_def_field, div_eq_inv_mul, hw]

/-- **Finite Blaschke Factorization**: for any function `f` holomorphic on `ball 0 R` and
continuous on `closedBall 0 R` (`DiffContOnCl ℂ f (ball 0 R)`), and any finite set `Z` of zeros
of `f` inside `ball 0 R`, there exists `g` with `DiffContOnCl ℂ g (ball 0 R)` such that
`f z = g z * ∏ a ∈ Z, B_a(z)` for all `z ∈ closedBall 0 R`. -/
theorem exists_blaschke_quotient_of_zeros {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (Z : Finset ℂ)
    (hZ_ball : ∀ a ∈ Z, a ∈ ball (0 : ℂ) R) (hZ_zero : ∀ a ∈ Z, f a = 0) :
    ∃ g : ℂ → ℂ, DiffContOnCl ℂ g (ball 0 R) ∧
      ∀ z ∈ closedBall (0 : ℂ) R, f z = g z * ∏ a ∈ Z, blaschkeFactor R a z := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    exact ⟨f, hf, fun z _ => by simp⟩
  | @insert a S haS ih =>
    have ha_ball : a ∈ ball (0 : ℂ) R := hZ_ball a (mem_insert_self a S)
    have ha_norm : ‖a‖ < R := mem_ball_zero_iff.mp ha_ball
    have ha_zero : f a = 0 := hZ_zero a (mem_insert_self a S)
    obtain ⟨g, hg_dcc, hg_eq⟩ := ih
      (fun b hb => hZ_ball b (mem_insert_of_mem hb))
      (fun b hb => hZ_zero b (mem_insert_of_mem hb))
    have hprod_ne : (∏ b ∈ S, blaschkeFactor R b a) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun b hb => ?_
      have hb_norm : ‖b‖ < R := mem_ball_zero_iff.mp (hZ_ball b (mem_insert_of_mem hb))
      have hne : a ≠ b := fun h => haS (h ▸ hb)
      exact blaschkeFactor_ne_zero hR hb_norm ha_norm.le hne
    have hga : g a = 0 := by
      have h1 := hg_eq a (ball_subset_closedBall ha_ball)
      rw [ha_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hprod_ne
    let g₁ : ℂ → ℂ := fun z => dslope g a z * (((R : ℂ) ^ 2 - starRingEnd ℂ a * z) / (R : ℂ))
    have hlin_diff : Differentiable ℂ (fun z : ℂ => ((R : ℂ) ^ 2 - starRingEnd ℂ a * z) / (R : ℂ)) :=
      ((differentiable_const _).sub ((differentiable_const _).mul differentiable_id)).div_const _
    have hg1_diff : DifferentiableOn ℂ g₁ (ball 0 R) := by
      have hd : DifferentiableOn ℂ (dslope g a) (ball 0 R) :=
        (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha_ball)).mpr hg_dcc.differentiableOn
      exact hd.mul hlin_diff.differentiableOn
    have hg1_cont : ContinuousOn g₁ (closure (ball 0 R)) := by
      rw [closure_ball 0 hR.ne']
      exact (continuousOn_dslope_closedBall hR ha_ball hg_dcc).mul hlin_diff.continuous.continuousOn
    refine ⟨g₁, ⟨hg1_diff, hg1_cont⟩, fun z hz => ?_⟩
    rw [Finset.prod_insert haS]
    rw [hg_eq z hz]
    suffices hstep : g z = g₁ z * blaschkeFactor R a z by
      rw [hstep]; ring
    by_cases hza : z = a
    · subst hza
      simp [hga]
    · have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
      have hden : (R : ℂ) ^ 2 - starRingEnd ℂ a * z ≠ 0 :=
        blaschke_denom_ne_zero hR ha_norm (mem_closedBall_zero_iff.mp hz)
      have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
      dsimp only [g₁, blaschkeFactor]
      rw [dslope_of_ne _ hza, slope_def_field, hga, sub_zero]
      have hden' : (R : ℂ) ^ 2 - z * starRingEnd ℂ a ≠ 0 := by simpa [mul_comm] using hden
      field_simp [hRC, hden, hden', hza']

/-- **Jensen's Upper Bound (Product Form)**: for any `f` holomorphic on `ball 0 R` and continuous
on `closedBall 0 R`, with `f 0 ≠ 0`, `‖f z‖ ≤ M` on `sphere 0 R`, and any finite set `Z` of zeros
of `f` in `ball 0 R`, we have `∏ a ∈ Z, (R / ‖a‖) ≤ M / ‖f 0‖`. -/
theorem jensen_prod_le {R M : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (Z : Finset ℂ)
    (hZ_ball : ∀ a ∈ Z, a ∈ ball (0 : ℂ) R) (hZ_zero : ∀ a ∈ Z, f a = 0) :
    ∏ a ∈ Z, (R / ‖a‖) ≤ M / ‖f 0‖ := by
  obtain ⟨g, hg_dcc, hg_eq⟩ := exists_blaschke_quotient_of_zeros hR hf Z hZ_ball hZ_zero
  have hg_frontier : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖g z‖ ≤ M := by
    intro z hz
    rw [frontier_ball (0 : ℂ) hR.ne'] at hz
    have hz_norm : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
    have hprod_norm : ‖∏ a ∈ Z, blaschkeFactor R a z‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one fun a ha =>
        norm_blaschkeFactor_eq_one_of_norm_eq hR (mem_ball_zero_iff.mp (hZ_ball a ha)) hz_norm
    have hfz := hg_eq z (sphere_subset_closedBall hz)
    have hnorm_eq : ‖f z‖ = ‖g z‖ := by
      rw [hfz, norm_mul, hprod_norm, mul_one]
    linarith [hM z hz]
  have hg0_le : ‖g 0‖ ≤ M := by
    have h0_mem : (0 : ℂ) ∈ closure (ball (0 : ℂ) R) := by
      rw [closure_ball 0 hR.ne']
      exact mem_closedBall_self hR.le
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg_dcc hg_frontier h0_mem
  have hf0_eq : ‖f 0‖ = ‖g 0‖ * ∏ a ∈ Z, (‖a‖ / R) := by
    have h1 := hg_eq 0 (mem_closedBall_self hR.le)
    rw [h1, norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun a _ => norm_blaschkeFactor_zero hR a
  have hprod_pos : 0 < ∏ a ∈ Z, (‖a‖ / R) := by
    refine Finset.prod_pos fun a ha => div_pos ?_ hR
    have ha0 : a ≠ 0 := fun h => hf0 (h ▸ hZ_zero a ha)
    exact norm_pos_iff.mpr ha0
  have hinv : ∏ a ∈ Z, (R / ‖a‖) = (∏ a ∈ Z, (‖a‖ / R))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun a _ => (inv_div ‖a‖ R).symm
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  rw [hinv, le_div_iff₀ hf0_pos, inv_mul_le_iff₀ hprod_pos]
  nlinarith [hf0_eq, hg0_le]

/-- **Jensen's Upper Bound (Logarithmic Sum Form)**:
`∑ a ∈ Z, Real.log (R / ‖a‖) ≤ Real.log (M / ‖f 0‖)`. -/
theorem jensen_sum_log_le {R M : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (Z : Finset ℂ)
    (hZ_ball : ∀ a ∈ Z, a ∈ ball (0 : ℂ) R) (hZ_zero : ∀ a ∈ Z, f a = 0) :
    ∑ a ∈ Z, Real.log (R / ‖a‖) ≤ Real.log (M / ‖f 0‖) := by
  have hprod := jensen_prod_le hR hf hf0 hM Z hZ_ball hZ_zero
  have hpos : ∀ a ∈ Z, R / ‖a‖ ≠ 0 := fun a ha => by
    have ha0 : a ≠ 0 := fun h => hf0 (h ▸ hZ_zero a ha)
    exact div_ne_zero hR.ne' (norm_ne_zero_iff.mpr ha0)
  have hprod_pos : 0 < ∏ a ∈ Z, (R / ‖a‖) := Finset.prod_pos fun a ha =>
    div_pos hR (norm_pos_iff.mpr fun h => hf0 (h ▸ hZ_zero a ha))
  rw [← Real.log_prod hpos]
  exact Real.log_le_log hprod_pos hprod

/-- **Exact Jensen Zero-Counting Inequality** (for zeros in `closedBall 0 r`, `0 < r < R`):
`(Z.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r)`. -/
theorem jensen_zero_count_le {r R M : ℝ} (hr : 0 < r) (hrR : r < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (Z : Finset ℂ)
    (hZ_ball : ∀ a ∈ Z, a ∈ closedBall (0 : ℂ) r) (hZ_zero : ∀ a ∈ Z, f a = 0) :
    (Z.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hZ_open : ∀ a ∈ Z, a ∈ ball (0 : ℂ) R := fun a ha =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hZ_ball a ha)).trans_lt hrR)
  have hsum := jensen_sum_log_le hR hf hf0 hM Z hZ_open hZ_zero
  have hlog_pos : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlower : (Z.card : ℝ) * Real.log (R / r) ≤ ∑ a ∈ Z, Real.log (R / ‖a‖) := by
    calc (Z.card : ℝ) * Real.log (R / r)
        = ∑ _a ∈ Z, Real.log (R / r) := by simp
      _ ≤ ∑ a ∈ Z, Real.log (R / ‖a‖) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr fun h => hf0 (h ▸ hZ_zero a ha)
          have ha_le : ‖a‖ ≤ r := mem_closedBall_zero_iff.mp (hZ_ball a ha)
          exact Real.log_le_log (div_pos hR hr) (div_le_div_of_nonneg_left hR.le ha_pos ha_le)
  exact (le_div_iff₀ hlog_pos).mpr (hlower.trans hsum)

/-- Exact Jensen zero-counting inequality for zeros in the open ball `ball 0 r`. -/
theorem jensen_zero_count_ball_le {r R M : ℝ} (hr : 0 < r) (hrR : r < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (Z : Finset ℂ)
    (hZ_ball : ∀ a ∈ Z, a ∈ ball (0 : ℂ) r) (hZ_zero : ∀ a ∈ Z, f a = 0) :
    (Z.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) :=
  jensen_zero_count_le hr hrR hf hf0 hM Z (fun a ha => ball_subset_closedBall (hZ_ball a ha)) hZ_zero

/-- **Exact Circle-Average Jensen's Formula** (wrapper around Mathlib's
`AnalyticOnNhd.circleAverage_log_norm`) for `f` analytic on `closedBall 0 R` with `f 0 ≠ 0`. -/
theorem jensen_circleAverage_exact {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    Real.circleAverage (fun x => Real.log ‖f x‖) 0 R =
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (closedBall 0 R) u : ℝ) * Real.log (R * ‖u‖⁻¹)) +
        Real.log ‖f 0‖ := by
  have h := AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := R) (f := f)
    hR.ne' (by rwa [abs_of_pos hR]) hf0
  rw [abs_of_pos hR] at h
  simpa using h

/-- **Multiplicity-Counted Jensen Zero-Counting Bound** via Mathlib's divisor formulation. -/
theorem jensen_divisor_zero_count_le {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM1 : 1 ≤ M)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    ((∑ᶠ u : ℂ, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) ≤
      Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have h := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := R) (M := M) (f := f)
    (by rwa [abs_of_pos hr])
    (by rwa [abs_of_pos hr, abs_of_pos hR])
    hM1 (by rwa [abs_of_pos hR]) hf0 (by rwa [abs_of_pos hR])
  rwa [abs_of_pos hr] at h

/-! ## Section 3: Order-`≤ 1` Entire Functions & Convergence Exponent -/

/-- An entire function of order `≤ 1` (with logarithmic factor matching `ξ(s)` and `Λ(s, χ)`):
`‖f z‖ ≤ exp(A ‖z‖ log(‖z‖ + 2) + B)` for all `z : ℂ`. -/
def HasOrderOneGrowth (f : ℂ → ℂ) (A B : ℝ) : Prop :=
  Differentiable ℂ f ∧ ∀ z : ℂ, ‖f z‖ ≤ Real.exp (A * ‖z‖ * Real.log (‖z‖ + 2) + B)

private lemma log_two_mul_add_two_le {r : ℝ} (hr : 1 ≤ r) :
    Real.log (2 * r + 2) ≤ 2 * Real.log (r + 2) := by
  have h1 : 2 * r + 2 ≤ (r + 2) ^ 2 := by nlinarith
  calc Real.log (2 * r + 2)
      ≤ Real.log ((r + 2) ^ 2) := Real.log_le_log (by linarith) h1
    _ = 2 * Real.log (r + 2) := by rw [Real.log_pow]; norm_num

private lemma one_le_log_add_two {r : ℝ} (hr : 1 ≤ r) : 1 ≤ Real.log (r + 2) := by
  have he : Real.exp 1 ≤ r + 2 := by
    have := Real.exp_one_lt_d9
    linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (r + 2) := Real.log_le_log (Real.exp_pos 1) he

/-- **Order-`≤ 1` Zero-Counting Bound (`n(r) ≤ C r log(r + 2)`)**:
every entire function `f` with `‖f z‖ ≤ exp(A ‖z‖ log(‖z‖ + 2) + B)` (`A ≥ 0`) and `f 0 ≠ 0`
has at most `C * r * log(r + 2)` zeros in `closedBall 0 r` for all `r ≥ 1`, with explicit constant
`C = (4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2`. -/
theorem order_one_zero_count_le {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hf : HasOrderOneGrowth f A B) (hf0 : f 0 ≠ 0) :
    ∀ r : ℝ, 1 ≤ r → ∀ Z : Finset ℂ,
      (∀ a ∈ Z, a ∈ closedBall (0 : ℂ) r) → (∀ a ∈ Z, f a = 0) →
      (Z.card : ℝ) ≤
        ((4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2) * r * Real.log (r + 2) := by
  intro r hr Z hZ_ball hZ_zero
  have hr_pos : 0 < r := by linarith
  have hR : r < 2 * r := by linarith
  let M : ℝ := Real.exp (A * (2 * r) * Real.log (2 * r + 2) + B)
  have hM_bound : ∀ z ∈ sphere (0 : ℂ) (2 * r), ‖f z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ = 2 * r := mem_sphere_zero_iff_norm.mp hz
    simpa [M, hzn] using hf.2 z
  have hj := jensen_zero_count_le hr_pos hR hf.1.diffContOnCl hf0 hM_bound Z hZ_ball hZ_zero
  have hdiv : 2 * r / r = 2 := by field_simp [hr_pos.ne']
  rw [hdiv] at hj
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hlogM : Real.log (M / ‖f 0‖) = A * (2 * r) * Real.log (2 * r + 2) + B - Real.log ‖f 0‖ := by
    rw [Real.log_div (Real.exp_pos _).ne' hf0_pos.ne', Real.log_exp]
  rw [hlogM] at hj
  have hlog2r : Real.log (2 * r + 2) ≤ 2 * Real.log (r + 2) := log_two_mul_add_two_le hr
  have h1le : 1 ≤ r * Real.log (r + 2) := by
    have h1 := one_le_log_add_two hr
    nlinarith
  have hnum : A * (2 * r) * Real.log (2 * r + 2) + B - Real.log ‖f 0‖ ≤
      (4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) * (r * Real.log (r + 2)) := by
    have hA_term : A * (2 * r) * Real.log (2 * r + 2) ≤ 4 * A * (r * Real.log (r + 2)) := by
      have h1 := mul_le_mul_of_nonneg_left hlog2r (by positivity : 0 ≤ A * (2 * r))
      linarith
    have hB_term : B ≤ max B 0 * (r * Real.log (r + 2)) := by
      have h1 : B ≤ max B 0 := le_max_left B 0
      have h2 : 0 ≤ max B 0 := le_max_right B 0
      nlinarith
    have hf0_term : -Real.log ‖f 0‖ ≤ max (-Real.log ‖f 0‖) 0 * (r * Real.log (r + 2)) := by
      have h1 : -Real.log ‖f 0‖ ≤ max (-Real.log ‖f 0‖) 0 := le_max_left _ 0
      have h2 : 0 ≤ max (-Real.log ‖f 0‖) 0 := le_max_right _ 0
      nlinarith
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc (Z.card : ℝ)
      ≤ (A * (2 * r) * Real.log (2 * r + 2) + B - Real.log ‖f 0‖) / Real.log 2 := hj
    _ ≤ ((4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) * (r * Real.log (r + 2))) / Real.log 2 :=
        div_le_div_of_nonneg_right hnum hlog2_pos.le
    _ = ((4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2) * r * Real.log (r + 2) := by
        ring

/-- **Dyadic Convergence Exponent Theorem**: if `ρ : ℕ → ℂ` satisfies `∀ n, ρ n ≠ 0` and has
cumulative counting bound `#{n | ‖ρ n‖ ≤ r} ≤ C * r * log(r + 2)` for all `r ≥ 1`, then
`∑' n, ‖ρ n‖ ^ (-σ)` converges for every `σ > 1`! -/
theorem summable_rpow_neg_of_zero_counting {ρ : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (_hρ_ne : ∀ n, ρ n ≠ 0)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ ≤ r) → (F.card : ℝ) ≤ C * r * Real.log (r + 2))
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖ρ n‖ ^ (-σ)) := by
  classical
  -- Step 1: The set `{n | ‖ρ n‖ < 1}` is finite because its cardinality is bounded by `C * log 3`.
  have hsmall_fin : {n : ℕ | ‖ρ n‖ < 1}.Finite := by
    by_contra hinf
    obtain ⟨F, hFsub, hFcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (Nat.floor (C * Real.log 3) + 1)
    have hle := hcount 1 le_rfl F (fun n hn => (hFsub hn).le)
    simp only [mul_one, show (1 : ℝ) + 2 = 3 by norm_num] at hle
    have hgt : C * Real.log 3 < (F.card : ℝ) := by
      rw [hFcard]; push_cast; exact Nat.lt_floor_add_one _
    linarith
  set F₀ : Finset ℕ := hsmall_fin.toFinset
  set S₀ : ℝ := ∑ n ∈ F₀, ‖ρ n‖ ^ (-σ)
  -- Step 2: Dyadic geometric majorant for `k ≥ 0` on `2^k ≤ ‖ρ n‖ < 2^(k+1)`.
  set q : ℝ := (2 : ℝ) ^ (1 - σ)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq_lt1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom_k : Summable (fun k : ℕ => ((k : ℝ) + 2) * q ^ k) := by
    have h1 : Summable (fun k : ℕ => ((k : ℝ) * q ^ k)) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q) (by rwa [Real.norm_of_nonneg hq_pos.le])
      simpa [pow_one] using h
    have h2 : Summable (fun k : ℕ => (2 : ℝ) * q ^ k) :=
      (summable_geometric_of_lt_one hq_pos.le hq_lt1).mul_left 2
    refine (h1.add h2).congr fun k => by ring
  set B_dyadic : ℝ := ∑' k : ℕ, (4 * C * Real.log 2) * (((k : ℝ) + 2) * q ^ k)
  refine summable_of_sum_le (fun n => Real.rpow_nonneg (norm_nonneg (ρ n)) (-σ))
    (c := S₀ + B_dyadic) fun F => ?_
  -- Split `F` into `F_small = F ∩ {‖ρ n‖ < 1}` and `F_large = F ∩ {1 ≤ ‖ρ n‖}`.
  let F_small := F.filter (fun n => ‖ρ n‖ < 1)
  let F_large := F.filter (fun n => ¬ (‖ρ n‖ < 1))
  have hsplit : ∑ n ∈ F, ‖ρ n‖ ^ (-σ) =
      (∑ n ∈ F_small, ‖ρ n‖ ^ (-σ)) + ∑ n ∈ F_large, ‖ρ n‖ ^ (-σ) :=
    (Finset.sum_filter_add_sum_filter_not F (fun n => ‖ρ n‖ < 1) _).symm
  rw [hsplit]
  have hsmall_le : ∑ n ∈ F_small, ‖ρ n‖ ^ (-σ) ≤ S₀ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    intro n hn
    exact hsmall_fin.mem_toFinset.mpr (Finset.mem_filter.mp hn).2
  -- Cover `F_large` by finitely many dyadic shells `k ∈ range K`.
  let shell (n : ℕ) : ℕ := Nat.floor (Real.log ‖ρ n‖ / Real.log 2)
  let K : ℕ := F_large.sup shell + 1
  have hcover : ∀ n ∈ F_large, shell n ∈ Finset.range K := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := shell) hn))
  have hlarge_eq : ∑ n ∈ F_large, ‖ρ n‖ ^ (-σ) =
      ∑ k ∈ Finset.range K, ∑ n ∈ F_large.filter (fun n => shell n = k), ‖ρ n‖ ^ (-σ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hcover]
  have hshell_bound : ∀ k ∈ Finset.range K,
      ∑ n ∈ F_large.filter (fun n => shell n = k), ‖ρ n‖ ^ (-σ) ≤
        (4 * C * Real.log 2) * (((k : ℝ) + 2) * q ^ k) := by
    intro k _
    let Gk := F_large.filter (fun n => shell n = k)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbounds : ∀ n ∈ Gk, (2 : ℝ) ^ k ≤ ‖ρ n‖ ∧ ‖ρ n‖ ≤ (2 : ℝ) ^ (k + 1) := by
      intro n hn
      have hnl : 1 ≤ ‖ρ n‖ := not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      have hsh : Nat.floor (Real.log ‖ρ n‖ / Real.log 2) = k := (Finset.mem_filter.mp hn).2
      have hdiv_nonneg : 0 ≤ Real.log ‖ρ n‖ / Real.log 2 :=
        div_nonneg (Real.log_nonneg hnl) hlog2_pos.le
      have hk_le : (k : ℝ) ≤ Real.log ‖ρ n‖ / Real.log 2 := by
        rw [← hsh]; exact Nat.floor_le hdiv_nonneg
      have hlt_k1 : Real.log ‖ρ n‖ / Real.log 2 < (k : ℝ) + 1 := by
        rw [← hsh]; exact Nat.lt_floor_add_one _
      have h1 : (k : ℝ) * Real.log 2 ≤ Real.log ‖ρ n‖ := (le_div_iff₀ hlog2_pos).mp hk_le
      have h2 : Real.log ‖ρ n‖ ≤ ((k : ℝ) + 1) * Real.log 2 :=
        ((div_lt_iff₀ hlog2_pos).mp hlt_k1).le
      have hρpos : 0 < ‖ρ n‖ := by linarith
      constructor
      · have hpow : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [← hpow, ← Real.exp_log hρpos]
        exact Real.exp_le_exp.mpr h1
      · have hpow : Real.exp (((k : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (k + 1) := by
          have : (((k + 1 : ℕ) : ℝ)) * Real.log 2 = ((k : ℝ) + 1) * Real.log 2 := by push_cast; ring
          rw [← this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [← hpow, ← Real.exp_log hρpos]
        exact Real.exp_le_exp.mpr h2
    have hterm_le : ∀ n ∈ Gk, ‖ρ n‖ ^ (-σ) ≤ ((2 : ℝ) ^ k) ^ (-σ) := fun n hn => by
      have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      exact Real.rpow_le_rpow_of_nonpos h2k_pos (hbounds n hn).1 (by linarith)
    have h2k1_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact one_le_pow₀ this
    have hcard_le : (Gk.card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1) + 2) :=
      hcount ((2 : ℝ) ^ (k + 1)) h2k1_ge1 Gk (fun n hn => (hbounds n hn).2)
    have hlog_le : Real.log ((2 : ℝ) ^ (k + 1) + 2) ≤ ((k : ℝ) + 2) * Real.log 2 := by
      have hle : (2 : ℝ) ^ (k + 1) + 2 ≤ (2 : ℝ) ^ (k + 2) := by
        have h2ge : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
          calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
            _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))
        have h2k2 : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := pow_succ (2 : ℝ) (k + 1)
        linarith
      calc Real.log ((2 : ℝ) ^ (k + 1) + 2)
          ≤ Real.log ((2 : ℝ) ^ (k + 2)) := Real.log_le_log (by positivity) hle
        _ = ((k + 2 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (k + 2)
        _ = ((k : ℝ) + 2) * Real.log 2 := by push_cast; ring
    have hpow_mul : (2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ (-σ) = q ^ k := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul h2pos.le,
        ← Real.rpow_add h2pos, ← Real.rpow_natCast q k]
      dsimp only [q]
      rw [← Real.rpow_mul h2pos.le]
      congr 1; ring
    calc ∑ n ∈ Gk, ‖ρ n‖ ^ (-σ)
        ≤ ∑ _n ∈ Gk, ((2 : ℝ) ^ k) ^ (-σ) := Finset.sum_le_sum hterm_le
      _ = (Gk.card : ℝ) * ((2 : ℝ) ^ k) ^ (-σ) := by simp
      _ ≤ (C * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1) + 2)) * ((2 : ℝ) ^ k) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hcard_le (Real.rpow_nonneg (by positivity) _)
      _ ≤ (C * (2 : ℝ) ^ (k + 1) * (((k : ℝ) + 2) * Real.log 2)) * ((2 : ℝ) ^ k) ^ (-σ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = (2 * C * Real.log 2) * (((k : ℝ) + 2) * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ (-σ))) := by
          rw [pow_succ]; ring
      _ = (2 * C * Real.log 2) * (((k : ℝ) + 2) * q ^ k) := by rw [hpow_mul]
      _ ≤ (4 * C * Real.log 2) * (((k : ℝ) + 2) * q ^ k) := by
          have hnn : 0 ≤ ((k : ℝ) + 2) * q ^ k := by positivity
          have hnn2 : 0 ≤ C * Real.log 2 := mul_nonneg hC hlog2_pos.le
          nlinarith
  have hlarge_le : ∑ n ∈ F_large, ‖ρ n‖ ^ (-σ) ≤ B_dyadic := by
    rw [hlarge_eq]
    calc ∑ k ∈ Finset.range K, ∑ n ∈ F_large.filter (fun n => shell n = k), ‖ρ n‖ ^ (-σ)
        ≤ ∑ k ∈ Finset.range K, (4 * C * Real.log 2) * (((k : ℝ) + 2) * q ^ k) :=
          Finset.sum_le_sum hshell_bound
      _ ≤ B_dyadic :=
          (hgeom_k.mul_left (4 * C * Real.log 2)).sum_le_tsum (Finset.range K)
            (fun k _ => mul_nonneg (mul_nonneg (by linarith) (Real.log_pos (by norm_num)).le)
              (by positivity))
  linarith

/-- Specialization to `σ = 2`: `∑' n, (‖ρ n‖ ^ 2)⁻¹` converges under order-1 zero counting. -/
theorem summable_inv_sq_of_zero_counting {ρ : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hρ_ne : ∀ n, ρ n ≠ 0)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ ≤ r) → (F.card : ℝ) ≤ C * r * Real.log (r + 2)) :
    Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) := by
  have h := summable_rpow_neg_of_zero_counting hC hρ_ne hcount (σ := 2) (by norm_num)
  refine h.congr fun n => ?_
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]

/-- For any entire function `f` of order `≤ 1` with `f 0 ≠ 0` and any injective zero enumeration
`ρ : ℕ → ℂ`, `∑' n, ‖ρ n‖ ^ (-σ)` converges for every `σ > 1`. -/
theorem order_one_zero_seq_summable_rpow_neg {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hf : HasOrderOneGrowth f A B) (hf0 : f 0 ≠ 0)
    {ρ : ℕ → ℂ} (hinj : Function.Injective ρ) (hzeros : ∀ n, f (ρ n) = 0)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖ρ n‖ ^ (-σ)) := by
  set C : ℝ := (4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2
  have hC : 0 ≤ C := div_nonneg (by linarith [le_max_right B 0, le_max_right (-Real.log ‖f 0‖) 0])
    (Real.log_pos (by norm_num)).le
  refine summable_rpow_neg_of_zero_counting hC
    (fun n h => by have hz := hzeros n; rw [h] at hz; exact hf0 hz) ?_ hσ
  intro r hr F hF
  classical
  have hcard : (F.image ρ).card = F.card := Finset.card_image_of_injective F hinj
  rw [← hcard]
  refine order_one_zero_count_le hA hf hf0 r hr (F.image ρ) ?_ ?_
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact mem_closedBall_zero_iff.mpr (hF n hn)
  · intro a ha
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp ha
    exact hzeros n

/-- In particular, for any entire function `f` of order `≤ 1` with `f 0 ≠ 0`, any injective
zero sequence satisfies `∑' n, (‖ρ n‖ ^ 2)⁻¹ < ∞`. -/
theorem order_one_zero_seq_summable_inv_sq {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hf : HasOrderOneGrowth f A B) (hf0 : f 0 ≠ 0)
    {ρ : ℕ → ℂ} (hinj : Function.Injective ρ) (hzeros : ∀ n, f (ρ n) = 0) :
    Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) := by
  have h := order_one_zero_seq_summable_rpow_neg hA hf hf0 hinj hzeros (σ := 2) (by norm_num)
  refine h.congr fun n => ?_
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]

/-! ## Section 4: Weierstrass Genus-1 Elementary Factors & Canonical Product Convergence -/

/-- Weierstrass genus-1 elementary factor `E₁(z) = (1 - z) exp(z)`. -/
def weierstrassE1 (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

@[simp]
theorem weierstrassE1_zero : weierstrassE1 0 = 1 := by
  simp [weierstrassE1]

@[simp]
theorem weierstrassE1_one : weierstrassE1 1 = 0 := by
  simp [weierstrassE1]

theorem weierstrassE1_eq_zero_iff (z : ℂ) : weierstrassE1 z = 0 ↔ z = 1 := by
  unfold weierstrassE1
  rw [mul_eq_zero, sub_eq_zero, or_iff_left (Complex.exp_ne_zero z), eq_comm]

theorem differentiable_weierstrassE1 : Differentiable ℂ weierstrassE1 :=
  ((differentiable_const 1).sub differentiable_id).mul Complex.differentiable_exp

theorem hasDerivAt_weierstrassE1 (z : ℂ) :
    HasDerivAt weierstrassE1 (-z * Complex.exp z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have h2 : HasDerivAt Complex.exp (Complex.exp z) z := Complex.hasDerivAt_exp z
  have h3 : HasDerivAt weierstrassE1 ((-1) * Complex.exp z + (1 - z) * Complex.exp z) z :=
    h1.mul h2
  convert h3 using 1
  ring

/-- Derivative of a scaled Weierstrass factor `z ↦ E₁(z / a)`. -/
theorem hasDerivAt_weierstrassE1_div {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    HasDerivAt (fun w => weierstrassE1 (w / a))
      (-(z / a ^ 2) * Complex.exp (z / a)) z := by
  have hdiv : HasDerivAt (fun w : ℂ => w / a) (1 / a) z :=
    (hasDerivAt_id z).div_const a
  have hcomp := HasDerivAt.comp z (hasDerivAt_weierstrassE1 (z / a)) hdiv
  change HasDerivAt (fun w => weierstrassE1 (w / a))
    (-(z / a) * Complex.exp (z / a) * (1 / a)) z at hcomp
  convert hcomp using 1
  field_simp [ha]

/-- Logarithmic derivative of a single genus-1 Weierstrass factor:
`deriv (fun w => E₁(w / a)) z / E₁(z / a) = 1 / (z - a) + 1 / a` for `a ≠ 0` and `z ≠ a`. -/
theorem logDeriv_weierstrassE1_div {a z : ℂ} (ha : a ≠ 0) (hza : z ≠ a) :
    deriv (fun w => weierstrassE1 (w / a)) z / weierstrassE1 (z / a) =
      1 / (z - a) + 1 / a := by
  rw [(hasDerivAt_weierstrassE1_div ha z).deriv]
  unfold weierstrassE1
  have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
  have h1sub : 1 - z / a ≠ 0 := by
    intro h
    have : z / a = 1 := (sub_eq_zero.mp h).symm
    exact hza ((div_eq_one_iff_eq ha).mp this)
  have hexp : Complex.exp (z / a) ≠ 0 := Complex.exp_ne_zero _
  field_simp [ha, hsub, h1sub, hexp]
  ring

/-- Exact principal-branch logarithm identity for `E₁(z)` on `‖z‖ ≤ 1/2`:
`Complex.log (E₁(z)) = Complex.log (1 - z) + z`. -/
theorem log_weierstrassE1_eq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    Complex.log (weierstrassE1 z) = Complex.log (1 - z) + z := by
  have hz_lt1 : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have hlog_bound : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 := by
    have h := Complex.norm_log_one_add_sub_self_le hz_lt1
    have heq1 : (1 : ℂ) + (-z) = 1 - z := by ring
    have heq2 : Complex.log (1 - z) - (-z) = Complex.log (1 - z) + z := by ring
    rw [heq1, heq2, norm_neg] at h
    have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 - ‖z‖ := by linarith
      rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hmul : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by
      gcongr
    linarith
  set w : ℂ := Complex.log (1 - z) + z
  have hw_norm : ‖w‖ ≤ 1 / 4 := by
    have hsq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg z) hz 2
    linarith
  have hw_im : -Real.pi < w.im ∧ w.im ≤ Real.pi := by
    have habs : |w.im| ≤ 1 / 4 := (Complex.abs_im_le_norm w).trans hw_norm
    have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have hle := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩
  have h1sub : 1 - z ≠ 0 := by
    intro h
    have h1 : z = 1 := (sub_eq_zero.mp h).symm
    have h2 : ‖z‖ = 1 := by rw [h1, norm_one]
    linarith
  have hexp_w : Complex.exp w = weierstrassE1 z := by
    dsimp only [w, weierstrassE1]
    rw [Complex.exp_add, Complex.exp_log h1sub]
  rw [← hexp_w, Complex.log_exp hw_im.1 hw_im.2]

/-- Sharp quadratic estimate for `log E₁(z)` on `‖z‖ ≤ 1/2`: `‖Complex.log (E₁(z))‖ ≤ ‖z‖²`. -/
theorem norm_log_weierstrassE1_le_sq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (weierstrassE1 z)‖ ≤ ‖z‖ ^ 2 := by
  rw [log_weierstrassE1_eq hz]
  have hz_lt1 : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le hz_lt1
  have heq1 : (1 : ℂ) + (-z) = 1 - z := by ring
  have heq2 : Complex.log (1 - z) - (-z) = Complex.log (1 - z) + z := by ring
  rw [heq1, heq2, norm_neg] at h
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 - ‖z‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hmul : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
  linarith

/-- Quadratic estimate `‖Complex.log (E₁(z))‖ ≤ 2 * ‖z‖²` for `‖z‖ ≤ 1/2`. -/
theorem norm_log_weierstrassE1_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (weierstrassE1 z)‖ ≤ 2 * ‖z‖ ^ 2 := by
  have h := norm_log_weierstrassE1_le_sq hz
  nlinarith [sq_nonneg ‖z‖]

private lemma norm_exp_sub_one_le_two_mul {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  have h := Complex.exp_bound hw (n := 1) (by norm_num)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_one, Nat.factorial_one, mul_one, Nat.cast_one] at h
  linarith

/-- Sharp quadratic estimate `‖E₁(z) - 1‖ ≤ 2 * ‖z‖²` for `‖z‖ ≤ 1/2`. -/
theorem norm_weierstrassE1_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassE1 z - 1‖ ≤ 2 * ‖z‖ ^ 2 := by
  have hne : weierstrassE1 z ≠ 0 := by
    intro h
    have h1 : z = 1 := (weierstrassE1_eq_zero_iff z).mp h
    have : ‖z‖ = 1 := by rw [h1, norm_one]
    linarith
  set w : ℂ := Complex.log (weierstrassE1 z)
  have hw_sq : ‖w‖ ≤ ‖z‖ ^ 2 := norm_log_weierstrassE1_le_sq hz
  have hw_le1 : ‖w‖ ≤ 1 := by
    have hsq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    linarith
  have hexp : Complex.exp w = weierstrassE1 z := Complex.exp_log hne
  rw [← hexp]
  exact (norm_exp_sub_one_le_two_mul hw_le1).trans (by linarith)

/-- For `‖z‖ ≤ 1/2`, `E₁(z)` lies in `Complex.slitPlane` (in fact `Re(E₁(z)) ≥ 1/2 > 0`). -/
theorem weierstrassE1_mem_slitPlane {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    weierstrassE1 z ∈ Complex.slitPlane := by
  have h1 : ‖weierstrassE1 z - 1‖ ≤ 1 / 2 := by
    have h2 := norm_weierstrassE1_sub_one_le hz
    have hsq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    linarith
  have hre : 0 < (weierstrassE1 z).re := by
    have habs : |(weierstrassE1 z - 1).re| ≤ 1 / 2 :=
      (Complex.abs_re_le_norm _).trans h1
    rw [Complex.sub_re, Complex.one_re] at habs
    linarith [(abs_le.mp habs).1]
  exact Complex.mem_slitPlane_iff.mpr (.inl hre)

/-- Genus-1 Weierstrass canonical product `∏' n, E₁(z / ρ n)`. -/
def weierstrassProduct (ρ : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassE1 (z / ρ n)

/-- If `∑' n, (‖ρ n‖ ^ 2)⁻¹ < ∞` and `∀ n, ρ n ≠ 0`, then `‖ρ n‖ → ∞`. -/
theorem tendsto_norm_atTop_of_summable_inv_sq {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) :
    Tendsto (fun n => ‖ρ n‖) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  set B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right M 1)
  have htend : Tendsto (fun n => (‖ρ n‖ ^ 2)⁻¹) atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, (‖ρ n‖ ^ 2)⁻¹ < (B ^ 2)⁻¹ :=
    htend.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with n hn
  have hρ_pos : 0 < ‖ρ n‖ := norm_pos_iff.mpr (hρ_ne n)
  have hsq : B ^ 2 < ‖ρ n‖ ^ 2 := by
    rwa [inv_lt_inv₀ (sq_pos_of_pos hρ_pos) (sq_pos_of_pos hB_pos)] at hn
  have hBle : B ≤ ‖ρ n‖ := by nlinarith
  exact (le_max_left M 1).trans hBle

private lemma exists_tail_norm_ge {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) (R : ℝ) :
    ∃ N : ℕ, ∀ n, N ≤ n → 2 * R ≤ ‖ρ n‖ := by
  have ht := tendsto_norm_atTop_of_summable_inv_sq hρ_ne hsum
  exact Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop (2 * R)))

private lemma hasProd_nat_of_tail {f : ℕ → ℂ} {N : ℕ} {a : ℂ}
    (htail : HasProd (fun m : ℕ => f (m + N)) a) :
    HasProd f ((∏ i ∈ Finset.range N, f i) * a) := by
  classical
  change Tendsto (fun s : Finset ℕ => ∏ m ∈ s, f (m + N)) atTop (nhds a) at htail
  change Tendsto (fun s : Finset ℕ => ∏ i ∈ s, f i) atTop (nhds ((∏ i ∈ Finset.range N, f i) * a))
  rw [Metric.tendsto_atTop] at htail ⊢
  intro ε hε
  set P : ℂ := ∏ i ∈ Finset.range N, f i
  have hP1 : 0 < ‖P‖ + 1 := by positivity
  obtain ⟨t₀, ht₀⟩ := htail (ε / (‖P‖ + 1)) (div_pos hε hP1)
  refine ⟨Finset.range N ∪ t₀.image (· + N), fun s hs => ?_⟩
  have hsubN : Finset.range N ⊆ s := Finset.union_subset_left hs
  have hsubT : t₀.image (· + N) ⊆ s := Finset.union_subset_right hs
  let t : Finset ℕ := (s \ Finset.range N).image (· - N)
  have ht_ge : t₀ ≤ t := by
    intro m hm
    refine Finset.mem_image.mpr ⟨m + N, ?_, Nat.add_sub_cancel m N⟩
    refine Finset.mem_sdiff.mpr ⟨hsubT (Finset.mem_image_of_mem _ hm), ?_⟩
    simp [Finset.mem_range]
  have hprod_split : ∏ i ∈ s, f i = P * ∏ m ∈ t, f (m + N) := by
    have hdisj : Disjoint (Finset.range N) (s \ Finset.range N) := disjoint_sdiff_self_right
    have hunion : Finset.range N ∪ (s \ Finset.range N) = s := Finset.union_sdiff_of_subset hsubN
    rw [← hunion, Finset.prod_union hdisj]
    congr 1
    have hbi : t.image (· + N) = s \ Finset.range N := by
      ext x
      simp only [t, Finset.mem_image, Finset.mem_sdiff, Finset.mem_range]
      constructor
      · rintro ⟨m, ⟨y, ⟨hys, hyN⟩, rfl⟩, rfl⟩
        have hge : N ≤ y := not_lt.mp hyN
        rw [Nat.sub_add_cancel hge]
        exact ⟨hys, hyN⟩
      · rintro ⟨hxs, hxN⟩
        have hge : N ≤ x := not_lt.mp hxN
        exact ⟨x - N, ⟨x, ⟨hxs, hxN⟩, rfl⟩, Nat.sub_add_cancel hge⟩
    rw [← hbi, Finset.prod_image]
    intro x _ y _ hxy
    exact Nat.add_right_cancel hxy
  rw [hprod_split, dist_eq_norm, ← mul_sub, norm_mul]
  have hdist := ht₀ t ht_ge
  rw [dist_eq_norm] at hdist
  calc ‖P‖ * ‖(∏ m ∈ t, f (m + N)) - a‖
      ≤ (‖P‖ + 1) * ‖(∏ m ∈ t, f (m + N)) - a‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (‖P‖ + 1) * (ε / (‖P‖ + 1)) := mul_lt_mul_of_pos_left hdist hP1
    _ = ε := mul_div_cancel₀ ε hP1.ne'

/-- Local prefix-times-exponential-tail factorization of the genus-1 Weierstrass product
on `closedBall 0 R`. -/
theorem hasProd_weierstrassE1_prefix_mul_exp_tail {ρ : ℕ → ℂ} (_hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : ∀ n, N ≤ n → 2 * R ≤ ‖ρ n‖)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    HasProd (fun n => weierstrassE1 (z / ρ n))
      ((∏ i ∈ Finset.range N, weierstrassE1 (z / ρ i)) *
        Complex.exp (∑' m : ℕ, Complex.log (weierstrassE1 (z / ρ (m + N))))) := by
  have hz_norm : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hsmall : ∀ m : ℕ, ‖z / ρ (m + N)‖ ≤ 1 / 2 := fun m => by
    have hge : 2 * R ≤ ‖ρ (m + N)‖ := hN (m + N) (Nat.le_add_left N m)
    have hρ_pos : 0 < ‖ρ (m + N)‖ := by linarith
    rw [norm_div, div_le_iff₀ hρ_pos]
    linarith
  have hlog_summ : Summable (fun m : ℕ => Complex.log (weierstrassE1 (z / ρ (m + N)))) := by
    have hdom : Summable (fun m : ℕ => R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹) :=
      ((summable_nat_add_iff N).mpr hsum).mul_left (R ^ 2)
    refine Summable.of_norm_bounded hdom fun m => ?_
    calc ‖Complex.log (weierstrassE1 (z / ρ (m + N)))‖
        ≤ ‖z / ρ (m + N)‖ ^ 2 := norm_log_weierstrassE1_le_sq (hsmall m)
      _ = ‖z‖ ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ := by rw [norm_div, div_pow, div_eq_mul_inv]
      _ ≤ R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hz_norm 2) (by positivity)
  have htail_hasProd : HasProd (fun m : ℕ => weierstrassE1 (z / ρ (m + N)))
      (Complex.exp (∑' m : ℕ, Complex.log (weierstrassE1 (z / ρ (m + N))))) := by
    unfold HasProd
    have htend := (Complex.continuous_exp.tendsto _).comp hlog_summ.hasSum
    refine htend.congr fun s => ?_
    change Complex.exp (∑ m ∈ s, Complex.log (weierstrassE1 (z / ρ (m + N)))) =
      ∏ m ∈ s, weierstrassE1 (z / ρ (m + N))
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun m _ => Complex.exp_log ?_
    exact Complex.slitPlane_ne_zero (weierstrassE1_mem_slitPlane (hsmall m))
  exact hasProd_nat_of_tail htail_hasProd

/-- **Unconditional Convergence of the Genus-1 Weierstrass Canonical Product**:
for every sequence `ρ : ℕ → ℂ` with `ρ n ≠ 0` and `∑' n, (‖ρ n‖ ^ 2)⁻¹ < ∞`, the infinite product
`∏' n, (1 - z / ρ n) exp(z / ρ n)` converges unconditionally for every `z : ℂ`! -/
theorem multipliable_weierstrassE1 {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) (z : ℂ) :
    Multipliable (fun n => weierstrassE1 (z / ρ n)) := by
  set R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨N, hN⟩ := exists_tail_norm_ge hρ_ne hsum R
  have hz : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
  exact ⟨_, hasProd_weierstrassE1_prefix_mul_exp_tail hρ_ne hsum hR hN hz⟩

/-- Exact local factorization of `weierstrassProduct ρ` on `closedBall 0 R`. -/
theorem weierstrassProduct_eq_prefix_mul_exp_tail {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : ∀ n, N ≤ n → 2 * R ≤ ‖ρ n‖)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    weierstrassProduct ρ z =
      (∏ i ∈ Finset.range N, weierstrassE1 (z / ρ i)) *
        Complex.exp (∑' m : ℕ, Complex.log (weierstrassE1 (z / ρ (m + N)))) :=
  (hasProd_weierstrassE1_prefix_mul_exp_tail hρ_ne hsum hR hN hz).tprod_eq

/-- Exact zero-set characterization of the genus-1 Weierstrass product:
`weierstrassProduct ρ z = 0 ↔ ∃ n, z = ρ n`. -/
theorem weierstrassProduct_eq_zero_iff {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) (z : ℂ) :
    weierstrassProduct ρ z = 0 ↔ ∃ n : ℕ, z = ρ n := by
  set R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨N, hN⟩ := exists_tail_norm_ge hρ_ne hsum R
  have hz : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
  rw [weierstrassProduct_eq_prefix_mul_exp_tail hρ_ne hsum hR hN hz,
    mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    rw [weierstrassE1_eq_zero_iff, div_eq_one_iff_eq (hρ_ne i)] at hi
    exact ⟨i, hi⟩
  · rintro ⟨n, rfl⟩
    have hn_lt : n < N := by
      by_contra hge
      have h1 := hN n (not_lt.mp hge)
      dsimp only [R] at h1
      linarith [norm_nonneg (ρ n)]
    refine ⟨n, Finset.mem_range.mpr hn_lt, ?_⟩
    rw [div_self (hρ_ne n), weierstrassE1_one]

/-- **Entireness of the Genus-1 Weierstrass Canonical Product**:
`weierstrassProduct ρ` is differentiable on all of `ℂ`. -/
theorem differentiable_weierstrassProduct {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) :
    Differentiable ℂ (weierstrassProduct ρ) := by
  intro z₀
  set R : ℝ := ‖z₀‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨N, hN⟩ := exists_tail_norm_ge hρ_ne hsum R
  let U : Set ℂ := ball (0 : ℂ) R
  have hz₀U : z₀ ∈ U := mem_ball_zero_iff.mpr (by linarith)
  let P : ℂ → ℂ := fun w => ∏ i ∈ Finset.range N, weierstrassE1 (w / ρ i)
  let F : ℕ → ℂ → ℂ := fun m w => Complex.log (weierstrassE1 (w / ρ (m + N)))
  let u : ℕ → ℝ := fun m => R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹
  have hu : Summable u := ((summable_nat_add_iff N).mpr hsum).mul_left (R ^ 2)
  have hsmall : ∀ m : ℕ, ∀ w ∈ U, ‖w / ρ (m + N)‖ ≤ 1 / 2 := fun m w hw => by
    have hwn : ‖w‖ < R := mem_ball_zero_iff.mp hw
    have hge : 2 * R ≤ ‖ρ (m + N)‖ := hN (m + N) (Nat.le_add_left N m)
    have hρ_pos : 0 < ‖ρ (m + N)‖ := by linarith
    rw [norm_div, div_le_iff₀ hρ_pos]
    linarith
  have hF_diff : ∀ m : ℕ, DifferentiableOn ℂ (F m) U := fun m => by
    have hbase : DifferentiableOn ℂ (fun w => weierstrassE1 (w / ρ (m + N))) U :=
      (differentiable_weierstrassE1.comp (differentiable_id.div_const _)).differentiableOn
    exact hbase.clog fun w hw => weierstrassE1_mem_slitPlane (hsmall m w hw)
  have hF_bound : ∀ m : ℕ, ∀ w ∈ U, ‖F m w‖ ≤ u m := fun m w hw => by
    have hwn : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
    calc ‖F m w‖
        ≤ ‖w / ρ (m + N)‖ ^ 2 := norm_log_weierstrassE1_le_sq (hsmall m w hw)
      _ = ‖w‖ ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ := by rw [norm_div, div_pow, div_eq_mul_inv]
      _ ≤ R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg w) hwn 2) (by positivity)
  have htail_diff : DifferentiableOn ℂ (fun w => ∑' m : ℕ, F m w) U :=
    Complex.differentiableOn_tsum_of_summable_norm hu hF_diff isOpen_ball hF_bound
  have hP_diff : DifferentiableOn ℂ P U := by
    have hdiff : ∀ k : ℕ, Differentiable ℂ (fun w => ∏ i ∈ Finset.range k, weierstrassE1 (w / ρ i)) := by
      intro k
      induction k with
      | zero => simp [differentiable_const]
      | succ k ih =>
        have hfun : (fun w => ∏ i ∈ Finset.range (k + 1), weierstrassE1 (w / ρ i)) =
            fun w => (∏ i ∈ Finset.range k, weierstrassE1 (w / ρ i)) * weierstrassE1 (w / ρ k) := by
          funext w; exact Finset.prod_range_succ _ _
        rw [hfun]
        exact ih.mul (differentiable_weierstrassE1.comp (differentiable_id.div_const _))
    exact (hdiff N).differentiableOn
  have hprod_diff : DifferentiableOn ℂ (fun w => P w * Complex.exp (∑' m : ℕ, F m w)) U :=
    hP_diff.mul htail_diff.cexp
  have heq : weierstrassProduct ρ =ᶠ[nhds z₀] fun w => P w * Complex.exp (∑' m : ℕ, F m w) := by
    filter_upwards [isOpen_ball.mem_nhds hz₀U] with w hw
    exact weierstrassProduct_eq_prefix_mul_exp_tail hρ_ne hsum hR hN (ball_subset_closedBall hw)
  exact (hprod_diff.differentiableAt (isOpen_ball.mem_nhds hz₀U)).congr_of_eventuallyEq heq

private lemma hasDerivAt_finset_prod_weierstrassE1 {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (z : ℂ) (N : ℕ) (hzn : ∀ i < N, z ≠ ρ i) :
    HasDerivAt (fun w => ∏ i ∈ Finset.range N, weierstrassE1 (w / ρ i))
      ((∏ i ∈ Finset.range N, weierstrassE1 (z / ρ i)) *
        ∑ i ∈ Finset.range N, (1 / (z - ρ i) + 1 / ρ i)) z := by
  induction N with
  | zero =>
    simpa using hasDerivAt_const z (1 : ℂ)
  | succ k ih =>
    have hih := ih (fun i hi => hzn i (Nat.lt_succ_of_lt hi))
    have hzk : z ≠ ρ k := hzn k (Nat.lt_succ_self k)
    have hf_k : HasDerivAt (fun w => weierstrassE1 (w / ρ k))
        (weierstrassE1 (z / ρ k) * (1 / (z - ρ k) + 1 / ρ k)) z := by
      have hd := hasDerivAt_weierstrassE1_div (hρ_ne k) z
      have hld := logDeriv_weierstrassE1_div (hρ_ne k) hzk
      have hEk_ne : weierstrassE1 (z / ρ k) ≠ 0 := by
        rw [ne_eq, weierstrassE1_eq_zero_iff, div_eq_one_iff_eq (hρ_ne k)]
        exact hzk
      rw [hd.deriv] at hld
      have hval : -(z / ρ k ^ 2) * Complex.exp (z / ρ k) =
          weierstrassE1 (z / ρ k) * (1 / (z - ρ k) + 1 / ρ k) := by
        rw [← hld, mul_div_cancel₀ _ hEk_ne]
      rwa [hval] at hd
    have hmul : HasDerivAt
        (fun w => (∏ i ∈ Finset.range k, weierstrassE1 (w / ρ i)) * weierstrassE1 (w / ρ k))
        (((∏ i ∈ Finset.range k, weierstrassE1 (z / ρ i)) *
            ∑ i ∈ Finset.range k, (1 / (z - ρ i) + 1 / ρ i)) * weierstrassE1 (z / ρ k) +
          (∏ i ∈ Finset.range k, weierstrassE1 (z / ρ i)) *
            (weierstrassE1 (z / ρ k) * (1 / (z - ρ k) + 1 / ρ k))) z :=
      hih.mul hf_k
    have hfun : (fun w => (∏ i ∈ Finset.range k, weierstrassE1 (w / ρ i)) *
        weierstrassE1 (w / ρ k)) = fun w => ∏ i ∈ Finset.range (k + 1), weierstrassE1 (w / ρ i) := by
      funext w; rw [Finset.prod_range_succ]
    rw [hfun] at hmul
    convert hmul using 1
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    ring

/-- **Term-by-Term Logarithmic Derivative of the Genus-1 Weierstrass Product**:
for every `z : ℂ` with `∀ n, z ≠ ρ n`, the series `∑_n (1 / (z - ρ n) + 1 / ρ n)` converges
unconditionally to `deriv (weierstrassProduct ρ) z / weierstrassProduct ρ z`. -/
theorem hasSum_logDeriv_weierstrassProduct {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {z : ℂ} (hz : ∀ n, z ≠ ρ n) :
    HasSum (fun n => 1 / (z - ρ n) + 1 / ρ n)
      (deriv (weierstrassProduct ρ) z / weierstrassProduct ρ z) := by
  set R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨N, hN⟩ := exists_tail_norm_ge hρ_ne hsum R
  let U : Set ℂ := ball (0 : ℂ) R
  have hzU : z ∈ U := mem_ball_zero_iff.mpr (by linarith)
  let P : ℂ → ℂ := fun w => ∏ i ∈ Finset.range N, weierstrassE1 (w / ρ i)
  let F : ℕ → ℂ → ℂ := fun m w => Complex.log (weierstrassE1 (w / ρ (m + N)))
  let L : ℂ → ℂ := fun w => ∑' m : ℕ, F m w
  let u : ℕ → ℝ := fun m => R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹
  have hu : Summable u := ((summable_nat_add_iff N).mpr hsum).mul_left (R ^ 2)
  have hsmall : ∀ m : ℕ, ∀ w ∈ U, ‖w / ρ (m + N)‖ ≤ 1 / 2 := fun m w hw => by
    have hwn : ‖w‖ < R := mem_ball_zero_iff.mp hw
    have hge : 2 * R ≤ ‖ρ (m + N)‖ := hN (m + N) (Nat.le_add_left N m)
    have hρ_pos : 0 < ‖ρ (m + N)‖ := by linarith
    rw [norm_div, div_le_iff₀ hρ_pos]
    linarith
  have hF_diff : ∀ m : ℕ, DifferentiableOn ℂ (F m) U := fun m => by
    have hbase : DifferentiableOn ℂ (fun w => weierstrassE1 (w / ρ (m + N))) U :=
      (differentiable_weierstrassE1.comp (differentiable_id.div_const _)).differentiableOn
    exact hbase.clog fun w hw => weierstrassE1_mem_slitPlane (hsmall m w hw)
  have hF_bound : ∀ m : ℕ, ∀ w ∈ U, ‖F m w‖ ≤ u m := fun m w hw => by
    have hwn : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
    calc ‖F m w‖
        ≤ ‖w / ρ (m + N)‖ ^ 2 := norm_log_weierstrassE1_le_sq (hsmall m w hw)
      _ = ‖w‖ ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ := by rw [norm_div, div_pow, div_eq_mul_inv]
      _ ≤ R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg w) hwn 2) (by positivity)
  have hL_diff : DifferentiableAt ℂ L z :=
    (Complex.differentiableOn_tsum_of_summable_norm hu hF_diff isOpen_ball hF_bound).differentiableAt
      (isOpen_ball.mem_nhds hzU)
  have hL_hasSum : HasSum (fun m : ℕ => deriv (F m) z) (deriv L z) :=
    Complex.hasSum_deriv_of_summable_norm hu hF_diff isOpen_ball hF_bound hzU
  have hderiv_Fm : ∀ m : ℕ, deriv (F m) z = 1 / (z - ρ (m + N)) + 1 / ρ (m + N) := fun m => by
    have hbase : DifferentiableAt ℂ (fun w => weierstrassE1 (w / ρ (m + N))) z :=
      (differentiable_weierstrassE1.comp (differentiable_id.div_const _)) z
    have hslit : weierstrassE1 (z / ρ (m + N)) ∈ Complex.slitPlane :=
      weierstrassE1_mem_slitPlane (hsmall m z hzU)
    have hcomp : deriv (F m) z =
        deriv (fun w => weierstrassE1 (w / ρ (m + N))) z / weierstrassE1 (z / ρ (m + N)) := by
      change deriv (Complex.log ∘ fun w => weierstrassE1 (w / ρ (m + N))) z = _
      rw [Complex.deriv_log_comp_eq_logDeriv hbase hslit, logDeriv_apply]
    rw [hcomp, logDeriv_weierstrassE1_div (hρ_ne (m + N)) (hz (m + N))]
  have htail_hasSum : HasSum (fun m : ℕ => 1 / (z - ρ (m + N)) + 1 / ρ (m + N)) (deriv L z) :=
    hL_hasSum.congr_fun (fun m => (hderiv_Fm m).symm)
  have hP_deriv : HasDerivAt P (P z * ∑ i ∈ Finset.range N, (1 / (z - ρ i) + 1 / ρ i)) z :=
    hasDerivAt_finset_prod_weierstrassE1 hρ_ne z N (fun i _ => hz i)
  have hexpL_deriv : HasDerivAt (fun w => Complex.exp (L w)) (Complex.exp (L z) * deriv L z) z := by
    simpa [mul_comm] using hL_diff.hasDerivAt.cexp
  have hprod_deriv : HasDerivAt (fun w => P w * Complex.exp (L w))
      ((P z * ∑ i ∈ Finset.range N, (1 / (z - ρ i) + 1 / ρ i)) * Complex.exp (L z) +
        P z * (Complex.exp (L z) * deriv L z)) z :=
    hP_deriv.mul hexpL_deriv
  have heq_ev : weierstrassProduct ρ =ᶠ[nhds z] fun w => P w * Complex.exp (L w) := by
    filter_upwards [isOpen_ball.mem_nhds hzU] with w hw
    exact weierstrassProduct_eq_prefix_mul_exp_tail hρ_ne hsum hR hN (ball_subset_closedBall hw)
  have hW_deriv : deriv (weierstrassProduct ρ) z =
      (P z * Complex.exp (L z)) *
        ((∑ i ∈ Finset.range N, (1 / (z - ρ i) + 1 / ρ i)) + deriv L z) := by
    rw [heq_ev.deriv_eq, hprod_deriv.deriv]
    ring
  have hW_val : weierstrassProduct ρ z = P z * Complex.exp (L z) :=
    weierstrassProduct_eq_prefix_mul_exp_tail hρ_ne hsum hR hN (ball_subset_closedBall hzU)
  have hW_ne : weierstrassProduct ρ z ≠ 0 := by
    rw [ne_eq, weierstrassProduct_eq_zero_iff hρ_ne hsum]
    push Not
    exact hz
  have hdiv_eq : deriv (weierstrassProduct ρ) z / weierstrassProduct ρ z =
      (∑ i ∈ Finset.range N, (1 / (z - ρ i) + 1 / ρ i)) + deriv L z := by
    rw [hW_deriv, ← hW_val, mul_div_cancel_left₀ _ hW_ne]
  rw [hdiv_eq, ← hasSum_nat_add_iff' N]
  simpa [add_sub_cancel_left] using htail_hasSum

/-- Summability of the genus-1 Hadamard partial-fraction series `∑_n (1 / (z - ρ n) + 1 / ρ n)`. -/
theorem summable_hadamard_term {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {z : ℂ} (hz : ∀ n, z ≠ ρ n) :
    Summable (fun n => 1 / (z - ρ n) + 1 / ρ n) :=
  ⟨_, hasSum_logDeriv_weierstrassProduct hρ_ne hsum hz⟩

/-- Exact `tsum` formula for the logarithmic derivative of the genus-1 Weierstrass product. -/
theorem logDeriv_weierstrassProduct_eq_tsum {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {z : ℂ} (hz : ∀ n, z ≠ ρ n) :
    deriv (weierstrassProduct ρ) z / weierstrassProduct ρ z =
      ∑' n : ℕ, (1 / (z - ρ n) + 1 / ρ n) :=
  (hasSum_logDeriv_weierstrassProduct hρ_ne hsum hz).tsum_eq.symm

/-- Exact logarithmic derivative of a full genus-1 Hadamard factorization
`ξ(z) = C * exp(B * z) * ∏' n, E₁(z / ρ n)` (`C ≠ 0`):
`ξ'(z) / ξ(z) = B + ∑' n, (1 / (z - ρ n) + 1 / ρ n)`. -/
theorem hadamard_canonical_logDeriv_eq {C B : ℂ} (hC : C ≠ 0) {ρ : ℕ → ℂ}
    (hρ_ne : ∀ n, ρ n ≠ 0) (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {z : ℂ} (hz : ∀ n, z ≠ ρ n) :
    deriv (fun w => C * Complex.exp (B * w) * weierstrassProduct ρ w) z /
        (C * Complex.exp (B * z) * weierstrassProduct ρ z) =
      B + ∑' n : ℕ, (1 / (z - ρ n) + 1 / ρ n) := by
  have hW_diff : DifferentiableAt ℂ (weierstrassProduct ρ) z :=
    differentiable_weierstrassProduct hρ_ne hsum z
  have hW_ne : weierstrassProduct ρ z ≠ 0 := by
    rw [ne_eq, weierstrassProduct_eq_zero_iff hρ_ne hsum]
    push Not
    exact hz
  have hexp_deriv : HasDerivAt (fun w => C * Complex.exp (B * w))
      (C * (Complex.exp (B * z) * B)) z := by
    have h1 : HasDerivAt (fun w : ℂ => B * w) B z := by
      simpa using (hasDerivAt_id z).const_mul B
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (B * w)) (Complex.exp (B * z) * B) z := by
      simpa [mul_comm] using h1.cexp
    exact h2.const_mul C
  have hfull : HasDerivAt (fun w => C * Complex.exp (B * w) * weierstrassProduct ρ w)
      (C * (Complex.exp (B * z) * B) * weierstrassProduct ρ z +
        C * Complex.exp (B * z) * deriv (weierstrassProduct ρ) z) z :=
    hexp_deriv.mul hW_diff.hasDerivAt
  rw [hfull.deriv, ← logDeriv_weierstrassProduct_eq_tsum hρ_ne hsum hz]
  have hexp_ne : Complex.exp (B * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp [hC, hexp_ne, hW_ne]

/-! ## Section 5: Critical-Strip Positivity, Davenport's Identity & Principal-Character Euler Bound -/

/-- Exact real-part formula for `1 / (s - ρ)`. -/
theorem re_inv_sub_eq (s ρ : ℂ) :
    (1 / (s - ρ)).re = (s.re - ρ.re) / ((s.re - ρ.re) ^ 2 + (s.im - ρ.im) ^ 2) := by
  have hns : Complex.normSq (s - ρ) = (s.re - ρ.re) ^ 2 + (s.im - ρ.im) ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  rw [one_div, Complex.inv_re, Complex.sub_re, hns]

/-- **Exact Real-Part Positivity** for `ρ.re < s.re`: `0 < Re(1 / (s - ρ))`. -/
theorem re_inv_sub_pos {s ρ : ℂ} (h : ρ.re < s.re) :
    0 < (1 / (s - ρ)).re := by
  rw [re_inv_sub_eq]
  have hpos : 0 < s.re - ρ.re := sub_pos.mpr h
  exact div_pos hpos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hpos) (sq_nonneg _))

/-- **Critical-Strip Real-Part Positivity**: for `0 < ρ.re < 1` and `1 < s.re`,
`0 < Re(1 / (s - ρ))`. -/
theorem re_inv_sub_pos_of_strip {s ρ : ℂ} (_h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hs : 1 < s.re) :
    0 < (1 / (s - ρ)).re :=
  re_inv_sub_pos (h1.trans hs)

/-- **Symmetric Critical-Strip Pair Positivity**: for `0 < ρ.re < 1` and `1 < s.re`,
`0 < Re(1 / (s - ρ) + 1 / (s - (1 - conj ρ)))`. -/
theorem re_inv_sub_add_symm_pos {s ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hs : 1 < s.re) :
    0 < (1 / (s - ρ) + 1 / (s - (1 - starRingEnd ℂ ρ))).re := by
  rw [Complex.add_re]
  have hp1 : 0 < (1 / (s - ρ)).re := re_inv_sub_pos (h1.trans hs)
  have hsymm_re : (1 - starRingEnd ℂ ρ).re < s.re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hp2 : 0 < (1 / (s - (1 - starRingEnd ℂ ρ))).re := re_inv_sub_pos hsymm_re
  linarith

/-- Non-negativity form of symmetric critical-strip pair positivity:
`0 ≤ Re(1 / (s - ρ) + 1 / (s - (1 - conj ρ)))`. -/
theorem re_inv_sub_add_symm_nonneg {s ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hs : 1 < s.re) :
    0 ≤ (1 / (s - ρ) + 1 / (s - (1 - starRingEnd ℂ ρ))).re :=
  (re_inv_sub_add_symm_pos h0 h1 hs).le

/-- For any critical-strip zero `0 < ρ.re`, `0 < Re(1 / ρ)`. -/
theorem re_inv_zero_pos {ρ : ℂ} (h0 : 0 < ρ.re) : 0 < (1 / ρ).re := by
  rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hρ_ne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
  exact div_pos h0 (sq_pos_of_pos (norm_pos_iff.mpr hρ_ne))

/-- Upper bound `Re(1 / ρ) ≤ (‖ρ‖ ^ 2)⁻¹` for `0 < ρ.re < 1`. -/
theorem re_inv_zero_le_inv_norm_sq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (1 / ρ).re ≤ (‖ρ‖ ^ 2)⁻¹ := by
  rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, div_eq_mul_inv]
  have hρ_ne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
  have hpos : 0 ≤ (‖ρ‖ ^ 2)⁻¹ := by positivity
  calc ρ.re * (‖ρ‖ ^ 2)⁻¹ ≤ 1 * (‖ρ‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1.le hpos
    _ = (‖ρ‖ ^ 2)⁻¹ := one_mul _

/-- Each Hadamard partial-fraction term satisfies `Re(1 / (s - ρ)) < Re(1 / (s - ρ) + 1 / ρ)`
for `0 < ρ.re` and `1 < s.re`. -/
theorem re_inv_sub_lt_re_hadamard_term {s ρ : ℂ} (h0 : 0 < ρ.re) :
    (1 / (s - ρ)).re < (1 / (s - ρ) + 1 / ρ).re := by
  rw [Complex.add_re]
  linarith [re_inv_zero_pos h0]

/-- Absolute summability of `n ↦ Re(1 / ρ n)` for critical-strip zeros with `∑ ‖ρ n‖⁻² < ∞`. -/
theorem summable_re_inv_of_strip {ρ : ℕ → ℂ} (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) :
    Summable (fun n => (1 / ρ n).re) :=
  Summable.of_nonneg_of_le (fun n => (re_inv_zero_pos (hstrip n).1).le)
    (fun n => re_inv_zero_le_inv_norm_sq (hstrip n).1 (hstrip n).2) hsum

/-- Absolute summability of `n ↦ Re(1 / (s - ρ n))` for critical-strip zeros with `∑ ‖ρ n‖⁻² < ∞`
and any `s : ℂ` with `∀ n, s ≠ ρ n` (in particular any `s` with `s.re > 1` or `s.re < 0`). -/
theorem summable_re_inv_sub_of_strip {ρ : ℕ → ℂ} (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) {s : ℂ} (hs : ∀ n, s ≠ ρ n) :
    Summable (fun n => (1 / (s - ρ n)).re) := by
  have hρ_ne : ∀ n, ρ n ≠ 0 := fun n h => by
    have := (hstrip n).1; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
  obtain ⟨N, hN⟩ := exists_tail_norm_ge hρ_ne hsum ‖s‖
  rw [← summable_nat_add_iff N]
  have hdom : Summable (fun m : ℕ => (4 * (|s.re| + 1)) * (‖ρ (m + N)‖ ^ 2)⁻¹) :=
    ((summable_nat_add_iff N).mpr hsum).mul_left (4 * (|s.re| + 1))
  refine Summable.of_norm_bounded hdom fun m => ?_
  have hge : 2 * ‖s‖ ≤ ‖ρ (m + N)‖ := hN (m + N) (Nat.le_add_left N m)
  have hsub_ge : ‖ρ (m + N)‖ / 2 ≤ ‖s - ρ (m + N)‖ := by
    have h1 : ‖ρ (m + N)‖ - ‖s‖ ≤ ‖ρ (m + N) - s‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    linarith
  have hρ_pos : 0 < ‖ρ (m + N)‖ := norm_pos_iff.mpr (hρ_ne (m + N))
  have hsub_pos : 0 < ‖s - ρ (m + N)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hs (m + N)))
  have hsq_ge : ‖ρ (m + N)‖ ^ 2 / 4 ≤ ‖s - ρ (m + N)‖ ^ 2 := by nlinarith
  have hnum_le : |s.re - (ρ (m + N)).re| ≤ |s.re| + 1 := by
    have h1 : |(ρ (m + N)).re| ≤ 1 := by
      rw [abs_of_pos (hstrip (m + N)).1]; exact (hstrip (m + N)).2.le
    calc |s.re - (ρ (m + N)).re|
        ≤ |s.re| + |(ρ (m + N)).re| := abs_sub _ _
      _ ≤ |s.re| + 1 := by linarith
  have hre_eq : (1 / (s - ρ (m + N))).re = (s.re - (ρ (m + N)).re) / ‖s - ρ (m + N)‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, Complex.normSq_eq_norm_sq]
  rw [Real.norm_eq_abs, hre_eq, abs_div, abs_of_pos (sq_pos_of_pos hsub_pos)]
  calc |s.re - (ρ (m + N)).re| / ‖s - ρ (m + N)‖ ^ 2
      ≤ (|s.re| + 1) / (‖ρ (m + N)‖ ^ 2 / 4) :=
        div_le_div₀ (by positivity) hnum_le (by positivity) hsq_ge
    _ = 4 * (|s.re| + 1) * (‖ρ (m + N)‖ ^ 2)⁻¹ := by field_simp [hρ_pos.ne']

/-- Exact real-part splitting of the genus-1 Hadamard partial-fraction sum:
`Re(∑' n, (1 / (s - ρ n) + 1 / ρ n)) = (∑' n, Re(1 / (s - ρ n))) + (∑' n, Re(1 / ρ n))`. -/
theorem re_tsum_hadamard_term_eq {ρ : ℕ → ℂ} (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) {s : ℂ} (hs : ∀ n, s ≠ ρ n) :
    (∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n)).re =
      (∑' n : ℕ, (1 / (s - ρ n)).re) + ∑' n : ℕ, (1 / ρ n).re := by
  have hρ_ne : ∀ n, ρ n ≠ 0 := fun n h => by
    have := (hstrip n).1; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
  have hsumm_c : Summable (fun n => 1 / (s - ρ n) + 1 / ρ n) :=
    summable_hadamard_term hρ_ne hsum hs
  have hre_tsum : (∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n)).re =
      ∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n).re := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hsumm_c
  rw [hre_tsum]
  have h1 := summable_re_inv_sub_of_strip hstrip hsum hs
  have h2 := summable_re_inv_of_strip hstrip hsum
  simp_rw [Complex.add_re]
  exact h1.tsum_add h2

private lemma re_inv_sub_functional_symm (s ρ : ℂ) :
    (1 / ((1 - starRingEnd ℂ s) - (1 - starRingEnd ℂ ρ))).re = -(1 / (s - ρ)).re := by
  have hsub : (1 - starRingEnd ℂ s) - (1 - starRingEnd ℂ ρ) = -(starRingEnd ℂ (s - ρ)) := by
    rw [map_sub]; ring
  rw [hsub, div_neg, Complex.neg_re, one_div, ← map_inv₀, Complex.conj_re, ← one_div]

/-- **Davenport's Real-Part Cancellation Identity (`Re(B) = -∑_ρ Re(1 / ρ)`)**:
if `f(s) = B + ∑' n, (1 / (s - ρ n) + 1 / ρ n)` has critical-strip zeros invariant under the
functional-equation involution `ρ (τ n) = 1 - conj (ρ n)` (`τ : Equiv.Perm ℕ`) and satisfies
real-part antisymmetry `(f (1 - conj s)).re = -(f s).re` at some point `s` with `1 < s.re`,
then `B.re = -(∑' n, (1 / ρ n).re)` AND `(f s).re = ∑' n, (1 / (s - ρ n)).re`! -/
theorem davenport_re_B_eq_neg_tsum_re_inv {ρ : ℕ → ℂ} (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    (τ : Equiv.Perm ℕ) (hτ : ∀ n, ρ (τ n) = 1 - starRingEnd ℂ (ρ n))
    {B : ℂ} {s : ℂ} (hs : 1 < s.re)
    (hanti : (B + ∑' n : ℕ, (1 / ((1 - starRingEnd ℂ s) - ρ n) + 1 / ρ n)).re =
      -(B + ∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n)).re) :
    B.re = -(∑' n : ℕ, (1 / ρ n).re) ∧
      (B + ∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n)).re = ∑' n : ℕ, (1 / (s - ρ n)).re := by
  have hs_ne : ∀ n, s ≠ ρ n := fun n h => by
    have h1 := (hstrip n).2; rw [← h] at h1; linarith
  have hs'_ne : ∀ n, 1 - starRingEnd ℂ s ≠ ρ n := fun n h => by
    have h0 := (hstrip n).1
    have hre : (1 - starRingEnd ℂ s).re = 1 - s.re := by simp
    rw [← h, hre] at h0
    linarith
  have hre1 : (B + ∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n)).re =
      B.re + (∑' n : ℕ, (1 / (s - ρ n)).re) + ∑' n : ℕ, (1 / ρ n).re := by
    rw [Complex.add_re, re_tsum_hadamard_term_eq hstrip hsum hs_ne]; ring
  have hre2 : (B + ∑' n : ℕ, (1 / ((1 - starRingEnd ℂ s) - ρ n) + 1 / ρ n)).re =
      B.re + (∑' n : ℕ, (1 / ((1 - starRingEnd ℂ s) - ρ n)).re) + ∑' n : ℕ, (1 / ρ n).re := by
    rw [Complex.add_re, re_tsum_hadamard_term_eq hstrip hsum hs'_ne]; ring
  have hcancel : (∑' n : ℕ, (1 / ((1 - starRingEnd ℂ s) - ρ n)).re) =
      -(∑' n : ℕ, (1 / (s - ρ n)).re) := by
    rw [← Equiv.tsum_eq τ (fun n => (1 / ((1 - starRingEnd ℂ s) - ρ n)).re)]
    simp_rw [hτ, re_inv_sub_functional_symm, tsum_neg]
  rw [hre1, hre2, hcancel] at hanti
  have hB : B.re = -(∑' n : ℕ, (1 / ρ n).re) := by linarith
  refine ⟨hB, ?_⟩
  rw [hre1, hB]
  ring

/-- **General Hadamard Partial-Fraction Upper Bound** (dropping all zeros outside any `F : Finset ℕ`):
for `1 < s.re` and critical-strip zeros `ρ` with `∑ ‖ρ n‖⁻² < ∞`, if
`f s = P s - B₀ - ∑' n, (1 / (s - ρ n) + 1 / ρ n) + E s` and
`-(B₀.re + ∑' n, (1 / ρ n).re) + (E s).re ≤ M`, then for EVERY finite set `F : Finset ℕ`:
`(f s).re ≤ (P s).re + M - ∑ n ∈ F, (1 / (s - ρ n)).re`. -/
theorem re_le_sub_finset_of_hadamard_partialFraction
    {ρ : ℕ → ℂ} (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹))
    {f P E : ℂ → ℂ} {B₀ : ℂ} {s : ℂ} (hs : 1 < s.re)
    (hrep : f s = P s - B₀ - ∑' n : ℕ, (1 / (s - ρ n) + 1 / ρ n) + E s)
    {M : ℝ} (hM : -(B₀.re + ∑' n : ℕ, (1 / ρ n).re) + (E s).re ≤ M)
    (F : Finset ℕ) :
    (f s).re ≤ (P s).re + M - ∑ n ∈ F, (1 / (s - ρ n)).re := by
  have hs_ne : ∀ n, s ≠ ρ n := fun n h => by
    have h1 := (hstrip n).2; rw [← h] at h1; linarith
  have hre : (f s).re = (P s).re - B₀.re -
      ((∑' n : ℕ, (1 / (s - ρ n)).re) + ∑' n : ℕ, (1 / ρ n).re) + (E s).re := by
    rw [hrep]
    simp only [Complex.add_re, Complex.sub_re]
    rw [re_tsum_hadamard_term_eq hstrip hsum hs_ne]
  have hsumm := summable_re_inv_sub_of_strip hstrip hsum hs_ne
  have hF_le : ∑ n ∈ F, (1 / (s - ρ n)).re ≤ ∑' n : ℕ, (1 / (s - ρ n)).re :=
    hsumm.sum_le_tsum F (fun n _ => (re_inv_sub_pos_of_strip (hstrip n).1 (hstrip n).2 hs).le)
  linarith

/-- **Unconditional Principal-Character Euler-Factor Bound**:
for EVERY modulus `q ≥ 1` (`[NeZero q]`) and EVERY `s : ℂ` with `1 < s.re`,
`‖-L'/L(1_q, s) - (-ζ'/ζ(s))‖ ≤ Real.log q`. -/
theorem norm_negLogDerivL_one_sub_negLogDerivZeta_le_log {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    ‖Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s -
        Stage3ZeroFreeRegion.negLogDerivZeta s‖ ≤ Real.log (q : ℝ) := by
  classical
  rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) hs,
      Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs]
  have hsum1 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) s :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold LSeries
  rw [← Summable.tsum_sub hsum1 hsumZ]
  set g : ℕ → ℝ := fun n =>
    if ¬ Nat.Coprime n q then Λ n / (n : ℝ) ^ s.re else 0
  have hterm_norm : ∀ n : ℕ,
      ‖LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n -
        LSeries.term (fun m => (Λ m : ℂ)) s n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, g]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, g]
      by_cases hcop : Nat.Coprime n q
      · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hcop
        rw [MulChar.one_apply hu, one_mul, sub_self, norm_zero, if_neg (not_not.mpr hcop)]
      · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
        rw [MulChar.map_nonunit _ hnu, zero_mul, zero_div, zero_sub, norm_neg, if_pos hcop,
          norm_div, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hn]
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => by
    dsimp only [g]
    split_ifs
    · exact le_rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hnorm_sumZ : Summable (fun n => ‖LSeries.term (fun m => (Λ m : ℂ)) s n‖) :=
    hsumZ.norm
  have hg_summ : Summable g := by
    refine Summable.of_nonneg_of_le hg_nonneg (fun n => ?_) hnorm_sumZ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [g, LSeries.term]
    · dsimp only [g]
      split_ifs
      · exact norm_nonneg _
      · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hn]
        exact le_rfl
  have hsub_summ : Summable (fun n =>
      LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n -
        LSeries.term (fun m => (Λ m : ℂ)) s n) :=
    Summable.sub hsum1 hsumZ
  have htsum_le : ‖∑' n, (LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n -
        LSeries.term (fun m => (Λ m : ℂ)) s n)‖ ≤ ∑' n, g n := by
    calc ‖∑' n, (LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n -
          LSeries.term (fun m => (Λ m : ℂ)) s n)‖
        ≤ ∑' n, ‖LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n -
          LSeries.term (fun m => (Λ m : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsub_summ.norm
      _ ≤ ∑' n, g n := hsub_summ.norm.tsum_le_tsum hterm_norm hg_summ
  refine htsum_le.trans ?_
  -- Bound every finite partial sum of `g` by `Real.log q` via prime powers `p^(j+1)` with `p ∣ q`.
  refine hg_summ.tsum_le_of_sum_le fun F => ?_
  let K : ℕ := F.sup id + 1
  let Bset : Finset ℕ := q.primeFactors.biUnion fun p => (Finset.range K).image (fun j => p ^ (j + 1))
  have hsub : F.filter (fun n => g n ≠ 0) ⊆ Bset := by
    intro n hn
    have hnF : n ∈ F := (Finset.mem_filter.mp hn).1
    have hgn : g n ≠ 0 := (Finset.mem_filter.mp hn).2
    have hncop : ¬ Nat.Coprime n q := by
      intro hc; exact hgn (by simp [g, hc])
    have hΛne : Λ n ≠ 0 := by
      intro h0; exact hgn (by simp [g, h0])
    have hpp : IsPrimePow n := by
      by_contra hnp
      exact hΛne (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp)
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp_dvd : p ∣ q := by
      by_contra hndvd
      have hcop_pq : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hndvd
      exact hncop (hcop_pq.pow_left k)
    have hp_mem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, NeZero.ne q⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hjK : j < K := by
      have hle_sup : p ^ (j + 1) ≤ F.sup id := Finset.le_sup (f := id) hnF
      have hj_le_pow : j < p ^ (j + 1) := by
        calc j < j + 1 := Nat.lt_succ_self j
          _ < 2 ^ (j + 1) := Nat.lt_two_pow_self
          _ ≤ p ^ (j + 1) := Nat.pow_le_pow_left hp.two_le (j + 1)
      exact Nat.lt_succ_of_le (hj_le_pow.le.trans hle_sup)
    exact Finset.mem_biUnion.mpr ⟨p, hp_mem, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjK, rfl⟩⟩
  have hsum_F_eq : ∑ n ∈ F, g n = ∑ n ∈ F.filter (fun n => g n ≠ 0), g n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · exact not_not.mp h
  have hbiUnion_le : ∀ (S : Finset ℕ) (t : ℕ → Finset ℕ),
      ∑ n ∈ S.biUnion t, g n ≤ ∑ p ∈ S, ∑ n ∈ t p, g n := by
    intro S t
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have hunion := Finset.sum_union_inter (s₁ := t a) (s₂ := S.biUnion t) (f := g)
      have hinter : 0 ≤ ∑ n ∈ t a ∩ S.biUnion t, g n := Finset.sum_nonneg (fun n _ => hg_nonneg n)
      linarith
  have hBset_le : ∑ n ∈ Bset, g n ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
    calc ∑ n ∈ Bset, g n
        ≤ ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.range K).image (fun j => p ^ (j + 1)), g n :=
          hbiUnion_le q.primeFactors (fun p => (Finset.range K).image (fun j => p ^ (j + 1)))
      _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
          have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
          have hinj : Function.Injective (fun j : ℕ => p ^ (j + 1)) := fun a b hab => by
            have := Nat.pow_right_injective hprime.two_le hab
            omega
          rw [Finset.sum_image (fun a _ b _ h => hinj h)]
          set r : ℝ := (p : ℝ) ^ (-s.re)
          have hr_pos : 0 < r := Real.rpow_pos_of_pos hp_pos _
          have hr_lt1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
          have hterm_j : ∀ j ∈ Finset.range K,
              g (p ^ (j + 1)) ≤ Real.log (p : ℝ) * (r * r ^ j) := fun j _ => by
            dsimp only [g]
            split_ifs
            · exact mul_nonneg (Real.log_nonneg (by linarith)) (by positivity)
            · have hΛ : Λ (p ^ (j + 1)) = Real.log (p : ℝ) :=
                ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero j) |>.trans
                  (ArithmeticFunction.vonMangoldt_apply_prime hprime)
              rw [hΛ]
              have hpow : (((p ^ (j + 1) : ℕ) : ℝ) ^ s.re)⁻¹ = r * r ^ j := by
                push_cast
                rw [← Real.rpow_neg (by positivity), ← Real.rpow_natCast (p : ℝ) (j + 1),
                  ← Real.rpow_mul hp_pos.le, ← pow_succ', ← Real.rpow_natCast r (j + 1)]
                dsimp only [r]
                rw [← Real.rpow_mul hp_pos.le]
                congr 1; ring
              rw [div_eq_mul_inv, hpow]
          have hgeom_sum : ∑ j ∈ Finset.range K, r ^ j ≤ (1 - r)⁻¹ := by
            rw [geom_sum_eq hr_lt1.ne K]
            have h1r : 0 < 1 - r := by linarith
            have hrK : 0 ≤ r ^ K := pow_nonneg hr_pos.le K
            have heq : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
              rw [← neg_div_neg_eq]; ring_nf
            rw [heq, inv_eq_one_div]
            exact div_le_div_of_nonneg_right (by linarith) h1r.le
          have hps_ge : (p : ℝ) ≤ (p : ℝ) ^ s.re := by
            calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (p : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
          have hr_ratio : r * (1 - r)⁻¹ ≤ 1 := by
            have hr_le_half : r ≤ 1 / 2 := by
              dsimp only [r]
              rw [Real.rpow_neg hp_pos.le]
              rw [inv_le_comm₀ (Real.rpow_pos_of_pos hp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)]
              norm_num
              linarith
            have h1r : 0 < 1 - r := by linarith
            rw [← div_eq_mul_inv, div_le_one h1r]
            linarith
          calc ∑ j ∈ Finset.range K, g (p ^ (j + 1))
              ≤ ∑ j ∈ Finset.range K, Real.log (p : ℝ) * (r * r ^ j) := Finset.sum_le_sum hterm_j
            _ = Real.log (p : ℝ) * (r * ∑ j ∈ Finset.range K, r ^ j) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
            _ ≤ Real.log (p : ℝ) * (r * (1 - r)⁻¹) := by
                refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by linarith))
                exact mul_le_mul_of_nonneg_left hgeom_sum hr_pos.le
            _ ≤ Real.log (p : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hr_ratio (Real.log_nonneg (by linarith))
            _ = Real.log (p : ℝ) := mul_one _
  have hlog_prod : ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
    have hne0 : ∀ p ∈ q.primeFactors, (p : ℝ) ≠ 0 := fun p hp =>
      Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [← Real.log_prod hne0]
    have hdvd : ∏ p ∈ q.primeFactors, p ∣ q := Nat.prod_primeFactors_dvd q
    have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (NeZero.pos q) hdvd
    have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, (p : ℝ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hleR : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
      have : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
      simpa using this
    exact Real.log_le_log hpos hleR
  calc ∑ n ∈ F, g n
      = ∑ n ∈ F.filter (fun n => g n ≠ 0), g n := hsum_F_eq
    _ ≤ ∑ n ∈ Bset, g n := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg_nonneg n)
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := hBset_le
    _ ≤ Real.log (q : ℝ) := hlog_prod

/-- Unconditional real-part corollary: for all `q ≥ 1` and `1 < s.re`,
`Re(-L'/L(1_q, s)) ≤ Re(-ζ'/ζ(s)) + Real.log q`. -/
theorem re_negLogDerivL_one_le_re_negLogDerivZeta_add_log {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s).re ≤
      (Stage3ZeroFreeRegion.negLogDerivZeta s).re + Real.log (q : ℝ) := by
  have h := norm_negLogDerivL_one_sub_negLogDerivZeta_le_log (q := q) hs
  have habs := (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re] at habs
  linarith [(abs_le.mp habs).2]

/-! ## Section 6: Bridge to `Stage3ZeroFreeRegion.HadamardLogDerivPackage` & Zero-Free Regions -/

/-- A genus-1 Hadamard partial-fraction representation of a negative logarithmic derivative `f`
on the strip `1 < Re(s) ≤ 2` with pole term `P`, critical-strip zero enumeration `ρ`, constant
`B₀`, and analytic/gamma error `E` bounded by `M(t)`. -/
structure HadamardPartialFractionRep (f P : ℂ → ℂ) (zeroPred : ℂ → Prop) (M : ℝ → ℝ) : Type where
  ρ : ℕ → ℂ
  hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1
  hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)
  hcomplete : ∀ z : ℂ, 0 < z.re → z.re < 1 → zeroPred z → ∃ n, ρ n = z
  B₀ : ℂ
  E : ℂ → ℂ
  hrep : ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    f ((σ : ℂ) + I * (t : ℂ)) =
      P ((σ : ℂ) + I * (t : ℂ)) - B₀ -
        (∑' n : ℕ, (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ n) + 1 / ρ n)) +
        E ((σ : ℂ) + I * (t : ℂ))
  hbound : ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    -(B₀.re + ∑' n : ℕ, (1 / ρ n).re) + (E ((σ : ℂ) + I * (t : ℂ))).re ≤ M t

/-- Any `HadamardPartialFractionRep` yields the 0-zero, 1-zero, and 2-zero upper bounds on `1 < σ ≤ 2`. -/
theorem HadamardPartialFractionRep.re_le_sub_finset {f P : ℂ → ℂ} {zeroPred : ℂ → Prop} {M : ℝ → ℝ}
    (H : HadamardPartialFractionRep f P zeroPred M) {σ : ℝ} (t : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (F : Finset ℕ) :
    (f ((σ : ℂ) + I * (t : ℂ))).re ≤
      (P ((σ : ℂ) + I * (t : ℂ))).re + M t -
        ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) - H.ρ n)).re := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ1]
  exact re_le_sub_finset_of_hadamard_partialFraction H.hstrip H.hsum hs
    (H.hrep σ t hσ1 hσ2) (H.hbound σ t hσ1 hσ2) F

/-- System of genus-1 Hadamard partial-fraction representations for `riemannZeta` and all
non-principal Dirichlet `L`-functions `DirichletCharacter.LFunction χ` (`χ ≠ 1`), with
error bound `B_err * log(q (|t| + 2))`. (Principal characters `χ = 1` are handled
unconditionally via `re_negLogDerivL_one_le_re_negLogDerivZeta_add_log`!) -/
structure HadamardPartialFractionSystem (B_err : ℝ) : Type where
  B_pos : 0 < B_err
  zeta_rep :
    HadamardPartialFractionRep
      Stage3ZeroFreeRegion.negLogDerivZeta
      (fun s => 1 / (s - 1))
      (fun z => riemannZeta z = 0)
      (fun t => B_err * Real.log (|t| + 2))
  nonprincipal_rep :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      HadamardPartialFractionRep
        (Stage3ZeroFreeRegion.negLogDerivL χ)
        (fun _ => 0)
        (fun z => DirichletCharacter.LFunction χ z = 0)
        (fun t => B_err * Real.log ((q : ℝ) * (|t| + 2)))

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_two_lt_d9]

/-- **Main Bridge Theorem**: any `HadamardPartialFractionSystem B_err` unconditionally constructs
`Stage3ZeroFreeRegion.HadamardLogDerivPackage (max B_err 1)`. -/
theorem hadamardLogDerivPackage_of_partialFractionSystem {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err) :
    Stage3ZeroFreeRegion.HadamardLogDerivPackage (max B_err 1) := by
  set B : ℝ := max B_err 1
  have hB1 : 1 ≤ B := le_max_right B_err 1
  have hB_pos : 0 < B := lt_of_lt_of_le (by norm_num) hB1
  have hBeB : B_err ≤ B := le_max_left B_err 1
  have hlog_nonneg : ∀ t : ℝ, 0 ≤ Real.log (|t| + 2) := fun t =>
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hlogq_nonneg : ∀ (q : ℕ) [NeZero q] (t : ℝ), 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
    fun q _ t => by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
      exact Real.log_nonneg (by nlinarith [abs_nonneg t])
  refine
    { B_pos := hB_pos
      zeta_pole := fun σ hσ1 hσ2 => ?_
      zeta_upper := fun σ t hσ1 hσ2 => ?_
      zeta_one_zero := fun ρ h0 h1 hz σ t hσ1 hσ2 => ?_
      zeta_two_zeros := fun ρ₁ ρ₂ hne h10 h11 h20 h21 hz1 hz2 σ t hσ1 hσ2 => ?_
      principal_upper := fun q _ σ t hσ1 hσ2 => ?_
      nonprincipal_upper := fun q _ χ hχ σ t hσ1 hσ2 => ?_
      nonprincipal_one_zero := fun q _ χ hχ ρ h0 h1 hz σ t hσ1 hσ2 => ?_
      nonprincipal_two_zeros := fun q _ χ hχ ρ₁ ρ₂ hne h10 h11 h20 h21 hz1 hz2 σ t hσ1 hσ2 => ?_ }
  · -- `zeta_pole`
    have h := H.zeta_rep.re_le_sub_finset 0 hσ1 hσ2 ∅
    simp only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero, zero_add,
      Finset.sum_empty, sub_zero] at h
    have hpole : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
      have hsub : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hpole] at h
    have hlog2 : B_err * Real.log 2 ≤ B := by
      have h1 : B_err * Real.log 2 ≤ B_err * 1 :=
        mul_le_mul_of_nonneg_left log_two_le_one H.B_pos.le
      linarith
    linarith
  · -- `zeta_upper`
    have h := H.zeta_rep.re_le_sub_finset t hσ1 hσ2 ∅
    simp only [Finset.sum_empty, sub_zero] at h
    have hBe : B_err * Real.log (|t| + 2) ≤ B * Real.log (|t| + 2) :=
      mul_le_mul_of_nonneg_right hBeB (hlog_nonneg t)
    linarith
  · -- `zeta_one_zero`
    obtain ⟨n, hn⟩ := H.zeta_rep.hcomplete ρ h0 h1 hz
    have h := H.zeta_rep.re_le_sub_finset t hσ1 hσ2 {n}
    simp only [Finset.sum_singleton, hn] at h
    have hBe : B_err * Real.log (|t| + 2) ≤ B * Real.log (|t| + 2) :=
      mul_le_mul_of_nonneg_right hBeB (hlog_nonneg t)
    linarith
  · -- `zeta_two_zeros`
    obtain ⟨n₁, hn₁⟩ := H.zeta_rep.hcomplete ρ₁ h10 h11 hz1
    obtain ⟨n₂, hn₂⟩ := H.zeta_rep.hcomplete ρ₂ h20 h21 hz2
    have hn_ne : n₁ ≠ n₂ := fun heq => hne (by rw [← hn₁, ← hn₂, heq])
    have h := H.zeta_rep.re_le_sub_finset t hσ1 hσ2 {n₁, n₂}
    rw [Finset.sum_pair hn_ne, hn₁, hn₂] at h
    have hBe : B_err * Real.log (|t| + 2) ≤ B * Real.log (|t| + 2) :=
      mul_le_mul_of_nonneg_right hBeB (hlog_nonneg t)
    linarith
  · -- `principal_upper` (unconditionally derived from `zeta_upper` + Euler-factor `log q` bound!)
    have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ1]
    have heuler := re_negLogDerivL_one_le_re_negLogDerivZeta_add_log (q := q) hs
    have hζ := H.zeta_rep.re_le_sub_finset t hσ1 hσ2 ∅
    simp only [Finset.sum_empty, sub_zero] at hζ
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hlog_split : Real.log ((q : ℝ) * (|t| + 2)) = Real.log (q : ℝ) + Real.log (|t| + 2) :=
      Real.log_mul hq_pos.ne' (by positivity)
    have hBe : B_err * Real.log (|t| + 2) ≤ B * Real.log (|t| + 2) :=
      mul_le_mul_of_nonneg_right hBeB (hlog_nonneg t)
    have hlogq : Real.log (q : ℝ) ≤ B * Real.log (q : ℝ) := by
      nlinarith [Real.log_nonneg hq_ge1]
    rw [hlog_split]
    linarith
  · -- `nonprincipal_upper`
    have h := (H.nonprincipal_rep q χ hχ).re_le_sub_finset t hσ1 hσ2 ∅
    simp only [Complex.zero_re, zero_add, Finset.sum_empty, sub_zero] at h
    have hBe : B_err * Real.log ((q : ℝ) * (|t| + 2)) ≤ B * Real.log ((q : ℝ) * (|t| + 2)) :=
      mul_le_mul_of_nonneg_right hBeB (hlogq_nonneg q t)
    linarith
  · -- `nonprincipal_one_zero`
    obtain ⟨n, hn⟩ := (H.nonprincipal_rep q χ hχ).hcomplete ρ h0 h1 hz
    have h := (H.nonprincipal_rep q χ hχ).re_le_sub_finset t hσ1 hσ2 {n}
    simp only [Complex.zero_re, zero_add, Finset.sum_singleton, hn] at h
    have hBe : B_err * Real.log ((q : ℝ) * (|t| + 2)) ≤ B * Real.log ((q : ℝ) * (|t| + 2)) :=
      mul_le_mul_of_nonneg_right hBeB (hlogq_nonneg q t)
    linarith
  · -- `nonprincipal_two_zeros`
    obtain ⟨n₁, hn₁⟩ := (H.nonprincipal_rep q χ hχ).hcomplete ρ₁ h10 h11 hz1
    obtain ⟨n₂, hn₂⟩ := (H.nonprincipal_rep q χ hχ).hcomplete ρ₂ h20 h21 hz2
    have hn_ne : n₁ ≠ n₂ := fun heq => hne (by rw [← hn₁, ← hn₂, heq])
    have h := (H.nonprincipal_rep q χ hχ).re_le_sub_finset t hσ1 hσ2 {n₁, n₂}
    simp only [Complex.zero_re, zero_add] at h
    rw [Finset.sum_pair hn_ne, hn₁, hn₂] at h
    have hBe : B_err * Real.log ((q : ℝ) * (|t| + 2)) ≤ B * Real.log ((q : ℝ) * (|t| + 2)) :=
      mul_le_mul_of_nonneg_right hBeB (hlogq_nonneg q t)
    linarith

/-- Direct wiring from `HadamardPartialFractionSystem` into
`Stage3ZeroFreeRegion.zeroFreeRegion_complex_char`. -/
theorem zeroFreeRegion_complex_char_of_hadamard {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 ≠ 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - 1 / (168 * max B_err 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) := by
  have h := Stage3ZeroFreeRegion.zeroFreeRegion_complex_char
    (hadamardLogDerivPackage_of_partialFractionSystem H) hχ2 h0 h1 hz
  simpa [max_assoc] using h

/-- Direct wiring from `HadamardPartialFractionSystem` into
`Stage3ZeroFreeRegion.zeroFreeRegion_real_char_nonreal_zero`. -/
theorem zeroFreeRegion_real_char_nonreal_zero_of_hadamard {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0)
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - 1 / (296 * max B_err 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) := by
  have h := Stage3ZeroFreeRegion.zeroFreeRegion_real_char_nonreal_zero
    (hadamardLogDerivPackage_of_partialFractionSystem H) hχ1 hχ2 h0 h1 him hz
  simpa [max_assoc] using h

/-- Direct wiring from `HadamardPartialFractionSystem` into
`Stage3ZeroFreeRegion.zeroFreeRegion_riemannZeta`. -/
theorem zeroFreeRegion_riemannZeta_of_hadamard {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) (hz : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - 1 / (640 * max B_err 1 * Real.log (|ρ.im| + 2)) := by
  have h := Stage3ZeroFreeRegion.zeroFreeRegion_riemannZeta
    (hadamardLogDerivPackage_of_partialFractionSystem H) h0 h1 him hz
  simpa [max_assoc] using h

/-- Direct wiring from `HadamardPartialFractionSystem` into
`Stage3ZeroFreeRegion.real_char_at_most_one_exceptional_real_zero`. -/
theorem real_char_at_most_one_exceptional_real_zero_of_hadamard {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {β₁ β₂ : ℝ} (hne : β₁ ≠ β₂)
    (h10 : 0 < β₁) (h11 : β₁ < 1) (h20 : 0 < β₂) (h21 : β₂ < 1)
    (hz1 : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0)
    (hz2 : DirichletCharacter.LFunction χ (β₂ : ℂ) = 0) :
    min β₁ β₂ ≤ 1 - 1 / (18 * max B_err 1 * Real.log (2 * (q : ℝ))) := by
  have h := Stage3ZeroFreeRegion.real_char_at_most_one_exceptional_real_zero
    (hadamardLogDerivPackage_of_partialFractionSystem H) hχ1 hne h10 h11 h20 h21 hz1 hz2
  simpa [max_assoc] using h

/-- Direct wiring from `HadamardPartialFractionSystem` into
`Stage3ZeroFreeRegion.landau_page_exceptional_zero_isolation`. -/
theorem landau_page_exceptional_zero_isolation_of_hadamard {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err) {Q : ℝ} (hQ : 2 ≤ Q) :
    (∀ (ψ : RHDirect.PChar) (β : ℝ), ψ.χ ≠ 1 → (ψ.N : ℝ) ≤ Q → 0 < β → β < 1 →
        DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 →
        1 - 1 / (168 * max B_err 1 * Real.log (2 * Q)) < β → ψ.IsReal) ∧
    (∀ (ψ₁ ψ₂ : RHDirect.PChar) (β₁ β₂ : ℝ),
        ψ₁.χ ≠ 1 → ψ₂.χ ≠ 1 → (ψ₁.N : ℝ) ≤ Q → (ψ₂.N : ℝ) ≤ Q →
        0 < β₁ → β₁ < 1 → 0 < β₂ → β₂ < 1 →
        DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0 →
        DirichletCharacter.LFunction ψ₂.χ (β₂ : ℂ) = 0 →
        1 - 1 / (168 * max B_err 1 * Real.log (2 * Q)) < β₁ →
        1 - 1 / (168 * max B_err 1 * Real.log (2 * Q)) < β₂ →
        ψ₁ = ψ₂ ∧ β₁ = β₂) := by
  have h := Stage3ZeroFreeRegion.landau_page_exceptional_zero_isolation
    (hadamardLogDerivPackage_of_partialFractionSystem H) hQ
  simpa [max_assoc] using h

/-- Direct wiring from `HadamardPartialFractionSystem` into
`Stage3ZeroFreeRegion.zeroFreeRegion_nonexceptional`. -/
theorem zeroFreeRegion_nonexceptional_of_hadamard {B_err : ℝ}
    (H : HadamardPartialFractionSystem B_err)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - 1 / (296 * max B_err 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) ∨
      (Stage3ZeroFreeRegion.IsRealChar χ ∧ ρ.im = 0 ∧
        1 - 1 / (296 * max B_err 1 * Real.log (2 * (q : ℝ))) < ρ.re) := by
  have h := Stage3ZeroFreeRegion.zeroFreeRegion_nonexceptional
    (hadamardLogDerivPackage_of_partialFractionSystem H) hχ1 h0 h1 hz
  simpa [max_assoc] using h

end RHDirect.Stage5JensenHadamard
