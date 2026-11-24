import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.MellinTransform

/-!
# RHDirect.Stage5StirlingPhragmen

Unconditional, 0-`sorry`, 0-custom-`axiom` Stage 5 complex-analytic foundations in pure
Mathlib `v4.33.1`, establishing:

1. **Phragmén–Lindelöf Vertical-Strip Convexity & Polynomial Convexity**:
   - Rectangle Maximum Modulus Principle on `[a, b] × [-T, T]` (`norm_le_of_rectangle_frontier`).
   - Direct `exp(ε s²)`-damped sub-Gaussian Phragmén–Lindelöf maximum principle and Three-Lines
     Convexity Theorem (`phragmen_lindelof_strip_subgaussian`,
     `phragmen_lindelof_convexity_subgaussian`).
   - Sharp double-exponential Phragmén–Lindelöf Vertical-Strip Convexity Theorem
     (`phragmen_lindelof_convexity`, `phragmen_lindelof_convexity_double_exp`).
   - Polynomial Vertical-Strip Convexity Corollary (`phragmen_lindelof_polynomial_convexity`,
     `phragmen_lindelof_polynomial_convexity_subgaussian`) via Gaussian-shift damping
     `exp((s - i t₀)²)`.

2. **Concrete Upper/Lower Bounds on Mathlib's `Complex.Gamma`, `Real.Gamma`, `Stirling`, & `Complex.digamma`**:
   - Integral modulus inequality `‖Complex.Gamma s‖ ≤ Real.Gamma s.re` (`norm_Gamma_le_real_Gamma`).
   - Convexity and factorial-shift upper bounds on `Real.Gamma` and `Complex.Gamma`:
     `Real.Gamma σ ≤ 1` on `[1, 2]`, `Real.Gamma σ ≤ σ ^ (σ - 1) ≤ σ ^ σ` for `σ ≥ 1`,
     two-sided Stirling bounds for `n!`, and `‖Complex.Gamma s‖ ≤ (‖s‖ + 1) ^ s.re` for `s.re ≥ 1`.
   - Exact critical-line reflection formula modulus
     `‖Complex.Gamma (1 / 2 + I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t)`
     (`norm_sq_Gamma_half_add_I_mul`), yielding exact two-sided exponential decay
     `√π exp(-π |t| / 2) ≤ ‖Γ(1/2 + i t)‖ ≤ √(2 π) exp(-π |t| / 2)`, exact 1-line modulus
     `‖Γ(1 + i t)‖² = π t / sinh(π t)`, and full Complex Stirling vertical-strip decay
     `‖Γ(σ + i t)‖ ≤ C * (|t| + 2) ^ (σ - 1 / 2) * exp(-π |t| / 2)` on `1/2 ≤ σ ≤ b`
     via Phragmén–Lindelöf polynomial convexity.
   - Digamma shift recurrence `Complex.digamma (s + n) = Complex.digamma s + ∑ j < n, (s + j)⁻¹`.

3. **Unconditional Entirety, Functional Equation, Zero Equivalence, & Order-1 Growth of Mathlib's
   Actual Completed Zeta `ξ(s) = s (s - 1) completedRiemannZeta₀ s + 1`**:
   - `xi s = s * (s - 1) * completedRiemannZeta s` for all `s ≠ 0, 1`, with `xi 0 = xi 1 = 1`.
   - Entirety (`differentiable_xi`), exact functional equation (`xi_one_sub`), exact critical-strip
     zero equivalence (`xi_eq_zero_iff_riemannZeta_eq_zero`, `xi_eq_zero_iff_critical_strip_zeta_zero`,
     `riemannHypothesis_iff_xi_zeros_on_half_line`).
   - Uniform vertical-strip boundedness of `completedRiemannZeta₀` from its Mellin–theta integral
     representation (`norm_completedRiemannZeta₀_bounded_on_strip`).
   - Unconditional Order-1 Exponential Growth Bound:
     `∃ A > 0, ∃ B > 0, ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B)`
     (`norm_xi_order_one_bound`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators Real

namespace RHDirect.Stage5StirlingPhragmen

/-! ## Section 1: Rectangle Maximum Modulus & Phragmén–Lindelöf Vertical-Strip Convexity -/

/-- Open axis-aligned rectangle `(a, b) × (-T, T)` in `ℂ`. -/
def openRect (a b T : ℝ) : Set ℂ := Set.Ioo a b ×ℂ Set.Ioo (-T) T

lemma isBounded_openRect (a b T : ℝ) : Bornology.IsBounded (openRect a b T) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨max |a| |b| + |T| + 1, fun z hz => ?_⟩
  simp only [openRect, Complex.mem_reProdIm, Set.mem_Ioo] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le a) hz.1.1.le)
    · exact le_trans hz.1.2.le (le_trans (le_abs_self b) (le_max_right _ _))
  have him : |z.im| ≤ |T| := by
    rw [abs_le]
    have hT : 0 ≤ T := by linarith [hz.2.1, hz.2.2]
    rw [abs_of_nonneg hT]
    exact ⟨hz.2.1.le, hz.2.2.le⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ max |a| |b| + |T| := add_le_add hre him
    _ ≤ max |a| |b| + |T| + 1 := by linarith

lemma closure_openRect {a b T : ℝ} (hab : a < b) (hT : 0 < T) :
    closure (openRect a b T) = Set.Icc a b ×ℂ Set.Icc (-T) T := by
  unfold openRect
  rw [Complex.closure_reProdIm, closure_Ioo hab.ne, closure_Ioo (by linarith : -T ≠ T)]

lemma frontier_openRect_subset {a b T : ℝ} (hab : a < b) (hT : 0 < T) :
    frontier (openRect a b T) ⊆
      {z : ℂ | (z.re = a ∨ z.re = b) ∧ |z.im| ≤ T} ∪
      {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| = T} := by
  intro z hz
  rw [frontier, closure_openRect hab hT] at hz
  rw [show interior (openRect a b T) = openRect a b T from
    (isOpen_Ioo.reProdIm isOpen_Ioo).interior_eq] at hz
  rcases hz with ⟨hcl, hnot⟩
  simp only [Complex.mem_reProdIm, Set.mem_Icc] at hcl
  simp only [openRect, Complex.mem_reProdIm, Set.mem_Ioo, not_and_or, not_lt] at hnot
  have him_le : |z.im| ≤ T := abs_le.mpr hcl.2
  rcases hnot with (hre | him)
  · left
    refine ⟨?_, him_le⟩
    rcases hre with h1 | h2
    · exact Or.inl (le_antisymm h1 hcl.1.1)
    · exact Or.inr (le_antisymm hcl.1.2 h2)
  · right
    refine ⟨hcl.1.1, hcl.1.2, ?_⟩
    rcases him with h1 | h2
    · have : z.im = -T := le_antisymm h1 hcl.2.1
      rw [this, abs_neg, abs_of_pos hT]
    · have : z.im = T := le_antisymm hcl.2.2 h2
      rw [this, abs_of_pos hT]

/-- **Maximum Modulus Principle on Closed Rectangles `[a, b] × [-T, T]`**:
a function holomorphic on `(a, b) × (-T, T)` and continuous on `[a, b] × [-T, T]` is bounded
on the closed rectangle by any upper bound holding on all four boundary edges. -/
theorem norm_le_of_rectangle_frontier {a b T M : ℝ} (hab : a < b) (hT : 0 < T) {f : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ f (openRect a b T))
    (hcont : ContinuousOn f (Set.Icc a b ×ℂ Set.Icc (-T) T))
    (hleft : ∀ t : ℝ, |t| ≤ T → ‖f (a + I * t)‖ ≤ M)
    (hright : ∀ t : ℝ, |t| ≤ T → ‖f (b + I * t)‖ ≤ M)
    (htop : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖f (σ + I * T)‖ ≤ M)
    (hbot : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖f (σ + I * (-T))‖ ≤ M)
    {z : ℂ} (hre1 : a ≤ z.re) (hre2 : z.re ≤ b) (him : |z.im| ≤ T) :
    ‖f z‖ ≤ M := by
  have hdc : DiffContOnCl ℂ f (openRect a b T) := by
    refine ⟨hdiff, ?_⟩
    rw [closure_openRect hab hT]
    exact hcont
  have hfront : ∀ w ∈ frontier (openRect a b T), ‖f w‖ ≤ M := by
    intro w hw
    have hw' := frontier_openRect_subset hab hT hw
    rcases hw' with ⟨hre | hre, him_w⟩ | ⟨ha, hb, him_w⟩
    · have heq : w = (a : ℂ) + I * (w.im : ℂ) := by
        apply Complex.ext <;> simp [hre]
      rw [heq]; exact hleft w.im him_w
    · have heq : w = (b : ℂ) + I * (w.im : ℂ) := by
        apply Complex.ext <;> simp [hre]
      rw [heq]; exact hright w.im him_w
    · rcases abs_eq hT.le |>.mp him_w with hpos | hneg
      · have heq : w = (w.re : ℂ) + I * (T : ℂ) := by
          apply Complex.ext <;> simp [hpos]
        rw [heq]; exact htop w.re ha hb
      · have heq : w = (w.re : ℂ) + I * (-(T : ℂ)) := by
          apply Complex.ext <;> simp [hneg]
        rw [heq]; exact hbot w.re ha hb
  have hz_cl : z ∈ closure (openRect a b T) := by
    rw [closure_openRect hab hT]
    exact ⟨⟨hre1, hre2⟩, abs_le.mp him⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_openRect a b T) hdc hfront hz_cl

/-- Norm of the Gaussian damping factor `exp(ε * s ^ 2)`. -/
lemma norm_exp_mul_sq (ε : ℝ) (s : ℂ) :
    ‖Complex.exp ((ε : ℂ) * s ^ 2)‖ = Real.exp (ε * (s.re ^ 2 - s.im ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re, Complex.mul_im]

/-- For `α < 2` and `ε > 0`, `A * T ^ α - ε * T ^ 2 → -∞` as `T → ∞`. -/
lemma tendsto_subgaussian_damp {A ε α : ℝ} (hε : 0 < ε) (hα : α < 2) :
    Tendsto (fun T : ℝ => A * T ^ α - ε * T ^ 2) atTop atBot := by
  have h2α : 0 < 2 - α := sub_pos.mpr hα
  have h1 : Tendsto (fun T : ℝ => T ^ (2 - α)) atTop atTop :=
    tendsto_rpow_atTop h2α
  have h2 : Tendsto (fun T : ℝ => ε * T ^ (2 - α) - A) atTop atTop :=
    (h1.const_mul_atTop hε).atTop_add tendsto_const_nhds
  have h3 : Tendsto (fun T : ℝ => T ^ α) atTop atTop ∨
      ∀ᶠ T : ℝ in atTop, T ^ α ≤ 1 := by
    by_cases hα0 : 0 < α
    · exact Or.inl (tendsto_rpow_atTop hα0)
    · right
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact Real.rpow_le_one_of_one_le_of_nonpos hT (not_lt.mp hα0)
  have hneg : Tendsto (fun T : ℝ => ε * T ^ 2 - A * T ^ α) atTop atTop := by
    have heq : ∀ᶠ T : ℝ in atTop,
        ε * T ^ 2 - A * T ^ α = (ε * T ^ (2 - α) - A) * T ^ α := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hr : T ^ (2 - α) * T ^ α = T ^ 2 := by
        rw [← Real.rpow_add hT, sub_add_cancel]
        exact Real.rpow_two T
      linarith [show ε * T ^ (2 - α) * T ^ α = ε * T ^ 2 by rw [mul_assoc, hr]]
    rw [tendsto_congr' heq]
    rcases h3 with htop | hle
    · exact h2.atTop_mul_atTop₀ htop
    · have h2' : Tendsto (fun T : ℝ => ε * T ^ 2 - |A|) atTop atTop := by
        have hsq : Tendsto (fun T : ℝ => T ^ (2 : ℝ)) atTop atTop :=
          tendsto_rpow_atTop (by norm_num)
        have hsq' : Tendsto (fun T : ℝ => T ^ (2 : ℕ)) atTop atTop :=
          hsq.congr (fun T => Real.rpow_two T)
        exact (hsq'.const_mul_atTop hε).atTop_add tendsto_const_nhds
      refine tendsto_atTop_mono' atTop ?_ h2'
      filter_upwards [hle, eventually_gt_atTop (0 : ℝ)] with T hT1 hT0
      have hr : T ^ (2 - α) * T ^ α = T ^ 2 := by
        rw [← Real.rpow_add hT0, sub_add_cancel]
        exact Real.rpow_two T
      have hmul : (ε * T ^ (2 - α) - A) * T ^ α = ε * T ^ 2 - A * T ^ α := by
        linarith [show ε * T ^ (2 - α) * T ^ α = ε * T ^ 2 by rw [mul_assoc, hr]]
      rw [hmul]
      have hTα0 : 0 ≤ T ^ α := Real.rpow_nonneg hT0.le α
      have hAT : A * T ^ α ≤ |A| := by
        calc A * T ^ α ≤ |A| * T ^ α := mul_le_mul_of_nonneg_right (le_abs_self A) hTα0
          _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left hT1 (abs_nonneg A)
          _ = |A| := mul_one _
      linarith
  have hbot : Tendsto (fun T : ℝ => -(ε * T ^ 2 - A * T ^ α)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hneg
  exact hbot.congr (fun T => by ring)

/-- **Direct `exp(ε s²)`-Damped Phragmén–Lindelöf Maximum Principle on Vertical Strips**:
proved directly from the rectangle Maximum Modulus Principle on `[a, b] × [-T, T]` under
sub-Gaussian growth `‖f(s)‖ ≤ C exp(A |Im s|^α)` (`α < 2`). -/
theorem phragmen_lindelof_strip_subgaussian {a b C A α M : ℝ}
    (hab : a < b) (hα : α < 2) (hM : 0 ≤ M) {f : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hcont : ContinuousOn f (Complex.re ⁻¹' Set.Icc a b))
    (hgrow : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C * Real.exp (A * |s.im| ^ α))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ M)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ M)
    {s₀ : ℂ} (hs1 : a ≤ s₀.re) (hs2 : s₀.re ≤ b) :
    ‖f s₀‖ ≤ M := by
  -- Reduce to `M' > 0` by taking `M' = M + δ` and letting `δ → 0⁺`.
  suffices hpos : ∀ M' : ℝ, M < M' → ‖f s₀‖ ≤ M' by
    by_contra hlt
    push Not at hlt
    have := hpos ((‖f s₀‖ + M) / 2) (by linarith)
    linarith
  intro M' hMM'
  have hM' : 0 < M' := lt_of_le_of_lt hM hMM'
  -- Fix `ε > 0`; bound `g_ε(s) = f(s) * exp(ε s²)` on `[a, b] × [-T, T]` for large `T`.
  have hε_bound : ∀ ε : ℝ, 0 < ε →
      ‖f s₀‖ * Real.exp (ε * (s₀.re ^ 2 - s₀.im ^ 2)) ≤ M' * Real.exp (ε * max (a ^ 2) (b ^ 2)) := by
    intro ε hε
    set g : ℂ → ℂ := fun s => f s * Complex.exp ((ε : ℂ) * s ^ 2)
    have hC0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right C 1)
    have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have hlim := tendsto_subgaussian_damp (A := A) hε hα
    have hT_ev := (hlim.eventually (eventually_le_atBot (Real.log (M' / max C 1)))).and
      (eventually_gt_atTop (max |s₀.im| 1))
    obtain ⟨T, hT_log, hT_gt⟩ := hT_ev.exists
    have hT_pos : 0 < T := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hT_gt.le
    have hT_im : |s₀.im| ≤ T := le_trans (le_max_left _ _) hT_gt.le
    have hdiff_g : DifferentiableOn ℂ g (openRect a b T) := by
      refine (hdiff.mono ?_).mul ?_
      · intro z hz; exact hz.1
      · exact ((differentiable_const _).mul (differentiable_id.pow 2)).cexp.differentiableOn
    have hcont_g : ContinuousOn g (Set.Icc a b ×ℂ Set.Icc (-T) T) := by
      refine (hcont.mono ?_).mul ?_
      · intro z hz; exact hz.1
      · exact ((continuous_const.mul (continuous_id.pow 2)).cexp).continuousOn
    set B := M' * Real.exp (ε * max (a ^ 2) (b ^ 2))
    have hre_sq_le : ∀ σ : ℝ, a ≤ σ → σ ≤ b → σ ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
      intro σ h1 h2
      rcases le_total 0 σ with h0 | h0
      · exact le_trans (sq_le_sq.mpr (by rw [abs_of_nonneg h0]; exact le_trans h2 (le_abs_self b)))
          (le_max_right _ _)
      · have ha0 : a ≤ 0 := le_trans h1 h0
        have : |σ| ≤ |a| := by rw [abs_of_nonpos h0, abs_of_nonpos ha0]; linarith
        exact le_trans (sq_le_sq.mpr this) (le_max_left _ _)
    have hleft_g : ∀ t : ℝ, |t| ≤ T → ‖g (a + I * t)‖ ≤ B := by
      intro t _
      change ‖f (a + I * t) * Complex.exp ((ε : ℂ) * (a + I * t) ^ 2)‖ ≤ B
      rw [norm_mul, norm_exp_mul_sq]
      have hre : ((a : ℂ) + I * (t : ℂ)).re = a := by simp
      have him : ((a : ℂ) + I * (t : ℂ)).im = t := by simp
      rw [hre, him]
      calc ‖f (a + I * t)‖ * Real.exp (ε * (a ^ 2 - t ^ 2))
          ≤ M' * Real.exp (ε * (a ^ 2 - t ^ 2)) :=
            mul_le_mul_of_nonneg_right (le_trans (hleft t) hMM'.le) (Real.exp_pos _).le
        _ ≤ M' * Real.exp (ε * max (a ^ 2) (b ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM'.le
            have : a ^ 2 - t ^ 2 ≤ max (a ^ 2) (b ^ 2) :=
              le_trans (sub_le_self _ (sq_nonneg t)) (le_max_left _ _)
            exact mul_le_mul_of_nonneg_left this hε.le
    have hright_g : ∀ t : ℝ, |t| ≤ T → ‖g (b + I * t)‖ ≤ B := by
      intro t _
      change ‖f (b + I * t) * Complex.exp ((ε : ℂ) * (b + I * t) ^ 2)‖ ≤ B
      rw [norm_mul, norm_exp_mul_sq]
      have hre : ((b : ℂ) + I * (t : ℂ)).re = b := by simp
      have him : ((b : ℂ) + I * (t : ℂ)).im = t := by simp
      rw [hre, him]
      calc ‖f (b + I * t)‖ * Real.exp (ε * (b ^ 2 - t ^ 2))
          ≤ M' * Real.exp (ε * (b ^ 2 - t ^ 2)) :=
            mul_le_mul_of_nonneg_right (le_trans (hright t) hMM'.le) (Real.exp_pos _).le
        _ ≤ M' * Real.exp (ε * max (a ^ 2) (b ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM'.le
            have : b ^ 2 - t ^ 2 ≤ max (a ^ 2) (b ^ 2) :=
              le_trans (sub_le_self _ (sq_nonneg t)) (le_max_right _ _)
            exact mul_le_mul_of_nonneg_left this hε.le
    have hhoriz : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| = T → ‖g s‖ ≤ B := by
      intro s h1 h2 himT
      change ‖f s * Complex.exp ((ε : ℂ) * s ^ 2)‖ ≤ B
      rw [norm_mul, norm_exp_mul_sq]
      have hfs : ‖f s‖ ≤ max C 1 * Real.exp (A * T ^ α) := by
        have h1' := hgrow s h1 h2
        rw [himT] at h1'
        exact le_trans h1' (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le)
      have hsqT : s.im ^ 2 = T ^ 2 := by rw [← sq_abs s.im, himT]
      have hsq_re := hre_sq_le s.re h1 h2
      have hexp_le : Real.exp (A * T ^ α - ε * T ^ 2) ≤ M' / max C 1 := by
        calc Real.exp (A * T ^ α - ε * T ^ 2)
            ≤ Real.exp (Real.log (M' / max C 1)) := Real.exp_le_exp.mpr hT_log
          _ = M' / max C 1 := Real.exp_log (div_pos hM' hCpos)
      calc ‖f s‖ * Real.exp (ε * (s.re ^ 2 - s.im ^ 2))
          ≤ (max C 1 * Real.exp (A * T ^ α)) * Real.exp (ε * (max (a ^ 2) (b ^ 2) - T ^ 2)) := by
            refine mul_le_mul hfs (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
              (mul_nonneg hC0 (Real.exp_pos _).le)
            rw [hsqT]
            exact mul_le_mul_of_nonneg_left (sub_le_sub_right hsq_re _) hε.le
        _ = max C 1 * Real.exp (A * T ^ α - ε * T ^ 2) * Real.exp (ε * max (a ^ 2) (b ^ 2)) := by
            rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
            congr 1; congr 1; ring
        _ ≤ max C 1 * (M' / max C 1) * Real.exp (ε * max (a ^ 2) (b ^ 2)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp_le hC0) (Real.exp_pos _).le
        _ = B := by rw [mul_div_cancel₀ _ hCpos.ne']
    have htop_g : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖g (σ + I * T)‖ ≤ B := by
      intro σ h1 h2
      exact hhoriz (σ + I * T) (by simpa using h1) (by simpa using h2) (by simp [abs_of_pos hT_pos])
    have hbot_g : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖g (σ + I * (-T))‖ ≤ B := by
      intro σ h1 h2
      exact hhoriz (σ + I * (-T)) (by simpa using h1) (by simpa using h2)
        (by simp [abs_of_pos hT_pos])
    have hres := norm_le_of_rectangle_frontier hab hT_pos hdiff_g hcont_g
      hleft_g hright_g htop_g hbot_g hs1 hs2 hT_im
    simpa [g, norm_mul, norm_exp_mul_sq] using hres
  -- Let `ε → 0⁺`.
  have h_le : ∀ ε : ℝ, 0 < ε →
      ‖f s₀‖ ≤ M' * Real.exp (ε * (max (a ^ 2) (b ^ 2) - (s₀.re ^ 2 - s₀.im ^ 2))) := by
    intro ε hε
    have h := hε_bound ε hε
    have hexp_pos : 0 < Real.exp (ε * (s₀.re ^ 2 - s₀.im ^ 2)) := Real.exp_pos _
    rw [← le_div_iff₀ hexp_pos, mul_div_assoc, ← Real.exp_sub] at h
    refine le_trans h (le_of_eq ?_)
    congr 2; ring
  have hlim_rhs : Tendsto
      (fun ε : ℝ => M' * Real.exp (ε * (max (a ^ 2) (b ^ 2) - (s₀.re ^ 2 - s₀.im ^ 2))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds M') := by
    have h0 : Continuous fun ε : ℝ =>
        M' * Real.exp (ε * (max (a ^ 2) (b ^ 2) - (s₀.re ^ 2 - s₀.im ^ 2))) := by fun_prop
    have h1 := (h0.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h1
  exact ge_of_tendsto hlim_rhs (eventually_nhdsWithin_of_forall fun ε hε => h_le ε hε)

/-- Auxiliary entire exponential interpolation weight `W(s) = M_a^{-(b-s)/(b-a)} M_b^{-(s-a)/(b-a)}`. -/
def interpWeight (a b Ma Mb : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(((b : ℂ) - s) / ((b - a : ℝ) : ℂ)) * (Real.log Ma : ℂ) -
    ((s - (a : ℂ)) / ((b - a : ℝ) : ℂ)) * (Real.log Mb : ℂ))

lemma differentiable_interpWeight (a b Ma Mb : ℝ) :
    Differentiable ℂ (interpWeight a b Ma Mb) := by
  unfold interpWeight
  fun_prop

lemma norm_interpWeight {a b Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (s : ℂ) :
    ‖interpWeight a b Ma Mb s‖ =
      Ma ^ (-((b - s.re) / (b - a))) * Mb ^ (-((s.re - a) / (b - a))) := by
  unfold interpWeight
  rw [Complex.norm_exp, Real.rpow_def_of_pos hMa, Real.rpow_def_of_pos hMb, ← Real.exp_add]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.div_ofReal_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

lemma norm_interpWeight_le_max {a b Ma Mb : ℝ} (hab : a < b) (hMa : 0 < Ma) (hMb : 0 < Mb)
    {s : ℂ} (hs1 : a ≤ s.re) (hs2 : s.re ≤ b) :
    ‖interpWeight a b Ma Mb s‖ ≤ max Ma⁻¹ Mb⁻¹ := by
  rw [norm_interpWeight hMa hMb s]
  have hba : 0 < b - a := sub_pos.mpr hab
  set θa := (b - s.re) / (b - a)
  set θb := (s.re - a) / (b - a)
  have hθa : 0 ≤ θa := div_nonneg (sub_nonneg.mpr hs2) hba.le
  have hθb : 0 ≤ θb := div_nonneg (sub_nonneg.mpr hs1) hba.le
  have hsum : θa + θb = 1 := by
    dsimp only [θa, θb]; field_simp [hba.ne']; ring
  have h1 : Ma ^ (-θa) = (Ma⁻¹) ^ θa := by
    rw [Real.inv_rpow hMa.le, Real.rpow_neg hMa.le]
  have h2 : Mb ^ (-θb) = (Mb⁻¹) ^ θb := by
    rw [Real.inv_rpow hMb.le, Real.rpow_neg hMb.le]
  rw [h1, h2]
  set M := max Ma⁻¹ Mb⁻¹
  have hMpos : 0 < M := lt_of_lt_of_le (inv_pos.mpr hMa) (le_max_left _ _)
  calc (Ma⁻¹) ^ θa * (Mb⁻¹) ^ θb
      ≤ M ^ θa * M ^ θb :=
        mul_le_mul (Real.rpow_le_rpow (inv_pos.mpr hMa).le (le_max_left _ _) hθa)
          (Real.rpow_le_rpow (inv_pos.mpr hMb).le (le_max_right _ _) hθb)
          (Real.rpow_nonneg (inv_pos.mpr hMb).le _) (Real.rpow_nonneg hMpos.le _)
    _ = M ^ (θa + θb) := (Real.rpow_add hMpos θa θb).symm
    _ = M := by rw [hsum, Real.rpow_one]

/-- **Phragmén–Lindelöf Vertical-Strip Convexity Theorem (Sub-Gaussian Growth, Direct `exp(ε s²)` Proof)**:
for `f` holomorphic on `a < Re s < b`, continuous on `a ≤ Re s ≤ b`, with sub-Gaussian growth
`‖f(s)‖ ≤ C exp(A |Im s|^α)` (`α < 2`) and boundary bounds `M_a, M_b > 0`,
`‖f(σ + i t)‖ ≤ M_a ^ ((b - σ)/(b - a)) * M_b ^ ((σ - a)/(b - a))`. -/
theorem phragmen_lindelof_convexity_subgaussian {a b C A α Ma Mb : ℝ}
    (hab : a < b) (hα : α < 2) (hMa : 0 < Ma) (hMb : 0 < Mb) {f : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hcont : ContinuousOn f (Complex.re ⁻¹' Set.Icc a b))
    (hgrow : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C * Real.exp (A * |s.im| ^ α))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ Ma)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ Mb)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    ‖f (σ + I * t)‖ ≤ Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set W := interpWeight a b Ma Mb
  set g : ℂ → ℂ := fun s => f s * W s
  have hdiff_g : DifferentiableOn ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    hdiff.mul (differentiable_interpWeight a b Ma Mb).differentiableOn
  have hcont_g : ContinuousOn g (Complex.re ⁻¹' Set.Icc a b) :=
    hcont.mul (differentiable_interpWeight a b Ma Mb).continuous.continuousOn
  have hgrow_g : ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖g s‖ ≤ (max C 0 * max Ma⁻¹ Mb⁻¹) * Real.exp (A * |s.im| ^ α) := by
    intro s h1 h2
    have hW := norm_interpWeight_le_max hab hMa hMb h1 h2
    have hM0 : 0 ≤ max Ma⁻¹ Mb⁻¹ := le_trans (inv_pos.mpr hMa).le (le_max_left _ _)
    calc ‖f s * W s‖ = ‖f s‖ * ‖W s‖ := norm_mul _ _
      _ ≤ (max C 0 * Real.exp (A * |s.im| ^ α)) * max Ma⁻¹ Mb⁻¹ :=
        mul_le_mul (le_trans (hgrow s h1 h2)
          (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le))
          hW (norm_nonneg _) (mul_nonneg (le_max_right C 0) (Real.exp_pos _).le)
      _ = (max C 0 * max Ma⁻¹ Mb⁻¹) * Real.exp (A * |s.im| ^ α) := by ring
  have hleft_g : ∀ τ : ℝ, ‖g (a + I * τ)‖ ≤ 1 := by
    intro τ
    change ‖f (a + I * τ) * W (a + I * τ)‖ ≤ 1
    rw [norm_mul, norm_interpWeight hMa hMb]
    have hre : ((a : ℂ) + I * (τ : ℂ)).re = a := by simp
    rw [hre, div_self hba.ne', sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one,
      Real.rpow_neg_one]
    calc ‖f (a + I * τ)‖ * Ma⁻¹ ≤ Ma * Ma⁻¹ :=
          mul_le_mul_of_nonneg_right (hleft τ) (inv_pos.mpr hMa).le
      _ = 1 := mul_inv_cancel₀ hMa.ne'
  have hright_g : ∀ τ : ℝ, ‖g (b + I * τ)‖ ≤ 1 := by
    intro τ
    change ‖f (b + I * τ) * W (b + I * τ)‖ ≤ 1
    rw [norm_mul, norm_interpWeight hMa hMb]
    have hre : ((b : ℂ) + I * (τ : ℂ)).re = b := by simp
    rw [hre, sub_self, zero_div, neg_zero, Real.rpow_zero, one_mul, div_self hba.ne',
      Real.rpow_neg_one]
    calc ‖f (b + I * τ)‖ * Mb⁻¹ ≤ Mb * Mb⁻¹ :=
          mul_le_mul_of_nonneg_right (hright τ) (inv_pos.mpr hMb).le
      _ = 1 := mul_inv_cancel₀ hMb.ne'
  have h1 := phragmen_lindelof_strip_subgaussian hab hα zero_le_one hdiff_g hcont_g hgrow_g
    hleft_g hright_g (s₀ := (σ : ℂ) + I * (t : ℂ)) (by simpa using hσ.1) (by simpa using hσ.2)
  change ‖f (σ + I * t) * W (σ + I * t)‖ ≤ 1 at h1
  rw [norm_mul, norm_interpWeight hMa hMb] at h1
  have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
  rw [hre] at h1
  have hp1 : 0 < Ma ^ ((b - σ) / (b - a)) := Real.rpow_pos_of_pos hMa _
  have hp2 : 0 < Mb ^ ((σ - a) / (b - a)) := Real.rpow_pos_of_pos hMb _
  rw [Real.rpow_neg hMa.le, Real.rpow_neg hMb.le] at h1
  have hmul : ‖f (σ + I * t)‖ * (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)))⁻¹ ≤ 1 := by
    simpa [mul_inv, mul_comm, mul_assoc] using h1
  calc ‖f (σ + I * t)‖
      = ‖f (σ + I * t)‖ * (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)))⁻¹ *
          (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a))) := by
        rw [mul_assoc, inv_mul_cancel₀ (mul_pos hp1 hp2).ne', mul_one]
    _ ≤ 1 * (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a))) :=
        mul_le_mul_of_nonneg_right hmul (mul_pos hp1 hp2).le
    _ = Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)) := one_mul _

/-- **Sharp Double-Exponential Phragmén–Lindelöf Vertical-Strip Convexity Theorem**:
extends Three-Lines convexity all the way to the optimal double-exponential growth rate
`f =O[|Im z| → ∞] exp(B * exp(c * |Im z|))` with `c < π / (b - a)`. -/
theorem phragmen_lindelof_convexity {a b Ma Mb : ℝ}
    (hab : a < b) (hMa : 0 < Ma) (hMb : 0 < Mb) {f : ℂ → ℂ}
    (hdf : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hgrow : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      f =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ Ma)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ Mb)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    ‖f (σ + I * t)‖ ≤ Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set W := interpWeight a b Ma Mb
  set g : ℂ → ℂ := fun s => f s * W s
  have hdg : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    ⟨hdf.1.mul (differentiable_interpWeight a b Ma Mb).differentiableOn,
      hdf.2.mul (differentiable_interpWeight a b Ma Mb).continuous.continuousOn⟩
  have hgrow_g : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      g =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    rcases hgrow with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    have hW_O : W =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo a b)] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨max Ma⁻¹ Mb⁻¹, ?_⟩
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz
      simpa using norm_interpWeight_le_max hab hMa hMb hz.1.le hz.2.le
    simpa [g] using hO.mul hW_O
  have hleft_g : ∀ z : ℂ, z.re = a → ‖g z‖ ≤ 1 := by
    intro z hz
    have heq : z = (a : ℂ) + I * (z.im : ℂ) := by apply Complex.ext <;> simp [hz]
    change ‖f z * W z‖ ≤ 1
    rw [norm_mul, norm_interpWeight hMa hMb, hz, div_self hba.ne', sub_self, zero_div,
      neg_zero, Real.rpow_zero, mul_one, Real.rpow_neg_one, heq]
    calc ‖f (a + I * z.im)‖ * Ma⁻¹ ≤ Ma * Ma⁻¹ :=
          mul_le_mul_of_nonneg_right (hleft z.im) (inv_pos.mpr hMa).le
      _ = 1 := mul_inv_cancel₀ hMa.ne'
  have hright_g : ∀ z : ℂ, z.re = b → ‖g z‖ ≤ 1 := by
    intro z hz
    have heq : z = (b : ℂ) + I * (z.im : ℂ) := by apply Complex.ext <;> simp [hz]
    change ‖f z * W z‖ ≤ 1
    rw [norm_mul, norm_interpWeight hMa hMb, hz, sub_self, zero_div, neg_zero, Real.rpow_zero,
      one_mul, div_self hba.ne', Real.rpow_neg_one, heq]
    calc ‖f (b + I * z.im)‖ * Mb⁻¹ ≤ Mb * Mb⁻¹ :=
          mul_le_mul_of_nonneg_right (hright z.im) (inv_pos.mpr hMb).le
      _ = 1 := mul_inv_cancel₀ hMb.ne'
  have h1 := PhragmenLindelof.vertical_strip hdg hgrow_g hleft_g hright_g
    (z := (σ : ℂ) + I * (t : ℂ)) (by simpa using hσ.1) (by simpa using hσ.2)
  change ‖f (σ + I * t) * W (σ + I * t)‖ ≤ 1 at h1
  rw [norm_mul, norm_interpWeight hMa hMb] at h1
  have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
  rw [hre] at h1
  have hp1 : 0 < Ma ^ ((b - σ) / (b - a)) := Real.rpow_pos_of_pos hMa _
  have hp2 : 0 < Mb ^ ((σ - a) / (b - a)) := Real.rpow_pos_of_pos hMb _
  rw [Real.rpow_neg hMa.le, Real.rpow_neg hMb.le] at h1
  have hmul : ‖f (σ + I * t)‖ * (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)))⁻¹ ≤ 1 := by
    simpa [mul_inv, mul_comm, mul_assoc] using h1
  calc ‖f (σ + I * t)‖
      = ‖f (σ + I * t)‖ * (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)))⁻¹ *
          (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a))) := by
        rw [mul_assoc, inv_mul_cancel₀ (mul_pos hp1 hp2).ne', mul_one]
    _ ≤ 1 * (Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a))) :=
        mul_le_mul_of_nonneg_right hmul (mul_pos hp1 hp2).le
    _ = Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)) := one_mul _

/-- Explicit pointwise-inequality wrapper for double-exponential vertical-strip convexity. -/
theorem phragmen_lindelof_convexity_double_exp {a b c B C Ma Mb : ℝ}
    (hab : a < b) (hc : c < Real.pi / (b - a)) (hMa : 0 < Ma) (hMb : 0 < Mb) {f : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hcont : ContinuousOn f (Complex.re ⁻¹' Set.Icc a b))
    (hgrow : ∀ s : ℂ, a < s.re → s.re < b → ‖f s‖ ≤ C * Real.exp (B * Real.exp (c * |s.im|)))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ Ma)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ Mb)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    ‖f (σ + I * t)‖ ≤ Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)) := by
  have hcl : closure (Complex.re ⁻¹' Set.Ioo a b) ⊆ Complex.re ⁻¹' Set.Icc a b := by
    refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) ?_
    exact isClosed_Icc.preimage Complex.continuous_re
  have hdf : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) := ⟨hdiff, hcont.mono hcl⟩
  have hO : ∃ c' < Real.pi / (b - a), ∃ B' : ℝ,
      f =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B' * Real.exp (c' * |z.im|)) := by
    refine ⟨c, hc, B, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨max C 0, ?_⟩
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_trans (hgrow z hz.1 hz.2)
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)
  exact phragmen_lindelof_convexity hab hMa hMb hdf hO hleft hright hσ t

/-- Key Gaussian-shift inequality for polynomial vertical-strip convexity:
for ALL `α, t, t₀ ∈ ℝ` (positive, negative, or zero `α`),
`(|t| + 2)^α * exp(-(t - t₀)²) ≤ exp(α² / 4) * (|t₀| + 2)^α`. -/
lemma rpow_add_two_mul_exp_neg_sq_le (α t t₀ : ℝ) :
    (|t| + 2) ^ α * Real.exp (-(t - t₀) ^ 2) ≤ Real.exp (α ^ 2 / 4) * (|t₀| + 2) ^ α := by
  have ht_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
  have ht0_pos : 0 < |t₀| + 2 := by linarith [abs_nonneg t₀]
  have hbase : ∀ u : ℝ, 0 ≤ u → (u + 1) ^ |α| * Real.exp (-(u ^ 2)) ≤ Real.exp (α ^ 2 / 4) := by
    intro u hu
    have h1 : (u + 1) ^ |α| ≤ Real.exp (|α| * u) := by
      calc (u + 1) ^ |α| ≤ (Real.exp u) ^ |α| :=
            Real.rpow_le_rpow (by linarith) (Real.add_one_le_exp u) (abs_nonneg α)
        _ = Real.exp (u * |α|) := (Real.exp_mul u |α|).symm
        _ = Real.exp (|α| * u) := by ring_nf
    calc (u + 1) ^ |α| * Real.exp (-(u ^ 2))
        ≤ Real.exp (|α| * u) * Real.exp (-(u ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (|α| * u - u ^ 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (α ^ 2 / 4) := by
          apply Real.exp_le_exp.mpr
          have hsq : 0 ≤ (u - |α| / 2) ^ 2 := sq_nonneg _
          have habs : |α| ^ 2 = α ^ 2 := sq_abs α
          nlinarith
  have hratio : (|t| + 2) ^ α ≤ (|t₀| + 2) ^ α * (|t - t₀| + 1) ^ |α| := by
    rcases le_total 0 α with hα | hα
    · rw [abs_of_nonneg hα]
      have htri : |t| + 2 ≤ (|t₀| + 2) * (|t - t₀| + 1) := by
        have h1 : |t| ≤ |t - t₀| + |t₀| := by
          have := abs_add_le (t - t₀) t₀
          simpa [sub_add_cancel] using this
        nlinarith [abs_nonneg (t - t₀), abs_nonneg t₀]
      calc (|t| + 2) ^ α ≤ ((|t₀| + 2) * (|t - t₀| + 1)) ^ α :=
            Real.rpow_le_rpow ht_pos.le htri hα
        _ = (|t₀| + 2) ^ α * (|t - t₀| + 1) ^ α :=
            Real.mul_rpow ht0_pos.le (by linarith [abs_nonneg (t - t₀)])
    · rw [abs_of_nonpos hα]
      have htri : |t₀| + 2 ≤ (|t| + 2) * (|t - t₀| + 1) := by
        have h1 : |t₀| ≤ |t - t₀| + |t| := by
          have := abs_add_le (t₀ - t) t
          rw [sub_add_cancel, abs_sub_comm] at this
          exact this
        nlinarith [abs_nonneg (t - t₀), abs_nonneg t]
      have hneg : 0 ≤ -α := neg_nonneg.mpr hα
      have hstep : (|t₀| + 2) ^ (-α) ≤ (|t| + 2) ^ (-α) * (|t - t₀| + 1) ^ (-α) := by
        calc (|t₀| + 2) ^ (-α) ≤ ((|t| + 2) * (|t - t₀| + 1)) ^ (-α) :=
              Real.rpow_le_rpow ht0_pos.le htri hneg
          _ = (|t| + 2) ^ (-α) * (|t - t₀| + 1) ^ (-α) :=
              Real.mul_rpow ht_pos.le (by linarith [abs_nonneg (t - t₀)])
      have hp1 : 0 < (|t| + 2) ^ α := Real.rpow_pos_of_pos ht_pos α
      have hp2 : 0 < (|t₀| + 2) ^ α := Real.rpow_pos_of_pos ht0_pos α
      rw [Real.rpow_neg ht0_pos.le, Real.rpow_neg ht_pos.le] at hstep
      have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hp1.le) hp2.le
      calc (|t| + 2) ^ α
          = (|t₀| + 2) ^ α * (((|t₀| + 2) ^ α)⁻¹ * (|t| + 2) ^ α) := by
            rw [← mul_assoc, mul_inv_cancel₀ hp2.ne', one_mul]
        _ ≤ (|t₀| + 2) ^ α * ((((|t| + 2) ^ α)⁻¹ * (|t - t₀| + 1) ^ (-α)) * (|t| + 2) ^ α) :=
            hmul
        _ = (|t₀| + 2) ^ α * (|t - t₀| + 1) ^ (-α) := by
            congr 1; rw [mul_right_comm, inv_mul_cancel₀ hp1.ne', one_mul]
  calc (|t| + 2) ^ α * Real.exp (-(t - t₀) ^ 2)
      ≤ ((|t₀| + 2) ^ α * (|t - t₀| + 1) ^ |α|) * Real.exp (-(|t - t₀| ^ 2)) := by
        rw [sq_abs (t - t₀)]
        exact mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
    _ = (|t₀| + 2) ^ α * ((|t - t₀| + 1) ^ |α| * Real.exp (-(|t - t₀| ^ 2))) := by ring
    _ ≤ (|t₀| + 2) ^ α * Real.exp (α ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (hbase |t - t₀| (abs_nonneg _)) (Real.rpow_pos_of_pos ht0_pos _).le
    _ = Real.exp (α ^ 2 / 4) * (|t₀| + 2) ^ α := mul_comm _ _

/-- **Polynomial Vertical-Strip Convexity Corollary (Sharp Double-Exponential Growth)**:
if `‖f(a + i t)‖ ≤ M_a (|t| + 2)^α` and `‖f(b + i t)‖ ≤ M_b (|t| + 2)^β`, then throughout
`a ≤ σ ≤ b`, `‖f(σ + i t)‖` is bounded by an explicit constant times `(|t| + 2)^ℓ(σ)` where
`ℓ(σ) = α (b - σ)/(b - a) + β (σ - a)/(b - a)` interpolates linearly between `α` and `β`. -/
theorem phragmen_lindelof_polynomial_convexity {a b Ma Mb α β : ℝ}
    (hab : a < b) (hMa : 0 < Ma) (hMb : 0 < Mb) {f : ℂ → ℂ}
    (hdf : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hgrow : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      f =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ Ma * (|t| + 2) ^ α)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ Mb * (|t| + 2) ^ β)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) (t₀ : ℝ) :
    ‖f (σ + I * t₀)‖ ≤
      Real.exp ((b - σ) * (σ - a) +
        (α ^ 2 / 4) * ((b - σ) / (b - a)) + (β ^ 2 / 4) * ((σ - a) / (b - a))) *
      Ma ^ ((b - σ) / (b - a)) * Mb ^ ((σ - a) / (b - a)) *
      (|t₀| + 2) ^ (α * ((b - σ) / (b - a)) + β * ((σ - a) / (b - a))) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set θa := (b - σ) / (b - a)
  set θb := (σ - a) / (b - a)
  have hθa : 0 ≤ θa := div_nonneg (sub_nonneg.mpr hσ.2) hba.le
  have hθb : 0 ≤ θb := div_nonneg (sub_nonneg.mpr hσ.1) hba.le
  have hθsum : θa + θb = 1 := by dsimp only [θa, θb]; field_simp [hba.ne']; ring
  -- Gaussian-shifted holomorphic function `g(s) = f(s) * exp((s - i t₀)²)`.
  set E : ℂ → ℂ := fun s => Complex.exp ((s - I * (t₀ : ℂ)) ^ 2)
  set g : ℂ → ℂ := fun s => f s * E s
  have hE_diff : Differentiable ℂ E := by
    unfold E; fun_prop
  have hE_norm : ∀ s : ℂ, ‖E s‖ = Real.exp (s.re ^ 2 - (s.im - t₀) ^ 2) := by
    intro s
    dsimp only [E]
    rw [Complex.norm_exp]
    congr 1
    simp [sq, Complex.mul_re, Complex.mul_im]
  have hdg : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    ⟨hdf.1.mul hE_diff.differentiableOn, hdf.2.mul hE_diff.continuous.continuousOn⟩
  have hgrow_g : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      g =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    rcases hgrow with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    have hE_O : E =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo a b)] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨Real.exp (max (a ^ 2) (b ^ 2)), ?_⟩
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz
      rw [hE_norm, norm_one, mul_one]
      apply Real.exp_le_exp.mpr
      have hre_sq : z.re ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
        rcases le_total 0 z.re with h0 | h0
        · exact le_trans (sq_le_sq.mpr (by rw [abs_of_nonneg h0]; exact le_trans hz.2.le (le_abs_self b)))
            (le_max_right _ _)
        · have ha0 : a ≤ 0 := le_trans hz.1.le h0
          have : |z.re| ≤ |a| := by rw [abs_of_nonpos h0, abs_of_nonpos ha0]; linarith [hz.1]
          exact le_trans (sq_le_sq.mpr this) (le_max_left _ _)
      linarith [sq_nonneg (z.im - t₀)]
    simpa [g] using hO.mul hE_O
  have ht0_pos : 0 < |t₀| + 2 := by linarith [abs_nonneg t₀]
  set Na := Ma * Real.exp (a ^ 2 + α ^ 2 / 4) * (|t₀| + 2) ^ α
  set Nb := Mb * Real.exp (b ^ 2 + β ^ 2 / 4) * (|t₀| + 2) ^ β
  have hNa : 0 < Na :=
    mul_pos (mul_pos hMa (Real.exp_pos _)) (Real.rpow_pos_of_pos ht0_pos α)
  have hNb : 0 < Nb :=
    mul_pos (mul_pos hMb (Real.exp_pos _)) (Real.rpow_pos_of_pos ht0_pos β)
  have hleft_g : ∀ t : ℝ, ‖g (a + I * t)‖ ≤ Na := by
    intro t
    change ‖f (a + I * t) * E (a + I * t)‖ ≤ Na
    rw [norm_mul, hE_norm]
    have hre : ((a : ℂ) + I * (t : ℂ)).re = a := by simp
    have him : ((a : ℂ) + I * (t : ℂ)).im = t := by simp
    rw [hre, him]
    calc ‖f (a + I * t)‖ * Real.exp (a ^ 2 - (t - t₀) ^ 2)
        ≤ (Ma * (|t| + 2) ^ α) * (Real.exp (a ^ 2) * Real.exp (-(t - t₀) ^ 2)) := by
          rw [← Real.exp_add, sub_eq_add_neg]
          exact mul_le_mul_of_nonneg_right (hleft t) (Real.exp_pos _).le
      _ = Ma * Real.exp (a ^ 2) * ((|t| + 2) ^ α * Real.exp (-(t - t₀) ^ 2)) := by ring
      _ ≤ Ma * Real.exp (a ^ 2) * (Real.exp (α ^ 2 / 4) * (|t₀| + 2) ^ α) :=
          mul_le_mul_of_nonneg_left (rpow_add_two_mul_exp_neg_sq_le α t t₀)
            (mul_pos hMa (Real.exp_pos _)).le
      _ = Na := by dsimp only [Na]; rw [Real.exp_add]; ring
  have hright_g : ∀ t : ℝ, ‖g (b + I * t)‖ ≤ Nb := by
    intro t
    change ‖f (b + I * t) * E (b + I * t)‖ ≤ Nb
    rw [norm_mul, hE_norm]
    have hre : ((b : ℂ) + I * (t : ℂ)).re = b := by simp
    have him : ((b : ℂ) + I * (t : ℂ)).im = t := by simp
    rw [hre, him]
    calc ‖f (b + I * t)‖ * Real.exp (b ^ 2 - (t - t₀) ^ 2)
        ≤ (Mb * (|t| + 2) ^ β) * (Real.exp (b ^ 2) * Real.exp (-(t - t₀) ^ 2)) := by
          rw [← Real.exp_add, sub_eq_add_neg]
          exact mul_le_mul_of_nonneg_right (hright t) (Real.exp_pos _).le
      _ = Mb * Real.exp (b ^ 2) * ((|t| + 2) ^ β * Real.exp (-(t - t₀) ^ 2)) := by ring
      _ ≤ Mb * Real.exp (b ^ 2) * (Real.exp (β ^ 2 / 4) * (|t₀| + 2) ^ β) :=
          mul_le_mul_of_nonneg_left (rpow_add_two_mul_exp_neg_sq_le β t t₀)
            (mul_pos hMb (Real.exp_pos _)).le
      _ = Nb := by dsimp only [Nb]; rw [Real.exp_add]; ring
  have hconv := phragmen_lindelof_convexity hab hNa hNb hdg hgrow_g hleft_g hright_g hσ t₀
  change ‖f (σ + I * t₀) * E (σ + I * t₀)‖ ≤ Na ^ θa * Nb ^ θb at hconv
  rw [norm_mul, hE_norm] at hconv
  have hre : ((σ : ℂ) + I * (t₀ : ℂ)).re = σ := by simp
  have him : ((σ : ℂ) + I * (t₀ : ℂ)).im = t₀ := by simp
  rw [hre, him, sub_self, zero_pow two_ne_zero, sub_zero] at hconv
  -- Simplify `Na^θa * Nb^θb / exp(σ²)`.
  have hNa_pow : Na ^ θa =
      Ma ^ θa * Real.exp ((a ^ 2 + α ^ 2 / 4) * θa) * (|t₀| + 2) ^ (α * θa) := by
    dsimp only [Na]
    rw [Real.mul_rpow (mul_pos hMa (Real.exp_pos _)).le (Real.rpow_pos_of_pos ht0_pos _).le,
      Real.mul_rpow hMa.le (Real.exp_pos _).le, ← Real.exp_mul, ← Real.rpow_mul ht0_pos.le]
  have hNb_pow : Nb ^ θb =
      Mb ^ θb * Real.exp ((b ^ 2 + β ^ 2 / 4) * θb) * (|t₀| + 2) ^ (β * θb) := by
    dsimp only [Nb]
    rw [Real.mul_rpow (mul_pos hMb (Real.exp_pos _)).le (Real.rpow_pos_of_pos ht0_pos _).le,
      Real.mul_rpow hMb.le (Real.exp_pos _).le, ← Real.exp_mul, ← Real.rpow_mul ht0_pos.le]
  have hquad : a ^ 2 * θa + b ^ 2 * θb - σ ^ 2 = (b - σ) * (σ - a) := by
    dsimp only [θa, θb]
    field_simp [hba.ne']
    ring
  have hdiv : ‖f (σ + I * t₀)‖ ≤ Na ^ θa * Nb ^ θb * Real.exp (-(σ ^ 2)) := by
    have hexp_pos : 0 < Real.exp (σ ^ 2) := Real.exp_pos _
    calc ‖f (σ + I * t₀)‖
        = ‖f (σ + I * t₀)‖ * Real.exp (σ ^ 2) * Real.exp (-(σ ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ Na ^ θa * Nb ^ θb * Real.exp (-(σ ^ 2)) :=
          mul_le_mul_of_nonneg_right hconv (Real.exp_pos _).le
  refine le_trans hdiv ?_
  rw [hNa_pow, hNb_pow]
  have hexp_comb :
      Real.exp ((a ^ 2 + α ^ 2 / 4) * θa) * Real.exp ((b ^ 2 + β ^ 2 / 4) * θb) *
        Real.exp (-(σ ^ 2)) =
      Real.exp ((b - σ) * (σ - a) + (α ^ 2 / 4) * θa + (β ^ 2 / 4) * θb) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linarith [hquad]
  have hrpow_comb :
      (|t₀| + 2) ^ (α * θa) * (|t₀| + 2) ^ (β * θb) =
      (|t₀| + 2) ^ (α * θa + β * θb) :=
    (Real.rpow_add ht0_pos _ _).symm
  calc Ma ^ θa * Real.exp ((a ^ 2 + α ^ 2 / 4) * θa) * (|t₀| + 2) ^ (α * θa) *
        (Mb ^ θb * Real.exp ((b ^ 2 + β ^ 2 / 4) * θb) * (|t₀| + 2) ^ (β * θb)) *
        Real.exp (-(σ ^ 2))
      = (Real.exp ((a ^ 2 + α ^ 2 / 4) * θa) * Real.exp ((b ^ 2 + β ^ 2 / 4) * θb) *
          Real.exp (-(σ ^ 2))) * Ma ^ θa * Mb ^ θb *
          ((|t₀| + 2) ^ (α * θa) * (|t₀| + 2) ^ (β * θb)) := by ring
    _ = Real.exp ((b - σ) * (σ - a) + (α ^ 2 / 4) * θa + (β ^ 2 / 4) * θb) *
          Ma ^ θa * Mb ^ θb * (|t₀| + 2) ^ (α * θa + β * θb) := by
        rw [hexp_comb, hrpow_comb]
    _ ≤ _ := le_rfl

/-- Uniform-constant existential form of Polynomial Vertical-Strip Convexity. -/
theorem phragmen_lindelof_polynomial_convexity_exists {a b Ma Mb α β : ℝ}
    (hab : a < b) (hMa : 0 < Ma) (hMb : 0 < Mb) {f : ℂ → ℂ}
    (hdf : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hgrow : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      f =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ Ma * (|t| + 2) ^ α)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ Mb * (|t| + 2) ^ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + I * t)‖ ≤
        C * (|t| + 2) ^ (α * ((b - σ) / (b - a)) + β * ((σ - a) / (b - a))) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set M := max Ma Mb
  have hM : 0 < M := lt_of_lt_of_le hMa (le_max_left _ _)
  set C := Real.exp ((b - a) ^ 2 / 4 + max (α ^ 2) (β ^ 2) / 4) * M
  refine ⟨C, mul_pos (Real.exp_pos _) hM, fun σ hσ t => ?_⟩
  have h1 := phragmen_lindelof_polynomial_convexity hab hMa hMb hdf hgrow hleft hright hσ t
  set θa := (b - σ) / (b - a)
  set θb := (σ - a) / (b - a)
  have hθa : 0 ≤ θa := div_nonneg (sub_nonneg.mpr hσ.2) hba.le
  have hθb : 0 ≤ θb := div_nonneg (sub_nonneg.mpr hσ.1) hba.le
  have hθsum : θa + θb = 1 := by dsimp only [θa, θb]; field_simp [hba.ne']; ring
  have hprod_le : (b - σ) * (σ - a) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((b - σ) - (σ - a))]
  have hab_sq : (α ^ 2 / 4) * θa + (β ^ 2 / 4) * θb ≤ max (α ^ 2) (β ^ 2) / 4 := by
    calc (α ^ 2 / 4) * θa + (β ^ 2 / 4) * θb
        ≤ (max (α ^ 2) (β ^ 2) / 4) * θa + (max (α ^ 2) (β ^ 2) / 4) * θb :=
          add_le_add
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)) hθa)
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num)) hθb)
      _ = (max (α ^ 2) (β ^ 2) / 4) * (θa + θb) := by ring
      _ = max (α ^ 2) (β ^ 2) / 4 := by rw [hθsum, mul_one]
  have hMpow : Ma ^ θa * Mb ^ θb ≤ M := by
    calc Ma ^ θa * Mb ^ θb
        ≤ M ^ θa * M ^ θb :=
          mul_le_mul (Real.rpow_le_rpow hMa.le (le_max_left _ _) hθa)
            (Real.rpow_le_rpow hMb.le (le_max_right _ _) hθb)
            (Real.rpow_nonneg hMb.le _) (Real.rpow_nonneg hM.le _)
      _ = M ^ (θa + θb) := (Real.rpow_add hM θa θb).symm
      _ = M := by rw [hθsum, Real.rpow_one]
  have hC_ge :
      Real.exp ((b - σ) * (σ - a) + (α ^ 2 / 4) * θa + (β ^ 2 / 4) * θb) *
        Ma ^ θa * Mb ^ θb ≤ C := by
    rw [mul_assoc]
    refine mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hMpow
      (mul_nonneg (Real.rpow_nonneg hMa.le _) (Real.rpow_nonneg hMb.le _)) (Real.exp_pos _).le
  exact le_trans h1 (mul_le_mul_of_nonneg_right hC_ge
    (Real.rpow_nonneg (by linarith [abs_nonneg t]) _))

/-- Convenience form of Polynomial Vertical-Strip Convexity under any finite-order growth
`‖f(s)‖ ≤ C₀ exp(A |Im s|^γ)` (in particular sub-Gaussian growth `γ < 2`). -/
theorem phragmen_lindelof_polynomial_convexity_subgaussian {a b C₀ A γ Ma Mb α β : ℝ}
    (hab : a < b) (hMa : 0 < Ma) (hMb : 0 < Mb) {f : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hcont : ContinuousOn f (Complex.re ⁻¹' Set.Icc a b))
    (hgrow : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C₀ * Real.exp (A * |s.im| ^ γ))
    (hleft : ∀ t : ℝ, ‖f (a + I * t)‖ ≤ Ma * (|t| + 2) ^ α)
    (hright : ∀ t : ℝ, ‖f (b + I * t)‖ ≤ Mb * (|t| + 2) ^ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + I * t)‖ ≤
        C * (|t| + 2) ^ (α * ((b - σ) / (b - a)) + β * ((σ - a) / (b - a))) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hcl : closure (Complex.re ⁻¹' Set.Ioo a b) ⊆ Complex.re ⁻¹' Set.Icc a b :=
    closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) (isClosed_Icc.preimage Complex.continuous_re)
  have hdf : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) := ⟨hdiff, hcont.mono hcl⟩
  -- Sub-Gaussian growth `exp(A |t|^γ)` (`γ < 2`) is strictly dominated by `exp(B exp(c |t|))`
  -- for any `0 < c < π / (b - a)`.
  set c := Real.pi / (2 * (b - a))
  have hc_pos : 0 < c := div_pos Real.pi_pos (by linarith)
  have hc_lt : c < Real.pi / (b - a) := by
    dsimp only [c]
    rw [div_lt_div_iff₀ (by linarith) hba]
    nlinarith [Real.pi_pos]
  have hO : ∃ c' < Real.pi / (b - a), ∃ B : ℝ,
      f =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c' * |z.im|)) := by
    refine ⟨c, hc_lt, 1, ?_⟩
    -- For large `u = |z.im|`, `A * u^γ ≤ exp(c * u)`.
    have hdom : ∀ᶠ u : ℝ in atTop, A * u ^ γ ≤ Real.exp (c * u) := by
      have hlittle : (fun u : ℝ => u ^ γ) =o[atTop] (fun u : ℝ => Real.exp (c * u)) := by
        have h := isLittleO_rpow_exp_atTop γ
        have hc_tend : Tendsto (fun u : ℝ => c * u) atTop atTop :=
          tendsto_id.const_mul_atTop hc_pos
        have hcomp := h.comp_tendsto hc_tend
        have hscale : (fun u : ℝ => (c * u) ^ γ) =ᶠ[atTop] fun u : ℝ => c ^ γ * u ^ γ := by
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
          exact Real.mul_rpow hc_pos.le hu
        have hcomp' := hcomp.congr' hscale EventuallyEq.rfl
        have hpos : c ^ γ ≠ 0 := (Real.rpow_pos_of_pos hc_pos γ).ne'
        simpa [Function.comp_def, inv_mul_cancel_left₀ hpos] using hcomp'.const_mul_left (c ^ γ)⁻¹
      have hbound := hlittle.bound (show (0 : ℝ) < (max |A| 1)⁻¹ by
        exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
      filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with u hu hu0
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hu0.le γ),
        Real.norm_of_nonneg (Real.exp_pos _).le] at hu
      have hM : 0 < max |A| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      calc A * u ^ γ ≤ max |A| 1 * u ^ γ :=
            mul_le_mul_of_nonneg_right (le_trans (le_abs_self A) (le_max_left _ _))
              (Real.rpow_nonneg hu0.le γ)
        _ ≤ max |A| 1 * ((max |A| 1)⁻¹ * Real.exp (c * u)) :=
            mul_le_mul_of_nonneg_left hu hM.le
        _ = Real.exp (c * u) := by rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
    rw [Asymptotics.isBigO_iff]
    refine ⟨max C₀ 0, ?_⟩
    filter_upwards [Filter.mem_inf_of_left (Filter.preimage_mem_comap hdom),
      Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz1 hz2
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    calc ‖f z‖ ≤ C₀ * Real.exp (A * |z.im| ^ γ) := hgrow z hz2.1.le hz2.2.le
      _ ≤ max C₀ 0 * Real.exp (A * |z.im| ^ γ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C₀ 0 * Real.exp (Real.exp (c * |z.im|)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz1) (le_max_right _ _)
  exact phragmen_lindelof_polynomial_convexity_exists hab hMa hMb hdf hO hleft hright

/-! ## Section 2: Concrete Bounds on Mathlib's `Complex.Gamma`, `Real.Gamma`, `Stirling`, & `Complex.digamma` -/

/-- **Integral Modulus Bound for Mathlib's `Complex.Gamma`**:
for all `s : ℂ` with `0 < s.re`, `‖Complex.Gamma s‖ ≤ Real.Gamma s.re`. -/
theorem norm_Gamma_le_real_Gamma {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine le_of_eq (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
  have hx_pos : 0 < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
  simp

/-- Vertical-line specialization: `‖Complex.Gamma (σ + I * t)‖ ≤ Real.Gamma σ` for `σ > 0`. -/
theorem norm_Gamma_add_I_mul_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖Complex.Gamma (σ + I * t)‖ ≤ Real.Gamma σ := by
  have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
  simpa [hre] using norm_Gamma_le_real_Gamma (s := (σ : ℂ) + I * (t : ℂ)) (by simpa using hσ)

/-- Convexity bound: `Real.Gamma σ ≤ 1` for all `σ ∈ [1, 2]`. -/
theorem real_Gamma_le_one_of_mem_Icc {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) :
    Real.Gamma σ ≤ 1 := by
  have hconv := Real.convexOn_Gamma.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 2 - σ by linarith) (show (0 : ℝ) ≤ σ - 1 by linarith) (by ring)
  have hcomb : (2 - σ) • (1 : ℝ) + (σ - 1) • (2 : ℝ) = σ := by simp; ring
  rw [hcomb, Real.Gamma_one, Real.Gamma_two, smul_eq_mul, smul_eq_mul] at hconv
  linarith

/-- Pole-adjacent bound: `Real.Gamma σ ≤ 1 / σ` for all `0 < σ ≤ 1`. -/
theorem real_Gamma_le_inv_of_Ioc {σ : ℝ} (h0 : 0 < σ) (h1 : σ ≤ 1) :
    Real.Gamma σ ≤ 1 / σ := by
  have hrec := Real.Gamma_add_one h0.ne'
  have hle : Real.Gamma (σ + 1) ≤ 1 :=
    real_Gamma_le_one_of_mem_Icc (by linarith) (by linarith)
  rw [le_div_iff₀ h0, mul_comm, ← hrec]
  exact hle

/-- Real Gamma factorial shift identity:
`Real.Gamma (x + n) = (∏ j ∈ Finset.range n, (x + j)) * Real.Gamma x` for `x > 0`. -/
theorem real_Gamma_add_nat_eq_prod {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = (∏ j ∈ Finset.range n, (x + j)) * Real.Gamma x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by positivity
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hxn.ne', ih, Finset.prod_range_succ]
    ring

/-- Complex Gamma factorial shift identity:
`Complex.Gamma (s + n) = (∏ j ∈ Finset.range n, (s + j)) * Complex.Gamma s` for `s.re > 0`. -/
theorem Gamma_add_nat_eq_prod {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Complex.Gamma (s + n) = (∏ j ∈ Finset.range n, (s + j)) * Complex.Gamma s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : s + (n : ℂ) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hsn, ih, Finset.prod_range_succ]
    ring

/-- Explicit factorial-shift upper bound on `Real.Gamma σ` for `σ ≥ 1`:
`Real.Gamma σ ≤ σ ^ (σ - 1)`. -/
theorem real_Gamma_le_rpow_sub_one {σ : ℝ} (hσ : 1 ≤ σ) :
    Real.Gamma σ ≤ σ ^ (σ - 1) := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  set m : ℕ := ⌊σ⌋₊
  have hm_ge : 1 ≤ m := Nat.le_floor (by simpa using hσ)
  set n : ℕ := m - 1
  have hmn : (m : ℝ) = (n : ℝ) + 1 := by
    have : m = n + 1 := (Nat.sub_add_cancel hm_ge).symm
    exact_mod_cast this
  set x : ℝ := σ - n
  have hx1 : 1 ≤ x := by
    have hle : (m : ℝ) ≤ σ := Nat.floor_le hσ_pos.le
    dsimp only [x]; linarith
  have hx2 : x ≤ 2 := by
    have hlt : σ < (m : ℝ) + 1 := Nat.lt_floor_add_one σ
    dsimp only [x]; linarith
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hσ_eq : σ = x + n := by dsimp only [x]; ring
  rw [hσ_eq, real_Gamma_add_nat_eq_prod hx_pos n, ← hσ_eq]
  have hprod_le : ∏ j ∈ Finset.range n, (x + j) ≤ σ ^ n := by
    have h1 : ∏ j ∈ Finset.range n, (x + j) ≤ ∏ _j ∈ Finset.range n, σ := by
      refine Finset.prod_le_prod (fun j _ => by positivity) (fun j hj => ?_)
      have hj_lt : (j : ℝ) < (n : ℝ) := by exact_mod_cast Finset.mem_range.mp hj
      linarith
    simpa [Finset.prod_const, Finset.card_range] using h1
  have hGx : Real.Gamma x ≤ 1 := real_Gamma_le_one_of_mem_Icc hx1 hx2
  have hn_le : (n : ℝ) ≤ σ - 1 := by linarith
  calc (∏ j ∈ Finset.range n, (x + j)) * Real.Gamma x
      ≤ σ ^ n * 1 :=
        mul_le_mul hprod_le hGx (Real.Gamma_pos_of_pos hx_pos).le (pow_nonneg hσ_pos.le n)
    _ = σ ^ (n : ℝ) := by rw [mul_one, Real.rpow_natCast]
    _ ≤ σ ^ (σ - 1) := Real.rpow_le_rpow_of_exponent_le hσ hn_le

/-- Explicit upper bound `Real.Gamma σ ≤ σ ^ σ` for `σ ≥ 1`. -/
theorem real_Gamma_le_rpow_self {σ : ℝ} (hσ : 1 ≤ σ) :
    Real.Gamma σ ≤ σ ^ σ :=
  le_trans (real_Gamma_le_rpow_sub_one hσ)
    (Real.rpow_le_rpow_of_exponent_le hσ (by linarith))

/-- Concrete two-sided Stirling bounds for `n! = Real.Gamma (n + 1)` (`n ≥ 1`) directly from
Mathlib's `Stirling`: `√(2 π n) (n / e)^n ≤ n! ≤ e √n (n / e)^n`. -/
theorem factorial_stirling_bounds {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n ≤ n.factorial ∧
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
  refine ⟨Stirling.le_factorial_stirling n, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  have hanti : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.stirlingSeq_one] at hanti
  have hden_pos : 0 < Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
    positivity
  have hdef : Stirling.stirlingSeq (k + 1) =
      ((k + 1).factorial : ℝ) /
        (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) :=
    Stirling.stirlingSeq.eq_1 (k + 1)
  rw [hdef, div_le_iff₀ hden_pos] at hanti
  have hsqrt : Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have hsq2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  calc ((k + 1).factorial : ℝ)
      ≤ Real.exp 1 / Real.sqrt 2 *
          (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := hanti
    _ = Real.exp 1 * Real.sqrt ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
        rw [hsqrt]
        field_simp [hsq2_ne]

/-- **Explicit Factorial-Shift Upper Bound for Mathlib's `Complex.Gamma`**:
for every `s : ℂ` with `1 ≤ s.re`, `‖Complex.Gamma s‖ ≤ (‖s‖ + 1) ^ s.re`. -/
theorem norm_Gamma_le_norm_add_one_rpow {s : ℂ} (hs : 1 ≤ s.re) :
    ‖Complex.Gamma s‖ ≤ (‖s‖ + 1) ^ s.re := by
  have hs_pos : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  calc ‖Complex.Gamma s‖
      ≤ Real.Gamma s.re := norm_Gamma_le_real_Gamma hs_pos
    _ ≤ s.re ^ s.re := real_Gamma_le_rpow_self hs
    _ ≤ (‖s‖ + 1) ^ s.re := by
        refine Real.rpow_le_rpow hs_pos.le ?_ hs_pos.le
        have hre : s.re ≤ ‖s‖ := le_trans (le_abs_self s.re) (Complex.abs_re_le_norm s)
        linarith

/-- Explicit upper bound on `Complex.Gamma` for `1 / 2 ≤ s.re`:
`‖Complex.Gamma s‖ ≤ 2 * (‖s‖ + 1) ^ s.re`. -/
theorem norm_Gamma_le_of_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Complex.Gamma s‖ ≤ 2 * (‖s‖ + 1) ^ s.re := by
  have hs_pos : 0 < s.re := by linarith
  rcases le_or_gt 1 s.re with h1 | hlt
  · have h := norm_Gamma_le_norm_add_one_rpow h1
    have hnonneg : 0 ≤ (‖s‖ + 1) ^ s.re := Real.rpow_nonneg (by linarith [norm_nonneg s]) _
    linarith
  · calc ‖Complex.Gamma s‖
        ≤ Real.Gamma s.re := norm_Gamma_le_real_Gamma hs_pos
      _ ≤ 1 / s.re := real_Gamma_le_inv_of_Ioc hs_pos hlt.le
      _ ≤ 2 := by rw [div_le_iff₀ hs_pos]; linarith
      _ ≤ 2 * (‖s‖ + 1) ^ s.re := by
          have hpow : 1 ≤ (‖s‖ + 1) ^ s.re :=
            Real.one_le_rpow (by linarith [norm_nonneg s]) hs_pos.le
          linarith

/-- Explicit upper bound on `Complex.Gamma` for all `0 < s.re`:
`‖Complex.Gamma s‖ ≤ (1 / s.re) * (s.re + 1) ^ s.re`. -/
theorem norm_Gamma_le_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ (1 / s.re) * (s.re + 1) ^ s.re := by
  have h1 : 1 ≤ s.re + 1 := by linarith
  have hrec := Real.Gamma_add_one hs.ne'
  have hle : Real.Gamma (s.re + 1) ≤ (s.re + 1) ^ s.re := by
    simpa [add_sub_cancel_right] using real_Gamma_le_rpow_sub_one h1
  calc ‖Complex.Gamma s‖
      ≤ Real.Gamma s.re := norm_Gamma_le_real_Gamma hs
    _ = Real.Gamma (s.re + 1) / s.re := by
        rw [hrec, mul_div_cancel_left₀ _ hs.ne']
    _ ≤ (s.re + 1) ^ s.re / s.re := div_le_div_of_nonneg_right hle hs.le
    _ = (1 / s.re) * (s.re + 1) ^ s.re := by ring

/-- **Exact Reflection Formula Modulus on the Critical Line `Re(s) = 1/2`**:
`‖Complex.Gamma (1 / 2 + I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t)`. -/
theorem norm_sq_Gamma_half_add_I_mul (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  have h1sub : (1 : ℂ) - z = starRingEnd ℂ z := by
    apply Complex.ext
    · simp [z]; norm_num
    · simp [z]
  have hprod : Complex.Gamma z * Complex.Gamma (1 - z) =
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    rw [h1sub, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * t) : ℂ) := by
    have harg : (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I + (Real.pi : ℂ) / 2 := by
      dsimp only [z]; push_cast; ring
    rw [harg, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hprod, hsin, ← Complex.ofReal_div] at hrefl
  exact Complex.ofReal_injective hrefl

/-- Exact critical-line modulus `‖Complex.Gamma (1/2 + I * t)‖ = √(π / cosh(π t))`. -/
theorem norm_Gamma_half_add_I_mul_eq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ = Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
  rw [← norm_sq_Gamma_half_add_I_mul t, Real.sqrt_sq (norm_nonneg _)]

/-- **Exact Exponential Decay on `Re(s) = 1/2`**:
`‖Complex.Gamma (1 / 2 + I * t)‖ ≤ √(2 π) * exp(-π |t| / 2)`. -/
theorem norm_Gamma_half_add_I_mul_le (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2) := by
  have hcosh_ge : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    have hpos1 : 0 < Real.exp (Real.pi * t) := Real.exp_pos _
    have hpos2 : 0 < Real.exp (-(Real.pi * t)) := Real.exp_pos _
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]; linarith
    · rw [abs_of_nonpos ht, mul_neg]; linarith
  have hcosh_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hexp_pos : 0 < Real.exp (Real.pi * |t|) / 2 := by positivity
  have hsq : ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
      (Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2)) ^ 2 := by
    rw [norm_sq_Gamma_half_add_I_mul t, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have h1 : Real.pi / Real.cosh (Real.pi * t) ≤ Real.pi / (Real.exp (Real.pi * |t|) / 2) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hexp_pos hcosh_ge
    refine le_trans h1 (le_of_eq ?_)
    have h2 : ((2 : ℕ) : ℝ) * (-Real.pi * |t| / 2) = -(Real.pi * |t|) := by push_cast; ring
    rw [h2, Real.exp_neg]
    field_simp [(Real.exp_pos _).ne']
  have hrhs_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2) := by positivity
  nlinarith [sq_nonneg (Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2) -
    ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖),
    norm_nonneg (Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ)))]

/-- Matching exact exponential lower bound on `Re(s) = 1/2`:
`√π * exp(-π |t| / 2) ≤ ‖Complex.Gamma (1 / 2 + I * t)‖`. -/
theorem norm_Gamma_half_add_I_mul_ge (t : ℝ) :
    Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2) ≤
      ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ := by
  have hcosh_le : Real.cosh (Real.pi * t) ≤ Real.exp (Real.pi * |t|) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (Real.pi * t) ≤ Real.exp (Real.pi * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) Real.pi_pos.le)
    have h2 : Real.exp (-(Real.pi * t)) ≤ Real.exp (Real.pi * |t|) :=
      Real.exp_le_exp.mpr (by
        have : -t ≤ |t| := neg_le_abs t
        nlinarith [Real.pi_pos])
    linarith
  have hsq : (Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2)) ^ 2 ≤
      ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 := by
    rw [norm_sq_Gamma_half_add_I_mul t, mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Real.exp_nat_mul]
    have h1 : Real.pi / Real.exp (Real.pi * |t|) ≤ Real.pi / Real.cosh (Real.pi * t) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (Real.cosh_pos _) hcosh_le
    refine le_trans (le_of_eq ?_) h1
    have h2 : ((2 : ℕ) : ℝ) * (-Real.pi * |t| / 2) = -(Real.pi * |t|) := by push_cast; ring
    rw [h2, Real.exp_neg]
    field_simp [(Real.exp_pos _).ne']
  have hlhs_nonneg : 0 ≤ Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2) := by positivity
  nlinarith [sq_nonneg (‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ -
    Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2)),
    norm_nonneg (Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ)))]

/-- Exact reflection formula modulus on the 1-line `Re(s) = 1`:
`‖Complex.Gamma (1 + I * t)‖ ^ 2 = (π * t) / Real.sinh (π * t)` for `t ≠ 0`. -/
theorem norm_sq_Gamma_one_add_I_mul {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + I * (t : ℂ))‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  set z : ℂ := I * (t : ℂ)
  have hz_ne : z ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht)
  have h1sub : (1 : ℂ) - z = starRingEnd ℂ (1 + z) := by
    apply Complex.ext <;> simp [z]
  have hprod : Complex.Gamma (1 + z) * Complex.Gamma (1 - z) =
      ((‖Complex.Gamma (1 + z)‖ ^ 2 : ℝ) : ℂ) := by
    rw [h1sub, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hshift : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    rw [add_comm, Complex.Gamma_add_one z hz_ne]
  have hrefl : Complex.Gamma (1 + z) * Complex.Gamma (1 - z) =
      z * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z)) := by
    rw [hshift, mul_assoc, Complex.Gamma_mul_Gamma_one_sub z]
  have hsin : Complex.sin ((Real.pi : ℂ) * z) = (Real.sinh (Real.pi * t) : ℂ) * I := by
    have harg : (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I := by
      dsimp only [z]; push_cast; ring
    rw [harg, Complex.sin_mul_I, Complex.ofReal_sinh]
  rw [hprod, hsin] at hrefl
  have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hsinh_ne : (Real.sinh (Real.pi * t) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro h0
    rw [Real.sinh_eq] at h0
    have heq : Real.exp (Real.pi * t) = Real.exp (-(Real.pi * t)) := by linarith
    have harg0 := Real.exp_injective heq
    have hpt : Real.pi * t = 0 := by linarith
    exact mul_ne_zero Real.pi_pos.ne' ht hpt
  have hrhs : z * ((Real.pi : ℂ) / ((Real.sinh (Real.pi * t) : ℂ) * I)) =
      ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    dsimp only [z]
    push_cast
    field_simp [hI_ne, hsinh_ne]
  rw [hrhs] at hrefl
  exact Complex.ofReal_injective hrefl

/-- Exponential decay along shifted half-integer vertical lines `Re(s) = 1/2 + n`:
`‖Complex.Gamma (1/2 + n + I * t)‖ ≤ (|t| + n + 1)^n * √(2 π) * exp(-π |t| / 2)`. -/
theorem norm_Gamma_half_add_nat_add_I_mul_le (n : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (n : ℂ) + I * (t : ℂ))‖ ≤
      (|t| + n + 1) ^ n * Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2) := by
  have heq : (1 / 2 : ℂ) + (n : ℂ) + I * (t : ℂ) = ((1 / 2 : ℂ) + I * (t : ℂ)) + (n : ℂ) := by
    ring
  rw [heq, Gamma_add_nat_eq_prod (by simp : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re) n,
    norm_mul, norm_prod]
  have hprod_le : ∏ j ∈ Finset.range n, ‖(1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)‖ ≤
      (|t| + n + 1) ^ n := by
    have h1 : ∏ j ∈ Finset.range n, ‖(1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)‖ ≤
        ∏ _j ∈ Finset.range n, (|t| + n + 1) := by
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j hj => ?_)
      have hj_le : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hre : ((1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)).re = 1 / 2 + (j : ℝ) := by simp
      have him : ((1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)).im = t := by simp
      calc ‖(1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)‖
          ≤ |((1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)).re| +
            |((1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 + (j : ℝ)) + |t| := by
            rw [hre, him, abs_of_nonneg (by positivity)]
        _ ≤ |t| + n + 1 := by linarith
    simpa [Finset.prod_const, Finset.card_range] using h1
  calc (∏ j ∈ Finset.range n, ‖(1 / 2 : ℂ) + I * (t : ℂ) + (j : ℂ)‖) *
        ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖
      ≤ (|t| + n + 1) ^ n * (Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2)) :=
        mul_le_mul hprod_le (norm_Gamma_half_add_I_mul_le t) (norm_nonneg _) (by positivity)
    _ = (|t| + n + 1) ^ n * Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2) := by ring

/-- **Full Complex Stirling Vertical-Strip Upper Bound via Phragmén–Lindelöf Convexity**:
for every `b : ℝ`, there is `C > 0` such that on the entire vertical strip `1 / 2 ≤ σ ≤ b`,
`‖Complex.Gamma (σ + I * t)‖ ≤ C * (|t| + 2) ^ (σ - 1 / 2) * Real.exp (-Real.pi * |t| / 2)`. -/
theorem norm_Gamma_strip_stirling_upper (b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (1 / 2 : ℝ) b, ∀ t : ℝ,
      ‖Complex.Gamma (σ + I * t)‖ ≤
        C * (|t| + 2) ^ (σ - 1 / 2) * Real.exp (-Real.pi * |t| / 2) := by
  set N : ℕ := max 1 ⌈b - 1 / 2⌉₊
  have hN_pos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hN_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hb_le : b ≤ 1 / 2 + (N : ℝ) := by
    have h1 : b - 1 / 2 ≤ (⌈b - 1 / 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈b - 1 / 2⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right 1 ⌈b - 1 / 2⌉₊
    linarith
  set a : ℝ := 1 / 2
  set b' : ℝ := 1 / 2 + (N : ℝ)
  have hab' : a < b' := by dsimp only [a, b']; linarith
  -- Auxiliary holomorphic function `h(s) = Γ(s) * exp(-(π/2) i s)` with `‖h(σ+it)‖ = ‖Γ(σ+it)‖ exp(π t / 2)`.
  set h : ℂ → ℂ := fun s => Complex.Gamma s * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * s)
  have hnorm_exp : ∀ s : ℂ,
      ‖Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * s)‖ = Real.exp (Real.pi / 2 * s.im) := by
    intro s
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hdiff_h : DifferentiableOn ℂ h (Complex.re ⁻¹' Set.Ioo a b') := by
    intro s hs
    have hne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m heq
      have hre := congrArg Complex.re heq
      simp at hre
      have : (0 : ℝ) < s.re := lt_trans (by norm_num : (0 : ℝ) < a) hs.1
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have h1 : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s hne
    have h2 : DifferentiableAt ℂ (fun z => Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * z)) s := by
      fun_prop
    exact (h1.mul h2).differentiableWithinAt
  have hcont_h : ContinuousOn h (Complex.re ⁻¹' Set.Icc a b') := by
    intro s hs
    have hne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m heq
      have hre := congrArg Complex.re heq
      simp at hre
      have : (0 : ℝ) < s.re := lt_of_lt_of_le (by norm_num : (0 : ℝ) < a) hs.1
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have h1 : ContinuousAt Complex.Gamma s := Complex.continuousAt_Gamma s hne
    have h2 : ContinuousAt (fun z => Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * z)) s := by
      fun_prop
    exact (h1.mul h2).continuousWithinAt
  -- Uniform strip bound on `‖Γ(s)‖`: `‖Γ(s)‖ ≤ 2 * (b' + 1) ^ b'`.
  set C₀ : ℝ := 2 * (b' + 1) ^ b'
  have hgrow_h : ∀ s : ℂ, a ≤ s.re → s.re ≤ b' →
      ‖h s‖ ≤ C₀ * Real.exp ((Real.pi / 2) * |s.im| ^ (1 : ℝ)) := by
    intro s hs1 hs2
    have hs_pos : 0 < s.re := lt_of_lt_of_le (by norm_num : (0 : ℝ) < a) hs1
    have hG : ‖Complex.Gamma s‖ ≤ C₀ := by
      calc ‖Complex.Gamma s‖
          ≤ (1 / s.re) * (s.re + 1) ^ s.re := norm_Gamma_le_of_re_pos hs_pos
        _ ≤ 2 * (b' + 1) ^ b' := by
            have hinv : 1 / s.re ≤ 2 := by
              rw [div_le_iff₀ hs_pos]; dsimp only [a] at hs1; linarith
            have hpow : (s.re + 1) ^ s.re ≤ (b' + 1) ^ b' := by
              calc (s.re + 1) ^ s.re
                  ≤ (b' + 1) ^ s.re := Real.rpow_le_rpow (by linarith) (by linarith) hs_pos.le
                _ ≤ (b' + 1) ^ b' := Real.rpow_le_rpow_of_exponent_le (by linarith) hs2
            exact mul_le_mul hinv hpow (Real.rpow_nonneg (by linarith) _) (by norm_num)
    change ‖Complex.Gamma s * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * s)‖ ≤ _
    rw [norm_mul, hnorm_exp, Real.rpow_one]
    refine mul_le_mul hG (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left (le_abs_self s.im) (by positivity)
  set Ma : ℝ := Real.sqrt (2 * Real.pi)
  have hMa : 0 < Ma := Real.sqrt_pos.mpr (by positivity)
  have hleft_h : ∀ t : ℝ, ‖h (a + I * t)‖ ≤ Ma * (|t| + 2) ^ (0 : ℝ) := by
    intro t
    have ha_cast : (a : ℂ) = (1 / 2 : ℂ) := by dsimp only [a]; push_cast; rfl
    rw [ha_cast]
    change ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ)) *
      Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * ((1 / 2 : ℂ) + I * (t : ℂ)))‖ ≤ _
    rw [norm_mul, hnorm_exp, Real.rpow_zero, mul_one]
    have him : ((1 / 2 : ℂ) + I * (t : ℂ)).im = t := by simp
    rw [him]
    calc ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ * Real.exp (Real.pi / 2 * t)
        ≤ (Ma * Real.exp (-Real.pi * |t| / 2)) * Real.exp (Real.pi / 2 * t) :=
          mul_le_mul_of_nonneg_right (norm_Gamma_half_add_I_mul_le t) (Real.exp_pos _).le
      _ = Ma * Real.exp (Real.pi / 2 * (t - |t|)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ Ma * Real.exp 0 := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hMa.le
          have : t - |t| ≤ 0 := sub_nonpos.mpr (le_abs_self t)
          nlinarith [Real.pi_pos]
      _ = Ma := by rw [Real.exp_zero, mul_one]
  set Mb : ℝ := (N + 1 : ℝ) ^ N * Real.sqrt (2 * Real.pi)
  have hMb : 0 < Mb := by positivity
  have hright_h : ∀ t : ℝ, ‖h (b' + I * t)‖ ≤ Mb * (|t| + 2) ^ (N : ℝ) := by
    intro t
    have hb'_eq : (b' : ℂ) + I * (t : ℂ) = (1 / 2 : ℂ) + (N : ℂ) + I * (t : ℂ) := by
      dsimp only [b']; push_cast; ring
    change ‖Complex.Gamma ((b' : ℂ) + I * (t : ℂ)) *
      Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * ((b' : ℂ) + I * (t : ℂ)))‖ ≤ _
    rw [norm_mul, hnorm_exp]
    have him : ((b' : ℂ) + I * (t : ℂ)).im = t := by simp
    rw [him, hb'_eq]
    have hlin : |t| + (N : ℝ) + 1 ≤ ((N : ℝ) + 1) * (|t| + 2) := by
      nlinarith [abs_nonneg t, hN_real]
    have hpow : (|t| + (N : ℝ) + 1) ^ N ≤ ((N : ℝ) + 1) ^ N * (|t| + 2) ^ (N : ℝ) := by
      rw [Real.rpow_natCast, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hlin N
    calc ‖Complex.Gamma ((1 / 2 : ℂ) + (N : ℂ) + I * (t : ℂ))‖ * Real.exp (Real.pi / 2 * t)
        ≤ ((|t| + (N : ℝ) + 1) ^ N * Real.sqrt (2 * Real.pi) * Real.exp (-Real.pi * |t| / 2)) *
            Real.exp (Real.pi / 2 * t) :=
          mul_le_mul_of_nonneg_right (norm_Gamma_half_add_nat_add_I_mul_le N t) (Real.exp_pos _).le
      _ = (|t| + (N : ℝ) + 1) ^ N * Real.sqrt (2 * Real.pi) *
            Real.exp (Real.pi / 2 * (t - |t|)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ (|t| + (N : ℝ) + 1) ^ N * Real.sqrt (2 * Real.pi) * Real.exp 0 := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have : t - |t| ≤ 0 := sub_nonpos.mpr (le_abs_self t)
          nlinarith [Real.pi_pos]
      _ = (|t| + (N : ℝ) + 1) ^ N * Real.sqrt (2 * Real.pi) := by rw [Real.exp_zero, mul_one]
      _ ≤ (((N : ℝ) + 1) ^ N * (|t| + 2) ^ (N : ℝ)) * Real.sqrt (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)
      _ = Mb * (|t| + 2) ^ (N : ℝ) := by dsimp only [Mb]; ring
  obtain ⟨C, hC_pos, hC⟩ :=
    phragmen_lindelof_polynomial_convexity_subgaussian hab' hMa hMb
      hdiff_h hcont_h hgrow_h hleft_h hright_h
  refine ⟨C, hC_pos, fun σ hσ t => ?_⟩
  have hσ' : σ ∈ Set.Icc a b' := ⟨hσ.1, le_trans hσ.2 hb_le⟩
  have hexp_eq : (0 : ℝ) * ((b' - σ) / (b' - a)) + (N : ℝ) * ((σ - a) / (b' - a)) = σ - 1 / 2 := by
    dsimp only [a, b']
    have hsub : 1 / 2 + (N : ℝ) - 1 / 2 = (N : ℝ) := by ring
    rw [hsub, zero_mul, zero_add, mul_div_cancel₀ _ hN_real.ne']
  have hpos_t : ∀ u : ℝ, 0 ≤ u →
      ‖Complex.Gamma (σ + I * u)‖ ≤ C * (|u| + 2) ^ (σ - 1 / 2) * Real.exp (-Real.pi * |u| / 2) := by
    intro u hu
    have h1 := hC σ hσ' u
    rw [hexp_eq] at h1
    change ‖Complex.Gamma (σ + I * u) *
      Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I * (σ + I * u))‖ ≤ _ at h1
    rw [norm_mul, hnorm_exp] at h1
    have him : ((σ : ℂ) + I * (u : ℂ)).im = u := by simp
    rw [him] at h1
    calc ‖Complex.Gamma (σ + I * u)‖
        = ‖Complex.Gamma (σ + I * u)‖ * Real.exp (Real.pi / 2 * u) *
            Real.exp (-Real.pi * |u| / 2) := by
          rw [abs_of_nonneg hu, mul_assoc, ← Real.exp_add]
          have : Real.pi / 2 * u + -Real.pi * u / 2 = 0 := by ring
          rw [this, Real.exp_zero, mul_one]
      _ ≤ C * (|u| + 2) ^ (σ - 1 / 2) * Real.exp (-Real.pi * |u| / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  rcases le_total 0 t with ht | ht
  · exact hpos_t t ht
  · have hconj : ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ =
        ‖Complex.Gamma ((σ : ℂ) + I * ((-t : ℝ) : ℂ))‖ := by
      have harg : (σ : ℂ) + I * ((-t : ℝ) : ℂ) = starRingEnd ℂ ((σ : ℂ) + I * (t : ℂ)) := by
        apply Complex.ext <;> simp
      rw [harg, Complex.Gamma_conj, Complex.norm_conj]
    rw [hconj, ← abs_neg t]
    exact hpos_t (-t) (neg_nonneg.mpr ht)

/-- Complex digamma finite-shift recurrence directly from `Complex.digamma_apply_add_one`:
`Complex.digamma (s + n) = Complex.digamma s + ∑ j ∈ Finset.range n, (s + j)⁻¹`. -/
theorem digamma_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    Complex.digamma (s + n) = Complex.digamma s + ∑ j ∈ Finset.range n, (s + (j : ℂ))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : ∀ m : ℕ, s + (n : ℂ) ≠ -(m : ℂ) := by
      intro m heq
      apply hs (m + n)
      push_cast
      linear_combination heq
    rw [Nat.cast_succ, ← add_assoc, Complex.digamma_apply_add_one _ hsn, ih,
      Finset.sum_range_succ, add_assoc]

/-- Norm bound on the digamma shift difference for `0 < s.re`. -/
theorem norm_digamma_add_nat_sub_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖Complex.digamma (s + n) - Complex.digamma s‖ ≤
      ∑ j ∈ Finset.range n, (s.re + (j : ℝ))⁻¹ := by
  have hne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [digamma_add_nat hne n, add_sub_cancel_left]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_inv]
  have hre_pos : 0 < s.re + (j : ℝ) := by positivity
  have hle : s.re + (j : ℝ) ≤ ‖s + (j : ℂ)‖ := by
    have : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
    rw [← this]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  exact inv_anti₀ hre_pos hle

/-! ## Section 3: Unconditional Entirety, Functional Equation, Zero Equivalence, & Order-1 Growth of `ξ(s)` -/

/-- The entire completed Riemann xi function:
`xi s = s * (s - 1) * completedRiemannZeta₀ s + 1`,
which agrees identically with `s * (s - 1) * completedRiemannZeta s` for all `s ≠ 0, 1`
and removes the simple poles at `s = 0` and `s = 1` cleanly (`xi 0 = xi 1 = 1`). -/
def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

@[simp]
theorem xi_zero : xi 0 = 1 := by simp [xi]

@[simp]
theorem xi_one : xi 1 = 1 := by simp [xi]

/-- Exact agreement with Mathlib's `completedRiemannZeta` away from `{0, 1}`:
`xi s = s * (s - 1) * completedRiemannZeta s`. -/
theorem xi_eq_mul_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp [h0, h1s]
  ring

/-- Exact factorization `xi s = s * (s - 1) * s.Gammaℝ * riemannZeta s` away from `{0, 1}`. -/
theorem xi_eq_mul_Gammaℝ_mul_riemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : s.Gammaℝ ≠ 0) :
    xi s = s * (s - 1) * s.Gammaℝ * riemannZeta s := by
  rw [xi_eq_mul_completedRiemannZeta h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp [hG]

/-- **Unconditional Entirety of `xi`**: `Differentiable ℂ xi`. -/
theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).mul
    differentiable_completedZeta₀).add (differentiable_const 1)

theorem continuous_xi : Continuous xi := differentiable_xi.continuous

/-- **Exact Functional Equation**: `xi (1 - s) = xi s` for all `s : ℂ`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub s]
  ring

/-- **Exact Critical-Strip Zero Equivalence**:
for `0 < Re(s) < 1`, `xi s = 0 ↔ riemannZeta s = 0`. -/
theorem xi_eq_zero_iff_riemannZeta_eq_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    xi s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  have h1 : s ≠ 1 := by intro h; simp [h] at hs1
  have hG : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 h1 hG]
  have hpre : s * (s - 1) * s.Gammaℝ ≠ 0 :=
    mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hG
  simp [hpre]

/-- Non-vanishing of `xi` on `Re(s) ≥ 1`. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1; simp
  · have hs0 : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
    have h0 : s ≠ 0 := by intro h; simp [h] at hs0
    have hG : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
    rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 h1 hG]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hG)
      (riemannZeta_ne_zero_of_one_le_re hs)

/-- Non-vanishing of `xi` on `Re(s) ≤ 0`. -/
theorem xi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_one_sub]
  exact xi_ne_zero_of_one_le_re (by simp; linarith)

/-- Complete characterization of ALL zeros of `xi` in `ℂ`:
`xi s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0`. -/
theorem xi_eq_zero_iff_critical_strip_zeta_zero (s : ℂ) :
    xi s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  constructor
  · intro h
    have hs0 : 0 < s.re := by
      by_contra hle
      exact xi_ne_zero_of_re_le_zero (not_lt.mp hle) h
    have hs1 : s.re < 1 := by
      by_contra hge
      exact xi_ne_zero_of_one_le_re (not_lt.mp hge) h
    exact ⟨hs0, hs1, (xi_eq_zero_iff_riemannZeta_eq_zero hs0 hs1).mp h⟩
  · rintro ⟨hs0, hs1, hz⟩
    exact (xi_eq_zero_iff_riemannZeta_eq_zero hs0 hs1).mpr hz

/-- Exact equivalence with Mathlib's `RiemannHypothesis`:
`RiemannHypothesis ↔ ∀ s : ℂ, xi s = 0 → s.re = 1 / 2`. -/
theorem riemannHypothesis_iff_xi_zeros_on_half_line :
    RiemannHypothesis ↔ ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hRH s hs
    obtain ⟨hs0, hs1, hz⟩ := (xi_eq_zero_iff_critical_strip_zeta_zero s).mp hs
    have hnottriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      simp at hs0
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hne1 : s ≠ 1 := by intro h; simp [h] at hs1
    exact hRH s hz hnottriv hne1
  · intro hxi s hz hnottriv hne1
    have hlt1 : s.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
    have hgt0 : 0 < s.re := by
      by_contra hle
      have hre_le : s.re ≤ 0 := not_lt.mp hle
      by_cases h0 : s = 0
      · subst h0; rw [riemannZeta_zero] at hz; norm_num at hz
      · -- On `Re(s) ≤ 0`, `s ≠ 0`, `xi s ≠ 0`, and if `s` is not a negative even integer then
        -- `s.Gammaℝ ≠ 0`, contradiction!
        have hG : s.Gammaℝ ≠ 0 := by
          rw [ne_eq, Complex.Gammaℝ_eq_zero_iff]
          rintro ⟨n, rfl⟩
          cases n with
          | zero => exact h0 (by simp)
          | succ m =>
            apply hnottriv
            refine ⟨m, ?_⟩
            push_cast; ring
        have hxi0 : xi s = 0 := by
          rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 hne1 hG, hz, mul_zero]
        exact xi_ne_zero_of_re_le_zero hre_le hxi0
    exact hxi s ((xi_eq_zero_iff_riemannZeta_eq_zero hgt0 hlt1).mpr hz)

/-- Global Mellin convergence of the modified theta kernel defining `completedRiemannZeta₀`. -/
lemma mellinConvergent_hurwitzEvenFEPair_zero (s : ℂ) :
    MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s := by
  set P := HurwitzZeta.hurwitzEvenFEPair 0
  have htop : P.f_modif =O[atTop] fun x : ℝ => x ^ (-(s.re + 1)) := by
    simpa using P.hf_modif_top (-(s.re + 1))
  have hzero_eq : P.f_modif =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun x : ℝ => P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀ := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one (α := ℝ))] with x hx
    rw [WeakFEPair.f_modif.eq_1]
    simp [Set.indicator_of_mem hx, not_lt.mpr hx.2.le]
  have hzero : P.f_modif =O[nhdsWithin 0 (Set.Ioi 0)] fun x : ℝ => x ^ (-(s.re - 1)) :=
    (P.hf_zero (-(s.re - 1))).congr' hzero_eq.symm EventuallyEq.rfl
  exact mellinConvergent_of_isBigO_rpow P.hf_modif_int htop (by linarith) hzero (by linarith)

/-- **Uniform Vertical-Strip Boundedness of Mathlib's `completedRiemannZeta₀`**:
for EVERY vertical strip `a ≤ Re(s) ≤ b`, `‖completedRiemannZeta₀ s‖` is uniformly bounded
independently of `Im(s)` directly from its Mellin–theta integral representation. -/
theorem norm_completedRiemannZeta₀_bounded_on_strip (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedRiemannZeta₀ s‖ ≤ C := by
  set P := HurwitzZeta.hurwitzEvenFEPair 0
  have hA : IntegrableOn (fun x : ℝ => x ^ (a / 2 - 1) * ‖P.f_modif x‖) (Set.Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (((a / 2 : ℝ) : ℂ) - 1) • P.f_modif x‖)
        (Set.Ioi 0) := (mellinConvergent_hurwitzEvenFEPair_zero ((a / 2 : ℝ) : ℂ)).norm
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only
    have hx_pos : 0 < x := hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    simp
  have hB : IntegrableOn (fun x : ℝ => x ^ (b / 2 - 1) * ‖P.f_modif x‖) (Set.Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (((b / 2 : ℝ) : ℂ) - 1) • P.f_modif x‖)
        (Set.Ioi 0) := (mellinConvergent_hurwitzEvenFEPair_zero ((b / 2 : ℝ) : ℂ)).norm
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only
    have hx_pos : 0 < x := hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    simp
  set C : ℝ := (∫ x in Set.Ioi (0 : ℝ),
      (x ^ (a / 2 - 1) * ‖P.f_modif x‖ + x ^ (b / 2 - 1) * ‖P.f_modif x‖)) / 2
  have hC0 : 0 ≤ C := by
    refine div_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x hx => ?_) (by norm_num)
    have hx_pos : 0 < x := hx
    positivity
  refine ⟨C, hC0, fun s hs1 hs2 => ?_⟩
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := by
    rw [completedRiemannZeta₀.eq_1, HurwitzZeta.completedHurwitzZetaEven₀.eq_1, WeakFEPair.Λ₀.eq_1]
  rw [hdef, norm_div, Complex.norm_ofNat]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  have hint_s : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (s / 2 - 1) • P.f_modif x‖) (Set.Ioi 0) :=
    (mellinConvergent_hurwitzEvenFEPair_zero (s / 2)).norm
  calc ‖mellin P.f_modif (s / 2)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖(x : ℂ) ^ (s / 2 - 1) • P.f_modif x‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi (0 : ℝ),
          (x ^ (a / 2 - 1) * ‖P.f_modif x‖ + x ^ (b / 2 - 1) * ‖P.f_modif x‖) := by
        refine MeasureTheory.setIntegral_mono_on hint_s (hA.add hB) measurableSet_Ioi fun x hx => ?_
        have hx_pos : 0 < x := hx
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        have hre : (s / 2 - 1).re = s.re / 2 - 1 := by simp
        rw [hre]
        have hrpow_le : x ^ (s.re / 2 - 1) ≤ x ^ (a / 2 - 1) + x ^ (b / 2 - 1) := by
          rcases le_total x 1 with hx1 | hx1
          · have h1 : x ^ (s.re / 2 - 1) ≤ x ^ (a / 2 - 1) :=
              Real.rpow_le_rpow_of_exponent_ge hx_pos hx1 (by linarith)
            linarith [Real.rpow_nonneg hx_pos.le (b / 2 - 1)]
          · have h2 : x ^ (s.re / 2 - 1) ≤ x ^ (b / 2 - 1) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
            linarith [Real.rpow_nonneg hx_pos.le (a / 2 - 1)]
        have hmul := mul_le_mul_of_nonneg_right hrpow_le (norm_nonneg (P.f_modif x))
        simpa [add_mul] using hmul

/-- Polynomial `O((‖s‖ + 1)²)` upper bound for `xi` on every vertical strip `a ≤ Re(s) ≤ b`. -/
theorem norm_xi_bounded_on_strip (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖xi s‖ ≤ C * (‖s‖ + 1) ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := norm_completedRiemannZeta₀_bounded_on_strip a b
  refine ⟨C₀ + 1, by linarith, fun s hs1 hs2 => ?_⟩
  have h1 : ‖s * (s - 1)‖ ≤ (‖s‖ + 1) ^ 2 := by
    rw [norm_mul]
    have hs1_le : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
        _ = ‖s‖ + 1 := by simp
    nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
  calc ‖xi s‖ = ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ := rfl
    _ ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ + 1 := by rw [norm_mul, norm_one]
    _ ≤ (‖s‖ + 1) ^ 2 * C₀ + 1 := by
        have hmul := mul_le_mul h1 (hbound s hs1 hs2) (norm_nonneg _) (by positivity)
        linarith
    _ ≤ (C₀ + 1) * (‖s‖ + 1) ^ 2 := by
        have hsq : 1 ≤ (‖s‖ + 1) ^ 2 := by nlinarith [norm_nonneg s]
        nlinarith

/-- Elementary telescoping bound `∑' n : ℕ, 1 / (n : ℝ) ^ 2 ≤ 2`. -/
lemma tsum_inv_nat_sq_le_two : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 := by
  have hsumm : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simp [one_div, Real.summable_nat_pow_inv]
  refine hsumm.tsum_le_of_sum_le fun s => ?_
  set N : ℕ := s.sup id + 1
  have hsub : s ⊆ Finset.range (N + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hn
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) ?_
  have hbound : ∀ k : ℕ,
      ∑ n ∈ Finset.range (k + 2), (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 - 1 / ((k + 1 : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero =>
      simp [Finset.sum_range_succ]
      norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hterm : (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 ≤
          1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) := by
        push_cast
        have hstep : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
            1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
          field_simp; ring
        rw [hstep]
        refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
        nlinarith
      linarith
  have h1 := hbound N
  have hsub2 : Finset.range (N + 1) ⊆ Finset.range (N + 2) :=
    Finset.range_mono (Nat.le_succ _)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by positivity) ?_
  have : (0 : ℝ) ≤ 1 / ((N + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Unconditional Dirichlet-series bound `‖riemannZeta s‖ ≤ 2` on `Re(s) ≥ 2`. -/
theorem norm_riemannZeta_le_two_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 2 := by
  have hs1 : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hs1]
  have hsumm_real : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simp [one_div, Real.summable_nat_pow_inv]
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    cases n with
    | zero =>
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs1; linarith
      simp [Complex.zero_cpow hs0]
    | succ k =>
      have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k)]
      refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
      simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hk1 hs
  have hsumm_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖) :=
    hsumm_real.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := hsumm_norm.tsum_le_tsum hterm hsumm_real
    _ ≤ 2 := tsum_inv_nat_sq_le_two

/-- Explicit growth bound for `xi` on the right half-plane `Re(s) ≥ 2`:
`‖xi s‖ ≤ Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2) + 2)`. -/
theorem norm_xi_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖xi s‖ ≤ Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2) + 2) := by
  have hs1 : 1 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [xi_eq_mul_completedRiemannZeta h0 h1, completedZeta_eq_tsum_of_one_lt_re hs1,
    ← zeta_eq_tsum_one_div_nat_cpow hs1]
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-s / 2).re = -s.re / 2 := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
  have hG : ‖Complex.Gamma (s / 2)‖ ≤ (‖s‖ + 2) ^ (s.re / 2) := by
    have hre2 : 1 ≤ (s / 2).re := by simp; linarith
    have hG1 := norm_Gamma_le_norm_add_one_rpow hre2
    have hre_eq : (s / 2).re = s.re / 2 := by simp
    rw [hre_eq] at hG1
    refine le_trans hG1 (Real.rpow_le_rpow (by linarith [norm_nonneg (s / 2)]) ?_ (by linarith))
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_nonneg s]
  have hZ : ‖riemannZeta s‖ ≤ 2 := norm_riemannZeta_le_two_of_two_le_re hs
  have hpoly : ‖s * (s - 1)‖ ≤ (‖s‖ + 2) ^ 2 := by
    rw [norm_mul]
    have : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
        _ = ‖s‖ + 1 := by simp
    nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
  have hbase_ge : 2 ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
  have hbase_pos : 0 < ‖s‖ + 2 := by linarith
  have hlog_pos : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
  have hre_le : s.re / 2 ≤ ‖s‖ + 2 := by
    have : s.re ≤ ‖s‖ := le_trans (le_abs_self s.re) (Complex.abs_re_le_norm s)
    linarith
  have hcomb : ‖s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s)‖ ≤
      2 * (‖s‖ + 2) ^ (2 + s.re / 2) := by
    rw [norm_mul (s * (s - 1)), norm_mul ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)),
      norm_mul ((Real.pi : ℂ) ^ (-s / 2))]
    have hstep1 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ ≤ (‖s‖ + 2) ^ (s.re / 2) := by
      calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
          ≤ 1 * (‖s‖ + 2) ^ (s.re / 2) :=
            mul_le_mul hpi hG (norm_nonneg _) zero_le_one
        _ = (‖s‖ + 2) ^ (s.re / 2) := one_mul _
    have hstep2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ ≤
        2 * (‖s‖ + 2) ^ (s.re / 2) := by
      calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖
          ≤ (‖s‖ + 2) ^ (s.re / 2) * 2 :=
            mul_le_mul hstep1 hZ (norm_nonneg _) (Real.rpow_nonneg hbase_pos.le _)
        _ = 2 * (‖s‖ + 2) ^ (s.re / 2) := mul_comm _ _
    calc ‖s * (s - 1)‖ * (‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖)
        ≤ (‖s‖ + 2) ^ 2 * (2 * (‖s‖ + 2) ^ (s.re / 2)) :=
          mul_le_mul hpoly hstep2 (by positivity) (by positivity)
      _ = 2 * ((‖s‖ + 2) ^ (2 : ℝ) * (‖s‖ + 2) ^ (s.re / 2)) := by
          rw [Real.rpow_two]; ring
      _ = 2 * (‖s‖ + 2) ^ (2 + s.re / 2) := by rw [← Real.rpow_add hbase_pos]
  refine le_trans hcomb ?_
  rw [Real.rpow_def_of_pos hbase_pos]
  have h2_le_exp : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  calc 2 * Real.exp (Real.log (‖s‖ + 2) * (2 + s.re / 2))
      ≤ Real.exp 2 * Real.exp (Real.log (‖s‖ + 2) * (2 + s.re / 2)) :=
        mul_le_mul_of_nonneg_right h2_le_exp (Real.exp_pos _).le
    _ = Real.exp (Real.log (‖s‖ + 2) * (2 + s.re / 2) + 2) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2) + 2) := by
        refine Real.exp_le_exp.mpr ?_
        have hcoef : 2 + s.re / 2 ≤ 2 * (‖s‖ + 2) := by linarith
        nlinarith

/-- **Unconditional Order-1 Exponential Growth Bound for Mathlib's ACTUAL Completed Zeta `ξ(s)`**:
`∃ A > 0, ∃ B > 0, ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B)`. -/
theorem norm_xi_order_one_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
      ‖xi s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B) := by
  obtain ⟨Cs, hCs_pos, hstrip⟩ := norm_xi_bounded_on_strip (1 / 2) 2
  set B₁ : ℝ := max 2 (Real.log Cs + 1)
  have hB₁_pos : 0 < B₁ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  -- Step 1: Bound on the entire right half-plane `1 / 2 ≤ Re(s)`.
  have hright : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖xi s‖ ≤ Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B₁) := by
    intro s hs
    rcases le_or_gt 2 s.re with hs2 | hs2
    · refine le_trans (norm_xi_le_of_two_le_re hs2) (Real.exp_le_exp.mpr ?_)
      linarith [le_max_left (2 : ℝ) (Real.log Cs + 1)]
    · have hst := hstrip s hs hs2.le
      have hbase_ge : 2 ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
      have hbase_pos : 0 < ‖s‖ + 2 := by linarith
      have hlog_nonneg : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
      have hsq_le : (‖s‖ + 1) ^ 2 ≤ Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2)) := by
        calc (‖s‖ + 1) ^ 2
            ≤ (‖s‖ + 2) ^ 2 := pow_le_pow_left₀ (by linarith [norm_nonneg s]) (by linarith) 2
          _ = Real.exp (2 * Real.log (‖s‖ + 2)) := by
              rw [← Real.rpow_two, Real.rpow_def_of_pos hbase_pos, mul_comm]
          _ ≤ Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2)) := by
              refine Real.exp_le_exp.mpr ?_
              nlinarith
      have hCs_le : Cs ≤ Real.exp B₁ := by
        calc Cs = Real.exp (Real.log Cs) := (Real.exp_log hCs_pos).symm
          _ ≤ Real.exp B₁ := Real.exp_le_exp.mpr (le_trans (by linarith) (le_max_right _ _))
      calc ‖xi s‖
          ≤ Cs * (‖s‖ + 1) ^ 2 := hst
        _ ≤ Real.exp B₁ * Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2)) :=
            mul_le_mul hCs_le hsq_le (by positivity) (Real.exp_pos _).le
        _ = Real.exp (2 * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B₁) := by
            rw [← Real.exp_add]; congr 1; ring
  -- Step 2: Reflect across `Re(s) = 1 / 2` using `xi (1 - s) = xi s`.
  refine ⟨8, by norm_num, B₁, hB₁_pos, fun s => ?_⟩
  have hbase_ge : 2 ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
  have hbase_pos : 0 < ‖s‖ + 2 := by linarith
  have hlog_nonneg : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
  rcases le_or_gt (1 / 2 : ℝ) s.re with hs | hs
  · refine le_trans (hright s hs) (Real.exp_le_exp.mpr ?_)
    nlinarith
  · rw [← xi_one_sub s]
    have hre' : 1 / 2 ≤ (1 - s).re := by simp; linarith
    refine le_trans (hright (1 - s) hre') (Real.exp_le_exp.mpr ?_)
    have hnorm' : ‖1 - s‖ + 2 ≤ 2 * (‖s‖ + 2) := by
      have htri : ‖1 - s‖ ≤ 1 + ‖s‖ := by
        calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le 1 s
          _ = 1 + ‖s‖ := by simp
      linarith [norm_nonneg s]
    have hlog' : Real.log (‖1 - s‖ + 2) ≤ 2 * Real.log (‖s‖ + 2) := by
      calc Real.log (‖1 - s‖ + 2)
          ≤ Real.log (2 * (‖s‖ + 2)) := Real.log_le_log (by linarith [norm_nonneg (1 - s)]) hnorm'
        _ = Real.log 2 + Real.log (‖s‖ + 2) := Real.log_mul (by norm_num) hbase_pos.ne'
        _ ≤ Real.log (‖s‖ + 2) + Real.log (‖s‖ + 2) :=
            add_le_add (Real.log_le_log (by norm_num) hbase_ge) le_rfl
        _ = 2 * Real.log (‖s‖ + 2) := by ring
    have hmul : (‖1 - s‖ + 2) * Real.log (‖1 - s‖ + 2) ≤
        (2 * (‖s‖ + 2)) * (2 * Real.log (‖s‖ + 2)) :=
      mul_le_mul hnorm' hlog' (Real.log_nonneg (by linarith [norm_nonneg (1 - s)])) (by positivity)
    linarith

/-- Order-1 Hadamard corollary: for every `ε > 0`, `xi` satisfies the sub-order `1 + ε` bound
`∃ C > 0, ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (C * (‖s‖ + 2) ^ (1 + ε))`. -/
theorem norm_xi_order_one_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (C * (‖s‖ + 2) ^ (1 + ε)) := by
  obtain ⟨A, hA, B, hB, hxi⟩ := norm_xi_order_one_bound
  -- For all `x ≥ 2`, `log x ≤ x ^ ε / ε` (since `log (x^ε) = ε log x ≤ x^ε`).
  refine ⟨A / ε + B, by positivity, fun s => ?_⟩
  refine le_trans (hxi s) (Real.exp_le_exp.mpr ?_)
  set x : ℝ := ‖s‖ + 2
  have hx_ge : 2 ≤ x := by dsimp only [x]; linarith [norm_nonneg s]
  have hx_pos : 0 < x := by linarith
  have hlog_le : Real.log x ≤ x ^ ε / ε := by
    have h1 : ε * Real.log x = Real.log (x ^ ε) := (Real.log_rpow hx_pos ε).symm
    have h2 : Real.log (x ^ ε) ≤ x ^ ε :=
      le_trans (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos ε)) (by linarith)
    rw [le_div_iff₀ hε, mul_comm, h1]
    exact h2
  have hx_pow : x * x ^ ε = x ^ (1 + ε) := by
    conv_lhs => arg 1; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx_pos]
  have hx1_le : 1 ≤ x ^ (1 + ε) := Real.one_le_rpow (by linarith) (by linarith)
  calc A * x * Real.log x + B
      ≤ A * x * (x ^ ε / ε) + B * x ^ (1 + ε) := by
        have h1 : A * x * Real.log x ≤ A * x * (x ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog_le (by positivity)
        have h2 : B ≤ B * x ^ (1 + ε) := by nlinarith
        linarith
    _ = (A / ε + B) * x ^ (1 + ε) := by
        rw [← hx_pow]; field_simp [hε.ne']

end RHDirect.Stage5StirlingPhragmen
