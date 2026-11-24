import RHDirect.Stage5StirlingPhragmen
import RHDirect.Stage5JensenHadamard
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage6XiZeroDensity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Denumerable

/-!
# RHDirect.Stage7HadamardXiProduct

Completely **UNCONDITIONAL** (0 assumptions, 0 `sorry`, 0 custom `axiom`s) formalization of:

1. **Entire Holomorphic Logarithm & Borel–Carathéodory Polynomial-Growth Liouville Theorem**:
   - `exists_entire_log`: every nonvanishing entire function `g : ℂ → ℂ` admits an entire logarithm
     `h : ℂ → ℂ` with `∀ z, g z = Complex.exp (h z)` (via the radial primitive on `ℂ`).
   - `entire_eq_linear_of_re_circle_seq`: if `h` is entire and `(h z).re ≤ M k` on circles
     `‖z‖ = R k → ∞` with `M k / (R k)² → 0`, then `h'' ≡ 0`, so `∃ a b, ∀ z, h z = a + b * z`.
   - `entire_nonvanishing_order_lt_two_eq_exp_linear`: every nonvanishing entire function of
     order `< 2` (in particular `‖g z‖ ≤ exp(A (‖z‖ + 2) log(‖z‖ + 2) + B)`) equals
     `Complex.exp (a + b * z)`.

2. **Minimum-Modulus Lower Bound for Genus-1 Weierstrass Products & Full Hadamard Factorization**:
   - `order_one_multiplicity_zero_count_le`: multiplicity-counted Jensen bound `n_mult(r) ≤ C r log(r + 2)`.
   - `exists_avoiding_radius`: pigeonhole circle avoidance `|R - ‖ρ n‖| ≥ 1 / (2 (m + 1))`.
   - `weierstrassProduct_min_modulus_good_circles`: elementary lower bound
     `Real.exp (-C * R * (Real.log (R + 2)) ^ 2) ≤ ‖weierstrassProduct ρ z‖` on arbitrarily large
     good circles `‖z‖ = R ∈ [R₀, R₀ + 1]`.
   - `hadamard_factorization_order_one`: full Hadamard factorization theorem for ANY entire
     order-1 function `f` with `f 0 ≠ 0` and multiplicity-counted zero sequence `{ρ n}`.

3. **Unconditional Infinitude of Zeros & Concrete Hadamard Product of Mathlib's Actual `xi(s)`**:
   - `infinite_xi_zeros`: unconditional proof that Mathlib's `xi` (hence `riemannZeta` in the
     critical strip) has infinitely many zeros, deduced from Part 1 + factorial growth of `Γ(n) = (n - 1)!`.
   - `xiZeroSeq : ℕ → ℂ`: exact multiplicity-counted enumeration of ALL zeros of `xi`, with
     `xiZeroSeq_summable_inv_sq`, `xiZeroSeq_summable_rpow_neg`, and functional-equation
     involution symmetry `xiZeroSeq_symm_perm`.
   - `xi_hadamard_product`: `∃ b : ℂ, ∀ s : ℂ, xi s = Complex.exp (b * s) * weierstrassProduct xiZeroSeq s`
     (with canonical `b = xiHadamardB := deriv xi 0`).
   - `xi_logDeriv_hadamard`: `∀ s : ℂ, xi s ≠ 0 → deriv xi s / xi s = xiHadamardB + ∑' n, (1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n)`.
   - `xi_hadamard_davenport_B`: `xiHadamardB.re = -∑' n, (xiZeroSeq n)⁻¹.re` and
     `(deriv xi s / xi s).re = ∑' n, (1 / (s - xiZeroSeq n)).re` for `1 < s.re`.
-/

noncomputable section

open Complex Finset Filter Topology Metric MeasureTheory
open scoped BigOperators Real

namespace RHDirect.Stage7HadamardXiProduct

open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage6XiZeroDensity

/-! ## Section 1: Entire Holomorphic Logarithm & Borel–Carathéodory Order-<2 Liouville Theorem -/

/-- **Entire Holomorphic Logarithm via Radial Primitive on `ℂ`**:
if `g : ℂ → ℂ` is entire and never vanishes, then there exists an entire function `h : ℂ → ℂ`
such that `∀ z : ℂ, g z = Complex.exp (h z)`. -/
theorem exists_entire_log {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hnz : ∀ z : ℂ, g z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z : ℂ, g z = Complex.exp (h z) := by
  let H : ℂ → ℂ := fun z => deriv g z / g z
  have hH_diff : Differentiable ℂ H := by
    have hg'_diff : Differentiable ℂ (deriv g) :=
      (differentiableOn_univ.mp (hg.differentiableOn.deriv isOpen_univ))
    exact hg'_diff.div hg hnz
  let L : ℂ → ℂ := fun w => ∫ u in (0 : ℝ)..1, w * H ((u : ℂ) * w)
  have hL_deriv : ∀ z : ℂ, HasDerivAt L (H z) z := by
    intro z
    set r : ℝ := ‖z‖ + 1
    have hz : z ∈ Metric.ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff]; linarith
    have hrad := Stage5ZetaZeroFree.hasDerivAt_radial_primitive_ball
      (s₀ := (0 : ℂ)) (r := r) hH_diff.differentiableOn hz
    have hfun : (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - 0) * H (0 + (u : ℂ) * (w - 0))) = L := by
      funext w; simp [L]
    rwa [hfun] at hrad
  have hL_diff : Differentiable ℂ L := fun z => (hL_deriv z).differentiableAt
  have hL0 : L 0 = 0 := by simp [L]
  let q : ℂ → ℂ := fun w => g w * Complex.exp (-L w)
  have hq_deriv : ∀ w : ℂ, HasDerivAt q 0 w := by
    intro w
    have hg_at : HasDerivAt g (deriv g w) w := (hg w).hasDerivAt
    have hL_at : HasDerivAt L (deriv g w / g w) w := hL_deriv w
    have hexp : HasDerivAt (fun x => Complex.exp (-L x))
        (Complex.exp (-L w) * -(deriv g w / g w)) w := hL_at.neg.cexp
    refine (hg_at.mul hexp).congr_deriv ?_
    have hne := hnz w
    field_simp [hne]
    ring
  have hq_diff : Differentiable ℂ q := fun w => (hq_deriv w).differentiableAt
  have hq_const : ∀ z : ℂ, q z = q 0 := fun z =>
    is_const_of_deriv_eq_zero hq_diff (fun w => (hq_deriv w).deriv) z 0
  have hq0 : q 0 = g 0 := by simp [q, hL0]
  refine ⟨fun z => Complex.log (g 0) + L z, (differentiable_const _).add hL_diff, fun z => ?_⟩
  rw [Complex.exp_add, Complex.exp_log (hnz 0)]
  have hqz := hq_const z
  rw [hq0] at hqz
  dsimp only [q] at hqz
  calc g z = (g z * Complex.exp (-L z)) * Complex.exp (L z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = g 0 * Complex.exp (L z) := by rw [hqz]

/-- Elementary limit: `(A * (R + 2) * (Real.log (R + 2)) ^ 2 + B) / R ^ 2 → 0` as `R → ∞`. -/
lemma tendsto_mul_log_sq_div_sq_atTop (A B : ℝ) :
    Tendsto (fun R : ℝ => (A * (R + 2) * (Real.log (R + 2)) ^ 2 + B) / R ^ 2) atTop (nhds 0) := by
  have hlog_sq : ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    have hs1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hs2 : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hs1
    have hlog_eq : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
      have h1 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx_pos.le
      have h2 : Real.log (Real.sqrt (Real.sqrt x)) = Real.log (Real.sqrt x) / 2 :=
        Real.log_sqrt hs1.le
      linarith
    have hle1 : Real.log (Real.sqrt (Real.sqrt x)) ≤ Real.sqrt (Real.sqrt x) :=
      le_trans (Real.log_le_sub_one_of_pos hs2) (by linarith)
    have hlog_le : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by linarith
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
    calc (Real.log x) ^ 2
        ≤ (4 * Real.sqrt (Real.sqrt x)) ^ 2 := pow_le_pow_left₀ hlog_nn hlog_le 2
      _ = 16 * (Real.sqrt (Real.sqrt x)) ^ 2 := by ring
      _ = 16 * Real.sqrt x := by rw [Real.sq_sqrt hs1.le]
  have hsqrt_top : Tendsto Real.sqrt atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨max b 0 ^ 2, fun x hx => by
      calc b ≤ max b 0 := le_max_left b 0
        _ = Real.sqrt (max b 0 ^ 2) := (Real.sqrt_sq (le_max_right b 0)).symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx⟩
  have hinv_sqrt : Tendsto (fun R : ℝ => (32 * Real.sqrt 2 * |A| + |B|) * (Real.sqrt R)⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hsqrt_top).const_mul (32 * Real.sqrt 2 * |A| + |B|)
  refine squeeze_zero_norm' ?_ hinv_sqrt
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
  have hR_pos : 0 < R := by linarith
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR_pos
  have h1 : (Real.log (R + 2)) ^ 2 ≤ 16 * Real.sqrt (R + 2) := hlog_sq (R + 2) (by linarith)
  have h2 : Real.sqrt (R + 2) ≤ Real.sqrt 2 * Real.sqrt R := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hR2 : R + 2 ≤ 2 * R := by linarith
  have hsqrt_le_R2 : Real.sqrt R ≤ R ^ 2 := by
    have hsr : Real.sqrt R ≤ R := by
      have : Real.sqrt R ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hR_pos.le] at this
    nlinarith
  have hterm1 : |A * (R + 2) * (Real.log (R + 2)) ^ 2| / R ^ 2 ≤
      32 * Real.sqrt 2 * |A| * (Real.sqrt R)⁻¹ := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < R + 2),
      abs_of_nonneg (sq_nonneg (Real.log (R + 2)))]
    have hnum : |A| * (R + 2) * (Real.log (R + 2)) ^ 2 ≤
        |A| * (2 * R) * (16 * (Real.sqrt 2 * Real.sqrt R)) := by
      have h12 : (Real.log (R + 2)) ^ 2 ≤ 16 * (Real.sqrt 2 * Real.sqrt R) := by linarith
      have ha : |A| * (R + 2) ≤ |A| * (2 * R) :=
        mul_le_mul_of_nonneg_left hR2 (abs_nonneg A)
      exact mul_le_mul ha h12 (sq_nonneg _) (by positivity)
    have hdiv : |A| * (2 * R) * (16 * (Real.sqrt 2 * Real.sqrt R)) / R ^ 2 =
        32 * Real.sqrt 2 * |A| * (Real.sqrt R)⁻¹ := by
      field_simp [hR_pos.ne', hsqrtR_pos.ne']
      rw [Real.sq_sqrt hR_pos.le]
      ring
    calc |A| * (R + 2) * (Real.log (R + 2)) ^ 2 / R ^ 2
        ≤ |A| * (2 * R) * (16 * (Real.sqrt 2 * Real.sqrt R)) / R ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg R)
      _ = 32 * Real.sqrt 2 * |A| * (Real.sqrt R)⁻¹ := hdiv
  have hterm2 : |B| / R ^ 2 ≤ |B| * (Real.sqrt R)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hsqrtR_pos hsqrt_le_R2) (abs_nonneg B)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hR_pos)]
  calc |A * (R + 2) * (Real.log (R + 2)) ^ 2 + B| / R ^ 2
      ≤ (|A * (R + 2) * (Real.log (R + 2)) ^ 2| + |B|) / R ^ 2 :=
        div_le_div_of_nonneg_right (abs_add_le _ _) (sq_nonneg R)
    _ = |A * (R + 2) * (Real.log (R + 2)) ^ 2| / R ^ 2 + |B| / R ^ 2 := add_div _ _ _
    _ ≤ 32 * Real.sqrt 2 * |A| * (Real.sqrt R)⁻¹ + |B| * (Real.sqrt R)⁻¹ :=
        add_le_add hterm1 hterm2
    _ = (32 * Real.sqrt 2 * |A| + |B|) * (Real.sqrt R)⁻¹ := by ring

/-- **Borel–Carathéodory Sub-Quadratic Liouville Theorem on Circle Sequences**:
if `h : ℂ → ℂ` is entire and `(h z).re ≤ M k` on spheres `‖z‖ = R k` with `R k → ∞` and
`M k / (R k)² → 0`, then `deriv (deriv h) ≡ 0`, hence `∃ a b : ℂ, ∀ z, h z = a + b * z`. -/
theorem entire_eq_linear_of_re_circle_seq {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R M : ℕ → ℝ} (hR_top : Tendsto R atTop atTop)
    (hM_bound : ∀ k : ℕ, ∀ z ∈ Metric.sphere (0 : ℂ) (R k), (h z).re ≤ M k)
    (hM_subquad : Tendsto (fun k => M k / (R k) ^ 2) atTop (nhds 0)) :
    ∃ a b : ℂ, ∀ z : ℂ, h z = a + b * z := by
  have hh'_diff : Differentiable ℂ (deriv h) :=
    differentiableOn_univ.mp (hh.differentiableOn.deriv isOpen_univ)
  -- Step 1: Maximum Modulus on `exp ∘ h` lifts `(h z).re ≤ M k` from `sphere 0 (R k)` to `closedBall 0 (R k)`.
  have hre_cb : ∀ k : ℕ, 0 < R k → ∀ w ∈ Metric.closedBall (0 : ℂ) (R k), (h w).re ≤ M k := by
    intro k hRk w hw
    have hexp_diff : DiffContOnCl ℂ (fun z => Complex.exp (h z)) (Metric.ball (0 : ℂ) (R k)) :=
      hh.cexp.diffContOnCl
    have hfront : ∀ z ∈ frontier (Metric.ball (0 : ℂ) (R k)),
        ‖Complex.exp (h z)‖ ≤ Real.exp (M k) := by
      intro z hz
      rw [frontier_ball (0 : ℂ) hRk.ne'] at hz
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (hM_bound k z hz)
    have hw_cl : w ∈ closure (Metric.ball (0 : ℂ) (R k)) := by
      rwa [closure_ball (0 : ℂ) hRk.ne']
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hexp_diff hfront hw_cl
    rw [Complex.norm_exp] at hle
    exact Real.exp_le_exp.mp hle
  -- Step 2: Double Borel–Carathéodory proves `deriv (deriv h) z = 0` for every `z : ℂ`.
  have hh''_zero : ∀ z : ℂ, deriv (deriv h) z = 0 := by
    intro z
    have hlim_rhs : Tendsto (fun k : ℕ => 128 * (M k / (R k) ^ 2 - (h 0).re / (R k) ^ 2))
        atTop (nhds 0) := by
      have hsq_top : Tendsto (fun k : ℕ => (R k) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hR_top
      have hconst_zero : Tendsto (fun k : ℕ => (h 0).re / (R k) ^ 2) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hsq_top).const_mul (h 0).re
      simpa using (hM_subquad.sub hconst_zero).const_mul (128 : ℝ)
    have hnorm_le_zero : ‖deriv (deriv h) z‖ ≤ 0 := by
      refine ge_of_tendsto hlim_rhs ?_
      filter_upwards [hR_top.eventually (eventually_gt_atTop (max (4 * ‖z‖) 4))] with k hk
      have hRk_gt4 : 4 < R k := lt_of_le_of_lt (le_max_right _ _) hk
      have hRk_pos : 0 < R k := by linarith
      have hz_lt : ‖z‖ < R k / 4 := by
        have := lt_of_le_of_lt (le_max_left _ _) hk; linarith
      have hre_k := hre_cb k hRk_pos
      have hbc1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (R k / 2),
          ‖deriv h w‖ ≤ (8 / R k) * (M k - (h 0).re) := by
        intro w hw
        have h1 := Stage5ZetaZeroFree.borelCaratheodory_deriv_le (z₀ := (0 : ℂ)) (z := w)
          (M := M k) (R := R k) (r := R k / 2) hRk_pos (by linarith)
          hh.differentiableOn hre_k (by simpa [mem_closedBall_zero_iff] using hw)
        have hcoeff : 2 * R k / (R k - R k / 2) ^ 2 = 8 / R k := by
          field_simp [hRk_pos.ne']; ring
        rwa [hcoeff] at h1
      set K : ℝ := (8 / R k) * (M k - (h 0).re)
      have hball_sub : Metric.ball z (R k / 4) ⊆ Metric.closedBall (0 : ℂ) (R k / 2) := by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        rw [mem_closedBall_zero_iff]
        have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa [sub_add_cancel] using norm_add_le (w - z) z
        linarith
      have hre_deriv : ∀ w ∈ Metric.ball z (R k / 4), (deriv h w).re ≤ K := fun w hw =>
        (le_trans (le_abs_self _) (Complex.abs_re_le_norm (deriv h w))).trans
          (hbc1 w (hball_sub hw))
      have hbc2 := Stage5ZetaZeroFree.borelCaratheodory_deriv_at_center (f := deriv h)
        (z₀ := z) (M := K) (R := R k / 4) (by linarith) hh'_diff.differentiableOn hre_deriv
      have hz_cb : z ∈ Metric.closedBall (0 : ℂ) (R k / 2) :=
        mem_closedBall_zero_iff.mpr (by linarith)
      have hneg_re : -(deriv h z).re ≤ K :=
        ((neg_le_abs _).trans (Complex.abs_re_le_norm (deriv h z))).trans (hbc1 z hz_cb)
      have hstep : (2 / (R k / 4)) * (K - (deriv h z).re) ≤ (2 / (R k / 4)) * (2 * K) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hsimp : (2 / (R k / 4)) * (2 * K) =
          128 * (M k / (R k) ^ 2 - (h 0).re / (R k) ^ 2) := by
        dsimp only [K]; field_simp [hRk_pos.ne']; ring
      linarith
    exact norm_le_zero_iff.mp hnorm_le_zero
  -- Step 3: Integrate `h'' ≡ 0` twice on `ℂ`.
  set b : ℂ := deriv h 0
  have hh'_const : ∀ z : ℂ, deriv h z = b := fun z =>
    is_const_of_deriv_eq_zero hh'_diff hh''_zero z 0
  let p : ℂ → ℂ := fun z => h z - b * z
  have hp_deriv : ∀ z : ℂ, HasDerivAt p 0 z := by
    intro z
    have h1 : HasDerivAt h b z := by
      rw [← hh'_const z]; exact (hh z).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => b * w) b z := by
      simpa using (hasDerivAt_id z).const_mul b
    simpa [p] using h1.fun_sub h2
  have hp_const : ∀ z : ℂ, p z = p 0 := fun z =>
    is_const_of_deriv_eq_zero (fun w => (hp_deriv w).differentiableAt)
      (fun w => (hp_deriv w).deriv) z 0
  refine ⟨h 0, b, fun z => ?_⟩
  have hz := hp_const z
  simp only [p, mul_zero, sub_zero] at hz
  linear_combination hz

/-- **Borel–Carathéodory Liouville Theorem for Entire Functions with Order-1 Real-Part Bound**:
if `h : ℂ → ℂ` is entire and `∀ z, (h z).re ≤ A * (‖z‖ + 2) * Real.log (‖z‖ + 2) + B`, then
`∃ a b : ℂ, ∀ z, h z = a + b * z`. -/
theorem entire_eq_linear_of_re_order_one_bound {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {A B : ℝ} (hre : ∀ z : ℂ, (h z).re ≤ A * (‖z‖ + 2) * Real.log (‖z‖ + 2) + B) :
    ∃ a b : ℂ, ∀ z : ℂ, h z = a + b * z := by
  let R : ℕ → ℝ := fun k => (k : ℝ) + 2
  let M : ℕ → ℝ := fun k => max A 0 * (R k + 2) * (Real.log (R k + 2)) ^ 2 + B
  have hR_top : Tendsto R atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine entire_eq_linear_of_re_circle_seq hh hR_top ?_
    ((tendsto_mul_log_sq_div_sq_atTop (max A 0) B).comp hR_top)
  intro k z hz
  have hzn : ‖z‖ = R k := mem_sphere_zero_iff_norm.mp hz
  have h1 := hre z
  rw [hzn] at h1
  have hlog_ge1 : 1 ≤ Real.log (R k + 2) := by
    have he : Real.exp 1 ≤ R k + 2 := by
      have := Real.exp_one_lt_d9
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      dsimp only [R]; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (R k + 2) := Real.log_le_log (Real.exp_pos 1) he
  have hlog_le_sq : Real.log (R k + 2) ≤ (Real.log (R k + 2)) ^ 2 := by nlinarith
  have hR2_pos : 0 ≤ R k + 2 := by dsimp only [R]; positivity
  have hA_le : A * (R k + 2) * Real.log (R k + 2) ≤
      max A 0 * (R k + 2) * (Real.log (R k + 2)) ^ 2 := by
    calc A * (R k + 2) * Real.log (R k + 2)
        ≤ max A 0 * (R k + 2) * Real.log (R k + 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left A 0) hR2_pos) (by linarith)
      _ ≤ max A 0 * (R k + 2) * (Real.log (R k + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog_le_sq (mul_nonneg (le_max_right A 0) hR2_pos)
  linarith

/-- **Nonvanishing Entire Order-<2 Characterization**:
every entire function `g : ℂ → ℂ` with `∀ z, g z ≠ 0` and
`∀ z, ‖g z‖ ≤ Real.exp (A * (‖z‖ + 2) * Real.log (‖z‖ + 2) + B)` is of the form
`g z = Complex.exp (a + b * z)`. -/
theorem entire_nonvanishing_order_lt_two_eq_exp_linear {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hnz : ∀ z : ℂ, g z ≠ 0)
    {A B : ℝ} (hbound : ∀ z : ℂ, ‖g z‖ ≤ Real.exp (A * (‖z‖ + 2) * Real.log (‖z‖ + 2) + B)) :
    ∃ a b : ℂ, ∀ z : ℂ, g z = Complex.exp (a + b * z) := by
  obtain ⟨h, hh, hge⟩ := exists_entire_log hg hnz
  have hre : ∀ z : ℂ, (h z).re ≤ A * (‖z‖ + 2) * Real.log (‖z‖ + 2) + B := by
    intro z
    have h1 := hbound z
    rw [hge z, Complex.norm_exp] at h1
    exact Real.exp_le_exp.mp h1
  obtain ⟨a, b, hab⟩ := entire_eq_linear_of_re_order_one_bound hh hre
  exact ⟨a, b, fun z => by rw [hge z, hab z]⟩

/-! ## Section 2: Minimum-Modulus Lower Bound for Genus-1 Weierstrass Products & Hadamard Factorization -/

/-- Exact multiplicity-counted zero-sequence specification for an entire function `f`:
`ρ : ℕ → ℂ` never hits `0`, and each `w : ℂ` occurs in `ρ` exactly `analyticOrderNatAt f w` times. -/
def IsMultiplicityZeroSeq (f : ℂ → ℂ) (ρ : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, ρ n ≠ 0) ∧
  (∀ w : ℂ, {n : ℕ | ρ n = w}.Finite ∧
    ∀ F : Finset ℕ, (∀ n, n ∈ F ↔ ρ n = w) → F.card = analyticOrderNatAt f w)

lemma IsMultiplicityZeroSeq.apply_eq_zero {f : ℂ → ℂ} {ρ : ℕ → ℂ}
    (h : IsMultiplicityZeroSeq f ρ) (n : ℕ) : f (ρ n) = 0 := by
  classical
  have hfin := (h.2 (ρ n)).1
  have hcard := (h.2 (ρ n)).2 hfin.toFinset (fun m => hfin.mem_toFinset)
  have hmem : n ∈ hfin.toFinset := hfin.mem_toFinset.mpr rfl
  have hpos : 0 < hfin.toFinset.card := Finset.card_pos.mpr ⟨n, hmem⟩
  rw [hcard] at hpos
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne'

/-- An entire function not vanishing at `0` has finite analytic order everywhere. -/
private lemma analyticOrderAt_ne_top_of_entire_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ w in 𝓝 z, f w = 0 := analyticOrderAt_eq_top.mp htop
  have hfreq : ∃ᶠ w in 𝓝[≠] z, f w = 0 := (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have heq : Set.EqOn f (fun _ => (0 : ℂ)) Set.univ :=
    hf_an.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const isPreconnected_univ
      (Set.mem_univ z) hfreq
  exact hf0 (heq (Set.mem_univ 0))

/-- Finite product of entire functions is entire. -/
private lemma differentiable_finset_prod {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, Differentiable ℂ (F i)) :
    Differentiable ℂ (fun z => ∏ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [differentiable_const]
  | @insert a t hat ih =>
    have hfun : (fun z => ∏ i ∈ insert a t, F i z) = fun z => F a z * ∏ i ∈ t, F i z := by
      funext z; exact Finset.prod_insert hat
    rw [hfun]
    exact (hF a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

lemma IsMultiplicityZeroSeq.exists_of_eq_zero {f : ℂ → ℂ} {ρ : ℕ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (h : IsMultiplicityZeroSeq f ρ)
    {w : ℂ} (hw : f w = 0) : ∃ n : ℕ, ρ n = w := by
  classical
  have hf_an : ∀ z : ℂ, AnalyticAt ℂ f z := fun z =>
    (hf.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hne_top : analyticOrderAt f w ≠ ⊤ := analyticOrderAt_ne_top_of_entire_ne_zero hf hf0 w
  have hne_zero : analyticOrderAt f w ≠ 0 := (hf_an w).analyticOrderAt_ne_zero.mpr hw
  have hnat_ne : analyticOrderNatAt f w ≠ 0 := by
    intro h0
    have hcoe : (analyticOrderNatAt f w : ℕ∞) = analyticOrderAt f w :=
      ENat.natCast_toNat hne_top
    rw [h0, Nat.cast_zero] at hcoe
    exact hne_zero hcoe.symm
  have hfin := (h.2 w).1
  have hcard := (h.2 w).2 hfin.toFinset (fun m => hfin.mem_toFinset)
  have hpos : 0 < hfin.toFinset.card := Nat.pos_of_ne_zero (hcard.symm ▸ hnat_ne)
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  exact ⟨n, hfin.mem_toFinset.mp hn⟩

/-- **Multiplicity-Counted Order-1 Zero-Counting Bound**:
for any entire function `f` with `HasOrderOneGrowth f A B` (`A ≥ 0`), `f 0 ≠ 0`, and
multiplicity-counted zero sequence `ρ`, every finite index set `F` with `‖ρ n‖ ≤ r` (`r ≥ 1`)
satisfies `(F.card : ℝ) ≤ C * r * Real.log (r + 2)`. -/
theorem order_one_multiplicity_zero_count_le {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hf : HasOrderOneGrowth f A B) (hf0 : f 0 ≠ 0)
    {ρ : ℕ → ℂ} (hmult : IsMultiplicityZeroSeq f ρ) :
    ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ, (∀ n ∈ F, ‖ρ n‖ ≤ r) →
      (F.card : ℝ) ≤
        ((4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2) * r * Real.log (r + 2) := by
  classical
  have hf_an_univ : AnalyticOnNhd ℂ f Set.univ := hf.1.differentiableOn.analyticOnNhd isOpen_univ
  have hne_top : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := analyticOrderAt_ne_top_of_entire_ne_zero hf.1 hf0
  intro r hr F hF
  have hr_pos : 0 < r := by linarith
  have hR : r < 2 * r := by linarith
  let M : ℝ := Real.exp (A * (2 * r) * Real.log (2 * r + 2) + max B 0)
  have hM1 : 1 ≤ M := by
    dsimp only [M]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hlog_nn : 0 ≤ Real.log (2 * r + 2) := Real.log_nonneg (by linarith)
    have hA_nn : 0 ≤ A * (2 * r) * Real.log (2 * r + 2) := by positivity
    linarith [le_max_right B 0]
  have hM_bound : ∀ z ∈ sphere (0 : ℂ) (2 * r), ‖f z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ = 2 * r := mem_sphere_zero_iff_norm.mp hz
    refine (hf.2 z).trans (Real.exp_le_exp.mpr ?_)
    rw [hzn]
    linarith [le_max_left B 0]
  have hj := Stage5JensenHadamard.jensen_divisor_zero_count_le hr_pos hR hM1
    (hf_an_univ.mono (Set.subset_univ _)) hf0 hM_bound
  have hdiv : 2 * r / r = 2 := by field_simp [hr_pos.ne']
  rw [hdiv] at hj
  -- Relate `F.card` to `∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u`.
  let D : ℂ → ℤ := MeromorphicOn.divisor f (closedBall (0 : ℂ) r)
  have hD_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := hf_an_univ.mono (Set.subset_univ _)
  have hD_fin : D.support.Finite :=
    hD_an.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall 0 r) Set.Subset.rfl
  have hD_nn : ∀ u : ℂ, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hD_an u
  have hD_eval : ∀ u ∈ closedBall (0 : ℂ) r, D u = (analyticOrderNatAt f u : ℤ) := by
    intro u hu
    dsimp only [D]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hD_an hu]
    have hcoe : analyticOrderAt f u = (analyticOrderNatAt f u : ℕ∞) :=
      (ENat.natCast_toNat (hne_top u)).symm
    rw [hcoe]
    rfl
  have hF_le_sum : (F.card : ℤ) ≤ ∑ w ∈ F.image ρ, D w := by
    have hfib : F.card = ∑ w ∈ F.image ρ, (F.filter (fun n => ρ n = w)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := ρ) (t := F.image ρ)
        (fun n hn => Finset.mem_image_of_mem ρ hn)]
    rw [hfib, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hw
    have hw_cb : ρ n₀ ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.mpr (hF n₀ hn₀)
    rw [hD_eval (ρ n₀) hw_cb]
    have hfin_w := (hmult.2 (ρ n₀)).1
    have hcard_w := (hmult.2 (ρ n₀)).2 hfin_w.toFinset (fun m => hfin_w.mem_toFinset)
    have hsub : F.filter (fun n => ρ n = ρ n₀) ⊆ hfin_w.toFinset := by
      intro m hm
      exact hfin_w.mem_toFinset.mpr (Finset.mem_filter.mp hm).2
    exact_mod_cast (Finset.card_le_card hsub).trans_eq hcard_w
  have hsum_le_finsum : ∑ w ∈ F.image ρ, D w ≤ ∑ᶠ u : ℂ, D u := by
    have hfs : ∑ᶠ u : ℂ, D u = ∑ u ∈ hD_fin.toFinset, D u :=
      finsum_eq_sum_of_support_subset D (fun u hu => hD_fin.mem_toFinset.mpr hu)
    rw [hfs]
    have h1 : ∑ w ∈ F.image ρ, D w ≤ ∑ w ∈ F.image ρ ∪ hD_fin.toFinset, D w :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun u _ _ => hD_nn u)
    have h2 : ∑ w ∈ F.image ρ ∪ hD_fin.toFinset, D w = ∑ u ∈ hD_fin.toFinset, D u := by
      refine (Finset.sum_subset Finset.subset_union_right fun u _ hu => ?_).symm
      by_contra hne
      exact hu (hD_fin.mem_toFinset.mpr hne)
    linarith
  have hcard_le_hj : (F.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log 2 := by
    have h1 : (F.card : ℝ) ≤ ((∑ᶠ u : ℂ, D u : ℤ) : ℝ) := by
      exact_mod_cast hF_le_sum.trans hsum_le_finsum
    exact h1.trans hj
  -- Finish with the same elementary logarithm bound as `order_one_zero_count_le`.
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hlogM : Real.log (M / ‖f 0‖) =
      A * (2 * r) * Real.log (2 * r + 2) + max B 0 - Real.log ‖f 0‖ := by
    rw [Real.log_div (Real.exp_pos _).ne' hf0_pos.ne', Real.log_exp]
  rw [hlogM] at hcard_le_hj
  have hlog2r : Real.log (2 * r + 2) ≤ 2 * Real.log (r + 2) := by
    have hsq : 2 * r + 2 ≤ (r + 2) ^ 2 := by nlinarith
    calc Real.log (2 * r + 2)
        ≤ Real.log ((r + 2) ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log (r + 2) := by rw [Real.log_pow]; norm_num
  have h1le : 1 ≤ r * Real.log (r + 2) := by
    have he : Real.exp 1 ≤ r + 2 := by linarith [Real.exp_one_lt_d9]
    have hlog1 : 1 ≤ Real.log (r + 2) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (r + 2) := Real.log_le_log (Real.exp_pos 1) he
    nlinarith
  have hnum : A * (2 * r) * Real.log (2 * r + 2) + max B 0 - Real.log ‖f 0‖ ≤
      (4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) * (r * Real.log (r + 2)) := by
    have hA_term : A * (2 * r) * Real.log (2 * r + 2) ≤ 4 * A * (r * Real.log (r + 2)) := by
      have h1 := mul_le_mul_of_nonneg_left hlog2r (by positivity : 0 ≤ A * (2 * r))
      linarith
    have hB_term : max B 0 ≤ max B 0 * (r * Real.log (r + 2)) := by
      nlinarith [le_max_right B 0]
    have hf0_term : -Real.log ‖f 0‖ ≤ max (-Real.log ‖f 0‖) 0 * (r * Real.log (r + 2)) := by
      have h1 : -Real.log ‖f 0‖ ≤ max (-Real.log ‖f 0‖) 0 := le_max_left _ 0
      have h2 : 0 ≤ max (-Real.log ‖f 0‖) 0 := le_max_right _ 0
      nlinarith
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc (F.card : ℝ)
      ≤ (A * (2 * r) * Real.log (2 * r + 2) + max B 0 - Real.log ‖f 0‖) / Real.log 2 := hcard_le_hj
    _ ≤ ((4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) * (r * Real.log (r + 2))) / Real.log 2 :=
        div_le_div_of_nonneg_right hnum hlog2_pos.le
    _ = ((4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2) * r * Real.log (r + 2) := by
        ring

/-- **Pigeonhole Circle Avoidance Lemma**:
given `R₀ : ℝ` and a finite set `S : Finset ℕ` containing all indices with `R₀ ≤ ‖ρ n‖ < R₀ + 1`,
there exists `R ∈ [R₀, R₀ + 1]` avoiding every `‖ρ n‖` by at least `1 / (2 * (S.card + 1))`. -/
theorem exists_avoiding_radius (ρ : ℕ → ℂ) (R₀ : ℝ) (S : Finset ℕ)
    (hS : ∀ n : ℕ, R₀ ≤ ‖ρ n‖ → ‖ρ n‖ < R₀ + 1 → n ∈ S) :
    ∃ R ∈ Set.Icc R₀ (R₀ + 1), ∀ n : ℕ, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |R - ‖ρ n‖| := by
  classical
  set m : ℕ := S.card
  set M : ℝ := (m : ℝ) + 1
  have hM_pos : 0 < M := by dsimp only [M]; positivity
  let idx : ℕ → ℕ := fun n => Nat.floor ((‖ρ n‖ - R₀) * M)
  let bad : Finset ℕ := (S.image idx).filter (fun j => j < m + 1)
  have hbad_lt : bad.card < (Finset.range (m + 1)).card := by
    rw [Finset.card_range]
    calc bad.card ≤ (S.image idx).card := Finset.card_filter_le _ _
      _ ≤ S.card := Finset.card_image_le
      _ < m + 1 := Nat.lt_succ_self m
  have hnot_sub : ¬ Finset.range (m + 1) ⊆ bad := fun hsub =>
    not_lt_of_ge (Finset.card_le_card hsub) hbad_lt
  obtain ⟨j₀, hj₀_range, hj₀_not_bad⟩ := Finset.not_subset.mp hnot_sub
  have hj₀_lt : j₀ < m + 1 := Finset.mem_range.mp hj₀_range
  have hj₀_le : (j₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hj₀_lt
  set R : ℝ := R₀ + ((j₀ : ℝ) + 1 / 2) / M
  have hR_lo : R₀ ≤ R := by
    dsimp only [R]; have : 0 ≤ ((j₀ : ℝ) + 1 / 2) / M := by positivity
    linarith
  have hR_hi : R ≤ R₀ + 1 := by
    dsimp only [R]
    have hdiv : ((j₀ : ℝ) + 1 / 2) / M ≤ 1 := by
      rw [div_le_one hM_pos]; dsimp only [M]; linarith
    linarith
  refine ⟨R, ⟨hR_lo, hR_hi⟩, fun n => ?_⟩
  by_cases hlo : ‖ρ n‖ < R₀
  · have hpos : 1 / (2 * M) ≤ R - ‖ρ n‖ := by
      dsimp only [R]
      have h1 : 1 / (2 * M) ≤ ((j₀ : ℝ) + 1 / 2) / M := by
        rw [div_le_div_iff₀ (by positivity) hM_pos]
        have : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀
        nlinarith
      linarith
    exact hpos.trans (le_abs_self _)
  · push Not at hlo
    by_cases hhi : R₀ + 1 ≤ ‖ρ n‖
    · have hpos : 1 / (2 * M) ≤ ‖ρ n‖ - R := by
        dsimp only [R]
        have h1 : 1 / (2 * M) ≤ 1 - ((j₀ : ℝ) + 1 / 2) / M := by
          have heq : 1 - ((j₀ : ℝ) + 1 / 2) / M = ((m : ℝ) - (j₀ : ℝ) + 1 / 2) / M := by
            dsimp only [M]; field_simp [hM_pos.ne']; ring
          rw [heq, div_le_div_iff₀ (by positivity) hM_pos]
          nlinarith
        linarith
      rw [abs_sub_comm]
      exact hpos.trans (le_abs_self _)
    · push Not at hhi
      have hnS : n ∈ S := hS n hlo hhi
      have hscaled_nn : 0 ≤ (‖ρ n‖ - R₀) * M := mul_nonneg (sub_nonneg.mpr hlo) hM_pos.le
      have hscaled_lt : (‖ρ n‖ - R₀) * M < ((m + 1 : ℕ) : ℝ) := by
        have hcast : ((m + 1 : ℕ) : ℝ) = M := by dsimp only [M]; push_cast; ring
        rw [hcast]
        nlinarith
      have hidx_lt : idx n < m + 1 := (Nat.floor_lt hscaled_nn).mpr hscaled_lt
      have hidx_ne : idx n ≠ j₀ := by
        intro heq
        apply hj₀_not_bad
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨n, hnS, heq⟩, hj₀_lt⟩
      rcases lt_or_gt_of_ne hidx_ne with hlt | hgt
      · have hle_j0 : ((idx n + 1 : ℕ) : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hlt
        have hlt_floor : (‖ρ n‖ - R₀) * M < (idx n : ℝ) + 1 := Nat.lt_floor_add_one _
        have hlt_j0 : (‖ρ n‖ - R₀) * M < (j₀ : ℝ) := by push_cast at hle_j0; linarith
        have hdiff : 1 / (2 * M) ≤ R - ‖ρ n‖ := by
          dsimp only [R]
          have h1 : ‖ρ n‖ - R₀ < (j₀ : ℝ) / M := (lt_div_iff₀ hM_pos).mpr hlt_j0
          have h2 : ((j₀ : ℝ) + 1 / 2) / M - (j₀ : ℝ) / M = 1 / (2 * M) := by
            field_simp [hM_pos.ne']; ring
          linarith
        exact hdiff.trans (le_abs_self _)
      · have hge_j0 : ((j₀ + 1 : ℕ) : ℝ) ≤ (idx n : ℝ) := by exact_mod_cast hgt
        have hfloor_le : (idx n : ℝ) ≤ (‖ρ n‖ - R₀) * M := Nat.floor_le hscaled_nn
        have hge_scaled : (j₀ : ℝ) + 1 ≤ (‖ρ n‖ - R₀) * M := by push_cast at hge_j0; linarith
        have hdiff : 1 / (2 * M) ≤ ‖ρ n‖ - R := by
          dsimp only [R]
          have h1 : ((j₀ : ℝ) + 1) / M ≤ ‖ρ n‖ - R₀ := (div_le_iff₀ hM_pos).mpr hge_scaled
          have h2 : ((j₀ : ℝ) + 1) / M - ((j₀ : ℝ) + 1 / 2) / M = 1 / (2 * M) := by
            field_simp [hM_pos.ne']; ring
          linarith
        rw [abs_sub_comm]
        exact hdiff.trans (le_abs_self _)

/-- Near inverse-norm sum bound `∑_{‖ρ n‖ < 2 R} ‖ρ n‖⁻¹ ≤ C₁ (log (R + 2))²` from order-1
zero counting. -/
private lemma sum_inv_norm_lt_two_mul_le {ρ : ℕ → ℂ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (_hρ_ne : ∀ n, ρ n ≠ 0)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ ≤ r) → (F.card : ℝ) ≤ C₀ * r * Real.log (r + 2)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ < 2 * R) → ∑ n ∈ F, (‖ρ n‖)⁻¹ ≤ C₁ * (Real.log (R + 2)) ^ 2 := by
  classical
  -- Small zeros `{n | ‖ρ n‖ < 1}` form a fixed finite set independent of `R`.
  have hsmall_fin : {n : ℕ | ‖ρ n‖ < 1}.Finite := by
    by_contra hinf
    obtain ⟨F, hFsub, hFcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (Nat.floor (C₀ * Real.log 3) + 1)
    have hle := hcount 1 le_rfl F (fun n hn => (hFsub hn).le)
    simp only [mul_one, show (1 : ℝ) + 2 = 3 by norm_num] at hle
    have hgt : C₀ * Real.log 3 < (F.card : ℝ) := by
      rw [hFcard]; push_cast; exact Nat.lt_floor_add_one _
    linarith
  set F₀ : Finset ℕ := hsmall_fin.toFinset
  set S₀ : ℝ := ∑ n ∈ F₀, (‖ρ n‖)⁻¹
  have hS₀_nn : 0 ≤ S₀ := Finset.sum_nonneg fun n _ => by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₁ : ℝ := S₀ + 6 * C₀ * (2 / Real.log 2 + 1) + 1
  have hC₁_pos : 0 < C₁ := by positivity
  refine ⟨C₁, hC₁_pos, fun R hR F hF => ?_⟩
  let F_small := F.filter (fun n => ‖ρ n‖ < 1)
  let F_mid := F.filter (fun n => ¬ (‖ρ n‖ < 1))
  have hsplit : ∑ n ∈ F, (‖ρ n‖)⁻¹ = (∑ n ∈ F_small, (‖ρ n‖)⁻¹) + ∑ n ∈ F_mid, (‖ρ n‖)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not F (fun n => ‖ρ n‖ < 1) _).symm
  rw [hsplit]
  have hsmall_le : ∑ n ∈ F_small, (‖ρ n‖)⁻¹ ≤ S₀ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro n hn
    exact hsmall_fin.mem_toFinset.mpr (Finset.mem_filter.mp hn).2
  -- Cover `F_mid` by dyadic shells `k ∈ range (K + 1)` where `K = Nat.floor (log (2 R) / log 2)`.
  let shell (n : ℕ) : ℕ := Nat.floor (Real.log ‖ρ n‖ / Real.log 2)
  let K : ℕ := Nat.floor (Real.log (2 * R) / Real.log 2)
  have hcover : ∀ n ∈ F_mid, shell n ∈ Finset.range (K + 1) := by
    intro n hn
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hnl : 1 ≤ ‖ρ n‖ := not_lt.mp (Finset.mem_filter.mp hn).2
    have hnu : ‖ρ n‖ < 2 * R := hF n (Finset.mem_filter.mp hn).1
    refine Nat.floor_mono (div_le_div_of_nonneg_right ?_ hlog2_pos.le)
    exact Real.log_le_log (by linarith) hnu.le
  have hmid_eq : ∑ n ∈ F_mid, (‖ρ n‖)⁻¹ =
      ∑ k ∈ Finset.range (K + 1), ∑ n ∈ F_mid.filter (fun n => shell n = k), (‖ρ n‖)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hcover]
  have hlogR_ge1 : 1 ≤ Real.log (R + 2) := by
    have he : Real.exp 1 ≤ R + 2 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (R + 2) := Real.log_le_log (Real.exp_pos 1) he
  have hshell_le : ∀ k ∈ Finset.range (K + 1),
      ∑ n ∈ F_mid.filter (fun n => shell n = k), (‖ρ n‖)⁻¹ ≤ 6 * C₀ * Real.log (R + 2) := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    let Gk := F_mid.filter (fun n => shell n = k)
    have hbounds : ∀ n ∈ Gk, (2 : ℝ) ^ k ≤ ‖ρ n‖ ∧ ‖ρ n‖ ≤ (2 : ℝ) ^ (k + 1) := by
      intro n hn
      have hnl : 1 ≤ ‖ρ n‖ := not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      have hsh : Nat.floor (Real.log ‖ρ n‖ / Real.log 2) = k := (Finset.mem_filter.mp hn).2
      have hdiv_nn : 0 ≤ Real.log ‖ρ n‖ / Real.log 2 :=
        div_nonneg (Real.log_nonneg hnl) hlog2_pos.le
      have hk_le : (k : ℝ) ≤ Real.log ‖ρ n‖ / Real.log 2 := by rw [← hsh]; exact Nat.floor_le hdiv_nn
      have hlt_k1 : Real.log ‖ρ n‖ / Real.log 2 < (k : ℝ) + 1 := by rw [← hsh]; exact Nat.lt_floor_add_one _
      have h1 : (k : ℝ) * Real.log 2 ≤ Real.log ‖ρ n‖ := (le_div_iff₀ hlog2_pos).mp hk_le
      have h2 : Real.log ‖ρ n‖ ≤ ((k : ℝ) + 1) * Real.log 2 := ((div_lt_iff₀ hlog2_pos).mp hlt_k1).le
      have hρ_pos : 0 < ‖ρ n‖ := by linarith
      constructor
      · have hpow : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [← hpow, ← Real.exp_log hρ_pos]; exact Real.exp_le_exp.mpr h1
      · have hpow : Real.exp (((k : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (k + 1) := by
          have : (((k + 1 : ℕ) : ℝ)) * Real.log 2 = ((k : ℝ) + 1) * Real.log 2 := by push_cast; ring
          rw [← this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [← hpow, ← Real.exp_log hρ_pos]; exact Real.exp_le_exp.mpr h2
    have h2k_le : (2 : ℝ) ^ k ≤ 2 * R := by
      have hK_le : (K : ℝ) ≤ Real.log (2 * R) / Real.log 2 :=
        Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) hlog2_pos.le)
      have hk_real : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hkK
      have h1 : (k : ℝ) * Real.log 2 ≤ Real.log (2 * R) :=
        (le_div_iff₀ hlog2_pos).mp (hk_real.trans hK_le)
      have hpow : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [← hpow, ← Real.exp_log (by linarith : 0 < 2 * R)]
      exact Real.exp_le_exp.mpr h1
    have hlog_le : Real.log ((2 : ℝ) ^ (k + 1) + 2) ≤ 3 * Real.log (R + 2) := by
      have hle : (2 : ℝ) ^ (k + 1) + 2 ≤ (R + 2) ^ 3 := by
        have h2k1 : (2 : ℝ) ^ (k + 1) ≤ 4 * R := by rw [pow_succ]; linarith
        have hexp : (R + 2) ^ 3 = R ^ 3 + 6 * R ^ 2 + 12 * R + 8 := by ring
        nlinarith [sq_nonneg R]
      calc Real.log ((2 : ℝ) ^ (k + 1) + 2)
          ≤ Real.log ((R + 2) ^ 3) := Real.log_le_log (by positivity) hle
        _ = 3 * Real.log (R + 2) := by rw [Real.log_pow]; norm_num
    have hcard := hcount ((2 : ℝ) ^ (k + 1)) (one_le_pow₀ (by norm_num)) Gk
      (fun n hn => (hbounds n hn).2)
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    calc ∑ n ∈ Gk, (‖ρ n‖)⁻¹
        ≤ ∑ _n ∈ Gk, ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum fun n hn => inv_anti₀ h2k_pos (hbounds n hn).1
      _ = (Gk.card : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by simp
      _ ≤ (C₀ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1) + 2)) * ((2 : ℝ) ^ k)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * C₀ * Real.log ((2 : ℝ) ^ (k + 1) + 2) := by
          rw [pow_succ]; field_simp [h2k_pos.ne']
      _ ≤ 2 * C₀ * (3 * Real.log (R + 2)) :=
          mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = 6 * C₀ * Real.log (R + 2) := by ring
  have hK1_le : ((K + 1 : ℕ) : ℝ) ≤ (2 / Real.log 2 + 1) * Real.log (R + 2) := by
    have hK_le : (K : ℝ) ≤ Real.log (2 * R) / Real.log 2 :=
      Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) hlog2_pos.le)
    have hlog2R : Real.log (2 * R) ≤ 2 * Real.log (R + 2) := by
      have hsq : 2 * R ≤ (R + 2) ^ 2 := by nlinarith
      calc Real.log (2 * R) ≤ Real.log ((R + 2) ^ 2) := Real.log_le_log (by linarith) hsq
        _ = 2 * Real.log (R + 2) := by rw [Real.log_pow]; norm_num
    have hdiv : Real.log (2 * R) / Real.log 2 ≤ (2 / Real.log 2) * Real.log (R + 2) := by
      calc Real.log (2 * R) / Real.log 2
          ≤ (2 * Real.log (R + 2)) / Real.log 2 := div_le_div_of_nonneg_right hlog2R hlog2_pos.le
        _ = (2 / Real.log 2) * Real.log (R + 2) := by ring
    push_cast
    linarith
  have hmid_le : ∑ n ∈ F_mid, (‖ρ n‖)⁻¹ ≤ 6 * C₀ * (2 / Real.log 2 + 1) * (Real.log (R + 2)) ^ 2 := by
    rw [hmid_eq]
    calc ∑ k ∈ Finset.range (K + 1), ∑ n ∈ F_mid.filter (fun n => shell n = k), (‖ρ n‖)⁻¹
        ≤ ∑ _k ∈ Finset.range (K + 1), (6 * C₀ * Real.log (R + 2)) :=
          Finset.sum_le_sum hshell_le
      _ = ((K + 1 : ℕ) : ℝ) * (6 * C₀ * Real.log (R + 2)) := by simp
      _ ≤ ((2 / Real.log 2 + 1) * Real.log (R + 2)) * (6 * C₀ * Real.log (R + 2)) :=
          mul_le_mul_of_nonneg_right hK1_le (by positivity)
      _ = 6 * C₀ * (2 / Real.log 2 + 1) * (Real.log (R + 2)) ^ 2 := by ring
  have hlog_sq_ge1 : 1 ≤ (Real.log (R + 2)) ^ 2 := by nlinarith
  have hS₀_le : S₀ ≤ S₀ * (Real.log (R + 2)) ^ 2 := by nlinarith
  dsimp only [C₁]
  nlinarith

/-- Tail inverse-square sum bound `∑' n, (if 2 R ≤ ‖ρ n‖ then ‖ρ n‖⁻² else 0) ≤ C₂ log(R + 2) / R`. -/
private lemma tsum_tail_inv_sq_le {ρ : ℕ → ℂ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hρ_ne : ∀ n, ρ n ≠ 0)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ ≤ r) → (F.card : ℝ) ≤ C₀ * r * Real.log (r + 2)) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ R : ℝ, 2 ≤ R →
      ∑' n : ℕ, (if 2 * R ≤ ‖ρ n‖ then (‖ρ n‖ ^ 2)⁻¹ else 0) ≤ C₂ * Real.log (R + 2) / R := by
  classical
  have hsum_all : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) :=
    Stage5JensenHadamard.summable_inv_sq_of_zero_counting hC₀ hρ_ne hcount
  have hgeom : Summable (fun k : ℕ => ((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    have h2 : Summable (fun k : ℕ => (3 : ℝ) * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3
    exact (h1.add h2).congr fun k => by ring
  set K_sum : ℝ := ∑' k : ℕ, ((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k
  have hK_nn : 0 ≤ K_sum := tsum_nonneg fun k => by positivity
  set C₂ : ℝ := C₀ * K_sum + 1
  have hC₂_pos : 0 < C₂ := by positivity
  refine ⟨C₂, hC₂_pos, fun R hR => ?_⟩
  let g : ℕ → ℝ := fun n => if 2 * R ≤ ‖ρ n‖ then (‖ρ n‖ ^ 2)⁻¹ else 0
  have hg_nn : ∀ n, 0 ≤ g n := fun n => by dsimp only [g]; split_ifs <;> positivity
  have hg_summ : Summable g :=
    Summable.of_nonneg_of_le hg_nn (fun n => by dsimp only [g]; split_ifs <;> [exact le_rfl; positivity]) hsum_all
  refine hg_summ.tsum_le_of_sum_le fun F => ?_
  let F_far := F.filter (fun n => 2 * R ≤ ‖ρ n‖)
  have hF_eq : ∑ n ∈ F, g n = ∑ n ∈ F_far, (‖ρ n‖ ^ 2)⁻¹ := by
    rw [Finset.sum_filter]
  rw [hF_eq]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let shell (n : ℕ) : ℕ := Nat.floor (Real.log (‖ρ n‖ / (2 * R)) / Real.log 2)
  let K : ℕ := F_far.sup shell + 1
  have hcover : ∀ n ∈ F_far, shell n ∈ Finset.range K := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := shell) hn))
  rw [← Finset.sum_fiberwise_of_maps_to hcover]
  have hlogR_ge1 : 1 ≤ Real.log (R + 2) := by
    have he : Real.exp 1 ≤ R + 2 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (R + 2) := Real.log_le_log (Real.exp_pos 1) he
  have hshell_le : ∀ k ∈ Finset.range K,
      ∑ n ∈ F_far.filter (fun n => shell n = k), (‖ρ n‖ ^ 2)⁻¹ ≤
        C₀ * (Real.log (R + 2) / R) * (((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k) := by
    intro k _
    let Gk := F_far.filter (fun n => shell n = k)
    have hbounds : ∀ n ∈ Gk, (2 : ℝ) ^ k * (2 * R) ≤ ‖ρ n‖ ∧ ‖ρ n‖ ≤ (2 : ℝ) ^ (k + 1) * (2 * R) := by
      intro n hn
      have hge : 2 * R ≤ ‖ρ n‖ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      have hsh : Nat.floor (Real.log (‖ρ n‖ / (2 * R)) / Real.log 2) = k := (Finset.mem_filter.mp hn).2
      have hratio_ge1 : 1 ≤ ‖ρ n‖ / (2 * R) := (one_le_div (by linarith)).mpr hge
      have hratio_pos : 0 < ‖ρ n‖ / (2 * R) := by linarith
      have hdiv_nn : 0 ≤ Real.log (‖ρ n‖ / (2 * R)) / Real.log 2 :=
        div_nonneg (Real.log_nonneg hratio_ge1) hlog2_pos.le
      have hk_le : (k : ℝ) ≤ Real.log (‖ρ n‖ / (2 * R)) / Real.log 2 := by
        rw [← hsh]; exact Nat.floor_le hdiv_nn
      have hlt_k1 : Real.log (‖ρ n‖ / (2 * R)) / Real.log 2 < (k : ℝ) + 1 := by
        rw [← hsh]; exact Nat.lt_floor_add_one _
      have h1 : (k : ℝ) * Real.log 2 ≤ Real.log (‖ρ n‖ / (2 * R)) := (le_div_iff₀ hlog2_pos).mp hk_le
      have h2 : Real.log (‖ρ n‖ / (2 * R)) ≤ ((k : ℝ) + 1) * Real.log 2 :=
        ((div_lt_iff₀ hlog2_pos).mp hlt_k1).le
      constructor
      · have hpow : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        have hexp : (2 : ℝ) ^ k ≤ ‖ρ n‖ / (2 * R) := by
          rw [← hpow, ← Real.exp_log hratio_pos]; exact Real.exp_le_exp.mpr h1
        exact (le_div_iff₀ (by linarith)).mp hexp
      · have hpow : Real.exp (((k : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (k + 1) := by
          have : (((k + 1 : ℕ) : ℝ)) * Real.log 2 = ((k : ℝ) + 1) * Real.log 2 := by push_cast; ring
          rw [← this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
        have hexp : ‖ρ n‖ / (2 * R) ≤ (2 : ℝ) ^ (k + 1) := by
          rw [← hpow, ← Real.exp_log hratio_pos]; exact Real.exp_le_exp.mpr h2
        exact (div_le_iff₀ (by linarith)).mp hexp
    have hr_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) * (2 * R) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hcard := hcount ((2 : ℝ) ^ (k + 1) * (2 * R)) hr_ge1 Gk (fun n hn => (hbounds n hn).2)
    have hlog_le : Real.log ((2 : ℝ) ^ (k + 1) * (2 * R) + 2) ≤ ((k : ℝ) + 3) * Real.log (R + 2) := by
      have hle : (2 : ℝ) ^ (k + 1) * (2 * R) + 2 ≤ (2 : ℝ) ^ (k + 2) * (R + 2) := by
        have h2ge : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        have hpow : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := pow_succ (2 : ℝ) (k + 1)
        nlinarith
      calc Real.log ((2 : ℝ) ^ (k + 1) * (2 * R) + 2)
          ≤ Real.log ((2 : ℝ) ^ (k + 2) * (R + 2)) := Real.log_le_log (by positivity) hle
        _ = ((k + 2 : ℕ) : ℝ) * Real.log 2 + Real.log (R + 2) := by
            rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
        _ ≤ ((k : ℝ) + 2) * Real.log (R + 2) + Real.log (R + 2) := by
            push_cast
            have hlog2_le : Real.log 2 ≤ Real.log (R + 2) :=
              Real.log_le_log (by norm_num) (by linarith)
            nlinarith [Nat.cast_nonneg (α := ℝ) k]
        _ = ((k : ℝ) + 3) * Real.log (R + 2) := by ring
    have hlow_pos : (0 : ℝ) < (2 : ℝ) ^ k * (2 * R) := by positivity
    have hterm_le : ∀ n ∈ Gk, (‖ρ n‖ ^ 2)⁻¹ ≤ (((2 : ℝ) ^ k * (2 * R)) ^ 2)⁻¹ := fun n hn =>
      inv_anti₀ (sq_pos_of_pos hlow_pos) (pow_le_pow_left₀ hlow_pos.le (hbounds n hn).1 2)
    have h2k_ne : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have hR_ne : R ≠ 0 := by linarith
    have halg : (C₀ * ((2 : ℝ) ^ (k + 1) * (2 * R)) * (((k : ℝ) + 3) * Real.log (R + 2))) *
        (((2 : ℝ) ^ k * (2 * R)) ^ 2)⁻¹ =
        C₀ * (Real.log (R + 2) / R) * (((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k) := by
      rw [pow_succ, one_div_pow]
      field_simp [h2k_ne, hR_ne]
    calc ∑ n ∈ Gk, (‖ρ n‖ ^ 2)⁻¹
        ≤ ∑ _n ∈ Gk, (((2 : ℝ) ^ k * (2 * R)) ^ 2)⁻¹ := Finset.sum_le_sum hterm_le
      _ = (Gk.card : ℝ) * (((2 : ℝ) ^ k * (2 * R)) ^ 2)⁻¹ := by simp
      _ ≤ (C₀ * ((2 : ℝ) ^ (k + 1) * (2 * R)) * Real.log ((2 : ℝ) ^ (k + 1) * (2 * R) + 2)) *
            (((2 : ℝ) ^ k * (2 * R)) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C₀ * ((2 : ℝ) ^ (k + 1) * (2 * R)) * (((k : ℝ) + 3) * Real.log (R + 2))) *
            (((2 : ℝ) ^ k * (2 * R)) ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = C₀ * (Real.log (R + 2) / R) * (((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k) := halg
  calc ∑ k ∈ Finset.range K, ∑ n ∈ F_far.filter (fun n => shell n = k), (‖ρ n‖ ^ 2)⁻¹
      ≤ ∑ k ∈ Finset.range K, C₀ * (Real.log (R + 2) / R) * (((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k) :=
        Finset.sum_le_sum hshell_le
    _ = C₀ * (Real.log (R + 2) / R) * ∑ k ∈ Finset.range K, ((k : ℝ) + 3) * (1 / 2 : ℝ) ^ k := by
        rw [← Finset.mul_sum]
    _ ≤ C₀ * (Real.log (R + 2) / R) * K_sum :=
        mul_le_mul_of_nonneg_left (hgeom.sum_le_tsum (Finset.range K) (fun k _ => by positivity))
          (by positivity)
    _ = (C₀ * K_sum) * Real.log (R + 2) / R := by ring
    _ ≤ C₂ * Real.log (R + 2) / R := by
        dsimp only [C₂]
        have hpos : 0 ≤ Real.log (R + 2) / R := by positivity
        nlinarith [show (C₀ * K_sum) * Real.log (R + 2) / R = (C₀ * K_sum) * (Real.log (R + 2) / R) by ring,
          show (C₀ * K_sum + 1) * Real.log (R + 2) / R = (C₀ * K_sum + 1) * (Real.log (R + 2) / R) by ring]

/-- **Minimum-Modulus Lower Bound for Genus-1 Weierstrass Products on Good Circles**:
for any zero sequence `ρ : ℕ → ℂ` with `∀ n, ρ n ≠ 0` and order-1 zero counting
`#{n | ‖ρ n‖ ≤ r} ≤ C₀ * r * Real.log (r + 2)`, there exists `C > 0` such that for every
`R₀ ≥ 2` there is a good circle radius `R ∈ [R₀, R₀ + 1]` on which `weierstrassProduct ρ`
never vanishes and satisfies
`Real.exp (-C * R * (Real.log (R + 2)) ^ 2) ≤ ‖weierstrassProduct ρ z‖`. -/
theorem weierstrassProduct_min_modulus_good_circles {ρ : ℕ → ℂ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hρ_ne : ∀ n, ρ n ≠ 0)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ ≤ r) → (F.card : ℝ) ≤ C₀ * r * Real.log (r + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ R₀ : ℝ, 2 ≤ R₀ →
      ∃ R ∈ Set.Icc R₀ (R₀ + 1), ∀ z ∈ Metric.sphere (0 : ℂ) R,
        weierstrassProduct ρ z ≠ 0 ∧
        Real.exp (-C * R * (Real.log (R + 2)) ^ 2) ≤ ‖weierstrassProduct ρ z‖ := by
  classical
  have hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) :=
    Stage5JensenHadamard.summable_inv_sq_of_zero_counting hC₀ hρ_ne hcount
  obtain ⟨C₁, hC₁_pos, hnear_inv⟩ := sum_inv_norm_lt_two_mul_le hC₀ hρ_ne hcount
  obtain ⟨C₂, hC₂_pos, htail_sq⟩ := tsum_tail_inv_sq_le hC₀ hρ_ne hcount
  set C_near_log : ℝ := 6 * C₀ * (Real.log (24 * C₀ + 4) + 3)
  set C : ℝ := C_near_log + C₁ + C₂ + 1
  have hC_pos : 0 < C := by
    have hlog_pos : 0 ≤ Real.log (24 * C₀ + 4) := Real.log_nonneg (by linarith)
    have hcn : 0 ≤ C_near_log := by positivity
    linarith
  refine ⟨C, hC_pos, fun R₀ hR₀ => ?_⟩
  -- Pick `N₀` so that all zeros with `‖ρ n‖ ≤ 2 * (R₀ + 1)` lie inside `Finset.range N₀`.
  have htend := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq hρ_ne hsum
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (htend.eventually (Filter.eventually_gt_atTop (2 * (R₀ + 1))))
  let S : Finset ℕ := (Finset.range N₀).filter (fun n => ‖ρ n‖ ≤ 2 * (R₀ + 1))
  have hS_cover : ∀ n : ℕ, R₀ ≤ ‖ρ n‖ → ‖ρ n‖ < R₀ + 1 → n ∈ S := by
    intro n _ hlt
    have hn_lt : n < N₀ := by
      by_contra hge
      have := hN₀ n (not_lt.mp hge)
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn_lt, by linarith⟩
  obtain ⟨R, hR_mem, hR_avoid⟩ := exists_avoiding_radius ρ R₀ S hS_cover
  have hR_ge2 : 2 ≤ R := hR₀.trans hR_mem.1
  have hR_pos : 0 < R := by linarith
  have hlogR_ge1 : 1 ≤ Real.log (R + 2) := by
    have he : Real.exp 1 ≤ R + 2 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (R + 2) := Real.log_le_log (Real.exp_pos 1) he
  -- Pick `N` so that `∀ n ≥ N, 2 * R ≤ ‖ρ n‖`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (htend.eventually (Filter.eventually_ge_atTop (2 * R)))
  -- Bound `S.card ≤ 6 * C₀ * R * Real.log (R + 2)`.
  have h2R0 : 2 * (R₀ + 1) ≤ 3 * R := by linarith [hR_mem.1, hR₀]
  have hS_card_le : (S.card : ℝ) ≤ 6 * C₀ * R * Real.log (R + 2) := by
    have h1 := hcount (3 * R) (by linarith) S (fun n hn =>
      (Finset.mem_filter.mp hn).2.trans h2R0)
    have hlog3R : Real.log (3 * R + 2) ≤ 2 * Real.log (R + 2) := by
      have hsq : 3 * R + 2 ≤ (R + 2) ^ 2 := by nlinarith
      calc Real.log (3 * R + 2) ≤ Real.log ((R + 2) ^ 2) := Real.log_le_log (by linarith) hsq
        _ = 2 * Real.log (R + 2) := by rw [Real.log_pow]; norm_num
    have h2 : C₀ * (3 * R) * Real.log (3 * R + 2) ≤ C₀ * (3 * R) * (2 * Real.log (R + 2)) :=
      mul_le_mul_of_nonneg_left hlog3R (by positivity)
    linarith
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1))
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨R, hR_mem, fun z hz => ?_⟩
  have hzn : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  have hdist_ge : ∀ n : ℕ, δ ≤ ‖z - ρ n‖ := fun n => by
    have htri : |‖z‖ - ‖ρ n‖| ≤ ‖z - ρ n‖ := abs_norm_sub_norm_le z (ρ n)
    rw [hzn] at htri
    exact (hR_avoid n).trans htri
  have hz_ne : ∀ n : ℕ, z ≠ ρ n := fun n heq => by
    have h := hdist_ge n; rw [heq, sub_self, norm_zero] at h; linarith
  have hW_ne : weierstrassProduct ρ z ≠ 0 := by
    rw [ne_eq, Stage5JensenHadamard.weierstrassProduct_eq_zero_iff hρ_ne hsum]
    push Not; exact hz_ne
  refine ⟨hW_ne, ?_⟩
  -- Factor `weierstrassProduct ρ z` into `F_near`, `F_far`, and infinite tail `m + N`.
  have hfac := Stage5JensenHadamard.weierstrassProduct_eq_prefix_mul_exp_tail hρ_ne hsum hR_pos hN
    (mem_closedBall_zero_iff.mpr hzn.le)
  rw [hfac, norm_mul]
  let F_near := (Finset.range N).filter (fun i => ‖ρ i‖ < 2 * R)
  let F_far := (Finset.range N).filter (fun i => ¬ (‖ρ i‖ < 2 * R))
  have hprod_split : ∏ i ∈ Finset.range N, weierstrassE1 (z / ρ i) =
      (∏ i ∈ F_near, weierstrassE1 (z / ρ i)) * (∏ i ∈ F_far, weierstrassE1 (z / ρ i)) :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.range N) (fun i => ‖ρ i‖ < 2 * R) _).symm
  rw [hprod_split, norm_mul, norm_prod, norm_prod]
  -- (1) Near factors `i ∈ F_near`:
  have hF_near_sub : F_near ⊆ S := by
    intro i hi
    have hlt : ‖ρ i‖ < 2 * R := (Finset.mem_filter.mp hi).2
    have hle : ‖ρ i‖ ≤ 2 * (R₀ + 1) := by linarith [hR_mem.2]
    have hi_lt : i < N₀ := by
      by_contra hge
      have := hN₀ i (not_lt.mp hge)
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi_lt, hle⟩
  have hnear_prod_ge :
      Real.exp (-((F_near.card : ℝ) * Real.log (2 * R / δ) + R * ∑ i ∈ F_near, (‖ρ i‖)⁻¹)) ≤
        ∏ i ∈ F_near, ‖weierstrassE1 (z / ρ i)‖ := by
    have hfac_ge : ∀ i ∈ F_near,
        Real.exp (-(Real.log (2 * R / δ) + R * (‖ρ i‖)⁻¹)) ≤ ‖weierstrassE1 (z / ρ i)‖ := by
      intro i hi
      have hρ_lt : ‖ρ i‖ < 2 * R := (Finset.mem_filter.mp hi).2
      have hρ_pos : 0 < ‖ρ i‖ := norm_pos_iff.mpr (hρ_ne i)
      unfold weierstrassE1
      rw [norm_mul, Complex.norm_exp]
      have h1sub : ‖1 - z / ρ i‖ = ‖z - ρ i‖ / ‖ρ i‖ := by
        have heq : 1 - z / ρ i = -(z - ρ i) / ρ i := by field_simp [hρ_ne i]; ring
        rw [heq, norm_div, norm_neg]
      rw [h1sub]
      have hlin_ge : Real.exp (-Real.log (2 * R / δ)) ≤ ‖z - ρ i‖ / ‖ρ i‖ := by
        rw [Real.exp_neg, Real.exp_log (div_pos (by linarith) hδ_pos), inv_div]
        calc δ / (2 * R) ≤ ‖z - ρ i‖ / (2 * R) :=
              div_le_div_of_nonneg_right (hdist_ge i) (by linarith)
          _ ≤ ‖z - ρ i‖ / ‖ρ i‖ :=
              div_le_div_of_nonneg_left (norm_nonneg _) hρ_pos hρ_lt.le
      have hexp_ge : Real.exp (-(R * (‖ρ i‖)⁻¹)) ≤ Real.exp (z / ρ i).re := by
        apply Real.exp_le_exp.mpr
        have h1 : -(z / ρ i).re ≤ ‖z / ρ i‖ :=
          (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        have h2 : ‖z / ρ i‖ = R * (‖ρ i‖)⁻¹ := by rw [norm_div, hzn, div_eq_mul_inv]
        linarith
      calc Real.exp (-(Real.log (2 * R / δ) + R * (‖ρ i‖)⁻¹))
          = Real.exp (-Real.log (2 * R / δ)) * Real.exp (-(R * (‖ρ i‖)⁻¹)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ (‖z - ρ i‖ / ‖ρ i‖) * Real.exp (z / ρ i).re :=
            mul_le_mul hlin_ge hexp_ge (Real.exp_pos _).le (div_nonneg (norm_nonneg _) hρ_pos.le)
    calc Real.exp (-((F_near.card : ℝ) * Real.log (2 * R / δ) + R * ∑ i ∈ F_near, (‖ρ i‖)⁻¹))
        = Real.exp (∑ i ∈ F_near, -(Real.log (2 * R / δ) + R * (‖ρ i‖)⁻¹)) := by
          congr 1
          rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            ← Finset.mul_sum]
      _ = ∏ i ∈ F_near, Real.exp (-(Real.log (2 * R / δ) + R * (‖ρ i‖)⁻¹)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ F_near, ‖weierstrassE1 (z / ρ i)‖ :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) hfac_ge
  -- (2) Far factors in `F_far`:
  have hfar_prod_ge :
      Real.exp (-(R ^ 2 * ∑ i ∈ F_far, (‖ρ i‖ ^ 2)⁻¹)) ≤
        ∏ i ∈ F_far, ‖weierstrassE1 (z / ρ i)‖ := by
    have hfac_ge : ∀ i ∈ F_far,
        Real.exp (-(R ^ 2 * (‖ρ i‖ ^ 2)⁻¹)) ≤ ‖weierstrassE1 (z / ρ i)‖ := by
      intro i hi
      have hge : 2 * R ≤ ‖ρ i‖ := not_lt.mp (Finset.mem_filter.mp hi).2
      have hρ_pos : 0 < ‖ρ i‖ := by linarith
      have hsmall : ‖z / ρ i‖ ≤ 1 / 2 := by
        rw [norm_div, hzn, div_le_iff₀ hρ_pos]; linarith
      have hne_E : weierstrassE1 (z / ρ i) ≠ 0 :=
        Complex.slitPlane_ne_zero (Stage5JensenHadamard.weierstrassE1_mem_slitPlane hsmall)
      rw [← Complex.exp_log hne_E, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hlog_bd := Stage5JensenHadamard.norm_log_weierstrassE1_le_sq hsmall
      have hsq_eq : ‖z / ρ i‖ ^ 2 = R ^ 2 * (‖ρ i‖ ^ 2)⁻¹ := by
        rw [norm_div, hzn, div_pow, div_eq_mul_inv]
      have hneg := (neg_le_abs _).trans (Complex.abs_re_le_norm (Complex.log (weierstrassE1 (z / ρ i))))
      linarith
    calc Real.exp (-(R ^ 2 * ∑ i ∈ F_far, (‖ρ i‖ ^ 2)⁻¹))
        = Real.exp (∑ i ∈ F_far, -(R ^ 2 * (‖ρ i‖ ^ 2)⁻¹)) := by
          congr 1; rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      _ = ∏ i ∈ F_far, Real.exp (-(R ^ 2 * (‖ρ i‖ ^ 2)⁻¹)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ F_far, ‖weierstrassE1 (z / ρ i)‖ :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) hfac_ge
  -- (3) Infinite tail `m + N`:
  have htail_ge :
      Real.exp (-(R ^ 2 * ∑' m : ℕ, (‖ρ (m + N)‖ ^ 2)⁻¹)) ≤
        ‖Complex.exp (∑' m : ℕ, Complex.log (weierstrassE1 (z / ρ (m + N))))‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hsmall : ∀ m : ℕ, ‖z / ρ (m + N)‖ ≤ 1 / 2 := fun m => by
      have hge := hN (m + N) (Nat.le_add_left N m)
      have hρ_pos : 0 < ‖ρ (m + N)‖ := by linarith
      rw [norm_div, hzn, div_le_iff₀ hρ_pos]; linarith
    have hdom : Summable (fun m : ℕ => R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹) :=
      ((summable_nat_add_iff N).mpr hsum).mul_left (R ^ 2)
    have hlog_summ : Summable (fun m : ℕ => Complex.log (weierstrassE1 (z / ρ (m + N)))) := by
      refine Summable.of_norm_bounded hdom fun m => ?_
      have h1 := Stage5JensenHadamard.norm_log_weierstrassE1_le_sq (hsmall m)
      rwa [norm_div, hzn, div_pow, div_eq_mul_inv] at h1
    have hre_tsum : (∑' m : ℕ, Complex.log (weierstrassE1 (z / ρ (m + N)))).re =
        ∑' m : ℕ, (Complex.log (weierstrassE1 (z / ρ (m + N)))).re := by
      simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hlog_summ
    rw [hre_tsum, ← tsum_mul_left, ← tsum_neg]
    refine Summable.tsum_le_tsum (fun m => ?_) hdom.neg (Complex.reCLM.summable hlog_summ)
    have h1 := Stage5JensenHadamard.norm_log_weierstrassE1_le_sq (hsmall m)
    have hsq_eq : ‖z / ρ (m + N)‖ ^ 2 = R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ := by
      rw [norm_div, hzn, div_pow, div_eq_mul_inv]
    have hneg := (neg_le_abs _).trans (Complex.abs_re_le_norm (Complex.log (weierstrassE1 (z / ρ (m + N)))))
    linarith
  -- Combine all three exponents!
  have hfar_tail_eq :
      (∑ i ∈ F_far, (‖ρ i‖ ^ 2)⁻¹) + (∑' m : ℕ, (‖ρ (m + N)‖ ^ 2)⁻¹) =
        ∑' n : ℕ, (if 2 * R ≤ ‖ρ n‖ then (‖ρ n‖ ^ 2)⁻¹ else 0) := by
    let g : ℕ → ℝ := fun n => if 2 * R ≤ ‖ρ n‖ then (‖ρ n‖ ^ 2)⁻¹ else 0
    have hg_summ : Summable g :=
      Summable.of_nonneg_of_le (fun n => by dsimp only [g]; split_ifs <;> positivity)
        (fun n => by dsimp only [g]; split_ifs <;> [exact le_rfl; positivity]) hsum
    rw [← hg_summ.sum_add_tsum_nat_add N]
    congr 1
    · dsimp only [F_far, g]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : ‖ρ i‖ < 2 * R
      · rw [if_neg (not_not.mpr h), if_neg (not_le.mpr h)]
      · rw [if_pos h, if_pos (not_lt.mp h)]
    · refine tsum_congr fun m => ?_
      dsimp only [g]
      rw [if_pos (hN (m + N) (Nat.le_add_left N m))]
  -- Bound each of the three exponent pieces by `C_near_log`, `C₁`, `C₂` times `R * (log (R + 2))^2`.
  have hpiece1 : (F_near.card : ℝ) * Real.log (2 * R / δ) ≤
      C_near_log * R * (Real.log (R + 2)) ^ 2 := by
    have hcard_le : (F_near.card : ℝ) ≤ 6 * C₀ * R * Real.log (R + 2) :=
      le_trans (by exact_mod_cast Finset.card_le_card hF_near_sub) hS_card_le
    have harg_eq : 2 * R / δ = 4 * R * ((S.card : ℝ) + 1) := by
      dsimp only [δ]; field_simp; ring
    have hlog_le : Real.log (2 * R / δ) ≤ (Real.log (24 * C₀ + 4) + 3) * Real.log (R + 2) := by
      rw [harg_eq]
      have hlog_lin : Real.log (R + 2) ≤ R + 2 :=
        le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
      have hprod_le : 4 * R * ((S.card : ℝ) + 1) ≤ (24 * C₀ + 4) * (R + 2) ^ 3 := by
        have hS1 : (S.card : ℝ) + 1 ≤ (6 * C₀ + 1) * (R + 2) ^ 2 := by
          have h1 : 6 * C₀ * R * Real.log (R + 2) ≤ 6 * C₀ * (R + 2) ^ 2 := by
            have : R * Real.log (R + 2) ≤ (R + 2) * (R + 2) :=
              mul_le_mul (by linarith) hlog_lin (by linarith) (by linarith)
            nlinarith
          nlinarith
        have h4R : 4 * R ≤ 4 * (R + 2) := by linarith
        calc 4 * R * ((S.card : ℝ) + 1)
            ≤ (4 * (R + 2)) * ((6 * C₀ + 1) * (R + 2) ^ 2) :=
              mul_le_mul h4R hS1 (by positivity) (by linarith)
          _ = (24 * C₀ + 4) * (R + 2) ^ 3 := by ring
      calc Real.log (4 * R * ((S.card : ℝ) + 1))
          ≤ Real.log ((24 * C₀ + 4) * (R + 2) ^ 3) := Real.log_le_log (by positivity) hprod_le
        _ = Real.log (24 * C₀ + 4) + 3 * Real.log (R + 2) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num
        _ ≤ Real.log (24 * C₀ + 4) * Real.log (R + 2) + 3 * Real.log (R + 2) := by
            have hlog_c_nn : 0 ≤ Real.log (24 * C₀ + 4) := Real.log_nonneg (by linarith)
            nlinarith
        _ = (Real.log (24 * C₀ + 4) + 3) * Real.log (R + 2) := by ring
    have hlog_nn : 0 ≤ Real.log (2 * R / δ) := by
      rw [harg_eq]
      exact Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) S.card])
    calc (F_near.card : ℝ) * Real.log (2 * R / δ)
        ≤ (6 * C₀ * R * Real.log (R + 2)) * ((Real.log (24 * C₀ + 4) + 3) * Real.log (R + 2)) :=
          mul_le_mul hcard_le hlog_le hlog_nn (by positivity)
      _ = C_near_log * R * (Real.log (R + 2)) ^ 2 := by dsimp only [C_near_log]; ring
  have hpiece2 : R * ∑ i ∈ F_near, (‖ρ i‖)⁻¹ ≤ C₁ * R * (Real.log (R + 2)) ^ 2 := by
    have h1 := hnear_inv R hR_ge2 F_near (fun i hi => (Finset.mem_filter.mp hi).2)
    have h2 := mul_le_mul_of_nonneg_left h1 hR_pos.le
    linarith
  have hpiece3 : R ^ 2 * ((∑ i ∈ F_far, (‖ρ i‖ ^ 2)⁻¹) + ∑' m : ℕ, (‖ρ (m + N)‖ ^ 2)⁻¹) ≤
      C₂ * R * (Real.log (R + 2)) ^ 2 := by
    rw [hfar_tail_eq]
    have h1 := htail_sq R hR_ge2
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg R)
    have h3 : R ^ 2 * (C₂ * Real.log (R + 2) / R) = C₂ * R * Real.log (R + 2) := by
      field_simp [hR_pos.ne']
    rw [h3] at h2
    have hlog_le_sq : Real.log (R + 2) ≤ (Real.log (R + 2)) ^ 2 := by nlinarith
    have h4 : C₂ * R * Real.log (R + 2) ≤ C₂ * R * (Real.log (R + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hlog_le_sq (by positivity)
    exact h2.trans h4
  have hcomb_exp :
      Real.exp (-C * R * (Real.log (R + 2)) ^ 2) ≤
        Real.exp (-((F_near.card : ℝ) * Real.log (2 * R / δ) + R * ∑ i ∈ F_near, (‖ρ i‖)⁻¹)) *
        Real.exp (-(R ^ 2 * ∑ i ∈ F_far, (‖ρ i‖ ^ 2)⁻¹)) *
        Real.exp (-(R ^ 2 * ∑' m : ℕ, (‖ρ (m + N)‖ ^ 2)⁻¹)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [C]
    have hpos_Rlog : 0 ≤ R * (Real.log (R + 2)) ^ 2 := by positivity
    nlinarith
  have hprod_ge := mul_le_mul
    (mul_le_mul hnear_prod_ge hfar_prod_ge (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    htail_ge (Real.exp_pos _).le
    (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  exact hcomb_exp.trans hprod_ge

/-- Local factorization of `weierstrassProduct ρ` at any point `w : ℂ`:
`weierstrassProduct ρ z = (z - w) ^ m * Q z` near `w` where `Q` is analytic and nonzero at `w`
and `m` is the number of occurrences of `w` in `ρ`. -/
private lemma local_factor_weierstrassProduct {ρ : ℕ → ℂ} (hρ_ne : ∀ n, ρ n ≠ 0)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) (w : ℂ) :
    ∃ (A : Finset ℕ) (Q : ℂ → ℂ),
      (∀ n : ℕ, n ∈ A ↔ ρ n = w) ∧
      AnalyticAt ℂ Q w ∧ Q w ≠ 0 ∧
      ∀ᶠ z in 𝓝 w, weierstrassProduct ρ z = (z - w) ^ A.card * Q z := by
  classical
  set R : ℝ := ‖w‖ + 1
  have hR_pos : 0 < R := by positivity
  have htend := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq hρ_ne hsum
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (htend.eventually (Filter.eventually_ge_atTop (2 * R)))
  let U : Set ℂ := ball (0 : ℂ) R
  have hwU : w ∈ U := mem_ball_zero_iff.mpr (by linarith)
  let F : ℕ → ℂ → ℂ := fun m z => Complex.log (weierstrassE1 (z / ρ (m + N)))
  let L : ℂ → ℂ := fun z => ∑' m : ℕ, F m z
  let u : ℕ → ℝ := fun m => R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹
  have hu : Summable u := ((summable_nat_add_iff N).mpr hsum).mul_left (R ^ 2)
  have hsmall : ∀ m : ℕ, ∀ z ∈ U, ‖z / ρ (m + N)‖ ≤ 1 / 2 := fun m z hz => by
    have hzn : ‖z‖ < R := mem_ball_zero_iff.mp hz
    have hge : 2 * R ≤ ‖ρ (m + N)‖ := hN (m + N) (Nat.le_add_left N m)
    have hρ_pos : 0 < ‖ρ (m + N)‖ := by linarith
    rw [norm_div, div_le_iff₀ hρ_pos]; linarith
  have hF_diff : ∀ m : ℕ, DifferentiableOn ℂ (F m) U := fun m =>
    (differentiable_weierstrassE1.comp (differentiable_id.div_const _)).differentiableOn.clog
      fun z hz => Stage5JensenHadamard.weierstrassE1_mem_slitPlane (hsmall m z hz)
  have hF_bound : ∀ m : ℕ, ∀ z ∈ U, ‖F m z‖ ≤ u m := fun m z hz => by
    have hzn : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
    calc ‖F m z‖
        ≤ ‖z / ρ (m + N)‖ ^ 2 := Stage5JensenHadamard.norm_log_weierstrassE1_le_sq (hsmall m z hz)
      _ = ‖z‖ ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ := by rw [norm_div, div_pow, div_eq_mul_inv]
      _ ≤ R ^ 2 * (‖ρ (m + N)‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzn 2) (by positivity)
  have hL_diff : DifferentiableOn ℂ L U :=
    Complex.differentiableOn_tsum_of_summable_norm hu hF_diff isOpen_ball hF_bound
  have hL_an : AnalyticAt ℂ L w := hL_diff.analyticAt (isOpen_ball.mem_nhds hwU)
  let A : Finset ℕ := (Finset.range N).filter (fun i => ρ i = w)
  let B : Finset ℕ := (Finset.range N).filter (fun i => ρ i ≠ w)
  have hA_iff : ∀ n : ℕ, n ∈ A ↔ ρ n = w := fun n => by
    simp only [A, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    intro heq
    by_contra hge
    have h1 := hN n (not_lt.mp hge)
    rw [heq] at h1
    dsimp only [R] at h1
    linarith [norm_nonneg w]
  let Q : ℂ → ℂ := fun z =>
    (∏ i ∈ A, (-(1 / ρ i) * Complex.exp (z / ρ i))) *
    (∏ i ∈ B, weierstrassE1 (z / ρ i)) * Complex.exp (L z)
  have hQ_an : AnalyticAt ℂ Q w := by
    have h1 : AnalyticAt ℂ (fun z => ∏ i ∈ A, (-(1 / ρ i) * Complex.exp (z / ρ i))) w := by
      have hd : Differentiable ℂ (fun z => ∏ i ∈ A, (-(1 / ρ i) * Complex.exp (z / ρ i))) :=
        differentiable_finset_prod A (fun i z => -(1 / ρ i) * Complex.exp (z / ρ i)) fun i _ =>
          (differentiable_const _).mul (Complex.differentiable_exp.comp (differentiable_id.div_const _))
      exact hd.differentiableOn.analyticAt Filter.univ_mem
    have h2 : AnalyticAt ℂ (fun z => ∏ i ∈ B, weierstrassE1 (z / ρ i)) w := by
      have hd : Differentiable ℂ (fun z => ∏ i ∈ B, weierstrassE1 (z / ρ i)) :=
        differentiable_finset_prod B (fun i z => weierstrassE1 (z / ρ i)) fun i _ =>
          differentiable_weierstrassE1.comp (differentiable_id.div_const _)
      exact hd.differentiableOn.analyticAt Filter.univ_mem
    exact (h1.mul h2).mul hL_an.cexp
  have hQ_ne : Q w ≠ 0 := by
    dsimp only [Q]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
    · refine Finset.prod_ne_zero_iff.mpr fun i _ =>
        mul_ne_zero (neg_ne_zero.mpr (div_ne_zero one_ne_zero (hρ_ne i))) (Complex.exp_ne_zero _)
    · refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
      rw [ne_eq, weierstrassE1_eq_zero_iff, div_eq_one_iff_eq (hρ_ne i)]
      exact (Finset.mem_filter.mp hi).2.symm
  refine ⟨A, Q, hA_iff, hQ_an, hQ_ne, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hwU] with z hz
  rw [Stage5JensenHadamard.weierstrassProduct_eq_prefix_mul_exp_tail hρ_ne hsum hR_pos hN
    (ball_subset_closedBall hz)]
  have hsplit : ∏ i ∈ Finset.range N, weierstrassE1 (z / ρ i) =
      (∏ i ∈ A, weierstrassE1 (z / ρ i)) * (∏ i ∈ B, weierstrassE1 (z / ρ i)) :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.range N) (fun i => ρ i = w) _).symm
  have hA_prod : ∏ i ∈ A, weierstrassE1 (z / ρ i) =
      (z - w) ^ A.card * ∏ i ∈ A, (-(1 / ρ i) * Complex.exp (z / ρ i)) := by
    have hterm : ∀ i ∈ A, weierstrassE1 (z / ρ i) = (z - w) * (-(1 / ρ i) * Complex.exp (z / ρ i)) := by
      intro i hi
      have hρi_eq : ρ i = w := (hA_iff i).mp hi
      have hρi_ne : ρ i ≠ 0 := hρ_ne i
      unfold weierstrassE1
      rw [← hρi_eq]
      field_simp [hρi_ne]
      ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const]
  rw [hsplit, hA_prod]
  dsimp only [Q, L, F]
  ring

/-- **Entire Nonvanishing Quotient by a Genus-1 Weierstrass Product**:
if `f : ℂ → ℂ` is entire with `f 0 ≠ 0`, `ρ` is a multiplicity-counted zero sequence of `f`,
and `∑ (‖ρ n‖²)⁻¹ < ∞`, then there exists an entire nonvanishing function `g : ℂ → ℂ` such that
`∀ z, f z = g z * weierstrassProduct ρ z`. -/
theorem exists_entire_nonvanishing_quotient_weierstrass {f : ℂ → ℂ} {ρ : ℕ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hmult : IsMultiplicityZeroSeq f ρ)
    (hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z : ℂ, g z ≠ 0) ∧
      ∀ z : ℂ, f z = g z * weierstrassProduct ρ z := by
  let P : ℂ → ℂ := weierstrassProduct ρ
  have hf_an : ∀ z : ℂ, AnalyticAt ℂ f z := fun z =>
    (hf.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hne_top : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := analyticOrderAt_ne_top_of_entire_ne_zero hf hf0
  let g : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun z => f z / P z)
  have hlocal : ∀ w : ℂ, ∃ q : ℂ → ℂ, AnalyticAt ℂ q w ∧ q w ≠ 0 ∧
      g =ᶠ[𝓝 w] q ∧ f w = q w * P w := by
    intro w
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hf_an w).analyticOrderAt_ne_top.mp (hne_top w)
    obtain ⟨A, Q, hA_iff, hQ_an, hQ_ne, hQ_eq⟩ := local_factor_weierstrassProduct hmult.1 hsum w
    have hA_card : A.card = analyticOrderNatAt f w := (hmult.2 w).2 A hA_iff
    let q : ℂ → ℂ := fun z => h z / Q z
    have hq_an : AnalyticAt ℂ q w := hh_an.div hQ_an hQ_ne
    have hq_ne : q w ≠ 0 := div_ne_zero hh_ne hQ_ne
    have hQ_ne_ev : ∀ᶠ z in 𝓝 w, Q z ≠ 0 :=
      hQ_an.continuousAt.eventually_ne hQ_ne
    have hq_cont_ev : ∀ᶠ z in 𝓝 w, ContinuousAt q z :=
      hq_an.eventually_analyticAt.mono fun z hz => hz.continuousAt
    -- On an open neighborhood `U` of `w`, `f z = (z - w)^m * h z`, `P z = (z - w)^m * Q z`, `Q z ≠ 0`, `ContinuousAt q z`.
    have hev_all : ∀ᶠ z in 𝓝 w,
        f z = (z - w) ^ analyticOrderNatAt f w * h z ∧
        P z = (z - w) ^ analyticOrderNatAt f w * Q z ∧
        Q z ≠ 0 ∧ ContinuousAt q z := by
      filter_upwards [hh_eq, hQ_eq, hQ_ne_ev, hq_cont_ev] with z h1 h2 h3 h4
      refine ⟨by simpa [smul_eq_mul] using h1, ?_, h3, h4⟩
      simpa [P, hA_card] using h2
    obtain ⟨U, hU_sub, hU_open, hwU⟩ := _root_.eventually_nhds_iff.mp hev_all
    have hfp_eq_q : ∀ z ∈ U, z ≠ w → f z / P z = q z := by
      intro z hzU hzw
      obtain ⟨h1, h2, h3, _⟩ := hU_sub z hzU
      have hpow_ne : (z - w) ^ analyticOrderNatAt f w ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzw)
      rw [h1, h2]
      dsimp only [q]
      field_simp [hpow_ne, h3]
    have hg_eq_q : ∀ z ∈ U, g z = q z := by
      intro z hzU
      have hcont_z : ContinuousAt q z := (hU_sub z hzU).2.2.2
      have htend_q : Tendsto q (𝓝[≠] z) (𝓝 (q z)) := hcont_z.tendsto.mono_left nhdsWithin_le_nhds
      have htend_fp : Tendsto (fun u => f u / P u) (𝓝[≠] z) (𝓝 (q z)) := by
        refine htend_q.congr' ?_
        have hmem_U : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hU_open.mem_nhds hzU)
        have hmem_ne : ({w}ᶜ : Set ℂ) ∈ 𝓝[≠] z := by
          by_cases hzw : z = w
          · subst hzw; exact self_mem_nhdsWithin
          · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzw)
        filter_upwards [Filter.inter_mem hmem_U hmem_ne] with u ⟨huU, huw⟩
        exact (hfp_eq_q u huU huw).symm
      exact htend_fp.limUnder_eq
    have hfw : f w = q w * P w := by
      obtain ⟨h1, h2, h3, _⟩ := hU_sub w hwU
      rw [h1, h2]
      dsimp only [q]
      field_simp [h3]
    exact ⟨q, hq_an, hq_ne, Filter.eventually_of_mem (hU_open.mem_nhds hwU) hg_eq_q, hfw⟩
  refine ⟨g, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · obtain ⟨q, hq_an, _, heq, _⟩ := hlocal w
    exact hq_an.differentiableAt.congr_of_eventuallyEq heq
  · obtain ⟨q, _, hq_ne, heq, _⟩ := hlocal w
    rwa [heq.self_of_nhds]
  · obtain ⟨q, _, _, heq, hfw⟩ := hlocal w
    rwa [heq.self_of_nhds]

/-- **FULL HADAMARD FACTORIZATION THEOREM FOR ENTIRE ORDER-1 FUNCTIONS**:
for ANY entire function `f : ℂ → ℂ` with `f 0 ≠ 0`, `HasOrderOneGrowth f A B` (`A ≥ 0`), and
multiplicity-counted zero sequence `ρ : ℕ → ℂ`:
1. `∑' n, (‖ρ n‖ ^ 2)⁻¹ < ∞`,
2. `∃ a b : ℂ`, `∀ z, f z = Complex.exp (a + b * z) * weierstrassProduct ρ z`, and
3. `∀ z, (∀ n, z ≠ ρ n) → deriv f z / f z = b + ∑' n, (1 / (z - ρ n) + 1 / ρ n)`. -/
theorem hadamard_factorization_order_one {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hf : HasOrderOneGrowth f A B) (hf0 : f 0 ≠ 0)
    {ρ : ℕ → ℂ} (hmult : IsMultiplicityZeroSeq f ρ) :
    Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) ∧
    ∃ a b : ℂ,
      (∀ z : ℂ, f z = Complex.exp (a + b * z) * weierstrassProduct ρ z) ∧
      (∀ z : ℂ, (∀ n : ℕ, z ≠ ρ n) →
        deriv f z / f z = b + ∑' n : ℕ, (1 / (z - ρ n) + 1 / ρ n)) := by
  set C₀ : ℝ := (4 * A + max B 0 + max (-Real.log ‖f 0‖) 0) / Real.log 2
  have hC₀ : 0 ≤ C₀ := div_nonneg (by linarith [le_max_right B 0, le_max_right (-Real.log ‖f 0‖) 0])
    (Real.log_pos (by norm_num)).le
  have hcount : ∀ r : ℝ, 1 ≤ r → ∀ F : Finset ℕ,
      (∀ n ∈ F, ‖ρ n‖ ≤ r) → (F.card : ℝ) ≤ C₀ * r * Real.log (r + 2) :=
    order_one_multiplicity_zero_count_le hA hf hf0 hmult
  have hsum : Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) :=
    Stage5JensenHadamard.summable_inv_sq_of_zero_counting hC₀ hmult.1 hcount
  obtain ⟨g, hg_diff, hg_nz, hfg⟩ :=
    exists_entire_nonvanishing_quotient_weierstrass hf.1 hf0 hmult hsum
  obtain ⟨h, hh_diff, hge⟩ := exists_entire_log hg_diff hg_nz
  obtain ⟨C_P, hCP_pos, hmin⟩ := weierstrassProduct_min_modulus_good_circles hC₀ hmult.1 hcount
  -- Choose good circles `R k ∈ [k + 2, k + 3]` tending to `∞`.
  have hchoose : ∀ k : ℕ, ∃ R ∈ Set.Icc ((k : ℝ) + 2) ((k : ℝ) + 3),
      ∀ z ∈ Metric.sphere (0 : ℂ) R,
        weierstrassProduct ρ z ≠ 0 ∧
        Real.exp (-C_P * R * (Real.log (R + 2)) ^ 2) ≤ ‖weierstrassProduct ρ z‖ := fun k => by
    have := hmin ((k : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    simpa [add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using this
  choose R hR_mem hR_bd using hchoose
  have hR_top : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun k => (hR_mem k).1)
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let M : ℕ → ℝ := fun k => (A + C_P) * (R k + 2) * (Real.log (R k + 2)) ^ 2 + B
  have hM_bound : ∀ k : ℕ, ∀ z ∈ Metric.sphere (0 : ℂ) (R k), (h z).re ≤ M k := by
    intro k z hz
    have hzn : ‖z‖ = R k := mem_sphere_zero_iff_norm.mp hz
    have hRk_ge2 : 2 ≤ R k := by linarith [(hR_mem k).1, Nat.cast_nonneg (α := ℝ) k]
    have hlog_ge1 : 1 ≤ Real.log (R k + 2) := by
      have he : Real.exp 1 ≤ R k + 2 := by linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (R k + 2) := Real.log_le_log (Real.exp_pos 1) he
    have ⟨hW_ne, hW_ge⟩ := hR_bd k z hz
    have hW_pos : 0 < ‖weierstrassProduct ρ z‖ := norm_pos_iff.mpr hW_ne
    have hnorm_eq : ‖f z‖ = Real.exp (h z).re * ‖weierstrassProduct ρ z‖ := by
      rw [hfg z, hge z, norm_mul, Complex.norm_exp]
    have hf_le : ‖f z‖ ≤ Real.exp (A * R k * Real.log (R k + 2) + B) := by
      simpa [hzn] using hf.2 z
    have hprod_le : Real.exp (h z).re * Real.exp (-C_P * R k * (Real.log (R k + 2)) ^ 2) ≤
        Real.exp (A * R k * Real.log (R k + 2) + B) := by
      calc Real.exp (h z).re * Real.exp (-C_P * R k * (Real.log (R k + 2)) ^ 2)
          ≤ Real.exp (h z).re * ‖weierstrassProduct ρ z‖ :=
            mul_le_mul_of_nonneg_left hW_ge (Real.exp_pos _).le
        _ = ‖f z‖ := hnorm_eq.symm
        _ ≤ Real.exp (A * R k * Real.log (R k + 2) + B) := hf_le
    rw [← Real.exp_add] at hprod_le
    have hlin := Real.exp_le_exp.mp hprod_le
    have hA_le : A * R k * Real.log (R k + 2) ≤ A * (R k + 2) * (Real.log (R k + 2)) ^ 2 := by
      have h1 : R k * Real.log (R k + 2) ≤ (R k + 2) * (Real.log (R k + 2)) ^ 2 :=
        mul_le_mul (by linarith) (by nlinarith) (by linarith) (by linarith)
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hA
    have hCP_le : C_P * R k * (Real.log (R k + 2)) ^ 2 ≤
        C_P * (R k + 2) * (Real.log (R k + 2)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (R k + 2))]
    dsimp only [M]
    linarith
  have hM_subquad : Tendsto (fun k => M k / (R k) ^ 2) atTop (nhds 0) :=
    (tendsto_mul_log_sq_div_sq_atTop (A + C_P) B).comp hR_top
  obtain ⟨a, b, hab⟩ := entire_eq_linear_of_re_circle_seq hh_diff hR_top hM_bound hM_subquad
  have hf_eq : ∀ z : ℂ, f z = Complex.exp (a + b * z) * weierstrassProduct ρ z := fun z => by
    rw [hfg z, hge z, hab z]
  refine ⟨hsum, a, b, hf_eq, fun z hz => ?_⟩
  have hfun : f = fun w => Complex.exp a * Complex.exp (b * w) * weierstrassProduct ρ w := by
    funext w; rw [hf_eq w, Complex.exp_add]
  rw [hfun]
  exact Stage5JensenHadamard.hadamard_canonical_logDeriv_eq (Complex.exp_ne_zero a) hmult.1 hsum hz

/-! ## Section 3: Unconditional Infinitude of Zeros & Exact Enumeration `xiZeroSeq` -/

/-- Auxiliary lower bound `1 ≤ ‖riemannZeta (σ : ℂ)‖` for real `σ ≥ 2`. -/
private lemma one_le_norm_riemannZeta_of_two_le_real {σ : ℝ} (hσ : 2 ≤ σ) :
    (1 : ℝ) ≤ ‖riemannZeta (σ : ℂ)‖ := by
  have hσ1 : 1 < ((σ : ℂ)).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hσ1]
  have hsumm_r : Summable (fun k : ℕ => ((k : ℝ) ^ σ)⁻¹) := by
    have h := Real.summable_nat_rpow_inv.mpr (by linarith : 1 < σ)
    exact h
  have hsumm_c : Summable (fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ (σ : ℂ)) := by
    refine Summable.of_norm_bounded hsumm_r fun k => ?_
    cases k with
    | zero =>
      have hne : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      simp [Complex.zero_cpow hne]
      positivity
    | succ m =>
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m), one_div]
      simp
  have hre_tsum : (∑' k : ℕ, (1 : ℂ) / (k : ℂ) ^ (σ : ℂ)).re =
      ∑' k : ℕ, ((1 : ℂ) / (k : ℂ) ^ (σ : ℂ)).re := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hsumm_c
  have hterm_nn : ∀ k : ℕ, 0 ≤ ((1 : ℂ) / (k : ℂ) ^ (σ : ℂ)).re := fun k => by
    cases k with
    | zero =>
      have hne : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      simp [Complex.zero_cpow hne]
    | succ m =>
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
        ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity
  have hterm_1 : ((1 : ℂ) / ((1 : ℕ) : ℂ) ^ (σ : ℂ)).re = 1 := by simp
  have hge1 : (1 : ℝ) ≤ (∑' k : ℕ, (1 : ℂ) / (k : ℂ) ^ (σ : ℂ)).re := by
    rw [hre_tsum, ← hterm_1]
    exact (Complex.reCLM.summable hsumm_c).le_tsum 1 (fun k _ => hterm_nn k)
  exact hge1.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

/-- **UNCONDITIONAL INFINITUDE OF ZEROS OF MATHLIB'S `xi(s)` (`0` ASSUMPTIONS!)**:
if `xi` had only finitely many zeros, then dividing by the finite zero polynomial would yield an
entire nonvanishing function of order `≤ 1`, forcing `xi(2n) = O(K^n)` by Borel–Carathéodory
Liouville, contradicting `‖xi(2n)‖ ≥ (n - 1)! / π^n`! -/
theorem infinite_xi_zeros : {s : ℂ | xi s = 0}.Infinite := by
  classical
  intro hfin
  let Z : Finset ℂ := hfin.toFinset
  let Q : ℂ → ℂ := fun s => ∏ ρ ∈ Z, (s - ρ) ^ analyticOrderNatAt xi ρ
  have hQ_diff : Differentiable ℂ Q :=
    differentiable_finset_prod Z (fun ρ s => (s - ρ) ^ analyticOrderNatAt xi ρ) fun ρ _ =>
      (differentiable_id.sub (differentiable_const ρ)).pow _
  have hxi_an : ∀ z : ℂ, AnalyticAt ℂ xi z := fun z =>
    (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hxi0 : xi 0 ≠ 0 := by simp
  have hne_top : ∀ z : ℂ, analyticOrderAt xi z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_ne_zero differentiable_xi hxi0
  -- Local factorization of `Q` matches `xi` at every `w : ℂ`, so `g = xi / Q` extends to an entire nonvanishing function.
  let g : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun z => xi z / Q z)
  have hlocal : ∀ w : ℂ, ∃ q : ℂ → ℂ, AnalyticAt ℂ q w ∧ q w ≠ 0 ∧
      g =ᶠ[𝓝 w] q ∧ xi w = q w * Q w := by
    intro w
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hxi_an w).analyticOrderAt_ne_top.mp (hne_top w)
    have hQ_loc : ∃ Q₁ : ℂ → ℂ, AnalyticAt ℂ Q₁ w ∧ Q₁ w ≠ 0 ∧
        ∀ z : ℂ, Q z = (z - w) ^ analyticOrderNatAt xi w * Q₁ z := by
      by_cases hwZ : w ∈ Z
      · refine ⟨fun z => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt xi ρ, ?_, ?_, fun z => ?_⟩
        · exact (differentiable_finset_prod (Z.erase w) (fun ρ z => (z - ρ) ^ analyticOrderNatAt xi ρ)
            fun ρ _ => (differentiable_id.sub (differentiable_const ρ)).pow _).differentiableOn.analyticAt
            Filter.univ_mem
        · refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
            pow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_erase.mp hρ).1.symm)
        · exact (Finset.mul_prod_erase Z (fun ρ => (z - ρ) ^ analyticOrderNatAt xi ρ) hwZ).symm
      · have hxiw_ne : xi w ≠ 0 := fun hw0 => hwZ (hfin.mem_toFinset.mpr hw0)
        have hord0 : analyticOrderNatAt xi w = 0 := by
          have h0 : analyticOrderAt xi w = 0 := (hxi_an w).analyticOrderAt_eq_zero.mpr hxiw_ne
          simp [analyticOrderNatAt, h0]
        refine ⟨Q, hQ_diff.differentiableOn.analyticAt Filter.univ_mem, ?_, fun z => by simp [hord0]⟩
        refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr fun heq => hwZ (heq ▸ hρ))
    obtain ⟨Q₁, hQ₁_an, hQ₁_ne, hQ₁_eq⟩ := hQ_loc
    let q : ℂ → ℂ := fun z => h z / Q₁ z
    have hq_an : AnalyticAt ℂ q w := hh_an.div hQ₁_an hQ₁_ne
    have hq_ne : q w ≠ 0 := div_ne_zero hh_ne hQ₁_ne
    have hev_all : ∀ᶠ z in 𝓝 w,
        xi z = (z - w) ^ analyticOrderNatAt xi w * h z ∧
        Q₁ z ≠ 0 ∧ ContinuousAt q z := by
      filter_upwards [hh_eq, hQ₁_an.continuousAt.eventually_ne hQ₁_ne,
        hq_an.eventually_analyticAt.mono fun z hz => hz.continuousAt] with z h1 h2 h3
      exact ⟨by simpa [smul_eq_mul] using h1, h2, h3⟩
    obtain ⟨U, hU_sub, hU_open, hwU⟩ := _root_.eventually_nhds_iff.mp hev_all
    have hfp : ∀ z ∈ U, z ≠ w → xi z / Q z = q z := by
      intro z hzU hzw
      obtain ⟨h1, h2, _⟩ := hU_sub z hzU
      have hpow_ne : (z - w) ^ analyticOrderNatAt xi w ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzw)
      rw [h1, hQ₁_eq z]
      dsimp only [q]
      field_simp [hpow_ne, h2]
    have hg_eq : ∀ z ∈ U, g z = q z := by
      intro z hzU
      have htend_q : Tendsto q (𝓝[≠] z) (𝓝 (q z)) :=
        (hU_sub z hzU).2.2.tendsto.mono_left nhdsWithin_le_nhds
      have htend_fp : Tendsto (fun u => xi u / Q u) (𝓝[≠] z) (𝓝 (q z)) := by
        refine htend_q.congr' ?_
        have hmem_U : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hU_open.mem_nhds hzU)
        have hmem_ne : ({w}ᶜ : Set ℂ) ∈ 𝓝[≠] z := by
          by_cases hzw : z = w
          · subst hzw; exact self_mem_nhdsWithin
          · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzw)
        filter_upwards [Filter.inter_mem hmem_U hmem_ne] with u ⟨huU, huw⟩
        exact (hfp u huU huw).symm
      exact htend_fp.limUnder_eq
    have hxiw : xi w = q w * Q w := by
      obtain ⟨h1, h2, _⟩ := hU_sub w hwU
      rw [h1, hQ₁_eq w]
      dsimp only [q]
      field_simp [h2]
    exact ⟨q, hq_an, hq_ne, Filter.eventually_of_mem (hU_open.mem_nhds hwU) hg_eq, hxiw⟩
  have hg_diff : Differentiable ℂ g := fun w => by
    obtain ⟨q, hq_an, _, heq, _⟩ := hlocal w
    exact hq_an.differentiableAt.congr_of_eventuallyEq heq
  have hg_nz : ∀ w : ℂ, g w ≠ 0 := fun w => by
    obtain ⟨q, _, hq_ne, heq, _⟩ := hlocal w; rwa [heq.self_of_nhds]
  have hxi_eq_gQ : ∀ w : ℂ, xi w = g w * Q w := fun w => by
    obtain ⟨q, _, _, heq, hfw⟩ := hlocal w; rwa [heq.self_of_nhds]
  -- Order-1 growth bound for `g`: outside `R₀`, `‖Q s‖ ≥ 1`; inside `closedBall 0 R₀`, `g` is bounded.
  obtain ⟨A, hA_pos, B, hB_pos, hxi_bd⟩ := Stage5StirlingPhragmen.norm_xi_order_one_bound
  set M_nat : ℕ := Z.sup (fun ρ => ⌈‖ρ‖⌉₊)
  set R₀ : ℝ := (M_nat : ℝ) + 2
  have hR₀_ge2 : 2 ≤ R₀ := by dsimp only [R₀]; linarith [Nat.cast_nonneg (α := ℝ) M_nat]
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn
    hg_diff.continuous.continuousOn
  set B' : ℝ := max B (Real.log (max M₀ 1))
  have hg_bd : ∀ s : ℂ, ‖g s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B') := by
    intro s
    have hA_nn : 0 ≤ A * (‖s‖ + 2) * Real.log (‖s‖ + 2) := by
      have hlog : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
      positivity
    by_cases hs : ‖s‖ ≤ R₀
    · have h1 : ‖g s‖ ≤ max M₀ 1 :=
        (hM₀ s (mem_closedBall_zero_iff.mpr hs)).trans (le_max_left M₀ 1)
      have h2 : max M₀ 1 ≤ Real.exp B' := by
        rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1))]
        exact Real.exp_le_exp.mpr (le_max_right B _)
      exact h1.trans (h2.trans (Real.exp_le_exp.mpr (by linarith)))
    · push Not at hs
      have hQ_ge1 : (1 : ℝ) ≤ ‖Q s‖ := by
        dsimp only [Q]
        rw [norm_prod]
        have hfac : ∀ ρ ∈ Z, (1 : ℝ) ≤ ‖(s - ρ) ^ analyticOrderNatAt xi ρ‖ := by
          intro ρ hρ
          rw [norm_pow]
          refine one_le_pow₀ ?_
          have hρ_le : ‖ρ‖ ≤ (M_nat : ℝ) := by
            have h1 : ‖ρ‖ ≤ (⌈‖ρ‖⌉₊ : ℝ) := Nat.le_ceil ‖ρ‖
            have h2 : ⌈‖ρ‖⌉₊ ≤ M_nat := Finset.le_sup (f := fun x => ⌈‖x‖⌉₊) hρ
            exact h1.trans (by exact_mod_cast h2)
          have htri : ‖s‖ - ‖ρ‖ ≤ ‖s - ρ‖ := norm_sub_norm_le s ρ
          dsimp only [R₀] at hs
          linarith
        simpa using Finset.prod_le_prod (fun _ _ => zero_le_one) hfac
      have hgn : ‖g s‖ ≤ ‖xi s‖ := by
        rw [hxi_eq_gQ s, norm_mul]
        have h1 : ‖g s‖ * 1 ≤ ‖g s‖ * ‖Q s‖ :=
          mul_le_mul_of_nonneg_left hQ_ge1 (norm_nonneg (g s))
        linarith
      exact hgn.trans ((hxi_bd s).trans (Real.exp_le_exp.mpr (by linarith [le_max_left B (Real.log (max M₀ 1))])))
  obtain ⟨a, b, hab⟩ := entire_nonvanishing_order_lt_two_eq_exp_linear hg_diff hg_nz hg_bd
  -- Now compare `‖xi (2 * (n + 2))‖ ≥ (n + 1)! / π^(n + 2)` against `O(K^(n + 2))`.
  set D : ℕ := ∑ ρ ∈ Z, analyticOrderNatAt xi ρ
  set C₁ : ℝ := Real.exp a.re * (R₀ + 2) ^ D
  set K : ℝ := Real.exp ((D : ℝ) + 2 * ‖b‖)
  have hC₁_pos : 0 < C₁ := by positivity
  have hK_pos : 0 < K := Real.exp_pos _
  have hcontra_bound : ∀ n : ℕ,
      1 ≤ C₁ * (Real.pi * K) * ((Real.pi * K) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
    intro n
    set m : ℕ := n + 2
    set s : ℂ := ((2 * m : ℕ) : ℂ)
    have hm_pos : 0 < m := by positivity
    have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
    have hs_re : s.re = 2 * (m : ℝ) := by dsimp only [s]; push_cast; simp
    have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs_re; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs_re; linarith
    have hs_gt1 : 1 < s.re := by rw [hs_re]; linarith
    -- Lower bound on `‖xi s‖`:
    have hxi_def : xi s = s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) *
        Complex.Gamma (s / 2) * riemannZeta s) := by
      rw [xi_eq_mul_completedRiemannZeta hs0 hs1, completedZeta_eq_tsum_of_one_lt_re hs_gt1,
        ← zeta_eq_tsum_one_div_nat_cpow hs_gt1]
    have hs_div2 : s / 2 = (m : ℂ) := by
      dsimp only [s]; push_cast; ring
    have hG_eq : Complex.Gamma (s / 2) = (((n + 1).factorial : ℕ) : ℂ) := by
      have hm_cast : (m : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 := by dsimp only [m]; push_cast; ring
      rw [hs_div2, hm_cast]
      exact Complex.Gamma_nat_eq_factorial (n + 1)
    have hpi_norm : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = (Real.pi ^ m)⁻¹ := by
      have harg : -s / 2 = ((-(m : ℝ)) : ℂ) := by
        dsimp only [s]; push_cast; ring
      rw [harg, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      simp [Real.rpow_neg Real.pi_pos.le]
    have hZ_ge1 : (1 : ℝ) ≤ ‖riemannZeta s‖ := by
      have hs_real : s = ((2 * (m : ℝ) : ℝ) : ℂ) := by dsimp only [s]; push_cast; ring
      rw [hs_real]
      exact one_le_norm_riemannZeta_of_two_le_real (by linarith)
    have hpoly_ge1 : (1 : ℝ) ≤ ‖s‖ * ‖s - 1‖ := by
      have h1 : (1 : ℝ) ≤ ‖s‖ := by
        have := (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
        rw [hs_re] at this; linarith
      have h2 : (1 : ℝ) ≤ ‖s - 1‖ := by
        have := (le_abs_self (s - 1).re).trans (Complex.abs_re_le_norm (s - 1))
        simp only [Complex.sub_re, hs_re, Complex.one_re] at this; linarith
      nlinarith
    have hxi_lower : ((n + 1).factorial : ℝ) / Real.pi ^ m ≤ ‖xi s‖ := by
      rw [hxi_def, norm_mul, norm_mul, norm_mul, norm_mul, hpi_norm, hG_eq]
      have hGnorm : ‖(((n + 1).factorial : ℕ) : ℂ)‖ = ((n + 1).factorial : ℝ) :=
        Complex.norm_natCast _
      rw [hGnorm]
      calc ((n + 1).factorial : ℝ) / Real.pi ^ m
          = 1 * ((Real.pi ^ m)⁻¹ * ((n + 1).factorial : ℝ) * 1) := by ring
        _ ≤ (‖s‖ * ‖s - 1‖) * ((Real.pi ^ m)⁻¹ * ((n + 1).factorial : ℝ) * ‖riemannZeta s‖) :=
            mul_le_mul hpoly_ge1 (mul_le_mul_of_nonneg_left hZ_ge1 (by positivity))
              (by positivity) (by positivity)
    -- Upper bound on `‖xi s‖ = ‖exp(a + b * s) * Q s‖`:
    have hexp_upper : ‖Complex.exp (a + b * s)‖ ≤ Real.exp a.re * Real.exp (2 * ‖b‖ * (m : ℝ)) := by
      rw [Complex.norm_exp, Complex.add_re, Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      have h1 : (b * s).re ≤ ‖b * s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      have hsn : ‖s‖ = 2 * (m : ℝ) := by
        dsimp only [s]; rw [Complex.norm_natCast]; push_cast; ring
      rw [norm_mul, hsn] at h1
      linarith
    have hQ_upper : ‖Q s‖ ≤ (R₀ + 2) ^ D * Real.exp ((D : ℝ) * (m : ℝ)) := by
      dsimp only [Q]
      rw [norm_prod]
      have hfac : ∀ ρ ∈ Z, ‖(s - ρ) ^ analyticOrderNatAt xi ρ‖ ≤
          ((R₀ + 2) * Real.exp (m : ℝ)) ^ analyticOrderNatAt xi ρ := by
        intro ρ hρ
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
        have hsn : ‖s‖ = 2 * (m : ℝ) := by dsimp only [s]; rw [Complex.norm_natCast]; push_cast; ring
        have hρ_le : ‖ρ‖ ≤ R₀ := by
          have h1 : ‖ρ‖ ≤ (⌈‖ρ‖⌉₊ : ℝ) := Nat.le_ceil ‖ρ‖
          have h2 : ⌈‖ρ‖⌉₊ ≤ M_nat := Finset.le_sup (f := fun x => ⌈‖x‖⌉₊) hρ
          have h3 : (⌈‖ρ‖⌉₊ : ℝ) ≤ (M_nat : ℝ) := by exact_mod_cast h2
          dsimp only [R₀]; linarith
        have hm_le_exp : (m : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
        have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
        calc ‖s - ρ‖ ≤ ‖s‖ + ‖ρ‖ := norm_sub_le s ρ
          _ ≤ 2 * (m : ℝ) + R₀ := by linarith
          _ ≤ (R₀ + 2) * (m : ℝ) := by nlinarith
          _ ≤ (R₀ + 2) * Real.exp (m : ℝ) := mul_le_mul_of_nonneg_left hm_le_exp (by linarith)
      calc ∏ ρ ∈ Z, ‖(s - ρ) ^ analyticOrderNatAt xi ρ‖
          ≤ ∏ ρ ∈ Z, ((R₀ + 2) * Real.exp (m : ℝ)) ^ analyticOrderNatAt xi ρ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
        _ = ((R₀ + 2) * Real.exp (m : ℝ)) ^ D := by rw [← Finset.prod_pow_eq_pow_sum]
        _ = (R₀ + 2) ^ D * Real.exp ((D : ℝ) * (m : ℝ)) := by
            rw [mul_pow, ← Real.exp_nat_mul]
    have hxi_upper : ‖xi s‖ ≤ C₁ * K ^ m := by
      rw [hxi_eq_gQ s, hab s, norm_mul]
      calc ‖Complex.exp (a + b * s)‖ * ‖Q s‖
          ≤ (Real.exp a.re * Real.exp (2 * ‖b‖ * (m : ℝ))) *
              ((R₀ + 2) ^ D * Real.exp ((D : ℝ) * (m : ℝ))) :=
            mul_le_mul hexp_upper hQ_upper (norm_nonneg _) (by positivity)
        _ = C₁ * Real.exp ((m : ℝ) * ((D : ℝ) + 2 * ‖b‖)) := by
            dsimp only [C₁]; rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring
        _ = C₁ * K ^ m := by dsimp only [K]; rw [Real.exp_nat_mul]
    have hcomb : ((n + 1).factorial : ℝ) / Real.pi ^ m ≤ C₁ * K ^ m := hxi_lower.trans hxi_upper
    have hfac_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hpi_pow_pos : (0 : ℝ) < Real.pi ^ m := pow_pos Real.pi_pos m
    have hmul := (div_le_iff₀ hpi_pow_pos).mp hcomb
    have hdiv : (1 : ℝ) ≤ C₁ * K ^ m * Real.pi ^ m / ((n + 1).factorial : ℝ) :=
      (le_div_iff₀ hfac_pos).mpr (by simpa [one_mul] using hmul)
    have hrhs : C₁ * K ^ m * Real.pi ^ m / ((n + 1).factorial : ℝ) =
        C₁ * (Real.pi * K) * ((Real.pi * K) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      have hm_eq : m = (n + 1) + 1 := rfl
      rw [hm_eq, pow_succ, pow_succ, mul_pow]
      ring
    linarith
  have htend_zero : Tendsto (fun n : ℕ =>
      C₁ * (Real.pi * K) * ((Real.pi * K) ^ (n + 1) / ((n + 1).factorial : ℝ))) atTop (nhds 0) := by
    have h1 := (FloorSemiring.tendsto_pow_div_factorial_atTop (Real.pi * K)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h1.const_mul (C₁ * (Real.pi * K))
  have hle0 : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto htend_zero (Eventually.of_forall hcontra_bound)
  linarith

/-- Type of zeros of `xi` paired with their multiplicity index `Fin (analyticOrderNatAt xi z)`. -/
abbrev XiZeroWithMult : Type :=
  Σ z : {s : ℂ // xi s = 0}, Fin (analyticOrderNatAt xi z.1)

lemma analyticOrderNatAt_xi_pos {z : ℂ} (hz : xi z = 0) : 0 < analyticOrderNatAt xi z := by
  have hxi_an : ∀ w : ℂ, AnalyticAt ℂ xi w := fun w =>
    (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ) w (Set.mem_univ w)
  have hne_top : analyticOrderAt xi z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_ne_zero differentiable_xi (by simp) z
  have hne0 : analyticOrderAt xi z ≠ 0 := (hxi_an z).analyticOrderAt_ne_zero.mpr hz
  have hnat_ne : analyticOrderNatAt xi z ≠ 0 := by
    intro h0
    have hcoe : (analyticOrderNatAt xi z : ℕ∞) = analyticOrderAt xi z := ENat.natCast_toNat hne_top
    rw [h0, Nat.cast_zero] at hcoe
    exact hne0 hcoe.symm
  exact Nat.pos_of_ne_zero hnat_ne

instance : Countable {s : ℂ // xi s = 0} := by
  have hset : {s : ℂ | xi s = 0} = {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0} := by
    ext s; exact xi_eq_zero_iff_critical_strip_zeta_zero s
  have hc : {s : ℂ | xi s = 0}.Countable := by
    rw [hset]; exact Stage6XiZeroDensity.countable_critical_strip_riemannZeta_zeros
  exact hc.to_subtype

instance : Infinite {s : ℂ // xi s = 0} := infinite_xi_zeros.to_subtype

instance : Countable XiZeroWithMult := instCountableSigma

instance : Infinite XiZeroWithMult :=
  Infinite.of_injective (fun z : {s : ℂ // xi s = 0} => ⟨z, ⟨0, analyticOrderNatAt_xi_pos z.2⟩⟩)
    fun z₁ z₂ h => by cases h; rfl

/-- Canonical bijection `ℕ ≃ XiZeroWithMult` enumerating all zeros of `xi` with exact multiplicity. -/
def xiZeroEquiv : ℕ ≃ XiZeroWithMult :=
  letI : Encodable XiZeroWithMult := Encodable.ofCountable XiZeroWithMult
  letI : Denumerable XiZeroWithMult := Denumerable.ofEncodableOfInfinite XiZeroWithMult
  (Denumerable.eqv XiZeroWithMult).symm

/-- **Unconditional Multiplicity-Counted Enumeration `xiZeroSeq : ℕ → ℂ`** of ALL zeros of
Mathlib's actual `Stage5StirlingPhragmen.xi`. -/
def xiZeroSeq (n : ℕ) : ℂ := (xiZeroEquiv n).1.1

theorem xiZeroSeq_zero (n : ℕ) : xi (xiZeroSeq n) = 0 := (xiZeroEquiv n).1.2

theorem xiZeroSeq_strip (n : ℕ) : 0 < (xiZeroSeq n).re ∧ (xiZeroSeq n).re < 1 := by
  have h := (xi_eq_zero_iff_critical_strip_zeta_zero (xiZeroSeq n)).mp (xiZeroSeq_zero n)
  exact ⟨h.1, h.2.1⟩

theorem xiZeroSeq_riemannZeta_zero (n : ℕ) : riemannZeta (xiZeroSeq n) = 0 :=
  ((xi_eq_zero_iff_critical_strip_zeta_zero (xiZeroSeq n)).mp (xiZeroSeq_zero n)).2.2

theorem xiZeroSeq_ne_zero (n : ℕ) : xiZeroSeq n ≠ 0 := by
  intro h
  have hpos := (xiZeroSeq_strip n).1
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- `xiZeroSeq` enumerates every zero of `xi` with its exact analytic multiplicity `analyticOrderNatAt xi w`. -/
theorem isMultiplicityZeroSeq_xi : IsMultiplicityZeroSeq xi xiZeroSeq := by
  classical
  refine ⟨xiZeroSeq_ne_zero, fun w => ?_⟩
  by_cases hw : xi w = 0
  · let f : Fin (analyticOrderNatAt xi w) → ℕ := fun j => xiZeroEquiv.symm ⟨⟨w, hw⟩, j⟩
    have hf_inj : Function.Injective f := fun j₁ j₂ h => by
      have h1 := xiZeroEquiv.symm.injective h
      cases h1; rfl
    have hset_eq : {n : ℕ | xiZeroSeq n = w} = Set.range f := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_range, xiZeroSeq, f]
      constructor
      · intro h
        refine ⟨(xiZeroEquiv n).2.cast (by rw [h]), ?_⟩
        apply xiZeroEquiv.injective
        rw [Equiv.apply_symm_apply]
        refine Sigma.ext (Subtype.ext h.symm) ?_
        exact (Fin.heq_ext_iff (congrArg (analyticOrderNatAt xi) h.symm)).mpr rfl
      · rintro ⟨j, rfl⟩
        simp
    refine ⟨by rw [hset_eq]; exact Set.finite_range f, fun F hF => ?_⟩
    have hF_eq : F = Finset.univ.image f := by
      ext n
      rw [hF n, Finset.mem_image]
      have hmem : n ∈ {m : ℕ | xiZeroSeq m = w} ↔ n ∈ Set.range f := by rw [hset_eq]
      simpa using hmem
    rw [hF_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  · have hxi_an : AnalyticAt ℂ xi w :=
      (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ) w (Set.mem_univ w)
    have hord0 : analyticOrderNatAt xi w = 0 := by
      have h0 : analyticOrderAt xi w = 0 := hxi_an.analyticOrderAt_eq_zero.mpr hw
      simp [analyticOrderNatAt, h0]
    have hempty : {n : ℕ | xiZeroSeq n = w} = ∅ := by
      ext n; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hw (h ▸ xiZeroSeq_zero n)
    refine ⟨by rw [hempty]; exact Set.finite_empty, fun F hF => ?_⟩
    have hFe : F = ∅ := by
      ext n; simp only [hF n, Finset.notMem_empty, iff_false]
      intro h; exact hw (h ▸ xiZeroSeq_zero n)
    rw [hFe, Finset.card_empty, hord0]

/-- **Unconditional Inverse-Square Summability of `xiZeroSeq`** (counted with multiplicity!). -/
theorem xiZeroSeq_summable_inv_sq : Summable (fun n : ℕ => (‖xiZeroSeq n‖ ^ 2)⁻¹) := by
  obtain ⟨A, hA, B, _, hxi⟩ := Stage6XiZeroDensity.hasOrderOneGrowth_xi
  have hxi0 : xi 0 ≠ 0 := by simp
  set C₀ : ℝ := (4 * A + max B 0 + max (-Real.log ‖xi 0‖) 0) / Real.log 2
  have hC₀ : 0 ≤ C₀ := div_nonneg (by linarith [le_max_right B 0, le_max_right (-Real.log ‖xi 0‖) 0])
    (Real.log_pos (by norm_num)).le
  exact Stage5JensenHadamard.summable_inv_sq_of_zero_counting hC₀ xiZeroSeq_ne_zero
    (order_one_multiplicity_zero_count_le hA.le hxi hxi0 isMultiplicityZeroSeq_xi)

/-- **Unconditional Convergence-Exponent Summability of `xiZeroSeq`** for every `σ > 1`. -/
theorem xiZeroSeq_summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖xiZeroSeq n‖ ^ (-σ)) := by
  obtain ⟨A, hA, B, _, hxi⟩ := Stage6XiZeroDensity.hasOrderOneGrowth_xi
  have hxi0 : xi 0 ≠ 0 := by simp
  set C₀ : ℝ := (4 * A + max B 0 + max (-Real.log ‖xi 0‖) 0) / Real.log 2
  have hC₀ : 0 ≤ C₀ := div_nonneg (by linarith [le_max_right B 0, le_max_right (-Real.log ‖xi 0‖) 0])
    (Real.log_pos (by norm_num)).le
  exact Stage5JensenHadamard.summable_rpow_neg_of_zero_counting hC₀ xiZeroSeq_ne_zero
    (order_one_multiplicity_zero_count_le hA.le hxi hxi0 isMultiplicityZeroSeq_xi) hσ

/-- Helper: `w ↦ starRingEnd ℂ (h (1 - starRingEnd ℂ w))` is differentiable wherever `h` is
differentiable at `1 - starRingEnd ℂ w`. -/
private lemma hasDerivAt_conj_comp_one_sub_conj {h : ℂ → ℂ} {w : ℂ}
    (hh : DifferentiableAt ℂ h (1 - starRingEnd ℂ w)) :
    HasDerivAt (fun z : ℂ => starRingEnd ℂ (h (1 - starRingEnd ℂ z)))
      (-(starRingEnd ℂ (deriv h (1 - starRingEnd ℂ w)))) w := by
  have hd : HasDerivAt h (deriv h (1 - starRingEnd ℂ w)) (1 - starRingEnd ℂ w) := hh.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd ⊢
  have hmap_cont : Continuous (fun t : ℂ => -starRingEnd ℂ t) := Complex.continuous_conj.neg
  have hmap_nhds : Tendsto (fun t : ℂ => -starRingEnd ℂ t) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (hmap_cont.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_ne_zero.mpr ((map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr ht)
  have hcomp : Tendsto (fun t : ℂ =>
      -(starRingEnd ℂ ((-starRingEnd ℂ t)⁻¹ •
        (h (1 - starRingEnd ℂ w + (-starRingEnd ℂ t)) - h (1 - starRingEnd ℂ w)))))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-(starRingEnd ℂ (deriv h (1 - starRingEnd ℂ w))))) :=
    (Complex.continuous_conj.neg.tendsto _).comp (hd.comp hmap_nhds)
  refine hcomp.congr fun t => ?_
  have harg : 1 - starRingEnd ℂ (w + t) = 1 - starRingEnd ℂ w + (-starRingEnd ℂ t) := by
    rw [map_add]; ring
  rw [harg]
  simp only [smul_eq_mul, map_mul, map_inv₀, map_neg, map_sub, Complex.conj_conj]
  ring

/-- Multiplicity symmetry of `xi` under `ρ ↦ 1 - conj ρ`:
`analyticOrderNatAt xi (1 - starRingEnd ℂ ρ) = analyticOrderNatAt xi ρ`. -/
theorem analyticOrderNatAt_xi_one_sub_conj (ρ : ℂ) :
    analyticOrderNatAt xi (1 - starRingEnd ℂ ρ) = analyticOrderNatAt xi ρ := by
  have hxi_an : ∀ z : ℂ, AnalyticAt ℂ xi z := fun z =>
    (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hxi0 : xi 0 ≠ 0 := by simp
  have hne_top : ∀ z : ℂ, analyticOrderAt xi z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_ne_zero differentiable_xi hxi0
  set m : ℕ := analyticOrderNatAt xi ρ
  obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hxi_an ρ).analyticOrderAt_ne_top.mp (hne_top ρ)
  obtain ⟨U, hU_sub, hU_open, hρU⟩ := _root_.eventually_nhds_iff.mp
    (hh_an.eventually_analyticAt.and hh_eq)
  set ρ' : ℂ := 1 - starRingEnd ℂ ρ
  let ψ : ℂ → ℂ := fun z => 1 - starRingEnd ℂ z
  have hψ_cont : Continuous ψ := continuous_const.sub Complex.continuous_conj
  let V : Set ℂ := ψ ⁻¹' U
  have hV_open : IsOpen V := hU_open.preimage hψ_cont
  have hρ'V : ρ' ∈ V := by
    change 1 - starRingEnd ℂ (1 - starRingEnd ℂ ρ) ∈ U
    simpa [map_sub, map_one, Complex.conj_conj] using hρU
  let h' : ℂ → ℂ := fun z => (-1 : ℂ) ^ m * starRingEnd ℂ (h (ψ z))
  have hh'_diff : DifferentiableOn ℂ h' V := fun z hz => by
    have hd := hasDerivAt_conj_comp_one_sub_conj (hU_sub (ψ z) hz).1.differentiableAt
    exact (hd.const_mul ((-1 : ℂ) ^ m)).differentiableAt.differentiableWithinAt
  have hh'_an : AnalyticAt ℂ h' ρ' := hh'_diff.analyticAt (hV_open.mem_nhds hρ'V)
  have hh'_ne : h' ρ' ≠ 0 := by
    dsimp only [h', ψ, ρ']
    have harg : 1 - starRingEnd ℂ (1 - starRingEnd ℂ ρ) = ρ := by
      simp [map_sub, map_one]
    rw [harg]
    exact mul_ne_zero (pow_ne_zero m (by norm_num))
      ((map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hh_ne)
  rw [(hxi_an ρ').analyticOrderNatAt_eq_iff (hne_top ρ')]
  refine ⟨h', hh'_an, hh'_ne, ?_⟩
  filter_upwards [hV_open.mem_nhds hρ'V] with z hz
  have hxi_symm : xi z = starRingEnd ℂ (xi (ψ z)) := by
    dsimp only [ψ]
    rw [xi_one_sub, Stage6XiZeroDensity.xi_conj, Complex.conj_conj]
  have hfac : xi (ψ z) = (ψ z - ρ) ^ m * h (ψ z) := by
    simpa [smul_eq_mul] using (hU_sub (ψ z) hz).2
  rw [hxi_symm, hfac, map_mul, map_pow, map_sub, smul_eq_mul]
  have hbase : starRingEnd ℂ (ψ z) - starRingEnd ℂ ρ = -(z - ρ') := by
    dsimp only [ψ, ρ']
    rw [map_sub, map_one, Complex.conj_conj]
    ring
  rw [hbase, neg_eq_neg_one_mul, mul_pow]
  dsimp only [h']
  ring

/-- **Functional-Equation Permutation Symmetry of `xiZeroSeq`**:
there exists a permutation `τ : Equiv.Perm ℕ` such that
`∀ n, xiZeroSeq (τ n) = 1 - starRingEnd ℂ (xiZeroSeq n)`. -/
theorem xiZeroSeq_symm_perm :
    ∃ τ : Equiv.Perm ℕ, ∀ n : ℕ, xiZeroSeq (τ n) = 1 - starRingEnd ℂ (xiZeroSeq n) := by
  have hzero_symm : ∀ s : ℂ, xi s = 0 → xi (1 - starRingEnd ℂ s) = 0 := fun s hs => by
    rw [xi_one_sub, Stage6XiZeroDensity.xi_conj, hs, map_zero]
  let f : XiZeroWithMult → XiZeroWithMult := fun x =>
    ⟨⟨1 - starRingEnd ℂ x.1.1, hzero_symm x.1.1 x.1.2⟩,
      x.2.cast (analyticOrderNatAt_xi_one_sub_conj x.1.1).symm⟩
  have hf_inv : Function.Involutive f := by
    intro ⟨⟨s, hs⟩, j⟩
    dsimp only [f]
    have hs' : 1 - starRingEnd ℂ (1 - starRingEnd ℂ s) = s := by
      simp [map_sub, map_one]
    refine Sigma.ext (Subtype.ext hs') ?_
    exact (Fin.heq_ext_iff (congrArg (analyticOrderNatAt xi) hs')).mpr rfl
  let f_perm : Equiv.Perm XiZeroWithMult := hf_inv.toPerm f
  refine ⟨xiZeroEquiv.trans (f_perm.trans xiZeroEquiv.symm), fun n => ?_⟩
  simp only [xiZeroSeq, Equiv.trans_apply, Equiv.apply_symm_apply, f_perm,
    Function.Involutive.coe_toPerm, f]

/-! ## Section 4: Unconditional Concrete Hadamard Factorization of Mathlib's `xi(s)` -/

/-- Canonical Hadamard exponential constant `b = ξ'(0)` for Mathlib's actual `xi(s)`. -/
def xiHadamardB : ℂ := deriv xi 0

/-- At `z = 0`, `weierstrassProduct ρ 0 = 1`. -/
lemma weierstrassProduct_zero (ρ : ℕ → ℂ) : weierstrassProduct ρ 0 = 1 := by
  unfold weierstrassProduct
  simp [weierstrassE1_zero]

/-- **UNCONDITIONAL CONCRETE HADAMARD PRODUCT OF MATHLIB'S `xi(s)` (CANONICAL `b = deriv xi 0`)**:
for ALL `s : ℂ`, `xi s = Complex.exp (xiHadamardB * s) * weierstrassProduct xiZeroSeq s`. -/
theorem xi_eq_exp_hadamardB_mul_weierstrassProduct (s : ℂ) :
    xi s = Complex.exp (xiHadamardB * s) * weierstrassProduct xiZeroSeq s := by
  obtain ⟨A, hA, B, _, hxi⟩ := Stage6XiZeroDensity.hasOrderOneGrowth_xi
  have hxi0 : xi 0 ≠ 0 := by simp
  obtain ⟨hsum, a, b, hfac, hlogd⟩ :=
    hadamard_factorization_order_one hA.le hxi hxi0 isMultiplicityZeroSeq_xi
  have hexpa : Complex.exp a = 1 := by
    have h0 := hfac 0
    rw [xi_zero, mul_zero, add_zero, weierstrassProduct_zero, mul_one] at h0
    exact h0.symm
  have hb_eq : b = xiHadamardB := by
    have h0_ne : ∀ n : ℕ, (0 : ℂ) ≠ xiZeroSeq n := fun n h => xiZeroSeq_ne_zero n h.symm
    have hld0 := hlogd 0 h0_ne
    rw [xi_zero, div_one] at hld0
    have hsum0 : ∑' n : ℕ, (1 / ((0 : ℂ) - xiZeroSeq n) + 1 / xiZeroSeq n) = 0 := by
      simp [zero_sub, div_neg]
    rw [hsum0, add_zero] at hld0
    exact hld0.symm
  rw [hfac s, Complex.exp_add, hexpa, one_mul, hb_eq]

/-- **UNCONDITIONAL HADAMARD PRODUCT FOR MATHLIB'S ACTUAL `xi(s)` (`0` ASSUMPTIONS!)**:
`∃ b : ℂ, ∀ s : ℂ, xi s = Complex.exp (b * s) * weierstrassProduct xiZeroSeq s`. -/
theorem xi_hadamard_product :
    ∃ b : ℂ, ∀ s : ℂ, xi s = Complex.exp (b * s) * weierstrassProduct xiZeroSeq s :=
  ⟨xiHadamardB, xi_eq_exp_hadamardB_mul_weierstrassProduct⟩

/-- Uniqueness of the Hadamard exponential constant `b` in `xi_hadamard_product`. -/
theorem xi_hadamard_unique_b {b : ℂ}
    (hb : ∀ s : ℂ, xi s = Complex.exp (b * s) * weierstrassProduct xiZeroSeq s) :
    b = xiHadamardB := by
  have hfun : xi = fun s => (1 : ℂ) * Complex.exp (b * s) * weierstrassProduct xiZeroSeq s := by
    funext s; rw [one_mul]; exact hb s
  have h0_ne : ∀ n : ℕ, (0 : ℂ) ≠ xiZeroSeq n := fun n h => xiZeroSeq_ne_zero n h.symm
  have hld := Stage5JensenHadamard.hadamard_canonical_logDeriv_eq (C := 1) (B := b) one_ne_zero
    xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq h0_ne
  have hval0 : (1 : ℂ) * Complex.exp (b * 0) * weierstrassProduct xiZeroSeq 0 = 1 := by
    simp [weierstrassProduct_zero]
  rw [← hfun, hval0, div_one] at hld
  have hsum0 : ∑' n : ℕ, (1 / ((0 : ℂ) - xiZeroSeq n) + 1 / xiZeroSeq n) = 0 := by
    simp [zero_sub, div_neg]
  rw [hsum0, add_zero] at hld
  exact hld.symm

/-- **UNCONDITIONAL HADAMARD LOGARITHMIC DERIVATIVE OF MATHLIB'S ACTUAL `xi(s)` (`0` ASSUMPTIONS!)**:
for EVERY `s : ℂ` with `xi s ≠ 0`:
`deriv xi s / xi s = xiHadamardB + ∑' n, (1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n)`. -/
theorem xi_logDeriv_hadamard (s : ℂ) (hs : xi s ≠ 0) :
    deriv xi s / xi s =
      xiHadamardB + ∑' n : ℕ, (1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n) := by
  have hs_ne : ∀ n : ℕ, s ≠ xiZeroSeq n := fun n heq => hs (heq ▸ xiZeroSeq_zero n)
  have hfun : xi = fun w => (1 : ℂ) * Complex.exp (xiHadamardB * w) * weierstrassProduct xiZeroSeq w := by
    funext w; rw [one_mul]; exact xi_eq_exp_hadamardB_mul_weierstrassProduct w
  conv_lhs => rw [hfun]
  exact Stage5JensenHadamard.hadamard_canonical_logDeriv_eq (C := 1) one_ne_zero
    xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq hs_ne

/-- Functional-equation antisymmetry of `deriv xi / xi`: `deriv xi (1 - s) / xi (1 - s) = -(deriv xi s / xi s)`. -/
theorem logDeriv_xi_one_sub (s : ℂ) :
    deriv xi (1 - s) / xi (1 - s) = -(deriv xi s / xi s) := by
  have hcomp : HasDerivAt (fun w : ℂ => xi (1 - w)) (-deriv xi (1 - s)) s := by
    have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
    have h2 : HasDerivAt xi (deriv xi (1 - s)) (1 - s) := (differentiable_xi (1 - s)).hasDerivAt
    have h3 : HasDerivAt (fun w : ℂ => xi (1 - w)) (deriv xi (1 - s) * (-1)) s :=
      HasDerivAt.comp s h2 h1
    simpa using h3
  have hfun : (fun w : ℂ => xi (1 - w)) = xi := funext xi_one_sub
  rw [hfun] at hcomp
  have hd : deriv xi (1 - s) = -deriv xi s := by
    have := hcomp.deriv; linear_combination this
  rw [hd, xi_one_sub, neg_div]

/-- **UNCONDITIONAL DAVENPORT REAL-PART CANCELLATION IDENTITY FOR MATHLIB'S `xi(s)` (`0` ASSUMPTIONS!)**:
`xiHadamardB.re = -∑' n, (xiZeroSeq n)⁻¹.re`! -/
theorem xi_hadamard_davenport_B :
    xiHadamardB.re = -∑' n : ℕ, (xiZeroSeq n)⁻¹.re := by
  obtain ⟨τ, hτ⟩ := xiZeroSeq_symm_perm
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hxi2 : xi 2 ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
  have hconj2 : (1 : ℂ) - starRingEnd ℂ (2 : ℂ) = 1 - 2 := by simp only [map_ofNat]
  have hxi_m1 : xi (1 - starRingEnd ℂ (2 : ℂ)) ≠ 0 := by
    rw [hconj2, xi_one_sub]; exact hxi2
  have hanti : (xiHadamardB + ∑' n : ℕ, (1 / ((1 - starRingEnd ℂ (2 : ℂ)) - xiZeroSeq n) + 1 / xiZeroSeq n)).re =
      -(xiHadamardB + ∑' n : ℕ, (1 / ((2 : ℂ) - xiZeroSeq n) + 1 / xiZeroSeq n)).re := by
    rw [← xi_logDeriv_hadamard _ hxi_m1, ← xi_logDeriv_hadamard 2 hxi2, hconj2,
      logDeriv_xi_one_sub 2, Complex.neg_re]
  have hdav := Stage5JensenHadamard.davenport_re_B_eq_neg_tsum_re_inv
    xiZeroSeq_strip xiZeroSeq_summable_inv_sq τ hτ hs hanti
  simpa [one_div] using hdav.1

/-- **UNCONDITIONAL REAL-PART PARTIAL-FRACTION FORMULA FOR `xi'/xi(s)` ON `Re(s) > 1`**:
`(deriv xi s / xi s).re = ∑' n, (1 / (s - xiZeroSeq n)).re` for every `s` with `1 < s.re`. -/
theorem xi_re_logDeriv_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    (deriv xi s / xi s).re = ∑' n : ℕ, (1 / (s - xiZeroSeq n)).re := by
  have hxis : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs.le
  have hs_ne : ∀ n : ℕ, s ≠ xiZeroSeq n := fun n h => hxis (h ▸ xiZeroSeq_zero n)
  rw [xi_logDeriv_hadamard s hxis, Complex.add_re,
    Stage5JensenHadamard.re_tsum_hadamard_term_eq xiZeroSeq_strip xiZeroSeq_summable_inv_sq hs_ne,
    xi_hadamard_davenport_B]
  simp_rw [one_div]
  ring

end RHDirect.Stage7HadamardXiProduct
