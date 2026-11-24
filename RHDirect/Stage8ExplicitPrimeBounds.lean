import RHDirect.Stage6EffectivePNT
import RHDirect.Stage7PNTInAP
import RHDirect.Stage2DirichletAP
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Monotone

/-!
# RHDirect.Stage8ExplicitPrimeBounds

**UNCONDITIONAL EFFECTIVE PRIME DISTRIBUTION COROLLARIES (`0` ASSUMPTIONS, `0` `sorry`, `0` custom `axiom`s)**
built directly on `Stage6EffectivePNT`, `Stage7PNTInAP`, and `Stage2DirichletAP` in pure Mathlib `v4.33.1`.

## Main Contents
1. **Effective Two-Term Prime Counting & Unconditional `n`-th Prime Asymptotics (`p_n = Nat.nth Nat.Prime n`)**:
   - `effective_pnt_pi_two_term`: `∃ C > 0, ∀ x ≥ 4, |π(x) - (x / log x + x / (log x)^2)| ≤ C x / (log x)^3`
     via `Stage3RealAnalyticLandau.primeCounting_eq_abel_theta` + `Stage6EffectivePNT.effective_pnt_theta` + FTC.
   - `nth_prime_asymptotic`: `p_n / (n log n) → 1`.
   - `nth_prime_cipolla_two_term` (Cipolla 1902): `p_n / n - log n - log (log n) → -1`.
   - `nth_prime_gap_effective` & `nth_prime_gap_little_o`: `(p_{n+1} - p_n) / p_n ≤ exp(-c √(log n)) → 0`.
2. **Unconditional Super-Polynomial Short-Interval Prime Existence**:
   - `exists_prime_short_interval_effective`: `∃ c > 0, ∃ X₀, ∀ x ≥ X₀, ∃ p prime, x < p ≤ x + x exp(-c √(log x))`.
   - `exists_prime_in_Ioc_polylog`: for every `A > 0`, eventually `∃ p prime, x < p ≤ x + x / (log x)^A`.
   - `exists_prime_in_AP_short_interval` & `exists_prime_in_AP_Ioc_polylog`: unconditional short-interval
     primes in EVERY reduced residue class `a mod q`.
3. **Unconditional Asymptotics of Ramanujan Primes (`R_n ~ 2 n log n`, Sondow 2009)**:
   - `isRamanujanPrimeBound`, `ramanujanPrime`, `ramanujanPrime_set_nonempty`, `ramanujanPrime_prime`,
     and `ramanujan_prime_asymptotic`: `R_n / (2 n log n) → 1`.
4. **Unconditional `n`-th Prime in Arithmetic Progressions & Equidistribution Ratio**:
   - `nthPrimeAP`, `nth_prime_ap_asymptotic`: `p_n(q, a) / (φ(q) n log n) → 1`.
   - `prime_density_in_AP_ratio`: `π(n; q, a) / π(n) → 1 / φ(q)`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHDirect.Stage8ExplicitPrimeBounds

/-! ## Elementary Analytic Helpers -/

/-- Elementary inequality `u ^ k * exp (-(k : ℝ) * u) ≤ 1` for `k : ℕ` and `u ≥ 0`. -/
private lemma pow_mul_exp_neg_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-(k : ℝ) * u) ≤ 1 := by
  have h1 : u * Real.exp (-u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos u)).mpr (by linarith)
  have h2 : u ^ k * Real.exp (-(k : ℝ) * u) = (u * Real.exp (-u)) ^ k := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; ring
  rw [h2]
  exact pow_le_one₀ (mul_nonneg hu (Real.exp_pos (-u)).le) h1

/-- For all `x ≥ 2`, `(Real.log x) ^ 3 ≤ 216 * Real.sqrt x`. -/
private lemma log_cube_le_216_mul_sqrt {x : ℝ} (hx : 2 ≤ x) :
    (Real.log x) ^ 3 ≤ 216 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hLx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h1 := pow_mul_exp_neg_le_one 3 (show 0 ≤ Real.log x / 6 by linarith)
  push_cast at h1
  have hpow : (Real.log x / 6) ^ 3 = (Real.log x) ^ 3 / 216 := by ring
  have hexp : Real.exp (-(3 : ℝ) * (Real.log x / 6)) = (Real.sqrt x)⁻¹ := by
    rw [show -(3 : ℝ) * (Real.log x / 6) = -(Real.log x / 2) by ring, Real.exp_neg,
      ← Real.log_sqrt hx0.le, Real.exp_log (Real.sqrt_pos.mpr hx0)]
  rw [hpow, hexp] at h1
  have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h2 : (Real.log x) ^ 3 / (216 * Real.sqrt x) ≤ 1 := by
    rwa [← div_eq_mul_inv, div_div] at h1
  exact (div_le_one (by positivity)).mp h2

/-- For `c > 0` and `x ≥ 2`, `(Real.log x) ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) ≤ (4 / c) ^ 4`. -/
private lemma log_sq_mul_exp_neg_sqrt_le {c x : ℝ} (hc : 0 < c) (hx : 2 ≤ x) :
    (Real.log x) ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) ≤ (4 / c) ^ 4 := by
  have hLx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set u : ℝ := c * Real.sqrt (Real.log x) / 4
  have hu_nn : 0 ≤ u := by positivity
  have h1 := pow_mul_exp_neg_le_one 4 hu_nn
  push_cast at h1
  have h4u : -(4 : ℝ) * u = -c * Real.sqrt (Real.log x) := by dsimp only [u]; ring
  have hu4 : u ^ 4 = (c / 4) ^ 4 * (Real.log x) ^ 2 := by
    have hsq : (Real.sqrt (Real.log x)) ^ 4 = (Real.log x) ^ 2 := by
      calc (Real.sqrt (Real.log x)) ^ 4 = ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
        _ = (Real.log x) ^ 2 := by rw [Real.sq_sqrt hLx_nn]
    dsimp only [u]
    calc (c * Real.sqrt (Real.log x) / 4) ^ 4
        = (c / 4) ^ 4 * (Real.sqrt (Real.log x)) ^ 4 := by ring
      _ = (c / 4) ^ 4 * (Real.log x) ^ 2 := by rw [hsq]
  rw [h4u, hu4, mul_assoc] at h1
  have hpos : 0 < (c / 4) ^ 4 := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (4 / c) ^ 4 by positivity)
  have hcancel : (4 / c) ^ 4 * ((c / 4) ^ 4 * ((Real.log x) ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)))) =
      (Real.log x) ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) := by
    field_simp [hc.ne']
  linarith

/-- Helper: `Real.exp (-c * Real.sqrt (Real.log x)) → 0` as `x → ∞` for `c > 0`. -/
private lemma tendsto_exp_neg_mul_sqrt_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      Real.tendsto_log_atTop |>.congr fun x => (Real.sqrt_eq_rpow (Real.log x)).symm)
  have h2 : Tendsto (fun x : ℝ => -(c * Real.sqrt (Real.log x))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  exact (Real.tendsto_exp_atBot.comp h2).congr fun x => by
    dsimp only [Function.comp_apply]; congr 1; ring

/-- Helper: for any `c > 0` and `A > 0`, eventually `exp (-c * √(log x)) ≤ 1 / (log x) ^ A`. -/
private lemma eventually_exp_neg_sqrt_log_le_inv_rpow {c A : ℝ} (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 / (Real.log x) ^ A := by
  have hratio : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) atTop (𝓝 0) :=
    hratio.comp Real.tendsto_log_atTop
  have hev := hcomp.eventually (Iio_mem_nhds (div_pos hc hA))
  filter_upwards [hev, eventually_gt_atTop (Real.exp 1)] with x hx hx_e
  have hLx_gt1 : 1 < Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hx_e
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hsq_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLx_pos
  have hlt : A * Real.log (Real.log x) < c * Real.sqrt (Real.log x) := by
    have h1 : Real.log (Real.log x) < (c / A) * Real.sqrt (Real.log x) :=
      (div_lt_iff₀ hsq_pos).mp hx
    have h2 := mul_lt_mul_of_pos_left h1 hA
    have h3 : A * ((c / A) * Real.sqrt (Real.log x)) = c * Real.sqrt (Real.log x) := by
      field_simp [hA.ne']
    linarith
  have hrhs : 1 / (Real.log x) ^ A = Real.exp (-A * Real.log (Real.log x)) := by
    rw [one_div, ← Real.rpow_neg hLx_pos.le, Real.rpow_def_of_pos hLx_pos]
    congr 1; ring
  rw [hrhs]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Helper: `log x / x → 0` as `x → ∞`. -/
private lemma tendsto_log_div_self :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  exact h.congr' (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])

/-- Helper: `log (log x) / log x → 0` as `x → ∞`. -/
private lemma tendsto_log_log_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
  tendsto_log_div_self.comp Real.tendsto_log_atTop

/-! ## Section 1: Effective Two-Term Prime Counting & Unconditional `n`-th Prime Asymptotics -/

/-- Exact integration-by-parts identity for `∫_2^x (log t)^{-2} dt`:
`∫ t in 2..x, 1 / (log t)^2 = x / (log x)^2 - 2 / (log 2)^2 + 2 * ∫ t in 2..x, 1 / (log t)^3`. -/
private lemma integral_inv_log_sq_eq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 =
      x / (Real.log x) ^ 2 - 2 / (Real.log 2) ^ 2 +
        2 * ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3 := by
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ 2) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hcont3 : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ 3) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 3) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 3 (Real.log_pos (by linarith [ht.1])).ne'
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => u / (Real.log u) ^ 2)
        (1 / (Real.log t) ^ 2 - 2 * (1 / (Real.log t) ^ 3)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hd_log : HasDerivAt (fun u : ℝ => (Real.log u) ^ 2) (2 * (Real.log t) ^ 1 * t⁻¹) t := by
      simpa using (Real.hasDerivAt_log ht0.ne').fun_pow 2
    have hd_div := (hasDerivAt_id' t).fun_div hd_log (pow_ne_zero 2 hlt0.ne')
    refine hd_div.congr_deriv ?_
    field_simp [ht0.ne', hlt0.ne']
  have hcont3' : ContinuousOn (fun t : ℝ => 2 * (1 / (Real.log t) ^ 3)) (Set.uIcc 2 x) :=
    continuousOn_const.mul hcont3
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont2.sub hcont3').intervalIntegrable
  rw [intervalIntegral.integral_sub (f := fun t : ℝ => 1 / (Real.log t) ^ 2)
      (g := fun t : ℝ => 2 * (1 / (Real.log t) ^ 3))
      hcont2.intervalIntegrable hcont3'.intervalIntegrable,
    intervalIntegral.integral_const_mul] at hftc
  linarith

/-- Effective upper bound on `∫_2^x (log t)^{-3} dt` for `x ≥ 4`. -/
private lemma integral_inv_log_cube_le {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3 ≤
      (216 / (Real.log 2) ^ 3 + 8) * (x / (Real.log x) ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq_ge2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith : (2 : ℝ) ^ 2 ≤ x)
  have hsq_le : Real.sqrt x ≤ x := by
    have : x ≤ x ^ 2 := by nlinarith
    exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
  have hint : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 3) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 3) ?_
    · intro t ht; exact ne_of_gt (by linarith [ha, ht.1])
    · intro t ht; exact pow_ne_zero 3 (Real.log_pos (by linarith [ha, ht.1])).ne'
  have hsplit : ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3 =
      (∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 3) +
      (∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 3) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint 2 (Real.sqrt x) le_rfl hsq_ge2)
      (hint (Real.sqrt x) x hsq_ge2 hsq_le)).symm
  have hpart1 : ∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 3 ≤
      Real.sqrt x / (Real.log 2) ^ 3 := by
    have h1 : ∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 3 ≤
        ∫ _t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log 2) ^ 3 := by
      refine intervalIntegral.integral_mono_on hsq_ge2
        (hint 2 (Real.sqrt x) le_rfl hsq_ge2) intervalIntegrable_const fun t ht => ?_
      have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
      exact one_div_le_one_div_of_le (pow_pos hlog2_pos 3) (pow_le_pow_left₀ hlog2_pos.le hlt_ge 3)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have hlen : Real.sqrt x - 2 ≤ Real.sqrt x := by linarith
    calc ∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 3
        ≤ (Real.sqrt x - 2) * (1 / (Real.log 2) ^ 3) := h1
      _ ≤ Real.sqrt x * (1 / (Real.log 2) ^ 3) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = Real.sqrt x / (Real.log 2) ^ 3 := by ring
  have hpart2 : ∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 3 ≤ 8 * x / (Real.log x) ^ 3 := by
    have h1 : ∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 3 ≤
        ∫ _t in (Real.sqrt x)..x, 8 / (Real.log x) ^ 3 := by
      refine intervalIntegral.integral_mono_on hsq_le
        (hint (Real.sqrt x) x hsq_ge2 hsq_le) intervalIntegrable_const fun t ht => ?_
      have hlt_ge : Real.log x / 2 ≤ Real.log t := by
        have h := Real.log_le_log (by linarith) ht.1
        rwa [Real.log_sqrt hx0.le] at h
      have hcube : (Real.log x / 2) ^ 3 ≤ (Real.log t) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hlt_ge 3
      calc 1 / (Real.log t) ^ 3 ≤ 1 / (Real.log x / 2) ^ 3 :=
            one_div_le_one_div_of_le (by positivity) hcube
        _ = 8 / (Real.log x) ^ 3 := by field_simp [hLx_pos.ne']; ring
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have hlen : x - Real.sqrt x ≤ x := by linarith [Real.sqrt_nonneg x]
    calc ∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 3
        ≤ (x - Real.sqrt x) * (8 / (Real.log x) ^ 3) := h1
      _ ≤ x * (8 / (Real.log x) ^ 3) := mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = 8 * x / (Real.log x) ^ 3 := by ring
  have hsq_bd : Real.sqrt x ≤ 216 * (x / (Real.log x) ^ 3) := by
    have h1 := log_cube_le_216_mul_sqrt (by linarith : 2 ≤ x)
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
    rw [show Real.sqrt x * (216 * Real.sqrt x) = 216 * (Real.sqrt x * Real.sqrt x) by ring,
      Real.mul_self_sqrt hx0.le] at h2
    rw [show 216 * (x / (Real.log x) ^ 3) = (216 * x) / (Real.log x) ^ 3 by ring,
      le_div_iff₀ (pow_pos hLx_pos 3)]
    linarith
  rw [hsplit]
  have hpart1' : Real.sqrt x / (Real.log 2) ^ 3 ≤
      (216 / (Real.log 2) ^ 3) * (x / (Real.log x) ^ 3) := by
    calc Real.sqrt x / (Real.log 2) ^ 3
        ≤ (216 * (x / (Real.log x) ^ 3)) / (Real.log 2) ^ 3 :=
          div_le_div_of_nonneg_right hsq_bd (pow_nonneg hlog2_pos.le 3)
      _ = (216 / (Real.log 2) ^ 3) * (x / (Real.log x) ^ 3) := by ring
  linarith [show 8 * x / (Real.log x) ^ 3 = 8 * (x / (Real.log x) ^ 3) by ring]

/-- **UNCONDITIONAL EFFECTIVE TWO-TERM PRIME NUMBER THEOREM FOR `π(x)` (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 4, |π(x) - (x / log x + x / (log x)^2)| ≤ C * x / (log x)^3`. -/
theorem effective_pnt_pi_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 4 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - (x / Real.log x + x / (Real.log x) ^ 2)| ≤
        C * x / (Real.log x) ^ 3 := by
  obtain ⟨c_θ, hc_θ, C_θ, hC_θ, hth⟩ := Stage6EffectivePNT.effective_pnt_theta
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K_E : ℝ := C_θ * (4 / c_θ) ^ 4 with hKE_def
  have hKE_pos : 0 < K_E := by positivity
  set K_int : ℝ := 216 / (Real.log 2) ^ 3 + 8 with hKint_def
  have hKint_pos : 0 < K_int := by positivity
  set C_fin : ℝ := K_E + 432 / (Real.log 2) ^ 2 + (2 + K_E / Real.log 2) * K_int
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨C_fin, hC_fin_pos, fun x hx4 => ?_⟩
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  -- Pointwise error bound `|θ(t) - t| ≤ K_E * t / (log t)^2` for all `t ≥ 2`
  have hE_pt : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ K_E * t / (Real.log t) ^ 2 := by
    intro t ht2
    have hlt_pos : 0 < Real.log t := Real.log_pos (by linarith)
    have h1 := hth t ht2
    have h2 := log_sq_mul_exp_neg_sqrt_le hc_θ ht2
    rw [le_div_iff₀ (pow_pos hlt_pos 2)]
    calc |Chebyshev.theta t - t| * (Real.log t) ^ 2
        ≤ (C_θ * t * Real.exp (-c_θ * Real.sqrt (Real.log t))) * (Real.log t) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = C_θ * t * ((Real.log t) ^ 2 * Real.exp (-c_θ * Real.sqrt (Real.log t))) := by ring
      _ ≤ C_θ * t * (4 / c_θ) ^ 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K_E * t := by dsimp only [K_E]; ring
  -- Integrability of `θ(t) / (t (log t)^2)` and `(θ(t) - t) / (t (log t)^2)` on `[2, x]`
  have hcont_inv2 : IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 2) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx2]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hcont_inv3 : IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 3) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx2]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 3) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 3 (Real.log_pos (by linarith [ht.1])).ne'
  have hint_err : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) volume 2 x := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx2).mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := K_E / (Real.log 2) ^ 4) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable Chebyshev.theta := by
        have h : Chebyshev.theta =
            (fun k : ℕ => ∑ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, Real.log (p : ℝ)) ∘ Nat.floor := rfl
        rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact ((hm.sub measurable_id).div
        (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : 0 < t := by linarith
      have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
      calc |Chebyshev.theta t - t| / (t * (Real.log t) ^ 2)
          ≤ (K_E * t / (Real.log t) ^ 2) / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right (hE_pt t ht2) (by positivity)
        _ = K_E / (Real.log t) ^ 4 := by field_simp [ht0.ne', hlt_pos.ne']
        _ ≤ K_E / (Real.log 2) ^ 4 :=
            div_le_div_of_nonneg_left hKE_pos.le (pow_pos hlog2_pos 4)
              (pow_le_pow_left₀ hlog2_pos.le hlt_ge 4)
  -- Split `∫_2^x θ(t) / (t (log t)^2) = ∫_2^x 1 / (log t)^2 + ∫_2^x (θ(t) - t) / (t (log t)^2)`
  have hsplit_int :
      ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) =
        (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) +
        (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) := by
    rw [← intervalIntegral.integral_add hcont_inv2 hint_err]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx2] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    field_simp [ht0.ne', hlt0.ne']
    ring
  -- Assemble the exact identity for `π(x) - (x / log x + x / (log x)^2)`
  have hdecomp :
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - (x / Real.log x + x / (Real.log x) ^ 2) =
        (Chebyshev.theta x - x) / Real.log x - 2 / (Real.log 2) ^ 2 +
          2 * (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3) +
          (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) := by
    rw [Stage3RealAnalyticLandau.primeCounting_eq_abel_theta hx2, hsplit_int,
      integral_inv_log_sq_eq hx2]
    ring
  rw [hdecomp]
  -- Bound each of the four pieces by a multiple of `x / (log x)^3`
  have hI3_bd : ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3 ≤ K_int * (x / (Real.log x) ^ 3) :=
    integral_inv_log_cube_le hx4
  have hI3_nn : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3 :=
    intervalIntegral.integral_nonneg hx2 fun t ht =>
      div_nonneg zero_le_one (pow_nonneg (Real.log_nonneg (by linarith [ht.1])) 3)
  have hb1 : |(Chebyshev.theta x - x) / Real.log x| ≤ K_E * (x / (Real.log x) ^ 3) := by
    rw [abs_div, abs_of_pos hLx_pos]
    calc |Chebyshev.theta x - x| / Real.log x
        ≤ (K_E * x / (Real.log x) ^ 2) / Real.log x :=
          div_le_div_of_nonneg_right (hE_pt x hx2) hLx_pos.le
      _ = K_E * (x / (Real.log x) ^ 3) := by field_simp [hLx_pos.ne']
  have hb2 : 2 / (Real.log 2) ^ 2 ≤ (432 / (Real.log 2) ^ 2) * (x / (Real.log x) ^ 3) := by
    have h1 : (1 : ℝ) ≤ 216 * (x / (Real.log x) ^ 3) := by
      have hsq1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
      have hcube := log_cube_le_216_mul_sqrt hx2
      have hmul : (Real.log x) ^ 3 ≤ 216 * x := by
        have h := mul_le_mul_of_nonneg_left hcube (Real.sqrt_nonneg x)
        have : Real.sqrt x * (216 * Real.sqrt x) = 216 * x := by
          calc Real.sqrt x * (216 * Real.sqrt x) = 216 * (Real.sqrt x * Real.sqrt x) := by ring
            _ = 216 * x := by rw [Real.mul_self_sqrt hx0.le]
        nlinarith [pow_pos hLx_pos 3]
      rw [show 216 * (x / (Real.log x) ^ 3) = (216 * x) / (Real.log x) ^ 3 by ring,
        one_le_div (pow_pos hLx_pos 3)]
      exact hmul
    calc 2 / (Real.log 2) ^ 2 = (2 / (Real.log 2) ^ 2) * 1 := (mul_one _).symm
      _ ≤ (2 / (Real.log 2) ^ 2) * (216 * (x / (Real.log x) ^ 3)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (432 / (Real.log 2) ^ 2) * (x / (Real.log x) ^ 3) := by ring
  have hb4 : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤
      (K_E / Real.log 2) * K_int * (x / (Real.log x) ^ 3) := by
    have hnorm : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤
        ∫ t in (2 : ℝ)..x, |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm
          (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) hx2
    have hmono : ∫ t in (2 : ℝ)..x, |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤
        ∫ t in (2 : ℝ)..x, (K_E / Real.log 2) * (1 / (Real.log t) ^ 3) := by
      refine intervalIntegral.integral_mono_on hx2 hint_err.abs
        (hcont_inv3.const_mul _) fun t ht => ?_
      have ht2 : 2 ≤ t := ht.1
      have ht0 : 0 < t := by linarith
      have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
      rw [abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
      calc |Chebyshev.theta t - t| / (t * (Real.log t) ^ 2)
          ≤ (K_E * t / (Real.log t) ^ 2) / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right (hE_pt t ht2) (by positivity)
        _ = (K_E / Real.log t) * (1 / (Real.log t) ^ 3) := by
            field_simp [ht0.ne', hlt_pos.ne']
        _ ≤ (K_E / Real.log 2) * (1 / (Real.log t) ^ 3) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact div_le_div_of_nonneg_left hKE_pos.le hlog2_pos hlt_ge
    rw [intervalIntegral.integral_const_mul] at hmono
    calc |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)|
        ≤ (K_E / Real.log 2) * ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3 := hnorm.trans hmono
      _ ≤ (K_E / Real.log 2) * (K_int * (x / (Real.log x) ^ 3)) :=
          mul_le_mul_of_nonneg_left hI3_bd (by positivity)
      _ = (K_E / Real.log 2) * K_int * (x / (Real.log x) ^ 3) := by ring
  have htri :
      |(Chebyshev.theta x - x) / Real.log x - 2 / (Real.log 2) ^ 2 +
          2 * (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3) +
          (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))| ≤
        |(Chebyshev.theta x - x) / Real.log x| + 2 / (Real.log 2) ^ 2 +
          2 * (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3) +
          |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| := by
    have h1 := abs_add_le
      ((Chebyshev.theta x - x) / Real.log x - 2 / (Real.log 2) ^ 2 +
        2 * (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3))
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
    have h2 := abs_add_le
      ((Chebyshev.theta x - x) / Real.log x - 2 / (Real.log 2) ^ 2)
      (2 * (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3))
    have h3 := abs_sub ((Chebyshev.theta x - x) / Real.log x) (2 / (Real.log 2) ^ 2)
    rw [abs_of_nonneg (show 0 ≤ 2 * (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 3) by linarith)] at h2
    rw [abs_of_pos (show (0 : ℝ) < 2 / (Real.log 2) ^ 2 by positivity)] at h3
    linarith
  have hrhs : C_fin * x / (Real.log x) ^ 3 =
      (K_E + 432 / (Real.log 2) ^ 2 + 2 * K_int + (K_E / Real.log 2) * K_int) *
        (x / (Real.log x) ^ 3) := by
    dsimp only [C_fin]; ring
  linarith

/-- Exact prime-counting identity at the `n`-th prime (`0`-indexed: `Nat.nth Nat.Prime 0 = 2`):
`Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1`. -/
theorem primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  have hpr : (Nat.nth Nat.Prime n).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ, if_pos hpr, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime n]

/-- The sequence `n ↦ Nat.nth Nat.Prime n` tends to `∞`. -/
private lemma tendsto_nth_prime_atTop :
    Tendsto (fun n : ℕ => Nat.nth Nat.Prime n) atTop atTop :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-- Auxiliary limit: `n * log (p_n) / p_n → 1` as `n → ∞`. -/
private lemma tendsto_n_mul_log_nth_prime_div_nth_prime :
    Tendsto
      (fun n : ℕ => ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ)) / (Nat.nth Nat.Prime n : ℝ))
      atTop (𝓝 1) := by
  have hpnt := Stage6EffectivePNT.pnt_primeCounting_asymp.comp tendsto_nth_prime_atTop
  have h1 : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) / ((Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n : ℝ)))
      atTop (𝓝 1) := by
    refine hpnt.congr fun n => ?_
    simp only [Function.comp_apply, primeCounting_nth_prime]
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr fun n => by
          simp [one_div]
      simpa using tendsto_const_nhds.add h0
    have hinv' := hinv.inv₀ one_ne_zero
    rw [inv_one] at hinv'
    refine hinv'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    push_cast
    field_simp [hn0.ne']
  have hmul := hratio.mul h1
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp_ge2 : 2 ≤ Nat.nth Nat.Prime n := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le
  have hp0 : (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
  have hlogp0 : (0 : ℝ) < Real.log (Nat.nth Nat.Prime n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.nth Nat.Prime n))
  field_simp [hn1, hp0.ne', hlogp0.ne']

/-- Auxiliary limit: `log (p_n) / log n → 1` as `n → ∞`. -/
private lemma tendsto_log_nth_prime_div_log :
    Tendsto
      (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hlog_ratio :
      Tendsto
        (fun n : ℕ =>
          Real.log (((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ)) / (Nat.nth Nat.Prime n : ℝ)))
        atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    exact (by simpa [Real.log_one] using hc.tendsto.comp tendsto_n_mul_log_nth_prime_div_nth_prime :
      Tendsto (Real.log ∘ _) atTop (𝓝 0)).congr fun _ => rfl
  have hlogp_top : Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop)
  have hdiv_logp :
      Tendsto
        (fun n : ℕ =>
          Real.log (((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ)) / (Nat.nth Nat.Prime n : ℝ)) /
            Real.log (Nat.nth Nat.Prime n : ℝ))
        atTop (𝓝 0) := by
    have h := hlog_ratio.mul (tendsto_inv_atTop_zero.comp hlogp_top)
    rw [mul_zero] at h
    exact h.congr fun n => by simp [div_eq_mul_inv]
  have hloglogp :
      Tendsto
        (fun n : ℕ =>
          Real.log (Real.log (Nat.nth Nat.Prime n : ℝ)) / Real.log (Nat.nth Nat.Prime n : ℝ))
        atTop (𝓝 0) :=
    tendsto_log_div_self.comp hlogp_top
  have hinv_lim :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hloglogp |>.add hdiv_logp
    rw [sub_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hp_ge2 : 2 ≤ Nat.nth Nat.Prime n := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le
    have hp0 : (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
    have hlogp0 : (0 : ℝ) < Real.log (Nat.nth Nat.Prime n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.nth Nat.Prime n))
    rw [Real.log_div (mul_pos hn0 hlogp0).ne' hp0.ne', Real.log_mul hn0.ne' hlogp0.ne']
    field_simp [hlogp0.ne']
    ring
  have hrec := hinv_lim.inv₀ one_ne_zero
  rw [inv_one] at hrec
  exact hrec.congr fun n => by rw [inv_div]

/-- **UNCONDITIONAL PRIME NUMBER THEOREM FOR THE `n`-TH PRIME (`p_n ~ n log n`, 0 ASSUMPTIONS!)**:
`Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1)`. -/
theorem nth_prime_asymptotic :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 1) := by
  have h1 : Tendsto
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ)))
      atTop (𝓝 1) := by
    have h := tendsto_n_mul_log_nth_prime_div_nth_prime.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun n => by rw [inv_div]
  have hmul := h1.mul tendsto_log_nth_prime_div_log
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn0 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hp_ge2 : 2 ≤ Nat.nth Nat.Prime n := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le
  have hlogp0 : (0 : ℝ) < Real.log (Nat.nth Nat.Prime n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.nth Nat.Prime n))
  field_simp [hn0.ne', hlogn0.ne', hlogp0.ne']

/-- **UNCONDITIONAL CIPOLLA (1902) TWO-TERM `n`-TH PRIME EXPANSION (`0` ASSUMPTIONS!)**:
`p_n = n (log n + log log n - 1 + o(1))`, i.e.,
`Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / n - Real.log n - Real.log (Real.log n)) atTop (𝓝 (-1))`. -/
theorem nth_prime_cipolla_two_term :
    Tendsto
      (fun n : ℕ =>
        (Nat.nth Nat.Prime n : ℝ) / (n : ℝ) - Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)))
      atTop (𝓝 (-1)) := by
  obtain ⟨C, hC, hpi2⟩ := effective_pnt_pi_two_term
  have hlogp_top : Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop)
  have hp_div_nlogp : Tendsto
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ)))
      atTop (𝓝 1) := by
    have h := tendsto_n_mul_log_nth_prime_div_nth_prime.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun n => by rw [inv_div]
  -- Step 1: `p_n / n - log p_n → -1` from `effective_pnt_pi_two_term`
  have hstep1 :
      Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / (n : ℝ) - Real.log (Nat.nth Nat.Prime n : ℝ))
        atTop (𝓝 (-1)) := by
    set R : ℕ → ℝ := fun n =>
      (((n + 1 : ℕ) : ℝ) - ((Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n : ℝ) +
        (Nat.nth Nat.Prime n : ℝ) / (Real.log (Nat.nth Nat.Prime n : ℝ)) ^ 2)) *
        (Real.log (Nat.nth Nat.Prime n : ℝ) / (n : ℝ))
    have hR_zero : Tendsto R atTop (𝓝 0) := by
      have hdom : Tendsto
          (fun n : ℕ =>
            C * ((Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ))) *
              (Real.log (Nat.nth Nat.Prime n : ℝ))⁻¹)
          atTop (𝓝 0) := by
        have h := (hp_div_nlogp.const_mul C).mul (tendsto_inv_atTop_zero.comp hlogp_top)
        simpa using h
      refine squeeze_zero_norm' (a := fun n : ℕ =>
          C * ((Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ))) *
            (Real.log (Nat.nth Nat.Prime n : ℝ))⁻¹) ?_ hdom
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hp_ge4 : 4 ≤ Nat.nth Nat.Prime n := by
        have hlt : Nat.nth Nat.Prime 1 < Nat.nth Nat.Prime n :=
          Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
        have h0 : 2 ≤ Nat.nth Nat.Prime 0 :=
          (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime 0).two_le
        have h01 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
          Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
        omega
      have hp_ge4R : (4 : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast hp_ge4
      have hbd := hpi2 (Nat.nth Nat.Prime n : ℝ) hp_ge4R
      rw [Nat.floor_natCast, primeCounting_nth_prime] at hbd
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hlogp0 : (0 : ℝ) < Real.log (Nat.nth Nat.Prime n : ℝ) := Real.log_pos (by linarith)
      dsimp only [R]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hlogp0 hn0)]
      calc |((n + 1 : ℕ) : ℝ) - ((Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n : ℝ) +
              (Nat.nth Nat.Prime n : ℝ) / (Real.log (Nat.nth Nat.Prime n : ℝ)) ^ 2)| *
            (Real.log (Nat.nth Nat.Prime n : ℝ) / (n : ℝ))
          ≤ (C * (Nat.nth Nat.Prime n : ℝ) / (Real.log (Nat.nth Nat.Prime n : ℝ)) ^ 3) *
              (Real.log (Nat.nth Nat.Prime n : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_right hbd (div_nonneg hlogp0.le hn0.le)
        _ = C * ((Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ))) *
              (Real.log (Nat.nth Nat.Prime n : ℝ))⁻¹ := by
            field_simp [hn0.ne', hlogp0.ne']
    have hlogp_div_n : Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      have hlogn_div_n : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_log_div_self.comp tendsto_natCast_atTop_atTop
      have hmul := tendsto_log_nth_prime_div_log.mul hlogn_div_n
      rw [one_mul] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hlogn0 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      field_simp [hlogn0.ne']
    have hcomb : Tendsto
        (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) / (n : ℝ) -
          (Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ)) - R n)
        atTop (𝓝 (-1)) := by
      have h := (hlogp_div_n.sub hp_div_nlogp).sub hR_zero
      simpa using h
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hp_ge2 : 2 ≤ Nat.nth Nat.Prime n := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le
    have hlogp0 : (0 : ℝ) < Real.log (Nat.nth Nat.Prime n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.nth Nat.Prime n))
    dsimp only [R]
    push_cast
    field_simp [hn0.ne', hlogp0.ne']
    ring
  -- Step 2: `log p_n - log n - log (log n) = log (p_n / (n log n)) → log 1 = 0`
  have hstep2 :
      Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) - Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)))
        atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    have hlim : Tendsto
        (fun n : ℕ => Real.log ((Nat.nth Nat.Prime n : ℝ) / ((n : ℝ) * Real.log (n : ℝ))))
        atTop (𝓝 0) :=
      (by simpa [Real.log_one] using hc.tendsto.comp nth_prime_asymptotic :
        Tendsto (Real.log ∘ _) atTop (𝓝 0)).congr fun _ => rfl
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn0 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hp_ge2 : 2 ≤ Nat.nth Nat.Prime n := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le
    have hp0 : (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
    rw [Real.log_div hp0.ne' (mul_pos hn0 hlogn0).ne', Real.log_mul hn0.ne' hlogn0.ne']
    ring
  -- Step 3: Add Steps 1 and 2!
  have hsum := hstep1.add hstep2
  rw [add_zero] at hsum
  exact hsum.congr fun n => by ring

/-! ## Section 2: Unconditional Super-Polynomial Short-Interval Prime Existence & Prime Gaps -/

/-- If `Chebyshev.theta x < Chebyshev.theta y` for `0 ≤ x ≤ y`, there is a prime in `(x, y]`. -/
private lemma exists_prime_in_Ioc_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hlt : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra hno
  push Not at hno
  have hsub : (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    have hpy : (p : ℝ) ≤ y := le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by linarith))
    have hpx : (p : ℝ) ≤ x := by
      by_contra hgt; push Not at hgt
      exact (not_le_of_gt (hno p hp.2 hgt)) hpy
    exact (Nat.le_floor_iff hx).mpr hpx
  have hsub' : (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy))
  have heq : Chebyshev.theta x = Chebyshev.theta y := by
    unfold Chebyshev.theta
    congr 1
    exact Finset.Subset.antisymm hsub' hsub
  linarith

/-- **UNCONDITIONAL SUPER-POLYNOMIAL SHORT-INTERVAL PRIME EXISTENCE (`0` ASSUMPTIONS!)**:
there exist `c > 0` and `X₀ : ℝ` such that for ALL `x ≥ X₀`, there exists a prime `p` in
`(x, x + x * Real.exp (-c * Real.sqrt (Real.log x))]`. -/
theorem exists_prime_short_interval_effective :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x + x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c_θ, hc_θ, C_θ, hC_θ, hth⟩ := Stage6EffectivePNT.effective_pnt_theta
  set c : ℝ := c_θ / 2 with hc_def
  have hc_pos : 0 < c := by positivity
  have hev := (tendsto_exp_neg_mul_sqrt_log hc_pos).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * C_θ) by positivity))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨c, hc_pos, max 2 X₁, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  set δ : ℝ := Real.exp (-c * Real.sqrt (Real.log x)) with hδ_def
  have hδ_pos : 0 < δ := Real.exp_pos _
  have hδ_le1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by
    nlinarith [Real.sqrt_nonneg (Real.log x)])
  have hδ_small : δ < 1 / (4 * C_θ) := hX₁ x hx1
  set y : ℝ := x + x * δ with hy_def
  have hxy : x ≤ y := by nlinarith
  have hy2 : 2 ≤ y := by linarith
  have hy_le2x : y ≤ 2 * x := by nlinarith
  have hE_x : Real.exp (-c_θ * Real.sqrt (Real.log x)) = δ ^ 2 := by
    rw [hδ_def, ← Real.exp_nat_mul]; congr 1; push_cast; dsimp only [c]; ring
  have hE_y : Real.exp (-c_θ * Real.sqrt (Real.log y)) ≤ δ ^ 2 := by
    rw [← hE_x]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    nlinarith [Real.sqrt_le_sqrt hlog]
  have hth_x := (abs_le.mp (hth x hx2)).2
  have hth_y := (abs_le.mp (hth y hy2)).1
  have hth_diff : Chebyshev.theta x < Chebyshev.theta y := by
    have h1 : C_θ * y * Real.exp (-c_θ * Real.sqrt (Real.log y)) ≤ 2 * C_θ * x * δ ^ 2 := by
      calc C_θ * y * Real.exp (-c_θ * Real.sqrt (Real.log y))
          ≤ C_θ * (2 * x) * δ ^ 2 := by gcongr
        _ = 2 * C_θ * x * δ ^ 2 := by ring
    have h2 : C_θ * x * Real.exp (-c_θ * Real.sqrt (Real.log x)) = C_θ * x * δ ^ 2 := by
      rw [hE_x]
    have h3 : 3 * C_θ * δ < 1 := by
      have := mul_lt_mul_of_pos_left hδ_small (show (0 : ℝ) < 4 * C_θ by positivity)
      rw [mul_one_div_cancel (by positivity : (4 * C_θ) ≠ 0)] at this
      nlinarith
    have h4 : 3 * C_θ * x * δ ^ 2 < x * δ := by
      have h := mul_lt_mul_of_pos_right h3 (mul_pos hx0 hδ_pos)
      linarith
    linarith
  exact exists_prime_in_Ioc_of_theta_lt hx0.le hxy hth_diff

/-- **UNCONDITIONAL POLYLOGARITHMIC SHORT-INTERVAL PRIME EXISTENCE (`0` ASSUMPTIONS!)**:
for EVERY `A > 0`, for all sufficiently large `x`, there is a prime in `(x, x + x / (Real.log x) ^ A]`,
beating Bertrand's postulate by every power of `log x`! -/
theorem exists_prime_in_Ioc_polylog (A : ℝ) (hA : 0 < A) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x / (Real.log x) ^ A := by
  obtain ⟨c, hc, X₁, hshort⟩ := exists_prime_short_interval_effective
  have hev := eventually_exp_neg_sqrt_log_le_inv_rpow hc hA
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₂, hX₂⟩ := hev
  refine ⟨max (max X₁ X₂) 2, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx2 : X₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx_ge2 : 2 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨p, hp, hxp, hpy⟩ := hshort x hx1
  refine ⟨p, hp, hxp, hpy.trans ?_⟩
  have hle := hX₂ x hx2
  have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ x by linarith)
  rw [mul_one_div] at hmul
  linarith

/-- **UNCONDITIONAL EFFECTIVE PRIME GAP DECAY (`0` ASSUMPTIONS!)**:
`(p_{n+1} - p_n) / p_n ≤ Real.exp (-c * Real.sqrt (Real.log n))` for all sufficiently large `n`. -/
theorem nth_prime_gap_effective :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ)) /
        (Nat.nth Nat.Prime n : ℝ) ≤ Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by
  obtain ⟨c, hc, X₀, hshort⟩ := exists_prime_short_interval_effective
  refine ⟨c, hc, max 2 ⌈max X₀ 0⌉₊, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hpn_ge_n : n ≤ Nat.nth Nat.Prime n :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le n
  have hpn_ge_X₀ : X₀ ≤ (Nat.nth Nat.Prime n : ℝ) := by
    have h1 : ⌈max X₀ 0⌉₊ ≤ n := (le_max_right _ _).trans hn
    have h2 : max X₀ 0 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    exact (le_max_left _ _).trans (h2.trans (by exact_mod_cast hpn_ge_n))
  obtain ⟨p, hp, hlt_p, hp_le⟩ := hshort (Nat.nth Nat.Prime n : ℝ) hpn_ge_X₀
  have hlt_nat : Nat.nth Nat.Prime n < p := by exact_mod_cast hlt_p
  -- `p_{n+1} ≤ p` since `p` is prime and `p_n < p`
  have hp_next_le : Nat.nth Nat.Prime (n + 1) ≤ p := by
    have hcnt_le : n + 1 ≤ Nat.count Nat.Prime p := by
      have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1 := by
        rw [Nat.count_succ, if_pos (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n),
          Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime n]
      rw [← h1]
      exact Nat.count_monotone Nat.Prime (by omega)
    calc Nat.nth Nat.Prime (n + 1)
        ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime p) :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hcnt_le
      _ = p := Nat.nth_count hp
  have hp_next_leR : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_next_le
  have hpn_pos : (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
  rw [div_le_iff₀ hpn_pos]
  have hlog_mono : Real.log (n : ℝ) ≤ Real.log (Nat.nth Nat.Prime n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hpn_ge_n)
  have hexp_mono : Real.exp (-c * Real.sqrt (Real.log (Nat.nth Nat.Prime n : ℝ))) ≤
      Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlog_mono])
  have hmul : (Nat.nth Nat.Prime n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (Nat.nth Nat.Prime n : ℝ))) ≤
      Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Nat.nth Nat.Prime n : ℝ) := by
    nlinarith
  linarith

/-- **UNCONDITIONAL RELATIVE PRIME GAP DECAY (`(p_{n+1} - p_n) / p_n → 0`, 0 ASSUMPTIONS!)**:
`Tendsto (fun n : ℕ => ((Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ)) / (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 0)`. -/
theorem nth_prime_gap_little_o :
    Tendsto
      (fun n : ℕ =>
        ((Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ)) /
          (Nat.nth Nat.Prime n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, N₀, hgap⟩ := nth_prime_gap_effective
  refine squeeze_zero_norm' (a := fun n : ℕ => Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) ?_ ?_
  · filter_upwards [eventually_ge_atTop N₀] with n hn
    have hlt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
    have hpn_pos : (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).pos
    have hnn : 0 ≤ ((Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ)) /
        (Nat.nth Nat.Prime n : ℝ) :=
      div_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)) hpn_pos.le
    rw [Real.norm_of_nonneg hnn]
    exact hgap n hn
  · exact (tendsto_exp_neg_mul_sqrt_log hc).comp tendsto_natCast_atTop_atTop

/-- If `chebyshevThetaAP q a x < chebyshevThetaAP q a y` for `0 ≤ x ≤ y`, there is a prime
`p ≡ a [MOD q]` in `(x, y]`. -/
private lemma exists_prime_in_AP_Ioc_of_thetaAP_lt (q a : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hlt : Stage2DirichletAP.chebyshevThetaAP q a x < Stage2DirichletAP.chebyshevThetaAP q a y) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra hno
  push Not at hno
  have hsub :
      (Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
        (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    have hpy : (p : ℝ) ≤ y :=
      le_trans (by exact_mod_cast (by omega : p ≤ ⌊y⌋₊)) (Nat.floor_le (by linarith))
    have hpx : (p : ℝ) ≤ x := by
      by_contra hgt; push Not at hgt
      exact (not_le_of_gt (hno p hp.2.1 hp.2.2 hgt)) hpy
    have hfl : p ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).mpr hpx
    omega
  have hsub' :
      (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
        (Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) :=
    Finset.filter_subset_filter _ (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hxy) 1))
  have heq : Stage2DirichletAP.chebyshevThetaAP q a x = Stage2DirichletAP.chebyshevThetaAP q a y := by
    unfold Stage2DirichletAP.chebyshevThetaAP
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.Subset.antisymm hsub' hsub]
  linarith

section APShortInterval

open Complex
open scoped ArithmeticFunction.vonMangoldt

/-- Elementary comparison `log (A * (|t| + 2)) ≤ (2 * log A + 1) * log (|t| + 2)` for `A ≥ 2`. -/
private lemma log_const_mul_le_mul_log {A : ℝ} (hA : 2 ≤ A) (t : ℝ) :
    Real.log (A * (|t| + 2)) ≤ (2 * Real.log A + 1) * Real.log (|t| + 2) := by
  have hA0 : 0 < A := by linarith
  have ht2_ge2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have ht2_pos : 0 < |t| + 2 := by linarith
  rw [Real.log_mul hA0.ne' ht2_pos.ne']
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_t_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    hlog2_gt.le.trans (Real.log_le_log (by norm_num) ht2_ge2)
  have hlogA_nn : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  nlinarith

/-- Strip upper bound for the principal character `L(1_q, z)` via the Euler product factorization
`L(1_q, z) = ζ(z) * ∏_{p ∣ q} (1 - p^{-z})` on `1/2 ≤ Re(z) ≤ 2`, `1/2 ≤ |Im(z)|`. -/
private lemma norm_LFunction_principal_strip_le {q : ℕ} [NeZero q] {z : ℂ}
    (hre_lo : 1 / 2 ≤ z.re) (hre_hi : z.re ≤ 2) (him_lo : 1 / 2 ≤ |z.im|) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (2 * |z.im| + 7) := by
  have hz_re0 : 0 < z.re := by linarith
  have hz1 : z ≠ 1 := by
    intro h; subst h; simp at him_lo; linarith
  have hchg := DirichletCharacter.LFunction_changeLevel q.one_dvd
    (1 : DirichletCharacter ℂ 1) (s := z) (Or.inr hz1)
  rw [map_one, DirichletCharacter.LFunction_modOne_eq] at hchg
  rw [hchg, norm_mul, norm_prod]
  have hprod_le :
      ∏ p ∈ q.primeFactors,
          ‖(1 : ℂ) - (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-z)‖ ≤
        (2 : ℝ) ^ q.primeFactors.card := by
    calc ∏ p ∈ q.primeFactors,
            ‖(1 : ℂ) - (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-z)‖
        ≤ ∏ _p ∈ q.primeFactors, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
          have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hp_pos : 0 < p := hpr.pos
          have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_lt.le
          have hcpow_le : ‖(p : ℂ) ^ (-z)‖ ≤ 1 := by
            rw [Complex.norm_natCast_cpow_of_pos hp_pos, Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos hp_ge1 (by linarith)
          have hchar_le : ‖(1 : DirichletCharacter ℂ 1) (p : ZMod 1)‖ ≤ 1 :=
            (1 : DirichletCharacter ℂ 1).norm_le_one _
          calc ‖(1 : ℂ) - (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-z)‖
              ≤ ‖(1 : ℂ)‖ + ‖(1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-z)‖ :=
                norm_sub_le _ _
            _ = 1 + ‖(1 : DirichletCharacter ℂ 1) (p : ZMod 1)‖ * ‖(p : ℂ) ^ (-z)‖ := by
                rw [norm_one, norm_mul]
            _ ≤ 1 + 1 * 1 := by
                have := mul_le_mul hchar_le hcpow_le (norm_nonneg _) zero_le_one
                linarith
            _ = 2 := by norm_num
      _ = (2 : ℝ) ^ q.primeFactors.card := by rw [Finset.prod_const]
  have hzeta_le : ‖riemannZeta z‖ ≤ 2 * |z.im| + 7 := by
    have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos hz_re0 hz1
    have hsub_ge : 1 / 2 ≤ ‖z - 1‖ := by
      have := Complex.abs_im_le_norm (z - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    have hinv_le : 1 / ‖z - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hnorm_z : ‖z‖ ≤ |z.im| + 2 := by
      have htri := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz_re0] at htri
      linarith
    have hdiv_le : ‖z‖ / z.re ≤ 2 * |z.im| + 4 := by
      rw [div_le_iff₀ hz_re0]
      nlinarith [abs_nonneg z.im]
    linarith
  have h2 := mul_le_mul hzeta_le hprod_le (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (by linarith [abs_nonneg z.im])
  linarith

/-- Numerical closing inequality `87 + 40 * log 48000 < 1000`. -/
private lemma numerical_dlvp_closing_real :
    (87 : ℝ) + 40 * Real.log (48000 : ℝ) < 1000 := by
  have hlt : (48000 : ℝ) < (2 : ℝ) ^ (16 : ℕ) := by norm_num
  have hlog : Real.log (48000 : ℝ) < 16 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num) hlt
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  linarith

/-- Classical de la Vallée Poussin zero-free region for a REAL non-principal character (`χ ≠ 1`,
`χ ^ 2 = 1`) at height `4 ≤ |s.im|`:
`1 - 1 / (14000 * Real.log (2 ^ ω(q) * q * (|s.im| + 2))) ≤ s.re → LFunction χ s ≠ 0`. -/
private lemma LFunction_real_char_dlvp_high {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) {s : ℂ}
    (him : 4 ≤ |s.im|)
    (hre : 1 - 1 / (14000 * Real.log ((2 : ℝ) ^ q.primeFactors.card * (q : ℝ) * (|s.im| + 2))) ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hz
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ1
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlt1 : s.re < 1 := by
    by_contra hge; push Not at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) hge hz
  set γ : ℝ := s.im
  set β : ℝ := s.re
  set Aq : ℝ := (2 : ℝ) ^ q.primeFactors.card with hAq_def
  have hAq_ge1 : (1 : ℝ) ≤ Aq := one_le_pow₀ (by norm_num)
  set Pq : ℝ := Aq * (q : ℝ) with hPq_def
  have hPq_ge2 : (2 : ℝ) ≤ Pq := by dsimp only [Pq]; nlinarith
  set Q : ℝ := Pq * (|γ| + 2) with hQ_def
  have hQ_ge12 : (12 : ℝ) ≤ Q := by dsimp only [Q]; nlinarith
  set L : ℝ := Real.log Q with hL_def
  have hL_gt1 : 1 < L := by
    have h12 : Real.exp 1 < Q := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h12)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  set δ : ℝ := 1 / (2000 * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp only [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hβ_gt : 7 / 8 < β := by
    have h1 : 1 / (14000 * L) < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ_le : σ ≤ 5 / 4 := by linarith
  -- (1) Landau bound for `L(χ, ·)` on `closedBall s₁ (1/2)`
  set s₁ : ℂ := (σ : ℂ) + I * (γ : ℂ)
  have hs₁_re : s₁.re = σ := by simp [s₁]
  have hs₁_im : s₁.im = γ := by simp [s₁]
  have hs₁_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s₁ (1 / 2)) :=
    (DifferentiableOn.analyticOnNhd (fun z _ =>
      (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ1)).differentiableWithinAt)
      isOpen_univ).mono (Set.subset_univ _)
  have hs₁_nz : DirichletCharacter.LFunction χ s₁ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by rw [hs₁_re]; linarith)
  set M₁ : ℝ := 12 * Q / δ
  have hM₁_ge1 : 1 ≤ M₁ := by dsimp only [M₁]; rw [le_div_iff₀ hδ_pos]; linarith
  have hs₁_bd : ∀ z ∈ Metric.closedBall s₁ (1 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M₁ * ‖DirichletCharacter.LFunction χ s₁‖ := by
    intro z hz_mem
    rw [Metric.mem_closedBall, dist_eq_norm] at hz_mem
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₁)).trans hz_mem)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₁)).trans hz_mem)
    rw [Complex.sub_re, hs₁_re] at hre_diff
    rw [Complex.sub_im, hs₁_im] at him_diff
    have hz_im_hi : |z.im| ≤ |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |γ| + |z.im - γ| := by
        simpa [add_sub_cancel] using abs_add_le γ (z.im - γ)
      linarith [abs_le.mpr him_diff]
    have hz_strip : ‖DirichletCharacter.LFunction χ z‖ ≤ 6 * Q := by
      have h := Stage5ZetaZeroFree.norm_LFunction_strip_le hχ1
        (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
      have hq_le : (q : ℝ) ≤ Pq := by dsimp only [Pq]; nlinarith
      dsimp only [Q]; nlinarith [abs_nonneg γ]
    have hinv_s₁ : ‖1 / DirichletCharacter.LFunction χ s₁‖ ≤ 2 / δ := by
      have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hσ1 γ).2.1
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
    have h1 : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ s₁‖ ≤ M₁ := by
      rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₁ =
          DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₁) by ring, norm_mul]
      calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₁‖
          ≤ (6 * Q) * (2 / δ) := mul_le_mul hz_strip hinv_s₁ (norm_nonneg _) (by positivity)
        _ = M₁ := by dsimp only [M₁]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₁_nz)).mp h1
  have hs₁_zeros : ∀ ρ ∈ Metric.closedBall s₁ (1 / 4),
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ s₁.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by rw [hs₁_re] at hgt; linarith) hρ0
  have hs_mem : s ∈ Metric.closedBall s₁ (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : s - s₁ = (((β - σ : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hlandau₁ := Stage5ZetaZeroFree.landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM₁_ge1 hs₁_an hs₁_nz hs₁_bd hs₁_zeros hs_mem hz
  have hs₁_sub_s : s₁ - s = (((σ - β : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
  have hre_inv : (1 / (s₁ - s)).re = 1 / (σ - β) := by
    rw [hs₁_sub_s, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre_err : (s₁ - s).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    rw [hs₁_sub_s, Complex.ofReal_re, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    have hle : σ - β ≤ 1 / 4 := by dsimp only [σ]; linarith
    linarith
  have hbound₁ : (Stage3ZeroFreeRegion.negLogDerivL χ s₁).re ≤
      8 * Real.log M₁ + 1 - 1 / (σ - β) := by
    unfold Stage3ZeroFreeRegion.negLogDerivL
    rw [hre_inv] at hlandau₁
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at hlandau₁
    linarith
  -- (2) Landau bound for `L(χ^2, ·) = L(1_q, ·)` on `closedBall s₂ (1/2)` (avoids `s = 1` since `|2γ| ≥ 8`!)
  set s₂ : ℂ := (σ : ℂ) + I * ((2 * γ : ℝ) : ℂ)
  have hs₂_re : s₂.re = σ := by simp [s₂]
  have hs₂_im : s₂.im = 2 * γ := by simp [s₂]
  have hball₂_ne1 : ∀ z ∈ Metric.closedBall s₂ (1 / 2), z ≠ 1 := by
    intro z hz_mem h1
    subst h1
    rw [Metric.mem_closedBall, dist_eq_norm] at hz_mem
    have him_diff := (Complex.abs_im_le_norm ((1 : ℂ) - s₂)).trans hz_mem
    rw [Complex.sub_im, Complex.one_im, hs₂_im, zero_sub, abs_neg, abs_mul, abs_of_pos two_pos] at him_diff
    linarith
  have hs₂_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      (Metric.closedBall s₂ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (s := {(1 : ℂ)}ᶜ) (fun z hz1 =>
      (DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ q) z
        (.inl hz1)).differentiableWithinAt) isClosed_singleton.isOpen_compl).mono ?_
    intro z hz_mem; exact hball₂_ne1 z hz_mem
  have hs₂_nz : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q)
      (.inr (hball₂_ne1 s₂ (Metric.mem_closedBall_self (by norm_num)))) (by rw [hs₂_re]; linarith)
  set M₂ : ℝ := 24 * Q / δ
  have hM₂_ge1 : 1 ≤ M₂ := by dsimp only [M₂]; rw [le_div_iff₀ hδ_pos]; linarith
  have hs₂_bd : ∀ z ∈ Metric.closedBall s₂ (1 / 2),
      ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤
        M₂ * ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂‖ := by
    intro z hz_mem
    rw [Metric.mem_closedBall, dist_eq_norm] at hz_mem
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₂)).trans hz_mem)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₂)).trans hz_mem)
    rw [Complex.sub_re, hs₂_re] at hre_diff
    rw [Complex.sub_im, hs₂_im] at him_diff
    have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul, abs_of_pos two_pos]
    have hz_im_lo : 1 / 2 ≤ |z.im| := by
      have htri : |2 * γ| ≤ |z.im| + |z.im - 2 * γ| := by
        have := abs_sub_le (2 * γ) z.im 0
        linarith [abs_sub_comm (2 * γ) z.im, show |2 * γ - 0| = |2 * γ| by simp,
          show |z.im - 0| = |z.im| by simp]
      linarith [abs_le.mpr him_diff]
    have hz_im_hi : |z.im| ≤ 2 * |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |2 * γ| + |z.im - 2 * γ| := by
        simpa [add_sub_cancel] using abs_add_le (2 * γ) (z.im - 2 * γ)
      linarith [abs_le.mpr him_diff]
    have hz_strip : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤ 12 * Q := by
      have h := norm_LFunction_principal_strip_le (q := q)
        (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2) hz_im_lo
      have h1 : 2 * |z.im| + 7 ≤ 4 * (|γ| + 2) := by linarith
      have hAq_le : Aq ≤ Pq := by dsimp only [Pq]; nlinarith
      calc ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖
          ≤ Aq * (2 * |z.im| + 7) := h
        _ ≤ Aq * (4 * (|γ| + 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ Pq * (4 * (|γ| + 2)) := mul_le_mul_of_nonneg_right hAq_le (by positivity)
        _ = 4 * Q := by dsimp only [Q]; ring
        _ ≤ 12 * Q := by linarith
    have hinv_s₂ : ‖1 / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂‖ ≤ 2 / δ := by
      have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re
        (1 : DirichletCharacter ℂ q) hσ1 (2 * γ)).2.1
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
    have h1 : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ /
        ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂‖ ≤ M₂ := by
      rw [← norm_div, show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂ =
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z *
          (1 / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂) by ring, norm_mul]
      calc ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ *
              ‖1 / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂‖
          ≤ (12 * Q) * (2 / δ) := mul_le_mul hz_strip hinv_s₂ (norm_nonneg _) (by positivity)
        _ = M₂ := by dsimp only [M₂]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₂_nz)).mp h1
  have hs₂_zeros : ∀ ρ ∈ Metric.closedBall s₂ (1 / 4),
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ = 0 → ρ.re ≤ s₂.re := by
    intro ρ hρ_mem hρ0
    by_contra hgt; push Not at hgt
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, Complex.one_re, hs₂_re] at hgt; linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q)
      (.inr hρ1) (by rw [hs₂_re] at hgt; linarith) hρ0
  have hbound₂ : (Stage3ZeroFreeRegion.negLogDerivL (χ ^ 2) s₂).re ≤ 8 * Real.log M₂ := by
    rw [hχ2]
    have h := Stage5ZetaZeroFree.landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
      (by norm_num) (by norm_num) hM₂_ge1 hs₂_an hs₂_nz hs₂_bd hs₂_zeros
    unfold Stage3ZeroFreeRegion.negLogDerivL
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at h
    exact h
  -- (3) Combine via `three_four_one_zeta_negLogDerivL_re_nonneg`!
  have hbound₀ : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := Stage5ZetaZeroFree.negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  have h341 := Stage3ZeroFreeRegion.three_four_one_zeta_negLogDerivL_re_nonneg χ hσ1 γ
  have h2it : (σ : ℂ) + 2 * I * (γ : ℂ) = s₂ := by dsimp only [s₂]; push_cast; ring
  rw [h2it] at h341
  have hlogM₁ : Real.log M₁ ≤ Real.log M₂ :=
    Real.log_le_log (by linarith) (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
  have hlogM₂ : Real.log M₂ ≤ Real.log (48000 : ℝ) + 2 * L := by
    have hL_le : L ≤ Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hM₂_le : M₂ ≤ 48000 * Q ^ 2 := by
      have hM₂_eq : M₂ = 48000 * Q * L := by dsimp only [M₂, δ]; field_simp [hL_pos.ne']; ring
      rw [hM₂_eq]; nlinarith
    calc Real.log M₂ ≤ Real.log (48000 * Q ^ 2) := Real.log_le_log (by linarith) hM₂_le
      _ = Real.log (48000 : ℝ) + Real.log (Q ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log (48000 : ℝ) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have herr_strict : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ < 1 / (2 * δ) := by
    have h1000 : 1000 * L = 1 / (2 * δ) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hcomb : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ ≤ (87 + 40 * Real.log (48000 : ℝ)) * L := by
      nlinarith [hlogM₁, hlogM₂, hL_gt1, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 48000)]
    have h2 : (87 + 40 * Real.log (48000 : ℝ)) * L < 1000 * L :=
      mul_lt_mul_of_pos_right numerical_dlvp_closing_real hL_pos
    linarith
  have hineq_strict : 4 / (σ - β) < 7 / (2 * δ) := by
    have h1 : 4 / (σ - β) < 3 / δ + 1 / (2 * δ) := by
      have h4 : 4 * (1 / (σ - β)) = 4 / (σ - β) := by ring
      have h3 : 3 * (1 / δ) = 3 / δ := by ring
      linarith
    have h2 : 3 / δ + 1 / (2 * δ) = 7 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by linarith
  have hmul_strict : 8 * δ < 7 * (σ - β) := by
    have h := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq_strict
    linarith
  have hβ_strict : β < 1 - δ / 7 := by dsimp only [σ] at hmul_strict; linarith
  have hδ7 : δ / 7 = 1 / (14000 * L) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
  linarith

/-- **UNCONDITIONAL FIXED-MODULUS DE LA VALLÉE POUSSIN ZERO-FREE REGION FOR EVERY NON-PRINCIPAL `χ ≠ 1`**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `χ ≠ 1` (both complex AND real!), there exists `c_χ > 0`
such that `LFunction χ s ≠ 0` whenever `1 - c_χ / Real.log (|s.im| + 2) ≤ s.re`. -/
theorem LFunction_deLaValleePoussin_zeroFree_fixed_char {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∃ c_χ : ℝ, 0 < c_χ ∧
      ∀ s : ℂ, 1 - c_χ / Real.log (|s.im| + 2) ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hχ2 : χ ^ 2 ≠ 1
  · -- Complex character `χ ^ 2 ≠ 1`: direct from `Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree`!
    set A_q : ℝ := 2 * Real.log (q : ℝ) + 1
    have hAq_pos : 0 < A_q := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ q); linarith
    set c_χ : ℝ := 1 / (14000 * A_q)
    refine ⟨c_χ, by positivity, fun s hs => ?_⟩
    have hlog_cmp := log_const_mul_le_mul_log hqR s.im
    have hlogt_pos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hlogq_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
      Real.log_pos (by nlinarith [abs_nonneg s.im])
    have hdiv : c_χ / Real.log (|s.im| + 2) ≤ 1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by
      dsimp only [c_χ]
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      nlinarith
    exact Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree χ hχ2 (by linarith)
  · -- Real character `χ ^ 2 = 1`: combine `LFunction_real_char_dlvp_high` (`|s.im| ≥ 4`) with compactness on `[-4, 4]`
    push Not at hχ2
    have hcont_seg : ContinuousOn (fun t : ℝ => ‖DirichletCharacter.LFunction χ (1 + I * (t : ℂ))‖)
        (Set.Icc (-4 : ℝ) 4) := by
      have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous
      have hmap : Continuous (fun t : ℝ => (1 : ℂ) + I * (t : ℂ)) := by fun_prop
      exact (hL_cont.comp hmap).norm.continuousOn
    have hne_Icc : (Set.Icc (-4 : ℝ) 4).Nonempty := ⟨0, by norm_num, by norm_num⟩
    obtain ⟨t₀, _, ht₀_min⟩ := isCompact_Icc.exists_isMinOn hne_Icc hcont_seg
    set m : ℝ := ‖DirichletCharacter.LFunction χ (1 + I * (t₀ : ℂ))‖
    have hm_pos : 0 < m := norm_pos_iff.mpr
      (Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) (by simp))
    set L6q : ℝ := Real.log ((q : ℝ) * 6)
    have hL6q_pos : 0 < L6q := Real.log_pos (by linarith)
    set δ_χ : ℝ := min L6q⁻¹ (m / (2 * (288 * L6q ^ 2)))
    have hδ_pos : 0 < δ_χ := lt_min (inv_pos.mpr hL6q_pos) (by positivity)
    set Pq : ℝ := (2 : ℝ) ^ q.primeFactors.card * (q : ℝ)
    have hPq_ge2 : (2 : ℝ) ≤ Pq := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card := one_le_pow₀ (by norm_num)
      dsimp only [Pq]; nlinarith
    set A_q : ℝ := 2 * Real.log Pq + 1
    have hAq_pos : 0 < A_q := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Pq); linarith
    set c_high : ℝ := 1 / (14000 * A_q)
    set c_χ : ℝ := min c_high (δ_χ * Real.log 2)
    have hc_pos : 0 < c_χ := lt_min (by positivity) (by positivity)
    refine ⟨c_χ, hc_pos, fun s hs => ?_⟩
    by_cases hre1 : 1 ≤ s.re
    · exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) hre1
    · push Not at hre1
      have hlog_t_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
      have hlog_t_pos : 0 < Real.log (|s.im| + 2) := hlog2_pos.trans_le hlog_t_ge
      by_cases him4 : 4 ≤ |s.im|
      · have hlog_cmp := log_const_mul_le_mul_log hPq_ge2 s.im
        have hlogP_pos : 0 < Real.log (Pq * (|s.im| + 2)) :=
          Real.log_pos (by nlinarith [abs_nonneg s.im])
        have hdiv : c_χ / Real.log (|s.im| + 2) ≤ 1 / (14000 * Real.log (Pq * (|s.im| + 2))) := by
          calc c_χ / Real.log (|s.im| + 2)
              ≤ c_high / Real.log (|s.im| + 2) :=
                div_le_div_of_nonneg_right (min_le_left _ _) hlog_t_pos.le
            _ = 1 / (14000 * (A_q * Real.log (|s.im| + 2))) := by
                dsimp only [c_high]; rw [div_div]; ring
            _ ≤ 1 / (14000 * Real.log (Pq * (|s.im| + 2))) := by
                refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
                nlinarith
        exact LFunction_real_char_dlvp_high hχ hχ2 him4 (by linarith)
      · push Not at him4
        have hdiv_le_δ : c_χ / Real.log (|s.im| + 2) ≤ δ_χ := by
          calc c_χ / Real.log (|s.im| + 2)
              ≤ (δ_χ * Real.log 2) / Real.log (|s.im| + 2) :=
                div_le_div_of_nonneg_right (min_le_right _ _) hlog_t_pos.le
            _ ≤ (δ_χ * Real.log 2) / Real.log 2 :=
                div_le_div_of_nonneg_left (by positivity) hlog2_pos hlog_t_ge
            _ = δ_χ := mul_div_cancel_right₀ _ hlog2_pos.ne'
        have hs_re_ge : 1 - δ_χ ≤ s.re := by linarith
        set Lq : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
        have hLq_pos : 0 < Lq := Real.log_pos (by nlinarith [abs_nonneg s.im])
        have hLq_le : Lq ≤ L6q := Real.log_le_log (by nlinarith [abs_nonneg s.im]) (by nlinarith)
        have hinv_le : L6q⁻¹ ≤ Lq⁻¹ := inv_anti₀ hLq_pos hLq_le
        have hδ_le_inv : δ_χ ≤ L6q⁻¹ := min_le_left _ _
        have hδ_le_m : δ_χ ≤ m / (2 * (288 * L6q ^ 2)) := min_le_right _ _
        have hmvt := Stage5DirichletLZeroFree.norm_LFunction_sub_le_of_strip hχ
          (σ₁ := s.re) (σ₂ := 1) (t := s.im) (by linarith) hre1.le (by norm_num)
        have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
          have := Complex.re_add_im s; simpa only [mul_comm I] using this
        have h1_eq : ((1 : ℝ) : ℂ) + I * (s.im : ℂ) = 1 + I * (s.im : ℂ) := by simp
        rw [hs_eq, h1_eq] at hmvt
        have hmin_le : m ≤ ‖DirichletCharacter.LFunction χ (1 + I * (s.im : ℂ))‖ :=
          ht₀_min (abs_le.mp him4.le)
        have hdiff_lt : (1 - s.re) * (288 * Lq ^ 2) < m := by
          have h1s : 1 - s.re ≤ δ_χ := by linarith
          have hsq : Lq ^ 2 ≤ L6q ^ 2 := pow_le_pow_left₀ hLq_pos.le hLq_le 2
          have h1 : (1 - s.re) * (288 * Lq ^ 2) ≤ δ_χ * (288 * L6q ^ 2) :=
            mul_le_mul h1s (by linarith) (by positivity) hδ_pos.le
          have h2 : δ_χ * (288 * L6q ^ 2) ≤ m / 2 := by
            have := mul_le_mul_of_nonneg_right hδ_le_m (show 0 ≤ 288 * L6q ^ 2 by positivity)
            have hcancel : m / (2 * (288 * L6q ^ 2)) * (288 * L6q ^ 2) = m / 2 := by
              field_simp [hL6q_pos.ne']
            linarith
          linarith
        intro hzero
        rw [hzero, sub_zero] at hmvt
        linarith

/-- **Unconditional Classical `(log(|s.im| + 2))^2` Log-Derivative Bound for EVERY Non-Principal `χ ≠ 1`**
inside the de la Vallée Poussin zero-free region (valid for ALL `s.im : ℝ`). -/
private lemma negLogDerivL_zeroFree_bound_dlvp {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ s : ℂ, 1 - c' / Real.log (|s.im| + 2) ≤ s.re → s.re ≤ 2 →
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          C' * (Real.log (|s.im| + 2)) ^ 2 := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c_zf, hc_zf_pos, hzf⟩ := LFunction_deLaValleePoussin_zeroFree_fixed_char hχ
  set c : ℝ := min c_zf (Real.log 2 / 4)
  have hc_pos : 0 < c := lt_min hc_zf_pos (by positivity)
  have hc_le_zf : c ≤ c_zf := min_le_left _ _
  have hc_le_qtr : c ≤ Real.log 2 / 4 := min_le_right _ _
  have hc_le_one : c ≤ 1 := by linarith [Real.log_two_lt_d9]
  set c' : ℝ := c / 32
  have hc'_pos : 0 < c' := by positivity
  set C_right : ℝ := (1 / c') / Real.log 2 + 1 / (Real.log 2) ^ 2
  have hC_right_pos : 0 < C_right := by positivity
  set K_arg : ℝ := 128 * (q : ℝ) / c
  have hK_arg_gt1 : 1 < K_arg := by dsimp only [K_arg]; rw [one_lt_div hc_pos]; nlinarith
  have hlogK_pos : 0 < Real.log K_arg := Real.log_pos hK_arg_gt1
  set A_M : ℝ := Real.log K_arg / Real.log 2 + 2
  have hAM_pos : 0 < A_M := by positivity
  set C_left : ℝ := (32 / c) * A_M
  have hC_left_pos : 0 < C_left := by positivity
  set C' : ℝ := max C_right C_left
  refine ⟨c', hc'_pos, C', lt_of_lt_of_le hC_left_pos (le_max_right _ _), fun s hre_lo hre_hi => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (|t| + 2)
  have ht2_ge2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have ht2_pos : 0 < |t| + 2 := by linarith
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) ht2_ge2
  have hL_pos : 0 < L := hlog2_pos.trans_le hL_ge
  by_cases hright : 1 + c' / L ≤ s.re
  · have hs_re_gt1 : 1 < s.re := by linarith [div_pos hc'_pos hL_pos]
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s; simpa only [t, mul_comm I] using this
    have hbd := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hs_re_gt1 t).2.2
    unfold Stage3ZeroFreeRegion.negLogDerivL at hbd
    rw [hs_eq] at hbd
    have hinv_le : 1 / (s.re - 1) ≤ L / c' := by
      rw [div_le_div_iff₀ (by linarith) hc'_pos, one_mul]
      have h1 : c' / L ≤ s.re - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hL_pos.le
      rw [div_mul_cancel₀ _ hL_pos.ne'] at h2; linarith
    have h1_le_L : 1 ≤ L / Real.log 2 := (one_le_div hlog2_pos).mpr hL_ge
    have h1_le_L2 : 1 ≤ L ^ 2 / (Real.log 2) ^ 2 :=
      (one_le_div (sq_pos_of_pos hlog2_pos)).mpr (pow_le_pow_left₀ hlog2_pos.le hL_ge 2)
    have hterm1 : L / c' ≤ ((1 / c') / Real.log 2) * L ^ 2 := by
      have h := mul_le_mul_of_nonneg_left h1_le_L (show 0 ≤ L / c' by positivity)
      have hrhs : (L / c') * (L / Real.log 2) = ((1 / c') / Real.log 2) * L ^ 2 := by
        field_simp [hc'_pos.ne', hlog2_pos.ne']
      linarith
    have hterm2 : (1 : ℝ) ≤ (1 / (Real.log 2) ^ 2) * L ^ 2 := by
      have : (1 / (Real.log 2) ^ 2) * L ^ 2 = L ^ 2 / (Real.log 2) ^ 2 := by ring
      linarith
    calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ 1 / (s.re - 1) + 1 := hbd
      _ ≤ L / c' + 1 := by linarith
      _ ≤ ((1 / c') / Real.log 2) * L ^ 2 + (1 / (Real.log 2) ^ 2) * L ^ 2 := by linarith
      _ = C_right * L ^ 2 := by dsimp only [C_right]; ring
      _ ≤ C' * L ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg L)
  · push Not at hright
    set η : ℝ := c / (16 * L)
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      have h1 : c / L ≤ 1 / 4 := by
        calc c / L ≤ (Real.log 2 / 4) / L := div_le_div_of_nonneg_right hc_le_qtr hL_pos.le
          _ ≤ (Real.log 2 / 4) / Real.log 2 := div_le_div_of_nonneg_left (by positivity) hlog2_pos hL_ge
          _ = 1 / 4 := by field_simp [hlog2_pos.ne']
      have hη_eq : η = (c / L) / 16 := by dsimp only [η]; ring
      linarith
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ)
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz_mem
      rw [Metric.mem_ball, dist_eq_norm] at hz_mem
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz_mem.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz_mem.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im_le : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1; simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv_ge : c / (2 * L) ≤ c_zf / Real.log (|z.im| + 2) := by
        calc c / (2 * L) ≤ c / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_pos.le hlogz_pos hlog_le
          _ ≤ c_zf / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_le_zf hlogz_pos.le
      have h4η : 4 * η ≤ c / (2 * L) := by dsimp only [η]; rw [show 4 * (c / (16 * L)) = c / (4 * L) by ring]; exact div_le_div_of_nonneg_left hc_pos.le (by positivity) (by linarith)
      exact hzf z (by dsimp only [R_open] at hre_diff; linarith)
    have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    set M : ℝ := A_M * L
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz_mem
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz_mem
      have hznz : DirichletCharacter.LFunction χ z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : DirichletCharacter.LFunction χ s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz_mem
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz_mem)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz_mem)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le_8 : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_im_hi : |z.im| ≤ |t| + 1 / 8 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 4 * (q : ℝ) * (|t| + 2) := by
        have h := Stage5ZetaZeroFree.norm_LFunction_strip_le hχ
          (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
        nlinarith [abs_nonneg t]
      have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 2 / η := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + η) t).2.1
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h
        exact h.trans (div_le_div_of_nonneg_right (by linarith) hη_pos.le)
      have hratio_le : ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
          K_arg * (|t| + 2) ^ 2 := by
        rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
            DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring, norm_mul]
        have hL_le_t2 : L ≤ |t| + 2 := (Real.log_le_sub_one_of_pos ht2_pos).trans (by linarith)
        have hmul_eq : (4 * (q : ℝ) * (|t| + 2)) * (2 / η) = K_arg * (|t| + 2) * L := by
          dsimp only [K_arg, η]; field_simp [hc_pos.ne', hL_pos.ne']; ring
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (4 * (q : ℝ) * (|t| + 2)) * (2 / η) := mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = K_arg * (|t| + 2) * L := hmul_eq
          _ ≤ K_arg * (|t| + 2) * (|t| + 2) := mul_le_mul_of_nonneg_left hL_le_t2 (by positivity)
          _ = K_arg * (|t| + 2) ^ 2 := by ring
      have hexp_norm : Real.exp (Log z).re =
          ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        rw [← Complex.norm_exp, hLog_exp z hz_ball]
      have h1 : (Log z).re ≤ Real.log (K_arg * (|t| + 2) ^ 2) := by
        rw [← Real.log_exp (Log z).re, hexp_norm]
        exact Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)) hratio_le
      have h2 : Real.log (K_arg * (|t| + 2) ^ 2) = Real.log K_arg + 2 * L := by
        rw [Real.log_mul (by linarith) (sq_pos_of_pos ht2_pos).ne', Real.log_pow]; push_cast; rfl
      have h3 : Real.log K_arg ≤ (Real.log K_arg / Real.log 2) * L := by
        have h := mul_le_mul_of_nonneg_left ((one_le_div hlog2_pos).mpr hL_ge) hlogK_pos.le
        have hrhs : Real.log K_arg * (L / Real.log 2) = (Real.log K_arg / Real.log 2) * L := by ring
        linarith
      dsimp only [M, A_M]; linarith
    have hs_norm : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h1 : c' / L ≤ η := by
        dsimp only [c', η]
        rw [show c / 32 / L = c / (32 * L) by ring]
        exact div_le_div_of_nonneg_left hc_pos.le (by positivity) (by linarith)
      dsimp only [r]; constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_norm
    rw [hLog0, Complex.zero_re, sub_zero] at hbc
    have hs_ball : s ∈ Metric.ball s₀ R_open := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hs_norm (by dsimp only [r, R_open]; linarith)
    have hderiv_eq : deriv Log s = deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s :=
      (hLog_d s hs_ball).deriv
    have hnorm_eq : ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖deriv Log s‖ := by
      rw [neg_div, norm_neg, hderiv_eq]
    rw [hnorm_eq]
    have hcoef : 2 * R / (R - r) ^ 2 * M = C_left * L ^ 2 := by
      dsimp only [R, r, M, C_left, η]; field_simp [hc_pos.ne', hL_pos.ne']; ring
    calc ‖deriv Log s‖ ≤ 2 * R / (R - r) ^ 2 * M := hbc
      _ = C_left * L ^ 2 := hcoef
      _ ≤ C' * L ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg L)

/-- **UNCONDITIONAL `√(log x)` DECAY FOR NON-PRINCIPAL `ψ₁(x, χ)` (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ ≠ 1`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, ‖psi1Char χ x‖ ≤ C * x ^ 2 * Real.exp (-c * Real.sqrt (Real.log x))`. -/
private lemma effective_psi1Char_bound_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          C * x ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c_zf, hc_zf, hzf⟩ := LFunction_deLaValleePoussin_zeroFree_fixed_char hχ
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := negLogDerivL_zeroFree_bound_dlvp hχ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c_star : ℝ := min (min c_zf c₁) (1 / 4)
  have hc_star_pos : 0 < c_star := by positivity
  have hc_star_le_zf : c_star ≤ c_zf := (min_le_left _ _).trans (min_le_left _ _)
  have hc_star_le_c₁ : c_star ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_star_le_qtr : c_star ≤ 1 / 4 := min_le_right _ _
  -- Optimal height `α = √c_star / 2` so `(2 * α) ^ 2 = c_star`
  set α : ℝ := Real.sqrt c_star / 2
  have hα_pos : 0 < α := by positivity
  have h2α_sq : (2 * α) ^ 2 = c_star := by
    have h1 : 2 * α = Real.sqrt c_star := by dsimp only [α]; ring
    rw [h1, Real.sq_sqrt hc_star_pos.le]
  set c_fin : ℝ := α / 2
  have hc_fin_pos : 0 < c_fin := by positivity
  set x₀ : ℝ := max 2 (Real.exp ((1 / α) ^ 2))
  have hx₀_ge2 : 2 ≤ x₀ := le_max_left _ _
  set K_large : ℝ :=
    (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) * (4 / α) ^ 2
  have hK_large_pos : 0 < K_large := by positivity
  have hlarge : ∀ x : ℝ, x₀ ≤ x →
      ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        K_large * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
    intro x hx
    have hx2 : 2 ≤ x := hx₀_ge2.trans hx
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_ge_log2 : Real.log 2 ≤ Lx := Real.log_le_log (by norm_num) hx2
    have hLx_pos : 0 < Lx := hlog2_pos.trans_le hLx_ge_log2
    set u : ℝ := Real.sqrt Lx with hu_def
    have hu_pos : 0 < u := Real.sqrt_pos.mpr hLx_pos
    have hu_sq : u ^ 2 = Lx := Real.sq_sqrt hLx_pos.le
    have hLx_ge_inv : (1 / α) ^ 2 ≤ Lx := by
      have hexp : Real.exp ((1 / α) ^ 2) ≤ x := (le_max_right _ _).trans hx
      exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
    have hαu_ge1 : 1 ≤ α * u := by
      have hsq : (1 : ℝ) ^ 2 ≤ (α * u) ^ 2 := by
        rw [one_pow, mul_pow, hu_sq]
        have h := mul_le_mul_of_nonneg_left hLx_ge_inv (sq_nonneg α)
        rw [← mul_pow, mul_one_div_cancel hα_pos.ne', one_pow] at h
        exact h
      nlinarith [mul_pos hα_pos hu_pos]
    set T : ℝ := Real.exp (α * u) with hT_def
    have hT_pos : 0 < T := Real.exp_pos _
    have hT_ge_e : Real.exp 1 ≤ T := Real.exp_le_exp.mpr hαu_ge1
    have hT_ge2 : 2 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlogT : Real.log T = α * u := Real.log_exp _
    set LT : ℝ := Real.log (T + 2) with hLT_def
    have hLT_ge1 : 1 ≤ LT := by
      have h : Real.exp 1 ≤ T + 2 := by linarith
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h)
    have hLT_pos : 0 < LT := zero_lt_one.trans_le hLT_ge1
    have hLT_le : LT ≤ 2 * (α * u) := by
      have h1 : LT ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hT_pos.ne', hlogT] at h1
      linarith [Real.log_two_lt_d9]
    set c : ℝ := 1 + 1 / (2 * Lx) with hc_def
    have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos (by linarith : 0 < 2 * Lx)]
    have hc_le2 : c ≤ 2 := by
      have h2Lx : 1 ≤ 2 * Lx := by linarith [Real.log_two_gt_d9]
      have : 1 / (2 * Lx) ≤ 1 := (div_le_one (by linarith)).mpr h2Lx
      dsimp only [c]; linarith
    have hx_pow_c : x ^ (c + 1) ≤ 2 * x ^ 2 := by
      have h1 : x ^ (c + 1) = x ^ 2 * x ^ (1 / (2 * Lx)) := by
        rw [show c + 1 = (2 : ℝ) + 1 / (2 * Lx) by dsimp only [c]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (1 / (2 * Lx)) = Real.exp (1 / 2) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; field_simp [hLx_pos.ne']
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num; linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1 / 2)]
      rw [h1, h2]; nlinarith [sq_nonneg x]
    set σ_T : ℝ := 1 - c_star / LT with hσ_def
    have hσ_lt1 : σ_T < 1 := by dsimp only [σ_T]; linarith [div_pos hc_star_pos hLT_pos]
    have hσ_ge_half : 1 / 2 ≤ σ_T := by
      have h1 : c_star / LT ≤ 1 / 4 := by
        calc c_star / LT ≤ c_star / 1 := div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hLT_ge1
          _ = c_star := div_one _
          _ ≤ 1 / 4 := hc_star_le_qtr
      dsimp only [σ_T]; linarith
    have hσ_pos : 0 < σ_T := by linarith
    have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hlo _ him
      have hlog_le : Real.log (|z.im| + 2) ≤ LT :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
      have hlog_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
      have h1 : c_star / LT ≤ c_zf / Real.log (|z.im| + 2) := by
        calc c_star / LT ≤ c_star / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
          _ ≤ c_zf / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_star_le_zf hlog_pos.le
      exact hzf z (by linarith)
    set F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    -- Truncation error
    have htrunc_err :
        ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (48 / Real.pi) * x ^ 2 * Lx / T := by
      have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le χ hx0 hc_gt1 hT_pos
      have hc_sub : c - 1 = 1 / (2 * Lx) := by dsimp only [c]; ring
      rw [hc_sub] at h0
      calc ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖
          ≤ (6 * c / Real.pi) * x ^ (c + 1) / (1 / (2 * Lx) * T) := h0
        _ ≤ (6 * 2 / Real.pi) * (2 * x ^ 2) / (1 / (2 * Lx) * T) := by gcongr
        _ = (48 / Real.pi) * x ^ 2 * Lx / T := by
            field_simp [Real.pi_ne_zero, hLx_pos.ne', hT_pos.ne']; ring
    -- Exact pole-free contour shift from `Stage7PNTInAP.perron_contour_shift_psi1Char`!
    have hshift := Stage7PNTInAP.perron_contour_shift_psi1Char hχ hx0 hσ_pos (by linarith : σ_T < c) hT_pos hzf_rect
    -- Horizontal segments
    have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
        ‖∫ v in σ_T..c, F ((v : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
          2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      intro sgn hsgn
      have hle : σ_T ≤ c := by linarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2) fun v hv => ?_).trans ?_
      · rw [Set.uIoc_of_le hle] at hv
        set z : ℂ := (v : ℂ) + ((sgn * T : ℝ) : ℂ) * I
        have hz_re : z.re = v := by simp [z]
        have hz_im : z.im = sgn * T := by simp [z]
        have hz_abs_im : |z.im| = T := by
          rw [hz_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
        have hz_re_lo : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by
          rw [hz_re, hz_abs_im]
          have : c_star / LT ≤ c₁ / LT := div_le_div_of_nonneg_right hc_star_le_c₁ hLT_pos.le
          dsimp only [σ_T] at hv; linarith [hv.1]
        have hnd := hbd₁ z hz_re_lo (by rw [hz_re]; linarith [hv.2])
        rw [hz_abs_im] at hnd
        have hpow_norm : ‖(x : ℂ) ^ (z + 1)‖ ≤ x ^ (c + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre1 : (z + 1).re = v + 1 := by simp [hz_re]
          rw [hre1]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hv.2])
        have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
          have h2 : T ≤ ‖z + 1‖ := by
            have := Complex.abs_im_le_norm (z + 1); simpa [hz_abs_im] using this
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul]
        calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
                ‖(x : ℂ) ^ (z + 1)‖ / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 2) * x ^ (c + 1) / T ^ 2 := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
                (sq_pos_of_pos hT_pos) hden_ge
          _ = C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        have hlen : c - σ_T ≤ 2 := by linarith
        calc C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 * (c - σ_T)
            ≤ C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 * 2 := mul_le_mul_of_nonneg_left hlen (by positivity)
          _ = 2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by ring
    have htop_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by simpa using hhoriz_bd 1 (by norm_num)
    have hbot_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by simpa using hhoriz_bd (-1) (by norm_num)
    -- Left vertical segment
    have hleft_cont : ContinuousOn (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
      have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous
      have hL'_cont : Continuous (deriv (DirichletCharacter.LFunction χ)) :=
        continuousOn_univ.mp
          ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.deriv isOpen_univ).continuousOn
      have hmap : Continuous (fun t : ℝ => (σ_T : ℂ) + (t : ℂ) * I) := by fun_prop
      have hnd_cont : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((σ_T : ℂ) + (t : ℂ) * I))
          (Set.Icc (-T) T) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        refine (hL'_cont.comp hmap).neg.continuousOn.div (hL_cont.comp hmap).continuousOn fun t ht => ?_
        exact hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2])
      have hpow_cont : Continuous (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) := by
        have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
        have hEq : (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * (((σ_T : ℂ) + (t : ℂ) * I) + 1)) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      have hden_cont : Continuous (fun t : ℝ => ((σ_T : ℂ) + (t : ℂ) * I) * (((σ_T : ℂ) + (t : ℂ) * I) + 1)) := by
        fun_prop
      refine (hnd_cont.mul hpow_cont.continuousOn).div hden_cont.continuousOn fun t _ => ?_
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    have hint_seg : ∀ a b : ℝ, -T ≤ a → b ≤ T → a ≤ b →
        IntervalIntegrable (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) volume a b := by
      intro a b ha hb hab
      refine (hleft_cont.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc ha hb
    have hsplit_left : ∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I) =
        (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)) +
        (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith))
        (hint_seg (-1) 1 (by linarith) (by linarith) (by norm_num))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) 1 le_rfl (by linarith) (by linarith))
        (hint_seg 1 T (by linarith) le_rfl (by linarith))
      rw [← h2, ← h1]
    have hleft_nd : ∀ t : ℝ, |t| ≤ T →
        ‖-deriv (DirichletCharacter.LFunction χ) ((σ_T : ℂ) + (t : ℂ) * I) /
          DirichletCharacter.LFunction χ ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 2 := by
      intro t htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hlog_le : Real.log (|t| + 2) ≤ LT := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
      have hlog_pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      have hre_lo : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by
        rw [hz_re, hz_im]
        have h1 : c_star / LT ≤ c₁ / Real.log (|t| + 2) := by
          calc c_star / LT ≤ c_star / Real.log (|t| + 2) := div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
            _ ≤ c₁ / Real.log (|t| + 2) := div_le_div_of_nonneg_right hc_star_le_c₁ hlog_pos.le
        dsimp only [σ_T]; linarith
      have hnd := hbd₁ z hre_lo (by rw [hz_re]; linarith)
      rw [hz_im] at hnd
      exact hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 2) hC₁.le)
    have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
        ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) / t ^ 2 := by
      intro t ht1 htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
      have hden : t ^ 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : |t| ≤ ‖z‖ := by rw [← hz_im]; exact Complex.abs_im_le_norm z
        have h2 : |t| ≤ ‖z + 1‖ := by have := Complex.abs_im_le_norm (z + 1); simpa [hz_im] using this
        have hsq : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
        nlinarith [abs_nonneg t]
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
      rw [norm_div, norm_mul, hpow]
      calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
              x ^ (σ_T + 1) / ‖z * (z + 1)‖
          ≤ (C₁ * LT ^ 2) * x ^ (σ_T + 1) / t ^ 2 :=
            div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_right (hleft_nd t htT) (Real.rpow_nonneg hx0.le _))
              (by nlinarith [sq_abs t]) hden
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) / t ^ 2 := by ring
    have hinv_sq_1T : ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun u : ℝ => -(u⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht; rw [Set.uIcc_of_le (by linarith)] at ht
        exact ((hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) T) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      simp only [inv_one, sub_neg_eq_add]; linarith [inv_nonneg.mpr hT_pos.le]
    have hinv_sq_neg : ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (-T) (-1 : ℝ), HasDerivAt (fun u : ℝ => -(u⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht; rw [Set.uIcc_of_le (by linarith)] at ht
        exact ((hasDerivAt_inv (by linarith [ht.2] : t ≠ 0)).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (-T) (-1 : ℝ)) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.2])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      simp only [inv_neg, neg_neg, inv_one]; linarith [inv_nonneg.mpr hT_pos.le]
    have hleft_pos_bd : ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (1 : ℝ) T := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht; exact pow_ne_zero 2 (by linarith [ht.1])
      calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (1 : ℝ)..T, C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg 1 T (by linarith) le_rfl (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
              (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) * 1 := mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) := mul_one _
    have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (-T) (-1 : ℝ) := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht; exact pow_ne_zero 2 (by linarith [ht.2])
      calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (-T)..(-1 : ℝ), C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
              (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) * 1 := mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) := mul_one _
    have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        4 * C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * C₁ * LT ^ 2 * x ^ (σ_T + 1)) fun t ht => ?_).trans ?_
      · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
        have hz_re : z.re = σ_T := by simp [z]
        have htT : |t| ≤ T := by have : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩; linarith
        have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
        have hden : 1 / 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : 1 / 2 ≤ ‖z‖ := by
            have := Complex.abs_re_le_norm z; rw [hz_re, abs_of_pos hσ_pos] at this; linarith
          have h2 : 1 ≤ ‖z + 1‖ := by
            have := Complex.abs_re_le_norm (z + 1)
            have hre1 : (z + 1).re = σ_T + 1 := by simp [hz_re]
            rw [hre1, abs_of_pos (by linarith)] at this; linarith
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul, hpow]
        calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
                x ^ (σ_T + 1) / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 2) * x ^ (σ_T + 1) / (1 / 2) :=
              div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right (hleft_nd t htT) (Real.rpow_nonneg hx0.le _))
                (by norm_num) hden
          _ = 2 * C₁ * LT ^ 2 * x ^ (σ_T + 1) := by ring
      · norm_num; linarith
    have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        6 * C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      rw [hsplit_left]
      have htri1 := norm_add_le
        ((∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)))
        (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I))
      have htri2 := norm_add_le
        (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I))
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I))
      linarith
    -- Combine contour shift & truncation error
    have hshift_bd :
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (3 * C₁ / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) +
          (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
      rw [hshift]
      have hnorm_2pi : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hnorm_2piI : ‖((2 * Real.pi * I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      have htri :
          ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
          (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
        have h1 := norm_sub_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)))
        have h2 := norm_add_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)))
        simp only [norm_mul, hnorm_2pi, hnorm_2piI] at h1 h2; linarith
      have hterm_left : (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
          (3 * C₁ / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) := by
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * Real.pi)⁻¹ * (6 * C₁ * LT ^ 2 * x ^ (σ_T + 1)) :=
              mul_le_mul_of_nonneg_left hleft_bd (by positivity)
          _ = (3 * C₁ / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]; ring
      have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 →
          (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
        intro Ival hIval
        have hxc_div : x ^ (c + 1) / T ^ 2 ≤ x ^ 2 / T := by
          have h1 : x ^ (c + 1) / T ^ 2 ≤ (2 * x ^ 2) / T ^ 2 :=
            div_le_div_of_nonneg_right hx_pow_c (sq_nonneg T)
          have h2 : 2 * x ^ 2 / T ^ 2 ≤ x ^ 2 / T := by
            rw [div_le_div_iff₀ (sq_pos_of_pos hT_pos) hT_pos]
            have hT2 : 2 * T ≤ T ^ 2 := by nlinarith
            nlinarith [sq_nonneg x]
          linarith
        calc (2 * Real.pi)⁻¹ * ‖Ival‖
            ≤ (2 * Real.pi)⁻¹ * (2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2) :=
              mul_le_mul_of_nonneg_left hIval (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 2 * (x ^ (c + 1) / T ^ 2) := by field_simp [Real.pi_ne_zero, hT_pos.ne']
          _ ≤ (C₁ / Real.pi) * LT ^ 2 * (x ^ 2 / T) := mul_le_mul_of_nonneg_left hxc_div (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by ring
      have htop_h := hterm_horiz _ htop_bd
      have hbot_h := hterm_horiz _ hbot_bd
      change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
      have hsum2 : (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T + (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T =
          (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by ring
      linarith
    have htotal : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        (48 / Real.pi) * x ^ 2 * Lx / T +
        (3 * C₁ / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) +
        (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
      have htri : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ +
          ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
          (Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
      linarith
    have hLT_sq : LT ^ 2 ≤ c_star * Lx := by
      have h1 := pow_le_pow_left₀ hLT_pos.le hLT_le 2
      have h2 : (2 * (α * u)) ^ 2 = c_star * Lx := by
        rw [show 2 * (α * u) = (2 * α) * u by ring, mul_pow, h2α_sq, hu_sq]
      linarith
    have hx_left_exp : x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-α * u) := by
      have h1 : x ^ (σ_T + 1) = x ^ 2 * x ^ (-(c_star / LT)) := by
        rw [show σ_T + 1 = (2 : ℝ) + (-(c_star / LT)) by dsimp only [σ_T]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (-(c_star / LT)) = Real.exp (-(c_star * Lx / LT)) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; ring
      have hexp_le : -(c_star * Lx / LT) ≤ -α * u := by
        have hdiv : α * u ≤ c_star * Lx / LT := by
          rw [le_div_iff₀ hLT_pos]
          calc α * u * LT ≤ α * u * (2 * (α * u)) := mul_le_mul_of_nonneg_left hLT_le (by positivity)
            _ = (1 / 2) * ((2 * α) ^ 2 * u ^ 2) := by ring
            _ = (1 / 2) * (c_star * Lx) := by rw [h2α_sq, hu_sq]
            _ ≤ c_star * Lx := by nlinarith
        linarith
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (sq_nonneg x)
    have hinvT : (1 : ℝ) / T = Real.exp (-α * u) := by
      rw [hT_def, one_div, ← Real.exp_neg]; congr 1; ring
    have habsorb : Lx * Real.exp (-α * u) ≤ (4 / α) ^ 2 * Real.exp (-c_fin * u) := by
      have hsplit : Real.exp (-α * u) =
          Real.exp (-((2 : ℕ) : ℝ) * ((α / 4) * u)) * Real.exp (-c_fin * u) := by
        rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; push_cast; ring
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hv_nn : 0 ≤ (α / 4) * u := by positivity
      have hid : Lx * Real.exp (-((2 : ℕ) : ℝ) * ((α / 4) * u)) =
          (4 / α) ^ 2 * (((α / 4) * u) ^ 2 * Real.exp (-((2 : ℕ) : ℝ) * ((α / 4) * u))) := by
        have h1 : Lx = (4 / α) ^ 2 * ((α / 4) * u) ^ 2 := by
          rw [← mul_pow, show (4 / α) * ((α / 4) * u) = u by field_simp [hα_pos.ne'], hu_sq]
        have h2 := congrArg (· * Real.exp (-((2 : ℕ) : ℝ) * ((α / 4) * u))) h1
        simpa only [mul_assoc] using h2
      calc Lx * Real.exp (-((2 : ℕ) : ℝ) * ((α / 4) * u))
          = (4 / α) ^ 2 * (((α / 4) * u) ^ 2 * Real.exp (-((2 : ℕ) : ℝ) * ((α / 4) * u))) := hid
        _ ≤ (4 / α) ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one 2 hv_nn) (by positivity)
        _ = (4 / α) ^ 2 := mul_one _
    have hterm1 : (48 / Real.pi) * x ^ 2 * Lx / T =
        (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have hterm2 : (3 * C₁ / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) ≤
        ((3 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      calc (3 * C₁ / Real.pi) * LT ^ 2 * x ^ (σ_T + 1)
          ≤ (3 * C₁ / Real.pi) * (c_star * Lx) * (x ^ 2 * Real.exp (-α * u)) := by gcongr
        _ = ((3 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by ring
    have hterm3 : (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T ≤
        ((2 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]
      calc (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 * Real.exp (-α * u)
          ≤ (2 * C₁ / Real.pi) * (c_star * Lx) * x ^ 2 * Real.exp (-α * u) := by gcongr
        _ = ((2 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by ring
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) *
            x ^ 2 * (Lx * Real.exp (-α * u)) := by linarith
      _ ≤ (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) *
            x ^ 2 * ((4 / α) ^ 2 * Real.exp (-c_fin * u)) := by gcongr
      _ = K_large * x ^ 2 * Real.exp (-c_fin * u) := by dsimp only [K_large]; ring
  set C_small : ℝ := 6 * Real.exp (c_fin * Real.sqrt (Real.log x₀))
  set C_fin : ℝ := max K_large C_small
  refine ⟨c_fin, hc_fin_pos, C_fin, lt_of_lt_of_le hK_large_pos (le_max_left _ _), fun x hx2 => ?_⟩
  by_cases hge : x₀ ≤ x
  · exact (hlarge x hge).trans (by gcongr; exact le_max_left _ _)
  · push Not at hge
    have hpsi1_le : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ 6 * x ^ 2 := by
      have h1 : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ x * RHDirect.chebyshevPsi x := by
        unfold Stage4ExplicitFormula.psi1Char RHDirect.chebyshevPsi
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.norm_of_nonneg (le_max_right _ _)]
        have hmax : max (x - (n : ℝ)) 0 ≤ x :=
          max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        have hchi : ‖χ n‖ ≤ 1 := χ.norm_le_one _
        calc Λ n * ‖χ n‖ * max (x - (n : ℝ)) 0
            ≤ Λ n * 1 * x :=
              mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
                hmax (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
          _ = x * Λ n := by ring
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ x)
      nlinarith
    have hexp_ge : Real.exp (-c_fin * Real.sqrt (Real.log x₀)) ≤ Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hge.le
      nlinarith [Real.sqrt_le_sqrt hlog]
    have hcancel : C_small * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) = 6 := by
      dsimp only [C_small]; rw [mul_assoc, ← Real.exp_add]
      have : c_fin * Real.sqrt (Real.log x₀) + -c_fin * Real.sqrt (Real.log x₀) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ 6 * x ^ 2 := hpsi1_le
      _ = C_small * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) := by rw [← hcancel]; ring
      _ ≤ C_small * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by gcongr
      _ ≤ C_fin * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL `√(log x)` CHARACTER-SUM DECAY (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ ≠ 1`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, ‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
private lemma effective_chebyshevPsiChar_bound_sqrt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hpsi1⟩ := effective_psi1Char_bound_sqrt hχ
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c_fin : ℝ := min (c₁ / 2) c_ψ
  have hc_fin_pos : 0 < c_fin := lt_min (by positivity) hc_ψ
  have hc_fin_le1 : c_fin ≤ c₁ / 2 := min_le_left _ _
  have hc_fin_le_ψ : c_fin ≤ c_ψ := min_le_right _ _
  set C_fin : ℝ := 5 * C₁ + 1 + 3 * C_ψ
  refine ⟨c_fin, hc_fin_pos, C_fin, by positivity, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  set u : ℝ := Real.sqrt (Real.log x)
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  set E : ℝ := Real.exp (-c_fin * u) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := x * E with hh_def
  have hh_pos : 0 < h := by positivity
  have hh_le_x : h ≤ x := by nlinarith
  have hxph_ge2 : 2 ≤ x + h := by linarith
  have hxph_le2x : x + h ≤ 2 * x := by linarith
  have hexp_E2 : Real.exp (-c₁ * u) ≤ E ^ 2 := by
    rw [hE_def, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; nlinarith
  have hexp_xh : Real.exp (-c₁ * Real.sqrt (Real.log (x + h))) ≤ E ^ 2 := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    exact (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlog])).trans hexp_E2
  have hexp_psi : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ E :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp_psi_xh : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ E := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    exact (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlog])).trans hexp_psi
  have hdiff := Stage7PNTInAP.norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le χ hx0.le hh_pos.le
  have hnorm_mul : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ + ‖Stage4ExplicitFormula.psi1Char χ x‖ +
        h * (RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x) := by
    have h1 : ‖(h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x‖ +
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
      have htri := norm_sub_le
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x)
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x)
      simpa [sub_sub_cancel] using htri
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh_pos.le] at h1
    linarith [norm_sub_le (Stage4ExplicitFormula.psi1Char χ (x + h)) (Stage4ExplicitFormula.psi1Char χ x)]
  have hbd_xh : ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ ≤ 4 * C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖
        ≤ C₁ * (x + h) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log (x + h))) := hpsi1 (x + h) hxph_ge2
      _ ≤ C₁ * (2 * x) ^ 2 * E ^ 2 := by
          have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C₁ * x ^ 2 * E ^ 2 := by ring
  have hbd_x : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ C₁ * x ^ 2 * Real.exp (-c₁ * u) := hpsi1 x hx2
      _ ≤ C₁ * x ^ 2 * E ^ 2 := by gcongr
  have hpsi_diff_le : RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x ≤
      (1 + 3 * C_ψ) * x * E := by
    have h1 := (abs_le.mp (hpsi (x + h) hxph_ge2)).2
    have h2 := (abs_le.mp (hpsi x hx2)).1
    have h3 : C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ 2 * C_ψ * x * E := by
      calc C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h)))
          ≤ C_ψ * (2 * x) * E := by gcongr
        _ = 2 * C_ψ * x * E := by ring
    have h4 : C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ C_ψ * x * E := by gcongr
    dsimp only [h] at h1 h2 h3 ⊢; linarith
  have hcomb : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ h * (C_fin * x * E) := by
    have hrhs1 : 5 * C₁ * x ^ 2 * E ^ 2 = h * (5 * C₁ * x * E) := by dsimp only [h]; ring
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_diff_le hh_pos.le
    have hrhs2 : h * (5 * C₁ * x * E) + h * ((1 + 3 * C_ψ) * x * E) = h * (C_fin * x * E) := by
      dsimp only [C_fin]; ring
    linarith
  exact le_of_mul_le_mul_left hcomb hh_pos

/-- Uniform `√(log x)` bound over any finite set of non-principal characters. -/
private lemma exists_uniform_nonprincipal_char_bound_sqrt {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ χ ∈ S, ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 1, one_pos, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert χ₀ S' hnot ih =>
    obtain ⟨c₀, hc₀, C₀, hC₀, hbd₀⟩ := effective_chebyshevPsiChar_bound_sqrt (hS χ₀ (Finset.mem_insert_self _ _))
    obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := ih fun χ hχ => hS χ (Finset.mem_insert_of_mem hχ)
    refine ⟨min c₀ c₁, lt_min hc₀ hc₁, max C₀ C₁, lt_of_lt_of_le hC₀ (le_max_left _ _), fun χ hχ x hx => ?_⟩
    have hsqrt_nn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    rcases Finset.mem_insert.mp hχ with rfl | hmem
    · calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
          ≤ C₀ * x * Real.exp (-c₀ * Real.sqrt (Real.log x)) := hbd₀ x hx
        _ ≤ max C₀ C₁ * x * Real.exp (-(min c₀ c₁) * Real.sqrt (Real.log x)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
              (Real.exp_le_exp.mpr (by nlinarith [min_le_left c₀ c₁])) (Real.exp_pos _).le (by positivity)
    · calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
          ≤ C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) := hbd₁ χ hmem x hx
        _ ≤ max C₀ C₁ * x * Real.exp (-(min c₀ c₁) * Real.sqrt (Real.log x)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
              (Real.exp_le_exp.mpr (by nlinarith [min_le_right c₀ c₁])) (Real.exp_pos _).le (by positivity)

/-- Helper: `√x * log x ≤ 4 * x * exp (-c * √(log x))` for `0 < c ≤ 1/4` and `x ≥ 2`. -/
private lemma sqrt_mul_log_le_four_mul_exp_neg_sqrt {c x : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hx : 2 ≤ x) :
    Real.sqrt x * Real.log x ≤ 4 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  set Lx : ℝ := Real.log x with hLx_def
  have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
  have hsqrt_eq : Real.sqrt x = x * Real.exp (-(1 / 2) * Lx) := by
    have h1 : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have h2 : x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2 : ℝ)) := by
      calc x ^ (1 / 2 : ℝ) = x ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := by norm_num
        _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := Real.rpow_add hx0 _ _
        _ = x * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
    rw [h1, h2, Real.rpow_def_of_pos hx0, ← hLx_def]; congr 2; ring
  have hkey : Lx * Real.exp (-(1 / 2) * Lx) ≤ 4 * Real.exp (-c * Real.sqrt Lx) := by
    by_cases hL1 : 1 ≤ Lx
    · have hsq_le : Real.sqrt Lx ≤ Lx := by
        have : Lx ≤ Lx ^ 2 := by nlinarith
        exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hLx_pos.le)
      have hexp : Real.exp (-(1 / 2) * Lx) ≤ Real.exp (-(Lx / 4)) * Real.exp (-c * Real.sqrt Lx) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      have h1 := pow_mul_exp_neg_le_one 1 (show 0 ≤ Lx / 4 by linarith)
      simp only [pow_one, Nat.cast_one, neg_mul, one_mul] at h1
      calc Lx * Real.exp (-(1 / 2) * Lx)
          ≤ Lx * (Real.exp (-(Lx / 4)) * Real.exp (-c * Real.sqrt Lx)) :=
            mul_le_mul_of_nonneg_left hexp hLx_pos.le
        _ = 4 * ((Lx / 4) * Real.exp (-(Lx / 4))) * Real.exp (-c * Real.sqrt Lx) := by ring
        _ ≤ 4 * 1 * Real.exp (-c * Real.sqrt Lx) := by gcongr
        _ = 4 * Real.exp (-c * Real.sqrt Lx) := by ring
    · push Not at hL1
      have hsq_le1 : Real.sqrt Lx ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1.le
      have h1 : Real.exp (-(1 / 2) * Lx) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-c * Real.sqrt Lx) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg Lx])
      have h3 : (1 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
      calc Lx * Real.exp (-(1 / 2) * Lx) ≤ 1 * 1 := mul_le_mul hL1.le h1 (Real.exp_pos _).le zero_le_one
        _ = 4 * (1 / 4) := by norm_num
        _ ≤ 4 * Real.exp (-c * Real.sqrt Lx) := by linarith
  rw [hsqrt_eq]
  have := mul_le_mul_of_nonneg_left hkey hx0.le
  linarith

/-- **UNCONDITIONAL SHARP `√(log x)` EFFECTIVE PNT IN ARITHMETIC PROGRESSIONS FOR `ψ(x; q, a)` (`0` ASSUMPTIONS!)**:
upgrades `Stage7PNTInAP.effective_pnt_psiAP` from `(log x)^(1/20)` to the classical de la Vallée Poussin
`√(log x)` error term for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `Nat.Coprime a q`! -/
theorem effective_pnt_psiAP_sqrt {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  classical
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  obtain ⟨c_χ, hc_χ, C_χ, hC_χ, hchar⟩ :=
    exists_uniform_nonprincipal_char_bound_sqrt (Finset.univ.erase (1 : DirichletCharacter ℂ q))
      (fun χ hχ => (Finset.mem_erase.mp hχ).1)
  set c_fin : ℝ := min (min c_ψ c_χ) (1 / 4)
  have hc_fin_pos : 0 < c_fin := by positivity
  have hc_fin_le_ψ : c_fin ≤ c_ψ := (min_le_left _ _).trans (min_le_left _ _)
  have hc_fin_le_χ : c_fin ≤ c_χ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_fin_le_qtr : c_fin ≤ 1 / 4 := min_le_right _ _
  set ω : ℝ := (q.primeFactors.card : ℝ)
  set C_fin : ℝ := C_ψ + 4 * ω + C_χ
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine ⟨c_fin, hc_fin_pos, C_fin, by positivity, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  set E : ℝ := Real.exp (-c_fin * Real.sqrt (Real.log x))
  have hpsi_bd : |RHDirect.chebyshevPsi x - x| ≤ C_ψ * x * E := by
    refine (hpsi x hx2).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have hlog_bd : ω * Real.log x ≤ (4 * ω) * x * E := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have h1 : Real.log x ≤ Real.sqrt x * Real.log x := by nlinarith [Real.log_pos (by linarith : (1 : ℝ) < x)]
    have h2 := h1.trans (sqrt_mul_log_le_four_mul_exp_neg_sqrt hc_fin_pos hc_fin_le_qtr hx2)
    have hω_nn : 0 ≤ ω := Nat.cast_nonneg _
    calc ω * Real.log x ≤ ω * (4 * x * E) := mul_le_mul_of_nonneg_left h2 hω_nn
      _ = (4 * ω) * x * E := by ring
  have hchar_bd : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C_χ * x * E := by
    intro χ hχ
    have hmem : χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
      Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ _⟩
    exact (hchar χ hmem x hx2).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity))
  have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop
    (by linarith : 1 ≤ x) (by positivity : 0 ≤ C_χ * x * E) hpsi_bd hchar_bd
  have hdiv_le : (C_ψ * x * E + ω * Real.log x) / (q.totient : ℝ) ≤ (C_ψ + 4 * ω) * x * E := by
    calc (C_ψ * x * E + ω * Real.log x) / (q.totient : ℝ)
        ≤ (C_ψ * x * E + (4 * ω) * x * E) / 1 :=
          div_le_div₀ (by positivity) (by linarith) zero_lt_one hphi_ge1
      _ = (C_ψ + 4 * ω) * x * E := by ring
  dsimp only [C_fin]; linarith

/-- **UNCONDITIONAL SHARP `√(log x)` EFFECTIVE PNT IN ARITHMETIC PROGRESSIONS FOR `θ(x; q, a)` (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `Nat.Coprime a q`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |chebyshevThetaAP q a x - x / φ(q)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem effective_pnt_thetaAP_sqrt {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hpsi⟩ := effective_pnt_psiAP_sqrt hcop
  set c' : ℝ := min c (1 / 4)
  have hc'_pos : 0 < c' := lt_min hc (by norm_num)
  refine ⟨c', hc'_pos, C + 4, by positivity, fun x hx => ?_⟩
  have hdiff : |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| ≤
      Real.sqrt x * Real.log x := by
    have h1 := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a x
    have h2 := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a (by linarith : 1 ≤ x)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]; exact h2
  have hsqrt := sqrt_mul_log_le_four_mul_exp_neg_sqrt hc'_pos (min_le_right _ _) hx
  have hpsi' : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      C * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
    refine (hpsi x hx).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [min_le_left c (1 / 4 : ℝ), Real.sqrt_nonneg (Real.log x)]))
      (by positivity)
  have htri : |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
      |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| +
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| := by
    simpa [sub_add_sub_cancel] using abs_add_le
      (Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x)
      (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ))
  linarith

end APShortInterval

/-- **UNCONDITIONAL SUPER-POLYNOMIAL SHORT-INTERVAL PRIMES IN EVERY ARITHMETIC PROGRESSION (`0` ASSUMPTIONS!)**:
for EVERY modulus `q ≥ 1` (`[NeZero q]`) and EVERY coprime `a` (`Nat.Coprime a q`), there exist
`c_q > 0` and `X_q : ℝ` such that for ALL `x ≥ X_q`, there exists a prime `p ≡ a [MOD q]` in
`(x, x + x * Real.exp (-c_q * Real.sqrt (Real.log x))]`. -/
theorem exists_prime_in_AP_short_interval {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c_q : ℝ, 0 < c_q ∧ ∃ X_q : ℝ, ∀ x : ℝ, X_q ≤ x →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x + x * Real.exp (-c_q * Real.sqrt (Real.log x)) := by
  obtain ⟨c_θ, hc_θ, C_θ, hC_θ, hth⟩ := effective_pnt_thetaAP_sqrt hcop
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set c_q : ℝ := c_θ / 2
  have hc_pos : 0 < c_q := by positivity
  have hev := (tendsto_exp_neg_mul_sqrt_log hc_pos).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * (q.totient : ℝ) * C_θ) by positivity))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨c_q, hc_pos, max 2 X₁, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  set δ : ℝ := Real.exp (-c_q * Real.sqrt (Real.log x)) with hδ_def
  have hδ_pos : 0 < δ := Real.exp_pos _
  have hδ_le1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
  have hδ_small : δ < 1 / (4 * (q.totient : ℝ) * C_θ) := hX₁ x hx1
  set y : ℝ := x + x * δ with hy_def
  have hxy : x ≤ y := by nlinarith
  have hy2 : 2 ≤ y := by linarith
  have hy_le2x : y ≤ 2 * x := by nlinarith
  have hE_x : Real.exp (-c_θ * Real.sqrt (Real.log x)) = δ ^ 2 := by
    rw [hδ_def, ← Real.exp_nat_mul]; congr 1; push_cast; dsimp only [c_q]; ring
  have hE_y : Real.exp (-c_θ * Real.sqrt (Real.log y)) ≤ δ ^ 2 := by
    rw [← hE_x]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    nlinarith [Real.sqrt_le_sqrt hlog]
  have hth_x := (abs_le.mp (hth x hx2)).2
  have hth_y := (abs_le.mp (hth y hy2)).1
  have hth_diff : Stage2DirichletAP.chebyshevThetaAP q a x < Stage2DirichletAP.chebyshevThetaAP q a y := by
    have h1 : C_θ * y * Real.exp (-c_θ * Real.sqrt (Real.log y)) ≤ 2 * C_θ * x * δ ^ 2 := by
      calc C_θ * y * Real.exp (-c_θ * Real.sqrt (Real.log y))
          ≤ C_θ * (2 * x) * δ ^ 2 := by gcongr
        _ = 2 * C_θ * x * δ ^ 2 := by ring
    have h2 : C_θ * x * Real.exp (-c_θ * Real.sqrt (Real.log x)) = C_θ * x * δ ^ 2 := by rw [hE_x]
    have h3 : 3 * (q.totient : ℝ) * C_θ * δ < 1 := by
      have := mul_lt_mul_of_pos_left hδ_small (show (0 : ℝ) < 4 * (q.totient : ℝ) * C_θ by positivity)
      rw [mul_one_div_cancel (by positivity : (4 * (q.totient : ℝ) * C_θ) ≠ 0)] at this
      nlinarith
    have h4 : 3 * C_θ * x * δ ^ 2 < (x * δ) / (q.totient : ℝ) := by
      rw [lt_div_iff₀ hphi_pos]
      have h := mul_lt_mul_of_pos_right h3 (mul_pos hx0 hδ_pos)
      linarith
    have hdiff_main : y / (q.totient : ℝ) - x / (q.totient : ℝ) = (x * δ) / (q.totient : ℝ) := by
      dsimp only [y]; ring
    linarith
  exact exists_prime_in_AP_Ioc_of_thetaAP_lt q a hx0.le hxy hth_diff

/-- **UNCONDITIONAL POLYLOGARITHMIC SHORT-INTERVAL PRIMES IN EVERY ARITHMETIC PROGRESSION (`0` ASSUMPTIONS!)**:
for EVERY modulus `q ≥ 1` (`[NeZero q]`), EVERY coprime `a`, and EVERY `A > 0`, for all sufficiently
large `x` there is a prime `p ≡ a [MOD q]` in `(x, x + x / (Real.log x) ^ A]`. -/
theorem exists_prime_in_AP_Ioc_polylog {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q)
    (A : ℝ) (hA : 0 < A) :
    ∃ X_q : ℝ, ∀ x : ℝ, X_q ≤ x →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x / (Real.log x) ^ A := by
  obtain ⟨c_q, hc_q, X₁, hshort⟩ := exists_prime_in_AP_short_interval hcop
  have hev := eventually_exp_neg_sqrt_log_le_inv_rpow hc_q hA
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₂, hX₂⟩ := hev
  refine ⟨max (max X₁ X₂) 2, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx2 : X₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx_ge2 : 2 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨p, hp, hmod, hxp, hpy⟩ := hshort x hx1
  refine ⟨p, hp, hmod, hxp, hpy.trans ?_⟩
  have hle := hX₂ x hx2
  have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ x by linarith)
  rw [mul_one_div] at hmul
  linarith

/-! ## Section 3: Unconditional Asymptotics of Ramanujan Primes (`R_n ~ 2 n log n`, Sondow 2009) -/

/-- `isRamanujanPrimeBound n R` means every integer `x ≥ R` has at least `n` primes in `(x/2, x]`. -/
def isRamanujanPrimeBound (n R : ℕ) : Prop :=
  ∀ x : ℕ, R ≤ x → n ≤ Nat.primeCounting x - Nat.primeCounting (x / 2)

/-- The `n`-th Ramanujan prime `R_n`: the least `R : ℕ` such that `π(x) - π(⌊x/2⌋) ≥ n`
for all `x ≥ R`. -/
noncomputable def ramanujanPrime (n : ℕ) : ℕ :=
  sInf {R : ℕ | isRamanujanPrimeBound n R}

/-- **Dyadic Prime Counting Asymptotic (`π(x) - π(⌊x/2⌋) ~ x / (2 log x)`, 0 ASSUMPTIONS!)**:
`Tendsto (fun x : ℕ => ((Nat.primeCounting x - Nat.primeCounting (x / 2) : ℕ) : ℝ) / ((x : ℝ) / (2 * Real.log (x : ℝ)))) atTop (𝓝 1)`. -/
theorem primeCounting_dyadic_asymp :
    Tendsto
      (fun x : ℕ =>
        ((Nat.primeCounting x - Nat.primeCounting (x / 2) : ℕ) : ℝ) /
          ((x : ℝ) / (2 * Real.log (x : ℝ))))
      atTop (𝓝 1) := by
  have hdiv2_top : Tendsto (fun x : ℕ => x / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨2 * b, fun x hx => by omega⟩
  have hhalf_ratio : Tendsto (fun x : ℕ => ((x / 2 : ℕ) : ℝ) / (x : ℝ)) atTop (𝓝 (1 / 2)) := by
    have hinv : Tendsto (fun x : ℕ => (1 : ℝ) / (x : ℝ)) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr fun x => by simp [one_div]
    have hlo : Tendsto (fun x : ℕ => (1 / 2 : ℝ) - (1 : ℝ) / (x : ℝ)) atTop (𝓝 (1 / 2)) := by
      simpa using tendsto_const_nhds.sub hinv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr hx
      have hnat : x ≤ 2 * (x / 2) + 1 := by omega
      have hR : (x : ℝ) ≤ 2 * ((x / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hx0]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr hx
      have hnat : 2 * (x / 2) ≤ x := by omega
      have hR : 2 * ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnat
      rw [div_le_iff₀ hx0]; linarith
  have hlog_half : Tendsto (fun x : ℕ => Real.log (x : ℝ) / Real.log ((x / 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hlog_ratio : Tendsto (fun x : ℕ => Real.log (((x / 2 : ℕ) : ℝ) / (x : ℝ))) atTop (𝓝 (Real.log (1 / 2))) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp hhalf_ratio
    have hlogx_top : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hquot : Tendsto (fun x : ℕ => Real.log (((x / 2 : ℕ) : ℝ) / (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) := by
      have h := hlog_ratio.mul (tendsto_inv_atTop_zero.comp hlogx_top)
      rw [mul_zero] at h
      exact h.congr fun x => by simp [div_eq_mul_inv]
    have hinv_lim : Tendsto (fun x : ℕ => Real.log ((x / 2 : ℕ) : ℝ) / Real.log (x : ℝ)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add hquot
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 4] with x hx
      have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
      have hx20 : (0 : ℝ) < ((x / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < x / 2)
      have hlogx0 : (0 : ℝ) < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
      rw [Real.log_div hx20.ne' hx0.ne']
      field_simp [hlogx0.ne']
      ring
    have hrec := hinv_lim.inv₀ one_ne_zero
    rw [inv_one] at hrec
    exact hrec.congr fun x => by rw [inv_div]
  have hpnt_half :
      Tendsto (fun x : ℕ => (Nat.primeCounting (x / 2) : ℝ) / ((x : ℝ) / Real.log (x : ℝ)))
        atTop (𝓝 (1 / 2)) := by
    have h1 := Stage6EffectivePNT.pnt_primeCounting_asymp.comp hdiv2_top
    have hmul := (h1.mul hhalf_ratio).mul hlog_half
    rw [one_mul, mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with x hx
    have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hx20 : (0 : ℝ) < ((x / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < x / 2)
    have hlogx0 : (0 : ℝ) < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hlogx20 : (0 : ℝ) < Real.log ((x / 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x / 2))
    dsimp only [Function.comp_apply]
    field_simp [hx0.ne', hx20.ne', hlogx0.ne', hlogx20.ne']
  have hsub := Stage6EffectivePNT.pnt_primeCounting_asymp.sub hpnt_half
  have hmul2 := hsub.const_mul 2
  have hlim_val : (2 : ℝ) * (1 - 1 / 2) = 1 := by norm_num
  rw [hlim_val] at hmul2
  refine hmul2.congr' ?_
  filter_upwards [eventually_ge_atTop 4] with x hx
  have hmono : Nat.primeCounting (x / 2) ≤ Nat.primeCounting x :=
    Nat.monotone_primeCounting (Nat.div_le_self x 2)
  rw [Nat.cast_sub hmono]
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx0 : (0 : ℝ) < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  field_simp [hx0.ne', hlogx0.ne']

/-- The Ramanujan prime bound set `{R | isRamanujanPrimeBound n R}` is nonempty for EVERY `n : ℕ`. -/
theorem ramanujanPrime_set_nonempty (n : ℕ) :
    {R : ℕ | isRamanujanPrimeBound n R}.Nonempty := by
  have h_div : Tendsto (fun x : ℕ => (x : ℝ) / (2 * Real.log (x : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => (2 * Real.log x) / x) atTop (𝓝 0) := by
      have h := tendsto_log_div_self.const_mul 2
      rw [mul_zero] at h
      exact h.congr fun x => by ring
    have h1_pos : Tendsto (fun x : ℝ => (2 * Real.log x) / x) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_pos (mul_pos two_pos (Real.log_pos hx)) (by linarith)
    have hreal : Tendsto (fun x : ℝ => x / (2 * Real.log x)) atTop atTop :=
      (tendsto_inv_nhdsGT_zero.comp h1_pos).congr fun x => by
        dsimp only [Function.comp_apply]; rw [inv_div]
    exact hreal.comp tendsto_natCast_atTop_atTop
  have hev1 := primeCounting_dyadic_asymp.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hev2 := h_div.eventually (eventually_ge_atTop (2 * (n : ℝ)))
  have hev := (hev1.and hev2).and (eventually_ge_atTop 4)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  refine ⟨R, fun x hx => ?_⟩
  obtain ⟨⟨h1, h2⟩, hx4⟩ := hR x hx
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx0 : (0 : ℝ) < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hden : 0 < (x : ℝ) / (2 * Real.log (x : ℝ)) := div_pos hx0 (mul_pos two_pos hlogx0)
  have hgt := (lt_div_iff₀ hden).mp h1
  have hcast : (n : ℝ) ≤ ((Nat.primeCounting x - Nat.primeCounting (x / 2) : ℕ) : ℝ) := by linarith
  exact_mod_cast hcast

/-- `ramanujanPrime n` satisfies `isRamanujanPrimeBound n`. -/
theorem isRamanujanPrimeBound_ramanujanPrime (n : ℕ) :
    isRamanujanPrimeBound n (ramanujanPrime n) :=
  Nat.sInf_mem (ramanujanPrime_set_nonempty n)

/-- Every `n`-th Ramanujan prime (`n ≥ 1`) is genuinely prime! -/
theorem ramanujanPrime_prime {n : ℕ} (hn : 1 ≤ n) :
    (ramanujanPrime n).Prime := by
  set R := ramanujanPrime n
  have hR_bound : isRamanujanPrimeBound n R := isRamanujanPrimeBound_ramanujanPrime n
  have hR_pos : 1 ≤ R := by
    by_contra h0
    have hR0 : R = 0 := by omega
    have hbad := hR_bound 0 (by omega)
    have hpc0 : Nat.primeCounting 0 = 0 := by decide
    simp [hpc0] at hbad
    omega
  have hnot : ¬ isRamanujanPrimeBound n (R - 1) := by
    intro hmem
    have hle : R ≤ R - 1 := Nat.sInf_le hmem
    omega
  unfold isRamanujanPrimeBound at hnot
  push Not at hnot
  obtain ⟨x, hx_ge, hx_lt⟩ := hnot
  have hx_eq : x = R - 1 := by
    by_contra hne
    have hgeR : R ≤ x := by omega
    have := hR_bound x hgeR
    omega
  subst hx_eq
  have hR_ge : n ≤ Nat.primeCounting R - Nat.primeCounting (R / 2) := hR_bound R le_rfl
  have hhalf : Nat.primeCounting ((R - 1) / 2) ≤ Nat.primeCounting (R / 2) :=
    Nat.monotone_primeCounting (Nat.div_le_div_right (Nat.sub_le R 1))
  have hlt_pc : Nat.primeCounting (R - 1) < Nat.primeCounting R := by omega
  have hsucc : R - 1 + 1 = R := by omega
  have hstep : Nat.primeCounting R = Nat.primeCounting (R - 1) + if R.Prime then 1 else 0 := by
    unfold Nat.primeCounting Nat.primeCounting'
    conv_lhs => rw [← hsucc]
    rw [Nat.count_succ, hsucc]
  by_contra hnp
  rw [if_neg hnp, add_zero] at hstep
  omega

/-- Monotonicity of `t ↦ t / (2 * Real.log t)` on `[Real.exp 1, ∞)`. -/
private lemma monotoneOn_div_two_log :
    MonotoneOn (fun t : ℝ => t / (2 * Real.log t)) (Set.Ici (Real.exp 1)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici (Real.exp 1)) ?_ ?_ ?_
  · refine continuousOn_id.div (continuousOn_const.mul (Real.continuousOn_log.mono ?_)) ?_
    · intro t ht; exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos 1) ht)
    · intro t ht
      have hlt : 1 ≤ Real.log t := by
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ht
      exact mul_ne_zero two_ne_zero (by linarith)
  · intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos 1) ht
    have hlt : 1 < Real.log t := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) ht
    exact ((hasDerivAt_id t).div ((Real.hasDerivAt_log ht0.ne').const_mul 2)
      (mul_ne_zero two_ne_zero (by linarith))).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos 1) ht
    have hlt : 1 < Real.log t := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) ht
    have hd : HasDerivAt (fun u : ℝ => u / (2 * Real.log u))
        ((1 * (2 * Real.log t) - t * (2 * t⁻¹)) / (2 * Real.log t) ^ 2) t :=
      (hasDerivAt_id t).div ((Real.hasDerivAt_log ht0.ne').const_mul 2)
        (mul_ne_zero two_ne_zero (by linarith))
    rw [hd.deriv]
    refine div_nonneg ?_ (sq_nonneg _)
    have hmul : t * (2 * t⁻¹) = 2 := by field_simp [ht0.ne']
    linarith

/-- Helper: for any `c > 0`, `Real.log (c * n * Real.log n) / Real.log n → 1`. -/
private lemma tendsto_log_const_mul_n_log_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (c * (n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hlogn_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.log c / Real.log (n : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hlogn_top).const_mul (Real.log c)
    rw [mul_zero] at h
    exact h.congr fun n => by simp [div_eq_mul_inv]
  have h2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_log_log_div_log.comp tendsto_natCast_atTop_atTop
  have hsum := (h1.add (tendsto_const_nhds (x := (1 : ℝ)))).add h2
  rw [zero_add, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn0 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [Real.log_mul (mul_pos hc hn0).ne' hlogn0.ne', Real.log_mul hc.ne' hn0.ne']
  field_simp [hlogn0.ne']

/-- **UNCONDITIONAL RAMANUJAN PRIME ASYMPTOTIC (`R_n ~ 2 n log n`, Sondow 2009, 0 ASSUMPTIONS!)**:
`Tendsto (fun n : ℕ => (ramanujanPrime n : ℝ) / (2 * (n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1)`. -/
theorem ramanujan_prime_asymptotic :
    Tendsto
      (fun n : ℕ => (ramanujanPrime n : ℝ) / (2 * (n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := min (ε / 2) (1 / 4) with hη_def
  have hη_pos : 0 < η := lt_min (by linarith) (by norm_num)
  have hη_le_eps : η ≤ ε / 2 := min_le_left _ _
  have hη_le_qtr : η ≤ 1 / 4 := min_le_right _ _
  -- Get dyadic prime-counting band `(1 - η/4, 1 + η/4)` for all `x ≥ X₁`
  have hev_dyad := primeCounting_dyadic_asymp.eventually
    (Ioo_mem_nhds (by linarith : 1 - η / 4 < 1) (by linarith : 1 < 1 + η / 4))
  rw [Filter.eventually_atTop] at hev_dyad
  obtain ⟨X₁, hX₁⟩ := hev_dyad
  -- Auxiliary `n log n → ∞`
  have hnlog_top : Tendsto (fun n : ℕ => 2 * (n : ℝ) * Real.log (n : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact h1.atTop_mul_atTop₀ h2
  -- Upper bound log ratio: `log ((1 + η) * 2 * n * log n + 1) / log n → 1`
  have hlog_up : Tendsto
      (fun n : ℕ => Real.log (2 * (1 + η) * (n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 1) :=
    tendsto_log_const_mul_n_log_div_log (by linarith)
  have hlog_up2 : Tendsto
      (fun n : ℕ => Real.log (4 * (1 + η) * (n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 1) :=
    tendsto_log_const_mul_n_log_div_log (by linarith)
  -- Lower bound log ratio: `log ((1 - η) * n * log n) / log n → 1`
  have hlog_lo : Tendsto
      (fun n : ℕ => Real.log ((1 - η) * (n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 1) :=
    tendsto_log_const_mul_n_log_div_log (by linarith)
  have hev_all :
      ∀ᶠ n : ℕ in atTop,
        3 ≤ n ∧
        (max (X₁ : ℝ) 4 + 2) / (1 - η) ≤ 2 * (n : ℝ) * Real.log (n : ℝ) ∧
        2 / η ≤ 2 * (n : ℝ) * Real.log (n : ℝ) ∧
        Real.log (4 * (1 + η) * (n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ) ≤ 1 + η / 4 ∧
        1 - η / 4 ≤ Real.log ((1 - η) * (n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    have h1 := eventually_ge_atTop 3
    have h2 := hnlog_top.eventually (eventually_ge_atTop ((max (X₁ : ℝ) 4 + 2) / (1 - η)))
    have h3 := hnlog_top.eventually (eventually_ge_atTop (2 / η))
    have h4 := hlog_up2.eventually (Iic_mem_nhds (by linarith : (1 : ℝ) < 1 + η / 4))
    have h5 := hlog_lo.eventually (Ici_mem_nhds (by linarith : 1 - η / 4 < (1 : ℝ)))
    filter_upwards [h1, h2, h3, h4, h5] with n hn1 hn2 hn3 hn4 hn5
    exact ⟨hn1, hn2, hn3, hn4, hn5⟩
  rw [Filter.eventually_atTop] at hev_all
  obtain ⟨N₀, hN₀⟩ := hev_all
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hn3, hn_big, hn_eta, hlog_hi, hlog_lo_b⟩ := hN₀ n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  set M : ℝ := 2 * (n : ℝ) * Real.log (n : ℝ) with hM_def
  have hM_pos : 0 < M := by positivity
  have hM_ge : max (X₁ : ℝ) 4 + 2 ≤ (1 - η) * M := by
    have := mul_le_mul_of_nonneg_left hn_big (show 0 ≤ 1 - η by linarith)
    rwa [mul_div_cancel₀ _ (by linarith : 1 - η ≠ 0)] at this
  have hM_eta : 1 / M ≤ η / 2 := by
    have h1 : 2 ≤ η * M := by
      have := mul_le_mul_of_nonneg_left hn_eta hη_pos.le
      rwa [mul_div_cancel₀ _ hη_pos.ne'] at this
    rw [div_le_div_iff₀ hM_pos two_pos]; linarith
  -- Part 1: Upper bound `ramanujanPrime n ≤ ⌈(1 + η) * M⌉₊`
  have hR_upper : (ramanujanPrime n : ℝ) ≤ (1 + η) * M + 1 := by
    set R_hi : ℕ := ⌈(1 + η) * M⌉₊
    have hbound : isRamanujanPrimeBound n R_hi := by
      intro x hx
      have hRhi_ge : (1 + η) * M ≤ (R_hi : ℝ) := Nat.le_ceil _
      have hRhi_le : (R_hi : ℝ) ≤ (1 + η) * M + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      have hxR : (R_hi : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      have hx_ge_X₁ : X₁ ≤ x := by
        have h1 : (X₁ : ℝ) ≤ (x : ℝ) := by
          have := le_max_left (X₁ : ℝ) 4
          nlinarith
        exact_mod_cast h1
      have hx_ge4 : (4 : ℝ) ≤ (x : ℝ) := by
        have := le_max_right (X₁ : ℝ) 4
        nlinarith
      have hRhi_ge_e : Real.exp 1 ≤ (R_hi : ℝ) := by
        have := le_max_right (X₁ : ℝ) 4
        nlinarith [Real.exp_one_lt_d9]
      have hx_ge_e : Real.exp 1 ≤ (x : ℝ) := hRhi_ge_e.trans hxR
      have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
      have hden_x : 0 < (x : ℝ) / (2 * Real.log (x : ℝ)) := by positivity
      have hdyad_lo := (hX₁ x hx_ge_X₁).1
      have hcnt_lo : (1 - η / 4) * ((x : ℝ) / (2 * Real.log (x : ℝ))) <
          ((Nat.primeCounting x - Nat.primeCounting (x / 2) : ℕ) : ℝ) :=
        (lt_div_iff₀ hden_x).mp hdyad_lo
      have hmono := monotoneOn_div_two_log hRhi_ge_e hx_ge_e hxR
      -- Bound `log R_hi ≤ (1 + η / 4) * log n`
      have hRhi_le_2 : (R_hi : ℝ) ≤ 2 * (1 + η) * M := by
        have : 1 ≤ (1 + η) * M := by
          have := le_max_right (X₁ : ℝ) 4; nlinarith
        linarith
      have hlogR_le : Real.log (R_hi : ℝ) ≤ (1 + η / 4) * Real.log (n : ℝ) := by
        have h1 : Real.log (R_hi : ℝ) ≤ Real.log (4 * (1 + η) * (n : ℝ) * Real.log (n : ℝ)) := by
          refine Real.log_le_log (by linarith [Real.exp_pos 1]) ?_
          have : 2 * (1 + η) * M = 4 * (1 + η) * (n : ℝ) * Real.log (n : ℝ) := by dsimp only [M]; ring
          linarith
        have h2 := (div_le_iff₀ hlogn_pos).mp hlog_hi
        linarith
      have hlogR_pos : 0 < Real.log (R_hi : ℝ) :=
        Real.log_pos (by linarith [Real.exp_one_lt_d9, Real.exp_one_gt_d9])
      have hfrac : (n : ℝ) ≤ (1 - η / 4) * ((R_hi : ℝ) / (2 * Real.log (R_hi : ℝ))) := by
        have h1 : (1 + η) * M / (2 * ((1 + η / 4) * Real.log (n : ℝ))) ≤
            (R_hi : ℝ) / (2 * Real.log (R_hi : ℝ)) := by
          refine div_le_div₀ (by positivity) hRhi_ge (by positivity) (by linarith)
        have hsimp : (1 + η) * M / (2 * ((1 + η / 4) * Real.log (n : ℝ))) =
            ((1 + η) / (1 + η / 4)) * (n : ℝ) := by
          dsimp only [M]; field_simp [hlogn_pos.ne', (show (0 : ℝ) < 1 + η / 4 by linarith).ne']
        rw [hsimp] at h1
        have hconst : (1 : ℝ) ≤ (1 - η / 4) * ((1 + η) / (1 + η / 4)) := by
          rw [show (1 - η / 4) * ((1 + η) / (1 + η / 4)) = ((1 - η / 4) * (1 + η)) / (1 + η / 4) by ring,
            one_le_div (by linarith)]
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - η / 4 by linarith)
        have hmul2 : (n : ℝ) ≤ (1 - η / 4) * (((1 + η) / (1 + η / 4)) * (n : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hconst hn_pos.le
          linarith
        linarith
      have hcast : (n : ℝ) ≤ ((Nat.primeCounting x - Nat.primeCounting (x / 2) : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 1 - η / 4 by linarith)
        linarith
      exact_mod_cast hcast
    have hle : ramanujanPrime n ≤ R_hi := Nat.sInf_le hbound
    have hleR : (ramanujanPrime n : ℝ) ≤ (R_hi : ℝ) := by exact_mod_cast hle
    exact hleR.trans (Nat.ceil_lt_add_one (by positivity)).le
  -- Part 2: Lower bound `(1 - η) * M - 1 < ramanujanPrime n`
  have hR_lower : (1 - η) * M - 1 ≤ (ramanujanPrime n : ℝ) := by
    have h1mη_pos : 0 < 1 - η := by linarith
    have h1mη4_pos : 0 < 1 - η / 4 := by linarith
    set x₀ : ℕ := ⌊(1 - η) * M⌋₊
    have hx₀_le : (x₀ : ℝ) ≤ (1 - η) * M := Nat.floor_le (by nlinarith)
    have hx₀_gt : (1 - η) * M - 1 < (x₀ : ℝ) := by linarith [Nat.lt_floor_add_one ((1 - η) * M)]
    have hx₀_ge_X₁ : X₁ ≤ x₀ := by
      have h1 : (X₁ : ℝ) ≤ (x₀ : ℝ) := by
        have := le_max_left (X₁ : ℝ) 4; linarith
      exact_mod_cast h1
    have hx₀_ge4 : (4 : ℝ) ≤ (x₀ : ℝ) := by
      have := le_max_right (X₁ : ℝ) 4; linarith
    have hx₀_ge_half : (1 - η) * (n : ℝ) * Real.log (n : ℝ) ≤ (x₀ : ℝ) := by
      have h1 : 1 ≤ (1 - η) * (n : ℝ) * Real.log (n : ℝ) := by
        have := le_max_right (X₁ : ℝ) 4; dsimp only [M] at hM_ge; linarith
      dsimp only [M] at hx₀_gt
      linarith
    have hlogx₀_ge : (1 - η / 4) * Real.log (n : ℝ) ≤ Real.log (x₀ : ℝ) := by
      have h1 : Real.log ((1 - η) * (n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (x₀ : ℝ) :=
        Real.log_le_log (by positivity) hx₀_ge_half
      have h2 := (le_div_iff₀ hlogn_pos).mp hlog_lo_b
      linarith
    have hlogx₀_pos : 0 < Real.log (x₀ : ℝ) := Real.log_pos (by linarith)
    have hden_x₀ : 0 < (x₀ : ℝ) / (2 * Real.log (x₀ : ℝ)) := by positivity
    have hdyad_hi := (hX₁ x₀ hx₀_ge_X₁).2
    have hcnt_hi : ((Nat.primeCounting x₀ - Nat.primeCounting (x₀ / 2) : ℕ) : ℝ) <
        (1 + η / 4) * ((x₀ : ℝ) / (2 * Real.log (x₀ : ℝ))) :=
      (div_lt_iff₀ hden_x₀).mp hdyad_hi
    have hfrac_le : (1 + η / 4) * ((x₀ : ℝ) / (2 * Real.log (x₀ : ℝ))) ≤ (n : ℝ) := by
      have h1 : (x₀ : ℝ) / (2 * Real.log (x₀ : ℝ)) ≤
          ((1 - η) * M) / (2 * ((1 - η / 4) * Real.log (n : ℝ))) :=
        div_le_div₀ (by positivity) hx₀_le (by positivity) (by linarith)
      have hsimp : ((1 - η) * M) / (2 * ((1 - η / 4) * Real.log (n : ℝ))) =
          ((1 - η) / (1 - η / 4)) * (n : ℝ) := by
        dsimp only [M]; field_simp [hlogn_pos.ne', (show (0 : ℝ) < 1 - η / 4 by linarith).ne']
      rw [hsimp] at h1
      have hconst : (1 + η / 4) * ((1 - η) / (1 - η / 4)) ≤ 1 := by
        rw [show (1 + η / 4) * ((1 - η) / (1 - η / 4)) = ((1 + η / 4) * (1 - η)) / (1 - η / 4) by ring,
          div_le_one (by linarith)]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + η / 4 by linarith)
      have hmul2 : (1 + η / 4) * (((1 - η) / (1 - η / 4)) * (n : ℝ)) ≤ (n : ℝ) := by
        have := mul_le_mul_of_nonneg_right hconst hn_pos.le
        linarith
      linarith
    have hlt_n : Nat.primeCounting x₀ - Nat.primeCounting (x₀ / 2) < n := by
      have : ((Nat.primeCounting x₀ - Nat.primeCounting (x₀ / 2) : ℕ) : ℝ) < (n : ℝ) :=
        lt_of_lt_of_le hcnt_hi hfrac_le
      exact_mod_cast this
    have hx₀_lt_R : x₀ < ramanujanPrime n := by
      by_contra hle
      push Not at hle
      have := isRamanujanPrimeBound_ramanujanPrime n x₀ hle
      omega
    have hx₀_lt_RR : (x₀ : ℝ) < (ramanujanPrime n : ℝ) := by exact_mod_cast hx₀_lt_R
    linarith
  -- Combine upper and lower bounds to get `dist (R_n / M) 1 < ε`
  rw [Real.dist_eq, abs_lt]
  have hup_div : (ramanujanPrime n : ℝ) / M ≤ 1 + η + 1 / M := by
    rw [div_le_iff₀ hM_pos]
    have hmul : (1 + η + 1 / M) * M = (1 + η) * M + 1 := by field_simp [hM_pos.ne']
    linarith
  have hlo_div : 1 - η - 1 / M ≤ (ramanujanPrime n : ℝ) / M := by
    rw [le_div_iff₀ hM_pos]
    have hmul : (1 - η - 1 / M) * M = (1 - η) * M - 1 := by field_simp [hM_pos.ne']
    linarith
  constructor <;> linarith

/-! ## Section 4: Unconditional `n`-th Prime in Arithmetic Progressions & Equidistribution Ratio -/

/-- The `n`-th prime (`0`-indexed) in the arithmetic progression `p ≡ a [MOD q]`. -/
noncomputable def nthPrimeAP (q a n : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ p ≡ a [MOD q]) n

/-- Exact residue-class prime count at the `n`-th prime in `a mod q`:
`primeCountAP q a (nthPrimeAP q a n) = n + 1`. -/
theorem primeCountAP_nthPrimeAP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) :
    Stage2DirichletAP.primeCountAP q a (nthPrimeAP q a n : ℝ) = n + 1 := by
  have hinf := Stage2DirichletAP.dirichlet_infinite_primes_modEq (NeZero.ne q) hcop
  have hmem : (nthPrimeAP q a n).Prime ∧ nthPrimeAP q a n ≡ a [MOD q] :=
    Nat.nth_mem_of_infinite hinf n
  unfold Stage2DirichletAP.primeCountAP
  rw [Nat.floor_natCast, ← Nat.count_eq_card_filter_range, Nat.count_succ, if_pos hmem]
  exact congrArg (· + 1) (Nat.count_nth_of_infinite hinf n)

/-- **UNCONDITIONAL `n`-TH PRIME IN ARITHMETIC PROGRESSIONS (`p_n(q, a) ~ φ(q) n log n`, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
`Tendsto (fun n : ℕ => (nthPrimeAP q a n : ℝ) / ((q.totient : ℝ) * (n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1)`. -/
theorem nth_prime_ap_asymptotic {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto
      (fun n : ℕ =>
        (nthPrimeAP q a n : ℝ) / ((q.totient : ℝ) * (n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 1) := by
  have hinf := Stage2DirichletAP.dirichlet_infinite_primes_modEq (NeZero.ne q) hcop
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hnth_top : Tendsto (fun n : ℕ => nthPrimeAP q a n) atTop atTop :=
    (Nat.nth_strictMono hinf).tendsto_atTop
  -- Step 1: `φ(q) * n * log (p_n(q, a)) / p_n(q, a) → 1`
  have hstep1 :
      Tendsto
        (fun n : ℕ =>
          ((q.totient : ℝ) * (n : ℝ) * Real.log (nthPrimeAP q a n : ℝ)) / (nthPrimeAP q a n : ℝ))
        atTop (𝓝 1) := by
    have hpnt := (Stage7PNTInAP.pnt_primeCountAP_asymp hcop).comp hnth_top
    have h1 : Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ)) /
            ((nthPrimeAP q a n : ℝ) / ((q.totient : ℝ) * Real.log (nthPrimeAP q a n : ℝ))))
        atTop (𝓝 1) := by
      refine hpnt.congr fun n => ?_
      simp only [Function.comp_apply, primeCountAP_nthPrimeAP hcop]
    have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
      have hinv : Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
          (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr fun n => by
            simp [one_div]
        simpa using tendsto_const_nhds.add h0
      have hinv' := hinv.inv₀ one_ne_zero
      rw [inv_one] at hinv'
      refine hinv'.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      push_cast; field_simp [hn0.ne']
    have hmul := hratio.mul h1
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hp_ge2 : 2 ≤ nthPrimeAP q a n := (Nat.nth_mem_of_infinite hinf n).1.two_le
    have hp0 : (0 : ℝ) < (nthPrimeAP q a n : ℝ) := by exact_mod_cast (by omega : 0 < nthPrimeAP q a n)
    have hlogp0 : (0 : ℝ) < Real.log (nthPrimeAP q a n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < nthPrimeAP q a n))
    field_simp [hn1, hp0.ne', hlogp0.ne', hphi_pos.ne']
  -- Step 2: `log (p_n(q, a)) / log n → 1`
  have hstep2 :
      Tendsto (fun n : ℕ => Real.log (nthPrimeAP q a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 1) := by
    have hlog_ratio :
        Tendsto
          (fun n : ℕ =>
            Real.log (((q.totient : ℝ) * (n : ℝ) * Real.log (nthPrimeAP q a n : ℝ)) /
              (nthPrimeAP q a n : ℝ)))
          atTop (𝓝 0) := by
      have hc : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
      exact (by simpa [Real.log_one] using hc.tendsto.comp hstep1 :
        Tendsto (Real.log ∘ _) atTop (𝓝 0)).congr fun _ => rfl
    have hlogp_top : Tendsto (fun n : ℕ => Real.log (nthPrimeAP q a n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hnth_top)
    have hdiv_logp :
        Tendsto
          (fun n : ℕ =>
            Real.log (((q.totient : ℝ) * (n : ℝ) * Real.log (nthPrimeAP q a n : ℝ)) /
              (nthPrimeAP q a n : ℝ)) / Real.log (nthPrimeAP q a n : ℝ))
          atTop (𝓝 0) := by
      have h := hlog_ratio.mul (tendsto_inv_atTop_zero.comp hlogp_top)
      rw [mul_zero] at h
      exact h.congr fun n => by simp [div_eq_mul_inv]
    have hlogphi_div :
        Tendsto (fun n : ℕ => Real.log (q.totient : ℝ) / Real.log (nthPrimeAP q a n : ℝ))
          atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.comp hlogp_top).const_mul (Real.log (q.totient : ℝ))
      rw [mul_zero] at h
      exact h.congr fun n => by simp [div_eq_mul_inv]
    have hloglogp :
        Tendsto
          (fun n : ℕ => Real.log (Real.log (nthPrimeAP q a n : ℝ)) / Real.log (nthPrimeAP q a n : ℝ))
          atTop (𝓝 0) :=
      tendsto_log_div_self.comp hlogp_top
    have hinv_lim :
        Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (nthPrimeAP q a n : ℝ)) atTop (𝓝 1) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlogphi_div).sub hloglogp |>.add hdiv_logp
      rw [sub_zero, sub_zero, add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hp_ge2 : 2 ≤ nthPrimeAP q a n := (Nat.nth_mem_of_infinite hinf n).1.two_le
      have hp0 : (0 : ℝ) < (nthPrimeAP q a n : ℝ) := by exact_mod_cast (by omega : 0 < nthPrimeAP q a n)
      have hlogp0 : (0 : ℝ) < Real.log (nthPrimeAP q a n : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < nthPrimeAP q a n))
      rw [Real.log_div (mul_pos (mul_pos hphi_pos hn0) hlogp0).ne' hp0.ne',
        Real.log_mul (mul_pos hphi_pos hn0).ne' hlogp0.ne',
        Real.log_mul hphi_pos.ne' hn0.ne']
      field_simp [hlogp0.ne']
      ring
    have hrec := hinv_lim.inv₀ one_ne_zero
    rw [inv_one] at hrec
    exact hrec.congr fun n => by rw [inv_div]
  -- Step 3: Multiply `p_n / (φ(q) n log p_n)` by `log p_n / log n`
  have h1 :
      Tendsto
        (fun n : ℕ =>
          (nthPrimeAP q a n : ℝ) / ((q.totient : ℝ) * (n : ℝ) * Real.log (nthPrimeAP q a n : ℝ)))
        atTop (𝓝 1) := by
    have h := hstep1.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun n => by rw [inv_div]
  have hmul := h1.mul hstep2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn0 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hp_ge2 : 2 ≤ nthPrimeAP q a n := (Nat.nth_mem_of_infinite hinf n).1.two_le
  have hlogp0 : (0 : ℝ) < Real.log (nthPrimeAP q a n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < nthPrimeAP q a n))
  field_simp [hn0.ne', hlogn0.ne', hlogp0.ne', hphi_pos.ne']

/-- **UNCONDITIONAL EQUIDISTRIBUTION OF PRIMES ACROSS REDUCED RESIDUE CLASSES (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
`Tendsto (fun n : ℕ => (primeCountAP q a n : ℝ) / (Nat.primeCounting n : ℝ)) atTop (𝓝 ((q.totient : ℝ)⁻¹))`. -/
theorem prime_density_in_AP_ratio {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto
      (fun n : ℕ =>
        (Stage2DirichletAP.primeCountAP q a n : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv := (Stage7PNTInAP.pnt_primeCountAP_asymp hcop).div
    Stage6EffectivePNT.pnt_primeCounting_asymp one_ne_zero
  rw [div_one] at hdiv
  have hscaled := hdiv.const_mul (q.totient : ℝ)⁻¹
  rw [mul_one] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn0 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hpc_pos : (0 : ℝ) < (Nat.primeCounting n : ℝ) := by
    have h1 : 1 ≤ Nat.primeCounting 2 := by decide
    have h2 : Nat.primeCounting 2 ≤ Nat.primeCounting n := Nat.monotone_primeCounting hn
    exact_mod_cast (by omega : 0 < Nat.primeCounting n)
  dsimp only [Pi.div_apply]
  field_simp [hn0.ne', hlogn0.ne', hphi_pos.ne', hpc_pos.ne']

/-- Real-variable version of prime equidistribution across reduced residue classes:
`π(x; q, a) / π(⌊x⌋₊) → 1 / φ(q)`. -/
theorem prime_density_in_AP_ratio_real {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto
      (fun x : ℝ =>
        (Stage2DirichletAP.primeCountAP q a x : ℝ) / (Nat.primeCounting ⌊x⌋₊ : ℝ))
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h := (prime_density_in_AP_ratio hcop).comp (tendsto_nat_floor_atTop (α := ℝ))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
  simp only [Function.comp_apply, Stage2DirichletAP.primeCountAP, Nat.floor_natCast]

end RHDirect.Stage8ExplicitPrimeBounds
