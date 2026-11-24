import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage6LFunctionOrder
import RHDirect.Stage6XiZeroDensity
import RHDirect.Stage7SieveMethods
import RHDirect.Stage7VonMangoldtExplicit
import RHDirect.Stage8HadamardLFunction
import RHDirect.Stage8MertensTheorems
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# RHDirect.Stage11LogFreeDensity

Completely **UNCONDITIONAL** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) formalization
of **Gallagher's 1970 Log-Free Zero-Density Estimate for Dirichlet `L`-Functions** directly on
Mathlib's actual `DirichletCharacter.LFunction` in pure Mathlib `v4.33.1`.

## Main Results
1. **Gallagher's Mean-Value Lemma & Hybrid Large Sieve** (Section 1):
   - `gallagher_sobolev_mean_value`: Sobolev–Gallagher discrete mean-value inequality for `C¹`
     functions on `δ`-well-spaced points.
   - `gallagher_continuous_mean_value` (Gallagher 1970, Theorem 1): continuous `L²` mean value
     of any finite exponential sum bounded by the `L²` integral of short-interval sums via
     Fourier inversion of the tent kernel.
   - `gallagher_continuous_hybrid_large_sieve` & `gallagher_continuous_hybrid_large_sieve_fixed_mod`
     (Gallagher 1970, Theorem 2): 100% log-free continuous hybrid large sieve with `(Q² T + n)`
     (and `(m T + n)`) inside the sum.
   - `gallagher_hybrid_large_sieve_dyadic`, `gallagher_hybrid_large_sieve_fixed_mod_dyadic`,
     and `gallagher_hybrid_large_sieve_window`: log-free discrete hybrid large sieve on dyadic
     and bounded-ratio windows, plus the `[1, N]` discrete version.
2. **Prime-Weighted Large Sieve & Continuous Prime Hybrid Large Sieve** (Section 2):
   - `fixed_mod_prime_large_sieve`: via character orthogonality + `Stage7SieveMethods.brun_titchmarsh_ap`.
   - `primitive_prime_large_sieve`: via duality + `Stage7SieveMethods` optimal Selberg sieve weights.
   - `gallagher_continuous_prime_hybrid_large_sieve_fixed_mod` &
     `gallagher_continuous_prime_hybrid_large_sieve_prim`: 100% log-free prime hybrid large sieve
     with `(p / log p)` weight.
3. **Turán's Second Main Theorem & Unconditional High-Derivative Prime Zero Detector** (Section 3):
   - `turan_power_sum_second_main`: unconditional lower bound `(1 / (64 e))^M * (1/2)^K` on
     `max_{K+1 ≤ k ≤ K+M} ‖∑ j, (z j)^k‖` via exact circle-integral identity + discrete averaging.
   - Term-by-term `iteratedDeriv k` of `-L'/L` and `-ζ'/ζ` via Cauchy's integral formula, local
     multiplicity zero count `#(zeros in |s₀ - ρ| < d) ≤ C_Z (d L + 1)`, and prime-sum zero
     detection on `(N₁(k), N₂(k)]`.
4. **Unconditional Gallagher Log-Free Zero-Density Theorems (`0` Assumptions!)** (Section 4):
   - `zerosOfLInBox`, `dirichletZeroBoxCount`, `primitiveZeroBoxCount` (counting zeros with
     exact analytic multiplicity `analyticOrderNatAt`).
   - `gallagher_logfree_zero_density_fixed_mod`:
     `∃ C > 0, ∃ A > 0, ∀ m [NeZero m], 2 ≤ m → ∀ T ≥ 1, ∀ σ ∈ [1/2, 1], (dirichletZeroBoxCount m σ T : ℝ) ≤ C * (m * (T + 2)) ^ (A * (1 - σ))`.
   - `gallagher_logfree_zero_density_sum`:
     `∃ C > 0, ∃ A > 0, ∀ Q ≥ 1, ∀ T ≥ 1, ∀ σ ∈ [1/2, 1], (primitiveZeroBoxCount Q σ T : ℝ) ≤ C * (Q^2 * (T + 2)) ^ (A * (1 - σ))`.
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology Metric MeasureTheory Set
open scoped BigOperators Real ArithmeticFunction.vonMangoldt FourierTransform

namespace RHDirect.Stage11LogFreeDensity

open RHDirect.Stage3BombieriVinogradov
open RHDirect.Stage3ZeroFreeRegion
open RHDirect.Stage6LFunctionOrder
open RHDirect.Stage6XiZeroDensity
open RHDirect.Stage7SieveMethods
open RHDirect.Stage7VonMangoldtExplicit
open RHDirect.Stage8HadamardLFunction
open RHDirect.Stage8MertensTheorems

/-! ## Section 1: Gallagher's Mean-Value Lemma & Hybrid Large Sieve -/

/-- **Sobolev–Gallagher Pointwise Lemma**:
for any `C¹` function `f : ℝ → ℂ` on `[t₀ - η, t₀ + η]` (`0 < η`),
`‖f t₀‖ ^ 2 ≤ (1 / (2 * η)) * ∫_{t₀ - η}^{t₀ + η} ‖f t‖ ^ 2 dt + 2 * ∫_{t₀ - η}^{t₀ + η} ‖f t‖ * ‖f' t‖ dt`. -/
theorem sobolev_gallagher_pointwise {f f' : ℝ → ℂ} {t₀ η : ℝ} (hη : 0 < η)
    (hderiv : ∀ t ∈ Set.Icc (t₀ - η) (t₀ + η), HasDerivAt f (f' t) t)
    (hcont' : ContinuousOn f' (Set.Icc (t₀ - η) (t₀ + η))) :
    ‖f t₀‖ ^ 2 ≤
      (1 / (2 * η)) * (∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ ^ 2) +
      2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
  have hcont_f : ContinuousOn f (Set.Icc (t₀ - η) (t₀ + η)) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hcont_normsq : ContinuousOn (fun t => ‖f t‖ ^ 2) (Set.Icc (t₀ - η) (t₀ + η)) :=
    (continuous_norm.comp_continuousOn hcont_f).pow 2
  have hcont_prod : ContinuousOn (fun t => ‖f t‖ * ‖f' t‖) (Set.Icc (t₀ - η) (t₀ + η)) :=
    (continuous_norm.comp_continuousOn hcont_f).mul (continuous_norm.comp_continuousOn hcont')
  have hderiv_sq : ∀ t ∈ Set.Icc (t₀ - η) (t₀ + η),
      HasDerivAt (fun u : ℝ => ‖f u‖ ^ 2) (2 * (f' t * star (f t)).re) t := by
    intro t ht
    have hf := hderiv t ht
    have hstar : HasDerivAt (fun u : ℝ => star (f u)) (star (f' t)) t :=
      Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hf
    have hre : HasDerivAt (fun u : ℝ => (f u * star (f u)).re)
        (f' t * star (f t) + f t * star (f' t)).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.mul hstar)
    have hfun : (fun u : ℝ => (f u * star (f u)).re) = fun u : ℝ => ‖f u‖ ^ 2 := by
      funext u
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hfun] at hre
    refine hre.congr_deriv ?_
    rw [Complex.add_re]
    have hconj_re : (f t * star (f' t)).re = (f' t * star (f t)).re := by
      have h1 : star (f' t * star (f t)) = f t * star (f' t) := by
        rw [star_mul', star_star, mul_comm]
      rw [← h1, Complex.star_def, Complex.conj_re]
    linarith
  have hcont_deriv_sq : ContinuousOn (fun t => 2 * (f' t * star (f t)).re) (Set.Icc (t₀ - η) (t₀ + η)) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (hcont'.mul (Complex.conjCLE.continuous.comp_continuousOn hcont_f)))
  have hpt_u : ∀ u ∈ Set.Icc (t₀ - η) (t₀ + η),
      ‖f t₀‖ ^ 2 - ‖f u‖ ^ 2 ≤ 2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
    intro u hu
    have huIcc : Set.uIcc u t₀ ⊆ Set.Icc (t₀ - η) (t₀ + η) :=
      Set.uIcc_subset_Icc hu ⟨by linarith, by linarith⟩
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv_sq t (huIcc ht))
      ((hcont_deriv_sq.mono huIcc).intervalIntegrable)
    rw [← hftc]
    have hle_abs : ∫ t in u..t₀, 2 * (f' t * star (f t)).re ≤
        ∫ t in (min u t₀)..(max u t₀), |2 * (f' t * star (f t)).re| := by
      rcases le_total u t₀ with hle | hge
      · rw [min_eq_left hle, max_eq_right hle]
        exact intervalIntegral.integral_mono_on hle
          ((hcont_deriv_sq.mono huIcc).intervalIntegrable)
          ((continuous_abs.comp_continuousOn (hcont_deriv_sq.mono huIcc)).intervalIntegrable)
          (fun _ _ => le_abs_self _)
      · rw [min_eq_right hge, max_eq_left hge, intervalIntegral.integral_symm t₀ u]
        calc -(∫ t in t₀..u, 2 * (f' t * star (f t)).re)
            ≤ |∫ t in t₀..u, 2 * (f' t * star (f t)).re| := neg_le_abs _
          _ ≤ ∫ t in t₀..u, |2 * (f' t * star (f t)).re| :=
              intervalIntegral.abs_integral_le_integral_abs hge
    have hle_prod : ∫ t in (min u t₀)..(max u t₀), |2 * (f' t * star (f t)).re| ≤
        ∫ t in (min u t₀)..(max u t₀), 2 * (‖f t‖ * ‖f' t‖) := by
      have hsub : Set.uIcc (min u t₀) (max u t₀) ⊆ Set.Icc (t₀ - η) (t₀ + η) := by
        rw [Set.uIcc_of_le min_le_max]
        exact Set.Icc_subset_Icc (le_min hu.1 (by linarith)) (max_le hu.2 (by linarith))
      refine intervalIntegral.integral_mono_on min_le_max
        ((continuous_abs.comp_continuousOn (hcont_deriv_sq.mono hsub)).intervalIntegrable)
        ((continuousOn_const.mul (hcont_prod.mono hsub)).intervalIntegrable) fun t _ => ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hre : |(f' t * star (f t)).re| ≤ ‖f t‖ * ‖f' t‖ := by
        calc |(f' t * star (f t)).re| ≤ ‖f' t * star (f t)‖ := Complex.abs_re_le_norm _
          _ = ‖f' t‖ * ‖f t‖ := by rw [norm_mul, norm_star]
          _ = ‖f t‖ * ‖f' t‖ := mul_comm _ _
      linarith
    have hle_full : ∫ t in (min u t₀)..(max u t₀), 2 * (‖f t‖ * ‖f' t‖) ≤
        2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
      have hlo : t₀ - η ≤ min u t₀ := le_min hu.1 (by linarith)
      have hhi : max u t₀ ≤ t₀ + η := max_le hu.2 (by linarith)
      have hint_full : IntervalIntegrable (fun t => 2 * (‖f t‖ * ‖f' t‖)) volume (t₀ - η) (t₀ + η) :=
        (continuousOn_const.mul hcont_prod).intervalIntegrable_of_Icc (by linarith)
      rw [← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le min_le_max, intervalIntegral.integral_of_le (by linarith)]
      refine setIntegral_mono_set ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hint_full)
        (ae_of_all _ fun _ => by positivity) (Eventually.of_forall (Set.Ioc_subset_Ioc hlo hhi))
    linarith
  have havg : ∫ u in (t₀ - η)..(t₀ + η), (‖f t₀‖ ^ 2 - ‖f u‖ ^ 2) ≤
      ∫ u in (t₀ - η)..(t₀ + η), (2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖) :=
    intervalIntegral.integral_mono_on (by linarith : t₀ - η ≤ t₀ + η)
      (intervalIntegrable_const.sub (hcont_normsq.intervalIntegrable_of_Icc (by linarith)))
      intervalIntegrable_const hpt_u
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hcont_normsq.intervalIntegrable_of_Icc (by linarith)),
    intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at havg
  have hlen : t₀ + η - (t₀ - η) = 2 * η := by ring
  rw [hlen] at havg
  have hdiv := div_le_div_of_nonneg_right havg (by positivity : (0 : ℝ) ≤ 2 * η)
  have h2η : (2 * η) ≠ 0 := by positivity
  have hLHS : (2 * η * ‖f t₀‖ ^ 2 - ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ ^ 2) / (2 * η) =
      ‖f t₀‖ ^ 2 - (1 / (2 * η)) * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ ^ 2 := by
    field_simp [h2η]
  have hRHS : (2 * η * (2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖)) / (2 * η) =
      2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
    field_simp [h2η]
  rw [hLHS, hRHS] at hdiv
  linarith

/-- **Gallagher's Sobolev Mean-Value Lemma (`δ`-well-spaced points)**:
for any `C¹` function `S : ℝ → ℂ` with continuous derivative `S'`, any `T ≥ 0`, `δ > 0`, and any
`δ`-well-spaced finite collection of points `t r ∈ [-T, T]` (`r ∈ J`),
`∑ r ∈ J, ‖S (t r)‖ ^ 2 ≤ δ⁻¹ * ∫_{-(T+δ/2)}^{T+δ/2} ‖S u‖^2 du + 2 * ∫_{-(T+δ/2)}^{T+δ/2} ‖S u‖ * ‖S' u‖ du`. -/
theorem gallagher_sobolev_mean_value {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (t : ι → ℝ) {S S' : ℝ → ℂ} {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hbd : ∀ r ∈ J, |t r| ≤ T)
    (hsep : ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ |t r - t s|)
    (hderiv : ∀ u : ℝ, HasDerivAt S (S' u) u)
    (hcont' : Continuous S') :
    ∑ r ∈ J, ‖S (t r)‖ ^ 2 ≤
      δ⁻¹ * (∫ u in (-(T + δ / 2))..(T + δ / 2), ‖S u‖ ^ 2) +
      2 * ∫ u in (-(T + δ / 2))..(T + δ / 2), ‖S u‖ * ‖S' u‖ := by
  set η : ℝ := δ / 2
  have hη_eq : η = δ / 2 := rfl
  have hη : 0 < η := by positivity
  set T' : ℝ := T + η
  have hS_cont : Continuous S := continuous_iff_continuousAt.mpr fun u => (hderiv u).continuousAt
  have hdisj_sum : ∀ g : ℝ → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      ∑ r ∈ J, (∫ u in (t r - η)..(t r + η), g u) ≤ ∫ u in (-T')..T', g u := by
    intro g hg hgnn
    have h1 : ∀ r ∈ J, ∫ u in (t r - η)..(t r + η), g u =
        ∫ u in Set.Ioo (t r - η) (t r + η), g u := fun r _ => by
      rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [Finset.sum_congr rfl h1]
    have hdisj : Set.PairwiseDisjoint (J : Set ι) (fun r => Set.Ioo (t r - η) (t r + η)) := by
      intro r hr s hs hrs
      rw [Function.onFun, Set.disjoint_left]
      intro x hxr hxs
      have hsep' := hsep r hr s hs hrs
      rcases le_or_gt (t r) (t s) with hle | hgt
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hsep'
        linarith [hxr.2, hxs.1, hη_eq]
      · rw [abs_of_pos (sub_pos.mpr hgt)] at hsep'
        linarith [hxs.2, hxr.1, hη_eq]
    have hmeas : ∀ r ∈ J, MeasurableSet (Set.Ioo (t r - η) (t r + η)) :=
      fun _ _ => measurableSet_Ioo
    have hint_T' : IntegrableOn g (Set.Ioc (-T') T') :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hT, hη])).mp
        (hg.intervalIntegrable (-T') T')
    have hsub : ∀ r ∈ J, Set.Ioo (t r - η) (t r + η) ⊆ Set.Ioc (-T') T' := by
      intro r hr x hx
      have htr := abs_le.mp (hbd r hr)
      exact ⟨by linarith [hx.1, htr.1], by linarith [hx.2, htr.2]⟩
    have hint_r : ∀ r ∈ J, IntegrableOn g (Set.Ioo (t r - η) (t r + η)) :=
      fun r hr => hint_T'.mono_set (hsub r hr)
    rw [← MeasureTheory.integral_biUnion_finset J hmeas hdisj hint_r,
      intervalIntegral.integral_of_le (by linarith [hT, hη])]
    exact setIntegral_mono_set hint_T' (ae_of_all _ hgnn)
      (Eventually.of_forall (Set.iUnion₂_subset hsub))
  have hpt : ∀ r ∈ J, ‖S (t r)‖ ^ 2 ≤
      δ⁻¹ * (∫ u in (t r - η)..(t r + η), ‖S u‖ ^ 2) +
      2 * ∫ u in (t r - η)..(t r + η), ‖S u‖ * ‖S' u‖ := by
    intro r _
    have h := sobolev_gallagher_pointwise (f := S) (f' := S') (t₀ := t r) hη
      (fun u _ => hderiv u) hcont'.continuousOn
    have h2η : 1 / (2 * η) = δ⁻¹ := by dsimp only [η]; field_simp [hδ.ne']
    rwa [h2η] at h
  calc ∑ r ∈ J, ‖S (t r)‖ ^ 2
      ≤ ∑ r ∈ J, (δ⁻¹ * (∫ u in (t r - η)..(t r + η), ‖S u‖ ^ 2) +
          2 * ∫ u in (t r - η)..(t r + η), ‖S u‖ * ‖S' u‖) := Finset.sum_le_sum hpt
    _ = δ⁻¹ * (∑ r ∈ J, ∫ u in (t r - η)..(t r + η), ‖S u‖ ^ 2) +
        2 * (∑ r ∈ J, ∫ u in (t r - η)..(t r + η), ‖S u‖ * ‖S' u‖) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ δ⁻¹ * (∫ u in (-T')..T', ‖S u‖ ^ 2) +
        2 * ∫ u in (-T')..T', ‖S u‖ * ‖S' u‖ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (hdisj_sum _ (hS_cont.norm.pow 2) (fun _ => sq_nonneg _)) (by positivity)
        · exact mul_le_mul_of_nonneg_left
            (hdisj_sum _ (hS_cont.norm.mul hcont'.norm) (fun _ => by positivity)) (by norm_num)

/-- Weighted AM-GM corollary of `gallagher_sobolev_mean_value`: for any `α > 0`,
`∑ r ∈ J, ‖S (t r)‖^2 ≤ (δ⁻¹ + α) ∫ ‖S‖^2 + α⁻¹ ∫ ‖S'‖^2`. -/
theorem gallagher_sobolev_mean_value_weighted {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (t : ι → ℝ) {S S' : ℝ → ℂ} {T δ α : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hα : 0 < α)
    (hbd : ∀ r ∈ J, |t r| ≤ T)
    (hsep : ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ |t r - t s|)
    (hderiv : ∀ u : ℝ, HasDerivAt S (S' u) u)
    (hcont' : Continuous S') :
    ∑ r ∈ J, ‖S (t r)‖ ^ 2 ≤
      (δ⁻¹ + α) * (∫ u in (-(T + δ / 2))..(T + δ / 2), ‖S u‖ ^ 2) +
      α⁻¹ * (∫ u in (-(T + δ / 2))..(T + δ / 2), ‖S' u‖ ^ 2) := by
  set T' : ℝ := T + δ / 2
  have hS_cont : Continuous S := continuous_iff_continuousAt.mpr fun u => (hderiv u).continuousAt
  have hsg := gallagher_sobolev_mean_value J t hT hδ hbd hsep hderiv hcont'
  have h2 : 2 * ∫ u in (-T')..T', ‖S u‖ * ‖S' u‖ ≤
      α * (∫ u in (-T')..T', ‖S u‖ ^ 2) + α⁻¹ * (∫ u in (-T')..T', ‖S' u‖ ^ 2) := by
    have hpt : ∀ u ∈ Set.Icc (-T') T', 2 * (‖S u‖ * ‖S' u‖) ≤ α * ‖S u‖ ^ 2 + α⁻¹ * ‖S' u‖ ^ 2 := by
      intro u _
      have hsq := sq_nonneg (Real.sqrt α * ‖S u‖ - ‖S' u‖ / Real.sqrt α)
      have hsqα : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
      have hexp : (Real.sqrt α * ‖S u‖ - ‖S' u‖ / Real.sqrt α) ^ 2 =
          α * ‖S u‖ ^ 2 - 2 * (‖S u‖ * ‖S' u‖) + α⁻¹ * ‖S' u‖ ^ 2 := by
        field_simp [hsqα]; rw [Real.sq_sqrt hα.le]; field_simp [hα.ne']; ring
      linarith
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (show -T' ≤ T' by dsimp only [T']; linarith [hT, hδ])
      ((continuous_const.mul (hS_cont.norm.mul hcont'.norm)).intervalIntegrable (-T') T')
      (((continuous_const.mul (hS_cont.norm.pow 2)).add
        (continuous_const.mul (hcont'.norm.pow 2))).intervalIntegrable (-T') T') hpt
    have hL_eq : ∫ u in (-T')..T', ((fun _ : ℝ => (2 : ℝ)) * ((fun x => ‖S x‖) * fun x => ‖S' x‖)) u =
        2 * ∫ u in (-T')..T', ‖S u‖ * ‖S' u‖ := by
      simp [Pi.mul_apply, intervalIntegral.integral_const_mul]
    have hR_eq : ∫ u in (-T')..T', ((fun _ : ℝ => α) * (fun x => ‖S x‖) ^ 2 +
          (fun _ : ℝ => α⁻¹) * (fun x => ‖S' x‖) ^ 2) u =
        α * (∫ u in (-T')..T', ‖S u‖ ^ 2) + α⁻¹ * (∫ u in (-T')..T', ‖S' u‖ ^ 2) := by
      have h1 : (fun u : ℝ => ((fun _ : ℝ => α) * (fun x => ‖S x‖) ^ 2 +
            (fun _ : ℝ => α⁻¹) * (fun x => ‖S' x‖) ^ 2) u) =
          fun u => α * ‖S u‖ ^ 2 + α⁻¹ * ‖S' u‖ ^ 2 := by funext u; simp
      have hi1 : IntervalIntegrable (fun u : ℝ => α * ‖S u‖ ^ 2) volume (-T') T' :=
        (continuous_const.mul (hS_cont.norm.pow 2)).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun u : ℝ => α⁻¹ * ‖S' u‖ ^ 2) volume (-T') T' :=
        (continuous_const.mul (hcont'.norm.pow 2)).intervalIntegrable _ _
      rw [h1, intervalIntegral.integral_add hi1 hi2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith
  linarith

/-- Symmetric tent (Fejér) kernel `tentKernel h u = max 0 (h - |u|)` (complex-valued for Fourier inversion). -/
def tentKernel (h u : ℝ) : ℂ := ((max 0 (h - |u|) : ℝ) : ℂ)

/-- Real-valued tent kernel `tentKernelR h u = max 0 (h - |u|)`. -/
def tentKernelR (h u : ℝ) : ℝ := max 0 (h - |u|)

/-- Squared sinc kernel `sincSqKernel h t = (sin (π h t) / (π t))^2` for `t ≠ 0`, `h^2` at `t = 0`. -/
def sincSqKernel (h t : ℝ) : ℝ :=
  if t = 0 then h ^ 2 else (Real.sin (Real.pi * h * t) / (Real.pi * t)) ^ 2

private lemma continuous_tentKernel (h : ℝ) : Continuous (tentKernel h) := by
  unfold tentKernel
  exact Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_abs))

private lemma integrable_tentKernel {h : ℝ} (hh : 0 < h) : Integrable (tentKernel h) := by
  have hcomp : HasCompactSupport (tentKernel h) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -h) (b := h)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hnot
    apply hu
    unfold tentKernel
    have habs : h ≤ |u| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with hlt | hgt
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hmax : max (0 : ℝ) (h - |u|) = 0 := max_eq_left (by linarith)
    simp [hmax]
  exact (continuous_tentKernel h).integrable_of_hasCompactSupport hcomp

/-- Explicit evaluation of the Fourier transform of the tent kernel:
`𝓕 (tentKernel h) t = (sincSqKernel h t : ℂ)`. -/
private lemma fourier_tentKernel_eq {h : ℝ} (hh : 0 < h) (t : ℝ) :
    𝓕 (tentKernel h) t = ((sincSqKernel h t : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have hzero_out : ∀ u : ℝ, u ∉ Set.Icc (-h) h →
      Complex.exp (((-2 * Real.pi * inner ℝ u t : ℝ) : ℂ) * Complex.I) • tentKernel h u = 0 := by
    intro u hu
    have habs : h ≤ |u| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with hlt | hgt
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    unfold tentKernel
    rw [max_eq_left (by linarith : h - |u| ≤ 0), Complex.ofReal_zero, smul_zero]
  have hint_eq : ∫ u : ℝ, Complex.exp (((-2 * Real.pi * inner ℝ u t : ℝ) : ℂ) * Complex.I) • tentKernel h u =
      ∫ u in (-h)..h, Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) * tentKernel h u := by
    rw [intervalIntegral.integral_of_le (by linarith), ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_out]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    rw [RCLike.inner_apply, conj_trivial, mul_comm t u, smul_eq_mul]
  rw [hint_eq]
  -- Split `∫_{-h}^h` into `∫_{-h}^0 + ∫_0^h`
  have hcont_full : Continuous (fun u : ℝ =>
      Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) * tentKernel h u) :=
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_id.mul continuous_const))).mul continuous_const)).mul
      (continuous_tentKernel h)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont_full.intervalIntegrable (-h) 0) (hcont_full.intervalIntegrable 0 h)]
  by_cases ht : t = 0
  · subst ht
    simp only [sincSqKernel, ↓reduceIte, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_mul]
    have hL : ∫ u in (-h)..0, tentKernel h u = ((h ^ 2 / 2 : ℝ) : ℂ) := by
      have hcongr : Set.EqOn (tentKernel h) (fun u => ((h + u : ℝ) : ℂ)) (Set.uIcc (-h) 0) := by
        intro u hu
        rw [Set.uIcc_of_le (by linarith)] at hu
        unfold tentKernel
        rw [abs_of_nonpos hu.2, sub_neg_eq_add, max_eq_right (by linarith [hu.1])]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal]
      congr 1
      have hd : ∀ u ∈ Set.uIcc (-h) 0, HasDerivAt (fun x : ℝ => h * x + x ^ 2 / 2) (h + u) u := by
        intro u _
        have h1 : HasDerivAt (fun x : ℝ => h * x) h u := by simpa using (hasDerivAt_id u).const_mul h
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) u u := by
          have := ((hasDerivAt_pow 2 u).div_const 2)
          refine this.congr_deriv ?_; ring
        exact h1.add h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.add continuous_id).intervalIntegrable _ _)]
      ring
    have hR : ∫ u in (0 : ℝ)..h, tentKernel h u = ((h ^ 2 / 2 : ℝ) : ℂ) := by
      have hcongr : Set.EqOn (tentKernel h) (fun u => ((h - u : ℝ) : ℂ)) (Set.uIcc 0 h) := by
        intro u hu
        rw [Set.uIcc_of_le (by linarith)] at hu
        unfold tentKernel
        rw [abs_of_nonneg hu.1, max_eq_right (by linarith [hu.2])]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal]
      congr 1
      have hd : ∀ u ∈ Set.uIcc (0 : ℝ) h, HasDerivAt (fun x : ℝ => h * x - x ^ 2 / 2) (h - u) u := by
        intro u _
        have h1 : HasDerivAt (fun x : ℝ => h * x) h u := by simpa using (hasDerivAt_id u).const_mul h
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) u u := by
          have := ((hasDerivAt_pow 2 u).div_const 2)
          refine this.congr_deriv ?_; ring
        exact h1.sub h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
      ring
    rw [hL, hR, ← Complex.ofReal_add]
    congr 1; ring
  · -- Case `t ≠ 0`: explicit antiderivatives on `[-h, 0]` and `[0, h]`!
    simp only [sincSqKernel, ht, ↓reduceIte]
    set ω : ℂ := ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I
    have hω_ne : -2 * Real.pi * t ≠ 0 := by
      intro h0
      have h2pi : (-2 * Real.pi : ℝ) ≠ 0 := by linarith [Real.pi_pos]
      exact ht ((mul_eq_zero.mp h0).resolve_left h2pi)
    have hω : ω ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hω_ne) Complex.I_ne_zero
    have hexp_eq : ∀ u : ℝ,
        Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) = Complex.exp (ω * (u : ℂ)) := by
      intro u; dsimp only [ω]; congr 1; push_cast; ring
    have hL : ∫ u in (-h)..0, Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) * tentKernel h u =
        ((h : ℂ) / ω) - (1 - Complex.exp (ω * ((-h : ℝ) : ℂ))) / ω ^ 2 := by
      have hcongr : Set.EqOn
          (fun u => Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) * tentKernel h u)
          (fun u => Complex.exp (ω * (u : ℂ)) * ((h : ℂ) + (u : ℂ))) (Set.uIcc (-h) 0) := by
        intro u hu
        dsimp only
        rw [Set.uIcc_of_le (by linarith)] at hu
        rw [hexp_eq u]
        unfold tentKernel
        rw [abs_of_nonpos hu.2, sub_neg_eq_add, max_eq_right (by linarith [hu.1])]
        push_cast; rfl
      rw [intervalIntegral.integral_congr hcongr]
      have hd : ∀ u ∈ Set.uIcc (-h) 0,
          HasDerivAt (fun x : ℝ => Complex.exp (ω * (x : ℂ)) * (((h : ℂ) + (x : ℂ)) / ω - 1 / ω ^ 2))
            (Complex.exp (ω * (u : ℂ)) * ((h : ℂ) + (u : ℂ))) u := by
        intro u _
        have hlin : HasDerivAt (fun x : ℝ => ω * (x : ℂ)) ω u := by
          simpa using ((hasDerivAt_id u).ofReal_comp).const_mul ω
        have h1 := hlin.cexp
        have h2 : HasDerivAt (fun x : ℝ => ((h : ℂ) + (x : ℂ)) / ω - 1 / ω ^ 2) (1 / ω) u := by
          have ha : HasDerivAt (fun x : ℝ => (h : ℂ) + (x : ℂ)) 1 u := by
            simpa using ((hasDerivAt_id u).ofReal_comp).const_add (h : ℂ)
          simpa using (ha.div_const ω).sub_const (1 / ω ^ 2)
        refine (h1.mul h2).congr_deriv ?_
        field_simp [hω]; ring
      have hc : Continuous (fun x : ℝ => Complex.exp (ω * (x : ℂ)) * ((h : ℂ) + (x : ℂ))) :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
          (continuous_const.add Complex.continuous_ofReal)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul,
        Complex.ofReal_neg, add_neg_cancel, zero_div, zero_sub]
      ring
    have hR : ∫ u in (0 : ℝ)..h, Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) * tentKernel h u =
        (-(h : ℂ) / ω) + (Complex.exp (ω * (h : ℂ)) - 1) / ω ^ 2 := by
      have hcongr : Set.EqOn
          (fun u => Complex.exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * Complex.I) * tentKernel h u)
          (fun u => Complex.exp (ω * (u : ℂ)) * ((h : ℂ) - (u : ℂ))) (Set.uIcc 0 h) := by
        intro u hu
        dsimp only
        rw [Set.uIcc_of_le (by linarith)] at hu
        rw [hexp_eq u]
        unfold tentKernel
        rw [abs_of_nonneg hu.1, max_eq_right (by linarith [hu.2])]
        push_cast; rfl
      rw [intervalIntegral.integral_congr hcongr]
      have hd : ∀ u ∈ Set.uIcc (0 : ℝ) h,
          HasDerivAt (fun x : ℝ => Complex.exp (ω * (x : ℂ)) * (((h : ℂ) - (x : ℂ)) / ω + 1 / ω ^ 2))
            (Complex.exp (ω * (u : ℂ)) * ((h : ℂ) - (u : ℂ))) u := by
        intro u _
        have hlin : HasDerivAt (fun x : ℝ => ω * (x : ℂ)) ω u := by
          simpa using ((hasDerivAt_id u).ofReal_comp).const_mul ω
        have h1 := hlin.cexp
        have h2 : HasDerivAt (fun x : ℝ => ((h : ℂ) - (x : ℂ)) / ω + 1 / ω ^ 2) (-1 / ω) u := by
          have ha : HasDerivAt (fun x : ℝ => (h : ℂ) - (x : ℂ)) (-1) u := by
            simpa using ((hasDerivAt_id u).ofReal_comp).const_sub (h : ℂ)
          simpa using (ha.div_const ω).add_const (1 / ω ^ 2)
        refine (h1.mul h2).congr_deriv ?_
        field_simp [hω]; ring
      have hc : Continuous (fun x : ℝ => Complex.exp (ω * (x : ℂ)) * ((h : ℂ) - (x : ℂ))) :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
          (continuous_const.sub Complex.continuous_ofReal)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero, one_mul,
        sub_self, zero_div, zero_add]
      ring
    rw [hL, hR]
    have hsum : ((h : ℂ) / ω) - (1 - Complex.exp (ω * ((-h : ℝ) : ℂ))) / ω ^ 2 +
        ((-(h : ℂ) / ω) + (Complex.exp (ω * (h : ℂ)) - 1) / ω ^ 2) =
        (Complex.exp (ω * (h : ℂ)) + Complex.exp (-(ω * (h : ℂ))) - 2) / ω ^ 2 := by
      rw [Complex.ofReal_neg, mul_neg]; ring
    rw [hsum]
    have hωh : ω * (h : ℂ) = -(((2 * Real.pi * h * t : ℝ) : ℂ) * Complex.I) := by
      dsimp only [ω]; push_cast; ring
    have hωsq : ω ^ 2 = -((4 * (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
      dsimp only [ω]; push_cast; rw [mul_pow, Complex.I_sq]; ring
    have hnum : Complex.exp (ω * (h : ℂ)) + Complex.exp (-(ω * (h : ℂ))) - 2 =
        -(((4 * (Real.sin (Real.pi * h * t)) ^ 2 : ℝ) : ℂ)) := by
      rw [hωh, neg_neg]
      have he1 : Complex.exp (-(((2 * Real.pi * h * t : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (((-(2 * Real.pi * h * t) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [he1, Complex.exp_mul_I, Complex.exp_mul_I]
      have hneg : ((-(2 * Real.pi * h * t) : ℝ) : ℂ) = -((2 * Real.pi * h * t : ℝ) : ℂ) := by
        push_cast; ring
      rw [hneg, Complex.cos_neg, Complex.sin_neg]
      have hcos2 : Real.cos (2 * Real.pi * h * t) = 1 - 2 * (Real.sin (Real.pi * h * t)) ^ 2 := by
        rw [show 2 * Real.pi * h * t = 2 * (Real.pi * h * t) by ring, Real.cos_two_mul']
        linarith [Real.sin_sq_add_cos_sq (Real.pi * h * t)]
      have hcos2C : Complex.cos ((2 * Real.pi * h * t : ℝ) : ℂ) =
          ((1 - 2 * (Real.sin (Real.pi * h * t)) ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_cos, hcos2]
      rw [hcos2C]; push_cast; ring
    rw [hnum, hωsq]
    have hpit : (Real.pi * t : ℝ) ≠ 0 := mul_ne_zero Real.pi_pos.ne' ht
    have hpitC : ((Real.pi * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpit
    push_cast
    field_simp [hpitC]

private lemma sincSqKernel_nonneg (h t : ℝ) : 0 ≤ sincSqKernel h t := by
  unfold sincSqKernel
  split_ifs <;> positivity

private lemma sincSqKernel_le_sq {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    sincSqKernel h t ≤ h ^ 2 := by
  unfold sincSqKernel
  split_ifs with ht
  · exact le_rfl
  · have hpi_t : 0 < |Real.pi * t| := abs_pos.mpr (mul_ne_zero Real.pi_pos.ne' ht)
    have hsin : |Real.sin (Real.pi * h * t)| ≤ |Real.pi * h * t| := Real.abs_sin_le_abs
    have h1 : |Real.sin (Real.pi * h * t) / (Real.pi * t)| ≤ h := by
      rw [abs_div, div_le_iff₀ hpi_t]
      calc |Real.sin (Real.pi * h * t)| ≤ |Real.pi * h * t| := hsin
        _ = h * |Real.pi * t| := by
            rw [show Real.pi * h * t = h * (Real.pi * t) by ring, abs_mul, abs_of_nonneg hh]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2

private lemma sincSqKernel_le_inv_sq (h : ℝ) {t : ℝ} (ht : t ≠ 0) :
    sincSqKernel h t ≤ 1 / (Real.pi ^ 2 * t ^ 2) := by
  unfold sincSqKernel
  rw [if_neg ht, div_pow, mul_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : |Real.sin (Real.pi * h * t)| ≤ 1 := Real.abs_sin_le_one _
  rw [← sq_abs]
  nlinarith [abs_nonneg (Real.sin (Real.pi * h * t))]

private lemma integrable_sincSqKernel {h : ℝ} (hh : 0 < h) :
    Integrable (fun t : ℝ => ((sincSqKernel h t : ℝ) : ℂ)) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((sincSqKernel h t : ℝ) : ℂ)) volume := by
    have hfun : (fun t : ℝ => ((sincSqKernel h t : ℝ) : ℂ)) =
        fun t => if t = 0 then ((h ^ 2 : ℝ) : ℂ)
          else (((Real.sin (Real.pi * h * t) / (Real.pi * t)) ^ 2 : ℝ) : ℂ) := by
      funext t; unfold sincSqKernel; split_ifs <;> rfl
    rw [hfun]
    have hmeas1 : Measurable (fun t : ℝ => if t = 0 then ((h ^ 2 : ℝ) : ℂ)
        else (((Real.sin (Real.pi * h * t) / (Real.pi * t)) ^ 2 : ℝ) : ℂ)) := by
      refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
      fun_prop
    exact hmeas1.aestronglyMeasurable
  have hdom : Integrable (fun t : ℝ => (2 * h ^ 2 + 2) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2 * h ^ 2 + 2)
  refine hdom.mono' hmeas (Eventually.of_forall fun t => ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (sincSqKernel_nonneg h t)]
  by_cases ht1 : |t| ≤ 1
  · have ht2 : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
    have h1 : sincSqKernel h t ≤ h ^ 2 := sincSqKernel_le_sq hh.le t
    have hinv : (1 / 2 : ℝ) ≤ (1 + t ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]; linarith
    nlinarith [sq_nonneg h]
  · push Not at ht1
    have ht0 : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht1; linarith
    have ht2 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
    have h1 : sincSqKernel h t ≤ 1 / (Real.pi ^ 2 * t ^ 2) := sincSqKernel_le_inv_sq h ht0
    have hpi1 : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have h2 : 1 / (Real.pi ^ 2 * t ^ 2) ≤ 1 / t ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h3 : 1 / t ^ 2 ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h4 : 2 * (1 + t ^ 2)⁻¹ ≤ (2 * h ^ 2 + 2) * (1 + t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg h]) (by positivity)
    linarith

/-- Lower bound on `sincSqKernel h t` on `[-1 / (2 * h), 1 / (2 * h)]`:
`4 * h ^ 2 / π ^ 2 ≤ sincSqKernel h t`. -/
private lemma sincSqKernel_ge_on_Icc {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : |t| ≤ 1 / (2 * h)) :
    4 * h ^ 2 / Real.pi ^ 2 ≤ sincSqKernel h t := by
  unfold sincSqKernel
  split_ifs with ht0
  · rw [div_le_iff₀ (by positivity)]
    have hpi : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    nlinarith [sq_nonneg h]
  · have hpi_ht : |Real.pi * h * t| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh]
      have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ Real.pi * h)
      refine hmul.trans_eq ?_
      field_simp [hh.ne']
    have hsin_ge : (2 / Real.pi) * |Real.pi * h * t| ≤ |Real.sin (Real.pi * h * t)| := by
      rcases le_total 0 (Real.pi * h * t) with hnn | hnp
      · have hle : Real.pi * h * t ≤ Real.pi / 2 := by rwa [abs_of_nonneg hnn] at hpi_ht
        have h := Real.mul_le_sin hnn hle
        rw [abs_of_nonneg hnn, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hnn (by linarith [Real.pi_pos]))]
        linarith
      · have hnn : 0 ≤ -(Real.pi * h * t) := by linarith
        have hle : -(Real.pi * h * t) ≤ Real.pi / 2 := by rwa [abs_of_nonpos hnp] at hpi_ht
        have h := Real.mul_le_sin hnn hle
        rw [abs_of_nonpos hnp, ← abs_neg (Real.sin _), ← Real.sin_neg,
          abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hnn (by linarith [Real.pi_pos]))]
        linarith
    have hpit_pos : 0 < |Real.pi * t| := abs_pos.mpr (mul_ne_zero Real.pi_pos.ne' ht0)
    have hratio : 2 * h / Real.pi ≤ |Real.sin (Real.pi * h * t) / (Real.pi * t)| := by
      rw [abs_div, le_div_iff₀ hpit_pos]
      have habs_eq : h * |Real.pi * t| = |Real.pi * h * t| := by
        rw [show Real.pi * h * t = h * (Real.pi * t) by ring, abs_mul h (Real.pi * t),
          abs_of_pos hh]
      calc 2 * h / Real.pi * |Real.pi * t|
          = 2 / Real.pi * (h * |Real.pi * t|) := by ring
        _ = 2 / Real.pi * |Real.pi * h * t| := by rw [habs_eq]
        _ ≤ |Real.sin (Real.pi * h * t)| := hsin_ge
    have hsq := pow_le_pow_left₀ (by positivity) hratio 2
    rw [sq_abs] at hsq
    refine le_trans ?_ hsq
    have heq : 4 * h ^ 2 / Real.pi ^ 2 = (2 * h / Real.pi) ^ 2 := by ring
    exact heq.le

/-- Exact Fourier inversion of `sincSqKernel h`:
`∫ t : ℝ, (sincSqKernel h t : ℂ) * Complex.exp (2 * π * I * ω * t) = tentKernel h ω`. -/
private lemma integral_sincSqKernel_mul_exp {h : ℝ} (hh : 0 < h) (ω : ℝ) :
    ∫ t : ℝ, ((sincSqKernel h t : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ) * (t : ℂ)) =
      tentKernel h ω := by
  have hft : 𝓕 (tentKernel h) = fun t => ((sincSqKernel h t : ℝ) : ℂ) :=
    funext (fourier_tentKernel_eq hh)
  have hinv := (continuous_tentKernel h).fourierInv_fourier_eq (integrable_tentKernel hh)
    (hft ▸ integrable_sincSqKernel hh)
  have hpt := congrFun hinv ω
  rw [Real.fourierInv_eq', hft] at hpt
  rw [← hpt]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_comm]
  congr 2
  push_cast; ring

/-- Exact convolution identity for the tent kernel: for any `h > 0` and `a, b : ℝ`,
`∫ x : ℝ, (if x < a ∧ a ≤ x + h then 1 else 0) * (if x < b ∧ b ≤ x + h then 1 else 0) = tentKernelR h (a - b)`. -/
private lemma integral_box_mul_box {h : ℝ} (_hh : 0 < h) (a b : ℝ) :
    ∫ x : ℝ, (if x < a ∧ a ≤ x + h then (1 : ℝ) else 0) *
        (if x < b ∧ b ≤ x + h then (1 : ℝ) else 0) =
      tentKernelR h (a - b) := by
  have hind : (fun x : ℝ => (if x < a ∧ a ≤ x + h then (1 : ℝ) else 0) *
      (if x < b ∧ b ≤ x + h then (1 : ℝ) else 0)) =
      Set.indicator (Set.Ico (max (a - h) (b - h)) (min a b)) (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hmem : x ∈ Set.Ico (max (a - h) (b - h)) (min a b)
    · rw [Set.indicator_of_mem hmem]
      simp only [Set.mem_Ico, max_le_iff, lt_min_iff] at hmem
      rw [if_pos ⟨hmem.2.1, by linarith [hmem.1.1]⟩, if_pos ⟨hmem.2.2, by linarith [hmem.1.2]⟩, mul_one]
    · rw [Set.indicator_of_notMem hmem]
      simp only [Set.mem_Ico, max_le_iff, lt_min_iff, not_and_or, not_le, not_lt] at hmem
      rcases hmem with (h1 | h1) | (h2 | h2)
      · have : ¬ (x < a ∧ a ≤ x + h) := fun h' => by linarith [h'.2]
        simp [this]
      · have : ¬ (x < b ∧ b ≤ x + h) := fun h' => by linarith [h'.2]
        simp [this]
      · have : ¬ (x < a ∧ a ≤ x + h) := fun h' => by linarith [h'.1]
        simp [this]
      · have : ¬ (x < b ∧ b ≤ x + h) := fun h' => by linarith [h'.1]
        simp [this]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Ico, MeasureTheory.setIntegral_const,
    Real.volume_real_Ico, smul_eq_mul, mul_one]
  unfold tentKernelR
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right (by linarith : a - h ≤ b - h),
      abs_of_nonpos (sub_nonpos.mpr hab), max_comm]
    congr 1; ring
  · rw [min_eq_right hba, max_eq_left (by linarith : b - h ≤ a - h),
      abs_of_nonneg (sub_nonneg.mpr hba), max_comm]
    congr 1; ring

/-- **Gallagher's Continuous Mean-Value Theorem (Gallagher 1970, Theorem 1)**:
for any `T > 0`, finite index set `I`, real frequencies `ν : I → ℝ`, and complex coefficients `c : I → ℂ`,
`∫ t in (-T)..T, ‖∑ i ∈ I, c i * exp (-2 π I ν_i t)‖² ≤ π² T² * ∫ x, ‖∑_{i ∈ I, x < ν_i ≤ x + 1/(2T)} c i‖²`. -/
theorem gallagher_continuous_mean_value {ι : Type*} (I : Finset ι) (ν : ι → ℝ) (c : ι → ℂ)
    {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ‖∑ i ∈ I, c i * Complex.exp (-2 * Real.pi * Complex.I * (ν i : ℂ) * (t : ℂ))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 *
        ∫ x : ℝ, ‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + 1 / (2 * T)), c i‖ ^ 2 := by
  set h : ℝ := 1 / (2 * T)
  have hh : 0 < h := by positivity
  let S : ℝ → ℂ := fun t =>
    ∑ i ∈ I, c i * Complex.exp (-2 * Real.pi * Complex.I * (ν i : ℂ) * (t : ℂ))
  have hS_cont : Continuous S := by
    refine continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact continuous_const.mul Complex.continuous_ofReal
  have hS_bd : ∀ t : ℝ, ‖S t‖ ^ 2 ≤ (∑ i ∈ I, ‖c i‖) ^ 2 := fun t => by
    have h1 : ‖S t‖ ≤ ∑ i ∈ I, ‖c i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul,
        show -2 * Real.pi * Complex.I * (ν i : ℂ) * (t : ℂ) =
          ((-(2 * Real.pi * ν i * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsinc_int : Integrable (fun t : ℝ => sincSqKernel h t) := by
    have h1 := (integrable_sincSqKernel hh).re
    simpa using h1
  have hprod_int : Integrable (fun t : ℝ => sincSqKernel h t * ‖S t‖ ^ 2) := by
    refine (hsinc_int.const_mul ((∑ i ∈ I, ‖c i‖) ^ 2)).mono'
      (hsinc_int.aestronglyMeasurable.mul (hS_cont.norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sincSqKernel_nonneg h t) (sq_nonneg _)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS_bd t) (sincSqKernel_nonneg h t)
  -- Step 1: Lower-bound `∫_ℝ sincSqKernel h t * ‖S t‖^2` by `(1 / (π^2 T^2)) * ∫_{-T}^T ‖S t‖^2`
  have hstep1 : (1 / (Real.pi ^ 2 * T ^ 2)) * (∫ t in (-T)..T, ‖S t‖ ^ 2) ≤
      ∫ t : ℝ, sincSqKernel h t * ‖S t‖ ^ 2 := by
    have hcoeff : 4 * h ^ 2 / Real.pi ^ 2 = 1 / (Real.pi ^ 2 * T ^ 2) := by
      dsimp only [h]; field_simp [Real.pi_pos.ne', hT.ne']; ring
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith)]
    calc ∫ t in Set.Ioc (-T) T, (1 / (Real.pi ^ 2 * T ^ 2)) * ‖S t‖ ^ 2
        ≤ ∫ t in Set.Ioc (-T) T, sincSqKernel h t * ‖S t‖ ^ 2 := by
          refine setIntegral_mono_on
            ((continuous_const.mul (hS_cont.norm.pow 2)).integrableOn_Ioc)
            hprod_int.integrableOn measurableSet_Ioc fun t ht => ?_
          have habs : |t| ≤ 1 / (2 * h) := by
            have h12h : 1 / (2 * h) = T := by dsimp only [h]; field_simp [hT.ne']
            rw [h12h, abs_le]; exact ⟨ht.1.le, ht.2⟩
          have hge := sincSqKernel_ge_on_Icc hh habs
          rw [hcoeff] at hge
          exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)
      _ ≤ ∫ t : ℝ, sincSqKernel h t * ‖S t‖ ^ 2 :=
          setIntegral_le_integral hprod_int
            (Eventually.of_forall fun t => mul_nonneg (sincSqKernel_nonneg h t) (sq_nonneg _))
  -- Step 2: Evaluate `∫_ℝ sincSqKernel h t * ‖S t‖^2 = ∑_{i,j} (c i * star (c j) * tentKernel h (ν j - ν i)).re`
  have hstep2 : ∫ t : ℝ, sincSqKernel h t * ‖S t‖ ^ 2 =
      (∑ i ∈ I, ∑ j ∈ I, c i * star (c j) * tentKernel h (ν j - ν i)).re := by
    have hpt : ∀ t : ℝ, ((sincSqKernel h t * ‖S t‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ I, ∑ j ∈ I,
          c i * star (c j) *
            (((sincSqKernel h t : ℝ) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * ((ν j - ν i : ℝ) : ℂ) * (t : ℂ))) := by
      intro t
      have hsq : ((‖S t‖ ^ 2 : ℝ) : ℂ) = S t * star (S t) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [Complex.ofReal_mul, hsq]
      dsimp only [S]
      rw [star_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul', Complex.star_def, ← Complex.exp_conj]
      simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, neg_mul,
        mul_neg, neg_neg]
      have hexp :
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ν i : ℂ) * (t : ℂ))) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ν j : ℂ) * (t : ℂ)) =
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ν j - ν i : ℝ) : ℂ) * (t : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      calc ((sincSqKernel h t : ℝ) : ℂ) *
            (c i * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ν i : ℂ) * (t : ℂ))) *
              (starRingEnd ℂ (c j) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ν j : ℂ) * (t : ℂ))))
          = c i * star (c j) * (((sincSqKernel h t : ℝ) : ℂ) *
              (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ν i : ℂ) * (t : ℂ))) *
               Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ν j : ℂ) * (t : ℂ)))) := by
            rw [Complex.star_def]; ring
        _ = c i * star (c j) * (((sincSqKernel h t : ℝ) : ℂ) *
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ν j - ν i : ℝ) : ℂ) * (t : ℂ))) := by
            rw [hexp]
    have hterm_int : ∀ i j : ι, Integrable (fun t : ℝ =>
        c i * star (c j) * (((sincSqKernel h t : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((ν j - ν i : ℝ) : ℂ) * (t : ℂ)))) := by
      intro i j
      refine ((integrable_sincSqKernel hh).norm.const_mul ‖c i * star (c j)‖).mono' ?_ ?_
      · exact (aestronglyMeasurable_const).mul
          ((integrable_sincSqKernel hh).aestronglyMeasurable.mul
            (Complex.continuous_exp.comp
              (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
      · refine Eventually.of_forall fun t => ?_
        rw [norm_mul, norm_mul, norm_mul,
          show 2 * Real.pi * Complex.I * ((ν j - ν i : ℝ) : ℂ) * (t : ℂ) =
            ((2 * Real.pi * (ν j - ν i) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    have hint_C : ∫ t : ℝ, ((sincSqKernel h t * ‖S t‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ I, ∑ j ∈ I, c i * star (c j) * tentKernel h (ν j - ν i) := by
      simp_rw [hpt]
      rw [MeasureTheory.integral_finsetSum I fun i _ =>
        MeasureTheory.integrable_finsetSum I fun j _ => hterm_int i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MeasureTheory.integral_finsetSum I fun j _ => hterm_int i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MeasureTheory.integral_const_mul, integral_sincSqKernel_mul_exp hh (ν j - ν i)]
    have hre := congrArg Complex.re hint_C
    have hofR : (∫ t : ℝ, ((sincSqKernel h t * ‖S t‖ ^ 2 : ℝ) : ℂ)) =
        ((∫ t : ℝ, sincSqKernel h t * ‖S t‖ ^ 2 : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hprod_int
    rw [hofR, Complex.ofReal_re] at hre
    exact hre
  -- Step 3: Evaluate `∫_ℝ ‖∑_{x < ν i ≤ x + h} c i‖^2 dx = (∑_{i,j} c i * star (c j) * tentKernel h (ν j - ν i)).re`
  have hstep3 : ∫ x : ℝ, ‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 =
      (∑ i ∈ I, ∑ j ∈ I, c i * star (c j) * tentKernel h (ν j - ν i)).re := by
    have hpt : ∀ x : ℝ, ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ I, ∑ j ∈ I,
          c i * star (c j) *
            (((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
              (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      intro x
      have hsq : ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) =
          (∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i) *
          star (∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hsq, Finset.sum_filter, star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hi : x < ν i ∧ ν i ≤ x + h <;> by_cases hj : x < ν j ∧ ν j ≤ x + h <;>
        simp [hi, hj]
    have hbox_intR : ∀ i j : ι, Integrable (fun x : ℝ =>
        ((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
          (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ)) := by
      intro i j
      have hind : (fun x : ℝ =>
          ((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
            (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ)) =
          Set.indicator (Set.Ico (max (ν i - h) (ν j - h)) (min (ν i) (ν j))) (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hmem : x ∈ Set.Ico (max (ν i - h) (ν j - h)) (min (ν i) (ν j))
        · rw [Set.indicator_of_mem hmem]
          simp only [Set.mem_Ico, max_le_iff, lt_min_iff] at hmem
          rw [if_pos ⟨hmem.2.1, by linarith [hmem.1.1]⟩, if_pos ⟨hmem.2.2, by linarith [hmem.1.2]⟩, mul_one]
        · rw [Set.indicator_of_notMem hmem]
          simp only [Set.mem_Ico, max_le_iff, lt_min_iff, not_and_or, not_le, not_lt] at hmem
          rcases hmem with (h1 | h1) | (h2 | h2)
          · have : ¬ (x < ν i ∧ ν i ≤ x + h) := fun h' => by linarith [h'.2]
            simp [this]
          · have : ¬ (x < ν j ∧ ν j ≤ x + h) := fun h' => by linarith [h'.2]
            simp [this]
          · have : ¬ (x < ν i ∧ ν i ≤ x + h) := fun h' => by linarith [h'.1]
            simp [this]
          · have : ¬ (x < ν j ∧ ν j ≤ x + h) := fun h' => by linarith [h'.1]
            simp [this]
      rw [hind]
      exact (integrableOn_const (hs := measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
    have hbox_int : ∀ i j : ι, Integrable (fun x : ℝ =>
        c i * star (c j) *
          (((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
            (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ) : ℂ)) :=
      fun i j => (Complex.ofRealCLM.integrable_comp (hbox_intR i j)).const_mul (c i * star (c j))
    have hnorm_intR : Integrable (fun x : ℝ => ‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2) := by
      have hC_int : Integrable (fun x : ℝ =>
          ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ)) := by
        simp_rw [hpt]
        exact MeasureTheory.integrable_finsetSum I fun i _ =>
          MeasureTheory.integrable_finsetSum I fun j _ => hbox_int i j
      have hre_int := hC_int.re
      refine hre_int.congr (Eventually.of_forall fun x => ?_)
      simp only [RCLike.re_to_complex, Complex.ofReal_re]
    have hint_C : ∫ x : ℝ, ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ I, ∑ j ∈ I, c i * star (c j) * tentKernel h (ν j - ν i) := by
      simp_rw [hpt]
      rw [MeasureTheory.integral_finsetSum I fun i _ =>
        MeasureTheory.integrable_finsetSum I fun j _ => hbox_int i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MeasureTheory.integral_finsetSum I fun j _ => hbox_int i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hofR_ij : ∫ a : ℝ, (((if a < ν i ∧ ν i ≤ a + h then (1 : ℝ) else 0) *
            (if a < ν j ∧ ν j ≤ a + h then (1 : ℝ) else 0) : ℝ) : ℂ) =
          ((∫ a : ℝ, (if a < ν i ∧ ν i ≤ a + h then (1 : ℝ) else 0) *
            (if a < ν j ∧ ν j ≤ a + h then (1 : ℝ) else 0) : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm (hbox_intR i j)
      rw [MeasureTheory.integral_const_mul, hofR_ij, integral_box_mul_box hh (ν i) (ν j)]
      congr 1
      unfold tentKernel tentKernelR
      rw [show |ν j - ν i| = |ν i - ν j| by rw [← abs_neg, neg_sub]]
    have hre := congrArg Complex.re hint_C
    have hofR_norm : ∫ x : ℝ, ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) =
        ((∫ x : ℝ, ‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hnorm_intR
    rw [hofR_norm, Complex.ofReal_re] at hre
    exact hre
  -- Combine Steps 1, 2, 3!
  have hcomb : (1 / (Real.pi ^ 2 * T ^ 2)) * (∫ t in (-T)..T, ‖S t‖ ^ 2) ≤
      ∫ x : ℝ, ‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 := by
    linarith [hstep1, hstep2, hstep3]
  have hmul := mul_le_mul_of_nonneg_left hcomb (by positivity : 0 ≤ Real.pi ^ 2 * T ^ 2)
  have hcancel : Real.pi ^ 2 * T ^ 2 * (1 / (Real.pi ^ 2 * T ^ 2) * ∫ t in (-T)..T, ‖S t‖ ^ 2) =
      ∫ t in (-T)..T, ‖S t‖ ^ 2 := by
    field_simp [Real.pi_pos.ne', hT.ne']
  linarith

/-! ### Section 1b: Gallagher's Continuous & Discrete Hybrid Large Sieve -/

/-- Frequency `ν(n) = log n / (2 π)` for Dirichlet polynomial terms `n^(-I * t) = exp(-2 π I ν(n) t)`. -/
private def logFreq (n : ℕ) : ℝ := Real.log (n : ℝ) / (2 * Real.pi)

private lemma nat_cpow_neg_I_mul_eq_exp_logFreq {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(Complex.I * (t : ℂ))) =
      Complex.exp (-2 * Real.pi * Complex.I * (logFreq n : ℂ) * (t : ℂ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
  congr 1
  unfold logFreq
  push_cast
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp [hpiC]

private lemma exp_sub_one_le_mul_exp {u M : ℝ} (hu0 : 0 ≤ u) (huM : u ≤ M) :
    Real.exp u - 1 ≤ Real.exp M * u := by
  have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos u).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have h3 : Real.exp u - 1 ≤ Real.exp u * u := by linarith
  have h4 : Real.exp u ≤ Real.exp M := Real.exp_le_exp.mpr huM
  nlinarith

/-- Measure of the indicator `{x : ℝ | x < a ∧ a ≤ x + h}` equals `h` for `h > 0`. -/
private lemma integral_box_indicator {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∫ x : ℝ, (if x < a ∧ a ≤ x + h then (1 : ℝ) else 0) = h := by
  have h1 := integral_box_mul_box hh a a
  have heq : (fun x : ℝ => (if x < a ∧ a ≤ x + h then (1 : ℝ) else 0) *
      (if x < a ∧ a ≤ x + h then (1 : ℝ) else 0)) =
      fun x => if x < a ∧ a ≤ x + h then (1 : ℝ) else 0 := by
    funext x; split_ifs <;> norm_num
  rw [heq] at h1
  simpa only [sub_self, abs_zero, sub_zero, tentKernelR, max_eq_right hh.le] using h1

/-- Integrability of `x ↦ ‖∑_{n ∈ I, x < ν n ≤ x + h} c n‖^2`. -/
private lemma integrable_short_sum_norm_sq {ι : Type*} (I : Finset ι) (ν : ι → ℝ) (c : ι → ℂ)
    {h : ℝ} (_hh : 0 < h) :
    Integrable (fun x : ℝ => ‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2) := by
  have hpt : ∀ x : ℝ, ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ I, ∑ j ∈ I,
        c i * star (c j) *
          (((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
            (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    intro x
    have hsq : ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ) =
        (∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i) *
        star (∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, Finset.sum_filter, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : x < ν i ∧ ν i ≤ x + h <;> by_cases hj : x < ν j ∧ ν j ≤ x + h <;>
      simp [hi, hj]
  have hbox : ∀ i j : ι, Integrable (fun x : ℝ =>
      c i * star (c j) *
        (((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
          (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ) : ℂ)) := by
    intro i j
    have hind : (fun x : ℝ =>
        ((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
          (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ)) =
        Set.indicator (Set.Ico (max (ν i - h) (ν j - h)) (min (ν i) (ν j))) (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hmem : x ∈ Set.Ico (max (ν i - h) (ν j - h)) (min (ν i) (ν j))
      · rw [Set.indicator_of_mem hmem]
        simp only [Set.mem_Ico, max_le_iff, lt_min_iff] at hmem
        rw [if_pos ⟨hmem.2.1, by linarith [hmem.1.1]⟩, if_pos ⟨hmem.2.2, by linarith [hmem.1.2]⟩, mul_one]
      · rw [Set.indicator_of_notMem hmem]
        simp only [Set.mem_Ico, max_le_iff, lt_min_iff, not_and_or, not_le, not_lt] at hmem
        rcases hmem with (h1 | h1) | (h2 | h2)
        · have : ¬ (x < ν i ∧ ν i ≤ x + h) := fun h' => by linarith [h'.2]
          simp [this]
        · have : ¬ (x < ν j ∧ ν j ≤ x + h) := fun h' => by linarith [h'.2]
          simp [this]
        · have : ¬ (x < ν i ∧ ν i ≤ x + h) := fun h' => by linarith [h'.1]
          simp [this]
        · have : ¬ (x < ν j ∧ ν j ≤ x + h) := fun h' => by linarith [h'.1]
          simp [this]
    have hintR : Integrable (fun x : ℝ =>
        ((if x < ν i ∧ ν i ≤ x + h then (1 : ℝ) else 0) *
          (if x < ν j ∧ ν j ≤ x + h then (1 : ℝ) else 0) : ℝ)) := by
      rw [hind]
      exact (integrableOn_const (hs := measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
    exact (Complex.ofRealCLM.integrable_comp hintR).const_mul (c i * star (c j))
  have hC : Integrable (fun x : ℝ => ((‖∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), c i‖ ^ 2 : ℝ) : ℂ)) := by
    simp_rw [hpt]
    exact MeasureTheory.integrable_finsetSum I fun i _ =>
      MeasureTheory.integrable_finsetSum I fun j _ => hbox i j
  refine hC.re.congr (Eventually.of_forall fun x => ?_)
  simp only [RCLike.re_to_complex, Complex.ofReal_re]

/-- Integrability of `x ↦ ∑_{n ∈ I, x < ν n ≤ x + h} w n` and its exact value `h * ∑_{n ∈ I} w n`. -/
private lemma integral_short_sum_weight {ι : Type*} (I : Finset ι) (ν : ι → ℝ) (w : ι → ℝ)
    {h : ℝ} (hh : 0 < h) :
    Integrable (fun x : ℝ => ∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), w i) ∧
    ∫ x : ℝ, (∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), w i) = h * ∑ i ∈ I, w i := by
  have hind : ∀ i : ι, (fun x : ℝ => if x < ν i ∧ ν i ≤ x + h then w i else 0) =
      Set.indicator (Set.Ico (ν i - h) (ν i)) (fun _ => w i) := fun i => by
    funext x
    by_cases hmem : x ∈ Set.Ico (ν i - h) (ν i)
    · rw [Set.indicator_of_mem hmem]
      simp only [Set.mem_Ico] at hmem
      rw [if_pos ⟨hmem.2, by linarith [hmem.1]⟩]
    · rw [Set.indicator_of_notMem hmem]
      simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hmem
      rcases hmem with h1 | h2
      · rw [if_neg (fun h' => by linarith [h'.2])]
      · rw [if_neg (fun h' => by linarith [h'.1])]
  have hint_i : ∀ i : ι, Integrable (fun x : ℝ => if x < ν i ∧ ν i ≤ x + h then w i else 0) := by
    intro i; rw [hind i]
    exact (integrableOn_const (hs := measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
  have hfun : (fun x : ℝ => ∑ i ∈ I.filter (fun i => x < ν i ∧ ν i ≤ x + h), w i) =
      fun x => ∑ i ∈ I, if x < ν i ∧ ν i ≤ x + h then w i else 0 := by
    funext x; rw [Finset.sum_filter]
  rw [hfun]
  refine ⟨MeasureTheory.integrable_finsetSum I fun i _ => hint_i i, ?_⟩
  rw [MeasureTheory.integral_finsetSum I fun i _ => hint_i i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hind i, MeasureTheory.integral_indicator measurableSet_Ico, MeasureTheory.setIntegral_const,
    Real.volume_real_Ico, smul_eq_mul, show ν i - (ν i - h) = h by ring, max_eq_left hh.le]

/-- Short logarithmic window containment: for `T ≥ 1`, `x : ℝ`, and `I ⊆ Finset.Icc 1 N`,
every `n ∈ I` with `x < log n / (2 π) ≤ x + 1 / (2 T)` satisfies
`exp (2 π x) < n ≤ exp (2 π x) * exp (π / T)` and lies in `Icc (⌊y⌋₊ + 1) (⌊y * exp (π / T)⌋₊)`. -/
private lemma short_logFreq_window_subset {I : Finset ℕ} (hI : ∀ n ∈ I, 1 ≤ n)
    {T : ℝ} (hT : 1 ≤ T) (x : ℝ) :
    let y : ℝ := Real.exp (2 * Real.pi * x)
    let M₁ : ℕ := ⌊y⌋₊ + 1
    let M₂ : ℕ := ⌊y * Real.exp (Real.pi / T)⌋₊
    (I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + 1 / (2 * T))) ⊆ Finset.Icc M₁ M₂ ∧
    (∀ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + 1 / (2 * T)), y < (n : ℝ)) ∧
    (((M₂ + 1 - M₁ : ℕ) : ℝ) ≤ Real.pi * Real.exp Real.pi * (y / T) + 1) := by
  intro y M₁ M₂
  have hy_pos : 0 < y := Real.exp_pos _
  have hpiT_pos : 0 < Real.pi / T := div_pos Real.pi_pos (by linarith)
  have hpiT_le : Real.pi / T ≤ Real.pi := div_le_self Real.pi_pos.le hT
  have hexp_sub : Real.exp (Real.pi / T) - 1 ≤ Real.exp Real.pi * (Real.pi / T) :=
    exp_sub_one_le_mul_exp hpiT_pos.le hpiT_le
  have hmem_bounds : ∀ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + 1 / (2 * T)),
      y < (n : ℝ) ∧ (n : ℝ) ≤ y * Real.exp (Real.pi / T) := by
    intro n hn
    obtain ⟨hnI, hxlo, hxhi⟩ := Finset.mem_filter.mp hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (hI n hnI)
    unfold logFreq at hxlo hxhi
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hlo : 2 * Real.pi * x < Real.log (n : ℝ) := by
      have := (lt_div_iff₀ h2pi).mp hxlo; linarith
    have hhi : Real.log (n : ℝ) ≤ 2 * Real.pi * x + Real.pi / T := by
      have h1 := (div_le_iff₀ h2pi).mp hxhi
      have h2 : (x + 1 / (2 * T)) * (2 * Real.pi) = 2 * Real.pi * x + Real.pi / T := by
        field_simp [(by linarith : T ≠ 0)]
      linarith
    constructor
    · rw [← Real.exp_log hn_pos]; exact Real.exp_lt_exp.mpr hlo
    · rw [← Real.exp_log hn_pos, show y * Real.exp (Real.pi / T) =
          Real.exp (2 * Real.pi * x + Real.pi / T) from (Real.exp_add _ _).symm]
      exact Real.exp_le_exp.mpr hhi
  refine ⟨fun n hn => ?_, fun n hn => (hmem_bounds n hn).1, ?_⟩
  · obtain ⟨hlo, hhi⟩ := hmem_bounds n hn
    rw [Finset.mem_Icc]
    constructor
    · have hlt : ⌊y⌋₊ < n := (Nat.floor_lt hy_pos.le).mpr hlo
      omega
    · exact Nat.le_floor hhi
  · by_cases hle : M₁ ≤ M₂ + 1
    · rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
      have hM2 : (M₂ : ℝ) ≤ y * Real.exp (Real.pi / T) := Nat.floor_le (by positivity)
      have hM1 : y < (M₁ : ℝ) := by
        dsimp only [M₁]; push_cast; exact Nat.lt_floor_add_one y
      have hdiff : y * Real.exp (Real.pi / T) - y ≤ Real.pi * Real.exp Real.pi * (y / T) := by
        have h1 : y * Real.exp (Real.pi / T) - y = y * (Real.exp (Real.pi / T) - 1) := by ring
        rw [h1]
        calc y * (Real.exp (Real.pi / T) - 1)
            ≤ y * (Real.exp Real.pi * (Real.pi / T)) := mul_le_mul_of_nonneg_left hexp_sub hy_pos.le
          _ = Real.pi * Real.exp Real.pi * (y / T) := by ring
      linarith
    · have h0 : M₂ + 1 - M₁ = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [h0, Nat.cast_zero]
      positivity

open Classical in
/-- **Gallagher's Continuous Hybrid Large Sieve (Primitive Characters, 100% LOG-FREE!)**:
for EVERY `Q ≥ 1`, `T ≥ 1`, finite `I ⊆ [1, ∞)`, and `a : ℕ → ℂ`:
`∑_{q=1}^Q ∑*_{χ mod q} ∫_{-T}^T ‖∑_{n ∈ I} a n * χ(n) * n^(-I*t)‖² dt ≤ 400 * ∑_{n ∈ I} (Q² T + n) * ‖a n‖²`. -/
theorem gallagher_continuous_hybrid_large_sieve (Q : ℕ) (hQ : 1 ≤ Q) {T : ℝ} (hT : 1 ≤ T)
    (I : Finset ℕ) (hI : ∀ n ∈ I, 1 ≤ n) (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ∫ t in (-T)..T, ‖∑ n ∈ I, a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      400 * ∑ n ∈ I, ((Q : ℝ) ^ 2 * T + (n : ℝ)) * ‖a n‖ ^ 2 := by
  classical
  set h : ℝ := 1 / (2 * T)
  have hh : 0 < h := by positivity
  have hTpos : 0 < T := by linarith
  -- Step 1: Apply `gallagher_continuous_mean_value` to every primitive character `(k, χ)`
  have hstep1 :
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖∑ n ∈ I, a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 *
        ∫ x : ℝ, ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
              a n * χ (n : ZMod (k + 1))‖ ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [MeasureTheory.integral_finsetSum]
      · rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun χ _ => ?_
        have hrew : ∀ t : ℝ,
            ∑ n ∈ I, a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))) =
            ∑ n ∈ I, (a n * χ (n : ZMod (k + 1))) *
              Complex.exp (-2 * Real.pi * Complex.I * (logFreq n : ℂ) * (t : ℂ)) := fun t =>
          Finset.sum_congr rfl fun n hn => by rw [nat_cpow_neg_I_mul_eq_exp_logFreq (hI n hn) t]
        simp_rw [hrew]
        exact gallagher_continuous_mean_value I logFreq (fun n => a n * χ (n : ZMod (k + 1))) hTpos
      · intro χ _
        exact integrable_short_sum_norm_sq I logFreq (fun n => a n * χ (n : ZMod (k + 1))) hh
    · intro k _
      exact MeasureTheory.integrable_finsetSum _ fun χ _ =>
        integrable_short_sum_norm_sq I logFreq (fun n => a n * χ (n : ZMod (k + 1))) hh
  -- Step 2: Bound the integrand pointwise using `Stage3BombieriVinogradov.multiplicative_large_sieve_Icc_range`!
  set K_π : ℝ := Real.pi * Real.exp Real.pi
  have hpoint : ∀ x : ℝ,
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
            a n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
        (K_π * ((n : ℝ) / T) + 4 * (Q : ℝ) ^ 2) * ‖a n‖ ^ 2 := by
    intro x
    set Sx : Finset ℕ := I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h)
    obtain ⟨hsub, hy_lt, hlen⟩ := short_logFreq_window_subset hI hT x
    set y : ℝ := Real.exp (2 * Real.pi * x)
    set M₁ : ℕ := ⌊y⌋₊ + 1
    set M₂ : ℕ := ⌊y * Real.exp (Real.pi / T)⌋₊
    have hsub' : Sx ⊆ Finset.Icc M₁ M₂ := hsub
    let c : ℕ → ℂ := fun n => if n ∈ Sx then a n else 0
    have hsum_eq : ∀ (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)),
        ∑ n ∈ Sx, a n * χ (n : ZMod (k + 1)) =
        ∑ n ∈ Finset.Icc M₁ M₂, c n * χ (n : ZMod (k + 1)) := by
      intro k χ
      symm
      rw [← Finset.sum_subset hsub']
      · refine Finset.sum_congr rfl fun n hn => by simp [c, hn]
      · intro n _ hn; simp [c, hn]
    have hnorm_eq : ∑ n ∈ Finset.Icc M₁ M₂, ‖c n‖ ^ 2 = ∑ n ∈ Sx, ‖a n‖ ^ 2 := by
      rw [← Finset.sum_subset hsub']
      · refine Finset.sum_congr rfl fun n hn => by simp [c, hn]
      · intro n _ hn; simp [c, hn]
    simp_rw [hsum_eq]
    have hmls := Stage3BombieriVinogradov.multiplicative_large_sieve_Icc_range Q M₁ M₂ c
    rw [hnorm_eq] at hmls
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      nlinarith
    have hcoeff : ((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2 ≤ K_π * (y / T) + 4 * (Q : ℝ) ^ 2 := by
      dsimp only [K_π]; linarith
    calc ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Icc M₁ M₂, c n * χ (n : ZMod (k + 1))‖ ^ 2
        ≤ (((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Sx, ‖a n‖ ^ 2 := hmls
      _ ≤ (K_π * (y / T) + 4 * (Q : ℝ) ^ 2) * ∑ n ∈ Sx, ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = ∑ n ∈ Sx, (K_π * (y / T) + 4 * (Q : ℝ) ^ 2) * ‖a n‖ ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ Sx, (K_π * ((n : ℝ) / T) + 4 * (Q : ℝ) ^ 2) * ‖a n‖ ^ 2 := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hyn : y ≤ (n : ℝ) := (hy_lt n hn).le
          have hdiv : y / T ≤ (n : ℝ) / T := div_le_div_of_nonneg_right hyn hTpos.le
          have hK_nn : 0 ≤ K_π := by dsimp only [K_π]; positivity
          nlinarith
  -- Step 3: Integrate `hpoint` over `x : ℝ` and bound `π² / 2 * max K_π 4 ≤ 400`
  have hint_lhs : Integrable (fun x : ℝ => ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ‖∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
          a n * χ (n : ZMod (k + 1))‖ ^ 2) :=
    MeasureTheory.integrable_finsetSum _ fun k _ =>
      MeasureTheory.integrable_finsetSum _ fun χ _ =>
        integrable_short_sum_norm_sq I logFreq (fun n => a n * χ (n : ZMod (k + 1))) hh
  obtain ⟨hint_rhs, hrhs_eq⟩ := integral_short_sum_weight I logFreq
    (fun n => (K_π * ((n : ℝ) / T) + 4 * (Q : ℝ) ^ 2) * ‖a n‖ ^ 2) hh
  have hint_mono := MeasureTheory.integral_mono hint_lhs hint_rhs hpoint
  rw [hrhs_eq] at hint_mono
  have hpi_le : Real.pi ≤ 315 / 100 := by linarith [Real.pi_lt_d2]
  have hexp_pi_le : Real.exp Real.pi ≤ 252 / 10 := by
    have he1 : Real.exp 1 ≤ 272 / 100 := by linarith [Real.exp_one_lt_d9]
    have h1 : Real.exp Real.pi ≤ Real.exp (16 / 5 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith [Real.pi_lt_d2])
    have h2 : Real.exp (16 / 5 : ℝ) = Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) := by
      rw [← Real.exp_add]; congr 1; norm_num
    have h3 : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
      have hinv : 1 - (1 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 5 : ℝ))]
      have hmul := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (1 / 5 : ℝ)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      linarith
    have hpow3 : (Real.exp 1) ^ 3 ≤ (272 / 100 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1 3
    have hprod : Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) ≤ (272 / 100 : ℝ) ^ 3 * (5 / 4) := by
      rw [h3]
      exact mul_le_mul hpow3 h4 (Real.exp_pos _).le (by positivity)
    linarith [show (272 / 100 : ℝ) ^ 3 * (5 / 4) ≤ 252 / 10 by norm_num]
  -- Use `exp(π) ≤ 25.2` (directly from `exp(1) < 2.72` and `exp(1/5) ≤ 5/4`) so `π^2 / 2 * K_π < 400`!
  have hKpi_le : K_π ≤ 80 := by
    dsimp only [K_π]; nlinarith [Real.pi_pos, Real.exp_pos Real.pi]
  have hpi2_le : Real.pi ^ 2 / 2 ≤ 5 := by nlinarith [Real.pi_pos]
  calc ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖∑ n ∈ I, a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ Real.pi ^ 2 * T ^ 2 * (h * ∑ n ∈ I, (K_π * ((n : ℝ) / T) + 4 * (Q : ℝ) ^ 2) * ‖a n‖ ^ 2) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hint_mono (by positivity))
    _ = (Real.pi ^ 2 / 2) * ∑ n ∈ I, (K_π * (n : ℝ) + 4 * (Q : ℝ) ^ 2 * T) * ‖a n‖ ^ 2 := by
        dsimp only [h]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        field_simp [hTpos.ne']
    _ ≤ 5 * ∑ n ∈ I, (80 * ((Q : ℝ) ^ 2 * T + (n : ℝ))) * ‖a n‖ ^ 2 := by
        refine mul_le_mul hpi2_le ?_ ?_ (by norm_num)
        · refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hQ2T : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * T := by positivity
          nlinarith
        · exact Finset.sum_nonneg fun n _ => mul_nonneg (by dsimp only [K_π]; positivity) (sq_nonneg _)
    _ = 400 * ∑ n ∈ I, ((Q : ℝ) ^ 2 * T + (n : ℝ)) * ‖a n‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring

/-- **Gallagher's Continuous Hybrid Large Sieve (Fixed Modulus `m`, 100% LOG-FREE!)**:
for EVERY `m ≥ 1`, `T ≥ 1`, finite `I ⊆ [1, ∞)`, and `a : ℕ → ℂ`:
`∑_{χ mod m} ∫_{-T}^T ‖∑_{n ∈ I} a n * χ(n) * n^(-I*t)‖² dt ≤ 400 * ∑_{n ∈ I} (m * T + n) * ‖a n‖²`. -/
theorem gallagher_continuous_hybrid_large_sieve_fixed_mod (m : ℕ) [NeZero m] {T : ℝ} (hT : 1 ≤ T)
    (I : Finset ℕ) (hI : ∀ n ∈ I, 1 ≤ n) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
      ∫ t in (-T)..T, ‖∑ n ∈ I, a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      400 * ∑ n ∈ I, ((m : ℝ) * T + (n : ℝ)) * ‖a n‖ ^ 2 := by
  set h : ℝ := 1 / (2 * T)
  have hh : 0 < h := by positivity
  have hTpos : 0 < T := by linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hstep1 :
      ∑ χ : DirichletCharacter ℂ m,
        ∫ t in (-T)..T, ‖∑ n ∈ I, a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 *
        ∫ x : ℝ, ∑ χ : DirichletCharacter ℂ m,
          ‖∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
            a n * χ (n : ZMod m)‖ ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun χ _ => ?_
      have hrew : ∀ t : ℝ,
          ∑ n ∈ I, a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))) =
          ∑ n ∈ I, (a n * χ (n : ZMod m)) *
            Complex.exp (-2 * Real.pi * Complex.I * (logFreq n : ℂ) * (t : ℂ)) := fun t =>
        Finset.sum_congr rfl fun n hn => by rw [nat_cpow_neg_I_mul_eq_exp_logFreq (hI n hn) t]
      simp_rw [hrew]
      exact gallagher_continuous_mean_value I logFreq (fun n => a n * χ (n : ZMod m)) hTpos
    · intro χ _
      exact integrable_short_sum_norm_sq I logFreq (fun n => a n * χ (n : ZMod m)) hh
  set K_π : ℝ := Real.pi * Real.exp Real.pi
  have hpoint : ∀ x : ℝ,
      ∑ χ : DirichletCharacter ℂ m,
        ‖∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
          a n * χ (n : ZMod m)‖ ^ 2 ≤
      ∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h),
        (K_π * ((n : ℝ) / T) + 2 * (m : ℝ)) * ‖a n‖ ^ 2 := by
    intro x
    set Sx : Finset ℕ := I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h)
    obtain ⟨hsub, hy_lt, hlen⟩ := short_logFreq_window_subset hI hT x
    set y : ℝ := Real.exp (2 * Real.pi * x)
    set M₁ : ℕ := ⌊y⌋₊ + 1
    set M₂ : ℕ := ⌊y * Real.exp (Real.pi / T)⌋₊
    let c : ℕ → ℂ := fun n => if n ∈ Sx then a n else 0
    have hIco_sub : Finset.Icc M₁ M₂ ⊆ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)) := by
      intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ico]; omega
    have hsub' : Sx ⊆ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)) := hsub.trans hIco_sub
    have hsum_eq : ∀ χ : DirichletCharacter ℂ m,
        ∑ n ∈ Sx, a n * χ (n : ZMod m) =
        ∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * χ (n : ZMod m) := by
      intro χ; symm
      rw [← Finset.sum_subset hsub']
      · refine Finset.sum_congr rfl fun n hn => by simp [c, hn]
      · intro n _ hn; simp [c, hn]
    have hnorm_le :
        ∑ n ∈ (Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁))).filter (fun n : ℕ => IsUnit (n : ZMod m)), ‖c n‖ ^ 2 ≤
        ∑ n ∈ Sx, ‖a n‖ ^ 2 := by
      calc ∑ n ∈ (Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁))).filter (fun n : ℕ => IsUnit (n : ZMod m)), ‖c n‖ ^ 2
          ≤ ∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), ‖c n‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
        _ = ∑ n ∈ Sx, ‖a n‖ ^ 2 := by
            rw [← Finset.sum_subset hsub']
            · refine Finset.sum_congr rfl fun n hn => by simp [c, hn]
            · intro n _ hn; simp [c, hn]
    simp_rw [hsum_eq]
    have hms := Stage2BehrendSieve.dirichlet_mean_square_Ico_sharp (q := m) M₁ (M₂ + 1 - M₁) c
    have hphi_le : (Nat.totient m : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.totient_le m
    have hratio_le : (Nat.totient m : ℝ) / (m : ℝ) ≤ 1 :=
      (div_le_one (by linarith)).mpr hphi_le
    have hcoeff : (Nat.totient m : ℝ) + (Nat.totient m : ℝ) / (m : ℝ) * ((M₂ + 1 - M₁ : ℕ) : ℝ) ≤
        K_π * (y / T) + 2 * (m : ℝ) := by
      have h1 : (Nat.totient m : ℝ) / (m : ℝ) * ((M₂ + 1 - M₁ : ℕ) : ℝ) ≤ ((M₂ + 1 - M₁ : ℕ) : ℝ) :=
        mul_le_of_le_one_left (Nat.cast_nonneg _) hratio_le
      dsimp only [K_π]; linarith
    calc ∑ χ : DirichletCharacter ℂ m, ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * χ (n : ZMod m)‖ ^ 2
        ≤ ((Nat.totient m : ℝ) + (Nat.totient m : ℝ) / (m : ℝ) * ((M₂ + 1 - M₁ : ℕ) : ℝ)) *
            ∑ n ∈ (Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁))).filter (fun n : ℕ => IsUnit (n : ZMod m)), ‖c n‖ ^ 2 := hms
      _ ≤ (K_π * (y / T) + 2 * (m : ℝ)) * ∑ n ∈ Sx, ‖a n‖ ^ 2 :=
          mul_le_mul hcoeff hnorm_le (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by dsimp only [K_π]; positivity)
      _ = ∑ n ∈ Sx, (K_π * (y / T) + 2 * (m : ℝ)) * ‖a n‖ ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ Sx, (K_π * ((n : ℝ) / T) + 2 * (m : ℝ)) * ‖a n‖ ^ 2 := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hyn : y ≤ (n : ℝ) := (hy_lt n hn).le
          have hdiv : y / T ≤ (n : ℝ) / T := div_le_div_of_nonneg_right hyn hTpos.le
          have hK_nn : 0 ≤ K_π := by dsimp only [K_π]; positivity
          nlinarith
  have hint_lhs : Integrable (fun x : ℝ => ∑ χ : DirichletCharacter ℂ m,
      ‖∑ n ∈ I.filter (fun n => x < logFreq n ∧ logFreq n ≤ x + h), a n * χ (n : ZMod m)‖ ^ 2) :=
    MeasureTheory.integrable_finsetSum _ fun χ _ =>
      integrable_short_sum_norm_sq I logFreq (fun n => a n * χ (n : ZMod m)) hh
  obtain ⟨hint_rhs, hrhs_eq⟩ := integral_short_sum_weight I logFreq
    (fun n => (K_π * ((n : ℝ) / T) + 2 * (m : ℝ)) * ‖a n‖ ^ 2) hh
  have hint_mono := MeasureTheory.integral_mono hint_lhs hint_rhs hpoint
  rw [hrhs_eq] at hint_mono
  have hpi_le : Real.pi ≤ 315 / 100 := by linarith [Real.pi_lt_d2]
  have hexp_pi_le : Real.exp Real.pi ≤ 252 / 10 := by
    have he1 : Real.exp 1 ≤ 272 / 100 := by linarith [Real.exp_one_lt_d9]
    have h1 : Real.exp Real.pi ≤ Real.exp (16 / 5 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith [Real.pi_lt_d2])
    have h2 : Real.exp (16 / 5 : ℝ) = Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) := by
      rw [← Real.exp_add]; congr 1; norm_num
    have h3 : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
      have hinv : 1 - (1 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 5 : ℝ))]
      have hmul := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (1 / 5 : ℝ)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      linarith
    have hpow3 : (Real.exp 1) ^ 3 ≤ (272 / 100 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1 3
    have hprod : Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) ≤ (272 / 100 : ℝ) ^ 3 * (5 / 4) := by
      rw [h3]
      exact mul_le_mul hpow3 h4 (Real.exp_pos _).le (by positivity)
    linarith [show (272 / 100 : ℝ) ^ 3 * (5 / 4) ≤ 252 / 10 by norm_num]
  have hKpi_le : K_π ≤ 80 := by
    dsimp only [K_π]; nlinarith [Real.pi_pos, Real.exp_pos Real.pi]
  have hpi2_le : Real.pi ^ 2 / 2 ≤ 5 := by nlinarith [Real.pi_pos]
  calc ∑ χ : DirichletCharacter ℂ m,
        ∫ t in (-T)..T, ‖∑ n ∈ I, a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ Real.pi ^ 2 * T ^ 2 * (h * ∑ n ∈ I, (K_π * ((n : ℝ) / T) + 2 * (m : ℝ)) * ‖a n‖ ^ 2) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hint_mono (by positivity))
    _ = (Real.pi ^ 2 / 2) * ∑ n ∈ I, (K_π * (n : ℝ) + 2 * (m : ℝ) * T) * ‖a n‖ ^ 2 := by
        dsimp only [h]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        field_simp [hTpos.ne']
    _ ≤ 5 * ∑ n ∈ I, (80 * ((m : ℝ) * T + (n : ℝ))) * ‖a n‖ ^ 2 := by
        refine mul_le_mul hpi2_le ?_ ?_ (by norm_num)
        · refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hmT : (0 : ℝ) ≤ (m : ℝ) * T := by positivity
          nlinarith
        · exact Finset.sum_nonneg fun n _ => mul_nonneg (by dsimp only [K_π]; positivity) (sq_nonneg _)
    _ = 400 * ∑ n ∈ I, ((m : ℝ) * T + (n : ℝ)) * ‖a n‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring

/-- Derivative helper for phase-shifted Dirichlet polynomials `M₁^{I * u} * ∑_{n ∈ I} c n * n^(-I * u)`. -/
private lemma hasDerivAt_shifted_dirichletPoly {I : Finset ℕ} (hI : ∀ n ∈ I, 1 ≤ n)
    {M₁ : ℕ} (hM₁ : 1 ≤ M₁) (c : ℕ → ℂ) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => (M₁ : ℂ) ^ (Complex.I * (x : ℂ)) * ∑ n ∈ I, c n * (n : ℂ) ^ (-(Complex.I * (x : ℂ))))
      ((M₁ : ℂ) ^ (Complex.I * (u : ℂ)) *
        ∑ n ∈ I, ((-Complex.I * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)) * c n) *
          (n : ℂ) ^ (-(Complex.I * (u : ℂ)))) u := by
  have hM₁_pos : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM₁_C : (M₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrew : (fun x : ℝ => (M₁ : ℂ) ^ (Complex.I * (x : ℂ)) *
        ∑ n ∈ I, c n * (n : ℂ) ^ (-(Complex.I * (x : ℂ)))) =
      fun x : ℝ => ∑ n ∈ I, c n * Complex.exp (-Complex.I * (x : ℂ) * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)) := by
    funext x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (hI n hn)
    have hn_C : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hI n hn; omega)
    rw [Complex.cpow_def_of_ne_zero hM₁_C, Complex.cpow_def_of_ne_zero hn_C,
      ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hM₁_pos.le, ← Complex.ofReal_log hn_pos.le,
      Real.log_div hn_pos.ne' hM₁_pos.ne']
    calc Complex.exp ((Real.log (M₁ : ℝ) : ℂ) * (Complex.I * (x : ℂ))) *
          (c n * Complex.exp ((Real.log (n : ℝ) : ℂ) * -(Complex.I * (x : ℂ))))
        = c n * (Complex.exp ((Real.log (M₁ : ℝ) : ℂ) * (Complex.I * (x : ℂ))) *
            Complex.exp ((Real.log (n : ℝ) : ℂ) * -(Complex.I * (x : ℂ)))) := by ring
      _ = c n * Complex.exp (-Complex.I * (x : ℂ) * ((Real.log (n : ℝ) - Real.log (M₁ : ℝ) : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]; congr 2; push_cast; ring
  have hrew_val :
      (M₁ : ℂ) ^ (Complex.I * (u : ℂ)) *
        ∑ n ∈ I, ((-Complex.I * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)) * c n) *
          (n : ℂ) ^ (-(Complex.I * (u : ℂ))) =
      ∑ n ∈ I, ((-Complex.I * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)) * c n) *
        Complex.exp (-Complex.I * (u : ℂ) * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (hI n hn)
    have hn_C : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hI n hn; omega)
    rw [Complex.cpow_def_of_ne_zero hM₁_C, Complex.cpow_def_of_ne_zero hn_C,
      ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hM₁_pos.le, ← Complex.ofReal_log hn_pos.le,
      Real.log_div hn_pos.ne' hM₁_pos.ne']
    calc Complex.exp ((Real.log (M₁ : ℝ) : ℂ) * (Complex.I * (u : ℂ))) *
          ((-Complex.I * ((Real.log (n : ℝ) - Real.log (M₁ : ℝ) : ℝ) : ℂ) * c n) *
            Complex.exp ((Real.log (n : ℝ) : ℂ) * -(Complex.I * (u : ℂ))))
        = (-Complex.I * ((Real.log (n : ℝ) - Real.log (M₁ : ℝ) : ℝ) : ℂ) * c n) *
            (Complex.exp ((Real.log (M₁ : ℝ) : ℂ) * (Complex.I * (u : ℂ))) *
              Complex.exp ((Real.log (n : ℝ) : ℂ) * -(Complex.I * (u : ℂ)))) := by ring
      _ = (-Complex.I * ((Real.log (n : ℝ) - Real.log (M₁ : ℝ) : ℝ) : ℂ) * c n) *
            Complex.exp (-Complex.I * (u : ℂ) * ((Real.log (n : ℝ) - Real.log (M₁ : ℝ) : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]; congr 2; push_cast; ring
  rw [hrew, hrew_val]
  refine HasDerivAt.fun_sum fun n _ => ?_
  have hlin : HasDerivAt (fun x : ℝ => -Complex.I * (x : ℂ) * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ))
      (-Complex.I * (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)) u := by
    have hid := (hasDerivAt_id u).ofReal_comp
    refine ((hid.const_mul (-Complex.I)).mul_const (Real.log ((n : ℝ) / (M₁ : ℝ)) : ℂ)).congr_deriv ?_
    simp only [Complex.ofReal_one, mul_one]
  refine (hlin.cexp.const_mul (c n)).congr_deriv ?_
  ring

private lemma norm_nat_cpow_I_mul {M : ℕ} (hM : 1 ≤ M) (u : ℝ) :
    ‖(M : ℂ) ^ (Complex.I * (u : ℂ))‖ = 1 := by
  have hM0 : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hMC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hM0.le,
    show (Real.log (M : ℝ) : ℂ) * (Complex.I * (u : ℂ)) =
      ((Real.log (M : ℝ) * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

open Classical in
/-- **Gallagher's Discrete Hybrid Large Sieve on a Dyadic Window `Icc M (2 * M)` (100% LOG-FREE!)**:
for EVERY `Q ≥ 1`, `T ≥ 1`, `M ≥ 1`, `a : ℕ → ℂ`, and ANY `1`-well-spaced finite sets `S_χ ⊆ [-T, T]`:
`∑_{q ≤ Q} ∑*_{χ mod q} ∑_{t ∈ S_χ} ‖∑_{n ∈ Icc M (2*M)} a n * χ(n) * n^(-I*t)‖² ≤ 4800 * (Q² T + M) * ∑_{n ∈ Icc M (2*M)} ‖a n‖²`. -/
theorem gallagher_hybrid_large_sieve_dyadic (Q M : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M) {T : ℝ} (hT : 1 ≤ T)
    (S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℝ)
    (hbd : ∀ k ∈ Finset.range Q, ∀ χ : DirichletCharacter ℂ (k + 1), ∀ t ∈ S k χ, |t| ≤ T)
    (hsep : ∀ k ∈ Finset.range Q, ∀ χ : DirichletCharacter ℂ (k + 1),
      ∀ t₁ ∈ S k χ, ∀ t₂ ∈ S k χ, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|)
    (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ∑ t ∈ S k χ,
          ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      4800 * ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 := by
  classical
  have hI : ∀ n ∈ Finset.Icc M (2 * M), 1 ≤ n := fun n hn => le_trans hM (Finset.mem_Icc.mp hn).1
  set T' : ℝ := T + 1 / 2
  have hT'1 : 1 ≤ T' := by dsimp only [T']; linarith
  have hT'_le : T' ≤ 2 * T := by dsimp only [T']; linarith
  let a' : ℕ → ℂ := fun n => (-Complex.I * (Real.log ((n : ℝ) / (M : ℝ)) : ℂ)) * a n
  have hsobolev :
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∑ t ∈ S k χ,
            ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      2 * (∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∫ u in (-T')..T', ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ ^ 2) +
      (∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∫ u in (-T')..T', ‖∑ n ∈ Finset.Icc M (2 * M), a' n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun χ _ => ?_
    let f : ℝ → ℂ := fun u => (M : ℂ) ^ (Complex.I * (u : ℂ)) *
      ∑ n ∈ Finset.Icc M (2 * M), (a n * χ (n : ZMod (k + 1))) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))
    let f' : ℝ → ℂ := fun u => (M : ℂ) ^ (Complex.I * (u : ℂ)) *
      ∑ n ∈ Finset.Icc M (2 * M), (a' n * χ (n : ZMod (k + 1))) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))
    have hfnorm : ∀ u : ℝ, ‖f u‖ =
        ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ := by
      intro u; dsimp only [f]; rw [norm_mul, norm_nat_cpow_I_mul hM u, one_mul]
    have hf'norm : ∀ u : ℝ, ‖f' u‖ =
        ‖∑ n ∈ Finset.Icc M (2 * M), a' n * χ (n : ZMod (k + 1)) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ := by
      intro u; dsimp only [f']; rw [norm_mul, norm_nat_cpow_I_mul hM u, one_mul]
    have hf_deriv : ∀ u : ℝ, HasDerivAt f (f' u) u := fun u => by
      have hd := hasDerivAt_shifted_dirichletPoly hI hM (fun n => a n * χ (n : ZMod (k + 1))) u
      refine hd.congr_deriv ?_
      dsimp only [f', a']
      congr 1; refine Finset.sum_congr rfl fun n _ => by ring
    have hf'_cont : Continuous f' := by
      have hM_C : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hM_cont : Continuous (fun u : ℝ => (M : ℂ) ^ (Complex.I * (u : ℂ))) := by
        have hrew : (fun u : ℝ => (M : ℂ) ^ (Complex.I * (u : ℂ))) =
            fun u : ℝ => Complex.exp (Complex.log (M : ℂ) * (Complex.I * (u : ℂ))) := by
          funext u; rw [Complex.cpow_def_of_ne_zero hM_C]
        rw [hrew]; fun_prop
      refine hM_cont.mul (continuous_finsetSum _ fun n hn => continuous_const.mul ?_)
      have hrew : (fun u : ℝ => (n : ℂ) ^ (-(Complex.I * (u : ℂ)))) =
          fun u : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (logFreq n : ℂ) * (u : ℂ)) := by
        funext u; exact nat_cpow_neg_I_mul_eq_exp_logFreq (hI n hn) u
      rw [hrew]; fun_prop
    have hsg := gallagher_sobolev_mean_value_weighted (S k χ) id (S := f) (S' := f')
      (T := T) (δ := 1) (α := 1) (by linarith) zero_lt_one zero_lt_one
      (hbd k hk χ) (hsep k hk χ) hf_deriv hf'_cont
    simp only [id_eq, inv_one, one_mul] at hsg
    simp_rw [hfnorm, hf'norm] at hsg
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h11] at hsg
    exact hsg
  have hc1 := gallagher_continuous_hybrid_large_sieve Q hQ hT'1 (Finset.Icc M (2 * M)) hI a
  have hc2 := gallagher_continuous_hybrid_large_sieve Q hQ hT'1 (Finset.Icc M (2 * M)) hI a'
  have ha'_le : ∀ n ∈ Finset.Icc M (2 * M), ‖a' n‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
    intro n hn
    obtain ⟨hMn, hn2M⟩ := Finset.mem_Icc.mp hn
    have hM0 : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio_ge : (1 : ℝ) ≤ (n : ℝ) / (M : ℝ) := (one_le_div hM0).mpr (by exact_mod_cast hMn)
    have hratio_le : (n : ℝ) / (M : ℝ) ≤ 2 := (div_le_iff₀ hM0).mpr (by exact_mod_cast hn2M)
    have hlog_nn : 0 ≤ Real.log ((n : ℝ) / (M : ℝ)) := Real.log_nonneg hratio_ge
    have hlog_le : Real.log ((n : ℝ) / (M : ℝ)) ≤ 1 := by
      have h1 := Real.log_le_log (by positivity) hratio_le
      linarith [Real.log_two_lt_d9]
    dsimp only [a']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hlog_nn, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  have hsum_bd : ∑ n ∈ Finset.Icc M (2 * M), ((Q : ℝ) ^ 2 * T' + (n : ℝ)) * ‖a n‖ ^ 2 ≤
      2 * ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hn2M : (n : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    nlinarith [sq_nonneg (Q : ℝ)]
  have hsum_bd' : ∑ n ∈ Finset.Icc M (2 * M), ((Q : ℝ) ^ 2 * T' + (n : ℝ)) * ‖a' n‖ ^ 2 ≤
      2 * ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 := by
    refine (Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (ha'_le n hn) (by positivity)).trans hsum_bd
  have htot :
      2 * (400 * (2 * ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2)) +
      400 * (2 * ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2) =
      2400 * ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 := by ring
  have hsum_nn : 0 ≤ ((Q : ℝ) ^ 2 * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith

/-- **Gallagher's Discrete Hybrid Large Sieve (Fixed Modulus `m`, Dyadic Window `Icc M (2 * M)`, 100% LOG-FREE!)**. -/
theorem gallagher_hybrid_large_sieve_fixed_mod_dyadic (m M : ℕ) [NeZero m] (hM : 1 ≤ M)
    {T : ℝ} (hT : 1 ≤ T)
    (S : DirichletCharacter ℂ m → Finset ℝ)
    (hbd : ∀ χ : DirichletCharacter ℂ m, ∀ t ∈ S χ, |t| ≤ T)
    (hsep : ∀ χ : DirichletCharacter ℂ m, ∀ t₁ ∈ S χ, ∀ t₂ ∈ S χ, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|)
    (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
      ∑ t ∈ S χ,
        ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      4800 * ((m : ℝ) * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 := by
  have hI : ∀ n ∈ Finset.Icc M (2 * M), 1 ≤ n := fun n hn => le_trans hM (Finset.mem_Icc.mp hn).1
  set T' : ℝ := T + 1 / 2
  have hT'1 : 1 ≤ T' := by dsimp only [T']; linarith
  have hT'_le : T' ≤ 2 * T := by dsimp only [T']; linarith
  let a' : ℕ → ℂ := fun n => (-Complex.I * (Real.log ((n : ℝ) / (M : ℝ)) : ℂ)) * a n
  have hsobolev :
      ∑ χ : DirichletCharacter ℂ m,
        ∑ t ∈ S χ,
          ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      2 * (∑ χ : DirichletCharacter ℂ m,
        ∫ u in (-T')..T', ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ ^ 2) +
      (∑ χ : DirichletCharacter ℂ m,
        ∫ u in (-T')..T', ‖∑ n ∈ Finset.Icc M (2 * M), a' n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun χ _ => ?_
    let f : ℝ → ℂ := fun u => (M : ℂ) ^ (Complex.I * (u : ℂ)) *
      ∑ n ∈ Finset.Icc M (2 * M), (a n * χ (n : ZMod m)) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))
    let f' : ℝ → ℂ := fun u => (M : ℂ) ^ (Complex.I * (u : ℂ)) *
      ∑ n ∈ Finset.Icc M (2 * M), (a' n * χ (n : ZMod m)) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))
    have hfnorm : ∀ u : ℝ, ‖f u‖ =
        ‖∑ n ∈ Finset.Icc M (2 * M), a n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ := by
      intro u; dsimp only [f]; rw [norm_mul, norm_nat_cpow_I_mul hM u, one_mul]
    have hf'norm : ∀ u : ℝ, ‖f' u‖ =
        ‖∑ n ∈ Finset.Icc M (2 * M), a' n * χ (n : ZMod m) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖ := by
      intro u; dsimp only [f']; rw [norm_mul, norm_nat_cpow_I_mul hM u, one_mul]
    have hf_deriv : ∀ u : ℝ, HasDerivAt f (f' u) u := fun u => by
      have hd := hasDerivAt_shifted_dirichletPoly hI hM (fun n => a n * χ (n : ZMod m)) u
      refine hd.congr_deriv ?_
      dsimp only [f', a']
      congr 1; refine Finset.sum_congr rfl fun n _ => by ring
    have hf'_cont : Continuous f' := by
      have hM_C : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hM_cont : Continuous (fun u : ℝ => (M : ℂ) ^ (Complex.I * (u : ℂ))) := by
        have hrew : (fun u : ℝ => (M : ℂ) ^ (Complex.I * (u : ℂ))) =
            fun u : ℝ => Complex.exp (Complex.log (M : ℂ) * (Complex.I * (u : ℂ))) := by
          funext u; rw [Complex.cpow_def_of_ne_zero hM_C]
        rw [hrew]; fun_prop
      refine hM_cont.mul (continuous_finsetSum _ fun n hn => continuous_const.mul ?_)
      have hrew : (fun u : ℝ => (n : ℂ) ^ (-(Complex.I * (u : ℂ)))) =
          fun u : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (logFreq n : ℂ) * (u : ℂ)) := by
        funext u; exact nat_cpow_neg_I_mul_eq_exp_logFreq (hI n hn) u
      rw [hrew]; fun_prop
    have hsg := gallagher_sobolev_mean_value_weighted (S χ) id (S := f) (S' := f')
      (T := T) (δ := 1) (α := 1) (by linarith) zero_lt_one zero_lt_one
      (hbd χ) (hsep χ) hf_deriv hf'_cont
    simp only [id_eq, inv_one, one_mul] at hsg
    simp_rw [hfnorm, hf'norm] at hsg
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h11] at hsg
    exact hsg
  have hc1 := gallagher_continuous_hybrid_large_sieve_fixed_mod m hT'1 (Finset.Icc M (2 * M)) hI a
  have hc2 := gallagher_continuous_hybrid_large_sieve_fixed_mod m hT'1 (Finset.Icc M (2 * M)) hI a'
  have ha'_le : ∀ n ∈ Finset.Icc M (2 * M), ‖a' n‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
    intro n hn
    obtain ⟨hMn, hn2M⟩ := Finset.mem_Icc.mp hn
    have hM0 : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio_ge : (1 : ℝ) ≤ (n : ℝ) / (M : ℝ) := (one_le_div hM0).mpr (by exact_mod_cast hMn)
    have hratio_le : (n : ℝ) / (M : ℝ) ≤ 2 := (div_le_iff₀ hM0).mpr (by exact_mod_cast hn2M)
    have hlog_nn : 0 ≤ Real.log ((n : ℝ) / (M : ℝ)) := Real.log_nonneg hratio_ge
    have hlog_le : Real.log ((n : ℝ) / (M : ℝ)) ≤ 1 := by
      have h1 := Real.log_le_log (by positivity) hratio_le
      linarith [Real.log_two_lt_d9]
    dsimp only [a']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hlog_nn, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  have hsum_bd : ∑ n ∈ Finset.Icc M (2 * M), ((m : ℝ) * T' + (n : ℝ)) * ‖a n‖ ^ 2 ≤
      2 * ((m : ℝ) * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hn2M : (n : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hsum_bd' : ∑ n ∈ Finset.Icc M (2 * M), ((m : ℝ) * T' + (n : ℝ)) * ‖a' n‖ ^ 2 ≤
      2 * ((m : ℝ) * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 :=
    (Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (ha'_le n hn) (by positivity)).trans hsum_bd
  have hsum_nn : 0 ≤ ((m : ℝ) * T + (M : ℝ)) * ∑ n ∈ Finset.Icc M (2 * M), ‖a n‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith

/-! ## Section 2: Prime-Weighted Large Sieve & Continuous Prime Hybrid Large Sieve -/

/-- **Fixed-Modulus Prime Large Sieve (via `Stage7SieveMethods.brun_titchmarsh_ap` + Orthogonality)**:
for EVERY `m ≥ 1`, `x, H : ℕ` with `9 * m ≤ H`, and `a : ℕ → ℂ`:
`∑_{χ mod m} ‖∑_{p ∈ (x, x + H], p prime} a p * χ(p)‖² ≤ (10 * H / log(H / m)) * ∑_{p ∈ (x, x + H], p prime} ‖a p‖²`. -/
theorem fixed_mod_prime_large_sieve (m : ℕ) [NeZero m] (x H : ℕ) (hH : 9 * m ≤ H) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
      ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * χ (p : ZMod m)‖ ^ 2 ≤
      (10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ))) *
        ∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, ‖a p‖ ^ 2 := by
  set P : Finset ℕ := (Finset.Ioc x (x + H)).filter Nat.Prime
  rw [Stage2BehrendSieve.dirichlet_parseval_residue_classes (q := m) P a]
  have hm_pos : 0 < m := NeZero.pos m
  have hmR_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hphi_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm_pos)
  have hlog_pos : 0 < Real.log ((H : ℝ) / (m : ℝ)) := by
    apply Real.log_pos
    rw [one_lt_div hmR_pos]
    have hH9 : (9 : ℝ) * (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    linarith
  have hstep :
      (m.totient : ℝ) * ∑ r : (ZMod m)ˣ, ‖∑ p ∈ P.filter (fun p : ℕ => (p : ZMod m) = (r : ZMod m)), a p‖ ^ 2 ≤
      (10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ))) *
        ∑ r : (ZMod m)ˣ, ∑ p ∈ P.filter (fun p : ℕ => (p : ZMod m) = (r : ZMod m)), ‖a p‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    set Pr : Finset ℕ := P.filter (fun p : ℕ => (p : ZMod m) = (r : ZMod m))
    have hcs := Stage2BehrendSieve.cauchy_schwarz_complex_card Pr a
    have hcop : Nat.Coprime (r : ZMod m).val m := by
      have hu : IsUnit (((r : ZMod m).val : ℕ) : ZMod m) := by
        rw [ZMod.natCast_zmod_val]; exact r.isUnit
      exact (ZMod.isUnit_iff_coprime _ m).mp hu
    have hPr_eq : Pr = (Finset.Ioc x (x + H)).filter (fun p => p.Prime ∧ p ≡ (r : ZMod m).val [MOD m]) := by
      ext p
      simp only [Pr, P, Finset.mem_filter, and_assoc]
      refine and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    have hbt := Stage7SieveMethods.brun_titchmarsh_ap hm_pos hcop x H hH
    rw [← hPr_eq] at hbt
    have hmul_bt : (m.totient : ℝ) * (Pr.card : ℝ) ≤ 10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hbt hphi_pos.le
      refine h1.trans_eq ?_
      field_simp [hphi_pos.ne', hlog_pos.ne']
    calc (m.totient : ℝ) * ‖∑ p ∈ Pr, a p‖ ^ 2
        ≤ (m.totient : ℝ) * ((Pr.card : ℝ) * ∑ p ∈ Pr, ‖a p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hphi_pos.le
      _ = ((m.totient : ℝ) * (Pr.card : ℝ)) * ∑ p ∈ Pr, ‖a p‖ ^ 2 := by ring
      _ ≤ (10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ))) * ∑ p ∈ Pr, ‖a p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmul_bt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hdisj_sum :
      ∑ r : (ZMod m)ˣ, ∑ p ∈ P.filter (fun p : ℕ => (p : ZMod m) = (r : ZMod m)), ‖a p‖ ^ 2 =
      ∑ p ∈ P.filter (fun p : ℕ => IsUnit (p : ZMod m)), ‖a p‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hu : IsUnit (p : ZMod m)
    · obtain ⟨r₀, hr₀⟩ := hu
      rw [if_pos ⟨r₀, hr₀⟩, Finset.sum_eq_single r₀]
      · rw [if_pos hr₀.symm]
      · intro r _ hne; exact if_neg fun h => hne (Units.ext (h.symm.trans hr₀.symm))
      · intro h; exact absurd (Finset.mem_univ r₀) h
    · rw [if_neg hu]
      exact Finset.sum_eq_zero fun r _ =>
        if_neg fun (h : (p : ZMod m) = (r : ZMod m)) => hu (h.symm ▸ r.isUnit)
  rw [hdisj_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- Elementary non-principal character sum bound on `Finset.Ioc a b`:
for every `q ≥ 1` and non-principal `χ ≠ 1` mod `q`, `‖∑ n ∈ Finset.Ioc a b, χ n‖ ≤ q`. -/
private lemma norm_sum_nonprincipal_char_Ioc_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ioc a b, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  have hq_pos : 0 < q := NeZero.pos q
  -- First prove `∑ x : ZMod q, χ x = 0` directly from `χ ≠ 1`
  have hsum_zero : ∑ x : ZMod q, χ x = 0 := by
    have hex : ∃ u : (ZMod q)ˣ, χ (u : ZMod q) ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hχ
      refine MulChar.ext fun u => ?_
      rw [hall u, MulChar.one_apply u.isUnit]
    obtain ⟨u, hu⟩ := hex
    have hmul : χ (u : ZMod q) * ∑ x : ZMod q, χ x = ∑ x : ZMod q, χ x := by
      rw [Finset.mul_sum]
      have h1 : ∀ x : ZMod q, χ (u : ZMod q) * χ x = χ ((u : ZMod q) * x) :=
        fun x => (map_mul χ _ _).symm
      simp_rw [h1]
      exact Fintype.sum_equiv
        { toFun := fun x : ZMod q => (u : ZMod q) * x
          invFun := fun x : ZMod q => (u⁻¹ : (ZMod q)ˣ) * x
          left_inv := fun x => by dsimp only; rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
          right_inv := fun x => by dsimp only; rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] }
        _ _ (fun _ => rfl)
    have hsub : (χ (u : ZMod q) - 1) * ∑ x : ZMod q, χ x = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hu)
  -- Period sum: for any `c : ℕ`, `∑ n ∈ Finset.Ioc c (c + q), χ n = 0`
  have hperiod : ∀ c : ℕ, ∑ n ∈ Finset.Ioc c (c + q), χ (n : ZMod q) = 0 := by
    intro c
    have hbij : ∑ n ∈ Finset.Ioc c (c + q), χ (n : ZMod q) = ∑ x : ZMod q, χ x := by
      refine Finset.sum_bij (fun n _ => (n : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro n₁ hn₁ n₂ hn₂ heq
        obtain ⟨h1a, h1b⟩ := Finset.mem_Ioc.mp hn₁
        obtain ⟨h2a, h2b⟩ := Finset.mem_Ioc.mp hn₂
        have hmod : n₁ % q = n₂ % q := (ZMod.natCast_eq_natCast_iff' n₁ n₂ q).mp heq
        rcases le_total n₁ n₂ with hle | hle
        · have hdvd : q ∣ n₂ - n₁ := (Nat.modEq_iff_dvd' hle).mp hmod
          by_contra hne
          have hpos : 0 < n₂ - n₁ := by omega
          have hge : q ≤ n₂ - n₁ := Nat.le_of_dvd hpos hdvd
          omega
        · have hdvd : q ∣ n₁ - n₂ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
          by_contra hne
          have hpos : 0 < n₁ - n₂ := by omega
          have hge : q ≤ n₁ - n₂ := Nat.le_of_dvd hpos hdvd
          omega
      · intro x _
        set r : ℕ := (x - (c + 1 : ZMod q)).val
        have hr_lt : r < q := ZMod.val_lt _
        refine ⟨c + 1 + r, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
        push_cast
        rw [ZMod.natCast_zmod_val]
        ring
      · intro _ _; rfl
    rw [hbij, hsum_zero]
  -- Any multiple of `q` has sum `0`
  have hmult : ∀ k : ℕ, ∑ n ∈ Finset.Ioc a (a + k * q), χ (n : ZMod q) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hunion : Finset.Ioc a (a + (k + 1) * q) =
          Finset.Ioc a (a + k * q) ∪ Finset.Ioc (a + k * q) (a + k * q + q) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_union]
        have : a + (k + 1) * q = a + k * q + q := by ring
        omega
      have hdisj : Disjoint (Finset.Ioc a (a + k * q)) (Finset.Ioc (a + k * q) (a + k * q + q)) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_Ioc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj, ih, hperiod, zero_add]
  by_cases hab : b ≤ a
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact Nat.cast_nonneg q
  · push Not at hab
    set k : ℕ := (b - a) / q
    set r : ℕ := (b - a) % q
    have hdiv_mod : k * q + r = b - a := by rw [mul_comm]; exact Nat.div_add_mod (b - a) q
    have hr_lt : r < q := Nat.mod_lt (b - a) hq_pos
    have hunion : Finset.Ioc a b = Finset.Ioc a (a + k * q) ∪ Finset.Ioc (a + k * q) b := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Ioc a (a + k * q)) (Finset.Ioc (a + k * q) b) := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_Ioc] at h1 h2; omega
    rw [hunion, Finset.sum_union hdisj, hmult k, zero_add]
    calc ‖∑ n ∈ Finset.Ioc (a + k * q) b, χ (n : ZMod q)‖
        ≤ ∑ n ∈ Finset.Ioc (a + k * q) b, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc (a + k * q) b, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => χ.norm_le_one _
      _ = ((Finset.Ioc (a + k * q) b).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (q : ℝ) := by
          have hcard : (Finset.Ioc (a + k * q) b).card = r := by rw [Nat.card_Ioc]; omega
          rw [hcard]; exact_mod_cast hr_lt.le

private lemma pchar_of_changeLevel_local {d N : ℕ} [NeZero d] [NeZero N] (hd : d ∣ N)
    (χ : DirichletCharacter ℂ d) (hprim : χ.IsPrimitive) :
    RHDirect.PChar.of (DirichletCharacter.changeLevel hd χ) = RHDirect.PChar.mk d χ hprim := by
  set η : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hd χ
  have hcond : η.conductor = d := (DirichletCharacter.conductor_changeLevel χ hd).trans hprim
  have : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
  have aux : ∀ (e : ℕ) [NeZero e] (φ : DirichletCharacter ℂ e) (he : e ∣ N) (hed : e = d)
      (hφ : DirichletCharacter.changeLevel he φ = DirichletCharacter.changeLevel hd χ)
      (hp : φ.IsPrimitive), RHDirect.PChar.mk e φ hp = RHDirect.PChar.mk d χ hprim := by
    intro e _ φ he hed hφ hp
    subst hed
    have hq : φ = χ := DirichletCharacter.changeLevel_injective hd hφ
    subst hq
    rfl
  exact aux η.conductor η.primitiveCharacter η.conductor_dvd_level hcond
    η.changeLevel_primitiveCharacter η.primitiveCharacter_isPrimitive

/-- Non-principality of `prodChar χ₁ χ₂⁻¹` for ANY two distinct primitive Dirichlet characters
`⟨k₁, χ₁⟩ ≠ ⟨k₂, χ₂⟩`. -/
private lemma prodChar_inv_ne_one_of_distinct_primitive
    {p₁ p₂ : Σ k : ℕ, DirichletCharacter ℂ (k + 1)}
    (h1 : p₁.2.IsPrimitive) (h2 : p₂.2.IsPrimitive) (hne : p₁ ≠ p₂) :
    prodChar p₁.2 p₂.2⁻¹ ≠ 1 := by
  intro hprod
  unfold prodChar at hprod
  have hinv_eq :
      DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2 =
      DirichletCharacter.changeLevel (dvd_mul_right (p₁.1 + 1) (p₂.1 + 1)) p₁.2 := by
    have hmul :
        DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2⁻¹ *
        DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2 = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2
        = 1 * DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2 := (one_mul _).symm
      _ = (DirichletCharacter.changeLevel (dvd_mul_right (p₁.1 + 1) (p₂.1 + 1)) p₁.2 *
            DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2⁻¹) *
            DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2 := by rw [hprod]
      _ = DirichletCharacter.changeLevel (dvd_mul_right (p₁.1 + 1) (p₂.1 + 1)) p₁.2 *
            (DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2⁻¹ *
              DirichletCharacter.changeLevel (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2) := mul_assoc _ _ _
      _ = DirichletCharacter.changeLevel (dvd_mul_right (p₁.1 + 1) (p₂.1 + 1)) p₁.2 := by
          rw [hmul, mul_one]
  have hof := congrArg RHDirect.PChar.of hinv_eq
  rw [pchar_of_changeLevel_local (dvd_mul_left (p₂.1 + 1) (p₁.1 + 1)) p₂.2 h2,
      pchar_of_changeLevel_local (dvd_mul_right (p₁.1 + 1) (p₂.1 + 1)) p₁.2 h1] at hof
  apply hne
  rcases p₁ with ⟨k₁, χ₁⟩
  rcases p₂ with ⟨k₂, χ₂⟩
  have hN : k₂ + 1 = k₁ + 1 := congrArg RHDirect.PChar.N hof
  have hk : k₁ = k₂ := by omega
  subst hk
  have hχ : χ₂ = χ₁ := by cases hof; rfl
  subst hχ
  rfl

/-- Elementary bound `Real.log x ≤ 6 * x ^ (1 / 6)` for all `x > 0`. -/
private lemma log_le_six_mul_rpow_sixth {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 6 * x ^ (1 / 6 : ℝ) := by
  have h1 : Real.log (x ^ (1 / 6 : ℝ)) ≤ x ^ (1 / 6 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx _)
  rw [Real.log_rpow hx] at h1
  linarith

open Classical in
/-- **Primitive-Character Prime Large Sieve (via Duality + `Stage7SieveMethods` Optimal Selberg Sieve)**:
for EVERY `Q ≥ 1`, `x, H : ℕ` with `max (Q ^ 12) 16 ≤ H` and `⌊H^(1/4)⌋₊ ≤ x`, and ANY `a : ℕ → ℂ`:
`∑_{q ≤ Q} ∑*_{χ mod q} ‖∑_{p ∈ (x, x + H], p prime} a p * χ(p)‖² ≤ (20 * H / log H) * ∑_{p ∈ (x, x + H], p prime} ‖a p‖²`. -/
theorem primitive_prime_large_sieve (Q : ℕ) (hQ : 1 ≤ Q) (x H : ℕ)
    (hHQ : Q ^ 12 ≤ H) (hH16 : 16 ≤ H) (hzx : ⌊(H : ℝ) ^ (1 / 4 : ℝ)⌋₊ ≤ x) (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * χ (p : ZMod (k + 1))‖ ^ 2 ≤
      (20 * (H : ℝ) / Real.log (H : ℝ)) *
        ∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, ‖a p‖ ^ 2 := by
  set P : Finset ℕ := (Finset.Ioc x (x + H)).filter Nat.Prime
  set J : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) := Stage3BombieriVinogradov.primCharsUpTo Q
  have hHR_pos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogH_pos : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  set Δ : ℝ := 20 * (H : ℝ) / Real.log (H : ℝ)
  have hΔ_nn : 0 ≤ Δ := by positivity
  -- Rewrite LHS as sum over `J = primCharsUpTo Q` and apply `Stage2BehrendSieve.duality_principle`!
  rw [← Stage3BombieriVinogradov.sum_primCharsUpTo Q
    (fun j => ‖∑ p ∈ P, a p * j.2 (p : ZMod (j.1 + 1))‖ ^ 2)]
  have hswap : ∀ j : Σ k : ℕ, DirichletCharacter ℂ (k + 1),
      ∑ p ∈ P, a p * j.2 (p : ZMod (j.1 + 1)) = ∑ p ∈ P, j.2 (p : ZMod (j.1 + 1)) * a p :=
    fun j => Finset.sum_congr rfl fun p _ => mul_comm _ _
  simp_rw [hswap]
  refine Stage2BehrendSieve.duality_principle P J (fun j p => j.2 (p : ZMod (j.1 + 1))) hΔ_nn ?_ a
  -- Prove the dual inequality: `∑ p ∈ P, ‖∑ j ∈ J, conj(j.2 p) * b j‖² ≤ Δ * ∑ j ∈ J, ‖b j‖²`!
  intro b
  -- Choose Selberg sieve level `z = ⌊H^(1/4)⌋₊` with density `g(d) = 1 / d`
  set z : ℕ := ⌊(H : ℝ) ^ (1 / 4 : ℝ)⌋₊
  have hz_ge2 : 2 ≤ z := by
    refine Nat.le_floor ?_
    have h16 : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      rw [h1, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [Nat.cast_ofNat, h16]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hH16) (by norm_num)
  have hz1 : 1 ≤ z := by omega
  have hz_le : (z : ℝ) ≤ (H : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
  have hz_gt : (H : ℝ) ^ (1 / 4 : ℝ) < (z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hz_lt_H : z < H := by
    have hlt : (H : ℝ) ^ (1 / 4 : ℝ) < (H : ℝ) := by
      have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
      calc (H : ℝ) ^ (1 / 4 : ℝ) < (H : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hH1 (by norm_num)
        _ = (H : ℝ) := Real.rpow_one _
    have : (z : ℝ) < (H : ℝ) := hz_le.trans_lt hlt
    exact_mod_cast this
  let g : ℕ → ℝ := fun d => if d = 0 then 0 else (1 : ℝ) / (d : ℝ)
  have hg : Stage7SieveMethods.IsSelbergDensity g := by
    refine ⟨by simp [g], fun a b => ?_, fun p hp => ?_⟩
    · by_cases ha : a = 0
      · subst ha; simp [g]
      · by_cases hb : b = 0
        · subst hb; simp [g]
        · simp [g, ha, hb, mul_ne_zero ha hb]; ring
    · have hp0 : p ≠ 0 := hp.ne_zero
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      simp only [g, hp0, ↓reduceIte]
      exact ⟨by positivity, (div_lt_one (by linarith)).mpr hp1⟩
  let lam : ℕ → ℝ := Stage7SieveMethods.selbergOptLam z g
  have hlam1 : lam 1 = 1 := Stage7SieveMethods.selbergOptLam_one hz1 hg
  have hlam_sqf : ∀ d, ¬ Squarefree d → lam d = 0 :=
    Stage7SieveMethods.selbergOptLam_eq_zero_of_not_squarefree z g
  have hlam_abs : ∀ d, |lam d| ≤ 1 := Stage7SieveMethods.abs_selbergOptLam_le_one hz1 hg
  -- Step 1: Majorize prime indicator on `P` by Selberg weight `w(n) = (∑_{d ≤ z, d ∣ n} lam d)^2`
  let w : ℕ → ℝ := fun n => (∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n), lam d) ^ 2
  have hw_prime : ∀ p ∈ P, w p = 1 := by
    intro p hp
    obtain ⟨hpI, hpPr⟩ := Finset.mem_filter.mp hp
    have hp_gt_z : z < p := lt_of_le_of_lt hzx (Finset.mem_Ioc.mp hpI).1
    have hfilt : (Finset.Icc 1 z).filter (fun d => d ∣ p) = {1} := by
      ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd1, hdz⟩, hdp⟩
        rcases hpPr.eq_one_or_self_of_dvd d hdp with rfl | rfl
        · rfl
        · omega
      · rintro rfl; exact ⟨⟨le_rfl, hz1⟩, one_dvd p⟩
    dsimp only [w]; rw [hfilt, Finset.sum_singleton, hlam1, one_pow]
  have hmaj :
      ∑ p ∈ P, ‖∑ j ∈ J, starRingEnd ℂ (j.2 (p : ZMod (j.1 + 1))) * b j‖ ^ 2 ≤
      ∑ n ∈ Finset.Ioc x (x + H), w n * ‖∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j‖ ^ 2 := by
    calc ∑ p ∈ P, ‖∑ j ∈ J, starRingEnd ℂ (j.2 (p : ZMod (j.1 + 1))) * b j‖ ^ 2
        = ∑ p ∈ P, w p * ‖∑ j ∈ J, starRingEnd ℂ (j.2 (p : ZMod (j.1 + 1))) * b j‖ ^ 2 :=
          Finset.sum_congr rfl fun p hp => by rw [hw_prime p hp, one_mul]
      _ ≤ ∑ n ∈ Finset.Ioc x (x + H), w n * ‖∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by
            dsimp only [w]; positivity
  -- Step 2: Expand `‖∑_j‖^2` and split into diagonal (`j₁ = j₂`) and off-diagonal (`j₁ ≠ j₂`)!
  have hexp :
      ∑ n ∈ Finset.Ioc x (x + H), w n * ‖∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j‖ ^ 2 =
      (∑ j₁ ∈ J, ∑ j₂ ∈ J, b j₁ * starRingEnd ℂ (b j₂) *
        ∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) *
          (starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₂.2 (n : ZMod (j₂.1 + 1)))).re := by
    have hpt : ∀ n ∈ Finset.Ioc x (x + H),
        w n * ‖∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j‖ ^ 2 =
        (∑ j₁ ∈ J, ∑ j₂ ∈ J, b j₁ * starRingEnd ℂ (b j₂) *
          (((w n : ℝ) : ℂ) * (starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₂.2 (n : ZMod (j₂.1 + 1))))).re := by
      intro n _
      have hsq : (w n * ‖∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j‖ ^ 2 : ℝ) =
          (((w n : ℝ) : ℂ) * ((∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j) *
            starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (j.2 (n : ZMod (j.1 + 1))) * b j))).re := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hsq]
      congr 1
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]; ring
    rw [Finset.sum_congr rfl hpt, ← Complex.re_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₂ _ => (Finset.mul_sum _ _ _).symm
  -- Step 3: Bound diagonal sum `∑_{n ∈ Ioc x (x+H)} w n ≤ H / G(z) + z^2` via `selberg_upper_bound_sieve`!
  have hG_ge : (1 / 4 : ℝ) * Real.log (H : ℝ) ≤ Stage7SieveMethods.selbergG g z := by
    have hG_eq : Stage7SieveMethods.selbergG g z =
        ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (r.totient : ℝ) := by
      unfold Stage7SieveMethods.selbergG
      refine Finset.sum_congr rfl fun r hr => ?_
      have hrsqf : Squarefree r := (Finset.mem_filter.mp hr).2
      have hF_eq : Stage7SieveMethods.selbergF g r = (r.totient : ℝ) := by
        unfold Stage7SieveMethods.selbergF
        have h1 : ∏ p ∈ r.primeFactors, (1 / g p - 1) = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
          simp [g, hp0]
        rw [h1]
        have htot := Stage7SieveMethods.sieveWeight_one_eq_inv_totient hrsqf
        simp only [Stage7SieveMethods.sieveWeight, hrsqf, ↓reduceIte, Nat.cast_one] at htot
        have hprod_pos : 0 < ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos fun p hp => by
          have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          linarith
        have htot_pos : (0 : ℝ) < (r.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hrsqf.ne_zero))
        have hinv : (∏ p ∈ r.primeFactors, ((p : ℝ) - 1))⁻¹ = (r.totient : ℝ)⁻¹ := by
          rw [← Finset.prod_inv_distrib]
          simpa only [one_div] using htot
        exact inv_injective hinv
      rw [hF_eq]
    rw [hG_eq]
    have h1 := Stage7SieveMethods.log_add_one_le_sum_squarefree_inv_totient z
    have h2 : (1 / 4 : ℝ) * Real.log (H : ℝ) ≤ Real.log ((z : ℝ) + 1) := by
      rw [← Real.log_rpow hHR_pos]
      exact Real.log_le_log (by positivity) hz_gt.le
    linarith
  have hG_pos : 0 < Stage7SieveMethods.selbergG g z := lt_of_lt_of_le (by positivity) hG_ge
  have hdiag : ∑ n ∈ Finset.Ioc x (x + H), w n ≤ 4 * (H : ℝ) / Real.log (H : ℝ) + (z : ℝ) ^ 2 := by
    have hModel : ∀ d : ℕ, Squarefree d →
        (((Finset.Ioc x (x + H)).filter (fun n => d ∣ n)).card : ℝ) =
        (H : ℝ) * g d + ((((Finset.Ioc x (x + H)).filter (fun n => d ∣ n)).card : ℝ) - (H : ℝ) * g d) :=
      fun _ _ => by ring
    -- Expand `∑ w n = H * Q(lam) + ∑_{d₁,d₂} lam d₁ * lam d₂ * R([d₁, d₂])` directly!
    have hexp_w : ∑ n ∈ Finset.Ioc x (x + H), w n =
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          lam d₁ * lam d₂ * (((Finset.Ioc x (x + H)).filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) := by
      calc ∑ n ∈ Finset.Ioc x (x + H), w n
          = ∑ n ∈ Finset.Ioc x (x + H), ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
              if d₁ ∣ n ∧ d₂ ∣ n then lam d₁ * lam d₂ else 0 := by
            refine Finset.sum_congr rfl fun n _ => ?_
            dsimp only [w]
            rw [sq, Finset.sum_mul, Finset.sum_filter]
            refine Finset.sum_congr rfl fun d₁ _ => ?_
            by_cases h1 : d₁ ∣ n
            · rw [if_pos h1, Finset.mul_sum, Finset.sum_filter]
              refine Finset.sum_congr rfl fun d₂ _ => by by_cases h2 : d₂ ∣ n <;> simp [h1, h2]
            · rw [if_neg h1]; exact (Finset.sum_eq_zero fun d₂ _ => if_neg (fun h => h1 h.1)).symm
        _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Ioc x (x + H), ∑ d₂ ∈ Finset.Icc 1 z,
              if d₁ ∣ n ∧ d₂ ∣ n then lam d₁ * lam d₂ else 0 := Finset.sum_comm
        _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Ioc x (x + H),
              if d₁ ∣ n ∧ d₂ ∣ n then lam d₁ * lam d₂ else 0 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
              lam d₁ * lam d₂ * (((Finset.Ioc x (x + H)).filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) := by
            refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
            have hcond : ∀ n : ℕ, (d₁ ∣ n ∧ d₂ ∣ n) ↔ Nat.lcm d₁ d₂ ∣ n :=
              fun _ => Nat.lcm_dvd_iff.symm
            simp_rw [hcond, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    -- For every `D ≥ 1`, `|card((Ioc x (x + H)).filter (D ∣ ·)) - H / D| ≤ 1`!
    have hcard_R : ∀ D : ℕ, 0 < D →
        |(((Finset.Ioc x (x + H)).filter (fun n => D ∣ n)).card : ℝ) - (H : ℝ) * g D| ≤ 1 := by
      intro D hD
      have hD0 : D ≠ 0 := hD.ne'
      have hDR : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
      have hcard_eq : ((Finset.Ioc x (x + H)).filter (fun n => D ∣ n)).card = (x + H) / D - x / D := by
        have hbij : ((Finset.Ioc x (x + H)).filter (fun n => D ∣ n)).card =
            (Finset.Ioc (x / D) ((x + H) / D)).card := by
          refine Finset.card_bij (fun n _ => n / D) ?_ ?_ ?_
          · intro n hn
            obtain ⟨hnI, hDn⟩ := Finset.mem_filter.mp hn
            obtain ⟨hxn, hnH⟩ := Finset.mem_Ioc.mp hnI
            rw [Finset.mem_Ioc]
            refine ⟨?_, Nat.div_le_div_right hnH⟩
            by_contra hle; push Not at hle
            have h1 : n = D * (n / D) := (Nat.mul_div_cancel' hDn).symm
            have h2 : n ≤ D * (x / D) := by rw [h1]; exact Nat.mul_le_mul_left D hle
            have h3 : D * (x / D) ≤ x := Nat.mul_div_le x D
            omega
          · intro n₁ hn₁ n₂ hn₂ heq
            have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2
            have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2
            rw [← h1, ← h2, heq]
          · intro k hk
            obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
            refine ⟨D * k, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, dvd_mul_right D k⟩,
              Nat.mul_div_right k hD⟩
            · have hlt : x < D * (x / D + 1) := by
                have := Nat.div_add_mod x D
                have := Nat.mod_lt x hD
                nlinarith
              have hle : D * (x / D + 1) ≤ D * k := Nat.mul_le_mul_left D hlo
              omega
            · exact (Nat.mul_le_mul_left D hhi).trans (Nat.mul_div_le (x + H) D)
        rw [hbij, Nat.card_Ioc]
      rw [hcard_eq]
      simp only [g, hD0, ↓reduceIte]
      have hle_div : x / D ≤ (x + H) / D := Nat.div_le_div_right (Nat.le_add_right x H)
      rw [Nat.cast_sub hle_div]
      have h1 : (D : ℝ) * ((x / D : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.mul_div_le x D
      have h2 : (x : ℝ) < (D : ℝ) * ((x / D : ℕ) : ℝ) + (D : ℝ) := by
        have := Nat.div_add_mod x D; have := Nat.mod_lt x hD
        exact_mod_cast (by omega : x < D * (x / D) + D)
      have h3 : (D : ℝ) * (((x + H) / D : ℕ) : ℝ) ≤ (x : ℝ) + (H : ℝ) := by
        exact_mod_cast Nat.mul_div_le (x + H) D
      have h4 : (x : ℝ) + (H : ℝ) < (D : ℝ) * (((x + H) / D : ℕ) : ℝ) + (D : ℝ) := by
        have := Nat.div_add_mod (x + H) D; have := Nat.mod_lt (x + H) hD
        exact_mod_cast (by omega : x + H < D * ((x + H) / D) + D)
      rw [abs_le]
      have hmul_div : (H : ℝ) * (1 / (D : ℝ)) = (H : ℝ) / (D : ℝ) := by ring
      rw [hmul_div]
      constructor
      · have hmul : -(D : ℝ) + (H : ℝ) ≤ ((((x + H) / D : ℕ) : ℝ) - ((x / D : ℕ) : ℝ)) * (D : ℝ) := by nlinarith
        have hdiv := (div_le_iff₀ hDR).mpr hmul
        rw [add_div, neg_div, div_self hDR.ne'] at hdiv
        linarith
      · have hmul : ((((x + H) / D : ℕ) : ℝ) - ((x / D : ℕ) : ℝ)) * (D : ℝ) ≤ (H : ℝ) + (D : ℝ) := by nlinarith
        have hdiv := (le_div_iff₀ hDR).mpr hmul
        rw [add_div, div_self hDR.ne'] at hdiv
        linarith
    rw [hexp_w]
    have hsplit :
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          lam d₁ * lam d₂ * (((Finset.Ioc x (x + H)).filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) =
        (H : ℝ) * Stage7SieveMethods.selbergQuadForm z g lam +
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          lam d₁ * lam d₂ * ((((Finset.Ioc x (x + H)).filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) -
            (H : ℝ) * g (Nat.lcm d₁ d₂)) := by
      unfold Stage7SieveMethods.selbergQuadForm
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d₂ _ => by ring
    rw [hsplit, Stage7SieveMethods.selberg_optLam_eq_min hz1 hg, mul_one_div]
    have hmain_le : (H : ℝ) / Stage7SieveMethods.selbergG g z ≤ 4 * (H : ℝ) / Real.log (H : ℝ) := by
      have h1 : (H : ℝ) / Stage7SieveMethods.selbergG g z ≤ (H : ℝ) / ((1 / 4 : ℝ) * Real.log (H : ℝ)) :=
        div_le_div_of_nonneg_left hHR_pos.le (by positivity) hG_ge
      refine h1.trans_eq ?_
      field_simp [hlogH_pos.ne']
    have herr_le :
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          lam d₁ * lam d₂ * ((((Finset.Ioc x (x + H)).filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) -
            (H : ℝ) * g (Nat.lcm d₁ d₂)) ≤ (z : ℝ) ^ 2 := by
      calc _ ≤ ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, (1 : ℝ) := by
            refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
            have hlcm_pos : 0 < Nat.lcm d₁ d₂ :=
              Nat.lcm_pos (Finset.mem_Icc.mp hd₁).1 (Finset.mem_Icc.mp hd₂).1
            calc _ ≤ |lam d₁ * lam d₂ * _| := le_abs_self _
              _ = |lam d₁| * |lam d₂| * |_ - _| := by rw [abs_mul, abs_mul]
              _ ≤ 1 * 1 * 1 := by
                  have h1 := hlam_abs d₁; have h2 := hlam_abs d₂; have h3 := hcard_R _ hlcm_pos
                  exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3 (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
        _ = (z : ℝ) ^ 2 := by
            simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, sq]
    linarith
  -- Step 4: Bound off-diagonal sum `‖∑_{n ∈ Ioc x (x+H)} w n * conj(χ₁ n) * χ₂ n‖ ≤ z^2 * Q^2`!
  have hoff : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ →
      ‖∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) *
        (starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₂.2 (n : ZMod (j₂.1 + 1)))‖ ≤
      (z : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by
    intro j₁ hj₁ j₂ hj₂ hne
    have h1 := Stage3BombieriVinogradov.mem_primCharsUpTo.mp hj₁
    have h2 := Stage3BombieriVinogradov.mem_primCharsUpTo.mp hj₂
    set ψ : DirichletCharacter ℂ ((j₂.1 + 1) * (j₁.1 + 1)) := prodChar j₂.2 j₁.2⁻¹
    have hψ_ne1 : ψ ≠ 1 := prodChar_inv_ne_one_of_distinct_primitive h2.2 h1.2 hne.symm
    have hchar_eq : ∀ n : ℕ,
        starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₂.2 (n : ZMod (j₂.1 + 1)) =
        ψ (n : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) := by
      intro n
      dsimp only [ψ]
      rw [Stage3ZeroFreeRegion.prodChar_apply_nat, mul_comm]
      congr 1
      by_cases hu : IsUnit (n : ZMod (j₁.1 + 1))
      · have hnorm1 : ‖j₁.2 (n : ZMod (j₁.1 + 1))‖ = 1 :=
          (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj j₁.2 hu).1
        have hmul1 : j₁.2 (n : ZMod (j₁.1 + 1)) * starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm1]; norm_num
        have hconj_inv : starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) = (j₁.2 (n : ZMod (j₁.1 + 1)))⁻¹ :=
          eq_inv_of_mul_eq_one_right hmul1
        rw [hconj_inv, MulChar.inv_apply_eq_inv' j₁.2 (n : ZMod (j₁.1 + 1))]
      · rw [MulChar.map_nonunit j₁.2 hu, map_zero, MulChar.map_nonunit j₁.2⁻¹ hu]
    simp_rw [hchar_eq]
    have hexp_off :
        ∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) * ψ (n : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) =
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          ((lam d₁ * lam d₂ : ℝ) : ℂ) * ψ ((Nat.lcm d₁ d₂ : ℕ) : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) *
            ∑ m ∈ Finset.Ioc (x / Nat.lcm d₁ d₂) ((x + H) / Nat.lcm d₁ d₂),
              ψ (m : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) := by
      calc ∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) * ψ (n : ZMod ((j₂.1 + 1) * (j₁.1 + 1)))
          = ∑ n ∈ Finset.Ioc x (x + H), ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
              if d₁ ∣ n ∧ d₂ ∣ n then ((lam d₁ * lam d₂ : ℝ) : ℂ) * ψ (n : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) else 0 := by
            refine Finset.sum_congr rfl fun n _ => ?_
            dsimp only [w]
            rw [Complex.ofReal_pow, sq, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_filter]
            refine Finset.sum_congr rfl fun d₁ _ => ?_
            by_cases h1d : d₁ ∣ n
            · rw [if_pos h1d, Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
              refine Finset.sum_congr rfl fun d₂ _ => ?_
              by_cases h2d : d₂ ∣ n
              · rw [if_pos h2d, if_pos ⟨h1d, h2d⟩, Complex.ofReal_mul]
              · simp [h2d]
            · simp [h1d]
        _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Ioc x (x + H), ∑ d₂ ∈ Finset.Icc 1 z,
              if d₁ ∣ n ∧ d₂ ∣ n then ((lam d₁ * lam d₂ : ℝ) : ℂ) * ψ (n : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) else 0 :=
            Finset.sum_comm
        _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Ioc x (x + H),
              if d₁ ∣ n ∧ d₂ ∣ n then ((lam d₁ * lam d₂ : ℝ) : ℂ) * ψ (n : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) else 0 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
              ((lam d₁ * lam d₂ : ℝ) : ℂ) * ψ ((Nat.lcm d₁ d₂ : ℕ) : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) *
                ∑ m ∈ Finset.Ioc (x / Nat.lcm d₁ d₂) ((x + H) / Nat.lcm d₁ d₂),
                  ψ (m : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) := by
            refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
            set D : ℕ := Nat.lcm d₁ d₂
            have hD : 0 < D := Nat.lcm_pos (Finset.mem_Icc.mp hd₁).1 (Finset.mem_Icc.mp hd₂).1
            have hcond : ∀ n : ℕ, (d₁ ∣ n ∧ d₂ ∣ n) ↔ D ∣ n := fun _ => Nat.lcm_dvd_iff.symm
            simp_rw [hcond, ← Finset.sum_filter]
            rw [Finset.mul_sum]
            refine Finset.sum_bij (fun n _ => n / D) ?_ ?_ ?_ ?_
            · intro n hn
              obtain ⟨hnI, hDn⟩ := Finset.mem_filter.mp hn
              obtain ⟨hxn, hnH⟩ := Finset.mem_Ioc.mp hnI
              rw [Finset.mem_Ioc]
              refine ⟨?_, Nat.div_le_div_right hnH⟩
              by_contra hle; push Not at hle
              have h1' : n = D * (n / D) := (Nat.mul_div_cancel' hDn).symm
              have h2' : n ≤ D * (x / D) := by rw [h1']; exact Nat.mul_le_mul_left D hle
              have h3' : D * (x / D) ≤ x := Nat.mul_div_le x D
              omega
            · intro n₁ hn₁ n₂ hn₂ heq
              have h1' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2
              have h2' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2
              rw [← h1', ← h2', heq]
            · intro m hm
              obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hm
              refine ⟨D * m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, dvd_mul_right D m⟩,
                Nat.mul_div_right m hD⟩
              · have hlt : x < D * (x / D + 1) := by
                  have := Nat.div_add_mod x D; have := Nat.mod_lt x hD; nlinarith
                have hle : D * (x / D + 1) ≤ D * m := Nat.mul_le_mul_left D hlo
                omega
              · exact (Nat.mul_le_mul_left D hhi).trans (Nat.mul_div_le (x + H) D)
            · intro n hn
              have hDn : D ∣ n := (Finset.mem_filter.mp hn).2
              have hn_eq : D * (n / D) = n := Nat.mul_div_cancel' hDn
              conv_lhs => rw [← hn_eq, Nat.cast_mul, map_mul]
              ring
    rw [hexp_off]
    calc ‖∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
            ((lam d₁ * lam d₂ : ℝ) : ℂ) * ψ ((Nat.lcm d₁ d₂ : ℕ) : ZMod ((j₂.1 + 1) * (j₁.1 + 1))) *
              ∑ m ∈ Finset.Ioc (x / Nat.lcm d₁ d₂) ((x + H) / Nat.lcm d₁ d₂),
                ψ (m : ZMod ((j₂.1 + 1) * (j₁.1 + 1)))‖
        ≤ ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, (Q : ℝ) ^ 2 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d₁ _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun d₂ _ => ?_))
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          have hlam12 : |lam d₁| * |lam d₂| ≤ 1 := by
            have := mul_le_mul (hlam_abs d₁) (hlam_abs d₂) (abs_nonneg _) zero_le_one
            linarith
          have hψ1 : ‖ψ ((Nat.lcm d₁ d₂ : ℕ) : ZMod ((j₂.1 + 1) * (j₁.1 + 1)))‖ ≤ 1 := ψ.norm_le_one _
          have hsum_bd := norm_sum_nonprincipal_char_Ioc_le hψ_ne1
            (x / Nat.lcm d₁ d₂) ((x + H) / Nat.lcm d₁ d₂)
          have hq12 : (((j₂.1 + 1) * (j₁.1 + 1) : ℕ) : ℝ) ≤ (Q : ℝ) ^ 2 := by
            have h1' : j₁.1 + 1 ≤ Q := h1.1
            have h2' : j₂.1 + 1 ≤ Q := h2.1
            have : (j₂.1 + 1) * (j₁.1 + 1) ≤ Q * Q := Nat.mul_le_mul h2' h1'
            simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr this
          have hprod1 : |lam d₁| * |lam d₂| * ‖ψ ((Nat.lcm d₁ d₂ : ℕ) : ZMod ((j₂.1 + 1) * (j₁.1 + 1)))‖ ≤ 1 := by
            have := mul_le_mul hlam12 hψ1 (norm_nonneg _) zero_le_one
            linarith
          calc |lam d₁| * |lam d₂| * ‖ψ _‖ * ‖∑ m ∈ Finset.Ioc _ _, ψ _‖
              ≤ 1 * (Q : ℝ) ^ 2 := mul_le_mul hprod1 (hsum_bd.trans hq12) (norm_nonneg _) zero_le_one
            _ = (Q : ℝ) ^ 2 := one_mul _
      _ = (z : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by
          simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  -- Step 5: Combine diagonal and off-diagonal sums!
  have hJ_card : (J.card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hnat : J.card ≤ Q * Q := by
      dsimp only [J, Stage3BombieriVinogradov.primCharsUpTo]
      rw [Finset.card_sigma]
      calc ∑ k ∈ Finset.range Q, (Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive).card
          ≤ ∑ k ∈ Finset.range Q, Fintype.card (DirichletCharacter ℂ (k + 1)) :=
            Finset.sum_le_sum fun k _ => Finset.card_filter_le _ _
        _ ≤ ∑ _k ∈ Finset.range Q, Q := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hcard_char : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
              have horth := Stage2BehrendSieve.dirichlet_orthogonality_conj
                (1 : ZMod (k + 1)) (1 : ZMod (k + 1))
              simp only [map_one, mul_one, isUnit_one, and_self, ↓reduceIte, Finset.sum_const,
                Finset.card_univ, nsmul_eq_mul] at horth
              exact_mod_cast horth
            rw [hcard_char]
            exact (Nat.totient_le (k + 1)).trans (Finset.mem_range.mp hk)
        _ = Q * Q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hnat
  have hcomb :
      (∑ j₁ ∈ J, ∑ j₂ ∈ J, b j₁ * starRingEnd ℂ (b j₂) *
        ∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) *
          (starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₂.2 (n : ZMod (j₂.1 + 1)))).re ≤
      (4 * (H : ℝ) / Real.log (H : ℝ) + (z : ℝ) ^ 2 + (z : ℝ) ^ 2 * (Q : ℝ) ^ 4) * ∑ j ∈ J, ‖b j‖ ^ 2 := by
    rw [Complex.re_sum]
    have hsplit_j : ∀ j₁ ∈ J,
        (∑ j₂ ∈ J, b j₁ * starRingEnd ℂ (b j₂) *
          ∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) *
            (starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₂.2 (n : ZMod (j₂.1 + 1)))).re ≤
        ‖b j₁‖ ^ 2 * (4 * (H : ℝ) / Real.log (H : ℝ) + (z : ℝ) ^ 2) +
        ∑ j₂ ∈ J.erase j₁, ‖b j₁‖ * ‖b j₂‖ * ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) := by
      intro j₁ hj₁
      rw [← Finset.add_sum_erase _ _ hj₁, Complex.add_re, Complex.re_sum]
      refine add_le_add ?_ ?_
      · -- Diagonal `j₂ = j₁`
        have hdiag_term :
            (b j₁ * starRingEnd ℂ (b j₁) *
              ∑ n ∈ Finset.Ioc x (x + H), ((w n : ℝ) : ℂ) *
                (starRingEnd ℂ (j₁.2 (n : ZMod (j₁.1 + 1))) * j₁.2 (n : ZMod (j₁.1 + 1)))).re =
            ‖b j₁‖ ^ 2 * ∑ n ∈ Finset.Ioc x (x + H), w n * ‖j₁.2 (n : ZMod (j₁.1 + 1))‖ ^ 2 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul, Complex.re_sum]
          congr 1; refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_comm (starRingEnd ℂ _), Complex.mul_conj, Complex.normSq_eq_norm_sq,
            ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [hdiag_term]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        calc ∑ n ∈ Finset.Ioc x (x + H), w n * ‖j₁.2 (n : ZMod (j₁.1 + 1))‖ ^ 2
            ≤ ∑ n ∈ Finset.Ioc x (x + H), w n := by
              refine Finset.sum_le_sum fun n _ => ?_
              have h1 := j₁.2.norm_le_one (n : ZMod (j₁.1 + 1))
              have hsq : ‖j₁.2 (n : ZMod (j₁.1 + 1))‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (j₁.2 (n : ZMod (j₁.1 + 1)))]
              exact mul_le_of_le_one_right (by dsimp only [w]; positivity) hsq
          _ ≤ 4 * (H : ℝ) / Real.log (H : ℝ) + (z : ℝ) ^ 2 := hdiag
      · -- Off-diagonal `j₂ ≠ j₁`
        refine Finset.sum_le_sum fun j₂ hj₂ => ?_
        have hne : j₁ ≠ j₂ := (Finset.mem_erase.mp hj₂).1.symm
        have hj₂J : j₂ ∈ J := Finset.mem_of_mem_erase hj₂
        calc (b j₁ * starRingEnd ℂ (b j₂) * ∑ n ∈ Finset.Ioc x (x + H), _).re
            ≤ ‖b j₁ * starRingEnd ℂ (b j₂) * ∑ n ∈ Finset.Ioc x (x + H), _‖ := Complex.re_le_norm _
          _ = ‖b j₁‖ * ‖b j₂‖ * ‖∑ n ∈ Finset.Ioc x (x + H), _‖ := by
              rw [norm_mul, norm_mul, RCLike.norm_conj]
          _ ≤ ‖b j₁‖ * ‖b j₂‖ * ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left (hoff j₁ hj₁ j₂ hj₂J hne) (by positivity)
    have hsum1 := Finset.sum_le_sum hsplit_j
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum1
    have hoff_cs :
        ∑ j₁ ∈ J, ∑ j₂ ∈ J.erase j₁, ‖b j₁‖ * ‖b j₂‖ * ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) ≤
        ((z : ℝ) ^ 2 * (Q : ℝ) ^ 4) * ∑ j ∈ J, ‖b j‖ ^ 2 := by
      have h1 : ∑ j₁ ∈ J, ∑ j₂ ∈ J.erase j₁, ‖b j₁‖ * ‖b j₂‖ * ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) ≤
          ∑ j₁ ∈ J, ∑ j₂ ∈ J, ‖b j₁‖ * ‖b j₂‖ * ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) :=
        Finset.sum_le_sum fun j₁ _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun _ _ _ => by positivity
      have h2 : ∑ j₁ ∈ J, ∑ j₂ ∈ J, ‖b j₁‖ * ‖b j₂‖ * ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) =
          ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) * (∑ j ∈ J, ‖b j‖) ^ 2 := by
        have hsq : (∑ j ∈ J, ‖b j‖) ^ 2 = (∑ j ∈ J, ‖b j‖) * (∑ j ∈ J, ‖b j‖) := sq _
        rw [hsq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j₁ _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j₂ _ => by ring
      have h3 : (∑ j ∈ J, ‖b j‖) ^ 2 ≤ (J.card : ℝ) * ∑ j ∈ J, ‖b j‖ ^ 2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) (fun j => ‖b j‖)
      calc _ ≤ ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) * ((J.card : ℝ) * ∑ j ∈ J, ‖b j‖ ^ 2) :=
            h1.trans (h2 ▸ mul_le_mul_of_nonneg_left h3 (by positivity))
        _ ≤ ((z : ℝ) ^ 2 * (Q : ℝ) ^ 2) * ((Q : ℝ) ^ 2 * ∑ j ∈ J, ‖b j‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hJ_card (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by positivity)
        _ = ((z : ℝ) ^ 2 * (Q : ℝ) ^ 4) * ∑ j ∈ J, ‖b j‖ ^ 2 := by ring
    linarith
  -- Step 6: Show `4 * H / log H + z^2 + z^2 * Q^4 ≤ 20 * H / log H`!
  have hcoeff_le : 4 * (H : ℝ) / Real.log (H : ℝ) + (z : ℝ) ^ 2 + (z : ℝ) ^ 2 * (Q : ℝ) ^ 4 ≤ Δ := by
    have hz2 : (z : ℝ) ^ 2 ≤ (H : ℝ) ^ (1 / 2 : ℝ) := by
      calc (z : ℝ) ^ 2 ≤ ((H : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg z) hz_le 2
        _ = (H : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hHR_pos.le]; norm_num
    have hQ4 : (Q : ℝ) ^ 4 ≤ (H : ℝ) ^ (1 / 3 : ℝ) := by
      have hQ12R : ((Q : ℝ) ^ 4) ^ (3 : ℕ) ≤ (H : ℝ) := by
        have h1 : (Q : ℝ) ^ 12 ≤ (H : ℝ) := by exact_mod_cast hHQ
        linarith [show ((Q : ℝ) ^ 4) ^ (3 : ℕ) = (Q : ℝ) ^ 12 by ring]
      have h1 : ((Q : ℝ) ^ 4) = (((Q : ℝ) ^ 4) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast ((Q : ℝ) ^ 4) 3, ← Real.rpow_mul (by positivity)]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) hQ12R (by norm_num)
    have h56 : (H : ℝ) ^ (5 / 6 : ℝ) ≤ 6 * (H : ℝ) / Real.log (H : ℝ) := by
      rw [le_div_iff₀ hlogH_pos]
      have hlog := log_le_six_mul_rpow_sixth hHR_pos
      calc (H : ℝ) ^ (5 / 6 : ℝ) * Real.log (H : ℝ)
          ≤ (H : ℝ) ^ (5 / 6 : ℝ) * (6 * (H : ℝ) ^ (1 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 6 * ((H : ℝ) ^ (5 / 6 : ℝ) * (H : ℝ) ^ (1 / 6 : ℝ)) := by ring
        _ = 6 * (H : ℝ) := by rw [← Real.rpow_add hHR_pos]; norm_num
    have hz2_le : (z : ℝ) ^ 2 ≤ (H : ℝ) ^ (5 / 6 : ℝ) := by
      refine hz2.trans ?_
      have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 1 ≤ H)
      exact Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
    have hz2Q4 : (z : ℝ) ^ 2 * (Q : ℝ) ^ 4 ≤ (H : ℝ) ^ (5 / 6 : ℝ) := by
      calc (z : ℝ) ^ 2 * (Q : ℝ) ^ 4
          ≤ (H : ℝ) ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 3 : ℝ) :=
            mul_le_mul hz2 hQ4 (by positivity) (by positivity)
        _ = (H : ℝ) ^ (5 / 6 : ℝ) := by rw [← Real.rpow_add hHR_pos]; norm_num
    dsimp only [Δ]
    have hHdiv_pos : 0 ≤ (H : ℝ) / Real.log (H : ℝ) := by positivity
    have h20 : 4 * (H : ℝ) / Real.log (H : ℝ) + 6 * (H : ℝ) / Real.log (H : ℝ) +
        6 * (H : ℝ) / Real.log (H : ℝ) + 4 * ((H : ℝ) / Real.log (H : ℝ)) =
        20 * (H : ℝ) / Real.log (H : ℝ) := by ring
    linarith
  exact hmaj.trans (hexp ▸ hcomb.trans (mul_le_mul_of_nonneg_right hcoeff_le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

/-- **Gallagher's Continuous Prime Hybrid Large Sieve (Fixed Modulus `m`, 100% LOG-FREE!)**:
for `m ≥ 1`, `T ≥ 1`, `N₁, N₂ : ℕ` with `((m : ℝ) * (T + 2)) ^ 20 ≤ (N₁ : ℝ)`, and ANY `b : ℕ → ℂ`:
`∑_{χ mod m} ∫_{-T}^T ‖∑_{p ∈ (N₁, N₂], p prime} b p * χ(p) * p^(-I*t)‖² dt ≤ 16000 * ∑_{p ∈ (N₁, N₂], p prime} (p / log p) * ‖b p‖²`. -/
theorem gallagher_continuous_prime_hybrid_large_sieve_fixed_mod (m : ℕ) [NeZero m]
    {T : ℝ} (hT : 1 ≤ T) (N₁ N₂ : ℕ) (hN₁_ge : ((m : ℝ) * (T + 2)) ^ 20 ≤ (N₁ : ℝ))
    (b : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
      ∫ t in (-T)..T,
        ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      16000 * ∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
  set P : Finset ℕ := (Finset.Ioc N₁ N₂).filter Nat.Prime
  have hP1 : ∀ p ∈ P, 1 ≤ p := fun p hp => (Finset.mem_filter.mp hp).2.one_le
  set h : ℝ := 1 / (2 * T)
  have hh : 0 < h := by positivity
  have hTpos : 0 < T := by linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hmT3 : (3 : ℝ) ≤ (m : ℝ) * (T + 2) := by nlinarith
  have hstep1 :
      ∑ χ : DirichletCharacter ℂ m,
        ∫ t in (-T)..T, ‖∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 *
        ∫ x : ℝ, ∑ χ : DirichletCharacter ℂ m,
          ‖∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h), b p * χ (p : ZMod m)‖ ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun χ _ => ?_
      have hrew : ∀ t : ℝ,
          ∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(Complex.I * (t : ℂ))) =
          ∑ p ∈ P, (b p * χ (p : ZMod m)) *
            Complex.exp (-2 * Real.pi * Complex.I * (logFreq p : ℂ) * (t : ℂ)) := fun t =>
        Finset.sum_congr rfl fun p hp => by rw [nat_cpow_neg_I_mul_eq_exp_logFreq (hP1 p hp) t]
      simp_rw [hrew]
      exact gallagher_continuous_mean_value P logFreq (fun p => b p * χ (p : ZMod m)) hTpos
    · intro χ _
      exact integrable_short_sum_norm_sq P logFreq (fun p => b p * χ (p : ZMod m)) hh
  have hexp_pi_le : Real.exp Real.pi ≤ 252 / 10 := by
    have he1 : Real.exp 1 ≤ 272 / 100 := by linarith [Real.exp_one_lt_d9]
    have h1 : Real.exp Real.pi ≤ Real.exp (16 / 5 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith [Real.pi_lt_d2])
    have h2 : Real.exp (16 / 5 : ℝ) = Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) := by
      rw [← Real.exp_add]; congr 1; norm_num
    have h3 : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
      have hinv : 1 - (1 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 5 : ℝ))]
      have hmul := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (1 / 5 : ℝ)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      linarith
    have hpow3 : (Real.exp 1) ^ 3 ≤ (272 / 100 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1 3
    have hprod : Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) ≤ (272 / 100 : ℝ) ^ 3 * (5 / 4) := by
      rw [h3]; exact mul_le_mul hpow3 h4 (Real.exp_pos _).le (by positivity)
    linarith [show (272 / 100 : ℝ) ^ 3 * (5 / 4) ≤ 252 / 10 by norm_num]
  have hpi_le : Real.pi ≤ 315 / 100 := by linarith [Real.pi_lt_d2]
  have hKpi_le : Real.pi * Real.exp Real.pi ≤ 80 := by nlinarith [Real.pi_pos, Real.exp_pos Real.pi]
  have hpoint : ∀ x : ℝ,
      ∑ χ : DirichletCharacter ℂ m,
        ‖∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h), b p * χ (p : ZMod m)‖ ^ 2 ≤
      ∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h),
        (3200 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
    intro x
    set Sx : Finset ℕ := P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h)
    by_cases hne : Sx = ∅
    · rw [hne]; simp
    · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨hsub, hy_lt, hlen⟩ := short_logFreq_window_subset hP1 hT x
      set y : ℝ := Real.exp (2 * Real.pi * x)
      set M₁ : ℕ := ⌊y⌋₊
      set M₂ : ℕ := ⌊y * Real.exp (Real.pi / T)⌋₊
      have hy_pos : 0 < y := Real.exp_pos _
      have hp₀_gt_N₁ : (N₁ : ℝ) < (p₀ : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).1).1
      have hp₀_le : (p₀ : ℝ) ≤ y * Real.exp (Real.pi / T) := by
        have hmem := hsub hp₀
        exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hmem).2).trans (Nat.floor_le (by positivity))
      have hexp_piT : Real.exp (Real.pi / T) ≤ 26 := by
        have h1 : Real.exp (Real.pi / T) ≤ Real.exp Real.pi :=
          Real.exp_le_exp.mpr (div_le_self Real.pi_pos.le hT)
        linarith
      have hy_ge : (N₁ : ℝ) / 26 ≤ y := by nlinarith
      set H : ℕ := M₂ - M₁
      have hM₁_le_M₂ : M₁ ≤ M₂ :=
        Nat.floor_mono (le_mul_of_one_le_right hy_pos.le (Real.one_le_exp (by positivity)))
      have hHR_ge : y * (Real.pi / T) - 1 ≤ (H : ℝ) := by
        rw [Nat.cast_sub hM₁_le_M₂]
        have hM₂_gt : y * Real.exp (Real.pi / T) - 1 < (M₂ : ℝ) := by
          linarith [Nat.lt_floor_add_one (y * Real.exp (Real.pi / T))]
        have hM₁_le : (M₁ : ℝ) ≤ y := Nat.floor_le hy_pos.le
        have hexp_ge : 1 + Real.pi / T ≤ Real.exp (Real.pi / T) := by
          linarith [Real.add_one_le_exp (Real.pi / T)]
        nlinarith
      have hHR_le : (H : ℝ) ≤ 80 * y / T + 1 := by
        have h1 : ((M₂ + 1 - (⌊y⌋₊ + 1) : ℕ) : ℝ) = (H : ℝ) := by
          have : M₂ + 1 - (M₁ + 1) = M₂ - M₁ := by omega
          rw [this]
        rw [← h1]
        refine hlen.trans ?_
        have : Real.pi * Real.exp Real.pi * (y / T) ≤ 80 * y / T := by
          rw [show 80 * y / T = 80 * (y / T) by ring]
          exact mul_le_mul_of_nonneg_right hKpi_le (by positivity)
        linarith
      -- Massive slack from `N₁ ≥ (m * (T + 2)) ^ 20`!
      have hmT_le : (m : ℝ) * T ≤ (m : ℝ) * (T + 2) := by nlinarith
      have hN₁_div : 1000 * ((m : ℝ) * T) ^ 2 ≤ (N₁ : ℝ) / 26 := by
        have hpow18 : (3 : ℝ) ^ 18 ≤ ((m : ℝ) * (T + 2)) ^ 18 :=
          pow_le_pow_left₀ (by norm_num) hmT3 18
        have h318 : (26000 : ℝ) ≤ (3 : ℝ) ^ 18 := by norm_num
        have hsq : ((m : ℝ) * T) ^ 2 ≤ ((m : ℝ) * (T + 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hmT_le 2
        have h20 : ((m : ℝ) * (T + 2)) ^ 18 * ((m : ℝ) * (T + 2)) ^ 2 = ((m : ℝ) * (T + 2)) ^ 20 := by ring
        have hprod := mul_le_mul (h318.trans hpow18) hsq (by positivity) (by positivity)
        linarith
      have hy_ge_mT2 : 1000 * ((m : ℝ) * T) ^ 2 ≤ y := hN₁_div.trans hy_ge
      have hy_div_T : 1000 * (m : ℝ) ^ 2 * T ≤ y / T := by
        rw [le_div_iff₀ hTpos]; nlinarith
      have hH_ge_2yT : 2 * y / T ≤ (H : ℝ) := by
        have hpi3 : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
        have h1 : 3 * (y / T) ≤ y * (Real.pi / T) := by
          rw [show y * (Real.pi / T) = Real.pi * (y / T) by ring]
          exact mul_le_mul_of_nonneg_right hpi3 (by positivity)
        have h2 : 1 ≤ y / T := by nlinarith [sq_nonneg ((m : ℝ) - 1)]
        have : 2 * y / T = 2 * (y / T) := by ring
        linarith
      have hH_le_81yT : (H : ℝ) ≤ 81 * y / T := by
        have h2 : 1 ≤ y / T := by nlinarith [sq_nonneg ((m : ℝ) - 1)]
        have h81 : 81 * y / T = 80 * y / T + y / T := by ring
        linarith
      have hH9m : 9 * m ≤ H := by
        have h1 : (9 * m : ℝ) ≤ (H : ℝ) := by
          have : 9 * (m : ℝ) ≤ 2 * (1000 * (m : ℝ) ^ 2 * T) := by nlinarith
          have h2yT : 2 * y / T = 2 * (y / T) := by ring
          linarith
        exact_mod_cast h1
      -- Embed `Sx ⊆ (Ioc M₁ (M₁ + H)).filter Nat.Prime` and apply `fixed_mod_prime_large_sieve`!
      have hSx_sub : Sx ⊆ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime := by
        intro p hp
        have hmem := hsub hp
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem
        have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hpr⟩
      let c : ℕ → ℂ := fun p => if p ∈ Sx then b p else 0
      have hsum_eq : ∀ χ : DirichletCharacter ℂ m,
          ∑ p ∈ Sx, b p * χ (p : ZMod m) =
          ∑ p ∈ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime, c p * χ (p : ZMod m) := by
        intro χ; symm
        rw [← Finset.sum_subset hSx_sub]
        · refine Finset.sum_congr rfl fun p hp => by simp [c, hp]
        · intro p _ hp; simp [c, hp]
      have hnorm_eq : ∑ p ∈ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime, ‖c p‖ ^ 2 = ∑ p ∈ Sx, ‖b p‖ ^ 2 := by
        rw [← Finset.sum_subset hSx_sub]
        · refine Finset.sum_congr rfl fun p hp => by simp [c, hp]
        · intro p _ hp; simp [c, hp]
      simp_rw [hsum_eq]
      have hpls := fixed_mod_prime_large_sieve m M₁ H hH9m c
      rw [hnorm_eq] at hpls
      have hlogHm_pos : 0 < Real.log ((H : ℝ) / (m : ℝ)) := by
        have hm_pos : 0 < m := NeZero.pos m
        apply Real.log_pos; rw [one_lt_div (by linarith)]; exact_mod_cast (by omega : m < H)
      calc ∑ χ : DirichletCharacter ℂ m,
            ‖∑ p ∈ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime, c p * χ (p : ZMod m)‖ ^ 2
          ≤ (10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ))) * ∑ p ∈ Sx, ‖b p‖ ^ 2 := hpls
        _ = ∑ p ∈ Sx, (10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ))) * ‖b p‖ ^ 2 := Finset.mul_sum _ _ _
        _ ≤ ∑ p ∈ Sx, (3200 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
            refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            have hp_gt_y : y < (p : ℝ) := hy_lt p hp
            have hp_le_26y : (p : ℝ) ≤ 26 * y := by
              have hmem := hsub hp
              have h1 : (p : ℝ) ≤ y * Real.exp (Real.pi / T) :=
                (Nat.cast_le.mpr (Finset.mem_Icc.mp hmem).2).trans (Nat.floor_le (by positivity))
              nlinarith
            have hp_pos : (0 : ℝ) < (p : ℝ) := lt_trans hy_pos hp_gt_y
            have hlogp_pos : 0 < Real.log (p : ℝ) :=
              Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.one_lt)
            -- Show `(1 / 2) * log p ≤ log (H / m)` via `p ≤ (H / m)^2`!
            have hp_le_sq : (p : ℝ) ≤ ((H : ℝ) / (m : ℝ)) ^ 2 := by
              have h1 : 2 * y / ((m : ℝ) * T) ≤ (H : ℝ) / (m : ℝ) := by
                rw [div_le_div_iff₀ (by positivity) (by linarith)]
                have := mul_le_mul_of_nonneg_right hH_ge_2yT (by linarith : (0 : ℝ) ≤ (m : ℝ))
                have h2 : 2 * y / T * (m : ℝ) = 2 * y * (m : ℝ) / T := by ring
                have h3 : (2 * y) * (m : ℝ) ≤ (H : ℝ) * ((m : ℝ) * T) := by
                  have h4 := (div_le_iff₀ hTpos).mp hH_ge_2yT
                  nlinarith
                exact h3
              have hsq1 : (2 * y / ((m : ℝ) * T)) ^ 2 ≤ ((H : ℝ) / (m : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (by positivity) h1 2
              have h26y : 26 * y ≤ (2 * y / ((m : ℝ) * T)) ^ 2 := by
                rw [div_pow, le_div_iff₀ (by positivity)]
                nlinarith
              linarith
            have hlog_half : (1 / 2 : ℝ) * Real.log (p : ℝ) ≤ Real.log ((H : ℝ) / (m : ℝ)) := by
              have h1 := Real.log_le_log hp_pos hp_le_sq
              rw [Real.log_pow] at h1; push_cast at h1; linarith
            calc 10 * (H : ℝ) / Real.log ((H : ℝ) / (m : ℝ))
                ≤ 10 * (81 * y / T) / ((1 / 2 : ℝ) * Real.log (p : ℝ)) :=
                  div_le_div₀ (by positivity) (by linarith) (by positivity) hlog_half
              _ = (1620 / T) * (y / Real.log (p : ℝ)) := by ring
              _ ≤ (3200 / T) * ((p : ℝ) / Real.log (p : ℝ)) := by
                  refine mul_le_mul (div_le_div_of_nonneg_right (by norm_num) hTpos.le)
                    (div_le_div_of_nonneg_right hp_gt_y.le hlogp_pos.le) (by positivity) (by positivity)
  have hint_lhs : Integrable (fun x : ℝ => ∑ χ : DirichletCharacter ℂ m,
      ‖∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h), b p * χ (p : ZMod m)‖ ^ 2) :=
    MeasureTheory.integrable_finsetSum _ fun χ _ =>
      integrable_short_sum_norm_sq P logFreq (fun p => b p * χ (p : ZMod m)) hh
  obtain ⟨hint_rhs, hrhs_eq⟩ := integral_short_sum_weight P logFreq
    (fun p => (3200 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2) hh
  have hint_mono := MeasureTheory.integral_mono hint_lhs hint_rhs hpoint
  rw [hrhs_eq] at hint_mono
  have hpi2_le : Real.pi ^ 2 / 2 ≤ 5 := by nlinarith [Real.pi_pos]
  calc ∑ χ : DirichletCharacter ℂ m,
        ∫ t in (-T)..T, ‖∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ Real.pi ^ 2 * T ^ 2 * (h * ∑ p ∈ P, (3200 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hint_mono (by positivity))
    _ = (Real.pi ^ 2 / 2) * 3200 * ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
        dsimp only [h]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        field_simp [hTpos.ne']
    _ ≤ 16000 * ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right (by linarith) ?_
        refine Finset.sum_nonneg fun p hp => mul_nonneg ?_ (sq_nonneg _)
        have hlp : 0 < Real.log (p : ℝ) :=
          Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt)
        positivity

open Classical in
/-- **Gallagher's Continuous Prime Hybrid Large Sieve (Primitive Family `q ≤ Q`, 100% LOG-FREE!)**:
for `Q ≥ 1`, `T ≥ 1`, `N₁, N₂ : ℕ` with `((Q : ℝ) ^ 2 * (T + 2)) ^ 20 ≤ (N₁ : ℝ)`, and ANY `b : ℕ → ℂ`:
`∑_{q ≤ Q} ∑*_{χ mod q} ∫_{-T}^T ‖∑_{p ∈ (N₁, N₂], p prime} b p * χ(p) * p^(-I*t)‖² dt ≤ 20000 * ∑_{p ∈ (N₁, N₂], p prime} (p / log p) * ‖b p‖²`. -/
theorem gallagher_continuous_prime_hybrid_large_sieve_prim (Q : ℕ) (hQ : 1 ≤ Q)
    {T : ℝ} (hT : 1 ≤ T) (N₁ N₂ : ℕ) (hN₁_ge : ((Q : ℝ) ^ 2 * (T + 2)) ^ 20 ≤ (N₁ : ℝ))
    (b : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ∫ t in (-T)..T,
          ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, b p * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      20000 * ∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
  set P : Finset ℕ := (Finset.Ioc N₁ N₂).filter Nat.Prime
  have hP1 : ∀ p ∈ P, 1 ≤ p := fun p hp => (Finset.mem_filter.mp hp).2.one_le
  set h : ℝ := 1 / (2 * T)
  have hh : 0 < h := by positivity
  have hTpos : 0 < T := by linarith
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQT3 : (3 : ℝ) ≤ (Q : ℝ) ^ 2 * (T + 2) := by nlinarith
  have hstep1 :
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖∑ p ∈ P, b p * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 *
        ∫ x : ℝ, ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h),
              b p * χ (p : ZMod (k + 1))‖ ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [MeasureTheory.integral_finsetSum]
      · rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun χ _ => ?_
        have hrew : ∀ t : ℝ,
            ∑ p ∈ P, b p * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(Complex.I * (t : ℂ))) =
            ∑ p ∈ P, (b p * χ (p : ZMod (k + 1))) *
              Complex.exp (-2 * Real.pi * Complex.I * (logFreq p : ℂ) * (t : ℂ)) := fun t =>
          Finset.sum_congr rfl fun p hp => by rw [nat_cpow_neg_I_mul_eq_exp_logFreq (hP1 p hp) t]
        simp_rw [hrew]
        exact gallagher_continuous_mean_value P logFreq (fun p => b p * χ (p : ZMod (k + 1))) hTpos
      · intro χ _
        exact integrable_short_sum_norm_sq P logFreq (fun p => b p * χ (p : ZMod (k + 1))) hh
    · intro k _
      exact MeasureTheory.integrable_finsetSum _ fun χ _ =>
        integrable_short_sum_norm_sq P logFreq (fun p => b p * χ (p : ZMod (k + 1))) hh
  have hexp_pi_le : Real.exp Real.pi ≤ 252 / 10 := by
    have he1 : Real.exp 1 ≤ 272 / 100 := by linarith [Real.exp_one_lt_d9]
    have h1 : Real.exp Real.pi ≤ Real.exp (16 / 5 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith [Real.pi_lt_d2])
    have h2 : Real.exp (16 / 5 : ℝ) = Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) := by
      rw [← Real.exp_add]; congr 1; norm_num
    have h3 : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
      have hinv : 1 - (1 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 5 : ℝ))]
      have hmul := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (1 / 5 : ℝ)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      linarith
    have hpow3 : (Real.exp 1) ^ 3 ≤ (272 / 100 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1 3
    have hprod : Real.exp (3 : ℝ) * Real.exp (1 / 5 : ℝ) ≤ (272 / 100 : ℝ) ^ 3 * (5 / 4) := by
      rw [h3]; exact mul_le_mul hpow3 h4 (Real.exp_pos _).le (by positivity)
    linarith [show (272 / 100 : ℝ) ^ 3 * (5 / 4) ≤ 252 / 10 by norm_num]
  have hpi_le : Real.pi ≤ 315 / 100 := by linarith [Real.pi_lt_d2]
  have hKpi_le : Real.pi * Real.exp Real.pi ≤ 80 := by nlinarith [Real.pi_pos, Real.exp_pos Real.pi]
  have hpoint : ∀ x : ℝ,
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h), b p * χ (p : ZMod (k + 1))‖ ^ 2 ≤
      ∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h),
        (4000 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
    intro x
    set Sx : Finset ℕ := P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h)
    by_cases hne : Sx = ∅
    · rw [hne]; simp
    · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨hsub, hy_lt, hlen⟩ := short_logFreq_window_subset hP1 hT x
      set y : ℝ := Real.exp (2 * Real.pi * x)
      set M₁ : ℕ := ⌊y⌋₊
      set M₂ : ℕ := ⌊y * Real.exp (Real.pi / T)⌋₊
      have hy_pos : 0 < y := Real.exp_pos _
      have hp₀_gt_N₁ : (N₁ : ℝ) < (p₀ : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).1).1
      have hp₀_le : (p₀ : ℝ) ≤ y * Real.exp (Real.pi / T) := by
        have hmem := hsub hp₀
        exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hmem).2).trans (Nat.floor_le (by positivity))
      have hexp_piT : Real.exp (Real.pi / T) ≤ 26 := by
        have h1 : Real.exp (Real.pi / T) ≤ Real.exp Real.pi :=
          Real.exp_le_exp.mpr (div_le_self Real.pi_pos.le hT)
        linarith
      have hy_ge : (N₁ : ℝ) / 26 ≤ y := by nlinarith
      set H : ℕ := M₂ - M₁
      have hM₁_le_M₂ : M₁ ≤ M₂ :=
        Nat.floor_mono (le_mul_of_one_le_right hy_pos.le (Real.one_le_exp (by positivity)))
      have hHR_ge : y * (Real.pi / T) - 1 ≤ (H : ℝ) := by
        rw [Nat.cast_sub hM₁_le_M₂]
        have hM₂_gt : y * Real.exp (Real.pi / T) - 1 < (M₂ : ℝ) := by
          linarith [Nat.lt_floor_add_one (y * Real.exp (Real.pi / T))]
        have hM₁_le : (M₁ : ℝ) ≤ y := Nat.floor_le hy_pos.le
        have hexp_ge : 1 + Real.pi / T ≤ Real.exp (Real.pi / T) := by
          linarith [Real.add_one_le_exp (Real.pi / T)]
        nlinarith
      have hHR_le : (H : ℝ) ≤ 80 * y / T + 1 := by
        have h1 : ((M₂ + 1 - (⌊y⌋₊ + 1) : ℕ) : ℝ) = (H : ℝ) := by
          have : M₂ + 1 - (M₁ + 1) = M₂ - M₁ := by omega
          rw [this]
        rw [← h1]
        refine hlen.trans ?_
        have : Real.pi * Real.exp Real.pi * (y / T) ≤ 80 * y / T := by
          rw [show 80 * y / T = 80 * (y / T) by ring]
          exact mul_le_mul_of_nonneg_right hKpi_le (by positivity)
        linarith
      -- Massive slack from `N₁ ≥ (Q^2 * (T + 2)) ^ 20`!
      have hQT_le : (Q : ℝ) ^ 2 * T ≤ (Q : ℝ) ^ 2 * (T + 2) := by nlinarith
      have hy_ge_QT : 1000 * ((Q : ℝ) ^ 2 * T) ^ 6 * T ^ 2 ≤ y := by
        have hpow12 : (3 : ℝ) ^ 12 ≤ ((Q : ℝ) ^ 2 * (T + 2)) ^ 12 :=
          pow_le_pow_left₀ (by norm_num) hQT3 12
        have h312 : (26000 : ℝ) ≤ (3 : ℝ) ^ 12 := by norm_num
        have hQ2_ge1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ hQ1
        have hT2 : T ^ 2 ≤ ((Q : ℝ) ^ 2 * (T + 2)) ^ 2 :=
          pow_le_pow_left₀ hTpos.le (by nlinarith) 2
        have hQT6 : ((Q : ℝ) ^ 2 * T) ^ 6 ≤ ((Q : ℝ) ^ 2 * (T + 2)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hQT_le 6
        have h8 : ((Q : ℝ) ^ 2 * T) ^ 6 * T ^ 2 ≤ ((Q : ℝ) ^ 2 * (T + 2)) ^ 8 := by
          have h1 := mul_le_mul hQT6 hT2 (by positivity) (by positivity)
          linarith [show ((Q : ℝ) ^ 2 * (T + 2)) ^ 6 * ((Q : ℝ) ^ 2 * (T + 2)) ^ 2 =
            ((Q : ℝ) ^ 2 * (T + 2)) ^ 8 by ring]
        have h20 : ((Q : ℝ) ^ 2 * (T + 2)) ^ 12 * ((Q : ℝ) ^ 2 * (T + 2)) ^ 8 =
            ((Q : ℝ) ^ 2 * (T + 2)) ^ 20 := by ring
        have hprod := mul_le_mul (h312.trans hpow12) h8 (by positivity) (by positivity)
        linarith
      have hQT_ge1 : (1 : ℝ) ≤ ((Q : ℝ) ^ 2 * T) ^ 6 := one_le_pow₀ (by nlinarith)
      have hy_div_T : 1000 * ((Q : ℝ) ^ 2 * T) ^ 6 * T ≤ y / T := by
        rw [le_div_iff₀ hTpos]; linarith
      have hH_ge_2yT : 2 * y / T ≤ (H : ℝ) := by
        have hpi3 : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
        have h1 : 3 * (y / T) ≤ y * (Real.pi / T) := by
          rw [show y * (Real.pi / T) = Real.pi * (y / T) by ring]
          exact mul_le_mul_of_nonneg_right hpi3 (by positivity)
        have h2 : 1 ≤ y / T := by nlinarith
        have : 2 * y / T = 2 * (y / T) := by ring
        linarith
      have hH_le_81yT : (H : ℝ) ≤ 81 * y / T := by
        have h2 : 1 ≤ y / T := by nlinarith
        have h81 : 81 * y / T = 80 * y / T + y / T := by ring
        linarith
      have hHQ : Q ^ 12 ≤ H := by
        have hQ12_le : ((Q : ℝ) ^ 12) ≤ (H : ℝ) := by
          have h1 : (Q : ℝ) ^ 12 ≤ ((Q : ℝ) ^ 2 * T) ^ 6 := by
            rw [mul_pow, show ((Q : ℝ) ^ 2) ^ 6 = (Q : ℝ) ^ 12 by ring]
            exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hT)
          have h2 : 2 * (y / T) ≤ (H : ℝ) := by rw [← mul_div_assoc]; exact hH_ge_2yT
          nlinarith
        exact_mod_cast hQ12_le
      have hH16 : 16 ≤ H := by
        have h1 : (16 : ℝ) ≤ (H : ℝ) := by
          have h2 : 2 * (y / T) ≤ (H : ℝ) := by rw [← mul_div_assoc]; exact hH_ge_2yT
          nlinarith
        exact_mod_cast h1
      have hzx : ⌊(H : ℝ) ^ (1 / 4 : ℝ)⌋₊ ≤ M₁ := by
        refine Nat.floor_mono ?_
        have hH_le_81y : (H : ℝ) ≤ 81 * y :=
          hH_le_81yT.trans (div_le_self (by positivity) hT)
        have h81y_le_y4 : 81 * y ≤ y ^ 4 := by
          have hy100 : (100 : ℝ) ≤ y := by nlinarith
          have hy3 : (81 : ℝ) ≤ y ^ 3 :=
            (show (81 : ℝ) ≤ 100 ^ 3 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hy100 3)
          nlinarith
        have hy_rpow : y = (y ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy_pos.le]; norm_num
        rw [hy_rpow]
        exact Real.rpow_le_rpow (Nat.cast_nonneg H) (hH_le_81y.trans h81y_le_y4) (by norm_num)
      have hSx_sub : Sx ⊆ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime := by
        intro p hp
        have hmem := hsub hp
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem
        have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hpr⟩
      let c : ℕ → ℂ := fun p => if p ∈ Sx then b p else 0
      have hsum_eq : ∀ (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)),
          ∑ p ∈ Sx, b p * χ (p : ZMod (k + 1)) =
          ∑ p ∈ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime, c p * χ (p : ZMod (k + 1)) := by
        intro k χ; symm
        rw [← Finset.sum_subset hSx_sub]
        · refine Finset.sum_congr rfl fun p hp => by simp [c, hp]
        · intro p _ hp; simp [c, hp]
      have hnorm_eq : ∑ p ∈ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime, ‖c p‖ ^ 2 = ∑ p ∈ Sx, ‖b p‖ ^ 2 := by
        rw [← Finset.sum_subset hSx_sub]
        · refine Finset.sum_congr rfl fun p hp => by simp [c, hp]
        · intro p _ hp; simp [c, hp]
      simp_rw [hsum_eq]
      have hpls := primitive_prime_large_sieve Q hQ M₁ H hHQ hH16 hzx c
      rw [hnorm_eq] at hpls
      have hlogH_pos : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
      calc ∑ k ∈ Finset.range Q,
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ p ∈ (Finset.Ioc M₁ (M₁ + H)).filter Nat.Prime, c p * χ (p : ZMod (k + 1))‖ ^ 2
          ≤ (20 * (H : ℝ) / Real.log (H : ℝ)) * ∑ p ∈ Sx, ‖b p‖ ^ 2 := hpls
        _ = ∑ p ∈ Sx, (20 * (H : ℝ) / Real.log (H : ℝ)) * ‖b p‖ ^ 2 := Finset.mul_sum _ _ _
        _ ≤ ∑ p ∈ Sx, (4000 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
            refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            have hp_gt_y : y < (p : ℝ) := hy_lt p hp
            have hp_le_26y : (p : ℝ) ≤ 26 * y := by
              have hmem := hsub hp
              have h1 : (p : ℝ) ≤ y * Real.exp (Real.pi / T) :=
                (Nat.cast_le.mpr (Finset.mem_Icc.mp hmem).2).trans (Nat.floor_le (by positivity))
              nlinarith
            have hp_pos : (0 : ℝ) < (p : ℝ) := lt_trans hy_pos hp_gt_y
            have hlogp_pos : 0 < Real.log (p : ℝ) :=
              Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.one_lt)
            have hp_le_H2 : (p : ℝ) ≤ (H : ℝ) ^ 2 := by
              have h1 : (2 * y / T) ^ 2 ≤ (H : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hH_ge_2yT 2
              have h26y : 26 * y ≤ (2 * y / T) ^ 2 := by
                rw [div_pow, le_div_iff₀ (by positivity)]
                have hyT2 : 1000 * T ^ 2 ≤ y := by nlinarith
                nlinarith
              linarith
            have hlog_half : (1 / 2 : ℝ) * Real.log (p : ℝ) ≤ Real.log (H : ℝ) := by
              have h1 := Real.log_le_log hp_pos hp_le_H2
              rw [Real.log_pow] at h1; push_cast at h1; linarith
            calc 20 * (H : ℝ) / Real.log (H : ℝ)
                ≤ 20 * (81 * y / T) / ((1 / 2 : ℝ) * Real.log (p : ℝ)) :=
                  div_le_div₀ (by positivity) (by linarith) (by positivity) hlog_half
              _ = (3240 / T) * (y / Real.log (p : ℝ)) := by ring
              _ ≤ (4000 / T) * ((p : ℝ) / Real.log (p : ℝ)) := by
                  refine mul_le_mul (div_le_div_of_nonneg_right (by norm_num) hTpos.le)
                    (div_le_div_of_nonneg_right hp_gt_y.le hlogp_pos.le) (by positivity) (by positivity)
  have hint_lhs : Integrable (fun x : ℝ => ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ‖∑ p ∈ P.filter (fun p => x < logFreq p ∧ logFreq p ≤ x + h), b p * χ (p : ZMod (k + 1))‖ ^ 2) :=
    MeasureTheory.integrable_finsetSum _ fun k _ =>
      MeasureTheory.integrable_finsetSum _ fun χ _ =>
        integrable_short_sum_norm_sq P logFreq (fun p => b p * χ (p : ZMod (k + 1))) hh
  obtain ⟨hint_rhs, hrhs_eq⟩ := integral_short_sum_weight P logFreq
    (fun p => (4000 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2) hh
  have hint_mono := MeasureTheory.integral_mono hint_lhs hint_rhs hpoint
  rw [hrhs_eq] at hint_mono
  have hpi2_le : Real.pi ^ 2 / 2 ≤ 5 := by nlinarith [Real.pi_pos]
  calc ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖∑ p ∈ P, b p * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ Real.pi ^ 2 * T ^ 2 * (h * ∑ p ∈ P, (4000 / T) * ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hint_mono (by positivity))
    _ = (Real.pi ^ 2 / 2) * 4000 * ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
        dsimp only [h]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        field_simp [hTpos.ne']
    _ ≤ 20000 * ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) * ‖b p‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right (by linarith) ?_
        refine Finset.sum_nonneg fun p hp => mul_nonneg ?_ (sq_nonneg _)
        have hlp : 0 < Real.log (p : ℝ) :=
          Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt)
        positivity

/-! ## Section 3: Turán's Second Main Theorem & High-Derivative Prime Zero Detector -/

/-! ### Section 3a: Turán's Second Main Theorem (`turan_power_sum_second_main`) -/

/-- Elementary geometric-difference factorization:
`(a - b) * ∑ m ∈ Finset.range d, a ^ m * b ^ (d - 1 - m) = a ^ d - b ^ d`. -/
private lemma mul_geom_sum_eq_pow_sub_pow (a b : ℂ) (d : ℕ) :
    (a - b) * ∑ m ∈ Finset.range d, a ^ m * b ^ (d - 1 - m) = a ^ d - b ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have hshift : ∑ m ∈ Finset.range d, a ^ m * b ^ (d - m) =
        b * ∑ m ∈ Finset.range d, a ^ m * b ^ (d - 1 - m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmd : m < d := Finset.mem_range.mp hm
      have hexp : d - m = (d - 1 - m) + 1 := by omega
      rw [hexp, pow_succ]; ring
    rw [hshift, mul_add]
    calc (a - b) * (b * ∑ m ∈ Finset.range d, a ^ m * b ^ (d - 1 - m)) + (a - b) * a ^ d
        = b * ((a - b) * ∑ m ∈ Finset.range d, a ^ m * b ^ (d - 1 - m)) + (a - b) * a ^ d := by ring
      _ = b * (a ^ d - b ^ d) + (a - b) * a ^ d := by rw [ih]
      _ = a ^ (d + 1) - b ^ (d + 1) := by rw [pow_succ, pow_succ]; ring

/-- Elementary Stirling lower bound `(n / e) ^ n ≤ n!` for all `n : ℕ`. -/
private lemma div_exp_one_pow_le_factorial (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) :=
    Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr n.factorial_pos
  have hexp_eq : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp_eq, div_le_iff₀ hfac_pos] at h1
  rw [div_pow, div_le_iff₀ (pow_pos he_pos n)]
  linarith

/-- Elementary product lower bound for binomial-split factorials:
`((a + b)! : ℝ) / 2 ^ (a + b) ≤ (a! : ℝ) * (b! : ℝ)`. -/
private lemma factorial_add_div_two_pow_le (a b : ℕ) :
    (((a + b).factorial : ℝ)) / (2 : ℝ) ^ (a + b) ≤ (a.factorial : ℝ) * (b.factorial : ℝ) := by
  have hch : (a + b).choose a * (a.factorial * b.factorial) = (a + b).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rw [Nat.add_sub_cancel_left, mul_assoc] at this
    exact this
  have hle_pow : (a + b).choose a ≤ 2 ^ (a + b) := by
    have hsum : ∑ i ∈ Finset.range (a + b + 1), (a + b).choose i = 2 ^ (a + b) :=
      Nat.sum_range_choose (a + b)
    calc (a + b).choose a
        ≤ ∑ i ∈ Finset.range (a + b + 1), (a + b).choose i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      _ = 2 ^ (a + b) := hsum
  have hnat : (a + b).factorial ≤ 2 ^ (a + b) * (a.factorial * b.factorial) := by
    rw [← hch]; exact Nat.mul_le_mul_right _ hle_pow
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (a + b))]
  have hR : (((a + b).factorial : ℝ)) ≤ (2 : ℝ) ^ (a + b) * ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
    exact_mod_cast hnat
  linarith

/-- Circle integral of `(z - w)⁻¹` around `C(0, r)` equals `2 π i` when `‖w‖ < r`. -/
private lemma circleIntegral_inv_sub_of_lt {r : ℝ} (_hr : 0 < r) {w : ℂ} (hw : ‖w‖ < r) :
    (∮ z in C(0, r), (z - w)⁻¹) = 2 * (Real.pi : ℂ) * I := by
  have hmem : w ∈ Metric.ball (0 : ℂ) r := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hc := (differentiableOn_const (1 : ℂ)).diffContOnCl.circleIntegral_sub_inv_smul hmem
  simpa only [smul_eq_mul, mul_one] using hc

/-- Circle integral of `(z - w)⁻¹` around `C(0, r)` equals `0` when `r < ‖w‖`. -/
private lemma circleIntegral_inv_sub_of_gt {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : r < ‖w‖) :
    (∮ z in C(0, r), (z - w)⁻¹) = 0 := by
  have hne : ∀ z ∈ Metric.closedBall (0 : ℂ) r, z - w ≠ 0 := fun z hz h0 => by
    have hzn : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
    have hzw : z = w := sub_eq_zero.mp h0
    linarith [hzw ▸ hzn]
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) (Metric.closedBall 0 r) :=
    fun z hz => ((differentiableAt_id.sub (differentiableAt_const w)).inv (hne z hz)).differentiableWithinAt
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    Set.countable_empty hdiff.continuousOn (fun z hz => hdiff.differentiableAt
      (closedBall_mem_nhds_of_mem hz.1))

/-- Circle integral of `(z ^ (k + 1))⁻¹` around `C(0, r)` equals `0` for all `k ≥ 1`. -/
private lemma circleIntegral_inv_pow_eq_zero {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : 1 ≤ k) :
    (∮ z in C(0, r), (z ^ (k + 1))⁻¹) = 0 := by
  unfold circleIntegral
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsimp : ∀ θ : ℝ,
      deriv (circleMap 0 r) θ • ((circleMap 0 r θ) ^ (k + 1))⁻¹ =
        (I * ((r : ℂ) ^ k)⁻¹) * Complex.exp (-((k : ℂ) * I) * (θ : ℂ)) := by
    intro θ
    rw [deriv_circleMap, circleMap_zero, smul_eq_mul]
    have hexp_ne : Complex.exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    have hexp_pow : (Complex.exp ((θ : ℂ) * I)) ^ (k + 1) =
        Complex.exp ((θ : ℂ) * I) * Complex.exp (((k : ℂ) * I) * (θ : ℂ)) := by
      rw [pow_succ', ← Complex.exp_nat_mul]
      congr 1; ring
    have hexp_inv : (Complex.exp (((k : ℂ) * I) * (θ : ℂ)))⁻¹ =
        Complex.exp (-((k : ℂ) * I) * (θ : ℂ)) := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [mul_pow, hexp_pow, mul_inv, mul_inv, pow_succ', mul_inv, hexp_inv]
    have hmul : Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹ = 1 :=
      mul_inv_cancel₀ hexp_ne
    have hrmul : (r : ℂ) * (r : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hrC
    calc (r : ℂ) * Complex.exp ((θ : ℂ) * I) * I *
          (((r : ℂ)⁻¹ * ((r : ℂ) ^ k)⁻¹) * ((Complex.exp ((θ : ℂ) * I))⁻¹ *
            Complex.exp (-((k : ℂ) * I) * (θ : ℂ))))
        = ((r : ℂ) * (r : ℂ)⁻¹) * (Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹) *
            ((I * ((r : ℂ) ^ k)⁻¹) * Complex.exp (-((k : ℂ) * I) * (θ : ℂ))) := by ring
      _ = (I * ((r : ℂ) ^ k)⁻¹) * Complex.exp (-((k : ℂ) * I) * (θ : ℂ)) := by
          rw [hrmul, hmul, one_mul, one_mul]
  simp_rw [hsimp, intervalIntegral.integral_const_mul]
  have hprim : ∀ θ : ℝ,
      HasDerivAt (fun x : ℝ => (-((k : ℂ) * I))⁻¹ * Complex.exp (-((k : ℂ) * I) * (x : ℂ)))
        (Complex.exp (-((k : ℂ) * I) * (θ : ℂ))) θ := by
    intro θ
    have hlin : HasDerivAt (fun x : ℝ => -((k : ℂ) * I) * (x : ℂ)) (-((k : ℂ) * I)) θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (-((k : ℂ) * I))
    have hexp := hlin.cexp
    have hmul := hexp.const_mul (-((k : ℂ) * I))⁻¹
    have hc_ne : -((k : ℂ) * I) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hkC I_ne_zero)
    refine hmul.congr_deriv ?_
    rw [mul_comm (Complex.exp _), ← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
  have hcont : Continuous (fun x : ℝ => Complex.exp (-((k : ℂ) * I) * (x : ℂ))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hprim θ)
    (hcont.intervalIntegrable _ _)]
  have hexp_2pi : Complex.exp (-((k : ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have hrew : -((k : ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ) = ((-(k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast; ring
    rw [hrew]
    exact Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
  rw [hexp_2pi, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, mul_zero]

private lemma circleIntegral_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hF : ∀ i ∈ s, CircleIntegrable (F i) c r) :
    CircleIntegrable (fun z : ℂ => ∑ i ∈ s, F i z) c r ∧
    (∮ z in C(c, r), ∑ i ∈ s, F i z) = ∑ i ∈ s, ∮ z in C(c, r), F i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp [circleIntegrable_const], by unfold circleIntegral; simp⟩
  | @insert a s has ih =>
    have ha : CircleIntegrable (F a) c r := hF a (Finset.mem_insert_self a s)
    obtain ⟨hs_int, hs_eq⟩ := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have hfun : (fun z : ℂ => ∑ i ∈ insert a s, F i z) = fun z => F a z + ∑ i ∈ s, F i z := by
      funext z; exact Finset.sum_insert has
    rw [hfun, Finset.sum_insert has]
    exact ⟨ha.add hs_int, by rw [circleIntegral.integral_add ha hs_int, hs_eq]⟩

/-- **Turán's Second Main Theorem (`0` Assumptions!)**:
for EVERY `M ≥ 1`, `K : ℕ`, and `z : Fin M → ℂ` with `max_j ‖z j‖ ≥ 1`, there exists
`k ∈ Finset.Icc (K + 1) (K + M)` such that
`‖∑ j : Fin M, z j ^ k‖ ≥ (1 / (64 * Real.exp 1)) ^ M * (1 / 2) ^ K`. -/
theorem turan_power_sum_second_main {M : ℕ} (hM : 1 ≤ M) (K : ℕ) (z : Fin M → ℂ)
    (hmax : ∃ j₀ : Fin M, 1 ≤ ‖z j₀‖) :
    ∃ k ∈ Finset.Icc (K + 1) (K + M),
      (1 / (64 * Real.exp 1)) ^ M * (1 / 2 : ℝ) ^ K ≤ ‖∑ j : Fin M, z j ^ k‖ := by
  classical
  -- Step 1: Normalize by `m₀ = max_j ‖z j‖ ≥ 1` so `‖w j‖ ≤ 1` and `‖w j₀‖ = 1`
  have huniv_ne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  set m₀ : ℝ := Finset.univ.sup' huniv_ne (fun j => ‖z j‖)
  obtain ⟨j₀, _, hm₀_eq⟩ := Finset.exists_mem_eq_sup' huniv_ne (fun j => ‖z j‖)
  have hm₀_ge1 : 1 ≤ m₀ := by
    obtain ⟨j₁, hj₁⟩ := hmax
    exact hj₁.trans (Finset.le_sup' (fun j => ‖z j‖) (Finset.mem_univ j₁))
  have hm₀_pos : 0 < m₀ := by linarith
  let w : Fin M → ℂ := fun j => z j / (m₀ : ℂ)
  have hw_le1 : ∀ j : Fin M, ‖w j‖ ≤ 1 := fun j => by
    dsimp only [w]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hm₀_pos.le, div_le_one hm₀_pos]
    exact Finset.le_sup' (fun i => ‖z i‖) (Finset.mem_univ j)
  have hw_j₀ : ‖w j₀‖ = 1 := by
    dsimp only [w]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hm₀_pos.le, ← hm₀_eq, div_self hm₀_pos.ne']
  -- Step 2: Choose a good circle radius `r ∈ (1/2, 1)` among `2 M` midpoints via product averaging!
  have hMR_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  let rad : Fin (2 * M) → ℝ := fun t => 1 / 2 + (2 * (t.1 : ℝ) + 1) / (8 * (M : ℝ))
  have hrad_gt_half : ∀ t : Fin (2 * M), 1 / 2 < rad t := fun t => by
    dsimp only [rad]; have : 0 < (2 * (t.1 : ℝ) + 1) / (8 * (M : ℝ)) := by positivity
    linarith
  have hrad_lt_one : ∀ t : Fin (2 * M), rad t < 1 := fun t => by
    dsimp only [rad]
    have ht : (t.1 : ℝ) + 1 ≤ 2 * (M : ℝ) := by exact_mod_cast t.2
    have hfrac : (2 * (t.1 : ℝ) + 1) / (8 * (M : ℝ)) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  have hrad_sub : ∀ t₁ t₂ : Fin (2 * M), rad t₁ - rad t₂ = ((t₁.1 : ℝ) - (t₂.1 : ℝ)) / (4 * (M : ℝ)) := by
    intro t₁ t₂; dsimp only [rad]; field_simp [hMR_pos.ne']; ring
  let bad : Finset (Fin (2 * M)) :=
    Finset.univ.filter (fun t => ∃ j : Fin M, |rad t - ‖w j‖| < 1 / (8 * (M : ℝ)))
  have hbad_card : bad.card ≤ M := by
    have hsub : bad ⊆ Finset.univ.biUnion
        (fun j : Fin M => Finset.univ.filter fun t : Fin (2 * M) => |rad t - ‖w j‖| < 1 / (8 * (M : ℝ))) := by
      intro t ht
      obtain ⟨j, hj⟩ := (Finset.mem_filter.mp ht).2
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hj⟩⟩
    calc bad.card
        ≤ ∑ j : Fin M, (Finset.univ.filter fun t : Fin (2 * M) => |rad t - ‖w j‖| < 1 / (8 * (M : ℝ))).card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin M, 1 := by
          refine Finset.sum_le_sum fun j _ => Finset.card_le_one.mpr fun t₁ ht₁ t₂ ht₂ => ?_
          have h1 := (Finset.mem_filter.mp ht₁).2
          have h2 := (Finset.mem_filter.mp ht₂).2
          by_contra hne
          have hne_val : t₁.1 ≠ t₂.1 := fun h => hne (Fin.ext h)
          have hdiff_ge : (1 : ℝ) ≤ |(t₁.1 : ℝ) - (t₂.1 : ℝ)| := by
            rcases lt_or_gt_of_ne hne_val with hlt | hgt
            · have : (t₁.1 : ℝ) + 1 ≤ (t₂.1 : ℝ) := by exact_mod_cast hlt
              rw [abs_of_neg (by linarith)]; linarith
            · have : (t₂.1 : ℝ) + 1 ≤ (t₁.1 : ℝ) := by exact_mod_cast hgt
              rw [abs_of_pos (by linarith)]; linarith
          have hrad_ge : 1 / (4 * (M : ℝ)) ≤ |rad t₁ - rad t₂| := by
            rw [hrad_sub, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * (M : ℝ))]
            exact div_le_div_of_nonneg_right hdiff_ge (by positivity)
          have htri : |rad t₁ - rad t₂| ≤ |rad t₁ - ‖w j‖| + |rad t₂ - ‖w j‖| := by
            have := abs_sub_le (rad t₁) ‖w j‖ (rad t₂)
            rwa [abs_sub_comm ‖w j‖ (rad t₂)] at this
          have hsum_lt : |rad t₁ - ‖w j‖| + |rad t₂ - ‖w j‖| < 1 / (4 * (M : ℝ)) := by
            have : 1 / (8 * (M : ℝ)) + 1 / (8 * (M : ℝ)) = 1 / (4 * (M : ℝ)) := by ring
            linarith
          linarith
      _ = M := by simp
  set G : Finset (Fin (2 * M)) := Finset.univ \ bad
  have hG_card : M ≤ G.card := by
    have h1 : G.card = (Finset.univ : Finset (Fin (2 * M))).card - bad.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ bad)
    rw [h1, Finset.card_univ, Fintype.card_fin]
    omega
  have hG_ne : G.Nonempty := Finset.card_pos.mp (by omega)
  have hG_sep : ∀ t ∈ G, ∀ j : Fin M, 1 / (8 * (M : ℝ)) ≤ |rad t - ‖w j‖| := by
    intro t ht j
    have hnb : t ∉ bad := (Finset.mem_sdiff.mp ht).2
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_lt] at hnb
    exact hnb j
  -- Product lower bound for EACH `j : Fin M` over `t ∈ G`:
  have hprod_j : ∀ j : Fin M, (1 / (16 * Real.exp 1)) ^ G.card ≤ ∏ t ∈ G, |rad t - ‖w j‖| := by
    intro j
    set Gpos : Finset (Fin (2 * M)) := G.filter (fun t => ‖w j‖ ≤ rad t)
    set Gneg : Finset (Fin (2 * M)) := G.filter (fun t => ¬ (‖w j‖ ≤ rad t))
    have hdisj : Disjoint Gpos Gneg := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hunion : G = Gpos ∪ Gneg := by
      ext t; simp only [Gpos, Gneg, Finset.mem_union, Finset.mem_filter]; tauto
    have hcard_add : Gpos.card + Gneg.card = G.card := by
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hpos_prod : (Gpos.card.factorial : ℝ) / (8 * (M : ℝ)) ^ Gpos.card ≤
        ∏ t ∈ Gpos, |rad t - ‖w j‖| := by
      let emb := Gpos.orderEmbOfFin rfl
      have hrew : ∏ t ∈ Gpos, |rad t - ‖w j‖| = ∏ i : Fin Gpos.card, |rad (emb i) - ‖w j‖| := by
        symm
        refine Finset.prod_bij (fun i _ => emb i) (fun i _ => Gpos.orderEmbOfFin_mem rfl i)
          (fun _ _ _ _ h => emb.injective h) ?_ (fun _ _ => rfl)
        intro t ht
        have hmem_range : t ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact ht
        obtain ⟨i, rfl⟩ := hmem_range
        exact ⟨i, Finset.mem_univ i, rfl⟩
      rw [hrew]
      have hterm : ∀ i : Fin Gpos.card, ((i.1 + 1 : ℕ) : ℝ) / (8 * (M : ℝ)) ≤ |rad (emb i) - ‖w j‖| := by
        intro i
        have hi0 : (0 : ℕ) < Gpos.card := lt_of_le_of_lt (Nat.zero_le _) i.2
        let i0 : Fin Gpos.card := ⟨0, hi0⟩
        have hmem0 : emb i0 ∈ Gpos := Gpos.orderEmbOfFin_mem rfl i0
        have hmemi : emb i ∈ Gpos := Gpos.orderEmbOfFin_mem rfl i
        have hsep0 : 1 / (8 * (M : ℝ)) ≤ rad (emb i0) - ‖w j‖ := by
          have hle := (Finset.mem_filter.mp hmem0).2
          have hsep := hG_sep (emb i0) (Finset.mem_filter.mp hmem0).1 j
          rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hsep
        have hstep : (emb i0).1 + i.1 ≤ (emb i).1 := by
          have haux : ∀ k : ℕ, (hk : k < Gpos.card) → (emb i0).1 + k ≤ (emb ⟨k, hk⟩).1 := by
            intro k
            induction k with
            | zero => intro hk; simp [i0]
            | succ k ih =>
              intro hk
              have hk' : k < Gpos.card := by omega
              have hlt : (emb ⟨k, hk'⟩).1 < (emb ⟨k + 1, hk⟩).1 := by
                have := emb.strictMono (show (⟨k, hk'⟩ : Fin Gpos.card) < ⟨k + 1, hk⟩ by
                  exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
                exact this
              have := ih hk'
              omega
          exact haux i.1 i.2
        have hdiff_rad : (i.1 : ℝ) / (4 * (M : ℝ)) ≤ rad (emb i) - rad (emb i0) := by
          rw [hrad_sub]
          have hle_val : (i.1 : ℝ) ≤ ((emb i).1 : ℝ) - ((emb i0).1 : ℝ) := by
            have : ((emb i0).1 : ℝ) + (i.1 : ℝ) ≤ ((emb i).1 : ℝ) := by exact_mod_cast hstep
            linarith
          exact div_le_div_of_nonneg_right hle_val (by positivity)
        have hle_i := (Finset.mem_filter.mp hmemi).2
        rw [abs_of_nonneg (sub_nonneg.mpr hle_i)]
        have h2i : ((i.1 + 1 : ℕ) : ℝ) / (8 * (M : ℝ)) ≤ 1 / (8 * (M : ℝ)) + (i.1 : ℝ) / (4 * (M : ℝ)) := by
          push_cast
          have : ((i.1 : ℝ) + 1) / (8 * (M : ℝ)) + (i.1 : ℝ) / (8 * (M : ℝ)) =
              1 / (8 * (M : ℝ)) + (i.1 : ℝ) / (4 * (M : ℝ)) := by ring
          have hnn : 0 ≤ (i.1 : ℝ) / (8 * (M : ℝ)) := by positivity
          linarith
        linarith
      calc (Gpos.card.factorial : ℝ) / (8 * (M : ℝ)) ^ Gpos.card
          = ∏ i : Fin Gpos.card, ((i.1 + 1 : ℕ) : ℝ) / (8 * (M : ℝ)) := by
            rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            congr 1
            have hfac : ∏ i : Fin Gpos.card, ((i.1 + 1 : ℕ) : ℝ) = (Gpos.card.factorial : ℝ) := by
              rw [Fin.prod_univ_eq_prod_range (fun k => ((k + 1 : ℕ) : ℝ))]
              exact_mod_cast Finset.prod_range_add_one_eq_factorial Gpos.card
            exact hfac.symm
        _ ≤ ∏ i : Fin Gpos.card, |rad (emb i) - ‖w j‖| :=
            Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hterm i)
    have hneg_prod : (Gneg.card.factorial : ℝ) / (8 * (M : ℝ)) ^ Gneg.card ≤
        ∏ t ∈ Gneg, |rad t - ‖w j‖| := by
      let emb := Gneg.orderEmbOfFin rfl
      have hrew : ∏ t ∈ Gneg, |rad t - ‖w j‖| = ∏ i : Fin Gneg.card, |rad (emb i) - ‖w j‖| := by
        symm
        refine Finset.prod_bij (fun i _ => emb i) (fun i _ => Gneg.orderEmbOfFin_mem rfl i)
          (fun _ _ _ _ h => emb.injective h) ?_ (fun _ _ => rfl)
        intro t ht
        have hmem_range : t ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact ht
        obtain ⟨i, rfl⟩ := hmem_range
        exact ⟨i, Finset.mem_univ i, rfl⟩
      rw [hrew]
      have hterm : ∀ i : Fin Gneg.card,
          ((Gneg.card - 1 - i.1 + 1 : ℕ) : ℝ) / (8 * (M : ℝ)) ≤ |rad (emb i) - ‖w j‖| := by
        intro i
        have hgn_pos : 0 < Gneg.card := lt_of_le_of_lt (Nat.zero_le _) i.2
        have hlast_lt : Gneg.card - 1 < Gneg.card := by omega
        let ilast : Fin Gneg.card := ⟨Gneg.card - 1, hlast_lt⟩
        have hmemL : emb ilast ∈ Gneg := Gneg.orderEmbOfFin_mem rfl ilast
        have hmemi : emb i ∈ Gneg := Gneg.orderEmbOfFin_mem rfl i
        have hsepL : 1 / (8 * (M : ℝ)) ≤ ‖w j‖ - rad (emb ilast) := by
          have hlt : rad (emb ilast) < ‖w j‖ := not_le.mp (Finset.mem_filter.mp hmemL).2
          have hsep := hG_sep (emb ilast) (Finset.mem_filter.mp hmemL).1 j
          rwa [abs_of_neg (sub_neg.mpr hlt), neg_sub] at hsep
        have hstep : (emb i).1 + (Gneg.card - 1 - i.1) ≤ (emb ilast).1 := by
          have haux : ∀ d : ℕ, ∀ (k : ℕ) (hk : k + d < Gneg.card),
              (emb ⟨k, by omega⟩).1 + d ≤ (emb ⟨k + d, hk⟩).1 := by
            intro d
            induction d with
            | zero => intro k hk; simp
            | succ d ih =>
              intro k hk
              have hk' : k + d < Gneg.card := by omega
              have hfin : (⟨k + d + 1, by omega⟩ : Fin Gneg.card) = ⟨k + (d + 1), hk⟩ := by
                apply Fin.ext; dsimp only; omega
              have hlt : (emb ⟨k + d, hk'⟩).1 < (emb ⟨k + d + 1, by omega⟩).1 :=
                emb.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
              rw [hfin] at hlt
              have := ih k hk'
              omega
          have hsum_eq : i.1 + (Gneg.card - 1 - i.1) = Gneg.card - 1 := by omega
          have h := haux (Gneg.card - 1 - i.1) i.1 (by omega)
          have hfin : (⟨i.1 + (Gneg.card - 1 - i.1), by omega⟩ : Fin Gneg.card) = ilast :=
            Fin.ext hsum_eq
          simpa [hfin] using h
        have hdiff_rad : ((Gneg.card - 1 - i.1 : ℕ) : ℝ) / (4 * (M : ℝ)) ≤
            rad (emb ilast) - rad (emb i) := by
          rw [hrad_sub]
          have hle_val : ((Gneg.card - 1 - i.1 : ℕ) : ℝ) ≤ ((emb ilast).1 : ℝ) - ((emb i).1 : ℝ) := by
            have : ((emb i).1 : ℝ) + ((Gneg.card - 1 - i.1 : ℕ) : ℝ) ≤ ((emb ilast).1 : ℝ) := by
              exact_mod_cast hstep
            linarith
          exact div_le_div_of_nonneg_right hle_val (by positivity)
        have hlt_i : rad (emb i) < ‖w j‖ := not_le.mp (Finset.mem_filter.mp hmemi).2
        rw [abs_of_neg (sub_neg.mpr hlt_i), neg_sub]
        have h2d : ((Gneg.card - 1 - i.1 + 1 : ℕ) : ℝ) / (8 * (M : ℝ)) ≤
            1 / (8 * (M : ℝ)) + ((Gneg.card - 1 - i.1 : ℕ) : ℝ) / (4 * (M : ℝ)) := by
          push_cast
          have hnn : 0 ≤ ((Gneg.card - 1 - i.1 : ℕ) : ℝ) / (8 * (M : ℝ)) := by positivity
          have : (((Gneg.card - 1 - i.1 : ℕ) : ℝ) + 1) / (8 * (M : ℝ)) +
              ((Gneg.card - 1 - i.1 : ℕ) : ℝ) / (8 * (M : ℝ)) =
              1 / (8 * (M : ℝ)) + ((Gneg.card - 1 - i.1 : ℕ) : ℝ) / (4 * (M : ℝ)) := by ring
          linarith
        linarith
      calc (Gneg.card.factorial : ℝ) / (8 * (M : ℝ)) ^ Gneg.card
          = ∏ i : Fin Gneg.card, ((Gneg.card - 1 - i.1 + 1 : ℕ) : ℝ) / (8 * (M : ℝ)) := by
            rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            congr 1
            have hrev : ∏ i : Fin Gneg.card, ((Gneg.card - 1 - i.1 + 1 : ℕ) : ℝ) =
                ∏ i : Fin Gneg.card, ((i.1 + 1 : ℕ) : ℝ) := by
              refine Finset.prod_bij (fun i _ => ⟨Gneg.card - 1 - i.1, by omega⟩)
                (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
              · intro i₁ _ i₂ _ heq
                have hval := congrArg Fin.val heq
                dsimp only at hval
                exact Fin.ext (by omega)
              · intro k _
                refine ⟨⟨Gneg.card - 1 - k.1, by omega⟩, Finset.mem_univ _, ?_⟩
                apply Fin.ext; dsimp only; omega
            rw [hrev, Fin.prod_univ_eq_prod_range (fun k => ((k + 1 : ℕ) : ℝ))]
            exact_mod_cast (Finset.prod_range_add_one_eq_factorial Gneg.card).symm
        _ ≤ ∏ i : Fin Gneg.card, |rad (emb i) - ‖w j‖| :=
            Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hterm i)
    -- Combine `Gpos` and `Gneg` via `a! * b! ≥ (a + b)! / 2^(a + b)` and `(n / e)^n ≤ n!`!
    have hprod_split : ∏ t ∈ G, |rad t - ‖w j‖| =
        (∏ t ∈ Gpos, |rad t - ‖w j‖|) * (∏ t ∈ Gneg, |rad t - ‖w j‖|) := by
      rw [hunion, Finset.prod_union hdisj]
    rw [hprod_split]
    have hstirl := div_exp_one_pow_le_factorial G.card
    have hbin := factorial_add_div_two_pow_le Gpos.card Gneg.card
    rw [hcard_add] at hbin
    have hM_le_G : (M : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hG_card
    have hbase : 1 / (16 * Real.exp 1) ≤ (G.card : ℝ) / (16 * Real.exp 1 * (M : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.exp_pos 1]
    calc (1 / (16 * Real.exp 1)) ^ G.card
        ≤ ((G.card : ℝ) / (16 * Real.exp 1 * (M : ℝ))) ^ G.card :=
          pow_le_pow_left₀ (by positivity) hbase G.card
      _ = (((G.card : ℝ) / Real.exp 1) ^ G.card) / ((2 : ℝ) ^ G.card * (8 * (M : ℝ)) ^ G.card) := by
          rw [div_pow, div_pow, ← mul_pow, div_div]; congr 2; ring
      _ ≤ (G.card.factorial : ℝ) / ((2 : ℝ) ^ G.card * (8 * (M : ℝ)) ^ G.card) :=
          div_le_div_of_nonneg_right hstirl (by positivity)
      _ = ((G.card.factorial : ℝ) / (2 : ℝ) ^ G.card) / (8 * (M : ℝ)) ^ G.card := by rw [div_div]
      _ ≤ ((Gpos.card.factorial : ℝ) * (Gneg.card.factorial : ℝ)) / (8 * (M : ℝ)) ^ (Gpos.card + Gneg.card) := by
          rw [hcard_add]; exact div_le_div_of_nonneg_right hbin (by positivity)
      _ = ((Gpos.card.factorial : ℝ) / (8 * (M : ℝ)) ^ Gpos.card) *
          ((Gneg.card.factorial : ℝ) / (8 * (M : ℝ)) ^ Gneg.card) := by rw [pow_add]; ring
      _ ≤ (∏ t ∈ Gpos, |rad t - ‖w j‖|) * (∏ t ∈ Gneg, |rad t - ‖w j‖|) :=
          mul_le_mul hpos_prod hneg_prod (by positivity)
            (Finset.prod_nonneg fun _ _ => abs_nonneg _)
  -- Pigeonhole on the product over `t ∈ G`:
  have hex_t : ∃ t ∈ G, (1 / (16 * Real.exp 1)) ^ M ≤ ∏ j : Fin M, |rad t - ‖w j‖| := by
    by_contra hall
    push Not at hall
    have hlt_prod : ∏ t ∈ G, ∏ j : Fin M, |rad t - ‖w j‖| <
        ∏ _t ∈ G, (1 / (16 * Real.exp 1)) ^ M :=
      Finset.prod_lt_prod_of_nonempty (fun t ht => Finset.prod_pos fun j _ =>
        lt_of_lt_of_le (by positivity) (hG_sep t ht j))
        hall hG_ne
    rw [Finset.prod_comm, Finset.prod_const] at hlt_prod
    have hge_prod : ((1 / (16 * Real.exp 1)) ^ M) ^ G.card ≤
        ∏ j : Fin M, ∏ t ∈ G, |rad t - ‖w j‖| := by
      have hpow_swap : ((1 / (16 * Real.exp 1)) ^ M) ^ G.card =
          ∏ _j : Fin M, (1 / (16 * Real.exp 1)) ^ G.card := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul, mul_comm M G.card]
      rw [hpow_swap]
      exact Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => hprod_j j)
    linarith
  obtain ⟨t_star, ht_star_G, hprod_r⟩ := hex_t
  set r : ℝ := rad t_star
  have hr_half : 1 / 2 < r := hrad_gt_half t_star
  have hr_pos : 0 < r := by linarith
  have hr_lt1 : r < 1 := hrad_lt_one t_star
  have hr_ne_w : ∀ j : Fin M, r ≠ ‖w j‖ := fun j heq => by
    have hsep := hG_sep t_star ht_star_G j
    change rad t_star = ‖w j‖ at heq
    rw [heq, sub_self, abs_zero] at hsep
    have : (0 : ℝ) < 1 / (8 * (M : ℝ)) := by positivity
    linarith
  -- Step 3: Exact polynomial identity & circle-integral evaluation on `C(0, r)`!
  let s : ℕ → ℂ := fun k => ∑ j : Fin M, w j ^ k
  set I_k : Finset ℕ := Finset.Icc (K + 1) (K + M)
  have hIk_ne : I_k.Nonempty := ⟨K + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  set S : ℝ := I_k.sup' hIk_ne (fun k => ‖s k‖)
  have hS_nn : 0 ≤ S := (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖s k‖) hIk_ne.choose_spec)
  have hs_le_S : ∀ k ∈ I_k, ‖s k‖ ≤ S := fun k hk => Finset.le_sup' (fun m => ‖s m‖) hk
  let P : ℂ → ℂ := fun ζ => ∏ j : Fin M, (ζ - w j)
  let cA : Finset (Fin M) → ℂ := fun A => ∏ j ∈ A, (-w j)
  have hP_exp : ∀ ζ : ℂ, P ζ = ∑ A ∈ (Finset.univ : Finset (Fin M)).powerset,
      cA A * ζ ^ (M - A.card) := by
    intro ζ
    have h1 : P ζ = ∏ j : Fin M, (-w j + ζ) :=
      Finset.prod_congr rfl fun j _ => by ring
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun A hA => ?_
    dsimp only [cA]
    congr 1
    rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA), Finset.card_univ, Fintype.card_fin]
  let H : ℂ → ℂ := fun ζ =>
    ∑ A ∈ (Finset.univ : Finset (Fin M)).powerset,
      cA A * ∑ m ∈ Finset.range (M - A.card), ζ ^ m * s (K + M - A.card - m)
  have hH_eq : ∀ ζ : ℂ, (∀ j : Fin M, ζ ≠ w j) → ζ ≠ 0 →
      H ζ / (ζ ^ (K + 1) * P ζ) =
        (∑ j : Fin M, (ζ - w j)⁻¹) - ∑ k ∈ Finset.range (K + 1), s k * (ζ ^ (k + 1))⁻¹ := by
    intro ζ hζw hζ0
    have hP_ne : P ζ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hζw j)
    have hpow_ne : ζ ^ (K + 1) ≠ 0 := pow_ne_zero _ hζ0
    -- First show `H ζ = ∑ j, w j ^ (K + 1) * (P ζ / (ζ - w j))`!
    have hH_num : H ζ = ∑ j : Fin M, w j ^ (K + 1) * (P ζ / (ζ - w j)) := by
      have hterm_j : ∀ j : Fin M,
          P ζ / (ζ - w j) = ∑ A ∈ (Finset.univ : Finset (Fin M)).powerset,
            cA A * ∑ m ∈ Finset.range (M - A.card), ζ ^ m * w j ^ (M - A.card - 1 - m) := by
        intro j
        have hPj0 : P (w j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
        have hsub : P ζ = P ζ - P (w j) := by rw [hPj0, sub_zero]
        have hne : ζ - w j ≠ 0 := sub_ne_zero.mpr (hζw j)
        rw [div_eq_iff hne, hsub, hP_exp ζ, hP_exp (w j), ← Finset.sum_sub_distrib, Finset.sum_mul]
        refine Finset.sum_congr rfl fun A _ => ?_
        have hgeom := mul_geom_sum_eq_pow_sub_pow ζ (w j) (M - A.card)
        calc cA A * ζ ^ (M - A.card) - cA A * w j ^ (M - A.card)
            = cA A * (ζ ^ (M - A.card) - w j ^ (M - A.card)) := by ring
          _ = cA A * ((ζ - w j) * ∑ m ∈ Finset.range (M - A.card), ζ ^ m * w j ^ (M - A.card - 1 - m)) := by
              rw [hgeom]
          _ = cA A * (∑ m ∈ Finset.range (M - A.card), ζ ^ m * w j ^ (M - A.card - 1 - m)) * (ζ - w j) := by
              ring
      have hrew_j : ∑ j : Fin M, w j ^ (K + 1) * (P ζ / (ζ - w j)) =
          ∑ j : Fin M, ∑ A ∈ (Finset.univ : Finset (Fin M)).powerset,
            w j ^ (K + 1) * (cA A * ∑ m ∈ Finset.range (M - A.card), ζ ^ m * w j ^ (M - A.card - 1 - m)) :=
        Finset.sum_congr rfl fun j _ => by rw [hterm_j j, Finset.mul_sum]
      rw [hrew_j, Finset.sum_comm]
      refine Finset.sum_congr rfl fun A hA => ?_
      have hA_card : A.card ≤ M := by
        simpa using Finset.card_le_card (Finset.mem_powerset.mp hA)
      have hpull : ∑ j : Fin M, w j ^ (K + 1) * (cA A * ∑ m ∈ Finset.range (M - A.card),
            ζ ^ m * w j ^ (M - A.card - 1 - m)) =
          cA A * ∑ m ∈ Finset.range (M - A.card), ζ ^ m * ∑ j : Fin M, w j ^ (K + M - A.card - m) := by
        rw [Finset.mul_sum]
        have h1 : ∀ j : Fin M, w j ^ (K + 1) * (cA A * ∑ m ∈ Finset.range (M - A.card),
              ζ ^ m * w j ^ (M - A.card - 1 - m)) =
            ∑ m ∈ Finset.range (M - A.card), cA A * (ζ ^ m * (w j ^ (K + 1) * w j ^ (M - A.card - 1 - m))) := by
          intro j; rw [← mul_assoc, mul_comm (w j ^ (K + 1)) (cA A), mul_assoc, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => by ring
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmlt : m < M - A.card := Finset.mem_range.mp hm
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← pow_add]
        have hexp : K + 1 + (M - A.card - 1 - m) = K + M - A.card - m := by omega
        rw [hexp]
      exact hpull.symm
    -- Now divide `H ζ` by `ζ^(K+1) * P ζ` and match with geometric series!
    rw [hH_num, Finset.sum_div]
    have hterm_div : ∀ j : Fin M,
        w j ^ (K + 1) * (P ζ / (ζ - w j)) / (ζ ^ (K + 1) * P ζ) =
          (ζ - w j)⁻¹ - ∑ k ∈ Finset.range (K + 1), w j ^ k * (ζ ^ (k + 1))⁻¹ := by
      intro j
      have hne : ζ - w j ≠ 0 := sub_ne_zero.mpr (hζw j)
      have hgeom : (ζ - w j) * ∑ k ∈ Finset.range (K + 1), w j ^ k * ζ ^ (K - k) =
          ζ ^ (K + 1) - w j ^ (K + 1) := by
        have h := mul_geom_sum_eq_pow_sub_pow ζ (w j) (K + 1)
        rw [Nat.add_sub_cancel] at h
        have hrev : ∑ m ∈ Finset.range (K + 1), ζ ^ m * w j ^ (K - m) =
            ∑ k ∈ Finset.range (K + 1), w j ^ k * ζ ^ (K - k) := by
          refine Finset.sum_bij (fun m _ => K - m)
            (fun m hm => Finset.mem_range.mpr (by have := Finset.mem_range.mp hm; omega))
            (fun m₁ hm₁ m₂ hm₂ heq => by
              have := Finset.mem_range.mp hm₁; have := Finset.mem_range.mp hm₂; omega)
            (fun k hk => ⟨K - k, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega),
              by have := Finset.mem_range.mp hk; omega⟩)
            (fun m hm => by
              have := Finset.mem_range.mp hm
              rw [show K - (K - m) = m by omega, mul_comm])
        rwa [hrev] at h
      have hsum_div : ∑ k ∈ Finset.range (K + 1), w j ^ k * (ζ ^ (k + 1))⁻¹ =
          (∑ k ∈ Finset.range (K + 1), w j ^ k * ζ ^ (K - k)) / ζ ^ (K + 1) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hpow_split : ζ ^ (K + 1) = ζ ^ (k + 1) * ζ ^ (K - k) := by
          rw [← pow_add]; congr 1; omega
        have hkpow : ζ ^ (k + 1) ≠ 0 := pow_ne_zero _ hζ0
        have hKpow : ζ ^ (K - k) ≠ 0 := pow_ne_zero _ hζ0
        rw [hpow_split]; field_simp [hkpow, hKpow]
      rw [hsum_div]
      field_simp [hP_ne, hne, hpow_ne]
      linear_combination hgeom
    simp_rw [hterm_div, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [s]; rw [Finset.sum_mul]
  -- Evaluate `∮ z in C(0, r), H z / (z^(K+1) * P z)` using the RHS!
  have hnorm_P_ge : ∀ z ∈ Metric.sphere (0 : ℂ) r, (1 / (16 * Real.exp 1)) ^ M ≤ ‖P z‖ := by
    intro z hz
    have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    dsimp only [P]
    rw [norm_prod]
    refine hprod_r.trans (Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_)
    rw [← hzn]
    exact abs_norm_sub_norm_le z (w j)
  have hnorm_H_le : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖H z‖ ≤ (2 : ℝ) ^ M * (M : ℝ) * S := by
    intro z hz
    have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzn_le1 : ‖z‖ ≤ 1 := by linarith
    dsimp only [H]
    calc ‖∑ A ∈ (Finset.univ : Finset (Fin M)).powerset,
            cA A * ∑ m ∈ Finset.range (M - A.card), z ^ m * s (K + M - A.card - m)‖
        ≤ ∑ A ∈ (Finset.univ : Finset (Fin M)).powerset,
            ‖cA A * ∑ m ∈ Finset.range (M - A.card), z ^ m * s (K + M - A.card - m)‖ := norm_sum_le _ _
      _ ≤ ∑ _A ∈ (Finset.univ : Finset (Fin M)).powerset, (M : ℝ) * S := by
          refine Finset.sum_le_sum fun A hA => ?_
          have hA_card : A.card ≤ M := by simpa using Finset.card_le_card (Finset.mem_powerset.mp hA)
          rw [norm_mul]
          have hcA_le1 : ‖cA A‖ ≤ 1 := by
            dsimp only [cA]; rw [norm_prod]
            exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => by
              rw [norm_neg]; exact hw_le1 j
          have hinner : ‖∑ m ∈ Finset.range (M - A.card), z ^ m * s (K + M - A.card - m)‖ ≤
              (M : ℝ) * S := by
            calc _ ≤ ∑ m ∈ Finset.range (M - A.card), ‖z ^ m * s (K + M - A.card - m)‖ := norm_sum_le _ _
              _ ≤ ∑ _m ∈ Finset.range (M - A.card), S := by
                  refine Finset.sum_le_sum fun m hm => ?_
                  have hmlt : m < M - A.card := Finset.mem_range.mp hm
                  rw [norm_mul, norm_pow]
                  have hk_mem : K + M - A.card - m ∈ I_k :=
                    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
                  calc ‖z‖ ^ m * ‖s (K + M - A.card - m)‖
                      ≤ 1 * S := mul_le_mul (pow_le_one₀ (norm_nonneg z) hzn_le1) (hs_le_S _ hk_mem)
                        (norm_nonneg _) zero_le_one
                    _ = S := one_mul _
              _ = ((M - A.card : ℕ) : ℝ) * S := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              _ ≤ (M : ℝ) * S := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le M A.card) hS_nn
          calc ‖cA A‖ * ‖∑ m ∈ Finset.range (M - A.card), z ^ m * s (K + M - A.card - m)‖
              ≤ 1 * ((M : ℝ) * S) := mul_le_mul hcA_le1 hinner (norm_nonneg _) zero_le_one
            _ = (M : ℝ) * S := one_mul _
      _ = (2 : ℝ) ^ M * (M : ℝ) * S := by
          rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- Evaluate the circle integral of the RHS!
  have hci_sub : ∀ j : Fin M, CircleIntegrable (fun z : ℂ => (z - w j)⁻¹) 0 r := fun j => by
    have hcont : ContinuousOn (fun z : ℂ => (z - w j)⁻¹) (Metric.sphere 0 r) :=
      ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz h0 => by
        have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        exact hr_ne_w j (hzn ▸ congrArg norm (sub_eq_zero.mp h0))
    exact hcont.circleIntegrable hr_pos.le
  have hci_pow : ∀ k : ℕ, CircleIntegrable (fun z : ℂ => s k * (z ^ (k + 1))⁻¹) 0 r := fun k => by
    have hcont : ContinuousOn (fun z : ℂ => s k * (z ^ (k + 1))⁻¹) (Metric.sphere 0 r) :=
      continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.pow _) fun z hz h0 => by
        have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        have hne : z ≠ 0 := fun hz0 => by rw [hz0, norm_zero] at hzn; linarith
        exact pow_ne_zero _ hne h0)
    exact hcont.circleIntegrable hr_pos.le
  have hci_eq : (∮ z in C(0, r), H z / (z ^ (K + 1) * P z)) =
      -((Finset.univ.filter (fun j : Fin M => r < ‖w j‖)).card : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have hcongr : Set.EqOn (fun z => H z / (z ^ (K + 1) * P z))
        (fun z => (∑ j : Fin M, (z - w j)⁻¹) - ∑ k ∈ Finset.range (K + 1), s k * (z ^ (k + 1))⁻¹)
        (Metric.sphere 0 r) := by
      intro z hz
      have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hz0 : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at hzn; linarith
      have hzw : ∀ j : Fin M, z ≠ w j := fun j h => hr_ne_w j (hzn ▸ congrArg norm h)
      exact hH_eq z hzw hz0
    rw [circleIntegral.integral_congr hr_pos.le hcongr]
    obtain ⟨hsum1, hsum1_eq⟩ := circleIntegral_finsetSum (Finset.univ : Finset (Fin M))
      (fun j z => (z - w j)⁻¹) 0 r (fun j _ => hci_sub j)
    obtain ⟨hsum2, hsum2_eq⟩ := circleIntegral_finsetSum (Finset.range (K + 1))
      (fun k z => s k * (z ^ (k + 1))⁻¹) 0 r (fun k _ => hci_pow k)
    rw [circleIntegral.integral_sub hsum1 hsum2, hsum1_eq, hsum2_eq]
    have hterm_j : ∀ j : Fin M,
        (∮ z in C(0, r), (z - w j)⁻¹) = if ‖w j‖ < r then 2 * (Real.pi : ℂ) * I else 0 := fun j => by
      by_cases hlt : ‖w j‖ < r
      · rw [if_pos hlt, circleIntegral_inv_sub_of_lt hr_pos hlt]
      · have hgt : r < ‖w j‖ := lt_of_le_of_ne (not_lt.mp hlt) (hr_ne_w j)
        rw [if_neg hlt, circleIntegral_inv_sub_of_gt hr_pos hgt]
    simp_rw [hterm_j]
    have hpart1 : ∑ j : Fin M, (if ‖w j‖ < r then 2 * (Real.pi : ℂ) * I else 0) =
        ((Finset.univ.filter (fun j : Fin M => ‖w j‖ < r)).card : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hpart2 : ∑ k ∈ Finset.range (K + 1), (∮ z in C(0, r), s k * (z ^ (k + 1))⁻¹) =
        (M : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [Finset.sum_eq_single 0]
      · simp only [zero_add, pow_one]
        rw [circleIntegral.integral_const_mul]
        have hs0 : s 0 = (M : ℂ) := by simp [s]
        rw [hs0]
        have h0 := circleIntegral_inv_sub_of_lt hr_pos (w := 0) (by simpa using hr_pos)
        simp only [sub_zero] at h0
        rw [h0]
      · intro k _ hk0
        rw [circleIntegral.integral_const_mul, circleIntegral_inv_pow_eq_zero hr_pos (Nat.pos_of_ne_zero hk0),
          mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos K)) h
    rw [hpart1, hpart2]
    have hcard_sum : (Finset.univ.filter (fun j : Fin M => ‖w j‖ < r)).card +
        (Finset.univ.filter (fun j : Fin M => r < ‖w j‖)).card = M := by
      have heq : Finset.univ.filter (fun j : Fin M => r < ‖w j‖) =
          Finset.univ.filter (fun j : Fin M => ¬ (‖w j‖ < r)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => not_lt.mpr h.le, fun h => lt_of_le_of_ne (not_lt.mp h) (hr_ne_w j)⟩
      have hdisj : Disjoint (Finset.univ.filter (fun j : Fin M => ‖w j‖ < r))
          (Finset.univ.filter (fun j : Fin M => ¬ (‖w j‖ < r))) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : Finset.univ.filter (fun j : Fin M => ‖w j‖ < r) ∪
          Finset.univ.filter (fun j : Fin M => ¬ (‖w j‖ < r)) = Finset.univ := by
        ext j
        by_cases h : ‖w j‖ < r
        · simp [h]
        · simp [h, le_of_not_gt h]
      rw [heq, ← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have hcardC : ((Finset.univ.filter (fun j : Fin M => ‖w j‖ < r)).card : ℂ) +
        ((Finset.univ.filter (fun j : Fin M => r < ‖w j‖)).card : ℂ) = (M : ℂ) := by
      exact_mod_cast hcard_sum
    linear_combination hcardC * (2 * (Real.pi : ℂ) * I)
  -- Compare lower bound `2 π` with upper bound on `‖∮ z in C(0, r), H z / (z^(K+1) * P z)‖`!
  have hgt_card_ge1 : 1 ≤ (Finset.univ.filter (fun j : Fin M => r < ‖w j‖)).card := by
    refine Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, ?_⟩⟩
    rw [hw_j₀]; exact hr_lt1
  have hlhs_ge : 2 * Real.pi ≤ ‖∮ z in C(0, r), H z / (z ^ (K + 1) * P z)‖ := by
    rw [hci_eq, norm_mul, norm_neg, Complex.norm_natCast, norm_mul, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_I, mul_one]
    have hc1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun j : Fin M => r < ‖w j‖)).card : ℝ) := by
      exact_mod_cast hgt_card_ge1
    nlinarith [Real.pi_pos]
  set B_sup : ℝ := ((2 : ℝ) ^ M * (M : ℝ) * S) / (r ^ (K + 1) * (1 / (16 * Real.exp 1)) ^ M)
  have hB_nn : 0 ≤ B_sup := by dsimp only [B_sup]; positivity
  have hlhs_le : ‖∮ z in C(0, r), H z / (z ^ (K + 1) * P z)‖ ≤ 2 * Real.pi * r * B_sup := by
    unfold circleIntegral
    have hbound : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
        ‖deriv (circleMap 0 r) θ • (H (circleMap 0 r θ) / ((circleMap 0 r θ) ^ (K + 1) * P (circleMap 0 r θ)))‖ ≤
          r * B_sup := by
      intro θ _
      have hmem : circleMap 0 r θ ∈ Metric.sphere (0 : ℂ) r := circleMap_mem_sphere 0 hr_pos.le θ
      have hnorm_c : ‖circleMap 0 r θ‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hmem
      have hnorm_d : ‖deriv (circleMap 0 r) θ‖ = r := by
        rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr_pos]
      rw [norm_smul, hnorm_d, norm_div, norm_mul, norm_pow, hnorm_c]
      refine mul_le_mul_of_nonneg_left ?_ hr_pos.le
      exact div_le_div₀ (by positivity) (hnorm_H_le _ hmem) (by positivity)
        (mul_le_mul_of_nonneg_left (hnorm_P_ge _ hmem) (pow_nonneg hr_pos.le _))
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hint
    linarith
  have h1_le : 1 ≤ r * B_sup := by
    have h2pi : 0 < 2 * Real.pi := by positivity
    nlinarith
  -- Solve for `S`!
  have hM_le_2M : (M : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast Nat.lt_two_pow_self.le
  have hrK_ge : (1 / 2 : ℝ) ^ K ≤ r ^ K := pow_le_pow_left₀ (by norm_num) hr_half.le K
  have hS_ge : (1 / (64 * Real.exp 1)) ^ M * (1 / 2 : ℝ) ^ K ≤ S := by
    have hden_pos : 0 < r ^ (K + 1) * (1 / (16 * Real.exp 1)) ^ M := by positivity
    have hmul := (le_div_iff₀ hden_pos).mp (by
      calc 1 / r ≤ B_sup := (div_le_iff₀ hr_pos).mpr (by linarith)
        _ = ((2 : ℝ) ^ M * (M : ℝ) * S) / (r ^ (K + 1) * (1 / (16 * Real.exp 1)) ^ M) := rfl)
    have hrK : 1 / r * (r ^ (K + 1) * (1 / (16 * Real.exp 1)) ^ M) =
        r ^ K * (1 / (16 * Real.exp 1)) ^ M := by
      rw [pow_succ]; field_simp [hr_pos.ne']
    rw [hrK] at hmul
    have hprod_le : (2 : ℝ) ^ M * (M : ℝ) ≤ (4 : ℝ) ^ M := by
      calc (2 : ℝ) ^ M * (M : ℝ) ≤ (2 : ℝ) ^ M * (2 : ℝ) ^ M :=
            mul_le_mul_of_nonneg_left hM_le_2M (by positivity)
        _ = (4 : ℝ) ^ M := by rw [← mul_pow]; norm_num
    have h4S : r ^ K * (1 / (16 * Real.exp 1)) ^ M ≤ (4 : ℝ) ^ M * S :=
      hmul.trans (mul_le_mul_of_nonneg_right hprod_le hS_nn)
    have hstep : (1 / 2 : ℝ) ^ K * (1 / (16 * Real.exp 1)) ^ M ≤ (4 : ℝ) ^ M * S :=
      (mul_le_mul_of_nonneg_right hrK_ge (by positivity)).trans h4S
    have hdiv := (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ M)).mpr (by linarith :
      (1 / 2 : ℝ) ^ K * (1 / (16 * Real.exp 1)) ^ M ≤ S * (4 : ℝ) ^ M)
    refine le_trans ?_ hdiv
    have halg : (1 / (64 * Real.exp 1)) ^ M * (1 / 2 : ℝ) ^ K =
        ((1 / 2 : ℝ) ^ K * (1 / (16 * Real.exp 1)) ^ M) / (4 : ℝ) ^ M := by
      have h64 : (1 / (64 * Real.exp 1)) = (1 / (16 * Real.exp 1)) / 4 := by ring
      rw [h64, div_pow]; ring
    rw [halg]
  -- Extract the maximizing `k ∈ I_k` and un-normalize by `m₀ ^ k ≥ 1`!
  obtain ⟨k, hk_mem, hk_eq⟩ := Finset.exists_mem_eq_sup' hIk_ne (fun k => ‖s k‖)
  refine ⟨k, hk_mem, ?_⟩
  have hm₀_pow : 1 ≤ m₀ ^ k := one_le_pow₀ hm₀_ge1
  have hnorm_scale : ‖∑ j : Fin M, z j ^ k‖ = m₀ ^ k * ‖s k‖ := by
    have hsum_scale : ∑ j : Fin M, z j ^ k = (m₀ : ℂ) ^ k * s k := by
      dsimp only [s, w]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero k (Complex.ofReal_ne_zero.mpr hm₀_pos.ne'))]
    rw [hsum_scale, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hm₀_pos.le]
  rw [hnorm_scale, ← hk_eq]
  calc (1 / (64 * Real.exp 1)) ^ M * (1 / 2 : ℝ) ^ K
      ≤ S := hS_ge
    _ = 1 * S := (one_mul S).symm
    _ ≤ m₀ ^ k * S := mul_le_mul_of_nonneg_right hm₀_pow hS_nn

/-! ### Section 3b: Term-by-Term High-Derivative Identities & Local Multiplicity Zero Count -/

/-- Elementary telescoping bound `∑' n : ℕ, ((n + 1 : ℝ) ^ 2)⁻¹ ≤ 2`. -/
private lemma tsum_inv_add_one_sq_le_two :
    ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hsum_sq : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have h1 : Summable (fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h1
  refine hsum_sq.tsum_le_of_sum_le fun s => ?_
  set N : ℕ := s.sup id + 1
  have hsub : s ⊆ Finset.range N := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  have hbound : ∀ m : ℕ, ∑ n ∈ Finset.range (m + 1), (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
      2 - 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp; norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      have hterm : (((m + 1 + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
          1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 2 : ℕ) : ℝ) := by
        have hdiff : 1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 2 : ℕ) : ℝ) =
            1 / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) := by
          field_simp [hm1.ne', hm2.ne']
          push_cast; ring
        rw [hdiff, one_div]
        refine inv_anti₀ (by positivity) ?_
        have hle : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (m + 1)
        have : (((m + 1 + 1 : ℕ) : ℝ) ^ 2) = ((m + 2 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) := by
          push_cast; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hle hm2.le
      linarith
  have hN : N = (s.sup id) + 1 := rfl
  rw [hN]
  have h1 := hbound (s.sup id)
  have hpos : (0 : ℝ) < 1 / ((s.sup id + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Exact `k`-th derivative of `z ↦ (z - c)⁻¹` at `s ≠ c`. -/
private lemma iteratedDeriv_inv_sub_const (k : ℕ) (c : ℂ) :
    ∀ s : ℂ, s ≠ c →
      iteratedDeriv k (fun z : ℂ => (z - c)⁻¹) s =
        (-1 : ℂ) ^ k * (k.factorial : ℂ) * ((s - c) ^ (k + 1))⁻¹ := by
  induction k with
  | zero =>
    intro s _
    simp
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun z : ℂ => (z - c)⁻¹) =ᶠ[𝓝 s]
        fun z : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * ((z - c) ^ (k + 1))⁻¹ := by
      filter_upwards [(isOpen_ne (x := c)).mem_nhds hs] with z hz
      exact ih z hz
    rw [hev.deriv_eq]
    have hpow_d : HasDerivAt (fun z : ℂ => (z - c) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (s - c) ^ k) s := by
      simpa using ((hasDerivAt_id s).sub_const c).fun_pow (k + 1)
    have hpow_ne : (s - c) ^ (k + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
    have hinv_d : HasDerivAt (fun z : ℂ => ((z - c) ^ (k + 1))⁻¹)
        (-(((k + 1 : ℕ) : ℂ) * (s - c) ^ k) / ((s - c) ^ (k + 1)) ^ 2) s := hpow_d.fun_inv hpow_ne
    have hmul_d := hinv_d.const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
    rw [hmul_d.deriv]
    have hsc_ne : s - c ≠ 0 := sub_ne_zero.mpr hs
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp [hsc_ne]
    ring

/-- Exact `k`-th derivative of `z ↦ (z + c)⁻¹` at `s ≠ -c`. -/
private lemma iteratedDeriv_inv_add_const (k : ℕ) (c : ℂ) {s : ℂ} (hs : s + c ≠ 0) :
    iteratedDeriv k (fun z : ℂ => (z + c)⁻¹) s =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * ((s + c) ^ (k + 1))⁻¹ := by
  have hfun : (fun z : ℂ => (z + c)⁻¹) = fun z : ℂ => (z - (-c))⁻¹ := by
    funext z; rw [sub_neg_eq_add]
  rw [hfun, iteratedDeriv_inv_sub_const k (-c) s (by intro h; apply hs; linear_combination h)]
  rw [sub_neg_eq_add]

/-- Exact `k`-th derivative of `z ↦ (n : ℂ) ^ (-z)` for `n ≥ 1`. -/
private lemma iteratedDeriv_nat_cpow_neg (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ s : ℂ, iteratedDeriv k (fun z : ℂ => (n : ℂ) ^ (-z)) s =
      (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-s) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrew : (fun z : ℂ => (n : ℂ) ^ (-z)) =
      fun z : ℂ => Complex.exp (-(Real.log (n : ℝ) : ℂ) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
    congr 1; ring
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv k (fun z : ℂ => (n : ℂ) ^ (-z)) =
        fun z : ℂ => (-(Real.log (n : ℝ) : ℂ)) ^ k * Complex.exp (-(Real.log (n : ℝ) : ℂ) * z) := by
      funext z; rw [ih z, congrFun hrew z]
    rw [hfun]
    have hd : HasDerivAt (fun z : ℂ => Complex.exp (-(Real.log (n : ℝ) : ℂ) * z))
        ((-(Real.log (n : ℝ) : ℂ)) * Complex.exp (-(Real.log (n : ℝ) : ℂ) * s)) s := by
      have hlin : HasDerivAt (fun z : ℂ => -(Real.log (n : ℝ) : ℂ) * z) (-(Real.log (n : ℝ) : ℂ)) s := by
        simpa using (hasDerivAt_id s).const_mul (-(Real.log (n : ℝ) : ℂ))
      simpa [mul_comm] using hlin.cexp
    rw [(hd.const_mul _).deriv, ← congrFun hrew s, pow_succ]
    ring

/-- Elementary bound `(Real.log n)^m ≤ (1 / η)^m * n^(m * η)` for all `n ≥ 1`, `η > 0`, `m : ℕ`. -/
private lemma log_pow_le_rpow {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) (m : ℕ) :
    (Real.log (n : ℝ)) ^ m ≤ (1 / η) ^ m * (n : ℝ) ^ ((m : ℝ) * η) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 : Real.log (n : ℝ) ≤ (1 / η) * (n : ℝ) ^ η := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos η)
    rw [Real.log_rpow hn_pos] at h
    have h2 : η * Real.log (n : ℝ) ≤ (n : ℝ) ^ η := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / η)
    rwa [← mul_assoc, one_div_mul_cancel hη.ne', one_mul] at h3
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc (Real.log (n : ℝ)) ^ m
      ≤ ((1 / η) * (n : ℝ) ^ η) ^ m := pow_le_pow_left₀ hlog_nn h1 m
    _ = (1 / η) ^ m * ((n : ℝ) ^ η) ^ m := mul_pow _ _ _
    _ = (1 / η) ^ m * (n : ℝ) ^ ((m : ℝ) * η) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ η) m, ← Real.rpow_mul hn_pos.le, mul_comm η (m : ℝ)]

/-- Term-by-term `k`-th derivative of any bounded-coefficient von Mangoldt `L`-series on `Re(s) > 1`:
`iteratedDeriv k (LSeries (fun n => c n * Λ n)) s = ∑' n, if n = 0 then 0 else c n * Λ n * (-log n)^k * n^(-s)`. -/
private lemma iteratedDeriv_LSeries_vonMangoldt (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ) :
    ∀ s : ℂ, 1 < s.re →
      iteratedDeriv k (fun z : ℂ => LSeries (fun n => c n * (Λ n : ℂ)) z) s =
        ∑' n : ℕ, if n = 0 then (0 : ℂ) else
          c n * (Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-s) := by
  induction k with
  | zero =>
    intro s _
    rw [iteratedDeriv_zero]
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, pow_zero, mul_one]
      rw [div_eq_mul_inv, Complex.cpow_neg]
  | succ k ih =>
    intro s hs
    set δ : ℝ := (s.re - 1) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    set U : Set ℂ := Metric.ball s δ
    have hsU : s ∈ U := Metric.mem_ball_self hδ
    have hU_re : ∀ w ∈ U, 1 + δ < w.re := fun w hw => by
      have hdist : ‖w - s‖ < δ := by simpa [U, Metric.mem_ball, dist_eq_norm] using hw
      have hre : |w.re - s.re| < δ :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s)) hdist
      have h1 := (abs_lt.mp hre).1
      dsimp only [δ] at h1 ⊢; linarith
    let g : ℕ → ℂ → ℂ := fun n w => if n = 0 then 0 else
      c n * (Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-w)
    let g' : ℕ → ℂ → ℂ := fun n w => if n = 0 then 0 else
      c n * (Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ (k + 1) * (n : ℂ) ^ (-w)
    -- Dominate `g' n w` and `g n s` by a constant multiple of `Λ n / n^(1 + δ/2)`!
    set η : ℝ := δ / (2 * ((k + 2 : ℕ) : ℝ))
    have hη : 0 < η := by positivity
    have hbase_sum : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n / (n : ℝ) ^ (1 + δ / 2)) := by
      have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((1 + δ / 2 : ℝ) : ℂ))
        (by simp; linarith)).norm
      refine hL.congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [LSeries.term]
      · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hn, Complex.ofReal_re]
    set M_dom : ℝ := (1 / η) ^ (k + 1) + (1 / η) ^ k
    let u : ℕ → ℝ := fun n => M_dom * (if n = 0 then 0 else Λ n / (n : ℝ) ^ (1 + δ / 2))
    have hu_sum : Summable u := hbase_sum.mul_left M_dom
    have hbound_pow : ∀ (m : ℕ) (hm : m ≤ k + 1) (n : ℕ) (w : ℂ), w ∈ U → n ≠ 0 →
        ‖c n * (Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ m * (n : ℂ) ^ (-w)‖ ≤
          (1 / η) ^ m * (Λ n / (n : ℝ) ^ (1 + δ / 2)) := by
      intro m hm n w hw hn0
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_real, Real.norm_of_nonneg hlog_nn,
        Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re]
      have hcn1 : ‖c n‖ ≤ 1 := hc n
      have hw_re : 1 + δ < w.re := hU_re w hw
      have hlog_bd := log_pow_le_rpow hn1 hη m
      have hm_eta : (m : ℝ) * η ≤ δ / 2 := by
        dsimp only [η]
        have hm_le : (m : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ k + 2)
        have hpos2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
        calc (m : ℝ) * (δ / (2 * ((k + 2 : ℕ) : ℝ)))
            ≤ ((k + 2 : ℕ) : ℝ) * (δ / (2 * ((k + 2 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_right hm_le (by positivity)
          _ = δ / 2 := by field_simp [hpos2.ne']
      have hrpow_le : (n : ℝ) ^ ((m : ℝ) * η) * (n : ℝ) ^ (-w.re) ≤ (n : ℝ) ^ (-(1 + δ / 2)) := by
        rw [← Real.rpow_add hn_pos]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
      have hprod_le : (Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-w.re) ≤
          (1 / η) ^ m * (n : ℝ) ^ (-(1 + δ / 2)) := by
        calc (Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-w.re)
            ≤ ((1 / η) ^ m * (n : ℝ) ^ ((m : ℝ) * η)) * (n : ℝ) ^ (-w.re) :=
              mul_le_mul_of_nonneg_right hlog_bd (Real.rpow_nonneg hn_pos.le _)
          _ = (1 / η) ^ m * ((n : ℝ) ^ ((m : ℝ) * η) * (n : ℝ) ^ (-w.re)) := by ring
          _ ≤ (1 / η) ^ m * (n : ℝ) ^ (-(1 + δ / 2)) :=
              mul_le_mul_of_nonneg_left hrpow_le (by positivity)
      calc ‖c n‖ * Λ n * (Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-w.re)
          ≤ 1 * Λ n * ((Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-w.re)) := by
            rw [mul_assoc (‖c n‖ * Λ n)]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hcn1 ArithmeticFunction.vonMangoldt_nonneg
        _ = Λ n * ((Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-w.re)) := by ring
        _ ≤ Λ n * ((1 / η) ^ m * (n : ℝ) ^ (-(1 + δ / 2))) :=
            mul_le_mul_of_nonneg_left hprod_le ArithmeticFunction.vonMangoldt_nonneg
        _ = (1 / η) ^ m * (Λ n / (n : ℝ) ^ (1 + δ / 2)) := by
            rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv]; ring
    have hg'_bound : ∀ n : ℕ, ∀ w ∈ U, ‖g' n w‖ ≤ u n := fun n w hw => by
      dsimp only [g', u, M_dom]
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        have h1 := hbound_pow (k + 1) le_rfl n w hw hn0
        have hnn : 0 ≤ Λ n / (n : ℝ) ^ (1 + δ / 2) :=
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        exact h1.trans (mul_le_mul_of_nonneg_right (by linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 1 / η) k]) hnn)
    have hgs_sum : Summable (fun n : ℕ => g n s) := by
      refine Summable.of_norm_bounded hu_sum fun n => ?_
      dsimp only [g, u, M_dom]
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        have h1 := hbound_pow k (Nat.le_succ k) n s hsU hn0
        have hnn : 0 ≤ Λ n / (n : ℝ) ^ (1 + δ / 2) :=
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        exact h1.trans (mul_le_mul_of_nonneg_right
          (by linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 1 / η) (k + 1)]) hnn)
    have hderiv_g : ∀ n : ℕ, ∀ w ∈ U, HasDerivAt (g n) (g' n w) w := fun n w _ => by
      dsimp only [g, g']
      by_cases hn0 : n = 0
      · simp only [hn0, ↓reduceIte]; exact hasDerivAt_const w 0
      · simp only [hn0, ↓reduceIte]
        have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
        have hpow : HasDerivAt (fun z : ℂ => (n : ℂ) ^ (-z))
            ((-(Real.log (n : ℝ) : ℂ)) * (n : ℂ) ^ (-w)) w := by
          have hrew : (fun z : ℂ => (n : ℂ) ^ (-z)) =
              fun z : ℂ => Complex.exp (-(Real.log (n : ℝ) : ℂ) * z) := by
            funext z
            rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast,
              Complex.ofReal_log hn_pos.le]
            congr 1; ring
          rw [hrew, congrFun hrew w]
          have hlin : HasDerivAt (fun z : ℂ => -(Real.log (n : ℝ) : ℂ) * z)
              (-(Real.log (n : ℝ) : ℂ)) w := by
            simpa using (hasDerivAt_id w).const_mul (-(Real.log (n : ℝ) : ℂ))
          simpa [mul_comm] using hlin.cexp
        refine (hpow.const_mul (c n * (Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k)).congr_deriv ?_
        rw [pow_succ]; ring
    have htsum_d : HasDerivAt (fun w : ℂ => ∑' n : ℕ, g n w) (∑' n : ℕ, g' n s) s :=
      hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
        (convex_ball s δ).isPreconnected hderiv_g hg'_bound hsU hgs_sum hsU
    have hev : iteratedDeriv k (fun z : ℂ => LSeries (fun n => c n * (Λ n : ℂ)) z) =ᶠ[𝓝 s]
        fun w : ℂ => ∑' n : ℕ, g n w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hsU] with w hw
      exact ih w (by linarith [hU_re w hw])
    rw [iteratedDeriv_succ, hev.deriv_eq, htsum_d.deriv]

/-- Term-by-term `k`-th derivative (`k ≥ 1`) of the Hadamard zero partial-fraction series
`∑' n, (1 / (z - ρ n) + 1 / ρ n)` on `Re(s) > 1`. -/
private lemma iteratedDeriv_hadamard_zero_tsum {ρ : ℕ → ℂ}
    (hstrip : ∀ n : ℕ, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹)) (k : ℕ) (hk : 1 ≤ k) :
    ∀ s : ℂ, 1 < s.re →
      iteratedDeriv k (fun z : ℂ => ∑' n : ℕ, (1 / (z - ρ n) + 1 / ρ n)) s =
        (-1 : ℂ) ^ k * (k.factorial : ℂ) * ∑' n : ℕ, ((s - ρ n) ^ (k + 1))⁻¹ := by
  have hρ_ne : ∀ n : ℕ, ρ n ≠ 0 := fun n h0 => by
    have := (hstrip n).1; rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
  -- Uniform lower bound on `‖w - ρ n‖` for `w ∈ ball s ((s.re - 1) / 2)`:
  have hunif : ∀ (s : ℂ), 1 < s.re →
      ∃ C_s : ℝ, 0 < C_s ∧ ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball s ((s.re - 1) / 2) →
        ((s.re - 1) / 2) ≤ ‖w - ρ n‖ ∧ ‖(w - ρ n)⁻¹‖ ≤ C_s / ‖ρ n‖ := by
    intro s hs
    set δ : ℝ := (s.re - 1) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    set C_s : ℝ := max 2 (2 * (‖s‖ + δ) / δ)
    refine ⟨C_s, by positivity, fun n w hw => ?_⟩
    have hdist : ‖w - s‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw_re : 1 + δ < w.re := by
      have hre : |w.re - s.re| < δ :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s)) hdist
      have h1 := (abs_lt.mp hre).1
      dsimp only [δ] at h1 ⊢; linarith
    have hdiff_re : δ < (w - ρ n).re := by simp; linarith [(hstrip n).2]
    have hge_δ : δ ≤ ‖w - ρ n‖ :=
      hdiff_re.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    refine ⟨hge_δ, ?_⟩
    rw [norm_inv]
    have hρ_pos : 0 < ‖ρ n‖ := norm_pos_iff.mpr (hρ_ne n)
    have hwn : ‖w‖ ≤ ‖s‖ + δ := by
      calc ‖w‖ = ‖(w - s) + s‖ := by congr 1; ring
        _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
        _ ≤ ‖s‖ + δ := by linarith
    by_cases hbig : 2 * (‖s‖ + δ) ≤ ‖ρ n‖
    · have hge_half : ‖ρ n‖ / 2 ≤ ‖w - ρ n‖ := by
        have htri : ‖ρ n‖ ≤ ‖w‖ + ‖w - ρ n‖ := by
          have := norm_sub_le w (w - ρ n); rwa [sub_sub_cancel] at this
        linarith
      calc ‖w - ρ n‖⁻¹ ≤ (‖ρ n‖ / 2)⁻¹ := inv_anti₀ (by positivity) hge_half
        _ = 2 / ‖ρ n‖ := by rw [inv_div]
        _ ≤ C_s / ‖ρ n‖ := div_le_div_of_nonneg_right (le_max_left _ _) hρ_pos.le
    · push Not at hbig
      calc ‖w - ρ n‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hge_δ
        _ = (δ⁻¹ * ‖ρ n‖) / ‖ρ n‖ := by field_simp [hρ_pos.ne']
        _ ≤ (2 * (‖s‖ + δ) / δ) / ‖ρ n‖ := by
            refine div_le_div_of_nonneg_right ?_ hρ_pos.le
            rw [div_eq_mul_inv, mul_comm (2 * (‖s‖ + δ))]
            exact mul_le_mul_of_nonneg_left hbig.le (by positivity)
        _ ≤ C_s / ‖ρ n‖ := div_le_div_of_nonneg_right (le_max_right _ _) hρ_pos.le
  -- First prove `k = 1`, then induct on `k ≥ 1`!
  induction k, hk using Nat.le_induction with
  | base =>
    intro s hs
    rw [iteratedDeriv_one]
    set δ : ℝ := (s.re - 1) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    obtain ⟨C_s, hCs_pos, hCs⟩ := hunif s hs
    set U : Set ℂ := Metric.ball s δ
    have hsU : s ∈ U := Metric.mem_ball_self hδ
    let g : ℕ → ℂ → ℂ := fun n w => 1 / (w - ρ n) + 1 / ρ n
    let g' : ℕ → ℂ → ℂ := fun n w => -((w - ρ n) ^ 2)⁻¹
    let u : ℕ → ℝ := fun n => C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹
    have hu_sum : Summable u := hsum.mul_left (C_s ^ 2)
    have hderiv_g : ∀ n : ℕ, ∀ w ∈ U, HasDerivAt (g n) (g' n w) w := fun n w hw => by
      have hne : w - ρ n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ (hCs n w hw).1)
      have h1 : HasDerivAt (fun z : ℂ => (z - ρ n)⁻¹) (-((w - ρ n) ^ 2)⁻¹) w := by
        simpa [one_div, neg_div] using ((hasDerivAt_id w).sub_const (ρ n)).fun_inv hne
      simpa [g, g', one_div] using h1.add_const (1 / ρ n)
    have hg'_bd : ∀ n : ℕ, ∀ w ∈ U, ‖g' n w‖ ≤ u n := fun n w hw => by
      dsimp only [g', u]
      rw [norm_neg, norm_inv, norm_pow, ← inv_pow]
      have h1 := (hCs n w hw).2
      rw [norm_inv] at h1
      calc (‖w - ρ n‖⁻¹) ^ 2 ≤ (C_s / ‖ρ n‖) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
    have hgs_sum : Summable (fun n : ℕ => g n s) := by
      refine Summable.of_norm_bounded (hsum.mul_left (‖s‖ * C_s)) fun n => ?_
      have hne : s - ρ n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ (hCs n s hsU).1)
      have hcomb : g n s = s / ((s - ρ n) * ρ n) := by
        dsimp only [g]; field_simp [hne, hρ_ne n]; ring
      rw [hcomb, norm_div, norm_mul, div_eq_mul_inv, mul_inv]
      have h1 := (hCs n s hsU).2
      rw [norm_inv] at h1
      calc ‖s‖ * (‖s - ρ n‖⁻¹ * ‖ρ n‖⁻¹)
          ≤ ‖s‖ * ((C_s / ‖ρ n‖) * ‖ρ n‖⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) (norm_nonneg s)
        _ = ‖s‖ * C_s * (‖ρ n‖ ^ 2)⁻¹ := by rw [sq, mul_inv]; ring
    have htsum_d := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
      (convex_ball s δ).isPreconnected hderiv_g hg'_bd hsU hgs_sum hsU
    rw [htsum_d.deriv]
    simp only [g', tsum_neg, pow_one, Nat.factorial_one, Nat.cast_one, mul_one, neg_mul, one_mul]
  | succ k hk ih =>
    intro s hs
    set δ : ℝ := (s.re - 1) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    obtain ⟨C_s, hCs_pos, hCs⟩ := hunif s hs
    set U : Set ℂ := Metric.ball s δ
    have hsU : s ∈ U := Metric.mem_ball_self hδ
    have hU_re : ∀ w ∈ U, 1 < w.re := fun w hw => by
      have hdist : ‖w - s‖ < δ := by simpa [U, Metric.mem_ball, dist_eq_norm] using hw
      have hre : |w.re - s.re| < δ :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s)) hdist
      have h1 := (abs_lt.mp hre).1
      dsimp only [δ] at h1; linarith
    let g : ℕ → ℂ → ℂ := fun n w => ((w - ρ n) ^ (k + 1))⁻¹
    let g' : ℕ → ℂ → ℂ := fun n w => -(((k + 1 : ℕ) : ℂ) * ((w - ρ n) ^ (k + 2))⁻¹)
    set M_dom : ℝ := ((k + 1 : ℕ) : ℝ) * (δ⁻¹) ^ k * C_s ^ 2
    let u : ℕ → ℝ := fun n => M_dom * (‖ρ n‖ ^ 2)⁻¹
    have hu_sum : Summable u := hsum.mul_left M_dom
    have hderiv_g : ∀ n : ℕ, ∀ w ∈ U, HasDerivAt (g n) (g' n w) w := fun n w hw => by
      have hne : w - ρ n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ (hCs n w hw).1)
      have hpow_d : HasDerivAt (fun z : ℂ => (z - ρ n) ^ (k + 1))
          (((k + 1 : ℕ) : ℂ) * (w - ρ n) ^ k) w := by
        simpa using ((hasDerivAt_id w).sub_const (ρ n)).fun_pow (k + 1)
      refine (hpow_d.fun_inv (pow_ne_zero _ hne)).congr_deriv ?_
      dsimp only [g']; field_simp [hne]; ring
    have hg'_bd : ∀ n : ℕ, ∀ w ∈ U, ‖g' n w‖ ≤ u n := fun n w hw => by
      dsimp only [g', u, M_dom]
      rw [norm_neg, norm_mul, Complex.norm_natCast, norm_inv, norm_pow, ← inv_pow]
      have h1 : ‖w - ρ n‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (hCs n w hw).1
      have h2 : ‖w - ρ n‖⁻¹ ≤ C_s / ‖ρ n‖ := by simpa only [norm_inv] using (hCs n w hw).2
      have hsplit : (‖w - ρ n‖⁻¹) ^ (k + 2) = (‖w - ρ n‖⁻¹) ^ k * (‖w - ρ n‖⁻¹) ^ 2 := by
        rw [← pow_add]
      rw [hsplit]
      have hp1 : (‖w - ρ n‖⁻¹) ^ k ≤ (δ⁻¹) ^ k := pow_le_pow_left₀ (by positivity) h1 k
      have hp2 : (‖w - ρ n‖⁻¹) ^ 2 ≤ C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹ := by
        calc (‖w - ρ n‖⁻¹) ^ 2 ≤ (C_s / ‖ρ n‖) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ = C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      calc ((k + 1 : ℕ) : ℝ) * ((‖w - ρ n‖⁻¹) ^ k * (‖w - ρ n‖⁻¹) ^ 2)
          ≤ ((k + 1 : ℕ) : ℝ) * ((δ⁻¹) ^ k * (C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hp1 hp2 (by positivity) (by positivity)) (by positivity)
        _ = ((k + 1 : ℕ) : ℝ) * (δ⁻¹) ^ k * C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹ := by ring
    have hgs_sum : Summable (fun n : ℕ => g n s) := by
      refine Summable.of_norm_bounded (hsum.mul_left ((δ⁻¹) ^ (k - 1) * C_s ^ 2)) fun n => ?_
      dsimp only [g]
      rw [norm_inv, norm_pow, ← inv_pow]
      have h1 : ‖s - ρ n‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (hCs n s hsU).1
      have h2 : ‖s - ρ n‖⁻¹ ≤ C_s / ‖ρ n‖ := by simpa only [norm_inv] using (hCs n s hsU).2
      have hexp : k + 1 = (k - 1) + 2 := by omega
      rw [hexp, pow_add]
      calc (‖s - ρ n‖⁻¹) ^ (k - 1) * (‖s - ρ n‖⁻¹) ^ 2
          ≤ (δ⁻¹) ^ (k - 1) * (C_s / ‖ρ n‖) ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) h1 _) (pow_le_pow_left₀ (by positivity) h2 _)
              (by positivity) (by positivity)
        _ = (δ⁻¹) ^ (k - 1) * C_s ^ 2 * (‖ρ n‖ ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]; ring
    have htsum_d := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
      (convex_ball s δ).isPreconnected hderiv_g hg'_bd hsU hgs_sum hsU
    have hev : iteratedDeriv k (fun z : ℂ => ∑' n : ℕ, (1 / (z - ρ n) + 1 / ρ n)) =ᶠ[𝓝 s]
        fun w : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * ∑' n : ℕ, g n w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hsU] with w hw
      exact ih w (hU_re w hw)
    rw [iteratedDeriv_succ, hev.deriv_eq, (htsum_d.const_mul _).deriv]
    simp only [g', tsum_neg, tsum_mul_left, Nat.factorial_succ, pow_succ]
    push_cast; ring

/-- Term-by-term `k`-th derivative (`k ≥ 1`) of `Complex.digamma` on `Re(w) > 0`:
`iteratedDeriv k Complex.digamma w = (-1)^(k+1) * k! * ∑' n, ((w + n)^(k+1))⁻¹`. -/
private lemma iteratedDeriv_digamma_eq_tsum (k : ℕ) (hk : 1 ≤ k) :
    ∀ w : ℂ, 0 < w.re →
      iteratedDeriv k Complex.digamma w =
        (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, ((w + (n : ℂ)) ^ (k + 1))⁻¹ := by
  have hunif : ∀ (w : ℂ), 0 < w.re →
      ∃ c_w : ℝ, 0 < c_w ∧ ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball w (w.re / 2) →
        c_w * ((n + 1 : ℕ) : ℝ) ≤ ‖z + (n : ℂ)‖ := by
    intro w hw
    set c_w : ℝ := min (w.re / 2) (1 / 2)
    refine ⟨c_w, lt_min (by linarith) (by norm_num), fun n z hz => ?_⟩
    have hdist : ‖z - w‖ < w.re / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz_re : w.re / 2 < z.re := by
      have hre : |z.re - w.re| ≤ ‖z - w‖ := by simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
      linarith [(abs_le.mp hre).1]
    have hzn_re : c_w * ((n + 1 : ℕ) : ℝ) ≤ (z + (n : ℂ)).re := by
      have hre_eq : (z + (n : ℂ)).re = z.re + (n : ℝ) := by simp
      rw [hre_eq]
      have h1 : c_w ≤ w.re / 2 := min_le_left _ _
      have h2 : c_w ≤ 1 / 2 := min_le_right _ _
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact hzn_re.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hsum_sq : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
  induction k, hk using Nat.le_induction with
  | base =>
    intro w hw
    rw [iteratedDeriv_one]
    obtain ⟨c_w, hcw_pos, hcw⟩ := hunif w hw
    set δ : ℝ := w.re / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    set U : Set ℂ := Metric.ball w δ
    have hwU : w ∈ U := Metric.mem_ball_self hδ
    have hU_re : ∀ z ∈ U, 0 < z.re := fun z hz => by
      have hdist : ‖z - w‖ < δ := by simpa [U, Metric.mem_ball, dist_eq_norm] using hz
      have hre : |z.re - w.re| < δ :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)) hdist
      have h1 := (abs_lt.mp hre).1
      dsimp only [δ] at h1; linarith
    let g : ℕ → ℂ → ℂ := fun n z => (((n + 1 : ℕ) : ℂ))⁻¹ - (z + (n : ℂ))⁻¹
    let g' : ℕ → ℂ → ℂ := fun n z => ((z + (n : ℂ)) ^ 2)⁻¹
    let u : ℕ → ℝ := fun n => (c_w ^ 2)⁻¹ * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
    have hu_sum : Summable u := hsum_sq.mul_left (c_w ^ 2)⁻¹
    have hderiv_g : ∀ n : ℕ, ∀ z ∈ U, HasDerivAt (g n) (g' n z) z := fun n z hz => by
      have hne : z + (n : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hcw n z hz))
      have h1 : HasDerivAt (fun x : ℂ => (x + (n : ℂ))⁻¹) (-((z + (n : ℂ)) ^ 2)⁻¹) z := by
        simpa [one_div, neg_div] using ((hasDerivAt_id z).add_const (n : ℂ)).fun_inv hne
      simpa [g, g'] using (hasDerivAt_const z (((n + 1 : ℕ) : ℂ))⁻¹).fun_sub h1
    have hg'_bd : ∀ n : ℕ, ∀ z ∈ U, ‖g' n z‖ ≤ u n := fun n z hz => by
      dsimp only [g', u]
      rw [norm_inv, norm_pow, ← mul_inv, ← mul_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (hcw n z hz) 2)
    have htsum_d := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
      (convex_ball w δ).isPreconnected hderiv_g hg'_bd hwU
      (Stage7VonMangoldtExplicit.summable_digamma_term hw) hwU
    have hev : Complex.digamma =ᶠ[𝓝 w] fun z : ℂ => -(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, g n z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwU] with z hz
      exact Stage7VonMangoldtExplicit.digamma_eq_neg_eulerMascheroni_add_tsum (hU_re z hz)
    rw [hev.deriv_eq, (htsum_d.const_add _).deriv]
    simp [g']
  | succ k hk ih =>
    intro w hw
    obtain ⟨c_w, hcw_pos, hcw⟩ := hunif w hw
    set δ : ℝ := w.re / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    set U : Set ℂ := Metric.ball w δ
    have hwU : w ∈ U := Metric.mem_ball_self hδ
    have hU_re : ∀ z ∈ U, 0 < z.re := fun z hz => by
      have hdist : ‖z - w‖ < δ := by simpa [U, Metric.mem_ball, dist_eq_norm] using hz
      have hre : |z.re - w.re| < δ :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)) hdist
      have h1 := (abs_lt.mp hre).1
      dsimp only [δ] at h1; linarith
    let g : ℕ → ℂ → ℂ := fun n z => ((z + (n : ℂ)) ^ (k + 1))⁻¹
    let g' : ℕ → ℂ → ℂ := fun n z => -(((k + 1 : ℕ) : ℂ) * ((z + (n : ℂ)) ^ (k + 2))⁻¹)
    let u : ℕ → ℝ := fun n => ((k + 1 : ℕ) : ℝ) * (c_w ^ (k + 2))⁻¹ * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
    have hu_sum : Summable u := hsum_sq.mul_left (((k + 1 : ℕ) : ℝ) * (c_w ^ (k + 2))⁻¹)
    have hderiv_g : ∀ n : ℕ, ∀ z ∈ U, HasDerivAt (g n) (g' n z) z := fun n z hz => by
      have hne : z + (n : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hcw n z hz))
      have hpow_d : HasDerivAt (fun x : ℂ => (x + (n : ℂ)) ^ (k + 1))
          (((k + 1 : ℕ) : ℂ) * (z + (n : ℂ)) ^ k) z := by
        simpa using ((hasDerivAt_id z).add_const (n : ℂ)).fun_pow (k + 1)
      refine (hpow_d.fun_inv (pow_ne_zero _ hne)).congr_deriv ?_
      dsimp only [g']; field_simp [hne]; ring
    have hg'_bd : ∀ n : ℕ, ∀ z ∈ U, ‖g' n z‖ ≤ u n := fun n z hz => by
      dsimp only [g', u]
      rw [norm_neg, norm_mul, Complex.norm_natCast, norm_inv, norm_pow]
      have hpow_ge : c_w ^ (k + 2) * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ‖z + (n : ℂ)‖ ^ (k + 2) := by
        have h1 : (c_w * ((n + 1 : ℕ) : ℝ)) ^ (k + 2) ≤ ‖z + (n : ℂ)‖ ^ (k + 2) :=
          pow_le_pow_left₀ (by positivity) (hcw n z hz) (k + 2)
        have h2 : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ (k + 2) :=
          pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (by omega)
        rw [mul_pow] at h1
        exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h1
      have hinv := inv_anti₀ (by positivity) hpow_ge
      rw [mul_inv] at hinv
      calc ((k + 1 : ℕ) : ℝ) * (‖z + (n : ℂ)‖ ^ (k + 2))⁻¹
          ≤ ((k + 1 : ℕ) : ℝ) * ((c_w ^ (k + 2))⁻¹ * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = ((k + 1 : ℕ) : ℝ) * (c_w ^ (k + 2))⁻¹ * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by ring
    have hgw_sum : Summable (fun n : ℕ => g n w) := by
      refine Summable.of_norm_bounded (hsum_sq.mul_left (c_w ^ (k + 1))⁻¹) fun n => ?_
      dsimp only [g]; rw [norm_inv, norm_pow]
      have hpow_ge : c_w ^ (k + 1) * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ‖w + (n : ℂ)‖ ^ (k + 1) := by
        have h1 : (c_w * ((n + 1 : ℕ) : ℝ)) ^ (k + 1) ≤ ‖w + (n : ℂ)‖ ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) (hcw n w hwU) (k + 1)
        have h2 : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ (k + 1) :=
          pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (by omega)
        rw [mul_pow] at h1
        exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h1
      have hinv := inv_anti₀ (by positivity) hpow_ge
      rwa [mul_inv] at hinv
    have htsum_d := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
      (convex_ball w δ).isPreconnected hderiv_g hg'_bd hwU hgw_sum hwU
    have hev : iteratedDeriv k Complex.digamma =ᶠ[𝓝 w]
        fun z : ℂ => (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, g n z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwU] with z hz
      exact ih z (hU_re z hz)
    rw [iteratedDeriv_succ, hev.deriv_eq, (htsum_d.const_mul _).deriv]
    simp only [g', tsum_neg, tsum_mul_left, Nat.factorial_succ, pow_succ]
    push_cast; ring

/-- Analyticity of `iteratedDeriv m f` at `z` whenever `f` is analytic at `z`. -/
private lemma analyticAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (m : ℕ) :
    AnalyticAt ℂ (iteratedDeriv m f) z := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- Analyticity of `Complex.digamma` on `{w : ℂ | 0 < w.re}`. -/
private lemma analyticAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ Complex.digamma w := by
  have hopen0 : IsOpen {x : ℂ | 0 < x.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hne_neg : ∀ x : ℂ, 0 < x.re → ∀ n : ℕ, x ≠ -(n : ℂ) := fun x hx n h => by
    have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hGam_diff : DifferentiableOn ℂ Complex.Gamma {x : ℂ | 0 < x.re} :=
    fun x hx => (Complex.differentiableAt_Gamma x (hne_neg x hx)).differentiableWithinAt
  have hGam : AnalyticAt ℂ Complex.Gamma w := hGam_diff.analyticAt (hopen0.mem_nhds hw)
  have hEq : Complex.digamma = fun x => deriv Complex.Gamma x / Complex.Gamma x := by
    funext x; rw [Complex.digamma_def, logDeriv_apply]
  rw [hEq]
  exact hGam.deriv.div hGam (Complex.Gamma_ne_zero (hne_neg w hw))

/-- Analyticity of the Hadamard zero partial-fraction series `∑' j, (1/(z - ρ j) + 1/ρ j)`
on `{s : ℂ | 1 < s.re}`. -/
private lemma analyticAt_hadamard_zero_tsum {ρ : ℕ → ℂ}
    (hstrip : ∀ j : ℕ, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j : ℕ => (‖ρ j‖ ^ 2)⁻¹)) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∑' j : ℕ, (1 / (z - ρ j) + 1 / ρ j)) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hρ_ne : ∀ j : ℕ, ρ j ≠ 0 := fun j h0 => by
    have := (hstrip j).1; rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => ∑' j : ℕ, (1 / (z - ρ j) + 1 / ρ j)) {z : ℂ | 1 < z.re} := by
    intro z hz
    change 1 < z.re at hz
    set δ : ℝ := (z.re - 1) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    set C_z : ℝ := max 2 (2 * (‖z‖ + δ) / δ)
    have hinv_bd : ∀ j : ℕ, ∀ w ∈ Metric.ball z δ,
        δ ≤ ‖w - ρ j‖ ∧ ‖w - ρ j‖⁻¹ ≤ C_z / ‖ρ j‖ := by
      intro j w hw
      have hdist : ‖w - z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hre : |w.re - z.re| < δ :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)) hdist
      have hw_re : 1 + δ < w.re := by
        have := (abs_lt.mp hre).1; dsimp only [δ] at this ⊢; linarith
      have hge_δ : δ ≤ ‖w - ρ j‖ := by
        have h1 : δ < (w - ρ j).re := by simp; linarith [(hstrip j).2]
        exact h1.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
      refine ⟨hge_δ, ?_⟩
      have hρ_pos : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ_ne j)
      have hwn : ‖w‖ ≤ ‖z‖ + δ := by
        calc ‖w‖ = ‖(w - z) + z‖ := by congr 1; ring
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + δ := by linarith
      by_cases hbig : 2 * (‖z‖ + δ) ≤ ‖ρ j‖
      · have hge_h : ‖ρ j‖ / 2 ≤ ‖w - ρ j‖ := by
          have htri := norm_sub_le w (w - ρ j); rw [sub_sub_cancel] at htri; linarith
        calc ‖w - ρ j‖⁻¹ ≤ (‖ρ j‖ / 2)⁻¹ := inv_anti₀ (by positivity) hge_h
          _ = 2 / ‖ρ j‖ := inv_div _ _
          _ ≤ C_z / ‖ρ j‖ := div_le_div_of_nonneg_right (le_max_left _ _) hρ_pos.le
      · push Not at hbig
        calc ‖w - ρ j‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hge_δ
          _ = (δ⁻¹ * ‖ρ j‖) / ‖ρ j‖ := by field_simp [hρ_pos.ne']
          _ ≤ (2 * (‖z‖ + δ) / δ) / ‖ρ j‖ := by
              refine div_le_div_of_nonneg_right ?_ hρ_pos.le
              rw [div_eq_mul_inv, mul_comm (2 * (‖z‖ + δ))]
              exact mul_le_mul_of_nonneg_left hbig.le (by positivity)
          _ ≤ C_z / ‖ρ j‖ := div_le_div_of_nonneg_right (le_max_right _ _) hρ_pos.le
    have hbd : ∀ j : ℕ, ∀ w ∈ Metric.ball z δ, ‖-((w - ρ j) ^ 2)⁻¹‖ ≤ C_z ^ 2 * (‖ρ j‖ ^ 2)⁻¹ := fun j w hw => by
      rw [norm_neg, norm_inv, norm_pow, ← inv_pow]
      calc (‖w - ρ j‖⁻¹) ^ 2 ≤ (C_z / ‖ρ j‖) ^ 2 := pow_le_pow_left₀ (by positivity) (hinv_bd j w hw).2 2
        _ = C_z ^ 2 * (‖ρ j‖ ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
    have hsumm_z : Summable (fun j : ℕ => 1 / (z - ρ j) + 1 / ρ j) := by
      refine Summable.of_norm_bounded (hsum.mul_left (‖z‖ * C_z)) fun j => ?_
      have hne : z - ρ j ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ (hinv_bd j z (Metric.mem_ball_self hδ)).1)
      have hcomb : 1 / (z - ρ j) + 1 / ρ j = z / ((z - ρ j) * ρ j) := by field_simp [hne, hρ_ne j]; ring
      rw [hcomb, norm_div, norm_mul, div_eq_mul_inv, mul_inv]
      calc ‖z‖ * (‖z - ρ j‖⁻¹ * ‖ρ j‖⁻¹)
          ≤ ‖z‖ * ((C_z / ‖ρ j‖) * ‖ρ j‖⁻¹) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hinv_bd j z (Metric.mem_ball_self hδ)).2 (by positivity))
              (norm_nonneg z)
        _ = ‖z‖ * C_z * (‖ρ j‖ ^ 2)⁻¹ := by rw [sq, mul_inv]; ring
    have hd := hasDerivAt_tsum_of_isPreconnected (hsum.mul_left (C_z ^ 2)) Metric.isOpen_ball
      (convex_ball z δ).isPreconnected
      (fun j w hw => by
        have hne : w - ρ j ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ (hinv_bd j w hw).1)
        have h1 : HasDerivAt (fun x : ℂ => (x - ρ j)⁻¹) (-((w - ρ j) ^ 2)⁻¹) w := by
          simpa [one_div, neg_div] using ((hasDerivAt_id w).sub_const (ρ j)).fun_inv hne
        have h2 : HasDerivAt (fun x : ℂ => (x - ρ j)⁻¹ + 1 / ρ j) (-((w - ρ j) ^ 2)⁻¹) w :=
          h1.add_const (1 / ρ j)
        simpa only [one_div] using h2)
      hbd (Metric.mem_ball_self hδ) (by simpa only [one_div] using hsumm_z) (Metric.mem_ball_self hδ)
    simpa only [one_div] using hd.differentiableAt.differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hs)

/-- Uniform norm bound on the scaled `k`-th derivative of `(1 / 2) * Complex.digamma ((z + a) / 2)`
for `0 ≤ a.re`, `1 < s.re`, and `k ≥ 1`: bounded by `2`! -/
private lemma norm_scaled_iteratedDeriv_digamma_half_le (a : ℂ) (ha : 0 ≤ a.re)
    {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    ‖((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
        iteratedDeriv k (fun z : ℂ => (1 / 2 : ℂ) * Complex.digamma ((z + a) / 2)) s‖ ≤ 2 := by
  have hchain : ∀ m : ℕ, ∀ z : ℂ, 1 < z.re →
      iteratedDeriv m (fun x : ℂ => Complex.digamma ((x + a) / 2)) z =
        ((1 / 2 : ℂ) ^ m) * iteratedDeriv m Complex.digamma ((z + a) / 2) := by
    intro m
    induction m with
    | zero => intro z _; simp
    | succ m ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {x : ℂ | 1 < x.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
      have hev : iteratedDeriv m (fun x : ℂ => Complex.digamma ((x + a) / 2)) =ᶠ[𝓝 z]
          fun x : ℂ => ((1 / 2 : ℂ) ^ m) * iteratedDeriv m Complex.digamma ((x + a) / 2) := by
        filter_upwards [hopen.mem_nhds hz] with x hx using ih x hx
      rw [hev.deriv_eq]
      have hdiff_dig : DifferentiableAt ℂ (iteratedDeriv m Complex.digamma) ((z + a) / 2) :=
        (analyticAt_iteratedDeriv (analyticAt_digamma_of_re_pos (by simp; linarith)) m).differentiableAt
      have hlin : HasDerivAt (fun x : ℂ => (x + a) / 2) (1 / 2 : ℂ) z := by
        simpa using ((hasDerivAt_id z).add_const a).div_const (2 : ℂ)
      have hcomp : HasDerivAt (fun x : ℂ => ((1 / 2 : ℂ) ^ m) * iteratedDeriv m Complex.digamma ((x + a) / 2))
          (((1 / 2 : ℂ) ^ m) * (deriv (iteratedDeriv m Complex.digamma) ((z + a) / 2) * (1 / 2 : ℂ))) z :=
        (hdiff_dig.hasDerivAt.comp z hlin).const_mul ((1 / 2 : ℂ) ^ m)
      rw [hcomp.deriv, ← iteratedDeriv_succ, pow_succ]
      ring
  rw [iteratedDeriv_const_mul_field, hchain k s hs,
    iteratedDeriv_digamma_eq_tsum k hk ((s + a) / 2) (by simp; linarith)]
  have hfacC : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  set Tsum : ℂ := ∑' n : ℕ, (((s + a) / 2 + (n : ℂ)) ^ (k + 1))⁻¹
  have hneg1 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ (k + 1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  have hsimp : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
      ((1 / 2 : ℂ) * ((1 / 2 : ℂ) ^ k * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * Tsum))) =
      -((1 / 2 : ℂ) ^ (k + 1) * Tsum) := by
    calc ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
          ((1 / 2 : ℂ) * ((1 / 2 : ℂ) ^ k * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * Tsum)))
        = (((-1 : ℂ) ^ k * (-1 : ℂ) ^ (k + 1)) * ((k.factorial : ℂ) / (k.factorial : ℂ))) *
            (((1 / 2 : ℂ) * (1 / 2 : ℂ) ^ k) * Tsum) := by ring
      _ = ((-1) * 1) * ((1 / 2 : ℂ) ^ (k + 1) * Tsum) := by
            rw [hneg1, div_self hfacC, pow_succ']
      _ = -((1 / 2 : ℂ) ^ (k + 1) * Tsum) := by ring
  rw [hsimp, norm_neg, ← tsum_mul_left]
  have hsum_sq : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
  have hterm : ∀ n : ℕ,
      ‖(1 / 2 : ℂ) ^ (k + 1) * (((s + a) / 2 + (n : ℂ)) ^ (k + 1))⁻¹‖ ≤ (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro n
    rw [norm_mul, norm_pow, norm_inv, norm_pow, one_div, norm_inv, Complex.norm_ofNat,
      ← inv_pow, ← mul_pow, ← mul_inv]
    have hre_ge : ((n + 1 : ℕ) : ℝ) ≤ 2 * ‖(s + a) / 2 + (n : ℂ)‖ := by
      have h1 : ((s + a) / 2 + (n : ℂ)).re ≤ ‖(s + a) / 2 + (n : ℂ)‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      have hre : ((s + a) / 2 + (n : ℂ)).re = (s.re + a.re) / 2 + (n : ℝ) := by simp
      rw [hre] at h1
      push_cast; linarith
    have hpow_ge : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * ‖(s + a) / 2 + (n : ℂ)‖) ^ (k + 1) := by
      calc ((n + 1 : ℕ) : ℝ) ^ 2
          ≤ ((n + 1 : ℕ) : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (by omega)
        _ ≤ (2 * ‖(s + a) / 2 + (n : ℂ)‖) ^ (k + 1) := pow_le_pow_left₀ (by positivity) hre_ge (k + 1)
    rw [inv_pow]
    exact inv_anti₀ (by positivity) hpow_ge
  exact (norm_tsum_le_tsum_norm (Summable.of_norm_bounded hsum_sq hterm).norm).trans
    ((Summable.tsum_le_tsum hterm (Summable.of_norm_bounded hsum_sq hterm).norm hsum_sq).trans
      tsum_inv_add_one_sq_le_two)

/-- **Master High-Derivative Identity for Primitive `DirichletCharacter.LFunction`** (`0` assumptions!):
for every primitive `ψ ≠ 1` mod `f`, `k ≥ 1`, and `s : ℂ` with `1 < s.re`:
`‖(∑' n, if n = 0 then 0 else ψ n * Λ n * ((log n)^k / k!) * n^(-s)) + ∑' j, ((s - ρ j)^(k+1))⁻¹‖ ≤ 2`. -/
theorem master_highDeriv_prim {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    ‖(∑' n : ℕ, if n = 0 then (0 : ℂ) else
        ψ (n : ZMod f) * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s)) +
      ∑' j : ℕ, ((s - Stage8HadamardLFunction.completedLZeroSeq hprim hψ j) ^ (k + 1))⁻¹‖ ≤ 2 := by
  classical
  have hopen : IsOpen {z : ℂ | 1 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hfacC : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hLHS : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (Stage3ZeroFreeRegion.negLogDerivL ψ) s =
      ∑' n : ℕ, if n = 0 then (0 : ℂ) else
        ψ (n : ZMod f) * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s) := by
    have hev : Stage3ZeroFreeRegion.negLogDerivL ψ =ᶠ[𝓝 s]
        fun z => LSeries (fun n => ψ (n : ZMod f) * (Λ n : ℂ)) z := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries ψ hz
    rw [hev.iteratedDeriv_eq k, iteratedDeriv_LSeries_vonMangoldt (fun n => ψ (n : ZMod f))
      (fun n => ψ.norm_le_one _) k s hs, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      have hneg : (-1 : ℂ) ^ k * (-(Real.log (n : ℝ) : ℂ)) ^ k = (Real.log (n : ℝ) : ℂ) ^ k := by
        rw [← mul_pow]; simp
      calc ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
            (ψ (n : ZMod f) * (Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-s))
          = ψ (n : ZMod f) * (Λ n : ℂ) * (((-1 : ℂ) ^ k * (-(Real.log (n : ℝ) : ℂ)) ^ k) /
              (k.factorial : ℂ)) * (n : ℂ) ^ (-s) := by ring
        _ = ψ (n : ZMod f) * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) *
              (n : ℂ) ^ (-s) := by rw [hneg]
  let Z : ℂ → ℂ := fun z => ∑' j : ℕ, (1 / (z - Stage8HadamardLFunction.completedLZeroSeq hprim hψ j) +
      1 / Stage8HadamardLFunction.completedLZeroSeq hprim hψ j)
  let a_par : ℂ := if ψ.Even then 0 else 1
  have ha_re : 0 ≤ a_par.re := by dsimp only [a_par]; split_ifs <;> simp
  let G : ℂ → ℂ := fun z => (1 / 2 : ℂ) * Complex.digamma ((z + a_par) / 2)
  have hev_pf : Stage3ZeroFreeRegion.negLogDerivL ψ =ᶠ[𝓝 s]
      fun z => (-Stage8HadamardLFunction.symmetricCompletedLHadamardB ψ +
        ((Real.log (f : ℝ) / 2 : ℝ) : ℂ) - ((Real.log Real.pi / 2 : ℝ) : ℂ)) + (-Z z + G z) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hpf := Stage8HadamardLFunction.negLogDerivL_prim_eq_hadamard_partialFraction hprim hψ hz
    rcases ψ.even_or_odd with he | ho
    · have hγ := Stage8HadamardLFunction.logDeriv_gammaFactor_even he (by linarith : 0 < z.re)
      have ha0 : a_par = 0 := if_pos he
      rw [hpf, hγ]; dsimp only [Z, G]; rw [ha0, add_zero]; ring
    · have hγ := Stage8HadamardLFunction.logDeriv_gammaFactor_odd ho (by linarith : 0 < z.re)
      have hne : ¬ ψ.Even := fun he => by
        have h1 : ψ (-1) = 1 := he
        have h2 : ψ (-1) = -1 := ho
        rw [h1] at h2; norm_num at h2
      have ha1 : a_par = 1 := if_neg hne
      rw [hpf, hγ]; dsimp only [Z, G]; rw [ha1]; ring
  have hZ_an : AnalyticAt ℂ Z s :=
    analyticAt_hadamard_zero_tsum (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
      (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprim hψ) hs
  have hG_an : AnalyticAt ℂ G s := by
    have hdig : AnalyticAt ℂ Complex.digamma ((fun z : ℂ => (z + a_par) / 2) s) :=
      analyticAt_digamma_of_re_pos (by simp; linarith)
    have hlin : AnalyticAt ℂ (fun z : ℂ => (z + a_par) / 2) s :=
      (analyticAt_id.add analyticAt_const).div analyticAt_const two_ne_zero
    have hcomp : AnalyticAt ℂ (Complex.digamma ∘ fun z : ℂ => (z + a_par) / 2) s :=
      AnalyticAt.comp (g := Complex.digamma) (f := fun z : ℂ => (z + a_par) / 2) hdig hlin
    exact analyticAt_const.mul hcomp
  have hRHS : iteratedDeriv k (Stage3ZeroFreeRegion.negLogDerivL ψ) s =
      -iteratedDeriv k Z s + iteratedDeriv k G s := by
    rw [hev_pf.iteratedDeriv_eq k, iteratedDeriv_const_add (by omega : 0 < k)]
    change iteratedDeriv k (-Z + G) s = -iteratedDeriv k Z s + iteratedDeriv k G s
    rw [iteratedDeriv_add (hZ_an.neg.contDiffAt.of_le le_top) (hG_an.contDiffAt.of_le le_top),
      iteratedDeriv_neg]
  rw [← hLHS, hRHS,
    iteratedDeriv_hadamard_zero_tsum (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
      (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprim hψ) k hk s hs]
  set Zsum : ℂ := ∑' j : ℕ, ((s - Stage8HadamardLFunction.completedLZeroSeq hprim hψ j) ^ (k + 1))⁻¹
  have hsq1 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  have hcancel : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
      (-((-1 : ℂ) ^ k * (k.factorial : ℂ) * Zsum) + iteratedDeriv k G s) + Zsum =
      ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s := by
    calc ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
          (-((-1 : ℂ) ^ k * (k.factorial : ℂ) * Zsum) + iteratedDeriv k G s) + Zsum
        = (1 - ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((k.factorial : ℂ) / (k.factorial : ℂ))) * Zsum +
            ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s := by ring
      _ = ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s := by
            rw [hsq1, div_self hfacC]; ring
  rw [hcancel]
  exact norm_scaled_iteratedDeriv_digamma_half_le a_par ha_re hk hs

/-- **Master High-Derivative Identity for Mathlib's `riemannZeta`** (`0` assumptions!):
for every `k ≥ 1` and `s : ℂ` with `1 < s.re`:
`‖(∑' n, if n = 0 then 0 else Λ n * ((log n)^k / k!) * n^(-s)) - ((s - 1)^(k+1))⁻¹ + ∑' j, ((s - xiZeroSeq j)^(k+1))⁻¹‖ ≤ 3`. -/
theorem master_highDeriv_zeta {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    ‖(∑' n : ℕ, if n = 0 then (0 : ℂ) else
        (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s)) -
      ((s - 1) ^ (k + 1))⁻¹ +
      ∑' j : ℕ, ((s - Stage7HadamardXiProduct.xiZeroSeq j) ^ (k + 1))⁻¹‖ ≤ 3 := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hfacC : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hLHS : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k Stage3ZeroFreeRegion.negLogDerivZeta s =
      ∑' n : ℕ, if n = 0 then (0 : ℂ) else
        (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s) := by
    have hev : Stage3ZeroFreeRegion.negLogDerivZeta =ᶠ[𝓝 s]
        fun z => LSeries (fun n => (1 : ℂ) * (Λ n : ℂ)) z := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      simpa only [one_mul] using Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hz
    rw [hev.iteratedDeriv_eq k, iteratedDeriv_LSeries_vonMangoldt (fun _ => (1 : ℂ))
      (fun _ => by simp) k s hs, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte, one_mul]
      have hneg : (-1 : ℂ) ^ k * (-(Real.log (n : ℝ) : ℂ)) ^ k = (Real.log (n : ℝ) : ℂ) ^ k := by
        rw [← mul_pow]; simp
      calc ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
            ((Λ n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-s))
          = (Λ n : ℂ) * (((-1 : ℂ) ^ k * (-(Real.log (n : ℝ) : ℂ)) ^ k) / (k.factorial : ℂ)) *
              (n : ℂ) ^ (-s) := by ring
        _ = (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s) := by rw [hneg]
  let Z : ℂ → ℂ := fun z => ∑' j : ℕ, (1 / (z - Stage7HadamardXiProduct.xiZeroSeq j) +
      1 / Stage7HadamardXiProduct.xiZeroSeq j)
  let G : ℂ → ℂ := fun z => (1 / 2 : ℂ) * Complex.digamma ((z + 0) / 2)
  have hev_pf : Stage3ZeroFreeRegion.negLogDerivZeta =ᶠ[𝓝 s]
      fun z => (-Stage7HadamardXiProduct.xiHadamardB - ((Real.log Real.pi / 2 : ℝ) : ℂ)) +
        (((z - 1)⁻¹ + (-Z z)) + ((z - 0)⁻¹ + G z)) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [Stage8HadamardLFunction.negLogDerivZeta_eq_hadamard_partialFraction hz]
    dsimp only [Z, G]; simp only [add_zero, sub_zero, one_div]; ring
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have h1_an : AnalyticAt ℂ (fun z : ℂ => (z - 1)⁻¹) s :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs1)
  have h0_an : AnalyticAt ℂ (fun z : ℂ => (z - 0)⁻¹) s :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs0)
  have hZ_an : AnalyticAt ℂ Z s :=
    analyticAt_hadamard_zero_tsum Stage7HadamardXiProduct.xiZeroSeq_strip
      Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq hs
  have hG_an : AnalyticAt ℂ G s := by
    have hdig : AnalyticAt ℂ Complex.digamma ((fun z : ℂ => (z + 0) / 2) s) :=
      analyticAt_digamma_of_re_pos (by simp; linarith)
    have hlin : AnalyticAt ℂ (fun z : ℂ => (z + 0) / 2) s :=
      (analyticAt_id.add analyticAt_const).div analyticAt_const two_ne_zero
    have hcomp : AnalyticAt ℂ (Complex.digamma ∘ fun z : ℂ => (z + 0) / 2) s :=
      AnalyticAt.comp (g := Complex.digamma) (f := fun z : ℂ => (z + 0) / 2) hdig hlin
    exact analyticAt_const.mul hcomp
  have hRHS : iteratedDeriv k Stage3ZeroFreeRegion.negLogDerivZeta s =
      (iteratedDeriv k (fun z : ℂ => (z - 1)⁻¹) s - iteratedDeriv k Z s) +
        (iteratedDeriv k (fun z : ℂ => (z - 0)⁻¹) s + iteratedDeriv k G s) := by
    rw [hev_pf.iteratedDeriv_eq k, iteratedDeriv_const_add (by omega : 0 < k)]
    change iteratedDeriv k (((fun z : ℂ => (z - 1)⁻¹) + (-Z)) + ((fun z : ℂ => (z - 0)⁻¹) + G)) s = _
    rw [iteratedDeriv_add ((h1_an.add hZ_an.neg).contDiffAt.of_le le_top)
        ((h0_an.add hG_an).contDiffAt.of_le le_top),
      iteratedDeriv_add (h1_an.contDiffAt.of_le le_top) (hZ_an.neg.contDiffAt.of_le le_top),
      iteratedDeriv_add (h0_an.contDiffAt.of_le le_top) (hG_an.contDiffAt.of_le le_top),
      iteratedDeriv_neg]
    ring
  rw [← hLHS, hRHS,
    iteratedDeriv_inv_sub_const k 1 s hs1,
    iteratedDeriv_inv_sub_const k 0 s hs0,
    iteratedDeriv_hadamard_zero_tsum Stage7HadamardXiProduct.xiZeroSeq_strip
      Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq k hk s hs]
  set Zsum : ℂ := ∑' j : ℕ, ((s - Stage7HadamardXiProduct.xiZeroSeq j) ^ (k + 1))⁻¹
  set P1 : ℂ := ((s - 1) ^ (k + 1))⁻¹
  set P0 : ℂ := (s ^ (k + 1))⁻¹
  have hsq1 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  have hcancel : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
      (((-1 : ℂ) ^ k * (k.factorial : ℂ) * P1 - (-1 : ℂ) ^ k * (k.factorial : ℂ) * Zsum) +
        ((-1 : ℂ) ^ k * (k.factorial : ℂ) * ((s - 0) ^ (k + 1))⁻¹ + iteratedDeriv k G s)) -
      P1 + Zsum = P0 + ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s := by
    simp only [sub_zero]
    change ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
      (((-1 : ℂ) ^ k * (k.factorial : ℂ) * P1 - (-1 : ℂ) ^ k * (k.factorial : ℂ) * Zsum) +
        ((-1 : ℂ) ^ k * (k.factorial : ℂ) * P0 + iteratedDeriv k G s)) - P1 + Zsum =
      P0 + ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s
    calc _ = (((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((k.factorial : ℂ) / (k.factorial : ℂ)) - 1) * (P1 - Zsum) +
              (((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((k.factorial : ℂ) / (k.factorial : ℂ))) * P0 +
              ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s := by ring
      _ = P0 + ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s := by
            rw [hsq1, div_self hfacC]; ring
  rw [hcancel]
  have hs_norm : 1 ≤ ‖s‖ := hs.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have h1s : ‖P0‖ ≤ 1 := by
    dsimp only [P0]; rw [norm_inv, norm_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hs_norm)
  have h2G : ‖((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k G s‖ ≤ 2 :=
    norm_scaled_iteratedDeriv_digamma_half_le 0 (by simp) hk hs
  exact (norm_add_le _ _).trans (by linarith)

/-! ### Section 3b (cont.): Shared Constants & Local Multiplicity Zero-Count Lemmas -/

/-- Universal Hadamard partial-fraction constant extracted from
`Stage8HadamardLFunction.re_negLogDeriv_le_sub_finset_unconditional`. -/
private noncomputable def hadamardConst : ℝ :=
  Classical.choose Stage8HadamardLFunction.re_negLogDeriv_le_sub_finset_unconditional

private lemma hadamardConst_spec :
    0 < hadamardConst ∧
    (∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      (Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
        hadamardConst * Real.log (|t| + 2) + (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re -
          ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq n)).re) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1),
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
        (Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
          hadamardConst * Real.log ((q : ℝ) * (|t| + 2)) -
            ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) -
              Stage8HadamardLFunction.completedLZeroSeq hprim hχ n)).re) :=
  Classical.choose_spec Stage8HadamardLFunction.re_negLogDeriv_le_sub_finset_unconditional

private noncomputable def C_Z_const : ℝ := 2 * hadamardConst + 4

private lemma one_le_C_Z_const : 1 ≤ C_Z_const := by
  dsimp only [C_Z_const]; linarith [hadamardConst_spec.1]

/-- Real-axis bound `Re(-ζ'/ζ(1 + d)) ≤ hadamardConst * log 2 + 1 / d` for `0 < d ≤ 1`. -/
private lemma re_negLogDerivZeta_real_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (Stage3ZeroFreeRegion.negLogDerivZeta ((1 + d : ℝ) : ℂ)).re ≤
      hadamardConst * Real.log 2 + 1 / d := by
  have h1 := hadamardConst_spec.2.1 (1 + d) 0 (by linarith) (by linarith) ∅
  simp only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero, zero_add, Finset.sum_empty,
    sub_zero] at h1
  have hpole : (1 / (((1 + d : ℝ) : ℂ) - 1)).re = 1 / d := by
    have hsub : ((1 + d : ℝ) : ℂ) - 1 = (d : ℂ) := by push_cast; ring
    rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hpole] at h1
  exact h1

/-- Uniform upper bound `‖LSeries (c * Λ) (1 + d + I * γ₀)‖ ≤ hadamardConst * log 2 + 1 / d`
for every `c : ℕ → ℂ` with `‖c n‖ ≤ 1` and `0 < d ≤ 1`. -/
private lemma norm_LSeries_vonMangoldt_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (γ₀ : ℝ) :
    ‖LSeries (fun n => c n * (Λ n : ℂ)) (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ))‖ ≤
      hadamardConst * Real.log 2 + 1 / d := by
  set s : ℂ := ((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)
  have hs_re : s.re = 1 + d := by simp [s]
  have hsum_r : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + d : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
  have hsum_c : LSeriesSummable (fun n => c n * (Λ n : ℂ)) s := by
    refine Summable.of_norm_bounded hsum_r.norm fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, norm_mul,
        Complex.norm_natCast_cpow_of_pos hn, hs_re, Complex.ofReal_re]
      exact div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (Λ n : ℂ))) (by positivity)
  have hre_z : (Stage3ZeroFreeRegion.negLogDerivZeta ((1 + d : ℝ) : ℂ)).re =
      ∑' n : ℕ, ‖LSeries.term (fun m => (Λ m : ℂ)) ((1 + d : ℝ) : ℂ) n‖ := by
    rw [Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries (by simp; linarith)]
    unfold LSeries
    rw [show (∑' n, LSeries.term (fun m => (Λ m : ℂ)) ((1 + d : ℝ) : ℂ) n).re =
        ∑' n, (LSeries.term (fun m => (Λ m : ℂ)) ((1 + d : ℝ) : ℂ) n).re from
      Complex.reCLM.map_tsum hsum_r]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos hn, Complex.ofReal_re]
      have hcp : ((n : ℂ) ^ ((1 + d : ℝ) : ℂ)) = (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcp, ← Complex.ofReal_div, Complex.ofReal_re]
  refine le_trans ?_ (re_negLogDerivZeta_real_le hd hd1)
  rw [hre_z]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum_c.norm).trans (Summable.tsum_le_tsum (fun n => ?_) hsum_c.norm hsum_r.norm)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, norm_mul,
      Complex.norm_natCast_cpow_of_pos hn, hs_re, Complex.ofReal_re]
    exact div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (Λ n : ℂ))) (by positivity)

/-- Real part of `1 / (σ + i t - ρ)` equals `(σ - ρ.re) / ‖σ + i t - ρ‖² ≥ 0`. -/
private lemma re_one_div_sub_eq {ρ : ℂ} {σ t : ℝ} (hσ : 1 < σ) (hρ1 : ρ.re < 1) :
    (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ)).re = (σ - ρ.re) / ‖((σ : ℂ) + I * (t : ℂ)) - ρ‖ ^ 2 ∧
    0 ≤ (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ)).re := by
  set z : ℂ := ((σ : ℂ) + I * (t : ℂ)) - ρ
  have hz_re : z.re = σ - ρ.re := by simp [z]
  have h1 : (1 / z).re = z.re / ‖z‖ ^ 2 := by rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [h1, hz_re]
  exact ⟨rfl, div_nonneg (by linarith) (sq_nonneg _)⟩

/-- Finite-sum bound on `∑ j ∈ F, Re(1 / (1 + d + i γ₀ - ρ j))` for `ζ`. -/
private lemma sum_re_inv_sub_xiZero_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (γ₀ : ℝ) (F : Finset ℕ) :
    ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j)).re ≤
      C_Z_const * (Real.log (|γ₀| + 2) + 1 / d) := by
  have h1 := hadamardConst_spec.2.1 (1 + d) γ₀ (by linarith) (by linarith) F
  have h2 := norm_LSeries_vonMangoldt_le (fun _ => (1 : ℂ)) (fun _ => by simp) hd hd1 γ₀
  have h3 : Stage3ZeroFreeRegion.negLogDerivZeta (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) =
      LSeries (fun n => (1 : ℂ) * (Λ n : ℂ)) (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) := by
    simpa only [one_mul] using Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries (by simp; linarith)
  rw [← h3] at h2
  have hneg : -(Stage3ZeroFreeRegion.negLogDerivZeta (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ))).re ≤
      hadamardConst * Real.log 2 + 1 / d :=
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h2
  have hpole : (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - 1)).re ≤ 1 / d := by
    have hsub : (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - 1 = (d : ℂ) + I * (γ₀ : ℂ) := by push_cast; ring
    rw [hsub, one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    have hre : ((d : ℂ) + I * (γ₀ : ℂ)).re = d := by simp
    have hnorm : d ≤ ‖(d : ℂ) + I * (γ₀ : ℂ)‖ :=
      (le_abs_self d).trans (by simpa [hre] using Complex.abs_re_le_norm ((d : ℂ) + I * (γ₀ : ℂ)))
    rw [hre]
    calc d / ‖(d : ℂ) + I * (γ₀ : ℂ)‖ ^ 2 ≤ d / d ^ 2 :=
          div_le_div_of_nonneg_left hd.le (sq_pos_of_pos hd) (pow_le_pow_left₀ hd.le hnorm 2)
      _ = 1 / d := by field_simp [hd.ne']
  have hlog2 : Real.log 2 ≤ Real.log (|γ₀| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ₀])
  have hlog_nn : 0 ≤ Real.log (|γ₀| + 2) := Real.log_nonneg (by linarith [abs_nonneg γ₀])
  dsimp only [C_Z_const]
  nlinarith [hadamardConst_spec.1, div_nonneg zero_le_one hd.le]

/-- Finite-sum bound on `∑ j ∈ F, Re(1 / (1 + d + i γ₀ - ρ j))` for primitive `χ ≠ 1`. -/
private lemma sum_re_inv_sub_LZero_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (γ₀ : ℝ) (F : Finset ℕ) :
    ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) -
        Stage8HadamardLFunction.completedLZeroSeq hprim hχ j)).re ≤
      C_Z_const * (Real.log ((q : ℝ) * (|γ₀| + 2)) + 1 / d) := by
  have h1 := hadamardConst_spec.2.2 q χ hprim hχ (1 + d) γ₀ (by linarith) (by linarith) F
  have h2 := norm_LSeries_vonMangoldt_le (fun n => χ (n : ZMod q)) (fun n => χ.norm_le_one _) hd hd1 γ₀
  have h3 := Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ
    (s := ((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) (by simp; linarith)
  rw [← h3] at h2
  have hneg : -(Stage3ZeroFreeRegion.negLogDerivL χ (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ))).re ≤
      hadamardConst * Real.log 2 + 1 / d :=
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h2
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|γ₀| + 2)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg γ₀])
  have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (|γ₀| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg γ₀])
  dsimp only [C_Z_const]
  nlinarith [hadamardConst_spec.1, div_nonneg zero_le_one hd.le]

/-- General global `r² / ‖1 + r + i γ₀ - ρ j‖²` sum bound from a finite-sum bound on `Re(1/(s - ρ j))`. -/
private lemma tsum_r_sq_div_norm_sq_le {ρ : ℕ → ℂ} (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    {r : ℝ} (hr : 0 < r) (γ₀ B : ℝ)
    (hB : ∀ F : Finset ℕ, ∑ j ∈ F, (1 / ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re ≤ B) :
    Summable (fun j : ℕ => r ^ 2 / ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ^ 2) ∧
    ∑' j : ℕ, r ^ 2 / ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ^ 2 ≤ r * B := by
  have hsumm_re : Summable (fun j : ℕ => (1 / ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re) :=
    summable_of_sum_le (fun j => (re_one_div_sub_eq (by linarith : 1 < 1 + r) (hstrip j).2).2) hB
  have hterm : ∀ j : ℕ,
      r ^ 2 / ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ^ 2 ≤
        r * (1 / ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re := fun j => by
    rw [(re_one_div_sub_eq (by linarith : 1 < 1 + r) (hstrip j).2).1, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [(hstrip j).2]
  have hsumm_sq : Summable (fun j : ℕ => r ^ 2 / ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hterm (hsumm_re.mul_left r)
  refine ⟨hsumm_sq, ?_⟩
  calc ∑' j : ℕ, r ^ 2 / ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ^ 2
      ≤ ∑' j : ℕ, r * (1 / ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re :=
        Summable.tsum_le_tsum hterm hsumm_sq (hsumm_re.mul_left r)
    _ = r * ∑' j : ℕ, (1 / ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re := tsum_mul_left
    _ ≤ r * B := mul_le_mul_of_nonneg_left (hsumm_re.tsum_le_of_sum_le hB) hr.le

/-- General local-ball multiplicity zero count (`0 < r ≤ d ≤ 1`). -/
private lemma local_ball_card_le {ρ : ℕ → ℂ} (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    {r d : ℝ} (hr : 0 < r) (hrd : r ≤ d) (γ₀ B : ℝ)
    (hB : ∀ F : Finset ℕ, ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re ≤ B)
    (F : Finset ℕ) (hF : ∀ j ∈ F, ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ < d) :
    (F.card : ℝ) ≤ 4 * d * B := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hge : ∀ j ∈ F, 1 / (4 * d) ≤ (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re := fun j hj => by
    rw [(re_one_div_sub_eq (by linarith : 1 < 1 + d) (hstrip j).2).1]
    have hnorm_le : ‖(((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ≤ 2 * d := by
      have hrew : (((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j =
          ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j) + ((d - r : ℝ) : ℂ) := by push_cast; ring
      rw [hrew]
      calc ‖((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j) + ((d - r : ℝ) : ℂ)‖
          ≤ ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ + ‖((d - r : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ d + (d - r) := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith [hF j hj]
        _ ≤ 2 * d := by linarith
    have hpos_n : 0 < ‖(((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ := by
      have h1 := (le_abs_self _).trans (Complex.abs_re_le_norm ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j))
      have hre : ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j).re = 1 + d - (ρ j).re := by simp
      rw [hre] at h1; linarith [(hstrip j).2]
    calc 1 / (4 * d) = d / (2 * d) ^ 2 := by field_simp [hd.ne']; ring
      _ ≤ (1 + d - (ρ j).re) / ‖(((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j‖ ^ 2 :=
          div_le_div₀ (by linarith [(hstrip j).2]) (by linarith [(hstrip j).2])
            (sq_pos_of_pos hpos_n) (pow_le_pow_left₀ hpos_n.le hnorm_le 2)
  have hsum_ge : (F.card : ℝ) * (1 / (4 * d)) ≤ B := by
    calc (F.card : ℝ) * (1 / (4 * d)) = ∑ _j ∈ F, (1 / (4 * d)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re := Finset.sum_le_sum hge
      _ ≤ B := hB F
  have hmul := mul_le_mul_of_nonneg_left hsum_ge (by positivity : (0 : ℝ) ≤ 4 * d)
  have hlhs : 4 * d * ((F.card : ℝ) * (1 / (4 * d))) = (F.card : ℝ) := by field_simp [hd.ne']
  linarith

/-- General multiplicity-counted cumulative height bound (`T ≥ 1`). -/
private lemma height_card_le_of_re_bound {ρ : ℕ → ℂ} (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    {q : ℝ} (hq1 : 1 ≤ q) {T : ℝ} (hT : 1 ≤ T)
    (hB : ∀ (t : ℝ) (G : Finset ℕ),
      ∑ j ∈ G, (1 / ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j)).re ≤ C_Z_const * (Real.log (q * (|t| + 2)) + 1))
    (F : Finset ℕ) (hF : ∀ j ∈ F, |(ρ j).im| ≤ T) :
    (F.card : ℝ) ≤ 180 * C_Z_const * T * Real.log (q * (T + 2)) := by
  classical
  have hunit : ∀ (t : ℝ) (G : Finset ℕ), (∀ j ∈ G, |(ρ j).im - t| ≤ 1) →
      (G.card : ℝ) ≤ 15 * C_Z_const * Real.log (q * (|t| + 2)) := by
    intro t G hG
    have hge : ∀ j ∈ G, (1 / 5 : ℝ) ≤ (1 / ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j)).re := fun j hj => by
      rw [(re_one_div_sub_eq (by norm_num : (1 : ℝ) < 1 + 1) (hstrip j).2).1]
      have hns : ‖(((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j‖ ^ 2 ≤ 5 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        have hre : ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j).re = 2 - (ρ j).re := by simp; ring
        have him : ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j).im = t - (ρ j).im := by simp
        rw [hre, him]
        have h1 : (2 - (ρ j).re) ^ 2 ≤ 4 := by nlinarith [(hstrip j).1, (hstrip j).2]
        have h2 : (t - (ρ j).im) ^ 2 ≤ 1 := by
          rw [← sq_abs, abs_sub_comm]; nlinarith [hG j hj, abs_nonneg ((ρ j).im - t)]
        nlinarith
      have hpos_n : 0 < ‖(((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j‖ := by
        have h1 := (le_abs_self _).trans (Complex.abs_re_le_norm ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j))
        have hre : ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j).re = 2 - (ρ j).re := by simp; ring
        rw [hre] at h1; linarith [(hstrip j).2]
      exact div_le_div₀ (by linarith [(hstrip j).2]) (by linarith [(hstrip j).2])
        (sq_pos_of_pos hpos_n) hns
    have hsum_ge : (G.card : ℝ) * (1 / 5) ≤ C_Z_const * (Real.log (q * (|t| + 2)) + 1) := by
      calc (G.card : ℝ) * (1 / 5) = ∑ _j ∈ G, (1 / 5 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ G, (1 / ((((1 + 1 : ℝ) : ℂ) + I * (t : ℂ)) - ρ j)).re := Finset.sum_le_sum hge
        _ ≤ C_Z_const * (Real.log (q * (|t| + 2)) + 1) := hB t G
    have hlog_ge : 1 / 2 ≤ Real.log (q * (|t| + 2)) :=
      (show (1 / 2 : ℝ) < Real.log 2 by linarith [Real.log_two_gt_d9]).le.trans
        (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t]))
    nlinarith [one_le_C_Z_const]
  set N : ℕ := ⌈T⌉₊
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hN_ge : T ≤ (N : ℝ) := Nat.le_ceil T
  have hN_le : (N : ℝ) ≤ 2 * T := by linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ T by linarith)]
  set I_int : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hcover : F ⊆ I_int.biUnion (fun k => F.filter fun j => |(ρ j).im - (k : ℝ)| ≤ 1) := by
    intro j hj
    rw [Finset.mem_biUnion]
    set k : ℤ := round (ρ j).im
    have hk_half : |(ρ j).im - (k : ℝ)| ≤ 1 / 2 := abs_sub_round (ρ j).im
    have hdiff := abs_le.mp hk_half
    have him := abs_le.mp (hF j hj)
    have hk_mem : k ∈ I_int := by
      rw [Finset.mem_Icc]
      constructor
      · have hlt : ((-(N : ℤ) - 1 : ℤ) : ℝ) < (k : ℝ) := by push_cast; linarith
        have hltZ : -(N : ℤ) - 1 < k := Int.cast_lt.mp hlt; omega
      · have hlt : (k : ℝ) < (((N : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
        have hltZ : k < (N : ℤ) + 1 := Int.cast_lt.mp hlt; omega
    exact ⟨k, hk_mem, Finset.mem_filter.mpr ⟨hj, hk_half.trans (by norm_num)⟩⟩
  have hcard_le : (F.card : ℝ) ≤ ∑ k ∈ I_int, ((F.filter fun j => |(ρ j).im - (k : ℝ)| ≤ 1).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hterm : ∀ k ∈ I_int,
      ((F.filter fun j => |(ρ j).im - (k : ℝ)| ≤ 1).card : ℝ) ≤ 30 * C_Z_const * Real.log (q * (T + 2)) := by
    intro k hk
    have h1 := hunit (k : ℝ) (F.filter fun j => |(ρ j).im - (k : ℝ)| ≤ 1)
      fun j hj => (Finset.mem_filter.mp hj).2
    have hk_abs : |(k : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]; rcases Finset.mem_Icc.mp hk with ⟨hlo, hhi⟩
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    have hlog_le : Real.log (q * (|(k : ℝ)| + 2)) ≤ 2 * Real.log (q * (T + 2)) := by
      have harg : q * (|(k : ℝ)| + 2) ≤ (q * (T + 2)) ^ 2 := by
        have hstep : |(k : ℝ)| + 2 ≤ 2 * (T + 2) := by linarith
        have hqT : 2 ≤ q * (T + 2) := by nlinarith
        nlinarith
      calc Real.log (q * (|(k : ℝ)| + 2))
          ≤ Real.log ((q * (T + 2)) ^ 2) := Real.log_le_log (by positivity) harg
        _ = 2 * Real.log (q * (T + 2)) := by rw [Real.log_pow]; norm_num
    nlinarith [one_le_C_Z_const]
  have hI_card : (I_int.card : ℝ) ≤ 6 * T := by
    have hcard_eq : I_int.card = 2 * N + 1 := by dsimp only [I_int]; rw [Int.card_Icc]; omega
    rw [hcard_eq]; push_cast
    have h1N : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
    linarith
  have hlog_nn : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
  have hCZ_nn : 0 ≤ 30 * C_Z_const * Real.log (q * (T + 2)) :=
    mul_nonneg (by linarith [one_le_C_Z_const]) hlog_nn
  calc (F.card : ℝ)
      ≤ ∑ _k ∈ I_int, (30 * C_Z_const * Real.log (q * (T + 2))) := hcard_le.trans (Finset.sum_le_sum hterm)
    _ = (I_int.card : ℝ) * (30 * C_Z_const * Real.log (q * (T + 2))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (6 * T) * (30 * C_Z_const * Real.log (q * (T + 2))) :=
        mul_le_mul_of_nonneg_right hI_card hCZ_nn
    _ = 180 * C_Z_const * T * Real.log (q * (T + 2)) := by ring

/-! ### Section 3c: Gallagher's High-Derivative Prime Zero Detector (`0` Assumptions!) -/

/-- Gallagher's Poisson-like high-derivative weight:
`gallagherWeight k r n = (Λ n / n) * r * ((r * log n)^k / k!) * n^(-r)`. -/
private noncomputable def gallagherWeight (k : ℕ) (r : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (Λ n / (n : ℝ)) * r * ((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * (n : ℝ) ^ (-r)

private lemma gallagherWeight_nonneg (k : ℕ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 ≤ gallagherWeight k r n := by
  dsimp only [gallagherWeight]
  split_ifs with hn0
  · exact le_rfl
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hL_nn : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    positivity

private lemma gallagherWeight_le (k : ℕ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    gallagherWeight k r n ≤ if n = 0 then 0 else r * (Λ n / (n : ℝ)) := by
  dsimp only [gallagherWeight]
  split_ifs with hn0
  · exact le_rfl
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hpois : ((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * (n : ℝ) ^ (-r) ≤ 1 := by
      have h1 := Real.pow_div_factorial_le_exp (r * Real.log (n : ℝ)) (by positivity) k
      have h2 : (n : ℝ) ^ (-r) = Real.exp (-(r * Real.log (n : ℝ))) := by
        rw [Real.rpow_def_of_pos hn_pos]; congr 1; ring
      rw [h2]
      calc ((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * Real.exp (-(r * Real.log (n : ℝ)))
          ≤ Real.exp (r * Real.log (n : ℝ)) * Real.exp (-(r * Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hL_nn : 0 ≤ Λ n / (n : ℝ) := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn_pos.le
    calc (Λ n / (n : ℝ)) * r * ((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * (n : ℝ) ^ (-r)
        = (r * (Λ n / (n : ℝ))) * (((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * (n : ℝ) ^ (-r)) := by ring
      _ ≤ (r * (Λ n / (n : ℝ))) * 1 := mul_le_mul_of_nonneg_left hpois (by positivity)
      _ = r * (Λ n / (n : ℝ)) := mul_one _

/-- Algebraic rewrite connecting `r^(k+1)` times the Dirichlet `k`-th derivative term with `gallagherWeight`. -/
private lemma r_pow_mul_dirichlet_term_eq (k : ℕ) {r : ℝ} (_hr : 0 < r) (γ₀ : ℝ)
    (c : ℕ → ℂ) (n : ℕ) :
    ((r : ℂ) ^ (k + 1)) * (if n = 0 then (0 : ℂ) else
      c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) *
        (n : ℂ) ^ (-(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)))) =
      (gallagherWeight k r n : ℂ) * c n * (n : ℂ) ^ (-(I * (γ₀ : ℂ))) := by
  by_cases hn0 : n = 0
  · simp [hn0, gallagherWeight]
  · simp only [hn0, ↓reduceIte, gallagherWeight]
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hcpow_split : (n : ℂ) ^ (-(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ))) =
        (((n : ℝ) : ℂ)⁻¹ * (((n : ℝ) ^ (-r) : ℝ) : ℂ)) * (n : ℂ) ^ (-(I * (γ₀ : ℂ))) := by
      have hexp : -(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) = (-1 : ℂ) + ((-r : ℝ) : ℂ) + (-(I * (γ₀ : ℂ))) := by
        push_cast; ring
      rw [hexp, Complex.cpow_add _ _ hnC, Complex.cpow_add _ _ hnC,
        Complex.cpow_neg_one, ← Complex.ofReal_natCast, Complex.ofReal_cpow hn_pos.le]
    rw [hcpow_split]
    push_cast
    rw [mul_pow, pow_succ]
    ring

/-- Sum of `r * Λ n / n^(1 + r)` over all `n` is bounded by `hadamardConst + 1`. -/
private lemma tsum_r_mul_vonMangoldt_div_rpow_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) ∧
    ∑' n : ℕ, (if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) ≤ hadamardConst + 1 := by
  have hsum_r : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + r : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
  have hsumm : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n / (n : ℝ) ^ (1 + r)) := by
    refine hsum_r.norm.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos hn, Complex.ofReal_re]
  have hsumm' : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) := by
    refine (hsumm.mul_left r).congr fun n => ?_
    split_ifs <;> ring
  refine ⟨hsumm', ?_⟩
  have hre : (Stage3ZeroFreeRegion.negLogDerivZeta ((1 + r : ℝ) : ℂ)).re =
      ∑' n : ℕ, (if n = 0 then (0 : ℝ) else Λ n / (n : ℝ) ^ (1 + r)) := by
    rw [Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries (by simp; linarith)]
    unfold LSeries
    rw [show (∑' n, LSeries.term (fun m => (Λ m : ℂ)) ((1 + r : ℝ) : ℂ) n).re =
        ∑' n, (LSeries.term (fun m => (Λ m : ℂ)) ((1 + r : ℝ) : ℂ) n).re from
      Complex.reCLM.map_tsum hsum_r]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte]
      have hcp : ((n : ℂ) ^ ((1 + r : ℝ) : ℂ)) = (((n : ℝ) ^ (1 + r) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcp, ← Complex.ofReal_div, Complex.ofReal_re]
  have heq : (∑' n : ℕ, if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) =
      r * ∑' n : ℕ, (if n = 0 then (0 : ℝ) else Λ n / (n : ℝ) ^ (1 + r)) := by
    rw [← tsum_mul_left]; refine tsum_congr fun n => ?_; split_ifs <;> ring
  rw [heq, ← hre]
  have hbd := re_negLogDerivZeta_real_le hr hr1
  have hlog2_lt1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  calc r * (Stage3ZeroFreeRegion.negLogDerivZeta ((1 + r : ℝ) : ℂ)).re
      ≤ r * (hadamardConst * Real.log 2 + 1 / r) := mul_le_mul_of_nonneg_left hbd hr.le
    _ = r * hadamardConst * Real.log 2 + 1 := by field_simp [hr.ne']
    _ ≤ hadamardConst + 1 := by
        have h1 : r * hadamardConst * Real.log 2 ≤ 1 * hadamardConst * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hr1 hadamardConst_spec.1.le) hlog2_lt1
            (Real.log_nonneg (by norm_num)) (by linarith [hadamardConst_spec.1])
        linarith

/-- **Lower Truncation Tail Bound**:
for `k ≥ 1`, `0 < r ≤ 1`, and `(N₁ : ℝ) ≤ Real.exp (Real.exp (-10) * k / r)`:
`∑ n ∈ Finset.Icc 1 N₁, gallagherWeight k r n ≤ (hadamardConst + 1) * Real.exp (-9 * k)`. -/
private lemma gallagher_lower_tail_le {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {N₁ : ℕ} (hN₁ : (N₁ : ℝ) ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r)) :
    ∑ n ∈ Finset.Icc 1 N₁, gallagherWeight k r n ≤ (hadamardConst + 1) * Real.exp (-9 * (k : ℝ)) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N₁,
      gallagherWeight k r n ≤ Real.exp (-9 * (k : ℝ)) * (if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) := by
    intro n hn
    obtain ⟨hn1, hnN₁⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hlog_le : r * Real.log (n : ℝ) ≤ Real.exp (-10) * (k : ℝ) := by
      have h1 : (n : ℝ) ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r) :=
        (Nat.cast_le.mpr hnN₁).trans hN₁
      have h2 := Real.log_le_log hn_pos h1
      rw [Real.log_exp] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 hr.le
      rwa [mul_div_cancel₀ _ hr.ne'] at h3
    have hstirl := div_exp_one_pow_le_factorial k
    have hfrac_le : (r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) ≤ Real.exp (-9 * (k : ℝ)) := by
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr k.factorial_pos
      calc (r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)
          ≤ (Real.exp (-10) * (k : ℝ)) ^ k / ((k : ℝ) / Real.exp 1) ^ k :=
            div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hlog_le k) (by positivity) hstirl
        _ = (Real.exp (-10) * Real.exp 1) ^ k := by
            rw [div_pow, mul_pow, mul_pow]
            field_simp [(pow_pos hk_pos k).ne']
        _ = (Real.exp (-9)) ^ k := by rw [← Real.exp_add]; norm_num
        _ = Real.exp (-9 * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    have hrpow : (n : ℝ) ^ (1 + r) = (n : ℝ) * (n : ℝ) ^ r := by
      rw [Real.rpow_add hn_pos, Real.rpow_one]
    have hrew : (Λ n / (n : ℝ)) * r * (n : ℝ) ^ (-r) = r * (Λ n / (n : ℝ) ^ (1 + r)) := by
      rw [hrpow, Real.rpow_neg hn_pos.le]; field_simp [hn_pos.ne', (Real.rpow_pos_of_pos hn_pos r).ne']
    dsimp only [gallagherWeight]
    simp only [hn0, ↓reduceIte]
    calc (Λ n / (n : ℝ)) * r * ((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * (n : ℝ) ^ (-r)
        = ((r * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) * ((Λ n / (n : ℝ)) * r * (n : ℝ) ^ (-r)) := by ring
      _ ≤ Real.exp (-9 * (k : ℝ)) * (r * (Λ n / (n : ℝ) ^ (1 + r))) := by
          rw [hrew]
          exact mul_le_mul_of_nonneg_right hfrac_le (by
            have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity)
  obtain ⟨hsumm, htsum_le⟩ := tsum_r_mul_vonMangoldt_div_rpow_le hr hr1
  calc ∑ n ∈ Finset.Icc 1 N₁, gallagherWeight k r n
      ≤ ∑ n ∈ Finset.Icc 1 N₁,
          Real.exp (-9 * (k : ℝ)) * (if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) :=
        Finset.sum_le_sum hterm
    _ = Real.exp (-9 * (k : ℝ)) * ∑ n ∈ Finset.Icc 1 N₁,
          (if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-9 * (k : ℝ)) * ∑' n : ℕ, (if n = 0 then (0 : ℝ) else r * (Λ n / (n : ℝ) ^ (1 + r))) := by
        refine mul_le_mul_of_nonneg_left (hsumm.sum_le_tsum _ fun n _ => ?_) (Real.exp_pos _).le
        split_ifs
        · exact le_rfl
        · have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
    _ ≤ Real.exp (-9 * (k : ℝ)) * (hadamardConst + 1) :=
        mul_le_mul_of_nonneg_left htsum_le (Real.exp_pos _).le
    _ = (hadamardConst + 1) * Real.exp (-9 * (k : ℝ)) := mul_comm _ _

/-- **Upper Truncation Tail Bound**:
for `k ≥ 1`, `0 < r ≤ 1`, and `Real.exp (30 * k / r) - 1 ≤ N₂`:
`∑' n, (if N₂ < n then gallagherWeight k r n else 0) ≤ 2 * (hadamardConst + 1) * Real.exp (-6 * k)`. -/
private lemma gallagher_upper_tail_le {k : ℕ} (_hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {N₂ : ℕ} (hN₂ : Real.exp (30 * (k : ℝ) / r) - 1 ≤ (N₂ : ℝ)) :
    Summable (fun n : ℕ => if N₂ < n then gallagherWeight k r n else 0) ∧
    ∑' n : ℕ, (if N₂ < n then gallagherWeight k r n else 0) ≤
      2 * (hadamardConst + 1) * Real.exp (-6 * (k : ℝ)) := by
  have h4_le : (4 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
    have h1 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
    have hhalf : (13 / 8 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by norm_num at h1; linarith
    have h3 : (13 / 8 : ℝ) ^ 3 ≤ (Real.exp (1 / 2 : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hhalf 3
    have hexp3 : (Real.exp (1 / 2 : ℝ)) ^ 3 = Real.exp (3 / 2 : ℝ) := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    rw [hexp3] at h3
    linarith [show (4 : ℝ) ≤ (13 / 8 : ℝ) ^ 3 by norm_num]
  obtain ⟨hsumm_half, htsum_half⟩ := tsum_r_mul_vonMangoldt_div_rpow_le (r := r / 2) (by linarith) (by linarith)
  have hterm : ∀ n : ℕ,
      (if N₂ < n then gallagherWeight k r n else 0) ≤
        (2 * Real.exp (-6 * (k : ℝ))) * (if n = 0 then (0 : ℝ) else (r / 2) * (Λ n / (n : ℝ) ^ (1 + r / 2))) := by
    intro n
    by_cases hn : N₂ < n
    · have hn0 : n ≠ 0 := by omega
      have hn1 : 1 ≤ n := by omega
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      have hn_ge_exp : Real.exp (30 * (k : ℝ) / r) ≤ (n : ℝ) := by
        have h1 : (N₂ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hu_ge : 30 * (k : ℝ) ≤ r * Real.log (n : ℝ) := by
        have h1 := Real.log_le_log (Real.exp_pos _) hn_ge_exp
        rw [Real.log_exp] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 hr.le
        rwa [mul_div_cancel₀ _ hr.ne'] at h2
      set u : ℝ := r * Real.log (n : ℝ)
      have hu_nn : 0 ≤ u := by positivity
      have hchernoff : (u ^ k / (k.factorial : ℝ)) * Real.exp (-u / 2) ≤ Real.exp (-6 * (k : ℝ)) := by
        have h1 : (u / 4) ^ k / (k.factorial : ℝ) ≤ Real.exp (u / 4) :=
          Real.pow_div_factorial_le_exp (u / 4) (by positivity) k
        have h2 : (u ^ k / (k.factorial : ℝ)) * Real.exp (-u / 2) =
            (4 : ℝ) ^ k * (((u / 4) ^ k / (k.factorial : ℝ)) * Real.exp (-u / 4)) * Real.exp (-u / 4) := by
          have hexp_half : Real.exp (-u / 2) = Real.exp (-u / 4) * Real.exp (-u / 4) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp_half, div_pow]
          have h4ne : (4 : ℝ) ^ k ≠ 0 := by positivity
          field_simp [h4ne]
        rw [h2]
        have h3 : ((u / 4) ^ k / (k.factorial : ℝ)) * Real.exp (-u / 4) ≤ 1 := by
          calc ((u / 4) ^ k / (k.factorial : ℝ)) * Real.exp (-u / 4)
              ≤ Real.exp (u / 4) * Real.exp (-u / 4) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
            _ = 1 := by rw [← Real.exp_add, show u / 4 + -u / 4 = 0 by ring, Real.exp_zero]
        have h4k : (4 : ℝ) ^ k ≤ Real.exp ((3 / 2 : ℝ) * (k : ℝ)) := by
          calc (4 : ℝ) ^ k ≤ (Real.exp (3 / 2 : ℝ)) ^ k := pow_le_pow_left₀ (by norm_num) h4_le k
            _ = Real.exp ((k : ℝ) * (3 / 2 : ℝ)) := (Real.exp_nat_mul _ k).symm
            _ = Real.exp ((3 / 2 : ℝ) * (k : ℝ)) := by congr 1; ring
        have hexp_u : Real.exp (-u / 4) ≤ Real.exp (-(15 / 2 : ℝ) * (k : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
        calc (4 : ℝ) ^ k * (((u / 4) ^ k / (k.factorial : ℝ)) * Real.exp (-u / 4)) * Real.exp (-u / 4)
            ≤ (4 : ℝ) ^ k * 1 * Real.exp (-(15 / 2 : ℝ) * (k : ℝ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) hexp_u (Real.exp_pos _).le (by positivity)
          _ ≤ Real.exp ((3 / 2 : ℝ) * (k : ℝ)) * Real.exp (-(15 / 2 : ℝ) * (k : ℝ)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_right h4k (Real.exp_pos _).le
          _ = Real.exp (-6 * (k : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      have hrpow_split : (n : ℝ) ^ (-r) = (n : ℝ) ^ (-(r / 2)) * Real.exp (-u / 2) := by
        rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hn_pos, ← Real.exp_add]
        congr 1; dsimp only [u]; ring
      have hden_eq : (Λ n / (n : ℝ)) * r * (n : ℝ) ^ (-(r / 2)) =
          2 * ((r / 2) * (Λ n / (n : ℝ) ^ (1 + r / 2))) := by
        rw [Real.rpow_add hn_pos, Real.rpow_one, Real.rpow_neg hn_pos.le]
        field_simp [hn_pos.ne', (Real.rpow_pos_of_pos hn_pos (r / 2)).ne']
      simp only [hn, hn0, ↓reduceIte, gallagherWeight]
      calc (Λ n / (n : ℝ)) * r * (u ^ k / (k.factorial : ℝ)) * (n : ℝ) ^ (-r)
          = ((u ^ k / (k.factorial : ℝ)) * Real.exp (-u / 2)) * ((Λ n / (n : ℝ)) * r * (n : ℝ) ^ (-(r / 2))) := by
              rw [hrpow_split]; ring
        _ ≤ Real.exp (-6 * (k : ℝ)) * (2 * ((r / 2) * (Λ n / (n : ℝ) ^ (1 + r / 2)))) := by
            rw [hden_eq]
            exact mul_le_mul_of_nonneg_right hchernoff (by
              have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity)
        _ = 2 * Real.exp (-6 * (k : ℝ)) * (r / 2 * (Λ n / (n : ℝ) ^ (1 + r / 2))) := by ring
    · simp only [hn, ↓reduceIte]
      split_ifs
      · simp
      · have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
  have hsumm : Summable (fun n : ℕ => if N₂ < n then gallagherWeight k r n else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs; exact gallagherWeight_nonneg k hr n; exact le_rfl)
      hterm (hsumm_half.mul_left _)
  refine ⟨hsumm, ?_⟩
  calc ∑' n : ℕ, (if N₂ < n then gallagherWeight k r n else 0)
      ≤ ∑' n : ℕ, (2 * Real.exp (-6 * (k : ℝ))) *
          (if n = 0 then (0 : ℝ) else (r / 2) * (Λ n / (n : ℝ) ^ (1 + r / 2))) :=
        Summable.tsum_le_tsum hterm hsumm (hsumm_half.mul_left _)
    _ = (2 * Real.exp (-6 * (k : ℝ))) *
          ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (r / 2) * (Λ n / (n : ℝ) ^ (1 + r / 2))) := tsum_mul_left
    _ ≤ (2 * Real.exp (-6 * (k : ℝ))) * (hadamardConst + 1) :=
        mul_le_mul_of_nonneg_left htsum_half (by positivity)
    _ = 2 * (hadamardConst + 1) * Real.exp (-6 * (k : ℝ)) := by ring

/-- Elementary dyadic-block bound `∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(5 / 4 : ℝ)) ≤ 16`. -/
private lemma sum_rpow_neg_five_fourths_le (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ (-(5 / 4 : ℝ))) ≤ 16 := by
  set K : ℕ := M + 1
  have hsub : Finset.Icc 1 M ⊆ (Finset.range K).biUnion (fun j : ℕ => Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1) : ℕ)) := by
    intro n hn
    obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
    rw [Finset.mem_biUnion]
    set j : ℕ := Nat.log 2 n
    have hj_lt : j < K := lt_of_le_of_lt (Nat.log_le_self 2 n) (by omega)
    refine ⟨j, Finset.mem_range.mpr hj_lt, Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 (by omega),
      Nat.lt_pow_succ_log_self (by norm_num) n⟩⟩
  have hbiUnion_le : ∀ (s : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℝ),
      (∀ x, 0 ≤ f x) → ∑ x ∈ s.biUnion t, f x ≤ ∑ j ∈ s, ∑ x ∈ t j, f x := by
    classical
    intro s t f hf
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert has]
      have hunion_le : ∑ x ∈ t a ∪ s.biUnion t, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
        have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
        have hnn : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun _ _ => hf _
        linarith
      exact hunion_le.trans (add_le_add le_rfl ih)
  have h1 : ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ (-(5 / 4 : ℝ))) ≤
      ∑ j ∈ Finset.range K, ∑ n ∈ Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1) : ℕ), ((n : ℝ) ^ (-(5 / 4 : ℝ))) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (hbiUnion_le _ _ _ fun _ => by positivity)
  set q : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ))
  have hq_pos : 0 < q := by positivity
  have hq_le : q ≤ 7 / 8 := by
    have hpow : q ^ 4 = 1 / 2 := by
      dsimp only [q]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    by_contra hgt; push Not at hgt
    have h4 : (7 / 8 : ℝ) ^ 4 < q ^ 4 := pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
    rw [hpow] at h4; norm_num at h4
  have hblock : ∀ j : ℕ, ∑ n ∈ Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1) : ℕ), ((n : ℝ) ^ (-(5 / 4 : ℝ))) ≤ q ^ j := by
    intro j
    have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    calc ∑ n ∈ Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1) : ℕ), ((n : ℝ) ^ (-(5 / 4 : ℝ)))
        ≤ ∑ _n ∈ Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1) : ℕ), (((2 : ℝ) ^ j) ^ (-(5 / 4 : ℝ))) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hge : ((2 : ℝ) ^ j) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hn).1
          rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
          exact inv_anti₀ (by positivity) (Real.rpow_le_rpow h2j_pos.le hge (by norm_num))
      _ = ((2 ^ (j + 1) - 2 ^ j : ℕ) : ℝ) * (((2 : ℝ) ^ j) ^ (-(5 / 4 : ℝ))) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ = ((2 : ℝ) ^ j) * (((2 : ℝ) ^ j) ^ (-(5 / 4 : ℝ))) := by
          have hsub2 : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
          rw [hsub2]; push_cast; rfl
      _ = q ^ j := by
          dsimp only [q]
          rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]
          congr 1; ring
  have hgeom : ∑ j ∈ Finset.range K, q ^ j ≤ 8 := by
    have hlt1 : q < 1 := by linarith
    have hsum := geom_sum_eq hlt1.ne K
    rw [hsum]
    have hnum : 1 - q ^ K ≤ 1 := by linarith [pow_nonneg hq_pos.le K]
    have hden : 1 / 8 ≤ 1 - q := by linarith
    have hrew : (q ^ K - 1) / (q - 1) = (1 - q ^ K) / (1 - q) := by
      rw [← neg_div_neg_eq]; congr 1 <;> ring
    rw [hrew]
    calc (1 - q ^ K) / (1 - q) ≤ 1 / (1 / 8) := div_le_div₀ zero_le_one hnum (by norm_num) hden
      _ = 8 := by norm_num
  exact h1.trans ((Finset.sum_le_sum fun j _ => hblock j).trans (by linarith))

/-- **Prime-Power Tail Bound**:
for `k ≥ 1`, `0 < r ≤ 1`, and `1 ≤ N₁`:
`∑' n, (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ≤ 256 * r * (N₁ : ℝ) ^ (-(1 / 4 : ℝ))`. -/
private lemma gallagher_prime_power_tail_le {k : ℕ} (_hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) (_hr1 : r ≤ 1)
    {N₁ : ℕ} (hN₁ : 1 ≤ N₁) :
    Summable (fun n : ℕ => if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ∧
    ∑' n : ℕ, (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ≤
      256 * r * (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hN₁_pos : (0 : ℝ) < (N₁ : ℝ) := Nat.cast_pos.mpr hN₁
  -- Bound EVERY finite partial sum by `256 * r * N₁^(-1/4)`!
  have hfin : ∀ F : Finset ℕ,
      ∑ n ∈ F, (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ≤
        256 * r * (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro F
    classical
    set F' : Finset ℕ := F.filter (fun n => N₁ < n ∧ ¬ n.Prime ∧ IsPrimePow n)
    have hstep1 : ∑ n ∈ F, (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ≤
        r * (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) * ∑ n ∈ F', Λ n / (n : ℝ) ^ (3 / 4 : ℝ) := by
      have hzero_out : ∀ n ∈ F, n ∉ F' →
          (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) = 0 := by
        intro n hn hnot
        by_cases hcond : N₁ < n ∧ ¬ n.Prime
        · have hnotpp : ¬ IsPrimePow n := fun hpp => hnot (Finset.mem_filter.mpr ⟨hn, hcond.1, hcond.2, hpp⟩)
          rw [if_pos hcond]
          dsimp only [gallagherWeight]
          have hL0 : Λ n = 0 := by rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnotpp]
          split_ifs <;> simp [hL0]
        · rw [if_neg hcond]
      rw [← Finset.sum_subset (Finset.filter_subset _ F) hzero_out, Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      obtain ⟨_, hnN₁, hnNP, _⟩ := Finset.mem_filter.mp hn
      have hn0 : n ≠ 0 := by omega
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [if_pos ⟨hnN₁, hnNP⟩]
      have hle1 := gallagherWeight_le k hr n
      rw [if_neg hn0] at hle1
      refine hle1.trans ?_
      have hn_gt : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN₁.le
      have hrpow_le : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_neg hn_pos.le, Real.rpow_neg hN₁_pos.le]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hN₁_pos.le hn_gt (by norm_num))
      have hsplit : (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 / 4 : ℝ)) * ((n : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
        rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos]; norm_num
      calc r * (Λ n / (n : ℝ))
          = r * (n : ℝ) ^ (-(1 / 4 : ℝ)) * (Λ n / (n : ℝ) ^ (3 / 4 : ℝ)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv, hsplit]; ring
        _ ≤ r * (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) * (Λ n / (n : ℝ) ^ (3 / 4 : ℝ)) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow_le hr.le) ?_
              exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    -- Map `n ∈ F'` injectively to `(p, m) = (n.minFac, n.factorization n.minFac)` with `p ≥ 2`, `m ≥ 2`!
    set M : ℕ := F'.sup id + 2
    have hinj : ∀ n ∈ F',
        n.minFac ∈ Finset.Icc 2 M ∧ n.factorization n.minFac ∈ Finset.Icc 2 M ∧
        n = n.minFac ^ (n.factorization n.minFac) ∧ Λ n = Real.log (n.minFac : ℝ) := by
      intro n hn
      obtain ⟨_, hnN₁, hnNP, hpp⟩ := Finset.mem_filter.mp hn
      obtain ⟨p, m, hp_pr, hm_pos, hpm_eq⟩ := (isPrimePow_nat_iff n).mp hpp
      have hn_ne1 : n ≠ 1 := by
        intro h1; rw [h1] at hpm_eq
        have : 2 ≤ p ^ m := le_trans hp_pr.two_le (Nat.le_self_pow hm_pos.ne' p)
        omega
      have hmf : n.minFac = p := by
        have hdvd_pm : n.minFac ∣ p ^ m := hpm_eq.symm ▸ Nat.minFac_dvd n
        have hpr_mf : n.minFac.Prime := Nat.minFac_prime hn_ne1
        have hdvd_p : n.minFac ∣ p := hpr_mf.dvd_of_dvd_pow hdvd_pm
        rcases hp_pr.eq_one_or_self_of_dvd _ hdvd_p with h1 | hself
        · exact absurd h1 hpr_mf.ne_one
        · exact hself
      have hfac : n.factorization n.minFac = m := by
        rw [hmf, ← hpm_eq, hp_pr.factorization_pow]; simp
      have hm_ge2 : 2 ≤ m := by
        by_contra hlt; push Not at hlt
        have hm1 : m = 1 := by omega
        rw [hm1, pow_one] at hpm_eq
        exact hnNP (hpm_eq ▸ hp_pr)
      have hn_le_M : n ≤ M := le_trans (Finset.le_sup (f := id) hn) (Nat.le_add_right _ 2)
      have hp_le_n : p ≤ n := by rw [← hpm_eq]; exact Nat.le_self_pow hm_pos.ne' p
      have hm_le_n : m ≤ n := by
        rw [← hpm_eq]
        exact le_trans (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_left hp_pr.two_le m)
      have hL : Λ n = Real.log (p : ℝ) := by
        rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp, hmf]
      rw [hfac, hmf, hL]
      exact ⟨Finset.mem_Icc.mpr ⟨hp_pr.two_le, hp_le_n.trans hn_le_M⟩,
        Finset.mem_Icc.mpr ⟨hm_ge2, hm_le_n.trans hn_le_M⟩, hpm_eq.symm, rfl⟩
    have hsum_F' : ∑ n ∈ F', Λ n / (n : ℝ) ^ (3 / 4 : ℝ) ≤
        ∑ p ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 2 M,
          Real.log (p : ℝ) / ((p : ℝ) ^ m) ^ (3 / 4 : ℝ) := by
      rw [← Finset.sum_product']
      let phi : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac)
      have hmap : ∑ n ∈ F', Λ n / (n : ℝ) ^ (3 / 4 : ℝ) =
          ∑ x ∈ F'.image phi, Real.log (x.1 : ℝ) / ((x.1 : ℝ) ^ x.2) ^ (3 / 4 : ℝ) := by
        symm
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun n hn => ?_
          obtain ⟨_, _, hpow, hL⟩ := hinj n hn
          dsimp only [phi]
          rw [hL]
          congr 1
          conv_rhs => rw [hpow]
          push_cast; rfl
        · intro n₁ hn₁ n₂ hn₂ heq
          have h1 := (hinj n₁ hn₁).2.2.1
          have h2 := (hinj n₂ hn₂).2.2.1
          have hmf : n₁.minFac = n₂.minFac := congrArg Prod.fst heq
          have hfc : n₁.factorization n₁.minFac = n₂.factorization n₂.minFac := congrArg Prod.snd heq
          rw [h1, h2, hfc, hmf]
      rw [hmap]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => ?_)
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
        exact Finset.mem_product.mpr ⟨(hinj n hn).1, (hinj n hn).2.1⟩
      · have hlog : 0 ≤ Real.log (x.1 : ℝ) := Real.log_nonneg (by
          rcases Finset.mem_product.mp hx with ⟨h1, _⟩
          exact_mod_cast (by have := (Finset.mem_Icc.mp h1).1; omega : 1 ≤ x.1))
        positivity
    -- Bound the double sum by `256`!
    have hinner : ∀ p ∈ Finset.Icc 2 M,
        ∑ m ∈ Finset.Icc 2 M, Real.log (p : ℝ) / ((p : ℝ) ^ m) ^ (3 / 4 : ℝ) ≤
          16 * (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      intro p hp
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp).1
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
      set α : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
      have hα_pos : 0 < α := by positivity
      have hα_le : α ≤ 3 / 4 := by
        have h1 : α ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
          dsimp only [α]; rw [Real.rpow_neg hp_pos.le, Real.rpow_neg (by norm_num)]
          exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) (by norm_num))
        have h2 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 / 4 := by
          by_contra hgt; push Not at hgt
          have h4 : (3 / 4 : ℝ) ^ 4 < ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 4 :=
            pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(3 / 4 : ℝ))) 4, ← Real.rpow_mul (by norm_num)] at h4
          norm_num at h4
        linarith
      have hterm_eq : ∀ m : ℕ, Real.log (p : ℝ) / ((p : ℝ) ^ m) ^ (3 / 4 : ℝ) = Real.log (p : ℝ) * α ^ m := by
        intro m; dsimp only [α]
        rw [div_eq_mul_inv, ← Real.rpow_natCast (p : ℝ) m, ← Real.rpow_mul hp_pos.le,
          ← Real.rpow_neg hp_pos.le, ← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
        congr 2; ring
      simp_rw [hterm_eq, ← Finset.mul_sum]
      have hgeom : ∑ m ∈ Finset.Icc 2 M, α ^ m ≤ 4 * α ^ 2 := by
        have hsub_m : Finset.Icc 2 M ⊆ (Finset.range M).image (fun j => j + 2) := by
          intro m hm
          obtain ⟨h2, hM⟩ := Finset.mem_Icc.mp hm
          exact Finset.mem_image.mpr ⟨m - 2, Finset.mem_range.mpr (by omega), by omega⟩
        have h1 : ∑ m ∈ Finset.Icc 2 M, α ^ m ≤ ∑ j ∈ Finset.range M, α ^ (j + 2) := by
          refine (Finset.sum_le_sum_of_subset_of_nonneg hsub_m fun _ _ _ => by positivity).trans_eq ?_
          exact Finset.sum_image (fun a _ b _ h => by omega)
        have h2 : ∑ j ∈ Finset.range M, α ^ (j + 2) = α ^ 2 * ∑ j ∈ Finset.range M, α ^ j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
        rw [h2] at h1
        have h3 : ∑ j ∈ Finset.range M, α ^ j ≤ 4 := by
          have hlt1 : α < 1 := by linarith
          rw [geom_sum_eq hlt1.ne M]
          have hrew : (α ^ M - 1) / (α - 1) = (1 - α ^ M) / (1 - α) := by
            rw [← neg_div_neg_eq]; congr 1 <;> ring
          rw [hrew]
          calc (1 - α ^ M) / (1 - α) ≤ 1 / (1 / 4) :=
                div_le_div₀ zero_le_one (by linarith [pow_nonneg hα_pos.le M]) (by norm_num) (by linarith)
            _ = 4 := by norm_num
        calc ∑ m ∈ Finset.Icc 2 M, α ^ m ≤ α ^ 2 * ∑ j ∈ Finset.range M, α ^ j := h1
          _ ≤ α ^ 2 * 4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg α)
          _ = 4 * α ^ 2 := by ring
      have hlog_bd : Real.log (p : ℝ) ≤ 4 * (p : ℝ) ^ (1 / 4 : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp_pos (1 / 4 : ℝ))
        rw [Real.log_rpow hp_pos] at h; linarith
      have hα2 : α ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        dsimp only [α]; rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]; congr 1; norm_num
      have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      calc Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 2 M, α ^ m
          ≤ (4 * (p : ℝ) ^ (1 / 4 : ℝ)) * (4 * α ^ 2) :=
            mul_le_mul hlog_bd hgeom (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 16 * ((p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by rw [hα2]; ring
        _ = 16 * (p : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [← Real.rpow_add hp_pos]; norm_num
    have hdouble : ∑ p ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 2 M,
        Real.log (p : ℝ) / ((p : ℝ) ^ m) ^ (3 / 4 : ℝ) ≤ 256 := by
      calc _ ≤ ∑ p ∈ Finset.Icc 2 M, 16 * (p : ℝ) ^ (-(5 / 4 : ℝ)) := Finset.sum_le_sum hinner
        _ = 16 * ∑ p ∈ Finset.Icc 2 M, (p : ℝ) ^ (-(5 / 4 : ℝ)) := (Finset.mul_sum _ _ _).symm
        _ ≤ 16 * ∑ p ∈ Finset.Icc 1 M, (p : ℝ) ^ (-(5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc (by omega) le_rfl) fun _ _ _ => by positivity) (by norm_num)
        _ ≤ 16 * 16 := mul_le_mul_of_nonneg_left (sum_rpow_neg_five_fourths_le M) (by norm_num)
        _ = 256 := by norm_num
    exact hstep1.trans (mul_le_mul_of_nonneg_left (hsum_F'.trans hdouble) (by positivity) |>.trans_eq (by ring))
  have hsumm : Summable (fun n : ℕ => if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) :=
    summable_of_sum_le (fun n => by split_ifs; exact gallagherWeight_nonneg k hr n; exact le_rfl) hfin
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le hfin⟩

/-- Universal de la Vallée Poussin constant for `riemannZeta` from `Stage6XiZeroDensity`. -/
private noncomputable def c_zeta_zfr : ℝ :=
  Classical.choose Stage6XiZeroDensity.riemannZeta_two_sided_zeroFree_strip

private lemma c_zeta_zfr_spec :
    0 < c_zeta_zfr ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
      c_zeta_zfr / Real.log (|ρ.im| + 2) < ρ.re ∧ ρ.re < 1 - c_zeta_zfr / Real.log (|ρ.im| + 2) :=
  Classical.choose_spec Stage6XiZeroDensity.riemannZeta_two_sided_zeroFree_strip

/-- Universal detector multiplier `C_K : ℕ` (strictly independent of `m, Q, T, σ, r`). -/
private noncomputable def detectorCK : ℕ :=
  max 50 (max ⌈45 / (Real.exp (-10) * C_Z_const * 300)⌉₊
    (⌈Real.log (100000 * C_Z_const + 10000 * hadamardConst + 100000)⌉₊ + 20))

/-- Universal small-radius threshold `δ₀ > 0` for the log-free zero detector. -/
private noncomputable def detectorDelta0 : ℝ :=
  min (1 / 301 : ℝ) (min (Real.exp (-10) / 40) (c_zeta_zfr / (4 * Real.log 4)))

private lemma detectorDelta0_pos : 0 < detectorDelta0 := by
  dsimp only [detectorDelta0]
  have h1 : 0 < c_zeta_zfr := c_zeta_zfr_spec.1
  have h2 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

private lemma detectorCK_ge_50 : 50 ≤ detectorCK := le_max_left _ _

/-- Core prime-sum lower bound shared by both primitive `L(s, ψ)` and `riemannZeta`:
given `D ≥ 3`, `0 < r < detectorDelta0`, `γ₀ : ℝ`, `ρ_seq`, and a witness `j₀` with `‖s₀ - ρ_seq j₀‖ < 3 * r`,
produces `k ∈ Icc K (K + M₀)` with `(1 / 16) * exp (-4 k) ≤ ‖∑_{p ∈ (N₁, N₂], p prime} gallagherWeight k r p * c p * p^(-I*γ₀)‖`! -/
private lemma gallagher_prime_zero_detector_core
    {D : ℝ} (hD : 3 ≤ D) {r : ℝ} (hr : 0 < r) (hr_lt : r < detectorDelta0) (γ₀ : ℝ)
    (ρ : ℕ → ℂ) (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum_inv : Summable (fun j : ℕ => (‖ρ j‖ ^ 2)⁻¹))
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hB_re : ∀ (d : ℝ) (F : Finset ℕ), 0 < d → d ≤ 1 →
      ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j)).re ≤ C_Z_const * (2 * Real.log D + 1 / d))
    (hhigh : ∀ k : ℕ, 1 ≤ k →
      ‖(∑' n : ℕ, if n = 0 then (0 : ℂ) else
          c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) *
            (n : ℂ) ^ (-(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)))) +
        ∑' j : ℕ, (((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j) ^ (k + 1))⁻¹‖ ≤
      3 + ((300 * r) ^ (k + 1))⁻¹)
    (j_star : ℕ) (hj_star : ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ j_star‖ < 3 * r) :
    let L := Real.log D
    let M₀ := ⌈8 * C_Z_const * (300 * r * L + 1)⌉₊
    let K := detectorCK * M₀
    ∃ k ∈ Finset.Icc K (K + M₀),
      let N₁ := ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
      let N₂ := ⌊Real.exp (30 * (k : ℝ) / r)⌋₊
      D ^ 40 ≤ (N₁ : ℝ) ∧ 2 ≤ N₁ ∧ N₁ ≤ N₂ ∧
      (1 / 16 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤
        ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
          (gallagherWeight k r p : ℂ) * c p * (p : ℂ) ^ (-(I * (γ₀ : ℂ)))‖ := by
  classical
  intro L M₀ K
  have hL_gt1 : 1 < L := by
    dsimp only [L]
    have h3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) (h3.trans_le hD)
    rwa [Real.log_exp] at this
  have hCZ : 1 ≤ C_Z_const := one_le_C_Z_const
  have hr_301 : r < 1 / 301 := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_eps : r < Real.exp (-10) / 40 :=
    lt_of_lt_of_le hr_lt ((min_le_right _ _).trans (min_le_left _ _))
  have hR_le1 : 300 * r ≤ 1 := by linarith
  have hR_pos : 0 < 300 * r := by positivity
  set s₀ : ℂ := ((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)
  -- Step 1: Collect the finite set `B` of ALL zero indices with `‖s₀ - ρ j‖ < 300 * r`!
  have hB_fin : {j : ℕ | ‖s₀ - ρ j‖ < 300 * r}.Finite := by
    have htend := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq
      (fun j h0 => by have := (hstrip j).1; rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this) hsum_inv
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually (Filter.eventually_ge_atTop (‖s₀‖ + 300 * r + 1)))
    refine (Set.finite_lt_nat N).subset fun j hj => ?_
    by_contra hlt
    have hge : N ≤ j := not_lt.mp hlt
    have h1 := hN j hge
    have htri : ‖ρ j‖ ≤ ‖s₀‖ + ‖s₀ - ρ j‖ := by
      have := norm_sub_le s₀ (s₀ - ρ j); rwa [sub_sub_cancel] at this
    change ‖s₀ - ρ j‖ < 300 * r at hj
    linarith
  set B : Finset ℕ := hB_fin.toFinset
  have hB_mem : ∀ j : ℕ, j ∈ B ↔ ‖s₀ - ρ j‖ < 300 * r := fun j => hB_fin.mem_toFinset
  have hj_mem : j_star ∈ B := (hB_mem j_star).mpr (lt_trans hj_star (by linarith))
  have hM_ge1 : 1 ≤ B.card := Finset.card_pos.mpr ⟨j_star, hj_mem⟩
  have hM_le_M₀ : B.card ≤ M₀ := by
    have hcardR : (B.card : ℝ) ≤ 4 * (300 * r) * (C_Z_const * (2 * L + 1 / (300 * r))) :=
      local_ball_card_le hstrip hr (by linarith) γ₀ _ (hB_re (300 * r) · hR_pos hR_le1) B
        (fun j hj => (hB_mem j).mp hj)
    have hle : (B.card : ℝ) ≤ 8 * C_Z_const * (300 * r * L + 1) := by
      have halg : 4 * (300 * r) * (C_Z_const * (2 * L + 1 / (300 * r))) =
          8 * C_Z_const * (300 * r * L) + 4 * C_Z_const := by field_simp [hr.ne']; ring
      rw [halg] at hcardR; linarith
    exact Nat.cast_le.mp (hle.trans (Nat.le_ceil (8 * C_Z_const * (300 * r * L + 1))))
  have hM₀_ge1 : 1 ≤ M₀ := hM_ge1.trans hM_le_M₀
  -- Step 2: Apply Turán's Second Main Theorem (`turan_power_sum_second_main`) to `z j = (3*r) / (s₀ - ρ j)` on `B`!
  let emb : Fin B.card → ℕ := fun i => (B.equivFin.symm i).1
  let zB : Fin B.card → ℂ := fun i => ((3 * r : ℝ) : ℂ) / (s₀ - ρ (emb i))
  have hmax_zB : ∃ i₀ : Fin B.card, 1 ≤ ‖zB i₀‖ := by
    let i₀ : Fin B.card := B.equivFin ⟨j_star, hj_mem⟩
    refine ⟨i₀, ?_⟩
    have heq : emb i₀ = j_star := by dsimp only [emb, i₀]; simp
    dsimp only [zB]; rw [heq, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hpos_d : 0 < ‖s₀ - ρ j_star‖ := by
      have h1 : r < (s₀ - ρ j_star).re := by simp [s₀]; linarith [(hstrip j_star).2]
      exact lt_of_lt_of_le hr (h1.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))
    exact (one_le_div hpos_d).mpr hj_star.le
  obtain ⟨kp, hkp_mem, hturan⟩ := turan_power_sum_second_main hM_ge1 K zB hmax_zB
  obtain ⟨hkp_lo, hkp_hi⟩ := Finset.mem_Icc.mp hkp_mem
  set k : ℕ := kp - 1
  have hkp_eq : k + 1 = kp := by omega
  have hk_mem : k ∈ Finset.Icc K (K + M₀) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hk_ge_K : K ≤ k := (Finset.mem_Icc.mp hk_mem).1
  have hk_ge_50 : 50 ≤ k := by
    have : 50 ≤ detectorCK := detectorCK_ge_50
    have : detectorCK ≤ K := Nat.le_mul_of_pos_right detectorCK hM₀_ge1
    omega
  have hk1 : 1 ≤ k := by omega
  have hsum_zB_eq : ∑ i : Fin B.card, zB i ^ kp =
      ∑ j ∈ B, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1) := by
    rw [hkp_eq]
    symm
    refine Finset.sum_bij (fun j hj => B.equivFin ⟨j, hj⟩) (fun _ _ => Finset.mem_univ _)
      (fun j₁ hj₁ j₂ hj₂ h => by
        have := B.equivFin.injective h
        exact congrArg Subtype.val this)
      (fun i _ => ⟨(B.equivFin.symm i).1, (B.equivFin.symm i).2, by simp⟩)
      (fun j hj => by dsimp only [zB, emb]; simp)
  rw [hsum_zB_eq] at hturan
  -- Simplify Turán lower bound: `(1 / (64 * e)) ^ B.card * (1/2) ^ K ≥ exp (-2 * k)`!
  have hturan_exp : Real.exp (-2 * (k : ℝ)) ≤ ‖∑ j ∈ B, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)‖ := by
    have h64e : 64 * Real.exp 1 ≤ Real.exp 6 := by
      have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h5 : (64 : ℝ) ≤ (Real.exp 1) ^ 5 := by
        have h25 : (25 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have := pow_le_pow_left₀ (by norm_num) h25 5
        linarith [show (64 : ℝ) ≤ (25 / 10 : ℝ) ^ 5 by norm_num]
      have hexp6 : Real.exp 6 = (Real.exp 1) ^ 5 * Real.exp 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num
      rw [hexp6]; exact mul_le_mul_of_nonneg_right h5 (Real.exp_pos 1).le
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp1 : Real.exp (-6 * (B.card : ℝ)) ≤ (1 / (64 * Real.exp 1)) ^ B.card := by
      have hbase : Real.exp (-6) ≤ 1 / (64 * Real.exp 1) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (by positivity) h64e
      calc Real.exp (-6 * (B.card : ℝ)) = (Real.exp (-6)) ^ B.card := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ (1 / (64 * Real.exp 1)) ^ B.card := pow_le_pow_left₀ (Real.exp_pos _).le hbase B.card
    have hp2 : Real.exp (-(K : ℝ)) ≤ (1 / 2 : ℝ) ^ K := by
      have hbase : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (by norm_num) h2e
      calc Real.exp (-(K : ℝ)) = (Real.exp (-1)) ^ K := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ (1 / 2 : ℝ) ^ K := pow_le_pow_left₀ (Real.exp_pos _).le hbase K
    have hexp_comb : Real.exp (-2 * (k : ℝ)) ≤ Real.exp (-6 * (B.card : ℝ)) * Real.exp (-(K : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hB_le_M₀ : (B.card : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM_le_M₀
      have h6M₀ : 6 * (M₀ : ℝ) ≤ (K : ℝ) := by
        dsimp only [K]; push_cast
        have hCK6 : (6 : ℝ) ≤ (detectorCK : ℝ) := by exact_mod_cast (by have := detectorCK_ge_50; omega : 6 ≤ detectorCK)
        nlinarith [Nat.cast_nonneg (α := ℝ) M₀]
      have hKk : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_K
      linarith
    exact hexp_comb.trans ((mul_le_mul hp1 hp2 (Real.exp_pos _).le (by positivity)).trans hturan)
  -- Step 3: Bound outer zeros `j ∉ B` (`‖s₀ - ρ j‖ ≥ 300 * r`) via `tsum_r_sq_div_norm_sq_le`!
  obtain ⟨hsumm_sq, htsum_sq_le⟩ := tsum_r_sq_div_norm_sq_le hstrip hr γ₀
    (C_Z_const * (2 * L + 1 / r)) (fun F => hB_re r F hr (by linarith))
  have htsum_sq_clean : ∑' j : ℕ, r ^ 2 / ‖s₀ - ρ j‖ ^ 2 ≤ C_Z_const * (2 * r * L + 1) :=
    htsum_sq_le.trans_eq (by field_simp [hr.ne'])
  have hsumm_zp : Summable (fun j : ℕ => (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)) := by
    refine Summable.of_norm_bounded (hsumm_sq.mul_left (9 * (3 : ℝ) ^ (k - 1))) fun j => ?_
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hge_r : r ≤ ‖s₀ - ρ j‖ := by
      have h1 : r < (s₀ - ρ j).re := by simp [s₀]; linarith [(hstrip j).2]
      exact h1.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    have hratio : 3 * r / ‖s₀ - ρ j‖ ≤ 3 := (div_le_iff₀ (lt_of_lt_of_le hr hge_r)).mpr (by linarith)
    have hexp : k + 1 = (k - 1) + 2 := by omega
    rw [hexp, pow_add]
    calc (3 * r / ‖s₀ - ρ j‖) ^ (k - 1) * (3 * r / ‖s₀ - ρ j‖) ^ 2
        ≤ (3 : ℝ) ^ (k - 1) * (3 * r / ‖s₀ - ρ j‖) ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio _) (sq_nonneg _)
      _ = 9 * (3 : ℝ) ^ (k - 1) * (r ^ 2 / ‖s₀ - ρ j‖ ^ 2) := by rw [div_pow, mul_pow]; ring
  have houter_le : ‖∑' j : ℕ, (if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1))‖ ≤
      (1 / 8 : ℝ) * Real.exp (-2 * (k : ℝ)) := by
    have hterm_out : ∀ j : ℕ,
        ‖if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)‖ ≤
          (9 * (1 / 100 : ℝ) ^ (k - 1)) * (r ^ 2 / ‖s₀ - ρ j‖ ^ 2) := by
      intro j
      by_cases hjB : j ∈ B
      · rw [if_pos hjB, norm_zero]; positivity
      · rw [if_neg hjB, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hge300 : 300 * r ≤ ‖s₀ - ρ j‖ := not_lt.mp (fun h => hjB ((hB_mem j).mpr h))
        have hratio : 3 * r / ‖s₀ - ρ j‖ ≤ 1 / 100 := by
          rw [div_le_iff₀ (lt_of_lt_of_le hR_pos hge300)]; linarith
        have hexp : k + 1 = (k - 1) + 2 := by omega
        rw [hexp, pow_add]
        calc (3 * r / ‖s₀ - ρ j‖) ^ (k - 1) * (3 * r / ‖s₀ - ρ j‖) ^ 2
            ≤ (1 / 100 : ℝ) ^ (k - 1) * (3 * r / ‖s₀ - ρ j‖) ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio _) (sq_nonneg _)
          _ = 9 * (1 / 100 : ℝ) ^ (k - 1) * (r ^ 2 / ‖s₀ - ρ j‖ ^ 2) := by
              rw [div_pow (3 * r), mul_pow]; ring
    have hsumm_out : Summable (fun j : ℕ => if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)) :=
      Summable.of_norm_bounded (hsumm_sq.mul_left _) hterm_out
    have h1 : ‖∑' j : ℕ, (if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1))‖ ≤
        9 * (1 / 100 : ℝ) ^ (k - 1) * (C_Z_const * (2 * r * L + 1)) := by
      calc ‖∑' j : ℕ, (if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1))‖
          ≤ ∑' j : ℕ, ‖if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)‖ :=
            norm_tsum_le_tsum_norm hsumm_out.norm
        _ ≤ ∑' j : ℕ, (9 * (1 / 100 : ℝ) ^ (k - 1)) * (r ^ 2 / ‖s₀ - ρ j‖ ^ 2) :=
            Summable.tsum_le_tsum hterm_out hsumm_out.norm (hsumm_sq.mul_left _)
        _ = 9 * (1 / 100 : ℝ) ^ (k - 1) * ∑' j : ℕ, r ^ 2 / ‖s₀ - ρ j‖ ^ 2 := tsum_mul_left
        _ ≤ 9 * (1 / 100 : ℝ) ^ (k - 1) * (C_Z_const * (2 * r * L + 1)) :=
            mul_le_mul_of_nonneg_left htsum_sq_clean (by positivity)
    -- Show `9 * (1 / 100)^(k-1) * C_Z_const * (2 r L + 1) ≤ (1 / 8) * exp (-2 k)`!
    have h100 : Real.exp 4 ≤ 100 := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ ≤ 100 := by norm_num
    have hpow100 : (1 / 100 : ℝ) ^ (k - 1) ≤ 100 * Real.exp (-4 * (k : ℝ)) := by
      have hbase : (1 / 100 : ℝ) ≤ Real.exp (-4) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 4) h100
      have hmul : (1 / 100 : ℝ) ^ (k - 1) = 100 * (1 / 100 : ℝ) ^ k := by
        have hk' : k = (k - 1) + 1 := by omega
        conv_rhs => rw [hk', pow_succ]; ring
      rw [hmul]
      calc 100 * (1 / 100 : ℝ) ^ k ≤ 100 * (Real.exp (-4)) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hbase k) (by norm_num)
        _ = 100 * Real.exp (-4 * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 2; ring
    have hfactor : 900 * C_Z_const * (2 * r * L + 1) ≤ (1 / 8 : ℝ) * Real.exp (2 * (k : ℝ)) := by
      have hk_ge_k1 : (k : ℝ) ≤ Real.exp (k : ℝ) := le_trans (by linarith) (Real.add_one_le_exp (k : ℝ))
      have hM₀_le_k : (M₀ : ℝ) ≤ (k : ℝ) := by
        have : M₀ ≤ K := Nat.le_mul_of_pos_left M₀ (by have := detectorCK_ge_50; omega)
        exact_mod_cast this.trans hk_ge_K
      have hlin : 2 * r * L + 1 ≤ (M₀ : ℝ) := by
        have h1' : 8 * C_Z_const * (300 * r * L + 1) ≤ (M₀ : ℝ) := Nat.le_ceil _
        nlinarith [mul_nonneg hr.le (show 0 ≤ L by linarith)]
      have hck_log : Real.log (100000 * C_Z_const + 10000 * hadamardConst + 100000) ≤ (k : ℝ) := by
        have h1' : ⌈Real.log (100000 * C_Z_const + 10000 * hadamardConst + 100000)⌉₊ ≤ detectorCK :=
          (Nat.le_add_right _ 20).trans ((le_max_right _ _).trans (le_max_right _ _))
        have h2' : detectorCK ≤ k := (Nat.le_mul_of_pos_right detectorCK hM₀_ge1).trans hk_ge_K
        exact (Nat.le_ceil _).trans (by exact_mod_cast h1'.trans h2')
      have hexp_k_ge : 100000 * C_Z_const + 10000 * hadamardConst + 100000 ≤ Real.exp (k : ℝ) := by
        have hpos_arg : 0 < 100000 * C_Z_const + 10000 * hadamardConst + 100000 := by
          linarith [hadamardConst_spec.1]
        rw [← Real.exp_log hpos_arg]
        exact Real.exp_le_exp.mpr hck_log
      have hexp2 : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) * Real.exp (k : ℝ) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp2]
      have h1' : 7200 * C_Z_const ≤ Real.exp (k : ℝ) := by linarith [hadamardConst_spec.1]
      have h2' : 2 * r * L + 1 ≤ Real.exp (k : ℝ) := hlin.trans (hM₀_le_k.trans hk_ge_k1)
      have hmul := mul_le_mul h1' h2' (by positivity) (Real.exp_pos _).le
      linarith
    refine h1.trans ?_
    calc 9 * (1 / 100 : ℝ) ^ (k - 1) * (C_Z_const * (2 * r * L + 1))
        ≤ 9 * (100 * Real.exp (-4 * (k : ℝ))) * (C_Z_const * (2 * r * L + 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow100 (by norm_num)) (by positivity)
      _ = (900 * C_Z_const * (2 * r * L + 1)) * Real.exp (-4 * (k : ℝ)) := by ring
      _ ≤ ((1 / 8 : ℝ) * Real.exp (2 * (k : ℝ))) * Real.exp (-4 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ = (1 / 8 : ℝ) * Real.exp (-2 * (k : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  -- Step 4: Combine Turán, outer zeros, and `hhigh` to lower-bound the full Dirichlet series `D_k(s₀)`!
  have hsplit_tsum :
      ∑' j : ℕ, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1) =
        (∑ j ∈ B, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)) +
        ∑' j : ℕ, (if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)) := by
    have hsumm_out : Summable (fun j : ℕ => if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)) :=
      Summable.of_norm_bounded hsumm_zp.norm fun j => by
        by_cases hj : j ∈ B
        · rw [if_pos hj, norm_zero]; exact norm_nonneg _
        · rw [if_neg hj]
    have hsumm_in : Summable (fun j : ℕ => if j ∈ B then (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1) else 0) :=
      summable_of_ne_finset_zero (s := B) fun j hj => if_neg hj
    have hsum_in : (∑' j : ℕ, if j ∈ B then (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1) else 0) =
        ∑ j ∈ B, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1) := by
      rw [tsum_eq_sum (s := B) (fun j hj => if_neg hj)]
      exact Finset.sum_congr rfl fun j hj => if_pos hj
    rw [← hsum_in, ← Summable.tsum_add hsumm_in hsumm_out]
    refine tsum_congr fun j => ?_; split_ifs <;> simp
  have hscaled_high :
      ‖((3 * r : ℝ) : ℂ) ^ (k + 1) *
          (∑' n : ℕ, if n = 0 then (0 : ℂ) else
            c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀)) +
        ∑' j : ℕ, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)‖ ≤
      (1 / 4 : ℝ) * Real.exp (-2 * (k : ℝ)) := by
    have hpull :
        ((3 * r : ℝ) : ℂ) ^ (k + 1) *
          (∑' n : ℕ, if n = 0 then (0 : ℂ) else
            c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀)) +
        ∑' j : ℕ, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1) =
        ((3 * r : ℝ) : ℂ) ^ (k + 1) *
          ((∑' n : ℕ, if n = 0 then (0 : ℂ) else
            c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀)) +
          ∑' j : ℕ, ((s₀ - ρ j) ^ (k + 1))⁻¹) := by
      rw [mul_add]; congr 1
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_; rw [div_pow, div_eq_mul_inv]
    rw [hpull, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left (hhigh k hk1) (by positivity : 0 ≤ (3 * r) ^ (k + 1))
    have h3r_le : 3 * r ≤ 1 / 100 := by linarith
    have hpow_3r : (3 * r) ^ (k + 1) ≤ (1 / 100 : ℝ) ^ (k + 1) :=
      pow_le_pow_left₀ (by positivity) h3r_le (k + 1)
    have hcancel_300 : (3 * r) ^ (k + 1) * ((300 * r) ^ (k + 1))⁻¹ = (1 / 100 : ℝ) ^ (k + 1) := by
      rw [← div_eq_mul_inv, ← div_pow]
      congr 1; field_simp [hr.ne']; ring
    have h100 : Real.exp 4 ≤ 100 := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ ≤ 100 := by norm_num
    have h100_pow : (1 / 100 : ℝ) ^ (k + 1) ≤ (1 / 100 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
      rw [pow_succ']
      have hbase : (1 / 100 : ℝ) ≤ Real.exp (-4) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 4) h100
      calc (1 / 100 : ℝ) * (1 / 100 : ℝ) ^ k ≤ (1 / 100 : ℝ) * (Real.exp (-4)) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hbase k) (by norm_num)
        _ = (1 / 100 : ℝ) * Real.exp (-4 * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 2; ring
    have hexp_dec : Real.exp (-4 * (k : ℝ)) ≤ Real.exp (-2 * (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    calc (3 * r) ^ (k + 1) * ‖_‖
        ≤ (3 * r) ^ (k + 1) * (3 + ((300 * r) ^ (k + 1))⁻¹) := h1
      _ = 3 * (3 * r) ^ (k + 1) + (3 * r) ^ (k + 1) * ((300 * r) ^ (k + 1))⁻¹ := by ring
      _ ≤ 3 * (1 / 100 : ℝ) ^ (k + 1) + (1 / 100 : ℝ) ^ (k + 1) := by rw [hcancel_300]; linarith
      _ = 4 * (1 / 100 : ℝ) ^ (k + 1) := by ring
      _ ≤ 4 * ((1 / 100 : ℝ) * Real.exp (-4 * (k : ℝ))) := mul_le_mul_of_nonneg_left h100_pow (by norm_num)
      _ ≤ (1 / 4 : ℝ) * Real.exp (-2 * (k : ℝ)) := by nlinarith [Real.exp_pos (-4 * (k : ℝ))]
  -- Deduce `‖∑' n, (gallagherWeight k r n : ℂ) * c n * n^(-I*γ₀)‖ ≥ (1/8) * exp (-4 k)`!
  have hfull_ge : (1 / 8 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤
      ‖∑' n : ℕ, (gallagherWeight k r n : ℂ) * c n * (n : ℂ) ^ (-(I * (γ₀ : ℂ)))‖ := by
    have htri1 : (5 / 8 : ℝ) * Real.exp (-2 * (k : ℝ)) ≤
        ‖((3 * r : ℝ) : ℂ) ^ (k + 1) *
          (∑' n : ℕ, if n = 0 then (0 : ℂ) else
            c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀))‖ := by
      set A_dir : ℂ := ((3 * r : ℝ) : ℂ) ^ (k + 1) *
          (∑' n : ℕ, if n = 0 then (0 : ℂ) else
            c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀))
      set B_in : ℂ := ∑ j ∈ B, (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1)
      set B_out : ℂ := ∑' j : ℕ, (if j ∈ B then (0 : ℂ) else (((3 * r : ℝ) : ℂ) / (s₀ - ρ j)) ^ (k + 1))
      have hdecomp : B_in = (A_dir + (B_in + B_out)) - A_dir - B_out := by ring
      have hnorm : ‖B_in‖ ≤ ‖A_dir + (B_in + B_out)‖ + ‖A_dir‖ + ‖B_out‖ := by
        have h1' : ‖(A_dir + (B_in + B_out)) - A_dir - B_out‖ ≤
            ‖(A_dir + (B_in + B_out)) - A_dir‖ + ‖B_out‖ := norm_sub_le _ _
        have h2' : ‖(A_dir + (B_in + B_out)) - A_dir‖ ≤
            ‖A_dir + (B_in + B_out)‖ + ‖A_dir‖ := norm_sub_le _ _
        conv_lhs => rw [hdecomp]
        linarith
      rw [hsplit_tsum] at hscaled_high
      linarith
    have hrew_dir : ((3 * r : ℝ) : ℂ) ^ (k + 1) *
          (∑' n : ℕ, if n = 0 then (0 : ℂ) else
            c n * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀)) =
        ((3 : ℝ) : ℂ) ^ (k + 1) *
          ∑' n : ℕ, (gallagherWeight k r n : ℂ) * c n * (n : ℂ) ^ (-(I * (γ₀ : ℂ))) := by
      have hmul3 : ((3 * r : ℝ) : ℂ) ^ (k + 1) = ((3 : ℝ) : ℂ) ^ (k + 1) * (r : ℂ) ^ (k + 1) := by
        push_cast; rw [mul_pow]
      rw [hmul3, mul_assoc, ← tsum_mul_left]
      congr 1; refine tsum_congr fun n => r_pow_mul_dirichlet_term_eq k hr γ₀ c n
    rw [hrew_dir, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at htri1
    have h3_le : (3 : ℝ) ^ (k + 1) ≤ 3 * Real.exp (2 * (k : ℝ)) := by
      rw [pow_succ']
      have h3e2 : (3 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
          _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
          _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      calc (3 : ℝ) * (3 : ℝ) ^ k ≤ 3 * (Real.exp 2) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h3e2 k) (by norm_num)
        _ = 3 * Real.exp (2 * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 2; ring
    have hprod := htri1.trans (mul_le_mul_of_nonneg_right h3_le (norm_nonneg _))
    have hdiv := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ (3 * Real.exp (2 * (k : ℝ)))⁻¹)
    have hrhs_eq : (3 * Real.exp (2 * (k : ℝ)))⁻¹ * (3 * Real.exp (2 * (k : ℝ)) *
        ‖∑' n : ℕ, (gallagherWeight k r n : ℂ) * c n * (n : ℂ) ^ (-(I * (γ₀ : ℂ)))‖) =
        ‖∑' n : ℕ, (gallagherWeight k r n : ℂ) * c n * (n : ℂ) ^ (-(I * (γ₀ : ℂ)))‖ := by
      field_simp [(Real.exp_pos _).ne']
    have hlhs_ge : (1 / 8 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤
        (3 * Real.exp (2 * (k : ℝ)))⁻¹ * ((5 / 8 : ℝ) * Real.exp (-2 * (k : ℝ))) := by
      rw [mul_inv, ← Real.exp_neg]
      have hcomb : Real.exp (-(2 * (k : ℝ))) * Real.exp (-2 * (k : ℝ)) = Real.exp (-4 * (k : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (1 / 8 : ℝ) * Real.exp (-4 * (k : ℝ))
          ≤ (5 / 24 : ℝ) * Real.exp (-4 * (k : ℝ)) := by nlinarith [Real.exp_pos (-4 * (k : ℝ))]
        _ = (3 : ℝ)⁻¹ * Real.exp (-(2 * (k : ℝ))) * ((5 / 8 : ℝ) * Real.exp (-2 * (k : ℝ))) := by
            rw [← hcomb]; ring
    exact hlhs_ge.trans (hdiv.trans_eq hrhs_eq)
  -- Step 5: Truncate to primes `p ∈ (N₁, N₂]` and subtract the 3 tiny tails!
  set N₁ : ℕ := ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
  set N₂ : ℕ := ⌊Real.exp (30 * (k : ℝ) / r)⌋₊
  have harg1_ge : 45 * L ≤ Real.exp (-10) * (k : ℝ) / r := by
    have hCK_nat : ⌈45 / (Real.exp (-10) * C_Z_const * 300)⌉₊ ≤ detectorCK := by
      dsimp only [detectorCK]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hCK_ge : 45 / (Real.exp (-10) * C_Z_const * 300) ≤ (detectorCK : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hCK_nat)
    have hM₀_ge : 8 * C_Z_const * (300 * r * L) ≤ (M₀ : ℝ) := by
      have h1 := Nat.le_ceil (8 * C_Z_const * (300 * r * L + 1))
      linarith [hCZ]
    have hk_ge_KM : (detectorCK : ℝ) * (M₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_K
    have hk_ge_lb : (45 / (Real.exp (-10) * C_Z_const * 300)) * (300 * C_Z_const * r * L) ≤ (k : ℝ) := by
      have h1 : 300 * C_Z_const * r * L ≤ (M₀ : ℝ) := by
        have : 0 ≤ C_Z_const * r * L := by positivity
        linarith
      exact (mul_le_mul hCK_ge h1 (by positivity) (by positivity)).trans hk_ge_KM
    have halg : (45 / (Real.exp (-10) * C_Z_const * 300)) * (300 * C_Z_const * r * L) =
        45 * r * L / Real.exp (-10) := by
      field_simp [(Real.exp_pos (-10)).ne', (show (0 : ℝ) < C_Z_const by linarith).ne']
    rw [halg] at hk_ge_lb
    rw [le_div_iff₀ hr]
    have hmul := mul_le_mul_of_nonneg_left hk_ge_lb (Real.exp_pos (-10)).le
    rw [mul_div_cancel₀ _ (Real.exp_pos (-10)).ne'] at hmul
    linarith
  have hN₁_ge_D40 : D ^ 40 ≤ (N₁ : ℝ) := by
    have hD40_eq : D ^ 40 = Real.exp (40 * L) := by
      dsimp only [L]
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < D)]; congr 1; push_cast; ring
    have hexp_ge : Real.exp (40 * L) + 1 ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r) := by
      have h1 : Real.exp (40 * L) * Real.exp 5 ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      have h2 : (2 : ℝ) ≤ Real.exp 5 := by
        linarith [Real.add_one_le_exp (5 : ℝ)]
      have h3 : (1 : ℝ) ≤ Real.exp (40 * L) := Real.one_le_exp (by positivity)
      nlinarith
    have hlt := Nat.lt_floor_add_one (Real.exp (Real.exp (-10) * (k : ℝ) / r))
    rw [hD40_eq]; linarith
  have hN₁_ge2 : 2 ≤ N₁ := by
    have h1 : (2 : ℝ) ≤ (N₁ : ℝ) := (show (2 : ℝ) ≤ 3 ^ 40 by norm_num).trans
      ((pow_le_pow_left₀ (by norm_num) hD 40).trans hN₁_ge_D40)
    exact_mod_cast h1
  have hN₁_le_N₂ : N₁ ≤ N₂ := by
    refine Nat.floor_mono (Real.exp_le_exp.mpr ?_)
    refine div_le_div_of_nonneg_right ?_ hr.le
    have h1 : Real.exp (-10) ≤ 30 := (Real.exp_le_one_iff.mpr (by norm_num)).trans (by norm_num)
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg k)
  refine ⟨k, hk_mem, hN₁_ge_D40, hN₁_ge2, hN₁_le_N₂, ?_⟩
  -- Bound the 3 tails individually by `(1 / 64) * exp (-4 k)`:
  have hck_log : Real.log (100000 * C_Z_const + 10000 * hadamardConst + 100000) ≤ (k : ℝ) := by
    have h1' : ⌈Real.log (100000 * C_Z_const + 10000 * hadamardConst + 100000)⌉₊ ≤ detectorCK :=
      (Nat.le_add_right _ 20).trans ((le_max_right _ _).trans (le_max_right _ _))
    have h2' : detectorCK ≤ k := (Nat.le_mul_of_pos_right detectorCK hM₀_ge1).trans hk_ge_K
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1'.trans h2')
  have hexp_k_big : 100000 * C_Z_const + 10000 * hadamardConst + 100000 ≤ Real.exp (k : ℝ) := by
    have hpos : 0 < 100000 * C_Z_const + 10000 * hadamardConst + 100000 := by linarith [hadamardConst_spec.1]
    rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hck_log
  have htail1 : ∑ n ∈ Finset.Icc 1 N₁, gallagherWeight k r n ≤ (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
    have h1 := gallagher_lower_tail_le hk1 hr (by linarith) (Nat.floor_le (Real.exp_pos _).le)
    refine h1.trans ?_
    have hexp5 : Real.exp (-9 * (k : ℝ)) = Real.exp (-5 * (k : ℝ)) * Real.exp (-4 * (k : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp5, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h5k : Real.exp (k : ℝ) ≤ Real.exp (5 * (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hdiv : (hadamardConst + 1) * Real.exp (-5 * (k : ℝ)) ≤ (hadamardConst + 1) / Real.exp (k : ℝ) := by
      rw [show -5 * (k : ℝ) = -(5 * (k : ℝ)) by ring, Real.exp_neg, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by linarith [hadamardConst_spec.1]) (Real.exp_pos _) h5k
    refine hdiv.trans ((div_le_iff₀ (Real.exp_pos _)).mpr ?_)
    linarith [hadamardConst_spec.1]
  have htail2 :
      Summable (fun n : ℕ => if N₂ < n then gallagherWeight k r n else 0) ∧
      ∑' n : ℕ, (if N₂ < n then gallagherWeight k r n else 0) ≤ (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
    have hN₂_ge : Real.exp (30 * (k : ℝ) / r) - 1 ≤ (N₂ : ℝ) := by
      linarith [Nat.lt_floor_add_one (Real.exp (30 * (k : ℝ) / r))]
    obtain ⟨hs2, h2⟩ := gallagher_upper_tail_le hk1 hr (by linarith) hN₂_ge
    refine ⟨hs2, h2.trans ?_⟩
    have hexp2 : Real.exp (-6 * (k : ℝ)) = Real.exp (-2 * (k : ℝ)) * Real.exp (-4 * (k : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp2, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h2k : Real.exp (k : ℝ) ≤ Real.exp (2 * (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hdiv : 2 * (hadamardConst + 1) * Real.exp (-2 * (k : ℝ)) ≤
        (2 * (hadamardConst + 1)) / Real.exp (k : ℝ) := by
      rw [show -2 * (k : ℝ) = -(2 * (k : ℝ)) by ring, Real.exp_neg, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by linarith [hadamardConst_spec.1]) (Real.exp_pos _) h2k
    refine hdiv.trans ((div_le_iff₀ (Real.exp_pos _)).mpr ?_)
    linarith [hadamardConst_spec.1]
  have htail3 :
      Summable (fun n : ℕ => if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ∧
      ∑' n : ℕ, (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) ≤
        (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
    obtain ⟨hs3, h3⟩ := gallagher_prime_power_tail_le hk1 hr (by linarith) (by omega : 1 ≤ N₁)
    refine ⟨hs3, h3.trans ?_⟩
    have hN₁_half : (1 / 2 : ℝ) * Real.exp (Real.exp (-10) * (k : ℝ) / r) ≤ (N₁ : ℝ) := by
      have hlt := Nat.lt_floor_add_one (Real.exp (Real.exp (-10) * (k : ℝ) / r))
      have hexp_ge2 : (2 : ℝ) ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r) := by
        have h1 : (2 : ℝ) ≤ Real.exp (45 * L) := by
          linarith [Real.add_one_le_exp (45 * L)]
        exact h1.trans (Real.exp_le_exp.mpr harg1_ge)
      linarith
    have hN₁_rpow : (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * Real.exp (-10 * (k : ℝ)) := by
      have h1 : ((1 / 2 : ℝ) * Real.exp (Real.exp (-10) * (k : ℝ) / r)) ^ (-(1 / 4 : ℝ)) ≥
          (N₁ : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hN₁_half (by norm_num))
      have h2 : ((1 / 2 : ℝ) * Real.exp (Real.exp (-10) * (k : ℝ) / r)) ^ (-(1 / 4 : ℝ)) =
          (1 / 2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.exp (-10) / (4 * r)) * (k : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
        congr 2; ring
      have hhalf_le2 : (1 / 2 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 := by
        rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
        have h1' : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        rwa [Real.rpow_one] at h1'
      have hexp_ge10 : 10 ≤ Real.exp (-10) / (4 * r) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hexp_le : Real.exp (-(Real.exp (-10) / (4 * r)) * (k : ℝ)) ≤ Real.exp (-10 * (k : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
      calc (N₁ : ℝ) ^ (-(1 / 4 : ℝ))
          ≤ (1 / 2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.exp (-10) / (4 * r)) * (k : ℝ)) := by
            rw [← h2]; exact h1
        _ ≤ 2 * Real.exp (-10 * (k : ℝ)) :=
            mul_le_mul hhalf_le2 hexp_le (Real.exp_pos _).le (by norm_num)
    calc 256 * r * (N₁ : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ 256 * 1 * (2 * Real.exp (-10 * (k : ℝ))) :=
          mul_le_mul (by linarith) hN₁_rpow (by positivity) (by norm_num)
      _ = 512 * Real.exp (-6 * (k : ℝ)) * Real.exp (-4 * (k : ℝ)) := by
          have hexp10 : Real.exp (-10 * (k : ℝ)) = Real.exp (-6 * (k : ℝ)) * Real.exp (-4 * (k : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp10]; ring
      _ ≤ (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have h6k : Real.exp (k : ℝ) ≤ Real.exp (6 * (k : ℝ)) :=
            Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
          have hdiv : 512 * Real.exp (-6 * (k : ℝ)) ≤ 512 / Real.exp (k : ℝ) := by
            rw [show -6 * (k : ℝ) = -(6 * (k : ℝ)) by ring, Real.exp_neg, ← div_eq_mul_inv]
            exact div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) h6k
          refine hdiv.trans ((div_le_iff₀ (Real.exp_pos _)).mpr ?_)
          linarith [hadamardConst_spec.1]
  -- Split the full `tsum` into primes in `(N₁, N₂]` + the 3 tails!
  let f_term : ℕ → ℂ := fun n => (gallagherWeight k r n : ℂ) * c n * (n : ℂ) ^ (-(I * (γ₀ : ℂ)))
  have hf_norm : ∀ n : ℕ, ‖f_term n‖ ≤ gallagherWeight k r n := fun n => by
    dsimp only [f_term]
    by_cases hn0 : n = 0
    · simp [hn0, gallagherWeight]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gallagherWeight_nonneg k hr n),
        Complex.norm_natCast_cpow_of_pos hn1]
      simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, neg_zero, Real.rpow_zero, mul_one]
      exact mul_le_of_le_one_right (gallagherWeight_nonneg k hr n) (hc n)
  have hf_summ : Summable f_term := by
    have hsumm_w : Summable (fun n : ℕ => gallagherWeight k r n) := by
      have hdom : ∀ n : ℕ, gallagherWeight k r n ≤
          (if n ≤ N₂ then gallagherWeight k r n else 0) + (if N₂ < n then gallagherWeight k r n else 0) := fun n => by
        by_cases h : n ≤ N₂
        · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
        · rw [if_neg h, if_pos (not_le.mp h), zero_add]
      have hfin_s : Summable (fun n : ℕ => if n ≤ N₂ then gallagherWeight k r n else 0) :=
        summable_of_ne_finset_zero (s := Finset.range (N₂ + 1)) fun n hn =>
          if_neg (by simp only [Finset.mem_range] at hn; omega)
      exact Summable.of_nonneg_of_le (gallagherWeight_nonneg k hr) hdom (hfin_s.add htail2.1)
    exact Summable.of_norm_bounded hsumm_w hf_norm
  have htsum_split : ∑' n : ℕ, f_term n =
      (∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p) +
      (∑ n ∈ Finset.Icc 1 N₁, f_term n) +
      (∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n) +
      (∑' n : ℕ, if N₂ < n then f_term n else 0) := by
    have hfin_part : ∑ n ∈ Finset.range (N₂ + 1), f_term n =
        (∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p) +
        (∑ n ∈ Finset.Icc 1 N₁, f_term n) +
        (∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n) := by
      have h0 : f_term 0 = 0 := by simp [f_term, gallagherWeight]
      have hIcc_union : Finset.Icc 1 N₂ = Finset.Icc 1 N₁ ∪ Finset.Ioc N₁ N₂ := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]; omega
      have hIcc_disj : Disjoint (Finset.Icc 1 N₁) (Finset.Ioc N₁ N₂) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
      have hrange : Finset.range (N₂ + 1) = insert 0 (Finset.Icc 1 N₂) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      have h0not : (0 : ℕ) ∉ Finset.Icc 1 N₂ := by simp
      have hpr_split : ∑ n ∈ Finset.Ioc N₁ N₂, f_term n =
          (∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p) +
          (∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n) :=
        (Finset.sum_filter_add_sum_filter_not (Finset.Ioc N₁ N₂) Nat.Prime f_term).symm
      rw [hrange, Finset.sum_insert h0not, h0, zero_add, hIcc_union, Finset.sum_union hIcc_disj, hpr_split]
      ring
    have htail_eq : ∑' n : ℕ, f_term (n + (N₂ + 1)) = ∑' n : ℕ, if N₂ < n then f_term n else 0 := by
      have hs_tail : Summable (fun n : ℕ => if N₂ < n then f_term n else 0) :=
        Summable.of_norm_bounded htail2.1 fun n => by
          split_ifs; exact hf_norm n; simp
      rw [← hs_tail.sum_add_tsum_nat_add (N₂ + 1)]
      have hzero_init : ∑ n ∈ Finset.range (N₂ + 1), (if N₂ < n then f_term n else 0) = 0 :=
        Finset.sum_eq_zero fun n hn => if_neg (by simp only [Finset.mem_range] at hn; omega)
      rw [hzero_init, zero_add]
      refine tsum_congr fun n => ?_; rw [if_pos (by omega)]
    rw [← hf_summ.sum_add_tsum_nat_add (N₂ + 1), hfin_part, htail_eq]
  have hnorm_t1 : ‖∑ n ∈ Finset.Icc 1 N₁, f_term n‖ ≤ (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hf_norm n).trans htail1)
  have hnorm_t3 : ‖∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n‖ ≤
      (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hf_norm n).trans ?_)
    have hle_sum : ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), gallagherWeight k r n =
        ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime),
          (if N₁ < n ∧ ¬ n.Prime then gallagherWeight k r n else 0) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨hI, hnp⟩ := Finset.mem_filter.mp hn
      rw [if_pos ⟨(Finset.mem_Ioc.mp hI).1, hnp⟩]
    rw [hle_sum]
    exact (htail3.1.sum_le_tsum _ fun n _ => by
      split_ifs; exact gallagherWeight_nonneg k hr n; exact le_rfl).trans htail3.2
  have hnorm_t2 : ‖∑' n : ℕ, if N₂ < n then f_term n else 0‖ ≤ (1 / 64 : ℝ) * Real.exp (-4 * (k : ℝ)) := by
    have hs_t2 : Summable (fun n : ℕ => if N₂ < n then f_term n else 0) :=
      Summable.of_norm_bounded htail2.1 fun n => by split_ifs; exact hf_norm n; simp
    exact (norm_tsum_le_tsum_norm hs_t2.norm).trans
      ((Summable.tsum_le_tsum (fun n => by split_ifs; exact hf_norm n; simp) hs_t2.norm htail2.1).trans htail2.2)
  have htri_all : ‖∑' n : ℕ, f_term n‖ ≤
      ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p‖ +
      ‖∑ n ∈ Finset.Icc 1 N₁, f_term n‖ +
      ‖∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n‖ +
      ‖∑' n : ℕ, if N₂ < n then f_term n else 0‖ := by
    rw [htsum_split]
    have ha := norm_add_le
      ((∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p) + (∑ n ∈ Finset.Icc 1 N₁, f_term n) +
        (∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n))
      (∑' n : ℕ, if N₂ < n then f_term n else 0)
    have hb := norm_add_le
      ((∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p) + (∑ n ∈ Finset.Icc 1 N₁, f_term n))
      (∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => ¬ n.Prime), f_term n)
    have hc' := norm_add_le
      (∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p)
      (∑ n ∈ Finset.Icc 1 N₁, f_term n)
    linarith
  change (1 / 8 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤ ‖∑' n : ℕ, f_term n‖ at hfull_ge
  change (1 / 16 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤ ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, f_term p‖
  nlinarith [Real.exp_pos (-4 * (k : ℝ))]

/-- **Gallagher Prime Zero Detector for ANY Non-Principal Character `χ ≠ 1` (Primitive OR Imprimitive!)**:
Notice that for `p > N₁ ≥ D^40 ≥ m^40 > m`, `p` is automatically coprime to `m`, so `χ(p) = ψ(p)`! -/
theorem gallagher_prime_zero_detector_nonprincipal {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    {D : ℝ} (hD : 3 ≤ D) (hmD : (m : ℝ) ≤ D) {r : ℝ} (hr : 0 < r) (hr_lt : r < detectorDelta0)
    {γ₀ : ℝ} (hγD : (m : ℝ) * (|γ₀| + 2) ≤ 2 * D)
    {ρ_star : ℂ} (hρ0 : 0 < ρ_star.re) (hρ1 : ρ_star.re < 1)
    (hL0 : DirichletCharacter.LFunction χ ρ_star = 0)
    (hdist : ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ_star‖ < 3 * r) :
    let L := Real.log D
    let M₀ := ⌈8 * C_Z_const * (300 * r * L + 1)⌉₊
    let K := detectorCK * M₀
    ∃ k ∈ Finset.Icc K (K + M₀),
      let N₁ := ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
      let N₂ := ⌊Real.exp (30 * (k : ℝ) / r)⌋₊
      D ^ 40 ≤ (N₁ : ℝ) ∧ 2 ≤ N₁ ∧ N₁ ≤ N₂ ∧
      (1 / 16 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤
        ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
          (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (γ₀ : ℂ)))‖ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set f : ℕ := χ.conductor
  set ψ : DirichletCharacter ℂ f := χ.primitiveCharacter
  have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
  have hf_le_m : f ≤ m := Nat.le_of_dvd (NeZero.pos m) χ.conductor_dvd_level
  have hLψ0 : DirichletCharacter.LFunction ψ ρ_star = 0 :=
    (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ hρ0 (.inl hχ)).mp hL0
  have hc0 : DirichletCharacter.completedLFunction ψ ρ_star = 0 :=
    (Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ ρ_star).mpr
      ⟨hρ0, hρ1, hLψ0⟩
  obtain ⟨j_star, hj_eq⟩ :=
    (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprim hψ).exists_of_eq_zero
      (Stage6LFunctionOrder.differentiable_completedLFunction_prim hψ)
      (Stage6LFunctionOrder.completedLFunction_zero_ne_zero hprim hψ) hc0
  have hB_re : ∀ (d : ℝ) (F : Finset ℕ), 0 < d → d ≤ 1 →
      ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) -
        Stage8HadamardLFunction.completedLZeroSeq hprim hψ j)).re ≤ C_Z_const * (2 * Real.log D + 1 / d) := by
    intro d F hd hd1
    have h1 := sum_re_inv_sub_LZero_le hprim hψ hd hd1 γ₀ F
    have hlog_le : Real.log ((f : ℝ) * (|γ₀| + 2)) ≤ 2 * Real.log D := by
      have hf_pos : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr (NeZero.pos f)
      have harg : (f : ℝ) * (|γ₀| + 2) ≤ D ^ 2 := by
        have hfmR : (f : ℝ) ≤ (m : ℝ) := by exact_mod_cast hf_le_m
        have h2D : (f : ℝ) * (|γ₀| + 2) ≤ 2 * D :=
          (mul_le_mul_of_nonneg_right hfmR (by positivity)).trans hγD
        nlinarith
      calc Real.log ((f : ℝ) * (|γ₀| + 2)) ≤ Real.log (D ^ 2) := Real.log_le_log (by positivity) harg
        _ = 2 * Real.log D := by rw [Real.log_pow]; norm_num
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith [one_le_C_Z_const]))
  have hhigh : ∀ k : ℕ, 1 ≤ k →
      ‖(∑' n : ℕ, if n = 0 then (0 : ℂ) else
          ψ (n : ZMod f) * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) *
            (n : ℂ) ^ (-(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)))) +
        ∑' j : ℕ, (((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) -
          Stage8HadamardLFunction.completedLZeroSeq hprim hψ j) ^ (k + 1))⁻¹‖ ≤
      3 + ((300 * r) ^ (k + 1))⁻¹ := fun k hk =>
    (master_highDeriv_prim hprim hψ hk (by simp; linarith)).trans (by
      have : 0 ≤ ((300 * r) ^ (k + 1))⁻¹ := by positivity
      linarith)
  obtain ⟨k, hk_mem, hN₁_D40, hN₁_ge2, hN₁_le, hdet⟩ :=
    gallagher_prime_zero_detector_core hD hr hr_lt γ₀
      (Stage8HadamardLFunction.completedLZeroSeq hprim hψ)
      (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
      (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprim hψ)
      (fun n => ψ (n : ZMod f)) (fun n => ψ.norm_le_one _) hB_re hhigh j_star (hj_eq.symm ▸ hdist)
  refine ⟨k, hk_mem, hN₁_D40, hN₁_ge2, hN₁_le, ?_⟩
  -- Replace `ψ(p)` with `χ(p)` for every prime `p > N₁ ≥ D^40 ≥ m^40 > m`!
  have hsum_eq :
      ∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
        ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
        (gallagherWeight k r p : ℂ) * ψ (p : ZMod f) * (p : ℂ) ^ (-(I * (γ₀ : ℂ))) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
        ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
        (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (γ₀ : ℂ))) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpI, hpPr⟩ := Finset.mem_filter.mp hp
    have hp_gt_m : m < p := by
      have hm_le_D40 : (m : ℝ) ≤ D ^ 40 := hmD.trans (le_self_pow₀ (by linarith) (by norm_num))
      have hp_gt : (m : ℝ) < (p : ℝ) := lt_of_le_of_lt (hm_le_D40.trans hN₁_D40)
        (by exact_mod_cast (Finset.mem_Ioc.mp hpI).1)
      exact_mod_cast hp_gt
    have hcop : Nat.Coprime p m := hpPr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos m) hp_gt_m)
    have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hcop
    have hχ_eq : χ (p : ZMod m) = ψ (p : ZMod f) := by
      rw [← χ.changeLevel_primitiveCharacter]
      obtain ⟨u, hu_eq⟩ := hu
      rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd ψ χ.conductor_dvd_level u,
        hu_eq, ZMod.cast_natCast χ.conductor_dvd_level]
    rw [hχ_eq]
  rwa [← hsum_eq]

/-- **Gallagher Prime Zero Detector for Principal Character `χ = 1` (i.e. `riemannZeta`)**:
uses `c_zeta_zfr` inside `detectorDelta0` to guarantee `|γ₀| > 1 ≥ 300 * r` so the pole at `s = 1`
satisfies `‖((s₀ - 1)^(k+1))⁻¹‖ ≤ (300 * r)^(-(k+1))`! -/
theorem gallagher_prime_zero_detector_principal {m : ℕ} [NeZero m]
    {D : ℝ} (hD : 3 ≤ D) (hmD : (m : ℝ) ≤ D) {r : ℝ} (hr : 0 < r) (hr_lt : r < detectorDelta0)
    {γ₀ : ℝ} (hγD : |γ₀| + 2 ≤ 2 * D)
    {ρ_star : ℂ} (hρ0 : 0 < ρ_star.re) (hρ1 : ρ_star.re < 1)
    (hZ0 : riemannZeta ρ_star = 0)
    (hdist : ‖(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ_star‖ < 3 * r) :
    let L := Real.log D
    let M₀ := ⌈8 * C_Z_const * (300 * r * L + 1)⌉₊
    let K := detectorCK * M₀
    ∃ k ∈ Finset.Icc K (K + M₀),
      let N₁ := ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
      let N₂ := ⌊Real.exp (30 * (k : ℝ) / r)⌋₊
      D ^ 40 ≤ (N₁ : ℝ) ∧ 2 ≤ N₁ ∧ N₁ ≤ N₂ ∧
      (1 / 16 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤
        ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
          (gallagherWeight k r p : ℂ) * (1 : DirichletCharacter ℂ m) (p : ZMod m) *
            (p : ℂ) ^ (-(I * (γ₀ : ℂ)))‖ := by
  have hxi0 : Stage5StirlingPhragmen.xi ρ_star = 0 :=
    (Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero ρ_star).mpr ⟨hρ0, hρ1, hZ0⟩
  obtain ⟨j_star, hj_eq⟩ :=
    Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi.exists_of_eq_zero
      Stage5StirlingPhragmen.differentiable_xi (by simp) hxi0
  -- Show `|γ₀| ≥ 1 ≥ 300 * r` from `c_zeta_zfr` inside `detectorDelta0`!
  have hγ_ge1 : 1 ≤ |γ₀| := by
    have hre_sub : 1 + r - ρ_star.re < 3 * r := by
      have h1 : (((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ) - ρ_star).re = 1 + r - ρ_star.re := by simp
      have h2 := (le_abs_self _).trans (Complex.abs_re_le_norm ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ_star))
      rw [h1] at h2; linarith
    have hρ_re_gt : 1 - 2 * r < ρ_star.re := by linarith
    have hρ_im_gt2 : 2 < |ρ_star.im| := by
      by_contra hle; push Not at hle
      have hzfr := (c_zeta_zfr_spec.2 ρ_star hρ0 hρ1 hZ0).2
      have hlog_le : Real.log (|ρ_star.im| + 2) ≤ Real.log 4 :=
        Real.log_le_log (by linarith [abs_nonneg ρ_star.im]) (by linarith)
      have hc_div : c_zeta_zfr / Real.log 4 ≤ c_zeta_zfr / Real.log (|ρ_star.im| + 2) :=
        div_le_div_of_nonneg_left c_zeta_zfr_spec.1.le
          (Real.log_pos (by linarith [abs_nonneg ρ_star.im])) hlog_le
      have hr_c : r < c_zeta_zfr / (4 * Real.log 4) :=
        lt_of_lt_of_le hr_lt ((min_le_right _ _).trans (min_le_right _ _))
      have h2r : 2 * r < c_zeta_zfr / Real.log 4 := by
        have : c_zeta_zfr / (4 * Real.log 4) = (c_zeta_zfr / Real.log 4) / 4 := by ring
        have hpos : 0 < c_zeta_zfr / Real.log 4 := div_pos c_zeta_zfr_spec.1 (Real.log_pos (by norm_num))
        linarith
      linarith
    have him_diff : |γ₀ - ρ_star.im| < 3 * r := by
      have h1 : (((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ) - ρ_star).im = γ₀ - ρ_star.im := by simp
      have h2 := Complex.abs_im_le_norm ((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) - ρ_star)
      rw [h1] at h2; linarith
    have hr_small : 3 * r < 1 := by
      have := lt_of_lt_of_le hr_lt (min_le_left _ _); linarith
    have htri : |ρ_star.im| - |γ₀| ≤ |γ₀ - ρ_star.im| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub ρ_star.im γ₀
    linarith
  have hB_re : ∀ (d : ℝ) (F : Finset ℕ), 0 < d → d ≤ 1 →
      ∑ j ∈ F, (1 / ((((1 + d : ℝ) : ℂ) + I * (γ₀ : ℂ)) -
        Stage7HadamardXiProduct.xiZeroSeq j)).re ≤ C_Z_const * (2 * Real.log D + 1 / d) := by
    intro d F hd hd1
    have h1 := sum_re_inv_sub_xiZero_le hd hd1 γ₀ F
    have hlog_le : Real.log (|γ₀| + 2) ≤ 2 * Real.log D := by
      have harg : |γ₀| + 2 ≤ D ^ 2 := by nlinarith
      calc Real.log (|γ₀| + 2) ≤ Real.log (D ^ 2) := Real.log_le_log (by linarith [abs_nonneg γ₀]) harg
        _ = 2 * Real.log D := by rw [Real.log_pow]; norm_num
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith [one_le_C_Z_const]))
  have hhigh : ∀ k : ℕ, 1 ≤ k →
      ‖(∑' n : ℕ, if n = 0 then (0 : ℂ) else
          (1 : ℂ) * (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) *
            (n : ℂ) ^ (-(((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)))) +
        ∑' j : ℕ, (((((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) -
          Stage7HadamardXiProduct.xiZeroSeq j) ^ (k + 1))⁻¹‖ ≤
      3 + ((300 * r) ^ (k + 1))⁻¹ := by
    intro k hk
    have h1 := master_highDeriv_zeta hk (s := ((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)) (by simp; linarith)
    set s₀ : ℂ := ((1 + r : ℝ) : ℂ) + I * (γ₀ : ℂ)
    have hpole : ‖((s₀ - 1) ^ (k + 1))⁻¹‖ ≤ ((300 * r) ^ (k + 1))⁻¹ := by
      rw [norm_inv, norm_pow]
      have hge : 300 * r ≤ ‖s₀ - 1‖ := by
        have h1' : 300 * r ≤ 1 := by
          have := lt_of_lt_of_le hr_lt (min_le_left _ _); linarith
        have him : (s₀ - 1).im = γ₀ := by simp [s₀]
        exact h1'.trans (hγ_ge1.trans (by simpa [him] using Complex.abs_im_le_norm (s₀ - 1)))
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hge (k + 1))
    simp only [one_mul]
    set X : ℂ := (∑' n : ℕ, if n = 0 then (0 : ℂ) else
        (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀)) +
        ∑' j : ℕ, ((s₀ - Stage7HadamardXiProduct.xiZeroSeq j) ^ (k + 1))⁻¹
    have hrew : X = (X - ((s₀ - 1) ^ (k + 1))⁻¹) + ((s₀ - 1) ^ (k + 1))⁻¹ := by ring
    have hX_sub : ‖X - ((s₀ - 1) ^ (k + 1))⁻¹‖ ≤ 3 := by
      have : X - ((s₀ - 1) ^ (k + 1))⁻¹ =
          (∑' n : ℕ, if n = 0 then (0 : ℂ) else
            (Λ n : ℂ) * (((Real.log (n : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) * (n : ℂ) ^ (-s₀)) -
          ((s₀ - 1) ^ (k + 1))⁻¹ +
          ∑' j : ℕ, ((s₀ - Stage7HadamardXiProduct.xiZeroSeq j) ^ (k + 1))⁻¹ := by dsimp only [X]; ring
      rw [this]; exact h1
    rw [hrew]; exact (norm_add_le _ _).trans (add_le_add hX_sub hpole)
  obtain ⟨k, hk_mem, hN₁_D40, hN₁_ge2, hN₁_le, hdet⟩ :=
    gallagher_prime_zero_detector_core hD hr hr_lt γ₀
      Stage7HadamardXiProduct.xiZeroSeq Stage7HadamardXiProduct.xiZeroSeq_strip
      Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq
      (fun _ => (1 : ℂ)) (fun _ => by simp) hB_re hhigh j_star (hj_eq.symm ▸ hdist)
  refine ⟨k, hk_mem, hN₁_D40, hN₁_ge2, hN₁_le, ?_⟩
  have hsum_eq :
      ∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
        ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
        (gallagherWeight k r p : ℂ) * (1 : ℂ) * (p : ℂ) ^ (-(I * (γ₀ : ℂ))) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
        ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
        (gallagherWeight k r p : ℂ) * (1 : DirichletCharacter ℂ m) (p : ZMod m) *
          (p : ℂ) ^ (-(I * (γ₀ : ℂ))) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpI, hpPr⟩ := Finset.mem_filter.mp hp
    have hp_gt_m : m < p := by
      have hm_le_D40 : (m : ℝ) ≤ D ^ 40 := hmD.trans (le_self_pow₀ (by linarith) (by norm_num))
      have hp_gt : (m : ℝ) < (p : ℝ) := lt_of_le_of_lt (hm_le_D40.trans hN₁_D40)
        (by exact_mod_cast (Finset.mem_Ioc.mp hpI).1)
      exact_mod_cast hp_gt
    have hcop : Nat.Coprime p m := hpPr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos m) hp_gt_m)
    have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hcop
    rw [MulChar.one_apply hu]
  rwa [← hsum_eq]

/-! ## Section 4: Multiplicity-Counted Zero Box Counts & Unconditional Gallagher Log-Free Zero-Density Theorems -/

/-! ### Section 4a: Exact Analytic Multiplicity & `zerosOfLInBox` -/

/-- Multiplying an analytic function by a locally nonvanishing analytic function preserves
exact `analyticOrderNatAt`. -/
private lemma analyticOrderNatAt_mul_of_ne_zero {f g : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w) (hgw : g w ≠ 0) :
    analyticOrderNatAt (fun z => f z * g z) w = analyticOrderNatAt f w := by
  by_cases htop : analyticOrderAt f w = ⊤
  · have hfg_top : analyticOrderAt (fun z => f z * g z) w = ⊤ := by
      rw [analyticOrderAt_eq_top] at htop ⊢
      filter_upwards [htop] with z hz; simp [hz]
    simp only [analyticOrderNatAt, htop, hfg_top]
  · obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := hf.analyticOrderAt_ne_top.mp htop
    have hfg_an : AnalyticAt ℂ (fun z => f z * g z) w := hf.mul hg
    have hfg_eq : (fun z => f z * g z) =ᶠ[𝓝 w]
        fun z => (z - w) ^ analyticOrderNatAt f w • (h z * g z) := by
      filter_upwards [hh_eq] with z hz
      simp only [smul_eq_mul] at hz ⊢
      rw [hz]; ring
    have hord : analyticOrderAt (fun z => f z * g z) w = (analyticOrderNatAt f w : ℕ∞) :=
      hfg_an.analyticOrderAt_eq_natCast.mpr ⟨fun z => h z * g z, hh_an.mul hg, mul_ne_zero hh_ne hgw, hfg_eq⟩
    simp only [analyticOrderNatAt, hord, ENat.toNat_natCast]

/-- On `0 < ρ.re < 1`, the analytic zero multiplicity of `DirichletCharacter.LFunction χ` equals
the analytic zero multiplicity of `DirichletCharacter.completedLFunction χ.primitiveCharacter`
(for `χ ≠ 1`) or `Stage5StirlingPhragmen.xi` (for `χ = 1`). -/
private lemma analyticOrderNatAt_LFunction_eq_nonprincipal {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) {ρ : ℂ} (h0 : 0 < ρ.re) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
  have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
  have hopen : IsOpen {z : ℂ | 0 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  -- Step 1: `LFunction χ =ᶠ[𝓝 ρ] fun z => LFunction ψ z * eulerProd z`
  let eulerProd : ℂ → ℂ := fun z => ∏ p ∈ m.primeFactors, (1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))
  have heuler_an : AnalyticAt ℂ eulerProd ρ := by
    have hdiff : Differentiable ℂ eulerProd := by
      have hterm : ∀ p ∈ m.primeFactors,
          Differentiable ℂ (fun z : ℂ => 1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)) := fun p hp => by
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
        have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
        have hrew : (fun z : ℂ => (p : ℂ) ^ (-z)) = fun z : ℂ => Complex.exp (-(Real.log (p : ℝ) : ℂ) * z) := by
          funext z; rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_natCast,
            Complex.ofReal_log hp_pos.le]; congr 1; ring
        have hd : Differentiable ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) := by rw [hrew]; fun_prop
        exact (differentiable_const 1).sub ((differentiable_const _).mul hd)
      exact Differentiable.fun_finsetProd hterm
    exact hdiff.differentiableOn.analyticAt Filter.univ_mem
  have heuler_ne : eulerProd ρ ≠ 0 := RHDirect.eulerFactorProd_ne_zero_of_re_pos (N := m) ψ h0
  have hLψ_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) ρ :=
    (DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticAt Filter.univ_mem
  have hev1 : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ] fun z => DirichletCharacter.LFunction ψ z * eulerProd z := by
    filter_upwards [hopen.mem_nhds h0] with z _
    have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (s := z) (.inl hψ)
    rw [χ.changeLevel_primitiveCharacter] at hcl
    rw [hcl, mul_comm]
  have hord1 : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ := by
    have h1 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ =
        analyticOrderAt (fun z => DirichletCharacter.LFunction ψ z * eulerProd z) ρ :=
      analyticOrderAt_congr hev1
    simp only [analyticOrderNatAt, h1]
    exact analyticOrderNatAt_mul_of_ne_zero hLψ_an heuler_an heuler_ne
  -- Step 2: `completedLFunction ψ =ᶠ[𝓝 ρ] fun z => LFunction ψ z * gammaFactor ψ z`
  have hgam_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor ψ) ρ := by
    have hGamℝ_diff : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := by
      intro z hz
      change 0 < z.re at hz
      have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hne_neg : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := fun n h => by
        have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hrew : Complex.Gammaℝ = fun w => Complex.exp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) := by
        funext w; rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
      rw [hrew]
      have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-w / 2))) z := by fun_prop
      have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
        (Complex.differentiableAt_Gamma (z / 2) hne_neg).comp z (differentiableAt_id.div_const 2)
      exact (h1.mul h2).differentiableWithinAt
    rcases ψ.even_or_odd with he | ho
    · have hfun : DirichletCharacter.gammaFactor ψ = Complex.Gammaℝ := funext he.gammaFactor_def
      rw [hfun]; exact hGamℝ_diff.analyticAt (hopen.mem_nhds h0)
    · have hfun : DirichletCharacter.gammaFactor ψ = fun z => Complex.Gammaℝ (z + 1) := funext ho.gammaFactor_def
      rw [hfun]
      have hG1 : AnalyticAt ℂ Complex.Gammaℝ ((fun z : ℂ => z + 1) ρ) :=
        hGamℝ_diff.analyticAt (hopen.mem_nhds (by simp; linarith))
      exact AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun z : ℂ => z + 1) hG1 (analyticAt_id.add analyticAt_const)
  have hgam_ne : DirichletCharacter.gammaFactor ψ ρ ≠ 0 :=
    Stage6LFunctionOrder.gammaFactor_ne_zero_of_re_pos ψ h0
  have hev2 : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 ρ]
      fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z := by
    filter_upwards [hopen.mem_nhds h0] with z hz
    exact Stage6LFunctionOrder.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ hz
  have hord2 : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ := by
    have h1 : analyticOrderAt (DirichletCharacter.completedLFunction ψ) ρ =
        analyticOrderAt (fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z) ρ :=
      analyticOrderAt_congr hev2
    simp only [analyticOrderNatAt, h1]
    exact analyticOrderNatAt_mul_of_ne_zero hLψ_an hgam_an hgam_ne
  exact hord1.trans hord2.symm

private lemma analyticOrderNatAt_LFunction_eq_principal {m : ℕ} [NeZero m]
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m)) ρ =
      analyticOrderNatAt Stage5StirlingPhragmen.xi ρ := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).inter
      (Complex.continuous_re.isOpen_preimage _ isOpen_Iio)
  have hmem : ρ ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := ⟨h0, h1⟩
  have hZ_diff : DifferentiableOn ℂ riemannZeta {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    fun z hz => (differentiableAt_riemannZeta (fun h => by
      have h2 : z.re < 1 := hz.2; rw [h, Complex.one_re] at h2; linarith)).differentiableWithinAt
  have hZ_an : AnalyticAt ℂ riemannZeta ρ := hZ_diff.analyticAt (hopen.mem_nhds hmem)
  -- Step 1: `LFunction 1 =ᶠ[𝓝 ρ] fun z => riemannZeta z * eulerProd z`
  let eulerProd : ℂ → ℂ := fun z => ∏ p ∈ m.primeFactors, (1 - (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-z))
  have heuler_an : AnalyticAt ℂ eulerProd ρ := by
    have hdiff : Differentiable ℂ eulerProd := by
      have hterm : ∀ p ∈ m.primeFactors,
          Differentiable ℂ (fun z : ℂ => 1 - (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-z)) := fun p hp => by
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
        have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
        have hrew : (fun z : ℂ => (p : ℂ) ^ (-z)) = fun z : ℂ => Complex.exp (-(Real.log (p : ℝ) : ℂ) * z) := by
          funext z; rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_natCast,
            Complex.ofReal_log hp_pos.le]; congr 1; ring
        have hd : Differentiable ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) := by rw [hrew]; fun_prop
        exact (differentiable_const 1).sub ((differentiable_const _).mul hd)
      exact Differentiable.fun_finsetProd hterm
    exact hdiff.differentiableOn.analyticAt Filter.univ_mem
  have heuler_ne : eulerProd ρ ≠ 0 :=
    RHDirect.eulerFactorProd_ne_zero_of_re_pos (N := m) (1 : DirichletCharacter ℂ 1) h0
  have hev1 : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m) =ᶠ[𝓝 ρ]
      fun z => riemannZeta z * eulerProd z := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz; linarith [hz.2]
    have hcl := DirichletCharacter.LFunction_changeLevel m.one_dvd (1 : DirichletCharacter ℂ 1) (s := z) (.inr hz1)
    rw [map_one, DirichletCharacter.LFunction_modOne_eq] at hcl
    rw [hcl, mul_comm]
  have hord1 : analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m)) ρ =
      analyticOrderNatAt riemannZeta ρ := by
    have h := analyticOrderAt_congr hev1
    simp only [analyticOrderNatAt, h]
    exact analyticOrderNatAt_mul_of_ne_zero hZ_an heuler_an heuler_ne
  -- Step 2: `xi =ᶠ[𝓝 ρ] fun z => riemannZeta z * (z * (z - 1) * Gammaℝ z)`
  let pref : ℂ → ℂ := fun z => z * (z - 1) * Complex.Gammaℝ z
  have hpref_an : AnalyticAt ℂ pref ρ := by
    have hGamℝ_diff : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := by
      intro z hz; change 0 < z.re at hz
      have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hne_neg : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := fun n h => by
        have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hrew : Complex.Gammaℝ = fun w => Complex.exp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) := by
        funext w; rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
      rw [hrew]
      have h1' : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-w / 2))) z := by fun_prop
      have h2' : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
        (Complex.differentiableAt_Gamma (z / 2) hne_neg).comp z (differentiableAt_id.div_const 2)
      exact (h1'.mul h2').differentiableWithinAt
    have hG_an := hGamℝ_diff.analyticAt ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds h0)
    exact (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hG_an
  have hpref_ne : pref ρ ≠ 0 := by
    dsimp only [pref]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.Gammaℝ_ne_zero_of_re_pos h0)
    · intro h; rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
    · exact sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hev2 : Stage5StirlingPhragmen.xi =ᶠ[𝓝 ρ] fun z => riemannZeta z * pref z := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; linarith [hz.1]
    have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz; linarith [hz.2]
    rw [Stage5StirlingPhragmen.xi_eq_mul_Gammaℝ_mul_riemannZeta hz0 hz1 (Complex.Gammaℝ_ne_zero_of_re_pos hz.1)]
    dsimp only [pref]; ring
  have hord2 : analyticOrderNatAt Stage5StirlingPhragmen.xi ρ = analyticOrderNatAt riemannZeta ρ := by
    have h := analyticOrderAt_congr hev2
    simp only [analyticOrderNatAt, h]
    exact analyticOrderNatAt_mul_of_ne_zero hZ_an hpref_an hpref_ne
  exact hord1.trans hord2.symm

/-- Finiteness of the set of critical-strip zeros of `DirichletCharacter.LFunction χ` in the box
`0 < ρ.re`, `σ ≤ ρ.re < 1`, `|ρ.im| ≤ T`. -/
theorem finite_LFunction_zeros_in_box {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (σ T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}.Finite := by
  by_cases hχ : χ = 1
  · subst hχ
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m) ρ = 0} ⊆
        {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ max T 0} := by
      intro ρ ⟨h0, _, h1, him, hL0⟩
      have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
      exact ⟨h0, h1, (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos m h0 hρ1).mp hL0,
        him.trans (le_max_left T 0)⟩
    exact (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height (max T 0)).subset hsub
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
    have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
    have htend := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq
      (fun j h0 => by
        have := (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ j).1
        rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this)
      (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprim hψ)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually (Filter.eventually_ge_atTop (max T 0 + 2)))
    refine ((Set.finite_lt_nat N).image (Stage8HadamardLFunction.completedLZeroSeq hprim hψ)).subset ?_
    intro ρ ⟨h0, _, h1, him, hL0⟩
    have hLψ0 : DirichletCharacter.LFunction ψ ρ = 0 :=
      (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ)).mp hL0
    have hc0 : DirichletCharacter.completedLFunction ψ ρ = 0 :=
      (Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ ρ).mpr
        ⟨h0, h1, hLψ0⟩
    obtain ⟨j, rfl⟩ :=
      (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprim hψ).exists_of_eq_zero
        (Stage6LFunctionOrder.differentiable_completedLFunction_prim hψ)
        (Stage6LFunctionOrder.completedLFunction_zero_ne_zero hprim hψ) hc0
    refine ⟨j, ?_, rfl⟩
    change j < N
    by_contra hlt; have hge : N ≤ j := not_lt.mp hlt
    have hnorm_ge := hN j hge
    have hnorm_le : ‖Stage8HadamardLFunction.completedLZeroSeq hprim hψ j‖ ≤ max T 0 + 1 := by
      have htri := Complex.norm_le_abs_re_add_abs_im (Stage8HadamardLFunction.completedLZeroSeq hprim hψ j)
      rw [abs_of_pos h0] at htri
      linarith [le_max_left T 0]
    linarith

/-- **Multiplicity-Counted Zero Multiset of `DirichletCharacter.LFunction χ` in the Box
`σ ≤ ρ.re < 1, |ρ.im| ≤ T` (with `0 < ρ.re`)**:
each zero `ρ` appears with its exact analytic multiplicity
`analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ`. -/
noncomputable def zerosOfLInBox {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (σ T : ℝ) : Multiset ℂ :=
  (finite_LFunction_zeros_in_box χ σ T).toFinset.val.bind
    fun ρ => Multiset.replicate (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ρ

/-- **Total Multiplicity-Counted Zero Count Across All Characters mod `m`**:
`dirichletZeroBoxCount m σ T = ∑_{χ mod m} N(σ, T, χ)`. -/
noncomputable def dirichletZeroBoxCount (m : ℕ) [NeZero m] (σ T : ℝ) : ℕ :=
  ∑ χ : DirichletCharacter ℂ m, (zerosOfLInBox χ σ T).card

open Classical in
/-- **Total Multiplicity-Counted Zero Count Across All Primitive Characters of Modulus `1 ≤ q ≤ Q`**:
`primitiveZeroBoxCount Q σ T = ∑_{q ≤ Q} ∑*_{χ mod q} N(σ, T, χ)`. -/
noncomputable def primitiveZeroBoxCount (Q : ℕ) (σ T : ℝ) : ℕ :=
  ∑ k ∈ Finset.range Q,
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
      (zerosOfLInBox χ σ T).card

/-- Cardinality of `zerosOfLInBox χ σ T` equals `∑ ρ ∈ Z_box, analyticOrderNatAt (LFunction χ) ρ`. -/
theorem zerosOfLInBox_card_eq_sum {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (σ T : ℝ) :
    (zerosOfLInBox χ σ T).card =
      ∑ ρ ∈ (finite_LFunction_zeros_in_box χ σ T).toFinset,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  unfold zerosOfLInBox
  rw [Multiset.card_bind]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun ρ _ => Multiset.card_replicate _ _)

/-- At `σ = 1`, the box `1 ≤ ρ.re < 1` is empty, so `(zerosOfLInBox χ 1 T).card = 0`. -/
private lemma zerosOfLInBox_card_one {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (T : ℝ) :
    (zerosOfLInBox χ 1 T).card = 0 := by
  rw [zerosOfLInBox_card_eq_sum]
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  have hmem := (finite_LFunction_zeros_in_box χ 1 T).mem_toFinset.mp hρ
  linarith [hmem.2.1, hmem.2.2.1]

/-- Exact bijective match between `(zerosOfLInBox χ σ T).card` and the cardinality of the index finset
`{j : ℕ | σ ≤ (ρ_seq j).re ∧ (ρ_seq j).re < 1 ∧ |(ρ_seq j).im| ≤ T}`! -/
private lemma zerosOfLInBox_card_eq_index_finset {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    {σ T : ℝ} (_hσ : 0 < σ) (f_ent : ℂ → ℂ) (ρ_seq : ℕ → ℂ)
    (hmult : Stage7HadamardXiProduct.IsMultiplicityZeroSeq f_ent ρ_seq)
    (hstrip : ∀ j : ℕ, 0 < (ρ_seq j).re ∧ (ρ_seq j).re < 1)
    (hsum : Summable (fun j : ℕ => (‖ρ_seq j‖ ^ 2)⁻¹))
    (hiff : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → (DirichletCharacter.LFunction χ ρ = 0 ↔ f_ent ρ = 0))
    (hord : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = analyticOrderNatAt f_ent ρ) :
    ∃ F : Finset ℕ,
      (∀ j : ℕ, j ∈ F ↔ σ ≤ (ρ_seq j).re ∧ (ρ_seq j).re < 1 ∧ |(ρ_seq j).im| ≤ T) ∧
      (zerosOfLInBox χ σ T).card = F.card := by
  classical
  have hF_fin : {j : ℕ | σ ≤ (ρ_seq j).re ∧ (ρ_seq j).re < 1 ∧ |(ρ_seq j).im| ≤ T}.Finite := by
    have htend := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq hmult.1 hsum
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually (Filter.eventually_ge_atTop (max T 0 + 2)))
    refine (Set.finite_lt_nat N).subset fun j hj => ?_
    change j < N
    by_contra hlt; have hge : N ≤ j := not_lt.mp hlt
    have hnorm_ge := hN j hge
    have hnorm_le : ‖ρ_seq j‖ ≤ max T 0 + 1 := by
      have htri := Complex.norm_le_abs_re_add_abs_im (ρ_seq j)
      rw [abs_of_pos (hstrip j).1] at htri
      linarith [hj.2.1, hj.2.2, le_max_left T 0]
    linarith
  set F : Finset ℕ := hF_fin.toFinset
  have hF_mem : ∀ j : ℕ, j ∈ F ↔ σ ≤ (ρ_seq j).re ∧ (ρ_seq j).re < 1 ∧ |(ρ_seq j).im| ≤ T :=
    fun j => hF_fin.mem_toFinset
  refine ⟨F, hF_mem, ?_⟩
  rw [zerosOfLInBox_card_eq_sum]
  set Zbox : Finset ℂ := (finite_LFunction_zeros_in_box χ σ T).toFinset
  have hZbox_mem : ∀ ρ : ℂ, ρ ∈ Zbox ↔
      0 < ρ.re ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0 :=
    fun ρ => (finite_LFunction_zeros_in_box χ σ T).mem_toFinset
  have hpart : F = Zbox.biUnion (fun ρ => F.filter fun j => ρ_seq j = ρ) := by
    ext j; simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hj
      obtain ⟨hσj, h1j, himj⟩ := (hF_mem j).mp hj
      have h0j : 0 < (ρ_seq j).re := (hstrip j).1
      have hLz : DirichletCharacter.LFunction χ (ρ_seq j) = 0 :=
        (hiff (ρ_seq j) h0j h1j).mpr (hmult.apply_eq_zero j)
      exact ⟨ρ_seq j, (hZbox_mem _).mpr ⟨h0j, hσj, h1j, himj, hLz⟩, hj, rfl⟩
    · rintro ⟨_, _, hj, _⟩; exact hj
  have hdisj : Set.PairwiseDisjoint (Zbox : Set ℂ) (fun ρ => F.filter fun j => ρ_seq j = ρ) := by
    intro ρ₁ _ ρ₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]; intro j h1 h2
    exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  conv_rhs => rw [hpart, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨h0, hσρ, h1, him, _⟩ := (hZbox_mem ρ).mp hρ
  rw [hord ρ h0 h1]
  symm
  refine (hmult.2 ρ).2 (F.filter fun j => ρ_seq j = ρ) fun j => ?_
  simp only [Finset.mem_filter, hF_mem]
  constructor
  · exact fun h => h.2
  · intro heq; rw [heq]; exact ⟨⟨hσρ, h1, him⟩, rfl⟩

/-! ### Section 4b: Greedy `r`-Well-Spaced Thinning & Phase-Shifted Prime-Sum Sobolev Bound -/

/-- **Greedy `r`-Well-Spaced Thinning Lemma**:
for any `r > 0` and finite set `Y : Finset ℝ`, there exists `S ⊆ Y` that is `r`-well-spaced
(`t₁ ≠ t₂ → r ≤ |t₁ - t₂|`) and covers `Y` within radius `r` (`∀ y ∈ Y, ∃ t ∈ S, |y - t| < r`). -/
private lemma greedy_well_spaced_thinning {r : ℝ} (hr : 0 < r) (Y : Finset ℝ) :
    ∃ S : Finset ℝ, S ⊆ Y ∧
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → r ≤ |t₁ - t₂|) ∧
      (∀ y ∈ Y, ∃ t ∈ S, |y - t| < r) := by
  classical
  induction hcard : Y.card using Nat.strong_induction_on generalizing Y with
  | h n ih =>
    by_cases hY : Y = ∅
    · subst hY; exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · obtain ⟨y₀, hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hY
      set Y' : Finset ℝ := Y.filter (fun y => r ≤ |y - y₀|)
      have hlt : Y'.card < n := by
        rw [← hcard]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ Y, ?_⟩)
        intro heq
        have hmem : y₀ ∈ Y' := heq ▸ hy₀
        have hsep := (Finset.mem_filter.mp hmem).2
        rw [sub_self, abs_zero] at hsep; linarith
      obtain ⟨S', hS'_sub, hS'_ws, hS'_cov⟩ := ih Y'.card hlt Y' rfl
      refine ⟨insert y₀ S', Finset.insert_subset hy₀ (hS'_sub.trans (Finset.filter_subset _ Y)), ?_, ?_⟩
      · intro t₁ ht₁ t₂ ht₂ hne
        rcases Finset.mem_insert.mp ht₁ with rfl | ht₁'
        · rcases Finset.mem_insert.mp ht₂ with rfl | ht₂'
          · exact absurd rfl hne
          · rw [abs_sub_comm]; exact (Finset.mem_filter.mp (hS'_sub ht₂')).2
        · rcases Finset.mem_insert.mp ht₂ with rfl | ht₂'
          · exact (Finset.mem_filter.mp (hS'_sub ht₁')).2
          · exact hS'_ws t₁ ht₁' t₂ ht₂' hne
      · intro y hy
        by_cases hclose : |y - y₀| < r
        · exact ⟨y₀, Finset.mem_insert_self _ _, hclose⟩
        · have hy' : y ∈ Y' := Finset.mem_filter.mpr ⟨hy, not_lt.mp hclose⟩
          obtain ⟨t, ht, hdist⟩ := hS'_cov y hy'
          exact ⟨t, Finset.mem_insert_of_mem ht, hdist⟩

/-- Mertens constant extracted from `Stage8MertensTheorems.mertens_first_theorem`. -/
private noncomputable def mertensC : ℝ :=
  Classical.choose Stage8MertensTheorems.mertens_first_theorem

private lemma mertensC_spec :
    0 < mertensC ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) - Real.log x| ≤ mertensC :=
  Classical.choose_spec Stage8MertensTheorems.mertens_first_theorem

/-- Prime reciprocal log sum on `(N₁, N₂]` bounded via `Stage8MertensTheorems.mertens_first_theorem`. -/
private lemma sum_primes_Ioc_log_div_le {N₁ N₂ : ℕ} (hN₁ : 2 ≤ N₁) (hle : N₁ ≤ N₂) :
    ∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (N₂ : ℝ) - Real.log (N₁ : ℝ) + 2 * mertensC := by
  have h1 := mertensC_spec.2 (N₁ : ℝ) (by exact_mod_cast hN₁)
  have h2 := mertensC_spec.2 (N₂ : ℝ) (by exact_mod_cast (hN₁.trans hle))
  rw [Nat.floor_natCast] at h1 h2
  have hunion : (Finset.Icc 1 N₂).filter Nat.Prime =
      (Finset.Icc 1 N₁).filter Nat.Prime ∪ (Finset.Ioc N₁ N₂).filter Nat.Prime := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    by_cases hp : p.Prime <;> simp [hp]; omega
  have hdisj : Disjoint ((Finset.Icc 1 N₁).filter Nat.Prime) ((Finset.Ioc N₁ N₂).filter Nat.Prime) := by
    rw [Finset.disjoint_left]; intro p h1' h2'
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at h1' h2'; omega
  have hsplit : ∑ p ∈ (Finset.Icc 1 N₂).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) =
      (∑ p ∈ (Finset.Icc 1 N₁).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) +
      (∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) := by
    rw [hunion, Finset.sum_union hdisj]
  have h1' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).2
  linarith

/-- Per-character phase-shifted Sobolev inequality for prime sums on `(N₁, N₂]` at spacing `r`:
for `P_k = (Ioc N₁ N₂).filter Nat.Prime` (`2 ≤ N₁ ≤ N₂`), `T ≥ 1`, `0 < r < 1`, and ANY `r`-well-spaced
`S ⊆ [-T, T]`, setting `T' = T + 1`:
`∑ t ∈ S, ‖∑ p ∈ P_k, b p * χ p * p^(-I*t)‖² ≤`
`(2 / r) * ∫_{-T'}^{T'} ‖∑ p ∈ P_k, b p * χ p * p^(-I*t)‖² dt +`
`r * ∫_{-T'}^{T'} ‖∑ p ∈ P_k, ((-I * log(p / N₁)) * b p) * χ p * p^(-I*t)‖² dt`. -/
private lemma prime_sum_sobolev_char {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    {N₁ N₂ : ℕ} (hN₁ : 2 ≤ N₁) {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) (hr1 : r < 1)
    (b : ℕ → ℂ) (S : Finset ℝ) (hS_bound : ∀ t ∈ S, |t| ≤ T)
    (hS_ws : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → r ≤ |t₁ - t₂|) :
    let P := (Finset.Ioc N₁ N₂).filter Nat.Prime
    ∑ t ∈ S, ‖∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
      ((2 / r) * ∫ t in (-(T + 1))..(T + 1),
        ‖∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2) +
      (r * ∫ t in (-(T + 1))..(T + 1),
        ‖∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * b p) * χ (p : ZMod m) *
          (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2) := by
  intro P
  have hN₁_pos : (0 : ℝ) < (N₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN₁C : (N₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let F : ℝ → ℂ := fun t => (N₁ : ℂ) ^ (I * (t : ℂ)) *
    ∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))
  let F' : ℝ → ℂ := fun t => (N₁ : ℂ) ^ (I * (t : ℂ)) *
    ∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * b p) * χ (p : ZMod m) *
      (p : ℂ) ^ (-(I * (t : ℂ)))
  have hnorm_N₁ : ∀ t : ℝ, ‖(N₁ : ℂ) ^ (I * (t : ℂ))‖ = 1 := fun t => by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, Real.rpow_zero]
  have hnorm_F : ∀ t : ℝ, ‖F t‖ = ‖∑ p ∈ P, b p * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ := fun t => by
    dsimp only [F]; rw [norm_mul, hnorm_N₁ t, one_mul]
  have hnorm_F' : ∀ t : ℝ, ‖F' t‖ =
      ‖∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * b p) * χ (p : ZMod m) *
        (p : ℂ) ^ (-(I * (t : ℂ)))‖ := fun t => by
    dsimp only [F']; rw [norm_mul, hnorm_N₁ t, one_mul]
  have hF_deriv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have hF_rew : F = fun x : ℝ => ∑ p ∈ P, (b p * χ (p : ZMod m)) *
        Complex.exp (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ) * (x : ℂ)) := by
      funext x; dsimp only [F]; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos
      have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
      have hprod : (N₁ : ℂ) ^ (I * (x : ℂ)) * (p : ℂ) ^ (-(I * (x : ℂ))) =
          Complex.exp (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ) * (x : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hN₁C, Complex.cpow_def_of_ne_zero hpC, ← Complex.exp_add,
          ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_log hN₁_pos.le,
          ← Complex.ofReal_log hp_pos.le, Real.log_div hp_pos.ne' hN₁_pos.ne']
        congr 1; push_cast; ring
      calc (N₁ : ℂ) ^ (I * (x : ℂ)) * (b p * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (x : ℂ))))
          = (b p * χ (p : ZMod m)) * ((N₁ : ℂ) ^ (I * (x : ℂ)) * (p : ℂ) ^ (-(I * (x : ℂ)))) := by ring
        _ = _ := by rw [hprod]
    have hF'_rew : F' t = ∑ p ∈ P, (b p * χ (p : ZMod m)) *
        ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) *
          Complex.exp (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ) * (t : ℂ))) := by
      dsimp only [F']; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos
      have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
      have hprod : (N₁ : ℂ) ^ (I * (t : ℂ)) * (p : ℂ) ^ (-(I * (t : ℂ))) =
          Complex.exp (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ) * (t : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hN₁C, Complex.cpow_def_of_ne_zero hpC, ← Complex.exp_add,
          ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_log hN₁_pos.le,
          ← Complex.ofReal_log hp_pos.le, Real.log_div hp_pos.ne' hN₁_pos.ne']
        congr 1; push_cast; ring
      calc (N₁ : ℂ) ^ (I * (t : ℂ)) * (((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * b p) *
            χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ))))
          = (b p * χ (p : ZMod m)) * ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) *
              ((N₁ : ℂ) ^ (I * (t : ℂ)) * (p : ℂ) ^ (-(I * (t : ℂ))))) := by ring
        _ = _ := by rw [hprod]
    rw [hF_rew, hF'_rew]
    refine HasDerivAt.fun_sum fun p _ => ?_
    have hlin : HasDerivAt (fun x : ℝ => -I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ) * (x : ℂ))
        (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ))
    simpa [mul_comm] using (hlin.cexp.const_mul (b p * χ (p : ZMod m)))
  have hF'_cont : Continuous F' := by
    dsimp only [F']
    have hN₁_cont : Continuous (fun t : ℝ => (N₁ : ℂ) ^ (I * (t : ℂ))) := by
      have hrew : (fun t : ℝ => (N₁ : ℂ) ^ (I * (t : ℂ))) =
          fun t : ℝ => Complex.exp (Complex.log (N₁ : ℂ) * (I * (t : ℂ))) :=
        funext fun t => Complex.cpow_def_of_ne_zero hN₁C _
      rw [hrew]; fun_prop
    refine hN₁_cont.mul (continuous_finsetSum P fun p hp => ?_)
    have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
    have hrew : (fun t : ℝ => (p : ℂ) ^ (-(I * (t : ℂ)))) =
        fun t : ℝ => Complex.exp (Complex.log (p : ℂ) * (-(I * (t : ℂ)))) :=
      funext fun t => Complex.cpow_def_of_ne_zero hpC _
    refine continuous_const.mul ?_; rw [hrew]; fun_prop
  have hF_cont : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF_deriv t).continuousAt
  have hsob := gallagher_sobolev_mean_value_weighted S id (S := F) (S' := F') (T := T) (δ := r) (α := r⁻¹)
    (by linarith) hr (by positivity) hS_bound hS_ws hF_deriv hF'_cont
  have hwid : ∀ g : ℝ → ℝ, Continuous g → (∀ u, 0 ≤ g u) →
      ∫ u in (-(T + r / 2))..(T + r / 2), g u ≤ ∫ u in (-(T + 1))..(T + 1), g u := by
    intro g hg_cont hg_nn
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (μ := volume) (-(T + 1)) (-(T + r / 2)))
      (hg_cont.intervalIntegrable (μ := volume) (-(T + r / 2)) (T + r / 2))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (μ := volume) (-(T + 1)) (T + r / 2))
      (hg_cont.intervalIntegrable (μ := volume) (T + r / 2) (T + 1))
    have hL_nn : 0 ≤ ∫ u in (-(T + 1))..(-(T + r / 2)), g u :=
      intervalIntegral.integral_nonneg (by linarith) fun u _ => hg_nn u
    have hR_nn : 0 ≤ ∫ u in (T + r / 2)..(T + 1), g u :=
      intervalIntegral.integral_nonneg (by linarith) fun u _ => hg_nn u
    linarith
  have hwid1 := hwid (fun u => ‖F u‖ ^ 2) (hF_cont.norm.pow 2) (fun _ => sq_nonneg _)
  have hwid2 := hwid (fun u => ‖F' u‖ ^ 2) (hF'_cont.norm.pow 2) (fun _ => sq_nonneg _)
  have hcomb : ∑ t ∈ S, ‖F t‖ ^ 2 ≤
      (r⁻¹ + r⁻¹) * (∫ u in (-(T + 1))..(T + 1), ‖F u‖ ^ 2) +
      (r⁻¹)⁻¹ * (∫ u in (-(T + 1))..(T + 1), ‖F' u‖ ^ 2) :=
    hsob.trans (add_le_add (mul_le_mul_of_nonneg_left hwid1 (by positivity))
      (mul_le_mul_of_nonneg_left hwid2 (by positivity)))
  simp_rw [hnorm_F, hnorm_F'] at hcomb
  have hinv_inv : (r⁻¹)⁻¹ = r := inv_inv r
  have hcoef : r⁻¹ + r⁻¹ = 2 / r := by ring
  rw [hinv_inv, hcoef] at hcomb
  exact hcomb

/-! ### Section 4c: UNCONDITIONAL Gallagher Log-Free Zero-Density Theorems (`0` Assumptions!) -/

/-- **UNCONDITIONAL GALLAGHER LOG-FREE ZERO-DENSITY THEOREM (FIXED MODULUS `m`, `0` ASSUMPTIONS!)**:
directly on Mathlib's actual `DirichletCharacter.LFunction`, counting ALL zeros in
`σ ≤ ρ.re < 1, |ρ.im| ≤ T` with exact analytic multiplicity `analyticOrderNatAt`:
`∃ C > 0, ∃ A > 0, ∀ m [NeZero m], 2 ≤ m → ∀ T ≥ 1, ∀ σ, 1/2 ≤ σ → σ ≤ 1 →`
`(dirichletZeroBoxCount m σ T : ℝ) ≤ C * ((m : ℝ) * (T + 2)) ^ (A * (1 - σ))`! -/
theorem gallagher_logfree_zero_density_fixed_mod :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 < A ∧
      ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ T : ℝ, 1 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        (dirichletZeroBoxCount m σ T : ℝ) ≤ C * ((m : ℝ) * (T + 2)) ^ (A * (1 - σ)) := by
  classical
  set δ₀ : ℝ := detectorDelta0
  have hδ₀_pos : 0 < δ₀ := detectorDelta0_pos
  set C_prime : ℝ := 16000 * 902 * (30 + 2 * mertensC)
  have hCprime_pos : 0 < C_prime := by dsimp only [C_prime]; have := mertensC_spec.1; positivity
  set C_big : ℝ := max (180 * C_Z_const) (256 * C_prime * Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1)))
  set A_big : ℝ := max (2 / δ₀) (13 * ((detectorCK : ℝ) + 1) * (2400 * C_Z_const))
  have hCbig_pos : 0 < C_big := lt_of_lt_of_le (by linarith [one_le_C_Z_const]) (le_max_left _ _)
  have hAbig_pos : 0 < A_big := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C_big, hCbig_pos, A_big, hAbig_pos, fun m _ hm2 T hT σ hσ_lo hσ_hi => ?_⟩
  set D : ℝ := (m : ℝ) * (T + 2)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hD_ge3 : 3 ≤ D := by dsimp only [D]; nlinarith
  have hD_pos : 0 < D := by linarith
  have hL_gt1 : 1 < Real.log D := by
    have h3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) (h3.trans_le hD_ge3)
    rwa [Real.log_exp] at this
  set r : ℝ := 1 - σ
  have hr_nn : 0 ≤ r := by dsimp only [r]; linarith
  -- Case 1: `σ = 1` (`r = 0`), box is empty!
  by_cases hr0 : r = 0
  · have hσ1 : σ = 1 := by dsimp only [r] at hr0; linarith
    subst hσ1
    have hzero : dirichletZeroBoxCount m 1 T = 0 := by
      unfold dirichletZeroBoxCount
      exact Finset.sum_eq_zero fun χ _ => zerosOfLInBox_card_one χ T
    rw [hzero, Nat.cast_zero]
    positivity
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr0)
  -- Case 2: `δ₀ ≤ r`, trivial from multiplicity-counted cumulative height bound!
  by_cases hbig : δ₀ ≤ r
  · have hcard_char : (Fintype.card (DirichletCharacter ℂ m) : ℝ) ≤ (m : ℝ) := by
      have horth := Stage2BehrendSieve.dirichlet_orthogonality_conj (1 : ZMod m) (1 : ZMod m)
      simp only [map_one, mul_one, isUnit_one, and_self, ↓reduceIte, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul] at horth
      have hnat : Fintype.card (DirichletCharacter ℂ m) = m.totient := by exact_mod_cast horth
      rw [hnat]; exact_mod_cast Nat.totient_le m
    have hper_char : ∀ χ : DirichletCharacter ℂ m,
        ((zerosOfLInBox χ σ T).card : ℝ) ≤ 180 * C_Z_const * T * Real.log D := by
      intro χ
      by_cases hχ : χ = 1
      · subst hχ
        obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset (1 : DirichletCharacter ℂ m)
          (σ := σ) (T := T) (by linarith) Stage5StirlingPhragmen.xi Stage7HadamardXiProduct.xiZeroSeq
          Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi Stage7HadamardXiProduct.xiZeroSeq_strip
          Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq
          (fun ρ h0 h1 => by
            have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
            rw [RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos m h0 hρ1,
              Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero]
            exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
          (fun ρ h0 h1 => analyticOrderNatAt_LFunction_eq_principal h0 h1)
        rw [hcard_eq]
        have hbd := height_card_le_of_re_bound Stage7HadamardXiProduct.xiZeroSeq_strip le_rfl hT
          (fun t G => by simpa [one_mul, div_one] using sum_re_inv_sub_xiZero_le one_pos le_rfl t G)
          F (fun j hj => ((hF_mem j).mp hj).2.2)
        have hlog_le : Real.log (1 * (T + 2)) ≤ Real.log D :=
          Real.log_le_log (by linarith) (by dsimp only [D]; nlinarith)
        exact hbd.trans (mul_le_mul_of_nonneg_left hlog_le (by linarith [one_le_C_Z_const, mul_pos (by linarith [one_le_C_Z_const] : 0 < 180 * C_Z_const) (by linarith : 0 < T)]))
      · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
        set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
        have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
        have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
        obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset χ
          (σ := σ) (T := T) (by linarith) (DirichletCharacter.completedLFunction ψ)
          (Stage8HadamardLFunction.completedLZeroSeq hprim hψ)
          (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprim hψ)
          (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
          (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprim hψ)
          (fun ρ h0 h1 => by
            rw [RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ),
              Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ]
            exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
          (fun ρ h0 _ => analyticOrderNatAt_LFunction_eq_nonprincipal χ hχ h0)
        rw [hcard_eq]
        have hf_ge1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast NeZero.pos χ.conductor
        have hbd := height_card_le_of_re_bound (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
          hf_ge1 hT
          (fun t G => by simpa [div_one] using sum_re_inv_sub_LZero_le hprim hψ one_pos le_rfl t G)
          F (fun j hj => ((hF_mem j).mp hj).2.2)
        have hf_le_m : (χ.conductor : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (NeZero.pos m) χ.conductor_dvd_level
        have hlog_le : Real.log ((χ.conductor : ℝ) * (T + 2)) ≤ Real.log D :=
          Real.log_le_log (by positivity) (by dsimp only [D]; nlinarith)
        exact hbd.trans (mul_le_mul_of_nonneg_left hlog_le (by linarith [one_le_C_Z_const, mul_pos (by linarith [one_le_C_Z_const] : 0 < 180 * C_Z_const) (by linarith : 0 < T)]))
    have htot : (dirichletZeroBoxCount m σ T : ℝ) ≤ 180 * C_Z_const * D ^ 2 := by
      unfold dirichletZeroBoxCount
      rw [Nat.cast_sum]
      calc ∑ χ : DirichletCharacter ℂ m, ((zerosOfLInBox χ σ T).card : ℝ)
          ≤ ∑ _χ : DirichletCharacter ℂ m, (180 * C_Z_const * T * Real.log D) :=
            Finset.sum_le_sum fun χ _ => hper_char χ
        _ = (Fintype.card (DirichletCharacter ℂ m) : ℝ) * (180 * C_Z_const * T * Real.log D) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (m : ℝ) * (180 * C_Z_const * T * Real.log D) :=
            mul_le_mul_of_nonneg_right hcard_char (by
              have := one_le_C_Z_const; positivity)
        _ ≤ 180 * C_Z_const * D * Real.log D := by
            have hD_ge_mT : (m : ℝ) * T ≤ D := by dsimp only [D]; nlinarith
            have h1 : (m : ℝ) * (180 * C_Z_const * T * Real.log D) =
                (180 * C_Z_const * Real.log D) * ((m : ℝ) * T) := by ring
            rw [h1]
            calc (180 * C_Z_const * Real.log D) * ((m : ℝ) * T)
                ≤ (180 * C_Z_const * Real.log D) * D :=
                  mul_le_mul_of_nonneg_left hD_ge_mT (by have := one_le_C_Z_const; positivity)
              _ = 180 * C_Z_const * D * Real.log D := by ring
        _ ≤ 180 * C_Z_const * D ^ 2 := by
            have hlog_le_D : Real.log D ≤ D := le_trans (Real.log_le_sub_one_of_pos hD_pos) (by linarith)
            have h1 : 180 * C_Z_const * D * Real.log D ≤ 180 * C_Z_const * D * D :=
              mul_le_mul_of_nonneg_left hlog_le_D (by have := one_le_C_Z_const; positivity)
            linarith [show 180 * C_Z_const * D * D = 180 * C_Z_const * D ^ 2 by ring]
    have hexp_ge2 : (2 : ℝ) ≤ A_big * r := by
      have h1 : 2 / δ₀ ≤ A_big := le_max_left _ _
      have h2 := mul_le_mul h1 hbig hδ₀_pos.le (by positivity)
      rwa [div_mul_cancel₀ _ hδ₀_pos.ne'] at h2
    have hD2_le : D ^ 2 ≤ D ^ (A_big * r) := by
      rw [← Real.rpow_natCast D 2]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simpa using hexp_ge2)
    calc (dirichletZeroBoxCount m σ T : ℝ)
        ≤ 180 * C_Z_const * D ^ 2 := htot
      _ ≤ C_big * D ^ (A_big * r) :=
          mul_le_mul (le_max_left _ _) hD2_le (by positivity) hCbig_pos.le
  -- Case 3: `0 < r < δ₀` — FULL GALLAGHER LOG-FREE ZERO-DENSITY PROOF!
  push Not at hbig
  set L : ℝ := Real.log D
  set M₀ : ℕ := ⌈8 * C_Z_const * (300 * r * L + 1)⌉₊
  set K : ℕ := detectorCK * M₀
  have hM₀_ge1 : 1 ≤ M₀ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by
    have := one_le_C_Z_const; positivity)).ne'
  have hK_ge1 : 1 ≤ K := Nat.mul_pos (by have := detectorCK_ge_50; omega) hM₀_ge1
  have hr_lt1 : r < 1 := lt_trans hbig (lt_of_le_of_lt (min_le_left _ _) (by norm_num))
  -- Step 1: For EACH character `χ mod m`, extract an `r`-well-spaced set `S_χ ⊆ [-T, T]` of zero
  -- ordinates such that `(zerosOfLInBox χ σ T).card ≤ M₀ * (S_χ.card)` AND every `t ∈ S_χ` triggers
  -- `gallagher_prime_zero_detector` at some `k ∈ Icc K (K + M₀)`!
  have hthin_char : ∀ χ : DirichletCharacter ℂ m,
      ∃ S : Finset ℝ,
        (∀ t ∈ S, |t| ≤ T) ∧
        (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → r ≤ |t₁ - t₂|) ∧
        ((zerosOfLInBox χ σ T).card : ℝ) ≤ (M₀ : ℝ) * (S.card : ℝ) ∧
        (∀ t ∈ S, ∃ k ∈ Finset.Icc K (K + M₀),
          let N₁ := ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
          let N₂ := ⌊Real.exp (30 * (k : ℝ) / r)⌋₊
          D ^ 40 ≤ (N₁ : ℝ) ∧ 2 ≤ N₁ ∧ N₁ ≤ N₂ ∧
          (1 / 16 : ℝ) * Real.exp (-4 * (k : ℝ)) ≤
            ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
              (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖) := by
    intro χ
    by_cases hχ : χ = 1
    · subst hχ
      obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset (1 : DirichletCharacter ℂ m)
        (σ := σ) (T := T) (by linarith) Stage5StirlingPhragmen.xi Stage7HadamardXiProduct.xiZeroSeq
        Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi Stage7HadamardXiProduct.xiZeroSeq_strip
        Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq
        (fun ρ h0 h1 => by
          have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
          rw [RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos m h0 hρ1,
            Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero]
          exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
        (fun ρ h0 h1 => analyticOrderNatAt_LFunction_eq_principal h0 h1)
      set Y : Finset ℝ := F.image (fun j => (Stage7HadamardXiProduct.xiZeroSeq j).im)
      obtain ⟨S, hS_sub, hS_ws, hS_cov⟩ := greedy_well_spaced_thinning hr_pos Y
      have hS_bd : ∀ t ∈ S, |t| ≤ T := fun t ht => by
        obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp (hS_sub ht)
        exact ((hF_mem j).mp hjF).2.2
      have hcard_le : ((zerosOfLInBox (1 : DirichletCharacter ℂ m) σ T).card : ℝ) ≤ (M₀ : ℝ) * (S.card : ℝ) := by
        rw [hcard_eq]
        have hcov : F ⊆ S.biUnion (fun t => F.filter fun j =>
            ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j‖ < 3 * r) := by
          intro j hj
          obtain ⟨t, htS, hdist_im⟩ := hS_cov _ (Finset.mem_image_of_mem _ hj)
          refine Finset.mem_biUnion.mpr ⟨t, htS, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
          obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hj
          have htri := Complex.norm_le_abs_re_add_abs_im
            ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j)
          have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j).re =
              1 + r - (Stage7HadamardXiProduct.xiZeroSeq j).re := by simp
          have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j).im =
              t - (Stage7HadamardXiProduct.xiZeroSeq j).im := by simp
          rw [hre, him, abs_of_pos (by linarith), abs_sub_comm] at htri
          have : 1 - r ≤ (Stage7HadamardXiProduct.xiZeroSeq j).re := by dsimp only [r]; linarith
          linarith
        have hsum_le : (F.card : ℝ) ≤ ∑ t ∈ S,
            ((F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) -
              Stage7HadamardXiProduct.xiZeroSeq j‖ < 3 * r).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
        refine hsum_le.trans ?_
        calc _ ≤ ∑ _t ∈ S, (M₀ : ℝ) := by
              refine Finset.sum_le_sum fun t ht => ?_
              have h3r_le1 : 3 * r ≤ 1 := by
                have := lt_of_lt_of_le hbig (min_le_left _ _); linarith
              have hball := local_ball_card_le Stage7HadamardXiProduct.xiZeroSeq_strip hr_pos (by linarith) t
                (C_Z_const * (Real.log (|t| + 2) + 1 / (3 * r)))
                (fun G => sum_re_inv_sub_xiZero_le (by positivity) h3r_le1 t G)
                (F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) -
                  Stage7HadamardXiProduct.xiZeroSeq j‖ < 3 * r)
                (fun j hj => (Finset.mem_filter.mp hj).2)
              have hlog_le : Real.log (|t| + 2) ≤ L := by
                refine Real.log_le_log (by linarith [abs_nonneg t]) ?_
                have := hS_bd t ht; dsimp only [D]; nlinarith
              have h1 : 4 * (3 * r) * (C_Z_const * (Real.log (|t| + 2) + 1 / (3 * r))) ≤
                  8 * C_Z_const * (300 * r * L + 1) := by
                have halg : 4 * (3 * r) * (C_Z_const * (Real.log (|t| + 2) + 1 / (3 * r))) =
                    12 * C_Z_const * r * Real.log (|t| + 2) + 4 * C_Z_const := by field_simp [hr_pos.ne']; ring
                rw [halg]
                have hCZ : 1 ≤ C_Z_const := one_le_C_Z_const
                have hCZ_pos : 0 < C_Z_const := by linarith
                have hL_pos : 0 < L := by linarith
                have hmul_log : 12 * C_Z_const * r * Real.log (|t| + 2) ≤ 12 * C_Z_const * r * L :=
                  mul_le_mul_of_nonneg_left hlog_le (by positivity)
                have hcrL : 0 ≤ C_Z_const * r * L := by positivity
                linarith
              exact (hball.trans h1).trans (Nat.le_ceil _)
          _ = (M₀ : ℝ) * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      refine ⟨S, hS_bd, hS_ws, hcard_le, fun t ht => ?_⟩
      obtain ⟨j, hjF, htim⟩ := Finset.mem_image.mp (hS_sub ht)
      obtain ⟨hσj, h1j, himj⟩ := (hF_mem j).mp hjF
      set ρ_star := Stage7HadamardXiProduct.xiZeroSeq j
      have h0j : 0 < ρ_star.re := (Stage7HadamardXiProduct.xiZeroSeq_strip j).1
      have hxi0 : Stage5StirlingPhragmen.xi ρ_star = 0 := Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi.apply_eq_zero j
      have hZ0 : riemannZeta ρ_star = 0 :=
        ((Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero ρ_star).mp hxi0).2.2
      have hdist : ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star‖ < 3 * r := by
        have htri := Complex.norm_le_abs_re_add_abs_im ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star)
        have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).re = 1 + r - ρ_star.re := by simp
        have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).im = 0 := by simp [htim]
        rw [hre, him, abs_zero, add_zero, abs_of_pos (by linarith)] at htri
        have : 1 - r ≤ ρ_star.re := by dsimp only [r]; linarith
        linarith
      exact gallagher_prime_zero_detector_principal (m := m) hD_ge3 (by dsimp only [D]; nlinarith) hr_pos hbig
        (by have := hS_bd t ht; dsimp only [D]; nlinarith) h0j h1j hZ0 hdist
    · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
      have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
      have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
      obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset χ
        (σ := σ) (T := T) (by linarith) (DirichletCharacter.completedLFunction ψ)
        (Stage8HadamardLFunction.completedLZeroSeq hprim hψ)
        (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprim hψ)
        (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
        (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprim hψ)
        (fun ρ h0 h1 => by
          rw [RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ),
            Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ]
          exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
        (fun ρ h0 _ => analyticOrderNatAt_LFunction_eq_nonprincipal χ hχ h0)
      set ρ_seq := Stage8HadamardLFunction.completedLZeroSeq hprim hψ
      set Y : Finset ℝ := F.image (fun j => (ρ_seq j).im)
      obtain ⟨S, hS_sub, hS_ws, hS_cov⟩ := greedy_well_spaced_thinning hr_pos Y
      have hS_bd : ∀ t ∈ S, |t| ≤ T := fun t ht => by
        obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp (hS_sub ht)
        exact ((hF_mem j).mp hjF).2.2
      have hcard_le : ((zerosOfLInBox χ σ T).card : ℝ) ≤ (M₀ : ℝ) * (S.card : ℝ) := by
        rw [hcard_eq]
        have hcov : F ⊆ S.biUnion (fun t => F.filter fun j =>
            ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j‖ < 3 * r) := by
          intro j hj
          obtain ⟨t, htS, hdist_im⟩ := hS_cov _ (Finset.mem_image_of_mem _ hj)
          refine Finset.mem_biUnion.mpr ⟨t, htS, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
          obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hj
          have htri := Complex.norm_le_abs_re_add_abs_im ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j)
          have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j).re = 1 + r - (ρ_seq j).re := by simp
          have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j).im = t - (ρ_seq j).im := by simp
          rw [hre, him, abs_of_pos (by linarith), abs_sub_comm] at htri
          have : 1 - r ≤ (ρ_seq j).re := by dsimp only [r]; linarith
          linarith
        have hsum_le : (F.card : ℝ) ≤ ∑ t ∈ S,
            ((F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j‖ < 3 * r).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
        refine hsum_le.trans ?_
        calc _ ≤ ∑ _t ∈ S, (M₀ : ℝ) := by
              refine Finset.sum_le_sum fun t ht => ?_
              have h3r_le1 : 3 * r ≤ 1 := by
                have := lt_of_lt_of_le hbig (min_le_left _ _); linarith
              have hball := local_ball_card_le (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ)
                hr_pos (by linarith) t
                (C_Z_const * (Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 1 / (3 * r)))
                (fun G => sum_re_inv_sub_LZero_le hprim hψ (by positivity) h3r_le1 t G)
                (F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j‖ < 3 * r)
                (fun j hj => (Finset.mem_filter.mp hj).2)
              have hf_le_m : (χ.conductor : ℝ) ≤ (m : ℝ) := by
                exact_mod_cast Nat.le_of_dvd (NeZero.pos m) χ.conductor_dvd_level
              have hf_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ.conductor)
              have hlog_le : Real.log ((χ.conductor : ℝ) * (|t| + 2)) ≤ L := by
                refine Real.log_le_log (by positivity) ?_
                have := hS_bd t ht; dsimp only [D]; nlinarith
              have h1 : 4 * (3 * r) * (C_Z_const * (Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 1 / (3 * r))) ≤
                  8 * C_Z_const * (300 * r * L + 1) := by
                have halg : 4 * (3 * r) * (C_Z_const * (Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 1 / (3 * r))) =
                    12 * C_Z_const * r * Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 4 * C_Z_const := by
                  field_simp [hr_pos.ne']; ring
                rw [halg]
                have hCZ : 1 ≤ C_Z_const := one_le_C_Z_const
                have hCZ_pos : 0 < C_Z_const := by linarith
                have hL_pos : 0 < L := by linarith
                have hmul_log : 12 * C_Z_const * r * Real.log ((χ.conductor : ℝ) * (|t| + 2)) ≤
                    12 * C_Z_const * r * L :=
                  mul_le_mul_of_nonneg_left hlog_le (by positivity)
                have hcrL : 0 ≤ C_Z_const * r * L := by positivity
                linarith
              exact (hball.trans h1).trans (Nat.le_ceil _)
          _ = (M₀ : ℝ) * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      refine ⟨S, hS_bd, hS_ws, hcard_le, fun t ht => ?_⟩
      obtain ⟨j, hjF, htim⟩ := Finset.mem_image.mp (hS_sub ht)
      obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hjF
      set ρ_star := ρ_seq j
      have h0j : 0 < ρ_star.re := (Stage8HadamardLFunction.completedLZeroSeq_strip hprim hψ j).1
      have hc0 : DirichletCharacter.completedLFunction ψ ρ_star = 0 :=
        (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprim hψ).apply_eq_zero j
      have hLψ0 : DirichletCharacter.LFunction ψ ρ_star = 0 :=
        ((Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ ρ_star).mp hc0).2.2
      have hL0 : DirichletCharacter.LFunction χ ρ_star = 0 :=
        (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0j (.inl hχ)).mpr hLψ0
      have hdist : ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star‖ < 3 * r := by
        have htri := Complex.norm_le_abs_re_add_abs_im ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star)
        have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).re = 1 + r - ρ_star.re := by simp
        have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).im = 0 := by simp [htim]
        rw [hre, him, abs_zero, add_zero, abs_of_pos (by linarith)] at htri
        have : 1 - r ≤ ρ_star.re := by dsimp only [r]; linarith
        linarith
      exact gallagher_prime_zero_detector_nonprincipal χ hχ hD_ge3 (by dsimp only [D]; nlinarith) hr_pos hbig
        (by have := hS_bd t ht; dsimp only [D]; nlinarith) h0j h1j hL0 hdist
  choose S_fam hS_bd hS_ws hS_card hS_det using hthin_char
  -- Step 2: For EACH `k ∈ Icc K (K + M₀)`, apply Sobolev + Prime Hybrid Large Sieve + Mertens!
  have hper_k : ∀ k ∈ Finset.Icc K (K + M₀),
      let N₁ := ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
      let N₂ := ⌊Real.exp (30 * (k : ℝ) / r)⌋₊
      ∑ χ : DirichletCharacter ℂ m, ∑ t ∈ S_fam χ,
        ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
          (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
      C_prime * (k : ℝ) ^ 3 := by
    intro k hk_mem N₁ N₂
    have hk_ge_K : K ≤ k := (Finset.mem_Icc.mp hk_mem).1
    have hk1 : 1 ≤ k := hK_ge1.trans hk_ge_K
    -- Verify `D^40 ≤ N₁`, `2 ≤ N₁ ≤ N₂`, and `((m : ℝ) * (T + 1 + 2))^20 ≤ N₁`!
    have harg1_ge : 45 * L ≤ Real.exp (-10) * (k : ℝ) / r := by
      have hCK_nat : ⌈45 / (Real.exp (-10) * C_Z_const * 300)⌉₊ ≤ detectorCK := by
        dsimp only [detectorCK]; exact (le_max_left _ _).trans (le_max_right _ _)
      have hCK_ge : 45 / (Real.exp (-10) * C_Z_const * 300) ≤ (detectorCK : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hCK_nat)
      have hM₀_ge : 300 * C_Z_const * r * L ≤ (M₀ : ℝ) := by
        have h1 := Nat.le_ceil (8 * C_Z_const * (300 * r * L + 1))
        have := one_le_C_Z_const
        have : 0 ≤ C_Z_const * r * L := by positivity
        linarith
      have hk_ge_KM : (detectorCK : ℝ) * (M₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_K
      have hCZ_pos : 0 < C_Z_const := by linarith [one_le_C_Z_const]
      have hL_pos : 0 < L := by linarith
      have hprod := (mul_le_mul hCK_ge hM₀_ge (by positivity) (by positivity)).trans hk_ge_KM
      have halg : (45 / (Real.exp (-10) * C_Z_const * 300)) * (300 * C_Z_const * r * L) =
          45 * r * L / Real.exp (-10) := by
        field_simp [(Real.exp_pos (-10)).ne', (show (0 : ℝ) < C_Z_const by linarith [one_le_C_Z_const]).ne']
      rw [halg] at hprod
      rw [le_div_iff₀ hr_pos]
      have hmul := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-10)).le
      rw [mul_div_cancel₀ _ (Real.exp_pos (-10)).ne'] at hmul; linarith
    have hN₁_D40 : D ^ 40 ≤ (N₁ : ℝ) := by
      have hD40_eq : D ^ 40 = Real.exp (40 * L) := by
        dsimp only [L]; rw [← Real.rpow_natCast, Real.rpow_def_of_pos hD_pos]; congr 1; push_cast; ring
      have hexp_ge : Real.exp (40 * L) + 1 ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r) := by
        have h1 : Real.exp (40 * L) * Real.exp 5 ≤ Real.exp (Real.exp (-10) * (k : ℝ) / r) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
        have h2 : (2 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
        have h3 : (1 : ℝ) ≤ Real.exp (40 * L) := Real.one_le_exp (by positivity)
        nlinarith
      have hlt := Nat.lt_floor_add_one (Real.exp (Real.exp (-10) * (k : ℝ) / r))
      rw [hD40_eq]; linarith
    have hN₁_ge2 : 2 ≤ N₁ := by
      have h1 : (2 : ℝ) ≤ (N₁ : ℝ) := (show (2 : ℝ) ≤ 3 ^ 40 by norm_num).trans
        ((pow_le_pow_left₀ (by norm_num) hD_ge3 40).trans hN₁_D40)
      exact_mod_cast h1
    have hN₁_le_N₂ : N₁ ≤ N₂ := by
      refine Nat.floor_mono (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ hr_pos.le))
      have h1 : Real.exp (-10) ≤ 30 := (Real.exp_le_one_iff.mpr (by norm_num)).trans (by norm_num)
      exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg k)
    have hN₁_sieve : ((m : ℝ) * ((T + 1) + 2)) ^ 20 ≤ (N₁ : ℝ) := by
      have h1 : (m : ℝ) * ((T + 1) + 2) ≤ 2 * D := by dsimp only [D]; nlinarith
      have h2 : 2 * D ≤ D ^ 2 := by nlinarith
      calc ((m : ℝ) * ((T + 1) + 2)) ^ 20 ≤ (D ^ 2) ^ 20 := pow_le_pow_left₀ (by positivity) (h1.trans h2) 20
        _ = D ^ 40 := by ring
        _ ≤ (N₁ : ℝ) := hN₁_D40
    set P := (Finset.Ioc N₁ N₂).filter Nat.Prime
    -- Apply `prime_sum_sobolev_char` to every `χ`, sum over `χ`, then apply `gallagher_continuous_prime_hybrid_large_sieve_fixed_mod`!
    have hsob_sum :
        ∑ χ : DirichletCharacter ℂ m, ∑ t ∈ S_fam χ,
          ‖∑ p ∈ P, (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
        ((2 / r) * ∑ χ : DirichletCharacter ℂ m, ∫ t in (-(T + 1))..(T + 1),
          ‖∑ p ∈ P, (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2) +
        (r * ∑ χ : DirichletCharacter ℂ m, ∫ t in (-(T + 1))..(T + 1),
          ‖∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight k r p : ℂ)) *
            χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun χ _ => prime_sum_sobolev_char χ hN₁_ge2 hT hr_pos hr_lt1
        (fun p => (gallagherWeight k r p : ℂ)) (S_fam χ) (hS_bd χ) (hS_ws χ)
    have hls1 := gallagher_continuous_prime_hybrid_large_sieve_fixed_mod m (T := T + 1) (by linarith)
      N₁ N₂ hN₁_sieve (fun p => (gallagherWeight k r p : ℂ))
    have hls2 := gallagher_continuous_prime_hybrid_large_sieve_fixed_mod m (T := T + 1) (by linarith)
      N₁ N₂ hN₁_sieve (fun p => (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight k r p : ℂ))
    have hsum_w1 : ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) * ‖(gallagherWeight k r p : ℂ)‖ ^ 2 ≤
        r ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hpPr : p.Prime := (Finset.mem_filter.mp hp).2
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpPr.pos
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpPr.one_lt)
      have hw_le : gallagherWeight k r p ≤ r * (Real.log (p : ℝ) / (p : ℝ)) := by
        have h1 := gallagherWeight_le k hr_pos p
        rw [if_neg hpPr.ne_zero, ArithmeticFunction.vonMangoldt_apply_prime hpPr] at h1
        exact h1
      rw [Complex.norm_real, Real.norm_of_nonneg (gallagherWeight_nonneg k hr_pos p)]
      calc ((p : ℝ) / Real.log (p : ℝ)) * (gallagherWeight k r p) ^ 2
          ≤ ((p : ℝ) / Real.log (p : ℝ)) * (r * (Real.log (p : ℝ) / (p : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gallagherWeight_nonneg k hr_pos p) hw_le 2) (by positivity)
        _ = r ^ 2 * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp [hp_pos.ne', hlogp_pos.ne']
    have hsum_w2 : ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) *
          ‖(-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight k r p : ℂ)‖ ^ 2 ≤
        (900 * (k : ℝ) ^ 2) * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpI, hpPr⟩ := Finset.mem_filter.mp hp
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpPr.pos
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpPr.one_lt)
      have hN₁_pos : (0 : ℝ) < (N₁ : ℝ) := Nat.cast_pos.mpr (by omega)
      have hlog_ratio_nn : 0 ≤ Real.log ((p : ℝ) / (N₁ : ℝ)) :=
        Real.log_nonneg ((one_le_div hN₁_pos).mpr (by exact_mod_cast (Finset.mem_Ioc.mp hpI).1.le))
      have hlog_ratio_le : Real.log ((p : ℝ) / (N₁ : ℝ)) ≤ 30 * (k : ℝ) / r := by
        rw [Real.log_div hp_pos.ne' hN₁_pos.ne']
        have h1 : Real.log (p : ℝ) ≤ 30 * (k : ℝ) / r := by
          have hp_le : (p : ℝ) ≤ Real.exp (30 * (k : ℝ) / r) :=
            (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpI).2).trans (Nat.floor_le (Real.exp_pos _).le)
          simpa [Real.log_exp] using Real.log_le_log hp_pos hp_le
        have h2 : 0 ≤ Real.log (N₁ : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₁))
        linarith
      have hw_le : gallagherWeight k r p ≤ r * (Real.log (p : ℝ) / (p : ℝ)) := by
        have h1 := gallagherWeight_le k hr_pos p
        rw [if_neg hpPr.ne_zero, ArithmeticFunction.vonMangoldt_apply_prime hpPr] at h1
        exact h1
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hlog_ratio_nn, Real.norm_of_nonneg (gallagherWeight_nonneg k hr_pos p)]
      have hprod_le : Real.log ((p : ℝ) / (N₁ : ℝ)) * gallagherWeight k r p ≤
          30 * (k : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
        calc Real.log ((p : ℝ) / (N₁ : ℝ)) * gallagherWeight k r p
            ≤ (30 * (k : ℝ) / r) * (r * (Real.log (p : ℝ) / (p : ℝ))) :=
              mul_le_mul hlog_ratio_le hw_le (gallagherWeight_nonneg k hr_pos p) (by positivity)
          _ = 30 * (k : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp [hr_pos.ne']
      calc ((p : ℝ) / Real.log (p : ℝ)) * (Real.log ((p : ℝ) / (N₁ : ℝ)) * gallagherWeight k r p) ^ 2
          ≤ ((p : ℝ) / Real.log (p : ℝ)) * (30 * (k : ℝ) * (Real.log (p : ℝ) / (p : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg hlog_ratio_nn (gallagherWeight_nonneg k hr_pos p)) hprod_le 2) (by positivity)
        _ = (900 * (k : ℝ) ^ 2) * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp [hp_pos.ne', hlogp_pos.ne']; ring
    have hmert : r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) ≤ (30 + 2 * mertensC) * (k : ℝ) := by
      have h1 := sum_primes_Ioc_log_div_le hN₁_ge2 hN₁_le_N₂
      have hlogN₂ : Real.log (N₂ : ℝ) ≤ 30 * (k : ℝ) / r := by
        have hpos : (0 : ℝ) < (N₂ : ℝ) := Nat.cast_pos.mpr (by omega)
        simpa [Real.log_exp] using Real.log_le_log hpos (Nat.floor_le (Real.exp_pos _).le)
      have hlogN₁ : 0 ≤ Real.log (N₁ : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₁))
      have h2 : ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) ≤ 30 * (k : ℝ) / r + 2 * mertensC := by
        dsimp only [P]; linarith
      have hmul := mul_le_mul_of_nonneg_left h2 hr_pos.le
      have hrhs : r * (30 * (k : ℝ) / r + 2 * mertensC) = 30 * (k : ℝ) + 2 * mertensC * r := by
        field_simp [hr_pos.ne']
      rw [hrhs] at hmul
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have := mertensC_spec.1
      nlinarith
    have hpart1 : (2 / r) * ∑ χ : DirichletCharacter ℂ m, ∫ t in (-(T + 1))..(T + 1),
          ‖∑ p ∈ P, (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
        16000 * 2 * (r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left (hls1.trans (mul_le_mul_of_nonneg_left hsum_w1 (by norm_num)))
        (by positivity : (0 : ℝ) ≤ 2 / r)
      refine h1.trans_eq ?_; field_simp [hr_pos.ne']
    have hpart2 : r * ∑ χ : DirichletCharacter ℂ m, ∫ t in (-(T + 1))..(T + 1),
          ‖∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight k r p : ℂ)) *
            χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
        16000 * (900 * (k : ℝ) ^ 2) * (r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left (hls2.trans (mul_le_mul_of_nonneg_left hsum_w2 (by norm_num))) hr_pos.le
      refine h1.trans_eq ?_; ring
    have hcomb := hsob_sum.trans (add_le_add hpart1 hpart2)
    have hsum_nn : 0 ≤ r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
      refine mul_nonneg hr_pos.le (Finset.sum_nonneg fun p hp => div_nonneg
        (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)) (Nat.cast_nonneg p))
    have hk2_ge1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hk1)
    have h902 : 16000 * 2 + 16000 * (900 * (k : ℝ) ^ 2) ≤ 16000 * 902 * (k : ℝ) ^ 2 := by nlinarith
    calc _ ≤ (16000 * 2 + 16000 * (900 * (k : ℝ) ^ 2)) * (r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
            linarith
      _ ≤ (16000 * 902 * (k : ℝ) ^ 2) * ((30 + 2 * mertensC) * (k : ℝ)) :=
            mul_le_mul h902 hmert hsum_nn (by positivity)
      _ = C_prime * (k : ℝ) ^ 3 := by dsimp only [C_prime]; ring
  -- Step 3: Sum over `k ∈ Icc K (K + M₀)` and extract total well-spaced count `∑ χ, (S_fam χ).card`!
  have hS_total : ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ) ≤
      256 * C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) := by
    have hpt : ∀ (χ : DirichletCharacter ℂ m), ∀ t ∈ S_fam χ,
        (1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) ≤
          ∑ k ∈ Finset.Icc K (K + M₀),
            ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
                ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
              (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
      intro χ t ht
      obtain ⟨k₀, hk₀_mem, _, _, _, hdet⟩ := hS_det χ t ht
      have hk₀_le : (k₀ : ℝ) ≤ ((K + M₀ : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk₀_mem).2
      have hsq : (1 / 256 : ℝ) * Real.exp (-8 * (k₀ : ℝ)) ≤
          ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k₀ : ℝ) / r)⌋₊
              ⌊Real.exp (30 * (k₀ : ℝ) / r)⌋₊).filter Nat.Prime,
            (gallagherWeight k₀ r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
        have h1 := pow_le_pow_left₀ (by positivity) hdet 2
        have h2 : ((1 / 16 : ℝ) * Real.exp (-4 * (k₀ : ℝ))) ^ 2 = (1 / 256 : ℝ) * Real.exp (-8 * (k₀ : ℝ)) := by
          rw [mul_pow, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-4 * (k₀ : ℝ)) = -8 * (k₀ : ℝ) by push_cast; ring]
          norm_num
        rwa [h2] at h1
      have hmono : Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) ≤ Real.exp (-8 * (k₀ : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      refine (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans (hsq.trans ?_)
      exact Finset.single_le_sum
        (f := fun k : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
            ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
          (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2)
        (fun _ _ => sq_nonneg _) hk₀_mem
    have hsum_lb : (1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) *
        ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ) ≤
        ∑ k ∈ Finset.Icc K (K + M₀), C_prime * (k : ℝ) ^ 3 := by
      calc (1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) *
            ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ)
          = ∑ χ : DirichletCharacter ℂ m, ∑ _t ∈ S_fam χ,
              ((1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun χ _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ χ : DirichletCharacter ℂ m, ∑ t ∈ S_fam χ, ∑ k ∈ Finset.Icc K (K + M₀),
              ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
                  ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
                (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 :=
            Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun t ht => hpt χ t ht
        _ = ∑ k ∈ Finset.Icc K (K + M₀), ∑ χ : DirichletCharacter ℂ m, ∑ t ∈ S_fam χ,
              ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
                  ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
                (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
            have h1 : ∀ χ : DirichletCharacter ℂ m,
                ∑ t ∈ S_fam χ, ∑ k ∈ Finset.Icc K (K + M₀),
                  ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
                      ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
                    (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 =
                ∑ k ∈ Finset.Icc K (K + M₀), ∑ t ∈ S_fam χ,
                  ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (k : ℝ) / r)⌋₊
                      ⌊Real.exp (30 * (k : ℝ) / r)⌋₊).filter Nat.Prime,
                    (gallagherWeight k r p : ℂ) * χ (p : ZMod m) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 :=
              fun _ => Finset.sum_comm
            simp_rw [h1]; exact Finset.sum_comm
        _ ≤ ∑ k ∈ Finset.Icc K (K + M₀), C_prime * (k : ℝ) ^ 3 := Finset.sum_le_sum hper_k
    have hrhs_le : ∑ k ∈ Finset.Icc K (K + M₀), C_prime * (k : ℝ) ^ 3 ≤
        C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 := by
      have hcard_Icc : ((Finset.Icc K (K + M₀)).card : ℝ) ≤ ((K + M₀ : ℕ) : ℝ) := by
        have h1 : (Finset.Icc K (K + M₀)).card = M₀ + 1 := by rw [Nat.card_Icc]; omega
        rw [h1]; exact_mod_cast (show M₀ + 1 ≤ K + M₀ by omega)
      calc ∑ k ∈ Finset.Icc K (K + M₀), C_prime * (k : ℝ) ^ 3
          ≤ ∑ _k ∈ Finset.Icc K (K + M₀), C_prime * ((K + M₀ : ℕ) : ℝ) ^ 3 :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast (Finset.mem_Icc.mp hk).2) 3) hCprime_pos.le
        _ = ((Finset.Icc K (K + M₀)).card : ℝ) * (C_prime * ((K + M₀ : ℕ) : ℝ) ^ 3) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((K + M₀ : ℕ) : ℝ) * (C_prime * ((K + M₀ : ℕ) : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right hcard_Icc (by positivity)
        _ = C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 := by ring
    have hmul := mul_le_mul_of_nonneg_left (hsum_lb.trans hrhs_le)
      (by positivity : (0 : ℝ) ≤ 256 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)))
    have hlhs : 256 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) *
        ((1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) *
          ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ)) =
        ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ) := by
      have hcan : Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ = (Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ))) *
              ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ) := by ring
        _ = _ := by rw [hcan, one_mul]
    rw [hlhs] at hmul
    exact hmul.trans_eq (by ring)
  -- Step 4: Multiply by `M₀` and absorb polynomial factor into `exp (13 * (K + M₀)) ≤ C_big * D ^ (A_big * r)`!
  have hpoly_exp : ((M₀ : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4) ≤ Real.exp (5 * ((K + M₀ : ℕ) : ℝ)) := by
    have h1 : (M₀ : ℝ) ≤ ((K + M₀ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left M₀ K
    have h2 : ((K + M₀ : ℕ) : ℝ) ≤ Real.exp ((K + M₀ : ℕ) : ℝ) :=
      le_trans (by linarith) (Real.add_one_le_exp ((K + M₀ : ℕ) : ℝ))
    calc (M₀ : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4
        ≤ ((K + M₀ : ℕ) : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((K + M₀ : ℕ) : ℝ) ^ 5 := by ring
      _ ≤ (Real.exp ((K + M₀ : ℕ) : ℝ)) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 5
      _ = Real.exp (5 * ((K + M₀ : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; push_cast; rfl
  have hKM₀_le : ((K + M₀ : ℕ) : ℝ) ≤ ((detectorCK : ℝ) + 1) * (2400 * C_Z_const * r * L + (8 * C_Z_const + 1)) := by
    have hM₀_ub : (M₀ : ℝ) ≤ 8 * C_Z_const * (300 * r * L + 1) + 1 :=
      (Nat.ceil_lt_add_one (by have := one_le_C_Z_const; positivity)).le
    have hK_eq : ((K + M₀ : ℕ) : ℝ) = ((detectorCK : ℝ) + 1) * (M₀ : ℝ) := by
      dsimp only [K]; push_cast; ring
    rw [hK_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hexp_final : 256 * C_prime * Real.exp (13 * ((K + M₀ : ℕ) : ℝ)) ≤ C_big * D ^ (A_big * r) := by
    have h1 : 13 * ((K + M₀ : ℕ) : ℝ) ≤
        13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1) +
        (13 * ((detectorCK : ℝ) + 1) * (2400 * C_Z_const)) * r * L := by
      have := mul_le_mul_of_nonneg_left hKM₀_le (by norm_num : (0 : ℝ) ≤ 13)
      linarith
    have h2 : Real.exp (13 * ((K + M₀ : ℕ) : ℝ)) ≤
        Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1)) * D ^ (A_big * r) := by
      have hD_rpow : D ^ (A_big * r) = Real.exp (A_big * r * L) := by
        dsimp only [L]; rw [Real.rpow_def_of_pos hD_pos]; congr 1; ring
      rw [hD_rpow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hA_ge : 13 * ((detectorCK : ℝ) + 1) * (2400 * C_Z_const) ≤ A_big := le_max_right _ _
      have hrL_nn : 0 ≤ r * L := by positivity
      have := mul_le_mul_of_nonneg_right hA_ge hrL_nn
      linarith
    calc 256 * C_prime * Real.exp (13 * ((K + M₀ : ℕ) : ℝ))
        ≤ 256 * C_prime * (Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1)) * D ^ (A_big * r)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (256 * C_prime * Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1))) * D ^ (A_big * r) := by ring
      _ ≤ C_big * D ^ (A_big * r) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hD_pos.le _)
  unfold dirichletZeroBoxCount
  rw [Nat.cast_sum]
  calc ∑ χ : DirichletCharacter ℂ m, ((zerosOfLInBox χ σ T).card : ℝ)
      ≤ ∑ χ : DirichletCharacter ℂ m, ((M₀ : ℝ) * ((S_fam χ).card : ℝ)) :=
        Finset.sum_le_sum fun χ _ => hS_card χ
    _ = (M₀ : ℝ) * ∑ χ : DirichletCharacter ℂ m, ((S_fam χ).card : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (M₀ : ℝ) * (256 * C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hS_total (Nat.cast_nonneg M₀)
    _ = 256 * C_prime * ((M₀ : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4) * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) := by ring
    _ ≤ 256 * C_prime * Real.exp (5 * ((K + M₀ : ℕ) : ℝ)) * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly_exp (by positivity)) (Real.exp_pos _).le
    _ = 256 * C_prime * Real.exp (13 * ((K + M₀ : ℕ) : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ C_big * D ^ (A_big * r) := hexp_final

/-- **UNCONDITIONAL GALLAGHER LOG-FREE ZERO-DENSITY THEOREM (PRIMITIVE FAMILY `q ≤ Q`, `0` ASSUMPTIONS!)**:
directly on Mathlib's actual `DirichletCharacter.LFunction`, counting ALL zeros in
`σ ≤ ρ.re < 1, |ρ.im| ≤ T` with exact analytic multiplicity `analyticOrderNatAt`:
`∃ C > 0, ∃ A > 0, ∀ Q ≥ 1, ∀ T ≥ 1, ∀ σ, 1/2 ≤ σ → σ ≤ 1 →`
`(primitiveZeroBoxCount Q σ T : ℝ) ≤ C * (((Q : ℝ) ^ 2) * (T + 2)) ^ (A * (1 - σ))`! -/
theorem gallagher_logfree_zero_density_sum :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 < A ∧
      ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        (primitiveZeroBoxCount Q σ T : ℝ) ≤ C * (((Q : ℝ) ^ 2) * (T + 2)) ^ (A * (1 - σ)) := by
  classical
  set δ₀ : ℝ := detectorDelta0
  have hδ₀_pos : 0 < δ₀ := detectorDelta0_pos
  set C_prime : ℝ := 20000 * 902 * (30 + 2 * mertensC)
  have hCprime_pos : 0 < C_prime := by dsimp only [C_prime]; have := mertensC_spec.1; positivity
  set C_big : ℝ := max (180 * C_Z_const) (256 * C_prime * Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1)))
  set A_big : ℝ := max (2 / δ₀) (13 * ((detectorCK : ℝ) + 1) * (2400 * C_Z_const))
  have hCbig_pos : 0 < C_big := lt_of_lt_of_le (by linarith [one_le_C_Z_const]) (le_max_left _ _)
  have hAbig_pos : 0 < A_big := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C_big, hCbig_pos, A_big, hAbig_pos, fun Q hQ T hT σ hσ_lo hσ_hi => ?_⟩
  set D : ℝ := (Q : ℝ) ^ 2 * (T + 2)
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ2_ge1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hQ_le_Q2 : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hD_ge3 : 3 ≤ D := by dsimp only [D]; nlinarith
  have hD_pos : 0 < D := by linarith
  have hL_gt1 : 1 < Real.log D := by
    have h3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) (h3.trans_le hD_ge3)
    rwa [Real.log_exp] at this
  set r : ℝ := 1 - σ
  have hr_nn : 0 ≤ r := by dsimp only [r]; linarith
  -- Case 1: `σ = 1`
  by_cases hr0 : r = 0
  · have hσ1 : σ = 1 := by dsimp only [r] at hr0; linarith
    subst hσ1
    have hzero : primitiveZeroBoxCount Q 1 T = 0 := by
      unfold primitiveZeroBoxCount
      exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun χ _ => zerosOfLInBox_card_one χ T
    rw [hzero, Nat.cast_zero]; positivity
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr0)
  -- Case 2: `δ₀ ≤ r`
  by_cases hbig : δ₀ ≤ r
  · have hper_char : ∀ (k : ℕ) (_hk : k ∈ Finset.range Q) (χ : DirichletCharacter ℂ (k + 1)),
        χ.IsPrimitive → ((zerosOfLInBox χ σ T).card : ℝ) ≤ 180 * C_Z_const * T * Real.log D := by
      intro k hk χ hprim
      have hq_le_Q : (k + 1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Finset.mem_range.mp hk
      by_cases hχ : χ = 1
      · subst hχ
        obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset (1 : DirichletCharacter ℂ (k + 1))
          (σ := σ) (T := T) (by linarith) Stage5StirlingPhragmen.xi Stage7HadamardXiProduct.xiZeroSeq
          Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi Stage7HadamardXiProduct.xiZeroSeq_strip
          Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq
          (fun ρ h0 h1 => by
            have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
            rw [RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (k + 1) h0 hρ1,
              Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero]
            exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
          (fun ρ h0 h1 => analyticOrderNatAt_LFunction_eq_principal h0 h1)
        rw [hcard_eq]
        have hbd := height_card_le_of_re_bound Stage7HadamardXiProduct.xiZeroSeq_strip le_rfl hT
          (fun t G => by simpa [one_mul, div_one] using sum_re_inv_sub_xiZero_le one_pos le_rfl t G)
          F (fun j hj => ((hF_mem j).mp hj).2.2)
        have hlog_le : Real.log (1 * (T + 2)) ≤ Real.log D :=
          Real.log_le_log (by linarith) (by dsimp only [D]; nlinarith)
        exact hbd.trans (mul_le_mul_of_nonneg_left hlog_le (by have := one_le_C_Z_const; positivity))
      · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
        set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
        have hprimψ : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
        have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
        obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset χ
          (σ := σ) (T := T) (by linarith) (DirichletCharacter.completedLFunction ψ)
          (Stage8HadamardLFunction.completedLZeroSeq hprimψ hψ)
          (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprimψ hψ)
          (Stage8HadamardLFunction.completedLZeroSeq_strip hprimψ hψ)
          (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprimψ hψ)
          (fun ρ h0 h1 => by
            rw [RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ),
              Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprimψ hψ]
            exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
          (fun ρ h0 _ => analyticOrderNatAt_LFunction_eq_nonprincipal χ hχ h0)
        rw [hcard_eq]
        have hf_ge1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast NeZero.pos χ.conductor
        have hf_le_Q : (χ.conductor : ℝ) ≤ (Q : ℝ) := by
          have : χ.conductor ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) χ.conductor_dvd_level
          have : (χ.conductor : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this; linarith
        have hbd := height_card_le_of_re_bound (Stage8HadamardLFunction.completedLZeroSeq_strip hprimψ hψ)
          hf_ge1 hT
          (fun t G => by simpa [div_one] using sum_re_inv_sub_LZero_le hprimψ hψ one_pos le_rfl t G)
          F (fun j hj => ((hF_mem j).mp hj).2.2)
        have hlog_le : Real.log ((χ.conductor : ℝ) * (T + 2)) ≤ Real.log D :=
          Real.log_le_log (by positivity) (by dsimp only [D]; nlinarith)
        exact hbd.trans (mul_le_mul_of_nonneg_left hlog_le (by have := one_le_C_Z_const; positivity))
    have hcard_prim : (∑ k ∈ Finset.range Q,
        ((Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive).card : ℝ)) ≤ (Q : ℝ) ^ 2 := by
      have hnat : ∑ k ∈ Finset.range Q,
          (Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive).card ≤ Q * Q := by
        calc _ ≤ ∑ k ∈ Finset.range Q, Fintype.card (DirichletCharacter ℂ (k + 1)) :=
              Finset.sum_le_sum fun k _ => Finset.card_filter_le _ _
          _ ≤ ∑ _k ∈ Finset.range Q, Q := by
              refine Finset.sum_le_sum fun k hk => ?_
              have horth := Stage2BehrendSieve.dirichlet_orthogonality_conj
                (1 : ZMod (k + 1)) (1 : ZMod (k + 1))
              simp only [map_one, mul_one, isUnit_one, and_self, ↓reduceIte, Finset.sum_const,
                Finset.card_univ, nsmul_eq_mul] at horth
              have hcard_c : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
                exact_mod_cast horth
              rw [hcard_c]
              exact (Nat.totient_le (k + 1)).trans (Finset.mem_range.mp hk)
          _ = Q * Q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      simpa only [sq, Nat.cast_mul, Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hnat
    have htot : (primitiveZeroBoxCount Q σ T : ℝ) ≤ 180 * C_Z_const * D ^ 2 := by
      unfold primitiveZeroBoxCount
      simp only [Nat.cast_sum]
      calc ∑ k ∈ Finset.range Q,
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ((zerosOfLInBox χ σ T).card : ℝ)
          ≤ ∑ k ∈ Finset.range Q,
              ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                (180 * C_Z_const * T * Real.log D) :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun χ hχ =>
              hper_char k hk χ (Finset.mem_filter.mp hχ).2
        _ = (∑ k ∈ Finset.range Q,
              ((Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive).card : ℝ)) *
              (180 * C_Z_const * T * Real.log D) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Q : ℝ) ^ 2 * (180 * C_Z_const * T * Real.log D) :=
            mul_le_mul_of_nonneg_right hcard_prim (by have := one_le_C_Z_const; positivity)
        _ ≤ 180 * C_Z_const * D * Real.log D := by
            have hD_ge : (Q : ℝ) ^ 2 * T ≤ D := by dsimp only [D]; nlinarith
            have h1 : (Q : ℝ) ^ 2 * (180 * C_Z_const * T * Real.log D) =
                (180 * C_Z_const * Real.log D) * ((Q : ℝ) ^ 2 * T) := by ring
            rw [h1]
            exact (mul_le_mul_of_nonneg_left hD_ge (by have := one_le_C_Z_const; positivity)).trans_eq (by ring)
        _ ≤ 180 * C_Z_const * D ^ 2 := by
            have hlog_le_D : Real.log D ≤ D := le_trans (Real.log_le_sub_one_of_pos hD_pos) (by linarith)
            have h1 := mul_le_mul_of_nonneg_left hlog_le_D (by have := one_le_C_Z_const; positivity : 0 ≤ 180 * C_Z_const * D)
            linarith [show 180 * C_Z_const * D * D = 180 * C_Z_const * D ^ 2 by ring]
    have hexp_ge2 : (2 : ℝ) ≤ A_big * r := by
      have h1 : 2 / δ₀ ≤ A_big := le_max_left _ _
      have h2 := mul_le_mul h1 hbig hδ₀_pos.le (by positivity)
      rwa [div_mul_cancel₀ _ hδ₀_pos.ne'] at h2
    have hD2_le : D ^ 2 ≤ D ^ (A_big * r) := by
      rw [← Real.rpow_natCast D 2]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simpa using hexp_ge2)
    exact htot.trans (mul_le_mul (le_max_left _ _) hD2_le (by positivity) hCbig_pos.le)
  -- Case 3: `0 < r < δ₀` — FULL GALLAGHER LOG-FREE ZERO-DENSITY PROOF FOR PRIMITIVE FAMILY!
  push Not at hbig
  set L : ℝ := Real.log D
  set M₀ : ℕ := ⌈8 * C_Z_const * (300 * r * L + 1)⌉₊
  set K : ℕ := detectorCK * M₀
  have hM₀_ge1 : 1 ≤ M₀ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by
    have := one_le_C_Z_const; positivity)).ne'
  have hK_ge1 : 1 ≤ K := Nat.mul_pos (by have := detectorCK_ge_50; omega) hM₀_ge1
  have hr_lt1 : r < 1 := lt_trans hbig (lt_of_le_of_lt (min_le_left _ _) (by norm_num))
  have hthin_prim : ∀ (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)),
      ∃ S : Finset ℝ,
        (∀ t ∈ S, |t| ≤ T) ∧
        (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → r ≤ |t₁ - t₂|) ∧
        (k < Q → χ.IsPrimitive → ((zerosOfLInBox χ σ T).card : ℝ) ≤ (M₀ : ℝ) * (S.card : ℝ)) ∧
        (k < Q → χ.IsPrimitive → ∀ t ∈ S, ∃ j ∈ Finset.Icc K (K + M₀),
          let N₁ := ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
          let N₂ := ⌊Real.exp (30 * (j : ℝ) / r)⌋₊
          D ^ 40 ≤ (N₁ : ℝ) ∧ 2 ≤ N₁ ∧ N₁ ≤ N₂ ∧
          (1 / 16 : ℝ) * Real.exp (-4 * (j : ℝ)) ≤
            ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
              (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖) := by
    intro k χ
    by_cases hcond : k < Q ∧ χ.IsPrimitive
    · obtain ⟨hkQ, hprim⟩ := hcond
      have hq_le_Q : ((k + 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hkQ
      have hq_le_D : ((k + 1 : ℕ) : ℝ) ≤ D := by dsimp only [D]; nlinarith
      by_cases hχ : χ = 1
      · subst hχ
        obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset (1 : DirichletCharacter ℂ (k + 1))
          (σ := σ) (T := T) (by linarith) Stage5StirlingPhragmen.xi Stage7HadamardXiProduct.xiZeroSeq
          Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi Stage7HadamardXiProduct.xiZeroSeq_strip
          Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq
          (fun ρ h0 h1 => by
            have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
            rw [RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (k + 1) h0 hρ1,
              Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero]
            exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
          (fun ρ h0 h1 => analyticOrderNatAt_LFunction_eq_principal h0 h1)
        set Y : Finset ℝ := F.image (fun j => (Stage7HadamardXiProduct.xiZeroSeq j).im)
        obtain ⟨S, hS_sub, hS_ws, hS_cov⟩ := greedy_well_spaced_thinning hr_pos Y
        have hS_bd : ∀ t ∈ S, |t| ≤ T := fun t ht => by
          obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp (hS_sub ht)
          exact ((hF_mem j).mp hjF).2.2
        refine ⟨S, hS_bd, hS_ws, fun _ _ => ?_, fun _ _ t ht => ?_⟩
        · rw [hcard_eq]
          have hcov : F ⊆ S.biUnion (fun t => F.filter fun j =>
              ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j‖ < 3 * r) := by
            intro j hj
            obtain ⟨t, htS, hdist_im⟩ := hS_cov _ (Finset.mem_image_of_mem _ hj)
            refine Finset.mem_biUnion.mpr ⟨t, htS, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
            obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hj
            have htri := Complex.norm_le_abs_re_add_abs_im
              ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j)
            have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j).re =
                1 + r - (Stage7HadamardXiProduct.xiZeroSeq j).re := by simp
            have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - Stage7HadamardXiProduct.xiZeroSeq j).im =
                t - (Stage7HadamardXiProduct.xiZeroSeq j).im := by simp
            rw [hre, him, abs_of_pos (by linarith), abs_sub_comm] at htri
            have : 1 - r ≤ (Stage7HadamardXiProduct.xiZeroSeq j).re := by dsimp only [r]; linarith
            linarith
          have hsum_le : (F.card : ℝ) ≤ ∑ t ∈ S,
              ((F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) -
                Stage7HadamardXiProduct.xiZeroSeq j‖ < 3 * r).card : ℝ) := by
            exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
          refine hsum_le.trans ?_
          calc _ ≤ ∑ _t ∈ S, (M₀ : ℝ) := by
                refine Finset.sum_le_sum fun t ht => ?_
                have h3r_le1 : 3 * r ≤ 1 := by
                  have := lt_of_lt_of_le hbig (min_le_left _ _); linarith
                have hball := local_ball_card_le Stage7HadamardXiProduct.xiZeroSeq_strip hr_pos (by linarith) t
                  (C_Z_const * (Real.log (|t| + 2) + 1 / (3 * r)))
                  (fun G => sum_re_inv_sub_xiZero_le (by positivity) h3r_le1 t G)
                  (F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) -
                    Stage7HadamardXiProduct.xiZeroSeq j‖ < 3 * r)
                  (fun j hj => (Finset.mem_filter.mp hj).2)
                have hlog_le : Real.log (|t| + 2) ≤ L := by
                  refine Real.log_le_log (by linarith [abs_nonneg t]) ?_
                  have := hS_bd t ht; dsimp only [D]; nlinarith
                have h1 : 4 * (3 * r) * (C_Z_const * (Real.log (|t| + 2) + 1 / (3 * r))) ≤
                    8 * C_Z_const * (300 * r * L + 1) := by
                  have halg : 4 * (3 * r) * (C_Z_const * (Real.log (|t| + 2) + 1 / (3 * r))) =
                      12 * C_Z_const * r * Real.log (|t| + 2) + 4 * C_Z_const := by field_simp [hr_pos.ne']; ring
                  rw [halg]
                  have hCZ : 1 ≤ C_Z_const := one_le_C_Z_const
                  have hCZ_pos : 0 < C_Z_const := by linarith
                  have hL_pos : 0 < L := by linarith
                  have hmul_log : 12 * C_Z_const * r * Real.log (|t| + 2) ≤ 12 * C_Z_const * r * L :=
                    mul_le_mul_of_nonneg_left hlog_le (by positivity)
                  have hcrL : 0 ≤ C_Z_const * r * L := by positivity
                  linarith
                exact (hball.trans h1).trans (Nat.le_ceil _)
            _ = (M₀ : ℝ) * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        · obtain ⟨j, hjF, htim⟩ := Finset.mem_image.mp (hS_sub ht)
          obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hjF
          set ρ_star := Stage7HadamardXiProduct.xiZeroSeq j
          have h0j : 0 < ρ_star.re := (Stage7HadamardXiProduct.xiZeroSeq_strip j).1
          have hxi0 : Stage5StirlingPhragmen.xi ρ_star = 0 :=
            Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi.apply_eq_zero j
          have hZ0 : riemannZeta ρ_star = 0 :=
            ((Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero ρ_star).mp hxi0).2.2
          have hdist : ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star‖ < 3 * r := by
            have htri := Complex.norm_le_abs_re_add_abs_im ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star)
            have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).re = 1 + r - ρ_star.re := by simp
            have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).im = 0 := by simp [htim]
            rw [hre, him, abs_zero, add_zero, abs_of_pos (by linarith)] at htri
            have : 1 - r ≤ ρ_star.re := by dsimp only [r]; linarith
            linarith
          exact gallagher_prime_zero_detector_principal (m := k + 1) hD_ge3 hq_le_D hr_pos hbig
            (by have := hS_bd t ht; dsimp only [D]; nlinarith) h0j h1j hZ0 hdist
      · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
        set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
        have hprimψ : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
        have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
        obtain ⟨F, hF_mem, hcard_eq⟩ := zerosOfLInBox_card_eq_index_finset χ
          (σ := σ) (T := T) (by linarith) (DirichletCharacter.completedLFunction ψ)
          (Stage8HadamardLFunction.completedLZeroSeq hprimψ hψ)
          (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprimψ hψ)
          (Stage8HadamardLFunction.completedLZeroSeq_strip hprimψ hψ)
          (Stage8HadamardLFunction.completedLZeroSeq_summable_inv_sq hprimψ hψ)
          (fun ρ h0 h1 => by
            rw [RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ),
              Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprimψ hψ]
            exact ⟨fun h => ⟨h0, h1, h⟩, fun h => h.2.2⟩)
          (fun ρ h0 _ => analyticOrderNatAt_LFunction_eq_nonprincipal χ hχ h0)
        set ρ_seq := Stage8HadamardLFunction.completedLZeroSeq hprimψ hψ
        set Y : Finset ℝ := F.image (fun j => (ρ_seq j).im)
        obtain ⟨S, hS_sub, hS_ws, hS_cov⟩ := greedy_well_spaced_thinning hr_pos Y
        have hS_bd : ∀ t ∈ S, |t| ≤ T := fun t ht => by
          obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp (hS_sub ht)
          exact ((hF_mem j).mp hjF).2.2
        refine ⟨S, hS_bd, hS_ws, fun _ _ => ?_, fun _ _ t ht => ?_⟩
        · rw [hcard_eq]
          have hcov : F ⊆ S.biUnion (fun t => F.filter fun j =>
              ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j‖ < 3 * r) := by
            intro j hj
            obtain ⟨t, htS, hdist_im⟩ := hS_cov _ (Finset.mem_image_of_mem _ hj)
            refine Finset.mem_biUnion.mpr ⟨t, htS, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
            obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hj
            have htri := Complex.norm_le_abs_re_add_abs_im ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j)
            have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j).re = 1 + r - (ρ_seq j).re := by simp
            have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j).im = t - (ρ_seq j).im := by simp
            rw [hre, him, abs_of_pos (by linarith), abs_sub_comm] at htri
            have : 1 - r ≤ (ρ_seq j).re := by dsimp only [r]; linarith
            linarith
          have hsum_le : (F.card : ℝ) ≤ ∑ t ∈ S,
              ((F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j‖ < 3 * r).card : ℝ) := by
            exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
          refine hsum_le.trans ?_
          calc _ ≤ ∑ _t ∈ S, (M₀ : ℝ) := by
                refine Finset.sum_le_sum fun t ht => ?_
                have h3r_le1 : 3 * r ≤ 1 := by
                  have := lt_of_lt_of_le hbig (min_le_left _ _); linarith
                have hball := local_ball_card_le (Stage8HadamardLFunction.completedLZeroSeq_strip hprimψ hψ)
                  hr_pos (by linarith) t
                  (C_Z_const * (Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 1 / (3 * r)))
                  (fun G => sum_re_inv_sub_LZero_le hprimψ hψ (by positivity) h3r_le1 t G)
                  (F.filter fun j => ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_seq j‖ < 3 * r)
                  (fun j hj => (Finset.mem_filter.mp hj).2)
                have hf_le_q : (χ.conductor : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
                  exact_mod_cast Nat.le_of_dvd (Nat.succ_pos k) χ.conductor_dvd_level
                have hf_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ.conductor)
                have hlog_le : Real.log ((χ.conductor : ℝ) * (|t| + 2)) ≤ L := by
                  refine Real.log_le_log (by positivity) ?_
                  have := hS_bd t ht; dsimp only [D]; nlinarith
                have h1 : 4 * (3 * r) * (C_Z_const * (Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 1 / (3 * r))) ≤
                    8 * C_Z_const * (300 * r * L + 1) := by
                  have halg : 4 * (3 * r) * (C_Z_const * (Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 1 / (3 * r))) =
                      12 * C_Z_const * r * Real.log ((χ.conductor : ℝ) * (|t| + 2)) + 4 * C_Z_const := by
                    field_simp [hr_pos.ne']; ring
                  rw [halg]
                  have hCZ : 1 ≤ C_Z_const := one_le_C_Z_const
                  have hCZ_pos : 0 < C_Z_const := by linarith
                  have hL_pos : 0 < L := by linarith
                  have hmul_log : 12 * C_Z_const * r * Real.log ((χ.conductor : ℝ) * (|t| + 2)) ≤
                      12 * C_Z_const * r * L :=
                    mul_le_mul_of_nonneg_left hlog_le (by positivity)
                  have hcrL : 0 ≤ C_Z_const * r * L := by positivity
                  linarith
                exact (hball.trans h1).trans (Nat.le_ceil _)
            _ = (M₀ : ℝ) * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        · obtain ⟨j, hjF, htim⟩ := Finset.mem_image.mp (hS_sub ht)
          obtain ⟨hσj, h1j, _⟩ := (hF_mem j).mp hjF
          set ρ_star := ρ_seq j
          have h0j : 0 < ρ_star.re := (Stage8HadamardLFunction.completedLZeroSeq_strip hprimψ hψ j).1
          have hc0 : DirichletCharacter.completedLFunction ψ ρ_star = 0 :=
            (Stage8HadamardLFunction.isMultiplicityZeroSeq_completedLFunction hprimψ hψ).apply_eq_zero j
          have hLψ0 : DirichletCharacter.LFunction ψ ρ_star = 0 :=
            ((Stage6LFunctionOrder.completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprimψ hψ ρ_star).mp hc0).2.2
          have hL0 : DirichletCharacter.LFunction χ ρ_star = 0 :=
            (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0j (.inl hχ)).mpr hLψ0
          have hdist : ‖(((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star‖ < 3 * r := by
            have htri := Complex.norm_le_abs_re_add_abs_im ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star)
            have hre : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).re = 1 + r - ρ_star.re := by simp
            have him : ((((1 + r : ℝ) : ℂ) + I * (t : ℂ)) - ρ_star).im = 0 := by simp [htim]
            rw [hre, him, abs_zero, add_zero, abs_of_pos (by linarith)] at htri
            have : 1 - r ≤ ρ_star.re := by dsimp only [r]; linarith
            linarith
          exact gallagher_prime_zero_detector_nonprincipal χ hχ hD_ge3 hq_le_D hr_pos hbig
            (by have := hS_bd t ht; dsimp only [D]; nlinarith) h0j h1j hL0 hdist
    · exact ⟨∅, by simp, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hcond, fun h1 h2 => absurd ⟨h1, h2⟩ hcond⟩
  choose S_fam hS_bd hS_ws hS_card hS_det using hthin_prim
  -- Step 2: For EACH `j ∈ Icc K (K + M₀)`, apply Sobolev + Primitive Prime Hybrid Large Sieve + Mertens!
  have hper_j : ∀ j ∈ Finset.Icc K (K + M₀),
      let N₁ := ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
      let N₂ := ⌊Real.exp (30 * (j : ℝ) / r)⌋₊
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ∑ t ∈ S_fam k χ,
            ‖∑ p ∈ (Finset.Ioc N₁ N₂).filter Nat.Prime,
              (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
      C_prime * (j : ℝ) ^ 3 := by
    intro j hj_mem N₁ N₂
    have hj_ge_K : K ≤ j := (Finset.mem_Icc.mp hj_mem).1
    have hj1 : 1 ≤ j := hK_ge1.trans hj_ge_K
    have harg1_ge : 45 * L ≤ Real.exp (-10) * (j : ℝ) / r := by
      have hCK_nat : ⌈45 / (Real.exp (-10) * C_Z_const * 300)⌉₊ ≤ detectorCK := by
        dsimp only [detectorCK]; exact (le_max_left _ _).trans (le_max_right _ _)
      have hCK_ge : 45 / (Real.exp (-10) * C_Z_const * 300) ≤ (detectorCK : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hCK_nat)
      have hM₀_ge : 300 * C_Z_const * r * L ≤ (M₀ : ℝ) := by
        have h1 := Nat.le_ceil (8 * C_Z_const * (300 * r * L + 1))
        have := one_le_C_Z_const
        have : 0 ≤ C_Z_const * r * L := by positivity
        linarith
      have hj_ge_KM : (detectorCK : ℝ) * (M₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj_ge_K
      have hCZ_pos : 0 < C_Z_const := by linarith [one_le_C_Z_const]
      have hL_pos : 0 < L := by linarith
      have hprod := (mul_le_mul hCK_ge hM₀_ge (by positivity) (by positivity)).trans hj_ge_KM
      have halg : (45 / (Real.exp (-10) * C_Z_const * 300)) * (300 * C_Z_const * r * L) =
          45 * r * L / Real.exp (-10) := by
        field_simp [(Real.exp_pos (-10)).ne', (show (0 : ℝ) < C_Z_const by linarith [one_le_C_Z_const]).ne']
      rw [halg] at hprod
      rw [le_div_iff₀ hr_pos]
      have hmul := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-10)).le
      rw [mul_div_cancel₀ _ (Real.exp_pos (-10)).ne'] at hmul; linarith
    have hN₁_D40 : D ^ 40 ≤ (N₁ : ℝ) := by
      have hD40_eq : D ^ 40 = Real.exp (40 * L) := by
        dsimp only [L]; rw [← Real.rpow_natCast, Real.rpow_def_of_pos hD_pos]; congr 1; push_cast; ring
      have hexp_ge : Real.exp (40 * L) + 1 ≤ Real.exp (Real.exp (-10) * (j : ℝ) / r) := by
        have h1 : Real.exp (40 * L) * Real.exp 5 ≤ Real.exp (Real.exp (-10) * (j : ℝ) / r) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
        have h2 : (2 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
        have h3 : (1 : ℝ) ≤ Real.exp (40 * L) := Real.one_le_exp (by positivity)
        nlinarith
      have hlt := Nat.lt_floor_add_one (Real.exp (Real.exp (-10) * (j : ℝ) / r))
      rw [hD40_eq]; linarith
    have hN₁_ge2 : 2 ≤ N₁ := by
      have h1 : (2 : ℝ) ≤ (N₁ : ℝ) := (show (2 : ℝ) ≤ 3 ^ 40 by norm_num).trans
        ((pow_le_pow_left₀ (by norm_num) hD_ge3 40).trans hN₁_D40)
      exact_mod_cast h1
    have hN₁_le_N₂ : N₁ ≤ N₂ := by
      refine Nat.floor_mono (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ hr_pos.le))
      have h1 : Real.exp (-10) ≤ 30 := (Real.exp_le_one_iff.mpr (by norm_num)).trans (by norm_num)
      exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg j)
    have hN₁_sieve : ((Q : ℝ) ^ 2 * ((T + 1) + 2)) ^ 20 ≤ (N₁ : ℝ) := by
      have h1 : (Q : ℝ) ^ 2 * ((T + 1) + 2) ≤ 2 * D := by dsimp only [D]; nlinarith
      have h2 : 2 * D ≤ D ^ 2 := by nlinarith
      calc ((Q : ℝ) ^ 2 * ((T + 1) + 2)) ^ 20 ≤ (D ^ 2) ^ 20 := pow_le_pow_left₀ (by positivity) (h1.trans h2) 20
        _ = D ^ 40 := by ring
        _ ≤ (N₁ : ℝ) := hN₁_D40
    set P := (Finset.Ioc N₁ N₂).filter Nat.Prime
    have hsob_sum :
        ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ∑ t ∈ S_fam k χ,
              ‖∑ p ∈ P, (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
        ((2 / r) * ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ∫ t in (-(T + 1))..(T + 1),
              ‖∑ p ∈ P, (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2) +
        (r * ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ∫ t in (-(T + 1))..(T + 1),
              ‖∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight j r p : ℂ)) *
                χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun χ _ => prime_sum_sobolev_char χ hN₁_ge2 hT hr_pos hr_lt1
        (fun p => (gallagherWeight j r p : ℂ)) (S_fam k χ) (hS_bd k χ) (hS_ws k χ)
    have hls1 := gallagher_continuous_prime_hybrid_large_sieve_prim Q hQ (T := T + 1) (by linarith)
      N₁ N₂ hN₁_sieve (fun p => (gallagherWeight j r p : ℂ))
    have hls2 := gallagher_continuous_prime_hybrid_large_sieve_prim Q hQ (T := T + 1) (by linarith)
      N₁ N₂ hN₁_sieve (fun p => (-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight j r p : ℂ))
    have hsum_w1 : ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) * ‖(gallagherWeight j r p : ℂ)‖ ^ 2 ≤
        r ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hpPr : p.Prime := (Finset.mem_filter.mp hp).2
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpPr.pos
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpPr.one_lt)
      have hw_le : gallagherWeight j r p ≤ r * (Real.log (p : ℝ) / (p : ℝ)) := by
        have h1 := gallagherWeight_le j hr_pos p
        rw [if_neg hpPr.ne_zero, ArithmeticFunction.vonMangoldt_apply_prime hpPr] at h1
        exact h1
      rw [Complex.norm_real, Real.norm_of_nonneg (gallagherWeight_nonneg j hr_pos p)]
      calc ((p : ℝ) / Real.log (p : ℝ)) * (gallagherWeight j r p) ^ 2
          ≤ ((p : ℝ) / Real.log (p : ℝ)) * (r * (Real.log (p : ℝ) / (p : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gallagherWeight_nonneg j hr_pos p) hw_le 2) (by positivity)
        _ = r ^ 2 * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp [hp_pos.ne', hlogp_pos.ne']
    have hsum_w2 : ∑ p ∈ P, ((p : ℝ) / Real.log (p : ℝ)) *
          ‖(-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight j r p : ℂ)‖ ^ 2 ≤
        (900 * (j : ℝ) ^ 2) * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpI, hpPr⟩ := Finset.mem_filter.mp hp
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpPr.pos
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpPr.one_lt)
      have hN₁_pos : (0 : ℝ) < (N₁ : ℝ) := Nat.cast_pos.mpr (by omega)
      have hlog_ratio_nn : 0 ≤ Real.log ((p : ℝ) / (N₁ : ℝ)) :=
        Real.log_nonneg ((one_le_div hN₁_pos).mpr (by exact_mod_cast (Finset.mem_Ioc.mp hpI).1.le))
      have hlog_ratio_le : Real.log ((p : ℝ) / (N₁ : ℝ)) ≤ 30 * (j : ℝ) / r := by
        rw [Real.log_div hp_pos.ne' hN₁_pos.ne']
        have h1 : Real.log (p : ℝ) ≤ 30 * (j : ℝ) / r := by
          have hp_le : (p : ℝ) ≤ Real.exp (30 * (j : ℝ) / r) :=
            (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpI).2).trans (Nat.floor_le (Real.exp_pos _).le)
          simpa [Real.log_exp] using Real.log_le_log hp_pos hp_le
        have h2 : 0 ≤ Real.log (N₁ : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₁))
        linarith
      have hw_le : gallagherWeight j r p ≤ r * (Real.log (p : ℝ) / (p : ℝ)) := by
        have h1 := gallagherWeight_le j hr_pos p
        rw [if_neg hpPr.ne_zero, ArithmeticFunction.vonMangoldt_apply_prime hpPr] at h1
        exact h1
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hlog_ratio_nn, Real.norm_of_nonneg (gallagherWeight_nonneg j hr_pos p)]
      have hprod_le : Real.log ((p : ℝ) / (N₁ : ℝ)) * gallagherWeight j r p ≤
          30 * (j : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
        calc Real.log ((p : ℝ) / (N₁ : ℝ)) * gallagherWeight j r p
            ≤ (30 * (j : ℝ) / r) * (r * (Real.log (p : ℝ) / (p : ℝ))) :=
              mul_le_mul hlog_ratio_le hw_le (gallagherWeight_nonneg j hr_pos p) (by positivity)
          _ = 30 * (j : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp [hr_pos.ne']
      calc ((p : ℝ) / Real.log (p : ℝ)) * (Real.log ((p : ℝ) / (N₁ : ℝ)) * gallagherWeight j r p) ^ 2
          ≤ ((p : ℝ) / Real.log (p : ℝ)) * (30 * (j : ℝ) * (Real.log (p : ℝ) / (p : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg hlog_ratio_nn (gallagherWeight_nonneg j hr_pos p)) hprod_le 2) (by positivity)
        _ = (900 * (j : ℝ) ^ 2) * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp [hp_pos.ne', hlogp_pos.ne']; ring
    have hmert : r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) ≤ (30 + 2 * mertensC) * (j : ℝ) := by
      have h1 := sum_primes_Ioc_log_div_le hN₁_ge2 hN₁_le_N₂
      have hlogN₂ : Real.log (N₂ : ℝ) ≤ 30 * (j : ℝ) / r := by
        have hpos : (0 : ℝ) < (N₂ : ℝ) := Nat.cast_pos.mpr (by omega)
        simpa [Real.log_exp] using Real.log_le_log hpos (Nat.floor_le (Real.exp_pos _).le)
      have hlogN₁ : 0 ≤ Real.log (N₁ : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₁))
      have h2 : ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) ≤ 30 * (j : ℝ) / r + 2 * mertensC := by
        dsimp only [P]; linarith
      have hmul := mul_le_mul_of_nonneg_left h2 hr_pos.le
      have hrhs : r * (30 * (j : ℝ) / r + 2 * mertensC) = 30 * (j : ℝ) + 2 * mertensC * r := by
        field_simp [hr_pos.ne']
      rw [hrhs] at hmul
      have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have := mertensC_spec.1
      nlinarith
    have hpart1 : (2 / r) * ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ∫ t in (-(T + 1))..(T + 1),
              ‖∑ p ∈ P, (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
        20000 * 2 * (r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left (hls1.trans (mul_le_mul_of_nonneg_left hsum_w1 (by norm_num)))
        (by positivity : (0 : ℝ) ≤ 2 / r)
      refine h1.trans_eq ?_; field_simp [hr_pos.ne']
    have hpart2 : r * ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ∫ t in (-(T + 1))..(T + 1),
              ‖∑ p ∈ P, ((-I * (Real.log ((p : ℝ) / (N₁ : ℝ)) : ℂ)) * (gallagherWeight j r p : ℂ)) *
                χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 ≤
        20000 * (900 * (j : ℝ) ^ 2) * (r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left (hls2.trans (mul_le_mul_of_nonneg_left hsum_w2 (by norm_num))) hr_pos.le
      refine h1.trans_eq ?_; ring
    have hcomb := hsob_sum.trans (add_le_add hpart1 hpart2)
    have hsum_nn : 0 ≤ r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
      refine mul_nonneg hr_pos.le (Finset.sum_nonneg fun p hp => div_nonneg
        (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)) (Nat.cast_nonneg p))
    have hj2_ge1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hj1)
    have h902 : 20000 * 2 + 20000 * (900 * (j : ℝ) ^ 2) ≤ 20000 * 902 * (j : ℝ) ^ 2 := by nlinarith
    calc _ ≤ (20000 * 2 + 20000 * (900 * (j : ℝ) ^ 2)) * (r * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
            linarith
      _ ≤ (20000 * 902 * (j : ℝ) ^ 2) * ((30 + 2 * mertensC) * (j : ℝ)) :=
            mul_le_mul h902 hmert hsum_nn (by positivity)
      _ = C_prime * (j : ℝ) ^ 3 := by dsimp only [C_prime]; ring
  -- Step 3: Sum over `j ∈ Icc K (K + M₀)` and extract total well-spaced count!
  have hS_total : ∑ k ∈ Finset.range Q,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ((S_fam k χ).card : ℝ) ≤
      256 * C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) := by
    have hpt : ∀ k ∈ Finset.range Q,
        ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ∀ t ∈ S_fam k χ,
          (1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) ≤
            ∑ j ∈ Finset.Icc K (K + M₀),
              ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                  ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
      intro k hk χ hχ t ht
      obtain ⟨j₀, hj₀_mem, _, _, _, hdet⟩ :=
        hS_det k χ (Finset.mem_range.mp hk) (Finset.mem_filter.mp hχ).2 t ht
      have hj₀_le : (j₀ : ℝ) ≤ ((K + M₀ : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj₀_mem).2
      have hsq : (1 / 256 : ℝ) * Real.exp (-8 * (j₀ : ℝ)) ≤
          ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j₀ : ℝ) / r)⌋₊
              ⌊Real.exp (30 * (j₀ : ℝ) / r)⌋₊).filter Nat.Prime,
            (gallagherWeight j₀ r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
        have h1 := pow_le_pow_left₀ (by positivity) hdet 2
        have h2 : ((1 / 16 : ℝ) * Real.exp (-4 * (j₀ : ℝ))) ^ 2 = (1 / 256 : ℝ) * Real.exp (-8 * (j₀ : ℝ)) := by
          rw [mul_pow, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-4 * (j₀ : ℝ)) = -8 * (j₀ : ℝ) by push_cast; ring]
          norm_num
        rwa [h2] at h1
      have hmono : Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) ≤ Real.exp (-8 * (j₀ : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      refine (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans (hsq.trans ?_)
      exact Finset.single_le_sum
        (f := fun j : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
            ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
          (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2)
        (fun _ _ => sq_nonneg _) hj₀_mem
    have hsum_lb : (1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) *
        (∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((S_fam k χ).card : ℝ)) ≤
        ∑ j ∈ Finset.Icc K (K + M₀), C_prime * (j : ℝ) ^ 3 := by
      calc (1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) *
            (∑ k ∈ Finset.range Q,
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ((S_fam k χ).card : ℝ))
          = ∑ k ∈ Finset.range Q,
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ∑ _t ∈ S_fam k χ, ((1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun χ _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ k ∈ Finset.range Q,
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ∑ t ∈ S_fam k χ, ∑ j ∈ Finset.Icc K (K + M₀),
                  ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                      ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                    (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun χ hχ => Finset.sum_le_sum fun t ht =>
              hpt k hk χ hχ t ht
        _ = ∑ j ∈ Finset.Icc K (K + M₀), ∑ k ∈ Finset.range Q,
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ∑ t ∈ S_fam k χ,
                  ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                      ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                    (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
            have h1 : ∀ k : ℕ,
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ∑ t ∈ S_fam k χ, ∑ j ∈ Finset.Icc K (K + M₀),
                    ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                        ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                      (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 =
                ∑ j ∈ Finset.Icc K (K + M₀),
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                    ∑ t ∈ S_fam k χ,
                      ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                          ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                        (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 := by
              intro k
              have hswap : ∀ χ : DirichletCharacter ℂ (k + 1),
                  ∑ t ∈ S_fam k χ, ∑ j ∈ Finset.Icc K (K + M₀),
                    ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                        ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                      (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 =
                  ∑ j ∈ Finset.Icc K (K + M₀), ∑ t ∈ S_fam k χ,
                    ‖∑ p ∈ (Finset.Ioc ⌊Real.exp (Real.exp (-10) * (j : ℝ) / r)⌋₊
                        ⌊Real.exp (30 * (j : ℝ) / r)⌋₊).filter Nat.Prime,
                      (gallagherWeight j r p : ℂ) * χ (p : ZMod (k + 1)) * (p : ℂ) ^ (-(I * (t : ℂ)))‖ ^ 2 :=
                fun _ => Finset.sum_comm
              simp_rw [hswap]; exact Finset.sum_comm
            simp_rw [h1]; exact Finset.sum_comm
        _ ≤ ∑ j ∈ Finset.Icc K (K + M₀), C_prime * (j : ℝ) ^ 3 := Finset.sum_le_sum hper_j
    have hrhs_le : ∑ j ∈ Finset.Icc K (K + M₀), C_prime * (j : ℝ) ^ 3 ≤
        C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 := by
      have hcard_Icc : ((Finset.Icc K (K + M₀)).card : ℝ) ≤ ((K + M₀ : ℕ) : ℝ) := by
        have h1 : (Finset.Icc K (K + M₀)).card = M₀ + 1 := by rw [Nat.card_Icc]; omega
        rw [h1]; exact_mod_cast (show M₀ + 1 ≤ K + M₀ by omega)
      calc ∑ j ∈ Finset.Icc K (K + M₀), C_prime * (j : ℝ) ^ 3
          ≤ ∑ _j ∈ Finset.Icc K (K + M₀), C_prime * ((K + M₀ : ℕ) : ℝ) ^ 3 :=
            Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Nat.cast_nonneg j) (by exact_mod_cast (Finset.mem_Icc.mp hj).2) 3) hCprime_pos.le
        _ = ((Finset.Icc K (K + M₀)).card : ℝ) * (C_prime * ((K + M₀ : ℕ) : ℝ) ^ 3) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((K + M₀ : ℕ) : ℝ) * (C_prime * ((K + M₀ : ℕ) : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right hcard_Icc (by positivity)
        _ = C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 := by ring
    have hmul := mul_le_mul_of_nonneg_left (hsum_lb.trans hrhs_le)
      (by positivity : (0 : ℝ) ≤ 256 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)))
    have hlhs : 256 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) *
        ((1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) *
          (∑ k ∈ Finset.range Q,
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ((S_fam k χ).card : ℝ))) =
        ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((S_fam k χ).card : ℝ) := by
      have hcan : Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      set Ssum : ℝ := ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ((S_fam k χ).card : ℝ)
      calc 256 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) * ((1 / 256 : ℝ) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ)) * Ssum)
          = (Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) * Real.exp (-8 * ((K + M₀ : ℕ) : ℝ))) * Ssum := by ring
        _ = Ssum := by rw [hcan, one_mul]
    rw [hlhs] at hmul
    exact hmul.trans_eq (by ring)
  -- Step 4: Final exponential absorption!
  have hpoly_exp : ((M₀ : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4) ≤ Real.exp (5 * ((K + M₀ : ℕ) : ℝ)) := by
    have h1 : (M₀ : ℝ) ≤ ((K + M₀ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left M₀ K
    have h2 : ((K + M₀ : ℕ) : ℝ) ≤ Real.exp ((K + M₀ : ℕ) : ℝ) :=
      le_trans (by linarith) (Real.add_one_le_exp ((K + M₀ : ℕ) : ℝ))
    calc (M₀ : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4
        ≤ ((K + M₀ : ℕ) : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((K + M₀ : ℕ) : ℝ) ^ 5 := by ring
      _ ≤ (Real.exp ((K + M₀ : ℕ) : ℝ)) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 5
      _ = Real.exp (5 * ((K + M₀ : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; push_cast; rfl
  have hKM₀_le : ((K + M₀ : ℕ) : ℝ) ≤ ((detectorCK : ℝ) + 1) * (2400 * C_Z_const * r * L + (8 * C_Z_const + 1)) := by
    have hM₀_ub : (M₀ : ℝ) ≤ 8 * C_Z_const * (300 * r * L + 1) + 1 :=
      (Nat.ceil_lt_add_one (by have := one_le_C_Z_const; positivity)).le
    have hK_eq : ((K + M₀ : ℕ) : ℝ) = ((detectorCK : ℝ) + 1) * (M₀ : ℝ) := by
      dsimp only [K]; push_cast; ring
    rw [hK_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hexp_final : 256 * C_prime * Real.exp (13 * ((K + M₀ : ℕ) : ℝ)) ≤ C_big * D ^ (A_big * r) := by
    have h1 : 13 * ((K + M₀ : ℕ) : ℝ) ≤
        13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1) +
        (13 * ((detectorCK : ℝ) + 1) * (2400 * C_Z_const)) * r * L := by
      have := mul_le_mul_of_nonneg_left hKM₀_le (by norm_num : (0 : ℝ) ≤ 13)
      linarith
    have h2 : Real.exp (13 * ((K + M₀ : ℕ) : ℝ)) ≤
        Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1)) * D ^ (A_big * r) := by
      have hD_rpow : D ^ (A_big * r) = Real.exp (A_big * r * L) := by
        dsimp only [L]; rw [Real.rpow_def_of_pos hD_pos]; congr 1; ring
      rw [hD_rpow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hA_ge : 13 * ((detectorCK : ℝ) + 1) * (2400 * C_Z_const) ≤ A_big := le_max_right _ _
      have hrL_nn : 0 ≤ r * L := by positivity
      have := mul_le_mul_of_nonneg_right hA_ge hrL_nn
      linarith
    calc 256 * C_prime * Real.exp (13 * ((K + M₀ : ℕ) : ℝ))
        ≤ 256 * C_prime * (Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1)) * D ^ (A_big * r)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (256 * C_prime * Real.exp (13 * ((detectorCK : ℝ) + 1) * (8 * C_Z_const + 1))) * D ^ (A_big * r) := by ring
      _ ≤ C_big * D ^ (A_big * r) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hD_pos.le _)
  unfold primitiveZeroBoxCount
  simp only [Nat.cast_sum]
  calc ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ((zerosOfLInBox χ σ T).card : ℝ)
      ≤ ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((M₀ : ℝ) * ((S_fam k χ).card : ℝ)) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun χ hχ =>
          hS_card k χ (Finset.mem_range.mp hk) (Finset.mem_filter.mp hχ).2
    _ = (M₀ : ℝ) * ∑ k ∈ Finset.range Q,
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((S_fam k χ).card : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ (M₀ : ℝ) * (256 * C_prime * ((K + M₀ : ℕ) : ℝ) ^ 4 * Real.exp (8 * ((K + M₀ : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hS_total (Nat.cast_nonneg M₀)
    _ = 256 * C_prime * ((M₀ : ℝ) * ((K + M₀ : ℕ) : ℝ) ^ 4) * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) := by ring
    _ ≤ 256 * C_prime * Real.exp (5 * ((K + M₀ : ℕ) : ℝ)) * Real.exp (8 * ((K + M₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly_exp (by positivity)) (Real.exp_pos _).le
    _ = 256 * C_prime * Real.exp (13 * ((K + M₀ : ℕ) : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ C_big * D ^ (A_big * r) := hexp_final

end RHDirect.Stage11LogFreeDensity

end
