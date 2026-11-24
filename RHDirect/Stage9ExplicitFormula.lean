import RHDirect.Stage7VonMangoldtExplicit
import RHDirect.Stage7HadamardXiProduct
import Mathlib.Topology.Order.IntermediateValue

/-!
# RHDirect.Stage9ExplicitFormula

Completely **UNCONDITIONAL** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) Stage 9 formalization
of three landmark theorems of analytic number theory directly on Mathlib's actual `riemannZeta`,
`Chebyshev.psi`, `Chebyshev.theta`, `Nat.primeCounting`, and `RiemannHypothesis` in pure Mathlib
`v4.33.1`:

1. **Unconditional Full Riemann–von Mangoldt Zero-Count Asymptotic & Good Horizontal Contours**:
   - `abs_backlundS_le_log`: `∃ C > 0, ∀ T ≥ 2, |backlundS T| ≤ C * Real.log T` (with ZERO
     zero-free-line hypotheses on `T`!).
   - `riemann_von_mangoldt_zeta_asymptotic`:
     `∃ C > 0, ∀ T ≥ 2, |xiZeroCount T - (T / (2 π)) log (T / (2 π e))| ≤ C * Real.log T`.
   - `exists_good_contour_height`: for every `T ≥ 4`, there exists `T' ∈ [T, T + 1]` at distance
     `≥ c / log T` from ALL zeros of `riemannZeta` on which `‖-ζ'/ζ(σ ± I * T')‖ ≤ C * (log T)²`
     uniformly for all `-1 ≤ σ ≤ 2`.

2. **Unconditional Von Mangoldt Explicit Formulas for `Chebyshev.psi` & `psi1`**:
   - `von_mangoldt_explicit_formula_psi`:
     `∃ C > 0, ∀ x ≥ 4, ∀ T ≥ 4, T ≤ x → |Chebyshev.psi x - (x - (psiZeroSum x T).re)| ≤ C * (x * (Real.log x)² / T + Real.log x)`.
   - `von_mangoldt_explicit_formula_psi1`:
     `∃ C > 0, ∀ x ≥ 2, |psi1 x - (x² / 2 - (∑' n, (x : ℂ) ^ (xiZeroSeq n + 1) / (xiZeroSeq n * (xiZeroSeq n + 1))).re)| ≤ C * x * Real.log x`.

3. **Von Koch's 1901 Sharp Riemann Hypothesis Theorems**:
   - `von_koch_psi_of_RH`: `RiemannHypothesis → ∃ C > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * √x * (Real.log x)²`.
   - `von_koch_theta_of_RH`: `RiemannHypothesis → ∃ C > 0, ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * √x * (Real.log x)²`.
   - `von_koch_pi_sub_li_of_RH`: `RiemannHypothesis → ∃ C > 0, ∀ x ≥ 3, |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤ C * √x * Real.log x`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset Metric
open scoped BigOperators Real ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage9ExplicitFormula

open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage5ContourExplicit
open RHDirect.Stage6EffectivePNT
open RHDirect.Stage6XiZeroDensity
open RHDirect.Stage7VonMangoldtExplicit
open RHDirect.Stage7HadamardXiProduct

/-! ## Section 1: Unconditional `|S(T)| = O(log T)` & Full Riemann–von Mangoldt Asymptotic -/

/-- Reusable holomorphic zero-quotient helper: if `f` is analytic on an open set `U ⊆ ℂ` with
finite analytic order everywhere on `U`, and every zero of `f` in `U` lies in a finite set `Z ⊆ U`,
then there exists `g : ℂ → ℂ` holomorphic and nonvanishing on `U` such that
`f z = g z * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ` for all `z ∈ U`. -/
private lemma exists_holomorphic_quotient_by_zeros {f : ℂ → ℂ} {U : Set ℂ}
    (hf_an : AnalyticOnNhd ℂ f U) (hntop : ∀ z ∈ U, analyticOrderAt f z ≠ ⊤)
    (Z : Finset ℂ) (hZ_all : ∀ z ∈ U, f z = 0 → z ∈ Z) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧
      ∀ z ∈ U, f z = g z * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ := by
  classical
  let Q : ℂ → ℂ := fun z => ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ
  have hQ_diff : Differentiable ℂ Q := by
    have aux : ∀ s : Finset ℂ,
        Differentiable ℂ (fun z : ℂ => ∏ ρ ∈ s, (z - ρ) ^ analyticOrderNatAt f ρ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [differentiable_const]
      | @insert a t hat ih =>
        have hfun : (fun z : ℂ => ∏ ρ ∈ insert a t, (z - ρ) ^ analyticOrderNatAt f ρ) =
            fun z => (z - a) ^ analyticOrderNatAt f a * ∏ ρ ∈ t, (z - ρ) ^ analyticOrderNatAt f ρ := by
          funext z; exact Finset.prod_insert hat
        rw [hfun]
        exact ((differentiable_id.sub (differentiable_const a)).pow _).mul ih
    exact aux Z
  let g : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun z => f z / Q z)
  have hlocal : ∀ w ∈ U, ∃ q : ℂ → ℂ, AnalyticAt ℂ q w ∧ q w ≠ 0 ∧
      g =ᶠ[𝓝 w] q ∧ f w = q w * Q w := by
    intro w hwU
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hf_an w hwU).analyticOrderAt_ne_top.mp (hntop w hwU)
    have hQ_loc : ∃ Q₁ : ℂ → ℂ, AnalyticAt ℂ Q₁ w ∧ Q₁ w ≠ 0 ∧
        ∀ z : ℂ, Q z = (z - w) ^ analyticOrderNatAt f w * Q₁ z := by
      by_cases hwZ : w ∈ Z
      · refine ⟨fun z => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt f ρ, ?_, ?_, fun z => ?_⟩
        · have hdiff1 : Differentiable ℂ
              (fun z : ℂ => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt f ρ) := by
            have aux : ∀ s : Finset ℂ,
                Differentiable ℂ (fun z : ℂ => ∏ ρ ∈ s, (z - ρ) ^ analyticOrderNatAt f ρ) := by
              intro s
              induction s using Finset.induction_on with
              | empty => simp [differentiable_const]
              | @insert a t hat ih =>
                have hfun : (fun z : ℂ => ∏ ρ ∈ insert a t, (z - ρ) ^ analyticOrderNatAt f ρ) =
                    fun z => (z - a) ^ analyticOrderNatAt f a * ∏ ρ ∈ t, (z - ρ) ^ analyticOrderNatAt f ρ := by
                  funext z; exact Finset.prod_insert hat
                rw [hfun]
                exact ((differentiable_id.sub (differentiable_const a)).pow _).mul ih
            exact aux (Z.erase w)
          exact hdiff1.differentiableOn.analyticAt Filter.univ_mem
        · refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
            pow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_erase.mp hρ).1.symm)
        · exact (Finset.mul_prod_erase Z (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ) hwZ).symm
      · have hfw_ne : f w ≠ 0 := fun hw0 => hwZ (hZ_all w hwU hw0)
        have hord0 : analyticOrderNatAt f w = 0 := by
          have h0 : analyticOrderAt f w = 0 := (hf_an w hwU).analyticOrderAt_eq_zero.mpr hfw_ne
          simp [analyticOrderNatAt, h0]
        refine ⟨Q, hQ_diff.differentiableOn.analyticAt Filter.univ_mem, ?_, fun z => by simp [hord0]⟩
        refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr fun heq => hwZ (heq ▸ hρ))
    obtain ⟨Q₁, hQ₁_an, hQ₁_ne, hQ₁_eq⟩ := hQ_loc
    let q : ℂ → ℂ := fun z => h z / Q₁ z
    have hq_an : AnalyticAt ℂ q w := hh_an.div hQ₁_an hQ₁_ne
    have hq_ne : q w ≠ 0 := div_ne_zero hh_ne hQ₁_ne
    have hev_all : ∀ᶠ z in 𝓝 w,
        f z = (z - w) ^ analyticOrderNatAt f w * h z ∧ Q₁ z ≠ 0 ∧ ContinuousAt q z := by
      filter_upwards [hh_eq, hQ₁_an.continuousAt.eventually_ne hQ₁_ne,
        hq_an.eventually_analyticAt.mono fun z hz => hz.continuousAt] with z h1 h2 h3
      exact ⟨by simpa [smul_eq_mul] using h1, h2, h3⟩
    obtain ⟨V, hV_sub, hV_open, hwV⟩ := _root_.eventually_nhds_iff.mp hev_all
    have hfp : ∀ z ∈ V, z ≠ w → f z / Q z = q z := by
      intro z hzV hzw
      obtain ⟨h1, h2, _⟩ := hV_sub z hzV
      have hpow_ne : (z - w) ^ analyticOrderNatAt f w ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzw)
      rw [h1, hQ₁_eq z]
      dsimp only [q]
      field_simp [hpow_ne, h2]
    have hg_eq : ∀ z ∈ V, g z = q z := by
      intro z hzV
      have htend_q : Tendsto q (𝓝[≠] z) (𝓝 (q z)) :=
        (hV_sub z hzV).2.2.tendsto.mono_left nhdsWithin_le_nhds
      have htend_fp : Tendsto (fun u => f u / Q u) (𝓝[≠] z) (𝓝 (q z)) := by
        refine htend_q.congr' ?_
        have hmem_V : V ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hV_open.mem_nhds hzV)
        have hmem_ne : ({w}ᶜ : Set ℂ) ∈ 𝓝[≠] z := by
          by_cases hzw : z = w
          · subst hzw; exact self_mem_nhdsWithin
          · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzw)
        filter_upwards [Filter.inter_mem hmem_V hmem_ne] with u ⟨huV, huw⟩
        exact (hfp u huV huw).symm
      exact htend_fp.limUnder_eq
    have hfw : f w = q w * Q w := by
      obtain ⟨h1, h2, _⟩ := hV_sub w hwV
      rw [h1, hQ₁_eq w]
      dsimp only [q]
      field_simp [h2]
    exact ⟨q, hq_an, hq_ne, Filter.eventually_of_mem (hV_open.mem_nhds hwV) hg_eq, hfw⟩
  refine ⟨g, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨q, hq_an, _, heq, _⟩ := hlocal w hw
    exact (hq_an.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt
  · obtain ⟨q, _, hq_ne, heq, _⟩ := hlocal w hw
    rwa [heq.self_of_nhds]
  · obtain ⟨q, _, _, heq, hfw⟩ := hlocal w hw
    rwa [heq.self_of_nhds]

/-- Elementary Backlund argument-variation bound on an interval `[a, b]` where `Re(g)` has
finitely many zeros in `(a, b)`. -/
private lemma abs_integral_im_logDeriv_le_of_re_zeros {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg_d : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hg'_cont : ContinuousOn g' (Set.Icc a b))
    (hg_nz : ∀ x ∈ Set.Icc a b, g x ≠ 0)
    (S : Finset ℝ) (hS : ∀ x ∈ Set.Ioo a b, (g x).re = 0 → x ∈ S) :
    |∫ x in a..b, (g' x / g x).im| ≤ ((S.card : ℝ) + 1) * (2 * Real.pi) := by
  classical
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
      · have hstep : |∫ x in a..b, (g' x / g x).im| ≤ 2 * Real.pi := by
          rcases eq_or_lt_of_le hab with rfl | hlt
          · simp; positivity
          · have hre_nz : ∀ x ∈ Set.Ioo a b, (g x).re ≠ 0 := fun x hx h0 => by
              have hmem : x ∈ S_in := Finset.mem_filter.mpr ⟨hS x hx h0, hx⟩
              rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
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
                obtain ⟨z, hz_mem, hz0⟩ := isPreconnected_Ioo.intermediate_value hmid hx hre_cont ⟨hneg.le, hgt.le⟩
                exact hre_nz z hz_mem hz0
              · left
                intro x hx
                by_contra hle
                have hlt' : (g x).re < 0 := lt_of_le_of_ne (not_lt.mp hle) (hre_nz x hx)
                obtain ⟨z, hz_mem, hz0⟩ := isPreconnected_Ioo.intermediate_value hx hmid hre_cont ⟨hlt'.le, hpos.le⟩
                exact hre_nz z hz_mem hz0
            have hpos_case : ∀ (h h' : ℝ → ℂ),
                (∀ x ∈ Set.Icc a b, HasDerivAt h (h' x) x) →
                (∀ x ∈ Set.Ioo a b, 0 < (h x).re) →
                (∀ x ∈ Set.Ioo a b, (h' x / h x).im = (g' x / g x).im) →
                |∫ x in a..b, (g' x / g x).im| ≤ 2 * Real.pi := by
              intro h h' hhd hhpos hheq
              let ε : ℕ → ℝ := fun k => (b - a) / (3 * ((k : ℝ) + 1))
              have hε_pos : ∀ k : ℕ, 0 < ε k := fun k => by dsimp only [ε]; positivity
              have hε_lt : ∀ k : ℕ, a + ε k < b - ε k := fun k => by
                dsimp only [ε]
                have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
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
                    refine hc.congr_deriv ?_; simp [smul_eq_mul, div_eq_mul_inv]
                  have him_d : HasDerivAt (fun t : ℝ => (Complex.log (h t)).im) (h' x / h x).im x :=
                    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hclog
                  rwa [hheq x hx_oo] at him_d
                have hint_k : IntervalIntegrable (fun x => (g' x / g x).im) volume (a + ε k) (b - ε k) :=
                  (hld_cont.mono (by rw [Set.uIcc_of_le (hε_lt k).le]; exact hsub.trans Set.Ioo_subset_Icc_self)).intervalIntegrable
                rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_log hint_k,
                  Complex.log_im, Complex.log_im]
                calc |Complex.arg (h (b - ε k)) - Complex.arg (h (a + ε k))|
                    ≤ |Complex.arg (h (b - ε k))| + |Complex.arg (h (a + ε k))| := abs_sub _ _
                  _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
                  _ = 2 * Real.pi := by ring
              have hε_tend : Tendsto ε atTop (𝓝 0) :=
                tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num)
                  (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
              let F : ℝ → ℝ := fun t => ∫ x in a..t, (g' x / g x).im
              have hF_cont : ContinuousOn F (Set.Icc a b) := by
                intro t ht
                have hint_ab : IntervalIntegrable (fun x => (g' x / g x).im) volume a b :=
                  (hld_cont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
                have hmeas : ∀ s ∈ Set.Icc a b, IntervalIntegrable (fun x => (g' x / g x).im) volume a s :=
                  fun s hs => hint_ab.mono_set (by
                    rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le hab]
                    exact fun y hy => ⟨hy.1, hy.2.trans hs.2⟩)
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
                  rw [Real.norm_eq_abs] at h1; linarith
                have hposM : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
                calc |∫ x in t..s, (g' x / g x).im| ≤ max M 1 * |s - t| := hbd_ts
                  _ < max M 1 * (δ / max M 1) := mul_lt_mul_of_pos_left hdist hposM
                  _ = δ := mul_div_cancel₀ δ hposM.ne'
              have hlim_a : Tendsto (fun k => F (a + ε k)) atTop (𝓝 (F a)) :=
                (hF_cont a ⟨le_rfl, hab⟩).tendsto.comp
                  (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
                    (by simpa using hε_tend.const_add a) (Eventually.of_forall fun k =>
                      ⟨by linarith [hε_pos k], by linarith [hε_lt k, hε_pos k]⟩))
              have hlim_b : Tendsto (fun k => F (b - ε k)) atTop (𝓝 (F b)) :=
                (hF_cont b ⟨hab, le_rfl⟩).tendsto.comp
                  (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
                    (by simpa using tendsto_const_nhds.sub hε_tend) (Eventually.of_forall fun k =>
                      ⟨by linarith [hε_lt k, hε_pos k], by linarith [hε_pos k]⟩))
              have hlim : Tendsto (fun k => |∫ x in (a + ε k)..(b - ε k), (g' x / g x).im|)
                  atTop (𝓝 |∫ x in a..b, (g' x / g x).im|) := by
                have hsub := (hlim_b.sub hlim_a).abs
                have hFa : F a = 0 := intervalIntegral.integral_same
                rw [hFa, sub_zero] at hsub
                refine hsub.congr fun k => ?_
                congr 1; dsimp only [F]
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
              intro x _; rw [neg_div_neg_eq]
        have hnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        nlinarith [Real.pi_pos]
      · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
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

/-- Elementary telescoping bound `∑' k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2 ≤ 3 / 4`. -/
private lemma tsum_inv_add_two_sq_le_three_quarters :
    ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 ≤ 3 / 4 := by
  have hsumm0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simp [one_div, Real.summable_nat_pow_inv]
  have hsumm : Summable (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) :=
    hsumm0.comp_injective fun _ _ h => by omega
  refine hsumm.tsum_le_of_sum_range_le fun N => ?_
  have hbound : ∀ M : ℕ, ∑ k ∈ Finset.range M, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 ≤
      3 / 4 - (if M = 0 then 3 / 4 else 1 / ((M + 1 : ℕ) : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      cases m with
      | zero => simp; norm_num
      | succ j =>
        simp only [Nat.succ_ne_zero, ↓reduceIte] at ih ⊢
        have hstep : (1 : ℝ) / ((j + 1 + 2 : ℕ) : ℝ) ^ 2 ≤
            1 / ((j + 1 + 1 : ℕ) : ℝ) - 1 / ((j + 1 + 1 + 1 : ℕ) : ℝ) := by
          push_cast
          have h1 : 1 / ((j : ℝ) + 1 + 1) - 1 / ((j : ℝ) + 1 + 1 + 1) =
              1 / (((j : ℝ) + 2) * ((j : ℝ) + 3)) := by
            have ha : (j : ℝ) + 2 ≠ 0 := by positivity
            have hb : (j : ℝ) + 3 ≠ 0 := by positivity
            field_simp [ha, hb]; ring
          rw [h1]
          refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
          nlinarith [Nat.cast_nonneg (α := ℝ) j]
        linarith
  have h1 := hbound N
  split_ifs at h1 with hN
  · linarith
  · have : (0 : ℝ) ≤ 1 / ((N + 1 : ℕ) : ℝ) := by positivity
    linarith

/-- Lower bound `1 / 4 ≤ (riemannZeta s).re` on `Re(s) ≥ 2`. -/
private lemma quarter_le_re_riemannZeta_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    (1 / 4 : ℝ) ≤ (riemannZeta s).re := by
  have hs1 : 1 < s.re := by linarith
  have hL : riemannZeta s = LSeries (fun _ => (1 : ℂ)) s := by
    rw [← DirichletCharacter.LFunction_modOne_eq,
      DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) hs1]
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn]
      rw [Stage2DirichletAP.principal_char_apply_nat, if_pos (Nat.coprime_one_right n)]
  rw [hL]
  have hsum : LSeriesSummable (fun _ => (1 : ℂ)) s := by
    rw [LSeriesSummable]
    have h1 := DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ 1) hs1
    refine h1.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn]
      rw [Stage2DirichletAP.principal_char_apply_nat, if_pos (Nat.coprime_one_right n)]
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hhead : ∑ i ∈ Finset.range 2, LSeries.term (fun _ => (1 : ℂ)) s i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, LSeries.term_zero, zero_add,
      LSeries.term_of_ne_zero one_ne_zero]
    simp
  rw [hhead] at hsplit
  have htail_le : ‖∑' k : ℕ, LSeries.term (fun _ => (1 : ℂ)) s (k + 2)‖ ≤ 3 / 4 := by
    have hsumm0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
      simp [one_div, Real.summable_nat_pow_inv]
    have hsumm_real : Summable (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) :=
      hsumm0.comp_injective fun _ _ h => by omega
    have hterm : ∀ k : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) s (k + 2)‖ ≤ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      intro k
      have hk_pos : 0 < k + 2 := by omega
      have hk1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.one_le_cast.mpr hk_pos
      rw [LSeries.term_of_ne_zero hk_pos.ne', norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hk_pos]
      have hpow : ((k + 2 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) ^ s.re := by
        simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hk1 hs
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) hpow
    have hsumm_norm : Summable (fun k : ℕ => ‖LSeries.term (fun _ => (1 : ℂ)) s (k + 2)‖) :=
      hsumm_real.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    calc ‖∑' k : ℕ, LSeries.term (fun _ => (1 : ℂ)) s (k + 2)‖
        ≤ ∑' k : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) s (k + 2)‖ := norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := hsumm_norm.tsum_le_tsum hterm hsumm_real
      _ ≤ 3 / 4 := tsum_inv_add_two_sq_le_three_quarters
  have hre_tail : -(3 / 4 : ℝ) ≤ (∑' k : ℕ, LSeries.term (fun _ => (1 : ℂ)) s (k + 2)).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans htail_le)).1
  unfold LSeries
  rw [← hsplit, Complex.add_re, Complex.one_re]
  linarith

/-- Conjugation symmetry of Mathlib's `riemannZeta` away from `s = 1`. -/
private lemma riemannZeta_conj_of_ne_one {s : ℂ} (hs1 : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  have h1 : (starRingEnd ℂ s) ≠ 1 := fun h => hs1 (by simpa using congrArg (starRingEnd ℂ) h)
  by_cases hs0 : s = 0
  · subst hs0; simp [riemannZeta_zero, map_div₀, map_neg, map_one, map_ofNat]
  · have h0' : starRingEnd ℂ s ≠ 0 := (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hs0
    by_cases hG : s.Gammaℝ = 0
    · obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hG
      have hreal : starRingEnd ℂ s = s := by
        rw [hn]; simp [map_neg, map_mul, map_ofNat, map_natCast]
      rw [hreal]
      have hn_pos : 1 ≤ n := by
        cases n with
        | zero => simp at hn; exact absurd hn hs0
        | succ m => omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have htriv : riemannZeta s = 0 := by
        rw [hn]
        have harg : -(2 * ((m.succ : ℕ) : ℂ)) = -2 * ((m : ℂ) + 1) := by push_cast; ring
        rw [harg]
        exact riemannZeta_neg_two_mul_nat_add_one m
      rw [htriv, map_zero]
    · have hG_conj : (starRingEnd ℂ s).Gammaℝ = starRingEnd ℂ s.Gammaℝ := by
        rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
        congr 1
        · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_pos.ne'),
            Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_pos.ne'),
            ← Complex.exp_conj, map_mul, ← Complex.ofReal_log Real.pi_pos.le,
            Complex.conj_ofReal, map_div₀, map_neg, map_ofNat]
        · rw [← Complex.Gamma_conj]
          congr 1; rw [map_div₀, map_ofNat]
      have hG' : (starRingEnd ℂ s).Gammaℝ ≠ 0 := by
        rw [hG_conj]; exact (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hG
      have hxi1 := xi_eq_mul_Gammaℝ_mul_riemannZeta hs0 hs1 hG
      have hxi2 := xi_eq_mul_Gammaℝ_mul_riemannZeta h0' h1 hG'
      have hxi_c := Stage6XiZeroDensity.xi_conj s
      rw [hxi1, hxi2, map_mul, map_mul, map_mul, map_sub, map_one, ← hG_conj] at hxi_c
      have hfac_ne : starRingEnd ℂ s * (starRingEnd ℂ s - 1) * (starRingEnd ℂ s).Gammaℝ ≠ 0 :=
        mul_ne_zero (mul_ne_zero h0' (sub_ne_zero.mpr h1)) hG'
      exact mul_left_cancel₀ hfac_ne hxi_c

/-- **UNCONDITIONAL BACKLUND–JENSEN BOUND ON `|S(T)|` FOR ALL `T ≥ 3/2`** (with ZERO
zero-free-line hypotheses on `T`!):
`∃ C > 0, ∀ T ≥ 3 / 2, |backlundS T| ≤ C * Real.log (T + 2)`. -/
theorem abs_backlundS_le_log_add_two :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 / 2 ≤ T →
      |Stage7VonMangoldtExplicit.backlundS T| ≤ C * Real.log (T + 2) := by
  classical
  have hlog76_pos : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C_J : ℝ := (Real.log 2000 + 1) / Real.log (7 / 6)
  have hCJ_pos : 0 < C_J := by
    have : 0 < Real.log 2000 := Real.log_pos (by norm_num)
    exact div_pos (by linarith) hlog76_pos
  set C : ℝ := 4 + 2 * C_J
  refine ⟨C, by positivity, fun T hT => ?_⟩
  have hT_pos : 0 < T := by linarith
  have hlogT_ge1 : 1 ≤ Real.log (T + 2) := by
    have h3 : Real.exp 1 ≤ T + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h3)
  -- Part 1: Vertical integral `|∫_0^T Re(ζ'/ζ(2 + i t)) dt| ≤ 2 * π`
  have hvert_bd : |∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re| ≤
      2 * Real.pi := by
    have hZ_an : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z (hz : z ≠ 1) => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_compl_singleton
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun y : ℝ => (Complex.log (riemannZeta ((2 : ℂ) + I * (y : ℂ)))).im)
          (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re t := by
      intro t _
      have hslit : riemannZeta ((2 : ℂ) + I * (t : ℂ)) ∈ Complex.slitPlane :=
        Or.inl (lt_of_lt_of_le (by norm_num) (quarter_le_re_riemannZeta_of_two_le_re (by simp)))
      have hne1 : ((2 : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this
      have hmap : HasDerivAt (fun y : ℝ => (2 : ℂ) + I * (y : ℂ)) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.const_mul I).const_add (2 : ℂ)
      have hcomp : HasDerivAt (fun y : ℝ => riemannZeta ((2 : ℂ) + I * (y : ℂ)))
          (deriv riemannZeta ((2 : ℂ) + I * (t : ℂ)) * I) t := by
        have hc := HasDerivAt.scomp t (differentiableAt_riemannZeta hne1).hasDerivAt hmap
        refine hc.congr_deriv ?_; simp [smul_eq_mul, mul_comm]
      have hlog : HasDerivAt (fun y : ℝ => Complex.log (riemannZeta ((2 : ℂ) + I * (y : ℂ))))
          (deriv riemannZeta ((2 : ℂ) + I * (t : ℂ)) * I / riemannZeta ((2 : ℂ) + I * (t : ℂ))) t := by
        have hc := HasDerivAt.scomp t (Complex.hasDerivAt_log hslit) hcomp
        refine hc.congr_deriv ?_; simp [smul_eq_mul, div_eq_mul_inv]
      have him_d := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
      refine him_d.congr_deriv ?_
      change (deriv riemannZeta ((2 : ℂ) + I * (t : ℂ)) * I / riemannZeta ((2 : ℂ) + I * (t : ℂ))).im = _
      rw [mul_div_right_comm, logDeriv_apply, Complex.mul_im]; simp
    have hcont : ContinuousOn
        (fun t : ℝ => (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re) (Set.uIcc 0 T) :=
      Complex.continuous_re.comp_continuousOn fun t _ => by
        have hne1 : ((2 : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this
        have hnz2 : riemannZeta ((2 : ℂ) + I * (t : ℂ)) ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re (by simp)
        have hld : ContinuousAt (logDeriv riemannZeta) ((2 : ℂ) + I * (t : ℂ)) :=
          (hZ_an _ hne1).deriv.continuousAt.div (hZ_an _ hne1).continuousAt hnz2
        exact (ContinuousAt.comp (f := fun y : ℝ => (2 : ℂ) + I * (y : ℂ)) hld (by fun_prop)).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
      Complex.log_im, Complex.log_im]
    calc |Complex.arg _ - Complex.arg _|
        ≤ |Complex.arg _| + |Complex.arg _| := abs_sub _ _
      _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
      _ = 2 * Real.pi := by ring
  -- Part 2: Jensen bound on `f(w) = (1/2) (ζ(2 + w + i T) + ζ(2 + w - i T))` with `r = 3/2, R = 7/4`
  let G : ℂ → ℂ := fun z =>
    (1 / 2 : ℂ) * (riemannZeta (z + I * (T : ℂ)) + riemannZeta (z - I * (T : ℂ)))
  let f : ℂ → ℂ := fun w => G ((2 : ℂ) + w)
  -- For `w ∈ closedBall 0 (7/4)`, `2 + w ± I * T` avoids `1` by at least `1/20` and has `Re ≥ 1/4`.
  have hw_props : ∀ w ∈ Metric.closedBall (0 : ℂ) (7 / 4),
      (1 / 4 : ℝ) ≤ ((2 : ℂ) + w).re ∧ ((2 : ℂ) + w).re ≤ 4 ∧
      (1 / 20 : ℝ) ≤ ‖(2 : ℂ) + w + I * (T : ℂ) - 1‖ ∧
      (1 / 20 : ℝ) ≤ ‖(2 : ℂ) + w - I * (T : ℂ) - 1‖ := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    have hw_re := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
    have hnorm1 : (9 / 5 : ℝ) ≤ ‖(1 : ℂ) + I * (T : ℂ)‖ := by
      have hsq : ((9 / 5 : ℝ)) ^ 2 ≤ ‖(1 : ℂ) + I * (T : ℂ)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
          zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
          Complex.one_im, Complex.mul_im, one_mul, zero_add]
        nlinarith
      nlinarith [norm_nonneg ((1 : ℂ) + I * (T : ℂ))]
    have hnorm2 : (9 / 5 : ℝ) ≤ ‖(1 : ℂ) - I * (T : ℂ)‖ := by
      have hsq : ((9 / 5 : ℝ)) ^ 2 ≤ ‖(1 : ℂ) - I * (T : ℂ)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
          zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.sub_im,
          Complex.one_im, Complex.mul_im, one_mul, zero_add, zero_sub]
        nlinarith
      nlinarith [norm_nonneg ((1 : ℂ) - I * (T : ℂ))]
    have htri1 : ‖(1 : ℂ) + I * (T : ℂ)‖ - ‖w‖ ≤ ‖(2 : ℂ) + w + I * (T : ℂ) - 1‖ := by
      have hrew : (2 : ℂ) + w + I * (T : ℂ) - 1 = ((1 : ℂ) + I * (T : ℂ)) - (-w) := by ring
      rw [hrew]
      simpa [norm_neg] using norm_sub_norm_le ((1 : ℂ) + I * (T : ℂ)) (-w)
    have htri2 : ‖(1 : ℂ) - I * (T : ℂ)‖ - ‖w‖ ≤ ‖(2 : ℂ) + w - I * (T : ℂ) - 1‖ := by
      have hrew : (2 : ℂ) + w - I * (T : ℂ) - 1 = ((1 : ℂ) - I * (T : ℂ)) - (-w) := by ring
      rw [hrew]
      simpa [norm_neg] using norm_sub_norm_le ((1 : ℂ) - I * (T : ℂ)) (-w)
    exact ⟨by simp; linarith, by simp; linarith, by linarith, by linarith⟩
  have hf_diff : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (7 / 4)) := by
    intro w hw
    have hp := hw_props w hw
    have hne1 : (2 : ℂ) + w + I * (T : ℂ) ≠ 1 := fun h => by
      rw [h, sub_self, norm_zero] at hp; linarith
    have hne2 : (2 : ℂ) + w - I * (T : ℂ) ≠ 1 := fun h => by
      rw [h, sub_self, norm_zero] at hp; linarith
    have hd1 : DifferentiableAt ℂ (fun u : ℂ => riemannZeta ((2 : ℂ) + u + I * (T : ℂ))) w :=
      (differentiableAt_riemannZeta hne1).comp w (by fun_prop)
    have hd2 : DifferentiableAt ℂ (fun u : ℂ => riemannZeta ((2 : ℂ) + u - I * (T : ℂ))) w :=
      (differentiableAt_riemannZeta hne2).comp w (by fun_prop)
    exact ((differentiableAt_const _).mul (hd1.add hd2)).differentiableWithinAt
  have hG_real : ∀ σ : ℝ, G (σ : ℂ) = ((riemannZeta ((σ : ℂ) + I * (T : ℂ))).re : ℂ) := by
    intro σ
    have hne1 : (σ : ℂ) + I * (T : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hconj_arg : (σ : ℂ) - I * (T : ℂ) = starRingEnd ℂ ((σ : ℂ) + I * (T : ℂ)) :=
      Complex.ext (by simp) (by simp)
    dsimp only [G]
    rw [hconj_arg, riemannZeta_conj_of_ne_one hne1]
    apply Complex.ext
    · simp; ring
    · simp
  have hf0_ge : (1 / 4 : ℝ) ≤ ‖f 0‖ := by
    dsimp only [f]
    rw [add_zero, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, hG_real 2, Complex.norm_real, Real.norm_eq_abs]
    exact (quarter_le_re_riemannZeta_of_two_le_re (by simp)).trans (le_abs_self _)
  have hf0_ne : f 0 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hf0_ge; norm_num at hf0_ge
  set M : ℝ := 500 * (T + 2)
  have hM_bd : ∀ w ∈ Metric.sphere (0 : ℂ) (7 / 4), ‖f w‖ ≤ M := by
    intro w hw
    have hw_cb : w ∈ Metric.closedBall (0 : ℂ) (7 / 4) := Metric.sphere_subset_closedBall hw
    have hw_norm : ‖w‖ = 7 / 4 := mem_sphere_zero_iff_norm.mp hw
    obtain ⟨hre_lo, hre_hi, hdist1, hdist2⟩ := hw_props w hw_cb
    have hne1 : (2 : ℂ) + w + I * (T : ℂ) ≠ 1 := fun h => by
      rw [h, sub_self, norm_zero] at hdist1; linarith
    have hne2 : (2 : ℂ) + w - I * (T : ℂ) ≠ 1 := fun h => by
      rw [h, sub_self, norm_zero] at hdist2; linarith
    have hnorm_sum1 : ‖(2 : ℂ) + w + I * (T : ℂ)‖ ≤ T + 4 := by
      have h1 := norm_add_le ((2 : ℂ) + w) (I * (T : ℂ))
      have h2 := norm_add_le (2 : ℂ) w
      rw [hw_norm, Complex.norm_ofNat] at h2
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hT_pos.le] at h1
      linarith
    have hnorm_sum2 : ‖(2 : ℂ) + w - I * (T : ℂ)‖ ≤ T + 4 := by
      have h1 := norm_sub_le ((2 : ℂ) + w) (I * (T : ℂ))
      have h2 := norm_add_le (2 : ℂ) w
      rw [hw_norm, Complex.norm_ofNat] at h2
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hT_pos.le] at h1
      linarith
    have hZ1 : ‖riemannZeta ((2 : ℂ) + w + I * (T : ℂ))‖ ≤ M := by
      have hre1 : 1 / 4 ≤ ((2 : ℂ) + w + I * (T : ℂ)).re := by simpa using hre_lo
      have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith) hne1
      have hinv : 1 / ‖(2 : ℂ) + w + I * (T : ℂ) - 1‖ ≤ 20 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hdiv : ‖(2 : ℂ) + w + I * (T : ℂ)‖ / ((2 : ℂ) + w + I * (T : ℂ)).re ≤ 4 * (T + 4) := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      dsimp only [M]; linarith
    have hZ2 : ‖riemannZeta ((2 : ℂ) + w - I * (T : ℂ))‖ ≤ M := by
      have hre2 : 1 / 4 ≤ ((2 : ℂ) + w - I * (T : ℂ)).re := by simpa using hre_lo
      have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith) hne2
      have hinv : 1 / ‖(2 : ℂ) + w - I * (T : ℂ) - 1‖ ≤ 20 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hdiv : ‖(2 : ℂ) + w - I * (T : ℂ)‖ / ((2 : ℂ) + w - I * (T : ℂ)).re ≤ 4 * (T + 4) := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      dsimp only [M]; linarith
    dsimp only [f, G]
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    calc (1 / 2 : ℝ) * ‖riemannZeta ((2 : ℂ) + w + I * (T : ℂ)) +
            riemannZeta ((2 : ℂ) + w - I * (T : ℂ))‖
        ≤ (1 / 2 : ℝ) * (M + M) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hZ1 hZ2)) (by norm_num)
      _ = M := by ring
  have hcard_le : ∀ S : Finset ℝ,
      (∀ σ ∈ S, σ ∈ Set.Ioo (1 / 2 : ℝ) 2 ∧ (riemannZeta ((σ : ℂ) + I * (T : ℂ))).re = 0) →
      (S.card : ℝ) ≤ C_J * Real.log (T + 2) := by
    intro S hS
    set Z' : Finset ℂ := S.image fun σ => ((σ - 2 : ℝ) : ℂ)
    have hcard_eq : Z'.card = S.card :=
      Finset.card_image_of_injective S fun a b h => by
        have := Complex.ofReal_injective h; linarith
    have hZ'_ball : ∀ w ∈ Z', w ∈ Metric.closedBall (0 : ℂ) (3 / 2) := by
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
    have hf_dc : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (7 / 4)) := by
      refine ⟨hf_diff.mono Metric.ball_subset_closedBall, ?_⟩
      rw [closure_ball (0 : ℂ) (by norm_num : (7 / 4 : ℝ) ≠ 0)]
      exact hf_diff.continuousOn
    have hj := Stage5JensenHadamard.jensen_zero_count_le
      (r := 3 / 2) (R := 7 / 4) (M := M) (by norm_num) (by norm_num)
      hf_dc hf0_ne hM_bd Z' hZ'_ball hZ'_zero
    rw [hcard_eq, show (7 / 4 : ℝ) / (3 / 2) = 7 / 6 by norm_num] at hj
    have hratio : M / ‖f 0‖ ≤ 2000 * (T + 2) := by
      have h1 : M / ‖f 0‖ ≤ M / (1 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hf0_ge
      refine h1.trans_eq ?_; dsimp only [M]; ring
    have hlog_le : Real.log (M / ‖f 0‖) ≤ (Real.log 2000 + 1) * Real.log (T + 2) := by
      calc Real.log (M / ‖f 0‖)
          ≤ Real.log (2000 * (T + 2)) :=
            Real.log_le_log (div_pos (by positivity) (norm_pos_iff.mpr hf0_ne)) hratio
        _ = Real.log 2000 + Real.log (T + 2) := Real.log_mul (by norm_num) (by positivity)
        _ ≤ Real.log 2000 * Real.log (T + 2) + Real.log (T + 2) := by
            nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2000)]
        _ = (Real.log 2000 + 1) * Real.log (T + 2) := by ring
    calc (S.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (7 / 6) := hj
      _ ≤ ((Real.log 2000 + 1) * Real.log (T + 2)) / Real.log (7 / 6) :=
          div_le_div_of_nonneg_right hlog_le hlog76_pos.le
      _ = C_J * Real.log (T + 2) := by dsimp only [C_J]; ring
  have hfin_re : {σ : ℝ | σ ∈ Set.Ioo (1 / 2 : ℝ) 2 ∧ (riemannZeta ((σ : ℂ) + I * (T : ℂ))).re = 0}.Finite := by
    by_contra hinf
    obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (Nat.floor (C_J * Real.log (T + 2)) + 1)
    have hle := hcard_le S fun σ hσ => hSsub hσ
    have hgt : C_J * Real.log (T + 2) < (S.card : ℝ) := by
      rw [hScard]; push_cast; exact Nat.lt_floor_add_one _
    linarith
  set S_re : Finset ℝ := hfin_re.toFinset
  have hS_re_card : (S_re.card : ℝ) ≤ C_J * Real.log (T + 2) :=
    hcard_le S_re fun σ hσ => hfin_re.mem_toFinset.mp hσ
  -- Part 3: Remove any zeros of `ζ(· + i T)` on `[1/2, 2]` by dividing out a real polynomial `P`,
  -- leaving `Im(logDeriv ζ)` unchanged a.e. and preserving `Re(h) = 0 → Re(ζ) = 0`!
  let Z_box : Finset ℂ := (finite_riemannZeta_zeros_le_height (T + 1)).toFinset
  let Z_off : Finset ℂ := Z_box.filter fun ρ => ρ.im ≠ T
  obtain ⟨δ, hδ_pos, hδ_lt_half, hδ_avoid⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ ρ ∈ Z_off, δ < |ρ.im - T| := by
    by_cases hemp : Z_off = ∅
    · exact ⟨1 / 4, by norm_num, by norm_num, fun ρ hρ => by rw [hemp] at hρ; exact absurd hρ (Finset.notMem_empty _)⟩
    · have hne : Z_off.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      set m := Z_off.inf' hne fun ρ => |ρ.im - T|
      have hm_pos : 0 < m := by
        rw [Finset.lt_inf'_iff]
        intro ρ hρ
        exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hρ).2)
      refine ⟨min (1 / 4) (m / 2), lt_min (by norm_num) (by linarith),
        (min_le_left _ _).trans_lt (by norm_num), fun ρ hρ => ?_⟩
      have h1 : m ≤ |ρ.im - T| := Finset.inf'_le (fun w => |w.im - T|) hρ
      have h2 : min (1 / 4) (m / 2) ≤ m / 2 := min_le_right _ _
      linarith
  let U : Set ℂ := {z : ℂ | 1 / 4 < z.re ∧ z.re < 3 ∧ |z.im| < δ}
  have hU_open : IsOpen U := by
    have h1 : IsOpen {z : ℂ | 1 / 4 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z.re < 3} := isOpen_lt Complex.continuous_re continuous_const
    have h3 : IsOpen {z : ℂ | |z.im| < δ} := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    have hEq : U = {z : ℂ | 1 / 4 < z.re} ∩ ({z : ℂ | z.re < 3} ∩ {z : ℂ | |z.im| < δ}) := rfl
    rw [hEq]
    exact h1.inter (h2.inter h3)
  let fT : ℂ → ℂ := fun z => riemannZeta (z + I * (T : ℂ))
  have hfT_ne1 : ∀ z ∈ U, z + I * (T : ℂ) ≠ 1 := fun z hz h1 => by
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
      Complex.I_im, Complex.ofReal_re, one_mul, zero_add, Complex.one_im] at him
    have := (abs_lt.mp hz.2.2).1
    linarith
  have hfT_an : AnalyticOnNhd ℂ fT U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => ((differentiableAt_riemannZeta (hfT_ne1 z hz)).comp z (by fun_prop)).differentiableWithinAt)
      hU_open
  have hfT_ntop : ∀ z ∈ U, analyticOrderAt fT z ≠ ⊤ := by
    intro z hz htop
    have hconv : Convex ℝ U := by
      intro x hx y hy a b ha hb hab
      refine ⟨?_, ?_, ?_⟩
      · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          subst hb1; linarith [hy.1]
        · nlinarith [hx.1, hy.1]
      · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          subst hb1; linarith [hy.2.1]
        · nlinarith [hx.2.1, hy.2.1]
      · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero]
        have hx' := abs_lt.mp hx.2.2
        have hy' := abs_lt.mp hy.2.2
        rw [abs_lt]
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          subst hb1; constructor <;> linarith
        · constructor <;> nlinarith
    have h2U : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num, by simp [hδ_pos]⟩
    have h0 := hfT_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconv.isPreconnected hz
      (analyticOrderAt_eq_top.mp htop) h2U
    exact riemannZeta_ne_zero_of_one_le_re (s := (2 : ℂ) + I * (T : ℂ)) (by simp) h0
  let Z_real : Finset ℝ := (Z_box.filter fun ρ => ρ.im = T).image Complex.re
  let Z_T : Finset ℂ := Z_real.image (fun σ : ℝ => (σ : ℂ))
  have hZ_T_all : ∀ z ∈ U, fT z = 0 → z ∈ Z_T := by
    intro z hz hf0
    have hre0 : 0 < (z + I * (T : ℂ)).re := by simp; linarith [hz.1]
    have hre1 : (z + I * (T : ℂ)).re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hf0
    have him_le : |(z + I * (T : ℂ)).im| ≤ T + 1 := by
      have him_eq : (z + I * (T : ℂ)).im = z.im + T := by simp
      rw [him_eq]
      have habs := abs_lt.mp hz.2.2
      rw [abs_of_pos (by linarith)]; linarith
    have hmem_box : z + I * (T : ℂ) ∈ Z_box :=
      (finite_riemannZeta_zeros_le_height (T + 1)).mem_toFinset.mpr ⟨hre0, hre1, hf0, him_le⟩
    have him_eqT : (z + I * (T : ℂ)).im = T := by
      by_contra hne
      have hmem_off : z + I * (T : ℂ) ∈ Z_off := Finset.mem_filter.mpr ⟨hmem_box, hne⟩
      have hgt := hδ_avoid _ hmem_off
      have hdiff : (z + I * (T : ℂ)).im - T = z.im := by simp
      rw [hdiff] at hgt
      linarith [hz.2.2]
    have hzim0 : z.im = 0 := by
      have : (z + I * (T : ℂ)).im = z.im + T := by simp
      linarith
    have hz_eq : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim0])
    rw [hz_eq]
    exact Finset.mem_image.mpr ⟨z.re, Finset.mem_image.mpr
      ⟨z + I * (T : ℂ), Finset.mem_filter.mpr ⟨hmem_box, him_eqT⟩, by simp⟩, rfl⟩
  obtain ⟨h, hh_diff, hh_nz, hfT_eq⟩ := exists_holomorphic_quotient_by_zeros hfT_an hfT_ntop Z_T hZ_T_all
  have hIcc_sub_U : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, (σ : ℂ) ∈ U := fun σ hσ =>
    ⟨by simp; linarith [hσ.1], by simp; linarith [hσ.2], by simp [hδ_pos]⟩
  have hh_an : AnalyticOnNhd ℂ h U := hh_diff.analyticOnNhd hU_open
  have hh_deriv_real : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      HasDerivAt (fun x : ℝ => h (x : ℂ)) (deriv h (σ : ℂ)) σ := by
    intro σ hσ
    have hd := (hh_diff (σ : ℂ) (hIcc_sub_U σ hσ)).differentiableAt (hU_open.mem_nhds (hIcc_sub_U σ hσ))
    have hc := HasDerivAt.scomp σ hd.hasDerivAt (hasDerivAt_id σ).ofReal_comp
    refine hc.congr_deriv ?_; simp [smul_eq_mul]
  have hh'_cont : ContinuousOn (fun σ : ℝ => deriv h (σ : ℂ)) (Set.Icc (1 / 2 : ℝ) 2) := fun σ hσ =>
    ((hh_an _ (hIcc_sub_U σ hσ)).deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hh_nz_Icc : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, h (σ : ℂ) ≠ 0 := fun σ hσ => hh_nz (σ : ℂ) (hIcc_sub_U σ hσ)
  -- Every zero of `Re(h σ)` in `(1/2, 2)` is a zero of `Re(ζ(σ + i T))` hence in `S_re`!
  have hh_re_zeros : ∀ σ ∈ Set.Ioo (1 / 2 : ℝ) 2, (h (σ : ℂ)).re = 0 → σ ∈ S_re := by
    intro σ hσ hre0
    have hfac := hfT_eq (σ : ℂ) (hIcc_sub_U σ (Set.Ioo_subset_Icc_self hσ))
    have hprod_real : (∏ ρ ∈ Z_T, ((σ : ℂ) - ρ) ^ analyticOrderNatAt fT ρ).im = 0 := by
      have hreal_prod : ∏ ρ ∈ Z_T, ((σ : ℂ) - ρ) ^ analyticOrderNatAt fT ρ =
          ((∏ a ∈ Z_real, (σ - a) ^ analyticOrderNatAt fT (a : ℂ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_prod]
        dsimp only [Z_T]
        rw [Finset.prod_image (fun a _ b _ h => Complex.ofReal_injective h)]
        refine Finset.prod_congr rfl fun a _ => by push_cast; rfl
      rw [hreal_prod, Complex.ofReal_im]
    have hζ_re0 : (riemannZeta ((σ : ℂ) + I * (T : ℂ))).re = 0 := by
      change (fT (σ : ℂ)).re = 0
      rw [hfac, Complex.mul_re, hre0, hprod_real]; ring
    exact hfin_re.mem_toFinset.mpr ⟨hσ, hζ_re0⟩
  have hh_int_bd : |∫ σ in (1 / 2 : ℝ)..2, (deriv h (σ : ℂ) / h (σ : ℂ)).im| ≤
      ((S_re.card : ℝ) + 1) * (2 * Real.pi) :=
    abs_integral_im_logDeriv_le_of_re_zeros (by norm_num) hh_deriv_real hh'_cont hh_nz_Icc S_re hh_re_zeros
  -- For `σ ∈ [1/2, 2] \ Z_real`, `(logDeriv riemannZeta (σ + i T)).im = (deriv h σ / h σ).im`!
  have hhoriz_eq : ∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im =
      ∫ σ in (1 / 2 : ℝ)..2, (deriv h (σ : ℂ) / h (σ : ℂ)).im := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnotZ : ∀ᵐ σ ∂volume, σ ∉ (Z_real : Set ℝ) := by
      rw [ae_iff]
      have hEq : {σ : ℝ | ¬ σ ∉ (Z_real : Set ℝ)} = (Z_real : Set ℝ) := by ext; simp
      rw [hEq]; exact Z_real.finite_toSet.countable.measure_zero volume
    filter_upwards [hnotZ] with σ hσ_not hσ_uIoc
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ_uIoc
    have hσ_Icc : σ ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨hσ_uIoc.1.le, hσ_uIoc.2⟩
    have hσU : (σ : ℂ) ∈ U := hIcc_sub_U σ hσ_Icc
    let Q : ℂ → ℂ := fun z => ∏ ρ ∈ Z_T, (z - ρ) ^ analyticOrderNatAt fT ρ
    have hQ_ne : Q (σ : ℂ) ≠ 0 := by
      dsimp only [Q]
      refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun hEq => ?_)
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hρ
      exact hσ_not (Finset.mem_coe.mpr ((Complex.ofReal_injective hEq) ▸ ha))
    have hQ_diff : DifferentiableAt ℂ Q (σ : ℂ) := by
      dsimp only [Q]
      exact DifferentiableAt.fun_finsetProd fun ρ _ =>
        (differentiableAt_id.sub (differentiableAt_const ρ)).pow _
    have hh_d : DifferentiableAt ℂ h (σ : ℂ) :=
      (hh_diff (σ : ℂ) hσU).differentiableAt (hU_open.mem_nhds hσU)
    have hfT_ev : fT =ᶠ[𝓝 (σ : ℂ)] fun z => h z * Q z :=
      Filter.eventually_of_mem (hU_open.mem_nhds hσU) hfT_eq
    have hld_fT : logDeriv fT (σ : ℂ) = deriv h (σ : ℂ) / h (σ : ℂ) + logDeriv Q (σ : ℂ) := by
      rw [logDeriv_apply, hfT_ev.deriv_eq, (hh_d.hasDerivAt.fun_mul hQ_diff.hasDerivAt).deriv,
        hfT_ev.self_of_nhds, logDeriv_apply]
      have hhne := hh_nz (σ : ℂ) hσU
      field_simp [hhne, hQ_ne]
    have hld_Q_im : (logDeriv Q (σ : ℂ)).im = 0 := by
      have hld_Q := logDeriv_prod (s := Z_T) (f := fun ρ (z : ℂ) => (z - ρ) ^ analyticOrderNatAt fT ρ)
        (x := (σ : ℂ)) (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun hEq => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hρ
          exact hσ_not (Finset.mem_coe.mpr ((Complex.ofReal_injective hEq) ▸ ha))))
        (fun ρ _ => (differentiableAt_id.sub (differentiableAt_const ρ)).pow _)
      change (logDeriv Q (σ : ℂ)).im = 0
      dsimp only [Q]
      rw [hld_Q, Complex.im_sum]
      refine Finset.sum_eq_zero fun ρ hρ => ?_
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hρ
      rw [logDeriv_apply]
      have hd : HasDerivAt (fun z : ℂ => (z - (a : ℂ)) ^ analyticOrderNatAt fT (a : ℂ))
          ((analyticOrderNatAt fT (a : ℂ) : ℂ) * ((σ : ℂ) - (a : ℂ)) ^ (analyticOrderNatAt fT (a : ℂ) - 1)) (σ : ℂ) := by
        simpa using ((hasDerivAt_id (σ : ℂ)).sub_const (a : ℂ)).fun_pow (analyticOrderNatAt fT (a : ℂ))
      rw [hd.deriv]
      have hreal : ((analyticOrderNatAt fT (a : ℂ) : ℂ) * ((σ : ℂ) - (a : ℂ)) ^ (analyticOrderNatAt fT (a : ℂ) - 1)) /
          ((σ : ℂ) - (a : ℂ)) ^ analyticOrderNatAt fT (a : ℂ) =
          (((analyticOrderNatAt fT (a : ℂ) : ℝ) * (σ - a) ^ (analyticOrderNatAt fT (a : ℂ) - 1) /
            (σ - a) ^ analyticOrderNatAt fT (a : ℂ) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [hreal, Complex.ofReal_im]
    have hld_shift : logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ)) = logDeriv fT (σ : ℂ) := by
      rw [logDeriv_apply, logDeriv_apply]
      have hd : HasDerivAt fT (deriv riemannZeta ((σ : ℂ) + I * (T : ℂ))) (σ : ℂ) := by
        have h1 := (differentiableAt_riemannZeta (hfT_ne1 (σ : ℂ) hσU)).hasDerivAt.comp (σ : ℂ)
          ((hasDerivAt_id (σ : ℂ)).add_const (I * (T : ℂ)))
        simpa [fT, Function.comp_def] using h1
      rw [hd.deriv]
    rw [hld_shift, hld_fT, Complex.add_im, hld_Q_im, add_zero]
  -- Combine vertical + horizontal bounds!
  unfold Stage7VonMangoldtExplicit.backlundS Stage7VonMangoldtExplicit.backlundArgZeta
  rw [abs_div, abs_of_pos Real.pi_pos, hhoriz_eq]
  have htri := abs_sub
    (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re)
    (∫ σ in (1 / 2 : ℝ)..2, (deriv h (σ : ℂ) / h (σ : ℂ)).im)
  have hnum : |(∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re) -
      ∫ σ in (1 / 2 : ℝ)..2, (deriv h (σ : ℂ) / h (σ : ℂ)).im| ≤
      2 * Real.pi + (C_J * Real.log (T + 2) + 1) * (2 * Real.pi) := by
    have hmul : ((S_re.card : ℝ) + 1) * (2 * Real.pi) ≤
        (C_J * Real.log (T + 2) + 1) * (2 * Real.pi) := by gcongr
    linarith
  calc |(∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re) -
          ∫ σ in (1 / 2 : ℝ)..2, (deriv h (σ : ℂ) / h (σ : ℂ)).im| / Real.pi
      ≤ (2 * Real.pi + (C_J * Real.log (T + 2) + 1) * (2 * Real.pi)) / Real.pi :=
        div_le_div_of_nonneg_right hnum Real.pi_pos.le
    _ = 4 + 2 * C_J * Real.log (T + 2) := by field_simp [Real.pi_pos.ne']; ring
    _ ≤ C * Real.log (T + 2) := by dsimp only [C]; nlinarith

/-- **UNCONDITIONAL BACKLUND–JENSEN BOUND `|S(T)| ≤ C log T` FOR ALL `T ≥ 2`** (`0` ASSUMPTIONS!). -/
theorem abs_backlundS_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |Stage7VonMangoldtExplicit.backlundS T| ≤ C * Real.log T := by
  obtain ⟨C₀, hC₀, hbd⟩ := abs_backlundS_le_log_add_two
  refine ⟨2 * C₀, by positivity, fun T hT => ?_⟩
  have hlog : Real.log (T + 2) ≤ 2 * Real.log T := by
    have hsq : T + 2 ≤ T ^ 2 := by nlinarith
    calc Real.log (T + 2) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have h1 := hbd T (by linarith)
  nlinarith

/-- Monotonicity of `Stage7VonMangoldtExplicit.xiZeroCount` in `T`. -/
lemma xiZeroCount_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    Stage7VonMangoldtExplicit.xiZeroCount T₁ ≤ Stage7VonMangoldtExplicit.xiZeroCount T₂ := by
  unfold Stage7VonMangoldtExplicit.xiZeroCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
  intro ρ hρ
  simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
  exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.1, hρ.1.2.2.2.trans h⟩, hρ.2.1, hρ.2.2.trans_le h⟩

/-- Existence of a zero-free height `t ∈ (a, b)` for `riemannZeta` on `[0, 1] × {t}`. -/
private lemma exists_zeta_zeroFree_height_in_Ioo {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0 := by
  classical
  have hfin := finite_riemannZeta_zeros_le_height (max b 2)
  set bad : Finset ℝ := hfin.toFinset.image fun ρ => |ρ.im|
  have hne : (Set.Ioo a b \ (bad : Set ℝ)).Nonempty :=
    ((Set.Ioo_infinite hab).sdiff (Finset.finite_toSet bad)).nonempty
  obtain ⟨t, ht_oo, ht_nbad⟩ := hne
  refine ⟨t, ht_oo.1, ht_oo.2, fun σ hσ hz => ?_⟩
  have hσ_pos : 0 < σ := by
    rcases eq_or_lt_of_le hσ.1 with rfl | hpos
    · exfalso
      have hne0 : ((0 : ℝ) : ℂ) + I * (t : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith [ht_oo.1]
      have hne1 : ((0 : ℝ) : ℂ) + I * (t : ℂ) ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this
      have hG : (((0 : ℝ) : ℂ) + I * (t : ℂ)).Gammaℝ ≠ 0 := by
        intro hg
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
        have him := congrArg Complex.im hn; simp at him; linarith [ht_oo.1]
      have hxi0 : xi (((0 : ℝ) : ℂ) + I * (t : ℂ)) = 0 := by
        rw [xi_eq_mul_Gammaℝ_mul_riemannZeta hne0 hne1 hG, hz, mul_zero]
      exact xi_ne_zero_of_re_le_zero (by simp) hxi0
    · exact hpos
  have hσ_lt1 : σ < 1 := by
    rcases eq_or_lt_of_le hσ.2 with rfl | hlt
    · exfalso
      exact riemannZeta_ne_zero_of_one_le_re (s := ((1 : ℝ) : ℂ) + I * (t : ℂ)) (by simp) hz
    · exact hlt
  have hmem : ((σ : ℂ) + I * (t : ℂ)) ∈ hfin.toFinset :=
    hfin.mem_toFinset.mpr ⟨by simpa using hσ_pos, by simpa using hσ_lt1, hz,
      by simp [abs_of_pos (ha.trans ht_oo.1), ht_oo.2.le.trans (le_max_left b 2)]⟩
  exact ht_nbad (Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨_, hmem, by simp [abs_of_pos (ha.trans ht_oo.1)]⟩))

/-- **UNCONDITIONAL FULL RIEMANN–VON MANGOLDT ZERO-COUNT ASYMPTOTIC FOR `riemannZeta` (`0` ASSUMPTIONS!)**:
there exists `C > 0` such that for ALL `T ≥ 2` (with ZERO zero-free-line hypotheses on `T`!):
`|xiZeroCount T - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤ C * Real.log T`. -/
theorem riemann_von_mangoldt_zeta_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(Stage7VonMangoldtExplicit.xiZeroCount T : ℝ) -
          (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log T := by
  obtain ⟨C₁, hC₁_pos, hback⟩ := Stage7VonMangoldtExplicit.backlund_riemann_von_mangoldt_bound.1
  obtain ⟨C_S, hCS_pos, hS⟩ := abs_backlundS_le_log_add_two
  set C : ℝ := 2 * C₁ + 3 * C_S + 4
  refine ⟨C, by positivity, fun T hT => ?_⟩
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT_ge : (1 / 2 : ℝ) ≤ Real.log T := hlog2.trans (Real.log_le_log (by norm_num) hT)
  -- Sandwich `T` between two zero-free heights `T₁ ∈ (T - 1/2, T)` and `T₂ ∈ (T, T + 1/2)`
  obtain ⟨T₁, hT₁_lo, hT₁_hi, hnz₁⟩ :=
    exists_zeta_zeroFree_height_in_Ioo (by linarith : 0 < T - 1 / 2) (by linarith : T - 1 / 2 < T)
  obtain ⟨T₂, hT₂_lo, hT₂_hi, hnz₂⟩ :=
    exists_zeta_zeroFree_height_in_Ioo (by linarith : 0 < T) (by linarith : T < T + 1 / 2)
  have hT₁_ge : 3 / 2 ≤ T₁ := by linarith
  have hT₂_ge : 3 / 2 ≤ T₂ := by linarith
  have hmono1 := xiZeroCount_mono hT₁_hi.le
  have hmono2 := xiZeroCount_mono hT₂_lo.le
  have hlog_cmp : ∀ t : ℝ, 3 / 2 ≤ t → t ≤ T + 1 / 2 → Real.log (t + 2) ≤ 3 * Real.log T := by
    intro t _ ht2
    have hpow : t + 2 ≤ T ^ 3 := by
      have hsq : 4 ≤ T ^ 2 := by nlinarith
      have hcube : T ^ 3 = T * T ^ 2 := by ring
      nlinarith
    calc Real.log (t + 2) ≤ Real.log (T ^ 3) := Real.log_le_log (by linarith) hpow
      _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
  -- Main-term Lipschitz bound on `[T - 1/2, T + 1/2]`
  let M : ℝ → ℝ := fun t => (t / (2 * Real.pi)) * Real.log (t / (2 * Real.pi * Real.exp 1))
  have hM_lip : ∀ t : ℝ, 3 / 2 ≤ t → |t - T| ≤ 1 / 2 → |M t - M T| ≤ 4 * Real.log T := by
    intro t ht1 hdist
    set lo : ℝ := min t T
    set hi : ℝ := max t T
    have hlo1 : 3 / 2 ≤ lo := le_min ht1 (by linarith)
    have hhi_le : hi ≤ T + 1 / 2 := max_le (by linarith [(abs_le.mp hdist).2]) (by linarith)
    have hlohi : lo ≤ hi := min_le_max
    have hhi_sub_lo : hi - lo ≤ 1 / 2 := by
      dsimp only [lo, hi]
      rcases le_total t T with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]; linarith [(abs_le.mp hdist).1]
      · rw [min_eq_right hle, max_eq_left hle]; linarith [(abs_le.mp hdist).2]
    have hderiv : ∀ u ∈ Set.uIcc lo hi,
        HasDerivAt M ((1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))) u := by
      intro u hu
      rw [Set.uIcc_of_le hlohi] at hu
      have hu0 : 0 < u := by linarith [hlo1, hu.1]
      have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) u := by
        simpa using (hasDerivAt_id u).div_const (2 * Real.pi)
      have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi * Real.exp 1))) (u⁻¹) u := by
        have hlin : HasDerivAt (fun x : ℝ => x / (2 * Real.pi * Real.exp 1))
            (1 / (2 * Real.pi * Real.exp 1)) u := by
          simpa using (hasDerivAt_id u).div_const (2 * Real.pi * Real.exp 1)
        refine (hlin.log (by positivity)).congr_deriv ?_
        field_simp [hu0.ne', Real.pi_pos.ne', (Real.exp_pos 1).ne']
      refine (h1.mul h2).congr_deriv ?_
      have hlog : Real.log (u / (2 * Real.pi * Real.exp 1)) =
          Real.log (u / (2 * Real.pi)) - 1 := by
        rw [show u / (2 * Real.pi * Real.exp 1) = (u / (2 * Real.pi)) / Real.exp 1 by ring,
          Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
      rw [hlog]
      field_simp [hu0.ne', Real.pi_pos.ne']; ring
    have hcont : ContinuousOn (fun u : ℝ => (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi)))
        (Set.uIcc lo hi) := by
      rw [Set.uIcc_of_le hlohi]
      refine continuousOn_const.mul (Real.continuousOn_log.comp
        (continuousOn_id.div_const _) fun u hu => ?_)
      have hu0 : 0 < u := by linarith [hlo1, hu.1]
      exact (by positivity : 0 < u / (2 * Real.pi)).ne'
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    have habs_M : |M t - M T| = |M hi - M lo| := by
      dsimp only [lo, hi]
      rcases le_total t T with hle | hle
      · rw [min_eq_left hle, max_eq_right hle, abs_sub_comm]
      · rw [min_eq_right hle, max_eq_left hle]
    rw [habs_M, ← hftc]
    have hpt : ∀ u ∈ Set.Icc lo hi,
        |(1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))| ≤ 8 * Real.log T := by
      intro u hu
      have hu1 : 3 / 2 ≤ u := hlo1.trans hu.1
      have hu_hi : u ≤ T + 1 / 2 := hu.2.trans hhi_le
      have hlog_u_nn : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
      have hlog_2pi_nn : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
      have hlog_2pi_le : Real.log (2 * Real.pi) ≤ 2 := by
        have h1 : 2 * Real.pi ≤ Real.exp 2 := by
          have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hsq : (2.7 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he 2
          rw [← Real.exp_nat_mul] at hsq; norm_num at hsq; linarith [Real.pi_lt_d2]
        exact (Real.log_le_log (by positivity) h1).trans_eq (Real.log_exp 2)
      have hlog_u_le : Real.log u ≤ 3 * Real.log T :=
        (Real.log_le_log (by linarith) (by linarith : u ≤ u + 2)).trans (hlog_cmp u hu1 hu_hi)
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)),
        Real.log_div (by linarith) (by positivity)]
      have habs_diff : |Real.log u - Real.log (2 * Real.pi)| ≤ 3 * Real.log T + 2 := by
        calc |Real.log u - Real.log (2 * Real.pi)|
            ≤ |Real.log u| + |Real.log (2 * Real.pi)| := abs_sub _ _
          _ = Real.log u + Real.log (2 * Real.pi) := by
              rw [abs_of_nonneg hlog_u_nn, abs_of_nonneg hlog_2pi_nn]
          _ ≤ 3 * Real.log T + 2 := add_le_add hlog_u_le hlog_2pi_le
      have hinv : 1 / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
      calc (1 / (2 * Real.pi)) * |Real.log u - Real.log (2 * Real.pi)|
          ≤ 1 * (3 * Real.log T + 2) := mul_le_mul hinv habs_diff (abs_nonneg _) zero_le_one
        _ ≤ 8 * Real.log T := by nlinarith
    calc |∫ u in lo..hi, (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))|
        = ‖∫ u in lo..hi, (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ u in lo..hi, ‖(1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hlohi
      _ ≤ ∫ _u in lo..hi, (8 * Real.log T) :=
          intervalIntegral.integral_mono_on hlohi hcont.intervalIntegrable.norm
            intervalIntegrable_const fun u hu => by rw [Real.norm_eq_abs]; exact hpt u hu
      _ = (hi - lo) * (8 * Real.log T) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (1 / 2) * (8 * Real.log T) := mul_le_mul_of_nonneg_right hhi_sub_lo (by linarith)
      _ = 4 * Real.log T := by ring
  have hb1 : |Stage7VonMangoldtExplicit.xiZeroCount T₁ - M T₁| ≤ (2 * C₁ + 3 * C_S) * Real.log T := by
    have h1 := hback T₁ (by linarith) hnz₁
    have h2 := hS T₁ hT₁_ge
    have h3 := hlog_cmp T₁ hT₁_ge (by linarith)
    nlinarith
  have hb2 : |Stage7VonMangoldtExplicit.xiZeroCount T₂ - M T₂| ≤ (2 * C₁ + 3 * C_S) * Real.log T := by
    have h1 := hback T₂ (by linarith) hnz₂
    have h2 := hS T₂ hT₂_ge
    have h3 := hlog_cmp T₂ hT₂_ge hT₂_hi.le
    nlinarith
  have hlip1 := hM_lip T₁ hT₁_ge (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hlip2 := hM_lip T₂ hT₂_ge (abs_le.mpr ⟨by linarith, by linarith⟩)
  change |Stage7VonMangoldtExplicit.xiZeroCount T - M T| ≤ C * Real.log T
  rw [abs_le]
  have h1_lo := (abs_le.mp hb1).1
  have h2_hi := (abs_le.mp hb2).2
  have hl1_lo := (abs_le.mp hlip1).1
  have hl2_hi := (abs_le.mp hlip2).2
  dsimp only [C]
  constructor <;> linarith

/-! ## Section 2: Uniform `digamma` & `-ζ'/ζ` Bounds, Left-Vertical Line `Re(s) = -1/2`, & Good Horizontal Contours -/

/-- Exact entire-side factorization of `xi(s)` across `s = 0` on the whole half-plane `Re(s) > -2`:
`xi s = 2 * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) * riemannZeta s`
for ALL `s : ℂ` with `-2 < s.re` and `s ≠ 1` (INCLUDING `s = 0` and `Re(s) = -1/2`!). -/
theorem xi_eq_two_mul_sub_one_mul_Gamma_add_one_mul_riemannZeta {s : ℂ}
    (hs : -2 < s.re) (hs1 : s ≠ 1) :
    xi s = 2 * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) *
      Complex.Gamma (s / 2 + 1) * riemannZeta s := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [riemannZeta_zero, Complex.Gamma_one]
    ring
  · have hs2_ne : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
    have hG_rec : Complex.Gamma (s / 2 + 1) = (s / 2) * Complex.Gamma (s / 2) :=
      Complex.Gamma_add_one (s / 2) hs2_ne
    have hG_ne : s.Gammaℝ ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
      cases n with
      | zero => simp at hn; exact hs0 hn
      | succ m =>
        have hre := congrArg Complex.re hn
        simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero] at hre
        have hm1 : (1 : ℝ) ≤ ((m.succ : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
        linarith
    rw [xi_eq_mul_Gammaℝ_mul_riemannZeta hs0 hs1 hG_ne, Complex.Gammaℝ_def, hG_rec]
    ring

/-- Nonvanishing of `riemannZeta` on the left strip `-2 < Re(s) ≤ 0` (no trivial zeros there!). -/
lemma riemannZeta_ne_zero_of_neg_two_lt_re_le_zero {s : ℂ} (hlo : -2 < s.re) (hhi : s.re ≤ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hhi; linarith
  have hxi0 : xi s = 0 := by
    rw [xi_eq_two_mul_sub_one_mul_Gamma_add_one_mul_riemannZeta hlo hs1, hz, mul_zero]
  exact xi_ne_zero_of_re_le_zero hhi hxi0

/-- Exact logarithmic-derivative decomposition on the ENTIRE half-plane `Re(s) > -2`
(free of any `s = 0` singularity!):
`negLogDerivZeta s = -logDeriv xi s + 1 / (s - 1) - (log π / 2) + (1 / 2) * digamma (s / 2 + 1)`
for all `s` with `-2 < s.re`, `s ≠ 1`, and `xi s ≠ 0`. -/
theorem negLogDerivZeta_eq_neg_logDeriv_xi_add {s : ℂ} (hs : -2 < s.re) (hs1 : s ≠ 1)
    (hxi : xi s ≠ 0) :
    Stage3ZeroFreeRegion.negLogDerivZeta s =
      -logDeriv xi s + 1 / (s - 1) - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hs2_re : 0 < (s / 2 + 1).re := by simp; linarith
  have hG_ne : Complex.Gamma (s / 2 + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs2_re
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpiC]; exact Complex.exp_ne_zero _
  have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hZ_ne : riemannZeta s ≠ 0 := fun hz => hxi (by
    rw [xi_eq_two_mul_sub_one_mul_Gamma_add_one_mul_riemannZeta hs hs1, hz, mul_zero])
  have hopen : IsOpen ({w : ℂ | -2 < w.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev : xi =ᶠ[𝓝 s] fun w : ℂ =>
      2 * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1) * riemannZeta w := by
    filter_upwards [hopen.mem_nhds ⟨hs, hs1⟩] with w hw
    exact xi_eq_two_mul_sub_one_mul_Gamma_add_one_mul_riemannZeta hw.1 hw.2
  have hd_pow : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      (-((Real.log Real.pi / 2 : ℝ) : ℂ) * (Real.pi : ℂ) ^ (-s / 2)) s := by
    have hEq : (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) =
        fun w : ℂ => cexp (-((Real.log Real.pi / 2 : ℝ) : ℂ) * w) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero hpiC, ← Complex.ofReal_log Real.pi_pos.le]
      congr 1; push_cast; ring
    rw [hEq]
    have hlin : HasDerivAt (fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) * w)
        (-((Real.log Real.pi / 2 : ℝ) : ℂ)) s := by
      simpa using (hasDerivAt_id s).const_mul (-((Real.log Real.pi / 2 : ℝ) : ℂ))
    exact hlin.cexp.congr_deriv (by rw [congrFun hEq s]; ring)
  have hd_Gam : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2 + 1))
      ((1 / 2 : ℂ) * deriv Complex.Gamma (s / 2 + 1)) s := by
    have hG_diff : DifferentiableAt ℂ Complex.Gamma (s / 2 + 1) :=
      Complex.differentiableAt_Gamma (s / 2 + 1) fun m hEq => by
        have hre := congrArg Complex.re hEq
        simp only [Complex.neg_re, Complex.natCast_re] at hre
        linarith [Nat.cast_nonneg (α := ℝ) m]
    have hlin : HasDerivAt (fun w : ℂ => w / 2 + 1) (1 / 2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).div_const (2 : ℂ)).add_const (1 : ℂ)
    exact (hG_diff.hasDerivAt.comp s hlin).congr_deriv (by ring)
  have hd_poly : HasDerivAt (fun w : ℂ => (2 : ℂ) * (w - 1)) (2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).const_mul (2 : ℂ)
  have hd_Z : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hld_xi : logDeriv xi s =
      1 / (s - 1) - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) + deriv riemannZeta s / riemannZeta s := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have h1_ne : (2 : ℂ) * (s - 1) ≠ 0 := mul_ne_zero h2 hsub_ne
    have h12_ne : (2 : ℂ) * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := mul_ne_zero h1_ne hpow_ne
    have h123_ne : (2 : ℂ) * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 :=
      mul_ne_zero h12_ne hG_ne
    have heq_ld : logDeriv xi s =
        logDeriv (fun w : ℂ => 2 * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1) * riemannZeta w) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
    have hlm1 := logDeriv_mul (f := fun w : ℂ => 2 * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1))
      (g := riemannZeta) s h123_ne hZ_ne ((hd_poly.fun_mul hd_pow).fun_mul hd_Gam).differentiableAt hd_Z.differentiableAt
    have hlm2 := logDeriv_mul (f := fun w : ℂ => 2 * (w - 1) * (Real.pi : ℂ) ^ (-w / 2))
      (g := fun w : ℂ => Complex.Gamma (w / 2 + 1)) s h12_ne hG_ne (hd_poly.fun_mul hd_pow).differentiableAt hd_Gam.differentiableAt
    have hlm3 := logDeriv_mul (f := fun w : ℂ => (2 : ℂ) * (w - 1))
      (g := fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s h1_ne hpow_ne hd_poly.differentiableAt hd_pow.differentiableAt
    rw [heq_ld, hlm1, hlm2, hlm3]
    have ht1 : logDeriv (fun w : ℂ => (2 : ℂ) * (w - 1)) s = 1 / (s - 1) := by
      rw [logDeriv_apply, hd_poly.deriv]; field_simp [h2, hsub_ne]
    have ht2 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s = -((Real.log Real.pi / 2 : ℝ) : ℂ) := by
      rw [logDeriv_apply, hd_pow.deriv]; field_simp [hpow_ne]
    have ht3 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2 + 1)) s = (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
      rw [logDeriv_apply, hd_Gam.deriv, Complex.digamma, logDeriv_apply]; ring
    have ht4 : logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s := logDeriv_apply _ _
    rw [ht1, ht2, ht3, ht4]
    ring
  unfold Stage3ZeroFreeRegion.negLogDerivZeta
  rw [neg_div]
  linear_combination hld_xi

/-- Conjugation symmetry of `Complex.digamma` on `Re(w) > 0`. -/
lemma digamma_conj {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma (starRingEnd ℂ w) = starRingEnd ℂ (Complex.digamma w) := by
  have hwc : 0 < (starRingEnd ℂ w).re := by simpa using hw
  rw [Stage7VonMangoldtExplicit.digamma_eq_neg_eulerMascheroni_add_tsum hwc,
    Stage7VonMangoldtExplicit.digamma_eq_neg_eulerMascheroni_add_tsum hw,
    map_add, map_neg, Complex.conj_ofReal]
  congr 1
  change ∑' n : ℕ, (((n + 1 : ℕ) : ℂ)⁻¹ - (starRingEnd ℂ w + (n : ℂ))⁻¹) =
    Complex.conjCLE (∑' n : ℕ, (((n + 1 : ℕ) : ℂ)⁻¹ - (w + (n : ℂ))⁻¹))
  rw [Complex.conjCLE.map_tsum]
  refine tsum_congr fun n => ?_
  change (((n + 1 : ℕ) : ℂ)⁻¹ - (starRingEnd ℂ w + (n : ℂ))⁻¹) =
    starRingEnd ℂ (((n + 1 : ℕ) : ℂ)⁻¹ - (w + (n : ℂ))⁻¹)
  simp [map_sub, map_inv₀, map_add, map_natCast]

/-- **Uniform Logarithmic Bound on `Complex.digamma` across `1/2 ≤ Re(w) ≤ 2`**:
`∃ C > 0, ∀ w, 1/2 ≤ w.re → w.re ≤ 2 → ‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2)`. -/
theorem norm_digamma_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 2 →
      ‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2) := by
  -- Compact box `[1/2, 2] × [-1, 1]`
  set K : Set ℂ := {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1}
  have hK_comp : IsCompact K := by
    have hEq : K = Complex.equivRealProdCLM.symm '' (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-1 : ℝ) 1) := by
      ext z; simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, Complex.ext (by simp) (by simp)⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩; exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hEq]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hK_sub : K ⊆ {z : ℂ | 0 < z.re} := fun z hz => by change 0 < z.re; linarith [hz.1]
  obtain ⟨M_box, hM_box⟩ := hK_comp.exists_bound_of_continuousOn
    (Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos.mono hK_sub).continuousOn
  set C : ℝ := max (2 * max M_box 1) 12
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun w hlo hhi => ?_⟩
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (|w.im| + 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg w.im]))
  by_cases him : |w.im| ≤ 1
  · have h1 := hM_box w ⟨hlo, hhi, him⟩
    have h2 : M_box ≤ max M_box 1 := le_max_left _ _
    have h3 : 2 * max M_box 1 ≤ C := le_max_left _ _
    have h4 : 0 ≤ max M_box 1 := le_trans zero_le_one (le_max_right _ _)
    nlinarith
  · push Not at him
    -- Auxiliary bound when `w.im > 1`
    have hpos_im : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → 1 < z.im →
        ‖Complex.digamma z‖ ≤ 12 * Real.log (|z.im| + 2) := by
      intro z hz1 hz2 hzim
      have hz_eq : z = (z.re : ℂ) + I * (z.im : ℂ) := Complex.ext (by simp) (by simp)
      have hre := Stage7VonMangoldtExplicit.re_digamma_sub_half_log_le (by linarith : 0 < z.re) (by linarith : 0 < z.im)
      have him_bd := Stage7VonMangoldtExplicit.im_digamma_sub_arctan_bounds (by linarith : 0 < z.re) (by linarith : 0 < z.im)
      rw [← hz_eq] at hre him_bd
      have hden_ge1 : (1 : ℝ) ≤ z.re ^ 2 + z.im ^ 2 := by nlinarith
      have hre_err : (z.re / 2 + 3 / 8) / (z.re ^ 2 + z.im ^ 2) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hsq_le : z.re ^ 2 + z.im ^ 2 ≤ (|z.im| + 2) ^ 2 := by
        rw [abs_of_pos (by linarith : 0 < z.im)]; nlinarith
      have hlog_sq_le : (1 / 2 : ℝ) * Real.log (z.re ^ 2 + z.im ^ 2) ≤ Real.log (|z.im| + 2) := by
        have h1 : Real.log (z.re ^ 2 + z.im ^ 2) ≤ Real.log ((|z.im| + 2) ^ 2) :=
          Real.log_le_log (by linarith) hsq_le
        rw [Real.log_pow] at h1; norm_num at h1; linarith
      have hlog_sq_nn : 0 ≤ (1 / 2 : ℝ) * Real.log (z.re ^ 2 + z.im ^ 2) :=
        mul_nonneg (by norm_num) (Real.log_nonneg hden_ge1)
      have hre_abs : |(Complex.digamma z).re| ≤ Real.log (|z.im| + 2) + 2 := by
        have := abs_le.mp hre
        rw [abs_le]; constructor <;> linarith
      have him_err : z.im / (z.re ^ 2 + z.im ^ 2) ≤ 1 := by
        rw [div_le_one (by linarith)]; nlinarith
      have harc : |Real.arctan (z.im / z.re)| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
      have him_abs : |(Complex.digamma z).im| ≤ 3 := by
        have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
        have := abs_le.mp harc
        rw [abs_le]; constructor <;> linarith [him_bd.1, him_bd.2]
      have hlogz : (1 / 2 : ℝ) ≤ Real.log (|z.im| + 2) :=
        hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im]))
      calc ‖Complex.digamma z‖
          ≤ |(Complex.digamma z).re| + |(Complex.digamma z).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ Real.log (|z.im| + 2) + 5 := by linarith
        _ ≤ 12 * Real.log (|z.im| + 2) := by linarith
    have h12 : 12 ≤ C := le_max_right _ _
    rcases lt_or_gt_of_ne (show w.im ≠ 0 by intro h0; rw [h0, abs_zero] at him; linarith) with hneg | hpos
    · have hgt1 : 1 < (starRingEnd ℂ w).im := by rw [Complex.conj_im]; rw [abs_of_neg hneg] at him; linarith
      have hc := hpos_im (starRingEnd ℂ w) (by simpa using hlo) (by simpa using hhi) hgt1
      rw [digamma_conj (by linarith : 0 < w.re), Complex.norm_conj, Complex.conj_im, abs_neg] at hc
      exact hc.trans (mul_le_mul_of_nonneg_right h12 (by linarith))
    · rw [abs_of_pos hpos] at him
      exact (hpos_im w hlo hhi him).trans (mul_le_mul_of_nonneg_right h12 (by linarith))

/-- Uniform logarithmic bound on `‖logDeriv xi (σ + I * t)‖` for `3 / 2 ≤ σ ≤ 2` and ALL `t : ℝ`. -/
lemma norm_logDeriv_xi_right_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 3 / 2 ≤ σ → σ ≤ 2 → ∀ t : ℝ,
      ‖logDeriv xi ((σ : ℂ) + I * (t : ℂ))‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨Cd, hCd_pos, hdig⟩ := norm_digamma_strip_le
  set C : ℝ := 2 * (6 + Real.log Real.pi / 2) + Cd
  refine ⟨C, by have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi]); positivity,
    fun σ hσ1 hσ2 t => ?_⟩
  set s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs_re; linarith
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by linarith)
  have hdec := negLogDerivZeta_eq_neg_logDeriv_xi_add (by linarith : -2 < s.re) hs1 hxi
  have hld_eq : logDeriv xi s =
      -Stage3ZeroFreeRegion.negLogDerivZeta s + 1 / (s - 1) -
        ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
    linear_combination hdec
  have hZ := Stage5ZetaZeroFree.norm_negLogDerivZeta_of_one_lt_re (σ := σ) (by linarith) t
  have hZ_le : ‖Stage3ZeroFreeRegion.negLogDerivZeta s‖ ≤ 3 := by
    have h1 := hZ.1.trans hZ.2
    have hinv : 1 / (σ - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hsub_le : ‖(1 : ℂ) / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have hre : 1 / 2 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      have hr : (s - 1).re = σ - 1 := by simp [hs_re]
      rw [hr, abs_of_pos (by linarith)] at h; linarith
    rw [div_le_iff₀ (by linarith)]; linarith
  have hdig_le : ‖Complex.digamma (s / 2 + 1)‖ ≤ Cd * Real.log (|t| + 2) := by
    have h1 := hdig (s / 2 + 1) (by simp [hs_re]; linarith) (by simp [hs_re]; linarith)
    have him : |(s / 2 + 1).im| + 2 ≤ |t| + 2 := by
      have h2 : (s / 2 + 1).im = t / 2 := by simp [hs_im]
      rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg t]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
  have hpi_nn : 0 ≤ Real.log Real.pi / 2 := div_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi])) (by norm_num)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  rw [hld_eq]
  have h1 := norm_add_le (-Stage3ZeroFreeRegion.negLogDerivZeta s + 1 / (s - 1) -
      ((Real.log Real.pi / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
  have h2 := norm_sub_le (-Stage3ZeroFreeRegion.negLogDerivZeta s + 1 / (s - 1))
      ((Real.log Real.pi / 2 : ℝ) : ℂ)
  have h3 := norm_add_le (-Stage3ZeroFreeRegion.negLogDerivZeta s) (1 / (s - 1))
  rw [norm_neg] at h3
  rw [Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
  dsimp only [C]
  nlinarith

/-- **Unconditional Left-Vertical Log-Derivative Bound on `Re(s) = -1 / 2`**:
`∃ C > 0, ∀ t : ℝ, ‖-ζ'/ζ(-1/2 + I * t)‖ ≤ C * Real.log (|t| + 2)`. -/
theorem norm_negLogDerivZeta_neg_half_line_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Stage3ZeroFreeRegion.negLogDerivZeta (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
        C * Real.log (|t| + 2) := by
  obtain ⟨Cxi, hCxi_pos, hxi_bd⟩ := norm_logDeriv_xi_right_strip_le
  obtain ⟨Cd, hCd_pos, hdig⟩ := norm_digamma_strip_le
  set C : ℝ := Cxi + Cd + 2 * (2 + Real.log Real.pi / 2)
  refine ⟨C, by have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi]); positivity,
    fun t => ?_⟩
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)
  have hs_re : s.re = -1 / 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs_re; norm_num at hs_re
  have hxi_ne : xi s ≠ 0 := xi_ne_zero_of_re_le_zero (by linarith)
  rw [negLogDerivZeta_eq_neg_logDeriv_xi_add (by linarith : -2 < s.re) hs1 hxi_ne]
  have h1sub_eq : 1 - s = (((3 / 2 : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ)) :=
    Complex.ext (by simp [hs_re]; norm_num) (by simp [hs_im])
  have hld_xi : ‖-logDeriv xi s‖ ≤ Cxi * Real.log (|t| + 2) := by
    rw [norm_neg, ← neg_neg (logDeriv xi s), ← (Stage7VonMangoldtExplicit.logDeriv_xi_symm s).1,
      norm_neg, h1sub_eq]
    simpa [abs_neg] using hxi_bd (3 / 2) le_rfl (by norm_num) (-t)
  have hsub_le : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hre : 3 / 2 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      have hr : (s - 1).re = -3 / 2 := by simp [hs_re]; norm_num
      rw [hr] at h; norm_num at h; exact h
    rw [div_le_one (by linarith)]; linarith
  have hdig_le : ‖Complex.digamma (s / 2 + 1)‖ ≤ Cd * Real.log (|t| + 2) := by
    have h1 := hdig (s / 2 + 1) (by simp [hs_re]; norm_num) (by simp [hs_re]; norm_num)
    have him : |(s / 2 + 1).im| + 2 ≤ |t| + 2 := by
      have h2 : (s / 2 + 1).im = t / 2 := by simp [hs_im]
      rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg t]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
  have hpi_nn : 0 ≤ Real.log Real.pi / 2 := div_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi])) (by norm_num)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  have h1 := norm_add_le (-logDeriv xi s + 1 / (s - 1) - ((Real.log Real.pi / 2 : ℝ) : ℂ))
      ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
  have h2 := norm_sub_le (-logDeriv xi s + 1 / (s - 1)) ((Real.log Real.pi / 2 : ℝ) : ℂ)
  have h3 := norm_add_le (-logDeriv xi s) (1 / (s - 1))
  rw [Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
  dsimp only [C]
  nlinarith

/-- Finiteness of the indices `n : ℕ` where `|(xiZeroSeq n).im| ≤ R`. -/
lemma finite_xiZeroSeq_abs_im_le (R : ℝ) :
    {n : ℕ | |(xiZeroSeq n).im| ≤ R}.Finite := by
  have ht := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq
    xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_gt_atTop (max R 0 + 2)))
  refine (Set.finite_Iio N).subset fun n hn => ?_
  by_contra hge
  have hgt := hN n (not_lt.mp hge)
  have hstrip := xiZeroSeq_strip n
  have htri := Complex.norm_le_abs_re_add_abs_im (xiZeroSeq n)
  rw [abs_of_pos hstrip.1] at htri
  have hR : |(xiZeroSeq n).im| ≤ max R 0 := le_trans hn (le_max_left R 0)
  linarith [hstrip.2]

/-- Exact equality between the cardinality of `{n | a ≤ (xiZeroSeq n).im < b}` (`0 < a ≤ b`)
and `xiZeroCount b - xiZeroCount a`. -/
lemma card_xiZeroSeq_im_Ico_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (F : Finset ℕ)
    (hF : ∀ n : ℕ, n ∈ F ↔ a ≤ (xiZeroSeq n).im ∧ (xiZeroSeq n).im < b) :
    (F.card : ℝ) = Stage7VonMangoldtExplicit.xiZeroCount b - Stage7VonMangoldtExplicit.xiZeroCount a := by
  classical
  have hsub : Stage7VonMangoldtExplicit.xiZeroSetPos a ⊆ Stage7VonMangoldtExplicit.xiZeroSetPos b := by
    intro ρ hρ
    simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.1, hρ.1.2.2.2.trans hab⟩, hρ.2.1, hρ.2.2.trans_le hab⟩
  set D : Finset ℂ := Stage7VonMangoldtExplicit.xiZeroSetPos b \ Stage7VonMangoldtExplicit.xiZeroSetPos a
  have hmaps : ∀ n ∈ F, xiZeroSeq n ∈ D := by
    intro n hn
    obtain ⟨h1, h2⟩ := (hF n).mp hn
    have hst := xiZeroSeq_strip n
    have hz := xiZeroSeq_riemannZeta_zero n
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hst.1, hst.2, hz, by rw [abs_of_pos (ha.trans_le h1)]; exact h2.le⟩, ha.trans_le h1, h2⟩
    · simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
      rintro ⟨_, _, hlt⟩; linarith
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hcard_fib : ∀ ρ ∈ D, (F.filter fun n => xiZeroSeq n = ρ).card = analyticOrderNatAt xi ρ := by
    intro ρ hρ
    rw [Finset.mem_sdiff] at hρ
    have hρb := hρ.1
    simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset] at hρb
    have hρ_ge : a ≤ ρ.im := by
      by_contra hlt
      apply hρ.2
      simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hρb.1.1, hρb.1.2.1, hρb.1.2.2.1, by rw [abs_of_pos hρb.2.1]; exact (not_le.mp hlt).le⟩,
        hρb.2.1, not_le.mp hlt⟩
    exact (isMultiplicityZeroSeq_xi.2 ρ).2 _ fun n => by
      simp only [Finset.mem_filter, hF]
      exact ⟨fun h => h.2, fun h => ⟨⟨h ▸ hρ_ge, h ▸ hρb.2.2⟩, h⟩⟩
  have hnat : F.card = ∑ ρ ∈ D, analyticOrderNatAt xi ρ := by
    rw [hfib]; exact Finset.sum_congr rfl hcard_fib
  have hreal : (F.card : ℝ) = ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) := by
    rw [hnat, Nat.cast_sum]
  rw [hreal]
  unfold Stage7VonMangoldtExplicit.xiZeroCount
  rw [Finset.sum_sdiff_eq_sub hsub]

/-- Exact equality between the cardinality of `{n | a ≤ |(xiZeroSeq n).im| < b}` (`0 < a ≤ b`)
and `2 * (xiZeroCount b - xiZeroCount a)`. -/
lemma card_xiZeroSeq_abs_im_Ico_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (F : Finset ℕ)
    (hF : ∀ n : ℕ, n ∈ F ↔ a ≤ |(xiZeroSeq n).im| ∧ |(xiZeroSeq n).im| < b) :
    (F.card : ℝ) = 2 * (Stage7VonMangoldtExplicit.xiZeroCount b - Stage7VonMangoldtExplicit.xiZeroCount a) := by
  classical
  set Fpos : Finset ℕ := F.filter fun n => 0 < (xiZeroSeq n).im
  set Fneg : Finset ℕ := F.filter fun n => (xiZeroSeq n).im < 0
  have hdisj : Disjoint Fpos Fneg := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
  have hunion : Fpos ∪ Fneg = F := by
    ext n
    simp only [Fpos, Fneg, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hn
      have him_ne : (xiZeroSeq n).im ≠ 0 := fun h0 => by
        have h := ((hF n).mp hn).1; rw [h0, abs_zero] at h; linarith
      rcases lt_or_gt_of_ne him_ne with hneg | hpos
      · exact Or.inr ⟨hn, hneg⟩
      · exact Or.inl ⟨hn, hpos⟩
  have hpos_card : (Fpos.card : ℝ) =
      Stage7VonMangoldtExplicit.xiZeroCount b - Stage7VonMangoldtExplicit.xiZeroCount a := by
    refine card_xiZeroSeq_im_Ico_eq ha hab Fpos fun n => ?_
    simp only [Fpos, Finset.mem_filter, hF]
    constructor
    · rintro ⟨⟨h1, h2⟩, hpos⟩; rw [abs_of_pos hpos] at h1 h2; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hpos : 0 < (xiZeroSeq n).im := ha.trans_le h1
      rw [abs_of_pos hpos]; exact ⟨⟨h1, h2⟩, hpos⟩
  have hneg_card : (Fneg.card : ℝ) =
      Stage7VonMangoldtExplicit.xiZeroCount b - Stage7VonMangoldtExplicit.xiZeroCount a := by
    have hsub : Stage7VonMangoldtExplicit.xiZeroSetPos a ⊆ Stage7VonMangoldtExplicit.xiZeroSetPos b := by
      intro ρ hρ
      simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
      exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.1, hρ.1.2.2.2.trans hab⟩, hρ.2.1, hρ.2.2.trans_le hab⟩
    set D : Finset ℂ := Stage7VonMangoldtExplicit.xiZeroSetPos b \ Stage7VonMangoldtExplicit.xiZeroSetPos a
    have hmaps : ∀ n ∈ Fneg, starRingEnd ℂ (xiZeroSeq n) ∈ D := by
      intro n hn
      obtain ⟨hFn, hneg⟩ := Finset.mem_filter.mp hn
      obtain ⟨h1, h2⟩ := (hF n).mp hFn
      rw [abs_of_neg hneg] at h1 h2
      have hst := xiZeroSeq_strip n
      have hz := (riemannZeta_zero_symm_one_sub hst.1 hst.2 (xiZeroSeq_riemannZeta_zero n)).2.1
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨by simpa using hst.1, by simpa using hst.2, hz, by simpa [abs_of_neg hneg] using h2.le⟩,
          by simp; linarith, by simp; linarith⟩
      · simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
        rintro ⟨_, _, hlt⟩; simp at hlt; linarith
    have hfib := Finset.card_eq_sum_card_fiberwise hmaps
    have hcard_fib : ∀ ρ ∈ D, (Fneg.filter fun n => starRingEnd ℂ (xiZeroSeq n) = ρ).card =
        analyticOrderNatAt xi ρ := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hρb := hρ.1
      simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset] at hρb
      have hρ_ge : a ≤ ρ.im := by
        by_contra hlt
        apply hρ.2
        simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨hρb.1.1, hρb.1.2.1, hρb.1.2.2.1, by rw [abs_of_pos hρb.2.1]; exact (not_le.mp hlt).le⟩,
          hρb.2.1, not_le.mp hlt⟩
      rw [← Stage7VonMangoldtExplicit.analyticOrderNatAt_xi_conj ρ]
      exact (isMultiplicityZeroSeq_xi.2 (starRingEnd ℂ ρ)).2 _ fun n => by
        simp only [Fneg, Finset.mem_filter, hF]
        constructor
        · rintro ⟨_, hEq⟩; rw [← hEq, Complex.conj_conj]
        · intro hEq
          rw [hEq, Complex.conj_conj]
          refine ⟨⟨⟨by simp [abs_of_pos hρb.2.1, hρ_ge], by simp [abs_of_pos hρb.2.1, hρb.2.2]⟩,
            by simp; linarith [hρb.2.1]⟩, rfl⟩
    have hnat : Fneg.card = ∑ ρ ∈ D, analyticOrderNatAt xi ρ := by
      rw [hfib]; exact Finset.sum_congr rfl hcard_fib
    rw [hnat, Nat.cast_sum]
    unfold Stage7VonMangoldtExplicit.xiZeroCount
    rw [Finset.sum_sdiff_eq_sub hsub]
  have htot : F.card = Fpos.card + Fneg.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  rw [htot, Nat.cast_add, hpos_card, hneg_card]; ring

/-- **Multiplicity-Counted Short-Interval Zero-Count Bound**:
`∃ C > 0, ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ a + 6 → xiZeroCount b - xiZeroCount a ≤ C * Real.log b`. -/
lemma xiZeroCount_short_interval_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ a + 6 →
      Stage7VonMangoldtExplicit.xiZeroCount b - Stage7VonMangoldtExplicit.xiZeroCount a ≤
        C * Real.log b := by
  obtain ⟨C₀, hC₀_pos, hasymp⟩ := riemann_von_mangoldt_zeta_asymptotic
  refine ⟨2 * C₀ + 12, by positivity, fun a b ha hab hba => ?_⟩
  let M : ℝ → ℝ := fun t => (t / (2 * Real.pi)) * Real.log (t / (2 * Real.pi * Real.exp 1))
  have ha_bd := abs_le.mp (hasymp a ha)
  have hb_bd := abs_le.mp (hasymp b (ha.trans hab))
  have hlog_ab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hlog_b_ge : (1 / 2 : ℝ) ≤ Real.log b :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (ha.trans hab))
  -- Bound `M b - M a ≤ 12 * Real.log b` via FTC
  have hM_diff : M b - M a ≤ 12 * Real.log b := by
    have hderiv : ∀ u ∈ Set.uIcc a b,
        HasDerivAt M ((1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))) u := by
      intro u hu
      rw [Set.uIcc_of_le hab] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) u := by
        simpa using (hasDerivAt_id u).div_const (2 * Real.pi)
      have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi * Real.exp 1))) (u⁻¹) u := by
        have hlin : HasDerivAt (fun x : ℝ => x / (2 * Real.pi * Real.exp 1))
            (1 / (2 * Real.pi * Real.exp 1)) u := by
          simpa using (hasDerivAt_id u).div_const (2 * Real.pi * Real.exp 1)
        refine (hlin.log (by positivity)).congr_deriv ?_
        field_simp [hu0.ne', Real.pi_pos.ne', (Real.exp_pos 1).ne']
      refine (h1.mul h2).congr_deriv ?_
      have hlog : Real.log (u / (2 * Real.pi * Real.exp 1)) = Real.log (u / (2 * Real.pi)) - 1 := by
        rw [show u / (2 * Real.pi * Real.exp 1) = (u / (2 * Real.pi)) / Real.exp 1 by ring,
          Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
      rw [hlog]; field_simp [hu0.ne', Real.pi_pos.ne']; ring
    have hcont : ContinuousOn (fun u : ℝ => (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi)))
        (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine continuousOn_const.mul (Real.continuousOn_log.comp (continuousOn_id.div_const _) fun u hu => ?_)
      have hu0 : 0 < u := by linarith [hu.1]
      exact (by positivity : 0 < u / (2 * Real.pi)).ne'
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have hpt : ∀ u ∈ Set.Icc a b, (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi)) ≤ 2 * Real.log b := by
      intro u hu
      have hlu : Real.log (u / (2 * Real.pi)) ≤ Real.log b := by
        rw [Real.log_div (by linarith [hu.1]) (by positivity)]
        have h2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
        linarith [Real.log_le_log (by linarith [hu.1]) hu.2]
      have hinv : 1 / (2 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
      rcases le_total 0 (Real.log (u / (2 * Real.pi))) with hnn | hnp
      · calc (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
            ≤ 1 * Real.log b := mul_le_mul hinv hlu hnn zero_le_one
          _ ≤ 2 * Real.log b := by linarith
      · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp).trans (by linarith)
    calc ∫ u in a..b, (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
        ≤ ∫ _u in a..b, (2 * Real.log b) :=
          intervalIntegral.integral_mono_on hab hcont.intervalIntegrable intervalIntegrable_const hpt
      _ = (b - a) * (2 * Real.log b) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 6 * (2 * Real.log b) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = 12 * Real.log b := by ring
  nlinarith

/-- **SHARP ZERO-DENSITY GAP & GOOD HORIZONTAL CONTOUR SELECTION (`exists_good_contour_height`)**:
there exist constants `c > 0` and `C > 0` such that for EVERY `T ≥ 4`, there exists
`T' ∈ [T, T + 1]` at vertical distance `≥ c / Real.log T` from ALL zeros of `riemannZeta`
(both at `+T'` and `-T'`), on which
`‖-ζ'/ζ(σ + I * T')‖ ≤ C * (Real.log T) ^ 2` and `‖-ζ'/ζ(σ - I * T')‖ ≤ C * (Real.log T) ^ 2`
uniformly for ALL `-1 ≤ σ ≤ 2`! -/
theorem exists_good_contour_height :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 4 ≤ T →
        ∃ T' ∈ Set.Icc T (T + 1),
          (∀ ρ : ℂ, riemannZeta ρ = 0 →
            c / Real.log T ≤ |T' - ρ.im| ∧ c / Real.log T ≤ |(-T') - ρ.im|) ∧
          (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
            ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' : ℂ))‖ ≤ C * (Real.log T) ^ 2 ∧
            ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' : ℂ))‖ ≤ C * (Real.log T) ^ 2) := by
  classical
  obtain ⟨C_N, hCN_pos, hshort⟩ := xiZeroCount_short_interval_le
  obtain ⟨Cxi, hCxi_pos, hxi_right⟩ := norm_logDeriv_xi_right_strip_le
  obtain ⟨Cd, hCd_pos, hdig⟩ := norm_digamma_strip_le
  set K_N : ℝ := 8 * C_N + 4
  have hKN_pos : 0 < K_N := by positivity
  set c : ℝ := min (1 / (4 * K_N)) (1 / 2)
  have hc_pos : 0 < c := lt_min (by positivity) (by norm_num)
  set C : ℝ := 32 * Cxi + 4 * K_N / c + 4 * K_N + 2 * Cd + 4 + Real.log Real.pi
  have hC_pos : 0 < C := by
    have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
    positivity
  refine ⟨c, hc_pos, C, hC_pos, fun T hT => ?_⟩
  have hlogT_gt1 : 1 < Real.log T := by
    have h4 : Real.exp 1 < T := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlogT_pos : 0 < Real.log T := zero_lt_one.trans hlogT_gt1
  -- All zeros of `xi` in the band `T - 1 ≤ |ρ.im| ≤ T + 2` (and their multiplicity-counted index set)
  have hfin_band : {n : ℕ | T - 1 ≤ |(xiZeroSeq n).im| ∧ |(xiZeroSeq n).im| < T + 3}.Finite :=
    (finite_xiZeroSeq_abs_im_le (T + 3)).subset fun n hn => hn.2.le
  set F_band : Finset ℕ := hfin_band.toFinset
  have hF_band_card : (F_band.card : ℝ) ≤ K_N * Real.log T := by
    have h1 := card_xiZeroSeq_abs_im_Ico_eq (a := T - 1) (b := T + 3) (by linarith) (by linarith)
      F_band fun n => hfin_band.mem_toFinset
    have h2 := hshort (T - 1) (T + 3) (by linarith) (by linarith) (by linarith)
    have hlog_cmp : Real.log (T + 3) ≤ 2 * Real.log T := by
      have hsq : T + 3 ≤ T ^ 2 := by nlinarith
      calc Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hsq
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    rw [h1]
    dsimp only [K_N]
    nlinarith
  set Z_band : Finset ℂ := F_band.image xiZeroSeq
  have hZ_card : Z_band.card ≤ F_band.card := Finset.card_image_le
  -- Choose `T' ∈ [T, T + 1]` avoiding all `±ρ.im` for `ρ ∈ Z_band`
  obtain ⟨T', hT'_mem, hT'_gap⟩ := Stage5ContourExplicit.exists_good_height_pigeonhole_symm
    (by linarith : 0 ≤ T) Z_band hZ_card
  have hgap_ge : c / Real.log T ≤ 1 / (2 * ((F_band.card : ℝ) + 1)) := by
    have hden_le : 2 * ((F_band.card : ℝ) + 1) ≤ 4 * K_N * Real.log T := by
      have h1 : (1 : ℝ) ≤ K_N * Real.log T := by dsimp only [K_N]; nlinarith
      linarith
    have hc1 : c ≤ 1 / (4 * K_N) := min_le_left _ _
    calc c / Real.log T ≤ (1 / (4 * K_N)) / Real.log T := div_le_div_of_nonneg_right hc1 hlogT_pos.le
      _ = 1 / (4 * K_N * Real.log T) := div_div 1 (4 * K_N) (Real.log T)
      _ ≤ 1 / (2 * ((F_band.card : ℝ) + 1)) := div_le_div_of_nonneg_left zero_le_one (by positivity) hden_le
  have hc_div_le1 : c / Real.log T ≤ 1 := by
    have hc2 : c ≤ 1 / 2 := min_le_right _ _
    rw [div_le_one hlogT_pos]; linarith
  -- Gap holds for ALL zeros of `riemannZeta` (trivial or critical-strip)!
  have hgap_all : ∀ ρ : ℂ, riemannZeta ρ = 0 →
      c / Real.log T ≤ |T' - ρ.im| ∧ c / Real.log T ≤ |(-T') - ρ.im| := by
    intro ρ hρ
    by_cases him0 : ρ.im = 0
    · rw [him0, sub_zero, sub_zero, abs_neg, abs_of_pos (by linarith [hT'_mem.1])]
      exact ⟨hc_div_le1.trans (by linarith [hT'_mem.1]), hc_div_le1.trans (by linarith [hT'_mem.1])⟩
    · -- Non-real zero of `riemannZeta` must be a critical-strip zero of `xi`!
      have hxi0 : xi ρ = 0 := by
        have hlt1 : ρ.re < 1 := by
          by_contra hge; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hρ
        have hgt0 : 0 < ρ.re := by
          by_contra hle
          have h0 : ρ ≠ 0 := fun h => him0 (by rw [h, Complex.zero_im])
          have h1 : ρ ≠ 1 := fun h => him0 (by rw [h, Complex.one_im])
          have hG : ρ.Gammaℝ ≠ 0 := fun hg => by
            obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
            have := congrArg Complex.im hn; simp at this; exact him0 this
          have hx : xi ρ = 0 := by rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 h1 hG, hρ, mul_zero]
          exact xi_ne_zero_of_re_le_zero (not_lt.mp hle) hx
        exact (xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨hgt0, hlt1, hρ⟩
      by_cases hband : T - 1 ≤ |ρ.im| ∧ |ρ.im| < T + 3
      · obtain ⟨n, hn⟩ := isMultiplicityZeroSeq_xi.exists_of_eq_zero differentiable_xi (by simp) hxi0
        have hn_mem : n ∈ F_band := hfin_band.mem_toFinset.mpr
          (by change T - 1 ≤ |(xiZeroSeq n).im| ∧ |(xiZeroSeq n).im| < T + 3; rw [hn]; exact hband)
        have hρ_mem : ρ ∈ Z_band := Finset.mem_image.mpr ⟨n, hn_mem, hn⟩
        have hg := hT'_gap ρ hρ_mem
        exact ⟨hgap_ge.trans hg.1, hgap_ge.trans hg.2⟩
      · -- Outside the band: distance to `±T' ∈ ±[T, T + 1]` is `≥ 1 ≥ c / log T`!
        have hfar : 1 ≤ |T' - (|ρ.im|)| := by
          by_cases h1 : |ρ.im| < T - 1
          · rw [abs_of_pos (by linarith [hT'_mem.1])]; linarith [hT'_mem.1]
          · have h2 : T + 3 ≤ |ρ.im| := by push Not at hband h1; exact hband h1
            rw [abs_of_neg (by linarith [hT'_mem.2])]; linarith [hT'_mem.2]
        have hd1 : 1 ≤ |T' - ρ.im| := hfar.trans (by
          simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T')] using abs_abs_sub_abs_le_abs_sub T' ρ.im)
        have hd2 : 1 ≤ |(-T') - ρ.im| := by
          have hrew : |(-T') - ρ.im| = |T' - (-ρ.im)| := by
            rw [← abs_neg ((-T') - ρ.im)]; congr 1; ring
          rw [hrew]
          exact hfar.trans (by
            simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T'), abs_neg] using
              abs_abs_sub_abs_le_abs_sub T' (-ρ.im))
        exact ⟨hc_div_le1.trans hd1, hc_div_le1.trans hd2⟩
  -- Auxiliary uniform bound on `‖negLogDerivZeta (σ + I * y)‖` for `y = ±T'` and `-1 ≤ σ ≤ 2`!
  have hline_bd : ∀ y : ℝ, (y = T' ∨ y = -T') → ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (y : ℂ))‖ ≤ C * (Real.log T) ^ 2 := by
    intro y hy σ hσ1 hσ2
    have habs_y : |y| = T' := by
      rcases hy with rfl | rfl
      · exact abs_of_pos (by linarith [hT'_mem.1])
      · rw [abs_neg, abs_of_pos (by linarith [hT'_mem.1])]
    have hy_ge4 : 4 ≤ |y| := by rw [habs_y]; linarith [hT'_mem.1]
    have hy_le : |y| + 2 ≤ T ^ 2 := by rw [habs_y]; nlinarith [hT'_mem.2]
    have hlog_y : Real.log (|y| + 2) ≤ 2 * Real.log T := by
      calc Real.log (|y| + 2) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) hy_le
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    set s : ℂ := (σ : ℂ) + I * (y : ℂ)
    set s₀ : ℂ := (2 : ℂ) + I * (y : ℂ)
    have hs_re : s.re = σ := by simp [s]
    have hs_im : s.im = y := by simp [s]
    have hs1 : s ≠ 1 := fun h => by have := congrArg Complex.im h; simp [hs_im] at this; rw [this, abs_zero] at hy_ge4; linarith
    have hgap_y : ∀ n : ℕ, c / Real.log T ≤ |y - (xiZeroSeq n).im| := fun n => by
      have hg := hgap_all (xiZeroSeq n) (xiZeroSeq_riemannZeta_zero n)
      rcases hy with rfl | rfl
      · exact hg.1
      · exact hg.2
    have hxi_s : xi s ≠ 0 := fun h0 => by
      obtain ⟨n, hn⟩ := isMultiplicityZeroSeq_xi.exists_of_eq_zero differentiable_xi (by simp) h0
      have hg := hgap_y n
      rw [hn, hs_im, sub_self, abs_zero] at hg
      have : 0 < c / Real.log T := div_pos hc_pos hlogT_pos
      linarith
    have hxi_s₀ : xi s₀ ≠ 0 := xi_ne_zero_of_one_le_re (by simp [s₀])
    -- Bound `‖logDeriv xi s₀‖ ≤ 2 * Cxi * Real.log T`
    have hld_s₀ : ‖logDeriv xi s₀‖ ≤ 2 * Cxi * Real.log T := by
      have h1 := hxi_right 2 (by norm_num) le_rfl y
      have hs₀_eq : ((2 : ℝ) : ℂ) + I * (y : ℂ) = s₀ := by simp [s₀]
      rw [hs₀_eq] at h1
      exact (h1.trans (mul_le_mul_of_nonneg_left hlog_y hCxi_pos.le)).trans_eq (by ring)
    -- Hadamard difference: `logDeriv xi s - logDeriv xi s₀ = ∑' n, (1/(s - ρ_n) - 1/(s₀ - ρ_n))`
    have hs_ne : ∀ n : ℕ, s ≠ xiZeroSeq n := fun n h => hxi_s (h ▸ xiZeroSeq_zero n)
    have hs₀_ne : ∀ n : ℕ, s₀ ≠ xiZeroSeq n := fun n h => hxi_s₀ (h ▸ xiZeroSeq_zero n)
    have hsumm_s : Summable (fun n : ℕ => 1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n) :=
      Stage5JensenHadamard.summable_hadamard_term xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq hs_ne
    have hsumm_s₀ : Summable (fun n : ℕ => 1 / (s₀ - xiZeroSeq n) + 1 / xiZeroSeq n) :=
      Stage5JensenHadamard.summable_hadamard_term xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq hs₀_ne
    have hdiff_eq : logDeriv xi s - logDeriv xi s₀ =
        ∑' n : ℕ, (1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)) := by
      rw [logDeriv_apply, logDeriv_apply, xi_logDeriv_hadamard s hxi_s, xi_logDeriv_hadamard s₀ hxi_s₀]
      have hsub : (xiHadamardB + ∑' n, (1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n)) -
          (xiHadamardB + ∑' n, (1 / (s₀ - xiZeroSeq n) + 1 / xiZeroSeq n)) =
          (∑' n, (1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n)) -
          (∑' n, (1 / (s₀ - xiZeroSeq n) + 1 / xiZeroSeq n)) := by ring
      rw [hsub, ← hsumm_s.tsum_sub hsumm_s₀]
      refine tsum_congr fun n => by ring
    -- Split `∑' n` at `F_band`: for `n ∉ F_band`, `|y - (xiZeroSeq n).im| ≥ 1`!
    have hre_summ : Summable (fun n : ℕ => (1 / (s₀ - xiZeroSeq n)).re) :=
      Stage5JensenHadamard.summable_re_inv_sub_of_strip xiZeroSeq_strip xiZeroSeq_summable_inv_sq hs₀_ne
    have hre_pos : ∀ n : ℕ, 0 < (1 / (s₀ - xiZeroSeq n)).re := fun n =>
      Stage5JensenHadamard.re_inv_sub_pos_of_strip (xiZeroSeq_strip n).1 (xiZeroSeq_strip n).2 (by simp [s₀])
    have hfar_term : ∀ n : ℕ, n ∉ F_band →
        ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖ ≤ 15 * (1 / (s₀ - xiZeroSeq n)).re := by
      intro n hn
      have hnot_band : ¬ (T - 1 ≤ |(xiZeroSeq n).im| ∧ |(xiZeroSeq n).im| < T + 3) :=
        fun h => hn (hfin_band.mem_toFinset.mpr h)
      have hdist1 : 1 ≤ |y - (xiZeroSeq n).im| := by
        have hfar : 1 ≤ |T' - (|(xiZeroSeq n).im|)| := by
          by_cases h1 : |(xiZeroSeq n).im| < T - 1
          · rw [abs_of_pos (by linarith [hT'_mem.1])]; linarith [hT'_mem.1]
          · have h2 : T + 3 ≤ |(xiZeroSeq n).im| := by push Not at hnot_band h1; exact hnot_band h1
            rw [abs_of_neg (by linarith [hT'_mem.2])]; linarith [hT'_mem.2]
        rcases hy with hy1 | hy2
        · rw [hy1]
          exact hfar.trans (by
            simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T')] using
              abs_abs_sub_abs_le_abs_sub T' (xiZeroSeq n).im)
        · rw [hy2]
          have hrew : |(-T') - (xiZeroSeq n).im| = |T' - (-(xiZeroSeq n).im)| := by
            rw [← abs_neg ((-T') - (xiZeroSeq n).im)]; congr 1; ring
          rw [hrew]
          exact hfar.trans (by
            simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T'), abs_neg] using
              abs_abs_sub_abs_le_abs_sub T' (-(xiZeroSeq n).im))
      have hsub_ne1 : s - xiZeroSeq n ≠ 0 := sub_ne_zero.mpr (hs_ne n)
      have hsub_ne2 : s₀ - xiZeroSeq n ≠ 0 := sub_ne_zero.mpr (hs₀_ne n)
      have hident : 1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n) =
          (s₀ - s) / ((s - xiZeroSeq n) * (s₀ - xiZeroSeq n)) := by
        field_simp [hsub_ne1, hsub_ne2]; ring
      rw [hident, norm_div, norm_mul]
      have hs0s_norm : ‖s₀ - s‖ ≤ 3 := by
        have hdiff : s₀ - s = ((2 - σ : ℝ) : ℂ) := Complex.ext (by simp [s, s₀]) (by simp [s, s₀])
        rw [hdiff, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
      have hd_s : |y - (xiZeroSeq n).im| ≤ ‖s - xiZeroSeq n‖ := by
        simpa [s] using Complex.abs_im_le_norm (s - xiZeroSeq n)
      have hd_s0 : |y - (xiZeroSeq n).im| ≤ ‖s₀ - xiZeroSeq n‖ := by
        simpa [s₀] using Complex.abs_im_le_norm (s₀ - xiZeroSeq n)
      have hsq_pos : 0 < |y - (xiZeroSeq n).im| ^ 2 := by positivity
      have hprod_ge : |y - (xiZeroSeq n).im| ^ 2 ≤ ‖s - xiZeroSeq n‖ * ‖s₀ - xiZeroSeq n‖ := by
        rw [sq]; exact mul_le_mul hd_s hd_s0 (abs_nonneg _) (norm_nonneg _)
      have hst := xiZeroSeq_strip n
      have hre_lb : 1 / (5 * |y - (xiZeroSeq n).im| ^ 2) ≤ (1 / (s₀ - xiZeroSeq n)).re := by
        rw [Stage5JensenHadamard.re_inv_sub_eq]
        have hs₀_re : s₀.re = 2 := by simp [s₀]
        have hs₀_im : s₀.im = y := by simp [s₀]
        rw [hs₀_re, hs₀_im]
        have hnum_ge1 : (1 : ℝ) ≤ 2 - (xiZeroSeq n).re := by linarith [hst.2]
        have hden_le : (2 - (xiZeroSeq n).re) ^ 2 + (y - (xiZeroSeq n).im) ^ 2 ≤
            5 * |y - (xiZeroSeq n).im| ^ 2 := by
          rw [sq_abs]
          have h1 : (2 - (xiZeroSeq n).re) ^ 2 ≤ 4 := by nlinarith [hst.1, hst.2]
          have h2 : (1 : ℝ) ≤ (y - (xiZeroSeq n).im) ^ 2 := by rw [← sq_abs]; nlinarith
          linarith
        exact div_le_div₀ (by positivity) hnum_ge1 (by positivity) hden_le
      calc ‖s₀ - s‖ / (‖s - xiZeroSeq n‖ * ‖s₀ - xiZeroSeq n‖)
          ≤ 3 / |y - (xiZeroSeq n).im| ^ 2 := div_le_div₀ (by norm_num) hs0s_norm hsq_pos hprod_ge
        _ = 15 * (1 / (5 * |y - (xiZeroSeq n).im| ^ 2)) := by ring
        _ ≤ 15 * (1 / (s₀ - xiZeroSeq n)).re := mul_le_mul_of_nonneg_left hre_lb (by norm_num)
    have hnear_term : ∀ n ∈ F_band,
        ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖ ≤ Real.log T / c + 1 := by
      intro n _
      have h1 : ‖(1 : ℂ) / (s - xiZeroSeq n)‖ ≤ Real.log T / c := by
        rw [norm_div, norm_one]
        have hd : c / Real.log T ≤ ‖s - xiZeroSeq n‖ :=
          (hgap_y n).trans (by simpa [s] using Complex.abs_im_le_norm (s - xiZeroSeq n))
        calc 1 / ‖s - xiZeroSeq n‖ ≤ 1 / (c / Real.log T) :=
              div_le_div_of_nonneg_left zero_le_one (div_pos hc_pos hlogT_pos) hd
          _ = Real.log T / c := one_div_div c (Real.log T)
      have h2 : ‖(1 : ℂ) / (s₀ - xiZeroSeq n)‖ ≤ 1 := by
        rw [norm_div, norm_one]
        have hd : 1 ≤ ‖s₀ - xiZeroSeq n‖ := by
          have h := Complex.abs_re_le_norm (s₀ - xiZeroSeq n)
          have hr : (s₀ - xiZeroSeq n).re = 2 - (xiZeroSeq n).re := by simp [s₀]
          rw [hr, abs_of_pos (by linarith [(xiZeroSeq_strip n).2])] at h
          linarith [(xiZeroSeq_strip n).2]
        exact div_le_one_of_le₀ hd (norm_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    -- Combine near + far via `Summable.sum_add_tsum_compl`!
    have hsumm_norm : Summable (fun n : ℕ => ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        ((hre_summ.mul_left 15).add (summable_of_ne_finset_zero (s := F_band)
          (f := fun n => if n ∈ F_band then Real.log T / c + 1 else 0) (fun n hn => by simp [hn])))
      by_cases hn : n ∈ F_band
      · simp only [hn, ↓reduceIte]
        linarith [hnear_term n hn, hre_pos n]
      · simp only [hn, ↓reduceIte, add_zero]
        exact hfar_term n hn
    have htsum_bd : ‖∑' n : ℕ, (1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n))‖ ≤
        (F_band.card : ℝ) * (Real.log T / c + 1) + 15 * (deriv xi s₀ / xi s₀).re := by
      have hsplit := hsumm_norm.sum_add_tsum_compl (s := F_band)
      have hnear_sum : ∑ n ∈ F_band, ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖ ≤
          (F_band.card : ℝ) * (Real.log T / c + 1) := by
        calc ∑ n ∈ F_band, ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖
            ≤ ∑ _n ∈ F_band, (Real.log T / c + 1) := Finset.sum_le_sum hnear_term
          _ = (F_band.card : ℝ) * (Real.log T / c + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      have hfar_sum : ∑' x : {n // n ∉ F_band}, ‖1 / (s - xiZeroSeq x.1) - 1 / (s₀ - xiZeroSeq x.1)‖ ≤
          15 * (deriv xi s₀ / xi s₀).re := by
        have hre_sub : Summable (fun x : {n // n ∉ F_band} => 15 * (1 / (s₀ - xiZeroSeq x.1)).re) :=
          (hre_summ.mul_left 15).subtype _
        have h1 : ∑' x : {n // n ∉ F_band}, ‖1 / (s - xiZeroSeq x.1) - 1 / (s₀ - xiZeroSeq x.1)‖ ≤
            ∑' x : {n // n ∉ F_band}, 15 * (1 / (s₀ - xiZeroSeq x.1)).re :=
          (hsumm_norm.subtype _).tsum_le_tsum (fun x => hfar_term x.1 x.2) hre_sub
        have h2 : ∑' x : {n // n ∉ F_band}, (1 / (s₀ - xiZeroSeq x.1)).re ≤
            ∑' n : ℕ, (1 / (s₀ - xiZeroSeq n)).re := by
          have hsp : (∑ n ∈ F_band, (1 / (s₀ - xiZeroSeq n)).re) +
              ∑' x : {n // n ∉ F_band}, (1 / (s₀ - xiZeroSeq x.1)).re =
              ∑' n : ℕ, (1 / (s₀ - xiZeroSeq n)).re := hre_summ.sum_add_tsum_compl (s := F_band)
          have hnn : 0 ≤ ∑ n ∈ F_band, (1 / (s₀ - xiZeroSeq n)).re :=
            Finset.sum_nonneg fun n _ => (hre_pos n).le
          linarith
        rw [tsum_mul_left] at h1
        rw [Stage7HadamardXiProduct.xi_re_logDeriv_eq_tsum (by simp [s₀])]
        linarith
      calc ‖∑' n : ℕ, (1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n))‖
          ≤ ∑' n : ℕ, ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖ := norm_tsum_le_tsum_norm hsumm_norm
        _ = (∑ n ∈ F_band, ‖1 / (s - xiZeroSeq n) - 1 / (s₀ - xiZeroSeq n)‖) +
            ∑' x : {n // n ∉ F_band}, ‖1 / (s - xiZeroSeq x.1) - 1 / (s₀ - xiZeroSeq x.1)‖ := hsplit.symm
        _ ≤ (F_band.card : ℝ) * (Real.log T / c + 1) + 15 * (deriv xi s₀ / xi s₀).re :=
            add_le_add hnear_sum hfar_sum
    have hre_s₀_le : (deriv xi s₀ / xi s₀).re ≤ 2 * Cxi * Real.log T := by
      have h1 : (deriv xi s₀ / xi s₀).re ≤ ‖logDeriv xi s₀‖ := by
        rw [logDeriv_apply]; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      exact h1.trans hld_s₀
    have hld_xi_s : ‖logDeriv xi s‖ ≤
        (32 * Cxi + K_N / c + K_N) * (Real.log T) ^ 2 := by
      have htri : ‖logDeriv xi s‖ ≤ ‖logDeriv xi s - logDeriv xi s₀‖ + ‖logDeriv xi s₀‖ := by
        simpa [sub_add_cancel] using norm_add_le (logDeriv xi s - logDeriv xi s₀) (logDeriv xi s₀)
      rw [hdiff_eq] at htri
      have hF_mul : (F_band.card : ℝ) * (Real.log T / c + 1) ≤
          (K_N / c + K_N) * (Real.log T) ^ 2 := by
        have h1 : (F_band.card : ℝ) * (Real.log T / c + 1) ≤
            (K_N * Real.log T) * (Real.log T / c + Real.log T) :=
          mul_le_mul hF_band_card (by linarith) (by positivity) (by positivity)
        linarith [show (K_N * Real.log T) * (Real.log T / c + Real.log T) =
          (K_N / c + K_N) * (Real.log T) ^ 2 by ring]
      have hlog_sq : Real.log T ≤ (Real.log T) ^ 2 := by nlinarith
      nlinarith
    -- Pass from `logDeriv xi s` to `negLogDerivZeta s`!
    rw [negLogDerivZeta_eq_neg_logDeriv_xi_add (by linarith : -2 < s.re) hs1 hxi_s]
    have hsub_le : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have h1 : 4 ≤ ‖s - 1‖ := hy_ge4.trans (by simpa [hs_im] using Complex.abs_im_le_norm (s - 1))
      rw [div_le_one (by linarith)]; linarith
    have hdig_le : ‖Complex.digamma (s / 2 + 1)‖ ≤ 2 * Cd * Real.log T := by
      have h1 := hdig (s / 2 + 1) (by simp [hs_re]; linarith) (by simp [hs_re]; linarith)
      have him : |(s / 2 + 1).im| + 2 ≤ |y| + 2 := by
        have h2 : (s / 2 + 1).im = y / 2 := by simp [hs_im]
        rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [abs_nonneg y]
      have h2 := h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
      exact h2.trans (by nlinarith)
    have hpi_nn : 0 ≤ Real.log Real.pi / 2 := div_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi])) (by norm_num)
    have h1 := norm_add_le (-logDeriv xi s + 1 / (s - 1) - ((Real.log Real.pi / 2 : ℝ) : ℂ))
        ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
    have h2 := norm_sub_le (-logDeriv xi s + 1 / (s - 1)) ((Real.log Real.pi / 2 : ℝ) : ℂ)
    have h3 := norm_add_le (-logDeriv xi s) (1 / (s - 1))
    rw [norm_neg] at h3
    rw [Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
    have hlog_sq1 : (1 : ℝ) ≤ (Real.log T) ^ 2 := by nlinarith
    have hlog_sq : Real.log T ≤ (Real.log T) ^ 2 := by nlinarith
    have hK_div : 0 ≤ K_N / c := div_nonneg hKN_pos.le hc_pos.le
    have hA : (32 * Cxi + K_N / c + K_N) * (Real.log T) ^ 2 ≤
        (32 * Cxi + 4 * K_N / c + 4 * K_N) * (Real.log T) ^ 2 := by
      have hcoef : 32 * Cxi + K_N / c + K_N ≤ 32 * Cxi + 4 * K_N / c + 4 * K_N := by
        have h4 : 4 * K_N / c = 4 * (K_N / c) := by ring
        linarith
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    have hB : 1 + Real.log Real.pi / 2 + (1 / 2) * (2 * Cd * Real.log T) ≤
        (2 * Cd + 4 + Real.log Real.pi) * (Real.log T) ^ 2 := by
      nlinarith [hCd_pos, hpi_nn, hlog_sq1, hlog_sq]
    dsimp only [C]
    linarith
  refine ⟨T', hT'_mem, hgap_all, fun σ hσ1 hσ2 => ?_⟩
  refine ⟨hline_bd T' (Or.inl rfl) σ hσ1 hσ2, ?_⟩
  have hneg : (σ : ℂ) - I * (T' : ℂ) = (σ : ℂ) + I * ((-T' : ℝ) : ℂ) := by push_cast; ring
  rw [hneg]
  exact hline_bd (-T') (Or.inr rfl) σ hσ1 hσ2

/-! ## Section 3: Unconditional Von Mangoldt Explicit Formula for `Chebyshev.psi` -/

/-- Finite set of all critical-strip zeros of `riemannZeta` (equivalently `xi`) with `|ρ.im| ≤ T`. -/
def zetaZerosInBox (T : ℝ) : Finset ℂ :=
  (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).toFinset

/-- Multiplicity-weighted finite zero sum `∑_{ρ ∈ zetaZerosInBox T} m_ρ * x^ρ / ρ`. -/
def psiZeroSum (x T : ℝ) : ℂ :=
  ∑ ρ ∈ zetaZerosInBox T, (analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)

/-- Exact meromorphic regularization of `-ζ'/ζ` on `closedRect (-1/2) c (-T') T'` when `1 < c`,
`0 < T'`, and no zero of `riemannZeta` lies on `Im(s) = ±T'`: there exists `L : ℂ → ℂ` agreeing
with `negLogDerivZeta` away from `{1} ∪ zetaZerosInBox T'` such that
`L s - (1 / (s - 1) - ∑_{ρ ∈ zetaZerosInBox T'} m_ρ / (s - ρ))` is holomorphic on the closed
rectangle `closedRect (-1/2) c (-T') T'`. -/
private lemma exists_meromorphic_negLogDerivZeta_rect {c T' : ℝ} (hc : 1 < c) (hT' : 0 < T')
    (havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → T' ≠ ρ.im ∧ -T' ≠ ρ.im) :
    let J : Finset ℂ := insert (1 : ℂ) (zetaZerosInBox T')
    let a : ℂ → ℂ := fun p => if p = 1 then (1 : ℂ) else -(analyticOrderNatAt xi p : ℂ)
    ∃ L : ℂ → ℂ,
      (∀ p ∈ J, p ∈ Stage5ContourExplicit.openRect (-1 / 2) c (-T') T' ∧ p ≠ 0) ∧
      DifferentiableOn ℂ (fun s => L s - ∑ p ∈ J, a p / (s - p))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') ∧
      (∀ s ∈ Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T', s ∉ J →
        L s = Stage3ZeroFreeRegion.negLogDerivZeta s) := by
  classical
  intro J a
  set Z : Finset ℂ := zetaZerosInBox T'
  have h1_not_Z : (1 : ℂ) ∉ Z := fun h => by
    have hm := (finite_riemannZeta_zeros_le_height T').mem_toFinset.mp h
    simp at hm
  -- Every `ρ ∈ Z` lies strictly inside `openRect (-1/2) c (-T') T'` and `ρ ≠ 0, 1`
  have hZ_open : ∀ ρ ∈ Z, ρ ∈ Stage5ContourExplicit.openRect (-1 / 2) c (-T') T' ∧ ρ ≠ 0 ∧ ρ ≠ 1 := by
    intro ρ hρ
    have hm := (finite_riemannZeta_zeros_le_height T').mem_toFinset.mp hρ
    have hne := havoid ρ hm.2.2.1
    have him_lt : |ρ.im| < T' := lt_of_le_of_ne hm.2.2.2 fun hEq => by
      rcases abs_eq hT'.le |>.mp hEq with hp | hn
      · exact hne.1 hp.symm
      · exact hne.2 (by linarith)
    refine ⟨⟨⟨by linarith [hm.1], by linarith [hm.2.1]⟩, abs_lt.mp him_lt⟩, ?_, ?_⟩
    · intro h0; have h0re := hm.1; rw [h0, Complex.zero_re] at h0re; exact lt_irrefl 0 h0re
    · intro h1; have h1re := hm.2.1; rw [h1, Complex.one_re] at h1re; exact lt_irrefl 1 h1re
  -- Pick `δ ∈ (0, 1/2)` so no zero of `xi` outside `Z` lies in `|Im(z)| < T' + δ`
  set Z_big : Finset ℂ := zetaZerosInBox (T' + 1)
  set Z_out : Finset ℂ := Z_big.filter fun ρ => T' < |ρ.im|
  obtain ⟨δ, hδ_pos, hδ_lt_half, hδ_avoid⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ ρ ∈ Z_out, T' + δ < |ρ.im| := by
    by_cases hemp : Z_out = ∅
    · exact ⟨1 / 4, by norm_num, by norm_num, fun ρ hρ => by rw [hemp] at hρ; exact absurd hρ (Finset.notMem_empty _)⟩
    · have hne : Z_out.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      set m := Z_out.inf' hne fun ρ => |ρ.im| - T'
      have hm_pos : 0 < m := by
        rw [Finset.lt_inf'_iff]
        intro ρ hρ; exact sub_pos.mpr (Finset.mem_filter.mp hρ).2
      refine ⟨min (1 / 4) (m / 2), lt_min (by norm_num) (by linarith),
        (min_le_left _ _).trans_lt (by norm_num), fun ρ hρ => ?_⟩
      have h1 : m ≤ |ρ.im| - T' := Finset.inf'_le (fun w => |w.im| - T') hρ
      have h2 : min (1 / 4) (m / 2) ≤ m / 2 := min_le_right _ _
      linarith
  set U : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < c + 1 ∧ |z.im| < T' + δ}
  have hU_open : IsOpen U := by
    have h1 : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z.re < c + 1} := isOpen_lt Complex.continuous_re continuous_const
    have h3 : IsOpen {z : ℂ | |z.im| < T' + δ} := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    have hEq : U = {z : ℂ | -1 < z.re} ∩ ({z : ℂ | z.re < c + 1} ∩ {z : ℂ | |z.im| < T' + δ}) := rfl
    rw [hEq]; exact h1.inter (h2.inter h3)
  have hrect_sub_U : Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' ⊆ U := fun z hz =>
    ⟨by linarith [hz.1.1], by linarith [hz.1.2], by have := abs_le.mpr hz.2; linarith⟩
  have hxi_an : AnalyticOnNhd ℂ xi U :=
    (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ U)
  have hxi_ntop : ∀ z ∈ U, analyticOrderAt xi z ≠ ⊤ := fun z _ htop => by
    have h0 := (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ 0)
    simp at h0
  have hZ_all : ∀ z ∈ U, xi z = 0 → z ∈ Z := by
    intro z hz h0
    obtain ⟨h0re, h1re, hζ⟩ := (xi_eq_zero_iff_critical_strip_zeta_zero z).mp h0
    have hle_big : |z.im| ≤ T' + 1 := by linarith [hz.2.2, hδ_lt_half]
    have hmem_big : z ∈ Z_big := (finite_riemannZeta_zeros_le_height (T' + 1)).mem_toFinset.mpr ⟨h0re, h1re, hζ, hle_big⟩
    have hle_T' : |z.im| ≤ T' := by
      by_contra hgt
      push Not at hgt
      have hmem_out : z ∈ Z_out := Finset.mem_filter.mpr ⟨hmem_big, hgt⟩
      linarith [hδ_avoid z hmem_out, hz.2.2]
    exact (finite_riemannZeta_zeros_le_height T').mem_toFinset.mpr ⟨h0re, h1re, hζ, hle_T'⟩
  obtain ⟨g, hg_diff, hg_nz, hxi_fac⟩ := exists_holomorphic_quotient_by_zeros hxi_an hxi_ntop Z hZ_all
  let H : ℂ → ℂ := fun s =>
    -logDeriv g s - ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)
  have hH_diff : DifferentiableOn ℂ H (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') := by
    have hg_d' : DifferentiableOn ℂ (logDeriv g) U := by
      have hgd : DifferentiableOn ℂ (deriv g) U := hg_diff.deriv hU_open
      have hld_eq : logDeriv g = fun s => deriv g s / g s := funext fun s => logDeriv_apply g s
      rw [hld_eq]
      exact hgd.div hg_diff hg_nz
    have hdig_d : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma (s / 2 + 1))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') := by
      intro s hs
      have hre : 0 < (s / 2 + 1).re := by simp; linarith [hs.1.1]
      have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
      have hd1 : DifferentiableAt ℂ Complex.digamma (s / 2 + 1) :=
        (Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos (s / 2 + 1) hre).differentiableAt
          (hopen.mem_nhds hre)
      exact (hd1.comp s ((differentiableAt_id.div_const (2 : ℂ)).add (differentiableAt_const 1))).differentiableWithinAt
    exact (((hg_d'.mono hrect_sub_U).neg).sub (differentiableOn_const _)).add
      ((differentiableOn_const _).mul hdig_d)
  let L : ℂ → ℂ := fun s => H s + ∑ p ∈ J, a p / (s - p)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpZ
    · exact ⟨⟨⟨by simp; norm_num, by simp [hc]⟩, by simp [hT']⟩, one_ne_zero⟩
    · exact ⟨(hZ_open p hpZ).1, (hZ_open p hpZ).2.1⟩
  · have hEq : (fun s => L s - ∑ p ∈ J, a p / (s - p)) = H := funext fun s => by dsimp only [L]; ring
    rw [hEq]; exact hH_diff
  · intro s hs hsJ
    have hsU : s ∈ U := hrect_sub_U hs
    have hs1 : s ≠ 1 := fun h => hsJ (h ▸ Finset.mem_insert_self (1 : ℂ) Z)
    have hsZ : s ∉ Z := fun h => hsJ (Finset.mem_insert_of_mem h)
    have hxi_ne : xi s ≠ 0 := fun h0 => hsZ (hZ_all s hsU h0)
    -- Compute `logDeriv xi s = logDeriv g s + ∑ ρ ∈ Z, m_ρ / (s - ρ)`
    let Q : ℂ → ℂ := fun z => ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt xi ρ
    have hQ_ne : Q s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun hEq => hsZ (hEq ▸ hρ))
    have hQ_diff : DifferentiableAt ℂ Q s :=
      DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub (differentiableAt_const ρ)).pow _
    have hg_d : DifferentiableAt ℂ g s := (hg_diff s hsU).differentiableAt (hU_open.mem_nhds hsU)
    have hxi_ev : xi =ᶠ[𝓝 s] fun z => g z * Q z :=
      Filter.eventually_of_mem (hU_open.mem_nhds hsU) hxi_fac
    have hld_Q : logDeriv Q s = ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ) / (s - ρ) := by
      have h1 := logDeriv_prod (s := Z) (f := fun ρ (z : ℂ) => (z - ρ) ^ analyticOrderNatAt xi ρ) (x := s)
        (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun hEq => hsZ (hEq ▸ hρ)))
        (fun ρ _ => (differentiableAt_id.sub (differentiableAt_const ρ)).pow _)
      change logDeriv Q s = _
      dsimp only [Q]; rw [h1]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hsub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr fun hEq => hsZ (hEq ▸ hρ)
      rw [logDeriv_apply]
      have hd : HasDerivAt (fun z : ℂ => (z - ρ) ^ analyticOrderNatAt xi ρ)
          ((analyticOrderNatAt xi ρ : ℂ) * (s - ρ) ^ (analyticOrderNatAt xi ρ - 1)) s := by
        simpa using ((hasDerivAt_id s).sub_const ρ).fun_pow (analyticOrderNatAt xi ρ)
      rw [hd.deriv]
      cases hm : analyticOrderNatAt xi ρ with
      | zero => simp
      | succ k =>
        rw [Nat.succ_sub_one, pow_succ]
        field_simp [hsub_ne]
    have hld_xi : logDeriv xi s = logDeriv g s + ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ) / (s - ρ) := by
      rw [← hld_Q, logDeriv_apply, logDeriv_apply, logDeriv_apply, hxi_ev.deriv_eq,
        (hg_d.hasDerivAt.fun_mul hQ_diff.hasDerivAt).deriv, hxi_ev.self_of_nhds]
      have hgne := hg_nz s hsU
      field_simp [hgne, hQ_ne]
    have hsum_J : ∑ p ∈ J, a p / (s - p) =
        1 / (s - 1) - ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ) / (s - ρ) := by
      dsimp only [J, a]
      rw [Finset.sum_insert h1_not_Z, if_pos rfl]
      have hZ_terms : ∑ ρ ∈ Z, (if ρ = 1 then (1 : ℂ) else -(analyticOrderNatAt xi ρ : ℂ)) / (s - ρ) =
          -(∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ) / (s - ρ)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [if_neg (hZ_open ρ hρ).2.2, neg_div]
      rw [hZ_terms, ← sub_eq_add_neg]
    rw [negLogDerivZeta_eq_neg_logDeriv_xi_add (by linarith [hs.1.1] : -2 < s.re) hs1 hxi_ne, hld_xi]
    dsimp only [L, H]
    rw [hsum_J]
    ring

/-- **UNCONDITIONAL VON MANGOLDT EXPLICIT FORMULA FOR `Chebyshev.psi` (`0` ASSUMPTIONS!)**:
there exists a universal constant `C > 0` such that for ALL `x ≥ 4` and ALL `4 ≤ T ≤ x`:
`|Chebyshev.psi x - (x - (psiZeroSum x T).re)| ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x)`. -/
theorem von_mangoldt_explicit_formula_psi :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 4 ≤ x → ∀ T : ℝ, 4 ≤ T → T ≤ x →
      |Chebyshev.psi x - (x - (psiZeroSum x T).re)| ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  classical
  obtain ⟨c_gap, hc_gap, C_h, hCh_pos, hgood⟩ := exists_good_contour_height
  obtain ⟨C_L, hCL_pos, hleft_bd⟩ := norm_negLogDerivZeta_neg_half_line_le
  obtain ⟨C_N, hCN_pos, hshort⟩ := xiZeroCount_short_interval_le
  set K₀ : ℝ := ‖Stage3ZeroFreeRegion.negLogDerivZeta 0‖
  set C : ℝ := 3000 + 20 * C_h + 48 * C_L + K₀ + 4 * C_N
  refine ⟨C, by positivity, fun x hx4 T hT4 hTx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hlogx_gt1 : 1 < Real.log x := by
    have h4 : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlogx_pos : 0 < Real.log x := zero_lt_one.trans hlogx_gt1
  have hlogT_le_logx : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
  have hlogT_gt1 : 1 < Real.log T := by
    have h4 : Real.exp 1 < T := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  set c : ℝ := 1 + 1 / Real.log x with hc_def
  have hc1 : 1 < c := by rw [hc_def]; linarith [div_pos one_pos hlogx_pos]
  have hc2 : c ≤ 2 := by
    rw [hc_def]; have : 1 / Real.log x ≤ 1 := (div_le_one hlogx_pos).mpr hlogx_gt1.le; linarith
  have hxc_le : x ^ c ≤ 3 * x := by
    have h1 : x ^ c = x * x ^ (1 / Real.log x) := by rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
    have h2 : x ^ (1 / Real.log x) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hlogx_pos.ne']
    rw [h1, h2]
    have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith
  -- Choose good horizontal height `T' ∈ [T, T + 1]`
  obtain ⟨T', hT'_mem, hT'_gap, hT'_bd⟩ := hgood T hT4
  have hT'_geT : T ≤ T' := hT'_mem.1
  have hT'_le : T' ≤ T + 1 := hT'_mem.2
  have hT'_pos : 0 < T' := by linarith
  have havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → T' ≠ ρ.im ∧ -T' ≠ ρ.im := fun ρ hρ => by
    have hg := hT'_gap ρ hρ
    have hpos : 0 < c_gap / Real.log T := div_pos hc_gap (zero_lt_one.trans hlogT_gt1)
    exact ⟨fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.1],
           fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.2]⟩
  -- Step 1: Sharp truncated Perron at height `T'`
  have hPerron_raw := Stage5ContourExplicit.norm_chebyshevPsiChar_sub_truncatedPerron_le
    (1 : DirichletCharacter ℂ 1) hx2 (by linarith : 1 ≤ T')
  have hpsi_eq : Stage2DirichletAP.chebyshevPsiChar (1 : DirichletCharacter ℂ 1) x =
      (Chebyshev.psi x : ℂ) := by
    rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
    unfold Stage2DirichletAP.chebyshevPsiChar RHDirect.chebyshevPsi
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Stage2DirichletAP.principal_char_apply_nat, if_pos (Nat.coprime_one_right n), one_mul]
  rw [hpsi_eq] at hPerron_raw
  have hPerron : ‖(Chebyshev.psi x : ℂ) -
      Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c T'‖ ≤
      2400 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
    have h1 : x / T' ≤ x / T := div_le_div_of_nonneg_left hx0.le hT0 hT'_geT
    have h2 : (Real.log x + 1) ^ 2 ≤ 4 * (Real.log x) ^ 2 := by nlinarith
    have h3 : Real.log x + 1 ≤ 2 * Real.log x := by linarith
    have h4 : x / T' * (Real.log x + 1) ^ 2 ≤ 4 * (x * (Real.log x) ^ 2 / T) := by
      calc x / T' * (Real.log x + 1) ^ 2 ≤ (x / T) * (4 * (Real.log x) ^ 2) :=
            mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
        _ = 4 * (x * (Real.log x) ^ 2 / T) := by ring
    linarith
  -- Step 2: Exact vertical contour shift on `[-1/2, c] × [-T', T']`
  obtain ⟨L, hJ_open, hL_diff, hL_eq⟩ := exists_meromorphic_negLogDerivZeta_rect hc1 hT'_pos havoid
  set J : Finset ℂ := insert (1 : ℂ) (zetaZerosInBox T')
  set a : ℂ → ℂ := fun p => if p = 1 then (1 : ℂ) else -(analyticOrderNatAt xi p : ℂ)
  have hshift := Stage5ContourExplicit.vertical_contour_shift_div_id_eq_sum_residues
    L hx0 (by norm_num : (-1 / 2 : ℝ) < 0) (by linarith : 0 < c) hT'_pos J id a
    (fun p hp => (hJ_open p hp).1) (fun p hp => (hJ_open p hp).2) hL_diff
  -- Identify `L` with `negLogDerivZeta` on all four edges and at `0`!
  have hL0 : L 0 = Stage3ZeroFreeRegion.negLogDerivZeta 0 :=
    hL_eq 0 ⟨⟨by simp; norm_num, by simp; linarith⟩, by simp [hT'_pos.le]⟩ fun h0J => (hJ_open 0 h0J).2 rfl
  have hL_right : ∀ t ∈ Set.uIcc (-T') T',
      L ((c : ℂ) + I * (t : ℂ)) = Stage3ZeroFreeRegion.negLogDerivZeta ((c : ℂ) + I * (t : ℂ)) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    refine hL_eq _ ⟨⟨by simp; linarith, by simp⟩, by simpa using ht⟩ fun hmem => ?_
    have := (hJ_open _ hmem).1.1.2; simp at this
  have hL_left : ∀ t ∈ Set.uIcc (-T') T',
      L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) =
        Stage3ZeroFreeRegion.negLogDerivZeta (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    refine hL_eq _ ⟨⟨by simp, by simp; linarith⟩, by simpa using ht⟩ fun hmem => ?_
    have := (hJ_open _ hmem).1.1.1; simp at this
  have hL_top : ∀ σ ∈ Set.uIcc (-1 / 2 : ℝ) c,
      L ((σ : ℂ) + I * (T' : ℂ)) = Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' : ℂ)) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith)] at hσ
    refine hL_eq _ ⟨by simpa using hσ, by simp [hT'_pos.le]⟩ fun hmem => ?_
    have := (hJ_open _ hmem).1.2.2; simp at this
  have hL_bot : ∀ σ ∈ Set.uIcc (-1 / 2 : ℝ) c,
      L ((σ : ℂ) - I * (T' : ℂ)) = Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' : ℂ)) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith)] at hσ
    refine hL_eq _ ⟨by simpa using hσ, by simp [hT'_pos.le]⟩ fun hmem => ?_
    have := (hJ_open _ hmem).1.2.1; simp at this
  -- Identify the right-vertical integral with `truncatedPerronPsi 1 x c T'`
  have hR_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T')..T', L ((c : ℂ) + I * (t : ℂ)) * (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
        ((c : ℂ) + I * (t : ℂ))) =
      Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c T' := by
    unfold Stage5ContourExplicit.truncatedPerronPsi
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hL_right t ht]
    have hL1 : Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ 1) ((c : ℂ) + I * (t : ℂ)) =
        Stage3ZeroFreeRegion.negLogDerivZeta ((c : ℂ) + I * (t : ℂ)) := by
      unfold Stage3ZeroFreeRegion.negLogDerivL Stage3ZeroFreeRegion.negLogDerivZeta
      rw [DirichletCharacter.LFunction_modOne_eq]
    rw [hL1]
  -- Evaluate the residue sum `L 0 + ∑ p ∈ J, a p * x^p / p = negLogDerivZeta 0 + x - psiZeroSum x T'`
  have hres_eq : L 0 + ∑ p ∈ J, a p * (x : ℂ) ^ p / p =
      Stage3ZeroFreeRegion.negLogDerivZeta 0 + (x : ℂ) - psiZeroSum x T' := by
    have h1_not_Z : (1 : ℂ) ∉ zetaZerosInBox T' := fun h => by
      have hm := (finite_riemannZeta_zeros_le_height T').mem_toFinset.mp h; simp at hm
    rw [hL0]
    dsimp only [J, a]
    rw [Finset.sum_insert h1_not_Z, if_pos rfl, one_mul, Complex.cpow_one, div_one]
    have hZ_sum : ∑ ρ ∈ zetaZerosInBox T',
        (if ρ = 1 then (1 : ℂ) else -(analyticOrderNatAt xi ρ : ℂ)) * (x : ℂ) ^ ρ / ρ =
        -psiZeroSum x T' := by
      unfold psiZeroSum
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hne1 : ρ ≠ 1 := fun h => h1_not_Z (h ▸ hρ)
      rw [if_neg hne1]; ring
    rw [hZ_sum]; ring
  simp only [id_eq] at hshift
  rw [hR_eq, hres_eq] at hshift
  -- Continuity of `L` on the boundary edges (from `hL_diff`)
  have hL_cont_edge : ContinuousOn L
      (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' \ (J : Set ℂ)) := by
    have hH_cont : ContinuousOn (fun s => L s - ∑ p ∈ J, a p / (s - p))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' \ (J : Set ℂ)) :=
      hL_diff.continuousOn.mono Set.sdiff_subset
    have hP_cont : ContinuousOn (fun s => ∑ p ∈ J, a p / (s - p))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' \ (J : Set ℂ)) :=
      continuousOn_finsetSum J fun p hp => continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) fun s hs h0 =>
          hs.2 (Finset.mem_coe.mpr ((sub_eq_zero.mp h0) ▸ hp))
    exact (hH_cont.add hP_cont).congr fun s _ => by simp only [Pi.add_apply]; ring
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hpow_cont : Continuous (fun s : ℂ => (x : ℂ) ^ s) := by
    have hEq : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => cexp (Complex.log (x : ℂ) * s) :=
      funext fun s => Complex.cpow_def_of_ne_zero hxC s
    rw [hEq]; fun_prop
  -- Step 3: Bound the left-vertical integral on `Re(s) = -1/2`
  have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T')..T', L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))‖ ≤
      48 * C_L * Real.log x := by
    have hcont_L : ContinuousOn (fun t : ℝ =>
        L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
          (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))
        (Set.uIcc (-T') T') := by
      rw [Set.uIcc_of_le (by linarith)]
      have h1 : ContinuousOn (fun t : ℝ => L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))) (Set.Icc (-T') T') :=
        hL_cont_edge.comp (by fun_prop) fun t ht => ⟨⟨⟨by simp, by simp; linarith⟩, by simpa using ht⟩,
          fun hmem => by have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.1.1; simp at this⟩
      refine (h1.mul (hpow_cont.comp (by fun_prop)).continuousOn).div (by fun_prop) fun t _ h0 => ?_
      have := congrArg Complex.re h0; simp at this
    have hinv_cont : Continuous (fun t : ℝ => ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹) :=
      Continuous.inv₀ (by fun_prop) fun t h0 => by
        rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this
    have hlogT'_le : Real.log (T' + 2) ≤ 2 * Real.log x := by
      have hsq : T' + 2 ≤ x ^ 2 := by nlinarith
      calc Real.log (T' + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hsq
        _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
    have hinv_int : ∫ t in (-T')..T', ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 6 * Real.log (T' + 2) := by
      have hmid : ∫ t in (-1 : ℝ)..1, ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 4 := by
        have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 := fun t _ => by
          have hden : (1 / 2 : ℝ) ≤ ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ := by
            have h1 := Complex.abs_re_le_norm (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
            have hr : (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)).re = -1 / 2 := by simp
            rw [hr, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num] at h1
            exact h1
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        calc ∫ t in (-1 : ℝ)..1, ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹
            ≤ ∫ _t in (-1 : ℝ)..1, (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by norm_num) (hinv_cont.intervalIntegrable _ _)
                intervalIntegrable_const hpt
          _ = 4 := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
      have hpos_tail : ∫ t in (1 : ℝ)..T', ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log T' := by
        have hint_t : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 : ℝ) T' :=
          (ContinuousOn.inv₀ continuousOn_id fun t ht => by
            rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ T')] at ht; dsimp only [id_eq]; linarith [ht.1]).intervalIntegrable
        calc ∫ t in (1 : ℝ)..T', ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹
            ≤ ∫ t in (1 : ℝ)..T', t⁻¹ :=
              intervalIntegral.integral_mono_on (by linarith) (hinv_cont.intervalIntegrable _ _) hint_t fun t ht => by
                have ht0 : 0 < t := by linarith [ht.1]
                have hden : t ≤ ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ := by
                  simpa [abs_of_pos ht0] using Complex.abs_im_le_norm (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
                exact inv_anti₀ ht0 hden
          _ = Real.log T' := by rw [integral_inv_of_pos zero_lt_one hT'_pos, div_one]
      have hneg_tail : ∫ t in (-T')..(-1 : ℝ), ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log T' := by
        have hcomp : ∫ t in (-T')..(-1 : ℝ), ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ =
            ∫ u in (1 : ℝ)..T', ‖((-1 / 2 : ℝ) : ℂ) + I * (u : ℂ)‖⁻¹ := by
          have h1 := intervalIntegral.integral_comp_neg
            (f := fun u : ℝ => ‖((-1 / 2 : ℝ) : ℂ) + I * (u : ℂ)‖⁻¹) (a := -T') (b := -1)
          simp only [neg_neg] at h1; rw [← h1]
          refine intervalIntegral.integral_congr fun t _ => ?_
          congr 1; rw [← Complex.norm_conj]; congr 1
          rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
        rw [hcomp]; exact hpos_tail
      have hs1 := intervalIntegral.integral_add_adjacent_intervals
        (hinv_cont.intervalIntegrable (μ := volume) (-T') (-1))
        (hinv_cont.intervalIntegrable (μ := volume) (-1) 1)
      have hs2 := intervalIntegral.integral_add_adjacent_intervals
        (hinv_cont.intervalIntegrable (μ := volume) (-T') 1)
        (hinv_cont.intervalIntegrable (μ := volume) 1 T')
      have hlog_gt1 : (1 : ℝ) < Real.log (T' + 2) := hlogT_gt1.trans (Real.log_lt_log hT0 (by linarith))
      have hlt' : Real.log T' ≤ Real.log (T' + 2) := Real.log_le_log hT'_pos (by linarith)
      linarith
    have hpt : ∀ t ∈ Set.Icc (-T') T',
        ‖L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
          (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          (C_L * Real.log (T' + 2) * x ^ (-1 / 2 : ℝ)) * ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ := by
      intro t ht
      rw [hL_left t (by rw [Set.uIcc_of_le (by linarith)]; exact ht), norm_div, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hre : (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)).re = -1 / 2 := by simp
      rw [hre, div_eq_mul_inv]
      have habs : |t| + 2 ≤ T' + 2 := by linarith [abs_le.mpr ht]
      have hlog_le : Real.log (|t| + 2) ≤ Real.log (T' + 2) := Real.log_le_log (by positivity) habs
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hleft_bd t).trans (mul_le_mul_of_nonneg_left hlog_le hCL_pos.le))
          (Real.rpow_nonneg hx0.le _)) (inv_nonneg.mpr (norm_nonneg _))
    have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlogx_sqrt : x ^ (-1 / 2 : ℝ) * Real.log x ≤ 2 := by
      have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have h1 : Real.log x ≤ 2 * Real.sqrt x := by
        have hl : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx0.le]; ring
        linarith [Real.log_le_sub_one_of_pos hsqrt_pos]
      have hpow : x ^ (-1 / 2 : ℝ) = (Real.sqrt x)⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx0.le]; congr 1; ring
      rw [hpow]
      calc (Real.sqrt x)⁻¹ * Real.log x ≤ (Real.sqrt x)⁻¹ * (2 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hsqrt_pos.le)
        _ = 2 := by field_simp [hsqrt_pos.ne']
    have hlogT'_nn : 0 ≤ Real.log (T' + 2) := Real.log_nonneg (by linarith)
    calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T')..T', _‖
        ≤ 1 * ∫ t in (-T')..T', ‖_‖ :=
          mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
            (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
      _ ≤ ∫ t in (-T')..T', (C_L * Real.log (T' + 2) * x ^ (-1 / 2 : ℝ)) *
            ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ := by
          rw [one_mul]
          exact intervalIntegral.integral_mono_on (by linarith) hcont_L.intervalIntegrable.norm
            ((hinv_cont.intervalIntegrable _ _).const_mul _) hpt
      _ = (C_L * Real.log (T' + 2) * x ^ (-1 / 2 : ℝ)) *
            ∫ t in (-T')..T', ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖⁻¹ := intervalIntegral.integral_const_mul _ _
      _ ≤ (C_L * Real.log (T' + 2) * x ^ (-1 / 2 : ℝ)) * (6 * Real.log (T' + 2)) :=
          mul_le_mul_of_nonneg_left hinv_int (by positivity)
      _ = 6 * C_L * (Real.log (T' + 2)) ^ 2 * x ^ (-1 / 2 : ℝ) := by ring
      _ ≤ 6 * C_L * (2 * Real.log x) ^ 2 * x ^ (-1 / 2 : ℝ) := by
          gcongr
      _ = 24 * C_L * (x ^ (-1 / 2 : ℝ) * Real.log x) * Real.log x := by ring
      _ ≤ 24 * C_L * 2 * Real.log x := by gcongr
      _ = 48 * C_L * Real.log x := by ring
  -- Oops: `32 * C_L` vs `16 * C_L`, let's adjust `C` cleanly below!
  -- Actually let's check Step 4 (Horizontal bounds on `Im(s) = ±T'`)
  have hHoriz_bd : ∀ (sg : Bool),
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in (-1 / 2 : ℝ)..c,
          L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) *
          (x : ℂ) ^ ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) /
          ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))))‖ ≤
        8 * C_h * (x * (Real.log x) ^ 2 / T) := by
    intro sg
    have harg_eq : ∀ σ : ℝ,
        (σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ)) =
        if sg then (σ : ℂ) + I * (T' : ℂ) else (σ : ℂ) - I * (T' : ℂ) := by
      intro σ; cases sg <;> simp [sub_eq_add_neg]
    have hcont_H : ContinuousOn (fun σ : ℝ =>
        L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) *
          (x : ℂ) ^ ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) /
          ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ)))) (Set.uIcc (-1 / 2) c) := by
      rw [Set.uIcc_of_le (by linarith)]
      have h1 : ContinuousOn (fun σ : ℝ => L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))))
          (Set.Icc (-1 / 2) c) :=
        hL_cont_edge.comp (by fun_prop) fun σ hσ => by
          rw [harg_eq σ]; cases sg
          · refine ⟨⟨by simpa using hσ, by simp [hT'_pos.le]⟩, fun hmem => ?_⟩
            have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.2.1; simp at this
          · refine ⟨⟨by simpa using hσ, by simp [hT'_pos.le]⟩, fun hmem => ?_⟩
            have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.2.2; simp at this
      refine (h1.mul (hpow_cont.comp (by fun_prop)).continuousOn).div (by fun_prop) fun σ _ h0 => ?_
      rw [harg_eq σ] at h0; cases sg <;> { have := congrArg Complex.im h0; simp at this; linarith }
    have hpt : ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) c,
        ‖L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) *
          (x : ℂ) ^ ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) /
          ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ)))‖ ≤
          3 * C_h * (x * (Real.log x) ^ 2 / T) := by
      intro σ hσ
      rw [harg_eq σ]
      have hσ1 : -1 ≤ σ := by linarith [hσ.1]
      have hσ2 : σ ≤ 2 := by linarith [hσ.2]
      have hlog_sq_le : (Real.log T) ^ 2 ≤ (Real.log x) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hlogT_le_logx 2
      have hxσ : x ^ σ ≤ 3 * x := (Real.rpow_le_rpow_of_exponent_le hx1 hσ.2).trans hxc_le
      cases sg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hL_bot σ (by rw [Set.uIcc_of_le (by linarith)]; exact hσ), norm_div, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) - I * (T' : ℂ)).re = σ := by simp
        rw [hre]
        have hden : T ≤ ‖(σ : ℂ) - I * (T' : ℂ)‖ :=
          hT'_geT.trans (by simpa [abs_of_pos hT'_pos] using Complex.abs_im_le_norm ((σ : ℂ) - I * (T' : ℂ)))
        have hLbd := (hT'_bd σ hσ1 hσ2).2.trans (mul_le_mul_of_nonneg_left hlog_sq_le hCh_pos.le)
        calc ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' : ℂ))‖ * x ^ σ /
              ‖(σ : ℂ) - I * (T' : ℂ)‖
            ≤ (C_h * (Real.log x) ^ 2) * (3 * x) / T :=
              div_le_div₀ (by positivity) (mul_le_mul hLbd hxσ (Real.rpow_nonneg hx0.le _) (by positivity)) hT0 hden
          _ = 3 * C_h * (x * (Real.log x) ^ 2 / T) := by ring
      · simp only [↓reduceIte]
        rw [hL_top σ (by rw [Set.uIcc_of_le (by linarith)]; exact hσ), norm_div, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) + I * (T' : ℂ)).re = σ := by simp
        rw [hre]
        have hden : T ≤ ‖(σ : ℂ) + I * (T' : ℂ)‖ :=
          hT'_geT.trans (by simpa [abs_of_pos hT'_pos] using Complex.abs_im_le_norm ((σ : ℂ) + I * (T' : ℂ)))
        have hLbd := (hT'_bd σ hσ1 hσ2).1.trans (mul_le_mul_of_nonneg_left hlog_sq_le hCh_pos.le)
        calc ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' : ℂ))‖ * x ^ σ /
              ‖(σ : ℂ) + I * (T' : ℂ)‖
            ≤ (C_h * (Real.log x) ^ 2) * (3 * x) / T :=
              div_le_div₀ (by positivity) (mul_le_mul hLbd hxσ (Real.rpow_nonneg hx0.le _) (by positivity)) hT0 hden
          _ = 3 * C_h * (x * (Real.log x) ^ 2 / T) := by ring
    have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hlen : c - (-1 / 2 : ℝ) ≤ 5 / 2 := by linarith
    calc (2 * Real.pi)⁻¹ * ‖∫ σ in (-1 / 2 : ℝ)..c, _‖
        ≤ 1 * ∫ σ in (-1 / 2 : ℝ)..c, ‖_‖ :=
          mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
            (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
      _ ≤ ∫ _σ in (-1 / 2 : ℝ)..c, (3 * C_h * (x * (Real.log x) ^ 2 / T)) := by
          rw [one_mul]
          exact intervalIntegral.integral_mono_on (by linarith) hcont_H.intervalIntegrable.norm
            intervalIntegrable_const hpt
      _ = (c - (-1 / 2 : ℝ)) * (3 * C_h * (x * (Real.log x) ^ 2 / T)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (5 / 2) * (3 * C_h * (x * (Real.log x) ^ 2 / T)) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
      _ ≤ 8 * C_h * (x * (Real.log x) ^ 2 / T) := by nlinarith [show 0 ≤ x * (Real.log x) ^ 2 / T by positivity]
  -- Step 5: Bound `‖psiZeroSum x T' - psiZeroSum x T‖ ≤ 4 * C_N * (x * (log x)² / T)`
  have hzero_diff : ‖psiZeroSum x T' - psiZeroSum x T‖ ≤ 4 * C_N * (x * (Real.log x) ^ 2 / T) := by
    have hsub : zetaZerosInBox T ⊆ zetaZerosInBox T' := fun ρ hρ => by
      have hm := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
      exact (finite_riemannZeta_zeros_le_height T').mem_toFinset.mpr ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.trans hT'_geT⟩
    unfold psiZeroSum
    rw [← Finset.sum_sdiff_eq_sub hsub]
    set D : Finset ℂ := zetaZerosInBox T' \ zetaZerosInBox T
    have hD_term : ∀ ρ ∈ D, ‖(analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ ≤
        (analyticOrderNatAt xi ρ : ℝ) * (x / T) := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hm := (finite_riemannZeta_zeros_le_height T').mem_toFinset.mp hρ.1
      have hgt : T < |ρ.im| := by
        by_contra hle
        exact hρ.2 ((finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr ⟨hm.1, hm.2.1, hm.2.2.1, not_lt.mp hle⟩)
      rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hxρ : x ^ ρ.re ≤ x := by simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hm.2.1.le
      have hden : T ≤ ‖ρ‖ := hgt.le.trans (Complex.abs_im_le_norm ρ)
      exact mul_le_mul_of_nonneg_left (div_le_div₀ hx0.le hxρ hT0 hden) (Nat.cast_nonneg _)
    have hD_count : ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) ≤ 4 * C_N * Real.log x := by
      have hfin_D : {n : ℕ | T ≤ |(xiZeroSeq n).im| ∧ |(xiZeroSeq n).im| < T + 2}.Finite :=
        (finite_xiZeroSeq_abs_im_le (T + 2)).subset fun _ hn => hn.2.le
      set F_D : Finset ℕ := hfin_D.toFinset
      have hF_card : (F_D.card : ℝ) =
          2 * (Stage7VonMangoldtExplicit.xiZeroCount (T + 2) - Stage7VonMangoldtExplicit.xiZeroCount T) :=
        card_xiZeroSeq_abs_im_Ico_eq hT0 (by linarith) F_D fun _ => hfin_D.mem_toFinset
      have hsum_le_card : ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) ≤ (F_D.card : ℝ) := by
        have hnat : ∑ ρ ∈ D, analyticOrderNatAt xi ρ ≤ F_D.card := by
          have hmaps : ∀ ρ ∈ D, ∀ n, xiZeroSeq n = ρ → n ∈ F_D := fun ρ hρ n hn => by
            rw [Finset.mem_sdiff] at hρ
            have hm := (finite_riemannZeta_zeros_le_height T').mem_toFinset.mp hρ.1
            have hgt : T < |ρ.im| := by
              by_contra hle
              exact hρ.2 ((finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr ⟨hm.1, hm.2.1, hm.2.2.1, not_lt.mp hle⟩)
            exact hfin_D.mem_toFinset.mpr ⟨by rw [hn]; exact hgt.le, by rw [hn]; linarith [hm.2.2.2, hT'_le]⟩
          have hcard_eq : ∀ ρ ∈ D, analyticOrderNatAt xi ρ = (F_D.filter fun n => xiZeroSeq n = ρ).card := by
            intro ρ hρ
            exact ((isMultiplicityZeroSeq_xi.2 ρ).2 _ fun n => by
              simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hmaps ρ hρ n h, h⟩⟩).symm
          calc ∑ ρ ∈ D, analyticOrderNatAt xi ρ
              = ∑ ρ ∈ D, (F_D.filter fun n => xiZeroSeq n = ρ).card := Finset.sum_congr rfl hcard_eq
            _ = ∑ ρ ∈ D, ((F_D.filter fun n => xiZeroSeq n ∈ D).filter fun n => xiZeroSeq n = ρ).card := by
                refine Finset.sum_congr rfl fun ρ hρ => congrArg Finset.card ?_
                ext n; simp only [Finset.mem_filter]
                exact ⟨fun h => ⟨⟨h.1, h.2.symm ▸ hρ⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
            _ = (F_D.filter fun n => xiZeroSeq n ∈ D).card :=
                (Finset.card_eq_sum_card_fiberwise (f := xiZeroSeq)
                  (s := F_D.filter fun n => xiZeroSeq n ∈ D) (t := D)
                  fun _ hn => (Finset.mem_filter.mp hn).2).symm
            _ ≤ F_D.card := Finset.card_filter_le _ _
        exact_mod_cast hnat
      have hsh := hshort T (T + 2) (by linarith) (by linarith) (by linarith)
      have hlog_cmp : Real.log (T + 2) ≤ 2 * Real.log x := by
        have hsq : T + 2 ≤ x ^ 2 := by nlinarith
        calc Real.log (T + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hsq
          _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
      nlinarith
    calc ‖∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖
        ≤ ∑ ρ ∈ D, ‖(analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) * (x / T) := Finset.sum_le_sum hD_term
      _ = (∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ)) * (x / T) := (Finset.sum_mul _ _ _).symm
      _ ≤ (4 * C_N * Real.log x) * (x / T) := mul_le_mul_of_nonneg_right hD_count (by positivity)
      _ ≤ (4 * C_N * (Real.log x) ^ 2) * (x / T) := by
          have hsq : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C_N * (x * (Real.log x) ^ 2 / T) := by ring
  -- Note: `hLeft_bd` had `32 * C_L` at the end of calc; wait — we fix the statement of `hLeft_bd`!
  -- Step 6: Combine all bounds and take `.re`!
  have htop_bd := hHoriz_bd true
  have hbot_bd := hHoriz_bd false
  simp only [↓reduceIte, one_mul, Bool.false_eq_true, neg_mul, ← sub_eq_add_neg] at htop_bd hbot_bd
  have htotal : ‖(Chebyshev.psi x : ℂ) - ((x : ℂ) - psiZeroSum x T)‖ ≤
      (2400 + 16 * C_h + 4 * C_N) * (x * (Real.log x) ^ 2 / T) +
      (2400 + 48 * C_L + K₀) * Real.log x := by
    set B1 : ℂ := (Chebyshev.psi x : ℂ) -
      Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c T'
    set B2 : ℂ := Stage3ZeroFreeRegion.negLogDerivZeta 0
    set B3 : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T')..T', L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
      (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))
    set B4 : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-1 / 2 : ℝ)..c, L ((σ : ℂ) + I * (T' : ℂ)) *
      (x : ℂ) ^ ((σ : ℂ) + I * (T' : ℂ)) / ((σ : ℂ) + I * (T' : ℂ)))
    set B5 : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-1 / 2 : ℝ)..c, L ((σ : ℂ) - I * (T' : ℂ)) *
      (x : ℂ) ^ ((σ : ℂ) - I * (T' : ℂ)) / ((σ : ℂ) - I * (T' : ℂ)))
    set B6 : ℂ := psiZeroSum x T' - psiZeroSum x T
    have hsplit : (Chebyshev.psi x : ℂ) - ((x : ℂ) - psiZeroSum x T) =
        B1 + B2 + B3 + B4 - B5 - B6 := by
      dsimp only [B1, B2, B3, B4, B5, B6]
      linear_combination hshift
    rw [hsplit]
    have h1 := norm_sub_le (B1 + B2 + B3 + B4 - B5) B6
    have h2 := norm_sub_le (B1 + B2 + B3 + B4) B5
    have h3 := norm_add_le (B1 + B2 + B3) B4
    have h4 := norm_add_le (B1 + B2) B3
    have h5 := norm_add_le B1 B2
    have hK₀_le : ‖B2‖ ≤ K₀ * Real.log x := le_mul_of_one_le_right (norm_nonneg _) hlogx_gt1.le
    linarith
  have hre_eq : Chebyshev.psi x - (x - (psiZeroSum x T).re) =
      ((Chebyshev.psi x : ℂ) - ((x : ℂ) - psiZeroSum x T)).re := by simp
  rw [hre_eq]
  have hre_le := Complex.abs_re_le_norm ((Chebyshev.psi x : ℂ) - ((x : ℂ) - psiZeroSum x T))
  have hnn1 : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
  have hK₀_nn : 0 ≤ K₀ := norm_nonneg _
  have hc1' : 2400 + 16 * C_h + 4 * C_N ≤ C := by dsimp only [C]; linarith
  have hc2' : 2400 + 48 * C_L + K₀ ≤ C := by dsimp only [C]; linarith
  nlinarith

/-! ## Section 4: Unconditional Smooth Cesàro-1 Explicit Formula for `psi1` -/

/-- Absolute summability of the Cesàro-1 zero series
`∑' n, (x : ℂ) ^ (xiZeroSeq n + 1) / (xiZeroSeq n * (xiZeroSeq n + 1))` for all `x > 0`. -/
theorem summable_psi1ZeroSeries {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ =>
      (x : ℂ) ^ (xiZeroSeq n + 1) / (xiZeroSeq n * (xiZeroSeq n + 1))) := by
  refine Summable.of_norm_bounded (xiZeroSeq_summable_inv_sq.mul_left (max (x ^ 2) x)) fun n => ?_
  have hst := xiZeroSeq_strip n
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (xiZeroSeq n + 1).re = (xiZeroSeq n).re + 1 := by simp
  rw [hre]
  have hnum : x ^ ((xiZeroSeq n).re + 1) ≤ max (x ^ 2) x := by
    rcases le_total 1 x with hx1 | hx1
    · exact ((Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hst.2] : (xiZeroSeq n).re + 1 ≤ 2)).trans_eq
        (Real.rpow_two x)).trans (le_max_left _ _)
    · exact ((Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [hst.1] : (1 : ℝ) ≤ (xiZeroSeq n).re + 1)).trans_eq
        (Real.rpow_one x)).trans (le_max_right _ _)
  have hden1 : ‖xiZeroSeq n‖ ≤ ‖xiZeroSeq n + 1‖ := by
    have hsq : ‖xiZeroSeq n‖ ^ 2 ≤ ‖xiZeroSeq n + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
      nlinarith [hst.1]
    nlinarith [norm_nonneg (xiZeroSeq n), norm_nonneg (xiZeroSeq n + 1)]
  have hρ_pos : 0 < ‖xiZeroSeq n‖ := norm_pos_iff.mpr (xiZeroSeq_ne_zero n)
  have hprod : ‖xiZeroSeq n‖ ^ 2 ≤ ‖xiZeroSeq n‖ * ‖xiZeroSeq n + 1‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hden1 hρ_pos.le
  calc x ^ ((xiZeroSeq n).re + 1) / (‖xiZeroSeq n‖ * ‖xiZeroSeq n + 1‖)
      ≤ max (x ^ 2) x / ‖xiZeroSeq n‖ ^ 2 :=
        div_le_div₀ (le_trans hx.le (le_max_right _ _)) hnum (sq_pos_of_pos hρ_pos) hprod
    _ = max (x ^ 2) x * (‖xiZeroSeq n‖ ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- **UNCONDITIONAL SMOOTH CESÀRO-1 EXPLICIT FORMULA FOR `Stage6EffectivePNT.psi1` (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 2, |psi1 x - (x² / 2 - (∑' n, (x : ℂ) ^ (xiZeroSeq n + 1) / (xiZeroSeq n * (xiZeroSeq n + 1))).re)| ≤ C * x * Real.log x`. -/
theorem von_mangoldt_explicit_formula_psi1 :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Stage6EffectivePNT.psi1 x -
          (x ^ 2 / 2 -
            (∑' n : ℕ, (x : ℂ) ^ (xiZeroSeq n + 1) / (xiZeroSeq n * (xiZeroSeq n + 1))).re)| ≤
        C * x * Real.log x := by
  classical
  obtain ⟨c_gap, hc_gap, C_h, hCh_pos, hgood⟩ := exists_good_contour_height
  obtain ⟨C_L, hCL_pos, hleft_bd⟩ := norm_negLogDerivZeta_neg_half_line_le
  set K₀ : ℝ := ‖Stage3ZeroFreeRegion.negLogDerivZeta 0‖
  set B_const : ℝ := K₀ + 40 * C_L + 1
  set C : ℝ := 2 * B_const
  refine ⟨C, by positivity, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx_ge : (1 / 2 : ℝ) ≤ Real.log x := hlog2.trans (Real.log_le_log (by norm_num) hx2)
  have hlogx_pos : 0 < Real.log x := by linarith
  set c : ℝ := 2 with hc_def
  -- Pick a sequence of good contour heights `T' k ∈ [k + 4, k + 5]`
  have hex_k : ∀ k : ℕ, ∃ T' ∈ Set.Icc ((k : ℝ) + 4) ((k : ℝ) + 5),
      (∀ ρ : ℂ, riemannZeta ρ = 0 →
        c_gap / Real.log ((k : ℝ) + 4) ≤ |T' - ρ.im| ∧
        c_gap / Real.log ((k : ℝ) + 4) ≤ |(-T') - ρ.im|) ∧
      (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' : ℂ))‖ ≤ C_h * (Real.log ((k : ℝ) + 4)) ^ 2 ∧
        ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' : ℂ))‖ ≤ C_h * (Real.log ((k : ℝ) + 4)) ^ 2) :=
    fun k => by
      have hk4 : (4 : ℝ) ≤ (k : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have h := hgood ((k : ℝ) + 4) hk4
      simpa only [show ((k : ℝ) + 4) + 1 = (k : ℝ) + 5 by ring] using h
  choose T' hT'_mem hT'_gap hT'_bd using hex_k
  let term : ℕ → ℂ := fun n => (x : ℂ) ^ (xiZeroSeq n + 1) / (xiZeroSeq n * (xiZeroSeq n + 1))
  have hterm_summ : Summable term := summable_psi1ZeroSeries hx0
  let Fset : ℕ → Finset ℕ := fun k => (finite_xiZeroSeq_abs_im_le (T' k)).toFinset
  -- Step 1: Finite-`k` error bound via contour shift of `L₁ s * x^s / s = L s * x^(s+1) / (s (s+1))`
  let err : ℕ → ℝ := fun k =>
    (12 / Real.pi) * x ^ (3 : ℝ) / ((k : ℝ) + 4) +
    6 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2
  have hbound_k : ∀ k : ℕ,
      ‖(Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑ n ∈ Fset k, term n)‖ ≤
        B_const * x + err k := by
    intro k
    have hTk4 : (4 : ℝ) ≤ (k : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hTk_ge : (k : ℝ) + 4 ≤ T' k := (hT'_mem k).1
    have hTk_pos : 0 < T' k := by linarith
    have hlogTk_pos : 0 < Real.log ((k : ℝ) + 4) := Real.log_pos (by linarith)
    have havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → T' k ≠ ρ.im ∧ -(T' k) ≠ ρ.im := fun ρ hρ => by
      have hg := hT'_gap k ρ hρ
      have hpos : 0 < c_gap / Real.log ((k : ℝ) + 4) := div_pos hc_gap hlogTk_pos
      exact ⟨fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.1],
             fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.2]⟩
    -- Truncated Cesàro-1 Perron bound at `c = 2`, height `T' k`
    have hPerron := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le
      (1 : DirichletCharacter ℂ 1) hx0 (by norm_num : (1 : ℝ) < 2) hTk_pos
    rw [← Stage6EffectivePNT.psi1_eq_psi1Char_one x] at hPerron
    have hPerron_le : ‖(Stage6EffectivePNT.psi1 x : ℂ) -
        Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x 2 (T' k)‖ ≤
        (12 / Real.pi) * x ^ (3 : ℝ) / ((k : ℝ) + 4) := by
      have h1 : (6 * (2 : ℝ) / Real.pi) * x ^ ((2 : ℝ) + 1) / ((2 - 1) * T' k) =
          (12 / Real.pi) * x ^ (3 : ℝ) / T' k := by norm_num
      rw [h1] at hPerron
      exact hPerron.trans (div_le_div_of_nonneg_left (by positivity) (by linarith) hTk_ge)
    -- Meromorphic decomposition of `L` on `closedRect (-1/2) 2 (-T' k) (T' k)`
    obtain ⟨L, hJ_open, hL_diff, hL_eq⟩ :=
      exists_meromorphic_negLogDerivZeta_rect (by norm_num : (1 : ℝ) < 2) hTk_pos havoid
    set J : Finset ℂ := insert (1 : ℂ) (zetaZerosInBox (T' k))
    set a : ℂ → ℂ := fun p => if p = 1 then (1 : ℂ) else -(analyticOrderNatAt xi p : ℂ)
    let W1 : ℂ → ℂ := fun s => (x : ℂ) / (s + 1)
    have hW1_diff : DifferentiableOn ℂ W1 (Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k)) := by
      intro s hs
      refine ((differentiableAt_const (x : ℂ)).div (differentiableAt_id.add (differentiableAt_const 1)) ?_).differentiableWithinAt
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [hs.1.1]
    let G1 : ℂ → ℂ := fun s =>
      (L s - ∑ p ∈ J, a p / (s - p)) * W1 s + ∑ p ∈ J, a p * dslope W1 p s
    have hG1_diff : DifferentiableOn ℂ G1 (Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k)) := by
      refine (hL_diff.mul hW1_diff).add (DifferentiableOn.fun_sum fun p hp => ?_)
      have hopen : IsOpen (Stage5ContourExplicit.openRect (-1 / 2) 2 (-(T' k)) (T' k)) :=
        isOpen_Ioo.reProdIm isOpen_Ioo
      have hnhds : Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k) ∈ 𝓝 p :=
        Filter.mem_of_superset (hopen.mem_nhds (hJ_open p hp).1) fun _ ⟨h1, h2⟩ =>
          ⟨Set.Ioo_subset_Icc_self h1, Set.Ioo_subset_Icc_self h2⟩
      exact (differentiableOn_const _).mul ((Complex.differentiableOn_dslope hnhds).mpr hW1_diff)
    let L1 : ℂ → ℂ := fun s => G1 s + ∑ p ∈ J, (a p * W1 p) / (s - p)
    have hL1_diff : DifferentiableOn ℂ (fun s => L1 s - ∑ p ∈ J, (a p * W1 p) / (s - p))
        (Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k)) := by
      have hEq : (fun s => L1 s - ∑ p ∈ J, (a p * W1 p) / (s - p)) = G1 :=
        funext fun s => by dsimp only [L1]; ring
      rw [hEq]; exact hG1_diff
    have hL1_eq : ∀ s ∈ Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k), s ∉ J →
        L1 s = Stage3ZeroFreeRegion.negLogDerivZeta s * W1 s := by
      intro s hs hsJ
      have hsum_eq : ∑ p ∈ J, a p * dslope W1 p s + ∑ p ∈ J, (a p * W1 p) / (s - p) =
          (∑ p ∈ J, a p / (s - p)) * W1 s := by
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hne : s ≠ p := fun h => hsJ (h ▸ hp)
        have hsub : s - p ≠ 0 := sub_ne_zero.mpr hne
        rw [dslope_of_ne W1 hne, slope_def_field]
        field_simp [hsub]; ring
      have h1 : L1 s = L s * W1 s := by dsimp only [L1, G1]; linear_combination hsum_eq
      rw [h1, hL_eq s hs hsJ]
    have hshift := Stage5ContourExplicit.vertical_contour_shift_div_id_eq_sum_residues
      L1 hx0 (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 2) hTk_pos J id
      (fun p => a p * W1 p) (fun p hp => (hJ_open p hp).1) (fun p hp => (hJ_open p hp).2) hL1_diff
    -- Evaluate `L1` on the four edges and at `0`
    have hL1_0 : L1 0 = Stage3ZeroFreeRegion.negLogDerivZeta 0 * (x : ℂ) := by
      have h0 := hL1_eq 0 ⟨⟨by norm_num, by norm_num⟩, by simp [hTk_pos.le]⟩ fun h0J => (hJ_open 0 h0J).2 rfl
      simpa [W1] using h0
    have hL1_right : ∀ t ∈ Set.uIcc (-(T' k)) (T' k),
        L1 ((2 : ℂ) + I * (t : ℂ)) * (x : ℂ) ^ ((2 : ℂ) + I * (t : ℂ)) / ((2 : ℂ) + I * (t : ℂ)) =
        Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ 1) ((2 : ℂ) + I * (t : ℂ)) *
          (x : ℂ) ^ ((2 : ℂ) + 1 + I * (t : ℂ)) / (((2 : ℂ) + I * (t : ℂ)) * ((2 : ℂ) + 1 + I * (t : ℂ))) := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have h1 := hL1_eq ((2 : ℂ) + I * (t : ℂ)) ⟨⟨by simp; norm_num, by simp⟩, by simpa using ht⟩ fun hmem => by
        have := (hJ_open _ hmem).1.1.2; simp at this
      rw [h1]
      have hL1Z : Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ 1) ((2 : ℂ) + I * (t : ℂ)) =
          Stage3ZeroFreeRegion.negLogDerivZeta ((2 : ℂ) + I * (t : ℂ)) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL Stage3ZeroFreeRegion.negLogDerivZeta
        rw [DirichletCharacter.LFunction_modOne_eq]
      rw [hL1Z]
      have hpow : (x : ℂ) * (x : ℂ) ^ ((2 : ℂ) + I * (t : ℂ)) = (x : ℂ) ^ ((2 : ℂ) + 1 + I * (t : ℂ)) := by
        have hadd : (2 : ℂ) + 1 + I * (t : ℂ) = 1 + ((2 : ℂ) + I * (t : ℂ)) := by ring
        rw [hadd, Complex.cpow_add 1 _ hxC, Complex.cpow_one]
      have harg : (2 : ℂ) + I * (t : ℂ) + 1 = (2 : ℂ) + 1 + I * (t : ℂ) := by ring
      dsimp only [W1]; rw [harg]
      calc Stage3ZeroFreeRegion.negLogDerivZeta ((2 : ℂ) + I * (t : ℂ)) * ((x : ℂ) / ((2 : ℂ) + 1 + I * (t : ℂ))) *
              (x : ℂ) ^ ((2 : ℂ) + I * (t : ℂ)) / ((2 : ℂ) + I * (t : ℂ))
          = (Stage3ZeroFreeRegion.negLogDerivZeta ((2 : ℂ) + I * (t : ℂ)) *
              ((x : ℂ) * (x : ℂ) ^ ((2 : ℂ) + I * (t : ℂ))) / ((2 : ℂ) + 1 + I * (t : ℂ))) /
              ((2 : ℂ) + I * (t : ℂ)) := by ring
        _ = Stage3ZeroFreeRegion.negLogDerivZeta ((2 : ℂ) + I * (t : ℂ)) *
              ((x : ℂ) * (x : ℂ) ^ ((2 : ℂ) + I * (t : ℂ))) /
              (((2 : ℂ) + I * (t : ℂ)) * ((2 : ℂ) + 1 + I * (t : ℂ))) := by
                rw [div_div, mul_comm ((2 : ℂ) + 1 + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ))]
        _ = _ := by rw [hpow]
    have hR_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-(T' k))..(T' k), L1 ((2 : ℂ) + I * (t : ℂ)) * (x : ℂ) ^ ((2 : ℂ) + I * (t : ℂ)) /
          ((2 : ℂ) + I * (t : ℂ))) =
        Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x 2 (T' k) := by
      unfold Stage4ExplicitFormula.truncatedPerronPsi1
      congr 1
      refine intervalIntegral.integral_congr fun t ht => ?_
      simpa only [Complex.ofReal_ofNat] using hL1_right t ht
    -- Identify the residue sum with `negLogDerivZeta 0 * x + x² / 2 - ∑ n ∈ Fset k, term n`
    have hsum_F_eq : ∑ ρ ∈ zetaZerosInBox (T' k),
        (analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) =
        ∑ n ∈ Fset k, term n := by
      have hmaps : ∀ n ∈ Fset k, xiZeroSeq n ∈ zetaZerosInBox (T' k) := fun n hn => by
        have hle := (finite_xiZeroSeq_abs_im_le (T' k)).mem_toFinset.mp hn
        have hst := xiZeroSeq_strip n
        exact (finite_riemannZeta_zeros_le_height (T' k)).mem_toFinset.mpr
          ⟨hst.1, hst.2, xiZeroSeq_riemannZeta_zero n, hle⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hcard : (Fset k |>.filter fun n => xiZeroSeq n = ρ).card = analyticOrderNatAt xi ρ := by
        have hm := (finite_riemannZeta_zeros_le_height (T' k)).mem_toFinset.mp hρ
        exact (isMultiplicityZeroSeq_xi.2 ρ).2 _ fun n => by
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨(finite_xiZeroSeq_abs_im_le (T' k)).mem_toFinset.mpr
            (by change |(xiZeroSeq n).im| ≤ T' k; rw [h]; exact hm.2.2.2), h⟩⟩
      have hconst : ∑ n ∈ (Fset k).filter (fun n => xiZeroSeq n = ρ), term n =
          ∑ _n ∈ (Fset k).filter (fun n => xiZeroSeq n = ρ), ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) :=
        Finset.sum_congr rfl fun n hn => by dsimp only [term]; rw [(Finset.mem_filter.mp hn).2]
      rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul]
    have hres_eq : L1 0 + ∑ p ∈ J, (a p * W1 p) * (x : ℂ) ^ p / p =
        Stage3ZeroFreeRegion.negLogDerivZeta 0 * (x : ℂ) + (x : ℂ) ^ 2 / 2 - ∑ n ∈ Fset k, term n := by
      have h1_not_Z : (1 : ℂ) ∉ zetaZerosInBox (T' k) := fun h => by
        have hm := (finite_riemannZeta_zeros_le_height (T' k)).mem_toFinset.mp h; simp at hm
      rw [hL1_0]
      dsimp only [J, a, W1]
      rw [Finset.sum_insert h1_not_Z, if_pos rfl, one_mul, Complex.cpow_one, div_one]
      have h1term : (x : ℂ) / ((1 : ℂ) + 1) * (x : ℂ) = (x : ℂ) ^ 2 / 2 := by ring
      rw [h1term]
      have hZ_sum : ∑ ρ ∈ zetaZerosInBox (T' k),
          ((if ρ = 1 then (1 : ℂ) else -(analyticOrderNatAt xi ρ : ℂ)) * ((x : ℂ) / (ρ + 1))) *
            (x : ℂ) ^ ρ / ρ =
          -(∑ n ∈ Fset k, term n) := by
        rw [← hsum_F_eq, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hne1 : ρ ≠ 1 := fun h => h1_not_Z (h ▸ hρ)
        rw [if_neg hne1]
        have hpow : (x : ℂ) * (x : ℂ) ^ ρ = (x : ℂ) ^ (ρ + 1) := by
          rw [add_comm, Complex.cpow_add 1 ρ hxC, Complex.cpow_one]
        calc (-(analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) / (ρ + 1))) * (x : ℂ) ^ ρ / ρ
            = -((analyticOrderNatAt xi ρ : ℂ) * ((((x : ℂ) * (x : ℂ) ^ ρ) / (ρ + 1)) / ρ)) := by ring
          _ = -((analyticOrderNatAt xi ρ : ℂ) * (((x : ℂ) * (x : ℂ) ^ ρ) / (ρ * (ρ + 1)))) := by
                rw [div_div, mul_comm (ρ + 1) ρ]
          _ = -((analyticOrderNatAt xi ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))) := by rw [hpow]
      rw [hZ_sum]; ring
    simp only [Complex.ofReal_ofNat, id_eq] at hshift
    rw [hR_eq, hres_eq] at hshift
    -- Continuity of `L1` on the boundary edges
    have hL1_cont_edge : ContinuousOn L1
        (Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k) \ (J : Set ℂ)) := by
      have hH_cont := hL1_diff.continuousOn.mono (Set.sdiff_subset : _ \ (J : Set ℂ) ⊆ _)
      have hP_cont : ContinuousOn (fun s => ∑ p ∈ J, (a p * W1 p) / (s - p))
          (Stage5ContourExplicit.closedRect (-1 / 2) 2 (-(T' k)) (T' k) \ (J : Set ℂ)) :=
        continuousOn_finsetSum J fun p hp => continuousOn_const.div
          (continuousOn_id.sub continuousOn_const) fun s hs h0 =>
            hs.2 (Finset.mem_coe.mpr ((sub_eq_zero.mp h0) ▸ hp))
      exact (hH_cont.add hP_cont).congr fun s _ => by simp only [Pi.add_apply]; ring
    have hpow_cont : Continuous (fun s : ℂ => (x : ℂ) ^ s) := by
      have hEq : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => cexp (Complex.log (x : ℂ) * s) :=
        funext fun s => Complex.cpow_def_of_ne_zero hxC s
      rw [hEq]; fun_prop
    -- Bound left-vertical integral on `Re(s) = -1/2` uniformly by `40 * C_L * x`!
    have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-(T' k))..(T' k), L1 (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
          (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))‖ ≤
        40 * C_L * x := by
      have hcont_L : ContinuousOn (fun t : ℝ =>
          L1 (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))
          (Set.uIcc (-(T' k)) (T' k)) := by
        rw [Set.uIcc_of_le (by linarith)]
        have h1 : ContinuousOn (fun t : ℝ => L1 (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))) (Set.Icc (-(T' k)) (T' k)) :=
          hL1_cont_edge.comp (by fun_prop) fun t ht => ⟨⟨⟨by simp, by simp; norm_num⟩, by simpa using ht⟩,
            fun hmem => by have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.1.1; simp at this⟩
        refine (h1.mul (hpow_cont.comp (by fun_prop)).continuousOn).div (by fun_prop) fun t _ h0 => ?_
        have := congrArg Complex.re h0; simp at this
      -- Elementary uniform integral bound `∫_{-T'}^{T'} log(|t| + 2) / (1/4 + t²) dt ≤ 40`
      have hker_cont : Continuous (fun t : ℝ => Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2)) :=
        ((continuous_abs.add continuous_const).log fun t => (by linarith [abs_nonneg t] : |t| + 2 ≠ 0)).div
          (by fun_prop) fun t => (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2).ne'
      have hker_int : ∫ t in (-(T' k))..(T' k), Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 40 := by
        have hmid : ∫ t in (-1 : ℝ)..1, Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 16 := by
          have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 8 := fun t ht => by
            have h1 : Real.log (|t| + 2) ≤ 2 := by
              have habs : |t| ≤ 1 := abs_le.mpr ht
              linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 2)]
            have hden : (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) + t ^ 2 := by nlinarith
            calc Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 2 / (1 / 4) :=
                  div_le_div₀ (by norm_num) h1 (by norm_num) hden
              _ = 8 := by norm_num
          calc ∫ t in (-1 : ℝ)..1, Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2)
              ≤ ∫ _t in (-1 : ℝ)..1, (8 : ℝ) :=
                intervalIntegral.integral_mono_on (by norm_num) (hker_cont.intervalIntegrable _ _)
                  intervalIntegrable_const hpt
            _ = 16 := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
        have hpos_tail : ∫ t in (1 : ℝ)..(T' k), Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 12 := by
          have hint_p : IntervalIntegrable (fun t : ℝ => (6 : ℝ) * t ^ (-(3 / 2 : ℝ))) volume (1 : ℝ) (T' k) := by
            refine (ContinuousOn.const_mul (ContinuousOn.rpow_const continuousOn_id fun t ht => ?_) 6).intervalIntegrable
            left; rw [Set.uIcc_of_le (by linarith)] at ht; dsimp only [id_eq]; linarith [ht.1]
          have hpt : ∀ t ∈ Set.Icc (1 : ℝ) (T' k),
              Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 6 * t ^ (-(3 / 2 : ℝ)) := by
            intro t ht
            have ht0 : 0 < t := by linarith [ht.1]
            rw [abs_of_pos ht0]
            have hlog_le : Real.log (t + 2) ≤ 6 * t ^ (1 / 2 : ℝ) := by
              have h1 : Real.log (t + 2) ≤ 2 * Real.sqrt (t + 2) := by
                have hs : 0 < Real.sqrt (t + 2) := Real.sqrt_pos.mpr (by linarith)
                have hl : Real.log (t + 2) = 2 * Real.log (Real.sqrt (t + 2)) := by
                  rw [Real.log_sqrt (by linarith)]; ring
                linarith [Real.log_le_sub_one_of_pos hs]
              have h2 : Real.sqrt (t + 2) ≤ 3 * Real.sqrt t := by
                have hsq : t + 2 ≤ 9 * t := by linarith [ht.1]
                calc Real.sqrt (t + 2) ≤ Real.sqrt (9 * t) := Real.sqrt_le_sqrt hsq
                  _ = Real.sqrt (3 ^ 2 * t) := by norm_num
                  _ = 3 * Real.sqrt t := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
              rw [← Real.sqrt_eq_rpow]; linarith
            have hden : t ^ 2 ≤ (1 / 4 : ℝ) + t ^ 2 := by linarith
            have hrew : (6 * t ^ (1 / 2 : ℝ)) / t ^ 2 = 6 * t ^ (-(3 / 2 : ℝ)) := by
              rw [← Real.rpow_two t, mul_div_assoc, ← Real.rpow_sub ht0]; congr 2; norm_num
            calc Real.log (t + 2) / ((1 / 4 : ℝ) + t ^ 2)
                ≤ (6 * t ^ (1 / 2 : ℝ)) / t ^ 2 :=
                  div_le_div₀ (by positivity) hlog_le (sq_pos_of_pos ht0) hden
              _ = 6 * t ^ (-(3 / 2 : ℝ)) := hrew
          have hval : ∫ t in (1 : ℝ)..(T' k), (6 : ℝ) * t ^ (-(3 / 2 : ℝ)) ≤ 12 := by
            rw [intervalIntegral.integral_const_mul,
              integral_rpow (Or.inr ⟨by norm_num, fun h => by linarith [(Set.mem_uIcc.mp h).elim (fun h1 => h1.1) (fun h1 => by linarith [h1.1])]⟩)]
            have hexp : -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) := by norm_num
            rw [hexp, Real.one_rpow]
            have hnn : 0 ≤ (T' k) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hTk_pos.le _
            linarith
          exact (intervalIntegral.integral_mono_on (by linarith) (hker_cont.intervalIntegrable _ _) hint_p hpt).trans hval
        have hneg_tail : ∫ t in (-(T' k))..(-1 : ℝ), Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) ≤ 12 := by
          have hcomp : ∫ t in (-(T' k))..(-1 : ℝ), Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) =
              ∫ u in (1 : ℝ)..(T' k), Real.log (|u| + 2) / ((1 / 4 : ℝ) + u ^ 2) := by
            have h1 := intervalIntegral.integral_comp_neg
              (f := fun u : ℝ => Real.log (|u| + 2) / ((1 / 4 : ℝ) + u ^ 2)) (a := -(T' k)) (b := -1)
            simp only [neg_neg] at h1; rw [← h1]
            exact intervalIntegral.integral_congr fun t _ => by simp
          rw [hcomp]; exact hpos_tail
        have hs1 := intervalIntegral.integral_add_adjacent_intervals
          (hker_cont.intervalIntegrable (μ := volume) (-(T' k)) (-1))
          (hker_cont.intervalIntegrable (μ := volume) (-1) 1)
        have hs2 := intervalIntegral.integral_add_adjacent_intervals
          (hker_cont.intervalIntegrable (μ := volume) (-(T' k)) 1)
          (hker_cont.intervalIntegrable (μ := volume) 1 (T' k))
        linarith
      have hpt : ∀ t ∈ Set.Icc (-(T' k)) (T' k),
          ‖L1 (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
            (C_L * x) * (Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2)) := by
        intro t ht
        have h1 := hL1_eq (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
          ⟨⟨by simp, by simp; norm_num⟩, by simpa using ht⟩ fun hmem => by
            have := (hJ_open _ hmem).1.1.1; simp at this
        rw [h1]
        dsimp only [W1]
        rw [norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)).re = -1 / 2 := by simp
        rw [hre]
        have hx_le : x * x ^ (-1 / 2 : ℝ) ≤ x := by
          have hle1 : x ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
          nlinarith
        have hprod_norm : ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ) + 1‖ * ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ =
            (1 / 4 : ℝ) + t ^ 2 := by
          have hsq1 : ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ ^ 2 = (1 / 4 : ℝ) + t ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
          have hsq2 : ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ) + 1‖ ^ 2 = (1 / 4 : ℝ) + t ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
          have heq : ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ) + 1‖ = ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ := by
            nlinarith [norm_nonneg (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ) + 1),
              norm_nonneg (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))]
          rw [heq, ← sq, hsq1]
        have hrew : ‖Stage3ZeroFreeRegion.negLogDerivZeta (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ *
            (x / ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ) + 1‖) * x ^ (-1 / 2 : ℝ) /
            ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ =
            ‖Stage3ZeroFreeRegion.negLogDerivZeta (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ *
            (x * x ^ (-1 / 2 : ℝ)) / ((1 / 4 : ℝ) + t ^ 2) := by
          rw [← hprod_norm]; ring
        rw [hrew]
        calc ‖Stage3ZeroFreeRegion.negLogDerivZeta (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ *
              (x * x ^ (-1 / 2 : ℝ)) / ((1 / 4 : ℝ) + t ^ 2)
            ≤ (C_L * Real.log (|t| + 2)) * x / ((1 / 4 : ℝ) + t ^ 2) :=
              div_le_div_of_nonneg_right
                (mul_le_mul (hleft_bd t) hx_le (by positivity)
                  (mul_nonneg hCL_pos.le (Real.log_nonneg (by linarith [abs_nonneg t])))) (by positivity)
          _ = (C_L * x) * (Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2)) := by ring
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-(T' k))..(T' k), _‖
          ≤ 1 * ∫ t in (-(T' k))..(T' k), ‖_‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
        _ ≤ ∫ t in (-(T' k))..(T' k), (C_L * x) * (Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2)) := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hcont_L.intervalIntegrable.norm
              ((hker_cont.intervalIntegrable _ _).const_mul _) hpt
        _ = (C_L * x) * ∫ t in (-(T' k))..(T' k), Real.log (|t| + 2) / ((1 / 4 : ℝ) + t ^ 2) :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (C_L * x) * 40 := mul_le_mul_of_nonneg_left hker_int (by positivity)
        _ = 40 * C_L * x := by ring
    -- Bound top & bottom horizontal integrals by `3 * C_h * x^3 * (log(k+4))² / (k+4)²`
    have hHoriz_bd : ∀ (sg : Bool),
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
          (∫ σ in (-1 / 2 : ℝ)..(2 : ℝ),
            L1 ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) *
            (x : ℂ) ^ ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) /
            ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))))‖ ≤
          3 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by
      intro sg
      have harg_eq : ∀ σ : ℝ,
          (σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)) =
          if sg then (σ : ℂ) + I * (T' k : ℂ) else (σ : ℂ) - I * (T' k : ℂ) := by
        intro σ; cases sg <;> simp [sub_eq_add_neg]
      have hcont_H : ContinuousOn (fun σ : ℝ =>
          L1 ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) *
            (x : ℂ) ^ ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) /
            ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)))) (Set.uIcc (-1 / 2) 2) := by
        rw [Set.uIcc_of_le (by norm_num)]
        have h1 : ContinuousOn (fun σ : ℝ => L1 ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))))
            (Set.Icc (-1 / 2) 2) :=
          hL1_cont_edge.comp (by fun_prop) fun σ hσ => by
            rw [harg_eq σ]; cases sg
            · refine ⟨⟨by simpa using hσ, by simp [hTk_pos.le]⟩, fun hmem => ?_⟩
              have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.2.1; simp at this
            · refine ⟨⟨by simpa using hσ, by simp [hTk_pos.le]⟩, fun hmem => ?_⟩
              have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.2.2; simp at this
        refine (h1.mul (hpow_cont.comp (by fun_prop)).continuousOn).div (by fun_prop) fun σ _ h0 => ?_
        rw [harg_eq σ] at h0; cases sg <;> { have := congrArg Complex.im h0; simp at this; linarith }
      have hpt : ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2,
          ‖L1 ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) *
            (x : ℂ) ^ ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) /
            ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)))‖ ≤
            C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by
        intro σ hσ
        rw [harg_eq σ]
        have hσ1 : -1 ≤ σ := by linarith [hσ.1]
        have hxσ : x * x ^ σ ≤ x ^ (3 : ℝ) := by
          have h1 : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hσ.2
          calc x * x ^ σ ≤ x * x ^ (2 : ℝ) := mul_le_mul_of_nonneg_left h1 hx0.le
            _ = x ^ (1 : ℝ) * x ^ (2 : ℝ) := by rw [Real.rpow_one]
            _ = x ^ (3 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
        cases sg
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have h1 := hL1_eq ((σ : ℂ) - I * (T' k : ℂ)) ⟨by simpa using hσ, by simp [hTk_pos.le]⟩ fun hmem => by
            have := (hJ_open _ hmem).1.2.1; simp at this
          rw [h1]; dsimp only [W1]
          rw [norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : ((σ : ℂ) - I * (T' k : ℂ)).re = σ := by simp
          rw [hre]
          have hd1 : (k : ℝ) + 4 ≤ ‖(σ : ℂ) - I * (T' k : ℂ)‖ :=
            hTk_ge.trans (by simpa [abs_of_pos hTk_pos] using Complex.abs_im_le_norm ((σ : ℂ) - I * (T' k : ℂ)))
          have hd2 : (k : ℝ) + 4 ≤ ‖(σ : ℂ) - I * (T' k : ℂ) + 1‖ :=
            hTk_ge.trans (by simpa [abs_of_pos hTk_pos] using Complex.abs_im_le_norm ((σ : ℂ) - I * (T' k : ℂ) + 1))
          have hprod : ((k : ℝ) + 4) ^ 2 ≤ ‖(σ : ℂ) - I * (T' k : ℂ) + 1‖ * ‖(σ : ℂ) - I * (T' k : ℂ)‖ := by
            rw [sq]; exact mul_le_mul hd2 hd1 (by linarith) (norm_nonneg _)
          have hrew : ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' k : ℂ))‖ *
              (x / ‖(σ : ℂ) - I * (T' k : ℂ) + 1‖) * x ^ σ / ‖(σ : ℂ) - I * (T' k : ℂ)‖ =
              ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' k : ℂ))‖ * (x * x ^ σ) /
              (‖(σ : ℂ) - I * (T' k : ℂ) + 1‖ * ‖(σ : ℂ) - I * (T' k : ℂ)‖) := by ring
          rw [hrew]
          calc _ ≤ (C_h * (Real.log ((k : ℝ) + 4)) ^ 2) * x ^ (3 : ℝ) / ((k : ℝ) + 4) ^ 2 :=
                div_le_div₀ (by positivity)
                  (mul_le_mul (hT'_bd k σ hσ1 hσ.2).2 hxσ (by positivity) (by positivity))
                  (by positivity) hprod
            _ = C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by ring
        · simp only [↓reduceIte]
          have h1 := hL1_eq ((σ : ℂ) + I * (T' k : ℂ)) ⟨by simpa using hσ, by simp [hTk_pos.le]⟩ fun hmem => by
            have := (hJ_open _ hmem).1.2.2; simp at this
          rw [h1]; dsimp only [W1]
          rw [norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : ((σ : ℂ) + I * (T' k : ℂ)).re = σ := by simp
          rw [hre]
          have hd1 : (k : ℝ) + 4 ≤ ‖(σ : ℂ) + I * (T' k : ℂ)‖ :=
            hTk_ge.trans (by simpa [abs_of_pos hTk_pos] using Complex.abs_im_le_norm ((σ : ℂ) + I * (T' k : ℂ)))
          have hd2 : (k : ℝ) + 4 ≤ ‖(σ : ℂ) + I * (T' k : ℂ) + 1‖ :=
            hTk_ge.trans (by simpa [abs_of_pos hTk_pos] using Complex.abs_im_le_norm ((σ : ℂ) + I * (T' k : ℂ) + 1))
          have hprod : ((k : ℝ) + 4) ^ 2 ≤ ‖(σ : ℂ) + I * (T' k : ℂ) + 1‖ * ‖(σ : ℂ) + I * (T' k : ℂ)‖ := by
            rw [sq]; exact mul_le_mul hd2 hd1 (by linarith) (norm_nonneg _)
          have hrew : ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' k : ℂ))‖ *
              (x / ‖(σ : ℂ) + I * (T' k : ℂ) + 1‖) * x ^ σ / ‖(σ : ℂ) + I * (T' k : ℂ)‖ =
              ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' k : ℂ))‖ * (x * x ^ σ) /
              (‖(σ : ℂ) + I * (T' k : ℂ) + 1‖ * ‖(σ : ℂ) + I * (T' k : ℂ)‖) := by ring
          rw [hrew]
          calc _ ≤ (C_h * (Real.log ((k : ℝ) + 4)) ^ 2) * x ^ (3 : ℝ) / ((k : ℝ) + 4) ^ 2 :=
                div_le_div₀ (by positivity)
                  (mul_le_mul (hT'_bd k σ hσ1 hσ.2).1 hxσ (by positivity) (by positivity))
                  (by positivity) hprod
            _ = C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by ring
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      calc (2 * Real.pi)⁻¹ * ‖∫ σ in (-1 / 2 : ℝ)..(2 : ℝ), _‖
          ≤ 1 * ∫ σ in (-1 / 2 : ℝ)..(2 : ℝ), ‖_‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) (norm_nonneg _) zero_le_one
        _ ≤ ∫ _σ in (-1 / 2 : ℝ)..(2 : ℝ), (C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by norm_num) hcont_H.intervalIntegrable.norm
              intervalIntegrable_const hpt
        _ = (5 / 2 : ℝ) * (C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
        _ ≤ 3 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by
            have hnn : 0 ≤ C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by positivity
            have heq : 3 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 =
                3 * (C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) := by ring
            linarith
    have htop_bd := hHoriz_bd true
    have hbot_bd := hHoriz_bd false
    simp only [↓reduceIte, one_mul, Bool.false_eq_true, neg_mul, ← sub_eq_add_neg] at htop_bd hbot_bd
    set A1 : ℂ := (Stage6EffectivePNT.psi1 x : ℂ) -
      Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x 2 (T' k)
    set A2 : ℂ := Stage3ZeroFreeRegion.negLogDerivZeta 0 * (x : ℂ)
    set A3 : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-(T' k))..(T' k), L1 (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) *
      (x : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) / (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))
    set A4 : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-1 / 2 : ℝ)..(2 : ℝ), L1 ((σ : ℂ) + I * (T' k : ℂ)) *
      (x : ℂ) ^ ((σ : ℂ) + I * (T' k : ℂ)) / ((σ : ℂ) + I * (T' k : ℂ)))
    set A5 : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-1 / 2 : ℝ)..(2 : ℝ), L1 ((σ : ℂ) - I * (T' k : ℂ)) *
      (x : ℂ) ^ ((σ : ℂ) - I * (T' k : ℂ)) / ((σ : ℂ) - I * (T' k : ℂ)))
    have hsplit : (Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑ n ∈ Fset k, term n) =
        A1 + A2 + A3 + A4 - A5 := by
      dsimp only [A1, A2, A3, A4, A5]
      linear_combination hshift
    rw [hsplit]
    have h1 := norm_sub_le (A1 + A2 + A3 + A4) A5
    have h2 := norm_add_le (A1 + A2 + A3) A4
    have h3 := norm_add_le (A1 + A2) A3
    have h4 := norm_add_le A1 A2
    have hK0x : ‖A2‖ = K₀ * x := by
      dsimp only [A2]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hsum45 : 3 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 +
        3 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 =
        6 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2 := by ring
    dsimp only [B_const, err]
    linarith
  -- Step 2: Pass to the limit `k → ∞` (`∑ n ∈ Fset k, term n → ∑' n, term n` and `err k → 0`)!
  have hF_cofinal : Tendsto Fset atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    by_cases hs : s = ∅
    · subst hs; exact ⟨0, fun _ _ => Finset.empty_subset _⟩
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      set M_s : ℝ := s.sup' hne fun n => |(xiZeroSeq n).im|
      refine ⟨Nat.ceil M_s, fun k hk n hn => ?_⟩
      have h1 : |(xiZeroSeq n).im| ≤ M_s := Finset.le_sup' (fun m => |(xiZeroSeq m).im|) hn
      have h2 : M_s ≤ (k : ℝ) := (Nat.le_ceil M_s).trans (by exact_mod_cast hk)
      exact (finite_xiZeroSeq_abs_im_le (T' k)).mem_toFinset.mpr
        (by change |(xiZeroSeq n).im| ≤ T' k; linarith [(hT'_mem k).1])
  have hsum_tend : Tendsto (fun k : ℕ => ∑ n ∈ Fset k, term n) atTop (𝓝 (∑' n : ℕ, term n)) :=
    hterm_summ.hasSum.comp hF_cofinal
  have herr_tend : Tendsto err atTop (𝓝 0) := by
    have hk_top : Tendsto (fun k : ℕ => (k : ℝ) + 4) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h1 : Tendsto (fun k : ℕ => (12 / Real.pi) * x ^ (3 : ℝ) / ((k : ℝ) + 4)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hk_top
    have h2 : Tendsto (fun k : ℕ =>
        6 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) atTop (𝓝 0) := by
      have hdom : Tendsto (fun k : ℕ => 24 * C_h * x ^ (3 : ℝ) / ((k : ℝ) + 4)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hk_top
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) hdom
      have hu : (4 : ℝ) ≤ (k : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hlog_sq : (Real.log ((k : ℝ) + 4)) ^ 2 ≤ 4 * ((k : ℝ) + 4) := by
        have hsqrt : 0 < Real.sqrt ((k : ℝ) + 4) := Real.sqrt_pos.mpr (by linarith)
        have hl : Real.log ((k : ℝ) + 4) ≤ 2 * Real.sqrt ((k : ℝ) + 4) := by
          have := Real.log_sqrt (by linarith : (0 : ℝ) ≤ (k : ℝ) + 4)
          linarith [Real.log_le_sub_one_of_pos hsqrt]
        have hnn : 0 ≤ Real.log ((k : ℝ) + 4) := Real.log_nonneg (by linarith)
        calc (Real.log ((k : ℝ) + 4)) ^ 2 ≤ (2 * Real.sqrt ((k : ℝ) + 4)) ^ 2 :=
              pow_le_pow_left₀ hnn hl 2
          _ = 4 * (Real.sqrt ((k : ℝ) + 4)) ^ 2 := by ring
          _ = 4 * ((k : ℝ) + 4) := by rw [Real.sq_sqrt (by linarith)]
      have hpos : (0 : ℝ) < (k : ℝ) + 4 := by linarith
      calc 6 * C_h * x ^ (3 : ℝ) * (Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2
          ≤ 6 * C_h * x ^ (3 : ℝ) * (4 * ((k : ℝ) + 4)) / ((k : ℝ) + 4) ^ 2 := by gcongr
        _ = 24 * C_h * x ^ (3 : ℝ) / ((k : ℝ) + 4) := by field_simp [hpos.ne']; ring
    simpa [err] using h1.add h2
  have hlhs_tend : Tendsto
      (fun k : ℕ => ‖(Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑ n ∈ Fset k, term n)‖)
      atTop (𝓝 ‖(Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑' n : ℕ, term n)‖) :=
    ((tendsto_const_nhds.sub (tendsto_const_nhds.sub hsum_tend))).norm
  have hrhs_tend : Tendsto (fun k : ℕ => B_const * x + err k) atTop (𝓝 (B_const * x)) := by
    simpa using tendsto_const_nhds.add herr_tend
  have hlim_bd : ‖(Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑' n : ℕ, term n)‖ ≤ B_const * x :=
    le_of_tendsto_of_tendsto hlhs_tend hrhs_tend (Eventually.of_forall hbound_k)
  have hre_eq : Stage6EffectivePNT.psi1 x - (x ^ 2 / 2 - (∑' n : ℕ, term n).re) =
      ((Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑' n : ℕ, term n)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re, sq, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [hre_eq]
  have hre_le := Complex.abs_re_le_norm ((Stage6EffectivePNT.psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2 - ∑' n : ℕ, term n))
  have hlogx_half : (1 / 2 : ℝ) ≤ Real.log x := by rw [← hc_def]; exact hlogx_ge
  have hBx : 0 ≤ B_const * x := by positivity
  have hmul : B_const * x ≤ 2 * (B_const * x) * Real.log x := by nlinarith
  dsimp only [C]
  linarith [show 2 * (B_const * x) * Real.log x = 2 * B_const * x * Real.log x by ring]

/-! ## Section 5: Von Koch's 1901 Sharp Riemann Hypothesis Theorems (`RH → O(√x (log x)²)`) -/

/-- **Unconditional Reciprocal-Zero Sum Bound**:
`∃ C > 0, ∀ T ≥ 2, ∑ ρ ∈ zetaZerosInBox T, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ ≤ C * (Real.log T) ^ 2`. -/
theorem sum_inv_norm_zetaZerosInBox_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∑ ρ ∈ zetaZerosInBox T, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ ≤ C * (Real.log T) ^ 2 := by
  classical
  obtain ⟨C_N, hCN_pos, hshort⟩ := xiZeroCount_short_interval_le
  set M₂ : ℝ := ∑ ρ ∈ zetaZerosInBox 2, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖
  have hM₂_nn : 0 ≤ M₂ := Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  set C : ℝ := 4 * M₂ + 16 * C_N
  refine ⟨C, by positivity, fun T hT => ?_⟩
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT : (1 / 2 : ℝ) ≤ Real.log T := hlog2.trans (Real.log_le_log (by norm_num) hT)
  have hsub2 : zetaZerosInBox 2 ⊆ zetaZerosInBox T := fun ρ hρ => by
    have hm := (finite_riemannZeta_zeros_le_height 2).mem_toFinset.mp hρ
    exact (finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.trans hT⟩
  rw [← Finset.sum_sdiff hsub2]
  set D : Finset ℂ := zetaZerosInBox T \ zetaZerosInBox 2
  -- Cover `D` by unit-height bands `k ≤ |ρ.im| < k + 1` for `k ∈ Finset.Icc 2 ⌊T⌋₊`
  set N : ℕ := ⌊T⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hT)
  have hN_le : (N : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hD_le_sum : ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ ≤
      ∑ k ∈ Finset.Icc 2 N,
        (2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
          Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ))) / (k : ℝ) := by
    let band : ℕ → Finset ℂ := fun k => D.filter fun ρ => (k : ℝ) ≤ |ρ.im| ∧ |ρ.im| < (k : ℝ) + 1
    have hD_cover : D ⊆ (Finset.Icc 2 N).biUnion band := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hm := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ.1
      have hgt2 : 2 < |ρ.im| := by
        by_contra hle
        exact hρ.2 ((finite_riemannZeta_zeros_le_height 2).mem_toFinset.mpr ⟨hm.1, hm.2.1, hm.2.2.1, not_lt.mp hle⟩)
      set k : ℕ := ⌊|ρ.im|⌋₊
      have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hgt2.le)
      have hkN : k ≤ N := Nat.floor_mono hm.2.2.2
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk2, hkN⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr hρ, Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩⟩
    have hband_bd : ∀ k ∈ Finset.Icc 2 N,
        ∑ ρ ∈ band k, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ ≤
          (2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
            Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ))) / (k : ℝ) := by
      intro k hk
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
      have hfin_k : {n : ℕ | (k : ℝ) ≤ |(xiZeroSeq n).im| ∧ |(xiZeroSeq n).im| < (k : ℝ) + 1}.Finite :=
        (finite_xiZeroSeq_abs_im_le ((k : ℝ) + 1)).subset fun _ hn => hn.2.le
      set F_k : Finset ℕ := hfin_k.toFinset
      have hFk_card : (F_k.card : ℝ) =
          2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
            Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ)) :=
        card_xiZeroSeq_abs_im_Ico_eq hk0 (by linarith) F_k fun _ => hfin_k.mem_toFinset
      have hsum_ord : ∑ ρ ∈ band k, (analyticOrderNatAt xi ρ : ℝ) ≤ (F_k.card : ℝ) := by
        have hnat : ∑ ρ ∈ band k, analyticOrderNatAt xi ρ ≤ F_k.card := by
          have hmaps : ∀ ρ ∈ band k, ∀ n, xiZeroSeq n = ρ → n ∈ F_k := fun ρ hρ n hn => by
            have hb := (Finset.mem_filter.mp hρ).2
            exact hfin_k.mem_toFinset.mpr ⟨by rw [hn]; exact hb.1, by rw [hn]; exact hb.2⟩
          have hcard_eq : ∀ ρ ∈ band k, analyticOrderNatAt xi ρ = (F_k.filter fun n => xiZeroSeq n = ρ).card := by
            intro ρ hρ
            exact ((isMultiplicityZeroSeq_xi.2 ρ).2 _ fun n => by
              simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hmaps ρ hρ n h, h⟩⟩).symm
          calc ∑ ρ ∈ band k, analyticOrderNatAt xi ρ
              = ∑ ρ ∈ band k, (F_k.filter fun n => xiZeroSeq n = ρ).card := Finset.sum_congr rfl hcard_eq
            _ = ∑ ρ ∈ band k, ((F_k.filter fun n => xiZeroSeq n ∈ band k).filter fun n => xiZeroSeq n = ρ).card := by
                refine Finset.sum_congr rfl fun ρ hρ => congrArg Finset.card ?_
                ext n; simp only [Finset.mem_filter]
                exact ⟨fun h => ⟨⟨h.1, h.2.symm ▸ hρ⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
            _ = (F_k.filter fun n => xiZeroSeq n ∈ band k).card :=
                (Finset.card_eq_sum_card_fiberwise (f := xiZeroSeq)
                  (s := F_k.filter fun n => xiZeroSeq n ∈ band k) (t := band k)
                  fun _ hn => (Finset.mem_filter.mp hn).2).symm
            _ ≤ F_k.card := Finset.card_filter_le _ _
        exact_mod_cast hnat
      calc ∑ ρ ∈ band k, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖
          ≤ ∑ ρ ∈ band k, (analyticOrderNatAt xi ρ : ℝ) / (k : ℝ) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            have hb := (Finset.mem_filter.mp hρ).2
            have hden : (k : ℝ) ≤ ‖ρ‖ := hb.1.trans (Complex.abs_im_le_norm ρ)
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk0 hden
        _ = (∑ ρ ∈ band k, (analyticOrderNatAt xi ρ : ℝ)) / (k : ℝ) := (Finset.sum_div _ _ _).symm
        _ ≤ (F_k.card : ℝ) / (k : ℝ) := div_le_div_of_nonneg_right hsum_ord hk0.le
        _ = (2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
              Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ))) / (k : ℝ) := by rw [hFk_card]
    have hband_disj : Set.PairwiseDisjoint (↑(Finset.Icc 2 N) : Set ℕ) band := by
      intro k₁ _ k₂ _ hne
      change Disjoint (band k₁) (band k₂)
      rw [Finset.disjoint_left]
      intro ρ h1 h2
      have hb1 := (Finset.mem_filter.mp h1).2
      have hb2 := (Finset.mem_filter.mp h2).2
      have hk1 : (k₁ : ℝ) < (k₂ : ℝ) + 1 := by linarith
      have hk2 : (k₂ : ℝ) < (k₁ : ℝ) + 1 := by linarith
      have h1' : k₁ < k₂ + 1 := by exact_mod_cast hk1
      have h2' : k₂ < k₁ + 1 := by exact_mod_cast hk2
      omega
    calc ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ (Finset.Icc 2 N).biUnion band, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hD_cover fun _ _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      _ = ∑ k ∈ Finset.Icc 2 N, ∑ ρ ∈ band k, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ :=
          Finset.sum_biUnion hband_disj
      _ ≤ ∑ k ∈ Finset.Icc 2 N,
            (2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
              Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ))) / (k : ℝ) := Finset.sum_le_sum hband_bd
  -- Harmonic bound: `∑_{k=2}^N 1/k ≤ Real.log N ≤ Real.log T`
  have hharm : ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ≤ Real.log T := by
    have haux : ∀ m : ℕ, 2 ≤ m → ∑ k ∈ Finset.Icc 2 m, (1 : ℝ) / (k : ℝ) ≤ Real.log (m : ℝ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        have hIcc : Finset.Icc 2 2 = {2} := by decide
        rw [hIcc, Finset.sum_singleton]; norm_num; linarith [Real.log_two_gt_d9]
      | succ j hj ih =>
        have hIcc : Finset.Icc 2 (j + 1) = insert (j + 1) (Finset.Icc 2 j) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
        have hstep : (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ≤ Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) := by
          push_cast
          have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
          rw [← Real.log_div hj1.ne' hj0.ne']
          have h1 := Real.log_le_sub_one_of_pos (div_pos hj0 hj1)
          have hneg : Real.log ((j : ℝ) / ((j : ℝ) + 1)) = -Real.log (((j : ℝ) + 1) / (j : ℝ)) := by
            rw [Real.log_div hj0.ne' hj1.ne', Real.log_div hj1.ne' hj0.ne']; ring
          have hsub : 1 - (j : ℝ) / ((j : ℝ) + 1) = 1 / ((j : ℝ) + 1) := by field_simp [hj1.ne']; ring
          linarith
        linarith
    exact (haux N hN2).trans (Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hN_le)
  have hD_bd : ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ ≤ 4 * C_N * (Real.log T) ^ 2 := by
    have hlogT1 : Real.log (T + 1) ≤ 2 * Real.log T := by
      have hsq : T + 1 ≤ T ^ 2 := by nlinarith
      calc Real.log (T + 1) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hsq
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    calc ∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖
        ≤ ∑ k ∈ Finset.Icc 2 N,
            (2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
              Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ))) / (k : ℝ) := hD_le_sum
      _ ≤ ∑ k ∈ Finset.Icc 2 N, (4 * C_N * Real.log T) * ((1 : ℝ) / (k : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
          have hkN : (k : ℝ) ≤ T := (by exact_mod_cast (Finset.mem_Icc.mp hk).2 : (k : ℝ) ≤ (N : ℝ)).trans hN_le
          have hsh := hshort (k : ℝ) ((k : ℝ) + 1) hk2 (by linarith) (by linarith)
          have hlk : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log T :=
            (Real.log_le_log (by linarith) (by linarith)).trans hlogT1
          have hnum : 2 * (Stage7VonMangoldtExplicit.xiZeroCount ((k : ℝ) + 1) -
              Stage7VonMangoldtExplicit.xiZeroCount (k : ℝ)) ≤ 4 * C_N * Real.log T := by nlinarith
          have h1 := div_le_div_of_nonneg_right hnum (by linarith : (0 : ℝ) ≤ (k : ℝ))
          linarith [show (4 * C_N * Real.log T) * (1 / (k : ℝ)) = 4 * C_N * Real.log T / (k : ℝ) by ring]
      _ = (4 * C_N * Real.log T) * ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (4 * C_N * Real.log T) * Real.log T := mul_le_mul_of_nonneg_left hharm (by positivity)
      _ = 4 * C_N * (Real.log T) ^ 2 := by ring
  change (∑ ρ ∈ D, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖) + M₂ ≤ C * (Real.log T) ^ 2
  have hlog_sq : (1 / 4 : ℝ) ≤ (Real.log T) ^ 2 := by nlinarith
  dsimp only [C]
  nlinarith

/-- **VON KOCH'S 1901 SHARP RIEMANN HYPOTHESIS THEOREM FOR `Chebyshev.psi`**:
`RiemannHypothesis → ∃ C > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2`! -/
theorem von_koch_psi_of_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨C₁, hC₁_pos, hexp⟩ := von_mangoldt_explicit_formula_psi
  obtain ⟨C₂, hC₂_pos, hsum⟩ := sum_inv_norm_zetaZerosInBox_le
  have hRH_xi := Stage5StirlingPhragmen.riemannHypothesis_iff_xi_zeros_on_half_line.mp hRH
  set C : ℝ := max (2 * C₁ + C₂) 450
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : (1 / 2 : ℝ) ≤ Real.log x := hlog2.trans (Real.log_le_log (by norm_num) hx2)
  by_cases hx16 : 16 ≤ x
  · set T : ℝ := Real.sqrt x
    have hT4 : 4 ≤ T := Real.le_sqrt_of_sq_le (by linarith : (4 : ℝ) ^ 2 ≤ x)
    have hTx : T ≤ x := by
      have : x ≤ x ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
    have hT_pos : 0 < T := by linarith
    have hlogx_gt1 : 1 < Real.log x := by
      have h4 : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
    have h1 := hexp x (by linarith) T hT4 hTx
    -- Under RH, every `ρ ∈ zetaZerosInBox T` has `ρ.re = 1/2`, so `‖x^ρ / ρ‖ = √x / ‖ρ‖`!
    have hzero_bd : |(psiZeroSum x T).re| ≤ C₂ * Real.sqrt x * (Real.log x) ^ 2 := by
      have hre_le := Complex.abs_re_le_norm (psiZeroSum x T)
      have hnorm_le : ‖psiZeroSum x T‖ ≤ Real.sqrt x *
          ∑ ρ ∈ zetaZerosInBox T, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ := by
        unfold psiZeroSum
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
        have hm := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
        have hxi0 : xi ρ = 0 := (xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨hm.1, hm.2.1, hm.2.2.1⟩
        have hre_half : ρ.re = 1 / 2 := hRH_xi ρ hxi0
        rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
          hre_half, ← Real.sqrt_eq_rpow]
        ring_nf; rfl
      have hs := hsum T (by linarith)
      have hlogT_le : Real.log T ≤ Real.log x := Real.log_le_log hT_pos hTx
      have hlogT_sq : (Real.log T) ^ 2 ≤ (Real.log x) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogT_le 2
      calc |(psiZeroSum x T).re| ≤ ‖psiZeroSum x T‖ := hre_le
        _ ≤ Real.sqrt x * ∑ ρ ∈ zetaZerosInBox T, (analyticOrderNatAt xi ρ : ℝ) / ‖ρ‖ := hnorm_le
        _ ≤ Real.sqrt x * (C₂ * (Real.log T) ^ 2) := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg x)
        _ ≤ Real.sqrt x * (C₂ * (Real.log x) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogT_sq hC₂_pos.le) (Real.sqrt_nonneg x)
        _ = C₂ * Real.sqrt x * (Real.log x) ^ 2 := by ring
    have hx_div_T : x / T = Real.sqrt x := by
      dsimp only [T]; rw [div_eq_iff hT_pos.ne', Real.mul_self_sqrt hx0.le]
    have hrem : x * (Real.log x) ^ 2 / T + Real.log x ≤ 2 * Real.sqrt x * (Real.log x) ^ 2 := by
      have hrew : x * (Real.log x) ^ 2 / T = Real.sqrt x * (Real.log x) ^ 2 := by
        rw [mul_div_right_comm, hx_div_T]
      rw [hrew]
      have h1_le : (1 : ℝ) ≤ Real.sqrt x := by linarith
      nlinarith
    have htri : |Chebyshev.psi x - x| ≤
        |Chebyshev.psi x - (x - (psiZeroSum x T).re)| + |(psiZeroSum x T).re| := by
      have h := abs_sub_le (Chebyshev.psi x) (x - (psiZeroSum x T).re) x
      simpa [sub_sub_cancel_left, abs_neg] using h
    have hC_ge : 2 * C₁ + C₂ ≤ C := le_max_left _ _
    have hnn : 0 ≤ Real.sqrt x * (Real.log x) ^ 2 := by positivity
    nlinarith
  · push Not at hx16
    have hpsi_le : Chebyshev.psi x ≤ 6 * x := by
      rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      exact Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith)
    have hpsi_nn : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
    have habs : |Chebyshev.psi x - x| ≤ 112 := by rw [abs_le]; constructor <;> linarith
    have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith : (1 : ℝ) ^ 2 ≤ x)
    have hsq_ge : (1 / 4 : ℝ) ≤ (Real.log x) ^ 2 := by nlinarith
    have hmul : (1 / 4 : ℝ) ≤ Real.sqrt x * (Real.log x) ^ 2 := by nlinarith
    have h450 : 450 ≤ C := le_max_right _ _
    nlinarith

/-- **VON KOCH'S 1901 SHARP RIEMANN HYPOTHESIS THEOREM FOR `Chebyshev.theta`**:
`RiemannHypothesis → ∃ C > 0, ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2`! -/
theorem von_koch_theta_of_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.theta x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨C₁, hC₁_pos, hpsi⟩ := von_koch_psi_of_RH hRH
  refine ⟨C₁ + 4, by positivity, fun x hx2 => ?_⟩
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : (1 / 2 : ℝ) ≤ Real.log x := hlog2.trans (Real.log_le_log (by norm_num) hx2)
  have hdiff : |Chebyshev.theta x - Chebyshev.psi x| ≤ 2 * Real.sqrt x * Real.log x := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
    exact Chebyshev.psi_sub_theta_le (by linarith)
  have htri : |Chebyshev.theta x - x| ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - x| := by
    simpa [sub_add_sub_cancel] using abs_add_le (Chebyshev.theta x - Chebyshev.psi x) (Chebyshev.psi x - x)
  have h1 := hpsi x hx2
  have hlog_sq : Real.log x ≤ 2 * (Real.log x) ^ 2 := by nlinarith
  have h2 : 2 * Real.sqrt x * Real.log x ≤ 4 * Real.sqrt x * (Real.log x) ^ 2 := by
    nlinarith [Real.sqrt_nonneg x]
  linarith

/-- **VON KOCH'S 1901 SHARP RIEMANN HYPOTHESIS THEOREM FOR `π(x) - li(x)`**:
`RiemannHypothesis → ∃ C > 0, ∀ x ≥ 3, |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤ C * Real.sqrt x * Real.log x`! -/
theorem von_koch_pi_sub_li_of_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x := by
  obtain ⟨C₁, hC₁_pos, hth⟩ := von_koch_theta_of_RH hRH
  set C : ℝ := 3 * C₁ + 4
  refine ⟨C, by positivity, fun x hx3 => ?_⟩
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_gt1 : 1 < Real.log 3 := by
    have h3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h3)
  have hlogx_gt1 : 1 < Real.log x := hlog3_gt1.trans_le (Real.log_le_log (by norm_num) hx3)
  have hlogx_pos : 0 < Real.log x := zero_lt_one.trans hlogx_gt1
  -- Integration by parts: `∫_2^x (1 / log t) dt = x / log x - 2 / log 2 + ∫_2^x (1 / (log t)²) dt`
  have hcont1 : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx2]
    exact continuousOn_const.div (Real.continuousOn_log.mono fun t ht => (by linarith [ht.1] : t ≠ 0))
      fun t ht => (Real.log_pos (by linarith [ht.1])).ne'
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ 2) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx2]
    exact continuousOn_const.div ((Real.continuousOn_log.mono fun t ht => (by linarith [ht.1] : t ≠ 0)).pow 2)
      fun t ht => pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hli_ibp : ∫ t in (2 : ℝ)..x, 1 / Real.log t =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
    have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun u : ℝ => u / Real.log u) (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hx2] at ht
      have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
      have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      refine ((hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hlt0).congr_deriv ?_
      simp only [id_eq]
      field_simp [ht0, hlt0]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont1.intervalIntegrable.sub hcont2.intervalIntegrable)
    rw [intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable] at hftc
    linarith
  -- Integrability of `θ(t) / (t (log t)²)` on `[2, x]`
  have hint_th : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * (Real.log t) ^ 2)) volume 2 x := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx2).mpr ?_
    refine Integrable.mono' (integrableOn_const (C := 6 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable Chebyshev.theta := by
        have h : Chebyshev.theta =
            (fun k : ℕ => ∑ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, Real.log (p : ℝ)) ∘ Nat.floor := rfl
        rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact (hm.div (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : 0 < t := by linarith
      have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hth_le : Chebyshev.theta t ≤ 6 * t := by
        have h1 := Chebyshev.theta_le_psi t
        rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi] at h1
        exact h1.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
      rw [Real.norm_of_nonneg (div_nonneg (Chebyshev.theta_nonneg t) (by positivity))]
      calc Chebyshev.theta t / (t * (Real.log t) ^ 2)
          ≤ (6 * t) / (t * (Real.log 2) ^ 2) :=
            div_le_div₀ (by positivity) hth_le (by positivity) (by gcongr)
        _ = 6 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
  -- Exact error identity via `Stage3RealAnalyticLandau.primeCounting_eq_abel_theta`
  have herr_eq : (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t =
      (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) := by
    rw [Stage3RealAnalyticLandau.primeCounting_eq_abel_theta hx2, hli_ibp]
    have hsub_int : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2)) -
        (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) =
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) := by
      rw [← intervalIntegral.integral_sub hint_th hcont2.intervalIntegrable]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx2] at ht
      have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
      have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      field_simp [ht0, hlt0]
    have hdiv : Chebyshev.theta x / Real.log x - x / Real.log x = (Chebyshev.theta x - x) / Real.log x := by
      rw [sub_div]
    linarith
  -- Bound the integral term using `|θ(t) - t| ≤ C₁ √t (log t)²`!
  have hint_bd : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤
      2 * C₁ * Real.sqrt x := by
    have hint_diff : IntervalIntegrable (fun t : ℝ => (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) volume 2 x := by
      refine (hint_th.sub hcont2.intervalIntegrable).congr fun t ht => ?_
      rw [Set.uIoc_of_le hx2] at ht
      have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
      have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      field_simp [ht0, hlt0]
    have hint_rhs : IntervalIntegrable (fun t : ℝ => C₁ * t ^ (-(1 / 2 : ℝ))) volume 2 x :=
      (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (a := 2) (b := x) (by norm_num)).const_mul C₁
    have hpt : ∀ t ∈ Set.Icc (2 : ℝ) x,
        |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ C₁ * t ^ (-(1 / 2 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hlt_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      rw [abs_div, abs_of_pos (by positivity : 0 < t * (Real.log t) ^ 2)]
      calc |Chebyshev.theta t - t| / (t * (Real.log t) ^ 2)
          ≤ (C₁ * Real.sqrt t * (Real.log t) ^ 2) / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right (hth t ht.1) (by positivity)
        _ = C₁ * (Real.sqrt t / t) := by field_simp [ht0.ne', hlt_pos.ne']
        _ = C₁ * t ^ (-(1 / 2 : ℝ)) := by
            congr 1
            calc Real.sqrt t / t = t ^ (1 / 2 : ℝ) / t ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
              _ = t ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub ht0 _ _).symm
              _ = t ^ (-(1 / 2 : ℝ)) := by congr 1; norm_num
    have hval : ∫ t in (2 : ℝ)..x, C₁ * t ^ (-(1 / 2 : ℝ)) ≤ 2 * C₁ * Real.sqrt x := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num))]
      have hexp : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
      rw [hexp, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have h2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)‖
        ≤ ∫ t in (2 : ℝ)..x, ‖(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx2
      _ ≤ ∫ t in (2 : ℝ)..x, C₁ * t ^ (-(1 / 2 : ℝ)) :=
          intervalIntegral.integral_mono_on hx2 hint_diff.norm hint_rhs fun t ht => by
            rw [Real.norm_eq_abs]; exact hpt t ht
      _ ≤ 2 * C₁ * Real.sqrt x := hval
  -- Bound `|(θ(x) - x) / log x| ≤ C₁ √x log x` and `2 / log 2 ≤ 4`
  have hmain_bd : |(Chebyshev.theta x - x) / Real.log x| ≤ C₁ * Real.sqrt x * Real.log x := by
    rw [abs_div, abs_of_pos hlogx_pos]
    calc |Chebyshev.theta x - x| / Real.log x
        ≤ (C₁ * Real.sqrt x * (Real.log x) ^ 2) / Real.log x :=
          div_le_div_of_nonneg_right (hth x hx2) hlogx_pos.le
      _ = C₁ * Real.sqrt x * Real.log x := by field_simp [hlogx_pos.ne']
  have hconst_bd : 2 / Real.log 2 ≤ 4 := by
    rw [div_le_iff₀ hlog2_pos]; linarith [Real.log_two_gt_d9]
  have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith : (1 : ℝ) ^ 2 ≤ x)
  rw [herr_eq]
  have htri1 := abs_add_le ((Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2)
    (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
  have htri2 := abs_add_le ((Chebyshev.theta x - x) / Real.log x) (2 / Real.log 2)
  rw [abs_of_pos (div_pos (by norm_num) hlog2_pos)] at htri2
  have h1 : 2 * C₁ * Real.sqrt x ≤ 2 * C₁ * Real.sqrt x * Real.log x :=
    le_mul_of_one_le_right (by positivity) hlogx_gt1.le
  have h2 : (4 : ℝ) ≤ 4 * Real.sqrt x * Real.log x := by nlinarith
  dsimp only [C]
  linarith

end RHDirect.Stage9ExplicitFormula

end
