/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Full Unconditional Micciancio–Regev (2007) Lattice Smoothing Theory

Completes the unconditional formalization of Micciancio–Regev (*Worst-case to Average-case
Reductions based on Gaussian Measures*, SICOMP 2007) on native Mathlib lattices
`Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))` with `[DiscreteTopology Λ] [IsZLattice ℝ Λ]`:

1. **Full `0 < ε ≤ 1` Dual Smoothing Bound (`eta_le_sqrt_n_add_log_div_lambda1`)**:
   Extends `LatticeSmoothingGeneral.eta_le_sqrt_scaling` (which covered `0 < ε < 1 / (2^n - 1)`)
   to all `0 < ε ≤ 1` (and all `n ≥ 1`, including `n = 1`) via positivity, right-continuity, and
   antitonicity of `eta Λ`, giving `η_ε(Λ) ≤ √(n + ln(1/ε)/π) / λ₁(Λ*)`.

2. **MR07 Lemma 3.3 (Primal `λ_n(Λ)` & Gram–Schmidt Smoothing Bounds)**:
   Using Banaszczyk's transference (`Stage12BanaszczykTransference.banaszczyk_transference_lambda1_lambdan`)
   and Gram–Schmidt orthogonalization (`Stage11LLLSiegelReduction.gramSchmidtVec`), proves explicit
   unconditional primal upper bounds for all `0 < ε ≤ 1`:
   - `eta_le_sqrt_n_add_log_mul_lambdan` : `η_ε(Λ) ≤ √(n + ln(1/ε)/π) · λ_n(Λ)`
   - `eta_le_sqrt_n_add_log_mul_max_gsNorm` : for any `ℤ`-basis `b` of `Λ`,
     `η_ε(Λ) ≤ √(n + ln(1/ε)/π) · max_i ‖b̃_i‖` (and `max_i ‖b_i‖`).

3. **MR07 Lemma 4.1 (Statistical / Total-Variation Distance `≤ ε / 2` to Uniform on `ℝ^n / Λ`)**:
   Using multidimensional Poisson summation (`rhoShift_poisson_summation`), proves that for all
   `s ≥ η_ε(Λ)` (`0 < ε < 1`), the folded continuous Gaussian density
   `foldedGaussianDensity Λ s x := (s ^ n)⁻¹ * rhoShift s Λ x` satisfies:
   - Pointwise error bound:
     `|rhoShift s Λ x - s^n / covol Λ| ≤ ε · (s^n / covol Λ)` and
     `|foldedGaussianDensity Λ s x - (covol Λ)⁻¹| ≤ ε · (covol Λ)⁻¹`;
   - L¹ / Total-Variation distance on any fundamental parallelepiped `ZSpan.fundamentalDomain` (and
     any `IsAddFundamentalDomain Λ.toAddSubgroup F volume`):
     `(1 / 2) * ∫ x in F, |foldedGaussianDensity Λ s x - (covol Λ)⁻¹| ≤ ε / 2`.
-/
import RHDirect.LatticeSmoothingGeneral
import RHDirect.Stage11LLLSiegelReduction
import RHDirect.Stage12BanaszczykTransference

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace RHDirect.LatticeSmoothingFull

open RHDirect.LatticeSmoothing RHDirect.LatticeSmoothingGeneral
  RHDirect.Stage12BanaszczykTransference RHDirect.Stage10GeometryOfNumbers
  RHDirect.Stage11LLLSiegelReduction
open MeasureTheory Filter Module
open scoped BigOperators Real

variable {n : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))}

/-! ## Section 1: Nonemptiness, Positivity, Right-Continuity, and Antitonicity of `η_ε(Λ)` -/

/-- For every `ε > 0` and full-rank lattice `Λ` (`n ≥ 1`), the smoothing set
`{s > 0 | ρ_{1/s}(Λ* \ {0}) ≤ ε}` is nonempty. -/
theorem eta_set_nonempty (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) :
    {s : ℝ | 0 < s ∧ rhoPunct Λ s ≤ ε}.Nonempty := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  set L := shortestNorm (dualLattice Λ)
  have hL : 0 < L := shortestNorm_pos hn (dualLattice Λ)
  have h2n : (1 : ℝ) < (2 : ℝ) ^ n := by
    simpa using pow_lt_pow_left₀ (show (1 : ℝ) < 2 by norm_num) zero_le_one
      (Nat.pos_iff_ne_zero.mp hn)
  have hden : 0 < (2 : ℝ) ^ n - 1 := by linarith
  set s₀ := (Real.sqrt (n : ℝ) + 1) / L
  have hs₀ : 0 < s₀ := by positivity
  have hs₀_gt : Real.sqrt (n : ℝ) / s₀ < L := by
    have hnum : Real.sqrt (n : ℝ) < Real.sqrt (n : ℝ) + 1 := by linarith
    have heq : Real.sqrt (n : ℝ) / s₀ = Real.sqrt (n : ℝ) * L / (Real.sqrt (n : ℝ) + 1) := by
      dsimp [s₀]; field_simp [hL.ne']
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hnum hL]
  have hcore : rhoPunct Λ s₀ ≤ 1 / ((2 : ℝ) ^ n - 1) :=
    rhoPunct_le_of_sqrt_n_div_lt hn hs₀ hs₀_gt
  set a := max 0 (Real.log (1 / (ε * ((2 : ℝ) ^ n - 1))))
  have ha_nn : 0 ≤ a := le_max_left _ _
  set s := Real.sqrt (s₀ ^ 2 + a / (Real.pi * L ^ 2))
  have hs₀_sq : s₀ ^ 2 ≤ s ^ 2 := by
    have harg : 0 ≤ s₀ ^ 2 + a / (Real.pi * L ^ 2) := by positivity
    dsimp [s]
    rw [Real.sq_sqrt harg]
    have : 0 ≤ a / (Real.pi * L ^ 2) := by positivity
    linarith
  have hs₀_le_s : s₀ ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 2 < s₀ ^ 2 := pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) (by norm_num)
    linarith
  have hs : 0 < s := lt_of_lt_of_le hs₀ hs₀_le_s
  refine ⟨s, hs, ?_⟩
  have hscale := rhoPunct_scale_le (Λ := Λ) hs₀ hs₀_le_s
  have hdiff : Real.pi * (s ^ 2 - s₀ ^ 2) * L ^ 2 = a := by
    have harg : 0 ≤ s₀ ^ 2 + a / (Real.pi * L ^ 2) := by positivity
    have hssq : s ^ 2 = s₀ ^ 2 + a / (Real.pi * L ^ 2) := by dsimp [s]; rw [Real.sq_sqrt harg]
    rw [hssq]
    field_simp [Real.pi_ne_zero, hL.ne']
    ring
  have hexp : Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * L ^ 2) ≤ ε * ((2 : ℝ) ^ n - 1) := by
    have hneg : -Real.pi * (s ^ 2 - s₀ ^ 2) * L ^ 2 = -a := by
      rw [show -Real.pi * (s ^ 2 - s₀ ^ 2) * L ^ 2 = -(Real.pi * (s ^ 2 - s₀ ^ 2) * L ^ 2) by ring,
        hdiff]
    rw [hneg]
    have ha_ge : Real.log (1 / (ε * ((2 : ℝ) ^ n - 1))) ≤ a := le_max_right _ _
    have hle_exp : Real.exp (-a) ≤ Real.exp (-Real.log (1 / (ε * ((2 : ℝ) ^ n - 1)))) :=
      Real.exp_le_exp.mpr (neg_le_neg ha_ge)
    have hrhs : Real.exp (-Real.log (1 / (ε * ((2 : ℝ) ^ n - 1)))) = ε * ((2 : ℝ) ^ n - 1) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    linarith
  calc rhoPunct Λ s
      ≤ Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * L ^ 2) * rhoPunct Λ s₀ := hscale
    _ ≤ (ε * ((2 : ℝ) ^ n - 1)) * (1 / ((2 : ℝ) ^ n - 1)) := by
        exact mul_le_mul hexp hcore rhoPunct_nonneg (by positivity)
    _ = ε := by field_simp [hden.ne']

/-- **Antitonicity of `η_ε(Λ)`**: for `0 < ε₁ ≤ ε₂`, `η_{ε₂}(Λ) ≤ η_{ε₁}(Λ)`. -/
theorem eta_antitone (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hle : ε₁ ≤ ε₂) :
    eta Λ ε₂ ≤ eta Λ ε₁ := by
  unfold eta
  refine csInf_le_csInf ⟨0, fun _ ht => ht.1.le⟩ (eta_set_nonempty hn hε₁) ?_
  intro s hs
  exact ⟨hs.1, hs.2.trans hle⟩

/-- **Strict positivity of `η_ε(Λ)`**: for all `0 < ε < 2` (in particular all `0 < ε ≤ 1`),
`0 < η_ε(Λ)`. -/
theorem eta_pos (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) :
    0 < eta Λ ε := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  obtain ⟨w₀, hw₀_mem, hw₀_ne, _⟩ := exists_shortest_nonzero_vector hn (dualLattice Λ)
  have hw₀_pos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀_ne
  let w₁ : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} :=
    ⟨⟨w₀, hw₀_mem⟩, hw₀_ne⟩
  let w₂ : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} :=
    ⟨⟨-w₀, (dualLattice Λ).neg_mem hw₀_mem⟩, neg_ne_zero.mpr hw₀_ne⟩
  have hw_ne : w₁ ≠ w₂ := by
    intro heq
    have hval : w₀ = -w₀ := congrArg (fun x => (x.1 : EuclideanSpace ℝ (Fin n))) heq
    have h2 : (2 : ℝ) • w₀ = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hval
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact hw₀_ne h0
  set c := Real.sqrt (Real.log (2 / ε) / (Real.pi * ‖w₀‖ ^ 2))
  have h2ε : 1 < 2 / ε := (one_lt_div hε).mpr hε2
  have hc_pos : 0 < c := by
    apply Real.sqrt_pos.mpr
    exact div_pos (Real.log_pos h2ε) (by positivity)
  have hlb : ∀ s ∈ {s : ℝ | 0 < s ∧ rhoPunct Λ s ≤ ε}, c ≤ s := by
    intro s hs
    have hsum_le : ∑ w ∈ ({w₁, w₂} : Finset _),
        Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤ rhoPunct Λ s :=
      (summable_rhoPunct hs.1).sum_le_tsum _ (fun _ _ => Real.exp_nonneg _)
    have hpair : ∑ w ∈ ({w₁, w₂} : Finset _),
        Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) =
        2 * Real.exp (-Real.pi * s ^ 2 * ‖w₀‖ ^ 2) := by
      rw [Finset.sum_pair hw_ne]
      simp [w₁, w₂, norm_neg]
      ring
    have hexp_le : Real.exp (-Real.pi * s ^ 2 * ‖w₀‖ ^ 2) ≤ ε / 2 := by
      have h1 : 2 * Real.exp (-Real.pi * s ^ 2 * ‖w₀‖ ^ 2) ≤ ε := by linarith [hs.2]
      linarith
    have hlog_le : -Real.pi * s ^ 2 * ‖w₀‖ ^ 2 ≤ Real.log (ε / 2) := by
      rw [← Real.log_exp (-Real.pi * s ^ 2 * ‖w₀‖ ^ 2)]
      exact Real.log_le_log (Real.exp_pos _) hexp_le
    have hlog_neg : Real.log (ε / 2) = -Real.log (2 / ε) := by
      rw [show ε / 2 = (2 / ε)⁻¹ by field_simp, Real.log_inv]
    have hs_sq : c ^ 2 ≤ s ^ 2 := by
      have harg_nn : 0 ≤ Real.log (2 / ε) / (Real.pi * ‖w₀‖ ^ 2) :=
        div_nonneg (Real.log_pos h2ε).le (by positivity)
      dsimp [c]
      rw [Real.sq_sqrt harg_nn, div_le_iff₀ (by positivity)]
      rw [hlog_neg] at hlog_le
      nlinarith
    by_contra hlt
    push Not at hlt
    have : s ^ 2 < c ^ 2 := pow_lt_pow_left₀ hlt hs.1.le (by norm_num)
    linarith
  exact lt_of_lt_of_le hc_pos (le_csInf (eta_set_nonempty hn hε) hlb)

/-- For any `s > η_ε(Λ)` (`0 < ε`), `ρ_{1/s}(Λ* \ {0}) ≤ ε`. -/
theorem rhoPunct_le_of_eta_lt (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε s : ℝ} (hε : 0 < ε) (hs : eta Λ ε < s) :
    rhoPunct Λ s ≤ ε := by
  have hex : ∃ t ∈ {t : ℝ | 0 < t ∧ rhoPunct Λ t ≤ ε}, t < s := by
    by_contra hall
    push Not at hall
    have hle : s ≤ eta Λ ε := le_csInf (eta_set_nonempty hn hε) hall
    linarith
  obtain ⟨t, ⟨ht_pos, ht_rho⟩, hts⟩ := hex
  exact (rhoPunct_antitone ht_pos hts.le).trans ht_rho

/-- For every `0 < ε < 2` and every `s ≥ η_ε(Λ)`, `ρ_{1/s}(Λ* \ {0}) ≤ ε` (right-continuity of
`rhoPunct` at `η_ε(Λ)`). -/
theorem rhoPunct_le_of_eta_le (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε s : ℝ} (hε : 0 < ε) (hε2 : ε < 2) (hs : eta Λ ε ≤ s) :
    rhoPunct Λ s ≤ ε := by
  have heta_pos : 0 < eta Λ ε := eta_pos hn hε hε2
  suffices h0 : rhoPunct Λ (eta Λ ε) ≤ ε from
    (rhoPunct_antitone heta_pos hs).trans h0
  have hsum : Summable fun w : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      Real.exp (-Real.pi * (eta Λ ε) ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
    summable_rhoPunct heta_pos
  refine le_of_tendsto hsum.hasSum (Filter.Eventually.of_forall fun F => ?_)
  let g : ℝ → ℝ := fun t =>
    ∑ w ∈ F, Real.exp (-Real.pi * t ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hg_cont : Continuous g := by fun_prop
  have htend : Tendsto (fun k : ℕ => eta Λ ε + 1 / ((k : ℝ) + 1)) atTop (nhds (eta Λ ε)) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine le_of_tendsto (hg_cont.continuousAt.tendsto.comp htend)
    (Filter.Eventually.of_forall fun k => ?_)
  have hk_gt : eta Λ ε < eta Λ ε + 1 / ((k : ℝ) + 1) := by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hk_pos : 0 < eta Λ ε + 1 / ((k : ℝ) + 1) := lt_trans heta_pos hk_gt
  have hpart : g (eta Λ ε + 1 / ((k : ℝ) + 1)) ≤ rhoPunct Λ (eta Λ ε + 1 / ((k : ℝ) + 1)) :=
    (summable_rhoPunct hk_pos).sum_le_tsum F (fun _ _ => Real.exp_nonneg _)
  exact hpart.trans (rhoPunct_le_of_eta_lt hn hε hk_gt)

/-! ## Section 2: Full `0 < ε ≤ 1` Dual Smoothing Bound (MR07 Lemma 3.2) -/

/-- **Full Micciancio–Regev (2007) Dual Smoothing Bound (`0 < ε ≤ 1`)**:
For every dimension `n ≥ 1`, every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, and EVERY
`0 < ε ≤ 1` (including `n = 1` and `1 / (2^n - 1) ≤ ε ≤ 1`):
`η_ε(Λ) ≤ √(n + ln(1/ε)/π) / λ₁(Λ*)`. -/
theorem eta_le_sqrt_n_add_log_div_lambda1 (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) /
        shortestNorm (dualLattice Λ) := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  have hL_nn : 0 ≤ shortestNorm (dualLattice Λ) := shortestNorm_nonneg _
  have h2n_ge : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hden_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ n - 1 := by linarith
  have hden_pos : 0 < (2 : ℝ) ^ n - 1 := by linarith
  by_cases hlt : ε < 1 / ((2 : ℝ) ^ n - 1)
  · have hcore := eta_le_sqrt_scaling (Λ := Λ) hn hε hlt
    have hprod_ge : ε ≤ ε * ((2 : ℝ) ^ n - 1) := by
      simpa using mul_le_mul_of_nonneg_left hden_ge1 hε.le
    have hinv_le : 1 / (ε * ((2 : ℝ) ^ n - 1)) ≤ 1 / ε :=
      one_div_le_one_div_of_le hε hprod_ge
    have hlog_le : Real.log (1 / (ε * ((2 : ℝ) ^ n - 1))) ≤ Real.log (1 / ε) :=
      Real.log_le_log (by positivity) hinv_le
    have hsqrt_le : Real.sqrt ((n : ℝ) + Real.log (1 / (ε * ((2 : ℝ) ^ n - 1))) / Real.pi) ≤
        Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) := by
      apply Real.sqrt_le_sqrt
      gcongr
    exact hcore.trans (div_le_div_of_nonneg_right hsqrt_le hL_nn)
  · have hge : 1 / ((2 : ℝ) ^ n - 1) ≤ ε := not_lt.mp hlt
    have hanti := eta_antitone (Λ := Λ) hn (one_div_pos.mpr hden_pos) hge
    have hcore := eta_le_sqrt_n_div_lambda1 (Λ := Λ) hn
    have h1ε : 1 ≤ 1 / ε := (one_le_div hε).mpr hε1
    have hlog_nn : 0 ≤ Real.log (1 / ε) := Real.log_nonneg h1ε
    have hsqrt_le : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) := by
      apply Real.sqrt_le_sqrt
      have : 0 ≤ Real.log (1 / ε) / Real.pi := div_nonneg hlog_nn Real.pi_pos.le
      linarith
    exact (hanti.trans hcore).trans (div_le_div_of_nonneg_right hsqrt_le hL_nn)

/-- Equivalent `Stage2SiegelReduction.lambda1` form of `eta_le_sqrt_n_add_log_div_lambda1`. -/
theorem eta_le_sqrt_n_add_log_div_lambda1' (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) /
        RHDirect.Stage2SiegelReduction.lambda1 (dualLattice Λ) := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  rw [← shortestNorm_eq_lambda1 hn (dualLattice Λ)]
  exact eta_le_sqrt_n_add_log_div_lambda1 hn hε hε1

/-! ## Section 3: MR07 Lemma 3.3 — Primal `λ_n(Λ)` & Gram–Schmidt Smoothing Bounds -/

/-- Banaszczyk transference lower sandwich in primal-`λ_n` / dual-`λ_1` form:
`1 ≤ λ₁(Λ*) · λ_n(Λ)`. -/
theorem one_le_shortestNorm_dual_mul_lambdan (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    1 ≤ shortestNorm (dualLattice Λ) *
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  have h := (banaszczyk_transference_lambda1_lambdan hn (dualLattice Λ)).1
  rwa [dualLattice_dualLattice Λ] at h

/-- Inverse dual shortest vector bound: `λ₁(Λ*)⁻¹ ≤ λ_n(Λ)`. -/
theorem inv_shortestNorm_dual_le_lambdan (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (shortestNorm (dualLattice Λ))⁻¹ ≤
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  rw [inv_eq_one_div, div_le_iff₀ (shortestNorm_pos hn (dualLattice Λ)), mul_comm]
  exact one_le_shortestNorm_dual_mul_lambdan hn

/-- **MR07 Lemma 3.3 (Primal `λ_n(Λ)` Smoothing Bound via Banaszczyk Transference)**:
For every `n ≥ 1`, every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, and all `0 < ε ≤ 1`:
`η_ε(Λ) ≤ √(n + ln(1/ε)/π) · λ_n(Λ)`. -/
theorem eta_le_sqrt_n_add_log_mul_lambdan (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) *
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
          Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
  have hdual := eta_le_sqrt_n_add_log_div_lambda1 (Λ := Λ) hn hε hε1
  rw [div_eq_mul_inv] at hdual
  exact hdual.trans (mul_le_mul_of_nonneg_left (inv_shortestNorm_dual_le_lambdan hn)
    (Real.sqrt_nonneg _))

/-- Equivalent `Stage2SiegelReduction.succMin` form of `eta_le_sqrt_n_add_log_mul_lambdan`. -/
theorem eta_le_sqrt_n_add_log_mul_succMin (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) *
        RHDirect.Stage2SiegelReduction.succMin Λ
          ⟨n - 1, by
            rw [RHDirect.ArakelovCovolume.rk, ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
            exact Nat.sub_lt hn zero_lt_one⟩ := by
  have h := eta_le_sqrt_n_add_log_mul_lambdan (Λ := Λ) hn hε hε1
  have hrk : RHDirect.ArakelovCovolume.rk Λ = n := by
    rw [RHDirect.ArakelovCovolume.rk, ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  have hsucc := RHDirect.Stage11BostDworkSqueeze.succMin_eq_stage10_successiveMinimum Λ
    ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
  have heq : RHDirect.Stage2SiegelReduction.succMin Λ
      ⟨n - 1, by rw [hrk]; exact Nat.sub_lt hn zero_lt_one⟩ =
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
    convert hsucc using 2
    ext; simp
  rwa [heq]

/-- **Gram–Schmidt Dual Shortest-Vector Lower Bound**:
For ANY `ℤ`-basis `b : Basis (Fin n) ℤ Λ`, there exists an index `i : Fin n` such that
`1 ≤ λ₁(Λ*) · ‖b̃_i‖` (where `b̃_i = gramSchmidtVec (fun k => (b k : ℝ^n)) i`). -/
theorem exists_one_le_shortestNorm_dual_mul_gsNorm (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ) :
    ∃ i : Fin n,
      1 ≤ shortestNorm (dualLattice Λ) *
        ‖gramSchmidtVec (fun k => (b k : EuclideanSpace ℝ (Fin n))) i‖ := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  obtain ⟨v₀, hv₀_mem, hv₀_ne, hv₀_min⟩ := exists_shortest_nonzero_vector hn (dualLattice Λ)
  have hlam_eq : shortestNorm (dualLattice Λ) = ‖v₀‖ :=
    shortestNorm_eq_of_min (dualLattice Λ) hv₀_mem hv₀_ne hv₀_min
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun k => (b k : EuclideanSpace ℝ (Fin n))
  let bR : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := b.ofZLatticeBasis ℝ
  have hbR : ∀ j, bR j = v j := fun j => Basis.ofZLatticeBasis_apply ℝ Λ b j
  have hnonzero : ∃ j : Fin n, inner ℝ (v j) v₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hv₀_sq : inner ℝ v₀ v₀ = 0 := by
      have hrepr : v₀ = ∑ j : Fin n, bR.repr v₀ j • bR j := (bR.sum_repr v₀).symm
      nth_rewrite 1 [hrepr]
      rw [sum_inner]
      exact Finset.sum_eq_zero fun j _ => by
        rw [real_inner_smul_left, hbR j, hall j, mul_zero]
    rw [real_inner_self_eq_norm_sq] at hv₀_sq
    exact hv₀_ne (norm_eq_zero.mp (sq_eq_zero_iff.mp hv₀_sq))
  let S : Finset (Fin n) := Finset.univ.filter fun j => inner ℝ (v j) v₀ ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hnonzero
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let i : Fin n := S.min' hS
  have hi_ne : inner ℝ (v i) v₀ ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hlt_zero : ∀ t : Fin n, t < i → inner ℝ (v t) v₀ = 0 := by
    intro t hti
    by_contra ht0
    have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht0⟩
    exact not_le.mpr hti (Finset.min'_le S t htS)
  have hdiff_mem : v i - gramSchmidtVec v i ∈ Submodule.span ℝ {x | ∃ t : Fin n, t < i ∧ v t = x} :=
    gramSchmidtVec_sub_mem_span_lt v i
  have hdiff_inner : inner ℝ (v i - gramSchmidtVec v i) v₀ = 0 := by
    refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by
      rw [inner_add_left, hx, hy, add_zero]) (fun a x _ hx => by
      rw [real_inner_smul_left, hx, mul_zero]) hdiff_mem
    rintro x ⟨t, hti, rfl⟩
    exact hlt_zero t hti
  have hgs_eq : inner ℝ (gramSchmidtVec v i) v₀ = inner ℝ (v i) v₀ := by
    have := hdiff_inner
    rw [inner_sub_left] at this
    linarith
  obtain ⟨k, hk⟩ := hv₀_mem (v i) (b i).2
  have hk_ne : k ≠ 0 := by
    intro hk0
    apply hi_ne
    rw [hk, hk0, Int.cast_zero]
  have hk_ge1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk_ne
    have hnat : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast this
    simpa [Int.cast_abs] using hnat
  have hcs : |inner ℝ (gramSchmidtVec v i) v₀| ≤ ‖gramSchmidtVec v i‖ * ‖v₀‖ :=
    abs_real_inner_le_norm _ _
  refine ⟨i, ?_⟩
  rw [hlam_eq]
  have h1 : (1 : ℝ) ≤ ‖gramSchmidtVec v i‖ * ‖v₀‖ := by
    calc (1 : ℝ) ≤ |(k : ℝ)| := hk_ge1
      _ = |inner ℝ (v i) v₀| := by rw [hk]
      _ = |inner ℝ (gramSchmidtVec v i) v₀| := by rw [hgs_eq]
      _ ≤ ‖gramSchmidtVec v i‖ * ‖v₀‖ := hcs
  linarith

/-- **MR07 Lemma 3.3 (Gram–Schmidt Upper-Bound Form)**:
For any `ℤ`-basis `b : Basis (Fin n) ℤ Λ`, any upper bound `M` on the Gram–Schmidt norms
`∀ i, ‖b̃_i‖ ≤ M`, and all `0 < ε ≤ 1`:
`η_ε(Λ) ≤ √(n + ln(1/ε)/π) · M`. -/
theorem eta_le_sqrt_n_add_log_mul_gsNorm_bound (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ) {M : ℝ}
    (hM : ∀ i : Fin n, ‖gramSchmidtVec (fun k => (b k : EuclideanSpace ℝ (Fin n))) i‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤ Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) * M := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  obtain ⟨i, hi⟩ := exists_one_le_shortestNorm_dual_mul_gsNorm hn b
  have hL : 0 < shortestNorm (dualLattice Λ) := shortestNorm_pos hn (dualLattice Λ)
  have hinv_le : (shortestNorm (dualLattice Λ))⁻¹ ≤ M := by
    rw [inv_eq_one_div, div_le_iff₀ hL, mul_comm]
    exact hi.trans (mul_le_mul_of_nonneg_left (hM i) hL.le)
  have hdual := eta_le_sqrt_n_add_log_div_lambda1 (Λ := Λ) hn hε hε1
  rw [div_eq_mul_inv] at hdual
  exact hdual.trans (mul_le_mul_of_nonneg_left hinv_le (Real.sqrt_nonneg _))

/-- **MR07 Lemma 3.3 (Max Gram–Schmidt Norm Form)**:
For any `ℤ`-basis `b : Basis (Fin n) ℤ Λ` and all `0 < ε ≤ 1`:
`η_ε(Λ) ≤ √(n + ln(1/ε)/π) · max_i ‖b̃_i‖`. -/
theorem eta_le_sqrt_n_add_log_mul_max_gsNorm (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) *
        Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (fun i : Fin n => ‖gramSchmidtVec (fun k => (b k : EuclideanSpace ℝ (Fin n))) i‖) :=
  eta_le_sqrt_n_add_log_mul_gsNorm_bound hn b
    (fun i => Finset.le_sup'
      (fun j : Fin n => ‖gramSchmidtVec (fun k => (b k : EuclideanSpace ℝ (Fin n))) j‖)
      (Finset.mem_univ i))
    hε hε1

/-- **MR07 Lemma 3.3 (Max Basis-Vector Norm Form)**:
For any `ℤ`-basis `b : Basis (Fin n) ℤ Λ` and all `0 < ε ≤ 1`:
`η_ε(Λ) ≤ √(n + ln(1/ε)/π) · max_i ‖b_i‖`. -/
theorem eta_le_sqrt_n_add_log_mul_max_basis_norm (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) *
        Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (fun i : Fin n => ‖(b i : EuclideanSpace ℝ (Fin n))‖) :=
  eta_le_sqrt_n_add_log_mul_gsNorm_bound hn b
    (fun i => (RHDirect.Stage2SiegelReduction.gsVec_norm_le
      (fun k => (b k : EuclideanSpace ℝ (Fin n))) i).trans
      (Finset.le_sup' (fun j : Fin n => ‖(b j : EuclideanSpace ℝ (Fin n))‖) (Finset.mem_univ i)))
    hε hε1

/-! ## Section 4: MR07 Lemma 4.1 — Folded Gaussian Density & Statistical Distance `≤ ε / 2` -/

/-- The **folded continuous Gaussian density** on `ℝ^n / Λ` at width `s > 0`:
`p_s(x) := s⁻ⁿ · ρ_s(Λ − x)`. -/
def foldedGaussianDensity {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (s ^ n)⁻¹ * rhoShift s Λ x

/-- `s⁻ⁿ` rewrite: for `0 < s`, `foldedGaussianDensity Λ s x = s ^ (-(n : ℝ)) * rhoShift s Λ x`. -/
theorem foldedGaussianDensity_eq_rpow {s : ℝ} (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    foldedGaussianDensity Λ s x = s ^ (-(n : ℝ)) * rhoShift s Λ x := by
  unfold foldedGaussianDensity
  rw [Real.rpow_neg hs.le, Real.rpow_natCast]

theorem foldedGaussianDensity_nonneg {s : ℝ} (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ foldedGaussianDensity Λ s x := by
  unfold foldedGaussianDensity
  refine mul_nonneg (inv_nonneg.mpr (pow_nonneg hs n)) ?_
  exact tsum_nonneg fun _ => Real.exp_nonneg _

/-- Lattice periodicity of the folded Gaussian density: `p_s(x + v) = p_s(x)` for all `v ∈ Λ`. -/
theorem foldedGaussianDensity_add_mem {s : ℝ}
    (x : EuclideanSpace ℝ (Fin n)) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Λ) :
    foldedGaussianDensity Λ s (x + v) = foldedGaussianDensity Λ s x := by
  unfold foldedGaussianDensity
  rw [rhoShift_add_mem s Λ x hv]

/-- Poisson representation of the folded continuous Gaussian density:
`p_s(x) = (covol Λ)⁻¹ · (1 + dualErr Λ s x)`. -/
theorem foldedGaussianDensity_eq_covol_inv_mul {s : ℝ} (hs : 0 < s)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (x : EuclideanSpace ℝ (Fin n)) :
    foldedGaussianDensity Λ s x = (ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x) := by
  unfold foldedGaussianDensity
  rw [rhoShift_eq_one_add_dualErr (Λ := Λ) hs x, div_eq_mul_inv]
  have hs_ne : s ^ n ≠ 0 := (pow_pos hs n).ne'
  calc (s ^ n)⁻¹ * (s ^ n * (ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x))
      = ((s ^ n)⁻¹ * s ^ n) * ((ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x)) := by ring
    _ = 1 * ((ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x)) := by rw [inv_mul_cancel₀ hs_ne]
    _ = (ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x) := one_mul _

/-- Continuity of the dual Fourier error term `x ↦ dualErr Λ s x` via the Weierstrass M-test. -/
theorem continuous_dualErr {s : ℝ} (hs : 0 < s)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => dualErr Λ s x) := by
  unfold dualErr
  refine continuous_tsum (fun w => by fun_prop) (summable_rhoPunct (Λ := Λ) hs) fun w x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  nlinarith [Real.abs_cos_le_one (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) x),
    Real.exp_nonneg (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)]

/-- Continuity of the folded continuous Gaussian density `x ↦ p_s(x)` for `s > 0`. -/
theorem continuous_foldedGaussianDensity {s : ℝ} (hs : 0 < s)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => foldedGaussianDensity Λ s x) := by
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => foldedGaussianDensity Λ s x) =
      fun x => (ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x) :=
    funext (foldedGaussianDensity_eq_covol_inv_mul hs)
  rw [heq]
  exact continuous_const.mul (continuous_const.add (continuous_dualErr hs))

/-- **MR07 Lemma 4.1 (Shifted-Mass Pointwise Bound)**:
For `n ≥ 1`, `0 < ε < 1`, and `s ≥ η_ε(Λ)`, every shift `x : ℝ^n` satisfies:
`|ρ_s(Λ − x) − sⁿ / covol Λ| ≤ ε · (sⁿ / covol Λ)`. -/
theorem abs_rhoShift_sub_le (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hs_eta : eta Λ ε ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    |rhoShift s Λ x - s ^ n / ZLattice.covolume Λ volume| ≤
      ε * (s ^ n / ZLattice.covolume Λ volume) := by
  have hs : 0 < s := lt_of_lt_of_le (eta_pos hn hε (by linarith)) hs_eta
  have hsmooth : rhoPunct Λ s ≤ ε := rhoPunct_le_of_eta_le hn hε (by linarith) hs_eta
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  have hF_nn : 0 ≤ s ^ n / ZLattice.covolume Λ volume :=
    div_nonneg (pow_nonneg hs.le n) hcov_pos.le
  rw [rhoShift_eq_one_add_dualErr (Λ := Λ) hs x]
  have hdiff : s ^ n / ZLattice.covolume Λ volume * (1 + dualErr Λ s x) -
      s ^ n / ZLattice.covolume Λ volume =
      dualErr Λ s x * (s ^ n / ZLattice.covolume Λ volume) := by ring
  rw [hdiff, abs_mul, abs_of_nonneg hF_nn]
  have hE : |dualErr Λ s x| ≤ ε :=
    (abs_dualErr_le_rhoPunct (Λ := Λ) hs x).trans hsmooth
  exact mul_le_mul_of_nonneg_right hE hF_nn

/-- **MR07 Lemma 4.1 (Pointwise Folded Density Bound)**:
For `n ≥ 1`, `0 < ε < 1`, and `s ≥ η_ε(Λ)`, every `x : ℝ^n` satisfies:
`|p_s(x) − (covol Λ)⁻¹| ≤ ε · (covol Λ)⁻¹`. -/
theorem abs_foldedGaussianDensity_sub_le (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hs_eta : eta Λ ε ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹| ≤
      ε * (ZLattice.covolume Λ volume)⁻¹ := by
  have hs : 0 < s := lt_of_lt_of_le (eta_pos hn hε (by linarith)) hs_eta
  have hsmooth : rhoPunct Λ s ≤ ε := rhoPunct_le_of_eta_le hn hε (by linarith) hs_eta
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  have hinv_nn : 0 ≤ (ZLattice.covolume Λ volume)⁻¹ := inv_nonneg.mpr hcov_pos.le
  rw [foldedGaussianDensity_eq_covol_inv_mul hs x]
  have hdiff : (ZLattice.covolume Λ volume)⁻¹ * (1 + dualErr Λ s x) -
      (ZLattice.covolume Λ volume)⁻¹ =
      dualErr Λ s x * (ZLattice.covolume Λ volume)⁻¹ := by ring
  rw [hdiff, abs_mul, abs_of_nonneg hinv_nn]
  have hE : |dualErr Λ s x| ≤ ε :=
    (abs_dualErr_le_rhoPunct (Λ := Λ) hs x).trans hsmooth
  exact mul_le_mul_of_nonneg_right hE hinv_nn

/-- Two-sided pointwise sandwich for the folded Gaussian density:
`(1 − ε) · (covol Λ)⁻¹ ≤ p_s(x) ≤ (1 + ε) · (covol Λ)⁻¹`. -/
theorem foldedGaussianDensity_mem_Icc (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hs_eta : eta Λ ε ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    (1 - ε) * (ZLattice.covolume Λ volume)⁻¹ ≤ foldedGaussianDensity Λ s x ∧
      foldedGaussianDensity Λ s x ≤ (1 + ε) * (ZLattice.covolume Λ volume)⁻¹ := by
  have h := abs_le.mp (abs_foldedGaussianDensity_sub_le hn hε hε1 hs_eta x)
  constructor <;> linarith

/-- **MR07 Lemma 4.1 (Total-Variation / Statistical Distance `≤ ε / 2` over Any Fundamental Domain)**:
For `n ≥ 1`, `0 < ε < 1`, `s ≥ η_ε(Λ)`, and ANY fundamental domain `F` of `Λ`
(`IsAddFundamentalDomain Λ.toAddSubgroup F volume`):
`(1 / 2) * ∫ x in F, |p_s(x) − (covol Λ)⁻¹| ≤ ε / 2`. -/
theorem tv_distance_foldedGaussianDensity_isAddFundamentalDomain (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {F : Set (EuclideanSpace ℝ (Fin n))}
    (hfund : IsAddFundamentalDomain Λ.toAddSubgroup F volume)
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hs_eta : eta Λ ε ≤ s) :
    (1 / 2 : ℝ) *
        ∫ x in F, |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹| ∂volume ≤
      ε / 2 := by
  have hs : 0 < s := lt_of_lt_of_le (eta_pos hn hε (by linarith)) hs_eta
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  let b₀ : Basis (Fin n) ℤ Λ := basisOfZLattice Λ
  haveI : Countable Λ.toAddSubgroup :=
    Function.Injective.countable
      (f := fun x : Λ.toAddSubgroup => (b₀.repr ⟨x.1, x.2⟩ : Fin n → ℤ))
      (fun x y hxy =>
        Subtype.ext (congrArg Subtype.val (b₀.repr.injective (Finsupp.ext (congrFun hxy)))))
  have hfund₀ : IsAddFundamentalDomain Λ.toAddSubgroup
      (ZSpan.fundamentalDomain (b₀.ofZLatticeBasis ℝ)) volume :=
    ZLattice.isAddFundamentalDomain b₀ volume
  have hF_lt_top : volume F < ⊤ := by
    rw [hfund.measure_eq hfund₀]
    exact (ZSpan.fundamentalDomain_isBounded (b₀.ofZLatticeBasis ℝ)).measure_lt_top
  have hconst_int : IntegrableOn
      (fun _ : EuclideanSpace ℝ (Fin n) => ε * (ZLattice.covolume Λ volume)⁻¹) F volume :=
    integrableOn_const (hs := hF_lt_top.ne)
  have hf_cont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹|) :=
    ((continuous_foldedGaussianDensity hs).sub continuous_const).abs
  have hf_int : IntegrableOn
      (fun x : EuclideanSpace ℝ (Fin n) =>
        |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹|) F volume := by
    refine Integrable.mono' hconst_int hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_foldedGaussianDensity_sub_le hn hε hε1 hs_eta x
  have hmono : ∫ x in F, |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹| ∂volume ≤
      ∫ _ in F, (ε * (ZLattice.covolume Λ volume)⁻¹) ∂volume :=
    integral_mono hf_int hconst_int fun x =>
      abs_foldedGaussianDensity_sub_le hn hε hε1 hs_eta x
  have hconst_eq : ∫ _ in F, (ε * (ZLattice.covolume Λ volume)⁻¹) ∂volume = ε := by
    rw [setIntegral_const, smul_eq_mul,
      ← ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfund]
    field_simp [hcov_pos.ne']
  have hl1 : ∫ x in F, |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹| ∂volume ≤ ε :=
    hmono.trans_eq hconst_eq
  linarith

/-- **MR07 Lemma 4.1 (Fundamental Parallelepiped `P(B)` Form)**:
For `n ≥ 1`, `0 < ε < 1`, `s ≥ η_ε(Λ)`, and ANY `ℤ`-basis `b : Basis (Fin n) ℤ Λ`
with fundamental parallelepiped `P(B) = ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)`:
`(1 / 2) * ∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), |p_s(x) − (covol Λ)⁻¹| ≤ ε / 2`. -/
theorem tv_distance_foldedGaussianDensity_fundamentalDomain (hn : 0 < n)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ)
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hs_eta : eta Λ ε ≤ s) :
    (1 / 2 : ℝ) *
        ∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ),
          |foldedGaussianDensity Λ s x - (ZLattice.covolume Λ volume)⁻¹| ∂volume ≤
      ε / 2 :=
  tv_distance_foldedGaussianDensity_isAddFundamentalDomain hn
    (ZLattice.isAddFundamentalDomain b volume) hε hε1 hs_eta

end RHDirect.LatticeSmoothingFull
