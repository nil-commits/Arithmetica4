/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 060 (Erdős Problem #120): The Erdős Similarity Conjecture

## Scope & Honest Labeling
Erdős Problem #120 ($100, Paul Erdős 1974) asks whether for every infinite set `A ⊆ ℝ`,
there exists a measurable set `E ⊆ ℝ` of positive Lebesgue measure (`0 < volume E`)
containing no nontrivial affine copy `(fun x => a * x + b) '' A` (`a ≠ 0`).

Despite the October 2026 resolution of the geometric progression case `{q^n}` (and null
sequences with `liminf a_{n+1}/a_n > 0`), the conjecture remains **OPEN in full generality**
(notably for super-exponentially decaying sequences such as `{2^{-2^n}}` and `{1/n!}`).

This file formalizes 100% from scratch — with **zero custom or `private` definitions in
any public theorem signature** (pure Mathlib `MeasureTheory.volume`, `MeasurableSet`,
`IsCompact`, `Set.image`, `ℝ` types) — the following verified theorems:

1. **Steinhaus Finite-Set Universality & Difference-Set Contrast:**
   - `ppl060_steinhaus_small_scales`
   - `ppl060_steinhaus_finite_universality`
   - `ppl060_steinhaus_difference_set`
2. **Unbounded-Set Non-Universality & Bolzano–Weierstrass Reduction:**
   - `ppl060_unbounded_nonuniversal`
   - `ppl060_affine_avoidance_monotone`
   - `ppl060_affine_avoidance_of_affine_equiv`
   - `ppl060_reduction_to_monotone_null_seq`
   - `ppl060_conjecture_equiv_null_seq`
3. **Falconer (1984) / Eigen (1985) Slow-Decay Non-Universality Theorem:**
   - `ppl060_falconer_eigen_slow_decay` (compact `E ⊆ [0, 1]`, `volume E ≥ 1 - ε`, no monotonicity required)
   - `ppl060_harmonic_nonuniversal`, `ppl060_power_decay_nonuniversal`,
     `ppl060_log_decay_nonuniversal`, `ppl060_subexponential_nonuniversal`
4. **Universal Translation & Countable-Scale Avoidance for Arbitrary Infinite Sets:**
   - `ppl060_translation_avoidance_arbitrary_infinite`
   - `ppl060_countable_scales_avoidance_arbitrary_infinite`
   - `ppl060_rational_scales_avoidance`
   - `ppl060_dyadic_scales_avoidance`
5. **Geometric-Progression Continuum-Scale Avoidance (All `q ∈ (0, 1)`):**
   - `ppl060_geometric_bounded_scale_avoidance`
   - `ppl060_dyadic_bounded_scale_avoidance`
-/

namespace PPL060

open MeasureTheory Filter Topology

/-! ### Section 1: Steinhaus Finite-Set Universality & Difference-Set Contrast -/

/-- Inner-regularity helper: every measurable set `E ⊆ ℝ` with `0 < volume E` contains a compact
subset `K ⊆ E` with `0 < volume K` and `volume K < ⊤`. -/
private lemma exists_compact_subset_pos_lt_top {E : Set ℝ}
    (hE : MeasurableSet E) (hpos : 0 < volume E) :
    ∃ K : Set ℝ, K ⊆ E ∧ IsCompact K ∧ 0 < volume K ∧ volume K < ⊤ := by
  have hcover : E = ⋃ n : ℕ, (E ∩ Set.Icc (-(n : ℝ)) (n : ℝ)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      refine ⟨n, hx, ?_, ?_⟩
      · linarith [(abs_le.mp hn).1]
      · exact (abs_le.mp hn).2
    · rintro ⟨_, hx, _⟩
      exact hx
  have hexN : ∃ n : ℕ, 0 < volume (E ∩ Set.Icc (-(n : ℝ)) (n : ℝ)) := by
    by_contra hall
    push Not at hall
    have hzero : ∀ n : ℕ, volume (E ∩ Set.Icc (-(n : ℝ)) (n : ℝ)) = 0 :=
      fun n => le_antisymm (hall n) zero_le
    have hE0 : volume E = 0 := by
      rw [hcover]
      exact measure_iUnion_null hzero
    exact hpos.ne' hE0
  obtain ⟨n, hn_pos⟩ := hexN
  let E' : Set ℝ := E ∩ Set.Icc (-(n : ℝ)) (n : ℝ)
  have hE'_meas : MeasurableSet E' := hE.inter measurableSet_Icc
  have hE'_fin : volume E' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨K, hKE', hKcomp, hKlt⟩ := hE'_meas.exists_isCompact_lt_add hE'_fin hn_pos.ne'
  have hKpos : 0 < volume K := by
    by_contra hK0
    push Not at hK0
    have hKeq0 : volume K = 0 := le_antisymm hK0 zero_le
    rw [hKeq0, zero_add] at hKlt
    exact lt_irrefl _ hKlt
  refine ⟨K, hKE'.trans Set.inter_subset_left, hKcomp, hKpos,
    lt_of_le_of_lt (measure_mono hKE') hE'_fin.lt_top⟩

/-- **Generalized Steinhaus Small-Scale Universality**: For every measurable `E ⊆ ℝ` with
`0 < volume E` and every finite set `F : Finset ℝ`, there exists `δ > 0` such that for EVERY
scale `a : ℝ` satisfying `∀ y ∈ F, |a * y| < δ`, there exists `b ∈ E` with
`(fun y => a * y + b) '' (F : Set ℝ) ⊆ E`. -/
theorem ppl060_steinhaus_small_scales
    {E : Set ℝ} (hE : MeasurableSet E) (hpos : 0 < volume E) (F : Finset ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, (∀ y ∈ F, |a * y| < δ) →
      ∃ b ∈ E, (fun y : ℝ => a * y + b) '' (F : Set ℝ) ⊆ E := by
  by_cases hF : F.Nonempty
  · obtain ⟨K, hKE, hKcomp, hKpos, hKlt⟩ := exists_compact_subset_pos_lt_top hE hpos
    have hk_pos : (0 : ENNReal) < (F.card : ENNReal) := by
      exact_mod_cast hF.card_pos
    have hk_ne_top : (F.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top F.card
    have hdiv_pos : (0 : ENNReal) < volume K / (F.card : ENNReal) :=
      ENNReal.div_pos hKpos.ne' hk_ne_top
    obtain ⟨U, hKU, hUopen, _, hUdiff⟩ :=
      hKcomp.measurableSet.exists_isOpen_sdiff_lt hKlt.ne hdiv_pos.ne'
    obtain ⟨δ, hδ_pos, hthick⟩ := hKcomp.exists_thickening_subset_open hUopen hKU
    refine ⟨δ, hδ_pos, fun a ha => ?_⟩
    let B : Set ℝ := ⋃ y ∈ F, (fun z : ℝ => z - a * y) '' (U \ K)
    have hB_le : volume B ≤ (F.card : ENNReal) * volume (U \ K) := by
      calc volume B
          ≤ ∑ y ∈ F, volume ((fun z : ℝ => z - a * y) '' (U \ K)) :=
            measure_biUnion_finset_le F _
        _ = ∑ _y ∈ F, volume (U \ K) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            have hpre : (fun z : ℝ => z - a * y) '' (U \ K) =
                (fun z : ℝ => z + a * y) ⁻¹' (U \ K) := by
              ext z
              simp only [Set.mem_image, Set.mem_preimage]
              constructor
              · rintro ⟨w, hw, rfl⟩
                simpa [sub_add_cancel] using hw
              · intro hz
                exact ⟨z + a * y, hz, by ring⟩
            rw [hpre, MeasureTheory.measure_preimage_add_right]
        _ = (F.card : ENNReal) * volume (U \ K) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hB_lt : volume B < volume K := by
      calc volume B
          ≤ (F.card : ENNReal) * volume (U \ K) := hB_le
        _ < (F.card : ENNReal) * (volume K / (F.card : ENNReal)) := by
            rw [mul_comm (F.card : ENNReal), mul_comm (F.card : ENNReal)]
            exact ENNReal.mul_lt_mul_left hk_pos.ne' hk_ne_top hUdiff
        _ = volume K := ENNReal.mul_div_cancel hk_pos.ne' hk_ne_top
    have hKB_ne : (K \ B).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hempty
      exact hB_lt.not_ge (measure_mono hempty)
    obtain ⟨b, hbK, hbB⟩ := hKB_ne
    refine ⟨b, hKE hbK, ?_⟩
    rintro _ ⟨y, hyF, rfl⟩
    have hyU : a * y + b ∈ U := by
      have hmem : a * y + b ∈ Metric.thickening δ K := by
        rw [Metric.mem_thickening_iff]
        refine ⟨b, hbK, ?_⟩
        rw [Real.dist_eq]
        simpa [add_sub_cancel_right] using ha y hyF
      exact hthick hmem
    have hyK : a * y + b ∈ K := by
      by_contra hnotK
      apply hbB
      refine Set.mem_iUnion₂.mpr ⟨y, hyF, a * y + b, ⟨hyU, hnotK⟩, ?_⟩
      ring
    exact hKE hyK
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    have hEne : E.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      subst h
      simp at hpos
    obtain ⟨b, hb⟩ := hEne
    exact ⟨1, one_pos, fun _ _ => ⟨b, hb, by simp⟩⟩

/-- **Steinhaus Finite-Set Universality Contrast**: Every measurable set `E ⊆ ℝ` with
`0 < volume E` contains a positively-scaled affine copy `(fun x => a * x + b) '' (F : Set ℝ)`
(`0 < a`, hence `a ≠ 0`) of EVERY finite set `F : Finset ℝ`. -/
theorem ppl060_steinhaus_finite_universality
    {E : Set ℝ} (hE : MeasurableSet E) (hpos : 0 < volume E) (F : Finset ℝ) :
    ∃ a b : ℝ, 0 < a ∧ (fun x : ℝ => a * x + b) '' (F : Set ℝ) ⊆ E := by
  obtain ⟨δ, hδ_pos, hsmall⟩ := ppl060_steinhaus_small_scales hE hpos F
  by_cases hF : F.Nonempty
  · let M : ℝ := F.sup' hF (fun y => |y|) + 1
    have hM_pos : 0 < M := by
      have ⟨y0, hy0⟩ := hF
      have h0 : 0 ≤ F.sup' hF (fun y => |y|) :=
        le_trans (abs_nonneg y0) (Finset.le_sup' (f := fun y : ℝ => |y|) hy0)
      linarith
    let a : ℝ := δ / (2 * M)
    have ha_pos : 0 < a := by positivity
    have ha_bound : ∀ y ∈ F, |a * y| < δ := by
      intro y hy
      rw [abs_mul, abs_of_pos ha_pos]
      have hyM : |y| ≤ M - 1 := by
        dsimp only [M]
        have := Finset.le_sup' (f := fun y : ℝ => |y|) hy
        linarith
      have h1 : a * |y| ≤ a * M := by
        apply mul_le_mul_of_nonneg_left _ ha_pos.le
        linarith
      have h2 : a * M = δ / 2 := by
        dsimp only [a]
        field_simp
      linarith
    obtain ⟨b, _, hsub⟩ := hsmall a ha_bound
    exact ⟨a, b, ha_pos, hsub⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    exact ⟨1, 0, one_pos, by simp⟩

/-- **Steinhaus Difference-Set Theorem**: For every measurable set `E ⊆ ℝ` with `0 < volume E`,
there exists `δ > 0` such that `(-δ, δ) ⊆ E - E`. -/
theorem ppl060_steinhaus_difference_set
    {E : Set ℝ} (hE : MeasurableSet E) (hpos : 0 < volume E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, |d| < δ → ∃ x ∈ E, ∃ y ∈ E, x - y = d := by
  obtain ⟨δ, hδ_pos, hsmall⟩ := ppl060_steinhaus_small_scales hE hpos ({0, 1} : Finset ℝ)
  refine ⟨δ, hδ_pos, fun d hd => ?_⟩
  have hcond : ∀ y ∈ ({0, 1} : Finset ℝ), |d * y| < δ := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · simpa using hδ_pos
    · simpa using hd
  obtain ⟨b, hbE, hsub⟩ := hsmall d hcond
  have hdb : d + b ∈ E := by
    have hmem : d * 1 + b ∈ (fun y : ℝ => d * y + b) '' (({0, 1} : Finset ℝ) : Set ℝ) :=
      ⟨1, by simp, rfl⟩
    simpa using hsub hmem
  exact ⟨d + b, hdb, b, hbE, by ring⟩

/-! ### Section 2: Unbounded-Set Non-Universality & Structural Reductions -/

/-- Monotonicity of affine avoidance: if `A ⊆ B` and `E` avoids all affine copies of `A`,
then `E` avoids all affine copies of `B`. -/
theorem ppl060_affine_avoidance_monotone
    {A B E : Set ℝ} (hAB : A ⊆ B)
    (hAvoid : ∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' A ⊆ E)) :
    ∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' B ⊆ E) := by
  intro a b ha hsub
  exact hAvoid a b ha ((Set.image_mono hAB).trans hsub)

/-- Affine invariance of avoidance: if `A' = (fun x => c * x + d) '' A` with `c ≠ 0`,
then `E` avoids all affine copies of `A` iff `E` avoids all affine copies of `A'`. -/
theorem ppl060_affine_avoidance_of_affine_equiv
    {A E : Set ℝ} {c d : ℝ} (hc : c ≠ 0) :
    (∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' A ⊆ E)) ↔
    (∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' ((fun x : ℝ => c * x + d) '' A) ⊆ E)) := by
  constructor
  · intro hA a b ha hsub
    apply hA (a * c) (a * d + b) (mul_ne_zero ha hc)
    rintro _ ⟨x, hxA, rfl⟩
    apply hsub
    refine ⟨c * x + d, ⟨x, hxA, rfl⟩, ?_⟩
    ring
  · intro hA' a b ha hsub
    apply hA' (a / c) (b - a * d / c) (div_ne_zero ha hc)
    rintro _ ⟨_, ⟨x, hxA, rfl⟩, rfl⟩
    apply hsub
    refine ⟨x, hxA, ?_⟩
    field_simp
    ring

/-- **Unbounded-Set Non-Universality**: Every unbounded set `A ⊆ ℝ` is avoided by
`E = Set.Icc (0 : ℝ) 1`, which is compact, measurable, and has `volume E = 1 > 0`. -/
theorem ppl060_unbounded_nonuniversal
    {A : Set ℝ} (hUnb : ¬ Bornology.IsBounded A) :
    MeasurableSet (Set.Icc (0 : ℝ) 1) ∧
    0 < volume (Set.Icc (0 : ℝ) 1) ∧
    ∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' A ⊆ Set.Icc (0 : ℝ) 1) := by
  refine ⟨measurableSet_Icc, ?_, ?_⟩
  · rw [Real.volume_Icc]
    norm_num
  · intro a b ha hsub
    apply hUnb
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨(1 + |b|) / |a|, fun x hxA => ?_⟩
    have hx_in : a * x + b ∈ Set.Icc (0 : ℝ) 1 := hsub ⟨x, hxA, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    have haxb : |a * x + b| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hx_in.1], hx_in.2⟩
    have hax : |a| * |x| ≤ 1 + |b| := by
      rw [← abs_mul]
      have h1 : |a * x| = |(a * x + b) - b| := by ring_nf
      rw [h1]
      linarith [abs_sub (a * x + b) b]
    have ha_pos : 0 < |a| := abs_pos.mpr ha
    exact (le_div_iff₀ ha_pos).mpr (by linarith)

/-- **Bolzano–Weierstrass Reduction to Strictly Decreasing Positive Null Sequences**:
Every bounded infinite set `A ⊆ ℝ` admits an affine copy `(fun x => c * x + d) '' A` (`c ≠ 0`)
containing the range of a strictly decreasing positive sequence `u : ℕ → ℝ` with `u n → 0`. -/
theorem ppl060_reduction_to_monotone_null_seq
    {A : Set ℝ} (hInf : A.Infinite) (hBdd : Bornology.IsBounded A) :
    ∃ (c d : ℝ) (u : ℕ → ℝ),
      c ≠ 0 ∧
      (∀ n, 0 < u n) ∧
      StrictAnti u ∧
      Tendsto u atTop (nhds 0) ∧
      Set.range u ⊆ (fun x : ℝ => c * x + d) '' A := by
  obtain ⟨R, hAR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℝ) |>.mp hBdd
  have hcomp : IsCompact (Metric.closedBall (0 : ℝ) R) := isCompact_closedBall 0 R
  have : Infinite A := hInf.to_subtype
  let g : ℕ ↪ A := Infinite.natEmbedding A
  let f : ℕ → ℝ := fun n => (g n).1
  have hfA : ∀ n, f n ∈ A := fun n => (g n).2
  have hf_inj : Function.Injective f := fun i j hij =>
    g.injective (Subtype.ext hij)
  obtain ⟨x₀, _, φ, hφ_mono, hφ_tend⟩ := hcomp.tendsto_subseq (fun n => hAR (hfA n))
  have hnear : ∀ r : ℝ, 0 < r → ∃ y ∈ A, y ≠ x₀ ∧ |y - x₀| < r := by
    intro r hr
    rw [Metric.tendsto_atTop] at hφ_tend
    obtain ⟨N, hN⟩ := hφ_tend r hr
    by_cases h0 : f (φ N) = x₀
    · refine ⟨f (φ (N + 1)), hfA _, ?_, ?_⟩
      · intro heq
        have := hf_inj (heq.trans h0.symm)
        have := hφ_mono.injective this
        omega
      · simpa [Real.dist_eq] using hN (N + 1) (Nat.le_succ N)
    · exact ⟨f (φ N), hfA _, h0, by simpa [Real.dist_eq] using hN N le_rfl⟩
  have hside :
      (∀ r : ℝ, 0 < r → ∃ y ∈ A, x₀ < y ∧ y - x₀ < r) ∨
      (∀ r : ℝ, 0 < r → ∃ y ∈ A, y < x₀ ∧ x₀ - y < r) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨r₁, hr₁, hno₁⟩, ⟨r₂, hr₂, hno₂⟩⟩ := hboth
    obtain ⟨y, hyA, hyne, hylt⟩ := hnear (min r₁ r₂) (lt_min hr₁ hr₂)
    rcases lt_or_gt_of_ne hyne with hlt | hgt
    · have h1 : x₀ - y < r₂ := by
        have := lt_of_lt_of_le hylt (min_le_right r₁ r₂)
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)] at this
        exact this
      linarith [hno₂ y hyA hlt]
    · have h1 : y - x₀ < r₁ := by
        have := lt_of_lt_of_le hylt (min_le_left r₁ r₂)
        rw [abs_of_pos (sub_pos.mpr hgt)] at this
        exact this
      linarith [hno₁ y hyA hgt]
  have hbuild : ∀ B : Set ℝ, (∀ r : ℝ, 0 < r → ∃ z ∈ B, 0 < z ∧ z < r) →
      ∃ u : ℕ → ℝ, (∀ n, 0 < u n) ∧ StrictAnti u ∧ Tendsto u atTop (nhds 0) ∧ Set.range u ⊆ B := by
    intro B hB
    choose fB hfB hfpos hflt using hB
    let step : ℕ → {x : ℝ // x ∈ B ∧ 0 < x} → {x : ℝ // x ∈ B ∧ 0 < x} :=
      fun n prev =>
        let r := min prev.1 (1 / ((n : ℝ) + 2))
        have hr : 0 < r := lt_min prev.2.2 (by positivity)
        ⟨fB r hr, hfB r hr, hfpos r hr⟩
    let v : ℕ → {x : ℝ // x ∈ B ∧ 0 < x} :=
      Nat.rec ⟨fB 1 one_pos, hfB 1 one_pos, hfpos 1 one_pos⟩ step
    refine ⟨fun n => (v n).1, fun n => (v n).2.2, ?_, ?_, ?_⟩
    · refine strictAnti_nat_of_succ_lt fun n => ?_
      change (step n (v n)).1 < (v n).1
      exact lt_of_lt_of_le (hflt _ _) (min_le_left _ _)
    · refine squeeze_zero (fun n => (v n).2.2.le) (f := fun n => (v n).1)
        (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ?_ ?_
      · intro n
        cases n with
        | zero =>
          have := hflt 1 one_pos
          simpa [v] using this.le
        | succ m =>
          have hlt' : (step m (v m)).1 < min (v m).1 (1 / ((m : ℝ) + 2)) := hflt _ _
          have hle' : (v (m + 1)).1 ≤ 1 / ((m : ℝ) + 2) := (lt_of_lt_of_le hlt' (min_le_right _ _)).le
          convert hle' using 2
          push_cast; ring
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · rintro _ ⟨n, rfl⟩
      exact (v n).2.1
  rcases hside with hright | hleft
  · obtain ⟨u, hupos, huanti, huzero, hurange⟩ :=
      hbuild ((fun x : ℝ => 1 * x + (-x₀)) '' A) (fun r hr => by
        obtain ⟨y, hyA, hgt, hlt⟩ := hright r hr
        exact ⟨1 * y + (-x₀), ⟨y, hyA, rfl⟩, by linarith, by linarith⟩)
    exact ⟨1, -x₀, u, one_ne_zero, hupos, huanti, huzero, hurange⟩
  · obtain ⟨u, hupos, huanti, huzero, hurange⟩ :=
      hbuild ((fun x : ℝ => (-1) * x + x₀) '' A) (fun r hr => by
        obtain ⟨y, hyA, hlt, hsub⟩ := hleft r hr
        exact ⟨(-1) * y + x₀, ⟨y, hyA, rfl⟩, by linarith, by linarith⟩)
    exact ⟨-1, x₀, u, by norm_num, hupos, huanti, huzero, hurange⟩

/-- **Exact Equivalence of Erdős Problem #120 with Positive Strictly Decreasing Null Sequences**:
The full Erdős Similarity Conjecture holds for all infinite sets `A ⊆ ℝ` if and only if
it holds for the range of every strictly decreasing positive sequence `u : ℕ → ℝ` tending to `0`. -/
theorem ppl060_conjecture_equiv_null_seq :
    (∀ A : Set ℝ, A.Infinite →
      ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧
        ∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' A ⊆ E)) ↔
    (∀ u : ℕ → ℝ, (∀ n, 0 < u n) → StrictAnti u → Tendsto u atTop (nhds 0) →
      ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧
        ∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' Set.range u ⊆ E)) := by
  constructor
  · intro hAll u _ huanti _
    exact hAll (Set.range u) (Set.infinite_range_of_injective huanti.injective)
  · intro hSeq A hInf
    by_cases hBdd : Bornology.IsBounded A
    · obtain ⟨c, d, u, hc, hupos, huanti, huzero, hsub⟩ :=
        ppl060_reduction_to_monotone_null_seq hInf hBdd
      obtain ⟨E, hEmeas, hEpos, hEavoid⟩ := hSeq u hupos huanti huzero
      refine ⟨E, hEmeas, hEpos, ?_⟩
      exact (ppl060_affine_avoidance_of_affine_equiv hc).mpr
        (ppl060_affine_avoidance_monotone hsub hEavoid)
    · obtain ⟨hmeas, hpos, havoid⟩ := ppl060_unbounded_nonuniversal hBdd
      exact ⟨Set.Icc (0 : ℝ) 1, hmeas, hpos, havoid⟩

/-! ### Section 3: Falconer (1984) / Eigen (1985) Slow-Decay Non-Universality Theorem -/

/-- Helper: removing an open set `U` with `volume U ≤ ENNReal.ofReal ε` (`0 < ε < 1`) from
`[0, 1]` yields a compact, measurable subset `E ⊆ [0, 1]` with `ENNReal.ofReal (1 - ε) ≤ volume E`. -/
private lemma compact_sdiff_open_measure_ge {U : Set ℝ} {ε : ℝ}
    (hUopen : IsOpen U) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hUmeas : volume U ≤ ENNReal.ofReal ε) :
    let E : Set ℝ := Set.Icc (0 : ℝ) 1 \ U
    E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E := by
  intro E
  have hsub : E ⊆ Set.Icc (0 : ℝ) 1 := Set.sdiff_subset
  have hcomp : IsCompact E := isCompact_Icc.diff hUopen
  have hmeas : MeasurableSet E := hcomp.measurableSet
  have hvol : ENNReal.ofReal (1 - ε) ≤ volume E := by
    have hcov : Set.Icc (0 : ℝ) 1 ⊆ E ∪ U := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inr hxU
      · exact Or.inl ⟨hx, hxU⟩
    have h1 : ENNReal.ofReal 1 ≤ volume E + ENNReal.ofReal ε := by
      calc ENNReal.ofReal 1
          = volume (Set.Icc (0 : ℝ) 1) := by rw [Real.volume_Icc]; norm_num
        _ ≤ volume (E ∪ U) := measure_mono hcov
        _ ≤ volume E + volume U := measure_union_le E U
        _ ≤ volume E + ENNReal.ofReal ε := add_le_add le_rfl hUmeas
    have hsum : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = ENNReal.ofReal 1 := by
      rw [← ENNReal.ofReal_add (by linarith) hε_pos.le]
      ring_nf
    rw [← hsum] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1
  exact ⟨hsub, hcomp, hmeas, hvol⟩

/-- Helper: the periodic grid of `N` open intervals `(m/N, (m+r)/N)` (`m < N`) is open and has
Lebesgue measure at most `ENNReal.ofReal r`. -/
private lemma periodic_holes_open_and_measure (N : ℕ) (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    let U : Set ℝ := ⋃ m ∈ Finset.range N, Set.Ioo ((m : ℝ) / N) ((m : ℝ) / N + r / N)
    IsOpen U ∧ volume U ≤ ENNReal.ofReal r := by
  intro U
  refine ⟨isOpen_biUnion fun _ _ => isOpen_Ioo, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc volume U
      ≤ ∑ m ∈ Finset.range N, volume (Set.Ioo ((m : ℝ) / N) ((m : ℝ) / N + r / N)) :=
        measure_biUnion_finset_le (Finset.range N) _
    _ = ∑ _m ∈ Finset.range N, ENNReal.ofReal (r / N) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = (N : ENNReal) * ENNReal.ofReal (r / N) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (r / N) := by
        rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((N : ℝ) * (r / N)) := by
        rw [← ENNReal.ofReal_mul hNpos.le]
    _ = ENNReal.ofReal r := by
        congr 1
        field_simp

/-- Helper: `∑' k : ℕ, ENNReal.ofReal (ε / 2^(k+1)) = ENNReal.ofReal ε` for `ε ≥ 0`. -/
private lemma tsum_ofReal_eps_div_two_pow {ε : ℝ} (hε : 0 ≤ ε) :
    (∑' k : ℕ, ENNReal.ofReal (ε / (2 : ℝ) ^ (k + 1))) = ENNReal.ofReal ε := by
  have hgeom : HasSum (fun k : ℕ => ε / (2 : ℝ) ^ (k + 1)) ε := by
    have hbase : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) (1 - 1 / 2)⁻¹ :=
      hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
    have hmul := hbase.mul_left (ε / 2)
    have hsimp : (ε / 2) * (1 - 1 / 2 : ℝ)⁻¹ = ε := by ring
    rw [hsimp] at hmul
    refine hmul.congr_fun fun k => ?_
    rw [pow_succ, one_div, inv_pow]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom.summable, hgeom.tsum_eq]

/-- **Falconer (1984) / Eigen (1985) Slow-Decay Non-Universality Theorem**:
For every positive null sequence `u : ℕ → ℝ` satisfying `u (n + 1) / u n → 1` (with NO
monotonicity assumed) and every `ε ∈ (0, 1)`, there exists a compact, measurable subset
`E ⊆ [0, 1]` with `ENNReal.ofReal (1 - ε) ≤ volume E` (hence `0 < volume E`) that contains
no affine copy `(fun x => a * x + b) '' Set.range u` for any `a ≠ 0` and `b : ℝ`. -/
theorem ppl060_falconer_eigen_slow_decay
    {u : ℕ → ℝ} (hu_pos : ∀ n, 0 < u n)
    (hu_zero : Tendsto u atTop (nhds 0))
    (hu_ratio : Tendsto (fun n => u (n + 1) / u n) atTop (nhds 1))
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ a b : ℝ, a ≠ 0 → ¬ ((fun x : ℝ => a * x + b) '' Set.range u ⊆ E) := by
  let r : ℕ → ℝ := fun k => ε / (2 : ℝ) ^ (k + 1)
  have hr_pos : ∀ k, 0 < r k := fun k => by dsimp [r]; positivity
  have hr_lt_half : ∀ k, r k < 1 / 2 := fun k => by
    dsimp [r]
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))
      simpa using this
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hM_exists : ∀ k : ℕ, ∃ M : ℕ, ∀ n ≥ M, |u (n + 1) / u n - 1| < r k / 4 := by
    intro k
    rw [Metric.tendsto_atTop] at hu_ratio
    obtain ⟨M, hM⟩ := hu_ratio (r k / 4) (by linarith [hr_pos k])
    exact ⟨M, fun n hn => by simpa [Real.dist_eq] using hM n hn⟩
  choose M hM using hM_exists
  let N : ℕ → ℕ := fun k => Nat.ceil (2 * ((k : ℝ) + 1) / u (M k)) + 1
  have hN_pos : ∀ k, 0 < N k := fun k => Nat.succ_pos _
  have hN_bound : ∀ k, 2 / (N k : ℝ) ≤ u (M k) / ((k : ℝ) + 1) := by
    intro k
    have hNreal : 2 * ((k : ℝ) + 1) / u (M k) ≤ (N k : ℝ) := by
      dsimp only [N]
      push_cast
      linarith [Nat.le_ceil (2 * ((k : ℝ) + 1) / u (M k))]
    have huM : 0 < u (M k) := hu_pos (M k)
    have hNposR : (0 : ℝ) < (N k : ℝ) := by exact_mod_cast hN_pos k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ hNposR hk1]
    have hmul := (div_le_iff₀ huM).mp hNreal
    linarith
  let U_lvl : ℕ → Set ℝ := fun k =>
    ⋃ m ∈ Finset.range (N k), Set.Ioo ((m : ℝ) / N k) ((m : ℝ) / N k + r k / N k)
  let U : Set ℝ := ⋃ k : ℕ, U_lvl k
  have hUopen : IsOpen U :=
    isOpen_iUnion fun k => (periodic_holes_open_and_measure (N k) (hN_pos k) (hr_pos k)).1
  have hUmeas : volume U ≤ ENNReal.ofReal ε := by
    calc volume U
        ≤ ∑' k : ℕ, volume (U_lvl k) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (r k) :=
          ENNReal.tsum_le_tsum fun k =>
            (periodic_holes_open_and_measure (N k) (hN_pos k) (hr_pos k)).2
      _ = ENNReal.ofReal ε := tsum_ofReal_eps_div_two_pow hε_pos.le
  obtain ⟨hEsub, hEcomp, hEmeas, hEvol⟩ :=
    compact_sdiff_open_measure_ge hUopen hε_pos hε_lt hUmeas
  refine ⟨Set.Icc (0 : ℝ) 1 \ U, hEsub, hEcomp, hEmeas, hEvol, ?_⟩
  intro a b ha hsub
  let y : ℕ → ℝ := fun n => a * u n + b
  have hyE : ∀ n, y n ∈ Set.Icc (0 : ℝ) 1 \ U := fun n => hsub ⟨u n, ⟨n, rfl⟩, rfl⟩
  have hyIcc : ∀ n, y n ∈ Set.Icc (0 : ℝ) 1 := fun n => (hyE n).1
  have hyNotU : ∀ n, y n ∉ U := fun n => (hyE n).2
  have hy_tend : Tendsto y atTop (nhds b) := by
    have h1 : Tendsto (fun n => a * u n + b) atTop (nhds (a * 0 + b)) :=
      (hu_zero.const_mul a).add_const b
    simpa [y] using h1
  have hbIcc : b ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hy_tend (Eventually.of_forall hyIcc)
  -- Choose level `k` so `1 / (k + 1) ≤ |a|`, ensuring `2 / N k ≤ |a| * u (M k)`.
  have ha_pos : 0 < |a| := abs_pos.mpr ha
  let k : ℕ := Nat.ceil (1 / |a|)
  have hk_le : 1 / ((k : ℝ) + 1) ≤ |a| := by
    have hceil : 1 / |a| ≤ (k : ℝ) := Nat.le_ceil (1 / |a|)
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hk1]
    have h1 : 1 ≤ (k : ℝ) * |a| := (div_le_iff₀ ha_pos).mp hceil
    linarith
  have hNposR : (0 : ℝ) < (N k : ℝ) := by exact_mod_cast hN_pos k
  have hstart : 2 / (N k : ℝ) ≤ |a| * u (M k) := by
    calc 2 / (N k : ℝ)
        ≤ u (M k) / ((k : ℝ) + 1) := hN_bound k
      _ = (1 / ((k : ℝ) + 1)) * u (M k) := by ring
      _ ≤ |a| * u (M k) := mul_le_mul_of_nonneg_right hk_le (hu_pos (M k)).le
  -- Find the LAST index `n₁ ≥ M k` such that `2 / N k ≤ |a| * u n₁`.
  have hau_tend : Tendsto (fun n => |a| * u n) atTop (nhds 0) := by
    simpa using hu_zero.const_mul |a|
  rw [Metric.tendsto_atTop] at hau_tend
  obtain ⟨L0, hL0⟩ := hau_tend (2 / (N k : ℝ)) (by positivity)
  let L : ℕ := max (M k) L0
  have hgtL : ∀ n ≥ L, |a| * u n < 2 / (N k : ℝ) := by
    intro n hn
    have hdist := hL0 n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos ha_pos (hu_pos n))] at hdist
    exact hdist
  let S : Finset ℕ := (Finset.Icc (M k) L).filter (fun n => 2 / (N k : ℝ) ≤ |a| * u n)
  have hMkS : M k ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, le_max_left _ _⟩, hstart⟩
  let n₁ : ℕ := S.max' ⟨M k, hMkS⟩
  have hn₁S : n₁ ∈ S := Finset.max'_mem S ⟨M k, hMkS⟩
  have hn₁_ge_M : M k ≤ n₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn₁S).1).1
  have hn₁_ge : 2 / (N k : ℝ) ≤ |a| * u n₁ := (Finset.mem_filter.mp hn₁S).2
  have hgt_n₁ : ∀ n, n₁ < n → |a| * u n < 2 / (N k : ℝ) := by
    intro n hn
    by_cases hleL : n ≤ L
    · by_contra hge
      push Not at hge
      have hnS : n ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_trans hn₁_ge_M hn.le, hleL⟩, hge⟩
      exact hn.not_ge (Finset.le_max' S n hnS)
    · exact hgtL n (Nat.le_of_not_le hleL)
  -- Bound `|a| * u n₁ < (8/3) / N k`, hence all steps `|y (n+1) - y n| < r k / N k` for `n ≥ n₁`.
  have hratio_n₁ : |u (n₁ + 1) / u n₁ - 1| < r k / 4 := hM k n₁ hn₁_ge_M
  have hratio_gt : (3 / 4 : ℝ) < u (n₁ + 1) / u n₁ := by
    have h1 := (abs_lt.mp hratio_n₁).1
    linarith [hr_lt_half k]
  have hu_n₁_lt : |a| * u n₁ < (8 / 3 : ℝ) / (N k : ℝ) := by
    have hnext : |a| * u (n₁ + 1) < 2 / (N k : ℝ) := hgt_n₁ (n₁ + 1) (Nat.lt_succ_self n₁)
    have h34 : (3 / 4 : ℝ) * u n₁ < u (n₁ + 1) := (lt_div_iff₀ (hu_pos n₁)).mp hratio_gt
    have h34a : (3 / 4 : ℝ) * (|a| * u n₁) < |a| * u (n₁ + 1) := by
      have := mul_lt_mul_of_pos_left h34 ha_pos
      linarith
    have h83 : (8 / 3 : ℝ) / (N k : ℝ) = (4 / 3 : ℝ) * (2 / (N k : ℝ)) := by ring
    linarith
  have hstep : ∀ n ≥ n₁, |y (n + 1) - y n| < r k / (N k : ℝ) := by
    intro n hn
    have hrat : |u (n + 1) / u n - 1| < r k / 4 := hM k n (le_trans hn₁_ge_M hn)
    have hdiff_u : |u (n + 1) - u n| < (r k / 4) * u n := by
      have hu_n : 0 < u n := hu_pos n
      have hrewrite : u (n + 1) / u n - 1 = (u (n + 1) - u n) / u n := by field_simp
      rw [hrewrite, abs_div, abs_of_pos hu_n] at hrat
      exact (div_lt_iff₀ hu_n).mp hrat
    have haun : |a| * u n < (8 / 3 : ℝ) / (N k : ℝ) := by
      rcases eq_or_lt_of_le hn with rfl | hlt
      · exact hu_n₁_lt
      · have hlt2 := hgt_n₁ n hlt
        have hposN : (0 : ℝ) < 1 / (N k : ℝ) := by positivity
        have h83 : (8 / 3 : ℝ) / (N k : ℝ) = (4 / 3 : ℝ) * (2 / (N k : ℝ)) := by ring
        have h2pos : (0 : ℝ) < 2 / (N k : ℝ) := by positivity
        linarith
    have hy_diff : |y (n + 1) - y n| = |a| * |u (n + 1) - u n| := by
      dsimp only [y]
      rw [show (a * u (n + 1) + b) - (a * u n + b) = a * (u (n + 1) - u n) by ring, abs_mul]
    rw [hy_diff]
    calc |a| * |u (n + 1) - u n|
        < |a| * ((r k / 4) * u n) := mul_lt_mul_of_pos_left hdiff_u ha_pos
      _ = (r k / 4) * (|a| * u n) := by ring
      _ < (r k / 4) * ((8 / 3 : ℝ) / (N k : ℝ)) :=
          mul_lt_mul_of_pos_left haun (by linarith [hr_pos k])
      _ < r k / (N k : ℝ) := by
          have hrN : 0 < r k / (N k : ℝ) := div_pos (hr_pos k) hNposR
          have h23 : (r k / 4) * ((8 / 3 : ℝ) / (N k : ℝ)) = (2 / 3 : ℝ) * (r k / (N k : ℝ)) := by
            ring
          linarith
  -- Locate a full hole `Ioo L_h R_h ⊆ U_lvl k` strictly between `b` and `y n₁`.
  let p : ℝ := min b (y n₁)
  let q : ℝ := max b (y n₁)
  have hp0 : 0 ≤ p := le_min hbIcc.1 (hyIcc n₁).1
  have hq1 : q ≤ 1 := max_le hbIcc.2 (hyIcc n₁).2
  have hqp : 2 / (N k : ℝ) ≤ q - p := by
    have hdiff : q - p = |y n₁ - b| := by
      dsimp only [p, q]
      rcases le_total b (y n₁) with hle | hle
      · rw [max_eq_right hle, min_eq_left hle, abs_of_nonneg (by linarith)]
      · rw [max_eq_left hle, min_eq_right hle, abs_of_nonpos (by linarith)]; ring
    rw [hdiff]
    have hyb : |y n₁ - b| = |a| * u n₁ := by
      dsimp only [y]
      rw [add_sub_cancel_right, abs_mul, abs_of_pos (hu_pos n₁)]
    rw [hyb]
    exact hn₁_ge
  let m : ℕ := Nat.floor (p * (N k : ℝ)) + 1
  have hm_gt : p < (m : ℝ) / (N k : ℝ) := by
    rw [lt_div_iff₀ hNposR]
    dsimp only [m]
    push_cast
    exact Nat.lt_floor_add_one (p * (N k : ℝ))
  have hm_succ_le : ((m : ℝ) + 1) / (N k : ℝ) ≤ q := by
    rw [div_le_iff₀ hNposR]
    dsimp only [m]
    push_cast
    have hfl : (Nat.floor (p * (N k : ℝ)) : ℝ) ≤ p * (N k : ℝ) :=
      Nat.floor_le (mul_nonneg hp0 hNposR.le)
    have hqp' : 2 ≤ (q - p) * (N k : ℝ) := (div_le_iff₀ hNposR).mp hqp
    linarith
  have hm_lt_N : m < N k := by
    have h1 : ((m : ℝ) + 1) / (N k : ℝ) ≤ 1 := le_trans hm_succ_le hq1
    have h2 : (m : ℝ) + 1 ≤ (N k : ℝ) := (div_le_one hNposR).mp h1
    have h3 : m + 1 ≤ N k := by exact_mod_cast h2
    omega
  let Lh : ℝ := (m : ℝ) / (N k : ℝ)
  let Rh : ℝ := Lh + r k / (N k : ℝ)
  have hLh_lt_Rh : Lh < Rh := by
    dsimp only [Rh]
    linarith [div_pos (hr_pos k) hNposR]
  have hRh_lt_q : Rh < q := by
    have hr1 : r k < 1 := lt_trans (hr_lt_half k) (by norm_num)
    have h1 : Rh < ((m : ℝ) + 1) / (N k : ℝ) := by
      dsimp only [Rh, Lh]
      have : r k / (N k : ℝ) < 1 / (N k : ℝ) := div_lt_div_of_pos_right hr1 hNposR
      linarith [add_div (m : ℝ) 1 (N k : ℝ)]
    exact lt_of_lt_of_le h1 hm_succ_le
  have hhole_sub : Set.Ioo Lh Rh ⊆ U := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr hm_lt_N, hx⟩⟩
  -- Traverse from `y n₁` to `b` with steps `< Rh - Lh`, forcing some `y j ∈ Ioo Lh Rh ⊆ U`.
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos'
  · -- Case `a < 0`: `y n₁ < b`, so `p = y n₁ < Lh < Rh < b = q`.
    have hyn1_lt_b : y n₁ < b := by
      dsimp only [y]
      nlinarith [hu_pos n₁]
    have hp_eq : p = y n₁ := min_eq_right hyn1_lt_b.le
    have hq_eq : q = b := max_eq_left hyn1_lt_b.le
    have hyn1_lt_Lh : y n₁ < Lh := hp_eq ▸ hm_gt
    have hRh_lt_b : Rh < b := hq_eq ▸ hRh_lt_q
    have hex : ∃ d : ℕ, Lh < y (n₁ + d) := by
      have hev := (tendsto_order.mp hy_tend).1 Lh (lt_trans hLh_lt_Rh hRh_lt_b)
      rw [eventually_atTop] at hev
      obtain ⟨N0, hN0⟩ := hev
      exact ⟨N0, hN0 (n₁ + N0) (Nat.le_add_left N0 n₁)⟩
    classical
    let d₀ : ℕ := Nat.find hex
    have hd₀_spec : Lh < y (n₁ + d₀) := Nat.find_spec hex
    have hd₀_pos : 0 < d₀ := by
      by_contra h0
      have hd0 : d₀ = 0 := Nat.eq_zero_of_not_pos h0
      rw [hd0, add_zero] at hd₀_spec
      linarith
    let d : ℕ := d₀ - 1
    have hd_succ : d + 1 = d₀ := Nat.sub_add_cancel hd₀_pos
    have hprev_le : y (n₁ + d) ≤ Lh := by
      have hnot := Nat.find_min hex (m := d) (by omega)
      linarith
    have hstep_d := hstep (n₁ + d) (Nat.le_add_right n₁ d)
    have hlt_Rh : y (n₁ + d₀) < Rh := by
      have h1 : y (n₁ + d + 1) - y (n₁ + d) < r k / (N k : ℝ) :=
        lt_of_le_of_lt (le_abs_self _) hstep_d
      rw [show n₁ + d₀ = n₁ + d + 1 by omega]
      dsimp only [Rh]
      linarith
    exact hyNotU (n₁ + d₀) (hhole_sub ⟨hd₀_spec, hlt_Rh⟩)
  · -- Case `a > 0`: `b < y n₁`, so `p = b < Lh < Rh < y n₁ = q`.
    have hb_lt_yn1 : b < y n₁ := by
      dsimp only [y]
      nlinarith [hu_pos n₁]
    have hp_eq : p = b := min_eq_left hb_lt_yn1.le
    have hq_eq : q = y n₁ := max_eq_right hb_lt_yn1.le
    have hb_lt_Lh : b < Lh := hp_eq ▸ hm_gt
    have hRh_lt_yn1 : Rh < y n₁ := hq_eq ▸ hRh_lt_q
    have hex : ∃ d : ℕ, y (n₁ + d) < Rh := by
      have hev := (tendsto_order.mp hy_tend).2 Rh (lt_trans hb_lt_Lh hLh_lt_Rh)
      rw [eventually_atTop] at hev
      obtain ⟨N0, hN0⟩ := hev
      exact ⟨N0, hN0 (n₁ + N0) (Nat.le_add_left N0 n₁)⟩
    classical
    let d₀ : ℕ := Nat.find hex
    have hd₀_spec : y (n₁ + d₀) < Rh := Nat.find_spec hex
    have hd₀_pos : 0 < d₀ := by
      by_contra h0
      have hd0 : d₀ = 0 := Nat.eq_zero_of_not_pos h0
      rw [hd0, add_zero] at hd₀_spec
      linarith
    let d : ℕ := d₀ - 1
    have hd_succ : d + 1 = d₀ := Nat.sub_add_cancel hd₀_pos
    have hprev_ge : Rh ≤ y (n₁ + d) := by
      have hnot := Nat.find_min hex (m := d) (by omega)
      linarith
    have hstep_d := hstep (n₁ + d) (Nat.le_add_right n₁ d)
    have hgt_Lh : Lh < y (n₁ + d₀) := by
      have h1 : y (n₁ + d) - y (n₁ + d + 1) < r k / (N k : ℝ) := by
        have h2 := neg_le_abs (y (n₁ + d + 1) - y (n₁ + d))
        linarith
      rw [show n₁ + d₀ = n₁ + d + 1 by omega]
      dsimp only [Rh] at hprev_ge ⊢
      linarith
    exact hyNotU (n₁ + d₀) (hhole_sub ⟨hgt_Lh, hd₀_spec⟩)

/-- **Harmonic Sequence `{1 / (n + 1)}` Non-Universality**: For every `ε ∈ (0, 1)`, there exists
a compact `E ⊆ [0, 1]` with `volume E ≥ 1 - ε` avoiding all affine copies of `{1 / (n + 1)}`. -/
theorem ppl060_harmonic_nonuniversal {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ a b : ℝ, a ≠ 0 →
        ¬ ((fun x : ℝ => a * x + b) '' Set.range (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ⊆ E) := by
  refine ppl060_falconer_eigen_slow_decay (u := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat ?_ hε_pos hε_lt
  have hshift : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => by
      dsimp only [Function.comp_apply]; push_cast; ring
  have h1 : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hshift
  rw [sub_zero] at h1
  refine h1.congr fun n => ?_
  push_cast
  field_simp
  ring

/-- **Power-Law Sequence `{1 / (n + 1)^α}` (`α > 0`) Non-Universality**: For every `α > 0` and
`ε ∈ (0, 1)`, there exists a compact `E ⊆ [0, 1]` with `volume E ≥ 1 - ε` avoiding all affine
copies of `{1 / (n + 1)^α}`. -/
theorem ppl060_power_decay_nonuniversal {α : ℝ} (hα : 0 < α)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ a b : ℝ, a ≠ 0 →
        ¬ ((fun x : ℝ => a * x + b) ''
            Set.range (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ α) ⊆ E) := by
  refine ppl060_falconer_eigen_slow_decay
    (u := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ α)
    (fun n => by positivity) ?_ ?_ hε_pos hε_lt
  · have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp hnat
    exact (tendsto_inv_atTop_zero.comp hpow).congr fun n => by
      dsimp only [Function.comp_apply]; rw [one_div]
  · have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (nhds 1) := by
      have hshift : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => by
          dsimp only [Function.comp_apply]; push_cast; ring
      have h1 : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hshift
      rw [sub_zero] at h1
      refine h1.congr fun n => ?_
      field_simp
      ring
    have hlim : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ α) atTop (nhds ((1 : ℝ) ^ α)) :=
      hbase.rpow_const (Or.inl one_ne_zero)
    rw [Real.one_rpow] at hlim
    refine hlim.congr fun n => ?_
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [Real.div_rpow h1.le h2.le]
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    field_simp

/-- **Logarithmic-Decay Sequence `{1 / log (n + 2)}` Non-Universality**: For every `ε ∈ (0, 1)`,
there exists a compact `E ⊆ [0, 1]` with `volume E ≥ 1 - ε` avoiding all affine copies of
`{1 / Real.log (n + 2)}`. -/
theorem ppl060_log_decay_nonuniversal {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ a b : ℝ, a ≠ 0 →
        ¬ ((fun x : ℝ => a * x + b) ''
            Set.range (fun n : ℕ => (1 : ℝ) / Real.log ((n : ℝ) + 2)) ⊆ E) := by
  have hlog_pos : ∀ n : ℕ, 0 < Real.log ((n : ℝ) + 2) := fun n =>
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlog_top : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv_zero : Tendsto (fun n : ℕ => (1 : ℝ) / Real.log ((n : ℝ) + 2)) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp hlog_top).congr fun n => by
      dsimp only [Function.comp_apply]; rw [one_div]
  refine ppl060_falconer_eigen_slow_decay
    (u := fun n : ℕ => (1 : ℝ) / Real.log ((n : ℝ) + 2))
    (fun n => div_pos one_pos (hlog_pos n)) hinv_zero ?_ hε_pos hε_lt
  have hlow : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / Real.log ((n : ℝ) + 2)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro n
    dsimp only
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    have hlog2 : 0 < Real.log ((n : ℝ) + 2) := hlog_pos n
    have hlog3 : 0 < Real.log ((n : ℝ) + 3) :=
      Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hadd : Real.log ((n : ℝ) + 3) =
        Real.log ((n : ℝ) + 2) + Real.log (((n : ℝ) + 3) / ((n : ℝ) + 2)) := by
      rw [← Real.log_mul h2.ne' (div_pos h3 h2).ne']
      congr 1; field_simp
    have hgap : Real.log (((n : ℝ) + 3) / ((n : ℝ) + 2)) ≤ 1 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos h3 h2)
      have h2' : ((n : ℝ) + 3) / ((n : ℝ) + 2) - 1 ≤ 1 := by
        rw [sub_le_iff_le_add, div_le_iff₀ h2]; linarith
      linarith
    have hrewrite :
        ((1 : ℝ) / Real.log ((↑(n + 1) : ℝ) + 2)) / ((1 : ℝ) / Real.log ((n : ℝ) + 2)) =
          Real.log ((n : ℝ) + 2) / Real.log ((n : ℝ) + 3) := by
      push_cast
      rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
      field_simp
    rw [hrewrite, sub_le_iff_le_add]
    have hle : Real.log ((n : ℝ) + 3) ≤ Real.log ((n : ℝ) + 2) + 1 := by linarith
    have hdiv : 1 ≤ Real.log ((n : ℝ) + 2) / Real.log ((n : ℝ) + 3) +
        1 / Real.log ((n : ℝ) + 3) := by
      rw [← add_div, one_le_div hlog3]
      exact hle
    have hmono : 1 / Real.log ((n : ℝ) + 3) ≤ 1 / Real.log ((n : ℝ) + 2) := by
      apply one_div_le_one_div_of_le hlog2
      exact Real.log_le_log h2 (by linarith)
    linarith
  · intro n
    dsimp only
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hlog3 : 0 < Real.log ((n : ℝ) + 3) :=
      Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hrewrite :
        ((1 : ℝ) / Real.log ((↑(n + 1) : ℝ) + 2)) / ((1 : ℝ) / Real.log ((n : ℝ) + 2)) =
          Real.log ((n : ℝ) + 2) / Real.log ((n : ℝ) + 3) := by
      push_cast
      rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
      field_simp
    rw [hrewrite, div_le_one hlog3]
    exact Real.log_le_log h2 (by linarith)

/-- **Subexponential Stretched-Decay Sequence `{exp (-n^β)}` (`0 < β < 1`) Non-Universality**:
For every `0 < β < 1` and `ε ∈ (0, 1)`, there exists a compact `E ⊆ [0, 1]` with
`volume E ≥ 1 - ε` avoiding all affine copies of `{Real.exp (-((n : ℝ) ^ β))}`. -/
theorem ppl060_subexponential_nonuniversal {β : ℝ} (hβ_pos : 0 < β) (hβ_lt : β < 1)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ a b : ℝ, a ≠ 0 →
        ¬ ((fun x : ℝ => a * x + b) ''
            Set.range (fun n : ℕ => Real.exp (-((n : ℝ) ^ β))) ⊆ E) := by
  refine ppl060_falconer_eigen_slow_decay
    (u := fun n : ℕ => Real.exp (-((n : ℝ) ^ β)))
    (fun n => Real.exp_pos _) ?_ ?_ hε_pos hε_lt
  · have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ β) atTop atTop :=
      (tendsto_rpow_atTop hβ_pos).comp tendsto_natCast_atTop_atTop
    have hneg : Tendsto (fun n : ℕ => -((n : ℝ) ^ β)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hpow
    exact Real.tendsto_exp_atBot.comp hneg
  · have hdiff_zero : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ β) - (n : ℝ) ^ β) atTop (nhds 0) := by
      have hupper : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop (nhds 0) :=
        ((tendsto_rpow_neg_atTop (show 0 < 1 - β by linarith)).comp
          tendsto_natCast_atTop_atTop).congr fun n => by
            dsimp only [Function.comp_apply]
            congr 1
            ring
      refine squeeze_zero' ?_ ?_ hupper
      · exact Eventually.of_forall fun n => by
          have hle : (n : ℝ) ^ β ≤ ((n + 1 : ℕ) : ℝ) ^ β :=
            Real.rpow_le_rpow (Nat.cast_nonneg n) (by push_cast; linarith) hβ_pos.le
          linarith
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hstep1 : ((n + 1 : ℕ) : ℝ) ^ β = (n : ℝ) ^ β * (1 + 1 / (n : ℝ)) ^ β := by
          rw [← Real.mul_rpow hn_pos.le (by positivity)]
          congr 1
          push_cast
          field_simp
        have hpow_le : (1 + 1 / (n : ℝ)) ^ β ≤ 1 + 1 / (n : ℝ) := by
          calc (1 + 1 / (n : ℝ)) ^ β
              ≤ (1 + 1 / (n : ℝ)) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [div_pos one_pos hn_pos]) hβ_lt.le
            _ = 1 + 1 / (n : ℝ) := Real.rpow_one _
        have hmul : ((n + 1 : ℕ) : ℝ) ^ β - (n : ℝ) ^ β ≤ (n : ℝ) ^ β * (1 / (n : ℝ)) := by
          rw [hstep1]
          nlinarith [Real.rpow_pos_of_pos hn_pos β]
        have heq : (n : ℝ) ^ β * (1 / (n : ℝ)) = (n : ℝ) ^ (β - 1) := by
          rw [one_div, ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn_pos, sub_eq_add_neg]
        linarith
    have hexp_lim : Tendsto (fun n : ℕ => Real.exp (-((((n + 1 : ℕ) : ℝ) ^ β) - (n : ℝ) ^ β)))
        atTop (nhds (Real.exp (-0))) :=
      (Real.continuous_exp.tendsto _).comp hdiff_zero.neg
    rw [neg_zero, Real.exp_zero] at hexp_lim
    refine hexp_lim.congr fun n => ?_
    rw [← Real.exp_sub]
    congr 1
    ring

/-! ### Section 4: Universal Translation & Countable-Scale Avoidance for Arbitrary Infinite Sets -/

/-- Exact Finset counting helper 1: for any `v : α` in a finite type `α` and `Q ≥ 1`,
`Q * |{f : α → Fin Q | f v = 0}| = |α → Fin Q|`. -/
private lemma card_filter_apply_eq_zero_mul {α : Type*} [Fintype α] [DecidableEq α]
    {Q : ℕ} (hQ : 0 < Q) (v : α) :
    (Finset.univ.filter (fun f : α → Fin Q => f v = ⟨0, hQ⟩)).card * Q =
      Fintype.card (α → Fin Q) := by
  classical
  let e : {f : α → Fin Q // f v = ⟨0, hQ⟩} × Fin Q ≃ (α → Fin Q) :=
    { toFun := fun p => Function.update p.1.1 v p.2
      invFun := fun g => (⟨Function.update g v ⟨0, hQ⟩, by simp⟩, g v)
      left_inv := by
        rintro ⟨⟨f, hf⟩, q⟩
        ext w
        · by_cases hw : w = v
          · subst hw; simp [hf]
          · simp [hw]
        · simp
      right_inv := by
        intro g
        funext w
        by_cases hw : w = v
        · subst hw; simp
        · simp [hw] }
  have hcard := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype] at hcard
  exact hcard

/-- Exact Finset counting helper 2: for any `T : Finset α` and `Q ≥ 1`,
`|{f : α → Fin Q | ∀ v ∈ T, f v ≠ 0}| * Q ^ T.card = (Q - 1) ^ T.card * |α → Fin Q|`. -/
private lemma card_filter_avoid_zero_mul {α : Type*} [Fintype α] [DecidableEq α]
    {Q : ℕ} (hQ : 0 < Q) (T : Finset α) :
    (Finset.univ.filter (fun f : α → Fin Q => ∀ v ∈ T, f v ≠ ⟨0, hQ⟩)).card * Q ^ T.card =
      (Q - 1) ^ T.card * Fintype.card (α → Fin Q) := by
  classical
  let e1 : {f : α → Fin Q // ∀ v ∈ T, f v ≠ ⟨0, hQ⟩} ≃
      ({v : α // v ∈ T} → {q : Fin Q // q ≠ ⟨0, hQ⟩}) × ({v : α // v ∉ T} → Fin Q) :=
    { toFun := fun f =>
        (fun v => ⟨f.1 v.1, f.2 v.1 v.2⟩, fun v => f.1 v.1)
      invFun := fun p =>
        ⟨fun v => if hv : v ∈ T then (p.1 ⟨v, hv⟩).1 else p.2 ⟨v, hv⟩,
         fun v hv => by simp [hv, (p.1 ⟨v, hv⟩).2]⟩
      left_inv := by
        rintro ⟨f, hf⟩
        ext v
        by_cases hv : v ∈ T <;> simp [hv]
      right_inv := by
        rintro ⟨g₁, g₂⟩
        ext v
        · simp [v.2]
        · simp [v.2] }
  let e2 : (α → Fin Q) ≃ ({v : α // v ∈ T} → Fin Q) × ({v : α // v ∉ T} → Fin Q) :=
    { toFun := fun f => (fun v => f v.1, fun v => f v.1)
      invFun := fun p v => if hv : v ∈ T then p.1 ⟨v, hv⟩ else p.2 ⟨v, hv⟩
      left_inv := by
        intro f; funext v; by_cases hv : v ∈ T <;> simp [hv]
      right_inv := by
        rintro ⟨g₁, g₂⟩
        ext v
        · simp [v.2]
        · simp [v.2] }
  have hc1 := Fintype.card_congr e1
  have hc2 := Fintype.card_congr e2
  rw [Fintype.card_subtype, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_coe, Fintype.card_fin] at hc1
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe,
      Fintype.card_fin] at hc2
  have hsubQ : Fintype.card {q : Fin Q // q ≠ ⟨0, hQ⟩} = Q - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  rw [hsubQ] at hc1
  rw [hc1, Fintype.card_fun, Fintype.card_fin, hc2, Fintype.card_fun, Fintype.card_fin]
  ring

/-- Single-scale open covering lemma via Finset derandomization: for ANY infinite set `B ⊆ ℝ`
and ANY `δ > 0`, there exists an open set `U ⊆ ℝ` with `volume U ≤ ENNReal.ofReal δ` such that
no translate `B + b` (`b : ℝ`) is contained in `[0, 1] \ U`. -/
private lemma exists_open_avoid_translates {B : Set ℝ} (hInf : B.Infinite)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set ℝ, IsOpen U ∧ volume U ≤ ENNReal.ofReal δ ∧
      ∀ b : ℝ, ¬ ((fun x : ℝ => x + b) '' B ⊆ Set.Icc (0 : ℝ) 1 \ U) := by
  classical
  let Q : ℕ := max 2 (Nat.ceil (64 / δ))
  have hQ2 : 2 ≤ Q := le_max_left _ _
  have hQpos : 0 < Q := by omega
  have hQreal : 64 / δ ≤ (Q : ℝ) :=
    le_trans (Nat.le_ceil (64 / δ)) (by exact_mod_cast le_max_right 2 (Nat.ceil (64 / δ)))
  have hQinv : 1 / (Q : ℝ) ≤ δ / 64 := by
    have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    rw [div_le_div_iff₀ hQposR (by norm_num)]
    have := (div_le_iff₀ hδ).mp hQreal
    linarith
  have hbase_lt : (1 : ℝ) - 1 / (Q : ℝ) < 1 := by
    have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    linarith [div_pos one_pos hQposR]
  have hbase_nonneg : (0 : ℝ) ≤ 1 - 1 / (Q : ℝ) := by
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hQ1
  have htend_pow : Tendsto (fun k : ℕ => (1 - 1 / (Q : ℝ)) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt
  rw [Metric.tendsto_atTop] at htend_pow
  obtain ⟨K0, hK0⟩ := htend_pow (δ / 32) (by positivity)
  let K : ℕ := max 1 K0
  have hKpos : 0 < K := le_max_left 1 K0
  have hpowK : (1 - 1 / (Q : ℝ)) ^ K ≤ δ / 32 := by
    have hdist := hK0 K (le_max_right 1 K0)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hbase_nonneg K)] at hdist
    exact hdist.le
  -- Extract `K` distinct elements `t : Fin K → ℝ` from `B`, shifted by `t 0`.
  have : Infinite B := hInf.to_subtype
  let eB : ℕ ↪ B := Infinite.natEmbedding B
  let t : Fin K → ℝ := fun j => (eB j.1).1
  have htB : ∀ j, t j ∈ B := fun j => (eB j.1).2
  have ht_inj : Function.Injective t := fun i j hij =>
    Fin.ext (eB.injective (Subtype.ext hij))
  let t₀ : ℝ := t ⟨0, hKpos⟩
  let s : Fin K → ℝ := fun j => t j - t₀
  have hs0 : s ⟨0, hKpos⟩ = 0 := sub_self t₀
  have hs_inj : Function.Injective s := fun i j hij =>
    ht_inj (sub_left_inj.mp hij)
  by_cases hbig : ∃ j : Fin K, 1 < |s j|
  · obtain ⟨j, hj⟩ := hbig
    refine ⟨∅, isOpen_empty, by simp, fun b hsub => ?_⟩
    have h0 : t₀ + b ∈ Set.Icc (0 : ℝ) 1 := (hsub ⟨t₀, htB ⟨0, hKpos⟩, rfl⟩).1
    have hj_in : t j + b ∈ Set.Icc (0 : ℝ) 1 := (hsub ⟨t j, htB j, rfl⟩).1
    have habs : |s j| ≤ 1 := by
      rw [show s j = (t j + b) - (t₀ + b) by dsimp only [s]; ring, abs_le]
      exact ⟨by linarith [h0.2, hj_in.1], by linarith [h0.1, hj_in.2]⟩
    linarith
  · push Not at hbig
    -- Choose resolution `M ≥ 4` separating all distinct pairs `s i, s j` by more than `2 / M`.
    let D : Finset (Fin K × Fin K) :=
      (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2)
    have hM_exists : ∃ M : ℕ, 4 ≤ M ∧ ∀ i j : Fin K, i ≠ j → 2 / (M : ℝ) < |s i - s j| := by
      by_cases hD : D.Nonempty
      · let dmin : ℝ := D.inf' hD (fun p => |s p.1 - s p.2|)
        have hdmin_pos : 0 < dmin := by
          rw [Finset.lt_inf'_iff]
          intro p hp
          have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
          exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hne (hs_inj h)))
        let M : ℕ := max 4 (Nat.ceil (2 / dmin) + 1)
        refine ⟨M, le_max_left _ _, fun i j hij => ?_⟩
        have hMgt : 2 / dmin < (M : ℝ) := by
          have h1 : 2 / dmin ≤ (Nat.ceil (2 / dmin) : ℝ) := Nat.le_ceil _
          have h2 : (Nat.ceil (2 / dmin) : ℝ) + 1 ≤ (M : ℝ) := by
            exact_mod_cast le_max_right 4 (Nat.ceil (2 / dmin) + 1)
          linarith
        have hMpos : (0 : ℝ) < (M : ℝ) := by
          have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left 4 (Nat.ceil (2 / dmin) + 1)
          linarith
        have hlt_dmin : 2 / (M : ℝ) < dmin := by
          rw [div_lt_iff₀ hMpos]
          have := (div_lt_iff₀ hdmin_pos).mp hMgt
          linarith
        have hpD : (i, j) ∈ D := by simp [D, hij]
        exact lt_of_lt_of_le hlt_dmin (Finset.inf'_le (f := fun p : Fin K × Fin K => |s p.1 - s p.2|) hpD)
      · refine ⟨4, le_rfl, fun i j hij => ?_⟩
        exfalso
        exact hD ⟨(i, j), by simp [D, hij]⟩
    obtain ⟨M, hM4, hMsep⟩ := hM_exists
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
      linarith
    let c : Fin K → ℤ := fun j => Int.floor ((M : ℝ) * s j)
    have hc_inj : Function.Injective c := by
      intro i j hij
      by_contra hne
      have hsep := hMsep i j hne
      have hi1 : (c i : ℝ) ≤ (M : ℝ) * s i := Int.floor_le _
      have hi2 : (M : ℝ) * s i < (c i : ℝ) + 1 := Int.lt_floor_add_one _
      have hj1 : (c j : ℝ) ≤ (M : ℝ) * s j := Int.floor_le _
      have hj2 : (M : ℝ) * s j < (c j : ℝ) + 1 := Int.lt_floor_add_one _
      rw [hij] at hi1 hi2
      have hdiff : |(M : ℝ) * s i - (M : ℝ) * s j| < 1 := by
        rw [abs_lt]; constructor <;> linarith
      have hdiff' : (M : ℝ) * |s i - s j| < 1 := by
        rw [← abs_of_pos hMpos, ← abs_mul, mul_sub]
        exact hdiff
      have hsep' : 2 < (M : ℝ) * |s i - s j| := by
        have := (div_lt_iff₀ hMpos).mp hsep
        linarith
      linarith
    have hc_bounds : ∀ j : Fin K, -(M : ℤ) ≤ c j ∧ c j ≤ (M : ℤ) := by
      intro j
      have hle1 : -(1 : ℝ) ≤ s j ∧ s j ≤ 1 := abs_le.mp (hbig j)
      constructor
      · exact Int.le_floor.mpr (by push_cast; nlinarith)
      · have hfl : (c j : ℝ) ≤ (M : ℝ) * s j := Int.floor_le _
        have hleM : (c j : ℝ) ≤ (M : ℝ) := by nlinarith
        exact_mod_cast hleM
    let V : Finset ℤ := Finset.Icc (-(M : ℤ)) (2 * (M : ℤ))
    have hVmem : ∀ (x : Fin (M + 1)) (j : Fin K), (x.1 : ℤ) + c j ∈ V := by
      intro x j
      simp only [V, Finset.mem_Icc]
      have hx : (x.1 : ℤ) ≤ (M : ℤ) := by omega
      have hcj := hc_bounds j
      omega
    have hVmem_x : ∀ x : Fin (M + 1), (x.1 : ℤ) ∈ V := by
      intro x
      simp only [V, Finset.mem_Icc]
      omega
    have hVcard_le : V.card ≤ 4 * M := by
      have hcard : V.card = 3 * M + 1 := by
        dsimp only [V]
        rw [Int.card_Icc]
        omega
      omega
    -- Exact Finset averaging over `f : {v // v ∈ V} → Fin Q`.
    let S0 : ({v : ℤ // v ∈ V} → Fin Q) → Finset {v : ℤ // v ∈ V} :=
      fun f => Finset.univ.filter (fun v => f v = ⟨0, hQpos⟩)
    let R : ({v : ℤ // v ∈ V} → Fin Q) → Finset (Fin (M + 1)) :=
      fun f => Finset.univ.filter (fun x => ∀ j : Fin K, f ⟨(x.1 : ℤ) + c j, hVmem x j⟩ ≠ ⟨0, hQpos⟩)
    let NΩ : ℕ := Fintype.card ({v : ℤ // v ∈ V} → Fin Q)
    have hNΩ_pos : (0 : ℝ) < (NΩ : ℝ) := by
      have hpos : 0 < NΩ := by
        dsimp only [NΩ]
        rw [Fintype.card_fun, Fintype.card_fin]
        exact pow_pos hQpos _
      exact_mod_cast hpos
    have hsum_S0 : (∑ f : {v : ℤ // v ∈ V} → Fin Q, ((S0 f).card : ℝ)) =
        (NΩ : ℝ) * ((V.card : ℝ) / (Q : ℝ)) := by
      have hnat : (∑ f : {v : ℤ // v ∈ V} → Fin Q, (S0 f).card) * Q = V.card * NΩ := by
        have hswap : ∑ f : {v : ℤ // v ∈ V} → Fin Q, (S0 f).card =
            ∑ v : {v : ℤ // v ∈ V}, (Finset.univ.filter (fun f : {v : ℤ // v ∈ V} → Fin Q =>
              f v = ⟨0, hQpos⟩)).card := by
          simp_rw [S0, Finset.card_filter]
          rw [Finset.sum_comm]
        rw [hswap, Finset.sum_mul]
        calc ∑ v : {v : ℤ // v ∈ V},
                (Finset.univ.filter (fun f : {v : ℤ // v ∈ V} → Fin Q => f v = ⟨0, hQpos⟩)).card * Q
            = ∑ _v : {v : ℤ // v ∈ V}, NΩ := by
                refine Finset.sum_congr rfl fun v _ => card_filter_apply_eq_zero_mul hQpos v
          _ = V.card * NΩ := by
                simp [Finset.sum_const]
      have hcast : ((∑ f : {v : ℤ // v ∈ V} → Fin Q, ((S0 f).card : ℝ)) * (Q : ℝ)) =
          (V.card : ℝ) * (NΩ : ℝ) := by
        exact_mod_cast hnat
      have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
      calc (∑ f : {v : ℤ // v ∈ V} → Fin Q, ((S0 f).card : ℝ))
          = ((V.card : ℝ) * (NΩ : ℝ)) / (Q : ℝ) := (eq_div_iff hQposR.ne').mpr hcast
        _ = (NΩ : ℝ) * ((V.card : ℝ) / (Q : ℝ)) := by ring
    have hsum_R : (∑ f : {v : ℤ // v ∈ V} → Fin Q, ((R f).card : ℝ)) =
        (NΩ : ℝ) * (((M + 1 : ℕ) : ℝ) * (1 - 1 / (Q : ℝ)) ^ K) := by
      have hnat : (∑ f : {v : ℤ // v ∈ V} → Fin Q, (R f).card) * Q ^ K =
          (M + 1) * ((Q - 1) ^ K * NΩ) := by
        have hswap : ∑ f : {v : ℤ // v ∈ V} → Fin Q, (R f).card =
            ∑ x : Fin (M + 1), (Finset.univ.filter (fun f : {v : ℤ // v ∈ V} → Fin Q =>
              ∀ j : Fin K, f ⟨(x.1 : ℤ) + c j, hVmem x j⟩ ≠ ⟨0, hQpos⟩)).card := by
          simp_rw [R, Finset.card_filter]
          rw [Finset.sum_comm]
        rw [hswap, Finset.sum_mul]
        calc ∑ x : Fin (M + 1),
                (Finset.univ.filter (fun f : {v : ℤ // v ∈ V} → Fin Q =>
                  ∀ j : Fin K, f ⟨(x.1 : ℤ) + c j, hVmem x j⟩ ≠ ⟨0, hQpos⟩)).card * Q ^ K
            = ∑ _x : Fin (M + 1), (Q - 1) ^ K * NΩ := by
                refine Finset.sum_congr rfl fun x _ => ?_
                let T : Finset {v : ℤ // v ∈ V} :=
                  Finset.univ.image (fun j : Fin K => (⟨(x.1 : ℤ) + c j, hVmem x j⟩ : {v : ℤ // v ∈ V}))
                have hTcard : T.card = K := by
                  dsimp only [T]
                  rw [Finset.card_image_of_injective]
                  · simp
                  · intro i j hij
                    have hval : (x.1 : ℤ) + c i = (x.1 : ℤ) + c j := congrArg Subtype.val hij
                    exact hc_inj (add_left_cancel hval)
                have hfilt : (Finset.univ.filter (fun f : {v : ℤ // v ∈ V} → Fin Q =>
                    ∀ j : Fin K, f ⟨(x.1 : ℤ) + c j, hVmem x j⟩ ≠ ⟨0, hQpos⟩)) =
                    (Finset.univ.filter (fun f : {v : ℤ // v ∈ V} → Fin Q =>
                      ∀ v ∈ T, f v ≠ ⟨0, hQpos⟩)) := by
                  ext f
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, Finset.mem_image]
                  constructor
                  · rintro hf v ⟨j, rfl⟩
                    exact hf j
                  · intro hf j
                    exact hf _ ⟨j, rfl⟩
                rw [hfilt, ← hTcard]
                exact card_filter_avoid_zero_mul hQpos T
          _ = (M + 1) * ((Q - 1) ^ K * NΩ) := by
                simp [Finset.sum_const]
      have hcast : (∑ f : {v : ℤ // v ∈ V} → Fin Q, ((R f).card : ℝ)) * ((Q : ℝ) ^ K) =
          ((M + 1 : ℕ) : ℝ) * ((((Q - 1 : ℕ) : ℝ) ^ K) * (NΩ : ℝ)) := by
        exact_mod_cast hnat
      have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
      have hQKpos : (0 : ℝ) < (Q : ℝ) ^ K := pow_pos hQposR K
      have hQm1 : ((Q - 1 : ℕ) : ℝ) / (Q : ℝ) = 1 - 1 / (Q : ℝ) := by
        rw [Nat.cast_sub hQpos, Nat.cast_one]
        field_simp
      calc (∑ f : {v : ℤ // v ∈ V} → Fin Q, ((R f).card : ℝ))
          = (((M + 1 : ℕ) : ℝ) * ((((Q - 1 : ℕ) : ℝ) ^ K) * (NΩ : ℝ))) / ((Q : ℝ) ^ K) :=
            (eq_div_iff hQKpos.ne').mpr hcast
        _ = (NΩ : ℝ) * (((M + 1 : ℕ) : ℝ) * ((((Q - 1 : ℕ) : ℝ) / (Q : ℝ)) ^ K)) := by
            rw [div_pow]; ring
        _ = (NΩ : ℝ) * (((M + 1 : ℕ) : ℝ) * (1 - 1 / (Q : ℝ)) ^ K) := by rw [hQm1]
    -- Pigeonhole: extract deterministic `f` achieving at most the average size.
    have hsum_tot : (∑ f : {v : ℤ // v ∈ V} → Fin Q, (((S0 f).card : ℝ) + ((R f).card : ℝ))) ≤
        ∑ _f : {v : ℤ // v ∈ V} → Fin Q, ((δ / 8) * (M : ℝ)) := by
      rw [Finset.sum_add_distrib, hsum_S0, hsum_R]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (NΩ : ℝ) * ((V.card : ℝ) / (Q : ℝ)) +
          (NΩ : ℝ) * (((M + 1 : ℕ) : ℝ) * (1 - 1 / (Q : ℝ)) ^ K) ≤
        (NΩ : ℝ) * (δ / 8 * (M : ℝ))
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hNΩ_pos.le
      have h1 : (V.card : ℝ) / (Q : ℝ) ≤ (4 * (M : ℝ)) * (δ / 64) := by
        have hV' : (V.card : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast hVcard_le
        calc (V.card : ℝ) / (Q : ℝ)
            = (V.card : ℝ) * (1 / (Q : ℝ)) := by ring
          _ ≤ (4 * (M : ℝ)) * (δ / 64) :=
              mul_le_mul hV' hQinv (by positivity) (by positivity)
      have h2 : ((M + 1 : ℕ) : ℝ) * (1 - 1 / (Q : ℝ)) ^ K ≤ (2 * (M : ℝ)) * (δ / 32) := by
        have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
          have hMge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
          push_cast; linarith
        exact mul_le_mul hM1 hpowK (pow_nonneg hbase_nonneg K) (by positivity)
      linarith
    have huniv_ne : (Finset.univ : Finset ({v : ℤ // v ∈ V} → Fin Q)).Nonempty :=
      ⟨fun _ => ⟨0, hQpos⟩, Finset.mem_univ _⟩
    obtain ⟨f, _, hf_le⟩ := Finset.exists_le_of_sum_le huniv_ne hsum_tot
    let S : Finset ℤ :=
      (S0 f).image Subtype.val ∪ (R f).image (fun x : Fin (M + 1) => (x.1 : ℤ))
    have hScard : (S.card : ℝ) ≤ (δ / 8) * (M : ℝ) := by
      have h1 : S.card ≤ (S0 f).card + (R f).card :=
        le_trans (Finset.card_union_le _ _)
          (add_le_add Finset.card_image_le Finset.card_image_le)
      have h2 : (S.card : ℝ) ≤ ((S0 f).card : ℝ) + ((R f).card : ℝ) := by exact_mod_cast h1
      linarith
    let U : Set ℝ := ⋃ v ∈ S, Set.Ioo (((v : ℝ) - 1) / (M : ℝ)) (((v : ℝ) + 3) / (M : ℝ))
    have hUopen : IsOpen U := isOpen_biUnion fun _ _ => isOpen_Ioo
    have hUmeas : volume U ≤ ENNReal.ofReal δ := by
      calc volume U
          ≤ ∑ v ∈ S, volume (Set.Ioo (((v : ℝ) - 1) / (M : ℝ)) (((v : ℝ) + 3) / (M : ℝ))) :=
            measure_biUnion_finset_le S _
        _ = ∑ _v ∈ S, ENNReal.ofReal (4 / (M : ℝ)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Real.volume_Ioo]
            congr 1
            ring
        _ = (S.card : ENNReal) * ENNReal.ofReal (4 / (M : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = ENNReal.ofReal ((S.card : ℝ) * (4 / (M : ℝ))) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ ≤ ENNReal.ofReal δ := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : (S.card : ℝ) * (4 / (M : ℝ)) ≤ ((δ / 8) * (M : ℝ)) * (4 / (M : ℝ)) :=
              mul_le_mul_of_nonneg_right hScard (by positivity)
            have h2 : ((δ / 8) * (M : ℝ)) * (4 / (M : ℝ)) = δ / 2 := by field_simp; ring
            linarith
    refine ⟨U, hUopen, hUmeas, fun b hsub => ?_⟩
    let b' : ℝ := t₀ + b
    have hb'E : b' ∈ Set.Icc (0 : ℝ) 1 \ U := hsub ⟨t₀, htB ⟨0, hKpos⟩, rfl⟩
    let x0 : ℕ := Nat.floor ((M : ℝ) * b')
    have hx0_le : x0 ≤ M := by
      have h1 : (M : ℝ) * b' ≤ (M : ℝ) := by nlinarith [hb'E.1.2]
      exact Nat.floor_le_of_le (by exact_mod_cast h1)
    let x : Fin (M + 1) := ⟨x0, Nat.lt_succ_of_le hx0_le⟩
    have hx0_lo : (x0 : ℝ) ≤ (M : ℝ) * b' := Nat.floor_le (mul_nonneg hMpos.le hb'E.1.1)
    have hx0_hi : (M : ℝ) * b' < (x0 : ℝ) + 1 := Nat.lt_floor_add_one _
    by_cases hxR : x ∈ R f
    · have hvS : (x0 : ℤ) ∈ S :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hxR, rfl⟩)
      apply hb'E.2
      refine Set.mem_iUnion₂.mpr ⟨(x0 : ℤ), hvS, ?_, ?_⟩
      · rw [div_lt_iff₀ hMpos]; push_cast; linarith
      · rw [lt_div_iff₀ hMpos]; push_cast; linarith
    · simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hxR
      push Not at hxR
      obtain ⟨j, hj⟩ := hxR
      let v : {v : ℤ // v ∈ V} := ⟨(x0 : ℤ) + c j, hVmem x j⟩
      have hvS0 : v ∈ S0 f := by
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      have hvS : v.1 ∈ S := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hvS0, rfl⟩)
      have htjE : t j + b ∈ Set.Icc (0 : ℝ) 1 \ U := hsub ⟨t j, htB j, rfl⟩
      apply htjE.2
      have hcj_lo : (c j : ℝ) ≤ (M : ℝ) * s j := Int.floor_le _
      have hcj_hi : (M : ℝ) * s j < (c j : ℝ) + 1 := Int.lt_floor_add_one _
      have hsum_eq : t j + b = b' + s j := by dsimp only [b', s]; ring
      refine Set.mem_iUnion₂.mpr ⟨v.1, hvS, ?_, ?_⟩
      · rw [div_lt_iff₀ hMpos, hsum_eq]
        have hvcast : (v.1 : ℝ) = (x0 : ℝ) + (c j : ℝ) := by dsimp only [v]; push_cast; ring
        rw [hvcast]; linarith
      · rw [lt_div_iff₀ hMpos, hsum_eq]
        have hvcast : (v.1 : ℝ) = (x0 : ℝ) + (c j : ℝ) := by dsimp only [v]; push_cast; ring
        rw [hvcast]; linarith

/-- **Universal Countable-Scale Avoidance for Arbitrary Infinite Sets**:
For EVERY infinite set `A ⊆ ℝ` (including `{2^{-n}}`, `{2^{-2^n}}`, `{1/n!}`, or arbitrary
Cantor/sparse sets), EVERY countable set of nonzero scales `S ⊆ ℝ`, and EVERY `ε ∈ (0, 1)`,
there exists a compact, measurable subset `E ⊆ [0, 1]` with `ENNReal.ofReal (1 - ε) ≤ volume E`
containing NO affine copy `(fun x => a * x + b) '' A` for any `a ∈ S` and `b : ℝ`. -/
theorem ppl060_countable_scales_avoidance_arbitrary_infinite
    {A S : Set ℝ} (hInf : A.Infinite) (hS_cnt : S.Countable) (hS_nz : ∀ a ∈ S, a ≠ 0)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ a ∈ S, ∀ b : ℝ, ¬ ((fun x : ℝ => a * x + b) '' A ⊆ E) := by
  by_cases hSne : S.Nonempty
  · obtain ⟨g, hg⟩ := hS_cnt.exists_eq_range hSne
    have hg_nz : ∀ k : ℕ, g k ≠ 0 := fun k => hS_nz (g k) (hg ▸ Set.mem_range_self k)
    have hg_inf : ∀ k : ℕ, ((fun x : ℝ => g k * x) '' A).Infinite := fun k =>
      hInf.image (fun x _ y _ hxy => mul_left_cancel₀ (hg_nz k) hxy)
    have hU_exists : ∀ k : ℕ, ∃ U : Set ℝ, IsOpen U ∧
        volume U ≤ ENNReal.ofReal (ε / (2 : ℝ) ^ (k + 1)) ∧
        ∀ b : ℝ, ¬ ((fun x : ℝ => x + b) '' ((fun x : ℝ => g k * x) '' A) ⊆ Set.Icc (0 : ℝ) 1 \ U) :=
      fun k => exists_open_avoid_translates (hg_inf k) (by positivity)
    choose U_lvl hUopen_lvl hUmeas_lvl hUavoid_lvl using hU_exists
    let U : Set ℝ := ⋃ k : ℕ, U_lvl k
    have hUopen : IsOpen U := isOpen_iUnion hUopen_lvl
    have hUmeas : volume U ≤ ENNReal.ofReal ε := by
      calc volume U
          ≤ ∑' k : ℕ, volume (U_lvl k) := measure_iUnion_le _
        _ ≤ ∑' k : ℕ, ENNReal.ofReal (ε / (2 : ℝ) ^ (k + 1)) :=
            ENNReal.tsum_le_tsum hUmeas_lvl
        _ = ENNReal.ofReal ε := tsum_ofReal_eps_div_two_pow hε_pos.le
    obtain ⟨hEsub, hEcomp, hEmeas, hEvol⟩ :=
      compact_sdiff_open_measure_ge hUopen hε_pos hε_lt hUmeas
    refine ⟨Set.Icc (0 : ℝ) 1 \ U, hEsub, hEcomp, hEmeas, hEvol, ?_⟩
    intro a haS b hsub
    rw [hg] at haS
    obtain ⟨k, rfl⟩ := haS
    apply hUavoid_lvl k b
    rintro _ ⟨_, ⟨x, hxA, rfl⟩, rfl⟩
    have hxE := hsub ⟨x, hxA, rfl⟩
    exact ⟨hxE.1, fun hxUk => hxE.2 (Set.mem_iUnion.mpr ⟨k, hxUk⟩)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hSne
    subst hSne
    refine ⟨Set.Icc (0 : ℝ) 1, le_rfl, isCompact_Icc, measurableSet_Icc, ?_, by simp⟩
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Universal Translation Avoidance for Arbitrary Infinite Sets**:
For EVERY infinite set `A ⊆ ℝ` and EVERY `ε ∈ (0, 1)`, there exists a compact `E ⊆ [0, 1]`
with `ENNReal.ofReal (1 - ε) ≤ volume E` containing NO translate `(fun x => x + b) '' A`. -/
theorem ppl060_translation_avoidance_arbitrary_infinite
    {A : Set ℝ} (hInf : A.Infinite) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ b : ℝ, ¬ ((fun x : ℝ => x + b) '' A ⊆ E) := by
  obtain ⟨E, hEsub, hEcomp, hEmeas, hEvol, hAvoid⟩ :=
    ppl060_countable_scales_avoidance_arbitrary_infinite (S := {(1 : ℝ)}) hInf
      (Set.countable_singleton 1) (by simp) hε_pos hε_lt
  refine ⟨E, hEsub, hEcomp, hEmeas, hEvol, fun b hsub => ?_⟩
  apply hAvoid 1 (Set.mem_singleton 1) b
  simpa using hsub

/-- **Rational-Scale Avoidance for Arbitrary Infinite Sets**:
For EVERY infinite set `A ⊆ ℝ` (including `{2^{-n}}`, `{2^{-2^n}}`, `{1/n!}`) and EVERY
`ε ∈ (0, 1)`, there exists a compact `E ⊆ [0, 1]` with `volume E ≥ 1 - ε` avoiding ALL
rationally scaled affine copies `(fun x => (q : ℝ) * x + b) '' A` (`q : ℚ`, `q ≠ 0`). -/
theorem ppl060_rational_scales_avoidance
    {A : Set ℝ} (hInf : A.Infinite) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ q : ℚ, q ≠ 0 → ∀ b : ℝ, ¬ ((fun x : ℝ => (q : ℝ) * x + b) '' A ⊆ E) := by
  let S : Set ℝ := Set.range (fun q : {q : ℚ // q ≠ 0} => (q.1 : ℝ))
  have hS_cnt : S.Countable := Set.countable_range _
  have hS_nz : ∀ a ∈ S, a ≠ 0 := by
    rintro _ ⟨q, rfl⟩
    dsimp only
    exact_mod_cast q.2
  obtain ⟨E, hEsub, hEcomp, hEmeas, hEvol, hAvoid⟩ :=
    ppl060_countable_scales_avoidance_arbitrary_infinite hInf hS_cnt hS_nz hε_pos hε_lt
  exact ⟨E, hEsub, hEcomp, hEmeas, hEvol, fun q hq b =>
    hAvoid (q : ℝ) ⟨⟨q, hq⟩, rfl⟩ b⟩

/-- **Dyadic-Scale Avoidance for `{2^{-n}}`**:
For EVERY `ε ∈ (0, 1)`, there exists a compact `E ⊆ [0, 1]` with `volume E ≥ 1 - ε` avoiding
all dyadically scaled affine copies `(fun x => ± (2 : ℝ)^k * x + b) '' {2^{-n}}` (`k : ℤ`). -/
theorem ppl060_dyadic_scales_avoidance {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      ENNReal.ofReal (1 - ε) ≤ volume E ∧
      ∀ (s : Bool) (k : ℤ) (b : ℝ),
        ¬ ((fun x : ℝ => (if s then (2 : ℝ) ^ k else -((2 : ℝ) ^ k)) * x + b) ''
            Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ n) ⊆ E) := by
  have hInf : (Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ n)).Infinite := by
    refine Set.infinite_range_of_injective (StrictAnti.injective ?_)
    exact strictAnti_nat_of_succ_lt fun n => by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
  let S : Set ℝ := Set.range (fun p : Bool × ℤ => if p.1 then (2 : ℝ) ^ p.2 else -((2 : ℝ) ^ p.2))
  have hS_cnt : S.Countable := Set.countable_range _
  have hS_nz : ∀ a ∈ S, a ≠ 0 := by
    rintro _ ⟨⟨b, k⟩, rfl⟩
    cases b <;> simp [zpow_ne_zero]
  obtain ⟨E, hEsub, hEcomp, hEmeas, hEvol, hAvoid⟩ :=
    ppl060_countable_scales_avoidance_arbitrary_infinite hInf hS_cnt hS_nz hε_pos hε_lt
  exact ⟨E, hEsub, hEcomp, hEmeas, hEvol, fun s k b =>
    hAvoid _ ⟨(s, k), rfl⟩ b⟩

/-! ### Section 5: Geometric-Progression Continuum-Scale Avoidance (All `q ∈ (0, 1)`) -/

/-- Fractional-part distance helper: for every real `x` and every integer `z`,
`min (Int.fract x) (1 - Int.fract x) ≤ |x - z|`. -/
private lemma min_fract_le_abs_sub_int (x : ℝ) (z : ℤ) :
    min (Int.fract x) (1 - Int.fract x) ≤ |x - (z : ℝ)| := by
  set n : ℤ := ⌊x⌋
  have hfx : Int.fract x = x - (n : ℝ) := rfl
  rcases le_or_gt z n with hle | hgt
  · have hleR : (z : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
    have hnonneg : 0 ≤ x - (z : ℝ) := by linarith [Int.fract_nonneg x]
    rw [abs_of_nonneg hnonneg]
    exact le_trans (min_le_left _ _) (by linarith)
  · have hge : n + 1 ≤ z := Int.add_one_le_iff.mpr hgt
    have hgeR : (n : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hge
    have hnonpos : x - (z : ℝ) ≤ 0 := by linarith [Int.fract_lt_one x]
    rw [abs_of_nonpos hnonpos]
    exact le_trans (min_le_right _ _) (by linarith)

/-- Periodic-island set helper: for `N ≥ 1` and `0 < δ < 1`, the union
`E = ⋃ m ∈ Finset.range N, [m/N, (m+δ)/N]` is compact, measurable, lies in `[0, 1]`,
and has exact Lebesgue measure `ENNReal.ofReal δ`. -/
private lemma periodic_islands_properties (N : ℕ) (hN : 0 < N) {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    let E : Set ℝ := ⋃ m ∈ Finset.range N, Set.Icc ((m : ℝ) / N) (((m : ℝ) + δ) / N)
    E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧ volume E = ENNReal.ofReal δ := by
  intro E
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsub : E ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨m, hm, hlo, hhi⟩
    have hm_lt : m < N := Finset.mem_range.mp hm
    have hm1 : (m : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hm_lt
    refine ⟨le_trans (by positivity) hlo, le_trans hhi ?_⟩
    rw [div_le_one hNpos]
    linarith
  have hcomp : IsCompact E := (Finset.range N).isCompact_biUnion fun _ _ => isCompact_Icc
  have hmeas : MeasurableSet E := hcomp.measurableSet
  have hdisj : (Finset.range N : Set ℕ).PairwiseDisjoint
      (fun m => Set.Icc ((m : ℝ) / N) (((m : ℝ) + δ) / N)) := by
    intro m₁ _ m₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx₁ hx₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by exact_mod_cast hlt
      have h1 : ((m₁ : ℝ) + δ) / (N : ℝ) < (m₂ : ℝ) / (N : ℝ) :=
        div_lt_div_of_pos_right (by linarith) hNpos
      linarith [hx₁.2, hx₂.1]
    · have hm : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by exact_mod_cast hgt
      have h1 : ((m₂ : ℝ) + δ) / (N : ℝ) < (m₁ : ℝ) / (N : ℝ) :=
        div_lt_div_of_pos_right (by linarith) hNpos
      linarith [hx₁.1, hx₂.2]
  have hvol : volume E = ENNReal.ofReal δ := by
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_Icc)]
    have hsum : ∑ m ∈ Finset.range N, volume (Set.Icc ((m : ℝ) / N) (((m : ℝ) + δ) / N)) =
        ∑ _m ∈ Finset.range N, ENNReal.ofReal (δ / N) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Real.volume_Icc]
      congr 1
      ring
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNpos.le]
    congr 1
    field_simp
  exact ⟨hsub, hcomp, hmeas, hvol⟩

/-- Core periodic-island avoidance lemma for geometric sequences `{q^n}`:
If `0 < q < 1`, `N ≥ 1`, `0 < δ < 1/4`, and `δ < min (fract (q*k)) (1 - fract (q*k))` for every
integer `1 ≤ k ≤ ⌈1/q⌉ + 1` with `q * k ∉ ℤ`, then the periodic-island set
`E = ⋃ m < N, [m/N, (m+δ)/N]` avoids ALL affine copies `a * {q^n} + b` with `1/N ≤ |a|`. -/
private lemma periodic_islands_avoid_geometric
    {q δ : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1)
    (hδ_pos : 0 < δ) (hδ_quarter : δ < 1 / 4)
    (hδ_gap : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.ceil (1 / q) + 1 →
      (¬ ∃ z : ℤ, q * (k : ℝ) = (z : ℝ)) →
      δ < min (Int.fract (q * (k : ℝ))) (1 - Int.fract (q * (k : ℝ))))
    {N : ℕ} (hN : 0 < N) {a b : ℝ} (ha_ge : 1 / (N : ℝ) ≤ |a|) :
    ¬ ((fun x : ℝ => a * x + b) '' Set.range (fun n : ℕ => q ^ n) ⊆
        ⋃ m ∈ Finset.range N, Set.Icc ((m : ℝ) / N) (((m : ℝ) + δ) / N)) := by
  classical
  let E : Set ℝ := ⋃ m ∈ Finset.range N, Set.Icc ((m : ℝ) / N) (((m : ℝ) + δ) / N)
  intro hsub
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ha_pos : 0 < |a| := lt_of_lt_of_le (by positivity) ha_ge
  let y : ℕ → ℝ := fun n => a * q ^ n + b
  have hyE : ∀ n, y n ∈ E := fun n => hsub ⟨q ^ n, ⟨n, rfl⟩, rfl⟩
  have hq_tend : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_pos.le hq_lt
  have hy_tend : Tendsto y atTop (nhds b) := by
    have := (hq_tend.const_mul a).add_const b
    simpa [y] using this
  have hEcomp : IsCompact E :=
    (periodic_islands_properties N hN hδ_pos (by linarith)).2.1
  have hbE : b ∈ E := hEcomp.isClosed.mem_of_tendsto hy_tend (Eventually.of_forall hyE)
  -- Find the LAST index `n₁` with `1 / N ≤ |a| * q ^ n₁`.
  have haq_tend : Tendsto (fun n : ℕ => |a| * q ^ n) atTop (nhds 0) := by
    simpa using hq_tend.const_mul |a|
  rw [Metric.tendsto_atTop] at haq_tend
  obtain ⟨L, hL⟩ := haq_tend (1 / (N : ℝ)) (by positivity)
  let S : Finset ℕ := (Finset.range (L + 1)).filter (fun n => 1 / (N : ℝ) ≤ |a| * q ^ n)
  have h0S : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range, pow_zero, mul_one]
    exact ⟨Nat.succ_pos L, ha_ge⟩
  let n₁ : ℕ := S.max' ⟨0, h0S⟩
  have hn₁S : n₁ ∈ S := Finset.max'_mem S ⟨0, h0S⟩
  have hn₁_ge : 1 / (N : ℝ) ≤ |a| * q ^ n₁ := (Finset.mem_filter.mp hn₁S).2
  have hn₁_next : |a| * q ^ (n₁ + 1) < 1 / (N : ℝ) := by
    by_cases hle : n₁ + 1 < L + 1
    · by_contra hge
      push Not at hge
      have hmem : n₁ + 1 ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        exact ⟨hle, hge⟩
      have := Finset.le_max' S (n₁ + 1) hmem
      omega
    · have hdist := hL (n₁ + 1) (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos ha_pos (pow_pos hq_pos _))] at hdist
      exact hdist
  have hn₁_hi : |a| * q ^ n₁ < 1 / (q * (N : ℝ)) := by
    have hpow : |a| * q ^ (n₁ + 1) = q * (|a| * q ^ n₁) := by rw [pow_succ]; ring
    rw [hpow] at hn₁_next
    rw [lt_div_iff₀ (mul_pos hq_pos hNpos)]
    have h1 := (lt_div_iff₀ hNpos).mp hn₁_next
    linarith
  -- Extract island coordinates `(m, r)` for `b` and every `y n`.
  have hcoord : ∀ x ∈ E, ∃ m : ℕ, (m : ℝ) / (N : ℝ) ≤ x ∧ x ≤ ((m : ℝ) + δ) / (N : ℝ) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨m, _, hlo, hhi⟩
    exact ⟨m, hlo, hhi⟩
  obtain ⟨m₀, hm₀_lo, hm₀_hi⟩ := hcoord b hbE
  choose m hm_lo hm_hi using fun n => hcoord (y n) (hyE n)
  let r₀ : ℝ := (N : ℝ) * b - (m₀ : ℝ)
  let r : ℕ → ℝ := fun n => (N : ℝ) * y n - (m n : ℝ)
  have hr₀_bounds : 0 ≤ r₀ ∧ r₀ ≤ δ := by
    constructor
    · dsimp only [r₀]; have := (div_le_iff₀ hNpos).mp hm₀_lo; linarith
    · dsimp only [r₀]; have := (le_div_iff₀ hNpos).mp hm₀_hi; linarith
  have hr_bounds : ∀ n, 0 ≤ r n ∧ r n ≤ δ := fun n => by
    constructor
    · dsimp only [r]; have := (div_le_iff₀ hNpos).mp (hm_lo n); linarith
    · dsimp only [r]; have := (le_div_iff₀ hNpos).mp (hm_hi n); linarith
  let K : ℕ := Nat.ceil (1 / q) + 1
  let k : ℕ → ℕ := fun n => ((m n : ℤ) - (m₀ : ℤ)).natAbs
  -- Bounds at `n₁`: `1 ≤ k n₁ ≤ K`.
  have hk_n₁_pos : 1 ≤ k n₁ := by
    by_contra h0
    have hk0 : k n₁ = 0 := by omega
    have hmeq : m n₁ = m₀ := by
      have : (m n₁ : ℤ) - (m₀ : ℤ) = 0 := Int.natAbs_eq_zero.mp hk0
      omega
    have hdiff : |y n₁ - b| ≤ δ / (N : ℝ) := by
      have hNy : (N : ℝ) * y n₁ = (m₀ : ℝ) + r n₁ := by dsimp only [r]; rw [hmeq]; ring
      have hNb : (N : ℝ) * b = (m₀ : ℝ) + r₀ := by dsimp only [r₀]; ring
      have hmul : (N : ℝ) * |y n₁ - b| ≤ δ := by
        rw [← abs_of_pos hNpos, ← abs_mul, mul_sub, hNy, hNb]
        have : (m₀ : ℝ) + r n₁ - ((m₀ : ℝ) + r₀) = r n₁ - r₀ := by ring
        rw [this, abs_le]
        exact ⟨by linarith [(hr_bounds n₁).1, hr₀_bounds.2],
               by linarith [(hr_bounds n₁).2, hr₀_bounds.1]⟩
      exact (le_div_iff₀ hNpos).mpr (by linarith)
    have hyb : |y n₁ - b| = |a| * q ^ n₁ := by
      dsimp only [y]
      rw [add_sub_cancel_right, abs_mul, abs_of_pos (pow_pos hq_pos _)]
    rw [hyb] at hdiff
    have hδN : δ / (N : ℝ) < 1 / (N : ℝ) := div_lt_div_of_pos_right (by linarith) hNpos
    linarith
  have hk_n₁_le : k n₁ ≤ K := by
    have hNdiff : |(m n₁ : ℝ) - (m₀ : ℝ)| ≤ (N : ℝ) * |y n₁ - b| + δ := by
      have hNy : (N : ℝ) * y n₁ = (m n₁ : ℝ) + r n₁ := by dsimp only [r]; ring
      have hNb : (N : ℝ) * b = (m₀ : ℝ) + r₀ := by dsimp only [r₀]; ring
      have h1 : (m n₁ : ℝ) - (m₀ : ℝ) = (N : ℝ) * (y n₁ - b) - (r n₁ - r₀) := by linarith
      have hr_abs : |r n₁ - r₀| ≤ δ := by
        rw [abs_le]
        exact ⟨by linarith [(hr_bounds n₁).1, hr₀_bounds.2],
               by linarith [(hr_bounds n₁).2, hr₀_bounds.1]⟩
      calc |(m n₁ : ℝ) - (m₀ : ℝ)|
          = |(N : ℝ) * (y n₁ - b) - (r n₁ - r₀)| := by rw [h1]
        _ ≤ |(N : ℝ) * (y n₁ - b)| + |r n₁ - r₀| := abs_sub _ _
        _ = (N : ℝ) * |y n₁ - b| + |r n₁ - r₀| := by rw [abs_mul, abs_of_pos hNpos]
        _ ≤ (N : ℝ) * |y n₁ - b| + δ := by linarith
    have hyb : |y n₁ - b| = |a| * q ^ n₁ := by
      dsimp only [y]
      rw [add_sub_cancel_right, abs_mul, abs_of_pos (pow_pos hq_pos _)]
    have hNyb_lt : (N : ℝ) * |y n₁ - b| < 1 / q := by
      rw [hyb]
      have h1 := (lt_div_iff₀ (mul_pos hq_pos hNpos)).mp hn₁_hi
      rw [lt_div_iff₀ hq_pos]
      linarith
    have hkcast : (k n₁ : ℝ) = |(m n₁ : ℝ) - (m₀ : ℝ)| := by
      dsimp only [k]
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    have hklt : (k n₁ : ℝ) < (K : ℝ) := by
      dsimp only [K]
      push_cast
      linarith [Nat.le_ceil (1 / q)]
    exact (Nat.cast_lt.mp hklt).le
  -- Convex-combination descent step: if `1 ≤ k n ≤ K`, then `1 ≤ k (n + 1) < k n`.
  have hdescent : ∀ n : ℕ, 1 ≤ k n → k n ≤ K → 1 ≤ k (n + 1) ∧ k (n + 1) < k n := by
    intro n hk1 hkK
    have hconv : y (n + 1) = (1 - q) * b + q * y n := by
      dsimp only [y]; rw [pow_succ]; ring
    let r' : ℝ := (1 - q) * r₀ + q * r n
    have hr'_bounds : 0 ≤ r' ∧ r' ≤ δ := by
      constructor
      · dsimp only [r']; nlinarith [hr₀_bounds.1, (hr_bounds n).1]
      · dsimp only [r']; nlinarith [hr₀_bounds.2, (hr_bounds n).2]
    have hNconv : (m (n + 1) : ℝ) + r (n + 1) =
        (m₀ : ℝ) + q * ((m n : ℝ) - (m₀ : ℝ)) + r' := by
      have h1 : (N : ℝ) * y (n + 1) = (m (n + 1) : ℝ) + r (n + 1) := by dsimp only [r]; ring
      have h2 : (N : ℝ) * b = (m₀ : ℝ) + r₀ := by dsimp only [r₀]; ring
      have h3 : (N : ℝ) * y n = (m n : ℝ) + r n := by dsimp only [r]; ring
      have h4 : (N : ℝ) * y (n + 1) = (1 - q) * ((N : ℝ) * b) + q * ((N : ℝ) * y n) := by
        rw [hconv]; ring
      dsimp only [r']
      linarith
    let d_n : ℤ := (m n : ℤ) - (m₀ : ℤ)
    let d_next : ℤ := (m (n + 1) : ℤ) - (m₀ : ℤ)
    have happrox : |q * (d_n : ℝ) - (d_next : ℝ)| ≤ δ := by
      have heq : q * (d_n : ℝ) - (d_next : ℝ) = r (n + 1) - r' := by
        dsimp only [d_n, d_next]; push_cast; linarith
      rw [heq, abs_le]
      exact ⟨by linarith [(hr_bounds (n + 1)).1, hr'_bounds.2],
             by linarith [(hr_bounds (n + 1)).2, hr'_bounds.1]⟩
    have hex_int : ∃ z : ℤ, q * (k n : ℝ) = (z : ℝ) := by
      by_contra hnot
      have hgap := hδ_gap (k n) hk1 hkK hnot
      have hcase : (d_n : ℝ) = (k n : ℝ) ∨ (d_n : ℝ) = -((k n : ℝ)) := by
        have h1 : |(d_n : ℝ)| = (k n : ℝ) := by
          dsimp only [k, d_n]
          symm
          rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
        rcases le_or_gt (0 : ℝ) (d_n : ℝ) with hnn | hneg
        · left; rw [abs_of_nonneg hnn] at h1; exact h1
        · right; rw [abs_of_neg hneg] at h1; linarith
      rcases hcase with hd | hd
      · rw [hd] at happrox
        linarith [min_fract_le_abs_sub_int (q * (k n : ℝ)) d_next]
      · rw [hd] at happrox
        have habs_eq : |q * -((k n : ℝ)) - (d_next : ℝ)| = |q * (k n : ℝ) - ((-d_next : ℤ) : ℝ)| := by
          push_cast
          rw [show q * -(k n : ℝ) - (d_next : ℝ) = -(q * (k n : ℝ) - -(d_next : ℝ)) by ring,
              abs_neg]
        rw [habs_eq] at happrox
        linarith [min_fract_le_abs_sub_int (q * (k n : ℝ)) (-d_next)]
    obtain ⟨z, hz⟩ := hex_int
    have hcase : (d_n : ℝ) = (k n : ℝ) ∨ (d_n : ℝ) = -((k n : ℝ)) := by
      have h1 : |(d_n : ℝ)| = (k n : ℝ) := by
        dsimp only [k, d_n]
        symm
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rcases le_or_gt (0 : ℝ) (d_n : ℝ) with hnn | hneg
      · left; rw [abs_of_nonneg hnn] at h1; exact h1
      · right; rw [abs_of_neg hneg] at h1; linarith
    have hdnext_abs : |(d_next : ℝ)| = q * (k n : ℝ) := by
      rcases hcase with hd | hd
      · rw [hd, hz] at happrox
        have hsub_lt : |(z - d_next : ℤ)| < 1 := by
          have : ((z - d_next : ℤ) : ℝ) = (z : ℝ) - (d_next : ℝ) := by push_cast; rfl
          have hR : |((z - d_next : ℤ) : ℝ)| < 1 := by rw [this]; linarith
          exact_mod_cast (by rwa [← Int.cast_abs] at hR : ((|(z - d_next : ℤ)| : ℤ) : ℝ) < (1 : ℝ))
        rw [abs_lt] at hsub_lt
        have heq_z : d_next = z := by omega
        rw [heq_z, ← hz, abs_of_pos (mul_pos hq_pos (by exact_mod_cast hk1))]
      · rw [hd] at happrox
        have hneg_eq : q * -((k n : ℝ)) - (d_next : ℝ) = ((-z - d_next : ℤ) : ℝ) := by
          push_cast; linarith
        rw [hneg_eq] at happrox
        have hsub_lt : |(-z - d_next : ℤ)| < 1 := by
          have hR : |((-z - d_next : ℤ) : ℝ)| < 1 := by linarith
          exact_mod_cast (by rwa [← Int.cast_abs] at hR : ((|(-z - d_next : ℤ)| : ℤ) : ℝ) < (1 : ℝ))
        rw [abs_lt] at hsub_lt
        have heq_z : d_next = -z := by omega
        rw [heq_z]; push_cast
        rw [abs_neg, ← hz, abs_of_pos (mul_pos hq_pos (by exact_mod_cast hk1))]
    have hknext_real : (k (n + 1) : ℝ) = q * (k n : ℝ) := by
      have h1 : (k (n + 1) : ℝ) = |(d_next : ℝ)| := by
        dsimp only [k, d_next]; rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [h1, hdnext_abs]
    have hkn_posR : (0 : ℝ) < (k n : ℝ) := by exact_mod_cast hk1
    have hpos_next : (0 : ℝ) < (k (n + 1) : ℝ) := by rw [hknext_real]; exact mul_pos hq_pos hkn_posR
    have hlt_next : (k (n + 1) : ℝ) < (k n : ℝ) := by rw [hknext_real]; nlinarith
    exact ⟨Nat.succ_le_of_lt (by exact_mod_cast hpos_next), by exact_mod_cast hlt_next⟩
  -- Well-founded descent on `k n : ℕ` yields contradiction!
  have hcontra : ∀ t : ℕ, ∀ n : ℕ, k n = t → 1 ≤ k n → k n ≤ K → False := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro n hkt hk1 hkK
      obtain ⟨h1', hlt'⟩ := hdescent n hk1 hkK
      exact ih (k (n + 1)) (hkt ▸ hlt') (n + 1) rfl h1' (le_trans hlt'.le hkK)
  exact hcontra (k n₁) n₁ rfl hk_n₁_pos hk_n₁_le

/-- **Geometric-Progression Continuum-Scale Avoidance (All `q ∈ (0, 1)`)**:
For EVERY real `q ∈ (0, 1)` (rational or irrational) and EVERY lower scale cutoff `a₀ > 0`,
there exists a compact, measurable subset `E ⊆ [0, 1]` with `0 < volume E` that contains
NO affine copy `(fun x => a * x + b) '' {q^n : n ∈ ℕ}` for ANY `b : ℝ` and ANY real scale
`a : ℝ` with `a₀ ≤ |a|` (an uncountable continuum of scales). -/
theorem ppl060_geometric_bounded_scale_avoidance
    {q a₀ : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) (ha₀ : 0 < a₀) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧ 0 < volume E ∧
      ∀ a b : ℝ, a₀ ≤ |a| →
        ¬ ((fun x : ℝ => a * x + b) '' Set.range (fun n : ℕ => q ^ n) ⊆ E) := by
  classical
  let K : ℕ := Nat.ceil (1 / q) + 1
  let Bad : Finset ℕ := (Finset.Icc 1 K).filter (fun k => ¬ ∃ z : ℤ, q * (k : ℝ) = (z : ℝ))
  have h1Bad : 1 ∈ Bad := by
    simp only [Bad, Finset.mem_filter, Finset.mem_Icc, le_refl, true_and, Nat.cast_one, mul_one]
    refine ⟨by omega, ?_⟩
    rintro ⟨z, hz⟩
    have hz_pos : (0 : ℤ) < z := by exact_mod_cast (hz ▸ hq_pos)
    have hz_lt : z < (1 : ℤ) := by exact_mod_cast (hz ▸ hq_lt)
    omega
  have hBadNe : Bad.Nonempty := ⟨1, h1Bad⟩
  let dmin : ℝ := Bad.inf' hBadNe
    (fun k => min (Int.fract (q * (k : ℝ))) (1 - Int.fract (q * (k : ℝ))))
  have hdmin_pos : 0 < dmin := by
    dsimp only [dmin]
    rw [Finset.lt_inf'_iff]
    intro k hk
    have hnot : ¬ ∃ z : ℤ, q * (k : ℝ) = (z : ℝ) := (Finset.mem_filter.mp hk).2
    refine lt_min ?_ (sub_pos.mpr (Int.fract_lt_one _))
    have hnn := Int.fract_nonneg (q * (k : ℝ))
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · exfalso
      apply hnot
      refine ⟨⌊q * (k : ℝ)⌋, ?_⟩
      have : Int.fract (q * (k : ℝ)) = q * (k : ℝ) - (⌊q * (k : ℝ)⌋ : ℝ) := rfl
      linarith
    · exact hpos
  let δ : ℝ := min (1 / 5) (dmin / 2)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ_quarter : δ < 1 / 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδ_gap : ∀ k : ℕ, 1 ≤ k → k ≤ K → (¬ ∃ z : ℤ, q * (k : ℝ) = (z : ℝ)) →
      δ < min (Int.fract (q * (k : ℝ))) (1 - Int.fract (q * (k : ℝ))) := by
    intro k hk1 hkK hnot
    have hkBad : k ∈ Bad := by
      simp only [Bad, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk1, hkK⟩, hnot⟩
    have hle : dmin ≤ min (Int.fract (q * (k : ℝ))) (1 - Int.fract (q * (k : ℝ))) :=
      Finset.inf'_le _ hkBad
    have hδ_le : δ ≤ dmin / 2 := min_le_right _ _
    linarith
  let N : ℕ := Nat.ceil (1 / a₀) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hN_le : 1 / (N : ℝ) ≤ a₀ := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 : 1 / a₀ ≤ (N : ℝ) := by
      dsimp only [N]; push_cast; linarith [Nat.le_ceil (1 / a₀)]
    rw [div_le_iff₀ hNpos]
    have h2 := (div_le_iff₀ ha₀).mp h1
    linarith
  obtain ⟨hEsub, hEcomp, hEmeas, hEvol⟩ :=
    periodic_islands_properties N hN hδ_pos (by linarith)
  refine ⟨⋃ m ∈ Finset.range N, Set.Icc ((m : ℝ) / N) (((m : ℝ) + δ) / N),
    hEsub, hEcomp, hEmeas, ?_, ?_⟩
  · rw [hEvol]
    exact ENNReal.ofReal_pos.mpr hδ_pos
  · intro a b ha
    exact periodic_islands_avoid_geometric hq_pos hq_lt hδ_pos hδ_quarter hδ_gap hN
      (le_trans hN_le ha)

/-- **Dyadic Sequence `{2^{-n}}` Explicit-Measure Continuum-Scale Avoidance**:
For EVERY lower scale cutoff `a₀ > 0`, there exists a compact, measurable subset `E ⊆ [0, 1]`
with exact Lebesgue measure `volume E = ENNReal.ofReal (1 / 5)` avoiding ALL affine copies
`a * {2^{-n}} + b` for ANY `b : ℝ` and ANY real `a` with `a₀ ≤ |a|`. -/
theorem ppl060_dyadic_bounded_scale_avoidance {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasurableSet E ∧
      volume E = ENNReal.ofReal (1 / 5) ∧
      ∀ a b : ℝ, a₀ ≤ |a| →
        ¬ ((fun x : ℝ => a * x + b) '' Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ n) ⊆ E) := by
  let N : ℕ := Nat.ceil (1 / a₀) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hN_le : 1 / (N : ℝ) ≤ a₀ := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 : 1 / a₀ ≤ (N : ℝ) := by
      dsimp only [N]; push_cast; linarith [Nat.le_ceil (1 / a₀)]
    rw [div_le_iff₀ hNpos]
    have h2 := (div_le_iff₀ ha₀).mp h1
    linarith
  have hδ_gap : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.ceil (1 / (1 / 2 : ℝ)) + 1 →
      (¬ ∃ z : ℤ, (1 / 2 : ℝ) * (k : ℝ) = (z : ℝ)) →
      (1 / 5 : ℝ) < min (Int.fract ((1 / 2 : ℝ) * (k : ℝ)))
                        (1 - Int.fract ((1 / 2 : ℝ) * (k : ℝ))) := by
    intro k hk1 hkK hnot
    have hK : Nat.ceil (1 / (1 / 2 : ℝ)) + 1 = 3 := by
      have h2 : (1 / (1 / 2 : ℝ)) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h2, Nat.ceil_natCast]
    rw [hK] at hkK
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · have hf : Int.fract ((1 / 2 : ℝ) * ((1 : ℕ) : ℝ)) = 1 / 2 := by
        rw [Nat.cast_one, mul_one, Int.fract_eq_self.mpr (by constructor <;> norm_num)]
      rw [hf]; norm_num
    · exfalso; exact hnot ⟨1, by norm_num⟩
    · have hf : Int.fract ((1 / 2 : ℝ) * ((3 : ℕ) : ℝ)) = 1 / 2 := by
        have hfl : ⌊(1 / 2 : ℝ) * ((3 : ℕ) : ℝ)⌋ = 1 := by
          rw [Int.floor_eq_iff]; norm_num
        show (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) - (⌊(1 / 2 : ℝ) * ((3 : ℕ) : ℝ)⌋ : ℝ) = 1 / 2
        rw [hfl]; norm_num
      rw [hf]; norm_num
  obtain ⟨hEsub, hEcomp, hEmeas, hEvol⟩ :=
    periodic_islands_properties N hN (by norm_num : (0 : ℝ) < 1 / 5) (by norm_num)
  refine ⟨⋃ m ∈ Finset.range N, Set.Icc ((m : ℝ) / N) (((m : ℝ) + 1 / 5) / N),
    hEsub, hEcomp, hEmeas, hEvol, fun a b ha => ?_⟩
  exact periodic_islands_avoid_geometric (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hδ_gap hN (le_trans hN_le ha)

end PPL060
