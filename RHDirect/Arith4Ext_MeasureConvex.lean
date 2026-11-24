/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Arith4Ext.MeasureConvex: Convex Geometry, Loomis–Whitney, Steinhaus & Brunn–Minkowski

Reusable Tier A `Arithmetica4` library module built from scratch on targeted Mathlib imports,
providing convex geometry, projection inequalities, and 1D measure/sumset theorems in
`namespace Arith4Ext.MeasureConvex`:

1. **Carathéodory, Convex Diameter, Radon & Helly (`Section 1`):**
   - `caratheodory_finrank`, `caratheodory_fin`, `caratheodory_euclidean`: Carathéodory's theorem
     representing every point of `convexHull ℝ s` using at most `dim + 1` points of `s`.
   - `convexHull_diam_bound`: diameter preservation under `convexHull ℝ`.
   - `radon_lemma`, `radon_lemma_fin`: Radon's partition theorem for `≥ dim + 2` points.
   - `helly_theorem`, `helly_theorem_fin`, `helly_theorem_euclidean`: Helly's intersection theorem
     for finite families of convex sets in `ℝ^d`.

2. **Loomis–Whitney Projection Inequalities (`Section 2`):**
   - `loomis_whitney_2d`, `loomis_whitney_3d`, `loomis_whitney_fin`, `loomis_whitney_rpow`:
     discrete Loomis–Whitney inequalities `|S|^{d-1} ≤ ∏_i |π_i(S)|` for `2D`, `3D`, and
     arbitrary dimension `d ≥ 2`, plus the `(1/(d-1))`-power real form.

3. **Steinhaus Theorem & Difference-Set Measure Corollaries (`Section 3`):**
   - `steinhaus_pos_volume_shift`: for measurable `A ⊆ ℝ` with `0 < volume A < ∞`, there exists
     `δ > 0` such that every `t ∈ (-δ, δ)` gives `0 < volume ((t +ᵥ A) ∩ A)`.
   - `steinhaus_finite`, `steinhaus`, `steinhaus_ball`: `(-δ, δ) ⊆ A - A` for every measurable
     `A ⊆ ℝ` with `0 < volume A` (both finite and infinite volume).

4. **1D Brunn–Minkowski & Discrete Sumset Bounds (`Section 4`):**
   - `discrete_sumset_int`, `discrete_sumset_real`: Cauchy–Davenport-style ordered sumset bound
     `|A| + |B| - 1 ≤ |A + B|` on `Finset ℤ` and `Finset ℝ`.
   - `brunn_minkowski_1d_compact`, `brunn_minkowski_1d`, `brunn_minkowski_1d_sub`,
     `brunn_minkowski_intervals`: continuous 1D Brunn–Minkowski inequality
     `volume A + volume B ≤ volume (A + B)` for all nonempty measurable `A, B ⊆ ℝ`.

All public declarations use strictly pure-Mathlib signatures (`0` custom public types or proxies).
-/

namespace Arith4Ext.MeasureConvex

open scoped BigOperators Pointwise

/-! ## Section 1: Carathéodory, Quantitative Hull Diameter, Radon & Helly -/

section ConvexGeometry

/-- **Carathéodory's Theorem** in any finite-dimensional real vector space `V`:
every point in `convexHull ℝ s` lies in the convex hull of at most `finrank ℝ V + 1` points
of `s`. -/
theorem caratheodory_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} {x : V} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset V, (t : Set V) ⊆ s ∧ t.card ≤ Module.finrank ℝ V + 1 ∧
      x ∈ convexHull ℝ (t : Set V) := by
  classical
  rw [convexHull_eq_union] at hx
  rcases Set.mem_iUnion.mp hx with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨hts, ht'⟩
  rcases Set.mem_iUnion.mp ht' with ⟨haff, hxt⟩
  refine ⟨t, hts, ?_, hxt⟩
  by_cases hne : t.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    have hli : LinearIndependent ℝ (fun v : {v : t // v ≠ ⟨v₀, hv₀⟩} => (v.1 : V) -ᵥ v₀) := by
      have hsub := (affineIndependent_iff_linearIndependent_vsub ℝ (Subtype.val : t → V)
        ⟨v₀, hv₀⟩).mp haff
      exact hsub
    have hcard_sub : Fintype.card {v : t // v ≠ ⟨v₀, hv₀⟩} ≤ Module.finrank ℝ V :=
      hli.fintype_card_le_finrank
    have hcard_t : Fintype.card t = Fintype.card {v : t // v ≠ ⟨v₀, hv₀⟩} + 1 := by
      have hpos_t : 0 < Fintype.card t := Fintype.card_pos_iff.mpr ⟨⟨v₀, hv₀⟩⟩
      rw [Fintype.card_subtype_compl]
      have h1 : Fintype.card {v : t // v = ⟨v₀, hv₀⟩} = 1 := by
        rw [Fintype.card_eq_one_iff]
        exact ⟨⟨⟨v₀, hv₀⟩, rfl⟩, fun ⟨y, hy⟩ => Subtype.ext hy⟩
      omega
    rw [Fintype.card_coe] at hcard_t
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    omega

/-- Carathéodory's Theorem specialized to `Fin d → ℝ`. -/
theorem caratheodory_fin {d : ℕ} {s : Set (Fin d → ℝ)} {x : Fin d → ℝ}
    (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset (Fin d → ℝ), (t : Set (Fin d → ℝ)) ⊆ s ∧ t.card ≤ d + 1 ∧
      x ∈ convexHull ℝ (t : Set (Fin d → ℝ)) := by
  simpa [Module.finrank_fin_fun] using caratheodory_finrank hx

/-- Carathéodory's Theorem specialized to `EuclideanSpace ℝ (Fin d)`. -/
theorem caratheodory_euclidean {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)), (t : Set (EuclideanSpace ℝ (Fin d))) ⊆ s ∧
      t.card ≤ d + 1 ∧ x ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin d))) := by
  simpa [finrank_euclideanSpace_fin] using caratheodory_finrank hx

private lemma convex_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) (D : ℝ) : Convex ℝ {z : E | ‖z - c‖ ≤ D} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hsplit : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    calc a • x + b • y - c
        = a • x + b • y - (a + b) • c := by rw [hab, one_smul]
      _ = a • (x - c) + b • (y - c) := by rw [add_smul, smul_sub, smul_sub]; abel
  calc ‖a • x + b • y - c‖
      = ‖a • (x - c) + b • (y - c)‖ := by rw [hsplit]
    _ ≤ ‖a • (x - c)‖ + ‖b • (y - c)‖ := norm_add_le _ _
    _ = a * ‖x - c‖ + b * ‖y - c‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * D + b * D := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
    _ = D := by rw [← add_mul, hab, one_mul]

/-- Quantitative convex-hull diameter bound: if every pair of points in `s` has distance `≤ D`,
then every pair of points in `convexHull ℝ s` also has distance `≤ D`. -/
theorem convexHull_diam_bound {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {D : ℝ} (hs : ∀ a ∈ s, ∀ b ∈ s, ‖a - b‖ ≤ D)
    {x y : E} (hx : x ∈ convexHull ℝ s) (hy : y ∈ convexHull ℝ s) :
    ‖x - y‖ ≤ D := by
  have hx_mem : ∀ b ∈ s, ‖x - b‖ ≤ D := fun b hb =>
    convexHull_min (fun a ha => hs a ha b hb) (convex_norm_sub_le b D) hx
  have hconv_x : Convex ℝ {z : E | ‖x - z‖ ≤ D} := by
    simpa [norm_sub_rev] using convex_norm_sub_le x D
  exact convexHull_min (fun b hb => hx_mem b hb) hconv_x hy

/-- **Radon's Lemma** in any finite-dimensional real vector space `V`:
any family `p : ι → V` with `Module.finrank ℝ V + 2 ≤ Fintype.card ι` partitions into
nonempty disjoint sets `I, J` whose convex hulls intersect. -/
theorem radon_lemma {V ι : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] [DecidableEq ι] (hcard : Module.finrank ℝ V + 2 ≤ Fintype.card ι)
    (p : ι → V) :
    ∃ I J : Finset ι, Disjoint I J ∧ I ∪ J = Finset.univ ∧ I.Nonempty ∧ J.Nonempty ∧
      (convexHull ℝ (p '' (I : Set ι)) ∩ convexHull ℝ (p '' (J : Set ι))).Nonempty := by
  let L : (ι → ℝ) →ₗ[ℝ] (V × ℝ) :=
    { toFun := fun c => (∑ i : ι, c i • p i, ∑ i : ι, c i)
      map_add' := fun a b => by
        ext <;> simp [Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        ext <;> simp [Finset.smul_sum, mul_smul, smul_eq_mul, Finset.mul_sum] }
  have hfin_dom : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by simp
  have hfin_cod : Module.finrank ℝ (V × ℝ) = Module.finrank ℝ V + 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker L) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker L
    have hrange : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ (V × ℝ) :=
      Submodule.finrank_le (LinearMap.range L)
    omega
  have hker_nontriv : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    omega
  obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_nontriv
  have hc_sum_vec : ∑ i : ι, c i • p i = 0 := by
    simpa [L] using congrArg Prod.fst hc_mem
  have hc_sum_sca : ∑ i : ι, c i = 0 := by
    simpa [L] using congrArg Prod.snd hc_mem
  let I : Finset ι := Finset.univ.filter (fun i => 0 < c i)
  let J : Finset ι := Finset.univ.filter (fun i => c i ≤ 0)
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [I, J, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    linarith
  have hunion : I ∪ J = Finset.univ := by
    ext i
    simp only [I, J, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact lt_or_ge 0 (c i)
  have hI_pos : 0 < ∑ i ∈ I, c i := by
    by_contra hle
    push Not at hle
    have hI_nonneg : ∀ i ∈ I, 0 ≤ c i := fun i hi => by
      simp only [I, Finset.mem_filter] at hi; exact hi.2.le
    have hI_zero : ∑ i ∈ I, c i = 0 := le_antisymm hle (Finset.sum_nonneg hI_nonneg)
    have hI_all_zero : ∀ i ∈ I, c i = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff_of_nonneg hI_nonneg).mp hI_zero i hi
    have hJ_sum : ∑ j ∈ J, c j = 0 := by
      have hpart : ∑ i ∈ I, c i + ∑ j ∈ J, c j = ∑ i : ι, c i := by
        rw [← Finset.sum_union hdisj, hunion]
      linarith
    have hJ_nonpos : ∀ j ∈ J, c j ≤ 0 := fun j hj => by
      simp only [J, Finset.mem_filter] at hj; exact hj.2
    have hJ_neg_sum : ∑ j ∈ J, (-c j) = 0 := by
      simp [Finset.sum_neg_distrib, hJ_sum]
    have hJ_all_zero : ∀ j ∈ J, c j = 0 := fun j hj => by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => neg_nonneg.mpr (hJ_nonpos k hk))).mp
        hJ_neg_sum j hj
      linarith
    apply hc_ne
    ext i
    have hi : i ∈ I ∪ J := by rw [hunion]; exact Finset.mem_univ i
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact hI_all_zero i hiI
    · exact hJ_all_zero i hiJ
  let S : ℝ := ∑ i ∈ I, c i
  have hS_pos : 0 < S := hI_pos
  have hJ_neg_S : ∑ j ∈ J, (-c j) = S := by
    have hpart : ∑ i ∈ I, c i + ∑ j ∈ J, c j = ∑ i : ι, c i := by
      rw [← Finset.sum_union hdisj, hunion]
    have : ∑ j ∈ J, c j = -S := by linarith
    simp [Finset.sum_neg_distrib, this]
  have hI_ne : I.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hI_pos
    linarith
  have hJ_ne : J.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hJ_neg_S
    linarith
  let x : V := ∑ i ∈ I, (c i / S) • p i
  have hx_eq_J : x = ∑ j ∈ J, ((-c j) / S) • p j := by
    have hpart : ∑ i ∈ I, c i • p i + ∑ j ∈ J, c j • p j = ∑ i : ι, c i • p i := by
      rw [← Finset.sum_union hdisj, hunion]
    have hneg : ∑ i ∈ I, c i • p i = ∑ j ∈ J, (-c j) • p j := by
      have h1 : ∑ i ∈ I, c i • p i = - ∑ j ∈ J, c j • p j := eq_neg_of_add_eq_zero_left (by
        rw [hpart, hc_sum_vec])
      rw [h1, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [neg_smul]
    calc x = (S⁻¹) • ∑ i ∈ I, c i • p i := by
            simp only [x, Finset.smul_sum, smul_smul, div_eq_inv_mul]
      _ = (S⁻¹) • ∑ j ∈ J, (-c j) • p j := by rw [hneg]
      _ = ∑ j ∈ J, ((-c j) / S) • p j := by
            simp only [Finset.smul_sum, smul_smul, div_eq_inv_mul]
  have hx_I : x ∈ convexHull ℝ (p '' (I : Set ι)) := by
    have hw_nonneg : ∀ i ∈ I, 0 ≤ c i / S := fun i hi => by
      simp only [I, Finset.mem_filter] at hi
      exact div_nonneg hi.2.le hS_pos.le
    have hw_sum : ∑ i ∈ I, c i / S = 1 := by
      rw [← Finset.sum_div]
      exact div_self hS_pos.ne'
    have hcm := I.centerMass_mem_convexHull hw_nonneg (by rw [hw_sum]; norm_num)
      (fun i hi => Set.mem_image_of_mem p hi)
    have hx_cm : x = I.centerMass (fun i => c i / S) p := by
      simp [Finset.centerMass, hw_sum, x]
    rw [hx_cm]
    exact hcm
  have hx_J : x ∈ convexHull ℝ (p '' (J : Set ι)) := by
    have hw_nonneg : ∀ j ∈ J, 0 ≤ (-c j) / S := fun j hj => by
      simp only [J, Finset.mem_filter] at hj
      exact div_nonneg (neg_nonneg.mpr hj.2) hS_pos.le
    have hw_sum : ∑ j ∈ J, (-c j) / S = 1 := by
      rw [← Finset.sum_div, hJ_neg_S]
      exact div_self hS_pos.ne'
    have hcm := J.centerMass_mem_convexHull hw_nonneg (by rw [hw_sum]; norm_num)
      (fun j hj => Set.mem_image_of_mem p hj)
    have hx_cm : x = J.centerMass (fun j => (-c j) / S) p := by
      simp [Finset.centerMass, hw_sum, hx_eq_J]
    rw [hx_cm]
    exact hcm
  exact ⟨I, J, hdisj, hunion, hI_ne, hJ_ne, x, hx_I, hx_J⟩

/-- Radon's Lemma specialized to `d + 2` points in `Fin d → ℝ`. -/
theorem radon_lemma_fin {d : ℕ} (p : Fin (d + 2) → (Fin d → ℝ)) :
    ∃ I J : Finset (Fin (d + 2)), Disjoint I J ∧ I ∪ J = Finset.univ ∧
      I.Nonempty ∧ J.Nonempty ∧
      (convexHull ℝ (p '' (I : Set (Fin (d + 2)))) ∩
        convexHull ℝ (p '' (J : Set (Fin (d + 2))))).Nonempty :=
  radon_lemma (by simp) p

private lemma helly_aux {V ι : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [DecidableEq ι] (C : ι → Set V) (hconv : ∀ i : ι, Convex ℝ (C i)) :
    ∀ k : ℕ, ∀ s : Finset ι, s.card = k →
      (∀ t ⊆ s, t.card ≤ Module.finrank ℝ V + 1 → (⋂ i ∈ t, C i).Nonempty) →
      (⋂ i ∈ s, C i).Nonempty := by
  intro k
  induction k with
  | zero =>
    intro s hs _
    rw [Finset.card_eq_zero.mp hs]
    exact ⟨0, by simp⟩
  | succ k ih =>
    intro s hs hsub
    by_cases hle : s.card ≤ Module.finrank ℝ V + 1
    · exact hsub s Finset.Subset.rfl hle
    have hge : Module.finrank ℝ V + 2 ≤ s.card := by omega
    have herase : ∀ i ∈ s, (⋂ j ∈ s.erase i, C j).Nonempty := by
      intro i hi
      refine ih (s.erase i) (by rw [Finset.card_erase_of_mem hi, hs]; simp) ?_
      intro t ht ht_card
      exact hsub t (ht.trans (Finset.erase_subset i s)) ht_card
    choose p hp using fun i : s => herase i.1 i.2
    have hcard_s : Module.finrank ℝ V + 2 ≤ Fintype.card s := by
      rw [Fintype.card_coe]; exact hge
    obtain ⟨I, J, hdisj, hunion, _, _, x, hxI, hxJ⟩ := radon_lemma hcard_s p
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro r hr
    have hr' : (⟨r, hr⟩ : s) ∈ I ∪ J := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hr' with hrI | hrJ
    · have hr_notJ : (⟨r, hr⟩ : s) ∉ J := Finset.disjoint_left.mp hdisj hrI
      have hJ_sub : p '' (J : Set s) ⊆ C r := by
        rintro _ ⟨j, hj, rfl⟩
        have hj_ne : j.1 ≠ r := fun heq => hr_notJ (by
          have : j = ⟨r, hr⟩ := Subtype.ext heq
          simpa [this] using hj)
        have hmem := hp j
        simp only [Set.mem_iInter] at hmem
        exact hmem r (Finset.mem_erase.mpr ⟨hj_ne.symm, hr⟩)
      exact convexHull_min hJ_sub (hconv r) hxJ
    · have hr_notI : (⟨r, hr⟩ : s) ∉ I := Finset.disjoint_right.mp hdisj hrJ
      have hI_sub : p '' (I : Set s) ⊆ C r := by
        rintro _ ⟨i, hi, rfl⟩
        have hi_ne : i.1 ≠ r := fun heq => hr_notI (by
          have : i = ⟨r, hr⟩ := Subtype.ext heq
          simpa [this] using hi)
        have hmem := hp i
        simp only [Set.mem_iInter] at hmem
        exact hmem r (Finset.mem_erase.mpr ⟨hi_ne.symm, hr⟩)
      exact convexHull_min hI_sub (hconv r) hxI

/-- **Helly's Theorem** in any finite-dimensional real vector space `V`:
if `{C i | i : ι}` is a finite family of convex sets in `V` such that every subfamily of
at most `finrank ℝ V + 1` sets has nonempty intersection, then the entire family has nonempty
intersection. -/
theorem helly_theorem {V ι : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] [DecidableEq ι] (C : ι → Set V) (hconv : ∀ i : ι, Convex ℝ (C i))
    (hsub : ∀ t : Finset ι, t.card ≤ Module.finrank ℝ V + 1 → (⋂ i ∈ t, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty := by
  have hall := helly_aux C hconv (Finset.univ : Finset ι).card Finset.univ rfl
    (fun t _ ht => hsub t ht)
  simpa using hall

/-- Helly's Theorem specialized to `Fin d → ℝ`. -/
theorem helly_theorem_fin {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Set (Fin d → ℝ)) (hconv : ∀ i : ι, Convex ℝ (C i))
    (hsub : ∀ t : Finset ι, t.card ≤ d + 1 → (⋂ i ∈ t, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty :=
  helly_theorem C hconv (by simpa [Module.finrank_fin_fun] using hsub)

/-- Helly's Theorem specialized to `EuclideanSpace ℝ (Fin d)`. -/
theorem helly_theorem_euclidean {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Set (EuclideanSpace ℝ (Fin d))) (hconv : ∀ i : ι, Convex ℝ (C i))
    (hsub : ∀ t : Finset ι, t.card ≤ d + 1 → (⋂ i ∈ t, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty :=
  helly_theorem C hconv (by simpa [finrank_euclideanSpace_fin] using hsub)

end ConvexGeometry

/-! ## Section 2: Loomis–Whitney Projection Inequalities -/

section LoomisWhitney

/-- **2D Loomis–Whitney / Rectangular Projection Bound**: `|S| ≤ |π₁(S)| · |π₂(S)|`. -/
theorem loomis_whitney_2d {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) :
    S.card ≤ (S.image Prod.fst).card * (S.image Prod.snd).card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card fun p hp => ?_
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩

private lemma holder_inv_dim {α : Type*} {d : ℕ} (hd : 0 < d) (X : Finset α)
    (f : Fin d → α → ℝ) (hf : ∀ j x, 0 ≤ f j x) :
    ∑ x ∈ X, ∏ j : Fin d, (f j x) ^ ((1 : ℝ) / d) ≤
      ∏ j : Fin d, (∑ x ∈ X, f j x) ^ ((1 : ℝ) / d) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  by_cases hzero : ∃ j : Fin d, ∑ x ∈ X, f j x = 0
  · rcases hzero with ⟨j₀, hj₀⟩
    have hj₀_each : ∀ x ∈ X, f j₀ x = 0 := fun x hx =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hf j₀ y)).mp hj₀ x hx
    have hL : ∑ x ∈ X, ∏ j : Fin d, (f j x) ^ ((1 : ℝ) / d) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
      rw [hj₀_each x hx, Real.zero_rpow (one_div_ne_zero hd_ne)]
    have hR : ∏ j : Fin d, (∑ x ∈ X, f j x) ^ ((1 : ℝ) / d) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
      rw [hj₀, Real.zero_rpow (one_div_ne_zero hd_ne)]
    rw [hL, hR]
  push Not at hzero
  have hA_pos : ∀ j : Fin d, 0 < ∑ x ∈ X, f j x := fun j =>
    lt_of_le_of_ne (Finset.sum_nonneg fun x _ => hf j x) (Ne.symm (hzero j))
  let A : Fin d → ℝ := fun j => ∑ x ∈ X, f j x
  let P : ℝ := ∏ j : Fin d, (A j) ^ ((1 : ℝ) / d)
  have hP_pos : 0 < P :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hA_pos j) _
  have hnorm_sum : ∑ x ∈ X, ∏ j : Fin d, (f j x / A j) ^ ((1 : ℝ) / d) ≤ 1 := by
    have ham : ∀ x ∈ X, ∏ j : Fin d, (f j x / A j) ^ ((1 : ℝ) / d) ≤
        ∑ j : Fin d, ((1 : ℝ) / d) * (f j x / A j) := fun x _ =>
      Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / d)
        (fun j => f j x / A j) (fun _ _ => by positivity)
        (by simp [Finset.card_univ, mul_inv_cancel₀ hd_ne])
        (fun j _ => div_nonneg (hf j x) (hA_pos j).le)
    calc ∑ x ∈ X, ∏ j : Fin d, (f j x / A j) ^ ((1 : ℝ) / d)
        ≤ ∑ x ∈ X, ∑ j : Fin d, ((1 : ℝ) / d) * (f j x / A j) := Finset.sum_le_sum ham
      _ = ∑ j : Fin d, ∑ x ∈ X, ((1 : ℝ) / d) * (f j x / A j) := Finset.sum_comm
      _ = ∑ j : Fin d, ((1 : ℝ) / d) * ((∑ x ∈ X, f j x) / A j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.mul_sum, ← Finset.sum_div]
      _ = ∑ j : Fin d, ((1 : ℝ) / d) * 1 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [div_self (hA_pos j).ne']
      _ = 1 := by simp [Finset.card_univ, mul_inv_cancel₀ hd_ne]
  have hscale : ∑ x ∈ X, ∏ j : Fin d, (f j x) ^ ((1 : ℝ) / d) =
      P * ∑ x ∈ X, ∏ j : Fin d, (f j x / A j) ^ ((1 : ℝ) / d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only [P]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.div_rpow (hf j x) (hA_pos j).le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos (hA_pos j) _).ne']
  rw [hscale]
  calc P * ∑ x ∈ X, ∏ j : Fin d, (f j x / A j) ^ ((1 : ℝ) / d)
      ≤ P * 1 := mul_le_mul_of_nonneg_left hnorm_sum hP_pos.le
    _ = P := mul_one P

private lemma succAbove_succ_zero {d : ℕ} (j : Fin (d + 1)) :
    j.succ.succAbove 0 = 0 := by
  simp [Fin.succAbove, Fin.lt_def]

private lemma succAbove_succ_succ {d : ℕ} (j : Fin (d + 1)) (k : Fin d) :
    j.succ.succAbove k.succ = (j.succAbove k).succ := by
  simp only [Fin.succAbove]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    apply h2
    exact Fin.succ_lt_succ_iff.mp h1
  · exfalso
    apply h1
    exact Fin.succ_lt_succ_iff.mpr h2
  · rfl

private lemma prod_rpow_inv_pow {ι : Type*} (s : Finset ι) (d : ℕ) (hd : (d : ℝ) ≠ 0)
    (g : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∏ i ∈ s, (g i) ^ ((1 : ℝ) / d)) ^ d = ∏ i ∈ s, g i := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Real.rpow_natCast ((g i) ^ ((1 : ℝ) / d)) d, ← Real.rpow_mul (hg i hi),
      one_div_mul_cancel hd, Real.rpow_one]

private lemma loomis_whitney_succ_two : ∀ m : ℕ,
    ∀ (α : Type*) [DecidableEq α] (S : Finset (Fin (m + 2) → α)),
      S.card ^ (m + 1) ≤ ∏ i : Fin (m + 2), (S.image (fun x j => x (i.succAbove j))).card := by
  intro m
  induction m with
  | zero =>
    intro α _ S
    change S.card ^ 1 ≤ ∏ i : Fin 2, (S.image (fun x j => x (i.succAbove j))).card
    simp only [pow_one, Fin.prod_univ_two]
    let π₀ : (Fin 2 → α) → α := fun x => x 0
    let π₁ : (Fin 2 → α) → α := fun x => x 1
    have hsub : S.image (fun x => (x 0, x 1)) ⊆ S.image π₀ ×ˢ S.image π₁ := by
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_image] at hab
      rcases hab with ⟨x, hx, hxy⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem π₀ hx, Finset.mem_image_of_mem π₁ hx⟩
    have hinj : Function.Injective (fun x : Fin 2 → α => (x 0, x 1)) := by
      intro x y hxy
      ext i
      fin_cases i
      · exact congrArg Prod.fst hxy
      · exact congrArg Prod.snd hxy
    have hcard_eq : S.card ≤ (S.image π₀).card * (S.image π₁).card := by
      calc S.card
          = (S.image (fun x => (x 0, x 1))).card := (Finset.card_image_of_injective S hinj).symm
        _ ≤ (S.image π₀ ×ˢ S.image π₁).card := Finset.card_le_card hsub
        _ = (S.image π₀).card * (S.image π₁).card := Finset.card_product _ _
    have hc0 : (S.image (fun x (j : Fin 1) => x ((0 : Fin 2).succAbove j))).card =
        (S.image π₁).card := by
      have hbi : (S.image (fun x (j : Fin 1) => x ((0 : Fin 2).succAbove j))).card =
          ((S.image (fun x (j : Fin 1) => x ((0 : Fin 2).succAbove j))).image (fun y => y 0)).card := by
        symm
        refine Finset.card_image_of_injective _ ?_
        intro u v huv; ext j; fin_cases j; exact huv
      rw [hbi, Finset.image_image]
      congr 2
    have hc1 : (S.image (fun x (j : Fin 1) => x ((1 : Fin 2).succAbove j))).card =
        (S.image π₀).card := by
      have hbi : (S.image (fun x (j : Fin 1) => x ((1 : Fin 2).succAbove j))).card =
          ((S.image (fun x (j : Fin 1) => x ((1 : Fin 2).succAbove j))).image (fun y => y 0)).card := by
        symm
        refine Finset.card_image_of_injective _ ?_
        intro u v huv; ext j; fin_cases j; exact huv
      rw [hbi, Finset.image_image]
      congr 2
    rw [hc0, hc1, mul_comm]
    exact hcard_eq
  | succ m ih =>
    intro α _ S
    let d := m + 2
    have hd_pos : 0 < d := by omega
    have hd_real_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
    have hd_real_ne : (d : ℝ) ≠ 0 := hd_real_pos.ne'
    let drop : Fin (d + 1) → (Fin (d + 1) → α) → (Fin d → α) := fun i x j => x (i.succAbove j)
    let P : Fin (d + 1) → Finset (Fin d → α) := fun i => S.image (drop i)
    let X : Finset α := S.image (fun x => x 0)
    let slice : α → Finset (Fin d → α) := fun a =>
      (P 0).filter (fun y => Fin.cons a y ∈ S)
    have hcard_S : S.card = ∑ a ∈ X, (slice a).card := by
      let pairs := S.image (fun x => (x 0, Fin.tail x))
      have hinj : Function.Injective (fun x : Fin (d + 1) → α => (x 0, Fin.tail x)) := by
        intro x y hxy
        ext i
        refine Fin.cases (congrArg Prod.fst hxy) (fun j => ?_) i
        exact congrFun (congrArg Prod.snd hxy) j
      have hmaps : Set.MapsTo Prod.fst (pairs : Set (α × (Fin d → α))) (X : Set α) := by
        intro p hp
        simp only [Finset.mem_coe, pairs, Finset.mem_image, X] at hp ⊢
        rcases hp with ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      rw [← Finset.card_image_of_injective S hinj]
      change pairs.card = ∑ a ∈ X, (slice a).card
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      refine Finset.sum_congr rfl fun a ha => ?_
      have himg_fib : pairs.filter (fun p => p.1 = a) =
          (slice a).map ⟨fun y => (a, y), fun _ _ h => congrArg Prod.snd h⟩ := by
        ext ⟨a', y⟩
        simp only [Finset.mem_filter, pairs, Finset.mem_image, Finset.mem_map, slice, P, drop]
        constructor
        · rintro ⟨⟨x, hx, hxy⟩, rfl⟩
          obtain ⟨h0, htail⟩ := Prod.mk.inj hxy
          refine ⟨Fin.tail x, ⟨⟨x, hx, ?_⟩, ?_⟩, ?_⟩
          · ext j; rfl
          · convert hx using 1; ext i; refine Fin.cases (by simp [h0]) (fun j => rfl) i
          · simp [← h0, htail]
        · rintro ⟨y', ⟨⟨_, hcons⟩, hy'⟩⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy'
          exact ⟨⟨Fin.cons a y', hcons, by simp⟩, rfl⟩
      rw [himg_fib, Finset.card_map]
    have hslice_le_P0 : ∀ a ∈ X, (slice a).card ≤ (P 0).card := fun a _ =>
      Finset.card_le_card (Finset.filter_subset _ _)
    let fiber : Fin d → α → Finset (Fin (m + 1) → α) := fun j a =>
      (slice a).image (fun y k => y (j.succAbove k))
    have hfiber_sum : ∀ j : Fin d, ∑ a ∈ X, (fiber j a).card = (P j.succ).card := by
      intro j
      let pairsJ := (P j.succ).image (fun z => (z 0, Fin.tail z))
      have hinjJ : Function.Injective (fun z : Fin d → α => (z 0, Fin.tail z)) := by
        intro z₁ z₂ hz
        ext i
        refine Fin.cases (congrArg Prod.fst hz) (fun k => ?_) i
        exact congrFun (congrArg Prod.snd hz) k
      have hmapsJ : Set.MapsTo Prod.fst (pairsJ : Set (α × (Fin (m + 1) → α))) (X : Set α) := by
        intro p hp
        simp only [Finset.mem_coe, pairsJ, Finset.mem_image, P, drop, X] at hp ⊢
        rcases hp with ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      rw [← Finset.card_image_of_injective (P j.succ) hinjJ]
      change ∑ a ∈ X, (fiber j a).card = pairsJ.card
      rw [Finset.card_eq_sum_card_fiberwise hmapsJ]
      refine Finset.sum_congr rfl fun a ha => ?_
      have himg_fib : pairsJ.filter (fun p => p.1 = a) =
          (fiber j a).map ⟨fun w => (a, w), fun _ _ h => congrArg Prod.snd h⟩ := by
        ext ⟨a', w⟩
        simp only [Finset.mem_filter, pairsJ, Finset.mem_image, Finset.mem_map, fiber, slice, P, drop]
        constructor
        · rintro ⟨⟨z, ⟨x, hx, rfl⟩, hzw⟩, rfl⟩
          obtain ⟨h0, htail⟩ := Prod.mk.inj hzw
          have hx0 : x 0 = a' := by simpa [succAbove_succ_zero] using h0
          refine ⟨Fin.tail (fun r => x (j.succ.succAbove r)), ⟨Fin.tail x, ⟨⟨x, hx, ?_⟩, ?_⟩, ?_⟩, ?_⟩
          · ext r; rfl
          · convert hx using 1; ext i; refine Fin.cases (by simp [hx0]) (fun r => rfl) i
          · ext k; simp [Fin.tail]
          · exact Prod.ext (by simp [← h0]) htail
        · rintro ⟨w', ⟨y, ⟨_, hcons⟩, hw'⟩, hy'⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy'
          refine ⟨⟨drop j.succ (Fin.cons a y), ⟨Fin.cons a y, hcons, rfl⟩, ?_⟩, rfl⟩
          ext
          · simp [drop]
          · simp [Fin.tail, drop, ← hw']
      rw [himg_fib, Finset.card_map]
    have hih_slice : ∀ a : α, ((slice a).card : ℝ) ^ (m + 1) ≤
        ∏ j : Fin d, ((fiber j a).card : ℝ) := fun a => by
      exact_mod_cast ih α (slice a)
    have hrpow_slice : ∀ a ∈ X, ((slice a).card : ℝ) ≤
        ((P 0).card : ℝ) ^ ((1 : ℝ) / d) *
          ∏ j : Fin d, ((fiber j a).card : ℝ) ^ ((1 : ℝ) / d) := by
      intro a ha
      have hs0 : (0 : ℝ) ≤ (slice a).card := Nat.cast_nonneg _
      have h1 : ((slice a).card : ℝ) ^ ((1 : ℝ) / d) ≤ ((P 0).card : ℝ) ^ ((1 : ℝ) / d) :=
        Real.rpow_le_rpow hs0 (by exact_mod_cast hslice_le_P0 a ha) (by positivity)
      have h2 : ((slice a).card : ℝ) ^ ((m + 1 : ℝ) / d) ≤
          ∏ j : Fin d, ((fiber j a).card : ℝ) ^ ((1 : ℝ) / d) := by
        have hp_le : (((slice a).card : ℝ) ^ (m + 1)) ^ ((1 : ℝ) / d) ≤
            (∏ j : Fin d, ((fiber j a).card : ℝ)) ^ ((1 : ℝ) / d) :=
          Real.rpow_le_rpow (pow_nonneg hs0 _) (hih_slice a) (by positivity)
        rw [← Real.rpow_natCast ((slice a).card : ℝ) (m + 1), ← Real.rpow_mul hs0,
            Nat.cast_add, Nat.cast_one, mul_one_div] at hp_le
        have hprod_eq : (∏ j : Fin d, ((fiber j a).card : ℝ)) ^ ((1 : ℝ) / d) =
            ∏ j : Fin d, ((fiber j a).card : ℝ) ^ ((1 : ℝ) / d) :=
          (Real.finsetProd_rpow Finset.univ (fun j => ((fiber j a).card : ℝ))
            (fun _ _ => Nat.cast_nonneg _) ((1 : ℝ) / d)).symm
        rw [hprod_eq] at hp_le
        exact hp_le
      have hsplit : ((slice a).card : ℝ) =
          ((slice a).card : ℝ) ^ ((1 : ℝ) / d) *
            ((slice a).card : ℝ) ^ ((m + 1 : ℝ) / d) := by
        by_cases hcz : (slice a).card = 0
        · simp [hcz]
        · have hc_pos : (0 : ℝ) < (slice a).card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcz)
          rw [← Real.rpow_add hc_pos]
          have hexp : (1 : ℝ) / d + (m + 1 : ℝ) / d = 1 := by
            have hd_eq : (d : ℝ) = (m : ℝ) + 2 := by push_cast [d]; ring
            field_simp [hd_real_ne]
            linarith
          rw [hexp, Real.rpow_one]
      rw [hsplit]
      exact mul_le_mul h1 h2 (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum_real : (S.card : ℝ) ≤
        ((P 0).card : ℝ) ^ ((1 : ℝ) / d) *
          ∏ j : Fin d, ((P j.succ).card : ℝ) ^ ((1 : ℝ) / d) := by
      have hS_eq : (S.card : ℝ) = ∑ a ∈ X, ((slice a).card : ℝ) := by exact_mod_cast hcard_S
      rw [hS_eq]
      calc ∑ a ∈ X, ((slice a).card : ℝ)
          ≤ ∑ a ∈ X, ((P 0).card : ℝ) ^ ((1 : ℝ) / d) *
              ∏ j : Fin d, ((fiber j a).card : ℝ) ^ ((1 : ℝ) / d) :=
                Finset.sum_le_sum hrpow_slice
        _ = ((P 0).card : ℝ) ^ ((1 : ℝ) / d) *
              ∑ a ∈ X, ∏ j : Fin d, ((fiber j a).card : ℝ) ^ ((1 : ℝ) / d) := by
                rw [← Finset.mul_sum]
        _ ≤ ((P 0).card : ℝ) ^ ((1 : ℝ) / d) *
              ∏ j : Fin d, (∑ a ∈ X, ((fiber j a).card : ℝ)) ^ ((1 : ℝ) / d) := by
                refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
                exact holder_inv_dim hd_pos X (fun j a => ((fiber j a).card : ℝ))
                  (fun _ _ => Nat.cast_nonneg _)
        _ = ((P 0).card : ℝ) ^ ((1 : ℝ) / d) *
              ∏ j : Fin d, ((P j.succ).card : ℝ) ^ ((1 : ℝ) / d) := by
                congr 1
                refine Finset.prod_congr rfl fun j _ => ?_
                have hfs : ∑ a ∈ X, ((fiber j a).card : ℝ) = ((P j.succ).card : ℝ) := by
                  exact_mod_cast hfiber_sum j
                rw [hfs]
    have hpow_d : (S.card : ℝ) ^ d ≤
        (((P 0).card : ℝ) * ∏ j : Fin d, ((P j.succ).card : ℝ)) := by
      have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hsum_real d
      have hpow_rpow : ∀ r : ℝ, 0 ≤ r → (r ^ ((1 : ℝ) / d)) ^ d = r := fun r hr => by
        rw [← Real.rpow_natCast (r ^ ((1 : ℝ) / d)) d, ← Real.rpow_mul hr,
            one_div_mul_cancel hd_real_ne, Real.rpow_one]
      rw [mul_pow, hpow_rpow _ (Nat.cast_nonneg _),
          prod_rpow_inv_pow Finset.univ d hd_real_ne (fun j : Fin d => ((P j.succ).card : ℝ))
            (fun _ _ => Nat.cast_nonneg _)] at h1
      exact h1
    have hnat : S.card ^ d ≤ (P 0).card * ∏ j : Fin d, (P j.succ).card := by
      exact_mod_cast hpow_d
    rw [Fin.prod_univ_succ]
    exact hnat

/-- **General-`d` Discrete Loomis–Whitney Inequality**: for `d = m + 2` (`d ≥ 2`) and any
finite set `S : Finset (Fin (m + 2) → α)`,
`|S|^{m + 1} ≤ ∏ i : Fin (m + 2), |π_i(S)|`, where `π_i` drops the `i`-th coordinate. -/
theorem loomis_whitney_fin {m : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin (m + 2) → α)) :
    S.card ^ (m + 1) ≤ ∏ i : Fin (m + 2), (S.image (fun x j => x (i.succAbove j))).card :=
  loomis_whitney_succ_two m α S

/-- Real `(1 / (m + 1))`-power form of the **Discrete Loomis–Whitney Inequality**. -/
theorem loomis_whitney_rpow {m : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin (m + 2) → α)) :
    (S.card : ℝ) ≤
      (∏ i : Fin (m + 2), ((S.image (fun x j => x (i.succAbove j))).card : ℝ)) ^
        ((1 : ℝ) / (m + 1)) := by
  have hnat : (S.card : ℝ) ^ (m + 1) ≤
      ∏ i : Fin (m + 2), ((S.image (fun x j => x (i.succAbove j))).card : ℝ) := by
    exact_mod_cast loomis_whitney_fin S
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm1_ne : ((m : ℝ) + 1) ≠ 0 := hm1_pos.ne'
  have hr : ((S.card : ℝ) ^ (m + 1)) ^ ((1 : ℝ) / (m + 1)) ≤
      (∏ i : Fin (m + 2), ((S.image (fun x j => x (i.succAbove j))).card : ℝ)) ^
        ((1 : ℝ) / (m + 1)) :=
    Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _) hnat (by positivity)
  rw [← Real.rpow_natCast (S.card : ℝ) (m + 1), ← Real.rpow_mul (Nat.cast_nonneg _),
      Nat.cast_add, Nat.cast_one, mul_one_div_cancel hm1_ne, Real.rpow_one] at hr
  exact hr

/-- **3D Discrete Loomis–Whitney Inequality** on `α × β × γ`:
`|S|^2 ≤ |π_{yz}(S)| · |π_{xz}(S)| · |π_{xy}(S)|`. -/
theorem loomis_whitney_3d {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) :
    S.card ^ 2 ≤
      (S.image (fun p => (p.2.1, p.2.2))).card *
        (S.image (fun p => (p.1, p.2.2))).card *
        (S.image (fun p => (p.1, p.2.1))).card := by
  let S' : Finset (Fin 3 → α ⊕ β ⊕ γ) := S.image (fun p =>
    ![Sum.inl p.1, Sum.inr (Sum.inl p.2.1), Sum.inr (Sum.inr p.2.2)])
  have hinj : Function.Injective (fun p : α × β × γ =>
      ![Sum.inl p.1, Sum.inr (Sum.inl p.2.1), Sum.inr (Sum.inr p.2.2)]) := by
    intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
    obtain rfl := Sum.inl.inj h0
    obtain rfl := Sum.inl.inj (Sum.inr.inj h1)
    obtain rfl := Sum.inr.inj (Sum.inr.inj h2)
    rfl
  have hS' : S'.card = S.card := Finset.card_image_of_injective S hinj
  have hlw := loomis_whitney_fin (m := 1) S'
  rw [hS', Fin.prod_univ_three] at hlw
  have hc0 : (S'.image (fun x (j : Fin 2) => x ((0 : Fin 3).succAbove j))).card =
      (S.image (fun p => (p.2.1, p.2.2))).card := by
    have hinj0 : Function.Injective (fun p : β × γ =>
        (![Sum.inr (Sum.inl p.1), Sum.inr (Sum.inr p.2)] : Fin 2 → α ⊕ β ⊕ γ)) := by
      intro ⟨b₁, c₁⟩ ⟨b₂, c₂⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      obtain rfl := Sum.inl.inj (Sum.inr.inj h0)
      obtain rfl := Sum.inr.inj (Sum.inr.inj h1)
      rfl
    have heq : S'.image (fun x (j : Fin 2) => x ((0 : Fin 3).succAbove j)) =
        (S.image (fun p => (p.2.1, p.2.2))).image (fun p : β × γ =>
          ![Sum.inr (Sum.inl p.1), Sum.inr (Sum.inr p.2)]) := by
      ext y
      simp only [Finset.mem_image, S']
      constructor
      · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨(p.2.1, p.2.2), ⟨p, hp, rfl⟩, ?_⟩
        ext j; fin_cases j <;> rfl
      · rintro ⟨⟨b, c⟩, ⟨p, hp, hbc⟩, rfl⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbc
        refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
        ext j; fin_cases j <;> rfl
    rw [heq, Finset.card_image_of_injective _ hinj0]
  have hc1 : (S'.image (fun x (j : Fin 2) => x ((1 : Fin 3).succAbove j))).card =
      (S.image (fun p => (p.1, p.2.2))).card := by
    have hinj1 : Function.Injective (fun p : α × γ =>
        (![Sum.inl p.1, Sum.inr (Sum.inr p.2)] : Fin 2 → α ⊕ β ⊕ γ)) := by
      intro ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      obtain rfl := Sum.inl.inj h0
      obtain rfl := Sum.inr.inj (Sum.inr.inj h1)
      rfl
    have heq : S'.image (fun x (j : Fin 2) => x ((1 : Fin 3).succAbove j)) =
        (S.image (fun p => (p.1, p.2.2))).image (fun p : α × γ =>
          ![Sum.inl p.1, Sum.inr (Sum.inr p.2)]) := by
      ext y
      simp only [Finset.mem_image, S']
      constructor
      · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨(p.1, p.2.2), ⟨p, hp, rfl⟩, ?_⟩
        ext j; fin_cases j <;> rfl
      · rintro ⟨⟨a, c⟩, ⟨p, hp, hac⟩, rfl⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
        refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
        ext j; fin_cases j <;> rfl
    rw [heq, Finset.card_image_of_injective _ hinj1]
  have hc2 : (S'.image (fun x (j : Fin 2) => x ((2 : Fin 3).succAbove j))).card =
      (S.image (fun p => (p.1, p.2.1))).card := by
    have hinj2 : Function.Injective (fun p : α × β =>
        (![Sum.inl p.1, Sum.inr (Sum.inl p.2)] : Fin 2 → α ⊕ β ⊕ γ)) := by
      intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      obtain rfl := Sum.inl.inj h0
      obtain rfl := Sum.inl.inj (Sum.inr.inj h1)
      rfl
    have heq : S'.image (fun x (j : Fin 2) => x ((2 : Fin 3).succAbove j)) =
        (S.image (fun p => (p.1, p.2.1))).image (fun p : α × β =>
          ![Sum.inl p.1, Sum.inr (Sum.inl p.2)]) := by
      ext y
      simp only [Finset.mem_image, S']
      constructor
      · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨(p.1, p.2.1), ⟨p, hp, rfl⟩, ?_⟩
        ext j; fin_cases j <;> rfl
      · rintro ⟨⟨a, b⟩, ⟨p, hp, hab⟩, rfl⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
        refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
        ext j; fin_cases j <;> rfl
    rw [heq, Finset.card_image_of_injective _ hinj2]
  rw [hc0, hc1, hc2] at hlw
  exact hlw

end LoomisWhitney

/-! ## Section 3: Steinhaus Theorem & Difference-Set Measure Corollaries -/

section Steinhaus

private lemma volume_vadd_eq (t : ℝ) (S : Set ℝ) :
    MeasureTheory.volume (t +ᵥ S) = MeasureTheory.volume S := by
  have hpre : t +ᵥ S = (fun x : ℝ => -t + x) ⁻¹' S := by
    ext y
    simp only [Set.mem_vadd_set, Set.mem_preimage, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨-t + y, hy, by ring⟩
  rw [hpre, MeasureTheory.measure_preimage_add]

private lemma compact_shift_subset_open {K U : Set ℝ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (-δ) δ, t +ᵥ K ⊆ U := by
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδ_pos, fun t ht y hy => ?_⟩
  rcases Set.mem_vadd_set.mp hy with ⟨x, hx, rfl⟩
  apply hδ_sub
  rw [Metric.mem_cthickening_iff]
  refine le_trans (Metric.infEDist_le_edist_of_mem hx) ?_
  rw [edist_dist, Real.dist_eq, vadd_eq_add, add_sub_cancel_right]
  have habs : |t| < δ := abs_lt.mpr ht
  exact ENNReal.ofReal_le_ofReal habs.le

/-- Quantitative Steinhaus intersection lemma: if `A : Set ℝ` is measurable with
`0 < volume A < ∞`, there exists `δ > 0` such that every shift `t ∈ (-δ, δ)` yields
positive-measure intersection `0 < volume ((t +ᵥ A) ∩ A)`. -/
theorem steinhaus_pos_volume_shift {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : 0 < MeasureTheory.volume A) (hfin : MeasureTheory.volume A < ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (-δ) δ,
      0 < MeasureTheory.volume ((t +ᵥ A) ∩ A) := by
  classical
  let m := MeasureTheory.volume A
  have hm_ne0 : m ≠ 0 := hpos.ne'
  have hm_ne_top : m ≠ ⊤ := hfin.ne
  have heps1 : m / 2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hm_ne0, by norm_num⟩
  obtain ⟨K, hKA, hK_comp, hAK_lt⟩ := hA.exists_isCompact_sdiff_lt hm_ne_top heps1
  have hK_meas : MeasurableSet K := hK_comp.measurableSet
  have hK_pos : 0 < MeasureTheory.volume K := by
    have hsplit : m ≤ MeasureTheory.volume K + MeasureTheory.volume (A \ K) := by
      have : A ⊆ K ∪ (A \ K) := fun x hx =>
        if h : x ∈ K then Or.inl h else Or.inr ⟨hx, h⟩
      exact le_trans (MeasureTheory.measure_mono this) (MeasureTheory.measure_union_le K (A \ K))
    by_contra hK0
    rw [not_lt, nonpos_iff_eq_zero] at hK0
    rw [hK0, zero_add] at hsplit
    have hle_half : m / 2 ≤ m := ENNReal.half_le_self
    have : m < m / 2 := lt_of_le_of_lt hsplit hAK_lt
    exact (not_lt_of_ge hle_half) this
  have hK_fin : MeasureTheory.volume K < ⊤ := lt_of_le_of_lt (MeasureTheory.measure_mono hKA) hfin
  obtain ⟨U, hKU, hU_open, hU_fin, hUK_lt⟩ :=
    hK_meas.exists_isOpen_sdiff_lt hK_fin.ne hK_pos.ne'
  have hU_lt_2K : MeasureTheory.volume U < MeasureTheory.volume K + MeasureTheory.volume K := by
    have hU_eq : U = K ∪ (U \ K) := (Set.union_sdiff_cancel hKU).symm
    have hU_le : MeasureTheory.volume U ≤ MeasureTheory.volume K + MeasureTheory.volume (U \ K) := by
      conv_lhs => rw [hU_eq]
      exact MeasureTheory.measure_union_le K (U \ K)
    exact lt_of_le_of_lt hU_le (ENNReal.add_lt_add_left hK_fin.ne hUK_lt)
  obtain ⟨δ, hδ_pos, hshift⟩ := compact_shift_subset_open hK_comp hU_open hKU
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  have hshiftK : MeasureTheory.volume (t +ᵥ K) = MeasureTheory.volume K := volume_vadd_eq t K
  have hadd : MeasureTheory.volume ((t +ᵥ K) ∪ K) + MeasureTheory.volume ((t +ᵥ K) ∩ K) =
      MeasureTheory.volume K + MeasureTheory.volume K := by
    rw [MeasureTheory.measure_union_add_inter _ hK_meas, hshiftK]
  have hunion_le : MeasureTheory.volume ((t +ᵥ K) ∪ K) ≤ MeasureTheory.volume U :=
    MeasureTheory.measure_mono (Set.union_subset (hshift t ht) hKU)
  have hunion_lt : MeasureTheory.volume ((t +ᵥ K) ∪ K) <
      MeasureTheory.volume K + MeasureTheory.volume K :=
    lt_of_le_of_lt hunion_le hU_lt_2K
  have hK_inter_pos : 0 < MeasureTheory.volume ((t +ᵥ K) ∩ K) := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, add_zero] at hadd
    rw [hadd] at hunion_lt
    exact (lt_irrefl _) hunion_lt
  have hmono : (t +ᵥ K) ∩ K ⊆ (t +ᵥ A) ∩ A :=
    Set.inter_subset_inter (fun y ⟨x, hx, hy⟩ => Set.mem_vadd_set.mpr ⟨x, hKA hx, hy⟩) hKA
  exact lt_of_lt_of_le hK_inter_pos (MeasureTheory.measure_mono hmono)

/-- **Steinhaus's Theorem** for finite positive-measure sets: if `A : Set ℝ` is measurable
with `0 < volume A < ∞`, then `A - A` contains an open neighborhood `(-δ, δ)` of `0`. -/
theorem steinhaus_finite {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : 0 < MeasureTheory.volume A) (hfin : MeasureTheory.volume A < ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (-δ) δ ⊆ A - A := by
  obtain ⟨δ, hδ_pos, hshift⟩ := steinhaus_pos_volume_shift hA hpos hfin
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  have hpos_t : 0 < MeasureTheory.volume ((t +ᵥ A) ∩ A) := hshift t ht
  have hne : ((t +ᵥ A) ∩ A).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, MeasureTheory.measure_empty] at hpos_t
    exact lt_irrefl (0 : ENNReal) hpos_t
  rcases hne with ⟨y, hy_vadd, hy_A⟩
  rcases Set.mem_vadd_set.mp hy_vadd with ⟨x, hx_A, hy_eq⟩
  refine ⟨y, hy_A, x, hx_A, ?_⟩
  rw [← hy_eq, vadd_eq_add]
  ring

/-- **General Steinhaus Theorem** on `ℝ`: for ANY measurable `A : Set ℝ` with `0 < volume A`
(including `volume A = ⊤`), `A - A` contains an open interval `(-δ, δ)` around `0`. -/
theorem steinhaus {A : Set ℝ} (hA : MeasurableSet A) (hpos : 0 < MeasureTheory.volume A) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (-δ) δ ⊆ A - A := by
  have hunion : A = ⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, hx, neg_le_of_abs_le hn, le_of_abs_le hn⟩
    · rintro ⟨_, hx, _⟩
      exact hx
  have hex_pos : ∃ n : ℕ, 0 < MeasureTheory.volume (A ∩ Set.Icc (-(n : ℝ)) n) := by
    by_contra hnone
    push Not at hnone
    have hnull : ∀ n : ℕ, MeasureTheory.volume (A ∩ Set.Icc (-(n : ℝ)) n) = 0 := fun n =>
      nonpos_iff_eq_zero.mp (hnone n)
    have hA0 : MeasureTheory.volume A = 0 := by
      rw [hunion]
      exact MeasureTheory.measure_iUnion_null hnull
    rw [hA0] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨n, hn_pos⟩ := hex_pos
  have hn_meas : MeasurableSet (A ∩ Set.Icc (-(n : ℝ)) n) :=
    hA.inter measurableSet_Icc
  have hn_fin : MeasureTheory.volume (A ∩ Set.Icc (-(n : ℝ)) n) < ⊤ := by
    have hle : MeasureTheory.volume (A ∩ Set.Icc (-(n : ℝ)) n) ≤
        MeasureTheory.volume (Set.Icc (-(n : ℝ)) n) :=
      MeasureTheory.measure_mono Set.inter_subset_right
    rw [Real.volume_Icc] at hle
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  obtain ⟨δ, hδ_pos, hsub⟩ := steinhaus_finite hn_meas hn_pos hn_fin
  refine ⟨δ, hδ_pos, hsub.trans ?_⟩
  exact Set.sub_subset_sub Set.inter_subset_left Set.inter_subset_left

/-- Metric-ball corollary of Steinhaus's Theorem: `Metric.ball 0 δ ⊆ A - A`. -/
theorem steinhaus_ball {A : Set ℝ} (hA : MeasurableSet A) (hpos : 0 < MeasureTheory.volume A) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : ℝ) δ ⊆ A - A := by
  obtain ⟨δ, hδ_pos, hsub⟩ := steinhaus hA hpos
  refine ⟨δ, hδ_pos, fun t ht => hsub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  exact abs_lt.mp ht

end Steinhaus

/-! ## Section 4: 1D Brunn–Minkowski & Discrete Interval Sumsets -/

section BrunnMinkowski1D

/-- **Discrete 1D Sumset / Brunn–Minkowski Bound on `ℤ`**:
for nonempty finite `A, B : Finset ℤ`, `A.card + B.card - 1 ≤ (A + B).card`. -/
theorem discrete_sumset_int {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  let a₀ := A.min' hA
  let b₁ := B.max' hB
  let S₁ : Finset ℤ := B.image (fun b => a₀ + b)
  let S₂ : Finset ℤ := (A.erase a₀).image (fun a => a + b₁)
  have hS₁_sub : S₁ ⊆ A + B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
    exact Finset.add_mem_add (A.min'_mem hA) hb
  have hS₂_sub : S₂ ⊆ A + B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact Finset.add_mem_add (Finset.erase_subset _ _ ha) (B.max'_mem hB)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨a, ha, heq⟩
    have ha_gt : a₀ < a := lt_of_le_of_ne (A.min'_le a (Finset.erase_subset _ _ ha))
      (Finset.ne_of_mem_erase ha).symm
    have hb_le : b ≤ b₁ := B.le_max' b hb
    linarith
  have hS₁_card : S₁.card = B.card := Finset.card_image_of_injective B (add_right_injective a₀)
  have hS₂_card : S₂.card = A.card - 1 := by
    rw [Finset.card_image_of_injective _ (add_left_injective b₁),
        Finset.card_erase_of_mem (A.min'_mem hA)]
  have hA1 : 1 ≤ A.card := Finset.one_le_card.mpr hA
  calc A.card + B.card - 1
      = B.card + (A.card - 1) := by omega
    _ = S₁.card + S₂.card := by rw [hS₁_card, hS₂_card]
    _ = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (A + B).card := Finset.card_le_card (Finset.union_subset hS₁_sub hS₂_sub)

/-- **Discrete 1D Sumset / Brunn–Minkowski Bound on `ℝ`**:
for nonempty finite `A, B : Finset ℝ`, `A.card + B.card - 1 ≤ (A + B).card`. -/
theorem discrete_sumset_real {A B : Finset ℝ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  let a₀ := A.min' hA
  let b₁ := B.max' hB
  let S₁ : Finset ℝ := B.image (fun b => a₀ + b)
  let S₂ : Finset ℝ := (A.erase a₀).image (fun a => a + b₁)
  have hS₁_sub : S₁ ⊆ A + B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
    exact Finset.add_mem_add (A.min'_mem hA) hb
  have hS₂_sub : S₂ ⊆ A + B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact Finset.add_mem_add (Finset.erase_subset _ _ ha) (B.max'_mem hB)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨a, ha, heq⟩
    have ha_gt : a₀ < a := lt_of_le_of_ne (A.min'_le a (Finset.erase_subset _ _ ha))
      (Finset.ne_of_mem_erase ha).symm
    have hb_le : b ≤ b₁ := B.le_max' b hb
    linarith
  have hS₁_card : S₁.card = B.card := Finset.card_image_of_injective B (add_right_injective a₀)
  have hS₂_card : S₂.card = A.card - 1 := by
    rw [Finset.card_image_of_injective _ (add_left_injective b₁),
        Finset.card_erase_of_mem (A.min'_mem hA)]
  have hA1 : 1 ≤ A.card := Finset.one_le_card.mpr hA
  calc A.card + B.card - 1
      = B.card + (A.card - 1) := by omega
    _ = S₁.card + S₂.card := by rw [hS₁_card, hS₂_card]
    _ = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (A + B).card := Finset.card_le_card (Finset.union_subset hS₁_sub hS₂_sub)

/-- **Compact 1D Brunn–Minkowski Inequality**: for any nonempty compact `K₁, K₂ : Set ℝ`,
`volume K₁ + volume K₂ ≤ volume (K₁ + K₂)`. -/
theorem brunn_minkowski_1d_compact {K₁ K₂ : Set ℝ} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty) :
    MeasureTheory.volume K₁ + MeasureTheory.volume K₂ ≤ MeasureTheory.volume (K₁ + K₂) := by
  let a := sSup K₁
  let b := sInf K₂
  have ha : a ∈ K₁ := hK₁.sSup_mem hne₁
  have hb : b ∈ K₂ := hK₂.sInf_mem hne₂
  let K₁' : Set ℝ := (-a) +ᵥ K₁
  let K₂' : Set ℝ := (-b) +ᵥ K₂
  have hle0 : K₁' ⊆ Set.Iic 0 := by
    intro y hy
    rcases Set.mem_vadd_set.mp hy with ⟨x, hx, rfl⟩
    have hx_le : x ≤ a := le_csSup hK₁.bddAbove hx
    simp only [Set.mem_Iic, vadd_eq_add]
    linarith
  have hge0 : K₂' ⊆ Set.Ici 0 := by
    intro y hy
    rcases Set.mem_vadd_set.mp hy with ⟨x, hx, rfl⟩
    have hx_ge : b ≤ x := csInf_le hK₂.bddBelow hx
    simp only [Set.mem_Ici, vadd_eq_add]
    linarith
  have hinter : K₁' ∩ K₂' ⊆ {(0 : ℝ)} := by
    intro y hy
    have h1 : y ≤ 0 := hle0 hy.1
    have h2 : 0 ≤ y := hge0 hy.2
    simp [le_antisymm h1 h2]
  have hunion_sub : K₁' ∪ K₂' ⊆ (-(a + b)) +ᵥ (K₁ + K₂) := by
    intro y hy
    rcases hy with hy₁ | hy₂
    · rcases Set.mem_vadd_set.mp hy₁ with ⟨x₁, hx₁, rfl⟩
      refine Set.mem_vadd_set.mpr ⟨x₁ + b, Set.add_mem_add hx₁ hb, ?_⟩
      rw [vadd_eq_add, vadd_eq_add]; ring
    · rcases Set.mem_vadd_set.mp hy₂ with ⟨x₂, hx₂, rfl⟩
      refine Set.mem_vadd_set.mpr ⟨a + x₂, Set.add_mem_add ha hx₂, ?_⟩
      rw [vadd_eq_add, vadd_eq_add]; ring
  have hK₂'_meas : MeasurableSet K₂' :=
    (hK₂.vadd (-b)).measurableSet
  have hinter_vol : MeasureTheory.volume (K₁' ∩ K₂') = 0 :=
    nonpos_iff_eq_zero.mp (le_trans (MeasureTheory.measure_mono hinter) (by simp))
  calc MeasureTheory.volume K₁ + MeasureTheory.volume K₂
      = MeasureTheory.volume K₁' + MeasureTheory.volume K₂' := by
          rw [volume_vadd_eq (-a) K₁, volume_vadd_eq (-b) K₂]
    _ = MeasureTheory.volume (K₁' ∪ K₂') + MeasureTheory.volume (K₁' ∩ K₂') :=
          (MeasureTheory.measure_union_add_inter K₁' hK₂'_meas).symm
    _ = MeasureTheory.volume (K₁' ∪ K₂') := by rw [hinter_vol, add_zero]
    _ ≤ MeasureTheory.volume ((-(a + b)) +ᵥ (K₁ + K₂)) :=
          MeasureTheory.measure_mono hunion_sub
    _ = MeasureTheory.volume (K₁ + K₂) := volume_vadd_eq (-(a + b)) (K₁ + K₂)

/-- **Continuous 1D Brunn–Minkowski Inequality**: for ALL nonempty measurable sets
`A, B : Set ℝ`, `volume A + volume B ≤ volume (A + B)` (without requiring boundedness or
measurability of `A + B`). -/
theorem brunn_minkowski_1d {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    MeasureTheory.volume A + MeasureTheory.volume B ≤ MeasureTheory.volume (A + B) := by
  classical
  by_cases hA_top : MeasureTheory.volume A = ⊤
  · obtain ⟨b, hb⟩ := hneB
    have hvol : MeasureTheory.volume (b +ᵥ A) ≤ MeasureTheory.volume (A + B) :=
      MeasureTheory.measure_mono fun y hy => by
        rcases Set.mem_vadd_set.mp hy with ⟨a, ha, rfl⟩
        rw [vadd_eq_add, add_comm b a]
        exact Set.add_mem_add ha hb
    rw [volume_vadd_eq b A, hA_top] at hvol
    rw [hA_top, top_add]
    exact hvol
  by_cases hB_top : MeasureTheory.volume B = ⊤
  · obtain ⟨a, ha⟩ := hneA
    have hvol : MeasureTheory.volume (a +ᵥ B) ≤ MeasureTheory.volume (A + B) :=
      MeasureTheory.measure_mono fun y hy => by
        rcases Set.mem_vadd_set.mp hy with ⟨b, hb, rfl⟩
        exact Set.add_mem_add ha hb
    rw [volume_vadd_eq a B, hB_top] at hvol
    rw [hB_top, add_top]
    exact hvol
  by_cases hA0 : MeasureTheory.volume A = 0
  · obtain ⟨a, ha⟩ := hneA
    have hvol : MeasureTheory.volume (a +ᵥ B) ≤ MeasureTheory.volume (A + B) :=
      MeasureTheory.measure_mono fun y hy => by
        rcases Set.mem_vadd_set.mp hy with ⟨b, hb, rfl⟩
        exact Set.add_mem_add ha hb
    rw [volume_vadd_eq a B] at hvol
    simpa [hA0] using hvol
  by_cases hB0 : MeasureTheory.volume B = 0
  · obtain ⟨b, hb⟩ := hneB
    have hvol : MeasureTheory.volume (b +ᵥ A) ≤ MeasureTheory.volume (A + B) :=
      MeasureTheory.measure_mono fun y hy => by
        rcases Set.mem_vadd_set.mp hy with ⟨a, ha, rfl⟩
        rw [vadd_eq_add, add_comm b a]
        exact Set.add_mem_add ha hb
    rw [volume_vadd_eq b A] at hvol
    simpa [hB0] using hvol
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hAB_fin => ?_
  let ε₁ : ENNReal := min ((ε : ENNReal) / 2) (MeasureTheory.volume A / 2)
  let ε₂ : ENNReal := min ((ε : ENNReal) / 2) (MeasureTheory.volume B / 2)
  have hε₁_pos : ε₁ ≠ 0 :=
    (lt_min (ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num))
      (ENNReal.div_pos hA0 (by norm_num))).ne'
  have hε₂_pos : ε₂ ≠ 0 :=
    (lt_min (ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num))
      (ENNReal.div_pos hB0 (by norm_num))).ne'
  obtain ⟨K₁, hK₁A, hK₁_comp, hAK₁_lt⟩ := hA.exists_isCompact_sdiff_lt hA_top hε₁_pos
  obtain ⟨K₂, hK₂B, hK₂_comp, hBK₂_lt⟩ := hB.exists_isCompact_sdiff_lt hB_top hε₂_pos
  have hK₁_ne : K₁.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, Set.sdiff_empty] at hAK₁_lt
    have h1 : MeasureTheory.volume A < MeasureTheory.volume A / 2 :=
      lt_of_lt_of_le hAK₁_lt (min_le_right _ _)
    exact (not_lt_of_ge ENNReal.half_le_self) h1
  have hK₂_ne : K₂.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, Set.sdiff_empty] at hBK₂_lt
    have h1 : MeasureTheory.volume B < MeasureTheory.volume B / 2 :=
      lt_of_lt_of_le hBK₂_lt (min_le_right _ _)
    exact (not_lt_of_ge ENNReal.half_le_self) h1
  have hbm := brunn_minkowski_1d_compact hK₁_comp hK₂_comp hK₁_ne hK₂_ne
  have hbm' : MeasureTheory.volume K₁ + MeasureTheory.volume K₂ ≤ MeasureTheory.volume (A + B) :=
    le_trans hbm (MeasureTheory.measure_mono (Set.add_subset_add hK₁A hK₂B))
  have hA_le : MeasureTheory.volume A ≤ MeasureTheory.volume K₁ + (ε : ENNReal) / 2 := by
    have hsplit : MeasureTheory.volume A ≤
        MeasureTheory.volume K₁ + MeasureTheory.volume (A \ K₁) := by
      have : A ⊆ K₁ ∪ (A \ K₁) := fun x hx =>
        if h : x ∈ K₁ then Or.inl h else Or.inr ⟨hx, h⟩
      exact le_trans (MeasureTheory.measure_mono this) (MeasureTheory.measure_union_le K₁ (A \ K₁))
    have hAK₁_le : MeasureTheory.volume (A \ K₁) ≤ (ε : ENNReal) / 2 :=
      le_trans hAK₁_lt.le (min_le_left _ _)
    exact le_trans hsplit (add_le_add le_rfl hAK₁_le)
  have hB_le : MeasureTheory.volume B ≤ MeasureTheory.volume K₂ + (ε : ENNReal) / 2 := by
    have hsplit : MeasureTheory.volume B ≤
        MeasureTheory.volume K₂ + MeasureTheory.volume (B \ K₂) := by
      have : B ⊆ K₂ ∪ (B \ K₂) := fun x hx =>
        if h : x ∈ K₂ then Or.inl h else Or.inr ⟨hx, h⟩
      exact le_trans (MeasureTheory.measure_mono this) (MeasureTheory.measure_union_le K₂ (B \ K₂))
    have hBK₂_le : MeasureTheory.volume (B \ K₂) ≤ (ε : ENNReal) / 2 :=
      le_trans hBK₂_lt.le (min_le_left _ _)
    exact le_trans hsplit (add_le_add le_rfl hBK₂_le)
  calc MeasureTheory.volume A + MeasureTheory.volume B
      ≤ (MeasureTheory.volume K₁ + (ε : ENNReal) / 2) +
          (MeasureTheory.volume K₂ + (ε : ENNReal) / 2) := add_le_add hA_le hB_le
    _ = (MeasureTheory.volume K₁ + MeasureTheory.volume K₂) + (ε : ENNReal) := by
          rw [add_add_add_comm, ENNReal.add_halves]
    _ ≤ MeasureTheory.volume (A + B) + (ε : ENNReal) := add_le_add hbm' le_rfl

/-- **1D Brunn–Minkowski Difference Inequality**: for nonempty measurable `A, B : Set ℝ`,
`volume A + volume B ≤ volume (A - B)`. -/
theorem brunn_minkowski_1d_sub {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    MeasureTheory.volume A + MeasureTheory.volume B ≤ MeasureTheory.volume (A - B) := by
  have hnegB : MeasurableSet (-B) := hB.neg
  have hne_negB : (-B).Nonempty := hneB.neg
  have hbm := brunn_minkowski_1d hA hnegB hneA hne_negB
  have hvol_neg : MeasureTheory.volume (-B) = MeasureTheory.volume B := by
    have hpre : -B = (fun x : ℝ => (-1 : ℝ) * x) ⁻¹' B := by ext x; simp
    rw [hpre, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0) B]
    simp
  have hsub_eq : A + (-B) = A - B := by simp [sub_eq_add_neg]
  rw [hvol_neg, hsub_eq] at hbm
  exact hbm

/-- **1D Brunn–Minkowski on Closed Intervals**:
`volume (Set.Icc a b) + volume (Set.Icc c d) ≤ volume (Set.Icc a b + Set.Icc c d)` whenever
`a ≤ b` and `c ≤ d`. -/
theorem brunn_minkowski_intervals {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    MeasureTheory.volume (Set.Icc a b) + MeasureTheory.volume (Set.Icc c d) ≤
      MeasureTheory.volume (Set.Icc a b + Set.Icc c d) :=
  brunn_minkowski_1d measurableSet_Icc measurableSet_Icc ⟨a, le_rfl, hab⟩ ⟨c, le_rfl, hcd⟩

end BrunnMinkowski1D

end Arith4Ext.MeasureConvex
