/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# Arithmetica4 Tier A Extension: Euclidean Incidence Geometry Engine (`Arith4Ext.GeometryIncidence`)

Clean, general, non-vacuous Tier A reusable library built 100% from scratch on targeted
Mathlib imports (`0` monolithic `import Mathlib`, `0` Tier C imports, `0` custom axioms).

## Exported API Summary (`namespace Arith4Ext.GeometryIncidence`)
1. **Euclidean Plane Primitives, Intersection Bounds (`≤ 1` / `≤ 2`), & Generic Similarity Tilt:**
   - `IsLine`, `lineThrough`, `linesOf`, `IsCollinear`, `affine_line_eq_of_two_mem`
   - `two_line_inter_card_le_one`, `line_circle_inter_card_le_two`, `two_circle_inter_card_le_two`
   - `congruent_circles_inter_sum`, `upper_congruent_semicircle_inter_subsingleton`
   - `rotUnit`, `simMap`, `exists_rotation_avoiding_vertical`, `exists_rotation_avoiding_axes`, `exists_rotation_generic`
2. **Sylvester–Gallai Theorem (Kelly's Shortest-Altitude Proof):**
   - `sylvester_gallai`, `sylvester_gallai_pair`: any finite non-collinear `P : Finset (EuclideanSpace ℝ (Fin 2))`
     determines an ordinary line `ℓ` with `(P.filter (· ∈ ℓ)).card = 2`.
3. **Topology-Free Wiring-Diagram Multigraph Crossing Lemma:**
   - `SlabWiring`, `slabWiring_zero_crossings_edge_le` (`|E| ≤ 3 n`),
     `exists_minimal_slabWiring_disjoint_inversions`, `slabWiring_linear_crossing_bound`,
     `slabWiring_crossing_lemma`, `MultiSlabWiring`,
     `multigraph_slabWiring_crossing_lemma`, `multigraph_slabWiring_crossing_lemma_threshold`,
     `xMonotone_multi_to_slabWiring`.
4. **Szemerédi–Trotter Theorem, `k`-Rich Lines, & Beck's Theorem (1983):**
   - `xMonotone_one_inter_incidences_le`, `lineIncidences`, `szemeredi_trotter`:
     `I(P, L) ≤ 4 |P|^(2/3) |L|^(2/3) + 4 |P| + |L|`.
   - `k_rich_lines_bound` (`k ≥ 2`) and `k_rich_incidences_bound`.
   - `beck_theorem`: linear collinearity (`≥ (1/1024)|P|`) or quadratic determined lines.
5. **Unit-Distance `O(n^(4/3))` & Pinned/Global Distinct-Distance `Ω(n^(4/5))` Corollaries:**
   - `congruent_circle_incidences_le`, `unit_circle_incidences_le`,
     `unit_distances_le`, `unit_distances_le_compact`.
   - `pinnedDistCount`, `distinctDistCount`, `pinned_distinct_distances_ge`, `distinct_distances_ge`.
-/

namespace Arith4Ext.GeometryIncidence

open scoped BigOperators Classical
open Finset

/-! ## Section 1: Euclidean Plane Primitives, Intersection Bounds, & Generic Similarity Tilt -/

section PlanePrimitives

/-- Construct a point `(x, y)` in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def mkPt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

@[simp] lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := by
  simp [mkPt]

@[simp] lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := by
  simp [mkPt]

lemma pt_ext {p q : EuclideanSpace ℝ (Fin 2)} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- 2D determinant / cross product `u₀ v₁ - u₁ v₀`. -/
def det2 (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- 2D dot product `u₀ v₀ + u₁ v₁`. -/
def dot2 (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- 2D squared Euclidean norm `u₀² + u₁²`. -/
def normSq2 (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  u 0 ^ 2 + u 1 ^ 2

lemma normSq2_nonneg (u : EuclideanSpace ℝ (Fin 2)) : 0 ≤ normSq2 u := by
  unfold normSq2; positivity

lemma normSq2_eq_zero_iff (u : EuclideanSpace ℝ (Fin 2)) : normSq2 u = 0 ↔ u = 0 := by
  constructor
  · intro h
    unfold normSq2 at h
    have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    exact pt_ext h0 h1
  · rintro rfl; simp [normSq2]

lemma normSq2_pos_iff (u : EuclideanSpace ℝ (Fin 2)) : 0 < normSq2 u ↔ u ≠ 0 := by
  constructor
  · intro h h0; rw [h0, (normSq2_eq_zero_iff 0).mpr rfl] at h; exact lt_irrefl 0 h
  · intro h
    exact lt_of_le_of_ne (normSq2_nonneg u) (fun heq => h ((normSq2_eq_zero_iff u).mp heq.symm))

lemma lagrange_det2_dot2 (u v : EuclideanSpace ℝ (Fin 2)) :
    dot2 u v ^ 2 + det2 u v ^ 2 = normSq2 u * normSq2 v := by
  unfold dot2 det2 normSq2; ring

lemma dist_sq_eq_normSq2 (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = normSq2 (p - q) := by
  rw [EuclideanSpace.dist_eq]
  have hnn : 0 ≤ ∑ i : Fin 2, dist (p i) (q i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.sq_sqrt hnn, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs, normSq2, PiLp.sub_apply]

lemma dist_eq_sqrt_normSq2 (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q = Real.sqrt (normSq2 (p - q)) := by
  rw [← dist_sq_eq_normSq2, Real.sqrt_sq dist_nonneg]

/-- Predicate for a 1-dimensional affine line in `EuclideanSpace ℝ (Fin 2)`. -/
def IsLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Module.finrank ℝ ℓ.direction = 1

lemma isLine_nonempty {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ) :
    (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hbot : ℓ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact False.elim (Set.eq_empty_iff_forall_notMem.mp h x hx)
  rw [hbot, IsLine, AffineSubspace.direction_bot, finrank_bot] at hℓ
  omega

/-- The affine line spanned by two points `p, q ∈ ℝ²`. -/
noncomputable def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))

lemma mem_lineThrough_left (p q : EuclideanSpace ℝ (Fin 2)) : p ∈ lineThrough p q :=
  subset_affineSpan ℝ _ (by simp)

lemma mem_lineThrough_right (p q : EuclideanSpace ℝ (Fin 2)) : q ∈ lineThrough p q :=
  subset_affineSpan ℝ _ (by simp)

lemma lineThrough_comm (p q : EuclideanSpace ℝ (Fin 2)) :
    lineThrough p q = lineThrough q p := by
  simp only [lineThrough, Set.pair_comm]

lemma direction_lineThrough (p q : EuclideanSpace ℝ (Fin 2)) :
    (lineThrough p q).direction = Submodule.span ℝ ({q - p} : Set (EuclideanSpace ℝ (Fin 2))) := by
  unfold lineThrough
  rw [direction_affineSpan, vectorSpan_pair, vsub_eq_sub]
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    have : p - q = -(q - p) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    have : q - p = -(p - q) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))

lemma isLine_lineThrough {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) :
    IsLine (lineThrough p q) := by
  rw [IsLine, direction_lineThrough]
  exact finrank_span_singleton (sub_ne_zero.mpr hpq.symm)

lemma mem_lineThrough_iff {p q r : EuclideanSpace ℝ (Fin 2)} :
    r ∈ lineThrough p q ↔ ∃ t : ℝ, r = p + t • (q - p) := by
  have hp : p ∈ lineThrough p q := mem_lineThrough_left p q
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp, direction_lineThrough,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [vsub_eq_sub] at ht
    have := congrArg (fun z => p + z) ht.symm
    simpa [add_sub_cancel] using this
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [vsub_eq_sub]⟩

lemma mem_lineThrough_iff_det2 {p q r : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) :
    r ∈ lineThrough p q ↔ det2 (q - p) (r - p) = 0 := by
  rw [mem_lineThrough_iff]
  constructor
  · rintro ⟨t, rfl⟩
    simp [det2, PiLp.sub_apply, PiLp.smul_apply]
    ring
  · intro hdet
    unfold det2 at hdet
    simp only [PiLp.sub_apply] at hdet
    by_cases h0 : q 0 - p 0 ≠ 0
    · refine ⟨(r 0 - p 0) / (q 0 - p 0), pt_ext ?_ ?_⟩
      · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
        field_simp [h0]; ring
      · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
        field_simp [h0]; linarith
    · push Not at h0
      have h1 : q 1 - p 1 ≠ 0 := by
        intro h1
        exact hpq (pt_ext (by linarith) (by linarith))
      have hr0 : r 0 - p 0 = 0 := by
        rw [h0] at hdet
        have hmul : (q 1 - p 1) * (r 0 - p 0) = 0 := by linarith
        exact (mul_eq_zero.mp hmul).resolve_left h1
      refine ⟨(r 1 - p 1) / (q 1 - p 1), pt_ext ?_ ?_⟩
      · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, h0]
        linarith
      · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
        field_simp [h1]; ring

/-- Two 1-dimensional affine lines sharing two distinct points coincide. -/
theorem affine_line_eq_of_two_mem
    {ℓ₁ ℓ₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    (h₁ : IsLine ℓ₁) (h₂ : IsLine ℓ₂)
    {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (hp₁ : p ∈ ℓ₁) (hq₁ : q ∈ ℓ₁) (hp₂ : p ∈ ℓ₂) (hq₂ : q ∈ ℓ₂) :
    ℓ₁ = ℓ₂ := by
  have hv_ne : q -ᵥ p ≠ (0 : EuclideanSpace ℝ (Fin 2)) := vsub_ne_zero.mpr hpq.symm
  have hle₁ : Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ₁.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (AffineSubspace.vsub_mem_direction hq₁ hp₁))
  have hle₂ : Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ₂.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (AffineSubspace.vsub_mem_direction hq₂ hp₂))
  have hspan_dim : Module.finrank ℝ (Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2)))) = 1 :=
    finrank_span_singleton hv_ne
  have hd₁ : Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) = ℓ₁.direction :=
    Submodule.eq_of_le_of_finrank_eq hle₁ (by rw [hspan_dim, h₁])
  have hd₂ : Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) = ℓ₂.direction :=
    Submodule.eq_of_le_of_finrank_eq hle₂ (by rw [hspan_dim, h₂])
  have hdir : ℓ₁.direction = ℓ₂.direction := hd₁.symm.trans hd₂
  ext x
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp₁,
      ← AffineSubspace.vsub_right_mem_direction_iff_mem hp₂, hdir]

lemma lineThrough_eq_of_mem {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    (hℓ : IsLine ℓ) {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (hp : p ∈ ℓ) (hq : q ∈ ℓ) : lineThrough p q = ℓ :=
  affine_line_eq_of_two_mem (isLine_lineThrough hpq) hℓ hpq
    (mem_lineThrough_left p q) (mem_lineThrough_right p q) hp hq

lemma isLine_exists_two_points {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ) :
    ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧ p ∈ ℓ ∧ q ∈ ℓ := by
  obtain ⟨p, hp⟩ := isLine_nonempty hℓ
  have hne : ℓ.direction ≠ ⊥ := by
    intro hb; unfold IsLine at hℓ; rw [hb, finrank_bot] at hℓ; omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨p, v +ᵥ p, ?_, hp, AffineSubspace.vadd_mem_of_mem_direction hv_mem hp⟩
  intro h
  exact hv_ne (by simpa [vadd_eq_add] using h.symm)

/-- **Two-Line Intersection Bound (`≤ 1`):** Two distinct lines intersect in at most one point. -/
theorem two_line_inter_subsingleton
    {ℓ₁ ℓ₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    (h₁ : IsLine ℓ₁) (h₂ : IsLine ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    Set.Subsingleton ((ℓ₁ : Set (EuclideanSpace ℝ (Fin 2))) ∩ (ℓ₂ : Set (EuclideanSpace ℝ (Fin 2)))) := by
  rintro p ⟨hp₁, hp₂⟩ q ⟨hq₁, hq₂⟩
  by_contra hpq
  exact hne (affine_line_eq_of_two_mem h₁ h₂ hpq hp₁ hq₁ hp₂ hq₂)

/-- Finset version of the two-line intersection bound (`≤ 1`). -/
theorem two_line_inter_card_le_one
    {ℓ₁ ℓ₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    (h₁ : IsLine ℓ₁) (h₂ : IsLine ℓ₂) (hne : ℓ₁ ≠ ℓ₂)
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (P.filter (fun p => p ∈ ℓ₁ ∧ p ∈ ℓ₂)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  exact two_line_inter_subsingleton h₁ h₂ hne hp.2 hq.2

/-- A finite point set is collinear if all its points lie on some affine line. -/
def IsCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)), IsLine ℓ ∧ ∀ p ∈ P, p ∈ ℓ

lemma isCollinear_of_card_le_two {P : Finset (EuclideanSpace ℝ (Fin 2))} (h : P.card ≤ 2) :
    IsCollinear P := by
  by_cases h0 : P.card = 0
  · rw [Finset.card_eq_zero] at h0; subst h0
    refine ⟨lineThrough 0 (mkPt 1 0), isLine_lineThrough ?_, by simp⟩
    intro heq
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
    simp at this
  · by_cases h1 : P.card = 1
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp h1
      refine ⟨lineThrough p (p + mkPt 1 0), isLine_lineThrough ?_, ?_⟩
      · intro heq
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
        simp [PiLp.add_apply] at this
      · intro q hq; rw [Finset.mem_singleton.mp hq]; exact mem_lineThrough_left _ _
    · have h2 : P.card = 2 := by omega
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp h2
      refine ⟨lineThrough p q, isLine_lineThrough hpq, ?_⟩
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr'
      · exact mem_lineThrough_left r q
      · rw [Finset.mem_singleton.mp hr']; exact mem_lineThrough_right p q

/-- The finite set of all distinct lines determined by pairs of distinct points of `P`. -/
noncomputable def linesOf (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := by
  classical
  exact ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => lineThrough pq.1 pq.2)

lemma mem_linesOf_iff {P : Finset (EuclideanSpace ℝ (Fin 2))}
    {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} :
    ℓ ∈ linesOf P ↔ ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ ℓ = lineThrough p q := by
  classical
  simp only [linesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq⟩, rfl⟩
    exact ⟨p, hp, q, hq, hpq, rfl⟩
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    exact ⟨(p, q), ⟨⟨hp, hq⟩, hpq⟩, rfl⟩

lemma isLine_of_mem_linesOf {P : Finset (EuclideanSpace ℝ (Fin 2))}
    {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : ℓ ∈ linesOf P) :
    IsLine ℓ := by
  rcases mem_linesOf_iff.mp hℓ with ⟨p, _, q, _, hpq, rfl⟩
  exact isLine_lineThrough hpq

/-- Auxiliary: a real quadratic `a t² + b t + c = 0` with `a ≠ 0` has at most 2 roots. -/
lemma quadratic_roots_card_le_two {a b c : ℝ} (ha : a ≠ 0) (S : Finset ℝ)
    (hS : ∀ t ∈ S, a * t ^ 2 + b * t + c = 0) : S.card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  have h3 : 3 ≤ S.card := hgt
  obtain ⟨T, hTS, hT3⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨t₁, ht₁T⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hT2 : (T.erase t₁).card = 2 := by rw [Finset.card_erase_of_mem ht₁T, hT3]
  obtain ⟨t₂, t₃, h23, hTer⟩ := Finset.card_eq_two.mp hT2
  have ht₂er : t₂ ∈ T.erase t₁ := hTer ▸ Finset.mem_insert_self t₂ {t₃}
  have ht₃er : t₃ ∈ T.erase t₁ := hTer ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t₃)
  have ht₂T : t₂ ∈ T := Finset.mem_of_mem_erase ht₂er
  have ht₃T : t₃ ∈ T := Finset.mem_of_mem_erase ht₃er
  have h12 : t₁ ≠ t₂ := (Finset.ne_of_mem_erase ht₂er).symm
  have h13 : t₁ ≠ t₃ := (Finset.ne_of_mem_erase ht₃er).symm
  have e1 := hS t₁ (hTS ht₁T)
  have e2 := hS t₂ (hTS ht₂T)
  have e3 := hS t₃ (hTS ht₃T)
  have d12 : a * (t₁ + t₂) + b = 0 := by
    have : (t₁ - t₂) * (a * (t₁ + t₂) + b) = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h12)
  have d13 : a * (t₁ + t₃) + b = 0 := by
    have : (t₁ - t₃) * (a * (t₁ + t₃) + b) = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h13)
  have : a * (t₂ - t₃) = 0 := by linarith
  exact (mul_eq_zero.mp this).elim ha (sub_ne_zero.mpr h23)

/-- **Line–Circle Intersection Bound (`≤ 2`):** Any affine line intersects any circle in at most 2 points. -/
theorem line_circle_inter_card_le_two
    {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ)
    (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (P.filter (fun p => p ∈ ℓ ∧ dist p c = r)).card ≤ 2 := by
  classical
  obtain ⟨p₀, q₀, hpq, hp₀, hq₀⟩ := isLine_exists_two_points hℓ
  have hℓeq : lineThrough p₀ q₀ = ℓ := lineThrough_eq_of_mem hℓ hpq hp₀ hq₀
  let v := q₀ - p₀
  have hv : normSq2 v ≠ 0 := by
    intro h0
    exact hpq ((sub_eq_zero.mp ((normSq2_eq_zero_iff v).mp h0)).symm)
  let F := P.filter (fun p => p ∈ ℓ ∧ dist p c = r)
  let tOf : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => dot2 (p - p₀) v / normSq2 v
  have hparam : ∀ p ∈ F, p = p₀ + tOf p • v := by
    intro p hp
    have hpℓ : p ∈ lineThrough p₀ q₀ := hℓeq.symm ▸ (Finset.mem_filter.mp hp).2.1
    obtain ⟨t, ht⟩ := mem_lineThrough_iff.mp hpℓ
    have ht_eq : tOf p = t := by
      simp only [tOf, ht, add_sub_cancel_left]
      have hdot : dot2 (t • v) v = t * normSq2 v := by
        unfold dot2 normSq2; simp [PiLp.smul_apply]; ring
      rw [hdot, mul_div_cancel_right₀ t hv]
    rw [ht_eq]; exact ht
  have hinj : Set.InjOn tOf (F : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p₁ hp₁ p₂ hp₂ hEq
    rw [hparam p₁ hp₁, hparam p₂ hp₂, hEq]
  rw [← Finset.card_image_of_injOn hinj]
  apply quadratic_roots_card_le_two (a := normSq2 v) (b := 2 * dot2 (p₀ - c) v)
    (c := normSq2 (p₀ - c) - r ^ 2) hv
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨p, hpF, rfl⟩
  have hdist : dist p c = r := (Finset.mem_filter.mp hpF).2.2
  have hsq : normSq2 (p - c) = r ^ 2 := by rw [← dist_sq_eq_normSq2, hdist]
  have hp_eq : p - c = (p₀ - c) + tOf p • v := by
    conv_lhs => rw [hparam p hpF]
    abel
  rw [hp_eq] at hsq
  simp only [normSq2, dot2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hsq ⊢
  nlinarith

/-- **Two-Circle Intersection Bound (`≤ 2`):** Any two distinct circles intersect in at most 2 points. -/
theorem two_circle_inter_card_le_two
    {c₁ c₂ : EuclideanSpace ℝ (Fin 2)} {r₁ r₂ : ℝ}
    (hne : c₁ ≠ c₂ ∨ r₁ ≠ r₂)
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (P.filter (fun p => dist p c₁ = r₁ ∧ dist p c₂ = r₂)).card ≤ 2 := by
  classical
  by_cases hc : c₁ = c₂
  · subst hc
    have hr : r₁ ≠ r₂ := hne.resolve_left (not_not.mpr rfl)
    have hemp : P.filter (fun p => dist p c₁ = r₁ ∧ dist p c₁ = r₂) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p _ ⟨h1, h2⟩
      exact hr (h1.symm.trans h2)
    rw [hemp]; simp
  · -- Radical axis: all intersection points lie on a single affine line perpendicular to `c₂ - c₁`
    let d := c₂ - c₁
    have hd : normSq2 d ≠ 0 := by
      intro h0; exact hc ((sub_eq_zero.mp ((normSq2_eq_zero_iff d).mp h0)).symm)
    let rhs : ℝ := (normSq2 c₂ - normSq2 c₁ + r₁ ^ 2 - r₂ ^ 2) / 2
    let p₀ : EuclideanSpace ℝ (Fin 2) := (rhs / normSq2 d) • d
    let nvec : EuclideanSpace ℝ (Fin 2) := mkPt (-d 1) (d 0)
    have hn_ne : nvec ≠ 0 := by
      intro h0
      have h00 : -d 1 = 0 := by simpa [nvec] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h0
      have h01 : d 0 = 0 := by simpa [nvec] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h0
      have : normSq2 d = 0 := by unfold normSq2; linarith [sq_eq_zero_iff.mpr h01, sq_eq_zero_iff.mpr (neg_eq_zero.mp h00)]
      exact hd this
    let ℓ := lineThrough p₀ (p₀ + nvec)
    have hℓ : IsLine ℓ := isLine_lineThrough (by intro h; exact hn_ne (by simpa using h.symm))
    have hsub : P.filter (fun p => dist p c₁ = r₁ ∧ dist p c₂ = r₂) ⊆
        P.filter (fun p => p ∈ ℓ ∧ dist p c₁ = r₁) := by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, ?_, hp.2.1⟩
      have h1 : normSq2 (p - c₁) = r₁ ^ 2 := by rw [← dist_sq_eq_normSq2, hp.2.1]
      have h2 : normSq2 (p - c₂) = r₂ ^ 2 := by rw [← dist_sq_eq_normSq2, hp.2.2]
      have hlin : dot2 d p = rhs := by
        simp only [normSq2, dot2, d, rhs, PiLp.sub_apply] at h1 h2 ⊢
        linarith
      have hlin0 : dot2 d p₀ = rhs := by
        simp only [dot2, p₀, PiLp.smul_apply, smul_eq_mul, normSq2] at hd ⊢
        have : d 0 * (rhs / (d 0 ^ 2 + d 1 ^ 2) * d 0) + d 1 * (rhs / (d 0 ^ 2 + d 1 ^ 2) * d 1) =
            rhs * ((d 0 ^ 2 + d 1 ^ 2) / (d 0 ^ 2 + d 1 ^ 2)) := by ring
        rw [this, div_self hd, mul_one]
      have hdet : det2 ((p₀ + nvec) - p₀) (p - p₀) = 0 := by
        rw [add_sub_cancel_left]
        unfold det2 nvec
        simp only [mkPt_zero, mkPt_one, PiLp.sub_apply]
        unfold dot2 at hlin hlin0
        linarith
      exact (mem_lineThrough_iff_det2 (by intro h; exact hn_ne (by simpa using h.symm))).mpr hdet
    exact le_trans (Finset.card_le_card hsub) (line_circle_inter_card_le_two hℓ c₁ r₁ P)

/-- **Rhombus Identity:** Two distinct intersection points of two distinct congruent circles satisfy `p + q = c₁ + c₂`. -/
lemma congruent_circles_inter_sum {c₁ c₂ p q : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hc : c₁ ≠ c₂) (hpq : p ≠ q)
    (hp1 : dist p c₁ = r) (hp2 : dist p c₂ = r)
    (hq1 : dist q c₁ = r) (hq2 : dist q c₂ = r) :
    p + q = c₁ + c₂ := by
  have e1 : normSq2 (p - c₁) = r ^ 2 := by rw [← dist_sq_eq_normSq2, hp1]
  have e2 : normSq2 (p - c₂) = r ^ 2 := by rw [← dist_sq_eq_normSq2, hp2]
  have e3 : normSq2 (q - c₁) = r ^ 2 := by rw [← dist_sq_eq_normSq2, hq1]
  have e4 : normSq2 (q - c₂) = r ^ 2 := by rw [← dist_sq_eq_normSq2, hq2]
  -- Let a = c₂ - c₁ ≠ 0, b = p - q ≠ 0, w = p + q - c₁ - c₂
  let a := c₂ - c₁
  let b := p - q
  let w := p + q - (c₁ + c₂)
  have ha : normSq2 a ≠ 0 := fun h0 => hc ((sub_eq_zero.mp ((normSq2_eq_zero_iff a).mp h0)).symm)
  have hb : normSq2 b ≠ 0 := fun h0 => hpq (sub_eq_zero.mp ((normSq2_eq_zero_iff b).mp h0))
  have hab : dot2 a b = 0 := by
    simp only [normSq2, dot2, a, b, PiLp.sub_apply] at e1 e2 e3 e4 ⊢
    linarith
  have haw : dot2 a w = 0 := by
    simp only [normSq2, dot2, a, w, PiLp.sub_apply, PiLp.add_apply] at e1 e2 e3 e4 ⊢
    linarith
  have hbw : dot2 b w = 0 := by
    simp only [normSq2, dot2, b, w, PiLp.sub_apply, PiLp.add_apply] at e1 e2 e3 e4 ⊢
    linarith
  -- Since a, b are nonzero orthogonal vectors in ℝ², det2 a b ≠ 0, so dot2 a w = dot2 b w = 0 ⇒ w = 0.
  have hdet_sq : det2 a b ^ 2 = normSq2 a * normSq2 b := by
    have := lagrange_det2_dot2 a b
    rw [hab] at this; linarith
  have hdet_ne : det2 a b ≠ 0 := by
    intro h0; rw [h0] at hdet_sq
    exact mul_ne_zero ha hb (by linarith)
  have hw0 : w 0 = 0 := by
    have : det2 a b * w 0 = b 1 * dot2 a w - a 1 * dot2 b w := by unfold det2 dot2; ring
    rw [haw, hbw] at this
    exact (mul_eq_zero.mp (by linarith)).resolve_left hdet_ne
  have hw1 : w 1 = 0 := by
    have : det2 a b * w 1 = a 0 * dot2 b w - b 0 * dot2 a w := by unfold det2 dot2; ring
    rw [haw, hbw] at this
    exact (mul_eq_zero.mp (by linarith)).resolve_left hdet_ne
  have hw : w = 0 := pt_ext hw0 hw1
  exact sub_eq_zero.mp hw

/-- **Upper Unit Semicircle Unique Intersection:** Two distinct upper semicircles of equal radius
intersect in at most ONE point! -/
theorem upper_congruent_semicircle_inter_subsingleton
    {c₁ c₂ : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hc : c₁ ≠ c₂) :
    Set.Subsingleton {p : EuclideanSpace ℝ (Fin 2) |
      dist p c₁ = r ∧ c₁ 1 ≤ p 1 ∧ dist p c₂ = r ∧ c₂ 1 ≤ p 1} := by
  rintro p ⟨hp1, hpy1, hp2, hpy2⟩ q ⟨hq1, hqy1, hq2, hqy2⟩
  by_contra hpq
  have hsum := congruent_circles_inter_sum hc hpq hp1 hp2 hq1 hq2
  have hsum1 : p 1 + q 1 = c₁ 1 + c₂ 1 := by
    simpa [PiLp.add_apply] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hsum
  have hsum0 : p 0 + q 0 = c₁ 0 + c₂ 0 := by
    simpa [PiLp.add_apply] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hsum
  have hc1_eq : c₁ 1 = c₂ 1 := by linarith
  have hp1_eq : p 1 = c₁ 1 := by linarith
  have hq1_eq : q 1 = c₁ 1 := by linarith
  have e1 : (p 0 - c₁ 0) ^ 2 = r ^ 2 := by
    have := dist_sq_eq_normSq2 p c₁; rw [hp1] at this; unfold normSq2 at this
    simp only [PiLp.sub_apply, hp1_eq, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero] at this; exact this.symm
  have e2 : (p 0 - c₂ 0) ^ 2 = r ^ 2 := by
    have := dist_sq_eq_normSq2 p c₂; rw [hp2] at this; unfold normSq2 at this
    simp only [PiLp.sub_apply, hp1_eq, hc1_eq, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at this; exact this.symm
  have e3 : (q 0 - c₁ 0) ^ 2 = r ^ 2 := by
    have := dist_sq_eq_normSq2 q c₁; rw [hq1] at this; unfold normSq2 at this
    simp only [PiLp.sub_apply, hq1_eq, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero] at this; exact this.symm
  have hc0_ne : c₁ 0 ≠ c₂ 0 := fun h0 => hc (pt_ext h0 hc1_eq)
  have hpq0_ne : p 0 ≠ q 0 := fun h0 => hpq (pt_ext h0 (hp1_eq.trans hq1_eq.symm))
  have hpc : (p 0 - c₁ 0) = -(p 0 - c₂ 0) := by
    have : (p 0 - c₁ 0 - (p 0 - c₂ 0)) * (p 0 - c₁ 0 + (p 0 - c₂ 0)) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; exact hc0_ne (by linarith)
    · linarith
  -- Then 2 * p 0 = c₁ 0 + c₂ 0 = p 0 + q 0, so p 0 = q 0, contradiction!
  exact hpq0_ne (by linarith)

/-! ### Generic Rotation & Similarity Tilt -/

/-- Planar rotation by unit vector `(u, v)` with `u² + v² = 1`: `(x, y) ↦ (u x - v y, v x + u y)`. -/
noncomputable def rotUnit (u v : ℝ) : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun p => mkPt (u * p 0 - v * p 1) (v * p 0 + u * p 1)

lemma rotUnit_zero (u v : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u v p 0 = u * p 0 - v * p 1 := by simp [rotUnit]

lemma rotUnit_one (u v : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u v p 1 = v * p 0 + u * p 1 := by simp [rotUnit]

lemma rotUnit_add (u v : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u v (p + q) = rotUnit u v p + rotUnit u v q := by
  apply pt_ext <;> simp [rotUnit, PiLp.add_apply] <;> ring

lemma rotUnit_sub (u v : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u v (p - q) = rotUnit u v p - rotUnit u v q := by
  apply pt_ext <;> simp [rotUnit, PiLp.sub_apply] <;> ring

lemma rotUnit_smul (u v c : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u v (c • p) = c • rotUnit u v p := by
  apply pt_ext <;> simp [rotUnit, PiLp.smul_apply] <;> ring

lemma rotUnit_comp_inv {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (p : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u (-v) (rotUnit u v p) = p := by
  apply pt_ext <;> simp only [rotUnit_zero, rotUnit_one]
  · calc u * (u * p 0 - v * p 1) - -v * (v * p 0 + u * p 1)
        = (u ^ 2 + v ^ 2) * p 0 := by ring
      _ = p 0 := by rw [huv, one_mul]
  · calc -v * (u * p 0 - v * p 1) + u * (v * p 0 + u * p 1)
        = (u ^ 2 + v ^ 2) * p 1 := by ring
      _ = p 1 := by rw [huv, one_mul]

lemma rotUnit_inv_comp {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (p : EuclideanSpace ℝ (Fin 2)) :
    rotUnit u v (rotUnit u (-v) p) = p := by
  apply pt_ext <;> simp only [rotUnit_zero, rotUnit_one]
  · calc u * (u * p 0 - -v * p 1) - v * (-v * p 0 + u * p 1)
        = (u ^ 2 + v ^ 2) * p 0 := by ring
      _ = p 0 := by rw [huv, one_mul]
  · calc v * (u * p 0 - -v * p 1) + u * (-v * p 0 + u * p 1)
        = (u ^ 2 + v ^ 2) * p 1 := by ring
      _ = p 1 := by rw [huv, one_mul]

lemma rotUnit_bijective {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) :
    Function.Bijective (rotUnit u v) :=
  Function.bijective_iff_has_inverse.mpr ⟨rotUnit u (-v), rotUnit_comp_inv huv, rotUnit_inv_comp huv⟩

lemma rotUnit_injective {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) :
    Function.Injective (rotUnit u v) :=
  (rotUnit_bijective huv).1

lemma rotUnit_normSq2 {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (p : EuclideanSpace ℝ (Fin 2)) :
    normSq2 (rotUnit u v p) = normSq2 p := by
  unfold normSq2
  rw [rotUnit_zero, rotUnit_one]
  nlinarith

lemma rotUnit_dist {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (p q : EuclideanSpace ℝ (Fin 2)) :
    dist (rotUnit u v p) (rotUnit u v q) = dist p q := by
  rw [dist_eq_sqrt_normSq2, dist_eq_sqrt_normSq2, ← rotUnit_sub, rotUnit_normSq2 huv]

lemma rotUnit_det2 {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (p q : EuclideanSpace ℝ (Fin 2)) :
    det2 (rotUnit u v p) (rotUnit u v q) = det2 p q := by
  unfold det2
  rw [rotUnit_zero, rotUnit_one, rotUnit_zero, rotUnit_one]
  calc (u * p 0 - v * p 1) * (v * q 0 + u * q 1) - (v * p 0 + u * p 1) * (u * q 0 - v * q 1)
      = (u ^ 2 + v ^ 2) * (p 0 * q 1 - p 1 * q 0) := by ring
    _ = p 0 * q 1 - p 1 * q 0 := by rw [huv, one_mul]

/-- Package `rotUnit u v` as a `LinearEquiv` when `u² + v² = 1`. -/
noncomputable def rotUnitLinearEquiv {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) :
    EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := rotUnit u v
  map_add' := rotUnit_add u v
  map_smul' := fun c p => by simpa using rotUnit_smul u v c p
  invFun := rotUnit u (-v)
  left_inv := rotUnit_comp_inv huv
  right_inv := rotUnit_inv_comp huv

/-- Image of an affine line under a rotation `rotUnit u v`. -/
noncomputable def rotUnitLine {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1)
    (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ℓ.map (rotUnitLinearEquiv huv).toAffineMap

lemma mem_rotUnitLine_iff {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1)
    {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} {p : EuclideanSpace ℝ (Fin 2)} :
    rotUnit u v p ∈ rotUnitLine huv ℓ ↔ p ∈ ℓ := by
  simp only [rotUnitLine, AffineSubspace.mem_map]
  constructor
  · rintro ⟨q, hq, heq⟩
    have : q = p := rotUnit_injective huv heq
    exact this ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

lemma isLine_rotUnitLine {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1)
    {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ) :
    IsLine (rotUnitLine huv ℓ) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := isLine_exists_two_points hℓ
  have hℓeq : lineThrough p q = ℓ := lineThrough_eq_of_mem hℓ hpq hp hq
  have hmap : rotUnitLine huv ℓ = lineThrough (rotUnit u v p) (rotUnit u v q) := by
    rw [← hℓeq, rotUnitLine, lineThrough, AffineSubspace.map_span]
    simp [lineThrough, Set.image_pair, rotUnitLinearEquiv]
  rw [hmap]
  exact isLine_lineThrough (fun h => hpq (rotUnit_injective huv h))

lemma rotUnitLine_injective {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) :
    Function.Injective (rotUnitLine huv) := by
  intro ℓ₁ ℓ₂ h
  ext p
  calc p ∈ ℓ₁ ↔ rotUnit u v p ∈ rotUnitLine huv ℓ₁ := (mem_rotUnitLine_iff huv).symm
    _ ↔ rotUnit u v p ∈ rotUnitLine huv ℓ₂ := by rw [h]
    _ ↔ p ∈ ℓ₂ := mem_rotUnitLine_iff huv

/-- Orientation-preserving Euclidean similarity `p ↦ c • rotUnit u v p + b`. -/
noncomputable def simMap (c u v : ℝ) (b : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun p => c • rotUnit u v p + b

lemma simMap_dist {c u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (b p q : EuclideanSpace ℝ (Fin 2)) :
    dist (simMap c u v b p) (simMap c u v b q) = |c| * dist p q := by
  rw [dist_eq_sqrt_normSq2, dist_eq_sqrt_normSq2]
  have hsub : simMap c u v b p - simMap c u v b q = c • rotUnit u v (p - q) := by
    simp only [simMap, add_sub_add_right_eq_sub, ← smul_sub, rotUnit_sub]
  rw [hsub]
  have hns : normSq2 (c • rotUnit u v (p - q)) = c ^ 2 * normSq2 (p - q) := by
    rw [← rotUnit_normSq2 huv (p - q)]
    unfold normSq2; simp [PiLp.smul_apply]; ring
  rw [hns, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **Generic Rotation Tilt (Forbidden Vectors):** Given any finite set `V` of nonzero vectors in `ℝ²`,
there exists a planar rotation `(u, v)` (`u² + v² = 1`) such that `(rotUnit u v w) 0 ≠ 0` for all `w ∈ V`. -/
theorem exists_rotation_avoiding_vertical
    (V : Finset (EuclideanSpace ℝ (Fin 2))) (hV : ∀ w ∈ V, w ≠ 0) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ ∀ w ∈ V, rotUnit u v w 0 ≠ 0 := by
  classical
  -- Rational unit circle parametrization: u(t) = (1 - t²)/(1 + t²), v(t) = 2t/(1 + t²).
  -- Pick t ∈ {0, 1, ..., 2|V|} avoiding the ≤ 2 bad roots of each w ∈ V.
  let S : Finset ℝ := (Finset.range (2 * V.card + 1)).image (fun k : ℕ => (k : ℝ))
  have hScard : S.card = 2 * V.card + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  let bad : EuclideanSpace ℝ (Fin 2) → Finset ℝ :=
    fun w => S.filter (fun t => (1 - t ^ 2) * w 0 - (2 * t) * w 1 = 0)
  have hbad_le : ∀ w ∈ V, (bad w).card ≤ 2 := by
    intro w hw
    have hw_ne : w ≠ 0 := hV w hw
    by_cases h0 : w 0 ≠ 0
    · apply quadratic_roots_card_le_two (a := -w 0) (b := -2 * w 1) (c := w 0) (neg_ne_zero.mpr h0)
      intro t ht
      have hEq := (Finset.mem_filter.mp ht).2
      linarith
    · push Not at h0
      have h1 : w 1 ≠ 0 := fun h1 => hw_ne (pt_ext h0 h1)
      have hsub : bad w ⊆ {0} := by
        intro t ht
        have hEq := (Finset.mem_filter.mp ht).2
        rw [h0] at hEq
        have ht0 : t = 0 := by
          have : (-2 * w 1) * t = 0 := by linarith
          exact (mul_eq_zero.mp this).resolve_left (fun h => h1 (by linarith))
        exact Finset.mem_singleton.mpr ht0
      exact le_trans (Finset.card_le_card hsub) (by simp)
  have hunion_le : (V.biUnion bad).card ≤ 2 * V.card := by
    calc (V.biUnion bad).card
        ≤ ∑ w ∈ V, (bad w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ V, 2 := Finset.sum_le_sum fun w hw => hbad_le w hw
      _ = 2 * V.card := by simp [mul_comm]
  have hlt : (V.biUnion bad).card < S.card := by omega
  obtain ⟨t, htS, ht_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let denom : ℝ := 1 + t ^ 2
  have hdenom_pos : 0 < denom := by unfold denom; positivity
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  refine ⟨(1 - t ^ 2) / denom, (2 * t) / denom, ?_, ?_⟩
  · unfold denom
    field_simp [hdenom_ne]
    ring
  · intro w hw
    rw [rotUnit_zero]
    intro hzero
    have hnum : (1 - t ^ 2) * w 0 - (2 * t) * w 1 = 0 := by
      have : ((1 - t ^ 2) * w 0 - (2 * t) * w 1) / denom = 0 := by
        calc ((1 - t ^ 2) * w 0 - (2 * t) * w 1) / denom
            = (1 - t ^ 2) / denom * w 0 - (2 * t) / denom * w 1 := by ring
          _ = 0 := hzero
      exact (div_eq_zero_iff.mp this).resolve_right hdenom_ne
    exact ht_not (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨htS, hnum⟩⟩)

/-- **Generic Rotation Avoiding Both Vertical & Horizontal Directions:**
Given finite `V` of nonzero vectors, there is a rotation making both coordinates of every `w ∈ V` nonzero. -/
theorem exists_rotation_avoiding_axes
    (V : Finset (EuclideanSpace ℝ (Fin 2))) (hV : ∀ w ∈ V, w ≠ 0) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ ∀ w ∈ V, rotUnit u v w 0 ≠ 0 ∧ rotUnit u v w 1 ≠ 0 := by
  classical
  let rot90 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w => mkPt (-w 1) (w 0)
  let V' := V ∪ V.image rot90
  have hV' : ∀ w ∈ V', w ≠ 0 := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwV | hwIm
    · exact hV w hwV
    · rcases Finset.mem_image.mp hwIm with ⟨z, hzV, rfl⟩
      intro h0
      have h1 : z 1 = 0 := by
        have := congrArg (fun a : EuclideanSpace ℝ (Fin 2) => a 0) h0
        simp [rot90] at this; exact this
      have h2 : z 0 = 0 := by
        have := congrArg (fun a : EuclideanSpace ℝ (Fin 2) => a 1) h0
        simp [rot90] at this; exact this
      exact hV z hzV (pt_ext h2 h1)
  obtain ⟨u, v, huv, hrot⟩ := exists_rotation_avoiding_vertical V' hV'
  refine ⟨u, v, huv, fun w hw => ⟨hrot w (Finset.mem_union_left _ hw), ?_⟩⟩
  have h90 := hrot (rot90 w) (Finset.mem_union_right _ (Finset.mem_image_of_mem rot90 hw))
  rw [rotUnit_zero] at h90
  rw [rotUnit_one]
  intro h1
  apply h90
  simp only [rot90, mkPt_zero, mkPt_one]
  linarith

/-- **Generic Rotation Tilt for Points and Lines:**
Given any finite set `P` of points and any finite set `L` of affine lines in `ℝ²`, there exists a
planar rotation `rotUnit u v` (`u² + v² = 1`) such that:
1. All rotated points in `P` have pairwise distinct `x`-coordinates AND pairwise distinct `y`-coordinates.
2. Every rotated line `ℓ ∈ L` is non-vertical (two distinct points on it have distinct `x`-coordinates). -/
theorem exists_rotation_generic
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, IsLine ℓ) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → rotUnit u v p 0 ≠ rotUnit u v q 0 ∧ rotUnit u v p 1 ≠ rotUnit u v q 1) ∧
      (∀ ℓ ∈ L, ∀ p ∈ ℓ, ∀ q ∈ ℓ, p ≠ q → rotUnit u v p 0 ≠ rotUnit u v q 0) := by
  classical
  let VP : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => pq.1 - pq.2)
  let dirVec : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2) :=
    fun ℓ =>
      if h : IsLine ℓ then
        let h2 := isLine_exists_two_points h
        h2.choose - h2.choose_spec.choose
      else 0
  let VL : Finset (EuclideanSpace ℝ (Fin 2)) := L.image dirVec
  let V := VP ∪ VL
  have hV : ∀ w ∈ V, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwP | hwL
    · rcases Finset.mem_image.mp hwP with ⟨⟨p, q⟩, hmem, rfl⟩
      exact sub_ne_zero.mpr (Finset.mem_filter.mp hmem).2
    · rcases Finset.mem_image.mp hwL with ⟨ℓ, hℓL, rfl⟩
      have hℓ := hL ℓ hℓL
      simp only [dirVec, dif_pos hℓ]
      exact sub_ne_zero.mpr (isLine_exists_two_points hℓ).choose_spec.choose_spec.1
  obtain ⟨u, v, huv, haxes⟩ := exists_rotation_avoiding_axes V hV
  refine ⟨u, v, huv, ?_, ?_⟩
  · intro p hp q hq hpq
    have hmem : p - q ∈ V := Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩, rfl⟩)
    obtain ⟨h0, h1⟩ := haxes (p - q) hmem
    rw [rotUnit_sub] at h0 h1
    simp only [PiLp.sub_apply] at h0 h1
    exact ⟨sub_ne_zero.mp h0, sub_ne_zero.mp h1⟩
  · intro ℓ hℓL p hp q hq hpq
    have hℓ := hL ℓ hℓL
    let h2 := isLine_exists_two_points hℓ
    let a := h2.choose
    let b := h2.choose_spec.choose
    have hab : a ≠ b := h2.choose_spec.choose_spec.1
    have ha : a ∈ ℓ := h2.choose_spec.choose_spec.2.1
    have hb : b ∈ ℓ := h2.choose_spec.choose_spec.2.2
    have hdir_mem : a - b ∈ V := Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨ℓ, hℓL, by simp [dirVec, dif_pos hℓ, a, b]⟩)
    have hrot_ab : rotUnit u v (a - b) 0 ≠ 0 := (haxes (a - b) hdir_mem).1
    -- Both p - q and a - b are nonzero elements of the 1-dim subspace ℓ.direction, hence proportional!
    have hℓeq : lineThrough a b = ℓ := lineThrough_eq_of_mem hℓ hab ha hb
    have hpa : p ∈ lineThrough a b := hℓeq.symm ▸ hp
    have hqa : q ∈ lineThrough a b := hℓeq.symm ▸ hq
    obtain ⟨tp, htp⟩ := mem_lineThrough_iff.mp hpa
    obtain ⟨tq, htq⟩ := mem_lineThrough_iff.mp hqa
    have htpq : tp ≠ tq := fun heq => hpq (by rw [htp, htq, heq])
    have hpq_eq : p - q = (tq - tp) • (a - b) := by
      rw [htp, htq]
      ext i
      simp [PiLp.sub_apply, PiLp.smul_apply]
      ring
    intro hEq
    have h0 : rotUnit u v (p - q) 0 = 0 := by
      rw [rotUnit_sub]; simp [PiLp.sub_apply, hEq]
    rw [hpq_eq, rotUnit_smul] at h0
    simp only [PiLp.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).elim (sub_ne_zero.mpr htpq.symm) hrot_ab

end PlanePrimitives

/-! ## Section 2: Sylvester–Gallai Theorem (Kelly's Shortest-Altitude Proof) -/

section SylvesterGallai

/-- Squared altitude (orthogonal distance squared) from point `p` to the line through `a` and `b`. -/
noncomputable def altSqPts (p a b : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  det2 (b - a) (p - a) ^ 2 / normSq2 (b - a)

/-- Orthogonal projection (foot of the altitude) of `p` onto the line through `a` and `b`. -/
noncomputable def footPts (p a b : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  a + (dot2 (p - a) (b - a) / normSq2 (b - a)) • (b - a)

lemma footPts_mem (p a b : EuclideanSpace ℝ (Fin 2)) :
    footPts p a b ∈ lineThrough a b :=
  mem_lineThrough_iff.mpr ⟨dot2 (p - a) (b - a) / normSq2 (b - a), rfl⟩

lemma footPts_orth (p a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b) :
    dot2 (p - footPts p a b) (b - a) = 0 := by
  have hns : normSq2 (b - a) ≠ 0 := by
    intro h0; exact hab ((sub_eq_zero.mp ((normSq2_eq_zero_iff (b - a)).mp h0)).symm)
  simp only [footPts, dot2, normSq2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hns ⊢
  field_simp [hns]
  ring

lemma normSq2_sub_footPts (p a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b) :
    normSq2 (p - footPts p a b) = altSqPts p a b := by
  have hns : normSq2 (b - a) ≠ 0 := by
    intro h0; exact hab ((sub_eq_zero.mp ((normSq2_eq_zero_iff (b - a)).mp h0)).symm)
  simp only [footPts, altSqPts, normSq2, dot2, det2, PiLp.sub_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] at hns ⊢
  field_simp [hns]
  ring

lemma pythagoras_line (p a b q : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b)
    (hq : q ∈ lineThrough a b) :
    normSq2 (p - q) = altSqPts p a b + normSq2 (q - footPts p a b) := by
  rw [← normSq2_sub_footPts p a b hab]
  obtain ⟨t, rfl⟩ := mem_lineThrough_iff.mp hq
  have horth := footPts_orth p a b hab
  let f := footPts p a b
  have hf_sub : a + t • (b - a) - f = (t - dot2 (p - a) (b - a) / normSq2 (b - a)) • (b - a) := by
    ext i
    simp [f, footPts, PiLp.sub_apply, PiLp.smul_apply]
    ring
  have hpq_split : p - (a + t • (b - a)) = (p - f) - (a + t • (b - a) - f) := by abel
  rw [hpq_split]
  have hcross : dot2 (p - f) (a + t • (b - a) - f) = 0 := by
    rw [hf_sub]
    unfold dot2 at horth ⊢
    simp only [PiLp.smul_apply, smul_eq_mul]
    calc (p - f) 0 * ((t - dot2 (p - a) (b - a) / normSq2 (b - a)) * (b - a) 0) +
         (p - f) 1 * ((t - dot2 (p - a) (b - a) / normSq2 (b - a)) * (b - a) 1)
        = (t - dot2 (p - a) (b - a) / normSq2 (b - a)) *
          ((p - f) 0 * (b - a) 0 + (p - f) 1 * (b - a) 1) := by ring
      _ = (t - dot2 (p - a) (b - a) / normSq2 (b - a)) * 0 := by rw [horth]
      _ = 0 := by ring
  simp only [normSq2, dot2, PiLp.sub_apply] at hcross ⊢
  nlinarith

/-- Squared altitude from `p` to a line `ℓ` is independent of the choice of two distinct points on `ℓ`. -/
lemma altSqPts_invariant {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ)
    (p : EuclideanSpace ℝ (Fin 2))
    {a b c d : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ ℓ) (hb : b ∈ ℓ) (hc : c ∈ ℓ) (hd : d ∈ ℓ) :
    altSqPts p a b = altSqPts p c d := by
  have h1 : lineThrough a b = ℓ := lineThrough_eq_of_mem hℓ hab ha hb
  have h2 : lineThrough c d = ℓ := lineThrough_eq_of_mem hℓ hcd hc hd
  have hf1_in : footPts p a b ∈ lineThrough c d := h2.symm ▸ h1 ▸ footPts_mem p a b
  have hf2_in : footPts p c d ∈ lineThrough a b := h1.symm ▸ h2 ▸ footPts_mem p c d
  have le1 : altSqPts p a b ≤ altSqPts p c d := by
    have hp := pythagoras_line p a b (footPts p c d) hab hf2_in
    rw [normSq2_sub_footPts p c d hcd] at hp
    linarith [normSq2_nonneg (footPts p c d - footPts p a b)]
  have le2 : altSqPts p c d ≤ altSqPts p a b := by
    have hp := pythagoras_line p c d (footPts p a b) hcd hf1_in
    rw [normSq2_sub_footPts p a b hab] at hp
    linarith [normSq2_nonneg (footPts p a b - footPts p c d)]
  exact le_antisymm le1 le2

/-- Squared altitude from a point `p` to a 1-dimensional affine line `ℓ`. -/
noncomputable def altSqLine (p : EuclideanSpace ℝ (Fin 2))
    (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  if h : IsLine ℓ then
    let h2 := isLine_exists_two_points h
    altSqPts p h2.choose h2.choose_spec.choose
  else 0

lemma altSqLine_eq_altSqPts {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ)
    (p : EuclideanSpace ℝ (Fin 2)) {a b : EuclideanSpace ℝ (Fin 2)}
    (hab : a ≠ b) (ha : a ∈ ℓ) (hb : b ∈ ℓ) :
    altSqLine p ℓ = altSqPts p a b := by
  simp only [altSqLine, dif_pos hℓ]
  let h2 := isLine_exists_two_points hℓ
  exact altSqPts_invariant hℓ p h2.choose_spec.choose_spec.1 hab
    h2.choose_spec.choose_spec.2.1 h2.choose_spec.choose_spec.2.2 ha hb

lemma altSqLine_pos_of_not_mem {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} (hℓ : IsLine ℓ)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∉ ℓ) :
    0 < altSqLine p ℓ := by
  obtain ⟨a, b, hab, ha, hb⟩ := isLine_exists_two_points hℓ
  rw [altSqLine_eq_altSqPts hℓ p hab ha hb, ← normSq2_sub_footPts p a b hab]
  rw [normSq2_pos_iff]
  intro h0
  have hpf : p = footPts p a b := sub_eq_zero.mp h0
  have hmem : p ∈ ℓ := by
    rw [hpf, ← lineThrough_eq_of_mem hℓ hab ha hb]
    exact footPts_mem p a b
  exact hp hmem

/-- **Kelly's Core Inequality:** If `p ∉ ℓ` has foot `f` on `ℓ` with unit/nonzero direction `v`,
and `q₁ = f + t₁ • v`, `q₂ = f + t₂ • v` with `0 ≤ t₁ < t₂`, then
`altSq(q₁, lineThrough p q₂) < altSq(p, ℓ)`. -/
lemma kelly_shorter_altitude {p f v : EuclideanSpace ℝ (Fin 2)}
    (hpf : p ≠ f) (hv : v ≠ 0) (horth : dot2 (p - f) v = 0)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht12 : t₁ < t₂) :
    altSqPts (f + t₁ • v) p (f + t₂ • v) < normSq2 (p - f) := by
  let h := p - f
  have hH : 0 < normSq2 h := (normSq2_pos_iff h).mpr (sub_ne_zero.mpr hpf)
  have hV : 0 < normSq2 v := (normSq2_pos_iff v).mpr hv
  have hq2p : (f + t₂ • v) - p = t₂ • v - h := by
    ext i; simp [h, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]; ring
  have hq1p : (f + t₁ • v) - p = t₁ • v - h := by
    ext i; simp [h, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]; ring
  have hns_q2p : normSq2 ((f + t₂ • v) - p) = t₂ ^ 2 * normSq2 v + normSq2 h := by
    rw [hq2p]
    simp only [normSq2, dot2, h, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at horth ⊢
    nlinarith
  have hdet_eq : det2 ((f + t₂ • v) - p) ((f + t₁ • v) - p) = (t₂ - t₁) * det2 h v := by
    rw [hq2p, hq1p]
    unfold det2
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hdet_hv_sq : det2 h v ^ 2 = normSq2 h * normSq2 v := by
    have := lagrange_det2_dot2 h v
    rw [horth] at this
    linarith
  have hdenom_pos : 0 < t₂ ^ 2 * normSq2 v + normSq2 h := by positivity
  unfold altSqPts
  rw [hns_q2p, hdet_eq, mul_pow, hdet_hv_sq, div_lt_iff₀ hdenom_pos]
  have hdiff_sq : (t₂ - t₁) ^ 2 ≤ t₂ ^ 2 := by nlinarith
  have hmul : (t₂ - t₁) ^ 2 * normSq2 v ≤ t₂ ^ 2 * normSq2 v :=
    mul_le_mul_of_nonneg_right hdiff_sq (le_of_lt hV)
  nlinarith

/-- **Sylvester–Gallai Theorem (Kelly's Shortest-Altitude Proof):**
Any finite non-collinear point set `P` in `EuclideanSpace ℝ (Fin 2)` determines an ordinary line
containing **exacty 2** points of `P`. -/
theorem sylvester_gallai (P : Finset (EuclideanSpace ℝ (Fin 2))) (hnc : ¬ IsCollinear P) :
    ∃ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      IsLine ℓ ∧ (P.filter (fun p => p ∈ ℓ)).card = 2 := by
  classical
  have hP3 : 3 ≤ P.card := by
    by_contra hlt
    push Not at hlt
    exact hnc (isCollinear_of_card_le_two (by omega))
  -- Pairs (p, ℓ) with p ∈ P, ℓ ∈ linesOf P, and p ∉ ℓ.
  let S : Finset (EuclideanSpace ℝ (Fin 2) × AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    (P ×ˢ linesOf P).filter (fun x => x.1 ∉ x.2)
  have hS_ne : S.Nonempty := by
    obtain ⟨p₁, hp₁⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    obtain ⟨p₂, hp₂⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hp₁]; omega : 0 < (P.erase p₁).card)
    have h12 : p₁ ≠ p₂ := (Finset.ne_of_mem_erase hp₂).symm
    have hp₂P : p₂ ∈ P := Finset.mem_of_mem_erase hp₂
    let ℓ₀ := lineThrough p₁ p₂
    have hℓ₀_mem : ℓ₀ ∈ linesOf P := mem_linesOf_iff.mpr ⟨p₁, hp₁, p₂, hp₂P, h12, rfl⟩
    have hnotall : ¬ ∀ r ∈ P, r ∈ ℓ₀ := fun hall => hnc ⟨ℓ₀, isLine_lineThrough h12, hall⟩
    push Not at hnotall
    obtain ⟨r, hrP, hr_not⟩ := hnotall
    exact ⟨(r, ℓ₀), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hrP, hℓ₀_mem⟩, hr_not⟩⟩
  -- Choose (p, ℓ) ∈ S minimizing altSqLine p ℓ.
  obtain ⟨⟨p, ℓ⟩, hplS, hmin⟩ := S.exists_min_image (fun x => altSqLine x.1 x.2) hS_ne
  have hpP : p ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hplS).1).1
  have hℓL : ℓ ∈ linesOf P := (Finset.mem_product.mp (Finset.mem_filter.mp hplS).1).2
  have hp_not : p ∉ ℓ := (Finset.mem_filter.mp hplS).2
  have hℓ_line : IsLine ℓ := isLine_of_mem_linesOf hℓL
  -- Every line in linesOf P contains at least 2 points of P.
  have hge2 : 2 ≤ (P.filter (fun q => q ∈ ℓ)).card := by
    rcases mem_linesOf_iff.mp hℓL with ⟨a, haP, b, hbP, hab, hℓab⟩
    have hsub : ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆ P.filter (fun q => q ∈ ℓ) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact Finset.mem_filter.mpr ⟨haP, hℓab ▸ mem_lineThrough_left x b⟩
      · rw [Finset.mem_singleton.mp hx']
        exact Finset.mem_filter.mpr ⟨hbP, hℓab ▸ mem_lineThrough_right a b⟩
    have hcard2 : ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))).card = 2 := Finset.card_pair hab
    exact le_trans (le_of_eq hcard2.symm) (Finset.card_le_card hsub)
  refine ⟨ℓ, hℓ_line, ?_⟩
  by_contra hne2
  have hge3 : 3 ≤ (P.filter (fun q => q ∈ ℓ)).card := by omega
  -- Pick 3 distinct points on ℓ and express them relative to the foot f of p on ℓ.
  obtain ⟨a, b, hab, ha, hb⟩ := isLine_exists_two_points hℓ_line
  have hℓeq : lineThrough a b = ℓ := lineThrough_eq_of_mem hℓ_line hab ha hb
  let f := footPts p a b
  let v := b - a
  have hv_ne : v ≠ 0 := sub_ne_zero.mpr hab.symm
  have hv_ns : normSq2 v ≠ 0 := fun h0 => hv_ne ((normSq2_eq_zero_iff v).mp h0)
  have hf_mem : f ∈ ℓ := hℓeq ▸ footPts_mem p a b
  have hpf_ne : p ≠ f := fun heq => hp_not (heq ▸ hf_mem)
  have horth : dot2 (p - f) v = 0 := footPts_orth p a b hab
  have halt_eq : altSqLine p ℓ = normSq2 (p - f) := by
    rw [altSqLine_eq_altSqPts hℓ_line p hab ha hb, ← normSq2_sub_footPts p a b hab]
  -- Parameterize every point q ∈ ℓ as f + coord(q) • v.
  let coord : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => dot2 (q - f) v / normSq2 v
  have hparam : ∀ q ∈ ℓ, q = f + coord q • v := by
    intro q hq
    have hq' : q ∈ lineThrough a b := hℓeq.symm ▸ hq
    obtain ⟨tq, htq⟩ := mem_lineThrough_iff.mp hq'
    let tf := dot2 (p - a) v / normSq2 v
    have hqf : q - f = (tq - tf) • v := by
      rw [htq]
      ext i
      simp [f, footPts, tf, v, PiLp.sub_apply, PiLp.smul_apply]
      ring
    have hc : coord q = tq - tf := by
      simp only [coord, hqf]
      have : dot2 ((tq - tf) • v) v = (tq - tf) * normSq2 v := by
        unfold dot2 normSq2; simp [PiLp.smul_apply]; ring
      rw [this, mul_div_cancel_right₀ _ hv_ns]
    rw [hc, ← hqf]
    abel
  -- Pigeonhole on sign of coord(q) for the ≥ 3 points in F = P.filter (· ∈ ℓ).
  let F := P.filter (fun q => q ∈ ℓ)
  let Fpos := F.filter (fun q => 0 ≤ coord q)
  let Fneg := F.filter (fun q => coord q ≤ 0)
  have hcov : F ⊆ Fpos ∪ Fneg := by
    intro q hq
    rcases le_total 0 (coord q) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq, h⟩)
  have hsum_card : 3 ≤ Fpos.card + Fneg.card :=
    le_trans hge3 (le_trans (Finset.card_le_card hcov) (Finset.card_union_le Fpos Fneg))
  -- Common contradiction builder given q₁, q₂ ∈ F and direction w with qᵢ = f + tᵢ • w, 0 ≤ t₁ < t₂.
  have hcontra : ∀ (w : EuclideanSpace ℝ (Fin 2)) (hw : w ≠ 0) (horth_w : dot2 (p - f) w = 0)
      (q₁ q₂ : EuclideanSpace ℝ (Fin 2)) (hq₁F : q₁ ∈ F) (hq₂F : q₂ ∈ F)
      (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (ht12 : t₁ < t₂)
      (hq₁_eq : q₁ = f + t₁ • w) (hq₂_eq : q₂ = f + t₂ • w), False := by
    intro w hw horth_w q₁ q₂ hq₁F hq₂F t₁ t₂ ht₁ ht12 hq₁_eq hq₂_eq
    have hq₁P : q₁ ∈ P := (Finset.mem_filter.mp hq₁F).1
    have hq₁ℓ : q₁ ∈ ℓ := (Finset.mem_filter.mp hq₁F).2
    have hq₂P : q₂ ∈ P := (Finset.mem_filter.mp hq₂F).1
    have hq₂ℓ : q₂ ∈ ℓ := (Finset.mem_filter.mp hq₂F).2
    have hpq₂ : p ≠ q₂ := fun heq => hp_not (heq ▸ hq₂ℓ)
    have hq₁q₂ : q₁ ≠ q₂ := by
      intro heq
      have : (t₂ - t₁) • w = 0 := by
        have hsub : q₂ - q₁ = (t₂ - t₁) • w := by
          rw [hq₁_eq, hq₂_eq]
          ext i; simp [PiLp.sub_apply, PiLp.smul_apply]; ring
        rw [← hsub, heq, sub_self]
      exact (smul_eq_zero.mp this).elim (sub_ne_zero.mpr (ne_of_gt ht12)) hw
    let ℓ' := lineThrough p q₂
    have hℓ'_line : IsLine ℓ' := isLine_lineThrough hpq₂
    have hℓ'_mem : ℓ' ∈ linesOf P := mem_linesOf_iff.mpr ⟨p, hpP, q₂, hq₂P, hpq₂, rfl⟩
    have hq₁_not : q₁ ∉ ℓ' := by
      intro hmem
      have heq_line : ℓ' = ℓ := affine_line_eq_of_two_mem hℓ'_line hℓ_line hq₁q₂
        hmem (mem_lineThrough_right p q₂) hq₁ℓ hq₂ℓ
      exact hp_not (heq_line ▸ mem_lineThrough_left p q₂)
    have hmemS : (q₁, ℓ') ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq₁P, hℓ'_mem⟩, hq₁_not⟩
    have hle := hmin (q₁, ℓ') hmemS
    have halt' : altSqLine q₁ ℓ' = altSqPts q₁ p q₂ :=
      altSqLine_eq_altSqPts hℓ'_line q₁ hpq₂ (mem_lineThrough_left p q₂) (mem_lineThrough_right p q₂)
    have hlt : altSqPts q₁ p q₂ < normSq2 (p - f) := by
      rw [hq₁_eq, hq₂_eq]
      exact kelly_shorter_altitude hpf_ne hw horth_w ht₁ ht12
    linarith
  -- Extract two distinct points from whichever of Fpos or Fneg has card ≥ 2.
  rcases (by omega : 2 ≤ Fpos.card ∨ 2 ≤ Fneg.card) with hpos2 | hneg2
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < Fpos.card)
    have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
    have hyF : y ∈ F := (Finset.mem_filter.mp hy).1
    have hx0 : 0 ≤ coord x := (Finset.mem_filter.mp hx).2
    have hy0 : 0 ≤ coord y := (Finset.mem_filter.mp hy).2
    have hcx_ne : coord x ≠ coord y := fun heq =>
      hxy (by rw [hparam x (Finset.mem_filter.mp hxF).2, hparam y (Finset.mem_filter.mp hyF).2, heq])
    rcases lt_or_gt_of_ne hcx_ne with hlt | hgt
    · exact hcontra v hv_ne horth x y hxF hyF (coord x) (coord y) hx0 hlt
        (hparam x (Finset.mem_filter.mp hxF).2) (hparam y (Finset.mem_filter.mp hyF).2)
    · exact hcontra v hv_ne horth y x hyF hxF (coord y) (coord x) hy0 hgt
        (hparam y (Finset.mem_filter.mp hyF).2) (hparam x (Finset.mem_filter.mp hxF).2)
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < Fneg.card)
    have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
    have hyF : y ∈ F := (Finset.mem_filter.mp hy).1
    have hx0 : 0 ≤ -coord x := neg_nonneg.mpr (Finset.mem_filter.mp hx).2
    have hy0 : 0 ≤ -coord y := neg_nonneg.mpr (Finset.mem_filter.mp hy).2
    have hcx_ne : -coord x ≠ -coord y := fun heq =>
      hxy (by rw [hparam x (Finset.mem_filter.mp hxF).2, hparam y (Finset.mem_filter.mp hyF).2, neg_inj.mp heq])
    have horth_neg : dot2 (p - f) (-v) = 0 := by
      simp only [dot2, PiLp.neg_apply, PiLp.sub_apply] at horth ⊢; linarith
    have hparam_neg : ∀ q ∈ ℓ, q = f + (-coord q) • (-v) := by
      intro q hq; rw [neg_smul_neg]; exact hparam q hq
    rcases lt_or_gt_of_ne hcx_ne with hlt | hgt
    · exact hcontra (-v) (neg_ne_zero.mpr hv_ne) horth_neg x y hxF hyF (-coord x) (-coord y) hx0 hlt
        (hparam_neg x (Finset.mem_filter.mp hxF).2) (hparam_neg y (Finset.mem_filter.mp hyF).2)
    · exact hcontra (-v) (neg_ne_zero.mpr hv_ne) horth_neg y x hyF hxF (-coord y) (-coord x) hy0 hgt
        (hparam_neg y (Finset.mem_filter.mp hyF).2) (hparam_neg x (Finset.mem_filter.mp hxF).2)

/-- Equivalent 2-point formulation of Sylvester–Gallai: any finite non-collinear `P ⊂ ℝ²` contains
two distinct points whose spanned line meets `P` in no third point. -/
theorem sylvester_gallai_pair (P : Finset (EuclideanSpace ℝ (Fin 2))) (hnc : ¬ IsCollinear P) :
    ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ ∀ r ∈ P, r ∈ lineThrough p q → r = p ∨ r = q := by
  classical
  obtain ⟨ℓ, hℓ, hcard⟩ := sylvester_gallai P hnc
  obtain ⟨p, q, hpq, hpair⟩ := Finset.card_eq_two.mp hcard
  have hp : p ∈ P.filter (fun x => x ∈ ℓ) := hpair ▸ Finset.mem_insert_self p {q}
  have hq : q ∈ P.filter (fun x => x ∈ ℓ) := hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hℓeq : lineThrough p q = ℓ :=
    lineThrough_eq_of_mem hℓ hpq (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  refine ⟨p, (Finset.mem_filter.mp hp).1, q, (Finset.mem_filter.mp hq).1, hpq, ?_⟩
  intro r hrP hr_mem
  have hrF : r ∈ P.filter (fun x => x ∈ ℓ) := Finset.mem_filter.mpr ⟨hrP, hℓeq ▸ hr_mem⟩
  rw [hpair] at hrF
  simpa using hrF

end SylvesterGallai

/-! ## Section 3: Topology-Free Wiring-Diagram Planar Bound & Multigraph Crossing Lemma -/

section WiringCrossingLemma

/-! ### 3A. Elementary Finite-Graph Component–Edge Inequality -/

/-- Any walk in `G` that is not a walk in `G.deleteEdges {s(u, v)}` reaches `{u, v}` from its start
using only edges of `G.deleteEdges {s(u, v)}`. -/
private lemma walk_reaches_deleted_endpoint {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (w : G.Walk x y) :
    (G.deleteEdges {s(u, v)}).Reachable x y ∨
      ((G.deleteEdges {s(u, v)}).Reachable x u ∨ (G.deleteEdges {s(u, v)}).Reachable x v) := by
  induction w with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons a b c hab w ih =>
    by_cases hdel : s(a, b) = s(u, v)
    · right
      have hmem : a ∈ (s(u, v) : Sym2 V) := hdel ▸ Sym2.mem_mk_left a b
      rcases Sym2.mem_iff.mp hmem with rfl | rfl
      · exact Or.inl (SimpleGraph.Reachable.refl _)
      · exact Or.inr (SimpleGraph.Reachable.refl _)
    · have hab' : (G.deleteEdges {s(u, v)}).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using hdel⟩
      have hstep : (G.deleteEdges {s(u, v)}).Reachable a b := hab'.reachable
      rcases ih with hbc | hbu | hbv
      · exact Or.inl (hstep.trans hbc)
      · exact Or.inr (Or.inl (hstep.trans hbu))
      · exact Or.inr (Or.inr (hstep.trans hbv))

/-- For any finite simple graph `G`, `|V| ≤ #(connected components of G) + |E(G)|`. -/
lemma simpleGraph_card_le_components_add_edges {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card V ≤ Fintype.card G.ConnectedComponent + G.edgeFinset.card := by
  classical
  -- Strong induction on the number of edges `m = G.edgeFinset.card`.
  suffices h : ∀ (m : ℕ) (G : SimpleGraph V), G.edgeFinset.card = m →
      Fintype.card V ≤ Fintype.card G.ConnectedComponent + m by
    exact h G.edgeFinset.card G rfl
  intro m
  induction m with
  | zero =>
    intro G hG0
    have hbot : G = ⊥ := by
      ext x y
      simp only [SimpleGraph.bot_adj, iff_false]
      intro hadj
      have hmem : s(x, y) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
      rw [Finset.card_eq_zero.mp hG0] at hmem
      exact Finset.notMem_empty _ hmem
    subst hbot
    have hinj : Function.Injective ((⊥ : SimpleGraph V).connectedComponentMk) := by
      intro x y hxy
      have hreach : (⊥ : SimpleGraph V).Reachable x y :=
        SimpleGraph.ConnectedComponent.exact hxy
      obtain ⟨w⟩ := hreach
      cases w with
      | nil => rfl
      | cons hadj _ => exact False.elim hadj
    simpa using Fintype.card_le_of_injective _ hinj
  | succ m ih =>
    intro G hGm
    have hne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      let G' := G.deleteEdges {s(u, v)}
      have hG'le : G' ≤ G := SimpleGraph.deleteEdges_le _
      have hG'card : G'.edgeFinset.card = m := by
        have hsub : G'.edgeFinset = G.edgeFinset.erase s(u, v) := by
          ext x
          simp only [G', SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
            Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase, and_comm]
        rw [hsub, Finset.card_erase_of_mem he, hGm]
        omega
      have hih := ih G' (by convert hG'card)
      let φ : G'.ConnectedComponent → G.ConnectedComponent :=
        SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hG'le)
      have hinj_off : Set.InjOn φ ((Finset.univ.erase (G'.connectedComponentMk v)) : Set G'.ConnectedComponent) := by
        intro c₁ hc₁ c₂ hc₂ hφ
        rcases Quot.exists_rep c₁ with ⟨x, rfl⟩
        rcases Quot.exists_rep c₂ with ⟨y, rfl⟩
        have hxy : G.Reachable x y := SimpleGraph.ConnectedComponent.exact hφ
        obtain ⟨w⟩ := hxy
        have h1 := walk_reaches_deleted_endpoint (u := u) (v := v) w
        rcases h1 with hxy' | hxu | hxv
        · exact SimpleGraph.ConnectedComponent.sound hxy'
        · have h2 := walk_reaches_deleted_endpoint (u := u) (v := v) w.reverse
          rcases h2 with hyx' | hyu | hyv
          · exact SimpleGraph.ConnectedComponent.sound hyx'.symm
          · exact SimpleGraph.ConnectedComponent.sound (hxu.trans hyu.symm)
          · exfalso
            have hv2 : G'.connectedComponentMk y = G'.connectedComponentMk v :=
              SimpleGraph.ConnectedComponent.sound hyv
            exact (Finset.ne_of_mem_erase hc₂) hv2
        · exfalso
          have hv1 : G'.connectedComponentMk x = G'.connectedComponentMk v :=
            SimpleGraph.ConnectedComponent.sound hxv
          exact (Finset.ne_of_mem_erase hc₁) hv1
      have hcomp_le : Fintype.card G'.ConnectedComponent ≤ Fintype.card G.ConnectedComponent + 1 := by
        have h1 : (Finset.univ.erase (G'.connectedComponentMk v)).card ≤ Fintype.card G.ConnectedComponent := by
          rw [← Finset.card_image_of_injOn hinj_off]
          exact Finset.card_le_univ _
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h1
        have hpos : 0 < Fintype.card G'.ConnectedComponent :=
          Fintype.card_pos_iff.mpr ⟨G'.connectedComponentMk v⟩
        omega
      omega

/-! ### 3B. Topology-Free `SlabWiring` Structure & Zero-Crossing Planar Bound (`|E| ≤ 3 n`) -/

/-- Edges active on slab `s : Fin (n + 1)` (between vertex `s - 1` and vertex `s`): `e.1 < s ≤ e.2`. -/
def activeEdges {n : ℕ} (E : Finset (Fin n × Fin n)) (s : Fin (n + 1)) : Finset (Fin n × Fin n) :=
  E.filter (fun e => e.1.val < s.val ∧ s.val ≤ e.2.val)

/-- Edges passing strictly over or under vertex `k : Fin n`: `e.1 < k < e.2`. -/
def passingEdges {n : ℕ} (E : Finset (Fin n × Fin n)) (k : Fin n) : Finset (Fin n × Fin n) :=
  E.filter (fun e => e.1.val < k.val ∧ k.val < e.2.val)

/-- Edges ending at vertex `k : Fin n`: `e.2 = k`. -/
def endingEdges {n : ℕ} (E : Finset (Fin n × Fin n)) (k : Fin n) : Finset (Fin n × Fin n) :=
  E.filter (fun e => e.2 = k)

/-- Edges starting at vertex `k : Fin n`: `e.1 = k`. -/
def startingEdges {n : ℕ} (E : Finset (Fin n × Fin n)) (k : Fin n) : Finset (Fin n × Fin n) :=
  E.filter (fun e => e.1 = k)

lemma activeEdges_zero {n : ℕ} (E : Finset (Fin n × Fin n)) : activeEdges E 0 = ∅ := by
  ext e; simp [activeEdges]

lemma activeEdges_last {n : ℕ} (E : Finset (Fin n × Fin n)) : activeEdges E (Fin.last n) = ∅ := by
  ext e; simp only [activeEdges, Finset.mem_filter, Fin.val_last, Finset.notMem_empty, iff_false]
  rintro ⟨_, _, hle⟩; omega

lemma activeEdges_castSucc {n : ℕ} {E : Finset (Fin n × Fin n)} (hE : ∀ e ∈ E, e.1 < e.2) (k : Fin n) :
    activeEdges E k.castSucc = passingEdges E k ∪ endingEdges E k := by
  ext e
  simp only [activeEdges, passingEdges, endingEdges, Finset.mem_filter, Finset.mem_union,
    Fin.val_castSucc]
  constructor
  · rintro ⟨heE, h1, h2⟩
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact Or.inl ⟨heE, h1, hlt⟩
    · exact Or.inr ⟨heE, Fin.ext heq.symm⟩
  · rintro (⟨heE, h1, h2⟩ | ⟨heE, h2⟩)
    · exact ⟨heE, h1, le_of_lt h2⟩
    · have hlt : e.1.val < e.2.val := hE e heE
      refine ⟨heE, ?_, ?_⟩
      · rw [← h2]; exact hlt
      · rw [h2]

lemma activeEdges_succ {n : ℕ} {E : Finset (Fin n × Fin n)} (hE : ∀ e ∈ E, e.1 < e.2) (k : Fin n) :
    activeEdges E k.succ = passingEdges E k ∪ startingEdges E k := by
  ext e
  simp only [activeEdges, passingEdges, startingEdges, Finset.mem_filter, Finset.mem_union,
    Fin.val_succ]
  constructor
  · rintro ⟨heE, h1, h2⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h1) with hlt | heq
    · exact Or.inl ⟨heE, hlt, by omega⟩
    · exact Or.inr ⟨heE, Fin.ext heq⟩
  · rintro (⟨heE, h1, h2⟩ | ⟨heE, h1⟩)
    · exact ⟨heE, by omega, by omega⟩
    · have hlt := hE e heE
      refine ⟨heE, by rw [h1]; omega, ?_⟩
      rw [← h1]; exact hlt

lemma disjoint_passing_ending {n : ℕ} (E : Finset (Fin n × Fin n)) (k : Fin n) :
    Disjoint (passingEdges E k) (endingEdges E k) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  simp only [passingEdges, endingEdges, Finset.mem_filter] at h1 h2
  rw [h2.2] at h1; omega

lemma disjoint_passing_starting {n : ℕ} (E : Finset (Fin n × Fin n)) (k : Fin n) :
    Disjoint (passingEdges E k) (startingEdges E k) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  simp only [passingEdges, startingEdges, Finset.mem_filter] at h1 h2
  rw [h2.2] at h1; omega

lemma sum_activeEdges_eq_edges_add_sum_passing {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : ∀ e ∈ E, e.1 < e.2) :
    ∑ s : Fin (n + 1), (activeEdges E s).card =
      E.card + ∑ k : Fin n, (passingEdges E k).card := by
  have hact : ∑ s : Fin (n + 1), (activeEdges E s).card =
      ∑ e ∈ E, ((Finset.univ : Finset (Fin (n + 1))).filter (fun s => e.1.val < s.val ∧ s.val ≤ e.2.val)).card := by
    simp only [activeEdges, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpass : ∑ k : Fin n, (passingEdges E k).card =
      ∑ e ∈ E, ((Finset.univ : Finset (Fin n)).filter (fun k => e.1.val < k.val ∧ k.val < e.2.val)).card := by
    simp only [passingEdges, Finset.card_filter]
    rw [Finset.sum_comm]
  have hones : E.card = ∑ _e ∈ E, 1 := by simp
  rw [hact, hpass, hones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  have hlt : e.1.val < e.2.val := hE e he
  -- The active slabs for e are {k.castSucc | e.1 < k < e.2} ∪ {e.2.castSucc}!
  let S_act := (Finset.univ : Finset (Fin (n + 1))).filter (fun s => e.1.val < s.val ∧ s.val ≤ e.2.val)
  let S_pass := (Finset.univ : Finset (Fin n)).filter (fun k => e.1.val < k.val ∧ k.val < e.2.val)
  have hbij : S_act = insert e.2.castSucc (S_pass.image Fin.castSucc) := by
    ext s
    simp only [S_act, S_pass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le h2 with hlt2 | heq2
      · right
        refine ⟨⟨s.val, by omega⟩, ⟨h1, hlt2⟩, Fin.ext rfl⟩
      · left; exact Fin.ext heq2
    · rintro (rfl | ⟨k, ⟨h1, h2⟩, rfl⟩)
      · exact ⟨hlt, le_rfl⟩
      · exact ⟨h1, le_of_lt h2⟩
  have hnotmem : e.2.castSucc ∉ S_pass.image Fin.castSucc := by
    simp only [S_pass, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨k, ⟨_, h2⟩, hEq⟩
    have : k.val = e.2.val := congrArg Fin.val (Fin.castSucc_inj.mp hEq)
    omega
  change S_act.card = 1 + S_pass.card
  rw [hbij, Finset.card_insert_of_notMem hnotmem,
    Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
  omega

/-- Ordered inversions between two height functions `f, g : α → ℝ` on a finite set `A`.
Each unordered inverted pair `{a, b}` appears exactly once (as `(a, b)` with `f a < f b`). -/
noncomputable def invPairs {α : Type*} (A : Finset α) (f g : α → ℝ) : Finset (α × α) :=
  (A ×ˢ A).filter (fun p => f p.1 < f p.2 ∧ g p.2 < g p.1)

/-- Topology-free combinatorial wiring diagram of a simple graph `E` on `Fin n` (`e.1 < e.2`). -/
structure SlabWiring (n : ℕ) (E : Finset (Fin n × Fin n)) where
  edge_lt : ∀ e ∈ E, e.1 < e.2
  posL : Fin (n + 1) → (Fin n × Fin n) → ℝ
  posR : Fin (n + 1) → (Fin n × Fin n) → ℝ
  posL_inj : ∀ s, Set.InjOn (posL s) (activeEdges E s)
  posR_inj : ∀ s, Set.InjOn (posR s) (activeEdges E s)
  above : Fin n → (Fin n × Fin n) → Bool
  pass_order : ∀ (k : Fin n), ∀ e₁ ∈ passingEdges E k, ∀ e₂ ∈ passingEdges E k,
    posR k.castSucc e₁ < posR k.castSucc e₂ ↔ posL k.succ e₁ < posL k.succ e₂
  pass_above_end : ∀ (k : Fin n), ∀ e ∈ passingEdges E k, ∀ e' ∈ endingEdges E k,
    if above k e then posR k.castSucc e' < posR k.castSucc e
    else posR k.castSucc e < posR k.castSucc e'
  pass_above_start : ∀ (k : Fin n), ∀ e ∈ passingEdges E k, ∀ e' ∈ startingEdges E k,
    if above k e then posL k.succ e' < posL k.succ e
    else posL k.succ e < posL k.succ e'
  pass_below_lt_above : ∀ (k : Fin n), ∀ e₁ ∈ passingEdges E k, ∀ e₂ ∈ passingEdges E k,
    above k e₁ = false → above k e₂ = true → posR k.castSucc e₁ < posR k.castSucc e₂

/-- Total crossing (inversion) count of a `SlabWiring`. -/
noncomputable def SlabWiring.crossings {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E) : ℕ :=
  ∑ s : Fin (n + 1), (invPairs (activeEdges E s) (W.posL s) (W.posR s)).card

/-- Zero-crossing `SlabWiring` has identical relative vertical order on `posL s` and `posR s`. -/
lemma SlabWiring.posL_lt_iff_posR_lt_of_zero {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (h0 : W.crossings = 0) (s : Fin (n + 1))
    {e₁ e₂ : Fin n × Fin n} (h₁ : e₁ ∈ activeEdges E s) (h₂ : e₂ ∈ activeEdges E s) :
    W.posL s e₁ < W.posL s e₂ ↔ W.posR s e₁ < W.posR s e₂ := by
  have hs0 : (invPairs (activeEdges E s) (W.posL s) (W.posR s)).card = 0 := by
    have hsum := Finset.sum_eq_zero_iff.mp h0 s (Finset.mem_univ s)
    exact hsum
  have hemp : invPairs (activeEdges E s) (W.posL s) (W.posR s) = ∅ := Finset.card_eq_zero.mp hs0
  constructor
  · intro hlt
    have hne : e₁ ≠ e₂ := fun heq => lt_irrefl _ (heq ▸ hlt)
    have hrne : W.posR s e₁ ≠ W.posR s e₂ := fun heq => hne (W.posR_inj s h₁ h₂ heq)
    rcases lt_or_gt_of_ne hrne with h | h
    · exact h
    · exfalso
      have hmem : (e₁, e₂) ∈ invPairs (activeEdges E s) (W.posL s) (W.posR s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₁, h₂⟩, hlt, h⟩
      rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
  · intro hlt
    have hne : e₁ ≠ e₂ := fun heq => lt_irrefl _ (heq ▸ hlt)
    have hlne : W.posL s e₁ ≠ W.posL s e₂ := fun heq => hne (W.posL_inj s h₁ h₂ heq)
    rcases lt_or_gt_of_ne hlne with h | h
    · exact h
    · exfalso
      have hmem : (e₂, e₁) ∈ invPairs (activeEdges E s) (W.posL s) (W.posR s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₂, h₁⟩, h, hlt⟩
      rw [hemp] at hmem; exact Finset.notMem_empty _ hmem

/-- Rank of an active edge `e` in slab `s` under `W.posL s`. -/
noncomputable def SlabWiring.rankL {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    (s : Fin (n + 1)) (e : Fin n × Fin n) : ℕ :=
  ((activeEdges E s).filter (fun e' => W.posL s e' < W.posL s e)).card

lemma SlabWiring.rankL_lt {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    (s : Fin (n + 1)) {e : Fin n × Fin n} (he : e ∈ activeEdges E s) :
    W.rankL s e < (activeEdges E s).card := by
  unfold SlabWiring.rankL
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro hEq
  have hmem : e ∈ (activeEdges E s).filter (fun e' => W.posL s e' < W.posL s e) := by
    rw [hEq]; exact he
  exact lt_irrefl _ (Finset.mem_filter.mp hmem).2

lemma SlabWiring.rankL_lt_iff {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    (s : Fin (n + 1)) {e₁ e₂ : Fin n × Fin n}
    (h₁ : e₁ ∈ activeEdges E s) (_h₂ : e₂ ∈ activeEdges E s) :
    W.rankL s e₁ < W.rankL s e₂ ↔ W.posL s e₁ < W.posL s e₂ := by
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    have hsub : (activeEdges E s).filter (fun e' => W.posL s e' < W.posL s e₂) ⊆
        (activeEdges E s).filter (fun e' => W.posL s e' < W.posL s e₁) := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 hge⟩
    have : W.rankL s e₂ ≤ W.rankL s e₁ := Finset.card_le_card hsub
    omega
  · intro hlt
    unfold SlabWiring.rankL
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_trans hx.2 hlt⟩
    · intro hEq
      have hmem : e₁ ∈ (activeEdges E s).filter (fun e' => W.posL s e' < W.posL s e₂) :=
        Finset.mem_filter.mpr ⟨h₁, hlt⟩
      rw [← hEq] at hmem
      exact lt_irrefl _ (Finset.mem_filter.mp hmem).2

lemma SlabWiring.rankL_inj {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    (s : Fin (n + 1)) : Set.InjOn (W.rankL s) (activeEdges E s) := by
  intro e₁ h₁ e₂ h₂ hEq
  by_contra hne
  have hpne : W.posL s e₁ ≠ W.posL s e₂ := fun h => hne (W.posL_inj s h₁ h₂ h)
  rcases lt_or_gt_of_ne hpne with h | h
  · have := (W.rankL_lt_iff s h₁ h₂).mpr h; omega
  · have := (W.rankL_lt_iff s h₂ h₁).mpr h; omega

lemma SlabWiring.exists_edge_of_rankL {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    (s : Fin (n + 1)) {r : ℕ} (hr : r < (activeEdges E s).card) :
    ∃ e ∈ activeEdges E s, W.rankL s e = r := by
  let imgs := (activeEdges E s).image (W.rankL s)
  have hsub : imgs ⊆ Finset.range (activeEdges E s).card := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
    exact Finset.mem_range.mpr (W.rankL_lt s he)
  have hcard : imgs.card = (Finset.range (activeEdges E s).card).card := by
    rw [Finset.card_image_of_injOn (W.rankL_inj s), Finset.card_range]
  have heq : imgs = Finset.range (activeEdges E s).card := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hmem : r ∈ imgs := heq ▸ Finset.mem_range.mpr hr
  exact Finset.mem_image.mp hmem

/-- Number of passing edges strictly below vertex `k : Fin n`. -/
def SlabWiring.belowCount {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E) (k : Fin n) : ℕ :=
  ((passingEdges E k).filter (fun e => W.above k e = false)).card

/-- Number of passing edges strictly above vertex `k : Fin n`. -/
def SlabWiring.aboveCount {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E) (k : Fin n) : ℕ :=
  ((passingEdges E k).filter (fun e => W.above k e = true)).card

lemma SlabWiring.belowCount_add_aboveCount {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (k : Fin n) :
    W.belowCount k + W.aboveCount k = (passingEdges E k).card := by
  unfold belowCount aboveCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    cases W.above k e <;> simp
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2; cases h2.2

/-- Exact rank structure of a zero-crossing `SlabWiring` on slabs `k.castSucc` and `k.succ`. -/
lemma SlabWiring.rankL_pass_below_eq {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (h0 : W.crossings = 0) (k : Fin n)
    {e : Fin n × Fin n} (he : e ∈ passingEdges E k) (hbelow : W.above k e = false) :
    W.rankL k.castSucc e < W.belowCount k ∧ W.rankL k.succ e = W.rankL k.castSucc e := by
  have heL : e ∈ activeEdges E k.castSucc :=
    (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_left _ he
  have heR : e ∈ activeEdges E k.succ :=
    (activeEdges_succ W.edge_lt k).symm ▸ Finset.mem_union_left _ he
  -- Every edge below e on slab k.castSucc MUST be a passing edge with above = false!
  have hsetL : (activeEdges E k.castSucc).filter (fun e' => W.posL k.castSucc e' < W.posL k.castSucc e) =
      ((passingEdges E k).filter (fun e' => W.above k e' = false)).filter
        (fun e' => W.posR k.castSucc e' < W.posR k.castSucc e) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he'act, hltL⟩
      have hltR := (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mp hltL
      rw [activeEdges_castSucc W.edge_lt k, Finset.mem_union] at he'act
      rcases he'act with he'p | he'end
      · refine ⟨⟨he'p, ?_⟩, hltR⟩
        cases hab : W.above k e'
        · rfl
        · exfalso
          have hgt := W.pass_below_lt_above k e he e' he'p hbelow hab
          linarith
      · exfalso
        have hgt := W.pass_above_end k e he e' he'end
        rw [hbelow] at hgt; simp only [Bool.false_eq_true, ↓reduceIte] at hgt
        linarith
    · rintro ⟨⟨he'p, _⟩, hltR⟩
      have he'act : e' ∈ activeEdges E k.castSucc :=
        (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
      exact ⟨he'act, (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mpr hltR⟩
  -- Every edge below e on slab k.succ is the EXACT SAME set!
  have hsetR : (activeEdges E k.succ).filter (fun e' => W.posL k.succ e' < W.posL k.succ e) =
      ((passingEdges E k).filter (fun e' => W.above k e' = false)).filter
        (fun e' => W.posR k.castSucc e' < W.posR k.castSucc e) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he'act, hlt⟩
      rw [activeEdges_succ W.edge_lt k, Finset.mem_union] at he'act
      rcases he'act with he'p | he'st
      · have hltR := (W.pass_order k e' he'p e he).mpr hlt
        refine ⟨⟨he'p, ?_⟩, hltR⟩
        cases hab : W.above k e'
        · rfl
        · exfalso
          have hgt := W.pass_below_lt_above k e he e' he'p hbelow hab
          linarith
      · exfalso
        have hgt := W.pass_above_start k e he e' he'st
        rw [hbelow] at hgt; simp only [Bool.false_eq_true, ↓reduceIte] at hgt
        linarith
    · rintro ⟨⟨he'p, _⟩, hltR⟩
      have he'act : e' ∈ activeEdges E k.succ :=
        (activeEdges_succ W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
      exact ⟨he'act, (W.pass_order k e' he'p e he).mp hltR⟩
  constructor
  · unfold SlabWiring.rankL SlabWiring.belowCount
    rw [hsetL]
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hEq
    have hmem : e ∈ ((passingEdges E k).filter (fun e' => W.above k e' = false)).filter
        (fun e' => W.posR k.castSucc e' < W.posR k.castSucc e) := by
      rw [hEq]; exact Finset.mem_filter.mpr ⟨he, hbelow⟩
    exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  · unfold SlabWiring.rankL
    rw [hsetL, hsetR]

lemma SlabWiring.rankL_pass_above_eq {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (h0 : W.crossings = 0) (k : Fin n)
    {e : Fin n × Fin n} (he : e ∈ passingEdges E k) (habove : W.above k e = true) :
    ∃ s : ℕ, s < W.aboveCount k ∧
      W.rankL k.castSucc e = W.belowCount k + (endingEdges E k).card + s ∧
      W.rankL k.succ e = W.belowCount k + (startingEdges E k).card + s := by
  have heL : e ∈ activeEdges E k.castSucc :=
    (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_left _ he
  let Pbelow := (passingEdges E k).filter (fun e' => W.above k e' = false)
  let Pabove := (passingEdges E k).filter (fun e' => W.above k e' = true)
  let Pabove_lt := Pabove.filter (fun e' => W.posR k.castSucc e' < W.posR k.castSucc e)
  refine ⟨Pabove_lt.card, ?_, ?_, ?_⟩
  · refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hEq
    have hmem : e ∈ Pabove_lt := hEq ▸ Finset.mem_filter.mpr ⟨he, habove⟩
    exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  · -- Slab k.castSucc: edges below e = Pbelow ⊔ endingEdges E k ⊔ Pabove_lt
    have hsetL : (activeEdges E k.castSucc).filter (fun e' => W.posL k.castSucc e' < W.posL k.castSucc e) =
        Pbelow ∪ endingEdges E k ∪ Pabove_lt := by
      ext e'
      simp only [Finset.mem_filter, Finset.mem_union, Pbelow, Pabove, Pabove_lt]
      constructor
      · rintro ⟨he'act, hltL⟩
        have hltR := (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mp hltL
        rw [activeEdges_castSucc W.edge_lt k, Finset.mem_union] at he'act
        rcases he'act with he'p | he'end
        · cases hab : W.above k e'
          · exact Or.inl (Or.inl ⟨he'p, rfl⟩)
          · exact Or.inr ⟨⟨he'p, rfl⟩, hltR⟩
        · exact Or.inl (Or.inr he'end)
      · rintro ((⟨he'p, hbel⟩ | he'end) | ⟨⟨he'p, _⟩, hltR⟩)
        · have he'act : e' ∈ activeEdges E k.castSucc :=
            (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
          have hltR := W.pass_below_lt_above k e' he'p e he hbel habove
          exact ⟨he'act, (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mpr hltR⟩
        · have he'act : e' ∈ activeEdges E k.castSucc :=
            (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_right _ he'end
          have hltR := W.pass_above_end k e he e' he'end
          rw [habove] at hltR; simp only [↓reduceIte] at hltR
          exact ⟨he'act, (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mpr hltR⟩
        · have he'act : e' ∈ activeEdges E k.castSucc :=
            (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
          exact ⟨he'act, (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mpr hltR⟩
    unfold SlabWiring.rankL SlabWiring.belowCount
    rw [hsetL]
    have hd1 : Disjoint Pbelow (endingEdges E k) :=
      Disjoint.mono_left (Finset.filter_subset _ _) (disjoint_passing_ending E k)
    have hd2 : Disjoint (Pbelow ∪ endingEdges E k) Pabove_lt := by
      rw [Finset.disjoint_left]
      intro x hx hy
      have hy1 : x ∈ passingEdges E k ∧ W.above k x = true := Finset.mem_filter.mp (Finset.mem_filter.mp hy).1
      rcases Finset.mem_union.mp hx with hxb | hxe
      · have := (Finset.mem_filter.mp hxb).2; rw [hy1.2] at this; cases this
      · exact Finset.disjoint_left.mp (disjoint_passing_ending E k) hy1.1 hxe
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  · -- Slab k.succ: edges below e = Pbelow ⊔ startingEdges E k ⊔ Pabove_lt
    have hsetR : (activeEdges E k.succ).filter (fun e' => W.posL k.succ e' < W.posL k.succ e) =
        Pbelow ∪ startingEdges E k ∪ Pabove_lt := by
      ext e'
      simp only [Finset.mem_filter, Finset.mem_union, Pbelow, Pabove, Pabove_lt]
      constructor
      · rintro ⟨he'act, hlt⟩
        rw [activeEdges_succ W.edge_lt k, Finset.mem_union] at he'act
        rcases he'act with he'p | he'st
        · have hltR := (W.pass_order k e' he'p e he).mpr hlt
          cases hab : W.above k e'
          · exact Or.inl (Or.inl ⟨he'p, rfl⟩)
          · exact Or.inr ⟨⟨he'p, rfl⟩, hltR⟩
        · exact Or.inl (Or.inr he'st)
      · rintro ((⟨he'p, hbel⟩ | he'st) | ⟨⟨he'p, _⟩, hltR⟩)
        · have he'act : e' ∈ activeEdges E k.succ :=
            (activeEdges_succ W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
          have hltR := W.pass_below_lt_above k e' he'p e he hbel habove
          exact ⟨he'act, (W.pass_order k e' he'p e he).mp hltR⟩
        · have he'act : e' ∈ activeEdges E k.succ :=
            (activeEdges_succ W.edge_lt k).symm ▸ Finset.mem_union_right _ he'st
          have hlt := W.pass_above_start k e he e' he'st
          rw [habove] at hlt; simp only [↓reduceIte] at hlt
          exact ⟨he'act, hlt⟩
        · have he'act : e' ∈ activeEdges E k.succ :=
            (activeEdges_succ W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
          exact ⟨he'act, (W.pass_order k e' he'p e he).mp hltR⟩
    unfold SlabWiring.rankL SlabWiring.belowCount
    rw [hsetR]
    have hd1 : Disjoint Pbelow (startingEdges E k) :=
      Disjoint.mono_left (Finset.filter_subset _ _) (disjoint_passing_starting E k)
    have hd2 : Disjoint (Pbelow ∪ startingEdges E k) Pabove_lt := by
      rw [Finset.disjoint_left]
      intro x hx hy
      have hy1 : x ∈ passingEdges E k ∧ W.above k x = true := Finset.mem_filter.mp (Finset.mem_filter.mp hy).1
      rcases Finset.mem_union.mp hx with hxb | hxs
      · have := (Finset.mem_filter.mp hxb).2; rw [hy1.2] at this; cases this
      · exact Finset.disjoint_left.mp (disjoint_passing_starting E k) hy1.1 hxs
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]

lemma SlabWiring.rankL_ending_range {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (h0 : W.crossings = 0) (k : Fin n)
    {e : Fin n × Fin n} (he : e ∈ endingEdges E k) :
    W.belowCount k ≤ W.rankL k.castSucc e ∧ W.rankL k.castSucc e < W.belowCount k + (endingEdges E k).card := by
  have heL : e ∈ activeEdges E k.castSucc :=
    (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_right _ he
  let Pbelow := (passingEdges E k).filter (fun e' => W.above k e' = false)
  have hsub1 : Pbelow ⊆ (activeEdges E k.castSucc).filter (fun e' => W.posL k.castSucc e' < W.posL k.castSucc e) := by
    intro e' he'
    have ⟨he'p, hbel⟩ := Finset.mem_filter.mp he'
    have he'act : e' ∈ activeEdges E k.castSucc :=
      (activeEdges_castSucc W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
    have hltR := W.pass_above_end k e' he'p e he
    rw [hbel] at hltR; simp only [Bool.false_eq_true, ↓reduceIte] at hltR
    exact Finset.mem_filter.mpr ⟨he'act, (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mpr hltR⟩
  have hsub2 : (activeEdges E k.castSucc).filter (fun e' => W.posL k.castSucc e' < W.posL k.castSucc e) ⊂
      Pbelow ∪ endingEdges E k := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro e' he'
      have ⟨he'act, hltL⟩ := Finset.mem_filter.mp he'
      have hltR := (W.posL_lt_iff_posR_lt_of_zero h0 k.castSucc he'act heL).mp hltL
      rw [activeEdges_castSucc W.edge_lt k, Finset.mem_union] at he'act
      rcases he'act with he'p | he'end
      · cases hab : W.above k e'
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he'p, hab⟩)
        · exfalso
          have hgt := W.pass_above_end k e' he'p e he
          rw [hab] at hgt; simp only [↓reduceIte] at hgt
          linarith
      · exact Finset.mem_union_right _ he'end
    · intro hEq
      have hmem : e ∈ (activeEdges E k.castSucc).filter (fun e' => W.posL k.castSucc e' < W.posL k.castSucc e) :=
        hEq ▸ Finset.mem_union_right _ he
      exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  have hd : Disjoint Pbelow (endingEdges E k) :=
    Disjoint.mono_left (Finset.filter_subset _ _) (disjoint_passing_ending E k)
  constructor
  · exact Finset.card_le_card hsub1
  · have hlt := Finset.card_lt_card hsub2
    rw [Finset.card_union_of_disjoint hd] at hlt
    exact hlt

lemma SlabWiring.rankL_starting_range {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (k : Fin n)
    {e : Fin n × Fin n} (he : e ∈ startingEdges E k) :
    W.belowCount k ≤ W.rankL k.succ e ∧ W.rankL k.succ e < W.belowCount k + (startingEdges E k).card := by
  let Pbelow := (passingEdges E k).filter (fun e' => W.above k e' = false)
  have hsub1 : Pbelow ⊆ (activeEdges E k.succ).filter (fun e' => W.posL k.succ e' < W.posL k.succ e) := by
    intro e' he'
    have ⟨he'p, hbel⟩ := Finset.mem_filter.mp he'
    have he'act : e' ∈ activeEdges E k.succ :=
      (activeEdges_succ W.edge_lt k).symm ▸ Finset.mem_union_left _ he'p
    have hlt := W.pass_above_start k e' he'p e he
    rw [hbel] at hlt; simp only [Bool.false_eq_true, ↓reduceIte] at hlt
    exact Finset.mem_filter.mpr ⟨he'act, hlt⟩
  have hsub2 : (activeEdges E k.succ).filter (fun e' => W.posL k.succ e' < W.posL k.succ e) ⊂
      Pbelow ∪ startingEdges E k := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro e' he'
      have ⟨he'act, hlt⟩ := Finset.mem_filter.mp he'
      rw [activeEdges_succ W.edge_lt k, Finset.mem_union] at he'act
      rcases he'act with he'p | he'st
      · cases hab : W.above k e'
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he'p, hab⟩)
        · exfalso
          have hgt := W.pass_above_start k e' he'p e he
          rw [hab] at hgt; simp only [↓reduceIte] at hgt
          linarith
      · exact Finset.mem_union_right _ he'st
    · intro hEq
      have hmem : e ∈ (activeEdges E k.succ).filter (fun e' => W.posL k.succ e' < W.posL k.succ e) :=
        hEq ▸ Finset.mem_union_right _ he
      exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  have hd : Disjoint Pbelow (startingEdges E k) :=
    Disjoint.mono_left (Finset.filter_subset _ _) (disjoint_passing_starting E k)
  constructor
  · exact Finset.card_le_card hsub1
  · have hlt := Finset.card_lt_card hsub2
    rw [Finset.card_union_of_disjoint hd] at hlt
    exact hlt

/-- **Topology-Free Planar Edge Bound (`|E| ≤ 3 n`):**
Any zero-crossing `SlabWiring` of a simple graph `E` on `Fin n` has at most `3 * n` edges. -/
theorem slabWiring_zero_crossings_edge_le {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (h0 : W.crossings = 0) :
    E.card ≤ 3 * n := by
  classical
  -- Vertices of the finite slab-gap graph H: pairs (s, r) with s : Fin (n+1) and r : Fin (|A_s| + 1).
  let Gap := Σ s : Fin (n + 1), Fin ((activeEdges E s).card + 1)
  have hcard_Gap : Fintype.card Gap = (n + 1) + ∑ s : Fin (n + 1), (activeEdges E s).card := by
    simp only [Gap, Fintype.card_sigma, Fintype.card_fin, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, add_comm]
  -- Helper: activeEdges card decomposition at k.castSucc and k.succ.
  have hcardL : ∀ k : Fin n, (activeEdges E k.castSucc).card =
      W.belowCount k + (endingEdges E k).card + W.aboveCount k := by
    intro k
    rw [activeEdges_castSucc W.edge_lt k, Finset.card_union_of_disjoint (disjoint_passing_ending E k),
      ← W.belowCount_add_aboveCount k]
    omega
  have hcardR : ∀ k : Fin n, (activeEdges E k.succ).card =
      W.belowCount k + (startingEdges E k).card + W.aboveCount k := by
    intro k
    rw [activeEdges_succ W.edge_lt k, Finset.card_union_of_disjoint (disjoint_passing_starting E k),
      ← W.belowCount_add_aboveCount k]
    omega
  -- Directed step relation across vertex k from slab k.castSucc to slab k.succ:
  let stepRel : Gap → Gap → Prop := fun x y =>
    ∃ (k : Fin n), x.1 = k.castSucc ∧ y.1 = k.succ ∧ (
      (x.2.val ≤ W.belowCount k ∧ y.2.val = x.2.val) ∨
      (x.2.val = W.belowCount k + (endingEdges E k).card ∧ y.2.val = W.belowCount k + (startingEdges E k).card) ∨
      (∃ s : ℕ, s < W.aboveCount k ∧
        x.2.val = W.belowCount k + (endingEdges E k).card + 1 + s ∧
        y.2.val = W.belowCount k + (startingEdges E k).card + 1 + s))
  let H : SimpleGraph Gap :=
    { Adj := fun x y => stepRel x y ∨ stepRel y x
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun x h => by
        rcases h with ⟨k, hx, hy, _⟩ | ⟨k, hx, hy, _⟩
        all_goals
          have := hx.symm.trans hy
          have hval := congrArg Fin.val this
          simp at hval⟩ }
  have gap_ext : ∀ {s₁ s₂ : Fin (n + 1)} {r₁ : Fin ((activeEdges E s₁).card + 1)}
      {r₂ : Fin ((activeEdges E s₂).card + 1)},
      s₁ = s₂ → r₁.val = r₂.val → (⟨s₁, r₁⟩ : Gap) = ⟨s₂, r₂⟩ := by
    intro s₁ s₂ r₁ r₂ hs hr
    cases hs
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hr))
  -- Step 1: Bound |E(H)| ≤ 2 * n + ∑ k, |P_k|.
  have hEdgeH : H.edgeFinset.card ≤ 2 * n + ∑ k : Fin n, (passingEdges E k).card := by
    let mkEdge (k : Fin n) (rl rr : ℕ) (hl : rl < (activeEdges E k.castSucc).card + 1)
        (hr : rr < (activeEdges E k.succ).card + 1) : Sym2 Gap :=
      s(⟨k.castSucc, ⟨rl, hl⟩⟩, ⟨k.succ, ⟨rr, hr⟩⟩)
    let edgesAt (k : Fin n) : Finset (Sym2 Gap) :=
      ((Finset.range (W.belowCount k + 1)).attach.image fun ⟨r, hr⟩ =>
        mkEdge k r r (by have := hcardL k; have := Finset.mem_range.mp hr; omega)
                     (by have := hcardR k; have := Finset.mem_range.mp hr; omega)) ∪
      {mkEdge k (W.belowCount k + (endingEdges E k).card) (W.belowCount k + (startingEdges E k).card)
        (by have := hcardL k; omega) (by have := hcardR k; omega)} ∪
      ((Finset.range (W.aboveCount k)).attach.image fun ⟨s, hs⟩ =>
        mkEdge k (W.belowCount k + (endingEdges E k).card + 1 + s)
                 (W.belowCount k + (startingEdges E k).card + 1 + s)
          (by have := hcardL k; have := Finset.mem_range.mp hs; omega)
          (by have := hcardR k; have := Finset.mem_range.mp hs; omega))
    have hsub : H.edgeFinset ⊆ (Finset.univ : Finset (Fin n)).biUnion edgesAt := by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : H.Adj x y := SimpleGraph.mem_edgeFinset.mp he
        have hstep : ∀ a b : Gap, stepRel a b → s(a, b) ∈ (Finset.univ : Finset (Fin n)).biUnion edgesAt := by
          intro a b ⟨k, ha1, hb1, hcases⟩
          refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩
          rcases a with ⟨sa, ra⟩; rcases b with ⟨sb, rb⟩
          dsimp only at ha1 hb1 hcases
          subst ha1; subst hb1
          rcases hcases with ⟨hrle, hreq⟩ | ⟨hx, hy⟩ | ⟨s, hs, hx, hy⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            refine Finset.mem_image.mpr ⟨⟨ra.val, Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _, ?_⟩
            dsimp only [mkEdge]
            exact congrArg₂ (fun p q => s(p, q)) (gap_ext rfl rfl) (gap_ext rfl hreq.symm)
          · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            rw [Finset.mem_singleton]
            dsimp only [mkEdge]
            exact congrArg₂ (fun p q => s(p, q)) (gap_ext rfl hx) (gap_ext rfl hy)
          · refine Finset.mem_union_right _ ?_
            refine Finset.mem_image.mpr ⟨⟨s, Finset.mem_range.mpr hs⟩, Finset.mem_attach _ _, ?_⟩
            dsimp only [mkEdge]
            exact congrArg₂ (fun p q => s(p, q)) (gap_ext rfl hx.symm) (gap_ext rfl hy.symm)
        rcases hadj with h | h
        · exact hstep x y h
        · rw [Sym2.eq_swap]; exact hstep y x h
    have hcardAt : ∀ k : Fin n, (edgesAt k).card ≤ (passingEdges E k).card + 2 := by
      intro k
      dsimp only [edgesAt]
      have h1 : (((Finset.range (W.belowCount k + 1)).attach.image fun ⟨r, hr⟩ =>
        mkEdge k r r (by have := hcardL k; have := Finset.mem_range.mp hr; omega)
                     (by have := hcardR k; have := Finset.mem_range.mp hr; omega))).card ≤ W.belowCount k + 1 :=
        le_trans Finset.card_image_le (le_of_eq (by rw [Finset.card_attach, Finset.card_range]))
      have h2 : ({mkEdge k (W.belowCount k + (endingEdges E k).card) (W.belowCount k + (startingEdges E k).card)
        (by have := hcardL k; omega) (by have := hcardR k; omega)} : Finset (Sym2 Gap)).card = 1 :=
        Finset.card_singleton _
      have h3 : (((Finset.range (W.aboveCount k)).attach.image fun ⟨s, hs⟩ =>
        mkEdge k (W.belowCount k + (endingEdges E k).card + 1 + s)
                 (W.belowCount k + (startingEdges E k).card + 1 + s)
          (by have := hcardL k; have := Finset.mem_range.mp hs; omega)
          (by have := hcardR k; have := Finset.mem_range.mp hs; omega))).card ≤ W.aboveCount k :=
        le_trans Finset.card_image_le (le_of_eq (by rw [Finset.card_attach, Finset.card_range]))
      have hu1 := Finset.card_union_le
        (((Finset.range (W.belowCount k + 1)).attach.image fun ⟨r, hr⟩ =>
          mkEdge k r r (by have := hcardL k; have := Finset.mem_range.mp hr; omega)
                       (by have := hcardR k; have := Finset.mem_range.mp hr; omega)) ∪
        {mkEdge k (W.belowCount k + (endingEdges E k).card) (W.belowCount k + (startingEdges E k).card)
          (by have := hcardL k; omega) (by have := hcardR k; omega)})
        ((Finset.range (W.aboveCount k)).attach.image fun ⟨s, hs⟩ =>
          mkEdge k (W.belowCount k + (endingEdges E k).card + 1 + s)
                   (W.belowCount k + (startingEdges E k).card + 1 + s)
            (by have := hcardL k; have := Finset.mem_range.mp hs; omega)
            (by have := hcardR k; have := Finset.mem_range.mp hs; omega))
      have hu2 := Finset.card_union_le
        ((Finset.range (W.belowCount k + 1)).attach.image fun ⟨r, hr⟩ =>
          mkEdge k r r (by have := hcardL k; have := Finset.mem_range.mp hr; omega)
                       (by have := hcardR k; have := Finset.mem_range.mp hr; omega))
        {mkEdge k (W.belowCount k + (endingEdges E k).card) (W.belowCount k + (startingEdges E k).card)
          (by have := hcardL k; omega) (by have := hcardR k; omega)}
      have hp := W.belowCount_add_aboveCount k
      calc _ ≤ _ := hu1
        _ ≤ _ := Nat.add_le_add_right hu2 _
        _ ≤ (W.belowCount k + 1 + 1) + W.aboveCount k := Nat.add_le_add (Nat.add_le_add h1 (le_of_eq h2)) h3
        _ = (passingEdges E k).card + 2 := by omega
    calc H.edgeFinset.card
        ≤ ((Finset.univ : Finset (Fin n)).biUnion edgesAt).card := Finset.card_le_card hsub
      _ ≤ ∑ k : Fin n, (edgesAt k).card := Finset.card_biUnion_le
      _ ≤ ∑ k : Fin n, ((passingEdges E k).card + 2) := Finset.sum_le_sum fun k _ => hcardAt k
      _ = 2 * n + ∑ k : Fin n, (passingEdges E k).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        omega
  -- Step 2: Combine |V(H)| ≤ c(H) + |E(H)| with |V(H)| = n + 1 + |E| + ∑ |P_k| to get |E| + 1 ≤ c(H) + n!
  have hcomp_lb : E.card + 1 ≤ Fintype.card H.ConnectedComponent + n := by
    have h1 : Fintype.card Gap ≤ Fintype.card H.ConnectedComponent + H.edgeFinset.card := by
      convert simpleGraph_card_le_components_add_edges H
    rw [hcard_Gap, sum_activeEdges_eq_edges_add_sum_passing W.edge_lt] at h1
    omega
  -- Step 3: Outer component contains ALL bottom gaps (s, 0) for every s : Fin (n + 1).
  let g0 : Gap := ⟨0, ⟨0, by simp⟩⟩
  let cOut : H.ConnectedComponent := H.connectedComponentMk g0
  have hbottom_out : ∀ s : Fin (n + 1),
      H.connectedComponentMk ⟨s, ⟨0, Nat.zero_lt_succ _⟩⟩ = cOut := by
    intro ⟨m, hm⟩
    induction m with
    | zero => rfl
    | succ m ih =>
      let k : Fin n := ⟨m, by omega⟩
      have hadj : H.Adj ⟨k.castSucc, ⟨0, Nat.zero_lt_succ _⟩⟩ ⟨k.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ := by
        left
        refine ⟨k, rfl, rfl, Or.inl ⟨Nat.zero_le _, rfl⟩⟩
      exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans (ih (by omega))
  -- Step 4: Every edge-side (e, top : Bool) has a well-defined component constant along all slabs s ∈ [e.1+1, e.2]!
  have hedge_side_const : ∀ (e : Fin n × Fin n) (he : e ∈ E) (top : Bool)
      (k : Fin n) (hk1 : e.1.val < k.val) (hk2 : k.val < e.2.val),
      let rL := W.rankL k.castSucc e + (if top then 1 else 0)
      let rR := W.rankL k.succ e + (if top then 1 else 0)
      have hL : rL < (activeEdges E k.castSucc).card + 1 := by
        have := W.rankL_lt k.castSucc (Finset.mem_filter.mpr ⟨he, hk1, le_of_lt hk2⟩)
        cases top <;> simp [rL] <;> omega
      have hR : rR < (activeEdges E k.succ).card + 1 := by
        have := W.rankL_lt k.succ (Finset.mem_filter.mpr ⟨he, by simp; omega, by simp; omega⟩)
        cases top <;> simp [rR] <;> omega
      H.Adj ⟨k.castSucc, ⟨rL, hL⟩⟩ ⟨k.succ, ⟨rR, hR⟩⟩ := by
    intro e he top k hk1 hk2 rL rR hL hR
    have heP : e ∈ passingEdges E k := Finset.mem_filter.mpr ⟨he, hk1, hk2⟩
    left
    refine ⟨k, rfl, rfl, ?_⟩
    cases hab : W.above k e
    · obtain ⟨hlt, heq⟩ := W.rankL_pass_below_eq h0 k heP hab
      left
      cases top
      · exact ⟨by simp [rL]; omega, by simp [rL, rR, heq]⟩
      · exact ⟨by simp [rL]; omega, by simp [rL, rR, heq]⟩
    · obtain ⟨s, hs, hrankL, hrankR⟩ := W.rankL_pass_above_eq h0 k heP hab
      cases top
      · cases s with
        | zero =>
          right; left
          exact ⟨by simp [rL, hrankL], by simp [rR, hrankR]⟩
        | succ s' =>
          right; right
          exact ⟨s', by omega, by simp [rL, hrankL]; omega, by simp [rR, hrankR]; omega⟩
      · right; right
        exact ⟨s, hs, by simp [rL, hrankL]; omega, by simp [rR, hrankR]; omega⟩
  -- Define sideComp (e, top) using the FIRST active slab s = e.1.succ!
  let sideComp : (Fin n × Fin n) × Bool → H.ConnectedComponent := fun p =>
    if h : p.1 ∈ E then
      let s0 : Fin (n + 1) := p.1.1.succ
      have hs0 : p.1 ∈ activeEdges E s0 :=
        Finset.mem_filter.mpr ⟨h, by simp [s0], by have := W.edge_lt p.1 h; simp [s0]; omega⟩
      let r := W.rankL s0 p.1 + (if p.2 then 1 else 0)
      have hr : r < (activeEdges E s0).card + 1 := by
        have := W.rankL_lt s0 hs0; cases hb : p.2 <;> simp [r, hb] <;> omega
      H.connectedComponentMk ⟨s0, ⟨r, hr⟩⟩
    else cOut
  -- Show sideComp agrees with the gap at ANY active slab s of e!
  have hsideComp_eq : ∀ (e : Fin n × Fin n) (he : e ∈ E) (top : Bool)
      (s : Fin (n + 1)) (hs : e ∈ activeEdges E s),
      have hr : W.rankL s e + (if top then 1 else 0) < (activeEdges E s).card + 1 := by
        have := W.rankL_lt s hs; cases top <;> simp <;> omega
      sideComp (e, top) = H.connectedComponentMk ⟨s, ⟨W.rankL s e + (if top then 1 else 0), hr⟩⟩ := by
    intro e he top ⟨m, hm⟩ hs hr
    simp only [activeEdges, Finset.mem_filter] at hs
    have h1 : e.1.val < m := hs.2.1
    have h2 : m ≤ e.2.val := hs.2.2
    suffices hstep : ∀ d : ℕ, ∀ (hd : e.1.val + 1 + d ≤ e.2.val),
        let s' : Fin (n + 1) := ⟨e.1.val + 1 + d, by have := e.2.isLt; omega⟩
        have hs' : e ∈ activeEdges E s' := Finset.mem_filter.mpr ⟨he, by simp [s']; omega, by simp [s']; omega⟩
        have hr' : W.rankL s' e + (if top then 1 else 0) < (activeEdges E s').card + 1 := by
          have := W.rankL_lt s' hs'; cases top <;> simp <;> omega
        sideComp (e, top) = H.connectedComponentMk ⟨s', ⟨W.rankL s' e + (if top then 1 else 0), hr'⟩⟩ by
      have hd : e.1.val + 1 + (m - (e.1.val + 1)) ≤ e.2.val := by omega
      have hres := hstep (m - (e.1.val + 1)) hd
      have hseq : (⟨e.1.val + 1 + (m - (e.1.val + 1)), by have := e.2.isLt; omega⟩ : Fin (n + 1)) = ⟨m, hm⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hres]
      exact congrArg H.connectedComponentMk (gap_ext hseq (by dsimp only; rw [hseq]))
    intro d
    induction d with
    | zero =>
      intro _
      simp only [sideComp, dif_pos he]
      have hseq : (e.1.succ : Fin (n + 1)) = ⟨e.1.val + 1 + 0, by have := e.2.isLt; omega⟩ :=
        Fin.ext (by simp)
      exact congrArg H.connectedComponentMk (gap_ext hseq (by dsimp only; rw [hseq]))
    | succ d ih =>
      intro hd
      let k : Fin n := ⟨e.1.val + 1 + d, by have := e.2.isLt; omega⟩
      have hih := ih (by omega)
      have hadj := hedge_side_const e he top k (by simp [k]; omega) (by simp [k]; omega)
      have hcomp := SimpleGraph.ConnectedComponent.sound hadj.reachable
      have hcast : (⟨e.1.val + 1 + d, by have := e.2.isLt; omega⟩ : Fin (n + 1)) = k.castSucc :=
        Fin.ext rfl
      have hsucc : (⟨e.1.val + 1 + (d + 1), by have := e.2.isLt; omega⟩ : Fin (n + 1)) = k.succ :=
        Fin.ext (by simp [k]; omega)
      rw [hih]
      exact (congrArg H.connectedComponentMk (gap_ext hcast (by dsimp only; rw [hcast]))).trans
        (hcomp.trans (congrArg H.connectedComponentMk (gap_ext hsucc.symm (by dsimp only; rw [hsucc]))))
  -- Step 5: Every bounded component c ≠ cOut has at least 3 edge-sides (e, top) ∈ E × Bool with sideComp = c!
  let allSides : Finset ((Fin n × Fin n) × Bool) := E ×ˢ (Finset.univ : Finset Bool)
  have hbounded_ge3 : ∀ c : H.ConnectedComponent, c ≠ cOut →
      3 ≤ (allSides.filter (fun p => sideComp p = c)).card := by
    intro c hc_out
    let gapsInC : Finset Gap := Finset.univ.filter (fun g => H.connectedComponentMk g = c)
    have hne : gapsInC.Nonempty := by
      rcases Quot.exists_rep c with ⟨g, rfl⟩
      exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    -- Minimum slab gap in c:
    obtain ⟨⟨sMin, rMin⟩, hgMin_mem, hgMin_le⟩ := gapsInC.exists_min_image (fun g : Gap => g.1.val) hne
    have hgMin_c : H.connectedComponentMk ⟨sMin, rMin⟩ = c := (Finset.mem_filter.mp hgMin_mem).2
    -- Maximum slab gap in c:
    obtain ⟨⟨sMax, rMax⟩, hgMax_mem, hgMax_ge⟩ := gapsInC.exists_max_image (fun g : Gap => g.1.val) hne
    have hgMax_c : H.connectedComponentMk ⟨sMax, rMax⟩ = c := (Finset.mem_filter.mp hgMax_mem).2
    -- sMin cannot be 0 (its only gap (0, 0) is in cOut).
    have hMin_pos : 0 < sMin.val := by
      by_contra h0v
      have h0eq : sMin = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      subst h0eq
      have hr0 : rMin.val = 0 := by
        have hlt := rMin.isLt
        have hcz : (activeEdges E 0).card = 0 := by rw [activeEdges_zero]; rfl
        omega
      have hgEq : (⟨0, rMin⟩ : Gap) = ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩ := gap_ext rfl hr0
      rw [hgEq] at hgMin_c
      exact hc_out (hgMin_c.symm.trans (hbottom_out 0))
    -- sMax cannot be n (its only gap (n, 0) is in cOut).
    have hMax_lt : sMax.val < n := by
      by_contra hnv
      have hneq : sMax = Fin.last n := Fin.ext (by have := sMax.isLt; simp; omega)
      subst hneq
      have hr0 : rMax.val = 0 := by
        have hlt := rMax.isLt
        have hcz : (activeEdges E (Fin.last n)).card = 0 := by rw [activeEdges_last]; rfl
        omega
      have hgEq : (⟨Fin.last n, rMax⟩ : Gap) = ⟨Fin.last n, ⟨0, Nat.zero_lt_succ _⟩⟩ := gap_ext rfl hr0
      rw [hgEq] at hgMax_c
      exact hc_out (hgMax_c.symm.trans (hbottom_out (Fin.last n)))
    -- Analyze ⟨sMin, rMin⟩ on slab kMin.succ: it has NO H-neighbor on slab kMin.castSucc!
    let kMin : Fin n := ⟨sMin.val - 1, by have := sMin.isLt; omega⟩
    have hgMin_s : sMin = kMin.succ := Fin.ext (by simp [kMin]; omega)
    have hMin_range : W.belowCount kMin < rMin.val ∧ rMin.val < W.belowCount kMin + (startingEdges E kMin).card := by
      have hno_left : ∀ rl : Fin ((activeEdges E kMin.castSucc).card + 1),
          ¬ stepRel ⟨kMin.castSucc, rl⟩ ⟨sMin, rMin⟩ := by
        intro rl hstep
        have hadj : H.Adj ⟨kMin.castSucc, rl⟩ ⟨sMin, rMin⟩ := Or.inl hstep
        have hmem : (⟨kMin.castSucc, rl⟩ : Gap) ∈ gapsInC :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (SimpleGraph.ConnectedComponent.sound hadj.reachable).trans hgMin_c⟩
        have hle := hgMin_le ⟨kMin.castSucc, rl⟩ hmem
        simp [kMin] at hle; omega
      constructor
      · by_contra hle; push Not at hle
        have hrl : rMin.val < (activeEdges E kMin.castSucc).card + 1 := by
          have := hcardL kMin; omega
        exact hno_left ⟨rMin.val, hrl⟩ ⟨kMin, rfl, hgMin_s, Or.inl ⟨hle, rfl⟩⟩
      · by_contra hge; push Not at hge
        rcases eq_or_lt_of_le hge with heq | hgt
        · have hrl : W.belowCount kMin + (endingEdges E kMin).card < (activeEdges E kMin.castSucc).card + 1 := by
            have := hcardL kMin; omega
          exact hno_left ⟨W.belowCount kMin + (endingEdges E kMin).card, hrl⟩
            ⟨kMin, rfl, hgMin_s, Or.inr (Or.inl ⟨rfl, heq.symm⟩)⟩
        · let s := rMin.val - (W.belowCount kMin + (startingEdges E kMin).card + 1)
          have hs : s < W.aboveCount kMin := by
            have h1 := rMin.isLt
            have hceq : (activeEdges E sMin).card = (activeEdges E kMin.succ).card :=
              congrArg (fun x => (activeEdges E x).card) hgMin_s
            have := hcardR kMin; omega
          have hrl : W.belowCount kMin + (endingEdges E kMin).card + 1 + s < (activeEdges E kMin.castSucc).card + 1 := by
            have := hcardL kMin; omega
          exact hno_left ⟨W.belowCount kMin + (endingEdges E kMin).card + 1 + s, hrl⟩
            ⟨kMin, rfl, hgMin_s, Or.inr (Or.inr ⟨s, hs, rfl, by dsimp; omega⟩)⟩
    have hr1_lt : rMin.val < (activeEdges E kMin.succ).card := by
      have := hcardR kMin; omega
    obtain ⟨eBot1, heBot1_act, heBot1_rk⟩ := W.exists_edge_of_rankL kMin.succ (by omega : rMin.val - 1 < (activeEdges E kMin.succ).card)
    obtain ⟨eTop1, heTop1_act, heTop1_rk⟩ := W.exists_edge_of_rankL kMin.succ hr1_lt
    have heBot1_E : eBot1 ∈ E := (Finset.mem_filter.mp heBot1_act).1
    have heTop1_E : eTop1 ∈ E := (Finset.mem_filter.mp heTop1_act).1
    have hne1 : eBot1 ≠ eTop1 := fun heq => by rw [heq] at heBot1_rk; omega
    have hstart1 : ∀ e ∈ activeEdges E kMin.succ,
        W.belowCount kMin ≤ W.rankL kMin.succ e →
        W.rankL kMin.succ e < W.belowCount kMin + (startingEdges E kMin).card →
        e.1 = kMin := by
      intro e heact hlo hhi
      rw [activeEdges_succ W.edge_lt kMin, Finset.mem_union] at heact
      rcases heact with hep | hest
      · cases hab : W.above kMin e
        · obtain ⟨hlt, heq⟩ := W.rankL_pass_below_eq h0 kMin hep hab; omega
        · obtain ⟨s, _, _, hsr⟩ := W.rankL_pass_above_eq h0 kMin hep hab; omega
      · exact (Finset.mem_filter.mp hest).2
    have heBot1_fst : eBot1.1 = kMin := hstart1 eBot1 heBot1_act (by omega) (by omega)
    have heTop1_fst : eTop1.1 = kMin := hstart1 eTop1 heTop1_act (by omega) (by omega)
    have hs1 : sideComp (eBot1, true) = c := by
      rw [hsideComp_eq eBot1 heBot1_E true kMin.succ heBot1_act, ← hgMin_c]
      exact congrArg H.connectedComponentMk (gap_ext hgMin_s.symm (by simp [heBot1_rk]; omega))
    have hs2 : sideComp (eTop1, false) = c := by
      rw [hsideComp_eq eTop1 heTop1_E false kMin.succ heTop1_act, ← hgMin_c]
      exact congrArg H.connectedComponentMk (gap_ext hgMin_s.symm (by simp [heTop1_rk]))
    -- Symmetrically analyze ⟨sMax, rMax⟩ on slab kMax.castSucc: it has NO H-neighbor on slab kMax.succ!
    let kMax : Fin n := ⟨sMax.val, hMax_lt⟩
    have hgMax_s : sMax = kMax.castSucc := Fin.ext rfl
    have hMax_range : W.belowCount kMax < rMax.val ∧ rMax.val < W.belowCount kMax + (endingEdges E kMax).card := by
      have hno_right : ∀ rr : Fin ((activeEdges E kMax.succ).card + 1),
          ¬ stepRel ⟨sMax, rMax⟩ ⟨kMax.succ, rr⟩ := by
        intro rr hstep
        have hadj : H.Adj ⟨sMax, rMax⟩ ⟨kMax.succ, rr⟩ := Or.inl hstep
        have hmem : (⟨kMax.succ, rr⟩ : Gap) ∈ gapsInC :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans hgMax_c⟩
        have hge := hgMax_ge ⟨kMax.succ, rr⟩ hmem
        simp [kMax] at hge
      constructor
      · by_contra hle; push Not at hle
        have hrr : rMax.val < (activeEdges E kMax.succ).card + 1 := by
          have := hcardR kMax; omega
        exact hno_right ⟨rMax.val, hrr⟩ ⟨kMax, hgMax_s, rfl, Or.inl ⟨hle, rfl⟩⟩
      · by_contra hge; push Not at hge
        rcases eq_or_lt_of_le hge with heq | hgt
        · have hrr : W.belowCount kMax + (startingEdges E kMax).card < (activeEdges E kMax.succ).card + 1 := by
            have := hcardR kMax; omega
          exact hno_right ⟨W.belowCount kMax + (startingEdges E kMax).card, hrr⟩
            ⟨kMax, hgMax_s, rfl, Or.inr (Or.inl ⟨heq.symm, rfl⟩)⟩
        · let s := rMax.val - (W.belowCount kMax + (endingEdges E kMax).card + 1)
          have hs : s < W.aboveCount kMax := by
            have h1 := rMax.isLt
            have hceq : (activeEdges E sMax).card = (activeEdges E kMax.castSucc).card :=
              congrArg (fun x => (activeEdges E x).card) hgMax_s
            have := hcardL kMax; omega
          have hrr : W.belowCount kMax + (startingEdges E kMax).card + 1 + s < (activeEdges E kMax.succ).card + 1 := by
            have := hcardR kMax; omega
          exact hno_right ⟨W.belowCount kMax + (startingEdges E kMax).card + 1 + s, hrr⟩
            ⟨kMax, hgMax_s, rfl, Or.inr (Or.inr ⟨s, hs, by dsimp; omega, rfl⟩)⟩
    have hr2_lt : rMax.val < (activeEdges E kMax.castSucc).card := by
      have := hcardL kMax; omega
    obtain ⟨eBot2, heBot2_act, heBot2_rk⟩ := W.exists_edge_of_rankL kMax.castSucc (by omega : rMax.val - 1 < (activeEdges E kMax.castSucc).card)
    obtain ⟨eTop2, heTop2_act, heTop2_rk⟩ := W.exists_edge_of_rankL kMax.castSucc hr2_lt
    have heBot2_E : eBot2 ∈ E := (Finset.mem_filter.mp heBot2_act).1
    have heTop2_E : eTop2 ∈ E := (Finset.mem_filter.mp heTop2_act).1
    have hend2 : ∀ e ∈ activeEdges E kMax.castSucc,
        W.belowCount kMax ≤ W.rankL kMax.castSucc e →
        W.rankL kMax.castSucc e < W.belowCount kMax + (endingEdges E kMax).card →
        e.2 = kMax := by
      intro e heact hlo hhi
      rw [activeEdges_castSucc W.edge_lt kMax, Finset.mem_union] at heact
      rcases heact with hep | heend
      · cases hab : W.above kMax e
        · obtain ⟨hlt, _⟩ := W.rankL_pass_below_eq h0 kMax hep hab; omega
        · obtain ⟨s, _, hsl, _⟩ := W.rankL_pass_above_eq h0 kMax hep hab; omega
      · exact (Finset.mem_filter.mp heend).2
    have heBot2_snd : eBot2.2 = kMax := hend2 eBot2 heBot2_act (by omega) (by omega)
    have heTop2_snd : eTop2.2 = kMax := hend2 eTop2 heTop2_act (by omega) (by omega)
    have hs3 : sideComp (eBot2, true) = c := by
      rw [hsideComp_eq eBot2 heBot2_E true kMax.castSucc heBot2_act, ← hgMax_c]
      exact congrArg H.connectedComponentMk (gap_ext hgMax_s.symm (by simp [heBot2_rk]; omega))
    have hs4 : sideComp (eTop2, false) = c := by
      rw [hsideComp_eq eTop2 heTop2_E false kMax.castSucc heTop2_act, ← hgMax_c]
      exact congrArg H.connectedComponentMk (gap_ext hgMax_s.symm (by simp [heTop2_rk]))
    -- Simple-graph contradiction: we cannot have both eBot2 = eBot1 AND eTop2 = eTop1!
    have hnotboth : ¬ (eBot2 = eBot1 ∧ eTop2 = eTop1) := by
      rintro ⟨h1, h2⟩
      apply hne1
      exact Prod.ext (heBot1_fst.trans heTop1_fst.symm)
        ((h1 ▸ heBot2_snd).trans (h2 ▸ heTop2_snd).symm)
    let target := allSides.filter (fun p => sideComp p = c)
    have hmem1 : (eBot1, true) ∈ target := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heBot1_E, Finset.mem_univ _⟩, hs1⟩
    have hmem2 : (eTop1, false) ∈ target := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heTop1_E, Finset.mem_univ _⟩, hs2⟩
    have hmem3 : (eBot2, true) ∈ target := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heBot2_E, Finset.mem_univ _⟩, hs3⟩
    have hmem4 : (eTop2, false) ∈ target := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heTop2_E, Finset.mem_univ _⟩, hs4⟩
    by_cases h1 : eBot2 ≠ eBot1
    · have hsub3 : ({(eBot1, true), (eTop1, false), (eBot2, true)} : Finset ((Fin n × Fin n) × Bool)) ⊆ target := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard3 : ({(eBot1, true), (eTop1, false), (eBot2, true)} : Finset ((Fin n × Fin n) × Bool)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp
        · simp [h1.symm]
      exact le_trans (le_of_eq hcard3.symm) (Finset.card_le_card hsub3)
    · push Not at h1
      have h2 : eTop2 ≠ eTop1 := fun h2 => hnotboth ⟨h1, h2⟩
      have hsub3 : ({(eBot1, true), (eTop1, false), (eTop2, false)} : Finset ((Fin n × Fin n) × Bool)) ⊆ target := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard3 : ({(eBot1, true), (eTop1, false), (eTop2, false)} : Finset ((Fin n × Fin n) × Bool)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [h2.symm]
        · simp
      exact le_trans (le_of_eq hcard3.symm) (Finset.card_le_card hsub3)
  -- Step 6: Double-count 3 * (c(H) - 1) ≤ 2 * |E|, then combine with |E| + 1 ≤ c(H) + n!
  have hdouble : 3 * (Fintype.card H.ConnectedComponent - 1) ≤ 2 * E.card := by
    let bounded := (Finset.univ : Finset H.ConnectedComponent).erase cOut
    have hcard_b : bounded.card = Fintype.card H.ConnectedComponent - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have hpart : ∑ c ∈ bounded, (allSides.filter (fun p => sideComp p = c)).card ≤ allSides.card := by
      rw [← Finset.card_biUnion]
      · refine Finset.card_le_card ?_
        intro p hp
        rcases Finset.mem_biUnion.mp hp with ⟨c, _, hpc⟩
        exact (Finset.mem_filter.mp hpc).1
      · intro c₁ _ c₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact hne ((Finset.mem_filter.mp hp1).2.symm.trans (Finset.mem_filter.mp hp2).2)
    have hsum_lb : 3 * bounded.card ≤ ∑ c ∈ bounded, (allSides.filter (fun p => sideComp p = c)).card := by
      calc 3 * bounded.card = ∑ _c ∈ bounded, 3 := by simp [mul_comm]
        _ ≤ ∑ c ∈ bounded, (allSides.filter (fun p => sideComp p = c)).card :=
          Finset.sum_le_sum fun c hc => hbounded_ge3 c (Finset.ne_of_mem_erase hc)
    have hall : allSides.card = 2 * E.card := by
      simp [allSides, Finset.card_product, mul_comm]
    omega
  have hc_pos : 1 ≤ Fintype.card H.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨cOut⟩
  omega

/-! ### 3C. Shared-Endpoint Uncrossing & Simple-Graph `SlabWiring` Crossing Lemma -/

/-- Pointwise transposition of a function `f` at two elements `e₁, e₂`. -/
def swapVal {α β : Type*} [DecidableEq α] (f : α → β) (e₁ e₂ : α) : α → β :=
  fun e => if e = e₁ then f e₂ else if e = e₂ then f e₁ else f e

lemma swapVal_self_left {α β : Type*} [DecidableEq α] (f : α → β) (e₁ e₂ : α) :
    swapVal f e₁ e₂ e₁ = f e₂ := by simp [swapVal]

lemma swapVal_self_right {α β : Type*} [DecidableEq α] (f : α → β) (e₁ e₂ : α) :
    swapVal f e₁ e₂ e₂ = f e₁ := by
  by_cases h : e₂ = e₁
  · subst h; simp [swapVal]
  · simp [swapVal, h]

lemma swapVal_other {α β : Type*} [DecidableEq α] (f : α → β) {e₁ e₂ e : α}
    (h1 : e ≠ e₁) (h2 : e ≠ e₂) : swapVal f e₁ e₂ e = f e := by
  simp [swapVal, h1, h2]

lemma swapVal_comm {α β : Type*} [DecidableEq α] (f : α → β) (e₁ e₂ : α) :
    swapVal f e₁ e₂ = swapVal f e₂ e₁ := by
  ext e
  by_cases h1 : e = e₁
  · subst h1; by_cases h12 : e = e₂ <;> simp [swapVal, h12]
  · by_cases h2 : e = e₂
    · subst h2; simp [swapVal, h1]
    · simp [swapVal, h1, h2]

lemma swapVal_injOn {α β : Type*} [DecidableEq α] {A : Finset α} {f : α → β}
    (hf : Set.InjOn f A) {e₁ e₂ : α} (h1 : e₁ ∈ A) (h2 : e₂ ∈ A) :
    Set.InjOn (swapVal f e₁ e₂) A := by
  by_cases h12 : e₁ = e₂
  · subst h12
    have heq : swapVal f e₁ e₁ = f := by ext x; by_cases hx : x = e₁ <;> simp [swapVal, hx]
    rw [heq]; exact hf
  · let τ : α → α := fun e => if e = e₁ then e₂ else if e = e₂ then e₁ else e
    have hτ_inv : ∀ e, τ (τ e) = e := by
      intro e
      by_cases h1e : e = e₁
      · subst h1e; simp [τ, Ne.symm h12]
      · by_cases h2e : e = e₂
        · subst h2e; simp [τ, Ne.symm h12]
        · simp [τ, h1e, h2e]
    have hτ_mem : ∀ e ∈ A, τ e ∈ A := by
      intro e he
      by_cases h1e : e = e₁
      · simp [τ, h1e, h2]
      · by_cases h2e : e = e₂
        · subst h2e; simp [τ, Ne.symm h12, h1]
        · simp [τ, h1e, h2e, he]
    have hfτ : ∀ e, swapVal f e₁ e₂ e = f (τ e) := by
      intro e
      by_cases h1e : e = e₁
      · simp [swapVal, τ, h1e]
      · by_cases h2e : e = e₂
        · subst h2e; simp [swapVal, τ, Ne.symm h12]
        · simp [swapVal, τ, h1e, h2e]
    intro a ha b hb hEq
    rw [hfτ a, hfτ b] at hEq
    have := hf (hτ_mem a ha) (hτ_mem b hb) hEq
    have := congrArg τ this
    rwa [hτ_inv, hτ_inv] at this

lemma invPairs_comm_card {α : Type*} (A : Finset α) (f g : α → ℝ) :
    (invPairs A f g).card = (invPairs A g f).card := by
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [invPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.2, hp.2.1⟩
  · intro p₁ _ p₂ _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [invPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.2, hp.2.1⟩

lemma invPairs_swap_both_card {α : Type*} [DecidableEq α] (A : Finset α) (f g : α → ℝ)
    {e₁ e₂ : α} (h1 : e₁ ∈ A) (h2 : e₂ ∈ A) :
    (invPairs A (swapVal f e₁ e₂) (swapVal g e₁ e₂)).card = (invPairs A f g).card := by
  by_cases h12 : e₁ = e₂
  · subst h12
    have hf : swapVal f e₁ e₁ = f := by ext x; by_cases hx : x = e₁ <;> simp [swapVal, hx]
    have hg : swapVal g e₁ e₁ = g := by ext x; by_cases hx : x = e₁ <;> simp [swapVal, hx]
    rw [hf, hg]
  · let τ : α → α := fun e => if e = e₁ then e₂ else if e = e₂ then e₁ else e
    have hτ_inv : ∀ e, τ (τ e) = e := by
      intro e
      by_cases h1e : e = e₁
      · subst h1e; simp [τ, Ne.symm h12]
      · by_cases h2e : e = e₂
        · subst h2e; simp [τ, Ne.symm h12]
        · simp [τ, h1e, h2e]
    have hτ_mem : ∀ e ∈ A, τ e ∈ A := by
      intro e he
      by_cases h1e : e = e₁
      · simp [τ, h1e, h2]
      · by_cases h2e : e = e₂
        · subst h2e; simp [τ, Ne.symm h12, h1]
        · simp [τ, h1e, h2e, he]
    have hfτ : ∀ e, swapVal f e₁ e₂ e = f (τ e) := by
      intro e
      by_cases h1e : e = e₁
      · simp [swapVal, τ, h1e]
      · by_cases h2e : e = e₂
        · subst h2e; simp [swapVal, τ, Ne.symm h12]
        · simp [swapVal, τ, h1e, h2e]
    have hgτ : ∀ e, swapVal g e₁ e₂ e = g (τ e) := by
      intro e
      by_cases h1e : e = e₁
      · simp [swapVal, τ, h1e]
      · by_cases h2e : e = e₂
        · subst h2e; simp [swapVal, τ, Ne.symm h12]
        · simp [swapVal, τ, h1e, h2e]
    refine Finset.card_bij (fun p _ => (τ p.1, τ p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [invPairs, Finset.mem_filter, Finset.mem_product, hfτ, hgτ] at hp ⊢
      exact ⟨⟨hτ_mem _ hp.1.1, hτ_mem _ hp.1.2⟩, hp.2.1, hp.2.2⟩
    · intro p₁ _ p₂ _ h
      have h1' := congrArg τ (congrArg Prod.fst h)
      have h2' := congrArg τ (congrArg Prod.snd h)
      rw [hτ_inv, hτ_inv] at h1' h2'
      exact Prod.ext h1' h2'
    · intro p hp
      refine ⟨(τ p.1, τ p.2), ?_, Prod.ext (hτ_inv p.1) (hτ_inv p.2)⟩
      simp only [invPairs, Finset.mem_filter, Finset.mem_product, hfτ, hgτ, hτ_inv] at hp ⊢
      exact ⟨⟨hτ_mem _ hp.1.1, hτ_mem _ hp.1.2⟩, hp.2.1, hp.2.2⟩

/-- Core 9-case swap inequality: uncrossing a single inverted pair `(e₁, e₂)` on the left
strictly reduces the total inversion count! -/
lemma invPairs_swap_left_lt {α : Type*} [DecidableEq α] (A : Finset α) (f g : α → ℝ)
    (hf : Set.InjOn f A) (hg : Set.InjOn g A)
    {e₁ e₂ : α} (h1 : e₁ ∈ A) (h2 : e₂ ∈ A) (hfl : f e₁ < f e₂) (hgr : g e₂ < g e₁) :
    (invPairs A (swapVal f e₁ e₂) g).card < (invPairs A f g).card := by
  have hne : e₁ ≠ e₂ := fun heq => lt_irrefl _ (heq ▸ hfl)
  let f' := swapVal f e₁ e₂
  let R := (A.erase e₁).erase e₂
  have hR_sub : R ⊆ A := fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hR_ne : ∀ x ∈ R, x ≠ e₁ ∧ x ≠ e₂ := fun x hx =>
    ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx), Finset.ne_of_mem_erase hx⟩
  -- For any height function h injective on A, invPairs A h g partitions into 3 disjoint parts:
  -- (1) inside {e₁, e₂}², (2) crossing {e₁, e₂} × R ∪ R × {e₁, e₂}, (3) inside R × R.
  let crossSet (h : α → ℝ) (x : α) : Finset (α × α) :=
    ({(e₁, x), (x, e₁), (e₂, x), (x, e₂)} : Finset (α × α)).filter (fun p => h p.1 < h p.2 ∧ g p.2 < g p.1)
  have hdecomp : ∀ (h : α → ℝ),
      (invPairs A h g).card =
        ((({(e₁, e₂), (e₂, e₁)} : Finset (α × α)).filter (fun p => h p.1 < h p.2 ∧ g p.2 < g p.1)).card) +
        (∑ x ∈ R, (crossSet h x).card) +
        (invPairs R h g).card := by
    intro h
    let S1 := ({(e₁, e₂), (e₂, e₁)} : Finset (α × α)).filter (fun p => h p.1 < h p.2 ∧ g p.2 < g p.1)
    let S2 := R.biUnion (crossSet h)
    let S3 := invPairs R h g
    have hEq : invPairs A h g = S1 ∪ S2 ∪ S3 := by
      ext ⟨a, b⟩
      simp only [invPairs, S1, S2, S3, crossSet, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨haA, hbA⟩, hlt, hgt⟩
        have hab : a ≠ b := fun heq => lt_irrefl _ (heq ▸ hlt)
        by_cases ha1 : a = e₁ <;> by_cases ha2 : a = e₂ <;>
          by_cases hb1 : b = e₁ <;> by_cases hb2 : b = e₂
        · exact absurd (ha1.symm.trans ha2) hne
        · exact absurd (ha1.symm.trans ha2) hne
        · exact absurd (ha1.symm.trans ha2) hne
        · exact absurd (ha1.symm.trans ha2) hne
        · exact absurd (hb1.symm.trans hb2) hne
        · exact absurd (ha1.trans hb1.symm) hab
        · left; left; exact ⟨Or.inl (Prod.ext ha1 hb2), hlt, hgt⟩
        · left; right; refine ⟨b, Finset.mem_erase.mpr ⟨hb2, Finset.mem_erase.mpr ⟨hb1, hbA⟩⟩, ?_, hlt, hgt⟩
          exact Or.inl (Prod.ext ha1 rfl)
        · exact absurd (hb1.symm.trans hb2) hne
        · left; left; exact ⟨Or.inr (Prod.ext ha2 hb1), hlt, hgt⟩
        · exact absurd (ha2.trans hb2.symm) hab
        · left; right; refine ⟨b, Finset.mem_erase.mpr ⟨hb2, Finset.mem_erase.mpr ⟨hb1, hbA⟩⟩, ?_, hlt, hgt⟩
          exact Or.inr (Or.inr (Or.inl (Prod.ext ha2 rfl)))
        · exact absurd (hb1.symm.trans hb2) hne
        · left; right; refine ⟨a, Finset.mem_erase.mpr ⟨ha2, Finset.mem_erase.mpr ⟨ha1, haA⟩⟩, ?_, hlt, hgt⟩
          exact Or.inr (Or.inl (Prod.ext rfl hb1))
        · left; right; refine ⟨a, Finset.mem_erase.mpr ⟨ha2, Finset.mem_erase.mpr ⟨ha1, haA⟩⟩, ?_, hlt, hgt⟩
          exact Or.inr (Or.inr (Or.inr (Prod.ext rfl hb2)))
        · right; exact ⟨⟨Finset.mem_erase.mpr ⟨ha2, Finset.mem_erase.mpr ⟨ha1, haA⟩⟩,
            Finset.mem_erase.mpr ⟨hb2, Finset.mem_erase.mpr ⟨hb1, hbA⟩⟩⟩, hlt, hgt⟩
      · rintro ((⟨h12, hlt, hgt⟩ | ⟨x, hxR, h4, hlt, hgt⟩) | ⟨⟨haR, hbR⟩, hlt, hgt⟩)
        · rcases h12 with hEq' | hEq'
          · rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩; exact ⟨⟨h1, h2⟩, hlt, hgt⟩
          · rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩; exact ⟨⟨h2, h1⟩, hlt, hgt⟩
        · rcases h4 with hEq' | hEq' | hEq' | hEq'
          · rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩; exact ⟨⟨h1, hR_sub hxR⟩, hlt, hgt⟩
          · rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩; exact ⟨⟨hR_sub hxR, h1⟩, hlt, hgt⟩
          · rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩; exact ⟨⟨h2, hR_sub hxR⟩, hlt, hgt⟩
          · rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩; exact ⟨⟨hR_sub hxR, h2⟩, hlt, hgt⟩
        · exact ⟨⟨hR_sub haR, hR_sub hbR⟩, hlt, hgt⟩
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro ⟨a, b⟩ h1m h2m
      have h1' := (Finset.mem_filter.mp h1m).1
      rcases Finset.mem_biUnion.mp h2m with ⟨x, hxR, hx⟩
      have hx' := (Finset.mem_filter.mp hx).1
      have ⟨hx1, hx2⟩ := hR_ne x hxR
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1' hx'
      rcases h1' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hx' with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;>
        first | exact hx1 h | exact hx2 h | exact hx1 h.symm | exact hx2 h.symm
    have hd123 : Disjoint (S1 ∪ S2) S3 := by
      rw [Finset.disjoint_left]
      intro ⟨a, b⟩ h12m h3m
      have ⟨haR, hbR⟩ := (Finset.mem_product.mp (Finset.mem_filter.mp h3m).1)
      have ⟨ha1, ha2⟩ := hR_ne a haR
      have ⟨hb1, hb2⟩ := hR_ne b hbR
      rcases Finset.mem_union.mp h12m with h1m | h2m
      · have h1' := (Finset.mem_filter.mp h1m).1
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1'
        rcases h1' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha1 rfl
        · exact ha2 rfl
      · rcases Finset.mem_biUnion.mp h2m with ⟨x, _, hx⟩
        have hx' := (Finset.mem_filter.mp hx).1
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hx'
        rcases hx' with ⟨rfl, _⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact ha1 rfl
        · exact hb1 rfl
        · exact ha2 rfl
        · exact hb2 rfl
    have hS2_card : S2.card = ∑ x ∈ R, (crossSet h x).card := by
      refine Finset.card_biUnion ?_
      intro x hxR y hyR hxy
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a, b⟩ hxm hym
      have hx' := (Finset.mem_filter.mp hxm).1
      have hy' := (Finset.mem_filter.mp hym).1
      have ⟨hx1, hx2⟩ := hR_ne x hxR
      have ⟨hy1, hy2⟩ := hR_ne y hyR
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hx' hy'
      rcases hx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hy' with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ <;>
        first | exact hxy hB | exact hxy hA | exact hxy hB.symm | exact hxy hA.symm |
                exact hx1 hB | exact hx2 hB | exact hx1 hA | exact hx2 hA
    rw [hEq, Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12, hS2_card]
  -- Compare each of the 3 parts between f' and f!
  -- Part 1: {e₁, e₂}² drops from 1 to 0!
  have hP1_f' : (({(e₁, e₂), (e₂, e₁)} : Finset (α × α)).filter (fun p => f' p.1 < f' p.2 ∧ g p.2 < g p.1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp only [f', swapVal_self_left, swapVal_self_right]; intro h; linarith
    · simp only [f', swapVal_self_left, swapVal_self_right]; intro h; linarith
  have hP1_f : 1 ≤ (({(e₁, e₂), (e₂, e₁)} : Finset (α × α)).filter (fun p => f p.1 < f p.2 ∧ g p.2 < g p.1)).card := by
    refine Finset.card_pos.mpr ⟨(e₁, e₂), Finset.mem_filter.mpr ⟨by simp, hfl, hgr⟩⟩
  -- Part 3: R × R is identical!
  have hP3 : invPairs R f' g = invPairs R f g := by
    ext ⟨a, b⟩
    simp only [invPairs, Finset.mem_filter, Finset.mem_product]
    constructor <;> rintro ⟨⟨haR, hbR⟩, hlt, hgt⟩
    · have ⟨ha1, ha2⟩ := hR_ne a haR; have ⟨hb1, hb2⟩ := hR_ne b hbR
      dsimp only [f'] at hlt
      rw [swapVal_other f ha1 ha2, swapVal_other f hb1 hb2] at hlt
      exact ⟨⟨haR, hbR⟩, hlt, hgt⟩
    · have ⟨ha1, ha2⟩ := hR_ne a haR; have ⟨hb1, hb2⟩ := hR_ne b hbR
      refine ⟨⟨haR, hbR⟩, ?_, hgt⟩
      dsimp only [f']
      rw [swapVal_other f ha1 ha2, swapVal_other f hb1 hb2]; exact hlt
  -- Part 2: For every x ∈ R, (crossSet f' x).card ≤ (crossSet f x).card!
  have hP2 : ∀ x ∈ R, (crossSet f' x).card ≤ (crossSet f x).card := by
    intro x hxR
    have hxA : x ∈ A := hR_sub hxR
    have ⟨hx1, hx2⟩ := hR_ne x hxR
    let ind (a b c d : ℝ) : ℕ := (if a < b ∧ d < c then 1 else 0) + (if b < a ∧ c < d then 1 else 0)
    have h4card : ∀ (h : α → ℝ), (crossSet h x).card =
        ind (h e₁) (h x) (g e₁) (g x) + ind (h e₂) (h x) (g e₂) (g x) := by
      intro h
      let p1 : α × α := (e₁, x)
      let p2 : α × α := (x, e₁)
      let p3 : α × α := (e₂, x)
      let p4 : α × α := (x, e₂)
      have h12 : p1 ≠ p2 := fun heq => hx1 (Prod.mk.inj heq).1.symm
      have h13 : p1 ≠ p3 := fun heq => hne (Prod.mk.inj heq).1
      have h14 : p1 ≠ p4 := fun heq => hx1 (Prod.mk.inj heq).1.symm
      have h23 : p2 ≠ p3 := fun heq => hx2 (Prod.mk.inj heq).1
      have h24 : p2 ≠ p4 := fun heq => hne (Prod.mk.inj heq).2
      have h34 : p3 ≠ p4 := fun heq => hx2 (Prod.mk.inj heq).1.symm
      unfold crossSet ind
      rw [Finset.card_filter]
      rw [Finset.sum_insert (by simp [p1, p2, p3, p4] at h12 h13 h14 ⊢; exact ⟨h12, h13, h14⟩),
          Finset.sum_insert (by simp [p2, p3, p4] at h23 h24 ⊢; exact ⟨h23, h24⟩),
          Finset.sum_insert (by simp [p3, p4] at h34 ⊢; exact h34),
          Finset.sum_singleton]
      dsimp only
      omega
    rw [h4card f', h4card f]
    simp only [f', swapVal_self_left, swapVal_self_right, swapVal_other f hx1 hx2, ind]
    have hf1x : f e₁ ≠ f x := fun h => hx1 (hf h1 hxA h).symm
    have hf2x : f e₂ ≠ f x := fun h => hx2 (hf h2 hxA h).symm
    have hg1x : g e₁ ≠ g x := fun h => hx1 (hg h1 hxA h).symm
    have hg2x : g e₂ ≠ g x := fun h => hx2 (hg h2 hxA h).symm
    rcases lt_or_gt_of_ne hf1x with h1f | h1f <;>
      rcases lt_or_gt_of_ne hf2x with h2f | h2f <;>
      rcases lt_or_gt_of_ne hg1x with h1g | h1g <;>
      rcases lt_or_gt_of_ne hg2x with h2g | h2g
    all_goals
      try linarith
    all_goals
      simp only [h1f, h2f, h1g, h2g, lt_asymm h1f, lt_asymm h2f, lt_asymm h1g, lt_asymm h2g,
        and_self, and_false, false_and, ↓reduceIte]
      omega
  have hsum2 : ∑ x ∈ R, (crossSet f' x).card ≤ ∑ x ∈ R, (crossSet f x).card :=
    Finset.sum_le_sum hP2
  rw [hdecomp f', hdecomp f, hP1_f', hP3]
  omega

lemma invPairs_swap_right_lt {α : Type*} [DecidableEq α] (A : Finset α) (f g : α → ℝ)
    (hf : Set.InjOn f A) (hg : Set.InjOn g A)
    {e₁ e₂ : α} (h1 : e₁ ∈ A) (h2 : e₂ ∈ A) (hfl : f e₁ < f e₂) (hgr : g e₂ < g e₁) :
    (invPairs A f (swapVal g e₁ e₂)).card < (invPairs A f g).card := by
  rw [invPairs_comm_card A f (swapVal g e₁ e₂), invPairs_comm_card A f g, swapVal_comm]
  exact invPairs_swap_left_lt A g f hg hf h2 h1 hgr hfl

/-- **Shared-Endpoint Uncrossing Theorem:**
Every `SlabWiring n E` admits another `SlabWiring n E` with at most as many crossings
in which EVERY crossing (inversion) occurs between two **vertex-disjoint** edges! -/
theorem exists_minimal_slabWiring_disjoint_inversions {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W₀ : SlabWiring n E) :
    ∃ W : SlabWiring n E, W.crossings ≤ W₀.crossings ∧
      ∀ (s : Fin (n + 1)) (e₁ e₂ : Fin n × Fin n),
        (e₁, e₂) ∈ invPairs (activeEdges E s) (W.posL s) (W.posR s) →
        e₁.1 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 := by
  classical
  let P : ℕ → Prop := fun c => ∃ W : SlabWiring n E, W.crossings = c
  have hP : ∃ c, P c := ⟨W₀.crossings, W₀, rfl⟩
  let cMin := Nat.find hP
  obtain ⟨W, hWc⟩ := Nat.find_spec hP
  have hle0 : W.crossings ≤ W₀.crossings := by rw [hWc]; exact Nat.find_min' hP ⟨W₀, rfl⟩
  have hmin : ∀ W' : SlabWiring n E, W.crossings ≤ W'.crossings := fun W' => by
    rw [hWc]; exact Nat.find_min' hP ⟨W', rfl⟩
  refine ⟨W, hle0, ?_⟩
  intro s e₁ e₂ hinv
  have hmem := Finset.mem_filter.mp hinv
  have h1act : e₁ ∈ activeEdges E s := (Finset.mem_product.mp hmem.1).1
  have h2act : e₂ ∈ activeEdges E s := (Finset.mem_product.mp hmem.1).2
  have h1a := (Finset.mem_filter.mp h1act).2
  have h2a := (Finset.mem_filter.mp h2act).2
  -- First, e₁.1 ≠ e₂.2 and e₁.2 ≠ e₂.1 are automatic from activeEdges!
  have h12_disj : e₁.1 ≠ e₂.2 := fun heq => by rw [heq] at h1a; omega
  have h21_disj : e₁.2 ≠ e₂.1 := fun heq => by rw [heq] at h1a; omega
  refine ⟨?_, ?_, h12_disj, h21_disj⟩
  · -- Suppose e₁.1 = e₂.1 = k! Take the FIRST slab s* where {e₁, e₂} are inverted!
    intro hsame_fst
    let k : Fin n := e₁.1
    let invSlabs : Finset (Fin (n + 1)) := Finset.univ.filter fun t =>
      (e₁, e₂) ∈ invPairs (activeEdges E t) (W.posL t) (W.posR t) ∨
      (e₂, e₁) ∈ invPairs (activeEdges E t) (W.posL t) (W.posR t)
    have hinv_ne : invSlabs.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hinv⟩⟩
    obtain ⟨sStar, hsStar_mem, hsStar_min⟩ := invSlabs.exists_min_image (fun t : Fin (n + 1) => t.val) hinv_ne
    have hsStar_inv := (Finset.mem_filter.mp hsStar_mem).2
    have he1_sStar : e₁ ∈ activeEdges E sStar := by
      rcases hsStar_inv with h | h
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2
    have he2_sStar : e₂ ∈ activeEdges E sStar := by
      rcases hsStar_inv with h | h
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
    have he1_E : e₁ ∈ E := (Finset.mem_filter.mp he1_sStar).1
    have he2_E : e₂ ∈ E := (Finset.mem_filter.mp he2_sStar).1
    have hks : k.val < sStar.val := (Finset.mem_filter.mp he1_sStar).2.1
    have hs_e1 : sStar.val ≤ e₁.2.val := (Finset.mem_filter.mp he1_sStar).2.2
    have hs_e2 : sStar.val ≤ e₂.2.val := (Finset.mem_filter.mp he2_sStar).2.2
    -- Construct W' by swapping e₁ ↔ e₂ in posL t (k < t ≤ sStar), posR t (k < t < sStar), above j (k < j < sStar)!
    let posL' : Fin (n + 1) → (Fin n × Fin n) → ℝ := fun t =>
      if k.val < t.val ∧ t.val ≤ sStar.val then swapVal (W.posL t) e₁ e₂ else W.posL t
    let posR' : Fin (n + 1) → (Fin n × Fin n) → ℝ := fun t =>
      if k.val < t.val ∧ t.val < sStar.val then swapVal (W.posR t) e₁ e₂ else W.posR t
    let above' : Fin n → (Fin n × Fin n) → Bool := fun j =>
      if k.val < j.val ∧ j.val < sStar.val then swapVal (W.above j) e₁ e₂ else W.above j
    have hact_both : ∀ t : Fin (n + 1), k.val < t.val → t.val ≤ sStar.val →
        e₁ ∈ activeEdges E t ∧ e₂ ∈ activeEdges E t := fun t hkt hts =>
      ⟨Finset.mem_filter.mpr ⟨he1_E, hkt, le_trans hts hs_e1⟩,
       Finset.mem_filter.mpr ⟨he2_E, hsame_fst ▸ hkt, le_trans hts hs_e2⟩⟩
    have hpass_both : ∀ j : Fin n, k.val < j.val → j.val < sStar.val →
        e₁ ∈ passingEdges E j ∧ e₂ ∈ passingEdges E j := fun j hkj hjs =>
      ⟨Finset.mem_filter.mpr ⟨he1_E, hkj, lt_of_lt_of_le hjs hs_e1⟩,
       Finset.mem_filter.mpr ⟨he2_E, hsame_fst ▸ hkj, lt_of_lt_of_le hjs hs_e2⟩⟩
    let W' : SlabWiring n E :=
      { edge_lt := W.edge_lt
        posL := posL'
        posR := posR'
        posL_inj := fun t => by
          dsimp only [posL']
          split_ifs with ht
          · exact swapVal_injOn (W.posL_inj t) (hact_both t ht.1 ht.2).1 (hact_both t ht.1 ht.2).2
          · exact W.posL_inj t
        posR_inj := fun t => by
          dsimp only [posR']
          split_ifs with ht
          · exact swapVal_injOn (W.posR_inj t) (hact_both t ht.1 (le_of_lt ht.2)).1
              (hact_both t ht.1 (le_of_lt ht.2)).2
          · exact W.posR_inj t
        above := above'
        pass_order := fun j a ha b hb => by
          dsimp only [posR', posL']
          by_cases hj : k.val < j.val ∧ j.val < sStar.val
          · have h1c : k.val < j.castSucc.val ∧ j.castSucc.val < sStar.val := ⟨hj.1, hj.2⟩
            have h2c : k.val < j.succ.val ∧ j.succ.val ≤ sStar.val := ⟨by simp; omega, by simp; omega⟩
            rw [if_pos h1c, if_pos h2c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            unfold swapVal
            split_ifs <;> exact W.pass_order j _ (by assumption) _ (by assumption)
          · have h1c : ¬ (k.val < j.castSucc.val ∧ j.castSucc.val < sStar.val) := by
              simp only [Fin.val_castSucc]; exact hj
            rw [if_neg h1c]
            by_cases h2c : k.val < j.succ.val ∧ j.succ.val ≤ sStar.val
            · -- This only happens when j = k! Then neither a nor b (both in passingEdges E k) is e₁ or e₂!
              have hjk : j = k := Fin.ext (by simp at h2c; omega)
              have ha1 : a ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp ha).2.1; rw [hjk] at this; exact lt_irrefl _ this
              have ha2 : a ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp ha).2.1; rw [hjk, ← hsame_fst] at this; exact lt_irrefl _ this
              have hb1 : b ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp hb).2.1; rw [hjk] at this; exact lt_irrefl _ this
              have hb2 : b ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp hb).2.1; rw [hjk, ← hsame_fst] at this; exact lt_irrefl _ this
              rw [if_pos h2c, swapVal_other _ ha1 ha2, swapVal_other _ hb1 hb2]
              exact W.pass_order j a ha b hb
            · rw [if_neg h2c]; exact W.pass_order j a ha b hb
        pass_above_end := fun j e he e' he' => by
          dsimp only [above', posR']
          by_cases hj : k.val < j.val ∧ j.val < sStar.val
          · have h1c : k.val < j.castSucc.val ∧ j.castSucc.val < sStar.val := ⟨hj.1, hj.2⟩
            simp only [if_pos hj, if_pos h1c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            have he'1 : e' ≠ e₁ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_ending E j) h1p he'
            have he'2 : e' ≠ e₂ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_ending E j) h2p he'
            rw [swapVal_other _ he'1 he'2]
            by_cases h1 : e = e₁
            · subst h1; simp only [swapVal_self_left]; exact W.pass_above_end j e₂ h2p e' he'
            · by_cases h2 : e = e₂
              · subst h2; simp only [swapVal_self_right]; exact W.pass_above_end j e₁ h1p e' he'
              · simp only [swapVal_other _ h1 h2]; exact W.pass_above_end j e he e' he'
          · have h1c : ¬ (k.val < j.castSucc.val ∧ j.castSucc.val < sStar.val) := by
              simp only [Fin.val_castSucc]; exact hj
            simp only [if_neg hj, if_neg h1c]
            exact W.pass_above_end j e he e' he'
        pass_above_start := fun j e he e' he' => by
          dsimp only [above', posL']
          by_cases hj : k.val < j.val ∧ j.val < sStar.val
          · have h2c : k.val < j.succ.val ∧ j.succ.val ≤ sStar.val := ⟨by simp; omega, by simp; omega⟩
            simp only [if_pos hj, if_pos h2c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            have he'1 : e' ≠ e₁ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_starting E j) h1p he'
            have he'2 : e' ≠ e₂ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_starting E j) h2p he'
            rw [swapVal_other _ he'1 he'2]
            by_cases h1 : e = e₁
            · subst h1; simp only [swapVal_self_left]; exact W.pass_above_start j e₂ h2p e' he'
            · by_cases h2 : e = e₂
              · subst h2; simp only [swapVal_self_right]; exact W.pass_above_start j e₁ h1p e' he'
              · simp only [swapVal_other _ h1 h2]; exact W.pass_above_start j e he e' he'
          · simp only [if_neg hj]
            by_cases h2c : k.val < j.succ.val ∧ j.succ.val ≤ sStar.val
            · have hjk : j = k := Fin.ext (by simp at h2c; omega)
              have he1 : e ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp he).2.1; rw [hjk] at this; exact lt_irrefl _ this
              have he2 : e ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp he).2.1; rw [hjk, ← hsame_fst] at this; exact lt_irrefl _ this
              have h1s : e₁ ∈ startingEdges E j := Finset.mem_filter.mpr ⟨he1_E, hjk.symm⟩
              have h2s : e₂ ∈ startingEdges E j := Finset.mem_filter.mpr ⟨he2_E, hsame_fst.symm.trans hjk.symm⟩
              simp only [if_pos h2c, swapVal_other _ he1 he2]
              by_cases h1 : e' = e₁
              · subst h1; simp only [swapVal_self_left]; exact W.pass_above_start j e he e₂ h2s
              · by_cases h2 : e' = e₂
                · subst h2; simp only [swapVal_self_right]; exact W.pass_above_start j e he e₁ h1s
                · simp only [swapVal_other _ h1 h2]; exact W.pass_above_start j e he e' he'
            · simp only [if_neg h2c]; exact W.pass_above_start j e he e' he'
        pass_below_lt_above := fun j a ha b hb haF hbT => by
          dsimp only [above', posR'] at haF hbT ⊢
          by_cases hj : k.val < j.val ∧ j.val < sStar.val
          · have h1c : k.val < j.castSucc.val ∧ j.castSucc.val < sStar.val := ⟨hj.1, hj.2⟩
            simp only [if_pos hj] at haF hbT
            simp only [if_pos h1c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            unfold swapVal at haF hbT ⊢
            split_ifs at haF hbT ⊢ <;>
              exact W.pass_below_lt_above j _ (by assumption) _ (by assumption) haF hbT
          · have h1c : ¬ (k.val < j.castSucc.val ∧ j.castSucc.val < sStar.val) := by
              simp only [Fin.val_castSucc]; exact hj
            simp only [if_neg hj] at haF hbT
            simp only [if_neg h1c]
            exact W.pass_below_lt_above j a ha b hb haF hbT }
    -- Now show W'.crossings < W.crossings!
    have hlt_cross : W'.crossings < W.crossings := by
      unfold SlabWiring.crossings
      refine Finset.sum_lt_sum ?_ ⟨sStar, Finset.mem_univ _, ?_⟩
      · intro t _
        dsimp only [W', posL', posR']
        by_cases h1 : k.val < t.val ∧ t.val < sStar.val
        · have h2 : k.val < t.val ∧ t.val ≤ sStar.val := ⟨h1.1, le_of_lt h1.2⟩
          rw [if_pos h2, if_pos h1]
          exact le_of_eq (invPairs_swap_both_card (activeEdges E t) (W.posL t) (W.posR t)
            (hact_both t h2.1 h2.2).1 (hact_both t h2.1 h2.2).2)
        · by_cases h2 : k.val < t.val ∧ t.val ≤ sStar.val
          · have htEq : t = sStar := Fin.ext (by omega)
            subst htEq
            rw [if_pos h2, if_neg h1]
            rcases hsStar_inv with h | h
            · have hp := (Finset.mem_filter.mp h).2
              exact le_of_lt (invPairs_swap_left_lt (activeEdges E t) (W.posL t) (W.posR t)
                (W.posL_inj t) (W.posR_inj t) he1_sStar he2_sStar hp.1 hp.2)
            · have hp := (Finset.mem_filter.mp h).2
              rw [swapVal_comm]
              exact le_of_lt (invPairs_swap_left_lt (activeEdges E t) (W.posL t) (W.posR t)
                (W.posL_inj t) (W.posR_inj t) he2_sStar he1_sStar hp.1 hp.2)
          · rw [if_neg h2, if_neg h1]
      · dsimp only [W', posL', posR']
        rw [if_pos ⟨hks, le_rfl⟩, if_neg (by intro h; exact lt_irrefl _ h.2)]
        rcases hsStar_inv with h | h
        · have hp := (Finset.mem_filter.mp h).2
          exact invPairs_swap_left_lt (activeEdges E sStar) (W.posL sStar) (W.posR sStar)
            (W.posL_inj sStar) (W.posR_inj sStar) he1_sStar he2_sStar hp.1 hp.2
        · have hp := (Finset.mem_filter.mp h).2
          rw [swapVal_comm]
          exact invPairs_swap_left_lt (activeEdges E sStar) (W.posL sStar) (W.posR sStar)
            (W.posL_inj sStar) (W.posR_inj sStar) he2_sStar he1_sStar hp.1 hp.2
    exact absurd (hmin W') (not_le_of_gt hlt_cross)
  · -- Symmetrically, suppose e₁.2 = e₂.2 = k! Take the LAST slab s* where {e₁, e₂} are inverted!
    intro hsame_snd
    let k : Fin n := e₁.2
    let invSlabs : Finset (Fin (n + 1)) := Finset.univ.filter fun t =>
      (e₁, e₂) ∈ invPairs (activeEdges E t) (W.posL t) (W.posR t) ∨
      (e₂, e₁) ∈ invPairs (activeEdges E t) (W.posL t) (W.posR t)
    have hinv_ne : invSlabs.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hinv⟩⟩
    obtain ⟨sStar, hsStar_mem, hsStar_max⟩ := invSlabs.exists_max_image (fun t : Fin (n + 1) => t.val) hinv_ne
    have hsStar_inv := (Finset.mem_filter.mp hsStar_mem).2
    have he1_sStar : e₁ ∈ activeEdges E sStar := by
      rcases hsStar_inv with h | h
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2
    have he2_sStar : e₂ ∈ activeEdges E sStar := by
      rcases hsStar_inv with h | h
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
    have he1_E : e₁ ∈ E := (Finset.mem_filter.mp he1_sStar).1
    have he2_E : e₂ ∈ E := (Finset.mem_filter.mp he2_sStar).1
    have hsk : sStar.val ≤ k.val := (Finset.mem_filter.mp he1_sStar).2.2
    have he1_s : e₁.1.val < sStar.val := (Finset.mem_filter.mp he1_sStar).2.1
    have he2_s : e₂.1.val < sStar.val := (Finset.mem_filter.mp he2_sStar).2.1
    -- Swap e₁ ↔ e₂ in posR t (sStar ≤ t ≤ k), posL t (sStar < t ≤ k), above j (sStar ≤ j < k)!
    let posL' : Fin (n + 1) → (Fin n × Fin n) → ℝ := fun t =>
      if sStar.val < t.val ∧ t.val ≤ k.val then swapVal (W.posL t) e₁ e₂ else W.posL t
    let posR' : Fin (n + 1) → (Fin n × Fin n) → ℝ := fun t =>
      if sStar.val ≤ t.val ∧ t.val ≤ k.val then swapVal (W.posR t) e₁ e₂ else W.posR t
    let above' : Fin n → (Fin n × Fin n) → Bool := fun j =>
      if sStar.val ≤ j.val ∧ j.val < k.val then swapVal (W.above j) e₁ e₂ else W.above j
    have hact_both : ∀ t : Fin (n + 1), sStar.val ≤ t.val → t.val ≤ k.val →
        e₁ ∈ activeEdges E t ∧ e₂ ∈ activeEdges E t := fun t hst htk =>
      ⟨Finset.mem_filter.mpr ⟨he1_E, lt_of_lt_of_le he1_s hst, htk⟩,
       Finset.mem_filter.mpr ⟨he2_E, lt_of_lt_of_le he2_s hst, hsame_snd ▸ htk⟩⟩
    have hpass_both : ∀ j : Fin n, sStar.val ≤ j.val → j.val < k.val →
        e₁ ∈ passingEdges E j ∧ e₂ ∈ passingEdges E j := fun j hsj hjk =>
      ⟨Finset.mem_filter.mpr ⟨he1_E, lt_of_lt_of_le he1_s hsj, hjk⟩,
       Finset.mem_filter.mpr ⟨he2_E, lt_of_lt_of_le he2_s hsj, hsame_snd ▸ hjk⟩⟩
    let W' : SlabWiring n E :=
      { edge_lt := W.edge_lt
        posL := posL'
        posR := posR'
        posL_inj := fun t => by
          dsimp only [posL']
          split_ifs with ht
          · exact swapVal_injOn (W.posL_inj t) (hact_both t (le_of_lt ht.1) ht.2).1
              (hact_both t (le_of_lt ht.1) ht.2).2
          · exact W.posL_inj t
        posR_inj := fun t => by
          dsimp only [posR']
          split_ifs with ht
          · exact swapVal_injOn (W.posR_inj t) (hact_both t ht.1 ht.2).1 (hact_both t ht.1 ht.2).2
          · exact W.posR_inj t
        above := above'
        pass_order := fun j a ha b hb => by
          dsimp only [posR', posL']
          by_cases hj : sStar.val ≤ j.val ∧ j.val < k.val
          · have h1c : sStar.val ≤ j.castSucc.val ∧ j.castSucc.val ≤ k.val := ⟨hj.1, le_of_lt hj.2⟩
            have h2c : sStar.val < j.succ.val ∧ j.succ.val ≤ k.val := ⟨by simp; omega, by simp; omega⟩
            rw [if_pos h1c, if_pos h2c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            unfold swapVal
            split_ifs <;> exact W.pass_order j _ (by assumption) _ (by assumption)
          · have h2c : ¬ (sStar.val < j.succ.val ∧ j.succ.val ≤ k.val) := by
              simp only [Fin.val_succ]; intro h; exact hj ⟨by omega, by omega⟩
            rw [if_neg h2c]
            by_cases h1c : sStar.val ≤ j.castSucc.val ∧ j.castSucc.val ≤ k.val
            · -- Only happens when j = k! Neither a nor b (in passingEdges E k) is e₁ or e₂!
              have hjk : j = k := Fin.ext (by simp at h1c; omega)
              have ha1 : a ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp ha).2.2; rw [hjk] at this; exact lt_irrefl _ this
              have ha2 : a ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp ha).2.2; rw [hjk, ← hsame_snd] at this; exact lt_irrefl _ this
              have hb1 : b ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp hb).2.2; rw [hjk] at this; exact lt_irrefl _ this
              have hb2 : b ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp hb).2.2; rw [hjk, ← hsame_snd] at this; exact lt_irrefl _ this
              rw [if_pos h1c, swapVal_other _ ha1 ha2, swapVal_other _ hb1 hb2]
              exact W.pass_order j a ha b hb
            · rw [if_neg h1c]; exact W.pass_order j a ha b hb
        pass_above_end := fun j e he e' he' => by
          dsimp only [above', posR']
          by_cases hj : sStar.val ≤ j.val ∧ j.val < k.val
          · have h1c : sStar.val ≤ j.castSucc.val ∧ j.castSucc.val ≤ k.val := ⟨hj.1, le_of_lt hj.2⟩
            simp only [if_pos hj, if_pos h1c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            have he'1 : e' ≠ e₁ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_ending E j) h1p he'
            have he'2 : e' ≠ e₂ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_ending E j) h2p he'
            rw [swapVal_other _ he'1 he'2]
            by_cases h1 : e = e₁
            · subst h1; simp only [swapVal_self_left]; exact W.pass_above_end j e₂ h2p e' he'
            · by_cases h2 : e = e₂
              · subst h2; simp only [swapVal_self_right]; exact W.pass_above_end j e₁ h1p e' he'
              · simp only [swapVal_other _ h1 h2]; exact W.pass_above_end j e he e' he'
          · simp only [if_neg hj]
            by_cases h1c : sStar.val ≤ j.castSucc.val ∧ j.castSucc.val ≤ k.val
            · have hjk : j = k := Fin.ext (by simp at h1c; omega)
              have he1 : e ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp he).2.2; rw [hjk] at this; exact lt_irrefl _ this
              have he2 : e ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp he).2.2; rw [hjk, ← hsame_snd] at this; exact lt_irrefl _ this
              have h1e : e₁ ∈ endingEdges E j := Finset.mem_filter.mpr ⟨he1_E, hjk.symm⟩
              have h2e : e₂ ∈ endingEdges E j := Finset.mem_filter.mpr ⟨he2_E, hsame_snd.symm.trans hjk.symm⟩
              simp only [if_pos h1c, swapVal_other _ he1 he2]
              by_cases h1 : e' = e₁
              · subst h1; simp only [swapVal_self_left]; exact W.pass_above_end j e he e₂ h2e
              · by_cases h2 : e' = e₂
                · subst h2; simp only [swapVal_self_right]; exact W.pass_above_end j e he e₁ h1e
                · simp only [swapVal_other _ h1 h2]; exact W.pass_above_end j e he e' he'
            · simp only [if_neg h1c]; exact W.pass_above_end j e he e' he'
        pass_above_start := fun j e he e' he' => by
          dsimp only [above', posL']
          by_cases hj : sStar.val ≤ j.val ∧ j.val < k.val
          · have h2c : sStar.val < j.succ.val ∧ j.succ.val ≤ k.val := ⟨by simp; omega, by simp; omega⟩
            simp only [if_pos hj, if_pos h2c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            have he'1 : e' ≠ e₁ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_starting E j) h1p he'
            have he'2 : e' ≠ e₂ := fun heq => by subst heq; exact Finset.disjoint_left.mp (disjoint_passing_starting E j) h2p he'
            rw [swapVal_other _ he'1 he'2]
            by_cases h1 : e = e₁
            · subst h1; simp only [swapVal_self_left]; exact W.pass_above_start j e₂ h2p e' he'
            · by_cases h2 : e = e₂
              · subst h2; simp only [swapVal_self_right]; exact W.pass_above_start j e₁ h1p e' he'
              · simp only [swapVal_other _ h1 h2]; exact W.pass_above_start j e he e' he'
          · have h2c : ¬ (sStar.val < j.succ.val ∧ j.succ.val ≤ k.val) := by
              simp only [Fin.val_succ]; intro h; exact hj ⟨by omega, by omega⟩
            simp only [if_neg hj, if_neg h2c]
            exact W.pass_above_start j e he e' he'
        pass_below_lt_above := fun j a ha b hb haF hbT => by
          dsimp only [above', posR'] at haF hbT ⊢
          by_cases hj : sStar.val ≤ j.val ∧ j.val < k.val
          · have h1c : sStar.val ≤ j.castSucc.val ∧ j.castSucc.val ≤ k.val := ⟨hj.1, le_of_lt hj.2⟩
            simp only [if_pos hj] at haF hbT
            simp only [if_pos h1c]
            have ⟨h1p, h2p⟩ := hpass_both j hj.1 hj.2
            unfold swapVal at haF hbT ⊢
            split_ifs at haF hbT ⊢ <;>
              exact W.pass_below_lt_above j _ (by assumption) _ (by assumption) haF hbT
          · simp only [if_neg hj] at haF hbT
            by_cases h1c : sStar.val ≤ j.castSucc.val ∧ j.castSucc.val ≤ k.val
            · have hjk : j = k := Fin.ext (by simp at h1c; omega)
              have ha1 : a ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp ha).2.2; rw [hjk] at this; exact lt_irrefl _ this
              have ha2 : a ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp ha).2.2; rw [hjk, ← hsame_snd] at this; exact lt_irrefl _ this
              have hb1 : b ≠ e₁ := fun heq => by subst heq; have := (Finset.mem_filter.mp hb).2.2; rw [hjk] at this; exact lt_irrefl _ this
              have hb2 : b ≠ e₂ := fun heq => by subst heq; have := (Finset.mem_filter.mp hb).2.2; rw [hjk, ← hsame_snd] at this; exact lt_irrefl _ this
              simp only [if_pos h1c, swapVal_other _ ha1 ha2, swapVal_other _ hb1 hb2]
              exact W.pass_below_lt_above j a ha b hb haF hbT
            · simp only [if_neg h1c]; exact W.pass_below_lt_above j a ha b hb haF hbT }
    have hlt_cross : W'.crossings < W.crossings := by
      unfold SlabWiring.crossings
      refine Finset.sum_lt_sum ?_ ⟨sStar, Finset.mem_univ _, ?_⟩
      · intro t _
        dsimp only [W', posL', posR']
        by_cases h1 : sStar.val < t.val ∧ t.val ≤ k.val
        · have h2 : sStar.val ≤ t.val ∧ t.val ≤ k.val := ⟨le_of_lt h1.1, h1.2⟩
          rw [if_pos h1, if_pos h2]
          exact le_of_eq (invPairs_swap_both_card (activeEdges E t) (W.posL t) (W.posR t)
            (hact_both t h2.1 h2.2).1 (hact_both t h2.1 h2.2).2)
        · by_cases h2 : sStar.val ≤ t.val ∧ t.val ≤ k.val
          · have htEq : t = sStar := Fin.ext (by omega)
            subst htEq
            rw [if_neg h1, if_pos h2]
            rcases hsStar_inv with h | h
            · have hp := (Finset.mem_filter.mp h).2
              exact le_of_lt (invPairs_swap_right_lt (activeEdges E t) (W.posL t) (W.posR t)
                (W.posL_inj t) (W.posR_inj t) he1_sStar he2_sStar hp.1 hp.2)
            · have hp := (Finset.mem_filter.mp h).2
              rw [swapVal_comm]
              exact le_of_lt (invPairs_swap_right_lt (activeEdges E t) (W.posL t) (W.posR t)
                (W.posL_inj t) (W.posR_inj t) he2_sStar he1_sStar hp.1 hp.2)
          · rw [if_neg h1, if_neg h2]
      · dsimp only [W', posL', posR']
        rw [if_neg (by intro h; exact lt_irrefl _ h.1), if_pos ⟨le_rfl, hsk⟩]
        rcases hsStar_inv with h | h
        · have hp := (Finset.mem_filter.mp h).2
          exact invPairs_swap_right_lt (activeEdges E sStar) (W.posL sStar) (W.posR sStar)
            (W.posL_inj sStar) (W.posR_inj sStar) he1_sStar he2_sStar hp.1 hp.2
        · have hp := (Finset.mem_filter.mp h).2
          rw [swapVal_comm]
          exact invPairs_swap_right_lt (activeEdges E sStar) (W.posL sStar) (W.posR sStar)
            (W.posL_inj sStar) (W.posR_inj sStar) he2_sStar he1_sStar hp.1 hp.2
    exact absurd (hmin W') (not_le_of_gt hlt_cross)

/-- Restricting a `SlabWiring` to a subset of edges `E' ⊆ E`. -/
def SlabWiring.restrictEdges {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    {E' : Finset (Fin n × Fin n)} (hsub : E' ⊆ E) : SlabWiring n E' where
  edge_lt := fun e he => W.edge_lt e (hsub he)
  posL := W.posL
  posR := W.posR
  posL_inj := fun s => (W.posL_inj s).mono (Finset.filter_subset_filter _ hsub)
  posR_inj := fun s => (W.posR_inj s).mono (Finset.filter_subset_filter _ hsub)
  above := W.above
  pass_order := fun k e₁ h₁ e₂ h₂ => W.pass_order k e₁ (Finset.filter_subset_filter _ hsub h₁)
    e₂ (Finset.filter_subset_filter _ hsub h₂)
  pass_above_end := fun k e he e' he' => W.pass_above_end k e (Finset.filter_subset_filter _ hsub he)
    e' (Finset.filter_subset_filter _ hsub he')
  pass_above_start := fun k e he e' he' => W.pass_above_start k e (Finset.filter_subset_filter _ hsub he)
    e' (Finset.filter_subset_filter _ hsub he')
  pass_below_lt_above := fun k e₁ h₁ e₂ h₂ => W.pass_below_lt_above k e₁ (Finset.filter_subset_filter _ hsub h₁)
    e₂ (Finset.filter_subset_filter _ hsub h₂)

/-- **Linear Crossing Bound for `SlabWiring`:** `|E| ≤ 3 * n + W.crossings`. -/
theorem slabWiring_linear_crossing_bound {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E) :
    E.card ≤ 3 * n + W.crossings := by
  classical
  suffices h : ∀ (c : ℕ) (E : Finset (Fin n × Fin n)) (W : SlabWiring n E),
      W.crossings = c → E.card ≤ 3 * n + c by
    exact h W.crossings E W rfl
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro E W hWc
    by_cases hc0 : c = 0
    · subst hc0
      simpa using slabWiring_zero_crossings_edge_le W hWc
    · have hpos : 0 < ∑ s : Fin (n + 1), (invPairs (activeEdges E s) (W.posL s) (W.posR s)).card := by
        rw [← SlabWiring.crossings, hWc]; omega
      obtain ⟨s, _, hs_pos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
      obtain ⟨⟨e₁, e₂⟩, hinv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hs_pos)
      have he₁_act : e₁ ∈ activeEdges E s := (Finset.mem_product.mp (Finset.mem_filter.mp hinv).1).1
      have he₁_E : e₁ ∈ E := (Finset.mem_filter.mp he₁_act).1
      let E' := E.erase e₁
      let W' := W.restrictEdges (Finset.erase_subset e₁ E)
      have hlt : W'.crossings < W.crossings := by
        unfold SlabWiring.crossings
        refine Finset.sum_lt_sum ?_ ⟨s, Finset.mem_univ _, ?_⟩
        · intro t _
          refine Finset.card_le_card ?_
          intro p hp
          simp only [W', SlabWiring.restrictEdges, invPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨Finset.filter_subset_filter _ (Finset.erase_subset e₁ E) hp.1.1,
            Finset.filter_subset_filter _ (Finset.erase_subset e₁ E) hp.1.2⟩, hp.2⟩
        · refine Finset.card_lt_card ?_
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro p hp
            simp only [W', SlabWiring.restrictEdges, invPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
            exact ⟨⟨Finset.filter_subset_filter _ (Finset.erase_subset e₁ E) hp.1.1,
              Finset.filter_subset_filter _ (Finset.erase_subset e₁ E) hp.1.2⟩, hp.2⟩
          · intro hEq
            have hmem : (e₁, e₂) ∈ invPairs (activeEdges E' s) (W'.posL s) (W'.posR s) := by
              rw [hEq]; exact hinv
            have h1' : e₁ ∈ activeEdges E' s := (Finset.mem_product.mp (Finset.mem_filter.mp hmem).1).1
            exact Finset.notMem_erase e₁ E (Finset.mem_filter.mp h1').1
      have hih := ih W'.crossings (by omega) E' W' rfl
      have hcard' : E.card = E'.card + 1 := (Finset.card_erase_add_one he₁_E).symm
      omega

/-- Triangle inequality for inversions: every inversion of `(f, h)` is an inversion of `(f, g)` or `(g, h)`. -/
lemma invPairs_triangle {α : Type*} (A : Finset α) (f g h : α → ℝ) (hg : Set.InjOn g A) :
    invPairs A f h ⊆ invPairs A f g ∪ invPairs A g h := by
  intro ⟨a, b⟩ hab
  simp only [invPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_union] at hab ⊢
  obtain ⟨⟨haA, hbA⟩, hfl, hhr⟩ := hab
  have hne : a ≠ b := fun heq => lt_irrefl _ (heq ▸ hfl)
  have hgne : g a ≠ g b := fun heq => hne (hg haA hbA heq)
  rcases lt_or_gt_of_ne hgne with hgl | hgr
  · exact Or.inr ⟨⟨haA, hbA⟩, hgl, hhr⟩
  · exact Or.inl ⟨⟨haA, hbA⟩, hfl, hgr⟩

/-- Induced sub-wiring of `W : SlabWiring n E` on any vertex subset `S : Finset (Fin n)`. -/
lemma slabWiring_induced_subset {n : ℕ} {E : Finset (Fin n × Fin n)} (W : SlabWiring n E)
    (S : Finset (Fin n)) :
    (E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card ≤
      3 * S.card +
        ∑ s : Fin (n + 1),
          ((invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
            (fun p => p.1.1 ∈ S ∧ p.1.2 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S)).card := by
  classical
  let m := S.card
  let φ : Fin m ↪o Fin n := S.orderEmbOfFin rfl
  let liftE : Fin m × Fin m → Fin n × Fin n := fun e => (φ e.1, φ e.2)
  let E_S : Finset (Fin m × Fin m) := (Finset.univ ×ˢ Finset.univ).filter (fun e => liftE e ∈ E)
  have hE_S_card : E_S.card = (E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card := by
    refine Finset.card_bij (fun e _ => liftE e) ?_ ?_ ?_
    · intro e he
      have heE : liftE e ∈ E := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨heE, S.orderEmbOfFin_mem rfl e.1, S.orderEmbOfFin_mem rfl e.2⟩
    · intro e₁ _ e₂ _ hEq
      exact Prod.ext (φ.injective (congrArg Prod.fst hEq)) (φ.injective (congrArg Prod.snd hEq))
    · intro e he
      obtain ⟨heE, h1S, h2S⟩ := Finset.mem_filter.mp he
      have hrng : Set.range φ = (S : Set (Fin n)) := S.range_orderEmbOfFin rfl
      have h1r : e.1 ∈ Set.range φ := by rw [hrng]; exact h1S
      have h2r : e.2 ∈ Set.range φ := by rw [hrng]; exact h2S
      obtain ⟨a, ha⟩ := Set.mem_range.mp h1r
      obtain ⟨b, hb⟩ := Set.mem_range.mp h2r
      refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
      · have heq : liftE (a, b) = e := Prod.ext ha hb
        rw [heq]; exact heE
      · exact Prod.ext ha hb
  have hE_S_lt : ∀ e ∈ E_S, e.1 < e.2 := by
    intro e he
    have hlt := W.edge_lt (liftE e) (Finset.mem_filter.mp he).2
    exact φ.lt_iff_lt.mp hlt
  -- Build SlabWiring m E_S!
  -- On slab t : Fin (m + 1) with 0 < t.val < m: t = (i : Fin m).succ = (j : Fin m).castSucc where j = i + 1!
  let posL_S : Fin (m + 1) → (Fin m × Fin m) → ℝ := fun t e =>
    if h : 0 < t.val ∧ t.val < m then
      W.posL (φ ⟨t.val - 1, by omega⟩).succ (liftE e)
    else 0
  let posR_S : Fin (m + 1) → (Fin m × Fin m) → ℝ := fun t e =>
    if h : 0 < t.val ∧ t.val < m then
      W.posR (φ ⟨t.val, h.2⟩).castSucc (liftE e)
    else 0
  let above_S : Fin m → (Fin m × Fin m) → Bool := fun j e => W.above (φ j) (liftE e)
  have hact_lift : ∀ (t : Fin (m + 1)) (ht : 0 < t.val ∧ t.val < m) (e : Fin m × Fin m),
      e ∈ activeEdges E_S t →
      ∀ (s : Fin (n + 1)), (φ ⟨t.val - 1, by omega⟩).val < s.val → s.val ≤ (φ ⟨t.val, ht.2⟩).val →
      liftE e ∈ activeEdges E s := by
    intro t ht e he s hs1 hs2
    obtain ⟨heS, h1, h2⟩ := Finset.mem_filter.mp he
    have heE : liftE e ∈ E := (Finset.mem_filter.mp heS).2
    have hle1 : (φ e.1).val ≤ (φ ⟨t.val - 1, by omega⟩).val :=
      φ.monotone (show e.1 ≤ ⟨t.val - 1, by omega⟩ by change e.1.val ≤ t.val - 1; omega)
    have hle2 : (φ ⟨t.val, ht.2⟩).val ≤ (φ e.2).val :=
      φ.monotone (show (⟨t.val, ht.2⟩ : Fin m) ≤ e.2 by change t.val ≤ e.2.val; omega)
    exact Finset.mem_filter.mpr ⟨heE, by dsimp [liftE]; omega, by dsimp [liftE]; omega⟩
  have hpass_lift : ∀ (j : Fin m) (e : Fin m × Fin m),
      e ∈ passingEdges E_S j → liftE e ∈ passingEdges E (φ j) := by
    intro j e he
    obtain ⟨heS, h1, h2⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heS).2,
      φ.lt_iff_lt.mpr (show e.1 < j from h1), φ.lt_iff_lt.mpr (show j < e.2 from h2)⟩
  have hend_lift : ∀ (j : Fin m) (e : Fin m × Fin m),
      e ∈ endingEdges E_S j → liftE e ∈ endingEdges E (φ j) := by
    intro j e he
    obtain ⟨heS, h2⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heS).2, congrArg φ h2⟩
  have hstart_lift : ∀ (j : Fin m) (e : Fin m × Fin m),
      e ∈ startingEdges E_S j → liftE e ∈ startingEdges E (φ j) := by
    intro j e he
    obtain ⟨heS, h1⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heS).2, congrArg φ h1⟩
  have hlift_inj : Function.Injective liftE := fun e₁ e₂ h =>
    Prod.ext (φ.injective (congrArg Prod.fst h)) (φ.injective (congrArg Prod.snd h))
  let W_S : SlabWiring m E_S :=
    { edge_lt := hE_S_lt
      posL := posL_S
      posR := posR_S
      posL_inj := fun t a ha b hb hEq => by
        by_cases ht : 0 < t.val ∧ t.val < m
        · simp only [posL_S, dif_pos ht] at hEq
          have hltφ : (φ ⟨t.val - 1, by omega⟩).val < (φ ⟨t.val, ht.2⟩).val :=
            φ.lt_iff_lt.mpr (show (⟨t.val - 1, by omega⟩ : Fin m) < ⟨t.val, ht.2⟩ by change t.val - 1 < t.val; omega)
          have ha' := hact_lift t ht a ha (φ ⟨t.val - 1, by omega⟩).succ (by simp)
            (by simp only [Fin.val_succ]; omega)
          have hb' := hact_lift t ht b hb (φ ⟨t.val - 1, by omega⟩).succ (by simp)
            (by simp only [Fin.val_succ]; omega)
          exact hlift_inj (W.posL_inj _ ha' hb' hEq)
        · exfalso
          have h1 := (Finset.mem_filter.mp ha).2
          have h2 := a.2.isLt
          omega
      posR_inj := fun t a ha b hb hEq => by
        by_cases ht : 0 < t.val ∧ t.val < m
        · simp only [posR_S, dif_pos ht] at hEq
          have hltφ : (φ ⟨t.val - 1, by omega⟩).val < (φ ⟨t.val, ht.2⟩).val :=
            φ.lt_iff_lt.mpr (show (⟨t.val - 1, by omega⟩ : Fin m) < ⟨t.val, ht.2⟩ by change t.val - 1 < t.val; omega)
          have ha' := hact_lift t ht a ha (φ ⟨t.val, ht.2⟩).castSucc hltφ le_rfl
          have hb' := hact_lift t ht b hb (φ ⟨t.val, ht.2⟩).castSucc hltφ le_rfl
          exact hlift_inj (W.posR_inj _ ha' hb' hEq)
        · exfalso
          have h1 := (Finset.mem_filter.mp ha).2
          have h2 := a.2.isLt
          omega
      above := above_S
      pass_order := fun j e₁ h₁ e₂ h₂ => by
        have hj0 : 0 < j.val := by have := (Finset.mem_filter.mp h₁).2.1; omega
        have hjm : j.val + 1 < m := by have := (Finset.mem_filter.mp h₁).2.2; have := e₁.2.isLt; omega
        have hL : 0 < j.castSucc.val ∧ j.castSucc.val < m := ⟨hj0, j.isLt⟩
        have hR : 0 < j.succ.val ∧ j.succ.val < m := ⟨by simp, by simp; omega⟩
        simp only [posR_S, posL_S, dif_pos hL, dif_pos hR]
        have hj1 : (⟨j.castSucc.val, hL.2⟩ : Fin m) = j := Fin.ext rfl
        have hj2 : (⟨j.succ.val - 1, by omega⟩ : Fin m) = j := Fin.ext (by simp)
        rw [hj1, hj2]
        exact W.pass_order (φ j) (liftE e₁) (hpass_lift j e₁ h₁) (liftE e₂) (hpass_lift j e₂ h₂)
      pass_above_end := fun j e he e' he' => by
        have hj0 : 0 < j.val := by have := (Finset.mem_filter.mp he).2.1; omega
        have hL : 0 < j.castSucc.val ∧ j.castSucc.val < m := ⟨hj0, j.isLt⟩
        simp only [posR_S, above_S, dif_pos hL]
        have hj1 : (⟨j.castSucc.val, hL.2⟩ : Fin m) = j := Fin.ext rfl
        rw [hj1]
        exact W.pass_above_end (φ j) (liftE e) (hpass_lift j e he) (liftE e') (hend_lift j e' he')
      pass_above_start := fun j e he e' he' => by
        have hjm : j.val + 1 < m := by have := (Finset.mem_filter.mp he).2.2; have := e.2.isLt; omega
        have hR : 0 < j.succ.val ∧ j.succ.val < m := ⟨by simp, by simp; omega⟩
        simp only [posL_S, above_S, dif_pos hR]
        have hj2 : (⟨j.succ.val - 1, by omega⟩ : Fin m) = j := Fin.ext (by simp)
        rw [hj2]
        exact W.pass_above_start (φ j) (liftE e) (hpass_lift j e he) (liftE e') (hstart_lift j e' he')
      pass_below_lt_above := fun j e₁ h₁ e₂ h₂ hF hT => by
        have hj0 : 0 < j.val := by have := (Finset.mem_filter.mp h₁).2.1; omega
        have hL : 0 < j.castSucc.val ∧ j.castSucc.val < m := ⟨hj0, j.isLt⟩
        simp only [posR_S, above_S, dif_pos hL] at hF hT ⊢
        have hj1 : (⟨j.castSucc.val, hL.2⟩ : Fin m) = j := Fin.ext rfl
        rw [hj1]
        exact W.pass_below_lt_above (φ j) (liftE e₁) (hpass_lift j e₁ h₁) (liftE e₂) (hpass_lift j e₂ h₂) hF hT }
  -- Bound W_S.crossings by original inversions on slabs whose 4 endpoints lie in S!
  have hcross_le : W_S.crossings ≤
      ∑ s : Fin (n + 1),
        ((invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
          (fun p => p.1.1 ∈ S ∧ p.1.2 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S)).card := by
    let invFilt (s : Fin (n + 1)) :=
      (invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
        (fun p => p.1.1 ∈ S ∧ p.1.2 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S)
    -- For each slab t of W_S with 0 < t.val < m, its inversions inject into ⋃_{u < s ≤ v} invFilt s!
    let slabRange (t : Fin (m + 1)) : Finset (Fin (n + 1)) :=
      if h : 0 < t.val ∧ t.val < m then
        Finset.univ.filter (fun s => (φ ⟨t.val - 1, by omega⟩).val < s.val ∧ s.val ≤ (φ ⟨t.val, h.2⟩).val)
      else ∅
    have hslab_le : ∀ t : Fin (m + 1),
        (invPairs (activeEdges E_S t) (W_S.posL t) (W_S.posR t)).card ≤
          ∑ s ∈ slabRange t, (invFilt s).card := by
      intro t
      by_cases ht : 0 < t.val ∧ t.val < m
      · let u : Fin n := φ ⟨t.val - 1, by omega⟩
        let v : Fin n := φ ⟨t.val, ht.2⟩
        have huv : u.val < v.val :=
          φ.lt_iff_lt.mpr (show (⟨t.val - 1, by omega⟩ : Fin m) < ⟨t.val, ht.2⟩ by change t.val - 1 < t.val; omega)
        have hlift_inv : ∀ p ∈ invPairs (activeEdges E_S t) (W_S.posL t) (W_S.posR t),
            ∃ s ∈ slabRange t, (liftE p.1, liftE p.2) ∈ invFilt s := by
          rintro ⟨a, b⟩ hp
          obtain ⟨hab_prod, hLlt, hRgt⟩ := Finset.mem_filter.mp hp
          obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab_prod
          simp only [W_S, posL_S, posR_S, dif_pos ht] at hLlt hRgt
          -- Chain from u.succ to v.castSucc: at least one slab s ∈ (u, v] must invert (liftE a, liftE b)!
          have hchain : ∀ d : ℕ, ∀ (hd : u.val + 1 + d ≤ v.val),
              let s' : Fin (n + 1) := ⟨u.val + 1 + d, by have := v.isLt; omega⟩
              (W.posR s' (liftE b) < W.posR s' (liftE a)) →
              ∃ s ∈ slabRange t, (liftE a, liftE b) ∈ invFilt s := by
            intro d
            induction d with
            | zero =>
              intro hd s' hR0
              have hs'eq : s' = u.succ := Fin.ext (by simp [s'])
              refine ⟨u.succ, ?_, ?_⟩
              · simp only [slabRange, dif_pos ht, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ]
                exact ⟨by dsimp [u]; omega, by dsimp [u, v] at huv ⊢; omega⟩
              · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨hact_lift t ht a ha u.succ (by simp [u]) (by simp only [Fin.val_succ]; dsimp [u, v] at huv ⊢; omega),
                   hact_lift t ht b hb u.succ (by simp [u]) (by simp only [Fin.val_succ]; dsimp [u, v] at huv ⊢; omega)⟩,
                  hLlt, hs'eq ▸ hR0⟩,
                  S.orderEmbOfFin_mem rfl a.1, S.orderEmbOfFin_mem rfl a.2,
                  S.orderEmbOfFin_mem rfl b.1, S.orderEmbOfFin_mem rfl b.2⟩
            | succ d ih =>
              intro hd s' hRd
              have hs'in : s' ∈ slabRange t := by
                simp only [slabRange, dif_pos ht, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨by simp [s', u]; omega, by simp [s']; omega⟩
              have ha_s' := hact_lift t ht a ha s' (by simp [s', u]; omega) (by simp [s']; omega)
              have hb_s' := hact_lift t ht b hb s' (by simp [s', u]; omega) (by simp [s']; omega)
              have hne_ab : liftE a ≠ liftE b := fun heq => lt_irrefl _ (heq ▸ hLlt)
              have hneL : W.posL s' (liftE a) ≠ W.posL s' (liftE b) :=
                fun h => hne_ab (W.posL_inj s' ha_s' hb_s' h)
              rcases lt_or_gt_of_ne hneL with hltL | hgtL
              · exact ⟨s', hs'in, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨ha_s', hb_s'⟩, hltL, hRd⟩,
                  S.orderEmbOfFin_mem rfl a.1, S.orderEmbOfFin_mem rfl a.2,
                  S.orderEmbOfFin_mem rfl b.1, S.orderEmbOfFin_mem rfl b.2⟩⟩
              · let k : Fin n := ⟨u.val + 1 + d, by have := v.isLt; omega⟩
                have hs'eq : s' = k.succ := Fin.ext (by simp [s', k]; omega)
                have hprev : (⟨u.val + 1 + d, by have := v.isLt; omega⟩ : Fin (n + 1)) = k.castSucc := Fin.ext rfl
                have ha_pass : liftE a ∈ passingEdges E k := by
                  have hact := hact_lift t ht a ha k.castSucc (by simp [k, u]; omega) (by simp [k]; omega)
                  have hact2 := hact_lift t ht a ha s' (by simp [s', u]; omega) (by simp [s']; omega)
                  simp only [activeEdges, passingEdges, Finset.mem_filter] at hact hact2 ⊢
                  exact ⟨hact.1, hact.2.1, by simp only [s', k] at hact2 ⊢; omega⟩
                have hb_pass : liftE b ∈ passingEdges E k := by
                  have hact := hact_lift t ht b hb k.castSucc (by simp [k, u]; omega) (by simp [k]; omega)
                  have hact2 := hact_lift t ht b hb s' (by simp [s', u]; omega) (by simp [s']; omega)
                  simp only [activeEdges, passingEdges, Finset.mem_filter] at hact hact2 ⊢
                  exact ⟨hact.1, hact.2.1, by simp only [s', k] at hact2 ⊢; omega⟩
                have hprevR : W.posR k.castSucc (liftE b) < W.posR k.castSucc (liftE a) :=
                  (W.pass_order k (liftE b) hb_pass (liftE a) ha_pass).mpr (hs'eq ▸ hgtL)
                exact ih (by omega) (hprev.symm ▸ hprevR)
          have hlast := hchain (v.val - (u.val + 1)) (by omega)
          have hveq : (⟨u.val + 1 + (v.val - (u.val + 1)), by have := v.isLt; omega⟩ : Fin (n + 1)) = v.castSucc :=
            Fin.ext (by dsimp; omega)
          exact hlast (hveq.symm ▸ hRgt)
        -- Lift injection into biUnion over slabRange t!
        have hinj_lift : Set.InjOn (fun p : (Fin m × Fin m) × (Fin m × Fin m) => (liftE p.1, liftE p.2))
            (invPairs (activeEdges E_S t) (W_S.posL t) (W_S.posR t)) :=
          fun p₁ _ p₂ _ h => Prod.ext (hlift_inj (congrArg Prod.fst h)) (hlift_inj (congrArg Prod.snd h))
        rw [← Finset.card_image_of_injOn hinj_lift]
        calc ((invPairs (activeEdges E_S t) (W_S.posL t) (W_S.posR t)).image
                (fun p => (liftE p.1, liftE p.2))).card
            ≤ ((slabRange t).biUnion invFilt).card := by
              refine Finset.card_le_card ?_
              intro q hq
              rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
              obtain ⟨s, hs, hmem⟩ := hlift_inv p hp
              exact Finset.mem_biUnion.mpr ⟨s, hs, hmem⟩
          _ ≤ ∑ s ∈ slabRange t, (invFilt s).card := Finset.card_biUnion_le
      · -- Active edges empty when t = 0 or t = m!
        have hemp : activeEdges E_S t = ∅ := by
          ext e; simp only [activeEdges, Finset.mem_filter, Finset.notMem_empty, iff_false]
          rintro ⟨_, h1, h2⟩; have := e.2.isLt; omega
        simp [hemp, invPairs]
    -- The slabRanges for distinct t are pairwise disjoint!
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin (m + 1))) slabRange := by
      intro t₁ _ t₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      by_cases ht1 : 0 < t₁.val ∧ t₁.val < m
      · by_cases ht2 : 0 < t₂.val ∧ t₂.val < m
        · simp only [slabRange, dif_pos ht1, dif_pos ht2, Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
          have hne_val : t₁.val ≠ t₂.val := fun h => hne (Fin.ext h)
          rcases lt_or_gt_of_ne hne_val with hlt | hgt
          · have hle : (φ ⟨t₁.val, ht1.2⟩).val ≤ (φ ⟨t₂.val - 1, by omega⟩).val :=
              φ.monotone (show (⟨t₁.val, ht1.2⟩ : Fin m) ≤ ⟨t₂.val - 1, by omega⟩ by change t₁.val ≤ t₂.val - 1; omega)
            omega
          · have hle : (φ ⟨t₂.val, ht2.2⟩).val ≤ (φ ⟨t₁.val - 1, by omega⟩).val :=
              φ.monotone (show (⟨t₂.val, ht2.2⟩ : Fin m) ≤ ⟨t₁.val - 1, by omega⟩ by change t₂.val ≤ t₁.val - 1; omega)
            omega
        · have hne2 : slabRange t₂ = ∅ := dif_neg ht2
          rw [hne2] at hs2; exact Finset.notMem_empty _ hs2
      · have hne1 : slabRange t₁ = ∅ := dif_neg ht1
        rw [hne1] at hs1; exact Finset.notMem_empty _ hs1
    calc W_S.crossings
        = ∑ t : Fin (m + 1), (invPairs (activeEdges E_S t) (W_S.posL t) (W_S.posR t)).card := rfl
      _ ≤ ∑ t : Fin (m + 1), ∑ s ∈ slabRange t, (invFilt s).card :=
          Finset.sum_le_sum fun t _ => hslab_le t
      _ = ∑ s ∈ (Finset.univ : Finset (Fin (m + 1))).biUnion slabRange, (invFilt s).card :=
          (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ s : Fin (n + 1), (invFilt s).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hlin := slabWiring_linear_crossing_bound W_S
  rw [hE_S_card] at hlin
  exact le_trans hlin (Nat.add_le_add_left hcross_le _)

/-! ### 3D. Binomial Subset-Sampling Expectation & Simple/Multigraph Crossing Lemmas -/

/-- Exact binomial weight sum over all subsets `S ⊆ Fin n` containing a fixed subset `T`:
`∑_{T ⊆ S ⊆ Fin n} p^|S| (1 - p)^(n - |S|) = p^|T|`. -/
lemma sum_powerset_superset_weight {n : ℕ} (T : Finset (Fin n)) (p : ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
      p ^ S.card * (1 - p) ^ (n - S.card) = p ^ T.card := by
  classical
  let C := Tᶜ
  have hbij : ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
        p ^ S.card * (1 - p) ^ (n - S.card) =
      ∑ R ∈ C.powerset, p ^ (T.card + R.card) * (1 - p) ^ (C.card - R.card) := by
    refine Finset.sum_bij (fun S _ => S \ T) ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx
      exact Finset.mem_compl.mpr hx.2
    · intro S₁ hS₁ S₂ hS₂ hEq
      have h1 : T ⊆ S₁ := (Finset.mem_filter.mp hS₁).2
      have h2 : T ⊆ S₂ := (Finset.mem_filter.mp hS₂).2
      rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, hEq]
    · intro R hR
      have hRC : R ⊆ C := Finset.mem_powerset.mp hR
      have hdisj : Disjoint T R := Disjoint.mono_right hRC disjoint_compl_right
      refine ⟨T ∪ R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        Finset.subset_union_left⟩, ?_⟩
      exact Finset.union_sdiff_cancel_left hdisj
    · intro S hS
      have hTS : T ⊆ S := (Finset.mem_filter.mp hS).2
      have hcardS : S.card = T.card + (S \ T).card := by
        have h1 := Finset.card_sdiff_add_card_inter S T
        rw [Finset.inter_eq_right.mpr hTS] at h1
        omega
      have hcardC : C.card = n - T.card := by
        simp [C, Finset.card_compl, Fintype.card_fin]
      rw [hcardS, hcardC]
      congr 2; omega
  rw [hbij]
  have hfactor : ∑ R ∈ C.powerset, p ^ (T.card + R.card) * (1 - p) ^ (C.card - R.card) =
      p ^ T.card * ∑ R ∈ C.powerset, p ^ R.card * (1 - p) ^ (C.card - R.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [pow_add, mul_assoc]
  rw [hfactor]
  -- Evaluate ∑_{R ⊆ C} p^|R| (1 - p)^(|C| - |R|) = (p + (1 - p))^|C| = 1 by induction on C!
  have hbinom : ∀ (A : Finset (Fin n)),
      ∑ R ∈ A.powerset, p ^ R.card * (1 - p) ^ (A.card - R.card) = 1 := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert a A ha ih =>
      rw [Finset.powerset_insert, Finset.sum_union]
      · have h1 : ∑ R ∈ A.powerset, p ^ R.card * (1 - p) ^ ((insert a A).card - R.card) =
            (1 - p) * ∑ R ∈ A.powerset, p ^ R.card * (1 - p) ^ (A.card - R.card) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun R hR => ?_
          have hle : R.card ≤ A.card := Finset.card_le_card (Finset.mem_powerset.mp hR)
          rw [Finset.card_insert_of_notMem ha]
          have hsub : A.card + 1 - R.card = (A.card - R.card) + 1 := by omega
          rw [hsub, pow_succ]; ring
        have h2 : ∑ R ∈ A.powerset.image (insert a), p ^ R.card * (1 - p) ^ ((insert a A).card - R.card) =
            p * ∑ R ∈ A.powerset, p ^ R.card * (1 - p) ^ (A.card - R.card) := by
          rw [Finset.sum_image, Finset.mul_sum]
          · refine Finset.sum_congr rfl fun R hR => ?_
            have haR : a ∉ R := fun h => ha (Finset.mem_powerset.mp hR h)
            rw [Finset.card_insert_of_notMem haR, Finset.card_insert_of_notMem ha,
              Nat.add_sub_add_right, pow_succ]
            ring
          · intro R₁ hR₁ R₂ hR₂ hEq
            have ha₁ : a ∉ R₁ := fun h => ha (Finset.mem_powerset.mp hR₁ h)
            have ha₂ : a ∉ R₂ := fun h => ha (Finset.mem_powerset.mp hR₂ h)
            have := congrArg (fun X => X.erase a) hEq
            simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using this
        rw [h1, h2, ih]; ring
      · rw [Finset.disjoint_left]
        intro R hR1 hR2
        rcases Finset.mem_image.mp hR2 with ⟨R', _, rfl⟩
        exact ha (Finset.mem_powerset.mp hR1 (Finset.mem_insert_self a R'))
  rw [hbinom C, mul_one]

/-- **Topology-Free Simple-Graph Crossing Lemma (`SlabWiring`):**
For any `W : SlabWiring n E` with `0 < n` and `4 * n ≤ E.card`,
`E.card ^ 3 / (64 * n ^ 2) ≤ W.crossings`. -/
theorem slabWiring_crossing_lemma {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W₀ : SlabWiring n E) (hn : 0 < n) (he : 4 * n ≤ E.card) :
    (E.card : ℝ) ^ 3 / (64 * (n : ℝ) ^ 2) ≤ (W₀.crossings : ℝ) := by
  classical
  -- First pass to a crossing-minimal SlabWiring W whose every inversion is vertex-disjoint!
  obtain ⟨W, hW_le, hdisj⟩ := exists_minimal_slabWiring_disjoint_inversions W₀
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have he_pos : (0 : ℝ) < (E.card : ℝ) := by
    have : 0 < E.card := by omega
    exact Nat.cast_pos.mpr this
  let p : ℝ := (4 * (n : ℝ)) / (E.card : ℝ)
  have hp_pos : 0 < p := by unfold p; positivity
  have hp_le1 : p ≤ 1 := by
    unfold p; rw [div_le_one he_pos]; exact_mod_cast he
  have h1mp_nn : 0 ≤ 1 - p := by linarith
  let wt : Finset (Fin n) → ℝ := fun S => p ^ S.card * (1 - p) ^ (n - S.card)
  have hwt_nn : ∀ S : Finset (Fin n), 0 ≤ wt S := fun S => by unfold wt; positivity
  -- Average the induced-subset linear crossing bound over all S ⊆ Fin n with weight wt S!
  let U := (Finset.univ : Finset (Fin n)).powerset
  have hpointwise : ∀ S ∈ U,
      wt S * ((E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) ≤
        wt S * (3 * (S.card : ℝ) +
          ∑ s : Fin (n + 1),
            (((invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
              (fun q => q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S)).card : ℝ)) := by
    intro S _
    refine mul_le_mul_of_nonneg_left ?_ (hwt_nn S)
    exact_mod_cast slabWiring_induced_subset W S
  have hsum_ineq :
      ∑ S ∈ U, wt S * ((E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) ≤
      ∑ S ∈ U, wt S * (3 * (S.card : ℝ)) +
      ∑ S ∈ U, wt S * ∑ s : Fin (n + 1),
        (((invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
          (fun q => q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S)).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun S hS => ?_
    rw [← mul_add]; exact hpointwise S hS
  -- Evaluate the 3 weighted expectations using sum_powerset_superset_weight!
  have hE_exp : ∑ S ∈ U, wt S * ((E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) =
      p ^ 2 * (E.card : ℝ) := by
    have h1 : ∀ S ∈ U, wt S * ((E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) =
        ∑ e ∈ E, if ({e.1, e.2} : Finset (Fin n)) ⊆ S then wt S else 0 := by
      intro S _
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hiff : (e.1 ∈ S ∧ e.2 ∈ S) ↔ ({e.1, e.2} : Finset (Fin n)) ⊆ S := by
        simp [Finset.insert_subset_iff]
      by_cases h : e.1 ∈ S ∧ e.2 ∈ S
      · rw [if_pos h, if_pos (hiff.mp h)]; simp
      · rw [if_neg h, if_neg (mt hiff.mpr h)]; simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ e ∈ E, (∑ S ∈ U, if ({e.1, e.2} : Finset (Fin n)) ⊆ S then wt S else 0) = p ^ 2 := by
      intro e he
      rw [← Finset.sum_filter]
      have hcard2 : ({e.1, e.2} : Finset (Fin n)).card = 2 :=
        Finset.card_pair (ne_of_lt (W.edge_lt e he))
      rw [← hcard2]
      exact sum_powerset_superset_weight ({e.1, e.2} : Finset (Fin n)) p
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hV_exp : ∑ S ∈ U, wt S * (3 * (S.card : ℝ)) = 3 * p * (n : ℝ) := by
    have h1 : ∀ S ∈ U, wt S * (3 * (S.card : ℝ)) =
        3 * ∑ i : Fin n, if ({i} : Finset (Fin n)) ⊆ S then wt S else 0 := by
      intro S _
      have hSc : (S.card : ℝ) = ∑ i : Fin n, if ({i} : Finset (Fin n)) ⊆ S then (1 : ℝ) else 0 := by
        have : ∑ i : Fin n, (if i ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 2; ext i; simp
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Finset.singleton_subset_iff]
      rw [hSc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
    have h2 : ∀ i : Fin n, (∑ S ∈ U, if ({i} : Finset (Fin n)) ⊆ S then wt S else 0) = p := by
      intro i
      rw [← Finset.sum_filter]
      have h := sum_powerset_superset_weight ({i} : Finset (Fin n)) p
      simpa only [U, wt, Finset.card_singleton, pow_one] using h
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hC_exp : ∑ S ∈ U, wt S * ∑ s : Fin (n + 1),
        (((invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
          (fun q => q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S)).card : ℝ) =
      p ^ 4 * (W.crossings : ℝ) := by
    have h1 : ∀ S ∈ U,
        wt S * ∑ s : Fin (n + 1),
          (((invPairs (activeEdges E s) (W.posL s) (W.posR s)).filter
            (fun q => q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S)).card : ℝ) =
        ∑ s : Fin (n + 1), ∑ q ∈ invPairs (activeEdges E s) (W.posL s) (W.posR s),
          if ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset (Fin n)) ⊆ S then wt S else 0 := by
      intro S _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hiff : (q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S) ↔
          ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset (Fin n)) ⊆ S := by
        simp [Finset.insert_subset_iff]
      by_cases h : q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S
      · rw [if_pos h, if_pos (hiff.mp h)]; simp
      · rw [if_neg h, if_neg (mt hiff.mpr h)]; simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    unfold SlabWiring.crossings
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    have h2 : ∀ q ∈ invPairs (activeEdges E s) (W.posL s) (W.posR s),
        (∑ S ∈ U, if ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset (Fin n)) ⊆ S then wt S else 0) = p ^ 4 := by
      intro q hq
      rw [← Finset.sum_filter]
      have hq1E : q.1 ∈ E := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1).1
      have hq2E : q.2 ∈ E := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2).1
      have h12 : q.1.1 ≠ q.1.2 := ne_of_lt (W.edge_lt q.1 hq1E)
      have h34 : q.2.1 ≠ q.2.2 := ne_of_lt (W.edge_lt q.2 hq2E)
      obtain ⟨h13, h24, h14, h23⟩ := hdisj s q.1 q.2 hq
      have hcard4 : ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset (Fin n)).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [h34]
        · simp [h23, h24]
        · simp [h12, h13, h14]
      rw [← hcard4]
      exact sum_powerset_superset_weight ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset (Fin n)) p
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hE_exp, hV_exp, hC_exp] at hsum_ineq
  -- Solve p² |E| ≤ 3 p n + p⁴ W.crossings with p = 4 n / |E|!
  have hstep : (E.card : ℝ) ^ 3 / (64 * (n : ℝ) ^ 2) ≤ (W.crossings : ℝ) := by
    have hp4_pos : 0 < p ^ 4 := pow_pos hp_pos 4
    have hdiv : (p ^ 2 * (E.card : ℝ) - 3 * p * (n : ℝ)) / p ^ 4 ≤ (W.crossings : ℝ) := by
      rw [div_le_iff₀ hp4_pos]; linarith
    have halg : (p ^ 2 * (E.card : ℝ) - 3 * p * (n : ℝ)) / p ^ 4 =
        (E.card : ℝ) ^ 3 / (64 * (n : ℝ) ^ 2) := by
      unfold p
      field_simp [ne_of_gt hn_pos, ne_of_gt he_pos]
      ring
    linarith
  exact le_trans hstep (Nat.cast_le.mpr hW_le)

/-- Unconditional version of the Simple-Graph Crossing Lemma (holds for ALL `E`, no `4n ≤ |E|` threshold!). -/
theorem slabWiring_crossing_lemma_uncond {n : ℕ} {E : Finset (Fin n × Fin n)}
    (W : SlabWiring n E) (hn : 0 < n) :
    (E.card : ℝ) ^ 3 / (64 * (n : ℝ) ^ 2) - (n : ℝ) ≤ (W.crossings : ℝ) := by
  by_cases he : 4 * n ≤ E.card
  · linarith [slabWiring_crossing_lemma W hn he, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · push Not at he
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have heR : (E.card : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast le_of_lt he
    have hcube : (E.card : ℝ) ^ 3 ≤ (4 * (n : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) heR 3
    have hdiv : (E.card : ℝ) ^ 3 / (64 * (n : ℝ) ^ 2) ≤ (n : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith [(Nat.cast_nonneg W.crossings : (0 : ℝ) ≤ W.crossings)]

/-! ### 3E. Sharp Linear-in-`μ` Multigraph Crossing Lemma & Continuous `x`-Monotone Curve Bridge -/

/-- Multigraph edges active on slab `s : Fin (n + 1)`. -/
def multiActiveEdges {n : ℕ} {ι : Type*} (I : Finset ι) (u v : ι → Fin n) (s : Fin (n + 1)) : Finset ι :=
  I.filter (fun e => (u e).val < s.val ∧ s.val ≤ (v e).val)

/-- Multigraph edges passing over/under vertex `k : Fin n`. -/
def multiPassingEdges {n : ℕ} {ι : Type*} (I : Finset ι) (u v : ι → Fin n) (k : Fin n) : Finset ι :=
  I.filter (fun e => (u e).val < k.val ∧ k.val < (v e).val)

/-- Multigraph edges ending at vertex `k : Fin n`. -/
def multiEndingEdges {n : ℕ} {ι : Type*} (I : Finset ι) (v : ι → Fin n) (k : Fin n) : Finset ι :=
  I.filter (fun e => v e = k)

/-- Multigraph edges starting at vertex `k : Fin n`. -/
def multiStartingEdges {n : ℕ} {ι : Type*} (I : Finset ι) (u : ι → Fin n) (k : Fin n) : Finset ι :=
  I.filter (fun e => u e = k)

/-- Topology-free combinatorial wiring diagram of a multigraph `(Fin n, I, u, v)`. -/
structure MultiSlabWiring (n : ℕ) {ι : Type*} (I : Finset ι) (u v : ι → Fin n) where
  edge_lt : ∀ e ∈ I, u e < v e
  posL : Fin (n + 1) → ι → ℝ
  posR : Fin (n + 1) → ι → ℝ
  posL_inj : ∀ s, Set.InjOn (posL s) (multiActiveEdges I u v s)
  posR_inj : ∀ s, Set.InjOn (posR s) (multiActiveEdges I u v s)
  above : Fin n → ι → Bool
  pass_order : ∀ (k : Fin n), ∀ e₁ ∈ multiPassingEdges I u v k, ∀ e₂ ∈ multiPassingEdges I u v k,
    posR k.castSucc e₁ < posR k.castSucc e₂ ↔ posL k.succ e₁ < posL k.succ e₂
  pass_above_end : ∀ (k : Fin n), ∀ e ∈ multiPassingEdges I u v k, ∀ e' ∈ multiEndingEdges I v k,
    if above k e then posR k.castSucc e' < posR k.castSucc e
    else posR k.castSucc e < posR k.castSucc e'
  pass_above_start : ∀ (k : Fin n), ∀ e ∈ multiPassingEdges I u v k, ∀ e' ∈ multiStartingEdges I u k,
    if above k e then posL k.succ e' < posL k.succ e
    else posL k.succ e < posL k.succ e'
  pass_below_lt_above : ∀ (k : Fin n), ∀ e₁ ∈ multiPassingEdges I u v k, ∀ e₂ ∈ multiPassingEdges I u v k,
    above k e₁ = false → above k e₂ = true → posR k.castSucc e₁ < posR k.castSucc e₂

/-- Total crossing (inversion) count of a `MultiSlabWiring`. -/
noncomputable def MultiSlabWiring.crossings {n : ℕ} {ι : Type*} {I : Finset ι} {u v : ι → Fin n}
    (M : MultiSlabWiring n I u v) : ℕ :=
  ∑ s : Fin (n + 1), (invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).card

/-- **Topology-Free Multigraph Crossing Lemma (Sharp Linear-in-`μ` Form):**
For any `MultiSlabWiring` of a multigraph on `n > 0` vertices with maximum edge multiplicity `≤ μ` (`μ > 0`),
`I.card ^ 3 / (64 * μ * n ^ 2) - μ ^ 2 * n ≤ M.crossings`. -/
theorem multigraph_slabWiring_crossing_lemma {n μ : ℕ} {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {u v : ι → Fin n} (M : MultiSlabWiring n I u v)
    (hn : 0 < n) (hμ : 0 < μ)
    (hmult : ∀ a b : Fin n, (I.filter (fun e => u e = a ∧ v e = b)).card ≤ μ) :
    (I.card : ℝ) ^ 3 / (64 * (μ : ℝ) * (n : ℝ) ^ 2) - (μ : ℝ) ^ 2 * (n : ℝ) ≤ (M.crossings : ℝ) := by
  classical
  by_cases hI_ne : I.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hI_ne
    subst hI_ne
    simp only [Finset.card_empty, Nat.cast_zero, zero_pow (by norm_num : 3 ≠ 0), zero_div, zero_sub]
    have : (0 : ℝ) ≤ (μ : ℝ) ^ 2 * (n : ℝ) := by positivity
    have : (0 : ℝ) ≤ (M.crossings : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨e_default, _⟩ := hI_ne
  -- Parallel classes P_pairs = {(u e, v e) | e ∈ I}.
  let P_pairs : Finset (Fin n × Fin n) := I.image (fun e => (u e, v e))
  let fiber : (Fin n × Fin n) → Finset ι := fun q => I.filter (fun e => (u e, v e) = q)
  have hfiber_le : ∀ q : Fin n × Fin n, (fiber q).card ≤ μ := fun q => by
    have : fiber q = I.filter (fun e => u e = q.1 ∧ v e = q.2) := by
      ext e; simp [fiber, Prod.ext_iff]
    rw [this]; exact hmult q.1 q.2
  -- Assign each e ∈ fiber q an injective slot idx q e : Fin μ!
  have hslot_ex : ∀ q : Fin n × Fin n, ∃ f : {e // e ∈ fiber q} → Fin μ, Function.Injective f := fun q => by
    have hcard : Fintype.card {e // e ∈ fiber q} ≤ Fintype.card (Fin μ) := by
      simpa using hfiber_le q
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
    exact ⟨emb, emb.injective⟩
  let slot : ∀ q : Fin n × Fin n, {e // e ∈ fiber q} → Fin μ := fun q => (hslot_ex q).choose
  have hslot_inj : ∀ q, Function.Injective (slot q) := fun q => (hslot_ex q).choose_spec
  -- Uniform finite product space Ω = Π q : {q // q ∈ P_pairs}, Fin μ!
  let Ω := ∀ _q : {q // q ∈ P_pairs}, Fin μ
  have hΩ_card : Fintype.card Ω = μ ^ P_pairs.card := by
    simp [Ω, Fintype.card_pi, Fintype.card_fin]
  have hΩ_pos : 0 < Fintype.card Ω := by rw [hΩ_card]; exact pow_pos hμ _
  have hΩ_posR : (0 : ℝ) < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr hΩ_pos
  have hμ_posR : (0 : ℝ) < (μ : ℝ) := Nat.cast_pos.mpr hμ
  -- For each ω : Ω, define the selected simple subgraph E_ω ⊆ P_pairs and unique edge rep_ω!
  let selected (ω : Ω) (e : ι) : Prop :=
    ∃ (hq : (u e, v e) ∈ P_pairs) (he : e ∈ fiber (u e, v e)), slot (u e, v e) ⟨e, he⟩ = ω ⟨(u e, v e), hq⟩
  let E_of (ω : Ω) : Finset (Fin n × Fin n) :=
    P_pairs.filter (fun q => ∃ e ∈ fiber q, selected ω e)
  have hunique_rep : ∀ (ω : Ω) (q : Fin n × Fin n), q ∈ E_of ω →
      ∃! e : ι, e ∈ fiber q ∧ selected ω e := by
    intro ω q hqE
    obtain ⟨hqP, e, hef, hsel⟩ := Finset.mem_filter.mp hqE
    refine ⟨e, ⟨hef, hsel⟩, ?_⟩
    rintro e' ⟨he'f, hsel'⟩
    have hq1 : (u e, v e) = q := (Finset.mem_filter.mp hef).2
    have hq2 : (u e', v e') = q := (Finset.mem_filter.mp he'f).2
    rcases hsel with ⟨hqP1, he1, hs1⟩
    rcases hsel' with ⟨hqP2, he2, hs2⟩
    have hsub_eq : (⟨e, hef⟩ : {x // x ∈ fiber q}) = ⟨e', he'f⟩ := by
      apply hslot_inj q
      have h1 : slot q ⟨e, hef⟩ = ω ⟨q, hqP⟩ := by
        cases hq1; exact hs1
      have h2 : slot q ⟨e', he'f⟩ = ω ⟨q, hqP⟩ := by
        cases hq2; exact hs2
      exact h1.trans h2.symm
    exact (congrArg Subtype.val hsub_eq).symm
  -- Build a simple SlabWiring n (E_of ω) for every ω : Ω!
  have hsimple_bound : ∀ ω : Ω,
      ((E_of ω).card : ℝ) ^ 3 / (64 * (n : ℝ) ^ 2) - (n : ℝ) ≤
        (∑ s : Fin (n + 1),
          ((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
            (fun p => selected ω p.1 ∧ selected ω p.2)).card : ℝ) := by
    intro ω
    -- Define rep : Fin n × Fin n → ι choosing the unique selected edge in fiber q when q ∈ E_of ω!
    let rep : Fin n × Fin n → ι := fun q =>
      if h : q ∈ E_of ω then (hunique_rep ω q h).choose else e_default
    have hrep_spec : ∀ q (hq : q ∈ E_of ω), rep q ∈ fiber q ∧ selected ω (rep q) := fun q hq => by
      simp only [rep, dif_pos hq]
      exact (hunique_rep ω q hq).choose_spec.1
    have hrep_I : ∀ q ∈ E_of ω, rep q ∈ I := fun q hq => (Finset.mem_filter.mp (hrep_spec q hq).1).1
    have hrep_uv : ∀ q ∈ E_of ω, u (rep q) = q.1 ∧ v (rep q) = q.2 := fun q hq =>
      Prod.mk.inj (Finset.mem_filter.mp (hrep_spec q hq).1).2
    have hrep_inj : Set.InjOn rep (E_of ω) := by
      intro q₁ h1 q₂ h2 hEq
      have hu1 := hrep_uv q₁ h1; have hu2 := hrep_uv q₂ h2
      rw [hEq] at hu1
      exact Prod.ext (hu1.1.symm.trans hu2.1) (hu1.2.symm.trans hu2.2)
    have hrep_act : ∀ s q, q ∈ activeEdges (E_of ω) s → rep q ∈ multiActiveEdges I u v s := by
      intro s q hq
      obtain ⟨hqE, h1, h2⟩ := Finset.mem_filter.mp hq
      have huv := hrep_uv q hqE
      exact Finset.mem_filter.mpr ⟨hrep_I q hqE, huv.1.symm ▸ h1, huv.2.symm ▸ h2⟩
    have hrep_pass : ∀ k q, q ∈ passingEdges (E_of ω) k → rep q ∈ multiPassingEdges I u v k := by
      intro k q hq
      obtain ⟨hqE, h1, h2⟩ := Finset.mem_filter.mp hq
      have huv := hrep_uv q hqE
      exact Finset.mem_filter.mpr ⟨hrep_I q hqE, huv.1.symm ▸ h1, huv.2.symm ▸ h2⟩
    have hrep_end : ∀ k q, q ∈ endingEdges (E_of ω) k → rep q ∈ multiEndingEdges I v k := by
      intro k q hq
      obtain ⟨hqE, h2⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hrep_I q hqE, (hrep_uv q hqE).2.trans h2⟩
    have hrep_start : ∀ k q, q ∈ startingEdges (E_of ω) k → rep q ∈ multiStartingEdges I u k := by
      intro k q hq
      obtain ⟨hqE, h1⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hrep_I q hqE, (hrep_uv q hqE).1.trans h1⟩
    let W_ω : SlabWiring n (E_of ω) :=
      { edge_lt := fun q hq => by
          have huv := hrep_uv q hq
          rw [← huv.1, ← huv.2]; exact M.edge_lt (rep q) (hrep_I q hq)
        posL := fun s q => M.posL s (rep q)
        posR := fun s q => M.posR s (rep q)
        posL_inj := fun s q₁ h1 q₂ h2 hEq =>
          hrep_inj (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
            (M.posL_inj s (hrep_act s q₁ h1) (hrep_act s q₂ h2) hEq)
        posR_inj := fun s q₁ h1 q₂ h2 hEq =>
          hrep_inj (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
            (M.posR_inj s (hrep_act s q₁ h1) (hrep_act s q₂ h2) hEq)
        above := fun k q => M.above k (rep q)
        pass_order := fun k q₁ h1 q₂ h2 =>
          M.pass_order k (rep q₁) (hrep_pass k q₁ h1) (rep q₂) (hrep_pass k q₂ h2)
        pass_above_end := fun k q hq q' hq' =>
          M.pass_above_end k (rep q) (hrep_pass k q hq) (rep q') (hrep_end k q' hq')
        pass_above_start := fun k q hq q' hq' =>
          M.pass_above_start k (rep q) (hrep_pass k q hq) (rep q') (hrep_start k q' hq')
        pass_below_lt_above := fun k q₁ h1 q₂ h2 =>
          M.pass_below_lt_above k (rep q₁) (hrep_pass k q₁ h1) (rep q₂) (hrep_pass k q₂ h2) }
    have hcr_le : W_ω.crossings ≤ ∑ s : Fin (n + 1),
        ((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
          (fun p => selected ω p.1 ∧ selected ω p.2)).card := by
      unfold SlabWiring.crossings
      refine Finset.sum_le_sum fun s _ => ?_
      have hinj : Set.InjOn (fun p : (Fin n × Fin n) × (Fin n × Fin n) => (rep p.1, rep p.2))
          (invPairs (activeEdges (E_of ω) s) (W_ω.posL s) (W_ω.posR s)) := by
        intro p₁ hp₁ p₂ hp₂ hEq
        have h1a := Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1
        have h2a := Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1
        exact Prod.ext
          (hrep_inj (Finset.mem_filter.mp h1a.1).1 (Finset.mem_filter.mp h2a.1).1 (congrArg Prod.fst hEq))
          (hrep_inj (Finset.mem_filter.mp h1a.2).1 (Finset.mem_filter.mp h2a.2).1 (congrArg Prod.snd hEq))
      rw [← Finset.card_image_of_injOn hinj]
      refine Finset.card_le_card ?_
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨⟨q₁, q₂⟩, hq, rfl⟩
      obtain ⟨hprod, hlt, hgt⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hprod
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hrep_act s q₁ hq1, hrep_act s q₂ hq2⟩, hlt, hgt⟩,
        (hrep_spec q₁ (Finset.mem_filter.mp hq1).1).2,
        (hrep_spec q₂ (Finset.mem_filter.mp hq2).1).2⟩
    have hcl := slabWiring_crossing_lemma_uncond W_ω hn
    have hcr_leR : (W_ω.crossings : ℝ) ≤
        (∑ s : Fin (n + 1),
          ((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
            (fun p => selected ω p.1 ∧ selected ω p.2)).card : ℝ) := by
      exact_mod_cast hcr_le
    linarith
  -- Counting lemmas on Ω = Π q : {q // q ∈ P_pairs}, Fin μ!
  have hcount_one : ∀ (q : {q // q ∈ P_pairs}) (val : Fin μ),
      ((Finset.univ : Finset Ω).filter (fun ω => ω q = val)).card * μ = Fintype.card Ω := by
    intro q val
    let A := (Finset.univ : Finset Ω).filter (fun ω => ω q = val)
    have hbij : (A ×ˢ (Finset.univ : Finset (Fin μ))).card = (Finset.univ : Finset Ω).card := by
      refine Finset.card_bij (fun p _ => Function.update p.1 q p.2) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro ⟨ω₁, c₁⟩ h1 ⟨ω₂, c₂⟩ h2 hEq
        have hc : c₁ = c₂ := by
          have := congrFun hEq q; simpa using this
        have hω : ω₁ = ω₂ := by
          funext q'
          by_cases hqq : q' = q
          · subst hqq
            exact ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2).trans
              ((Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2).symm
          · have := congrFun hEq q'; simpa [hqq] using this
        exact Prod.ext hω hc
      · intro ω _
        refine ⟨(Function.update ω q val, ω q), Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, Finset.mem_univ _⟩, ?_⟩
        funext q'
        by_cases hqq : q' = q
        · subst hqq; simp
        · simp [hqq]
    simpa [A, Finset.card_product, Fintype.card_fin] using hbij
  have hcount_two : ∀ (q₁ q₂ : {q // q ∈ P_pairs}) (hne : q₁ ≠ q₂) (v₁ v₂ : Fin μ),
      ((Finset.univ : Finset Ω).filter (fun ω => ω q₁ = v₁ ∧ ω q₂ = v₂)).card * (μ * μ) = Fintype.card Ω := by
    intro q₁ q₂ hne v₁ v₂
    let A := (Finset.univ : Finset Ω).filter (fun ω => ω q₁ = v₁ ∧ ω q₂ = v₂)
    have hbij : (A ×ˢ ((Finset.univ : Finset (Fin μ)) ×ˢ (Finset.univ : Finset (Fin μ)))).card =
        (Finset.univ : Finset Ω).card := by
      refine Finset.card_bij (fun p _ => Function.update (Function.update p.1 q₁ p.2.1) q₂ p.2.2) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro ⟨ω₁, c₁, d₁⟩ h1 ⟨ω₂, c₂, d₂⟩ h2 hEq
        have hd : d₁ = d₂ := by have := congrFun hEq q₂; simpa using this
        have hc : c₁ = c₂ := by have := congrFun hEq q₁; simpa [hne] using this
        have hω : ω₁ = ω₂ := by
          funext q'
          by_cases hq2 : q' = q₂
          · subst hq2
            exact ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.2).trans
              ((Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2.2).symm
          · by_cases hq1 : q' = q₁
            · subst hq1
              exact ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.1).trans
                ((Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2.1).symm
            · have := congrFun hEq q'; simpa [hq1, hq2] using this
        exact Prod.ext hω (Prod.ext hc hd)
      · intro ω _
        refine ⟨(Function.update (Function.update ω q₁ v₁) q₂ v₂, ω q₁, ω q₂),
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hne], by simp⟩,
            Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩, ?_⟩
        funext q'
        by_cases hq2 : q' = q₂
        · subst hq2; simp
        · by_cases hq1 : q' = q₁
          · subst hq1; simp [hne]
          · simp [hq1, hq2]
    simpa [A, Finset.card_product, Fintype.card_fin] using hbij
  -- Evaluate ∑ ω, (E_of ω).card = (|Ω| / μ) * |I|!
  have hsum_E : (∑ ω : Ω, ((E_of ω).card : ℝ)) * (μ : ℝ) = (Fintype.card Ω : ℝ) * (I.card : ℝ) := by
    have hcard_eq : ∀ ω : Ω, (E_of ω).card = (I.filter (fun e => selected ω e)).card := by
      intro ω
      refine Finset.card_bij (fun q hq => (hunique_rep ω q hq).choose) ?_ ?_ ?_
      · intro q hq
        have hspec := (hunique_rep ω q hq).choose_spec.1
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hspec.1).1, hspec.2⟩
      · intro q₁ h1 q₂ h2 hEq
        have hs1 := (Finset.mem_filter.mp (hunique_rep ω q₁ h1).choose_spec.1.1).2
        have hs2 := (Finset.mem_filter.mp (hunique_rep ω q₂ h2).choose_spec.1.1).2
        rw [hEq] at hs1; exact hs1.symm.trans hs2
      · intro e he
        obtain ⟨heI, hsel⟩ := Finset.mem_filter.mp he
        have hqP : (u e, v e) ∈ P_pairs := Finset.mem_image_of_mem _ heI
        have hef : e ∈ fiber (u e, v e) := Finset.mem_filter.mpr ⟨heI, rfl⟩
        have hqE : (u e, v e) ∈ E_of ω := Finset.mem_filter.mpr ⟨hqP, e, hef, hsel⟩
        refine ⟨(u e, v e), hqE, ?_⟩
        exact ((hunique_rep ω (u e, v e) hqE).choose_spec.2 e ⟨hef, hsel⟩).symm
    have hnat : (∑ ω : Ω, (E_of ω).card) * μ = Fintype.card Ω * I.card := by
      calc (∑ ω : Ω, (E_of ω).card) * μ
          = (∑ ω : Ω, (I.filter (fun e => selected ω e)).card) * μ := by
            simp only [hcard_eq]
        _ = (∑ e ∈ I, ((Finset.univ : Finset Ω).filter (fun ω => selected ω e)).card) * μ := by
            congr 1; simp only [Finset.card_filter]; rw [Finset.sum_comm]
        _ = ∑ e ∈ I, ((Finset.univ : Finset Ω).filter (fun ω => selected ω e)).card * μ :=
            Finset.sum_mul _ _ _
        _ = ∑ _e ∈ I, Fintype.card Ω := by
            refine Finset.sum_congr rfl fun e heI => ?_
            have hqP : (u e, v e) ∈ P_pairs := Finset.mem_image_of_mem _ heI
            have hef : e ∈ fiber (u e, v e) := Finset.mem_filter.mpr ⟨heI, rfl⟩
            have hfilt : (Finset.univ : Finset Ω).filter (fun ω => selected ω e) =
                (Finset.univ : Finset Ω).filter (fun ω => ω ⟨(u e, v e), hqP⟩ = slot (u e, v e) ⟨e, hef⟩) := by
              ext ω
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, selected]
              constructor
              · rintro ⟨_, _, h⟩; exact h.symm
              · intro h; exact ⟨hqP, hef, h.symm⟩
            rw [hfilt]
            exact hcount_one ⟨(u e, v e), hqP⟩ (slot (u e, v e) ⟨e, hef⟩)
        _ = Fintype.card Ω * I.card := by simp [mul_comm]
    exact_mod_cast hnat
  -- Evaluate ∑ ω, cr(ω) * μ² ≤ |Ω| * M.crossings!
  have hsum_C : (∑ ω : Ω, ∑ s : Fin (n + 1),
        (((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
          (fun p => selected ω p.1 ∧ selected ω p.2)).card : ℝ)) * ((μ : ℝ) ^ 2) ≤
      (Fintype.card Ω : ℝ) * (M.crossings : ℝ) := by
    have hnat : (∑ ω : Ω, ∑ s : Fin (n + 1),
          ((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
            (fun p => selected ω p.1 ∧ selected ω p.2)).card) * (μ * μ) ≤
        Fintype.card Ω * M.crossings := by
      rw [Finset.sum_comm]
      unfold MultiSlabWiring.crossings
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hcomm : ∑ ω : Ω, ((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
            (fun p => selected ω p.1 ∧ selected ω p.2)).card =
          ∑ p ∈ invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s),
            ((Finset.univ : Finset Ω).filter (fun ω => selected ω p.1 ∧ selected ω p.2)).card := by
        simp only [Finset.card_filter]; rw [Finset.sum_comm]
      rw [hcomm, Finset.sum_mul]
      calc ∑ p ∈ invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s),
              ((Finset.univ : Finset Ω).filter (fun ω => selected ω p.1 ∧ selected ω p.2)).card * (μ * μ)
          ≤ ∑ _p ∈ invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s), Fintype.card Ω := by
            refine Finset.sum_le_sum fun ⟨e₁, e₂⟩ hp => ?_
            have hmem := Finset.mem_filter.mp hp
            have h1I : e₁ ∈ I := (Finset.mem_filter.mp (Finset.mem_product.mp hmem.1).1).1
            have h2I : e₂ ∈ I := (Finset.mem_filter.mp (Finset.mem_product.mp hmem.1).2).1
            have hne12 : e₁ ≠ e₂ := fun heq => lt_irrefl _ (heq ▸ hmem.2.1)
            by_cases hsame : (u e₁, v e₁) = (u e₂, v e₂)
            · -- Parallel edges can NEVER both be selected!
              have hemp : (Finset.univ : Finset Ω).filter (fun ω => selected ω e₁ ∧ selected ω e₂) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                rintro ω _ ⟨⟨hq1, hf1, hs1⟩, ⟨hq2, hf2, hs2⟩⟩
                have hs_eq : slot (u e₂, v e₂) ⟨e₁, hsame ▸ hf1⟩ = slot (u e₂, v e₂) ⟨e₂, hf2⟩ := by
                  have hgen : ∀ (q₁ q₂ : Fin n × Fin n) (hq : q₁ = q₂)
                      (h1p : q₁ ∈ P_pairs) (h2p : q₂ ∈ P_pairs)
                      (h1f : e₁ ∈ fiber q₁) (h2f : e₂ ∈ fiber q₂),
                      slot q₁ ⟨e₁, h1f⟩ = ω ⟨q₁, h1p⟩ → slot q₂ ⟨e₂, h2f⟩ = ω ⟨q₂, h2p⟩ →
                      slot q₂ ⟨e₁, hq ▸ h1f⟩ = slot q₂ ⟨e₂, h2f⟩ := by
                    rintro q₁ q₂ rfl h1p h2p h1f h2f h1s h2s
                    exact h1s.trans h2s.symm
                  exact hgen (u e₁, v e₁) (u e₂, v e₂) hsame hq1 hq2 hf1 hf2 hs1 hs2
                have hsub_eq := hslot_inj (u e₂, v e₂) hs_eq
                exact hne12 (congrArg Subtype.val hsub_eq)
              rw [hemp]; simp
            · have hq1P : (u e₁, v e₁) ∈ P_pairs := Finset.mem_image_of_mem _ h1I
              have hq2P : (u e₂, v e₂) ∈ P_pairs := Finset.mem_image_of_mem _ h2I
              have hf1 : e₁ ∈ fiber (u e₁, v e₁) := Finset.mem_filter.mpr ⟨h1I, rfl⟩
              have hf2 : e₂ ∈ fiber (u e₂, v e₂) := Finset.mem_filter.mpr ⟨h2I, rfl⟩
              have hfilt : (Finset.univ : Finset Ω).filter (fun ω => selected ω e₁ ∧ selected ω e₂) =
                  (Finset.univ : Finset Ω).filter (fun ω =>
                    ω ⟨(u e₁, v e₁), hq1P⟩ = slot (u e₁, v e₁) ⟨e₁, hf1⟩ ∧
                    ω ⟨(u e₂, v e₂), hq2P⟩ = slot (u e₂, v e₂) ⟨e₂, hf2⟩) := by
                ext ω
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, selected]
                constructor
                · rintro ⟨⟨_, _, hs1⟩, ⟨_, _, hs2⟩⟩; exact ⟨hs1.symm, hs2.symm⟩
                · rintro ⟨h1, h2⟩; exact ⟨⟨hq1P, hf1, h1.symm⟩, ⟨hq2P, hf2, h2.symm⟩⟩
              rw [hfilt]
              have hqne : (⟨(u e₁, v e₁), hq1P⟩ : {q // q ∈ P_pairs}) ≠ ⟨(u e₂, v e₂), hq2P⟩ :=
                fun h => hsame (congrArg Subtype.val h)
              exact le_of_eq (hcount_two _ _ hqne _ _)
        _ = Fintype.card Ω * (invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).card := by
            simp [mul_comm]
    have hnatR : ((∑ ω : Ω, ∑ s : Fin (n + 1),
          ((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
            (fun p => selected ω p.1 ∧ selected ω p.2)).card : ℕ) : ℝ) * ((μ : ℝ) * (μ : ℝ)) ≤
        (Fintype.card Ω : ℝ) * (M.crossings : ℝ) := by
      exact_mod_cast hnat
    simpa [pow_two, Nat.cast_sum] using hnatR
  -- Apply Jensen's inequality on x ↦ x³ over [0, ∞) to average hsimple_bound over ω : Ω!
  have hjensen : ((∑ ω : Ω, ((E_of ω).card : ℝ)) / (Fintype.card Ω : ℝ)) ^ 3 ≤
      (∑ ω : Ω, ((E_of ω).card : ℝ) ^ 3) / (Fintype.card Ω : ℝ) := by
    have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ 3) := by
      refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
      simp only [Set.mem_Ici] at hx hy
      simp only [smul_eq_mul]
      have hident : a * x ^ 3 + b * y ^ 3 - (a * x + b * y) ^ 3 =
          a * b * (x - y) ^ 2 * ((a + 1) * x + (b + 1) * y) := by
        have hb' : b = 1 - a := by linarith
        rw [hb']; ring
      have hnn : 0 ≤ a * b * (x - y) ^ 2 * ((a + 1) * x + (b + 1) * y) := by positivity
      linarith
    have h := hconv.map_sum_le (t := Finset.univ)
      (w := fun _ : Ω => (1 : ℝ) / (Fintype.card Ω : ℝ))
      (p := fun ω : Ω => ((E_of ω).card : ℝ))
      (fun _ _ => by positivity)
      (by simp [Finset.sum_const, nsmul_eq_mul, ne_of_gt hΩ_posR])
      (fun ω _ => Set.mem_Ici.mpr (Nat.cast_nonneg _))
    simp only [smul_eq_mul, ← Finset.mul_sum] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  have havg_E : (∑ ω : Ω, ((E_of ω).card : ℝ)) / (Fintype.card Ω : ℝ) = (I.card : ℝ) / (μ : ℝ) := by
    rw [div_eq_div_iff (ne_of_gt hΩ_posR) (ne_of_gt hμ_posR)]
    exact hsum_E.trans (mul_comm _ _)
  rw [havg_E] at hjensen
  have hsum_all :
      (∑ ω : Ω, ((E_of ω).card : ℝ) ^ 3) / (64 * (n : ℝ) ^ 2) - (Fintype.card Ω : ℝ) * (n : ℝ) ≤
      ∑ ω : Ω, ∑ s : Fin (n + 1),
        (((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
          (fun p => selected ω p.1 ∧ selected ω p.2)).card : ℝ) := by
    have h := Finset.sum_le_sum fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) => hsimple_bound ω
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    exact h
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hstep1 : ((I.card : ℝ) / (μ : ℝ)) ^ 3 / (64 * (n : ℝ) ^ 2) - (n : ℝ) ≤
      (M.crossings : ℝ) / (μ : ℝ) ^ 2 := by
    have h1 : (Fintype.card Ω : ℝ) * ((I.card : ℝ) / (μ : ℝ)) ^ 3 ≤
        ∑ ω : Ω, ((E_of ω).card : ℝ) ^ 3 := by
      rwa [le_div_iff₀ hΩ_posR, mul_comm] at hjensen
    have h2 : (Fintype.card Ω : ℝ) * (((I.card : ℝ) / (μ : ℝ)) ^ 3 / (64 * (n : ℝ) ^ 2) - (n : ℝ)) ≤
        (Fintype.card Ω : ℝ) * ((M.crossings : ℝ) / (μ : ℝ) ^ 2) := by
      have h3 : (∑ ω : Ω, ∑ s : Fin (n + 1),
          (((invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s)).filter
            (fun p => selected ω p.1 ∧ selected ω p.2)).card : ℝ)) ≤
          (Fintype.card Ω : ℝ) * ((M.crossings : ℝ) / (μ : ℝ) ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (pow_pos hμ_posR 2)]
        exact hsum_C
      have h4 : (Fintype.card Ω : ℝ) * ((I.card : ℝ) / (μ : ℝ)) ^ 3 / (64 * (n : ℝ) ^ 2) ≤
          (∑ ω : Ω, ((E_of ω).card : ℝ) ^ 3) / (64 * (n : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have hdist : (Fintype.card Ω : ℝ) * (((I.card : ℝ) / (μ : ℝ)) ^ 3 / (64 * (n : ℝ) ^ 2) - (n : ℝ)) =
          (Fintype.card Ω : ℝ) * ((I.card : ℝ) / (μ : ℝ)) ^ 3 / (64 * (n : ℝ) ^ 2) -
          (Fintype.card Ω : ℝ) * (n : ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left h2 hΩ_posR
  have hmul := mul_le_mul_of_nonneg_right hstep1 (sq_nonneg (μ : ℝ))
  have halg1 : (((I.card : ℝ) / (μ : ℝ)) ^ 3 / (64 * (n : ℝ) ^ 2) - (n : ℝ)) * (μ : ℝ) ^ 2 =
      (I.card : ℝ) ^ 3 / (64 * (μ : ℝ) * (n : ℝ) ^ 2) - (μ : ℝ) ^ 2 * (n : ℝ) := by
    field_simp [ne_of_gt hμ_posR, ne_of_gt hn_posR]
  have halg2 : (M.crossings : ℝ) / (μ : ℝ) ^ 2 * (μ : ℝ) ^ 2 = (M.crossings : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt (pow_pos hμ_posR 2))
  linarith

/-- Thresholded Multigraph Crossing Lemma: if `8 * μ * n ≤ |I|`, then `|I|³ / (80 μ n²) ≤ M.crossings`. -/
theorem multigraph_slabWiring_crossing_lemma_threshold {n μ : ℕ} {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {u v : ι → Fin n} (M : MultiSlabWiring n I u v)
    (hn : 0 < n) (hμ : 0 < μ)
    (hmult : ∀ a b : Fin n, (I.filter (fun e => u e = a ∧ v e = b)).card ≤ μ)
    (he : 8 * μ * n ≤ I.card) :
    (I.card : ℝ) ^ 3 / (80 * (μ : ℝ) * (n : ℝ) ^ 2) ≤ (M.crossings : ℝ) := by
  have hbase := multigraph_slabWiring_crossing_lemma M hn hμ hmult
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hμR : (0 : ℝ) < (μ : ℝ) := Nat.cast_pos.mpr hμ
  have heR : 8 * (μ : ℝ) * (n : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast he
  have hcube : (8 * (μ : ℝ) * (n : ℝ)) ^ 3 ≤ (I.card : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) heR 3
  have hsub : (μ : ℝ) ^ 2 * (n : ℝ) ≤ (I.card : ℝ) ^ 3 / (512 * (μ : ℝ) * (n : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hdiff : (I.card : ℝ) ^ 3 / (80 * (μ : ℝ) * (n : ℝ) ^ 2) ≤
      (I.card : ℝ) ^ 3 / (64 * (μ : ℝ) * (n : ℝ) ^ 2) - (I.card : ℝ) ^ 3 / (512 * (μ : ℝ) * (n : ℝ) ^ 2) := by
    have hpos : (0 : ℝ) < (μ : ℝ) * (n : ℝ) ^ 2 := by positivity
    have hnum : (0 : ℝ) ≤ (I.card : ℝ) ^ 3 := by positivity
    have hcoeff : (1 : ℝ) / 80 ≤ 1 / 64 - 1 / 512 := by norm_num
    have h1 : (I.card : ℝ) ^ 3 / (80 * (μ : ℝ) * (n : ℝ) ^ 2) =
        (1 / 80) * ((I.card : ℝ) ^ 3 / ((μ : ℝ) * (n : ℝ) ^ 2)) := by ring
    have h2 : (I.card : ℝ) ^ 3 / (64 * (μ : ℝ) * (n : ℝ) ^ 2) -
        (I.card : ℝ) ^ 3 / (512 * (μ : ℝ) * (n : ℝ) ^ 2) =
        (1 / 64 - 1 / 512) * ((I.card : ℝ) ^ 3 / ((μ : ℝ) * (n : ℝ) ^ 2)) := by ring
    have h3 := mul_le_mul_of_nonneg_right hcoeff (div_nonneg hnum (le_of_lt hpos))
    linarith
  linarith

/-- **Continuous `x`-Monotone Curve Bridge to `MultiSlabWiring`:**
Any finite family of continuous `x`-monotone curves `γ e : [x (u e), x (v e)] → ℝ` avoiding
non-endpoint vertices and having finitely many pairwise interior intersections `X_int` induces a
valid `MultiSlabWiring` whose every inversion corresponds to a geometric interior intersection
point `t ∈ X_int` inside that open slab `(x (s-1) + ε, x s - ε)`. -/
theorem xMonotone_multi_to_slabWiring {n : ℕ} {ι : Type*} [DecidableEq ι]
    (x y : Fin n → ℝ) (hx : StrictMono x)
    (I : Finset ι) (u v : ι → Fin n) (huv : ∀ e ∈ I, u e < v e)
    (γ : ι → ℝ → ℝ)
    (hcont : ∀ e ∈ I, ContinuousOn (γ e) (Set.Icc (x (u e)) (x (v e))))
    (hleft : ∀ e ∈ I, γ e (x (u e)) = y (u e))
    (hright : ∀ e ∈ I, γ e (x (v e)) = y (v e))
    (hno_hit : ∀ e ∈ I, ∀ k : Fin n, u e < k → k < v e → γ e (x k) ≠ y k)
    (X_int : Finset ℝ)
    (hX : ∀ e₁ ∈ I, ∀ e₂ ∈ I, e₁ ≠ e₂ → ∀ t : ℝ,
      x (max (u e₁) (u e₂)) < t → t < x (min (v e₁) (v e₂)) → γ e₁ t = γ e₂ t → t ∈ X_int)
    (hX_disj : ∀ k : Fin n, x k ∉ X_int) :
    ∃ (M : MultiSlabWiring n I u v) (ε : ℝ),
      0 < ε ∧
      (∀ (k : Fin n) (hk : k.val + 1 < n), x k + ε < x ⟨k.val + 1, hk⟩ - ε) ∧
      (∀ (s : Fin (n + 1)) (e₁ e₂ : ι),
        (e₁, e₂) ∈ invPairs (multiActiveEdges I u v s) (M.posL s) (M.posR s) →
        ∃ (h1 : 0 < s.val) (h2 : s.val < n) (t : ℝ),
          x ⟨s.val - 1, by omega⟩ + ε < t ∧ t < x ⟨s.val, h2⟩ - ε ∧
          γ e₁ t = γ e₂ t ∧ t ∈ X_int) := by
  classical
  -- Choose ε > 0 strictly smaller than:
  -- (1) (x (k+1) - x k) / 3 for all adjacent vertices,
  -- (2) |t - x k| for all k : Fin n and t ∈ X_int with t ≠ x k,
  -- (3) small enough that for every passing edge e at vertex k, γ e stays on the same side of y k
  --     AND for every ending/starting edge e' at k, γ e' stays strictly closer to y k than γ e does!
  -- Wait: for (3), by continuity of (γ e - γ e') at x k (where it equals γ e (x k) - y k ≠ 0!),
  -- there exists δ(k, e, e') > 0 such that on [x k - δ, x k] (or [x k, x k + δ]) γ e - γ e' has the same sign as at x k!
  have hδ_end : ∀ (k : Fin n) (e : ι) (e' : ι),
      e ∈ multiPassingEdges I u v k → e' ∈ multiEndingEdges I v k →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (x k - δ) (x k),
        (y k < γ e (x k) → γ e' t < γ e t) ∧ (γ e (x k) < y k → γ e t < γ e' t) := by
    intro k e e' he he'
    obtain ⟨heI, h1, h2⟩ := Finset.mem_filter.mp he
    obtain ⟨he'I, he'v⟩ := Finset.mem_filter.mp he'
    have hne : γ e (x k) ≠ y k := hno_hit e heI k h1 h2
    have he'_lt : u e' < k := he'v ▸ huv e' he'I
    have hx_lo : max (x (u e)) (x (u e')) < x k := max_lt (hx h1) (hx he'_lt)
    have hce : ContinuousWithinAt (γ e) (Set.Icc (x (u e)) (x (v e))) (x k) :=
      hcont e heI (x k) ⟨le_of_lt (hx h1), le_of_lt (hx h2)⟩
    have hce' : ContinuousWithinAt (γ e') (Set.Icc (x (u e')) (x (v e'))) (x k) :=
      hcont e' he'I (x k) ⟨le_of_lt (hx he'_lt), by rw [he'v]⟩
    have hdiff : ContinuousWithinAt (fun t => γ e t - γ e' t) (Set.Icc (max (x (u e)) (x (u e'))) (x k)) (x k) := by
      refine ContinuousWithinAt.sub ?_ ?_
      · exact hce.mono (fun t ht => ⟨le_trans (le_max_left _ _) ht.1, le_trans ht.2 (le_of_lt (hx h2))⟩)
      · exact hce'.mono (fun t ht => ⟨le_trans (le_max_right _ _) ht.1, by rw [he'v]; exact ht.2⟩)
    have hval : γ e (x k) - γ e' (x k) = γ e (x k) - y k := by rw [← he'v, hright e' he'I]
    have hgap : 0 < |γ e (x k) - y k| := abs_pos.mpr (sub_ne_zero.mpr hne)
    rw [Metric.continuousWithinAt_iff] at hdiff
    obtain ⟨δ₁, hδ₁, hclose⟩ := hdiff (|γ e (x k) - y k|) hgap
    let δ := min (δ₁ / 2) ((x k - max (x (u e)) (x (u e'))) / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    refine ⟨δ, hδ_pos, fun t ht => ?_⟩
    have ht_in : t ∈ Set.Icc (max (x (u e)) (x (u e'))) (x k) :=
      ⟨by have : δ ≤ (x k - max (x (u e)) (x (u e'))) / 2 := min_le_right _ _; linarith [ht.1], ht.2⟩
    have hdist : dist t (x k) < δ₁ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]
      have : δ ≤ δ₁ / 2 := min_le_left _ _
      linarith [ht.1]
    have hc := hclose ht_in hdist
    rw [Real.dist_eq, hval] at hc
    have hc' := abs_lt.mp hc
    constructor
    · intro hlt
      rw [abs_of_pos (by linarith)] at hc'
      linarith
    · intro hgt
      rw [abs_of_neg (by linarith)] at hc'
      linarith
  have hδ_start : ∀ (k : Fin n) (e : ι) (e' : ι),
      e ∈ multiPassingEdges I u v k → e' ∈ multiStartingEdges I u k →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (x k) (x k + δ),
        (y k < γ e (x k) → γ e' t < γ e t) ∧ (γ e (x k) < y k → γ e t < γ e' t) := by
    intro k e e' he he'
    obtain ⟨heI, h1, h2⟩ := Finset.mem_filter.mp he
    obtain ⟨he'I, he'u⟩ := Finset.mem_filter.mp he'
    have hne : γ e (x k) ≠ y k := hno_hit e heI k h1 h2
    have he'_gt : k < v e' := he'u ▸ huv e' he'I
    have hx_hi : x k < min (x (v e)) (x (v e')) := lt_min (hx h2) (hx he'_gt)
    have hce : ContinuousWithinAt (γ e) (Set.Icc (x (u e)) (x (v e))) (x k) :=
      hcont e heI (x k) ⟨le_of_lt (hx h1), le_of_lt (hx h2)⟩
    have hce' : ContinuousWithinAt (γ e') (Set.Icc (x (u e')) (x (v e'))) (x k) :=
      hcont e' he'I (x k) ⟨by rw [he'u], le_of_lt (hx he'_gt)⟩
    have hdiff : ContinuousWithinAt (fun t => γ e t - γ e' t) (Set.Icc (x k) (min (x (v e)) (x (v e')))) (x k) := by
      refine ContinuousWithinAt.sub ?_ ?_
      · exact hce.mono (fun t ht => ⟨le_trans (le_of_lt (hx h1)) ht.1, le_trans ht.2 (min_le_left _ _)⟩)
      · exact hce'.mono (fun t ht => ⟨by rw [he'u]; exact ht.1, le_trans ht.2 (min_le_right _ _)⟩)
    have hval : γ e (x k) - γ e' (x k) = γ e (x k) - y k := by rw [← he'u, hleft e' he'I]
    have hgap : 0 < |γ e (x k) - y k| := abs_pos.mpr (sub_ne_zero.mpr hne)
    rw [Metric.continuousWithinAt_iff] at hdiff
    obtain ⟨δ₁, hδ₁, hclose⟩ := hdiff (|γ e (x k) - y k|) hgap
    let δ := min (δ₁ / 2) ((min (x (v e)) (x (v e')) - x k) / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    refine ⟨δ, hδ_pos, fun t ht => ?_⟩
    have ht_in : t ∈ Set.Icc (x k) (min (x (v e)) (x (v e'))) :=
      ⟨ht.1, by have : δ ≤ (min (x (v e)) (x (v e')) - x k) / 2 := min_le_right _ _; linarith [ht.2]⟩
    have hdist : dist t (x k) < δ₁ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
      have : δ ≤ δ₁ / 2 := min_le_left _ _
      linarith [ht.2]
    have hc := hclose ht_in hdist
    rw [Real.dist_eq, hval] at hc
    have hc' := abs_lt.mp hc
    constructor
    · intro hlt
      rw [abs_of_pos (by linarith)] at hc'
      linarith
    · intro hgt
      rw [abs_of_neg (by linarith)] at hc'
      linarith
  -- Also ensure passing edges strictly below y k stay strictly below passing edges strictly above y k near x k,
  -- AND any two distinct passing edges stay strictly separated at x k if γ e₁ (x k) ≠ γ e₂ (x k)!
  -- Collect finitely many positive real constraints into a single Finset ℝ, take half its minimum!
  let adjGaps : Finset ℝ :=
    ((Finset.univ : Finset (Fin n)).filter (fun k => k.val + 1 < n)).image
      (fun k => if hk : k.val + 1 < n then (x ⟨k.val + 1, hk⟩ - x k) / 3 else 1)
  let intGaps : Finset ℝ :=
    (((Finset.univ : Finset (Fin n)) ×ˢ X_int).filter (fun p => p.2 ≠ x p.1)).image
      (fun p => |p.2 - x p.1|)
  let endGaps : Finset ℝ :=
    ((Finset.univ : Finset (Fin n)) ×ˢ (I ×ˢ I)).image fun p =>
      if h : p.2.1 ∈ multiPassingEdges I u v p.1 ∧ p.2.2 ∈ multiEndingEdges I v p.1 then
        (hδ_end p.1 p.2.1 p.2.2 h.1 h.2).choose
      else 1
  let startGaps : Finset ℝ :=
    ((Finset.univ : Finset (Fin n)) ×ˢ (I ×ˢ I)).image fun p =>
      if h : p.2.1 ∈ multiPassingEdges I u v p.1 ∧ p.2.2 ∈ multiStartingEdges I u p.1 then
        (hδ_start p.1 p.2.1 p.2.2 h.1 h.2).choose
      else 1
  let allGaps : Finset ℝ := {1} ∪ adjGaps ∪ intGaps ∪ endGaps ∪ startGaps
  have hall_ne : allGaps.Nonempty := ⟨1, by simp [allGaps]⟩
  have hall_pos : ∀ r ∈ allGaps, 0 < r := by
    intro r hr
    simp only [allGaps, Finset.mem_union, Finset.mem_singleton] at hr
    rcases hr with (((rfl | h1) | h2) | h3) | h4
    · norm_num
    · rcases Finset.mem_image.mp h1 with ⟨k, hk, rfl⟩
      have hk' : k.val + 1 < n := (Finset.mem_filter.mp hk).2
      rw [dif_pos hk']
      have hlt : x k < x ⟨k.val + 1, hk'⟩ := hx (show k < ⟨k.val + 1, hk'⟩ by change k.val < k.val + 1; omega)
      linarith
    · rcases Finset.mem_image.mp h2 with ⟨p, hp, rfl⟩
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
    · rcases Finset.mem_image.mp h3 with ⟨p, _, rfl⟩
      split_ifs with h
      · exact (hδ_end p.1 p.2.1 p.2.2 h.1 h.2).choose_spec.1
      · norm_num
    · rcases Finset.mem_image.mp h4 with ⟨p, _, rfl⟩
      split_ifs with h
      · exact (hδ_start p.1 p.2.1 p.2.2 h.1 h.2).choose_spec.1
      · norm_num
  let mGap := allGaps.min' hall_ne
  have hmGap_pos : 0 < mGap := hall_pos mGap (Finset.min'_mem allGaps hall_ne)
  let ε : ℝ := mGap / 2
  have hε_pos : 0 < ε := by unfold ε; linarith
  have hε_lt : ∀ r ∈ allGaps, ε < r := fun r hr => by
    have hle : mGap ≤ r := Finset.min'_le allGaps r hr
    unfold ε; linarith
  have hε_adj : ∀ (k : Fin n) (hk : k.val + 1 < n), x k + ε < x ⟨k.val + 1, hk⟩ - ε := by
    intro k hk
    have hmem : (x ⟨k.val + 1, hk⟩ - x k) / 3 ∈ allGaps := by
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ ?_)))
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, by rw [dif_pos hk]⟩
    have := hε_lt _ hmem
    linarith
  have hε_no_int : ∀ (k : Fin n) (t : ℝ), t ∈ X_int → t ≠ x k → ε < |t - x k| := by
    intro k t ht hne
    have hmem : |t - x k| ∈ allGaps := by
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
      exact Finset.mem_image.mpr ⟨(k, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩, hne⟩, rfl⟩
    exact hε_lt _ hmem
  -- Define posL and posR on each slab s : Fin (n + 1)!
  let posL_γ : Fin (n + 1) → ι → ℝ := fun s e =>
    if h : 0 < s.val ∧ s.val < n then γ e (x ⟨s.val - 1, by omega⟩ + ε) else 0
  let posR_γ : Fin (n + 1) → ι → ℝ := fun s e =>
    if h : 0 < s.val ∧ s.val < n then γ e (x ⟨s.val, h.2⟩ - ε) else 0
  let above_γ : Fin n → ι → Bool := fun k e => decide (y k < γ e (x k))
  -- Key separation lemma: no two distinct edges agree at ANY t with |t - x k| ≤ ε (including t = x k)!
  have hno_eq_near : ∀ (k : Fin n) (e₁ e₂ : ι) (h1I : e₁ ∈ I) (h2I : e₂ ∈ I) (hne : e₁ ≠ e₂) (t : ℝ),
      x (max (u e₁) (u e₂)) < t → t < x (min (v e₁) (v e₂)) →
      |t - x k| ≤ ε → γ e₁ t ≠ γ e₂ t := by
    intro k e₁ e₂ h1I h2I hne t ht1 ht2 hdist heq
    have htX : t ∈ X_int := hX e₁ h1I e₂ h2I hne t ht1 ht2 heq
    have htk : t ≠ x k := fun h => hX_disj k (h ▸ htX)
    have := hε_no_int k t htX htk
    linarith
  -- Auxiliary: if f is continuous on [a, b] and f a < 0 < f b, there is a root in (a, b).
  have hivt : ∀ (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
      (ha : f a < 0) (hb : 0 < f b), ∃ t ∈ Set.Ioo a b, f t = 0 := by
    intro f a b hab hf ha hb
    have h0 : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
    obtain ⟨t, htIcc, hft⟩ := intermediate_value_Icc hab hf h0
    refine ⟨t, ⟨lt_of_le_of_ne htIcc.1 ?_, lt_of_le_of_ne htIcc.2 ?_⟩, hft⟩
    · intro hEq; subst hEq; linarith
    · intro hEq; subst hEq; linarith
  -- Auxiliary: for k < v, x k + ε < x v; for u < k, x u < x k - ε.
  have hε_lt_right : ∀ (k v' : Fin n), k < v' → x k + ε < x v' := by
    intro k v' hkv
    have hk1 : k.val + 1 < n := by have := v'.isLt; omega
    have h1 := hε_adj k hk1
    have h2 : x ⟨k.val + 1, hk1⟩ ≤ x v' := hx.monotone (show (⟨k.val + 1, hk1⟩ : Fin n) ≤ v' by change k.val + 1 ≤ v'.val; omega)
    linarith
  have hε_gt_left : ∀ (u' k : Fin n), u' < k → x u' < x k - ε := by
    intro u' k huk
    let p : Fin n := ⟨k.val - 1, by have := k.isLt; omega⟩
    have hp1 : p.val + 1 < n := by simp [p]; have := k.isLt; omega
    have hpeq : (⟨p.val + 1, hp1⟩ : Fin n) = k := Fin.ext (by simp [p]; omega)
    have h1 := hε_adj p hp1
    rw [hpeq] at h1
    have h2 : x u' ≤ x p := hx.monotone (show u' ≤ p by change u'.val ≤ k.val - 1; omega)
    linarith
  -- Construct M : MultiSlabWiring n I u v!
  let M : MultiSlabWiring n I u v :=
    { edge_lt := huv
      posL := posL_γ
      posR := posR_γ
      posL_inj := fun s e₁ h1 e₂ h2 hEq => by
        by_contra hne
        obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2
        have hs0 : 0 < s.val := by omega
        have hsn : s.val < n := by have := (v e₁).isLt; omega
        have hs : 0 < s.val ∧ s.val < n := ⟨hs0, hsn⟩
        simp only [posL_γ, dif_pos hs] at hEq
        let k : Fin n := ⟨s.val - 1, by omega⟩
        have hmax : x (max (u e₁) (u e₂)) < x k + ε := by
          have hle : max (u e₁) (u e₂) ≤ k := max_le (show u e₁ ≤ k by change (u e₁).val ≤ s.val - 1; omega)
            (show u e₂ ≤ k by change (u e₂).val ≤ s.val - 1; omega)
          linarith [hx.monotone hle]
        have hmin : x k + ε < x (min (v e₁) (v e₂)) :=
          hε_lt_right k (min (v e₁) (v e₂)) (lt_min (show k < v e₁ by change s.val - 1 < (v e₁).val; omega)
            (show k < v e₂ by change s.val - 1 < (v e₂).val; omega))
        exact hno_eq_near k e₁ e₂ h1I h2I hne (x k + ε) hmax hmin
          (by rw [add_sub_cancel_left, abs_of_pos hε_pos]) hEq
      posR_inj := fun s e₁ h1 e₂ h2 hEq => by
        by_contra hne
        obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2
        have hs0 : 0 < s.val := by omega
        have hsn : s.val < n := by have := (v e₁).isLt; omega
        have hs : 0 < s.val ∧ s.val < n := ⟨hs0, hsn⟩
        simp only [posR_γ, dif_pos hs] at hEq
        let k : Fin n := ⟨s.val, hsn⟩
        have hmax : x (max (u e₁) (u e₂)) < x k - ε :=
          hε_gt_left (max (u e₁) (u e₂)) k (max_lt (show u e₁ < k by change (u e₁).val < s.val; omega)
            (show u e₂ < k by change (u e₂).val < s.val; omega))
        have hmin : x k - ε < x (min (v e₁) (v e₂)) := by
          have hle : k ≤ min (v e₁) (v e₂) := le_min (show k ≤ v e₁ by change s.val ≤ (v e₁).val; omega)
            (show k ≤ v e₂ by change s.val ≤ (v e₂).val; omega)
          linarith [hx.monotone hle]
        exact hno_eq_near k e₁ e₂ h1I h2I hne (x k - ε) hmax hmin
          (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε_pos]) hEq
      above := above_γ
      pass_order := fun k e₁ h1 e₂ h2 => by
        obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2
        have hk0 : 0 < k.val := by omega
        have hkn : k.val + 1 < n := by have := (v e₁).isLt; omega
        have hL : 0 < k.castSucc.val ∧ k.castSucc.val < n := ⟨hk0, k.isLt⟩
        have hR : 0 < k.succ.val ∧ k.succ.val < n := ⟨by simp, by simp; omega⟩
        simp only [posR_γ, posL_γ, dif_pos hL, dif_pos hR]
        have hk1 : (⟨k.castSucc.val, hL.2⟩ : Fin n) = k := Fin.ext rfl
        have hk2 : (⟨k.succ.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp)
        rw [hk1, hk2]
        by_cases h12 : e₁ = e₂
        · subst h12; simp
        · have hmax : x (max (u e₁) (u e₂)) < x k - ε := hε_gt_left _ k (max_lt h1u h2u)
          have hmin : x k + ε < x (min (v e₁) (v e₂)) := hε_lt_right k _ (lt_min h1v h2v)
          have hsub1 : Set.Icc (x k - ε) (x k + ε) ⊆ Set.Icc (x (u e₁)) (x (v e₁)) := fun t ht =>
            ⟨le_trans (le_of_lt (lt_of_le_of_lt (hx.monotone (le_max_left _ _)) hmax)) ht.1,
             le_trans ht.2 (le_of_lt (lt_of_lt_of_le hmin (hx.monotone (min_le_left _ _))))⟩
          have hsub2 : Set.Icc (x k - ε) (x k + ε) ⊆ Set.Icc (x (u e₂)) (x (v e₂)) := fun t ht =>
            ⟨le_trans (le_of_lt (lt_of_le_of_lt (hx.monotone (le_max_right _ _)) hmax)) ht.1,
             le_trans ht.2 (le_of_lt (lt_of_lt_of_le hmin (hx.monotone (min_le_right _ _))))⟩
          have hcdiff : ContinuousOn (fun t => γ e₁ t - γ e₂ t) (Set.Icc (x k - ε) (x k + ε)) :=
            (hcont e₁ h1I).mono hsub1 |>.sub ((hcont e₂ h2I).mono hsub2)
          have hno_root : ∀ t ∈ Set.Icc (x k - ε) (x k + ε), γ e₁ t ≠ γ e₂ t := fun t ht =>
            hno_eq_near k e₁ e₂ h1I h2I h12 t (lt_of_lt_of_le hmax ht.1) (lt_of_le_of_lt ht.2 hmin)
              (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          constructor
          · intro hlt
            have hneR : γ e₁ (x k + ε) ≠ γ e₂ (x k + ε) :=
              hno_root (x k + ε) ⟨by linarith, le_rfl⟩
            rcases lt_or_gt_of_ne hneR with h | h
            · exact h
            · exfalso
              obtain ⟨t, ht, hroot⟩ := hivt (fun t => γ e₁ t - γ e₂ t) (x k - ε) (x k + ε)
                (by linarith) hcdiff (by linarith) (by linarith)
              exact hno_root t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ (sub_eq_zero.mp hroot)
          · intro hlt
            have hneL : γ e₁ (x k - ε) ≠ γ e₂ (x k - ε) :=
              hno_root (x k - ε) ⟨le_rfl, by linarith⟩
            rcases lt_or_gt_of_ne hneL with h | h
            · exact h
            · exfalso
              obtain ⟨t, ht, hroot⟩ := hivt (fun t => γ e₂ t - γ e₁ t) (x k - ε) (x k + ε)
                (by linarith) ((hcont e₂ h2I).mono hsub2 |>.sub ((hcont e₁ h1I).mono hsub1))
                (by linarith) (by linarith)
              exact hno_root t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ (sub_eq_zero.mp hroot).symm
      pass_above_end := fun k e he e' he' => by
        obtain ⟨heI, heu, hev⟩ := Finset.mem_filter.mp he
        obtain ⟨he'I, he'v⟩ := Finset.mem_filter.mp he'
        have hk0 : 0 < k.val := by omega
        have hL : 0 < k.castSucc.val ∧ k.castSucc.val < n := ⟨hk0, k.isLt⟩
        simp only [posR_γ, above_γ, dif_pos hL]
        have hk1 : (⟨k.castSucc.val, hL.2⟩ : Fin n) = k := Fin.ext rfl
        rw [hk1]
        have hδmem : (hδ_end k e e' he he').choose ∈ allGaps := by
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact Finset.mem_image.mpr ⟨(k, (e, e')),
            Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨heI, he'I⟩⟩,
            by simp only [dif_pos (And.intro he he')]⟩
        have hε_le_δ : ε < (hδ_end k e e' he he').choose := hε_lt _ hδmem
        have hspec := (hδ_end k e e' he he').choose_spec.2 (x k - ε) ⟨by linarith, by linarith⟩
        have hne : γ e (x k) ≠ y k := hno_hit e heI k heu hev
        by_cases hgt : y k < γ e (x k)
        · simp only [decide_eq_true_eq, hgt, ↓reduceIte]; exact hspec.1 hgt
        · simp only [decide_eq_true_eq, hgt, ↓reduceIte]
          exact hspec.2 (lt_of_le_of_ne (not_lt.mp hgt) hne)
      pass_above_start := fun k e he e' he' => by
        obtain ⟨heI, heu, hev⟩ := Finset.mem_filter.mp he
        obtain ⟨he'I, he'u⟩ := Finset.mem_filter.mp he'
        have hkn : k.val + 1 < n := by have := (v e).isLt; omega
        have hR : 0 < k.succ.val ∧ k.succ.val < n := ⟨by simp, by simp; omega⟩
        simp only [posL_γ, above_γ, dif_pos hR]
        have hk2 : (⟨k.succ.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp)
        rw [hk2]
        have hδmem : (hδ_start k e e' he he').choose ∈ allGaps := by
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨(k, (e, e')),
            Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨heI, he'I⟩⟩,
            by simp only [dif_pos (And.intro he he')]⟩
        have hε_le_δ : ε < (hδ_start k e e' he he').choose := hε_lt _ hδmem
        have hspec := (hδ_start k e e' he he').choose_spec.2 (x k + ε) ⟨by linarith, by linarith⟩
        have hne : γ e (x k) ≠ y k := hno_hit e heI k heu hev
        by_cases hgt : y k < γ e (x k)
        · simp only [decide_eq_true_eq, hgt, ↓reduceIte]; exact hspec.1 hgt
        · simp only [decide_eq_true_eq, hgt, ↓reduceIte]
          exact hspec.2 (lt_of_le_of_ne (not_lt.mp hgt) hne)
      pass_below_lt_above := fun k e₁ h1 e₂ h2 hF hT => by
        obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2
        have hk0 : 0 < k.val := by omega
        have hL : 0 < k.castSucc.val ∧ k.castSucc.val < n := ⟨hk0, k.isLt⟩
        simp only [posR_γ, dif_pos hL]
        have hk1 : (⟨k.castSucc.val, hL.2⟩ : Fin n) = k := Fin.ext rfl
        rw [hk1]
        simp only [above_γ, decide_eq_false_iff_not, decide_eq_true_eq] at hF hT
        have hlt_k : γ e₁ (x k) < γ e₂ (x k) := lt_of_le_of_lt (not_lt.mp hF) hT
        have h12 : e₁ ≠ e₂ := fun heq => lt_irrefl _ (heq ▸ hlt_k)
        have hmax : x (max (u e₁) (u e₂)) < x k - ε := hε_gt_left _ k (max_lt h1u h2u)
        have hmin : x k < x (min (v e₁) (v e₂)) := hx (lt_min h1v h2v)
        have hsub1 : Set.Icc (x k - ε) (x k) ⊆ Set.Icc (x (u e₁)) (x (v e₁)) := fun t ht =>
          ⟨le_trans (le_of_lt (lt_of_le_of_lt (hx.monotone (le_max_left _ _)) hmax)) ht.1,
           le_trans ht.2 (le_of_lt (hx h1v))⟩
        have hsub2 : Set.Icc (x k - ε) (x k) ⊆ Set.Icc (x (u e₂)) (x (v e₂)) := fun t ht =>
          ⟨le_trans (le_of_lt (lt_of_le_of_lt (hx.monotone (le_max_right _ _)) hmax)) ht.1,
           le_trans ht.2 (le_of_lt (hx h2v))⟩
        have hno_root : ∀ t ∈ Set.Icc (x k - ε) (x k), γ e₁ t ≠ γ e₂ t := fun t ht =>
          hno_eq_near k e₁ e₂ h1I h2I h12 t (lt_of_lt_of_le hmax ht.1) (lt_of_le_of_lt ht.2 hmin)
            (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        have hneL : γ e₁ (x k - ε) ≠ γ e₂ (x k - ε) := hno_root (x k - ε) ⟨le_rfl, by linarith⟩
        rcases lt_or_gt_of_ne hneL with h | h
        · exact h
        · exfalso
          obtain ⟨t, ht, hroot⟩ := hivt (fun t => γ e₂ t - γ e₁ t) (x k - ε) (x k)
            (by linarith) ((hcont e₂ h2I).mono hsub2 |>.sub ((hcont e₁ h1I).mono hsub1))
            (by linarith) (by linarith)
          exact hno_root t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ (sub_eq_zero.mp hroot).symm }
  refine ⟨M, ε, hε_pos, hε_adj, ?_⟩
  intro s e₁ e₂ hinv
  obtain ⟨hprod, hLlt, hRgt⟩ := Finset.mem_filter.mp hinv
  obtain ⟨h1act, h2act⟩ := Finset.mem_product.mp hprod
  obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1act
  obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2act
  dsimp only at h1u h1v h2u h2v
  have hs0 : 0 < s.val := by omega
  have hsn : s.val < n := by have := (v e₁).isLt; omega
  have hs : 0 < s.val ∧ s.val < n := ⟨hs0, hsn⟩
  simp only [M, posL_γ, posR_γ, dif_pos hs] at hLlt hRgt
  let kL : Fin n := ⟨s.val - 1, by omega⟩
  let kR : Fin n := ⟨s.val, hsn⟩
  have hk_adj : x kL + ε < x kR - ε := by
    have hk1 : kL.val + 1 < n := by simp [kL]; omega
    have hkeq : (⟨kL.val + 1, hk1⟩ : Fin n) = kR := Fin.ext (by simp [kL, kR]; omega)
    rw [← hkeq]; exact hε_adj kL hk1
  have hmax : x (max (u e₁) (u e₂)) < x kL + ε := by
    have hle : max (u e₁) (u e₂) ≤ kL := max_le (show u e₁ ≤ kL by change (u e₁).val ≤ s.val - 1; omega)
      (show u e₂ ≤ kL by change (u e₂).val ≤ s.val - 1; omega)
    linarith [hx.monotone hle]
  have hmin : x kR - ε < x (min (v e₁) (v e₂)) := by
    have hle : kR ≤ min (v e₁) (v e₂) := le_min (show kR ≤ v e₁ by change s.val ≤ (v e₁).val; omega)
      (show kR ≤ v e₂ by change s.val ≤ (v e₂).val; omega)
    linarith [hx.monotone hle]
  have hsub1 : Set.Icc (x kL + ε) (x kR - ε) ⊆ Set.Icc (x (u e₁)) (x (v e₁)) := fun t ht =>
    ⟨le_trans (le_of_lt (lt_of_le_of_lt (hx.monotone (le_max_left _ _)) hmax)) ht.1,
     le_trans ht.2 (le_of_lt (lt_of_lt_of_le hmin (hx.monotone (min_le_left _ _))))⟩
  have hsub2 : Set.Icc (x kL + ε) (x kR - ε) ⊆ Set.Icc (x (u e₂)) (x (v e₂)) := fun t ht =>
    ⟨le_trans (le_of_lt (lt_of_le_of_lt (hx.monotone (le_max_right _ _)) hmax)) ht.1,
     le_trans ht.2 (le_of_lt (lt_of_lt_of_le hmin (hx.monotone (min_le_right _ _))))⟩
  have h12 : e₁ ≠ e₂ := fun heq => lt_irrefl _ (heq ▸ hLlt)
  obtain ⟨t, ht, hroot⟩ := hivt (fun t => γ e₁ t - γ e₂ t) (x kL + ε) (x kR - ε)
    (le_of_lt hk_adj) ((hcont e₁ h1I).mono hsub1 |>.sub ((hcont e₂ h2I).mono hsub2))
    (by linarith) (by linarith)
  have hγeq : γ e₁ t = γ e₂ t := sub_eq_zero.mp hroot
  have htX : t ∈ X_int := hX e₁ h1I e₂ h2I h12 t (lt_trans hmax ht.1) (lt_trans ht.2 hmin) hγeq
  exact ⟨hs0, hsn, t, ht.1, ht.2, hγeq, htX⟩

end WiringCrossingLemma

/-! ## Section 4: Szemerédi–Trotter Theorem, `k`-Rich Lines, & Beck's Theorem (1983) -/

section SzemerediTrotterBeck

/-- Helper: cube of `(a : ℝ) ^ ((2 : ℝ) / 3)` equals `a ^ 2` for `0 ≤ a`. -/
lemma rpow_two_thirds_cube {a : ℝ} (ha : 0 ≤ a) : (a ^ ((2 : ℝ) / 3)) ^ 3 = a ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  norm_num

/-- **Unified 1-Intersecting `x`-Monotone Curve Szemerédi–Trotter Theorem:**
Given `n` vertices `(x k, y k)` with strictly increasing `x`-coordinates and a finite family `ℱ` of
continuous `x`-monotone curves `f c : [lo c, hi c] → ℝ` such that:
1. Any two distinct curves agree at **at most 1** point in their common domain,
2. Any intersection of two distinct curves at a vertex abscissa `x k` actually passes through `(x k, y k)`,
then the total number of point–curve incidences satisfies
`I(P, ℱ) ≤ 4 |P|^(2/3) |ℱ|^(2/3) + 4 |P| + |ℱ|`. -/
theorem xMonotone_one_inter_incidences_le {n : ℕ} {κ : Type*} [DecidableEq κ]
    (x y : Fin n → ℝ) (hx : StrictMono x)
    (ℱ : Finset κ) (lo hi : κ → ℝ) (f : κ → ℝ → ℝ)
    (hcont : ∀ c ∈ ℱ, ContinuousOn (f c) (Set.Icc (lo c) (hi c)))
    (h1inter : ∀ c₁ ∈ ℱ, ∀ c₂ ∈ ℱ, c₁ ≠ c₂ →
      ∀ t₁ t₂ : ℝ,
        lo c₁ ≤ t₁ → t₁ ≤ hi c₁ → lo c₂ ≤ t₁ → t₁ ≤ hi c₂ → f c₁ t₁ = f c₂ t₁ →
        lo c₁ ≤ t₂ → t₂ ≤ hi c₁ → lo c₂ ≤ t₂ → t₂ ≤ hi c₂ → f c₁ t₂ = f c₂ t₂ →
        t₁ = t₂)
    (hgen : ∀ c₁ ∈ ℱ, ∀ c₂ ∈ ℱ, c₁ ≠ c₂ → ∀ k : Fin n,
      lo c₁ ≤ x k → x k ≤ hi c₁ → lo c₂ ≤ x k → x k ≤ hi c₂ →
      f c₁ (x k) = f c₂ (x k) → f c₁ (x k) = y k) :
    ((∑ c ∈ ℱ, ((Finset.univ : Finset (Fin n)).filter
      (fun k => lo c ≤ x k ∧ x k ≤ hi c ∧ f c (x k) = y k)).card : ℕ) : ℝ) ≤
      4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (ℱ.card : ℝ) ^ ((2 : ℝ) / 3) + 4 * (n : ℝ) + (ℱ.card : ℝ) := by
  classical
  let onC (c : κ) (k : Fin n) : Prop := lo c ≤ x k ∧ x k ≤ hi c ∧ f c (x k) = y k
  let pts (c : κ) : Finset (Fin n) := Finset.univ.filter (onC c)
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : ∀ c ∈ ℱ, (pts c).card = 0 := fun c _ => by simp [pts]
    have hsum0 : ∑ c ∈ ℱ, (pts c).card = 0 := Finset.sum_eq_zero h0
    change ((∑ c ∈ ℱ, (pts c).card : ℕ) : ℝ) ≤ _
    rw [hsum0, Nat.cast_zero]
    positivity
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hF0 : ℱ.card = 0
  · rw [Finset.card_eq_zero] at hF0; subst hF0; simp
  -- Build consecutive-arc simple graph E ⊆ Fin n × Fin n and curve-indexed edge set I_edges!
  let consecPairs (c : κ) : Finset (Fin n × Fin n) :=
    let S := pts c
    let φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
    ((Finset.univ : Finset (Fin S.card)).filter (fun i => i.val + 1 < S.card)).image
      (fun i => if hi' : i.val + 1 < S.card then (φ i, φ ⟨i.val + 1, hi'⟩) else (φ i, φ i))
  have hconsec_card : ∀ c ∈ ℱ, (pts c).card ≤ (consecPairs c).card + 1 := by
    intro c _
    let S := pts c
    let φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
    let idx := (Finset.univ : Finset (Fin S.card)).filter (fun i => i.val + 1 < S.card)
    have hinj : Set.InjOn
        (fun i : Fin S.card => if hi' : i.val + 1 < S.card then (φ i, φ ⟨i.val + 1, hi'⟩) else (φ i, φ i))
        idx := by
      intro i₁ h1 i₂ h2 hEq
      have hi1 : i₁.val + 1 < S.card := (Finset.mem_filter.mp h1).2
      have hi2 : i₂.val + 1 < S.card := (Finset.mem_filter.mp h2).2
      simp only [dif_pos hi1, dif_pos hi2] at hEq
      exact φ.injective (congrArg Prod.fst hEq)
    have hcard_eq : (consecPairs c).card = idx.card := Finset.card_image_of_injOn hinj
    change S.card ≤ (consecPairs c).card + 1
    rw [hcard_eq]
    by_cases hS0 : S.card = 0
    · omega
    · have hidx_eq : idx = Finset.univ.erase ⟨S.card - 1, by omega⟩ := by
        ext i
        simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, ne_eq, Fin.ext_iff]
        have := i.isLt
        omega
      rw [hidx_eq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
  have hconsec_spec : ∀ c ∈ ℱ, ∀ e ∈ consecPairs c,
      e.1 < e.2 ∧ onC c e.1 ∧ onC c e.2 ∧ ∀ k : Fin n, e.1 < k → k < e.2 → ¬ onC c k := by
    intro c _ e he
    let S := pts c
    let φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
    dsimp only [consecPairs] at he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hi' : i.val + 1 < S.card := (Finset.mem_filter.mp hi).2
    rw [dif_pos hi']
    have hlt : φ i < φ ⟨i.val + 1, hi'⟩ :=
      φ.lt_iff_lt.mpr (show i < ⟨i.val + 1, hi'⟩ by change i.val < i.val + 1; omega)
    have h1 : onC c (φ i) := (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl i)).2
    have h2 : onC c (φ ⟨i.val + 1, hi'⟩) := (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl ⟨i.val + 1, hi'⟩)).2
    refine ⟨hlt, h1, h2, fun k hk1 hk2 hkon => ?_⟩
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkon⟩
    have hrng : Set.range φ = (S : Set (Fin n)) := S.range_orderEmbOfFin rfl
    have hkr : k ∈ Set.range φ := by rw [hrng]; exact hkS
    obtain ⟨j, hj⟩ := Set.mem_range.mp hkr
    rw [← hj] at hk1 hk2
    have hj1 : i < j := φ.lt_iff_lt.mp hk1
    have hj2 : j < ⟨i.val + 1, hi'⟩ := φ.lt_iff_lt.mp hk2
    change i.val < j.val at hj1
    change j.val < i.val + 1 at hj2
    omega
  -- Collect curve-labeled edges I_edges : Finset (κ × (Fin n × Fin n))!
  let I_edges : Finset (κ × (Fin n × Fin n)) :=
    ℱ.biUnion (fun c => (consecPairs c).image (fun e => (c, e)))
  have hI_card : ∑ c ∈ ℱ, (pts c).card ≤ I_edges.card + ℱ.card := by
    have hdisj : Set.PairwiseDisjoint (ℱ : Set κ) (fun c => (consecPairs c).image (fun e => (c, e))) := by
      intro c₁ _ c₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨e₁, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨e₂, _, hEq⟩
      exact hne (congrArg Prod.fst hEq).symm
    have hIeq : I_edges.card = ∑ c ∈ ℱ, (consecPairs c).card := by
      rw [Finset.card_biUnion hdisj]
      refine Finset.sum_congr rfl fun c _ => Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
    calc ∑ c ∈ ℱ, (pts c).card
        ≤ ∑ c ∈ ℱ, ((consecPairs c).card + 1) := Finset.sum_le_sum hconsec_card
      _ = (∑ c ∈ ℱ, (consecPairs c).card) + ℱ.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = I_edges.card + ℱ.card := by rw [hIeq]
  -- Each edge e = (c, (a, b)) ∈ I_edges satisfies the hypotheses of xMonotone_multi_to_slabWiring!
  have hI_mem : ∀ e ∈ I_edges, e.1 ∈ ℱ ∧ e.2 ∈ consecPairs e.1 := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨c, hcF, hce⟩
    rcases Finset.mem_image.mp hce with ⟨p, hp, rfl⟩
    exact ⟨hcF, hp⟩
  -- Uniqueness of curve for a given endpoint pair (a, b): multiplicity ≤ 1!
  have hpair_inj : Set.InjOn (fun e : κ × (Fin n × Fin n) => e.2) I_edges := by
    intro e₁ h1 e₂ h2 hEq
    dsimp only at hEq
    have ⟨hc1, hp1⟩ := hI_mem e₁ h1
    have ⟨hc2, hp2⟩ := hI_mem e₂ h2
    obtain ⟨hlt1, h1a, h1b, _⟩ := hconsec_spec e₁.1 hc1 e₁.2 hp1
    obtain ⟨_, h2a, h2b, _⟩ := hconsec_spec e₂.1 hc2 e₂.2 hp2
    rw [← hEq] at h2a h2b
    by_cases hc : e₁.1 = e₂.1
    · exact Prod.ext hc hEq
    · exfalso
      have htx := h1inter e₁.1 hc1 e₂.1 hc2 hc (x e₁.2.1) (x e₁.2.2)
        h1a.1 h1a.2.1 h2a.1 h2a.2.1 (h1a.2.2.trans h2a.2.2.symm)
        h1b.1 h1b.2.1 h2b.1 h2b.2.1 (h1b.2.2.trans h2b.2.2.symm)
      exact ne_of_lt (hx hlt1) htx
  -- Disjoint open x-intervals for two distinct consecutive arcs on the SAME curve c!
  have hsame_curve_disj : ∀ c ∈ ℱ, ∀ p₁ ∈ consecPairs c, ∀ p₂ ∈ consecPairs c, p₁ ≠ p₂ →
      p₁.2 ≤ p₂.1 ∨ p₂.2 ≤ p₁.1 := by
    intro c hc p₁ hp1 p₂ hp2 hne
    obtain ⟨h1lt, h1a, h1b, h1no⟩ := hconsec_spec c hc p₁ hp1
    obtain ⟨h2lt, h2a, h2b, h2no⟩ := hconsec_spec c hc p₂ hp2
    by_contra hnot
    push Not at hnot
    obtain ⟨h21, h12⟩ := hnot
    rcases lt_trichotomy p₁.1 p₂.1 with h | h | h
    · exact h1no p₂.1 h h21 h2a
    · rcases lt_trichotomy p₁.2 p₂.2 with h' | h' | h'
      · exact h2no p₁.2 (h ▸ h1lt) h' h1b
      · exact hne (Prod.ext h h')
      · exact h1no p₂.2 (h.symm ▸ h2lt) h' h2b
    · exact h2no p₁.1 h h12 h1a
  -- Build finite X_int of all non-vertex pairwise intersections of distinct curves in ℱ!
  let interPred (c₁ c₂ : κ) (t : ℝ) : Prop :=
    lo c₁ ≤ t ∧ t ≤ hi c₁ ∧ lo c₂ ≤ t ∧ t ≤ hi c₂ ∧ f c₁ t = f c₂ t ∧ ∀ k : Fin n, t ≠ x k
  let X_int : Finset ℝ :=
    ((ℱ ×ˢ ℱ).filter (fun p => p.1 ≠ p.2 ∧ ∃ t : ℝ, interPred p.1 p.2 t)).image
      (fun p => if h : ∃ t : ℝ, interPred p.1 p.2 t then h.choose else 0)
  have hX_disj : ∀ k : Fin n, x k ∉ X_int := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, hEq⟩
    have hex : ∃ t : ℝ, interPred p.1 p.2 t := (Finset.mem_filter.mp hp).2.2
    rw [dif_pos hex] at hEq
    exact (hex.choose_spec.2.2.2.2.2 k) hEq
  have hX_mem : ∀ e₁ ∈ I_edges, ∀ e₂ ∈ I_edges, e₁ ≠ e₂ → ∀ t : ℝ,
      x (max e₁.2.1 e₂.2.1) < t → t < x (min e₁.2.2 e₂.2.2) →
      f e₁.1 t = f e₂.1 t → t ∈ X_int := by
    intro e₁ h1 e₂ h2 hne t ht1 ht2 hfeq
    have ⟨hc1, hp1⟩ := hI_mem e₁ h1
    have ⟨hc2, hp2⟩ := hI_mem e₂ h2
    obtain ⟨h1lt, h1a, h1b, h1no⟩ := hconsec_spec e₁.1 hc1 e₁.2 hp1
    obtain ⟨h2lt, h2a, h2b, h2no⟩ := hconsec_spec e₂.1 hc2 e₂.2 hp2
    have hxa1 : x e₁.2.1 < t := lt_of_le_of_lt (hx.monotone (le_max_left _ _)) ht1
    have hxb1 : t < x e₁.2.2 := lt_of_lt_of_le ht2 (hx.monotone (min_le_left _ _))
    have hxa2 : x e₂.2.1 < t := lt_of_le_of_lt (hx.monotone (le_max_right _ _)) ht1
    have hxb2 : t < x e₂.2.2 := lt_of_lt_of_le ht2 (hx.monotone (min_le_right _ _))
    have hc_ne : e₁.1 ≠ e₂.1 := by
      intro hceq
      have hp_ne : e₁.2 ≠ e₂.2 := fun hpeq => hne (Prod.ext hceq hpeq)
      have hp2' : e₂.2 ∈ consecPairs e₁.1 := hceq ▸ hp2
      rcases hsame_curve_disj e₁.1 hc1 e₁.2 hp1 e₂.2 hp2' hp_ne with hle | hle
      · have : x e₁.2.2 ≤ x e₂.2.1 := hx.monotone hle
        linarith
      · have : x e₂.2.2 ≤ x e₁.2.1 := hx.monotone hle
        linarith
    have ht_dom1 : lo e₁.1 ≤ t ∧ t ≤ hi e₁.1 := ⟨le_trans h1a.1 (le_of_lt hxa1), le_trans (le_of_lt hxb1) h1b.2.1⟩
    have ht_dom2 : lo e₂.1 ≤ t ∧ t ≤ hi e₂.1 := ⟨le_trans h2a.1 (le_of_lt hxa2), le_trans (le_of_lt hxb2) h2b.2.1⟩
    have ht_not_v : ∀ k : Fin n, t ≠ x k := by
      intro k htk
      subst htk
      have hk1 : e₁.2.1 < k := hx.lt_iff_lt.mp hxa1
      have hk2 : k < e₁.2.2 := hx.lt_iff_lt.mp hxb1
      have hfy := hgen e₁.1 hc1 e₂.1 hc2 hc_ne k ht_dom1.1 ht_dom1.2 ht_dom2.1 ht_dom2.2 hfeq
      exact h1no k hk1 hk2 ⟨ht_dom1.1, ht_dom1.2, hfy⟩
    have hinter : interPred e₁.1 e₂.1 t := ⟨ht_dom1.1, ht_dom1.2, ht_dom2.1, ht_dom2.2, hfeq, ht_not_v⟩
    have hex : ∃ s : ℝ, interPred e₁.1 e₂.1 s := ⟨t, hinter⟩
    refine Finset.mem_image.mpr ⟨(e₁.1, e₂.1), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hc1, hc2⟩, hc_ne, hex⟩, ?_⟩
    rw [dif_pos hex]
    have hs := hex.choose_spec
    exact h1inter e₁.1 hc1 e₂.1 hc2 hc_ne hex.choose t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
      ht_dom1.1 ht_dom1.2 ht_dom2.1 ht_dom2.2 hfeq
  -- Invoke xMonotone_multi_to_slabWiring!
  obtain ⟨M, ε, hε_pos, hε_adj, hinv_spec⟩ := xMonotone_multi_to_slabWiring x y hx
    I_edges (fun e => e.2.1) (fun e => e.2.2)
    (fun e he => (hconsec_spec e.1 (hI_mem e he).1 e.2 (hI_mem e he).2).1)
    (fun e => f e.1)
    (fun e he => by
      have ⟨hc, hp⟩ := hI_mem e he
      obtain ⟨_, ha, hb, _⟩ := hconsec_spec e.1 hc e.2 hp
      exact (hcont e.1 hc).mono (fun t ht => ⟨le_trans ha.1 ht.1, le_trans ht.2 hb.2.1⟩))
    (fun e he => (hconsec_spec e.1 (hI_mem e he).1 e.2 (hI_mem e he).2).2.1.2.2)
    (fun e he => (hconsec_spec e.1 (hI_mem e he).1 e.2 (hI_mem e he).2).2.2.1.2.2)
    (fun e he k hk1 hk2 => by
      have ⟨hc, hp⟩ := hI_mem e he
      obtain ⟨_, ha, hb, hno⟩ := hconsec_spec e.1 hc e.2 hp
      intro hEq
      exact hno k hk1 hk2 ⟨le_trans ha.1 (le_of_lt (hx hk1)), le_trans (le_of_lt (hx hk2)) hb.2.1, hEq⟩)
    X_int hX_mem hX_disj
  -- Bound 2 * M.crossings ≤ ℱ.card ^ 2 by injecting ALL slab inversions into unordered pairs of distinct curves!
  have hcr_bound : 2 * M.crossings ≤ ℱ.card ^ 2 := by
    let allInvs : Finset (Fin (n + 1) × ((κ × (Fin n × Fin n)) × (κ × (Fin n × Fin n)))) :=
      (Finset.univ : Finset (Fin (n + 1))).biUnion fun s =>
        (invPairs (multiActiveEdges I_edges (fun e => e.2.1) (fun e => e.2.2) s) (M.posL s) (M.posR s)).image
          (fun p => (s, p))
    have hallInvs_card : allInvs.card = M.crossings := by
      unfold MultiSlabWiring.crossings
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun s _ =>
          Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
      · intro s₁ _ s₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hx2 with ⟨_, _, hEq⟩
        exact hne (congrArg Prod.fst hEq).symm
    -- Every (s, (e₁, e₂)) ∈ allInvs has e₁.1 ≠ e₂.1, and maps INJECTIVELY to s(e₁.1, e₂.1) : Sym2 κ!
    let offDiag : Finset (κ × κ) := (ℱ ×ˢ ℱ).filter (fun p => p.1 ≠ p.2)
    -- Map (s, (e₁, e₂)) ↦ both (e₁.1, e₂.1) and (e₂.1, e₁.1) in offDiag (2-to-1 -> 2 * |allInvs| ≤ |offDiag| ≤ |ℱ|²)!
    let pairsBoth : Finset (Bool × (Fin (n + 1) × ((κ × (Fin n × Fin n)) × (κ × (Fin n × Fin n))))) :=
      (Finset.univ : Finset Bool) ×ˢ allInvs
    let toOff : Bool × (Fin (n + 1) × ((κ × (Fin n × Fin n)) × (κ × (Fin n × Fin n)))) → κ × κ :=
      fun z => if z.1 then (z.2.2.1.1, z.2.2.2.1) else (z.2.2.2.1, z.2.2.1.1)
    have hinv_props : ∀ z ∈ allInvs,
        let s := z.1; let e₁ := z.2.1; let e₂ := z.2.2
        e₁ ∈ I_edges ∧ e₂ ∈ I_edges ∧ e₁.1 ≠ e₂.1 ∧
        ∃ (h1 : 0 < s.val) (h2 : s.val < n) (t : ℝ),
          x ⟨s.val - 1, by omega⟩ + ε < t ∧ t < x ⟨s.val, h2⟩ - ε ∧
          lo e₁.1 ≤ t ∧ t ≤ hi e₁.1 ∧ lo e₂.1 ≤ t ∧ t ≤ hi e₂.1 ∧
          x e₁.2.1 < t ∧ t < x e₁.2.2 ∧ x e₂.2.1 < t ∧ t < x e₂.2.2 ∧
          f e₁.1 t = f e₂.1 t := by
      intro ⟨s, ⟨e₁, e₂⟩⟩ hz
      rcases Finset.mem_biUnion.mp hz with ⟨s', _, hs'⟩
      rcases Finset.mem_image.mp hs' with ⟨p, hp, hEq⟩
      have hsEq : s' = s := congrArg Prod.fst hEq
      have hpEq : p = (e₁, e₂) := congrArg Prod.snd hEq
      cases hsEq; cases hpEq
      obtain ⟨hprod, hLlt, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1act, h2act⟩ := Finset.mem_product.mp hprod
      obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1act
      obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2act
      dsimp only at h1u h1v h2u h2v
      obtain ⟨h1s, h2s, t, htL, htR, hfeq, _⟩ := hinv_spec s e₁ e₂ hp
      have hne12 : e₁ ≠ e₂ := fun h => lt_irrefl _ (h ▸ hLlt)
      have hxa1 : x e₁.2.1 < t := by
        have hle : e₁.2.1 ≤ ⟨s.val - 1, by omega⟩ := by change e₁.2.1.val ≤ s.val - 1; omega
        linarith [hx.monotone hle]
      have hxb1 : t < x e₁.2.2 := by
        have hle : (⟨s.val, h2s⟩ : Fin n) ≤ e₁.2.2 := by change s.val ≤ e₁.2.2.val; omega
        linarith [hx.monotone hle]
      have hxa2 : x e₂.2.1 < t := by
        have hle : e₂.2.1 ≤ ⟨s.val - 1, by omega⟩ := by change e₂.2.1.val ≤ s.val - 1; omega
        linarith [hx.monotone hle]
      have hxb2 : t < x e₂.2.2 := by
        have hle : (⟨s.val, h2s⟩ : Fin n) ≤ e₂.2.2 := by change s.val ≤ e₂.2.2.val; omega
        linarith [hx.monotone hle]
      have ⟨hc1, hp1⟩ := hI_mem e₁ h1I
      have ⟨hc2, hp2⟩ := hI_mem e₂ h2I
      obtain ⟨_, h1a, h1b, _⟩ := hconsec_spec e₁.1 hc1 e₁.2 hp1
      obtain ⟨_, h2a, h2b, _⟩ := hconsec_spec e₂.1 hc2 e₂.2 hp2
      have hcne : e₁.1 ≠ e₂.1 := by
        intro hceq
        have hp_ne : e₁.2 ≠ e₂.2 := fun hpeq => hne12 (Prod.ext hceq hpeq)
        rcases hsame_curve_disj e₁.1 hc1 e₁.2 hp1 e₂.2 (hceq ▸ hp2) hp_ne with hle | hle
        · have : x e₁.2.2 ≤ x e₂.2.1 := hx.monotone hle; linarith
        · have : x e₂.2.2 ≤ x e₁.2.1 := hx.monotone hle; linarith
      exact ⟨h1I, h2I, hcne, h1s, h2s, t, htL, htR,
        le_trans h1a.1 (le_of_lt hxa1), le_trans (le_of_lt hxb1) h1b.2.1,
        le_trans h2a.1 (le_of_lt hxa2), le_trans (le_of_lt hxb2) h2b.2.1,
        hxa1, hxb1, hxa2, hxb2, hfeq⟩
    -- Prove toOff maps pairsBoth INJECTIVELY into offDiag!
    have htoOff_mem : ∀ z ∈ pairsBoth, toOff z ∈ offDiag := by
      rintro ⟨b, z⟩ hz
      have hzA : z ∈ allInvs := (Finset.mem_product.mp hz).2
      obtain ⟨h1I, h2I, hcne, _⟩ := hinv_props z hzA
      cases b
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hI_mem _ h2I).1, (hI_mem _ h1I).1⟩, hcne.symm⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hI_mem _ h1I).1, (hI_mem _ h2I).1⟩, hcne⟩
    have htoOff_inj : Set.InjOn toOff pairsBoth := by
      rintro ⟨b₁, ⟨s₁, ⟨e₁, e₂⟩⟩⟩ h1 ⟨b₂, ⟨s₂, ⟨e₁', e₂'⟩⟩⟩ h2 hEq
      have hz1 : (s₁, (e₁, e₂)) ∈ allInvs := (Finset.mem_product.mp h1).2
      have hz2 : (s₂, (e₁', e₂')) ∈ allInvs := (Finset.mem_product.mp h2).2
      obtain ⟨h1I, h2I, hcne, h1s1, h2s1, t₁, ht1L, ht1R, hd1a, hd1b, hd2a, hd2b,
        hxa1, hxb1, hxa2, hxb2, hf1⟩ := hinv_props _ hz1
      obtain ⟨h1I', h2I', hcne', h1s2, h2s2, t₂, ht2L, ht2R, hd1a', hd1b', hd2a', hd2b',
        hxa1', hxb1', hxa2', hxb2', hf2⟩ := hinv_props _ hz2
      -- Auxiliary: if c = e.1 = e'.1 and t lies in BOTH (x e.2.1, x e.2.2) and (x e'.2.1, x e'.2.2), then e = e'!
      have hsame_arc : ∀ a b : κ × (Fin n × Fin n), a ∈ I_edges → b ∈ I_edges → a.1 = b.1 →
          x a.2.1 < t₁ → t₁ < x a.2.2 → x b.2.1 < t₁ → t₁ < x b.2.2 → a = b := by
        intro a b haI hbI hceq ha1 ha2 hb1 hb2
        by_contra hne
        have hpne : a.2 ≠ b.2 := fun hp => hne (Prod.ext hceq hp)
        rcases hsame_curve_disj a.1 (hI_mem a haI).1 a.2 (hI_mem a haI).2 b.2 (hceq ▸ (hI_mem b hbI).2) hpne with hle | hle
        · have : x a.2.2 ≤ x b.2.1 := hx.monotone hle; linarith
        · have : x b.2.2 ≤ x a.2.1 := hx.monotone hle; linarith
      -- Auxiliary: t₁ = t₂ forces s₁ = s₂ because open slab intervals are pairwise disjoint!
      have hsame_slab : t₁ = t₂ → s₁ = s₂ := by
        intro htEq
        by_contra hsne
        have hvalne : s₁.val ≠ s₂.val := fun h => hsne (Fin.ext h)
        rcases lt_or_gt_of_ne hvalne with hlt | hgt
        · have hle : (⟨s₁.val, h2s1⟩ : Fin n) ≤ ⟨s₂.val - 1, by omega⟩ := by
            change s₁.val ≤ s₂.val - 1; omega
          linarith [hx.monotone hle]
        · have hle : (⟨s₂.val, h2s2⟩ : Fin n) ≤ ⟨s₁.val - 1, by omega⟩ := by
            change s₂.val ≤ s₁.val - 1; omega
          linarith [hx.monotone hle]
      -- Auxiliary: extract original invPairs membership from allInvs!
      have hmem_inv : ∀ s p, (s, p) ∈ allInvs →
          p ∈ invPairs (multiActiveEdges I_edges (fun e => e.2.1) (fun e => e.2.2) s) (M.posL s) (M.posR s) := by
        intro s p hsp
        rcases Finset.mem_biUnion.mp hsp with ⟨s', _, hs'⟩
        rcases Finset.mem_image.mp hs' with ⟨p', hp', hEq'⟩
        have hs'eq : s' = s := congrArg Prod.fst hEq'
        have hp'eq : p' = p := congrArg Prod.snd hEq'
        subst hs'eq; subst hp'eq; exact hp'
      have hinv1 := hmem_inv s₁ (e₁, e₂) hz1
      have hinv2 := hmem_inv s₂ (e₁', e₂') hz2
      cases b₁ <;> cases b₂ <;> simp only [toOff, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hEq
      · -- (false, false): e₂.1 = e₂'.1 and e₁.1 = e₁'.1
        obtain ⟨hce2, hce1⟩ := hEq
        have htEq : t₁ = t₂ := h1inter e₁.1 (hI_mem _ h1I).1 e₂.1 (hI_mem _ h2I).1 hcne t₁ t₂
          hd1a hd1b hd2a hd2b hf1 (hce1 ▸ hd1a') (hce1 ▸ hd1b') (hce2 ▸ hd2a') (hce2 ▸ hd2b')
          (by rw [hce1, hce2]; exact hf2)
        have hsEq := hsame_slab htEq
        have he1Eq := hsame_arc e₁ e₁' h1I h1I' hce1 hxa1 hxb1 (htEq ▸ hxa1') (htEq ▸ hxb1')
        have he2Eq := hsame_arc e₂ e₂' h2I h2I' hce2 hxa2 hxb2 (htEq ▸ hxa2') (htEq ▸ hxb2')
        subst hsEq; subst he1Eq; subst he2Eq; rfl
      · -- (false, true): e₂.1 = e₁'.1 and e₁.1 = e₂'.1 → forces e₁ = e₂' and e₂ = e₁', impossible by invPairs asymmetry!
        obtain ⟨hce2, hce1⟩ := hEq
        have htEq : t₁ = t₂ := h1inter e₁.1 (hI_mem _ h1I).1 e₂.1 (hI_mem _ h2I).1 hcne t₁ t₂
          hd1a hd1b hd2a hd2b hf1 (hce1 ▸ hd2a') (hce1 ▸ hd2b') (hce2 ▸ hd1a') (hce2 ▸ hd1b')
          (by rw [hce1, hce2]; exact hf2.symm)
        have hsEq := hsame_slab htEq
        have he1Eq := hsame_arc e₁ e₂' h1I h2I' hce1 hxa1 hxb1 (htEq ▸ hxa2') (htEq ▸ hxb2')
        have he2Eq := hsame_arc e₂ e₁' h2I h1I' hce2 hxa2 hxb2 (htEq ▸ hxa1') (htEq ▸ hxb1')
        subst hsEq; subst he1Eq; subst he2Eq
        have hL1 := (Finset.mem_filter.mp hinv1).2.1
        have hL2 := (Finset.mem_filter.mp hinv2).2.1
        linarith
      · -- (true, false): symmetric contradiction by invPairs asymmetry!
        obtain ⟨hce1, hce2⟩ := hEq
        have htEq : t₁ = t₂ := h1inter e₁.1 (hI_mem _ h1I).1 e₂.1 (hI_mem _ h2I).1 hcne t₁ t₂
          hd1a hd1b hd2a hd2b hf1 (hce1 ▸ hd2a') (hce1 ▸ hd2b') (hce2 ▸ hd1a') (hce2 ▸ hd1b')
          (by rw [hce1, hce2]; exact hf2.symm)
        have hsEq := hsame_slab htEq
        have he1Eq := hsame_arc e₁ e₂' h1I h2I' hce1 hxa1 hxb1 (htEq ▸ hxa2') (htEq ▸ hxb2')
        have he2Eq := hsame_arc e₂ e₁' h2I h1I' hce2 hxa2 hxb2 (htEq ▸ hxa1') (htEq ▸ hxb1')
        subst hsEq; subst he1Eq; subst he2Eq
        have hL1 := (Finset.mem_filter.mp hinv1).2.1
        have hL2 := (Finset.mem_filter.mp hinv2).2.1
        linarith
      · -- (true, true): e₁.1 = e₁'.1 and e₂.1 = e₂'.1
        obtain ⟨hce1, hce2⟩ := hEq
        have htEq : t₁ = t₂ := h1inter e₁.1 (hI_mem _ h1I).1 e₂.1 (hI_mem _ h2I).1 hcne t₁ t₂
          hd1a hd1b hd2a hd2b hf1 (hce1 ▸ hd1a') (hce1 ▸ hd1b') (hce2 ▸ hd2a') (hce2 ▸ hd2b')
          (by rw [hce1, hce2]; exact hf2)
        have hsEq := hsame_slab htEq
        have he1Eq := hsame_arc e₁ e₁' h1I h1I' hce1 hxa1 hxb1 (htEq ▸ hxa1') (htEq ▸ hxb1')
        have he2Eq := hsame_arc e₂ e₂' h2I h2I' hce2 hxa2 hxb2 (htEq ▸ hxa2') (htEq ▸ hxb2')
        subst hsEq; subst he1Eq; subst he2Eq; rfl
    have hcard_le : pairsBoth.card ≤ offDiag.card := by
      rw [← Finset.card_image_of_injOn htoOff_inj]
      exact Finset.card_le_card (fun x hx => by
        rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩; exact htoOff_mem z hz)
    have hpcard : pairsBoth.card = 2 * M.crossings := by
      simp [pairsBoth, Finset.card_product, hallInvs_card]
    have hoff_le : offDiag.card ≤ ℱ.card ^ 2 := by
      calc offDiag.card ≤ (ℱ ×ˢ ℱ).card := Finset.card_filter_le _ _
        _ = ℱ.card ^ 2 := by simp [Finset.card_product, sq]
    omega
  -- Convert multiplicity-1 MultiSlabWiring M to simple SlabWiring W on E = I_edges.image Prod.snd!
  by_cases hsparse : I_edges.card < 4 * n
  · have hsumR : ((∑ c ∈ ℱ, (pts c).card : ℕ) : ℝ) ≤ (I_edges.card : ℝ) + (ℱ.card : ℝ) := by
      exact_mod_cast hI_card
    have hspR : (I_edges.card : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast le_of_lt hsparse
    have hterm_nn : (0 : ℝ) ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (ℱ.card : ℝ) ^ ((2 : ℝ) / 3) := by positivity
    linarith
  · push Not at hsparse
    -- Build simple SlabWiring W on E = I_edges.image Prod.snd with E.card = I_edges.card and W.crossings = M.crossings!
    have hI_ne : I_edges.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e_def, _⟩ := hI_ne
    let E : Finset (Fin n × Fin n) := I_edges.image Prod.snd
    have hE_card : E.card = I_edges.card := Finset.card_image_of_injOn hpair_inj
    let invE : Fin n × Fin n → κ × (Fin n × Fin n) := fun q =>
      if h : ∃ e ∈ I_edges, e.2 = q then h.choose else e_def
    have hinvE_spec : ∀ q ∈ E, invE q ∈ I_edges ∧ (invE q).2 = q := by
      intro q hq
      have hex : ∃ e ∈ I_edges, e.2 = q := Finset.mem_image.mp hq
      simp only [invE, dif_pos hex]
      exact hex.choose_spec
    have hinvE_left : ∀ e ∈ I_edges, invE e.2 = e := fun e he => by
      have hq : e.2 ∈ E := Finset.mem_image_of_mem _ he
      exact hpair_inj (hinvE_spec e.2 hq).1 he (hinvE_spec e.2 hq).2
    let W : SlabWiring n E :=
      { edge_lt := fun q hq => by
          have ⟨hI, h2⟩ := hinvE_spec q hq
          have := M.edge_lt (invE q) hI
          rwa [h2] at this
        posL := fun s q => M.posL s (invE q)
        posR := fun s q => M.posR s (invE q)
        posL_inj := fun s q₁ h1 q₂ h2 hEq => by
          have h1' : invE q₁ ∈ multiActiveEdges I_edges (fun e => e.2.1) (fun e => e.2.2) s := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h1
            have ⟨hI, h2eq⟩ := hinvE_spec q₁ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have h2' : invE q₂ ∈ multiActiveEdges I_edges (fun e => e.2.1) (fun e => e.2.2) s := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h2
            have ⟨hI, h2eq⟩ := hinvE_spec q₂ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have heq := M.posL_inj s h1' h2' hEq
          rw [← (hinvE_spec q₁ (Finset.mem_filter.mp h1).1).2, ← (hinvE_spec q₂ (Finset.mem_filter.mp h2).1).2, heq]
        posR_inj := fun s q₁ h1 q₂ h2 hEq => by
          have h1' : invE q₁ ∈ multiActiveEdges I_edges (fun e => e.2.1) (fun e => e.2.2) s := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h1
            have ⟨hI, h2eq⟩ := hinvE_spec q₁ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have h2' : invE q₂ ∈ multiActiveEdges I_edges (fun e => e.2.1) (fun e => e.2.2) s := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h2
            have ⟨hI, h2eq⟩ := hinvE_spec q₂ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have heq := M.posR_inj s h1' h2' hEq
          rw [← (hinvE_spec q₁ (Finset.mem_filter.mp h1).1).2, ← (hinvE_spec q₂ (Finset.mem_filter.mp h2).1).2, heq]
        above := fun k q => M.above k (invE q)
        pass_order := fun k q₁ h1 q₂ h2 => by
          have h1' : invE q₁ ∈ multiPassingEdges I_edges (fun e => e.2.1) (fun e => e.2.2) k := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h1
            have ⟨hI, h2eq⟩ := hinvE_spec q₁ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have h2' : invE q₂ ∈ multiPassingEdges I_edges (fun e => e.2.1) (fun e => e.2.2) k := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h2
            have ⟨hI, h2eq⟩ := hinvE_spec q₂ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          exact M.pass_order k (invE q₁) h1' (invE q₂) h2'
        pass_above_end := fun k q hq q' hq' => by
          have h1' : invE q ∈ multiPassingEdges I_edges (fun e => e.2.1) (fun e => e.2.2) k := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp hq
            have ⟨hI, h2eq⟩ := hinvE_spec q hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have h2' : invE q' ∈ multiEndingEdges I_edges (fun e => e.2.2) k := by
            obtain ⟨hqE, hb⟩ := Finset.mem_filter.mp hq'
            have ⟨hI, h2eq⟩ := hinvE_spec q' hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact hb⟩
          exact M.pass_above_end k (invE q) h1' (invE q') h2'
        pass_above_start := fun k q hq q' hq' => by
          have h1' : invE q ∈ multiPassingEdges I_edges (fun e => e.2.1) (fun e => e.2.2) k := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp hq
            have ⟨hI, h2eq⟩ := hinvE_spec q hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have h2' : invE q' ∈ multiStartingEdges I_edges (fun e => e.2.1) k := by
            obtain ⟨hqE, ha⟩ := Finset.mem_filter.mp hq'
            have ⟨hI, h2eq⟩ := hinvE_spec q' hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha⟩
          exact M.pass_above_start k (invE q) h1' (invE q') h2'
        pass_below_lt_above := fun k q₁ h1 q₂ h2 => by
          have h1' : invE q₁ ∈ multiPassingEdges I_edges (fun e => e.2.1) (fun e => e.2.2) k := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h1
            have ⟨hI, h2eq⟩ := hinvE_spec q₁ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          have h2' : invE q₂ ∈ multiPassingEdges I_edges (fun e => e.2.1) (fun e => e.2.2) k := by
            obtain ⟨hqE, ha, hb⟩ := Finset.mem_filter.mp h2
            have ⟨hI, h2eq⟩ := hinvE_spec q₂ hqE
            exact Finset.mem_filter.mpr ⟨hI, by dsimp only; rw [h2eq]; exact ha, by dsimp only; rw [h2eq]; exact hb⟩
          exact M.pass_below_lt_above k (invE q₁) h1' (invE q₂) h2' }
    have hW_cr : W.crossings = M.crossings := by
      unfold SlabWiring.crossings MultiSlabWiring.crossings
      refine Finset.sum_congr rfl fun s _ => ?_
      refine Finset.card_bij (fun p _ => (invE p.1, invE p.2)) ?_ ?_ ?_
      · intro ⟨q₁, q₂⟩ hp
        obtain ⟨hprod, hlt, hgt⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hprod
        obtain ⟨hq1E, ha1, hb1⟩ := Finset.mem_filter.mp h1
        obtain ⟨hq2E, ha2, hb2⟩ := Finset.mem_filter.mp h2
        have ⟨hI1, h21⟩ := hinvE_spec q₁ hq1E
        have ⟨hI2, h22⟩ := hinvE_spec q₂ hq2E
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hI1, by dsimp only; rw [h21]; exact ha1, by dsimp only; rw [h21]; exact hb1⟩,
           Finset.mem_filter.mpr ⟨hI2, by dsimp only; rw [h22]; exact ha2, by dsimp only; rw [h22]; exact hb2⟩⟩, hlt, hgt⟩
      · intro ⟨q₁, q₂⟩ hp₁ ⟨q₁', q₂'⟩ hp₂ hEq
        have h1a := Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1
        have h2a := Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1
        have heq1 := (hinvE_spec q₁ (Finset.mem_filter.mp h1a.1).1).2.symm.trans
          ((congrArg Prod.snd (congrArg Prod.fst hEq)).trans (hinvE_spec q₁' (Finset.mem_filter.mp h2a.1).1).2)
        have heq2 := (hinvE_spec q₂ (Finset.mem_filter.mp h1a.2).1).2.symm.trans
          ((congrArg Prod.snd (congrArg Prod.snd hEq)).trans (hinvE_spec q₂' (Finset.mem_filter.mp h2a.2).1).2)
        exact Prod.ext heq1 heq2
      · intro ⟨e₁, e₂⟩ hp
        obtain ⟨hprod, hlt, hgt⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hprod
        obtain ⟨h1I, ha1, hb1⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2I, ha2, hb2⟩ := Finset.mem_filter.mp h2
        refine ⟨(e₁.2, e₂.2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ h1I, ha1, hb1⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ h2I, ha2, hb2⟩⟩, ?_, ?_⟩,
          Prod.ext (hinvE_left e₁ h1I) (hinvE_left e₂ h2I)⟩
        · dsimp only [W]; rw [hinvE_left e₁ h1I, hinvE_left e₂ h2I]; exact hlt
        · dsimp only [W]; rw [hinvE_left e₁ h1I, hinvE_left e₂ h2I]; exact hgt
    have hcl := slabWiring_crossing_lemma W hn_pos (hE_card.symm ▸ hsparse)
    rw [hE_card, hW_cr] at hcl
    have hcrR : (M.crossings : ℝ) ≤ (ℱ.card : ℝ) ^ 2 / 2 := by
      have : (2 : ℝ) * (M.crossings : ℝ) ≤ (ℱ.card : ℝ) ^ 2 := by exact_mod_cast hcr_bound
      linarith
    have hcube : (I_edges.card : ℝ) ^ 3 ≤
        (4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (ℱ.card : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 := by
      have h1 : (I_edges.card : ℝ) ^ 3 ≤ 32 * (n : ℝ) ^ 2 * (ℱ.card : ℝ) ^ 2 := by
        have hpos : (0 : ℝ) < 64 * (n : ℝ) ^ 2 := by positivity
        have := (div_le_iff₀ hpos).mp (le_trans hcl hcrR)
        linarith
      have h2 : (4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (ℱ.card : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 =
          64 * (n : ℝ) ^ 2 * (ℱ.card : ℝ) ^ 2 := by
        rw [mul_pow, mul_pow, rpow_two_thirds_cube (Nat.cast_nonneg n),
          rpow_two_thirds_cube (Nat.cast_nonneg ℱ.card)]
        ring
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (ℱ.card : ℝ) ^ 2 := by positivity
      linarith
    have hI_le : (I_edges.card : ℝ) ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (ℱ.card : ℝ) ^ ((2 : ℝ) / 3) :=
      le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) hcube
    have hsumR : ((∑ c ∈ ℱ, (pts c).card : ℕ) : ℝ) ≤ (I_edges.card : ℝ) + (ℱ.card : ℝ) := by
      exact_mod_cast hI_card
    linarith

/-- Point–line incidence count `I(P, L) = ∑ ℓ ∈ L, |{p ∈ P | p ∈ ℓ}|`. -/
noncomputable def lineIncidences (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))) : ℕ :=
  ∑ ℓ ∈ L, (P.filter (fun p => p ∈ ℓ)).card

/-- **Szemerédi–Trotter Theorem (1983) — Topology-Free Wiring-Diagram Proof:**
For any finite point set `P` and finite line set `L` in `EuclideanSpace ℝ (Fin 2)`,
`I(P, L) ≤ 4 |P|^(2/3) |L|^(2/3) + 4 |P| + |L|`. -/
theorem szemeredi_trotter
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, IsLine ℓ) :
    (lineIncidences P L : ℝ) ≤
      4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
        4 * (P.card : ℝ) + (L.card : ℝ) := by
  classical
  -- Step 1: Collect ALL pairwise intersection points of distinct lines in L, plus P, into a finite set Q!
  let interPts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((L ×ˢ L).filter (fun p => p.1 ≠ p.2 ∧ ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ p.1 ∧ q ∈ p.2)).image
      (fun p => if h : ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ p.1 ∧ q ∈ p.2 then h.choose else 0)
  let Q := P ∪ interPts
  -- Apply generic rotation tilt to (Q, L) so ALL distinct points in Q have distinct x-coordinates
  -- AND every line in L is non-vertical!
  obtain ⟨u, v, huv, hQ_axes, hL_nonvert⟩ := exists_rotation_generic Q L hL
  -- Sort the rotated points P' = P.image (rotUnit u v) by strictly increasing x-coordinate!
  let P' := P.image (rotUnit u v)
  have hP'_card : P'.card = P.card := Finset.card_image_of_injective P (rotUnit_injective huv)
  let X_P : Finset ℝ := P'.image (fun p => p 0)
  have hx_inj_P' : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 2) => p 0) P' := by
    intro a ha b hb hEq
    rcases Finset.mem_image.mp ha with ⟨p, hpP, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hqP, rfl⟩
    by_contra hne
    have hpq : p ≠ q := fun h => hne (congrArg (rotUnit u v) h)
    exact (hQ_axes p (Finset.mem_union_left _ hpP) q (Finset.mem_union_left _ hqP) hpq).1 hEq
  have hXP_card : X_P.card = P.card := by
    rw [Finset.card_image_of_injOn hx_inj_P', hP'_card]
  let n := P.card
  let φx : Fin n ↪o ℝ := X_P.orderEmbOfFin hXP_card
  let x : Fin n → ℝ := fun k => φx k
  have hx_strict : StrictMono x := φx.strictMono
  have hx_mem_P' : ∀ k : Fin n, ∃ p ∈ P', p 0 = x k := fun k =>
    Finset.mem_image.mp (X_P.orderEmbOfFin_mem hXP_card k)
  let ptOf : Fin n → EuclideanSpace ℝ (Fin 2) := fun k => (hx_mem_P' k).choose
  have hptOf_mem : ∀ k : Fin n, ptOf k ∈ P' := fun k => (hx_mem_P' k).choose_spec.1
  have hptOf_x : ∀ k : Fin n, ptOf k 0 = x k := fun k => (hx_mem_P' k).choose_spec.2
  let y : Fin n → ℝ := fun k => ptOf k 1
  -- Parameterize every rotated line ℓ' = rotUnitLine huv ℓ as a linear function f_ℓ(t) = m_ℓ * t + b_ℓ!
  let slopeIntercept : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) → ℝ × ℝ := fun ℓ =>
    if h : IsLine ℓ then
      let h2 := isLine_exists_two_points h
      let a := rotUnit u v h2.choose
      let b := rotUnit u v h2.choose_spec.choose
      let m := (b 1 - a 1) / (b 0 - a 0)
      (m, a 1 - m * a 0)
    else (0, 0)
  let f : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) → ℝ → ℝ := fun ℓ t =>
    (slopeIntercept ℓ).1 * t + (slopeIntercept ℓ).2
  have hf_iff : ∀ ℓ ∈ L, ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ rotUnitLine huv ℓ ↔ f ℓ (p 0) = p 1 := by
    intro ℓ hℓL p
    have hℓ := hL ℓ hℓL
    let h2 := isLine_exists_two_points hℓ
    let a₀ := h2.choose
    let b₀ := h2.choose_spec.choose
    have hab₀ : a₀ ≠ b₀ := h2.choose_spec.choose_spec.1
    have ha₀ : a₀ ∈ ℓ := h2.choose_spec.choose_spec.2.1
    have hb₀ : b₀ ∈ ℓ := h2.choose_spec.choose_spec.2.2
    let a := rotUnit u v a₀
    let b := rotUnit u v b₀
    have hab_x : b 0 - a 0 ≠ 0 := sub_ne_zero.mpr (hL_nonvert ℓ hℓL a₀ ha₀ b₀ hb₀ hab₀).symm
    have hab : a ≠ b := fun h => hab₀ (rotUnit_injective huv h)
    have hline_eq : rotUnitLine huv ℓ = lineThrough a b := by
      have hℓeq : lineThrough a₀ b₀ = ℓ := lineThrough_eq_of_mem hℓ hab₀ ha₀ hb₀
      rw [← hℓeq, rotUnitLine, lineThrough, AffineSubspace.map_span]
      simp [lineThrough, Set.image_pair, rotUnitLinearEquiv, a, b]
    rw [hline_eq, mem_lineThrough_iff_det2 hab]
    simp only [f, slopeIntercept, dif_pos hℓ, det2, PiLp.sub_apply]
    change (b 0 - a 0) * (p 1 - a 1) - (b 1 - a 1) * (p 0 - a 0) = 0 ↔
      (b 1 - a 1) / (b 0 - a 0) * p 0 + (a 1 - (b 1 - a 1) / (b 0 - a 0) * a 0) = p 1
    constructor
    · intro hdet
      field_simp [hab_x]
      linarith
    · intro hlin
      have hmul := congrArg (fun z => z * (b 0 - a 0)) hlin
      field_simp [hab_x] at hmul
      linarith
  -- Choose a single big closed interval [lo_all, hi_all] covering ALL x k and ALL intersection x-coordinates!
  let allX : Finset ℝ := {0} ∪ X_P ∪ (interPts.image (fun q => rotUnit u v q 0))
  have hallX_ne : allX.Nonempty := ⟨0, by simp [allX]⟩
  let lo0 : ℝ := allX.min' hallX_ne
  let hi0 : ℝ := allX.max' hallX_ne
  -- Verify incidence count equals the sum in xMonotone_one_inter_incidences_le!
  have hinc_eq : lineIncidences P L =
      ∑ ℓ ∈ L, ((Finset.univ : Finset (Fin n)).filter
        (fun k => lo0 ≤ x k ∧ x k ≤ hi0 ∧ f ℓ (x k) = y k)).card := by
    unfold lineIncidences
    refine Finset.sum_congr rfl fun ℓ hℓL => ?_
    symm
    refine Finset.card_bij (fun k _ => rotUnit u (-v) (ptOf k)) ?_ ?_ ?_
    · intro k hk
      obtain ⟨_, _, _, hfk⟩ := Finset.mem_filter.mp hk
      rcases Finset.mem_image.mp (hptOf_mem k) with ⟨p, hpP, hpEq⟩
      have hback : rotUnit u (-v) (ptOf k) = p := by rw [← hpEq, rotUnit_comp_inv huv]
      rw [hback]
      refine Finset.mem_filter.mpr ⟨hpP, ?_⟩
      rw [← mem_rotUnitLine_iff huv, hpEq, hf_iff ℓ hℓL (ptOf k), hptOf_x k]
      exact hfk
    · intro k₁ _ k₂ _ hEq
      have hptEq : ptOf k₁ = ptOf k₂ := by
        have := congrArg (rotUnit u v) hEq
        simpa [rotUnit_inv_comp huv] using this
      have hxEq : x k₁ = x k₂ := by rw [← hptOf_x k₁, ← hptOf_x k₂, hptEq]
      exact hx_strict.injective hxEq
    · intro p hp
      obtain ⟨hpP, hpℓ⟩ := Finset.mem_filter.mp hp
      have hp' : rotUnit u v p ∈ P' := Finset.mem_image_of_mem _ hpP
      have hxmem : rotUnit u v p 0 ∈ X_P := Finset.mem_image_of_mem _ hp'
      have hrng : Set.range φx = (X_P : Set ℝ) := X_P.range_orderEmbOfFin hXP_card
      have hxr : rotUnit u v p 0 ∈ Set.range φx := by rw [hrng]; exact hxmem
      obtain ⟨k, hkEq⟩ := Set.mem_range.mp hxr
      have hptEq : ptOf k = rotUnit u v p :=
        hx_inj_P' (hptOf_mem k) hp' ((hptOf_x k).trans hkEq)
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩, ?_⟩
      · exact Finset.min'_le allX (x k)
          (Finset.mem_union_left _ (Finset.mem_union_right _ (X_P.orderEmbOfFin_mem hXP_card k)))
      · exact Finset.le_max' allX (x k)
          (Finset.mem_union_left _ (Finset.mem_union_right _ (X_P.orderEmbOfFin_mem hXP_card k)))
      · rw [← hptOf_x k, show y k = ptOf k 1 from rfl, hptEq]
        exact (hf_iff ℓ hℓL (rotUnit u v p)).mp ((mem_rotUnitLine_iff huv).mpr hpℓ)
      · rw [hptEq, rotUnit_comp_inv huv]
  -- Apply xMonotone_one_inter_incidences_le!
  rw [hinc_eq]
  refine xMonotone_one_inter_incidences_le x y hx_strict L (fun _ => lo0) (fun _ => hi0) f ?_ ?_ ?_
  · intro ℓ _
    exact (continuousOn_const.mul continuousOn_id).add continuousOn_const
  · intro ℓ₁ h1 ℓ₂ h2 hne t₁ t₂ _ _ _ _ heq1 _ _ _ _ heq2
    let p₁ := mkPt t₁ (f ℓ₁ t₁)
    let p₂ := mkPt t₂ (f ℓ₁ t₂)
    have hp1_1 : p₁ ∈ rotUnitLine huv ℓ₁ := (hf_iff ℓ₁ h1 p₁).mpr (by simp [p₁])
    have hp1_2 : p₁ ∈ rotUnitLine huv ℓ₂ := (hf_iff ℓ₂ h2 p₁).mpr (by simp [p₁, heq1])
    have hp2_1 : p₂ ∈ rotUnitLine huv ℓ₁ := (hf_iff ℓ₁ h1 p₂).mpr (by simp [p₂])
    have hp2_2 : p₂ ∈ rotUnitLine huv ℓ₂ := (hf_iff ℓ₂ h2 p₂).mpr (by simp [p₂, heq2])
    have hline_ne : rotUnitLine huv ℓ₁ ≠ rotUnitLine huv ℓ₂ := fun h => hne (rotUnitLine_injective huv h)
    have hpeq : p₁ = p₂ := two_line_inter_subsingleton (isLine_rotUnitLine huv (hL ℓ₁ h1))
      (isLine_rotUnitLine huv (hL ℓ₂ h2)) hline_ne ⟨hp1_1, hp1_2⟩ ⟨hp2_1, hp2_2⟩
    simpa [p₁, p₂] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hpeq
  · intro ℓ₁ h1 ℓ₂ h2 hne k _ _ _ _ hfeq
    -- The intersection point q' = mkPt (x k) (f ℓ₁ (x k)) lies on rotUnitLine ℓ₁ ∩ rotUnitLine ℓ₂.
    let q' := mkPt (x k) (f ℓ₁ (x k))
    have hq'1 : q' ∈ rotUnitLine huv ℓ₁ := (hf_iff ℓ₁ h1 q').mpr (by simp [q'])
    have hq'2 : q' ∈ rotUnitLine huv ℓ₂ := (hf_iff ℓ₂ h2 q').mpr (by simp [q', hfeq])
    let q := rotUnit u (-v) q'
    have hq1 : q ∈ ℓ₁ := (mem_rotUnitLine_iff huv).mp (by rwa [rotUnit_inv_comp huv])
    have hq2 : q ∈ ℓ₂ := (mem_rotUnitLine_iff huv).mp (by rwa [rotUnit_inv_comp huv])
    have hq_inter : q ∈ interPts := by
      have hex : ∃ z : EuclideanSpace ℝ (Fin 2), z ∈ ℓ₁ ∧ z ∈ ℓ₂ := ⟨q, hq1, hq2⟩
      refine Finset.mem_image.mpr ⟨(ℓ₁, ℓ₂), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hne, hex⟩, ?_⟩
      rw [dif_pos hex]
      exact two_line_inter_subsingleton (hL ℓ₁ h1) (hL ℓ₂ h2) hne hex.choose_spec ⟨hq1, hq2⟩
    rcases Finset.mem_image.mp (hptOf_mem k) with ⟨p, hpP, hpEq⟩
    have hqp : q = p := by
      by_contra hqp_ne
      have hneq0 := (hQ_axes q (Finset.mem_union_right _ hq_inter) p (Finset.mem_union_left _ hpP) hqp_ne).1
      apply hneq0
      rw [rotUnit_inv_comp huv, hpEq, hptOf_x k]
      simp [q']
    have hq'eq : q' = ptOf k := by rw [← hpEq, ← hqp, rotUnit_inv_comp huv]
    simpa [q', y] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hq'eq

/-- **`k`-Rich Line Corollary of Szemerédi–Trotter (`k ≥ 2`):**
For any finite `P ⊂ ℝ²`, any finite set `L` of distinct lines each containing at least `k ≥ 2` points of `P`
satisfies `|L| ≤ 4096 |P|² / k³ + 16 |P| / k`. -/
theorem k_rich_lines_bound
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, IsLine ℓ)
    {k : ℕ} (hk : 2 ≤ k)
    (hrich : ∀ ℓ ∈ L, k ≤ (P.filter (fun p => p ∈ ℓ)).card) :
    (L.card : ℝ) ≤ 4096 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + 16 * (P.card : ℝ) / (k : ℝ) := by
  have hst := szemeredi_trotter P L hL
  have hlb_nat : k * L.card ≤ lineIncidences P L := by
    unfold lineIncidences
    calc k * L.card = ∑ _ℓ ∈ L, k := by simp [mul_comm]
      _ ≤ ∑ ℓ ∈ L, (P.filter (fun p => p ∈ ℓ)).card := Finset.sum_le_sum hrich
  have hlb : (k : ℝ) * (L.card : ℝ) ≤ (lineIncidences P L : ℝ) := by exact_mod_cast hlb_nat
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hcomb : ((k : ℝ) / 2) * (L.card : ℝ) ≤
      4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) + 4 * (P.card : ℝ) := by
    have hhalf : (k : ℝ) / 2 ≤ (k : ℝ) - 1 := by linarith
    have hLnn : (0 : ℝ) ≤ (L.card : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hhalf hLnn
    linarith
  have hterm1_nn : (0 : ℝ) ≤ 4096 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by positivity
  have hterm2_nn : (0 : ℝ) ≤ 16 * (P.card : ℝ) / (k : ℝ) := by positivity
  by_cases hcase : 4 * (P.card : ℝ) ≤ 4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3)
  · have h1 : ((k : ℝ) / 2) * (L.card : ℝ) ≤
        8 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) := by linarith
    have hcube : (((k : ℝ) / 2) * (L.card : ℝ)) ^ 3 ≤
        (8 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    rw [mul_pow, mul_pow, mul_pow,
      rpow_two_thirds_cube (Nat.cast_nonneg P.card),
      rpow_two_thirds_cube (Nat.cast_nonneg L.card)] at hcube
    by_cases hL0 : L.card = 0
    · simp [hL0]; positivity
    · have hLpos : (0 : ℝ) < (L.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL0)
      have hL2pos : (0 : ℝ) < (L.card : ℝ) ^ 2 := pow_pos hLpos 2
      have hcancel : ((k : ℝ) / 2) ^ 3 * (L.card : ℝ) ≤ 8 ^ 3 * (P.card : ℝ) ^ 2 := by
        nlinarith [hcube, hL2pos]
      have hL_le : (L.card : ℝ) ≤ 4096 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
        rw [le_div_iff₀ (pow_pos hk_pos 3)]
        nlinarith
      linarith
  · push Not at hcase
    have h1 : ((k : ℝ) / 2) * (L.card : ℝ) ≤ 8 * (P.card : ℝ) := by linarith
    have hL_le : (L.card : ℝ) ≤ 16 * (P.card : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hk_pos]; linarith
    linarith

/-- **`k`-Rich Incidences Bound (`k ≥ 2`):**
The total number of incidences on any family `L` of `k`-rich lines (`k ≥ 2`) satisfies
`I(P, L) ≤ 4096 |P|² / k² + 16 |P|`. -/
theorem k_rich_incidences_bound
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, IsLine ℓ)
    {k : ℕ} (hk : 2 ≤ k)
    (hrich : ∀ ℓ ∈ L, k ≤ (P.filter (fun p => p ∈ ℓ)).card) :
    (lineIncidences P L : ℝ) ≤ 4096 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2 + 16 * (P.card : ℝ) := by
  have hst := szemeredi_trotter P L hL
  have hlb_nat : k * L.card ≤ lineIncidences P L := by
    unfold lineIncidences
    calc k * L.card = ∑ _ℓ ∈ L, k := by simp [mul_comm]
      _ ≤ ∑ ℓ ∈ L, (P.filter (fun p => p ∈ ℓ)).card := Finset.sum_le_sum hrich
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hL_le_I : (L.card : ℝ) ≤ (lineIncidences P L : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_pos]; exact_mod_cast (mul_comm k L.card ▸ hlb_nat)
  have hL_half : (L.card : ℝ) ≤ (lineIncidences P L : ℝ) / 2 := by
    have : (lineIncidences P L : ℝ) / (k : ℝ) ≤ (lineIncidences P L : ℝ) / 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hkR
    linarith
  have hL23 : (L.card : ℝ) ^ ((2 : ℝ) / 3) ≤ ((lineIncidences P L : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hL_le_I (by norm_num)
  have hmain : (lineIncidences P L : ℝ) / 2 ≤
      4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * ((lineIncidences P L : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3) +
        4 * (P.card : ℝ) := by
    have hmul : 4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) ≤
        4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * ((lineIncidences P L : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hL23 (by positivity)
    linarith
  have ht1_nn : (0 : ℝ) ≤ 4096 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2 := by positivity
  have ht2_nn : (0 : ℝ) ≤ 16 * (P.card : ℝ) := by positivity
  by_cases hcase : 4 * (P.card : ℝ) ≤
      4 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * ((lineIncidences P L : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3)
  · have h1 : (lineIncidences P L : ℝ) / 2 ≤
        8 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * ((lineIncidences P L : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3) := by linarith
    have hcube : ((lineIncidences P L : ℝ) / 2) ^ 3 ≤
        (8 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * ((lineIncidences P L : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    rw [mul_pow, mul_pow,
      rpow_two_thirds_cube (Nat.cast_nonneg P.card),
      rpow_two_thirds_cube (div_nonneg (Nat.cast_nonneg _) (le_of_lt hk_pos))] at hcube
    by_cases hI0 : lineIncidences P L = 0
    · simp [hI0]; positivity
    · have hIpos : (0 : ℝ) < (lineIncidences P L : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hI0)
      have hI2pos : (0 : ℝ) < (lineIncidences P L : ℝ) ^ 2 := pow_pos hIpos 2
      have halg : (lineIncidences P L : ℝ) ^ 2 * ((lineIncidences P L : ℝ) / 8) ≤
          (lineIncidences P L : ℝ) ^ 2 * (512 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2) := by
        have hL : (lineIncidences P L : ℝ) ^ 2 * ((lineIncidences P L : ℝ) / 8) =
            ((lineIncidences P L : ℝ) / 2) ^ 3 := by ring
        have hR : (lineIncidences P L : ℝ) ^ 2 * (512 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2) =
            8 ^ 3 * (P.card : ℝ) ^ 2 * ((lineIncidences P L : ℝ) / (k : ℝ)) ^ 2 := by ring
        linarith
      have hI_le : (lineIncidences P L : ℝ) / 8 ≤ 512 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2 :=
        le_of_mul_le_mul_left halg hI2pos
      have hmul8 : 8 * (512 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2) = 4096 * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 2 := by ring
      linarith
  · push Not at hcase
    linarith

/-- **Beck's Theorem (1983) — Explicit Constants Derived from Szemerédi–Trotter:**
For EVERY finite point set `P : Finset (EuclideanSpace ℝ (Fin 2))`, EITHER:
1. There exists an affine line `ℓ` containing at least `(1 / 1024) * |P|` points of `P`, OR
2. `P` determines at least `(1 / (4 * 262144 ^ 2)) * |P| ^ 2` distinct affine lines. -/
theorem beck_theorem (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (∃ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      IsLine ℓ ∧ ((P.card : ℝ) / 1024) ≤ ((P.filter (fun p => p ∈ ℓ)).card : ℝ)) ∨
    ((P.card : ℝ) ^ 2 / (4 * (262144 : ℝ) ^ 2) ≤ ((linesOf P).card : ℝ)) := by
  classical
  by_cases hP0 : P.card = 0
  · right; simp [hP0]
  by_cases hP1 : P.card = 1
  · left
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hP1
    let ℓ := lineThrough p (p + mkPt 1 0)
    have hne : p ≠ p + mkPt 1 0 := fun h => by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
      simp [PiLp.add_apply] at this
    refine ⟨ℓ, isLine_lineThrough hne, ?_⟩
    have hmem : p ∈ ({p} : Finset (EuclideanSpace ℝ (Fin 2))).filter (fun q => q ∈ ℓ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_singleton_self p, mem_lineThrough_left _ _⟩
    have h1 : 1 ≤ (({p} : Finset (EuclideanSpace ℝ (Fin 2))).filter (fun q => q ∈ ℓ)).card :=
      Finset.card_pos.mpr ⟨p, hmem⟩
    have h1R : (1 : ℝ) ≤ (({p} : Finset (EuclideanSpace ℝ (Fin 2))).filter (fun q => q ∈ ℓ)).card := by
      exact_mod_cast h1
    simp only [Finset.card_singleton, Nat.cast_one]
    linarith
  have hP2 : 2 ≤ P.card := by omega
  by_cases hcol : ∃ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      IsLine ℓ ∧ ((P.card : ℝ) / 1024) ≤ ((P.filter (fun p => p ∈ ℓ)).card : ℝ)
  · exact Or.inl hcol
  right
  push Not at hcol
  -- Every ordered pair (p, q) ∈ P × P with p ≠ q lies on a UNIQUE line ℓ = lineThrough p q ∈ linesOf P!
  let ordPairs := (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)
  have hord_card : ordPairs.card = P.card * (P.card - 1) := by
    have h1 : ordPairs.card + P.card = (P ×ˢ P).card := by
      have hdisj : Disjoint ordPairs (P.image (fun p => (p, p))) := by
        rw [Finset.disjoint_left]
        intro pq h1 h2
        rcases Finset.mem_image.mp h2 with ⟨p, _, rfl⟩
        exact (Finset.mem_filter.mp h1).2 rfl
      have hunion : ordPairs ∪ P.image (fun p => (p, p)) = P ×ˢ P := by
        ext ⟨p, q⟩
        simp only [ordPairs, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro (⟨h, _⟩ | ⟨r, hr, hEq⟩)
          · exact h
          · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩; exact ⟨hr, hr⟩
        · rintro ⟨hp, hq⟩
          by_cases hpq : p = q
          · subst hpq; exact Or.inr ⟨p, hp, rfl⟩
          · exact Or.inl ⟨⟨hp, hq⟩, hpq⟩
      have hdiag : (P.image (fun p => (p, p))).card = P.card :=
        Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
      rw [← hdiag, ← Finset.card_union_of_disjoint hdisj, hunion]
    rw [Finset.card_product] at h1
    have hmul : P.card * (P.card - 1) + P.card = P.card * P.card := by
      cases hc : P.card with
      | zero => simp
      | succ m => simp [Nat.mul_succ]
    omega
  -- Partition ordPairs by line ℓ ∈ linesOf P:
  let linePairs (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Finset _ :=
    ((P.filter (fun p => p ∈ ℓ)) ×ˢ (P.filter (fun p => p ∈ ℓ))).filter (fun pq => pq.1 ≠ pq.2)
  have hpart_pairs : ordPairs.card = ∑ ℓ ∈ linesOf P, (linePairs ℓ).card := by
    have hEq : ordPairs = (linesOf P).biUnion linePairs := by
      ext ⟨p, q⟩
      simp only [ordPairs, linePairs, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨hp, hq⟩, hpq⟩
        exact ⟨lineThrough p q, mem_linesOf_iff.mpr ⟨p, hp, q, hq, hpq, rfl⟩,
          ⟨⟨hp, mem_lineThrough_left p q⟩, ⟨hq, mem_lineThrough_right p q⟩⟩, hpq⟩
      · rintro ⟨ℓ, _, ⟨⟨hp, _⟩, ⟨hq, _⟩⟩, hpq⟩
        exact ⟨⟨hp, hq⟩, hpq⟩
    have hdisj : Set.PairwiseDisjoint ((linesOf P) : Set _) linePairs := by
      intro ℓ₁ h1 ℓ₂ h2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨p, q⟩ h1m h2m
      simp only [linePairs, Finset.mem_filter, Finset.mem_product] at h1m h2m
      exact hne (affine_line_eq_of_two_mem (isLine_of_mem_linesOf h1) (isLine_of_mem_linesOf h2)
        h1m.2 h1m.1.1.2 h1m.1.2.2 h2m.1.1.2 h2m.1.2.2)
    rw [hEq, Finset.card_biUnion hdisj]
  have hlinePairs_le : ∀ ℓ, (linePairs ℓ).card ≤ (P.filter (fun p => p ∈ ℓ)).card ^ 2 := fun ℓ =>
    le_trans (Finset.card_filter_le _ _) (by simp [Finset.card_product, sq])
  -- Split linesOf P into poor lines (< K = 2^18 = 262144) and rich lines (≥ K)!
  let K : ℕ := 2 ^ 18
  have hKval : K = 262144 := by norm_num [K]
  let L_poor := (linesOf P).filter (fun ℓ => (P.filter (fun p => p ∈ ℓ)).card < K)
  let L_rich := (linesOf P).filter (fun ℓ => K ≤ (P.filter (fun p => p ∈ ℓ)).card)
  have hsplit : ∑ ℓ ∈ linesOf P, (linePairs ℓ).card =
      (∑ ℓ ∈ L_poor, (linePairs ℓ).card) + (∑ ℓ ∈ L_rich, (linePairs ℓ).card) := by
    rw [← Finset.sum_filter_add_sum_filter_not (linesOf P) (fun ℓ => (P.filter (fun p => p ∈ ℓ)).card < K)]
    congr 1; apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ℓ; simp [L_rich]
  -- Bound rich lines using dyadic buckets j ∈ [18, J] where 2^J > P.card!
  let J : ℕ := P.card + 19
  let bucket (j : ℕ) := (linesOf P).filter (fun ℓ =>
    2 ^ j ≤ (P.filter (fun p => p ∈ ℓ)).card ∧ (P.filter (fun p => p ∈ ℓ)).card < 2 ^ (j + 1))
  have hrich_sub : L_rich ⊆ (Finset.Ico 18 J).biUnion bucket := by
    intro ℓ hℓ
    obtain ⟨hℓL, hKge⟩ := Finset.mem_filter.mp hℓ
    let m := (P.filter (fun p => p ∈ ℓ)).card
    have hm_le : m ≤ P.card := Finset.card_filter_le _ _
    have hm_pos : 0 < m := by omega
    let j := Nat.log 2 m
    have hj_lo : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (ne_of_gt hm_pos)
    have hj_hi : m < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    have hj18 : 18 ≤ j := by
      by_contra hlt; push Not at hlt
      have : 2 ^ (j + 1) ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hjJ : j < J := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      omega
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨hj18, hjJ⟩,
      Finset.mem_filter.mpr ⟨hℓL, hj_lo, hj_hi⟩⟩
  -- For each dyadic bucket j ≥ 18:
  -- (a) If bucket j is nonempty, then 2^j < |P| / 1024!
  -- (b) ∑_{ℓ ∈ bucket j} (linePairs ℓ).card ≤ 4 * 4^j * |bucket j| ≤ 16384 |P|² / 2^j + 64 |P| * 2^j!
  have hbucket_bound : ∀ j ∈ Finset.Ico 18 J,
      ((∑ ℓ ∈ bucket j, (linePairs ℓ).card : ℕ) : ℝ) ≤
        (16384 * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ j) +
        (if ((2 : ℝ) ^ j < (P.card : ℝ) / 1024) then 64 * (P.card : ℝ) * (2 : ℝ) ^ j else 0) := by
    intro j hj
    have hj18 : 18 ≤ j := (Finset.mem_Ico.mp hj).1
    by_cases hne : (bucket j).Nonempty
    · obtain ⟨ℓ₀, hℓ₀⟩ := hne
      have hℓ₀L := (Finset.mem_filter.mp hℓ₀).1
      have hℓ₀_lo := (Finset.mem_filter.mp hℓ₀).2.1
      have hlt_col := hcol ℓ₀ (isLine_of_mem_linesOf hℓ₀L)
      have h2j_lt : (2 : ℝ) ^ j < (P.card : ℝ) / 1024 := by
        have hloR : (2 : ℝ) ^ j ≤ ((P.filter (fun p => p ∈ ℓ₀)).card : ℝ) := by exact_mod_cast hℓ₀_lo
        linarith
      rw [if_pos h2j_lt]
      have h2j_ge2 : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hkr := k_rich_lines_bound P (bucket j)
        (fun ℓ hℓ => isLine_of_mem_linesOf (Finset.mem_filter.mp hℓ).1) h2j_ge2
        (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2.1)
      have hpair_nat : ∑ ℓ ∈ bucket j, (linePairs ℓ).card ≤ (bucket j).card * (2 ^ (j + 1)) ^ 2 := by
        calc ∑ ℓ ∈ bucket j, (linePairs ℓ).card
            ≤ ∑ ℓ ∈ bucket j, (P.filter (fun p => p ∈ ℓ)).card ^ 2 := Finset.sum_le_sum fun ℓ _ => hlinePairs_le ℓ
          _ ≤ ∑ _ℓ ∈ bucket j, (2 ^ (j + 1)) ^ 2 := Finset.sum_le_sum fun ℓ hℓ =>
              Nat.pow_le_pow_left (le_of_lt (Finset.mem_filter.mp hℓ).2.2) 2
          _ = (bucket j).card * (2 ^ (j + 1)) ^ 2 := by simp
      have hpairR : ((∑ ℓ ∈ bucket j, (linePairs ℓ).card : ℕ) : ℝ) ≤
          ((bucket j).card : ℝ) * (4 * ((2 : ℝ) ^ j) ^ 2) := by
        have h : ((∑ ℓ ∈ bucket j, (linePairs ℓ).card : ℕ) : ℝ) ≤
            ((bucket j).card : ℝ) * ((2 : ℝ) ^ (j + 1)) ^ 2 := by exact_mod_cast hpair_nat
        have hpow : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * ((2 : ℝ) ^ j) ^ 2 := by rw [pow_succ]; ring
        rw [hpow] at h
        exact h
      have hkr' : ((bucket j).card : ℝ) ≤
          4096 * (P.card : ℝ) ^ 2 / ((2 : ℝ) ^ j) ^ 3 + 16 * (P.card : ℝ) / (2 : ℝ) ^ j := by
        simpa [Nat.cast_pow] using hkr
      have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hmul := mul_le_mul_of_nonneg_right hkr' (show (0 : ℝ) ≤ 4 * ((2 : ℝ) ^ j) ^ 2 by positivity)
      have halg : (4096 * (P.card : ℝ) ^ 2 / ((2 : ℝ) ^ j) ^ 3 + 16 * (P.card : ℝ) / (2 : ℝ) ^ j) *
          (4 * ((2 : ℝ) ^ j) ^ 2) =
          16384 * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ j + 64 * (P.card : ℝ) * (2 : ℝ) ^ j := by
        field_simp [ne_of_gt h2j_pos]; ring
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty, Nat.cast_zero]
      split_ifs <;> positivity
  -- Sum the two geometric series cleanly!
  have hgeom_down : ∑ j ∈ Finset.Ico 18 J, (1 : ℝ) / (2 : ℝ) ^ j ≤ 2 / (2 : ℝ) ^ 18 := by
    have hshift : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 : ℝ) / (2 : ℝ) ^ (18 + i) ≤ 2 / (2 : ℝ) ^ 18 := by
      intro m
      have h1 : ∑ i ∈ Finset.range m, (1 : ℝ) / (2 : ℝ) ^ (18 + i) =
          (1 / (2 : ℝ) ^ 18) * ∑ i ∈ Finset.range m, ((1 : ℝ) / 2) ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add, one_div_pow]; ring
      rw [h1, geom_sum_eq (by norm_num : (1 : ℝ) / 2 ≠ 1)]
      have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ m := by positivity
      have h2 : (((1 : ℝ) / 2) ^ m - 1) / ((1 : ℝ) / 2 - 1) = 2 * (1 - ((1 : ℝ) / 2) ^ m) := by ring
      have hpos : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ 18 := by positivity
      nlinarith
    have hIco : Finset.Ico 18 J = (Finset.range (J - 18)).image (fun i => 18 + i) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨j - 18, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [hIco, Finset.sum_image (fun _ _ _ _ h => by omega)]
    exact hshift (J - 18)
  have hgeom_up : ∑ j ∈ Finset.Ico 18 J,
      (if ((2 : ℝ) ^ j < (P.card : ℝ) / 1024) then (2 : ℝ) ^ j else 0) ≤ (P.card : ℝ) / 512 := by
    let S := (Finset.Ico 18 J).filter (fun j => (2 : ℝ) ^ j < (P.card : ℝ) / 1024)
    rw [← Finset.sum_filter]
    change ∑ j ∈ S, (2 : ℝ) ^ j ≤ (P.card : ℝ) / 512
    by_cases hSne : S.Nonempty
    · let jMax := S.max' hSne
      have hjMax_mem : jMax ∈ S := Finset.max'_mem S hSne
      have hjMax_lt : (2 : ℝ) ^ jMax < (P.card : ℝ) / 1024 := (Finset.mem_filter.mp hjMax_mem).2
      have hsub : S ⊆ Finset.range (jMax + 1) := fun j hj =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S j hj))
      calc ∑ j ∈ S, (2 : ℝ) ^ j
          ≤ ∑ j ∈ Finset.range (jMax + 1), (2 : ℝ) ^ j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = (2 : ℝ) ^ (jMax + 1) - 1 := by
            rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; ring
        _ ≤ 2 * (2 : ℝ) ^ jMax := by rw [pow_succ]; linarith
        _ ≤ (P.card : ℝ) / 512 := by linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hSne
      rw [hSne, Finset.sum_empty]; positivity
  -- Combine to show ∑_{ℓ ∈ L_rich} (linePairs ℓ).card ≤ |P|² / 4!
  have hrich_le : ((∑ ℓ ∈ L_rich, (linePairs ℓ).card : ℕ) : ℝ) ≤ (P.card : ℝ) ^ 2 / 4 := by
    have hdisj_b : Set.PairwiseDisjoint ((Finset.Ico 18 J) : Set ℕ) bucket := by
      intro j₁ _ j₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro ℓ h1 h2
      have hb1 := (Finset.mem_filter.mp h1).2
      have hb2 := (Finset.mem_filter.mp h2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : 2 ^ (j₁ + 1) ≤ 2 ^ j₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 2 ^ (j₂ + 1) ≤ 2 ^ j₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    have hsub_sum : ∑ ℓ ∈ L_rich, (linePairs ℓ).card ≤
        ∑ j ∈ Finset.Ico 18 J, ∑ ℓ ∈ bucket j, (linePairs ℓ).card := by
      calc ∑ ℓ ∈ L_rich, (linePairs ℓ).card
          ≤ ∑ ℓ ∈ (Finset.Ico 18 J).biUnion bucket, (linePairs ℓ).card :=
            Finset.sum_le_sum_of_subset hrich_sub
        _ = ∑ j ∈ Finset.Ico 18 J, ∑ ℓ ∈ bucket j, (linePairs ℓ).card := Finset.sum_biUnion hdisj_b
    have hsub_sumR : ((∑ ℓ ∈ L_rich, (linePairs ℓ).card : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.Ico 18 J, ((∑ ℓ ∈ bucket j, (linePairs ℓ).card : ℕ) : ℝ) := by
      exact_mod_cast hsub_sum
    have hstep1 : ∑ j ∈ Finset.Ico 18 J, ((∑ ℓ ∈ bucket j, (linePairs ℓ).card : ℕ) : ℝ) ≤
        (16384 * (P.card : ℝ) ^ 2) * (∑ j ∈ Finset.Ico 18 J, (1 : ℝ) / (2 : ℝ) ^ j) +
        (64 * (P.card : ℝ)) * (∑ j ∈ Finset.Ico 18 J,
          if ((2 : ℝ) ^ j < (P.card : ℝ) / 1024) then (2 : ℝ) ^ j else 0) := by
      calc ∑ j ∈ Finset.Ico 18 J, ((∑ ℓ ∈ bucket j, (linePairs ℓ).card : ℕ) : ℝ)
          ≤ ∑ j ∈ Finset.Ico 18 J,
              ((16384 * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ j) +
                (if ((2 : ℝ) ^ j < (P.card : ℝ) / 1024) then 64 * (P.card : ℝ) * (2 : ℝ) ^ j else 0)) :=
            Finset.sum_le_sum hbucket_bound
        _ = (∑ j ∈ Finset.Ico 18 J, 16384 * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ j) +
            (∑ j ∈ Finset.Ico 18 J,
              if ((2 : ℝ) ^ j < (P.card : ℝ) / 1024) then 64 * (P.card : ℝ) * (2 : ℝ) ^ j else 0) :=
            Finset.sum_add_distrib
        _ = _ := by
            congr 1
            · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
            · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    have h1 := mul_le_mul_of_nonneg_left hgeom_down (show (0 : ℝ) ≤ 16384 * (P.card : ℝ) ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hgeom_up (show (0 : ℝ) ≤ 64 * (P.card : ℝ) by positivity)
    have hconst1 : 16384 * (P.card : ℝ) ^ 2 * (2 / (2 : ℝ) ^ 18) = (P.card : ℝ) ^ 2 / 8 := by ring
    have hconst2 : 64 * (P.card : ℝ) * ((P.card : ℝ) / 512) = (P.card : ℝ) ^ 2 / 8 := by ring
    linarith
  -- Total ordered pairs = |P|(|P| - 1) ≥ |P|² / 2 (since |P| ≥ 2), so poor lines get ≥ |P|² / 4!
  have hord_lb : (P.card : ℝ) ^ 2 / 2 ≤ (ordPairs.card : ℝ) := by
    have h2R : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hP2
    have hcast : (ordPairs.card : ℝ) = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
      rw [hord_card, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ P.card), Nat.cast_one]
    nlinarith
  have hpoor_ub : ((∑ ℓ ∈ L_poor, (linePairs ℓ).card : ℕ) : ℝ) ≤ ((linesOf P).card : ℝ) * (262144 : ℝ) ^ 2 := by
    have hnat : ∑ ℓ ∈ L_poor, (linePairs ℓ).card ≤ (linesOf P).card * K ^ 2 := by
      calc ∑ ℓ ∈ L_poor, (linePairs ℓ).card
          ≤ ∑ ℓ ∈ L_poor, (P.filter (fun p => p ∈ ℓ)).card ^ 2 := Finset.sum_le_sum fun ℓ _ => hlinePairs_le ℓ
        _ ≤ ∑ _ℓ ∈ L_poor, K ^ 2 := Finset.sum_le_sum fun ℓ hℓ =>
            Nat.pow_le_pow_left (le_of_lt (Finset.mem_filter.mp hℓ).2) 2
        _ = L_poor.card * K ^ 2 := by simp
        _ ≤ (linesOf P).card * K ^ 2 := Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    rw [hKval] at hnat
    exact_mod_cast hnat
  have hsplitR : (ordPairs.card : ℝ) =
      ((∑ ℓ ∈ L_poor, (linePairs ℓ).card : ℕ) : ℝ) + ((∑ ℓ ∈ L_rich, (linePairs ℓ).card : ℕ) : ℝ) := by
    rw [hpart_pairs, hsplit, Nat.cast_add]
  rw [div_le_iff₀ (by positivity)]
  linarith

end SzemerediTrotterBeck

/-! ## Section 5: Unit-Distance `O(n^(4/3))` & Pinned/Global Distinct-Distance `Ω(n^(4/5))` Corollaries -/

section UnitAndDistinctDistances

/-! ### 5A. Explicit Circle–Circle Intersection Finset (`≤ 2`) & Unit-Distance `O(n^(4/3))` -/

/-- Explicit finite set of at most `2` candidate intersection points of two circles `(c₁, r₁)` and `(c₂, r₂)`. -/
noncomputable def circleInterPts (c₁ : EuclideanSpace ℝ (Fin 2)) (r₁ : ℝ)
    (c₂ : EuclideanSpace ℝ (Fin 2)) (r₂ : ℝ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  let d := c₂ - c₁
  let L2 := normSq2 d
  let α := (r₁ ^ 2 - r₂ ^ 2 + L2) / (2 * L2)
  let foot := c₁ + α • d
  let nvec := mkPt (-d 1) (d 0)
  let t := Real.sqrt ((r₁ ^ 2 - α ^ 2 * L2) / L2)
  {foot + t • nvec, foot - t • nvec}

lemma circleInterPts_card_le_two (c₁ : EuclideanSpace ℝ (Fin 2)) (r₁ : ℝ)
    (c₂ : EuclideanSpace ℝ (Fin 2)) (r₂ : ℝ) :
    (circleInterPts c₁ r₁ c₂ r₂).card ≤ 2 :=
  Finset.card_le_two

lemma mem_circleInterPts_of_dist {c₁ c₂ p : EuclideanSpace ℝ (Fin 2)} {r₁ r₂ : ℝ}
    (hc : c₁ ≠ c₂) (h1 : dist p c₁ = r₁) (h2 : dist p c₂ = r₂) :
    p ∈ circleInterPts c₁ r₁ c₂ r₂ := by
  let d := c₂ - c₁
  let L2 := normSq2 d
  have hL2_pos : 0 < L2 := (normSq2_pos_iff d).mpr (sub_ne_zero.mpr hc.symm)
  have hL2_ne : L2 ≠ 0 := ne_of_gt hL2_pos
  let α := (r₁ ^ 2 - r₂ ^ 2 + L2) / (2 * L2)
  let foot := c₁ + α • d
  let nvec := mkPt (-d 1) (d 0)
  let t := Real.sqrt ((r₁ ^ 2 - α ^ 2 * L2) / L2)
  have he1 : normSq2 (p - c₁) = r₁ ^ 2 := by rw [← dist_sq_eq_normSq2, h1]
  have he2 : normSq2 (p - c₂) = r₂ ^ 2 := by rw [← dist_sq_eq_normSq2, h2]
  -- 1. dot2 (p - c₁) d = (r₁² - r₂² + L2) / 2 = α * L2, so dot2 (p - foot) d = 0.
  have hdot_d : dot2 (p - foot) d = 0 := by
    have hdot1 : 2 * dot2 (p - c₁) d = r₁ ^ 2 - r₂ ^ 2 + L2 := by
      simp only [normSq2, dot2, d, L2, PiLp.sub_apply] at he1 he2 ⊢
      linarith
    have hsub : p - foot = (p - c₁) - α • d := by
      ext i; simp [foot, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]; ring
    rw [hsub]
    have hlin : dot2 ((p - c₁) - α • d) d = dot2 (p - c₁) d - α * L2 := by
      simp only [dot2, normSq2, L2, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hlin]
    have hα : α * L2 = (r₁ ^ 2 - r₂ ^ 2 + L2) / 2 := by
      dsimp only [α]; field_simp [hL2_ne]
    linarith
  -- 2. Since dot2 (p - foot) d = 0, p - foot = s • nvec where s = dot2 (p - foot) nvec / L2.
  let s := dot2 (p - foot) nvec / L2
  have hpf_eq : p - foot = s • nvec := by
    apply pt_ext
    · simp only [PiLp.smul_apply, smul_eq_mul, s, nvec, mkPt_zero, mkPt_one, dot2]
      have h0 : (p - foot) 0 * L2 = (dot2 (p - foot) nvec) * (-d 1) + (dot2 (p - foot) d) * d 0 := by
        simp only [L2, normSq2, dot2, nvec, mkPt_zero, mkPt_one]; ring
      rw [hdot_d, zero_mul, add_zero] at h0
      simp only [dot2, nvec, mkPt_zero, mkPt_one] at h0
      field_simp [hL2_ne]
      linarith
    · simp only [PiLp.smul_apply, smul_eq_mul, s, nvec, mkPt_zero, mkPt_one, dot2]
      have h1' : (p - foot) 1 * L2 = (dot2 (p - foot) nvec) * d 0 + (dot2 (p - foot) d) * d 1 := by
        simp only [L2, normSq2, dot2, nvec, mkPt_zero, mkPt_one]; ring
      rw [hdot_d, zero_mul, add_zero] at h1'
      simp only [dot2, nvec, mkPt_zero, mkPt_one] at h1'
      field_simp [hL2_ne]
      linarith
  -- 3. Pythagoras: r₁² = normSq2 (p - c₁) = α² * L2 + s² * L2!
  have hs_sq : s ^ 2 = (r₁ ^ 2 - α ^ 2 * L2) / L2 := by
    have hp_split : p - c₁ = α • d + s • nvec := by
      have : p - c₁ = (foot - c₁) + (p - foot) := by abel
      rw [this, hpf_eq]; simp [foot]
    rw [hp_split] at he1
    have hpyth : normSq2 (α • d + s • nvec) = α ^ 2 * L2 + s ^ 2 * L2 := by
      simp only [normSq2, L2, nvec, mkPt_zero, mkPt_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hpyth] at he1
    rw [eq_div_iff hL2_ne]; linarith
  have hst : s = t ∨ s = -t := by
    have ht_sq : t ^ 2 = s ^ 2 := by
      dsimp only [t]; rw [← hs_sq, Real.sq_sqrt (sq_nonneg s)]
    have hfac : (s - t) * (s + t) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  simp only [circleInterPts, Finset.mem_insert, Finset.mem_singleton]
  rcases hst with hs | hs
  · left
    rw [hs] at hpf_eq
    change p = foot + t • nvec
    rw [eq_add_of_sub_eq' hpf_eq]
  · right
    rw [hs] at hpf_eq
    change p = foot - t • nvec
    rw [eq_add_of_sub_eq' hpf_eq, neg_smul, ← sub_eq_add_neg]

/-- **Congruent-Circle Incidence Theorem (Spencer–Szemerédi–Trotter / Székely):**
For any finite point set `P`, finite center set `Q`, and radius `r > 0`,
`∑ c ∈ Q, |{p ∈ P | dist p c = r}| ≤ 8 |P|^(2/3) |Q|^(2/3) + 8 |P| + 2 |Q|`. -/
theorem congruent_circle_incidences_le
    (P Q : Finset (EuclideanSpace ℝ (Fin 2))) {r : ℝ} (hr : 0 < r) :
    ((∑ c ∈ Q, (P.filter (fun p => dist p c = r)).card : ℕ) : ℝ) ≤
      8 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (Q.card : ℝ) ^ ((2 : ℝ) / 3) + 8 * (P.card : ℝ) + 2 * (Q.card : ℝ) := by
  classical
  -- Step 1: Rotate (P, Q) together so ALL distinct points in P ∪ Q ∪ interPts have distinct x-coordinates!
  let interPts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2)).biUnion (fun pq => circleInterPts pq.1 r pq.2 r)
  let AllPts := P ∪ Q ∪ interPts
  let V : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((AllPts ×ˢ AllPts).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => pq.1 - pq.2)
  have hV : ∀ w ∈ V, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨pq, hpq, rfl⟩
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hpq).2
  obtain ⟨u, v, huv, haxes⟩ := exists_rotation_avoiding_axes V hV
  have hAll_x : ∀ a ∈ AllPts, ∀ b ∈ AllPts, a ≠ b → rotUnit u v a 0 ≠ rotUnit u v b 0 := by
    intro a ha b hb hab
    have hmem : a - b ∈ V := Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
    have h0 := (haxes (a - b) hmem).1
    rw [rotUnit_sub] at h0; simp only [PiLp.sub_apply] at h0
    exact sub_ne_zero.mp h0
  let P' := P.image (rotUnit u v)
  let Q' := Q.image (rotUnit u v)
  have hP'_card : P'.card = P.card := Finset.card_image_of_injective P (rotUnit_injective huv)
  have hQ'_card : Q'.card = Q.card := Finset.card_image_of_injective Q (rotUnit_injective huv)
  -- Helper proving the upper-semicircle bound for ANY (A, B) with distinct x-coords on A ∪ interPts(B)!
  have hupper : ∀ (A B : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a 0 ≠ b 0) →
      (∀ c₁ ∈ B, ∀ c₂ ∈ B, c₁ ≠ c₂ → ∀ q : EuclideanSpace ℝ (Fin 2),
        dist q c₁ = r → dist q c₂ = r → ∀ a ∈ A, q 0 = a 0 → q = a) →
      ((∑ c ∈ B, (A.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card : ℕ) : ℝ) ≤
        4 * (A.card : ℝ) ^ ((2 : ℝ) / 3) * (B.card : ℝ) ^ ((2 : ℝ) / 3) + 4 * (A.card : ℝ) + (B.card : ℝ) := by
    intro A B hAx hAB_gen
    let X_A : Finset ℝ := A.image (fun p => p 0)
    have hXA_inj : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 2) => p 0) A :=
      fun a ha b hb hEq => by by_contra hne; exact hAx a ha b hb hne hEq
    have hXA_card : X_A.card = A.card := Finset.card_image_of_injOn hXA_inj
    let n := A.card
    let φx : Fin n ↪o ℝ := X_A.orderEmbOfFin hXA_card
    let x : Fin n → ℝ := fun k => φx k
    have hx_strict : StrictMono x := φx.strictMono
    have hx_mem : ∀ k : Fin n, ∃ p ∈ A, p 0 = x k := fun k =>
      Finset.mem_image.mp (X_A.orderEmbOfFin_mem hXA_card k)
    let ptOf : Fin n → EuclideanSpace ℝ (Fin 2) := fun k => (hx_mem k).choose
    have hptOf_mem : ∀ k : Fin n, ptOf k ∈ A := fun k => (hx_mem k).choose_spec.1
    have hptOf_x : ∀ k : Fin n, ptOf k 0 = x k := fun k => (hx_mem k).choose_spec.2
    let y : Fin n → ℝ := fun k => ptOf k 1
    let lo : EuclideanSpace ℝ (Fin 2) → ℝ := fun c => c 0 - r
    let hi : EuclideanSpace ℝ (Fin 2) → ℝ := fun c => c 0 + r
    let f : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ := fun c t => c 1 + Real.sqrt (r ^ 2 - (t - c 0) ^ 2)
    have hf_iff : ∀ (c p : EuclideanSpace ℝ (Fin 2)),
        (lo c ≤ p 0 ∧ p 0 ≤ hi c ∧ f c (p 0) = p 1) ↔ (dist p c = r ∧ c 1 ≤ p 1) := by
      intro c p
      constructor
      · rintro ⟨hlo, hhi, hfeq⟩
        have hnn : 0 ≤ r ^ 2 - (p 0 - c 0) ^ 2 := by
          dsimp only [lo, hi] at hlo hhi; nlinarith
        have hpy : c 1 ≤ p 1 := by
          rw [← hfeq]; linarith [Real.sqrt_nonneg (r ^ 2 - (p 0 - c 0) ^ 2)]
        have hdsq : dist p c ^ 2 = r ^ 2 := by
          rw [dist_sq_eq_normSq2]
          unfold normSq2; simp only [PiLp.sub_apply]
          have hsub : p 1 - c 1 = Real.sqrt (r ^ 2 - (p 0 - c 0) ^ 2) := by
            dsimp only [f] at hfeq; linarith
          rw [hsub, Real.sq_sqrt hnn]; ring
        have hdist : dist p c = r := by
          have : (dist p c - r) * (dist p c + r) = 0 := by nlinarith
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · linarith [dist_nonneg (x := p) (y := c)]
        exact ⟨hdist, hpy⟩
      · rintro ⟨hdist, hpy⟩
        have hdsq : (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 = r ^ 2 := by
          have := dist_sq_eq_normSq2 p c
          rw [hdist] at this
          simpa [normSq2, PiLp.sub_apply] using this.symm
        have hlo : lo c ≤ p 0 := by dsimp only [lo]; nlinarith [sq_nonneg (p 1 - c 1)]
        have hhi : p 0 ≤ hi c := by dsimp only [hi]; nlinarith [sq_nonneg (p 1 - c 1)]
        have hfeq : f c (p 0) = p 1 := by
          dsimp only [f]
          have hsub : r ^ 2 - (p 0 - c 0) ^ 2 = (p 1 - c 1) ^ 2 := by linarith
          rw [hsub, Real.sqrt_sq (by linarith)]; ring
        exact ⟨hlo, hhi, hfeq⟩
    have hsum_eq : ∑ c ∈ B, (A.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card =
        ∑ c ∈ B, ((Finset.univ : Finset (Fin n)).filter
          (fun k => lo c ≤ x k ∧ x k ≤ hi c ∧ f c (x k) = y k)).card := by
      refine Finset.sum_congr rfl fun c _ => ?_
      symm
      refine Finset.card_bij (fun k _ => ptOf k) ?_ ?_ ?_
      · intro k hk
        obtain ⟨_, hlo, hhi, hfeq⟩ := Finset.mem_filter.mp hk
        refine Finset.mem_filter.mpr ⟨hptOf_mem k, (hf_iff c (ptOf k)).mp ?_⟩
        rw [hptOf_x k]; exact ⟨hlo, hhi, hfeq⟩
      · intro k₁ _ k₂ _ hEq
        exact hx_strict.injective (by rw [← hptOf_x k₁, ← hptOf_x k₂, hEq])
      · intro p hp
        obtain ⟨hpA, hpC⟩ := Finset.mem_filter.mp hp
        have hxmem' : p 0 ∈ X_A := Finset.mem_image_of_mem _ hpA
        have hrng : Set.range φx = (X_A : Set ℝ) := X_A.range_orderEmbOfFin hXA_card
        have hxr : p 0 ∈ Set.range φx := by rw [hrng]; exact hxmem'
        obtain ⟨k, hkEq⟩ := Set.mem_range.mp hxr
        have hptEq : ptOf k = p := hXA_inj (hptOf_mem k) hpA ((hptOf_x k).trans hkEq)
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hptEq⟩
        have hcond := (hf_iff c p).mpr hpC
        rw [← hptOf_x k, show y k = ptOf k 1 from rfl, hptEq]; exact hcond
    rw [hsum_eq]
    refine xMonotone_one_inter_incidences_le x y hx_strict B lo hi f ?_ ?_ ?_
    · intro c _
      exact (continuous_const.add (Real.continuous_sqrt.comp
        (continuous_const.sub ((continuous_id.sub continuous_const).pow 2)))).continuousOn
    · intro c₁ _ c₂ _ hne t₁ t₂ hlo1 hhi1 hlo2 hhi2 heq1 hlo1' hhi1' hlo2' hhi2' heq2
      let q₁ := mkPt t₁ (f c₁ t₁)
      let q₂ := mkPt t₂ (f c₁ t₂)
      have hq1_1 : dist q₁ c₁ = r ∧ c₁ 1 ≤ q₁ 1 := (hf_iff c₁ q₁).mp (by simp [q₁, hlo1, hhi1])
      have hq1_2 : dist q₁ c₂ = r ∧ c₂ 1 ≤ q₁ 1 := (hf_iff c₂ q₁).mp (by simp [q₁, hlo2, hhi2, heq1])
      have hq2_1 : dist q₂ c₁ = r ∧ c₁ 1 ≤ q₂ 1 := (hf_iff c₁ q₂).mp (by simp [q₂, hlo1', hhi1'])
      have hq2_2 : dist q₂ c₂ = r ∧ c₂ 1 ≤ q₂ 1 := (hf_iff c₂ q₂).mp (by simp [q₂, hlo2', hhi2', heq2])
      have hqeq : q₁ = q₂ := upper_congruent_semicircle_inter_subsingleton hne
        ⟨hq1_1.1, hq1_1.2, hq1_2.1, hq1_2.2⟩ ⟨hq2_1.1, hq2_1.2, hq2_2.1, hq2_2.2⟩
      simpa [q₁, q₂] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hqeq
    · intro c₁ hc1 c₂ hc2 hne k hlo1 hhi1 hlo2 hhi2 hfeq
      let q := mkPt (x k) (f c₁ (x k))
      have hq1 : dist q c₁ = r := ((hf_iff c₁ q).mp (by simp [q, hlo1, hhi1])).1
      have hq2 : dist q c₂ = r := ((hf_iff c₂ q).mp (by simp [q, hlo2, hhi2, hfeq])).1
      have hqeq : q = ptOf k := hAB_gen c₁ hc1 c₂ hc2 hne q hq1 hq2 (ptOf k) (hptOf_mem k)
        (by simp [q, hptOf_x k])
      simpa [q, y] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hqeq
  -- Apply hupper to (P', Q') for upper semicircles, and to y-reflected (P'', Q'') for lower semicircles!
  have hP'x : ∀ a ∈ P', ∀ b ∈ P', a ≠ b → a 0 ≠ b 0 := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
    exact hAll_x p (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
      q (Finset.mem_union_left _ (Finset.mem_union_left _ hq))
      (fun h => hab (congrArg (rotUnit u v) h))
  have hP'Q'_gen : ∀ c₁ ∈ Q', ∀ c₂ ∈ Q', c₁ ≠ c₂ → ∀ q : EuclideanSpace ℝ (Fin 2),
      dist q c₁ = r → dist q c₂ = r → ∀ a ∈ P', q 0 = a 0 → q = a := by
    intro c₁ hc1 c₂ hc2 hne q hq1 hq2 a ha hqx
    rcases Finset.mem_image.mp hc1 with ⟨c₁₀, hc1₀, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨c₂₀, hc2₀, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨p₀, hp₀, rfl⟩
    have hcne₀ : c₁₀ ≠ c₂₀ := fun h => hne (congrArg (rotUnit u v) h)
    let q₀ := rotUnit u (-v) q
    have hq₀1 : dist q₀ c₁₀ = r := by
      have := rotUnit_dist huv q₀ c₁₀; rw [rotUnit_inv_comp huv, hq1] at this; exact this.symm
    have hq₀2 : dist q₀ c₂₀ = r := by
      have := rotUnit_dist huv q₀ c₂₀; rw [rotUnit_inv_comp huv, hq2] at this; exact this.symm
    have hq₀_inter : q₀ ∈ interPts :=
      Finset.mem_biUnion.mpr ⟨(c₁₀, c₂₀), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc1₀, hc2₀⟩, hcne₀⟩,
        mem_circleInterPts_of_dist hcne₀ hq₀1 hq₀2⟩
    by_contra hqa
    have hq₀p₀ : q₀ ≠ p₀ := fun h => hqa (by
      have := congrArg (rotUnit u v) h
      simpa [q₀, rotUnit_inv_comp huv] using this)
    have hne0 := hAll_x q₀ (Finset.mem_union_right _ hq₀_inter)
      p₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hp₀)) hq₀p₀
    rw [rotUnit_inv_comp huv] at hne0
    exact hne0 hqx
  have hup := hupper P' Q' hP'x hP'Q'_gen
  -- Reflect y ↦ -y to bound the lower semicircles!
  let reflY : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun p => mkPt (p 0) (-p 1)
  have hreflY_inj : Function.Injective reflY := fun a b h =>
    pt_ext (by simpa [reflY] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h)
      (by have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h; simp [reflY] at this; linarith)
  have hreflY_dist : ∀ a b, dist (reflY a) (reflY b) = dist a b := fun a b => by
    rw [dist_eq_sqrt_normSq2, dist_eq_sqrt_normSq2]
    congr 1; simp only [normSq2, reflY, PiLp.sub_apply, mkPt_zero, mkPt_one]; ring
  let P'' := P'.image reflY
  let Q'' := Q'.image reflY
  have hP''_card : P''.card = P'.card := Finset.card_image_of_injective P' hreflY_inj
  have hQ''_card : Q''.card = Q'.card := Finset.card_image_of_injective Q' hreflY_inj
  have hP''x : ∀ a ∈ P'', ∀ b ∈ P'', a ≠ b → a 0 ≠ b 0 := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
    simpa [reflY] using hP'x a' ha' b' hb' (fun h => hab (congrArg reflY h))
  have hP''Q''_gen : ∀ c₁ ∈ Q'', ∀ c₂ ∈ Q'', c₁ ≠ c₂ → ∀ q : EuclideanSpace ℝ (Fin 2),
      dist q c₁ = r → dist q c₂ = r → ∀ a ∈ P'', q 0 = a 0 → q = a := by
    intro c₁ hc1 c₂ hc2 hne q hq1 hq2 a ha hqx
    rcases Finset.mem_image.mp hc1 with ⟨c₁', hc1', rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨c₂', hc2', rfl⟩
    rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
    have hrr : reflY (reflY q) = q := pt_ext (by simp [reflY]) (by simp [reflY])
    have h1' : dist (reflY q) c₁' = r := by rw [← hreflY_dist (reflY q) c₁', hrr]; exact hq1
    have h2' : dist (reflY q) c₂' = r := by rw [← hreflY_dist (reflY q) c₂', hrr]; exact hq2
    have hEq' := hP'Q'_gen c₁' hc1' c₂' hc2' (fun h => hne (congrArg reflY h)) (reflY q) h1' h2'
      a' ha' (by simpa [reflY] using hqx)
    rw [← hrr, hEq']
  have hlo := hupper P'' Q'' hP''x hP''Q''_gen
  -- Relate original incidences to upper + lower on (P', Q')!
  have hsplit_inc : ∑ c ∈ Q, (P.filter (fun p => dist p c = r)).card ≤
      (∑ c ∈ Q', (P'.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card) +
      (∑ c ∈ Q'', (P''.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card) := by
    have hrot_eq : ∑ c ∈ Q, (P.filter (fun p => dist p c = r)).card =
        ∑ c ∈ Q', (P'.filter (fun p => dist p c = r)).card := by
      rw [Finset.sum_image (fun _ _ _ _ h => rotUnit_injective huv h)]
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.card_bij (fun p _ => rotUnit u v p) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hpP, by rw [rotUnit_dist huv]; exact hpd⟩
      · intro _ _ _ _ h; exact rotUnit_injective huv h
      · intro p' hp'
        obtain ⟨hp'P, hpd⟩ := Finset.mem_filter.mp hp'
        rcases Finset.mem_image.mp hp'P with ⟨p, hpP, rfl⟩
        exact ⟨p, Finset.mem_filter.mpr ⟨hpP, by rwa [rotUnit_dist huv] at hpd⟩, rfl⟩
    have hlo_eq : ∑ c ∈ Q'', (P''.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card =
        ∑ c ∈ Q', (P'.filter (fun p => dist p c = r ∧ p 1 ≤ c 1)).card := by
      rw [Finset.sum_image (fun _ _ _ _ h => hreflY_inj h)]
      refine Finset.sum_congr rfl fun c _ => ?_
      symm
      refine Finset.card_bij (fun p _ => reflY p) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpP, hpd, hle⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hpP,
          by rw [hreflY_dist]; exact hpd, by simp [reflY]; linarith⟩
      · intro _ _ _ _ h; exact hreflY_inj h
      · intro p'' hp''
        obtain ⟨hp''P, hpd, hle⟩ := Finset.mem_filter.mp hp''
        rcases Finset.mem_image.mp hp''P with ⟨p, hpP, rfl⟩
        exact ⟨p, Finset.mem_filter.mpr ⟨hpP, by rwa [hreflY_dist] at hpd, by simp [reflY] at hle; linarith⟩, rfl⟩
    rw [hrot_eq, hlo_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have hcov : P'.filter (fun p => dist p c = r) ⊆
        P'.filter (fun p => dist p c = r ∧ c 1 ≤ p 1) ∪ P'.filter (fun p => dist p c = r ∧ p 1 ≤ c 1) := by
      intro p hp
      obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
      rcases le_total (c 1) (p 1) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpP, hpd, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpP, hpd, h⟩)
    exact le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
  have hsplitR : ((∑ c ∈ Q, (P.filter (fun p => dist p c = r)).card : ℕ) : ℝ) ≤
      ((∑ c ∈ Q', (P'.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card : ℕ) : ℝ) +
      ((∑ c ∈ Q'', (P''.filter (fun p => dist p c = r ∧ c 1 ≤ p 1)).card : ℕ) : ℝ) := by
    exact_mod_cast hsplit_inc
  rw [hP''_card, hQ''_card, hP'_card, hQ'_card] at hlo
  rw [hP'_card, hQ'_card] at hup
  linarith

/-- **Unit-Circle Incidence Bound:**
For any finite `P, Q ⊂ ℝ²`, `I(P, unit circles centered at Q) ≤ 8 |P|^(2/3) |Q|^(2/3) + 8 |P| + 2 |Q|`. -/
theorem unit_circle_incidences_le (P Q : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((∑ c ∈ Q, (P.filter (fun p => dist p c = 1)).card : ℕ) : ℝ) ≤
      8 * (P.card : ℝ) ^ ((2 : ℝ) / 3) * (Q.card : ℝ) ^ ((2 : ℝ) / 3) + 8 * (P.card : ℝ) + 2 * (Q.card : ℝ) :=
  congruent_circle_incidences_le P Q (by norm_num)

/-- **Spencer–Szemerédi–Trotter Unit-Distance Theorem (`O(n^(4/3))`):**
The number of ordered unit-distance pairs in any finite `P ⊂ ℝ²` is at most `8 |P|^(4/3) + 10 |P|`. -/
theorem unit_distances_le (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (((P ×ˢ P).filter (fun pq => dist pq.1 pq.2 = 1)).card : ℝ) ≤
      8 * (P.card : ℝ) ^ ((4 : ℝ) / 3) + 10 * (P.card : ℝ) := by
  have hcard_eq : ((P ×ˢ P).filter (fun pq => dist pq.1 pq.2 = 1)).card =
      ∑ c ∈ P, (P.filter (fun p => dist p c = 1)).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.card_filter]
  rw [hcard_eq]
  have h := unit_circle_incidences_le P P
  have hpow : (P.card : ℝ) ^ ((2 : ℝ) / 3) * (P.card : ℝ) ^ ((2 : ℝ) / 3) =
      (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
    by_cases h0 : P.card = 0
    · simp [h0]
    · rw [← Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0))]
      norm_num
  linarith

/-- Compact `O(n^(4/3))` form of the Unit-Distance Theorem for all nonempty `P ⊂ ℝ²`. -/
theorem unit_distances_le_compact (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (((P ×ˢ P).filter (fun pq => dist pq.1 pq.2 = 1)).card : ℝ) ≤
      18 * (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
  have h := unit_distances_le P
  by_cases h0 : P.card = 0
  · have hP0 : P = ∅ := Finset.card_eq_zero.mp h0
    simp [hP0]
  · have h1 : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hle : (P.card : ℝ) ≤ (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
      conv_lhs => rw [← Real.rpow_one (P.card : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    linarith

/-! ### 5B. Pinned & Global Distinct-Distance `Ω(n^(4/5))` Corollaries (Székely 1997) -/

/-- The perpendicular bisector line of two points `u, v ∈ ℝ²`. -/
noncomputable def perpBisector (u v : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  let m : EuclideanSpace ℝ (Fin 2) := (1 / 2 : ℝ) • (u + v)
  let nvec : EuclideanSpace ℝ (Fin 2) := mkPt (-(v 1 - u 1)) (v 0 - u 0)
  lineThrough m (m + nvec)

lemma isLine_perpBisector {u v : EuclideanSpace ℝ (Fin 2)} (huv : u ≠ v) :
    IsLine (perpBisector u v) := by
  unfold perpBisector
  apply isLine_lineThrough
  intro hEq
  have h0 : -(v 1 - u 1) = 0 := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hEq
    simp [PiLp.add_apply] at this; linarith
  have h1 : v 0 - u 0 = 0 := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hEq
    simp [PiLp.add_apply] at this; linarith
  exact huv (pt_ext (by linarith) (by linarith))

lemma mem_perpBisector_iff {u v p : EuclideanSpace ℝ (Fin 2)} (huv : u ≠ v) :
    p ∈ perpBisector u v ↔ dist p u = dist p v := by
  unfold perpBisector
  let m : EuclideanSpace ℝ (Fin 2) := (1 / 2 : ℝ) • (u + v)
  let nvec : EuclideanSpace ℝ (Fin 2) := mkPt (-(v 1 - u 1)) (v 0 - u 0)
  have hmn : m ≠ m + nvec := by
    intro hEq
    have h0 : -(v 1 - u 1) = 0 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hEq
      simp [nvec, PiLp.add_apply] at this; linarith
    have h1 : v 0 - u 0 = 0 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hEq
      simp [nvec, PiLp.add_apply] at this; linarith
    exact huv (pt_ext (by linarith) (by linarith))
  change p ∈ lineThrough m (m + nvec) ↔ dist p u = dist p v
  rw [mem_lineThrough_iff_det2 hmn]
  have hdet_eq : det2 ((m + nvec) - m) (p - m) = -(normSq2 (p - u) - normSq2 (p - v)) / 2 := by
    rw [add_sub_cancel_left]
    simp only [det2, normSq2, m, nvec, mkPt_zero, mkPt_one, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.add_apply, smul_eq_mul]
    ring
  rw [hdet_eq, div_eq_zero_iff]
  simp only [OfNat.ofNat_ne_zero, or_false, neg_eq_zero, sub_eq_zero, ← dist_sq_eq_normSq2]
  constructor
  · intro hsq
    have : (dist p u - dist p v) * (dist p u + dist p v) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · have h1 : 0 ≤ dist p u := dist_nonneg
      have h2 : 0 ≤ dist p v := dist_nonneg
      linarith
  · intro h; rw [h]

/-- Strict concavity of the upper semicircle height `g(t) = √(r² - (t - c₀)²)`:
secant slopes strictly decrease from left to right. -/
lemma semicircle_slope_strict_antitone {r c₀ x y z : ℝ}
    (hlo : c₀ - r ≤ x) (hxy : x < y) (hyz : y < z) (hhi : z ≤ c₀ + r) :
    let g := fun t : ℝ => Real.sqrt (r ^ 2 - (t - c₀) ^ 2)
    (g z - g y) / (z - y) < (g y - g x) / (y - x) := by
  intro g
  have hxz : x < z := lt_trans hxy hyz
  let lam := (y - x) / (z - x)
  have hlam0 : 0 < lam := div_pos (by linarith) (by linarith)
  have hlam1 : lam < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hy_eq : y = (1 - lam) * x + lam * z := by
    dsimp only [lam]; field_simp [ne_of_gt (sub_pos.mpr hxz)]; ring
  have hnn_x : 0 ≤ r ^ 2 - (x - c₀) ^ 2 := by nlinarith
  have hnn_y : 0 ≤ r ^ 2 - (y - c₀) ^ 2 := by nlinarith
  have hnn_z : 0 ≤ r ^ 2 - (z - c₀) ^ 2 := by nlinarith
  have hgx_sq : g x ^ 2 = r ^ 2 - (x - c₀) ^ 2 := Real.sq_sqrt hnn_x
  have hgy_sq : g y ^ 2 = r ^ 2 - (y - c₀) ^ 2 := Real.sq_sqrt hnn_y
  have hgz_sq : g z ^ 2 = r ^ 2 - (z - c₀) ^ 2 := Real.sq_sqrt hnn_z
  have hsq_lt : ((1 - lam) * g x + lam * g z) ^ 2 < g y ^ 2 := by
    have hident : g y ^ 2 - ((1 - lam) * g x + lam * g z) ^ 2 =
        (1 - lam) * lam * ((z - x) ^ 2 + (g z - g x) ^ 2) := by
      have h1 : r ^ 2 = (x - c₀) ^ 2 + g x ^ 2 := by linarith
      have h2 : r ^ 2 = (z - c₀) ^ 2 + g z ^ 2 := by linarith
      rw [hgy_sq, hy_eq]
      have : r ^ 2 = (1 - lam) * ((x - c₀) ^ 2 + g x ^ 2) + lam * ((z - c₀) ^ 2 + g z ^ 2) := by
        nlinarith
      linarith [show (1 - lam) * ((x - c₀) ^ 2 + g x ^ 2) + lam * ((z - c₀) ^ 2 + g z ^ 2) -
          (((1 - lam) * x + lam * z - c₀) ^ 2 + ((1 - lam) * g x + lam * g z) ^ 2) =
          (1 - lam) * lam * ((z - x) ^ 2 + (g z - g x) ^ 2) by ring]
    have hpos : 0 < (1 - lam) * lam * ((z - x) ^ 2 + (g z - g x) ^ 2) := by
      have : 0 < (z - x) ^ 2 + (g z - g x) ^ 2 := by nlinarith [sq_nonneg (g z - g x)]
      positivity
    linarith
  have hgy_gt : (1 - lam) * g x + lam * g z < g y := by
    by_contra hle; push Not at hle
    have hnn1 : 0 ≤ g y := Real.sqrt_nonneg _
    have hnn2 : 0 ≤ (1 - lam) * g x + lam * g z := by
      have := Real.sqrt_nonneg (r ^ 2 - (x - c₀) ^ 2)
      have := Real.sqrt_nonneg (r ^ 2 - (z - c₀) ^ 2)
      nlinarith
    nlinarith
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have h1 : (g y - ((1 - lam) * g x + lam * g z)) * (z - x) =
      (g y - g x) * (z - y) - (g z - g y) * (y - x) := by
    dsimp only [lam]; field_simp [ne_of_gt (sub_pos.mpr hxz)]; ring
  have hpos : 0 < (g y - ((1 - lam) * g x + lam * g z)) * (z - x) := by nlinarith
  linarith

/-- Two chords on the same semicircle sharing a perpendicular bisector must either coincide
or have one left endpoint strictly between the other's endpoints! -/
lemma semicircle_consec_bisector_unique {c u₁ v₁ u₂ v₂ : EuclideanSpace ℝ (Fin 2)} {r : ℝ} {σ : Bool}
    (hu1 : dist u₁ c = r) (hv1 : dist v₁ c = r) (hu2 : dist u₂ c = r) (hv2 : dist v₂ c = r)
    (hs1u : if σ then c 1 < u₁ 1 else u₁ 1 < c 1)
    (hs1v : if σ then c 1 < v₁ 1 else v₁ 1 < c 1)
    (hs2u : if σ then c 1 < u₂ 1 else u₂ 1 < c 1)
    (hs2v : if σ then c 1 < v₂ 1 else v₂ 1 < c 1)
    (h1x : u₁ 0 < v₁ 0) (h2x : u₂ 0 < v₂ 0)
    (hbis : perpBisector u₁ v₁ = perpBisector u₂ v₂) :
    (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ 0 < u₂ 0 ∧ u₂ 0 < v₁ 0) ∨ (u₂ 0 < u₁ 0 ∧ u₁ 0 < v₂ 0) := by
  let g := fun t : ℝ => Real.sqrt (r ^ 2 - (t - c 0) ^ 2)
  have hdom : ∀ p : EuclideanSpace ℝ (Fin 2), dist p c = r → (if σ then c 1 < p 1 else p 1 < c 1) →
      c 0 - r ≤ p 0 ∧ p 0 ≤ c 0 + r ∧ p 1 = c 1 + (if σ then 1 else -1) * g (p 0) := by
    intro p hdp hsp
    have hsq : (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 = r ^ 2 := by
      have := dist_sq_eq_normSq2 p c; rw [hdp] at this
      simpa [normSq2, PiLp.sub_apply] using this.symm
    have hr_nn : 0 ≤ r := hdp ▸ dist_nonneg
    have hlo : c 0 - r ≤ p 0 := by nlinarith [sq_nonneg (p 1 - c 1)]
    have hhi : p 0 ≤ c 0 + r := by nlinarith [sq_nonneg (p 1 - c 1)]
    have hsub : r ^ 2 - (p 0 - c 0) ^ 2 = (p 1 - c 1) ^ 2 := by linarith
    refine ⟨hlo, hhi, ?_⟩
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsp ⊢
      have hg : g (p 0) = c 1 - p 1 := by
        dsimp only [g]; rw [hsub, show (p 1 - c 1) ^ 2 = (c 1 - p 1) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      linarith
    · simp only [↓reduceIte] at hsp ⊢
      have hg : g (p 0) = p 1 - c 1 := by
        dsimp only [g]; rw [hsub, Real.sqrt_sq (by linarith)]
      linarith
  obtain ⟨h1u_lo, h1u_hi, h1u_y⟩ := hdom u₁ hu1 hs1u
  obtain ⟨h1v_lo, h1v_hi, h1v_y⟩ := hdom v₁ hv1 hs1v
  obtain ⟨h2u_lo, h2u_hi, h2u_y⟩ := hdom u₂ hu2 hs2u
  obtain ⟨h2v_lo, h2v_hi, h2v_y⟩ := hdom v₂ hv2 hs2v
  -- Equal perpendicular bisectors ⇒ parallel chords ⇒ equal slopes!
  have hslope_eq : (g (v₁ 0) - g (u₁ 0)) / (v₁ 0 - u₁ 0) = (g (v₂ 0) - g (u₂ 0)) / (v₂ 0 - u₂ 0) := by
    have hu1v1 : u₁ ≠ v₁ := fun h => ne_of_lt h1x (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h)
    have hu2v2 : u₂ ≠ v₂ := fun h => ne_of_lt h2x (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h)
    -- Both n₁ = (-(v₁ 1 - u₁ 1), v₁ 0 - u₁ 0) and n₂ = (-(v₂ 1 - u₂ 1), v₂ 0 - u₂ 0) lie in the 1D direction!
    let n₁ : EuclideanSpace ℝ (Fin 2) := mkPt (-(v₁ 1 - u₁ 1)) (v₁ 0 - u₁ 0)
    let n₂ : EuclideanSpace ℝ (Fin 2) := mkPt (-(v₂ 1 - u₂ 1)) (v₂ 0 - u₂ 0)
    have hn1_dir : n₁ ∈ (perpBisector u₁ v₁).direction := by
      unfold perpBisector
      rw [direction_lineThrough, add_sub_cancel_left]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hn2_dir : n₂ ∈ (perpBisector u₁ v₁).direction := by
      rw [hbis]; unfold perpBisector
      rw [direction_lineThrough, add_sub_cancel_left]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hdir_span : (perpBisector u₁ v₁).direction = Submodule.span ℝ ({n₁} : Set (EuclideanSpace ℝ (Fin 2))) := by
      unfold perpBisector; rw [direction_lineThrough, add_sub_cancel_left]
    rw [hdir_span, Submodule.mem_span_singleton] at hn2_dir
    obtain ⟨lam, hlam⟩ := hn2_dir
    have hdet0 : det2 n₁ n₂ = 0 := by
      rw [← hlam]; simp [det2, PiLp.smul_apply]; ring
    have hch_eq : (v₁ 1 - u₁ 1) / (v₁ 0 - u₁ 0) = (v₂ 1 - u₂ 1) / (v₂ 0 - u₂ 0) := by
      simp only [det2, n₁, n₂, mkPt_zero, mkPt_one] at hdet0
      rw [div_eq_div_iff (ne_of_gt (sub_pos.mpr h1x)) (ne_of_gt (sub_pos.mpr h2x))]
      linarith
    rw [h1u_y, h1v_y, h2u_y, h2v_y] at hch_eq
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte] at hch_eq
      have h1 : (c 1 + -1 * g (v₁ 0) - (c 1 + -1 * g (u₁ 0))) / (v₁ 0 - u₁ 0) =
          -((g (v₁ 0) - g (u₁ 0)) / (v₁ 0 - u₁ 0)) := by ring
      have h2 : (c 1 + -1 * g (v₂ 0) - (c 1 + -1 * g (u₂ 0))) / (v₂ 0 - u₂ 0) =
          -((g (v₂ 0) - g (u₂ 0)) / (v₂ 0 - u₂ 0)) := by ring
      linarith
    · simp only [↓reduceIte] at hch_eq
      have h1 : (c 1 + 1 * g (v₁ 0) - (c 1 + 1 * g (u₁ 0))) / (v₁ 0 - u₁ 0) =
          (g (v₁ 0) - g (u₁ 0)) / (v₁ 0 - u₁ 0) := by ring
      have h2 : (c 1 + 1 * g (v₂ 0) - (c 1 + 1 * g (u₂ 0))) / (v₂ 0 - u₂ 0) =
          (g (v₂ 0) - g (u₂ 0)) / (v₂ 0 - u₂ 0) := by ring
      linarith
  -- Helper: slope(x, y) > slope(x, z) whenever x < y < z!
  have hslope_left_strict : ∀ a b₁ b₂, c 0 - r ≤ a → a < b₁ → b₁ < b₂ → b₂ ≤ c 0 + r →
      (g b₂ - g a) / (b₂ - a) < (g b₁ - g a) / (b₁ - a) := by
    intro a b₁ b₂ ha h1 h2 hb2
    have hsc := semicircle_slope_strict_antitone ha h1 h2 hb2
    have hsplit : (g b₂ - g a) * (b₁ - a) - (g b₁ - g a) * (b₂ - a) =
        (g b₂ - g b₁) * (b₁ - a) - (g b₁ - g a) * (b₂ - b₁) := by ring
    rw [div_lt_div_iff₀ (by linarith) (by linarith)] at hsc ⊢
    linarith
  -- Case split on u₁ 0 vs u₂ 0!
  rcases lt_trichotomy (u₁ 0) (u₂ 0) with hlt | heq | hgt
  · right; left
    refine ⟨hlt, ?_⟩
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with hEq | hlt2
    · have hsc := semicircle_slope_strict_antitone h1u_lo h1x (hEq ▸ h2x) h2v_hi
      dsimp only at hsc
      rw [hEq] at hslope_eq hsc; linarith
    · have hsc1 := semicircle_slope_strict_antitone h1u_lo h1x hlt2 h2u_hi
      have hsc2 := semicircle_slope_strict_antitone h1v_lo hlt2 h2x h2v_hi
      linarith
  · left
    have hu_eq : u₁ = u₂ := pt_ext heq (by rw [h1u_y, h2u_y, heq])
    have hv0_eq : v₁ 0 = v₂ 0 := by
      rcases lt_trichotomy (v₁ 0) (v₂ 0) with h12 | h12 | h12
      · exfalso
        have := hslope_left_strict (u₁ 0) (v₁ 0) (v₂ 0) h1u_lo h1x h12 h2v_hi
        rw [heq] at hslope_eq this; linarith
      · exact h12
      · exfalso
        have := hslope_left_strict (u₂ 0) (v₂ 0) (v₁ 0) h2u_lo h2x h12 h1v_hi
        rw [← heq] at hslope_eq this; linarith
    exact ⟨hu_eq, pt_ext hv0_eq (by rw [h1v_y, h2v_y, hv0_eq])⟩
  · right; right
    refine ⟨hgt, ?_⟩
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with hEq | hlt2
    · have hsc := semicircle_slope_strict_antitone h2u_lo h2x (hEq ▸ h1x) h1v_hi
      dsimp only at hsc
      rw [hEq] at hslope_eq hsc; linarith
    · have hsc1 := semicircle_slope_strict_antitone h2u_lo h2x hlt2 h1u_hi
      have hsc2 := semicircle_slope_strict_antitone h2v_lo hlt2 h1x h1v_hi
      linarith

/-- Number of distinct positive distances pinned at `p ∈ P`. -/
noncomputable def pinnedDistCount (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  ((P.erase p).image (dist p)).card

/-- Total number of distinct positive distances determined by `P`. -/
noncomputable def distinctDistCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card

lemma pinnedDistCount_le_distinctDistCount {P : Finset (EuclideanSpace ℝ (Fin 2))}
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ P) :
    pinnedDistCount P p ≤ distinctDistCount P := by
  unfold pinnedDistCount distinctDistCount
  refine Finset.card_le_card ?_
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨q, hq, rfl⟩
  refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hp, Finset.mem_of_mem_erase hq⟩, (Finset.ne_of_mem_erase hq).symm⟩, rfl⟩

private lemma pinned_algebra_step {n t M I_card cr : ℝ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hM_pos : 0 < M) (hM_hi : M ≤ 257 * Real.sqrt t)
    (hI_lb : n ^ 2 / 2 ≤ I_card)
    (hcr_ub : cr ≤ n ^ 2 * t ^ 2)
    (hcl : I_card ^ 3 / (64 * M * n ^ 2) - M ^ 2 * n ≤ cr) :
    (1 / 10000 : ℝ) * n ^ ((4 : ℝ) / 5) ≤ t := by
  have hn_pos : 0 < n := by linarith
  have ht_pos : 0 < t := by linarith
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hcube_lb : (n ^ 2 / 2) ^ 3 ≤ I_card ^ 3 :=
    pow_le_pow_left₀ (by positivity) hI_lb 3
  have hterm_lb : n ^ 4 / (512 * 257 * Real.sqrt t) ≤ I_card ^ 3 / (64 * M * n ^ 2) := by
    have h1 : n ^ 6 / 8 ≤ I_card ^ 3 := by linarith [show (n ^ 2 / 2) ^ 3 = n ^ 6 / 8 by ring]
    have h2 : 64 * M * n ^ 2 ≤ 64 * (257 * Real.sqrt t) * n ^ 2 := by nlinarith
    have h3 : n ^ 4 / (512 * 257 * Real.sqrt t) = (n ^ 6 / 8) / (64 * (257 * Real.sqrt t) * n ^ 2) := by
      field_simp [ne_of_gt hn_pos, ne_of_gt hsqrt_pos]; ring
    rw [h3]
    calc (n ^ 6 / 8) / (64 * (257 * Real.sqrt t) * n ^ 2)
        ≤ (n ^ 6 / 8) / (64 * M * n ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ ≤ I_card ^ 3 / (64 * M * n ^ 2) :=
          div_le_div_of_nonneg_right h1 (by positivity)
  have hsub_ub : M ^ 2 * n ≤ 257 ^ 2 * n ^ 2 * t ^ 2 := by
    have hM2 : M ^ 2 ≤ 257 ^ 2 * t := by
      have hsq := pow_le_pow_left₀ (le_of_lt hM_pos) hM_hi 2
      rw [mul_pow, Real.sq_sqrt (le_of_lt ht_pos)] at hsq
      exact hsq
    have h1nt : 1 ≤ n * t := by nlinarith
    have hnt : t * n ≤ n ^ 2 * t ^ 2 := by nlinarith
    nlinarith
  have hmain_ineq : n ^ 4 / (512 * 257 * Real.sqrt t) ≤ (1 + 257 ^ 2) * n ^ 2 * t ^ 2 := by linarith
  have hpow52 : n ^ 2 ≤ (10000 : ℝ) ^ ((5 : ℝ) / 2) * t ^ ((5 : ℝ) / 2) := by
    have hmul := (div_le_iff₀ (show (0 : ℝ) < 512 * 257 * Real.sqrt t by positivity)).mp hmain_ineq
    have hconst : (1 + 257 ^ 2 : ℝ) * (512 * 257) ≤ (10000 : ℝ) ^ ((5 : ℝ) / 2) := by
      have h10k : (10000 : ℝ) ^ ((5 : ℝ) / 2) = 10 ^ 10 := by
        have h1 : (10000 : ℝ) = (100 : ℝ) ^ (2 : ℝ) := by norm_num
        rw [h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
        norm_num
      rw [h10k]; norm_num
    have ht52 : t ^ 2 * Real.sqrt t = t ^ ((5 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 2, ← Real.rpow_add ht_pos]
      norm_num
    have hcancel : n ^ 2 * n ^ 2 ≤ n ^ 2 * ((1 + 257 ^ 2) * (512 * 257) * (t ^ 2 * Real.sqrt t)) := by
      nlinarith
    have hstep := le_of_mul_le_mul_left hcancel (pow_pos hn_pos 2)
    rw [ht52] at hstep
    have ht52_nn : (0 : ℝ) ≤ t ^ ((5 : ℝ) / 2) := by positivity
    nlinarith
  have h10k_mul : n ^ ((4 : ℝ) / 5) ≤ 10000 * t := by
    have h52_l : (n ^ ((4 : ℝ) / 5)) ^ ((5 : ℝ) / 2) = n ^ 2 := by
      rw [← Real.rpow_mul (le_of_lt hn_pos)]; norm_num
    have h52_r : (10000 * t) ^ ((5 : ℝ) / 2) = (10000 : ℝ) ^ ((5 : ℝ) / 2) * t ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) (le_of_lt ht_pos)
    have hle52 : (n ^ ((4 : ℝ) / 5)) ^ ((5 : ℝ) / 2) ≤ (10000 * t) ^ ((5 : ℝ) / 2) := by
      rw [h52_l, h52_r]; exact hpow52
    have h25 := Real.rpow_le_rpow (by positivity) hle52 (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 5)
    have hl : ((n ^ ((4 : ℝ) / 5)) ^ ((5 : ℝ) / 2)) ^ ((2 : ℝ) / 5) = n ^ ((4 : ℝ) / 5) := by
      rw [← Real.rpow_mul (by positivity)]; norm_num
    have hr : ((10000 * t) ^ ((5 : ℝ) / 2)) ^ ((2 : ℝ) / 5) = 10000 * t := by
      rw [← Real.rpow_mul (by positivity)]; norm_num
    rwa [hl, hr] at h25
  linarith

set_option maxHeartbeats 1200000 in
/-- **Székely's Pinned Distinct-Distance Theorem (`Ω(n^(4/5))`):**
Every finite set `P ⊂ EuclideanSpace ℝ (Fin 2)` with `|P| ≥ 2` contains a point `p ∈ P`
from which there are at least `(1 / 10000) * |P|^(4/5)` distinct positive distances to `P \ {p}`. -/
theorem pinned_distinct_distances_ge
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hP : 2 ≤ P.card) :
    ∃ p ∈ P, (1 / 10000 : ℝ) * (P.card : ℝ) ^ ((4 : ℝ) / 5) ≤ (pinnedDistCount P p : ℝ) := by
  classical
  have hP_ne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨pMax, hpMax, hmax⟩ := P.exists_max_image (pinnedDistCount P) hP_ne
  refine ⟨pMax, hpMax, ?_⟩
  let t : ℕ := pinnedDistCount P pMax
  let n : ℕ := P.card
  have hn_pos : 0 < n := by omega
  have ht_pos : 1 ≤ t := by
    have her_pos : 0 < (P.erase pMax).card := by rw [Finset.card_erase_of_mem hpMax]; omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp her_pos
    exact Finset.card_pos.mpr ⟨dist pMax q, Finset.mem_image_of_mem _ hq⟩
  -- Handle small n (< 16) and large t (t ≥ n / 256) immediately!
  by_cases hn_small : n < 16
  · have hn_le : (n : ℝ) ≤ 16 := by exact_mod_cast le_of_lt hn_small
    have hpow_le : (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      calc (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
    change (1 / 10000 : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (t : ℝ)
    linarith
  push Not at hn_small
  by_cases ht_large : (n : ℝ) / 256 ≤ (t : ℝ)
  · have hpow_le : (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      calc (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    change (1 / 10000 : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (t : ℝ)
    linarith
  push Not at ht_large
  -- Now 16 ≤ n and (t : ℝ) < n / 256!
  -- Step 1: Collect all circles 𝒞 = {(c, r) | c ∈ P, r ∈ (P.erase c).image (dist c)} and pairwise intersections!
  let 𝒞 : Finset (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    P.biUnion (fun c => ((P.erase c).image (dist c)).image (fun r => (c, r)))
  have h𝒞_pos : ∀ C ∈ 𝒞, 0 < C.2 := by
    intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨c, _, hrC⟩
    rcases Finset.mem_image.mp hrC with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hr with ⟨q, hq, rfl⟩
    exact dist_pos.mpr (Finset.ne_of_mem_erase hq).symm
  have h𝒞_card : 𝒞.card ≤ n * t := by
    calc 𝒞.card
        ≤ ∑ c ∈ P, (((P.erase c).image (dist c)).image (fun r => (c, r))).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ P, pinnedDistCount P c := Finset.sum_le_sum fun c _ => Finset.card_image_le
      _ ≤ ∑ _c ∈ P, t := Finset.sum_le_sum fun c hc => hmax c hc
      _ = n * t := by simp [n, t]
  let interPts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((𝒞 ×ˢ 𝒞).filter (fun p => p.1.1 ≠ p.2.1)).biUnion
      (fun p => circleInterPts p.1.1 p.1.2 p.2.1 p.2.2)
  let AllPts := P ∪ interPts
  let V : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((AllPts ×ˢ AllPts).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => pq.1 - pq.2)
  have hV : ∀ w ∈ V, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨pq, hpq, rfl⟩
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hpq).2
  obtain ⟨u, v, huv, haxes⟩ := exists_rotation_avoiding_axes V hV
  have hAll_xy : ∀ a ∈ AllPts, ∀ b ∈ AllPts, a ≠ b →
      rotUnit u v a 0 ≠ rotUnit u v b 0 ∧ rotUnit u v a 1 ≠ rotUnit u v b 1 := by
    intro a ha b hb hab
    have hmem : a - b ∈ V := Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
    obtain ⟨h0, h1⟩ := haxes (a - b) hmem
    rw [rotUnit_sub] at h0 h1; simp only [PiLp.sub_apply] at h0 h1
    exact ⟨sub_ne_zero.mp h0, sub_ne_zero.mp h1⟩
  -- Rotated points P' and rotated circles 𝒞':
  let P' := P.image (rotUnit u v)
  let 𝒞' := 𝒞.image (fun C => (rotUnit u v C.1, C.2))
  have hP'_card : P'.card = n := Finset.card_image_of_injective P (rotUnit_injective huv)
  have h𝒞'_card : 𝒞'.card = 𝒞.card :=
    Finset.card_image_of_injective 𝒞 (fun a b h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (rotUnit_injective huv h1) h2)
  have h𝒞'_mem : ∀ C ∈ 𝒞', C.1 ∈ P' ∧ 0 < C.2 := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨C₀, hC₀, rfl⟩
    rcases Finset.mem_biUnion.mp hC₀ with ⟨c₀, hc₀P, hrC⟩
    rcases Finset.mem_image.mp hrC with ⟨r, hr, hEq⟩
    have hc_eq : C₀.1 = c₀ := congrArg Prod.fst hEq.symm
    exact ⟨hc_eq ▸ Finset.mem_image_of_mem _ hc₀P, h𝒞_pos C₀ hC₀⟩
  -- Sort P' by strictly increasing x-coordinate: ptOf : Fin n → P'!
  let X_P : Finset ℝ := P'.image (fun p => p 0)
  have hx_inj_P' : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 2) => p 0) P' := by
    intro a ha b hb hEq
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
    by_contra hne
    exact (hAll_xy p (Finset.mem_union_left _ hp) q (Finset.mem_union_left _ hq)
      (fun h => hne (congrArg (rotUnit u v) h))).1 hEq
  have hy_inj_P' : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 2) => p 1) P' := by
    intro a ha b hb hEq
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
    by_contra hne
    exact (hAll_xy p (Finset.mem_union_left _ hp) q (Finset.mem_union_left _ hq)
      (fun h => hne (congrArg (rotUnit u v) h))).2 hEq
  have hXP_card : X_P.card = n := by rw [Finset.card_image_of_injOn hx_inj_P', hP'_card]
  let φx : Fin n ↪o ℝ := X_P.orderEmbOfFin hXP_card
  let x : Fin n → ℝ := fun k => φx k
  have hx_strict : StrictMono x := φx.strictMono
  have hx_mem_P' : ∀ k : Fin n, ∃ p ∈ P', p 0 = x k := fun k =>
    Finset.mem_image.mp (X_P.orderEmbOfFin_mem hXP_card k)
  let ptOf : Fin n → EuclideanSpace ℝ (Fin 2) := fun k => (hx_mem_P' k).choose
  have hptOf_mem : ∀ k : Fin n, ptOf k ∈ P' := fun k => (hx_mem_P' k).choose_spec.1
  have hptOf_x : ∀ k : Fin n, ptOf k 0 = x k := fun k => (hx_mem_P' k).choose_spec.2
  have hptOf_inj : Function.Injective ptOf := fun k₁ k₂ h =>
    hx_strict.injective (by rw [← hptOf_x k₁, ← hptOf_x k₂, h])
  have hptOf_surj : ∀ p ∈ P', ∃ k : Fin n, ptOf k = p := by
    intro p hp
    have hxmem' : p 0 ∈ X_P := Finset.mem_image_of_mem _ hp
    have hrng : Set.range φx = (X_P : Set ℝ) := X_P.range_orderEmbOfFin hXP_card
    have hxr : p 0 ∈ Set.range φx := by rw [hrng]; exact hxmem'
    obtain ⟨k, hk⟩ := Set.mem_range.mp hxr
    exact ⟨k, hx_inj_P' (hptOf_mem k) hp ((hptOf_x k).trans hk)⟩
  let y : Fin n → ℝ := fun k => ptOf k 1
  -- Step 2: For each circle C ∈ 𝒞' and sign σ : Bool, build consecutive arcs on the open semicircle C^σ!
  let onSemi (C : EuclideanSpace ℝ (Fin 2) × ℝ) (σ : Bool) (k : Fin n) : Prop :=
    dist (ptOf k) C.1 = C.2 ∧ (if σ then C.1 1 < y k else y k < C.1 1)
  let semiPts (C : EuclideanSpace ℝ (Fin 2) × ℝ) (σ : Bool) : Finset (Fin n) :=
    Finset.univ.filter (onSemi C σ)
  let semiConsec (C : EuclideanSpace ℝ (Fin 2) × ℝ) (σ : Bool) : Finset (Fin n × Fin n) :=
    let S := semiPts C σ
    let φ := S.orderEmbOfFin rfl
    ((Finset.univ : Finset (Fin S.card)).filter (fun i => i.val + 1 < S.card)).image
      (fun i => if hi' : i.val + 1 < S.card then (φ i, φ ⟨i.val + 1, hi'⟩) else (φ i, φ i))
  have hsemiConsec_card : ∀ C σ, (semiPts C σ).card ≤ (semiConsec C σ).card + 1 := by
    intro C σ
    let S := semiPts C σ
    let φ := S.orderEmbOfFin rfl
    let idx := (Finset.univ : Finset (Fin S.card)).filter (fun i => i.val + 1 < S.card)
    have hinj : Set.InjOn
        (fun i : Fin S.card => if hi' : i.val + 1 < S.card then (φ i, φ ⟨i.val + 1, hi'⟩) else (φ i, φ i))
        idx := by
      intro i₁ h1 i₂ h2 hEq
      have hi1 : i₁.val + 1 < S.card := (Finset.mem_filter.mp h1).2
      have hi2 : i₂.val + 1 < S.card := (Finset.mem_filter.mp h2).2
      simp only [dif_pos hi1, dif_pos hi2] at hEq
      exact φ.injective (congrArg Prod.fst hEq)
    have hcard_eq : (semiConsec C σ).card = idx.card := Finset.card_image_of_injOn hinj
    change S.card ≤ (semiConsec C σ).card + 1
    rw [hcard_eq]
    by_cases hS0 : S.card = 0
    · omega
    · have hidx_eq : idx = Finset.univ.erase ⟨S.card - 1, by omega⟩ := by
        ext i
        simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, ne_eq, Fin.ext_iff]
        have := i.isLt; omega
      rw [hidx_eq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
  have hsemiConsec_spec : ∀ C σ, ∀ e ∈ semiConsec C σ,
      e.1 < e.2 ∧ onSemi C σ e.1 ∧ onSemi C σ e.2 ∧ ∀ k : Fin n, e.1 < k → k < e.2 → ¬ onSemi C σ k := by
    intro C σ e he
    let S := semiPts C σ
    let φ := S.orderEmbOfFin rfl
    dsimp only [semiConsec] at he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hi' : i.val + 1 < S.card := (Finset.mem_filter.mp hi).2
    rw [dif_pos hi']
    have hlt : φ i < φ ⟨i.val + 1, hi'⟩ :=
      φ.lt_iff_lt.mpr (show i < ⟨i.val + 1, hi'⟩ by change i.val < i.val + 1; omega)
    have h1 : onSemi C σ (φ i) := (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl i)).2
    have h2 : onSemi C σ (φ ⟨i.val + 1, hi'⟩) := (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl ⟨i.val + 1, hi'⟩)).2
    refine ⟨hlt, h1, h2, fun k hk1 hk2 hkon => ?_⟩
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkon⟩
    have hrng : Set.range φ = (S : Set (Fin n)) := S.range_orderEmbOfFin rfl
    have hkr : k ∈ Set.range φ := by rw [hrng]; exact hkS
    obtain ⟨j, hj⟩ := Set.mem_range.mp hkr
    rw [← hj] at hk1 hk2
    have hj1 : i < j := φ.lt_iff_lt.mp hk1
    have hj2 : j < ⟨i.val + 1, hi'⟩ := φ.lt_iff_lt.mp hk2
    change i.val < j.val at hj1; change j.val < i.val + 1 at hj2
    omega
  -- Total semicircle arc set I_all indexed by ((C, σ), (a, b))!
  let Arc := ((EuclideanSpace ℝ (Fin 2) × ℝ) × Bool) × (Fin n × Fin n)
  let I_all : Finset Arc :=
    (𝒞' ×ˢ (Finset.univ : Finset Bool)).biUnion
      (fun cs => (semiConsec cs.1 cs.2).image (fun e => (cs, e)))
  have hI_all_mem : ∀ e ∈ I_all, e.1.1 ∈ 𝒞' ∧ e.2 ∈ semiConsec e.1.1 e.1.2 := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨cs, hcs, hce⟩
    rcases Finset.mem_image.mp hce with ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hcs).1, hp⟩
  -- Lower bound |I_all| ≥ n * (n - 1) - 2 * 𝒞.card!
  have hI_all_lb : n * (n - 1) ≤ I_all.card + 2 * 𝒞.card := by
    -- Every ordered pair (c', p') of distinct points in P' lies on a UNIQUE circle (c', dist p' c') ∈ 𝒞'
    -- AND on a UNIQUE semicircle σ (since y-coords of P' are pairwise distinct)!
    have hinc_total : ∑ C ∈ 𝒞', ((semiPts C true).card + (semiPts C false).card) = n * (n - 1) := by
      -- First show (semiPts C true).card + (semiPts C false).card = (P'.filter (dist · C.1 = C.2)).card!
      have hC_sum : ∀ C ∈ 𝒞', (semiPts C true).card + (semiPts C false).card =
          (P'.filter (fun p => dist p C.1 = C.2)).card := by
        intro C hC
        have ⟨hC1P', hCr_pos⟩ := h𝒞'_mem C hC
        have hdisj : Disjoint (semiPts C true) (semiPts C false) := by
          rw [Finset.disjoint_left]
          intro k h1 h2
          have h1' := (Finset.mem_filter.mp h1).2.2
          have h2' := (Finset.mem_filter.mp h2).2.2
          simp only [↓reduceIte, Bool.false_eq_true] at h1' h2'
          linarith
        rw [← Finset.card_union_of_disjoint hdisj]
        refine Finset.card_bij (fun k _ => ptOf k) ?_ ?_ ?_
        · intro k hk
          rcases Finset.mem_union.mp hk with h | h
          · exact Finset.mem_filter.mpr ⟨hptOf_mem k, (Finset.mem_filter.mp h).2.1⟩
          · exact Finset.mem_filter.mpr ⟨hptOf_mem k, (Finset.mem_filter.mp h).2.1⟩
        · intro _ _ _ _ h; exact hptOf_inj h
        · intro p hp
          obtain ⟨hpP', hpd⟩ := Finset.mem_filter.mp hp
          obtain ⟨k, rfl⟩ := hptOf_surj p hpP'
          have hne_c : ptOf k ≠ C.1 := fun h => by rw [h, dist_self] at hpd; linarith
          have hy_ne : y k ≠ C.1 1 := fun h => hne_c (hy_inj_P' (hptOf_mem k) hC1P' h)
          refine ⟨k, ?_, rfl⟩
          rcases lt_or_gt_of_ne hy_ne with hlt | hgt
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpd, by simp [hlt]⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpd, by simp [hgt]⟩)
      rw [Finset.sum_congr rfl hC_sum]
      -- Now ∑ C ∈ 𝒞', |{p ∈ P' | dist p C.1 = C.2}| = |{(c, p) ∈ P' × P' | c ≠ p}| = n * (n - 1)!
      let ordP' := (P' ×ˢ P').filter (fun cp => cp.1 ≠ cp.2)
      have hpart : ordP'.card = ∑ C ∈ 𝒞', (P'.filter (fun p => dist p C.1 = C.2)).card := by
        have hEq : ordP' = 𝒞'.biUnion (fun C => (P'.filter (fun p => dist p C.1 = C.2)).image (fun p => (C.1, p))) := by
          ext ⟨c', p'⟩
          simp only [ordP', Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
          constructor
          · rintro ⟨⟨hc', hp'⟩, hne⟩
            rcases Finset.mem_image.mp hc' with ⟨c₀, hc₀P, rfl⟩
            rcases Finset.mem_image.mp hp' with ⟨p₀, hp₀P, rfl⟩
            have hne₀ : c₀ ≠ p₀ := fun h => hne (congrArg (rotUnit u v) h)
            have hC₀_mem : (c₀, dist c₀ p₀) ∈ 𝒞 :=
              Finset.mem_biUnion.mpr ⟨c₀, hc₀P, Finset.mem_image_of_mem _
                (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hne₀.symm, hp₀P⟩))⟩
            have hC'_mem : (rotUnit u v c₀, dist c₀ p₀) ∈ 𝒞' :=
              Finset.mem_image.mpr ⟨(c₀, dist c₀ p₀), hC₀_mem, rfl⟩
            refine ⟨(rotUnit u v c₀, dist c₀ p₀), hC'_mem, rotUnit u v p₀, ⟨hp', ?_⟩, rfl⟩
            rw [rotUnit_dist huv, dist_comm]
          · rintro ⟨C, hC, q, ⟨hqP', hqd⟩, hEq⟩
            rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
            have ⟨hC1, hCr⟩ := h𝒞'_mem C hC
            refine ⟨⟨hC1, hqP'⟩, fun h => ?_⟩
            rw [← h, dist_self] at hqd; linarith
        have hdisj : Set.PairwiseDisjoint (𝒞' : Set (EuclideanSpace ℝ (Fin 2) × ℝ))
            (fun C => (P'.filter (fun p => dist p C.1 = C.2)).image (fun p => (C.1, p))) := by
          intro C₁ _ C₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro cp h1 h2
          rcases Finset.mem_image.mp h1 with ⟨p₁, hp1, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨p₂, hp2, hEq⟩
          rcases Prod.mk.inj hEq with ⟨hcEq, hpEq⟩
          subst hpEq
          have hd1 := (Finset.mem_filter.mp hp1).2
          have hd2 := (Finset.mem_filter.mp hp2).2
          rw [hcEq] at hd2
          exact hne (Prod.ext hcEq.symm (hd1.symm.trans hd2))
        rw [hEq, Finset.card_biUnion hdisj]
        refine Finset.sum_congr rfl fun C _ =>
          Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
      rw [← hpart]
      -- Compute ordP'.card = P'.card * (P'.card - 1) = n * (n - 1)!
      have h1 : ordP'.card + P'.card = (P' ×ˢ P').card := by
        have hdisj : Disjoint ordP' (P'.image (fun p => (p, p))) := by
          rw [Finset.disjoint_left]
          intro pq h1 h2
          rcases Finset.mem_image.mp h2 with ⟨p, _, rfl⟩
          exact (Finset.mem_filter.mp h1).2 rfl
        have hunion : ordP' ∪ P'.image (fun p => (p, p)) = P' ×ˢ P' := by
          ext ⟨a, b⟩
          simp only [ordP', Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro (⟨h, _⟩ | ⟨r, hr, hEq⟩)
            · exact h
            · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩; exact ⟨hr, hr⟩
          · rintro ⟨ha, hb⟩
            by_cases hab : a = b
            · subst hab; exact Or.inr ⟨a, ha, rfl⟩
            · exact Or.inl ⟨⟨ha, hb⟩, hab⟩
        have hdiag : (P'.image (fun p => (p, p))).card = P'.card :=
          Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
        rw [← hdiag, ← Finset.card_union_of_disjoint hdisj, hunion]
      rw [Finset.card_product, hP'_card] at h1
      have hmul : n * (n - 1) + n = n * n := by
        cases hn' : n with
        | zero => simp
        | succ m => simp [Nat.mul_succ]
      omega
    have hI_card_eq : I_all.card = ∑ C ∈ 𝒞', ((semiConsec C true).card + (semiConsec C false).card) := by
      rw [Finset.card_biUnion]
      · rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [Fintype.sum_bool,
          Finset.card_image_of_injective (semiConsec C true) (fun _ _ h => congrArg Prod.snd h),
          Finset.card_image_of_injective (semiConsec C false) (fun _ _ h => congrArg Prod.snd h)]
      · intro cs₁ _ cs₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x h1 h2
        rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
        exact hne (congrArg Prod.fst hEq).symm
    rw [← hinc_total, hI_card_eq, ← h𝒞'_card]
    calc ∑ C ∈ 𝒞', ((semiPts C true).card + (semiPts C false).card)
        ≤ ∑ C ∈ 𝒞', (((semiConsec C true).card + 1) + ((semiConsec C false).card + 1)) :=
          Finset.sum_le_sum fun C _ => Nat.add_le_add (hsemiConsec_card C true) (hsemiConsec_card C false)
      _ = (∑ C ∈ 𝒞', ((semiConsec C true).card + (semiConsec C false).card)) + 2 * 𝒞'.card := by
          have : ∑ C ∈ 𝒞', (((semiConsec C true).card + 1) + ((semiConsec C false).card + 1)) =
              ∑ C ∈ 𝒞', (((semiConsec C true).card + (semiConsec C false).card) + 2) :=
            Finset.sum_congr rfl fun C _ => by omega
          rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- Step 3: Split I_all into low-multiplicity (≤ M) and high-multiplicity (> M) arcs,
  -- where M = Nat.ceil (256 * √t)!
  let M : ℕ := Nat.ceil (256 * Real.sqrt (t : ℝ))
  have ht_posR : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht_pos
  have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt this
  have hM_lo : 256 * Real.sqrt (t : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  have hM_hi : (M : ℝ) ≤ 257 * Real.sqrt (t : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 256 * Real.sqrt (t : ℝ) by positivity)
    linarith
  have hM_pos : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast this
  let multOf (p : Fin n × Fin n) : ℕ := (I_all.filter (fun e => e.2 = p)).card
  let I_low : Finset Arc := I_all.filter (fun e => multOf e.2 ≤ M)
  let I_high : Finset Arc := I_all.filter (fun e => M < multOf e.2)
  have hI_split : I_all.card = I_low.card + I_high.card := by
    have hdisj : Disjoint I_low I_high := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      omega
    have hunion : I_low ∪ I_high = I_all := by
      ext e
      simp only [I_low, I_high, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hm : multOf e.2 ≤ M
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- Step 4: Bound |I_high| ≤ 2 * t * I(P', L_{> M}) via perpendicular bisectors + semicircle concavity!
  have hI_high_le : (I_high.card : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
    let L_rich := (linesOf P').filter (fun ℓ => M + 1 ≤ (P'.filter (fun p => p ∈ ℓ)).card)
    -- Every e ∈ I_high has perpBisector (ptOf e.2.1) (ptOf e.2.2) ∈ L_rich AND e.1.1.1 ∈ P' ∩ perpBisector!
    have hbis_rich : ∀ e ∈ I_high,
        let ℓ := perpBisector (ptOf e.2.1) (ptOf e.2.2)
        ℓ ∈ L_rich ∧ e.1.1.1 ∈ P' ∧ e.1.1.1 ∈ ℓ := by
      intro e heH
      obtain ⟨heA, hgtM⟩ := Finset.mem_filter.mp heH
      have ⟨hC', hcon⟩ := hI_all_mem e heA
      obtain ⟨helt, h1on, h2on, _⟩ := hsemiConsec_spec e.1.1 e.1.2 e.2 hcon
      have hne_pt : ptOf e.2.1 ≠ ptOf e.2.2 := fun h => ne_of_lt helt (hptOf_inj h)
      let ℓ := perpBisector (ptOf e.2.1) (ptOf e.2.2)
      -- Each arc e' ∈ I_all with e'.2 = e.2 has a DISTINCT center e'.1.1.1 ∈ P' ∩ ℓ!
      let F := I_all.filter (fun e' => e'.2 = e.2)
      have hF_inj : Set.InjOn (fun e' : Arc => e'.1.1.1) F := by
        intro e₁ h1 e₂ h2 hcEq
        dsimp only at hcEq
        obtain ⟨h1A, h1p⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2A, h2p⟩ := Finset.mem_filter.mp h2
        have hpEq : e₁.2 = e₂.2 := h1p.trans h2p.symm
        obtain ⟨_, h1on1, _, _⟩ := hsemiConsec_spec e₁.1.1 e₁.1.2 e₁.2 (hI_all_mem e₁ h1A).2
        obtain ⟨_, h2on1, _, _⟩ := hsemiConsec_spec e₂.1.1 e₂.1.2 e₂.2 (hI_all_mem e₂ h2A).2
        have hrEq : e₁.1.1.2 = e₂.1.1.2 := by
          rw [← h1on1.1, ← h2on1.1, hpEq, hcEq]
        have hCeq : e₁.1.1 = e₂.1.1 := Prod.ext hcEq hrEq
        have hσeq : e₁.1.2 = e₂.1.2 := by
          have hs1 := h1on1.2; have hs2 := h2on1.2
          rw [hpEq, hcEq] at hs1
          cases hσ1 : e₁.1.2 <;> cases hσ2 : e₂.1.2 <;> simp [hσ1, hσ2] at hs1 hs2 ⊢ <;> linarith
        exact Prod.ext (Prod.ext hCeq hσeq) hpEq
      have hF_sub : F.image (fun e' : Arc => e'.1.1.1) ⊆ P'.filter (fun p => p ∈ ℓ) := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨e', he', rfl⟩
        obtain ⟨he'A, he'p⟩ := Finset.mem_filter.mp he'
        obtain ⟨_, h1', h2', _⟩ := hsemiConsec_spec e'.1.1 e'.1.2 e'.2 (hI_all_mem e' he'A).2
        rw [he'p] at h1' h2'
        refine Finset.mem_filter.mpr ⟨(h𝒞'_mem e'.1.1 (hI_all_mem e' he'A).1).1, ?_⟩
        rw [mem_perpBisector_iff hne_pt, dist_comm _ (ptOf e.2.1), dist_comm _ (ptOf e.2.2)]
        exact h1'.1.trans h2'.1.symm
      have hcard_ge : M + 1 ≤ (P'.filter (fun p => p ∈ ℓ)).card := by
        have h1 : F.card ≤ (P'.filter (fun p => p ∈ ℓ)).card := by
          rw [← Finset.card_image_of_injOn hF_inj]
          exact Finset.card_le_card hF_sub
        exact le_trans hgtM h1
      -- Since M + 1 ≥ 2, ℓ contains ≥ 2 points of P', hence ℓ ∈ linesOf P'!
      have hℓ_in_lines : ℓ ∈ linesOf P' := by
        obtain ⟨p₁, hp₁, p₂, hp₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (P'.filter (fun p => p ∈ ℓ)).card)
        have hℓeq : lineThrough p₁ p₂ = ℓ := lineThrough_eq_of_mem (isLine_perpBisector hne_pt) h12
          (Finset.mem_filter.mp hp₁).2 (Finset.mem_filter.mp hp₂).2
        exact mem_linesOf_iff.mpr ⟨p₁, (Finset.mem_filter.mp hp₁).1, p₂, (Finset.mem_filter.mp hp₂).1, h12, hℓeq.symm⟩
      have he_on_ℓ : e.1.1.1 ∈ ℓ := by
        rw [mem_perpBisector_iff hne_pt, dist_comm _ (ptOf e.2.1), dist_comm _ (ptOf e.2.2)]
        exact h1on.1.trans h2on.1.symm
      exact ⟨Finset.mem_filter.mpr ⟨hℓ_in_lines, hcard_ge⟩, (h𝒞'_mem e.1.1 hC').1, he_on_ℓ⟩
    -- Map I_high INJECTIVELY into {(ℓ, C, σ) | ℓ ∈ L_rich, C ∈ 𝒞', C.1 ∈ ℓ, σ : Bool}!
    let targetSet := L_rich.biUnion fun ℓ =>
      ((𝒞'.filter (fun C => C.1 ∈ ℓ)) ×ˢ (Finset.univ : Finset Bool)).image (fun cs => (ℓ, cs))
    have hinj_high : Set.InjOn
        (fun e : Arc => (perpBisector (ptOf e.2.1) (ptOf e.2.2), e.1)) I_high := by
      intro e₁ h1 e₂ h2 hEq
      have hbisEq : perpBisector (ptOf e₁.2.1) (ptOf e₁.2.2) = perpBisector (ptOf e₂.2.1) (ptOf e₂.2.2) :=
        congrArg Prod.fst hEq
      have hcsEq : e₁.1 = e₂.1 := congrArg Prod.snd hEq
      have h1A := (Finset.mem_filter.mp h1).1
      have h2A := (Finset.mem_filter.mp h2).1
      obtain ⟨h1lt, h1u, h1v, h1no⟩ := hsemiConsec_spec e₁.1.1 e₁.1.2 e₁.2 (hI_all_mem e₁ h1A).2
      obtain ⟨h2lt, h2u, h2v, h2no⟩ := hsemiConsec_spec e₂.1.1 e₂.1.2 e₂.2 (hI_all_mem e₂ h2A).2
      rw [← hcsEq] at h2u h2v h2no
      have hcases := semicircle_consec_bisector_unique h1u.1 h1v.1 h2u.1 h2v.1
        h1u.2 h1v.2 h2u.2 h2v.2
        (by rw [hptOf_x, hptOf_x]; exact hx_strict h1lt)
        (by rw [hptOf_x, hptOf_x]; exact hx_strict h2lt) hbisEq
      rcases hcases with ⟨huEq, hvEq⟩ | ⟨h12, h21⟩ | ⟨h21, h12⟩
      · exact Prod.ext hcsEq (Prod.ext (hptOf_inj huEq) (hptOf_inj hvEq))
      · exfalso
        rw [hptOf_x, hptOf_x] at h12 h21
        exact h1no e₂.2.1 (hx_strict.lt_iff_lt.mp h12) (hx_strict.lt_iff_lt.mp h21) h2u
      · exfalso
        rw [hptOf_x, hptOf_x] at h21 h12
        exact h2no e₁.2.1 (hx_strict.lt_iff_lt.mp h21) (hx_strict.lt_iff_lt.mp h12) h1u
    have hhigh_card_le : I_high.card ≤ 2 * t * lineIncidences P' L_rich := by
      have hsub : I_high.image (fun e : Arc => (perpBisector (ptOf e.2.1) (ptOf e.2.2), e.1)) ⊆ targetSet := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨e, heH, rfl⟩
        have ⟨hℓ, _, hcℓ⟩ := hbis_rich e heH
        have hC' := (hI_all_mem e (Finset.mem_filter.mp heH).1).1
        refine Finset.mem_biUnion.mpr ⟨perpBisector (ptOf e.2.1) (ptOf e.2.2), hℓ,
          Finset.mem_image.mpr ⟨e.1, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hC', hcℓ⟩, Finset.mem_univ _⟩, rfl⟩⟩
      -- For each c' ∈ P', at most t circles in 𝒞' have center c'!
      have hcenter_le : ∀ c' ∈ P', (𝒞'.filter (fun C => C.1 = c')).card ≤ t := by
        intro c' hc'
        rcases Finset.mem_image.mp hc' with ⟨c₀, hc₀P, rfl⟩
        have hsubC : 𝒞'.filter (fun C => C.1 = rotUnit u v c₀) ⊆
            ((P.erase c₀).image (dist c₀)).image (fun r => (rotUnit u v c₀, r)) := by
          intro C hC
          obtain ⟨hC', hCc⟩ := Finset.mem_filter.mp hC
          rcases Finset.mem_image.mp hC' with ⟨C₀, hC₀, rfl⟩
          have hc₀eq : C₀.1 = c₀ := rotUnit_injective huv hCc
          rcases Finset.mem_biUnion.mp hC₀ with ⟨c₁, _, hrc⟩
          rcases Finset.mem_image.mp hrc with ⟨r, hr, hEq⟩
          have hc1 : c₁ = c₀ := (congrArg Prod.fst hEq).trans hc₀eq
          subst hc1
          have hrEq : C₀.2 = r := (congrArg Prod.snd hEq).symm
          exact Finset.mem_image.mpr ⟨r, hr, Prod.ext (congrArg (rotUnit u v) hc₀eq.symm) hrEq.symm⟩
        exact le_trans (Finset.card_le_card hsubC) (le_trans Finset.card_image_le (hmax c₀ hc₀P))
      have htarget_le : targetSet.card ≤ 2 * t * lineIncidences P' L_rich := by
        unfold lineIncidences
        rw [Finset.mul_sum]
        calc targetSet.card
            ≤ ∑ ℓ ∈ L_rich, (((𝒞'.filter (fun C => C.1 ∈ ℓ)) ×ˢ (Finset.univ : Finset Bool)).image
                (fun cs => (ℓ, cs))).card := Finset.card_biUnion_le
          _ ≤ ∑ ℓ ∈ L_rich, 2 * t * (P'.filter (fun p => p ∈ ℓ)).card := by
              refine Finset.sum_le_sum fun ℓ _ => ?_
              have h1 : (((𝒞'.filter (fun C => C.1 ∈ ℓ)) ×ˢ (Finset.univ : Finset Bool)).image
                  (fun cs => (ℓ, cs))).card ≤ 2 * (𝒞'.filter (fun C => C.1 ∈ ℓ)).card :=
                le_trans Finset.card_image_le (by simp [Finset.card_product, mul_comm])
              have h2 : (𝒞'.filter (fun C => C.1 ∈ ℓ)).card ≤ t * (P'.filter (fun p => p ∈ ℓ)).card := by
                have hcov : 𝒞'.filter (fun C => C.1 ∈ ℓ) ⊆
                    (P'.filter (fun p => p ∈ ℓ)).biUnion (fun c' => 𝒞'.filter (fun C => C.1 = c')) := by
                  intro C hC
                  obtain ⟨hC', hCℓ⟩ := Finset.mem_filter.mp hC
                  exact Finset.mem_biUnion.mpr ⟨C.1, Finset.mem_filter.mpr ⟨(h𝒞'_mem C hC').1, hCℓ⟩,
                    Finset.mem_filter.mpr ⟨hC', rfl⟩⟩
                calc (𝒞'.filter (fun C => C.1 ∈ ℓ)).card
                    ≤ ((P'.filter (fun p => p ∈ ℓ)).biUnion (fun c' => 𝒞'.filter (fun C => C.1 = c'))).card :=
                      Finset.card_le_card hcov
                  _ ≤ ∑ c' ∈ P'.filter (fun p => p ∈ ℓ), (𝒞'.filter (fun C => C.1 = c')).card :=
                      Finset.card_biUnion_le
                  _ ≤ ∑ _c' ∈ P'.filter (fun p => p ∈ ℓ), t :=
                      Finset.sum_le_sum fun c' hc' => hcenter_le c' (Finset.mem_filter.mp hc').1
                  _ = t * (P'.filter (fun p => p ∈ ℓ)).card := by simp [mul_comm]
              calc (((𝒞'.filter (fun C => C.1 ∈ ℓ)) ×ˢ (Finset.univ : Finset Bool)).image
                      (fun cs => (ℓ, cs))).card
                  ≤ 2 * (𝒞'.filter (fun C => C.1 ∈ ℓ)).card := h1
                _ ≤ 2 * (t * (P'.filter (fun p => p ∈ ℓ)).card) := Nat.mul_le_mul_left 2 h2
                _ = 2 * t * (P'.filter (fun p => p ∈ ℓ)).card := (Nat.mul_assoc 2 t _).symm
      rw [← Finset.card_image_of_injOn hinj_high]
      exact le_trans (Finset.card_le_card hsub) htarget_le
    -- Apply k_rich_incidences_bound with k = M + 1 ≥ 2!
    have hkr := k_rich_incidences_bound P' L_rich
      (fun ℓ hℓ => isLine_of_mem_linesOf (Finset.mem_filter.mp hℓ).1)
      (by omega : 2 ≤ M + 1)
      (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2)
    rw [hP'_card] at hkr
    have hhighR : (I_high.card : ℝ) ≤ 2 * (t : ℝ) * (lineIncidences P' L_rich : ℝ) := by
      exact_mod_cast hhigh_card_le
    have hM1_lo : 256 * Real.sqrt (t : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have hM1_sq : 65536 * (t : ℝ) ≤ (((M + 1 : ℕ) : ℝ)) ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hM1_lo 2
      rw [mul_pow, Real.sq_sqrt (le_of_lt ht_posR)] at hsq
      linarith
    have hterm1 : 2 * (t : ℝ) * (4096 * (n : ℝ) ^ 2 / (((M + 1 : ℕ) : ℝ)) ^ 2) ≤ (n : ℝ) ^ 2 / 8 := by
      have hpos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ)) ^ 2 := by positivity
      have h1 : 8192 * (t : ℝ) * (n : ℝ) ^ 2 / (((M + 1 : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 / 8 := by
        rw [div_le_iff₀ hpos]
        nlinarith [sq_nonneg (n : ℝ)]
      have h2 : 2 * (t : ℝ) * (4096 * (n : ℝ) ^ 2 / (((M + 1 : ℕ) : ℝ)) ^ 2) =
          8192 * (t : ℝ) * (n : ℝ) ^ 2 / (((M + 1 : ℕ) : ℝ)) ^ 2 := by ring
      linarith
    have hterm2 : 2 * (t : ℝ) * (16 * (n : ℝ)) ≤ (n : ℝ) ^ 2 / 8 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hkr (show (0 : ℝ) ≤ 2 * (t : ℝ) by positivity)
    linarith
  -- Step 5: Lower bound |I_low| ≥ n² / 2!
  have hI_low_lb : (n : ℝ) ^ 2 / 2 ≤ (I_low.card : ℝ) := by
    have hI_allR : (n : ℝ) * ((n : ℝ) - 1) ≤ (I_all.card : ℝ) + 2 * (𝒞.card : ℝ) := by
      have h1 : ((n * (n - 1) : ℕ) : ℝ) ≤ (I_all.card : ℝ) + 2 * (𝒞.card : ℝ) := by exact_mod_cast hI_all_lb
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h1
      exact h1
    have h𝒞R : (𝒞.card : ℝ) ≤ (n : ℝ) * (t : ℝ) := by exact_mod_cast h𝒞_card
    have hsplitR : (I_all.card : ℝ) = (I_low.card : ℝ) + (I_high.card : ℝ) := by exact_mod_cast hI_split
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_small
    nlinarith
  -- Step 6: Build MultiSlabWiring on I_low via xMonotone_multi_to_slabWiring and bound crossings ≤ 𝒞.card²!
  let γ_arc : Arc → ℝ → ℝ := fun e t =>
    e.1.1.1 1 + (if e.1.2 then 1 else -1) * Real.sqrt (e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2)
  have hγ_on : ∀ e ∈ I_all, ∀ (t : ℝ),
      x e.2.1 ≤ t → t ≤ x e.2.2 →
      dist (mkPt t (γ_arc e t)) e.1.1.1 = e.1.1.2 ∧
      (x e.2.1 < t → t < x e.2.2 →
        if e.1.2 then e.1.1.1 1 < γ_arc e t else γ_arc e t < e.1.1.1 1) := by
    intro e he t ht1 ht2
    have ⟨hC', hcon⟩ := hI_all_mem e he
    have hr_pos : 0 < e.1.1.2 := (h𝒞'_mem e.1.1 hC').2
    obtain ⟨_, h1on, h2on, _⟩ := hsemiConsec_spec e.1.1 e.1.2 e.2 hcon
    have hsq1 : (x e.2.1 - e.1.1.1 0) ^ 2 + (y e.2.1 - e.1.1.1 1) ^ 2 = e.1.1.2 ^ 2 := by
      have := dist_sq_eq_normSq2 (ptOf e.2.1) e.1.1.1
      rw [h1on.1] at this; simpa [normSq2, PiLp.sub_apply, hptOf_x, y] using this.symm
    have hsq2 : (x e.2.2 - e.1.1.1 0) ^ 2 + (y e.2.2 - e.1.1.1 1) ^ 2 = e.1.1.2 ^ 2 := by
      have := dist_sq_eq_normSq2 (ptOf e.2.2) e.1.1.1
      rw [h2on.1] at this; simpa [normSq2, PiLp.sub_apply, hptOf_x, y] using this.symm
    have hlo1 : e.1.1.1 0 - e.1.1.2 ≤ x e.2.1 := by nlinarith [sq_nonneg (y e.2.1 - e.1.1.1 1)]
    have hhi2 : x e.2.2 ≤ e.1.1.1 0 + e.1.1.2 := by nlinarith [sq_nonneg (y e.2.2 - e.1.1.1 1)]
    have hnn : 0 ≤ e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2 := by nlinarith
    constructor
    · have hdsq : dist (mkPt t (γ_arc e t)) e.1.1.1 ^ 2 = e.1.1.2 ^ 2 := by
        rw [dist_sq_eq_normSq2]
        simp only [normSq2, PiLp.sub_apply, mkPt_zero, mkPt_one, γ_arc]
        have hsgn : ((if e.1.2 then (1 : ℝ) else -1) * Real.sqrt (e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2)) ^ 2 =
            e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hnn]; cases e.1.2 <;> norm_num
        linarith [show (e.1.1.1 1 + (if e.1.2 then (1 : ℝ) else -1) * Real.sqrt (e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2) -
            e.1.1.1 1) ^ 2 = ((if e.1.2 then (1 : ℝ) else -1) * Real.sqrt (e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2)) ^ 2 by ring]
      have : (dist (mkPt t (γ_arc e t)) e.1.1.1 - e.1.1.2) * (dist (mkPt t (γ_arc e t)) e.1.1.1 + e.1.1.2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith [dist_nonneg (x := mkPt t (γ_arc e t)) (y := e.1.1.1)]
    · intro hlt1 hlt2
      have hpos : 0 < e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2 := by nlinarith
      have hsqpos : 0 < Real.sqrt (e.1.1.2 ^ 2 - (t - e.1.1.1 0) ^ 2) := Real.sqrt_pos.mpr hpos
      cases hσ : e.1.2 <;> simp [γ_arc, hσ] <;> linarith
  have hγ_eq_y : ∀ e ∈ I_all, ∀ k : Fin n, onSemi e.1.1 e.1.2 k → γ_arc e (x k) = y k := by
    intro e _ k hkon
    have hsq : (x k - e.1.1.1 0) ^ 2 + (y k - e.1.1.1 1) ^ 2 = e.1.1.2 ^ 2 := by
      have := dist_sq_eq_normSq2 (ptOf k) e.1.1.1
      rw [hkon.1] at this; simpa [normSq2, PiLp.sub_apply, hptOf_x, y] using this.symm
    have hsub : e.1.1.2 ^ 2 - (x k - e.1.1.1 0) ^ 2 = (y k - e.1.1.1 1) ^ 2 := by linarith
    have hsp := hkon.2
    cases hσ : e.1.2
    · simp only [hσ, Bool.false_eq_true, ↓reduceIte] at hsp
      simp only [γ_arc, hσ, Bool.false_eq_true, ↓reduceIte, hsub]
      rw [show (y k - e.1.1.1 1) ^ 2 = (e.1.1.1 1 - y k) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      ring
    · simp only [hσ, ↓reduceIte] at hsp
      simp only [γ_arc, hσ, ↓reduceIte, hsub]
      rw [Real.sqrt_sq (by linarith)]
      ring
  have hsame_semi_disj : ∀ C σ, ∀ p₁ ∈ semiConsec C σ, ∀ p₂ ∈ semiConsec C σ, p₁ ≠ p₂ →
      p₁.2 ≤ p₂.1 ∨ p₂.2 ≤ p₁.1 := by
    intro C σ p₁ hp1 p₂ hp2 hne
    obtain ⟨h1lt, h1a, h1b, h1no⟩ := hsemiConsec_spec C σ p₁ hp1
    obtain ⟨h2lt, h2a, h2b, h2no⟩ := hsemiConsec_spec C σ p₂ hp2
    by_contra hnot; push Not at hnot; obtain ⟨h21, h12⟩ := hnot
    rcases lt_trichotomy p₁.1 p₂.1 with h | h | h
    · exact h1no p₂.1 h h21 h2a
    · rcases lt_trichotomy p₁.2 p₂.2 with h' | h' | h'
      · exact h2no p₁.2 (h ▸ h1lt) h' h1b
      · exact hne (Prod.ext h h')
      · exact h1no p₂.2 (h.symm ▸ h2lt) h' h2b
    · exact h2no p₁.1 h h12 h1a
  -- Build finite X_int of all non-P' circle-circle intersection x-coordinates!
  let interPts' : Finset (EuclideanSpace ℝ (Fin 2)) := interPts.image (rotUnit u v)
  let X_int : Finset ℝ := (interPts' \ P').image (fun p => p 0)
  have hX_disj : ∀ k : Fin n, x k ∉ X_int := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨q', hq', hqx⟩
    obtain ⟨hq'I, hq'notP⟩ := Finset.mem_sdiff.mp hq'
    rcases Finset.mem_image.mp hq'I with ⟨q₀, hq₀I, rfl⟩
    rcases Finset.mem_image.mp (hptOf_mem k) with ⟨p₀, hp₀P, hp₀eq⟩
    have hne : q₀ ≠ p₀ := fun h => hq'notP (h ▸ Finset.mem_image_of_mem _ hp₀P)
    have hne0 := (hAll_xy q₀ (Finset.mem_union_right _ hq₀I) p₀ (Finset.mem_union_left _ hp₀P) hne).1
    apply hne0
    rw [hqx, ← hptOf_x k, ← hp₀eq]
  have hI_low_sub : I_low ⊆ I_all := Finset.filter_subset _ _
  -- Check that every interior crossing of two distinct arcs in I_low occurs on DIFFERENT circles
  -- and lands in X_int (and in interPts' \ P')!
  have hX_low : ∀ e₁ ∈ I_low, ∀ e₂ ∈ I_low, e₁ ≠ e₂ → ∀ t_int : ℝ,
      x (max e₁.2.1 e₂.2.1) < t_int → t_int < x (min e₁.2.2 e₂.2.2) →
      γ_arc e₁ t_int = γ_arc e₂ t_int →
      e₁.1.1 ≠ e₂.1.1 ∧ mkPt t_int (γ_arc e₁ t_int) ∈ interPts' \ P' ∧ t_int ∈ X_int := by
    intro e₁ h1 e₂ h2 hne t_int ht1 ht2 hγeq
    have h1A := hI_low_sub h1; have h2A := hI_low_sub h2
    have hxa1 : x e₁.2.1 < t_int := lt_of_le_of_lt (hx_strict.monotone (le_max_left _ _)) ht1
    have hxb1 : t_int < x e₁.2.2 := lt_of_lt_of_le ht2 (hx_strict.monotone (min_le_left _ _))
    have hxa2 : x e₂.2.1 < t_int := lt_of_le_of_lt (hx_strict.monotone (le_max_right _ _)) ht1
    have hxb2 : t_int < x e₂.2.2 := lt_of_lt_of_le ht2 (hx_strict.monotone (min_le_right _ _))
    have h1on := hγ_on e₁ h1A t_int (le_of_lt hxa1) (le_of_lt hxb1)
    have h2on := hγ_on e₂ h2A t_int (le_of_lt hxa2) (le_of_lt hxb2)
    have h1s := h1on.2 hxa1 hxb1
    have h2s := h2on.2 hxa2 hxb2
    -- First show e₁.1.1 ≠ e₂.1.1 (same circle → same sign from strict y-ineq → disjoint consecutive arcs!).
    have hCne : e₁.1.1 ≠ e₂.1.1 := by
      intro hCeq
      have hσeq : e₁.1.2 = e₂.1.2 := by
        rw [hCeq, hγeq] at h1s
        cases hσ1 : e₁.1.2 <;> cases hσ2 : e₂.1.2 <;> simp [hσ1, hσ2] at h1s h2s ⊢ <;> linarith
      have hcsEq : e₁.1 = e₂.1 := Prod.ext hCeq hσeq
      have hpne : e₁.2 ≠ e₂.2 := fun hp => hne (Prod.ext hcsEq hp)
      rcases hsame_semi_disj e₁.1.1 e₁.1.2 e₁.2 (hI_all_mem e₁ h1A).2 e₂.2 (hcsEq ▸ (hI_all_mem e₂ h2A).2) hpne with hle | hle
      · have : x e₁.2.2 ≤ x e₂.2.1 := hx_strict.monotone hle; linarith
      · have : x e₂.2.2 ≤ x e₁.2.1 := hx_strict.monotone hle; linarith
    -- Also show e₁.1.1.1 ≠ e₂.1.1.1 (concentric circles of different radii never intersect!).
    have hctr_ne : e₁.1.1.1 ≠ e₂.1.1.1 := by
      intro hceq
      have hrEq : e₁.1.1.2 = e₂.1.1.2 := by
        have h1d := h1on.1; have h2d := h2on.1
        rw [hγeq, hceq] at h1d
        exact h1d.symm.trans h2d
      exact hCne (Prod.ext hceq hrEq)
    -- Show q' = mkPt t_int (γ_arc e₁ t_int) ∈ interPts' \ P'!
    let q' := mkPt t_int (γ_arc e₁ t_int)
    have hq'_inter : q' ∈ interPts' := by
      rcases Finset.mem_image.mp (hI_all_mem e₁ h1A).1 with ⟨C₁₀, hC₁₀, hC₁eq⟩
      rcases Finset.mem_image.mp (hI_all_mem e₂ h2A).1 with ⟨C₂₀, hC₂₀, hC₂eq⟩
      have hctr₀_ne : C₁₀.1 ≠ C₂₀.1 := fun h => hctr_ne (by rw [← hC₁eq, ← hC₂eq, h])
      let q₀ := rotUnit u (-v) q'
      have hq₀1 : dist q₀ C₁₀.1 = C₁₀.2 := by
        have := rotUnit_dist huv q₀ C₁₀.1
        rw [rotUnit_inv_comp huv] at this
        have h1d := h1on.1; rw [← hC₁eq] at h1d; exact this.symm.trans h1d
      have hq₀2 : dist q₀ C₂₀.1 = C₂₀.2 := by
        have := rotUnit_dist huv q₀ C₂₀.1
        rw [rotUnit_inv_comp huv] at this
        have h2d := h2on.1; rw [← hγeq, ← hC₂eq] at h2d; exact this.symm.trans h2d
      have hq₀_in : q₀ ∈ interPts :=
        Finset.mem_biUnion.mpr ⟨(C₁₀, C₂₀), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hC₁₀, hC₂₀⟩, hctr₀_ne⟩,
          mem_circleInterPts_of_dist hctr₀_ne hq₀1 hq₀2⟩
      exact Finset.mem_image.mpr ⟨q₀, hq₀_in, rotUnit_inv_comp huv q'⟩
    have hq'_notP : q' ∉ P' := by
      intro hq'P
      obtain ⟨k, hk⟩ := hptOf_surj q' hq'P
      have hkx : x k = t_int := by rw [← hptOf_x k, hk]; simp [q']
      have hky : y k = γ_arc e₁ t_int := by change ptOf k 1 = _; rw [hk]; simp [q']
      have hk1 : e₁.2.1 < k := hx_strict.lt_iff_lt.mp (hkx.symm ▸ hxa1)
      have hk2 : k < e₁.2.2 := hx_strict.lt_iff_lt.mp (hkx.symm ▸ hxb1)
      have hno := (hsemiConsec_spec e₁.1.1 e₁.1.2 e₁.2 (hI_all_mem e₁ h1A).2).2.2.2 k hk1 hk2
      apply hno
      refine ⟨by rw [hk]; exact h1on.1, by rw [hky]; exact h1s⟩
    have hq'_sdiff : q' ∈ interPts' \ P' := Finset.mem_sdiff.mpr ⟨hq'_inter, hq'_notP⟩
    exact ⟨hCne, hq'_sdiff, Finset.mem_image.mpr ⟨q', hq'_sdiff, by simp [q']⟩⟩
  -- Invoke xMonotone_multi_to_slabWiring on I_low!
  obtain ⟨Mw, ε, hε_pos, hε_adj, hinv_spec⟩ := xMonotone_multi_to_slabWiring x y hx_strict
    I_low (fun e => e.2.1) (fun e => e.2.2)
    (fun e he => (hsemiConsec_spec e.1.1 e.1.2 e.2 (hI_all_mem e (hI_low_sub he)).2).1)
    γ_arc
    (fun e _ => by
      exact (continuous_const.add (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.sub ((continuous_id.sub continuous_const).pow 2))))).continuousOn)
    (fun e he => hγ_eq_y e (hI_low_sub he) e.2.1
      (hsemiConsec_spec e.1.1 e.1.2 e.2 (hI_all_mem e (hI_low_sub he)).2).2.1)
    (fun e he => hγ_eq_y e (hI_low_sub he) e.2.2
      (hsemiConsec_spec e.1.1 e.1.2 e.2 (hI_all_mem e (hI_low_sub he)).2).2.2.1)
    (fun e he k hk1 hk2 hEq => by
      have heA := hI_low_sub he
      have h1 := hγ_on e heA (x k) (le_of_lt (hx_strict hk1)) (le_of_lt (hx_strict hk2))
      have hptk : mkPt (x k) (γ_arc e (x k)) = ptOf k := pt_ext (by simp [hptOf_x]) (by simp [hEq, y])
      have hno := (hsemiConsec_spec e.1.1 e.1.2 e.2 (hI_all_mem e heA).2).2.2.2 k hk1 hk2
      exact hno ⟨by rw [← hptk]; exact h1.1, by rw [← hEq]; exact h1.2 (hx_strict hk1) (hx_strict hk2)⟩)
    X_int
    (fun e₁ h1 e₂ h2 hne t_int ht1 ht2 hγeq => (hX_low e₁ h1 e₂ h2 hne t_int ht1 ht2 hγeq).2.2)
    hX_disj
  -- Step 7: Bound Mw.crossings ≤ 𝒞.card² by injecting (Bool × allInvs) into {(C₁, C₂, q') | C₁ ≠ C₂ ∈ 𝒞', q' ∈ circleInterPts C₁ C₂}!
  have hMw_cr_le : Mw.crossings ≤ 𝒞.card ^ 2 := by
    let allInvs : Finset (Fin (n + 1) × (Arc × Arc)) :=
      (Finset.univ : Finset (Fin (n + 1))).biUnion fun s =>
        (invPairs (multiActiveEdges I_low (fun e => e.2.1) (fun e => e.2.2) s) (Mw.posL s) (Mw.posR s)).image
          (fun p => (s, p))
    have hallInvs_card : allInvs.card = Mw.crossings := by
      unfold MultiSlabWiring.crossings
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun s _ =>
          Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
      · intro s₁ _ s₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro z h1 h2
        rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
        exact hne (congrArg Prod.fst hEq).symm
    -- For each z = (s, (e₁, e₂)) ∈ allInvs, pick a witness crossing point q_of z = mkPt t_int (γ_arc e₁ t_int)!
    have hinv_wit : ∀ z ∈ allInvs,
        let s := z.1; let e₁ := z.2.1; let e₂ := z.2.2
        e₁ ∈ I_low ∧ e₂ ∈ I_low ∧ e₁ ≠ e₂ ∧
        ∃ (h1 : 0 < s.val) (h2 : s.val < n) (t_int : ℝ),
          x ⟨s.val - 1, by omega⟩ + ε < t_int ∧ t_int < x ⟨s.val, h2⟩ - ε ∧
          x e₁.2.1 < t_int ∧ t_int < x e₁.2.2 ∧ x e₂.2.1 < t_int ∧ t_int < x e₂.2.2 ∧
          γ_arc e₁ t_int = γ_arc e₂ t_int ∧
          e₁.1.1.1 ≠ e₂.1.1.1 ∧
          mkPt t_int (γ_arc e₁ t_int) ∈ circleInterPts e₁.1.1.1 e₁.1.1.2 e₂.1.1.1 e₂.1.1.2 := by
      intro ⟨s, ⟨e₁, e₂⟩⟩ hz
      rcases Finset.mem_biUnion.mp hz with ⟨s', _, hs'⟩
      rcases Finset.mem_image.mp hs' with ⟨p, hp, hEq⟩
      have hsEq : s' = s := congrArg Prod.fst hEq
      have hpEq : p = (e₁, e₂) := congrArg Prod.snd hEq
      cases hsEq; cases hpEq
      obtain ⟨hprod, hLlt, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1act, h2act⟩ := Finset.mem_product.mp hprod
      obtain ⟨h1I, h1u, h1v⟩ := Finset.mem_filter.mp h1act
      obtain ⟨h2I, h2u, h2v⟩ := Finset.mem_filter.mp h2act
      dsimp only at h1u h1v h2u h2v
      have hne12 : e₁ ≠ e₂ := fun h => lt_irrefl _ (h ▸ hLlt)
      obtain ⟨h1s, h2s, t_int, htL, htR, hγeq, _⟩ := hinv_spec s e₁ e₂ hp
      have hxa1 : x e₁.2.1 < t_int := by
        have hle : e₁.2.1 ≤ ⟨s.val - 1, by omega⟩ := by change e₁.2.1.val ≤ s.val - 1; omega
        linarith only [hx_strict.monotone hle, htL, hε_pos]
      have hxb1 : t_int < x e₁.2.2 := by
        have hle : (⟨s.val, h2s⟩ : Fin n) ≤ e₁.2.2 := by change s.val ≤ e₁.2.2.val; omega
        linarith only [hx_strict.monotone hle, htR, hε_pos]
      have hxa2 : x e₂.2.1 < t_int := by
        have hle : e₂.2.1 ≤ ⟨s.val - 1, by omega⟩ := by change e₂.2.1.val ≤ s.val - 1; omega
        linarith only [hx_strict.monotone hle, htL, hε_pos]
      have hxb2 : t_int < x e₂.2.2 := by
        have hle : (⟨s.val, h2s⟩ : Fin n) ≤ e₂.2.2 := by change s.val ≤ e₂.2.2.val; omega
        linarith only [hx_strict.monotone hle, htR, hε_pos]
      have hmax : x (max e₁.2.1 e₂.2.1) < t_int := by
        rcases le_total e₁.2.1 e₂.2.1 with h | h
        · rw [max_eq_right h]; exact hxa2
        · rw [max_eq_left h]; exact hxa1
      have hmin : t_int < x (min e₁.2.2 e₂.2.2) := by
        rcases le_total e₁.2.2 e₂.2.2 with h | h
        · rw [min_eq_left h]; exact hxb1
        · rw [min_eq_right h]; exact hxb2
      have hCne := (hX_low e₁ h1I e₂ h2I hne12 t_int hmax hmin hγeq).1
      have h1d := (hγ_on e₁ (hI_low_sub h1I) t_int (le_of_lt hxa1) (le_of_lt hxb1)).1
      have h2d := (hγ_on e₂ (hI_low_sub h2I) t_int (le_of_lt hxa2) (le_of_lt hxb2)).1
      rw [← hγeq] at h2d
      have hctr_ne : e₁.1.1.1 ≠ e₂.1.1.1 := fun hceq =>
        hCne (Prod.ext hceq (by rw [hceq] at h1d; exact h1d.symm.trans h2d))
      exact ⟨h1I, h2I, hne12, h1s, h2s, t_int, htL, htR, hxa1, hxb1, hxa2, hxb2, hγeq, hctr_ne,
        mem_circleInterPts_of_dist hctr_ne h1d h2d⟩
    -- Target set: {(C₁, C₂, q') | C₁ ∈ 𝒞', C₂ ∈ 𝒞', q' ∈ circleInterPts C₁ C₂} has card ≤ 2 * |𝒞'|²!
    let crossTriples : Finset ((EuclideanSpace ℝ (Fin 2) × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ) × EuclideanSpace ℝ (Fin 2)) :=
      (𝒞' ×ˢ 𝒞').biUnion fun CC => (circleInterPts CC.1.1 CC.1.2 CC.2.1 CC.2.2).image (fun q => (CC.1, CC.2, q))
    have htriples_card : crossTriples.card ≤ 2 * 𝒞'.card ^ 2 := by
      calc crossTriples.card
          ≤ ∑ CC ∈ 𝒞' ×ˢ 𝒞', ((circleInterPts CC.1.1 CC.1.2 CC.2.1 CC.2.2).image (fun q => (CC.1, CC.2, q))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _CC ∈ 𝒞' ×ˢ 𝒞', 2 :=
            Finset.sum_le_sum fun CC _ => le_trans Finset.card_image_le (circleInterPts_card_le_two _ _ _ _)
        _ = 2 * 𝒞'.card ^ 2 := by simp [Finset.card_product, sq, mul_comm]
    -- Map (b, z) ∈ Bool × allInvs INJECTIVELY into crossTriples!
    let tWit : Fin (n + 1) × (Arc × Arc) → ℝ := fun z =>
      if h : z ∈ allInvs then (hinv_wit z h).2.2.2.choose_spec.choose_spec.choose else 0
    let qWit : Fin (n + 1) × (Arc × Arc) → EuclideanSpace ℝ (Fin 2) := fun z =>
      mkPt (tWit z) (γ_arc z.2.1 (tWit z))
    let pairsBoth := (Finset.univ : Finset Bool) ×ˢ allInvs
    let toTriple : Bool × (Fin (n + 1) × (Arc × Arc)) →
        (EuclideanSpace ℝ (Fin 2) × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ) × EuclideanSpace ℝ (Fin 2) :=
      fun bz => if bz.1 then (bz.2.2.1.1.1, bz.2.2.2.1.1, qWit bz.2)
                else (bz.2.2.2.1.1, bz.2.2.1.1.1, qWit bz.2)
    have htoT_mem : ∀ bz ∈ pairsBoth, toTriple bz ∈ crossTriples := by
      rintro ⟨b, z⟩ hbz
      have hz : z ∈ allInvs := (Finset.mem_product.mp hbz).2
      have hw := hinv_wit z hz
      have hspec := hw.2.2.2.choose_spec.choose_spec.choose_spec
      have ht_eq : tWit z = hw.2.2.2.choose_spec.choose_spec.choose := dif_pos hz
      have hC1 : z.2.1.1.1 ∈ 𝒞' := (hI_all_mem _ (hI_low_sub hw.1)).1
      have hC2 : z.2.2.1.1 ∈ 𝒞' := (hI_all_mem _ (hI_low_sub hw.2.1)).1
      have hq12 : qWit z ∈ circleInterPts z.2.1.1.1.1 z.2.1.1.1.2 z.2.2.1.1.1 z.2.2.1.1.2 := by
        simpa [qWit, ht_eq] using hspec.2.2.2.2.2.2.2.2
      cases b
      · simp only [toTriple, Bool.false_eq_true, ↓reduceIte]
        have hq21 : qWit z ∈ circleInterPts z.2.2.1.1.1 z.2.2.1.1.2 z.2.1.1.1.1 z.2.1.1.1.2 := by
          have h1d := (hγ_on z.2.1 (hI_low_sub hw.1) (tWit z) (le_of_lt (ht_eq ▸ hspec.2.2.1))
            (le_of_lt (ht_eq ▸ hspec.2.2.2.1))).1
          have h2d := (hγ_on z.2.2 (hI_low_sub hw.2.1) (tWit z) (le_of_lt (ht_eq ▸ hspec.2.2.2.2.1))
            (le_of_lt (ht_eq ▸ hspec.2.2.2.2.2.1))).1
          have hγ := ht_eq ▸ hspec.2.2.2.2.2.2.1
          rw [← hγ] at h2d
          exact mem_circleInterPts_of_dist hspec.2.2.2.2.2.2.2.1.symm h2d h1d
        exact Finset.mem_biUnion.mpr ⟨(z.2.2.1.1, z.2.1.1.1), Finset.mem_product.mpr ⟨hC2, hC1⟩,
          Finset.mem_image_of_mem _ hq21⟩
      · simp only [toTriple, ↓reduceIte]
        exact Finset.mem_biUnion.mpr ⟨(z.2.1.1.1, z.2.2.1.1), Finset.mem_product.mpr ⟨hC1, hC2⟩,
          Finset.mem_image_of_mem _ hq12⟩
    have htoT_inj : Set.InjOn toTriple pairsBoth := by
      rintro ⟨b₁, z₁⟩ h1 ⟨b₂, z₂⟩ h2 hEq
      have hz1 : z₁ ∈ allInvs := (Finset.mem_product.mp h1).2
      have hz2 : z₂ ∈ allInvs := (Finset.mem_product.mp h2).2
      have hw1 := hinv_wit z₁ hz1; have hw2 := hinv_wit z₂ hz2
      have hs1 := hw1.2.2.2.choose_spec.choose_spec.choose_spec
      have hs2 := hw2.2.2.2.choose_spec.choose_spec.choose_spec
      have ht1_eq : tWit z₁ = hw1.2.2.2.choose_spec.choose_spec.choose := dif_pos hz1
      have ht2_eq : tWit z₂ = hw2.2.2.2.choose_spec.choose_spec.choose := dif_pos hz2
      obtain ⟨h1L0, h1R0, h1a1, h1b1, h1a2, h1b2, h1γ, _, _⟩ := hs1
      obtain ⟨h2L0, h2R0, h2a1, h2b1, h2a2, h2b2, h2γ, _, _⟩ := hs2
      rw [← ht1_eq] at h1L0 h1R0 h1a1 h1b1 h1a2 h1b2 h1γ
      rw [← ht2_eq] at h2L0 h2R0 h2a1 h2b1 h2a2 h2b2 h2γ
      -- Auxiliary: same circle C and same point q = mkPt t y_q on the open arc uniquely determine the arc!
      have huniq_arc : ∀ a b : Arc, a ∈ I_low → b ∈ I_low → a.1.1 = b.1.1 →
          ∀ t_q : ℝ, x a.2.1 < t_q → t_q < x a.2.2 → x b.2.1 < t_q → t_q < x b.2.2 →
          γ_arc a t_q = γ_arc b t_q → a = b := by
        intro a b ha hb hCeq t_q ha1 ha2 hb1 hb2 hγ
        have has := (hγ_on a (hI_low_sub ha) t_q (le_of_lt ha1) (le_of_lt ha2)).2 ha1 ha2
        have hbs := (hγ_on b (hI_low_sub hb) t_q (le_of_lt hb1) (le_of_lt hb2)).2 hb1 hb2
        have hσeq : a.1.2 = b.1.2 := by
          rw [hCeq, hγ] at has
          cases hσ1 : a.1.2 <;> cases hσ2 : b.1.2 <;> simp [hσ1, hσ2] at has hbs ⊢ <;> linarith only [has, hbs]
        have hcsEq : a.1 = b.1 := Prod.ext hCeq hσeq
        by_contra hne
        have hpne : a.2 ≠ b.2 := fun hp => hne (Prod.ext hcsEq hp)
        rcases hsame_semi_disj a.1.1 a.1.2 a.2 (hI_all_mem a (hI_low_sub ha)).2 b.2
          (hcsEq ▸ (hI_all_mem b (hI_low_sub hb)).2) hpne with hle | hle
        · have : x a.2.2 ≤ x b.2.1 := hx_strict.monotone hle; linarith only [ha2, hb1, this]
        · have : x b.2.2 ≤ x a.2.1 := hx_strict.monotone hle; linarith only [hb2, ha1, this]
      have hsame_slab : tWit z₁ = tWit z₂ → z₁.1 = z₂.1 := by
        intro htEq
        have h1s := hw1.2.2.2.choose; have h2s := hw1.2.2.2.choose_spec.choose
        have h1s' := hw2.2.2.2.choose; have h2s' := hw2.2.2.2.choose_spec.choose
        by_contra hsne
        have hvalne : z₁.1.val ≠ z₂.1.val := fun h => hsne (Fin.ext h)
        rcases lt_or_gt_of_ne hvalne with hlt | hgt
        · have hle : (⟨z₁.1.val, h2s⟩ : Fin n) ≤ ⟨z₂.1.val - 1, by omega⟩ := by
            change z₁.1.val ≤ z₂.1.val - 1; omega
          linarith only [hx_strict.monotone hle, h1R0, h2L0, htEq, hε_pos]
        · have hle : (⟨z₂.1.val, h2s'⟩ : Fin n) ≤ ⟨z₁.1.val - 1, by omega⟩ := by
            change z₂.1.val ≤ z₁.1.val - 1; omega
          linarith only [hx_strict.monotone hle, h2R0, h1L0, htEq, hε_pos]
      have hmem_inv : ∀ z ∈ allInvs,
          z.2 ∈ invPairs (multiActiveEdges I_low (fun e => e.2.1) (fun e => e.2.2) z.1) (Mw.posL z.1) (Mw.posR z.1) := by
        intro ⟨s, p⟩ hsp
        rcases Finset.mem_biUnion.mp hsp with ⟨s', _, hs'⟩
        rcases Finset.mem_image.mp hs' with ⟨p', hp', hEq'⟩
        have hs'eq : s' = s := congrArg Prod.fst hEq'
        have hp'eq : p' = p := congrArg Prod.snd hEq'
        cases hs'eq; cases hp'eq; exact hp'
      have hinv1 := hmem_inv z₁ hz1
      have hinv2 := hmem_inv z₂ hz2
      rcases z₁ with ⟨s₁, ⟨e₁, e₂⟩⟩; rcases z₂ with ⟨s₂, ⟨e₁', e₂'⟩⟩
      cases b₁ <;> cases b₂ <;> simp only [toTriple, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hEq
      · obtain ⟨hC2, hC1, hqEq⟩ := hEq
        have htEq : tWit (s₁, (e₁, e₂)) = tWit (s₂, (e₁', e₂')) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hqEq
        have hyEq : γ_arc e₁ (tWit (s₁, (e₁, e₂))) = γ_arc e₁' (tWit (s₂, (e₁', e₂'))) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hqEq
        have hsEq := hsame_slab htEq
        have he1Eq := huniq_arc e₁ e₁' hw1.1 hw2.1 hC1 (tWit (s₁, (e₁, e₂)))
          h1a1 h1b1 (htEq ▸ h2a1) (htEq ▸ h2b1) (by rw [hyEq, htEq])
        have he2Eq := huniq_arc e₂ e₂' hw1.2.1 hw2.2.1 hC2 (tWit (s₁, (e₁, e₂)))
          h1a2 h1b2 (htEq ▸ h2a2) (htEq ▸ h2b2) (by rw [← h1γ, hyEq, htEq, h2γ])
        dsimp only at hsEq; subst hsEq; subst he1Eq; subst he2Eq; rfl
      · obtain ⟨hC21, hC12, hqEq⟩ := hEq
        have htEq : tWit (s₁, (e₁, e₂)) = tWit (s₂, (e₁', e₂')) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hqEq
        have hyEq : γ_arc e₁ (tWit (s₁, (e₁, e₂))) = γ_arc e₁' (tWit (s₂, (e₁', e₂'))) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hqEq
        have hsEq := hsame_slab htEq
        have he1Eq := huniq_arc e₁ e₂' hw1.1 hw2.2.1 hC12 (tWit (s₁, (e₁, e₂)))
          h1a1 h1b1 (htEq ▸ h2a2) (htEq ▸ h2b2) (by rw [hyEq, htEq, h2γ])
        have he2Eq := huniq_arc e₂ e₁' hw1.2.1 hw2.1 hC21 (tWit (s₁, (e₁, e₂)))
          h1a2 h1b2 (htEq ▸ h2a1) (htEq ▸ h2b1) (by rw [← h1γ, hyEq, htEq])
        dsimp only at hsEq; subst hsEq; subst he1Eq; subst he2Eq
        have hL1 := (Finset.mem_filter.mp hinv1).2.1
        have hL2 := (Finset.mem_filter.mp hinv2).2.1
        dsimp only at hL1 hL2
        exact False.elim (lt_asymm hL1 hL2)
      · obtain ⟨hC12, hC21, hqEq⟩ := hEq
        have htEq : tWit (s₁, (e₁, e₂)) = tWit (s₂, (e₁', e₂')) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hqEq
        have hyEq : γ_arc e₁ (tWit (s₁, (e₁, e₂))) = γ_arc e₁' (tWit (s₂, (e₁', e₂'))) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hqEq
        have hsEq := hsame_slab htEq
        have he1Eq := huniq_arc e₁ e₂' hw1.1 hw2.2.1 hC12 (tWit (s₁, (e₁, e₂)))
          h1a1 h1b1 (htEq ▸ h2a2) (htEq ▸ h2b2) (by rw [hyEq, htEq, h2γ])
        have he2Eq := huniq_arc e₂ e₁' hw1.2.1 hw2.1 hC21 (tWit (s₁, (e₁, e₂)))
          h1a2 h1b2 (htEq ▸ h2a1) (htEq ▸ h2b1) (by rw [← h1γ, hyEq, htEq])
        dsimp only at hsEq; subst hsEq; subst he1Eq; subst he2Eq
        have hL1 := (Finset.mem_filter.mp hinv1).2.1
        have hL2 := (Finset.mem_filter.mp hinv2).2.1
        dsimp only at hL1 hL2
        exact False.elim (lt_asymm hL1 hL2)
      · obtain ⟨hC1, hC2, hqEq⟩ := hEq
        have htEq : tWit (s₁, (e₁, e₂)) = tWit (s₂, (e₁', e₂')) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hqEq
        have hyEq : γ_arc e₁ (tWit (s₁, (e₁, e₂))) = γ_arc e₁' (tWit (s₂, (e₁', e₂'))) := by
          simpa [qWit] using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hqEq
        have hsEq := hsame_slab htEq
        have he1Eq := huniq_arc e₁ e₁' hw1.1 hw2.1 hC1 (tWit (s₁, (e₁, e₂)))
          h1a1 h1b1 (htEq ▸ h2a1) (htEq ▸ h2b1) (by rw [hyEq, htEq])
        have he2Eq := huniq_arc e₂ e₂' hw1.2.1 hw2.2.1 hC2 (tWit (s₁, (e₁, e₂)))
          h1a2 h1b2 (htEq ▸ h2a2) (htEq ▸ h2b2) (by rw [← h1γ, hyEq, htEq, h2γ])
        dsimp only at hsEq; subst hsEq; subst he1Eq; subst he2Eq; rfl
    have hcard_le : pairsBoth.card ≤ crossTriples.card := by
      rw [← Finset.card_image_of_injOn htoT_inj]
      exact Finset.card_le_card (fun x hx => by
        rcases Finset.mem_image.mp hx with ⟨bz, hbz, rfl⟩; exact htoT_mem bz hbz)
    have hpcard : pairsBoth.card = 2 * Mw.crossings := by
      dsimp only [pairsBoth]
      rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, hallInvs_card]
    rw [h𝒞'_card] at htriples_card
    omega
  -- Step 8: Apply Sharp Linear-in-M Multigraph Crossing Lemma to I_low and solve for t ≥ (1/10000) n^(4/5)!
  have hmult_low : ∀ a b : Fin n, (I_low.filter (fun e => e.2.1 = a ∧ e.2.2 = b)).card ≤ M := by
    intro a b
    by_cases hne : (I_low.filter (fun e => e.2.1 = a ∧ e.2.2 = b)).Nonempty
    · obtain ⟨e₀, he₀⟩ := hne
      have he₀L := (Finset.mem_filter.mp he₀).1
      have he₀ab : e₀.2 = (a, b) := Prod.ext (Finset.mem_filter.mp he₀).2.1 (Finset.mem_filter.mp he₀).2.2
      have hMle : multOf (a, b) ≤ M := he₀ab ▸ (Finset.mem_filter.mp he₀L).2
      have hsub : I_low.filter (fun e => e.2.1 = a ∧ e.2.2 = b) ⊆ I_all.filter (fun e => e.2 = (a, b)) := by
        intro e he
        obtain ⟨heL, ha, hb⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨hI_low_sub heL, Prod.ext ha hb⟩
      exact le_trans (Finset.card_le_card hsub) hMle
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.card_empty]
      exact Nat.zero_le M
  have hcl := multigraph_slabWiring_crossing_lemma Mw hn_pos hM_pos hmult_low
  have hMw_crR : (Mw.crossings : ℝ) ≤ (n : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
    have h1 : Mw.crossings ≤ (n * t) ^ 2 := le_trans hMw_cr_le (Nat.pow_le_pow_left h𝒞_card 2)
    have h2 : (Mw.crossings : ℝ) ≤ ((n : ℝ) * (t : ℝ)) ^ 2 := by exact_mod_cast h1
    rw [mul_pow] at h2
    exact h2
  exact pinned_algebra_step (by exact_mod_cast hn_pos) (by exact_mod_cast ht_pos)
    (Nat.cast_pos.mpr hM_pos) hM_hi hI_low_lb hMw_crR hcl

/-- **Székely's Global Distinct-Distance Theorem (`Ω(n^(4/5))`):**
Every finite set `P ⊂ EuclideanSpace ℝ (Fin 2)` with `|P| ≥ 2` determines at least
`(1 / 10000) * |P|^(4/5)` distinct positive distances. -/
theorem distinct_distances_ge
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hP : 2 ≤ P.card) :
    (1 / 10000 : ℝ) * (P.card : ℝ) ^ ((4 : ℝ) / 5) ≤ (distinctDistCount P : ℝ) := by
  obtain ⟨p, hpP, hp_lb⟩ := pinned_distinct_distances_ge P hP
  exact le_trans hp_lb (Nat.cast_le.mpr (pinnedDistCount_le_distinctDistCount hpP))

end UnitAndDistinctDistances

end Arith4Ext.GeometryIncidence
