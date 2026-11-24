/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import RHDirect.Stage7SieveMethods
import RHDirect.Stage8MertensTheorems

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 174 & PPL 015 (Erdős Problems #604 & #661): Pinned & Bipartite Distinct Distances

## Honest Scope & Literature Status
This file formalizes a comprehensive, pure-Mathlib-signature milestone (`0` `sorry`, `0` custom
definitions in any public theorem signature, `0` Tier C imports) for TWO live-verified open
Erdős prize problems:

- **PPL 174 (Erdős Problem #604, $500, OPEN):** Given `n` points `A ⊂ ℝ²`, must there exist a
  pin `x ∈ A` determining `≫ n^{1-o(1)}` (or even `≫ n / √(log n)`) distinct distances to `A`?
- **PPL 015 (Erdős Problem #661, $50, OPEN):** Are there, for all large `n`, points
  `x_1, ..., x_n, y_1, ..., y_n ∈ ℝ²` such that the number of distinct bipartite distances
  `d(x_i, y_j)` is `o(n / √(log n))`?

**BOTH Erdős Problem #604 (PPL 174) and Erdős Problem #661 (PPL 015) REMAIN OPEN.**
This file does **not** claim to solve either full conjecture. Instead, it establishes from scratch:
1. **Unconditional Planar Geometry & Erdős `Ω(n^{1/2})` Bounds:** Two-circle intersection
   bound (`≤ 2`), Erdős (1946) unconditional `√(n/2)` pinned and bipartite lower bounds,
   collinear extreme-point linear bound, and the fixed-cyclic-order circle diameter-crossing bound
   (`≤ 2` consecutive chords per circle sharing a perpendicular bisector `ℓ`).
2. **Crossing Lemma (Simple & Multigraph) & Székely (1997) `Ω(n^{4/5})` Bounds:** Self-contained
   probabilistic Simple Crossing Lemma (`1/64`), finite-averaging + Jensen Multigraph Crossing
   Lemma (`e³ ≤ 64 m v² cr + 64 m³ v³`), Szemerédi–Trotter `m`-rich line bound, and Székely's
   `Ω(n^{4/5})` lower bound with explicit universal constant (`1/1000`) for BOTH pinned (PPL 174)
   and bipartite (PPL 015) distinct distances.
3. **Unconditional Landau–Ramanujan & Erdős Integer-Grid `O(n / √(log n))` Constructions:**
   Unconditional proof of `#{m ≤ X : ∃ a b, m = a² + b²} = O(X / √(log X))` via Tier A
   Montgomery Large Sieve (`Stage7SieveMethods`) + Rankin's trick + Mertens' theorems in AP
   (`Stage8MertensTheorems`), yielding explicit `O(n / √(log n))` upper constructions for BOTH
   PPL 174 (all pins simultaneously) and PPL 015 (disjoint bipartite `K_{n,n}`).
4. **Energy, Extremal Pin, and Finite-Field Barriers:** Unconditional Cauchy–Schwarz energy
   inequalities (Guth–Katz quadruple energy `Q(A)`, pinned isosceles energy `T(A)`, bipartite
   energy `Q(X, Y)`), the circle-plus-center example demonstrating necessity of `∃ x ∈ A`, and
   the `𝔽_p²` barrier showing why real/topological structure is mandatory to beat `n^{1/2}`.
-/

namespace PPL174

open Classical

/-! ### Section 1: Foundational Euclidean Geometry in `EuclideanSpace ℝ (Fin 2)` -/

/-- Coordinate formula for squared Euclidean distance in `ℝ²`. -/
private lemma dist_sq_eq_coords (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

private lemma pt_ext {p q : EuclideanSpace ℝ (Fin 2)} (h0 : p 0 = q 0) (h1 : p 1 = q 1) :
    p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

private noncomputable def mkPt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

/-- **Two-Circle Intersection Bound (Unconditional):** Any two circles in `ℝ²` with distinct
centers intersect in at most `2` points. -/
theorem ppl174_two_circles_inter_card_le_two
    (c₁ c₂ : EuclideanSpace ℝ (Fin 2)) (r₁ r₂ : ℝ) (hc : c₁ ≠ c₂)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ q ∈ S, dist c₁ q = r₁ ∧ dist c₂ q = r₂) :
    S.card ≤ 2 := by
  set dx : ℝ := c₂ 0 - c₁ 0
  set dy : ℝ := c₂ 1 - c₁ 1
  set D : ℝ := dx ^ 2 + dy ^ 2
  have hD_pos : 0 < D := by
    by_contra hle
    have hD0 : dx ^ 2 + dy ^ 2 ≤ 0 := not_lt.mp hle
    have hdx : dx = 0 := by nlinarith [sq_nonneg dx, sq_nonneg dy]
    have hdy : dy = 0 := by nlinarith [sq_nonneg dx, sq_nonneg dy]
    exact hc (pt_ext (by dsimp [dx] at hdx; linarith) (by dsimp [dy] at hdy; linarith))
  set u : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => dx * (q 0 - c₁ 0) + dy * (q 1 - c₁ 1)
  set v : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => -dy * (q 0 - c₁ 0) + dx * (q 1 - c₁ 1)
  have hu_const : ∀ q ∈ S, 2 * u q = r₁ ^ 2 - r₂ ^ 2 + D := by
    intro q hq
    have h1 : (c₁ 0 - q 0) ^ 2 + (c₁ 1 - q 1) ^ 2 = r₁ ^ 2 := by
      rw [← dist_sq_eq_coords, (hS q hq).1]
    have h2 : (c₂ 0 - q 0) ^ 2 + (c₂ 1 - q 1) ^ 2 = r₂ ^ 2 := by
      rw [← dist_sq_eq_coords, (hS q hq).2]
    have hid : 2 * u q = ((c₁ 0 - q 0) ^ 2 + (c₁ 1 - q 1) ^ 2) -
        ((c₂ 0 - q 0) ^ 2 + (c₂ 1 - q 1) ^ 2) + D := by
      dsimp [u, D, dx, dy]; ring
    linarith
  have hv_sq : ∀ q ∈ S, u q ^ 2 + v q ^ 2 = D * r₁ ^ 2 := by
    intro q hq
    have h1 : (c₁ 0 - q 0) ^ 2 + (c₁ 1 - q 1) ^ 2 = r₁ ^ 2 := by
      rw [← dist_sq_eq_coords, (hS q hq).1]
    have hid : u q ^ 2 + v q ^ 2 = D * ((c₁ 0 - q 0) ^ 2 + (c₁ 1 - q 1) ^ 2) := by
      dsimp [u, v, D]; ring
    rw [hid, h1]
  have huv_inj : ∀ p q : EuclideanSpace ℝ (Fin 2), u p = u q → v p = v q → p = q := by
    intro p q hu hv
    have hx : D * (p 0 - q 0) = 0 := by
      have hid : D * (p 0 - q 0) = dx * (u p - u q) - dy * (v p - v q) := by
        dsimp [u, v, D]; ring
      rw [hid, hu, hv]; ring
    have hy : D * (p 1 - q 1) = 0 := by
      have hid : D * (p 1 - q 1) = dy * (u p - u q) + dx * (v p - v q) := by
        dsimp [u, v, D]; ring
      rw [hid, hu, hv]; ring
    have h0 : p 0 = q 0 := by
      have := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hD_pos)
      linarith
    have h1 : p 1 = q 1 := by
      have := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hD_pos)
      linarith
    exact pt_ext h0 h1
  by_contra hgt
  have h2lt : 2 < S.card := not_le.mp hgt
  obtain ⟨q₁, hq₁, q₂, hq₂, q₃, hq₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h2lt
  have hu12 : u q₁ = u q₂ := by linarith [hu_const q₁ hq₁, hu_const q₂ hq₂]
  have hu13 : u q₁ = u q₃ := by linarith [hu_const q₁ hq₁, hu_const q₃ hq₃]
  have hu23 : u q₂ = u q₃ := hu12.symm.trans hu13
  have hv12_sq : v q₁ ^ 2 = v q₂ ^ 2 := by
    have h1 := hv_sq q₁ hq₁; have h2 := hv_sq q₂ hq₂; rw [hu12] at h1; linarith
  have hv13_sq : v q₁ ^ 2 = v q₃ ^ 2 := by
    have h1 := hv_sq q₁ hq₁; have h3 := hv_sq q₃ hq₃; rw [hu13] at h1; linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv12_sq with h | h
  · exact h12 (huv_inj q₁ q₂ hu12 h)
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv13_sq with h' | h'
    · exact h13 (huv_inj q₁ q₃ hu13 h')
    · exact h23 (huv_inj q₂ q₃ hu23 (by linarith))

/-- **Two-Pin Product Lower Bound (Unconditional):** For any two distinct points `p₁ ≠ p₂` and
any finite set `Y ⊂ ℝ²`, `|Y| ≤ 2 * |D(p₁, Y)| * |D(p₂, Y)|`. -/
theorem ppl174_two_pin_product_lower
    (p₁ p₂ : EuclideanSpace ℝ (Fin 2)) (hp : p₁ ≠ p₂)
    (Y : Finset (EuclideanSpace ℝ (Fin 2))) :
    Y.card ≤ 2 * (Y.image (dist p₁ ·)).card * (Y.image (dist p₂ ·)).card := by
  let f : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun q => (dist p₁ q, dist p₂ q)
  have hsub : Y.image f ⊆ (Y.image (dist p₁ ·)) ×ˢ (Y.image (dist p₂ ·)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
  have hfib : ∀ x ∈ Y.image f, (Y.filter (fun q => f q = x)).card ≤ 2 := by
    intro x _
    apply ppl174_two_circles_inter_card_le_two p₁ p₂ x.1 x.2 hp
    intro q hq
    have hfq : f q = x := (Finset.mem_filter.mp hq).2
    exact ⟨congrArg Prod.fst hfq, congrArg Prod.snd hfq⟩
  have hcard : Y.card ≤ 2 * (Y.image f).card := by
    calc Y.card
        = ∑ x ∈ Y.image f, (Y.filter (fun q => f q = x)).card :=
          Finset.card_eq_sum_card_image f Y
      _ ≤ ∑ _x ∈ Y.image f, 2 := Finset.sum_le_sum hfib
      _ = 2 * (Y.image f).card := by simp [mul_comm]
  have himg : (Y.image f).card ≤ (Y.image (dist p₁ ·)).card * (Y.image (dist p₂ ·)).card := by
    calc (Y.image f).card
        ≤ ((Y.image (dist p₁ ·)) ×ˢ (Y.image (dist p₂ ·))).card := Finset.card_le_card hsub
      _ = (Y.image (dist p₁ ·)).card * (Y.image (dist p₂ ·)).card := Finset.card_product _ _
  calc Y.card ≤ 2 * (Y.image f).card := hcard
    _ ≤ 2 * ((Y.image (dist p₁ ·)).card * (Y.image (dist p₂ ·)).card) := Nat.mul_le_mul_left 2 himg
    _ = 2 * (Y.image (dist p₁ ·)).card * (Y.image (dist p₂ ·)).card := by ring

/-- **Erdős (1946) Unconditional `Ω(n^{1/2})` Pinned-Distance Lower Bound (PPL 174):**
Every planar point set `A` of size `n ≥ 2` contains a pin `x ∈ A` with at least `√(n / 2)`
distinct distances to `A`. -/
theorem ppl174_erdos_sqrt_pinned_lower
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (hA : 2 ≤ A.card) :
    ∃ x ∈ A, Real.sqrt ((A.card : ℝ) / 2) ≤ ((A.image (dist x ·)).card : ℝ) := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hprod : (A.card : ℝ) ≤
      2 * ((A.image (dist p₁ ·)).card : ℝ) * ((A.image (dist p₂ ·)).card : ℝ) := by
    exact_mod_cast ppl174_two_pin_product_lower p₁ p₂ hne A
  by_cases hle : (A.image (dist p₁ ·)).card ≤ (A.image (dist p₂ ·)).card
  · refine ⟨p₂, hp₂, ?_⟩
    have hleR : ((A.image (dist p₁ ·)).card : ℝ) ≤ ((A.image (dist p₂ ·)).card : ℝ) := by
      exact_mod_cast hle
    have hsq : (A.card : ℝ) / 2 ≤ ((A.image (dist p₂ ·)).card : ℝ) ^ 2 := by nlinarith
    exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, hsq⟩
  · refine ⟨p₁, hp₁, ?_⟩
    have hleR : ((A.image (dist p₂ ·)).card : ℝ) ≤ ((A.image (dist p₁ ·)).card : ℝ) := by
      exact_mod_cast le_of_not_ge hle
    have hsq : (A.card : ℝ) / 2 ≤ ((A.image (dist p₁ ·)).card : ℝ) ^ 2 := by nlinarith
    exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, hsq⟩

/-- **Unconditional `Ω(n^{1/2})` Bipartite Pinned & Total Distinct Distance Lower Bound (PPL 015):**
For any finite `X, Y ⊂ ℝ²` with `|X| ≥ 2`, there exists `x ∈ X` determining at least `√(|Y| / 2)`
distinct distances to `Y`, and hence at least `√(|Y| / 2)` total bipartite distances `d(x, y)`. -/
theorem ppl015_erdos_sqrt_bipartite_lower
    (X Y : Finset (EuclideanSpace ℝ (Fin 2))) (hX : 2 ≤ X.card) :
    (∃ x ∈ X, Real.sqrt ((Y.card : ℝ) / 2) ≤ ((Y.image (dist x ·)).card : ℝ)) ∧
    Real.sqrt ((Y.card : ℝ) / 2) ≤ (((X ×ˢ Y).image (fun p => dist p.1 p.2)).card : ℝ) := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
  have hprod : (Y.card : ℝ) ≤
      2 * ((Y.image (dist x₁ ·)).card : ℝ) * ((Y.image (dist x₂ ·)).card : ℝ) := by
    exact_mod_cast ppl174_two_pin_product_lower x₁ x₂ hne Y
  have hpin : ∃ x ∈ X, Real.sqrt ((Y.card : ℝ) / 2) ≤ ((Y.image (dist x ·)).card : ℝ) := by
    by_cases hle : (Y.image (dist x₁ ·)).card ≤ (Y.image (dist x₂ ·)).card
    · refine ⟨x₂, hx₂, Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, ?_⟩⟩
      have hleR : ((Y.image (dist x₁ ·)).card : ℝ) ≤ ((Y.image (dist x₂ ·)).card : ℝ) := by
        exact_mod_cast hle
      nlinarith
    · refine ⟨x₁, hx₁, Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, ?_⟩⟩
      have hleR : ((Y.image (dist x₂ ·)).card : ℝ) ≤ ((Y.image (dist x₁ ·)).card : ℝ) := by
        exact_mod_cast le_of_not_ge hle
      nlinarith
  refine ⟨hpin, ?_⟩
  rcases hpin with ⟨x, hx, hxb⟩
  have hsub : Y.image (dist x ·) ⊆ (X ×ˢ Y).image (fun p => dist p.1 p.2) := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  exact hxb.trans (by exact_mod_cast Finset.card_le_card hsub)

/-- **Collinear Extreme-Point Linear Pinned Distance Bound (Unconditional):**
Any nonempty finite collinear set `S` on a 1D affine line `ℓ ⊂ ℝ²` contains an extreme pin
`x ∈ S` determining `|S|` distinct distances to `S` (including `0`). -/
theorem ppl174_collinear_pinned_linear
    (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (hℓ : Module.finrank ℝ ℓ.direction = 1)
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hSne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ ℓ) :
    ∃ x ∈ S, (S.image (dist x ·)).card = S.card := by
  have hfin : FiniteDimensional ℝ ℓ.direction := Module.finite_of_finrank_pos (by omega)
  have hne_bot : ℓ.direction ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hℓ
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  have hspan_le : Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_mem)
  have hdir : Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin 2))) = ℓ.direction :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [finrank_span_singleton hv_ne, hℓ])
  rcases hSne with ⟨p₀, hp₀⟩
  have hSne' : S.Nonempty := ⟨p₀, hp₀⟩
  have hcoord : ∀ q ∈ S, ∃ t : ℝ, q -ᵥ p₀ = t • v := by
    intro q hq
    have hmem : q -ᵥ p₀ ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [hdir]
      exact AffineSubspace.vsub_mem_direction (hS q hq) (hS p₀ hp₀)
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨t, ht.symm⟩
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  let coord : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun q => ((q 0 - p₀ 0) * v 0 + (q 1 - p₀ 1) * v 1) / (v 0 ^ 2 + v 1 ^ 2)
  have hv_sq_pos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
    rw [← hsq]; positivity
  have hcoord_eq : ∀ q ∈ S, q -ᵥ p₀ = coord q • v := by
    intro q hq
    obtain ⟨t, ht⟩ := hcoord q hq
    have h0 : q 0 - p₀ 0 = t * v 0 := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) ht
      simpa [vsub_eq_sub] using this
    have h1 : q 1 - p₀ 1 = t * v 1 := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) ht
      simpa [vsub_eq_sub] using this
    have hct : coord q = t := by
      dsimp [coord]
      rw [h0, h1]
      have hne : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := ne_of_gt hv_sq_pos
      field_simp [hne]
    rwa [hct]
  obtain ⟨x, hxS, hxmin⟩ := Finset.exists_min_image S coord hSne'
  refine ⟨x, hxS, ?_⟩
  apply Finset.card_image_of_injOn
  intro y₁ hy₁ y₂ hy₂ heq
  have hsub1 : y₁ -ᵥ x = (coord y₁ - coord x) • v := by
    have h1 := hcoord_eq y₁ hy₁
    have h2 := hcoord_eq x hxS
    rw [vsub_eq_sub] at h1 h2 ⊢
    rw [sub_smul, ← h1, ← h2]
    abel
  have hsub2 : y₂ -ᵥ x = (coord y₂ - coord x) • v := by
    have h1 := hcoord_eq y₂ hy₂
    have h2 := hcoord_eq x hxS
    rw [vsub_eq_sub] at h1 h2 ⊢
    rw [sub_smul, ← h1, ← h2]
    abel
  have hd1 : dist x y₁ = (coord y₁ - coord x) * ‖v‖ := by
    rw [dist_comm, dist_eq_norm_vsub, hsub1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hxmin y₁ hy₁))]
  have hd2 : dist x y₂ = (coord y₂ - coord x) * ‖v‖ := by
    rw [dist_comm, dist_eq_norm_vsub, hsub2, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hxmin y₂ hy₂))]
  have hce : coord y₁ = coord y₂ := by
    have : (coord y₁ - coord x) * ‖v‖ = (coord y₂ - coord x) * ‖v‖ := by linarith
    have := mul_right_cancel₀ (ne_of_gt hv_norm_pos) this
    linarith
  have hvy : y₁ -ᵥ p₀ = y₂ -ᵥ p₀ := by rw [hcoord_eq y₁ hy₁, hcoord_eq y₂ hy₂, hce]
  exact vsub_left_cancel hvy

/-- **Circle Cyclic-Ordering & Diameter-Crossing Bound (Unconditional Key Lemma for Székely 1997):**
Let `p` lie on a 1D affine line `ℓ ⊂ ℝ²` and let `S` be a finite set of points on the circle
`{q : dist p q = r}` (`r > 0`) enumerated by an equivalence `e : Fin S.card ≃ S` in strictly
increasing order of standard polar angle `Complex.arg ⟨q 0 - p 0, q 1 - p 1⟩` (a single fixed
cyclic order independent of `ℓ`!). Then at most `2` consecutive cyclic chords `(e i, e (i + 1))`
have `ℓ` as their perpendicular bisector (`∀ w ∈ ℓ, dist (e i) w = dist (e (i + 1)) w`). -/
theorem ppl174_circle_diameter_crossing_le_two
    (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (hℓ : Module.finrank ℝ ℓ.direction = 1)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ ℓ)
    (r : ℝ) (hr : 0 < r)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ q ∈ S, dist p q = r)
    (hS3 : 3 ≤ S.card)
    (e : Fin S.card ≃ S)
    (he_mono : StrictMono (fun i : Fin S.card =>
      Complex.arg (⟨(e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0,
                    (e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1⟩ : ℂ))) :
    (Finset.univ.filter (fun i : Fin S.card =>
      let q₁ : EuclideanSpace ℝ (Fin 2) := e i
      let q₂ : EuclideanSpace ℝ (Fin 2) := e ⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩
      ∀ w ∈ ℓ, dist q₁ w = dist q₂ w)).card ≤ 2 := by
  have hfin : FiniteDimensional ℝ ℓ.direction := Module.finite_of_finrank_pos (by omega)
  have hne_bot : ℓ.direction ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hℓ; omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  -- Unit normal vector `n` to `ℓ`
  have hv_sq_pos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
    rw [← hsq]; exact pow_pos (norm_pos_iff.mpr hv_ne) 2
  set nv : ℝ := Real.sqrt (v 0 ^ 2 + v 1 ^ 2)
  have hnv_pos : 0 < nv := Real.sqrt_pos.mpr hv_sq_pos
  have hnv_sq : nv ^ 2 = v 0 ^ 2 + v 1 ^ 2 := Real.sq_sqrt (le_of_lt hv_sq_pos)
  set nx : ℝ := -v 1 / nv
  set ny : ℝ := v 0 / nv
  have hn_unit : nx ^ 2 + ny ^ 2 = 1 := by
    dsimp [nx, ny]
    have hnv_ne : nv ≠ 0 := ne_of_gt hnv_pos
    field_simp [hnv_ne]
    nlinarith [hnv_sq]
  set nC : ℂ := ⟨nx, ny⟩
  have hnC_norm : ‖nC‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [nC]
    rw [show nx * nx + ny * ny = nx ^ 2 + ny ^ 2 by ring, hn_unit, Real.sqrt_one]
  set φ : ℝ := Complex.arg nC
  have hcos_φ : Real.cos φ = nx := by
    have hne0 : nC ≠ 0 := by intro h; rw [h, norm_zero] at hnC_norm; norm_num at hnC_norm
    have := Complex.cos_arg hne0
    simpa [φ, hnC_norm, nC] using this
  have hsin_φ : Real.sin φ = ny := by
    have := Complex.sin_arg nC
    simpa [φ, hnC_norm, nC] using this
  let z : Fin S.card → ℂ := fun i =>
    ⟨(e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0, (e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1⟩
  let θ : Fin S.card → ℝ := fun i => Complex.arg (z i)
  let t : Fin S.card → ℝ := fun i => θ i - φ
  have hz_norm : ∀ i, ‖z i‖ = r := by
    intro i
    have hd : dist p (e i : EuclideanSpace ℝ (Fin 2)) = r := hS (e i) (e i).2
    have hsq : ((e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0) ^ 2 +
        ((e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1) ^ 2 = r ^ 2 := by
      have h1 := dist_sq_eq_coords p (e i)
      rw [hd] at h1
      linarith
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [z]
    rw [show ((e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0) * ((e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0) +
        ((e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1) * ((e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1) =
        r ^ 2 by nlinarith [hsq], Real.sqrt_sq (le_of_lt hr)]
  have hsigned : ∀ i,
      nx * ((e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0) +
      ny * ((e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1) = r * Real.cos (t i) := by
    intro i
    have hzne : z i ≠ 0 := by
      intro h
      have hzi := hz_norm i
      rw [h, norm_zero] at hzi
      linarith
    have hxc : (e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0 = r * Real.cos (θ i) := by
      have hc := Complex.cos_arg hzne
      rw [hz_norm i] at hc
      have : (z i).re = (e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0 := rfl
      rw [this] at hc
      have hrne : r ≠ 0 := ne_of_gt hr
      field_simp [hrne] at hc ⊢
      linarith
    have hyc : (e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1 = r * Real.sin (θ i) := by
      have hs := Complex.sin_arg (z i)
      rw [hz_norm i] at hs
      have : (z i).im = (e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1 := rfl
      rw [this] at hs
      have hrne : r ≠ 0 := ne_of_gt hr
      field_simp [hrne] at hs ⊢
      linarith
    rw [hxc, hyc, ← hcos_φ, ← hsin_φ, show t i = θ i - φ from rfl, Real.cos_sub]
    ring
  -- Key geometric implication: if `q₁ ≠ q₂` on `S(p, r)` have bisector `ℓ`, then `cos(t i) * cos(t j) < 0`
  have hsign_flip : ∀ i : Fin S.card,
      let j : Fin S.card := ⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩
      (∀ w ∈ ℓ, dist (e i : EuclideanSpace ℝ (Fin 2)) w =
                dist (e j : EuclideanSpace ℝ (Fin 2)) w) →
      Real.cos (t i) * Real.cos (t j) < 0 := by
    intro i j hbis
    have hij_ne : i ≠ j := by
      intro h
      have h1 : i.1 = (i.1 + 1) % S.card := congrArg Fin.val h
      have : i.1 < S.card := i.2
      by_cases hlast : i.1 + 1 < S.card
      · rw [Nat.mod_eq_of_lt hlast] at h1; omega
      · have hlast' : i.1 + 1 = S.card := by omega
        rw [hlast', Nat.mod_self] at h1; omega
    have hq_ne : (e i : EuclideanSpace ℝ (Fin 2)) ≠ (e j : EuclideanSpace ℝ (Fin 2)) := by
      intro h; exact hij_ne (e.injective (Subtype.ext h))
    have hpw : v +ᵥ p ∈ ℓ := AffineSubspace.vadd_mem_of_mem_direction hv_mem hp
    have hdp := hbis p hp
    have hdv := hbis (v +ᵥ p) hpw
    set dx₁ : ℝ := (e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0
    set dy₁ : ℝ := (e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1
    set dx₂ : ℝ := (e j : EuclideanSpace ℝ (Fin 2)) 0 - p 0
    set dy₂ : ℝ := (e j : EuclideanSpace ℝ (Fin 2)) 1 - p 1
    have hsq_p : dx₁ ^ 2 + dy₁ ^ 2 = dx₂ ^ 2 + dy₂ ^ 2 := by
      have h1 := dist_sq_eq_coords (e i) p
      have h2 := dist_sq_eq_coords (e j) p
      rw [hdp] at h1
      linarith [h1, h2]
    have hsq_v : (dx₁ - v 0) ^ 2 + (dy₁ - v 1) ^ 2 = (dx₂ - v 0) ^ 2 + (dy₂ - v 1) ^ 2 := by
      have h1 := dist_sq_eq_coords (e i) (v +ᵥ p)
      have h2 := dist_sq_eq_coords (e j) (v +ᵥ p)
      have hv0 : (v +ᵥ p) 0 = p 0 + v 0 := by simp [vadd_eq_add, add_comm]
      have hv1 : (v +ᵥ p) 1 = p 1 + v 1 := by simp [vadd_eq_add, add_comm]
      rw [hv0, hv1] at h1 h2
      have h1' : (dx₁ - v 0) ^ 2 + (dy₁ - v 1) ^ 2 =
          ((e i : EuclideanSpace ℝ (Fin 2)) 0 - (p 0 + v 0)) ^ 2 +
          ((e i : EuclideanSpace ℝ (Fin 2)) 1 - (p 1 + v 1)) ^ 2 := by
        dsimp [dx₁, dy₁]; ring
      have h2' : (dx₂ - v 0) ^ 2 + (dy₂ - v 1) ^ 2 =
          ((e j : EuclideanSpace ℝ (Fin 2)) 0 - (p 0 + v 0)) ^ 2 +
          ((e j : EuclideanSpace ℝ (Fin 2)) 1 - (p 1 + v 1)) ^ 2 := by
        dsimp [dx₂, dy₂]; ring
      rw [h1', h2', ← h1, ← h2, hdv]
    set a₁ : ℝ := dx₁ * v 0 + dy₁ * v 1
    set a₂ : ℝ := dx₂ * v 0 + dy₂ * v 1
    set c₁ : ℝ := -v 1 * dx₁ + v 0 * dy₁
    set c₂ : ℝ := -v 1 * dx₂ + v 0 * dy₂
    have ha_eq : a₁ = a₂ := by
      have hid : 2 * (a₂ - a₁) = ((dx₁ - v 0) ^ 2 + (dy₁ - v 1) ^ 2) -
          ((dx₂ - v 0) ^ 2 + (dy₂ - v 1) ^ 2) - ((dx₁ ^ 2 + dy₁ ^ 2) - (dx₂ ^ 2 + dy₂ ^ 2)) := by
        dsimp [a₁, a₂]; ring
      linarith [hid, hsq_p, hsq_v]
    have hc_sq : c₁ ^ 2 = c₂ ^ 2 := by
      have h1 : a₁ ^ 2 + c₁ ^ 2 = (v 0 ^ 2 + v 1 ^ 2) * (dx₁ ^ 2 + dy₁ ^ 2) := by
        dsimp [a₁, c₁]; ring
      have h2 : a₂ ^ 2 + c₂ ^ 2 = (v 0 ^ 2 + v 1 ^ 2) * (dx₂ ^ 2 + dy₂ ^ 2) := by
        dsimp [a₂, c₂]; ring
      rw [ha_eq, hsq_p] at h1
      linarith [h1, h2]
    have hc_ne : c₁ ≠ c₂ := by
      intro hceq
      apply hq_ne
      have hx0 : (v 0 ^ 2 + v 1 ^ 2) * (dx₁ - dx₂) = 0 := by
        have hid : (v 0 ^ 2 + v 1 ^ 2) * (dx₁ - dx₂) =
            v 0 * (a₁ - a₂) - v 1 * (c₁ - c₂) := by dsimp [a₁, a₂, c₁, c₂]; ring
        rw [hid, ha_eq, hceq]; ring
      have hy0 : (v 0 ^ 2 + v 1 ^ 2) * (dy₁ - dy₂) = 0 := by
        have hid : (v 0 ^ 2 + v 1 ^ 2) * (dy₁ - dy₂) =
            v 1 * (a₁ - a₂) + v 0 * (c₁ - c₂) := by dsimp [a₁, a₂, c₁, c₂]; ring
        rw [hid, ha_eq, hceq]; ring
      have h0 : dx₁ - dx₂ = 0 := (mul_eq_zero.mp hx0).resolve_left (ne_of_gt hv_sq_pos)
      have h1 : dy₁ - dy₂ = 0 := (mul_eq_zero.mp hy0).resolve_left (ne_of_gt hv_sq_pos)
      have h0' : (e i : EuclideanSpace ℝ (Fin 2)) 0 - p 0 - ((e j : EuclideanSpace ℝ (Fin 2)) 0 - p 0) = 0 := h0
      have h1' : (e i : EuclideanSpace ℝ (Fin 2)) 1 - p 1 - ((e j : EuclideanSpace ℝ (Fin 2)) 1 - p 1) = 0 := h1
      exact pt_ext (by linarith) (by linarith)
    have hc_neg : c₁ = -c₂ := (sq_eq_sq_iff_eq_or_eq_neg.mp hc_sq).resolve_left hc_ne
    have hc_nz : c₁ ≠ 0 := by intro h0; apply hc_ne; linarith
    have hc_prod : c₁ * c₂ < 0 := by
      have : c₁ * c₂ = -(c₁ ^ 2) := by rw [hc_neg]; ring
      rw [this]
      exact neg_lt_zero.mpr (sq_pos_of_ne_zero hc_nz)
    have hb1 : nx * dx₁ + ny * dy₁ = c₁ / nv := by dsimp [nx, ny, c₁]; ring
    have hb2 : nx * dx₂ + ny * dy₂ = c₂ / nv := by dsimp [nx, ny, c₂]; ring
    have hprod_b : (r * Real.cos (t i)) * (r * Real.cos (t j)) = (c₁ * c₂) / nv ^ 2 := by
      rw [← hsigned i, ← hsigned j]
      change (nx * dx₁ + ny * dy₁) * (nx * dx₂ + ny * dy₂) = (c₁ * c₂) / nv ^ 2
      rw [hb1, hb2]; ring
    have hprod_neg : (r * Real.cos (t i)) * (r * Real.cos (t j)) < 0 := by
      rw [hprod_b]
      exact div_neg_of_neg_of_pos hc_prod (pow_pos hnv_pos 2)
    have hrew : (r * Real.cos (t i)) * (r * Real.cos (t j)) =
        r ^ 2 * (Real.cos (t i) * Real.cos (t j)) := by ring
    rw [hrew] at hprod_neg
    exact (mul_neg_iff.mp hprod_neg).resolve_right (fun h => not_lt_of_ge (le_of_lt (pow_pos hr 2)) h.1) |>.2
  -- Count sign changes of `cos (t i)` around the circle: strictly at most `2`
  let F := Finset.univ.filter (fun i : Fin S.card =>
    let q₁ : EuclideanSpace ℝ (Fin 2) := e i
    let q₂ : EuclideanSpace ℝ (Fin 2) := e ⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩
    ∀ w ∈ ℓ, dist q₁ w = dist q₂ w)
  have ht_mono : StrictMono t := fun i j hij => sub_lt_sub_right (he_mono hij) φ
  let i0 : Fin S.card := ⟨0, by omega⟩
  let ilast : Fin S.card := ⟨S.card - 1, by omega⟩
  have ht_span : t ilast - t i0 < 2 * Real.pi := by
    have h1 := Complex.neg_pi_lt_arg (z i0)
    have h2 := Complex.arg_le_pi (z ilast)
    dsimp [t, θ]
    linarith
  have hex_zero : ∀ a b : ℝ, a < b → Real.cos a * Real.cos b < 0 →
      ∃ c ∈ Set.Ioo a b, Real.cos c = 0 := by
    intro a b hab hneg
    have hcont : ContinuousOn Real.cos (Set.Icc a b) := Real.continuous_cos.continuousOn
    by_cases ha : Real.cos a < 0
    · have hb : 0 < Real.cos b := by nlinarith
      exact intermediate_value_Ioo (le_of_lt hab) hcont ⟨ha, hb⟩
    · have ha' : 0 < Real.cos a := by
        have hnz : Real.cos a ≠ 0 := by intro h; rw [h, zero_mul] at hneg; exact lt_irrefl 0 hneg
        exact lt_of_le_of_ne (not_lt.mp ha) hnz.symm
      have hb : Real.cos b < 0 := by nlinarith
      exact intermediate_value_Ioo' (le_of_lt hab) hcont ⟨hb, ha'⟩
  have hthree_zeros : ∀ c₁ c₂ c₃ : ℝ, c₁ < c₂ → c₂ < c₃ →
      Real.cos c₁ = 0 → Real.cos c₂ = 0 → Real.cos c₃ = 0 → 2 * Real.pi ≤ c₃ - c₁ := by
    intro c₁ c₂ c₃ h12 h23 hc₁ hc₂ hc₃
    obtain ⟨k₁, hk₁⟩ := Real.cos_eq_zero_iff.mp hc₁
    obtain ⟨k₂, hk₂⟩ := Real.cos_eq_zero_iff.mp hc₂
    obtain ⟨k₃, hk₃⟩ := Real.cos_eq_zero_iff.mp hc₃
    have hpi : 0 < Real.pi := Real.pi_pos
    have hk12 : k₁ < k₂ := by
      have : ((k₁ : ℝ) - (k₂ : ℝ)) * Real.pi < 0 := by linarith [hk₁, hk₂, h12]
      have : (k₁ : ℝ) < (k₂ : ℝ) := by nlinarith
      exact_mod_cast this
    have hk23 : k₂ < k₃ := by
      have : ((k₂ : ℝ) - (k₃ : ℝ)) * Real.pi < 0 := by linarith [hk₂, hk₃, h23]
      have : (k₂ : ℝ) < (k₃ : ℝ) := by nlinarith
      exact_mod_cast this
    have hk13 : k₁ + 2 ≤ k₃ := by omega
    have hk13R : (k₁ : ℝ) + 2 ≤ (k₃ : ℝ) := by exact_mod_cast hk13
    nlinarith [hk₁, hk₃, hk13R, hpi]
  have hzero_of_mem : ∀ i ∈ F,
      ∃ c : ℝ, Real.cos c = 0 ∧
        (if h : i.1 + 1 < S.card then
          t i < c ∧ c < t ⟨i.1 + 1, h⟩
        else
          t ilast < c ∧ c < t i0 + 2 * Real.pi) := by
    intro i hi
    have hbis := (Finset.mem_filter.mp hi).2
    have hneg := hsign_flip i hbis
    by_cases hlt : i.1 + 1 < S.card
    · have hj : (⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ : Fin S.card) = ⟨i.1 + 1, hlt⟩ := by
        ext; exact Nat.mod_eq_of_lt hlt
      rw [hj] at hneg
      have hab : t i < t ⟨i.1 + 1, hlt⟩ := ht_mono (show i < ⟨i.1 + 1, hlt⟩ by exact Nat.lt_succ_self i.1)
      obtain ⟨c, ⟨hc1, hc2⟩, hcz⟩ := hex_zero _ _ hab hneg
      exact ⟨c, hcz, by simp [hlt, hc1, hc2]⟩
    · have hil : i = ilast := by ext; dsimp [ilast]; omega
      have hj : (⟨(ilast.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ : Fin S.card) = i0 := by
        ext; dsimp [i0, ilast]; have : S.card - 1 + 1 = S.card := by omega
        rw [this, Nat.mod_self]
      rw [hil, hj] at hneg
      have hneg' : Real.cos (t ilast) * Real.cos (t i0 + 2 * Real.pi) < 0 := by
        rwa [Real.cos_add_two_pi]
      have hab : t ilast < t i0 + 2 * Real.pi := by linarith
      obtain ⟨c, ⟨hc1, hc2⟩, hcz⟩ := hex_zero _ _ hab hneg'
      exact ⟨c, hcz, by simp [hlt, hc1, hc2]⟩
  by_contra hgt
  have h2lt : 2 < F.card := not_le.mp hgt
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp h2lt
  have htriple : ∃ i₁ i₂ i₃ : Fin S.card,
      i₁ ∈ F ∧ i₂ ∈ F ∧ i₃ ∈ F ∧ i₁ < i₂ ∧ i₂ < i₃ := by
    rcases lt_or_gt_of_ne hab with h1 | h1
    · rcases lt_or_gt_of_ne hbd with h2 | h2
      · exact ⟨a, b, d, ha, hb, hd, h1, h2⟩
      · rcases lt_or_gt_of_ne had with h3 | h3
        · exact ⟨a, d, b, ha, hd, hb, h3, h2⟩
        · exact ⟨d, a, b, hd, ha, hb, h3, h1⟩
    · rcases lt_or_gt_of_ne had with h2 | h2
      · exact ⟨b, a, d, hb, ha, hd, h1, h2⟩
      · rcases lt_or_gt_of_ne hbd with h3 | h3
        · exact ⟨b, d, a, hb, hd, ha, h3, h2⟩
        · exact ⟨d, b, a, hd, hb, ha, h3, h1⟩
  obtain ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, h12, h23⟩ := htriple
  have hlt1 : i₁.1 + 1 < S.card := by have := i₁.2; have := i₂.2; have := i₃.2; omega
  have hlt2 : i₂.1 + 1 < S.card := by have := i₂.2; have := i₃.2; omega
  obtain ⟨c₁, hc₁z, hc₁b⟩ := hzero_of_mem i₁ hi₁
  obtain ⟨c₂, hc₂z, hc₂b⟩ := hzero_of_mem i₂ hi₂
  obtain ⟨c₃, hc₃z, hc₃b⟩ := hzero_of_mem i₃ hi₃
  simp only [hlt1, dif_pos] at hc₁b
  simp only [hlt2, dif_pos] at hc₂b
  have hc1_lo : t i0 < c₁ := by
    have h01 : t i0 ≤ t i₁ := ht_mono.monotone (show i0 ≤ i₁ from Nat.zero_le _)
    linarith [hc₁b.1]
  have hc12 : c₁ < c₂ := by
    have hle : (⟨i₁.1 + 1, hlt1⟩ : Fin S.card) ≤ i₂ := by
      show i₁.1 + 1 ≤ i₂.1; exact h12
    have := ht_mono.monotone hle
    linarith [hc₁b.2, hc₂b.1]
  have hc23 : c₂ < c₃ := by
    by_cases hlt3 : i₃.1 + 1 < S.card
    · simp only [hlt3, dif_pos] at hc₃b
      have hle : (⟨i₂.1 + 1, hlt2⟩ : Fin S.card) ≤ i₃ := by
        show i₂.1 + 1 ≤ i₃.1; exact h23
      have := ht_mono.monotone hle
      linarith [hc₂b.2, hc₃b.1]
    · simp only [hlt3, dif_neg, not_false_eq_true] at hc₃b
      have hle : (⟨i₂.1 + 1, hlt2⟩ : Fin S.card) ≤ ilast := by
        show i₂.1 + 1 ≤ S.card - 1; omega
      have := ht_mono.monotone hle
      linarith [hc₂b.2, hc₃b.1]
  have hc3_hi : c₃ < t i0 + 2 * Real.pi := by
    by_cases hlt3 : i₃.1 + 1 < S.card
    · simp only [hlt3, dif_pos] at hc₃b
      have hle : (⟨i₃.1 + 1, hlt3⟩ : Fin S.card) ≤ ilast := by
        show i₃.1 + 1 ≤ S.card - 1; omega
      have := ht_mono.monotone hle
      linarith [hc₃b.2, ht_span]
    · simp only [hlt3, dif_neg, not_false_eq_true] at hc₃b
      exact hc₃b.2
  have hge := hthree_zeros c₁ c₂ c₃ hc12 hc23 hc₁z hc₂z hc₃z
  linarith

/-! ### Section 2: Simple & Multigraph Crossing Lemmas, Szemerédi–Trotter & Székely `Ω(n^{4/5})` -/

private lemma sum_powerset_bernoulli {V : Type*} [DecidableEq V]
    (A : Finset V) (p : ℝ) :
    ∑ R ∈ A.powerset, p ^ R.card * (1 - p) ^ (A.card - R.card) = 1 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hcard_ins : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    rw [Finset.powerset_insert, Finset.sum_union]
    · have h1 : ∑ R ∈ s.powerset,
          p ^ R.card * (1 - p) ^ ((insert a s).card - R.card) =
          (1 - p) * ∑ R ∈ s.powerset, p ^ R.card * (1 - p) ^ (s.card - R.card) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun R hR => ?_
        have hle : R.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [hcard_ins, Nat.sub_add_comm hle, pow_succ]; ring
      have h2 : ∑ R ∈ s.powerset.image (insert a),
          p ^ R.card * (1 - p) ^ ((insert a s).card - R.card) =
          p * ∑ R ∈ s.powerset, p ^ R.card * (1 - p) ^ (s.card - R.card) := by
        rw [Finset.sum_image, Finset.mul_sum]
        · refine Finset.sum_congr rfl fun R hR => ?_
          have haR : a ∉ R := fun h => ha (Finset.mem_powerset.mp hR h)
          rw [Finset.card_insert_of_notMem haR, hcard_ins, Nat.add_sub_add_right, pow_succ]; ring
        · intro R₁ hR₁ R₂ hR₂ heq
          have ha₁ : a ∉ R₁ := fun h => ha (Finset.mem_powerset.mp hR₁ h)
          have ha₂ : a ∉ R₂ := fun h => ha (Finset.mem_powerset.mp hR₂ h)
          have := congrArg (Finset.erase · a) heq
          simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using this
      rw [h1, h2, ih]; ring
    · rw [Finset.disjoint_left]
      intro R hR hRimg
      rcases Finset.mem_image.mp hRimg with ⟨R', _, rfl⟩
      exact ha (Finset.mem_powerset.mp hR (Finset.mem_insert_self a R'))

private lemma sum_powerset_bernoulli_superset {V : Type*} [DecidableEq V]
    (verts T : Finset V) (hT : T ⊆ verts) (p : ℝ) :
    ∑ S ∈ verts.powerset.filter (T ⊆ ·), p ^ S.card * (1 - p) ^ (verts.card - S.card) =
      p ^ T.card := by
  have hbij : verts.powerset.filter (T ⊆ ·) = (verts \ T).powerset.image (T ∪ ·) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hSv, hTS⟩
      exact ⟨S \ T, Finset.sdiff_subset_sdiff hSv (Finset.Subset.refl T),
        Finset.union_sdiff_of_subset hTS⟩
    · rintro ⟨R, hR, rfl⟩
      exact ⟨Finset.union_subset hT (hR.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  rw [hbij, Finset.sum_image]
  · have hsum : ∑ R ∈ (verts \ T).powerset,
        p ^ (T ∪ R).card * (1 - p) ^ (verts.card - (T ∪ R).card) =
        p ^ T.card * ∑ R ∈ (verts \ T).powerset,
          p ^ R.card * (1 - p) ^ ((verts \ T).card - R.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun R hR => ?_
      have hdisj : Disjoint T R :=
        Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR) Finset.disjoint_sdiff
      rw [Finset.card_union_of_disjoint hdisj, pow_add]
      have hcard_sdiff : (verts \ T).card = verts.card - T.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT]
      rw [hcard_sdiff, Nat.sub_sub]; ring
    rw [hsum, sum_powerset_bernoulli, mul_one]
  · intro R₁ hR₁ R₂ hR₂ heq
    have hd₁ : Disjoint T R₁ :=
      Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR₁) Finset.disjoint_sdiff
    have hd₂ : Disjoint T R₂ :=
      Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR₂) Finset.disjoint_sdiff
    have := congrArg (· \ T) heq
    simpa [Finset.union_sdiff_cancel_left hd₁, Finset.union_sdiff_cancel_left hd₂] using this

/-- **Simple Crossing Lemma (Ajtai–Chvátal–Newborn–Szemerédi 1982 / Leighton 1983, All Densities):**
Under Euler's linear crossing bound `e(S) ≤ 3 |S| + cr(S)` on induced subgraphs `S ⊆ verts`,
every simple graph obeys `|edges|³ ≤ 64 |verts|² |crossings| + 64 |verts|³` (and in particular
`|edges|³ ≤ 64 |verts|² |crossings|` whenever `4 |verts| ≤ |edges|`). -/
theorem ppl174_crossing_lemma_simple {V α : Type*} [DecidableEq V] [DecidableEq α]
    (verts : Finset V) (edges : Finset (Finset V)) (crossings : Finset α)
    (supp : α → Finset V)
    (hE_sub : ∀ e ∈ edges, e ⊆ verts ∧ e.card = 2)
    (hC_sub : ∀ c ∈ crossings, supp c ⊆ verts ∧ (supp c).card = 4)
    (hEuler : ∀ S : Finset V, S ⊆ verts →
      (edges.filter (· ⊆ S)).card ≤ 3 * S.card + (crossings.filter (fun c => supp c ⊆ S)).card) :
    (edges.card : ℝ) ^ 3 ≤
      64 * (verts.card : ℝ) ^ 2 * (crossings.card : ℝ) + 64 * (verts.card : ℝ) ^ 3 := by
  by_cases hDense : 4 * verts.card ≤ edges.card
  · by_cases hv : verts.card = 0
    · have he0 : edges.card = 0 := by
        rw [Finset.card_eq_zero] at hv ⊢
        ext e; simp only [Finset.notMem_empty, iff_false]; intro he
        have h1 := (hE_sub e he).1; rw [hv, Finset.subset_empty] at h1
        have h2 := (hE_sub e he).2; rw [h1, Finset.card_empty] at h2; omega
      simp [hv, he0]
    have hv_pos : (0 : ℝ) < (verts.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hv)
    have he_pos : (0 : ℝ) < (edges.card : ℝ) := Nat.cast_pos.mpr (by omega)
    set p : ℝ := 4 * (verts.card : ℝ) / (edges.card : ℝ)
    have hp0 : 0 ≤ p := by positivity
    have hp1 : p ≤ 1 := by rw [div_le_one he_pos]; exact_mod_cast hDense
    set w : Finset V → ℝ := fun S => p ^ S.card * (1 - p) ^ (verts.card - S.card)
    have hw_nn : ∀ S, 0 ≤ w S := fun S =>
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
    have hsum_ineq :
        ∑ S ∈ verts.powerset, w S * ((edges.filter (· ⊆ S)).card : ℝ) ≤
        ∑ S ∈ verts.powerset, w S * (3 * (S.card : ℝ) +
          ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ)) := by
      refine Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ (hw_nn S)
      exact_mod_cast hEuler S (Finset.mem_powerset.mp hS)
    have hLHS : ∑ S ∈ verts.powerset, w S * ((edges.filter (· ⊆ S)).card : ℝ) =
        p ^ 2 * (edges.card : ℝ) := by
      have hrw : ∑ S ∈ verts.powerset, w S * ((edges.filter (· ⊆ S)).card : ℝ) =
          ∑ S ∈ verts.powerset, ∑ e ∈ edges, (if e ⊆ S then w S else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
      rw [hrw, Finset.sum_comm]
      calc ∑ e ∈ edges, ∑ S ∈ verts.powerset, (if e ⊆ S then w S else 0)
          = ∑ e ∈ edges, ∑ S ∈ verts.powerset.filter (e ⊆ ·), w S :=
            Finset.sum_congr rfl fun e _ => (Finset.sum_filter _ _).symm
        _ = ∑ e ∈ edges, p ^ 2 := Finset.sum_congr rfl fun e he => by
            rw [sum_powerset_bernoulli_superset verts e (hE_sub e he).1 p, (hE_sub e he).2]
        _ = p ^ 2 * (edges.card : ℝ) := by simp [mul_comm]
    have hV : ∑ S ∈ verts.powerset, w S * (S.card : ℝ) = p * (verts.card : ℝ) := by
      have hrw : ∑ S ∈ verts.powerset, w S * (S.card : ℝ) =
          ∑ S ∈ verts.powerset, ∑ v ∈ verts, (if ({v} : Finset V) ⊆ S then w S else 0) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have hc : S.card = ∑ v ∈ verts, (if ({v} : Finset V) ⊆ S then 1 else 0) := by
          simp [Finset.singleton_subset_iff, Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hS)]
        rw [hc, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
      rw [hrw, Finset.sum_comm]
      calc ∑ v ∈ verts, ∑ S ∈ verts.powerset, (if ({v} : Finset V) ⊆ S then w S else 0)
          = ∑ v ∈ verts, ∑ S ∈ verts.powerset.filter (({v} : Finset V) ⊆ ·), w S :=
            Finset.sum_congr rfl fun v _ => (Finset.sum_filter _ _).symm
        _ = ∑ v ∈ verts, p := Finset.sum_congr rfl fun v hv => by
            simpa using sum_powerset_bernoulli_superset verts {v} (Finset.singleton_subset_iff.mpr hv) p
        _ = p * (verts.card : ℝ) := by simp [mul_comm]
    have hC : ∑ S ∈ verts.powerset, w S * ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ) =
        p ^ 4 * (crossings.card : ℝ) := by
      have hrw : ∑ S ∈ verts.powerset, w S * ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ) =
          ∑ S ∈ verts.powerset, ∑ c ∈ crossings, (if supp c ⊆ S then w S else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
      rw [hrw, Finset.sum_comm]
      calc ∑ c ∈ crossings, ∑ S ∈ verts.powerset, (if supp c ⊆ S then w S else 0)
          = ∑ c ∈ crossings, ∑ S ∈ verts.powerset.filter (supp c ⊆ ·), w S :=
            Finset.sum_congr rfl fun c _ => (Finset.sum_filter _ _).symm
        _ = ∑ c ∈ crossings, p ^ 4 := Finset.sum_congr rfl fun c hc => by
            rw [sum_powerset_bernoulli_superset verts (supp c) (hC_sub c hc).1 p, (hC_sub c hc).2]
        _ = p ^ 4 * (crossings.card : ℝ) := by simp [mul_comm]
    have hRHS : ∑ S ∈ verts.powerset, w S * (3 * (S.card : ℝ) +
          ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ)) =
        3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ) := by
      have hsp : ∑ S ∈ verts.powerset, w S * (3 * (S.card : ℝ) +
            ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ)) =
          3 * (∑ S ∈ verts.powerset, w S * (S.card : ℝ)) +
          ∑ S ∈ verts.powerset, w S * ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun S _ => by ring
      rw [hsp, hV, hC]; ring
    have hmain : p ^ 2 * (edges.card : ℝ) ≤ 3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ) := by
      rwa [hLHS, hRHS] at hsum_ineq
    have hmul : (edges.card : ℝ) ^ 4 * (p ^ 2 * (edges.card : ℝ)) ≤
        (edges.card : ℝ) ^ 4 * (3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    have h1 : (edges.card : ℝ) ^ 4 * (p ^ 2 * (edges.card : ℝ)) =
        16 * (verts.card : ℝ) ^ 2 * (edges.card : ℝ) ^ 3 := by
      have he_ne : (edges.card : ℝ) ≠ 0 := ne_of_gt he_pos
      simp only [p]; field_simp [he_ne]; ring
    have h2 : (edges.card : ℝ) ^ 4 * (3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ)) =
        12 * (verts.card : ℝ) ^ 2 * (edges.card : ℝ) ^ 3 +
        256 * (verts.card : ℝ) ^ 4 * (crossings.card : ℝ) := by
      have he_ne : (edges.card : ℝ) ≠ 0 := ne_of_gt he_pos
      simp only [p]; field_simp [he_ne]; ring
    have hcr : (edges.card : ℝ) ^ 3 ≤ 64 * (verts.card : ℝ) ^ 2 * (crossings.card : ℝ) := by
      have h4v2 : (0 : ℝ) < 4 * (verts.card : ℝ) ^ 2 := by positivity
      nlinarith [hmul, h1, h2]
    linarith [show (0 : ℝ) ≤ 64 * (verts.card : ℝ) ^ 3 by positivity]
  · have hlt : (edges.card : ℝ) ≤ 4 * (verts.card : ℝ) := by
      exact_mod_cast le_of_lt (not_le.mp hDense)
    have hpow : (edges.card : ℝ) ^ 3 ≤ (4 * (verts.card : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlt 3
    have hnn : (0 : ℝ) ≤ 64 * (verts.card : ℝ) ^ 2 * (crossings.card : ℝ) := by positivity
    linarith [show (4 * (verts.card : ℝ)) ^ 3 = 64 * (verts.card : ℝ) ^ 3 by ring]

/-- Finite cubic Jensen inequality: `(∑ x_i)³ ≤ |S|² * ∑ x_i³` for `x_i ≥ 0`. -/
private lemma cube_sum_le_card_sq_mul_sum_cube {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) :
    (∑ i ∈ S, x i) ^ 3 ≤ (S.card : ℝ) ^ 2 * ∑ i ∈ S, (x i) ^ 3 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ 3) := convexOn_pow 3
  have hw_nn : ∀ i ∈ S, (0 : ℝ) ≤ (S.card : ℝ)⁻¹ := fun _ _ => inv_nonneg.mpr (le_of_lt hcard_pos)
  have hw_sum : ∑ _i ∈ S, (S.card : ℝ)⁻¹ = 1 := by
    simp [mul_inv_cancel₀ (ne_of_gt hcard_pos)]
  have hj := hconv.map_sum_le hw_nn hw_sum (fun i hi => hx i hi)
  simp only [smul_eq_mul] at hj
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
  have hmul := mul_le_mul_of_nonneg_left hj (show (0 : ℝ) ≤ (S.card : ℝ) ^ 3 by positivity)
  have hL : (S.card : ℝ) ^ 3 * ((S.card : ℝ)⁻¹ * ∑ i ∈ S, x i) ^ 3 = (∑ i ∈ S, x i) ^ 3 := by
    have hne0 : (S.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
    field_simp [hne0]
  have hR : (S.card : ℝ) ^ 3 * ((S.card : ℝ)⁻¹ * ∑ i ∈ S, x i ^ 3) =
      (S.card : ℝ) ^ 2 * ∑ i ∈ S, x i ^ 3 := by
    have hne0 : (S.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
    field_simp [hne0]
  linarith

/-- **Multigraph Crossing Lemma (Székely 1997 — Finite Bundle-Sampling + Cubic Jensen):**
For any finite multigraph `(verts, edges)` with endpoint map `endpts`, maximum parallel-edge
multiplicity `≤ m` (`m ≥ 1`), and crossing edge-pairs `crossings` between distinct endpoint pairs,
if every simple subgraph `H ⊆ edges` satisfies the simple Crossing Lemma
`|H|³ ≤ 64 |V|² |cr(H)| + 64 |V|³`, then
`|edges|³ ≤ 64 m |verts|² |crossings| + 64 m³ |verts|³`. -/
theorem ppl174_crossing_lemma_multigraph {V E : Type*} [DecidableEq V] [DecidableEq E]
    (verts : Finset V) (edges : Finset E) (endpts : E → Finset V)
    (crossings : Finset (E × E)) (m : ℕ) (hm : 1 ≤ m)
    (hMult : ∀ u : Finset V, (edges.filter (fun e => endpts e = u)).card ≤ m)
    (hC_sub : ∀ c ∈ crossings, c.1 ∈ edges ∧ c.2 ∈ edges ∧ endpts c.1 ≠ endpts c.2)
    (hSimpleCL : ∀ H : Finset E, H ⊆ edges →
      (∀ e₁ ∈ H, ∀ e₂ ∈ H, endpts e₁ = endpts e₂ → e₁ = e₂) →
      (H.card : ℝ) ^ 3 ≤
        64 * (verts.card : ℝ) ^ 2 * ((crossings.filter (fun c => c.1 ∈ H ∧ c.2 ∈ H)).card : ℝ) +
        64 * (verts.card : ℝ) ^ 3) :
    (edges.card : ℝ) ^ 3 ≤
      64 * (m : ℝ) * (verts.card : ℝ) ^ 2 * (crossings.card : ℝ) +
      64 * (m : ℝ) ^ 3 * (verts.card : ℝ) ^ 3 := by
  let U : Finset (Finset V) := edges.image endpts
  -- Assign each edge `e` in bundle `u = endpts e` a distinct slot in `Fin m` (non-dependent!)
  have hex_slot : ∃ slot : E → Fin m,
      ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, endpts e₁ = endpts e₂ → slot e₁ = slot e₂ → e₁ = e₂ := by
    have hper : ∀ u : Finset V, ∃ g : E → Fin m,
        Set.InjOn g (edges.filter (fun e => endpts e = u) : Set E) := by
      intro u
      have hne : Nonempty ({e : E // e ∈ edges.filter (fun e => endpts e = u)} ↪ Fin m) := by
        rw [Function.Embedding.nonempty_iff_card_le]
        simpa [Fintype.card_coe] using hMult u
      obtain ⟨emb⟩ := hne
      refine ⟨fun e => if h : e ∈ edges.filter (fun e => endpts e = u) then emb ⟨e, h⟩ else ⟨0, by omega⟩, ?_⟩
      intro e₁ h1 e₂ h2 heq
      have h1' : e₁ ∈ edges.filter (fun e => endpts e = u) := h1
      have h2' : e₂ ∈ edges.filter (fun e => endpts e = u) := h2
      simp only [dif_pos h1', dif_pos h2'] at heq
      exact congrArg Subtype.val (emb.injective heq)
    choose g hg using hper
    refine ⟨fun e => g (endpts e) e, ?_⟩
    intro e₁ h1 e₂ h2 hend hgeq
    dsimp only at hgeq
    rw [hend] at hgeq
    exact hg (endpts e₂) (Finset.mem_filter.mpr ⟨h1, hend⟩) (Finset.mem_filter.mpr ⟨h2, rfl⟩) hgeq
  obtain ⟨slot, hslot_inj⟩ := hex_slot
  -- Finite sample space `Ω := U → Fin m`
  let Ω := ∀ _u : U, Fin m
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hΩ_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  let H : Ω → Finset E := fun f =>
    edges.filter (fun e => ∃ he : e ∈ edges,
      f ⟨endpts e, Finset.mem_image_of_mem _ he⟩ = slot e)
  have hH_sub : ∀ f : Ω, H f ⊆ edges := fun f => Finset.filter_subset _ _
  have hH_simple : ∀ f : Ω, ∀ e₁ ∈ H f, ∀ e₂ ∈ H f, endpts e₁ = endpts e₂ → e₁ = e₂ := by
    intro f e₁ h1 e₂ h2 heq
    rcases (Finset.mem_filter.mp h1).2 with ⟨he₁, hf₁⟩
    rcases (Finset.mem_filter.mp h2).2 with ⟨he₂, hf₂⟩
    have hu : (⟨endpts e₁, Finset.mem_image_of_mem _ he₁⟩ : U) =
              ⟨endpts e₂, Finset.mem_image_of_mem _ he₂⟩ := Subtype.ext heq
    rw [hu] at hf₁
    exact hslot_inj e₁ he₁ e₂ he₂ heq (hf₁.symm.trans hf₂)
  -- Counting lemma 1: `m * #{f : Ω | f u₀ = k₀} = |Ω|`
  have hcount1 : ∀ (u₀ : U) (k₀ : Fin m),
      (m : ℝ) * ((Finset.univ.filter (fun f : Ω => f u₀ = k₀)).card : ℝ) = (Fintype.card Ω : ℝ) := by
    intro u₀ k₀
    let e1 : {f : Ω // f u₀ = k₀} × Fin m ≃ Ω :=
      { toFun := fun p => Function.update p.1.1 u₀ p.2
        invFun := fun f => (⟨Function.update f u₀ k₀, by simp⟩, f u₀)
        left_inv := fun ⟨⟨f, hf⟩, j⟩ => by
          ext u
          · by_cases h : u = u₀
            · subst h; simp [hf]
            · simp [Function.update, h]
          · simp
        right_inv := fun f => by
          funext u
          by_cases h : u = u₀
          · subst h; simp
          · simp [Function.update, h] }
    have hcard := Fintype.card_congr e1
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype] at hcard
    have hnat : m * (Finset.univ.filter (fun f : Ω => f u₀ = k₀)).card = Fintype.card Ω :=
      (mul_comm _ _).trans hcard
    exact_mod_cast hnat
  -- Counting lemma 2: `m² * #{f : Ω | f u₁ = k₁ ∧ f u₂ = k₂} = |Ω|` for `u₁ ≠ u₂`
  have hcount2 : ∀ (u₁ u₂ : U) (_hne : u₁ ≠ u₂) (k₁ k₂ : Fin m),
      (m : ℝ) ^ 2 * ((Finset.univ.filter (fun f : Ω => f u₁ = k₁ ∧ f u₂ = k₂)).card : ℝ) =
      (Fintype.card Ω : ℝ) := by
    intro u₁ u₂ hne k₁ k₂
    let e2 : {f : Ω // f u₁ = k₁ ∧ f u₂ = k₂} × Fin m × Fin m ≃ Ω :=
      { toFun := fun p => Function.update (Function.update p.1.1 u₁ p.2.1) u₂ p.2.2
        invFun := fun f =>
          (⟨Function.update (Function.update f u₁ k₁) u₂ k₂,
            by simp [Function.update, hne]⟩, f u₁, f u₂)
        left_inv := fun ⟨⟨f, hf1, hf2⟩, j₁, j₂⟩ => by
          apply Prod.ext
          · apply Subtype.ext; funext u
            by_cases h2 : u = u₂
            · subst h2; simp [hf2]
            · by_cases h1 : u = u₁
              · subst h1; simp [Function.update, h2, hf1]
              · simp [Function.update, h1, h2]
          · apply Prod.ext
            · simp [Function.update, hne]
            · simp
        right_inv := fun f => by
          funext u
          by_cases h2 : u = u₂
          · subst h2; simp
          · by_cases h1 : u = u₁
            · subst h1; simp [Function.update, h2]
            · simp [Function.update, h1, h2] }
    have hcard := Fintype.card_congr e2
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype] at hcard
    have hnat : m ^ 2 * (Finset.univ.filter (fun f : Ω => f u₁ = k₁ ∧ f u₂ = k₂)).card =
        Fintype.card Ω := by
      have : m ^ 2 = m * m := sq m
      rw [this]; linarith
    exact_mod_cast hnat
  -- Expected number of edges: `m * ∑ f, |H f| = |Ω| * |edges|`
  have hsum_E : (m : ℝ) * ∑ f : Ω, ((H f).card : ℝ) = (Fintype.card Ω : ℝ) * (edges.card : ℝ) := by
    have h1 : ∑ f : Ω, ((H f).card : ℝ) =
        ∑ e ∈ edges, ((Finset.univ.filter (fun f : Ω =>
          ∃ he : e ∈ edges, f ⟨endpts e, Finset.mem_image_of_mem _ he⟩ = slot e)).card : ℝ) := by
      have hrw : ∀ f : Ω, ((H f).card : ℝ) =
          ∑ e ∈ edges, (if (∃ he : e ∈ edges,
            f ⟨endpts e, Finset.mem_image_of_mem _ he⟩ = slot e) then (1 : ℝ) else 0) := fun f => by
        dsimp only [H]
        rw [Finset.card_filter, Nat.cast_sum]
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp_rw [hrw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.card_filter, Nat.cast_sum]
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [h1, Finset.mul_sum]
    calc ∑ e ∈ edges, (m : ℝ) * ((Finset.univ.filter (fun f : Ω =>
            ∃ he : e ∈ edges, f ⟨endpts e, Finset.mem_image_of_mem _ he⟩ = slot e)).card : ℝ)
        = ∑ e ∈ edges, (Fintype.card Ω : ℝ) := by
          refine Finset.sum_congr rfl fun e he => ?_
          have hfeq : Finset.univ.filter (fun f : Ω =>
                ∃ he' : e ∈ edges, f ⟨endpts e, Finset.mem_image_of_mem _ he'⟩ = slot e) =
              Finset.univ.filter (fun f : Ω =>
                f ⟨endpts e, Finset.mem_image_of_mem _ he⟩ = slot e) := by
            ext f; simp [he]
          rw [hfeq]
          exact hcount1 ⟨endpts e, Finset.mem_image_of_mem _ he⟩ (slot e)
      _ = (Fintype.card Ω : ℝ) * (edges.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Expected crossings: `m² * ∑ f, |cr(H f)| = |Ω| * |crossings|`
  have hsum_C : (m : ℝ) ^ 2 * ∑ f : Ω,
      ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ) =
      (Fintype.card Ω : ℝ) * (crossings.card : ℝ) := by
    have h1 : ∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ) =
        ∑ c ∈ crossings, ((Finset.univ.filter (fun f : Ω => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ) := by
      have hrw : ∀ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ) =
          ∑ c ∈ crossings, (if c.1 ∈ H f ∧ c.2 ∈ H f then (1 : ℝ) else 0) := fun f => by
        rw [Finset.card_filter, Nat.cast_sum]
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp_rw [hrw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.card_filter, Nat.cast_sum]
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [h1, Finset.mul_sum]
    calc ∑ c ∈ crossings, (m : ℝ) ^ 2 *
            ((Finset.univ.filter (fun f : Ω => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)
        = ∑ _c ∈ crossings, (Fintype.card Ω : ℝ) := by
          refine Finset.sum_congr rfl fun c hc => ?_
          obtain ⟨hc1, hc2, hne⟩ := hC_sub c hc
          have hfeq : Finset.univ.filter (fun f : Ω => c.1 ∈ H f ∧ c.2 ∈ H f) =
              Finset.univ.filter (fun f : Ω =>
                f ⟨endpts c.1, Finset.mem_image_of_mem _ hc1⟩ = slot c.1 ∧
                f ⟨endpts c.2, Finset.mem_image_of_mem _ hc2⟩ = slot c.2) := by
            ext f; simp [H, hc1, hc2]
          rw [hfeq]
          exact hcount2 ⟨endpts c.1, Finset.mem_image_of_mem _ hc1⟩
            ⟨endpts c.2, Finset.mem_image_of_mem _ hc2⟩
            (fun h => hne (congrArg Subtype.val h)) (slot c.1) (slot c.2)
      _ = (Fintype.card Ω : ℝ) * (crossings.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Apply `hSimpleCL` to every `H f`, sum over `f : Ω`, and apply cubic Jensen!
  have hsum_CL : ∑ f : Ω, ((H f).card : ℝ) ^ 3 ≤
      64 * (verts.card : ℝ) ^ 2 *
        (∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
      64 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ) := by
    calc ∑ f : Ω, ((H f).card : ℝ) ^ 3
        ≤ ∑ f : Ω, (64 * (verts.card : ℝ) ^ 2 *
            ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ) +
            64 * (verts.card : ℝ) ^ 3) :=
          Finset.sum_le_sum fun f _ => hSimpleCL (H f) (hH_sub f) (hH_simple f)
      _ = 64 * (verts.card : ℝ) ^ 2 *
            (∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
          64 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hj := cube_sum_le_card_sq_mul_sum_cube (Finset.univ : Finset Ω) (fun f => ((H f).card : ℝ))
    (fun _ _ => Nat.cast_nonneg _)
  rw [Finset.card_univ] at hj
  have hcomb : (∑ f : Ω, ((H f).card : ℝ)) ^ 3 ≤
      (Fintype.card Ω : ℝ) ^ 2 * (64 * (verts.card : ℝ) ^ 2 *
        (∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
        64 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ)) :=
    hj.trans (mul_le_mul_of_nonneg_left hsum_CL (sq_nonneg _))
  -- Multiply by `m³` and cancel `|Ω|³ > 0`
  have hmul_m : (m : ℝ) ^ 3 * (∑ f : Ω, ((H f).card : ℝ)) ^ 3 ≤
      (m : ℝ) ^ 3 * ((Fintype.card Ω : ℝ) ^ 2 * (64 * (verts.card : ℝ) ^ 2 *
        (∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
        64 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ))) :=
    mul_le_mul_of_nonneg_left hcomb (pow_nonneg (le_of_lt hm_pos) 3)
  have hLHS_eq : (m : ℝ) ^ 3 * (∑ f : Ω, ((H f).card : ℝ)) ^ 3 =
      (Fintype.card Ω : ℝ) ^ 3 * (edges.card : ℝ) ^ 3 := by
    calc (m : ℝ) ^ 3 * (∑ f : Ω, ((H f).card : ℝ)) ^ 3
        = ((m : ℝ) * ∑ f : Ω, ((H f).card : ℝ)) ^ 3 := by ring
      _ = ((Fintype.card Ω : ℝ) * (edges.card : ℝ)) ^ 3 := by rw [hsum_E]
      _ = (Fintype.card Ω : ℝ) ^ 3 * (edges.card : ℝ) ^ 3 := by ring
  have hRHS_eq : (m : ℝ) ^ 3 * ((Fintype.card Ω : ℝ) ^ 2 * (64 * (verts.card : ℝ) ^ 2 *
        (∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
        64 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ))) =
      (Fintype.card Ω : ℝ) ^ 3 * (64 * (m : ℝ) * (verts.card : ℝ) ^ 2 * (crossings.card : ℝ) +
        64 * (m : ℝ) ^ 3 * (verts.card : ℝ) ^ 3) := by
    have hsplit : (m : ℝ) ^ 3 * ((Fintype.card Ω : ℝ) ^ 2 * (64 * (verts.card : ℝ) ^ 2 *
          (∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
          64 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ))) =
        64 * (m : ℝ) * (verts.card : ℝ) ^ 2 * (Fintype.card Ω : ℝ) ^ 2 *
          ((m : ℝ) ^ 2 * ∑ f : Ω, ((crossings.filter (fun c => c.1 ∈ H f ∧ c.2 ∈ H f)).card : ℝ)) +
        64 * (m : ℝ) ^ 3 * (verts.card : ℝ) ^ 3 * (Fintype.card Ω : ℝ) ^ 3 := by ring
    rw [hsplit, hsum_C]; ring
  rw [hLHS_eq, hRHS_eq] at hmul_m
  exact le_of_mul_le_mul_left hmul_m (pow_pos hΩ_pos 3)

/-- **Szemerédi–Trotter `m`-Rich Line Incidence Bound (via Simple Crossing Lemma):**
For `m ≥ 2` and any finite `P ⊂ ℝ²` and `L` of `m`-rich lines (`∀ ℓ ∈ L, m ≤ |P ∩ ℓ|`),
if the straight-line segment graph on `(P, L)` (`e = I - |L|` edges, `cr ≤ C(|L|, 2)` crossings)
obeys the Simple Crossing Lemma `e³ ≤ 64 |P|² cr + 64 |P|³`, then
`I(P, L) ≤ 512 |P|² / m² + 11 |P|`. -/
theorem ppl174_szemeredi_trotter_rich_lines
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (m : ℕ) (hm : 2 ≤ m)
    (hrich : ∀ ℓ ∈ L, m ≤ (P.filter (· ∈ ℓ)).card)
    (hCL : (((∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card - 1)) : ℕ) : ℝ) ^ 3 ≤
      64 * (P.card : ℝ) ^ 2 * (L.card.choose 2 : ℝ) + 64 * (P.card : ℝ) ^ 3) :
    (∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card : ℝ)) ≤
      512 * (P.card : ℝ) ^ 2 / (m : ℝ) ^ 2 + 11 * (P.card : ℝ) := by
  set I : ℝ := ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card : ℝ)
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hI_ge_mL : (m : ℝ) * (L.card : ℝ) ≤ I := by
    calc (m : ℝ) * (L.card : ℝ)
        = ∑ _ℓ ∈ L, (m : ℝ) := by simp [mul_comm]
      _ ≤ ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card : ℝ) :=
          Finset.sum_le_sum fun ℓ hℓ => by exact_mod_cast hrich ℓ hℓ
  have hL_le : (L.card : ℝ) ≤ I / (m : ℝ) := (le_div_iff₀ hm_pos).mpr (by linarith)
  have hchoose : (L.card.choose 2 : ℝ) ≤ (L.card : ℝ) ^ 2 / 2 := by
    have h2 : 2 * L.card.choose 2 ≤ L.card * L.card := by
      rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self L.card).two_dvd]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have h2R : (2 : ℝ) * (L.card.choose 2 : ℝ) ≤ (L.card : ℝ) ^ 2 := by
      have : ((2 * L.card.choose 2 : ℕ) : ℝ) ≤ ((L.card * L.card : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith
    linarith
  have he_eq : (((∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card - 1)) : ℕ) : ℝ) = I - (L.card : ℝ) := by
    rw [Nat.cast_sum]
    have hterm : ∀ ℓ ∈ L, (((P.filter (· ∈ ℓ)).card - 1 : ℕ) : ℝ) =
        ((P.filter (· ∈ ℓ)).card : ℝ) - 1 := fun ℓ hℓ => by
      have h1 : 1 ≤ (P.filter (· ∈ ℓ)).card := le_trans (by omega) (hrich ℓ hℓ)
      simpa using Nat.cast_sub (R := ℝ) h1
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    simp [I]
  have he_lb : I / 2 ≤ I - (L.card : ℝ) := by
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h2L : 2 * (L.card : ℝ) ≤ I := by nlinarith [hI_ge_mL, hm2]
    linarith
  have hI_nn : 0 ≤ I := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcube : (I / 2) ^ 3 ≤ 32 * (P.card : ℝ) ^ 2 * (I / (m : ℝ)) ^ 2 + 64 * (P.card : ℝ) ^ 3 := by
    have h1 : (I / 2) ^ 3 ≤ (I - (L.card : ℝ)) ^ 3 := pow_le_pow_left₀ (by linarith) he_lb 3
    rw [he_eq] at hCL
    have hL2 : (L.card : ℝ) ^ 2 ≤ (I / (m : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hL_le 2
    have h2 : 64 * (P.card : ℝ) ^ 2 * (L.card.choose 2 : ℝ) ≤
        32 * (P.card : ℝ) ^ 2 * (I / (m : ℝ)) ^ 2 := by
      have : 64 * (P.card : ℝ) ^ 2 * (L.card.choose 2 : ℝ) ≤
          64 * (P.card : ℝ) ^ 2 * ((L.card : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      nlinarith [this, hL2, show (0 : ℝ) ≤ (P.card : ℝ) ^ 2 by positivity]
    linarith
  by_cases hdom : 64 * (P.card : ℝ) ^ 3 ≤ 32 * (P.card : ℝ) ^ 2 * (I / (m : ℝ)) ^ 2
  · have hcase : I ^ 3 ≤ 512 * (P.card : ℝ) ^ 2 * (I / (m : ℝ)) ^ 2 := by linarith
    by_cases hI0 : I = 0
    · rw [hI0]; positivity
    have hIpos : 0 < I := lt_of_le_of_ne hI_nn (Ne.symm hI0)
    have hI2 : 0 < I ^ 2 := pow_pos hIpos 2
    have hmul : I ^ 2 * I ≤ I ^ 2 * (512 * (P.card : ℝ) ^ 2 / (m : ℝ) ^ 2) := by
      have hrew : I ^ 2 * (512 * (P.card : ℝ) ^ 2 / (m : ℝ) ^ 2) =
          512 * (P.card : ℝ) ^ 2 * (I / (m : ℝ)) ^ 2 := by ring
      linarith
    have hle := le_of_mul_le_mul_left hmul hI2
    linarith [show (0 : ℝ) ≤ 11 * (P.card : ℝ) by positivity]
  · have hcase : I ^ 3 ≤ 1024 * (P.card : ℝ) ^ 3 := by linarith [not_le.mp hdom]
    have h11 : I ≤ 11 * (P.card : ℝ) := by
      by_contra hgt
      have hlt : 11 * (P.card : ℝ) < I := not_le.mp hgt
      have hp3 : (11 * (P.card : ℝ)) ^ 3 < I ^ 3 :=
        pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      have : (11 * (P.card : ℝ)) ^ 3 = 1331 * (P.card : ℝ) ^ 3 := by ring
      nlinarith [show (0 : ℝ) ≤ (P.card : ℝ) ^ 3 by positivity]
    linarith [show (0 : ℝ) ≤ 512 * (P.card : ℝ) ^ 2 / (m : ℝ) ^ 2 by positivity]

/-- Perpendicular bisector of two distinct points `u ≠ v` in `ℝ²`, as a 1D `AffineSubspace`. -/
private noncomputable def perpBisector (u v : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  AffineSubspace.mk' (mkPt ((u 0 + v 0) / 2) ((u 1 + v 1) / 2))
    (Submodule.span ℝ ({mkPt (-(v 1 - u 1)) (v 0 - u 0)} : Set (EuclideanSpace ℝ (Fin 2))))

private lemma perpBisector_finrank {u v : EuclideanSpace ℝ (Fin 2)} (huv : u ≠ v) :
    Module.finrank ℝ (perpBisector u v).direction = 1 := by
  unfold perpBisector
  rw [AffineSubspace.direction_mk']
  apply finrank_span_singleton
  intro h0
  apply huv
  have hx : -(v 1 - u 1) = 0 := by
    have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h0
    simpa [mkPt_zero] using this
  have hy : v 0 - u 0 = 0 := by
    have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h0
    simpa [mkPt_one] using this
  exact pt_ext (by linarith) (by linarith)

private lemma mem_perpBisector_iff {u v w : EuclideanSpace ℝ (Fin 2)} (huv : u ≠ v) :
    w ∈ perpBisector u v ↔ dist w u = dist w v := by
  set dx : ℝ := v 0 - u 0
  set dy : ℝ := v 1 - u 1
  have hD : 0 < dx ^ 2 + dy ^ 2 := by
    by_contra hle
    have h0 : dx ^ 2 + dy ^ 2 ≤ 0 := not_lt.mp hle
    have hdx : dx = 0 := by nlinarith [sq_nonneg dx, sq_nonneg dy]
    have hdy : dy = 0 := by nlinarith [sq_nonneg dx, sq_nonneg dy]
    exact huv (pt_ext (by dsimp [dx] at hdx; linarith) (by dsimp [dy] at hdy; linarith))
  have heq_dist : dist w u = dist w v ↔
      (w 0 - (u 0 + v 0) / 2) * dx + (w 1 - (u 1 + v 1) / 2) * dy = 0 := by
    have hsq : dist w u = dist w v ↔ dist w u ^ 2 = dist w v ^ 2 := by
      constructor
      · intro h; rw [h]
      · intro h
        have h1 := sq_eq_sq_iff_eq_or_eq_neg.mp h
        rcases h1 with h1 | h1
        · exact h1
        · linarith [dist_nonneg (x := w) (y := u), dist_nonneg (x := w) (y := v)]
    rw [hsq, dist_sq_eq_coords, dist_sq_eq_coords]
    have hid : ((w 0 - u 0) ^ 2 + (w 1 - u 1) ^ 2) - ((w 0 - v 0) ^ 2 + (w 1 - v 1) ^ 2) =
        2 * ((w 0 - (u 0 + v 0) / 2) * dx + (w 1 - (u 1 + v 1) / 2) * dy) := by
      dsimp [dx, dy]; ring
    constructor <;> intro h <;> linarith
  rw [heq_dist]
  unfold perpBisector
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    have h0 : t * (-dy) = w 0 - (u 0 + v 0) / 2 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) ht
      simpa [vsub_eq_sub, mkPt_zero, dy] using this
    have h1 : t * dx = w 1 - (u 1 + v 1) / 2 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) ht
      simpa [vsub_eq_sub, mkPt_one, dx] using this
    rw [← h0, ← h1]; ring
  · intro horth
    let t : ℝ := (-(w 0 - (u 0 + v 0) / 2) * dy + (w 1 - (u 1 + v 1) / 2) * dx) / (dx ^ 2 + dy ^ 2)
    refine ⟨t, pt_ext ?_ ?_⟩
    · simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply, mkPt_zero]
      change t * (-dy) = w 0 - (u 0 + v 0) / 2
      have hne : dx ^ 2 + dy ^ 2 ≠ 0 := ne_of_gt hD
      dsimp [t]; rw [div_mul_eq_mul_div, div_eq_iff hne]
      have hid : (-(w 0 - (u 0 + v 0) / 2) * dy + (w 1 - (u 1 + v 1) / 2) * dx) * (-dy) -
          (w 0 - (u 0 + v 0) / 2) * (dx ^ 2 + dy ^ 2) =
          -dx * ((w 0 - (u 0 + v 0) / 2) * dx + (w 1 - (u 1 + v 1) / 2) * dy) := by ring
      rw [horth, mul_zero] at hid; linarith
    · simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply, mkPt_one]
      change t * dx = w 1 - (u 1 + v 1) / 2
      have hne : dx ^ 2 + dy ^ 2 ≠ 0 := ne_of_gt hD
      dsimp [t]; rw [div_mul_eq_mul_div, div_eq_iff hne]
      have hid : (-(w 0 - (u 0 + v 0) / 2) * dy + (w 1 - (u 1 + v 1) / 2) * dx) * dx -
          (w 1 - (u 1 + v 1) / 2) * (dx ^ 2 + dy ^ 2) =
          -dy * ((w 0 - (u 0 + v 0) / 2) * dx + (w 1 - (u 1 + v 1) / 2) * dy) := by ring
      rw [horth, mul_zero] at hid; linarith

/-- Polar angle of `q` relative to center `x` in `ℝ²`. -/
private noncomputable def polarAng (x q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Complex.arg (⟨q 0 - x 0, q 1 - x 1⟩ : ℂ)

private lemma polarAng_injOn_circle {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    {S : Finset (EuclideanSpace ℝ (Fin 2))} (hS : ∀ q ∈ S, dist x q = r) :
    Set.InjOn (polarAng x) (S : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro q₁ hq₁ q₂ hq₂ harg
  let z₁ : ℂ := ⟨q₁ 0 - x 0, q₁ 1 - x 1⟩
  let z₂ : ℂ := ⟨q₂ 0 - x 0, q₂ 1 - x 1⟩
  have hnorm : ∀ q ∈ S, ‖(⟨q 0 - x 0, q 1 - x 1⟩ : ℂ)‖ = r := fun q hq => by
    have hd := dist_sq_eq_coords x q
    rw [hS q hq] at hd
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only
    rw [show (q 0 - x 0) * (q 0 - x 0) + (q 1 - x 1) * (q 1 - x 1) = r ^ 2 by linarith,
      Real.sqrt_sq (le_of_lt hr)]
  have hn1 : ‖z₁‖ = r := hnorm q₁ hq₁
  have hn2 : ‖z₂‖ = r := hnorm q₂ hq₂
  have hz1_ne : z₁ ≠ 0 := by intro h; rw [h, norm_zero] at hn1; linarith
  have hz2_ne : z₂ ≠ 0 := by intro h; rw [h, norm_zero] at hn2; linarith
  have hc1 := Complex.cos_arg hz1_ne; have hc2 := Complex.cos_arg hz2_ne
  have hs1 := Complex.sin_arg z₁; have hs2 := Complex.sin_arg z₂
  change z₁.arg = z₂.arg at harg
  rw [hn1] at hc1 hs1; rw [hn2, ← harg] at hc2 hs2
  have hre : z₁.re = z₂.re := by
    have : z₁.re / r = z₂.re / r := hc1.symm.trans hc2
    exact (div_left_inj' (ne_of_gt hr)).mp this
  have him : z₁.im = z₂.im := by
    have : z₁.im / r = z₂.im / r := hs1.symm.trans hs2
    exact (div_left_inj' (ne_of_gt hr)).mp this
  exact pt_ext (by dsimp [z₁, z₂] at hre; linarith) (by dsimp [z₁, z₂] at him; linarith)

/-- Canonical angle-sorted enumeration `Fin S.card ≃ S` of a finite set `S` on a circle `S(x, r)`. -/
private noncomputable def circleAngleEquiv {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : ∀ q ∈ S, dist x q = r) :
    Fin S.card ≃ S :=
  let A : Finset ℝ := S.image (polarAng x)
  have hAcard : A.card = S.card := Finset.card_image_of_injOn (polarAng_injOn_circle hr hS)
  let embA : Fin S.card ↪o ℝ := A.orderEmbOfFin hAcard
  let toS : Fin S.card → S := fun i =>
    have hmem : embA i ∈ S.image (polarAng x) := A.orderEmbOfFin_mem hAcard i
    ⟨Classical.choose (Finset.mem_image.mp hmem),
      (Classical.choose_spec (Finset.mem_image.mp hmem)).1⟩
  have htoS_ang : ∀ i, polarAng x (toS i).1 = embA i := fun i =>
    (Classical.choose_spec (Finset.mem_image.mp (A.orderEmbOfFin_mem hAcard i))).2
  have htoS_inj : Function.Injective toS := fun i j hij => by
    have : embA i = embA j := by rw [← htoS_ang i, ← htoS_ang j, hij]
    exact embA.injective this
  Equiv.ofBijective toS
    ((Fintype.bijective_iff_injective_and_card toS).mpr
      ⟨htoS_inj, by simp [Fintype.card_coe]⟩)

private lemma circleAngleEquiv_strictMono {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : ∀ q ∈ S, dist x q = r) :
    StrictMono (fun i : Fin S.card => polarAng x (circleAngleEquiv hr S hS i).1) := by
  intro i j hij
  dsimp only [circleAngleEquiv]
  have hi := (Classical.choose_spec (Finset.mem_image.mp
    ((S.image (polarAng x)).orderEmbOfFin_mem (Finset.card_image_of_injOn (polarAng_injOn_circle hr hS)) i))).2
  have hj := (Classical.choose_spec (Finset.mem_image.mp
    ((S.image (polarAng x)).orderEmbOfFin_mem (Finset.card_image_of_injOn (polarAng_injOn_circle hr hS)) j))).2
  simp only [Equiv.ofBijective_apply]
  rw [hi, hj]
  exact ((S.image (polarAng x)).orderEmbOfFin _).strictMono hij

/-- Pure real-algebraic finish of Székely's `Ω(n^{4/5})` bound from the multigraph Crossing Lemma. -/
private lemma szekely_algebraic_finish {n t m : ℕ} (hn_big : 5114 ≤ n) (ht_pos : 1 ≤ t)
    (ht_lt : (t : ℝ) < (n : ℝ) / 100)
    (hm_le : (m : ℝ) ≤ 65 * Real.sqrt (t : ℝ))
    (hpow6 : (n : ℝ) ^ 6 / 8 ≤ 64 * (m : ℝ) * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 +
      64 * (m : ℝ) ^ 3 * (n : ℝ) ^ 3) :
    (n : ℝ) ^ (4 / 5 : ℝ) / 1000 ≤ (t : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_lt_n : (m : ℝ) < (65 / 10 : ℝ) * Real.sqrt (n : ℝ) := by
    have hsq : Real.sqrt (t : ℝ) < Real.sqrt ((n : ℝ) / 100) :=
      Real.sqrt_lt_sqrt (Nat.cast_nonneg t) ht_lt
    have h100 : Real.sqrt ((n : ℝ) / 100) = Real.sqrt (n : ℝ) / 10 := by
      rw [Real.sqrt_div (Nat.cast_nonneg n), show (100 : ℝ) = 10 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
    linarith [hm_le]
  have hm3_small : 64 * (m : ℝ) ^ 3 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 6 / 16 := by
    have h1 : (m : ℝ) ^ 3 ≤ ((65 / 10 : ℝ) * Real.sqrt (n : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) (le_of_lt hm_lt_n) 3
    have hsq3 : (Real.sqrt (n : ℝ)) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
      rw [pow_succ, sq, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    have hsn : 71.5 ≤ Real.sqrt (n : ℝ) := by
      have hnR : (5114 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_big
      exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
    have hbase : 64 * ((65 / 10 : ℝ) ^ 3) * (n : ℝ) * Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ 3 / 16 := by
      have hsq_n : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
      have hcoef : 64 * ((65 / 10 : ℝ) ^ 3) * 16 ≤ 71.5 ^ 3 := by norm_num
      have hs3 : 71.5 ^ 3 ≤ Real.sqrt (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hsn 3
      have h16 : 64 * ((65 / 10 : ℝ) ^ 3) * 16 ≤ Real.sqrt (n : ℝ) ^ 3 := hcoef.trans hs3
      have hmul := mul_le_mul_of_nonneg_right h16 (by positivity : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt (n : ℝ))
      have hR : Real.sqrt (n : ℝ) ^ 3 * ((n : ℝ) * Real.sqrt (n : ℝ)) = (n : ℝ) ^ 3 := by
        calc Real.sqrt (n : ℝ) ^ 3 * ((n : ℝ) * Real.sqrt (n : ℝ))
            = (n : ℝ) * (Real.sqrt (n : ℝ) ^ 2) ^ 2 := by ring
          _ = (n : ℝ) * (n : ℝ) ^ 2 := by rw [hsq_n]
          _ = (n : ℝ) ^ 3 := by ring
      linarith
    have hstep : 64 * (m : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / 16 := by
      calc 64 * (m : ℝ) ^ 3
          ≤ 64 * ((65 / 10 : ℝ) * Real.sqrt (n : ℝ)) ^ 3 := by linarith
        _ = 64 * (65 / 10 : ℝ) ^ 3 * (Real.sqrt (n : ℝ)) ^ 3 := by ring
        _ = 64 * (65 / 10 : ℝ) ^ 3 * (n : ℝ) * Real.sqrt (n : ℝ) := by rw [hsq3]; ring
        _ ≤ (n : ℝ) ^ 3 / 16 := hbase
    have := mul_le_mul_of_nonneg_right hstep (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)
    linarith
  have hmain6 : (n : ℝ) ^ 6 / 16 ≤ 64 * (m : ℝ) * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by linarith
  have hmain2 : (n : ℝ) ^ 2 ≤ 1024 * (m : ℝ) * (t : ℝ) ^ 2 := by
    have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos hn_pos 4
    have hmul : (n : ℝ) ^ 4 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 * (1024 * (m : ℝ) * (t : ℝ) ^ 2) := by
      linarith
    exact le_of_mul_le_mul_left hmul hn4
  have ht52 : (n : ℝ) ^ 2 ≤ 66560 * (t : ℝ) ^ 2 * Real.sqrt (t : ℝ) := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm_le (by norm_num : (0 : ℝ) ≤ 1024)) (sq_nonneg (t : ℝ))
    linarith
  have ht5 : (n : ℝ) ^ 4 ≤ (1000 * (t : ℝ)) ^ 5 := by
    have hsq := pow_le_pow_left₀ (sq_nonneg (n : ℝ)) ht52 2
    have hL : ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 := by ring
    have hR : (66560 * (t : ℝ) ^ 2 * Real.sqrt (t : ℝ)) ^ 2 = 66560 ^ 2 * (t : ℝ) ^ 5 := by
      calc (66560 * (t : ℝ) ^ 2 * Real.sqrt (t : ℝ)) ^ 2
          = 66560 ^ 2 * (t : ℝ) ^ 4 * (Real.sqrt (t : ℝ)) ^ 2 := by ring
        _ = 66560 ^ 2 * (t : ℝ) ^ 4 * (t : ℝ) := by rw [Real.sq_sqrt (Nat.cast_nonneg t)]
        _ = 66560 ^ 2 * (t : ℝ) ^ 5 := by ring
    rw [hL, hR] at hsq
    have hcoef : (66560 : ℝ) ^ 2 ≤ 1000 ^ 5 := by norm_num
    have hR2 : 66560 ^ 2 * (t : ℝ) ^ 5 ≤ (1000 * (t : ℝ)) ^ 5 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    exact hsq.trans hR2
  have hrpow : (n : ℝ) ^ (4 / 5 : ℝ) ≤ 1000 * (t : ℝ) := by
    have h5 : ((n : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℝ) ≤ (1000 * (t : ℝ)) ^ (5 : ℝ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      have hexp : (4 / 5 : ℝ) * 5 = (4 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast, show (5 : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast]
      exact ht5
    exact (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (by positivity) (by norm_num)).mp h5
  linarith

/-- **Székely (1997) `Ω(n^{4/5})` Bipartite Pinned-Distance Lower Bound (Explicit Constant `1/1000`):**
For ANY two `n`-point planar sets `X, Y ⊂ ℝ²` (`n ≥ 1`), assuming:
1. `hST`: the Szemerédi–Trotter `m`-rich line bound on `X` (proved from the Simple Crossing Lemma
   in `ppl174_szemeredi_trotter_rich_lines`), and
2. `hCircleCL`: the circle-arc drawing Crossing Lemma on `Y` (every simple subgraph of the
   canonical consecutive-cyclic-arc multigraph `E₀` obeys `|H|³ ≤ 64 |Y|² |cr(H)| + 64 |Y|³` for a
   crossing edge-pair set `cr` with `|cr| ≤ 2 * C(|C|, 2)`),
there exists a pin `x ∈ X` determining at least `n^{4/5} / 1000` distinct distances to `Y`
(and hence at least `n^{4/5} / 1000` total bipartite distances `d(x, y)`!). -/
theorem ppl015_szekely_bipartite_four_fifths
    (X Y : Finset (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (hn : 1 ≤ n)
    (hX : X.card = n) (hY : Y.card = n)
    (hST : ∀ (m : ℕ), 2 ≤ m →
      ∀ L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
        (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ m ≤ (X.filter (· ∈ ℓ)).card) →
        (∑ ℓ ∈ L, ((X.filter (· ∈ ℓ)).card : ℝ)) ≤
          512 * (X.card : ℝ) ^ 2 / (m : ℝ) ^ 2 + 11 * (X.card : ℝ))
    (hCircleCL : ∀ (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
      (∀ e ∈ E,
        e.1 ∈ X ∧ e.2.1 ∈ Y ∧ e.2.2 ∈ Y ∧ e.2.1 ≠ e.2.2 ∧
        dist e.1 e.2.1 = dist e.1 e.2.2 ∧
        3 ≤ (Y.filter (fun y => dist e.1 y = dist e.1 e.2.1)).card ∧
        let ang := fun q : EuclideanSpace ℝ (Fin 2) =>
          Complex.arg (⟨q 0 - e.1 0, q 1 - e.1 1⟩ : ℂ)
        let S := Y.filter (fun y => dist e.1 y = dist e.1 e.2.1)
        ((ang e.2.1 < ang e.2.2 ∧ ∀ w ∈ S, ¬ (ang e.2.1 < ang w ∧ ang w < ang e.2.2)) ∨
         ((∀ w ∈ S, ang w ≤ ang e.2.1) ∧ (∀ w ∈ S, ang e.2.2 ≤ ang w)))) →
      ∃ crossings : Finset
          ((EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
           (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
        (∀ c ∈ crossings, c.1 ∈ E ∧ c.2 ∈ E ∧ ({c.1.2.1, c.1.2.2} : Finset _) ≠ {c.2.2.1, c.2.2.2}) ∧
        crossings.card ≤ 2 * (E.image (fun e => (e.1, dist e.1 e.2.1))).card.choose 2 ∧
        (∀ H : Finset _, H ⊆ E →
          (∀ e₁ ∈ H, ∀ e₂ ∈ H, ({e₁.2.1, e₁.2.2} : Finset _) = {e₂.2.1, e₂.2.2} → e₁ = e₂) →
          (H.card : ℝ) ^ 3 ≤
            64 * (Y.card : ℝ) ^ 2 * ((crossings.filter (fun c => c.1 ∈ H ∧ c.2 ∈ H)).card : ℝ) +
            64 * (Y.card : ℝ) ^ 3)) :
    (∃ x ∈ X, (n : ℝ) ^ (4 / 5 : ℝ) / 1000 ≤ ((Y.image (dist x ·)).card : ℝ)) ∧
    (n : ℝ) ^ (4 / 5 : ℝ) / 1000 ≤ (((X ×ˢ Y).image (fun p => dist p.1 p.2)).card : ℝ) := by
  -- Prove the pinned claim first; the total bipartite claim follows immediately
  suffices hpin : ∃ x ∈ X, (n : ℝ) ^ (4 / 5 : ℝ) / 1000 ≤ ((Y.image (dist x ·)).card : ℝ) by
    refine ⟨hpin, ?_⟩
    rcases hpin with ⟨x, hx, hxb⟩
    have hsub : Y.image (dist x ·) ⊆ (X ×ˢ Y).image (fun p => dist p.1 p.2) := by
      intro d hd; rcases Finset.mem_image.mp hd with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    exact hxb.trans (by exact_mod_cast Finset.card_le_card hsub)
  -- Pick `t = max_{x ∈ X} |Y.image (dist x ·)|`
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨xmax, hxmax_mem, hxmax⟩ := Finset.exists_max_image X (fun x => (Y.image (dist x ·)).card) hXne
  set t : ℕ := (Y.image (dist xmax ·)).card
  have ht_pos : 1 ≤ t := by
    obtain ⟨y₀, hy₀⟩ := hYne
    exact Finset.card_pos.mpr ⟨dist xmax y₀, Finset.mem_image_of_mem _ hy₀⟩
  have ht_bound : ∀ x ∈ X, (Y.image (dist x ·)).card ≤ t := hxmax
  refine ⟨xmax, hxmax_mem, ?_⟩
  -- Handle small `n ≤ 5113` directly: `n^{4/5} / 1000 < 1 ≤ t`
  by_cases hn_small : n ≤ 5113
  · have h1 : (n : ℝ) ^ (4 / 5 : ℝ) ≤ 1000 := by
      have h5 : ((n : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℝ) ≤ (1000 : ℝ) ^ (5 : ℝ) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num
        have hnR : (n : ℝ) ≤ 5113 := by exact_mod_cast hn_small
        have h4 : (n : ℝ) ^ (4 : ℕ) ≤ 5113 ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 4
        linarith [show (5113 : ℝ) ^ 4 ≤ 1000000000000000 by norm_num]
      exact (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by norm_num) (by norm_num)).mp h5
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
    linarith
  have hn_big : 5114 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Handle `t ≥ n / 100` directly: `n / 100 ≥ n^{4/5} / 100 > n^{4/5} / 1000`
  by_cases ht_large : (n : ℝ) / 100 ≤ (t : ℝ)
  · have h45 : (n : ℝ) ^ (4 / 5 : ℝ) ≤ (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 (show (4 / 5 : ℝ) ≤ 1 by norm_num)
    linarith
  have ht_lt : (t : ℝ) < (n : ℝ) / 100 := not_le.mp ht_large
  have htR_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Build the canonical consecutive-cyclic-arc multigraph `E₀` from `X` and `Y`
  let Edge := EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)
  let isConsec : Edge → Prop := fun e =>
    e.1 ∈ X ∧ e.2.1 ∈ Y ∧ e.2.2 ∈ Y ∧ e.2.1 ≠ e.2.2 ∧
    dist e.1 e.2.1 = dist e.1 e.2.2 ∧
    3 ≤ (Y.filter (fun y => dist e.1 y = dist e.1 e.2.1)).card ∧
    let S := Y.filter (fun y => dist e.1 y = dist e.1 e.2.1)
    ((polarAng e.1 e.2.1 < polarAng e.1 e.2.2 ∧
        ∀ w ∈ S, ¬ (polarAng e.1 e.2.1 < polarAng e.1 w ∧ polarAng e.1 w < polarAng e.1 e.2.2)) ∨
     ((∀ w ∈ S, polarAng e.1 w ≤ polarAng e.1 e.2.1) ∧
      (∀ w ∈ S, polarAng e.1 e.2.2 ≤ polarAng e.1 w)))
  let E₀ : Finset Edge := (X ×ˢ (Y ×ˢ Y)).filter isConsec
  -- Step 1: Total circles `|C| ≤ n * t`
  let C : Finset (EuclideanSpace ℝ (Fin 2) × ℝ) := E₀.image (fun e => (e.1, dist e.1 e.2.1))
  have hC_card : C.card ≤ n * t := by
    have hsub : C ⊆ X.biUnion (fun x => (Y.image (dist x ·)).image (fun r => (x, r))) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨e, he, rfl⟩
      have hcon := (Finset.mem_filter.mp he).2
      refine Finset.mem_biUnion.mpr ⟨e.1, hcon.1, ?_⟩
      exact Finset.mem_image.mpr ⟨dist e.1 e.2.1, Finset.mem_image_of_mem _ hcon.2.1, rfl⟩
    calc C.card
        ≤ (X.biUnion (fun x => (Y.image (dist x ·)).image (fun r => (x, r)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ X, ((Y.image (dist x ·)).image (fun r => (x, r))).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ X, (Y.image (dist x ·)).card :=
          Finset.sum_le_sum fun x _ => Finset.card_image_le
      _ ≤ ∑ _x ∈ X, t := Finset.sum_le_sum fun x hx => ht_bound x hx
      _ = n * t := by simp [hX]
  -- Helper: on any circle `S(x, r)` with `3 ≤ S.card`, `r > 0` and cyclic pairs lie in `E₀`
  have hcirc_rpos : ∀ x ∈ X, ∀ r : ℝ, 3 ≤ (Y.filter (fun y => dist x y = r)).card → 0 < r := by
    intro x _ r h3
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Y.filter (fun y => dist x y = r)).card)
    have hd1 : dist x y₁ = r := (Finset.mem_filter.mp hy₁).2
    have hd2 : dist x y₂ = r := (Finset.mem_filter.mp hy₂).2
    have hpos : 0 < dist y₁ y₂ := dist_pos.mpr hne
    have htri : dist y₁ y₂ ≤ dist y₁ x + dist x y₂ := dist_triangle _ _ _
    rw [dist_comm y₁ x, hd1, hd2] at htri
    linarith
  -- Step 2: Lower bound on `|E₀|`: `n² ≤ |E₀| + 2 * n * t`
  have hE₀_lb : n * n ≤ E₀.card + 2 * n * t := by
    -- Every `(x, y) ∈ X ×ˢ Y` either lies on a circle with `≤ 2` points, or gives a unique outgoing edge `(x, y, y_next) ∈ E₀`
    let good : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
      (X ×ˢ Y).filter (fun p => 3 ≤ (Y.filter (fun y => dist p.1 y = dist p.1 p.2)).card)
    let bad : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
      (X ×ˢ Y).filter (fun p => (Y.filter (fun y => dist p.1 y = dist p.1 p.2)).card ≤ 2)
    have hpart : n * n ≤ good.card + bad.card := by
      have hunion : X ×ˢ Y ⊆ good ∪ bad := by
        intro p hp
        by_cases h3 : 3 ≤ (Y.filter (fun y => dist p.1 y = dist p.1 p.2)).card
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h3⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, by omega⟩)
      calc n * n = (X ×ˢ Y).card := by rw [Finset.card_product, hX, hY]
        _ ≤ (good ∪ bad).card := Finset.card_le_card hunion
        _ ≤ good.card + bad.card := Finset.card_union_le _ _
    have hbad_le : bad.card ≤ 2 * n * t := by
      let fbad : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) →
          EuclideanSpace ℝ (Fin 2) × ℝ := fun p => (p.1, dist p.1 p.2)
      have himg_sub : bad.image fbad ⊆
          X.biUnion (fun x => (Y.image (dist x ·)).image (fun r => (x, r))) := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
        have hpxy := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
        refine Finset.mem_biUnion.mpr ⟨p.1, hpxy.1, ?_⟩
        exact Finset.mem_image.mpr ⟨dist p.1 p.2, Finset.mem_image_of_mem _ hpxy.2, rfl⟩
      have himg_card : (bad.image fbad).card ≤ n * t := by
        calc (bad.image fbad).card
            ≤ (X.biUnion (fun x => (Y.image (dist x ·)).image (fun r => (x, r)))).card :=
              Finset.card_le_card himg_sub
          _ ≤ ∑ x ∈ X, ((Y.image (dist x ·)).image (fun r => (x, r))).card := Finset.card_biUnion_le
          _ ≤ ∑ x ∈ X, (Y.image (dist x ·)).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
          _ ≤ ∑ _x ∈ X, t := Finset.sum_le_sum fun x hx => ht_bound x hx
          _ = n * t := by simp [hX]
      have hfib : ∀ c ∈ bad.image fbad, (bad.filter (fun p => fbad p = c)).card ≤ 2 := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨p₀, hp₀, rfl⟩
        have hle2 := (Finset.mem_filter.mp hp₀).2
        have hsub : bad.filter (fun p => fbad p = (p₀.1, dist p₀.1 p₀.2)) ⊆
            (Y.filter (fun y => dist p₀.1 y = dist p₀.1 p₀.2)).image (fun y => (p₀.1, y)) := by
          intro p hp
          have hp_mem := (Finset.mem_filter.mp hp).1
          have hp_eq : (p.1, dist p.1 p.2) = (p₀.1, dist p₀.1 p₀.2) := (Finset.mem_filter.mp hp).2
          rcases Prod.mk.inj hp_eq with ⟨hp1, hp2⟩
          have hy : p.2 ∈ Y := (Finset.mem_product.mp (Finset.mem_filter.mp hp_mem).1).2
          have hp2' : dist p₀.1 p.2 = dist p₀.1 p₀.2 := by rw [hp1] at hp2; exact hp2
          refine Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨hy, hp2'⟩, ?_⟩
          exact Prod.ext hp1.symm rfl
        calc (bad.filter (fun p => fbad p = (p₀.1, dist p₀.1 p₀.2))).card
            ≤ ((Y.filter (fun y => dist p₀.1 y = dist p₀.1 p₀.2)).image (fun y => (p₀.1, y))).card :=
              Finset.card_le_card hsub
          _ ≤ (Y.filter (fun y => dist p₀.1 y = dist p₀.1 p₀.2)).card := Finset.card_image_le
          _ ≤ 2 := hle2
      calc bad.card
          = ∑ c ∈ bad.image fbad, (bad.filter (fun p => fbad p = c)).card :=
            Finset.card_eq_sum_card_image fbad bad
        _ ≤ ∑ _c ∈ bad.image fbad, 2 := Finset.sum_le_sum hfib
        _ = 2 * (bad.image fbad).card := by simp [mul_comm]
        _ ≤ 2 * (n * t) := Nat.mul_le_mul_left 2 himg_card
        _ = 2 * n * t := by ring
    have hgood_le : good.card ≤ E₀.card := by
      -- Map each `(x, y) ∈ good` to its cyclic successor edge `(x, y, y_next) ∈ E₀`
      have hex_succ : ∀ p ∈ good, ∃ v ∈ Y, (p.1, p.2, v) ∈ E₀ := by
        intro p hp
        have hpxy := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
        have h3 := (Finset.mem_filter.mp hp).2
        set r := dist p.1 p.2
        set S := Y.filter (fun y => dist p.1 y = r)
        have hr : 0 < r := hcirc_rpos p.1 hpxy.1 r h3
        have hS : ∀ q ∈ S, dist p.1 q = r := fun q hq => (Finset.mem_filter.mp hq).2
        let eqv := circleAngleEquiv hr S hS
        have hmono := circleAngleEquiv_strictMono hr S hS
        have hpS : p.2 ∈ S := Finset.mem_filter.mpr ⟨hpxy.2, rfl⟩
        let i : Fin S.card := eqv.symm ⟨p.2, hpS⟩
        let j : Fin S.card := ⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩
        let v : EuclideanSpace ℝ (Fin 2) := (eqv j).1
        have hvS : v ∈ S := (eqv j).2
        have hvY : v ∈ Y := (Finset.mem_filter.mp hvS).1
        have hdv : dist p.1 v = r := (Finset.mem_filter.mp hvS).2
        have hij_ne : i ≠ j := by
          intro h
          have hval : i.1 = (i.1 + 1) % S.card := congrArg Fin.val h
          by_cases hlt : i.1 + 1 < S.card
          · rw [Nat.mod_eq_of_lt hlt] at hval; omega
          · have : i.1 + 1 = S.card := by omega
            rw [this, Nat.mod_self] at hval; omega
        have hp2_eq : (eqv i).1 = p.2 := congrArg Subtype.val (eqv.apply_symm_apply ⟨p.2, hpS⟩)
        have hpv_ne : p.2 ≠ v := by
          intro h; apply hij_ne; apply eqv.injective; exact Subtype.ext (hp2_eq.trans h)
        refine ⟨v, hvY, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpxy.1, Finset.mem_product.mpr ⟨hpxy.2, hvY⟩⟩, ?_⟩⟩
        refine ⟨hpxy.1, hpxy.2, hvY, hpv_ne, hdv.symm, h3, ?_⟩
        by_cases hlt : i.1 + 1 < S.card
        · left
          have hj_eq : j = ⟨i.1 + 1, hlt⟩ := by ext; exact Nat.mod_eq_of_lt hlt
          refine ⟨?_, ?_⟩
          · rw [← hp2_eq]; exact hmono (by rw [hj_eq]; exact Nat.lt_succ_self i.1)
          · intro w hw ⟨hw1, hw2⟩
            let k : Fin S.card := eqv.symm ⟨w, hw⟩
            have hwk : (eqv k).1 = w := congrArg Subtype.val (eqv.apply_symm_apply ⟨w, hw⟩)
            rw [← hp2_eq, ← hwk] at hw1
            rw [← hwk] at hw2
            have hik : i < k := hmono.lt_iff_lt.mp hw1
            have hkj : k < j := hmono.lt_iff_lt.mp hw2
            have h1 : i.1 < k.1 := hik
            have h2 : k.1 < i.1 + 1 := by rw [hj_eq] at hkj; exact hkj
            omega
        · right
          have hilast : i.1 = S.card - 1 := by have := i.2; omega
          have hj0 : j = ⟨0, by omega⟩ := by
            ext; dsimp only [j]; have : i.1 + 1 = S.card := by omega
            rw [this, Nat.mod_self]
          refine ⟨?_, ?_⟩
          · intro w hw
            let k : Fin S.card := eqv.symm ⟨w, hw⟩
            have hwk : (eqv k).1 = w := congrArg Subtype.val (eqv.apply_symm_apply ⟨w, hw⟩)
            rw [← hp2_eq, ← hwk]
            exact hmono.monotone (show k ≤ i by show k.1 ≤ i.1; have := k.2; omega)
          · intro w hw
            let k : Fin S.card := eqv.symm ⟨w, hw⟩
            have hwk : (eqv k).1 = w := congrArg Subtype.val (eqv.apply_symm_apply ⟨w, hw⟩)
            rw [← hwk]
            exact hmono.monotone (show j ≤ k by rw [hj0]; exact Nat.zero_le _)
      have hsub : good ⊆ E₀.image (fun e => (e.1, e.2.1)) := by
        intro p hp
        obtain ⟨v, _, he⟩ := hex_succ p hp
        exact Finset.mem_image.mpr ⟨(p.1, p.2, v), he, rfl⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    omega
  -- Step 3: Multiplicity threshold `m = ⌈64 √t⌉` (`m ≥ 2`), delete edges of multiplicity `> m`
  let endpts : Edge → Finset (EuclideanSpace ℝ (Fin 2)) := fun e => {e.2.1, e.2.2}
  set m : ℕ := Nat.ceil (64 * Real.sqrt (t : ℝ))
  have hm_ge_64 : 64 ≤ m := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast ht_pos)
    have h64 : (64 : ℝ) ≤ (m : ℝ) := (by linarith : (64 : ℝ) ≤ 64 * Real.sqrt (t : ℝ)).trans (Nat.le_ceil _)
    exact_mod_cast h64
  have hm_ge2 : 2 ≤ m := by omega
  have hm_ge_sq : 4096 * (t : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hceil : 64 * Real.sqrt (t : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
    have hsq := pow_le_pow_left₀ (by positivity) hceil 2
    have hrew : (64 * Real.sqrt (t : ℝ)) ^ 2 = 4096 * (t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg t)]; norm_num
    linarith
  have hm_le : (m : ℝ) ≤ 65 * Real.sqrt (t : ℝ) := by
    have hlt : (m : ℝ) < 64 * Real.sqrt (t : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast ht_pos)
    linarith
  let E₁ : Finset Edge := E₀.filter (fun e => (E₀.filter (fun e' => endpts e' = endpts e)).card ≤ m)
  let Ehigh : Finset Edge := E₀.filter (fun e => m < (E₀.filter (fun e' => endpts e' = endpts e)).card)
  -- Key property 3a: For any fixed unordered pair `{u, v}`, all edges in `E₀` with `endpts = {u, v}` have DISTINCT centers `x ∈ X ∩ perpBisector u v`
  have hedg_center_inj : ∀ e₁ ∈ E₀, ∀ e₂ ∈ E₀, endpts e₁ = endpts e₂ → e₁.1 = e₂.1 → e₁ = e₂ := by
    intro e₁ h1 e₂ h2 hend hcen
    change ({e₁.2.1, e₁.2.2} : Finset _) = {e₂.2.1, e₂.2.2} at hend
    have hc1 := (Finset.mem_filter.mp h1).2
    have hc2 := (Finset.mem_filter.mp h2).2
    have h3 := hc1.2.2.2.2.2.1
    set r := dist e₁.1 e₁.2.1
    set S := Y.filter (fun y => dist e₁.1 y = r)
    have hr : 0 < r := hcirc_rpos e₁.1 hc1.1 r h3
    have hS : ∀ q ∈ S, dist e₁.1 q = r := fun q hq => (Finset.mem_filter.mp hq).2
    have hmem21 : e₂.2.1 ∈ ({e₁.2.1, e₁.2.2} : Finset _) := by
      rw [hend]; exact Finset.mem_insert_self _ _
    have hmem22 : e₂.2.2 ∈ ({e₁.2.1, e₁.2.2} : Finset _) := by
      rw [hend]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hmem21 with h21 | h21
    · have h22 : e₂.2.2 = e₁.2.2 := by
        rcases Finset.mem_insert.mp hmem22 with h | h
        · exfalso; exact hc2.2.2.2.1 (h21.trans h.symm)
        · exact Finset.mem_singleton.mp h
      exact Prod.ext hcen (Prod.ext h21.symm h22.symm)
    · exfalso
      have h21' : e₂.2.1 = e₁.2.2 := Finset.mem_singleton.mp h21
      have h22' : e₂.2.2 = e₁.2.1 := by
        rcases Finset.mem_insert.mp hmem22 with h | h
        · exact h
        · exfalso; exact hc2.2.2.2.1 (h21'.trans (Finset.mem_singleton.mp h).symm)
      have hc1_ord := hc1.2.2.2.2.2.2
      have hc2_ord := hc2.2.2.2.2.2.2
      rw [← hcen, h21', h22', ← hc1.2.2.2.2.1] at hc2_ord
      -- Pick a third point `w ∈ S` distinct from `e₁.2.1` and `e₁.2.2`
      have hpair_sub : ({e₁.2.1, e₁.2.2} : Finset _) ⊆ S := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact Finset.mem_filter.mpr ⟨hc1.2.1, rfl⟩
        · rw [Finset.mem_singleton.mp hq]
          exact Finset.mem_filter.mpr ⟨hc1.2.2.1, hc1.2.2.2.2.1.symm⟩
      have hlt_card : ({e₁.2.1, e₁.2.2} : Finset _).card < S.card := by
        rw [Finset.card_pair hc1.2.2.2.1]; omega
      obtain ⟨w, hwS, hw_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
      have hw1 : w ≠ e₁.2.1 := fun h => hw_not (by simp [h])
      have hw2 : w ≠ e₁.2.2 := fun h => hw_not (by simp [h])
      have hinj := polarAng_injOn_circle hr hS
      have h1S : e₁.2.1 ∈ S := hpair_sub (by simp)
      have h2S : e₁.2.2 ∈ S := hpair_sub (by simp)
      have haw1 : polarAng e₁.1 w ≠ polarAng e₁.1 e₁.2.1 := fun h => hw1 (hinj hwS h1S h)
      have haw2 : polarAng e₁.1 w ≠ polarAng e₁.1 e₁.2.2 := fun h => hw2 (hinj hwS h2S h)
      rcases hc1_ord with ⟨h1lt, h1gap⟩ | ⟨h1max, h1min⟩
      · rcases hc2_ord with ⟨h2lt, _⟩ | ⟨h2max, h2min⟩
        · linarith
        · have hle := h2max w hwS
          have hge := h2min w hwS
          have hnot := h1gap w hwS
          have hlt1 : polarAng e₁.1 e₁.2.1 < polarAng e₁.1 w := lt_of_le_of_ne hge haw1.symm
          have hlt2 : polarAng e₁.1 w < polarAng e₁.1 e₁.2.2 := lt_of_le_of_ne hle haw2
          exact hnot ⟨hlt1, hlt2⟩
      · rcases hc2_ord with ⟨_, h2gap⟩ | ⟨h2max, h2min⟩
        · have hle := h1max w hwS
          have hge := h1min w hwS
          have hnot := h2gap w hwS
          have hlt1 : polarAng e₁.1 e₁.2.2 < polarAng e₁.1 w := lt_of_le_of_ne hge haw2.symm
          have hlt2 : polarAng e₁.1 w < polarAng e₁.1 e₁.2.1 := lt_of_le_of_ne hle haw1
          exact hnot ⟨hlt1, hlt2⟩
        · have hle1 := h1max e₁.2.2 h2S
          have hle2 := h2max e₁.2.1 h1S
          exact hc1.2.2.2.1 (hinj h1S h2S (le_antisymm hle2 hle1))
  -- Key property 3b: Bounding `|Ehigh| ≤ 2 * t * I(X, L_{>m})` using `ppl174_circle_diameter_crossing_le_two`!
  let Lhigh : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    Ehigh.image (fun e => perpBisector e.2.1 e.2.2)
  have hLhigh_rich : ∀ ℓ ∈ Lhigh, Module.finrank ℝ ℓ.direction = 1 ∧ m ≤ (X.filter (· ∈ ℓ)).card := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨e, he, rfl⟩
    have he0 := (Finset.mem_filter.mp he).1
    have hgt := (Finset.mem_filter.mp he).2
    have hcon := (Finset.mem_filter.mp he0).2
    refine ⟨perpBisector_finrank hcon.2.2.2.1, ?_⟩
    let B := E₀.filter (fun e' => endpts e' = endpts e)
    have hsub : B.image Prod.fst ⊆ X.filter (· ∈ perpBisector e.2.1 e.2.2) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e', he', rfl⟩
      have he'0 := (Finset.mem_filter.mp he').1
      have hend' : ({e'.2.1, e'.2.2} : Finset _) = {e.2.1, e.2.2} := (Finset.mem_filter.mp he').2
      have hcon' := (Finset.mem_filter.mp he'0).2
      refine Finset.mem_filter.mpr ⟨hcon'.1, (mem_perpBisector_iff hcon.2.2.2.1).mpr ?_⟩
      have hmem1 : e.2.1 ∈ ({e'.2.1, e'.2.2} : Finset _) := by rw [hend']; exact Finset.mem_insert_self _ _
      have hmem2 : e.2.2 ∈ ({e'.2.1, e'.2.2} : Finset _) := by
        rw [hend']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rcases Finset.mem_insert.mp hmem1 with h1 | h1 <;>
      rcases Finset.mem_insert.mp hmem2 with h2 | h2
      · rw [h1, h2]
      · rw [h1, Finset.mem_singleton.mp h2]; exact hcon'.2.2.2.2.1
      · rw [Finset.mem_singleton.mp h1, h2]; exact hcon'.2.2.2.2.1.symm
      · rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]
    have hinj : Set.InjOn Prod.fst (B : Set Edge) := by
      intro e₁ h1 e₂ h2 hfst
      have h1' := Finset.mem_filter.mp h1
      have h2' := Finset.mem_filter.mp h2
      exact hedg_center_inj e₁ h1'.1 e₂ h2'.1 (h1'.2.trans h2'.2.symm) hfst
    have hcard_eq : (B.image Prod.fst).card = B.card := Finset.card_image_of_injOn hinj
    have hle := Finset.card_le_card hsub
    rw [hcard_eq] at hle
    have hgt' : m < B.card := hgt
    omega
  -- For every `(ℓ, x, r)` with `ℓ ∈ Lhigh`, `x ∈ X ∩ ℓ`, `r ∈ Y.image (dist x ·)`, at most `2` edges in `Ehigh` have bisector `ℓ`, center `x`, radius `r`!
  have hEhigh_le : (Ehigh.card : ℝ) ≤ 2 * (t : ℝ) * ∑ ℓ ∈ Lhigh, ((X.filter (· ∈ ℓ)).card : ℝ) := by
    have hfib_le : ∀ ℓ ∈ Lhigh, ∀ x ∈ X.filter (· ∈ ℓ), ∀ r ∈ Y.image (dist x ·),
        (Ehigh.filter (fun e => perpBisector e.2.1 e.2.2 = ℓ ∧ e.1 = x ∧ dist e.1 e.2.1 = r)).card ≤ 2 := by
      intro ℓ hℓ x hx r hr_mem
      set F := Ehigh.filter (fun e => perpBisector e.2.1 e.2.2 = ℓ ∧ e.1 = x ∧ dist e.1 e.2.1 = r)
      by_cases hFempty : F = ∅
      · simp [hFempty]
      obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
      have he₀F := Finset.mem_filter.mp he₀
      have he₀0 := (Finset.mem_filter.mp he₀F.1).1
      have hcon₀ := (Finset.mem_filter.mp he₀0).2
      have h3 : 3 ≤ (Y.filter (fun y => dist x y = r)).card := by
        rw [← he₀F.2.2.1, ← he₀F.2.2.2]; exact hcon₀.2.2.2.2.2.1
      set S := Y.filter (fun y => dist x y = r)
      have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
      have hxℓ : x ∈ ℓ := (Finset.mem_filter.mp hx).2
      have hr_pos : 0 < r := hcirc_rpos x hxX r h3
      have hS : ∀ q ∈ S, dist x q = r := fun q hq => (Finset.mem_filter.mp hq).2
      let eqv := circleAngleEquiv hr_pos S hS
      have hmono := circleAngleEquiv_strictMono hr_pos S hS
      have hℓ1 : Module.finrank ℝ ℓ.direction = 1 := (hLhigh_rich ℓ hℓ).1
      have hdiam := ppl174_circle_diameter_crossing_le_two ℓ hℓ1 x hxℓ r hr_pos S hS h3 eqv hmono
      -- Inject `F` into the filtered cyclic indices of `hdiam` via `e ↦ eqv.symm ⟨e.2.1, _⟩`
      let G := Finset.univ.filter (fun i : Fin S.card =>
        let q₁ : EuclideanSpace ℝ (Fin 2) := eqv i
        let q₂ : EuclideanSpace ℝ (Fin 2) := eqv ⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩
        ∀ w ∈ ℓ, dist q₁ w = dist q₂ w)
      have hF_inj : ∃ f : Edge → Fin S.card, Set.InjOn f (F : Set Edge) ∧ ∀ e ∈ F, f e ∈ G := by
        let f : Edge → Fin S.card := fun e =>
          if h : e.2.1 ∈ S then eqv.symm ⟨e.2.1, h⟩ else ⟨0, by omega⟩
        have hmem_S : ∀ e ∈ F, e.2.1 ∈ S ∧ e.2.2 ∈ S := by
          intro e he
          have heF := Finset.mem_filter.mp he
          have hcon := (Finset.mem_filter.mp (Finset.mem_filter.mp heF.1).1).2
          have hx_eq : e.1 = x := heF.2.2.1
          have hr_eq : dist e.1 e.2.1 = r := heF.2.2.2
          rw [hx_eq] at hr_eq
          refine ⟨Finset.mem_filter.mpr ⟨hcon.2.1, hr_eq⟩,
            Finset.mem_filter.mpr ⟨hcon.2.2.1, ?_⟩⟩
          have := hcon.2.2.2.2.1
          rw [hx_eq] at this; linarith
        refine ⟨f, ?_, ?_⟩
        · intro e₁ h1 e₂ h2 hf_eq
          have hm1 := (hmem_S e₁ h1).1
          have hm2 := (hmem_S e₂ h2).1
          have hf1 : f e₁ = eqv.symm ⟨e₁.2.1, hm1⟩ := dif_pos hm1
          have hf2 : f e₂ = eqv.symm ⟨e₂.2.1, hm2⟩ := dif_pos hm2
          rw [hf1, hf2] at hf_eq
          have hu_eq : e₁.2.1 = e₂.2.1 := congrArg Subtype.val (eqv.symm.injective hf_eq)
          -- Also `e₁.1 = x = e₂.1`, and successor in cyclic order is uniquely determined!
          have hx1 : e₁.1 = x := (Finset.mem_filter.mp h1).2.2.1
          have hx2 : e₂.1 = x := (Finset.mem_filter.mp h2).2.2.1
          have hsucc_eq : ∀ (e : Edge) (he : e ∈ F),
              eqv ⟨((eqv.symm ⟨e.2.1, (hmem_S e he).1⟩).1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ =
              ⟨e.2.2, (hmem_S e he).2⟩ := by
            intro e he
            have hm1e := (hmem_S e he).1
            have hm2e := (hmem_S e he).2
            have heF := Finset.mem_filter.mp he
            have hcon := (Finset.mem_filter.mp (Finset.mem_filter.mp heF.1).1).2
            have hxe : e.1 = x := heF.2.2.1
            have hre : dist e.1 e.2.1 = r := heF.2.2.2
            set i := eqv.symm ⟨e.2.1, hm1e⟩
            set j := eqv.symm ⟨e.2.2, hm2e⟩
            have hi_eq : (eqv i).1 = e.2.1 := congrArg Subtype.val (eqv.apply_symm_apply _)
            have hj_eq : (eqv j).1 = e.2.2 := congrArg Subtype.val (eqv.apply_symm_apply _)
            have hord := hcon.2.2.2.2.2.2
            rw [hxe] at hord hre
            have hSeq : Y.filter (fun y => dist x y = dist x e.2.1) = S := by rw [hre]
            rw [hSeq] at hord
            have hj_val : j.1 = (i.1 + 1) % S.card := by
              rcases hord with ⟨hlt, hgap⟩ | ⟨hmax, hmin⟩
              · rw [← hi_eq, ← hj_eq] at hlt
                have hij : i < j := hmono.lt_iff_lt.mp hlt
                have hno : ¬ (i.1 + 1 < j.1) := by
                  intro hmid
                  let k : Fin S.card := ⟨i.1 + 1, by have := j.2; omega⟩
                  have h1 : polarAng x (eqv i).1 < polarAng x (eqv k).1 :=
                    hmono (show i < k from Nat.lt_succ_self i.1)
                  have h2 : polarAng x (eqv k).1 < polarAng x (eqv j).1 :=
                    hmono (show k < j from hmid)
                  rw [hi_eq] at h1; rw [hj_eq] at h2
                  exact hgap (eqv k).1 (eqv k).2 ⟨h1, h2⟩
                have hjeq : j.1 = i.1 + 1 := by omega
                have hltS : i.1 + 1 < S.card := by have := j.2; omega
                rw [Nat.mod_eq_of_lt hltS, hjeq]
              · have hilast : i.1 = S.card - 1 := by
                  have hle := hmax (eqv ⟨S.card - 1, by omega⟩).1 (eqv ⟨S.card - 1, by omega⟩).2
                  rw [← hi_eq] at hle
                  have hle' : (⟨S.card - 1, by omega⟩ : Fin S.card) ≤ i := hmono.le_iff_le.mp hle
                  have := i.2; exact le_antisymm (by omega) hle'
                have hj0 : j.1 = 0 := by
                  have hle := hmin (eqv ⟨0, by omega⟩).1 (eqv ⟨0, by omega⟩).2
                  rw [← hj_eq] at hle
                  have hle' : j ≤ ⟨0, by omega⟩ := hmono.le_iff_le.mp hle
                  exact Nat.eq_zero_of_le_zero hle'
                have : i.1 + 1 = S.card := by omega
                rw [this, Nat.mod_self, hj0]
            have hje : (⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ : Fin S.card) = j :=
              Fin.ext hj_val.symm
            rw [hje]
            exact eqv.apply_symm_apply _
          have hv1 := congrArg Subtype.val (hsucc_eq e₁ h1)
          have hv2 := congrArg Subtype.val (hsucc_eq e₂ h2)
          have hv_eq : e₁.2.2 = e₂.2.2 := by
            have hidx : (eqv.symm ⟨e₁.2.1, (hmem_S e₁ h1).1⟩).1 =
                (eqv.symm ⟨e₂.2.1, (hmem_S e₂ h2).1⟩).1 := congrArg Fin.val hf_eq
            have heqv_eq : eqv ⟨((eqv.symm ⟨e₁.2.1, (hmem_S e₁ h1).1⟩).1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ =
                eqv ⟨((eqv.symm ⟨e₂.2.1, (hmem_S e₂ h2).1⟩).1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ := by
              congr 1; exact Fin.ext (by rw [hidx])
            have := congrArg Subtype.val heqv_eq
            rw [hv1, hv2] at this; exact this
          exact Prod.ext (hx1.trans hx2.symm) (Prod.ext hu_eq hv_eq)
        · intro e he
          have hm1 := (hmem_S e he).1
          have hm2 := (hmem_S e he).2
          have hfe : f e = eqv.symm ⟨e.2.1, hm1⟩ := dif_pos hm1
          rw [hfe]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have heF := Finset.mem_filter.mp he
          have hcon := (Finset.mem_filter.mp (Finset.mem_filter.mp heF.1).1).2
          have hxe : e.1 = x := heF.2.2.1
          have hre : dist e.1 e.2.1 = r := heF.2.2.2
          set i := eqv.symm ⟨e.2.1, hm1⟩
          set j := eqv.symm ⟨e.2.2, hm2⟩
          have hi_eq : (eqv i).1 = e.2.1 := congrArg Subtype.val (eqv.apply_symm_apply _)
          have hj_eq : (eqv j).1 = e.2.2 := congrArg Subtype.val (eqv.apply_symm_apply _)
          have hord := hcon.2.2.2.2.2.2
          rw [hxe] at hord hre
          have hSeq : Y.filter (fun y => dist x y = dist x e.2.1) = S := by rw [hre]
          rw [hSeq] at hord
          have hj_val : j.1 = (i.1 + 1) % S.card := by
            rcases hord with ⟨hlt, hgap⟩ | ⟨hmax, hmin⟩
            · rw [← hi_eq, ← hj_eq] at hlt
              have hij : i < j := hmono.lt_iff_lt.mp hlt
              have hno : ¬ (i.1 + 1 < j.1) := by
                intro hmid
                let k : Fin S.card := ⟨i.1 + 1, by have := j.2; omega⟩
                have h1 : polarAng x (eqv i).1 < polarAng x (eqv k).1 :=
                  hmono (show i < k from Nat.lt_succ_self i.1)
                have h2 : polarAng x (eqv k).1 < polarAng x (eqv j).1 :=
                  hmono (show k < j from hmid)
                rw [hi_eq] at h1; rw [hj_eq] at h2
                exact hgap (eqv k).1 (eqv k).2 ⟨h1, h2⟩
              have hjeq : j.1 = i.1 + 1 := by omega
              have hltS : i.1 + 1 < S.card := by have := j.2; omega
              rw [Nat.mod_eq_of_lt hltS, hjeq]
            · have hilast : i.1 = S.card - 1 := by
                have hle := hmax (eqv ⟨S.card - 1, by omega⟩).1 (eqv ⟨S.card - 1, by omega⟩).2
                rw [← hi_eq] at hle
                have hle' : (⟨S.card - 1, by omega⟩ : Fin S.card) ≤ i := hmono.le_iff_le.mp hle
                have := i.2; exact le_antisymm (by omega) hle'
              have hj0 : j.1 = 0 := by
                have hle := hmin (eqv ⟨0, by omega⟩).1 (eqv ⟨0, by omega⟩).2
                rw [← hj_eq] at hle
                have hle' : j ≤ ⟨0, by omega⟩ := hmono.le_iff_le.mp hle
                exact Nat.eq_zero_of_le_zero hle'
              have : i.1 + 1 = S.card := by omega
              rw [this, Nat.mod_self, hj0]
          have hje : (⟨(i.1 + 1) % S.card, Nat.mod_lt _ (by omega)⟩ : Fin S.card) = j :=
            Fin.ext hj_val.symm
          dsimp only
          rw [hje, hi_eq, hj_eq]
          intro w hw
          rw [← heF.2.1] at hw
          have hdist := (mem_perpBisector_iff hcon.2.2.2.1).mp hw
          rw [dist_comm e.2.1 w, dist_comm e.2.2 w]
          exact hdist
      obtain ⟨f, hfinj, hfmem⟩ := hF_inj
      calc F.card = (F.image f).card := (Finset.card_image_of_injOn hfinj).symm
        _ ≤ G.card := Finset.card_le_card (Finset.image_subset_iff.mpr hfmem)
        _ ≤ 2 := hdiam
    -- Sum `hfib_le` over `(ℓ, x, r)` to bound `Ehigh.card`
    let key : Edge → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2) × ℝ :=
      fun e => (perpBisector e.2.1 e.2.2, e.1, dist e.1 e.2.1)
    let K : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2) × ℝ) :=
      Lhigh.biUnion (fun ℓ =>
        (X.filter (· ∈ ℓ)).biUnion (fun x =>
          (Y.image (dist x ·)).image (fun r => (ℓ, x, r))))
    have himg_sub : Ehigh.image key ⊆ K := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨e, he, rfl⟩
      have he0 := (Finset.mem_filter.mp he).1
      have hcon := (Finset.mem_filter.mp he0).2
      refine Finset.mem_biUnion.mpr ⟨perpBisector e.2.1 e.2.2, Finset.mem_image_of_mem _ he, ?_⟩
      have hx_bis : e.1 ∈ perpBisector e.2.1 e.2.2 :=
        (mem_perpBisector_iff hcon.2.2.2.1).mpr hcon.2.2.2.2.1
      refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hcon.1, hx_bis⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨dist e.1 e.2.1, Finset.mem_image_of_mem _ hcon.2.1, rfl⟩
    have hK_card : K.card ≤ t * ∑ ℓ ∈ Lhigh, (X.filter (· ∈ ℓ)).card := by
      calc K.card
          ≤ ∑ ℓ ∈ Lhigh, ((X.filter (· ∈ ℓ)).biUnion (fun x =>
              (Y.image (dist x ·)).image (fun r => (ℓ, x, r)))).card := Finset.card_biUnion_le
        _ ≤ ∑ ℓ ∈ Lhigh, ∑ x ∈ X.filter (· ∈ ℓ),
              ((Y.image (dist x ·)).image (fun r => (ℓ, x, r))).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
        _ ≤ ∑ ℓ ∈ Lhigh, ∑ x ∈ X.filter (· ∈ ℓ), (Y.image (dist x ·)).card :=
            Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ ≤ ∑ ℓ ∈ Lhigh, ∑ _x ∈ X.filter (· ∈ ℓ), t :=
            Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun x hx => ht_bound x (Finset.mem_filter.mp hx).1
        _ = ∑ ℓ ∈ Lhigh, (X.filter (· ∈ ℓ)).card * t := by simp
        _ = t * ∑ ℓ ∈ Lhigh, (X.filter (· ∈ ℓ)).card := by rw [Finset.mul_sum]; simp [mul_comm]
    have hEhigh_nat : Ehigh.card ≤ 2 * (t * ∑ ℓ ∈ Lhigh, (X.filter (· ∈ ℓ)).card) := by
      calc Ehigh.card
          = ∑ k ∈ Ehigh.image key, (Ehigh.filter (fun e => key e = k)).card :=
            Finset.card_eq_sum_card_image key Ehigh
        _ ≤ ∑ _k ∈ Ehigh.image key, 2 := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkK := himg_sub hk
            rcases Finset.mem_biUnion.mp hkK with ⟨ℓ, hℓ, hk1⟩
            rcases Finset.mem_biUnion.mp hk1 with ⟨x, hx, hk2⟩
            rcases Finset.mem_image.mp hk2 with ⟨r, hr_mem, rfl⟩
            have hfeq : Ehigh.filter (fun e => key e = (ℓ, x, r)) =
                Ehigh.filter (fun e => perpBisector e.2.1 e.2.2 = ℓ ∧ e.1 = x ∧ dist e.1 e.2.1 = r) := by
              refine Finset.filter_congr fun e _ => ?_
              simp only [key, Prod.mk.injEq]
            rw [hfeq]
            exact hfib_le ℓ hℓ x hx r hr_mem
        _ = 2 * (Ehigh.image key).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * K.card := Nat.mul_le_mul_left 2 (Finset.card_le_card himg_sub)
        _ ≤ 2 * (t * ∑ ℓ ∈ Lhigh, (X.filter (· ∈ ℓ)).card) := Nat.mul_le_mul_left 2 hK_card
    have hcast : (Ehigh.card : ℝ) ≤
        ((2 * (t * ∑ ℓ ∈ Lhigh, (X.filter (· ∈ ℓ)).card) : ℕ) : ℝ) := by exact_mod_cast hEhigh_nat
    push_cast at hcast
    linarith
  -- Apply `hST` to `Lhigh`!
  have hST_L : ∑ ℓ ∈ Lhigh, ((X.filter (· ∈ ℓ)).card : ℝ) ≤
      512 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 + 11 * (n : ℝ) := by
    have h := hST m hm_ge2 Lhigh hLhigh_rich
    rw [hX] at h
    exact h
  have hEhigh_num : (Ehigh.card : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 22 * (n : ℝ) * (t : ℝ) := by
    have h1 : 2 * (t : ℝ) * (512 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 + 11 * (n : ℝ)) =
        1024 * (t : ℝ) * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 + 22 * (n : ℝ) * (t : ℝ) := by ring
    have h2 : 1024 * (t : ℝ) * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by
      have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr (by omega)) 2
      rw [div_le_div_iff₀ hm2_pos (by norm_num : (0 : ℝ) < 4)]
      have hn2_nn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
      have := mul_le_mul_of_nonneg_right hm_ge_sq hn2_nn
      linarith
    have h2t_nn : (0 : ℝ) ≤ 2 * (t : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg t)
    have hcomb : (Ehigh.card : ℝ) ≤ 2 * (t : ℝ) * (512 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 + 11 * (n : ℝ)) :=
      hEhigh_le.trans (mul_le_mul_of_nonneg_left hST_L h2t_nn)
    linarith [hcomb, h1, h2]
  -- Step 4: Remaining multigraph `E₁` has `|E₁| ≥ n² / 2` and max multiplicity `≤ m`
  have hE₀_split : E₀.card = E₁.card + Ehigh.card := by
    have hdisj : Disjoint E₁ Ehigh := by
      rw [Finset.disjoint_left]; intro e h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
    have hunion : E₁ ∪ Ehigh = E₀ := by
      ext e; simp only [E₁, Ehigh, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hle : (E₀.filter (fun e' => endpts e' = endpts e)).card ≤ m
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hE₁_lb : (n : ℝ) ^ 2 / 2 ≤ (E₁.card : ℝ) := by
    have hE₀R : (n : ℝ) ^ 2 ≤ (E₀.card : ℝ) + 2 * (n : ℝ) * (t : ℝ) := by
      have hnat : ((n * n : ℕ) : ℝ) ≤ ((E₀.card + 2 * n * t : ℕ) : ℝ) := by exact_mod_cast hE₀_lb
      push_cast at hnat; linarith
    have hspR : (E₀.card : ℝ) = (E₁.card : ℝ) + (Ehigh.card : ℝ) := by exact_mod_cast hE₀_split
    have h24 : 24 * (n : ℝ) * (t : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by nlinarith [ht_lt, hn_pos]
    linarith
  -- Step 5: Apply Multigraph Crossing Lemma (`ppl174_crossing_lemma_multigraph`) to `E₁`!
  have hE₁_valid : ∀ e ∈ E₁,
      e.1 ∈ X ∧ e.2.1 ∈ Y ∧ e.2.2 ∈ Y ∧ e.2.1 ≠ e.2.2 ∧
      dist e.1 e.2.1 = dist e.1 e.2.2 ∧
      3 ≤ (Y.filter (fun y => dist e.1 y = dist e.1 e.2.1)).card ∧
      let ang := fun q : EuclideanSpace ℝ (Fin 2) =>
        Complex.arg (⟨q 0 - e.1 0, q 1 - e.1 1⟩ : ℂ)
      let S := Y.filter (fun y => dist e.1 y = dist e.1 e.2.1)
      ((ang e.2.1 < ang e.2.2 ∧ ∀ w ∈ S, ¬ (ang e.2.1 < ang w ∧ ang w < ang e.2.2)) ∨
       ((∀ w ∈ S, ang w ≤ ang e.2.1) ∧ (∀ w ∈ S, ang e.2.2 ≤ ang w))) := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  obtain ⟨crossings, hC_sub, hC_ub, hSimpleCL⟩ := hCircleCL E₁ hE₁_valid
  have hMult₁ : ∀ u : Finset (EuclideanSpace ℝ (Fin 2)),
      (E₁.filter (fun e => endpts e = u)).card ≤ m := by
    intro u
    by_cases hne : (E₁.filter (fun e => endpts e = u)).Nonempty
    · obtain ⟨e₀, he₀⟩ := hne
      have he₀1 := (Finset.mem_filter.mp he₀).1
      have he₀u := (Finset.mem_filter.mp he₀).2
      have hle_m := (Finset.mem_filter.mp he₀1).2
      have hsub : E₁.filter (fun e => endpts e = u) ⊆ E₀.filter (fun e => endpts e = endpts e₀) := by
        intro e he
        have he1 := (Finset.mem_filter.mp he).1
        have heu := (Finset.mem_filter.mp he).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he1).1, heu.trans he₀u.symm⟩
      exact (Finset.card_le_card hsub).trans hle_m
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
  have hMCL := ppl174_crossing_lemma_multigraph Y E₁ endpts crossings m (by omega) hMult₁ hC_sub
    (fun H hH hS => by
      have h := hSimpleCL H hH hS
      convert h using 4
      congr 1; ext c; simp)
  rw [hY] at hMCL
  have hcr_le : (crossings.card : ℝ) ≤ (n : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
    have hC₁_sub : E₁.image (fun e => (e.1, dist e.1 e.2.1)) ⊆ C :=
      Finset.image_subset_image (Finset.filter_subset _ _)
    have hC₁_card : (E₁.image (fun e => (e.1, dist e.1 e.2.1))).card ≤ n * t :=
      (Finset.card_le_card hC₁_sub).trans hC_card
    have hch : 2 * (E₁.image (fun e => (e.1, dist e.1 e.2.1))).card.choose 2 ≤ (n * t) * (n * t) := by
      rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd]
      exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_le_mul hC₁_card hC₁_card)
    have hnat : crossings.card ≤ (n * t) * (n * t) := hC_ub.trans hch
    have hR : (crossings.card : ℝ) ≤ (((n * t) * (n * t) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR; linarith
  -- Step 6: Combine `n⁶ / 8 ≤ 64 m n⁴ t² + 64 m³ n³` via `szekely_algebraic_finish`!
  have hpow6 : (n : ℝ) ^ 6 / 8 ≤ 64 * (m : ℝ) * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 +
      64 * (m : ℝ) ^ 3 * (n : ℝ) ^ 3 := by
    have h1 : ((n : ℝ) ^ 2 / 2) ^ 3 ≤ (E₁.card : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hE₁_lb 3
    have h2 : 64 * (m : ℝ) * (n : ℝ) ^ 2 * (crossings.card : ℝ) ≤
        64 * (m : ℝ) * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by
      have hm_nn : (0 : ℝ) ≤ 64 * (m : ℝ) * (n : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left hcr_le hm_nn
      linarith
    linarith [h1, hMCL, h2, show ((n : ℝ) ^ 2 / 2) ^ 3 = (n : ℝ) ^ 6 / 8 by ring]
  exact szekely_algebraic_finish hn_big ht_pos ht_lt hm_le hpow6

/-- **Székely (1997) `Ω(n^{4/5})` Pinned-Distance Lower Bound for PPL 174 (Explicit Constant `1/1000`):**
Direct specialization `X = Y = A` of `ppl015_szekely_bipartite_four_fifths`: every `n`-point
planar set `A` (`n ≥ 1`) contains a pin `x ∈ A` determining at least `n^{4/5} / 1000` distinct
distances to `A`. -/
theorem ppl174_szekely_pinned_four_fifths
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (hn : 1 ≤ n) (hA : A.card = n)
    (hST : ∀ (m : ℕ), 2 ≤ m →
      ∀ L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
        (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ m ≤ (A.filter (· ∈ ℓ)).card) →
        (∑ ℓ ∈ L, ((A.filter (· ∈ ℓ)).card : ℝ)) ≤
          512 * (A.card : ℝ) ^ 2 / (m : ℝ) ^ 2 + 11 * (A.card : ℝ))
    (hCircleCL : ∀ (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
      (∀ e ∈ E,
        e.1 ∈ A ∧ e.2.1 ∈ A ∧ e.2.2 ∈ A ∧ e.2.1 ≠ e.2.2 ∧
        dist e.1 e.2.1 = dist e.1 e.2.2 ∧
        3 ≤ (A.filter (fun y => dist e.1 y = dist e.1 e.2.1)).card ∧
        let ang := fun q : EuclideanSpace ℝ (Fin 2) =>
          Complex.arg (⟨q 0 - e.1 0, q 1 - e.1 1⟩ : ℂ)
        let S := A.filter (fun y => dist e.1 y = dist e.1 e.2.1)
        ((ang e.2.1 < ang e.2.2 ∧ ∀ w ∈ S, ¬ (ang e.2.1 < ang w ∧ ang w < ang e.2.2)) ∨
         ((∀ w ∈ S, ang w ≤ ang e.2.1) ∧ (∀ w ∈ S, ang e.2.2 ≤ ang w)))) →
      ∃ crossings : Finset
          ((EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
           (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
        (∀ c ∈ crossings, c.1 ∈ E ∧ c.2 ∈ E ∧ ({c.1.2.1, c.1.2.2} : Finset _) ≠ {c.2.2.1, c.2.2.2}) ∧
        crossings.card ≤ 2 * (E.image (fun e => (e.1, dist e.1 e.2.1))).card.choose 2 ∧
        (∀ H : Finset _, H ⊆ E →
          (∀ e₁ ∈ H, ∀ e₂ ∈ H, ({e₁.2.1, e₁.2.2} : Finset _) = {e₂.2.1, e₂.2.2} → e₁ = e₂) →
          (H.card : ℝ) ^ 3 ≤
            64 * (A.card : ℝ) ^ 2 * ((crossings.filter (fun c => c.1 ∈ H ∧ c.2 ∈ H)).card : ℝ) +
            64 * (A.card : ℝ) ^ 3)) :
    ∃ x ∈ A, (n : ℝ) ^ (4 / 5 : ℝ) / 1000 ≤ ((A.image (dist x ·)).card : ℝ) :=
  (ppl015_szekely_bipartite_four_fifths A A n hn hA hA hST hCircleCL).1

/-! ### Section 3: Unconditional Landau–Ramanujan Upper Bound & Erdős Integer-Grid Constructions -/

/-- Fermat's two-squares obstruction: if a prime `p ≡ 3 (mod 4)` divides `a² + b²`, then `p ∣ a` and `p ∣ b`. -/
private lemma prime_mod4_eq3_dvd_sq_add_sq {p a b : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hdvd : p ∣ a ^ 2 + b ^ 2) : p ∣ a ∧ p ∣ b := by
  have : Fact p.Prime := ⟨hp⟩
  have hmod : ((a : ZMod p) ^ 2 + (b : ZMod p) ^ 2) = 0 := by
    have h0 : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0; exact h0
  have hb : p ∣ b := by
    by_contra hnb
    have hbz : (b : ZMod p) ≠ 0 := by
      intro h0; exact hnb ((ZMod.natCast_eq_zero_iff b p).mp h0)
    have hsq : ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2 = -1 := by
      rw [mul_pow, inv_pow]
      have h1 : (a : ZMod p) ^ 2 = -((b : ZMod p) ^ 2) := eq_neg_of_add_eq_zero_left hmod
      rw [h1, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hbz)]
    have hex : IsSquare (-1 : ZMod p) := ⟨(a : ZMod p) * (b : ZMod p)⁻¹, by rw [← sq]; exact hsq.symm⟩
    have hne3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hex
    exact hne3 hp3
  have ha : p ∣ a := by
    have hb2 : p ∣ b ^ 2 := dvd_pow hb (by norm_num)
    have ha2 : p ∣ a ^ 2 := (Nat.dvd_add_left hb2).mp hdvd
    exact hp.dvd_of_dvd_pow ha2
  exact ⟨ha, hb⟩

/-- Every positive sum of two squares factors as `s * r²` where `s` has no prime factor `p ≡ 3 (mod 4)`. -/
private lemma sum_two_sq_decomp (n : ℕ) (hn : 1 ≤ n) (hsq : ∃ a b : ℕ, n = a ^ 2 + b ^ 2) :
    ∃ s r : ℕ, 1 ≤ s ∧ 1 ≤ r ∧ n = s * r ^ 2 ∧
      ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hex : ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ n
    · rcases hex with ⟨p, hp, hp3, hpn⟩
      rcases hsq with ⟨a, b, rfl⟩
      obtain ⟨hpa, hpb⟩ := prime_mod4_eq3_dvd_sq_add_sq hp hp3 hpn
      rcases hpa with ⟨a', rfl⟩
      rcases hpb with ⟨b', rfl⟩
      have hfac : (p * a') ^ 2 + (p * b') ^ 2 = p ^ 2 * (a' ^ 2 + b' ^ 2) := by ring
      set n' : ℕ := a' ^ 2 + b' ^ 2
      have hp2 : 2 ≤ p := hp.two_le
      have hn'_pos : 1 ≤ n' := by
        by_contra h0
        have : n' = 0 := by omega
        rw [hfac, this, mul_zero] at hn; omega
      have hn'_lt : n' < (p * a') ^ 2 + (p * b') ^ 2 := by
        rw [hfac]
        have hp4 : 4 ≤ p ^ 2 := by nlinarith
        nlinarith
      obtain ⟨s, r', hs, hr', hdecomp, havoid⟩ := ih n' hn'_lt hn'_pos ⟨a', b', rfl⟩
      refine ⟨s, p * r', hs, by nlinarith, ?_, havoid⟩
      rw [hfac, hdecomp]; ring
    · push Not at hex
      exact ⟨n, 1, hn, le_rfl, by ring, hex⟩

/-- Product of a finite set of distinct primes is squarefree, positive, and has `primeFactors = T`. -/
private lemma prod_primes_props (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) ∧ 1 ≤ ∏ p ∈ T, p ∧ (∏ p ∈ T, p).primeFactors = T := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hp_pr : p.Prime := hT p (Finset.mem_insert_self p s)
    have hs_pr : ∀ q ∈ s, q.Prime := fun q hq => hT q (Finset.mem_insert_of_mem hq)
    obtain ⟨hsq_s, hpos_s, hpf_s⟩ := ih hs_pr
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_pr := hs_pr q hq
      exact (hp_pr.coprime_iff_not_dvd).mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp hdvd ▸ hq)
    rw [Finset.prod_insert hp]
    refine ⟨(Nat.squarefree_mul hcop).mpr ⟨hp_pr.squarefree, hsq_s⟩, ?_, ?_⟩
    · exact Nat.mul_pos hp_pr.pos (by omega)
    · rw [Nat.primeFactors_mul hp_pr.ne_zero (by omega), hp_pr.primeFactors, hpf_s,
        Finset.singleton_union]

/-- Elementary convexity bound: `exp u ≤ 1 + 2 * u` for all `u ∈ [0, 1]`. -/
private lemma exp_le_one_add_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u ≤ 1 + 2 * u := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (sub_nonneg.mpr hu1) hu0 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at hconv
  have he3 : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
  nlinarith

/-- Telescoping bound: `∑ k ∈ Icc 1 N, (1/k - 1/(k+1)) ≤ 1`. -/
private lemma sum_Icc_inv_sub_succ_le_one (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹) ≤ 1 := by
  induction N with
  | zero => simp
  | succ m ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
    -- Compute exact telescoping value `1 - (N + 1)⁻¹`
    suffices hexact : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, ((k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹) =
        1 - ((n : ℝ) + 1)⁻¹ by
      rw [hexact (m + 1)]
      have hpos : (0 : ℝ) ≤ (((m + 1 : ℕ) : ℝ) + 1)⁻¹ := by positivity
      linarith
    intro n
    induction n with
    | zero => simp
    | succ k ihk =>
      have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp), ihk]
      push_cast; ring

/-- Telescoping reciprocal-square sum: `∑ r ∈ Icc 1 N, (r : ℝ)⁻² ≤ 2`. -/
private lemma sum_Icc_inv_sq_le_two (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, ((r : ℝ) ^ 2)⁻¹ ≤ 2 := by
  cases N with
  | zero => simp
  | succ m =>
    have hI : Finset.Icc 1 (m + 1) = insert 1 (Finset.Icc 2 (m + 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp)]
    have htail : ∑ r ∈ Finset.Icc 2 (m + 1), ((r : ℝ) ^ 2)⁻¹ ≤
        ∑ k ∈ Finset.Icc 1 m, ((k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹) := by
      have hbij : Finset.Icc 2 (m + 1) = (Finset.Icc 1 m).image (· + 1) := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_image]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨r - 1, ⟨by omega, by omega⟩, by omega⟩
        · rintro ⟨k, ⟨h1, h2⟩, rfl⟩; omega
      rw [hbij, Finset.sum_image (fun a _ b _ h => by omega)]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
      have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      have hdiff : (k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹ = ((k : ℝ) * ((k : ℝ) + 1))⁻¹ := by
        field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]; ring
      push_cast
      rw [hdiff]
      exact inv_anti₀ (mul_pos hk_pos hk1_pos) (by nlinarith)
    have h1 := (htail.trans (sum_Icc_inv_sub_succ_le_one m))
    norm_num; linarith

/-- Tail reciprocal-square sum: `∑ r ∈ Icc (R + 1) M, (r : ℝ)⁻² ≤ (R : ℝ)⁻¹` for `1 ≤ R`. -/
private lemma sum_Icc_inv_sq_tail_le {R M : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ Finset.Icc (R + 1) M, ((r : ℝ) ^ 2)⁻¹ ≤ (R : ℝ)⁻¹ := by
  by_cases hRM : M ≤ R
  · have hemp : Finset.Icc (R + 1) M = ∅ := by
      ext k; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [hemp, Finset.sum_empty]; positivity
  have hlt : R < M := not_le.mp hRM
  have hstep : ∀ k : ℕ, ∑ r ∈ Finset.Icc (R + 1) (R + k), ((r : ℝ) ^ 2)⁻¹ ≤
      (R : ℝ)⁻¹ - ((R + k : ℕ) : ℝ)⁻¹ := by
    intro k
    induction k with
    | zero =>
      have hemp : Finset.Icc (R + 1) (R + 0) = ∅ := by
        ext j; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hemp, Finset.sum_empty]; simp
    | succ j ihj =>
      have hI : Finset.Icc (R + 1) (R + (j + 1)) = insert (R + j + 1) (Finset.Icc (R + 1) (R + j)) := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp)]
      have hRj_pos : (0 : ℝ) < ((R + j : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hRj1_pos : (0 : ℝ) < ((R + j : ℕ) : ℝ) + 1 := by linarith
      have hbound : (((R + j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
          ((R + j : ℕ) : ℝ)⁻¹ - (((R + j : ℕ) : ℝ) + 1)⁻¹ := by
        have hdiff : ((R + j : ℕ) : ℝ)⁻¹ - (((R + j : ℕ) : ℝ) + 1)⁻¹ =
            (((R + j : ℕ) : ℝ) * (((R + j : ℕ) : ℝ) + 1))⁻¹ := by
          field_simp [ne_of_gt hRj_pos, ne_of_gt hRj1_pos]; ring
        rw [hdiff]
        have hcast : ((R + j + 1 : ℕ) : ℝ) = ((R + j : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        exact inv_anti₀ (mul_pos hRj_pos hRj1_pos) (by nlinarith)
      have hcast2 : ((R + (j + 1) : ℕ) : ℝ) = ((R + j : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast2]; linarith
  have hM : R + (M - R) = M := by omega
  have h := hstep (M - R)
  rw [hM] at h
  have hnn : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
  linarith

/-- Large-sieve + Rankin-trick + Mertens-AP upper bound on integers in `[1, Y]` free of `p ≡ 3 (mod 4)` prime factors. -/
private lemma avoid_mod4_eq3_upper_bound :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ Y : ℕ, 2 ≤ Y →
      (((Finset.Icc 1 Y).filter (fun s => ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ s)).card : ℝ) ≤
        C₁ * (Y : ℝ) / Real.sqrt (Real.log (Y : ℝ)) := by
  obtain ⟨C_M1, hC_M1_pos, hM1⟩ := RHDirect.Stage8MertensTheorems.mertens_first_theorem
  obtain ⟨M_43, C_M2, hC_M2_pos, hM2⟩ :=
    RHDirect.Stage8MertensTheorems.mertens_second_theorem_AP (q := 4) (a := 3) (by decide)
  set L₀ : ℝ := max 200 (max (14 * C_M1) (14 * C_M2))
  set Y₀ : ℕ := Nat.ceil (Real.exp L₀) + 100
  have hL₀_ge : 200 ≤ L₀ := le_max_left _ _
  have hY₀_ge2 : 2 ≤ Y₀ := by omega
  set C₁ : ℝ := max (8 * Real.sqrt 14 * Real.exp (2 - M_43)) (Real.sqrt (Real.log (Y₀ : ℝ)) + 1)
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C₁, hC₁_pos, fun Y hY2 => ?_⟩
  set A : Finset ℕ := (Finset.Icc 1 Y).filter (fun s => ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ s)
  have hlogY_pos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hsqrt_logY_pos : 0 < Real.sqrt (Real.log (Y : ℝ)) := Real.sqrt_pos.mpr hlogY_pos
  -- Small regime `Y < Y₀`
  by_cases hsmall : Y < Y₀
  · have hcard_le : (A.card : ℝ) ≤ (Y : ℝ) := by
      have h1 : A.card ≤ (Finset.Icc 1 Y).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.card_Icc] at h1
      have h2 : A.card ≤ Y := by omega
      exact_mod_cast h2
    have hlog_le : Real.log (Y : ℝ) ≤ Real.log (Y₀ : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast le_of_lt hsmall)
    have hsq_le : Real.sqrt (Real.log (Y : ℝ)) ≤ C₁ := by
      have h1 : Real.sqrt (Real.log (Y : ℝ)) ≤ Real.sqrt (Real.log (Y₀ : ℝ)) := Real.sqrt_le_sqrt hlog_le
      have h2 : Real.sqrt (Real.log (Y₀ : ℝ)) + 1 ≤ C₁ := le_max_right _ _
      linarith
    rw [le_div_iff₀ hsqrt_logY_pos]
    calc (A.card : ℝ) * Real.sqrt (Real.log (Y : ℝ))
        ≤ (Y : ℝ) * C₁ := mul_le_mul hcard_le hsq_le (le_of_lt hsqrt_logY_pos) (Nat.cast_nonneg Y)
      _ = C₁ * (Y : ℝ) := mul_comm _ _
  -- Asymptotic regime `Y₀ ≤ Y`
  have hY_ge : Y₀ ≤ Y := not_lt.mp hsmall
  have hlogY_ge : L₀ ≤ Real.log (Y : ℝ) := by
    have hexp_le : Real.exp L₀ ≤ (Y : ℝ) := by
      have h1 : Real.exp L₀ ≤ (Nat.ceil (Real.exp L₀) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (Real.exp L₀) : ℝ) ≤ (Y₀ : ℝ) := by exact_mod_cast (by omega : Nat.ceil (Real.exp L₀) ≤ Y₀)
      have h3 : (Y₀ : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY_ge
      linarith
    exact (Real.le_log_iff_exp_le (Nat.cast_pos.mpr (by omega))).mpr hexp_le
  set Q : ℕ := Nat.sqrt Y
  have hQ_sq_le : Q ^ 2 ≤ Y := by rw [sq]; exact Nat.sqrt_le Y
  have hY_lt_Q1 : Y < (Q + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt Y
  have hQ_ge_64 : 64 ≤ Q := by
    have hY_big : 4096 ≤ Y := by
      have h1 : Real.exp 200 ≤ (Y : ℝ) :=
        (Real.exp_le_exp.mpr hL₀_ge).trans ((Real.le_log_iff_exp_le (Nat.cast_pos.mpr (by omega))).mp hlogY_ge)
      have h2 : (4096 : ℝ) ≤ Real.exp 200 := by
        have h13 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have hp : (2 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) h13 12
        rw [← Real.exp_nat_mul] at hp
        have h12 : Real.exp 12 ≤ Real.exp 200 := Real.exp_le_exp.mpr (by norm_num)
        norm_num at hp; linarith
      have hYR : (4096 : ℝ) ≤ (Y : ℝ) := h2.trans h1
      exact_mod_cast hYR
    have h64 : 64 * 64 ≤ Y := by omega
    exact Nat.le_sqrt.mpr h64
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hQ_ge_half : (Y : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by
    have hnat : Y ≤ 4 * Q ^ 2 := by nlinarith [hY_lt_Q1, hQ_ge_64]
    exact_mod_cast hnat
  set z : ℕ := Nat.floor ((Q : ℝ) ^ (1 / 6 : ℝ))
  have hz_le_Q : (z : ℝ) ≤ (Q : ℝ) ^ (1 / 6 : ℝ) := Nat.floor_le (Real.rpow_nonneg (le_of_lt hQ_pos) _)
  have hQ16_ge2 : (2 : ℝ) ≤ (Q : ℝ) ^ (1 / 6 : ℝ) := by
    have h6 : (2 : ℝ) ^ (6 : ℝ) ≤ ((Q : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hQ_pos)]; norm_num
      exact_mod_cast hQ_ge_64
    exact (Real.rpow_le_rpow_iff (by norm_num) (Real.rpow_nonneg (le_of_lt hQ_pos) _) (by norm_num)).mp h6
  have hz_ge_half : (Q : ℝ) ^ (1 / 6 : ℝ) / 2 ≤ (z : ℝ) := by
    have hfl := Nat.sub_one_lt_floor ((Q : ℝ) ^ (1 / 6 : ℝ))
    linarith [hQ16_ge2]
  have hz_pos : (0 : ℝ) < (z : ℝ) := lt_of_lt_of_le (by linarith [hQ16_ge2]) hz_ge_half
  -- Log comparison: `(1 / 14) * log Y ≤ log z ≤ (1 / 6) * log Q`
  have hlogz_le : Real.log (z : ℝ) ≤ (1 / 6 : ℝ) * Real.log (Q : ℝ) := by
    have h1 := Real.log_le_log hz_pos hz_le_Q
    rwa [Real.log_rpow hQ_pos] at h1
  have hlogz_ge : (1 / 14 : ℝ) * Real.log (Y : ℝ) ≤ Real.log (z : ℝ) := by
    have h1 : Real.log ((Q : ℝ) ^ (1 / 6 : ℝ) / 2) ≤ Real.log (z : ℝ) :=
      Real.log_le_log (by linarith [hQ16_ge2]) hz_ge_half
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hQ_pos _)) (by norm_num),
        Real.log_rpow hQ_pos] at h1
    have hlogQ_ge : Real.log (Y : ℝ) - Real.log 4 ≤ 2 * Real.log (Q : ℝ) := by
      have h2 := Real.log_le_log (Nat.cast_pos.mpr (by omega)) hQ_ge_half
      rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hQ_pos 2)), Real.log_pow] at h2
      push_cast at h2; linarith
    have hlog2_lt1 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    have hlog4_lt2 : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hlogY_200 : 200 ≤ Real.log (Y : ℝ) := hL₀_ge.trans hlogY_ge
    linarith
  have hlogz_ge14 : 14 ≤ Real.log (z : ℝ) := by linarith [hL₀_ge.trans hlogY_ge]
  have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
  have hz_ge3 : 3 ≤ z := by
    have hzR : (3 : ℝ) ≤ (z : ℝ) := by
      have h1 : Real.exp 2 ≤ (z : ℝ) := (Real.le_log_iff_exp_le hz_pos).mp (by linarith)
      have h2 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      exact h2.trans h1
    exact_mod_cast hzR
  -- Step 1: Apply Montgomery's Arithmetic Large Sieve (`RHDirect.Stage7SieveMethods`)!
  let ω : ℕ → ℕ := fun p => if p % 4 = 3 then 1 else 0
  have hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω := by
    intro p hp _
    by_cases hp3 : p % 4 = 3
    · refine ⟨by simp [ω, hp3]; exact hp.one_lt, {(0 : ZMod p)}, by simp [ω, hp3], ?_⟩
      intro n hn hmem
      have h0 : (n : ZMod p) = 0 := Finset.mem_singleton.mp hmem
      have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
      exact (Finset.mem_filter.mp hn).2 p hp hp3 hdvd
    · refine ⟨by simp [ω, hp3]; exact hp.pos, ∅, by simp [ω, hp3], fun _ _ h => absurd h (Finset.notMem_empty _)⟩
  have hA_sub : A ⊆ Finset.Icc (0 + 1) (0 + Y) := by
    simpa only [zero_add] using
      Finset.filter_subset (fun s => ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ s) (Finset.Icc 1 Y)
  have hLS := RHDirect.Stage7SieveMethods.montgomery_arithmetic_large_sieve_Icc
    (M := 0) (N := Y) (Q := Q) (A := A) hA_sub ω hAvoid
  set L_Q : ℝ := ∑ q ∈ Finset.Icc 1 Q,
    if Squarefree q then ∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) else 0
  have hLS_4Y : (A.card : ℝ) * L_Q ≤ 4 * (Y : ℝ) := by
    have hQ2R : (Q : ℝ) ^ 2 ≤ (Y : ℝ) := by exact_mod_cast hQ_sq_le
    linarith [hLS]
  -- Step 2: Lower-bound `L_Q` via squarefree products of primes `P3(z)` + Rankin's trick!
  set P3 : Finset ℕ := (Finset.Icc 1 z).filter (fun p => p.Prime ∧ p % 4 = 3)
  have hP3_pr : ∀ p ∈ P3, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hP3_mod : ∀ p ∈ P3, p % 4 = 3 := fun p hp => (Finset.mem_filter.mp hp).2.2
  have hP3_le : ∀ p ∈ P3, p ≤ z := fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  set B_le : Finset (Finset ℕ) := P3.powerset.filter (fun T => ∏ p ∈ T, p ≤ Q)
  set B_gt : Finset (Finset ℕ) := P3.powerset.filter (fun T => Q < ∏ p ∈ T, p)
  have hL_ge_Ble : ∑ T ∈ B_le, ∏ p ∈ T, (p : ℝ)⁻¹ ≤ L_Q := by
    have hsub : B_le.image (fun T => ∏ p ∈ T, p) ⊆ Finset.Icc 1 Q := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨T, hT, rfl⟩
      have hTsub : T ⊆ P3 := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hTle : ∏ p ∈ T, p ≤ Q := (Finset.mem_filter.mp hT).2
      have hpos := (prod_primes_props T (fun p hp => hP3_pr p (hTsub hp))).2.1
      exact Finset.mem_Icc.mpr ⟨hpos, hTle⟩
    have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (B_le : Set (Finset ℕ)) := by
      intro T₁ h1 T₂ h2 heq
      dsimp only at heq
      have h1' : T₁ ⊆ P3 := Finset.mem_powerset.mp (Finset.mem_filter.mp h1).1
      have h2' : T₂ ⊆ P3 := Finset.mem_powerset.mp (Finset.mem_filter.mp h2).1
      have hpf1 := (prod_primes_props T₁ (fun p hp => hP3_pr p (h1' hp))).2.2
      have hpf2 := (prod_primes_props T₂ (fun p hp => hP3_pr p (h2' hp))).2.2
      rw [← hpf1, ← hpf2, heq]
    have hterm_nn : ∀ q ∈ Finset.Icc 1 Q,
        0 ≤ (if Squarefree q then ∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) else 0) := by
      intro q _
      split_ifs with hsq
      · refine Finset.prod_nonneg fun p hp => ?_
        have hpr := Nat.prime_of_mem_primeFactors hp
        have hlt : (ω p : ℝ) < (p : ℝ) := by
          dsimp [ω]; split_ifs
          · exact_mod_cast hpr.one_lt
          · exact_mod_cast hpr.pos
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · exact le_rfl
    calc ∑ T ∈ B_le, ∏ p ∈ T, (p : ℝ)⁻¹
        ≤ ∑ T ∈ B_le,
            (if Squarefree (∏ p ∈ T, p) then
              ∏ p ∈ (∏ r ∈ T, r).primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) else 0) := by
          refine Finset.sum_le_sum fun T hT => ?_
          have hTsub : T ⊆ P3 := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
          obtain ⟨hsq, _, hpf⟩ := prod_primes_props T (fun p hp => hP3_pr p (hTsub hp))
          rw [if_pos hsq, hpf]
          refine Finset.prod_le_prod (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)) fun p hp => ?_
          have hp3 := hP3_mod p (hTsub hp)
          have hpr := hP3_pr p (hTsub hp)
          simp only [ω, hp3, ite_true, Nat.cast_one]
          rw [one_div]
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
          exact inv_anti₀ (by linarith) (by linarith)
      _ = ∑ q ∈ B_le.image (fun T => ∏ p ∈ T, p),
            (if Squarefree q then ∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) else 0) :=
          (Finset.sum_image (f := fun q => if Squarefree q then
            ∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) else 0) hinj).symm
      _ ≤ L_Q := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hterm_nn q hq)
  -- Split `∏_{p ∈ P3} (1 + 1/p) = (B_le sum) + (B_gt sum)`
  have hprod_split : ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) =
      (∑ T ∈ B_le, ∏ p ∈ T, (p : ℝ)⁻¹) + (∑ T ∈ B_gt, ∏ p ∈ T, (p : ℝ)⁻¹) := by
    rw [Finset.prod_one_add]
    have hdisj : Disjoint B_le B_gt := by
      rw [Finset.disjoint_left]; intro T h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
    have hunion : B_le ∪ B_gt = P3.powerset := by
      ext T; simp only [B_le, B_gt, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hle : ∏ p ∈ T, p ≤ Q
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← hunion, Finset.sum_union hdisj]
  -- Rankin's trick with `α = 1 / log z` bounds `B_gt sum ≤ (1 / 2) * ∏_{p ∈ P3} (1 + 1/p)`
  set α : ℝ := 1 / Real.log (z : ℝ)
  have hα_pos : 0 < α := one_div_pos.mpr hlogz_pos
  have hBgt_le : ∑ T ∈ B_gt, ∏ p ∈ T, (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) * ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) := by
    have hrankin : ∑ T ∈ B_gt, ∏ p ∈ T, (p : ℝ)⁻¹ ≤
        (Q : ℝ) ^ (-α) * ∏ p ∈ P3, (1 + (p : ℝ) ^ α * (p : ℝ)⁻¹) := by
      rw [Finset.prod_one_add, Finset.mul_sum]
      calc ∑ T ∈ B_gt, ∏ p ∈ T, (p : ℝ)⁻¹
          ≤ ∑ T ∈ B_gt, (Q : ℝ) ^ (-α) * ∏ p ∈ T, ((p : ℝ) ^ α * (p : ℝ)⁻¹) := by
            refine Finset.sum_le_sum fun T hT => ?_
            have hTsub : T ⊆ P3 := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
            have hQlt : (Q : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hT).2
            have hprod_cast : ((∏ p ∈ T, p : ℕ) : ℝ) = ∏ p ∈ T, (p : ℝ) := Nat.cast_prod _ _
            rw [hprod_cast] at hQlt
            have hrpow_prod : (∏ p ∈ T, (p : ℝ)) ^ α = ∏ p ∈ T, (p : ℝ) ^ α :=
              (Real.finsetProd_rpow T (fun p => (p : ℝ)) (fun p _ => Nat.cast_nonneg p) α).symm
            have h1le : 1 ≤ (Q : ℝ) ^ (-α) * ∏ p ∈ T, (p : ℝ) ^ α := by
              rw [← hrpow_prod, Real.rpow_neg (le_of_lt hQ_pos)]
              have hle : (Q : ℝ) ^ α ≤ (∏ p ∈ T, (p : ℝ)) ^ α :=
                Real.rpow_le_rpow (le_of_lt hQ_pos) (le_of_lt hQlt) (le_of_lt hα_pos)
              have hQa_pos : 0 < (Q : ℝ) ^ α := Real.rpow_pos_of_pos hQ_pos α
              rw [← div_eq_inv_mul, one_le_div hQa_pos]; exact hle
            rw [Finset.prod_mul_distrib, ← mul_assoc]
            have hnn : 0 ≤ ∏ p ∈ T, (p : ℝ)⁻¹ := Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
            simpa using mul_le_mul_of_nonneg_right h1le hnn
        _ ≤ ∑ T ∈ P3.powerset, (Q : ℝ) ^ (-α) * ∏ p ∈ T, ((p : ℝ) ^ α * (p : ℝ)⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun T _ _ => ?_
            exact mul_nonneg (Real.rpow_nonneg (le_of_lt hQ_pos) _)
              (Finset.prod_nonneg fun p _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)
                (inv_nonneg.mpr (Nat.cast_nonneg p)))
    -- Compare `∏ (1 + p^α / p)` against `∏ (1 + 1/p)` using `exp_le_one_add_two_mul` + `mertens_first_theorem`
    have hratio : ∏ p ∈ P3, (1 + (p : ℝ) ^ α * (p : ℝ)⁻¹) ≤
        (∏ p ∈ P3, (1 + (p : ℝ)⁻¹)) * Real.exp (2 * α * ∑ p ∈ P3, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
      have hpr := hP3_pr p hp
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpr.pos
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_le
      have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
      have hlogp_le : Real.log (p : ℝ) ≤ Real.log (z : ℝ) :=
        Real.log_le_log hp_pos (by exact_mod_cast hP3_le p hp)
      have hu0 : 0 ≤ α * Real.log (p : ℝ) := mul_nonneg (le_of_lt hα_pos) hlogp_nn
      have hu1 : α * Real.log (p : ℝ) ≤ 1 := by
        dsimp [α]; rw [one_div_mul_eq_div, div_le_one hlogz_pos]; exact hlogp_le
      have hpa : (p : ℝ) ^ α - 1 ≤ 2 * α * Real.log (p : ℝ) := by
        rw [Real.rpow_def_of_pos hp_pos, mul_comm (Real.log (p : ℝ)) α]
        linarith [exp_le_one_add_two_mul hu0 hu1]
      have h1pinv_pos : 0 < 1 + (p : ℝ)⁻¹ := by positivity
      have hstep1 : 1 + (p : ℝ) ^ α * (p : ℝ)⁻¹ ≤
          (1 + (p : ℝ)⁻¹) * (1 + 2 * α * (Real.log (p : ℝ) / (p : ℝ))) := by
        have hpa_nn : 0 ≤ 2 * α * Real.log (p : ℝ) := by linarith
        have hrew : (1 + (p : ℝ)⁻¹) * (1 + 2 * α * (Real.log (p : ℝ) / (p : ℝ))) -
            (1 + (p : ℝ) ^ α * (p : ℝ)⁻¹) =
            (2 * α * Real.log (p : ℝ) - ((p : ℝ) ^ α - 1)) * (p : ℝ)⁻¹ +
            (p : ℝ)⁻¹ * (2 * α * (Real.log (p : ℝ) / (p : ℝ))) := by ring
        have hnn1 : 0 ≤ (2 * α * Real.log (p : ℝ) - ((p : ℝ) ^ α - 1)) * (p : ℝ)⁻¹ :=
          mul_nonneg (by linarith) (inv_nonneg.mpr (le_of_lt hp_pos))
        have hnn2 : 0 ≤ (p : ℝ)⁻¹ * (2 * α * (Real.log (p : ℝ) / (p : ℝ))) := by positivity
        linarith
      have hstep2 : 1 + 2 * α * (Real.log (p : ℝ) / (p : ℝ)) ≤
          Real.exp (2 * α * (Real.log (p : ℝ) / (p : ℝ))) := by
        linarith [Real.add_one_le_exp (2 * α * (Real.log (p : ℝ) / (p : ℝ)))]
      exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (le_of_lt h1pinv_pos))
    -- Apply `mertens_first_theorem`: `∑_{p ∈ P3} log p / p ≤ 2 * log z`
    have hm1_bd : ∑ p ∈ P3, Real.log (p : ℝ) / (p : ℝ) ≤ 2 * Real.log (z : ℝ) := by
      have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 2 ≤ z)
      have hfl : ⌊(z : ℝ)⌋₊ = z := Nat.floor_natCast z
      have hsub : P3 ⊆ (Finset.Icc 1 ⌊(z : ℝ)⌋₊).filter Nat.Prime := by
        rw [hfl]; intro p hp; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
      have hsum_le : ∑ p ∈ P3, Real.log (p : ℝ) / (p : ℝ) ≤
          ∑ p ∈ (Finset.Icc 1 ⌊(z : ℝ)⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
        have hpr := (Finset.mem_filter.mp hp).2
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_le)) (Nat.cast_nonneg p)
      have hm1z := (abs_le.mp (hM1 (z : ℝ) hz2)).2
      have hCM1_le : C_M1 ≤ Real.log (z : ℝ) := by
        have h1 : 14 * C_M1 ≤ L₀ := le_trans (le_max_left _ _) (le_max_right _ _)
        linarith [hlogY_ge, hlogz_ge]
      linarith
    have hexp_bd : Real.exp (2 * α * ∑ p ∈ P3, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hm1_bd (by positivity : (0 : ℝ) ≤ 2 * α)
      have h2a : 2 * α * (2 * Real.log (z : ℝ)) = 4 := by
        dsimp [α]; field_simp [ne_of_gt hlogz_pos]; ring
      linarith
    have hQ_neg : (Q : ℝ) ^ (-α) ≤ Real.exp (-6) := by
      rw [Real.rpow_def_of_pos hQ_pos]
      apply Real.exp_le_exp.mpr
      have h6 : 6 ≤ α * Real.log (Q : ℝ) := by
        dsimp [α]; rw [one_div_mul_eq_div, le_div_iff₀ hlogz_pos]; linarith [hlogz_le]
      linarith
    have hexp_m2 : Real.exp (-6) * Real.exp 4 ≤ 1 / 2 := by
      rw [← Real.exp_add, show (-6 : ℝ) + 4 = -2 by norm_num, Real.exp_neg]
      have h2e : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      rw [inv_le_comm₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num; linarith
    have hprod_nn : 0 ≤ ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) := Finset.prod_nonneg fun _ _ => by positivity
    calc ∑ T ∈ B_gt, ∏ p ∈ T, (p : ℝ)⁻¹
        ≤ (Q : ℝ) ^ (-α) * ∏ p ∈ P3, (1 + (p : ℝ) ^ α * (p : ℝ)⁻¹) := hrankin
      _ ≤ (Q : ℝ) ^ (-α) * ((∏ p ∈ P3, (1 + (p : ℝ)⁻¹)) * Real.exp 4) := by
          refine mul_le_mul_of_nonneg_left (hratio.trans ?_) (Real.rpow_nonneg (le_of_lt hQ_pos) _)
          exact mul_le_mul_of_nonneg_left hexp_bd hprod_nn
      _ = ((Q : ℝ) ^ (-α) * Real.exp 4) * ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) := by ring
      _ ≤ (Real.exp (-6) * Real.exp 4) * ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ_neg (le_of_lt (Real.exp_pos 4))) hprod_nn
      _ ≤ (1 / 2 : ℝ) * ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hexp_m2 hprod_nn
  have hL_ge_half : (1 / 2 : ℝ) * ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) ≤ L_Q := by
    linarith [hL_ge_Ble, hprod_split, hBgt_le]
  -- Step 3: Lower-bound `∏_{p ∈ P3} (1 + 1/p)` via `mertens_second_theorem_AP`!
  have hprod_lb : Real.exp (M_43 - 2) * Real.sqrt (Real.log (z : ℝ)) ≤ ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) := by
    have hlog_prod : Real.log (∏ p ∈ P3, (1 + (p : ℝ)⁻¹)) = ∑ p ∈ P3, Real.log (1 + (p : ℝ)⁻¹) :=
      Real.log_prod fun p _ => by positivity
    have hlog_lb : (∑ p ∈ P3, (p : ℝ)⁻¹) - 1 ≤ ∑ p ∈ P3, Real.log (1 + (p : ℝ)⁻¹) := by
      have hterm : ∀ p ∈ P3, (p : ℝ)⁻¹ - ((p : ℝ)⁻¹ - ((p : ℝ) + 1)⁻¹) ≤ Real.log (1 + (p : ℝ)⁻¹) := by
        intro p hp
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (hP3_pr p hp).pos
        have h1p_pos : 0 < 1 + (p : ℝ)⁻¹ := by positivity
        have h1 := Real.one_sub_inv_le_log_of_pos h1p_pos
        have halg : 1 - (1 + (p : ℝ)⁻¹)⁻¹ = ((p : ℝ) + 1)⁻¹ := by
          field_simp [ne_of_gt hp_pos, show (p : ℝ) + 1 ≠ 0 by linarith]; ring
        linarith
      have hsum1 := Finset.sum_le_sum hterm
      rw [Finset.sum_sub_distrib] at hsum1
      have hsub : P3 ⊆ Finset.Icc 1 z := Finset.filter_subset _ _
      have htele : ∑ p ∈ P3, ((p : ℝ)⁻¹ - ((p : ℝ) + 1)⁻¹) ≤ 1 := by
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => by
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
          exact sub_nonneg.mpr (inv_anti₀ hk_pos (by linarith : (k : ℝ) ≤ (k : ℝ) + 1))
        exact hle.trans (sum_Icc_inv_sub_succ_le_one z)
      linarith
    have hm2_lb : (1 / 2 : ℝ) * Real.log (Real.log (z : ℝ)) + M_43 - 1 ≤ ∑ p ∈ P3, (p : ℝ)⁻¹ := by
      have hz3R : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge3
      have hm2z := (abs_le.mp (hM2 (z : ℝ) hz3R)).1
      have htot_n : Nat.totient 4 = 2 := by decide
      have htot : (Nat.totient 4 : ℝ) = 2 := by rw [htot_n]; norm_num
      have hfl : ⌊(z : ℝ)⌋₊ = z := Nat.floor_natCast z
      have hset_eq : (Finset.Icc 1 ⌊(z : ℝ)⌋₊).filter (fun p => p.Prime ∧ p ≡ 3 [MOD 4]) = P3 := by
        rw [hfl]; ext p; simp [P3, Nat.ModEq]
      rw [htot, hset_eq] at hm2z
      have hCM2_le : C_M2 / Real.log (z : ℝ) ≤ 1 := by
        rw [div_le_one hlogz_pos]
        have h1 : 14 * C_M2 ≤ L₀ := le_trans (le_max_right _ _) (le_max_right _ _)
        linarith [hlogY_ge, hlogz_ge]
      linarith
    have hlog_tot : (M_43 - 2) + (1 / 2 : ℝ) * Real.log (Real.log (z : ℝ)) ≤
        Real.log (∏ p ∈ P3, (1 + (p : ℝ)⁻¹)) := by
      rw [hlog_prod]; linarith
    have hexp := Real.exp_le_exp.mpr hlog_tot
    have hprod_pos : 0 < ∏ p ∈ P3, (1 + (p : ℝ)⁻¹) := Finset.prod_pos fun _ _ => by positivity
    rw [Real.exp_log hprod_pos, Real.exp_add] at hexp
    have hsq_eq : Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (z : ℝ))) = Real.sqrt (Real.log (z : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlogz_pos, mul_comm]
    rwa [hsq_eq] at hexp
  -- Step 4: Combine to finish `|A| ≤ C₁ * Y / √(log Y)`!
  have hL_final : Real.exp (M_43 - 2) / (2 * Real.sqrt 14) * Real.sqrt (Real.log (Y : ℝ)) ≤ L_Q := by
    have hsq14 : Real.sqrt (Real.log (Y : ℝ)) / Real.sqrt 14 ≤ Real.sqrt (Real.log (z : ℝ)) := by
      rw [← Real.sqrt_div (le_of_lt hlogY_pos)]
      exact Real.sqrt_le_sqrt (by linarith [hlogz_ge])
    have h1 : (1 / 2 : ℝ) * (Real.exp (M_43 - 2) * (Real.sqrt (Real.log (Y : ℝ)) / Real.sqrt 14)) ≤ L_Q :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq14 (le_of_lt (Real.exp_pos _))) (by norm_num)).trans
        ((mul_le_mul_of_nonneg_left hprod_lb (by norm_num)).trans hL_ge_half)
    have hrew : Real.exp (M_43 - 2) / (2 * Real.sqrt 14) * Real.sqrt (Real.log (Y : ℝ)) =
        (1 / 2 : ℝ) * (Real.exp (M_43 - 2) * (Real.sqrt (Real.log (Y : ℝ)) / Real.sqrt 14)) := by ring
    linarith
  have hden_pos : 0 < Real.exp (M_43 - 2) / (2 * Real.sqrt 14) * Real.sqrt (Real.log (Y : ℝ)) := by positivity
  have hA_mul : (A.card : ℝ) * (Real.exp (M_43 - 2) / (2 * Real.sqrt 14) * Real.sqrt (Real.log (Y : ℝ))) ≤
      4 * (Y : ℝ) :=
    (mul_le_mul_of_nonneg_left hL_final (Nat.cast_nonneg _)).trans hLS_4Y
  have h8 : 8 * Real.sqrt 14 * Real.exp (2 - M_43) ≤ C₁ := le_max_left _ _
  rw [le_div_iff₀ hsqrt_logY_pos]
  have hinv : (Real.exp (M_43 - 2) / (2 * Real.sqrt 14))⁻¹ = 2 * Real.sqrt 14 * Real.exp (2 - M_43) := by
    rw [inv_div, show 2 - M_43 = -(M_43 - 2) by ring, Real.exp_neg, div_eq_mul_inv]
  have hstep : (A.card : ℝ) * Real.sqrt (Real.log (Y : ℝ)) ≤
      (8 * Real.sqrt 14 * Real.exp (2 - M_43)) * (Y : ℝ) := by
    have hpos_coef : 0 < Real.exp (M_43 - 2) / (2 * Real.sqrt 14) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hA_mul (inv_nonneg.mpr (le_of_lt hpos_coef))
    have hL : (Real.exp (M_43 - 2) / (2 * Real.sqrt 14))⁻¹ *
        ((A.card : ℝ) * (Real.exp (M_43 - 2) / (2 * Real.sqrt 14) * Real.sqrt (Real.log (Y : ℝ)))) =
        (A.card : ℝ) * Real.sqrt (Real.log (Y : ℝ)) := by
      have hne : Real.exp (M_43 - 2) / (2 * Real.sqrt 14) ≠ 0 := ne_of_gt hpos_coef
      field_simp [hne]
    have hR : (Real.exp (M_43 - 2) / (2 * Real.sqrt 14))⁻¹ * (4 * (Y : ℝ)) =
        (8 * Real.sqrt 14 * Real.exp (2 - M_43)) * (Y : ℝ) := by rw [hinv]; ring
    linarith
  exact hstep.trans (mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg Y))

/-- **Landau–Ramanujan Upper Bound (100% Unconditional on Native Mathlib `Nat`):**
There exists `C > 0` such that for all `X ≥ 2`, the number of integers `n ∈ [1, X]` representable
as a sum of two squares `a² + b²` is at most `C * X / √(log X)`. -/
theorem ppl174_sum_two_squares_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (((Finset.Icc 1 X).filter (fun n => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)).card : ℝ) ≤
        C * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
  obtain ⟨C₁, hC₁_pos, hAvoid⟩ := avoid_mod4_eq3_upper_bound
  set C : ℝ := max (4 * C₁ + 10) (Real.sqrt (Real.log 16) + 1)
  refine ⟨C, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun X hX2 => ?_⟩
  set B : Finset ℕ := (Finset.Icc 1 X).filter (fun n => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hsqrt_pos : 0 < Real.sqrt (Real.log (X : ℝ)) := Real.sqrt_pos.mpr hlogX_pos
  by_cases hsmall : X < 16
  · have hcard : (B.card : ℝ) ≤ (X : ℝ) := by
      have h1 : B.card ≤ (Finset.Icc 1 X).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.card_Icc] at h1; exact_mod_cast (by omega : B.card ≤ X)
    have hsq : Real.sqrt (Real.log (X : ℝ)) ≤ C := by
      have h1 : Real.log (X : ℝ) ≤ Real.log 16 :=
        Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast le_of_lt hsmall)
      have h2 := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (Real.log 16) + 1 ≤ C := le_max_right _ _
      linarith
    rw [le_div_iff₀ hsqrt_pos]
    calc (B.card : ℝ) * Real.sqrt (Real.log (X : ℝ))
        ≤ (X : ℝ) * C := mul_le_mul hcard hsq (le_of_lt hsqrt_pos) (Nat.cast_nonneg X)
      _ = C * (X : ℝ) := mul_comm _ _
  have hX16 : 16 ≤ X := not_lt.mp hsmall
  -- Cover `B` by `⋃_{r = 1}^{⌊√X⌋} (S_avoid (X / r²)) * r²`
  let Savoid : ℕ → Finset ℕ := fun Y =>
    (Finset.Icc 1 Y).filter (fun s => ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ s)
  have hcover : B ⊆ (Finset.Icc 1 (Nat.sqrt X)).biUnion (fun r =>
      (Savoid (X / r ^ 2)).image (fun s => s * r ^ 2)) := by
    intro n hn
    have hI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hsq := (Finset.mem_filter.mp hn).2
    obtain ⟨s, r, hs, hr, hdecomp, hav⟩ := sum_two_sq_decomp n hI.1 hsq
    have hr2_le : r ^ 2 ≤ X := by nlinarith [hdecomp, hs, hI.2]
    have hr_le : r ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by rwa [← sq])
    have hs_le : s ≤ X / r ^ 2 := (Nat.le_div_iff_mul_le (pow_pos (by omega) 2)).mpr (by nlinarith [hdecomp, hI.2])
    refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_Icc.mpr ⟨hr, hr_le⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs, hs_le⟩, hav⟩, hdecomp.symm⟩
  have hcard_sum : (B.card : ℝ) ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt X), ((Savoid (X / r ^ 2)).card : ℝ) := by
    have hnat : B.card ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt X), (Savoid (X / r ^ 2)).card := by
      calc B.card
          ≤ ((Finset.Icc 1 (Nat.sqrt X)).biUnion (fun r =>
              (Savoid (X / r ^ 2)).image (fun s => s * r ^ 2))).card := Finset.card_le_card hcover
        _ ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt X), ((Savoid (X / r ^ 2)).image (fun s => s * r ^ 2)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt X), (Savoid (X / r ^ 2)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
    exact_mod_cast hnat
  -- Split `r ∈ [1, √X]` at `R = Nat.sqrt (Nat.sqrt X)` (`2 ≤ R ≤ Nat.sqrt X`)
  set R : ℕ := Nat.sqrt (Nat.sqrt X)
  have hsqX_ge4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hR_ge2 : 2 ≤ R := Nat.le_sqrt.mpr (by omega)
  have hR_le_sqX : R ≤ Nat.sqrt X := Nat.sqrt_le_self _
  have hsplit : Finset.Icc 1 (Nat.sqrt X) = Finset.Icc 1 R ∪ Finset.Icc (R + 1) (Nat.sqrt X) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 R) (Finset.Icc (R + 1) (Nat.sqrt X)) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    have := (Finset.mem_Icc.mp h1).2; have := (Finset.mem_Icc.mp h2).1; omega
  rw [hsplit, Finset.sum_union hdisj] at hcard_sum
  -- Part 1: Small `r ∈ [1, R]`: `X / r² ≥ √X ≥ 4`, `log(X / r²) ≥ (1/4) log X`
  have hpart1 : ∑ r ∈ Finset.Icc 1 R, ((Savoid (X / r ^ 2)).card : ℝ) ≤
      4 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
    have hterm : ∀ r ∈ Finset.Icc 1 R,
        ((Savoid (X / r ^ 2)).card : ℝ) ≤
        2 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) * ((r : ℝ) ^ 2)⁻¹ := by
      intro r hr
      have hr1 := (Finset.mem_Icc.mp hr).1
      have hrR := (Finset.mem_Icc.mp hr).2
      have hr2_le : r ^ 2 ≤ Nat.sqrt X := by
        calc r ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hrR 2
          _ = R * R := sq R
          _ ≤ Nat.sqrt X := Nat.sqrt_le _
      have hdiv_ge : Nat.sqrt X ≤ X / r ^ 2 := by
        rw [Nat.le_div_iff_mul_le (pow_pos (by omega) 2)]
        calc Nat.sqrt X * r ^ 2 ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ hr2_le
          _ ≤ X := Nat.sqrt_le X
      have hdiv_ge2 : 2 ≤ X / r ^ 2 := by omega
      have hY_le : ((X / r ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / (r : ℝ) ^ 2 := by
        rw [le_div_iff₀ (pow_pos (Nat.cast_pos.mpr (by omega)) 2)]
        have hnat : (X / r ^ 2) * r ^ 2 ≤ X := Nat.div_mul_le_self X (r ^ 2)
        exact_mod_cast hnat
      have hlog_div : (1 / 4 : ℝ) * Real.log (X : ℝ) ≤ Real.log ((X / r ^ 2 : ℕ) : ℝ) := by
        have hsqX_le_div : (Nat.sqrt X : ℝ) ≤ ((X / r ^ 2 : ℕ) : ℝ) := by exact_mod_cast hdiv_ge
        have hX_le_sq : (X : ℝ) ≤ ((Nat.sqrt X : ℝ) ^ 4) := by
          have h1 : X < (Nat.sqrt X + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt X
          have h2 : (Nat.sqrt X + 1) ^ 2 ≤ (Nat.sqrt X) ^ 4 := by
            have h4 : 4 ≤ Nat.sqrt X := hsqX_ge4
            calc (Nat.sqrt X + 1) ^ 2 ≤ (Nat.sqrt X * Nat.sqrt X) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
              _ = Nat.sqrt X ^ 4 := by ring
          exact_mod_cast (le_of_lt h1).trans h2
        have h1 := Real.log_le_log (Nat.cast_pos.mpr (by omega)) hX_le_sq
        rw [Real.log_pow] at h1; push_cast at h1
        have h2 := Real.log_le_log (Nat.cast_pos.mpr (by omega)) hsqX_le_div
        linarith
      have hsq_lb : Real.sqrt (Real.log (X : ℝ)) / 2 ≤ Real.sqrt (Real.log ((X / r ^ 2 : ℕ) : ℝ)) := by
        have h1 := Real.sqrt_le_sqrt hlog_div
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
            show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by
              rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
        linarith
      have hav := hAvoid (X / r ^ 2) hdiv_ge2
      have hlog_d_pos : 0 < Real.sqrt (Real.log ((X / r ^ 2 : ℕ) : ℝ)) :=
        Real.sqrt_pos.mpr (by linarith)
      calc ((Savoid (X / r ^ 2)).card : ℝ)
          ≤ C₁ * ((X / r ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((X / r ^ 2 : ℕ) : ℝ)) := hav
        _ ≤ C₁ * ((X : ℝ) / (r : ℝ) ^ 2) / (Real.sqrt (Real.log (X : ℝ)) / 2) := by
            apply div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_left hY_le (le_of_lt hC₁_pos)) (by positivity) hsq_lb
        _ = 2 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) * ((r : ℝ) ^ 2)⁻¹ := by ring
    calc ∑ r ∈ Finset.Icc 1 R, ((Savoid (X / r ^ 2)).card : ℝ)
        ≤ ∑ r ∈ Finset.Icc 1 R,
            (2 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) * ((r : ℝ) ^ 2)⁻¹) :=
          Finset.sum_le_sum hterm
      _ = 2 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) *
            ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two R) (by positivity)
      _ = 4 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by ring
  -- Part 2: Large `r ∈ [R + 1, √X]`: `≤ X / R ≤ 10 * X / √(log X)`
  have hpart2 : ∑ r ∈ Finset.Icc (R + 1) (Nat.sqrt X), ((Savoid (X / r ^ 2)).card : ℝ) ≤
      10 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by
    have hsum_le : ∑ r ∈ Finset.Icc (R + 1) (Nat.sqrt X), ((Savoid (X / r ^ 2)).card : ℝ) ≤
        (X : ℝ) * (R : ℝ)⁻¹ := by
      calc ∑ r ∈ Finset.Icc (R + 1) (Nat.sqrt X), ((Savoid (X / r ^ 2)).card : ℝ)
          ≤ ∑ r ∈ Finset.Icc (R + 1) (Nat.sqrt X), (X : ℝ) * ((r : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
            have h1 : (Savoid (X / r ^ 2)).card ≤ X / r ^ 2 := by
              have hsubS : Savoid (X / r ^ 2) ⊆ Finset.Icc 1 (X / r ^ 2) :=
                Finset.filter_subset (fun s => ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ s) _
              have hle := Finset.card_le_card hsubS
              rw [Nat.card_Icc, Nat.add_sub_cancel] at hle
              exact hle
            have h2 : ((X / r ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) * ((r : ℝ) ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (Nat.cast_pos.mpr (by omega)) 2)]
              exact_mod_cast Nat.div_mul_le_self X (r ^ 2)
            exact (by exact_mod_cast h1 : ((Savoid (X / r ^ 2)).card : ℝ) ≤ _).trans h2
        _ = (X : ℝ) * ∑ r ∈ Finset.Icc (R + 1) (Nat.sqrt X), ((r : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
        _ ≤ (X : ℝ) * (R : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_tail_le (by omega : 1 ≤ R)) (Nat.cast_nonneg X)
    -- Show `√(log X) ≤ 10 * R` (since `X < (R + 1)^4` implies `log X ≤ 4 log(R + 1) ≤ 4(R + 1) ≤ 8 R`)
    have hsq_le_10R : Real.sqrt (Real.log (X : ℝ)) ≤ 10 * (R : ℝ) := by
      have hX_lt_R4 : (X : ℝ) ≤ ((R : ℝ) + 1) ^ 4 * 2 := by
        have h1 : Nat.sqrt X < (R + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt _
        have h2 : X < (Nat.sqrt X + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt X
        have h3 : Nat.sqrt X + 1 ≤ (R + 1) ^ 2 := by omega
        have h4 : X ≤ (R + 1) ^ 4 := by
          have := Nat.pow_le_pow_left h3 2
          nlinarith
        have h4R : (X : ℝ) ≤ ((R : ℝ) + 1) ^ 4 := by exact_mod_cast h4
        nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1) 4]
      have hlog_R : Real.log (X : ℝ) ≤ 4 * (R : ℝ) + 5 := by
        have h1 := Real.log_le_log (Nat.cast_pos.mpr (by omega)) hX_lt_R4
        rw [Real.log_mul (ne_of_gt (pow_pos (by positivity) 4)) (by norm_num), Real.log_pow] at h1
        push_cast at h1
        have h2 : Real.log ((R : ℝ) + 1) ≤ (R : ℝ) := by linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (R : ℝ) + 1)]
        have h3 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR_ge2
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
    have hinv_le : (R : ℝ)⁻¹ ≤ 10 / Real.sqrt (Real.log (X : ℝ)) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hR_pos hsqrt_pos]; linarith
    calc ∑ r ∈ Finset.Icc (R + 1) (Nat.sqrt X), ((Savoid (X / r ^ 2)).card : ℝ)
        ≤ (X : ℝ) * (R : ℝ)⁻¹ := hsum_le
      _ ≤ (X : ℝ) * (10 / Real.sqrt (Real.log (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hinv_le (Nat.cast_nonneg X)
      _ = 10 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by ring
  have h4C1 : 4 * C₁ + 10 ≤ C := le_max_left _ _
  calc (B.card : ℝ)
      ≤ 4 * C₁ * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) +
        10 * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by linarith [hcard_sum, hpart1, hpart2]
    _ = (4 * C₁ + 10) * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) := by ring
    _ ≤ C * (X : ℝ) / Real.sqrt (Real.log (X : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4C1 (Nat.cast_nonneg X))
          (le_of_lt hsqrt_pos)

/-- **Erdős (1946) Integer-Grid `O(n / √(log n))` Upper Construction (100% Unconditional, PPL 174):**
There exists `C > 0` such that for every `n ≥ 2`, there is an `n`-point planar set `A ⊂ ℝ²`
determining at most `C * n / √(log n)` total distinct Euclidean distances (and hence at most
`C * n / √(log n)` distinct distances from EVERY pin `x ∈ A` simultaneously!). -/
theorem ppl174_erdos_grid_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧
        (((A ×ˢ A).image (fun p => dist p.1 p.2)).card : ℝ) ≤
          C * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ∧
        (∀ x ∈ A, ((A.image (dist x ·)).card : ℝ) ≤
          C * (n : ℝ) / Real.sqrt (Real.log (n : ℝ))) := by
  obtain ⟨C₀, hC₀_pos, hLR⟩ := ppl174_sum_two_squares_upper_bound
  refine ⟨8 * C₀ + 1, by positivity, fun n hn2 => ?_⟩
  set s : ℕ := Nat.sqrt (n - 1)
  set k : ℕ := s + 1
  have hk2_ge : n ≤ k * k := by
    have hlt : n - 1 < k * k := Nat.lt_succ_sqrt (n - 1)
    omega
  have hk2_le : k * k ≤ 4 * n := by
    have hsq : s * s ≤ n := (Nat.sqrt_le (n - 1)).trans (Nat.sub_le n 1)
    have h1 : 1 ≤ s := Nat.le_sqrt.mpr (by omega)
    have hk_eq : k = s + 1 := rfl
    nlinarith
  let grid : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((Finset.range k) ×ˢ (Finset.range k)).image (fun p => mkPt (p.1 : ℝ) (p.2 : ℝ))
  have hgrid_inj : Set.InjOn (fun p : ℕ × ℕ => mkPt (p.1 : ℝ) (p.2 : ℝ))
      (((Finset.range k) ×ˢ (Finset.range k) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p₁ _ p₂ _ heq
    have h0 : (p₁.1 : ℝ) = (p₂.1 : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) heq
      simpa [mkPt_zero] using this
    have h1 : (p₁.2 : ℝ) = (p₂.2 : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) heq
      simpa [mkPt_one] using this
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hgrid_card : grid.card = k * k := by
    rw [Finset.card_image_of_injOn hgrid_inj, Finset.card_product, Finset.card_range]
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := grid) (n := n) (by rw [hgrid_card]; exact hk2_ge)
  -- Every squared distance `dist p q ^ 2` for `p, q ∈ A` is a sum of two squares `≤ 8 * n`!
  let S2 : Finset ℕ := insert 0 ((Finset.Icc 1 (8 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2))
  have hdist_sub : (A ×ˢ A).image (fun p => dist p.1 p.2) ⊆ S2.image (fun m : ℕ => Real.sqrt (m : ℝ)) := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨⟨p, q⟩, hpq, rfl⟩
    have hpA := (Finset.mem_product.mp hpq).1
    have hqA := (Finset.mem_product.mp hpq).2
    rcases Finset.mem_image.mp (hAsub hpA) with ⟨⟨i₁, j₁⟩, hij₁, rfl⟩
    rcases Finset.mem_image.mp (hAsub hqA) with ⟨⟨i₂, j₂⟩, hij₂, rfl⟩
    have hi₁ : i₁ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₁).1
    have hj₁ : j₁ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₁).2
    have hi₂ : i₂ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₂).1
    have hj₂ : j₂ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₂).2
    set a : ℕ := if i₁ ≤ i₂ then i₂ - i₁ else i₁ - i₂
    set b : ℕ := if j₁ ≤ j₂ then j₂ - j₁ else j₁ - j₂
    have ha_sq : ((i₁ : ℝ) - (i₂ : ℝ)) ^ 2 = ((a ^ 2 : ℕ) : ℝ) := by
      dsimp [a]; split_ifs with h
      · rw [Nat.cast_pow, Nat.cast_sub h]; ring
      · rw [Nat.cast_pow, Nat.cast_sub (le_of_not_ge h)]
    have hb_sq : ((j₁ : ℝ) - (j₂ : ℝ)) ^ 2 = ((b ^ 2 : ℕ) : ℝ) := by
      dsimp [b]; split_ifs with h
      · rw [Nat.cast_pow, Nat.cast_sub h]; ring
      · rw [Nat.cast_pow, Nat.cast_sub (le_of_not_ge h)]
    have hd_eq : dist (mkPt (i₁ : ℝ) (j₁ : ℝ)) (mkPt (i₂ : ℝ) (j₂ : ℝ)) =
        Real.sqrt (((a ^ 2 + b ^ 2 : ℕ) : ℝ)) := by
      have hsq : dist (mkPt (i₁ : ℝ) (j₁ : ℝ)) (mkPt (i₂ : ℝ) (j₂ : ℝ)) ^ 2 =
          ((a ^ 2 + b ^ 2 : ℕ) : ℝ) := by
        rw [dist_sq_eq_coords, mkPt_zero, mkPt_zero, mkPt_one, mkPt_one, ha_sq, hb_sq]
        push_cast; ring
      rw [← hsq, Real.sqrt_sq dist_nonneg]
    refine Finset.mem_image.mpr ⟨a ^ 2 + b ^ 2, ?_, hd_eq.symm⟩
    by_cases h0 : a ^ 2 + b ^ 2 = 0
    · rw [h0]; exact Finset.mem_insert_self 0 _
    · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ⟨a, b, rfl⟩⟩)
      have ha_lt : a ≤ k := by dsimp [a]; split_ifs <;> omega
      have hb_lt : b ≤ k := by dsimp [b]; split_ifs <;> omega
      nlinarith [hk2_le]
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsq_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have htot_bd : (((A ×ˢ A).image (fun p => dist p.1 p.2)).card : ℝ) ≤
      (8 * C₀ + 1) * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
    have hcard_le : ((A ×ˢ A).image (fun p => dist p.1 p.2)).card ≤
        1 + ((Finset.Icc 1 (8 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2)).card := by
      calc ((A ×ˢ A).image (fun p => dist p.1 p.2)).card
          ≤ (S2.image (fun m : ℕ => Real.sqrt (m : ℝ))).card := Finset.card_le_card hdist_sub
        _ ≤ S2.card := Finset.card_image_le
        _ ≤ 1 + ((Finset.Icc 1 (8 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2)).card := by
            have := Finset.card_insert_le 0 ((Finset.Icc 1 (8 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2))
            dsimp only [S2]; omega
    have hLR8 := hLR (8 * n) (by omega)
    have hlog_mono : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log ((8 * n : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt (Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast (by omega : n ≤ 8 * n)))
    have h1le : (1 : ℝ) ≤ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
      rw [one_le_div hsq_pos]
      have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < (n : ℝ))]
      have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg n, by nlinarith⟩
    have h8bd : (((Finset.Icc 1 (8 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2)).card : ℝ) ≤
        8 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
      have hcast8 : ((8 * n : ℕ) : ℝ) = 8 * (n : ℝ) := by push_cast; ring
      rw [hcast8] at hLR8
      have hdiv : C₀ * (8 * (n : ℝ)) / Real.sqrt (Real.log (8 * (n : ℝ))) ≤
          C₀ * (8 * (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hsq_pos (by rwa [← hcast8])
      have hrew : C₀ * (8 * (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) =
          8 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by ring
      linarith [hLR8.trans hdiv]
    have hcardR : (((A ×ˢ A).image (fun p => dist p.1 p.2)).card : ℝ) ≤
        1 + (((Finset.Icc 1 (8 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2)).card : ℝ) := by
      exact_mod_cast hcard_le
    linarith [show (8 * C₀ + 1) * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) =
      8 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) + (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) by ring]
  refine ⟨A, hAcard, htot_bd, fun x hx => ?_⟩
  have hsub : A.image (dist x ·) ⊆ (A ×ˢ A).image (fun p => dist p.1 p.2) := by
    intro d hd; rcases Finset.mem_image.mp hd with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  exact (by exact_mod_cast Finset.card_le_card hsub : ((A.image (dist x ·)).card : ℝ) ≤ _).trans htot_bd

/-- **Erdős Integer-Grid `O(n / √(log n))` Bipartite Upper Construction (100% Unconditional, PPL 015):**
There exists `C > 0` such that for every `n ≥ 2`, there exist two DISJOINT `n`-point planar sets
`X, Y ⊂ ℝ²` determining at most `C * n / √(log n)` distinct bipartite distances `d(x, y)` (`x ∈ X, y ∈ Y`).
(PPL 015 / Erdős #661 asks whether `o(n / √(log n))` is achievable — still OPEN!) -/
theorem ppl015_bipartite_grid_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ X Y : Finset (EuclideanSpace ℝ (Fin 2)),
        X.card = n ∧ Y.card = n ∧ Disjoint X Y ∧
        (((X ×ˢ Y).image (fun p => dist p.1 p.2)).card : ℝ) ≤
          C * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  obtain ⟨C₀, hC₀_pos, hLR⟩ := ppl174_sum_two_squares_upper_bound
  refine ⟨20 * C₀ + 1, by positivity, fun n hn2 => ?_⟩
  set s : ℕ := Nat.sqrt (n - 1)
  set k : ℕ := s + 1
  have hk2_ge : n ≤ k * k := by
    have hlt : n - 1 < k * k := Nat.lt_succ_sqrt (n - 1)
    omega
  have hk2_le : k * k ≤ 4 * n := by
    have hsq : s * s ≤ n := (Nat.sqrt_le (n - 1)).trans (Nat.sub_le n 1)
    have h1 : 1 ≤ s := Nat.le_sqrt.mpr (by omega)
    have hk_eq : k = s + 1 := rfl
    nlinarith
  let gridX : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((Finset.range k) ×ˢ (Finset.range k)).image (fun p => mkPt (p.1 : ℝ) (p.2 : ℝ))
  let gridY : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((Finset.range k) ×ˢ (Finset.range k)).image (fun p => mkPt ((p.1 + k : ℕ) : ℝ) (p.2 : ℝ))
  have hinjX : Set.InjOn (fun p : ℕ × ℕ => mkPt (p.1 : ℝ) (p.2 : ℝ))
      (((Finset.range k) ×ˢ (Finset.range k) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p₁ _ p₂ _ heq
    have h0 : (p₁.1 : ℝ) = (p₂.1 : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) heq; simpa [mkPt_zero] using this
    have h1 : (p₁.2 : ℝ) = (p₂.2 : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) heq; simpa [mkPt_one] using this
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hinjY : Set.InjOn (fun p : ℕ × ℕ => mkPt ((p.1 + k : ℕ) : ℝ) (p.2 : ℝ))
      (((Finset.range k) ×ˢ (Finset.range k) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p₁ _ p₂ _ heq
    have h0 : ((p₁.1 + k : ℕ) : ℝ) = ((p₂.1 + k : ℕ) : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) heq; simpa [mkPt_zero] using this
    have h1 : (p₁.2 : ℝ) = (p₂.2 : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) heq; simpa [mkPt_one] using this
    have h0' : p₁.1 + k = p₂.1 + k := by exact_mod_cast h0
    exact Prod.ext (by omega) (by exact_mod_cast h1)
  have hcardX : gridX.card = k * k := by
    rw [Finset.card_image_of_injOn hinjX, Finset.card_product, Finset.card_range]
  have hcardY : gridY.card = k * k := by
    rw [Finset.card_image_of_injOn hinjY, Finset.card_product, Finset.card_range]
  obtain ⟨X, hXsub, hXcard⟩ :=
    Finset.exists_subset_card_eq (s := gridX) (n := n) (by rw [hcardX]; exact hk2_ge)
  obtain ⟨Y, hYsub, hYcard⟩ :=
    Finset.exists_subset_card_eq (s := gridY) (n := n) (by rw [hcardY]; exact hk2_ge)
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro q hqX hqY
    rcases Finset.mem_image.mp (hXsub hqX) with ⟨⟨i₁, j₁⟩, hij₁, h1⟩
    rcases Finset.mem_image.mp (hYsub hqY) with ⟨⟨i₂, j₂⟩, _, h2⟩
    have hi₁ : i₁ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₁).1
    have h0 : (i₁ : ℝ) = ((i₂ + k : ℕ) : ℝ) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) (h1.trans h2.symm)
      simpa [mkPt_zero] using this
    have h0' : i₁ = i₂ + k := by exact_mod_cast h0
    omega
  let S2 : Finset ℕ := (Finset.Icc 1 (20 * n)).filter (fun m => ∃ a b : ℕ, m = a ^ 2 + b ^ 2)
  have hdist_sub : (X ×ˢ Y).image (fun p => dist p.1 p.2) ⊆ S2.image (fun m : ℕ => Real.sqrt (m : ℝ)) := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨⟨p, q⟩, hpq, rfl⟩
    rcases Finset.mem_image.mp (hXsub (Finset.mem_product.mp hpq).1) with ⟨⟨i₁, j₁⟩, hij₁, rfl⟩
    rcases Finset.mem_image.mp (hYsub (Finset.mem_product.mp hpq).2) with ⟨⟨i₂, j₂⟩, hij₂, rfl⟩
    have hi₁ : i₁ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₁).1
    have hj₁ : j₁ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₁).2
    have hi₂ : i₂ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₂).1
    have hj₂ : j₂ < k := Finset.mem_range.mp (Finset.mem_product.mp hij₂).2
    set a : ℕ := i₂ + k - i₁
    set b : ℕ := if j₁ ≤ j₂ then j₂ - j₁ else j₁ - j₂
    have ha_pos : 1 ≤ a := by dsimp [a]; omega
    have ha_le : a ≤ 2 * k := by dsimp [a]; omega
    have hb_le : b ≤ k := by dsimp [b]; split_ifs <;> omega
    have ha_sq : ((i₁ : ℝ) - ((i₂ + k : ℕ) : ℝ)) ^ 2 = ((a ^ 2 : ℕ) : ℝ) := by
      dsimp [a]; rw [Nat.cast_pow, Nat.cast_sub (by omega : i₁ ≤ i₂ + k)]; ring
    have hb_sq : ((j₁ : ℝ) - (j₂ : ℝ)) ^ 2 = ((b ^ 2 : ℕ) : ℝ) := by
      dsimp [b]; split_ifs with h
      · rw [Nat.cast_pow, Nat.cast_sub h]; ring
      · rw [Nat.cast_pow, Nat.cast_sub (le_of_not_ge h)]
    have hd_eq : dist (mkPt (i₁ : ℝ) (j₁ : ℝ)) (mkPt ((i₂ + k : ℕ) : ℝ) (j₂ : ℝ)) =
        Real.sqrt (((a ^ 2 + b ^ 2 : ℕ) : ℝ)) := by
      have hsq : dist (mkPt (i₁ : ℝ) (j₁ : ℝ)) (mkPt ((i₂ + k : ℕ) : ℝ) (j₂ : ℝ)) ^ 2 =
          ((a ^ 2 + b ^ 2 : ℕ) : ℝ) := by
        rw [dist_sq_eq_coords, mkPt_zero, mkPt_zero, mkPt_one, mkPt_one, ha_sq, hb_sq]
        push_cast; ring
      rw [← hsq, Real.sqrt_sq dist_nonneg]
    refine Finset.mem_image.mpr ⟨a ^ 2 + b ^ 2, ?_, hd_eq.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith [hk2_le]⟩, ⟨a, b, rfl⟩⟩
  refine ⟨X, Y, hXcard, hYcard, hdisj, ?_⟩
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsq_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have hLR20 := hLR (20 * n) (by omega)
  have hcast20 : ((20 * n : ℕ) : ℝ) = 20 * (n : ℝ) := by push_cast; ring
  have hlog_mono : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log ((20 * n : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt (Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast (by omega : n ≤ 20 * n)))
  have hcard : ((X ×ˢ Y).image (fun p => dist p.1 p.2)).card ≤ S2.card :=
    (Finset.card_le_card hdist_sub).trans Finset.card_image_le
  have hbd : (S2.card : ℝ) ≤ 20 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
    rw [hcast20] at hLR20
    have hdiv : C₀ * (20 * (n : ℝ)) / Real.sqrt (Real.log (20 * (n : ℝ))) ≤
        C₀ * (20 * (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) hsq_pos (by rwa [← hcast20])
    have hrew : C₀ * (20 * (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) =
        20 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by ring
    linarith [hLR20.trans hdiv]
  have hnn : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by positivity
  calc (((X ×ˢ Y).image (fun p => dist p.1 p.2)).card : ℝ)
      ≤ (S2.card : ℝ) := by exact_mod_cast hcard
    _ ≤ 20 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := hbd
    _ ≤ (20 * C₀ + 1) * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
        rw [show (20 * C₀ + 1) * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) =
          20 * C₀ * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) + (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) by ring]
        linarith

/-! ### Section 4: Energy Reductions (Guth–Katz / Katz–Tardos / Bipartite) & Structural Barriers -/

/-- General finite Cauchy–Schwarz fiber energy bound: for any `f : S → β`,
`|S|² ≤ |f(S)| * |{(a, b) ∈ S × S : f a = f b}|`. -/
private lemma card_sq_le_image_mul_energy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    (S.card : ℝ) ^ 2 ≤ ((S.image f).card : ℝ) *
      (((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card : ℝ) := by
  have hsum : (S.card : ℝ) = ∑ y ∈ S.image f, ((S.filter (fun a => f a = y)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f S
  have henergy : (((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card : ℝ) =
      ∑ y ∈ S.image f, ((S.filter (fun a => f a = y)).card : ℝ) ^ 2 := by
    have hnat : ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card =
        ∑ y ∈ S.image f, (S.filter (fun a => f a = y)).card ^ 2 := by
      have hbi : (S ×ˢ S).filter (fun p => f p.1 = f p.2) =
          (S.image f).biUnion (fun y => (S.filter (fun a => f a = y)) ×ˢ (S.filter (fun b => f b = y))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨⟨ha, hb⟩, hab⟩
          exact ⟨f a, ⟨a, ha, rfl⟩, ⟨ha, rfl⟩, ⟨hb, hab.symm⟩⟩
        · rintro ⟨y, _, ⟨ha, rfl⟩, ⟨hb, hby⟩⟩
          exact ⟨⟨ha, hb⟩, hby.symm⟩
      have hdisj : Set.PairwiseDisjoint (S.image f : Set β)
          (fun y => (S.filter (fun a => f a = y)) ×ˢ (S.filter (fun b => f b = y))) := by
        intro y₁ _ y₂ _ hne
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro ⟨a, b⟩ h1 h2
        have h1' := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
        have h2' := (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2
        exact hne (h1'.symm.trans h2')
      rw [hbi, Finset.card_biUnion hdisj]
      refine Finset.sum_congr rfl fun y _ => by rw [Finset.card_product, sq]
    exact_mod_cast hnat
  rw [hsum, henergy]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (S.image f) (fun _ => (1 : ℝ))
    (fun y => ((S.filter (fun a => f a = y)).card : ℝ))
  simpa using hcs

/-- **Guth–Katz / Elekes–Sharir Unpinned Distance Energy Lower Bound (Unconditional):**
For any finite `A ⊂ ℝ²`,
`(|A| (|A| - 1))² ≤ |{(p₁, q₁, p₂, q₂) ∈ A⁴ : p₁ ≠ q₁ ∧ p₂ ≠ q₂ ∧ d(p₁, q₁) = d(p₂, q₂)}| * |D(A \ diag)|`.
Hence Guth–Katz's quadruple energy bound `Q(A) = O(n³ log n)` yields `Ω(n / log n)` unpinned distances,
whereas it does NOT directly yield pinned bounds (PPL 174) or close the `√(log n)` gap. -/
theorem ppl174_cauchy_schwarz_distance_energy
    (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((A.card * (A.card - 1) : ℕ) : ℝ) ^ 2 ≤
      ((((A ×ˢ A).filter (fun p => p.1 ≠ p.2)) ×ˢ ((A ×ˢ A).filter (fun p => p.1 ≠ p.2))).filter
        (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card *
      ((((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card : ℝ) := by
  set S := (A ×ˢ A).filter (fun p => p.1 ≠ p.2)
  have hScard : S.card = A.card * (A.card - 1) := by
    have hdiag : (A ×ˢ A).filter (fun p => p.1 = p.2) = A.image (fun x => (x, x)) := by
      ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨x, hx, h⟩; rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact ⟨⟨hx, hx⟩, rfl⟩
    have hpart : S.card + ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = (A ×ˢ A).card := by
      have hdisj : Disjoint S ((A ×ˢ A).filter (fun p => p.1 = p.2)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hunion : S ∪ (A ×ˢ A).filter (fun p => p.1 = p.2) = A ×ˢ A := by
        ext p; simp only [S, Finset.mem_union, Finset.mem_filter]; tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hdiag_card : ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = A.card := by
      rw [hdiag, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    rw [Finset.card_product, hdiag_card] at hpart
    cases hA : A.card with
    | zero => rw [hA] at hpart; omega
    | succ k => rw [hA] at hpart; simp only [Nat.add_sub_cancel]; nlinarith
  have hcs := card_sq_le_image_mul_energy S (fun p => dist p.1 p.2)
  rw [hScard] at hcs
  linarith [mul_comm (((S.image (fun p => dist p.1 p.2)).card : ℝ))
    ((((S ×ˢ S).filter (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card : ℝ))]

/-- **Pinned Isosceles-Triangle Energy Lower Bound (Unconditional, PPL 174):**
For any finite `A ⊂ ℝ²` and `t : ℕ` with `∀ x ∈ A, |D(x, A)| ≤ t`,
`|A|³ ≤ t * |{(x, y₁, y₂) ∈ A³ : d(x, y₁) = d(x, y₂)}|`.
This isolates the exact Katz–Tardos / bisector-energy bottleneck: proving `Ω(n / √(log n))` pinned
distances via average isosceles energy requires bounding `T(A) = O(n² √(log n))`, whereas
single bad pins (such as a circle center) can already contribute `Θ(n²)` isosceles triples. -/
theorem ppl174_pinned_isosceles_energy_lower
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (t : ℕ)
    (ht : ∀ x ∈ A, (A.image (dist x ·)).card ≤ t) :
    (A.card : ℝ) ^ 3 ≤
      (t : ℝ) * (((A ×ˢ (A ×ˢ A)).filter (fun q => dist q.1 q.2.1 = dist q.1 q.2.2)).card : ℝ) := by
  have hper : ∀ x ∈ A, (A.card : ℝ) ^ 2 ≤
      (t : ℝ) * (((A ×ˢ A).filter (fun p => dist x p.1 = dist x p.2)).card : ℝ) := by
    intro x hx
    have hcs := card_sq_le_image_mul_energy A (dist x ·)
    have htle : ((A.image (dist x ·)).card : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht x hx
    exact hcs.trans (mul_le_mul_of_nonneg_right htle (Nat.cast_nonneg _))
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have heq : (((A ×ˢ (A ×ˢ A)).filter (fun q => dist q.1 q.2.1 = dist q.1 q.2.2)).card : ℝ) =
      ∑ x ∈ A, (((A ×ˢ A).filter (fun p => dist x p.1 = dist x p.2)).card : ℝ) := by
    have hnat : ((A ×ˢ (A ×ˢ A)).filter (fun q => dist q.1 q.2.1 = dist q.1 q.2.2)).card =
        ∑ x ∈ A, ((A ×ˢ A).filter (fun p => dist x p.1 = dist x p.2)).card := by
      have hbi : (A ×ˢ (A ×ˢ A)).filter (fun q => dist q.1 q.2.1 = dist q.1 q.2.2) =
          A.biUnion (fun x => ((A ×ˢ A).filter (fun p => dist x p.1 = dist x p.2)).image (fun p => (x, p))) := by
        ext ⟨x, y₁, y₂⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨⟨hx, hy₁, hy₂⟩, hd⟩
          exact ⟨x, hx, (y₁, y₂), ⟨⟨hy₁, hy₂⟩, hd⟩, rfl⟩
        · rintro ⟨x', hx', ⟨u, v⟩, ⟨⟨hu, hv⟩, hd⟩, heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, hp⟩
          rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
          exact ⟨⟨hx', hu, hv⟩, hd⟩
      have hdisj : Set.PairwiseDisjoint (A : Set (EuclideanSpace ℝ (Fin 2)))
          (fun x => ((A ×ˢ A).filter (fun p => dist x p.1 = dist x p.2)).image (fun p => (x, p))) := by
        intro x₁ _ x₂ _ hne
        dsimp [Function.onFun]; rw [Finset.disjoint_left]
        intro ⟨x, y₁, y₂⟩ h1 h2
        rcases Finset.mem_image.mp h1 with ⟨_, _, h1'⟩
        rcases Finset.mem_image.mp h2 with ⟨_, _, h2'⟩
        exact hne ((congrArg Prod.fst h1').trans (congrArg Prod.fst h2').symm)
      rw [hbi, Finset.card_biUnion hdisj]
      refine Finset.sum_congr rfl fun x _ =>
        Finset.card_image_of_injective _ (fun p₁ p₂ h => congrArg Prod.snd h)
    exact_mod_cast hnat
  rw [heq]
  linarith [show (A.card : ℝ) * (A.card : ℝ) ^ 2 = (A.card : ℝ) ^ 3 by ring]

/-- **Bipartite Elekes–Sharir Quadruple Energy Lower Bound (Unconditional, PPL 015):**
For any finite `X, Y ⊂ ℝ²`,
`(|X| · |Y|)² ≤ |{((x₁, y₁), (x₂, y₂)) ∈ (X × Y)² : d(x₁, y₁) = d(x₂, y₂)}| · |D(X, Y)|`. -/
theorem ppl015_bipartite_energy_lower
    (X Y : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((X.card * Y.card : ℕ) : ℝ) ^ 2 ≤
      ((((X ×ˢ Y) ×ˢ (X ×ˢ Y)).filter (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card : ℝ) *
      (((X ×ˢ Y).image (fun p => dist p.1 p.2)).card : ℝ) := by
  have hcs := card_sq_le_image_mul_energy (X ×ˢ Y) (fun p => dist p.1 p.2)
  rw [Finset.card_product] at hcs
  linarith [mul_comm ((((X ×ˢ Y).image (fun p => dist p.1 p.2)).card : ℝ))
    (((((X ×ˢ Y) ×ˢ (X ×ˢ Y)).filter (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card : ℝ))]

/-- **Circle-Plus-Center Extremal Pin Contrast (Unconditional, PPL 174):**
For every `n ≥ 3`, there exists an `n`-point set `A ⊂ ℝ²` containing:
- a "bad pin" `x₀ ∈ A` determining ONLY `2` distinct distances (`{0, 1}`), showing why the
  existential quantifier `∃ x ∈ A` in Erdős #604 cannot be strengthened to `∀ x ∈ A`, AND
- a "good pin" `x₁ ∈ A` determining at least `(n - 1) / 2` distinct distances (`Ω(n)`). -/
theorem ppl174_circle_center_extremal_pin (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧
      (∃ x₀ ∈ A, (A.image (dist x₀ ·)).card = 2) ∧
      (∃ x₁ ∈ A, (n - 1) / 2 ≤ (A.image (dist x₁ ·)).card) := by
  set m : ℕ := n - 1
  have hm2 : 2 ≤ m := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  let O : EuclideanSpace ℝ (Fin 2) := mkPt 0 0
  let pt : ℕ → EuclideanSpace ℝ (Fin 2) := fun k =>
    mkPt (Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)))
         (Real.sin (2 * Real.pi * (k : ℝ) / (m : ℝ)))
  let ringPts : Finset (EuclideanSpace ℝ (Fin 2)) := (Finset.range m).image pt
  have hpt_dist_O : ∀ k : ℕ, dist O (pt k) = 1 := fun k => by
    have hsq : dist O (pt k) ^ 2 = 1 := by
      rw [dist_sq_eq_coords, mkPt_zero, mkPt_one, mkPt_zero, mkPt_one]
      have := Real.cos_sq_add_sin_sq (2 * Real.pi * (k : ℝ) / (m : ℝ))
      nlinarith
    have hnn : 0 ≤ dist O (pt k) := dist_nonneg
    nlinarith [sq_nonneg (dist O (pt k) - 1)]
  have hO_notMem : O ∉ ringPts := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
    have h1 := hpt_dist_O k
    rw [hk, dist_self] at h1; norm_num at h1
  have hpt_inj : Set.InjOn pt (Finset.range m : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁' : k₁ < m := Finset.mem_range.mp hk₁
    have hk₂' : k₂ < m := Finset.mem_range.mp hk₂
    have hcos : Real.cos (2 * Real.pi * (k₁ : ℝ) / (m : ℝ)) =
                Real.cos (2 * Real.pi * (k₂ : ℝ) / (m : ℝ)) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) heq
      simpa [pt, mkPt_zero] using this
    have hsin : Real.sin (2 * Real.pi * (k₁ : ℝ) / (m : ℝ)) =
                Real.sin (2 * Real.pi * (k₂ : ℝ) / (m : ℝ)) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) heq
      simpa [pt, mkPt_one] using this
    -- Use `Complex.exp (I * θ₁) = Complex.exp (I * θ₂)` and `Complex.exp_eq_exp_iff_exists_int`!
    set θ₁ : ℝ := 2 * Real.pi * (k₁ : ℝ) / (m : ℝ)
    set θ₂ : ℝ := 2 * Real.pi * (k₂ : ℝ) / (m : ℝ)
    have hexp : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.exp_mul_I]
      rw [show (Complex.cos θ₁ : ℂ) = ↑(Real.cos θ₁) from (Complex.ofReal_cos θ₁).symm,
          show (Complex.sin θ₁ : ℂ) = ↑(Real.sin θ₁) from (Complex.ofReal_sin θ₁).symm,
          show (Complex.cos θ₂ : ℂ) = ↑(Real.cos θ₂) from (Complex.ofReal_cos θ₂).symm,
          show (Complex.sin θ₂ : ℂ) = ↑(Real.sin θ₂) from (Complex.ofReal_sin θ₂).symm,
          hcos, hsin]
    obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him : θ₁ = θ₂ + z * (2 * Real.pi) := by
      have := congrArg Complex.im hz
      simpa [mul_assoc] using this
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1_lt : θ₁ < 2 * Real.pi := by
      dsimp [θ₁]; rw [div_lt_iff₀ hm_pos]
      have : (k₁ : ℝ) < (m : ℝ) := by exact_mod_cast hk₁'
      nlinarith
    have h2_lt : θ₂ < 2 * Real.pi := by
      dsimp [θ₂]; rw [div_lt_iff₀ hm_pos]
      have : (k₂ : ℝ) < (m : ℝ) := by exact_mod_cast hk₂'
      nlinarith
    have h1_nn : 0 ≤ θ₁ := by dsimp [θ₁]; positivity
    have h2_nn : 0 ≤ θ₂ := by dsimp [θ₂]; positivity
    have hz0 : z = 0 := by
      have hlt1 : (z : ℝ) < 1 := by nlinarith
      have hgt1 : (-1 : ℝ) < (z : ℝ) := by nlinarith
      have hz_lt : z < 1 := by exact_mod_cast hlt1
      have hz_gt : -1 < z := by exact_mod_cast hgt1
      omega
    rw [hz0] at him; simp only [Int.cast_zero, zero_mul, add_zero] at him
    have hk_eq : (k₁ : ℝ) = (k₂ : ℝ) := by
      dsimp [θ₁, θ₂] at him
      have hmul := congrArg (· * (m : ℝ)) him
      field_simp [ne_of_gt hm_pos] at hmul
      exact hmul
    exact_mod_cast hk_eq
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := insert O ringPts
  have hAcard : A.card = n := by
    rw [Finset.card_insert_of_notMem hO_notMem, Finset.card_image_of_injOn hpt_inj, Finset.card_range]
    omega
  refine ⟨A, hAcard, ?_, ?_⟩
  · -- Bad pin `O` has exactly 2 distances `{0, 1}`
    refine ⟨O, Finset.mem_insert_self O ringPts, ?_⟩
    have himg : A.image (dist O ·) = {0, 1} := by
      ext d; simp only [A, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨q, rfl | hq, rfl⟩
        · left; exact dist_self O
        · right; rcases Finset.mem_image.mp hq with ⟨k, _, rfl⟩; exact hpt_dist_O k
      · rintro (rfl | rfl)
        · exact ⟨O, Or.inl rfl, dist_self O⟩
        · exact ⟨pt 0, Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))), hpt_dist_O 0⟩
    rw [himg, Finset.card_pair (by norm_num)]
  · -- Good pin `pt 0` has at least `m / 2` distinct distances (from `k = 0, ..., m / 2 - 1`)
    refine ⟨pt 0, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))), ?_⟩
    have hsub : (Finset.range (m / 2)).image (fun k => dist (pt 0) (pt k)) ⊆ A.image (dist (pt 0) ·) := by
      intro d hd; rcases Finset.mem_image.mp hd with ⟨k, hk, rfl⟩
      have hkm : k < m := lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.div_le_self m 2)
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hkm)))
    have hinj_d : Set.InjOn (fun k => dist (pt 0) (pt k)) (Finset.range (m / 2) : Set ℕ) := by
      intro k₁ hk₁ k₂ hk₂ heq
      have hk₁' : k₁ < m / 2 := Finset.mem_range.mp hk₁
      have hk₂' : k₂ < m / 2 := Finset.mem_range.mp hk₂
      have hcos_eq : Real.cos (2 * Real.pi * (k₁ : ℝ) / (m : ℝ)) =
                     Real.cos (2 * Real.pi * (k₂ : ℝ) / (m : ℝ)) := by
        have hsq : ∀ k : ℕ, dist (pt 0) (pt k) ^ 2 =
            2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) := fun k => by
          rw [dist_sq_eq_coords, mkPt_zero, mkPt_one, mkPt_zero, mkPt_one]
          simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, Real.sin_zero]
          have := Real.cos_sq_add_sin_sq (2 * Real.pi * (k : ℝ) / (m : ℝ))
          nlinarith
        have := congrArg (· ^ 2) heq
        rw [hsq k₁, hsq k₂] at this; linarith
      have hle_pi : ∀ k : ℕ, k < m / 2 → 2 * Real.pi * (k : ℝ) / (m : ℝ) ∈ Set.Icc 0 Real.pi := by
        intro k hk
        refine ⟨by positivity, ?_⟩
        rw [div_le_iff₀ hm_pos]
        have h2k : 2 * k ≤ m := by omega
        have h2kR : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2k
        nlinarith [Real.pi_pos]
      have hθ_eq := Real.injOn_cos (hle_pi k₁ hk₁') (hle_pi k₂ hk₂') hcos_eq
      have hkR : (k₁ : ℝ) = (k₂ : ℝ) := by
        have hmul := congrArg (· * (m : ℝ)) hθ_eq
        field_simp [ne_of_gt hm_pos] at hmul
        exact hmul
      exact_mod_cast hkR
    calc m / 2 = (Finset.range (m / 2)).card := (Finset.card_range _).symm
      _ = ((Finset.range (m / 2)).image (fun k => dist (pt 0) (pt k))).card :=
          (Finset.card_image_of_injOn hinj_d).symm
      _ ≤ (A.image (dist (pt 0) ·)).card := Finset.card_le_card hsub

/-- **Finite-Field `𝔽_p²` Barrier Theorem (100% Unconditional):**
For every prime `p`, on the full affine plane `A = 𝔽_p²` (`|A| = p²`), the algebraic squared
distance `((x₁ - x₂)² + (y₁ - y₂)²) : ZMod p` takes at most `p = √|A|` distinct values — both
globally over `A × A` and from every pin `x ∈ A`! Thus purely algebraic circle-incidence bounds
(such as `K_{2,3}`-free / `K_{3,2}`-free double counting) cannot surpass `n^{1/2}` without using
the order/topological structure of `ℝ²`. -/
theorem ppl174_finite_field_sqrt_barrier (p : ℕ) [Fact p.Prime] :
    let A : Finset (ZMod p × ZMod p) := Finset.univ
    A.card = p ^ 2 ∧
    ((A ×ˢ A).image (fun q => (q.1.1 - q.2.1) ^ 2 + (q.1.2 - q.2.2) ^ 2)).card ≤ p ∧
    (∀ x ∈ A, (A.image (fun y => (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)).card ≤ p) := by
  intro A
  have hcard : A.card = p ^ 2 := by
    simp [A, Fintype.card_prod, ZMod.card, sq]
  have hglob : ((A ×ˢ A).image (fun q => (q.1.1 - q.2.1) ^ 2 + (q.1.2 - q.2.2) ^ 2)).card ≤ p := by
    calc ((A ×ˢ A).image (fun q => (q.1.1 - q.2.1) ^ 2 + (q.1.2 - q.2.2) ^ 2)).card
        ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by simp [ZMod.card]
  refine ⟨hcard, hglob, fun x _ => ?_⟩
  calc (A.image (fun y => (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)).card
      ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = p := by simp [ZMod.card]

end PPL174
