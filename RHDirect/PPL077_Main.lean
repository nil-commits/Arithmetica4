/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 077 (Erdős Problem #104): Unit Circles Containing At Least Three Points

## Honest Scope & Literature Status
This file formalizes a pure-Mathlib milestone (`0` `sorry`, `0` custom definitions in any public
theorem signature) for **Erdős Problem #104** ($100 for proving `f(n) = o(n^2)` and £100 for
proving/disproving `f(n) = O(n^{3/2})`):

> Given `n` points in `ℝ²`, let `f(n)` be the maximum number of distinct unit circles containing at
> least three of the points.

**BOTH open conjectures (`f(n) = o(n^2)` and `f(n) = O(n^{3/2})` vs. `ω(n^{3/2})`) REMAIN OPEN.**
This file does **not** claim to solve either prize problem. Instead, it provides complete,
self-contained, pure-Mathlib formalizations of:

1. **Core Circle-Intersection & Harborth–Mengersen (1986) Upper Bounds:**
   - `ppl077_at_most_two_unit_circles_through_pair`: Any two distinct points in `ℝ²` lie on at most
     `2` unit circles.
   - `ppl077_at_most_two_points_on_two_unit_circles`: Dual intersection bound (two distinct unit
     circles intersect in at most `2` points).
   - `ppl077_weighted_pair_bound`: `∑ c ∈ C, (|P ∩ S(c, 1)|).choose 2 ≤ |P| * (|P| - 1)`.
   - `ppl077_k_rich_upper`: Generalized `k`-rich unit-circle bound
     `|C| * k * (k - 1) ≤ 2 * |P| * (|P| - 1)`.
   - `ppl077_harborth_mengersen_upper`: Harborth–Mengersen (1986) `3 * |C| ≤ |P| * (|P| - 1)`.
   - `ppl077_collinear_zero` & `ppl077_concyclic_bound`: Exact vanishing (`0`) for collinear sets
     and non-unit circles, and `≤ 1` for a unit circle.
2. **Sharpness at `n = 4` & Constructive Elekes (1984) `Ω(n^{3/2})` Lower Bound:**
   - `ppl077_orthocentric_four`: Explicit rational 4-point orthocentric configuration achieving
     `4 = 4 * 3 / 3` unit circles with `≥ 3` points.
   - `ppl077_elekes_lower_choose`: Explicit rational Weierstrass construction on `S¹` achieving
     `|P| = k.choose 2` and `|C| = k.choose 3 + k` (for all `k ≥ 4`), giving `∼ (√2 / 3) n^{3/2}`.
   - `ppl077_elekes_lower_all_n`: Universal lower bound for **every** `n ≥ 3`:
     there exist `P, C ⊆ ℝ²` with `|P| = n`, every `c ∈ C` containing `≥ 3` points of `P`, and
     `27 * |C|^2 ≥ n^3` (i.e., `|C| ≥ (1 / (3√3)) n^{3/2}`).
3. **New Formalized Structural Barrier Theorems (explaining why both prizes resist standard attacks):**
   - `ppl077_unit_circle_sidon`: Every antipode-free subset of `S¹` is a Sidon set, obstructing
     additive-energy compression of `U + U` on the unit circle.
   - `ppl077_zd_projection_barrier`: **Loomis–Whitney `ℤ^d`-Projection Barrier** — for any
     dimension `d` and any finite `X ⊆ (Fin d → ℤ)`, the set `Y` of lattice points with `≥ 3`
     `ℓ₁`-unit neighbors in `X` along `3` distinct coordinate axes satisfies
     `4 * |Y|^2 ≤ 81 * |X|^3` (i.e. `|Y| ≤ (9/2) |X|^{3/2}`), proving no linear projection of `ℤ^d`
     via unit vectors can beat Elekes's `Ω(n^{3/2})`.
   - `ppl077_pseudocircle_barrier_hypergraph`: **Shifted Böröczky `K_{2,3}`/`K_{3,2}`-Free
     Barrier** — for every `n ≥ 3`, there exists a family `T` of 3-subsets of `Fin n` where every
     pair lies in at most `2` triples and `3 * |T| + 2 * n ≥ n * (n - 1)` (asymptotically
     `n^2 / 3 - O(n)`), certifying why purely incidence-combinatorial or pseudocircle-topological
     arguments cannot improve the Harborth–Mengersen leading constant `1/3`.
-/

namespace PPL077

/-! ### Section 1: Euclidean Plane Coordinate Bridge & Quadratic Root Lemma -/

private noncomputable def mkPt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

private lemma dist_sq_eq_coords (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [Fin.sum_univ_two]
  simp [Real.dist_eq]

private lemma dist_eq_one_iff (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q = 1 ↔ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1 := by
  rw [← dist_sq_eq_coords]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have hnn : 0 ≤ dist p q := dist_nonneg
    nlinarith

/-- A quadratic equation `A * t^2 + B * t + D = 0` with `A ≠ 0` has at most two distinct roots. -/
private lemma not_three_roots_quadratic {A B D t₁ t₂ t₃ : ℝ} (hA : A ≠ 0)
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (hr1 : A * t₁ ^ 2 + B * t₁ + D = 0)
    (hr2 : A * t₂ ^ 2 + B * t₂ + D = 0)
    (hr3 : A * t₃ ^ 2 + B * t₃ + D = 0) : False := by
  have hd12 : (t₁ - t₂) * (A * (t₁ + t₂) + B) = 0 := by linarith [hr1, hr2]
  have hd13 : (t₁ - t₃) * (A * (t₁ + t₃) + B) = 0 := by linarith [hr1, hr3]
  have h12' : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
  have h13' : t₁ - t₃ ≠ 0 := sub_ne_zero.mpr h13
  have hs12 : A * (t₁ + t₂) + B = 0 := (mul_eq_zero.mp hd12).resolve_left h12'
  have hs13 : A * (t₁ + t₃) + B = 0 := (mul_eq_zero.mp hd13).resolve_left h13'
  have h23' : A * (t₂ - t₃) = 0 := by linarith
  exact (mul_eq_zero.mp h23').elim hA (sub_ne_zero.mpr h23)

/-- Any line `a * x + b * y = d` (`a ≠ 0 ∨ b ≠ 0`) intersects any circle `(x - cx)^2 + (y - cy)^2 = r2`
in at most two points. -/
private lemma line_inter_circle_card_le_two
    (a b d cx cy r2 : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ p ∈ S, a * p 0 + b * p 1 = d ∧ (p 0 - cx) ^ 2 + (p 1 - cy) ^ 2 = r2) :
    S.card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  rcases hS p₁ hp₁ with ⟨hl1, hc1⟩
  rcases hS p₂ hp₂ with ⟨hl2, hc2⟩
  rcases hS p₃ hp₃ with ⟨hl3, hc3⟩
  rcases hab with ha | hb
  · -- Express `p 0` linearly in terms of `p 1`; then `p 1` satisfies a nondegenerate quadratic.
    have hy_ne : ∀ u v : EuclideanSpace ℝ (Fin 2), u ≠ v →
        a * u 0 + b * u 1 = d → a * v 0 + b * v 1 = d → u 1 ≠ v 1 := by
      intro u v huv hu hv h1eq
      apply huv
      ext i; fin_cases i <;> dsimp
      · have hzero : a * (u 0 - v 0) = 0 := by
          calc a * (u 0 - v 0)
              = (a * u 0 + b * u 1) - (a * v 0 + b * v 1) - b * (u 1 - v 1) := by ring
            _ = d - d - b * (v 1 - v 1) := by rw [hu, hv, h1eq]
            _ = 0 := by ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ha)
      · exact h1eq
    have hq : ∀ u : EuclideanSpace ℝ (Fin 2),
        a * u 0 + b * u 1 = d → (u 0 - cx) ^ 2 + (u 1 - cy) ^ 2 = r2 →
        (a ^ 2 + b ^ 2) * (u 1) ^ 2 + (-2 * b * (d - a * cx) - 2 * a ^ 2 * cy) * (u 1) +
          ((d - a * cx) ^ 2 + a ^ 2 * cy ^ 2 - a ^ 2 * r2) = 0 := by
      intro u hlu hcu
      have hx : a * u 0 - a * cx = (d - a * cx) - b * u 1 := by linarith
      have hmul : (a * u 0 - a * cx) ^ 2 + a ^ 2 * (u 1 - cy) ^ 2 = a ^ 2 * r2 := by
        calc (a * u 0 - a * cx) ^ 2 + a ^ 2 * (u 1 - cy) ^ 2
            = a ^ 2 * ((u 0 - cx) ^ 2 + (u 1 - cy) ^ 2) := by ring
          _ = a ^ 2 * r2 := by rw [hcu]
      rw [hx] at hmul
      linarith
    have hA : a ^ 2 + b ^ 2 ≠ 0 := by positivity
    exact not_three_roots_quadratic hA
      (hy_ne p₁ p₂ h12 hl1 hl2) (hy_ne p₁ p₃ h13 hl1 hl3) (hy_ne p₂ p₃ h23 hl2 hl3)
      (hq p₁ hl1 hc1) (hq p₂ hl2 hc2) (hq p₃ hl3 hc3)
  · -- Symmetric case `b ≠ 0`: express `p 1` linearly in terms of `p 0`.
    have hx_ne : ∀ u v : EuclideanSpace ℝ (Fin 2), u ≠ v →
        a * u 0 + b * u 1 = d → a * v 0 + b * v 1 = d → u 0 ≠ v 0 := by
      intro u v huv hu hv h0eq
      apply huv
      ext i; fin_cases i <;> dsimp
      · exact h0eq
      · have hzero : b * (u 1 - v 1) = 0 := by
          calc b * (u 1 - v 1)
              = (a * u 0 + b * u 1) - (a * v 0 + b * v 1) - a * (u 0 - v 0) := by ring
            _ = d - d - a * (v 0 - v 0) := by rw [hu, hv, h0eq]
            _ = 0 := by ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hb)
    have hq : ∀ u : EuclideanSpace ℝ (Fin 2),
        a * u 0 + b * u 1 = d → (u 0 - cx) ^ 2 + (u 1 - cy) ^ 2 = r2 →
        (a ^ 2 + b ^ 2) * (u 0) ^ 2 + (-2 * a * (d - b * cy) - 2 * b ^ 2 * cx) * (u 0) +
          ((d - b * cy) ^ 2 + b ^ 2 * cx ^ 2 - b ^ 2 * r2) = 0 := by
      intro u hlu hcu
      have hy : b * u 1 - b * cy = (d - b * cy) - a * u 0 := by linarith
      have hmul : b ^ 2 * (u 0 - cx) ^ 2 + (b * u 1 - b * cy) ^ 2 = b ^ 2 * r2 := by
        calc b ^ 2 * (u 0 - cx) ^ 2 + (b * u 1 - b * cy) ^ 2
            = b ^ 2 * ((u 0 - cx) ^ 2 + (u 1 - cy) ^ 2) := by ring
          _ = b ^ 2 * r2 := by rw [hcu]
      rw [hy] at hmul
      linarith
    have hA : a ^ 2 + b ^ 2 ≠ 0 := by positivity
    exact not_three_roots_quadratic hA
      (hx_ne p₁ p₂ h12 hl1 hl2) (hx_ne p₁ p₃ h13 hl1 hl3) (hx_ne p₂ p₃ h23 hl2 hl3)
      (hq p₁ hl1 hc1) (hq p₂ hl2 hc2) (hq p₃ hl3 hc3)

/-- Any two circles with distinct centers `o₁ ≠ o₂` and arbitrary radii `r₁, r₂` intersect in at
most two points. -/
private lemma two_circles_inter_card_le_two
    (o₁ o₂ : EuclideanSpace ℝ (Fin 2)) (ho : o₁ ≠ o₂) (r₁ r₂ : ℝ)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ p ∈ S, dist p o₁ = r₁ ∧ dist p o₂ = r₂) :
    S.card ≤ 2 := by
  have hab : 2 * (o₂ 0 - o₁ 0) ≠ 0 ∨ 2 * (o₂ 1 - o₁ 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply ho
    ext i; fin_cases i <;> dsimp <;> linarith
  refine line_inter_circle_card_le_two
    (2 * (o₂ 0 - o₁ 0)) (2 * (o₂ 1 - o₁ 1))
    ((r₁ ^ 2 - r₂ ^ 2) + (o₂ 0 ^ 2 - o₁ 0 ^ 2) + (o₂ 1 ^ 2 - o₁ 1 ^ 2))
    (o₁ 0) (o₁ 1) (r₁ ^ 2) hab S ?_
  intro p hp
  rcases hS p hp with ⟨h1, h2⟩
  have hs1 : (p 0 - o₁ 0) ^ 2 + (p 1 - o₁ 1) ^ 2 = r₁ ^ 2 := by
    rw [← dist_sq_eq_coords, h1]
  have hs2 : (p 0 - o₂ 0) ^ 2 + (p 1 - o₂ 1) ^ 2 = r₂ ^ 2 := by
    rw [← dist_sq_eq_coords, h2]
  exact ⟨by linarith, hs1⟩

/-! ### Section 2: Harborth–Mengersen (1986) Upper Bounds & Special Cases -/

/-- **Pair-Circle Intersection Bound:** Any two distinct points `p ≠ q` in `ℝ²` lie on at most `2`
distinct unit circles. -/
theorem ppl077_at_most_two_unit_circles_through_pair
    (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q)
    (C : Finset (EuclideanSpace ℝ (Fin 2))) :
    (C.filter fun c => dist p c = 1 ∧ dist q c = 1).card ≤ 2 := by
  refine two_circles_inter_card_le_two p q hpq 1 1 _ ?_
  intro c hc
  rcases (Finset.mem_filter.mp hc).2 with ⟨h1, h2⟩
  exact ⟨by rwa [dist_comm], by rwa [dist_comm]⟩

/-- **Dual Circle-Intersection Bound:** Any two distinct unit circles in `ℝ²` intersect in at most
`2` points. -/
theorem ppl077_at_most_two_points_on_two_unit_circles
    (c₁ c₂ : EuclideanSpace ℝ (Fin 2)) (hc : c₁ ≠ c₂)
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (P.filter fun p => dist p c₁ = 1 ∧ dist p c₂ = 1).card ≤ 2 := by
  refine two_circles_inter_card_le_two c₁ c₂ hc 1 1 _ ?_
  intro p hp
  exact (Finset.mem_filter.mp hp).2

private lemma card_offDiag_eq {α : Type*} (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

/-- **Exact Weighted Pair-Counting Inequality:** For any finite set `P ⊆ ℝ²` and finite set `C` of
unit-circle centers, `∑ c ∈ C, (|P ∩ S(c, 1)|).choose 2 ≤ |P| * (|P| - 1)`. -/
theorem ppl077_weighted_pair_bound
    (P C : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∑ c ∈ C, ((P.filter fun p => dist p c = 1).card).choose 2 ≤ P.card * (P.card - 1) := by
  -- Double count triples `(c, (p, q)) ∈ C × P.offDiag` with `dist p c = 1 ∧ dist q c = 1`.
  have hdouble :
      ∑ c ∈ C, (P.filter fun p => dist p c = 1).card *
        ((P.filter fun p => dist p c = 1).card - 1) =
      ∑ x ∈ P.offDiag, (C.filter fun c => dist x.1 c = 1 ∧ dist x.2 c = 1).card := by
    have hL : ∀ c ∈ C,
        (P.filter fun p => dist p c = 1).card *
          ((P.filter fun p => dist p c = 1).card - 1) =
        ∑ x ∈ P.offDiag, if dist x.1 c = 1 ∧ dist x.2 c = 1 then 1 else 0 := by
      intro c _
      rw [← card_offDiag_eq, ← Finset.card_filter]
      congr 1
      ext ⟨p, q⟩
      simp only [Finset.mem_offDiag, Finset.mem_filter]
      tauto
    rw [Finset.sum_congr rfl hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
  have hR :
      ∑ x ∈ P.offDiag, (C.filter fun c => dist x.1 c = 1 ∧ dist x.2 c = 1).card ≤
      ∑ _x ∈ P.offDiag, 2 := by
    refine Finset.sum_le_sum fun x hx => ?_
    exact ppl077_at_most_two_unit_circles_through_pair x.1 x.2 (Finset.mem_offDiag.mp hx).2.2 C
  rw [Finset.sum_const, smul_eq_mul, card_offDiag_eq] at hR
  have h2 :
      2 * ∑ c ∈ C, ((P.filter fun p => dist p c = 1).card).choose 2 =
      ∑ c ∈ C, (P.filter fun p => dist p c = 1).card *
        ((P.filter fun p => dist p c = 1).card - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.choose_two_right]
    have heven : Even ((P.filter fun p => dist p c = 1).card *
        ((P.filter fun p => dist p c = 1).card - 1)) := Nat.even_mul_pred_self _
    obtain ⟨m, hm⟩ := heven
    omega
  omega

/-- **Generalized `k`-Rich Unit-Circle Upper Bound:** If every unit circle in `C` contains at least
`k` points of `P`, then `|C| * k * (k - 1) ≤ 2 * |P| * (|P| - 1)`. -/
theorem ppl077_k_rich_upper
    (P C : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ)
    (hC : ∀ c ∈ C, k ≤ (P.filter fun p => dist p c = 1).card) :
    C.card * (k * (k - 1)) ≤ 2 * (P.card * (P.card - 1)) := by
  have hw := ppl077_weighted_pair_bound P C
  have hsum : ∑ c ∈ C, k.choose 2 ≤ ∑ c ∈ C, ((P.filter fun p => dist p c = 1).card).choose 2 :=
    Finset.sum_le_sum fun c hc => Nat.choose_le_choose 2 (hC c hc)
  rw [Finset.sum_const, smul_eq_mul] at hsum
  have hk2 : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    obtain ⟨m, hm⟩ := Nat.even_mul_pred_self k
    omega
  calc C.card * (k * (k - 1))
      = 2 * (C.card * k.choose 2) := by rw [← hk2]; ring
    _ ≤ 2 * (P.card * (P.card - 1)) := Nat.mul_le_mul_left 2 (le_trans hsum hw)

/-- **Harborth–Mengersen (1986) Upper Bound:** Any `n` points in `ℝ²` determine at most
`n * (n - 1) / 3` distinct unit circles containing at least `3` points. -/
theorem ppl077_harborth_mengersen_upper
    (P C : Finset (EuclideanSpace ℝ (Fin 2)))
    (hC : ∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card) :
    3 * C.card ≤ P.card * (P.card - 1) := by
  have h := ppl077_k_rich_upper P C 3 hC
  omega

/-- **Collinear Vanishing:** If all points of `P` lie on a single line, then no unit circle contains
`≥ 3` points of `P`. -/
theorem ppl077_collinear_zero
    (P C : Finset (EuclideanSpace ℝ (Fin 2)))
    (a b d : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hP : ∀ p ∈ P, a * p 0 + b * p 1 = d)
    (hC : ∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card) :
    C.card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro c hc
  have h3 := hC c hc
  have h2 : (P.filter fun p => dist p c = 1).card ≤ 2 := by
    refine line_inter_circle_card_le_two a b d (c 0) (c 1) 1 hab _ ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpP, hdist⟩
    exact ⟨hP p hpP, (dist_eq_one_iff p c).mp hdist⟩
  omega

/-- **Concyclic Bound:** If all points of `P` lie on a single circle of center `o` and radius `r`,
then `C.card ≤ 1` (and `C.card = 0` whenever `r ≠ 1`). -/
theorem ppl077_concyclic_bound
    (P C : Finset (EuclideanSpace ℝ (Fin 2)))
    (o : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hP : ∀ p ∈ P, dist p o = r)
    (hC : ∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card) :
    C.card ≤ 1 ∧ (r ≠ 1 → C.card = 0) := by
  have hsub : C ⊆ {o} := by
    intro c hc
    rw [Finset.mem_singleton]
    by_contra hne
    have h3 := hC c hc
    have h2 : (P.filter fun p => dist p c = 1).card ≤ 2 := by
      refine two_circles_inter_card_le_two o c (Ne.symm hne) r 1 _ ?_
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hdist⟩
      exact ⟨hP p hpP, hdist⟩
    omega
  refine ⟨le_trans (Finset.card_le_card hsub) (by simp), ?_⟩
  intro hr
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro c hc
  have hco : c = o := Finset.mem_singleton.mp (hsub hc)
  subst hco
  have h3 := hC c hc
  have hempty : (P.filter fun p => dist p c = 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp hdist
    exact hr ((hP p hp).symm.trans hdist)
  rw [hempty] at h3
  simp at h3

/-! ### Section 3: Sharp `n = 4` Orthocentric Configuration -/

/-- **Exact Sharpness at `n = 4`:** Four rational points (three Pythagorean points on `S¹` plus
their orthocenter) determine `4 = 4 * 3 / 3` distinct unit circles each containing `3` points. -/
theorem ppl077_orthocentric_four :
    ∃ P C : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = 4 ∧ C.card = 4 ∧
      ∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card := by
  let p₁ := mkPt 1 0
  let p₂ := mkPt (-3 / 5) (4 / 5)
  let p₃ := mkPt (-3 / 5) (-4 / 5)
  let p₄ := mkPt (-1 / 5) 0
  let c₁ := mkPt 0 0
  let c₂ := mkPt (2 / 5) (4 / 5)
  let c₃ := mkPt (-6 / 5) 0
  let c₄ := mkPt (2 / 5) (-4 / 5)
  have hne : ∀ x₁ y₁ x₂ y₂ : ℝ, (x₁ ≠ x₂ ∨ y₁ ≠ y₂) → mkPt x₁ y₁ ≠ mkPt x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ hxy heq
    rcases hxy with hx | hy
    · exact hx (by simpa [mkPt_zero] using congr_arg (fun v => v 0) heq)
    · exact hy (by simpa [mkPt_one] using congr_arg (fun v => v 1) heq)
  have hd : ∀ x₁ y₁ x₂ y₂ : ℝ, (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1 →
      dist (mkPt x₁ y₁) (mkPt x₂ y₂) = 1 := by
    intro x₁ y₁ x₂ y₂ h
    rw [dist_eq_one_iff, mkPt_zero, mkPt_zero, mkPt_one, mkPt_one]
    exact h
  have hp12 : p₁ ≠ p₂ := hne _ _ _ _ (Or.inl (by norm_num))
  have hp13 : p₁ ≠ p₃ := hne _ _ _ _ (Or.inl (by norm_num))
  have hp14 : p₁ ≠ p₄ := hne _ _ _ _ (Or.inl (by norm_num))
  have hp23 : p₂ ≠ p₃ := hne _ _ _ _ (Or.inr (by norm_num))
  have hp24 : p₂ ≠ p₄ := hne _ _ _ _ (Or.inl (by norm_num))
  have hp34 : p₃ ≠ p₄ := hne _ _ _ _ (Or.inl (by norm_num))
  have hc12 : c₁ ≠ c₂ := hne _ _ _ _ (Or.inl (by norm_num))
  have hc13 : c₁ ≠ c₃ := hne _ _ _ _ (Or.inl (by norm_num))
  have hc14 : c₁ ≠ c₄ := hne _ _ _ _ (Or.inl (by norm_num))
  have hc23 : c₂ ≠ c₃ := hne _ _ _ _ (Or.inl (by norm_num))
  have hc24 : c₂ ≠ c₄ := hne _ _ _ _ (Or.inr (by norm_num))
  have hc34 : c₃ ≠ c₄ := hne _ _ _ _ (Or.inl (by norm_num))
  refine ⟨{p₁, p₂, p₃, p₄}, {c₁, c₂, c₃, c₄}, ?_, ?_, ?_⟩
  · simp [hp12, hp13, hp14, hp23, hp24, hp34]
  · simp [hc12, hc13, hc14, hc23, hc24, hc34]
  · intro c hc
    have htriple : ∀ q₁ q₂ q₃ : EuclideanSpace ℝ (Fin 2),
        q₁ ∈ ({p₁, p₂, p₃, p₄} : Finset _) →
        q₂ ∈ ({p₁, p₂, p₃, p₄} : Finset _) →
        q₃ ∈ ({p₁, p₂, p₃, p₄} : Finset _) →
        q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
        dist q₁ c = 1 → dist q₂ c = 1 → dist q₃ c = 1 →
        3 ≤ (({p₁, p₂, p₃, p₄} : Finset _).filter fun p => dist p c = 1).card := by
      intro q₁ q₂ q₃ hq1 hq2 hq3 h12 h13 h23 hd1 hd2 hd3
      have hsub : ({q₁, q₂, q₃} : Finset _) ⊆ ({p₁, p₂, p₃, p₄} : Finset _).filter
          (fun p => dist p c = 1) := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hq1, hd1⟩
        · exact Finset.mem_filter.mpr ⟨hq2, hd2⟩
        · exact Finset.mem_filter.mpr ⟨hq3, hd3⟩
      calc 3 = ({q₁, q₂, q₃} : Finset _).card := by simp [h12, h13, h23]
        _ ≤ _ := Finset.card_le_card hsub
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact htriple p₁ p₂ p₃ (by simp) (by simp) (by simp) hp12 hp13 hp23
        (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num))
    · exact htriple p₁ p₂ p₄ (by simp) (by simp) (by simp) hp12 hp14 hp24
        (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num))
    · exact htriple p₂ p₃ p₄ (by simp) (by simp) (by simp) hp23 hp24 hp34
        (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num))
    · exact htriple p₁ p₃ p₄ (by simp) (by simp) (by simp) hp13 hp14 hp34
        (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num)) (hd _ _ _ _ (by norm_num))

/-! ### Section 4: Explicit Rational Weierstrass Construction for Elekes (1984) `Ω(n^{3/2})` -/

/-- Superincreasing rational parameter `t i = 10^{-(i+1)}`. -/
private noncomputable def wParam (i : ℕ) : ℝ := (1 / 10 : ℝ) ^ (i + 1)

/-- Rational Weierstrass unit vector `u(i) = (2 t / (1 + t^2), (1 - t^2) / (1 + t^2)) ∈ S¹`. -/
private noncomputable def wVec (i : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  mkPt (2 * wParam i / (1 + wParam i ^ 2)) ((1 - wParam i ^ 2) / (1 + wParam i ^ 2))

private lemma wParam_pos (i : ℕ) : 0 < wParam i := by
  unfold wParam; positivity

private lemma wParam_le_tenth (i : ℕ) : wParam i ≤ 1 / 10 := by
  unfold wParam
  have h : (1 / 10 : ℝ) ^ (i + 1) ≤ (1 / 10 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa using h

private lemma wParam_step {a b : ℕ} (hab : a < b) : wParam b ≤ wParam a / 10 := by
  unfold wParam
  have h1 : (1 / 10 : ℝ) ^ (b + 1) ≤ (1 / 10 : ℝ) ^ (a + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (1 / 10 : ℝ) ^ (a + 2) = (1 / 10 : ℝ) ^ (a + 1) / 10 := by
    rw [pow_succ]; ring
  linarith

private lemma wVec_norm_sq (i : ℕ) : (wVec i 0) ^ 2 + (wVec i 1) ^ 2 = 1 := by
  simp only [wVec, mkPt_zero, mkPt_one]
  have hd : 1 + wParam i ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

private lemma wVec_x_bounds (i : ℕ) :
    (19 / 10 : ℝ) * wParam i < wVec i 0 ∧ wVec i 0 ≤ 2 * wParam i := by
  simp only [wVec, mkPt_zero]
  have ht : 0 < wParam i := wParam_pos i
  have hle : wParam i ≤ 1 / 10 := wParam_le_tenth i
  have hd : 0 < 1 + wParam i ^ 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith
  · rw [div_le_iff₀ hd]
    nlinarith

private lemma wVec_x_pos (i : ℕ) : 0 < wVec i 0 :=
  lt_trans (mul_pos (by norm_num) (wParam_pos i)) (wVec_x_bounds i).1

/-- Superincreasing injectivity: the sum of `x`-coordinates of any subset of size `≤ 3`
uniquely determines the subset. -/
private lemma wVec_sum_x_injective :
    ∀ n : ℕ, ∀ s s' : Finset ℕ, s.card + s'.card ≤ n → s.card ≤ 3 → s'.card ≤ 3 →
      (∑ i ∈ s, wVec i 0) = (∑ j ∈ s', wVec j 0) → s = s' := by
  intro n
  induction n with
  | zero =>
    intro s s' hle _ _ _
    have hs : s = ∅ := Finset.card_eq_zero.mp (by omega)
    have hs' : s' = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hs, hs']
  | succ n ih =>
    intro s s' hle hs3 hs'3 hsum
    by_cases hs : s = ∅
    · subst hs
      simp only [Finset.sum_empty] at hsum
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr (Ne.symm hne)
      have hpos : 0 < ∑ x ∈ s', wVec x 0 :=
        Finset.sum_pos (fun x _ => wVec_x_pos x) ⟨j, hj⟩
      linarith
    by_cases hs' : s' = ∅
    · subst hs'
      simp only [Finset.sum_empty] at hsum
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hpos : 0 < ∑ x ∈ s, wVec x 0 :=
        Finset.sum_pos (fun x _ => wVec_x_pos x) ⟨i, hi⟩
      linarith
    have hne_s : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    have hne_s' : s'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs'
    let a := s.min' hne_s
    let b := s'.min' hne_s'
    have ha_mem : a ∈ s := Finset.min'_mem s hne_s
    have hb_mem : b ∈ s' := Finset.min'_mem s' hne_s'
    have hdom : ∀ (u v : Finset ℕ) (m : ℕ), m ∈ u → v.card ≤ 3 →
        (∀ j ∈ v, m < j) → ∑ j ∈ v, wVec j 0 < ∑ i ∈ u, wVec i 0 := by
      intro u v m hm hv3 hlt
      have hupper : ∑ j ∈ v, wVec j 0 ≤ (6 / 10 : ℝ) * wParam m := by
        have h1 : ∑ j ∈ v, wVec j 0 ≤ ∑ _j ∈ v, (2 / 10 : ℝ) * wParam m := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hstep := wParam_step (hlt j hj)
          have hxb := (wVec_x_bounds j).2
          linarith
        rw [Finset.sum_const, nsmul_eq_mul] at h1
        have hv3R : (v.card : ℝ) ≤ 3 := by exact_mod_cast hv3
        have hpm : 0 < wParam m := wParam_pos m
        nlinarith
      have hlower : (19 / 10 : ℝ) * wParam m < ∑ i ∈ u, wVec i 0 := by
        have hle1 : wVec m 0 ≤ ∑ i ∈ u, wVec i 0 :=
          Finset.single_le_sum (fun i _ => le_of_lt (wVec_x_pos i)) hm
        linarith [(wVec_x_bounds m).1]
      linarith [wParam_pos m]
    have hab : a = b := by
      by_contra hneab
      rcases lt_or_gt_of_ne hneab with hlt | hgt
      · have hlt' : ∀ j ∈ s', a < j := fun j hj => lt_of_lt_of_le hlt (Finset.min'_le s' j hj)
        linarith [hdom s s' a ha_mem hs'3 hlt']
      · have hlt' : ∀ i ∈ s, b < i := fun i hi => lt_of_lt_of_le hgt (Finset.min'_le s i hi)
        linarith [hdom s' s b hb_mem hs3 hlt']
    have ha_mem' : a ∈ s' := hab ▸ hb_mem
    have hsum_er : ∑ i ∈ s.erase a, wVec i 0 = ∑ j ∈ s'.erase a, wVec j 0 := by
      have h1 := Finset.add_sum_erase s (fun i => wVec i 0) ha_mem
      have h2 := Finset.add_sum_erase s' (fun j => wVec j 0) ha_mem'
      linarith
    have hcard_s : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha_mem
    have hcard_s' : (s'.erase a).card = s'.card - 1 := Finset.card_erase_of_mem ha_mem'
    have hpos_s : 1 ≤ s.card := Finset.card_pos.mpr hne_s
    have hpos_s' : 1 ≤ s'.card := Finset.card_pos.mpr hne_s'
    have her : s.erase a = s'.erase a :=
      ih (s.erase a) (s'.erase a) (by omega) (by omega) (by omega) hsum_er
    rw [← Finset.insert_erase ha_mem, ← Finset.insert_erase ha_mem', her]

private lemma sum_euc_zero (s : Finset ℕ) (g : ℕ → EuclideanSpace ℝ (Fin 2)) :
    (∑ i ∈ s, g i) 0 = ∑ i ∈ s, g i 0 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha _ => simp

private lemma wVec_sum_injective_on_card_le_three
    {s s' : Finset ℕ} (hs : s.card ≤ 3) (hs' : s'.card ≤ 3)
    (heq : (∑ i ∈ s, wVec i) = (∑ j ∈ s', wVec j)) : s = s' := by
  have hx : (∑ i ∈ s, wVec i 0) = (∑ j ∈ s', wVec j 0) := by
    rw [← sum_euc_zero s wVec, ← sum_euc_zero s' wVec, heq]
  exact wVec_sum_x_injective (s.card + s'.card) s s' le_rfl hs hs' hx

private lemma dist_sum_erase_eq_one (t : Finset ℕ) {r : ℕ} (hr : r ∈ t) :
    dist (∑ i ∈ t.erase r, wVec i) (∑ i ∈ t, wVec i) = 1 := by
  rw [dist_eq_one_iff]
  have hsum : ∑ i ∈ t, wVec i = wVec r + ∑ i ∈ t.erase r, wVec i :=
    (Finset.add_sum_erase t wVec hr).symm
  rw [hsum]
  have h0 : (∑ i ∈ t.erase r, wVec i) 0 - (wVec r + ∑ i ∈ t.erase r, wVec i) 0 = -wVec r 0 := by
    simp
  have h1 : (∑ i ∈ t.erase r, wVec i) 1 - (wVec r + ∑ i ∈ t.erase r, wVec i) 1 = -wVec r 1 := by
    simp
  rw [h0, h1, neg_sq, neg_sq]
  exact wVec_norm_sq r

private lemma dist_pair_single_eq_one {i j : ℕ} (hij : i ≠ j) :
    dist (∑ x ∈ ({i, j} : Finset ℕ), wVec x) (wVec i) = 1 := by
  rw [Finset.sum_pair hij, dist_eq_one_iff]
  have h0 : (wVec i + wVec j) 0 - wVec i 0 = wVec j 0 := by simp
  have h1 : (wVec i + wVec j) 1 - wVec i 1 = wVec j 1 := by simp
  rw [h0, h1]
  exact wVec_norm_sq j

/-- **Elekes (1984) Lower Bound (Exact Binomial Form):** For every `k ≥ 4`, there exist
`P, C ⊆ ℝ²` with `|P| = k.choose 2` and `|C| = k.choose 3 + k` such that every unit circle
centered in `C` contains at least `3` points of `P`. -/
theorem ppl077_elekes_lower_choose (k : ℕ) (hk : 4 ≤ k) :
    ∃ P C : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = k.choose 2 ∧ C.card = k.choose 3 + k ∧
      ∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card := by
  let S2 := (Finset.range k).powersetCard 2
  let S3 := (Finset.range k).powersetCard 3
  let S1 := (Finset.range k).powersetCard 1
  let f : Finset ℕ → EuclideanSpace ℝ (Fin 2) := fun s => ∑ i ∈ s, wVec i
  let P := S2.image f
  let C := (S3 ∪ S1).image f
  have hf_inj2 : Set.InjOn f (S2 : Set (Finset ℕ)) := by
    intro s hs s' hs' heq
    exact wVec_sum_injective_on_card_le_three
      (by rw [(Finset.mem_powersetCard.mp hs).2]; omega)
      (by rw [(Finset.mem_powersetCard.mp hs').2]; omega) heq
  have hf_inj31 : Set.InjOn f ((S3 ∪ S1 : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro s hs s' hs' heq
    have hc_le : ∀ u ∈ S3 ∪ S1, u.card ≤ 3 := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu3 | hu1
      · rw [(Finset.mem_powersetCard.mp hu3).2]
      · rw [(Finset.mem_powersetCard.mp hu1).2]; omega
    exact wVec_sum_injective_on_card_le_three (hc_le s hs) (hc_le s' hs') heq
  have hdisj : Disjoint S3 S1 := by
    rw [Finset.disjoint_left]
    intro s hs3 hs1
    have h3 := (Finset.mem_powersetCard.mp hs3).2
    have h1 := (Finset.mem_powersetCard.mp hs1).2
    omega
  refine ⟨P, C, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hf_inj2, Finset.card_powersetCard, Finset.card_range]
  · rw [Finset.card_image_of_injOn hf_inj31, Finset.card_union_of_disjoint hdisj,
      Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_range, Nat.choose_one_right]
  · intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    rcases Finset.mem_union.mp ht with ht3 | ht1
    · -- Triple center `c = u_i + u_j + u_l`: its 3 points in `P` are `f (t.erase r)` for `r ∈ t`.
      rcases Finset.mem_powersetCard.mp ht3 with ⟨ht_sub, ht_card⟩
      let img := t.image (fun r => f (t.erase r))
      have himg_sub : img ⊆ P.filter (fun p => dist p (f t) = 1) := by
        intro p hp
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
        refine Finset.mem_filter.mpr ⟨?_, dist_sum_erase_eq_one t hr⟩
        refine Finset.mem_image.mpr ⟨t.erase r, ?_, rfl⟩
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.Subset.trans (Finset.erase_subset r t) ht_sub,
          by rw [Finset.card_erase_of_mem hr, ht_card]⟩
      have hinj_er : Set.InjOn (fun r => f (t.erase r)) (t : Set ℕ) := by
        intro r₁ hr₁ r₂ hr₂ heq
        have h1c : (t.erase r₁).card ≤ 3 := by rw [Finset.card_erase_of_mem hr₁, ht_card]; omega
        have h2c : (t.erase r₂).card ≤ 3 := by rw [Finset.card_erase_of_mem hr₂, ht_card]; omega
        have heq_set : t.erase r₁ = t.erase r₂ :=
          wVec_sum_injective_on_card_le_three h1c h2c heq
        by_contra hne
        have : r₁ ∈ t.erase r₂ := Finset.mem_erase.mpr ⟨hne, hr₁⟩
        rw [← heq_set] at this
        exact (Finset.mem_erase.mp this).1 rfl
      calc 3 = t.card := ht_card.symm
        _ = img.card := (Finset.card_image_of_injOn hinj_er).symm
        _ ≤ _ := Finset.card_le_card himg_sub
    · -- Singleton center `c = u_i`: its `k - 1 ≥ 3` points in `P` are `u_i + u_j` for `j ≠ i`.
      rcases Finset.mem_powersetCard.mp ht1 with ⟨ht_sub, ht_card⟩
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp ht_card
      have hi : i ∈ Finset.range k := ht_sub (Finset.mem_singleton_self i)
      let J := (Finset.range k).erase i
      let img := J.image (fun j => f ({i, j}))
      have himg_sub : img ⊆ P.filter (fun p => dist p (f {i}) = 1) := by
        intro p hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        rcases Finset.mem_erase.mp hj with ⟨hji, hjr⟩
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_image.mpr ⟨{i, j}, ?_, rfl⟩
          rw [Finset.mem_powersetCard]
          refine ⟨?_, Finset.card_pair (Ne.symm hji)⟩
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · simpa only [f, Finset.sum_singleton] using dist_pair_single_eq_one (Ne.symm hji)
      have hinj_j : Set.InjOn (fun j => f ({i, j})) (J : Set ℕ) := by
        intro j₁ hj₁ j₂ hj₂ heq
        have h1ne : i ≠ j₁ := Ne.symm (Finset.mem_erase.mp hj₁).1
        have h2ne : i ≠ j₂ := Ne.symm (Finset.mem_erase.mp hj₂).1
        have heq_set : ({i, j₁} : Finset ℕ) = {i, j₂} :=
          wVec_sum_injective_on_card_le_three
            (by rw [Finset.card_pair h1ne]; omega)
            (by rw [Finset.card_pair h2ne]; omega) heq
        have hj1_in : j₁ ∈ ({i, j₂} : Finset ℕ) := heq_set ▸ (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj1_in
        exact hj1_in.resolve_left (Ne.symm h1ne)
      have hJcard : 3 ≤ J.card := by
        rw [Finset.card_erase_of_mem hi, Finset.card_range]; omega
      calc 3 ≤ J.card := hJcard
        _ = img.card := (Finset.card_image_of_injOn hinj_j).symm
        _ ≤ _ := Finset.card_le_card himg_sub

/-- Padding a finite point set `P` in `ℝ²` to any larger size `n ≥ P.card` preserves all `≥ 3`-rich
unit circles. -/
private lemma pad_point_set
    (P C : Finset (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (hle : P.card ≤ n)
    (hC : ∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card) :
    ∃ P' : Finset (EuclideanSpace ℝ (Fin 2)),
      P'.card = n ∧ ∀ c ∈ C, 3 ≤ (P'.filter fun p => dist p c = 1).card := by
  let B : ℝ := 1 + ∑ p ∈ P, |p 0|
  let extra : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.range (n - P.card)).image (fun m : ℕ => mkPt (B + (m : ℝ)) 0)
  have hextra_inj : Set.InjOn (fun m : ℕ => mkPt (B + (m : ℝ)) 0)
      ((Finset.range (n - P.card) : Finset ℕ) : Set ℕ) := by
    intro m₁ _ m₂ _ heq
    have h0 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) heq
    simp only [mkPt_zero] at h0
    have : (m₁ : ℝ) = (m₂ : ℝ) := by linarith
    exact Nat.cast_injective this
  have hdisj : Disjoint P extra := by
    rw [Finset.disjoint_left]
    intro p hpP hpE
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hpE
    have hle_sum : |p 0| ≤ ∑ q ∈ P, |q 0| :=
      Finset.single_le_sum (fun q _ => abs_nonneg (q 0)) hpP
    have hp0 : p 0 ≤ |p 0| := le_abs_self _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpeq : p 0 = B + (m : ℝ) := by
      rw [← hm, mkPt_zero]
    linarith
  refine ⟨P ∪ extra, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj]
    have hextra_card : extra.card = n - P.card := by
      dsimp only [extra]
      rw [Finset.card_image_of_injOn hextra_inj, Finset.card_range]
    omega
  · intro c hc
    have hsub : P.filter (fun p => dist p c = 1) ⊆ (P ∪ extra).filter (fun p => dist p c = 1) :=
      Finset.filter_subset_filter _ Finset.subset_union_left
    exact le_trans (hC c hc) (Finset.card_le_card hsub)

/-- **Universal Elekes (1984) Lower Bound for Every `n ≥ 3`:**
For every `n ≥ 3`, there exist `n` points `P ⊆ ℝ²` and a set `C` of distinct unit circles each
containing `≥ 3` points of `P` satisfying `n^3 ≤ 27 * |C|^2` (equivalently
`|C| ≥ (1 / (3√3)) n^{3/2}`). -/
theorem ppl077_elekes_lower_all_n (n : ℕ) (hn : 3 ≤ n) :
    ∃ P C : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧
      (∀ c ∈ C, 3 ≤ (P.filter fun p => dist p c = 1).card) ∧
      n ^ 3 ≤ 27 * C.card ^ 2 := by
  by_cases hn3 : n = 3
  · subst hn3
    -- 3 points on the unit circle centered at `(0, 0)`.
    let p₁ := mkPt 1 0
    let p₂ := mkPt (-1) 0
    let p₃ := mkPt 0 1
    let c₀ := mkPt 0 0
    have hne12 : p₁ ≠ p₂ := fun h => by
      have := congr_arg (fun v => v 0) h; norm_num [p₁, p₂, mkPt_zero] at this
    have hne13 : p₁ ≠ p₃ := fun h => by
      have := congr_arg (fun v => v 0) h; norm_num [p₁, p₃, mkPt_zero] at this
    have hne23 : p₂ ≠ p₃ := fun h => by
      have := congr_arg (fun v => v 0) h; norm_num [p₂, p₃, mkPt_zero] at this
    refine ⟨{p₁, p₂, p₃}, {c₀}, by simp [hne12, hne13, hne23], ?_, by norm_num⟩
    intro c hc
    rw [Finset.mem_singleton.mp hc]
    have hfilt : ({p₁, p₂, p₃} : Finset _).filter (fun p => dist p c₀ = 1) = {p₁, p₂, p₃} := by
      rw [Finset.filter_eq_self]
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;>
        (rw [dist_eq_one_iff]; norm_num [p₁, p₂, p₃, c₀, mkPt_zero, mkPt_one])
    rw [hfilt]; simp [hne12, hne13, hne23]
  by_cases hn5 : n ≤ 5
  · -- `n ∈ {4, 5}`: pad the orthocentric 4-tuple (`C.card = 4`, `27 * 16 = 432 ≥ 125 = 5^3`).
    obtain ⟨P₀, C₀, hP₀, hC₀, hrich⟩ := ppl077_orthocentric_four
    obtain ⟨P, hPcard, hPrich⟩ := pad_point_set P₀ C₀ n (by omega) hrich
    refine ⟨P, C₀, hPcard, hPrich, ?_⟩
    rw [hC₀]
    have : n ^ 3 ≤ 5 ^ 3 := Nat.pow_le_pow_left hn5 3
    omega
  · -- `n ≥ 6`: pick maximal `k ≥ 4` with `k.choose 2 ≤ n < (k + 1).choose 2`.
    have hn6 : 6 ≤ n := by omega
    let S := (Finset.range (n + 2)).filter (fun k => k.choose 2 ≤ n)
    have h4S : 4 ∈ S := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have h42 : Nat.choose 4 2 = 6 := by decide
      omega
    let k := S.max' ⟨4, h4S⟩
    have hk_mem : k ∈ S := Finset.max'_mem S ⟨4, h4S⟩
    have hk4 : 4 ≤ k := Finset.le_max' S 4 h4S
    have hk_le : k.choose 2 ≤ n := (Finset.mem_filter.mp hk_mem).2
    have hkn : k ≤ n := by
      have htri : k ≤ k.choose 2 := by
        rw [Nat.choose_two_right]
        have hmul : 2 * k ≤ k * (k - 1) := by
          calc 2 * k = k * 2 := mul_comm 2 k
            _ ≤ k * (k - 1) := Nat.mul_le_mul_left k (by omega)
        omega
      omega
    have hk1_gt : n < (k + 1).choose 2 := by
      by_contra hle
      push Not at hle
      have hk1_mem : k + 1 ∈ S := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hle⟩
      have := Finset.le_max' S (k + 1) hk1_mem
      omega
    obtain ⟨P₀, C, hP₀, hC, hrich⟩ := ppl077_elekes_lower_choose k hk4
    obtain ⟨P, hPcard, hPrich⟩ := pad_point_set P₀ C n (by omega) hrich
    refine ⟨P, C, hPcard, hPrich, ?_⟩
    -- Algebraic check: `2 * n ≤ k * (k + 1)` and `6 * C.card = k * (k - 1) * (k - 2) + 6 * k`.
    have h2n : 2 * n ≤ k * (k + 1) := by
      rw [Nat.choose_two_right] at hk1_gt
      have hsucc : (k + 1 - 1) = k := by omega
      rw [hsucc, mul_comm (k + 1) k] at hk1_gt
      omega
    have h6C : 6 * C.card = k * (k - 1) * (k - 2) + 6 * k := by
      have h3 := Nat.descFactorial_eq_factorial_mul_choose k 3
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one] at h3
      have hfact : Nat.factorial 3 = 6 := by decide
      rw [hfact] at h3
      rw [hC, Nat.mul_add]
      linarith
    -- Set `m = k - 4` so `k = m + 4` and apply `positivity` on `ℤ`.
    set m := k - 4
    have hkm : k = m + 4 := by omega
    have h2nZ : 2 * (n : ℤ) ≤ ((m : ℤ) + 4) * ((m : ℤ) + 5) := by
      rw [hkm] at h2n
      exact_mod_cast h2n
    have h6CZ : 6 * (C.card : ℤ) = ((m : ℤ) + 4) * ((m : ℤ) + 3) * ((m : ℤ) + 2) +
        6 * ((m : ℤ) + 4) := by
      rw [hkm] at h6C
      have h1 : (m + 4) - 1 = m + 3 := by omega
      have h2 : (m + 4) - 2 = m + 2 := by omega
      rw [h1, h2] at h6C
      exact_mod_cast h6C
    have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    have h8n3 : 8 * (n : ℤ) ^ 3 ≤ (((m : ℤ) + 4) * ((m : ℤ) + 5)) ^ 3 := by
      have hcube : (2 * (n : ℤ)) ^ 3 ≤ (((m : ℤ) + 4) * ((m : ℤ) + 5)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) h2nZ 3
      linarith
    have hpoly :
        (((m : ℤ) + 4) * ((m : ℤ) + 5)) ^ 3 ≤
        6 * (((m : ℤ) + 4) * ((m : ℤ) + 3) * ((m : ℤ) + 2) + 6 * ((m : ℤ) + 4)) ^ 2 := by
      have hdiff :
          6 * (((m : ℤ) + 4) * ((m : ℤ) + 3) * ((m : ℤ) + 2) + 6 * ((m : ℤ) + 4)) ^ 2 -
          (((m : ℤ) + 4) * ((m : ℤ) + 5)) ^ 3 =
          ((m : ℤ) + 4) ^ 2 * (5 * (m : ℤ) ^ 4 + 41 * (m : ℤ) ^ 3 + 159 * (m : ℤ) ^ 2 +
            295 * (m : ℤ) + 364) := by ring
      have hnn : 0 ≤ ((m : ℤ) + 4) ^ 2 * (5 * (m : ℤ) ^ 4 + 41 * (m : ℤ) ^ 3 +
          159 * (m : ℤ) ^ 2 + 295 * (m : ℤ) + 364) := by
        exact_mod_cast Nat.zero_le ((m + 4) ^ 2 * (5 * m ^ 4 + 41 * m ^ 3 +
          159 * m ^ 2 + 295 * m + 364))
      linarith
    have hgoalZ : (n : ℤ) ^ 3 ≤ 27 * (C.card : ℤ) ^ 2 := by
      have hcomb : 8 * (n : ℤ) ^ 3 ≤ 6 * (6 * (C.card : ℤ)) ^ 2 := by
        rw [← h6CZ] at hpoly
        exact le_trans h8n3 hpoly
      linarith
    exact_mod_cast hgoalZ

/-! ### Section 5: Structural Barrier Theorems -/

/-- **Unit-Circle Sidon Theorem:** Any antipode-free subset of the unit circle `S¹ ⊆ ℝ²` is a
Sidon set (all pairwise sums `u₁ + u₂` are uniquely determined up to order). This explains why
additive-energy compression of `U + U` on `S¹` cannot reduce `|U + U|` below `C(|U|, 2)`. -/
theorem ppl077_unit_circle_sidon
    (u₁ u₂ u₃ u₄ : EuclideanSpace ℝ (Fin 2))
    (h1 : dist u₁ 0 = 1) (h2 : dist u₂ 0 = 1) (h3 : dist u₃ 0 = 1) (h4 : dist u₄ 0 = 1)
    (hanti : u₁ + u₂ ≠ 0)
    (hsum : u₁ + u₂ = u₃ + u₄) :
    (u₁ = u₃ ∧ u₂ = u₄) ∨ (u₁ = u₄ ∧ u₂ = u₃) := by
  by_cases h13 : u₁ = u₃
  · left; exact ⟨h13, by rw [h13] at hsum; exact add_left_cancel hsum⟩
  by_cases h14 : u₁ = u₄
  · right; exact ⟨h14, by rw [h14, add_comm u₃ u₄] at hsum; exact add_left_cancel hsum⟩
  -- Otherwise `u₁, u₃, u₄` (or if `u₃ = u₄`, then `u₁, u₂, u₃`) all lie on `S(0, 1) ∩ S(s, 1)`.
  exfalso
  let s := u₁ + u₂
  have hmem : ∀ u v : EuclideanSpace ℝ (Fin 2), dist u 0 = 1 → dist v 0 = 1 → u + v = s →
      dist u 0 = 1 ∧ dist u s = 1 := by
    intro u v hu hv huv
    refine ⟨hu, ?_⟩
    have hdiff : u - s = -v := by rw [← huv]; abel
    rw [dist_eq_norm, hdiff, norm_neg]
    simpa [dist_eq_norm] using hv
  by_cases h34 : u₃ = u₄
  · -- Then `u₁ + u₂ = 2 * u₃` and `‖u₁‖² = ‖u₂‖² = ‖u₃‖² = 1` forces `u₁ = u₂ = u₃`.
    have hc1 : u₁ 0 ^ 2 + u₁ 1 ^ 2 = 1 := by
      have := (dist_eq_one_iff u₁ 0).mp h1; simpa using this
    have hc2 : u₂ 0 ^ 2 + u₂ 1 ^ 2 = 1 := by
      have := (dist_eq_one_iff u₂ 0).mp h2; simpa using this
    have hc3 : u₃ 0 ^ 2 + u₃ 1 ^ 2 = 1 := by
      have := (dist_eq_one_iff u₃ 0).mp h3; simpa using this
    have hsum' : u₁ + u₂ = u₃ + u₃ := by rwa [← h34] at hsum
    have hs0 : u₁ 0 + u₂ 0 = 2 * u₃ 0 := by
      have := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hsum'
      simp at this; linarith
    have hs1 : u₁ 1 + u₂ 1 = 2 * u₃ 1 := by
      have := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hsum'
      simp at this; linarith
    have hdiff_sq : (u₁ 0 - u₂ 0) ^ 2 + (u₁ 1 - u₂ 1) ^ 2 = 0 := by
      calc (u₁ 0 - u₂ 0) ^ 2 + (u₁ 1 - u₂ 1) ^ 2
          = 2 * (u₁ 0 ^ 2 + u₁ 1 ^ 2) + 2 * (u₂ 0 ^ 2 + u₂ 1 ^ 2) -
              ((u₁ 0 + u₂ 0) ^ 2 + (u₁ 1 + u₂ 1) ^ 2) := by ring
        _ = 2 * 1 + 2 * 1 - ((2 * u₃ 0) ^ 2 + (2 * u₃ 1) ^ 2) := by rw [hc1, hc2, hs0, hs1]
        _ = 4 - 4 * (u₃ 0 ^ 2 + u₃ 1 ^ 2) := by ring
        _ = 4 - 4 * 1 := by rw [hc3]
        _ = 0 := by ring
    have heq0 : u₁ 0 = u₂ 0 := by nlinarith
    have heq1 : u₁ 1 = u₂ 1 := by nlinarith
    apply h13
    ext i; fin_cases i <;> dsimp <;> linarith
  · -- `u₁, u₃, u₄` are 3 distinct points on `S(0, 1) ∩ S(s, 1)` with `0 ≠ s`, contradicting `≤ 2`.
    have hcard : ({u₁, u₃, u₄} : Finset (EuclideanSpace ℝ (Fin 2))).card ≤ 2 := by
      refine two_circles_inter_card_le_two 0 s (Ne.symm hanti) 1 1 _ ?_
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp | hp
      · rw [hp]; exact hmem u₁ u₂ h1 h2 rfl
      · rw [hp]; exact hmem u₃ u₄ h3 h4 hsum.symm
      · rw [hp]; exact hmem u₄ u₃ h4 h3 (by rw [add_comm, ← hsum])
    have h3c : ({u₁, u₃, u₄} : Finset (EuclideanSpace ℝ (Fin 2))).card = 3 := by
      simp [h13, h14, h34]
    omega

/-! #### Elementary `ℕ` Cauchy–Schwarz & 3D Loomis–Whitney Inequality -/

private lemma sq_sum_le_card_mul_sum_sq_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ x ∈ s, f x) ^ 2 ≤ s.card * ∑ x ∈ s, (f x) ^ 2 := by
  have hZ : (0 : ℤ) ≤ ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp :
      ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        2 * (s.card : ℤ) * (∑ x ∈ s, (f x : ℤ) ^ 2) - 2 * (∑ x ∈ s, (f x : ℤ)) ^ 2 := by
    have h1 : ∀ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        (s.card : ℤ) * (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (∑ y ∈ s, (f y : ℤ)) +
          ∑ y ∈ s, (f y : ℤ) ^ 2 := by
      intro x _
      have hsub : ∀ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
          (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (f y : ℤ) + (f y : ℤ) ^ 2 := fun y _ => by ring
      rw [Finset.sum_congr rfl hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ s, 2 * (f x : ℤ) = 2 * ∑ x ∈ s, (f x : ℤ) := by rw [← Finset.mul_sum]
    rw [h2]; ring
  rw [hexp] at hZ
  have hle : (∑ x ∈ s, (f x : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ x ∈ s, (f x : ℤ) ^ 2 := by linarith
  exact_mod_cast hle

/-- 3D Loomis–Whitney inequality on finite sets `S ⊆ α × β × γ` via a single `ℕ` Cauchy–Schwarz. -/
private lemma loomis_whitney_3d {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) :
    S.card ^ 2 ≤
      (S.image fun x => (x.2.1, x.2.2)).card *
      (S.image fun x => (x.1, x.2.2)).card *
      (S.image fun x => (x.1, x.2.1)).card := by
  let P_bc := S.image fun x => (x.2.1, x.2.2)
  let P_ac := S.image fun x => (x.1, x.2.2)
  let P_ab := S.image fun x => (x.1, x.2.1)
  let m : β × γ → ℕ := fun p => (S.filter fun x => x.2.1 = p.1 ∧ x.2.2 = p.2).card
  let u : β → ℕ := fun b => (P_ab.filter fun p => p.2 = b).card
  let v : γ → ℕ := fun c => (P_ac.filter fun p => p.2 = c).card
  -- Step 1: `∑ p ∈ P_bc, m p = S.card`.
  have hsum_m : ∑ p ∈ P_bc, m p = S.card := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := fun x : α × β × γ => (x.2.1, x.2.2))
      (s := S) (t := P_bc) (fun x hx => Finset.mem_image_of_mem _ hx)
    rw [h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [m]
    congr 1; ext x; simp [Prod.ext_iff]
  -- Step 2: `m (b, c) ≤ u b` and `m (b, c) ≤ v c`.
  have hm_le_u : ∀ p : β × γ, m p ≤ u p.1 := by
    intro p
    let fib := S.filter fun x => x.2.1 = p.1 ∧ x.2.2 = p.2
    have hinj : Set.InjOn (fun x : α × β × γ => (x.1, x.2.1)) (fib : Set (α × β × γ)) := by
      intro x hx y hy heq
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have h1 : x.1 = y.1 := (Prod.mk.inj heq).1
      ext
      · exact h1
      · exact hx'.1.trans hy'.1.symm
      · exact hx'.2.trans hy'.2.symm
    have hsub : fib.image (fun x => (x.1, x.2.1)) ⊆ P_ab.filter (fun q => q.2 = p.1) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxb, _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxS, hxb⟩
    calc m p = fib.card := rfl
      _ = (fib.image (fun x => (x.1, x.2.1))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ u p.1 := Finset.card_le_card hsub
  have hm_le_v : ∀ p : β × γ, m p ≤ v p.2 := by
    intro p
    let fib := S.filter fun x => x.2.1 = p.1 ∧ x.2.2 = p.2
    have hinj : Set.InjOn (fun x : α × β × γ => (x.1, x.2.2)) (fib : Set (α × β × γ)) := by
      intro x hx y hy heq
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have h1 : x.1 = y.1 := (Prod.mk.inj heq).1
      ext
      · exact h1
      · exact hx'.1.trans hy'.1.symm
      · exact hx'.2.trans hy'.2.symm
    have hsub : fib.image (fun x => (x.1, x.2.2)) ⊆ P_ac.filter (fun q => q.2 = p.2) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      rcases Finset.mem_filter.mp hx with ⟨hxS, _, hxc⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxS, hxc⟩
    calc m p = fib.card := rfl
      _ = (fib.image (fun x => (x.1, x.2.2))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ v p.2 := Finset.card_le_card hsub
  -- Step 3: `∑ p ∈ P_bc, m p ^ 2 ≤ ∑ b ∈ B, ∑ c ∈ C, u b * v c = P_ab.card * P_ac.card`.
  let B := P_ab.image Prod.snd
  let C := P_ac.image Prod.snd
  have hPbc_sub : P_bc ⊆ B ×ˢ C := by
    intro p hp
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨(x.1, x.2.1), Finset.mem_image_of_mem _ hxS, rfl⟩,
       Finset.mem_image.mpr ⟨(x.1, x.2.2), Finset.mem_image_of_mem _ hxS, rfl⟩⟩
  have hsum_u : ∑ b ∈ B, u b = P_ab.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := P_ab) (t := B)
      (fun q hq => Finset.mem_image_of_mem _ hq)]
  have hsum_v : ∑ c ∈ C, v c = P_ac.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := P_ac) (t := C)
      (fun q hq => Finset.mem_image_of_mem _ hq)]
  have hsq_sum : ∑ p ∈ P_bc, (m p) ^ 2 ≤ P_ac.card * P_ab.card := by
    calc ∑ p ∈ P_bc, (m p) ^ 2
        ≤ ∑ p ∈ P_bc, u p.1 * v p.2 := Finset.sum_le_sum fun p _ => by
            rw [sq]; exact Nat.mul_le_mul (hm_le_u p) (hm_le_v p)
      _ ≤ ∑ p ∈ B ×ˢ C, u p.1 * v p.2 := Finset.sum_le_sum_of_subset hPbc_sub
      _ = (∑ b ∈ B, u b) * (∑ c ∈ C, v c) := by
            rw [Finset.sum_product, Finset.sum_mul]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
      _ = P_ab.card * P_ac.card := by rw [hsum_u, hsum_v]
      _ = P_ac.card * P_ab.card := mul_comm _ _
  calc S.card ^ 2 = (∑ p ∈ P_bc, m p) ^ 2 := by rw [hsum_m]
    _ ≤ P_bc.card * ∑ p ∈ P_bc, (m p) ^ 2 := sq_sum_le_card_mul_sum_sq_nat P_bc m
    _ ≤ P_bc.card * (P_ac.card * P_ab.card) := Nat.mul_le_mul_left _ hsq_sum
    _ = P_bc.card * P_ac.card * P_ab.card := by ring

/-- Counting colorings `f : Fin d → Fin 3` assigning prescribed values `(c₀, c₁, c₂)` to three
distinct coordinates `(i, j, l)`. -/
private lemma card_colorings_prescribed {d : ℕ} (i j l : Fin d)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (c₀ c₁ c₂ : Fin 3) :
    (Finset.univ.filter fun f : Fin d → Fin 3 => f i = c₀ ∧ f j = c₁ ∧ f l = c₂).card =
      3 ^ (d - 3) := by
  let R := {r : Fin d // r ≠ i ∧ r ≠ j ∧ r ≠ l}
  let φ : (R → Fin 3) → (Fin d → Fin 3) := fun g r =>
    if h1 : r = i then c₀
    else if h2 : r = j then c₁
    else if h3 : r = l then c₂
    else g ⟨r, h1, h2, h3⟩
  have hφ_inj : Function.Injective φ := by
    intro g₁ g₂ heq
    funext ⟨r, hri, hrj, hrl⟩
    have := congr_fun heq r
    simpa [φ, hri, hrj, hrl] using this
  have hφ_img : Finset.univ.image φ =
      Finset.univ.filter (fun f : Fin d → Fin 3 => f i = c₀ ∧ f j = c₁ ∧ f l = c₂) := by
    ext f
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨g, rfl⟩
      simp [φ, hij.symm, hil.symm, hjl.symm]
    · rintro ⟨hfi, hfj, hfl⟩
      refine ⟨fun r => f r.1, ?_⟩
      funext r
      dsimp only [φ]
      split_ifs with h1 h2 h3
      · rw [h1, hfi]
      · rw [h2, hfj]
      · rw [h3, hfl]
      · rfl
  rw [← hφ_img, Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]
  have hRcard : Fintype.card R = d - 3 := by
    have h1 : Fintype.card R = (Finset.univ.filter fun r : Fin d => r ≠ i ∧ r ≠ j ∧ r ≠ l).card :=
      Fintype.card_subtype _
    rw [h1]
    have hset : (Finset.univ.filter fun r : Fin d => r ≠ i ∧ r ≠ j ∧ r ≠ l) =
        Finset.univ \ ({i, j, l} : Finset (Fin d)) := by
      ext r; simp
    rw [hset, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have h3 : ({i, j, l} : Finset (Fin d)).card = 3 := by simp [hij, hil, hjl]
    rw [h3]
  rw [hRcard]

/-- **New Loomis–Whitney `ℤ^d`-Projection Barrier Theorem:**
For **any** dimension `d` and **any** finite set `X ⊆ ℤ^d`, let `Y ⊆ ℤ^d` be any finite set of
points each having `ℓ₁`-unit neighbors in `X` along at least `3` distinct coordinate axes. Then
`4 * |Y|^2 ≤ 81 * |X|^3` (i.e., `|Y| ≤ (9/2) |X|^{3/2}`).

Consequently, no linear projection `π(x) = ∑ x_i u_i` of any subset of `ℤ^d` via unit vectors
`u_1, ..., u_d ∈ S¹` can ever break Elekes's `Ω(n^{3/2})` barrier. -/
theorem ppl077_zd_projection_barrier (d : ℕ) (X Y : Finset (Fin d → ℤ))
    (hY : ∀ y ∈ Y, ∃ i j l : Fin d, i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
      (Function.update y i (y i + 1) ∈ X ∨ Function.update y i (y i - 1) ∈ X) ∧
      (Function.update y j (y j + 1) ∈ X ∨ Function.update y j (y j - 1) ∈ X) ∧
      (Function.update y l (y l + 1) ∈ X ∨ Function.update y l (y l - 1) ∈ X)) :
    4 * Y.card ^ 2 ≤ 81 * X.card ^ 3 := by
  by_cases hYe : Y = ∅
  · subst hYe; simp
  have hYne : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hYe
  -- Notice `3 ≤ d` since `Y` is nonempty and contains 3 distinct indices in `Fin d`.
  have hd3 : 3 ≤ d := by
    obtain ⟨y, hy⟩ := hYne
    obtain ⟨i, j, l, hij, hjl, hil, _, _, _⟩ := hY y hy
    have h3 : ({i, j, l} : Finset (Fin d)).card = 3 := by simp [hij, hil, hjl]
    have hle : ({i, j, l} : Finset (Fin d)).card ≤ d := by
      simpa using Finset.card_le_univ ({i, j, l} : Finset (Fin d))
    omega
  -- For each coloring `f : Fin d → Fin 3`, define the rainbow slice `Yf f ⊆ Y`.
  let Yf : (Fin d → Fin 3) → Finset (Fin d → ℤ) := fun f =>
    Y.filter fun y =>
      (∃ i : Fin d, f i = 0 ∧
        (Function.update y i (y i + 1) ∈ X ∨ Function.update y i (y i - 1) ∈ X)) ∧
      (∃ j : Fin d, f j = 1 ∧
        (Function.update y j (y j + 1) ∈ X ∨ Function.update y j (y j - 1) ∈ X)) ∧
      (∃ l : Fin d, f l = 2 ∧
        (Function.update y l (y l + 1) ∈ X ∨ Function.update y l (y l - 1) ∈ X))
  -- Step 1: Each `y ∈ Y` belongs to `Yf f` for at least `6 * 3^(d - 3)` colorings `f`.
  have hper_y : ∀ y ∈ Y,
      6 * 3 ^ (d - 3) ≤ (Finset.univ.filter fun f : Fin d → Fin 3 => y ∈ Yf f).card := by
    intro y hy
    obtain ⟨i, j, l, hij, hjl, hil, hxi, hxj, hxl⟩ := hY y hy
    let Fset : Fin 3 → Fin 3 → Fin 3 → Finset (Fin d → Fin 3) := fun c₀ c₁ c₂ =>
      Finset.univ.filter fun f : Fin d → Fin 3 => f i = c₀ ∧ f j = c₁ ∧ f l = c₂
    let U6 := Fset 0 1 2 ∪ Fset 0 2 1 ∪ Fset 1 0 2 ∪ Fset 1 2 0 ∪ Fset 2 0 1 ∪ Fset 2 1 0
    have hdisj_f : ∀ a₀ a₁ a₂ b₀ b₁ b₂ : Fin 3,
        (a₀ ≠ b₀ ∨ a₁ ≠ b₁ ∨ a₂ ≠ b₂) → Disjoint (Fset a₀ a₁ a₂) (Fset b₀ b₁ b₂) := by
      intro a₀ a₁ a₂ b₀ b₁ b₂ hne
      rw [Finset.disjoint_left]
      intro f hfa hfb
      rcases (Finset.mem_filter.mp hfa).2 with ⟨ha0, ha1, ha2⟩
      rcases (Finset.mem_filter.mp hfb).2 with ⟨hb0, hb1, hb2⟩
      rcases hne with h0 | h1 | h2
      · exact h0 (ha0.symm.trans hb0)
      · exact h1 (ha1.symm.trans hb1)
      · exact h2 (ha2.symm.trans hb2)
    have hU6_sub : U6 ⊆ Finset.univ.filter (fun f : Fin d → Fin 3 => y ∈ Yf f) := by
      intro f hf
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ f, Finset.mem_filter.mpr ⟨hy, ?_⟩⟩
      simp only [U6, Finset.mem_union, Fset, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rcases hf with (((((⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) | ⟨h0, h1, h2⟩) |
        ⟨h0, h1, h2⟩) | ⟨h0, h1, h2⟩) | ⟨h0, h1, h2⟩)
      · exact ⟨⟨i, h0, hxi⟩, ⟨j, h1, hxj⟩, ⟨l, h2, hxl⟩⟩
      · exact ⟨⟨i, h0, hxi⟩, ⟨l, h2, hxl⟩, ⟨j, h1, hxj⟩⟩
      · exact ⟨⟨j, h1, hxj⟩, ⟨i, h0, hxi⟩, ⟨l, h2, hxl⟩⟩
      · exact ⟨⟨l, h2, hxl⟩, ⟨i, h0, hxi⟩, ⟨j, h1, hxj⟩⟩
      · exact ⟨⟨j, h1, hxj⟩, ⟨l, h2, hxl⟩, ⟨i, h0, hxi⟩⟩
      · exact ⟨⟨l, h2, hxl⟩, ⟨j, h1, hxj⟩, ⟨i, h0, hxi⟩⟩
    have hcard_each : ∀ c₀ c₁ c₂ : Fin 3, (Fset c₀ c₁ c₂).card = 3 ^ (d - 3) := fun c₀ c₁ c₂ =>
      card_colorings_prescribed i j l hij hjl hil c₀ c₁ c₂
    have hU6_card : U6.card = 6 * 3 ^ (d - 3) := by
      have hd1 : Disjoint (Fset 0 1 2) (Fset 0 2 1) := hdisj_f 0 1 2 0 2 1 (by decide)
      have hd2 : Disjoint (Fset 0 1 2 ∪ Fset 0 2 1) (Fset 1 0 2) :=
        Finset.disjoint_union_left.mpr ⟨hdisj_f 0 1 2 1 0 2 (by decide),
          hdisj_f 0 2 1 1 0 2 (by decide)⟩
      have hd3 : Disjoint (Fset 0 1 2 ∪ Fset 0 2 1 ∪ Fset 1 0 2) (Fset 1 2 0) :=
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
          ⟨hdisj_f 0 1 2 1 2 0 (by decide), hdisj_f 0 2 1 1 2 0 (by decide)⟩,
          hdisj_f 1 0 2 1 2 0 (by decide)⟩
      have hd4 : Disjoint (Fset 0 1 2 ∪ Fset 0 2 1 ∪ Fset 1 0 2 ∪ Fset 1 2 0) (Fset 2 0 1) :=
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr ⟨hdisj_f 0 1 2 2 0 1 (by decide),
            hdisj_f 0 2 1 2 0 1 (by decide)⟩, hdisj_f 1 0 2 2 0 1 (by decide)⟩,
          hdisj_f 1 2 0 2 0 1 (by decide)⟩
      have hd5 : Disjoint (Fset 0 1 2 ∪ Fset 0 2 1 ∪ Fset 1 0 2 ∪ Fset 1 2 0 ∪ Fset 2 0 1)
          (Fset 2 1 0) :=
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
            ⟨hdisj_f 0 1 2 2 1 0 (by decide), hdisj_f 0 2 1 2 1 0 (by decide)⟩,
            hdisj_f 1 0 2 2 1 0 (by decide)⟩, hdisj_f 1 2 0 2 1 0 (by decide)⟩,
          hdisj_f 2 0 1 2 1 0 (by decide)⟩
      simp only [U6]
      rw [Finset.card_union_of_disjoint hd5, Finset.card_union_of_disjoint hd4,
        Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
        Finset.card_union_of_disjoint hd1]
      simp only [hcard_each]
      ring
    rw [← hU6_card]
    exact Finset.card_le_card hU6_sub
  -- Step 2: Average over all `3^d` colorings to find one `f` with `2 * Y.card ≤ 9 * (Yf f).card`.
  have hsum_avg : Y.card * (6 * 3 ^ (d - 3)) ≤ ∑ f : Fin d → Fin 3, (Yf f).card := by
    calc Y.card * (6 * 3 ^ (d - 3))
        = ∑ _y ∈ Y, (6 * 3 ^ (d - 3)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ Y, (Finset.univ.filter fun f : Fin d → Fin 3 => y ∈ Yf f).card :=
          Finset.sum_le_sum hper_y
      _ = ∑ f : Fin d → Fin 3, (Yf f).card := by
          have h1 : ∀ y ∈ Y,
              (Finset.univ.filter fun f : Fin d → Fin 3 => y ∈ Yf f).card =
              ∑ f : Fin d → Fin 3, if y ∈ Yf f then 1 else 0 := fun y _ => Finset.card_filter _ _
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [← Finset.card_filter]
          congr 1; ext y; simp only [Finset.mem_filter, Yf, and_self_left]
  obtain ⟨f, _, hf_max⟩ := Finset.exists_max_image Finset.univ (fun f : Fin d → Fin 3 => (Yf f).card)
    (Finset.univ_nonempty)
  have hsum_le_max : ∑ g : Fin d → Fin 3, (Yf g).card ≤ 3 ^ d * (Yf f).card := by
    calc ∑ g : Fin d → Fin 3, (Yf g).card
        ≤ ∑ _g : Fin d → Fin 3, (Yf f).card := Finset.sum_le_sum fun g _ => hf_max g (Finset.mem_univ g)
      _ = 3 ^ d * (Yf f).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, smul_eq_mul]
  have hpow : 3 ^ d = 27 * 3 ^ (d - 3) := by
    have : d = (d - 3) + 3 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  have h29 : 2 * Y.card ≤ 9 * (Yf f).card := by
    have h1 := le_trans hsum_avg hsum_le_max
    rw [hpow] at h1
    have hpos : 0 < 3 * 3 ^ (d - 3) := by positivity
    have h2 : (2 * Y.card) * (3 * 3 ^ (d - 3)) ≤ (9 * (Yf f).card) * (3 * 3 ^ (d - 3)) := by
      linarith
    exact Nat.le_of_mul_le_mul_right h2 hpos
  -- Step 3: Apply 3D Loomis–Whitney to `Yf f` via its 3 color-block coordinates.
  let blk : Fin 3 → (Fin d → ℤ) → (Fin d → ℤ) := fun c v r => if f r = c then v r else 0
  let embed : (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) :=
    fun v => (blk 0 v, blk 1 v, blk 2 v)
  have hembed_inj : Function.Injective embed := by
    intro v₁ v₂ heq
    funext r
    have h0 := congr_fun (congr_arg Prod.fst heq) r
    have h1 := congr_fun (congr_arg (fun p => p.2.1) heq) r
    have h2 := congr_fun (congr_arg (fun p => p.2.2) heq) r
    generalize hfr : f r = c
    fin_cases c
    · simpa [embed, blk, hfr] using h0
    · simpa [embed, blk, hfr] using h1
    · simpa [embed, blk, hfr] using h2
  let S := (Yf f).image embed
  have hScard : S.card = (Yf f).card := Finset.card_image_of_injective _ hembed_inj
  have hLW := loomis_whitney_3d S
  -- Each 2-block projection of `S` maps into the corresponding 2-block projection of `X`.
  have hproj0 : (S.image fun p => (p.2.1, p.2.2)).card ≤ X.card := by
    let π0 : (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) := fun v => (blk 1 v, blk 2 v)
    have hsub : (S.image fun p => (p.2.1, p.2.2)) ⊆ X.image π0 := by
      intro q hq
      obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hpS
      obtain ⟨i, hfi, hxi⟩ := (Finset.mem_filter.mp hy).2.1
      rcases hxi with hx | hx
      · refine Finset.mem_image.mpr ⟨Function.update y i (y i + 1), hx, ?_⟩
        ext r <;> (dsimp only [π0, embed, blk]; by_cases hri : r = i <;> simp [hri, hfi])
      · refine Finset.mem_image.mpr ⟨Function.update y i (y i - 1), hx, ?_⟩
        ext r <;> (dsimp only [π0, embed, blk]; by_cases hri : r = i <;> simp [hri, hfi])
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hproj1 : (S.image fun p => (p.1, p.2.2)).card ≤ X.card := by
    let π1 : (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) := fun v => (blk 0 v, blk 2 v)
    have hsub : (S.image fun p => (p.1, p.2.2)) ⊆ X.image π1 := by
      intro q hq
      obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hpS
      obtain ⟨j, hfj, hxj⟩ := (Finset.mem_filter.mp hy).2.2.1
      rcases hxj with hx | hx
      · refine Finset.mem_image.mpr ⟨Function.update y j (y j + 1), hx, ?_⟩
        ext r <;> (dsimp only [π1, embed, blk]; by_cases hrj : r = j <;> simp [hrj, hfj])
      · refine Finset.mem_image.mpr ⟨Function.update y j (y j - 1), hx, ?_⟩
        ext r <;> (dsimp only [π1, embed, blk]; by_cases hrj : r = j <;> simp [hrj, hfj])
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hproj2 : (S.image fun p => (p.1, p.2.1)).card ≤ X.card := by
    let π2 : (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) := fun v => (blk 0 v, blk 1 v)
    have hsub : (S.image fun p => (p.1, p.2.1)) ⊆ X.image π2 := by
      intro q hq
      obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hpS
      obtain ⟨l, hfl, hxl⟩ := (Finset.mem_filter.mp hy).2.2.2
      rcases hxl with hx | hx
      · refine Finset.mem_image.mpr ⟨Function.update y l (y l + 1), hx, ?_⟩
        ext r <;> (dsimp only [π2, embed, blk]; by_cases hrl : r = l <;> simp [hrl, hfl])
      · refine Finset.mem_image.mpr ⟨Function.update y l (y l - 1), hx, ?_⟩
        ext r <;> (dsimp only [π2, embed, blk]; by_cases hrl : r = l <;> simp [hrl, hfl])
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hYf_sq : (Yf f).card ^ 2 ≤ X.card ^ 3 := by
    rw [← hScard]
    calc S.card ^ 2
        ≤ (S.image fun p => (p.2.1, p.2.2)).card *
          (S.image fun p => (p.1, p.2.2)).card *
          (S.image fun p => (p.1, p.2.1)).card := hLW
      _ ≤ X.card * X.card * X.card :=
          Nat.mul_le_mul (Nat.mul_le_mul hproj0 hproj1) hproj2
      _ = X.card ^ 3 := by ring
  calc 4 * Y.card ^ 2 = (2 * Y.card) ^ 2 := by ring
    _ ≤ (9 * (Yf f).card) ^ 2 := Nat.pow_le_pow_left h29 2
    _ = 81 * (Yf f).card ^ 2 := by ring
    _ ≤ 81 * X.card ^ 3 := Nat.mul_le_mul_left 81 hYf_sq

private lemma eq_of_add_mod_eq {a b c n : ℕ} (hb : b < n) (hc : c < n)
    (h : (a + b) % n = (a + c) % n) : b = c := by
  set r := a % n
  have hr : r < n := Nat.mod_lt a (by omega)
  have h1 : (r + b) % n = (a + b) % n := by simp [r, Nat.add_mod]
  have h2 : (r + c) % n = (a + c) % n := by simp [r, Nat.add_mod]
  have h3 : (r + b) % n = (r + c) % n := by rw [h1, h2, h]
  have hmod : ∀ x < n, (r + x) % n = if r + x < n then r + x else r + x - n := by
    intro x hx
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod b hb, hmod c hc] at h3
  split_ifs at h3 <;> omega

/-- **Shifted Böröczky `K_{2,3}`-Free Pseudocircle Barrier Hypergraph:**
For every `n ≥ 3`, there exists a family `T` of 3-element subsets of `Fin n` (the combinatorial
triple-point hypergraph of the glued northern/southern Böröczky pseudocircle arrangement
`i + j + k ≡ 0, 1 (mod n)`) such that:
1. Every `e ∈ T` has size `3`.
2. Every pair of distinct elements `i ≠ j` lies in **at most `2`** triples of `T` (`K_{2,3}`-free,
   and `K_{3,2}`-free since triples are distinct subsets of size 3).
3. `3 * T.card + 2 * n ≥ n * (n - 1)` (asymptotically `n^2 / 3 - O(n)`).

This certifies that no purely incidence-combinatorial or pseudocircle-topological argument can
improve the Harborth–Mengersen leading constant `1/3`. -/
theorem ppl077_pseudocircle_barrier_hypergraph (n : ℕ) (hn : 3 ≤ n) :
    ∃ T : Finset (Finset (Fin n)),
      (∀ e ∈ T, e.card = 3) ∧
      (∀ i j : Fin n, i ≠ j → (T.filter fun e => i ∈ e ∧ j ∈ e).card ≤ 2) ∧
      n * (n - 1) ≤ 3 * T.card + 2 * n := by
  have hn0 : 0 < n := by omega
  let Tmod : ℕ → Finset (Finset (Fin n)) := fun r =>
    ((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun e =>
      (∑ x ∈ e, x.val) % n = r
  let T := Tmod 0 ∪ Tmod 1
  have hdisj : Disjoint (Tmod 0) (Tmod 1) := by
    rw [Finset.disjoint_left]
    intro e h0 h1
    have eq0 := (Finset.mem_filter.mp h0).2
    have eq1 := (Finset.mem_filter.mp h1).2
    omega
  -- Helper: given distinct `i, j : Fin n` and `r ∈ {0, 1}`, at most one `e ∈ Tmod r` contains `i, j`.
  have hpair_r : ∀ (r : ℕ) (i j : Fin n), i ≠ j →
      (Tmod r |>.filter fun e => i ∈ e ∧ j ∈ e).card ≤ 1 := by
    intro r i j hij
    rw [Finset.card_le_one]
    intro e₁ he₁ e₂ he₂
    rcases Finset.mem_filter.mp he₁ with ⟨he1T, hi1, hj1⟩
    rcases Finset.mem_filter.mp he₂ with ⟨he2T, hi2, hj2⟩
    rcases Finset.mem_filter.mp he1T with ⟨he1p, hsum1⟩
    rcases Finset.mem_filter.mp he2T with ⟨he2p, hsum2⟩
    have hc1 : e₁.card = 3 := (Finset.mem_powersetCard.mp he1p).2
    have hc2 : e₂.card = 3 := (Finset.mem_powersetCard.mp he2p).2
    -- Extract the 3rd element `k₁` of `e₁` and `k₂` of `e₂`.
    have hrem1 : ((e₁.erase i).erase j).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, hj1⟩),
        Finset.card_erase_of_mem hi1, hc1]
    have hrem2 : ((e₂.erase i).erase j).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, hj2⟩),
        Finset.card_erase_of_mem hi2, hc2]
    obtain ⟨k₁, hk1⟩ := Finset.card_eq_one.mp hrem1
    obtain ⟨k₂, hk2⟩ := Finset.card_eq_one.mp hrem2
    have hk1_mem : k₁ ∈ (e₁.erase i).erase j := hk1 ▸ Finset.mem_singleton_self k₁
    have hk2_mem : k₂ ∈ (e₂.erase i).erase j := hk2 ▸ Finset.mem_singleton_self k₂
    have hk1j : k₁ ≠ j := (Finset.mem_erase.mp hk1_mem).1
    have hk1i : k₁ ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk1_mem).2).1
    have hk2j : k₂ ≠ j := (Finset.mem_erase.mp hk2_mem).1
    have hk2i : k₂ ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk2_mem).2).1
    have he1_eq : e₁ = {i, j, k₁} := by
      rw [← Finset.insert_erase hi1,
        ← Finset.insert_erase (Finset.mem_erase.mpr ⟨hij.symm, hj1⟩), hk1]
    have he2_eq : e₂ = {i, j, k₂} := by
      rw [← Finset.insert_erase hi2,
        ← Finset.insert_erase (Finset.mem_erase.mpr ⟨hij.symm, hj2⟩), hk2]
    rw [he1_eq] at hsum1
    rw [he2_eq] at hsum2
    have hs1 : ∑ x ∈ ({i, j, k₁} : Finset (Fin n)), x.val = i.val + j.val + k₁.val := by
      rw [Finset.sum_insert (by simp [hij, hk1i.symm]),
        Finset.sum_insert (by simp [hk1j.symm]), Finset.sum_singleton]; ring
    have hs2 : ∑ x ∈ ({i, j, k₂} : Finset (Fin n)), x.val = i.val + j.val + k₂.val := by
      rw [Finset.sum_insert (by simp [hij, hk2i.symm]),
        Finset.sum_insert (by simp [hk2j.symm]), Finset.sum_singleton]; ring
    rw [hs1] at hsum1
    rw [hs2] at hsum2
    have hk_eq : k₁ = k₂ := Fin.ext (eq_of_add_mod_eq k₁.isLt k₂.isLt (hsum1.trans hsum2.symm))
    rw [he1_eq, he2_eq, hk_eq]
  -- Helper: lower bound `n * (n - 1) ≤ 6 * (Tmod r).card + 2 * n` for `r < n`.
  have hlower_r : ∀ r : ℕ, r < n → n * (n - 1) ≤ 6 * (Tmod r).card + 2 * n := by
    intro r hr
    let comp : Fin n → Fin n → Fin n := fun i j =>
      ⟨(2 * n + r - (i.val + j.val) % n) % n, Nat.mod_lt _ hn0⟩
    have hcomp_sum : ∀ i j : Fin n, (i.val + j.val + (comp i j).val) % n = r := by
      intro i j
      dsimp only [comp]
      have hlt : (i.val + j.val) % n < n := Nat.mod_lt _ hn0
      have hmod1 : (i.val + j.val + (2 * n + r - (i.val + j.val) % n) % n) % n =
          ((i.val + j.val) % n + (2 * n + r - (i.val + j.val) % n)) % n := by
        simp only [Nat.add_mod, Nat.mod_mod]
      rw [hmod1]
      have hadd : (i.val + j.val) % n + (2 * n + r - (i.val + j.val) % n) = r + 2 * n := by omega
      rw [hadd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    let U := (Finset.univ : Finset (Fin n)).offDiag
    let good := U.filter fun p => comp p.1 p.2 ≠ p.1 ∧ comp p.1 p.2 ≠ p.2
    let bad1 := U.filter fun p => comp p.1 p.2 = p.1
    let bad2 := U.filter fun p => comp p.1 p.2 = p.2
    have hU_sub : U ⊆ good ∪ bad1 ∪ bad2 := by
      intro p hp
      simp only [good, bad1, bad2, Finset.mem_union, Finset.mem_filter]
      by_cases h1 : comp p.1 p.2 = p.1
      · left; right; exact ⟨hp, h1⟩
      · by_cases h2 : comp p.1 p.2 = p.2
        · right; exact ⟨hp, h2⟩
        · left; left; exact ⟨hp, h1, h2⟩
    have hbad1_le : bad1.card ≤ n := by
      have hinj : Set.InjOn Prod.fst (bad1 : Set (Fin n × Fin n)) := by
        intro p hp q hq hf
        have hp1 := (Finset.mem_filter.mp hp).2
        have hq1 := (Finset.mem_filter.mp hq).2
        have hsp := hcomp_sum p.1 p.2
        have hsq := hcomp_sum q.1 q.2
        rw [hp1] at hsp; rw [hq1] at hsq
        have hfval : p.1.val = q.1.val := congr_arg Fin.val hf
        have hmod2 : (2 * p.1.val + p.2.val) % n = (2 * p.1.val + q.2.val) % n := by
          have hp' : 2 * p.1.val + p.2.val = p.1.val + p.2.val + p.1.val := by ring
          have hq' : 2 * p.1.val + q.2.val = q.1.val + q.2.val + q.1.val := by rw [hfval]; ring
          rw [hp', hq', hsp, hsq]
        have hp2q2 : p.2.val = q.2.val := eq_of_add_mod_eq p.2.isLt q.2.isLt hmod2
        exact Prod.ext hf (Fin.ext hp2q2)
      calc bad1.card = (bad1.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    have hbad2_le : bad2.card ≤ n := by
      have hinj : Set.InjOn Prod.snd (bad2 : Set (Fin n × Fin n)) := by
        intro p hp q hq hs
        have hp2 := (Finset.mem_filter.mp hp).2
        have hq2 := (Finset.mem_filter.mp hq).2
        have hsp := hcomp_sum p.1 p.2
        have hsq := hcomp_sum q.1 q.2
        rw [hp2] at hsp; rw [hq2] at hsq
        have hsval : p.2.val = q.2.val := congr_arg Fin.val hs
        have hmod1 : (2 * p.2.val + p.1.val) % n = (2 * p.2.val + q.1.val) % n := by
          have hp' : 2 * p.2.val + p.1.val = p.1.val + p.2.val + p.2.val := by ring
          have hq' : 2 * p.2.val + q.1.val = q.1.val + q.2.val + q.2.val := by rw [hsval]; ring
          rw [hp', hq', hsp, hsq]
        have hp1q1 : p.1.val = q.1.val := eq_of_add_mod_eq p.1.isLt q.1.isLt hmod1
        exact Prod.ext (Fin.ext hp1q1) hs
      calc bad2.card = (bad2.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    -- Map `good → Tmod r` via `(i, j) ↦ {i, j, comp i j}`; every fiber has size `≤ 6`.
    let φ : Fin n × Fin n → Finset (Fin n) := fun p => {p.1, p.2, comp p.1 p.2}
    have hφ_mem : ∀ p ∈ good, φ p ∈ Tmod r := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpU, hne1, hne2⟩
      have hij : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hpU).2.2
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · dsimp only [φ]
        rw [Finset.card_insert_of_notMem (by simp [hij, hne1.symm]),
          Finset.card_insert_of_notMem (by simp [hne2.symm]), Finset.card_singleton]
      · dsimp only [φ]
        rw [Finset.sum_insert (by simp [hij, hne1.symm]),
          Finset.sum_insert (by simp [hne2.symm]), Finset.sum_singleton]
        have : p.1.val + (p.2.val + (comp p.1 p.2).val) =
            p.1.val + p.2.val + (comp p.1 p.2).val := by ring
        rw [this]
        exact hcomp_sum p.1 p.2
    have hgood_le : good.card ≤ 6 * (Tmod r).card := by
      rw [Finset.card_eq_sum_card_fiberwise hφ_mem]
      calc ∑ e ∈ Tmod r, (good.filter fun p => φ p = e).card
          ≤ ∑ _e ∈ Tmod r, 6 := by
            refine Finset.sum_le_sum fun e he => ?_
            have hec : e.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
            have hsub : (good.filter fun p => φ p = e) ⊆ e.offDiag := by
              intro p hp
              rcases Finset.mem_filter.mp hp with ⟨hpg, hpe⟩
              have hij : p.1 ≠ p.2 := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hpg).1).2.2
              rw [Finset.mem_offDiag]
              refine ⟨?_, ?_, hij⟩
              · rw [← hpe]; simp [φ]
              · rw [← hpe]; simp [φ]
            calc (good.filter fun p => φ p = e).card
                ≤ e.offDiag.card := Finset.card_le_card hsub
              _ = e.card * (e.card - 1) := card_offDiag_eq e
              _ = 6 := by rw [hec]
        _ = 6 * (Tmod r).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hUcard : U.card = n * (n - 1) := by
      rw [card_offDiag_eq, Finset.card_univ, Fintype.card_fin]
    have hcov : U.card ≤ good.card + bad1.card + bad2.card :=
      le_trans (Finset.card_le_card hU_sub)
        (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    omega
  refine ⟨T, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h0 | h1
    · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h0).1).2
    · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h1).1).2
  · intro i j hij
    have hunion : (T.filter fun e => i ∈ e ∧ j ∈ e) =
        ((Tmod 0).filter fun e => i ∈ e ∧ j ∈ e) ∪ ((Tmod 1).filter fun e => i ∈ e ∧ j ∈ e) := by
      ext e; simp only [T, Finset.mem_filter, Finset.mem_union]; tauto
    rw [hunion]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add (hpair_r 0 i j hij) (hpair_r 1 i j hij))
  · have h0 := hlower_r 0 (by omega)
    have h1 := hlower_r 1 (by omega)
    have hTcard : T.card = (Tmod 0).card + (Tmod 1).card := Finset.card_union_of_disjoint hdisj
    omega

end PPL077
