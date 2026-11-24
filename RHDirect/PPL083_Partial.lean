import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# PPL 083 (Erdős Problem #99 — Minimum-Diameter Unit-Separated Point Sets): Partial Structural Milestone

**Scope Notice (Partial Milestone — NOT the full open conjecture):**
Erdős Problem #99 (asking whether every sufficiently large minimum-diameter unit-separated finite
planar point set contains three points forming a unit equilateral triangle) remains **OPEN**.
This file formalizes the unconditionally proved structural theorems and the exact sheared-lattice
proof barrier documented in `scripts/ppl083_findings.md`, using pure Mathlib (`EuclideanSpace ℝ (Fin 2)`,
`Finset`, `dist`, `Metric.diam`) without claiming a resolution of Erdős #99:

1. **Unit-Contact Non-Crossing, Kissing Bound & Euler `K_3`-Free Bound (Theorem 1):**
   - `ppl083_unit_segments_noncrossing`: Disjoint unit-contact pairs have disjoint closed line segments
     (straight-line planarity / penny graph).
   - `ppl083_unit_degree_le_six` & `ppl083_unit_edges_le_three_n`: Every point has at most `6` unit
     neighbors and `G₁(A)` has at most `3n` edges.
   - `ppl083_euler_trifree_edge_bound`: Planar `K_3`-free Euler inequality `|E| ≤ 2n - 2 - b/2`
     (and `|E| ≤ 2n - 4` for `b ≥ 4`).
2. **Diameter-Graph Thrackle, Extreme Points & Oler/Isodiametric Lower Bound (Theorem 2):**
   - `ppl083_diam_opposite_quad_impossible`: Two diameter edges cannot form opposite sides of a
     convex quadrilateral with crossing diagonals unless they share an endpoint.
   - `ppl083_diam_extreme_point`: Every endpoint of a diameter chord is an extreme point of
     `convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2)))`.
   - `ppl083_oler_diam_lower_bound`: Exact quadratic/radical lower bound from Oler's + Bieberbach's
     + Barbier's inequalities.
3. **KKT Equilibrium Stress, Virial Identity & Second-Order Perturbations (Theorem 3)**
4. **Exact Triangle-Free Small-`n` Witnesses (`n = 4, 5, 6, 8`)**
5. **Exact Sheared-Lattice `Λ_ε` Proof Barrier**
-/

namespace PPL083

section ContactPlanarity

open scoped RealInnerProductSpace

/-- Theorem 1a (Unit-Contact Non-Crossing / Penny-Graph Planarity):
In any unit-separated planar point set, two disjoint unit-length pairs `[p₁, p₂]` and `[q₁, q₂]`
have strictly disjoint closed segments. -/
theorem ppl083_unit_segments_noncrossing
    {p₁ p₂ q₁ q₂ : EuclideanSpace ℝ (Fin 2)}
    (hp12 : dist p₁ p₂ = 1) (hq12 : dist q₁ q₂ = 1)
    (hp1q1 : 1 ≤ dist p₁ q₁) (hp1q2 : 1 ≤ dist p₁ q₂)
    (hp2q1 : 1 ≤ dist p₂ q₁) (hp2q2 : 1 ≤ dist p₂ q₂) :
    Disjoint (segment ℝ p₁ p₂) (segment ℝ q₁ q₂) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  rw [segment_eq_image'] at hxp hxq
  rcases hxp with ⟨t, ht, rfl⟩
  rcases hxq with ⟨s, hs, hxs⟩
  have hxp_eq : (fun θ : ℝ => p₁ + θ • (p₂ - p₁)) t = (1 - t) • p₁ + t • p₂ := by module
  have hxq_eq : (fun θ : ℝ => q₁ + θ • (q₂ - q₁)) s = (1 - s) • q₁ + s • q₂ := by module
  have hx_eq : (1 - t) • p₁ + t • p₂ = (1 - s) • q₁ + s • q₂ := by
    rw [← hxp_eq, ← hxq_eq]; exact hxs.symm
  have hdist_p1 : dist p₁ ((1 - t) • p₁ + t • p₂) = t := by
    rw [dist_eq_norm, show p₁ - ((1 - t) • p₁ + t • p₂) = t • (p₁ - p₂) by module]
    rw [norm_smul, Real.norm_of_nonneg ht.1, ← dist_eq_norm, hp12, mul_one]
  have hdist_p2 : dist ((1 - t) • p₁ + t • p₂) p₂ = 1 - t := by
    rw [dist_eq_norm, show (1 - t) • p₁ + t • p₂ - p₂ = (1 - t) • (p₁ - p₂) by module]
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2), ← dist_eq_norm, hp12, mul_one]
  have hdist_q1 : dist q₁ ((1 - s) • q₁ + s • q₂) = s := by
    rw [dist_eq_norm, show q₁ - ((1 - s) • q₁ + s • q₂) = s • (q₁ - q₂) by module]
    rw [norm_smul, Real.norm_of_nonneg hs.1, ← dist_eq_norm, hq12, mul_one]
  have hdist_q2 : dist ((1 - s) • q₁ + s • q₂) q₂ = 1 - s := by
    rw [dist_eq_norm, show (1 - s) • q₁ + s • q₂ - q₂ = (1 - s) • (q₁ - q₂) by module]
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hs.2), ← dist_eq_norm, hq12, mul_one]
  have h11 : 1 ≤ t + s := by
    calc 1 ≤ dist p₁ q₁ := hp1q1
      _ ≤ dist p₁ ((1 - t) • p₁ + t • p₂) + dist ((1 - t) • p₁ + t • p₂) q₁ := dist_triangle _ _ _
      _ = t + dist ((1 - s) • q₁ + s • q₂) q₁ := by rw [hdist_p1, hx_eq]
      _ = t + s := by rw [dist_comm _ q₁, hdist_q1]
  have h22 : 1 ≤ (1 - t) + (1 - s) := by
    calc 1 ≤ dist p₂ q₂ := hp2q2
      _ ≤ dist p₂ ((1 - t) • p₁ + t • p₂) + dist ((1 - t) • p₁ + t • p₂) q₂ := dist_triangle _ _ _
      _ = (1 - t) + dist ((1 - s) • q₁ + s • q₂) q₂ := by rw [dist_comm p₂, hdist_p2, hx_eq]
      _ = (1 - t) + (1 - s) := by rw [hdist_q2]
  have h12 : 1 ≤ t + (1 - s) := by
    calc 1 ≤ dist p₁ q₂ := hp1q2
      _ ≤ dist p₁ ((1 - t) • p₁ + t • p₂) + dist ((1 - t) • p₁ + t • p₂) q₂ := dist_triangle _ _ _
      _ = t + dist ((1 - s) • q₁ + s • q₂) q₂ := by rw [hdist_p1, hx_eq]
      _ = t + (1 - s) := by rw [hdist_q2]
  have h21 : 1 ≤ (1 - t) + s := by
    calc 1 ≤ dist p₂ q₁ := hp2q1
      _ ≤ dist p₂ ((1 - t) • p₁ + t • p₂) + dist ((1 - t) • p₁ + t • p₂) q₁ := dist_triangle _ _ _
      _ = (1 - t) + dist ((1 - s) • q₁ + s • q₂) q₁ := by rw [dist_comm p₂, hdist_p2, hx_eq]
      _ = (1 - t) + s := by rw [dist_comm _ q₁, hdist_q1]
  have ht_half : t = 1 / 2 := by linarith
  have hs_half : s = 1 / 2 := by linarith
  rw [ht_half, hs_half] at hx_eq
  set u := ((1 / 2 : ℝ) • (p₁ - p₂))
  set w := ((1 / 2 : ℝ) • (q₁ - q₂))
  have hdiff : ((1 - (1 / 2 : ℝ)) • p₁ + (1 / 2 : ℝ) • p₂) -
      ((1 - (1 / 2 : ℝ)) • q₁ + (1 / 2 : ℝ) • q₂) = 0 := by rw [hx_eq, sub_self]
  have hp1_sub_q1 : p₁ - q₁ = u - w := by
    dsimp [u, w]
    calc p₁ - q₁ = (1 / 2 : ℝ) • (p₁ - p₂) - (1 / 2 : ℝ) • (q₁ - q₂) +
        (((1 - (1 / 2 : ℝ)) • p₁ + (1 / 2 : ℝ) • p₂) -
          ((1 - (1 / 2 : ℝ)) • q₁ + (1 / 2 : ℝ) • q₂)) := by module
      _ = (1 / 2 : ℝ) • (p₁ - p₂) - (1 / 2 : ℝ) • (q₁ - q₂) := by rw [hdiff, add_zero]
  have hp1_sub_q2 : p₁ - q₂ = u + w := by
    dsimp [u, w]
    calc p₁ - q₂ = (1 / 2 : ℝ) • (p₁ - p₂) + (1 / 2 : ℝ) • (q₁ - q₂) +
        (((1 - (1 / 2 : ℝ)) • p₁ + (1 / 2 : ℝ) • p₂) -
          ((1 - (1 / 2 : ℝ)) • q₁ + (1 / 2 : ℝ) • q₂)) := by module
      _ = (1 / 2 : ℝ) • (p₁ - p₂) + (1 / 2 : ℝ) • (q₁ - q₂) := by rw [hdiff, add_zero]
  have hu_norm : ‖u‖ = 1 / 2 := by
    dsimp [u]; rw [norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm, hp12]; norm_num
  have hw_norm : ‖w‖ = 1 / 2 := by
    dsimp [w]; rw [norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm, hq12]; norm_num
  have hnorm_sub : 1 ≤ ‖u - w‖ ^ 2 := by
    rw [← hp1_sub_q1, ← dist_eq_norm]
    nlinarith
  have hnorm_add : 1 ≤ ‖u + w‖ ^ 2 := by
    rw [← hp1_sub_q2, ← dist_eq_norm]
    nlinarith
  rw [norm_sub_sq_real, hu_norm, hw_norm] at hnorm_sub
  rw [norm_add_sq_real, hu_norm, hw_norm] at hnorm_add
  linarith

private noncomputable def toC (u : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨u 0, u 1⟩

private lemma norm_toC (u : EuclideanSpace ℝ (Fin 2)) : ‖toC u‖ = ‖u‖ := by
  have h1 : ‖toC u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
    dsimp [toC]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hn1 : 0 ≤ ‖toC u‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖u‖ := norm_nonneg _
  nlinarith

private lemma inner_toC {u₁ u₂ : EuclideanSpace ℝ (Fin 2)} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) :
    inner ℝ u₁ u₂ = Real.cos (Complex.arg (toC u₁) - Complex.arg (toC u₂)) := by
  have hz₁ : toC u₁ ≠ 0 := by
    intro h; have := norm_toC u₁; rw [h, norm_zero, hu₁] at this; norm_num at this
  have hz₂ : toC u₂ ≠ 0 := by
    intro h; have := norm_toC u₂; rw [h, norm_zero, hu₂] at this; norm_num at this
  have hn₁ : ‖toC u₁‖ = 1 := (norm_toC u₁).trans hu₁
  have hn₂ : ‖toC u₂‖ = 1 := (norm_toC u₂).trans hu₂
  have hc₁ : u₁ 0 = Real.cos (Complex.arg (toC u₁)) := by
    have := Complex.cos_arg hz₁; rw [hn₁, div_one] at this; exact this.symm
  have hs₁ : u₁ 1 = Real.sin (Complex.arg (toC u₁)) := by
    have := Complex.sin_arg (toC u₁); rw [hn₁, div_one] at this; exact this.symm
  have hc₂ : u₂ 0 = Real.cos (Complex.arg (toC u₂)) := by
    have := Complex.cos_arg hz₂; rw [hn₂, div_one] at this; exact this.symm
  have hs₂ : u₂ 1 = Real.sin (Complex.arg (toC u₂)) := by
    have := Complex.sin_arg (toC u₂); rw [hn₂, div_one] at this; exact this.symm
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hc₁, hs₁, hc₂, hs₂, Real.cos_sub]
  ring

/-- Theorem 1b (2D Kissing Bound): In any unit-separated planar set `A`, every point `p ∈ A`
has at most `6` unit-distance neighbors. -/
theorem ppl083_unit_degree_le_six {A : Finset (EuclideanSpace ℝ (Fin 2))}
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) {p : EuclideanSpace ℝ (Fin 2)} :
    (A.filter (fun q => dist p q = 1)).card ≤ 6 := by
  classical
  set S := A.filter (fun q => dist p q = 1)
  by_contra hgt
  have h7 : 6 < S.card := by omega
  let sec : EuclideanSpace ℝ (Fin 2) → Fin 6 := fun q =>
    let θ := Complex.arg (toC (q - p))
    if θ ≤ -2 * Real.pi / 3 then 0
    else if θ ≤ -Real.pi / 3 then 1
    else if θ ≤ 0 then 2
    else if θ ≤ Real.pi / 3 then 3
    else if θ ≤ 2 * Real.pi / 3 then 4
    else 5
  have hpig : (Finset.univ : Finset (Fin 6)).card < S.card := by
    rw [Finset.card_fin]; exact h7
  obtain ⟨q₁, hq1, q₂, hq2, hne, hsec_eq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hpig (fun _ _ => Finset.mem_univ _)
  rw [Finset.mem_filter] at hq1 hq2
  have hu₁ : ‖q₁ - p‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hq1.2
  have hu₂ : ‖q₂ - p‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hq2.2
  have hq12 : 1 ≤ ‖(q₁ - p) - (q₂ - p)‖ ^ 2 := by
    have h12 : 1 ≤ dist q₁ q₂ := hsep q₁ hq1.1 q₂ hq2.1 hne
    rw [show (q₁ - p) - (q₂ - p) = q₁ - q₂ by abel, ← dist_eq_norm]
    nlinarith
  rw [norm_sub_sq_real, hu₁, hu₂] at hq12
  have hinner_le : inner ℝ (q₁ - p) (q₂ - p) ≤ 1 / 2 := by linarith
  have harg₁ := Complex.arg_mem_Ioc (toC (q₁ - p))
  have harg₂ := Complex.arg_mem_Ioc (toC (q₂ - p))
  have hdiff_lt : |Complex.arg (toC (q₁ - p)) - Complex.arg (toC (q₂ - p))| < Real.pi / 3 := by
    have hsec' :
        (if Complex.arg (toC (q₁ - p)) ≤ -2 * Real.pi / 3 then (0 : Fin 6)
        else if Complex.arg (toC (q₁ - p)) ≤ -Real.pi / 3 then 1
        else if Complex.arg (toC (q₁ - p)) ≤ 0 then 2
        else if Complex.arg (toC (q₁ - p)) ≤ Real.pi / 3 then 3
        else if Complex.arg (toC (q₁ - p)) ≤ 2 * Real.pi / 3 then 4
        else 5) =
        (if Complex.arg (toC (q₂ - p)) ≤ -2 * Real.pi / 3 then (0 : Fin 6)
        else if Complex.arg (toC (q₂ - p)) ≤ -Real.pi / 3 then 1
        else if Complex.arg (toC (q₂ - p)) ≤ 0 then 2
        else if Complex.arg (toC (q₂ - p)) ≤ Real.pi / 3 then 3
        else if Complex.arg (toC (q₂ - p)) ≤ 2 * Real.pi / 3 then 4
        else 5) := hsec_eq
    split_ifs at hsec' with h1 h2 h3 h4 h5 h6 h7' h8 h9 h10
    all_goals first
      | (rw [abs_lt]; constructor <;> linarith [harg₁.1, harg₂.1, harg₁.2, harg₂.2])
      | (exfalso; revert hsec'; decide)
  have hcos_gt : 1 / 2 < Real.cos (Complex.arg (toC (q₁ - p)) - Complex.arg (toC (q₂ - p))) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    refine Real.strictAntiOn_cos
      ⟨abs_nonneg _, by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      hdiff_lt
  rw [inner_toC hu₁ hu₂] at hinner_le
  linarith

/-- Corollary (Global Unit-Contact Edge Bound `|E₁| ≤ 3n`): For any unit-separated `A`, the number
of ordered unit pairs is at most `6 * A.card` (and unordered edges at most `3 * A.card`). -/
theorem ppl083_unit_edges_le_three_n {A : Finset (EuclideanSpace ℝ (Fin 2))}
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) :
    ((A ×ˢ A).filter (fun pq => dist pq.1 pq.2 = 1)).card ≤ 6 * A.card := by
  classical
  have hcard : ((A ×ˢ A).filter (fun pq => dist pq.1 pq.2 = 1)).card =
      ∑ p ∈ A, (A.filter (fun q => dist p q = 1)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  rw [hcard]
  calc ∑ p ∈ A, (A.filter (fun q => dist p q = 1)).card
      ≤ ∑ _p ∈ A, 6 := Finset.sum_le_sum fun p _ => ppl083_unit_degree_le_six hsep
    _ = 6 * A.card := by simp [mul_comm]

/-- Theorem 1c (Euler `K_3`-Free Planar Edge Ceiling): For any connected planar drawing with
`n` vertices, `e` edges, `F ≥ 1` faces satisfying Euler's formula `n + F = e + 2` and
triangle-free face-degree bound `4 * (F - 1) + b ≤ 2 * e` (outer face length `b`),
`2 * e ≤ 4 * n - 4 - b` (hence `e ≤ 2 * n - 4` whenever `b ≥ 4`). -/
theorem ppl083_euler_trifree_edge_bound {n e F b : ℕ}
    (hF : 1 ≤ F) (heuler : n + F = e + 2) (hface : 4 * (F - 1) + b ≤ 2 * e) :
    2 * e ≤ 4 * n - 4 - b ∧ (4 ≤ b → e ≤ 2 * n - 4) := by
  omega

end ContactPlanarity

section DiameterGraphAndOler

open scoped RealInnerProductSpace

/-- Theorem 2a (Diameter-Graph Opposite-Quadrilateral Exclusion):
Two diameter chords `[p₁, p₂]` and `[q₁, q₂]` of length `D > 0` in a set of diameter `≤ D` cannot
have crossing diagonals `[p₁, q₂]` and `[p₂, q₁]` unless they share an endpoint. -/
theorem ppl083_diam_opposite_quad_impossible
    {D : ℝ} (hD : 0 < D) {p₁ p₂ q₁ q₂ : EuclideanSpace ℝ (Fin 2)}
    (hp12 : dist p₁ p₂ = D) (hq12 : dist q₁ q₂ = D)
    (hp1q2 : dist p₁ q₂ ≤ D) (hp2q1 : dist p₂ q₁ ≤ D)
    (hcross : ¬ Disjoint (segment ℝ p₁ q₂) (segment ℝ p₂ q₁)) :
    p₁ = q₁ ∨ p₁ = q₂ ∨ p₂ = q₁ ∨ p₂ = q₂ := by
  rw [Set.not_disjoint_iff] at hcross
  rcases hcross with ⟨x, hxp, hxq⟩
  rw [segment_eq_image'] at hxp hxq
  rcases hxp with ⟨t, ht, hxp_val⟩
  rcases hxq with ⟨s, hs, hxq_val⟩
  set x := (1 - t) • p₁ + t • q₂
  have hxp_eq : (fun θ : ℝ => p₁ + θ • (q₂ - p₁)) t = x := by dsimp [x]; module
  have hxq_eq : (fun θ : ℝ => p₂ + θ • (q₁ - p₂)) s = (1 - s) • p₂ + s • q₁ := by module
  have hx_eq : x = (1 - s) • p₂ + s • q₁ := by
    rw [← hxp_eq, ← hxq_eq, hxp_val, hxq_val]
  have h12 : D ≤ dist p₁ x + dist x p₂ := by rw [← hp12]; exact dist_triangle _ _ _
  have hq : D ≤ dist q₁ x + dist x q₂ := by rw [← hq12]; exact dist_triangle _ _ _
  have hp1_x : dist p₁ x ≤ t * D := by
    dsimp [x]
    rw [dist_eq_norm, show p₁ - ((1 - t) • p₁ + t • q₂) = t • (p₁ - q₂) by module]
    rw [norm_smul, Real.norm_of_nonneg ht.1, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hp1q2 ht.1
  have hx_q2 : dist x q₂ ≤ (1 - t) * D := by
    dsimp [x]
    rw [dist_eq_norm, show (1 - t) • p₁ + t • q₂ - q₂ = (1 - t) • (p₁ - q₂) by module]
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2), ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hp1q2 (sub_nonneg.mpr ht.2)
  have hp2_x : dist x p₂ ≤ s * D := by
    rw [hx_eq, dist_eq_norm, show (1 - s) • p₂ + s • q₁ - p₂ = s • (q₁ - p₂) by module]
    rw [norm_smul, Real.norm_of_nonneg hs.1, ← dist_eq_norm, dist_comm q₁ p₂]
    exact mul_le_mul_of_nonneg_left hp2q1 hs.1
  have hq1_x : dist q₁ x ≤ (1 - s) * D := by
    rw [hx_eq, dist_eq_norm, show q₁ - ((1 - s) • p₂ + s • q₁) = (1 - s) • (q₁ - p₂) by module]
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hs.2), ← dist_eq_norm, dist_comm q₁ p₂]
    exact mul_le_mul_of_nonneg_left hp2q1 (sub_nonneg.mpr hs.2)
  have hdist_p1x : dist p₁ x = t * D := by linarith
  have hdist_xp2 : dist x p₂ = s * D := by linarith
  have hts_eq : t + s = 1 := by
    have : (t + s) * D = D := by linarith
    exact mul_right_cancel₀ hD.ne' (by linarith)
  have hs_eq : s = 1 - t := by linarith
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · have hs1 : s = 1 := by linarith
    have hx1 : x = p₁ := by dsimp [x]; simp
    have hx2 : x = q₁ := by rw [hx_eq, hs1]; simp
    exact Or.inl (hx1.symm.trans hx2)
  · rcases eq_or_lt_of_le ht.2 with rfl | ht_lt1
    · have hs0 : s = 0 := by linarith
      have hx1 : x = q₂ := by dsimp [x]; simp
      have hx2 : x = p₂ := by rw [hx_eq, hs0]; simp
      exact Or.inr (Or.inr (Or.inr (hx2.symm.trans hx1)))
    · have hs_pos : 0 < s := by linarith
      have hu_norm : ‖p₁ - q₂‖ = D := by
        have hle : t * D ≤ t * dist p₁ q₂ := by
          have : dist p₁ x = t * dist p₁ q₂ := by
            dsimp [x]
            rw [dist_eq_norm, show p₁ - ((1 - t) • p₁ + t • q₂) = t • (p₁ - q₂) by module,
              norm_smul, Real.norm_of_nonneg ht_pos.le, ← dist_eq_norm]
          linarith
        have hge : D ≤ dist p₁ q₂ := (mul_le_mul_iff_right₀ ht_pos).mp hle
        rw [← dist_eq_norm]; exact le_antisymm hp1q2 hge
      have hw_norm : ‖q₁ - p₂‖ = D := by
        have hle : s * D ≤ s * dist p₂ q₁ := by
          have : dist x p₂ = s * dist p₂ q₁ := by
            rw [hx_eq, dist_eq_norm, show (1 - s) • p₂ + s • q₁ - p₂ = s • (q₁ - p₂) by module,
              norm_smul, Real.norm_of_nonneg hs_pos.le, ← dist_eq_norm, dist_comm q₁ p₂]
          linarith
        have hge : D ≤ dist p₂ q₁ := (mul_le_mul_iff_right₀ hs_pos).mp hle
        rw [← dist_eq_norm, dist_comm]; exact le_antisymm hp2q1 hge
      set u := p₁ - q₂
      set w := q₁ - p₂
      have hp12_eq : p₁ - p₂ = t • u + (1 - t) • w := by
        have hsub1 : p₁ - x = t • u := by dsimp [x, u]; module
        have hsub2 : x - p₂ = (1 - t) • w := by rw [hx_eq, hs_eq]; dsimp [w]; module
        calc p₁ - p₂ = (p₁ - x) + (x - p₂) := by abel
          _ = t • u + (1 - t) • w := by rw [hsub1, hsub2]
      have hsq : ‖t • u + (1 - t) • w‖ ^ 2 = D ^ 2 := by
        rw [← hp12_eq, ← dist_eq_norm, hp12]
      have hid : ‖t • u + (1 - t) • w‖ ^ 2 =
          t * ‖u‖ ^ 2 + (1 - t) * ‖w‖ ^ 2 - t * (1 - t) * ‖u - w‖ ^ 2 := by
        have hsub_sq : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u w + ‖w‖ ^ 2 := norm_sub_sq_real u w
        rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_of_nonneg ht_pos.le,
          Real.norm_of_nonneg (sub_pos.mpr ht_lt1).le, real_inner_smul_left, real_inner_smul_right,
          hsub_sq]
        ring
      rw [hu_norm, hw_norm] at hid
      have hzero : t * (1 - t) * ‖u - w‖ ^ 2 = 0 := by linarith
      have huw : u = w := by
        have hprod_pos : 0 < t * (1 - t) := mul_pos ht_pos (sub_pos.mpr ht_lt1)
        have hnorm0 : ‖u - w‖ ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left hprod_pos.ne'
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm0))
      have hp2q2 : p₁ - p₂ = p₁ - q₂ := by
        rw [hp12_eq, ← huw]
        calc t • u + (1 - t) • u = (t + (1 - t)) • u := (add_smul _ _ _).symm
          _ = u := by simp
      exact Or.inr (Or.inr (Or.inr (sub_right_injective hp2q2)))

/-- Theorem 2b (Diameter-Chord Extreme Points): Every vertex incident to a chord of length `D > 0`
in a finite planar set `A` of diameter `≤ D` is an extreme point of `convexHull ℝ (A : Set ℝ²)`. -/
theorem ppl083_diam_extreme_point {A : Finset (EuclideanSpace ℝ (Fin 2))}
    {D : ℝ} (hD_max : ∀ a ∈ A, ∀ b ∈ A, dist a b ≤ D)
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ A) (hq : q ∈ A) (hpq : dist p q = D) :
    p ∈ (convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2)))).extremePoints ℝ := by
  refine ⟨subset_convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) hp, fun a ha b hb hx => ?_⟩
  rw [openSegment_eq_image'] at hx
  rcases hx with ⟨t, ⟨ht0, ht1⟩, hpt⟩
  have hball : convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Metric.closedBall q D :=
    convexHull_min (fun x hx => by rw [Metric.mem_closedBall]; exact hD_max x hx q hq)
      (convex_closedBall q D)
  have ha_le : ‖a - q‖ ≤ D := by simpa [Metric.mem_closedBall, dist_eq_norm] using hball ha
  have hb_le : ‖b - q‖ ≤ D := by simpa [Metric.mem_closedBall, dist_eq_norm] using hball hb
  have hD_nonneg : 0 ≤ D := hpq ▸ dist_nonneg
  have ha_sq : ‖a - q‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (a - q)]
  have hb_sq : ‖b - q‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (b - q)]
  have hdiff : p - q = (1 - t) • (a - q) + t • (b - q) := by
    rw [← hpt]; module
  have hid : ‖p - q‖ ^ 2 =
      (1 - t) * ‖a - q‖ ^ 2 + t * ‖b - q‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
    have hsub_sq : ‖a - b‖ ^ 2 = ‖a - q‖ ^ 2 - 2 * inner ℝ (a - q) (b - q) + ‖b - q‖ ^ 2 := by
      rw [show a - b = (a - q) - (b - q) by abel, norm_sub_sq_real]
    rw [hdiff, norm_add_sq_real, norm_smul, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.mpr ht1.le), Real.norm_of_nonneg ht0.le,
      real_inner_smul_left, real_inner_smul_right, hsub_sq]
    ring
  rw [← dist_eq_norm, hpq] at hid
  have hnonpos : t * (1 - t) * ‖a - b‖ ^ 2 ≤ 0 := by
    have h1 : (1 - t) * ‖a - q‖ ^ 2 ≤ (1 - t) * D ^ 2 :=
      mul_le_mul_of_nonneg_left ha_sq (sub_nonneg.mpr ht1.le)
    have h2 : t * ‖b - q‖ ^ 2 ≤ t * D ^ 2 :=
      mul_le_mul_of_nonneg_left hb_sq ht0.le
    linarith
  have hprod_pos : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
  have hnorm0 : ‖a - b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a - b‖]
  have hab : a = b := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm0))
  have hpt' : b = p := by
    have h1 : (fun θ : ℝ => a + θ • (b - a)) t = (1 - t) • a + t • b := by module
    rw [h1, hab, show (1 - t) • b + t • b = b by module] at hpt
    exact hpt
  exact hab.trans hpt'

/-- Theorem 2c (Oler–Bieberbach–Barbier Diameter Lower Bound):
From Oler's inequality `n ≤ (2 / √3) * Area + (1 / 2) * Perim + 1`, Bieberbach's isodiametric
inequality `Area ≤ (π / 4) * D^2`, and Barbier's bound `Perim ≤ π * D`, the diameter satisfies
`(D + √3 / 2)^2 ≥ (2 * √3 / π) * (n - 1) + 3 / 4`. -/
theorem ppl083_oler_diam_lower_bound {n : ℕ} {D Area Perim : ℝ}
    (_hD : 0 ≤ D)
    (holer : (n : ℝ) ≤ (2 / Real.sqrt 3) * Area + (1 / 2) * Perim + 1)
    (hbieb : Area ≤ (Real.pi / 4) * D ^ 2)
    (hbarb : Perim ≤ Real.pi * D) :
    (2 * Real.sqrt 3 / Real.pi) * ((n : ℝ) - 1) + 3 / 4 ≤ (D + Real.sqrt 3 / 2) ^ 2 := by
  have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn_bound : (n : ℝ) - 1 ≤ (Real.pi / (2 * Real.sqrt 3)) * D ^ 2 + (Real.pi / 2) * D := by
    have h1 : (2 / Real.sqrt 3) * Area ≤ (2 / Real.sqrt 3) * ((Real.pi / 4) * D ^ 2) :=
      mul_le_mul_of_nonneg_left hbieb (by positivity)
    have h2 : (1 / 2) * Perim ≤ (1 / 2) * (Real.pi * D) :=
      mul_le_mul_of_nonneg_left hbarb (by norm_num)
    linarith [show (2 / Real.sqrt 3) * ((Real.pi / 4) * D ^ 2) =
      (Real.pi / (2 * Real.sqrt 3)) * D ^ 2 by ring,
      show (1 / 2) * (Real.pi * D) = (Real.pi / 2) * D by ring]
  have hmul : (2 * Real.sqrt 3 / Real.pi) * ((n : ℝ) - 1) ≤
      (2 * Real.sqrt 3 / Real.pi) * ((Real.pi / (2 * Real.sqrt 3)) * D ^ 2 + (Real.pi / 2) * D) :=
    mul_le_mul_of_nonneg_left hn_bound (by positivity)
  have hsimp : (2 * Real.sqrt 3 / Real.pi) *
      ((Real.pi / (2 * Real.sqrt 3)) * D ^ 2 + (Real.pi / 2) * D) = D ^ 2 + Real.sqrt 3 * D := by
    field_simp
  rw [hsimp] at hmul
  have hid : (D + Real.sqrt 3 / 2) ^ 2 = D ^ 2 + Real.sqrt 3 * D + 3 / 4 := by
    ring_nf; rw [hsq3]; ring
  linarith

end DiameterGraphAndOler

section KKTAndVirial

private lemma diam_attained {A : Finset (EuclideanSpace ℝ (Fin 2))} (hA : 2 ≤ A.card) :
    (∃ p ∈ A, ∃ q ∈ A, dist p q = Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))) ∧
    (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))) ∧
    0 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hpair : (A ×ˢ A).Nonempty := hAne.product hAne
  let dists := (A ×ˢ A).image (fun pq => dist pq.1 pq.2)
  have hne : dists.Nonempty := hpair.image _
  let M := dists.max' hne
  have hM_mem := Finset.max'_mem dists hne
  rcases Finset.mem_image.mp hM_mem with ⟨⟨p₀, q₀⟩, hpq₀, hdist₀⟩
  rw [Finset.mem_product] at hpq₀
  have hle : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ M := fun p hp q hq =>
    Finset.le_max' dists _ (Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩)
  have hM_nonneg : 0 ≤ M := by
    change 0 ≤ dists.max' hne
    rw [← hdist₀]; exact dist_nonneg
  have hdiam_le : Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ≤ M :=
    Metric.diam_le_of_forall_dist_le hM_nonneg fun p hp q hq => hle p hp q hq
  have hle_diam : M ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) := by
    change dists.max' hne ≤ _
    rw [← hdist₀]
    exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hpq₀.1 hpq₀.2
  have hM_eq : M = Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) := le_antisymm hle_diam hdiam_le
  refine ⟨⟨p₀, hpq₀.1, q₀, hpq₀.2, hdist₀.trans hM_eq⟩, ?_, hM_eq ▸ hM_nonneg⟩
  intro p hp q hq; rw [← hM_eq]; exact hle p hp q hq

/-- Theorem 3a (No Strictly Improving First-Order Perturbation):
At any diameter-minimizing unit-separated `n`-point set `A` (`n ≥ 2`), there is no velocity field
`v` simultaneously expanding all unit-contact edges (`E₁`) and contracting all diameter edges (`E_D`). -/
theorem ppl083_no_strict_improving_velocity {A : Finset (EuclideanSpace ℝ (Fin 2))}
    (hcard : 2 ≤ A.card)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q)
    (hunit : ∃ p ∈ A, ∃ q ∈ A, dist p q = 1)
    (hmin : IsMinOn (fun B : Finset (EuclideanSpace ℝ (Fin 2)) =>
        Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))))
      {B | B.card = A.card ∧ (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
        (∃ p ∈ B, ∃ q ∈ B, dist p q = 1)} A)
    (v : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hv1 : ∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 < inner ℝ (p - q) (v p - v q))
    (hvD : ∀ p ∈ A, ∀ q ∈ A, dist p q = Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) →
      inner ℝ (p - q) (v p - v q) < 0) :
    False := by
  classical
  set D := Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨⟨pD, hpD, qD, hqD, hpqD⟩, hD_le, _⟩ := diam_attained hcard
  have h1_le_D : 1 ≤ D := by
    rcases hunit with ⟨p₁, hp1, q₁, hq1, hpq1⟩
    rw [← hpq1]; exact hD_le p₁ hp1 q₁ hq1
  have hD_pos : 0 < D := by linarith
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  set pairs := (A ×ˢ A).filter (fun pq => pq.1 ≠ pq.2)
  have hpairs_ne : pairs.Nonempty := ⟨(a₀, b₀), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨ha₀, hb₀⟩, hab₀⟩⟩
  let δ : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ := fun pq =>
    if 1 < dist pq.1 pq.2 then (dist pq.1 pq.2 - 1) / (‖v pq.1 - v pq.2‖ + 1) else 1
  let η : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ := fun pq =>
    if dist pq.1 pq.2 = D then
      (-2 * inner ℝ (pq.1 - pq.2) (v pq.1 - v pq.2)) / (‖v pq.1 - v pq.2‖ ^ 2 + 1)
    else (D - dist pq.1 pq.2) / (‖v pq.1 - v pq.2‖ + 1)
  have hpos_vals : ∀ pq ∈ pairs, 0 < min (δ pq) (η pq) := by
    intro pq hpq
    rw [Finset.mem_filter, Finset.mem_product] at hpq
    have hδ : 0 < δ pq := by
      dsimp [δ]
      split_ifs with hgt
      · exact div_pos (by linarith) (by positivity)
      · norm_num
    have hη : 0 < η pq := by
      dsimp [η]
      split_ifs with heq
      · have hneg := hvD pq.1 hpq.1.1 pq.2 hpq.1.2 heq
        exact div_pos (by linarith) (by positivity)
      · have hle := hD_le pq.1 hpq.1.1 pq.2 hpq.1.2
        have hlt : dist pq.1 pq.2 < D := lt_of_le_of_ne hle heq
        exact div_pos (by linarith) (by positivity)
    exact lt_min hδ hη
  let vals := pairs.image (fun pq => min (δ pq) (η pq))
  have hvals_ne : vals.Nonempty := hpairs_ne.image _
  let m_step := vals.min' hvals_ne
  have hm_pos : 0 < m_step := by
    change 0 < vals.min' hvals_ne
    have hmem := Finset.min'_mem vals hvals_ne
    rcases Finset.mem_image.mp hmem with ⟨pq, hpq, heq⟩
    rw [← heq]; exact hpos_vals pq hpq
  let t := m_step / 2
  have ht_pos : 0 < t := by dsimp [t]; linarith
  have ht_lt : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → t < δ (p, q) ∧ t < η (p, q) := by
    intro p hp q hq hne
    have hmem : min (δ (p, q)) (η (p, q)) ∈ vals :=
      Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hne⟩, rfl⟩
    have hm_le : m_step ≤ min (δ (p, q)) (η (p, q)) := Finset.min'_le vals _ hmem
    have ht_lt_m : t < m_step := by dsimp [t]; linarith
    exact ⟨lt_of_lt_of_le ht_lt_m (le_trans hm_le (min_le_left _ _)),
      lt_of_lt_of_le ht_lt_m (le_trans hm_le (min_le_right _ _))⟩
  have hpert : ∀ p ∈ A, ∀ q ∈ A, p ≠ q →
      1 < dist (p + t • v p) (q + t • v q) ∧ dist (p + t • v p) (q + t • v q) < D := by
    intro p hp q hq hne
    have hlt_pq := ht_lt p hp q hq hne
    have hdiff_eq : (p + t • v p) - (q + t • v q) = (p - q) + t • (v p - v q) := by module
    constructor
    · by_cases h1 : dist p q = 1
      · have hinn := hv1 p hp q hq h1
        have hsq : 1 < ‖(p + t • v p) - (q + t • v q)‖ ^ 2 := by
          rw [hdiff_eq, norm_add_sq_real, norm_smul, Real.norm_of_nonneg ht_pos.le,
            real_inner_smul_right, ← dist_eq_norm, h1]
          have hsq_nn : 0 ≤ (t * ‖v p - v q‖) ^ 2 := sq_nonneg _
          have h2t : 0 < 2 * (t * inner ℝ (p - q) (v p - v q)) := by positivity
          linarith
        rw [dist_eq_norm]
        nlinarith [norm_nonneg ((p + t • v p) - (q + t • v q))]
      · have hgt1 : 1 < dist p q := lt_of_le_of_ne (hsep p hp q hq hne) (Ne.symm h1)
        have hδ_lt : t < (dist p q - 1) / (‖v p - v q‖ + 1) := by
          have := hlt_pq.1; dsimp [δ] at this; rwa [if_pos hgt1] at this
        have hmul : t * (‖v p - v q‖ + 1) < dist p q - 1 := (lt_div_iff₀ (by positivity)).mp hδ_lt
        have htri : dist p q ≤ dist (p + t • v p) (q + t • v q) + t * ‖v p - v q‖ := by
          rw [dist_eq_norm, dist_eq_norm]
          calc ‖p - q‖ = ‖((p + t • v p) - (q + t • v q)) - t • (v p - v q)‖ := by
                rw [hdiff_eq]; abel_nf
            _ ≤ ‖(p + t • v p) - (q + t • v q)‖ + ‖t • (v p - v q)‖ := norm_sub_le _ _
            _ = ‖(p + t • v p) - (q + t • v q)‖ + t * ‖v p - v q‖ := by
                rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
        linarith
    · by_cases hD_eq : dist p q = D
      · have hη_lt : t < (-2 * inner ℝ (p - q) (v p - v q)) / (‖v p - v q‖ ^ 2 + 1) := by
          have := hlt_pq.2; dsimp [η] at this; rwa [if_pos hD_eq] at this
        have hmul : t * (‖v p - v q‖ ^ 2 + 1) < -2 * inner ℝ (p - q) (v p - v q) :=
          (lt_div_iff₀ (by positivity)).mp hη_lt
        have hsq : ‖(p + t • v p) - (q + t • v q)‖ ^ 2 < D ^ 2 := by
          rw [hdiff_eq, norm_add_sq_real, norm_smul, Real.norm_of_nonneg ht_pos.le,
            real_inner_smul_right, ← dist_eq_norm, hD_eq]
          have hid : D ^ 2 + 2 * (t * inner ℝ (p - q) (v p - v q)) + (t * ‖v p - v q‖) ^ 2 =
              D ^ 2 + t * (2 * inner ℝ (p - q) (v p - v q) + t * ‖v p - v q‖ ^ 2) := by ring
          rw [hid]
          have hneg_br : 2 * inner ℝ (p - q) (v p - v q) + t * ‖v p - v q‖ ^ 2 < -t := by linarith
          nlinarith
        rw [dist_eq_norm]
        nlinarith [norm_nonneg ((p + t • v p) - (q + t • v q))]
      · have hltD : dist p q < D := lt_of_le_of_ne (hD_le p hp q hq) hD_eq
        have hη_lt : t < (D - dist p q) / (‖v p - v q‖ + 1) := by
          have := hlt_pq.2; dsimp [η] at this; rwa [if_neg hD_eq] at this
        have hmul : t * (‖v p - v q‖ + 1) < D - dist p q := (lt_div_iff₀ (by positivity)).mp hη_lt
        have htri : dist (p + t • v p) (q + t • v q) ≤ dist p q + t * ‖v p - v q‖ := by
          rw [dist_eq_norm, dist_eq_norm, hdiff_eq]
          calc ‖(p - q) + t • (v p - v q)‖ ≤ ‖p - q‖ + ‖t • (v p - v q)‖ := norm_add_le _ _
            _ = ‖p - q‖ + t * ‖v p - v q‖ := by rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
        linarith
  let B := A.image (fun p => p + t • v p)
  have hB_inj : Set.InjOn (fun p => p + t • v p) (A : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p hp q hq heq
    dsimp only at heq
    by_contra hne
    have := (hpert p hp q hq hne).1
    rw [heq, dist_self] at this
    linarith
  have hB_card : B.card = A.card := Finset.card_image_of_injOn hB_inj
  have hB_sep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → 1 < dist x y := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    have hne : p ≠ q := fun heq => hxy (congrArg (fun z => z + t • v z) heq)
    exact (hpert p hp q hq hne).1
  have hB_diam : ∀ x ∈ B, ∀ y ∈ B, dist x y < D := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    by_cases heq : p = q
    · rw [heq, dist_self]; exact hD_pos
    · exact (hpert p hp q hq heq).2
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  let Bpairs := (B ×ˢ B).filter (fun xy => xy.1 ≠ xy.2)
  have hBp_ne : Bpairs.Nonempty := ⟨(x₀, y₀), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hx₀, hy₀⟩, hxy₀⟩⟩
  let Bdists := Bpairs.image (fun xy => dist xy.1 xy.2)
  have hBd_ne : Bdists.Nonempty := hBp_ne.image _
  let m_min := Bdists.min' hBd_ne
  have hm_min_mem := Finset.min'_mem Bdists hBd_ne
  rcases Finset.mem_image.mp hm_min_mem with ⟨⟨u₀, v₀⟩, huv₀, hdist_uv₀⟩
  rw [Finset.mem_filter, Finset.mem_product] at huv₀
  have hm_gt1 : 1 < m_min := by
    change 1 < Bdists.min' hBd_ne
    rw [← hdist_uv₀]; exact hB_sep u₀ huv₀.1.1 v₀ huv₀.1.2 huv₀.2
  have hm_le : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → m_min ≤ dist x y := fun x hx y hy hxy =>
    Finset.min'_le Bdists _ (Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩)
  let c := 1 / m_min
  have hc_pos : 0 < c := by positivity
  have hc_lt1 : c < 1 := by dsimp [c]; rw [div_lt_one (by linarith)]; exact hm_gt1
  let B' := B.image (fun x => c • x)
  have hB'_card : B'.card = A.card := by
    rw [Finset.card_image_of_injective _ (smul_right_injective _ hc_pos.ne'), hB_card]
  have hB'_sep : ∀ x ∈ B', ∀ y ∈ B', x ≠ y → 1 ≤ dist x y := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
    have huw : u ≠ w := fun heq => hxy (congrArg (fun z => c • z) heq)
    rw [dist_smul₀, Real.norm_of_nonneg hc_pos.le]
    have : m_min ≤ dist u w := hm_le u hu w hw huw
    dsimp [c]; rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]; linarith
  have hB'_unit : ∃ x ∈ B', ∃ y ∈ B', dist x y = 1 := by
    refine ⟨c • u₀, Finset.mem_image_of_mem _ huv₀.1.1,
      c • v₀, Finset.mem_image_of_mem _ huv₀.1.2, ?_⟩
    rw [dist_smul₀, Real.norm_of_nonneg hc_pos.le]
    have huv_eq : dist u₀ v₀ = m_min := hdist_uv₀
    rw [huv_eq]; dsimp [c]; field_simp
  have hB'_mem : B' ∈ {B : Finset (EuclideanSpace ℝ (Fin 2)) |
      B.card = A.card ∧ (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
        (∃ p ∈ B, ∃ q ∈ B, dist p q = 1)} := ⟨hB'_card, hB'_sep, hB'_unit⟩
  have hdiam_le : D ≤ Metric.diam (B' : Set (EuclideanSpace ℝ (Fin 2))) := hmin hB'_mem
  obtain ⟨⟨x₁, hx1, y₁, hy1, hxy1⟩, _, _⟩ := diam_attained (by omega : 2 ≤ B'.card)
  rcases Finset.mem_image.mp hx1 with ⟨u₁, hu1, rfl⟩
  rcases Finset.mem_image.mp hy1 with ⟨v₁, hv1, rfl⟩
  have hdist_lt : dist (c • u₁) (c • v₁) < D := by
    rw [dist_smul₀, Real.norm_of_nonneg hc_pos.le]
    have h1 := hB_diam u₁ hu1 v₁ hv1
    nlinarith [dist_nonneg (x := u₁) (y := v₁)]
  linarith

private lemma ofLp_equiv_symm {ι : Type*} (f : ι → ℝ) (i : ι) :
    ((WithLp.equiv 2 (ι → ℝ)).symm f).ofLp i = f i := rfl

private noncomputable def fromPairVec {N : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin 2)) (i : Fin N) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![z (i, 0), z (i, 1)]

private noncomputable def edgeVec {N : ℕ} (i j : Fin N) (u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin N × Fin 2) :=
  (WithLp.equiv 2 (Fin N × Fin 2 → ℝ)).symm fun kc =>
    if kc.1 = i then (if kc.1 = j then 0 else u kc.2) else if kc.1 = j then -u kc.2 else 0

private lemma inner_edgeVec {N : ℕ} {i j : Fin N} (hij : i ≠ j) (u : EuclideanSpace ℝ (Fin 2))
    (z : EuclideanSpace ℝ (Fin N × Fin 2)) :
    inner ℝ (edgeVec i j u) z = inner ℝ u (fromPairVec z i - fromPairVec z j) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  have hsum_i : ∀ k : Fin N, ∑ c : Fin 2,
      inner ℝ ((edgeVec i j u).ofLp (k, c)) (z.ofLp (k, c)) =
      if k = i then (u.ofLp 0 * z.ofLp (i, 0) + u.ofLp 1 * z.ofLp (i, 1))
      else if k = j then -(u.ofLp 0 * z.ofLp (j, 0) + u.ofLp 1 * z.ofLp (j, 1))
      else 0 := by
    intro k
    rw [Fin.sum_univ_two]
    simp only [RCLike.inner_apply, conj_trivial, edgeVec, ofLp_equiv_symm]
    by_cases hki : k = i
    · subst hki; simp [hij]; ring
    · by_cases hkj : k = j
      · subst hkj; simp [hki]; ring
      · simp [hki, hkj]
  simp_rw [hsum_i]
  have hsplit : ∀ k : Fin N,
      (if k = i then u.ofLp 0 * z.ofLp (i, 0) + u.ofLp 1 * z.ofLp (i, 1)
       else if k = j then -(u.ofLp 0 * z.ofLp (j, 0) + u.ofLp 1 * z.ofLp (j, 1)) else 0) =
      (if k = i then u.ofLp 0 * z.ofLp (i, 0) + u.ofLp 1 * z.ofLp (i, 1) else 0) +
      (if k = j then -(u.ofLp 0 * z.ofLp (j, 0) + u.ofLp 1 * z.ofLp (j, 1)) else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [hij]
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_pos]
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, PiLp.sub_apply, fromPairVec, ofLp_equiv_symm,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma fromPairVec_edgeVec {N : ℕ} {i j k : Fin N} (hij : i ≠ j)
    (u : EuclideanSpace ℝ (Fin 2)) :
    fromPairVec (edgeVec i j u) k =
      (if k = i then u else 0) + (if k = j then -u else 0) := by
  ext c
  dsimp [fromPairVec, edgeVec]
  fin_cases c <;>
  · by_cases hki : k = i
    · subst hki; simp [hij]
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]

private lemma fromPairVec_linear {N : ℕ} (c : ℝ) (z₁ z₂ : EuclideanSpace ℝ (Fin N × Fin 2))
    (k : Fin N) :
    fromPairVec (c • z₁) k = c • fromPairVec z₁ k ∧
    fromPairVec (z₁ + z₂) k = fromPairVec z₁ k + fromPairVec z₂ k ∧
    fromPairVec 0 k = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext t
    fin_cases t <;>
    simp [fromPairVec]

private lemma fromPairVec_sum {N : ℕ} {α : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℝ (Fin N × Fin 2)) (k : Fin N) :
    fromPairVec (∑ a ∈ s, f a) k = ∑ a ∈ s, fromPairVec (f a) k := by
  classical
  induction s using Finset.induction with
  | empty => simp [(fromPairVec_linear (0 : ℝ) 0 0 k).2.2]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, (fromPairVec_linear (1 : ℝ) _ _ k).2.1, ih]

private lemma fenchel_gordan_finset {N : ℕ} (S : Finset (EuclideanSpace ℝ (Fin N × Fin 2)))
    (hSne : S.Nonempty) :
    (0 : EuclideanSpace ℝ (Fin N × Fin 2)) ∈ convexHull ℝ (S : Set _) ∨
    ∃ z : EuclideanSpace ℝ (Fin N × Fin 2), ∀ u ∈ S, 0 < inner ℝ u z := by
  let K : Set (EuclideanSpace ℝ (Fin N × Fin 2)) :=
    convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin N × Fin 2)))
  have hK_comp : IsCompact K := Set.Finite.isCompact_convexHull (𝕜 := ℝ) S.finite_toSet
  have hK_ne : K.Nonempty := (Finset.coe_nonempty.mpr hSne).convexHull
  obtain ⟨z₀, hz₀_mem, hz₀_min⟩ :=
    hK_comp.exists_isMinOn hK_ne (continuous_norm.pow 2).continuousOn
  by_cases hz : z₀ = 0
  · exact Or.inl (hz ▸ hz₀_mem)
  · right
    refine ⟨z₀, fun u hu => ?_⟩
    have hz_sq : 0 < ‖z₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    have huK : u ∈ K := subset_convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin N × Fin 2))) hu
    have hconv_step : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → z₀ + t • (u - z₀) ∈ K := by
      intro t ht0 ht1
      have hcomb : (1 - t) • z₀ + t • u ∈ K :=
        (convex_convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin N × Fin 2))))
          hz₀_mem huK (sub_nonneg.mpr ht1) ht0 (by ring)
      convert hcomb using 1
      module
    have hge0 : 0 ≤ inner ℝ z₀ (u - z₀) := by
      by_contra hneg
      push Not at hneg
      let t₀ := min (1 / 2 : ℝ) ((-inner ℝ z₀ (u - z₀)) / (‖u - z₀‖ ^ 2 + 1))
      have ht0_pos : 0 < t₀ := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
      have ht0_le1 : t₀ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
      have hmin_t : ‖z₀‖ ^ 2 ≤ ‖z₀ + t₀ • (u - z₀)‖ ^ 2 := hz₀_min (hconv_step ht0_pos.le ht0_le1)
      rw [norm_add_sq_real, norm_smul, Real.norm_of_nonneg ht0_pos.le,
        real_inner_smul_right] at hmin_t
      have hmul : t₀ * (‖u - z₀‖ ^ 2 + 1) ≤ -inner ℝ z₀ (u - z₀) :=
        (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
      have hid : ‖z₀‖ ^ 2 + 2 * (t₀ * inner ℝ z₀ (u - z₀)) + (t₀ * ‖u - z₀‖) ^ 2 =
          ‖z₀‖ ^ 2 + t₀ * (2 * inner ℝ z₀ (u - z₀) + t₀ * ‖u - z₀‖ ^ 2) := by ring
      rw [hid] at hmin_t
      have hneg_br : 2 * inner ℝ z₀ (u - z₀) + t₀ * ‖u - z₀‖ ^ 2 < 0 := by linarith
      nlinarith
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at hge0
    rw [real_inner_comm]; linarith

private lemma weights_pullback {α E : Type*} [DecidableEq α] [DecidableEq E]
    [AddCommGroup E] [Module ℝ E]
    (T : Finset α) (hT : T.Nonempty) (vec : α → E)
    (h0 : (0 : E) ∈ convexHull ℝ ((T.image vec : Finset E) : Set E)) :
    ∃ wT : α → ℝ, (∀ x, 0 ≤ wT x) ∧ (∀ x ∉ T, wT x = 0) ∧
      ∑ x ∈ T, wT x = 1 ∧ ∑ x ∈ T, wT x • vec x = 0 := by
  classical
  let S := T.image vec
  rw [Finset.mem_convexHull] at h0
  obtain ⟨w, hw_nn, hw_sum, hw_cm⟩ := h0
  rw [Finset.centerMass_eq_of_sum_1 S id hw_sum] at hw_cm
  simp only [id_eq] at hw_cm
  let x₀ := hT.choose
  let pre : E → α := fun u =>
    if hu : u ∈ S then Classical.choose (Finset.mem_image.mp hu) else x₀
  have hpre_spec : ∀ u ∈ S, pre u ∈ T ∧ vec (pre u) = u := fun u hu => by
    dsimp [pre]; rw [dif_pos hu]; exact Classical.choose_spec (Finset.mem_image.mp hu)
  let wT : α → ℝ := fun x => if x ∈ T ∧ pre (vec x) = x then w (vec x) else 0
  refine ⟨wT, ?_, ?_, ?_, ?_⟩
  · intro x; dsimp [wT]
    split_ifs with h
    · exact hw_nn _ (Finset.mem_image_of_mem vec h.1)
    · exact le_rfl
  · intro x hx; dsimp [wT]; rw [if_neg (fun h => hx h.1)]
  · rw [← hw_sum, ← Finset.sum_fiberwise_of_maps_to (g := vec) (t := S)
      (fun x hx => Finset.mem_image_of_mem vec hx)]
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨hpre_T, hpre_eq⟩ := hpre_spec u hu
    rw [← Finset.add_sum_erase _ _ (Finset.mem_filter.mpr ⟨hpre_T, hpre_eq⟩)]
    have hpre_val : wT (pre u) = w u := by
      dsimp [wT]; rw [if_pos ⟨hpre_T, by rw [hpre_eq]⟩, hpre_eq]
    have hrest_zero : ∑ x ∈ (T.filter (fun x => vec x = u)).erase (pre u), wT x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_erase, Finset.mem_filter] at hx
      dsimp [wT]; rw [if_neg]; rintro ⟨_, hpx⟩; rw [hx.2.2] at hpx; exact hx.1 hpx.symm
    rw [hpre_val, hrest_zero, add_zero]
  · rw [← hw_cm, ← Finset.sum_fiberwise_of_maps_to (g := vec) (t := S)
      (fun x hx => Finset.mem_image_of_mem vec hx)]
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨hpre_T, hpre_eq⟩ := hpre_spec u hu
    rw [← Finset.add_sum_erase _ _ (Finset.mem_filter.mpr ⟨hpre_T, hpre_eq⟩)]
    have hpre_val : wT (pre u) • vec (pre u) = w u • u := by
      dsimp [wT]; rw [if_pos ⟨hpre_T, by rw [hpre_eq]⟩, hpre_eq]
    have hrest_zero : ∑ x ∈ (T.filter (fun x => vec x = u)).erase (pre u), wT x • vec x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_erase, Finset.mem_filter] at hx
      dsimp [wT]; rw [if_neg, zero_smul]; rintro ⟨_, hpx⟩
      rw [hx.2.2] at hpx; exact hx.1 hpx.symm
    rw [hpre_val, hrest_zero, add_zero]

private lemma sum_bool_triple_kkt {N : ℕ}
    (T : Finset (Bool × Fin N × Fin N))
    (hT_lt : ∀ x ∈ T, x.2.1 < x.2.2)
    (wT : Bool × Fin N × Fin N → ℝ) (hwT_out : ∀ x ∉ T, wT x = 0)
    (ptOf : Fin N → EuclideanSpace ℝ (Fin 2)) (b : Bool) (k : Fin N) :
    (∑ j : Fin N, (wT (b, k, j) + wT (b, j, k)) • (ptOf k - ptOf j)) =
    ∑ x ∈ T with x.1 = b,
      (if x.2.1 = k then wT x • (ptOf k - ptOf x.2.2)
       else if x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0) := by
  have hsplit_j : ∀ j : Fin N,
      (wT (b, k, j) + wT (b, j, k)) • (ptOf k - ptOf j) =
      (if (b, k, j) ∈ T then wT (b, k, j) • (ptOf k - ptOf j) else 0) +
      (if (b, j, k) ∈ T then wT (b, j, k) • (ptOf k - ptOf j) else 0) := by
    intro j; rw [add_smul]; congr 1
    · by_cases hm : (b, k, j) ∈ T <;> simp [hm, hwT_out]
    · by_cases hm : (b, j, k) ∈ T <;> simp [hm, hwT_out]
  simp_rw [hsplit_j, Finset.sum_add_distrib]
  have h1 : (∑ j : Fin N, if (b, k, j) ∈ T then wT (b, k, j) • (ptOf k - ptOf j) else 0) =
      ∑ x ∈ T with x.1 = b, if x.2.1 = k then wT x • (ptOf k - ptOf x.2.2) else 0 := by
    rw [Finset.sum_filter]
    have h_univ : (∑ x ∈ T, if x.1 = b then if x.2.1 = k then wT x • (ptOf k - ptOf x.2.2) else 0 else 0) =
        ∑ b' : Bool, ∑ a : Fin N, ∑ j : Fin N,
          if (b', a, j) ∈ T ∧ b' = b ∧ a = k then wT (b', a, j) • (ptOf k - ptOf j) else 0 := by
      have hs : (∑ x ∈ T, if x.1 = b then if x.2.1 = k then wT x • (ptOf k - ptOf x.2.2) else 0 else 0) =
          ∑ x : Bool × Fin N × Fin N,
            if x ∈ T ∧ x.1 = b ∧ x.2.1 = k then wT x • (ptOf k - ptOf x.2.2) else 0 := by
        symm; rw [← Finset.sum_subset (Finset.subset_univ T)]
        · refine Finset.sum_congr rfl fun x hx => ?_; by_cases h1 : x.1 = b <;> by_cases h2 : x.2.1 = k <;> simp [hx, h1, h2]
        · intro x _ hx; simp [hx]
      rw [hs, Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
    rw [h_univ]
    have hb_eq : ∀ b' : Bool, (∑ a : Fin N, ∑ j : Fin N,
        if (b', a, j) ∈ T ∧ b' = b ∧ a = k then wT (b', a, j) • (ptOf k - ptOf j) else 0) =
        if b' = b then ∑ j : Fin N, if (b, k, j) ∈ T then wT (b, k, j) • (ptOf k - ptOf j) else 0 else 0 := by
      intro b'; by_cases hb : b' = b
      · subst hb; rw [if_pos rfl]
        simp only [true_and]
        have ha_eq : ∀ a : Fin N, (∑ j : Fin N,
            if (b', a, j) ∈ T ∧ a = k then wT (b', a, j) • (ptOf k - ptOf j) else 0) =
            if a = k then ∑ j : Fin N, if (b', k, j) ∈ T then wT (b', k, j) • (ptOf k - ptOf j) else 0 else 0 := by
          intro a; by_cases ha : a = k <;> simp [ha]
        simp_rw [ha_eq]
        rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
      · rw [if_neg hb]; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hb]
    simp_rw [hb_eq]
    rw [Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ b)]
  have h2 : (∑ j : Fin N, if (b, j, k) ∈ T then wT (b, j, k) • (ptOf k - ptOf j) else 0) =
      ∑ x ∈ T with x.1 = b, if x.2.1 ≠ k ∧ x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0 := by
    rw [Finset.sum_filter]
    have h_univ : (∑ x ∈ T, if x.1 = b then if x.2.1 ≠ k ∧ x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0 else 0) =
        ∑ b' : Bool, ∑ a : Fin N, ∑ j : Fin N,
          if (b', a, j) ∈ T ∧ b' = b ∧ a ≠ k ∧ j = k then wT (b', a, j) • (ptOf k - ptOf a) else 0 := by
      have hs : (∑ x ∈ T, if x.1 = b then if x.2.1 ≠ k ∧ x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0 else 0) =
          ∑ x : Bool × Fin N × Fin N,
            if x ∈ T ∧ x.1 = b ∧ x.2.1 ≠ k ∧ x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0 := by
        symm; rw [← Finset.sum_subset (Finset.subset_univ T)]
        · refine Finset.sum_congr rfl fun x hx => ?_
          by_cases h1 : x.1 = b <;> by_cases h2 : x.2.1 ≠ k ∧ x.2.2 = k <;> simp [hx, h1, h2]
        · intro x _ hx; simp [hx]
      rw [hs, Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
    rw [h_univ]
    have hb_eq : ∀ b' : Bool, (∑ a : Fin N, ∑ j : Fin N,
        if (b', a, j) ∈ T ∧ b' = b ∧ a ≠ k ∧ j = k then wT (b', a, j) • (ptOf k - ptOf a) else 0) =
        if b' = b then ∑ j : Fin N, if (b, j, k) ∈ T then wT (b, j, k) • (ptOf k - ptOf j) else 0 else 0 := by
      intro b'; by_cases hb : b' = b
      · subst hb; rw [if_pos rfl]
        simp only [true_and]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hj_eq : ∀ j : Fin N, (if (b', a, j) ∈ T ∧ a ≠ k ∧ j = k
            then wT (b', a, j) • (ptOf k - ptOf a) else 0) =
            if j = k then (if (b', a, k) ∈ T then wT (b', a, k) • (ptOf k - ptOf a) else 0) else 0 := by
          intro j; by_cases hj : j = k
          · subst hj; by_cases ha : a = j
            · subst ha; have hn : (b', a, a) ∉ T := fun h => lt_irrefl a (hT_lt _ h)
              simp [hn]
            · simp [ha]
          · simp [hj]
        simp_rw [hj_eq]
        rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
      · rw [if_neg hb]; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hb]
    simp_rw [hb_eq]
    rw [Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ b)]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx1 : x.2.1 = k <;> by_cases hx2 : x.2.2 = k <;> simp [hx1, hx2]

private lemma sum_bool_triple_scalar {N : ℕ}
    (T : Finset (Bool × Fin N × Fin N)) (wT : Bool × Fin N × Fin N → ℝ)
    (hwT_out : ∀ x ∉ T, wT x = 0) (b : Bool) :
    (∑ i : Fin N, ∑ j : Fin N, wT (b, i, j)) = ∑ x ∈ T with x.1 = b, wT x := by
  rw [Finset.sum_filter]
  have hs : (∑ x ∈ T, if x.1 = b then wT x else 0) =
      ∑ x : Bool × Fin N × Fin N, if x ∈ T ∧ x.1 = b then wT x else 0 := by
    symm; rw [← Finset.sum_subset (Finset.subset_univ T)]
    · refine Finset.sum_congr rfl fun x hx => ?_; by_cases h : x.1 = b <;> simp [hx, h]
    · intro x _ hx; simp [hx]
  rw [hs, Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
  have hb_eq : ∀ b' : Bool,
      (∑ i : Fin N, ∑ j : Fin N, if (b', i, j) ∈ T ∧ b' = b then wT (b', i, j) else 0) =
      if b' = b then ∑ i : Fin N, ∑ j : Fin N, wT (b, i, j) else 0 := by
    intro b'; by_cases hb : b' = b
    · subst hb; rw [if_pos rfl]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hm : (b', i, j) ∈ T <;> simp [hm, hwT_out]
    · rw [if_neg hb]; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hb]
  simp_rw [hb_eq]
  rw [Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ b)]

private lemma virial_alg_identity (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hcsymm : ∀ p q, c p q = c q p) :
    2 * ∑ p ∈ A, inner ℝ p (∑ q ∈ A, c p q • (p - q)) =
    ∑ p ∈ A, ∑ q ∈ A, c p q * ‖p - q‖ ^ 2 := by
  have h1 : ∑ p ∈ A, inner ℝ p (∑ q ∈ A, c p q • (p - q)) =
      ∑ p ∈ A, ∑ q ∈ A, c p q * inner ℝ p (p - q) :=
    Finset.sum_congr rfl fun p _ => by
      rw [inner_sum]; exact Finset.sum_congr rfl fun q _ => real_inner_smul_right _ _ _
  rw [h1]
  have hcomm : ∑ p ∈ A, ∑ q ∈ A, c p q * inner ℝ p (p - q) =
      ∑ p ∈ A, ∑ q ∈ A, c p q * inner ℝ q (q - p) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hcsymm q p]
  calc 2 * ∑ p ∈ A, ∑ q ∈ A, c p q * inner ℝ p (p - q)
      = (∑ p ∈ A, ∑ q ∈ A, c p q * inner ℝ p (p - q)) +
        (∑ p ∈ A, ∑ q ∈ A, c p q * inner ℝ q (q - p)) := by rw [two_mul]; nth_rw 2 [hcomm]
    _ = ∑ p ∈ A, ∑ q ∈ A, (c p q * inner ℝ p (p - q) + c p q * inner ℝ q (q - p)) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun p _ => (Finset.sum_add_distrib).symm
    _ = ∑ p ∈ A, ∑ q ∈ A, c p q * ‖p - q‖ ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [← mul_add, show inner ℝ p (p - q) + inner ℝ q (q - p) = inner ℝ (p - q) (p - q) by
          simp only [inner_sub_left, inner_sub_right, real_inner_comm q p]; ring,
          real_inner_self_eq_norm_sq]

/-- Theorem 3b (KKT Equilibrium Stress & Virial Identity):
At any diameter-minimizing unit-separated `n`-point set `A` (`n ≥ 2`), there exist nonnegative
symmetric stresses `ω, λ` supported on `E₁` and `E_D` respectively, satisfying the vertex force
balance `∑_q ω_{pq}(p - q) - ∑_q λ_{pq}(p - q) = 0` for all `p ∈ A` and the exact Virial
identity `∑_{p,q} ω_{pq} = D^2 * ∑_{p,q} λ_{pq} > 0`. -/
theorem ppl083_kkt_equilibrium_and_virial {A : Finset (EuclideanSpace ℝ (Fin 2))}
    (hcard : 2 ≤ A.card)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q)
    (hunit : ∃ p ∈ A, ∃ q ∈ A, dist p q = 1)
    (hmin : IsMinOn (fun B : Finset (EuclideanSpace ℝ (Fin 2)) =>
        Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))))
      {B | B.card = A.card ∧ (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
        (∃ p ∈ B, ∃ q ∈ B, dist p q = 1)} A) :
    ∃ ω lam : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ p q, 0 ≤ ω p q ∧ 0 ≤ lam p q) ∧
      (∀ p q, ω p q = ω q p ∧ lam p q = lam q p) ∧
      (∀ p q, 0 < ω p q → p ∈ A ∧ q ∈ A ∧ dist p q = 1) ∧
      (∀ p q, 0 < lam p q → p ∈ A ∧ q ∈ A ∧
        dist p q = Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ p ∈ A, ∑ q ∈ A, ω p q • (p - q) - ∑ q ∈ A, lam p q • (p - q) = 0) ∧
      (0 < ∑ p ∈ A, ∑ q ∈ A, ω p q) ∧
      (0 < ∑ p ∈ A, ∑ q ∈ A, lam p q) ∧
      (∑ p ∈ A, ∑ q ∈ A, ω p q =
        Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ^ 2 *
          ∑ p ∈ A, ∑ q ∈ A, lam p q) := by
  classical
  let D := Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨⟨_, _, _, _, _⟩, hD_le, _⟩ := diam_attained hcard
  have h1_le_D : 1 ≤ D := by
    rcases hunit with ⟨p₁, hp1, q₁, hq1, hpq1⟩
    rw [← hpq1]; exact hD_le p₁ hp1 q₁ hq1
  have hD_pos : 0 < D := by linarith
  let N := A.card
  let idx : Fin N ≃ A := A.equivFin.symm
  let ptOf : Fin N → EuclideanSpace ℝ (Fin 2) := fun i => (idx i).1
  have hpt_mem : ∀ i, ptOf i ∈ A := fun i => (idx i).2
  let T : Finset (Bool × Fin N × Fin N) := Finset.univ.filter fun x =>
    x.2.1 < x.2.2 ∧
      (if x.1 then dist (ptOf x.2.1) (ptOf x.2.2) = 1
       else dist (ptOf x.2.1) (ptOf x.2.2) = D)
  have hT_ne : T.Nonempty := by
    rcases hunit with ⟨p₁, hp1, q₁, hq1, hpq1⟩
    have hpq_ne : p₁ ≠ q₁ := fun h => by rw [h, dist_self] at hpq1; norm_num at hpq1
    let i₁ := idx.symm ⟨p₁, hp1⟩
    let j₁ := idx.symm ⟨q₁, hq1⟩
    have hij_ne : i₁ ≠ j₁ := fun h => hpq_ne (by
      have := congrArg idx h; simp [i₁, j₁] at this; exact this)
    rcases lt_or_gt_of_ne hij_ne with hlt | hlt
    · exact ⟨(true, i₁, j₁), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, by simpa [ptOf, i₁, j₁] using hpq1⟩⟩
    · exact ⟨(true, j₁, i₁), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, by simpa [ptOf, i₁, j₁, dist_comm] using hpq1⟩⟩
  let vec : Bool × Fin N × Fin N → EuclideanSpace ℝ (Fin N × Fin 2) := fun x =>
    if x.1 then edgeVec x.2.1 x.2.2 (ptOf x.2.1 - ptOf x.2.2)
    else edgeVec x.2.1 x.2.2 (-(ptOf x.2.1 - ptOf x.2.2))
  have h0_mem : (0 : EuclideanSpace ℝ (Fin N × Fin 2)) ∈ convexHull ℝ ((T.image vec : Finset _) : Set _) := by
    rcases fenchel_gordan_finset (T.image vec) (hT_ne.image vec) with h0 | ⟨z₀, hz₀⟩
    · exact h0
    · exfalso
      let v : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun p =>
        if hp : p ∈ A then fromPairVec z₀ (idx.symm ⟨p, hp⟩) else 0
      have hpair_sign : ∀ (b : Bool) (p q : EuclideanSpace ℝ (Fin 2)),
          p ∈ A → q ∈ A → dist p q = (if b then 1 else D) →
          0 < (if b then inner ℝ (p - q) (v p - v q) else -inner ℝ (p - q) (v p - v q)) := by
        intro b p q hp hq hdist
        have hpq_ne : p ≠ q := fun h => by rw [h, dist_self] at hdist; split_ifs at hdist <;> linarith
        let i := idx.symm ⟨p, hp⟩
        let j := idx.symm ⟨q, hq⟩
        have hij : i ≠ j := fun h => hpq_ne (by have := congrArg idx h; simp [i, j] at this; exact this)
        have hpi : ptOf i = p := by dsimp [ptOf, i]; simp
        have hqj : ptOf j = q := by dsimp [ptOf, j]; simp
        have hvp : v p = fromPairVec z₀ i := dif_pos hp
        have hvq : v q = fromPairVec z₀ j := dif_pos hq
        rw [hvp, hvq]
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · have hmem : vec (b, i, j) ∈ T.image vec := Finset.mem_image_of_mem vec
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, by cases b <;> simpa [hpi, hqj] using hdist⟩)
          have hge := hz₀ _ hmem
          cases b
          · dsimp [vec] at hge
            rw [inner_edgeVec hij, hpi, hqj, inner_neg_left] at hge
            simpa using hge
          · dsimp [vec] at hge
            rw [inner_edgeVec hij, hpi, hqj] at hge
            simpa using hge
        · have hmem : vec (b, j, i) ∈ T.image vec := Finset.mem_image_of_mem vec
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, by cases b <;> simpa [hpi, hqj, dist_comm] using hdist⟩)
          have hge := hz₀ _ hmem
          have hflip : inner ℝ (q - p) (fromPairVec z₀ j - fromPairVec z₀ i) =
              inner ℝ (p - q) (fromPairVec z₀ i - fromPairVec z₀ j) := by
            rw [show q - p = -(p - q) by abel,
              show fromPairVec z₀ j - fromPairVec z₀ i = -(fromPairVec z₀ i - fromPairVec z₀ j) by abel,
              inner_neg_left, inner_neg_right, neg_neg]
          cases b
          · dsimp [vec] at hge
            rw [inner_edgeVec hij.symm, hqj, hpi, inner_neg_left, hflip] at hge
            simpa using hge
          · dsimp [vec] at hge
            rw [inner_edgeVec hij.symm, hqj, hpi, hflip] at hge
            simpa using hge
      exact ppl083_no_strict_improving_velocity hcard hsep hunit hmin v
        (fun p hp q hq h1 => by simpa using hpair_sign true p q hp hq (by simpa using h1))
        (fun p hp q hq hD => by
          have := hpair_sign false p q hp hq (by simpa using hD)
          simp at this; exact this)
  obtain ⟨wT, hwT_nn, hwT_out, hwT_sum, hwT_vec⟩ := weights_pullback T hT_ne vec h0_mem
  let ω : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ := fun p q =>
    if hp : p ∈ A then if hq : q ∈ A then
      wT (true, idx.symm ⟨p, hp⟩, idx.symm ⟨q, hq⟩) +
      wT (true, idx.symm ⟨q, hq⟩, idx.symm ⟨p, hp⟩) else 0 else 0
  let lam : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ := fun p q =>
    if hp : p ∈ A then if hq : q ∈ A then
      wT (false, idx.symm ⟨p, hp⟩, idx.symm ⟨q, hq⟩) +
      wT (false, idx.symm ⟨q, hq⟩, idx.symm ⟨p, hp⟩) else 0 else 0
  have hω_lam_nn : ∀ p q, 0 ≤ ω p q ∧ 0 ≤ lam p q := fun p q => by
    constructor <;> dsimp [ω, lam]
    · by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;> simp [hp, hq]
      exact add_nonneg (hwT_nn _) (hwT_nn _)
    · by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;> simp [hp, hq]
      exact add_nonneg (hwT_nn _) (hwT_nn _)
  have hω_lam_symm : ∀ p q, ω p q = ω q p ∧ lam p q = lam q p := fun p q => by
    constructor <;> · dsimp [ω, lam]; by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;> simp [hp, hq, add_comm]
  have hω_supp : ∀ p q, 0 < ω p q → p ∈ A ∧ q ∈ A ∧ dist p q = 1 := by
    intro p q hpos; dsimp [ω] at hpos
    split_ifs at hpos with hp hq
    · refine ⟨hp, hq, ?_⟩; by_contra hne1
      have h1 : wT (true, idx.symm ⟨p, hp⟩, idx.symm ⟨q, hq⟩) = 0 :=
        hwT_out _ fun h => by rw [Finset.mem_filter] at h; exact hne1 (by simpa [ptOf] using h.2.2)
      have h2 : wT (true, idx.symm ⟨q, hq⟩, idx.symm ⟨p, hp⟩) = 0 :=
        hwT_out _ fun h => by rw [Finset.mem_filter] at h; exact hne1 (by simpa [ptOf, dist_comm] using h.2.2)
      linarith
    · exact absurd hpos (lt_irrefl _)
    · exact absurd hpos (lt_irrefl _)
  have hlam_supp : ∀ p q, 0 < lam p q → p ∈ A ∧ q ∈ A ∧ dist p q = D := by
    intro p q hpos; dsimp [lam] at hpos
    split_ifs at hpos with hp hq
    · refine ⟨hp, hq, ?_⟩; by_contra hneD
      have h1 : wT (false, idx.symm ⟨p, hp⟩, idx.symm ⟨q, hq⟩) = 0 :=
        hwT_out _ fun h => by rw [Finset.mem_filter] at h; exact hneD (by simpa [ptOf] using h.2.2)
      have h2 : wT (false, idx.symm ⟨q, hq⟩, idx.symm ⟨p, hp⟩) = 0 :=
        hwT_out _ fun h => by rw [Finset.mem_filter] at h; exact hneD (by simpa [ptOf, dist_comm] using h.2.2)
      linarith
    · exact absurd hpos (lt_irrefl _)
    · exact absurd hpos (lt_irrefl _)
  have hT_lt : ∀ x ∈ T, x.2.1 < x.2.2 := fun x hx => (Finset.mem_filter.mp hx).2.1
  have hsum_A_vec : ∀ (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      ∑ q ∈ A, f q = ∑ j : Fin N, f (ptOf j) := fun f => by
    rw [← Finset.sum_attach A f, ← Finset.univ_eq_attach]
    exact Fintype.sum_equiv idx.symm (fun x : ↥A => f ↑x) (fun j => f (ptOf j)) fun x => by
      dsimp [ptOf]; simp
  have hsum_A_R : ∀ (f : EuclideanSpace ℝ (Fin 2) → ℝ),
      ∑ q ∈ A, f q = ∑ j : Fin N, f (ptOf j) := fun f => by
    rw [← Finset.sum_attach A f, ← Finset.univ_eq_attach]
    exact Fintype.sum_equiv idx.symm (fun x : ↥A => f ↑x) (fun j => f (ptOf j)) fun x => by
      dsimp [ptOf]; simp
  have hbal : ∀ p ∈ A, ∑ q ∈ A, ω p q • (p - q) - ∑ q ∈ A, lam p q • (p - q) = 0 := by
    intro p hp
    let k := idx.symm ⟨p, hp⟩
    have hpk : ptOf k = p := by dsimp [ptOf, k]; simp
    have hzero_k : ∑ x ∈ T, fromPairVec (wT x • vec x) k = 0 := by
      rw [← fromPairVec_sum, hwT_vec]; exact (fromPairVec_linear (0 : ℝ) 0 0 k).2.2
    have hpart := Finset.sum_filter_add_sum_filter_not T (fun x => x.1 = true)
      (fun x => fromPairVec (wT x • vec x) k)
    have hnot_eq : T.filter (fun x => ¬ x.1 = true) = T.filter (fun x => x.1 = false) := by
      ext x; simp [Bool.not_eq_true]
    rw [hnot_eq, hzero_k] at hpart
    have hterm : ∀ x ∈ T, fromPairVec (wT x • vec x) k =
        if x.1 then
          (if x.2.1 = k then wT x • (ptOf k - ptOf x.2.2)
           else if x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0)
        else
          -(if x.2.1 = k then wT x • (ptOf k - ptOf x.2.2)
            else if x.2.2 = k then wT x • (ptOf k - ptOf x.2.1) else 0) := by
      intro x hx
      rw [(fromPairVec_linear (wT x) (vec x) 0 k).1]
      dsimp [vec]
      cases hb : x.1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [fromPairVec_edgeVec (ne_of_lt (hT_lt x hx))]
        by_cases h1 : k = x.2.1
        · rw [if_pos h1, if_neg (h1 ▸ ne_of_lt (hT_lt x hx)), if_pos h1.symm, ← h1]; simp; module
        · by_cases h2 : k = x.2.2
          · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm, ← h2]; simp; module
          · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; simp
      · simp only [↓reduceIte]
        rw [fromPairVec_edgeVec (ne_of_lt (hT_lt x hx))]
        by_cases h1 : k = x.2.1
        · rw [if_pos h1, if_neg (h1 ▸ ne_of_lt (hT_lt x hx)), if_pos h1.symm, ← h1, add_zero]
        · by_cases h2 : k = x.2.2
          · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm, ← h2, zero_add]; module
          · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2), add_zero, smul_zero]
    have hsum_ω : ∑ q ∈ A, ω p q • (p - q) = ∑ x ∈ T with x.1 = true,
        fromPairVec (wT x • vec x) k := by
      rw [hsum_A_vec]
      trans (∑ j : Fin N, (wT (true, k, j) + wT (true, j, k)) • (ptOf k - ptOf j))
      · refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [ω]; rw [dif_pos hp, dif_pos (hpt_mem j)]
        have hj : idx.symm ⟨ptOf j, hpt_mem j⟩ = j := by dsimp [ptOf]; simp
        rw [hj, hpk]
      · rw [sum_bool_triple_kkt T hT_lt wT hwT_out ptOf true k]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_filter] at hx; rw [hterm x hx.1, if_pos hx.2]
    have hsum_lam : ∑ q ∈ A, lam p q • (p - q) = - ∑ x ∈ T with x.1 = false,
        fromPairVec (wT x • vec x) k := by
      rw [hsum_A_vec]
      trans (∑ j : Fin N, (wT (false, k, j) + wT (false, j, k)) • (ptOf k - ptOf j))
      · refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [lam]; rw [dif_pos hp, dif_pos (hpt_mem j)]
        have hj : idx.symm ⟨ptOf j, hpt_mem j⟩ = j := by dsimp [ptOf]; simp
        rw [hj, hpk]
      · rw [sum_bool_triple_kkt T hT_lt wT hwT_out ptOf false k, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_filter] at hx
        have hxf : x.1 ≠ true := by rw [hx.2]; decide
        rw [hterm x hx.1, if_neg hxf, neg_neg]
    rw [hsum_ω, hsum_lam, sub_neg_eq_add, hpart]
  have hsum_T_split : ∀ b : Bool,
      ∑ p ∈ A, ∑ q ∈ A, (if hp : p ∈ A then if hq : q ∈ A then
        wT (b, idx.symm ⟨p, hp⟩, idx.symm ⟨q, hq⟩) +
        wT (b, idx.symm ⟨q, hq⟩, idx.symm ⟨p, hp⟩) else 0 else 0) =
      2 * ∑ x ∈ T with x.1 = b, wT x := fun b => by
    have hrw : (∑ p ∈ A, ∑ q ∈ A, (if hp : p ∈ A then if hq : q ∈ A then
        wT (b, idx.symm ⟨p, hp⟩, idx.symm ⟨q, hq⟩) +
        wT (b, idx.symm ⟨q, hq⟩, idx.symm ⟨p, hp⟩) else 0 else 0)) =
        ∑ i : Fin N, ∑ j : Fin N, (wT (b, i, j) + wT (b, j, i)) := by
      rw [hsum_A_R]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsum_A_R]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [dif_pos (hpt_mem i), dif_pos (hpt_mem j)]
      have hi : idx.symm ⟨ptOf i, hpt_mem i⟩ = i := by dsimp [ptOf]; simp
      have hj : idx.symm ⟨ptOf j, hpt_mem j⟩ = j := by dsimp [ptOf]; simp
      rw [hi, hj]
    rw [hrw]
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i j => wT (b, j, i)), sum_bool_triple_scalar T wT hwT_out b, two_mul]
  have hω_tot : ∑ p ∈ A, ∑ q ∈ A, ω p q = 2 * ∑ x ∈ T with x.1 = true, wT x := hsum_T_split true
  have hlam_tot : ∑ p ∈ A, ∑ q ∈ A, lam p q = 2 * ∑ x ∈ T with x.1 = false, wT x := hsum_T_split false
  have hzero_dot : ∑ p ∈ A, inner ℝ p (∑ q ∈ A, ω p q • (p - q) - ∑ q ∈ A, lam p q • (p - q)) = 0 :=
    Finset.sum_eq_zero fun p hp => by rw [hbal p hp, inner_zero_right]
  have hdot_eq : ∑ p ∈ A, inner ℝ p (∑ q ∈ A, ω p q • (p - q)) =
      ∑ p ∈ A, inner ℝ p (∑ q ∈ A, lam p q • (p - q)) := by
    have h0' : ∑ p ∈ A, (inner ℝ p (∑ q ∈ A, ω p q • (p - q)) -
        inner ℝ p (∑ q ∈ A, lam p q • (p - q))) = 0 := by
      rw [← hzero_dot]
      exact Finset.sum_congr rfl fun p _ => (inner_sub_right _ _ _).symm
    rw [Finset.sum_sub_distrib] at h0'
    linarith
  have hvirial_sq : ∑ p ∈ A, ∑ q ∈ A, ω p q * ‖p - q‖ ^ 2 =
      ∑ p ∈ A, ∑ q ∈ A, lam p q * ‖p - q‖ ^ 2 := by
    rw [← virial_alg_identity A ω (fun p q => (hω_lam_symm p q).1),
      ← virial_alg_identity A lam (fun p q => (hω_lam_symm p q).2), hdot_eq]
  have hω_sq : ∑ p ∈ A, ∑ q ∈ A, ω p q * ‖p - q‖ ^ 2 = ∑ p ∈ A, ∑ q ∈ A, ω p q :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rcases eq_or_lt_of_le (hω_lam_nn p q).1 with h0 | hpos
      · rw [← h0, zero_mul]
      · rw [← dist_eq_norm, (hω_supp p q hpos).2.2]; ring
  have hlam_sq : ∑ p ∈ A, ∑ q ∈ A, lam p q * ‖p - q‖ ^ 2 = D ^ 2 * ∑ p ∈ A, ∑ q ∈ A, lam p q := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by
        rcases eq_or_lt_of_le (hω_lam_nn p q).2 with h0 | hpos
        · rw [← h0, zero_mul, mul_zero]
        · rw [← dist_eq_norm, (hlam_supp p q hpos).2.2]; ring
  have hvirial : ∑ p ∈ A, ∑ q ∈ A, ω p q = D ^ 2 * ∑ p ∈ A, ∑ q ∈ A, lam p q := by
    rw [← hω_sq, ← hlam_sq, hvirial_sq]
  have hsum_both : ∑ p ∈ A, ∑ q ∈ A, ω p q + ∑ p ∈ A, ∑ q ∈ A, lam p q = 2 := by
    rw [hω_tot, hlam_tot, ← mul_add]
    have hpart := Finset.sum_filter_add_sum_filter_not T (fun x => x.1 = true) wT
    have hnot_eq : T.filter (fun x => ¬ x.1 = true) = T.filter (fun x => x.1 = false) := by
      ext x; simp [Bool.not_eq_true]
    rw [hnot_eq, hwT_sum] at hpart; rw [hpart, mul_one]
  have hlam_pos : 0 < ∑ p ∈ A, ∑ q ∈ A, lam p q := by
    by_contra hle
    have h0 : ∑ p ∈ A, ∑ q ∈ A, lam p q = 0 := le_antisymm (not_lt.mp hle)
      (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => (hω_lam_nn p q).2)
    rw [h0, mul_zero] at hvirial; linarith
  have hω_pos : 0 < ∑ p ∈ A, ∑ q ∈ A, ω p q := by
    rw [hvirial]; exact mul_pos (sq_pos_of_pos hD_pos) hlam_pos
  exact ⟨ω, lam, hω_lam_nn, hω_lam_symm, hω_supp, hlam_supp, hbal, hω_pos, hlam_pos, hvirial⟩

/-- Theorem 3c (Interior Equilibrium Half-Plane Exclusion):
At any vertex `p ∈ A` with zero incident `E_D`-stress (`∀ q ∈ A, lam p q = 0`) and positive
incident `E_1`-stress (`0 < ∑ q ∈ A, ω p q`), its positively stressed unit neighbors cannot all
lie in the same open half-plane `{q | 0 < inner ℝ (q - p) u}`. -/
theorem ppl083_interior_equilibrium_not_halfplane {A : Finset (EuclideanSpace ℝ (Fin 2))}
    {ω lam : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ}
    (hnn : ∀ p q, 0 ≤ ω p q)
    (hbal : ∀ p ∈ A, ∑ q ∈ A, ω p q • (p - q) - ∑ q ∈ A, lam p q • (p - q) = 0)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ A)
    (hno_D : ∀ q ∈ A, lam p q = 0) (hpos_1 : 0 < ∑ q ∈ A, ω p q)
    (u : EuclideanSpace ℝ (Fin 2)) :
    ∃ q ∈ A, 0 < ω p q ∧ inner ℝ (q - p) u ≤ 0 := by
  by_contra hall
  push Not at hall
  have hbal_p : ∑ q ∈ A, ω p q • (p - q) = 0 := by
    have h := hbal p hp
    have hlam0 : ∑ q ∈ A, lam p q • (p - q) = 0 :=
      Finset.sum_eq_zero fun q hq => by rw [hno_D q hq, zero_smul]
    rw [hlam0, sub_zero] at h
    exact h
  have hdot : ∑ q ∈ A, ω p q * inner ℝ (p - q) u = 0 := by
    have h0 : inner ℝ (∑ q ∈ A, ω p q • (p - q)) u = 0 := by rw [hbal_p, inner_zero_left]
    rw [sum_inner] at h0
    simpa [real_inner_smul_left] using h0
  have hneg_sum : ∑ q ∈ A, ω p q * inner ℝ (p - q) u < 0 := by
    have hle : ∀ q ∈ A, ω p q * inner ℝ (p - q) u ≤ 0 := by
      intro q hq
      rcases eq_or_lt_of_le (hnn p q) with h0 | hpos
      · rw [← h0, zero_mul]
      · have hgt := hall q hq hpos
        have hlt : inner ℝ (p - q) u < 0 := by
          rw [show p - q = -(q - p) by abel, inner_neg_left]; linarith
        exact mul_nonpos_of_nonneg_of_nonpos hpos.le hlt.le
    obtain ⟨q₀, hq₀, hω₀⟩ : ∃ q ∈ A, 0 < ω p q := by
      by_contra hnone; push Not at hnone
      have hsum0 : ∑ q ∈ A, ω p q ≤ 0 := Finset.sum_nonpos fun q hq => hnone q hq
      linarith
    have hstrict : ω p q₀ * inner ℝ (p - q₀) u < 0 := by
      have hgt := hall q₀ hq₀ hω₀
      have hlt : inner ℝ (p - q₀) u < 0 := by
        rw [show p - q₀ = -(q₀ - p) by abel, inner_neg_left]; linarith
      exact mul_neg_of_pos_of_neg hω₀ hlt
    simpa using Finset.sum_lt_sum hle ⟨q₀, hq₀, hstrict⟩
  linarith

/-- Theorem 3d (Second-Order Interior Expansion Identity):
For any pair `(p, q)` with `dist p q = 1`, any perturbation `(v_p, v_q)` with `v_p ≠ v_q` and
nonnegative first-order slack `0 ≤ inner ℝ (p - q) (v_p - v_q)` strictly increases separation
`1 < dist (p + t • v_p) (q + t • v_q)` for every `t > 0`. -/
theorem ppl083_second_order_expansion {p q v_p v_q : EuclideanSpace ℝ (Fin 2)}
    (hpq : dist p q = 1) (hv : v_p ≠ v_q) (hslack : 0 ≤ inner ℝ (p - q) (v_p - v_q))
    {t : ℝ} (ht : 0 < t) :
    1 < dist (p + t • v_p) (q + t • v_q) := by
  have hdiff : (p + t • v_p) - (q + t • v_q) = (p - q) + t • (v_p - v_q) := by module
  have hv_pos : 0 < ‖v_p - v_q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv))
  have hsq : 1 < ‖(p + t • v_p) - (q + t • v_q)‖ ^ 2 := by
    rw [hdiff, norm_add_sq_real, norm_smul, Real.norm_of_nonneg ht.le,
      real_inner_smul_right, ← dist_eq_norm, hpq]
    have h2t : 0 ≤ 2 * (t * inner ℝ (p - q) (v_p - v_q)) := by positivity
    have ht2 : 0 < (t * ‖v_p - v_q‖) ^ 2 := by
      rw [mul_pow]; exact mul_pos (sq_pos_of_pos ht) hv_pos
    linarith
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((p + t • v_p) - (q + t • v_q))]

end KKTAndVirial

section SmallNWitnesses

private noncomputable def pt2 (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![x, y]

private lemma pt2_eq_iff (x₁ y₁ x₂ y₂ : ℝ) :
    pt2 x₁ y₁ = pt2 x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    have h0 := congrFun (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp) h) 0
    have h1 := congrFun (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp) h) 1
    simpa [pt2, ofLp_equiv_symm] using And.intro h0 h1
  · rintro ⟨rfl, rfl⟩; rfl

private lemma dist_pt2_sq (x₁ y₁ x₂ y₂ : ℝ) :
    dist (pt2 x₁ y₁) (pt2 x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, pt2, ofLp_equiv_symm, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]

private noncomputable def circlePt (R α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  pt2 (R * Real.cos α) (R * Real.sin α)

private lemma dist_circlePt {R : ℝ} (hR : 0 ≤ R) (α β : ℝ) :
    dist (circlePt R α) (circlePt R β) = 2 * R * |Real.sin ((α - β) / 2)| := by
  have hsq : dist (circlePt R α) (circlePt R β) ^ 2 =
      (2 * R * |Real.sin ((α - β) / 2)|) ^ 2 := by
    dsimp [circlePt]
    rw [dist_pt2_sq]
    have htrig : (R * Real.cos α - R * Real.cos β) ^ 2 + (R * Real.sin α - R * Real.sin β) ^ 2 =
        R ^ 2 * (2 - 2 * Real.cos (α - β)) := by
      have h1 := Real.cos_sq_add_sin_sq α
      have h2 := Real.cos_sq_add_sin_sq β
      rw [Real.cos_sub]
      nlinarith
    have hhalf : 2 - 2 * Real.cos (α - β) = 4 * Real.sin ((α - β) / 2) ^ 2 := by
      have hc := Real.cos_two_mul ((α - β) / 2)
      rw [show 2 * ((α - β) / 2) = α - β by ring, Real.cos_sq'] at hc
      linarith
    rw [htrig, hhalf, mul_pow, mul_pow, sq_abs]
    ring
  have h1 : 0 ≤ dist (circlePt R α) (circlePt R β) := dist_nonneg
  have h2 : 0 ≤ 2 * R * |Real.sin ((α - β) / 2)| := by positivity
  nlinarith

private lemma dist_zero_circlePt {R : ℝ} (hR : 0 ≤ R) (α : ℝ) :
    dist (0 : EuclideanSpace ℝ (Fin 2)) (circlePt R α) = R := by
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) = pt2 0 0 := by
    ext c; fin_cases c <;> simp [pt2]
  have hsq : dist (0 : EuclideanSpace ℝ (Fin 2)) (circlePt R α) ^ 2 = R ^ 2 := by
    rw [hzero]; dsimp [circlePt]; rw [dist_pt2_sq]
    have hcs := Real.cos_sq_add_sin_sq α
    nlinarith
  have h1 : 0 ≤ dist (0 : EuclideanSpace ℝ (Fin 2)) (circlePt R α) := dist_nonneg
  nlinarith

private def cycDist (m a b : ℕ) : ℕ :=
  let raw := if a ≤ b then b - a else a - b
  min raw (m - raw)

private lemma regPolygon_chord_of_fin {m : ℕ} (hm : 3 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    (j k : Fin m) :
    2 * cycDist m j.1 k.1 ≤ m ∧ (j ≠ k → 1 ≤ cycDist m j.1 k.1) ∧
      dist (circlePt R (2 * (j : ℝ) * Real.pi / m)) (circlePt R (2 * (k : ℝ) * Real.pi / m)) =
        2 * R * Real.sin ((cycDist m j.1 k.1 : ℝ) * Real.pi / m) := by
  set raw := if j.1 ≤ k.1 then k.1 - j.1 else j.1 - k.1
  have hraw_lt : raw < m := by
    dsimp [raw]; split_ifs <;> omega
  have hraw_diff : |(j : ℝ) - (k : ℝ)| = (raw : ℝ) := by
    dsimp [raw]
    split_ifs with hjk
    · have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      rw [abs_of_nonpos (sub_nonpos.mpr this), Nat.cast_sub hjk]; ring
    · have hkj : k.1 ≤ j.1 := by omega
      have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
      rw [abs_of_nonneg (sub_nonneg.mpr this), Nat.cast_sub hkj]
  have hsin_abs : |Real.sin (((2 * (j : ℝ) * Real.pi / m) - (2 * (k : ℝ) * Real.pi / m)) / 2)| =
      Real.sin ((raw : ℝ) * Real.pi / m) := by
    have harg : ((2 * (j : ℝ) * Real.pi / m) - (2 * (k : ℝ) * Real.pi / m)) / 2 =
        ((j : ℝ) - (k : ℝ)) * Real.pi / m := by ring
    rw [harg]
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hsin_sign : |Real.sin (((j : ℝ) - (k : ℝ)) * Real.pi / m)| =
        Real.sin (|(j : ℝ) - (k : ℝ)| * Real.pi / m) := by
      rcases le_total (j : ℝ) (k : ℝ) with hjk | hkj
      · rw [abs_of_nonpos (sub_nonpos.mpr hjk)]
        have hneg : ((j : ℝ) - (k : ℝ)) * Real.pi / m = -((-((j : ℝ) - (k : ℝ))) * Real.pi / m) := by ring
        rw [hneg, Real.sin_neg, abs_neg]
        have hnonneg : 0 ≤ -((j : ℝ) - (k : ℝ)) * Real.pi / m := by
          have : 0 ≤ -((j : ℝ) - (k : ℝ)) := by linarith
          positivity
        have hle_pi : -((j : ℝ) - (k : ℝ)) * Real.pi / m ≤ Real.pi := by
          have hraw' : -((j : ℝ) - (k : ℝ)) = (raw : ℝ) := by
            dsimp [raw]; rw [if_pos (Nat.cast_le.mp hjk), Nat.cast_sub (Nat.cast_le.mp hjk)]; ring
          rw [hraw']
          have hrm : (raw : ℝ) ≤ m := by exact_mod_cast hraw_lt.le
          rw [div_le_iff₀ hm_pos]; nlinarith [Real.pi_pos]
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hnonneg hle_pi)
      · rw [abs_of_nonneg (sub_nonneg.mpr hkj)]
        have hnonneg : 0 ≤ ((j : ℝ) - (k : ℝ)) * Real.pi / m := by
          have : 0 ≤ (j : ℝ) - (k : ℝ) := by linarith
          positivity
        have hle_pi : ((j : ℝ) - (k : ℝ)) * Real.pi / m ≤ Real.pi := by
          have hraw' : (j : ℝ) - (k : ℝ) = (raw : ℝ) := by
            rw [← hraw_diff, abs_of_nonneg (sub_nonneg.mpr hkj)]
          rw [hraw']
          have hrm : (raw : ℝ) ≤ m := by exact_mod_cast hraw_lt.le
          rw [div_le_iff₀ hm_pos]; nlinarith [Real.pi_pos]
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hnonneg hle_pi)
    rw [hsin_sign, hraw_diff]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [cycDist]; omega
  · intro hne
    have hval : j.1 ≠ k.1 := fun h => hne (Fin.ext h)
    dsimp [cycDist]; split_ifs <;> omega
  · dsimp [cycDist]
    rcases le_or_gt raw (m - raw) with hle | hgt
    · rw [min_eq_left hle, dist_circlePt hR, hsin_abs]
    · rw [min_eq_right hgt.le, dist_circlePt hR, hsin_abs]
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hpi_sub : (m - raw : ℕ) * Real.pi / m = Real.pi - (raw : ℝ) * Real.pi / m := by
        rw [Nat.cast_sub hraw_lt.le]; field_simp
      rw [hpi_sub, Real.sin_pi_sub]

private lemma cycDist_no_triangle {m : ℕ} (hm : 4 ≤ m) (j k l : Fin m)
    (h1 : cycDist m j.1 k.1 = 1) (h2 : cycDist m k.1 l.1 = 1) (h3 : cycDist m j.1 l.1 = 1) :
    False := by
  have : NeZero m := ⟨by omega⟩
  have hmod : ∀ a b : Fin m, cycDist m a.1 b.1 = 1 →
      (a.1 : ZMod m) - (b.1 : ZMod m) = 1 ∨ (a.1 : ZMod m) - (b.1 : ZMod m) = -1 := by
    intro a b h
    have ha := a.2
    have hb := b.2
    have hraw : (a.1 : ℤ) - b.1 = 1 ∨ (a.1 : ℤ) - b.1 = -1 ∨
        (a.1 : ℤ) - b.1 = (m : ℤ) - 1 ∨ (a.1 : ℤ) - b.1 = 1 - (m : ℤ) := by
      dsimp [cycDist] at h
      split_ifs at h with hab
      · rcases min_cases (b.1 - a.1) (m - (b.1 - a.1)) with ⟨hmin, _⟩ | ⟨hmin, _⟩
        · rw [hmin] at h; right; left; omega
        · rw [hmin] at h; right; right; right; omega
      · rcases min_cases (a.1 - b.1) (m - (a.1 - b.1)) with ⟨hmin, _⟩ | ⟨hmin, _⟩
        · rw [hmin] at h; left; omega
        · rw [hmin] at h; right; right; left; omega
    have hc : (a.1 : ZMod m) - (b.1 : ZMod m) = (((a.1 : ℤ) - b.1 : ℤ) : ZMod m) := by
      push_cast; ring
    rw [hc]
    rcases hraw with heq | heq | heq | heq <;> rw [heq]
    · left; push_cast; rfl
    · right; push_cast; rfl
    · right; push_cast; simp
    · left; push_cast; simp
  have m1 := hmod j k h1
  have m2 := hmod k l h2
  have m3 := hmod j l h3
  have hsum : ((j.1 : ZMod m) - (k.1 : ZMod m)) + ((k.1 : ZMod m) - (l.1 : ZMod m)) =
      (j.1 : ZMod m) - (l.1 : ZMod m) := by ring
  have hz1 : (1 : ZMod m) ≠ 0 := by
    intro h
    have hv : ((1 : ℕ) : ZMod m).val = (0 : ZMod m).val := congrArg ZMod.val (by simpa using h)
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hz3 : (3 : ZMod m) ≠ 0 := by
    intro h
    have hv : ((3 : ℕ) : ZMod m).val = (0 : ZMod m).val := congrArg ZMod.val (by simpa using h)
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2 <;> rcases m3 with e3 | e3 <;>
    rw [e1, e2, e3] at hsum <;>
    (first
      | exact hz1 (by linear_combination hsum)
      | exact hz1 (by linear_combination -hsum)
      | exact hz3 (by linear_combination hsum)
      | exact hz3 (by linear_combination -hsum))

/-- Theorem 4a (`n = 4` Unit Square Witness):
`A = {(0,0), (1,0), (0,1), (1,1)}` has cardinality `4`, minimum distance `1`, diameter `√2`, and
no unit equilateral triangle. -/
theorem ppl083_n4_square_witness :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 4 ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) ∧
      (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) = Real.sqrt 2 ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ¬ (dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1)) := by
  let p00 := pt2 0 0
  let p10 := pt2 1 0
  let p01 := pt2 0 1
  let p11 := pt2 1 1
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := {p00, p10, p01, p11}
  have hne01 : p00 ≠ p10 := by intro h; rw [pt2_eq_iff] at h; norm_num at h
  have hne02 : p00 ≠ p01 := by intro h; rw [pt2_eq_iff] at h; norm_num at h
  have hne03 : p00 ≠ p11 := by intro h; rw [pt2_eq_iff] at h; norm_num at h
  have hne12 : p10 ≠ p01 := by intro h; rw [pt2_eq_iff] at h; norm_num at h
  have hne13 : p10 ≠ p11 := by intro h; rw [pt2_eq_iff] at h; norm_num at h
  have hne23 : p01 ≠ p11 := by intro h; rw [pt2_eq_iff] at h; norm_num at h
  have hd01 : dist p00 p10 = 1 := by
    have := dist_pt2_sq 0 0 1 0; have hn : 0 ≤ dist p00 p10 := dist_nonneg
    dsimp [p00, p10] at *; nlinarith
  have hd02 : dist p00 p01 = 1 := by
    have := dist_pt2_sq 0 0 0 1; have hn : 0 ≤ dist p00 p01 := dist_nonneg
    dsimp [p00, p01] at *; nlinarith
  have hd13 : dist p10 p11 = 1 := by
    have := dist_pt2_sq 1 0 1 1; have hn : 0 ≤ dist p10 p11 := dist_nonneg
    dsimp [p10, p11] at *; nlinarith
  have hd23 : dist p01 p11 = 1 := by
    have := dist_pt2_sq 0 1 1 1; have hn : 0 ≤ dist p01 p11 := dist_nonneg
    dsimp [p01, p11] at *; nlinarith
  have hd03 : dist p00 p11 = Real.sqrt 2 := by
    have hsq := dist_pt2_sq 0 0 1 1
    rw [← Real.sqrt_sq dist_nonneg]; dsimp [p00, p11] at *; rw [hsq]; norm_num
  have hd12 : dist p10 p01 = Real.sqrt 2 := by
    have hsq := dist_pt2_sq 1 0 0 1
    rw [← Real.sqrt_sq dist_nonneg]; dsimp [p10, p01] at *; rw [hsq]; norm_num
  have hsqrt2_gt1 : 1 < Real.sqrt 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have hcard : A.card = 4 := by
    dsimp [A]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp [hne01, hne02, hne03, hne12, hne13, hne23]
  refine ⟨A, hcard, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hne
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      (try exact absurd rfl hne
       try rw [hd01]
       try rw [hd02]
       try rw [hd13]
       try rw [hd23]
       try rw [dist_comm, hd01]
       try rw [dist_comm, hd02]
       try rw [dist_comm, hd13]
       try rw [dist_comm, hd23]
       try (rw [hd03]; exact hsqrt2_gt1.le)
       try (rw [dist_comm, hd03]; exact hsqrt2_gt1.le)
       try (rw [hd12]; exact hsqrt2_gt1.le)
       try (rw [dist_comm, hd12]; exact hsqrt2_gt1.le))
  · exact ⟨p00, by simp [A], p10, by simp [A], hd01⟩
  · have hle : Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ≤ Real.sqrt 2 := by
      refine Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg 2) fun p hp q hq => ?_
      simp only [Finset.mem_coe, A, Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        (try (rw [dist_self]; exact Real.sqrt_nonneg 2)
         try rw [hd03]
         try rw [dist_comm, hd03]
         try rw [hd12]
         try rw [dist_comm, hd12]
         try (rw [hd01]; exact hsqrt2_gt1.le)
         try (rw [dist_comm, hd01]; exact hsqrt2_gt1.le)
         try (rw [hd02]; exact hsqrt2_gt1.le)
         try (rw [dist_comm, hd02]; exact hsqrt2_gt1.le)
         try (rw [hd13]; exact hsqrt2_gt1.le)
         try (rw [dist_comm, hd13]; exact hsqrt2_gt1.le)
         try (rw [hd23]; exact hsqrt2_gt1.le)
         try (rw [dist_comm, hd23]; exact hsqrt2_gt1.le))
    have hge : Real.sqrt 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← hd03]
      exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded (by simp [A]) (by simp [A])
    exact le_antisymm hle hge
  · intro p hp q hq r hr ⟨h1, h2, h3⟩
    let par : EuclideanSpace ℝ (Fin 2) → Fin 2 := fun x =>
      if x.ofLp 0 = x.ofLp 1 then 0 else 1
    have hpar_neq : ∀ a ∈ A, ∀ b ∈ A, dist a b = 1 → par a ≠ par b := by
      intro a ha b hb hdist hpeq
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha hb
      have h00 : par p00 = 0 := by simp [par, p00, pt2]
      have h11 : par p11 = 0 := by simp [par, p11, pt2]
      have h10 : par p10 = 1 := by simp [par, p10, pt2]
      have h01 : par p01 = 1 := by simp [par, p01, pt2]
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        (try (rw [dist_self] at hdist; norm_num at hdist)
         try (simp only [h00, h10, h01, h11] at hpeq; contradiction)
         try (rw [hd03] at hdist; exact absurd hdist hsqrt2_gt1.ne')
         try (rw [dist_comm, hd03] at hdist; exact absurd hdist hsqrt2_gt1.ne')
         try (rw [hd12] at hdist; exact absurd hdist hsqrt2_gt1.ne')
         try (rw [dist_comm, hd12] at hdist; exact absurd hdist hsqrt2_gt1.ne'))
    have hne1 : (par p).1 ≠ (par q).1 := fun h => hpar_neq p hp q hq h1 (Fin.ext h)
    have hne2 : (par q).1 ≠ (par r).1 := fun h => hpar_neq q hq r hr h2 (Fin.ext h)
    have hne3 : (par p).1 ≠ (par r).1 := fun h => hpar_neq p hp r hr h3 (Fin.ext h)
    have hp1 := (par p).2; have hp2 := (par q).2; have hp3 := (par r).2
    omega

/-- Theorem 4b (`n = 5` Regular Pentagon Witness):
The regular pentagon of side `1` has cardinality `5`, minimum distance `1`, and `0` unit
equilateral triangles (`G₁ = C₅`). -/
theorem ppl083_n5_pentagon_witness :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 5 ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) ∧
      (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ¬ (dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1)) := by
  have hsin_pos : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  set R := 1 / (2 * Real.sin (Real.pi / 5))
  have hR_pos : 0 < R := by positivity
  let f : Fin 5 → EuclideanSpace ℝ (Fin 2) := fun k => circlePt R (2 * (k : ℝ) * Real.pi / 5)
  have hlt_pi2 : 2 * Real.pi / 5 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsin12 : Real.sin (Real.pi / 5) < Real.sin (2 * Real.pi / 5) :=
    Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], hlt_pi2.le⟩ (by linarith [Real.pi_pos])
  have h12 : 1 < 2 * R * Real.sin (2 * Real.pi / 5) := by
    calc (1 : ℝ) = Real.sin (Real.pi / 5) / Real.sin (Real.pi / 5) := (div_self hsin_pos.ne').symm
      _ < Real.sin (2 * Real.pi / 5) / Real.sin (Real.pi / 5) := div_lt_div_of_pos_right hsin12 hsin_pos
      _ = 2 * R * Real.sin (2 * Real.pi / 5) := by dsimp [R]; field_simp
  have hf_dist : ∀ j k : Fin 5, j ≠ k →
      (dist (f j) (f k) = 1 ↔ cycDist 5 j.1 k.1 = 1) ∧ 1 ≤ dist (f j) (f k) := by
    intro j k hne
    obtain ⟨hd2, hd1, hdist⟩ := regPolygon_chord_of_fin (m := 5) (by omega) hR_pos.le j k
    push_cast at hdist
    have hd_pos : 1 ≤ cycDist 5 j.1 k.1 := hd1 hne
    have hd_cases : cycDist 5 j.1 k.1 = 1 ∨ cycDist 5 j.1 k.1 = 2 := by omega
    rcases hd_cases with hd | hd
    · have h1 : dist (f j) (f k) = 1 := by
        dsimp [f]; rw [hdist, hd]; dsimp [R]; push_cast; rw [one_mul]; field_simp
      exact ⟨⟨fun _ => hd, fun _ => h1⟩, h1.ge⟩
    · have hgt : 1 < dist (f j) (f k) := by
        dsimp [f]; rw [hdist, hd]; push_cast; exact h12
      exact ⟨⟨fun h => absurd h hgt.ne', fun h => absurd (h ▸ hd) (by omega)⟩, hgt.le⟩
  have hf_inj : Function.Injective f := by
    intro j k heq
    by_contra hne
    have h1 := (hf_dist j k hne).2
    rw [heq, dist_self] at h1
    linarith
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.image f
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf_inj, Finset.card_fin]
  · intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨j, _, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨k, _, rfl⟩
    exact (hf_dist j k fun h => hne (congrArg f h)).2
  · refine ⟨f 0, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      f 1, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    exact (hf_dist 0 1 (by decide)).1.mpr (by decide)
  · intro p hp q hq r hr ⟨h12', h23', h13'⟩
    rcases Finset.mem_image.mp hp with ⟨j, _, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨k, _, rfl⟩
    rcases Finset.mem_image.mp hr with ⟨l, _, rfl⟩
    have hjk : j ≠ k := fun h => by rw [h, dist_self] at h12'; norm_num at h12'
    have hkl : k ≠ l := fun h => by rw [h, dist_self] at h23'; norm_num at h23'
    have hjl : j ≠ l := fun h => by rw [h, dist_self] at h13'; norm_num at h13'
    have hc1 := (hf_dist j k hjk).1.mp h12'
    have hc2 := (hf_dist k l hkl).1.mp h23'
    have hc3 := (hf_dist j l hjl).1.mp h13'
    exact cycDist_no_triangle (by omega) j k l hc1 hc2 hc3

/-- Theorem 4c (`n = 6` Regular Pentagon + Center Witness):
Regular pentagon of circumradius `1` plus its center `(0, 0)` has cardinality `6`, minimum
distance `1`, and `0` unit equilateral triangles (`G₁ = K_{1,5}`). -/
theorem ppl083_n6_pentagon_center_witness :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 6 ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) ∧
      (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ¬ (dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1)) := by
  let f : Fin 5 → EuclideanSpace ℝ (Fin 2) := fun k => circlePt 1 (2 * (k : ℝ) * Real.pi / 5)
  have hpi6_lt : Real.pi / 6 < Real.pi / 5 := by linarith [Real.pi_pos]
  have hsin_gt : 1 / 2 < Real.sin (Real.pi / 5) := by
    rw [← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hpi6_lt
  have hsin12 : Real.sin (Real.pi / 5) < Real.sin (2 * Real.pi / 5) :=
    Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
  have hf_dist_gt : ∀ j k : Fin 5, j ≠ k → 1 < dist (f j) (f k) := by
    intro j k hne
    obtain ⟨hd2, hd1, hdist⟩ := regPolygon_chord_of_fin (m := 5) (by omega) zero_le_one j k
    push_cast at hdist
    have hd_pos : 1 ≤ cycDist 5 j.1 k.1 := hd1 hne
    have hsin_le : Real.sin (Real.pi / 5) ≤ Real.sin ((cycDist 5 j.1 k.1 : ℝ) * Real.pi / 5) := by
      rcases (by omega : cycDist 5 j.1 k.1 = 1 ∨ cycDist 5 j.1 k.1 = 2) with h | h
      · rw [h]; norm_num
      · rw [h]; push_cast; exact hsin12.le
    dsimp [f]; rw [hdist]; linarith
  have hf_inj : Function.Injective f := by
    intro j k heq; by_contra hne
    have h1 := hf_dist_gt j k hne; rw [heq, dist_self] at h1; linarith
  have h0_dist : ∀ j : Fin 5, dist (0 : EuclideanSpace ℝ (Fin 2)) (f j) = 1 := fun j =>
    dist_zero_circlePt zero_le_one _
  have h0_not : (0 : EuclideanSpace ℝ (Fin 2)) ∉ Finset.univ.image f := by
    intro hmem; rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    have := h0_dist j; rw [hj, dist_self] at this; norm_num at this
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := insert 0 (Finset.univ.image f)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem h0_not, Finset.card_image_of_injective _ hf_inj, Finset.card_fin]
  · intro p hp q hq hne
    simp only [A, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    rcases hp with rfl | ⟨j, rfl⟩ <;> rcases hq with rfl | ⟨k, rfl⟩
    · exact absurd rfl hne
    · rw [h0_dist k]
    · rw [dist_comm, h0_dist j]
    · exact (hf_dist_gt j k fun h => hne (congrArg f h)).le
  · exact ⟨0, by simp [A], f 0, by simp [A], h0_dist 0⟩
  · intro p hp q hq r hr ⟨h12, h23, h13⟩
    simp only [A, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp hq hr
    rcases hp with rfl | ⟨j, rfl⟩ <;> rcases hq with rfl | ⟨k, rfl⟩ <;> rcases hr with rfl | ⟨l, rfl⟩ <;>
      first
        | (rw [dist_self] at h12; norm_num at h12)
        | (rw [dist_self] at h23; norm_num at h23)
        | (rw [dist_self] at h13; norm_num at h13)
        | (have hne : j ≠ k := fun h => by rw [h, dist_self] at h12; norm_num at h12
           linarith [hf_dist_gt j k hne])
        | (have hne : k ≠ l := fun h => by rw [h, dist_self] at h23; norm_num at h23
           linarith [hf_dist_gt k l hne])
        | (have hne : j ≠ l := fun h => by rw [h, dist_self] at h13; norm_num at h13
           linarith [hf_dist_gt j l hne])

/-- Theorem 4d (`n = 8` Regular Heptagon + Center Witness, Bezdek–Fodor Combinatorics):
The regular heptagon of side `1` together with its center `(0, 0)` has cardinality `8`, minimum
distance `1`, and `0` unit equilateral triangles (`G₁ = C₇ ⊔ {0}`). -/
theorem ppl083_n8_heptagon_center_witness :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 8 ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) ∧
      (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ¬ (dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1)) := by
  have hsin_pos : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin_lt_half : Real.sin (Real.pi / 7) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
  set R := 1 / (2 * Real.sin (Real.pi / 7))
  have hR_gt1 : 1 < R := by dsimp [R]; rw [one_lt_div (by positivity)]; linarith
  have hR_pos : 0 < R := by linarith
  let f : Fin 7 → EuclideanSpace ℝ (Fin 2) := fun k => circlePt R (2 * (k : ℝ) * Real.pi / 7)
  have hsin12 : Real.sin (Real.pi / 7) < Real.sin (2 * Real.pi / 7) :=
    Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
  have hsin13 : Real.sin (Real.pi / 7) < Real.sin (3 * Real.pi / 7) :=
    Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
  have hf_dist : ∀ j k : Fin 7, j ≠ k →
      (dist (f j) (f k) = 1 ↔ cycDist 7 j.1 k.1 = 1) ∧ 1 ≤ dist (f j) (f k) := by
    intro j k hne
    obtain ⟨hd2, hd1, hdist⟩ := regPolygon_chord_of_fin (m := 7) (by omega) hR_pos.le j k
    push_cast at hdist
    have hd_pos : 1 ≤ cycDist 7 j.1 k.1 := hd1 hne
    have hd_cases : cycDist 7 j.1 k.1 = 1 ∨ cycDist 7 j.1 k.1 = 2 ∨ cycDist 7 j.1 k.1 = 3 := by omega
    rcases hd_cases with hd | hd | hd
    · have h1 : dist (f j) (f k) = 1 := by
        dsimp [f]; rw [hdist, hd]; dsimp [R]; push_cast; rw [one_mul]; field_simp
      exact ⟨⟨fun _ => hd, fun _ => h1⟩, h1.ge⟩
    · have hgt : 1 < dist (f j) (f k) := by
        dsimp [f]; rw [hdist, hd]; push_cast
        calc (1 : ℝ) = Real.sin (Real.pi / 7) / Real.sin (Real.pi / 7) := (div_self hsin_pos.ne').symm
          _ < Real.sin (2 * Real.pi / 7) / Real.sin (Real.pi / 7) := div_lt_div_of_pos_right hsin12 hsin_pos
          _ = 2 * R * Real.sin (2 * Real.pi / 7) := by dsimp [R]; field_simp
      exact ⟨⟨fun h => absurd h hgt.ne', fun h => absurd (h ▸ hd) (by omega)⟩, hgt.le⟩
    · have hgt : 1 < dist (f j) (f k) := by
        dsimp [f]; rw [hdist, hd]; push_cast
        calc (1 : ℝ) = Real.sin (Real.pi / 7) / Real.sin (Real.pi / 7) := (div_self hsin_pos.ne').symm
          _ < Real.sin (3 * Real.pi / 7) / Real.sin (Real.pi / 7) := div_lt_div_of_pos_right hsin13 hsin_pos
          _ = 2 * R * Real.sin (3 * Real.pi / 7) := by dsimp [R]; field_simp
      exact ⟨⟨fun h => absurd h hgt.ne', fun h => absurd (h ▸ hd) (by omega)⟩, hgt.le⟩
  have hf_inj : Function.Injective f := by
    intro j k heq; by_contra hne
    have h1 := (hf_dist j k hne).2; rw [heq, dist_self] at h1; linarith
  have h0_dist : ∀ j : Fin 7, 1 < dist (0 : EuclideanSpace ℝ (Fin 2)) (f j) := fun j => by
    rw [dist_zero_circlePt hR_pos.le]; exact hR_gt1
  have h0_not : (0 : EuclideanSpace ℝ (Fin 2)) ∉ Finset.univ.image f := by
    intro hmem; rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    have := h0_dist j; rw [hj, dist_self] at this; linarith
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := insert 0 (Finset.univ.image f)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem h0_not, Finset.card_image_of_injective _ hf_inj, Finset.card_fin]
  · intro p hp q hq hne
    simp only [A, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    rcases hp with rfl | ⟨j, rfl⟩ <;> rcases hq with rfl | ⟨k, rfl⟩
    · exact absurd rfl hne
    · exact (h0_dist k).le
    · rw [dist_comm]; exact (h0_dist j).le
    · exact (hf_dist j k fun h => hne (congrArg f h)).2
  · refine ⟨f 0, by simp [A], f 1, by simp [A], (hf_dist 0 1 (by decide)).1.mpr (by decide)⟩
  · intro p hp q hq r hr ⟨h12, h23, h13⟩
    have h0_neq1 : ∀ x ∈ A, dist (0 : EuclideanSpace ℝ (Fin 2)) x ≠ 1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · simp
      · rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact (h0_dist i).ne'
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact absurd h12 (h0_neq1 q hq)
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · rw [dist_comm] at h12; exact absurd h12 (h0_neq1 p hp)
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · rw [dist_comm] at h13; exact absurd h13 (h0_neq1 p hp)
    rcases Finset.mem_image.mp hp' with ⟨j, _, rfl⟩
    rcases Finset.mem_image.mp hq' with ⟨k, _, rfl⟩
    rcases Finset.mem_image.mp hr' with ⟨l, _, rfl⟩
    have hjk : j ≠ k := fun h => by rw [h, dist_self] at h12; norm_num at h12
    have hkl : k ≠ l := fun h => by rw [h, dist_self] at h23; norm_num at h23
    have hjl : j ≠ l := fun h => by rw [h, dist_self] at h13; norm_num at h13
    have hc1 := (hf_dist j k hjk).1.mp h12
    have hc2 := (hf_dist k l hkl).1.mp h23
    have hc3 := (hf_dist j l hjl).1.mp h13
    exact cycDist_no_triangle (by omega) j k l hc1 hc2 hc3

end SmallNWitnesses

section ShearedLatticeBarrier

private noncomputable def shearV1 : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 0]

private noncomputable def shearV2 (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![Real.cos θ, Real.sin θ]

private lemma norm_shearV1 : ‖shearV1‖ = 1 := by
  have hsq : ‖shearV1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [shearV1]
  have hn : 0 ≤ ‖shearV1‖ := norm_nonneg _
  nlinarith

private lemma norm_shearV2 (θ : ℝ) : ‖shearV2 θ‖ = 1 := by
  have hsq : ‖shearV2 θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [shearV2, Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]
  have hn : 0 ≤ ‖shearV2 θ‖ := norm_nonneg _
  nlinarith

private lemma inner_shearV1_V2 (θ : ℝ) : inner ℝ shearV1 (shearV2 θ) = Real.cos θ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [shearV1, shearV2]

private lemma norm_sq_shear_lincomb (θ a b : ℝ) :
    ‖a • shearV1 + b • shearV2 θ‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos θ := by
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    norm_shearV1, norm_shearV2, real_inner_smul_left, real_inner_smul_right, inner_shearV1_V2,
    mul_one, mul_one, sq_abs, sq_abs]
  ring

private lemma int_hex_norm_ge_one {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    1 ≤ x ^ 2 + y ^ 2 - |x| * |y| := by
  have h : 0 ≤ (|x| - |y|) ^ 2 := sq_nonneg _
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hab : 2 * (x ^ 2 + y ^ 2 - |x| * |y|) = (|x| - |y|) ^ 2 + |x| ^ 2 + |y| ^ 2 := by
    rw [hx2, hy2]; ring
  rcases hxy with hx | hy
  · have h1 : 1 ≤ |x| ^ 2 := by nlinarith [abs_pos.mpr hx]
    linarith [sq_nonneg |x|, sq_nonneg |y|]
  · have h1 : 1 ≤ |y| ^ 2 := by nlinarith [abs_pos.mpr hy]
    linarith [sq_nonneg |x|, sq_nonneg |y|]

/-- Theorem 5a (Sheared-Lattice `Λ_ε` `K_3`-Free Contact Graph & Exact Edge Count):
For any shear angle `ε ∈ (0, π/6)` and grid size `L ≥ 2`, the `L × L` sheared-rhombus patch
`Λ_ε(L) = {i • v₁ + j • v₂(π/3 + ε)}` has cardinality `L^2`, minimum distance `1`, **0** unit
equilateral triangles (`G₁` is a 4-neighbor square grid), and exact ordered unit-pair count
`4 * L * (L - 1)` (`2 * L * (L - 1)` undirected edges). -/
theorem ppl083_sheared_lattice_k3_free {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < Real.pi / 6)
    {L : ℕ} (hL : 2 ≤ L) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = L ^ 2 ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) ∧
      (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ¬ (dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1)) ∧
      ((A ×ˢ A).filter (fun pq => dist pq.1 pq.2 = 1)).card = 4 * L * (L - 1) := by
  set θ := Real.pi / 3 + ε
  have hcos_pos : 0 < Real.cos θ := by
    rw [← Real.cos_pi_div_two]
    exact Real.strictAntiOn_cos ⟨by dsimp [θ]; linarith [Real.pi_pos], by dsimp [θ]; linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by dsimp [θ]; linarith)
  have hcos_lt : Real.cos θ < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by dsimp [θ]; linarith [Real.pi_pos], by dsimp [θ]; linarith [Real.pi_pos]⟩ (by dsimp [θ]; linarith)
  have hvec_sep : ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) →
      1 ≤ ‖(x : ℝ) • shearV1 + (y : ℝ) • shearV2 θ‖ ∧
      (‖(x : ℝ) • shearV1 + (y : ℝ) • shearV2 θ‖ = 1 ↔
        (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)) := by
    intro x y hxy
    have hsq := norm_sq_shear_lincomb θ (x : ℝ) (y : ℝ)
    by_cases hx0 : x = 0
    · subst hx0
      have hy0 : y ≠ 0 := hxy.resolve_left (fun h => h rfl)
      have hnorm : ‖((0 : ℤ) : ℝ) • shearV1 + (y : ℝ) • shearV2 θ‖ = |(y : ℝ)| := by
        rw [Int.cast_zero, zero_smul, zero_add, norm_smul, norm_shearV2, mul_one, Real.norm_eq_abs]
      rw [hnorm]
      have hy_abs : (1 : ℝ) ≤ |(y : ℝ)| := by
        exact_mod_cast (Int.one_le_abs hy0)
      refine ⟨hy_abs, ?_⟩
      constructor
      · intro heq
        have hy_int : |y| = 1 := by exact_mod_cast heq
        rcases abs_eq (by omega : (0 : ℤ) ≤ 1) |>.mp hy_int with rfl | rfl <;> simp
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> norm_num at *
    · by_cases hy0 : y = 0
      · subst hy0
        have hnorm : ‖(x : ℝ) • shearV1 + ((0 : ℤ) : ℝ) • shearV2 θ‖ = |(x : ℝ)| := by
          rw [Int.cast_zero, zero_smul, add_zero, norm_smul, norm_shearV1, mul_one, Real.norm_eq_abs]
        rw [hnorm]
        have hx_abs : (1 : ℝ) ≤ |(x : ℝ)| := by exact_mod_cast (Int.one_le_abs hx0)
        refine ⟨hx_abs, ?_⟩
        constructor
        · intro heq
          have hx_int : |x| = 1 := by exact_mod_cast heq
          rcases abs_eq (by omega : (0 : ℤ) ≤ 1) |>.mp hx_int with rfl | rfl <;> simp
        · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> norm_num at *
      · have hstrict : 1 < ‖(x : ℝ) • shearV1 + (y : ℝ) • shearV2 θ‖ ^ 2 := by
          rw [hsq]
          have hhex : (1 : ℤ) ≤ x ^ 2 + y ^ 2 - |x| * |y| := int_hex_norm_ge_one hxy
          have hhexR : (1 : ℝ) ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 - |(x : ℝ)| * |(y : ℝ)| := by
            exact_mod_cast hhex
          have hxy_pos : 0 < |(x : ℝ)| * |(y : ℝ)| :=
            mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hx0)) (abs_pos.mpr (Int.cast_ne_zero.mpr hy0))
          have hbound : -( |(x : ℝ)| * |(y : ℝ)| ) < 2 * (x : ℝ) * (y : ℝ) * Real.cos θ := by
            rcases lt_trichotomy ((x : ℝ) * (y : ℝ)) 0 with hneg | h0 | hpos
            · have heq_neg : |(x : ℝ)| * |(y : ℝ)| = -((x : ℝ) * (y : ℝ)) := by
                rw [← abs_mul, abs_of_neg hneg]
              rw [heq_neg]
              nlinarith
            · exfalso; rcases mul_eq_zero.mp h0 with h | h <;> simp_all
            · have heq_pos : |(x : ℝ)| * |(y : ℝ)| = (x : ℝ) * (y : ℝ) := by
                rw [← abs_mul, abs_of_pos hpos]
              have : 0 < 2 * (x : ℝ) * (y : ℝ) * Real.cos θ := by nlinarith
              linarith
          linarith
        have hgt1 : 1 < ‖(x : ℝ) • shearV1 + (y : ℝ) • shearV2 θ‖ := by
          nlinarith [norm_nonneg ((x : ℝ) • shearV1 + (y : ℝ) • shearV2 θ)]
        refine ⟨hgt1.le, ⟨fun h => absurd h hgt1.ne', ?_⟩⟩
        rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩) <;> contradiction
  let lat : Fin L × Fin L → EuclideanSpace ℝ (Fin 2) := fun p =>
    (p.1 : ℝ) • shearV1 + (p.2 : ℝ) • shearV2 θ
  have hlat_diff : ∀ a b : Fin L × Fin L,
      lat a - lat b = ((((a.1 : ℤ) - (b.1 : ℤ) : ℤ)) : ℝ) • shearV1 +
        ((((a.2 : ℤ) - (b.2 : ℤ) : ℤ)) : ℝ) • shearV2 θ := by
    intro a b; dsimp [lat]; push_cast; module
  have hlat_sep : ∀ a b : Fin L × Fin L, a ≠ b →
      1 ≤ dist (lat a) (lat b) ∧
      (dist (lat a) (lat b) = 1 ↔
        ((a.1 : ℤ) - b.1 = 1 ∧ a.2 = b.2) ∨ ((a.1 : ℤ) - b.1 = -1 ∧ a.2 = b.2) ∨
        (a.1 = b.1 ∧ (a.2 : ℤ) - b.2 = 1) ∨ (a.1 = b.1 ∧ (a.2 : ℤ) - b.2 = -1)) := by
    intro a b hne
    have hneZ : ((a.1 : ℤ) - b.1 ≠ 0) ∨ ((a.2 : ℤ) - b.2 ≠ 0) := by
      by_contra h; push Not at h
      exact hne (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    rw [dist_eq_norm, hlat_diff a b]
    have hs := hvec_sep ((a.1 : ℤ) - b.1) ((a.2 : ℤ) - b.2) hneZ
    refine ⟨hs.1, ?_⟩
    have heq2 : (a.2 = b.2 ↔ (a.2 : ℤ) - b.2 = 0) := by
      constructor <;> intro h
      · rw [h, sub_self]
      · exact Fin.ext (by omega)
    have heq1 : (a.1 = b.1 ↔ (a.1 : ℤ) - b.1 = 0) := by
      constructor <;> intro h
      · rw [h, sub_self]
      · exact Fin.ext (by omega)
    simpa [heq1, heq2] using hs.2
  have hlat_inj : Function.Injective lat := by
    intro a b heq; by_contra hne
    have h1 := (hlat_sep a b hne).1; rw [heq, dist_self] at h1; linarith
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.image lat
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hlat_inj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, sq]
  · intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨b, _, rfl⟩
    exact (hlat_sep a b fun h => hne (congrArg lat h)).1
  · refine ⟨lat (⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _),
      lat (⟨1, by omega⟩, ⟨0, by omega⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [(hlat_sep _ _ (by simp [Fin.ext_iff])).2]
    right; left; simp
  · -- Bipartiteness: parity of `a.1.1 + a.2.1` flips along every unit edge, ruling out `K_3`!
    intro p hp q hq r hr ⟨h12, h23, h13⟩
    rcases Finset.mem_image.mp hp with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨b, _, rfl⟩
    rcases Finset.mem_image.mp hr with ⟨c, _, rfl⟩
    have hab : a ≠ b := fun h => by rw [h, dist_self] at h12; norm_num at h12
    have hbc : b ≠ c := fun h => by rw [h, dist_self] at h23; norm_num at h23
    have hac : a ≠ c := fun h => by rw [h, dist_self] at h13; norm_num at h13
    have e1 := (hlat_sep a b hab).2.mp h12
    have e2 := (hlat_sep b c hbc).2.mp h23
    have e3 := (hlat_sep a c hac).2.mp h13
    have hp1 : ((a.1 : ℤ) + a.2) - ((b.1 : ℤ) + b.2) = 1 ∨
        ((a.1 : ℤ) + a.2) - ((b.1 : ℤ) + b.2) = -1 := by
      rcases e1 with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h', h⟩ | ⟨h', h⟩ <;> simp [h, h']
    have hp2 : ((b.1 : ℤ) + b.2) - ((c.1 : ℤ) + c.2) = 1 ∨
        ((b.1 : ℤ) + b.2) - ((c.1 : ℤ) + c.2) = -1 := by
      rcases e2 with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h', h⟩ | ⟨h', h⟩ <;> simp [h, h']
    have hp3 : ((a.1 : ℤ) + a.2) - ((c.1 : ℤ) + c.2) = 1 ∨
        ((a.1 : ℤ) + a.2) - ((c.1 : ℤ) + c.2) = -1 := by
      rcases e3 with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h', h⟩ | ⟨h', h⟩ <;> simp [h, h']
    omega
  · -- Exact ordered unit-pair count `4 * L * (L - 1)`
    have hbij : ((A ×ˢ A).filter (fun pq => dist pq.1 pq.2 = 1)).card =
        ((Finset.univ ×ˢ Finset.univ : Finset ((Fin L × Fin L) × (Fin L × Fin L))).filter
          (fun ab => dist (lat ab.1) (lat ab.2) = 1)).card := by
      refine Finset.card_bij
        (fun pq hpq =>
          (Classical.choose (Finset.mem_image.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1),
           Classical.choose (Finset.mem_image.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).2)))
        ?_ ?_ ?_
      · intro pq hpq
        rw [Finset.mem_filter, Finset.mem_product] at hpq ⊢
        have h1 := Classical.choose_spec (Finset.mem_image.mp hpq.1.1)
        have h2 := Classical.choose_spec (Finset.mem_image.mp hpq.1.2)
        refine ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
        rw [h1.2, h2.2]; exact hpq.2
      · intro pq₁ hpq1 pq₂ hpq2 heq
        rw [Finset.mem_filter, Finset.mem_product] at hpq1 hpq2
        have h11 := Classical.choose_spec (Finset.mem_image.mp hpq1.1.1)
        have h12 := Classical.choose_spec (Finset.mem_image.mp hpq1.1.2)
        have h21 := Classical.choose_spec (Finset.mem_image.mp hpq2.1.1)
        have h22 := Classical.choose_spec (Finset.mem_image.mp hpq2.1.2)
        have hp1 := Prod.ext_iff.mp heq
        exact Prod.ext (h11.2.symm.trans (congrArg lat hp1.1 |>.trans h21.2))
          (h12.2.symm.trans (congrArg lat hp1.2 |>.trans h22.2))
      · intro ab hab
        rw [Finset.mem_filter, Finset.mem_product] at hab
        refine ⟨(lat ab.1, lat ab.2), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
            Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, hab.2⟩, ?_⟩
        refine Prod.ext (hlat_inj ?_) (hlat_inj ?_)
        · exact (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem _ (Finset.mem_univ ab.1)))).2
        · exact (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem _ (Finset.mem_univ ab.2)))).2
    rw [hbij]
    -- Count the 4 disjoint edge types: `(a1 = b1 + 1, a2 = b2)`, `(b1 = a1 + 1, a2 = b2)`, etc.
    have hpred : ∀ ab : (Fin L × Fin L) × (Fin L × Fin L),
        dist (lat ab.1) (lat ab.2) = 1 ↔
        (ab.1.1.1 = ab.2.1.1 + 1 ∧ ab.1.2 = ab.2.2) ∨
        (ab.2.1.1 = ab.1.1.1 + 1 ∧ ab.1.2 = ab.2.2) ∨
        (ab.1.1 = ab.2.1 ∧ ab.1.2.1 = ab.2.2.1 + 1) ∨
        (ab.1.1 = ab.2.1 ∧ ab.2.2.1 = ab.1.2.1 + 1) := by
      intro ⟨a, b⟩
      dsimp only
      by_cases hab : a = b
      · subst hab
        rw [dist_self]
        constructor
        · intro h; norm_num at h
        · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> omega
      · rw [(hlat_sep a b hab).2]
        constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · left; exact ⟨by omega, h2⟩
        · right; left; exact ⟨by omega, h2⟩
        · right; right; left; exact ⟨h1, by omega⟩
        · right; right; right; exact ⟨h1, by omega⟩
        · left; exact ⟨by omega, h2⟩
        · right; left; exact ⟨by omega, h2⟩
        · right; right; left; exact ⟨h1, by omega⟩
        · right; right; right; exact ⟨h1, by omega⟩
    have hsum_succ : (∑ i : Fin L, ∑ j : Fin L, if i.1 = j.1 + 1 then 1 else 0) = L - 1 := by
      rw [Finset.sum_comm]
      have hrow : ∀ j : Fin L, (∑ i : Fin L, if i.1 = j.1 + 1 then 1 else 0) =
          if j.1 + 1 < L then 1 else 0 := by
        intro j
        by_cases hj : j.1 + 1 < L
        · rw [if_pos hj]
          have huniq : ∀ i : Fin L, (i.1 = j.1 + 1 ↔ i = ⟨j.1 + 1, hj⟩) :=
            fun i => ⟨fun h => Fin.ext h, fun h => by simp [h]⟩
          simp_rw [huniq]
          simp [Finset.sum_ite_eq']
        · rw [if_neg hj]
          exact Finset.sum_eq_zero fun i _ => by rw [if_neg (fun h => by have := i.2; omega)]
      simp_rw [hrow, ← Finset.card_filter]
      have hf_img : (Finset.univ.filter (fun j : Fin L => j.1 + 1 < L)).image Fin.val =
          Finset.range (L - 1) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
        exact ⟨fun ⟨j, hj, hxj⟩ => by subst hxj; omega,
          fun hx => ⟨⟨x, by omega⟩, by simp; omega, rfl⟩⟩
      rw [← Finset.card_image_of_injective _ Fin.val_injective, hf_img, Finset.card_range]
    have hsum_pred : (∑ i : Fin L, ∑ j : Fin L, if j.1 = i.1 + 1 then 1 else 0) = L - 1 := by
      rw [Finset.sum_comm]; exact hsum_succ
    have h4 : ∀ (a1 b1 a2 b2 : Fin L),
        (if dist (lat (a1, a2)) (lat (b1, b2)) = 1 then 1 else 0) =
        (if a1.1 = b1.1 + 1 ∧ a2 = b2 then 1 else 0) +
        (if b1.1 = a1.1 + 1 ∧ a2 = b2 then 1 else 0) +
        (if a1 = b1 ∧ a2.1 = b2.1 + 1 then 1 else 0) +
        (if a1 = b1 ∧ b2.1 = a2.1 + 1 then 1 else 0) := by
      intro a1 b1 a2 b2
      have hp := hpred ((a1, a2), (b1, b2))
      by_cases c1 : a1.1 = b1.1 + 1 ∧ a2 = b2
      · have nc2 : ¬ (b1.1 = a1.1 + 1 ∧ a2 = b2) := fun h => by omega
        have nc3 : ¬ (a1 = b1 ∧ a2.1 = b2.1 + 1) := fun h => by
          have := congrArg Fin.val h.1; omega
        have nc4 : ¬ (a1 = b1 ∧ b2.1 = a2.1 + 1) := fun h => by
          have := congrArg Fin.val h.1; omega
        rw [if_pos (hp.mpr (Or.inl c1)), if_pos c1, if_neg nc2, if_neg nc3, if_neg nc4]
      · by_cases c2 : b1.1 = a1.1 + 1 ∧ a2 = b2
        · have nc3 : ¬ (a1 = b1 ∧ a2.1 = b2.1 + 1) := fun h => by
            have := congrArg Fin.val h.1; omega
          have nc4 : ¬ (a1 = b1 ∧ b2.1 = a2.1 + 1) := fun h => by
            have := congrArg Fin.val h.1; omega
          rw [if_pos (hp.mpr (Or.inr (Or.inl c2))), if_neg c1, if_pos c2, if_neg nc3, if_neg nc4]
        · by_cases c3 : a1 = b1 ∧ a2.1 = b2.1 + 1
          · have nc4 : ¬ (a1 = b1 ∧ b2.1 = a2.1 + 1) := fun h => by omega
            rw [if_pos (hp.mpr (Or.inr (Or.inr (Or.inl c3)))), if_neg c1, if_neg c2, if_pos c3, if_neg nc4]
          · by_cases c4 : a1 = b1 ∧ b2.1 = a2.1 + 1
            · rw [if_pos (hp.mpr (Or.inr (Or.inr (Or.inr c4)))), if_neg c1, if_neg c2, if_neg c3, if_pos c4]
            · rw [if_neg (fun h => by rcases hp.mp h with h' | h' | h' | h' <;> contradiction),
                if_neg c1, if_neg c2, if_neg c3, if_neg c4]
    have hc_eq : ((Finset.univ ×ˢ Finset.univ : Finset ((Fin L × Fin L) × (Fin L × Fin L))).filter
        (fun ab => dist (lat ab.1) (lat ab.2) = 1)).card =
        ∑ a1 : Fin L, ∑ a2 : Fin L, ∑ b1 : Fin L, ∑ b2 : Fin L,
          ((if a1.1 = b1.1 + 1 ∧ a2 = b2 then 1 else 0) +
           (if b1.1 = a1.1 + 1 ∧ a2 = b2 then 1 else 0) +
           (if a1 = b1 ∧ a2.1 = b2.1 + 1 then 1 else 0) +
           (if a1 = b1 ∧ b2.1 = a2.1 + 1 then 1 else 0)) := by
      rw [Finset.card_filter, Finset.sum_product, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a2 _ => by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun b1 _ => Finset.sum_congr rfl fun b2 _ => h4 a1 b1 a2 b2
    rw [hc_eq]
    simp_rw [Finset.sum_add_distrib]
    have hdiag_a : ∀ P : Prop, [Decidable P] → ∀ x : Fin L,
        (∑ y : Fin L, if P ∧ x = y then 1 else 0) = if P then 1 else 0 := by
      intro P _ x; by_cases hP : P <;> simp [hP]
    have ht1 : (∑ a1 : Fin L, ∑ a2 : Fin L, ∑ b1 : Fin L, ∑ b2 : Fin L,
        if a1.1 = b1.1 + 1 ∧ a2 = b2 then 1 else 0) = L * (L - 1) := by
      have h_in : ∀ a1 a2 b1 : Fin L,
          (∑ b2 : Fin L, if a1.1 = b1.1 + 1 ∧ a2 = b2 then 1 else 0) =
          if a1.1 = b1.1 + 1 then 1 else 0 := fun a1 a2 b1 => hdiag_a _ a2
      simp_rw [h_in]
      have h_cst : ∀ a1 : Fin L,
          (∑ _a2 : Fin L, ∑ b1 : Fin L, if a1.1 = b1.1 + 1 then 1 else 0) =
          L * ∑ b1 : Fin L, if a1.1 = b1.1 + 1 then 1 else 0 := by
        intro a1; simp [Finset.sum_const]
      simp_rw [h_cst, ← Finset.mul_sum, hsum_succ]
    have ht2 : (∑ a1 : Fin L, ∑ a2 : Fin L, ∑ b1 : Fin L, ∑ b2 : Fin L,
        if b1.1 = a1.1 + 1 ∧ a2 = b2 then 1 else 0) = L * (L - 1) := by
      have h_in : ∀ a1 a2 b1 : Fin L,
          (∑ b2 : Fin L, if b1.1 = a1.1 + 1 ∧ a2 = b2 then 1 else 0) =
          if b1.1 = a1.1 + 1 then 1 else 0 := fun a1 a2 b1 => hdiag_a _ a2
      simp_rw [h_in]
      have h_cst : ∀ a1 : Fin L,
          (∑ _a2 : Fin L, ∑ b1 : Fin L, if b1.1 = a1.1 + 1 then 1 else 0) =
          L * ∑ b1 : Fin L, if b1.1 = a1.1 + 1 then 1 else 0 := by
        intro a1; simp [Finset.sum_const]
      simp_rw [h_cst, ← Finset.mul_sum, hsum_pred]
    have ht3 : (∑ a1 : Fin L, ∑ a2 : Fin L, ∑ b1 : Fin L, ∑ b2 : Fin L,
        if a1 = b1 ∧ a2.1 = b2.1 + 1 then 1 else 0) = L * (L - 1) := by
      have h_in : ∀ a1 a2 b1 : Fin L,
          (∑ b2 : Fin L, if a1 = b1 ∧ a2.1 = b2.1 + 1 then 1 else 0) =
          if a1 = b1 then ∑ b2 : Fin L, if a2.1 = b2.1 + 1 then 1 else 0 else 0 := by
        intro a1 a2 b1; by_cases h : a1 = b1 <;> simp [h]
      simp_rw [h_in, Finset.sum_ite_eq, Finset.mem_univ]
      simp only [↓reduceIte]
      simp only [hsum_succ, Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have ht4 : (∑ a1 : Fin L, ∑ a2 : Fin L, ∑ b1 : Fin L, ∑ b2 : Fin L,
        if a1 = b1 ∧ b2.1 = a2.1 + 1 then 1 else 0) = L * (L - 1) := by
      have h_in : ∀ a1 a2 b1 : Fin L,
          (∑ b2 : Fin L, if a1 = b1 ∧ b2.1 = a2.1 + 1 then 1 else 0) =
          if a1 = b1 then ∑ b2 : Fin L, if b2.1 = a2.1 + 1 then 1 else 0 else 0 := by
        intro a1 a2 b1; by_cases h : a1 = b1 <;> simp [h]
      simp_rw [h_in, Finset.sum_ite_eq, Finset.mem_univ]
      simp only [↓reduceIte]
      simp only [hsum_pred, Finset.sum_const, Finset.card_fin, smul_eq_mul]
    rw [ht1, ht2, ht3, ht4]
    ring

/-- Theorem 5b (Sheared-Lattice Strict Positive Interior KKT Stress Balance):
At any interior lattice point `p` with four unit neighbors `p ± v₁, p ± v₂(θ)`, ANY positive
weights `ω₁, ω₂ > 0` achieve exact vector equilibrium. -/
theorem ppl083_sheared_lattice_interior_kkt (p v₁ v₂ : EuclideanSpace ℝ (Fin 2)) (ω₁ ω₂ : ℝ) :
    ω₁ • (p - (p + v₁)) + ω₁ • (p - (p - v₁)) +
    ω₂ • (p - (p + v₂)) + ω₂ • (p - (p - v₂)) = 0 := by
  module

/-- Theorem 5c (Sheared-Lattice Voronoi Area Excess Budget):
For `0 < ε ≤ π / 6`, the fundamental parallelogram area `sin(π / 3 + ε)` strictly exceeds
Thue's optimum `√3 / 2` by at most `ε / 2`; hence across `n` cells the total area excess is
`≤ ε * n / 2` (smaller than `1` whenever `ε < 2 / n`). -/
theorem ppl083_sheared_lattice_area_excess {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ Real.pi / 6) :
    Real.sqrt 3 / 2 < Real.sin (Real.pi / 3 + ε) ∧
    Real.sin (Real.pi / 3 + ε) - Real.sqrt 3 / 2 ≤ ε / 2 := by
  have hgt : Real.sqrt 3 / 2 < Real.sin (Real.pi / 3 + ε) := by
    rw [← Real.sin_pi_div_three]
    exact Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
  have hadd : Real.sin (Real.pi / 3 + ε) =
      (Real.sqrt 3 / 2) * Real.cos ε + (1 / 2) * Real.sin ε := by
    rw [Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hcos : Real.cos ε ≤ 1 := Real.cos_le_one ε
  have hsin : Real.sin ε ≤ ε := Real.sin_le hε0.le
  have hsqrt : 0 ≤ Real.sqrt 3 / 2 := by positivity
  refine ⟨hgt, ?_⟩
  rw [hadd]
  nlinarith

/-- Theorem 5d (Sheared-Lattice Local Diameter Stability under Shear):
For positive lattice steps `a, b > 0`, the squared long diagonal `‖a • v₁ + b • v₂(θ)‖^2` has
strictly negative derivative `-2 * a * b * sin θ` on `(0, π)`, the squared short diagonal
`‖a • v₁ - b • v₂(θ)‖^2` has strictly positive derivative `+2 * a * b * sin θ`, and their
maximum `max ‖a • v₁ + b • v₂(θ)‖^2 ‖a • v₁ - b • v₂(θ)‖^2` is uniquely minimized on `[0, π]`
at `θ = π / 2 > π / 3` (the orthogonal / square configuration). -/
theorem ppl083_sheared_lattice_diam_competition
    {v₁ : EuclideanSpace ℝ (Fin 2)} {v₂ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hv₁ : ‖v₁‖ = 1) (hv₂ : ∀ θ : ℝ, ‖v₂ θ‖ = 1 ∧ inner ℝ v₁ (v₂ θ) = Real.cos θ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∀ θ : ℝ, HasDerivAt (fun t => ‖a • v₁ + b • v₂ t‖ ^ 2) (-2 * a * b * Real.sin θ) θ) ∧
    (∀ θ : ℝ, HasDerivAt (fun t => ‖a • v₁ - b • v₂ t‖ ^ 2) (2 * a * b * Real.sin θ) θ) ∧
    (∀ θ : ℝ, ‖a • v₁ + b • v₂ (Real.pi / 2)‖ ^ 2 ≤
        max (‖a • v₁ + b • v₂ θ‖ ^ 2) (‖a • v₁ - b • v₂ θ‖ ^ 2) ∧
      (θ ∈ Set.Icc 0 Real.pi → θ ≠ Real.pi / 2 →
        max (‖a • v₁ + b • v₂ (Real.pi / 2)‖ ^ 2)
            (‖a • v₁ - b • v₂ (Real.pi / 2)‖ ^ 2) <
        max (‖a • v₁ + b • v₂ θ‖ ^ 2) (‖a • v₁ - b • v₂ θ‖ ^ 2))) := by
  have hnorm_sq : ∀ t c d : ℝ, ‖c • v₁ + d • v₂ t‖ ^ 2 = c ^ 2 + d ^ 2 + 2 * c * d * Real.cos t := by
    intro t c d
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      hv₁, (hv₂ t).1, real_inner_smul_left, real_inner_smul_right, (hv₂ t).2,
      mul_one, mul_one, sq_abs, sq_abs]
    ring
  have hderiv_pos : ∀ θ : ℝ,
      HasDerivAt (fun t => ‖a • v₁ + b • v₂ t‖ ^ 2) (-2 * a * b * Real.sin θ) θ := by
    intro θ
    have hfun : (fun t => ‖a • v₁ + b • v₂ t‖ ^ 2) =
        (fun t => a ^ 2 + b ^ 2 + 2 * a * b * Real.cos t) :=
      funext fun t => hnorm_sq t a b
    rw [hfun]
    have hc := (Real.hasDerivAt_cos θ).const_mul (2 * a * b)
    have hconst := (hasDerivAt_const θ (a ^ 2 + b ^ 2)).add hc
    rw [show (0 + 2 * a * b * -Real.sin θ : ℝ) = -2 * a * b * Real.sin θ by ring] at hconst
    exact hconst
  have hderiv_neg : ∀ θ : ℝ,
      HasDerivAt (fun t => ‖a • v₁ - b • v₂ t‖ ^ 2) (2 * a * b * Real.sin θ) θ := by
    intro θ
    have hfun : (fun t => ‖a • v₁ - b • v₂ t‖ ^ 2) =
        (fun t => a ^ 2 + b ^ 2 + 2 * a * (-b) * Real.cos t) :=
      funext fun t => by
        rw [show a • v₁ - b • v₂ t = a • v₁ + (-b) • v₂ t by module, hnorm_sq]
        ring
    rw [hfun]
    have hc := (Real.hasDerivAt_cos θ).const_mul (2 * a * (-b))
    have hconst := (hasDerivAt_const θ (a ^ 2 + b ^ 2)).add hc
    rw [show (0 + 2 * a * (-b) * -Real.sin θ : ℝ) = 2 * a * b * Real.sin θ by ring] at hconst
    exact hconst
  refine ⟨hderiv_pos, hderiv_neg, fun θ => ?_⟩
  have hplus : ‖a • v₁ + b • v₂ (Real.pi / 2)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hnorm_sq, Real.cos_pi_div_two]; ring
  have hminus : ‖a • v₁ - b • v₂ (Real.pi / 2)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [show a • v₁ - b • v₂ (Real.pi / 2) = a • v₁ + (-b) • v₂ (Real.pi / 2) by module,
      hnorm_sq, Real.cos_pi_div_two]; ring
  have hθ_plus : ‖a • v₁ + b • v₂ θ‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos θ :=
    hnorm_sq θ a b
  have hθ_minus : ‖a • v₁ - b • v₂ θ‖ ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ := by
    rw [show a • v₁ - b • v₂ θ = a • v₁ + (-b) • v₂ θ by module,
      hnorm_sq]; ring
  have hab_pos : 0 < a * b := mul_pos ha hb
  constructor
  · rw [hplus, hθ_plus, hθ_minus]
    rcases le_total (Real.cos θ) 0 with hc | hc
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)
  · intro hmem hne
    rw [hplus, hminus, max_self, hθ_plus, hθ_minus]
    have hc_ne0 : Real.cos θ ≠ 0 := by
      intro hc0
      have : θ = Real.pi / 2 := by
        rcases lt_trichotomy θ (Real.pi / 2) with hlt | heq | hgt
        · have := Real.strictAntiOn_cos ⟨hmem.1, hmem.2⟩
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hlt
          rw [hc0, Real.cos_pi_div_two] at this; linarith
        · exact heq
        · have := Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨hmem.1, hmem.2⟩ hgt
          rw [hc0, Real.cos_pi_div_two] at this; linarith
      exact hne this
    rcases lt_or_gt_of_ne hc_ne0 with hc | hc
    · exact lt_max_of_lt_right (by nlinarith)
    · exact lt_max_of_lt_left (by nlinarith)

end ShearedLatticeBarrier

end PPL083
