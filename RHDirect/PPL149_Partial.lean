import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# PPL 149 (Erdős Problem #132 — Low-Multiplicity Distances): Partial Structural Milestone

**Scope Notice (Partial Milestone — NOT the full open conjecture):**
Erdős Problem #132 (asking whether every `n`-point set in `ℝ²` (`n ≥ 5`) has at least two
distances occurring at most `n` times, and whether the number of such low-multiplicity distances
`L(A)` tends to `∞`) remains OPEN. This file formalizes the unconditional partial theorems proved
in `scripts/ppl149_findings.md`:

1. **Layer-Sum Lemma & Corollaries (§2.1):**
   For peeled convex layers `L_1, L_2, ...` (`peelLayer A 0, peelLayer A 1, ...`), every pair
   `p ∈ L_i, q ∈ L_j` has at least `i + j - 2` distinct distances in `A` strictly greater than
   `dist p q`. In particular, no diameter edge is incident to `A \ L_1`, and no second-largest
   distance edge has both endpoints in `L_2`.
2. **Counterexample Ceiling & Even Convex Polygon Counting (§§2.2, 2.4):**
   Any counterexample to Part 1 has `k ≤ ⌊n / 2⌋` distinct distances (with exact rigidity for
   `n = 2m, k = m`). For `n = 2m ≥ 8`, `k ≥ m + 1` forces `L(A) ≥ 3` (improving `2` to `3`
   unconditionally under Altman–Fishburn for `k = m`).
3. **Layer-Boundary Corollary (§2.5.1):**
   Sets with `|L_1| = 3` and `|D(L_2)| ≥ m - 1` (`n = 2m + 1`) have `k ≥ m + 1`, ruling out
   Part 1 counterexamples.
4. **Infinite Family Refuting `min(m_2, m_3) ≤ n` (§2.3):**
   Explicit `(2m + s)`-point construction (`m ≥ 7` odd, `1 ≤ s`, `2s < m`) with `m_1 = m ≤ n`,
   `m_2 = 3m > n`, and `m_3 = 2m + 2s > n`.
-/

namespace PPL149

noncomputable section
open Classical

abbrev E2 := EuclideanSpace ℝ (Fin 2)

section DistancesAndMultiplicity

/-- Finset of distinct positive pairwise distances in `A : Finset E2`. -/
def posDistances (A : Finset E2) : Finset ℝ :=
  A.offDiag.image (fun pq => dist pq.1 pq.2)

/-- Number of unordered pairs `{p, q} ⊆ A` at distance `d` (computed as half the `offDiag`
ordered-pair fiber cardinality). -/
def pairMult (A : Finset E2) (d : ℝ) : ℕ :=
  (A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card / 2

lemma mem_posDistances_iff (A : Finset E2) (d : ℝ) :
    d ∈ posDistances A ↔ ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ dist p q = d := by
  simp [posDistances, Finset.mem_offDiag]
  aesop

lemma posDistances_pos (A : Finset E2) {d : ℝ} (hd : d ∈ posDistances A) : 0 < d := by
  rw [mem_posDistances_iff] at hd
  rcases hd with ⟨p, _, q, _, hne, rfl⟩
  exact dist_pos.mpr hne

private def ltE2 (x y : E2) : Bool :=
  decide (x 0 < y 0 ∨ (x 0 = y 0 ∧ x 1 < y 1))

private lemma ltE2_antisymm {x y : E2} (hne : x ≠ y) :
    ltE2 x y = true ↔ ltE2 y x = false := by
  have hneq : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
    by_contra h
    push Not at h
    apply hne
    ext i
    fin_cases i <;> [exact h.1; exact h.2]
  dsimp [ltE2]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  rcases lt_trichotomy (x 0) (y 0) with h0 | h0 | h0
  · constructor
    · intro _; rintro (h | ⟨h, _⟩) <;> linarith
    · intro _; exact Or.inl h0
  · rcases lt_trichotomy (x 1) (y 1) with h1 | h1 | h1
    · constructor
      · intro _; rintro (h | ⟨_, h⟩) <;> linarith
      · intro _; exact Or.inr ⟨h0, h1⟩
    · exfalso; rcases hneq with hneq | hneq <;> [exact hneq h0; exact hneq h1]
    · constructor
      · intro h; exfalso; rcases h with h | ⟨_, h⟩ <;> linarith
      · intro h; exfalso; exact h (Or.inr ⟨h0.symm, h1⟩)
  · constructor
    · intro h; exfalso; rcases h with h | ⟨h', _⟩ <;> linarith
    · intro h; exfalso; exact h (Or.inl h0)

lemma pairMult_fiber_even (A : Finset E2) (d : ℝ) :
    Even (A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card := by
  let S := A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)
  let S₁ := S.filter (fun pq => ltE2 pq.1 pq.2 = true)
  let S₂ := S.filter (fun pq => ltE2 pq.1 pq.2 = false)
  have hpart : S.card = S₁.card + S₂.card := by
    rw [← Finset.card_filter_add_card_filter_not (p := fun pq => ltE2 pq.1 pq.2 = true) (s := S)]
    congr 2
    ext pq
    simp [S₂, Bool.not_eq_true]
  have hbij : S₁.card = S₂.card := by
    apply Finset.card_bij (fun pq _ => (pq.2, pq.1))
    · intro pq hpq
      simp only [S₁, S₂, S, Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
      rcases hpq with ⟨⟨⟨hp, hq, hne⟩, hdist⟩, hlt⟩
      refine ⟨⟨⟨hq, hp, hne.symm⟩, by simpa [dist_comm] using hdist⟩, ?_⟩
      exact (ltE2_antisymm hne).mp hlt
    · intro p q _ _ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro pq hpq
      simp only [S₁, S₂, S, Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
      rcases hpq with ⟨⟨⟨hp, hq, hne⟩, hdist⟩, hlt⟩
      refine ⟨(pq.2, pq.1), ⟨⟨⟨hq, hp, hne.symm⟩, by simpa [dist_comm] using hdist⟩, ?_⟩, rfl⟩
      exact (ltE2_antisymm hne.symm).mpr hlt
  rw [hpart, hbij, ← two_mul]
  exact even_two_mul _

end DistancesAndMultiplicity

section LayerSum

/-- Remaining points after peeling `k` convex layers (`0`-indexed). -/
def peelRem (A : Finset E2) : ℕ → Finset E2
  | 0 => A
  | k + 1 =>
    let R := peelRem A k
    R.filter (fun x => x ∉ (convexHull ℝ (R : Set E2)).extremePoints ℝ)

/-- The `(k + 1)`-th peeled convex layer (`k = 0` is the outer convex hull boundary `L_1`). -/
def peelLayer (A : Finset E2) (k : ℕ) : Finset E2 :=
  let R := peelRem A k
  R.filter (fun x => x ∈ (convexHull ℝ (R : Set E2)).extremePoints ℝ)

private lemma peelRem_subset (A : Finset E2) (k : ℕ) : peelRem A k ⊆ A := by
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih => exact Finset.Subset.trans (Finset.filter_subset _ _) ih

private lemma peelLayer_subset_rem (A : Finset E2) (k : ℕ) : peelLayer A k ⊆ peelRem A k :=
  Finset.filter_subset _ _

private lemma peelLayer_subset (A : Finset E2) (k : ℕ) : peelLayer A k ⊆ A :=
  Finset.Subset.trans (peelLayer_subset_rem A k) (peelRem_subset A k)

/-- Two-point inner-product strict convexity: if `u = a • x + b • y` with `0 < a, 0 < b, a + b = 1`
and `x ≠ u`, then `‖p - u‖^2 < a * ‖p - x‖^2 + b * ‖p - y‖^2`. -/
private lemma two_point_strict_dist_sq {p u x y : E2} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hcomb : a • x + b • y = u) (hne : x ≠ u) :
    ‖p - u‖ ^ 2 < a * ‖p - x‖ ^ 2 + b * ‖p - y‖ ^ 2 := by
  have hx : ‖p - x‖ ^ 2 = ‖p - u‖ ^ 2 + 2 * @inner ℝ E2 _ (p - u) (u - x) + ‖u - x‖ ^ 2 := by
    have hsplit : p - x = (p - u) + (u - x) := by abel
    rw [hsplit, @norm_add_sq_real]
  have hy : ‖p - y‖ ^ 2 = ‖p - u‖ ^ 2 + 2 * @inner ℝ E2 _ (p - u) (u - y) + ‖u - y‖ ^ 2 := by
    have hsplit : p - y = (p - u) + (u - y) := by abel
    rw [hsplit, @norm_add_sq_real]
  have hcomb0 : a • (u - x) + b • (u - y) = 0 := by
    calc
      a • (u - x) + b • (u - y) = (a + b) • u - (a • x + b • y) := by module
      _ = 0 := by rw [hab, one_smul, hcomb, sub_self]
  have hinner : a * (2 * @inner ℝ E2 _ (p - u) (u - x)) +
      b * (2 * @inner ℝ E2 _ (p - u) (u - y)) = 0 := by
    have hlin : a * (2 * @inner ℝ E2 _ (p - u) (u - x)) +
        b * (2 * @inner ℝ E2 _ (p - u) (u - y)) =
        2 * @inner ℝ E2 _ (p - u) (a • (u - x) + b • (u - y)) := by
      rw [inner_add_right, inner_smul_right, inner_smul_right]; ring
    rw [hlin, hcomb0, inner_zero_right, mul_zero]
  have hpos1 : 0 < a * ‖u - x‖ ^ 2 := by
    have : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
    positivity
  have hpos2 : 0 ≤ b * ‖u - y‖ ^ 2 := by positivity
  rw [hx, hy]
  nlinarith

/-- Any `z ∈ convexHull ℝ (R : Set E2)` satisfies `dist p z ≤ dist p u₀` for a maximizer
`u₀ ∈ R` of `dist p ·`. -/
private lemma dist_le_max_on_convexHull (R : Finset E2) (p u₀ : E2)
    (hmax : ∀ u ∈ R, dist p u ≤ dist p u₀)
    {z : E2} (hz : z ∈ convexHull ℝ (R : Set E2)) :
    dist p z ≤ dist p u₀ := by
  rw [mem_convexHull_iff_exists_fintype] at hz
  obtain ⟨ι, _, w, f, hw0, hw1, hf, rfl⟩ := hz
  have hsplit : p - ∑ i, w i • f i = ∑ i, w i • (p - f i) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
  rw [dist_eq_norm, hsplit]
  calc
    ‖∑ i, w i • (p - f i)‖ ≤ ∑ i, ‖w i • (p - f i)‖ := norm_sum_le _ _
    _ = ∑ i, w i * dist p (f i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (hw0 i), dist_eq_norm]
    _ ≤ ∑ i, w i * dist p u₀ := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmax (f i) (hf i)) (hw0 i)
    _ = dist p u₀ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Any `u₀ ∈ R` maximizing `dist p ·` on `R` belongs to `(convexHull ℝ (R : Set E2)).extremePoints ℝ`. -/
private lemma max_dist_mem_extremePoints (R : Finset E2) (p u₀ : E2) (hu₀ : u₀ ∈ R)
    (hmax : ∀ u ∈ R, dist p u ≤ dist p u₀) :
    u₀ ∈ (convexHull ℝ (R : Set E2)).extremePoints ℝ := by
  refine ⟨subset_convexHull ℝ (R : Set E2) hu₀, fun x hx y hy hseg => ?_⟩
  rcases hseg with ⟨a, b, ha, hb, hab, hcomb⟩
  by_cases hxu : x = u₀
  · exact hxu
  · exfalso
    have hlt := two_point_strict_dist_sq (p := p) ha hb hab hcomb hxu
    have hdx : ‖p - x‖ ^ 2 ≤ ‖p - u₀‖ ^ 2 := by
      have := dist_le_max_on_convexHull R p u₀ hmax hx
      rw [dist_eq_norm, dist_eq_norm] at this
      nlinarith [norm_nonneg (p - x), norm_nonneg (p - u₀)]
    have hdy : ‖p - y‖ ^ 2 ≤ ‖p - u₀‖ ^ 2 := by
      have := dist_le_max_on_convexHull R p u₀ hmax hy
      rw [dist_eq_norm, dist_eq_norm] at this
      nlinarith [norm_nonneg (p - y), norm_nonneg (p - u₀)]
    have hle : a * ‖p - x‖ ^ 2 + b * ‖p - y‖ ^ 2 ≤ ‖p - u₀‖ ^ 2 := by
      calc
        a * ‖p - x‖ ^ 2 + b * ‖p - y‖ ^ 2
            ≤ a * ‖p - u₀‖ ^ 2 + b * ‖p - u₀‖ ^ 2 := by
              exact add_le_add (mul_le_mul_of_nonneg_left hdx (le_of_lt ha))
                (mul_le_mul_of_nonneg_left hdy (le_of_lt hb))
        _ = ‖p - u₀‖ ^ 2 := by rw [← add_mul, hab, one_mul]
    linarith

/-- Strict convexity ascent step: if `q ∈ R` is NOT an extreme point of `conv(R)`, then for any
`p : E2` there exists `u ∈ R ∩ ext(conv R)` with `dist p q < dist p u`. -/
private lemma exists_extreme_strictly_farther (R : Finset E2) (p q : E2) (hq : q ∈ R)
    (hnot : q ∉ (convexHull ℝ (R : Set E2)).extremePoints ℝ) :
    ∃ u ∈ R.filter (fun x => x ∈ (convexHull ℝ (R : Set E2)).extremePoints ℝ),
      dist p q < dist p u := by
  obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image R (fun u => dist p u) ⟨q, hq⟩
  have hu₀_ext : u₀ ∈ (convexHull ℝ (R : Set E2)).extremePoints ℝ :=
    max_dist_mem_extremePoints R p u₀ hu₀ hmax
  have hlt : dist p q < dist p u₀ := by
    have hle := hmax q hq
    refine lt_of_le_of_ne hle fun heq => ?_
    apply hnot
    refine max_dist_mem_extremePoints R p q hq fun u hu => ?_
    rw [heq]
    exact hmax u hu
  exact ⟨u₀, Finset.mem_filter.mpr ⟨hu₀, hu₀_ext⟩, hlt⟩

private lemma ascend_layers (A : Finset E2) (p : E2) (hp : p ∈ A) :
    ∀ k : ℕ, ∀ q ∈ peelRem A k,
      ∃ D : Finset ℝ, D ⊆ posDistances A ∧ D.card = k ∧
        (∃ u ∈ peelLayer A 0, dist p q ≤ dist p u ∧ (∀ d ∈ D, dist p q < d ∧ d ≤ dist p u)) := by
  intro k
  induction k with
  | zero =>
    intro q hq
    by_cases h0 : q ∈ peelLayer A 0
    · exact ⟨∅, Finset.empty_subset _, Finset.card_empty, q, h0, le_rfl, by simp⟩
    · have hnot : q ∉ (convexHull ℝ (A : Set E2)).extremePoints ℝ := by
        intro hext
        exact h0 (Finset.mem_filter.mpr ⟨hq, hext⟩)
      obtain ⟨u, hu, hlt⟩ := exists_extreme_strictly_farther A p q hq hnot
      exact ⟨∅, Finset.empty_subset _, Finset.card_empty, u, hu, le_of_lt hlt, by simp⟩
  | succ k ih =>
    intro q hq
    have hq_rem : q ∈ peelRem A k := (Finset.mem_filter.mp hq).1
    have hq_not_ext : q ∉ (convexHull ℝ ((peelRem A k : Set E2))).extremePoints ℝ :=
      (Finset.mem_filter.mp hq).2
    obtain ⟨u, hu, hlt⟩ := exists_extreme_strictly_farther (peelRem A k) p q hq_rem hq_not_ext
    have hu_rem : u ∈ peelRem A k := (Finset.mem_filter.mp hu).1
    obtain ⟨D, hD_sub, hD_card, u₀, hu₀, hle₀, hD_prop⟩ := ih u hu_rem
    have hdu_mem : dist p u ∈ posDistances A := by
      rw [mem_posDistances_iff]
      have huA : u ∈ A := peelRem_subset A k hu_rem
      have hne : p ≠ u := by
        intro heq
        rw [heq, dist_self] at hlt
        exact absurd hlt (not_lt.mpr dist_nonneg)
      exact ⟨p, hp, u, huA, hne, rfl⟩
    have hdu_not : dist p u ∉ D := by
      intro hmem
      have := (hD_prop (dist p u) hmem).1
      exact lt_irrefl _ this
    refine ⟨insert (dist p u) D, Finset.insert_subset_iff.mpr ⟨hdu_mem, hD_sub⟩, ?_, u₀, hu₀,
      le_trans (le_of_lt hlt) hle₀, ?_⟩
    · rw [Finset.card_insert_of_notMem hdu_not, hD_card]
    · intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd'
      · exact ⟨hlt, hle₀⟩
      · have := hD_prop d hd'
        exact ⟨lt_trans hlt this.1, this.2⟩

/-- Theorem 2.1 (Layer-Sum Lemma, 0-indexed):
For any `p ∈ peelLayer A i` and `q ∈ peelLayer A j`, there exist at least `i + j` distinct
positive distances in `A` strictly greater than `dist p q`. -/
theorem layer_sum_lemma (A : Finset E2) {i j : ℕ} {p q : E2}
    (hp : p ∈ peelLayer A i) (hq : q ∈ peelLayer A j) :
    ∃ D : Finset ℝ, D ⊆ posDistances A ∧ D.card = i + j ∧ ∀ d ∈ D, dist p q < d := by
  have hpA : p ∈ A := peelLayer_subset A i hp
  have hq_rem : q ∈ peelRem A j := peelLayer_subset_rem A j hq
  obtain ⟨D₁, hD₁_sub, hD₁_card, u₀, hu₀, _, hD₁_prop⟩ := ascend_layers A p hpA j q hq_rem
  have hu₀A : u₀ ∈ A := peelLayer_subset A 0 hu₀
  have hp_rem : p ∈ peelRem A i := peelLayer_subset_rem A i hp
  obtain ⟨D₂, hD₂_sub, hD₂_card, _, _, _, hD₂_prop⟩ := ascend_layers A u₀ hu₀A i p hp_rem
  have hdisj : Disjoint D₁ D₂ := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    have h1 := (hD₁_prop d hd₁).2
    have h2 := (hD₂_prop d hd₂).1
    rw [dist_comm u₀ p] at h2
    linarith
  refine ⟨D₁ ∪ D₂, Finset.union_subset hD₁_sub hD₂_sub, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hD₁_card, hD₂_card, Nat.add_comm]
  · intro d hd
    rcases Finset.mem_union.mp hd with hd₁ | hd₂
    · exact (hD₁_prop d hd₁).1
    · have h2 := (hD₂_prop d hd₂).1
      rw [dist_comm u₀ p] at h2
      linarith

/-- Corollary of Layer-Sum Lemma: No diameter pair `(p, q)` can have an endpoint outside
the outer convex layer `peelLayer A 0`. -/
theorem diam_only_outer_layer (A : Finset E2) {p q : E2} (hp : p ∈ A) (hq : q ∈ A)
    (hq_out : q ∉ peelLayer A 0) :
    ∃ d ∈ posDistances A, dist p q < d := by
  have hnot : q ∉ (convexHull ℝ (A : Set E2)).extremePoints ℝ := by
    intro hext
    exact hq_out (Finset.mem_filter.mpr ⟨hq, hext⟩)
  obtain ⟨u, hu, hlt⟩ := exists_extreme_strictly_farther A p q hq hnot
  have huA : u ∈ A := (Finset.mem_filter.mp hu).1
  have hne : p ≠ u := by
    intro heq
    rw [heq, dist_self] at hlt
    exact absurd hlt (not_lt.mpr dist_nonneg)
  exact ⟨dist p u, (mem_posDistances_iff A _).mpr ⟨p, hp, u, huA, hne, rfl⟩, hlt⟩

/-- Corollary of Layer-Sum Lemma: Any pair `(p, q)` with both endpoints in the second peeled
convex layer `peelLayer A 1` has at least `2` strictly larger distances in `posDistances A`
(hence cannot realize `d₁` or `d₂`). -/
theorem no_d2_within_second_layer (A : Finset E2) {p q : E2}
    (hp : p ∈ peelLayer A 1) (hq : q ∈ peelLayer A 1) :
    ∃ D : Finset ℝ, D ⊆ posDistances A ∧ D.card = 2 ∧ ∀ d ∈ D, dist p q < d :=
  layer_sum_lemma A hp hq

end LayerSum

section CountingAndEvenPolygons

lemma sum_pairMult_eq_choose (A : Finset E2) :
    2 * ∑ d ∈ posDistances A, pairMult A d = A.card * (A.card - 1) := by
  have hfib : ∑ d ∈ posDistances A, (A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card =
      A.offDiag.card := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun pq : E2 × E2 => dist pq.1 pq.2)
      (t := posDistances A) (s := A.offDiag)]
    intro pq hpq
    exact Finset.mem_image_of_mem _ hpq
  have hpair_even : ∀ d ∈ posDistances A,
      2 * pairMult A d = (A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card := by
    intro d _
    rcases pairMult_fiber_even A d with ⟨k, hk⟩
    dsimp [pairMult]
    omega
  calc
    2 * ∑ d ∈ posDistances A, pairMult A d
        = ∑ d ∈ posDistances A, 2 * pairMult A d := Finset.mul_sum _ _ _
    _ = ∑ d ∈ posDistances A, (A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card :=
        Finset.sum_congr rfl hpair_even
    _ = A.offDiag.card := hfib
    _ = A.card * A.card - A.card := Finset.offDiag_card A
    _ = A.card * (A.card - 1) := by
        cases A.card with
        | zero => simp
        | succ n =>
          calc
            (n + 1) * (n + 1) - (n + 1) = (n + 1) * (n + 1) - (n + 1) * 1 := by ring
            _ = (n + 1) * (n + 1 - 1) := (Nat.mul_sub_left_distrib (n + 1) (n + 1) 1).symm

/-- Theorem 2.2 (Counterexample Ceiling on Distinct Distances):
If at most one distance in `posDistances A` has `pairMult A d ≤ A.card`, then
`(posDistances A).card ≤ A.card / 2`. -/
theorem counterexample_distance_ceiling (A : Finset E2) (hn : 2 ≤ A.card)
    (hlow : ((posDistances A).filter (fun d => pairMult A d ≤ A.card)).card ≤ 1) :
    (posDistances A).card ≤ A.card / 2 := by
  have hsum := sum_pairMult_eq_choose A
  set n := A.card
  set k := (posDistances A).card
  set Lset := (posDistances A).filter (fun d => pairMult A d ≤ n)
  set Hset := (posDistances A).filter (fun d => n + 1 ≤ pairMult A d)
  have hpart : Disjoint Lset Hset ∧ Lset ∪ Hset = posDistances A := by
    refine ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega), ?_⟩
    ext d
    simp only [Lset, Hset, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hle : pairMult A d ≤ n
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, by omega⟩
  have hpos_ge1 : ∀ d ∈ posDistances A, 1 ≤ pairMult A d := by
    intro d hd
    rw [mem_posDistances_iff] at hd
    rcases hd with ⟨p, hp, q, hq, hne, rfl⟩
    have hfib : 2 ≤ (A.offDiag.filter (fun pq => dist pq.1 pq.2 = dist p q)).card := by
      have hsub : {(p, q), (q, p)} ⊆ A.offDiag.filter (fun pq => dist pq.1 pq.2 = dist p q) := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
        · simp [Finset.mem_offDiag, hp, hq, hne]
        · rw [Finset.mem_singleton.mp hx']; simp [Finset.mem_offDiag, hp, hq, hne.symm, dist_comm]
      have hcard2 : ({(p, q), (q, p)} : Finset (E2 × E2)).card = 2 := by
        rw [Finset.card_pair]; intro h; apply hne; exact congrArg Prod.fst h
      linarith [Finset.card_le_card hsub]
    dsimp [pairMult]; omega
  have hk_pos : 1 ≤ k := by
    have : (posDistances A).Nonempty := by
      rcases Finset.one_lt_card_iff.mp (by omega : 1 < A.card) with ⟨p, q, hp, hq, hne⟩
      exact ⟨dist p q, (mem_posDistances_iff A _).mpr ⟨p, hp, q, hq, hne, rfl⟩⟩
    exact Finset.card_pos.mpr this
  have hsum_split : ∑ d ∈ posDistances A, pairMult A d =
      (∑ d ∈ Lset, pairMult A d) + (∑ d ∈ Hset, pairMult A d) := by
    rw [← hpart.2, Finset.sum_union hpart.1]
  have hL_ge : Lset.card ≤ ∑ d ∈ Lset, pairMult A d := by
    calc
      Lset.card = ∑ _d ∈ Lset, 1 := by simp
      _ ≤ ∑ d ∈ Lset, pairMult A d := Finset.sum_le_sum (fun d hd => hpos_ge1 d (Finset.mem_filter.mp hd).1)
  have hH_ge : Hset.card * (n + 1) ≤ ∑ d ∈ Hset, pairMult A d := by
    calc
      Hset.card * (n + 1) = ∑ _d ∈ Hset, (n + 1) := by simp
      _ ≤ ∑ d ∈ Hset, pairMult A d := Finset.sum_le_sum (fun d hd => (Finset.mem_filter.mp hd).2)
  have hk_eq : k = Lset.card + Hset.card := by
    dsimp [k]; rw [← hpart.2, Finset.card_union_of_disjoint hpart.1]
  have htot : 1 + (k - 1) * (n + 1) ≤ ∑ d ∈ posDistances A, pairMult A d := by
    rcases Nat.eq_zero_or_pos Lset.card with h0 | h1
    · have hH : Hset.card = k := by omega
      have hLe : Lset = ∅ := Finset.card_eq_zero.mp h0
      rw [hsum_split, hLe, Finset.sum_empty, zero_add]
      have hmul : 1 + (k - 1) * (n + 1) ≤ Hset.card * (n + 1) := by
        rw [hH]; zify [show 1 ≤ k by omega]; nlinarith
      linarith [hH_ge]
    · have hL1 : Lset.card = 1 := by omega
      have hH : Hset.card = k - 1 := by omega
      rw [hL1] at hL_ge
      rw [hH] at hH_ge
      linarith [hsum_split, hL_ge, hH_ge]
  have hpair : 2 * (1 + (k - 1) * (n + 1)) ≤ n * (n - 1) := by linarith
  by_contra hgt
  have hk_ge : n / 2 + 1 ≤ k := by omega
  have h1 : n - 1 ≤ 2 * (k - 1) := by omega
  zify [show 1 ≤ k by omega, show 1 ≤ n by omega] at h1 hpair
  nlinarith

/-- Theorem 2.4 (Counting Step for Even Polygons, `L(A) ≥ 3`):
If `A.card = 2 * m` (`4 ≤ m`) and `m + 1 ≤ (posDistances A).card`, then at least `3`
distances in `posDistances A` occur at most `2 * m` times (`3 ≤ L(A)`). -/
theorem even_polygon_low_mult_ge_three (A : Finset E2) (m : ℕ) (hm : 4 ≤ m)
    (hcard : A.card = 2 * m) (hk : m + 1 ≤ (posDistances A).card) :
    3 ≤ ((posDistances A).filter (fun d => pairMult A d ≤ 2 * m)).card := by
  have hsum := sum_pairMult_eq_choose A
  rw [hcard] at hsum
  set Lset := (posDistances A).filter (fun d => pairMult A d ≤ 2 * m)
  set Hset := (posDistances A).filter (fun d => 2 * m + 1 ≤ pairMult A d)
  have hpart : Disjoint Lset Hset ∧ Lset ∪ Hset = posDistances A := by
    refine ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega), ?_⟩
    ext d
    simp only [Lset, Hset, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hle : pairMult A d ≤ 2 * m
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, by omega⟩
  have hpos_ge1 : ∀ d ∈ posDistances A, 1 ≤ pairMult A d := by
    intro d hd
    rw [mem_posDistances_iff] at hd
    rcases hd with ⟨p, hp, q, hq, hne, rfl⟩
    have hfib : 2 ≤ (A.offDiag.filter (fun pq => dist pq.1 pq.2 = dist p q)).card := by
      have hsub : {(p, q), (q, p)} ⊆ A.offDiag.filter (fun pq => dist pq.1 pq.2 = dist p q) := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
        · simp [Finset.mem_offDiag, hp, hq, hne]
        · rw [Finset.mem_singleton.mp hx']; simp [Finset.mem_offDiag, hp, hq, hne.symm, dist_comm]
      have hcard2 : ({(p, q), (q, p)} : Finset (E2 × E2)).card = 2 := by
        rw [Finset.card_pair]; intro h; apply hne; exact congrArg Prod.fst h
      linarith [Finset.card_le_card hsub]
    dsimp [pairMult]; omega
  by_contra hlt
  have hL_le2 : Lset.card ≤ 2 := by omega
  have hsum_split : ∑ d ∈ posDistances A, pairMult A d =
      (∑ d ∈ Lset, pairMult A d) + (∑ d ∈ Hset, pairMult A d) := by
    rw [← hpart.2, Finset.sum_union hpart.1]
  have hL_ge : Lset.card ≤ ∑ d ∈ Lset, pairMult A d := by
    calc
      Lset.card = ∑ _d ∈ Lset, 1 := by simp
      _ ≤ ∑ d ∈ Lset, pairMult A d := Finset.sum_le_sum (fun d hd => hpos_ge1 d (Finset.mem_filter.mp hd).1)
  have hH_sum : Hset.card * (2 * m + 1) ≤ ∑ d ∈ Hset, pairMult A d := by
    calc
      Hset.card * (2 * m + 1) = ∑ _d ∈ Hset, (2 * m + 1) := by simp
      _ ≤ ∑ d ∈ Hset, pairMult A d := Finset.sum_le_sum (fun d hd => (Finset.mem_filter.mp hd).2)
  have hmin_sum : 2 + (m - 1) * (2 * m + 1) ≤ ∑ d ∈ posDistances A, pairMult A d := by
    have h1 : (m + 1 - Lset.card) ≤ Hset.card := by
      have : (posDistances A).card = Lset.card + Hset.card := by
        rw [← hpart.2, Finset.card_union_of_disjoint hpart.1]
      omega
    have h2 : Lset.card + (m + 1 - Lset.card) * (2 * m + 1) ≤ ∑ d ∈ posDistances A, pairMult A d := by
      have hmul : (m + 1 - Lset.card) * (2 * m + 1) ≤ Hset.card * (2 * m + 1) :=
        Nat.mul_le_mul_right _ h1
      linarith [hsum_split, hL_ge, hH_sum]
    have h3 : 2 + (m - 1) * (2 * m + 1) ≤ Lset.card + (m + 1 - Lset.card) * (2 * m + 1) := by
      rcases Nat.lt_trichotomy Lset.card 2 with h01 | h2eq | hgt2
      · have : Lset.card ≤ 1 := by omega
        have hstep : 1 * (2 * m + 1) ≤ (m + 1 - Lset.card - (m - 1)) * (2 * m + 1) := by
          apply Nat.mul_le_mul_right; omega
        zify [show m - 1 ≤ m + 1 - Lset.card by omega] at hstep ⊢
        nlinarith
      · rw [h2eq]; simp
      · omega
    exact le_trans h3 h2
  have h2m : 2 * (2 + (m - 1) * (2 * m + 1)) ≤ 2 * m * (2 * m - 1) := by linarith
  zify [show 1 ≤ m by omega, show 1 ≤ 2 * m by omega] at h2m
  nlinarith

/-- Conditional corollary completing the even-polygon case `n = 2 * m ≥ 8`:
combining Altman's lower bound (`m ≤ |posDistances A|`) and Fishburn's `k = m` uniqueness
(`|posDistances A| = m → 3 ≤ L(A)`, e.g. for regular `2m`-gons where all `m` distances
have multiplicity `≤ 2m`) with `even_polygon_low_mult_ge_three` yields `3 ≤ L(A)`. -/
theorem even_convex_polygon_conditional (A : Finset E2) (m : ℕ) (hm : 4 ≤ m)
    (hcard : A.card = 2 * m)
    (hAltman : m ≤ (posDistances A).card)
    (hFishburn : (posDistances A).card = m →
      3 ≤ ((posDistances A).filter (fun d => pairMult A d ≤ 2 * m)).card) :
    3 ≤ ((posDistances A).filter (fun d => pairMult A d ≤ 2 * m)).card := by
  rcases Nat.lt_or_eq_of_le hAltman with hgt | heq
  · exact even_polygon_low_mult_ge_three A m hm hcard hgt
  · exact hFishburn heq.symm

/-- Theorem 2.5.1 (Boundary Case `|L_1| = 3`, `|D(L_2)| ≥ m - 1`):
If `A.card = 2 * m + 1` (`2 ≤ m`) and `peelLayer A 1` determines at least `m - 1` distinct
distances, then `A` has at least `m + 1` distinct distances (ruling out any Part 1
counterexample by `counterexample_distance_ceiling`). -/
theorem layer_boundary_L1_three (A : Finset E2) (m : ℕ) (hm : 2 ≤ m)
    (_hcard : A.card = 2 * m + 1)
    (hL2_dist : m - 1 ≤ (posDistances (peelLayer A 1)).card) :
    m + 1 ≤ (posDistances A).card := by
  have hne : (posDistances (peelLayer A 1)).Nonempty :=
    Finset.card_pos.mp (by omega)
  let dmax := (posDistances (peelLayer A 1)).max' hne
  have hdmax_mem : dmax ∈ posDistances (peelLayer A 1) := Finset.max'_mem _ hne
  rw [mem_posDistances_iff] at hdmax_mem
  rcases hdmax_mem with ⟨p, hp, q, hq, _, hdmax_eq⟩
  obtain ⟨D, hD_sub, hD_card, hD_gt⟩ := no_d2_within_second_layer A hp hq
  have hL2_sub : posDistances (peelLayer A 1) ⊆ posDistances A := by
    intro d hd
    rw [mem_posDistances_iff] at hd ⊢
    rcases hd with ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, peelLayer_subset A 1 hx, y, peelLayer_subset A 1 hy, hxy, rfl⟩
  have hdisj : Disjoint (posDistances (peelLayer A 1)) D := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    have hle : d ≤ dmax := Finset.le_max' _ d hd₁
    have hgt : dmax < d := by rw [← hdmax_eq]; exact hD_gt d hd₂
    linarith
  have hunion : posDistances (peelLayer A 1) ∪ D ⊆ posDistances A :=
    Finset.union_subset hL2_sub hD_sub
  have hcard_le := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, hD_card] at hcard_le
  omega

end CountingAndEvenPolygons

section MinM2M3Counterexample

/-!
## 3. Explicit Infinite Family Refuting `min(m₂, m₃) ≤ n`

For every odd `m ≥ 7` and `1 ≤ s` with `2 * s < m`, we place:
- `L₁`: regular `m`-gon of radius `1` at angles `2π j / m`, `j = 0, ..., m - 1`,
- `L₂`: aligned regular `m`-gon of radius `r₂` at angles `2π j / m`, `j = 0, ..., m - 1`,
- `L₃`: inner aligned circular arc of `s` points at radius `ρ` and angles `2π k / m`, `k = 0, ..., s - 1`,

with `r₂` and `ρ` tuned so that `L₁ × L₂` cross-distances match `d₂` (at circular step `t = (m - 1)/2`)
and `d₃` (at step `t - 1`), and `L₁ × L₃` cross-distances at step `t` match `d₃`.
Then `|A| = 2m + s`, `m₁ = m ≤ n`, `m₂ = 3m > n`, and `m₃ = 2m + 2s > n`.
-/

private def circlePt (r θ : ℝ) : E2 := !₂[r * Real.cos θ, r * Real.sin θ]

private lemma norm_circlePt {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circlePt r θ‖ = r := by
  have hsq : ‖circlePt r θ‖ ^ 2 = r ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, circlePt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    have hsc := Real.sin_sq_add_cos_sq θ
    linear_combination r ^ 2 * hsc
  nlinarith only [hsq, hr, norm_nonneg (circlePt r θ)]

private lemma dist_circlePt_sq (r₁ r₂ θ₁ θ₂ : ℝ) :
    dist (circlePt r₁ θ₁) (circlePt r₂ θ₂) ^ 2 =
      r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * Real.cos (θ₁ - θ₂) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, circlePt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.dist_eq, sq_abs]
  have h1 := Real.sin_sq_add_cos_sq θ₁
  have h2 := Real.sin_sq_add_cos_sq θ₂
  have hsub := Real.cos_sub θ₁ θ₂
  linear_combination r₁ ^ 2 * h1 + r₂ ^ 2 * h2 + 2 * r₁ * r₂ * hsub

private def cdiff (m j₁ j₂ : ℕ) : ℕ :=
  min ((j₁ + m - j₂) % m) ((j₂ + m - j₁) % m)

private lemma cdiff_comm (m j₁ j₂ : ℕ) : cdiff m j₁ j₂ = cdiff m j₂ j₁ :=
  min_comm _ _

private lemma cdiff_eq_zero_iff {m j₁ j₂ : ℕ} (h₁ : j₁ < m) (h₂ : j₂ < m) :
    cdiff m j₁ j₂ = 0 ↔ j₁ = j₂ := by
  unfold cdiff
  rcases Nat.lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · have h1 : (j₁ + m - j₂) % m = j₁ + m - j₂ := Nat.mod_eq_of_lt (by omega)
    have h2 : (j₂ + m - j₁) % m = j₂ - j₁ := by
      rw [show j₂ + m - j₁ = (j₂ - j₁) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    constructor <;> omega
  · simp
  · have h1 : (j₁ + m - j₂) % m = j₁ - j₂ := by
      rw [show j₁ + m - j₂ = (j₁ - j₂) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 : (j₂ + m - j₁) % m = j₂ + m - j₁ := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    constructor <;> omega

private lemma cdiff_le_half {t j₁ j₂ : ℕ} (h₁ : j₁ < 2 * t + 1) (h₂ : j₂ < 2 * t + 1) :
    cdiff (2 * t + 1) j₁ j₂ ≤ t := by
  unfold cdiff
  set m := 2 * t + 1
  rcases Nat.lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · have h1 : (j₁ + m - j₂) % m = j₁ + m - j₂ := Nat.mod_eq_of_lt (by omega)
    have h2 : (j₂ + m - j₁) % m = j₂ - j₁ := by
      rw [show j₂ + m - j₁ = (j₂ - j₁) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    omega
  · simp
  · have h1 : (j₁ + m - j₂) % m = j₁ - j₂ := by
      rw [show j₁ + m - j₂ = (j₁ - j₂) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 : (j₂ + m - j₁) % m = j₂ + m - j₁ := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    omega

private lemma cos_angle_diff_eq_cdiff {m j₁ j₂ : ℕ} (hm : 0 < m) (h₁ : j₁ < m) (h₂ : j₂ < m) :
    Real.cos (2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ)) =
      Real.cos (2 * Real.pi * (cdiff m j₁ j₂ : ℝ) / (m : ℝ)) := by
  by_cases heq : j₁ = j₂
  · subst heq; simp [cdiff]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  unfold cdiff
  rcases Nat.lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · have h1 : (j₁ + m - j₂) % m = j₁ + m - j₂ := Nat.mod_eq_of_lt (by omega)
    have h2 : (j₂ + m - j₁) % m = j₂ - j₁ := by
      rw [show j₂ + m - j₁ = (j₂ - j₁) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    rcases le_total (j₁ + m - j₂) (j₂ - j₁) with hmin | hmin
    · rw [min_eq_left hmin]
      have hsub : (j₁ : ℝ) - (j₂ : ℝ) = ((j₁ + m - j₂ : ℕ) : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add]; ring
      have harg : 2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ) =
          2 * Real.pi * ((j₁ + m - j₂ : ℕ) : ℝ) / (m : ℝ) - 2 * Real.pi := by
        calc
          2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ)
              = 2 * Real.pi * ((j₁ : ℝ) - (j₂ : ℝ)) / (m : ℝ) := by ring
          _ = 2 * Real.pi * (((j₁ + m - j₂ : ℕ) : ℝ) - (m : ℝ)) / (m : ℝ) := by rw [hsub]
          _ = 2 * Real.pi * ((j₁ + m - j₂ : ℕ) : ℝ) / (m : ℝ) - 2 * Real.pi := by
              field_simp
      rw [harg, Real.cos_sub_two_pi]
    · rw [min_eq_right hmin]
      have hsub : (j₁ : ℝ) - (j₂ : ℝ) = -((j₂ - j₁ : ℕ) : ℝ) := by
        rw [Nat.cast_sub hlt.le]; ring
      have harg : 2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ) =
          -(2 * Real.pi * ((j₂ - j₁ : ℕ) : ℝ) / (m : ℝ)) := by
        calc
          2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ)
              = 2 * Real.pi * ((j₁ : ℝ) - (j₂ : ℝ)) / (m : ℝ) := by ring
          _ = -(2 * Real.pi * ((j₂ - j₁ : ℕ) : ℝ) / (m : ℝ)) := by rw [hsub]; ring
      rw [harg, Real.cos_neg]
  · exact False.elim (heq rfl)
  · have h1 : (j₁ + m - j₂) % m = j₁ - j₂ := by
      rw [show j₁ + m - j₂ = (j₁ - j₂) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 : (j₂ + m - j₁) % m = j₂ + m - j₁ := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    rcases le_total (j₁ - j₂) (j₂ + m - j₁) with hmin | hmin
    · rw [min_eq_left hmin]
      have hsub : (j₁ : ℝ) - (j₂ : ℝ) = ((j₁ - j₂ : ℕ) : ℝ) := by rw [Nat.cast_sub hgt.le]
      have harg : 2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ) =
          2 * Real.pi * ((j₁ - j₂ : ℕ) : ℝ) / (m : ℝ) := by
        calc
          2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ)
              = 2 * Real.pi * ((j₁ : ℝ) - (j₂ : ℝ)) / (m : ℝ) := by ring
          _ = 2 * Real.pi * ((j₁ - j₂ : ℕ) : ℝ) / (m : ℝ) := by rw [hsub]
      rw [harg]
    · rw [min_eq_right hmin]
      have hsub : (j₁ : ℝ) - (j₂ : ℝ) = (m : ℝ) - ((j₂ + m - j₁ : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add]; ring
      have harg : 2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ) =
          -(2 * Real.pi * ((j₂ + m - j₁ : ℕ) : ℝ) / (m : ℝ)) + 2 * Real.pi := by
        calc
          2 * Real.pi * (j₁ : ℝ) / (m : ℝ) - 2 * Real.pi * (j₂ : ℝ) / (m : ℝ)
              = 2 * Real.pi * ((j₁ : ℝ) - (j₂ : ℝ)) / (m : ℝ) := by ring
          _ = 2 * Real.pi * ((m : ℝ) - ((j₂ + m - j₁ : ℕ) : ℝ)) / (m : ℝ) := by rw [hsub]
          _ = -(2 * Real.pi * ((j₂ + m - j₁ : ℕ) : ℝ) / (m : ℝ)) + 2 * Real.pi := by
              field_simp; ring
      rw [harg, Real.cos_add_two_pi, Real.cos_neg]

private lemma cdiff_fiber_card {t k j₂ : ℕ} (hk1 : 1 ≤ k) (hkt : k ≤ t) (hj₂ : j₂ < 2 * t + 1) :
    ((Finset.range (2 * t + 1)).filter (fun j₁ => cdiff (2 * t + 1) j₁ j₂ = k)).card = 2 := by
  set m := 2 * t + 1
  let a := (j₂ + k) % m
  let b := (j₂ + m - k) % m
  have ha_lt : a < m := Nat.mod_lt _ (by omega)
  have hb_lt : b < m := Nat.mod_lt _ (by omega)
  have hab_ne : a ≠ b := by
    dsimp [a, b]
    intro heq
    have hmod : (j₂ + k) % m = (j₂ + m - k) % m := heq
    rcases lt_or_ge (j₂ + k) m with hlt1 | hge1 <;>
    rcases lt_or_ge (j₂ + m - k) m with hlt2 | hge2
    · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod; omega
    · rw [Nat.mod_eq_of_lt hlt1, show j₂ + m - k = (j₂ - k) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hmod; omega
    · rw [show j₂ + k = (j₂ + k - m) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt2] at hmod; omega
    · rw [show j₂ + k = (j₂ + k - m) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), show j₂ + m - k = (j₂ - k) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hmod; omega
  have hset : (Finset.range m).filter (fun j₁ => cdiff m j₁ j₂ = k) = {a, b} := by
    ext j₁
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hj₁, hcd⟩
      have hne : j₁ ≠ j₂ := by
        intro rfl
        have := (cdiff_eq_zero_iff hj₁ hj₂).mpr rfl
        omega
      unfold cdiff at hcd
      rcases Nat.lt_trichotomy j₁ j₂ with hlt | rfl | hgt
      · have h1 : (j₁ + m - j₂) % m = j₁ + m - j₂ := Nat.mod_eq_of_lt (by omega)
        have h2 : (j₂ + m - j₁) % m = j₂ - j₁ := by
          rw [show j₂ + m - j₁ = (j₂ - j₁) + m by omega, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1, h2] at hcd
        rcases le_total (j₁ + m - j₂) (j₂ - j₁) with hmin | hmin
        · rw [min_eq_left hmin] at hcd
          left; dsimp [a]; rw [show j₂ + k = j₁ + m by omega, Nat.add_mod_right]
          exact (Nat.mod_eq_of_lt hj₁).symm
        · rw [min_eq_right hmin] at hcd
          right; dsimp [b]; rw [show j₂ + m - k = j₁ + m by omega, Nat.add_mod_right]
          exact (Nat.mod_eq_of_lt hj₁).symm
      · exact False.elim (hne rfl)
      · have h1 : (j₁ + m - j₂) % m = j₁ - j₂ := by
          rw [show j₁ + m - j₂ = (j₁ - j₂) + m by omega, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        have h2 : (j₂ + m - j₁) % m = j₂ + m - j₁ := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2] at hcd
        rcases le_total (j₁ - j₂) (j₂ + m - j₁) with hmin | hmin
        · rw [min_eq_left hmin] at hcd
          left; dsimp [a]; rw [show j₂ + k = j₁ by omega]
          exact (Nat.mod_eq_of_lt hj₁).symm
        · rw [min_eq_right hmin] at hcd
          right; dsimp [b]; rw [show j₂ + m - k = j₁ by omega]
          exact (Nat.mod_eq_of_lt hj₁).symm
    · rintro (rfl | rfl)
      · refine ⟨ha_lt, ?_⟩
        have ha_cases : (a = j₂ + k ∧ j₂ + k < m) ∨ (a + m = j₂ + k ∧ m ≤ j₂ + k) := by
          dsimp [a]
          rcases lt_or_ge (j₂ + k) m with hlt | hge
          · exact Or.inl ⟨Nat.mod_eq_of_lt hlt, hlt⟩
          · refine Or.inr ⟨?_, hge⟩
            have hmod : (j₂ + k) % m = j₂ + k - m := by
              rw [Nat.mod_eq_sub_mod hge]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hmod]; omega
        unfold cdiff
        rcases ha_cases with ⟨ha_eq, _⟩ | ⟨ha_eq, _⟩
        · have h1 : (a + m - j₂) % m = k := by
            rw [show a + m - j₂ = k + m by omega, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          have h2 : (j₂ + m - a) % m = m - k := by
            rw [show j₂ + m - a = m - k by omega]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]; omega
        · have h1 : (a + m - j₂) % m = k := by
            rw [show a + m - j₂ = k by omega]
            exact Nat.mod_eq_of_lt (by omega)
          have h2 : (j₂ + m - a) % m = m - k := by
            rw [show j₂ + m - a = (m - k) + m by omega, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]; omega
      · refine ⟨hb_lt, ?_⟩
        have hb_cases : (b = j₂ + m - k ∧ j₂ < k) ∨ (b + k = j₂ ∧ k ≤ j₂) := by
          dsimp [b]
          rcases lt_or_ge j₂ k with hlt | hge
          · exact Or.inl ⟨Nat.mod_eq_of_lt (by omega), hlt⟩
          · refine Or.inr ⟨?_, hge⟩
            have hmod : (j₂ + m - k) % m = j₂ - k := by
              rw [Nat.mod_eq_sub_mod (by omega), show j₂ + m - k - m = j₂ - k by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hmod]; omega
        unfold cdiff
        rcases hb_cases with ⟨hb_eq, _⟩ | ⟨hb_eq, _⟩
        · have h1 : (b + m - j₂) % m = m - k := by
            rw [show b + m - j₂ = (m - k) + m by omega, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          have h2 : (j₂ + m - b) % m = k := by
            rw [show j₂ + m - b = k by omega]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]; omega
        · have h1 : (b + m - j₂) % m = m - k := by
            rw [show b + m - j₂ = m - k by omega]
            exact Nat.mod_eq_of_lt (by omega)
          have h2 : (j₂ + m - b) % m = k := by
            rw [show j₂ + m - b = k + m by omega, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]; omega
  rw [hset, Finset.card_pair hab_ne]

private lemma card_cdiff_product {t k : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range (2 * t + 1))
    (hk1 : 1 ≤ k) (hkt : k ≤ t) :
    ((Finset.range (2 * t + 1) ×ˢ S).filter (fun p => cdiff (2 * t + 1) p.1 p.2 = k)).card =
      2 * S.card := by
  set m := 2 * t + 1
  have hbij :
      ((Finset.range m ×ˢ S).filter (fun p => cdiff m p.1 p.2 = k)).card =
        ∑ j₂ ∈ S, ((Finset.range m).filter (fun j₁ => cdiff m j₁ j₂ = k)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hbij]
  have hconst : ∀ j₂ ∈ S,
      ((Finset.range m).filter (fun j₁ => cdiff m j₁ j₂ = k)).card = 2 := fun j₂ hj₂ =>
    cdiff_fiber_card hk1 hkt (Finset.mem_range.mp (hS hj₂))
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Half-sector angle `α(m) = π / (2 * m)`. -/
noncomputable def breakAlpha (m : ℕ) : ℝ := Real.pi / (2 * (m : ℝ))

/-- Outer-layer largest distance `d₁(m) = 2 * cos (π / (2 * m))`. -/
noncomputable def breakD1 (m : ℕ) : ℝ := 2 * Real.cos (breakAlpha m)

/-- Second-largest distance `d₂(m) = 2 * cos (3 * π / (2 * m))`. -/
noncomputable def breakD2 (m : ℕ) : ℝ := 2 * Real.cos (3 * breakAlpha m)

/-- Radius `r₂(m)` of the middle regular `m`-gon `L₂`. -/
noncomputable def breakR2 (m : ℕ) : ℝ :=
  -(Real.cos (2 * breakAlpha m)) +
    Real.sqrt ((Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1)

/-- Third-largest distance `d₃(m)`. -/
noncomputable def breakD3 (m : ℕ) : ℝ :=
  Real.sqrt (1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m))

/-- Radius `ρ(m)` of the innermost arc `L₃`. -/
noncomputable def breakRho (m : ℕ) : ℝ :=
  -(Real.cos (2 * breakAlpha m)) +
    Real.sqrt ((Real.cos (2 * breakAlpha m)) ^ 2 + (breakD3 m) ^ 2 - 1)

/-- The explicit `(2 * m + s)`-point construction for `Odd m`, `7 ≤ m`, `1 ≤ s`, `2 * s < m`. -/
noncomputable def breakSet (m s : ℕ) : Finset E2 :=
  let L1 := (Finset.range m).image (fun j : ℕ => circlePt 1 (2 * Real.pi * (j : ℝ) / (m : ℝ)))
  let L2 := (Finset.range m).image (fun j : ℕ => circlePt (breakR2 m) (2 * Real.pi * (j : ℝ) / (m : ℝ)))
  let L3 := (Finset.range s).image (fun k : ℕ => circlePt (breakRho m) (2 * Real.pi * (k : ℝ) / (m : ℝ)))
  L1 ∪ L2 ∪ L3

private lemma sin_breakAlpha_bounds {m : ℕ} (hm : 7 ≤ m) :
    0 < Real.sin (breakAlpha m) ∧ Real.sin (breakAlpha m) < 9 / 40 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hα_pos : 0 < breakAlpha m := by unfold breakAlpha; positivity
  have hα_lt : breakAlpha m < 9 / 40 := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    unfold breakAlpha
    have hle : Real.pi / (2 * (m : ℝ)) ≤ Real.pi / 14 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith only [hmR])
    linarith only [hle, hpi]
  have hsin_lt : Real.sin (breakAlpha m) < breakAlpha m := Real.sin_lt hα_pos
  have hsin_pos : 0 < Real.sin (breakAlpha m) :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos (by linarith only [hα_lt, Real.pi_gt_three])
  exact ⟨hsin_pos, lt_trans hsin_lt hα_lt⟩

private lemma breakParams_identities {m : ℕ} (hm : 7 ≤ m) :
    let x := (Real.sin (breakAlpha m)) ^ 2
    0 < x ∧ x < 81 / 1600 ∧
    Real.cos (2 * breakAlpha m) = 1 - 2 * x ∧
    Real.cos (6 * breakAlpha m) = 1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3 ∧
    (breakD1 m) ^ 2 = 4 * (1 - x) ∧
    (breakD2 m) ^ 2 = 4 - 36 * x + 96 * x ^ 2 - 64 * x ^ 3 ∧
    0 < (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1 ∧
    1 - 8 * x - 2 * x ^ 2 < breakR2 m ∧ breakR2 m < 1 - 8 * x ∧
    (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (2 * breakAlpha m) + 1 = (breakD2 m) ^ 2 ∧
    2 - 17 * x < breakD3 m ∧
    (breakD3 m) ^ 2 < 4 - 68 * x + 448 * x ^ 2 - 832 * x ^ 3 + 320 * x ^ 4 + 128 * x ^ 5 ∧
    0 < (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD3 m) ^ 2 - 1 ∧
    0 < breakRho m ∧ breakRho m < 1 - 9 * x ∧
    (breakRho m) ^ 2 + 2 * (breakRho m) * Real.cos (2 * breakAlpha m) + 1 = (breakD3 m) ^ 2 ∧
    breakRho m < breakR2 m ∧ breakR2 m < 1 ∧
    breakR2 m + breakRho m < breakD3 m ∧
    2 * Real.cos (5 * breakAlpha m) < breakD3 m ∧
    2 * (breakR2 m) * Real.cos (breakAlpha m) < breakD3 m ∧
    breakD3 m < breakD2 m ∧ breakD2 m < breakD1 m := by
  intro x
  obtain ⟨hs_pos, hs_lt⟩ := sin_breakAlpha_bounds hm
  have hx_pos : 0 < x := sq_pos_of_pos hs_pos
  have hx_lt : x < 81 / 1600 := by
    have : x < (9 / 40) ^ 2 := sq_lt_sq' (by linarith) hs_lt
    linarith
  have hc2 : Real.cos (2 * breakAlpha m) = 1 - 2 * x := by
    rw [Real.cos_two_mul']
    have hsc := Real.sin_sq_add_cos_sq (breakAlpha m)
    dsimp [x]; linarith only [hsc]
  have hc6 : Real.cos (6 * breakAlpha m) = 1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3 := by
    rw [show 6 * breakAlpha m = 3 * (2 * breakAlpha m) by ring, Real.cos_three_mul, hc2]
    ring
  have hd1_sq : (breakD1 m) ^ 2 = 4 * (1 - x) := by
    unfold breakD1
    have hsc := Real.sin_sq_add_cos_sq (breakAlpha m)
    have hxdef : (Real.sin (breakAlpha m)) ^ 2 = x := rfl
    nlinarith only [hsc, hxdef]
  have hd2_sq : (breakD2 m) ^ 2 = 4 - 36 * x + 96 * x ^ 2 - 64 * x ^ 3 := by
    unfold breakD2
    rw [Real.cos_three_mul]
    have hsc := Real.sin_sq_add_cos_sq (breakAlpha m)
    have hcos_sq : Real.cos (breakAlpha m) ^ 2 = 1 - x := by
      dsimp [x]; linarith only [hsc]
    calc
      (2 * (4 * Real.cos (breakAlpha m) ^ 3 - 3 * Real.cos (breakAlpha m))) ^ 2
          = 4 * Real.cos (breakAlpha m) ^ 2 * (4 * Real.cos (breakAlpha m) ^ 2 - 3) ^ 2 := by ring
      _ = 4 * (1 - x) * (4 * (1 - x) - 3) ^ 2 := by rw [hcos_sq]
      _ = 4 - 36 * x + 96 * x ^ 2 - 64 * x ^ 3 := by ring
  have hdisc1_eq :
      (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1 =
        4 - 40 * x + 100 * x ^ 2 - 64 * x ^ 3 := by
    rw [hc2, hd2_sq]; ring
  have hdisc1_lo : (2 - 10 * x - 2 * x ^ 2) ^ 2 <
      (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1 := by
    rw [hdisc1_eq]
    have hpoly : (4 - 40 * x + 100 * x ^ 2 - 64 * x ^ 3) - (2 - 10 * x - 2 * x ^ 2) ^ 2 =
        x ^ 2 * (8 - 104 * x - 4 * x ^ 2) := by ring
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx_pos
    have hpos_fac : 0 < 8 - 104 * x - 4 * x ^ 2 := by nlinarith only [hx_pos, hx_lt]
    linarith only [hpoly, mul_pos hx2 hpos_fac]
  have hdisc1_hi : (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1 < (2 - 10 * x) ^ 2 := by
    rw [hdisc1_eq]
    have hx3 : 0 < x ^ 3 := pow_pos hx_pos 3
    linarith only [hx3, show (2 - 10 * x) ^ 2 - (4 - 40 * x + 100 * x ^ 2 - 64 * x ^ 3) = 64 * x ^ 3 by ring]
  have hdisc1_pos : 0 < (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1 := by
    linarith only [sq_nonneg (2 - 10 * x - 2 * x ^ 2), hdisc1_lo]
  have hsqrt1_lo : 2 - 10 * x - 2 * x ^ 2 <
      Real.sqrt ((Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1) := by
    rw [← Real.sqrt_sq (by nlinarith only [hx_pos, hx_lt] : 0 ≤ 2 - 10 * x - 2 * x ^ 2)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hdisc1_lo
  have hsqrt1_hi :
      Real.sqrt ((Real.cos (2 * breakAlpha m)) ^ 2 + (breakD2 m) ^ 2 - 1) < 2 - 10 * x := by
    rw [← Real.sqrt_sq (by linarith only [hx_lt] : 0 ≤ 2 - 10 * x)]
    exact Real.sqrt_lt_sqrt hdisc1_pos.le hdisc1_hi
  have hr2_lo : 1 - 8 * x - 2 * x ^ 2 < breakR2 m := by
    dsimp only [breakR2]; linarith only [hc2, hsqrt1_lo]
  have hr2_hi : breakR2 m < 1 - 8 * x := by
    dsimp only [breakR2]; linarith only [hc2, hsqrt1_hi]
  have hr2_pos : 0 < breakR2 m := by nlinarith only [hx_pos, hx_lt, hr2_lo]
  have hr2_lt1 : breakR2 m < 1 := by linarith only [hx_pos, hr2_hi]
  have hr2_quad :
      (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (2 * breakAlpha m) + 1 = (breakD2 m) ^ 2 := by
    unfold breakR2
    set c := Real.cos (2 * breakAlpha m)
    set D := c ^ 2 + (breakD2 m) ^ 2 - 1
    have hD : 0 ≤ D := hdisc1_pos.le
    calc
      (-c + Real.sqrt D) ^ 2 + 2 * (-c + Real.sqrt D) * c + 1
          = (Real.sqrt D) ^ 2 - c ^ 2 + 1 := by ring
      _ = D - c ^ 2 + 1 := by rw [Real.sq_sqrt hD]
      _ = (breakD2 m) ^ 2 := by dsimp [D]; ring
  have hd3_arg_eq :
      1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) =
        (breakD2 m) ^ 2 + 2 * (breakR2 m) * (Real.cos (6 * breakAlpha m) - Real.cos (2 * breakAlpha m)) := by
    linarith only [hr2_quad]
  have hcdiff_neg : Real.cos (6 * breakAlpha m) - Real.cos (2 * breakAlpha m) < 0 := by
    rw [hc6, hc2]
    have hpoly : (1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x) =
        -16 * x * (1 - x) * (1 - 2 * x) := by ring
    have h1 : 0 < 1 - x := by linarith only [hx_lt]
    have h2 : 0 < 1 - 2 * x := by linarith only [hx_lt]
    have hprod : 0 < x * (1 - x) * (1 - 2 * x) := mul_pos (mul_pos hx_pos h1) h2
    linarith only [hpoly, hprod]
  have hd3_arg_lo :
      4 - 68 * x + 448 * x ^ 2 - 896 * x ^ 3 + 512 * x ^ 4 <
        1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) := by
    rw [hd3_arg_eq, hd2_sq, hc6, hc2]
    have hcneg : (1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x) < 0 := by
      rw [← hc6, ← hc2]; exact hcdiff_neg
    have hmul : 2 * (1 - 8 * x) * ((1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x)) <
        2 * (breakR2 m) * ((1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x)) :=
      mul_lt_mul_of_neg_right (by linarith only [hr2_hi]) hcneg
    have hid :
        (4 - 36 * x + 96 * x ^ 2 - 64 * x ^ 3) +
          2 * (1 - 8 * x) * ((1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x)) =
          4 - 68 * x + 448 * x ^ 2 - 896 * x ^ 3 + 512 * x ^ 4 := by ring
    linarith only [hmul, hid]
  have hd3_arg_hi :
      1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) <
        4 - 68 * x + 448 * x ^ 2 - 832 * x ^ 3 + 320 * x ^ 4 + 128 * x ^ 5 := by
    rw [hd3_arg_eq, hd2_sq, hc6, hc2]
    have hcneg : (1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x) < 0 := by
      rw [← hc6, ← hc2]; exact hcdiff_neg
    have hmul : 2 * (breakR2 m) * ((1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x)) <
        2 * (1 - 8 * x - 2 * x ^ 2) * ((1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x)) :=
      mul_lt_mul_of_neg_right (by linarith only [hr2_lo]) hcneg
    have hid :
        (4 - 36 * x + 96 * x ^ 2 - 64 * x ^ 3) +
          2 * (1 - 8 * x - 2 * x ^ 2) * ((1 - 18 * x + 48 * x ^ 2 - 32 * x ^ 3) - (1 - 2 * x)) =
          4 - 68 * x + 448 * x ^ 2 - 832 * x ^ 3 + 320 * x ^ 4 + 128 * x ^ 5 := by ring
    linarith only [hmul, hid]
  have hd3_sq_lo : (2 - 17 * x) ^ 2 < 1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) := by
    have hdiff : (4 - 68 * x + 448 * x ^ 2 - 896 * x ^ 3 + 512 * x ^ 4) - (2 - 17 * x) ^ 2 =
        x ^ 2 * (159 - 896 * x + 512 * x ^ 2) := by ring
    have hfac : 0 < 159 - 896 * x + 512 * x ^ 2 := by linarith only [hx_lt, sq_nonneg x]
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx_pos
    linarith only [hdiff, mul_pos hx2 hfac, hd3_arg_lo]
  have hd3_arg_pos : 0 < 1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) := by
    linarith only [sq_nonneg (2 - 17 * x), hd3_sq_lo]
  have hd3_sq : (breakD3 m) ^ 2 = 1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) :=
    Real.sq_sqrt hd3_arg_pos.le
  have hd3_lo : 2 - 17 * x < breakD3 m := by
    unfold breakD3
    rw [← Real.sqrt_sq (by linarith only [hx_lt] : 0 ≤ 2 - 17 * x)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hd3_sq_lo
  have hd3_hi : (breakD3 m) ^ 2 < 4 - 68 * x + 448 * x ^ 2 - 832 * x ^ 3 + 320 * x ^ 4 + 128 * x ^ 5 := by
    rw [hd3_sq]; exact hd3_arg_hi
  have hd3_gt1 : 1 < breakD3 m := by linarith only [hx_lt, hd3_lo]
  have hdisc2_pos : 0 < (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD3 m) ^ 2 - 1 := by
    nlinarith only [sq_nonneg (Real.cos (2 * breakAlpha m)), hd3_gt1]
  have hdisc2_gt_c : (Real.cos (2 * breakAlpha m)) ^ 2 <
      (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD3 m) ^ 2 - 1 := by
    nlinarith only [hd3_gt1]
  have hrho_pos : 0 < breakRho m := by
    unfold breakRho
    have hcpos : 0 ≤ Real.cos (2 * breakAlpha m) := by rw [hc2]; linarith only [hx_lt]
    have hlt := Real.sqrt_lt_sqrt (sq_nonneg _) hdisc2_gt_c
    rw [Real.sqrt_sq hcpos] at hlt
    linarith only [hlt]
  have hdisc2_hi :
      (Real.cos (2 * breakAlpha m)) ^ 2 + (breakD3 m) ^ 2 - 1 < (2 - 11 * x) ^ 2 := by
    have hsub :
        (2 - 11 * x) ^ 2 - ((1 - 2 * x) ^ 2 +
          (4 - 68 * x + 448 * x ^ 2 - 832 * x ^ 3 + 320 * x ^ 4 + 128 * x ^ 5) - 1) =
          x * (28 - 331 * x + 832 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4) := by ring
    have h1 : 0 < 28 - 331 * x := by linarith only [hx_lt]
    have h2 : 0 ≤ 832 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4 := by
      rw [show 832 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4 =
        x ^ 2 * (832 - 320 * x - 128 * x ^ 2) by ring]
      exact mul_nonneg (sq_nonneg x) (by nlinarith only [hx_pos, hx_lt])
    have hpos : 0 < x * (28 - 331 * x + 832 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4) :=
      mul_pos hx_pos (by linarith only [h1, h2])
    rw [hc2]
    linarith only [hsub, hpos, hd3_hi]
  have hrho_hi : breakRho m < 1 - 9 * x := by
    dsimp only [breakRho]
    have hlt := Real.sqrt_lt_sqrt hdisc2_pos.le hdisc2_hi
    rw [Real.sqrt_sq (by linarith only [hx_lt] : 0 ≤ 2 - 11 * x)] at hlt
    linarith only [hc2, hlt]
  have hrho_quad :
      (breakRho m) ^ 2 + 2 * (breakRho m) * Real.cos (2 * breakAlpha m) + 1 = (breakD3 m) ^ 2 := by
    unfold breakRho
    set c := Real.cos (2 * breakAlpha m)
    set D := c ^ 2 + (breakD3 m) ^ 2 - 1
    have hD : 0 ≤ D := hdisc2_pos.le
    calc
      (-c + Real.sqrt D) ^ 2 + 2 * (-c + Real.sqrt D) * c + 1
          = (Real.sqrt D) ^ 2 - c ^ 2 + 1 := by ring
      _ = D - c ^ 2 + 1 := by rw [Real.sq_sqrt hD]
      _ = (breakD3 m) ^ 2 := by dsimp [D]; ring
  have hrho_lt_r2 : breakRho m < breakR2 m := by nlinarith only [hx_pos, hx_lt, hrho_hi, hr2_lo]
  have hsum_lt_d3 : breakR2 m + breakRho m < breakD3 m := by linarith only [hr2_hi, hrho_hi, hd3_lo]
  -- Check 2 * cos(5 * alpha) < d3:
  have ho3_lt_d3 : 2 * Real.cos (5 * breakAlpha m) < breakD3 m := by
    have hs5 : Real.sin (5 * breakAlpha m) =
        Real.sin (breakAlpha m) * (5 - 20 * x + 16 * x ^ 2) := by
      have h5 : 5 * breakAlpha m = 2 * breakAlpha m + 3 * breakAlpha m := by ring
      rw [h5, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul', Real.sin_three_mul,
        Real.cos_three_mul]
      have hsc := Real.sin_sq_add_cos_sq (breakAlpha m)
      have hc2' : Real.cos (breakAlpha m) ^ 2 = 1 - x := by dsimp [x]; linarith only [hsc]
      have hcos2 : Real.cos (breakAlpha m) ^ 2 - Real.sin (breakAlpha m) ^ 2 = 1 - 2 * x := by
        dsimp [x]; linarith only [hsc]
      rw [hcos2]
      calc
        2 * Real.sin (breakAlpha m) * Real.cos (breakAlpha m) *
            (4 * Real.cos (breakAlpha m) ^ 3 - 3 * Real.cos (breakAlpha m)) +
          (1 - 2 * x) *
            (3 * Real.sin (breakAlpha m) - 4 * Real.sin (breakAlpha m) ^ 3)
            = Real.sin (breakAlpha m) *
                (2 * Real.cos (breakAlpha m) ^ 2 * (4 * Real.cos (breakAlpha m) ^ 2 - 3) +
                  (1 - 2 * x) * (3 - 4 * x)) := by
              dsimp [x]; ring
        _ = Real.sin (breakAlpha m) * (2 * (1 - x) * (4 * (1 - x) - 3) + (1 - 2 * x) * (3 - 4 * x)) := by
              rw [hc2']
        _ = Real.sin (breakAlpha m) * (5 - 20 * x + 16 * x ^ 2) := by ring
    have ho3_sq : (2 * Real.cos (5 * breakAlpha m)) ^ 2 =
        4 - 100 * x + 800 * x ^ 2 - 2240 * x ^ 3 + 2560 * x ^ 4 - 1024 * x ^ 5 := by
      have hsc := Real.sin_sq_add_cos_sq (5 * breakAlpha m)
      have hs5sq : Real.sin (5 * breakAlpha m) ^ 2 = x * (5 - 20 * x + 16 * x ^ 2) ^ 2 := by
        rw [hs5]; dsimp [x]; ring
      calc
        (2 * Real.cos (5 * breakAlpha m)) ^ 2
            = 4 * (1 - Real.sin (5 * breakAlpha m) ^ 2) := by linarith only [hsc]
        _ = 4 * (1 - x * (5 - 20 * x + 16 * x ^ 2) ^ 2) := by rw [hs5sq]
        _ = 4 - 100 * x + 800 * x ^ 2 - 2240 * x ^ 3 + 2560 * x ^ 4 - 1024 * x ^ 5 := by ring
    have hdiff_pos : (2 * Real.cos (5 * breakAlpha m)) ^ 2 < (breakD3 m) ^ 2 := by
      rw [ho3_sq, hd3_sq]
      have hpoly :
          (4 - 68 * x + 448 * x ^ 2 - 896 * x ^ 3 + 512 * x ^ 4) -
            (4 - 100 * x + 800 * x ^ 2 - 2240 * x ^ 3 + 2560 * x ^ 4 - 1024 * x ^ 5) =
            x * (32 - 352 * x + 1344 * x ^ 2 - 2048 * x ^ 3 + 1024 * x ^ 4) := by ring
      have h32 : 0 < 32 - 352 * x := by linarith only [hx_lt]
      have h1344 : 0 ≤ 1344 * x ^ 2 - 2048 * x ^ 3 + 1024 * x ^ 4 := by
        rw [show 1344 * x ^ 2 - 2048 * x ^ 3 + 1024 * x ^ 4 =
          x ^ 2 * (1344 - 2048 * x + 1024 * x ^ 2) by ring]
        exact mul_nonneg (sq_nonneg x) (by nlinarith only [hx_lt, sq_nonneg x])
      have hbig : 0 < x * (32 - 352 * x + 1344 * x ^ 2 - 2048 * x ^ 3 + 1024 * x ^ 4) :=
        mul_pos hx_pos (by linarith only [h32, h1344])
      linarith only [hpoly, hbig, hd3_arg_lo]
    have hd3_nonneg : 0 ≤ breakD3 m := Real.sqrt_nonneg _
    nlinarith only [hdiff_pos, hd3_nonneg]
  -- Check 2 * r2 * cos(alpha) < d3 using the exact linear-in-r2 identity:
  have hi1_lt_d3 : 2 * (breakR2 m) * Real.cos (breakAlpha m) < breakD3 m := by
    have hc1_sq : Real.cos (breakAlpha m) ^ 2 = 1 - x := by
      have hsc := Real.sin_sq_add_cos_sq (breakAlpha m); dsimp [x]; linarith only [hsc]
    have hi1_sq : (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2 =
        4 * (1 - x) * (breakR2 m) ^ 2 := by
      calc
        (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2
            = 4 * Real.cos (breakAlpha m) ^ 2 * (breakR2 m) ^ 2 := by ring
        _ = 4 * (1 - x) * (breakR2 m) ^ 2 := by rw [hc1_sq]
    have hr2_sq_eq : (breakR2 m) ^ 2 = (breakD2 m) ^ 2 - 1 - 2 * Real.cos (2 * breakAlpha m) * (breakR2 m) := by
      linarith only [hr2_quad]
    have hdiff_eq :
        (breakD3 m) ^ 2 - (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2 =
          (-8 + 120 * x - 432 * x ^ 2 + 576 * x ^ 3 - 256 * x ^ 4) +
            (8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3) * (breakR2 m) := by
      rw [hd3_sq, hd3_arg_eq, hi1_sq, hr2_sq_eq, hd2_sq, hc6, hc2]
      ring
    have hB_pos : 0 < 8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3 := by
      have hfac : 8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3 =
          8 * (1 - x) * (1 - 2 * x) * (1 - 4 * x) := by ring
      rw [hfac]
      have h1 : 0 < 1 - x := by linarith only [hx_lt]
      have h2 : 0 < 1 - 2 * x := by linarith only [hx_lt]
      have h4 : 0 < 1 - 4 * x := by linarith only [hx_lt]
      exact mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) h4
    have hL_pos :
        0 < (-8 + 120 * x - 432 * x ^ 2 + 576 * x ^ 3 - 256 * x ^ 4) +
          (8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3) * (1 - 8 * x - 2 * x ^ 2) := by
      have hpoly :
          (-8 + 120 * x - 432 * x ^ 2 + 576 * x ^ 3 - 256 * x ^ 4) +
            (8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3) * (1 - 8 * x - 2 * x ^ 2) =
            x ^ 2 * (112 - 272 * x + 32 * x ^ 2 + 128 * x ^ 3) := by ring
      have h112 : 0 < 112 - 272 * x := by linarith only [hx_lt]
      have hsum : 0 < 112 - 272 * x + 32 * x ^ 2 + 128 * x ^ 3 := by
        linarith only [h112, sq_nonneg x, pow_nonneg hx_pos.le 3]
      rw [hpoly]
      exact mul_pos (sq_pos_of_pos hx_pos) hsum
    have hmul :
        (8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3) * (1 - 8 * x - 2 * x ^ 2) <
          (8 - 56 * x + 112 * x ^ 2 - 64 * x ^ 3) * (breakR2 m) :=
      mul_lt_mul_of_pos_left hr2_lo hB_pos
    have hsq_lt : (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2 < (breakD3 m) ^ 2 := by
      linarith only [hdiff_eq, hL_pos, hmul]
    have hd3_nonneg : 0 ≤ breakD3 m := Real.sqrt_nonneg _
    nlinarith only [hsq_lt, hd3_nonneg]
  have hd3_lt_d2 : breakD3 m < breakD2 m := by
    have hpoly :
        (4 - 36 * x + 96 * x ^ 2 - 64 * x ^ 3) -
          (4 - 68 * x + 448 * x ^ 2 - 832 * x ^ 3 + 320 * x ^ 4 + 128 * x ^ 5) =
          x * (32 - 352 * x + 768 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4) := by ring
    have h32 : 0 < 32 - 352 * x := by linarith only [hx_lt]
    have h768 : 0 ≤ 768 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4 := by
      rw [show 768 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4 =
        x ^ 2 * (768 - 320 * x - 128 * x ^ 2) by ring]
      exact mul_nonneg (sq_nonneg x) (by nlinarith only [hx_pos, hx_lt])
    have hbig : 0 < x * (32 - 352 * x + 768 * x ^ 2 - 320 * x ^ 3 - 128 * x ^ 4) :=
      mul_pos hx_pos (by linarith only [h32, h768])
    have hd2_nonneg : 0 ≤ breakD2 m := by
      unfold breakD2
      have hα_pos : 0 < breakAlpha m := by unfold breakAlpha; positivity
      have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h3α : 3 * breakAlpha m ≤ Real.pi / 2 := by
        unfold breakAlpha
        have hle : 3 * (Real.pi / (2 * (m : ℝ))) ≤ 3 * (Real.pi / 14) := by
          gcongr; linarith only [hmR]
        linarith only [hle, Real.pi_pos]
      exact mul_nonneg (by norm_num)
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hα_pos, Real.pi_pos], h3α⟩)
    have hsq_lt : (breakD3 m) ^ 2 < (breakD2 m) ^ 2 := by
      rw [hd2_sq]
      linarith only [hpoly, hbig, hd3_hi]
    nlinarith only [hsq_lt, hd2_nonneg, Real.sqrt_nonneg (1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m))]
  have hd2_lt_d1 : breakD2 m < breakD1 m := by
    unfold breakD2 breakD1
    have hα_pos : 0 < breakAlpha m := by unfold breakAlpha; positivity
    have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h3α_le : 3 * breakAlpha m ≤ Real.pi := by
      unfold breakAlpha
      have hle : 3 * (Real.pi / (2 * (m : ℝ))) ≤ 3 * (Real.pi / 14) := by
        gcongr; linarith only [hmR]
      linarith only [hle, Real.pi_pos]
    have hcos : Real.cos (3 * breakAlpha m) < Real.cos (breakAlpha m) :=
      Real.strictAntiOn_cos ⟨hα_pos.le, by linarith only [hα_pos, h3α_le]⟩
        ⟨by linarith only [hα_pos], h3α_le⟩ (by linarith only [hα_pos])
    linarith only [hcos]
  exact ⟨hx_pos, hx_lt, hc2, hc6, hd1_sq, hd2_sq, hdisc1_pos, hr2_lo, hr2_hi, hr2_quad,
    hd3_lo, hd3_hi, hdisc2_pos, hrho_pos, hrho_hi, hrho_quad, hrho_lt_r2, hr2_lt1, hsum_lt_d3,
    ho3_lt_d3, hi1_lt_d3, hd3_lt_d2, hd2_lt_d1⟩

private lemma circlePt_range_injOn {m : ℕ} (hm : 7 ≤ m) {r : ℝ} (hr : 0 < r) :
    Set.InjOn (fun j : ℕ => circlePt r (2 * Real.pi * (j : ℝ) / (m : ℝ))) (Finset.range m) := by
  intro j₁ hj₁ j₂ hj₂ heq
  dsimp only at heq
  rw [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
  have hd : dist (circlePt r (2 * Real.pi * (j₁ : ℝ) / (m : ℝ)))
      (circlePt r (2 * Real.pi * (j₂ : ℝ) / (m : ℝ))) ^ 2 = 0 := by
    rw [heq, dist_self]; norm_num
  rw [dist_circlePt_sq, cos_angle_diff_eq_cdiff (by omega) hj₁ hj₂] at hd
  have hcos1 : Real.cos (2 * Real.pi * (cdiff m j₁ j₂ : ℝ) / (m : ℝ)) = 1 := by
    have : 2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * (cdiff m j₁ j₂ : ℝ) / (m : ℝ))) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with hr0 | hc0
    · nlinarith
    · linarith
  by_contra hne
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨_, _⟩
  have hm_odd_or : cdiff m j₁ j₂ < m := by
    unfold cdiff
    have : (j₁ + m - j₂) % m < m := Nat.mod_lt _ (by omega)
    exact lt_of_le_of_lt (min_le_left _ _) this
  have hcd_pos : 0 < cdiff m j₁ j₂ :=
    Nat.pos_of_ne_zero (mt (cdiff_eq_zero_iff hj₁ hj₂).mp hne)
  -- Since `cdiff` could equal `m / 2` in general, use `2 * π * cdiff / m ∈ (0, 2π)`:
  -- wait, actually `min a b ≤ m / 2 < m`, and `2π * cdiff / m ≤ π`!
  have hcd_le : 2 * cdiff m j₁ j₂ ≤ m := by
    unfold cdiff
    rcases Nat.lt_trichotomy j₁ j₂ with hlt | rfl | hgt
    · have h1 : (j₁ + m - j₂) % m = j₁ + m - j₂ := Nat.mod_eq_of_lt (by omega)
      have h2 : (j₂ + m - j₁) % m = j₂ - j₁ := by
        rw [show j₂ + m - j₁ = (j₂ - j₁) + m by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2]; omega
    · exact False.elim (hne rfl)
    · have h1 : (j₁ + m - j₂) % m = j₁ - j₂ := by
        rw [show j₁ + m - j₂ = (j₁ - j₂) + m by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      have h2 : (j₂ + m - j₁) % m = j₂ + m - j₁ := Nat.mod_eq_of_lt (by omega)
      rw [h1, h2]; omega
  have harg_pos : 0 < 2 * Real.pi * (cdiff m j₁ j₂ : ℝ) / (m : ℝ) := by
    have : (0 : ℝ) < cdiff m j₁ j₂ := by exact_mod_cast hcd_pos
    positivity
  have harg_le : 2 * Real.pi * (cdiff m j₁ j₂ : ℝ) / (m : ℝ) ≤ Real.pi := by
    have hmR : (0 : ℝ) < m := by positivity
    have hleR : (2 : ℝ) * (cdiff m j₁ j₂ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcd_le
    rw [div_le_iff₀ hmR]
    nlinarith [Real.pi_pos]
  have hlt : Real.cos (2 * Real.pi * (cdiff m j₁ j₂ : ℝ) / (m : ℝ)) < Real.cos 0 :=
    Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨harg_pos.le, harg_le⟩ harg_pos
  rw [Real.cos_zero, hcos1] at hlt
  linarith

/-- Exact cardinality of `breakSet m s`: `|L₁ ∪ L₂ ∪ L₃| = 2 * m + s`. -/
theorem breakSet_card {m s : ℕ} (hm : 7 ≤ m) (hs : s ≤ m) :
    (breakSet m s).card = 2 * m + s := by
  have hp := breakParams_identities hm
  rcases hp with ⟨_, _, _, _, _, _, _, hr2_lo, hr2_hi, _, _, _, _, hrho_pos, _, _, hrho_lt_r2,
    hr2_lt1, _⟩
  have hr2_pos : 0 < breakR2 m := by
    have hx_lt : (Real.sin (breakAlpha m)) ^ 2 < 81 / 1600 := (breakParams_identities hm).2.1
    nlinarith
  have hS1 : ((Finset.range m).image (fun j : ℕ => circlePt 1 (2 * Real.pi * (j : ℝ) / (m : ℝ)))).card = m := by
    rw [Finset.card_image_of_injOn (circlePt_range_injOn hm one_pos), Finset.card_range]
  have hS2 : ((Finset.range m).image (fun j : ℕ => circlePt (breakR2 m) (2 * Real.pi * (j : ℝ) / (m : ℝ)))).card = m := by
    rw [Finset.card_image_of_injOn (circlePt_range_injOn hm hr2_pos), Finset.card_range]
  have hS3 : ((Finset.range s).image (fun k : ℕ => circlePt (breakRho m) (2 * Real.pi * (k : ℝ) / (m : ℝ)))).card = s := by
    have hinj : Set.InjOn (fun k : ℕ => circlePt (breakRho m) (2 * Real.pi * (k : ℝ) / (m : ℝ))) (Finset.range s) :=
      (circlePt_range_injOn hm hrho_pos).mono (Finset.coe_subset.mpr (Finset.range_mono hs))
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hnorm : ∀ {r₁ r₂ : ℝ}, 0 ≤ r₁ → 0 ≤ r₂ → r₁ ≠ r₂ →
      ∀ θ₁ θ₂, circlePt r₁ θ₁ ≠ circlePt r₂ θ₂ := by
    intro r₁ r₂ hr1 hr2 hne θ₁ θ₂ heq
    apply hne
    have := congrArg norm heq
    rwa [norm_circlePt hr1, norm_circlePt hr2] at this
  have h12 : Disjoint
      ((Finset.range m).image (fun j : ℕ => circlePt 1 (2 * Real.pi * (j : ℝ) / (m : ℝ))))
      ((Finset.range m).image (fun j : ℕ => circlePt (breakR2 m) (2 * Real.pi * (j : ℝ) / (m : ℝ)))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨j₁, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨j₂, _, heq⟩
    exact hnorm one_pos.le hr2_pos.le hr2_lt1.ne' _ _ heq.symm
  have h123 : Disjoint
      (((Finset.range m).image (fun j : ℕ => circlePt 1 (2 * Real.pi * (j : ℝ) / (m : ℝ)))) ∪
        ((Finset.range m).image (fun j : ℕ => circlePt (breakR2 m) (2 * Real.pi * (j : ℝ) / (m : ℝ)))))
      ((Finset.range s).image (fun k : ℕ => circlePt (breakRho m) (2 * Real.pi * (k : ℝ) / (m : ℝ)))) := by
    rw [Finset.disjoint_left]
    intro p hp12 hp3
    rcases Finset.mem_image.mp hp3 with ⟨k, _, hk⟩
    rcases Finset.mem_union.mp hp12 with hp1 | hp2
    · rcases Finset.mem_image.mp hp1 with ⟨j, _, rfl⟩
      exact hnorm one_pos.le hrho_pos.le (by linarith) _ _ hk.symm
    · rcases Finset.mem_image.mp hp2 with ⟨j, _, rfl⟩
      exact hnorm hr2_pos.le hrho_pos.le hrho_lt_r2.ne' _ _ hk.symm
  unfold breakSet
  rw [Finset.card_union_of_disjoint h123, Finset.card_union_of_disjoint h12, hS1, hS2, hS3]
  omega

private lemma cos_two_pi_div_odd_t {t : ℕ} (ht : 3 ≤ t) :
    Real.cos (2 * Real.pi * (t : ℝ) / ((2 * t + 1 : ℕ) : ℝ)) =
      -Real.cos (2 * breakAlpha (2 * t + 1)) := by
  have hmR : ((2 * t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have harg : 2 * Real.pi * (t : ℝ) / ((2 * t + 1 : ℕ) : ℝ) =
      Real.pi - 2 * breakAlpha (2 * t + 1) := by
    unfold breakAlpha
    push_cast
    field_simp
    ring
  rw [harg, Real.cos_pi_sub]

private lemma cos_two_pi_div_odd_t_sub_one {t : ℕ} (ht : 3 ≤ t) :
    Real.cos (2 * Real.pi * ((t - 1 : ℕ) : ℝ) / ((2 * t + 1 : ℕ) : ℝ)) =
      -Real.cos (6 * breakAlpha (2 * t + 1)) := by
  have hmR : ((2 * t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have hsub : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have harg : 2 * Real.pi * ((t - 1 : ℕ) : ℝ) / ((2 * t + 1 : ℕ) : ℝ) =
      Real.pi - 6 * breakAlpha (2 * t + 1) := by
    rw [hsub]
    unfold breakAlpha
    push_cast
    field_simp
    ring
  rw [harg, Real.cos_pi_sub]

private lemma two_mul_one_sub_cos_odd {t k : ℕ} (_hk1 : 1 ≤ k) (hkt : k ≤ t) :
    2 * (1 - Real.cos (2 * Real.pi * (k : ℝ) / ((2 * t + 1 : ℕ) : ℝ))) =
      (2 * Real.cos (((2 * t + 1 - 2 * k : ℕ) : ℝ) * breakAlpha (2 * t + 1))) ^ 2 := by
  have hmR : ((2 * t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsub : ((2 * t + 1 - 2 * k : ℕ) : ℝ) = 2 * (t : ℝ) + 1 - 2 * (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have harg : Real.pi * (k : ℝ) / ((2 * t + 1 : ℕ) : ℝ) =
      Real.pi / 2 - ((2 * t + 1 - 2 * k : ℕ) : ℝ) * breakAlpha (2 * t + 1) := by
    rw [hsub]
    unfold breakAlpha
    push_cast
    field_simp
    ring
  have hhalf : 2 * Real.pi * (k : ℝ) / ((2 * t + 1 : ℕ) : ℝ) =
      2 * (Real.pi * (k : ℝ) / ((2 * t + 1 : ℕ) : ℝ)) := by ring
  rw [hhalf, Real.cos_two_mul', harg, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hsc := Real.sin_sq_add_cos_sq (((2 * t + 1 - 2 * k : ℕ) : ℝ) * breakAlpha (2 * t + 1))
  nlinarith only [hsc]

/-- Exact top-three distances (`d₁ > d₂ > d₃ > 0`) and exact multiplicities
`m₁ = m`, `m₂ = 3 * m`, `m₃ = 2 * m + 2 * s` in `breakSet m s` for odd `m ≥ 7`, `1 ≤ s`, `2 * s < m`. -/
theorem breakSet_top_three_distances {m s : ℕ} (hm_odd : Odd m) (hm : 7 ≤ m)
    (hs1 : 1 ≤ s) (hsm : 2 * s < m) :
    let A := breakSet m s
    0 < breakD3 m ∧ breakD3 m < breakD2 m ∧ breakD2 m < breakD1 m ∧
    (∀ d ∈ posDistances A,
      d = breakD1 m ∨ d = breakD2 m ∨ d = breakD3 m ∨ d < breakD3 m) ∧
    pairMult A (breakD1 m) = m ∧
    pairMult A (breakD2 m) = 3 * m ∧
    pairMult A (breakD3 m) = 2 * m + 2 * s ∧
    pairMult A (breakD1 m) ≤ A.card ∧
    A.card < pairMult A (breakD2 m) ∧
    A.card < pairMult A (breakD3 m) := by
  intro A
  rcases hm_odd with ⟨t, rfl⟩
  have ht : 3 ≤ t := by omega
  set m := 2 * t + 1
  have hcardA : A.card = 2 * m + s := breakSet_card hm (by omega)
  obtain ⟨hx_pos, hx_lt, hc2, hc6, hd1_sq, hd2_sq, hdisc1_pos, hr2_lo, hr2_hi, hr2_quad,
    hd3_lo, hd3_hi, hdisc2_pos, hrho_pos, hrho_hi, hrho_quad, hrho_lt_r2, hr2_lt1, hsum_lt_d3,
    ho3_lt_d3, hi1_lt_d3, hd3_lt_d2, hd2_lt_d1⟩ := breakParams_identities hm
  have hr2_pos : 0 < breakR2 m := by nlinarith
  have hd3_pos : 0 < breakD3 m := by nlinarith
  have hd2_pos : 0 < breakD2 m := by linarith
  have hd1_pos : 0 < breakD1 m := by linarith
  -- Layer finsets and pairwise disjointness
  let θ : ℕ → ℝ := fun j : ℕ => 2 * Real.pi * (j : ℝ) / (m : ℝ)
  let L₁ := (Finset.range m).image (fun j : ℕ => circlePt 1 (θ j))
  let L₂ := (Finset.range m).image (fun j : ℕ => circlePt (breakR2 m) (θ j))
  let L₃ := (Finset.range s).image (fun k : ℕ => circlePt (breakRho m) (θ k))
  have hA_eq : A = L₁ ∪ L₂ ∪ L₃ := by
    dsimp only [A, L₁, L₂, L₃, θ, breakSet, m]
  have hnorm_pt : ∀ p ∈ A,
      (p ∈ L₁ ↔ ‖p‖ = 1) ∧ (p ∈ L₂ ↔ ‖p‖ = breakR2 m) ∧ (p ∈ L₃ ↔ ‖p‖ = breakRho m) := by
    intro p hp
    have hnorm_of : ∀ {r : ℝ} (hr : 0 ≤ r) (S : Finset ℕ),
        p ∈ S.image (fun j => circlePt r (θ j)) → ‖p‖ = r := by
      intro r hr S hmem
      rcases Finset.mem_image.mp hmem with ⟨j, _, rfl⟩
      exact norm_circlePt hr _
    rcases Finset.mem_union.mp hp with hp12 | hp3
    · rcases Finset.mem_union.mp hp12 with hp1 | hp2
      · have hn := hnorm_of one_pos.le (Finset.range m) hp1
        refine ⟨⟨fun _ => hn, fun _ => hp1⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;>
          [exact absurd (hn.symm.trans (hnorm_of hr2_pos.le _ h)) hr2_lt1.ne';
           exact absurd (hn.symm.trans h) hr2_lt1.ne';
           exact absurd (hn.symm.trans (hnorm_of hrho_pos.le _ h)) (by linarith);
           exact absurd (hn.symm.trans h) (by linarith)]
      · have hn := hnorm_of hr2_pos.le (Finset.range m) hp2
        refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun _ => hn, fun _ => hp2⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;>
          [exact absurd (hn.symm.trans (hnorm_of one_pos.le _ h)) hr2_lt1.ne;
           exact absurd (hn.symm.trans h) hr2_lt1.ne;
           exact absurd (hn.symm.trans (hnorm_of hrho_pos.le _ h)) hrho_lt_r2.ne';
           exact absurd (hn.symm.trans h) hrho_lt_r2.ne']
    · have hn := hnorm_of hrho_pos.le (Finset.range s) hp3
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun _ => hn, fun _ => hp3⟩⟩ <;>
        [exact absurd (hn.symm.trans (hnorm_of one_pos.le _ h)) (by linarith);
         exact absurd (hn.symm.trans h) (by linarith);
         exact absurd (hn.symm.trans (hnorm_of hr2_pos.le _ h)) hrho_lt_r2.ne;
         exact absurd (hn.symm.trans h) hrho_lt_r2.ne]
  -- Exact pairwise distance formulas on each of the 9 layer pairs
  have hdist_L1_L1 : ∀ {j₁ j₂ : ℕ}, j₁ < m → j₂ < m → j₁ ≠ j₂ →
      let k := cdiff m j₁ j₂
      (k = t → dist (circlePt 1 (θ j₁)) (circlePt 1 (θ j₂)) = breakD1 m) ∧
      (k = t - 1 → dist (circlePt 1 (θ j₁)) (circlePt 1 (θ j₂)) = breakD2 m) ∧
      (k ≤ t - 2 → dist (circlePt 1 (θ j₁)) (circlePt 1 (θ j₂)) < breakD3 m) := by
    intro j₁ j₂ hj1 hj2 hne k
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (mt (cdiff_eq_zero_iff hj1 hj2).mp hne)
    have hkt : k ≤ t := cdiff_le_half hj1 hj2
    have hsq : dist (circlePt 1 (θ j₁)) (circlePt 1 (θ j₂)) ^ 2 =
        (2 * Real.cos (((m - 2 * k : ℕ) : ℝ) * breakAlpha m)) ^ 2 := by
      rw [dist_circlePt_sq, cos_angle_diff_eq_cdiff (by omega) hj1 hj2]
      have h2 := two_mul_one_sub_cos_odd hk1 hkt
      linarith only [h2]
    have hα_pos : 0 < breakAlpha m := by unfold breakAlpha; positivity
    have hm_alpha : (m : ℝ) * breakAlpha m = Real.pi / 2 := by
      unfold breakAlpha
      have : (m : ℝ) ≠ 0 := by positivity
      field_simp
    refine ⟨fun hkt' => ?_, fun hkt' => ?_, fun hkt' => ?_⟩
    · rw [hkt', show m - 2 * t = 1 by omega, Nat.cast_one, one_mul] at hsq
      unfold breakD1
      have hd1' : 0 < 2 * Real.cos (breakAlpha m) := hd1_pos
      nlinarith only [hsq, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt 1 (θ j₂)), hd1']
    · rw [hkt', show m - 2 * (t - 1) = 3 by omega] at hsq
      unfold breakD2
      have h3cast : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [h3cast] at hsq
      have hd2' : 0 < 2 * Real.cos (3 * breakAlpha m) := hd2_pos
      nlinarith only [hsq, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt 1 (θ j₂)), hd2']
    · have h5_le : 5 ≤ m - 2 * k := by omega
      have h5_leR : (5 : ℝ) * breakAlpha m ≤ ((m - 2 * k : ℕ) : ℝ) * breakAlpha m := by
        have : (5 : ℝ) ≤ ((m - 2 * k : ℕ) : ℝ) := by exact_mod_cast h5_le
        exact mul_le_mul_of_nonneg_right this hα_pos.le
      have hm_le : ((m - 2 * k : ℕ) : ℝ) * breakAlpha m ≤ Real.pi / 2 := by
        have : ((m - 2 * k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.sub_le m (2 * k))
        calc
          ((m - 2 * k : ℕ) : ℝ) * breakAlpha m ≤ (m : ℝ) * breakAlpha m :=
            mul_le_mul_of_nonneg_right this hα_pos.le
          _ = Real.pi / 2 := hm_alpha
      have hcos_nonneg : 0 ≤ Real.cos (((m - 2 * k : ℕ) : ℝ) * breakAlpha m) := by
        have hnn : 0 ≤ ((m - 2 * k : ℕ) : ℝ) * breakAlpha m := by positivity
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hnn, Real.pi_pos], hm_le⟩
      have hcos_le : Real.cos (((m - 2 * k : ℕ) : ℝ) * breakAlpha m) ≤ Real.cos (5 * breakAlpha m) :=
        Real.strictAntiOn_cos.antitoneOn ⟨by positivity, by linarith only [h5_leR, hm_le, Real.pi_pos]⟩
          ⟨by positivity, by linarith only [hm_le, Real.pi_pos]⟩ h5_leR
      have hsq_le : dist (circlePt 1 (θ j₁)) (circlePt 1 (θ j₂)) ^ 2 ≤
          (2 * Real.cos (5 * breakAlpha m)) ^ 2 := by
        have hpos1 : 0 ≤ 2 * Real.cos (((m - 2 * k : ℕ) : ℝ) * breakAlpha m) := by linarith only [hcos_nonneg]
        have hpos2 : 0 ≤ 2 * Real.cos (5 * breakAlpha m) := by linarith only [hcos_nonneg, hcos_le]
        nlinarith only [hsq, hcos_le, hpos1, hpos2]
      have hdist_le : dist (circlePt 1 (θ j₁)) (circlePt 1 (θ j₂)) ≤ 2 * Real.cos (5 * breakAlpha m) := by
        have hpos2 : 0 ≤ 2 * Real.cos (5 * breakAlpha m) := by linarith only [hcos_nonneg, hcos_le]
        nlinarith only [hsq_le, hpos2, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt 1 (θ j₂))]
      exact lt_of_le_of_lt hdist_le ho3_lt_d3
  have hdist_L1_L2 : ∀ {j₁ j₂ : ℕ}, j₁ < m → j₂ < m →
      let k := cdiff m j₁ j₂
      (k = t → dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) = breakD2 m) ∧
      (k = t - 1 → dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) = breakD3 m) ∧
      (k ≤ t - 2 → dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) < breakD3 m) := by
    intro j₁ j₂ hj1 hj2 k
    have hsq : dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ^ 2 =
        1 + (breakR2 m) ^ 2 - 2 * (breakR2 m) * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) := by
      rw [dist_circlePt_sq, cos_angle_diff_eq_cdiff (by omega) hj1 hj2]; ring
    have hd3_sq_eq : (breakD3 m) ^ 2 =
        1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) := by
      have harg_nn : 0 ≤ 1 + (breakR2 m) ^ 2 + 2 * (breakR2 m) * Real.cos (6 * breakAlpha m) := by
        by_contra hlt
        push Not at hlt
        have hz : breakD3 m = 0 := by
          unfold breakD3
          exact Real.sqrt_eq_zero_of_nonpos hlt.le
        linarith only [hz, hd3_pos]
      unfold breakD3
      exact Real.sq_sqrt harg_nn
    refine ⟨fun hkt' => ?_, fun hkt' => ?_, fun hkt' => ?_⟩
    · rw [hkt', cos_two_pi_div_odd_t ht] at hsq
      have hsq2 : dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ^ 2 = (breakD2 m) ^ 2 := by
        linarith only [hsq, hr2_quad]
      nlinarith only [hsq2, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt (breakR2 m) (θ j₂)), hd2_pos]
    · rw [hkt', cos_two_pi_div_odd_t_sub_one ht] at hsq
      have hsq3 : dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ^ 2 = (breakD3 m) ^ 2 := by
        linarith only [hsq, hd3_sq_eq]
      nlinarith only [hsq3, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt (breakR2 m) (θ j₂)), hd3_pos]
    · have hk_lt : k < t - 1 := by omega
      have harg1 : 0 ≤ 2 * Real.pi * (k : ℝ) / (m : ℝ) := by positivity
      have hmR : (0 : ℝ) < (m : ℝ) := by positivity
      have harg_lt : 2 * Real.pi * (k : ℝ) / (m : ℝ) <
          2 * Real.pi * ((t - 1 : ℕ) : ℝ) / (m : ℝ) := by
        gcongr
      have harg2_le : 2 * Real.pi * ((t - 1 : ℕ) : ℝ) / (m : ℝ) ≤ Real.pi := by
        rw [div_le_iff₀ hmR]
        have hle : 2 * ((t - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * (t - 1) ≤ m)
        nlinarith only [Real.pi_pos, hle]
      have hcos_gt : Real.cos (2 * Real.pi * ((t - 1 : ℕ) : ℝ) / (m : ℝ)) <
          Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) :=
        Real.strictAntiOn_cos ⟨harg1, by linarith only [harg_lt, harg2_le]⟩ ⟨by positivity, harg2_le⟩ harg_lt
      rw [cos_two_pi_div_odd_t_sub_one ht] at hcos_gt
      have hmul : 2 * (breakR2 m) * (-Real.cos (6 * breakAlpha m)) <
          2 * (breakR2 m) * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) :=
        mul_lt_mul_of_pos_left hcos_gt (by linarith only [hr2_pos])
      have hlt_sq : dist (circlePt 1 (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ^ 2 < (breakD3 m) ^ 2 := by
        linarith only [hsq, hd3_sq_eq, hmul]
      nlinarith only [hlt_sq, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt (breakR2 m) (θ j₂)), hd3_pos]
  have hdist_L1_L3 : ∀ {j₁ j₃ : ℕ}, j₁ < m → j₃ < m →
      let k := cdiff m j₁ j₃
      (k = t → dist (circlePt 1 (θ j₁)) (circlePt (breakRho m) (θ j₃)) = breakD3 m) ∧
      (k ≤ t - 1 → dist (circlePt 1 (θ j₁)) (circlePt (breakRho m) (θ j₃)) < breakD3 m) := by
    intro j₁ j₃ hj1 hj3 k
    have hsq : dist (circlePt 1 (θ j₁)) (circlePt (breakRho m) (θ j₃)) ^ 2 =
        1 + (breakRho m) ^ 2 - 2 * (breakRho m) * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) := by
      rw [dist_circlePt_sq, cos_angle_diff_eq_cdiff (by omega) hj1 hj3]; ring
    refine ⟨fun hkt' => ?_, fun hkt' => ?_⟩
    · rw [hkt', cos_two_pi_div_odd_t ht] at hsq
      have hsq3 : dist (circlePt 1 (θ j₁)) (circlePt (breakRho m) (θ j₃)) ^ 2 = (breakD3 m) ^ 2 := by
        linarith only [hsq, hrho_quad]
      nlinarith only [hsq3, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt (breakRho m) (θ j₃)), hd3_pos]
    · have hk_lt : k < t := by omega
      have harg1 : 0 ≤ 2 * Real.pi * (k : ℝ) / (m : ℝ) := by positivity
      have hmR : (0 : ℝ) < (m : ℝ) := by positivity
      have harg_lt : 2 * Real.pi * (k : ℝ) / (m : ℝ) < 2 * Real.pi * (t : ℝ) / (m : ℝ) := by
        gcongr
      have harg2_le : 2 * Real.pi * (t : ℝ) / (m : ℝ) ≤ Real.pi := by
        rw [div_le_iff₀ hmR]
        have hle : 2 * (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * t ≤ m)
        nlinarith only [Real.pi_pos, hle]
      have hcos_gt : Real.cos (2 * Real.pi * (t : ℝ) / (m : ℝ)) <
          Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) :=
        Real.strictAntiOn_cos ⟨harg1, by linarith only [harg_lt, harg2_le]⟩ ⟨by positivity, harg2_le⟩ harg_lt
      rw [cos_two_pi_div_odd_t ht] at hcos_gt
      have hmul : 2 * (breakRho m) * (-Real.cos (2 * breakAlpha m)) <
          2 * (breakRho m) * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) :=
        mul_lt_mul_of_pos_left hcos_gt (by linarith only [hrho_pos])
      have hlt_sq : dist (circlePt 1 (θ j₁)) (circlePt (breakRho m) (θ j₃)) ^ 2 < (breakD3 m) ^ 2 := by
        linarith only [hsq, hrho_quad, hmul]
      nlinarith only [hlt_sq, dist_nonneg (x := circlePt 1 (θ j₁)) (y := circlePt (breakRho m) (θ j₃)), hd3_pos]
  have hdist_L2_L2 : ∀ {j₁ j₂ : ℕ}, j₁ < m → j₂ < m →
      dist (circlePt (breakR2 m) (θ j₁)) (circlePt (breakR2 m) (θ j₂)) < breakD3 m := by
    intro j₁ j₂ hj1 hj2
    by_cases heq : j₁ = j₂
    · subst heq; rw [dist_self]; exact hd3_pos
    · set k := cdiff m j₁ j₂
      have hkt : k ≤ t := cdiff_le_half hj1 hj2
      have hmR : (0 : ℝ) < (m : ℝ) := by positivity
      have harg1 : 0 ≤ 2 * Real.pi * (k : ℝ) / (m : ℝ) := by positivity
      have harg_le : 2 * Real.pi * (k : ℝ) / (m : ℝ) ≤ 2 * Real.pi * (t : ℝ) / (m : ℝ) := by
        gcongr
      have harg2_le : 2 * Real.pi * (t : ℝ) / (m : ℝ) ≤ Real.pi := by
        rw [div_le_iff₀ hmR]
        have hle : 2 * (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * t ≤ m)
        nlinarith only [Real.pi_pos, hle]
      have hcos_ge : Real.cos (2 * Real.pi * (t : ℝ) / (m : ℝ)) ≤
          Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) :=
        Real.strictAntiOn_cos.antitoneOn ⟨harg1, by linarith only [harg_le, harg2_le]⟩
          ⟨by positivity, harg2_le⟩ harg_le
      rw [cos_two_pi_div_odd_t ht, hc2] at hcos_ge
      have hmul : 2 * (breakR2 m) ^ 2 * (-(1 - 2 * (Real.sin (breakAlpha m)) ^ 2)) ≤
          2 * (breakR2 m) ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hcos_ge (by positivity)
      have hsq_step : dist (circlePt (breakR2 m) (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ^ 2 =
          2 * (breakR2 m) ^ 2 - 2 * (breakR2 m) ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) := by
        rw [dist_circlePt_sq, cos_angle_diff_eq_cdiff (by omega) hj1 hj2]; ring
      have hsc := Real.sin_sq_add_cos_sq (breakAlpha m)
      have hsq_rhs : (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2 =
          2 * (breakR2 m) ^ 2 - 2 * (breakR2 m) ^ 2 * (-(1 - 2 * (Real.sin (breakAlpha m)) ^ 2)) := by
        have hc1_sq : Real.cos (breakAlpha m) ^ 2 = 1 - (Real.sin (breakAlpha m)) ^ 2 := by
          linarith only [hsc]
        calc
          (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2
              = 4 * (breakR2 m) ^ 2 * Real.cos (breakAlpha m) ^ 2 := by ring
          _ = 4 * (breakR2 m) ^ 2 * (1 - (Real.sin (breakAlpha m)) ^ 2) := by rw [hc1_sq]
          _ = 2 * (breakR2 m) ^ 2 - 2 * (breakR2 m) ^ 2 * (-(1 - 2 * (Real.sin (breakAlpha m)) ^ 2)) := by ring
      have hsq : dist (circlePt (breakR2 m) (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ^ 2 ≤
          (2 * (breakR2 m) * Real.cos (breakAlpha m)) ^ 2 := by
        linarith only [hsq_step, hsq_rhs, hmul]
      have hle_i1 : dist (circlePt (breakR2 m) (θ j₁)) (circlePt (breakR2 m) (θ j₂)) ≤
          2 * (breakR2 m) * Real.cos (breakAlpha m) := by
        have hα_pos : 0 < breakAlpha m := by unfold breakAlpha; positivity
        have hα_le : breakAlpha m ≤ Real.pi / 2 := by
          unfold breakAlpha
          have hmR' : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [Real.pi_pos, hmR']
        have hc_nonneg : 0 ≤ Real.cos (breakAlpha m) :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hα_pos, Real.pi_pos], hα_le⟩
        have hr_nonneg : 0 ≤ 2 * (breakR2 m) * Real.cos (breakAlpha m) :=
          mul_nonneg (by linarith only [hr2_pos]) hc_nonneg
        nlinarith only [hsq, hr_nonneg, dist_nonneg (x := circlePt (breakR2 m) (θ j₁)) (y := circlePt (breakR2 m) (θ j₂))]
      exact lt_of_le_of_lt hle_i1 hi1_lt_d3
  have hdist_small : ∀ {p q : E2}, p ∈ L₂ ∪ L₃ → q ∈ L₃ → dist p q < breakD3 m := by
    intro p q hp hq
    have hnp : ‖p‖ ≤ breakR2 m := by
      rcases Finset.mem_union.mp hp with hp2 | hp3
      · rw [(hnorm_pt p (Finset.mem_union_left _ (Finset.mem_union_right _ hp2))).2.1.mp hp2]
      · rw [(hnorm_pt p (Finset.mem_union_right _ hp3)).2.2.mp hp3]; exact hrho_lt_r2.le
    have hnq : ‖q‖ = breakRho m := (hnorm_pt q (Finset.mem_union_right _ hq)).2.2.mp hq
    have htri : dist p q ≤ ‖p‖ + ‖q‖ := by
      rw [dist_eq_norm]
      calc
        ‖p - q‖ ≤ ‖p‖ + ‖-q‖ := norm_add_le p (-q)
        _ = ‖p‖ + ‖q‖ := by rw [norm_neg]
    linarith
  -- Part 1: every d ∈ posDistances A satisfies d = d₁ ∨ d = d₂ ∨ d = d₃ ∨ d < d₃
  have hpos_class : ∀ d ∈ posDistances A,
      d = breakD1 m ∨ d = breakD2 m ∨ d = breakD3 m ∨ d < breakD3 m := by
    intro d hd
    rw [mem_posDistances_iff] at hd
    rcases hd with ⟨p, hp, q, hq, hne, rfl⟩
    have hstep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        dist x y = breakD1 m ∨ dist x y = breakD2 m ∨ dist x y = breakD3 m ∨ dist x y < breakD3 m := by
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hx12 | hx3
      · rcases Finset.mem_union.mp hx12 with hx1 | hx2
        · rcases Finset.mem_image.mp hx1 with ⟨j₁, hj1, rfl⟩
          rw [Finset.mem_range] at hj1
          rcases Finset.mem_union.mp hy with hy12 | hy3
          · rcases Finset.mem_union.mp hy12 with hy1 | hy2
            · rcases Finset.mem_image.mp hy1 with ⟨j₂, hj2, rfl⟩
              rw [Finset.mem_range] at hj2
              have hne_j : j₁ ≠ j₂ := by rintro rfl; exact hxy rfl
              have h1 := hdist_L1_L1 hj1 hj2 hne_j
              have hk1 : 1 ≤ cdiff m j₁ j₂ :=
                Nat.pos_of_ne_zero (mt (cdiff_eq_zero_iff hj1 hj2).mp hne_j)
              have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
              rcases eq_or_lt_of_le hkt with h_t | h_lt
              · exact Or.inl (h1.1 h_t)
              · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
                · exact Or.inr (Or.inl (h1.2.1 h_tm1))
                · exact Or.inr (Or.inr (Or.inr (h1.2.2 (by omega))))
            · rcases Finset.mem_image.mp hy2 with ⟨j₂, hj2, rfl⟩
              rw [Finset.mem_range] at hj2
              have h1 := hdist_L1_L2 hj1 hj2
              have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
              rcases eq_or_lt_of_le hkt with h_t | h_lt
              · exact Or.inr (Or.inl (h1.1 h_t))
              · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
                · exact Or.inr (Or.inr (Or.inl (h1.2.1 h_tm1)))
                · exact Or.inr (Or.inr (Or.inr (h1.2.2 (by omega))))
          · rcases Finset.mem_image.mp hy3 with ⟨j₃, hj3, rfl⟩
            rw [Finset.mem_range] at hj3
            have h1 := hdist_L1_L3 hj1 (by omega : j₃ < m)
            have hkt : cdiff m j₁ j₃ ≤ t := cdiff_le_half hj1 (by omega : j₃ < m)
            rcases eq_or_lt_of_le hkt with h_t | h_lt
            · exact Or.inr (Or.inr (Or.inl (h1.1 h_t)))
            · exact Or.inr (Or.inr (Or.inr (h1.2 (by omega))))
        · rcases Finset.mem_union.mp hy with hy12 | hy3
          · rcases Finset.mem_union.mp hy12 with hy1 | hy2
            · rcases Finset.mem_image.mp hx2 with ⟨j₂, hj2, rfl⟩
              rcases Finset.mem_image.mp hy1 with ⟨j₁, hj1, rfl⟩
              rw [Finset.mem_range] at hj1 hj2
              rw [dist_comm]
              have h1 := hdist_L1_L2 hj1 hj2
              have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
              rcases eq_or_lt_of_le hkt with h_t | h_lt
              · exact Or.inr (Or.inl (h1.1 h_t))
              · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
                · exact Or.inr (Or.inr (Or.inl (h1.2.1 h_tm1)))
                · exact Or.inr (Or.inr (Or.inr (h1.2.2 (by omega))))
            · rcases Finset.mem_image.mp hx2 with ⟨j₁, hj1, rfl⟩
              rcases Finset.mem_image.mp hy2 with ⟨j₂, hj2, rfl⟩
              rw [Finset.mem_range] at hj1 hj2
              exact Or.inr (Or.inr (Or.inr (hdist_L2_L2 hj1 hj2)))
          · exact Or.inr (Or.inr (Or.inr (hdist_small (Finset.mem_union_left _ hx2) hy3)))
      · rcases Finset.mem_union.mp hy with hy12 | hy3
        · rcases Finset.mem_union.mp hy12 with hy1 | hy2
          · rcases Finset.mem_image.mp hx3 with ⟨j₃, hj3, rfl⟩
            rcases Finset.mem_image.mp hy1 with ⟨j₁, hj1, rfl⟩
            rw [Finset.mem_range] at hj1 hj3
            rw [dist_comm]
            have h1 := hdist_L1_L3 hj1 (by omega : j₃ < m)
            have hkt : cdiff m j₁ j₃ ≤ t := cdiff_le_half hj1 (by omega : j₃ < m)
            rcases eq_or_lt_of_le hkt with h_t | h_lt
            · exact Or.inr (Or.inr (Or.inl (h1.1 h_t)))
            · exact Or.inr (Or.inr (Or.inr (h1.2 (by omega))))
          · rw [dist_comm]
            exact Or.inr (Or.inr (Or.inr (hdist_small (Finset.mem_union_left _ hy2) hx3)))
        · exact Or.inr (Or.inr (Or.inr (hdist_small (Finset.mem_union_right _ hx3) hy3)))
    exact hstep p hp q hq hne
  -- Helper: counting ordered pairs in `L_a × L_b` via `card_cdiff_product`
  have hinj1 : Set.InjOn (fun j => circlePt 1 (θ j)) (Finset.range m) :=
    circlePt_range_injOn hm one_pos
  have hinj2 : Set.InjOn (fun j => circlePt (breakR2 m) (θ j)) (Finset.range m) :=
    circlePt_range_injOn hm hr2_pos
  have hinj3 : Set.InjOn (fun j => circlePt (breakRho m) (θ j)) (Finset.range s) :=
    (circlePt_range_injOn hm hrho_pos).mono (Finset.coe_subset.mpr (Finset.range_mono (by omega)))
  have hcount_L1_L1 : ∀ {k : ℕ} (hk1 : 1 ≤ k) (hkt : k ≤ t),
      ((L₁ ×ˢ L₁).filter (fun pq => cdiff m 0 0 = 0 ∧ True)).card = 0 ∨ True := fun _ _ => Or.inr trivial
  have hprod_card : ∀ {r₁ r₂ : ℝ} {S₁ S₂ : Finset ℕ}
      (hinjA : Set.InjOn (fun j => circlePt r₁ (θ j)) S₁)
      (hinjB : Set.InjOn (fun j => circlePt r₂ (θ j)) S₂)
      (P : ℕ × ℕ → Prop) [DecidablePred P]
      (Q : E2 × E2 → Prop) [DecidablePred Q]
      (hequiv : ∀ j₁ ∈ S₁, ∀ j₂ ∈ S₂, (P (j₁, j₂) ↔ Q (circlePt r₁ (θ j₁), circlePt r₂ (θ j₂)))),
      ((S₁.image (fun j => circlePt r₁ (θ j)) ×ˢ S₂.image (fun j => circlePt r₂ (θ j))).filter Q).card =
        ((S₁ ×ˢ S₂).filter P).card := by
    intro r₁ r₂ S₁ S₂ hinjA hinjB P _ Q _ hequiv
    symm
    apply Finset.card_bij (fun (jj : ℕ × ℕ) _ => (circlePt r₁ (θ jj.1), circlePt r₂ (θ jj.2)))
    · intro jj hjj
      rw [Finset.mem_filter, Finset.mem_product] at hjj ⊢
      rcases hjj with ⟨⟨h1, h2⟩, hP⟩
      exact ⟨⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩,
        (hequiv jj.1 h1 jj.2 h2).mp hP⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      rw [Finset.mem_filter, Finset.mem_product] at ha₁ ha₂
      have heq1 : circlePt r₁ (θ a₁.1) = circlePt r₁ (θ a₂.1) := congrArg Prod.fst heq
      have heq2 : circlePt r₂ (θ a₁.2) = circlePt r₂ (θ a₂.2) := congrArg Prod.snd heq
      exact Prod.ext (hinjA ha₁.1.1 ha₂.1.1 heq1) (hinjB ha₁.1.2 ha₂.1.2 heq2)
    · intro pq hpq
      rw [Finset.mem_filter, Finset.mem_product] at hpq
      rcases hpq with ⟨⟨hp1, hp2⟩, hQ⟩
      rcases Finset.mem_image.mp hp1 with ⟨j₁, hj1, hpe⟩
      rcases Finset.mem_image.mp hp2 with ⟨j₂, hj2, hqe⟩
      refine ⟨(j₁, j₂), ?_, Prod.ext hpe hqe⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hj1, hj2⟩, (hequiv j₁ hj1 j₂ hj2).mpr (by rwa [hpe, hqe])⟩
  have hoff_split : ∀ (d : ℝ) (hd0 : 0 < d)
      (hL22 : ∀ p ∈ L₂, ∀ q ∈ L₂, dist p q ≠ d)
      (hSml : ∀ p ∈ L₂ ∪ L₃, ∀ q ∈ L₃, dist p q ≠ d)
      (hL13 : ∀ p ∈ L₁, ∀ q ∈ L₃, dist p q ≠ d → True),
      (A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card =
        ((L₁ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = d)).card +
        ((L₁ ×ˢ L₂).filter (fun pq => dist pq.1 pq.2 = d)).card +
        ((L₂ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = d)).card +
        ((L₁ ×ˢ L₃).filter (fun pq => dist pq.1 pq.2 = d)).card +
        ((L₃ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = d)).card := by
    intro d hd0 hL22 hSml _
    let F := A.offDiag.filter (fun pq => dist pq.1 pq.2 = d)
    let F11 := (L₁ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = d)
    let F12 := (L₁ ×ˢ L₂).filter (fun pq => dist pq.1 pq.2 = d)
    let F21 := (L₂ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = d)
    let F13 := (L₁ ×ˢ L₃).filter (fun pq => dist pq.1 pq.2 = d)
    let F31 := (L₃ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = d)
    have hF_eq : F = F11 ∪ F12 ∪ F21 ∪ F13 ∪ F31 := by
      ext ⟨p, q⟩
      simp only [F, F11, F12, F21, F13, F31, Finset.mem_union, Finset.mem_filter,
        Finset.mem_offDiag, Finset.mem_product]
      constructor
      · rintro ⟨⟨hp, hq, hpq⟩, hdist⟩
        rcases Finset.mem_union.mp hp with hp12 | hp3
        · rcases Finset.mem_union.mp hp12 with hp1 | hp2
          · rcases Finset.mem_union.mp hq with hq12 | hq3
            · rcases Finset.mem_union.mp hq12 with hq1 | hq2
              · left; left; left; left; exact ⟨⟨hp1, hq1⟩, hdist⟩
              · left; left; left; right; exact ⟨⟨hp1, hq2⟩, hdist⟩
            · left; right; exact ⟨⟨hp1, hq3⟩, hdist⟩
          · rcases Finset.mem_union.mp hq with hq12 | hq3
            · rcases Finset.mem_union.mp hq12 with hq1 | hq2
              · left; left; right; exact ⟨⟨hp2, hq1⟩, hdist⟩
              · exact absurd hdist (hL22 p hp2 q hq2)
            · exact absurd hdist (hSml p (Finset.mem_union_left _ hp2) q hq3)
        · rcases Finset.mem_union.mp hq with hq12 | hq3
          · rcases Finset.mem_union.mp hq12 with hq1 | hq2
            · right; exact ⟨⟨hp3, hq1⟩, hdist⟩
            · exact absurd (by rwa [dist_comm]) (hSml q (Finset.mem_union_left _ hq2) p hp3)
          · exact absurd hdist (hSml p (Finset.mem_union_right _ hp3) q hq3)
      · have mkMem : ∀ x ∈ L₁ ∪ L₂ ∪ L₃, x ∈ A := fun x hx => hx
        have hne_dist : ∀ x y : E2, dist x y = d → x ≠ y := by
          intro x y hxy rfl; rw [dist_self] at hxy; linarith only [hxy, hd0]
        rintro ((((⟨⟨hp1, hq1⟩, hd⟩ | ⟨⟨hp1, hq2⟩, hd⟩) | ⟨⟨hp2, hq1⟩, hd⟩) | ⟨⟨hp1, hq3⟩, hd⟩) | ⟨⟨hp3, hq1⟩, hd⟩) <;>
          refine ⟨⟨?_, ?_, hne_dist _ _ hd⟩, hd⟩ <;>
          [exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp1));
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_left _ hq1));
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp1));
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_right _ hq2));
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_right _ hp2));
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_left _ hq1));
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp1));
           exact mkMem _ (Finset.mem_union_right _ hq3);
           exact mkMem _ (Finset.mem_union_right _ hp3);
           exact mkMem _ (Finset.mem_union_left _ (Finset.mem_union_left _ hq1))]
    have hdisj_norm : ∀ (S₁ S₂ T₁ T₂ : Finset E2)
        (hSub1 : S₁ ⊆ A) (hSub2 : S₂ ⊆ A) (hSub3 : T₁ ⊆ A) (hSub4 : T₂ ⊆ A),
        (Disjoint S₁ T₁ ∨ Disjoint S₂ T₂) →
        Disjoint ((S₁ ×ˢ S₂).filter (fun pq => dist pq.1 pq.2 = d))
                 ((T₁ ×ˢ T₂).filter (fun pq => dist pq.1 pq.2 = d)) := by
      intro S₁ S₂ T₁ T₂ _ _ _ _ hdisj
      rw [Finset.disjoint_left]
      intro ⟨x, y⟩ hxy1 hxy2
      rw [Finset.mem_filter, Finset.mem_product] at hxy1 hxy2
      rcases hdisj with hd1 | hd2
      · exact Finset.disjoint_left.mp hd1 hxy1.1.1 hxy2.1.1
      · exact Finset.disjoint_left.mp hd2 hxy1.1.2 hxy2.1.2
    have hd12 : Disjoint L₁ L₂ := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      have h1 := (hnorm_pt p (Finset.mem_union_left _ (Finset.mem_union_left _ hp1))).1.mp hp1
      have h2 := (hnorm_pt p (Finset.mem_union_left _ (Finset.mem_union_right _ hp2))).2.1.mp hp2
      linarith
    have hd13 : Disjoint L₁ L₃ := by
      rw [Finset.disjoint_left]; intro p hp1 hp3
      have h1 := (hnorm_pt p (Finset.mem_union_left _ (Finset.mem_union_left _ hp1))).1.mp hp1
      have h3 := (hnorm_pt p (Finset.mem_union_right _ hp3)).2.2.mp hp3
      linarith
    have hd23 : Disjoint L₂ L₃ := by
      rw [Finset.disjoint_left]; intro p hp2 hp3
      have h2 := (hnorm_pt p (Finset.mem_union_left _ (Finset.mem_union_right _ hp2))).2.1.mp hp2
      have h3 := (hnorm_pt p (Finset.mem_union_right _ hp3)).2.2.mp hp3
      linarith
    have hSub1 : L₁ ⊆ A := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    have hSub2 : L₂ ⊆ A := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    have hSub3 : L₃ ⊆ A := fun _ hx => Finset.mem_union_right _ hx
    have h_11_12 : Disjoint F11 F12 := hdisj_norm _ _ _ _ hSub1 hSub1 hSub1 hSub2 (Or.inr hd12)
    have h_112_21 : Disjoint (F11 ∪ F12) F21 := by
      refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
      · exact hdisj_norm _ _ _ _ hSub1 hSub1 hSub2 hSub1 (Or.inl hd12)
      · exact hdisj_norm _ _ _ _ hSub1 hSub2 hSub2 hSub1 (Or.inl hd12)
    have h_121_13 : Disjoint (F11 ∪ F12 ∪ F21) F13 := by
      refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨?_, ?_⟩, ?_⟩
      · exact hdisj_norm _ _ _ _ hSub1 hSub1 hSub1 hSub3 (Or.inr hd13)
      · exact hdisj_norm _ _ _ _ hSub1 hSub2 hSub1 hSub3 (Or.inr hd23)
      · exact hdisj_norm _ _ _ _ hSub2 hSub1 hSub1 hSub3 (Or.inl hd12.symm)
    have h_131_31 : Disjoint (F11 ∪ F12 ∪ F21 ∪ F13) F31 := by
      refine Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact hdisj_norm _ _ _ _ hSub1 hSub1 hSub3 hSub1 (Or.inl hd13)
      · exact hdisj_norm _ _ _ _ hSub1 hSub2 hSub3 hSub1 (Or.inl hd13)
      · exact hdisj_norm _ _ _ _ hSub2 hSub1 hSub3 hSub1 (Or.inl hd23)
      · exact hdisj_norm _ _ _ _ hSub1 hSub3 hSub3 hSub1 (Or.inl hd13)
    change F.card = F11.card + F12.card + F21.card + F13.card + F31.card
    rw [hF_eq, Finset.card_union_of_disjoint h_131_31,
      Finset.card_union_of_disjoint h_121_13,
      Finset.card_union_of_disjoint h_112_21,
      Finset.card_union_of_disjoint h_11_12]
  -- Swap symmetry helper: |F_ba| = |F_ab|
  have hswap_card : ∀ (S T : Finset E2) (d : ℝ),
      ((S ×ˢ T).filter (fun pq => dist pq.1 pq.2 = d)).card =
        ((T ×ˢ S).filter (fun pq => dist pq.1 pq.2 = d)).card := by
    intro S T d
    apply Finset.card_bij (fun pq _ => (pq.2, pq.1))
    · intro pq hpq
      simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
      exact ⟨⟨hpq.1.2, hpq.1.1⟩, by simpa [dist_comm] using hpq.2⟩
    · intro a b _ _ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro pq hpq
      simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
      exact ⟨(pq.2, pq.1), ⟨⟨hpq.1.2, hpq.1.1⟩, by simpa [dist_comm] using hpq.2⟩, rfl⟩
  -- Compute pairMult(d₁) = m
  have hm1 : pairMult A (breakD1 m) = m := by
    unfold pairMult
    have hsplit := hoff_split (breakD1 m) hd1_pos
      (fun p hp q hq => by
        rcases Finset.mem_image.mp hp with ⟨j₁, hj1, rfl⟩
        rcases Finset.mem_image.mp hq with ⟨j₂, hj2, rfl⟩
        rw [Finset.mem_range] at hj1 hj2
        have := hdist_L1_L1 (j₁ := j₁) (j₂ := j₂) hj1 hj2
        have h2 := hdist_L2_L2 hj1 hj2
        linarith)
      (fun p hp q hq => by have := hdist_small hp hq; linarith)
      (fun _ _ _ _ _ => trivial)
    have h11 : ((L₁ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD1 m)).card = 2 * m := by
      rw [hprod_card hinj1 hinj1 (fun jj => cdiff m jj.1 jj.2 = t) _]
      · have hc := card_cdiff_product (k := t) (Finset.range m) Finset.Subset.rfl (by omega) le_rfl
        rwa [Finset.card_range] at hc
      · intro j₁ hj1 j₂ hj2
        rw [Finset.mem_range] at hj1 hj2
        by_cases hne : j₁ = j₂
        · subst hne; rw [(cdiff_eq_zero_iff hj1 hj2).mpr rfl, dist_self]
          constructor
          · intro h; exfalso; omega
          · intro h; exfalso; linarith only [h, hd1_pos]
        · have h1 := hdist_L1_L1 hj1 hj2 hne
          have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
          constructor
          · intro h; exact h1.1 h
          · intro hd
            rcases eq_or_lt_of_le hkt with h_t | h_lt
            · exact h_t
            · exfalso
              rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
              · have := h1.2.1 h_tm1; linarith
              · have := h1.2.2 (by omega); linarith
    have h12 : ((L₁ ×ˢ L₂).filter (fun pq => dist pq.1 pq.2 = breakD1 m)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      rcases Finset.mem_image.mp hpq.1 with ⟨j₁, hj1, rfl⟩
      rcases Finset.mem_image.mp hpq.2 with ⟨j₂, hj2, rfl⟩
      rw [Finset.mem_range] at hj1 hj2
      have h1 := hdist_L1_L2 hj1 hj2
      have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
      rcases eq_or_lt_of_le hkt with h_t | h_lt
      · linarith [h1.1 h_t]
      · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
        · linarith [h1.2.1 h_tm1]
        · linarith [h1.2.2 (by omega)]
    have h13 : ((L₁ ×ˢ L₃).filter (fun pq => dist pq.1 pq.2 = breakD1 m)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      rcases Finset.mem_image.mp hpq.1 with ⟨j₁, hj1, rfl⟩
      rcases Finset.mem_image.mp hpq.2 with ⟨j₃, hj3, rfl⟩
      rw [Finset.mem_range] at hj1 hj3
      have h1 := hdist_L1_L3 hj1 (by omega : j₃ < m)
      have hkt : cdiff m j₁ j₃ ≤ t := cdiff_le_half hj1 (by omega : j₃ < m)
      rcases eq_or_lt_of_le hkt with h_t | h_lt
      · linarith [h1.1 h_t]
      · linarith [h1.2 (by omega)]
    have h21 : ((L₂ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD1 m)).card = 0 := by
      rw [hswap_card, h12]
    have h31 : ((L₃ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD1 m)).card = 0 := by
      rw [hswap_card, h13]
    rw [hsplit, h11, h12, h21, h13, h31]
    omega
  -- Compute pairMult(d₂) = 3 * m
  have hm2 : pairMult A (breakD2 m) = 3 * m := by
    unfold pairMult
    have hsplit := hoff_split (breakD2 m) hd2_pos
      (fun p hp q hq => by
        rcases Finset.mem_image.mp hp with ⟨j₁, hj1, rfl⟩
        rcases Finset.mem_image.mp hq with ⟨j₂, hj2, rfl⟩
        rw [Finset.mem_range] at hj1 hj2
        linarith [hdist_L2_L2 hj1 hj2])
      (fun p hp q hq => by linarith [hdist_small hp hq])
      (fun _ _ _ _ _ => trivial)
    have h11 : ((L₁ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD2 m)).card = 2 * m := by
      rw [hprod_card hinj1 hinj1 (fun jj => cdiff m jj.1 jj.2 = t - 1) _]
      · have hc := card_cdiff_product (k := t - 1) (Finset.range m) Finset.Subset.rfl (by omega) (by omega)
        rwa [Finset.card_range] at hc
      · intro j₁ hj1 j₂ hj2
        rw [Finset.mem_range] at hj1 hj2
        by_cases hne : j₁ = j₂
        · subst hne; rw [(cdiff_eq_zero_iff hj1 hj2).mpr rfl, dist_self]
          constructor
          · intro h; exfalso; omega
          · intro h; exfalso; linarith only [h, hd2_pos]
        · have h1 := hdist_L1_L1 hj1 hj2 hne
          have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
          constructor
          · intro h; exact h1.2.1 h
          · intro hd
            rcases eq_or_lt_of_le hkt with h_t | h_lt
            · linarith [h1.1 h_t]
            · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
              · exact h_tm1
              · linarith [h1.2.2 (by omega)]
    have h12 : ((L₁ ×ˢ L₂).filter (fun pq => dist pq.1 pq.2 = breakD2 m)).card = 2 * m := by
      rw [hprod_card hinj1 hinj2 (fun jj => cdiff m jj.1 jj.2 = t) _]
      · have hc := card_cdiff_product (k := t) (Finset.range m) Finset.Subset.rfl (by omega) le_rfl
        rwa [Finset.card_range] at hc
      · intro j₁ hj1 j₂ hj2
        rw [Finset.mem_range] at hj1 hj2
        have h1 := hdist_L1_L2 hj1 hj2
        have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
        constructor
        · intro h; exact h1.1 h
        · intro hd
          rcases eq_or_lt_of_le hkt with h_t | h_lt
          · exact h_t
          · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
            · linarith [h1.2.1 h_tm1]
            · linarith [h1.2.2 (by omega)]
    have h13 : ((L₁ ×ˢ L₃).filter (fun pq => dist pq.1 pq.2 = breakD2 m)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      rcases Finset.mem_image.mp hpq.1 with ⟨j₁, hj1, rfl⟩
      rcases Finset.mem_image.mp hpq.2 with ⟨j₃, hj3, rfl⟩
      rw [Finset.mem_range] at hj1 hj3
      have h1 := hdist_L1_L3 hj1 (by omega : j₃ < m)
      have hkt : cdiff m j₁ j₃ ≤ t := cdiff_le_half hj1 (by omega : j₃ < m)
      rcases eq_or_lt_of_le hkt with h_t | h_lt
      · linarith [h1.1 h_t]
      · linarith [h1.2 (by omega)]
    have h21 : ((L₂ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD2 m)).card = 2 * m := by
      rw [hswap_card, h12]
    have h31 : ((L₃ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD2 m)).card = 0 := by
      rw [hswap_card, h13]
    rw [hsplit, h11, h12, h21, h13, h31]
    omega
  -- Compute pairMult(d₃) = 2 * m + 2 * s
  have hm3 : pairMult A (breakD3 m) = 2 * m + 2 * s := by
    unfold pairMult
    have hsplit := hoff_split (breakD3 m) hd3_pos
      (fun p hp q hq => by
        rcases Finset.mem_image.mp hp with ⟨j₁, hj1, rfl⟩
        rcases Finset.mem_image.mp hq with ⟨j₂, hj2, rfl⟩
        rw [Finset.mem_range] at hj1 hj2
        exact (hdist_L2_L2 hj1 hj2).ne)
      (fun p hp q hq => (hdist_small hp hq).ne)
      (fun _ _ _ _ _ => trivial)
    have h11 : ((L₁ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD3 m)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      rcases Finset.mem_image.mp hpq.1 with ⟨j₁, hj1, rfl⟩
      rcases Finset.mem_image.mp hpq.2 with ⟨j₂, hj2, rfl⟩
      rw [Finset.mem_range] at hj1 hj2
      by_cases hne : j₁ = j₂
      · subst hne; rw [dist_self]; linarith
      · have h1 := hdist_L1_L1 hj1 hj2 hne
        have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
        rcases eq_or_lt_of_le hkt with h_t | h_lt
        · linarith [h1.1 h_t]
        · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
          · linarith [h1.2.1 h_tm1]
          · exact (h1.2.2 (by omega)).ne
    have h12 : ((L₁ ×ˢ L₂).filter (fun pq => dist pq.1 pq.2 = breakD3 m)).card = 2 * m := by
      rw [hprod_card hinj1 hinj2 (fun jj => cdiff m jj.1 jj.2 = t - 1) _]
      · have hc := card_cdiff_product (k := t - 1) (Finset.range m) Finset.Subset.rfl (by omega) (by omega)
        rwa [Finset.card_range] at hc
      · intro j₁ hj1 j₂ hj2
        rw [Finset.mem_range] at hj1 hj2
        have h1 := hdist_L1_L2 hj1 hj2
        have hkt : cdiff m j₁ j₂ ≤ t := cdiff_le_half hj1 hj2
        constructor
        · intro h; exact h1.2.1 h
        · intro hd
          rcases eq_or_lt_of_le hkt with h_t | h_lt
          · linarith [h1.1 h_t]
          · rcases eq_or_lt_of_le (by omega : cdiff m j₁ j₂ ≤ t - 1) with h_tm1 | h_lt2
            · exact h_tm1
            · linarith [h1.2.2 (by omega)]
    have h13 : ((L₁ ×ˢ L₃).filter (fun pq => dist pq.1 pq.2 = breakD3 m)).card = 2 * s := by
      rw [hprod_card hinj1 hinj3 (fun jj => cdiff m jj.1 jj.2 = t) _]
      · have hs_sub : Finset.range s ⊆ Finset.range m := Finset.range_mono (by omega)
        have := card_cdiff_product (Finset.range s) hs_sub (by omega) le_rfl
        rwa [Finset.card_range] at this
      · intro j₁ hj1 j₃ hj3
        rw [Finset.mem_range] at hj1 hj3
        have h1 := hdist_L1_L3 hj1 (by omega : j₃ < m)
        have hkt : cdiff m j₁ j₃ ≤ t := cdiff_le_half hj1 (by omega : j₃ < m)
        constructor
        · intro h; exact h1.1 h
        · intro hd
          rcases eq_or_lt_of_le hkt with h_t | h_lt
          · exact h_t
          · linarith [h1.2 (by omega)]
    have h21 : ((L₂ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD3 m)).card = 2 * m := by
      rw [hswap_card, h12]
    have h31 : ((L₃ ×ˢ L₁).filter (fun pq => dist pq.1 pq.2 = breakD3 m)).card = 2 * s := by
      rw [hswap_card, h13]
    rw [hsplit, h11, h12, h21, h13, h31]
    omega
  refine ⟨hd3_pos, hd3_lt_d2, hd2_lt_d1, hpos_class, hm1, hm2, hm3, ?_, ?_, ?_⟩ <;> omega

end MinM2M3Counterexample

end
end PPL149
