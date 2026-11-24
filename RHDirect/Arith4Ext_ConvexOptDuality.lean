/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Arith4Ext.ConvexOptDuality: Hyperplane Separation, Farkas, LP Duality, Minimax, Birkhoff, König & Dilworth

Reusable Tier A `Arithmetica4` library module built from scratch on targeted Mathlib imports,
providing finite-dimensional convex duality and combinatorial optimization theorems in
`namespace Arith4Ext.ConvexOptDuality`:

1. **Hyperplane Separation & Farkas' Lemma (`Section 1`):**
   - `hyperplane_separation_closed_convex`: strict hyperplane separation of a point `b ∉ K` from
     a nonempty closed convex set `K` in `EuclideanSpace ℝ (Fin d)` via nearest-point projection.
   - `hyperplane_separation_cone`: strict cone separation (`∀ x ∈ K, ⟨c, x⟩ ≤ 0` and `0 < ⟨c, b⟩`).
   - `farkas_lemma`, `farkas_lemma_le`, `farkas_lemma_nonneg_le`: equality, unconstrained
     inequality, and nonnegative inequality forms of Farkas' Lemma on `Matrix (Fin m) (Fin n) ℝ`.

2. **Linear Programming Duality & Complementary Slackness (`Section 2`):**
   - `lp_weak_duality`: `c ⬝ᵥ x ≤ b ⬝ᵥ y` for primal/dual feasible `(x, y)`.
   - `lp_complementary_slackness`: exact `c ⬝ᵥ x = b ⬝ᵥ y ↔` complementary slackness
     characterization and optimality certificates.
   - `lp_strong_duality`: attained primal-dual optimality `c ⬝ᵥ x* = b ⬝ᵥ y*` whenever both
     primal and dual are feasible.

3. **Von Neumann's Minimax Theorem (`Section 3`):**
   - `von_neumann_minimax_saddle`: attained Nash/saddle point `(p*, q*)` on the probability
     simplices `Δ_m × Δ_n` for every real payoff matrix `A : Matrix (Fin m) (Fin n) ℝ`
     (`0 < m`, `0 < n`), plus `von_neumann_minimax_value` (`max_p min_q = min_q max_p`).

4. **Birkhoff–von Neumann Theorem (`Section 4`):**
   - `birkhoff_hall_permutation`: every nonnegative matrix with positive constant row/column sums
     contains a positive permutation diagonal (via Hall's Marriage Theorem).
   - `birkhoff_von_neumann`: every `n × n` doubly stochastic matrix is a convex combination of
     permutation matrices.

5. **König–Egerváry, Mirsky & Dilworth Theorems (`Section 5`):**
   - `konig_egervary_weak`, `konig_egervary`: maximum bipartite matching equals minimum vertex
     cover (via Hall's Marriage Theorem).
   - `mirsky_theorem`: maximum chain size equals minimum antichain-cover size in any finite poset.
   - `dilworth_weak`, `dilworth_theorem`: maximum antichain size equals minimum chain-cover size
     in any finite poset (via Fulkerson's reduction to König–Egerváry).

All public declarations use strictly pure-Mathlib signatures (`0` custom public types or proxies).
-/

namespace Arith4Ext.ConvexOptDuality

open scoped BigOperators Matrix

/-! ## Section 1: Hyperplane Separation & Farkas' Lemma -/

section SeparationAndFarkas

/-- **Strict Hyperplane Separation** of a point `b ∉ K` from a nonempty closed convex set `K`
in `EuclideanSpace ℝ (Fin d)` via nearest-point projection. -/
theorem hyperplane_separation_closed_convex {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconv : Convex ℝ K)
    {b : EuclideanSpace ℝ (Fin d)} (hb : b ∉ K) :
    ∃ c : EuclideanSpace ℝ (Fin d), ∃ α : ℝ,
      (∀ x ∈ K, inner ℝ c x ≤ α) ∧ α < inner ℝ c b := by
  obtain ⟨k₀, hk₀⟩ := hne
  let R : ℝ := ‖b - k₀‖
  let S : Set (EuclideanSpace ℝ (Fin d)) := K ∩ Metric.closedBall b R
  have hS_comp : IsCompact S :=
    (isCompact_closedBall b R).inter_left hclosed
  have hk₀_S : k₀ ∈ S := ⟨hk₀, by simp [R, dist_eq_norm, norm_sub_rev]⟩
  have hcont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) => ‖b - x‖ ^ 2) S :=
    ((continuous_const.sub continuous_id).norm.pow 2).continuousOn
  obtain ⟨p, hp_S, hp_min⟩ := hS_comp.exists_isMinOn ⟨k₀, hk₀_S⟩ hcont
  have hp_K : p ∈ K := hp_S.1
  have hp_all : ∀ x ∈ K, ‖b - p‖ ^ 2 ≤ ‖b - x‖ ^ 2 := by
    intro x hx
    by_cases hbx : ‖b - x‖ ≤ R
    · exact hp_min ⟨hx, by simpa [S, dist_eq_norm, norm_sub_rev] using hbx⟩
    · push Not at hbx
      have hp_R : ‖b - p‖ ≤ R := by
        simpa [dist_eq_norm, norm_sub_rev] using hp_S.2
      have hsq : ‖b - p‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp_R 2
      have hsq' : R ^ 2 < ‖b - x‖ ^ 2 := by
        nlinarith [norm_nonneg (b - x), norm_nonneg (b - k₀)]
      exact le_trans hsq hsq'.le
  let c : EuclideanSpace ℝ (Fin d) := b - p
  have hc_ne : c ≠ 0 := by
    intro h0
    have hbp : b = p := sub_eq_zero.mp h0
    exact hb (hbp ▸ hp_K)
  have hsep : ∀ x ∈ K, inner ℝ c x ≤ inner ℝ c p := by
    intro x hx
    by_contra hgt
    push Not at hgt
    have hpos_ip : 0 < inner ℝ c (x - p) := by
      rw [inner_sub_right]
      linarith
    have hstep : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ 2 * inner ℝ c (x - p) > t * ‖x - p‖ ^ 2 := by
      by_cases hxp0 : ‖x - p‖ = 0
      · exact ⟨1, one_pos, le_rfl, by simp [hxp0]; exact hpos_ip⟩
      · have hxp_pos : 0 < ‖x - p‖ ^ 2 :=
          sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hxp0))
        let t := min (1 : ℝ) (inner ℝ c (x - p) / ‖x - p‖ ^ 2)
        have ht_pos : 0 < t := lt_min one_pos (div_pos hpos_ip hxp_pos)
        have ht_le1 : t ≤ 1 := min_le_left _ _
        have ht_le2 : t * ‖x - p‖ ^ 2 ≤ inner ℝ c (x - p) :=
          (le_div_iff₀ hxp_pos).mp (min_le_right _ _)
        exact ⟨t, ht_pos, ht_le1, by linarith⟩
    rcases hstep with ⟨t, ht_pos, ht_le1, ht_ineq⟩
    have hcomb_mem : (1 - t) • p + t • x ∈ K :=
      hconv hp_K hx (by linarith) ht_pos.le (by ring)
    have hcomb_eq : b - ((1 - t) • p + t • x) = c - t • (x - p) := by
      simp only [c, sub_smul, one_smul, smul_sub]
      abel
    have hmin_t := hp_all _ hcomb_mem
    rw [hcomb_eq, norm_sub_sq_real c (t • (x - p)), inner_smul_right, norm_smul,
        Real.norm_of_nonneg ht_pos.le] at hmin_t
    have hcontra : 2 * t * inner ℝ c (x - p) ≤ t ^ 2 * ‖x - p‖ ^ 2 := by nlinarith
    have hcontra' : 2 * inner ℝ c (x - p) ≤ t * ‖x - p‖ ^ 2 := by nlinarith
    linarith
  have hcb_gt : inner ℝ c p < inner ℝ c b := by
    have hsub : inner ℝ c b - inner ℝ c p = ‖c‖ ^ 2 := by
      rw [← inner_sub_right, show b - p = c from rfl, real_inner_self_eq_norm_sq]
    have hc_sq_pos : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc_ne)
    linarith
  exact ⟨c, inner ℝ c p, hsep, hcb_gt⟩

/-- **Hyperplane Separation for Closed Convex Cones**: if `K` is a closed convex cone
(`0 ∈ K` and closed under `r ≥ 0` scaling) and `b ∉ K`, there exists `c` such that
`∀ x ∈ K, inner ℝ c x ≤ 0` and `0 < inner ℝ c b`. -/
theorem hyperplane_separation_cone {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hzero : (0 : EuclideanSpace ℝ (Fin d)) ∈ K) (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (hcone : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ K, r • x ∈ K)
    {b : EuclideanSpace ℝ (Fin d)} (hb : b ∉ K) :
    ∃ c : EuclideanSpace ℝ (Fin d),
      (∀ x ∈ K, inner ℝ c x ≤ 0) ∧ 0 < inner ℝ c b := by
  obtain ⟨c, α, hle, hgt⟩ := hyperplane_separation_closed_convex ⟨0, hzero⟩ hclosed hconv hb
  have hα_nonneg : 0 ≤ α := by simpa using hle 0 hzero
  have hcb_pos : 0 < inner ℝ c b := lt_of_le_of_lt hα_nonneg hgt
  refine ⟨c, fun x hx => ?_, hcb_pos⟩
  by_contra hpos
  push Not at hpos
  obtain ⟨n, hn⟩ := exists_nat_gt (α / inner ℝ c x)
  have hscaled : (n : ℝ) • x ∈ K := hcone (n : ℝ) (Nat.cast_nonneg n) x hx
  have hle_n := hle _ hscaled
  rw [inner_smul_right] at hle_n
  have hlt_n : α < (n : ℝ) * inner ℝ c x := (div_lt_iff₀ hpos).mp hn
  linarith

private lemma conic_caratheodory {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    {y : EuclideanSpace ℝ (Fin d)}
    (hx : ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ ∑ j : Fin n, x j • a j = y) :
    ∃ S : Finset (Fin n), LinearIndependent ℝ (fun j : S => a j.1) ∧
      ∃ w : S → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j : S, w j • a j.1 = y := by
  classical
  let P : ℕ → Prop := fun k => ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧
    ∑ j : Fin n, x j • a j = y ∧ (Finset.univ.filter (fun j => x j ≠ 0)).card ≤ k
  have hk0 : ∃ k, P k := by
    rcases hx with ⟨x, hx0, hsum⟩
    exact ⟨_, x, hx0, hsum, le_rfl⟩
  let kmin := Nat.find hk0
  obtain ⟨x, hx0, hsum, hcard⟩ := Nat.find_spec hk0
  let S : Finset (Fin n) := Finset.univ.filter (fun j => x j ≠ 0)
  have hli : LinearIndependent ℝ (fun j : S => a j.1) := by
    by_contra hdep
    rw [Fintype.linearIndependent_iff] at hdep
    push Not at hdep
    rcases hdep with ⟨c, hcsum, j₀, hj₀⟩
    let c' : S → ℝ := if 0 < c j₀ then c else -c
    have hc'sum : ∑ j : S, c' j • a j.1 = 0 := by
      by_cases hpos0 : 0 < c j₀
      · simp only [c', hpos0, ↓reduceIte]; exact hcsum
      · simp only [c', hpos0, ↓reduceIte, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
          hcsum, neg_zero]
    have hc'j0 : 0 < c' j₀ := by
      by_cases hpos0 : 0 < c j₀
      · simp [c', hpos0]
      · have hneg0 : c j₀ < 0 := lt_of_le_of_ne (not_lt.mp hpos0) hj₀
        simp [c', hpos0, hneg0]
    let I : Finset S := Finset.univ.filter (fun j => 0 < c' j)
    have hI_ne : I.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc'j0⟩⟩
    obtain ⟨jstar, hjstar_I, hjstar_min⟩ :=
      I.exists_min_image (fun j => x j.1 / c' j) hI_ne
    have hjstar_pos_c : 0 < c' jstar := (Finset.mem_filter.mp hjstar_I).2
    let t : ℝ := x jstar.1 / c' jstar
    have hx_pos_S : ∀ j : S, 0 < x j.1 := fun j =>
      lt_of_le_of_ne (hx0 j.1) (Ne.symm (Finset.mem_filter.mp j.2).2)
    have ht_pos : 0 < t := div_pos (hx_pos_S jstar) hjstar_pos_c
    let x' : Fin n → ℝ := fun k => if hk : k ∈ S then x k - t * c' ⟨k, hk⟩ else 0
    have hx'_nonneg : ∀ k, 0 ≤ x' k := by
      intro k
      by_cases hk : k ∈ S
      · simp only [x', hk, ↓reduceDIte]
        by_cases hck : 0 < c' ⟨k, hk⟩
        · have hmin_k : t ≤ x k / c' ⟨k, hk⟩ :=
            hjstar_min ⟨k, hk⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hck⟩)
          have hmul : t * c' ⟨k, hk⟩ ≤ x k := (le_div_iff₀ hck).mp hmin_k
          linarith
        · have hle0 : c' ⟨k, hk⟩ ≤ 0 := not_lt.mp hck
          have hmul0 : t * c' ⟨k, hk⟩ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_pos.le hle0
          linarith [hx0 k]
      · simp [x', hk]
    have hx'_sum : ∑ k : Fin n, x' k • a k = y := by
      have hx_S : ∑ k ∈ S, x k • a k = y := by
        rw [← hsum, ← Finset.sum_subset (Finset.subset_univ S)]
        intro k _ hkS
        have hkx0 : x k = 0 := by
          by_contra hne
          exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        simp [hkx0]
      have hc'_S : ∑ j : S, (t * c' j) • a j.1 = 0 := by
        have : ∑ j : S, (t * c' j) • a j.1 = t • ∑ j : S, c' j • a j.1 := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]
        rw [this, hc'sum, smul_zero]
      have hsub_eq : ∑ j : S, (x j.1 - t * c' j) • a j.1 =
          (∑ j : S, x j.1 • a j.1) - ∑ j : S, (t * c' j) • a j.1 := by
        simp_rw [sub_smul, Finset.sum_sub_distrib]
      have hsum_x' : ∑ k ∈ S, x' k • a k = ∑ j : S, (x j.1 - t * c' j) • a j.1 := by
        rw [← Finset.sum_coe_sort S (fun k => x' k • a k)]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [x', j.2]
      calc ∑ k : Fin n, x' k • a k
          = ∑ k ∈ S, x' k • a k := by
              symm; refine Finset.sum_subset (Finset.subset_univ S) fun k _ hkS => by simp [x', hkS]
        _ = ∑ j : S, (x j.1 - t * c' j) • a j.1 := hsum_x'
        _ = (∑ j : S, x j.1 • a j.1) - 0 := by rw [hsub_eq, hc'_S]
        _ = y := by rw [sub_zero, Finset.sum_coe_sort S (fun k => x k • a k), hx_S]
    have hx'_supp_sub : Finset.univ.filter (fun k => x' k ≠ 0) ⊆ S.erase jstar.1 := by
      intro k hk
      have hxk : x' k ≠ 0 := (Finset.mem_filter.mp hk).2
      have hkS : k ∈ S := by
        by_contra hnot
        apply hxk
        simp [x', hnot]
      refine Finset.mem_erase.mpr ⟨?_, hkS⟩
      intro hkj
      apply hxk
      subst hkj
      simp [x', jstar.2, t, div_mul_cancel₀ _ hjstar_pos_c.ne']
    have hcard_lt : (Finset.univ.filter (fun k => x' k ≠ 0)).card < kmin := by
      have hle_er : (Finset.univ.filter (fun k => x' k ≠ 0)).card ≤ (S.erase jstar.1).card :=
        Finset.card_le_card hx'_supp_sub
      have her_lt : (S.erase jstar.1).card < S.card := Finset.card_erase_lt_of_mem jstar.2
      have hS_le : S.card ≤ kmin := hcard
      omega
    have hk_lt_ne : P (Finset.univ.filter (fun k => x' k ≠ 0)).card :=
      ⟨x', hx'_nonneg, hx'_sum, le_rfl⟩
    exact Nat.find_min hk0 hcard_lt hk_lt_ne
  refine ⟨S, hli, fun j => x j.1, fun j => hx0 j.1, ?_⟩
  rw [Finset.sum_coe_sort S (fun k => x k • a k), ← hsum]
  refine Finset.sum_subset (Finset.subset_univ S) fun k _ hkS => ?_
  have hkx0 : x k = 0 := by
    by_contra hne
    exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩)
  simp [hkx0]

private lemma linearIndependent_conic_isClosed {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℝ (Fin d)) (hli : LinearIndependent ℝ v) :
    IsClosed {y : EuclideanSpace ℝ (Fin d) | ∃ w : ι → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j • v j = y} := by
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ∃ w : ι → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j • v j = y}
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    { toFun := fun w => ∑ j : ι, w.ofLp j • v j
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, smul_smul] }
  have hT_cont : Continuous T := by
    refine continuous_finsetSum Finset.univ fun j _ => ?_
    exact (PiLp.continuous_apply 2 (fun _ => ℝ) j).smul continuous_const
  have hT_inj : Function.Injective T := by
    intro w₁ w₂ hw
    have hdiff : T (w₁ - w₂) = 0 := by rw [map_sub, hw, sub_self]
    have hcoeff := Fintype.linearIndependent_iff.mp hli (fun j => (w₁ - w₂).ofLp j) hdiff
    ext j
    have hj := hcoeff j
    simp only [PiLp.sub_apply] at hj
    linarith
  have hbound : ∃ c : ℝ, 0 < c ∧ ∀ w : EuclideanSpace ℝ ι, c * ‖w‖ ≤ ‖T w‖ := by
    by_cases hι : IsEmpty ι
    · refine ⟨1, one_pos, fun w => ?_⟩
      have hw0 : w = 0 := by ext j; exact hι.elim j
      simp [hw0]
    rw [not_isEmpty_iff] at hι
    let j₀ : ι := Classical.arbitrary ι
    let w₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => if j = j₀ then (1 : ℝ) else 0)
    have hw₀_norm : ‖w₀‖ = 1 := by
      have hsq : ‖w₀‖ ^ 2 = 1 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp [w₀]
      nlinarith [norm_nonneg w₀]
    have hSph_comp : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ ι) 1) :=
      isCompact_sphere 0 1
    have hSph_ne : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty :=
      ⟨w₀, by simp [hw₀_norm]⟩
    obtain ⟨wstar, hwstar_mem, hwstar_min⟩ :=
      hSph_comp.exists_isMinOn hSph_ne (hT_cont.norm.continuousOn)
    have hwstar_norm : ‖wstar‖ = 1 := by simpa using hwstar_mem
    have hwstar_ne : wstar ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hwstar_norm; linarith
    have hTstar_ne : T wstar ≠ 0 := fun h0 => hwstar_ne (hT_inj (h0.trans (map_zero T).symm))
    let c : ℝ := ‖T wstar‖
    have hc_pos : 0 < c := norm_pos_iff.mpr hTstar_ne
    refine ⟨c, hc_pos, fun w => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    have hwn_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    let u : EuclideanSpace ℝ ι := (‖w‖⁻¹) • w
    have hu_mem : u ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := by
      simp only [Metric.mem_sphere, dist_zero_right, u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn_pos.le)]
      exact inv_mul_cancel₀ hwn_pos.ne'
    have hmin_u := hwstar_min hu_mem
    change c ≤ ‖T u‖ at hmin_u
    have hTu : ‖T u‖ = ‖w‖⁻¹ * ‖T w‖ := by
      dsimp only [u]
      rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn_pos.le)]
    rw [hTu] at hmin_u
    have hmul := mul_le_mul_of_nonneg_right hmin_u hwn_pos.le
    rw [mul_right_comm, inv_mul_cancel₀ hwn_pos.ne', one_mul] at hmul
    exact hmul
  rcases hbound with ⟨c, hc_pos, hc_bound⟩
  rw [← closure_subset_iff_isClosed]
  intro y hy
  obtain ⟨u_seq, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hy
  choose w_seq hw_nonneg hw_sum using hu_mem
  let u_lp : ℕ → EuclideanSpace ℝ ι := fun k => WithLp.toLp 2 (w_seq k)
  have hTu : ∀ k, T (u_lp k) = u_seq k := fun k => hw_sum k
  have hbdd_T : ∃ M : ℝ, ∀ k, ‖T (u_lp k)‖ ≤ M := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu_lim 1 one_pos
    let M₁ := (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
      (fun k => ‖u_seq k‖)
    refine ⟨max M₁ (‖y‖ + 1), fun k => ?_⟩
    rw [hTu]
    by_cases hk : k < N + 1
    · exact le_trans (Finset.le_sup' (fun k => ‖u_seq k‖) (Finset.mem_range.mpr hk)) (le_max_left _ _)
    · have hk_ge : N ≤ k := by omega
      have hdist : dist (u_seq k) y < 1 := hN k hk_ge
      have hnorm : ‖u_seq k‖ ≤ ‖y‖ + 1 := by
        calc ‖u_seq k‖ = ‖(u_seq k - y) + y‖ := by simp
          _ ≤ ‖u_seq k - y‖ + ‖y‖ := norm_add_le _ _
          _ = dist (u_seq k) y + ‖y‖ := by rw [dist_eq_norm]
          _ ≤ 1 + ‖y‖ := by linarith
          _ = ‖y‖ + 1 := add_comm _ _
      exact le_trans hnorm (le_max_right _ _)
  rcases hbdd_T with ⟨M, hM⟩
  have hcomp_ball : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ ι) (M / c)) :=
    isCompact_closedBall _ _
  have hu_in_ball : ∀ k, u_lp k ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (M / c) := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc_pos, mul_comm]
    exact le_trans (hc_bound (u_lp k)) (hM k)
  obtain ⟨wstar, _, φ, hφ_mono, hφ_lim⟩ := hcomp_ball.tendsto_subseq hu_in_ball
  have hT_lim : Filter.Tendsto (fun k => T (u_lp (φ k))) Filter.atTop (nhds (T wstar)) :=
    (hT_cont.tendsto wstar).comp hφ_lim
  have hu_sub_lim : Filter.Tendsto (fun k => u_seq (φ k)) Filter.atTop (nhds y) :=
    hu_lim.comp hφ_mono.tendsto_atTop
  have hT_eq_y : T wstar = y := by
    have hT_eq' : Filter.Tendsto (fun k => T (u_lp (φ k))) Filter.atTop (nhds y) := by
      simpa [hTu] using hu_sub_lim
    exact tendsto_nhds_unique hT_lim hT_eq'
  have hwstar_nonneg : ∀ j, 0 ≤ wstar.ofLp j := by
    intro j
    have hlim_j : Filter.Tendsto (fun k => (u_lp (φ k)).ofLp j) Filter.atTop (nhds (wstar.ofLp j)) :=
      ((PiLp.continuous_apply 2 (fun _ => ℝ) j).tendsto wstar).comp hφ_lim
    exact ge_of_tendsto hlim_j (Filter.Eventually.of_forall fun k => hw_nonneg (φ k) j)
  exact ⟨fun j => wstar.ofLp j, hwstar_nonneg, hT_eq_y⟩

private lemma isClosed_conicHull {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    IsClosed {y : EuclideanSpace ℝ (Fin d) | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ ∑ j, x j • a j = y} := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ ∑ j, x j • a j = y}
  let indepSubs : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun S => LinearIndependent ℝ (fun j : S => a j.1))
  let KS : Finset (Fin n) → Set (EuclideanSpace ℝ (Fin d)) := fun S =>
    {y | ∃ w : S → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j : S, w j • a j.1 = y}
  have hEq : K = ⋃ S ∈ indepSubs, KS S := by
    ext y
    simp only [K, Set.mem_iUnion, Set.mem_ofPred_eq, indepSubs, Finset.mem_filter,
      Finset.mem_univ, true_and, KS]
    constructor
    · intro hy
      obtain ⟨S, hli, w, hw0, hwsum⟩ := conic_caratheodory a hy
      exact ⟨S, hli, w, hw0, hwsum⟩
    · rintro ⟨S, _, w, hw0, hwsum⟩
      refine ⟨fun j => if hj : j ∈ S then w ⟨j, hj⟩ else 0, ?_, ?_⟩
      · intro j; by_cases hj : j ∈ S <;> simp [hj, hw0]
      · rw [← hwsum, ← Finset.sum_subset (Finset.subset_univ S)]
        · rw [← Finset.sum_coe_sort S (fun j => (if hj : j ∈ S then w ⟨j, hj⟩ else 0) • a j)]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [j.2]
        · intro j _ hjS; simp [hjS]
  change IsClosed K
  rw [hEq]
  refine indepSubs.finite_toSet.isClosed_biUnion fun S hS => ?_
  have hli : LinearIndependent ℝ (fun j : S => a j.1) := (Finset.mem_filter.mp hS).2
  exact linearIndependent_conic_isClosed (fun j : S => a j.1) hli

/-- **Farkas' Lemma** (equality form): for `A : Matrix (Fin m) (Fin n) ℝ` and `b : Fin m → ℝ`,
`∃ x ≥ 0, A *ᵥ x = b` holds if and only if there is no `y` with `Aᵀ *ᵥ y ≥ 0` and `y ⬝ᵥ b < 0`. -/
theorem farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
      ¬ (∃ y : Fin m → ℝ, (∀ j, 0 ≤ (Aᵀ.mulVec y) j) ∧ y ⬝ᵥ b < 0) := by
  constructor
  · rintro ⟨x, hx0, rfl⟩ ⟨y, hy0, hneg⟩
    have h1 : 0 ≤ Aᵀ.mulVec y ⬝ᵥ x :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hy0 j) (hx0 j)
    have h2 : Aᵀ.mulVec y ⬝ᵥ x = y ⬝ᵥ A.mulVec x := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    linarith
  · intro hno
    let col : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    let bVec : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 b
    let K : Set (EuclideanSpace ℝ (Fin m)) :=
      {y | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ ∑ j : Fin n, x j • col j = y}
    have hsum_eq : ∀ x : Fin n → ℝ, ∑ j : Fin n, x j • col j = WithLp.toLp 2 (A.mulVec x) := by
      intro x
      ext i
      simp only [col, Matrix.mulVec, dotProduct, WithLp.ofLp_sum, Finset.sum_apply,
        WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    by_cases hbK : bVec ∈ K
    · rcases hbK with ⟨x, hx0, hxsum⟩
      rw [hsum_eq x] at hxsum
      refine ⟨x, hx0, ?_⟩
      ext i
      exact congrFun (congrArg WithLp.ofLp hxsum) i
    · exfalso
      have hzero : (0 : EuclideanSpace ℝ (Fin m)) ∈ K :=
        ⟨0, fun _ => le_rfl, by simp⟩
      have hclosed : IsClosed K := isClosed_conicHull col
      have hconv : Convex ℝ K := by
        rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ a b ha hb _
        refine ⟨a • x₁ + b • x₂, fun j => add_nonneg (mul_nonneg ha (hx₁ j))
          (mul_nonneg hb (hx₂ j)), ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
          Finset.sum_add_distrib, ← Finset.smul_sum]
      have hcone : ∀ r : ℝ, 0 ≤ r → ∀ y ∈ K, r • y ∈ K := by
        rintro r hr _ ⟨x, hx, rfl⟩
        refine ⟨r • x, fun j => mul_nonneg hr (hx j), ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      obtain ⟨c, hc_le, hcb_gt⟩ := hyperplane_separation_cone hzero hclosed hconv hcone hbK
      let y : Fin m → ℝ := fun i => -(c.ofLp i)
      apply hno
      refine ⟨y, fun j => ?_, ?_⟩
      · have hmem : col j ∈ K := by
          refine ⟨fun k => if k = j then 1 else 0, fun k => by dsimp only; split_ifs <;> norm_num, ?_⟩
          simp
        have hcj := hc_le (col j) hmem
        rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hcj
        have hdot : (col j).ofLp ⬝ᵥ c.ofLp = - (Aᵀ.mulVec y) j := by
          simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, col, y]
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        linarith
      · have hdot : y ⬝ᵥ b = - inner ℝ c bVec := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
          simp only [dotProduct, bVec, y]
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        linarith

/-- **Farkas' Lemma** (nonnegative inequality form `A *ᵥ x ≤ b`):
`∃ x ≥ 0, A *ᵥ x ≤ b` holds if and only if there is no `y ≥ 0` with `Aᵀ *ᵥ y ≥ 0` and
`y ⬝ᵥ b < 0`. -/
theorem farkas_lemma_nonneg_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i, (A.mulVec x) i ≤ b i) ↔
      ¬ (∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ (Aᵀ.mulVec y) j) ∧ y ⬝ᵥ b < 0) := by
  let A_aug : Matrix (Fin m) (Fin (n + m)) ℝ := fun i k =>
    if hk : k.1 < n then A i ⟨k.1, hk⟩ else if i.1 = k.1 - n then 1 else 0
  have heq_primal : (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i, (A.mulVec x) i ≤ b i) ↔
      (∃ z : Fin (n + m) → ℝ, (∀ k, 0 ≤ z k) ∧ A_aug.mulVec z = b) := by
    constructor
    · rintro ⟨x, hx0, hAx⟩
      let z : Fin (n + m) → ℝ := fun k =>
        if hk : k.1 < n then x ⟨k.1, hk⟩ else b ⟨k.1 - n, by omega⟩ - (A.mulVec x) ⟨k.1 - n, by omega⟩
      refine ⟨z, fun k => ?_, ?_⟩
      · by_cases hk : k.1 < n
        · simp [z, hk, hx0]
        · simp only [z, hk, ↓reduceDIte, sub_nonneg]; exact hAx _
      · ext i
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
        have h1 : ∑ j : Fin n, A_aug i (Fin.castAdd m j) * z (Fin.castAdd m j) = (A.mulVec x) i := by
          simp [A_aug, z, Matrix.mulVec, dotProduct]
        have h2 : ∑ j : Fin m, A_aug i (Fin.natAdd n j) * z (Fin.natAdd n j) =
            b i - (A.mulVec x) i := by
          have hterm : ∀ j : Fin m, A_aug i (Fin.natAdd n j) * z (Fin.natAdd n j) =
              if i = j then b i - (A.mulVec x) i else 0 := by
            intro j
            have hnot : ¬ (n + j.1 < n) := by omega
            have hsub : n + j.1 - n = j.1 := by omega
            by_cases hij : i = j
            · subst hij; simp [A_aug, z, hnot, hsub]
            · have hij' : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
              simp [A_aug, z, hnot, hsub, hij, hij']
          simp [hterm]
        rw [h1, h2]
        ring
    · rintro ⟨z, hz0, hAz⟩
      let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
      refine ⟨x, fun j => hz0 _, fun i => ?_⟩
      have hi := congrFun hAz i
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add] at hi
      have h1 : ∑ j : Fin n, A_aug i (Fin.castAdd m j) * z (Fin.castAdd m j) = (A.mulVec x) i := by
        simp [A_aug, x, Matrix.mulVec, dotProduct]
      have h2 : 0 ≤ ∑ j : Fin m, A_aug i (Fin.natAdd n j) * z (Fin.natAdd n j) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (hz0 _)
        have hnot : ¬ (n + j.1 < n) := by omega
        simp only [A_aug, Fin.val_natAdd, hnot, ↓reduceDIte]
        split_ifs <;> norm_num
      linarith
  have heq_dual : (∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ (Aᵀ.mulVec y) j) ∧ y ⬝ᵥ b < 0) ↔
      (∃ y : Fin m → ℝ, (∀ k, 0 ≤ (A_augᵀ.mulVec y) k) ∧ y ⬝ᵥ b < 0) := by
    refine exists_congr fun y => ?_
    rw [← and_assoc]
    refine and_congr_left fun _ => ?_
    constructor
    · rintro ⟨hy0, hAT⟩ k
      by_cases hk : k.1 < n
      · have heq : (A_augᵀ.mulVec y) k = (Aᵀ.mulVec y) ⟨k.1, hk⟩ := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [A_aug, hk]
        rw [heq]; exact hAT _
      · have hk_sub : k.1 - n < m := by omega
        have heq : (A_augᵀ.mulVec y) k = y ⟨k.1 - n, hk_sub⟩ := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          have hterm : ∀ i : Fin m, A_aug i k * y i =
              if i = ⟨k.1 - n, hk_sub⟩ then y ⟨k.1 - n, hk_sub⟩ else 0 := by
            intro i
            by_cases hi : i = ⟨k.1 - n, hk_sub⟩
            · subst hi; simp [A_aug, hk]
            · have hne : i.1 ≠ k.1 - n := fun h => hi (Fin.ext h)
              simp [A_aug, hk, hne, hi]
          simp [hterm]
        rw [heq]; exact hy0 _
    · intro hk
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have hi := hk (Fin.natAdd n i)
        have heq : (A_augᵀ.mulVec y) (Fin.natAdd n i) = y i := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          have hnot : ¬ (n + i.1 < n) := by omega
          have hsub : n + i.1 - n = i.1 := by omega
          have hterm : ∀ r : Fin m, A_aug r (Fin.natAdd n i) * y r =
              if r = i then y i else 0 := by
            intro r
            by_cases hr : r = i
            · subst hr; simp [A_aug, hnot, hsub]
            · have hne : r.1 ≠ i.1 := fun h => hr (Fin.ext h)
              simp [A_aug, hnot, hsub, hne, hr]
          simp [hterm]
        linarith
      · have hj := hk (Fin.castAdd m j)
        have heq : (A_augᵀ.mulVec y) (Fin.castAdd m j) = (Aᵀ.mulVec y) j := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [A_aug]
        linarith
  rw [heq_primal, heq_dual]
  exact farkas_lemma A_aug b

/-- **Farkas' Lemma** (unconstrained inequality form `A *ᵥ x ≤ b`):
`∃ x, A *ᵥ x ≤ b` holds if and only if there is no `y ≥ 0` with `Aᵀ *ᵥ y = 0` and `y ⬝ᵥ b < 0`. -/
theorem farkas_lemma_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, ∀ i, (A.mulVec x) i ≤ b i) ↔
      ¬ (∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ Aᵀ.mulVec y = 0 ∧ y ⬝ᵥ b < 0) := by
  let A_split : Matrix (Fin m) (Fin (n + n)) ℝ := fun i k =>
    if hk : k.1 < n then A i ⟨k.1, hk⟩ else - A i ⟨k.1 - n, by omega⟩
  have heq_p : (∃ x : Fin n → ℝ, ∀ i, (A.mulVec x) i ≤ b i) ↔
      (∃ z : Fin (n + n) → ℝ, (∀ k, 0 ≤ z k) ∧ ∀ i, (A_split.mulVec z) i ≤ b i) := by
    constructor
    · rintro ⟨x, hAx⟩
      let z : Fin (n + n) → ℝ := fun k =>
        if hk : k.1 < n then max (x ⟨k.1, hk⟩) 0 else max (-x ⟨k.1 - n, by omega⟩) 0
      refine ⟨z, fun k => by by_cases hk : k.1 < n <;> simp [z, hk], fun i => ?_⟩
      have hmul : (A_split.mulVec z) i = (A.mulVec x) i := by
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
        have h1 : ∑ j : Fin n, A_split i (Fin.castAdd n j) * z (Fin.castAdd n j) =
            ∑ j : Fin n, A i j * max (x j) 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [A_split, z]
        have h2 : ∑ j : Fin n, A_split i (Fin.natAdd n j) * z (Fin.natAdd n j) =
            ∑ j : Fin n, (-A i j) * max (-x j) 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [A_split, z]
        rw [h1, h2, ← Finset.sum_add_distrib, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hxp : max (x j) 0 - max (-x j) 0 = x j := by
          rcases le_total 0 (x j) with hx | hx <;> simp [hx]
        calc A i j * max (x j) 0 + -A i j * max (-x j) 0
            = A i j * (max (x j) 0 - max (-x j) 0) := by ring
          _ = A i j * x j := by rw [hxp]
      rw [hmul]; exact hAx i
    · rintro ⟨z, _, hAz⟩
      let x : Fin n → ℝ := fun j => z (Fin.castAdd n j) - z (Fin.natAdd n j)
      refine ⟨x, fun i => ?_⟩
      have hmul : (A.mulVec x) i = (A_split.mulVec z) i := by
        rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
        have h1 : ∑ j : Fin n, A_split i (Fin.castAdd n j) * z (Fin.castAdd n j) =
            ∑ j : Fin n, A i j * z (Fin.castAdd n j) := by
          refine Finset.sum_congr rfl fun j _ => by simp [A_split]
        have h2 : ∑ j : Fin n, A_split i (Fin.natAdd n j) * z (Fin.natAdd n j) =
            ∑ j : Fin n, (-A i j) * z (Fin.natAdd n j) := by
          refine Finset.sum_congr rfl fun j _ => by simp [A_split]
        rw [h1, h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by simp [x]; ring
      rw [hmul]; exact hAz i
  have heq_d : (∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ Aᵀ.mulVec y = 0 ∧ y ⬝ᵥ b < 0) ↔
      (∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, 0 ≤ (A_splitᵀ.mulVec y) k) ∧ y ⬝ᵥ b < 0) := by
    refine exists_congr fun y => and_congr_right fun _ => and_congr_left fun _ => ?_
    constructor
    · intro h0 k
      by_cases hk : k.1 < n
      · have heq : (A_splitᵀ.mulVec y) k = (Aᵀ.mulVec y) ⟨k.1, hk⟩ := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          refine Finset.sum_congr rfl fun i _ => by simp [A_split, hk]
        rw [heq, h0]; simp
      · have heq : (A_splitᵀ.mulVec y) k = - (Aᵀ.mulVec y) ⟨k.1 - n, by omega⟩ := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => by simp [A_split, hk]
        rw [heq, h0]; simp
    · intro hge
      ext j
      have hpos := hge (Fin.castAdd n j)
      have hneg := hge (Fin.natAdd n j)
      have h1 : (A_splitᵀ.mulVec y) (Fin.castAdd n j) = (Aᵀ.mulVec y) j := by
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun i _ => by simp [A_split]
      have h2 : (A_splitᵀ.mulVec y) (Fin.natAdd n j) = - (Aᵀ.mulVec y) j := by
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => by simp [A_split]
      simp only [Pi.zero_apply]
      linarith
  rw [heq_p, heq_d]
  exact farkas_lemma_nonneg_le A_split b

end SeparationAndFarkas

/-! ## Section 2: Linear Programming Duality & Complementary Slackness -/

section LinearProgramming

/-- **LP Weak Duality**: for primal feasible `x ≥ 0, A *ᵥ x ≤ b` and dual feasible
`y ≥ 0, c ≤ Aᵀ *ᵥ y`, we have `c ⬝ᵥ x ≤ b ⬝ᵥ y`. -/
theorem lp_weak_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} (hx0 : ∀ j, 0 ≤ x j) (hxA : ∀ i, (A.mulVec x) i ≤ b i)
    {y : Fin m → ℝ} (hy0 : ∀ i, 0 ≤ y i) (hyA : ∀ j, c j ≤ (Aᵀ.mulVec y) j) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  have h1 : c ⬝ᵥ x ≤ Aᵀ.mulVec y ⬝ᵥ x :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hyA j) (hx0 j)
  have h2 : Aᵀ.mulVec y ⬝ᵥ x = y ⬝ᵥ A.mulVec x := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have h3 : y ⬝ᵥ A.mulVec x ≤ y ⬝ᵥ b :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxA i) (hy0 i)
  have h4 : y ⬝ᵥ b = b ⬝ᵥ y := dotProduct_comm y b
  linarith

/-- **Complementary Slackness Theorem**: for primal feasible `x` and dual feasible `y`,
equality `c ⬝ᵥ x = b ⬝ᵥ y` holds if and only if both primal and dual complementary slackness
conditions hold (and implies both `x` and `y` are optimal). -/
theorem lp_complementary_slackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} (hx0 : ∀ j, 0 ≤ x j) (hxA : ∀ i, (A.mulVec x) i ≤ b i)
    {y : Fin m → ℝ} (hy0 : ∀ i, 0 ≤ y i) (hyA : ∀ j, c j ≤ (Aᵀ.mulVec y) j) :
    c ⬝ᵥ x = b ⬝ᵥ y ↔
      (∀ j, x j * ((Aᵀ.mulVec y) j - c j) = 0) ∧
        (∀ i, y i * (b i - (A.mulVec x) i) = 0) := by
  have hdiff : b ⬝ᵥ y - c ⬝ᵥ x =
      (∑ j : Fin n, x j * ((Aᵀ.mulVec y) j - c j)) +
        ∑ i : Fin m, y i * (b i - (A.mulVec x) i) := by
    have hdot : Aᵀ.mulVec y ⬝ᵥ x = y ⬝ᵥ A.mulVec x := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    have hs1 : ∑ j : Fin n, x j * ((Aᵀ.mulVec y) j - c j) = Aᵀ.mulVec y ⬝ᵥ x - c ⬝ᵥ x := by
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hs2 : ∑ i : Fin m, y i * (b i - (A.mulVec x) i) = b ⬝ᵥ y - y ⬝ᵥ A.mulVec x := by
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith
  have hnonneg1 : ∀ j : Fin n, 0 ≤ x j * ((Aᵀ.mulVec y) j - c j) := fun j =>
    mul_nonneg (hx0 j) (sub_nonneg.mpr (hyA j))
  have hnonneg2 : ∀ i : Fin m, 0 ≤ y i * (b i - (A.mulVec x) i) := fun i =>
    mul_nonneg (hy0 i) (sub_nonneg.mpr (hxA i))
  have hS1_nonneg : 0 ≤ ∑ j : Fin n, x j * ((Aᵀ.mulVec y) j - c j) :=
    Finset.sum_nonneg fun j _ => hnonneg1 j
  have hS2_nonneg : 0 ≤ ∑ i : Fin m, y i * (b i - (A.mulVec x) i) :=
    Finset.sum_nonneg fun i _ => hnonneg2 i
  constructor
  · intro heq
    have hsum0 : (∑ j : Fin n, x j * ((Aᵀ.mulVec y) j - c j)) +
        ∑ i : Fin m, y i * (b i - (A.mulVec x) i) = 0 := by linarith
    have hs1_0 : ∑ j : Fin n, x j * ((Aᵀ.mulVec y) j - c j) = 0 := by linarith
    have hs2_0 : ∑ i : Fin m, y i * (b i - (A.mulVec x) i) = 0 := by linarith
    exact ⟨fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg1 k)).mp hs1_0 j
        (Finset.mem_univ j),
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg2 k)).mp hs2_0 i
        (Finset.mem_univ i)⟩
  · rintro ⟨h1, h2⟩
    have hs1_0 : ∑ j : Fin n, x j * ((Aᵀ.mulVec y) j - c j) = 0 :=
      Finset.sum_eq_zero fun j _ => h1 j
    have hs2_0 : ∑ i : Fin m, y i * (b i - (A.mulVec x) i) = 0 :=
      Finset.sum_eq_zero fun i _ => h2 i
    linarith

private noncomputable def lpMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : Matrix (Fin (m + n + 1)) (Fin (n + m)) ℝ :=
  fun r col =>
    if hr1 : r.1 < m then
      if hc1 : col.1 < n then A ⟨r.1, hr1⟩ ⟨col.1, hc1⟩ else 0
    else if hr2 : r.1 < m + n then
      if hc1 : col.1 < n then 0 else -A ⟨col.1 - n, by omega⟩ ⟨r.1 - m, by omega⟩
    else
      if hc1 : col.1 < n then -c ⟨col.1, hc1⟩ else b ⟨col.1 - n, by omega⟩

private noncomputable def lpRhs {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Fin (m + n + 1) → ℝ := fun r =>
  if hr1 : r.1 < m then b ⟨r.1, hr1⟩
  else if hr2 : r.1 < m + n then -c ⟨r.1 - m, by omega⟩
  else 0

private lemma lpMat_top_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    lpMat A b c ((Fin.castAdd n i).castSucc) (Fin.castAdd m j) = A i j := by
  dsimp only [lpMat]
  rw [dif_pos (by simp [i.isLt]), dif_pos (by simp [j.isLt])]
  rfl

private lemma lpMat_top_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (i : Fin m) (r : Fin m) :
    lpMat A b c ((Fin.castAdd n i).castSucc) (Fin.natAdd n r) = 0 := by
  dsimp only [lpMat]
  rw [dif_pos (by simp [i.isLt]), dif_neg (by simp)]

private lemma lpMat_mid_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (j : Fin n) (r : Fin n) :
    lpMat A b c ((Fin.natAdd m j).castSucc) (Fin.castAdd m r) = 0 := by
  dsimp only [lpMat]
  rw [dif_neg (by simp), dif_pos (by simp [j.isLt]), dif_pos (by simp [r.isLt])]

private lemma lpMat_mid_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (j : Fin n) (i : Fin m) :
    lpMat A b c ((Fin.natAdd m j).castSucc) (Fin.natAdd n i) = -A i j := by
  dsimp only [lpMat]
  rw [dif_neg (by simp), dif_pos (by simp [j.isLt]), dif_neg (by simp)]
  congr 1; apply congrArg₂ A (Fin.ext (by simp)) (Fin.ext (by simp))

private lemma lpMat_bot_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (j : Fin n) :
    lpMat A b c (Fin.last (m + n)) (Fin.castAdd m j) = -c j := by
  dsimp only [lpMat]
  rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp [j.isLt])]
  rfl

private lemma lpMat_bot_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (i : Fin m) :
    lpMat A b c (Fin.last (m + n)) (Fin.natAdd n i) = b i := by
  dsimp only [lpMat]
  rw [dif_neg (by simp), dif_neg (by simp), dif_neg (by simp)]
  congr 1; exact Fin.ext (by simp)

private lemma lpRhs_top {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) (i : Fin m) :
    lpRhs b c ((Fin.castAdd n i).castSucc) = b i := by
  dsimp only [lpRhs]; rw [dif_pos (by simp [i.isLt])]; rfl

private lemma lpRhs_mid {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) (j : Fin n) :
    lpRhs b c ((Fin.natAdd m j).castSucc) = -c j := by
  dsimp only [lpRhs]; rw [dif_neg (by simp), dif_pos (by simp [j.isLt])]
  congr 1; apply congrArg c; exact Fin.ext (by simp)

private lemma lpRhs_bot {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) :
    lpRhs b c (Fin.last (m + n)) = 0 := by
  dsimp only [lpRhs]; rw [dif_neg (by simp), dif_neg (by simp)]

/-- **LP Strong Duality Theorem**: if both the primal (`x ≥ 0, A *ᵥ x ≤ b`) and dual
(`y ≥ 0, c ≤ Aᵀ *ᵥ y`) are feasible, then there exist primal-feasible `x*` and dual-feasible
`y*` attaining equal objective values `c ⬝ᵥ x* = b ⬝ᵥ y*`. -/
theorem lp_strong_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x₀ : Fin n → ℝ, (∀ j, 0 ≤ x₀ j) ∧ ∀ i, (A.mulVec x₀) i ≤ b i)
    (hD : ∃ y₀ : Fin m → ℝ, (∀ i, 0 ≤ y₀ i) ∧ ∀ j, c j ≤ (Aᵀ.mulVec y₀) j) :
    ∃ x : Fin n → ℝ, ∃ y : Fin m → ℝ,
      ((∀ j, 0 ≤ x j) ∧ ∀ i, (A.mulVec x) i ≤ b i) ∧
      ((∀ i, 0 ≤ y i) ∧ ∀ j, c j ≤ (Aᵀ.mulVec y) j) ∧
      c ⬝ᵥ x = b ⬝ᵥ y := by
  let M := lpMat A b c
  let rhs := lpRhs b c
  have hfeas : ∃ z : Fin (n + m) → ℝ, (∀ col, 0 ≤ z col) ∧ ∀ r, (M.mulVec z) r ≤ rhs r := by
    rw [farkas_lemma_nonneg_le M rhs]
    rintro ⟨w, hw0, hwM, hwb⟩
    let u : Fin m → ℝ := fun i => w ((Fin.castAdd n i).castSucc)
    let v : Fin n → ℝ := fun j => w ((Fin.natAdd m j).castSucc)
    let t : ℝ := w (Fin.last (m + n))
    have hu0 : ∀ i, 0 ≤ u i := fun i => hw0 _
    have hv0 : ∀ j, 0 ≤ v j := fun j => hw0 _
    have ht0 : 0 ≤ t := hw0 _
    have hw_dot : u ⬝ᵥ b - v ⬝ᵥ c < 0 := by
      have heq : w ⬝ᵥ rhs = u ⬝ᵥ b - v ⬝ᵥ c := by
        rw [dotProduct, Fin.sum_univ_castSucc, Fin.sum_univ_add]
        have hlast : w (Fin.last (m + n)) * rhs (Fin.last (m + n)) = 0 := by
          dsimp only [rhs]; rw [lpRhs_bot, mul_zero]
        have hm_sum : ∑ i : Fin m, w ((Fin.castAdd n i).castSucc) *
              rhs ((Fin.castAdd n i).castSucc) = u ⬝ᵥ b := by
          simp only [dotProduct]
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only [rhs]; rw [lpRhs_top]
        have hn_sum : ∑ j : Fin n, w ((Fin.natAdd m j).castSucc) *
              rhs ((Fin.natAdd m j).castSucc) = -(v ⬝ᵥ c) := by
          simp only [dotProduct, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [rhs]; rw [lpRhs_mid]; simp [v]
        rw [hm_sum, hn_sum, hlast]; ring
      linarith
    have hAu : ∀ j, t * c j ≤ (Aᵀ.mulVec u) j := by
      intro j
      have hj := hwM (Fin.castAdd m j)
      have heq : (Mᵀ.mulVec w) (Fin.castAdd m j) = (Aᵀ.mulVec u) j - t * c j := by
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.sum_univ_add]
        have hlast : Mᵀ (Fin.castAdd m j) (Fin.last (m + n)) * w (Fin.last (m + n)) = -t * c j := by
          rw [Matrix.transpose_apply]; dsimp only [M]; rw [lpMat_bot_left]; ring
        have hm_sum : ∑ i : Fin m, Mᵀ (Fin.castAdd m j) ((Fin.castAdd n i).castSucc) *
              w ((Fin.castAdd n i).castSucc) = (Aᵀ.mulVec u) j := by
          rw [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.transpose_apply]; dsimp only [M]; rw [lpMat_top_left]; rfl
        have hn_sum : ∑ r : Fin n, Mᵀ (Fin.castAdd m j) ((Fin.natAdd m r).castSucc) *
              w ((Fin.natAdd m r).castSucc) = 0 := by
          refine Finset.sum_eq_zero fun r _ => ?_
          rw [Matrix.transpose_apply]; dsimp only [M]; rw [lpMat_mid_left, zero_mul]
        rw [hm_sum, hn_sum, hlast]; ring
      linarith
    have hAv : ∀ i, (A.mulVec v) i ≤ t * b i := by
      intro i
      have hi := hwM (Fin.natAdd n i)
      have heq : (Mᵀ.mulVec w) (Fin.natAdd n i) = t * b i - (A.mulVec v) i := by
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.sum_univ_add]
        have hlast : Mᵀ (Fin.natAdd n i) (Fin.last (m + n)) * w (Fin.last (m + n)) = t * b i := by
          rw [Matrix.transpose_apply]; dsimp only [M]; rw [lpMat_bot_right]; ring
        have hm_sum : ∑ r : Fin m, Mᵀ (Fin.natAdd n i) ((Fin.castAdd n r).castSucc) *
              w ((Fin.castAdd n r).castSucc) = 0 := by
          refine Finset.sum_eq_zero fun r _ => ?_
          rw [Matrix.transpose_apply]; dsimp only [M]; rw [lpMat_top_right, zero_mul]
        have hn_sum : ∑ j : Fin n, Mᵀ (Fin.natAdd n i) ((Fin.natAdd m j).castSucc) *
              w ((Fin.natAdd m j).castSucc) = -(A.mulVec v) i := by
          rw [Matrix.mulVec, dotProduct, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.transpose_apply]; dsimp only [M]; rw [lpMat_mid_right]; simp [v]
        rw [hm_sum, hn_sum, hlast]; ring
      linarith
    by_cases ht_pos : 0 < t
    · let x' : Fin n → ℝ := fun j => v j / t
      let y' : Fin m → ℝ := fun i => u i / t
      have hx'0 : ∀ j, 0 ≤ x' j := fun j => div_nonneg (hv0 j) ht_pos.le
      have hy'0 : ∀ i, 0 ≤ y' i := fun i => div_nonneg (hu0 i) ht_pos.le
      have hx'A : ∀ i, (A.mulVec x') i ≤ b i := fun i => by
        have : (A.mulVec x') i = (A.mulVec v) i / t := by
          simp [x', Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
        rw [this, div_le_iff₀ ht_pos]; linarith [hAv i]
      have hy'A : ∀ j, c j ≤ (Aᵀ.mulVec y') j := fun j => by
        have : (Aᵀ.mulVec y') j = (Aᵀ.mulVec u) j / t := by
          simp [y', Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
        rw [this, le_div_iff₀ ht_pos]; linarith [hAu j]
      have hweak := lp_weak_duality A b c hx'0 hx'A hy'0 hy'A
      have hc_eq : c ⬝ᵥ x' = (v ⬝ᵥ c) / t := by
        simp [x', dotProduct, Finset.sum_div, mul_div_assoc, mul_comm]
      have hb_eq : b ⬝ᵥ y' = (u ⬝ᵥ b) / t := by
        simp [y', dotProduct, Finset.sum_div, mul_div_assoc, mul_comm]
      rw [hc_eq, hb_eq, div_le_div_iff_of_pos_right ht_pos] at hweak
      linarith
    · have ht_zero : t = 0 := le_antisymm (not_lt.mp ht_pos) ht0
      rcases hP with ⟨x₀, hx₀0, hx₀A⟩
      rcases hD with ⟨y₀, hy₀0, hy₀A⟩
      have hAu0 : ∀ j, 0 ≤ (Aᵀ.mulVec u) j := fun j => by simpa [ht_zero] using hAu j
      have hAv0 : ∀ i, (A.mulVec v) i ≤ 0 := fun i => by simpa [ht_zero] using hAv i
      have hu_b : 0 ≤ u ⬝ᵥ b := by
        have h1 : 0 ≤ Aᵀ.mulVec u ⬝ᵥ x₀ :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hAu0 j) (hx₀0 j)
        have h2 : Aᵀ.mulVec u ⬝ᵥ x₀ = u ⬝ᵥ A.mulVec x₀ := by
          rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
        have h3 : u ⬝ᵥ A.mulVec x₀ ≤ u ⬝ᵥ b :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx₀A i) (hu0 i)
        linarith
      have hv_c : v ⬝ᵥ c ≤ 0 := by
        have h1 : v ⬝ᵥ c ≤ v ⬝ᵥ Aᵀ.mulVec y₀ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy₀A j) (hv0 j)
        have h2 : v ⬝ᵥ Aᵀ.mulVec y₀ = y₀ ⬝ᵥ A.mulVec v := by
          rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
        have h3 : y₀ ⬝ᵥ A.mulVec v ≤ 0 :=
          Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy₀0 i) (hAv0 i)
        linarith
      linarith
  rcases hfeas with ⟨z, hz0, hzM⟩
  let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let y : Fin m → ℝ := fun i => z (Fin.natAdd n i)
  have hx0 : ∀ j, 0 ≤ x j := fun j => hz0 _
  have hy0 : ∀ i, 0 ≤ y i := fun i => hz0 _
  have hxA : ∀ i, (A.mulVec x) i ≤ b i := by
    intro i
    have hi := hzM ((Fin.castAdd n i).castSucc)
    have heq : (M.mulVec z) ((Fin.castAdd n i).castSucc) = (A.mulVec x) i := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      have h1 : ∑ j : Fin n, M ((Fin.castAdd n i).castSucc) (Fin.castAdd m j) *
            z (Fin.castAdd m j) = (A.mulVec x) i := by
        rw [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [M]; rw [lpMat_top_left]
      have h2 : ∑ r : Fin m, M ((Fin.castAdd n i).castSucc) (Fin.natAdd n r) *
            z (Fin.natAdd n r) = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        dsimp only [M]; rw [lpMat_top_right, zero_mul]
      rw [h1, h2, add_zero]
    have hrhs : rhs ((Fin.castAdd n i).castSucc) = b i := lpRhs_top b c i
    linarith
  have hyA : ∀ j, c j ≤ (Aᵀ.mulVec y) j := by
    intro j
    have hj := hzM ((Fin.natAdd m j).castSucc)
    have heq : (M.mulVec z) ((Fin.natAdd m j).castSucc) = -(Aᵀ.mulVec y) j := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      have h1 : ∑ r : Fin n, M ((Fin.natAdd m j).castSucc) (Fin.castAdd m r) *
            z (Fin.castAdd m r) = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        dsimp only [M]; rw [lpMat_mid_left, zero_mul]
      have h2 : ∑ i : Fin m, M ((Fin.natAdd m j).castSucc) (Fin.natAdd n i) *
            z (Fin.natAdd n i) = -(Aᵀ.mulVec y) j := by
        rw [Matrix.mulVec, dotProduct, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [M]; rw [lpMat_mid_right]; simp [y, Matrix.transpose_apply]
      rw [h1, h2, zero_add]
    have hrhs : rhs ((Fin.natAdd m j).castSucc) = -c j := lpRhs_mid b c j
    linarith
  have hobj : b ⬝ᵥ y ≤ c ⬝ᵥ x := by
    have hlast := hzM (Fin.last (m + n))
    have heq : (M.mulVec z) (Fin.last (m + n)) = b ⬝ᵥ y - c ⬝ᵥ x := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      have h1 : ∑ j : Fin n, M (Fin.last (m + n)) (Fin.castAdd m j) * z (Fin.castAdd m j) =
          -(c ⬝ᵥ x) := by
        rw [dotProduct, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [M]; rw [lpMat_bot_left]; simp [x]
      have h2 : ∑ i : Fin m, M (Fin.last (m + n)) (Fin.natAdd n i) * z (Fin.natAdd n i) =
          b ⬝ᵥ y := by
        rw [dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [M]; rw [lpMat_bot_right]
      rw [h1, h2]; ring
    have hrhs : rhs (Fin.last (m + n)) = 0 := lpRhs_bot b c
    linarith
  have hweak := lp_weak_duality A b c hx0 hxA hy0 hyA
  exact ⟨x, y, ⟨hx0, hxA⟩, ⟨hy0, hyA⟩, le_antisymm hweak hobj⟩

end LinearProgramming

/-! ## Section 3: Von Neumann's Minimax Theorem (1928) -/

section Minimax

/-- **Von Neumann's Minimax Theorem (Saddle-Point Form, 1928)**:
for every real payoff matrix `A : Matrix (Fin m) (Fin n) ℝ` with `0 < m` and `0 < n`,
there exist probability distributions `p* ∈ Δ_m` and `q* ∈ Δ_n` and value `v* : ℝ` such that
`p ⬝ᵥ A *ᵥ q* ≤ v* ≤ p* ⬝ᵥ A *ᵥ q` for all `p ∈ Δ_m` and `q ∈ Δ_n` (and `p* ⬝ᵥ A *ᵥ q* = v*`). -/
theorem von_neumann_minimax_saddle {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ pStar : Fin m → ℝ, ∃ qStar : Fin n → ℝ, ∃ vStar : ℝ,
      ((∀ i, 0 ≤ pStar i) ∧ ∑ i : Fin m, pStar i = 1) ∧
      ((∀ j, 0 ≤ qStar j) ∧ ∑ j : Fin n, qStar j = 1) ∧
      (∀ p : Fin m → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → p ⬝ᵥ A.mulVec qStar ≤ vStar) ∧
      (∀ q : Fin n → ℝ, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 → vStar ≤ pStar ⬝ᵥ A.mulVec q) ∧
      pStar ⬝ᵥ A.mulVec qStar = vStar := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let M : ℝ := (Finset.univ : Finset (Fin m × Fin n)).sup' Finset.univ_nonempty
    (fun p => |A p.1 p.2|) + 1
  have hM_pos : 0 < M := by
    have h0 : 0 ≤ (Finset.univ : Finset (Fin m × Fin n)).sup' Finset.univ_nonempty
        (fun p => |A p.1 p.2|) :=
      le_trans (abs_nonneg _) (Finset.le_sup' (fun p => |A p.1 p.2|)
        (Finset.mem_univ (⟨0, hm⟩, ⟨0, hn⟩)))
    linarith
  let B : Matrix (Fin m) (Fin n) ℝ := fun i j => A i j + M
  have hB_ge1 : ∀ i j, 1 ≤ B i j := fun i j => by
    have hle : |A i j| ≤ (Finset.univ : Finset (Fin m × Fin n)).sup' Finset.univ_nonempty
        (fun p => |A p.1 p.2|) :=
      Finset.le_sup' (fun p => |A p.1 p.2|) (Finset.mem_univ (i, j))
    have hneg : -|A i j| ≤ A i j := neg_abs_le (A i j)
    dsimp only [B, M]
    linarith
  let ones_m : Fin m → ℝ := fun _ => 1
  let ones_n : Fin n → ℝ := fun _ => 1
  have hP : ∃ x₀ : Fin n → ℝ, (∀ j, 0 ≤ x₀ j) ∧ ∀ i, (B.mulVec x₀) i ≤ ones_m i :=
    ⟨0, fun _ => le_rfl, fun _ => by simp [ones_m]⟩
  have hD : ∃ y₀ : Fin m → ℝ, (∀ i, 0 ≤ y₀ i) ∧ ∀ j, ones_n j ≤ (Bᵀ.mulVec y₀) j := by
    refine ⟨ones_m, fun _ => zero_le_one, fun j => ?_⟩
    simp only [ones_n, ones_m, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_one]
    have hge_one : (1 : ℝ) ≤ B ⟨0, hm⟩ j := hB_ge1 ⟨0, hm⟩ j
    have hsum_ge : B ⟨0, hm⟩ j ≤ ∑ i : Fin m, B i j :=
      Finset.single_le_sum (fun i _ => le_trans zero_le_one (hB_ge1 i j)) (Finset.mem_univ _)
    linarith
  obtain ⟨x, y, ⟨hx0, hxB⟩, ⟨hy0, hyB⟩, hobj⟩ :=
    lp_strong_duality B ones_m ones_n hP hD
  let V : ℝ := ones_n ⬝ᵥ x
  have hV_eq_y : V = ones_m ⬝ᵥ y := hobj
  have hV_pos : 0 < V := by
    by_contra hlt
    push Not at hlt
    have hy_nonneg_sum : 0 ≤ ∑ i : Fin m, y i := Finset.sum_nonneg fun i _ => hy0 i
    have hy_sum0 : ∑ i : Fin m, y i = 0 := by
      have : V = ∑ i : Fin m, y i := by simpa [ones_m, dotProduct] using hV_eq_y
      linarith
    have hy_all0 : ∀ i : Fin m, y i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hy0 r)).mp hy_sum0 i (Finset.mem_univ i)
    have hB0 : (Bᵀ.mulVec y) ⟨0, hn⟩ = 0 := by
      simp [Matrix.mulVec, dotProduct, hy_all0]
    have hge1 := hyB ⟨0, hn⟩
    simp only [ones_n] at hge1
    linarith
  let pStar : Fin m → ℝ := fun i => y i / V
  let qStar : Fin n → ℝ := fun j => x j / V
  let vStar : ℝ := 1 / V - M
  have hpStar0 : ∀ i, 0 ≤ pStar i := fun i => div_nonneg (hy0 i) hV_pos.le
  have hpStar1 : ∑ i : Fin m, pStar i = 1 := by
    rw [← Finset.sum_div]
    have hyV : ∑ i : Fin m, y i = V := by simpa [ones_m, dotProduct] using hV_eq_y.symm
    rw [hyV, div_self hV_pos.ne']
  have hqStar0 : ∀ j, 0 ≤ qStar j := fun j => div_nonneg (hx0 j) hV_pos.le
  have hqStar1 : ∑ j : Fin n, qStar j = 1 := by
    rw [← Finset.sum_div]
    have hxV : ∑ j : Fin n, x j = V := by simp [V, ones_n, dotProduct]
    rw [hxV, div_self hV_pos.ne']
  have hp_upper : ∀ p : Fin m → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      p ⬝ᵥ A.mulVec qStar ≤ vStar := by
    intro p hp0 hp1
    have hBq : ∀ i : Fin m, (B.mulVec qStar) i ≤ 1 / V := fun i => by
      have h1 : (B.mulVec qStar) i = (B.mulVec x) i / V := by
        simp [qStar, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
      rw [h1]
      exact div_le_div_of_nonneg_right (hxB i) hV_pos.le
    have hpBq : p ⬝ᵥ B.mulVec qStar ≤ 1 / V := by
      calc p ⬝ᵥ B.mulVec qStar
          = ∑ i : Fin m, p i * (B.mulVec qStar) i := rfl
        _ ≤ ∑ i : Fin m, p i * (1 / V) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hBq i) (hp0 i)
        _ = (∑ i : Fin m, p i) * (1 / V) := by rw [← Finset.sum_mul]
        _ = 1 / V := by rw [hp1, one_mul]
    have hshift : p ⬝ᵥ B.mulVec qStar = p ⬝ᵥ A.mulVec qStar + M := by
      simp only [B, Matrix.mulVec, dotProduct, Finset.mul_sum, add_mul, mul_add,
        Finset.sum_add_distrib]
      have hM_sum : ∑ i : Fin m, ∑ j : Fin n, p i * (M * qStar j) = M := by
        calc ∑ i : Fin m, ∑ j : Fin n, p i * (M * qStar j)
            = ∑ i : Fin m, p i * (M * ∑ j : Fin n, qStar j) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← Finset.mul_sum, ← Finset.mul_sum]
          _ = (∑ i : Fin m, p i) * M := by rw [hqStar1, mul_one, ← Finset.sum_mul]
          _ = M := by rw [hp1, one_mul]
      rw [hM_sum]
    linarith
  have hq_lower : ∀ q : Fin n → ℝ, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 →
      vStar ≤ pStar ⬝ᵥ A.mulVec q := by
    intro q hq0 hq1
    have hBp : ∀ j : Fin n, 1 / V ≤ (Bᵀ.mulVec pStar) j := fun j => by
      have h1 : (Bᵀ.mulVec pStar) j = (Bᵀ.mulVec y) j / V := by
        simp [pStar, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
      rw [h1]
      exact div_le_div_of_nonneg_right (hyB j) hV_pos.le
    have hpBq : 1 / V ≤ pStar ⬝ᵥ B.mulVec q := by
      have hdot : pStar ⬝ᵥ B.mulVec q = Bᵀ.mulVec pStar ⬝ᵥ q := by
        rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      rw [hdot]
      calc 1 / V
          = (1 / V) * ∑ j : Fin n, q j := by rw [hq1, mul_one]
        _ = ∑ j : Fin n, (1 / V) * q j := by rw [Finset.mul_sum]
        _ ≤ ∑ j : Fin n, (Bᵀ.mulVec pStar) j * q j :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hBp j) (hq0 j)
    have hshift : pStar ⬝ᵥ B.mulVec q = pStar ⬝ᵥ A.mulVec q + M := by
      simp only [B, Matrix.mulVec, dotProduct, Finset.mul_sum, add_mul, mul_add,
        Finset.sum_add_distrib]
      have hM_sum : ∑ i : Fin m, ∑ j : Fin n, pStar i * (M * q j) = M := by
        calc ∑ i : Fin m, ∑ j : Fin n, pStar i * (M * q j)
            = ∑ i : Fin m, pStar i * (M * ∑ j : Fin n, q j) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← Finset.mul_sum, ← Finset.mul_sum]
          _ = (∑ i : Fin m, pStar i) * M := by rw [hq1, mul_one, ← Finset.sum_mul]
          _ = M := by rw [hpStar1, one_mul]
      rw [hM_sum]
    linarith
  have heq_val : pStar ⬝ᵥ A.mulVec qStar = vStar :=
    le_antisymm (hp_upper pStar hpStar0 hpStar1) (hq_lower qStar hqStar0 hqStar1)
  exact ⟨pStar, qStar, vStar, ⟨hpStar0, hpStar1⟩, ⟨hqStar0, hqStar1⟩, hp_upper, hq_lower, heq_val⟩

/-- **Von Neumann's Minimax Theorem (Value Form)**: `max_{p ∈ Δ_m} min_{q ∈ Δ_n} pᵀ A q =
min_{q ∈ Δ_n} max_{p ∈ Δ_m} pᵀ A q`, stated via the existence of a unique game value `v*`
attained simultaneously as the max-min and min-max over `Δ_m` and `Δ_n`. -/
theorem von_neumann_minimax_value {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ vStar : ℝ,
      (∃ pStar : Fin m → ℝ, (∀ i, 0 ≤ pStar i) ∧ ∑ i, pStar i = 1 ∧
        ∀ q : Fin n → ℝ, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 → vStar ≤ pStar ⬝ᵥ A.mulVec q) ∧
      (∃ qStar : Fin n → ℝ, (∀ j, 0 ≤ qStar j) ∧ ∑ j, qStar j = 1 ∧
        ∀ p : Fin m → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → p ⬝ᵥ A.mulVec qStar ≤ vStar) := by
  obtain ⟨pStar, qStar, vStar, hp, hq, hup, hlo, _⟩ := von_neumann_minimax_saddle hm hn A
  exact ⟨vStar, ⟨pStar, hp.1, hp.2, hlo⟩, ⟨qStar, hq.1, hq.2, hup⟩⟩

end Minimax

/-! ## Section 4: Birkhoff–von Neumann Theorem (1946) -/

section BirkhoffVonNeumann

/-- **Hall Positive-Diagonal Lemma for Doubly Scaled Matrices**:
every nonnegative `n × n` matrix `M` with constant positive row and column sums `s > 0`
admits a permutation `σ : Equiv.Perm (Fin n)` with `0 < M i (σ i)` for every `i`. -/
theorem birkhoff_hall_permutation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {s : ℝ} (hs : 0 < s)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j : Fin n, M i j = s)
    (hcol : ∀ j, ∑ i : Fin n, M i j = s) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, 0 < M i (σ i) := by
  classical
  let t : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun j => 0 < M i j)
  have hall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion t).card := by
    intro S
    have hsum_row : s * S.card = ∑ i ∈ S, ∑ j ∈ S.biUnion t, M i j := by
      have h1 : s * S.card = ∑ _i ∈ S, s := by simp [mul_comm]
      rw [h1]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← hrow i]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hjU => ?_
      have hle0 : M i j ≤ 0 := by
        by_contra hpos
        push Not at hpos
        exact hjU (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩⟩)
      exact le_antisymm hle0 (hnonneg i j)
    have hsum_le : ∑ i ∈ S, ∑ j ∈ S.biUnion t, M i j ≤ s * (S.biUnion t).card := by
      have hcomm : ∑ i ∈ S, ∑ j ∈ S.biUnion t, M i j = ∑ j ∈ S.biUnion t, ∑ i ∈ S, M i j :=
        Finset.sum_comm
      rw [hcomm]
      have h2 : ∑ j ∈ S.biUnion t, ∑ i ∈ S, M i j ≤ ∑ j ∈ S.biUnion t, ∑ i : Fin n, M i j :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          fun i _ _ => hnonneg i j
      have h3 : ∑ _j ∈ S.biUnion t, s = s * (S.biUnion t).card := by simp [mul_comm]
      calc ∑ j ∈ S.biUnion t, ∑ i ∈ S, M i j
          ≤ ∑ j ∈ S.biUnion t, ∑ i : Fin n, M i j := h2
        _ = ∑ j ∈ S.biUnion t, s := Finset.sum_congr rfl fun j _ => hcol j
        _ = s * (S.biUnion t).card := h3
    have hmul : s * S.card ≤ s * (S.biUnion t).card := by linarith
    have hnat_real : (S.card : ℝ) ≤ ((S.biUnion t).card : ℝ) :=
      le_of_mul_le_mul_left hmul hs
    exact_mod_cast hnat_real
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  have hf_bij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
  exact (Finset.mem_filter.mp (hf_mem i)).2

private lemma birkhoff_scaled_aux {n : ℕ} (hn_pos : 0 < n) :
    ∀ k : ℕ, ∀ (M : Matrix (Fin n) (Fin n) ℝ) (s : ℝ),
      0 ≤ s →
      (∀ i j, 0 ≤ M i j) →
      (∀ i, ∑ j : Fin n, M i j = s) →
      (∀ j, ∑ i : Fin n, M i j = s) →
      (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 ≠ 0)).card ≤ k →
      ∃ w : Equiv.Perm (Fin n) → ℝ,
        (∀ σ, 0 ≤ w σ) ∧ (∑ σ : Equiv.Perm (Fin n), w σ = s) ∧
          M = ∑ σ : Equiv.Perm (Fin n), w σ • Matrix.of (fun i j => if σ i = j then (1 : ℝ) else 0) := by
  classical
  intro k
  induction k with
  | zero =>
    intro M s hs hnonneg hrow hcol hsupp
    rw [Nat.le_zero, Finset.card_eq_zero] at hsupp
    have hM0 : M = 0 := by
      ext i j
      by_contra hne
      have : (i, j) ∈ Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [hsupp] at this
      exact Finset.notMem_empty _ this
    have hs0 : s = 0 := by
      have hi := hrow ⟨0, hn_pos⟩
      simp [hM0] at hi
      exact hi.symm
    exact ⟨0, fun _ => le_rfl, by simp [hs0], by simp [hM0]⟩
  | succ k ih =>
    intro M s hs hnonneg hrow hcol hsupp
    by_cases hs0 : s = 0
    · have hM0 : M = 0 := by
        ext i j
        have hi := hrow i
        rw [hs0] at hi
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hnonneg i r)).mp hi j (Finset.mem_univ j)
      exact ⟨0, fun _ => le_rfl, by simp [hs0], by simp [hM0]⟩
    have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    obtain ⟨σ, hσ_pos⟩ := birkhoff_hall_permutation M hs_pos hnonneg hrow hcol
    obtain ⟨i₀, _, hi₀_min⟩ :=
      (Finset.univ : Finset (Fin n)).exists_min_image (fun i => M i (σ i))
        ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
    let α : ℝ := M i₀ (σ i₀)
    have hα_pos : 0 < α := hσ_pos i₀
    have hα_le_s : α ≤ s := by
      rw [← hrow i₀]
      exact Finset.single_le_sum (fun j _ => hnonneg i₀ j) (Finset.mem_univ (σ i₀))
    let Pσ : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => if σ i = j then (1 : ℝ) else 0)
    let M' : Matrix (Fin n) (Fin n) ℝ := M - α • Pσ
    have hM'_nonneg : ∀ i j, 0 ≤ M' i j := by
      intro i j
      by_cases hij : σ i = j
      · subst hij
        simp only [M', Pσ, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, ↓reduceIte,
          smul_eq_mul, mul_one, sub_nonneg]
        exact hi₀_min i (Finset.mem_univ i)
      · simp [M', Pσ, hij, hnonneg i j]
    have hM'_row : ∀ i, ∑ j : Fin n, M' i j = s - α := by
      intro i
      simp only [M', Pσ, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
        Finset.sum_sub_distrib, hrow i]
      have hProw : ∑ j : Fin n, α * (if σ i = j then (1 : ℝ) else 0) = α := by
        simp
      rw [hProw]
    have hM'_col : ∀ j, ∑ i : Fin n, M' i j = s - α := by
      intro j
      simp only [M', Pσ, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
        Finset.sum_sub_distrib, hcol j]
      have hPcol : ∑ i : Fin n, α * (if σ i = j then (1 : ℝ) else 0) = α := by
        have huniq : ∑ i : Fin n, α * (if σ i = j then (1 : ℝ) else 0) =
            ∑ i ∈ ({σ.symm j} : Finset (Fin n)), α * (if σ i = j then (1 : ℝ) else 0) := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
          have hne : σ i ≠ j := fun h => hi (by simp [← h])
          simp [hne]
        rw [huniq]
        simp
      rw [hPcol]
    have hM'_supp_sub : Finset.univ.filter (fun p : Fin n × Fin n => M' p.1 p.2 ≠ 0) ⊆
        (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 ≠ 0)).erase (i₀, σ i₀) := by
      intro ⟨i, j⟩ hp
      have hne : M' i j ≠ 0 := (Finset.mem_filter.mp hp).2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · intro heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        apply hne
        simp [M', Pσ, α]
      · intro hM0
        apply hne
        by_cases hij : σ i = j
        · subst hij; linarith [hσ_pos i]
        · simp [M', Pσ, hij, hM0]
    have hM'_card : (Finset.univ.filter (fun p : Fin n × Fin n => M' p.1 p.2 ≠ 0)).card ≤ k := by
      have hmem0 : (i₀, σ i₀) ∈ Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα_pos.ne'⟩
      have h1 := Finset.card_le_card hM'_supp_sub
      have h2 := Finset.card_erase_lt_of_mem hmem0
      omega
    obtain ⟨w', hw'0, hw'sum, hw'eq⟩ :=
      ih M' (s - α) (sub_nonneg.mpr hα_le_s) hM'_nonneg hM'_row hM'_col hM'_card
    let w : Equiv.Perm (Fin n) → ℝ := fun τ => w' τ + if τ = σ then α else 0
    refine ⟨w, fun τ => add_nonneg (hw'0 τ) (by split_ifs <;> linarith), ?_, ?_⟩
    · simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        hw'sum]
      ring
    · calc M = M' + α • Pσ := by simp [M']
        _ = (∑ τ : Equiv.Perm (Fin n), w' τ • Matrix.of (fun i j => if τ i = j then (1 : ℝ) else 0)) +
              α • Pσ := by rw [hw'eq]
        _ = ∑ τ : Equiv.Perm (Fin n), w τ • Matrix.of (fun i j => if τ i = j then (1 : ℝ) else 0) := by
              simp only [w, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
                Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pσ]

/-- **Birkhoff–von Neumann Theorem (1946)**: every `n × n` doubly stochastic matrix `M`
(`M i j ≥ 0`, all row sums `1`, all column sums `1`) is a convex combination of permutation
matrices. -/
theorem birkhoff_von_neumann {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j : Fin n, M i j = 1)
    (hcol : ∀ j, ∑ i : Fin n, M i j = 1) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧ (∑ σ : Equiv.Perm (Fin n), w σ = 1) ∧
        M = ∑ σ : Equiv.Perm (Fin n), w σ • Matrix.of (fun i j => if σ i = j then (1 : ℝ) else 0) := by
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_, ?_⟩
    · have huniq : Fintype.card (Equiv.Perm (Fin 0)) = 1 := by simp
      simp [Finset.sum_const]
    · ext i; exact i.elim0
  exact birkhoff_scaled_aux (Nat.pos_of_ne_zero hn0) _ M 1 zero_le_one hnonneg hrow hcol le_rfl

end BirkhoffVonNeumann

/-! ## Section 5: König–Egerváry, Mirsky & Dilworth Theorems -/

section CombinatorialDuality

/-- **König–Egerváry Weak Duality**: every bipartite matching `M` has cardinality at most
the cardinality `A.card + B.card` of any vertex cover `(A, B)`. -/
theorem konig_egervary_weak {L R : Type*} [DecidableEq L] [DecidableEq R]
    (adj : L → R → Prop)
    {M : Finset (L × R)} (hM_adj : ∀ e ∈ M, adj e.1 e.2)
    (hM_inj1 : (M : Set (L × R)).InjOn Prod.fst)
    (hM_inj2 : (M : Set (L × R)).InjOn Prod.snd)
    {A : Finset L} {B : Finset R} (hcov : ∀ u v, adj u v → u ∈ A ∨ v ∈ B) :
    M.card ≤ A.card + B.card := by
  let M₁ := M.filter (fun e => e.1 ∈ A)
  let M₂ := M.filter (fun e => e.1 ∉ A)
  have hdisj : Disjoint M₁ M₂ := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    exact (Finset.mem_filter.mp he2).2 (Finset.mem_filter.mp he1).2
  have hunion : M₁ ∪ M₂ = M := by
    ext e
    simp only [M₁, M₂, Finset.mem_union, Finset.mem_filter]
    tauto
  have hc1 : M₁.card ≤ A.card := by
    calc M₁.card
        = (M₁.image Prod.fst).card :=
            (Finset.card_image_of_injOn (hM_inj1.mono (Finset.filter_subset _ _))).symm
      _ ≤ A.card := Finset.card_le_card fun u hu => by
          rcases Finset.mem_image.mp hu with ⟨e, he, rfl⟩
          exact (Finset.mem_filter.mp he).2
  have hc2 : M₂.card ≤ B.card := by
    calc M₂.card
        = (M₂.image Prod.snd).card :=
            (Finset.card_image_of_injOn (hM_inj2.mono (Finset.filter_subset _ _))).symm
      _ ≤ B.card := Finset.card_le_card fun v hv => by
          rcases Finset.mem_image.mp hv with ⟨e, he, rfl⟩
          rcases Finset.mem_filter.mp he with ⟨heM, heA⟩
          exact (hcov e.1 e.2 (hM_adj e heM)).resolve_left heA
  calc M.card = (M₁ ∪ M₂).card := by rw [hunion]
    _ = M₁.card + M₂.card := Finset.card_union_of_disjoint hdisj
    _ ≤ A.card + B.card := add_le_add hc1 hc2

/-- **König–Egerváry Theorem (1931)**: in any finite bipartite graph `(L, R, adj)`, the
maximum cardinality of a matching equals the minimum cardinality of a vertex cover. -/
theorem konig_egervary {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (adj : L → R → Prop) [DecidableRel adj] :
    ∃ M : Finset (L × R), ∃ A : Finset L, ∃ B : Finset R,
      (∀ e ∈ M, adj e.1 e.2) ∧
      (M : Set (L × R)).InjOn Prod.fst ∧
      (M : Set (L × R)).InjOn Prod.snd ∧
      (∀ u v, adj u v → u ∈ A ∨ v ∈ B) ∧
      M.card = A.card + B.card := by
  let covers : Finset (Finset L × Finset R) :=
    Finset.univ.filter (fun p => ∀ u v, adj u v → u ∈ p.1 ∨ v ∈ p.2)
  have hcov_ne : covers.Nonempty :=
    ⟨(Finset.univ, Finset.univ),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
  obtain ⟨⟨A, B⟩, hAB_mem, hAB_min⟩ :=
    covers.exists_min_image (fun p => p.1.card + p.2.card) hcov_ne
  have hAB_cov : ∀ u v, adj u v → u ∈ A ∨ v ∈ B := (Finset.mem_filter.mp hAB_mem).2
  let tA : A → Finset {v : R // v ∉ B} := fun a =>
    (Finset.univ : Finset {v : R // v ∉ B}).filter (fun v => adj a.1 v.1)
  have hallA : ∀ S : Finset A, S.card ≤ (S.biUnion tA).card := by
    intro S
    by_contra hlt
    push Not at hlt
    let S_L : Finset L := S.image Subtype.val
    let T_R : Finset R := (S.biUnion tA).image Subtype.val
    have hS_card : S_L.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
    have hT_card : T_R.card = (S.biUnion tA).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    let A' := A \ S_L
    let B' := B ∪ T_R
    have hcov' : ∀ u v, adj u v → u ∈ A' ∨ v ∈ B' := by
      intro u v huv
      by_cases huA' : u ∈ A'
      · exact Or.inl huA'
      · right
        by_cases hvB : v ∈ B
        · exact Finset.mem_union_left _ hvB
        · apply Finset.mem_union_right
          have huA : u ∈ A := (hAB_cov u v huv).resolve_right hvB
          have huS : u ∈ S_L := by
            by_contra hnot
            exact huA' (Finset.mem_sdiff.mpr ⟨huA, hnot⟩)
          rcases Finset.mem_image.mp huS with ⟨a, haS, rfl⟩
          exact Finset.mem_image.mpr ⟨⟨v, hvB⟩,
            Finset.mem_biUnion.mpr ⟨a, haS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩⟩, rfl⟩
    have hmem' : (A', B') ∈ covers := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcov'⟩
    have hmin' := hAB_min (A', B') hmem'
    dsimp only at hmin'
    have hS_sub_A : S_L ⊆ A := fun u hu => by
      rcases Finset.mem_image.mp hu with ⟨a, _, rfl⟩; exact a.2
    have hA'_card : A'.card = A.card - S_L.card := Finset.card_sdiff_of_subset hS_sub_A
    have hB'_card : B'.card ≤ B.card + T_R.card := Finset.card_union_le B T_R
    have hS_le_A : S_L.card ≤ A.card := Finset.card_le_card hS_sub_A
    omega
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective tA).mp hallA
  let tB : B → Finset {u : L // u ∉ A} := fun b =>
    (Finset.univ : Finset {u : L // u ∉ A}).filter (fun u => adj u.1 b.1)
  have hallB : ∀ S : Finset B, S.card ≤ (S.biUnion tB).card := by
    intro S
    by_contra hlt
    push Not at hlt
    let S_R : Finset R := S.image Subtype.val
    let T_L : Finset L := (S.biUnion tB).image Subtype.val
    have hS_card : S_R.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
    have hT_card : T_L.card = (S.biUnion tB).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    let A' := A ∪ T_L
    let B' := B \ S_R
    have hcov' : ∀ u v, adj u v → u ∈ A' ∨ v ∈ B' := by
      intro u v huv
      by_cases hvB' : v ∈ B'
      · exact Or.inr hvB'
      · left
        by_cases huA : u ∈ A
        · exact Finset.mem_union_left _ huA
        · apply Finset.mem_union_right
          have hvB : v ∈ B := (hAB_cov u v huv).resolve_left huA
          have hvS : v ∈ S_R := by
            by_contra hnot
            exact hvB' (Finset.mem_sdiff.mpr ⟨hvB, hnot⟩)
          rcases Finset.mem_image.mp hvS with ⟨b, hbS, rfl⟩
          exact Finset.mem_image.mpr ⟨⟨u, huA⟩,
            Finset.mem_biUnion.mpr ⟨b, hbS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩⟩, rfl⟩
    have hmem' : (A', B') ∈ covers := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcov'⟩
    have hmin' := hAB_min (A', B') hmem'
    dsimp only at hmin'
    have hS_sub_B : S_R ⊆ B := fun v hv => by
      rcases Finset.mem_image.mp hv with ⟨b, _, rfl⟩; exact b.2
    have hB'_card : B'.card = B.card - S_R.card := Finset.card_sdiff_of_subset hS_sub_B
    have hA'_card : A'.card ≤ A.card + T_L.card := Finset.card_union_le A T_L
    have hS_le_B : S_R.card ≤ B.card := Finset.card_le_card hS_sub_B
    omega
  obtain ⟨g, hg_inj, hg_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective tB).mp hallB
  let MA : Finset (L × R) := (Finset.univ : Finset A).map
    ⟨fun a => (a.1, (f a).1), fun a₁ a₂ h => Subtype.ext (congrArg Prod.fst h)⟩
  let MB : Finset (L × R) := (Finset.univ : Finset B).map
    ⟨fun b => ((g b).1, b.1), fun b₁ b₂ h => Subtype.ext (congrArg Prod.snd h)⟩
  have hdisj_M : Disjoint MA MB := by
    rw [Finset.disjoint_left]
    intro e heA heB
    rcases Finset.mem_map.mp heA with ⟨a, _, ha⟩
    rcases Finset.mem_map.mp heB with ⟨b, _, hb⟩
    have heq : a.1 = (g b).1 := (congrArg Prod.fst ha).trans (congrArg Prod.fst hb).symm
    exact (g b).2 (heq ▸ a.2)
  let M : Finset (L × R) := MA ∪ MB
  refine ⟨M, A, B, ?_, ?_, ?_, hAB_cov, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with heA | heB
    · rcases Finset.mem_map.mp heA with ⟨a, _, rfl⟩
      exact (Finset.mem_filter.mp (hf_mem a)).2
    · rcases Finset.mem_map.mp heB with ⟨b, _, rfl⟩
      exact (Finset.mem_filter.mp (hg_mem b)).2
  · intro e₁ he₁ e₂ he₂ heq
    rcases Finset.mem_union.mp he₁ with h1A | h1B <;>
      rcases Finset.mem_union.mp he₂ with h2A | h2B
    · rcases Finset.mem_map.mp h1A with ⟨a₁, _, rfl⟩
      rcases Finset.mem_map.mp h2A with ⟨a₂, _, rfl⟩
      obtain rfl : a₁ = a₂ := Subtype.ext heq; rfl
    · rcases Finset.mem_map.mp h1A with ⟨a₁, _, rfl⟩
      rcases Finset.mem_map.mp h2B with ⟨b₂, _, rfl⟩
      have h_eq : a₁.1 = (g b₂).1 := heq
      exact absurd (h_eq ▸ a₁.2) (g b₂).2
    · rcases Finset.mem_map.mp h1B with ⟨b₁, _, rfl⟩
      rcases Finset.mem_map.mp h2A with ⟨a₂, _, rfl⟩
      have h_eq : a₂.1 = (g b₁).1 := heq.symm
      exact absurd (h_eq ▸ a₂.2) (g b₁).2
    · rcases Finset.mem_map.mp h1B with ⟨b₁, _, rfl⟩
      rcases Finset.mem_map.mp h2B with ⟨b₂, _, rfl⟩
      obtain rfl : b₁ = b₂ := hg_inj (Subtype.ext heq); rfl
  · intro e₁ he₁ e₂ he₂ heq
    rcases Finset.mem_union.mp he₁ with h1A | h1B <;>
      rcases Finset.mem_union.mp he₂ with h2A | h2B
    · rcases Finset.mem_map.mp h1A with ⟨a₁, _, rfl⟩
      rcases Finset.mem_map.mp h2A with ⟨a₂, _, rfl⟩
      obtain rfl : a₁ = a₂ := hf_inj (Subtype.ext heq); rfl
    · rcases Finset.mem_map.mp h1A with ⟨a₁, _, rfl⟩
      rcases Finset.mem_map.mp h2B with ⟨b₂, _, rfl⟩
      have h_eq : (f a₁).1 = b₂.1 := heq
      exact absurd (h_eq ▸ b₂.2) (f a₁).2
    · rcases Finset.mem_map.mp h1B with ⟨b₁, _, rfl⟩
      rcases Finset.mem_map.mp h2A with ⟨a₂, _, rfl⟩
      have h_eq : (f a₂).1 = b₁.1 := heq.symm
      exact absurd (h_eq ▸ b₁.2) (f a₂).2
    · rcases Finset.mem_map.mp h1B with ⟨b₁, _, rfl⟩
      rcases Finset.mem_map.mp h2B with ⟨b₂, _, rfl⟩
      obtain rfl : b₁ = b₂ := Subtype.ext heq; rfl
  · rw [Finset.card_union_of_disjoint hdisj_M]
    simp [MA, MB]

private lemma mirsky_aux {P : Type*} [PartialOrder P] [DecidableEq P] :
    ∀ n : ℕ, ∀ S : Finset P, S.card ≤ n →
      ∃ k : ℕ,
        (∃ C ⊆ S, IsChain (· ≤ ·) (C : Set P) ∧ C.card = k) ∧
        (∀ C ⊆ S, IsChain (· ≤ ·) (C : Set P) → C.card ≤ k) ∧
        (∃ 𝒜 : Finset (Finset P), 𝒜.card ≤ k ∧
          (∀ A ∈ 𝒜, IsAntichain (· ≤ ·) (A : Set P)) ∧ S ⊆ 𝒜.biUnion id) := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Nat.le_zero, Finset.card_eq_zero] at hS
    subst hS
    exact ⟨0, ⟨∅, Finset.Subset.rfl, by simp, rfl⟩,
      fun C hC _ => by rw [Finset.subset_empty.mp hC]; simp,
      ⟨∅, by simp⟩⟩
  | succ n ih =>
    intro S hS
    by_cases hEmpty : S = ∅
    · subst hEmpty
      exact ⟨0, ⟨∅, Finset.Subset.rfl, by simp, rfl⟩,
        fun C hC _ => by rw [Finset.subset_empty.mp hC]; simp,
        ⟨∅, by simp⟩⟩
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let M : Finset P := S.filter (fun x => ∀ y ∈ S, x ≤ y → x = y)
    have hex_max : ∀ x ∈ S, ∃ m ∈ M, x ≤ m := by
      intro x hx
      let above : Finset P := S.filter (fun y => x ≤ y)
      have habove_ne : above.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩
      have hfin_max : ∀ k : ℕ, ∀ T : Finset P, T.Nonempty → T.card ≤ k →
          ∃ m ∈ T, ∀ y ∈ T, m ≤ y → m = y := by
        intro k
        induction k with
        | zero =>
          intro T hT _; have := Finset.card_pos.mpr hT; omega
        | succ k ihk =>
          intro T hT hTk
          by_cases hm : ∃ m ∈ T, ∀ y ∈ T, m ≤ y → m = y
          · exact hm
          · obtain ⟨t, ht⟩ := hT
            push Not at hm
            obtain ⟨y, hyT, hty, hne⟩ := hm t ht
            let T' := (T.erase t).filter (fun z => y ≤ z)
            have hT'_ne : T'.Nonempty :=
              ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne.symm, hyT⟩, le_rfl⟩⟩
            have hT'_card : T'.card ≤ k := by
              have h1 : T'.card ≤ (T.erase t).card := Finset.card_le_card (Finset.filter_subset _ _)
              have h2 : (T.erase t).card < T.card := Finset.card_erase_lt_of_mem ht
              omega
            obtain ⟨m, hmT', hm_max⟩ := ihk T' hT'_ne hT'_card
            have hm_mem : m ∈ T := Finset.erase_subset _ _ (Finset.mem_filter.mp hmT').1
            have hym : y ≤ m := (Finset.mem_filter.mp hmT').2
            refine ⟨m, hm_mem, fun z hzT hmz => ?_⟩
            have htz_ne : z ≠ t := by
              intro rfl
              exact hne (le_antisymm hty (le_trans hym hmz))
            exact hm_max z (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨htz_ne, hzT⟩,
              le_trans hym hmz⟩) hmz
      obtain ⟨m, hm_ab, hm_max⟩ := hfin_max above.card above habove_ne le_rfl
      have hmS : m ∈ S := (Finset.mem_filter.mp hm_ab).1
      have hxm : x ≤ m := (Finset.mem_filter.mp hm_ab).2
      refine ⟨m, Finset.mem_filter.mpr ⟨hmS, fun y hyS hmy => hm_max y
        (Finset.mem_filter.mpr ⟨hyS, le_trans hxm hmy⟩) hmy⟩, hxm⟩
    obtain ⟨m₀, hm₀M, _⟩ := hex_max hSne.choose hSne.choose_spec
    have hM_anti : IsAntichain (· ≤ ·) (M : Set P) := by
      intro x hx y hy hxy hle
      simp only [Finset.mem_coe, M, Finset.mem_filter] at hx hy
      exact hxy (hx.2 y hy.1 hle)
    have hM_sub : M ⊆ S := Finset.filter_subset _ _
    have hS'_card : (S \ M).card ≤ n := by
      have h1 : (S \ M).card = S.card - M.card := Finset.card_sdiff_of_subset hM_sub
      have h2 : 1 ≤ M.card := Finset.one_le_card.mpr ⟨m₀, hm₀M⟩
      omega
    obtain ⟨k', ⟨C', hC'_sub, hC'_chain, hC'_card⟩, hC'_max, ⟨𝒜', h𝒜'_card, h𝒜'_anti, h𝒜'_cov⟩⟩ :=
      ih (S \ M) hS'_card
    refine ⟨k' + 1, ?_, ?_, ?_⟩
    · by_cases hk0 : k' = 0
      · subst hk0
        exact ⟨{m₀}, by simp [hM_sub hm₀M], by simp, by simp⟩
      · have hC'_ne : C'.Nonempty := Finset.card_pos.mp (hC'_card ▸ Nat.pos_of_ne_zero hk0)
        have hC'_tot : ∀ x ∈ C', ∀ y ∈ C', x ≤ y ∨ y ≤ x := fun x hx y hy =>
          hC'_chain.total (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy)
        have hex_top : ∃ c ∈ C', ∀ x ∈ C', x ≤ c := by
          clear hC'_card hC'_max h𝒜'_card h𝒜'_cov hC'_sub hS'_card
          induction C' using Finset.induction_on with
          | empty => exact absurd hC'_ne Finset.not_nonempty_empty
          | @insert a T ha ihT =>
            by_cases hT : T.Nonempty
            · have hT_chain : IsChain (· ≤ ·) (T : Set P) :=
                hC'_chain.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))
              obtain ⟨c, hcT, hc_max⟩ := ihT hT_chain hT (fun x hx y hy =>
                hC'_tot x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
              rcases hC'_tot a (Finset.mem_insert_self _ _) c (Finset.mem_insert_of_mem hcT) with hac | hca
              · refine ⟨c, Finset.mem_insert_of_mem hcT, fun x hx => ?_⟩
                rcases Finset.mem_insert.mp hx with rfl | hxT
                · exact hac
                · exact hc_max x hxT
              · refine ⟨a, Finset.mem_insert_self _ _, fun x hx => ?_⟩
                rcases Finset.mem_insert.mp hx with rfl | hxT
                · exact le_rfl
                · exact le_trans (hc_max x hxT) hca
            · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
              exact ⟨a, Finset.mem_insert_self _ _, fun x hx => by rw [Finset.mem_singleton.mp hx]⟩
        obtain ⟨c_top, hc_top_mem, hc_top_max⟩ := hex_top
        have hc_top_S : c_top ∈ S := (Finset.mem_sdiff.mp (hC'_sub hc_top_mem)).1
        obtain ⟨m, hmM, hcm⟩ := hex_max c_top hc_top_S
        have hm_not_C' : m ∉ C' := fun hmC' => (Finset.mem_sdiff.mp (hC'_sub hmC')).2 hmM
        refine ⟨insert m C', Finset.insert_subset (hM_sub hmM) (hC'_sub.trans Finset.sdiff_subset), ?_, ?_⟩
        · intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact Or.inr (le_trans (hc_top_max y hy) hcm)
          · exact Or.inl (le_trans (hc_top_max x hx) hcm)
          · exact hC'_chain hx hy hxy
        · rw [Finset.card_insert_of_notMem hm_not_C', hC'_card]
    · intro C hC hC_chain
      have hCM_le1 : (C ∩ M).card ≤ 1 := by
        by_contra hgt
        push Not at hgt
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hgt
        have hxC := (Finset.mem_inter.mp hx).1
        have hyC := (Finset.mem_inter.mp hy).1
        have hxM := (Finset.mem_inter.mp hx).2
        have hyM := (Finset.mem_inter.mp hy).2
        rcases hC_chain.total (Finset.mem_coe.mpr hxC) (Finset.mem_coe.mpr hyC) with hle | hle
        · exact hM_anti (Finset.mem_coe.mpr hxM) (Finset.mem_coe.mpr hyM) hxy hle
        · exact hM_anti (Finset.mem_coe.mpr hyM) (Finset.mem_coe.mpr hxM) hxy.symm hle
      have hC_sdiff : C \ M ⊆ S \ M := Finset.sdiff_subset_sdiff hC Finset.Subset.rfl
      have hC_sdiff_chain : IsChain (· ≤ ·) ((C \ M : Finset P) : Set P) :=
        hC_chain.mono (Finset.coe_subset.mpr Finset.sdiff_subset)
      have hle_k' := hC'_max (C \ M) hC_sdiff hC_sdiff_chain
      have hcard_split : (C \ M).card + (C ∩ M).card = C.card :=
        Finset.card_sdiff_add_card_inter C M
      omega
    · refine ⟨insert M 𝒜', le_trans (Finset.card_insert_le M 𝒜') (by omega), ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA'
        · exact hM_anti
        · exact h𝒜'_anti A hA'
      · intro x hx
        by_cases hxM : x ∈ M
        · exact Finset.mem_biUnion.mpr ⟨M, Finset.mem_insert_self _ _, hxM⟩
        · have hx' : x ∈ S \ M := Finset.mem_sdiff.mpr ⟨hx, hxM⟩
          rcases Finset.mem_biUnion.mp (h𝒜'_cov hx') with ⟨A, hA, hxA⟩
          exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_insert_of_mem hA, hxA⟩

/-- **Mirsky's Theorem (1971)**: in any finite subset `S` of a partial order `P`, the maximum
size of a chain in `S` equals the minimum number of antichains covering `S`. -/
theorem mirsky_theorem {P : Type*} [PartialOrder P] [DecidableEq P] (S : Finset P) :
    ∃ k : ℕ,
      (∃ C ⊆ S, IsChain (· ≤ ·) (C : Set P) ∧ C.card = k) ∧
      (∀ C ⊆ S, IsChain (· ≤ ·) (C : Set P) → C.card ≤ k) ∧
      (∃ 𝒜 : Finset (Finset P), 𝒜.card ≤ k ∧
        (∀ A ∈ 𝒜, IsAntichain (· ≤ ·) (A : Set P)) ∧ S ⊆ 𝒜.biUnion id) :=
  mirsky_aux S.card S le_rfl

/-- **Dilworth Weak Duality**: the cardinality of any antichain `U ⊆ S` is at most the number
of chains in any chain cover `𝒞` of `S`. -/
theorem dilworth_weak {P : Type*} [PartialOrder P] [DecidableEq P] {S U : Finset P}
    (hUS : U ⊆ S) (hanti : IsAntichain (· ≤ ·) (U : Set P))
    {𝒞 : Finset (Finset P)} (hchain : ∀ C ∈ 𝒞, IsChain (· ≤ ·) (C : Set P))
    (hcov : S ⊆ 𝒞.biUnion id) :
    U.card ≤ 𝒞.card := by
  have hpick : ∀ u ∈ U, ∃ C ∈ 𝒞, u ∈ C := fun u hu => by
    rcases Finset.mem_biUnion.mp (hcov (hUS hu)) with ⟨C, hC, huC⟩
    exact ⟨C, hC, huC⟩
  choose f hf𝒞 hfu using fun u : U => hpick u.1 u.2
  have hinj : Function.Injective f := by
    intro u₁ u₂ heq
    by_contra hne
    have hne' : u₁.1 ≠ u₂.1 := fun h => hne (Subtype.ext h)
    have hu₁C : u₁.1 ∈ f u₁ := hfu u₁
    have hu₂C : u₂.1 ∈ f u₁ := heq ▸ hfu u₂
    rcases (hchain (f u₁) (hf𝒞 u₁)).total (Finset.mem_coe.mpr hu₁C) (Finset.mem_coe.mpr hu₂C) with
      hle | hle
    · exact hanti (Finset.mem_coe.mpr u₁.2) (Finset.mem_coe.mpr u₂.2) hne' hle
    · exact hanti (Finset.mem_coe.mpr u₂.2) (Finset.mem_coe.mpr u₁.2) hne'.symm hle
  calc U.card
      = (Finset.univ : Finset U).card := (Fintype.card_coe U).symm
    _ = ((Finset.univ : Finset U).image f).card :=
        (Finset.card_image_of_injective Finset.univ hinj).symm
    _ ≤ 𝒞.card := Finset.card_le_card fun C hC => by
        rcases Finset.mem_image.mp hC with ⟨u, _, rfl⟩
        exact hf𝒞 u

private lemma matching_to_chain_cover {P : Type*} [PartialOrder P] [DecidableEq P] :
    ∀ k : ℕ, ∀ (S : Finset P) (M : Finset (P × P)),
      M.card = k →
      (∀ e ∈ M, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2) →
      (M : Set (P × P)).InjOn Prod.fst →
      (M : Set (P × P)).InjOn Prod.snd →
      ∃ 𝒞 : Finset (Finset P),
        (∀ C ∈ 𝒞, C ⊆ S ∧ C.Nonempty ∧ IsChain (· ≤ ·) (C : Set P)) ∧
        (∀ C₁ ∈ 𝒞, ∀ C₂ ∈ 𝒞, C₁ ≠ C₂ → Disjoint C₁ C₂) ∧
        𝒞.card + M.card = S.card ∧
        (∀ x ∈ S, ∃ C ∈ 𝒞, x ∈ C) ∧
        (∀ v ∈ S, (∀ e ∈ M, e.2 ≠ v) → ∃ C ∈ 𝒞, v ∈ C ∧ ∀ w ∈ C, v ≤ w) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S M hM _ _ _
    rw [Finset.card_eq_zero.mp hM]
    let 𝒞 := S.image (fun x => ({x} : Finset P))
    have hinj : Function.Injective (fun x : P => ({x} : Finset P)) := by
      intro x y h
      have hx : x ∈ ({x} : Finset P) := Finset.mem_singleton_self x
      dsimp only at h
      rw [h] at hx
      exact Finset.mem_singleton.mp hx
    refine ⟨𝒞, ?_, ?_, ?_, ?_, ?_⟩
    · intro C hC
      rcases Finset.mem_image.mp hC with ⟨x, hx, rfl⟩
      exact ⟨Finset.singleton_subset_iff.mpr hx, Finset.singleton_nonempty x, by simp⟩
    · intro C₁ h1 C₂ h2 hne
      rcases Finset.mem_image.mp h1 with ⟨x₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨x₂, _, rfl⟩
      have hxne : x₁ ≠ x₂ := fun h => hne (by rw [h])
      simp [hxne]
    · simp [𝒞, Finset.card_image_of_injective S hinj]
    · intro x hx
      exact ⟨{x}, Finset.mem_image_of_mem _ hx, Finset.mem_singleton_self x⟩
    · intro v hv _
      refine ⟨{v}, Finset.mem_image_of_mem _ hv, Finset.mem_singleton_self v, fun w hw => ?_⟩
      rw [Finset.mem_singleton.mp hw]
  | succ k ih =>
    intro S M hM hM_prop hM_inj1 hM_inj2
    have hM_ne : M.Nonempty := Finset.card_pos.mp (by omega)
    let sources := M.image Prod.fst
    have hsrc_ne : sources.Nonempty := hM_ne.image Prod.fst
    have hex_min : ∃ u ∈ sources, ∀ w ∈ sources, w ≤ u → w = u := by
      have hmin_aux : ∀ m : ℕ, ∀ T : Finset P, T.Nonempty → T.card ≤ m →
          ∃ u ∈ T, ∀ w ∈ T, w ≤ u → w = u := by
        intro m
        induction m with
        | zero =>
          intro T hT _; have := Finset.card_pos.mpr hT; omega
        | succ m ihm =>
          intro T hT hm
          by_cases hu : ∃ u ∈ T, ∀ w ∈ T, w ≤ u → w = u
          · exact hu
          · obtain ⟨t, ht⟩ := hT
            push Not at hu
            obtain ⟨w, hwT, hwt, hne⟩ := hu t ht
            let T' := (T.erase t).filter (fun z => z ≤ w)
            have hT'_ne : T'.Nonempty :=
              ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hwT⟩, le_rfl⟩⟩
            have hT'_card : T'.card ≤ m := by
              have h1 : T'.card ≤ (T.erase t).card := Finset.card_le_card (Finset.filter_subset _ _)
              have h2 : (T.erase t).card < T.card := Finset.card_erase_lt_of_mem ht
              omega
            obtain ⟨u, huT', hu_min⟩ := ihm T' hT'_ne hT'_card
            have huT : u ∈ T := Finset.erase_subset _ _ (Finset.mem_filter.mp huT').1
            have huw : u ≤ w := (Finset.mem_filter.mp huT').2
            refine ⟨u, huT, fun z hzT hzu => ?_⟩
            have hzt : z ≠ t := by
              intro rfl
              exact hne (le_antisymm hwt (le_trans hzu huw))
            exact hu_min z (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzt, hzT⟩,
              le_trans hzu huw⟩) hzu
      exact hmin_aux sources.card sources hsrc_ne le_rfl
    obtain ⟨u, hu_src, hu_min⟩ := hex_min
    rcases Finset.mem_image.mp hu_src with ⟨⟨u', v⟩, huv_mem, rfl⟩
    have huv_prop := hM_prop (u', v) huv_mem
    have hu_S : u' ∈ S := huv_prop.1
    have hv_S : v ∈ S := huv_prop.2.1
    have huv_lt : u' < v := huv_prop.2.2
    have hno_in_u : ∀ e ∈ M, e.2 ≠ u' := by
      intro e heM he2
      have he_prop := hM_prop e heM
      have he1_src : e.1 ∈ sources := Finset.mem_image_of_mem Prod.fst heM
      have he1_lt : e.1 < u' := he2 ▸ he_prop.2.2
      exact he1_lt.ne (hu_min e.1 he1_src he1_lt.le)
    let S' := S.erase u'
    let M' := M.erase (u', v)
    have hM'_card : M'.card = k := by
      rw [Finset.card_erase_of_mem huv_mem, hM]; simp
    have hM'_prop : ∀ e ∈ M', e.1 ∈ S' ∧ e.2 ∈ S' ∧ e.1 < e.2 := by
      intro e he'
      have heM : e ∈ M := Finset.erase_subset _ _ he'
      have he_ne : e ≠ (u', v) := Finset.ne_of_mem_erase he'
      have he_p := hM_prop e heM
      have he1_ne : e.1 ≠ u' := fun h => he_ne (hM_inj1 heM huv_mem h)
      have he2_ne : e.2 ≠ u' := hno_in_u e heM
      exact ⟨Finset.mem_erase.mpr ⟨he1_ne, he_p.1⟩, Finset.mem_erase.mpr ⟨he2_ne, he_p.2.1⟩,
        he_p.2.2⟩
    have hv_S' : v ∈ S' := Finset.mem_erase.mpr ⟨huv_lt.ne.symm, hv_S⟩
    have hno_in_v : ∀ e ∈ M', e.2 ≠ v := by
      intro e he' he2
      have heM : e ∈ M := Finset.erase_subset _ _ he'
      have he_ne : e ≠ (u', v) := Finset.ne_of_mem_erase he'
      exact he_ne (hM_inj2 heM huv_mem he2)
    obtain ⟨𝒞', h𝒞'_chain, h𝒞'_disj, h𝒞'_card, h𝒞'_cov, h𝒞'_min⟩ :=
      ih S' M' hM'_card hM'_prop (hM_inj1.mono (Finset.erase_subset _ _))
        (hM_inj2.mono (Finset.erase_subset _ _))
    obtain ⟨Cv, hCv_mem, hv_Cv, hv_min⟩ := h𝒞'_min v hv_S' hno_in_v
    let Cnew := insert u' Cv
    let 𝒞 := insert Cnew (𝒞'.erase Cv)
    have hu_not_mem : ∀ C ∈ 𝒞', u' ∉ C := fun C hC huC =>
      Finset.notMem_erase u' S ((h𝒞'_chain C hC).1 huC)
    have hCnew_not_mem : Cnew ∉ 𝒞'.erase Cv := by
      intro hmem
      have hCnew_C' : Cnew ∈ 𝒞' := Finset.erase_subset _ _ hmem
      exact hu_not_mem Cnew hCnew_C' (Finset.mem_insert_self u' Cv)
    refine ⟨𝒞, ?_, ?_, ?_, ?_, ?_⟩
    · intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC'
      · refine ⟨Finset.insert_subset hu_S ((h𝒞'_chain Cv hCv_mem).1.trans (Finset.erase_subset _ _)),
          Finset.insert_nonempty u' Cv, ?_⟩
        intro x hx y hy hxy
        simp only [Cnew, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact Or.inl (le_trans huv_lt.le (hv_min y hy))
        · exact Or.inr (le_trans huv_lt.le (hv_min x hx))
        · exact (h𝒞'_chain Cv hCv_mem).2.2 hx hy hxy
      · have hC_C' := Finset.erase_subset _ _ hC'
        have hP := h𝒞'_chain C hC_C'
        exact ⟨hP.1.trans (Finset.erase_subset _ _), hP.2⟩
    · intro C₁ h1 C₂ h2 hne
      rcases Finset.mem_insert.mp h1 with rfl | h1' <;>
        rcases Finset.mem_insert.mp h2 with rfl | h2'
      · exact absurd rfl hne
      · have h2C' := Finset.erase_subset _ _ h2'
        have h2_ne_Cv := Finset.ne_of_mem_erase h2'
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rcases Finset.mem_insert.mp hx1 with rfl | hxCv
        · exact hu_not_mem C₂ h2C' hx2
        · exact Finset.disjoint_left.mp (h𝒞'_disj Cv hCv_mem C₂ h2C' h2_ne_Cv.symm) hxCv hx2
      · have h1C' := Finset.erase_subset _ _ h1'
        have h1_ne_Cv := Finset.ne_of_mem_erase h1'
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rcases Finset.mem_insert.mp hx2 with rfl | hxCv
        · exact hu_not_mem C₁ h1C' hx1
        · exact Finset.disjoint_left.mp (h𝒞'_disj C₁ h1C' Cv hCv_mem h1_ne_Cv) hx1 hxCv
      · exact h𝒞'_disj C₁ (Finset.erase_subset _ _ h1') C₂ (Finset.erase_subset _ _ h2') hne
    · have hcard_C : 𝒞.card = 𝒞'.card := by
        rw [Finset.card_insert_of_notMem hCnew_not_mem, Finset.card_erase_of_mem hCv_mem]
        have hpos : 0 < 𝒞'.card := Finset.card_pos.mpr ⟨Cv, hCv_mem⟩
        omega
      have hS'_card : S'.card = S.card - 1 := Finset.card_erase_of_mem hu_S
      have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨u', hu_S⟩
      omega
    · intro x hx
      by_cases hxu : x = u'
      · subst hxu
        exact ⟨Cnew, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
      · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxu, hx⟩
        obtain ⟨C, hC_C', hxC⟩ := h𝒞'_cov x hxS'
        by_cases hCCv : C = Cv
        · subst hCCv
          exact ⟨Cnew, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxC⟩
        · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCCv, hC_C'⟩), hxC⟩
    · intro x hxS hx_no_in
      by_cases hxu : x = u'
      · subst hxu
        refine ⟨Cnew, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, fun w hw => ?_⟩
        rcases Finset.mem_insert.mp hw with rfl | hwCv
        · exact le_rfl
        · exact le_trans huv_lt.le (hv_min w hwCv)
      · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxu, hxS⟩
        have hx_no_in' : ∀ e ∈ M', e.2 ≠ x := fun e he =>
          hx_no_in e (Finset.erase_subset _ _ he)
        obtain ⟨Cx, hCx_C', hx_Cx, hx_min⟩ := h𝒞'_min x hxS' hx_no_in'
        have hCx_ne_Cv : Cx ≠ Cv := by
          intro heq
          subst heq
          have hxv_ne : x ≠ v := (hx_no_in (u', v) huv_mem).symm
          exact hxv_ne (le_antisymm (hx_min v hv_Cv) (hv_min x hx_Cx))
        exact ⟨Cx, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCx_ne_Cv, hCx_C'⟩), hx_Cx, hx_min⟩

/-- **Dilworth's Theorem (1950)**: in any finite subset `S` of a partial order `P`, the maximum
size of an antichain in `S` equals the minimum number of chains covering `S`
(proved via Fulkerson's reduction to König–Egerváry). -/
theorem dilworth_theorem {P : Type*} [PartialOrder P] [DecidableEq P] (S : Finset P) :
    ∃ k : ℕ,
      (∃ U ⊆ S, IsAntichain (· ≤ ·) (U : Set P) ∧ U.card = k) ∧
      (∀ U ⊆ S, IsAntichain (· ≤ ·) (U : Set P) → U.card ≤ k) ∧
      (∃ 𝒞 : Finset (Finset P), 𝒞.card ≤ k ∧
        (∀ C ∈ 𝒞, IsChain (· ≤ ·) (C : Set P)) ∧ S ⊆ 𝒞.biUnion id) := by
  classical
  let adj : S → S → Prop := fun x y => x.1 < y.1
  obtain ⟨M_sub, A, B, hM_adj, hM_inj1, hM_inj2, hAB_cov, hcard_eq⟩ := konig_egervary adj
  let M : Finset (P × P) := M_sub.map
    ⟨fun e => (e.1.1, e.2.1), fun e₁ e₂ h =>
      Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))⟩
  have hM_card : M.card = M_sub.card := Finset.card_map _
  have hM_prop : ∀ e ∈ M, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 := by
    intro e he
    rcases Finset.mem_map.mp he with ⟨⟨x, y⟩, hxy, rfl⟩
    exact ⟨x.2, y.2, hM_adj (x, y) hxy⟩
  have hM_inj1' : (M : Set (P × P)).InjOn Prod.fst := by
    intro e₁ he₁ e₂ he₂ heq
    rcases Finset.mem_map.mp he₁ with ⟨p₁, hp₁, rfl⟩
    rcases Finset.mem_map.mp he₂ with ⟨p₂, hp₂, rfl⟩
    have hp_eq : p₁.1 = p₂.1 := Subtype.ext heq
    rw [hM_inj1 hp₁ hp₂ hp_eq]
  have hM_inj2' : (M : Set (P × P)).InjOn Prod.snd := by
    intro e₁ he₁ e₂ he₂ heq
    rcases Finset.mem_map.mp he₁ with ⟨p₁, hp₁, rfl⟩
    rcases Finset.mem_map.mp he₂ with ⟨p₂, hp₂, rfl⟩
    have hp_eq : p₁.2 = p₂.2 := Subtype.ext heq
    rw [hM_inj2 hp₁ hp₂ hp_eq]
  obtain ⟨𝒞, h𝒞_chain, _, h𝒞_card, h𝒞_cov, _⟩ :=
    matching_to_chain_cover M.card S M rfl hM_prop hM_inj1' hM_inj2'
  let U_sub : Finset S := Finset.univ.filter (fun x => x ∉ A ∧ x ∉ B)
  let U : Finset P := U_sub.image Subtype.val
  have hUS : U ⊆ S := fun u hu => by
    rcases Finset.mem_image.mp hu with ⟨x, _, rfl⟩; exact x.2
  have hU_anti : IsAntichain (· ≤ ·) (U : Set P) := by
    intro u hu v hv huv hle
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hu) with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hv) with ⟨y, hy, rfl⟩
    have hlt : x.1 < y.1 := lt_of_le_of_ne hle huv
    have hxA := (Finset.mem_filter.mp hx).2.1
    have hyB := (Finset.mem_filter.mp hy).2.2
    rcases hAB_cov x y hlt with h1 | h2
    · exact hxA h1
    · exact hyB h2
  have hU_card_ge : 𝒞.card ≤ U.card := by
    have hU_sub_card : U.card = U_sub.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hcomp : S.card - (A.card + B.card) ≤ U_sub.card := by
      have hcov_sub : (Finset.univ : Finset S) ⊆ U_sub ∪ (A ∪ B) := by
        intro x _
        by_cases hxA : x ∈ A
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxA)
        · by_cases hxB : x ∈ B
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxB)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, hxB⟩)
      have hcard_univ : (Finset.univ : Finset S).card = S.card := Fintype.card_coe S
      have h1 := Finset.card_le_card hcov_sub
      have h2 := Finset.card_union_le U_sub (A ∪ B)
      have h3 := Finset.card_union_le A B
      omega
    omega
  have hU_card_le : U.card ≤ 𝒞.card :=
    dilworth_weak hUS hU_anti (fun C hC => (h𝒞_chain C hC).2.2) (fun x hx => by
      obtain ⟨C, hC, hxC⟩ := h𝒞_cov x hx
      exact Finset.mem_biUnion.mpr ⟨C, hC, hxC⟩)
  have hU_eq_𝒞 : U.card = 𝒞.card := le_antisymm hU_card_le hU_card_ge
  refine ⟨U.card, ⟨U, hUS, hU_anti, rfl⟩, fun W hWS hW_anti => ?_,
    ⟨𝒞, hU_eq_𝒞.symm.le, fun C hC => (h𝒞_chain C hC).2.2, fun x hx => by
      obtain ⟨C, hC, hxC⟩ := h𝒞_cov x hx
      exact Finset.mem_biUnion.mpr ⟨C, hC, hxC⟩⟩⟩
  exact le_trans (dilworth_weak hWS hW_anti (fun C hC => (h𝒞_chain C hC).2.2) (fun x hx => by
    obtain ⟨C, hC, hxC⟩ := h𝒞_cov x hx
    exact Finset.mem_biUnion.mpr ⟨C, hC, hxC⟩)) hU_eq_𝒞.symm.le

end CombinatorialDuality

end Arith4Ext.ConvexOptDuality
