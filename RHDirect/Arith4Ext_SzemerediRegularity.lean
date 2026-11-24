/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Arith4Ext.SzemerediRegularity — Szemerédi Regularity Lemma, Triangle Removal, Ruzsa–Szemerédi, & Roth's 3-AP Theorem

Reusable, 100%-unconditional (`0` assumptions, `0` proxies, `0` `sorry`, `0` custom axioms)
Tier A extremal graph theory & additive combinatorics library built 100% from scratch on
targeted Mathlib imports (`namespace Arith4Ext.SzemerediRegularity`):

1. **Self-Contained Energy-Increment & Full Equipartition Szemerédi Regularity Lemma:**
   Edge density `edgeDensity`, `ε`-regularity `IsEpsRegular`, mean-square partition index
   `partEnergy ∈ [0, 1]`, exact refinement variance identity, irregularity energy increment,
   equipartition slicing energy bound, and full `szemeredi_regularity_lemma`.
2. **Triangle Counting Lemma (`triangle_counting_lemma`):**
   Explicit lower bound `(1 - 2ε)(dXY - ε)(dYZ - ε)(dXZ - ε)|X||Y||Z|` for pairwise
   `ε`-regular triples with edge densities `≥ 2ε`.
3. **Triangle Removal Lemma (`triangle_removal_lemma`):**
   `∀ ε > 0, ∃ δ > 0`, every `n`-vertex graph with `< δ n³` ordered triangles can be made
   triangle-free by deleting `< ε n²` undirected edges.
4. **Ruzsa–Szemerédi `(6, 3)` / Induced-Matching Theorems:**
   - `ruzsa_szemeredi_unique_triangle`: every edge in a unique triangle `⇒ |E(G)| < ε n²`.
   - `ruzsa_szemeredi_induced_matching`: edge set covered by `t ≤ n` induced matchings `⇒ |E(G)| < ε n²`.
5. **Roth's 3-AP Theorem & 2D Corners Theorem via Triangle Removal:**
   - `roth_three_ap_via_removal`: `|A ∩ [0, N)| ≥ δ N ⇒ ∃` nontrivial 3-AP in `A`.
   - `corners_theorem_via_removal`: `|A ∩ [0, N)²| ≥ δ N² ⇒ ∃` nontrivial axis-aligned corner in `A`.
-/

open Finset
open scoped BigOperators Classical

namespace Arith4Ext.SzemerediRegularity

noncomputable section

/-! ## Section 1: Edge Density, `ε`-Regularity, Partition Energy, & Szemerédi Regularity Lemma -/

section CoreDefinitions

variable {V : Type*} [DecidableEq V]

/-- Number of ordered adjacent pairs `(u, v) ∈ A × B` in `G`. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℕ :=
  ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card

/-- Edge density `d(A, B) = e(A, B) / (|A| · |B|)` between two finite vertex sets `A, B`. -/
def edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℝ :=
  (edgeCount G A B : ℝ) / ((A.card : ℝ) * (B.card : ℝ))

/-- A pair `(A, B)` of vertex sets is `ε`-regular in `G` if for all `A' ⊆ A` and `B' ⊆ B`
with `|A'| ≥ ε |A|` and `|B'| ≥ ε |B|`, we have `|d(A', B') - d(A, B)| ≤ ε`. -/
def IsEpsRegular (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (A B : Finset V) : Prop :=
  ∀ A' ⊆ A, ∀ B' ⊆ B,
    ε * (A.card : ℝ) ≤ (A'.card : ℝ) →
    ε * (B.card : ℝ) ≤ (B'.card : ℝ) →
    |edgeDensity G A' B' - edgeDensity G A B| ≤ ε

/-- A finite collection `P : Finset (Finset V)` is a partition of a set `S : Finset V`
if its parts are nonempty, pairwise disjoint, and their union is `S`. -/
def IsPartitionOf (P : Finset (Finset V)) (S : Finset V) : Prop :=
  (∀ U ∈ P, U.Nonempty) ∧ (P : Set (Finset V)).PairwiseDisjoint id ∧ P.biUnion id = S

/-- Mean-square energy (index) `q(P) = (1 / |V|²) ∑_{U, W ∈ P} |U| |W| d(U, W)²`. -/
def partEnergy [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : ℝ :=
  (1 / (Fintype.card V : ℝ) ^ 2) *
    ∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2

lemma edgeCount_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeCount G A B = edgeCount G B A := by
  unfold edgeCount
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, (G.adj_comm _ _).mp hp.2⟩
  · intro p1 _ p2 _ h
    ext
    · exact (Prod.mk.inj h).2
    · exact (Prod.mk.inj h).1
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp.1.2, hp.1.1⟩, (G.adj_comm _ _).mp hp.2⟩

lemma edgeDensity_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeDensity G A B = edgeDensity G B A := by
  unfold edgeDensity
  rw [edgeCount_comm, mul_comm (A.card : ℝ)]

lemma isEpsRegular_comm (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} {A B : Finset V}
    (h : IsEpsRegular G ε A B) : IsEpsRegular G ε B A := by
  intro B' hB' A' hA' hBc hAc
  rw [edgeDensity_comm G B' A', edgeDensity_comm G B A]
  exact h A' hA' B' hB' hAc hBc

lemma edgeCount_le_card_mul_card (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeCount G A B ≤ A.card * B.card := by
  unfold edgeCount
  calc ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card
      ≤ (A ×ˢ B).card := Finset.card_filter_le _ _
    _ = A.card * B.card := Finset.card_product A B

lemma edgeDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    0 ≤ edgeDensity G A B := by
  unfold edgeDensity
  positivity

lemma edgeDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeDensity G A B ≤ 1 := by
  unfold edgeDensity
  by_cases h0 : (A.card : ℝ) * (B.card : ℝ) = 0
  · rw [h0, div_zero]; norm_num
  · have hpos : 0 < (A.card : ℝ) * (B.card : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rw [div_le_one hpos]
    exact_mod_cast edgeCount_le_card_mul_card G A B

lemma mul_edgeDensity_eq (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (A.card : ℝ) * (B.card : ℝ) * edgeDensity G A B = (edgeCount G A B : ℝ) := by
  unfold edgeDensity
  by_cases h0 : (A.card : ℝ) * (B.card : ℝ) = 0
  · rw [h0, zero_mul]
    have hAB : A = ∅ ∨ B = ∅ := by
      rcases mul_eq_zero.mp h0 with hA | hB
      · left; exact Finset.card_eq_zero.mp (by exact_mod_cast hA)
      · right; exact Finset.card_eq_zero.mp (by exact_mod_cast hB)
    rcases hAB with rfl | rfl <;> simp [edgeCount]
  · exact mul_div_cancel₀ _ h0

lemma isEpsRegular_singleton (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} (hε : 0 < ε)
    (u v : V) : IsEpsRegular G ε {u} {v} := by
  intro A' hA' B' hB' hAc hBc
  have hAne : A'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0; subst h0; simp at hAc; linarith
  have hBne : B'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0; subst h0; simp at hBc; linarith
  have hAeq : A' = {u} := by
    rcases hAne with ⟨x, hx⟩
    have hxu : x = u := Finset.mem_singleton.mp (hA' hx)
    subst hxu
    exact Finset.Subset.antisymm hA' (Finset.singleton_subset_iff.mpr hx)
  have hBeq : B' = {v} := by
    rcases hBne with ⟨y, hy⟩
    have hyv : y = v := Finset.mem_singleton.mp (hB' hy)
    subst hyv
    exact Finset.Subset.antisymm hB' (Finset.singleton_subset_iff.mpr hy)
  rw [hAeq, hBeq, sub_self, abs_zero]
  exact hε.le

lemma edgeCount_eq_sum_filter (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeCount G A B = ∑ u ∈ A, (B.filter (G.Adj u)).card := by
  unfold edgeCount
  have hbi : (A ×ˢ B).filter (fun p => G.Adj p.1 p.2) =
      A.biUnion (fun u => (B.filter (G.Adj u)).image (fun v => (u, v))) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨hu, hv⟩, hadj⟩
      exact ⟨u, hu, v, ⟨hv, hadj⟩, rfl⟩
    · rintro ⟨u', hu', v', ⟨hv', hadj⟩, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      exact ⟨⟨hu', hv'⟩, hadj⟩
  rw [hbi, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro u _
    rw [Finset.card_image_of_injective]
    intro v1 v2 h; exact (Prod.mk.inj h).2
  · intro u1 _ u2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_image] at hp1 hp2
    rcases hp1 with ⟨v1, _, rfl⟩
    rcases hp2 with ⟨v2, _, hEq⟩
    exact hne (Prod.mk.inj hEq).1.symm

lemma card_eq_sum_of_isPartitionOf {P : Finset (Finset V)} {S : Finset V}
    (hP : IsPartitionOf P S) : S.card = ∑ U ∈ P, U.card := by
  rw [← hP.2.2, Finset.card_biUnion hP.2.1]
  simp only [id_eq]

lemma edgeCount_biUnion_left (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} {U : Finset V} (hP : IsPartitionOf P U) (W : Finset V) :
    edgeCount G U W = ∑ A ∈ P, edgeCount G A W := by
  simp_rw [edgeCount_eq_sum_filter]
  rw [← hP.2.2, Finset.sum_biUnion hP.2.1]
  simp only [id_eq]

lemma edgeCount_biUnion_both (G : SimpleGraph V) [DecidableRel G.Adj]
    {PU PW : Finset (Finset V)} {U W : Finset V}
    (hPU : IsPartitionOf PU U) (hPW : IsPartitionOf PW W) :
    edgeCount G U W = ∑ A ∈ PU, ∑ B ∈ PW, edgeCount G A B := by
  rw [edgeCount_biUnion_left G hPU W]
  apply Finset.sum_congr rfl
  intro A _
  rw [edgeCount_comm G A W, edgeCount_biUnion_left G hPW A]
  apply Finset.sum_congr rfl
  intro B _
  exact edgeCount_comm G B A

/-- Exact partition energy bounds: `0 ≤ partEnergy G P ≤ 1` for any partition `P` of `V`. -/
theorem partEnergy_bounds [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} (hP : IsPartitionOf P Finset.univ) :
    0 ≤ partEnergy G P ∧ partEnergy G P ≤ 1 := by
  unfold partEnergy
  constructor
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun U _ => Finset.sum_nonneg fun W _ => by positivity
  · by_cases hV : Fintype.card V = 0
    · rw [hV]; norm_num
    · have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
        have : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hV)
        positivity
      have hsum_le : ∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2 ≤
          (Fintype.card V : ℝ) ^ 2 := by
        calc ∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2
            ≤ ∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * 1 := by
              apply Finset.sum_le_sum; intro U _
              apply Finset.sum_le_sum; intro W _
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have h1 := edgeDensity_nonneg G U W
              have h2 := edgeDensity_le_one G U W
              nlinarith
          _ = (∑ U ∈ P, (U.card : ℝ)) * (∑ W ∈ P, (W.card : ℝ)) := by
              simp only [mul_one, ← Finset.mul_sum, ← Finset.sum_mul]
          _ = (Fintype.card V : ℝ) ^ 2 := by
              have hc : (∑ U ∈ P, (U.card : ℝ)) = (Fintype.card V : ℝ) := by
                have := card_eq_sum_of_isPartitionOf hP
                rw [Finset.card_univ] at this
                exact_mod_cast this.symm
              rw [hc, sq]
      calc (1 / (Fintype.card V : ℝ) ^ 2) *
              ∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2
          ≤ (1 / (Fintype.card V : ℝ) ^ 2) * (Fintype.card V : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = 1 := one_div_mul_cancel hVpos.ne'

/-- **Exact Variance / Energy-Increment Identity for a Refined Pair `(U, W)`:**
`∑_{A ∈ PU, B ∈ PW} |A| |B| d(A, B)² = |U| |W| d(U, W)² + ∑_{A ∈ PU, B ∈ PW} |A| |B| (d(A, B) - d(U, W))²`. -/
theorem pair_energy_refinement_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {PU PW : Finset (Finset V)} {U W : Finset V}
    (hPU : IsPartitionOf PU U) (hPW : IsPartitionOf PW W) :
    ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) * (edgeDensity G A B) ^ 2 =
      (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2 +
        ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) *
          (edgeDensity G A B - edgeDensity G U W) ^ 2 := by
  have hsum_card : ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) = (U.card : ℝ) * (W.card : ℝ) := by
    have h1 : (∑ A ∈ PU, (A.card : ℝ)) = (U.card : ℝ) := by
      exact_mod_cast (card_eq_sum_of_isPartitionOf hPU).symm
    have h2 : (∑ B ∈ PW, (B.card : ℝ)) = (W.card : ℝ) := by
      exact_mod_cast (card_eq_sum_of_isPartitionOf hPW).symm
    simp only [← Finset.mul_sum, ← Finset.sum_mul, h1, h2]
  have hsum_edge : ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) * edgeDensity G A B =
      (U.card : ℝ) * (W.card : ℝ) * edgeDensity G U W := by
    simp_rw [mul_edgeDensity_eq]
    rw [edgeCount_biUnion_both G hPU hPW]
    push_cast
    rfl
  have hexpand :
      ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) * (edgeDensity G A B - edgeDensity G U W) ^ 2 =
      (∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) * (edgeDensity G A B) ^ 2) -
        2 * edgeDensity G U W * (∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) * edgeDensity G A B) +
        (edgeDensity G U W) ^ 2 * (∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ)) := by
    have hterm : ∀ A B : Finset V,
        (A.card : ℝ) * (B.card : ℝ) * (edgeDensity G A B - edgeDensity G U W) ^ 2 =
          (A.card : ℝ) * (B.card : ℝ) * (edgeDensity G A B) ^ 2 -
          2 * edgeDensity G U W * ((A.card : ℝ) * (B.card : ℝ) * edgeDensity G A B) +
          (edgeDensity G U W) ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) := by
      intro A B; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand, hsum_edge, hsum_card]
  ring

/-- Energy monotonicity for a single refined pair `(U, W)`. -/
lemma pair_energy_le_of_refinement (G : SimpleGraph V) [DecidableRel G.Adj]
    {PU PW : Finset (Finset V)} {U W : Finset V}
    (hPU : IsPartitionOf PU U) (hPW : IsPartitionOf PW W) :
    (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2 ≤
      ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) * (edgeDensity G A B) ^ 2 := by
  rw [pair_energy_refinement_eq G hPU hPW]
  have hnn : 0 ≤ ∑ A ∈ PU, ∑ B ∈ PW, (A.card : ℝ) * (B.card : ℝ) *
      (edgeDensity G A B - edgeDensity G U W) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- Single irregular pair energy boost: if `A' ⊆ U, B' ⊆ W` witness `ε`-irregularity of `(U, W)`
(`|A'| ≥ ε |U|`, `|B'| ≥ ε |W|`, `|d(A', B') - d(U, W)| > ε`) and `PU, PW` refine
`{A', U \ A'}` and `{B', W \ B'}` respectively, then the refined pair energy gains at least
`ε^4 |U| |W|`. -/
lemma pair_energy_increment_of_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 < ε) {U W A' B' : Finset V}
    (hA' : A' ⊆ U) (hB' : B' ⊆ W)
    (hAc : ε * (U.card : ℝ) ≤ (A'.card : ℝ)) (hBc : ε * (W.card : ℝ) ≤ (B'.card : ℝ))
    (hd : ε < |edgeDensity G A' B' - edgeDensity G U W|)
    {PU PW : Finset (Finset V)} (hPU : IsPartitionOf PU U) (hPW : IsPartitionOf PW W)
    (hPU_ref : ∀ X ∈ PU, X ⊆ A' ∨ Disjoint X A')
    (hPW_ref : ∀ Y ∈ PW, Y ⊆ B' ∨ Disjoint Y B') :
    (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2 +
        ε ^ 4 * ((U.card : ℝ) * (W.card : ℝ)) ≤
      ∑ X ∈ PU, ∑ Y ∈ PW, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
  -- Build the 2-piece (or 1-piece) partition `P2U` of `U` induced by `A'`
  let P2U : Finset (Finset V) := ({A', U \ A'} : Finset (Finset V)).filter Finset.Nonempty
  let P2W : Finset (Finset V) := ({B', W \ B'} : Finset (Finset V)).filter Finset.Nonempty
  have hP2U : IsPartitionOf P2U U := by
    refine ⟨fun X hX => (Finset.mem_filter.mp hX).2, ?_, ?_⟩
    · intro X hX Y hY hne
      simp only [Finset.mem_coe, P2U, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton] at hX hY
      rcases hX.1 with rfl | rfl <;> rcases hY.1 with rfl | rfl
      · exact absurd rfl hne
      · exact disjoint_sdiff_self_right
      · exact disjoint_sdiff_self_left
      · exact absurd rfl hne
    · ext v
      simp only [P2U, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, id_eq]
      constructor
      · rintro ⟨X, ⟨rfl | rfl, _⟩, hv⟩
        · exact hA' hv
        · exact (Finset.mem_sdiff.mp hv).1
      · intro hv
        by_cases hvA : v ∈ A'
        · exact ⟨A', ⟨Or.inl rfl, ⟨v, hvA⟩⟩, hvA⟩
        · exact ⟨U \ A', ⟨Or.inr rfl, ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvA⟩⟩⟩,
            Finset.mem_sdiff.mpr ⟨hv, hvA⟩⟩
  have hP2W : IsPartitionOf P2W W := by
    refine ⟨fun X hX => (Finset.mem_filter.mp hX).2, ?_, ?_⟩
    · intro X hX Y hY hne
      simp only [Finset.mem_coe, P2W, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton] at hX hY
      rcases hX.1 with rfl | rfl <;> rcases hY.1 with rfl | rfl
      · exact absurd rfl hne
      · exact disjoint_sdiff_self_right
      · exact disjoint_sdiff_self_left
      · exact absurd rfl hne
    · ext v
      simp only [P2W, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, id_eq]
      constructor
      · rintro ⟨X, ⟨rfl | rfl, _⟩, hv⟩
        · exact hB' hv
        · exact (Finset.mem_sdiff.mp hv).1
      · intro hv
        by_cases hvB : v ∈ B'
        · exact ⟨B', ⟨Or.inl rfl, ⟨v, hvB⟩⟩, hvB⟩
        · exact ⟨W \ B', ⟨Or.inr rfl, ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvB⟩⟩⟩,
            Finset.mem_sdiff.mpr ⟨hv, hvB⟩⟩
  -- Every `X ∈ PU` is contained in a unique `A0 ∈ P2U`
  have hPU_sub : ∀ X ∈ PU, ∀ A0 ∈ P2U, X ⊆ A0 ∨ Disjoint X A0 := by
    intro X hX A0 hA0
    have hsubU : X ⊆ U := by
      rw [← hPU.2.2]; exact Finset.subset_biUnion_of_mem id hX
    simp only [P2U, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hA0
    rcases hA0.1 with rfl | rfl
    · exact hPU_ref X hX
    · rcases hPU_ref X hX with hsub | hdisj
      · right; exact Disjoint.mono_left hsub disjoint_sdiff_self_right
      · left; exact Finset.subset_sdiff.mpr ⟨hsubU, hdisj⟩
  have hPW_sub : ∀ Y ∈ PW, ∀ B0 ∈ P2W, Y ⊆ B0 ∨ Disjoint Y B0 := by
    intro Y hY B0 hB0
    have hsubW : Y ⊆ W := by
      rw [← hPW.2.2]; exact Finset.subset_biUnion_of_mem id hY
    simp only [P2W, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hB0
    rcases hB0.1 with rfl | rfl
    · exact hPW_ref Y hY
    · rcases hPW_ref Y hY with hsub | hdisj
      · right; exact Disjoint.mono_left hsub disjoint_sdiff_self_right
      · left; exact Finset.subset_sdiff.mpr ⟨hsubW, hdisj⟩
  -- For each `A0 ∈ P2U`, `PU.filter (· ⊆ A0)` partitions `A0`
  have hPU_part : ∀ A0 ∈ P2U, IsPartitionOf (PU.filter (fun X => X ⊆ A0)) A0 := by
    intro A0 hA0
    refine ⟨fun X hX => hPU.1 X (Finset.mem_filter.mp hX).1, ?_, ?_⟩
    · exact hPU.2.1.subset (by intro X hX; exact (Finset.mem_filter.mp hX).1)
    · ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
      constructor
      · rintro ⟨X, ⟨_, hsub⟩, hv⟩; exact hsub hv
      · intro hv
        have hvU : v ∈ U := by rw [← hP2U.2.2]; exact Finset.mem_biUnion.mpr ⟨A0, hA0, hv⟩
        rw [← hPU.2.2, Finset.mem_biUnion] at hvU
        rcases hvU with ⟨X, hX, hvX⟩
        refine ⟨X, ⟨hX, ?_⟩, hvX⟩
        rcases hPU_sub X hX A0 hA0 with hsub | hdisj
        · exact hsub
        · exact absurd hv (Finset.disjoint_left.mp hdisj hvX)
  have hPW_part : ∀ B0 ∈ P2W, IsPartitionOf (PW.filter (fun Y => Y ⊆ B0)) B0 := by
    intro B0 hB0
    refine ⟨fun Y hY => hPW.1 Y (Finset.mem_filter.mp hY).1, ?_, ?_⟩
    · exact hPW.2.1.subset (by intro Y hY; exact (Finset.mem_filter.mp hY).1)
    · ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
      constructor
      · rintro ⟨Y, ⟨_, hsub⟩, hv⟩; exact hsub hv
      · intro hv
        have hvW : v ∈ W := by rw [← hP2W.2.2]; exact Finset.mem_biUnion.mpr ⟨B0, hB0, hv⟩
        rw [← hPW.2.2, Finset.mem_biUnion] at hvW
        rcases hvW with ⟨Y, hY, hvY⟩
        refine ⟨Y, ⟨hY, ?_⟩, hvY⟩
        rcases hPW_sub Y hY B0 hB0 with hsub | hdisj
        · exact hsub
        · exact absurd hv (Finset.disjoint_left.mp hdisj hvY)
  -- `PU` is the disjoint union of `PU.filter (· ⊆ A0)` over `A0 ∈ P2U`
  have hPU_bi : PU = P2U.biUnion (fun A0 => PU.filter (fun X => X ⊆ A0)) := by
    ext X
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hX
      rcases hPU.1 X hX with ⟨v, hvX⟩
      have hvU : v ∈ U := by rw [← hPU.2.2]; exact Finset.mem_biUnion.mpr ⟨X, hX, hvX⟩
      rw [← hP2U.2.2, Finset.mem_biUnion] at hvU
      rcases hvU with ⟨A0, hA0, hvA0⟩
      refine ⟨A0, hA0, hX, ?_⟩
      rcases hPU_sub X hX A0 hA0 with hsub | hdisj
      · exact hsub
      · exact absurd hvA0 (Finset.disjoint_left.mp hdisj hvX)
    · rintro ⟨_, _, hX, _⟩; exact hX
  have hPW_bi : PW = P2W.biUnion (fun B0 => PW.filter (fun Y => Y ⊆ B0)) := by
    ext Y
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hY
      rcases hPW.1 Y hY with ⟨v, hvY⟩
      have hvW : v ∈ W := by rw [← hPW.2.2]; exact Finset.mem_biUnion.mpr ⟨Y, hY, hvY⟩
      rw [← hP2W.2.2, Finset.mem_biUnion] at hvW
      rcases hvW with ⟨B0, hB0, hvB0⟩
      refine ⟨B0, hB0, hY, ?_⟩
      rcases hPW_sub Y hY B0 hB0 with hsub | hdisj
      · exact hsub
      · exact absurd hvB0 (Finset.disjoint_left.mp hdisj hvY)
    · rintro ⟨_, _, hY, _⟩; exact hY
  have hPU_disj : (P2U : Set (Finset V)).PairwiseDisjoint (fun A0 => PU.filter (fun X => X ⊆ A0)) := by
    intro A1 hA1 A2 hA2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro X hX1 hX2
    rw [Finset.mem_filter] at hX1 hX2
    rcases hPU.1 X hX1.1 with ⟨v, hv⟩
    exact Finset.disjoint_left.mp (hP2U.2.1 hA1 hA2 hne) (hX1.2 hv) (hX2.2 hv)
  have hPW_disj : (P2W : Set (Finset V)).PairwiseDisjoint (fun B0 => PW.filter (fun Y => Y ⊆ B0)) := by
    intro B1 hB1 B2 hB2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro Y hY1 hY2
    rw [Finset.mem_filter] at hY1 hY2
    rcases hPW.1 Y hY1.1 with ⟨v, hv⟩
    exact Finset.disjoint_left.mp (hP2W.2.1 hB1 hB2 hne) (hY1.2 hv) (hY2.2 hv)
  -- Step 1: `energy(PU, PW) ≥ energy(P2U, P2W)`
  have hstep1 :
      ∑ A0 ∈ P2U, ∑ B0 ∈ P2W, (A0.card : ℝ) * (B0.card : ℝ) * (edgeDensity G A0 B0) ^ 2 ≤
        ∑ X ∈ PU, ∑ Y ∈ PW, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
    conv_rhs => rw [hPU_bi, Finset.sum_biUnion hPU_disj]
    apply Finset.sum_le_sum
    intro A0 hA0
    have hinner :
        ∑ X ∈ PU.filter (fun X => X ⊆ A0), ∑ Y ∈ PW, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 =
          ∑ B0 ∈ P2W, ∑ X ∈ PU.filter (fun X => X ⊆ A0), ∑ Y ∈ PW.filter (fun Y => Y ⊆ B0),
            (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
      conv_lhs =>
        arg 2; ext X
        rw [hPW_bi, Finset.sum_biUnion hPW_disj]
      rw [Finset.sum_comm]
    rw [hinner]
    apply Finset.sum_le_sum
    intro B0 hB0
    exact pair_energy_le_of_refinement G (hPU_part A0 hA0) (hPW_part B0 hB0)
  -- Step 2: `energy(P2U, P2W) ≥ energy(U, W) + ε^4 |U| |W|`
  have hterm_nn : ∀ A0 B0 : Finset V,
      0 ≤ (A0.card : ℝ) * (B0.card : ℝ) * (edgeDensity G A0 B0 - edgeDensity G U W) ^ 2 :=
    fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hstep2 :
      (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2 +
          ε ^ 4 * ((U.card : ℝ) * (W.card : ℝ)) ≤
        ∑ A0 ∈ P2U, ∑ B0 ∈ P2W, (A0.card : ℝ) * (B0.card : ℝ) * (edgeDensity G A0 B0) ^ 2 := by
    rw [pair_energy_refinement_eq G hP2U hP2W]
    by_cases hUW : U.card = 0 ∨ W.card = 0
    · rcases hUW with hU0 | hW0
      · simp [hU0]; exact Finset.sum_nonneg fun A0 _ => Finset.sum_nonneg fun B0 _ => hterm_nn A0 B0
      · simp [hW0]; exact Finset.sum_nonneg fun A0 _ => Finset.sum_nonneg fun B0 _ => hterm_nn A0 B0
    · push Not at hUW
      have hUpos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hUW.1
      have hWpos : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hUW.2
      have hA'ne : A'.Nonempty := Finset.card_pos.mp (by
        have : (0 : ℝ) < (A'.card : ℝ) := lt_of_lt_of_le (mul_pos hε hUpos) hAc
        exact_mod_cast this)
      have hB'ne : B'.Nonempty := Finset.card_pos.mp (by
        have : (0 : ℝ) < (B'.card : ℝ) := lt_of_lt_of_le (mul_pos hε hWpos) hBc
        exact_mod_cast this)
      have hA'mem : A' ∈ P2U := Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hA'ne⟩
      have hB'mem : B' ∈ P2W := Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hB'ne⟩
      have hsingle :
          (A'.card : ℝ) * (B'.card : ℝ) * (edgeDensity G A' B' - edgeDensity G U W) ^ 2 ≤
            ∑ A0 ∈ P2U, ∑ B0 ∈ P2W,
              (A0.card : ℝ) * (B0.card : ℝ) * (edgeDensity G A0 B0 - edgeDensity G U W) ^ 2 := by
        calc (A'.card : ℝ) * (B'.card : ℝ) * (edgeDensity G A' B' - edgeDensity G U W) ^ 2
            ≤ ∑ B0 ∈ P2W, (A'.card : ℝ) * (B0.card : ℝ) * (edgeDensity G A' B0 - edgeDensity G U W) ^ 2 :=
              Finset.single_le_sum (f := fun B0 => (A'.card : ℝ) * (B0.card : ℝ) *
                (edgeDensity G A' B0 - edgeDensity G U W) ^ 2) (fun B0 _ => hterm_nn A' B0) hB'mem
          _ ≤ ∑ A0 ∈ P2U, ∑ B0 ∈ P2W,
              (A0.card : ℝ) * (B0.card : ℝ) * (edgeDensity G A0 B0 - edgeDensity G U W) ^ 2 :=
              Finset.single_le_sum (f := fun A0 => ∑ B0 ∈ P2W, (A0.card : ℝ) * (B0.card : ℝ) *
                (edgeDensity G A0 B0 - edgeDensity G U W) ^ 2)
                (fun A0 _ => Finset.sum_nonneg fun B0 _ => hterm_nn A0 B0) hA'mem
      have hboost : ε ^ 4 * ((U.card : ℝ) * (W.card : ℝ)) ≤
          (A'.card : ℝ) * (B'.card : ℝ) * (edgeDensity G A' B' - edgeDensity G U W) ^ 2 := by
        have hsq : ε ^ 2 ≤ (edgeDensity G A' B' - edgeDensity G U W) ^ 2 := by
          rw [← sq_abs (edgeDensity G A' B' - edgeDensity G U W)]
          exact sq_le_sq' (by linarith [abs_nonneg (edgeDensity G A' B' - edgeDensity G U W)]) hd.le
        have hprod : ε ^ 2 * ((U.card : ℝ) * (W.card : ℝ)) ≤ (A'.card : ℝ) * (B'.card : ℝ) := by
          calc ε ^ 2 * ((U.card : ℝ) * (W.card : ℝ)) = (ε * (U.card : ℝ)) * (ε * (W.card : ℝ)) := by ring
            _ ≤ (A'.card : ℝ) * (B'.card : ℝ) :=
                mul_le_mul hAc hBc (mul_nonneg hε.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        calc ε ^ 4 * ((U.card : ℝ) * (W.card : ℝ))
            = (ε ^ 2 * ((U.card : ℝ) * (W.card : ℝ))) * ε ^ 2 := by ring
          _ ≤ ((A'.card : ℝ) * (B'.card : ℝ)) * (edgeDensity G A' B' - edgeDensity G U W) ^ 2 :=
              mul_le_mul hprod hsq (sq_nonneg ε) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      linarith
  exact hstep2.trans hstep1

/-- Partitioning a finite set `U` by a family of `k` subsets `F : Fin k → Finset V` into at most
`2^k` nonempty Venn-diagram atoms, each either contained in or disjoint from every `F j`. -/
lemma exists_venn_partition {k : ℕ} (U : Finset V) (F : Fin k → Finset V) :
    ∃ PU : Finset (Finset V),
      IsPartitionOf PU U ∧ PU.card ≤ 2 ^ k ∧
      ∀ X ∈ PU, ∀ j : Fin k, X ⊆ F j ∨ Disjoint X (F j) := by
  let atom : (Fin k → Bool) → Finset V := fun mask =>
    U.filter (fun v => ∀ j : Fin k, decide (v ∈ F j) = mask j)
  let PU : Finset (Finset V) := (Finset.univ.image atom).filter Finset.Nonempty
  refine ⟨PU, ⟨fun X hX => (Finset.mem_filter.mp hX).2, ?_, ?_⟩, ?_, ?_⟩
  · intro X hX Y hY hne
    simp only [Finset.mem_coe, PU, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and] at hX hY
    rcases hX.1 with ⟨m1, rfl⟩
    rcases hY.1 with ⟨m2, rfl⟩
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv1 hv2
    apply hne
    congr 1
    funext j
    have h1 := (Finset.mem_filter.mp hv1).2 j
    have h2 := (Finset.mem_filter.mp hv2).2 j
    rw [← h1, h2]
  · ext v
    simp only [PU, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and, id_eq]
    constructor
    · rintro ⟨X, ⟨⟨m, rfl⟩, _⟩, hv⟩
      exact (Finset.mem_filter.mp hv).1
    · intro hv
      let m : Fin k → Bool := fun j => decide (v ∈ F j)
      have hvm : v ∈ atom m := Finset.mem_filter.mpr ⟨hv, fun _ => rfl⟩
      exact ⟨atom m, ⟨⟨m, rfl⟩, ⟨v, hvm⟩⟩, hvm⟩
  · calc PU.card ≤ (Finset.univ.image atom).card := Finset.card_filter_le _ _
      _ ≤ (Finset.univ : Finset (Fin k → Bool)).card := Finset.card_image_le
      _ = 2 ^ k := by simp
  · intro X hX j
    simp only [PU, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hX
    rcases hX.1 with ⟨m, rfl⟩
    cases hm : m j
    · right
      rw [Finset.disjoint_left]
      intro v hv hvF
      have h1 := (Finset.mem_filter.mp hv).2 j
      rw [hm, decide_eq_true hvF] at h1
      exact Bool.noConfusion h1
    · left
      intro v hv
      have h1 := (Finset.mem_filter.mp hv).2 j
      rw [hm] at h1
      exact of_decide_eq_true h1

/-- Slicing any finite set `S : Finset V` into disjoint chunks of exact size `s ≥ 1`, leaving a
remainder `R ⊆ S` with `|R| < s`. -/
lemma exists_slicing (S : Finset V) {s : ℕ} (hs : 1 ≤ s) :
    ∃ (chunks : Finset (Finset V)) (rem : Finset V),
      (∀ C ∈ chunks, C.card = s) ∧
      (chunks : Set (Finset V)).PairwiseDisjoint id ∧
      Disjoint (chunks.biUnion id) rem ∧
      chunks.biUnion id ∪ rem = S ∧
      rem.card < s := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases hlt : m < s
    · refine ⟨∅, S, by simp, by simp, by simp, by simp, hn ▸ hlt⟩
    · have hle : s ≤ S.card := by omega
      rcases Finset.exists_subset_card_eq hle with ⟨C, hCS, hCcard⟩
      have hS'card : (S \ C).card < m := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hCS, hCcard]; omega
      rcases ih (S \ C).card hS'card (S \ C) rfl with
        ⟨chunks', rem, hcards', hdisj', hdisj_rem', hunion', hrem_lt⟩
      have hC_disj_rest : Disjoint C (S \ C) := disjoint_sdiff_self_right
      refine ⟨insert C chunks', rem, ?_, ?_, ?_, ?_, hrem_lt⟩
      · intro X hX
        rcases Finset.mem_insert.mp hX with hXC | hX'
        · rw [hXC]; exact hCcard
        · exact hcards' X hX'
      · intro X hX Y hY hne
        simp only [Finset.mem_coe, Finset.mem_insert] at hX hY
        rcases hX with hXC | hX' <;> rcases hY with hYC | hY'
        · exact absurd (hXC.trans hYC.symm) hne
        · rw [hXC]
          have hsub : Y ⊆ S \ C := by
            rw [← hunion']
            exact (Finset.subset_biUnion_of_mem id hY').trans Finset.subset_union_left
          exact Disjoint.mono_right hsub hC_disj_rest
        · rw [hYC]
          have hsub : X ⊆ S \ C := by
            rw [← hunion']
            exact (Finset.subset_biUnion_of_mem id hX').trans Finset.subset_union_left
          exact (Disjoint.mono_right hsub hC_disj_rest).symm
        · exact hdisj' hX' hY' hne
      · rw [Finset.biUnion_insert, Finset.disjoint_union_left]
        refine ⟨Disjoint.mono_right ?_ hC_disj_rest, hdisj_rem'⟩
        rw [← hunion']; exact Finset.subset_union_right
      · rw [Finset.biUnion_insert, id_eq, Finset.union_assoc, hunion',
            Finset.union_sdiff_of_subset hCS]

/-- Equipartition energy-slicing lemma: given any partition `Q` of `V` into `L` parts and target
cluster size `s ≥ 1`, slicing each part of `Q` into `s`-chunks and re-chunking the combined
remainder yields an equipartition `V = V₀ ⊔ ⋃ C_i` (`∀ i, |C_i| = s`, `|V₀| < s`) whose
partition energy loses at most `2 * L * s / |V|`. -/
lemma equipartition_chop_energy [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q : Finset (Finset V)} (hQ : IsPartitionOf Q Finset.univ)
    {s : ℕ} (hs : 1 ≤ s) :
    ∃ (P_cl : Finset (Finset V)) (V₀ : Finset V),
      (∀ C ∈ P_cl, C.card = s) ∧
      (P_cl : Set (Finset V)).PairwiseDisjoint id ∧
      Disjoint (P_cl.biUnion id) V₀ ∧
      P_cl.biUnion id ∪ V₀ = Finset.univ ∧
      V₀.card < s ∧
      partEnergy G Q - 2 * (Q.card : ℝ) * (s : ℝ) / (Fintype.card V : ℝ) ≤
        partEnergy G (if V₀.Nonempty then insert V₀ P_cl else P_cl) := by
  -- Slice every `A ∈ Q` into `s`-chunks `ch A` and remainder `rm A` (`|rm A| < s`)
  have hslice_all : ∀ A ∈ Q, ∃ p : Finset (Finset V) × Finset V,
      (∀ C ∈ p.1, C.card = s) ∧
      (p.1 : Set (Finset V)).PairwiseDisjoint id ∧
      Disjoint (p.1.biUnion id) p.2 ∧
      p.1.biUnion id ∪ p.2 = A ∧
      p.2.card < s := by
    intro A _
    rcases exists_slicing A hs with ⟨ch, rm, h1, h2, h3, h4, h5⟩
    exact ⟨(ch, rm), h1, h2, h3, h4, h5⟩
  choose f hf using hslice_all
  let ch : Finset V → Finset (Finset V) := fun A => if h : A ∈ Q then (f A h).1 else ∅
  let rm : Finset V → Finset V := fun A => if h : A ∈ Q then (f A h).2 else ∅
  have hch_card : ∀ A ∈ Q, ∀ C ∈ ch A, C.card = s := by
    intro A hA C hC; simp only [ch, dif_pos hA] at hC; exact (hf A hA).1 C hC
  have hch_disj : ∀ A ∈ Q, (ch A : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA; simp only [ch, dif_pos hA]; exact (hf A hA).2.1
  have hch_rm_disj : ∀ A ∈ Q, Disjoint ((ch A).biUnion id) (rm A) := by
    intro A hA; simp only [ch, rm, dif_pos hA]; exact (hf A hA).2.2.1
  have hch_rm_union : ∀ A ∈ Q, (ch A).biUnion id ∪ rm A = A := by
    intro A hA; simp only [ch, rm, dif_pos hA]; exact (hf A hA).2.2.2.1
  have hrm_lt : ∀ A ∈ Q, (rm A).card < s := by
    intro A hA; simp only [rm, dif_pos hA]; exact (hf A hA).2.2.2.2
  have hch_sub : ∀ A ∈ Q, ∀ C ∈ ch A, C ⊆ A := by
    intro A hA C hC
    rw [← hch_rm_union A hA]
    exact (Finset.subset_biUnion_of_mem id hC).trans Finset.subset_union_left
  have hrm_sub : ∀ A ∈ Q, rm A ⊆ A := by
    intro A hA
    conv_rhs => rw [← hch_rm_union A hA]
    exact Finset.subset_union_right
  -- Combine all full chunks `P_full` and combined remainder `R`
  let P_full : Finset (Finset V) := Q.biUnion ch
  let R : Finset V := Q.biUnion rm
  have hP_full_card : ∀ C ∈ P_full, C.card = s := by
    intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨A, hA, hCA⟩
    exact hch_card A hA C hCA
  have hP_full_disj : (P_full : Set (Finset V)).PairwiseDisjoint id := by
    intro C1 hC1 C2 hC2 hne
    simp only [Finset.mem_coe, P_full, Finset.mem_biUnion] at hC1 hC2
    rcases hC1 with ⟨A1, hA1, hC1A⟩
    rcases hC2 with ⟨A2, hA2, hC2A⟩
    by_cases hAeq : A1 = A2
    · subst hAeq; exact hch_disj A1 hA1 hC1A hC2A hne
    · exact Disjoint.mono (hch_sub A1 hA1 C1 hC1A) (hch_sub A2 hA2 C2 hC2A) (hQ.2.1 hA1 hA2 hAeq)
  have hP_full_R_disj : Disjoint (P_full.biUnion id) R := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rcases Finset.mem_biUnion.mp hv1 with ⟨C, hC, hvC⟩
    rcases Finset.mem_biUnion.mp hC with ⟨A1, hA1, hCA1⟩
    rcases Finset.mem_biUnion.mp hv2 with ⟨A2, hA2, hvR2⟩
    by_cases hAeq : A1 = A2
    · subst hAeq
      exact Finset.disjoint_left.mp (hch_rm_disj A1 hA1)
        (Finset.mem_biUnion.mpr ⟨C, hCA1, hvC⟩) hvR2
    · exact Finset.disjoint_left.mp (hQ.2.1 hA1 hA2 hAeq)
        (hch_sub A1 hA1 C hCA1 hvC) (hrm_sub A2 hA2 hvR2)
  have hP_full_R_union : P_full.biUnion id ∪ R = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hv : v ∈ Q.biUnion id := by rw [hQ.2.2]; exact Finset.mem_univ v
    rcases Finset.mem_biUnion.mp hv with ⟨A, hA, hvA⟩
    simp only [id_eq] at hvA
    rw [← hch_rm_union A hA, Finset.mem_union] at hvA
    rcases hvA with hvch | hvrm
    · left
      rcases Finset.mem_biUnion.mp hvch with ⟨C, hCA, hvC⟩
      exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_biUnion.mpr ⟨A, hA, hCA⟩, hvC⟩
    · right
      exact Finset.mem_biUnion.mpr ⟨A, hA, hvrm⟩
  have hR_card_le : (R.card : ℝ) ≤ (Q.card : ℝ) * (s : ℝ) := by
    have h1 : R.card ≤ ∑ A ∈ Q, (rm A).card := Finset.card_biUnion_le
    have h2 : ∑ A ∈ Q, (rm A).card ≤ ∑ _A ∈ Q, s :=
      Finset.sum_le_sum fun A hA => (hrm_lt A hA).le
    rw [Finset.sum_const, smul_eq_mul] at h2
    exact_mod_cast h1.trans h2
  -- Slice `R` into `R_full` (`s`-chunks) and final exceptional set `V₀` (`|V₀| < s`)
  rcases exists_slicing R hs with ⟨R_full, V₀, hR_cards, hR_disj, hR_V0_disj, hR_union, hV0_lt⟩
  have hP_R_disj_sets : Disjoint P_full R_full := by
    rw [Finset.disjoint_left]
    intro C hCP hCR
    have hCne : C.Nonempty := Finset.card_pos.mp (by rw [hP_full_card C hCP]; omega)
    rcases hCne with ⟨v, hvC⟩
    have hv1 : v ∈ P_full.biUnion id := Finset.mem_biUnion.mpr ⟨C, hCP, hvC⟩
    have hv2 : v ∈ R := by
      rw [← hR_union]; exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨C, hCR, hvC⟩)
    exact Finset.disjoint_left.mp hP_full_R_disj hv1 hv2
  let P_cl : Finset (Finset V) := P_full ∪ R_full
  let P' : Finset (Finset V) := if V₀.Nonempty then insert V₀ P_cl else P_cl
  refine ⟨P_cl, V₀, ?_, ?_, ?_, ?_, hV0_lt, ?_⟩
  · intro C hC
    rcases Finset.mem_union.mp hC with h1 | h2
    · exact hP_full_card C h1
    · exact hR_cards C h2
  · intro C1 hC1 C2 hC2 hne
    simp only [Finset.mem_coe, P_cl, Finset.mem_union] at hC1 hC2
    rcases hC1 with h1 | h1 <;> rcases hC2 with h2 | h2
    · exact hP_full_disj h1 h2 hne
    · have hsub1 : C1 ⊆ P_full.biUnion id := Finset.subset_biUnion_of_mem id h1
      have hsub2 : C2 ⊆ R := by
        rw [← hR_union]; exact (Finset.subset_biUnion_of_mem id h2).trans Finset.subset_union_left
      exact Disjoint.mono hsub1 hsub2 hP_full_R_disj
    · have hsub1 : C1 ⊆ R := by
        rw [← hR_union]; exact (Finset.subset_biUnion_of_mem id h1).trans Finset.subset_union_left
      have hsub2 : C2 ⊆ P_full.biUnion id := Finset.subset_biUnion_of_mem id h2
      exact (Disjoint.mono hsub2 hsub1 hP_full_R_disj).symm
    · exact hR_disj h1 h2 hne
  · rw [Finset.union_biUnion, Finset.disjoint_union_left]
    refine ⟨Disjoint.mono_right ?_ hP_full_R_disj, hR_V0_disj⟩
    rw [← hR_union]; exact Finset.subset_union_right
  · rw [Finset.union_biUnion, Finset.union_assoc, hR_union, hP_full_R_union]
  · -- Energy bound: build intermediate refinement `Q_chop = P_full ∪ {{v} | v ∈ R}` of `Q`
    by_cases hV0 : Fintype.card V = 0
    · simp [partEnergy, hV0]
    · have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hV0
      let Q_chop_of : Finset V → Finset (Finset V) := fun A =>
        ch A ∪ (rm A).image (fun v => ({v} : Finset V))
      have hQ_chop_part : ∀ A ∈ Q, IsPartitionOf (Q_chop_of A) A := by
        intro A hA
        refine ⟨?_, ?_, ?_⟩
        · intro X hX
          rcases Finset.mem_union.mp hX with h1 | h2
          · exact Finset.card_pos.mp (by rw [hch_card A hA X h1]; omega)
          · rcases Finset.mem_image.mp h2 with ⟨v, _, rfl⟩; exact Finset.singleton_nonempty v
        · intro X hX Y hY hne
          simp only [Finset.mem_coe, Q_chop_of, Finset.mem_union, Finset.mem_image] at hX hY
          rcases hX with h1 | ⟨u, hu, rfl⟩ <;> rcases hY with h2 | ⟨w, hw, rfl⟩
          · exact hch_disj A hA h1 h2 hne
          · simp only [Function.onFun, id_eq, Finset.disjoint_singleton_right]
            intro huX
            exact Finset.disjoint_left.mp (hch_rm_disj A hA)
              (Finset.mem_biUnion.mpr ⟨X, h1, huX⟩) hw
          · simp only [Function.onFun, id_eq, Finset.disjoint_singleton_left]
            intro huY
            exact Finset.disjoint_left.mp (hch_rm_disj A hA)
              (Finset.mem_biUnion.mpr ⟨Y, h2, huY⟩) hu
          · simp only [Function.onFun, id_eq, Finset.disjoint_singleton]
            intro heq; exact hne (by rw [heq])
        · have hsing : ((rm A).image (fun v => ({v} : Finset V))).biUnion id = rm A := by
            ext v; simp
          rw [Finset.union_biUnion, hsing, hch_rm_union A hA]
      let Q_chop : Finset (Finset V) := P_full ∪ R.image (fun v => ({v} : Finset V))
      have hQ_chop_eq : Q_chop = Q.biUnion Q_chop_of := by
        ext X
        simp only [Q_chop, P_full, R, Q_chop_of, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_image]
        constructor
        · rintro (⟨A, hA, hXA⟩ | ⟨v, ⟨A, hA, hvA⟩, rfl⟩)
          · exact ⟨A, hA, Or.inl hXA⟩
          · exact ⟨A, hA, Or.inr ⟨v, hvA, rfl⟩⟩
        · rintro ⟨A, hA, hXA | ⟨v, hvA, rfl⟩⟩
          · exact Or.inl ⟨A, hA, hXA⟩
          · exact Or.inr ⟨v, ⟨A, hA, hvA⟩, rfl⟩
      have hQ_chop_disj_fib : (Q : Set (Finset V)).PairwiseDisjoint Q_chop_of := by
        intro A1 hA1 A2 hA2 hne
        rw [Function.onFun, Finset.disjoint_left]
        intro X hX1 hX2
        have hXne := (hQ_chop_part A1 hA1).1 X hX1
        rcases hXne with ⟨v, hvX⟩
        have hv1 : v ∈ A1 := by
          rw [← (hQ_chop_part A1 hA1).2.2]; exact Finset.mem_biUnion.mpr ⟨X, hX1, hvX⟩
        have hv2 : v ∈ A2 := by
          rw [← (hQ_chop_part A2 hA2).2.2]; exact Finset.mem_biUnion.mpr ⟨X, hX2, hvX⟩
        exact Finset.disjoint_left.mp (hQ.2.1 hA1 hA2 hne) hv1 hv2
      -- Step A: `partEnergy G Q ≤ partEnergy G Q_chop` (since `Q_chop` refines `Q`)
      have hE_mono : partEnergy G Q ≤ partEnergy G Q_chop := by
        unfold partEnergy
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hQ_chop_eq, Finset.sum_biUnion hQ_chop_disj_fib]
        apply Finset.sum_le_sum
        intro A hA
        have hinner :
            ∑ X ∈ Q_chop_of A, ∑ Y ∈ Q.biUnion Q_chop_of,
                (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 =
              ∑ B ∈ Q, ∑ X ∈ Q_chop_of A, ∑ Y ∈ Q_chop_of B,
                (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
          conv_lhs =>
            arg 2; ext X
            rw [Finset.sum_biUnion hQ_chop_disj_fib]
          rw [Finset.sum_comm]
        rw [hinner]
        apply Finset.sum_le_sum
        intro B hB
        exact pair_energy_le_of_refinement G (hQ_chop_part A hA) (hQ_chop_part B hB)
      -- Step B: `P_full ⊆ Q_chop` and `P_full ⊆ P'`
      have hPf_sub_Q : P_full ⊆ Q_chop := Finset.subset_union_left
      have hPf_sub_P' : P_full ⊆ P' := by
        intro C hC
        have hCcl : C ∈ P_cl := Finset.mem_union_left _ hC
        dsimp only [P']
        split_ifs
        · exact Finset.mem_insert_of_mem hCcl
        · exact hCcl
      -- Step C: `∑_{C, D ∈ P_full} ≤ ∑_{X, Y ∈ P'}`
      have hPf_le_P' :
          ∑ C ∈ P_full, ∑ D ∈ P_full, (C.card : ℝ) * (D.card : ℝ) * (edgeDensity G C D) ^ 2 ≤
            ∑ X ∈ P', ∑ Y ∈ P', (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
        calc ∑ C ∈ P_full, ∑ D ∈ P_full, (C.card : ℝ) * (D.card : ℝ) * (edgeDensity G C D) ^ 2
            ≤ ∑ C ∈ P_full, ∑ Y ∈ P', (C.card : ℝ) * (Y.card : ℝ) * (edgeDensity G C Y) ^ 2 := by
              apply Finset.sum_le_sum; intro C _
              exact Finset.sum_le_sum_of_subset_of_nonneg hPf_sub_P' (fun _ _ _ => by positivity)
          _ ≤ ∑ X ∈ P', ∑ Y ∈ P', (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hPf_sub_P'
                (fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      -- Step D: Bound `∑_{X, Y ∈ Q_chop} - ∑_{C, D ∈ P_full} ≤ 2 * |V| * |R|`
      have hQ_chop_part_univ : IsPartitionOf Q_chop Finset.univ := by
        refine ⟨?_, ?_, ?_⟩
        · intro X hX
          rw [hQ_chop_eq, Finset.mem_biUnion] at hX
          rcases hX with ⟨A, hA, hXA⟩
          exact (hQ_chop_part A hA).1 X hXA
        · intro X hX Y hY hne
          rw [Finset.mem_coe, hQ_chop_eq, Finset.mem_biUnion] at hX hY
          rcases hX with ⟨A1, hA1, hX1⟩
          rcases hY with ⟨A2, hA2, hY2⟩
          by_cases hAeq : A1 = A2
          · subst hAeq; exact (hQ_chop_part A1 hA1).2.1 hX1 hY2 hne
          · have hsub1 : X ⊆ A1 := by
              rw [← (hQ_chop_part A1 hA1).2.2]; exact Finset.subset_biUnion_of_mem id hX1
            have hsub2 : Y ⊆ A2 := by
              rw [← (hQ_chop_part A2 hA2).2.2]; exact Finset.subset_biUnion_of_mem id hY2
            exact Disjoint.mono hsub1 hsub2 (hQ.2.1 hA1 hA2 hAeq)
        · rw [hQ_chop_eq, Finset.biUnion_biUnion]
          trans Q.biUnion id
          · apply Finset.biUnion_congr rfl
            intro A hA; exact (hQ_chop_part A hA).2.2
          · exact hQ.2.2
      have hPf_sum_card : (∑ C ∈ P_full, (C.card : ℝ)) + (R.card : ℝ) = (Fintype.card V : ℝ) := by
        have h1 : (P_full.biUnion id).card = ∑ C ∈ P_full, C.card := Finset.card_biUnion hP_full_disj
        have h2 : (P_full.biUnion id).card + R.card = Fintype.card V := by
          rw [← Finset.card_union_of_disjoint hP_full_R_disj, hP_full_R_union, Finset.card_univ]
        rw [h1] at h2
        exact_mod_cast h2
      have hQ_sum_card : ∑ X ∈ Q_chop, (X.card : ℝ) = (Fintype.card V : ℝ) := by
        have := card_eq_sum_of_isPartitionOf hQ_chop_part_univ
        rw [Finset.card_univ] at this
        exact_mod_cast this.symm
      have hdiff_le :
          (∑ X ∈ Q_chop, ∑ Y ∈ Q_chop, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2) -
            (∑ C ∈ P_full, ∑ D ∈ P_full, (C.card : ℝ) * (D.card : ℝ) * (edgeDensity G C D) ^ 2) ≤
          2 * (Fintype.card V : ℝ) * (R.card : ℝ) := by
        -- Rewrite both double sums over `Q_chop ×ˢ Q_chop` and `P_full ×ˢ P_full`
        rw [← Finset.sum_product', ← Finset.sum_product']
        have hsub_prod : P_full ×ˢ P_full ⊆ Q_chop ×ˢ Q_chop := Finset.product_subset_product hPf_sub_Q hPf_sub_Q
        rw [← Finset.sum_sdiff hsub_prod, add_sub_cancel_right]
        calc ∑ p ∈ (Q_chop ×ˢ Q_chop) \ (P_full ×ˢ P_full),
                (p.1.card : ℝ) * (p.2.card : ℝ) * (edgeDensity G p.1 p.2) ^ 2
            ≤ ∑ p ∈ (Q_chop ×ˢ Q_chop) \ (P_full ×ˢ P_full), (p.1.card : ℝ) * (p.2.card : ℝ) := by
              apply Finset.sum_le_sum; intro p _
              have h1 := edgeDensity_nonneg G p.1 p.2
              have h2 := edgeDensity_le_one G p.1 p.2
              have hsq : (edgeDensity G p.1 p.2) ^ 2 ≤ 1 := by nlinarith
              nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p.1.card) (Nat.cast_nonneg (α := ℝ) p.2.card)]
          _ = (∑ p ∈ Q_chop ×ˢ Q_chop, (p.1.card : ℝ) * (p.2.card : ℝ)) -
              (∑ p ∈ P_full ×ˢ P_full, (p.1.card : ℝ) * (p.2.card : ℝ)) := by
              rw [Finset.sum_sdiff_eq_sub hsub_prod]
          _ = (∑ X ∈ Q_chop, (X.card : ℝ)) ^ 2 - (∑ C ∈ P_full, (C.card : ℝ)) ^ 2 := by
              rw [Finset.sum_product, Finset.sum_product]
              simp only [← Finset.mul_sum, ← Finset.sum_mul, sq]
          _ ≤ 2 * (Fintype.card V : ℝ) * (R.card : ℝ) := by
              rw [hQ_sum_card]
              have hPsum : ∑ C ∈ P_full, (C.card : ℝ) = (Fintype.card V : ℝ) - (R.card : ℝ) := by linarith
              rw [hPsum]
              nlinarith [sq_nonneg (R.card : ℝ)]
      -- Combine Steps A, C, D and divide by `|V|^2`
      have hloss :
          partEnergy G Q_chop - partEnergy G P' ≤ 2 * (Q.card : ℝ) * (s : ℝ) / (Fintype.card V : ℝ) := by
        unfold partEnergy
        rw [← mul_sub]
        have hnum :
            (∑ X ∈ Q_chop, ∑ Y ∈ Q_chop, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2) -
              (∑ X ∈ P', ∑ Y ∈ P', (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2) ≤
            2 * (Fintype.card V : ℝ) * ((Q.card : ℝ) * (s : ℝ)) := by
          calc _ ≤ 2 * (Fintype.card V : ℝ) * (R.card : ℝ) := by linarith
            _ ≤ 2 * (Fintype.card V : ℝ) * ((Q.card : ℝ) * (s : ℝ)) :=
                mul_le_mul_of_nonneg_left hR_card_le (by positivity)
        calc (1 / (Fintype.card V : ℝ) ^ 2) *
                ((∑ X ∈ Q_chop, ∑ Y ∈ Q_chop, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2) -
                  (∑ X ∈ P', ∑ Y ∈ P', (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2))
            ≤ (1 / (Fintype.card V : ℝ) ^ 2) * (2 * (Fintype.card V : ℝ) * ((Q.card : ℝ) * (s : ℝ))) :=
              mul_le_mul_of_nonneg_left hnum (by positivity)
          _ = 2 * (Q.card : ℝ) * (s : ℝ) / (Fintype.card V : ℝ) := by
              field_simp [hVpos.ne']
      linarith

/-- One full Szemerédi equipartition refinement step:
if the current equipartition `P_cl` (`k` equal-sized clusters of size `s`, exceptional set `V₀`
with `|V₀| < s`, `4 ≤ k`) has more than `ε k²` irregular ordered pairs `(i, j)` (`i ≠ j`),
and `n ≥ 2 * K'` where `K' = max (4 * k) (⌈8 * (k * 2^k + 1) / ε^5⌉₊ + 1)`, then there exists
a new equipartition `(P_cl', V₀')` with `K' ≤ |P_cl'| ≤ 2 * K'` and energy strictly increased
by at least `ε^5 / 4`. -/
lemma szemeredi_refinement_step [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 < ε)
    {P_cl : Finset (Finset V)} {V₀ : Finset V} {s : ℕ}
    (hk4 : 4 ≤ P_cl.card)
    (hcards : ∀ C ∈ P_cl, C.card = s)
    (hdisj : (P_cl : Set (Finset V)).PairwiseDisjoint id)
    (hV0_disj : Disjoint (P_cl.biUnion id) V₀)
    (hunion : P_cl.biUnion id ∪ V₀ = Finset.univ)
    (hV0_lt : V₀.card < s)
    (hirreg : ε * (P_cl.card : ℝ) ^ 2 <
      (((P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2)).card : ℝ))
    (hN_large : 2 * max (4 * P_cl.card) (⌈8 * ((P_cl.card * 2 ^ P_cl.card + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1) ≤
      Fintype.card V) :
    ∃ (P_cl' : Finset (Finset V)) (V₀' : Finset V) (s' : ℕ),
      1 ≤ s' ∧
      max (4 * P_cl.card) (⌈8 * ((P_cl.card * 2 ^ P_cl.card + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1) ≤ P_cl'.card ∧
      P_cl'.card ≤ 2 * max (4 * P_cl.card) (⌈8 * ((P_cl.card * 2 ^ P_cl.card + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1) ∧
      (∀ C ∈ P_cl', C.card = s') ∧
      (P_cl' : Set (Finset V)).PairwiseDisjoint id ∧
      Disjoint (P_cl'.biUnion id) V₀' ∧
      P_cl'.biUnion id ∪ V₀' = Finset.univ ∧
      V₀'.card < s' ∧
      partEnergy G (if V₀.Nonempty then insert V₀ P_cl else P_cl) + ε ^ 5 / 4 ≤
        partEnergy G (if V₀'.Nonempty then insert V₀' P_cl' else P_cl') := by
  set k := P_cl.card
  set K' := max (4 * k) (⌈8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1)
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hsz : s = 0 := by omega
    have hV0z : V₀.card = 0 := by omega
    have hVn : Fintype.card V = 0 := by
      rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hV0_disj,
          Finset.card_biUnion hdisj, hV0z, add_zero]
      exact Finset.sum_eq_zero fun C hC => by dsimp only [id_eq]; rw [hcards C hC, hsz]
    have hKpos : 1 ≤ K' := by omega
    omega
  have hK'_pos : 1 ≤ K' := by omega
  have hV_pos : 0 < Fintype.card V := by omega
  have hV_posR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV_pos
  -- Index `P_cl` by `e : Fin k ≃ P_cl` so we can pick symmetric witnesses for unordered pairs `{i, j}`
  let e : Fin k ≃ {C : Finset V // C ∈ P_cl} := (Fintype.equivFinOfCardEq (Fintype.card_coe P_cl)).symm
  let C : Fin k → Finset V := fun i => (e i).val
  have hC_mem : ∀ i : Fin k, C i ∈ P_cl := fun i => (e i).property
  have hC_inj : Function.Injective C := fun i j h => e.injective (Subtype.ext h)
  have hC_surj : ∀ X ∈ P_cl, ∃ i : Fin k, C i = X := fun X hX =>
    ⟨e.symm ⟨X, hX⟩, by simp [C]⟩
  -- For each unordered pair `i < j` with `¬ IsEpsRegular G ε (C i) (C j)`, choose witnesses `(A, B)`
  have hwit : ∀ i j : Fin k, i < j → ¬ IsEpsRegular G ε (C i) (C j) →
      ∃ p : Finset V × Finset V,
        p.1 ⊆ C i ∧ p.2 ⊆ C j ∧
        ε * ((C i).card : ℝ) ≤ (p.1.card : ℝ) ∧
        ε * ((C j).card : ℝ) ≤ (p.2.card : ℝ) ∧
        ε < |edgeDensity G p.1 p.2 - edgeDensity G (C i) (C j)| := by
    intro i j _ hnr
    unfold IsEpsRegular at hnr
    push Not at hnr
    rcases hnr with ⟨A', hA', B', hB', hAc, hBc, hd⟩
    exact ⟨(A', B'), hA', hB', hAc, hBc, hd⟩
  -- Define for each `i` a family `F i : Fin k → Finset V` of witnessing subsets of `C i`
  let witPair : (i j : Fin k) → Finset V × Finset V := fun i j =>
    if h : i < j ∧ ¬ IsEpsRegular G ε (C i) (C j) then
      Classical.choose (hwit i j h.1 h.2)
    else (∅, ∅)
  let F : Fin k → Fin k → Finset V := fun i j =>
    if i < j then (witPair i j).1
    else if j < i then (witPair j i).2
    else ∅
  -- For every `i`, refine `C i` by `F i` into `≤ 2^k` nonempty atoms
  have hvenn : ∀ i : Fin k, ∃ Pi : Finset (Finset V),
      IsPartitionOf Pi (C i) ∧ Pi.card ≤ 2 ^ k ∧
      ∀ X ∈ Pi, ∀ j : Fin k, X ⊆ F i j ∨ Disjoint X (F i j) :=
    fun i => exists_venn_partition (C i) (F i)
  choose Psub hPsub using hvenn
  -- Combine into refinement `Q` of `P := if V₀.Nonempty then insert V₀ P_cl else P_cl`
  let P : Finset (Finset V) := if V₀.Nonempty then insert V₀ P_cl else P_cl
  let Q_cl : Finset (Finset V) := Finset.univ.biUnion Psub
  let Q : Finset (Finset V) := if V₀.Nonempty then insert V₀ Q_cl else Q_cl
  have hP_part : IsPartitionOf P Finset.univ := by
    refine ⟨?_, ?_, ?_⟩
    · intro X hX
      dsimp only [P] at hX
      split_ifs at hX with hV0ne
      · rcases Finset.mem_insert.mp hX with rfl | hX'
        · exact hV0ne
        · exact Finset.card_pos.mp (by rw [hcards X hX']; omega)
      · exact Finset.card_pos.mp (by rw [hcards X hX]; omega)
    · intro X hX Y hY hne
      dsimp only [P] at hX hY
      split_ifs at hX hY with hV0ne
      · simp only [Finset.mem_coe, Finset.mem_insert] at hX hY
        rcases hX with rfl | hX' <;> rcases hY with rfl | hY'
        · exact absurd rfl hne
        · exact (Disjoint.mono_left (Finset.subset_biUnion_of_mem id hY') hV0_disj).symm
        · exact Disjoint.mono_left (Finset.subset_biUnion_of_mem id hX') hV0_disj
        · exact hdisj hX' hY' hne
      · exact hdisj hX hY hne
    · dsimp only [P]
      split_ifs with hV0ne
      · rw [Finset.biUnion_insert, id_eq, Finset.union_comm, hunion]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hV0ne, Finset.union_empty] at hunion
        exact hunion
  have hQsub_disj : (Set.univ : Set (Fin k)).PairwiseDisjoint Psub := by
    intro i _ j _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro X hXi hXj
    rcases (hPsub i).1.1 X hXi with ⟨v, hvX⟩
    have hvi : v ∈ C i := by rw [← (hPsub i).1.2.2]; exact Finset.mem_biUnion.mpr ⟨X, hXi, hvX⟩
    have hvj : v ∈ C j := by rw [← (hPsub j).1.2.2]; exact Finset.mem_biUnion.mpr ⟨X, hXj, hvX⟩
    exact Finset.disjoint_left.mp (hdisj (hC_mem i) (hC_mem j) (fun h => hne (hC_inj h))) hvi hvj
  have hQ_cl_union : Q_cl.biUnion id = P_cl.biUnion id := by
    ext v
    simp only [Q_cl, Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨X, ⟨i, hXi⟩, hvX⟩
      refine ⟨C i, hC_mem i, ?_⟩
      rw [← (hPsub i).1.2.2]; exact Finset.mem_biUnion.mpr ⟨X, hXi, hvX⟩
    · rintro ⟨U, hU, hvU⟩
      rcases hC_surj U hU with ⟨i, rfl⟩
      rw [← (hPsub i).1.2.2, Finset.mem_biUnion] at hvU
      rcases hvU with ⟨X, hXi, hvX⟩
      exact ⟨X, ⟨i, hXi⟩, hvX⟩
  have hQ_part : IsPartitionOf Q Finset.univ := by
    refine ⟨?_, ?_, ?_⟩
    · intro X hX
      dsimp only [Q] at hX
      split_ifs at hX with hV0ne
      · rcases Finset.mem_insert.mp hX with rfl | hX'
        · exact hV0ne
        · rcases Finset.mem_biUnion.mp hX' with ⟨i, _, hXi⟩; exact (hPsub i).1.1 X hXi
      · rcases Finset.mem_biUnion.mp hX with ⟨i, _, hXi⟩; exact (hPsub i).1.1 X hXi
    · intro X hX Y hY hne
      have hQcl_disj : (Q_cl : Set (Finset V)).PairwiseDisjoint id := by
        intro A hA B hB hAB
        rcases Finset.mem_biUnion.mp hA with ⟨i, _, hAi⟩
        rcases Finset.mem_biUnion.mp hB with ⟨j, _, hBj⟩
        by_cases hij : i = j
        · subst hij; exact (hPsub i).1.2.1 hAi hBj hAB
        · have hsub1 : A ⊆ C i := by rw [← (hPsub i).1.2.2]; exact Finset.subset_biUnion_of_mem id hAi
          have hsub2 : B ⊆ C j := by rw [← (hPsub j).1.2.2]; exact Finset.subset_biUnion_of_mem id hBj
          exact Disjoint.mono hsub1 hsub2 (hdisj (hC_mem i) (hC_mem j) (fun h => hij (hC_inj h)))
      dsimp only [Q] at hX hY
      split_ifs at hX hY with hV0ne
      · simp only [Finset.mem_coe, Finset.mem_insert] at hX hY
        rcases hX with rfl | hX' <;> rcases hY with rfl | hY'
        · exact absurd rfl hne
        · have hsub : Y ⊆ P_cl.biUnion id := by
            rw [← hQ_cl_union]; exact Finset.subset_biUnion_of_mem id hY'
          exact (Disjoint.mono_left hsub hV0_disj).symm
        · have hsub : X ⊆ P_cl.biUnion id := by
            rw [← hQ_cl_union]; exact Finset.subset_biUnion_of_mem id hX'
          exact Disjoint.mono_left hsub hV0_disj
        · exact hQcl_disj hX' hY' hne
      · exact hQcl_disj hX hY hne
    · dsimp only [Q]
      split_ifs with hV0ne
      · rw [Finset.biUnion_insert, id_eq, hQ_cl_union, Finset.union_comm, hunion]
      · rw [hQ_cl_union]
        rw [Finset.not_nonempty_iff_eq_empty.mp hV0ne, Finset.union_empty] at hunion
        exact hunion
  have hQ_card_le : Q.card ≤ k * 2 ^ k + 1 := by
    have hQcl_le : Q_cl.card ≤ k * 2 ^ k := by
      calc Q_cl.card ≤ ∑ i : Fin k, (Psub i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin k, 2 ^ k := Finset.sum_le_sum fun i _ => (hPsub i).2.1
        _ = k * 2 ^ k := by simp
    dsimp only [Q]
    split_ifs
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · omega
  -- Step 1: Energy increment `partEnergy G P + ε^5 / 2 ≤ partEnergy G Q`
  have hE_inc : partEnergy G P + ε ^ 5 / 2 ≤ partEnergy G Q := by
    -- Express `Q` as a disjoint union of sub-partitions of `U ∈ P`
    let refOf : Finset V → Finset (Finset V) := fun U =>
      if hU : U ∈ P_cl then Psub (e.symm ⟨U, hU⟩) else {U}
    have href_part : ∀ U ∈ P, IsPartitionOf (refOf U) U := by
      intro U hU
      by_cases hUcl : U ∈ P_cl
      · simp only [refOf, dif_pos hUcl]
        convert (hPsub (e.symm ⟨U, hUcl⟩)).1
        simp [C]
      · simp only [refOf, dif_neg hUcl]
        have hUne : U.Nonempty := hP_part.1 U hU
        refine ⟨fun X hX => by rw [Finset.mem_singleton.mp hX]; exact hUne, by simp, by simp⟩
    have hQ_eq_ref : Q = P.biUnion refOf := by
      ext X
      have hV0_not_cl : V₀.Nonempty → V₀ ∉ P_cl := by
        intro hne hmem
        rcases hne with ⟨v, hv⟩
        exact Finset.disjoint_left.mp hV0_disj (Finset.mem_biUnion.mpr ⟨V₀, hmem, hv⟩) hv
      have hQcl_mem : ∀ X, X ∈ Q_cl ↔ ∃ U ∈ P_cl, X ∈ refOf U := by
        intro X
        simp only [Q_cl, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hXi⟩
          refine ⟨C i, hC_mem i, ?_⟩
          simp only [refOf, dif_pos (hC_mem i)]
          have : e.symm ⟨C i, hC_mem i⟩ = i := by simp [C]
          rwa [this]
        · rintro ⟨U, hUcl, hXU⟩
          simp only [refOf, dif_pos hUcl] at hXU
          exact ⟨e.symm ⟨U, hUcl⟩, hXU⟩
      dsimp only [Q, P]
      split_ifs with hV0ne
      · simp only [Finset.mem_insert, Finset.mem_biUnion, hQcl_mem]
        constructor
        · rintro (hXV | ⟨U, hUcl, hXU⟩)
          · refine ⟨V₀, Or.inl rfl, ?_⟩
            rw [hXV]
            simp [refOf, dif_neg (hV0_not_cl hV0ne)]
          · exact ⟨U, Or.inr hUcl, hXU⟩
        · rintro ⟨U, hUV | hUcl, hXU⟩
          · rw [hUV] at hXU
            simp only [refOf, dif_neg (hV0_not_cl hV0ne), Finset.mem_singleton] at hXU
            exact Or.inl hXU
          · exact Or.inr ⟨U, hUcl, hXU⟩
      · simp only [Finset.mem_biUnion, hQcl_mem]
    have href_disj : (P : Set (Finset V)).PairwiseDisjoint refOf := by
      intro U1 hU1 U2 hU2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro X hX1 hX2
      rcases (href_part U1 hU1).1 X hX1 with ⟨v, hvX⟩
      have hv1 : v ∈ U1 := by rw [← (href_part U1 hU1).2.2]; exact Finset.mem_biUnion.mpr ⟨X, hX1, hvX⟩
      have hv2 : v ∈ U2 := by rw [← (href_part U2 hU2).2.2]; exact Finset.mem_biUnion.mpr ⟨X, hX2, hvX⟩
      exact Finset.disjoint_left.mp (hP_part.2.1 hU1 hU2 hne) hv1 hv2
    -- Rewrite `∑_{X, Y ∈ Q}` by grouping into `(U, W) ∈ P × P`
    have hQ_sum :
        ∑ X ∈ Q, ∑ Y ∈ Q, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 =
          ∑ U ∈ P, ∑ W ∈ P, ∑ X ∈ refOf U, ∑ Y ∈ refOf W,
            (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
      rw [hQ_eq_ref, Finset.sum_biUnion href_disj]
      apply Finset.sum_congr rfl
      intro U _
      conv_lhs =>
        arg 2; ext X
        rw [Finset.sum_biUnion href_disj]
      rw [Finset.sum_comm]
    -- Every `(U, W) ∈ P × P` gains `≥ 0`, and every irregular `(U, W) ∈ P_cl × P_cl` gains `≥ ε^4 s^2`
    let Irreg := (P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2)
    have hIrreg_sub : Irreg ⊆ P ×ˢ P := by
      intro p hp
      have h1 : p ∈ P_cl ×ˢ P_cl := (Finset.mem_filter.mp hp).1
      rw [Finset.mem_product] at h1 ⊢
      have hPcl_sub : P_cl ⊆ P := by
        dsimp only [P]; split_ifs
        · exact Finset.subset_insert _ _
        · exact Finset.Subset.rfl
      exact ⟨hPcl_sub h1.1, hPcl_sub h1.2⟩
    have hpair_gain : ∀ p ∈ P ×ˢ P,
        (p.1.card : ℝ) * (p.2.card : ℝ) * (edgeDensity G p.1 p.2) ^ 2 +
          (if p ∈ Irreg then ε ^ 4 * ((s : ℝ) ^ 2) else 0) ≤
        ∑ X ∈ refOf p.1, ∑ Y ∈ refOf p.2,
          (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
      intro p hp
      rw [Finset.mem_product] at hp
      by_cases hpI : p ∈ Irreg
      · rw [if_pos hpI]
        have hpI' := Finset.mem_filter.mp hpI
        rw [Finset.mem_product] at hpI'
        rcases hC_surj p.1 hpI'.1.1 with ⟨i, hi⟩
        rcases hC_surj p.2 hpI'.1.2 with ⟨j, hj⟩
        have hij_ne : i ≠ j := fun h => hpI'.2.1 (by rw [← hi, ← hj, h])
        have hnr_ij : ¬ IsEpsRegular G ε (C i) (C j) := hi ▸ hj ▸ hpI'.2.2
        have href_i : refOf p.1 = Psub i := by
          simp only [refOf, dif_pos hpI'.1.1]
          congr 1; apply e.injective; apply Subtype.ext; simpa [C] using hi.symm
        have href_j : refOf p.2 = Psub j := by
          simp only [refOf, dif_pos hpI'.1.2]
          congr 1; apply e.injective; apply Subtype.ext; simpa [C] using hj.symm
        have hcards_eq : (p.1.card : ℝ) * (p.2.card : ℝ) = (s : ℝ) ^ 2 := by
          rw [hcards p.1 hpI'.1.1, hcards p.2 hpI'.1.2, sq]
        rw [href_i, href_j, ← hi, ← hj, ← hcards_eq, hi, hj]
        rcases lt_or_gt_of_ne hij_ne with hlt | hgt
        · have hcond : i < j ∧ ¬ IsEpsRegular G ε (C i) (C j) := ⟨hlt, hnr_ij⟩
          have hspec := Classical.choose_spec (hwit i j hlt hnr_ij)
          have hFi : F i j = (Classical.choose (hwit i j hlt hnr_ij)).1 := by
            simp only [F, witPair, if_pos hlt, dif_pos hcond]
          have hFj : F j i = (Classical.choose (hwit i j hlt hnr_ij)).2 := by
            simp only [F, witPair, if_neg (not_lt.mpr hlt.le), if_pos hlt, dif_pos hcond]
          have hboost := pair_energy_increment_of_witness G hε hspec.1 hspec.2.1 hspec.2.2.1
            hspec.2.2.2.1 hspec.2.2.2.2 (hPsub i).1 (hPsub j).1
            (fun X hX => hFi ▸ (hPsub i).2.2 X hX j)
            (fun Y hY => hFj ▸ (hPsub j).2.2 Y hY i)
          simpa only [hi, hj] using hboost
        · have hnr_ji : ¬ IsEpsRegular G ε (C j) (C i) :=
            fun h => hnr_ij (isEpsRegular_comm G h)
          have hcond : j < i ∧ ¬ IsEpsRegular G ε (C j) (C i) := ⟨hgt, hnr_ji⟩
          have hspec := Classical.choose_spec (hwit j i hgt hnr_ji)
          have hFi : F i j = (Classical.choose (hwit j i hgt hnr_ji)).2 := by
            simp only [F, witPair, if_neg (not_lt.mpr hgt.le), if_pos hgt, dif_pos hcond]
          have hFj : F j i = (Classical.choose (hwit j i hgt hnr_ji)).1 := by
            simp only [F, witPair, if_pos hgt, dif_pos hcond]
          have hd_comm : ε < |edgeDensity G (Classical.choose (hwit j i hgt hnr_ji)).2
              (Classical.choose (hwit j i hgt hnr_ji)).1 - edgeDensity G (C i) (C j)| := by
            rw [edgeDensity_comm G _ _, edgeDensity_comm G (C i) (C j)]
            exact hspec.2.2.2.2
          have hboost := pair_energy_increment_of_witness G hε hspec.2.1 hspec.1 hspec.2.2.2.1
            hspec.2.2.1 hd_comm (hPsub i).1 (hPsub j).1
            (fun X hX => hFi ▸ (hPsub i).2.2 X hX j)
            (fun Y hY => hFj ▸ (hPsub j).2.2 Y hY i)
          simpa only [hi, hj] using hboost
      · rw [if_neg hpI, add_zero]
        exact pair_energy_le_of_refinement G (href_part p.1 hp.1) (href_part p.2 hp.2)
    have hsum_gain :
        (∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2) +
          (Irreg.card : ℝ) * (ε ^ 4 * (s : ℝ) ^ 2) ≤
        ∑ X ∈ Q, ∑ Y ∈ Q, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
      rw [hQ_sum]
      have h1 := Finset.sum_le_sum hpair_gain
      have h2 : ∑ p ∈ P ×ˢ P, (if p ∈ Irreg then ε ^ 4 * (s : ℝ) ^ 2 else 0) =
          (Irreg.card : ℝ) * (ε ^ 4 * (s : ℝ) ^ 2) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hIrreg_sub, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_add_distrib, h2, Finset.sum_product, Finset.sum_product] at h1
      exact h1
    -- Compare `(Irreg.card : ℝ) * (ε^4 * s^2)` with `(ε^5 / 2) * n^2`
    have hks_ge : (4 / 5 : ℝ) * (Fintype.card V : ℝ) ≤ (k : ℝ) * (s : ℝ) := by
      have htot : k * s + V₀.card = Fintype.card V := by
        have h1 : (P_cl.biUnion id).card = k * s := by
          rw [Finset.card_biUnion hdisj]
          trans ∑ _C ∈ P_cl, s
          · exact Finset.sum_congr rfl fun C hC => hcards C hC
          · simp [k]
        rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hV0_disj, h1]
      have hlt : Fintype.card V ≤ (k + 1) * s := by nlinarith
      have hltR : (Fintype.card V : ℝ) ≤ ((k : ℝ) + 1) * (s : ℝ) := by exact_mod_cast hlt
      have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
      have hratio : (4 / 5 : ℝ) * ((k : ℝ) + 1) ≤ (k : ℝ) := by linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) s]
    have hirreg_boost : (ε ^ 5 / 2) * (Fintype.card V : ℝ) ^ 2 ≤
        (Irreg.card : ℝ) * (ε ^ 4 * (s : ℝ) ^ 2) := by
      have h1 : ε * (k : ℝ) ^ 2 ≤ (Irreg.card : ℝ) := hirreg.le
      have h2 : ε ^ 5 * ((k : ℝ) * (s : ℝ)) ^ 2 ≤ (Irreg.card : ℝ) * (ε ^ 4 * (s : ℝ) ^ 2) := by
        calc ε ^ 5 * ((k : ℝ) * (s : ℝ)) ^ 2
            = (ε * (k : ℝ) ^ 2) * (ε ^ 4 * (s : ℝ) ^ 2) := by ring
          _ ≤ (Irreg.card : ℝ) * (ε ^ 4 * (s : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : (16 / 25 : ℝ) * (Fintype.card V : ℝ) ^ 2 ≤ ((k : ℝ) * (s : ℝ)) ^ 2 := by
        nlinarith
      have h4 : (ε ^ 5 / 2) * (Fintype.card V : ℝ) ^ 2 ≤
          ε ^ 5 * ((16 / 25 : ℝ) * (Fintype.card V : ℝ) ^ 2) := by
        have : 0 ≤ ε ^ 5 * (Fintype.card V : ℝ) ^ 2 := by positivity
        linarith
      nlinarith [pow_pos hε 5]
    unfold partEnergy
    have hVsq : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by positivity
    have hdiv := mul_le_mul_of_nonneg_left (by linarith :
        (∑ U ∈ P, ∑ W ∈ P, (U.card : ℝ) * (W.card : ℝ) * (edgeDensity G U W) ^ 2) +
          (ε ^ 5 / 2) * (Fintype.card V : ℝ) ^ 2 ≤
        ∑ X ∈ Q, ∑ Y ∈ Q, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2)
      (by positivity : 0 ≤ 1 / (Fintype.card V : ℝ) ^ 2)
    rw [mul_add] at hdiv
    have hcancel : (1 / (Fintype.card V : ℝ) ^ 2) * ((ε ^ 5 / 2) * (Fintype.card V : ℝ) ^ 2) = ε ^ 5 / 2 := by
      field_simp [hV_posR.ne']
    linarith
  -- Step 2: Chop `Q` into equal-sized `s'`-clusters (`s' = n / K'`)
  set s' : ℕ := Fintype.card V / K'
  have hs'_ge2 : 2 ≤ s' := by
    have : 2 * K' ≤ Fintype.card V := hN_large
    exact (Nat.le_div_iff_mul_le (by omega)).mpr this
  have hs'_ge1 : 1 ≤ s' := by omega
  rcases equipartition_chop_energy G hQ_part hs'_ge1 with
    ⟨P_cl', V₀', hcards', hdisj', hV0_disj', hunion', hV0_lt', hE_chop⟩
  -- Bound `K' ≤ P_cl'.card ≤ 2 * K'`
  have htot' : P_cl'.card * s' + V₀'.card = Fintype.card V := by
    have h1 : (P_cl'.biUnion id).card = P_cl'.card * s' := by
      rw [Finset.card_biUnion hdisj']
      trans ∑ _C ∈ P_cl', s'
      · exact Finset.sum_congr rfl fun C hC => hcards' C hC
      · simp
    rw [← Finset.card_univ, ← hunion', Finset.card_union_of_disjoint hV0_disj', h1]
  have hP'_ge : K' ≤ P_cl'.card := by
    have h1 : K' * s' ≤ Fintype.card V := Nat.mul_div_le (Fintype.card V) K'
    have h2 : Fintype.card V < (P_cl'.card + 1) * s' := by nlinarith
    have h3 : K' * s' < (P_cl'.card + 1) * s' := lt_of_le_of_lt h1 h2
    have h4 : K' < P_cl'.card + 1 := Nat.lt_of_mul_lt_mul_right h3
    omega
  have hP'_le : P_cl'.card ≤ 2 * K' := by
    have h1 : Fintype.card V < K' * (s' + 1) := by
      have hdiv := Nat.div_add_mod (Fintype.card V) K'
      have hmod := Nat.mod_lt (Fintype.card V) (by omega : 0 < K')
      dsimp only [s']
      nlinarith
    have h2 : P_cl'.card * s' ≤ Fintype.card V := by omega
    have h3 : K' * (s' + 1) ≤ (2 * K') * s' := by nlinarith
    have h4 : P_cl'.card * s' < (2 * K' + 1) * s' := by nlinarith
    have h5 : P_cl'.card < 2 * K' + 1 := Nat.lt_of_mul_lt_mul_right h4
    omega
  -- Bound the slicing energy loss `2 * |Q| * s' / n ≤ ε^5 / 4`
  have hloss_le : 2 * (Q.card : ℝ) * (s' : ℝ) / (Fintype.card V : ℝ) ≤ ε ^ 5 / 4 := by
    have hs'_le : (s' : ℝ) ≤ (Fintype.card V : ℝ) / (K' : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < K'))]
      exact_mod_cast Nat.div_mul_le_self (Fintype.card V) K'
    have hQ_leR : (Q.card : ℝ) ≤ ((k * 2 ^ k + 1 : ℕ) : ℝ) := by exact_mod_cast hQ_card_le
    have hK'_big : 8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5 ≤ (K' : ℝ) := by
      have h1 : 8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5 ≤
          (⌈8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ⌈8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1 ≤ K' := le_max_right _ _
      have h3 : ((⌈8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1 : ℕ) : ℝ) ≤ (K' : ℝ) :=
        Nat.cast_le.mpr h2
      rw [Nat.cast_add, Nat.cast_one] at h3
      linarith
    have hKposR : (0 : ℝ) < (K' : ℝ) := by exact_mod_cast (by omega : 0 < K')
    have hQdivK : 2 * (Q.card : ℝ) / (K' : ℝ) ≤ ε ^ 5 / 4 := by
      rw [div_le_iff₀ hKposR]
      have hmul := (div_le_iff₀ (pow_pos hε 5)).mp hK'_big
      nlinarith [pow_pos hε 5]
    have hsimp_div : ∀ a b c : ℝ, b ≠ 0 → a * (b / c) / b = a / c := fun a b c hb => by
      field_simp [hb]
    calc 2 * (Q.card : ℝ) * (s' : ℝ) / (Fintype.card V : ℝ)
        ≤ 2 * (Q.card : ℝ) * ((Fintype.card V : ℝ) / (K' : ℝ)) / (Fintype.card V : ℝ) := by
          apply div_le_div_of_nonneg_right _ hV_posR.le
          exact mul_le_mul_of_nonneg_left hs'_le (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      _ = 2 * (Q.card : ℝ) / (K' : ℝ) := hsimp_div _ _ _ hV_posR.ne'
      _ ≤ ε ^ 5 / 4 := hQdivK
  exact ⟨P_cl', V₀', s', hs'_ge1, hP'_ge, hP'_le, hcards', hdisj', hV0_disj', hunion', hV0_lt',
    by linarith⟩

/-- Explicit tower step function for Szemerédi's Regularity Lemma. -/
def szemerediStep (ε : ℝ) (k : ℕ) : ℕ :=
  2 * max (4 * k) (⌈8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1)

/-- Explicit tower bound `M(ε, m₀)` for Szemerédi's Regularity Lemma, obtained by iterating
`szemerediStep ε` for `⌈4 / ε^5⌉₊ + 1` steps starting from `max m₀ (max 4 (⌈1 / ε⌉₊ + 1))`. -/
def szemerediTower (ε : ℝ) (m₀ : ℕ) : ℕ :=
  (szemerediStep ε)^[⌈4 / ε ^ 5⌉₊ + 1] (max m₀ (max 4 (⌈1 / ε⌉₊ + 1)))

lemma szemerediStep_mono {ε : ℝ} (hε : 0 < ε) {a b : ℕ} (hab : a ≤ b) :
    szemerediStep ε a ≤ szemerediStep ε b := by
  unfold szemerediStep
  apply Nat.mul_le_mul_left
  apply max_le
  · exact le_trans (Nat.mul_le_mul_left 4 hab) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    apply Nat.add_le_add_right
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ (pow_pos hε 5).le
    have hpow : a * 2 ^ a + 1 ≤ b * 2 ^ b + 1 := by
      have h1 : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
      exact Nat.add_le_add_right (Nat.mul_le_mul hab h1) 1
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpow) (by norm_num)

lemma le_szemerediStep (ε : ℝ) (k : ℕ) : k ≤ szemerediStep ε k := by
  unfold szemerediStep
  have h1 : 4 * k ≤ max (4 * k) (⌈8 * ((k * 2 ^ k + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1) := le_max_left _ _
  omega

lemma iterate_szemerediStep_mono {ε : ℝ} (hε : 0 < ε) (t : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (szemerediStep ε)^[t] a ≤ (szemerediStep ε)^[t] b := by
  induction t generalizing a b with
  | zero => exact hab
  | succ t ih =>
    simp only [Function.iterate_succ_apply']
    exact szemerediStep_mono hε (ih hab)

lemma iterate_szemerediStep_le_of_le (ε : ℝ) (a : ℕ) {t1 t2 : ℕ} (h : t1 ≤ t2) :
    (szemerediStep ε)^[t1] a ≤ (szemerediStep ε)^[t2] a := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    simp only [Function.iterate_succ_apply']
    exact ih.trans (le_szemerediStep ε _)

/-- **Full Equipartition Szemerédi Regularity Lemma:**
For every `ε > 0` and `m₀ ≥ 1`, there exists `M : ℕ` (explicitly `szemerediTower ε m₀`) such that
for EVERY finite graph `G` on `n ≥ m₀` vertices, there exists an `ε`-regular equipartition
`V = V₀ ⊔ ⋃_{i : Fin k} C i` satisfying:
1. `m₀ ≤ k ≤ M`,
2. All `k` clusters `C i` have the **exact same size** `s ≥ 1`,
3. The exceptional set `V₀` satisfies `(V₀.card : ℝ) ≤ ε * n`,
4. At most `ε * k²` ordered pairs `(i, j)` (`i ≠ j`) are NOT `ε`-regular. -/
theorem szemeredi_regularity_lemma (ε : ℝ) (hε : 0 < ε) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    ∃ M : ℕ, m₀ ≤ M ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        m₀ ≤ Fintype.card V →
        ∃ (k s : ℕ) (C : Fin k → Finset V) (V₀ : Finset V),
          m₀ ≤ k ∧ k ≤ M ∧ 1 ≤ s ∧
          (∀ i : Fin k, (C i).card = s) ∧
          (∀ i j : Fin k, i ≠ j → Disjoint (C i) (C j)) ∧
          Disjoint (Finset.univ.biUnion C) V₀ ∧
          Finset.univ.biUnion C ∪ V₀ = Finset.univ ∧
          (V₀.card : ℝ) ≤ ε * (Fintype.card V : ℝ) ∧
          (((Finset.univ : Finset (Fin k × Fin k)).filter
            (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε (C p.1) (C p.2))).card : ℝ) ≤
            ε * (k : ℝ) ^ 2 := by
  set K₀ : ℕ := max m₀ (max 4 (⌈1 / ε⌉₊ + 1))
  set T : ℕ := ⌈4 / ε ^ 5⌉₊ + 1
  set M : ℕ := (szemerediStep ε)^[T] K₀
  have hK0_m0 : m₀ ≤ K₀ := le_max_left _ _
  have hK0_4 : 4 ≤ K₀ := (le_max_left 4 _).trans (le_max_right _ _)
  have hK0_eps : 1 / ε < (K₀ : ℝ) := by
    have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈1 / ε⌉₊ + 1 ≤ K₀ := (le_max_right 4 _).trans (le_max_right _ _)
    have h3 : ((⌈1 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (K₀ : ℝ) := Nat.cast_le.mpr h2
    push_cast at h3; linarith
  have hM_ge : m₀ ≤ M := hK0_m0.trans (iterate_szemerediStep_le_of_le ε K₀ (Nat.zero_le T))
  refine ⟨M, hM_ge, ?_⟩
  intro V _ _ G _ hVm0
  -- Case 1: `Fintype.card V ≤ M` -> use singleton equipartition (`k = |V|`, `s = 1`, `V₀ = ∅`)
  by_cases hsmall : Fintype.card V ≤ M
  · let eV : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    refine ⟨Fintype.card V, 1, fun i => {eV i}, ∅, hVm0, hsmall, le_rfl,
      fun _ => Finset.card_singleton _, ?_, by simp, ?_, by simp; positivity, ?_⟩
    · intro i j hij
      rw [Finset.disjoint_singleton]
      exact fun h => hij (eV.injective h)
    · ext v
      simp only [Finset.union_empty, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton,
        true_and, iff_true]
      exact ⟨eV.symm v, by simp⟩
    · have hempty : (Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
          (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε {eV p.1} {eV p.2}) = ∅ := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and, not_not]
        intro _
        exact isEpsRegular_singleton G hε (eV p.1) (eV p.2)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
  · -- Case 2: `M < Fintype.card V`, run energy-increment induction up to `T` steps
    push Not at hsmall
    -- Helper to extract `Fin k` indexing from a `Finset (Finset V)` equipartition
    have hfinish : ∀ (P_cl : Finset (Finset V)) (V₀ : Finset V) (s : ℕ),
        K₀ ≤ P_cl.card → P_cl.card ≤ M → 1 ≤ s →
        (∀ X ∈ P_cl, X.card = s) →
        (P_cl : Set (Finset V)).PairwiseDisjoint id →
        Disjoint (P_cl.biUnion id) V₀ →
        P_cl.biUnion id ∪ V₀ = Finset.univ →
        V₀.card < s →
        (((P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2)).card : ℝ) ≤
          ε * (P_cl.card : ℝ) ^ 2 →
        ∃ (k s : ℕ) (C : Fin k → Finset V) (V₀ : Finset V),
          m₀ ≤ k ∧ k ≤ M ∧ 1 ≤ s ∧
          (∀ i : Fin k, (C i).card = s) ∧
          (∀ i j : Fin k, i ≠ j → Disjoint (C i) (C j)) ∧
          Disjoint (Finset.univ.biUnion C) V₀ ∧
          Finset.univ.biUnion C ∪ V₀ = Finset.univ ∧
          (V₀.card : ℝ) ≤ ε * (Fintype.card V : ℝ) ∧
          (((Finset.univ : Finset (Fin k × Fin k)).filter
            (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε (C p.1) (C p.2))).card : ℝ) ≤
            ε * (k : ℝ) ^ 2 := by
      intro P_cl V₀ s hk_ge hk_le hs1 hcards hdisj hV0_disj hunion hV0_lt hreg
      let eP : Fin P_cl.card ≃ {X : Finset V // X ∈ P_cl} :=
        (Fintype.equivFinOfCardEq (Fintype.card_coe P_cl)).symm
      let C : Fin P_cl.card → Finset V := fun i => (eP i).val
      have hbi : Finset.univ.biUnion C = P_cl.biUnion id := by
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
        constructor
        · rintro ⟨i, hv⟩; exact ⟨C i, (eP i).property, hv⟩
        · rintro ⟨X, hX, hv⟩; exact ⟨eP.symm ⟨X, hX⟩, by simp [C, hv]⟩
      have hV0_bound : (V₀.card : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
        have htot : P_cl.card * s ≤ Fintype.card V := by
          have h1 : (P_cl.biUnion id).card = P_cl.card * s := by
            rw [Finset.card_biUnion hdisj]
            trans ∑ _X ∈ P_cl, s
            · exact Finset.sum_congr rfl fun X hX => hcards X hX
            · simp
          rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hV0_disj, h1]
          omega
        have hK0pos : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast (by omega : 0 < K₀)
        have h1 : (K₀ : ℝ) * (V₀.card : ℝ) ≤ (Fintype.card V : ℝ) := by
          have hnat : K₀ * V₀.card ≤ Fintype.card V :=
            (Nat.mul_le_mul hk_ge hV0_lt.le).trans htot
          exact_mod_cast hnat
        have h2 : (1 / ε) * (V₀.card : ℝ) ≤ (Fintype.card V : ℝ) :=
          (mul_le_mul_of_nonneg_right hK0_eps.le (Nat.cast_nonneg _)).trans h1
        have h3 := mul_le_mul_of_nonneg_left h2 hε.le
        rw [← mul_assoc, mul_one_div_cancel hε.ne', one_mul] at h3
        exact h3
      have hcard_irreg :
          ((Finset.univ : Finset (Fin P_cl.card × Fin P_cl.card)).filter
            (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε (C p.1) (C p.2))).card =
          ((P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2)).card := by
        refine Finset.card_bij (fun p _ => (C p.1, C p.2)) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
          exact ⟨⟨(eP p.1).property, (eP p.2).property⟩,
            fun h => hp.1 (eP.injective (Subtype.ext h)), hp.2⟩
        · intro p1 _ p2 _ h
          rcases Prod.mk.inj h with ⟨h1, h2⟩
          exact Prod.ext (eP.injective (Subtype.ext h1)) (eP.injective (Subtype.ext h2))
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_product] at hq
          refine ⟨(eP.symm ⟨q.1, hq.1.1⟩, eP.symm ⟨q.2, hq.1.2⟩), ?_, by simp [C]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => hq.2.1 (by
            have := congrArg (fun i => (eP i).val) h; simpa using this), by simpa [C] using hq.2.2⟩
      refine ⟨P_cl.card, s, C, V₀, hK0_m0.trans hk_ge, hk_le, hs1,
        fun i => hcards (C i) (eP i).property,
        fun i j hij => hdisj (eP i).property (eP j).property (fun h => hij (eP.injective (Subtype.ext h))),
        hbi ▸ hV0_disj, hbi ▸ hunion, hV0_bound, ?_⟩
      rw [hcard_irreg]; exact hreg
    -- Build initial equipartition at `t = 0` with `s₀ = |V| / K₀`
    have hK0_le_M : K₀ ≤ M := iterate_szemerediStep_le_of_le ε K₀ (Nat.zero_le T)
    have hV_gt_2K0 : 2 * K₀ ≤ Fintype.card V := by
      have hT1 : 1 ≤ T := Nat.succ_le_succ (Nat.zero_le _)
      have hstep : 2 * K₀ ≤ szemerediStep ε K₀ := by
        unfold szemerediStep
        have : 4 * K₀ ≤ max (4 * K₀) (⌈8 * ((K₀ * 2 ^ K₀ + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1) := le_max_left _ _
        omega
      have h1 : szemerediStep ε K₀ ≤ M := by
        have := iterate_szemerediStep_le_of_le ε K₀ hT1
        simpa using this
      omega
    set s₀ : ℕ := Fintype.card V / K₀
    have hs0_ge2 : 2 ≤ s₀ := (Nat.le_div_iff_mul_le (by omega)).mpr hV_gt_2K0
    rcases exists_slicing (Finset.univ : Finset V) (by omega : 1 ≤ s₀) with
      ⟨P₀, V₀_init, hcards0, hdisj0, hV0_disj0, hunion0, hV0_lt0⟩
    have htot0 : P₀.card * s₀ + V₀_init.card = Fintype.card V := by
      have h1 : (P₀.biUnion id).card = P₀.card * s₀ := by
        rw [Finset.card_biUnion hdisj0]
        trans ∑ _C ∈ P₀, s₀
        · exact Finset.sum_congr rfl fun C hC => hcards0 C hC
        · simp
      rw [← Finset.card_univ, ← hunion0, Finset.card_union_of_disjoint hV0_disj0, h1]
    have hP0_ge : K₀ ≤ P₀.card := by
      have h1 : K₀ * s₀ ≤ Fintype.card V := Nat.mul_div_le (Fintype.card V) K₀
      have h2 : Fintype.card V < (P₀.card + 1) * s₀ := by nlinarith
      have h3 : K₀ < P₀.card + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 h2)
      omega
    have hP0_le : P₀.card ≤ 2 * K₀ := by
      have h1 : Fintype.card V < K₀ * (s₀ + 1) := by
        have hdiv := Nat.div_add_mod (Fintype.card V) K₀
        have hmod := Nat.mod_lt (Fintype.card V) (by omega : 0 < K₀)
        dsimp only [s₀]
        nlinarith
      have h2 : P₀.card * s₀ ≤ Fintype.card V := by omega
      have h3 : K₀ * (s₀ + 1) ≤ (2 * K₀) * s₀ := by nlinarith
      have h4 : P₀.card < 2 * K₀ + 1 := Nat.lt_of_mul_lt_mul_right (by nlinarith)
      omega
    -- Induction on `t ≤ T`: either we already found an `ε`-regular equipartition, or we have an
    -- equipartition at step `t` with `K₀ ≤ |P_t| ≤ (szemerediStep ε)^[t] (2 * K₀)` and energy `≥ t * ε^5 / 4`
    -- Wait: notice `2 * K₀ ≤ szemerediStep ε K₀`, so starting at `t = 0` with `|P₀| ≤ szemerediStep ε K₀`
    -- needs `T` steps from `1`! Better: note `M = (szemerediStep ε)^[T] K₀`, and if `t < T` then
    -- `(szemerediStep ε)^[t+1] K₀ ≤ M`! Wait: check `t = 0`: `2 * K₀ ≤ szemerediStep ε K₀`, so at step `t`,
    -- `|P_t| ≤ (szemerediStep ε)^[t + 1] K₀` — wait: at `t = T`, we want `|P_T| ≤ M` AND energy `≥ T * ε^5 / 4 > 1` (impossible!).
    -- Wait: at step `t = ⌈4 / ε^5⌉₊` (so `t = T - 1` steps from `0` if `T = ⌈4/ε^5⌉₊ + 1`),
    -- `t * (ε^5 / 4) ≥ 1`, and if we need strictly `> 1`, we take `T_loop = ⌈4 / ε^5⌉₊ + 1` steps,
    -- which reaches `(szemerediStep ε)^[T_loop] (2 * K₀)` — wait: let's simply define
    -- `P₀` with `K₀` clusters (by merging the extra `P₀.card - K₀` chunks into `V₀`? No, simpler:
    -- just bound `M` with `T + 1` iterations in the theorem!).
    -- Even simpler: let's check `P₀.card ≤ szemerediStep ε K₀`!
    -- If `T_max := ⌈4 / ε^5⌉₊ + 1`, let's verify at `t = T_max`: energy `≥ (⌈4 / ε^5⌉₊ + 1) * ε^5 / 4 > 1`, IMPOSSIBLE!
    -- So the loop MUST terminate at some `t < T_max`, where `|P_t| ≤ (szemerediStep ε)^[t] (2 * K₀) ≤ (szemerediStep ε)^[t + 1] K₀ ≤ (szemerediStep ε)^[T_max] K₀ = M`!!
    -- WHOA!! CHECK THAT!
    -- At `t = 0`: `P₀.card ≤ 2 * K₀ ≤ (szemerediStep ε)^[1] K₀`.
    -- At `t` (`t < T`): `P_t.card ≤ (szemerediStep ε)^[t + 1] K₀ ≤ (szemerediStep ε)^[T] K₀ = M`!
    -- If `t + 1 < T`: `szemerediStep ε P_t.card ≤ szemerediStep ε ((szemerediStep ε)^[t + 1] K₀) = (szemerediStep ε)^[t + 2] K₀ ≤ M < |V|`!
    -- Wait: at `t = T - 1 = ⌈4 / ε^5⌉₊`: `energy ≥ (⌈4 / ε^5⌉₊) * ε^5 / 4 ≥ 1`!
    -- Can `energy = 1` AND still be irregular?
    -- If `energy = 1` and irregular, ONE more step (`t = T`) would give `energy ≥ 1 + ε^5 / 4 > 1`, CONTRADICTION!
    -- For that last step `t = T - 1 → T`, we need `szemerediStep ε P_{T-1}.card ≤ |V|`, i.e., `(szemerediStep ε)^[T + 1] K₀ ≤ |V|`!
    -- We have `M = (szemerediStep ε)^[T] K₀`; let's simply check if `T = ⌈4 / ε^5⌉₊ + 1` works when `M = (szemerediStep ε)^[T + 1] K₀`!
    -- YES!! Wait: let's just check right here: we already chose `M` above, so let's handle it cleanly by proving the induction for `t ≤ ⌈4 / ε^5⌉₊ + 1` with `M' = (szemerediStep ε)^[T + 1] K₀`!
    have hstep_base : P₀.card ≤ (szemerediStep ε)^[1] K₀ := by
      simp only [Function.iterate_one, szemerediStep]
      have : 4 * K₀ ≤ max (4 * K₀) (⌈8 * ((K₀ * 2 ^ K₀ + 1 : ℕ) : ℝ) / ε ^ 5⌉₊ + 1) := le_max_left _ _
      omega
    -- Wait: we only know `M < Fintype.card V` where `M = (szemerediStep ε)^[T] K₀`.
    -- Notice: if `t = 0`, `|P₀| ≤ 2 K₀ ≤ (szemerediStep ε)^[1] K₀`.
    -- Actually, at `t = T - 1`: `P_{T-1}.card ≤ M`. Could `partEnergy = 1`?
    -- Wait: if `partEnergy = 1`, can ANY pair `(U, W)` with `U, W ∈ P` be irregular?!
    -- CHECK!! If `partEnergy G P = 1`, then for EVERY `U, W ∈ P`, `edgeDensity G U W = 1` (since `0 ≤ d(U, W) ≤ 1` and `∑ |U||W| d(U, W)^2 = ∑ |U||W|`)!!
    -- Wait: if `edgeDensity G U W = 1`, then EVERY pair `(u, w) ∈ U × W` is adjacent in `G`!
    -- So for ANY nonempty `A' ⊆ U, B' ⊆ W`, `edgeDensity G A' B' = 1 = edgeDensity G U W`, so `(U, W)` IS `ε`-REGULAR!!
    -- OMG!! WHAT A GENIUS OBSERVATION!!
    -- If `partEnergy G P ≥ 1`, then `partEnergy G P = 1`, which forces ALL pairs to have density `1`, so ZERO pairs are irregular — WE NEVER EVEN NEED STEP `T`!!
    -- At `t = ⌈4 / ε^5⌉₊ = T - 1`: `partEnergy ≥ (⌈4 / ε^5⌉₊) * ε^5 / 4 ≥ 1`, SO IT IS ALREADY `ε`-REGULAR!!
    -- AND for EVERY `t < T - 1`, `t + 2 ≤ T`, so `(szemerediStep ε)^[t + 2] K₀ ≤ (szemerediStep ε)^[T] K₀ = M < |V|`!!
    have hfull_reg_of_energy_one : ∀ (P_cl : Finset (Finset V)) (V₀ : Finset V),
        (∀ X ∈ P_cl, X.Nonempty) →
        (P_cl : Set (Finset V)).PairwiseDisjoint id →
        Disjoint (P_cl.biUnion id) V₀ →
        P_cl.biUnion id ∪ V₀ = Finset.univ →
        1 ≤ partEnergy G (if V₀.Nonempty then insert V₀ P_cl else P_cl) →
        ∀ U ∈ P_cl, ∀ W ∈ P_cl, IsEpsRegular G ε U W := by
      intro P_cl V₀ hne_cl hdisj_cl hV0d hun hE1 U hU W hW
      let P := if V₀.Nonempty then insert V₀ P_cl else P_cl
      have hP_part : IsPartitionOf P Finset.univ := by
        refine ⟨?_, ?_, ?_⟩
        · intro X hX; dsimp only [P] at hX; split_ifs at hX with h0
          · rcases Finset.mem_insert.mp hX with rfl | hX'; exact h0; exact hne_cl X hX'
          · exact hne_cl X hX
        · intro X hX Y hY hne; dsimp only [P] at hX hY; split_ifs at hX hY with h0
          · simp only [Finset.mem_coe, Finset.mem_insert] at hX hY
            rcases hX with rfl | hX' <;> rcases hY with rfl | hY'
            · exact absurd rfl hne
            · exact (Disjoint.mono_left (Finset.subset_biUnion_of_mem id hY') hV0d).symm
            · exact Disjoint.mono_left (Finset.subset_biUnion_of_mem id hX') hV0d
            · exact hdisj_cl hX' hY' hne
          · exact hdisj_cl hX hY hne
        · dsimp only [P]; split_ifs with h0
          · rw [Finset.biUnion_insert, id_eq, Finset.union_comm, hun]
          · rw [Finset.not_nonempty_iff_eq_empty.mp h0, Finset.union_empty] at hun; exact hun
      have hU_P : U ∈ P := by dsimp only [P]; split_ifs; exact Finset.mem_insert_of_mem hU; exact hU
      have hW_P : W ∈ P := by dsimp only [P]; split_ifs; exact Finset.mem_insert_of_mem hW; exact hW
      have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
      -- Since `partEnergy G P ≥ 1`, `∑_{X, Y ∈ P} |X| |Y| (1 - d(X, Y)^2) ≤ 0`, so every term is `0`
      have hzero_sum :
          ∑ X ∈ P, ∑ Y ∈ P, (X.card : ℝ) * (Y.card : ℝ) * (1 - (edgeDensity G X Y) ^ 2) ≤ 0 := by
        have hsum_card : ∑ X ∈ P, ∑ Y ∈ P, (X.card : ℝ) * (Y.card : ℝ) = (Fintype.card V : ℝ) ^ 2 := by
          have hc : ∑ X ∈ P, (X.card : ℝ) = (Fintype.card V : ℝ) := by
            have := card_eq_sum_of_isPartitionOf hP_part
            rw [Finset.card_univ] at this
            exact_mod_cast this.symm
          simp only [← Finset.mul_sum, ← Finset.sum_mul, hc, sq]
        have hE_mul : (Fintype.card V : ℝ) ^ 2 ≤
            ∑ X ∈ P, ∑ Y ∈ P, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2 := by
          unfold partEnergy at hE1
          have := mul_le_mul_of_nonneg_left hE1 (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2)
          rw [← mul_assoc, mul_one_div_cancel (by positivity : (Fintype.card V : ℝ) ^ 2 ≠ 0), one_mul] at this
          linarith
        have hexp :
            ∑ X ∈ P, ∑ Y ∈ P, (X.card : ℝ) * (Y.card : ℝ) * (1 - (edgeDensity G X Y) ^ 2) =
              (∑ X ∈ P, ∑ Y ∈ P, (X.card : ℝ) * (Y.card : ℝ)) -
              (∑ X ∈ P, ∑ Y ∈ P, (X.card : ℝ) * (Y.card : ℝ) * (edgeDensity G X Y) ^ 2) := by
          simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
        linarith
      have hterm_nn : ∀ X ∈ P, ∀ Y ∈ P,
          0 ≤ (X.card : ℝ) * (Y.card : ℝ) * (1 - (edgeDensity G X Y) ^ 2) := by
        intro X _ Y _
        have h1 := edgeDensity_nonneg G X Y
        have h2 := edgeDensity_le_one G X Y
        have hsq : 0 ≤ 1 - (edgeDensity G X Y) ^ 2 := by nlinarith
        positivity
      have hUW_zero : (U.card : ℝ) * (W.card : ℝ) * (1 - (edgeDensity G U W) ^ 2) = 0 := by
        have hle : (U.card : ℝ) * (W.card : ℝ) * (1 - (edgeDensity G U W) ^ 2) ≤ 0 :=
          (Finset.single_le_sum (fun Y hY => hterm_nn U hU_P Y hY) hW_P).trans
            ((Finset.single_le_sum (fun X hX => Finset.sum_nonneg fun Y hY => hterm_nn X hX Y hY) hU_P).trans
              hzero_sum)
        exact le_antisymm hle (hterm_nn U hU_P W hW_P)
      have hUpos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast (hne_cl U hU).card_pos
      have hWpos : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast (hne_cl W hW).card_pos
      have hd1 : edgeDensity G U W = 1 := by
        rcases mul_eq_zero.mp hUW_zero with hUW0 | h1d
        · exact absurd hUW0 (mul_pos hUpos hWpos).ne'
        · have hdn := edgeDensity_nonneg G U W
          nlinarith
      -- `edgeDensity G U W = 1` means EVERY `(u, w) ∈ U × W` is adjacent!
      have hall_adj : ∀ u ∈ U, ∀ w ∈ W, G.Adj u w := by
        have hcard_eq : ((U ×ˢ W).filter (fun p => G.Adj p.1 p.2)).card = (U ×ˢ W).card := by
          have h1 := mul_edgeDensity_eq G U W
          rw [hd1, mul_one] at h1
          rw [Finset.card_product]
          exact_mod_cast h1.symm
        have hfilt_eq : (U ×ˢ W).filter (fun p => G.Adj p.1 p.2) = U ×ˢ W :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard_eq.ge
        intro u hu w hw
        have hmem : (u, w) ∈ (U ×ˢ W).filter (fun p => G.Adj p.1 p.2) := by
          rw [hfilt_eq]; exact Finset.mem_product.mpr ⟨hu, hw⟩
        exact (Finset.mem_filter.mp hmem).2
      intro A' hA' B' hB' hAc hBc
      have hA'pos : (0 : ℝ) < (A'.card : ℝ) := lt_of_lt_of_le (mul_pos hε hUpos) hAc
      have hB'pos : (0 : ℝ) < (B'.card : ℝ) := lt_of_lt_of_le (mul_pos hε hWpos) hBc
      have hdA'B' : edgeDensity G A' B' = 1 := by
        unfold edgeDensity edgeCount
        have hfilt : (A' ×ˢ B').filter (fun p => G.Adj p.1 p.2) = A' ×ˢ B' := by
          rw [Finset.filter_eq_self]
          intro p hp
          rw [Finset.mem_product] at hp
          exact hall_adj p.1 (hA' hp.1) p.2 (hB' hp.2)
        rw [hfilt, Finset.card_product, Nat.cast_mul, div_self (mul_pos hA'pos hB'pos).ne']
      rw [hdA'B', hd1, sub_self, abs_zero]
      exact hε.le
    -- Now prove by induction on `t` (`t ≤ ⌈4 / ε^5⌉₊`): either the final goal holds, OR there exists
    -- an equipartition at step `t` with `K₀ ≤ |P_cl| ≤ (szemerediStep ε)^[t + 1] K₀` and energy `≥ t * (ε^5 / 4)`
    have hloop : ∀ t : ℕ, t ≤ ⌈4 / ε ^ 5⌉₊ →
        (∃ (k s : ℕ) (C : Fin k → Finset V) (V₀ : Finset V),
          m₀ ≤ k ∧ k ≤ M ∧ 1 ≤ s ∧
          (∀ i : Fin k, (C i).card = s) ∧
          (∀ i j : Fin k, i ≠ j → Disjoint (C i) (C j)) ∧
          Disjoint (Finset.univ.biUnion C) V₀ ∧
          Finset.univ.biUnion C ∪ V₀ = Finset.univ ∧
          (V₀.card : ℝ) ≤ ε * (Fintype.card V : ℝ) ∧
          (((Finset.univ : Finset (Fin k × Fin k)).filter
            (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε (C p.1) (C p.2))).card : ℝ) ≤
            ε * (k : ℝ) ^ 2) ∨
        (∃ (P_cl : Finset (Finset V)) (V₀ : Finset V) (s : ℕ),
          K₀ ≤ P_cl.card ∧ P_cl.card ≤ (szemerediStep ε)^[t + 1] K₀ ∧ 1 ≤ s ∧
          (∀ X ∈ P_cl, X.card = s) ∧
          (P_cl : Set (Finset V)).PairwiseDisjoint id ∧
          Disjoint (P_cl.biUnion id) V₀ ∧
          P_cl.biUnion id ∪ V₀ = Finset.univ ∧
          V₀.card < s ∧
          (t : ℝ) * (ε ^ 5 / 4) ≤ partEnergy G (if V₀.Nonempty then insert V₀ P_cl else P_cl)) := by
      intro t
      induction t with
      | zero =>
        intro _
        right
        refine ⟨P₀, V₀_init, s₀, hP0_ge, hstep_base, by omega, hcards0, hdisj0, hV0_disj0,
          hunion0, hV0_lt0, ?_⟩
        rw [Nat.cast_zero, zero_mul]
        unfold partEnergy
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      | succ t ih =>
        intro ht
        rcases ih (Nat.le_of_succ_le ht) with hdone | ⟨P_cl, V₀, s, hk_ge, hk_le, hs1, hcards,
            hdisj, hV0_disj, hunion, hV0_lt, hE⟩
        · exact Or.inl hdone
        · by_cases hreg :
              (((P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2)).card : ℝ) ≤
                ε * (P_cl.card : ℝ) ^ 2
          · left
            have hk_le_M : P_cl.card ≤ M :=
              hk_le.trans (iterate_szemerediStep_le_of_le ε K₀ (by omega))
            exact hfinish P_cl V₀ s hk_ge hk_le_M hs1 hcards hdisj hV0_disj hunion hV0_lt hreg
          · push Not at hreg
            have hstep_le_M : szemerediStep ε P_cl.card ≤ (szemerediStep ε)^[t + 2] K₀ := by
              have := szemerediStep_mono hε hk_le
              simpa [Function.iterate_succ_apply'] using this
            have hstep_le_V : szemerediStep ε P_cl.card ≤ Fintype.card V := by
              have h1 : (szemerediStep ε)^[t + 2] K₀ ≤ M :=
                iterate_szemerediStep_le_of_le ε K₀ (by omega)
              omega
            rcases szemeredi_refinement_step G hε (hK0_4.trans hk_ge) hcards hdisj hV0_disj
                hunion hV0_lt hreg hstep_le_V with
              ⟨P_cl', V₀', s', hs1', hk_ge', hk_le', hcards', hdisj', hV0_disj', hunion',
                hV0_lt', hE'⟩
            right
            have hK0_le_P' : K₀ ≤ P_cl'.card := by
              have : 4 * P_cl.card ≤ P_cl'.card := (le_max_left _ _).trans hk_ge'
              omega
            have hP'_le_step : P_cl'.card ≤ (szemerediStep ε)^[t + 2] K₀ :=
              hk_le'.trans hstep_le_M
            refine ⟨P_cl', V₀', s', hK0_le_P', hP'_le_step, hs1', hcards', hdisj', hV0_disj',
              hunion', hV0_lt', ?_⟩
            push_cast
            linarith
    -- Evaluate at `t = ⌈4 / ε^5⌉₊`: if the second branch occurs, `partEnergy ≥ 1`, hence `ε`-regular!
    rcases hloop ⌈4 / ε ^ 5⌉₊ le_rfl with hdone | ⟨P_cl, V₀, s, hk_ge, hk_le, hs1, hcards,
        hdisj, hV0_disj, hunion, hV0_lt, hE⟩
    · exact hdone
    · have hE1 : 1 ≤ partEnergy G (if V₀.Nonempty then insert V₀ P_cl else P_cl) := by
        have h1 : 4 / ε ^ 5 ≤ (⌈4 / ε ^ 5⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (1 : ℝ) ≤ (⌈4 / ε ^ 5⌉₊ : ℝ) * (ε ^ 5 / 4) := by
          have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ε ^ 5 / 4)
          have hcancel : (4 / ε ^ 5) * (ε ^ 5 / 4) = 1 := by field_simp [(pow_pos hε 5).ne']
          linarith
        linarith
      have hall_reg := hfull_reg_of_energy_one P_cl V₀
        (fun X hX => Finset.card_pos.mp (by rw [hcards X hX]; omega)) hdisj hV0_disj hunion hE1
      have hreg : (((P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2)).card : ℝ) ≤
          ε * (P_cl.card : ℝ) ^ 2 := by
        have hempty : (P_cl ×ˢ P_cl).filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε p.1 p.2) = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.notMem_empty, iff_false,
            not_and, not_not]
          intro hp _; exact hall_reg p.1 hp.1 p.2 hp.2
        rw [hempty, Finset.card_empty, Nat.cast_zero]
        positivity
      exact hfinish P_cl V₀ s hk_ge hk_le hs1 hcards hdisj hV0_disj hunion hV0_lt hreg

end CoreDefinitions

/-! ## Section 2: Triangle Counting Lemma -/

section TriangleCounting

variable {V : Type*} [DecidableEq V]

/-- Number of ordered triples `(x, y, z) ∈ X × Y × Z` forming a triangle in `G`. -/
def triCount (G : SimpleGraph V) [DecidableRel G.Adj] (X Y Z : Finset V) : ℕ :=
  ((X ×ˢ (Y ×ˢ Z)).filter (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2)).card

lemma triCount_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (X Y Z : Finset V) :
    triCount G X Y Z = ∑ x ∈ X, edgeCount G (Y.filter (G.Adj x)) (Z.filter (G.Adj x)) := by
  unfold triCount edgeCount
  have hbi : (X ×ˢ (Y ×ˢ Z)).filter
      (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2) =
      X.biUnion (fun x =>
        (((Y.filter (G.Adj x)) ×ˢ (Z.filter (G.Adj x))).filter (fun p => G.Adj p.1 p.2)).image
          (fun p => (x, p))) := by
    ext ⟨x, y, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx, hy, hz⟩, hxy, hyz, hxz⟩
      exact ⟨x, hx, (y, z), ⟨⟨⟨hy, hxy⟩, ⟨hz, hxz⟩⟩, hyz⟩, rfl⟩
    · rintro ⟨x', hx', ⟨y', z'⟩, ⟨⟨⟨hy', hxy'⟩, ⟨hz', hxz'⟩⟩, hyz'⟩, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, h2⟩
      rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
      exact ⟨⟨hx', hy', hz'⟩, hxy', hyz', hxz'⟩
  rw [hbi, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    rw [Finset.card_image_of_injective]
    intro p1 p2 h; exact (Prod.mk.inj h).2
  · intro x1 _ x2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [Finset.mem_image] at ht1 ht2
    rcases ht1 with ⟨p1, _, rfl⟩
    rcases ht2 with ⟨p2, _, hEq⟩
    exact hne (Prod.mk.inj hEq).1.symm

/-- **Triangle Counting Lemma:**
For any pairwise `ε`-regular triple `(X, Y, Z)` (`0 < ε < 1/2`) with pairwise edge densities
`dXY, dYZ, dXZ ≥ 2ε`, the number of ordered triangles in `X × Y × Z` satisfies
`triCount G X Y Z ≥ (1 - 2ε)(dXY - ε)(dYZ - ε)(dXZ - ε) |X| |Y| |Z|`. -/
theorem triangle_counting_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε_half : ε < 1 / 2)
    (X Y Z : Finset V)
    (hXY : IsEpsRegular G ε X Y) (hYZ : IsEpsRegular G ε Y Z) (hXZ : IsEpsRegular G ε X Z)
    (hdXY : 2 * ε ≤ edgeDensity G X Y)
    (hdYZ : 2 * ε ≤ edgeDensity G Y Z)
    (hdXZ : 2 * ε ≤ edgeDensity G X Z) :
    (1 - 2 * ε) * (edgeDensity G X Y - ε) * (edgeDensity G Y Z - ε) * (edgeDensity G X Z - ε) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤
      (triCount G X Y Z : ℝ) := by
  by_cases hXYZ : X.card = 0 ∨ Y.card = 0 ∨ Z.card = 0
  · rcases hXYZ with h0 | h0 | h0 <;> simp [h0]
  · push Not at hXYZ
    have hXpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hXYZ.1
    have hYpos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hXYZ.2.1
    have hZpos : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hXYZ.2.2
    -- Bad sets in `X`: vertices with too few neighbors in `Y` or in `Z`
    let badY : Finset V := X.filter (fun x => ((Y.filter (G.Adj x)).card : ℝ) < (edgeDensity G X Y - ε) * (Y.card : ℝ))
    let badZ : Finset V := X.filter (fun x => ((Z.filter (G.Adj x)).card : ℝ) < (edgeDensity G X Z - ε) * (Z.card : ℝ))
    have hbadY : (badY.card : ℝ) < ε * (X.card : ℝ) := by
      by_contra hge
      push Not at hge
      have hbad_pos : (0 : ℝ) < (badY.card : ℝ) := lt_of_lt_of_le (mul_pos hε0 hXpos) hge
      have hbad_ne : badY.Nonempty := Finset.card_pos.mp (by exact_mod_cast hbad_pos)
      have hY_eps : ε * (Y.card : ℝ) ≤ (Y.card : ℝ) := by nlinarith
      have hreg := hXY badY (Finset.filter_subset _ _) Y Finset.Subset.rfl hge hY_eps
      have hlow : edgeDensity G X Y - ε ≤ edgeDensity G badY Y := by
        linarith [(abs_le.mp hreg).1]
      have hedge_low : (edgeDensity G X Y - ε) * ((badY.card : ℝ) * (Y.card : ℝ)) ≤
          (edgeCount G badY Y : ℝ) := by
        rw [← mul_edgeDensity_eq G badY Y]
        nlinarith [mul_pos hbad_pos hYpos]
      have hedge_high : (edgeCount G badY Y : ℝ) <
          (edgeDensity G X Y - ε) * ((badY.card : ℝ) * (Y.card : ℝ)) := by
        rw [edgeCount_eq_sum_filter, Nat.cast_sum]
        calc ∑ x ∈ badY, ((Y.filter (G.Adj x)).card : ℝ)
            < ∑ _x ∈ badY, ((edgeDensity G X Y - ε) * (Y.card : ℝ)) :=
              Finset.sum_lt_sum_of_nonempty hbad_ne fun x hx => (Finset.mem_filter.mp hx).2
          _ = (edgeDensity G X Y - ε) * ((badY.card : ℝ) * (Y.card : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
      linarith
    have hbadZ : (badZ.card : ℝ) < ε * (X.card : ℝ) := by
      by_contra hge
      push Not at hge
      have hbad_pos : (0 : ℝ) < (badZ.card : ℝ) := lt_of_lt_of_le (mul_pos hε0 hXpos) hge
      have hbad_ne : badZ.Nonempty := Finset.card_pos.mp (by exact_mod_cast hbad_pos)
      have hZ_eps : ε * (Z.card : ℝ) ≤ (Z.card : ℝ) := by nlinarith
      have hreg := hXZ badZ (Finset.filter_subset _ _) Z Finset.Subset.rfl hge hZ_eps
      have hlow : edgeDensity G X Z - ε ≤ edgeDensity G badZ Z := by
        linarith [(abs_le.mp hreg).1]
      have hedge_low : (edgeDensity G X Z - ε) * ((badZ.card : ℝ) * (Z.card : ℝ)) ≤
          (edgeCount G badZ Z : ℝ) := by
        rw [← mul_edgeDensity_eq G badZ Z]
        nlinarith [mul_pos hbad_pos hZpos]
      have hedge_high : (edgeCount G badZ Z : ℝ) <
          (edgeDensity G X Z - ε) * ((badZ.card : ℝ) * (Z.card : ℝ)) := by
        rw [edgeCount_eq_sum_filter, Nat.cast_sum]
        calc ∑ x ∈ badZ, ((Z.filter (G.Adj x)).card : ℝ)
            < ∑ _x ∈ badZ, ((edgeDensity G X Z - ε) * (Z.card : ℝ)) :=
              Finset.sum_lt_sum_of_nonempty hbad_ne fun x hx => (Finset.mem_filter.mp hx).2
          _ = (edgeDensity G X Z - ε) * ((badZ.card : ℝ) * (Z.card : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
      linarith
    -- Good vertices `X_good = X \ (badY ∪ badZ)`
    let X_good : Finset V := X \ (badY ∪ badZ)
    have hgood_sub : X_good ⊆ X := Finset.sdiff_subset
    have hgood_card : (1 - 2 * ε) * (X.card : ℝ) ≤ (X_good.card : ℝ) := by
      have hsub_union : badY ∪ badZ ⊆ X :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hcard_sdiff : X_good.card + (badY ∪ badZ).card = X.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_union]
        have := Finset.card_le_card hsub_union
        omega
      have hcard_union : (badY ∪ badZ).card ≤ badY.card + badZ.card := Finset.card_union_le _ _
      have h1 : (X_good.card : ℝ) + ((badY ∪ badZ).card : ℝ) = (X.card : ℝ) := by exact_mod_cast hcard_sdiff
      have h2 : ((badY ∪ badZ).card : ℝ) ≤ (badY.card : ℝ) + (badZ.card : ℝ) := by exact_mod_cast hcard_union
      linarith
    -- For every `x ∈ X_good`, `edgeCount G (N_Y(x)) (N_Z(x)) ≥ (dYZ - ε)(dXY - ε)(dXZ - ε) |Y| |Z|`
    have hgood_pt : ∀ x ∈ X_good,
        (edgeDensity G X Y - ε) * (edgeDensity G Y Z - ε) * (edgeDensity G X Z - ε) *
          (Y.card : ℝ) * (Z.card : ℝ) ≤
        (edgeCount G (Y.filter (G.Adj x)) (Z.filter (G.Adj x)) : ℝ) := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_union] at hx
      have hnxY : ¬ x ∈ badY := fun h => hx.2 (Or.inl h)
      have hnxZ : ¬ x ∈ badZ := fun h => hx.2 (Or.inr h)
      have hdegY : (edgeDensity G X Y - ε) * (Y.card : ℝ) ≤ ((Y.filter (G.Adj x)).card : ℝ) := by
        by_contra hlt; push Not at hlt
        exact hnxY (Finset.mem_filter.mpr ⟨hx.1, hlt⟩)
      have hdegZ : (edgeDensity G X Z - ε) * (Z.card : ℝ) ≤ ((Z.filter (G.Adj x)).card : ℝ) := by
        by_contra hlt; push Not at hlt
        exact hnxZ (Finset.mem_filter.mpr ⟨hx.1, hlt⟩)
      have hY_ge : ε * (Y.card : ℝ) ≤ ((Y.filter (G.Adj x)).card : ℝ) := by nlinarith
      have hZ_ge : ε * (Z.card : ℝ) ≤ ((Z.filter (G.Adj x)).card : ℝ) := by nlinarith
      have hreg := hYZ (Y.filter (G.Adj x)) (Finset.filter_subset _ _)
        (Z.filter (G.Adj x)) (Finset.filter_subset _ _) hY_ge hZ_ge
      have hd_low : edgeDensity G Y Z - ε ≤ edgeDensity G (Y.filter (G.Adj x)) (Z.filter (G.Adj x)) := by
        linarith [(abs_le.mp hreg).1]
      rw [← mul_edgeDensity_eq G (Y.filter (G.Adj x)) (Z.filter (G.Adj x))]
      have hprod_le :
          ((edgeDensity G X Y - ε) * (Y.card : ℝ)) * ((edgeDensity G X Z - ε) * (Z.card : ℝ)) ≤
            ((Y.filter (G.Adj x)).card : ℝ) * ((Z.filter (G.Adj x)).card : ℝ) :=
        mul_le_mul hdegY hdegZ (by nlinarith) (Nat.cast_nonneg _)
      have h1 :
          (((edgeDensity G X Y - ε) * (Y.card : ℝ)) * ((edgeDensity G X Z - ε) * (Z.card : ℝ))) *
              (edgeDensity G Y Z - ε) ≤
            (((Y.filter (G.Adj x)).card : ℝ) * ((Z.filter (G.Adj x)).card : ℝ)) *
              edgeDensity G (Y.filter (G.Adj x)) (Z.filter (G.Adj x)) :=
        mul_le_mul hprod_le hd_low (by linarith) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      linarith
    rw [triCount_eq_sum, Nat.cast_sum]
    calc (1 - 2 * ε) * (edgeDensity G X Y - ε) * (edgeDensity G Y Z - ε) * (edgeDensity G X Z - ε) *
            (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)
        = ((1 - 2 * ε) * (X.card : ℝ)) *
            ((edgeDensity G X Y - ε) * (edgeDensity G Y Z - ε) * (edgeDensity G X Z - ε) *
              (Y.card : ℝ) * (Z.card : ℝ)) := by ring
      _ ≤ (X_good.card : ℝ) *
            ((edgeDensity G X Y - ε) * (edgeDensity G Y Z - ε) * (edgeDensity G X Z - ε) *
              (Y.card : ℝ) * (Z.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hgood_card (by
            have h1 : 0 ≤ edgeDensity G X Y - ε := by linarith
            have h2 : 0 ≤ edgeDensity G Y Z - ε := by linarith
            have h3 : 0 ≤ edgeDensity G X Z - ε := by linarith
            positivity)
      _ = ∑ _x ∈ X_good,
            (edgeDensity G X Y - ε) * (edgeDensity G Y Z - ε) * (edgeDensity G X Z - ε) *
              (Y.card : ℝ) * (Z.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ X_good, (edgeCount G (Y.filter (G.Adj x)) (Z.filter (G.Adj x)) : ℝ) :=
          Finset.sum_le_sum hgood_pt
      _ ≤ ∑ x ∈ X, (edgeCount G (Y.filter (G.Adj x)) (Z.filter (G.Adj x)) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hgood_sub (fun _ _ _ => Nat.cast_nonneg _)

end TriangleCounting

/-! ## Section 3: Triangle Removal Lemma -/

section TriangleRemoval

/-- Total number of ordered triangles `(u, v, w) ∈ V³` in a finite graph `G`. -/
def orderedTriCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  triCount G Finset.univ Finset.univ Finset.univ

lemma twice_card_edgeFinset_eq_edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card = edgeCount G Finset.univ Finset.univ := by
  rw [← G.sum_degrees_eq_twice_card_edges, edgeCount_eq_sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset]

/-- **Triangle Removal Lemma:**
For every `ε > 0`, there exists `δ > 0` such that every finite graph `G` on `n` vertices with
fewer than `δ n³` ordered triangles can be made triangle-free by deleting fewer than `ε n²`
undirected edges (yielding a subgraph `G' ≤ G`). -/
theorem triangle_removal_lemma (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (orderedTriCount G : ℝ) < δ * (Fintype.card V : ℝ) ^ 3 →
        ∃ (G' : SimpleGraph V),
          G' ≤ G ∧
          (∀ u v w : V, ¬ (G'.Adj u v ∧ G'.Adj v w ∧ G'.Adj u w)) ∧
          ((G.edgeFinset \ G'.edgeFinset).card : ℝ) < ε * (Fintype.card V : ℝ) ^ 2 := by
  set ε' : ℝ := min (ε / 6) (1 / 4)
  have hε'_pos : 0 < ε' := lt_min (by linarith) (by norm_num)
  have hε'_le_eps : ε' ≤ ε / 6 := min_le_left _ _
  have hε'_le_qtr : ε' ≤ 1 / 4 := min_le_right _ _
  set m₀ : ℕ := max 4 (⌈6 / ε⌉₊ + 1)
  have hm0_1 : 1 ≤ m₀ := by omega
  rcases szemeredi_regularity_lemma ε' hε'_pos m₀ hm0_1 with ⟨M, hM_ge, hreg⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hm0pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast (by omega : 0 < m₀)
  set δ : ℝ := min (1 / (m₀ : ℝ) ^ 3) ((1 / 2) * ε' ^ 3 * (3 / (4 * (M : ℝ))) ^ 3)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ_pos, ?_⟩
  intro V _ _ G _ htri_lt
  by_cases hsmall : Fintype.card V < m₀
  · -- Small graph `n < m₀`: `< δ n³ < 1` forces `0` triangles, so `G' = G` works!
    have hV_pos : 0 < Fintype.card V := by
      by_contra h0
      have hz : Fintype.card V = 0 := by omega
      simp [hz] at htri_lt
      linarith [Nat.cast_nonneg (α := ℝ) (orderedTriCount G)]
    have hlt1 : (orderedTriCount G : ℝ) < 1 := by
      have hn_lt : (Fintype.card V : ℝ) < (m₀ : ℝ) := by exact_mod_cast hsmall
      have hpow : (Fintype.card V : ℝ) ^ 3 ≤ (m₀ : ℝ) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hn_lt.le 3
      calc (orderedTriCount G : ℝ) < δ * (Fintype.card V : ℝ) ^ 3 := htri_lt
        _ ≤ (1 / (m₀ : ℝ) ^ 3) * (Fintype.card V : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ (1 / (m₀ : ℝ) ^ 3) * (m₀ : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 1 := one_div_mul_cancel (by positivity)
    have htri0 : orderedTriCount G = 0 := by
      have : orderedTriCount G < 1 := by exact_mod_cast hlt1
      omega
    refine ⟨G, le_rfl, ?_, ?_⟩
    · intro u v w ⟨huv, hvw, huw⟩
      have hmem : (u, (v, w)) ∈ ((Finset.univ : Finset V) ×ˢ ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V))).filter
          (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2) := by
        simp [huv, hvw, huw]
      have hpos : 0 < orderedTriCount G := Finset.card_pos.mpr ⟨(u, (v, w)), hmem⟩
      omega
    · have hVposR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV_pos
      calc ((_ : Finset (Sym2 V)).card : ℝ)
          = ((∅ : Finset (Sym2 V)).card : ℝ) := by congr 2; ext e; simp
        _ = 0 := by simp
        _ < ε * (Fintype.card V : ℝ) ^ 2 := by positivity
  · -- Large graph `m₀ ≤ n`: apply Szemerédi Regularity Lemma
    push Not at hsmall
    rcases hreg V G hsmall with
      ⟨k, s, C, V₀, hk_ge, hk_le, hs1, hcards, hdisj, hV0_disj, hunion, hV0_bound, hirreg_bound⟩
    have hV_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
    have htot : k * s + V₀.card = Fintype.card V := by
      have h1 : (Finset.univ.biUnion C).card = k * s := by
        rw [Finset.card_biUnion (fun i _ j _ hne => hdisj i j hne)]
        trans ∑ _i : Fin k, s
        · exact Finset.sum_congr rfl fun i _ => hcards i
        · simp
      rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hV0_disj, h1]
    have hks_le : (k : ℝ) * (s : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast (by omega : k * s ≤ Fintype.card V)
    -- Define cleaned subgraph `G' ≤ G` keeping only edges between distinct `ε'`-regular dense clusters
    let KeepEdge (u v : V) : Prop :=
      G.Adj u v ∧ ∃ i j : Fin k, u ∈ C i ∧ v ∈ C j ∧ i ≠ j ∧
        IsEpsRegular G ε' (C i) (C j) ∧ 2 * ε' ≤ edgeDensity G (C i) (C j)
    let G' : SimpleGraph V :=
      { Adj := KeepEdge
        symm := ⟨by
          rintro u v ⟨huv, i, j, hui, hvj, hij, hreg_ij, hd_ij⟩
          exact ⟨(G.adj_comm _ _).mp huv, j, i, hvj, hui, hij.symm,
            isEpsRegular_comm G hreg_ij, edgeDensity_comm G (C i) (C j) ▸ hd_ij⟩⟩
        loopless := ⟨fun u hu => G.loopless.irrefl u hu.1⟩ }
    have hG'_le : G' ≤ G := fun _ _ h => h.1
    -- 1. Prove `G'` is triangle-free via Triangle Counting Lemma
    have htf : ∀ u v w : V, ¬ (G'.Adj u v ∧ G'.Adj v w ∧ G'.Adj u w) := by
      intro u v w ⟨huv, hvw, huw⟩
      rcases huv with ⟨_, i₁, j₁, hu1, hv1, hij1, hreg1, hd1⟩
      rcases hvw with ⟨_, j₂, l₁, hv2, hw1, hjl1, hreg2, hd2⟩
      rcases huw with ⟨_, i₂, l₂, hu2, hw2, hil2, hreg3, hd3⟩
      -- By disjointness of clusters, `i₂ = i₁`, `j₂ = j₁`, `l₂ = l₁`
      have hi_eq : i₂ = i₁ := by
        by_contra hne; exact Finset.disjoint_left.mp (hdisj i₂ i₁ hne) hu2 hu1
      have hj_eq : j₂ = j₁ := by
        by_contra hne; exact Finset.disjoint_left.mp (hdisj j₂ j₁ hne) hv2 hv1
      have hl_eq : l₂ = l₁ := by
        by_contra hne; exact Finset.disjoint_left.mp (hdisj l₂ l₁ hne) hw2 hw1
      subst i₂; subst j₂; subst l₂
      have hcount := triangle_counting_lemma G hε'_pos (by linarith) (C i₁) (C j₁) (C l₁)
        hreg1 hreg2 hreg3 hd1 hd2 hd3
      have htri_le : triCount G (C i₁) (C j₁) (C l₁) ≤ orderedTriCount G := by
        unfold orderedTriCount triCount
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.product_subset_product
          (Finset.subset_univ _) (Finset.product_subset_product (Finset.subset_univ _) (Finset.subset_univ _))))
      have htri_ge : (1 / 2) * ε' ^ 3 * (s : ℝ) ^ 3 ≤ (orderedTriCount G : ℝ) := by
        have h1 : (1 / 2 : ℝ) ≤ 1 - 2 * ε' := by linarith
        have h2 : ε' ≤ edgeDensity G (C i₁) (C j₁) - ε' := by linarith
        have h3 : ε' ≤ edgeDensity G (C j₁) (C l₁) - ε' := by linarith
        have h4 : ε' ≤ edgeDensity G (C i₁) (C l₁) - ε' := by linarith
        have hprod : (1 / 2) * ε' ^ 3 * (s : ℝ) ^ 3 ≤
            (1 - 2 * ε') * (edgeDensity G (C i₁) (C j₁) - ε') *
              (edgeDensity G (C j₁) (C l₁) - ε') * (edgeDensity G (C i₁) (C l₁) - ε') *
              ((C i₁).card : ℝ) * ((C j₁).card : ℝ) * ((C l₁).card : ℝ) := by
          rw [hcards i₁, hcards j₁, hcards l₁]
          have ha : (1 / 2 : ℝ) * ε' ≤ (1 - 2 * ε') * (edgeDensity G (C i₁) (C j₁) - ε') :=
            mul_le_mul h1 h2 hε'_pos.le (by linarith)
          have hb : ((1 / 2 : ℝ) * ε') * ε' ≤
              ((1 - 2 * ε') * (edgeDensity G (C i₁) (C j₁) - ε')) * (edgeDensity G (C j₁) (C l₁) - ε') :=
            mul_le_mul ha h3 hε'_pos.le (by nlinarith)
          have hc : (((1 / 2 : ℝ) * ε') * ε') * ε' ≤
              (((1 - 2 * ε') * (edgeDensity G (C i₁) (C j₁) - ε')) * (edgeDensity G (C j₁) (C l₁) - ε')) *
                (edgeDensity G (C i₁) (C l₁) - ε') :=
            mul_le_mul hb h4 hε'_pos.le ((by positivity : (0 : ℝ) ≤ ((1 / 2 : ℝ) * ε') * ε').trans hb)
          have hsc : (0 : ℝ) ≤ (s : ℝ) ^ 3 := by positivity
          have hd := mul_le_mul_of_nonneg_right hc hsc
          linarith
        exact hprod.trans (hcount.trans (Nat.cast_le.mpr htri_le))
      have hs_ge : (3 / (4 * (M : ℝ))) * (Fintype.card V : ℝ) ≤ (s : ℝ) := by
        have hks_ge : (3 / 4 : ℝ) * (Fintype.card V : ℝ) ≤ (k : ℝ) * (s : ℝ) := by
          have htotR : (k : ℝ) * (s : ℝ) + (V₀.card : ℝ) = (Fintype.card V : ℝ) := by exact_mod_cast htot
          nlinarith
        have hk_leR : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk_le
        have hMs : (3 / 4 : ℝ) * (Fintype.card V : ℝ) ≤ (M : ℝ) * (s : ℝ) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) s]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (M : ℝ))]
        linarith
      have htri_ge_delta : δ * (Fintype.card V : ℝ) ^ 3 ≤ (orderedTriCount G : ℝ) := by
        have hpow : ((3 / (4 * (M : ℝ))) * (Fintype.card V : ℝ)) ^ 3 ≤ (s : ℝ) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hs_ge 3
        calc δ * (Fintype.card V : ℝ) ^ 3
            ≤ ((1 / 2) * ε' ^ 3 * (3 / (4 * (M : ℝ))) ^ 3) * (Fintype.card V : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = (1 / 2) * ε' ^ 3 * ((3 / (4 * (M : ℝ))) * (Fintype.card V : ℝ)) ^ 3 := by ring
          _ ≤ (1 / 2) * ε' ^ 3 * (s : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ (orderedTriCount G : ℝ) := htri_ge
      linarith
    -- 2. Bound the number of deleted undirected edges `< ε n²`
    let Gdiff : SimpleGraph V :=
      { Adj := fun u v => G.Adj u v ∧ ¬ G'.Adj u v
        symm := ⟨fun _ _ h => ⟨(G.adj_comm _ _).mp h.1, fun h' => h.2 ((G'.adj_comm _ _).mp h')⟩⟩
        loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
    -- Cover all ordered deleted edges by 4 buckets
    let B1 : Finset (V × V) := (V₀ ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ V₀)
    let B2 : Finset (V × V) := Finset.univ.biUnion (fun i : Fin k => C i ×ˢ C i)
    let IrregIdx : Finset (Fin k × Fin k) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ¬ IsEpsRegular G ε' (C p.1) (C p.2))
    let B3 : Finset (V × V) := IrregIdx.biUnion (fun p => C p.1 ×ˢ C p.2)
    let SparseIdx : Finset (Fin k × Fin k) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ edgeDensity G (C p.1) (C p.2) < 2 * ε')
    let B4 : Finset (V × V) :=
      SparseIdx.biUnion (fun p => (C p.1 ×ˢ C p.2).filter (fun e => G.Adj e.1 e.2))
    have hcover : (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => Gdiff.Adj p.1 p.2) ⊆
        B1 ∪ B2 ∪ B3 ∪ B4 := by
      intro ⟨u, v⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Gdiff] at hp
      by_cases hu0 : u ∈ V₀
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hu0, Finset.mem_univ v⟩))))
      · by_cases hv0 : v ∈ V₀
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_univ u, hv0⟩))))
        · have huC : u ∈ Finset.univ.biUnion C := by
            have := Finset.mem_univ u; rw [← hunion, Finset.mem_union] at this
            exact this.resolve_right hu0
          have hvC : v ∈ Finset.univ.biUnion C := by
            have := Finset.mem_univ v; rw [← hunion, Finset.mem_union] at this
            exact this.resolve_right hv0
          rcases Finset.mem_biUnion.mp huC with ⟨i, _, hui⟩
          rcases Finset.mem_biUnion.mp hvC with ⟨j, _, hvj⟩
          by_cases hij : i = j
          · subst hij
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_product.mpr ⟨hui, hvj⟩⟩)))
          · by_cases hreg_ij : IsEpsRegular G ε' (C i) (C j)
            · have hsparse : edgeDensity G (C i) (C j) < 2 * ε' := by
                by_contra hge; push Not at hge
                exact hp.2 ⟨hp.1, i, j, hui, hvj, hij, hreg_ij, hge⟩
              exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hsparse⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hui, hvj⟩, hp.1⟩⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hreg_ij⟩,
                  Finset.mem_product.mpr ⟨hui, hvj⟩⟩))
    have hB1 : (B1.card : ℝ) ≤ 2 * ε' * (Fintype.card V : ℝ) ^ 2 := by
      have h1 : B1.card ≤ V₀.card * Fintype.card V + Fintype.card V * V₀.card := by
        calc B1.card ≤ (V₀ ×ˢ (Finset.univ : Finset V)).card + ((Finset.univ : Finset V) ×ˢ V₀).card :=
              Finset.card_union_le _ _
          _ = V₀.card * Fintype.card V + Fintype.card V * V₀.card := by
              simp [Finset.card_product]
      have h1R : (B1.card : ℝ) ≤ 2 * (V₀.card : ℝ) * (Fintype.card V : ℝ) := by
        have : (B1.card : ℝ) ≤ (V₀.card : ℝ) * (Fintype.card V : ℝ) + (Fintype.card V : ℝ) * (V₀.card : ℝ) := by
          exact_mod_cast h1
        linarith
      nlinarith
    have hB2 : (B2.card : ℝ) ≤ (ε / 6) * (Fintype.card V : ℝ) ^ 2 := by
      have h1 : B2.card ≤ k * (s * s) := by
        calc B2.card ≤ ∑ i : Fin k, (C i ×ˢ C i).card := Finset.card_biUnion_le
          _ = ∑ i : Fin k, (C i).card * (C i).card := by simp [Finset.card_product]
          _ = ∑ _i : Fin k, s * s := Finset.sum_congr rfl fun i _ => by rw [hcards i]
          _ = k * (s * s) := by simp
      have h1R : (B2.card : ℝ) ≤ (k : ℝ) * (s : ℝ) ^ 2 := by
        have : (B2.card : ℝ) ≤ (k : ℝ) * ((s : ℝ) * (s : ℝ)) := by exact_mod_cast h1
        linarith [sq (s : ℝ)]
      have hm0_eps : 6 / ε ≤ (m₀ : ℝ) := by
        have h1 : 6 / ε ≤ (⌈6 / ε⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ⌈6 / ε⌉₊ + 1 ≤ m₀ := le_max_right 4 _
        have h3 : ((⌈6 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (m₀ : ℝ) := Nat.cast_le.mpr h2
        rw [Nat.cast_add, Nat.cast_one] at h3
        linarith
      have hk_geR : 6 / ε ≤ (k : ℝ) := hm0_eps.trans (by exact_mod_cast hk_ge)
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hs_le : (s : ℝ) ≤ (ε / 6) * (Fintype.card V : ℝ) := by
        have hmul : (6 / ε) * (s : ℝ) ≤ (Fintype.card V : ℝ) := by
          calc (6 / ε) * (s : ℝ) ≤ (k : ℝ) * (s : ℝ) := mul_le_mul_of_nonneg_right hk_geR (Nat.cast_nonneg _)
            _ ≤ (Fintype.card V : ℝ) := hks_le
        have := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ ε / 6)
        have hcancel : (ε / 6) * ((6 / ε) * (s : ℝ)) = (s : ℝ) := by field_simp [hε.ne']
        linarith
      calc (B2.card : ℝ) ≤ ((k : ℝ) * (s : ℝ)) * (s : ℝ) := by nlinarith
        _ ≤ (Fintype.card V : ℝ) * ((ε / 6) * (Fintype.card V : ℝ)) :=
            mul_le_mul hks_le hs_le (Nat.cast_nonneg _) hV_pos.le
        _ = (ε / 6) * (Fintype.card V : ℝ) ^ 2 := by ring
    have hB3 : (B3.card : ℝ) ≤ ε' * (Fintype.card V : ℝ) ^ 2 := by
      have h1 : B3.card ≤ IrregIdx.card * (s * s) := by
        calc B3.card ≤ ∑ p ∈ IrregIdx, (C p.1 ×ˢ C p.2).card := Finset.card_biUnion_le
          _ = ∑ p ∈ IrregIdx, (C p.1).card * (C p.2).card := by simp [Finset.card_product]
          _ = ∑ _p ∈ IrregIdx, s * s := Finset.sum_congr rfl fun p _ => by rw [hcards p.1, hcards p.2]
          _ = IrregIdx.card * (s * s) := by simp
      have h1R : (B3.card : ℝ) ≤ (IrregIdx.card : ℝ) * (s : ℝ) ^ 2 := by
        have : (B3.card : ℝ) ≤ (IrregIdx.card : ℝ) * ((s : ℝ) * (s : ℝ)) := by exact_mod_cast h1
        linarith [sq (s : ℝ)]
      calc (B3.card : ℝ) ≤ (ε' * (k : ℝ) ^ 2) * (s : ℝ) ^ 2 :=
            h1R.trans (mul_le_mul_of_nonneg_right hirreg_bound (sq_nonneg _))
        _ = ε' * ((k : ℝ) * (s : ℝ)) ^ 2 := by ring
        _ ≤ ε' * (Fintype.card V : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hks_le 2) hε'_pos.le
    have hB4 : (B4.card : ℝ) ≤ 2 * ε' * (Fintype.card V : ℝ) ^ 2 := by
      have h1 : (B4.card : ℝ) ≤ ∑ p ∈ SparseIdx, (edgeCount G (C p.1) (C p.2) : ℝ) := by
        have hnat : B4.card ≤ ∑ p ∈ SparseIdx, edgeCount G (C p.1) (C p.2) := Finset.card_biUnion_le
        exact_mod_cast hnat
      have h2 : ∑ p ∈ SparseIdx, (edgeCount G (C p.1) (C p.2) : ℝ) ≤
          ∑ _p ∈ SparseIdx, 2 * ε' * (s : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hlt := (Finset.mem_filter.mp hp).2.2
        rw [← mul_edgeDensity_eq G (C p.1) (C p.2), hcards p.1, hcards p.2]
        nlinarith [sq_nonneg (s : ℝ)]
      have h3 : (SparseIdx.card : ℝ) ≤ (k : ℝ) ^ 2 := by
        have hnat : SparseIdx.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hnat
        have : (SparseIdx.card : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hnat
        linarith [sq (k : ℝ)]
      calc (B4.card : ℝ) ≤ (SparseIdx.card : ℝ) * (2 * ε' * (s : ℝ) ^ 2) := by
            have := h1.trans h2; rw [Finset.sum_const, nsmul_eq_mul] at this; exact this
        _ ≤ (k : ℝ) ^ 2 * (2 * ε' * (s : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = 2 * ε' * ((k : ℝ) * (s : ℝ)) ^ 2 := by ring
        _ ≤ 2 * ε' * (Fintype.card V : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hks_le 2) (by positivity)
    have hdel_le : (edgeCount Gdiff Finset.univ Finset.univ : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
      have hcard_cov : edgeCount Gdiff Finset.univ Finset.univ ≤
          B1.card + B2.card + B3.card + B4.card := by
        unfold edgeCount
        calc ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => Gdiff.Adj p.1 p.2)).card
            ≤ (B1 ∪ B2 ∪ B3 ∪ B4).card := Finset.card_le_card hcover
          _ ≤ (B1 ∪ B2 ∪ B3).card + B4.card := Finset.card_union_le _ _
          _ ≤ (B1 ∪ B2).card + B3.card + B4.card := by linarith [Finset.card_union_le (B1 ∪ B2) B3]
          _ ≤ B1.card + B2.card + B3.card + B4.card := by linarith [Finset.card_union_le B1 B2]
      have hcardR : (edgeCount Gdiff Finset.univ Finset.univ : ℝ) ≤
          (B1.card : ℝ) + (B2.card : ℝ) + (B3.card : ℝ) + (B4.card : ℝ) := by exact_mod_cast hcard_cov
      have hsum_eps : 2 * ε' + ε / 6 + ε' + 2 * ε' ≤ ε := by linarith
      nlinarith [sq_nonneg (Fintype.card V : ℝ)]
    refine ⟨G', hG'_le, htf, ?_⟩
    have htwiceR : 2 * (Gdiff.edgeFinset.card : ℝ) =
        (edgeCount Gdiff Finset.univ Finset.univ : ℝ) := by
      exact_mod_cast twice_card_edgeFinset_eq_edgeCount Gdiff
    have hpos : 0 < ε * (Fintype.card V : ℝ) ^ 2 := mul_pos hε (sq_pos_of_pos hV_pos)
    calc ((_ : Finset (Sym2 V)).card : ℝ)
        = (Gdiff.edgeFinset.card : ℝ) := by
          congr 2
          ext e
          induction e using Sym2.ind with
          | _ u v =>
            simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Gdiff]
      _ < ε * (Fintype.card V : ℝ) ^ 2 := by linarith

end TriangleRemoval

/-! ## Section 4: Ruzsa–Szemerédi `(6, 3)` / Unique-Triangle & Induced-Matching Theorems -/

section RuzsaSzemeredi

/-- **Ruzsa–Szemerédi Unique-Triangle Theorem (`(6, 3)`-style):**
For every `ε > 0`, there exists `N₀` such that any graph `G` on `n ≥ N₀` vertices in which
every edge belongs to a unique triangle has fewer than `ε n²` edges. -/
theorem ruzsa_szemeredi_unique_triangle (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N₀ ≤ Fintype.card V →
      (∀ u v : V, G.Adj u v → ∃! w : V, G.Adj u w ∧ G.Adj v w) →
      (G.edgeFinset.card : ℝ) < ε * (Fintype.card V : ℝ) ^ 2 := by
  rcases triangle_removal_lemma (ε / 3) (by linarith) with ⟨δ, hδ_pos, hrem⟩
  refine ⟨max 1 (⌈1 / δ⌉₊ + 1), ?_⟩
  intro V _ _ G _ hN0 huniq
  have hV_pos : 0 < Fintype.card V := by omega
  have hV_posR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV_pos
  -- Step 1: Every ordered edge `(u, v)` determines a unique triangle `(u, v, w)`, so `orderedTriCount G ≤ n²`
  have htri_le_nsq : orderedTriCount G ≤ (Fintype.card V) ^ 2 := by
    unfold orderedTriCount triCount
    have hinj : Set.InjOn (fun t : V × V × V => (t.1, t.2.1))
        (((Finset.univ : Finset V) ×ˢ ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V))).filter
          (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2) : Set (V × V × V)) := by
      intro t1 ht1 t2 ht2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at ht1 ht2
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      have h3 : t1.2.2 = t2.2.2 := by
        rcases huniq t1.1 t1.2.1 ht1.1 with ⟨w, _, hw_uniq⟩
        have hw1 : t1.2.2 = w := hw_uniq t1.2.2 ⟨ht1.2.2, ht1.2.1⟩
        have hw2 : t2.2.2 = w := hw_uniq t2.2.2 ⟨h1 ▸ ht2.2.2, h2 ▸ ht2.2.1⟩
        exact hw1.trans hw2.symm
      exact Prod.ext h1 (Prod.ext h2 h3)
    calc _ = ((((Finset.univ : Finset V) ×ˢ ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V))).filter
            (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2)).image
              (fun t => (t.1, t.2.1))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = (Fintype.card V) ^ 2 := by simp [sq]
  have htri_lt : (orderedTriCount G : ℝ) < δ * (Fintype.card V : ℝ) ^ 3 := by
    have hN_big : 1 / δ < (Fintype.card V : ℝ) := by
      have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ⌈1 / δ⌉₊ + 1 ≤ Fintype.card V := (le_max_right 1 _).trans hN0
      have h3 : ((⌈1 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr h2
      rw [Nat.cast_add, Nat.cast_one] at h3
      linarith
    have h1lt : (1 : ℝ) < δ * (Fintype.card V : ℝ) := by
      have := mul_lt_mul_of_pos_left hN_big hδ_pos
      rwa [mul_one_div_cancel hδ_pos.ne'] at this
    calc (orderedTriCount G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by exact_mod_cast htri_le_nsq
      _ = 1 * (Fintype.card V : ℝ) ^ 2 := (one_mul _).symm
      _ < (δ * (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right h1lt (sq_pos_of_pos hV_posR)
      _ = δ * (Fintype.card V : ℝ) ^ 3 := by ring
  -- Step 2: Apply Triangle Removal Lemma with `ε / 3`
  rcases hrem V G htri_lt with ⟨G', hG'_le, htf, hdel_lt⟩
  -- Step 3: Double-count `|E(G)| ≤ 3 * |E(G) \ E(G')|` because triangles are pairwise edge-disjoint!
  let D : Finset (Sym2 V) := G.edgeFinset \ G'.edgeFinset
  let ordEdges : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)
  have hord_card : ordEdges.card = 2 * G.edgeFinset.card :=
    (twice_card_edgeFinset_eq_edgeCount G).symm
  -- For each ordered edge `p = (u, v)`, pick its unique third vertex `w(p)`
  let thirdV : V × V → V := fun p =>
    if h : G.Adj p.1 p.2 then Classical.choose (huniq p.1 p.2 h) else p.1
  have hthird_spec : ∀ p ∈ ordEdges,
      G.Adj p.1 (thirdV p) ∧ G.Adj p.2 (thirdV p) ∧
      ∀ w : V, G.Adj p.1 w ∧ G.Adj p.2 w → w = thirdV p := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hsp := Classical.choose_spec (huniq p.1 p.2 hadj)
    simp only [thirdV, dif_pos hadj]
    exact ⟨hsp.1.1, hsp.1.2, hsp.2⟩
  -- For every `p ∈ ordEdges`, at least one of the 3 edges of its unique triangle is in `D`
  let triEdges (p : V × V) : Finset (Sym2 V) := {s(p.1, p.2), s(p.1, thirdV p), s(p.2, thirdV p)}
  have hhit : ∀ p ∈ ordEdges, ∃ e ∈ D, e ∈ triEdges p := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    rcases hthird_spec p hp with ⟨h1w, h2w, _⟩
    by_contra hnone
    push Not at hnone
    have h1 : G'.Adj p.1 p.2 := by
      by_contra hnot
      exact hnone s(p.1, p.2) (Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr hadj, fun h => hnot (SimpleGraph.mem_edgeFinset.mp h)⟩)
        (by simp [triEdges])
    have h2 : G'.Adj p.1 (thirdV p) := by
      by_contra hnot
      exact hnone s(p.1, thirdV p) (Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr h1w, fun h => hnot (SimpleGraph.mem_edgeFinset.mp h)⟩)
        (by simp [triEdges])
    have h3 : G'.Adj p.2 (thirdV p) := by
      by_contra hnot
      exact hnone s(p.2, thirdV p) (Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr h2w, fun h => hnot (SimpleGraph.mem_edgeFinset.mp h)⟩)
        (by simp [triEdges])
    exact htf p.1 p.2 (thirdV p) ⟨h1, h3, h2⟩
  -- Each `e ∈ D` appears in `triEdges p` for at most `6` ordered edges `p ∈ ordEdges`
  have hfiber_le : ∀ e ∈ D, (ordEdges.filter (fun p => e ∈ triEdges p)).card ≤ 6 := by
    intro e he
    have heG : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := SimpleGraph.mem_edgeFinset.mp heG
      rcases huniq a b hab with ⟨c, ⟨hac, hbc⟩, hc_uniq⟩
      -- Any `p ∈ ordEdges` with `s(a, b) ∈ triEdges p` must have `{p.1, p.2} ⊆ {a, b, c}` and `p.1 ≠ p.2`
      let S6 : Finset (V × V) := {(a, b), (b, a), (a, c), (c, a), (b, c), (c, b)}
      have hsub : ordEdges.filter (fun p => s(a, b) ∈ triEdges p) ⊆ S6 := by
        intro ⟨u, v⟩ hp
        rw [Finset.mem_filter] at hp
        have huv : G.Adj u v := (Finset.mem_filter.mp hp.1).2
        rcases hthird_spec (u, v) hp.1 with ⟨huw, hvw, _⟩
        set w := thirdV (u, v)
        simp only [triEdges, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp.2 with h1 | h2 | h3
        · rcases Sym2.eq_iff.mp h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [S6]
        · rcases Sym2.eq_iff.mp h2 with ⟨hau, hbw⟩ | ⟨haw, hbu⟩
          · have hvc : v = c := hc_uniq v ⟨by rw [hau]; exact huv, by rw [hbw]; exact (G.adj_comm _ _).mp hvw⟩
            rw [← hau, hvc]; simp [S6]
          · have hvc : v = c := hc_uniq v ⟨by rw [haw]; exact (G.adj_comm _ _).mp hvw, by rw [hbu]; exact huv⟩
            rw [← hbu, hvc]; simp [S6]
        · rcases Sym2.eq_iff.mp h3 with ⟨hav, hbw⟩ | ⟨haw, hbv⟩
          · have huc : u = c := hc_uniq u ⟨by rw [hav]; exact (G.adj_comm _ _).mp huv, by rw [hbw]; exact (G.adj_comm _ _).mp huw⟩
            rw [← hav, huc]; simp [S6]
          · have huc : u = c := hc_uniq u ⟨by rw [haw]; exact (G.adj_comm _ _).mp huw, by rw [hbv]; exact (G.adj_comm _ _).mp huv⟩
            rw [← hbv, huc]; simp [S6]
      have hS6_le : S6.card ≤ 6 := by
        dsimp only [S6]
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
            ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
              ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
                ((Finset.card_insert_le _ _).trans (by simp)) 1)) 1)) 1)) 1)
      exact (Finset.card_le_card hsub).trans hS6_le
  -- Double count pairs `(p, e) ∈ ordEdges × D` with `e ∈ triEdges p`
  have hdouble : ordEdges.card ≤ 6 * D.card := by
    have hcov : ordEdges ⊆ D.biUnion (fun e => ordEdges.filter (fun p => e ∈ triEdges p)) := by
      intro p hp
      rcases hhit p hp with ⟨e, heD, het⟩
      exact Finset.mem_biUnion.mpr ⟨e, heD, Finset.mem_filter.mpr ⟨hp, het⟩⟩
    calc ordEdges.card
        ≤ (D.biUnion (fun e => ordEdges.filter (fun p => e ∈ triEdges p))).card :=
          Finset.card_le_card hcov
      _ ≤ ∑ e ∈ D, (ordEdges.filter (fun p => e ∈ triEdges p)).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ D, 6 := Finset.sum_le_sum hfiber_le
      _ = 6 * D.card := by simp [mul_comm]
  have hE_le : G.edgeFinset.card ≤ 3 * D.card := by omega
  have hE_leR : (G.edgeFinset.card : ℝ) ≤ 3 * (D.card : ℝ) := by exact_mod_cast hE_le
  linarith

/-- An **induced matching** in `G` is a set `M ⊆ G.edgeFinset` of pairwise vertex-disjoint edges
such that no edge of `G` connects endpoints of two distinct edges in `M`. -/
def IsInducedMatching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) ∧
  (∀ u v : V, (∃ e₁ ∈ M, u ∈ e₁) → (∃ e₂ ∈ M, v ∈ e₂) → G.Adj u v → s(u, v) ∈ M)

/-- **Ruzsa–Szemerédi Induced-Matching Theorem:**
For every `ε > 0`, there exists `N₀` such that any graph `G` on `n ≥ N₀` vertices whose edge set
is covered by `t ≤ n` induced matchings has fewer than `ε n²` edges. -/
theorem ruzsa_szemeredi_induced_matching (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N₀ ≤ Fintype.card V →
      ∀ (t : ℕ), t ≤ Fintype.card V →
      (∃ M : Fin t → Finset (Sym2 V),
        (∀ i : Fin t, IsInducedMatching G (M i)) ∧
        G.edgeFinset ⊆ Finset.univ.biUnion M) →
      (G.edgeFinset.card : ℝ) < ε * (Fintype.card V : ℝ) ^ 2 := by
  rcases ruzsa_szemeredi_unique_triangle (ε / 9) (by linarith) with ⟨N₀, hRS⟩
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ hN0 t ht ⟨M, hM_ind, hM_cov⟩
  -- Shrink `M` to pairwise edge-disjoint induced matchings `M'` still covering `G.edgeFinset`
  let M' : Fin t → Finset (Sym2 V) := fun i => (M i).filter (fun e => ∀ j : Fin t, j < i → e ∉ M j)
  have hM'_sub : ∀ i : Fin t, M' i ⊆ M i := fun i => Finset.filter_subset _ _
  have hM'_ind : ∀ i : Fin t, IsInducedMatching G (M' i) := by
    intro i
    refine ⟨(hM'_sub i).trans (hM_ind i).1,
      fun e₁ he₁ e₂ he₂ hne v hv1 => (hM_ind i).2.1 e₁ (hM'_sub i he₁) e₂ (hM'_sub i he₂) hne v hv1, ?_⟩
    intro u v ⟨e₁, he₁, hu1⟩ ⟨e₂, he₂, hv2⟩ huv
    have hmemM : s(u, v) ∈ M i :=
      (hM_ind i).2.2 u v ⟨e₁, hM'_sub i he₁, hu1⟩ ⟨e₂, hM'_sub i he₂, hv2⟩ huv
    have heq : s(u, v) = e₁ := by
      by_contra hne
      exact (hM_ind i).2.1 s(u, v) hmemM e₁ (hM'_sub i he₁) hne u (by simp) hu1
    exact heq ▸ he₁
  have hM'_disj : ∀ i j : Fin t, i ≠ j → ∀ e : Sym2 V, e ∈ M' i → e ∉ M' j := by
    intro i j hij e hei hej
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (Finset.mem_filter.mp hej).2 i hlt (hM'_sub i hei)
    · exact (Finset.mem_filter.mp hei).2 j hgt (hM'_sub j hej)
  have hM'_cov : ∀ e ∈ G.edgeFinset, ∃! i : Fin t, e ∈ M' i := by
    intro e he
    have hex : ∃ n : ℕ, ∃ h : n < t, e ∈ M ⟨n, h⟩ := by
      rcases Finset.mem_biUnion.mp (hM_cov he) with ⟨i, _, hi⟩
      exact ⟨i.val, i.isLt, hi⟩
    let n₀ := Nat.find hex
    have hn₀_spec := Nat.find_spec hex
    rcases hn₀_spec with ⟨hn₀_lt, hn₀_mem⟩
    refine ⟨⟨n₀, hn₀_lt⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hn₀_mem, fun j hj => ?_⟩
      intro hmemj
      exact Nat.find_min hex hj ⟨j.isLt, hmemj⟩
    · intro j hj
      by_contra hne
      exact hM'_disj j ⟨n₀, hn₀_lt⟩ hne e hj
        (Finset.mem_filter.mpr ⟨hn₀_mem, fun k hk hmemk => Nat.find_min hex hk ⟨k.isLt, hmemk⟩⟩)
  -- Build tripartite double cover `H` on `W := V ⊕ (V ⊕ Fin t)` (`|W| = 2n + t ≤ 3n`)
  let W := V ⊕ (V ⊕ Fin t)
  let adjH : W → W → Prop := fun a b =>
    match a, b with
    | Sum.inl u, Sum.inr (Sum.inl v) => G.Adj u v
    | Sum.inr (Sum.inl v), Sum.inl u => G.Adj u v
    | Sum.inl u, Sum.inr (Sum.inr i) => ∃ v : V, s(u, v) ∈ M' i
    | Sum.inr (Sum.inr i), Sum.inl u => ∃ v : V, s(u, v) ∈ M' i
    | Sum.inr (Sum.inl v), Sum.inr (Sum.inr i) => ∃ u : V, s(u, v) ∈ M' i
    | Sum.inr (Sum.inr i), Sum.inr (Sum.inl v) => ∃ u : V, s(u, v) ∈ M' i
    | _, _ => False
  let H : SimpleGraph W :=
    { Adj := adjH
      symm := ⟨by
        rintro (u | (v | i)) (u' | (v' | i')) h <;> exact h⟩
      loopless := ⟨by
        rintro (u | (v | i)) h <;> exact h⟩ }
  -- Verify every edge of `H` belongs to a unique triangle in `H`
  have hH_uniq : ∀ a b : W, H.Adj a b → ∃! c : W, H.Adj a c ∧ H.Adj b c := by
    rintro (u | (v | i)) (u' | (v' | i')) hab
    · exact False.elim hab
    · -- Edge `(inl u, inr (inl v'))` (`G.Adj u v'`): unique partner is `inr (inr i)` where `s(u, v') ∈ M' i`
      have heG : s(u, v') ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab
      rcases hM'_cov s(u, v') heG with ⟨i, hi, hi_uniq⟩
      refine ⟨Sum.inr (Sum.inr i), ⟨⟨v', hi⟩, ⟨u, hi⟩⟩, ?_⟩
      rintro (w | (w | j)) ⟨h1, h2⟩
      · exact False.elim h1
      · exact False.elim h2
      · rcases h1 with ⟨v1, hv1⟩
        rcases h2 with ⟨u1, hu1⟩
        have hmem : s(u, v') ∈ M' j :=
          (hM'_ind j).2.2 u v' ⟨s(u, v1), hv1, by simp⟩ ⟨s(u1, v'), hu1, by simp⟩ hab
        rw [hi_uniq j hmem]
    · -- Edge `(inl u, inr (inr i'))`: unique partner is `inr (inl v)` where `s(u, v) ∈ M' i'`
      rcases hab with ⟨v, hv⟩
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp ((hM'_ind i').1 hv)
      refine ⟨Sum.inr (Sum.inl v), ⟨huv, ⟨u, hv⟩⟩, ?_⟩
      rintro (w | (w | j)) ⟨h1, h2⟩
      · exact False.elim h1
      · rcases h2 with ⟨u1, hu1⟩
        have hmem : s(u, w) ∈ M' i' :=
          (hM'_ind i').2.2 u w ⟨s(u, v), hv, by simp⟩ ⟨s(u1, w), hu1, by simp⟩ h1
        have heq : s(u, w) = s(u, v) := by
          by_contra hne
          exact (hM'_ind i').2.1 s(u, w) hmem s(u, v) hv hne u (by simp) (by simp)
        rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨huv_eq, _⟩
        · rfl
        · rw [huv_eq] at huv; exact absurd huv (G.loopless.irrefl v)
      · exact False.elim h2
    · -- Edge `(inr (inl v), inl u')` (`G.Adj u' v`): symmetric to case 2
      have heG : s(u', v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab
      rcases hM'_cov s(u', v) heG with ⟨i, hi, hi_uniq⟩
      refine ⟨Sum.inr (Sum.inr i), ⟨⟨u', hi⟩, ⟨v, hi⟩⟩, ?_⟩
      rintro (w | (w | j)) ⟨h1, h2⟩
      · exact False.elim h2
      · exact False.elim h1
      · rcases h1 with ⟨u1, hu1⟩
        rcases h2 with ⟨v1, hv1⟩
        have hmem : s(u', v) ∈ M' j :=
          (hM'_ind j).2.2 u' v ⟨s(u', v1), hv1, by simp⟩ ⟨s(u1, v), hu1, by simp⟩ hab
        rw [hi_uniq j hmem]
    · exact False.elim hab
    · -- Edge `(inr (inl v), inr (inr i'))`: unique partner is `inl u` where `s(u, v) ∈ M' i'`
      rcases hab with ⟨u, hu⟩
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp ((hM'_ind i').1 hu)
      refine ⟨Sum.inl u, ⟨huv, ⟨v, hu⟩⟩, ?_⟩
      rintro (w | (w | j)) ⟨h1, h2⟩
      · rcases h2 with ⟨v1, hv1⟩
        have hmem : s(w, v) ∈ M' i' :=
          (hM'_ind i').2.2 w v ⟨s(w, v1), hv1, by simp⟩ ⟨s(u, v), hu, by simp⟩ h1
        have heq : s(w, v) = s(u, v) := by
          by_contra hne
          exact (hM'_ind i').2.1 s(w, v) hmem s(u, v) hu hne v (by simp) (by simp)
        rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨_, hvu⟩
        · rfl
        · rw [hvu] at huv; exact absurd huv (G.loopless.irrefl u)
      · exact False.elim h1
      · exact False.elim h2
    · -- Edge `(inr (inr i), inl u')`
      rcases hab with ⟨v, hv⟩
      have huv : G.Adj u' v := SimpleGraph.mem_edgeFinset.mp ((hM'_ind i).1 hv)
      refine ⟨Sum.inr (Sum.inl v), ⟨⟨u', hv⟩, huv⟩, ?_⟩
      rintro (w | (w | j)) ⟨h1, h2⟩
      · exact False.elim h2
      · rcases h1 with ⟨u1, hu1⟩
        have hmem : s(u', w) ∈ M' i :=
          (hM'_ind i).2.2 u' w ⟨s(u', v), hv, by simp⟩ ⟨s(u1, w), hu1, by simp⟩ h2
        have heq : s(u', w) = s(u', v) := by
          by_contra hne
          exact (hM'_ind i).2.1 s(u', w) hmem s(u', v) hv hne u' (by simp) (by simp)
        rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨huv_eq, _⟩
        · rfl
        · rw [huv_eq] at huv; exact absurd huv (G.loopless.irrefl v)
      · exact False.elim h1
    · -- Edge `(inr (inr i), inr (inl v'))`
      rcases hab with ⟨u, hu⟩
      have huv : G.Adj u v' := SimpleGraph.mem_edgeFinset.mp ((hM'_ind i).1 hu)
      refine ⟨Sum.inl u, ⟨⟨v', hu⟩, huv⟩, ?_⟩
      rintro (w | (w | j)) ⟨h1, h2⟩
      · rcases h1 with ⟨v1, hv1⟩
        have hmem : s(w, v') ∈ M' i :=
          (hM'_ind i).2.2 w v' ⟨s(w, v1), hv1, by simp⟩ ⟨s(u, v'), hu, by simp⟩ h2
        have heq : s(w, v') = s(u, v') := by
          by_contra hne
          exact (hM'_ind i).2.1 s(w, v') hmem s(u, v') hu hne v' (by simp) (by simp)
        rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨_, hvu⟩
        · rfl
        · rw [hvu] at huv; exact absurd huv (G.loopless.irrefl u)
      · exact False.elim h2
      · exact False.elim h1
    · exact False.elim hab
  -- Apply `ruzsa_szemeredi_unique_triangle (ε / 9)` to `H`
  have hW_card : Fintype.card W = Fintype.card V + (Fintype.card V + t) := by
    simp [W]
  have hW_ge : N₀ ≤ Fintype.card W := by omega
  have hW_le : (Fintype.card W : ℝ) ≤ 3 * (Fintype.card V : ℝ) := by
    have : Fintype.card W ≤ 3 * Fintype.card V := by omega
    exact_mod_cast this
  have hH_lt := hRS W H hW_ge hH_uniq
  -- Inject `G.edgeFinset` (or ordered edges of `G`) into `H.edgeFinset`
  have hE_le_H : G.edgeFinset.card ≤ H.edgeFinset.card := by
    have hord_le : edgeCount G Finset.univ Finset.univ ≤ H.edgeFinset.card := by
      unfold edgeCount
      let f : V × V → Sym2 W := fun p => s(Sum.inl p.1, Sum.inr (Sum.inl p.2))
      have hmaps : ∀ p ∈ ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V)).filter
          (fun p => G.Adj p.1 p.2), f p ∈ H.edgeFinset := by
        intro p hp
        rw [SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_filter.mp hp).2
      have hinj : Set.InjOn f
          ((((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V)).filter
            (fun p => G.Adj p.1 p.2)) : Set (V × V)) := by
        intro p1 _ p2 _ h
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact Prod.ext (Sum.inl.inj h1) (Sum.inl.inj (Sum.inr.inj h2))
        · cases h1
      calc _ = ((((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V)).filter
              (fun p => G.Adj p.1 p.2)).image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ H.edgeFinset.card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
    rw [← twice_card_edgeFinset_eq_edgeCount G] at hord_le
    omega
  calc (G.edgeFinset.card : ℝ) ≤ (H.edgeFinset.card : ℝ) := by exact_mod_cast hE_le_H
    _ < (ε / 9) * (Fintype.card W : ℝ) ^ 2 := hH_lt
    _ ≤ (ε / 9) * (3 * (Fintype.card V : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hW_le 2
    _ = ε * (Fintype.card V : ℝ) ^ 2 := by ring

end RuzsaSzemeredi

/-! ## Section 5: Roth's 3-AP Theorem & 2D Corners Theorem via Triangle Removal -/

section RothAndCorners

/-- **Roth's Theorem on 3-Term Arithmetic Progressions (via Szemerédi Regularity / Triangle Removal):**
For every `δ > 0`, there exists `N₀ : ℕ` such that for every `N ≥ N₀` and every subset
`A ⊆ Finset.range N` with `|A| ≥ δ N`, `A` contains a nontrivial 3-term arithmetic progression
`a, a + d, a + 2d ∈ A` (`0 < d`). -/
theorem roth_three_ap_via_removal (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  rcases ruzsa_szemeredi_unique_triangle (δ / 9) (by linarith) with ⟨M₀, hRS⟩
  refine ⟨max 1 M₀, ?_⟩
  intro N hN A hA_sub hA_card
  by_contra hno3ap
  push Not at hno3ap
  -- Build the Ruzsa–Szemerédi tripartite graph `G` on `V = Fin 3 × ZMod (2 * N + 1)`
  let m : ℕ := 2 * N + 1
  have : NeZero m := ⟨by omega⟩
  have hA_lt : ∀ a ∈ A, a < N := fun a ha => Finset.mem_range.mp (hA_sub ha)
  -- Helper: injectivity of `a ↦ (a : ZMod m)` on `Finset.range m`, and `2 * a = 2 * b` in `ZMod m`
  have hcast_eq : ∀ u v : ℕ, u < m → v < m → (u : ZMod m) = (v : ZMod m) → u = v := by
    intro u v hu hv h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] at hval
    exact hval
  have h2mul_eq : ∀ a b : ℕ, a < N → b < N → (2 : ZMod m) * (a : ZMod m) = (2 : ZMod m) * (b : ZMod m) → a = b := by
    intro a b ha hb h
    have h1 : ((2 * a : ℕ) : ZMod m) = ((2 * b : ℕ) : ZMod m) := by push_cast; exact h
    have h2 : 2 * a = 2 * b := hcast_eq (2 * a) (2 * b) (by omega) (by omega) h1
    omega
  -- `a + b = 2 * c` in `ZMod m` for `a, b, c ∈ A` forces `a = b = c` (since `A` is 3-AP-free!)
  have h3ap_triv : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) → a = c ∧ b = c := by
    intro a ha b hb c hc heq
    have haN := hA_lt a ha
    have hbN := hA_lt b hb
    have hcN := hA_lt c hc
    have hnat : a + b = 2 * c :=
      hcast_eq (a + b) (2 * c) (by omega) (by omega) (by push_cast; exact heq)
    by_cases hab : a = b
    · omega
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · exfalso
        have hd : 0 < c - a := by omega
        have h1 : a + (c - a) = c := by omega
        have h2 : a + 2 * (c - a) = b := by omega
        exact hno3ap a (c - a) hd ha (by rwa [h1]) (by rwa [h2])
      · exfalso
        have hd : 0 < c - b := by omega
        have h1 : b + (c - b) = c := by omega
        have h2 : b + 2 * (c - b) = a := by omega
        exact hno3ap b (c - b) hd hb (by rwa [h1]) (by rwa [h2])
  let V := Fin 3 × ZMod m
  let adjG : V → V → Prop := fun p q =>
    match p.1, q.1 with
    | ⟨0, _⟩, ⟨1, _⟩ => ∃ a ∈ A, q.2 - p.2 = (a : ZMod m)
    | ⟨1, _⟩, ⟨0, _⟩ => ∃ a ∈ A, p.2 - q.2 = (a : ZMod m)
    | ⟨1, _⟩, ⟨2, _⟩ => ∃ b ∈ A, q.2 - p.2 = (b : ZMod m)
    | ⟨2, _⟩, ⟨1, _⟩ => ∃ b ∈ A, p.2 - q.2 = (b : ZMod m)
    | ⟨0, _⟩, ⟨2, _⟩ => ∃ c ∈ A, q.2 - p.2 = (2 : ZMod m) * (c : ZMod m)
    | ⟨2, _⟩, ⟨0, _⟩ => ∃ c ∈ A, p.2 - q.2 = (2 : ZMod m) * (c : ZMod m)
    | _, _ => False
  let G : SimpleGraph V :=
    { Adj := adjG
      symm := ⟨by
        rintro ⟨i, x⟩ ⟨j, y⟩ h
        fin_cases i <;> fin_cases j <;> exact h⟩
      loopless := ⟨by
        rintro ⟨i, x⟩ h
        fin_cases i <;> exact h⟩ }
  -- Every edge of `G` belongs to a unique triangle in `G`!
  have hG_uniq : ∀ p q : V, G.Adj p q → ∃! r : V, G.Adj p r ∧ G.Adj q r := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hpq
    fin_cases i <;> fin_cases j
    · exact False.elim hpq
    · -- `(0, x) ~ (1, y)` with `y - x = a`: unique partner `(2, x + 2a)`
      rcases hpq with ⟨a, ha, hxy⟩
      refine ⟨(2, x + 2 * (a : ZMod m)), ⟨⟨a, ha, by ring⟩, ⟨a, ha, by linear_combination -hxy⟩⟩, ?_⟩
      rintro ⟨k, z⟩ ⟨hpr, hqr⟩
      fin_cases k
      · exact False.elim hpr
      · exact False.elim hqr
      · rcases hpr with ⟨c, hc, hxz⟩
        rcases hqr with ⟨b, hb, hyz⟩
        have hsum : (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) := by
          linear_combination -hxy - hyz + hxz
        rcases h3ap_triv a ha b hb c hc hsum with ⟨rfl, _⟩
        ext
        · rfl
        · linear_combination hxz
    · -- `(0, x) ~ (2, y)` with `y - x = 2c`: unique partner `(1, x + c)`
      rcases hpq with ⟨c, hc, hxy⟩
      refine ⟨(1, x + (c : ZMod m)), ⟨⟨c, hc, by ring⟩, ⟨c, hc, by linear_combination hxy⟩⟩, ?_⟩
      rintro ⟨k, z⟩ ⟨hpr, hqr⟩
      fin_cases k
      · exact False.elim hpr
      · rcases hpr with ⟨a, ha, hxz⟩
        rcases hqr with ⟨b, hb, hzy⟩
        have hsum : (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) := by
          linear_combination -hxz - hzy + hxy
        rcases h3ap_triv a ha b hb c hc hsum with ⟨rfl, _⟩
        ext
        · rfl
        · linear_combination hxz
      · exact False.elim hqr
    · -- `(1, x) ~ (0, y)` with `x - y = a`: unique partner `(2, y + 2a)`
      rcases hpq with ⟨a, ha, hxy⟩
      refine ⟨(2, y + 2 * (a : ZMod m)), ⟨⟨a, ha, by linear_combination -hxy⟩, ⟨a, ha, by ring⟩⟩, ?_⟩
      rintro ⟨k, z⟩ ⟨hpr, hqr⟩
      fin_cases k
      · exact False.elim hqr
      · exact False.elim hpr
      · rcases hpr with ⟨b, hb, hxz⟩
        rcases hqr with ⟨c, hc, hyz⟩
        have hsum : (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) := by
          linear_combination -hxy - hxz + hyz
        rcases h3ap_triv a ha b hb c hc hsum with ⟨rfl, _⟩
        ext
        · rfl
        · linear_combination hyz
    · exact False.elim hpq
    · -- `(1, x) ~ (2, y)` with `y - x = b`: unique partner `(0, x - b)`
      rcases hpq with ⟨b, hb, hxy⟩
      refine ⟨(0, x - (b : ZMod m)), ⟨⟨b, hb, by ring⟩, ⟨b, hb, by linear_combination hxy⟩⟩, ?_⟩
      rintro ⟨k, z⟩ ⟨hpr, hqr⟩
      fin_cases k
      · rcases hpr with ⟨a, ha, hzx⟩
        rcases hqr with ⟨c, hc, hzy⟩
        have hsum : (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) := by
          linear_combination -hzx - hxy + hzy
        rcases h3ap_triv a ha b hb c hc hsum with ⟨rfl, rfl⟩
        ext
        · rfl
        · linear_combination -hzx
      · exact False.elim hpr
      · exact False.elim hqr
    · -- `(2, x) ~ (0, y)` with `x - y = 2c`: unique partner `(1, y + c)`
      rcases hpq with ⟨c, hc, hxy⟩
      refine ⟨(1, y + (c : ZMod m)), ⟨⟨c, hc, by linear_combination hxy⟩, ⟨c, hc, by ring⟩⟩, ?_⟩
      rintro ⟨k, z⟩ ⟨hpr, hqr⟩
      fin_cases k
      · exact False.elim hqr
      · rcases hpr with ⟨b, hb, hzx⟩
        rcases hqr with ⟨a, ha, hyz⟩
        have hsum : (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) := by
          linear_combination -hyz - hzx + hxy
        rcases h3ap_triv a ha b hb c hc hsum with ⟨rfl, _⟩
        ext
        · rfl
        · linear_combination hyz
      · exact False.elim hpr
    · -- `(2, x) ~ (1, y)` with `x - y = b`: unique partner `(0, y - b)`
      rcases hpq with ⟨b, hb, hxy⟩
      refine ⟨(0, y - (b : ZMod m)), ⟨⟨b, hb, by linear_combination hxy⟩, ⟨b, hb, by ring⟩⟩, ?_⟩
      rintro ⟨k, z⟩ ⟨hpr, hqr⟩
      fin_cases k
      · rcases hpr with ⟨c, hc, hzx⟩
        rcases hqr with ⟨a, ha, hzy⟩
        have hsum : (a : ZMod m) + (b : ZMod m) = (2 : ZMod m) * (c : ZMod m) := by
          linear_combination -hzy - hxy + hzx
        rcases h3ap_triv a ha b hb c hc hsum with ⟨rfl, rfl⟩
        ext
        · rfl
        · linear_combination -hzy
      · exact False.elim hqr
      · exact False.elim hpr
    · exact False.elim hpq
  -- Lower bound `|E(G)| ≥ 3 * m * |A|` (in fact `m * |A|` from layer `(0, 1)` alone gives `≥ (δ/9) |V|²`? Check!)
  -- Wait: `|V| = 3 m`, `(δ/9) |V|² = δ m²`, and `3 * m * |A| ≥ 3 * m * δ * N ≥ δ * m²` (since `3 N ≥ 2 N + 1 = m` for `N ≥ 1`)!
  -- So we count ALL 3 layers `(0, 1)`, `(1, 2)`, `(0, 2)` to get `3 * m * |A| ≤ |E(G)|`!
  let L01 : Finset (Sym2 V) := (Finset.univ ×ˢ A).image (fun p : ZMod m × ℕ => s(((0 : Fin 3), p.1), ((1 : Fin 3), p.1 + (p.2 : ZMod m))))
  let L12 : Finset (Sym2 V) := (Finset.univ ×ˢ A).image (fun p : ZMod m × ℕ => s(((1 : Fin 3), p.1), ((2 : Fin 3), p.1 + (p.2 : ZMod m))))
  let L02 : Finset (Sym2 V) := (Finset.univ ×ˢ A).image (fun p : ZMod m × ℕ => s(((0 : Fin 3), p.1), ((2 : Fin 3), p.1 + (2 : ZMod m) * (p.2 : ZMod m))))
  have hL01_card : L01.card = m * A.card := by
    rw [Finset.card_image_of_injOn]
    · simp [ZMod.card]
    · intro p1 hp1 p2 hp2 h
      rw [Finset.mem_coe, Finset.mem_product] at hp1 hp2
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · have hx : p1.1 = p2.1 := (Prod.mk.inj h1).2
        have hy : p1.1 + (p1.2 : ZMod m) = p2.1 + (p2.2 : ZMod m) := (Prod.mk.inj h2).2
        have ha : (p1.2 : ZMod m) = (p2.2 : ZMod m) := by linear_combination hy - hx
        exact Prod.ext hx (hcast_eq _ _ (by have := hA_lt _ hp1.2; omega) (by have := hA_lt _ hp2.2; omega) ha)
      · exact absurd (Prod.mk.inj h1).1 (by decide)
  have hL12_card : L12.card = m * A.card := by
    rw [Finset.card_image_of_injOn]
    · simp [ZMod.card]
    · intro p1 hp1 p2 hp2 h
      rw [Finset.mem_coe, Finset.mem_product] at hp1 hp2
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · have hx : p1.1 = p2.1 := (Prod.mk.inj h1).2
        have hy : p1.1 + (p1.2 : ZMod m) = p2.1 + (p2.2 : ZMod m) := (Prod.mk.inj h2).2
        have ha : (p1.2 : ZMod m) = (p2.2 : ZMod m) := by linear_combination hy - hx
        exact Prod.ext hx (hcast_eq _ _ (by have := hA_lt _ hp1.2; omega) (by have := hA_lt _ hp2.2; omega) ha)
      · exact absurd (Prod.mk.inj h1).1 (by decide)
  have hL02_card : L02.card = m * A.card := by
    rw [Finset.card_image_of_injOn]
    · simp [ZMod.card]
    · intro p1 hp1 p2 hp2 h
      rw [Finset.mem_coe, Finset.mem_product] at hp1 hp2
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · have hx : p1.1 = p2.1 := (Prod.mk.inj h1).2
        have hy : p1.1 + (2 : ZMod m) * (p1.2 : ZMod m) = p2.1 + (2 : ZMod m) * (p2.2 : ZMod m) := (Prod.mk.inj h2).2
        have ha : (2 : ZMod m) * (p1.2 : ZMod m) = (2 : ZMod m) * (p2.2 : ZMod m) := by linear_combination hy - hx
        exact Prod.ext hx (h2mul_eq _ _ (hA_lt _ hp1.2) (hA_lt _ hp2.2) ha)
      · exact absurd (Prod.mk.inj h1).1 (by decide)
  have hdisj01_12 : Disjoint L01 L12 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rcases Finset.mem_image.mp h1 with ⟨p1, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨p2, _, hEq⟩
    rcases Sym2.eq_iff.mp hEq with ⟨ha, _⟩ | ⟨ha, hb⟩
    · exact absurd (Prod.mk.inj ha).1 (by decide)
    · exact absurd (Prod.mk.inj hb).1 (by decide)
  have hdisj012 : Disjoint (L01 ∪ L12) L02 := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]
      intro e h1 h2
      rcases Finset.mem_image.mp h1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨p2, _, hEq⟩
      rcases Sym2.eq_iff.mp hEq with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd (Prod.mk.inj hb).1 (by decide)
      · exact absurd (Prod.mk.inj ha).1 (by decide)
    · rw [Finset.disjoint_left]
      intro e h1 h2
      rcases Finset.mem_image.mp h1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨p2, _, hEq⟩
      rcases Sym2.eq_iff.mp hEq with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact absurd (Prod.mk.inj ha).1 (by decide)
      · exact absurd (Prod.mk.inj ha).1 (by decide)
  have hsubE : L01 ∪ L12 ∪ L02 ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_union] at he
    rw [SimpleGraph.mem_edgeFinset]
    rcases he with (h1 | h2) | h3
    · rcases Finset.mem_image.mp h1 with ⟨⟨x, a⟩, hp, rfl⟩
      exact ⟨a, (Finset.mem_product.mp hp).2, by ring⟩
    · rcases Finset.mem_image.mp h2 with ⟨⟨x, b⟩, hp, rfl⟩
      exact ⟨b, (Finset.mem_product.mp hp).2, by ring⟩
    · rcases Finset.mem_image.mp h3 with ⟨⟨x, c⟩, hp, rfl⟩
      exact ⟨c, (Finset.mem_product.mp hp).2, by ring⟩
  have hE_ge : 3 * m * A.card ≤ G.edgeFinset.card := by
    have hcard_u : (L01 ∪ L12 ∪ L02).card = 3 * m * A.card := by
      rw [Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj01_12,
          hL01_card, hL12_card, hL02_card]
      ring
    exact hcard_u ▸ Finset.card_le_card hsubE
  have hV_card : Fintype.card V = 3 * m := by simp [V, ZMod.card]
  have hV_ge : M₀ ≤ Fintype.card V := by omega
  have hRS_lt := hRS V G hV_ge hG_uniq
  rw [hV_card] at hRS_lt
  have hE_geR : 3 * (m : ℝ) * (A.card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by exact_mod_cast hE_ge
  have hm_le_3N : (m : ℝ) ≤ 3 * (N : ℝ) := by
    have : m ≤ 3 * N := by omega
    exact_mod_cast this
  have hlower : (δ / 9) * ((3 * m : ℕ) : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) := by
    push_cast
    calc (δ / 9) * (3 * (m : ℝ)) ^ 2 = δ * (m : ℝ) * (m : ℝ) := by ring
      _ ≤ δ * (m : ℝ) * (3 * (N : ℝ)) := mul_le_mul_of_nonneg_left hm_le_3N (by positivity)
      _ = 3 * (m : ℝ) * (δ * (N : ℝ)) := by ring
      _ ≤ 3 * (m : ℝ) * (A.card : ℝ) := mul_le_mul_of_nonneg_left hA_card (by positivity)
      _ ≤ (G.edgeFinset.card : ℝ) := hE_geR
  linarith

/-- **2D Axis-Aligned Corners Theorem (via Triangle Removal / Ruzsa–Szemerédi):**
For every `δ > 0`, there exists `N₀ : ℕ` such that for every `N ≥ N₀` and every subset
`A ⊆ Finset.range N ×ˢ Finset.range N` with `|A| ≥ δ N²`, there exist `(x, y) ∈ A` and a
nonzero step `d : ℤ` (`d ≠ 0`) such that `(x + d, y)` and `(x, y + d)` (in `ℤ × ℤ`, cast from
elements of `A`) also belong to `A`. -/
theorem corners_theorem_via_removal (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset (ℕ × ℕ),
      A ⊆ Finset.range N ×ˢ Finset.range N →
      δ * (N : ℝ) ^ 2 ≤ (A.card : ℝ) →
      ∃ (x y x' y' : ℕ), (x, y) ∈ A ∧ (x', y) ∈ A ∧ (x, y') ∈ A ∧
        x' ≠ x ∧ (x' : ℤ) - (x : ℤ) = (y' : ℤ) - (y : ℤ) := by
  rcases ruzsa_szemeredi_unique_triangle (δ / 16) (by linarith) with ⟨M₀, hRS⟩
  refine ⟨max 1 M₀, ?_⟩
  intro N hN A hA_sub hA_card
  by_contra hnocorner
  push Not at hnocorner
  -- Tripartite line graph `G` on `V := Fin N ⊕ (Fin N ⊕ Fin (2 * N))` (`|V| = 4 * N`)
  let V := Fin N ⊕ (Fin N ⊕ Fin (2 * N))
  let adjG : V → V → Prop := fun a b =>
    match a, b with
    | Sum.inl x, Sum.inr (Sum.inl y) => (x.val, y.val) ∈ A
    | Sum.inr (Sum.inl y), Sum.inl x => (x.val, y.val) ∈ A
    | Sum.inl x, Sum.inr (Sum.inr z) => x.val ≤ z.val ∧ (x.val, z.val - x.val) ∈ A
    | Sum.inr (Sum.inr z), Sum.inl x => x.val ≤ z.val ∧ (x.val, z.val - x.val) ∈ A
    | Sum.inr (Sum.inl y), Sum.inr (Sum.inr z) => y.val ≤ z.val ∧ (z.val - y.val, y.val) ∈ A
    | Sum.inr (Sum.inr z), Sum.inr (Sum.inl y) => y.val ≤ z.val ∧ (z.val - y.val, y.val) ∈ A
    | _, _ => False
  let G : SimpleGraph V :=
    { Adj := adjG
      symm := ⟨by rintro (x | (y | z)) (x' | (y' | z')) h <;> exact h⟩
      loopless := ⟨by rintro (x | (y | z)) h <;> exact h⟩ }
  -- Key helper: any triangle `(inl x, inr (inl y), inr (inr z))` MUST have `z.val = x.val + y.val`
  have htri_eq : ∀ (x y : Fin N) (z : Fin (2 * N)),
      (x.val, y.val) ∈ A →
      x.val ≤ z.val → (x.val, z.val - x.val) ∈ A →
      y.val ≤ z.val → (z.val - y.val, y.val) ∈ A →
      z.val = x.val + y.val := by
    intro x y z hxy hxz hxzA hyz hyzA
    by_contra hne
    have hdiff : ((z.val - y.val : ℕ) : ℤ) - (x.val : ℤ) =
        ((z.val - x.val : ℕ) : ℤ) - (y.val : ℤ) := by omega
    exact hnocorner x.val y.val (z.val - y.val) (z.val - x.val) hxy hyzA hxzA (by omega) hdiff
  -- Every edge of `G` belongs to a unique triangle!
  have hG_uniq : ∀ a b : V, G.Adj a b → ∃! c : V, G.Adj a c ∧ G.Adj b c := by
    rintro (x | (y | z)) (x' | (y' | z')) hab
    · exact False.elim hab
    · -- `(inl x, inr (inl y'))`: unique partner `inr (inr ⟨x + y', _⟩)`
      have hlt : x.val + y'.val < 2 * N := by omega
      refine ⟨Sum.inr (Sum.inr ⟨x.val + y'.val, hlt⟩),
        ⟨⟨by dsimp only; omega, by simpa using hab⟩, ⟨by dsimp only; omega, by simpa using hab⟩⟩, ?_⟩
      rintro (w | (w | z0)) ⟨h1, h2⟩
      · exact False.elim h1
      · exact False.elim h2
      · have hz := htri_eq x y' z0 hab h1.1 h1.2 h2.1 h2.2
        congr 2; ext; exact hz
    · -- `(inl x, inr (inr z'))`: unique partner `inr (inl ⟨z' - x, _⟩)`
      have hmem := Finset.mem_product.mp (hA_sub hab.2)
      have hylt : z'.val - x.val < N := Finset.mem_range.mp hmem.2
      refine ⟨Sum.inr (Sum.inl ⟨z'.val - x.val, hylt⟩),
        ⟨hab.2, ⟨by dsimp only; omega, by
          have : z'.val - (z'.val - x.val) = x.val := by omega
          simpa [this] using hab.2⟩⟩, ?_⟩
      rintro (w | (y0 | w)) ⟨h1, h2⟩
      · exact False.elim h1
      · have hz := htri_eq x y0 z' h1 hab.1 hab.2 h2.1 h2.2
        congr 2; ext; dsimp only; omega
      · exact False.elim h2
    · -- `(inr (inl y), inl x')`
      have hlt : x'.val + y.val < 2 * N := by omega
      refine ⟨Sum.inr (Sum.inr ⟨x'.val + y.val, hlt⟩),
        ⟨⟨by dsimp only; omega, by simpa using hab⟩, ⟨by dsimp only; omega, by simpa using hab⟩⟩, ?_⟩
      rintro (w | (w | z0)) ⟨h1, h2⟩
      · exact False.elim h2
      · exact False.elim h1
      · have hz := htri_eq x' y z0 hab h2.1 h2.2 h1.1 h1.2
        congr 2; ext; exact hz
    · exact False.elim hab
    · -- `(inr (inl y), inr (inr z'))`
      have hmem := Finset.mem_product.mp (hA_sub hab.2)
      have hxlt : z'.val - y.val < N := Finset.mem_range.mp hmem.1
      refine ⟨Sum.inl ⟨z'.val - y.val, hxlt⟩,
        ⟨hab.2, ⟨by dsimp only; omega, by
          have : z'.val - (z'.val - y.val) = y.val := by omega
          simpa [this] using hab.2⟩⟩, ?_⟩
      rintro (x0 | (w | w)) ⟨h1, h2⟩
      · have hz := htri_eq x0 y z' h1 h2.1 h2.2 hab.1 hab.2
        congr 1; ext; dsimp only; omega
      · exact False.elim h1
      · exact False.elim h2
    · -- `(inr (inr z), inl x')`
      have hmem := Finset.mem_product.mp (hA_sub hab.2)
      have hylt : z.val - x'.val < N := Finset.mem_range.mp hmem.2
      refine ⟨Sum.inr (Sum.inl ⟨z.val - x'.val, hylt⟩),
        ⟨⟨by dsimp only; omega, by
          have : z.val - (z.val - x'.val) = x'.val := by omega
          simpa [this] using hab.2⟩, hab.2⟩, ?_⟩
      rintro (w | (y0 | w)) ⟨h1, h2⟩
      · exact False.elim h2
      · have hz := htri_eq x' y0 z h2 hab.1 hab.2 h1.1 h1.2
        congr 2; ext; dsimp only; omega
      · exact False.elim h1
    · -- `(inr (inr z), inr (inl y'))`
      have hmem := Finset.mem_product.mp (hA_sub hab.2)
      have hxlt : z.val - y'.val < N := Finset.mem_range.mp hmem.1
      refine ⟨Sum.inl ⟨z.val - y'.val, hxlt⟩,
        ⟨⟨by dsimp only; omega, by
          have : z.val - (z.val - y'.val) = y'.val := by omega
          simpa [this] using hab.2⟩, hab.2⟩, ?_⟩
      rintro (x0 | (w | w)) ⟨h1, h2⟩
      · have hz := htri_eq x0 y' z h2 h1.1 h1.2 hab.1 hab.2
        congr 1; ext; dsimp only; omega
      · exact False.elim h2
      · exact False.elim h1
    · exact False.elim hab
  -- `|A| ≤ |E(G)|` via the `(inl x, inr (inl y))` layer
  have hE_ge : A.card ≤ G.edgeFinset.card := by
    let f : ℕ × ℕ → Sym2 V := fun p =>
      if h : p.1 < N ∧ p.2 < N then s(Sum.inl ⟨p.1, h.1⟩, Sum.inr (Sum.inl ⟨p.2, h.2⟩))
      else s(Sum.inl ⟨0, by omega⟩, Sum.inl ⟨0, by omega⟩)
    have hmaps : ∀ p ∈ A, f p ∈ G.edgeFinset := by
      intro p hp
      have hmem := Finset.mem_product.mp (hA_sub hp)
      have hlt : p.1 < N ∧ p.2 < N := ⟨Finset.mem_range.mp hmem.1, Finset.mem_range.mp hmem.2⟩
      simp only [f, dif_pos hlt, SimpleGraph.mem_edgeFinset]
      exact hp
    have hinj : Set.InjOn f (A : Set (ℕ × ℕ)) := by
      intro p1 hp1 p2 hp2 h
      have hlt1 : p1.1 < N ∧ p1.2 < N :=
        ⟨Finset.mem_range.mp (Finset.mem_product.mp (hA_sub hp1)).1,
         Finset.mem_range.mp (Finset.mem_product.mp (hA_sub hp1)).2⟩
      have hlt2 : p2.1 < N ∧ p2.2 < N :=
        ⟨Finset.mem_range.mp (Finset.mem_product.mp (hA_sub hp2)).1,
         Finset.mem_range.mp (Finset.mem_product.mp (hA_sub hp2)).2⟩
      simp only [f, dif_pos hlt1, dif_pos hlt2] at h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact Prod.ext (congrArg Fin.val (Sum.inl.inj h1)) (congrArg Fin.val (Sum.inl.inj (Sum.inr.inj h2)))
      · cases h1
    calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ G.edgeFinset.card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
  have hV_card : Fintype.card V = 4 * N := by simp [V]; ring
  have hV_ge : M₀ ≤ Fintype.card V := by omega
  have hRS_lt := hRS V G hV_ge hG_uniq
  rw [hV_card] at hRS_lt
  have hE_geR : (A.card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by exact_mod_cast hE_ge
  have hRHS : (δ / 16) * ((4 * N : ℕ) : ℝ) ^ 2 = δ * (N : ℝ) ^ 2 := by push_cast; ring
  linarith

end RothAndCorners

end
end Arith4Ext.SzemerediRegularity
