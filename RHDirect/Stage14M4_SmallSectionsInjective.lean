import RHDirect.Stage12SchurWeylLattices
import RHDirect.Stage10GeometryOfNumbers

/-!
# RHDirect.Stage14M4_SmallSectionsInjective

Field-2 Package M4 Wave 1 formalization of:
1. **Small-Section Generated Sublattices & `SmallGeneratedCount`**:
   - Generated sublattices `smallGenSubmodule L R` and `smallStrictGenSubmodule L R` for
     arbitrary discrete Euclidean/Hermitian lattices `L ⊂ E`, graded Hermitian algebras
     `A : GradedHermAlgebra d`, and CM Hermitian lattices `Λ : CMHermLattice d r` /
     exterior-power lattices `(Λ.complexExtPow hk1 hkr).euclLat`.
   - Exact rank tracking `smallGenRank L R`, covolume / slope bounds, and cardinality
     `SmallGeneratedCount L R` (`gradedSmallGeneratedCount A k hk`).
2. **Proved Upper Bounds `small_generated_count_upper`**:
   - Geometry-of-numbers lattice-point counting bounds via `Stage10GeometryOfNumbers` and
     `Stage2SiegelReduction` in terms of `smallGenRank`, `lambda1`, `covol`, `succMin`, and `muMax`.
   - Successive-minima / covolume bound `covol (smallGenSubmodule L R) ≤ lambda1 * R^(m - 1)`
     yielding `(SmallGeneratedCount L R : ℝ) ≤ (1 + 2 * R^m / covol (smallGenSubmodule L R)) ^ m`.
   - Hodge covolume upper bounds bridged to `Stage12SchurWeylLattices.L3_hodge_covolume_bound`,
     `CMHermLattice`, and `O(k^(d+1))` graded-algebra counting upper bounds matching
     `Stage12SchurWeylLattices.moriwaki_big_small_sections`.
3. **Injectivity from Self-Intersection Bounds `small_sections_injective_of_self_intersection_bound`**:
   - Kernel-slope and first-minimum injectivity criteria on small sections `{x ∈ L | ‖x‖ ≤ R}`
     and `A.smallSectionsSet k`.
   - Divisible Bost-slope / vanishing-order injectivity (`bost_slope_inequality_divisible`) and
     self-intersection defect injectivity (`SelfIntersectionRestrictionDatum`) on single maps and
     families of irreducible components (`ComponentRestrictionSystem`), plus full-submodule
     injectivity on `smallGenSubmodule L R`.
   - Restriction-mediated small-section counting upper bounds on `gradedSmallGeneratedCount`.
4. **Large-Degree Line Extraction `line_of_large_degree_of_use`**:
   - Saturated rank-1 line extraction `line_of_large_degree_of_hermite_minkowski` using
     `Stage10GeometryOfNumbers.hermite_minkowski_bound_all_dims`.
   - Counting-to-line extraction `line_of_large_degree_of_counting_supply` deriving a saturated
     rank-1 sublattice of controlled large Arakelov degree directly from a small-section
     counting lower bound via `small_generated_count_upper`.
   - Full Hilbert–Samuel / Moriwaki theorem `line_of_large_degree_of_use` (and
     `line_of_arbitrary_large_degree_of_use`), plus a packaged Wave-2 bridge
     `M4SmallSectionsBridge` and 0-assumption projective-space witnesses
     `projSpace_m4_small_sections_bridge` and `projSpace_small_generated_count_two_sided`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Set
open RHDirect.ArakelovCovolume (rk covol degAr muMax
  discreteTopology_of_le finrank_int_eq_finrank_real_span rk_pos_of_ne_bot
  covol_pos covol_bot degAr_bot covol_span_singleton slope_span_singleton
  slope_le_muMax muMax_mono bost_slope_inequality bost_slope_inequality_divisible
  bost_vanishing_criterion)
open RHDirect.Stage2SiegelReduction (lattice_inter_closedBall_finite lambda1
  exists_norm_eq_lambda1 lambda1_pos lambda1_le_norm lambda1_le_hermite
  ncard_lattice_closedBall_le succMin succMin_mono succMin_zero_eq_lambda1
  succMin_pos covol_le_prod_succMin neg_log_lambda1_le_muMax
  slope_sub_half_log_rk_le_neg_log_lambda1 covol_le_prod_norm)
open RHDirect.Stage4ArakelovBost (IsSaturated saturation isSaturated_saturation
  le_saturation saturation_le rk_saturation covol_saturation_le
  slope_le_slope_saturation quotLat rk_add_quotLat covol_eq_mul_quotLat
  degAr_eq_add_quotLat muMin muMin_le_slope_le_muMax)
open RHDirect.Stage10GeometryOfNumbers (hermite_minkowski_bound_all_dims
  minkowski_second_theorem_lower unitBallVolume_eq)
open RHDirect.Stage11MoriwakiCovolume (arithDeg arithDeg_eq_rk_mul_slope
  slope_eq_arithDeg_div_rk unitBallVol unitBallVol_pos log_unitBallVol_ge
  h0Arith h0ArithStrict h0ArithStrict_le_h0Arith one_le_h0Arith one_le_h0ArithStrict
  exists_isometric_euclidean_lattice h0ArithStrict_lower_bound_minkowski
  log_h0ArithStrict_lower_bound minkowski_second_theorem_general)
open RHDirect.Stage12SchurWeylLattices (CMHermLattice GradedHermAlgebra
  moriwaki_big_small_sections projSpaceGradedHermAlgebra
  L3_hodge_covolume_bound)
open scoped BigOperators ENNReal Topology

namespace RHDirect.Stage14M4_SmallSectionsInjective

/-! ## Section 1: Small-Section Generated Sublattices and `SmallGeneratedCount` -/

section SmallGeneratedSublattices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Closed-ball set of integral sections `{v ∈ L | ‖v‖ ≤ R}` in a Euclidean lattice `L ⊂ E`. -/
def smallBallSet (L : Submodule ℤ E) (R : ℝ) : Set E :=
  (L : Set E) ∩ Metric.closedBall (0 : E) R

/-- Strict-ball set of integral sections `{v ∈ L | ‖v‖ < R}` in a Euclidean lattice `L ⊂ E`. -/
def smallStrictBallSet (L : Submodule ℤ E) (R : ℝ) : Set E :=
  (L : Set E) ∩ Metric.ball (0 : E) R

/-- Sublattice generated over `ℤ` by all integral sections of norm `≤ R`. -/
def smallGenSubmodule (L : Submodule ℤ E) (R : ℝ) : Submodule ℤ E :=
  Submodule.span ℤ (smallBallSet L R)

/-- Sublattice generated over `ℤ` by all integral sections of strict norm `< R`. -/
def smallStrictGenSubmodule (L : Submodule ℤ E) (R : ℝ) : Submodule ℤ E :=
  Submodule.span ℤ (smallStrictBallSet L R)

/-- Rank of the sublattice generated by small sections of norm `≤ R`. -/
def smallGenRank (L : Submodule ℤ E) (R : ℝ) : ℕ :=
  rk (smallGenSubmodule L R)

/-- **Small-Section Generated Count (`SmallGeneratedCount`)**:
number of integral lattice sections in `smallGenSubmodule L R` of norm `≤ R`. -/
def SmallGeneratedCount (L : Submodule ℤ E) (R : ℝ) : ℕ :=
  ((smallGenSubmodule L R : Set E) ∩ Metric.closedBall (0 : E) R).ncard

/-- Strict-ball version of `SmallGeneratedCount`. -/
def SmallGeneratedStrictCount (L : Submodule ℤ E) (R : ℝ) : ℕ :=
  ((smallStrictGenSubmodule L R : Set E) ∩ Metric.ball (0 : E) R).ncard

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma mem_smallBallSet_iff (L : Submodule ℤ E) (R : ℝ) (v : E) :
    v ∈ smallBallSet L R ↔ v ∈ L ∧ ‖v‖ ≤ R := by
  simp [smallBallSet, Metric.mem_closedBall, dist_zero_right]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma mem_smallStrictBallSet_iff (L : Submodule ℤ E) (R : ℝ) (v : E) :
    v ∈ smallStrictBallSet L R ↔ v ∈ L ∧ ‖v‖ < R := by
  simp [smallStrictBallSet, Metric.mem_ball, dist_zero_right]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma smallGenSubmodule_le (L : Submodule ℤ E) (R : ℝ) :
    smallGenSubmodule L R ≤ L :=
  Submodule.span_le.mpr fun _ hx => hx.1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma smallStrictGenSubmodule_le (L : Submodule ℤ E) (R : ℝ) :
    smallStrictGenSubmodule L R ≤ smallGenSubmodule L R :=
  Submodule.span_mono (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma smallStrictGenSubmodule_le_lat (L : Submodule ℤ E) (R : ℝ) :
    smallStrictGenSubmodule L R ≤ L :=
  (smallStrictGenSubmodule_le L R).trans (smallGenSubmodule_le L R)

instance discreteTopology_smallGenSubmodule (L : Submodule ℤ E) [DiscreteTopology L] (R : ℝ) :
    DiscreteTopology (smallGenSubmodule L R) :=
  discreteTopology_of_le (smallGenSubmodule_le L R)

instance discreteTopology_smallStrictGenSubmodule (L : Submodule ℤ E) [DiscreteTopology L]
    (R : ℝ) : DiscreteTopology (smallStrictGenSubmodule L R) :=
  discreteTopology_of_le (smallStrictGenSubmodule_le_lat L R)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma smallGenSubmodule_mono_radius (L : Submodule ℤ E) {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    smallGenSubmodule L R₁ ≤ smallGenSubmodule L R₂ :=
  Submodule.span_mono (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hR))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma smallGenSubmodule_mono_lat {L₁ L₂ : Submodule ℤ E} (hL : L₁ ≤ L₂) (R : ℝ) :
    smallGenSubmodule L₁ R ≤ smallGenSubmodule L₂ R :=
  Submodule.span_mono (Set.inter_subset_inter_left _ hL)

theorem smallGenRank_le_rk (L : Submodule ℤ E) [DiscreteTopology L] (R : ℝ) :
    smallGenRank L R ≤ rk L := by
  unfold smallGenRank rk
  have hsp : Submodule.span ℝ ((smallGenSubmodule L R : Submodule ℤ E) : Set E) ≤
      Submodule.span ℝ (L : Set E) :=
    Submodule.span_mono (smallGenSubmodule_le L R)
  rw [finrank_int_eq_finrank_real_span (smallGenSubmodule L R),
    finrank_int_eq_finrank_real_span L]
  exact Submodule.finrank_mono hsp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGenSubmodule_ne_bot_iff (L : Submodule ℤ E) (R : ℝ) :
    smallGenSubmodule L R ≠ ⊥ ↔ ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ R := by
  constructor
  · intro hne
    by_contra hnone
    push Not at hnone
    apply hne
    rw [eq_bot_iff]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨hvL, hvR⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    by_contra hv0
    exact (hnone v hvL hv0).not_ge (mem_closedBall_zero_iff.mp hvR)
  · rintro ⟨v, hvL, hv0, hvR⟩ hbot
    have hv : v ∈ smallGenSubmodule L R :=
      Submodule.subset_span ((mem_smallBallSet_iff L R v).mpr ⟨hvL, hvR⟩)
    rw [hbot, Submodule.mem_bot] at hv
    exact hv0 hv

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGenSubmodule_bot_of_lt_lambda1 (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : R < lambda1 L) :
    smallGenSubmodule L R = ⊥ := by
  by_contra hne
  obtain ⟨v, hvL, hv0, hvR⟩ := (smallGenSubmodule_ne_bot_iff L R).mp hne
  have hle := lambda1_le_norm L hvL hv0
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGenRank_eq_zero_of_lt_lambda1 (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : R < lambda1 L) :
    smallGenRank L R = 0 := by
  rw [smallGenRank, smallGenSubmodule_bot_of_lt_lambda1 L hR]
  simp [rk]

theorem smallGenSubmodule_bot_of_muMax_lt (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) (hmu : muMax L < -Real.log R) :
    smallGenSubmodule L R = ⊥ := by
  by_cases hL0 : L = ⊥
  · rw [eq_bot_iff]; exact (smallGenSubmodule_le L R).trans (le_of_eq hL0)
  have hlam : R < lambda1 L := by
    have h1 := neg_log_lambda1_le_muMax L hL0
    have hlog : Real.log R < Real.log (lambda1 L) := by linarith
    exact (Real.log_lt_log_iff hR (lambda1_pos L hL0)).mp hlog
  exact smallGenSubmodule_bot_of_lt_lambda1 L hlam

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGeneratedCount_eq_h0Arith_smallGen (L : Submodule ℤ E) (R : ℝ) :
    SmallGeneratedCount L R = h0Arith (smallGenSubmodule L R) R := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGeneratedCount_eq_h0Arith (L : Submodule ℤ E) (R : ℝ) :
    SmallGeneratedCount L R = h0Arith L R := by
  unfold SmallGeneratedCount h0Arith
  congr 1
  ext x
  simp only [Set.mem_inter_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxM, hxR⟩
    exact ⟨smallGenSubmodule_le L R hxM, hxR⟩
  · rintro ⟨hxL, hxR⟩
    exact ⟨Submodule.subset_span ⟨hxL, hxR⟩, hxR⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGeneratedStrictCount_eq_h0ArithStrict (L : Submodule ℤ E) (R : ℝ) :
    SmallGeneratedStrictCount L R = h0ArithStrict L R := by
  unfold SmallGeneratedStrictCount h0ArithStrict
  congr 1
  ext x
  simp only [Set.mem_inter_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxM, hxR⟩
    exact ⟨smallStrictGenSubmodule_le_lat L R hxM, hxR⟩
  · rintro ⟨hxL, hxR⟩
    exact ⟨Submodule.subset_span ⟨hxL, hxR⟩, hxR⟩

theorem smallGeneratedStrictCount_le_smallGeneratedCount (L : Submodule ℤ E)
    [DiscreteTopology L] (R : ℝ) :
    SmallGeneratedStrictCount L R ≤ SmallGeneratedCount L R := by
  rw [smallGeneratedStrictCount_eq_h0ArithStrict, smallGeneratedCount_eq_h0Arith]
  exact h0ArithStrict_le_h0Arith L R

theorem one_le_smallGeneratedCount (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 ≤ R) :
    1 ≤ SmallGeneratedCount L R := by
  rw [smallGeneratedCount_eq_h0Arith]
  exact one_le_h0Arith L hR

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smallGeneratedCount_eq_one_of_bot (L : Submodule ℤ E) {R : ℝ} (hR : 0 ≤ R)
    (hbot : smallGenSubmodule L R = ⊥) :
    SmallGeneratedCount L R = 1 := by
  unfold SmallGeneratedCount
  rw [hbot]
  have hset : ((⊥ : Submodule ℤ E) : Set E) ∩ Metric.closedBall (0 : E) R = {(0 : E)} := by
    ext x
    simp only [Submodule.bot_coe, Set.mem_inter_iff, Set.mem_singleton_iff,
      Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨rfl, _⟩; rfl
    · rintro rfl; exact ⟨rfl, by simpa using hR⟩
  rw [hset, Set.ncard_singleton]

theorem smallGeneratedCount_mono_radius (L : Submodule ℤ E) [DiscreteTopology L]
    {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    SmallGeneratedCount L R₁ ≤ SmallGeneratedCount L R₂ := by
  rw [smallGeneratedCount_eq_h0Arith, smallGeneratedCount_eq_h0Arith]
  exact RHDirect.Stage11MoriwakiCovolume.h0Arith_mono L hR

theorem smallGeneratedCount_mono_lat {L₁ L₂ : Submodule ℤ E} [DiscreteTopology L₂]
    (hL : L₁ ≤ L₂) (R : ℝ) :
    SmallGeneratedCount L₁ R ≤ SmallGeneratedCount L₂ R := by
  rw [smallGeneratedCount_eq_h0Arith, smallGeneratedCount_eq_h0Arith]
  exact Set.ncard_le_ncard (Set.inter_subset_inter_left _ hL)
    (lattice_inter_closedBall_finite L₂ R)

theorem lambda1_le_lambda1_smallGen (L : Submodule ℤ E) [DiscreteTopology L] (R : ℝ)
    (hne : smallGenSubmodule L R ≠ ⊥) :
    lambda1 L ≤ lambda1 (smallGenSubmodule L R) := by
  obtain ⟨v, hvM, hv0, hv_eq⟩ := exists_norm_eq_lambda1 (smallGenSubmodule L R) hne
  rw [← hv_eq]
  exact lambda1_le_norm L (smallGenSubmodule_le L R hvM) hv0

theorem muMax_smallGen_le (L : Submodule ℤ E) [DiscreteTopology L] (R : ℝ)
    (hne : smallGenSubmodule L R ≠ ⊥) :
    muMax (smallGenSubmodule L R) ≤ muMax L :=
  muMax_mono L (smallGenSubmodule L R) (smallGenSubmodule_le L R) hne

/-- Every successive minimum of `smallGenSubmodule L R` is bounded above by `R`
(when `smallGenSubmodule L R ≠ ⊥` and `0 < R`). -/
theorem succMin_smallGen_le (L : Submodule ℤ E) [DiscreteTopology L] {R : ℝ} (hR : 0 < R)
    (_hne : smallGenSubmodule L R ≠ ⊥) (k : Fin (smallGenRank L R)) :
    succMin (smallGenSubmodule L R) k ≤ R := by
  classical
  let M := smallGenSubmodule L R
  have hspan_eq : Submodule.span ℝ (smallBallSet L R) = Submodule.span ℝ (M : Set E) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      intro x hx
      exact Submodule.subset_span (Submodule.subset_span hx)
    · refine Submodule.span_le.mpr ?_
      intro x hxM
      have hx_z : x ∈ Submodule.span ℤ (smallBallSet L R) := hxM
      have hsub : (Submodule.span ℤ (smallBallSet L R) : Set E) ⊆
          (Submodule.span ℝ (smallBallSet L R) : Set E) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span hz
        | zero => exact Submodule.zero_mem _
        | add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb
        | smul a _ _ ha =>
            change (a : ℤ) • _ ∈ Submodule.span ℝ (smallBallSet L R)
            rw [← Int.cast_smul_eq_zsmul ℝ a]
            exact Submodule.smul_mem _ _ ha
      exact hsub hx_z
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℝ (smallBallSet L R)
  have hs_fin : s.Finite := hs_li.setFinite
  let T : Finset E := hs_fin.toFinset
  have hTs : (T : Set E) = s := hs_fin.coe_toFinset
  have hT_li : LinearIndependent ℝ (Subtype.val : T → E) := by
    have heq : (Subtype.val : T → E) = (Subtype.val : s → E) ∘ Equiv.setCongr hTs := rfl
    rw [heq]
    exact hs_li.comp (Equiv.setCongr hTs) (Equiv.setCongr hTs).injective
  have hrange : Set.range (Subtype.val : T → E) = s := by
    rw [← hTs]; ext x; simp
  have hcard : T.card = smallGenRank L R := by
    unfold smallGenRank rk
    rw [finrank_int_eq_finrank_real_span M, ← hspan_eq, ← hs_span, ← hrange]
    simpa only [Fintype.card_coe] using (finrank_span_eq_card hT_li).symm
  have hle : k.1 + 1 ≤ T.card := by
    rw [hcard]
    exact k.2
  let e : Fin (k.1 + 1) ↪ T := (Fin.castLEEmb hle).trans T.equivFin.symm.toEmbedding
  let v : Fin (k.1 + 1) → E := fun j => (e j : E)
  have hv_li : LinearIndependent ℝ v := hT_li.comp e e.injective
  have hv_ball : ∀ j, v j ∈ smallBallSet L R := fun j => hs_sub (hTs ▸ (e j).2)
  have hv_mem : ∀ j, v j ∈ M := fun j => Submodule.subset_span (hv_ball j)
  have hv_norm : ∀ j, ‖v j‖ ≤ R := fun j => ((mem_smallBallSet_iff L R (v j)).mp (hv_ball j)).2
  unfold succMin
  change sInf { t : ℝ | 0 ≤ t ∧ ∃ w : Fin (k.1 + 1) → E,
    (∀ j, w j ∈ M) ∧ LinearIndependent ℝ w ∧ ∀ j, ‖w j‖ ≤ t } ≤ R
  apply csInf_le
  · refine ⟨0, fun _ ht => ht.1⟩
  · exact ⟨hR.le, v, hv_mem, hv_li, hv_norm⟩

/-- Covolume and slope bounds for the small-section generated sublattice `smallGenSubmodule L R`:
`covol (smallGenSubmodule L R) ≤ lambda1 (smallGenSubmodule L R) * R ^ (smallGenRank L R - 1)`,
`covol (smallGenSubmodule L R) ≤ R ^ (smallGenRank L R)`, and
`-Real.log R ≤ ArakelovCovolume.slope (smallGenSubmodule L R) ≤ muMax L`. -/
theorem covol_and_slope_smallGen (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) (hne : smallGenSubmodule L R ≠ ⊥) :
    covol (smallGenSubmodule L R) ≤
      lambda1 (smallGenSubmodule L R) * R ^ (smallGenRank L R - 1) ∧
    covol (smallGenSubmodule L R) ≤ R ^ (smallGenRank L R) ∧
    -Real.log R ≤ RHDirect.ArakelovCovolume.slope (smallGenSubmodule L R) ∧
    RHDirect.ArakelovCovolume.slope (smallGenSubmodule L R) ≤ muMax L := by
  let M := smallGenSubmodule L R
  have hr_pos : 0 < rk M := rk_pos_of_ne_bot M hne
  have hprod_le : covol M ≤ ∏ i : Fin (rk M), succMin M i := covol_le_prod_succMin M
  have hsm_le : ∀ i : Fin (rk M), succMin M i ≤ R :=
    succMin_smallGen_le L hR hne
  have hlam_eq : succMin M ⟨0, hr_pos⟩ = lambda1 M :=
    succMin_zero_eq_lambda1 M hne
  have hprod_split : ∏ i : Fin (rk M), succMin M i ≤
      lambda1 M * R ^ (rk M - 1) := by
    let i0 : Fin (rk M) := ⟨0, hr_pos⟩
    have hsplit : ∏ i : Fin (rk M), succMin M i =
        succMin M i0 * ∏ i ∈ Finset.univ.erase i0, succMin M i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => succMin M i) (Finset.mem_univ i0)]
    have hrest : ∏ i ∈ Finset.univ.erase i0, succMin M i ≤ R ^ (rk M - 1) := by
      calc ∏ i ∈ Finset.univ.erase i0, succMin M i
          ≤ ∏ _i ∈ Finset.univ.erase i0, R :=
            Finset.prod_le_prod (fun i _ => (succMin_pos M hne i).le) fun i _ => hsm_le i
        _ = R ^ (Finset.univ.erase i0).card := by rw [Finset.prod_const]
        _ = R ^ (rk M - 1) := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_fin]
    have hi0 : succMin M i0 = lambda1 M := hlam_eq
    rw [hsplit, hi0]
    exact mul_le_mul_of_nonneg_left hrest (lambda1_pos M hne).le
  have hcov_lam : covol M ≤ lambda1 M * R ^ (rk M - 1) := hprod_le.trans hprod_split
  have hlam_le_R : lambda1 M ≤ R := by
    rw [← hlam_eq]
    exact hsm_le ⟨0, hr_pos⟩
  have hcov_R : covol M ≤ R ^ (rk M) := by
    calc covol M ≤ lambda1 M * R ^ (rk M - 1) := hcov_lam
      _ ≤ R * R ^ (rk M - 1) :=
          mul_le_mul_of_nonneg_right hlam_le_R (pow_nonneg hR.le _)
      _ = R ^ (rk M) := by
          conv_rhs => rw [← Nat.sub_add_cancel hr_pos, pow_succ']
  have hrposR : (0 : ℝ) < (rk M : ℝ) := Nat.cast_pos.mpr hr_pos
  have hsl_lo : -Real.log R ≤ RHDirect.ArakelovCovolume.slope M := by
    have hlog := Real.log_le_log (covol_pos M) hcov_R
    rw [Real.log_pow] at hlog
    unfold RHDirect.ArakelovCovolume.slope degAr
    change -Real.log (covol M) / (rk M : ℝ) ≥ -Real.log R
    rw [ge_iff_le, le_div_iff₀ hrposR]
    nlinarith
  have hsl_hi : RHDirect.ArakelovCovolume.slope M ≤ muMax L :=
    (slope_le_muMax M M le_rfl hne).trans (muMax_smallGen_le L R hne)
  exact ⟨hcov_lam, hcov_R, hsl_lo, hsl_hi⟩

end SmallGeneratedSublattices

section GradedAndCMLattices

/-- In a graded Hermitian section algebra `A : GradedHermAlgebra d`, the `ℤ`-submodule
generated by all strictly small sections `{s ∈ secLat k | supNorm k s < 1}`. -/
def gradedSmallGenSubmodule {d : ℕ} (A : GradedHermAlgebra d) (k : ℕ) :
    Submodule ℤ (A.secSpace k) :=
  Submodule.span ℤ (Subtype.val '' A.smallSectionsSet k)

/-- Rank of the sublattice generated by strictly small sections of `A` in degree `k`. -/
def gradedSmallGenRank {d : ℕ} (A : GradedHermAlgebra d) (k : ℕ) : ℕ :=
  rk (gradedSmallGenSubmodule A k)

/-- Small-section count `SmallGeneratedCount` in a graded Hermitian section algebra `A` at degree `k ≥ 1`. -/
def gradedSmallGeneratedCount {d : ℕ} (A : GradedHermAlgebra d)
    (k : ℕ) (hk : 1 ≤ k) : ℕ :=
  A.smallSectionsCard k hk

lemma gradedSmallGenSubmodule_le_secLat {d : ℕ} (A : GradedHermAlgebra d) (k : ℕ) :
    gradedSmallGenSubmodule A k ≤ A.secLat k := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, _, rfl⟩
  exact s.2

instance discreteTopology_gradedSmallGenSubmodule {d : ℕ}
    (A : GradedHermAlgebra d) (k : ℕ) : DiscreteTopology (gradedSmallGenSubmodule A k) :=
  discreteTopology_of_le (gradedSmallGenSubmodule_le_secLat A k)

lemma gradedSmallGenSubmodule_le_smallGen_volConst {d : ℕ}
    (A : GradedHermAlgebra d) {k : ℕ} (hk : 1 ≤ k) :
    gradedSmallGenSubmodule A k ≤ smallGenSubmodule (A.secLat k) A.volConst := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, rfl⟩
  refine Submodule.subset_span ((mem_smallBallSet_iff (A.secLat k) A.volConst s.1).mpr ⟨s.2, ?_⟩)
  have h1 := A.norm_le_vol_supNorm k hk s.1
  have h2 : A.supNorm k s.1 < 1 := hs
  exact h1.trans (mul_le_of_le_one_right A.volConst_pos.le h2.le)

theorem gradedSmallGenRank_le_rk {d : ℕ} (A : GradedHermAlgebra d) (k : ℕ) :
    gradedSmallGenRank A k ≤ rk (A.secLat k) := by
  unfold gradedSmallGenRank rk
  have hsp : Submodule.span ℝ ((gradedSmallGenSubmodule A k : Submodule ℤ (A.secSpace k)) :
      Set (A.secSpace k)) ≤ Submodule.span ℝ (A.secLat k : Set (A.secSpace k)) :=
    Submodule.span_mono (gradedSmallGenSubmodule_le_secLat A k)
  rw [finrank_int_eq_finrank_real_span (gradedSmallGenSubmodule A k),
    finrank_int_eq_finrank_real_span (A.secLat k)]
  exact Submodule.finrank_mono hsp

theorem gradedSmallGenRank_le_poly {d : ℕ} (A : GradedHermAlgebra d)
    {k : ℕ} (hk : 1 ≤ k) :
    (gradedSmallGenRank A k : ℝ) ≤ A.rankHi * (k : ℝ) ^ d :=
  (Nat.cast_le.mpr (gradedSmallGenRank_le_rk A k)).trans (A.rk_le_poly k hk)

theorem gradedSmallGeneratedCount_le_h0Arith {d : ℕ} (A : GradedHermAlgebra d)
    {k : ℕ} (hk : 1 ≤ k) :
    gradedSmallGeneratedCount A k hk ≤ h0Arith (A.secLat k) A.volConst := by
  unfold gradedSmallGeneratedCount GradedHermAlgebra.smallSectionsCard h0Arith
  have hsub : Subtype.val '' A.smallSectionsSet k ⊆
      (A.secLat k : Set (A.secSpace k)) ∩ Metric.closedBall 0 A.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := A.norm_le_vol_supNorm k hk s.1
    have h2 : A.supNorm k s.1 < 1 := hs
    exact h1.trans (mul_le_of_le_one_right A.volConst_pos.le h2.le)
  have hfin := lattice_inter_closedBall_finite (A.secLat k) A.volConst
  calc (A.smallSections_finite hk).toFinset.card
      = (A.smallSectionsSet k).ncard := (Set.ncard_eq_toFinset_card _ _).symm
    _ = (Subtype.val '' A.smallSectionsSet k).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((A.secLat k : Set (A.secSpace k)) ∩ Metric.closedBall 0 A.volConst).ncard :=
        Set.ncard_le_ncard hsub hfin

theorem gradedSmallGeneratedCount_le_smallGeneratedCount_volConst {d : ℕ}
    (A : GradedHermAlgebra d) {k : ℕ} (hk : 1 ≤ k) :
    gradedSmallGeneratedCount A k hk ≤ SmallGeneratedCount (A.secLat k) A.volConst := by
  rw [smallGeneratedCount_eq_h0Arith]
  exact gradedSmallGeneratedCount_le_h0Arith A hk

/-- Small-section count `SmallGeneratedCount` for a CM Hermitian lattice `Λ : CMHermLattice d r`. -/
def cmSmallGenCount {d r : ℕ} (Λ : CMHermLattice d r) (R : ℝ) : ℕ :=
  SmallGeneratedCount Λ.euclLat R

/-- Small-section count for the `k`-th exterior-power lattice `(Λ.complexExtPow hk1 hkr).euclLat`. -/
def cmExtPowSmallGenCount {d r : ℕ} (Λ : CMHermLattice d r)
    {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ r) (R : ℝ) : ℕ :=
  SmallGeneratedCount (Λ.complexExtPow hk1 hkr).euclLat R

end GradedAndCMLattices

/-! ## Section 2: `small_generated_count_upper` via Geometry of Numbers & Hodge Covolumes -/

section SmallGeneratedCountUpper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lattice-Point Sphere-Packing Upper Bound on `SmallGeneratedCount`**:
for any discrete lattice `L ⊂ E` and `R ≥ 0`, if `smallGenSubmodule L R ≠ ⊥`, then:
`SmallGeneratedCount L R ≤ (1 + 2 * R / lambda1 (smallGenSubmodule L R)) ^ (smallGenRank L R)`
and also `≤ (1 + 2 * R / lambda1 L) ^ (smallGenRank L R)`. -/
theorem small_generated_count_upper_lambda1 (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 ≤ R) (hne : smallGenSubmodule L R ≠ ⊥) :
    (SmallGeneratedCount L R : ℝ) ≤
      (1 + 2 * R / lambda1 (smallGenSubmodule L R)) ^ (smallGenRank L R) ∧
    (SmallGeneratedCount L R : ℝ) ≤
      (1 + 2 * R / lambda1 L) ^ (smallGenRank L R) := by
  let M := smallGenSubmodule L R
  have hL0 : L ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    exact (smallGenSubmodule_le L R).trans (le_of_eq h0)
  have h1 : (SmallGeneratedCount L R : ℝ) ≤ (1 + 2 * R / lambda1 M) ^ (smallGenRank L R) := by
    rw [smallGeneratedCount_eq_h0Arith_smallGen]
    exact ncard_lattice_closedBall_le M hne hR
  have hlam : lambda1 L ≤ lambda1 M := lambda1_le_lambda1_smallGen L R hne
  have hlamL_pos : 0 < lambda1 L := lambda1_pos L hL0
  have hlamM_pos : 0 < lambda1 M := lambda1_pos M hne
  have hbase : 1 + 2 * R / lambda1 M ≤ 1 + 2 * R / lambda1 L := by
    have hdiv : 2 * R / lambda1 M ≤ 2 * R / lambda1 L :=
      div_le_div_of_nonneg_left (by positivity) hlamL_pos hlam
    linarith
  have hbase_nn : 0 ≤ 1 + 2 * R / lambda1 M := by
    have : 0 ≤ 2 * R / lambda1 M := div_nonneg (by positivity) hlamM_pos.le
    linarith
  have h2 : (1 + 2 * R / lambda1 M) ^ (smallGenRank L R) ≤
      (1 + 2 * R / lambda1 L) ^ (smallGenRank L R) :=
    pow_le_pow_left₀ hbase_nn hbase _
  exact ⟨h1, h1.trans h2⟩

/-- **Minkowski / Covolume Upper Bound on `SmallGeneratedCount`** (using successive minima):
for `0 < R` and `smallGenSubmodule L R ≠ ⊥`, let `m = smallGenRank L R` and `M = smallGenSubmodule L R`.
Then `covol M ≤ lambda1 M * R ^ (m - 1)` and consequently
`(SmallGeneratedCount L R : ℝ) ≤ (1 + 2 * R ^ m / covol M) ^ m`. -/
theorem small_generated_count_upper_of_covol (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) (hne : smallGenSubmodule L R ≠ ⊥) :
    (SmallGeneratedCount L R : ℝ) ≤
      (1 + 2 * R ^ (smallGenRank L R) / covol (smallGenSubmodule L R)) ^ (smallGenRank L R) := by
  let M := smallGenSubmodule L R
  let m := smallGenRank L R
  have hm_pos : 0 < m := rk_pos_of_ne_bot M hne
  have hcov_lam := (covol_and_slope_smallGen L hR hne).1
  have hlam_pos : 0 < lambda1 M := lambda1_pos M hne
  have hcov_pos : 0 < covol M := covol_pos M
  have hinv_le : R / lambda1 M ≤ R ^ m / covol M := by
    have h1 : R * covol M ≤ R * (lambda1 M * R ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left hcov_lam hR.le
    have hpow : R * R ^ (m - 1) = R ^ m := by
      conv_rhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ']
    have h2 : R * covol M ≤ R ^ m * lambda1 M := by
      calc R * covol M ≤ R * (lambda1 M * R ^ (m - 1)) := h1
        _ = (R * R ^ (m - 1)) * lambda1 M := by ring
        _ = R ^ m * lambda1 M := by rw [hpow]
    exact (div_le_div_iff₀ hlam_pos hcov_pos).mpr h2
  have hbase : 1 + 2 * R / lambda1 M ≤ 1 + 2 * R ^ m / covol M := by
    have h2 : 2 * R / lambda1 M = 2 * (R / lambda1 M) := by ring
    have h3 : 2 * R ^ m / covol M = 2 * (R ^ m / covol M) := by ring
    linarith
  have hbase_nn : 0 ≤ 1 + 2 * R / lambda1 M := by
    have : 0 ≤ 2 * R / lambda1 M := div_nonneg (by positivity) hlam_pos.le
    linarith
  have hpack := (small_generated_count_upper_lambda1 L hR.le hne).1
  exact hpack.trans (pow_le_pow_left₀ hbase_nn hbase m)

/-- **Universal `muMax` Upper Bound on `SmallGeneratedCount`**:
holds unconditionally for EVERY discrete lattice `L ⊂ E` and EVERY `R ≥ 0`:
`(SmallGeneratedCount L R : ℝ) ≤ (1 + 2 * R * Real.exp (muMax L)) ^ (smallGenRank L R)` and
`Real.log (SmallGeneratedCount L R : ℝ) ≤ (smallGenRank L R : ℝ) * (max 0 (muMax L) + Real.log (1 + 2 * R))`. -/
theorem small_generated_count_upper (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 ≤ R) :
    (SmallGeneratedCount L R : ℝ) ≤
      (1 + 2 * R * Real.exp (muMax L)) ^ (smallGenRank L R) ∧
    Real.log (SmallGeneratedCount L R : ℝ) ≤
      (smallGenRank L R : ℝ) * (max 0 (muMax L) + Real.log (1 + 2 * R)) := by
  by_cases hne : smallGenSubmodule L R = ⊥
  · have hcount : SmallGeneratedCount L R = 1 := smallGeneratedCount_eq_one_of_bot L hR hne
    have hrk : smallGenRank L R = 0 := by rw [smallGenRank, hne]; simp [rk]
    rw [hcount, hrk]
    simp
  · have hL0 : L ≠ ⊥ := by
      intro h0
      apply hne
      rw [eq_bot_iff]
      exact (smallGenSubmodule_le L R).trans (le_of_eq h0)
    have hpack := (small_generated_count_upper_lambda1 L hR hne).2
    have hmu := neg_log_lambda1_le_muMax L hL0
    have hlamL_pos : 0 < lambda1 L := lambda1_pos L hL0
    have hlam_inv : (lambda1 L)⁻¹ ≤ Real.exp (muMax L) := by
      rw [← Real.exp_log hlamL_pos, ← Real.exp_neg]
      exact Real.exp_le_exp.mpr hmu
    have hbase : 1 + 2 * R / lambda1 L ≤ 1 + 2 * R * Real.exp (muMax L) := by
      rw [div_eq_mul_inv]
      have : 2 * R * (lambda1 L)⁻¹ ≤ 2 * R * Real.exp (muMax L) :=
        mul_le_mul_of_nonneg_left hlam_inv (by positivity)
      linarith
    have hbase_nn : 0 ≤ 1 + 2 * R / lambda1 L := by
      have : 0 ≤ 2 * R / lambda1 L := div_nonneg (by positivity) hlamL_pos.le
      linarith
    have hpow : (SmallGeneratedCount L R : ℝ) ≤
        (1 + 2 * R * Real.exp (muMax L)) ^ (smallGenRank L R) :=
      hpack.trans (pow_le_pow_left₀ hbase_nn hbase _)
    have hcnt_pos : (0 : ℝ) < (SmallGeneratedCount L R : ℝ) :=
      Nat.cast_pos.mpr (one_le_smallGeneratedCount L hR)
    have hbase_pos : 0 < 1 + 2 * R * Real.exp (muMax L) := by positivity
    have hlog := Real.log_le_log hcnt_pos hpow
    rw [Real.log_pow] at hlog
    have hle_exp : 1 + 2 * R * Real.exp (muMax L) ≤
        Real.exp (max 0 (muMax L)) * (1 + 2 * R) := by
      have h1 : 1 ≤ Real.exp (max 0 (muMax L)) := by
        rw [Real.one_le_exp_iff]; exact le_max_left _ _
      have h2 : Real.exp (muMax L) ≤ Real.exp (max 0 (muMax L)) :=
        Real.exp_le_exp.mpr (le_max_right _ _)
      nlinarith
    have hlog_base : Real.log (1 + 2 * R * Real.exp (muMax L)) ≤
        max 0 (muMax L) + Real.log (1 + 2 * R) := by
      have h3 := Real.log_le_log hbase_pos hle_exp
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at h3
      exact h3
    have hrk_nn : (0 : ℝ) ≤ (smallGenRank L R : ℝ) := Nat.cast_nonneg _
    exact ⟨hpow, hlog.trans (mul_le_mul_of_nonneg_left hlog_base hrk_nn)⟩

/-- **Minkowski Second Theorem Volume Bound on `smallGenSubmodule`**:
combining `Stage10GeometryOfNumbers.minkowski_second_theorem_lower` with `succMin_smallGen_le`
gives `(2^m / m!) * covol (smallGenSubmodule L R) ≤ R^m * unitBallVol m`. -/
theorem minkowski_covol_smallGen_le (L : Submodule ℤ E) [DiscreteTopology L]
    {R : ℝ} (hR : 0 < R) (hne : smallGenSubmodule L R ≠ ⊥) :
    ((2 : ℝ) ^ (smallGenRank L R) / ((smallGenRank L R).factorial : ℝ)) *
        covol (smallGenSubmodule L R) ≤
      R ^ (smallGenRank L R) * unitBallVol (smallGenRank L R) := by
  let M := smallGenSubmodule L R
  have hmink := (minkowski_second_theorem_general M hne).1
  have hprod : ∏ i : Fin (rk M), succMin M i ≤ R ^ (rk M) := by
    calc ∏ i : Fin (rk M), succMin M i
        ≤ ∏ _i : Fin (rk M), R :=
          Finset.prod_le_prod (fun i _ => (succMin_pos M hne i).le) fun i _ =>
            succMin_smallGen_le L hR hne i
      _ = R ^ (rk M) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hω_nn : 0 ≤ unitBallVol (rk M) := (unitBallVol_pos (rk M)).le
  exact hmink.trans (mul_le_mul_of_nonneg_right hprod hω_nn)

/-- **Hodge-Lattice `L3` Small-Section Counting Upper Bound**:
combines `Stage12SchurWeylLattices.L3_hodge_covolume_bound` with `small_generated_count_upper`
across a family of `m` Hodge lattices `M j ⊂ E j` (`j : Fin m`). -/
theorem small_generated_count_upper_of_hodge_covolume {m : ℕ}
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (s : ∀ j, Fin (rk (M j)) → E j)
    (hsM : ∀ j i, s j i ∈ M j)
    (hsli : ∀ j, LinearIndependent ℝ (s j))
    (C_sec : Fin m → ℝ) (hCpos : ∀ j, 0 < C_sec j)
    (hnorm : ∀ j i, ‖s j i‖ ≤ C_sec j)
    {D R : ℝ} (hD : 0 < D) (hR : 0 ≤ R)
    (μ_hi : Fin m → ℝ) (hμ : ∀ j, muMax (M j) ≤ μ_hi j) :
    (∀ j : Fin m, -Real.log (C_sec j) ≤ RHDirect.ArakelovCovolume.slope (M j)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      ∑ j : Fin m, (2 * (rk (M j) : ℝ) / D) * Real.log (C_sec j)) ∧
    (∀ j : Fin m, Real.log (SmallGeneratedCount (M j) R : ℝ) ≤
      (smallGenRank (M j) R : ℝ) * (max 0 (μ_hi j) + Real.log (1 + 2 * R))) ∧
    (∑ j : Fin m, Real.log (SmallGeneratedCount (M j) R : ℝ) ≤
      ∑ j : Fin m, (rk (M j) : ℝ) * (max 0 (μ_hi j) + Real.log (1 + 2 * R))) := by
  have hL3 := L3_hodge_covolume_bound E M hM0 s hsM hsli C_sec hCpos hnorm hD
  have hpt : ∀ j : Fin m, Real.log (SmallGeneratedCount (M j) R : ℝ) ≤
      (smallGenRank (M j) R : ℝ) * (max 0 (μ_hi j) + Real.log (1 + 2 * R)) := by
    intro j
    have hup := (small_generated_count_upper (M j) hR).2
    have hmax : max 0 (muMax (M j)) ≤ max 0 (μ_hi j) := max_le_max le_rfl (hμ j)
    have hrk_nn : (0 : ℝ) ≤ (smallGenRank (M j) R : ℝ) := Nat.cast_nonneg _
    exact hup.trans (mul_le_mul_of_nonneg_left (by linarith) hrk_nn)
  have hsum : ∑ j : Fin m, Real.log (SmallGeneratedCount (M j) R : ℝ) ≤
      ∑ j : Fin m, (rk (M j) : ℝ) * (max 0 (μ_hi j) + Real.log (1 + 2 * R)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hrk_le : (smallGenRank (M j) R : ℝ) ≤ (rk (M j) : ℝ) :=
      Nat.cast_le.mpr (smallGenRank_le_rk (M j) R)
    have hfac_nn : 0 ≤ max 0 (μ_hi j) + Real.log (1 + 2 * R) := by
      have h1 : 0 ≤ max (0 : ℝ) (μ_hi j) := le_max_left _ _
      have h2 : 0 ≤ Real.log (1 + 2 * R) := Real.log_nonneg (by linarith)
      linarith
    exact (hpt j).trans (mul_le_mul_of_nonneg_right hrk_le hfac_nn)
  exact ⟨hL3.2.2.1, hL3.2.2.2, hpt, hsum⟩

/-- **CM Hermitian Lattice & Exterior-Power `SmallGeneratedCount` Upper Bound**
on top of `Stage12SchurWeylLattices.CMHermLattice`:
bounds `cmSmallGenCount Λ R` and `cmExtPowSmallGenCount Λ hk1 hkr R` by rank and `muMax`. -/
theorem cm_small_generated_count_upper {d r : ℕ} (Λ : CMHermLattice d r)
    {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ r) {R : ℝ} (hR : 0 ≤ R) :
    Real.log (cmSmallGenCount Λ R : ℝ) ≤
      (2 * r : ℝ) * (max 0 (muMax Λ.euclLat) + Real.log (1 + 2 * R)) ∧
    Real.log (cmExtPowSmallGenCount Λ hk1 hkr R : ℝ) ≤
      (2 * Nat.choose r k : ℝ) *
        (max 0 (muMax (Λ.complexExtPow hk1 hkr).euclLat) + Real.log (1 + 2 * R)) := by
  have h1 := (small_generated_count_upper Λ.euclLat hR).2
  have h2 := (small_generated_count_upper (Λ.complexExtPow hk1 hkr).euclLat hR).2
  have hrk1 : (smallGenRank Λ.euclLat R : ℝ) ≤ (2 * r : ℝ) := by
    have hle := Nat.cast_le (α := ℝ).mpr (smallGenRank_le_rk Λ.euclLat R)
    rw [Λ.rk_euclLat] at hle
    exact_mod_cast hle
  have hrk2 : (smallGenRank (Λ.complexExtPow hk1 hkr).euclLat R : ℝ) ≤ (2 * Nat.choose r k : ℝ) := by
    have hle := Nat.cast_le (α := ℝ).mpr (smallGenRank_le_rk (Λ.complexExtPow hk1 hkr).euclLat R)
    rw [(Λ.complexExtPow hk1 hkr).rk_euclLat] at hle
    exact_mod_cast hle
  have hpos1 : 0 ≤ max 0 (muMax Λ.euclLat) + Real.log (1 + 2 * R) :=
    add_nonneg (le_max_left _ _) (Real.log_nonneg (by linarith))
  have hpos2 : 0 ≤ max 0 (muMax (Λ.complexExtPow hk1 hkr).euclLat) + Real.log (1 + 2 * R) :=
    add_nonneg (le_max_left _ _) (Real.log_nonneg (by linarith))
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hrk1 hpos1),
    h2.trans (mul_le_mul_of_nonneg_right hrk2 hpos2)⟩

/-- **Graded Hermitian Algebra `O(k^(d+1))` Upper Bound on `SmallGeneratedCount`**:
for any `A : GradedHermAlgebra d` whose maximal slope grows at most linearly `muMax (A.secLat k) ≤ slopeHi * k + c₀`,
we obtain the sharp polynomial-exponential upper bound matching `moriwaki_big_small_sections`:
`Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤ C_hi * (k : ℝ) ^ (d + 1)`. -/
theorem graded_small_generated_count_upper {d : ℕ} (A : GradedHermAlgebra d)
    (slopeHi c₀ : ℝ) (hslope : 0 ≤ slopeHi) (hc₀ : 0 ≤ c₀)
    (hmu : ∀ k : ℕ, 1 ≤ k → muMax (A.secLat k) ≤ slopeHi * (k : ℝ) + c₀) :
    ∃ C_hi : ℝ, 0 < C_hi ∧ ∀ k : ℕ, (hk : 1 ≤ k) →
      Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤ C_hi * (k : ℝ) ^ (d + 1) := by
  let C_hi : ℝ := A.rankHi * (slopeHi + c₀ + Real.log (1 + 2 * A.volConst) + 1)
  have hC_pos : 0 < C_hi := by
    have h1 : 0 < A.rankHi := lt_of_lt_of_le zero_lt_one A.rankHi_ge_one
    have h2 : 0 ≤ Real.log (1 + 2 * A.volConst) :=
      Real.log_nonneg (by linarith [A.volConst_pos])
    have h3 : 0 < slopeHi + c₀ + Real.log (1 + 2 * A.volConst) + 1 := by linarith
    exact mul_pos h1 h3
  refine ⟨C_hi, hC_pos, fun k hk => ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcnt_pos : (0 : ℝ) < (gradedSmallGeneratedCount A k hk : ℝ) := by
    have h1 : 1 ≤ gradedSmallGeneratedCount A k hk := by
      have h0 : 1 ≤ h0ArithStrict (A.secLat k) ((A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹) :=
        one_le_h0ArithStrict (A.secLat k) (inv_pos.mpr
          (mul_pos (lt_of_lt_of_le zero_lt_one A.bergConst_ge_one) (pow_pos (by positivity) _)))
      exact h0.trans (A.h0ArithStrict_le_smallSectionsCard hk)
    exact Nat.cast_pos.mpr h1
  have hle_lat : (gradedSmallGeneratedCount A k hk : ℝ) ≤
      (SmallGeneratedCount (A.secLat k) A.volConst : ℝ) :=
    Nat.cast_le.mpr (gradedSmallGeneratedCount_le_smallGeneratedCount_volConst A hk)
  have hlog1 : Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤
      Real.log (SmallGeneratedCount (A.secLat k) A.volConst : ℝ) :=
    Real.log_le_log hcnt_pos hle_lat
  have hlog2 := (small_generated_count_upper (A.secLat k) A.volConst_pos.le).2
  have hmax_le : max 0 (muMax (A.secLat k)) ≤ (slopeHi + c₀) * (k : ℝ) := by
    refine max_le (by positivity) ?_
    have h1 := hmu k hk
    nlinarith
  have hrk_le : (smallGenRank (A.secLat k) A.volConst : ℝ) ≤ A.rankHi * (k : ℝ) ^ d :=
    (Nat.cast_le.mpr (smallGenRank_le_rk (A.secLat k) A.volConst)).trans (A.rk_le_poly k hk)
  have hlog_v_nn : 0 ≤ Real.log (1 + 2 * A.volConst) :=
    Real.log_nonneg (by linarith [A.volConst_pos])
  have hfac_le : max 0 (muMax (A.secLat k)) + Real.log (1 + 2 * A.volConst) ≤
      (slopeHi + c₀ + Real.log (1 + 2 * A.volConst) + 1) * (k : ℝ) := by
    nlinarith
  have hfac_nn : 0 ≤ max 0 (muMax (A.secLat k)) + Real.log (1 + 2 * A.volConst) := by
    have : 0 ≤ max (0 : ℝ) (muMax (A.secLat k)) := le_max_left _ _
    linarith
  have hcomb : Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤
      (A.rankHi * (k : ℝ) ^ d) * ((slopeHi + c₀ + Real.log (1 + 2 * A.volConst) + 1) * (k : ℝ)) := by
    calc Real.log (gradedSmallGeneratedCount A k hk : ℝ)
        ≤ Real.log (SmallGeneratedCount (A.secLat k) A.volConst : ℝ) := hlog1
      _ ≤ (smallGenRank (A.secLat k) A.volConst : ℝ) *
            (max 0 (muMax (A.secLat k)) + Real.log (1 + 2 * A.volConst)) := hlog2
      _ ≤ (A.rankHi * (k : ℝ) ^ d) *
            (max 0 (muMax (A.secLat k)) + Real.log (1 + 2 * A.volConst)) :=
          mul_le_mul_of_nonneg_right hrk_le hfac_nn
      _ ≤ (A.rankHi * (k : ℝ) ^ d) *
            ((slopeHi + c₀ + Real.log (1 + 2 * A.volConst) + 1) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hfac_le (mul_nonneg (by linarith [A.rankHi_ge_one])
            (pow_nonneg hk_pos.le d))
  have hrhs : (A.rankHi * (k : ℝ) ^ d) *
      ((slopeHi + c₀ + Real.log (1 + 2 * A.volConst) + 1) * (k : ℝ)) =
      C_hi * (k : ℝ) ^ (d + 1) := by
    dsimp only [C_hi]
    rw [pow_succ']
    ring
  exact hcomb.trans_eq hrhs

end SmallGeneratedCountUpper

/-! ## Section 3: `small_sections_injective_of_self_intersection_bound` -/

section SmallSectionsInjective

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Ambient `ℤ`-submodule kernel of a restriction/evaluation map `φ : L →ₗ[ℤ] M`. -/
def vanishingKernel {L : Submodule ℤ E} {M : Submodule ℤ F} (φ : L →ₗ[ℤ] M) :
    Submodule ℤ E :=
  (LinearMap.ker φ).map L.subtype

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
lemma vanishingKernel_le {L : Submodule ℤ E} {M : Submodule ℤ F} (φ : L →ₗ[ℤ] M) :
    vanishingKernel φ ≤ L := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

instance discreteTopology_vanishingKernel {L : Submodule ℤ E} [DiscreteTopology L]
    {M : Submodule ℤ F} (φ : L →ₗ[ℤ] M) :
    DiscreteTopology (vanishingKernel φ) :=
  discreteTopology_of_le (vanishingKernel_le φ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
lemma mem_vanishingKernel_iff {L : Submodule ℤ E} {M : Submodule ℤ F} (φ : L →ₗ[ℤ] M)
    (x : L) : (x : E) ∈ vanishingKernel φ ↔ φ x = 0 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : x = y := Subtype.ext hyx.symm
    rw [hxy]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **First-Minimum Small-Section Injectivity**:
if `0 ≤ R` and `2 * R < lambda1 (vanishingKernel φ)` (or `vanishingKernel φ = ⊥`), then `φ` is
injective on the small-section ball `{x : L | ‖(x : E)‖ ≤ R}`. -/
theorem small_sections_injective_of_radius_lt_lambda1
    {L : Submodule ℤ E} [DiscreteTopology L] {M : Submodule ℤ F}
    (φ : L →ₗ[ℤ] M) {R : ℝ} (_hR : 0 ≤ R)
    (hgap : vanishingKernel φ = ⊥ ∨ 2 * R < lambda1 (vanishingKernel φ)) :
    Set.InjOn φ { x : L | ‖(x : E)‖ ≤ R } := by
  intro x₁ hx₁ x₂ hx₂ hφeq
  have hdiff_ker : ((x₁ - x₂ : L) : E) ∈ vanishingKernel φ := by
    rw [mem_vanishingKernel_iff]
    rw [map_sub, hφeq, sub_self]
  have hdiff_norm : ‖((x₁ - x₂ : L) : E)‖ ≤ 2 * R := by
    change ‖(x₁ : E) - (x₂ : E)‖ ≤ 2 * R
    calc ‖(x₁ : E) - (x₂ : E)‖ ≤ ‖(x₁ : E)‖ + ‖(x₂ : E)‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add hx₁ hx₂
      _ = 2 * R := by ring
  have hzero : ((x₁ - x₂ : L) : E) = 0 := by
    rcases hgap with hbot | hlt
    · rw [hbot, Submodule.mem_bot] at hdiff_ker
      exact hdiff_ker
    · by_contra hne
      have hlam := lambda1_le_norm (vanishingKernel φ) hdiff_ker hne
      linarith
  exact sub_eq_zero.mp (Subtype.ext hzero)

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Kernel-Slope Small-Section Injectivity**:
if `0 < R` and `muMax (vanishingKernel φ) < -Real.log (2 * R)`, then `φ` is injective on
`{x : L | ‖(x : E)‖ ≤ R}`. -/
theorem small_sections_injective_of_kernel_muMax_bound
    {L : Submodule ℤ E} [DiscreteTopology L] {M : Submodule ℤ F}
    (φ : L →ₗ[ℤ] M) {R : ℝ} (hR : 0 < R)
    (hmu : muMax (vanishingKernel φ) < -Real.log (2 * R)) :
    Set.InjOn φ { x : L | ‖(x : E)‖ ≤ R } := by
  by_cases hbot : vanishingKernel φ = ⊥
  · exact small_sections_injective_of_radius_lt_lambda1 φ hR.le (Or.inl hbot)
  · have hlam : 2 * R < lambda1 (vanishingKernel φ) := by
      have h1 := neg_log_lambda1_le_muMax (vanishingKernel φ) hbot
      have hlog : Real.log (2 * R) < Real.log (lambda1 (vanishingKernel φ)) := by linarith
      exact (Real.log_lt_log_iff (by positivity) (lambda1_pos _ hbot)).mp hlog
    exact small_sections_injective_of_radius_lt_lambda1 φ hR.le (Or.inr hlam)

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Divisible Bost-Slope Small-Section Injectivity**:
if the vanishing kernel `K = vanishingKernel φ` admits an injective `ℤ`-linear jet/intersection
map `ψ : K →ₗ[ℤ] J` with archimedean norm bound `‖ψ x‖ ≤ C * ‖x‖` and non-archimedean
divisibility `D ≥ 1` (`∀ x, ∃ y, ψ x = D • y`) satisfying the strict self-intersection / slope
budget `muMax J + Real.log C + Real.log (2 * R) < Real.log D`, then `φ` is injective on
`{x : L | ‖(x : E)‖ ≤ R}`. -/
theorem small_sections_injective_of_bost_divisible
    {L : Submodule ℤ E} [DiscreteTopology L] {M : Submodule ℤ F} {J : Submodule ℤ G}
    [DiscreteTopology J]
    (φ : L →ₗ[ℤ] M) (ψ : vanishingKernel φ →ₗ[ℤ] J) (C : ℝ) (D : ℕ) (hD : 0 < D)
    (hψ : Function.Injective ψ)
    (hC : ∀ x : vanishingKernel φ, ‖((ψ x : J) : G)‖ ≤ C * ‖(x : E)‖)
    (hDiv : ∀ x : vanishingKernel φ, ∃ y : J, ψ x = (D : ℤ) • y)
    {R : ℝ} (_hR : 0 < R)
    (hGap : muMax J + Real.log C + Real.log (2 * R) < Real.log (D : ℝ)) :
    Set.InjOn φ { x : L | ‖(x : E)‖ ≤ R } := by
  intro x₁ hx₁ x₂ hx₂ hφeq
  have hdiff_ker : ((x₁ - x₂ : L) : E) ∈ vanishingKernel φ := by
    rw [mem_vanishingKernel_iff, map_sub, hφeq, sub_self]
  have hdiff_norm : ‖((x₁ - x₂ : L) : E)‖ ≤ 2 * R := by
    change ‖(x₁ : E) - (x₂ : E)‖ ≤ 2 * R
    calc ‖(x₁ : E) - (x₂ : E)‖ ≤ ‖(x₁ : E)‖ + ‖(x₂ : E)‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add hx₁ hx₂
      _ = 2 * R := by ring
  by_contra hne
  let v : E := ((x₁ - x₂ : L) : E)
  have hv0 : v ≠ 0 := fun h => hne (sub_eq_zero.mp (Subtype.ext h))
  let V : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  have hVK : V ≤ vanishingKernel φ := Submodule.span_le.mpr (by rintro _ rfl; exact hdiff_ker)
  have : DiscreteTopology V := discreteTopology_of_le (hVK.trans (vanishingKernel_le φ))
  have hV0 : V ≠ ⊥ := by
    intro h0
    have hm : v ∈ V := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at hm
    exact hv0 hm
  let incl : V →ₗ[ℤ] vanishingKernel φ := Submodule.inclusion hVK
  let ψV : V →ₗ[ℤ] J := ψ.comp incl
  have hψV_inj : Function.Injective ψV := hψ.comp (Submodule.inclusion_injective hVK)
  have hψV_C : ∀ u : V, ‖((ψV u : J) : G)‖ ≤ C * ‖(u : E)‖ := fun u => hC (incl u)
  have hψV_Div : ∀ u : V, ∃ y : J, ψV u = (D : ℤ) • y := fun u => hDiv (incl u)
  have hBost := bost_slope_inequality_divisible V J hV0 ψV C D hD hψV_inj hψV_C hψV_Div
  have hV_slope : -Real.log (2 * R) ≤ RHDirect.ArakelovCovolume.slope V := by
    rw [slope_span_singleton hv0]
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    linarith [Real.log_le_log hv_pos hdiff_norm]
  linarith

/-- **Self-Intersection Restriction Datum (`SelfIntersectionRestrictionDatum`)**:
packages a section lattice `L ⊂ E`, a restriction/evaluation map `φ : L →ₗ[ℤ] M`,
an arithmetic self-intersection `selfInter : ℝ`, and a component intersection defect
`compInter : ℝ` together with the slope-drop inequality
`muMax (vanishingKernel φ) ≤ compInter - selfInter + err`. -/
structure SelfIntersectionRestrictionDatum
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] where
  L : Submodule ℤ E
  [discL : DiscreteTopology L]
  M : Submodule ℤ F
  [discM : DiscreteTopology M]
  φ : L →ₗ[ℤ] M
  selfInter : ℝ
  compInter : ℝ
  err : ℝ
  muMax_ker_le : muMax (vanishingKernel φ) ≤ compInter - selfInter + err

attribute [instance] SelfIntersectionRestrictionDatum.discL SelfIntersectionRestrictionDatum.discM

/-- **Main Theorem: `small_sections_injective_of_self_intersection_bound`**:
under the explicit self-intersection bound `compInter + err + Real.log (2 * R) < selfInter`,
the evaluation/restriction map `φ` is injective on all small sections `{x : L | ‖x‖ ≤ R}`. -/
theorem small_sections_injective_of_self_intersection_bound
    (S : SelfIntersectionRestrictionDatum E F) {R : ℝ} (hR : 0 < R)
    (hSI : S.compInter + S.err + Real.log (2 * R) < S.selfInter) :
    Set.InjOn S.φ { x : S.L | ‖(x : E)‖ ≤ R } := by
  refine small_sections_injective_of_kernel_muMax_bound S.φ hR ?_
  linarith [S.muMax_ker_le]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Full-Submodule Injectivity on `smallGenSubmodule L R` via Bost Vanishing**:
if `K = vanishingKernel φ` satisfies `covol (K ⊓ smallGenSubmodule L R) ≤ 1` and admits a
divisible map `ψ` to `J` with `muMax J + Real.log C < Real.log D`, then `φ` is injective on
the ENTIRE `ℤ`-submodule generated by small sections `{v ∈ L | ‖v‖ ≤ R}`. -/
theorem small_generated_injective_of_self_intersection_bound
    {L : Submodule ℤ E} [DiscreteTopology L] {M : Submodule ℤ F} {J : Submodule ℤ G}
    [DiscreteTopology J]
    (φ : L →ₗ[ℤ] M) {R : ℝ}
    (ψ : (vanishingKernel φ ⊓ smallGenSubmodule L R : Submodule ℤ E) →ₗ[ℤ] J)
    (C : ℝ) (D : ℕ) (hD : 0 < D)
    (hψ : Function.Injective ψ)
    (hC : ∀ x : (vanishingKernel φ ⊓ smallGenSubmodule L R : Submodule ℤ E),
      ‖((ψ x : J) : G)‖ ≤ C * ‖(x : E)‖)
    (hDiv : ∀ x : (vanishingKernel φ ⊓ smallGenSubmodule L R : Submodule ℤ E),
      ∃ y : J, ψ x = (D : ℤ) • y)
    (hCov : covol (vanishingKernel φ ⊓ smallGenSubmodule L R) ≤ 1)
    (hStrict : muMax J + Real.log C < Real.log (D : ℝ)) :
    ∀ x₁ x₂ : L, (x₁ : E) ∈ smallGenSubmodule L R → (x₂ : E) ∈ smallGenSubmodule L R →
      φ x₁ = φ x₂ → x₁ = x₂ := by
  let K : Submodule ℤ E := vanishingKernel φ ⊓ smallGenSubmodule L R
  have hKL : K ≤ L := inf_le_left.trans (vanishingKernel_le φ)
  have : DiscreteTopology K := discreteTopology_of_le hKL
  have hvan : K = ⊥ ∧ rk K = 0 :=
    bost_vanishing_criterion K J ψ C D hD hψ hC hDiv hCov hStrict
  intro x₁ x₂ hx₁ hx₂ hφeq
  have hmem1 : ((x₁ - x₂ : L) : E) ∈ vanishingKernel φ := by
    rw [mem_vanishingKernel_iff, map_sub, hφeq, sub_self]
  have hmem2 : ((x₁ - x₂ : L) : E) ∈ smallGenSubmodule L R :=
    (smallGenSubmodule L R).sub_mem hx₁ hx₂
  have hmemK : ((x₁ - x₂ : L) : E) ∈ K := ⟨hmem1, hmem2⟩
  rw [hvan.1, Submodule.mem_bot] at hmemK
  exact sub_eq_zero.mp (Subtype.ext hmemK)

/-- **Irreducible-Component Restriction System (`ComponentRestrictionSystem`)**:
models a section lattice `L ⊂ E` restricted to `c` irreducible components `i : Fin c` via
`res i : L →ₗ[ℤ] M i`, with self-intersection / slope-drop bounds along the joint kernel. -/
structure ComponentRestrictionSystem (c : ℕ)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Fin c → Type*) [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)] where
  L : Submodule ℤ E
  [discL : DiscreteTopology L]
  M : ∀ i, Submodule ℤ (F i)
  [discM : ∀ i, DiscreteTopology (M i)]
  res : ∀ i, L →ₗ[ℤ] M i
  jointSelfInter : ℝ
  jointCompInter : ℝ
  muMax_jointKer_le :
    muMax (L ⊓ ⨅ i : Fin c, vanishingKernel (res i)) ≤ jointCompInter - jointSelfInter

attribute [instance] ComponentRestrictionSystem.discL ComponentRestrictionSystem.discM

/-- **Component-Wise Small-Section Injectivity**:
if the joint arithmetic self-intersection strictly exceeds `jointCompInter + Real.log (2 * R)`,
then the joint component restriction map `x ↦ (fun i => res i x)` is injective on `{x : L | ‖x‖ ≤ R}`. -/
theorem small_sections_injective_on_components {c : ℕ}
    {F : Fin c → Type*} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)]
    (sys : ComponentRestrictionSystem c E F) {R : ℝ} (_hR : 0 < R)
    (hSI : sys.jointCompInter + Real.log (2 * R) < sys.jointSelfInter) :
    Set.InjOn (fun x : sys.L => fun i : Fin c => sys.res i x)
      { x : sys.L | ‖(x : E)‖ ≤ R } := by
  let K : Submodule ℤ E := sys.L ⊓ ⨅ i : Fin c, vanishingKernel (sys.res i)
  have hKL : K ≤ sys.L := inf_le_left
  have : DiscreteTopology K := discreteTopology_of_le hKL
  intro x₁ hx₁ x₂ hx₂ heq
  have hdiff_ker : ((x₁ - x₂ : sys.L) : E) ∈ K := by
    refine ⟨(x₁ - x₂).2, ?_⟩
    change ((x₁ - x₂ : sys.L) : E) ∈ ⨅ i : Fin c, vanishingKernel (sys.res i)
    rw [Submodule.mem_iInf]
    intro i
    have h_i : sys.res i x₁ = sys.res i x₂ := congrFun heq i
    rw [mem_vanishingKernel_iff, map_sub, h_i, sub_self]
  have hdiff_norm : ‖((x₁ - x₂ : sys.L) : E)‖ ≤ 2 * R := by
    change ‖(x₁ : E) - (x₂ : E)‖ ≤ 2 * R
    calc ‖(x₁ : E) - (x₂ : E)‖ ≤ ‖(x₁ : E)‖ + ‖(x₂ : E)‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add hx₁ hx₂
      _ = 2 * R := by ring
  by_contra hne
  let v : E := ((x₁ - x₂ : sys.L) : E)
  have hv0 : v ≠ 0 := fun h => hne (sub_eq_zero.mp (Subtype.ext h))
  let V : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  have hVK : V ≤ K := Submodule.span_le.mpr (by rintro _ rfl; exact hdiff_ker)
  have : DiscreteTopology V := discreteTopology_of_le (hVK.trans hKL)
  have hV0 : V ≠ ⊥ := by
    intro h0
    have hm : v ∈ V := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at hm
    exact hv0 hm
  have hslope : -Real.log (2 * R) ≤ RHDirect.ArakelovCovolume.slope V := by
    rw [slope_span_singleton hv0]
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    linarith [Real.log_le_log hv_pos hdiff_norm]
  have hmu : RHDirect.ArakelovCovolume.slope V ≤ muMax K := slope_le_muMax K V hVK hV0
  linarith [sys.muMax_jointKer_le]

/-- **Graded Hermitian Algebra Restriction Injectivity & Counting Upper Bound**:
if `φ : A.secLat k →ₗ[ℤ] M` has `muMax (vanishingKernel φ) < -Real.log (2 * A.volConst)` and
operator norm bound `‖(φ s : F)‖ ≤ C_op * ‖(s : A.secSpace k)‖` (`0 ≤ C_op`), then:
1. `φ` is injective on `A.smallSectionsSet k`;
2. `gradedSmallGeneratedCount A k hk ≤ h0Arith M (C_op * A.volConst)`;
3. `Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤ (rk M : ℝ) * (max 0 (muMax M) + Real.log (1 + 2 * C_op * A.volConst))`. -/
theorem graded_small_sections_injective_and_count_upper {d : ℕ} (A : GradedHermAlgebra d)
    {k : ℕ} (hk : 1 ≤ k) {M : Submodule ℤ F} [DiscreteTopology M]
    (φ : A.secLat k →ₗ[ℤ] M) (C_op : ℝ) (hC : 0 ≤ C_op)
    (hφ_bound : ∀ s : A.secLat k, ‖((φ s : M) : F)‖ ≤ C_op * ‖(s : A.secSpace k)‖)
    (hmu : muMax (vanishingKernel φ) < -Real.log (2 * A.volConst)) :
    Set.InjOn φ (A.smallSectionsSet k) ∧
    gradedSmallGeneratedCount A k hk ≤ h0Arith M (C_op * A.volConst) ∧
    Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤
      (rk M : ℝ) * (max 0 (muMax M) + Real.log (1 + 2 * C_op * A.volConst)) := by
  have hsub_ball : A.smallSectionsSet k ⊆ { s : A.secLat k | ‖(s : A.secSpace k)‖ ≤ A.volConst } := by
    intro s hs
    have h1 := A.norm_le_vol_supNorm k hk s.1
    have h2 : A.supNorm k s.1 < 1 := hs
    exact h1.trans (mul_le_of_le_one_right A.volConst_pos.le h2.le)
  have hinj_ball := small_sections_injective_of_kernel_muMax_bound φ A.volConst_pos hmu
  have hinj : Set.InjOn φ (A.smallSectionsSet k) := hinj_ball.mono hsub_ball
  let f : A.secLat k → F := fun s => ((φ s : M) : F)
  have hf_inj : Set.InjOn f (A.smallSectionsSet k) := by
    intro s₁ hs₁ s₂ hs₂ heq
    exact hinj hs₁ hs₂ (Subtype.ext heq)
  have hf_img : f '' A.smallSectionsSet k ⊆
      (M : Set F) ∩ Metric.closedBall (0 : F) (C_op * A.volConst) := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨(φ s).2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hφ_bound s
    have h2 : ‖(s : A.secSpace k)‖ ≤ A.volConst := hsub_ball hs
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
  have hfin_M := lattice_inter_closedBall_finite M (C_op * A.volConst)
  have hcount : gradedSmallGeneratedCount A k hk ≤ h0Arith M (C_op * A.volConst) := by
    unfold gradedSmallGeneratedCount GradedHermAlgebra.smallSectionsCard h0Arith
    calc (A.smallSections_finite hk).toFinset.card
        = (A.smallSectionsSet k).ncard := (Set.ncard_eq_toFinset_card _ _).symm
      _ = (f '' A.smallSectionsSet k).ncard := (hf_inj.ncard_image).symm
      _ ≤ ((M : Set F) ∩ Metric.closedBall (0 : F) (C_op * A.volConst)).ncard :=
          Set.ncard_le_ncard hf_img hfin_M
  have hcnt_pos : (0 : ℝ) < (gradedSmallGeneratedCount A k hk : ℝ) := by
    have h0 : 1 ≤ h0ArithStrict (A.secLat k) ((A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹) :=
      one_le_h0ArithStrict (A.secLat k) (inv_pos.mpr
        (mul_pos (lt_of_lt_of_le zero_lt_one A.bergConst_ge_one) (pow_pos (by positivity) _)))
    exact Nat.cast_pos.mpr (h0.trans (A.h0ArithStrict_le_smallSectionsCard hk))
  have hlog1 : Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤
      Real.log (SmallGeneratedCount M (C_op * A.volConst) : ℝ) := by
    rw [smallGeneratedCount_eq_h0Arith]
    exact Real.log_le_log hcnt_pos (Nat.cast_le.mpr hcount)
  have hup := (small_generated_count_upper M (mul_nonneg hC A.volConst_pos.le)).2
  have hrk_le : (smallGenRank M (C_op * A.volConst) : ℝ) ≤ (rk M : ℝ) :=
    Nat.cast_le.mpr (smallGenRank_le_rk M (C_op * A.volConst))
  have hfac_nn : 0 ≤ max 0 (muMax M) + Real.log (1 + 2 * (C_op * A.volConst)) :=
    add_nonneg (le_max_left _ _) (Real.log_nonneg (by nlinarith [A.volConst_pos]))
  have hlog2 : Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤
      (rk M : ℝ) * (max 0 (muMax M) + Real.log (1 + 2 * C_op * A.volConst)) := by
    calc Real.log (gradedSmallGeneratedCount A k hk : ℝ)
        ≤ Real.log (SmallGeneratedCount M (C_op * A.volConst) : ℝ) := hlog1
      _ ≤ (smallGenRank M (C_op * A.volConst) : ℝ) *
            (max 0 (muMax M) + Real.log (1 + 2 * (C_op * A.volConst))) := hup
      _ ≤ (rk M : ℝ) * (max 0 (muMax M) + Real.log (1 + 2 * (C_op * A.volConst))) :=
          mul_le_mul_of_nonneg_right hrk_le hfac_nn
      _ = (rk M : ℝ) * (max 0 (muMax M) + Real.log (1 + 2 * C_op * A.volConst)) := by
          ring_nf
  exact ⟨hinj, hcount, hlog2⟩

end SmallSectionsInjective

/-! ## Section 4: `line_of_large_degree_of_use` — Extracting Rank-1 Sublattices of Large Arakelov Degree -/

section LineOfLargeDegree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Saturated Rank-1 Line Extraction via `Stage10GeometryOfNumbers.hermite_minkowski_bound_all_dims`**:
for ANY nonzero discrete lattice `L ⊂ E`, there exists a nonzero vector `v ∈ L` and its
saturated rank-1 sublattice `ℓ = saturation L (span ℤ {v})` satisfying:
1. `IsSaturated L ℓ`, `rk ℓ = 1`, `ℓ ≠ ⊥`, `v ∈ ℓ`, `‖v‖ = lambda1 L`,
2. `ArakelovCovolume.slope L - (1 / 2) * Real.log (rk L) - Real.log (2 / √Real.pi) ≤ degAr ℓ`,
3. `ArakelovCovolume.slope L - (1 / 2) * Real.log (rk L) ≤ degAr ℓ`,
4. Exact Arakelov degree split `degAr L = degAr ℓ + degAr (quotLat L ℓ)` and `rk L = 1 + rk (quotLat L ℓ)`. -/
theorem line_of_large_degree_of_hermite_minkowski
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ (v : E) (ℓ : Submodule ℤ E),
      v ∈ L ∧ v ≠ 0 ∧ ‖v‖ = lambda1 L ∧
      ℓ ≤ L ∧ IsSaturated L ℓ ∧ ℓ ≠ ⊥ ∧ rk ℓ = 1 ∧ v ∈ ℓ ∧
      RHDirect.ArakelovCovolume.slope L - (1 / 2) * Real.log (rk L : ℝ) -
          Real.log (2 / √Real.pi) ≤ degAr ℓ ∧
      RHDirect.ArakelovCovolume.slope L - (1 / 2) * Real.log (rk L : ℝ) ≤ degAr ℓ ∧
      degAr L = degAr ℓ + degAr (quotLat L ℓ) ∧
      rk L = 1 + rk (quotLat L ℓ) := by
  obtain ⟨v, hvL, hv0, hv_norm⟩ := exists_norm_eq_lambda1 L hL0
  let N : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ rfl; exact hvL)
  let ℓ : Submodule ℤ E := saturation L N
  have hsat : IsSaturated L ℓ := isSaturated_saturation hNL
  have hℓL : ℓ ≤ L := saturation_le L N
  have : DiscreteTopology N := discreteTopology_of_le hNL
  have : DiscreteTopology ℓ := discreteTopology_of_le hℓL
  have hv_mem_N : v ∈ N := Submodule.subset_span rfl
  have hv_mem_ℓ : v ∈ ℓ := le_saturation hNL hv_mem_N
  have hℓ0 : ℓ ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hv_mem_ℓ
    exact hv0 hv_mem_ℓ
  have hrk_N : rk N = 1 := by
    unfold rk
    rw [finrank_int_eq_finrank_real_span N]
    have hsp : Submodule.span ℝ (N : Set E) = Submodule.span ℝ ({v} : Set E) := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        intro x hxN
        have hsub : (N : Set E) ⊆ (Submodule.span ℝ ({v} : Set E) : Set E) := by
          intro y hy
          change y ∈ Submodule.span ℤ ({v} : Set E) at hy
          rw [Submodule.mem_span_singleton] at hy
          rcases hy with ⟨a, rfl⟩
          rw [← Int.cast_smul_eq_zsmul ℝ a]
          exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        exact hsub hxN
      · exact Submodule.span_mono (by rintro _ rfl; exact hv_mem_N)
    rw [hsp]
    exact finrank_span_singleton hv0
  have hrk_ℓ : rk ℓ = 1 := (rk_saturation hNL).trans hrk_N
  have hdeg_N_le : degAr N ≤ degAr ℓ := (covol_saturation_le hNL).2
  have hdeg_N : degAr N = -Real.log (lambda1 L) := by
    unfold degAr
    rw [covol_span_singleton hv0, hv_norm]
  have hstage10_herm :
      RHDirect.ArakelovCovolume.slope L - (1 / 2) * Real.log (rk L : ℝ) -
          Real.log (2 / √Real.pi) ≤ -Real.log (lambda1 L) := by
    obtain ⟨Λ, hDiscΛ, hIsZΛ, hcov, _, _, hsucc⟩ := exists_isometric_euclidean_lattice L
    have hr : 0 < rk L := rk_pos_of_ne_bot L hL0
    have hhm := hermite_minkowski_bound_all_dims hr Λ
    have hlam_eq : RHDirect.Stage10GeometryOfNumbers.successiveMinimum
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1) Λ ⟨0, hr⟩ = lambda1 L := by
      rw [← hsucc ⟨0, hr⟩, succMin_zero_eq_lambda1 L hL0]
    have hω_eq : (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1)).toReal =
        unitBallVol (rk L) := unitBallVolume_eq hr
    rw [hlam_eq, hcov, hω_eq] at hhm
    have hrpos : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr hr
    have hlam_pos : 0 < lambda1 L := lambda1_pos L hL0
    have hω_pos : 0 < unitBallVol (rk L) := unitBallVol_pos (rk L)
    have hcov_pos : 0 < covol L := covol_pos L
    have hlog := Real.log_le_log (pow_pos hlam_pos 2) hhm
    rw [Real.log_pow, Real.log_mul (div_pos (by norm_num) (Real.rpow_pos_of_pos hω_pos _)).ne'
      (Real.rpow_pos_of_pos hcov_pos _).ne',
      Real.log_div (by norm_num) (Real.rpow_pos_of_pos hω_pos _).ne',
      Real.log_rpow hω_pos, Real.log_rpow hcov_pos] at hlog
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h4] at hlog
    have hω_ge := log_unitBallVol_ge hr
    have hslope_eq : RHDirect.ArakelovCovolume.slope L = -Real.log (covol L) / (rk L : ℝ) := rfl
    have hlogC : Real.log (2 / √Real.pi) = Real.log 2 - (1 / 2) * Real.log Real.pi := by
      rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).ne',
        Real.log_sqrt Real.pi_pos.le]
      ring
    have hdivω : (2 : ℝ) / (rk L : ℝ) * Real.log (unitBallVol (rk L)) ≥
        Real.log Real.pi - Real.log (rk L : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hω_ge (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrpos.le)
      have hsimp : (2 / (rk L : ℝ)) * (((rk L : ℝ) / 2) * Real.log Real.pi -
          ((rk L : ℝ) / 2) * Real.log (rk L : ℝ)) = Real.log Real.pi - Real.log (rk L : ℝ) := by
        field_simp [hrpos.ne']
      linarith
    have hdivC : (2 : ℝ) / (rk L : ℝ) * Real.log (covol L) =
        -2 * RHDirect.ArakelovCovolume.slope L := by
      rw [hslope_eq]
      ring
    rw [hlogC]
    linarith
  have hsharp : RHDirect.ArakelovCovolume.slope L - (1 / 2) * Real.log (rk L : ℝ) ≤
      -Real.log (lambda1 L) :=
    slope_sub_half_log_rk_le_neg_log_lambda1 L hL0
  have hsplit_deg : degAr L = degAr ℓ + degAr (quotLat L ℓ) := degAr_eq_add_quotLat hsat
  have hsplit_rk : rk L = 1 + rk (quotLat L ℓ) := by
    have h1 := rk_add_quotLat hsat
    rwa [hrk_ℓ] at h1
  refine ⟨v, ℓ, hvL, hv0, hv_norm, hℓL, hsat, hℓ0, hrk_ℓ, hv_mem_ℓ, ?_, ?_, hsplit_deg, hsplit_rk⟩
  · linarith
  · linarith

/-- **Counting-Supply Line Extraction (`line_of_large_degree_of_counting_supply`)**:
purely from a small-section counting supply `Real.exp (T * rk L) ≤ (SmallGeneratedCount L R : ℝ)`
with `0 < R` and `0 < T`, our upper bound `small_generated_count_upper_lambda1` forces
`lambda1 L ≤ 2 * R / (Real.exp T - 1)`, yielding a saturated rank-1 sublattice `ℓ ≤ L`
generated by a small section `v ∈ L \ {0}` of controlled large Arakelov degree:
`Real.log (Real.exp T - 1) - Real.log (2 * R) ≤ degAr ℓ`. -/
theorem line_of_large_degree_of_counting_supply
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hsupply : Real.exp (T * (rk L : ℝ)) ≤ (SmallGeneratedCount L R : ℝ)) :
    ∃ (v : E) (ℓ : Submodule ℤ E),
      v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ 2 * R / (Real.exp T - 1) ∧
      ℓ ≤ L ∧ IsSaturated L ℓ ∧ ℓ ≠ ⊥ ∧ rk ℓ = 1 ∧ v ∈ ℓ ∧
      Real.log (Real.exp T - 1) - Real.log (2 * R) ≤ degAr ℓ := by
  have hr_pos : 0 < rk L := rk_pos_of_ne_bot L hL0
  have hrposR : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr hr_pos
  have hexp_gt1 : 1 < Real.exp T := Real.one_lt_exp_iff.mpr hT
  have hden_pos : 0 < Real.exp T - 1 := sub_pos.mpr hexp_gt1
  have hne_gen : smallGenSubmodule L R ≠ ⊥ := by
    intro hbot
    have hcnt : SmallGeneratedCount L R = 1 := smallGeneratedCount_eq_one_of_bot L hR.le hbot
    rw [hcnt, Nat.cast_one] at hsupply
    have h1 : 1 < Real.exp (T * (rk L : ℝ)) := Real.one_lt_exp_iff.mpr (mul_pos hT hrposR)
    linarith
  have hlamL_pos : 0 < lambda1 L := lambda1_pos L hL0
  have hbase_ge1 : 1 ≤ 1 + 2 * R / lambda1 L := by
    have : 0 ≤ 2 * R / lambda1 L := div_nonneg (by positivity) hlamL_pos.le
    linarith
  have hpack := (small_generated_count_upper_lambda1 L hR.le hne_gen).2
  have hpow_le : (1 + 2 * R / lambda1 L) ^ (smallGenRank L R) ≤
      (1 + 2 * R / lambda1 L) ^ (rk L) :=
    pow_le_pow_right₀ hbase_ge1 (smallGenRank_le_rk L R)
  have hcomb : (Real.exp T) ^ (rk L) ≤ (1 + 2 * R / lambda1 L) ^ (rk L) := by
    have hpow_exp : (Real.exp T) ^ (rk L) = Real.exp (T * (rk L : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hpow_exp]
    exact hsupply.trans (hpack.trans hpow_le)
  have hbase_le : Real.exp T ≤ 1 + 2 * R / lambda1 L := by
    by_contra hlt
    push Not at hlt
    have h1 : (1 + 2 * R / lambda1 L) ^ (rk L) < (Real.exp T) ^ (rk L) :=
      pow_lt_pow_left₀ hlt (by linarith) hr_pos.ne'
    linarith
  have hlam_le : lambda1 L ≤ 2 * R / (Real.exp T - 1) := by
    have h1 : Real.exp T - 1 ≤ 2 * R / lambda1 L := by linarith
    have h2 : (Real.exp T - 1) * lambda1 L ≤ 2 * R := (le_div_iff₀ hlamL_pos).mp h1
    exact (le_div_iff₀ hden_pos).mpr (by linarith)
  obtain ⟨v, hvL, hv0, hv_norm⟩ := exists_norm_eq_lambda1 L hL0
  have hv_le : ‖v‖ ≤ 2 * R / (Real.exp T - 1) := hv_norm.symm ▸ hlam_le
  let N : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ rfl; exact hvL)
  let ℓ : Submodule ℤ E := saturation L N
  have hℓL : ℓ ≤ L := saturation_le L N
  have hsat : IsSaturated L ℓ := isSaturated_saturation hNL
  have hv_mem_ℓ : v ∈ ℓ := le_saturation hNL (Submodule.subset_span rfl)
  have hℓ0 : ℓ ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hv_mem_ℓ
    exact hv0 hv_mem_ℓ
  have : DiscreteTopology N := discreteTopology_of_le hNL
  have : DiscreteTopology ℓ := discreteTopology_of_le hℓL
  have hrk_N : rk N = 1 := by
    unfold rk
    rw [finrank_int_eq_finrank_real_span N]
    have hsp : Submodule.span ℝ (N : Set E) = Submodule.span ℝ ({v} : Set E) := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        intro x hxN
        have hx' : x ∈ Submodule.span ℤ ({v} : Set E) := hxN
        rw [Submodule.mem_span_singleton] at hx'
        rcases hx' with ⟨a, rfl⟩
        rw [← Int.cast_smul_eq_zsmul ℝ a]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.span_mono (by rintro _ rfl; exact Submodule.subset_span rfl)
    rw [hsp]
    exact finrank_span_singleton hv0
  have hrk_ℓ : rk ℓ = 1 := (rk_saturation hNL).trans hrk_N
  have hdeg_ge : Real.log (Real.exp T - 1) - Real.log (2 * R) ≤ degAr ℓ := by
    have hcov_le : covol ℓ ≤ covol N := (covol_saturation_le hNL).1
    have hcov_N : covol N = ‖v‖ := covol_span_singleton hv0
    have hcov_bound : covol ℓ ≤ 2 * R / (Real.exp T - 1) :=
      hcov_le.trans (hcov_N.symm ▸ hv_le)
    have hlog := Real.log_le_log (covol_pos ℓ) hcov_bound
    rw [Real.log_div (by positivity) hden_pos.ne'] at hlog
    unfold degAr
    linarith
  exact ⟨v, ℓ, hvL, hv0, hv_le, hℓL, hsat, hℓ0, hrk_ℓ, hv_mem_ℓ, hdeg_ge⟩

/-- **MAIN THEOREM: `line_of_large_degree_of_use`**:
given any graded Hermitian algebra `A : GradedHermAlgebra d` (`d ≥ 1`) with Moriwaki bigness
`0 < A.volAr` (from `Stage12SchurWeylLattices.moriwaki_big_small_sections`), we extract for all
sufficiently large degrees `k ≥ K₀` a nonzero strictly small section `s ∈ A.smallSectionsSet k`
generating a **saturated rank-1 sublattice `ℓ ≤ A.secLat k`** of linearly growing Arakelov degree
`c_deg * k ≤ degAr ℓ = ArakelovCovolume.slope ℓ`. -/
theorem line_of_large_degree_of_use {d : ℕ} (A : GradedHermAlgebra d) (hbig : 0 < A.volAr) :
    ∃ c_deg : ℝ, 0 < c_deg ∧ ∃ K₀ : ℕ, ∃ _hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (_hk : K₀ ≤ k) →
        ∃ (s : A.secLat k) (ℓ : Submodule ℤ (A.secSpace k)),
          s ≠ 0 ∧ A.supNorm k s.1 < 1 ∧
          ℓ ≤ A.secLat k ∧ IsSaturated (A.secLat k) ℓ ∧ ℓ ≠ ⊥ ∧ rk ℓ = 1 ∧
          (s : A.secSpace k) ∈ ℓ ∧ c_deg * (k : ℝ) ≤ degAr ℓ ∧
          RHDirect.ArakelovCovolume.slope ℓ = degAr ℓ := by
  obtain ⟨c₀, hc₀, K₁, hK₁, hmori⟩ := moriwaki_big_small_sections A hbig
  let c_deg : ℝ := c₀ / (2 * A.rankHi)
  have hrank_pos : 0 < A.rankHi := lt_of_lt_of_le zero_lt_one A.rankHi_ge_one
  have hc_deg_pos : 0 < c_deg := div_pos hc₀ (by positivity)
  have hberg_pos : (0 : ℝ) < A.bergConst := lt_of_lt_of_le zero_lt_one A.bergConst_ge_one
  have htend_lin : Tendsto (fun k : ℕ => c_deg * (k : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hc_deg_pos tendsto_natCast_atTop_atTop
  have hlog_poly_tend : Tendsto (fun k : ℕ =>
      Real.log (2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2) / (k : ℝ))
      atTop (𝓝 0) := by
    have h1 : ∀ k : ℕ, 1 ≤ k →
        0 ≤ Real.log (2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2) := by
      intro k _
      apply Real.log_nonneg
      have hterm_nn : 0 ≤ 2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) :=
        mul_nonneg (by linarith [A.volConst_pos]) (add_nonneg (mul_nonneg hberg_pos.le (pow_nonneg (by positivity) _)) zero_le_one)
      linarith
    have h2 : ∀ k : ℕ, 1 ≤ k →
        Real.log (2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2) ≤
          ((A.bergExp : ℝ) + 1) * Real.log ((k : ℝ) + 1) +
            Real.log (2 * A.volConst * (A.bergConst + 1) + 2) := by
      intro k _
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
      have hpow1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ A.bergExp := one_le_pow₀ hk1
      have hle_prod : 2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2 ≤
          ((k : ℝ) + 1) ^ A.bergExp * (2 * A.volConst * (A.bergConst + 1) + 2) := by
        nlinarith [A.volConst_pos, hberg_pos]
      have hpos_lhs : 0 < 2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2 := by
        have : 0 ≤ 2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) :=
          mul_nonneg (by linarith [A.volConst_pos]) (add_nonneg (mul_nonneg hberg_pos.le (pow_nonneg (by positivity) _)) zero_le_one)
        linarith
      have hpos_rhs : 0 < 2 * A.volConst * (A.bergConst + 1) + 2 := by
        have : 0 ≤ 2 * A.volConst * (A.bergConst + 1) :=
          mul_nonneg (by linarith [A.volConst_pos]) (by linarith [hberg_pos])
        linarith
      have hlog_le := Real.log_le_log hpos_lhs hle_prod
      rw [Real.log_mul (pow_pos (by positivity) _).ne' hpos_rhs.ne', Real.log_pow] at hlog_le
      have hlog_nn : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hk1
      linarith
    have hdiv_tend : Tendsto (fun k : ℕ =>
        (((A.bergExp : ℝ) + 1) * Real.log ((k : ℝ) + 1) +
          Real.log (2 * A.volConst * (A.bergConst + 1) + 2)) / (k : ℝ)) atTop (𝓝 0) := by
      have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
        simpa [pow_one, one_mul, add_zero] using
          Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero
      have hlog_k1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        hlog_div.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have hinv : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have hratio : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
        have hadd : Tendsto (fun k : ℕ => (1 : ℝ) + (k : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add hinv
        rw [add_zero] at hadd
        refine hadd.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [hk0]
      have hlog_k : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 0) := by
        have hprod := hlog_k1.mul hratio
        rw [zero_mul] at hprod
        refine hprod.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hk1]
      have hC : Tendsto (fun k : ℕ =>
          Real.log (2 * A.volConst * (A.bergConst + 1) + 2) * (k : ℝ)⁻¹) atTop (𝓝 0) := by
        simpa [mul_zero] using hinv.const_mul (Real.log (2 * A.volConst * (A.bergConst + 1) + 2))
      have hsum := (hlog_k.const_mul ((A.bergExp : ℝ) + 1)).add hC
      simp only [mul_zero, add_zero] at hsum
      exact hsum.congr fun k => by ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv_tend ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with k hk
      exact div_nonneg (h1 k hk) (Nat.cast_nonneg k)
    · filter_upwards [eventually_ge_atTop 1] with k hk
      exact div_le_div_of_nonneg_right (h2 k hk) (Nat.cast_nonneg k)
  have hmem_log := (Metric.tendsto_atTop.mp hlog_poly_tend) c_deg hc_deg_pos
  have hmem_lin := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp htend_lin) (Real.log (4 * A.volConst + 2)))
  let K₀ : ℕ := max K₁ (max hmem_log.choose hmem_lin.choose)
  have hK₀ : 1 ≤ K₀ := le_trans hK₁ (le_max_left _ _)
  refine ⟨c_deg, hc_deg_pos, K₀, hK₀, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans hK₀ hk
  have hkK₁ : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkLog : hmem_log.choose ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkLin : hmem_lin.choose ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  let L := A.secLat k
  have hL0 : L ≠ ⊥ := A.secLat_ne_bot k hk1
  let T : ℝ := (c₀ / A.rankHi) * (k : ℝ)
  have hT_pos : 0 < T := mul_pos (div_pos hc₀ hrank_pos) hk_pos
  have hT_eq : T = 2 * (c_deg * (k : ℝ)) := by
    dsimp only [T, c_deg]; ring
  have hsupply : Real.exp (T * (rk L : ℝ)) ≤ (SmallGeneratedCount L A.volConst : ℝ) := by
    have hrk_le := A.rk_le_poly k hk1
    have hmul : T * (rk L : ℝ) ≤ c₀ * (k : ℝ) ^ (d + 1) := by
      have h1 : T * (rk L : ℝ) ≤ T * (A.rankHi * (k : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hrk_le hT_pos.le
      have h2 : T * (A.rankHi * (k : ℝ) ^ d) = c₀ * (k : ℝ) ^ (d + 1) := by
        dsimp only [T]
        rw [pow_succ']
        field_simp [hrank_pos.ne']
      exact h1.trans_eq h2
    have hm_log := hmori k hkK₁
    have hle_cnt : (gradedSmallGeneratedCount A k hk1 : ℝ) ≤
        (SmallGeneratedCount L A.volConst : ℝ) :=
      Nat.cast_le.mpr (gradedSmallGeneratedCount_le_smallGeneratedCount_volConst A hk1)
    have hcnt_pos : (0 : ℝ) < (gradedSmallGeneratedCount A k hk1 : ℝ) := by
      have h0 : 1 ≤ h0ArithStrict L ((A.bergConst * ((k : ℝ) + 1) ^ A.bergExp)⁻¹) :=
        one_le_h0ArithStrict L (inv_pos.mpr (mul_pos hberg_pos (pow_pos (by positivity) _)))
      exact Nat.cast_pos.mpr (h0.trans (A.h0ArithStrict_le_smallSectionsCard hk1))
    have hexp_le : Real.exp (c₀ * (k : ℝ) ^ (d + 1)) ≤ (gradedSmallGeneratedCount A k hk1 : ℝ) := by
      calc Real.exp (c₀ * (k : ℝ) ^ (d + 1))
          ≤ Real.exp (Real.log (gradedSmallGeneratedCount A k hk1 : ℝ)) :=
            Real.exp_le_exp.mpr hm_log
        _ = (gradedSmallGeneratedCount A k hk1 : ℝ) := Real.exp_log hcnt_pos
    exact (Real.exp_le_exp.mpr hmul).trans (hexp_le.trans hle_cnt)
  obtain ⟨v, ℓ, hvL, hv0, hv_norm, hℓL, hsat, hℓ0, hrk_ℓ, hv_mem_ℓ, hdeg_ge⟩ :=
    line_of_large_degree_of_counting_supply L hL0 A.volConst_pos hT_pos hsupply
  have hlog_bd : Real.log (2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2) ≤
      c_deg * (k : ℝ) := by
    have hd := hmem_log.choose_spec k hkLog
    rw [Real.dist_eq, sub_zero] at hd
    have hle1 := (le_abs_self _).trans hd.le
    exact (div_le_iff₀ hk_pos).mp hle1
  have hlin_bd : Real.log (4 * A.volConst + 2) ≤ c_deg * (k : ℝ) := hmem_lin.choose_spec k hkLin
  have hterm_nn : 0 ≤ 2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) :=
    mul_nonneg (by linarith [A.volConst_pos])
      (add_nonneg (mul_nonneg hberg_pos.le (pow_nonneg (by positivity) _)) zero_le_one)
  have hberg_exp_le :
      2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 1 < Real.exp T := by
    have hck : Real.log (2 * A.volConst * (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp + 1) + 2) ≤ T := by
      have : 0 ≤ c_deg * (k : ℝ) := mul_nonneg hc_deg_pos.le hk_pos.le
      linarith [hT_eq]
    have h1 := Real.exp_le_exp.mpr hck
    rw [Real.exp_log (by linarith)] at h1
    linarith
  have hsmall : A.supNorm k v < 1 := by
    have h1 := A.supNorm_le_bergman k hk1 v
    have hden_pos : 0 < Real.exp T - 1 := by linarith
    have hprod_lt : A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * (2 * A.volConst) < Real.exp T - 1 := by
      have hpos_b : 0 < A.bergConst * ((k : ℝ) + 1) ^ A.bergExp :=
        mul_pos hberg_pos (pow_pos (by positivity) _)
      nlinarith [A.volConst_pos]
    have hv_lt : A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * ‖v‖ < 1 := by
      calc A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * ‖v‖
          ≤ A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * (2 * A.volConst / (Real.exp T - 1)) :=
            mul_le_mul_of_nonneg_left hv_norm (mul_nonneg hberg_pos.le (pow_nonneg (by positivity) _))
        _ = (A.bergConst * ((k : ℝ) + 1) ^ A.bergExp * (2 * A.volConst)) / (Real.exp T - 1) := by ring
        _ < 1 := (div_lt_one hden_pos).mpr hprod_lt
    exact h1.trans_lt hv_lt
  have hdeg_lin : c_deg * (k : ℝ) ≤ degAr ℓ := by
    have hexp_ge : 2 * A.volConst * Real.exp (c_deg * (k : ℝ)) + 1 ≤ Real.exp T := by
      have h4 : 4 * A.volConst + 2 ≤ Real.exp (c_deg * (k : ℝ)) := by
        have h1 := Real.exp_le_exp.mpr hlin_bd
        rwa [Real.exp_log (by linarith [A.volConst_pos])] at h1
      have hck : Real.exp T = Real.exp (c_deg * (k : ℝ)) * Real.exp (c_deg * (k : ℝ)) := by
        rw [hT_eq, ← Real.exp_add]
        congr 1; ring
      rw [hck]
      have hexp_pos : 0 < Real.exp (c_deg * (k : ℝ)) := Real.exp_pos _
      nlinarith [A.volConst_pos]
    have hlog_ge : c_deg * (k : ℝ) ≤ Real.log (Real.exp T - 1) - Real.log (2 * A.volConst) := by
      have h2v : 0 < 2 * A.volConst := mul_pos two_pos A.volConst_pos
      have hle : 2 * A.volConst * Real.exp (c_deg * (k : ℝ)) ≤ Real.exp T - 1 := by linarith
      have hlog := Real.log_le_log (mul_pos h2v (Real.exp_pos _)) hle
      rw [Real.log_mul h2v.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
      linarith
    exact hlog_ge.trans hdeg_ge
  have hsl_eq : RHDirect.ArakelovCovolume.slope ℓ = degAr ℓ := by
    unfold RHDirect.ArakelovCovolume.slope
    rw [hrk_ℓ, Nat.cast_one, div_one]
  refine ⟨⟨v, hvL⟩, ℓ, fun h0 => hv0 (congrArg Subtype.val h0), hsmall,
    hℓL, hsat, hℓ0, hrk_ℓ, hv_mem_ℓ, hdeg_lin, hsl_eq⟩

/-- **Arbitrary Target-Degree Corollary (`line_of_arbitrary_large_degree_of_use`)**:
for any `A : GradedHermAlgebra d` with `0 < A.volAr` and ANY target Arakelov degree `Δ : ℝ`,
there exists a degree `k ≥ 1`, a nonzero small section `s ∈ A.smallSectionsSet k`, and a
saturated rank-1 sublattice `ℓ ≤ A.secLat k` with `Δ ≤ degAr ℓ`. -/
theorem line_of_arbitrary_large_degree_of_use {d : ℕ} (A : GradedHermAlgebra d)
    (hbig : 0 < A.volAr) (Δ : ℝ) :
    ∃ (k : ℕ) (_ : 1 ≤ k) (s : A.secLat k) (ℓ : Submodule ℤ (A.secSpace k)),
      s ≠ 0 ∧ A.supNorm k s.1 < 1 ∧
      ℓ ≤ A.secLat k ∧ IsSaturated (A.secLat k) ℓ ∧ rk ℓ = 1 ∧
      (s : A.secSpace k) ∈ ℓ ∧ Δ ≤ degAr ℓ := by
  obtain ⟨c_deg, hc_deg, K₀, hK₀, hline⟩ := line_of_large_degree_of_use A hbig
  obtain ⟨N, hN⟩ := exists_nat_gt (Δ / c_deg)
  let k : ℕ := max K₀ N
  have hkK₀ : K₀ ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := le_trans hK₀ hkK₀
  obtain ⟨s, ℓ, hs0, hsm, hℓL, hsat, _, hrk, hmem, hdeg, _⟩ := hline k hkK₀
  have hk_ge : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
  have hΔ_le : Δ ≤ c_deg * (k : ℝ) := by
    have h1 : Δ / c_deg < (k : ℝ) := lt_of_lt_of_le hN hk_ge
    simpa [mul_comm] using ((div_lt_iff₀ hc_deg).mp h1).le
  exact ⟨k, hk1, s, ℓ, hs0, hsm, hℓL, hsat, hrk, hmem, hΔ_le.trans hdeg⟩

end LineOfLargeDegree

/-! ## Section 5: M4 Wave 2 Bridge & Concrete Zero-Assumption Projective-Space Realization -/

section Wave2BridgeAndWitness

/-- **Packaged M4 Wave 2 Interface (`M4SmallSectionsBridge`)**:
bundles a graded Hermitian algebra `A : GradedHermAlgebra d` with its Moriwaki small-section
supply, upper counting rate, and large-degree rank-1 line extraction for `Stage14M4_HeightLowerGeneral`
and `Stage14M4_CovolStepsBridge`. -/
structure M4SmallSectionsBridge (d : ℕ) where
  alg : GradedHermAlgebra d
  volAr_pos : 0 < alg.volAr
  c_deg : ℝ
  c_deg_pos : 0 < c_deg
  K₀ : ℕ
  hK₀ : 1 ≤ K₀
  extract_line : ∀ k : ℕ, K₀ ≤ k →
    ∃ (s : alg.secLat k) (ℓ : Submodule ℤ (alg.secSpace k)),
      s ≠ 0 ∧ alg.supNorm k s.1 < 1 ∧
      ℓ ≤ alg.secLat k ∧ IsSaturated (alg.secLat k) ℓ ∧ rk ℓ = 1 ∧
      (s : alg.secSpace k) ∈ ℓ ∧ c_deg * (k : ℝ) ≤ degAr ℓ

/-- Construct an `M4SmallSectionsBridge` unconditionally from any `A : GradedHermAlgebra d`
with `0 < A.volAr`. -/
def mkM4SmallSectionsBridge {d : ℕ} (A : GradedHermAlgebra d) (hbig : 0 < A.volAr) :
    M4SmallSectionsBridge d :=
  let h := line_of_large_degree_of_use A hbig
  { alg := A
    volAr_pos := hbig
    c_deg := h.choose
    c_deg_pos := h.choose_spec.1
    K₀ := h.choose_spec.2.choose
    hK₀ := h.choose_spec.2.choose_spec.choose
    extract_line := fun k hk => by
      obtain ⟨s, ℓ, hs0, hsm, hℓL, hsat, _, hrk, hmem, hdeg, _⟩ :=
        h.choose_spec.2.choose_spec.choose_spec k hk
      exact ⟨s, ℓ, hs0, hsm, hℓL, hsat, hrk, hmem, hdeg⟩ }

/-- **Concrete 0-Assumption Projective-Space Realization (`projSpace_m4_small_sections_bridge`)**:
proves that `M4SmallSectionsBridge d` and all small-section counting upper bounds and
large-degree line extraction theorems are genuinely inhabited for `ℙ^d` (`d ≥ 1`, `α > 0`). -/
def projSpace_m4_small_sections_bridge (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    M4SmallSectionsBridge d :=
  mkM4SmallSectionsBridge (projSpaceGradedHermAlgebra d hd hα)
    (mul_pos hα (Nat.cast_pos.mpr (Nat.succ_pos d)))

/-- Helper: every vector in `diagLat (fun _ : ι => (1 : ℝ))` has integer coordinates. -/
private lemma diagLat_one_coord_int {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : EuclideanSpace ℝ ι}
    (hx : x ∈ RHDirect.Stage11MoriwakiCovolume.diagLat (fun _ : ι => (1 : ℝ))) (i : ι) :
    ∃ z : ℤ, x i = (z : ℝ) := by
  change x ∈ Submodule.span ℤ
    (Set.range fun j : ι => (1 : ℝ) • EuclideanSpace.single j (1 : ℝ)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨j, rfl⟩
      simp only [one_smul, EuclideanSpace.single, PiLp.single_apply]
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hij]⟩
  | zero => exact ⟨0, by simp⟩
  | add _ _ _ _ ha hb =>
      rcases ha with ⟨z₁, hz₁⟩
      rcases hb with ⟨z₂, hz₂⟩
      exact ⟨z₁ + z₂, by simp [hz₁, hz₂]⟩
  | smul a y _ ha =>
      rcases ha with ⟨z, hz⟩
      refine ⟨a * z, ?_⟩
      change (a • y) i = ((a * z : ℤ) : ℝ)
      rw [PiLp.smul_apply, zsmul_eq_mul, hz]
      push_cast
      ring

/-- Helper: every nonzero sublattice `N ≤ diagLat (fun _ : ι => (1 : ℝ))` has `covol N ≥ 1`,
hence `muMax (diagLat (fun _ : ι => (1 : ℝ))) ≤ 0`. -/
theorem muMax_diagLat_one_le_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    muMax (RHDirect.Stage11MoriwakiCovolume.diagLat (fun _ : ι => (1 : ℝ))) ≤ 0 := by
  let ZLat := RHDirect.Stage11MoriwakiCovolume.diagLat (fun _ : ι => (1 : ℝ))
  have hinv := RHDirect.Stage11MoriwakiCovolume.diagLat_invariants (fun _ : ι => (1 : ℝ))
    (fun _ => zero_lt_one)
  have : DiscreteTopology ZLat := hinv.1
  unfold muMax RHDirect.ArakelovCovolume.slopes
  by_cases hne_ι : Nonempty ι
  · apply csSup_le
    · have hZ0 : ZLat ≠ ⊥ := by
        intro hbot
        have hrk := hinv.2.1
        change rk ZLat = Fintype.card ι at hrk
        rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) = 0 by simp [rk]] at hrk
        exact (Fintype.card_pos_iff.mpr hne_ι).ne hrk
      exact ⟨RHDirect.ArakelovCovolume.slope ZLat, ZLat, le_rfl, hZ0, rfl⟩
    · rintro _ ⟨N, hNZ, hN0, rfl⟩
      have : DiscreteTopology N := discreteTopology_of_le hNZ
      let b : Basis (Fin (rk N)) ℤ N := Module.finBasis ℤ N
      let G : Matrix (Fin (rk N)) (Fin (rk N)) ℝ :=
        Matrix.gram ℝ (fun j => (b j : EuclideanSpace ℝ ι))
      have hG_int : ∀ j l : Fin (rk N), ∃ z : ℤ, G j l = (z : ℝ) := by
        intro j l
        have hj : ∀ i : ι, ∃ z : ℤ, (b j : EuclideanSpace ℝ ι) i = (z : ℝ) :=
          fun i => diagLat_one_coord_int (hNZ (b j).2) i
        have hl : ∀ i : ι, ∃ z : ℤ, (b l : EuclideanSpace ℝ ι) i = (z : ℝ) :=
          fun i => diagLat_one_coord_int (hNZ (b l).2) i
        choose zj hzj using hj
        choose zl hzl using hl
        refine ⟨∑ i : ι, zj i * zl i, ?_⟩
        change inner ℝ (b j : EuclideanSpace ℝ ι) (b l : EuclideanSpace ℝ ι) = _
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial, dotProduct]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hzj i, hzl i, mul_comm]
      choose GZ hGZ using hG_int
      let GZMat : Matrix (Fin (rk N)) (Fin (rk N)) ℤ := Matrix.of GZ
      have hG_eq : G = GZMat.map (Int.castRingHom ℝ) := by
        ext j l; exact hGZ j l
      have hdet_int : G.det = ((GZMat.det : ℤ) : ℝ) := by
        rw [hG_eq]
        exact ((Int.castRingHom ℝ).map_det GZMat).symm
      have hdet_pos : 0 < G.det := RHDirect.ArakelovCovolume.det_gram_basis_pos N b
      have hdetZ_pos : 0 < GZMat.det := by
        rw [hdet_int] at hdet_pos
        exact_mod_cast hdet_pos
      have hdet_ge1 : (1 : ℝ) ≤ G.det := by
        rw [hdet_int]
        exact_mod_cast (Int.add_one_le_iff.mpr hdetZ_pos)
      have hcov_ge1 : 1 ≤ covol N := by
        rw [RHDirect.ArakelovCovolume.covol_eq_sqrt_det_gram N b]
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt G.det := Real.sqrt_le_sqrt hdet_ge1
      have hlog_nn : 0 ≤ Real.log (covol N) := Real.log_nonneg hcov_ge1
      unfold RHDirect.ArakelovCovolume.slope degAr
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
  · have hZbot : ZLat = ⊥ := by
      have hEmp : IsEmpty ι := not_nonempty_iff.mp hne_ι
      rw [eq_bot_iff]
      intro x _
      ext i
      exact hEmp.elim i
    have hset : { x : ℝ | ∃ N ≤ ZLat, N ≠ ⊥ ∧ RHDirect.ArakelovCovolume.slope N = x } = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro N hNZ hN0 _
      apply hN0
      rw [eq_bot_iff]
      exact hNZ.trans (le_of_eq hZbot)
    rw [hset, Real.sSup_empty]

/-- For any nonempty finite index type `ι` and `c > 0`,
`muMax (diagLat (fun _ : ι => c)) ≤ -Real.log c`. -/
theorem muMax_diagLat_const_le {ι : Type*} [Fintype ι] [DecidableEq ι] [hne_ι : Nonempty ι]
    {c : ℝ} (hc : 0 < c) :
    muMax (RHDirect.Stage11MoriwakiCovolume.diagLat (fun _ : ι => c)) ≤ -Real.log c := by
  let Lc := RHDirect.Stage11MoriwakiCovolume.diagLat (fun _ : ι => c)
  let L1 := RHDirect.Stage11MoriwakiCovolume.diagLat (fun _ : ι => (1 : ℝ))
  have hinv_c := RHDirect.Stage11MoriwakiCovolume.diagLat_invariants (fun _ : ι => c) (fun _ => hc)
  have hinv_1 := RHDirect.Stage11MoriwakiCovolume.diagLat_invariants (fun _ : ι => (1 : ℝ))
    (fun _ => zero_lt_one)
  have : DiscreteTopology Lc := hinv_c.1
  have : DiscreteTopology L1 := hinv_1.1
  unfold muMax RHDirect.ArakelovCovolume.slopes
  apply csSup_le
  · have hLc0 : Lc ≠ ⊥ := by
      intro hbot
      have hrk := hinv_c.2.1
      change rk Lc = Fintype.card ι at hrk
      rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) = 0 by simp [rk]] at hrk
      exact (Fintype.card_pos_iff.mpr hne_ι).ne hrk
    exact ⟨RHDirect.ArakelovCovolume.slope Lc, Lc, le_rfl, hLc0, rfl⟩
  · rintro _ ⟨N, hNLc, hN0, rfl⟩
    have : DiscreteTopology N := discreteTopology_of_le hNLc
    have hscale : ∀ x : EuclideanSpace ℝ ι, x ∈ Lc → c⁻¹ • x ∈ L1 := by
      intro x hx
      change x ∈ Submodule.span ℤ (Set.range fun j : ι => c • EuclideanSpace.single j (1 : ℝ)) at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨j, rfl⟩
          rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
          exact Submodule.subset_span ⟨j, by simp⟩
      | zero => simp
      | add _ _ _ _ ha hb => rw [smul_add]; exact L1.add_mem ha hb
      | smul a y _ ha =>
          change c⁻¹ • ((a : ℤ) • y) ∈ L1
          rw [← Int.cast_smul_eq_zsmul ℝ a, smul_comm, Int.cast_smul_eq_zsmul]
          exact L1.smul_mem a ha
    let φ : N →ₗ[ℤ] L1 :=
      { toFun := fun x => ⟨c⁻¹ • (x : EuclideanSpace ℝ ι), hscale x.1 (hNLc x.2)⟩
        map_add' := fun x y => Subtype.ext (by simp [smul_add])
        map_smul' := fun a x => Subtype.ext (by
          change c⁻¹ • (a • (x : EuclideanSpace ℝ ι)) = a • (c⁻¹ • (x : EuclideanSpace ℝ ι))
          rw [← Int.cast_smul_eq_zsmul ℝ a, smul_comm, Int.cast_smul_eq_zsmul]) }
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      have h1 : c⁻¹ • (x : EuclideanSpace ℝ ι) = c⁻¹ • (y : EuclideanSpace ℝ ι) :=
        congrArg Subtype.val hxy
      have h2 := congrArg (c • ·) h1
      rw [smul_inv_smul₀ hc.ne', smul_inv_smul₀ hc.ne'] at h2
      exact Subtype.ext h2
    have hφ_bd : ∀ x : N, ‖((φ x : L1) : EuclideanSpace ℝ ι)‖ ≤ c⁻¹ * ‖(x : EuclideanSpace ℝ ι)‖ := by
      intro x
      change ‖c⁻¹ • (x : EuclideanSpace ℝ ι)‖ ≤ c⁻¹ * ‖(x : EuclideanSpace ℝ ι)‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    have hBost := bost_slope_inequality N L1 hN0 φ c⁻¹ hφ_inj hφ_bd
    rw [Real.log_inv] at hBost
    linarith [muMax_diagLat_one_le_zero (ι := ι)]

/-- Concrete `O(k^(d+1))` counting upper bound on `projSpaceGradedHermAlgebra d hd hα`:
verifies both Moriwaki's lower bound and our matching `small_generated_count_upper` bound
on `ℙ^d` simultaneously! -/
theorem projSpace_small_generated_count_two_sided (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    let A := projSpaceGradedHermAlgebra d hd hα
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀, ∀ k : ℕ, (hk : K₀ ≤ k) →
      c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (gradedSmallGeneratedCount A k (le_trans hK₀ hk) : ℝ)) ∧
    (∃ C_hi : ℝ, 0 < C_hi ∧ ∀ k : ℕ, (hk : 1 ≤ k) →
      Real.log (gradedSmallGeneratedCount A k hk : ℝ) ≤ C_hi * (k : ℝ) ^ (d + 1)) := by
  let A := projSpaceGradedHermAlgebra d hd hα
  have hlo := RHDirect.Stage12SchurWeylLattices.projSpace_moriwaki_big d hd hα
  have hmu : ∀ k : ℕ, 1 ≤ k → muMax (A.secLat k) ≤ α * (k : ℝ) := by
    intro k _
    have hlat_eq : A.secLat k =
        RHDirect.Stage11MoriwakiCovolume.diagLat
          (fun _ : RHDirect.Stage11MoriwakiCovolume.MultiIndex (d + 1) k => Real.exp (-α * (k : ℝ))) := by
      change RHDirect.Stage11MoriwakiCovolume.symPowMonomialLat
        (fun _ : Fin (d + 1) => Real.exp (-α)) k = _
      unfold RHDirect.Stage11MoriwakiCovolume.symPowMonomialLat
        RHDirect.Stage11MoriwakiCovolume.symPowWeightedLat
      congr 1
      ext β
      rw [one_mul]
      have hprod : ∏ i : Fin (d + 1), Real.exp (-α) ^ β.1 i =
          Real.exp (∑ i : Fin (d + 1), (β.1 i : ℝ) * (-α)) := by
        simp_rw [← Real.exp_nat_mul]
        rw [← Real.exp_sum]
      rw [hprod, ← Finset.sum_mul]
      have hsum : (∑ i : Fin (d + 1), (β.1 i : ℝ)) = (k : ℝ) := by
        exact_mod_cast β.2
      rw [hsum]
      congr 1
      ring
    rw [hlat_eq]
    have : Nonempty (RHDirect.Stage11MoriwakiCovolume.MultiIndex (d + 1) k) :=
      Fintype.card_pos_iff.mp (RHDirect.Stage11MoriwakiCovolume.card_multiIndex_pos (Nat.succ_pos d) k)
    have hle := muMax_diagLat_const_le (ι := RHDirect.Stage11MoriwakiCovolume.MultiIndex (d + 1) k)
      (Real.exp_pos (-α * (k : ℝ)))
    rw [Real.log_exp] at hle
    ring_nf at hle ⊢
    exact hle
  exact ⟨hlo, graded_small_generated_count_upper A α 0 hα.le le_rfl (fun k hk => by
    have := hmu k hk; linarith)⟩

end Wave2BridgeAndWitness

end RHDirect.Stage14M4_SmallSectionsInjective

end
