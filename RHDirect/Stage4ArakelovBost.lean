import RHDirect.ArakelovCovolume
import RHDirect.Stage2SiegelReduction
import RHDirect.Stage3ThetaSiegelBridge
import RHDirect.Stage2HodgeWeights
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Order.Round

/-!
# RHDirect.Stage4ArakelovBost

Stage 4 deep mathematical foundation for Euclidean Arakelov geometry in pure Mathlib `v4.33.1`
(0 `sorry`, 0 custom `axiom`s):

1. **Saturated Sublattices, Exact Quotient-Orthogonal Additivity & Grayson–Stuhler Supermodularity**:
   - Saturated sublattices `IsSaturated L M`, saturation `saturation L N`, orthogonal projection
     `projOrth M` and quotient lattice `quotLat L M`.
   - Basis extension for saturated sublattices (`exists_basis_extend_of_isSaturated`), exact rank
     and covolume additivity (`rk_add_quotLat`, `covol_eq_mul_quotLat`, `degAr_eq_add_quotLat`),
     and quotient-of-quotient compatibility (`quotLat_quotLat`).
   - Grayson–Stuhler supermodularity of Arakelov degree:
     `covol (M₁ ⊔ M₂) * covol (M₁ ⊓ M₂) ≤ covol M₁ * covol M₂` and
     `degAr M₁ + degAr M₂ ≤ degAr (M₁ ⊔ M₂) + degAr (M₁ ⊓ M₂)` (plus saturated-join version).

2. **Finiteness, Maximal Destabilizing Sublattice & Canonical Harder–Narasimhan Filtration**:
   - Finiteness of saturated sublattices of bounded covolume / bounded-below slope via Hermite's
     first minimum and orthogonal quotient induction (`finite_saturated_covol_le`,
     `finite_saturated_slope_ge`).
   - Existence and uniqueness of the maximal destabilizing sublattice `maxDestab L` maximizing
     `(slope M, rk M)` lexicographically (`exists_maxDestab`, `maxDestab_unique`).
   - Existence and uniqueness of the canonical Harder–Narasimhan filtration `HNFiltration L`
     with semistable quotients and strictly decreasing slopes (`exists_hnFiltration`,
     `hnFiltration_unique`).

3. **Harder–Narasimhan Polygon, Concavity & `Stage2HodgeWeights.polygon` Bridge**:
   - Concave HN polygon `hnPolygon F`, Stuhler–Grayson upper envelope `degAr M ≤ hnPolygon F (rk M)`,
     and exact/approximate bridge to `Stage2HodgeWeights.polygon` and `Stage2HodgeWeights.polygon_convex`.

4. **Bost's Morphism Slope Inequality, Dual Lattice Duality, Sharp Successive-Minima Bounds &
   `BostSlopeFiber.SlopeIneq` Discharge**:
   - Filtered and general Bost morphism slope inequalities (`bost_filtered_slope_inequality`,
     `bost_muMin_le_muMax_add_log`, `bost_morphism_degree_inequality`, `bost_truncation_inclusion`).
   - Euclidean dual lattice `dualLat L`, annihilator correspondence `annLat L M = dualLat (quotLat L M)`,
     exact slope duality (`muMax_dualLat`, `muMin_dualLat`), and sharp successive-minima / Banaszczyk
     bounds.
   - Direct discharge of `RHDirect.BostSlopeFiber.SlopeIneq` from `HNFiltration` and Bost's
     truncation inclusion theorem.
-/

open Module Submodule Finset Real
open scoped BigOperators Matrix InnerProductSpace

namespace RHDirect.Stage4ArakelovBost

noncomputable section

open RHDirect.ArakelovCovolume (rk covol degAr slopes muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  covol_bot degAr_bot covol_span_singleton slope_span_singleton
  covol_le_of_le_same_rank covol_le_sqrt_det_gram gram_det_le
  norm_sum_smul_le_of_int slopes_bddAbove slope_le_muMax muMax_mono
  bost_slope_inequality bost_degree_inequality)

open RHDirect.Stage2SiegelReduction (gsVec gsCoeff gs_expansion_lt gs_expansion
  gsVec_orthogonal gsVec_sub_mem_span_lt gsVec_ne_zero_of_linearIndependent
  norm_sq_eq_sum_gsVec gsVec_norm_le det_gram_eq_prod_gsVec_norm_sq
  covol_eq_prod_gsVec covol_le_prod_norm lattice_inter_closedBall_finite
  lambda1 lambda1_pos lambda1_le_norm exists_norm_eq_lambda1 lambda1_le_hermite
  succMin succMin_mono succMin_zero_eq_lambda1 succMin_pos
  exists_vecs_attaining_succMin exists_independent_le_succMin covol_le_prod_succMin
  neg_log_lambda1_le_muMax slope_sub_half_log_rk_le_neg_log_lambda1)

/-! ## Section 1: Saturated Sublattices, Basis Extension & Orthogonal Quotient Lattice -/

section SaturatedAndQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A sublattice `M ≤ L` is **saturated** in `L` if `L ∩ span_ℝ(M) = M`. -/
def IsSaturated (L M : Submodule ℤ E) : Prop :=
  M ≤ L ∧ ∀ x ∈ L, x ∈ Submodule.span ℝ (M : Set E) → x ∈ M

/-- The **saturation** of `N` inside `L`: `L ∩ span_ℝ(N)`. -/
def saturation (L N : Submodule ℤ E) : Submodule ℤ E :=
  L ⊓ (Submodule.span ℝ (N : Set E)).restrictScalars ℤ

/-- The **saturated join** of `M₁, M₂` inside `L`: `saturation L (M₁ ⊔ M₂)`. -/
def satJoin (L M₁ M₂ : Submodule ℤ E) : Submodule ℤ E :=
  saturation L (M₁ ⊔ M₂)

omit [FiniteDimensional ℝ E] in
lemma isSaturated_self (L : Submodule ℤ E) : IsSaturated L L :=
  ⟨le_rfl, fun _ hx _ => hx⟩

omit [FiniteDimensional ℝ E] in
lemma isSaturated_bot (L : Submodule ℤ E) : IsSaturated L ⊥ := by
  refine ⟨bot_le, fun x _ hx => ?_⟩
  have hbot : Submodule.span ℝ ((⊥ : Submodule ℤ E) : Set E) = ⊥ := by
    rw [Submodule.bot_coe, Submodule.span_singleton_eq_bot.mpr rfl]
  rw [hbot, Submodule.mem_bot] at hx
  exact (Submodule.mem_bot ℤ).mpr hx

omit [FiniteDimensional ℝ E] in
lemma isSaturated_of_le_of_isSaturated {L L' M : Submodule ℤ E}
    (hsat : IsSaturated L M) (hML' : M ≤ L') (hL'L : L' ≤ L) :
    IsSaturated L' M :=
  ⟨hML', fun x hxL' hxsp => hsat.2 x (hL'L hxL') hxsp⟩

omit [FiniteDimensional ℝ E] in
lemma isSaturated_inf {L M₁ M₂ : Submodule ℤ E}
    (h₁ : IsSaturated L M₁) (h₂ : IsSaturated L M₂) :
    IsSaturated L (M₁ ⊓ M₂) := by
  refine ⟨inf_le_left.trans h₁.1, fun x hxL hxsp => ?_⟩
  have hsp1 : Submodule.span ℝ ((M₁ ⊓ M₂ : Submodule ℤ E) : Set E) ≤
      Submodule.span ℝ (M₁ : Set E) :=
    Submodule.span_mono (show ((M₁ ⊓ M₂ : Submodule ℤ E) : Set E) ⊆ (M₁ : Set E) from inf_le_left)
  have hsp2 : Submodule.span ℝ ((M₁ ⊓ M₂ : Submodule ℤ E) : Set E) ≤
      Submodule.span ℝ (M₂ : Set E) :=
    Submodule.span_mono (show ((M₁ ⊓ M₂ : Submodule ℤ E) : Set E) ⊆ (M₂ : Set E) from inf_le_right)
  exact ⟨h₁.2 x hxL (hsp1 hxsp), h₂.2 x hxL (hsp2 hxsp)⟩

omit [FiniteDimensional ℝ E] in
lemma le_saturation {L N : Submodule ℤ E} (hNL : N ≤ L) : N ≤ saturation L N :=
  fun _ hx => ⟨hNL hx, Submodule.subset_span hx⟩

omit [FiniteDimensional ℝ E] in
lemma saturation_le (L N : Submodule ℤ E) : saturation L N ≤ L :=
  inf_le_left

omit [FiniteDimensional ℝ E] in
lemma span_real_saturation {L N : Submodule ℤ E} (hNL : N ≤ L) :
    Submodule.span ℝ ((saturation L N : Submodule ℤ E) : Set E) =
      Submodule.span ℝ (N : Set E) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    intro x hx
    exact hx.2
  · exact Submodule.span_mono (show (N : Set E) ⊆ (saturation L N : Set E) from le_saturation hNL)

omit [FiniteDimensional ℝ E] in
lemma isSaturated_saturation {L N : Submodule ℤ E} (hNL : N ≤ L) :
    IsSaturated L (saturation L N) := by
  refine ⟨saturation_le L N, fun x hxL hxsp => ?_⟩
  rw [span_real_saturation hNL] at hxsp
  exact ⟨hxL, hxsp⟩

omit [FiniteDimensional ℝ E] in
lemma saturation_eq_self {L M : Submodule ℤ E} (h : IsSaturated L M) :
    saturation L M = M := by
  apply le_antisymm
  · intro x hx
    exact h.2 x hx.1 hx.2
  · exact le_saturation h.1

omit [FiniteDimensional ℝ E] in
lemma saturation_mono {L N₁ N₂ : Submodule ℤ E} (h : N₁ ≤ N₂) :
    saturation L N₁ ≤ saturation L N₂ :=
  inf_le_inf_left L (Submodule.span_mono (show (N₁ : Set E) ⊆ (N₂ : Set E) from h))

omit [FiniteDimensional ℝ E] in
lemma saturation_le_of_isSaturated {L N M : Submodule ℤ E} (hNM : N ≤ M) (hM : IsSaturated L M) :
    saturation L N ≤ M := by
  calc saturation L N ≤ saturation L M := saturation_mono hNM
    _ = M := saturation_eq_self hM

lemma rk_saturation {L N : Submodule ℤ E} [DiscreteTopology L] (hNL : N ≤ L) :
    rk (saturation L N) = rk N := by
  have : DiscreteTopology N := discreteTopology_of_le hNL
  have : DiscreteTopology ↥(saturation L N) := discreteTopology_of_le (saturation_le L N)
  unfold rk
  rw [finrank_int_eq_finrank_real_span (saturation L N), finrank_int_eq_finrank_real_span N,
    span_real_saturation hNL]

lemma covol_saturation_le {L N : Submodule ℤ E} [DiscreteTopology L] (hNL : N ≤ L) :
    covol (saturation L N) ≤ covol N ∧ degAr N ≤ degAr (saturation L N) := by
  have : DiscreteTopology ↥(saturation L N) := discreteTopology_of_le (saturation_le L N)
  exact covol_le_of_le_same_rank (L := saturation L N) (M := N) (le_saturation hNL) (rk_saturation hNL).symm

lemma slope_le_slope_saturation {L N : Submodule ℤ E} [DiscreteTopology L] (hNL : N ≤ L) :
    ArakelovCovolume.slope N ≤ ArakelovCovolume.slope (saturation L N) := by
  unfold ArakelovCovolume.slope
  rw [rk_saturation hNL]
  exact div_le_div_of_nonneg_right (covol_saturation_le hNL).2 (Nat.cast_nonneg _)

/-- Two saturated sublattices `M₁ ≤ M₂` of `L` with equal rank are equal. -/
lemma eq_of_isSaturated_of_rk_eq {L M₁ M₂ : Submodule ℤ E} [DiscreteTopology L]
    (h₁ : IsSaturated L M₁) (h₂ : M₂ ≤ L) (h12 : M₁ ≤ M₂) (hrk : rk M₁ = rk M₂) :
    M₁ = M₂ := by
  have : DiscreteTopology M₁ := discreteTopology_of_le h₁.1
  have : DiscreteTopology M₂ := discreteTopology_of_le h₂
  have hsp_le : Submodule.span ℝ (M₁ : Set E) ≤ Submodule.span ℝ (M₂ : Set E) :=
    Submodule.span_mono (show (M₁ : Set E) ⊆ (M₂ : Set E) from h12)
  have hdim : Module.finrank ℝ (Submodule.span ℝ (M₁ : Set E)) =
      Module.finrank ℝ (Submodule.span ℝ (M₂ : Set E)) := by
    rw [← finrank_int_eq_finrank_real_span M₁, ← finrank_int_eq_finrank_real_span M₂]
    exact hrk
  have hsp_eq : Submodule.span ℝ (M₁ : Set E) = Submodule.span ℝ (M₂ : Set E) :=
    Submodule.eq_of_le_of_finrank_eq hsp_le hdim
  apply le_antisymm h12
  intro x hxM₂
  exact h₁.2 x (h₂ hxM₂) (hsp_eq ▸ Submodule.subset_span hxM₂)

/-- A saturated sublattice `M ≤ L` yields a torsion-free quotient `L / M`, hence any `ℤ`-basis
`bM` of `M` extends to a `ℤ`-basis of `L`. -/
theorem exists_basis_extend_of_isSaturated {L M : Submodule ℤ E} [DiscreteTopology L]
    (hM : IsSaturated L M) {r₁ : ℕ} (bM : Basis (Fin r₁) ℤ M) :
    ∃ (s : ℕ) (l : Fin s → L) (bL : Basis (Fin (r₁ + s)) ℤ L),
      (∀ k, bL k = Fin.append (fun i => (⟨(bM i : E), hM.1 (bM i).2⟩ : L)) l k) ∧
      rk L = r₁ + s := by
  let ML : Submodule ℤ L := M.comap L.subtype
  let Q := L ⧸ ML
  have hTF : Module.IsTorsionFree ℤ Q := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    rintro n q hnq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective ML q
    have hmk : Submodule.Quotient.mk (p := ML) (n • x) = 0 := by
      simpa only [Submodule.Quotient.mk_smul] using hnq
    rw [Submodule.Quotient.mk_eq_zero] at hmk
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      rw [Submodule.Quotient.mk_eq_zero]
      have hnx : (n • x : L).1 ∈ M := hmk
      have hxsp : (x : E) ∈ Submodule.span ℝ (M : Set E) := by
        have h1 : (n : ℝ) • (x : E) ∈ Submodule.span ℝ (M : Set E) := by
          rw [Int.cast_smul_eq_zsmul]
          exact Submodule.subset_span hnx
        have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
        have h2 := Submodule.smul_mem (Submodule.span ℝ (M : Set E)) (n : ℝ)⁻¹ h1
        rwa [inv_smul_smul₀ hnR] at h2
      exact hM.2 x.1 x.2 hxsp
  have : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let bQ := Module.finBasis ℤ Q
  let s := Module.finrank ℤ Q
  have hsurj : Function.Surjective ML.mkQ := Submodule.mkQ_surjective ML
  choose l hl using fun j : Fin s => hsurj (bQ j)
  let mL : Fin r₁ → L := fun i => ⟨(bM i : E), hM.1 (bM i).2⟩
  let v : Fin (r₁ + s) → L := Fin.append mL l
  have hli : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hq0 : ∑ j : Fin s, c (Fin.natAdd r₁ j) • bQ j = 0 := by
      have h1 := congrArg ML.mkQ hc
      rw [map_zero, map_sum, Fin.sum_univ_add] at h1
      have hleft : ∑ i : Fin r₁, ML.mkQ (c (Fin.castAdd s i) • v (Fin.castAdd s i)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_zsmul]
        have hmem : v (Fin.castAdd s i) ∈ ML := by
          simp only [v, Fin.append_left, mL, ML, Submodule.mem_comap, Submodule.coe_subtype]
          exact (bM i).2
        have h0 : ML.mkQ (v (Fin.castAdd s i)) = 0 := (Submodule.Quotient.mk_eq_zero ML).mpr hmem
        rw [h0, smul_zero]
      rw [hleft, zero_add] at h1
      have hright : ∑ j : Fin s, ML.mkQ (c (Fin.natAdd r₁ j) • v (Fin.natAdd r₁ j)) =
          ∑ j : Fin s, c (Fin.natAdd r₁ j) • bQ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul]
        simp only [v, Fin.append_right, hl j]
      rwa [← hright]
    have hc_right : ∀ j : Fin s, c (Fin.natAdd r₁ j) = 0 :=
      Fintype.linearIndependent_iff.mp bQ.linearIndependent _ hq0
    have hleft0 : ∑ i : Fin r₁, c (Fin.castAdd s i) • bM i = 0 := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val hc
      rw [Submodule.coe_zero, Submodule.coe_sum, Fin.sum_univ_add] at h1
      have hr0 : ∑ j : Fin s, ((c (Fin.natAdd r₁ j) • v (Fin.natAdd r₁ j) : L) : E) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [hc_right j]
      rw [hr0, add_zero] at h1
      rw [Submodule.coe_sum, Submodule.coe_zero]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [v, mL]
    have hc_left : ∀ i : Fin r₁, c (Fin.castAdd s i) = 0 :=
      Fintype.linearIndependent_iff.mp bM.linearIndependent _ hleft0
    intro k
    refine Fin.addCases hc_left hc_right k
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    let d : Fin s → ℤ := fun j => bQ.repr (ML.mkQ x) j
    let y : L := x - ∑ j : Fin s, d j • l j
    have hyML : y ∈ ML := by
      rw [← Submodule.Quotient.mk_eq_zero ML]
      change ML.mkQ (x - ∑ j : Fin s, d j • l j) = 0
      rw [map_sub, map_sum]
      have hsum : ∑ j : Fin s, ML.mkQ (d j • l j) = ML.mkQ x := by
        have h1 : ∑ j : Fin s, ML.mkQ (d j • l j) = ∑ j : Fin s, d j • bQ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul, hl j]
        rw [h1]
        exact bQ.sum_repr (ML.mkQ x)
      rw [hsum, sub_self]
    let yM : M := ⟨y.1, hyML⟩
    have hy_eq : y = ∑ i : Fin r₁, bM.repr yM i • v (Fin.castAdd s i) := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val (bM.sum_repr yM)
      rw [Submodule.coe_sum] at h1
      change (yM : E) = _
      rw [← h1, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Submodule.coe_smul]
      simp [v, mL]
    have hx_eq : x = (∑ i : Fin r₁, bM.repr yM i • v (Fin.castAdd s i)) +
        ∑ j : Fin s, d j • v (Fin.natAdd r₁ j) := by
      have hsub : x = y + ∑ j : Fin s, d j • l j := (sub_add_cancel x _).symm
      rw [hsub, hy_eq]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [v]
    rw [hx_eq]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd s i, rfl⟩))
      (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd r₁ j, rfl⟩))
  let bL : Basis (Fin (r₁ + s)) ℤ L := Basis.mk hli hsp
  refine ⟨s, l, bL, fun k => Basis.mk_apply hli hsp k, ?_⟩
  unfold rk
  rw [Module.finrank_eq_card_basis bL, Fintype.card_fin]

/-- Orthogonal projection `E →ₗ[ℝ] E` onto `(span_ℝ M)ᗮ`. -/
def projOrth (M : Submodule ℤ E) : E →ₗ[ℝ] E :=
  (Submodule.span ℝ (M : Set E))ᗮ.subtype.comp
    (Submodule.orthogonalProjectionOnto (Submodule.span ℝ (M : Set E))ᗮ).toLinearMap

/-- The **orthogonal quotient lattice** `L / M` realized inside `(span_ℝ M)ᗮ ⊂ E` as the
orthogonal projection of `L` onto `(span_ℝ M)ᗮ`. -/
def quotLat (L M : Submodule ℤ E) : Submodule ℤ E :=
  L.map ((projOrth M).restrictScalars ℤ)

lemma projOrth_mem_orthogonal (M : Submodule ℤ E) (x : E) :
    projOrth M x ∈ (Submodule.span ℝ (M : Set E))ᗮ :=
  (Submodule.orthogonalProjectionOnto (Submodule.span ℝ (M : Set E))ᗮ x).2

lemma sub_projOrth_mem_span (M : Submodule ℤ E) (x : E) :
    x - projOrth M x ∈ Submodule.span ℝ (M : Set E) := by
  have h := Submodule.sub_starProjection_mem_orthogonal
    (K := (Submodule.span ℝ (M : Set E))ᗮ) x
  rw [Submodule.orthogonal_orthogonal] at h
  exact h

lemma projOrth_eq_zero_iff (M : Submodule ℤ E) (x : E) :
    projOrth M x = 0 ↔ x ∈ Submodule.span ℝ (M : Set E) := by
  constructor
  · intro h0
    have h := sub_projOrth_mem_span M x
    rwa [h0, sub_zero] at h
  · intro hx
    have hmem : x ∈ (Submodule.span ℝ (M : Set E))ᗮᗮ := by
      rwa [Submodule.orthogonal_orthogonal]
    have h0 := (Submodule.orthogonalProjectionOnto_eq_zero_iff
      (K := (Submodule.span ℝ (M : Set E))ᗮ)).mpr hmem
    change ((Submodule.orthogonalProjectionOnto (Submodule.span ℝ (M : Set E))ᗮ x : _) : E) = 0
    rw [h0]; rfl

lemma projOrth_eq_self_of_mem_orthogonal (M : Submodule ℤ E) {x : E}
    (hx : x ∈ (Submodule.span ℝ (M : Set E))ᗮ) :
    projOrth M x = x := by
  change ((Submodule.orthogonalProjectionOnto (Submodule.span ℝ (M : Set E))ᗮ x : _) : E) = x
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩]

lemma projOrth_idempotent (M : Submodule ℤ E) (x : E) :
    projOrth M (projOrth M x) = projOrth M x :=
  projOrth_eq_self_of_mem_orthogonal M (projOrth_mem_orthogonal M x)

lemma norm_projOrth_le (M : Submodule ℤ E) (x : E) :
    ‖projOrth M x‖ ≤ ‖x‖ := by
  have hsub : x - projOrth M x ∈ Submodule.span ℝ (M : Set E) := sub_projOrth_mem_span M x
  have horth : inner ℝ (x - projOrth M x) (projOrth M x) = 0 :=
    projOrth_mem_orthogonal M x _ hsub
  have hpyth : ‖x‖ ^ 2 = ‖x - projOrth M x‖ ^ 2 + ‖projOrth M x‖ ^ 2 := by
    have hx : x = (x - projOrth M x) + projOrth M x := (sub_add_cancel x _).symm
    conv_lhs => rw [hx]
    rw [norm_add_sq_real, horth, mul_zero, add_zero]
  nlinarith [norm_nonneg (projOrth M x), norm_nonneg x, sq_nonneg ‖x - projOrth M x‖]

lemma inner_projOrth_left (M : Submodule ℤ E) {u : E} (hu : u ∈ (Submodule.span ℝ (M : Set E))ᗮ)
    (v : E) :
    inner ℝ u (projOrth M v) = inner ℝ u v := by
  have hsub : v - projOrth M v ∈ Submodule.span ℝ (M : Set E) := sub_projOrth_mem_span M v
  have horth : inner ℝ u (v - projOrth M v) = 0 := by
    rw [real_inner_comm]
    exact hu (v - projOrth M v) hsub
  rw [inner_sub_right] at horth
  linarith

lemma projOrth_comp_of_le {M₁ M₂ : Submodule ℤ E} (h : M₁ ≤ M₂) (x : E) :
    projOrth M₂ (projOrth M₁ x) = projOrth M₂ x := by
  have hsub : x - projOrth M₁ x ∈ Submodule.span ℝ (M₂ : Set E) :=
    Submodule.span_mono (show (M₁ : Set E) ⊆ (M₂ : Set E) from h) (sub_projOrth_mem_span M₁ x)
  have h0 : projOrth M₂ (x - projOrth M₁ x) = 0 := (projOrth_eq_zero_iff M₂ _).mpr hsub
  rw [map_sub] at h0
  exact (sub_eq_zero.mp h0).symm

lemma projOrth_bot (x : E) : projOrth (⊥ : Submodule ℤ E) x = x := by
  apply projOrth_eq_self_of_mem_orthogonal
  intro y hy
  have hbot : Submodule.span ℝ ((⊥ : Submodule ℤ E) : Set E) = ⊥ := by
    rw [Submodule.bot_coe, Submodule.span_singleton_eq_bot.mpr rfl]
  rw [hbot, Submodule.mem_bot] at hy
  rw [hy, inner_zero_left]

lemma quotLat_bot (L : Submodule ℤ E) : quotLat L ⊥ = L := by
  ext x
  simp only [quotLat, Submodule.mem_map, LinearMap.coe_restrictScalars, projOrth_bot]
  exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

lemma quotLat_self (L : Submodule ℤ E) : quotLat L L = ⊥ := by
  ext x
  simp only [quotLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.mem_bot]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (projOrth_eq_zero_iff L y).mpr (Submodule.subset_span hy)
  · rintro rfl
    exact ⟨0, L.zero_mem, map_zero _⟩

/-- Any discrete `ℤ`-submodule `Q ⊂ E` spanned over `ℤ` by finitely many `ℝ`-linearly independent
vectors automatically carries the discrete topology! -/
lemma discreteTopology_of_fin_basis_real_li {Q : Submodule ℤ E} {s : ℕ}
    (b : Basis (Fin s) ℤ Q) (hli : LinearIndependent ℝ (fun j => (b j : E))) :
    DiscreteTopology Q := by
  let V := Submodule.span ℝ (Set.range fun j : Fin s => (b j : E))
  let bR : Basis (Fin s) ℝ V := Basis.span hli
  have hbR : ∀ j, (bR j : E) = (b j : E) := fun j => congrArg Subtype.val (Basis.span_apply hli j)
  let P : E →ₗ[ℝ] (Fin s → ℝ) :=
    (bR.equivFun.toLinearMap).comp (Submodule.orthogonalProjectionOnto V).toLinearMap
  have hP_cont : Continuous P := LinearMap.continuous_of_finiteDimensional P
  have hPb : ∀ x : Q, P (x : E) = fun j => (b.repr x j : ℝ) := by
    intro x
    have hxV : (x : E) ∈ V := by
      have h1 := congrArg Subtype.val (b.sum_repr x)
      rw [Submodule.coe_sum] at h1
      rw [← h1]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hx_eq : (⟨(x : E), hxV⟩ : V) = ∑ j, (b.repr x j : ℝ) • bR j := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val (b.sum_repr x)
      rw [Submodule.coe_sum] at h1
      rw [Submodule.coe_sum, ← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, Submodule.coe_smul, hbR, Int.cast_smul_eq_zsmul]
    change bR.equivFun (Submodule.orthogonalProjectionOnto V (x : E)) = _
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨(x : E), hxV⟩, hx_eq]
    funext j
    simp [map_sum, map_smul, Finsupp.single_apply]
  refine DiscreteTopology.of_continuous_injective (f := fun x : Q => fun j => b.repr x j) ?_
    (fun x y h => b.repr.injective (Finsupp.ext (congrFun h)))
  rw [continuous_pi_iff]
  intro j
  have hcast : Continuous (fun x : Q => ((b.repr x j : ℤ) : ℝ)) := by
    have hcomp : (fun x : Q => ((b.repr x j : ℤ) : ℝ)) = fun x : Q => P (x : E) j := by
      funext x; rw [hPb x]
    rw [hcomp]
    exact (continuous_apply j).comp (hP_cont.comp continuous_subtype_val)
  exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hcast

/-- Gram–Schmidt tail identity: when `b = Fin.append m l` extends a basis `m` of `M`,
the first `r₁` Gram–Schmidt vectors agree with `gsVec m` and the remaining `s` Gram–Schmidt
vectors equal `gsVec (projOrth M ∘ l)`! -/
private lemma gsVec_append_eq {r₁ s : ℕ} (M : Submodule ℤ E)
    (m : Fin r₁ → E) (l : Fin s → E)
    (hm_span : Submodule.span ℝ (Set.range m) = Submodule.span ℝ (M : Set E))
    (hli_m : LinearIndependent ℝ m) :
    (∀ i : Fin r₁, gsVec (Fin.append m l) (Fin.castAdd s i) = gsVec m i) ∧
    (∀ j : Fin s, gsVec (Fin.append m l) (Fin.natAdd r₁ j) = gsVec (fun k => projOrth M (l k)) j) := by
  have hhead : ∀ n : ℕ, ∀ i : Fin r₁, i.1 < n →
      gsVec (Fin.append m l) (Fin.castAdd s i) = gsVec m i := by
    intro n
    induction n with
    | zero => intro _ h; omega
    | succ n ih =>
      intro i hi
      rw [gsVec, gsVec]
      simp only [Fin.append_left]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk_eq : gsVec (Fin.append m l) ⟨k.1, lt_trans k.2 (Fin.castAdd s i).2⟩ =
          gsVec m ⟨k.1, lt_trans k.2 i.2⟩ :=
        ih ⟨k.1, lt_trans k.2 i.2⟩ (lt_of_lt_of_le k.2 (Nat.le_of_lt_succ hi))
      rw [hk_eq]
  have hhead_all : ∀ i : Fin r₁, gsVec (Fin.append m l) (Fin.castAdd s i) = gsVec m i :=
    fun i => hhead (i.1 + 1) i (Nat.lt_succ_self _)
  have hspan_gsm : Submodule.span ℝ (Set.range (gsVec m)) = Submodule.span ℝ (M : Set E) := by
    rw [← hm_span]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hsub := gsVec_sub_mem_span_lt m i
      have hmono : Submodule.span ℝ {x | ∃ k : Fin r₁, k < i ∧ m k = x} ≤
          Submodule.span ℝ (Set.range m) :=
        Submodule.span_mono fun x ⟨k, _, hkx⟩ => ⟨k, hkx⟩
      have hmi : m i ∈ Submodule.span ℝ (Set.range m) := Submodule.subset_span ⟨i, rfl⟩
      simpa using Submodule.add_mem _ (hmono hsub) hmi
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [gs_expansion m i]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hproj_eq : ∀ x : E,
      x - ∑ i : Fin r₁, (inner ℝ (gsVec m i) x / ‖gsVec m i‖ ^ 2) • gsVec m i = projOrth M x := by
    intro x
    set y := x - ∑ i : Fin r₁, (inner ℝ (gsVec m i) x / ‖gsVec m i‖ ^ 2) • gsVec m i
    have hy_orth : y ∈ (Submodule.span ℝ (M : Set E))ᗮ := by
      rw [← hspan_gsm]
      intro z hz
      induction hz using Submodule.span_induction with
      | mem u hu =>
        rcases hu with ⟨i, rfl⟩
        dsimp only [y]
        rw [inner_sub_right, inner_sum]
        have hterm : ∑ k : Fin r₁, inner ℝ (gsVec m i)
            ((inner ℝ (gsVec m k) x / ‖gsVec m k‖ ^ 2) • gsVec m k) =
            inner ℝ (gsVec m i) x := by
          rw [Finset.sum_eq_single i]
          · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
            have hne : ‖gsVec m i‖ ^ 2 ≠ 0 :=
              pow_ne_zero 2 (norm_ne_zero_iff.mpr (gsVec_ne_zero_of_linearIndependent hli_m i))
            exact div_mul_cancel₀ _ hne
          · intro k _ hki
            rw [real_inner_smul_right, gsVec_orthogonal m hki.symm, mul_zero]
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [hterm, sub_self]
      | zero => exact inner_zero_left _
      | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
      | smul a u _ hu => rw [real_inner_smul_left, hu, mul_zero]
    have hdiff_mem : x - y ∈ Submodule.span ℝ (M : Set E) := by
      have hxy : x - y = ∑ i : Fin r₁, (inner ℝ (gsVec m i) x / ‖gsVec m i‖ ^ 2) • gsVec m i := by
        dsimp only [y]; abel
      rw [hxy, ← hspan_gsm]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hpy : projOrth M y = y := projOrth_eq_self_of_mem_orthogonal M hy_orth
    have hpxy : projOrth M (x - y) = 0 := (projOrth_eq_zero_iff M _).mpr hdiff_mem
    rw [map_sub, hpy] at hpxy
    exact (sub_eq_zero.mp hpxy).symm
  have htail : ∀ n : ℕ, ∀ j : Fin s, j.1 < n →
      gsVec (Fin.append m l) (Fin.natAdd r₁ j) = gsVec (fun k => projOrth M (l k)) j := by
    intro n
    induction n with
    | zero => intro _ h; omega
    | succ n ih =>
      intro j hj
      conv_lhs => rw [gsVec]
      conv_rhs => rw [gsVec]
      simp only [Fin.append_right]
      have hsplit : ∑ k : Fin (Fin.natAdd r₁ j).1,
          (inner ℝ (gsVec (Fin.append m l) ⟨k.1, lt_trans k.2 (Fin.natAdd r₁ j).2⟩) (l j) /
            ‖gsVec (Fin.append m l) ⟨k.1, lt_trans k.2 (Fin.natAdd r₁ j).2⟩‖ ^ 2) •
            gsVec (Fin.append m l) ⟨k.1, lt_trans k.2 (Fin.natAdd r₁ j).2⟩ =
          (∑ i : Fin r₁, (inner ℝ (gsVec m i) (l j) / ‖gsVec m i‖ ^ 2) • gsVec m i) +
          (∑ t : Fin j.1,
            (inner ℝ (gsVec (fun k => projOrth M (l k)) ⟨t.1, lt_trans t.2 j.2⟩) (projOrth M (l j)) /
              ‖gsVec (fun k => projOrth M (l k)) ⟨t.1, lt_trans t.2 j.2⟩‖ ^ 2) •
              gsVec (fun k => projOrth M (l k)) ⟨t.1, lt_trans t.2 j.2⟩) := by
        change ∑ k : Fin (r₁ + j.1), _ = _
        rw [Fin.sum_univ_add]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          have hi_eq : (⟨(Fin.castAdd j.1 i).1, lt_trans (Fin.castAdd j.1 i).2 (Fin.natAdd r₁ j).2⟩ :
              Fin (r₁ + s)) = Fin.castAdd s i := Fin.ext rfl
          rw [hi_eq, hhead_all i]
        · refine Finset.sum_congr rfl fun t _ => ?_
          let t' : Fin s := ⟨t.1, lt_trans t.2 j.2⟩
          have ht_eq : (⟨(Fin.natAdd r₁ t).1, lt_trans (Fin.natAdd r₁ t).2 (Fin.natAdd r₁ j).2⟩ :
              Fin (r₁ + s)) = Fin.natAdd r₁ t' := Fin.ext rfl
          rw [ht_eq, ih t' (lt_of_lt_of_le t.2 (Nat.le_of_lt_succ hj))]
          have horth_t : gsVec (fun k => projOrth M (l k)) t' ∈ (Submodule.span ℝ (M : Set E))ᗮ := by
            have hsub := gsVec_sub_mem_span_lt (fun k => projOrth M (l k)) t'
            have hmono : Submodule.span ℝ {x | ∃ k : Fin s, k < t' ∧ projOrth M (l k) = x} ≤
                (Submodule.span ℝ (M : Set E))ᗮ :=
              Submodule.span_le.mpr fun x ⟨k, _, hkx⟩ => hkx ▸ projOrth_mem_orthogonal M (l k)
            have hmem := Submodule.add_mem _ (hmono hsub) (projOrth_mem_orthogonal M (l t'))
            simpa using hmem
          rw [inner_projOrth_left M horth_t (l j)]
      rw [hsplit, ← sub_sub, hproj_eq (l j)]
  exact ⟨hhead_all, fun j => htail (j.1 + 1) j (Nat.lt_succ_self _)⟩

/-- **Exact Quotient-Orthogonal Projection Additivity**:
for any saturated sublattice `M ≤ L` of a discrete Euclidean lattice `L ⊂ E`:
1. `quotLat L M` carries `DiscreteTopology`,
2. `rk L = rk M + rk (quotLat L M)`,
3. `covol L = covol M * covol (quotLat L M)`,
4. `degAr L = degAr M + degAr (quotLat L M)`! -/
theorem quotLat_exact_additivity {L M : Submodule ℤ E} [DiscreteTopology L]
    (hM : IsSaturated L M) :
    DiscreteTopology (quotLat L M) ∧
    rk L = rk M + rk (quotLat L M) ∧
    covol L = covol M * covol (quotLat L M) ∧
    degAr L = degAr M + degAr (quotLat L M) := by
  have : DiscreteTopology M := discreteTopology_of_le hM.1
  let r₁ := rk M
  let bM : Basis (Fin r₁) ℤ M := Module.finBasis ℤ M
  obtain ⟨s, l, bL, hbL, hrkL⟩ := exists_basis_extend_of_isSaturated hM bM
  let m : Fin r₁ → E := fun i => (bM i : E)
  let q : Fin s → E := fun j => projOrth M (l j : E)
  have hli_bL : LinearIndependent ℝ (fun k : Fin (r₁ + s) => (bL k : E)) :=
    linearIndependent_coe_basis L bL
  have hbL_coe : (fun k : Fin (r₁ + s) => (bL k : E)) = Fin.append m (fun j => (l j : E)) := by
    funext k
    rw [hbL k]
    refine Fin.addCases (fun i => by simp [m]) (fun j => by simp) k
  have hli_app : LinearIndependent ℝ (Fin.append m (fun j => (l j : E))) :=
    hbL_coe ▸ hli_bL
  have hm_span : Submodule.span ℝ (Set.range m) = Submodule.span ℝ (M : Set E) := by
    have hZ : Submodule.span ℤ (Set.range m) = M := by
      have : Set.range m = M.subtype '' Set.range bM := Set.range_comp _ _
      rw [this, ← Submodule.map_span, bM.span_eq, Submodule.map_subtype_top]
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range m), hZ]
  have hli_m : LinearIndependent ℝ m := linearIndependent_coe_basis M bM
  have hli_q : LinearIndependent ℝ q := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmem : ∑ j : Fin s, c j • (l j : E) ∈ Submodule.span ℝ (M : Set E) := by
      rw [← projOrth_eq_zero_iff M, map_sum]
      simpa only [map_smul, q] using hc
    rw [← hm_span] at hmem
    have hmem_range : ∑ j : Fin s, c j • (l j : E) ∈ Submodule.span ℝ (Set.range m) := hmem
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem_range
    obtain ⟨a, ha⟩ := hmem_range
    let d : Fin (r₁ + s) → ℝ := Fin.append a (fun j => -c j)
    have hd0 : ∑ k : Fin (r₁ + s), d k • Fin.append m (fun j => (l j : E)) k = 0 := by
      rw [Fin.sum_univ_add]
      simp only [d, Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib, ha,
        add_neg_cancel]
    have hall := Fintype.linearIndependent_iff.mp hli_app d hd0
    intro j
    have hj := hall (Fin.natAdd r₁ j)
    simp only [d, Fin.append_right, neg_eq_zero] at hj
    exact hj
  have hq_mem : ∀ j : Fin s, q j ∈ quotLat L M :=
    fun j => ⟨(l j : E), (l j).2, rfl⟩
  have hli_qZ : LinearIndependent ℤ (fun j : Fin s => (⟨q j, hq_mem j⟩ : quotLat L M)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 : ∑ k : Fin s, (c k : ℝ) • q k = 0 := by
      have h2 := congrArg Subtype.val hc
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hli_q (fun k => (c k : ℝ)) h1 j
  have hsp_qZ : ⊤ ≤ Submodule.span ℤ (Set.range fun j : Fin s => (⟨q j, hq_mem j⟩ : quotLat L M)) := by
    intro y _
    rcases y.2 with ⟨x, hxL, hxy⟩
    let c : Fin (r₁ + s) → ℤ := fun k => bL.repr ⟨x, hxL⟩ k
    have hx_eq : x = ∑ k : Fin (r₁ + s), c k • (bL k : E) := by
      have h1 := congrArg Subtype.val (bL.sum_repr ⟨x, hxL⟩)
      rw [Submodule.coe_sum] at h1
      change ∑ k : Fin (r₁ + s), ((c k • bL k : L) : E) = x at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => by simp
    have hy_eq : y = ∑ j : Fin s, c (Fin.natAdd r₁ j) • (⟨q j, hq_mem j⟩ : quotLat L M) := by
      apply Subtype.ext
      rw [Submodule.coe_sum, ← hxy, hx_eq]
      change projOrth M (∑ k : Fin (r₁ + s), c k • (bL k : E)) = _
      rw [map_sum, Fin.sum_univ_add]
      have hleft : ∑ i : Fin r₁, projOrth M (c (Fin.castAdd s i) • (bL (Fin.castAdd s i) : E)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_zsmul, hbL (Fin.castAdd s i)]
        simp only [Fin.append_left]
        rw [(projOrth_eq_zero_iff M _).mpr (Submodule.subset_span (bM i).2), smul_zero]
      rw [hleft, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, hbL (Fin.natAdd r₁ j), Fin.append_right]
      simp [q]
    rw [hy_eq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bQ : Basis (Fin s) ℤ (quotLat L M) := Basis.mk hli_qZ hsp_qZ
  have hDiscQ : DiscreteTopology (quotLat L M) :=
    discreteTopology_of_fin_basis_real_li bQ (by simpa [bQ] using hli_q)
  have hrkQ : rk (quotLat L M) = s := by
    unfold rk
    rw [Module.finrank_eq_card_basis bQ, Fintype.card_fin]
  have hgs := gsVec_append_eq M m (fun j => (l j : E)) hm_span hli_m
  have hcov : covol L = covol M * covol (quotLat L M) := by
    rw [covol_eq_prod_gsVec bL, covol_eq_prod_gsVec bM, covol_eq_prod_gsVec bQ]
    have hbQ_eq : (fun j : Fin s => (bQ j : E)) = q := by
      funext j; simp [bQ]
    rw [hbL_coe, hbQ_eq, Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => by rw [hgs.1 i]
    · refine Finset.prod_congr rfl fun j _ => by rw [hgs.2 j]
  have hdeg : degAr L = degAr M + degAr (quotLat L M) := by
    unfold degAr
    rw [hcov, Real.log_mul (covol_pos M).ne' (covol_pos (quotLat L M)).ne']
    ring
  exact ⟨hDiscQ, hrkQ ▸ hrkL, hcov, hdeg⟩

/-- Discrete topology passes to any orthogonal quotient `quotLat L M` of a saturated sublattice. -/
lemma discreteTopology_quotLat {L M : Submodule ℤ E} [DiscreteTopology L] (hM : IsSaturated L M) :
    DiscreteTopology (quotLat L M) :=
  (quotLat_exact_additivity hM).1

/-- Exact rank additivity `rk L = rk M + rk (quotLat L M)` for saturated `M ≤ L`. -/
theorem rk_add_quotLat {L M : Submodule ℤ E} [DiscreteTopology L] (hM : IsSaturated L M) :
    rk L = rk M + rk (quotLat L M) :=
  (quotLat_exact_additivity hM).2.1

/-- Exact covolume multiplicativity `covol L = covol M * covol (quotLat L M)` for saturated `M ≤ L`. -/
theorem covol_eq_mul_quotLat {L M : Submodule ℤ E} [DiscreteTopology L] (hM : IsSaturated L M) :
    covol L = covol M * covol (quotLat L M) :=
  (quotLat_exact_additivity hM).2.2.1

/-- Exact Arakelov degree additivity `degAr L = degAr M + degAr (quotLat L M)` for saturated `M ≤ L`. -/
theorem degAr_eq_add_quotLat {L M : Submodule ℤ E} [DiscreteTopology L] (hM : IsSaturated L M) :
    degAr L = degAr M + degAr (quotLat L M) :=
  (quotLat_exact_additivity hM).2.2.2

lemma quotLat_ne_bot_of_lt {L M : Submodule ℤ E} (hM : IsSaturated L M) (hML : M ≠ L) :
    quotLat L M ≠ ⊥ := by
  intro h0
  apply hML
  apply le_antisymm hM.1
  intro x hxL
  have hmem : projOrth M x ∈ quotLat L M := ⟨x, hxL, rfl⟩
  rw [h0, Submodule.mem_bot] at hmem
  exact hM.2 x hxL ((projOrth_eq_zero_iff M x).mp hmem)

/-- Pullback / lift of a sublattice `K ≤ quotLat L M` back to `L`:
`liftSub L M K = { x ∈ L | projOrth M x ∈ K }`. -/
def liftSub (L M K : Submodule ℤ E) : Submodule ℤ E :=
  L ⊓ K.comap ((projOrth M).restrictScalars ℤ)

lemma le_liftSub {L M K : Submodule ℤ E} (hM : M ≤ L) : M ≤ liftSub L M K := by
  intro x hxM
  refine ⟨hM hxM, ?_⟩
  change projOrth M x ∈ K
  rw [(projOrth_eq_zero_iff M x).mpr (Submodule.subset_span hxM)]
  exact K.zero_mem

lemma liftSub_le (L M K : Submodule ℤ E) : liftSub L M K ≤ L := inf_le_left

lemma quotLat_liftSub {L M K : Submodule ℤ E} (hK : K ≤ quotLat L M) :
    quotLat (liftSub L M K) M = K := by
  ext y
  constructor
  · rintro ⟨x, ⟨_, hxK⟩, rfl⟩
    exact hxK
  · intro hyK
    obtain ⟨x, hxL, rfl⟩ := hK hyK
    exact ⟨x, ⟨hxL, hyK⟩, rfl⟩

lemma liftSub_quotLat {L M N : Submodule ℤ E} (_hM : IsSaturated L M) (hN : IsSaturated L N)
    (hMN : M ≤ N) :
    liftSub L M (quotLat N M) = N := by
  apply le_antisymm
  · rintro x ⟨hxL, hxQ⟩
    rcases hxQ with ⟨y, hyN, hyx⟩
    have hsub : x - y ∈ Submodule.span ℝ (M : Set E) := by
      rw [← projOrth_eq_zero_iff M, map_sub]
      change projOrth M x - projOrth M y = 0
      have hyx' : projOrth M y = projOrth M x := hyx
      rw [hyx', sub_self]
    have hsubN : x - y ∈ Submodule.span ℝ (N : Set E) :=
      Submodule.span_mono (show (M : Set E) ⊆ (N : Set E) from hMN) hsub
    have hxsp : x ∈ Submodule.span ℝ (N : Set E) := by
      have := Submodule.add_mem _ hsubN (Submodule.subset_span hyN)
      simpa using this
    exact hN.2 x hxL hxsp
  · intro x hxN
    exact ⟨hN.1 hxN, ⟨x, hxN, rfl⟩⟩

lemma isSaturated_quotLat {L M N : Submodule ℤ E} (_hM : IsSaturated L M) (hN : IsSaturated L N)
    (hMN : M ≤ N) :
    IsSaturated (quotLat L M) (quotLat N M) := by
  refine ⟨Submodule.map_mono hN.1, ?_⟩
  intro y hyL hysp
  rcases hyL with ⟨x, hxL, rfl⟩
  have hsp_eq : Submodule.span ℝ ((quotLat N M : Submodule ℤ E) : Set E) =
      (Submodule.span ℝ (N : Set E)).map (projOrth M) := by
    rw [Submodule.map_span]
    rfl
  rw [hsp_eq] at hysp
  rcases hysp with ⟨z, hzN, hzx⟩
  have hdiff : x - z ∈ Submodule.span ℝ (M : Set E) := by
    rw [← projOrth_eq_zero_iff M, map_sub]
    have hzx' : projOrth M z = projOrth M x := hzx
    rw [hzx', sub_self]
  have hxspN : x ∈ Submodule.span ℝ (N : Set E) := by
    have h1 := Submodule.span_mono (show (M : Set E) ⊆ (N : Set E) from hMN) hdiff
    have h2 := Submodule.add_mem _ h1 hzN
    simpa using h2
  exact ⟨x, hN.2 x hxL hxspN, rfl⟩

lemma isSaturated_liftSub {L M K : Submodule ℤ E}
    (hK : IsSaturated (quotLat L M) K) :
    IsSaturated L (liftSub L M K) := by
  refine ⟨liftSub_le L M K, fun x hxL hxsp => ⟨hxL, ?_⟩⟩
  change projOrth M x ∈ K
  have hpx_sp : projOrth M x ∈ Submodule.span ℝ (K : Set E) := by
    have hmap : projOrth M x ∈ (Submodule.span ℝ ((liftSub L M K : Submodule ℤ E) : Set E)).map (projOrth M) :=
      ⟨x, hxsp, rfl⟩
    rw [Submodule.map_span] at hmap
    have hsub : (projOrth M) '' ((liftSub L M K : Submodule ℤ E) : Set E) ⊆ (K : Set E) := by
      rintro _ ⟨y, ⟨_, hyK⟩, rfl⟩; exact hyK
    exact Submodule.span_mono hsub hmap
  exact hK.2 (projOrth M x) ⟨x, hxL, rfl⟩ hpx_sp

/-- **Third Isomorphism / Quotient-of-Quotient Identity**:
for `M ≤ N ≤ L`, `quotLat (quotLat L M) (quotLat N M) = quotLat L N`! -/
theorem quotLat_quotLat {L M N : Submodule ℤ E} (hMN : M ≤ N) :
    quotLat (quotLat L M) (quotLat N M) = quotLat L N := by
  have hproj_eq : ∀ y ∈ (Submodule.span ℝ (M : Set E))ᗮ,
      projOrth (quotLat N M) y = projOrth N y := by
    intro y hyM
    have hspQ : Submodule.span ℝ ((quotLat N M : Submodule ℤ E) : Set E) ≤
        Submodule.span ℝ (N : Set E) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, hzN, rfl⟩
      have h1 : z - projOrth M z ∈ Submodule.span ℝ (N : Set E) :=
        Submodule.span_mono (show (M : Set E) ⊆ (N : Set E) from hMN) (sub_projOrth_mem_span M z)
      have h2 := Submodule.sub_mem _ (Submodule.subset_span hzN) h1
      simpa using h2
    have hsubN : y - projOrth N y ∈ Submodule.span ℝ ((quotLat N M : Submodule ℤ E) : Set E) := by
      have h1 : y - projOrth N y ∈ Submodule.span ℝ (N : Set E) := sub_projOrth_mem_span N y
      have h2 : projOrth M (y - projOrth N y) = y - projOrth N y := by
        rw [map_sub, projOrth_eq_self_of_mem_orthogonal M hyM]
        have horthN : projOrth N y ∈ (Submodule.span ℝ (M : Set E))ᗮ := by
          intro u hu
          exact projOrth_mem_orthogonal N y u
            (Submodule.span_mono (show (M : Set E) ⊆ (N : Set E) from hMN) hu)
        rw [projOrth_eq_self_of_mem_orthogonal M horthN]
      rw [← h2]
      have hmap : projOrth M (y - projOrth N y) ∈ (Submodule.span ℝ (N : Set E)).map (projOrth M) :=
        ⟨y - projOrth N y, h1, rfl⟩
      rw [Submodule.map_span] at hmap
      exact hmap
    have horthQ : projOrth N y ∈ (Submodule.span ℝ ((quotLat N M : Submodule ℤ E) : Set E))ᗮ := by
      intro u hu
      exact projOrth_mem_orthogonal N y u (hspQ hu)
    have h0 : projOrth (quotLat N M) (y - projOrth N y) = 0 :=
      (projOrth_eq_zero_iff (quotLat N M) _).mpr hsubN
    rw [map_sub, projOrth_eq_self_of_mem_orthogonal (quotLat N M) horthQ] at h0
    exact sub_eq_zero.mp h0
  ext w
  constructor
  · rintro ⟨y, ⟨x, hxL, rfl⟩, rfl⟩
    refine ⟨x, hxL, ?_⟩
    change projOrth N x = projOrth (quotLat N M) (projOrth M x)
    rw [hproj_eq _ (projOrth_mem_orthogonal M x), projOrth_comp_of_le hMN x]
  · rintro ⟨x, hxL, rfl⟩
    refine ⟨projOrth M x, ⟨x, hxL, rfl⟩, ?_⟩
    change projOrth (quotLat N M) (projOrth M x) = projOrth N x
    rw [hproj_eq _ (projOrth_mem_orthogonal M x), projOrth_comp_of_le hMN x]

end SaturatedAndQuotient

/-! ## Section 2: Grayson–Stuhler Supermodularity of Arakelov Degree -/

section Supermodularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Grayson–Stuhler Supermodularity for Saturated Sublattices**:
for any two saturated sublattices `M₁, M₂` of a discrete lattice `L ⊂ E`:
1. `rk (M₁ ⊔ M₂) + rk (M₁ ⊓ M₂) = rk M₁ + rk M₂`,
2. `covol (M₁ ⊔ M₂) * covol (M₁ ⊓ M₂) ≤ covol M₁ * covol M₂`,
3. `degAr M₁ + degAr M₂ ≤ degAr (M₁ ⊔ M₂) + degAr (M₁ ⊓ M₂)`,
4. Same inequalities hold for the saturated join `satJoin L M₁ M₂`! -/
theorem grayson_stuhler_supermodular {L M₁ M₂ : Submodule ℤ E} [DiscreteTopology L]
    (h₁ : IsSaturated L M₁) (h₂ : IsSaturated L M₂) :
    rk (M₁ ⊔ M₂) + rk (M₁ ⊓ M₂) = rk M₁ + rk M₂ ∧
    covol (M₁ ⊔ M₂) * covol (M₁ ⊓ M₂) ≤ covol M₁ * covol M₂ ∧
    degAr M₁ + degAr M₂ ≤ degAr (M₁ ⊔ M₂) + degAr (M₁ ⊓ M₂) ∧
    rk (satJoin L M₁ M₂) + rk (M₁ ⊓ M₂) = rk M₁ + rk M₂ ∧
    covol (satJoin L M₁ M₂) * covol (M₁ ⊓ M₂) ≤ covol M₁ * covol M₂ ∧
    degAr M₁ + degAr M₂ ≤ degAr (satJoin L M₁ M₂) + degAr (M₁ ⊓ M₂) := by
  have hsupL : M₁ ⊔ M₂ ≤ L := sup_le h₁.1 h₂.1
  have : DiscreteTopology M₁ := discreteTopology_of_le h₁.1
  have : DiscreteTopology M₂ := discreteTopology_of_le h₂.1
  have : DiscreteTopology ↥(M₁ ⊔ M₂) := discreteTopology_of_le hsupL
  have : DiscreteTopology ↥(M₁ ⊓ M₂) := discreteTopology_of_le (inf_le_left.trans h₁.1)
  have : DiscreteTopology ↥(satJoin L M₁ M₂) := discreteTopology_of_le (saturation_le L _)
  have h1_sup : IsSaturated (M₁ ⊔ M₂) M₁ := isSaturated_of_le_of_isSaturated h₁ le_sup_left hsupL
  have hI_M₂ : IsSaturated M₂ (M₁ ⊓ M₂) :=
    isSaturated_of_le_of_isSaturated (isSaturated_inf h₁ h₂) inf_le_right h₂.1
  have : DiscreteTopology ↥(quotLat (M₁ ⊔ M₂) M₁) := discreteTopology_quotLat h1_sup
  have : DiscreteTopology ↥(quotLat M₂ (M₁ ⊓ M₂)) := discreteTopology_quotLat hI_M₂
  have himg : ∀ y ∈ quotLat M₂ (M₁ ⊓ M₂), projOrth M₁ y ∈ quotLat (M₁ ⊔ M₂) M₁ := by
    rintro _ ⟨m₂, hm₂, rfl⟩
    change projOrth M₁ (projOrth (M₁ ⊓ M₂) m₂) ∈ quotLat (M₁ ⊔ M₂) M₁
    rw [projOrth_comp_of_le inf_le_left m₂]
    exact ⟨m₂, (le_sup_right : M₂ ≤ M₁ ⊔ M₂) hm₂, rfl⟩
  let φ : quotLat M₂ (M₁ ⊓ M₂) →ₗ[ℤ] quotLat (M₁ ⊔ M₂) M₁ :=
    { toFun := fun y => ⟨projOrth M₁ y.1, himg y.1 y.2⟩
      map_add' := fun a b => Subtype.ext (map_add (projOrth M₁) a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul (projOrth M₁) c a.1) }
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have h0 : projOrth M₁ (a.1 - b.1) = 0 := by
      rw [map_sub]
      have hval : projOrth M₁ a.1 = projOrth M₁ b.1 := congrArg (fun z : quotLat (M₁ ⊔ M₂) M₁ => (z : E)) hab
      exact sub_eq_zero.mpr hval
    obtain ⟨m₂, hm₂, hm₂eq⟩ := (quotLat M₂ (M₁ ⊓ M₂)).sub_mem a.2 b.2
    have hm₂_proj : projOrth M₁ m₂ = 0 := by
      rw [← projOrth_comp_of_le inf_le_left m₂]
      have hm₂eq' : projOrth (M₁ ⊓ M₂) m₂ = a.1 - b.1 := hm₂eq
      rw [hm₂eq', h0]
    have hm₂_M₁ : m₂ ∈ M₁ := h₁.2 m₂ (h₂.1 hm₂) ((projOrth_eq_zero_iff M₁ m₂).mp hm₂_proj)
    have hm₂_I : m₂ ∈ M₁ ⊓ M₂ := ⟨hm₂_M₁, hm₂⟩
    have hsub0 : a.1 - b.1 = 0 := by
      have hm₂eq' : projOrth (M₁ ⊓ M₂) m₂ = a.1 - b.1 := hm₂eq
      rw [← hm₂eq']
      exact (projOrth_eq_zero_iff (M₁ ⊓ M₂) m₂).mpr (Submodule.subset_span hm₂_I)
    exact sub_eq_zero.mp hsub0
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨w, x, hxsup, rfl⟩
    have hxsup' : x ∈ M₁ ⊔ M₂ := hxsup
    rw [Submodule.mem_sup] at hxsup'
    rcases hxsup' with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
    refine ⟨⟨projOrth (M₁ ⊓ M₂) m₂, ⟨m₂, hm₂, rfl⟩⟩, Subtype.ext ?_⟩
    change projOrth M₁ (projOrth (M₁ ⊓ M₂) m₂) = projOrth M₁ (m₁ + m₂)
    rw [projOrth_comp_of_le inf_le_left m₂, map_add,
      (projOrth_eq_zero_iff M₁ m₁).mpr (Submodule.subset_span hm₁), zero_add]
  let e : quotLat M₂ (M₁ ⊓ M₂) ≃ₗ[ℤ] quotLat (M₁ ⊔ M₂) M₁ := LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hrkQ : rk (quotLat (M₁ ⊔ M₂) M₁) = rk (quotLat M₂ (M₁ ⊓ M₂)) := e.finrank_eq.symm
  have hrk_sup : rk (M₁ ⊔ M₂) + rk (M₁ ⊓ M₂) = rk M₁ + rk M₂ := by
    have hA := rk_add_quotLat h1_sup
    have hB := rk_add_quotLat hI_M₂
    omega
  let b := Module.finBasis ℤ (quotLat M₂ (M₁ ⊓ M₂))
  have hcovQ : covol (quotLat (M₁ ⊔ M₂) M₁) ≤ covol (quotLat M₂ (M₁ ⊓ M₂)) := by
    rw [covol_eq_sqrt_det_gram _ (b.map e), covol_eq_sqrt_det_gram _ b]
    have hlip : ∀ c : Fin (Module.finrank ℤ (quotLat M₂ (M₁ ⊓ M₂))) → ℝ,
        ‖∑ i, c i • ((b.map e i : quotLat (M₁ ⊔ M₂) M₁) : E)‖ ≤
          1 * ‖∑ i, c i • (b i : E)‖ := by
      intro c
      rw [one_mul]
      have heq : ∑ i, c i • ((b.map e i : quotLat (M₁ ⊔ M₂) M₁) : E) =
          projOrth M₁ (∑ i, c i • (b i : E)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
      rw [heq]
      exact norm_projOrth_le M₁ _
    have hdet := gram_det_le (fun i => (b i : E)) (fun i => ((b.map e i : quotLat (M₁ ⊔ M₂) M₁) : E)) 1 hlip
    rw [one_pow, one_mul] at hdet
    exact Real.sqrt_le_sqrt hdet
  have hcov_sup : covol (M₁ ⊔ M₂) * covol (M₁ ⊓ M₂) ≤ covol M₁ * covol M₂ := by
    rw [covol_eq_mul_quotLat h1_sup, covol_eq_mul_quotLat hI_M₂]
    have hm1_pos := (covol_pos M₁).le
    have hI_pos := (covol_pos (M₁ ⊓ M₂)).le
    have hmul := mul_le_mul_of_nonneg_left hcovQ (mul_nonneg hm1_pos hI_pos)
    linarith
  have hdeg_sup : degAr M₁ + degAr M₂ ≤ degAr (M₁ ⊔ M₂) + degAr (M₁ ⊓ M₂) := by
    have hpos1 : 0 < covol (M₁ ⊔ M₂) * covol (M₁ ⊓ M₂) :=
      mul_pos (covol_pos _) (covol_pos _)
    have hlog := Real.log_le_log hpos1 hcov_sup
    rw [Real.log_mul (covol_pos _).ne' (covol_pos _).ne',
      Real.log_mul (covol_pos _).ne' (covol_pos _).ne'] at hlog
    unfold degAr
    linarith
  have hsat_rk : rk (satJoin L M₁ M₂) = rk (M₁ ⊔ M₂) := rk_saturation hsupL
  have hsat_cov : covol (satJoin L M₁ M₂) ≤ covol (M₁ ⊔ M₂) ∧
      degAr (M₁ ⊔ M₂) ≤ degAr (satJoin L M₁ M₂) := covol_saturation_le hsupL
  have hcov_sat : covol (satJoin L M₁ M₂) * covol (M₁ ⊓ M₂) ≤ covol M₁ * covol M₂ :=
    (mul_le_mul_of_nonneg_right hsat_cov.1 (covol_pos _).le).trans hcov_sup
  exact ⟨hrk_sup, hcov_sup, hdeg_sup, hsat_rk ▸ hrk_sup, hcov_sat, by linarith [hsat_cov.2]⟩

end Supermodularity

/-! ## Section 3: Finiteness, Maximal Destabilizing Sublattice & Canonical HN Filtration -/

section HarderNarasimhan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper: decomposing a vector `w` along a nonzero vector `v₁` and its orthogonal projection
`projOrth (span ℤ {v₁}) w`. -/
private lemma eq_add_smul_projOrth_singleton {v₁ : E} (hv₁ : v₁ ≠ 0) (w : E) :
    let M₁ := Submodule.span ℤ ({v₁} : Set E)
    w = projOrth M₁ w + (inner ℝ w v₁ / ‖v₁‖ ^ 2) • v₁ := by
  intro M₁
  have hsp : Submodule.span ℝ (M₁ : Set E) = Submodule.span ℝ ({v₁} : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ ({v₁} : Set E)]
  have hsub : w - projOrth M₁ w ∈ Submodule.span ℝ ({v₁} : Set E) := by
    rw [← hsp]; exact sub_projOrth_mem_span M₁ w
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hsub
  have horth : inner ℝ (projOrth M₁ w) v₁ = 0 := by
    rw [real_inner_comm]
    exact projOrth_mem_orthogonal M₁ w v₁ (Submodule.subset_span (Submodule.subset_span rfl))
  have hinner : inner ℝ w v₁ = t * ‖v₁‖ ^ 2 := by
    have hw : w = projOrth M₁ w + t • v₁ := by
      have : w - projOrth M₁ w = t • v₁ := ht.symm
      rw [← this]; abel
    rw [hw, inner_add_left, horth, zero_add, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hn0 : ‖v₁‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv₁)
  have ht_eq : t = inner ℝ w v₁ / ‖v₁‖ ^ 2 := by
    rw [hinner, mul_div_cancel_right₀ t hn0]
  rw [← ht_eq, ht]
  abel

/-- **Inductive Norm Bound for Bounded-Covolume Lattices**:
for every rank `r`, lower bound `δ > 0` on `λ₁(M)`, and upper bound `B > 0` on `covol M`,
there exists a uniform radius `R ≥ 0` such that every discrete lattice `M ⊂ E` of rank `r`
with `δ ≤ λ₁(M)` and `covol M ≤ B` contains `r` `ℝ`-linearly independent vectors inside `B̄(0, R)`. -/
theorem exists_norm_bound_of_covol_le :
    ∀ (r : ℕ) {δ B : ℝ}, 0 < δ → 0 < B →
      ∃ R : ℝ, 0 ≤ R ∧
        ∀ (M : Submodule ℤ E) [DiscreteTopology M],
          rk M = r → (M ≠ ⊥ → δ ≤ lambda1 M) → covol M ≤ B →
          ∃ w : Fin r → E, (∀ i, w i ∈ M) ∧ LinearIndependent ℝ w ∧ ∀ i, ‖w i‖ ≤ R
  | 0, _, _, _, _ =>
    ⟨0, le_rfl, fun _ _ _ _ _ => ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩⟩
  | r + 1, δ, B, hδ, hB => by
    obtain ⟨R', hR'0, hIH⟩ := exists_norm_bound_of_covol_le r (half_pos hδ) (div_pos hB hδ)
    set R₀ : ℝ := Real.sqrt (r + 1 : ℝ) * B ^ (1 / (r + 1 : ℝ))
    have hR₀0 : 0 ≤ R₀ := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hB.le _)
    refine ⟨max R₀ (R' + R₀), le_trans hR₀0 (le_max_left _ _), ?_⟩
    intro M hDiscM hrkM hlamM hcovM
    have hM0 : M ≠ ⊥ := by
      intro hbot
      subst hbot
      have hr0 : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
      omega
    have hlam_ge : δ ≤ lambda1 M := hlamM hM0
    obtain ⟨v₁, hv₁M, hv₁0, hv₁_norm⟩ := exists_norm_eq_lambda1 M hM0
    have hv₁_le_R₀ : ‖v₁‖ ≤ R₀ := by
      have hH := lambda1_le_hermite M hM0
      rw [← hv₁_norm, hrkM] at hH
      have hrpow : (covol M) ^ (1 / ((r + 1 : ℕ) : ℝ)) ≤ B ^ (1 / ((r + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (covol_pos M).le hcovM (by positivity)
      have hcast : ((r + 1 : ℕ) : ℝ) = (r + 1 : ℝ) := by push_cast; rfl
      rw [hcast] at hH hrpow
      exact hH.trans (mul_le_mul_of_nonneg_left hrpow (Real.sqrt_nonneg _))
    let M₁ : Submodule ℤ E := Submodule.span ℤ ({v₁} : Set E)
    have hM₁_le : M₁ ≤ M := Submodule.span_le.mpr (by rintro _ rfl; exact hv₁M)
    have hM₁_sat : IsSaturated M M₁ := by
      refine ⟨hM₁_le, fun x hxM hxsp => ?_⟩
      have hsp : Submodule.span ℝ (M₁ : Set E) = Submodule.span ℝ ({v₁} : Set E) := by
        rw [← Submodule.span_span_of_tower ℤ ℝ ({v₁} : Set E)]
      rw [hsp] at hxsp
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hxsp
      let k : ℤ := round t
      have hdiff_mem : x - k • v₁ ∈ M := M.sub_mem hxM (M.smul_mem k hv₁M)
      have hdiff_eq : x - k • v₁ = (t - (k : ℝ)) • v₁ := by
        rw [← ht, sub_smul, Int.cast_smul_eq_zsmul]
      have hdiff_norm : ‖x - k • v₁‖ < lambda1 M := by
        rw [hdiff_eq, norm_smul, Real.norm_eq_abs, ← hv₁_norm]
        have habs : |t - (k : ℝ)| ≤ 1 / 2 := abs_sub_round t
        have hpos : 0 < ‖v₁‖ := norm_pos_iff.mpr hv₁0
        nlinarith
      have hdiff0 : x - k • v₁ = 0 := by
        by_contra hne
        exact not_le.mpr hdiff_norm (lambda1_le_norm M hdiff_mem hne)
      have hxk : x = k • v₁ := sub_eq_zero.mp hdiff0
      rw [hxk]
      exact Submodule.smul_mem M₁ k (Submodule.subset_span rfl)
    have hcovM₁ : covol M₁ = ‖v₁‖ := covol_span_singleton hv₁0
    have hrkM₁ : rk M₁ = 1 := by
      have : DiscreteTopology M₁ := discreteTopology_of_le hM₁_le
      unfold rk
      rw [finrank_int_eq_finrank_real_span M₁,
        show Submodule.span ℝ (M₁ : Set E) = Submodule.span ℝ ({v₁} : Set E) by
          rw [← Submodule.span_span_of_tower ℤ ℝ ({v₁} : Set E)],
        finrank_span_singleton hv₁0]
    let Q := quotLat M M₁
    have hDiscQ : DiscreteTopology Q := discreteTopology_quotLat hM₁_sat
    have hrkQ : rk Q = r := by
      have hadd : rk M = rk M₁ + rk Q := rk_add_quotLat hM₁_sat
      omega
    have hcovQ : covol Q ≤ B / δ := by
      have hmul := covol_eq_mul_quotLat hM₁_sat
      rw [hcovM₁] at hmul
      have hv₁_ge_δ : δ ≤ ‖v₁‖ := hv₁_norm ▸ hlam_ge
      rw [le_div_iff₀ hδ]
      have hQpos : 0 ≤ covol Q := (covol_pos Q).le
      nlinarith
    have hlamQ : Q ≠ ⊥ → δ / 2 ≤ lambda1 Q := by
      intro hQ0
      obtain ⟨q, hqQ, hq0, hq_norm⟩ := exists_norm_eq_lambda1 Q hQ0
      rw [← hq_norm]
      rcases hqQ with ⟨w, hwM, hwq⟩
      have hwq' : projOrth M₁ w = q := hwq
      let t : ℝ := inner ℝ w v₁ / ‖v₁‖ ^ 2
      let k : ℤ := round t
      let w' : E := w - k • v₁
      have hw'M : w' ∈ M := M.sub_mem hwM (M.smul_mem k hv₁M)
      have hw'_eq : w' = q + (t - (k : ℝ)) • v₁ := by
        have hdecomp := eq_add_smul_projOrth_singleton hv₁0 w
        change w = projOrth M₁ w + t • v₁ at hdecomp
        dsimp only [w']
        rw [hdecomp, hwq', ← Int.cast_smul_eq_zsmul ℝ k v₁, sub_smul]
        abel
      have hq_orth : inner ℝ q v₁ = 0 := by
        rw [← hwq', real_inner_comm]
        exact projOrth_mem_orthogonal M₁ w v₁ (Submodule.subset_span (Submodule.subset_span rfl))
      have hw'_ne0 : w' ≠ 0 := by
        intro h0
        have hp0 : projOrth M₁ w' = 0 := by rw [h0, map_zero]
        have hp_eq : projOrth M₁ w' = q := by
          dsimp only [w']
          rw [map_sub, map_zsmul, hwq',
            (projOrth_eq_zero_iff M₁ v₁).mpr (Submodule.subset_span (Submodule.subset_span rfl)),
            smul_zero, sub_zero]
        exact hq0 (hp_eq ▸ hp0)
      have hpyth : ‖w'‖ ^ 2 = ‖q‖ ^ 2 + (t - (k : ℝ)) ^ 2 * ‖v₁‖ ^ 2 := by
        rw [hw'_eq, norm_add_sq_real, real_inner_smul_right, hq_orth, mul_zero, mul_zero, add_zero,
          norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have habs : (t - (k : ℝ)) ^ 2 ≤ 1 / 4 := by
        have h1 : |t - (k : ℝ)| ≤ 1 / 2 := abs_sub_round t
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [sq_abs] at h2
        norm_num at h2
        exact h2
      have hge_v₁ : ‖v₁‖ ≤ ‖w'‖ := by
        rw [hv₁_norm]; exact lambda1_le_norm M hw'M hw'_ne0
      have hsq_ge : ‖v₁‖ ^ 2 ≤ ‖w'‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hge_v₁ 2
      have hv₁_ge_δ : δ ≤ ‖v₁‖ := hv₁_norm ▸ hlam_ge
      nlinarith [norm_nonneg q, sq_nonneg ‖v₁‖]
    obtain ⟨q, hqQ, hqli, hqR'⟩ := hIH Q hrkQ hlamQ hcovQ
    choose raw hrawM hrawProj using fun i : Fin r => hqQ i
    let w_tail : Fin r → E := fun i =>
      raw i - (round (inner ℝ (raw i) v₁ / ‖v₁‖ ^ 2) : ℤ) • v₁
    have hw_tail_M : ∀ i, w_tail i ∈ M := fun i => M.sub_mem (hrawM i) (M.smul_mem _ hv₁M)
    have hw_tail_proj : ∀ i, projOrth M₁ (w_tail i) = q i := by
      intro i
      dsimp only [w_tail]
      rw [map_sub, map_zsmul,
        (projOrth_eq_zero_iff M₁ v₁).mpr (Submodule.subset_span (Submodule.subset_span rfl)),
        smul_zero, sub_zero]
      exact hrawProj i
    have hw_tail_norm : ∀ i, ‖w_tail i‖ ≤ R' + R₀ := by
      intro i
      let t := inner ℝ (raw i) v₁ / ‖v₁‖ ^ 2
      let k := round t
      have hdecomp := eq_add_smul_projOrth_singleton hv₁0 (raw i)
      have hproj_i : projOrth M₁ (raw i) = q i := hrawProj i
      have hwt_eq : w_tail i = q i + (t - (k : ℝ)) • v₁ := by
        have h1 : raw i = q i + t • v₁ := by rw [← hproj_i]; exact hdecomp
        have h2 : w_tail i = raw i - k • v₁ := rfl
        rw [h2, h1, ← Int.cast_smul_eq_zsmul ℝ k v₁, sub_smul]
        abel
      calc ‖w_tail i‖ ≤ ‖q i‖ + ‖(t - (k : ℝ)) • v₁‖ := by rw [hwt_eq]; exact norm_add_le _ _
        _ = ‖q i‖ + |t - (k : ℝ)| * ‖v₁‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ R' + (1 / 2) * R₀ := by
            have habs : |t - (k : ℝ)| ≤ 1 / 2 := abs_sub_round t
            nlinarith [hqR' i, hv₁_le_R₀, norm_nonneg v₁]
        _ ≤ R' + R₀ := by linarith
    refine ⟨Fin.cons v₁ w_tail, ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases hv₁M hw_tail_M i
    · rw [Fintype.linearIndependent_iff]
      intro c hc
      have hproj0 : ∑ i : Fin r, c i.succ • q i = 0 := by
        have h1 := congrArg (projOrth M₁) hc
        rw [map_zero, map_sum, Fin.sum_univ_succ, map_smul, Fin.cons_zero,
          (projOrth_eq_zero_iff M₁ v₁).mpr (Submodule.subset_span (Submodule.subset_span rfl)),
          smul_zero, zero_add] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => by rw [map_smul, Fin.cons_succ, hw_tail_proj i]
      have hc_succ : ∀ i : Fin r, c i.succ = 0 :=
        Fintype.linearIndependent_iff.mp hqli (fun i => c i.succ) hproj0
      have hc0 : c 0 = 0 := by
        rw [Fin.sum_univ_succ, Fin.cons_zero] at hc
        simp only [Fin.cons_succ] at hc
        have htail0 : ∑ i : Fin r, c i.succ • w_tail i = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hc_succ i, zero_smul]
        rw [htail0, add_zero] at hc
        exact (smul_eq_zero.mp hc).resolve_right hv₁0
      intro i
      exact Fin.cases hc0 hc_succ i
    · intro i
      refine Fin.cases (hv₁_le_R₀.trans (le_max_left _ _))
        (fun j => (hw_tail_norm j).trans (le_max_right _ _)) i

/-- **Finiteness of Saturated Sublattices of Bounded Covolume**:
every discrete Euclidean lattice `L ⊂ E` has only finitely many saturated sublattices `M ≤ L`
with `covol M ≤ B`. -/
theorem finite_saturated_covol_le (L : Submodule ℤ E) [DiscreteTopology L] (B : ℝ) :
    { M : Submodule ℤ E | IsSaturated L M ∧ covol M ≤ B }.Finite := by
  classical
  have hsub : { M : Submodule ℤ E | IsSaturated L M ∧ covol M ≤ B } ⊆
      ⋃ r ∈ Finset.range (rk L + 1),
        { M : Submodule ℤ E | IsSaturated L M ∧ rk M = r ∧ covol M ≤ B } := by
    rintro M ⟨hM, hcov⟩
    refine Set.mem_iUnion₂.mpr ⟨rk M, Finset.mem_range.mpr (Nat.lt_succ_of_le
      (RHDirect.Stage3ThetaSiegelBridge.rk_le_of_le hM.1)), hM, rfl, hcov⟩
  refine Set.Finite.subset ((Finset.range (rk L + 1)).finite_toSet.biUnion fun r _ => ?_) hsub
  cases r with
  | zero =>
    refine (Set.finite_singleton (⊥ : Submodule ℤ E)).subset ?_
    rintro M ⟨hM, hr0, _⟩
    have : DiscreteTopology M := discreteTopology_of_le hM.1
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hpos := rk_pos_of_ne_bot M hne
    omega
  | succ r =>
    by_cases hL0 : L = ⊥
    · subst hL0
      refine Set.finite_empty.subset ?_
      rintro M ⟨hM, hr, _⟩
      have hM0 : M = ⊥ := le_bot_iff.mp hM.1
      subst hM0
      have : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
      omega
    · have hδ : 0 < lambda1 L := lambda1_pos L hL0
      have hBpos : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
      obtain ⟨R, _, hbound⟩ := exists_norm_bound_of_covol_le (E := E) (r + 1) hδ hBpos
      let F : Finset E := (lattice_inter_closedBall_finite L R).toFinset
      let mkLat : (Fin (r + 1) → E) → Submodule ℤ E :=
        fun w => saturation L (Submodule.span ℤ (Set.range w))
      refine ((Fintype.piFinset fun _ : Fin (r + 1) => F).image mkLat).finite_toSet.subset ?_
      rintro M ⟨hM, hrM, hcovM⟩
      have : DiscreteTopology M := discreteTopology_of_le hM.1
      have hlamM : M ≠ ⊥ → lambda1 L ≤ lambda1 M :=
        fun hM0 => RHDirect.Stage3ThetaSiegelBridge.lambda1_le_of_le hM.1 hM0
      obtain ⟨w, hwM, hwli, hwR⟩ := hbound M hrM hlamM (hcovM.trans (le_max_left B 1))
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨w, ?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro i
        exact (lattice_inter_closedBall_finite L R).mem_toFinset.mpr
          ⟨hM.1 (hwM i), mem_closedBall_zero_iff.mpr (hwR i)⟩
      · let N := Submodule.span ℤ (Set.range w)
        have hNM : N ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hwM i)
        have hNL : N ≤ L := hNM.trans hM.1
        have : DiscreteTopology N := discreteTopology_of_le hNL
        have hrkN : rk N = r + 1 := by
          unfold rk
          rw [finrank_int_eq_finrank_real_span N,
            show Submodule.span ℝ (N : Set E) = Submodule.span ℝ (Set.range w) by
              rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range w)],
            finrank_span_eq_card hwli, Fintype.card_fin]
        have hmk_le : mkLat w ≤ M := saturation_le_of_isSaturated hNM hM
        have hmk_rk : rk (mkLat w) = rk M := by
          rw [rk_saturation hNL, hrkN, hrM]
        exact eq_of_isSaturated_of_rk_eq (isSaturated_saturation hNL) hM.1 hmk_le hmk_rk

/-- **Finiteness of Saturated Sublattices with Slope Bounded Below**:
for every `c : ℝ`, there are only finitely many nonzero saturated sublattices `M ≤ L`
satisfying `c ≤ slope M`. -/
theorem finite_saturated_slope_ge (L : Submodule ℤ E) [DiscreteTopology L] (c : ℝ) :
    { M : Submodule ℤ E | IsSaturated L M ∧ M ≠ ⊥ ∧ c ≤ ArakelovCovolume.slope M }.Finite := by
  let B : ℝ := Real.exp (max 0 (-c * (rk L : ℝ)))
  refine (finite_saturated_covol_le L B).subset ?_
  rintro M ⟨hM, hM0, hc⟩
  refine ⟨hM, ?_⟩
  have : DiscreteTopology M := discreteTopology_of_le hM.1
  have hrpos : (0 : ℝ) < (rk M : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot M hM0)
  have hrle : (rk M : ℝ) ≤ (rk L : ℝ) :=
    Nat.cast_le.mpr (RHDirect.Stage3ThetaSiegelBridge.rk_le_of_le hM.1)
  unfold ArakelovCovolume.slope degAr at hc
  rw [le_div_iff₀ hrpos] at hc
  have hlog : Real.log (covol M) ≤ max 0 (-c * (rk L : ℝ)) := by
    by_cases hcn : 0 ≤ -c
    · exact (by linarith : Real.log (covol M) ≤ -c * (rk M : ℝ)).trans
        ((mul_le_mul_of_nonneg_left hrle hcn).trans (le_max_right _ _))
    · push Not at hcn
      have hneg : -c * (rk M : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcn.le hrpos.le
      exact (by linarith : Real.log (covol M) ≤ -c * (rk M : ℝ)).trans (hneg.trans (le_max_left _ _))
  rw [← Real.exp_log (covol_pos M)]
  exact Real.exp_le_exp.mpr hlog

/-- A discrete Euclidean lattice `L` is **semistable** if no nonzero sublattice has strictly
larger slope than `L`. -/
def IsSemistable (L : Submodule ℤ E) : Prop :=
  ∀ N : Submodule ℤ E, N ≤ L → N ≠ ⊥ → ArakelovCovolume.slope N ≤ ArakelovCovolume.slope L

theorem isSemistable_bot : IsSemistable (⊥ : Submodule ℤ E) := by
  intro N hN hN0
  exact absurd (le_bot_iff.mp hN) hN0

theorem isSemistable_iff_muMax_eq_slope (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    IsSemistable L ↔ muMax L = ArakelovCovolume.slope L := by
  constructor
  · intro hS
    apply le_antisymm
    · exact csSup_le ⟨ArakelovCovolume.slope L, L, le_rfl, hL0, rfl⟩
        (fun _ ⟨N, hNL, hN0, ht⟩ => ht ▸ hS N hNL hN0)
    · exact slope_le_muMax L L le_rfl hL0
  · intro heq N hNL hN0
    rw [← heq]
    exact slope_le_muMax L N hNL hN0

/-- **Existence & Uniqueness of the Maximal Destabilizing Sublattice (Stuhler–Grayson)**:
every nonzero discrete lattice `L ⊂ E` contains a unique nonzero saturated sublattice `M_max ≤ L`
such that `slope M_max = muMax L` and every nonzero sublattice `N ≤ L` with `slope N = muMax L`
satisfies `N ≤ M_max`! -/
theorem exists_maxDestab (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ M : Submodule ℤ E,
      IsSaturated L M ∧ M ≠ ⊥ ∧ ArakelovCovolume.slope M = muMax L ∧
      (∀ N : Submodule ℤ E, N ≤ L → N ≠ ⊥ → ArakelovCovolume.slope N = muMax L → N ≤ M) := by
  classical
  have hfin := finite_saturated_slope_ge L (ArakelovCovolume.slope L)
  let S : Finset (Submodule ℤ E) := hfin.toFinset
  have hLS : L ∈ S := hfin.mem_toFinset.mpr ⟨isSaturated_self L, hL0, le_rfl⟩
  obtain ⟨M₀, hM₀S, hM₀max⟩ := S.exists_max_image ArakelovCovolume.slope ⟨L, hLS⟩
  have hM₀_prop := hfin.mem_toFinset.mp hM₀S
  have hmuMax_eq : ArakelovCovolume.slope M₀ = muMax L := by
    apply le_antisymm
    · exact slope_le_muMax L M₀ hM₀_prop.1.1 hM₀_prop.2.1
    · refine csSup_le ⟨ArakelovCovolume.slope L, L, le_rfl, hL0, rfl⟩ ?_
      rintro _ ⟨N, hNL, hN0, rfl⟩
      by_cases hge : ArakelovCovolume.slope L ≤ ArakelovCovolume.slope N
      · have hsat_ne : saturation L N ≠ ⊥ := fun h0 =>
          hN0 (le_bot_iff.mp ((le_saturation hNL).trans (le_of_eq h0)))
        have hsat_S : saturation L N ∈ S := hfin.mem_toFinset.mpr
          ⟨isSaturated_saturation hNL, hsat_ne, hge.trans (slope_le_slope_saturation hNL)⟩
        exact (slope_le_slope_saturation hNL).trans (hM₀max _ hsat_S)
      · exact (le_of_not_ge hge).trans hM₀_prop.2.2
  let Smax : Finset (Submodule ℤ E) := S.filter fun M => ArakelovCovolume.slope M = muMax L
  have hM₀_Smax : M₀ ∈ Smax := Finset.mem_filter.mpr ⟨hM₀S, hmuMax_eq⟩
  obtain ⟨M, hM_Smax, hM_rkmax⟩ := Smax.exists_max_image rk ⟨M₀, hM₀_Smax⟩
  have hM_f := Finset.mem_filter.mp hM_Smax
  have hM_prop := hfin.mem_toFinset.mp hM_f.1
  refine ⟨M, hM_prop.1, hM_prop.2.1, hM_f.2, ?_⟩
  intro N hNL hN0 hNslope
  let N' := saturation L N
  have hN'_sat : IsSaturated L N' := isSaturated_saturation hNL
  have hN'_ne : N' ≠ ⊥ := fun h0 => hN0 (le_bot_iff.mp ((le_saturation hNL).trans (le_of_eq h0)))
  have hN'_slope : ArakelovCovolume.slope N' = muMax L := by
    apply le_antisymm (slope_le_muMax L N' hN'_sat.1 hN'_ne)
    rw [← hNslope]; exact slope_le_slope_saturation hNL
  let J := satJoin L M N'
  let I := M ⊓ N'
  have hJ_sat : IsSaturated L J := isSaturated_saturation (sup_le hM_prop.1.1 hN'_sat.1)
  have hJ_ne : J ≠ ⊥ := fun h0 =>
    hM_prop.2.1 (le_bot_iff.mp (((le_sup_left : M ≤ M ⊔ N').trans
      (le_saturation (sup_le hM_prop.1.1 hN'_sat.1))).trans (le_of_eq h0)))
  have hI_le : I ≤ L := inf_le_left.trans hM_prop.1.1
  have : DiscreteTopology M := discreteTopology_of_le hM_prop.1.1
  have : DiscreteTopology N' := discreteTopology_of_le hN'_sat.1
  have : DiscreteTopology J := discreteTopology_of_le hJ_sat.1
  have : DiscreteTopology I := discreteTopology_of_le hI_le
  have hGS := grayson_stuhler_supermodular hM_prop.1 hN'_sat
  have hrk_eq : (rk J : ℝ) + (rk I : ℝ) = (rk M : ℝ) + (rk N' : ℝ) := by
    exact_mod_cast hGS.2.2.2.1
  have hdeg_M : degAr M = (rk M : ℝ) * muMax L := by
    have hr : (0 : ℝ) < (rk M : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot M hM_prop.2.1)
    have hs := hM_f.2; unfold ArakelovCovolume.slope at hs
    rw [div_eq_iff hr.ne'] at hs; linarith
  have hdeg_N' : degAr N' = (rk N' : ℝ) * muMax L := by
    have hr : (0 : ℝ) < (rk N' : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot N' hN'_ne)
    have hs := hN'_slope; unfold ArakelovCovolume.slope at hs
    rw [div_eq_iff hr.ne'] at hs; linarith
  have hdeg_J : degAr J ≤ (rk J : ℝ) * muMax L := by
    have hr : (0 : ℝ) < (rk J : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot J hJ_ne)
    have hs := slope_le_muMax L J hJ_sat.1 hJ_ne
    unfold ArakelovCovolume.slope at hs
    rw [div_le_iff₀ hr] at hs; linarith
  have hdeg_I : degAr I ≤ (rk I : ℝ) * muMax L := by
    by_cases hI0 : I = ⊥
    · rw [hI0, degAr_bot, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]]; simp
    · have hr : (0 : ℝ) < (rk I : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot I hI0)
      have hs := slope_le_muMax L I hI_le hI0
      unfold ArakelovCovolume.slope at hs
      rw [div_le_iff₀ hr] at hs; linarith
  have hdeg_J_eq : degAr J = (rk J : ℝ) * muMax L := by
    have hsup : degAr M + degAr N' ≤ degAr J + degAr I := hGS.2.2.2.2.2
    have htot : (rk J : ℝ) * muMax L + (rk I : ℝ) * muMax L =
        (rk M : ℝ) * muMax L + (rk N' : ℝ) * muMax L := by
      rw [← add_mul, hrk_eq, add_mul]
    linarith
  have hJ_slope : ArakelovCovolume.slope J = muMax L := by
    have hr : (0 : ℝ) < (rk J : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot J hJ_ne)
    unfold ArakelovCovolume.slope
    rw [hdeg_J_eq, mul_div_cancel_left₀ _ hr.ne']
  have hJ_Smax : J ∈ Smax := Finset.mem_filter.mpr
    ⟨hfin.mem_toFinset.mpr ⟨hJ_sat, hJ_ne, hJ_slope ▸ slope_le_muMax L L le_rfl hL0⟩, hJ_slope⟩
  have hMJ_le : M ≤ J := le_sup_left.trans (le_saturation (sup_le hM_prop.1.1 hN'_sat.1))
  have hrk_MJ : rk M = rk J :=
    le_antisymm (RHDirect.Stage3ThetaSiegelBridge.rk_le_of_le hMJ_le) (hM_rkmax J hJ_Smax)
  have hMJ_eq : M = J := eq_of_isSaturated_of_rk_eq hM_prop.1 hJ_sat.1 hMJ_le hrk_MJ
  exact (le_saturation hNL).trans ((le_sup_right.trans (le_saturation (sup_le hM_prop.1.1 hN'_sat.1))).trans hMJ_eq.symm.le)

/-- The canonical **maximal destabilizing sublattice** `maxDestab L` of a discrete lattice `L`. -/
def maxDestab (L : Submodule ℤ E) [DiscreteTopology L] : Submodule ℤ E :=
  if hL0 : L = ⊥ then ⊥ else Classical.choose (exists_maxDestab L hL0)

lemma maxDestab_spec (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    IsSaturated L (maxDestab L) ∧ maxDestab L ≠ ⊥ ∧
    ArakelovCovolume.slope (maxDestab L) = muMax L ∧
    ∀ N : Submodule ℤ E, N ≤ L → N ≠ ⊥ → ArakelovCovolume.slope N = muMax L → N ≤ maxDestab L := by
  unfold maxDestab
  rw [dif_neg hL0]
  exact Classical.choose_spec (exists_maxDestab L hL0)

lemma maxDestab_isSaturated (L : Submodule ℤ E) [DiscreteTopology L] :
    IsSaturated L (maxDestab L) := by
  by_cases hL0 : L = ⊥
  · unfold maxDestab; rw [dif_pos hL0]; exact isSaturated_bot L
  · exact (maxDestab_spec L hL0).1

lemma maxDestab_ne_bot (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    maxDestab L ≠ ⊥ := (maxDestab_spec L hL0).2.1

lemma slope_maxDestab (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ArakelovCovolume.slope (maxDestab L) = muMax L := (maxDestab_spec L hL0).2.2.1

lemma le_maxDestab_of_slope_eq (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {N : Submodule ℤ E} (hNL : N ≤ L) (hN0 : N ≠ ⊥) (hslope : ArakelovCovolume.slope N = muMax L) :
    N ≤ maxDestab L :=
  (maxDestab_spec L hL0).2.2.2 N hNL hN0 hslope

theorem isSemistable_maxDestab (L : Submodule ℤ E) [DiscreteTopology L] :
    IsSemistable (maxDestab L) := by
  by_cases hL0 : L = ⊥
  · unfold maxDestab; rw [dif_pos hL0]; exact isSemistable_bot
  · intro N hNM hN0
    rw [slope_maxDestab L hL0]
    exact slope_le_muMax L N (hNM.trans (maxDestab_isSaturated L).1) hN0

/-- **Uniqueness of the Maximal Destabilizing Sublattice**:
any saturated nonzero sublattice maximizing `(slope M, rk M)` lexicographically equals `maxDestab L`. -/
theorem maxDestab_unique (L M : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (hMsat : IsSaturated L M) (hM0 : M ≠ ⊥) (hMslope : ArakelovCovolume.slope M = muMax L)
    (hMrk : ∀ N : Submodule ℤ E, IsSaturated L N → N ≠ ⊥ → ArakelovCovolume.slope N = muMax L →
      rk N ≤ rk M) :
    M = maxDestab L := by
  have hle : M ≤ maxDestab L := le_maxDestab_of_slope_eq L hL0 hMsat.1 hM0 hMslope
  have : DiscreteTopology ↥(maxDestab L) := discreteTopology_of_le (maxDestab_isSaturated L).1
  have hrk_eq : rk M = rk (maxDestab L) :=
    le_antisymm (RHDirect.Stage3ThetaSiegelBridge.rk_le_of_le hle)
      (hMrk (maxDestab L) (maxDestab_isSaturated L) (maxDestab_ne_bot L hL0) (slope_maxDestab L hL0))
  exact eq_of_isSaturated_of_rk_eq hMsat (maxDestab_isSaturated L).1 hle hrk_eq

/-- Strict slope drop on the quotient `L / maxDestab L`:
whenever `maxDestab L ≠ L`, `muMax (quotLat L (maxDestab L)) < muMax L`. -/
theorem muMax_quotLat_maxDestab_lt (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (hne : maxDestab L ≠ L) :
    muMax (quotLat L (maxDestab L)) < muMax L := by
  let M₁ := maxDestab L
  have hM₁_sat : IsSaturated L M₁ := maxDestab_isSaturated L
  have hM₁_ne : M₁ ≠ ⊥ := maxDestab_ne_bot L hL0
  have hM₁_slope : ArakelovCovolume.slope M₁ = muMax L := slope_maxDestab L hL0
  let Q := quotLat L M₁
  have : DiscreteTopology M₁ := discreteTopology_of_le hM₁_sat.1
  have : DiscreteTopology Q := discreteTopology_quotLat hM₁_sat
  have hQ0 : Q ≠ ⊥ := quotLat_ne_bot_of_lt hM₁_sat hne
  let K := maxDestab Q
  have hK_sat : IsSaturated Q K := maxDestab_isSaturated Q
  have hK_ne : K ≠ ⊥ := maxDestab_ne_bot Q hQ0
  have hK_slope : ArakelovCovolume.slope K = muMax Q := slope_maxDestab Q hQ0
  let N := liftSub L M₁ K
  have hN_sat : IsSaturated L N := isSaturated_liftSub hK_sat
  have hM₁_le_N : M₁ ≤ N := le_liftSub hM₁_sat.1
  have hN_ne : N ≠ ⊥ := fun h0 => hM₁_ne (le_bot_iff.mp (hM₁_le_N.trans (le_of_eq h0)))
  have hM₁_lt_N : M₁ ≠ N := by
    intro heq
    have hqK : quotLat N M₁ = K := quotLat_liftSub hK_sat.1
    rw [← heq, quotLat_self] at hqK
    exact hK_ne hqK.symm
  have hN_slope_lt : ArakelovCovolume.slope N < muMax L := by
    have hle := slope_le_muMax L N hN_sat.1 hN_ne
    refine lt_of_le_of_ne hle fun heq => hM₁_lt_N ?_
    exact le_antisymm hM₁_le_N (le_maxDestab_of_slope_eq L hL0 hN_sat.1 hN_ne heq)
  have : DiscreteTopology N := discreteTopology_of_le hN_sat.1
  have : DiscreteTopology K := discreteTopology_of_le hK_sat.1
  have hM₁_sat_N : IsSaturated N M₁ := isSaturated_of_le_of_isSaturated hM₁_sat hM₁_le_N hN_sat.1
  have hqN : quotLat N M₁ = K := quotLat_liftSub hK_sat.1
  have hrkN : rk N = rk M₁ + rk K := by rw [← hqN]; exact rk_add_quotLat hM₁_sat_N
  have hdegN : degAr N = degAr M₁ + degAr K := by rw [← hqN]; exact degAr_eq_add_quotLat hM₁_sat_N
  have hrN : (0 : ℝ) < (rk N : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot N hN_ne)
  have hrM₁ : (0 : ℝ) < (rk M₁ : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot M₁ hM₁_ne)
  have hrK : (0 : ℝ) < (rk K : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot K hK_ne)
  have hdegN_lt : degAr N < (rk N : ℝ) * muMax L := by
    unfold ArakelovCovolume.slope at hN_slope_lt
    rw [div_lt_iff₀ hrN] at hN_slope_lt
    linarith
  have hdegM₁_eq : degAr M₁ = (rk M₁ : ℝ) * muMax L := by
    unfold ArakelovCovolume.slope at hM₁_slope
    rw [div_eq_iff hrM₁.ne'] at hM₁_slope
    linarith
  have hrN_cast : (rk N : ℝ) = (rk M₁ : ℝ) + (rk K : ℝ) := by exact_mod_cast hrkN
  have hdegK_lt : degAr K < (rk K : ℝ) * muMax L := by
    rw [hrN_cast, add_mul] at hdegN_lt
    linarith
  rw [← hK_slope]
  unfold ArakelovCovolume.slope
  rw [div_lt_iff₀ hrK]
  linarith

/-- **Canonical Harder–Narasimhan Filtration** of a discrete Euclidean lattice `L ⊂ E`:
a strictly increasing chain `0 = L_0 ⊂ L_1 ⊂ ... ⊂ L_k = L` of saturated sublattices whose
consecutive orthogonal quotients `L_{i+1} / L_i` are semistable with strictly decreasing slopes. -/
structure HNFiltration (L : Submodule ℤ E) [DiscreteTopology L] where
  len : ℕ
  step : Fin (len + 1) → Submodule ℤ E
  step_zero : step 0 = ⊥
  step_last : step (Fin.last len) = L
  step_saturated : ∀ i, IsSaturated L (step i)
  step_strictMono : StrictMono step
  quot_semistable : ∀ i : Fin len,
    IsSemistable (quotLat (step i.succ) (step i.castSucc))
  slope_strictAnti : ∀ i j : Fin len, i < j →
    ArakelovCovolume.slope (quotLat (step j.succ) (step j.castSucc)) <
      ArakelovCovolume.slope (quotLat (step i.succ) (step i.castSucc))

/-- The `i`-th Harder–Narasimhan quotient `L_{i+1} / L_i`. -/
def HNFiltration.quot {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (i : Fin F.len) : Submodule ℤ E :=
  quotLat (F.step i.succ) (F.step i.castSucc)

/-- The `i`-th Harder–Narasimhan slope `μ_i = slope (L_{i+1} / L_i)`. -/
def HNFiltration.hnSlope {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (i : Fin F.len) : ℝ :=
  ArakelovCovolume.slope (F.quot i)

lemma HNFiltration.quot_discrete {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (i : Fin F.len) :
    DiscreteTopology (F.quot i) := by
  have : DiscreteTopology (F.step i.succ) := discreteTopology_of_le (F.step_saturated i.succ).1
  have hsat : IsSaturated (F.step i.succ) (F.step i.castSucc) :=
    isSaturated_of_le_of_isSaturated (F.step_saturated i.castSucc)
      (F.step_strictMono (Fin.castSucc_lt_succ (i := i))).le (F.step_saturated i.succ).1
  exact discreteTopology_quotLat hsat

lemma HNFiltration.quot_ne_bot {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (i : Fin F.len) :
    F.quot i ≠ ⊥ := by
  have hsat : IsSaturated (F.step i.succ) (F.step i.castSucc) :=
    isSaturated_of_le_of_isSaturated (F.step_saturated i.castSucc)
      (F.step_strictMono (Fin.castSucc_lt_succ (i := i))).le (F.step_saturated i.succ).1
  exact quotLat_ne_bot_of_lt hsat (ne_of_lt (F.step_strictMono (Fin.castSucc_lt_succ (i := i))))

lemma HNFiltration.len_pos_of_ne_bot {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (hL0 : L ≠ ⊥) : 0 < F.len := by
  by_contra h0
  have hlen0 : F.len = 0 := by omega
  apply hL0
  have h1 : (0 : Fin (F.len + 1)) = Fin.last F.len := Fin.ext (by simp [hlen0])
  rw [← F.step_last, ← h1, F.step_zero]

/-- **Existence of the Canonical Harder–Narasimhan Filtration** (proved by strong induction on `rk L`). -/
theorem exists_hnFiltration (L : Submodule ℤ E) [DiscreteTopology L] :
    Nonempty (HNFiltration L) := by
  have hrec : ∀ n : ℕ, ∀ (L : Submodule ℤ E) [DiscreteTopology L],
      rk L ≤ n → Nonempty (HNFiltration L) := by
    intro n
    induction n with
    | zero =>
      intro L hDisc hrk
      have hL0 : L = ⊥ := by
        by_contra hne
        have hpos := rk_pos_of_ne_bot L hne
        omega
      refine ⟨{
        len := 0
        step := fun _ => ⊥
        step_zero := rfl
        step_last := hL0.symm
        step_saturated := fun _ => isSaturated_bot L
        step_strictMono := fun a b hab => by exfalso; omega
        quot_semistable := fun i => Fin.elim0 i
        slope_strictAnti := fun i => Fin.elim0 i
      }⟩
    | succ n ih =>
      intro L hDisc hrk
      by_cases hL0 : L = ⊥
      · exact ih L (by subst hL0; simp [rk])
      · let M₁ := maxDestab L
        have hM₁_sat : IsSaturated L M₁ := maxDestab_isSaturated L
        have hM₁_ne : M₁ ≠ ⊥ := maxDestab_ne_bot L hL0
        have : DiscreteTopology M₁ := discreteTopology_of_le hM₁_sat.1
        by_cases hM₁_eq : M₁ = L
        · refine ⟨{
            len := 1
            step := fun i => if i = 0 then ⊥ else L
            step_zero := by simp
            step_last := by simp
            step_saturated := fun i => by by_cases hi : i = 0 <;> simp [hi, isSaturated_bot, isSaturated_self]
            step_strictMono := fun a b hab => by
              fin_cases a <;> fin_cases b
              · exact absurd hab (lt_irrefl _)
              · simp [bot_lt_iff_ne_bot.mpr hL0]
              · exact absurd hab (by decide)
              · exact absurd hab (lt_irrefl _)
            quot_semistable := fun i => by
              fin_cases i
              change IsSemistable (quotLat L ⊥)
              rw [quotLat_bot, ← hM₁_eq]
              exact isSemistable_maxDestab L
            slope_strictAnti := fun i j hij => by fin_cases i; fin_cases j; exact absurd hij (lt_irrefl _)
          }⟩
        · let Q := quotLat L M₁
          have hDiscQ : DiscreteTopology Q := discreteTopology_quotLat hM₁_sat
          have hrkQ : rk Q ≤ n := by
            have hadd : rk L = rk M₁ + rk Q := rk_add_quotLat hM₁_sat
            have hpos := rk_pos_of_ne_bot M₁ hM₁_ne
            omega
          obtain ⟨FQ⟩ := ih Q hrkQ
          have hQ0 : Q ≠ ⊥ := quotLat_ne_bot_of_lt hM₁_sat hM₁_eq
          have hFQ_pos : 0 < FQ.len := FQ.len_pos_of_ne_bot hQ0
          let stepL : Fin (FQ.len + 1 + 1) → Submodule ℤ E :=
            Fin.cons ⊥ (fun j => liftSub L M₁ (FQ.step j))
          have hstepL_zero : stepL 0 = ⊥ := rfl
          have hstepL_one : stepL 1 = M₁ := by
            change liftSub L M₁ (FQ.step 0) = M₁
            rw [FQ.step_zero]
            have h1 := liftSub_quotLat hM₁_sat hM₁_sat le_rfl
            rwa [quotLat_self] at h1
          have hstepL_last : stepL (Fin.last (FQ.len + 1)) = L := by
            change liftSub L M₁ (FQ.step (Fin.last FQ.len)) = L
            rw [FQ.step_last]
            apply le_antisymm (liftSub_le L M₁ Q)
            intro x hxL
            exact ⟨hxL, ⟨x, hxL, rfl⟩⟩
          have hstepL_sat : ∀ i, IsSaturated L (stepL i) := by
            intro i
            refine Fin.cases (isSaturated_bot L) (fun j => isSaturated_liftSub (FQ.step_saturated j)) i
          have hstepL_mono : StrictMono stepL := by
            intro a b
            refine Fin.cases ?_ (fun a' => ?_) a
            · refine Fin.cases (fun hab => absurd hab (lt_irrefl _)) (fun b' _ => ?_) b
              change ⊥ < liftSub L M₁ (FQ.step b')
              exact bot_lt_iff_ne_bot.mpr (fun h0 =>
                hM₁_ne (le_bot_iff.mp ((le_liftSub hM₁_sat.1).trans (le_of_eq h0))))
            · refine Fin.cases (fun hab => absurd hab (not_lt.mpr (Fin.zero_le _))) (fun b' hab => ?_) b
              have hab' : a' < b' := Fin.succ_lt_succ_iff.mp hab
              have hltQ : FQ.step a' < FQ.step b' := FQ.step_strictMono hab'
              change liftSub L M₁ (FQ.step a') < liftSub L M₁ (FQ.step b')
              refine lt_of_le_of_ne ?_ fun heq => hltQ.ne ?_
              · exact inf_le_inf_left L (Submodule.comap_mono hltQ.le)
              · rw [← quotLat_liftSub (FQ.step_saturated a').1,
                  ← quotLat_liftSub (FQ.step_saturated b').1, heq]
          have hquot_succ : ∀ j : Fin FQ.len,
              quotLat (stepL j.succ.succ) (stepL j.succ.castSucc) = FQ.quot j := by
            intro j
            change quotLat (liftSub L M₁ (FQ.step j.succ)) (liftSub L M₁ (FQ.step j.castSucc)) =
              quotLat (FQ.step j.succ) (FQ.step j.castSucc)
            have h1 := quotLat_quotLat (L := liftSub L M₁ (FQ.step j.succ))
              (M := M₁) (N := liftSub L M₁ (FQ.step j.castSucc)) (le_liftSub hM₁_sat.1)
            rw [quotLat_liftSub (FQ.step_saturated j.succ).1,
              quotLat_liftSub (FQ.step_saturated j.castSucc).1] at h1
            exact h1.symm
          have hquot_zero : quotLat (stepL (0 : Fin (FQ.len + 1)).succ)
              (stepL (0 : Fin (FQ.len + 1)).castSucc) = M₁ := by
            change quotLat (stepL 1) (stepL 0) = M₁
            rw [hstepL_one, hstepL_zero, quotLat_bot]
          have hmuQ_lt : muMax Q < ArakelovCovolume.slope M₁ := by
            rw [slope_maxDestab L hL0]
            exact muMax_quotLat_maxDestab_lt L hL0 hM₁_eq
          refine ⟨{
            len := FQ.len + 1
            step := stepL
            step_zero := hstepL_zero
            step_last := hstepL_last
            step_saturated := hstepL_sat
            step_strictMono := hstepL_mono
            quot_semistable := fun i => by
              refine Fin.cases ?_ (fun j => ?_) i
              · rw [hquot_zero]; exact isSemistable_maxDestab L
              · rw [hquot_succ j]; exact FQ.quot_semistable j
            slope_strictAnti := fun i j => by
              refine Fin.cases ?_ (fun i' => ?_) i
              · refine Fin.cases (fun hij => absurd hij (lt_irrefl _)) (fun j' _ => ?_) j
                rw [hquot_zero, hquot_succ j']
                let j₀ : Fin FQ.len := ⟨0, hFQ_pos⟩
                have hj'_le_j0 : ArakelovCovolume.slope (FQ.quot j') ≤ ArakelovCovolume.slope (FQ.quot j₀) := by
                  rcases eq_or_lt_of_le (show j₀ ≤ j' from Nat.zero_le j'.1) with heq | hlt
                  · rw [heq]
                  · exact (FQ.slope_strictAnti j₀ j' hlt).le
                have hj0_eq : FQ.quot j₀ = FQ.step j₀.succ := by
                  change quotLat (FQ.step j₀.succ) (FQ.step j₀.castSucc) = FQ.step j₀.succ
                  have h0 : j₀.castSucc = (0 : Fin (FQ.len + 1)) := Fin.ext rfl
                  rw [h0, FQ.step_zero, quotLat_bot]
                have hj0_le_muQ : ArakelovCovolume.slope (FQ.quot j₀) ≤ muMax Q := by
                  rw [hj0_eq]
                  exact slope_le_muMax Q (FQ.step j₀.succ) (FQ.step_saturated _).1 (hj0_eq ▸ FQ.quot_ne_bot j₀)
                exact lt_of_le_of_lt (hj'_le_j0.trans hj0_le_muQ) hmuQ_lt
              · refine Fin.cases (fun hij => absurd hij (not_lt.mpr (Fin.zero_le _))) (fun j' hij => ?_) j
                rw [hquot_succ i', hquot_succ j']
                exact FQ.slope_strictAnti i' j' (Fin.succ_lt_succ_iff.mp hij)
          }⟩
  exact hrec (rk L) L le_rfl

/-- **Key Uniqueness Lemma**: for ANY Harder–Narasimhan filtration `F` of `L ≠ ⊥`,
every nonzero sublattice `N ≤ L` has `slope N ≤ slope (F.step 1)`, with strict inequality
whenever `N ≰ F.step 1`! Consequently `F.step 1 = maxDestab L`! -/
theorem hnFiltration_first_eq_maxDestab (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (F : HNFiltration L) :
    let hpos := F.len_pos_of_ne_bot hL0
    F.step ⟨1, Nat.succ_lt_succ hpos⟩ = maxDestab L := by
  intro hpos
  let i₀ : Fin F.len := ⟨0, hpos⟩
  let M₁ := F.step ⟨1, Nat.succ_lt_succ hpos⟩
  have hq0 : F.quot i₀ = M₁ := by
    change quotLat (F.step i₀.succ) (F.step i₀.castSucc) = M₁
    have h0 : i₀.castSucc = (0 : Fin (F.len + 1)) := Fin.ext rfl
    have h1 : i₀.succ = ⟨1, Nat.succ_lt_succ hpos⟩ := Fin.ext rfl
    rw [h0, h1, F.step_zero, quotLat_bot]
  have hM₁_ss : IsSemistable M₁ := hq0 ▸ F.quot_semistable i₀
  have hM₁_sat : IsSaturated L M₁ := F.step_saturated _
  have hM₁_ne : M₁ ≠ ⊥ := hq0 ▸ F.quot_ne_bot i₀
  -- Prove by induction on `k ≤ F.len` that any nonzero saturated `N ≤ F.step k` has
  -- `slope N ≤ slope M₁`, and strictly `< slope M₁` if `N ≰ M₁`!
  have hstep_bound : ∀ k : ℕ, (hk : k ≤ F.len) → ∀ N : Submodule ℤ E,
      IsSaturated L N → N ≤ F.step ⟨k, Nat.lt_succ_of_le hk⟩ → N ≠ ⊥ →
      ArakelovCovolume.slope N ≤ ArakelovCovolume.slope M₁ ∧
        (¬ N ≤ M₁ → ArakelovCovolume.slope N < ArakelovCovolume.slope M₁) := by
    intro k
    induction k with
    | zero =>
      intro _ N _ hN0 hNne
      rw [show (⟨0, _⟩ : Fin (F.len + 1)) = 0 from Fin.ext rfl, F.step_zero] at hN0
      exact absurd (le_bot_iff.mp hN0) hNne
    | succ k ih =>
      intro hk N hNsat hNle hNne
      by_cases hk0 : k = 0
      · subst hk0
        have hNM₁ : N ≤ M₁ := hNle
        exact ⟨hM₁_ss N hNM₁ hNne, fun h => absurd hNM₁ h⟩
      · let j : Fin F.len := ⟨k, hk⟩
        have hj_gt : i₀ < j := by show (0 : ℕ) < k; omega
        have hslope_lt : ArakelovCovolume.slope (F.quot j) < ArakelovCovolume.slope M₁ := by
          rw [← hq0]; exact F.slope_strictAnti i₀ j hj_gt
        let prev := F.step j.castSucc
        have hprev_eq : prev = F.step ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩ := rfl
        by_cases hNprev : N ≤ prev
        · exact ih (Nat.le_of_succ_le hk) N hNsat hNprev hNne
        · let N₀ := N ⊓ prev
          have hN₀_sat_L : IsSaturated L N₀ := isSaturated_inf hNsat (F.step_saturated j.castSucc)
          have hN₀_sat_N : IsSaturated N N₀ :=
            isSaturated_of_le_of_isSaturated hN₀_sat_L inf_le_left hNsat.1
          have hN₀_lt_N : N₀ ≠ N := fun heq => hNprev (heq ▸ inf_le_right)
          let K := quotLat N N₀
          have : DiscreteTopology N := discreteTopology_of_le hNsat.1
          have : DiscreteTopology N₀ := discreteTopology_of_le hN₀_sat_L.1
          have : DiscreteTopology K := discreteTopology_quotLat hN₀_sat_N
          have : DiscreteTopology (F.quot j) := F.quot_discrete j
          have hK_ne : K ≠ ⊥ := quotLat_ne_bot_of_lt hN₀_sat_N hN₀_lt_N
          -- `projOrth prev` injects `K` into `F.quot j` with norm `≤ 1`!
          have himg : ∀ y ∈ K, projOrth prev y ∈ F.quot j := by
            rintro _ ⟨x, hxN, rfl⟩
            change projOrth prev (projOrth N₀ x) ∈ quotLat (F.step j.succ) prev
            rw [projOrth_comp_of_le inf_le_right x]
            exact ⟨x, hNle hxN, rfl⟩
          let φ : K →ₗ[ℤ] F.quot j :=
            { toFun := fun y => ⟨projOrth prev y.1, himg y.1 y.2⟩
              map_add' := fun a b => Subtype.ext (map_add (projOrth prev) a.1 b.1)
              map_smul' := fun c a => Subtype.ext (map_zsmul (projOrth prev) c a.1) }
          have hφ_inj : Function.Injective φ := by
            intro a b hab
            apply Subtype.ext
            have h0 : projOrth prev (a.1 - b.1) = 0 := by
              rw [map_sub]
              have hv : projOrth prev a.1 = projOrth prev b.1 :=
                congrArg (fun z : F.quot j => (z : E)) hab
              exact sub_eq_zero.mpr hv
            obtain ⟨x, hxN, hxeq⟩ := K.sub_mem a.2 b.2
            have hxeq' : projOrth N₀ x = a.1 - b.1 := hxeq
            have hx_prev : projOrth prev x = 0 := by
              rw [← projOrth_comp_of_le inf_le_right x, hxeq', h0]
            have hx_mem_prev : x ∈ prev :=
              (F.step_saturated j.castSucc).2 x (hNsat.1 hxN) ((projOrth_eq_zero_iff prev x).mp hx_prev)
            have hx_N₀ : x ∈ N₀ := ⟨hxN, hx_mem_prev⟩
            have hsub0 : a.1 - b.1 = 0 := by
              rw [← hxeq']
              exact (projOrth_eq_zero_iff N₀ x).mpr (Submodule.subset_span hx_N₀)
            exact sub_eq_zero.mp hsub0
          have hφ_lip : ∀ y : K, ‖((φ y : F.quot j) : E)‖ ≤ 1 * ‖(y : E)‖ := by
            intro y; rw [one_mul]; exact norm_projOrth_le prev y.1
          have hBost := bost_slope_inequality K (F.quot j) hK_ne φ 1 hφ_inj hφ_lip
          rw [Real.log_one, add_zero,
            (isSemistable_iff_muMax_eq_slope (F.quot j) (F.quot_ne_bot j)).mp (F.quot_semistable j)] at hBost
          have hK_lt : ArakelovCovolume.slope K < ArakelovCovolume.slope M₁ :=
            lt_of_le_of_lt hBost hslope_lt
          have hrK : (0 : ℝ) < (rk K : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot K hK_ne)
          have hrN : (0 : ℝ) < (rk N : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot N hNne)
          have hdegK_lt : degAr K < (rk K : ℝ) * ArakelovCovolume.slope M₁ := by
            have h1 : degAr K / (rk K : ℝ) < ArakelovCovolume.slope M₁ := hK_lt
            rw [div_lt_iff₀ hrK] at h1
            linarith
          have hdegN₀_le : degAr N₀ ≤ (rk N₀ : ℝ) * ArakelovCovolume.slope M₁ := by
            by_cases hN₀0 : N₀ = ⊥
            · rw [hN₀0, degAr_bot, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]]; simp
            · have hIH := (ih (Nat.le_of_succ_le hk) N₀ hN₀_sat_L inf_le_right hN₀0).1
              have hrN₀ : (0 : ℝ) < (rk N₀ : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot N₀ hN₀0)
              have h1 : degAr N₀ / (rk N₀ : ℝ) ≤ ArakelovCovolume.slope M₁ := hIH
              rw [div_le_iff₀ hrN₀] at h1
              linarith
          have hrk_add : (rk N : ℝ) = (rk N₀ : ℝ) + (rk K : ℝ) := by
            exact_mod_cast rk_add_quotLat hN₀_sat_N
          have hdeg_add : degAr N = degAr N₀ + degAr K := degAr_eq_add_quotLat hN₀_sat_N
          have hN_lt : ArakelovCovolume.slope N < ArakelovCovolume.slope M₁ := by
            show degAr N / (rk N : ℝ) < ArakelovCovolume.slope M₁
            rw [div_lt_iff₀ hrN]
            have hmul : (rk N : ℝ) * ArakelovCovolume.slope M₁ =
                (rk N₀ : ℝ) * ArakelovCovolume.slope M₁ + (rk K : ℝ) * ArakelovCovolume.slope M₁ := by
              rw [hrk_add, add_mul]
            linarith
          exact ⟨hN_lt.le, fun _ => hN_lt⟩
  have hlast : F.step ⟨F.len, Nat.lt_succ_self _⟩ = L := F.step_last
  have hmu_eq : ArakelovCovolume.slope M₁ = muMax L := by
    apply le_antisymm (slope_le_muMax L M₁ hM₁_sat.1 hM₁_ne)
    refine csSup_le ⟨ArakelovCovolume.slope L, L, le_rfl, hL0, rfl⟩ ?_
    rintro _ ⟨N, hNL, hN0, rfl⟩
    have hsat_ne : saturation L N ≠ ⊥ :=
      fun h0 => hN0 (le_bot_iff.mp ((le_saturation hNL).trans (le_of_eq h0)))
    have hsat_le_step : saturation L N ≤ F.step ⟨F.len, Nat.lt_succ_self _⟩ := by
      rw [hlast]; exact saturation_le L N
    exact (slope_le_slope_saturation hNL).trans
      (hstep_bound F.len le_rfl (saturation L N) (isSaturated_saturation hNL) hsat_le_step hsat_ne).1
  apply maxDestab_unique L M₁ hL0 hM₁_sat hM₁_ne hmu_eq
  intro N hNsat hN0 hNslope
  have hNM₁ : N ≤ M₁ := by
    by_contra hnot
    have hN_le_step : N ≤ F.step ⟨F.len, Nat.lt_succ_self _⟩ := by rw [hlast]; exact hNsat.1
    have hlt := (hstep_bound F.len le_rfl N hNsat hN_le_step hN0).2 hnot
    linarith
  have : DiscreteTopology M₁ := discreteTopology_of_le hM₁_sat.1
  exact RHDirect.Stage3ThetaSiegelBridge.rk_le_of_le hNM₁

/-- Quotienting an `HNFiltration L` by `M₁ = F.step 1` yields an
`HNFiltration (quotLat L M₁)` of length `F.len - 1`. -/
private def HNFiltration.tailAt {L M₁ : Submodule ℤ E} [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (F : HNFiltration L) (hM₁ : F.step ⟨1, Nat.succ_lt_succ (F.len_pos_of_ne_bot hL0)⟩ = M₁)
    [DiscreteTopology (quotLat L M₁)] :
    HNFiltration (quotLat L M₁) := by
  have hpos := F.len_pos_of_ne_bot hL0
  have hM₁_sat : IsSaturated L M₁ := hM₁ ▸ F.step_saturated _
  have hstep_ge : ∀ j : Fin (F.len - 1 + 1), M₁ ≤ F.step ⟨j.1 + 1, by omega⟩ := by
    intro j
    rw [← hM₁]
    have hle : (⟨1, Nat.succ_lt_succ hpos⟩ : Fin (F.len + 1)) ≤ ⟨j.1 + 1, by omega⟩ := by
      show 1 ≤ j.1 + 1; omega
    exact F.step_strictMono.monotone hle
  refine {
    len := F.len - 1
    step := fun j => quotLat (F.step ⟨j.1 + 1, by omega⟩) M₁
    step_zero := by
      change quotLat (F.step ⟨1, Nat.succ_lt_succ hpos⟩) M₁ = ⊥
      rw [hM₁, quotLat_self]
    step_last := by
      have heq : (⟨(Fin.last (F.len - 1)).1 + 1, by omega⟩ : Fin (F.len + 1)) = Fin.last F.len := by
        ext; simp; omega
      rw [heq, F.step_last]
    step_saturated := fun j => isSaturated_quotLat hM₁_sat (F.step_saturated _) (hstep_ge j)
    step_strictMono := fun a b hab => by
      have hlt : F.step ⟨a.1 + 1, by omega⟩ < F.step ⟨b.1 + 1, by omega⟩ :=
        F.step_strictMono (show (⟨a.1 + 1, by omega⟩ : Fin (F.len + 1)) < ⟨b.1 + 1, by omega⟩ from
          Nat.succ_lt_succ hab)
      refine lt_of_le_of_ne (Submodule.map_mono hlt.le) fun heq => hlt.ne ?_
      have heq' : quotLat (F.step ⟨a.1 + 1, by omega⟩) M₁ = quotLat (F.step ⟨b.1 + 1, by omega⟩) M₁ := heq
      rw [← liftSub_quotLat hM₁_sat (F.step_saturated ⟨a.1 + 1, by omega⟩) (hstep_ge a),
        ← liftSub_quotLat hM₁_sat (F.step_saturated ⟨b.1 + 1, by omega⟩) (hstep_ge b), heq']
    quot_semistable := fun i => by
      have hqq := quotLat_quotLat (L := F.step ⟨i.1 + 2, by omega⟩)
        (M := M₁) (N := F.step ⟨i.1 + 1, by omega⟩) (hstep_ge i.castSucc)
      change IsSemistable (quotLat (quotLat (F.step ⟨i.1 + 2, by omega⟩) M₁)
        (quotLat (F.step ⟨i.1 + 1, by omega⟩) M₁))
      rw [hqq]
      exact F.quot_semistable ⟨i.1 + 1, by omega⟩
    slope_strictAnti := fun i j hij => by
      have hqi := quotLat_quotLat (L := F.step ⟨i.1 + 2, by omega⟩)
        (M := M₁) (N := F.step ⟨i.1 + 1, by omega⟩) (hstep_ge i.castSucc)
      have hqj := quotLat_quotLat (L := F.step ⟨j.1 + 2, by omega⟩)
        (M := M₁) (N := F.step ⟨j.1 + 1, by omega⟩) (hstep_ge j.castSucc)
      change ArakelovCovolume.slope (quotLat (quotLat (F.step ⟨j.1 + 2, by omega⟩) M₁)
          (quotLat (F.step ⟨j.1 + 1, by omega⟩) M₁)) <
        ArakelovCovolume.slope (quotLat (quotLat (F.step ⟨i.1 + 2, by omega⟩) M₁)
          (quotLat (F.step ⟨i.1 + 1, by omega⟩) M₁))
      rw [hqi, hqj]
      exact F.slope_strictAnti ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩ (Nat.succ_lt_succ hij)
  }

/-- **Uniqueness of the Canonical Harder–Narasimhan Filtration (Stuhler–Grayson Theorem)**:
any two Harder–Narasimhan filtrations `F₁, F₂` of a discrete Euclidean lattice `L ⊂ E` have the
same length and identical filtration steps! -/
theorem hnFiltration_unique (L : Submodule ℤ E) [DiscreteTopology L]
    (F₁ F₂ : HNFiltration L) :
    F₁.len = F₂.len ∧ ∀ (i : ℕ) (h₁ : i ≤ F₁.len) (h₂ : i ≤ F₂.len),
      F₁.step ⟨i, Nat.lt_succ_of_le h₁⟩ = F₂.step ⟨i, Nat.lt_succ_of_le h₂⟩ := by
  have hrec : ∀ n : ℕ, ∀ (L : Submodule ℤ E) [DiscreteTopology L],
      rk L ≤ n → ∀ (F₁ F₂ : HNFiltration L),
        F₁.len = F₂.len ∧ ∀ (i : ℕ) (h₁ : i ≤ F₁.len) (h₂ : i ≤ F₂.len),
          F₁.step ⟨i, Nat.lt_succ_of_le h₁⟩ = F₂.step ⟨i, Nat.lt_succ_of_le h₂⟩ := by
    intro n
    induction n with
    | zero =>
      intro L hDisc hrk F₁ F₂
      have hL0 : L = ⊥ := by
        by_contra hne; have := rk_pos_of_ne_bot L hne; omega
      have hlen1 : F₁.len = 0 := by
        by_contra hne
        have hlt := F₁.step_strictMono (show (0 : Fin (F₁.len + 1)) < Fin.last F₁.len by
          exact Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hne))
        rw [F₁.step_zero, F₁.step_last, hL0] at hlt
        exact lt_irrefl ⊥ hlt
      have hlen2 : F₂.len = 0 := by
        by_contra hne
        have hlt := F₂.step_strictMono (show (0 : Fin (F₂.len + 1)) < Fin.last F₂.len by
          exact Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hne))
        rw [F₂.step_zero, F₂.step_last, hL0] at hlt
        exact lt_irrefl ⊥ hlt
      refine ⟨hlen1.trans hlen2.symm, fun i h₁ h₂ => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      exact F₁.step_zero.trans F₂.step_zero.symm
    | succ n ih =>
      intro L hDisc hrk F₁ F₂
      by_cases hL0 : L = ⊥
      · exact ih L (by subst hL0; simp [rk]) F₁ F₂
      · have hpos₁ := F₁.len_pos_of_ne_bot hL0
        have hpos₂ := F₂.len_pos_of_ne_bot hL0
        let M₁ := maxDestab L
        have h1eq : F₁.step ⟨1, Nat.succ_lt_succ hpos₁⟩ = M₁ :=
          hnFiltration_first_eq_maxDestab L hL0 F₁
        have h2eq : F₂.step ⟨1, Nat.succ_lt_succ hpos₂⟩ = M₁ :=
          hnFiltration_first_eq_maxDestab L hL0 F₂
        have hM₁_sat : IsSaturated L M₁ := maxDestab_isSaturated L
        have hM₁_ne : M₁ ≠ ⊥ := maxDestab_ne_bot L hL0
        have : DiscreteTopology M₁ := discreteTopology_of_le hM₁_sat.1
        let Q := quotLat L M₁
        have hDiscQ : DiscreteTopology Q := discreteTopology_quotLat hM₁_sat
        have hrkQ : rk Q ≤ n := by
          have hadd : rk L = rk M₁ + rk Q := rk_add_quotLat hM₁_sat
          have hpos := rk_pos_of_ne_bot M₁ hM₁_ne
          omega
        let T₁ : HNFiltration Q := F₁.tailAt hL0 h1eq
        let T₂ : HNFiltration Q := F₂.tailAt hL0 h2eq
        have hT := ih Q hrkQ T₁ T₂
        have hlen_eq : F₁.len = F₂.len := by
          have htlen : F₁.len - 1 = F₂.len - 1 := hT.1
          omega
        refine ⟨hlen_eq, fun i h₁ h₂ => ?_⟩
        cases i with
        | zero => exact F₁.step_zero.trans F₂.step_zero.symm
        | succ i =>
          have hstepQ : quotLat (F₁.step ⟨i + 1, Nat.lt_succ_of_le h₁⟩) M₁ =
              quotLat (F₂.step ⟨i + 1, Nat.lt_succ_of_le h₂⟩) M₁ :=
            hT.2 i (by show i ≤ F₁.len - 1; omega) (by show i ≤ F₂.len - 1; omega)
          have hge1 : M₁ ≤ F₁.step ⟨i + 1, Nat.lt_succ_of_le h₁⟩ := by
            rw [← h1eq]
            exact F₁.step_strictMono.monotone (show (⟨1, _⟩ : Fin (F₁.len + 1)) ≤ ⟨i + 1, _⟩ from by
              show 1 ≤ i + 1; omega)
          have hge2 : M₁ ≤ F₂.step ⟨i + 1, Nat.lt_succ_of_le h₂⟩ := by
            rw [← h2eq]
            exact F₂.step_strictMono.monotone (show (⟨1, _⟩ : Fin (F₂.len + 1)) ≤ ⟨i + 1, _⟩ from by
              show 1 ≤ i + 1; omega)
          rw [← liftSub_quotLat hM₁_sat (F₁.step_saturated _) hge1,
            ← liftSub_quotLat hM₁_sat (F₂.step_saturated _) hge2, hstepQ]
  exact hrec (rk L) L le_rfl F₁ F₂

/-- The canonical Harder–Narasimhan filtration of any discrete lattice `L ⊂ E`. -/
def canonicalHN (L : Submodule ℤ E) [DiscreteTopology L] : HNFiltration L :=
  Classical.choice (exists_hnFiltration L)

end HarderNarasimhan

/-! ## Section 4: Harder–Narasimhan Polygon, Concavity & `Stage2HodgeWeights.polygon` Bridge -/

section HNPolygon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Telescoping rank and degree formulas along any `HNFiltration L`. -/
theorem HNFiltration.rk_step_eq_sum {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (j : Fin (F.len + 1)) :
    rk (F.step j) = ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < j.1), rk (F.quot i) := by
  have hrec : ∀ m : ℕ, (hm : m ≤ F.len) →
      rk (F.step ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), rk (F.quot i) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ : Fin (F.len + 1)) = 0 := Fin.ext rfl
      rw [h0, F.step_zero]
      simp [rk]
    | succ m ih =>
      intro hm
      let i_m : Fin F.len := ⟨m, hm⟩
      have : DiscreteTopology (F.step i_m.succ) := discreteTopology_of_le (F.step_saturated i_m.succ).1
      have hsat : IsSaturated (F.step i_m.succ) (F.step i_m.castSucc) :=
        isSaturated_of_le_of_isSaturated (F.step_saturated i_m.castSucc)
          (F.step_strictMono (Fin.castSucc_lt_succ (i := i_m))).le (F.step_saturated i_m.succ).1
      have hadd := rk_add_quotLat hsat
      have hfilt : Finset.univ.filter (fun i : Fin F.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]
        omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F.len => i.1 < m) := by
        simp [i_m]
      have hih := ih (Nat.le_of_succ_le hm)
      rw [hfilt, Finset.sum_insert hnotmem]
      change rk (F.step i_m.succ) = rk (F.step i_m.castSucc) + rk (F.quot i_m) at hadd
      change rk (F.step i_m.castSucc) = _ at hih
      change rk (F.step i_m.succ) = rk (F.quot i_m) + _
      omega
  exact hrec j.1 (Nat.le_of_lt_succ j.2)

theorem HNFiltration.degAr_step_eq_sum {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (j : Fin (F.len + 1)) :
    degAr (F.step j) = ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < j.1), degAr (F.quot i) := by
  have hrec : ∀ m : ℕ, (hm : m ≤ F.len) →
      degAr (F.step ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), degAr (F.quot i) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ : Fin (F.len + 1)) = 0 := Fin.ext rfl
      rw [h0, F.step_zero, degAr_bot]
      simp
    | succ m ih =>
      intro hm
      let i_m : Fin F.len := ⟨m, hm⟩
      have : DiscreteTopology (F.step i_m.succ) := discreteTopology_of_le (F.step_saturated i_m.succ).1
      have hsat : IsSaturated (F.step i_m.succ) (F.step i_m.castSucc) :=
        isSaturated_of_le_of_isSaturated (F.step_saturated i_m.castSucc)
          (F.step_strictMono (Fin.castSucc_lt_succ (i := i_m))).le (F.step_saturated i_m.succ).1
      have hadd := degAr_eq_add_quotLat hsat
      have hfilt : Finset.univ.filter (fun i : Fin F.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]
        omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F.len => i.1 < m) := by
        simp [i_m]
      have hih := ih (Nat.le_of_succ_le hm)
      rw [hfilt, Finset.sum_insert hnotmem]
      change degAr (F.step i_m.succ) = degAr (F.step i_m.castSucc) + degAr (F.quot i_m) at hadd
      change degAr (F.step i_m.castSucc) = _ at hih
      change degAr (F.step i_m.succ) = degAr (F.quot i_m) + _
      linarith
  exact hrec j.1 (Nat.le_of_lt_succ j.2)

theorem HNFiltration.rk_eq_sum {L : Submodule ℤ E} [DiscreteTopology L] (F : HNFiltration L) :
    rk L = ∑ i : Fin F.len, rk (F.quot i) := by
  have h := F.rk_step_eq_sum (Fin.last F.len)
  rw [F.step_last] at h
  have hf : Finset.univ.filter (fun i : Fin F.len => i.1 < (Fin.last F.len).1) = Finset.univ := by
    ext i; simp
  rwa [hf] at h

theorem HNFiltration.degAr_eq_sum {L : Submodule ℤ E} [DiscreteTopology L] (F : HNFiltration L) :
    degAr L = ∑ i : Fin F.len, (rk (F.quot i) : ℝ) * F.hnSlope i := by
  have h := F.degAr_step_eq_sum (Fin.last F.len)
  rw [F.step_last] at h
  have hf : Finset.univ.filter (fun i : Fin F.len => i.1 < (Fin.last F.len).1) = Finset.univ := by
    ext i; simp
  rw [hf] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : DiscreteTopology (F.quot i) := F.quot_discrete i
  have hrpos : (0 : ℝ) < (rk (F.quot i) : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot _ (F.quot_ne_bot i))
  unfold HNFiltration.hnSlope ArakelovCovolume.slope
  exact (mul_div_cancel₀ _ hrpos.ne').symm

/-- The Harder–Narasimhan slope multiset of `F`, repeating each slope `μ_i` with multiplicity
`rk (L_{i+1} / L_i)`. -/
def HNFiltration.slopeMultiset {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) : Multiset ℝ :=
  ∑ i : Fin F.len, Multiset.replicate (rk (F.quot i)) (F.hnSlope i)

/-- The descending list of all `rk L` Harder–Narasimhan slopes `μ_1 ≥ ... ≥ μ_{rk L}`! -/
def HNFiltration.slopesDesc {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) : List ℝ :=
  (List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)

/-- The **Harder–Narasimhan Polygon** `hnPolygon F m` at abscissa `m : ℕ`:
the sum of the `m` largest Harder–Narasimhan slopes of `L`. -/
def HNFiltration.hnPolygon {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (m : ℕ) : ℝ :=
  ((F.slopesDesc).take m).sum

private lemma list_sum_flatMap {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma HNFiltration.slopesDesc_coe {L : Submodule ℤ E} [DiscreteTopology L] (F : HNFiltration L) :
    ((F.slopesDesc : List ℝ) : Multiset ℝ) = F.slopeMultiset := by
  unfold slopesDesc slopeMultiset
  have h1 : ∀ (l : List (Fin F.len)),
      ((l.flatMap fun i => List.replicate (rk (F.quot i)) (F.hnSlope i) : List ℝ) : Multiset ℝ) =
      (l.map fun i => Multiset.replicate (rk (F.quot i)) (F.hnSlope i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons,
        Multiset.coe_replicate]
  rw [h1]
  have h2 : (Finset.univ : Finset (Fin F.len)).val = (List.finRange F.len : Multiset (Fin F.len)) := by
    apply Multiset.ext.mpr
    intro i
    rw [Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin F.len)).nodup (Finset.mem_univ i),
      Multiset.count_eq_one_of_mem (Multiset.coe_nodup.mpr (List.nodup_finRange F.len))
        (Multiset.mem_coe.mpr (List.mem_finRange i))]
  rw [Finset.sum_eq_multiset_sum]
  change ((List.map (fun i => Multiset.replicate (rk (F.quot i)) (F.hnSlope i)) (List.finRange F.len) :
      List (Multiset ℝ)) : Multiset (Multiset ℝ)).sum = _
  rw [← Multiset.map_coe, ← h2]

lemma HNFiltration.slopesDesc_length {L : Submodule ℤ E} [DiscreteTopology L] (F : HNFiltration L) :
    F.slopesDesc.length = rk L := by
  rw [F.rk_eq_sum]
  unfold slopesDesc
  rw [List.length_flatMap]
  have h1 : ((List.finRange F.len).map fun i => (List.replicate (rk (F.quot i)) (F.hnSlope i)).length).sum =
      ((List.finRange F.len).map fun i => rk (F.quot i)).sum := by
    congr 1; refine List.map_congr_left fun i _ => List.length_replicate
  rw [h1]
  exact (Fin.sum_univ_def (fun i : Fin F.len => rk (F.quot i))).symm

lemma HNFiltration.slopesDesc_pairwise_ge {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) :
    F.slopesDesc.Pairwise (· ≥ ·) := by
  unfold slopesDesc
  have hrec : ∀ (l : List (Fin F.len)), l.Pairwise (· < ·) →
      (l.flatMap fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)).Pairwise (· ≥ ·) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hpair
      rw [List.pairwise_cons] at hpair
      rw [List.flatMap_cons, List.pairwise_append]
      refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl), ih hpair.2, ?_⟩
      intro x hx y hy
      rw [List.mem_replicate] at hx
      rw [List.mem_flatMap] at hy
      rcases hy with ⟨b, hb, hyb⟩
      rw [List.mem_replicate] at hyb
      rw [hx.2, hyb.2]
      exact (F.slope_strictAnti a b (hpair.1 b hb)).le
  exact hrec (List.finRange F.len) (List.pairwise_lt_finRange F.len)

theorem HNFiltration.hnPolygon_zero {L : Submodule ℤ E} [DiscreteTopology L] (F : HNFiltration L) :
    F.hnPolygon 0 = 0 := by simp [hnPolygon]

theorem HNFiltration.hnPolygon_rk {L : Submodule ℤ E} [DiscreteTopology L] (F : HNFiltration L) :
    F.hnPolygon (rk L) = degAr L := by
  unfold hnPolygon
  rw [← F.slopesDesc_length, List.take_length]
  have hsum : (F.slopesDesc.sum : ℝ) = F.slopeMultiset.sum := by
    have := congrArg Multiset.sum F.slopesDesc_coe
    simpa using this
  rw [hsum, F.degAr_eq_sum]
  unfold slopeMultiset
  rw [Multiset.sum_sum]
  refine Finset.sum_congr rfl fun i _ => by simp [Multiset.sum_replicate, nsmul_eq_mul]

/-- **Concavity of the Harder–Narasimhan Polygon**:
the consecutive slopes `hnPolygon F (m + 1) - hnPolygon F m` are non-increasing! -/
theorem HNFiltration.hnPolygon_concave {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) {m : ℕ} (hm : m + 1 < rk L) :
    F.hnPolygon (m + 2) - F.hnPolygon (m + 1) ≤ F.hnPolygon (m + 1) - F.hnPolygon m := by
  set ls := F.slopesDesc
  have hlen : ls.length = rk L := F.slopesDesc_length
  have hm1 : m < ls.length := by omega
  have hm2 : m + 1 < ls.length := by omega
  have ht1 : (ls.take (m + 1)).sum = (ls.take m).sum + ls[m] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hm1, Option.toList_some, List.sum_append,
      List.sum_singleton]
  have ht2 : (ls.take (m + 2)).sum = (ls.take (m + 1)).sum + ls[m + 1] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hm2, Option.toList_some, List.sum_append,
      List.sum_singleton]
  have hpair := List.pairwise_iff_getElem.mp F.slopesDesc_pairwise_ge m (m + 1) hm1 hm2 (by omega)
  unfold hnPolygon
  change (ls.take (m + 2)).sum - (ls.take (m + 1)).sum ≤ (ls.take (m + 1)).sum - (ls.take m).sum
  linarith

/-- Ky Fan descending variational upper bound: any sub-multiset `T ≤ S` has
`T.sum ≤ ((ls).take T.card).sum` whenever `ls` is a descending sort of `S`. -/
private lemma sum_le_take_sum_of_le_sorted_ge :
    ∀ (ls : List ℝ), ls.Pairwise (· ≥ ·) →
      ∀ (T : Multiset ℝ), T ≤ (ls : Multiset ℝ) → T.sum ≤ (ls.take T.card).sum
  | [], _, T, hT => by
    have h0 : T = 0 := Multiset.le_zero.mp hT
    simp [h0]
  | a :: ls', hpair, T, hT => by
    rw [List.pairwise_cons] at hpair
    rcases hpair with ⟨ha, hls'⟩
    by_cases hT0 : T = 0
    · simp [hT0]
    · by_cases haT : a ∈ T
      · obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem haT
        have hT' : T' ≤ (ls' : Multiset ℝ) :=
          (Multiset.cons_le_cons_iff a).mp (by simpa using hT)
        have ih := sum_le_take_sum_of_le_sorted_ge ls' hls' T' hT'
        simp only [Multiset.card_cons, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
        linarith
      · have hTls' : T ≤ (ls' : Multiset ℝ) := by
          rw [Multiset.le_iff_count] at hT ⊢
          intro x
          have hx : T.count x ≤ (a ::ₘ (ls' : Multiset ℝ)).count x := by simpa using hT x
          by_cases hxa : x = a
          · subst hxa; rw [Multiset.count_eq_zero.mpr haT]; omega
          · rwa [Multiset.count_cons_of_ne hxa] at hx
        obtain ⟨x, hxT⟩ := Multiset.exists_mem_of_ne_zero hT0
        obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem hxT
        have hxa : x ≤ a := ha x (by simpa using Multiset.mem_of_le hTls' hxT)
        have hT'ls' : T' ≤ (ls' : Multiset ℝ) := le_trans (Multiset.le_cons_self T' x) hTls'
        have ih := sum_le_take_sum_of_le_sorted_ge ls' hls' T' hT'ls'
        simp only [Multiset.card_cons, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
        linarith

/-- **Vertex Attainment of the Harder–Narasimhan Polygon**:
at every filtration vertex `j : Fin (F.len + 1)`, `hnPolygon F (rk (F.step j)) = degAr (F.step j)`! -/
theorem HNFiltration.hnPolygon_at_step {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (j : Fin (F.len + 1)) :
    F.hnPolygon (rk (F.step j)) = degAr (F.step j) := by
  -- Split `List.finRange F.len` at `j.1`: prefix has indices `< j.1`, suffix has `≥ j.1`
  have hsplit : List.finRange F.len =
      (List.finRange F.len).take j.1 ++ (List.finRange F.len).drop j.1 :=
    (List.take_append_drop j.1 _).symm
  let pref := ((List.finRange F.len).take j.1).flatMap
    fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)
  let suff := ((List.finRange F.len).drop j.1).flatMap
    fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)
  have hdesc_eq : F.slopesDesc = pref ++ suff := by
    unfold slopesDesc
    conv_lhs => rw [hsplit, List.flatMap_append]
  have hpref_len : pref.length = rk (F.step j) := by
    rw [F.rk_step_eq_sum j]
    dsimp only [pref]
    rw [List.length_flatMap]
    have hmap : (((List.finRange F.len).take j.1).map fun i =>
        (List.replicate (rk (F.quot i)) (F.hnSlope i)).length).sum =
        (((List.finRange F.len).take j.1).map fun i => rk (F.quot i)).sum := by
      congr 1; refine List.map_congr_left fun i _ => List.length_replicate
    rw [hmap]
    -- `((List.finRange F.len).take j.1)` has the exact elements of `Finset.univ.filter (·.1 < j.1)`
    have hnodup : ((List.finRange F.len).take j.1).Nodup :=
      (List.nodup_finRange F.len).sublist (List.take_sublist _ _)
    have htoFinset : ((List.finRange F.len).take j.1).toFinset =
        Finset.univ.filter (fun i : Fin F.len => i.1 < j.1) := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hi
        rw [List.length_take] at hk
        rw [List.getElem_take, List.getElem_finRange] at hget
        rw [← hget]
        exact lt_of_lt_of_le hk (min_le_left _ _)
      · intro hi
        have hlt : i.1 < ((List.finRange F.len).take j.1).length := by
          rw [List.length_take, List.length_finRange]; omega
        refine List.mem_iff_getElem.mpr ⟨i.1, hlt, ?_⟩
        rw [List.getElem_take, List.getElem_finRange]
        ext; rfl
    rw [← htoFinset, List.sum_toFinset _ hnodup]
  have hpref_sum : pref.sum = degAr (F.step j) := by
    rw [F.degAr_step_eq_sum j]
    dsimp only [pref]
    rw [list_sum_flatMap]
    have hmap : (((List.finRange F.len).take j.1).map fun i =>
        (List.replicate (rk (F.quot i)) (F.hnSlope i)).sum).sum =
        (((List.finRange F.len).take j.1).map fun i => degAr (F.quot i)).sum := by
      congr 1
      refine List.map_congr_left fun i _ => ?_
      rw [List.sum_replicate, nsmul_eq_mul]
      have : DiscreteTopology (F.quot i) := F.quot_discrete i
      have hrpos : (0 : ℝ) < (rk (F.quot i) : ℝ) :=
        Nat.cast_pos.mpr (rk_pos_of_ne_bot _ (F.quot_ne_bot i))
      unfold HNFiltration.hnSlope ArakelovCovolume.slope
      exact mul_div_cancel₀ _ hrpos.ne'
    rw [hmap]
    have hnodup : ((List.finRange F.len).take j.1).Nodup :=
      (List.nodup_finRange F.len).sublist (List.take_sublist _ _)
    have htoFinset : ((List.finRange F.len).take j.1).toFinset =
        Finset.univ.filter (fun i : Fin F.len => i.1 < j.1) := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hi
        rw [List.length_take] at hk
        rw [List.getElem_take, List.getElem_finRange] at hget
        rw [← hget]
        exact lt_of_lt_of_le hk (min_le_left _ _)
      · intro hi
        have hlt : i.1 < ((List.finRange F.len).take j.1).length := by
          rw [List.length_take, List.length_finRange]; omega
        refine List.mem_iff_getElem.mpr ⟨i.1, hlt, ?_⟩
        rw [List.getElem_take, List.getElem_finRange]
        ext; rfl
    rw [← htoFinset, List.sum_toFinset _ hnodup]
  unfold hnPolygon
  rw [hdesc_eq, ← hpref_len, List.take_left, hpref_sum]

/-- **Stuhler–Grayson Upper Concave Envelope Theorem**:
for EVERY sublattice `M ≤ L` (saturated or not!), the point `(rk M, degAr M)` lies on or below
the Harder–Narasimhan polygon: `degAr M ≤ hnPolygon F (rk M)`! -/
theorem HNFiltration.degAr_le_hnPolygon {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) {M : Submodule ℤ E} (hML : M ≤ L) :
    degAr M ≤ F.hnPolygon (rk M) := by
  -- Pass to saturation `M' = saturation L M` (same rank, larger degree)
  let M' := saturation L M
  have hM'sat : IsSaturated L M' := isSaturated_saturation hML
  have hsat_cov := covol_saturation_le hML
  have hsat_rk := rk_saturation hML
  refine hsat_cov.2.trans ?_
  rw [← hsat_rk]
  -- Filter `M'` by `M_j = M' ⊓ F.step j`
  let Mstep : Fin (F.len + 1) → Submodule ℤ E := fun j => M' ⊓ F.step j
  let Mquot : Fin F.len → Submodule ℤ E := fun i => quotLat (Mstep i.succ) (Mstep i.castSucc)
  have hMstep_sat : ∀ j, IsSaturated L (Mstep j) :=
    fun j => isSaturated_inf hM'sat (F.step_saturated j)
  have hMstep_mono : ∀ i : Fin F.len, Mstep i.castSucc ≤ Mstep i.succ :=
    fun i => inf_le_inf_left M' (F.step_strictMono (Fin.castSucc_lt_succ (i := i))).le
  have hMquot_rk : ∀ i : Fin F.len, rk (Mquot i) ≤ rk (F.quot i) ∧
      degAr (Mquot i) ≤ (rk (Mquot i) : ℝ) * F.hnSlope i := by
    intro i
    have : DiscreteTopology (Mstep i.succ) := discreteTopology_of_le (hMstep_sat i.succ).1
    have hsat_i : IsSaturated (Mstep i.succ) (Mstep i.castSucc) :=
      isSaturated_of_le_of_isSaturated (hMstep_sat i.castSucc) (hMstep_mono i) (hMstep_sat i.succ).1
    have : DiscreteTopology (Mquot i) := discreteTopology_quotLat hsat_i
    have : DiscreteTopology (F.quot i) := F.quot_discrete i
    -- `projOrth (F.step i.castSucc)` maps `Mquot i` injectively into `F.quot i` with norm `≤ 1`
    have himg : ∀ y ∈ Mquot i, projOrth (F.step i.castSucc) y ∈ F.quot i := by
      rintro _ ⟨x, hx, rfl⟩
      change projOrth (F.step i.castSucc) (projOrth (Mstep i.castSucc) x) ∈ F.quot i
      rw [projOrth_comp_of_le inf_le_right x]
      exact ⟨x, hx.2, rfl⟩
    let φ : Mquot i →ₗ[ℤ] F.quot i :=
      { toFun := fun y => ⟨projOrth (F.step i.castSucc) y.1, himg y.1 y.2⟩
        map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
        map_smul' := fun c a => Subtype.ext (map_zsmul _ c a.1) }
    have hφ_inj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      have h0 : projOrth (F.step i.castSucc) (a.1 - b.1) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr (congrArg (fun z : F.quot i => (z : E)) hab)
      obtain ⟨x, hx, hxeq⟩ := (Mquot i).sub_mem a.2 b.2
      have hxeq' : projOrth (Mstep i.castSucc) x = a.1 - b.1 := hxeq
      have hx_proj : projOrth (F.step i.castSucc) x = 0 := by
        rw [← projOrth_comp_of_le inf_le_right x, hxeq', h0]
      have hx_step : x ∈ F.step i.castSucc :=
        (F.step_saturated i.castSucc).2 x ((hMstep_sat i.succ).1 hx)
          ((projOrth_eq_zero_iff _ x).mp hx_proj)
      have hx_prev : x ∈ Mstep i.castSucc := ⟨hx.1, hx_step⟩
      have hsub0 : a.1 - b.1 = 0 := by
        rw [← hxeq']
        exact (projOrth_eq_zero_iff _ x).mpr (Submodule.subset_span hx_prev)
      exact sub_eq_zero.mp hsub0
    have hφ_lip : ∀ y : Mquot i, ‖((φ y : F.quot i) : E)‖ ≤ 1 * ‖(y : E)‖ := by
      intro y; rw [one_mul]; exact norm_projOrth_le _ y.1
    have hdeg := bost_degree_inequality (Mquot i) (F.quot i) φ 1 hφ_inj hφ_lip
    rw [Real.log_one, add_zero,
      (isSemistable_iff_muMax_eq_slope (F.quot i) (F.quot_ne_bot i)).mp (F.quot_semistable i)] at hdeg
    have hrk_le : rk (Mquot i) ≤ rk (F.quot i) := by
      let g : Mquot i →ₗ[ℤ] E := (F.quot i).subtype.comp φ
      have hginj : Function.Injective g := (F.quot i).injective_subtype.comp hφ_inj
      let e := LinearEquiv.ofInjective g hginj
      have hle : LinearMap.range g ≤ F.quot i := by rintro _ ⟨y, rfl⟩; exact (φ y).2
      calc rk (Mquot i) = rk (LinearMap.range g) := e.finrank_eq
        _ ≤ rk (F.quot i) := RHDirect.Stage3ThetaSiegelBridge.rk_le_of_le hle
    exact ⟨hrk_le, hdeg⟩
  -- Telescoping rank and degree of `M'`
  have hrec : ∀ m : ℕ, (hm : m ≤ F.len) →
      rk (Mstep ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), rk (Mquot i) ∧
      degAr (Mstep ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), degAr (Mquot i) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : Mstep ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ = ⊥ := by
        dsimp only [Mstep]
        rw [show (⟨0, _⟩ : Fin (F.len + 1)) = 0 from Fin.ext rfl, F.step_zero, inf_bot_eq]
      rw [h0, degAr_bot]
      simp [rk]
    | succ m ih =>
      intro hm
      let i_m : Fin F.len := ⟨m, hm⟩
      have : DiscreteTopology (Mstep i_m.succ) := discreteTopology_of_le (hMstep_sat i_m.succ).1
      have hsat : IsSaturated (Mstep i_m.succ) (Mstep i_m.castSucc) :=
        isSaturated_of_le_of_isSaturated (hMstep_sat i_m.castSucc) (hMstep_mono i_m) (hMstep_sat i_m.succ).1
      have hfilt : Finset.univ.filter (fun i : Fin F.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]
        omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F.len => i.1 < m) := by simp [i_m]
      have hprev := ih (Nat.le_of_succ_le hm)
      have hadd_rk := rk_add_quotLat hsat
      have hadd_deg := degAr_eq_add_quotLat hsat
      change rk (Mstep i_m.succ) = rk (Mstep i_m.castSucc) + rk (Mquot i_m) at hadd_rk
      change degAr (Mstep i_m.succ) = degAr (Mstep i_m.castSucc) + degAr (Mquot i_m) at hadd_deg
      change rk (Mstep i_m.castSucc) = _ ∧ degAr (Mstep i_m.castSucc) = _ at hprev
      refine ⟨?_, ?_⟩
      · rw [hfilt, Finset.sum_insert hnotmem]
        change rk (Mstep i_m.succ) = rk (Mquot i_m) + _
        omega
      · rw [hfilt, Finset.sum_insert hnotmem]
        change degAr (Mstep i_m.succ) = degAr (Mquot i_m) + _
        linarith
  have hM'_last : Mstep ⟨F.len, Nat.lt_succ_self _⟩ = M' := by
    dsimp only [Mstep]
    rw [show (⟨F.len, Nat.lt_succ_self _⟩ : Fin (F.len + 1)) = Fin.last F.len from rfl,
      F.step_last, inf_eq_left.mpr hM'sat.1]
  have htot := hrec F.len le_rfl
  rw [hM'_last] at htot
  have hf : Finset.univ.filter (fun i : Fin F.len => i.1 < F.len) = Finset.univ := by
    ext i; simp
  rw [hf] at htot
  let T : Multiset ℝ := ∑ i : Fin F.len, Multiset.replicate (rk (Mquot i)) (F.hnSlope i)
  have hT_le : T ≤ (F.slopesDesc : Multiset ℝ) := by
    rw [F.slopesDesc_coe]
    unfold HNFiltration.slopeMultiset
    exact Finset.sum_le_sum fun i _ =>
      Multiset.le_iff_count.mpr fun x => by
        simp only [Multiset.count_replicate]
        split_ifs
        · exact (hMquot_rk i).1
        · exact le_rfl
  have hT_card : T.card = rk M' := by
    rw [htot.1]
    dsimp only [T]
    classical
    induction (Finset.univ : Finset (Fin F.len)) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, ih]
  have hT_sum : T.sum = ∑ i : Fin F.len, (rk (Mquot i) : ℝ) * F.hnSlope i := by
    dsimp only [T]
    rw [Multiset.sum_sum]
    refine Finset.sum_congr rfl fun i _ => by simp [Multiset.sum_replicate, nsmul_eq_mul]
  have hky := sum_le_take_sum_of_le_sorted_ge F.slopesDesc F.slopesDesc_pairwise_ge T hT_le
  rw [hT_card, hT_sum] at hky
  calc degAr M' = ∑ i : Fin F.len, degAr (Mquot i) := htot.2
    _ ≤ ∑ i : Fin F.len, (rk (Mquot i) : ℝ) * F.hnSlope i :=
        Finset.sum_le_sum fun i _ => (hMquot_rk i).2
    _ ≤ F.hnPolygon (rk M') := hky

/-- The first Harder–Narasimhan slope `hnPolygon F 1` equals `muMax L`! -/
theorem HNFiltration.hnPolygon_one_eq_muMax {L : Submodule ℤ E} [DiscreteTopology L]
    (hL0 : L ≠ ⊥) (F : HNFiltration L) :
    F.hnPolygon 1 = muMax L := by
  have hpos := F.len_pos_of_ne_bot hL0
  let i₀ : Fin F.len := ⟨0, hpos⟩
  have h1 : F.step ⟨1, Nat.succ_lt_succ hpos⟩ = maxDestab L :=
    hnFiltration_first_eq_maxDestab L hL0 F
  have hq0 : F.quot i₀ = maxDestab L := by
    change quotLat (F.step i₀.succ) (F.step i₀.castSucc) = maxDestab L
    have h0 : i₀.castSucc = (0 : Fin (F.len + 1)) := Fin.ext rfl
    have h1' : i₀.succ = ⟨1, Nat.succ_lt_succ hpos⟩ := Fin.ext rfl
    rw [h0, h1', F.step_zero, quotLat_bot, h1]
  have : DiscreteTopology (F.quot i₀) := F.quot_discrete i₀
  have hrpos : 0 < rk (F.quot i₀) := rk_pos_of_ne_bot _ (F.quot_ne_bot i₀)
  have hhead : F.slopesDesc.take 1 = [F.hnSlope i₀] := by
    unfold slopesDesc
    have hfr : ∃ tl, List.finRange F.len = i₀ :: tl := by
      cases h : List.finRange F.len with
      | nil =>
        have := congrArg List.length h
        rw [List.length_finRange, List.length_nil] at this
        omega
      | cons a tl =>
        refine ⟨tl, ?_⟩
        have h0 : a = (List.finRange F.len)[0]'(by rw [List.length_finRange]; exact hpos) := by
          simp [h]
        rw [h0, List.getElem_finRange]
        rfl
    obtain ⟨tl, htl⟩ := hfr
    rw [htl, List.flatMap_cons]
    cases hr : rk (F.quot i₀) with
    | zero => omega
    | succ k => simp [List.replicate_succ]
  unfold hnPolygon
  rw [hhead, List.sum_singleton]
  unfold hnSlope
  rw [hq0, slope_maxDestab L hL0]

/-- **Exact Bridge to `Stage2HodgeWeights.polygon` & `Stage2HodgeWeights.polygon_convex`**:
whenever a rational slope multiset `S : Multiset ℚ` represents the negated Harder–Narasimhan
slopes (`S.map (fun q : ℚ => -(q : ℝ)) = F.slopeMultiset`), the concave Arakelov HN polygon
equals the negated convex Hodge/Newton polygon `-(Stage2HodgeWeights.polygon S m : ℝ)` at
every abscissa `m : ℕ`! -/
theorem HNFiltration.hnPolygon_eq_neg_hodgePolygon {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (S : Multiset ℚ)
    (hS : S.map (fun q : ℚ => -(q : ℝ)) = F.slopeMultiset) (m : ℕ) :
    F.hnPolygon m = -(RHDirect.Stage2HodgeWeights.polygon S m : ℝ) := by
  let lsS : List ℝ := (RHDirect.Stage2HodgeWeights.sortedSlopes S).map (fun q : ℚ => -(q : ℝ))
  have hpair_S : lsS.Pairwise (· ≥ ·) := by
    refine List.Pairwise.map (fun q : ℚ => -(q : ℝ)) ?_
      (RHDirect.Stage2HodgeWeights.sortedSlopes_pairwise S)
    intro a b hab
    exact neg_le_neg (Rat.cast_le.mpr hab)
  have hperm : lsS.Perm F.slopesDesc := by
    rw [← Multiset.coe_eq_coe]
    have h1 : (lsS : Multiset ℝ) = S.map (fun q : ℚ => -(q : ℝ)) := by
      dsimp only [lsS]
      rw [← Multiset.map_coe, RHDirect.Stage2HodgeWeights.sortedSlopes_coe S]
    rw [h1, hS, F.slopesDesc_coe]
  have hlist_eq : F.slopesDesc = lsS :=
    (hperm.symm).eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h2 h1)
      F.slopesDesc_pairwise_ge hpair_S
  unfold hnPolygon RHDirect.Stage2HodgeWeights.polygon
  rw [hlist_eq]
  dsimp only [lsS]
  rw [← List.map_take, Rat.cast_list_sum]
  have hneg : ∀ (l : List ℚ), (l.map (fun q : ℚ => -(q : ℝ))).sum = -(l.map (fun q : ℚ => (q : ℝ))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]; ring
  exact hneg _

/-- **Unconditional Rational-Approximation Bridge to `Stage2HodgeWeights.polygon_convex`**:
for ANY discrete lattice `L ⊂ E` (even with irrational real Arakelov slopes!) and ANY `ε > 0`,
there exist rational slope multisets `S_lo, S_hi : Multiset ℚ` of cardinality `rk L` whose convex
Hodge/Newton polygons `Stage2HodgeWeights.polygon S_lo` and `Stage2HodgeWeights.polygon S_hi`
(each satisfying `Stage2HodgeWeights.polygon_convex`) sandwich `-F.hnPolygon m` within `m * ε`
at every abscissa `m ≤ rk L`! -/
theorem HNFiltration.exists_rat_hodgePolygon_approx {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S_lo S_hi : Multiset ℚ),
      S_lo.card = rk L ∧ S_hi.card = rk L ∧
      (∀ m, m + 1 < rk L →
        RHDirect.Stage2HodgeWeights.polygon S_lo (m + 1) - RHDirect.Stage2HodgeWeights.polygon S_lo m ≤
          RHDirect.Stage2HodgeWeights.polygon S_lo (m + 2) - RHDirect.Stage2HodgeWeights.polygon S_lo (m + 1)) ∧
      (∀ m, m + 1 < rk L →
        RHDirect.Stage2HodgeWeights.polygon S_hi (m + 1) - RHDirect.Stage2HodgeWeights.polygon S_hi m ≤
          RHDirect.Stage2HodgeWeights.polygon S_hi (m + 2) - RHDirect.Stage2HodgeWeights.polygon S_hi (m + 1)) ∧
      ∀ m ≤ rk L,
        -(RHDirect.Stage2HodgeWeights.polygon S_hi m : ℝ) ≤ F.hnPolygon m ∧
        F.hnPolygon m ≤ -(RHDirect.Stage2HodgeWeights.polygon S_lo m : ℝ) ∧
        -(RHDirect.Stage2HodgeWeights.polygon S_lo m : ℝ) -
          (-(RHDirect.Stage2HodgeWeights.polygon S_hi m : ℝ)) ≤ (m : ℝ) * ε := by
  have hδ_ex : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε / 2 ∧
      ∀ i j : Fin F.len, i < j → 2 * δ ≤ -F.hnSlope j - (-F.hnSlope i) := by
    let pairs : Finset (Fin F.len × Fin F.len) := Finset.univ.filter fun p => p.1 < p.2
    by_cases hp : pairs.Nonempty
    · let m_gap := pairs.inf' hp fun p => (-F.hnSlope p.2 - (-F.hnSlope p.1)) / 2
      have hm_pos : 0 < m_gap := (Finset.lt_inf'_iff hp).mpr fun p hp' => by
        have hlt : F.hnSlope p.2 < F.hnSlope p.1 := F.slope_strictAnti p.1 p.2 (Finset.mem_filter.mp hp').2
        linarith
      refine ⟨min (ε / 2) m_gap, lt_min (half_pos hε) hm_pos, min_le_left _ _, fun i j hij => ?_⟩
      have hmem : (i, j) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      have hle : m_gap ≤ (-F.hnSlope j - (-F.hnSlope i)) / 2 := Finset.inf'_le _ hmem
      have hmin : min (ε / 2) m_gap ≤ m_gap := min_le_right _ _
      linarith
    · refine ⟨ε / 2, half_pos hε, le_rfl, fun i j hij => ?_⟩
      exact absurd ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩ hp
  obtain ⟨δ, hδ_pos, hδ_le, hδ_sep⟩ := hδ_ex
  have hex' : ∀ i : Fin F.len, ∃ (al ah : ℚ),
      -F.hnSlope i - δ < (al : ℝ) ∧ (al : ℝ) ≤ -F.hnSlope i ∧
      -F.hnSlope i ≤ (ah : ℝ) ∧ (ah : ℝ) < -F.hnSlope i + δ := by
    intro i
    obtain ⟨al, hal1, hal2⟩ := exists_rat_btwn (show -F.hnSlope i - δ < -F.hnSlope i by linarith)
    obtain ⟨ah, hah1, hah2⟩ := exists_rat_btwn (show -F.hnSlope i < -F.hnSlope i + δ by linarith)
    exact ⟨al, ah, hal1, hal2.le, hah1.le, hah2⟩
  choose al ah hal1 hal2 hah1 hah2 using hex'
  let l_lo : List ℚ := (List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) (al i)
  let l_hi : List ℚ := (List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) (ah i)
  let S_lo : Multiset ℚ := (l_lo : Multiset ℚ)
  let S_hi : Multiset ℚ := (l_hi : Multiset ℚ)
  have hal_mono : ∀ i j : Fin F.len, i < j → al i ≤ al j := fun i j hij => by
    have h1 := hδ_sep i j hij
    have h2 : (al i : ℝ) ≤ (al j : ℝ) := by linarith [hal2 i, hal1 j]
    exact Rat.cast_le.mp h2
  have hah_mono : ∀ i j : Fin F.len, i < j → ah i ≤ ah j := fun i j hij => by
    have h1 := hδ_sep i j hij
    have h2 : (ah i : ℝ) ≤ (ah j : ℝ) := by linarith [hah2 i, hah1 j]
    exact Rat.cast_le.mp h2
  have hpair_list : ∀ (f : Fin F.len → ℚ), (∀ i j, i < j → f i ≤ f j) →
      ((List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) (f i)).Pairwise (· ≤ ·) := by
    intro f hf
    have hrec : ∀ (l : List (Fin F.len)), l.Pairwise (· < ·) →
        (l.flatMap fun i => List.replicate (rk (F.quot i)) (f i)).Pairwise (· ≤ ·) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a l ih =>
        intro hp
        rw [List.pairwise_cons] at hp
        rw [List.flatMap_cons, List.pairwise_append]
        refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl), ih hp.2, ?_⟩
        intro x hx y hy
        rw [List.mem_replicate] at hx
        rw [List.mem_flatMap] at hy
        rcases hy with ⟨b, hb, hyb⟩
        rw [List.mem_replicate] at hyb
        rw [hx.2, hyb.2]
        exact hf a b (hp.1 b hb)
    exact hrec (List.finRange F.len) (List.pairwise_lt_finRange F.len)
  have hsort_lo : RHDirect.Stage2HodgeWeights.sortedSlopes S_lo = l_lo := by
    have hperm : (RHDirect.Stage2HodgeWeights.sortedSlopes S_lo).Perm l_lo := by
      rw [← Multiset.coe_eq_coe, RHDirect.Stage2HodgeWeights.sortedSlopes_coe]
    exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
      (RHDirect.Stage2HodgeWeights.sortedSlopes_pairwise S_lo) (hpair_list al hal_mono)
  have hsort_hi : RHDirect.Stage2HodgeWeights.sortedSlopes S_hi = l_hi := by
    have hperm : (RHDirect.Stage2HodgeWeights.sortedSlopes S_hi).Perm l_hi := by
      rw [← Multiset.coe_eq_coe, RHDirect.Stage2HodgeWeights.sortedSlopes_coe]
    exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
      (RHDirect.Stage2HodgeWeights.sortedSlopes_pairwise S_hi) (hpair_list ah hah_mono)
  have hlen_lo : l_lo.length = rk L := by
    rw [F.rk_eq_sum]; dsimp only [l_lo]; rw [List.length_flatMap]
    have h1 : ((List.finRange F.len).map fun i => (List.replicate (rk (F.quot i)) (al i)).length).sum =
        ((List.finRange F.len).map fun i => rk (F.quot i)).sum := by
      congr 1; refine List.map_congr_left fun i _ => List.length_replicate
    rw [h1]; exact (Fin.sum_univ_def _).symm
  have hlen_hi : l_hi.length = rk L := by
    rw [F.rk_eq_sum]; dsimp only [l_hi]; rw [List.length_flatMap]
    have h1 : ((List.finRange F.len).map fun i => (List.replicate (rk (F.quot i)) (ah i)).length).sum =
        ((List.finRange F.len).map fun i => rk (F.quot i)).sum := by
      congr 1; refine List.map_congr_left fun i _ => List.length_replicate
    rw [h1]; exact (Fin.sum_univ_def _).symm
  have hcard_lo : S_lo.card = rk L := by simpa [S_lo] using hlen_lo
  have hcard_hi : S_hi.card = rk L := by simpa [S_hi] using hlen_hi
  -- Pointwise entry comparison between `l_lo`, `-F.slopesDesc`, and `l_hi`
  have hzip_bounds : ∀ (l : List (Fin F.len)),
      ∀ (k : ℕ),
        ((l.flatMap fun i => List.replicate (rk (F.quot i)) ((al i : ℝ))).take k).sum ≤
          ((l.flatMap fun i => List.replicate (rk (F.quot i)) (-F.hnSlope i)).take k).sum ∧
        ((l.flatMap fun i => List.replicate (rk (F.quot i)) (-F.hnSlope i)).take k).sum ≤
          ((l.flatMap fun i => List.replicate (rk (F.quot i)) ((ah i : ℝ))).take k).sum ∧
        ((l.flatMap fun i => List.replicate (rk (F.quot i)) ((ah i : ℝ))).take k).sum -
          ((l.flatMap fun i => List.replicate (rk (F.quot i)) ((al i : ℝ))).take k).sum ≤
          (min k (l.flatMap fun i => List.replicate (rk (F.quot i)) (0 : ℝ)).length : ℝ) * ε := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons a l ih =>
      intro k
      simp only [List.flatMap_cons, List.take_append, List.sum_append, List.length_append,
        List.length_replicate, List.take_replicate, List.sum_replicate, nsmul_eq_mul]
      have ih' := ih (k - rk (F.quot a))
      have hcast_min : ((min k (rk (F.quot a)) : ℕ) : ℝ) +
          ((min (k - rk (F.quot a)) (l.flatMap fun i => List.replicate (rk (F.quot i)) (0 : ℝ)).length : ℕ) : ℝ) =
          ((min k (rk (F.quot a) + (l.flatMap fun i => List.replicate (rk (F.quot i)) (0 : ℝ)).length) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : min k (rk (F.quot a)) +
          min (k - rk (F.quot a)) (l.flatMap fun i => List.replicate (rk (F.quot i)) (0 : ℝ)).length =
          min k (rk (F.quot a) + (l.flatMap fun i => List.replicate (rk (F.quot i)) (0 : ℝ)).length))
      have hdiff_a : (ah a : ℝ) - (al a : ℝ) ≤ ε := by linarith [hal1 a, hah2 a, hδ_le]
      have hmul1 : ((min k (rk (F.quot a)) : ℕ) : ℝ) * (al a : ℝ) ≤
          ((min k (rk (F.quot a)) : ℕ) : ℝ) * (-F.hnSlope a) :=
        mul_le_mul_of_nonneg_left (hal2 a) (Nat.cast_nonneg _)
      have hmul2 : ((min k (rk (F.quot a)) : ℕ) : ℝ) * (-F.hnSlope a) ≤
          ((min k (rk (F.quot a)) : ℕ) : ℝ) * (ah a : ℝ) :=
        mul_le_mul_of_nonneg_left (hah1 a) (Nat.cast_nonneg _)
      have hmul3 : ((min k (rk (F.quot a)) : ℕ) : ℝ) * ((ah a : ℝ) - (al a : ℝ)) ≤
          ((min k (rk (F.quot a)) : ℕ) : ℝ) * ε :=
        mul_le_mul_of_nonneg_left hdiff_a (Nat.cast_nonneg _)
      refine ⟨by linarith [ih'.1], by linarith [ih'.2.1], ?_⟩
      rw [← Nat.cast_min, ← hcast_min, add_mul]
      have hih_min := ih'.2.2
      rw [← Nat.cast_min] at hih_min
      linarith
  refine ⟨S_lo, S_hi, hcard_lo, hcard_hi,
    fun m hm => RHDirect.Stage2HodgeWeights.polygon_convex S_lo (hcard_lo.symm ▸ hm),
    fun m hm => RHDirect.Stage2HodgeWeights.polygon_convex S_hi (hcard_hi.symm ▸ hm),
    fun m hm => ?_⟩
  have hz := hzip_bounds (List.finRange F.len) m
  have hcast_lo : (RHDirect.Stage2HodgeWeights.polygon S_lo m : ℝ) =
      (((List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) ((al i : ℝ))).take m).sum := by
    unfold RHDirect.Stage2HodgeWeights.polygon
    rw [hsort_lo, Rat.cast_list_sum, List.map_take]
    dsimp only [l_lo]
    rw [List.map_flatMap]
    congr 2
    refine List.flatMap_congr fun i _ => by rw [List.map_replicate]
  have hcast_hi : (RHDirect.Stage2HodgeWeights.polygon S_hi m : ℝ) =
      (((List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) ((ah i : ℝ))).take m).sum := by
    unfold RHDirect.Stage2HodgeWeights.polygon
    rw [hsort_hi, Rat.cast_list_sum, List.map_take]
    dsimp only [l_hi]
    rw [List.map_flatMap]
    congr 2
    refine List.flatMap_congr fun i _ => by rw [List.map_replicate]
  have hneg_desc : (((List.finRange F.len).flatMap fun i =>
      List.replicate (rk (F.quot i)) (-F.hnSlope i)).take m).sum = -F.hnPolygon m := by
    unfold HNFiltration.hnPolygon HNFiltration.slopesDesc
    have hmap : ((List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) (-F.hnSlope i)) =
        ((List.finRange F.len).flatMap fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)).map Neg.neg := by
      rw [List.map_flatMap]
      refine List.flatMap_congr fun i _ => by rw [List.map_replicate]
    rw [hmap, ← List.map_take]
    have hsum_neg : ∀ (l : List ℝ), (l.map Neg.neg).sum = -l.sum := by
      intro l; induction l with | nil => simp | cons a l ih => simp [ih]; ring
    exact hsum_neg _
  have hmin_le : ((min m ((List.finRange F.len).flatMap fun i =>
      List.replicate (rk (F.quot i)) (0 : ℝ)).length : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast min_le_left _ _
  rw [hcast_lo, hcast_hi]
  rw [hneg_desc] at hz
  refine ⟨by linarith [hz.2.1], by linarith [hz.1], ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hmin_le hε.le
  have hz3 := hz.2.2
  rw [← Nat.cast_min] at hz3
  linarith

end HNPolygon

/-! ## Section 5: Bost's Morphism Slope Inequality, Minimal Slope & Truncation Vanishing -/

section BostMorphismAndMuMin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Set of slopes of nonzero orthogonal quotients `L / M` (`M ⊂ L` saturated). -/
def quotSlopes (L : Submodule ℤ E) : Set ℝ :=
  { t | ∃ M : Submodule ℤ E, IsSaturated L M ∧ M ≠ L ∧ ArakelovCovolume.slope (quotLat L M) = t }

/-- **Minimal Arakelov Slope** `μ_min(L) = inf_{M ⊂ L saturated} μ(L / M)`. -/
def muMin (L : Submodule ℤ E) : ℝ := sInf (quotSlopes L)

omit [FiniteDimensional ℝ F] in
/-- Helper: extending a `ℤ`-linear map `φ : L →ₗ[ℤ] M` with `‖φ x‖ ≤ C * ‖x‖` to an `ℝ`-linear
map `φ_ℝ : span_ℝ L →ₗ[ℝ] F` satisfying the same operator bound `‖φ_ℝ x‖ ≤ C * ‖x‖`. -/
private lemma exists_real_extension_of_lat_map
    {L : Submodule ℤ E} {M : Submodule ℤ F} [DiscreteTopology L]
    (φ : L →ₗ[ℤ] M) (C : ℝ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖) :
    ∃ φR : Submodule.span ℝ (L : Set E) →ₗ[ℝ] F,
      (∀ x : L, φR ⟨(x : E), Submodule.subset_span x.2⟩ = ((φ x : M) : F)) ∧
      (∀ x : Submodule.span ℝ (L : Set E), ‖φR x‖ ≤ C * ‖(x : E)‖) := by
  let b := Module.finBasis ℤ L
  have hli : LinearIndependent ℝ (fun i => (b i : E)) := linearIndependent_coe_basis L b
  have hspan : Submodule.span ℝ (Set.range fun i => (b i : E)) = Submodule.span ℝ (L : Set E) := by
    have hZ : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
      have : Set.range (fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp _ _
      rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (b i : E)), hZ]
  let bR : Basis (Fin (rk L)) ℝ (Submodule.span ℝ (L : Set E)) :=
    (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hbR : ∀ i, (bR i : E) = (b i : E) := fun i => congrArg Subtype.val (Basis.span_apply hli i)
  let φR : Submodule.span ℝ (L : Set E) →ₗ[ℝ] F := bR.constr ℝ (fun i => ((φ (b i) : M) : F))
  have hφR_basis : ∀ i, φR (bR i) = ((φ (b i) : M) : F) := fun i => bR.constr_basis ℝ _ i
  have hφR_lat : ∀ x : L, φR ⟨(x : E), Submodule.subset_span x.2⟩ = ((φ x : M) : F) := by
    intro x
    have hx_eq : (⟨(x : E), Submodule.subset_span x.2⟩ : Submodule.span ℝ (L : Set E)) =
        ∑ i, (b.repr x i : ℝ) • bR i := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val (b.sum_repr x)
      rw [Submodule.coe_sum] at h1
      change (x : E) = _
      rw [← h1, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Submodule.coe_smul, hbR i, Int.cast_smul_eq_zsmul]
    rw [hx_eq, map_sum]
    have h2 := congrArg (fun y : M => (y : F)) (congrArg φ (b.sum_repr x))
    rw [map_sum, Submodule.coe_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hφR_basis i, map_zsmul, Submodule.coe_smul, Int.cast_smul_eq_zsmul]
  have hint : ∀ n : Fin (rk L) → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := by
    intro n
    have h1 := hC (∑ i, n i • b i)
    simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h1
    simpa only [Int.cast_smul_eq_zsmul] using h1
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hint
  refine ⟨φR, hφR_lat, fun x => ?_⟩
  have hx : x = ∑ i, bR.repr x i • bR i := (bR.sum_repr x).symm
  have hxE : (x : E) = ∑ i, bR.repr x i • (b i : E) := by
    conv_lhs => rw [hx]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, hbR i]
  have hφx : φR x = ∑ i, bR.repr x i • ((φ (b i) : M) : F) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [map_smul, hφR_basis i]
  rw [hφx, hxE]
  exact hreal (fun i => bR.repr x i)

/-- **Filtered Bost Morphism Slope Inequality**:
for ANY `ℤ`-linear map `φ : L →ₗ[ℤ] M` between discrete Euclidean lattices with operator bound
`‖φ x‖ ≤ C * ‖x‖` (`C > 0`), and ANY Harder–Narasimhan filtration `F_HN : HNFiltration L`,
letting `N_j := saturation M (φ(F_HN.step j))` be the saturated image filtration in `M`:
1. `rk (N (Fin.last F_HN.len)) = ∑ i : Fin F_HN.len, rk (quotLat (N i.succ) (N i.castSucc))`,
2. `∑ i : Fin F_HN.len, (rk (quotLat (N i.succ) (N i.castSucc)) : ℝ) * F_HN.hnSlope i ≤
      degAr (N (Fin.last F_HN.len)) + (rk (N (Fin.last F_HN.len)) : ℝ) * Real.log C`! -/
theorem bost_filtered_slope_inequality
    {L : Submodule ℤ E} {M : Submodule ℤ F} [DiscreteTopology L] [DiscreteTopology M]
    (F_HN : HNFiltration L) (φ : L →ₗ[ℤ] M) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖) :
    let φImg : Submodule ℤ E → Submodule ℤ F :=
      fun A => (A.comap L.subtype).map (M.subtype.comp φ)
    let N : Fin (F_HN.len + 1) → Submodule ℤ F := fun j => saturation M (φImg (F_HN.step j))
    rk (N (Fin.last F_HN.len)) =
      ∑ i : Fin F_HN.len, rk (quotLat (N i.succ) (N i.castSucc)) ∧
    ∑ i : Fin F_HN.len, (rk (quotLat (N i.succ) (N i.castSucc)) : ℝ) * F_HN.hnSlope i ≤
      degAr (N (Fin.last F_HN.len)) + (rk (N (Fin.last F_HN.len)) : ℝ) * Real.log C := by
  intro φImg N
  obtain ⟨φR, hφR_lat, hφR_norm⟩ := exists_real_extension_of_lat_map φ C hC
  have hφImg_le : ∀ A, φImg A ≤ M := by
    intro A y hy
    rcases hy with ⟨x, _, rfl⟩
    exact (φ x).2
  have hN_sat : ∀ j, IsSaturated M (N j) := fun j => isSaturated_saturation (hφImg_le _)
  have hN_mono : ∀ i : Fin F_HN.len, N i.castSucc ≤ N i.succ := fun i =>
    saturation_mono (Submodule.map_mono (Submodule.comap_mono
      (F_HN.step_strictMono (Fin.castSucc_lt_succ (i := i))).le))
  -- Real span of `N j` equals `φR (span_ℝ (F_HN.step j))`
  have hspan_N : ∀ j : Fin (F_HN.len + 1),
      Submodule.span ℝ ((N j : Submodule ℤ F) : Set F) =
        ((Submodule.span ℝ ((F_HN.step j : Submodule ℤ E) : Set E)).comap
          (Submodule.span ℝ (L : Set E)).subtype).map φR := by
    intro j
    rw [span_real_saturation (hφImg_le _)]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro y ⟨x, hxStep, rfl⟩
      refine ⟨⟨(x : E), Submodule.subset_span x.2⟩, Submodule.subset_span hxStep, ?_⟩
      exact hφR_lat x
    · rintro y ⟨⟨v, hvL⟩, hvStep, rfl⟩
      have hmem : ∀ z ∈ Submodule.span ℝ ((F_HN.step j : Submodule ℤ E) : Set E),
          ∀ hzL : z ∈ Submodule.span ℝ (L : Set E),
            φR ⟨z, hzL⟩ ∈ Submodule.span ℝ ((φImg (F_HN.step j) : Submodule ℤ F) : Set F) := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem u hu =>
          intro hzL
          have huL : u ∈ L := (F_HN.step_saturated j).1 hu
          rw [show (⟨u, hzL⟩ : Submodule.span ℝ (L : Set E)) = ⟨u, Submodule.subset_span huL⟩ from rfl,
            hφR_lat ⟨u, huL⟩]
          exact Submodule.subset_span ⟨⟨u, huL⟩, hu, rfl⟩
        | zero =>
          intro hzL
          rw [show (⟨0, hzL⟩ : Submodule.span ℝ (L : Set E)) = 0 from rfl, map_zero]
          exact Submodule.zero_mem _
        | add u₁ u₂ hu₁ hu₂ ih₁ ih₂ =>
          intro hzL
          have h1L : u₁ ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_mono (show (F_HN.step j : Set E) ⊆ (L : Set E) from (F_HN.step_saturated j).1) hu₁
          have h2L : u₂ ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_mono (show (F_HN.step j : Set E) ⊆ (L : Set E) from (F_HN.step_saturated j).1) hu₂
          rw [show (⟨u₁ + u₂, hzL⟩ : Submodule.span ℝ (L : Set E)) = ⟨u₁, h1L⟩ + ⟨u₂, h2L⟩ from rfl,
            map_add]
          exact Submodule.add_mem _ (ih₁ h1L) (ih₂ h2L)
        | smul r u hu ih =>
          intro hzL
          have h1L : u ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_mono (show (F_HN.step j : Set E) ⊆ (L : Set E) from (F_HN.step_saturated j).1) hu
          rw [show (⟨r • u, hzL⟩ : Submodule.span ℝ (L : Set E)) = r • ⟨u, h1L⟩ from rfl,
            map_smul]
          exact Submodule.smul_mem _ r (ih h1L)
      exact hmem v hvStep hvL
  -- Key step inequality for each `i : Fin F_HN.len`
  have hstep : ∀ i : Fin F_HN.len,
      (rk (quotLat (N i.succ) (N i.castSucc)) : ℝ) * F_HN.hnSlope i ≤
        degAr (quotLat (N i.succ) (N i.castSucc)) +
          (rk (quotLat (N i.succ) (N i.castSucc)) : ℝ) * Real.log C := by
    intro i
    let A := F_HN.quot i
    let B := quotLat (N i.succ) (N i.castSucc)
    have : DiscreteTopology A := F_HN.quot_discrete i
    have : DiscreteTopology (N i.succ) := discreteTopology_of_le (hN_sat i.succ).1
    have hN_sat_i : IsSaturated (N i.succ) (N i.castSucc) :=
      isSaturated_of_le_of_isSaturated (hN_sat i.castSucc) (hN_mono i) (hN_sat i.succ).1
    have : DiscreteTopology B := discreteTopology_quotLat hN_sat_i
    -- Every element of `A` lies in `span_ℝ L`
    have hA_mem_VL : ∀ a ∈ A, a ∈ Submodule.span ℝ (L : Set E) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxL : x ∈ Submodule.span ℝ (L : Set E) := Submodule.subset_span ((F_HN.step_saturated i.succ).1 hx)
      have hsub : x - projOrth (F_HN.step i.castSucc) x ∈ Submodule.span ℝ (L : Set E) :=
        Submodule.span_mono (show (F_HN.step i.castSucc : Set E) ⊆ (L : Set E) from (F_HN.step_saturated _).1)
          (sub_projOrth_mem_span _ x)
      have := Submodule.sub_mem _ hxL hsub
      simpa using this
    -- Define `ψ : A →ₗ[ℤ] B` via `a ↦ projOrth (N i.castSucc) (φR ⟨a, ...⟩)`
    have hψ_mem : ∀ a (ha : a ∈ A), projOrth (N i.castSucc) (φR ⟨a, hA_mem_VL a ha⟩) ∈ B := by
      rintro _ ⟨x, hx, rfl⟩
      have hxL : x ∈ L := (F_HN.step_saturated i.succ).1 hx
      have hdiff_sp : x - projOrth (F_HN.step i.castSucc) x ∈
          Submodule.span ℝ ((F_HN.step i.castSucc : Submodule ℤ E) : Set E) :=
        sub_projOrth_mem_span _ x
      have hdiff_VL : x - projOrth (F_HN.step i.castSucc) x ∈ Submodule.span ℝ (L : Set E) :=
        Submodule.span_mono (show (F_HN.step i.castSucc : Set E) ⊆ (L : Set E) from (F_HN.step_saturated _).1)
          hdiff_sp
      have hφ_diff : φR ⟨x - projOrth (F_HN.step i.castSucc) x, hdiff_VL⟩ ∈
          Submodule.span ℝ ((N i.castSucc : Submodule ℤ F) : Set F) := by
        rw [hspan_N i.castSucc]
        exact ⟨⟨x - projOrth (F_HN.step i.castSucc) x, hdiff_VL⟩, hdiff_sp, rfl⟩
      have hproj_diff : projOrth (N i.castSucc) (φR ⟨x - projOrth (F_HN.step i.castSucc) x, hdiff_VL⟩) = 0 :=
        (projOrth_eq_zero_iff _ _).mpr hφ_diff
      have hsplit : (⟨x, Submodule.subset_span hxL⟩ : Submodule.span ℝ (L : Set E)) -
          ⟨projOrth (F_HN.step i.castSucc) x, hA_mem_VL _ ⟨x, hx, rfl⟩⟩ =
          ⟨x - projOrth (F_HN.step i.castSucc) x, hdiff_VL⟩ := Subtype.ext rfl
      have hproj_eq : projOrth (N i.castSucc) (φR ⟨projOrth (F_HN.step i.castSucc) x, hA_mem_VL _ ⟨x, hx, rfl⟩⟩) =
          projOrth (N i.castSucc) ((φ ⟨x, hxL⟩ : M) : F) := by
        have h1 := congrArg (fun v => projOrth (N i.castSucc) (φR v)) hsplit
        rw [map_sub, map_sub, hproj_diff, hφR_lat ⟨x, hxL⟩] at h1
        exact (sub_eq_zero.mp h1).symm
      change projOrth (N i.castSucc) (φR ⟨projOrth (F_HN.step i.castSucc) x, hA_mem_VL _ ⟨x, hx, rfl⟩⟩) ∈ B
      rw [hproj_eq]
      refine ⟨((φ ⟨x, hxL⟩ : M) : F), ?_, rfl⟩
      exact le_saturation (hφImg_le _) ⟨⟨x, hxL⟩, hx, rfl⟩
    let ψ : A →ₗ[ℤ] B :=
      { toFun := fun a => ⟨projOrth (N i.castSucc) (φR ⟨a.1, hA_mem_VL a.1 a.2⟩), hψ_mem a.1 a.2⟩
        map_add' := fun a b => Subtype.ext (by
          change projOrth (N i.castSucc) (φR (⟨a.1, hA_mem_VL a.1 a.2⟩ + ⟨b.1, hA_mem_VL b.1 b.2⟩)) = _
          rw [map_add, map_add]; rfl)
        map_smul' := fun c a => Subtype.ext (by
          change projOrth (N i.castSucc) (φR (c • ⟨a.1, hA_mem_VL a.1 a.2⟩)) = _
          rw [map_zsmul, map_zsmul]; rfl) }
    -- Kernel `K = (ker ψ).map A.subtype` is saturated in `A`
    let K : Submodule ℤ E := (LinearMap.ker ψ).map A.subtype
    have hK_sat : IsSaturated A K := by
      refine ⟨by rintro _ ⟨a, _, rfl⟩; exact a.2, fun x hxA hxsp => ?_⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      change ψ ⟨x, hxA⟩ = 0
      apply Subtype.ext
      change projOrth (N i.castSucc) (φR ⟨x, hA_mem_VL x hxA⟩) = 0
      have hvan : ∀ z ∈ Submodule.span ℝ (K : Set E), ∀ hzL : z ∈ Submodule.span ℝ (L : Set E),
          projOrth (N i.castSucc) (φR ⟨z, hzL⟩) = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem u hu =>
          intro hzL
          rcases hu with ⟨a, ha_ker, rfl⟩
          exact congrArg (fun y : B => (y : F)) (LinearMap.mem_ker.mp ha_ker)
        | zero =>
          intro hzL
          rw [show (⟨0, hzL⟩ : Submodule.span ℝ (L : Set E)) = 0 from rfl, map_zero, map_zero]
        | add u₁ u₂ hu₁ hu₂ ih₁ ih₂ =>
          intro hzL
          have h1L : u₁ ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_le.mpr (by rintro y ⟨a, _, rfl⟩; exact hA_mem_VL a.1 a.2) hu₁
          have h2L : u₂ ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_le.mpr (by rintro y ⟨a, _, rfl⟩; exact hA_mem_VL a.1 a.2) hu₂
          rw [show (⟨u₁ + u₂, hzL⟩ : Submodule.span ℝ (L : Set E)) = ⟨u₁, h1L⟩ + ⟨u₂, h2L⟩ from rfl,
            map_add, map_add, ih₁ h1L, ih₂ h2L, add_zero]
        | smul r u hu ih =>
          intro hzL
          have h1L : u ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_le.mpr (by rintro y ⟨a, _, rfl⟩; exact hA_mem_VL a.1 a.2) hu
          rw [show (⟨r • u, hzL⟩ : Submodule.span ℝ (L : Set E)) = r • ⟨u, h1L⟩ from rfl,
            map_smul, map_smul, ih h1L, smul_zero]
      exact hvan x hxsp (hA_mem_VL x hxA)
    -- Factor `ψ` through `A' := quotLat A K` to get an injective map `ψ' : A' →ₗ[ℤ] B` of norm `≤ C`
    -- whose image has full rank in `B`!
    let A' := quotLat A K
    have : DiscreteTopology K := discreteTopology_of_le hK_sat.1
    have : DiscreteTopology A' := discreteTopology_quotLat hK_sat
    have hA'_mem_VL : ∀ a' ∈ A', a' ∈ Submodule.span ℝ (L : Set E) := by
      rintro _ ⟨a, haA, rfl⟩
      have haL := hA_mem_VL a haA
      have hsub : a - projOrth K a ∈ Submodule.span ℝ (L : Set E) :=
        Submodule.span_le.mpr (fun y hy => hA_mem_VL y (hK_sat.1 hy)) (sub_projOrth_mem_span K a)
      have := Submodule.sub_mem _ haL hsub
      simpa using this
    have hvan_K : ∀ z ∈ Submodule.span ℝ (K : Set E), ∀ hzL : z ∈ Submodule.span ℝ (L : Set E),
        projOrth (N i.castSucc) (φR ⟨z, hzL⟩) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem u hu =>
        intro hzL
        rcases hu with ⟨a, ha_ker, rfl⟩
        exact congrArg (fun y : B => (y : F)) (LinearMap.mem_ker.mp ha_ker)
      | zero =>
        intro hzL
        rw [show (⟨0, hzL⟩ : Submodule.span ℝ (L : Set E)) = 0 from rfl, map_zero, map_zero]
      | add u₁ u₂ hu₁ hu₂ ih₁ ih₂ =>
        intro hzL
        have h1L : u₁ ∈ Submodule.span ℝ (L : Set E) :=
          Submodule.span_le.mpr (fun y hy => hA_mem_VL y (hK_sat.1 hy)) hu₁
        have h2L : u₂ ∈ Submodule.span ℝ (L : Set E) :=
          Submodule.span_le.mpr (fun y hy => hA_mem_VL y (hK_sat.1 hy)) hu₂
        rw [show (⟨u₁ + u₂, hzL⟩ : Submodule.span ℝ (L : Set E)) = ⟨u₁, h1L⟩ + ⟨u₂, h2L⟩ from rfl,
          map_add, map_add, ih₁ h1L, ih₂ h2L, add_zero]
      | smul r u hu ih =>
        intro hzL
        have h1L : u ∈ Submodule.span ℝ (L : Set E) :=
          Submodule.span_le.mpr (fun y hy => hA_mem_VL y (hK_sat.1 hy)) hu
        rw [show (⟨r • u, hzL⟩ : Submodule.span ℝ (L : Set E)) = r • ⟨u, h1L⟩ from rfl,
          map_smul, map_smul, ih h1L, smul_zero]
    have hψ'_eq : ∀ a (haA : a ∈ A),
        projOrth (N i.castSucc) (φR ⟨projOrth K a, hA'_mem_VL _ ⟨a, haA, rfl⟩⟩) =
        ((ψ ⟨a, haA⟩ : B) : F) := by
      intro a haA
      have hdiff_sp : a - projOrth K a ∈ Submodule.span ℝ (K : Set E) := sub_projOrth_mem_span K a
      have hdiff_VL : a - projOrth K a ∈ Submodule.span ℝ (L : Set E) :=
        Submodule.span_le.mpr (fun y hy => hA_mem_VL y (hK_sat.1 hy)) hdiff_sp
      have hsplit : (⟨a, hA_mem_VL a haA⟩ : Submodule.span ℝ (L : Set E)) -
          ⟨projOrth K a, hA'_mem_VL _ ⟨a, haA, rfl⟩⟩ = ⟨a - projOrth K a, hdiff_VL⟩ := Subtype.ext rfl
      have h1 := congrArg (fun v => projOrth (N i.castSucc) (φR v)) hsplit
      rw [map_sub, map_sub, hvan_K _ hdiff_sp hdiff_VL] at h1
      exact (sub_eq_zero.mp h1).symm
    have hψ'_mem : ∀ a' (ha' : a' ∈ A'), projOrth (N i.castSucc) (φR ⟨a', hA'_mem_VL a' ha'⟩) ∈ B := by
      rintro _ ⟨a, haA, rfl⟩
      change projOrth (N i.castSucc) (φR ⟨projOrth K a, hA'_mem_VL _ ⟨a, haA, rfl⟩⟩) ∈ B
      rw [hψ'_eq a haA]
      exact (ψ ⟨a, haA⟩).2
    let ψ' : A' →ₗ[ℤ] B :=
      { toFun := fun a' => ⟨projOrth (N i.castSucc) (φR ⟨a'.1, hA'_mem_VL a'.1 a'.2⟩), hψ'_mem a'.1 a'.2⟩
        map_add' := fun x y => Subtype.ext (by
          change projOrth (N i.castSucc) (φR (⟨x.1, hA'_mem_VL x.1 x.2⟩ + ⟨y.1, hA'_mem_VL y.1 y.2⟩)) = _
          rw [map_add, map_add]; rfl)
        map_smul' := fun c x => Subtype.ext (by
          change projOrth (N i.castSucc) (φR (c • ⟨x.1, hA'_mem_VL x.1 x.2⟩)) = _
          rw [map_zsmul, map_zsmul]; rfl) }
    have hψ'_inj : Function.Injective ψ' := by
      intro x y hxy
      apply Subtype.ext
      obtain ⟨a, haA, haeq⟩ := A'.sub_mem x.2 y.2
      have haeq' : projOrth K a = x.1 - y.1 := haeq
      have hψa : ψ ⟨a, haA⟩ = 0 := by
        apply Subtype.ext
        rw [← hψ'_eq a haA]
        change projOrth (N i.castSucc) (φR ⟨projOrth K a, _⟩) = 0
        have hsub : (⟨projOrth K a, hA'_mem_VL _ ⟨a, haA, rfl⟩⟩ : Submodule.span ℝ (L : Set E)) =
            ⟨x.1, hA'_mem_VL x.1 x.2⟩ - ⟨y.1, hA'_mem_VL y.1 y.2⟩ := Subtype.ext haeq'
        rw [hsub, map_sub, map_sub]
        exact sub_eq_zero.mpr (congrArg (fun z : B => (z : F)) hxy)
      have haK : a ∈ K := ⟨⟨a, haA⟩, LinearMap.mem_ker.mpr hψa, rfl⟩
      have h0 : x.1 - y.1 = 0 := by
        rw [← haeq']
        exact (projOrth_eq_zero_iff K a).mpr (Submodule.subset_span haK)
      exact sub_eq_zero.mp h0
    -- Image of `ψ'` inside `B` has the SAME rank as `B`
    let g : A' →ₗ[ℤ] F := B.subtype.comp ψ'
    have hginj : Function.Injective g := B.injective_subtype.comp hψ'_inj
    let Im := LinearMap.range g
    have hIm_le_B : Im ≤ B := by rintro _ ⟨x, rfl⟩; exact (ψ' x).2
    have : DiscreteTopology Im := discreteTopology_of_le hIm_le_B
    have hIm_span : Submodule.span ℝ (Im : Set F) = Submodule.span ℝ (B : Set F) := by
      apply le_antisymm (Submodule.span_mono (show (Im : Set F) ⊆ (B : Set F) from hIm_le_B))
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hwN, rfl⟩
      have hw_sp : w ∈ Submodule.span ℝ ((N i.succ : Submodule ℤ F) : Set F) :=
        Submodule.subset_span hwN
      rw [hspan_N i.succ] at hw_sp
      rcases hw_sp with ⟨⟨v, hvL⟩, hvStep, rfl⟩
      have hmem : ∀ z ∈ Submodule.span ℝ ((F_HN.step i.succ : Submodule ℤ E) : Set E),
          ∀ hzL : z ∈ Submodule.span ℝ (L : Set E),
            projOrth (N i.castSucc) (φR ⟨z, hzL⟩) ∈ Submodule.span ℝ (Im : Set F) := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem u hu =>
          intro hzL
          have huL : u ∈ L := (F_HN.step_saturated i.succ).1 hu
          have haA : projOrth (F_HN.step i.castSucc) u ∈ A := ⟨u, hu, rfl⟩
          have ha'A' : projOrth K (projOrth (F_HN.step i.castSucc) u) ∈ A' := ⟨_, haA, rfl⟩
          have hval : g ⟨projOrth K (projOrth (F_HN.step i.castSucc) u), ha'A'⟩ =
              projOrth (N i.castSucc) (φR ⟨u, hzL⟩) := by
            change ((ψ' ⟨projOrth K (projOrth (F_HN.step i.castSucc) u), ha'A'⟩ : B) : F) = _
            have h1 := hψ'_eq (projOrth (F_HN.step i.castSucc) u) haA
            have h2 : ((ψ ⟨projOrth (F_HN.step i.castSucc) u, haA⟩ : B) : F) =
                projOrth (N i.castSucc) (φR ⟨u, hzL⟩) := by
              have hdiff_sp : u - projOrth (F_HN.step i.castSucc) u ∈
                  Submodule.span ℝ ((F_HN.step i.castSucc : Submodule ℤ E) : Set E) :=
                sub_projOrth_mem_span _ u
              have hdiff_VL : u - projOrth (F_HN.step i.castSucc) u ∈ Submodule.span ℝ (L : Set E) :=
                Submodule.span_mono (show (F_HN.step i.castSucc : Set E) ⊆ (L : Set E) from
                  (F_HN.step_saturated _).1) hdiff_sp
              have hφ_diff : φR ⟨u - projOrth (F_HN.step i.castSucc) u, hdiff_VL⟩ ∈
                  Submodule.span ℝ ((N i.castSucc : Submodule ℤ F) : Set F) := by
                rw [hspan_N i.castSucc]; exact ⟨⟨_, hdiff_VL⟩, hdiff_sp, rfl⟩
              have hsplit : (⟨u, hzL⟩ : Submodule.span ℝ (L : Set E)) -
                  ⟨projOrth (F_HN.step i.castSucc) u, hA_mem_VL _ haA⟩ = ⟨_, hdiff_VL⟩ := Subtype.ext rfl
              have h3 := congrArg (fun v => projOrth (N i.castSucc) (φR v)) hsplit
              rw [map_sub, map_sub, (projOrth_eq_zero_iff _ _).mpr hφ_diff] at h3
              exact (sub_eq_zero.mp h3).symm
            exact h1.trans h2
          rw [← hval]
          exact Submodule.subset_span ⟨_, rfl⟩
        | zero =>
          intro hzL
          rw [show (⟨0, hzL⟩ : Submodule.span ℝ (L : Set E)) = 0 from rfl, map_zero, map_zero]
          exact Submodule.zero_mem _
        | add u₁ u₂ hu₁ hu₂ ih₁ ih₂ =>
          intro hzL
          have h1L : u₁ ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_mono (show (F_HN.step i.succ : Set E) ⊆ (L : Set E) from (F_HN.step_saturated _).1) hu₁
          have h2L : u₂ ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_mono (show (F_HN.step i.succ : Set E) ⊆ (L : Set E) from (F_HN.step_saturated _).1) hu₂
          rw [show (⟨u₁ + u₂, hzL⟩ : Submodule.span ℝ (L : Set E)) = ⟨u₁, h1L⟩ + ⟨u₂, h2L⟩ from rfl,
            map_add, map_add]
          exact Submodule.add_mem _ (ih₁ h1L) (ih₂ h2L)
        | smul r u hu ih =>
          intro hzL
          have h1L : u ∈ Submodule.span ℝ (L : Set E) :=
            Submodule.span_mono (show (F_HN.step i.succ : Set E) ⊆ (L : Set E) from (F_HN.step_saturated _).1) hu
          rw [show (⟨r • u, hzL⟩ : Submodule.span ℝ (L : Set E)) = r • ⟨u, h1L⟩ from rfl,
            map_smul, map_smul]
          exact Submodule.smul_mem _ r (ih h1L)
      exact hmem v hvStep hvL
    let eIm : A' ≃ₗ[ℤ] Im := LinearEquiv.ofInjective g hginj
    have hrk_Im_B : rk Im = rk B := by
      unfold rk
      rw [finrank_int_eq_finrank_real_span Im, finrank_int_eq_finrank_real_span B, hIm_span]
    have hrk_A'_B : rk A' = rk B := eIm.finrank_eq.trans hrk_Im_B
    -- Operator bound on `ψ'`: `‖ψ' x‖ ≤ C * ‖x‖`
    have hψ'_norm : ∀ x : A', ‖((ψ' x : B) : F)‖ ≤ C * ‖(x : E)‖ := by
      intro x
      exact (norm_projOrth_le _ _).trans (hφR_norm ⟨x.1, hA'_mem_VL x.1 x.2⟩)
    -- Hence `covol B ≤ covol Im ≤ C^(rk B) * covol A'`, so `degAr A' ≤ degAr B + rk B * log C`
    have hdeg_A'_B : degAr A' ≤ degAr B + (rk B : ℝ) * Real.log C := by
      let bA' := Module.finBasis ℤ A'
      have hint : ∀ n : Fin (rk A') → ℤ,
          ‖∑ k, (n k : ℝ) • ((ψ' (bA' k) : B) : F)‖ ≤ C * ‖∑ k, (n k : ℝ) • (bA' k : E)‖ := by
        intro n
        have h1 := hψ'_norm (∑ k, n k • bA' k)
        simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h1
        simpa only [Int.cast_smul_eq_zsmul] using h1
      have hreal := norm_sum_smul_le_of_int (fun k => (bA' k : E))
        (fun k => ((ψ' (bA' k) : B) : F)) C hint
      have hdet := gram_det_le (fun k => (bA' k : E)) (fun k => ((ψ' (bA' k) : B) : F)) C hreal
      have hcov_Im : covol Im ≤ C ^ rk A' * covol A' := by
        rw [covol_eq_sqrt_det_gram Im (bA'.map eIm), covol_eq_sqrt_det_gram A' bA']
        calc Real.sqrt (Matrix.gram ℝ (fun k => ((ψ' (bA' k) : B) : F))).det
            ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin (rk A'))) *
                (Matrix.gram ℝ (fun k => (bA' k : E))).det) := Real.sqrt_le_sqrt hdet
          _ = C ^ rk A' * Real.sqrt (Matrix.gram ℝ (fun k => (bA' k : E))).det := by
              rw [Fintype.card_fin, show C ^ (2 * rk A') = (C ^ rk A') ^ 2 by ring,
                Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have hcov_B : covol B ≤ C ^ rk A' * covol A' :=
        (covol_le_of_le_same_rank hIm_le_B hrk_Im_B).1.trans hcov_Im
      have hlog := Real.log_le_log (covol_pos B) hcov_B
      rw [Real.log_mul (pow_pos hCpos _).ne' (covol_pos A').ne', Real.log_pow, hrk_A'_B] at hlog
      unfold degAr
      linarith
    -- Semistability of `A = F_HN.quot i`: `rk A' * F_HN.hnSlope i ≤ degAr A'`
    have hdeg_A' : (rk A' : ℝ) * F_HN.hnSlope i ≤ degAr A' := by
      have hrkA := rk_add_quotLat hK_sat
      have hdegA := degAr_eq_add_quotLat hK_sat
      have hrA : (0 : ℝ) < (rk A : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot A (F_HN.quot_ne_bot i))
      have hdegA_eq : degAr A = (rk A : ℝ) * F_HN.hnSlope i := by
        unfold HNFiltration.hnSlope ArakelovCovolume.slope
        exact (mul_div_cancel₀ _ hrA.ne').symm
      have hdegK_le : degAr K ≤ (rk K : ℝ) * F_HN.hnSlope i := by
        by_cases hK0 : K = ⊥
        · rw [hK0, degAr_bot, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]]; simp
        · have hss := F_HN.quot_semistable i K hK_sat.1 hK0
          have hrK : (0 : ℝ) < (rk K : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot K hK0)
          have h1 : degAr K / (rk K : ℝ) ≤ F_HN.hnSlope i := hss
          rw [div_le_iff₀ hrK] at h1
          linarith
      have hrA_cast : (rk A : ℝ) = (rk K : ℝ) + (rk A' : ℝ) := by exact_mod_cast hrkA
      rw [hrA_cast, add_mul] at hdegA_eq
      linarith
    rw [← hrk_A'_B] at hdeg_A'_B
    change (rk B : ℝ) * F_HN.hnSlope i ≤ degAr B + (rk B : ℝ) * Real.log C
    rw [← hrk_A'_B]
    linarith
  -- Telescoping `rk` and `degAr` of `N`
  have htel : ∀ m : ℕ, (hm : m ≤ F_HN.len) →
      rk (N ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F_HN.len => i.1 < m),
          rk (quotLat (N i.succ) (N i.castSucc)) ∧
      degAr (N ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F_HN.len => i.1 < m),
          degAr (quotLat (N i.succ) (N i.castSucc)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hN0 : N ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ = ⊥ := by
        have hstep0 : F_HN.step ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ = ⊥ := F_HN.step_zero
        have him0 : φImg (F_HN.step ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩) = ⊥ := by
          rw [hstep0]; ext y; simp [φImg]
        change saturation M (φImg (F_HN.step ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩)) = ⊥
        rw [him0]
        exact saturation_eq_self (isSaturated_bot M)
      rw [hN0, degAr_bot]
      simp [rk]
    | succ m ih =>
      intro hm
      let i_m : Fin F_HN.len := ⟨m, hm⟩
      have : DiscreteTopology (N i_m.succ) := discreteTopology_of_le (hN_sat i_m.succ).1
      have hsat : IsSaturated (N i_m.succ) (N i_m.castSucc) :=
        isSaturated_of_le_of_isSaturated (hN_sat i_m.castSucc) (hN_mono i_m) (hN_sat i_m.succ).1
      have hfilt : Finset.univ.filter (fun i : Fin F_HN.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F_HN.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]
        omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F_HN.len => i.1 < m) := by simp [i_m]
      have hprev := ih (Nat.le_of_succ_le hm)
      have hadd_rk := rk_add_quotLat hsat
      have hadd_deg := degAr_eq_add_quotLat hsat
      change rk (N i_m.castSucc) = _ ∧ degAr (N i_m.castSucc) = _ at hprev
      refine ⟨?_, ?_⟩
      · rw [hfilt, Finset.sum_insert hnotmem]
        change rk (N i_m.succ) = rk (quotLat (N i_m.succ) (N i_m.castSucc)) + _
        omega
      · rw [hfilt, Finset.sum_insert hnotmem]
        change degAr (N i_m.succ) = degAr (quotLat (N i_m.succ) (N i_m.castSucc)) + _
        linarith
  have htot := htel F_HN.len le_rfl
  have hf : Finset.univ.filter (fun i : Fin F_HN.len => i.1 < F_HN.len) = Finset.univ := by
    ext i; simp
  rw [hf] at htot
  refine ⟨htot.1, ?_⟩
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hstep i
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← htot.2] at hsum
  have hrk_cast : ∑ i : Fin F_HN.len, (rk (quotLat (N i.succ) (N i.castSucc)) : ℝ) =
      (rk (N (Fin.last F_HN.len)) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast htot.1.symm
  rwa [hrk_cast] at hsum

/-- **Characterization of `muMin L` as the Last Harder–Narasimhan Slope**:
for any nonzero discrete lattice `L ⊂ E` and any `F : HNFiltration L`:
1. `muMin L = F.hnSlope ⟨F.len - 1, _⟩`,
2. `F.hnPolygon (rk L) - F.hnPolygon (rk L - 1) = muMin L`! -/
theorem HNFiltration.muMin_eq_last_hnSlope {L : Submodule ℤ E} [DiscreteTopology L]
    (hL0 : L ≠ ⊥) (F : HNFiltration L) :
    let hpos := F.len_pos_of_ne_bot hL0
    muMin L = F.hnSlope ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩ := by
  intro hpos
  let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  have hlast_succ : ilast.succ = Fin.last F.len := by ext; simp [ilast]; omega
  have hquot_last : F.quot ilast = quotLat L (F.step ilast.castSucc) := by
    unfold HNFiltration.quot
    rw [hlast_succ, F.step_last]
  have hne_last : F.step ilast.castSucc ≠ L := fun heq =>
    (F.step_strictMono (Fin.castSucc_lt_succ (i := ilast))).ne
      (heq.trans (F.step_last.symm.trans (congrArg F.step hlast_succ.symm)))
  have hmem : F.hnSlope ilast ∈ quotSlopes L :=
    ⟨F.step ilast.castSucc, F.step_saturated _, hne_last, by rw [← hquot_last]; rfl⟩
  have hlb : ∀ t ∈ quotSlopes L, F.hnSlope ilast ≤ t := by
    rintro _ ⟨M, hMsat, hMne, rfl⟩
    let Q := quotLat L M
    have : DiscreteTopology Q := discreteTopology_quotLat hMsat
    have hQ0 : Q ≠ ⊥ := quotLat_ne_bot_of_lt hMsat hMne
    let φ : L →ₗ[ℤ] Q :=
      { toFun := fun x => ⟨projOrth M x.1, ⟨x.1, x.2, rfl⟩⟩
        map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
        map_smul' := fun c a => Subtype.ext (map_zsmul _ c a.1) }
    have hφ_lip : ∀ x : L, ‖((φ x : Q) : E)‖ ≤ 1 * ‖(x : E)‖ := fun x => by
      rw [one_mul]; exact norm_projOrth_le M x.1
    have hBost := bost_filtered_slope_inequality F φ 1 zero_lt_one hφ_lip
    dsimp only at hBost
    rw [Real.log_one, mul_zero, add_zero] at hBost
    -- Here `N (Fin.last F.len) = Q` because `φ` is surjective onto `Q`!
    have hN_last : saturation Q ((F.step (Fin.last F.len)).comap L.subtype |>.map (Q.subtype.comp φ)) = Q := by
      have him : ((F.step (Fin.last F.len)).comap L.subtype).map (Q.subtype.comp φ) = Q := by
        rw [F.step_last]
        ext y
        simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.comp_apply]
        constructor
        · rintro ⟨x, _, rfl⟩; exact (φ x).2
        · rintro ⟨x, hxL, rfl⟩; exact ⟨⟨x, hxL⟩, hxL, rfl⟩
      rw [him]
      exact saturation_eq_self (isSaturated_self Q)
    have hge_all : ∀ i : Fin F.len, F.hnSlope ilast ≤ F.hnSlope i := fun i => by
      rcases eq_or_lt_of_le (show i ≤ ilast from by
        show i.1 ≤ F.len - 1; have := i.2; omega) with rfl | hlt
      · exact le_rfl
      · exact (F.slope_strictAnti i ilast hlt).le
    have hlow : (rk Q : ℝ) * F.hnSlope ilast ≤ degAr Q := by
      have hrkQ : (rk Q : ℝ) = ∑ i : Fin F.len,
          (rk (quotLat (saturation Q (((F.step i.succ).comap L.subtype).map (Q.subtype.comp φ)))
            (saturation Q (((F.step i.castSucc).comap L.subtype).map (Q.subtype.comp φ)))) : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast (congrArg rk hN_last).symm.trans hBost.1
      rw [hrkQ, Finset.sum_mul]
      calc ∑ i : Fin F.len, (rk _ : ℝ) * F.hnSlope ilast
          ≤ ∑ i : Fin F.len, (rk _ : ℝ) * F.hnSlope i :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hge_all i) (Nat.cast_nonneg _)
        _ ≤ degAr Q := hBost.2.trans_eq (congrArg degAr hN_last)
    have hrQ : (0 : ℝ) < (rk Q : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot Q hQ0)
    unfold ArakelovCovolume.slope
    rw [le_div_iff₀ hrQ]
    linarith
  apply le_antisymm
  · exact csInf_le ⟨F.hnSlope ilast, hlb⟩ hmem
  · exact le_csInf ⟨F.hnSlope ilast, hmem⟩ hlb

/-- **Lower Bound on Every Saturated Quotient Slope**:
for every saturated proper sublattice `M ⊂ L`, `muMin L ≤ slope (quotLat L M)`. -/
theorem muMin_le_slope_quotLat {L M : Submodule ℤ E} [DiscreteTopology L]
    (hM : IsSaturated L M) (hMne : M ≠ L) :
    muMin L ≤ ArakelovCovolume.slope (quotLat L M) := by
  have hL0 : L ≠ ⊥ := fun h0 => hMne (le_antisymm hM.1 (h0 ▸ bot_le))
  let F := canonicalHN L
  have hpos := F.len_pos_of_ne_bot hL0
  let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  rw [F.muMin_eq_last_hnSlope hL0]
  let Q := quotLat L M
  have : DiscreteTopology Q := discreteTopology_quotLat hM
  have hQ0 : Q ≠ ⊥ := quotLat_ne_bot_of_lt hM hMne
  let φ : L →ₗ[ℤ] Q :=
    { toFun := fun x => ⟨projOrth M x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul _ c a.1) }
  have hφ_lip : ∀ x : L, ‖((φ x : Q) : E)‖ ≤ 1 * ‖(x : E)‖ := fun x => by
    rw [one_mul]; exact norm_projOrth_le M x.1
  have hBost := bost_filtered_slope_inequality F φ 1 zero_lt_one hφ_lip
  dsimp only at hBost
  rw [Real.log_one, mul_zero, add_zero] at hBost
  have hN_last : saturation Q ((F.step (Fin.last F.len)).comap L.subtype |>.map (Q.subtype.comp φ)) = Q := by
    have him : ((F.step (Fin.last F.len)).comap L.subtype).map (Q.subtype.comp φ) = Q := by
      rw [F.step_last]
      ext y
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.comp_apply]
      constructor
      · rintro ⟨x, _, rfl⟩; exact (φ x).2
      · rintro ⟨x, hxL, rfl⟩; exact ⟨⟨x, hxL⟩, hxL, rfl⟩
    rw [him]
    exact saturation_eq_self (isSaturated_self Q)
  have hge_all : ∀ i : Fin F.len, F.hnSlope ilast ≤ F.hnSlope i := fun i => by
    rcases eq_or_lt_of_le (show i ≤ ilast from by
      show i.1 ≤ F.len - 1; have := i.2; omega) with rfl | hlt
    · exact le_rfl
    · exact (F.slope_strictAnti i ilast hlt).le
  have hlow : (rk Q : ℝ) * F.hnSlope ilast ≤ degAr Q := by
    have hrkQ : (rk Q : ℝ) = ∑ i : Fin F.len,
        (rk (quotLat (saturation Q (((F.step i.succ).comap L.subtype).map (Q.subtype.comp φ)))
          (saturation Q (((F.step i.castSucc).comap L.subtype).map (Q.subtype.comp φ)))) : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast (congrArg rk hN_last).symm.trans hBost.1
    rw [hrkQ, Finset.sum_mul]
    calc ∑ i : Fin F.len, (rk _ : ℝ) * F.hnSlope ilast
        ≤ ∑ i : Fin F.len, (rk _ : ℝ) * F.hnSlope i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hge_all i) (Nat.cast_nonneg _)
      _ ≤ degAr Q := hBost.2.trans_eq (congrArg degAr hN_last)
  have hrQ : (0 : ℝ) < (rk Q : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot Q hQ0)
  unfold ArakelovCovolume.slope
  rw [le_div_iff₀ hrQ]
  linarith

/-- The last slope of the Harder–Narasimhan polygon equals `muMin L`! -/
theorem HNFiltration.hnPolygon_last_slope_eq_muMin {L : Submodule ℤ E} [DiscreteTopology L]
    (hL0 : L ≠ ⊥) (F : HNFiltration L) :
    F.hnPolygon (rk L) - F.hnPolygon (rk L - 1) = muMin L := by
  have hpos := F.len_pos_of_ne_bot hL0
  have hrL : 0 < rk L := rk_pos_of_ne_bot L hL0
  let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  rw [F.muMin_eq_last_hnSlope hL0]
  set ls := F.slopesDesc
  have hlen : ls.length = rk L := F.slopesDesc_length
  have htake : (ls.take (rk L)).sum = (ls.take (rk L - 1)).sum + ls[rk L - 1]'(by omega) := by
    have h1 : rk L = (rk L - 1) + 1 := (Nat.sub_add_cancel hrL).symm
    conv_lhs => rw [h1, List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.sum_append, List.sum_singleton]
  have hlast_elem : ls[rk L - 1]'(by omega) = F.hnSlope ilast := by
    -- `ls` ends with `List.replicate (rk (F.quot ilast)) (F.hnSlope ilast)` which is nonempty!
    have hsplit : List.finRange F.len = (List.finRange F.len).take (F.len - 1) ++ [ilast] := by
      apply List.ext_getElem
      · rw [List.length_append, List.length_take, List.length_finRange, List.length_singleton]; omega
      · intro k h1 h2
        rw [List.getElem_finRange]
        by_cases hk : k < F.len - 1
        · have hk' : k < ((List.finRange F.len).take (F.len - 1)).length := by
            rw [List.length_take, List.length_finRange]; omega
          rw [List.getElem_append_left hk', List.getElem_take, List.getElem_finRange]
        · have hk_eq : k = F.len - 1 := by rw [List.length_finRange] at h1; omega
          have hge : ((List.finRange F.len).take (F.len - 1)).length ≤ k := by
            rw [List.length_take, List.length_finRange]; omega
          rw [List.getElem_append_right hge]
          have h0 : k - ((List.finRange F.len).take (F.len - 1)).length = 0 := by
            rw [List.length_take, List.length_finRange]; omega
          simp only [h0, List.getElem_singleton]
          ext; exact hk_eq
    have hls_eq : ls = (((List.finRange F.len).take (F.len - 1)).flatMap
        fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)) ++
        List.replicate (rk (F.quot ilast)) (F.hnSlope ilast) := by
      dsimp only [ls, slopesDesc]
      conv_lhs => rw [hsplit, List.flatMap_append, List.flatMap_singleton]
    have : DiscreteTopology (F.quot ilast) := F.quot_discrete ilast
    have hrq : 0 < rk (F.quot ilast) := rk_pos_of_ne_bot _ (F.quot_ne_bot ilast)
    have hmem_last : ls[rk L - 1]'(by omega) ∈ List.replicate (rk (F.quot ilast)) (F.hnSlope ilast) := by
      set pref := ((List.finRange F.len).take (F.len - 1)).flatMap
        fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)
      have htot_len : pref.length + rk (F.quot ilast) = rk L := by
        have := congrArg List.length hls_eq
        rw [List.length_append, List.length_replicate, hlen] at this
        exact this.symm
      have hge : pref.length ≤ rk L - 1 := by omega
      have hget : ls[rk L - 1]'(by omega) =
          (List.replicate (rk (F.quot ilast)) (F.hnSlope ilast))[rk L - 1 - pref.length]'(by
            rw [List.length_replicate]; omega) := by
        have hidx : rk L - 1 = pref.length + (rk L - 1 - pref.length) := by omega
        have hget1 : (pref ++ List.replicate (rk (F.quot ilast)) (F.hnSlope ilast))[rk L - 1]'(by
            rw [← hls_eq, hlen]; omega) =
            (List.replicate (rk (F.quot ilast)) (F.hnSlope ilast))[rk L - 1 - pref.length]'(by
              rw [List.length_replicate]; omega) :=
          List.getElem_append_right hge
        simpa only [← hls_eq] using hget1
      rw [hget]
      exact List.getElem_mem _
    exact (List.mem_replicate.mp hmem_last).2
  unfold hnPolygon
  change (ls.take (rk L)).sum - (ls.take (rk L - 1)).sum = F.hnSlope ilast
  rw [htake, hlast_elem]
  ring

theorem muMin_le_slope_le_muMax (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    muMin L ≤ ArakelovCovolume.slope L ∧ ArakelovCovolume.slope L ≤ muMax L := by
  refine ⟨?_, slope_le_muMax L L le_rfl hL0⟩
  let F := canonicalHN L
  have hpos := F.len_pos_of_ne_bot hL0
  rw [F.muMin_eq_last_hnSlope hL0]
  have hrL : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot L hL0)
  have hge_all : ∀ i : Fin F.len,
      F.hnSlope ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩ ≤ F.hnSlope i := fun i => by
    rcases eq_or_lt_of_le (show i ≤ ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩ from by
      show i.1 ≤ F.len - 1; have := i.2; omega) with rfl | hlt
    · exact le_rfl
    · exact (F.slope_strictAnti i _ hlt).le
  unfold ArakelovCovolume.slope
  rw [le_div_iff₀ hrL, F.degAr_eq_sum]
  have hrk_cast : (rk L : ℝ) = ∑ i : Fin F.len, (rk (F.quot i) : ℝ) := by
    rw [F.rk_eq_sum, Nat.cast_sum]
  rw [hrk_cast, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (hge_all i) (Nat.cast_nonneg _)

/-- **Bost's Fundamental Morphism Slope Inequality**:
for ANY nonzero `ℤ`-linear map `φ : L →ₗ[ℤ] M` between discrete Euclidean lattices (`φ ≠ 0`)
with operator bound `‖φ x‖ ≤ C * ‖x‖` (`C > 0`):
`muMin L ≤ muMax M + Real.log C`! -/
theorem bost_muMin_le_muMax_add_log
    {L : Submodule ℤ E} {M : Submodule ℤ F} [DiscreteTopology L] [DiscreteTopology M]
    (φ : L →ₗ[ℤ] M) (hφ : φ ≠ 0) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖) :
    muMin L ≤ muMax M + Real.log C := by
  have hL0 : L ≠ ⊥ := by
    intro h0
    apply hφ
    ext x
    have hx0 : x = 0 := Subtype.ext ((Submodule.mem_bot ℤ).mp (h0 ▸ x.2))
    rw [hx0, map_zero, LinearMap.zero_apply]
  let F_HN := canonicalHN L
  have hpos := F_HN.len_pos_of_ne_bot hL0
  let ilast : Fin F_HN.len := ⟨F_HN.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  rw [F_HN.muMin_eq_last_hnSlope hL0]
  have hBost := bost_filtered_slope_inequality F_HN φ C hCpos hC
  dsimp only at hBost
  let φImg : Submodule ℤ E → Submodule ℤ F :=
    fun A => (A.comap L.subtype).map (M.subtype.comp φ)
  let Ntot := saturation M (φImg L)
  have hNtot_eq : saturation M (φImg (F_HN.step (Fin.last F_HN.len))) = Ntot := by
    rw [F_HN.step_last]
  have hNtot_le : Ntot ≤ M := saturation_le M _
  have : DiscreteTopology Ntot := discreteTopology_of_le hNtot_le
  have hNtot_ne : Ntot ≠ ⊥ := by
    intro h0
    apply hφ
    ext x
    have hmem : ((φ x : M) : F) ∈ Ntot :=
      le_saturation (by rintro _ ⟨y, _, rfl⟩; exact (φ y).2) ⟨x, x.2, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have hrN : (0 : ℝ) < (rk Ntot : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot Ntot hNtot_ne)
  have hge_all : ∀ i : Fin F_HN.len, F_HN.hnSlope ilast ≤ F_HN.hnSlope i := fun i => by
    rcases eq_or_lt_of_le (show i ≤ ilast from by
      show i.1 ≤ F_HN.len - 1; have := i.2; omega) with rfl | hlt
    · exact le_rfl
    · exact (F_HN.slope_strictAnti i ilast hlt).le
  have hlow : (rk Ntot : ℝ) * F_HN.hnSlope ilast ≤ degAr Ntot + (rk Ntot : ℝ) * Real.log C := by
    have hB1 : rk Ntot = ∑ i : Fin F_HN.len,
        rk (quotLat (saturation M (φImg (F_HN.step i.succ)))
          (saturation M (φImg (F_HN.step i.castSucc)))) := by
      rw [← hNtot_eq]; exact hBost.1
    have hB2 : ∑ i : Fin F_HN.len,
        (rk (quotLat (saturation M (φImg (F_HN.step i.succ)))
          (saturation M (φImg (F_HN.step i.castSucc)))) : ℝ) * F_HN.hnSlope i ≤
        degAr Ntot + (rk Ntot : ℝ) * Real.log C := by
      rw [← hNtot_eq]; exact hBost.2
    have hrk_cast : (rk Ntot : ℝ) = ∑ i : Fin F_HN.len,
        (rk (quotLat (saturation M (φImg (F_HN.step i.succ)))
          (saturation M (φImg (F_HN.step i.castSucc)))) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hB1
    calc (rk Ntot : ℝ) * F_HN.hnSlope ilast
        = ∑ i : Fin F_HN.len, (rk (quotLat (saturation M (φImg (F_HN.step i.succ)))
            (saturation M (φImg (F_HN.step i.castSucc)))) : ℝ) * F_HN.hnSlope ilast := by
          rw [hrk_cast, Finset.sum_mul]
      _ ≤ ∑ i : Fin F_HN.len, (rk (quotLat (saturation M (φImg (F_HN.step i.succ)))
            (saturation M (φImg (F_HN.step i.castSucc)))) : ℝ) * F_HN.hnSlope i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hge_all i) (Nat.cast_nonneg _)
      _ ≤ degAr Ntot + (rk Ntot : ℝ) * Real.log C := hB2
  have hslope_le : ArakelovCovolume.slope Ntot ≤ muMax M := slope_le_muMax M Ntot hNtot_le hNtot_ne
  have hdeg_le : degAr Ntot ≤ (rk Ntot : ℝ) * muMax M := by
    have h1 : degAr Ntot / (rk Ntot : ℝ) ≤ muMax M := hslope_le
    rw [div_le_iff₀ hrN] at h1
    linarith
  have hmul_le : (rk Ntot : ℝ) * F_HN.hnSlope ilast ≤ (rk Ntot : ℝ) * (muMax M + Real.log C) := by
    linarith
  exact le_of_mul_le_mul_left hmul_le hrN

/-- **Bost's Morphism Slope Inequality for Ambient Linear Maps `φ : E →ₗ[ℝ] F`**:
if `φ : E →ₗ[ℝ] F` maps `L` into `M` (`∃ x ∈ L, φ x ≠ 0`) with `∀ x ∈ L, ‖φ x‖ ≤ C * ‖x‖` (`C > 0`),
then `muMin L ≤ muMax M + Real.log C`! -/
theorem bost_linearMap_muMin_le_muMax_add_log
    {L : Submodule ℤ E} {M : Submodule ℤ F} [DiscreteTopology L] [DiscreteTopology M]
    (φ : E →ₗ[ℝ] F) (hmap : ∀ x ∈ L, φ x ∈ M) (hne : ∃ x ∈ L, φ x ≠ 0)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ x ∈ L, ‖φ x‖ ≤ C * ‖x‖) :
    muMin L ≤ muMax M + Real.log C := by
  let φZ : L →ₗ[ℤ] M :=
    { toFun := fun x => ⟨φ x.1, hmap x.1 x.2⟩
      map_add' := fun a b => Subtype.ext (map_add φ a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul φ c a.1) }
  have hφZ : φZ ≠ 0 := by
    intro h0
    rcases hne with ⟨x, hxL, hφx⟩
    apply hφx
    exact congrArg (fun y : M => (y : F)) (LinearMap.congr_fun h0 ⟨x, hxL⟩)
  exact bost_muMin_le_muMax_add_log φZ hφZ C hCpos (fun x => hC x.1 x.2)

/-- **Harder–Narasimhan Truncation Sublattice `F.trunc θ`**:
the largest filtration step `F.step j` whose preceding HN slopes are all `≥ θ`! -/
def HNFiltration.truncIdx {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (θ : ℝ) : Fin (F.len + 1) :=
  ⟨(Finset.univ.filter fun i : Fin F.len => θ ≤ F.hnSlope i).card,
    Nat.lt_succ_of_le (by
      calc (Finset.univ.filter fun i : Fin F.len => θ ≤ F.hnSlope i).card
          ≤ (Finset.univ : Finset (Fin F.len)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = F.len := by simp)⟩

/-- The `≥ θ` Harder–Narasimhan truncation sublattice `L_{≥ θ} = F.step (F.truncIdx θ)`. -/
def HNFiltration.trunc {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (θ : ℝ) : Submodule ℤ E :=
  F.step (F.truncIdx θ)

lemma HNFiltration.mem_filter_trunc_iff {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (θ : ℝ) (i : Fin F.len) :
    θ ≤ F.hnSlope i ↔ i.1 < (F.truncIdx θ).1 := by
  classical
  let S := Finset.univ.filter fun j : Fin F.len => θ ≤ F.hnSlope j
  -- Because `F.hnSlope` is strictly decreasing, `S` is a downward-closed initial segment of `Fin F.len`!
  have hdown : ∀ a b : Fin F.len, a ≤ b → b ∈ S → a ∈ S := by
    intro a b hab hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ a, hb.2.trans ?_⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (F.slope_strictAnti a b hlt).le
  have hiff : θ ≤ F.hnSlope i ↔ i ∈ S := by simp [S]
  have hval : (F.truncIdx θ).1 = S.card := rfl
  rw [hiff, hval]
  constructor
  · intro hi
    have hsub : Finset.univ.filter (fun j : Fin F.len => j.1 ≤ i.1) ⊆ S := fun j hj =>
      hdown j i (Finset.mem_filter.mp hj).2 hi
    have hcard : (Finset.univ.filter (fun j : Fin F.len => j.1 ≤ i.1)).card = i.1 + 1 := by
      have hbij : (Finset.univ.filter (fun j : Fin F.len => j.1 ≤ i.1)).card =
          (Finset.range (i.1 + 1)).card := by
        refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
        · intro j hj; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
        · intro a _ b _ h; exact Fin.ext h
        · intro k hk
          have hk' := Finset.mem_range.mp hk
          exact ⟨⟨k, lt_of_le_of_lt (Nat.le_of_lt_succ hk') i.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ hk'⟩, rfl⟩
      rw [hbij, Finset.card_range]
    have hle := Finset.card_le_card hsub
    omega
  · intro hlt
    by_contra hnot
    have hsub : S ⊆ Finset.univ.filter (fun j : Fin F.len => j.1 < i.1) := by
      intro j hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
      by_contra hge
      exact hnot (hdown i j (not_lt.mp hge) hj)
    have hcard : (Finset.univ.filter (fun j : Fin F.len => j.1 < i.1)).card = i.1 := by
      have hbij : (Finset.univ.filter (fun j : Fin F.len => j.1 < i.1)).card =
          (Finset.range i.1).card := by
        refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
        · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        · intro a _ b _ h; exact Fin.ext h
        · intro k hk
          have hk' := Finset.mem_range.mp hk
          exact ⟨⟨k, lt_trans hk' i.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, rfl⟩
      rw [hbij, Finset.card_range]
    have hle := Finset.card_le_card hsub
    omega

lemma HNFiltration.trunc_isSaturated {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (θ : ℝ) : IsSaturated L (F.trunc θ) :=
  F.step_saturated _

/-- The quotient `L / F.trunc θ` above cutoff `θ` has maximal slope strictly below `θ`! -/
theorem HNFiltration.muMax_quotLat_trunc_lt {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (θ : ℝ) (hne : F.trunc θ ≠ L) :
    muMax (quotLat L (F.trunc θ)) < θ := by
  let M := F.trunc θ
  let j₀ := F.truncIdx θ
  have hMsat : IsSaturated L M := F.trunc_isSaturated θ
  have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hMsat
  have hj₀_lt : j₀.1 < F.len := by
    by_contra hge
    have hlast : F.truncIdx θ = Fin.last F.len := by ext; simp; change j₀.1 = F.len; omega
    exact hne (by unfold trunc; rw [hlast, F.step_last])
  -- Construct an HN filtration on `quotLat L M` from steps `j₀, ..., F.len`!
  let m := F.len - j₀.1
  have hm_pos : 0 < m := by omega
  have hge : ∀ k : Fin (m + 1), M ≤ F.step ⟨j₀.1 + k.1, by omega⟩ := fun k =>
    F.step_strictMono.monotone (show j₀ ≤ ⟨j₀.1 + k.1, by omega⟩ from by
      change j₀.1 ≤ j₀.1 + k.1; omega)
  let FQ : HNFiltration (quotLat L M) := {
    len := m
    step := fun k => quotLat (F.step ⟨j₀.1 + k.1, by omega⟩) M
    step_zero := by
      have h0 : (⟨j₀.1 + 0, by omega⟩ : Fin (F.len + 1)) = j₀ := Fin.ext (by simp)
      change quotLat (F.step ⟨j₀.1 + 0, by omega⟩) M = ⊥
      rw [h0]; exact quotLat_self M
    step_last := by
      have hl : (⟨j₀.1 + (Fin.last m).1, by omega⟩ : Fin (F.len + 1)) = Fin.last F.len := by
        ext; simp [m]; omega
      change quotLat (F.step ⟨j₀.1 + (Fin.last m).1, by omega⟩) M = quotLat L M
      rw [hl, F.step_last]
    step_saturated := fun k => isSaturated_quotLat hMsat (F.step_saturated _) (hge k)
    step_strictMono := fun a b hab => by
      have hlt : F.step ⟨j₀.1 + a.1, by omega⟩ < F.step ⟨j₀.1 + b.1, by omega⟩ :=
        F.step_strictMono (show (⟨j₀.1 + a.1, by omega⟩ : Fin (F.len + 1)) < ⟨j₀.1 + b.1, by omega⟩ from by
          change j₀.1 + a.1 < j₀.1 + b.1; exact Nat.add_lt_add_left hab _)
      refine lt_of_le_of_ne (Submodule.map_mono hlt.le) fun heq => hlt.ne ?_
      have heq' : quotLat (F.step ⟨j₀.1 + a.1, by omega⟩) M =
          quotLat (F.step ⟨j₀.1 + b.1, by omega⟩) M := heq
      rw [← liftSub_quotLat hMsat (F.step_saturated _) (hge a),
        ← liftSub_quotLat hMsat (F.step_saturated _) (hge b), heq']
    quot_semistable := fun i => by
      have hqq := quotLat_quotLat (L := F.step ⟨j₀.1 + i.1 + 1, by omega⟩)
        (M := M) (N := F.step ⟨j₀.1 + i.1, by omega⟩) (hge i.castSucc)
      change IsSemistable (quotLat (quotLat (F.step ⟨j₀.1 + (i.1 + 1), by omega⟩) M)
        (quotLat (F.step ⟨j₀.1 + i.1, by omega⟩) M))
      have hidx : (⟨j₀.1 + (i.1 + 1), by omega⟩ : Fin (F.len + 1)) = ⟨j₀.1 + i.1 + 1, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      rw [hidx, hqq]
      exact F.quot_semistable ⟨j₀.1 + i.1, by omega⟩
    slope_strictAnti := fun i j hij => by
      have hqi := quotLat_quotLat (L := F.step ⟨j₀.1 + i.1 + 1, by omega⟩)
        (M := M) (N := F.step ⟨j₀.1 + i.1, by omega⟩) (hge i.castSucc)
      have hqj := quotLat_quotLat (L := F.step ⟨j₀.1 + j.1 + 1, by omega⟩)
        (M := M) (N := F.step ⟨j₀.1 + j.1, by omega⟩) (hge j.castSucc)
      have hidx_i : (⟨j₀.1 + (i.1 + 1), by omega⟩ : Fin (F.len + 1)) = ⟨j₀.1 + i.1 + 1, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      have hidx_j : (⟨j₀.1 + (j.1 + 1), by omega⟩ : Fin (F.len + 1)) = ⟨j₀.1 + j.1 + 1, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      change ArakelovCovolume.slope (quotLat (quotLat (F.step ⟨j₀.1 + (j.1 + 1), by omega⟩) M)
          (quotLat (F.step ⟨j₀.1 + j.1, by omega⟩) M)) <
        ArakelovCovolume.slope (quotLat (quotLat (F.step ⟨j₀.1 + (i.1 + 1), by omega⟩) M)
          (quotLat (F.step ⟨j₀.1 + i.1, by omega⟩) M))
      rw [hidx_i, hidx_j, hqi, hqj]
      exact F.slope_strictAnti ⟨j₀.1 + i.1, by omega⟩ ⟨j₀.1 + j.1, by omega⟩
        (Nat.add_lt_add_left hij _)
  }
  have hQ0 : quotLat L M ≠ ⊥ := quotLat_ne_bot_of_lt hMsat hne
  have h1 := hnFiltration_first_eq_maxDestab (quotLat L M) hQ0 FQ
  have hmuQ : muMax (quotLat L M) = ArakelovCovolume.slope (FQ.step ⟨1, Nat.succ_lt_succ hm_pos⟩) := by
    rw [h1, slope_maxDestab _ hQ0]
  have hstep1 : FQ.step ⟨1, Nat.succ_lt_succ hm_pos⟩ = F.quot ⟨j₀.1, hj₀_lt⟩ := by
    change quotLat (F.step ⟨j₀.1 + 1, by omega⟩) M = quotLat (F.step ⟨j₀.1 + 1, by omega⟩) (F.step j₀)
    rfl
  rw [hmuQ, hstep1]
  by_contra hge_θ
  push Not at hge_θ
  have hlt := (F.mem_filter_trunc_iff θ ⟨j₀.1, hj₀_lt⟩).mp hge_θ
  exact lt_irrefl j₀.1 hlt

/-- **Bost Truncation Inclusion Theorem**:
if `φ : N →ₗ[ℤ] L` has operator bound `‖φ x‖ ≤ C * ‖x‖` (`C > 0`) and `N` satisfies
`θ + Real.log C ≤ muMin N` (when `N ≠ ⊥`), then `φ(N)` lands ENTIRELY inside the `≥ θ`
Harder–Narasimhan truncation `F.trunc θ` of `L`! -/
theorem bost_truncation_inclusion
    {N : Submodule ℤ E} {L : Submodule ℤ F} [DiscreteTopology N] [DiscreteTopology L]
    (F_HN : HNFiltration L) (φ : N →ₗ[ℤ] L) (C θ : ℝ) (hCpos : 0 < C)
    (hC : ∀ x : N, ‖((φ x : L) : F)‖ ≤ C * ‖(x : E)‖)
    (hmuMin : N ≠ ⊥ → θ + Real.log C ≤ muMin N) :
    ∀ x : N, ((φ x : L) : F) ∈ F_HN.trunc θ := by
  intro x
  by_cases hN0 : N = ⊥
  · have hx0 : x = 0 := Subtype.ext ((Submodule.mem_bot ℤ).mp (hN0 ▸ x.2))
    rw [hx0, map_zero]; exact (F_HN.trunc θ).zero_mem
  by_cases htop : F_HN.trunc θ = L
  · rw [htop]; exact (φ x).2
  let M := F_HN.trunc θ
  have hMsat : IsSaturated L M := F_HN.trunc_isSaturated θ
  let Q := quotLat L M
  have : DiscreteTopology Q := discreteTopology_quotLat hMsat
  let ψ : N →ₗ[ℤ] Q :=
    { toFun := fun y => ⟨projOrth M ((φ y : L) : F), ⟨((φ y : L) : F), (φ y).2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by
        change projOrth M (((φ (a + b) : L) : F)) = _
        rw [map_add, Submodule.coe_add, map_add]; rfl)
      map_smul' := fun c a => Subtype.ext (by
        change projOrth M (((φ (c • a) : L) : F)) = _
        rw [map_zsmul, Submodule.coe_smul, map_zsmul]; rfl) }
  have hψ0 : ψ = 0 := by
    by_contra hne
    have hψ_lip : ∀ y : N, ‖((ψ y : Q) : F)‖ ≤ C * ‖(y : E)‖ := fun y =>
      (norm_projOrth_le M _).trans (hC y)
    have hBost := bost_muMin_le_muMax_add_log ψ hne C hCpos hψ_lip
    have hlt := F_HN.muMax_quotLat_trunc_lt θ htop
    linarith [hmuMin hN0]
  have hx0 : projOrth M ((φ x : L) : F) = 0 :=
    congrArg (fun z : Q => (z : F)) (LinearMap.congr_fun hψ0 x)
  exact hMsat.2 _ (φ x).2 ((projOrth_eq_zero_iff M _).mp hx0)

end BostMorphismAndMuMin

/-! ## Section 6: Euclidean Dual Lattice, Slope Duality & Sharp Successive-Minima Bounds -/

section DualLatticeAndSuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **Euclidean Dual Lattice** `L* ⊂ span_ℝ(L)` of a lattice `L ⊂ E`:
`L* = { w ∈ span_ℝ(L) | ∀ v ∈ L, ⟨w, v⟩ ∈ ℤ }`. -/
def dualLat (L : Submodule ℤ E) : Submodule ℤ E where
  carrier := { w ∈ Submodule.span ℝ (L : Set E) | ∀ v ∈ L, ∃ n : ℤ, inner ℝ w v = (n : ℝ) }
  add_mem' := by
    rintro w₁ w₂ ⟨hw₁V, hw₁Z⟩ ⟨hw₂V, hw₂Z⟩
    refine ⟨Submodule.add_mem _ hw₁V hw₂V, fun v hv => ?_⟩
    obtain ⟨n₁, hn₁⟩ := hw₁Z v hv
    obtain ⟨n₂, hn₂⟩ := hw₂Z v hv
    exact ⟨n₁ + n₂, by rw [inner_add_left, hn₁, hn₂, Int.cast_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c w ⟨hwV, hwZ⟩
    refine ⟨by rw [← Int.cast_smul_eq_zsmul ℝ]; exact Submodule.smul_mem _ _ hwV, fun v hv => ?_⟩
    obtain ⟨n, hn⟩ := hwZ v hv
    exact ⟨c * n, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hn, Int.cast_mul]⟩

/-- The **Annihilator Sublattice** `annLat L M = L* ∩ (span_ℝ M)ᗮ` of a sublattice `M ≤ L`. -/
def annLat (L M : Submodule ℤ E) : Submodule ℤ E :=
  dualLat L ⊓ (Submodule.span ℝ (M : Set E))ᗮ.restrictScalars ℤ

/-- Construction of the dual basis `b*` of `dualLat L` from any `ℤ`-basis `b` of `L`:
`b* i = ∑ j, (Gram b)⁻¹_{j, i} • b j`, satisfying `⟨b* i, b k⟩ = δ_{i, k}`! -/
theorem exists_dualBasis (L : Submodule ℤ E) [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) :
    ∃ (bD : Basis (Fin r) ℤ (dualLat L)),
      (∀ i k : Fin r, inner ℝ (bD i : E) (b k : E) = if i = k then 1 else 0) ∧
      Matrix.gram ℝ (fun i => (bD i : E)) = (Matrix.gram ℝ (fun i => (b i : E)))⁻¹ ∧
      DiscreteTopology (dualLat L) ∧
      rk (dualLat L) = r ∧
      covol (dualLat L) = (covol L)⁻¹ ∧
      degAr (dualLat L) = -degAr L ∧
      ArakelovCovolume.slope (dualLat L) = -ArakelovCovolume.slope L := by
  let v : Fin r → E := fun i => (b i : E)
  have hvli : LinearIndependent ℝ v := linearIndependent_coe_basis L b
  let G : Matrix (Fin r) (Fin r) ℝ := Matrix.gram ℝ v
  have hGpos : G.PosDef := Matrix.posDef_gram_of_linearIndependent hvli
  have hGdet_pos : 0 < G.det := hGpos.det_pos
  have hGdet_ne : G.det ≠ 0 := hGdet_pos.ne'
  have hGsymm : G.transpose = G := by
    ext i j; simp [G, Matrix.gram_apply, real_inner_comm]
  have hGGinv : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hGdet_ne)
  have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hGdet_ne)
  have hGinv_symm : (G⁻¹).transpose = G⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hGsymm]
  let w : Fin r → E := fun i => ∑ j : Fin r, (G⁻¹) j i • v j
  have hw_inner : ∀ i k : Fin r, inner ℝ (w i) (v k) = if i = k then 1 else 0 := by
    intro i k
    dsimp only [w]
    rw [sum_inner]
    have h1 : ∑ j : Fin r, inner ℝ ((G⁻¹) j i • v j) (v k) = (G * G⁻¹) k i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left]
      have hGkj : G k j = inner ℝ (v j) (v k) := by simp [G, Matrix.gram_apply, real_inner_comm]
      rw [hGkj, mul_comm]
    rw [h1, hGGinv, Matrix.one_apply]
    by_cases h : i = k <;> simp [h, eq_comm]
  have hw_mem_V : ∀ i, w i ∈ Submodule.span ℝ (L : Set E) := fun i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (b j).2)
  have hw_mem_dual : ∀ i, w i ∈ dualLat L := by
    intro i
    refine ⟨hw_mem_V i, fun x hxL => ?_⟩
    let c : Fin r → ℤ := fun k => b.repr ⟨x, hxL⟩ k
    have hx_eq : x = ∑ k : Fin r, (c k : ℝ) • v k := by
      have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hxL⟩)
      rw [Submodule.coe_sum] at h1
      change ∑ k : Fin r, ((c k • b k : L) : E) = x at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => by simp [v, Int.cast_smul_eq_zsmul]
    refine ⟨c i, ?_⟩
    rw [hx_eq, inner_sum]
    have hsum : ∑ k : Fin r, inner ℝ (w i) ((c k : ℝ) • v k) = ∑ k : Fin r, if i = k then (c k : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, hw_inner i k]
      split_ifs <;> ring
    rw [hsum]
    simp
  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 : inner ℝ (∑ i : Fin r, c i • w i) (v k) = 0 := by rw [hc, inner_zero_left]
    rw [sum_inner] at h1
    have h2 : ∑ i : Fin r, inner ℝ (c i • w i) (v k) = c k := by
      rw [Finset.sum_eq_single k]
      · rw [real_inner_smul_left, hw_inner k k, if_pos rfl, mul_one]
      · intro i _ hik; rw [real_inner_smul_left, hw_inner i k, if_neg hik, mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    linarith
  have hwliZ : LinearIndependent ℤ (fun i : Fin r => (⟨w i, hw_mem_dual i⟩ : dualLat L)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 : ∑ i : Fin r, (c i : ℝ) • w i = 0 := by
      have h2 := congrArg Subtype.val hc
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hwli (fun i => (c i : ℝ)) h1 k
  have hspan_v : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (L : Set E) := by
    have hZ : Submodule.span ℤ (Set.range v) = L := by
      have : Set.range v = L.subtype '' Set.range b := Set.range_comp _ _
      rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range v), hZ]
  have hw_spZ : ⊤ ≤ Submodule.span ℤ (Set.range fun i : Fin r => (⟨w i, hw_mem_dual i⟩ : dualLat L)) := by
    intro y _
    rcases y.2 with ⟨hyV, hyZ⟩
    choose n hn using fun k : Fin r => hyZ (v k) (b k).2
    have hy_eq : (y : E) = ∑ i : Fin r, n i • w i := by
      set d := (y : E) - ∑ i : Fin r, n i • w i
      have hdV : d ∈ Submodule.span ℝ (L : Set E) :=
        Submodule.sub_mem _ hyV (Submodule.sum_mem _ fun i _ => by
          rw [← Int.cast_smul_eq_zsmul ℝ]; exact Submodule.smul_mem _ _ (hw_mem_V i))
      have hd_orth : ∀ k : Fin r, inner ℝ d (v k) = 0 := by
        intro k
        dsimp only [d]
        rw [inner_sub_left, hn k, sum_inner]
        have hsum : ∑ i : Fin r, inner ℝ (n i • w i) (v k) = (n k : ℝ) := by
          rw [Finset.sum_eq_single k]
          · rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hw_inner k k, if_pos rfl, mul_one]
          · intro i _ hik
            rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hw_inner i k, if_neg hik, mul_zero]
          · intro h; exact absurd (Finset.mem_univ k) h
        rw [hsum, sub_self]
      have hd_self : inner ℝ d d = 0 := by
        rw [← hspan_v] at hdV
        have h1 : ∀ z ∈ Submodule.span ℝ (Set.range v), inner ℝ d z = 0 := by
          intro z hz
          induction hz using Submodule.span_induction with
          | mem u hu => rcases hu with ⟨k, rfl⟩; exact hd_orth k
          | zero => exact inner_zero_right d
          | add u₁ u₂ _ _ h₁ h₂ => rw [inner_add_right, h₁, h₂, add_zero]
          | smul a u _ hu => rw [real_inner_smul_right, hu, mul_zero]
        exact h1 d hdV
      have hd0 : d = 0 := inner_self_eq_zero.mp hd_self
      exact sub_eq_zero.mp hd0
    have hy_sub : y = ∑ i : Fin r, n i • (⟨w i, hw_mem_dual i⟩ : dualLat L) := by
      apply Subtype.ext; rw [Submodule.coe_sum, hy_eq]; simp
    rw [hy_sub]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bD : Basis (Fin r) ℤ (dualLat L) := Basis.mk hwliZ hw_spZ
  have hbD_coe : ∀ i, (bD i : E) = w i := fun i => by simp [bD]
  have hDiscD : DiscreteTopology (dualLat L) :=
    discreteTopology_of_fin_basis_real_li bD (by simpa [hbD_coe] using hwli)
  have hGramD : Matrix.gram ℝ (fun i => (bD i : E)) = G⁻¹ := by
    ext i k
    rw [Matrix.gram_apply, hbD_coe i, hbD_coe k]
    dsimp only [w]
    rw [sum_inner]
    have h1 : ∑ j : Fin r, inner ℝ ((G⁻¹) j i • v j) (∑ l : Fin r, (G⁻¹) l k • v l) =
        (G⁻¹ * (G * G⁻¹)) i k := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left, inner_sum, Matrix.mul_apply]
      have hsym : (G⁻¹) i j = (G⁻¹) j i := by
        have := congrFun (congrFun hGinv_symm i) j
        simpa [Matrix.transpose_apply] using this.symm
      rw [← hsym, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [real_inner_smul_right]
      simp only [G, Matrix.gram_apply]
      ring
    rw [h1, hGGinv, Matrix.mul_one]
  have hrkD : rk (dualLat L) = r := by
    unfold rk; rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]
  have hrkL : rk L = r := by
    unfold rk; rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hcovD : covol (dualLat L) = (covol L)⁻¹ := by
    rw [covol_eq_sqrt_det_gram (dualLat L) bD, covol_eq_sqrt_det_gram L b, hGramD,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Real.sqrt_inv]
  have hdegD : degAr (dualLat L) = -degAr L := by
    unfold degAr; rw [hcovD, Real.log_inv]
  have hslopeD : ArakelovCovolume.slope (dualLat L) = -ArakelovCovolume.slope L := by
    unfold ArakelovCovolume.slope; rw [hdegD, hrkD, hrkL]; ring
  exact ⟨bD, fun i k => by rw [hbD_coe i]; exact hw_inner i k, hGramD, hDiscD, hrkD, hcovD, hdegD, hslopeD⟩

lemma discreteTopology_dualLat (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (dualLat L) :=
  (exists_dualBasis L (Module.finBasis ℤ L)).choose_spec.2.2.1

theorem rk_dualLat (L : Submodule ℤ E) [DiscreteTopology L] : rk (dualLat L) = rk L :=
  (exists_dualBasis L (Module.finBasis ℤ L)).choose_spec.2.2.2.1

theorem covol_dualLat (L : Submodule ℤ E) [DiscreteTopology L] : covol (dualLat L) = (covol L)⁻¹ :=
  (exists_dualBasis L (Module.finBasis ℤ L)).choose_spec.2.2.2.2.1

theorem degAr_dualLat (L : Submodule ℤ E) [DiscreteTopology L] : degAr (dualLat L) = -degAr L :=
  (exists_dualBasis L (Module.finBasis ℤ L)).choose_spec.2.2.2.2.2.1

theorem slope_dualLat (L : Submodule ℤ E) [DiscreteTopology L] :
    ArakelovCovolume.slope (dualLat L) = -ArakelovCovolume.slope L :=
  (exists_dualBasis L (Module.finBasis ℤ L)).choose_spec.2.2.2.2.2.2

theorem span_real_dualLat (L : Submodule ℤ E) [DiscreteTopology L] :
    Submodule.span ℝ ((dualLat L : Submodule ℤ E) : Set E) = Submodule.span ℝ (L : Set E) := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hle : Submodule.span ℝ ((dualLat L : Submodule ℤ E) : Set E) ≤ Submodule.span ℝ (L : Set E) :=
    Submodule.span_le.mpr fun _ h => h.1
  have hdim : Module.finrank ℝ (Submodule.span ℝ ((dualLat L : Submodule ℤ E) : Set E)) =
      Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [← finrank_int_eq_finrank_real_span (dualLat L), ← finrank_int_eq_finrank_real_span L]
    exact rk_dualLat L
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

/-- **Double Duality of Euclidean Lattices**: `dualLat (dualLat L) = L`! -/
theorem dualLat_dualLat (L : Submodule ℤ E) [DiscreteTopology L] :
    dualLat (dualLat L) = L := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  let b := Module.finBasis ℤ L
  obtain ⟨bD, hinner, _⟩ := exists_dualBasis L b
  have hle : L ≤ dualLat (dualLat L) := by
    intro v hvL
    refine ⟨(span_real_dualLat L).symm ▸ Submodule.subset_span hvL, fun w hwD => ?_⟩
    obtain ⟨n, hn⟩ := hwD.2 v hvL
    exact ⟨n, by rw [real_inner_comm]; exact hn⟩
  apply le_antisymm _ hle
  intro x hxDD
  rcases hxDD with ⟨hxV, hxZ⟩
  rw [span_real_dualLat L] at hxV
  have hspan_b : Submodule.span ℝ (Set.range fun i => (b i : E)) = Submodule.span ℝ (L : Set E) := by
    have hZ : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
      have : Set.range (fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp _ _
      rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (b i : E)), hZ]
  rw [← hspan_b, Submodule.mem_span_range_iff_exists_fun] at hxV
  obtain ⟨c, hc⟩ := hxV
  have hc_int : ∀ i, ∃ n : ℤ, c i = (n : ℝ) := by
    intro i
    obtain ⟨n, hn⟩ := hxZ (bD i : E) (bD i).2
    refine ⟨n, ?_⟩
    have hpair : inner ℝ x (bD i : E) = c i := by
      rw [← hc, sum_inner, Finset.sum_eq_single i]
      · rw [real_inner_smul_left, real_inner_comm, hinner i i, if_pos rfl, mul_one]
      · intro k _ hki
        rw [real_inner_smul_left, real_inner_comm, hinner i k, if_neg (Ne.symm hki), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    linarith
  choose n hn using hc_int
  have hx_eq : x = ∑ i, n i • (b i : E) := by
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => by rw [hn i, Int.cast_smul_eq_zsmul]
  rw [hx_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

/-- **Exact Annihilator–Quotient Duality**:
for any saturated sublattice `M ≤ L` of a discrete lattice `L ⊂ E`:
1. `annLat L M` is a saturated sublattice of `dualLat L`,
2. `annLat L M = dualLat (quotLat L M)`! -/
theorem annLat_eq_dualLat_quotLat {L M : Submodule ℤ E} [DiscreteTopology L]
    (hM : IsSaturated L M) :
    IsSaturated (dualLat L) (annLat L M) ∧
    annLat L M = dualLat (quotLat L M) := by
  have : DiscreteTopology M := discreteTopology_of_le hM.1
  have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hM
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hsat_ann : IsSaturated (dualLat L) (annLat L M) := by
    refine ⟨inf_le_left, fun x hxD hxsp => ⟨hxD, ?_⟩⟩
    have hle : Submodule.span ℝ ((annLat L M : Submodule ℤ E) : Set E) ≤
        (Submodule.span ℝ (M : Set E))ᗮ :=
      Submodule.span_le.mpr fun y hy => hy.2
    exact hle hxsp
  refine ⟨hsat_ann, ?_⟩
  -- Compare `annLat L M` and `dualLat (quotLat L M)` directly by membership!
  have hspan_Q : Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E) =
      Submodule.span ℝ (L : Set E) ⊓ (Submodule.span ℝ (M : Set E))ᗮ := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hxL, rfl⟩
      refine ⟨?_, projOrth_mem_orthogonal M x⟩
      have hxV : x ∈ Submodule.span ℝ (L : Set E) := Submodule.subset_span hxL
      have hsub : x - projOrth M x ∈ Submodule.span ℝ (L : Set E) :=
        Submodule.span_mono (show (M : Set E) ⊆ (L : Set E) from hM.1) (sub_projOrth_mem_span M x)
      simpa using Submodule.sub_mem _ hxV hsub
    · rintro y ⟨hyL, hyM⟩
      have hpy : projOrth M y = y := projOrth_eq_self_of_mem_orthogonal M hyM
      rw [← hpy]
      have hmap : projOrth M y ∈ (Submodule.span ℝ (L : Set E)).map (projOrth M) := ⟨y, hyL, rfl⟩
      rw [Submodule.map_span] at hmap
      exact hmap
  ext w
  constructor
  · rintro ⟨⟨hwV, hwZ⟩, hwOrth⟩
    refine ⟨hspan_Q.symm ▸ ⟨hwV, hwOrth⟩, fun y hyQ => ?_⟩
    rcases hyQ with ⟨x, hxL, rfl⟩
    change ∃ n : ℤ, inner ℝ w (projOrth M x) = (n : ℝ)
    rw [inner_projOrth_left M hwOrth x]
    exact hwZ x hxL
  · rintro ⟨hwQ, hwQZ⟩
    rw [hspan_Q] at hwQ
    refine ⟨⟨hwQ.1, fun x hxL => ?_⟩, hwQ.2⟩
    rw [← inner_projOrth_left M hwQ.2 x]
    exact hwQZ (projOrth M x) ⟨x, hxL, rfl⟩

theorem annLat_annLat {L M : Submodule ℤ E} [DiscreteTopology L] (hM : IsSaturated L M) :
    annLat (dualLat L) (annLat L M) = M := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hM
  have hann := annLat_eq_dualLat_quotLat hM
  have : DiscreteTopology (annLat L M) := discreteTopology_of_le hann.1.1
  have : DiscreteTopology (quotLat (dualLat L) (annLat L M)) := discreteTopology_quotLat hann.1
  have hann2 := annLat_eq_dualLat_quotLat hann.1
  have hle : M ≤ annLat (dualLat L) (annLat L M) := by
    intro x hxM
    refine ⟨(dualLat_dualLat L).symm ▸ hM.1 hxM, ?_⟩
    intro y hy
    have hle_orth : Submodule.span ℝ ((annLat L M : Submodule ℤ E) : Set E) ≤
        (Submodule.span ℝ (M : Set E))ᗮ := Submodule.span_le.mpr fun z hz => hz.2
    rw [real_inner_comm]
    exact hle_orth hy x (Submodule.subset_span hxM)
  have hrk : rk M = rk (annLat (dualLat L) (annLat L M)) := by
    have h1 : rk (annLat L M) = rk (quotLat L M) := by
      rw [hann.2, rk_dualLat]
    have h2 : rk (annLat (dualLat L) (annLat L M)) = rk (quotLat (dualLat L) (annLat L M)) := by
      rw [hann2.2, rk_dualLat]
    have hadd1 := rk_add_quotLat hM
    have hadd2 := rk_add_quotLat hann.1
    have hrkD := rk_dualLat L
    omega
  have hleL : annLat (dualLat L) (annLat L M) ≤ L :=
    hann2.1.1.trans (le_of_eq (dualLat_dualLat L))
  exact (eq_of_isSaturated_of_rk_eq hM hleL hle hrk).symm

/-- **Exact Dual Lattice Slope Duality (`μ_max(L*) = -μ_min(L)`)**:
for any nonzero discrete Euclidean lattice `L ⊂ E`, `muMax (dualLat L) = -muMin L`! -/
theorem muMax_dualLat (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    muMax (dualLat L) = -muMin L := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  apply le_antisymm
  · -- `muMax (dualLat L) = slope K = -slope (quotLat L M) ≤ -muMin L` where `K = maxDestab (dualLat L)`
    let K := maxDestab (dualLat L)
    have hKsat : IsSaturated (dualLat L) K := maxDestab_isSaturated (dualLat L)
    have hKne : K ≠ ⊥ := maxDestab_ne_bot (dualLat L) hDL0
    have hKslope : ArakelovCovolume.slope K = muMax (dualLat L) := slope_maxDestab (dualLat L) hDL0
    let M := annLat (dualLat L) K
    have hMsat : IsSaturated L M := by
      have h1 := (annLat_eq_dualLat_quotLat hKsat).1
      rwa [dualLat_dualLat L] at h1
    have hKeq : annLat L M = K := by
      have h1 := annLat_annLat hKsat
      rwa [dualLat_dualLat L] at h1
    have hMne : M ≠ L := by
      intro hML
      have hq0 : quotLat L M = ⊥ := by rw [hML, quotLat_self]
      have hK0 : K = ⊥ := by
        rw [← hKeq, (annLat_eq_dualLat_quotLat hMsat).2, hq0]
        ext w
        change (w ∈ Submodule.span ℝ ((⊥ : Submodule ℤ E) : Set E) ∧
            ∀ v ∈ (⊥ : Submodule ℤ E), ∃ n : ℤ, inner ℝ w v = (n : ℝ)) ↔ w = 0
        have hbot : Submodule.span ℝ ((⊥ : Submodule ℤ E) : Set E) = ⊥ := by
          rw [Submodule.bot_coe, Submodule.span_singleton_eq_bot.mpr rfl]
        rw [hbot, Submodule.mem_bot]
        exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => ⟨0, by simp [h]⟩⟩⟩
      exact hKne hK0
    have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hMsat
    have hslope_K : ArakelovCovolume.slope K = -ArakelovCovolume.slope (quotLat L M) := by
      rw [← hKeq, (annLat_eq_dualLat_quotLat hMsat).2, slope_dualLat]
    have hle := muMin_le_slope_quotLat hMsat hMne
    linarith
  · -- `-muMin L = -slope (quotLat L M) = slope (annLat L M) ≤ muMax (dualLat L)`
    let F := canonicalHN L
    have hpos := F.len_pos_of_ne_bot hL0
    let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
    let M := F.step ilast.castSucc
    have hMsat : IsSaturated L M := F.step_saturated _
    have hlast_succ : ilast.succ = Fin.last F.len := by ext; simp [ilast]; omega
    have hMne : M ≠ L := by
      rw [← F.step_last, ← hlast_succ]
      exact ne_of_lt (F.step_strictMono (Fin.castSucc_lt_succ (i := ilast)))
    have hquot : F.quot ilast = quotLat L M := by
      unfold HNFiltration.quot
      rw [hlast_succ, F.step_last]
    have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hMsat
    have hann := annLat_eq_dualLat_quotLat hMsat
    have hK_ne : annLat L M ≠ ⊥ := by
      intro h0
      have h1 : rk (annLat L M) = rk (quotLat L M) := by rw [hann.2, rk_dualLat]
      rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
      have hqpos := rk_pos_of_ne_bot _ (quotLat_ne_bot_of_lt hMsat hMne)
      omega
    have hle := slope_le_muMax (dualLat L) (annLat L M) hann.1.1 hK_ne
    rw [hann.2, slope_dualLat] at hle
    have hmuMin : muMin L = ArakelovCovolume.slope (quotLat L M) := by
      rw [F.muMin_eq_last_hnSlope hL0]; unfold HNFiltration.hnSlope; rw [hquot]
    linarith

/-- **Exact Dual Lattice Minimal-Slope Duality (`μ_min(L*) = -μ_max(L)`)**:
for any nonzero discrete Euclidean lattice `L ⊂ E`, `muMin (dualLat L) = -muMax L`! -/
theorem muMin_dualLat (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    muMin (dualLat L) = -muMax L := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  have h := muMax_dualLat (dualLat L) hDL0
  rw [dualLat_dualLat L] at h
  linarith

/-- **Semistability Duality**: a nonzero discrete lattice `L` is semistable iff its dual `L*` is! -/
theorem isSemistable_dualLat_iff (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    IsSemistable (dualLat L) ↔ IsSemistable L := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  rw [isSemistable_iff_muMax_eq_slope (dualLat L) hDL0, isSemistable_iff_muMax_eq_slope L hL0,
    muMax_dualLat L hL0, slope_dualLat L]
  constructor
  · intro heq
    have hmuMin_eq : muMin L = ArakelovCovolume.slope L := by linarith
    -- If `muMin L = slope L`, then `F.len = 1`, so `muMax L = slope L`!
    let F := canonicalHN L
    have hpos := F.len_pos_of_ne_bot hL0
    let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
    have hlast_eq : F.hnSlope ilast = ArakelovCovolume.slope L := by
      rw [← F.muMin_eq_last_hnSlope hL0, hmuMin_eq]
    have hlen1 : F.len = 1 := by
      by_contra hne
      have hlt0 : (⟨0, hpos⟩ : Fin F.len) < ilast := by show 0 < F.len - 1; omega
      have hstrict : F.hnSlope ilast < F.hnSlope ⟨0, hpos⟩ := F.slope_strictAnti ⟨0, hpos⟩ ilast hlt0
      have hdeg := F.degAr_eq_sum
      have hrk := F.rk_eq_sum
      have hge_all : ∀ i : Fin F.len, (rk (F.quot i) : ℝ) * F.hnSlope ilast ≤
          (rk (F.quot i) : ℝ) * F.hnSlope i := fun i => by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rcases eq_or_lt_of_le (show i ≤ ilast from by show i.1 ≤ F.len - 1; have := i.2; omega) with rfl | hlt
        · exact le_rfl
        · exact (F.slope_strictAnti i ilast hlt).le
      have : DiscreteTopology (F.quot ⟨0, hpos⟩) := F.quot_discrete ⟨0, hpos⟩
      have hr0_pos : (0 : ℝ) < (rk (F.quot ⟨0, hpos⟩) : ℝ) :=
        Nat.cast_pos.mpr (rk_pos_of_ne_bot _ (F.quot_ne_bot ⟨0, hpos⟩))
      have hstrict_term : (rk (F.quot ⟨0, hpos⟩) : ℝ) * F.hnSlope ilast <
          (rk (F.quot ⟨0, hpos⟩) : ℝ) * F.hnSlope ⟨0, hpos⟩ :=
        mul_lt_mul_of_pos_left hstrict hr0_pos
      have hsum_lt : ∑ i : Fin F.len, (rk (F.quot i) : ℝ) * F.hnSlope ilast <
          ∑ i : Fin F.len, (rk (F.quot i) : ℝ) * F.hnSlope i :=
        Finset.sum_lt_sum (fun i _ => hge_all i) ⟨⟨0, hpos⟩, Finset.mem_univ _, hstrict_term⟩
      rw [← Finset.sum_mul, ← Nat.cast_sum, ← hrk, ← hdeg, hlast_eq] at hsum_lt
      have hrL : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot L hL0)
      unfold ArakelovCovolume.slope at hsum_lt
      rw [mul_div_cancel₀ _ hrL.ne'] at hsum_lt
      exact lt_irrefl _ hsum_lt
    have hq0 : F.quot ilast = L := by
      unfold HNFiltration.quot
      have h0 : ilast.castSucc = 0 := by ext; simp [ilast, hlen1]
      have h1 : ilast.succ = Fin.last F.len := by ext; simp [ilast, hlen1]
      rw [h0, h1, F.step_zero, F.step_last, quotLat_bot]
    have hfirst : F.step ⟨1, Nat.succ_lt_succ hpos⟩ = maxDestab L :=
      hnFiltration_first_eq_maxDestab L hL0 F
    have h1_last : (⟨1, Nat.succ_lt_succ hpos⟩ : Fin (F.len + 1)) = Fin.last F.len := by
      ext; simp [hlen1]
    rw [h1_last, F.step_last] at hfirst
    rw [← slope_maxDestab L hL0, ← hfirst]
  · intro heq
    -- If `muMax L = slope L`, then for every saturated `M ⊂ L`, `degAr M ≤ rk M * slope L`,
    -- so `degAr (L / M) = degAr L - degAr M ≥ rk (L / M) * slope L`, hence `muMin L = slope L`!
    have hmuMin_eq : muMin L = ArakelovCovolume.slope L := by
      apply le_antisymm (muMin_le_slope_le_muMax L hL0).1
      let F := canonicalHN L
      have hpos := F.len_pos_of_ne_bot hL0
      let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
      rw [F.muMin_eq_last_hnSlope hL0]
      let M := F.step ilast.castSucc
      have hMsat : IsSaturated L M := F.step_saturated _
      have hlast_succ : ilast.succ = Fin.last F.len := by ext; simp [ilast]; omega
      have hquot : F.quot ilast = quotLat L M := by
        unfold HNFiltration.quot; rw [hlast_succ, F.step_last]
      have : DiscreteTopology M := discreteTopology_of_le hMsat.1
      have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hMsat
      have hQ0 : quotLat L M ≠ ⊥ := hquot ▸ F.quot_ne_bot ilast
      have hrQ : (0 : ℝ) < (rk (quotLat L M) : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot _ hQ0)
      have hrL : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot L hL0)
      have hdegM : degAr M ≤ (rk M : ℝ) * ArakelovCovolume.slope L := by
        by_cases hM0 : M = ⊥
        · rw [hM0, degAr_bot, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]]; simp
        · have hle := slope_le_muMax L M hMsat.1 hM0
          rw [heq] at hle
          have hrM : (0 : ℝ) < (rk M : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot M hM0)
          have h1 : degAr M / (rk M : ℝ) ≤ ArakelovCovolume.slope L := hle
          rw [div_le_iff₀ hrM] at h1
          linarith
      have hdegL : degAr L = (rk L : ℝ) * ArakelovCovolume.slope L := by
        unfold ArakelovCovolume.slope; exact (mul_div_cancel₀ _ hrL.ne').symm
      have hrk_add : (rk L : ℝ) = (rk M : ℝ) + (rk (quotLat L M) : ℝ) := by
        exact_mod_cast rk_add_quotLat hMsat
      have hdeg_add : degAr L = degAr M + degAr (quotLat L M) := degAr_eq_add_quotLat hMsat
      rw [hrk_add, add_mul] at hdegL
      unfold HNFiltration.hnSlope
      rw [hquot]
      show ArakelovCovolume.slope L ≤ degAr (quotLat L M) / (rk (quotLat L M) : ℝ)
      rw [le_div_iff₀ hrQ]
      linarith
    linarith

/-- **Sharp Dual First-Minimum Equivalence for `muMin L`**:
combining `Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1` with `muMax_dualLat`:
`log λ₁(L*) - (1/2) log (rk L) ≤ μ_min(L) ≤ log λ₁(L*)`! -/
theorem muMin_dual_lambda1_bounds (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let _ := discreteTopology_dualLat L
    Real.log (lambda1 (dualLat L)) - (1 / 2) * Real.log (rk L : ℝ) ≤ muMin L ∧
    muMin L ≤ Real.log (lambda1 (dualLat L)) := by
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  have h := RHDirect.Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1 (dualLat L) hDL0
  rw [muMax_dualLat L hL0, rk_dualLat L] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **Sharp Lower Bound on `muMin L` from the Last Successive Minimum `λ_r(L)`**:
for any nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`),
`-log λ_r(L) ≤ μ_min(L)`! -/
theorem neg_log_succMin_last_le_muMin (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0;
    -Real.log (succMin L ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩) ≤ muMin L := by
  intro r hr
  let klast : Fin r := ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩
  obtain ⟨v, hvL, hvli, hvb⟩ := exists_vecs_attaining_succMin L klast
  have hcard : klast.1 + 1 = r := Nat.sub_add_cancel hr
  have hspan_v : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (L : Set E) := by
    have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (L : Set E) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (hvL i))
    have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) =
        Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
      rw [finrank_span_eq_card hvli, Fintype.card_fin, hcard, ← finrank_int_eq_finrank_real_span L]
      rfl
    exact Submodule.eq_of_le_of_finrank_eq hle hdim
  -- Apply to `M = F.step ilast.castSucc` attaining `muMin L`!
  let F := canonicalHN L
  have hpos := F.len_pos_of_ne_bot hL0
  let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  let M := F.step ilast.castSucc
  have hMsat : IsSaturated L M := F.step_saturated _
  have hlast_succ : ilast.succ = Fin.last F.len := by ext; simp [ilast]; omega
  have hquot : F.quot ilast = quotLat L M := by
    unfold HNFiltration.quot; rw [hlast_succ, F.step_last]
  have : DiscreteTopology (quotLat L M) := discreteTopology_quotLat hMsat
  have hQ0 : quotLat L M ≠ ⊥ := hquot ▸ F.quot_ne_bot ilast
  have hmuMin_eq : muMin L = ArakelovCovolume.slope (quotLat L M) := by
    rw [F.muMin_eq_last_hnSlope hL0]; unfold HNFiltration.hnSlope; rw [hquot]
  rw [hmuMin_eq]
  -- Projected vectors `projOrth M (v i)` span `span_ℝ (quotLat L M)`
  let q : Fin (klast.1 + 1) → E := fun i => projOrth M (v i)
  have hqQ : ∀ i, q i ∈ quotLat L M := fun i => ⟨v i, hvL i, rfl⟩
  have hspan_q : Submodule.span ℝ (Set.range q) = Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E) := by
    have h1 : Set.range q = (projOrth M) '' Set.range v := Set.range_comp _ _
    rw [h1, ← Submodule.map_span, hspan_v, Submodule.map_span]
    rfl
  -- Extract a basis of `span_ℝ (quotLat L M)` from `Set.range q`!
  have hsp_top : (⊤ : Submodule ℝ (Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E))) ≤
      Submodule.span ℝ (Set.range fun i => (⟨q i, Submodule.subset_span (hqQ i)⟩ :
        Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E))) := by
    intro y _
    have hy : (y : E) ∈ Submodule.span ℝ (Set.range q) := hspan_q.symm ▸ y.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, hc⟩ := hy
    have hyeq : y = ∑ i, c i • (⟨q i, Submodule.subset_span (hqQ i)⟩ :
        Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E)) :=
      Subtype.ext (by simpa [Submodule.coe_sum] using hc.symm)
    rw [hyeq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨I, hI_li, hI_sp⟩ := exists_linearIndependent ℝ
    (Set.range fun i => (⟨q i, Submodule.subset_span (hqQ i)⟩ :
      Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E)))
  have hI_fin : I.Finite := (Set.finite_range _).subset hI_li
  let _ : Fintype I := hI_fin.fintype
  let s := rk (quotLat L M)
  have hs_pos : 0 < s := rk_pos_of_ne_bot _ hQ0
  let bQ_R : Basis I ℝ (Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E)) :=
    Basis.mk hI_sp.2 (by rw [Subtype.range_coe, hI_sp.1]; exact hsp_top)
  have hI_card : Fintype.card I = s := by
    have h1 := Module.finrank_eq_card_basis bQ_R
    rw [← finrank_int_eq_finrank_real_span (quotLat L M)] at h1
    exact h1.symm
  let eI' : Fin s ≃ I := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hI_card])
  let w : Fin s → E := fun j => ((eI' j : Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E)) : E)
  have hwQ : ∀ j, w j ∈ quotLat L M := by
    intro j
    obtain ⟨i, hi⟩ := hI_li (eI' j).2
    have hweq : w j = q i := congrArg Subtype.val hi.symm
    rw [hweq]; exact hqQ i
  have hw_norm : ∀ j, ‖w j‖ ≤ succMin L klast := by
    intro j
    obtain ⟨i, hi⟩ := hI_li (eI' j).2
    have hweq : w j = q i := congrArg Subtype.val hi.symm
    rw [hweq]
    exact (norm_projOrth_le M (v i)).trans (hvb i)
  have hwli : LinearIndependent ℝ w := by
    have h1 : LinearIndependent ℝ (fun j : Fin s => (eI' j :
        Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E))) :=
      hI_sp.2.comp eI' eI'.injective
    exact h1.map' (Submodule.span ℝ ((quotLat L M : Submodule ℤ E) : Set E)).subtype
      (Submodule.ker_subtype _)
  have hcov : covol (quotLat L M) ≤ (succMin L klast) ^ s := by
    have h1 := covol_le_prod_norm w hwQ hwli rfl
    have h2 : ∏ j : Fin s, ‖w j‖ ≤ ∏ _j : Fin s, succMin L klast :=
      Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hw_norm j)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    exact h1.trans h2
  have hlog := Real.log_le_log (covol_pos _) hcov
  rw [Real.log_pow] at hlog
  have hsR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs_pos
  unfold ArakelovCovolume.slope degAr
  rw [le_div_iff₀ hsR]
  linarith

/-- **Elementary Banaszczyk Lower Transference Bound**:
`1 ≤ λ₁(L*) * λ_r(L)` (obtained immediately from `muMin_dual_lambda1_bounds` + `neg_log_succMin_last_le_muMin`)! -/
theorem one_le_lambda1_dualLat_mul_succMin_last (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let _ := discreteTopology_dualLat L
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0;
    1 ≤ lambda1 (dualLat L) * succMin L ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ := by
  intro _ r hr
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  have h1 := neg_log_succMin_last_le_muMin L hL0
  have h2 := (muMin_dual_lambda1_bounds L hL0).2
  have hlamD : 0 < lambda1 (dualLat L) := lambda1_pos (dualLat L) hDL0
  have hsucc : 0 < succMin L ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ := succMin_pos L hL0 _
  have hlog : 0 ≤ Real.log (lambda1 (dualLat L) * succMin L ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩) := by
    rw [Real.log_mul hlamD.ne' hsucc.ne']
    linarith
  rw [← Real.exp_zero, ← Real.exp_log (mul_pos hlamD hsucc)]
  exact Real.exp_le_exp.mpr hlog

/-- **Sharp Successive-Minima Lower Bound on the Harder–Narasimhan Polygon**:
for every `k : Fin (rk L)`, `-(k + 1) * log λ_{k+1}(L) ≤ F.hnPolygon (k + 1)`! -/
theorem HNFiltration.neg_log_succMin_mul_le_hnPolygon {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (k : Fin (rk L)) :
    -((k.1 + 1 : ℕ) : ℝ) * Real.log (succMin L k) ≤ F.hnPolygon (k.1 + 1) := by
  obtain ⟨v, hvL, hvli, hvb⟩ := exists_vecs_attaining_succMin L k
  let N := Submodule.span ℤ (Set.range v)
  have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hvL i)
  have : DiscreteTopology N := discreteTopology_of_le hNL
  have hrkN : rk N = k.1 + 1 := by
    unfold rk
    rw [finrank_int_eq_finrank_real_span N,
      show Submodule.span ℝ (N : Set E) = Submodule.span ℝ (Set.range v) by
        rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range v)],
      finrank_span_eq_card hvli, Fintype.card_fin]
  have hcov : covol N ≤ (succMin L k) ^ (k.1 + 1) := by
    have h1 := covol_le_prod_norm (L := N) v (fun i => Submodule.subset_span (show v i ∈ Set.range v from ⟨i, rfl⟩)) hvli hrkN.symm
    have h2 : ∏ i : Fin (k.1 + 1), ‖v i‖ ≤ ∏ _i : Fin (k.1 + 1), succMin L k :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hvb i)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    exact h1.trans h2
  have hlog := Real.log_le_log (covol_pos N) hcov
  rw [Real.log_pow] at hlog
  have hdeg : -((k.1 + 1 : ℕ) : ℝ) * Real.log (succMin L k) ≤ degAr N := by
    unfold degAr; linarith
  have henv := F.degAr_le_hnPolygon hNL
  rw [hrkN] at henv
  exact hdeg.trans henv

end DualLatticeAndSuccessiveMinima

/-! ## Section 7: Direct Discharge of `RHDirect.BostSlopeFiber.SlopeIneq` via HN Filtration & Bost's Theorem -/

section BostSlopeFiberBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The `rk L`-dimensional vector of Harder–Narasimhan slopes of `L` in descending order. -/
def HNFiltration.slopeVec {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) : Fin (rk L) → ℝ :=
  fun j => F.slopesDesc[j.1]'(by rw [F.slopesDesc_length]; exact j.2)

theorem HNFiltration.sum_slopeVec_div_rk {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) :
    (∑ j : Fin (rk L), F.slopeVec j) / (rk L : ℝ) = ArakelovCovolume.slope L := by
  have hsum : ∑ j : Fin (rk L), F.slopeVec j = F.slopesDesc.sum := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · rw [List.length_ofFn, F.slopesDesc_length]
    · intro i h1 h2
      rw [List.getElem_ofFn]
      rfl
  have htot : F.slopesDesc.sum = degAr L := by
    have h := F.hnPolygon_rk
    unfold HNFiltration.hnPolygon at h
    rw [← F.slopesDesc_length, List.take_length] at h
    exact h
  rw [hsum, htot]
  rfl

theorem HNFiltration.muMin_le_slopeVec {L : Submodule ℤ E} [DiscreteTopology L]
    (hL0 : L ≠ ⊥) (F : HNFiltration L) (j : Fin (rk L)) :
    muMin L ≤ F.slopeVec j := by
  have hpos := F.len_pos_of_ne_bot hL0
  let ilast : Fin F.len := ⟨F.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  rw [F.muMin_eq_last_hnSlope hL0]
  have hmem : F.slopeVec j ∈ F.slopesDesc := List.getElem_mem _
  unfold slopesDesc at hmem
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨i, _, hi⟩
  rw [(List.mem_replicate.mp hi).2]
  rcases eq_or_lt_of_le (show i ≤ ilast from by show i.1 ≤ F.len - 1; have := i.2; omega) with rfl | hlt
  · exact le_rfl
  · exact (F.slope_strictAnti i ilast hlt).le

/-- Exact tail-count identity: the number of Harder–Narasimhan slopes `< θ` equals the corank
`rk (quotLat L (F.trunc θ))`! -/
theorem HNFiltration.card_slopeVec_lt_eq_rk_quot_trunc {L : Submodule ℤ E} [DiscreteTopology L]
    (F : HNFiltration L) (θ : ℝ) :
    (Finset.univ.filter fun j : Fin (rk L) => F.slopeVec j < θ).card =
      rk (quotLat L (F.trunc θ)) := by
  -- The number of `j : Fin (rk L)` with `θ ≤ F.slopeVec j` equals `rk (F.trunc θ)`!
  have hge_count : (Finset.univ.filter fun j : Fin (rk L) => θ ≤ F.slopeVec j).card =
      rk (F.trunc θ) := by
    -- Express both as the count of elements `≥ θ` in `F.slopesDesc`!
    have hlist_cnt : ∀ (l : List (Fin F.len)),
        ((l.flatMap fun i => List.replicate (rk (F.quot i)) (F.hnSlope i)).countP (fun x => decide (θ ≤ x))) =
        ((l.filter fun i => decide (θ ≤ F.hnSlope i)).map fun i => rk (F.quot i)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.flatMap_cons, List.countP_append, ih, List.filter_cons]
        by_cases h : θ ≤ F.hnSlope a
        · simp [h, List.countP_replicate]
        · simp [h, List.countP_replicate]
    have hcountP_fin : (Finset.univ.filter fun j : Fin (rk L) => θ ≤ F.slopeVec j).card =
        F.slopesDesc.countP (fun x => decide (θ ≤ x)) := by
      have hofFn : F.slopesDesc = List.ofFn F.slopeVec := by
        apply List.ext_getElem
        · rw [List.length_ofFn, F.slopesDesc_length]
        · intro i h1 h2; rw [List.getElem_ofFn]; rfl
      rw [hofFn, List.countP_eq_length_filter]
      have hsum_eq : ∀ {n : ℕ} (p : Fin n → Bool),
          (List.ofFn p).count true = (Finset.univ.filter fun j : Fin n => p j = true).card := by
        intro n p
        induction n with
        | zero => simp
        | succ n ih =>
          rw [List.ofFn_succ, List.count_cons, ih]
          have hcard : (Finset.univ.filter fun j : Fin (n + 1) => p j = true).card =
              (if p 0 = true then 1 else 0) +
              (Finset.univ.filter fun j : Fin n => p j.succ = true).card := by
            have hbij : (Finset.univ.filter fun j : Fin n => p j.succ = true).card =
                ((Finset.univ.filter fun j : Fin (n + 1) => p j = true).erase 0).card := by
              refine Finset.card_bij (fun j _ => j.succ) ?_ ?_ ?_
              · intro j hj
                rw [Finset.mem_erase, Finset.mem_filter]
                exact ⟨Fin.succ_ne_zero j, Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
              · intro a _ b _ h; exact Fin.succ_inj.mp h
              · intro k hk
                rw [Finset.mem_erase, Finset.mem_filter] at hk
                refine ⟨k.pred hk.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.succ_pred k hk.1⟩
                rw [Fin.succ_pred]
                exact hk.2.2
            rw [hbij]
            by_cases h0 : p 0 = true
            · have hmem : (0 : Fin (n + 1)) ∈ Finset.univ.filter fun j : Fin (n + 1) => p j = true :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ 0, h0⟩
              simp [h0, Finset.card_erase_of_mem hmem]
              have hpos := Finset.card_pos.mpr ⟨0, hmem⟩
              omega
            · have hnot : (0 : Fin (n + 1)) ∉ Finset.univ.filter fun j : Fin (n + 1) => p j = true := by
                simp [h0]
              rw [Finset.erase_eq_of_notMem hnot]
              simp [h0]
          rw [hcard, add_comm]
          cases hp0 : p 0 <;> simp
      have hcp : ∀ (l : List ℝ) (p : ℝ → Bool), (l.filter p).length = (l.map p).count true := by
        intro l p
        induction l with
        | nil => simp
        | cons a l ih => cases hp : p a <;> simp [ih, hp]
      rw [hcp, List.map_ofFn]
      simpa only [Function.comp_def, decide_eq_true_eq] using
        (hsum_eq (fun j => decide (θ ≤ F.slopeVec j))).symm
    rw [hcountP_fin]
    unfold slopesDesc
    rw [hlist_cnt]
    -- Show `((List.finRange F.len).filter (θ ≤ F.hnSlope ·))` has toFinset = `univ.filter (·.1 < (F.truncIdx θ).1)`
    have hnodup : ((List.finRange F.len).filter fun i => decide (θ ≤ F.hnSlope i)).Nodup :=
      (List.nodup_finRange F.len).filter _
    have htoFinset : ((List.finRange F.len).filter fun i => decide (θ ≤ F.hnSlope i)).toFinset =
        Finset.univ.filter fun i : Fin F.len => i.1 < (F.truncIdx θ).1 := by
      ext i
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
        Finset.mem_filter, Finset.mem_univ]
      exact F.mem_filter_trunc_iff θ i
    rw [← List.sum_toFinset _ hnodup, htoFinset, ← F.rk_step_eq_sum (F.truncIdx θ)]
    rfl
  have hcomp : (Finset.univ.filter fun j : Fin (rk L) => F.slopeVec j < θ).card +
      (Finset.univ.filter fun j : Fin (rk L) => θ ≤ F.slopeVec j).card = rk L := by
    have hdisj : Disjoint (Finset.univ.filter fun j : Fin (rk L) => F.slopeVec j < θ)
        (Finset.univ.filter fun j : Fin (rk L) => θ ≤ F.slopeVec j) :=
      Finset.disjoint_filter.mpr fun j _ h1 h2 => not_lt.mpr h2 h1
    have hunion : (Finset.univ.filter fun j : Fin (rk L) => F.slopeVec j < θ) ∪
        (Finset.univ.filter fun j : Fin (rk L) => θ ≤ F.slopeVec j) = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact lt_or_ge _ _
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hadd := rk_add_quotLat (F.trunc_isSaturated θ)
  omega

/-- **Direct Discharge of `RHDirect.BostSlopeFiber.SlopeIneq` from the Canonical HN Filtration**:
if `L ⊂ E` (`L ≠ ⊥`) realizes the common dual fiber `CC` (`B.muCC = slope L`, `B.muMinCC = muMin L`)
and its HN truncation coranks `rk (L / L_{≥ s - log|W| - τ})` satisfy the Bost tail bound,
then **`B.SlopeIneq` holds verbatim**! -/
theorem bostSlopeFiber_slopeIneq_of_hnFiltration (B : RHDirect.BostSlopeFiber)
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (hu : 0 ≤ B.uF) (hcard : 1 ≤ B.cardW)
    (hmuCC : ArakelovCovolume.slope L = B.muCC)
    (hmuMin : B.muMinCC ≤ muMin L)
    (hcorank : 0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
      B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
        (rk (quotLat L ((canonicalHN L).trunc (B.s - Real.log (B.cardW : ℝ) - τ))) : ℝ)
          ≤ RHDirect.ArakelovCovolume.bostTailWeight B.del B.η B.e B.uF τ * (rk L : ℝ)) :
    B.SlopeIneq := by
  let F := canonicalHN L
  refine RHDirect.ArakelovCovolume.bostSlopeFiber_slopeIneq_of_tail_bound B (rk L)
    (rk_pos_of_ne_bot L hL0) F.slopeVec hu hcard
    (F.sum_slopeVec_div_rk.trans hmuCC)
    (fun j => hmuMin.trans (F.muMin_le_slopeVec hL0 j)) ?_
  intro hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ
  rw [F.card_slopeVec_lt_eq_rk_quot_trunc]
  exact hcorank hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ

/-- **End-to-End Bost Morphism Slope Theorem → `RHDirect.BostSlopeFiber.SlopeIneq` Discharge**:
if a discrete lattice `L ⊂ E` (`L ≠ ⊥`) represents the common dual fiber (`slope L = B.muCC`,
`B.muMinCC ≤ muMin L`) and, at every threshold `τ ∈ [0, B.HH]`, a family of source lattices
`N_u` (`u : ι`) with `B.s - τ ≤ muMin (N_u)` maps into `L` via `φ_u : N_u →ₗ[ℤ] L` with
operator norm `≤ B.cardW` such that the joint real image `U_τ = ⨆ u, span_ℝ (φ_u(N_u))` has
codimension `rk L - finrank ℝ U_τ ≤ bostTailWeight B.del B.η B.e B.uF τ * rk L`, then:
1. By **`bost_truncation_inclusion`**, EVERY `φ_u(N_u)` lands inside `L_{≥ s - log|W| - τ}`,
2. Hence `rk (L / L_{≥ s - log|W| - τ}) ≤ rk L - finrank ℝ U_τ`,
3. And **`B.SlopeIneq` holds verbatim**! -/
theorem bostSlopeFiber_slopeIneq_of_bost_morphisms
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    {ι : Type*}
    (B : RHDirect.BostSlopeFiber)
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (hu : 0 ≤ B.uF) (hcard : 1 ≤ B.cardW)
    (hmuCC : ArakelovCovolume.slope L = B.muCC)
    (hmuMin : B.muMinCC ≤ muMin L)
    (N : ℝ → ι → Submodule ℤ E') [∀ τ u, DiscreteTopology (N τ u)]
    (φ : ∀ τ u, N τ u →ₗ[ℤ] L)
    (hNorm : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH, ∀ u (x : N τ u),
      ‖((φ τ u x : L) : E)‖ ≤ (B.cardW : ℝ) * ‖(x : E')‖)
    (hMuMin : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH, ∀ u, N τ u ≠ ⊥ → B.s - τ ≤ muMin (N τ u))
    (hCodim : 0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
      B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
        ((rk L - Module.finrank ℝ ↥(⨆ u : ι, Submodule.span ℝ
          (Set.range fun x : N τ u => ((φ τ u x : L) : E))) : ℕ) : ℝ)
          ≤ RHDirect.ArakelovCovolume.bostTailWeight B.del B.η B.e B.uF τ * (rk L : ℝ)) :
    B.SlopeIneq := by
  refine bostSlopeFiber_slopeIneq_of_hnFiltration B L hL0 hu hcard hmuCC hmuMin ?_
  intro hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ
  let F := canonicalHN L
  let θ := B.s - Real.log (B.cardW : ℝ) - τ
  have hCpos : (0 : ℝ) < (B.cardW : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  -- By Bost's truncation inclusion theorem, every `φ τ u` lands inside `F.trunc θ`!
  have hincl : (⨆ u : ι, Submodule.span ℝ (Set.range fun x : N τ u => ((φ τ u x : L) : E))) ≤
      Submodule.span ℝ ((F.trunc θ : Submodule ℤ E) : Set E) := by
    refine iSup_le fun u => Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    refine Submodule.subset_span ?_
    refine bost_truncation_inclusion F (φ τ u) (B.cardW : ℝ) θ hCpos (hNorm τ hτ u) ?_ x
    intro hN0
    have h1 := hMuMin τ hτ u hN0
    dsimp only [θ]
    linarith
  have : DiscreteTopology (F.trunc θ) := discreteTopology_of_le (F.trunc_isSaturated θ).1
  have hdim_le : Module.finrank ℝ ↥(⨆ u : ι, Submodule.span ℝ
      (Set.range fun x : N τ u => ((φ τ u x : L) : E))) ≤ rk (F.trunc θ) := by
    unfold rk
    rw [finrank_int_eq_finrank_real_span (F.trunc θ)]
    exact Submodule.finrank_mono hincl
  have hadd := rk_add_quotLat (F.trunc_isSaturated θ)
  have hcor_nat : rk (quotLat L (F.trunc θ)) ≤
      rk L - Module.finrank ℝ ↥(⨆ u : ι, Submodule.span ℝ
        (Set.range fun x : N τ u => ((φ τ u x : L) : E))) := by
    omega
  exact (Nat.cast_le.mpr hcor_nat).trans (hCodim hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ)

end BostSlopeFiberBridge

end

end RHDirect.Stage4ArakelovBost
