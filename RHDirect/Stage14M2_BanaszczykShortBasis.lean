import RHDirect.Stage12BanaszczykTransference
import RHDirect.Stage12SchurWeylLattices

/-!
# RHDirect.Stage14M2_BanaszczykShortBasis

Unconditional, zero-`sorry`, zero-custom-`axiom`, zero-`native_decide` Lean 4 formalization of
**Banaszczyk + Minkowski II Short Lattice Bases over Totally Complex Number Fields** (ZERO LLL!)
for Field-2 Package `M2` Wave 1 (`Stage14M2_*`):

1. **Isometric Lattice Transport & General Euclidean Transference Cover**:
   - `LatticeEuclideanTransport` packaging the isometric reduction of any nonzero discrete lattice
     `L ⊂ E` to a full-rank `IsZLattice ℝ Λ ⊂ EuclideanSpace ℝ (Fin (rk L))`, preserving
     covolumes, dual lattices, `lambda1`, and `succMin`.
   - `exists_attaining_basis_general`: simultaneous attainment of ALL successive minima
     `‖v i‖ ≤ succMin L i` (`i : Fin (rk L)`) via `Stage10GeometryOfNumbers.exists_attaining_basis`.
   - `transference_cover_euclidean` & `transference_cover_euclidean_lambda1`: every point in
     `span_ℝ L` lies within distance `(rk L / 2) / λ₁(L*)` of `L`.

2. **Concrete `ShortAtBasis`, Number-Field Realization & `transference_cover_number_field`**:
   - `ShortRealBasis L B` (Euclidean `ℝ`-basis in `L` with `‖v i‖ ≤ B`) and concrete number-field
     Hermitian `ShortAtBasis K b X L B` (`K`-basis `y : ι → V` inside `L` with archimedean
     norm-squared bound `‖realizeHLat b X (y a)‖^2 ≤ B`), plus `ShortAtBasis.toBasis`,
     `ShortAtBasis.arch_sum_normAt_sq_le`, and `ShortAtBasis.mean_log_normAt_sq_le` (Jensen
     log-mean bound over `InfinitePlace K`).
   - Exact number-field rank & realization lemmas (`nPl_mul_two_eq_finrank`,
     `realizeHLat_ratCast_smul`, `realizeHLat_injective`, `rk_zRealize_eq`, `zRealize_ne_bot`).
   - **`transference_cover_number_field`** & **`banaszczyk_transference_number_field`**:
     covering-radius and successive-minima transference for arbitrary `NumberFieldHLat K`.

3. **Explicit `O(log r)` Short Basis via Banaszczyk + Minkowski II (`short_basis_of_banaszczyk_and_minkowski`)**:
   - `short_basis_of_banaszczyk_and_minkowski_general`: constructs a simultaneously-attaining
     basis `v : Fin r → E` of `L` satisfying BOTH:
     * Banaszczyk pointwise bound `‖v i‖ ≤ r / λ₁(L*)` and `log ‖v i‖ ≤ log r - muMin L`
       (eliminating LLL's exponential `2^{r/2}` blowup), AND
     * Minkowski II product & `O(log r)` orthogonality-defect bound
       `(∑ i, log ‖v i‖) / r + slope L ≤ (1 / 2) * log r` (via `unitBallVolume_ge_cube_bound`).
   - **`short_basis_of_banaszczyk_and_minkowski`**: lifts the Banaszczyk + Minkowski II short
     real basis unconditionally to a concrete `K`-linearly independent `ShortAtBasis` for ANY
     `A : NumberFieldHLat K` (and for `dualLat A.zRealize`), with zero LLL!

4. **`banaszczyk_muMax_via_dual_lambda1` & `banaszczyk_hh_gap_le`**:
   - Sharp `O(log r)` upper bounds on `muMax L` and `NumberFieldHLat.muMax A` via `λ₁(L*)`,
     `slope L`, and `λ_r(L*)` (`banaszczyk_muMax_via_dual_lambda1`,
     `banaszczyk_numberFieldHLat_muMax_via_dual_lambda1`), plus explicit `muMax` upper bound
     from any short dual basis (`muMax_le_log_of_dual_short_basis`).
   - Sharp `O(log r)` Arakelov gap & Bost-frame ceiling bounds (`banaszczyk_hh_gap_le`,
     `banaszczyk_hh_gap_le_of_family`, `banaszczyk_numberFieldHLat_hh_gap_le`) ready for
     `M2` Wave 2 (`ClassMapMuMax` & `RamifiedJointBost`).
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Matrix NumberField NumberField.InfinitePlace
open scoped BigOperators ENNReal Pointwise InnerProductSpace Real

namespace RHDirect.Stage14M2_BanaszczykShortBasis

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis covol_pos rk_pos_of_ne_bot slope_le_muMax bost_slope_inequality)

open RHDirect.Stage2SiegelReduction (lambda1 lambda1_pos lambda1_le_norm
  succMin succMin_mono succMin_zero_eq_lambda1 succMin_pos)

open RHDirect.Stage4ArakelovBost (dualLat discreteTopology_dualLat rk_dualLat covol_dualLat
  degAr_dualLat slope_dualLat span_real_dualLat dualLat_dualLat
  muMin muMin_le_slope_le_muMax muMax_dualLat muMin_dualLat
  muMin_dual_lambda1_bounds neg_log_succMin_last_le_muMin
  one_le_lambda1_dualLat_mul_succMin_last maxDestab maxDestab_isSaturated
  maxDestab_ne_bot slope_maxDestab rk_add_quotLat degAr_eq_add_quotLat
  discreteTopology_quotLat quotLat quotLat_ne_bot_of_lt muMin_le_slope_quotLat)

open RHDirect.Stage10GeometryOfNumbers (basisOfZLattice covolume_eq_abs_det
  shortestNorm successiveMinimum successiveMinimum_pos successiveMinimum_mono
  exists_attaining_basis minkowski_second_theorem_upper unitBallVolume_eq)

open RHDirect.Stage11BostDworkSqueeze (covol_eq_zlattice_covolume_euclidean
  succMin_eq_stage10_successiveMinimum unitBallVolume_ge_cube_bound
  minkowski_second_theorem_general)

open RHDirect.Stage12BanaszczykTransference (dualLattice dualLattice_eq_dualLat
  dualLattice_dualLattice banaszczyk_transference_key banaszczyk_covering_radius_lambda1
  banaszczyk_transference_general banaszczyk_transference_succMin_general
  banaszczyk_muMin_equiv_neg_log_succMin_last banaszczyk_muMax_dual_equiv_log_succMin_last
  banaszczyk_muMax_add_muMax_dual_sandwich banaszczyk_slope_gap_O_log
  hhBanaszczyk hhBound_of_banaszczyk_transference)

open RHDirect.Stage12SchurWeylLattices (vecAt fcoord normAt realizeHLat norm_sq_realizeHLat
  NumberFieldHLat euclideanSpaceCongr)

/-! ## Section 1: Isometric Lattice Transport & General Euclidean Transference Cover -/

section GeneralEuclideanTransport

/-- Packaged isometric reduction of a nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`) to a
full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin r)`. -/
structure LatticeEuclideanTransport {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) where
  V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  iso : Submodule.span ℝ (L : Set E) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (rk L))
  Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (rk L)))
  discΛ : DiscreteTopology Λ
  zlatΛ : IsZLattice ℝ Λ
  mem_iff : ∀ v : Submodule.span ℝ (L : Set E), (v : E) ∈ L ↔ iso v ∈ Λ
  mem_dual_iff : ∀ w : Submodule.span ℝ (L : Set E),
    (w : E) ∈ dualLat L ↔ iso w ∈ dualLattice Λ

attribute [instance] LatticeEuclideanTransport.discΛ LatticeEuclideanTransport.zlatΛ

/-- Construct the canonical `LatticeEuclideanTransport` for any nonzero discrete lattice `L ⊂ E`. -/
def mkLatticeEuclideanTransport {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    LatticeEuclideanTransport L hL0 := by
  let r := rk L
  let V := Submodule.span ℝ (L : Set E)
  have hdim : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span L).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdim]))
  let iso : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let L₀ : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin r)) := L₀.map (iso.toLinearMap.restrictScalars ℤ)
  let eL : L ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨iso ⟨x.1, Submodule.subset_span x.2⟩,
        ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
      invFun := fun y => ⟨(iso.symm y.1 : E), by
        rcases y.2 with ⟨v, hv, hvEq⟩
        have hvy : iso.symm y.1 = v := by rw [← hvEq]; simp
        rw [hvy]; exact hv⟩
      map_add' := fun a b => Subtype.ext (by
        change iso ((⟨a.1, Submodule.subset_span a.2⟩ : V) + ⟨b.1, Submodule.subset_span b.2⟩) =
          iso ⟨a.1, Submodule.subset_span a.2⟩ + iso ⟨b.1, Submodule.subset_span b.2⟩
        exact map_add iso _ _)
      map_smul' := fun c a => Subtype.ext (by
        change iso (c • (⟨a.1, Submodule.subset_span a.2⟩ : V)) =
          c • iso ⟨a.1, Submodule.subset_span a.2⟩
        exact map_zsmul iso c _)
      left_inv := fun _ => Subtype.ext (by simp)
      right_inv := fun _ => Subtype.ext (by simp) }
  have hDisc : DiscreteTopology Λ :=
    DiscreteTopology.of_continuous_injective (f := eL.symm)
      (Continuous.subtype_mk
        (continuous_subtype_val.comp (iso.symm.continuous.comp continuous_subtype_val)) _)
      eL.symm.injective
  have hspanΛ : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hmem : iso.symm y ∈ Submodule.span ℝ (L₀ : Set V) := by
      have : Submodule.span ℝ (L₀ : Set V) = ⊤ := Submodule.span_span_coe_preimage
      rw [this]; trivial
    have hmap : Submodule.map iso.toLinearMap (Submodule.span ℝ (L₀ : Set V)) =
        Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) := by
      rw [Submodule.map_span]; rfl
    have : iso (iso.symm y) ∈ Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) := by
      rw [← hmap]; exact ⟨iso.symm y, hmem, rfl⟩
    simpa using this
  have hZLat : IsZLattice ℝ Λ := ⟨hspanΛ⟩
  have hmem_Λ : ∀ v : V, (v : E) ∈ L ↔ iso v ∈ Λ := by
    intro v; constructor
    · intro hv; exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, hwEq⟩; have := iso.injective hwEq; rwa [← this]
  have hmem_dual : ∀ w : V, (w : E) ∈ dualLat L ↔ iso w ∈ dualLattice Λ := by
    intro w; constructor
    · rintro ⟨_, hwZ⟩ x hxΛ
      rcases hxΛ with ⟨v, hvL, rfl⟩
      obtain ⟨k, hk⟩ := hwZ (v : E) hvL
      refine ⟨k, ?_⟩
      change inner ℝ (iso v) (iso w) = (k : ℝ)
      rw [iso.inner_map_map, real_inner_comm]
      exact hk
    · intro hwD
      refine ⟨w.2, fun x hxL => ?_⟩
      have hxV : x ∈ V := Submodule.subset_span hxL
      obtain ⟨k, hk⟩ := hwD (iso ⟨x, hxV⟩) ((hmem_Λ ⟨x, hxV⟩).mp hxL)
      refine ⟨k, ?_⟩
      change inner ℝ w ⟨x, hxV⟩ = (k : ℝ)
      rw [← iso.inner_map_map w ⟨x, hxV⟩, real_inner_comm]
      exact hk
  exact
    { iso := iso
      Λ := Λ
      discΛ := hDisc
      zlatΛ := hZLat
      mem_iff := hmem_Λ
      mem_dual_iff := hmem_dual }

lemma LatticeEuclideanTransport.succMin_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] {hL0 : L ≠ ⊥}
    (T : LatticeEuclideanTransport L hL0) (k : Fin (rk L)) :
    succMin L k =
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (rk L))) 1) T.Λ k := by
  have := T.discΛ
  have := T.zlatΛ
  rw [← succMin_eq_stage10_successiveMinimum T.Λ k]
  unfold succMin
  congr 1
  ext R
  simp only [Fin.val_cast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hR, v, hvL, hvli, hvn⟩
    refine ⟨hR, fun j => T.iso ⟨v j, Submodule.subset_span (hvL j)⟩,
      fun j => (T.mem_iff _).mp (hvL j), ?_, fun j => by simpa using hvn j⟩
    have hvliV : LinearIndependent ℝ
        (fun j => (⟨v j, Submodule.subset_span (hvL j)⟩ : Submodule.span ℝ (L : Set E))) :=
      hvli.of_comp (Submodule.span ℝ (L : Set E)).subtype
    exact hvliV.map' T.iso.toLinearMap T.iso.ker
  · rintro ⟨hR, w, hwΛ, hwli, hwn⟩
    refine ⟨hR, fun j => (T.iso.symm (w j) : E),
      fun j => (T.mem_iff _).mpr (by simpa using hwΛ j), ?_, fun j => by
        change ‖T.iso.symm (w j)‖ ≤ R
        rw [T.iso.symm.norm_map]; exact hwn j⟩
    exact (hwli.map' T.iso.symm.toLinearMap T.iso.symm.ker).map'
      (Submodule.span ℝ (L : Set E)).subtype (Submodule.ker_subtype _)

lemma LatticeEuclideanTransport.lambda1_dual_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] {hL0 : L ≠ ⊥}
    (T : LatticeEuclideanTransport L hL0) :
    letI := discreteTopology_dualLat L
    letI := T.discΛ
    letI := T.zlatΛ
    lambda1 (dualLat L) = lambda1 (dualLattice T.Λ) := by
  have := discreteTopology_dualLat L
  have := T.discΛ
  have := T.zlatΛ
  unfold lambda1
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hyD, hyne, rfl⟩
    refine ⟨T.iso ⟨y, (span_real_dualLat L) ▸ Submodule.subset_span hyD⟩,
      (T.mem_dual_iff _).mp hyD, ?_, ?_⟩
    · intro h0
      apply hyne
      have : (⟨y, (span_real_dualLat L) ▸ Submodule.subset_span hyD⟩ :
          Submodule.span ℝ (L : Set E)) = 0 := T.iso.injective (by simpa using h0)
      exact congrArg Subtype.val this
    · simp [T.iso.norm_map]
  · rintro ⟨w, hwD, hwne, rfl⟩
    refine ⟨(T.iso.symm w : E), (T.mem_dual_iff _).mpr (by simpa using hwD), ?_, ?_⟩
    · intro h0
      apply hwne
      have h1 : T.iso.symm w = 0 := Subtype.ext h0
      simpa using congrArg T.iso h1
    · change ‖T.iso.symm w‖ = ‖w‖
      exact T.iso.symm.norm_map w

/-- **Simultaneous Successive-Minima Attainment in Any Inner Product Space (`exists_attaining_basis_general`)**:
for any finite-dimensional real inner product space `E` and any nonzero discrete lattice `L ⊂ E`
(`r = rk L > 0`), there exist `r` `ℝ`-linearly independent vectors `v : Fin r → E` in `L` with
`‖v i‖ ≤ succMin L i` for every `i : Fin r`. -/
theorem exists_attaining_basis_general
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    ∃ v : Fin (rk L) → E,
      (∀ i, v i ∈ L) ∧
      LinearIndependent ℝ v ∧
      Submodule.span ℝ (Set.range v) = Submodule.span ℝ (L : Set E) ∧
      (∀ i, ‖v i‖ ≤ succMin L i) := by
  let T := mkLatticeEuclideanTransport L hL0
  have := T.discΛ
  have := T.zlatΛ
  set B : Set (EuclideanSpace ℝ (Fin (rk L))) := Metric.closedBall 0 1
  have h0B : (0 : EuclideanSpace ℝ (Fin (rk L))) ∈ interior B := by
    rw [mem_interior_iff_mem_nhds]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
  obtain ⟨w, hwΛ, hwli, hwB⟩ :=
    exists_attaining_basis (convex_closedBall 0 1) (isCompact_closedBall 0 1) h0B T.Λ
  let v : Fin (rk L) → E := fun i => (T.iso.symm (w i) : E)
  have hvL : ∀ i, v i ∈ L := fun i => (T.mem_iff _).mpr (by simpa using hwΛ i)
  have hvli : LinearIndependent ℝ v :=
    (hwli.map' T.iso.symm.toLinearMap T.iso.symm.ker).map'
      (Submodule.span ℝ (L : Set E)).subtype (Submodule.ker_subtype _)
  have hspan : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (L : Set E) := by
    have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (L : Set E) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (hvL i))
    have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) =
        Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
      rw [finrank_span_eq_card hvli, Fintype.card_fin, ← finrank_int_eq_finrank_real_span L]
      rfl
    exact Submodule.eq_of_le_of_finrank_eq hle hdim
  have hv_norm : ∀ i, ‖v i‖ ≤ succMin L i := by
    intro i
    rw [T.succMin_eq i]
    have hpos : 0 < successiveMinimum B T.Λ i :=
      successiveMinimum_pos Metric.isBounded_closedBall h0B T.Λ i
    rcases Set.mem_smul_set.mp (hwB i) with ⟨z, hzB, hzEq⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hzB
    have hw_norm : ‖w i‖ ≤ successiveMinimum B T.Λ i := by
      rw [← hzEq, norm_smul, Real.norm_of_nonneg hpos.le]
      nlinarith
    change ‖T.iso.symm (w i)‖ ≤ successiveMinimum B T.Λ i
    rwa [T.iso.symm.norm_map]
  exact ⟨v, hvL, hvli, hspan, hv_norm⟩

/-- **General Euclidean Banaszczyk Transference Cover (`transference_cover_euclidean`)**:
for any finite-dimensional real inner product space `E`, any nonzero discrete lattice `L ⊂ E`,
and any `lam > 0` bounded above by the norms of all nonzero vectors in `dualLat L`, every point
`x ∈ span_ℝ L` satisfies `∃ l ∈ L, ‖x - l‖ * lam ≤ (rk L : ℝ) / 2`. -/
theorem transference_cover_euclidean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {lam : ℝ} (hlam_pos : 0 < lam)
    (hlam_le : ∀ y ∈ dualLat L, y ≠ 0 → lam ≤ ‖y‖)
    {x : E} (hx : x ∈ Submodule.span ℝ (L : Set E)) :
    ∃ l ∈ L, ‖x - l‖ * lam ≤ (rk L : ℝ) / 2 := by
  let T := mkLatticeEuclideanTransport L hL0
  have := T.discΛ
  have := T.zlatΛ
  let u : EuclideanSpace ℝ (Fin (rk L)) := T.iso ⟨x, hx⟩
  obtain ⟨v, hvΛ, hvu⟩ := banaszczyk_transference_key T.Λ hlam_pos u (fun y hyD hy_lt => by
    have hwD : (T.iso.symm y : E) ∈ dualLat L := (T.mem_dual_iff _).mpr (by simpa using hyD)
    have hy0 : y = 0 := by
      by_contra hne
      have hwne : (T.iso.symm y : E) ≠ 0 := fun h0 => by
        have hsub0 : T.iso.symm y = 0 := Subtype.ext h0
        exact hne (by simpa using congrArg T.iso hsub0)
      have hge := hlam_le (T.iso.symm y : E) hwD hwne
      have hnorm : ‖(T.iso.symm y : E)‖ = ‖y‖ := T.iso.symm.norm_map y
      linarith
    exact ⟨0, by simp [hy0]⟩)
  refine ⟨(T.iso.symm v : E), (T.mem_iff _).mpr (by simpa using hvΛ), ?_⟩
  have hnorm_eq : ‖x - (T.iso.symm v : E)‖ = ‖u - v‖ := by
    have hsub : (⟨x, hx⟩ : Submodule.span ℝ (L : Set E)) - T.iso.symm v =
        T.iso.symm (u - v) := by
      rw [map_sub, T.iso.symm_apply_apply]
    change ‖((⟨x, hx⟩ : Submodule.span ℝ (L : Set E)) - T.iso.symm v :
        Submodule.span ℝ (L : Set E))‖ = ‖u - v‖
    rw [hsub, T.iso.symm.norm_map]
  rwa [hnorm_eq]

/-- Euclidean Banaszczyk covering-radius bound stated directly with `lambda1 (dualLat L)`. -/
theorem transference_cover_euclidean_lambda1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {x : E} (hx : x ∈ Submodule.span ℝ (L : Set E)) :
    letI := discreteTopology_dualLat L
    ∃ l ∈ L, ‖x - l‖ ≤ (rk L : ℝ) / (2 * lambda1 (dualLat L)) := by
  have := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  have hlam_pos : 0 < lambda1 (dualLat L) := lambda1_pos (dualLat L) hDL0
  obtain ⟨l, hl, hmul⟩ := transference_cover_euclidean L hL0 hlam_pos
    (fun y hy hy0 => lambda1_le_norm (dualLat L) hy hy0) hx
  refine ⟨l, hl, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  linarith

end GeneralEuclideanTransport

/-! ## Section 2: Concrete `ShortAtBasis`, Number-Field Realization & `transference_cover_number_field` -/

section NumberFieldShortBasisAndCover

/-- Concrete short `ℝ`-basis structure for any discrete lattice `L ⊂ E`:
`rk L` `ℝ`-linearly independent lattice vectors `v i ∈ L` of Euclidean norm at most `B`. -/
structure ShortRealBasis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) (B : ℝ) where
  v : Fin (rk L) → E
  mem : ∀ i, v i ∈ L
  linIndep : LinearIndependent ℝ v
  norm_le : ∀ i, ‖v i‖ ≤ B

lemma ShortRealBasis.span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] {B : ℝ}
    (S : ShortRealBasis L B) :
    Submodule.span ℝ (Set.range S.v) = Submodule.span ℝ (L : Set E) := by
  have hle : Submodule.span ℝ (Set.range S.v) ≤ Submodule.span ℝ (L : Set E) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (S.mem i))
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range S.v)) =
      Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [finrank_span_eq_card S.linIndep, Fintype.card_fin, ← finrank_int_eq_finrank_real_span L]
    rfl
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

/-- **Concrete Number-Field Hermitian Short `K`-Basis (`ShortAtBasis`)**:
over a totally complex number field `K`, a `K`-linearly independent `ι`-tuple `y : ι → V`
lying in the `𝓞 K`-lattice `L` whose archimedean norm-squared
`‖realizeHLat b X (y a)‖ ^ 2 = ∑ v : InfinitePlace K, normAt b X v (y a) ^ 2`
is uniformly bounded by `B`. -/
structure ShortAtBasis (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (B : ℝ) where
  y : ι → V
  mem : ∀ a, y a ∈ L
  linIndep : LinearIndependent K y
  norm_sq_le : ∀ a, ‖realizeHLat b X (y a)‖ ^ 2 ≤ B

namespace ShortAtBasis

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
  {L : Submodule (𝓞 K) V} {B : ℝ}

/-- Upgrade any `ShortAtBasis` directly to a `K`-basis `Module.Basis ι K V`. -/
def toBasis [Nonempty ι] (S : ShortAtBasis K b X L B) : Module.Basis ι K V :=
  basisOfLinearIndependentOfCardEqFinrank S.linIndep
    (by rw [Module.finrank_eq_card_basis b])

theorem toBasis_apply [Nonempty ι] (S : ShortAtBasis K b X L B) (a : ι) :
    S.toBasis a = S.y a := by
  simp [toBasis]

/-- Exact archimedean sum-of-places bound `∑ v : InfinitePlace K, normAt b X v (y a) ^ 2 ≤ B`. -/
theorem arch_sum_normAt_sq_le (S : ShortAtBasis K b X L B) (a : ι) :
    ∑ v : InfinitePlace K, normAt b X v (S.y a) ^ 2 ≤ B := by
  rw [← norm_sq_realizeHLat b X (S.y a)]
  exact S.norm_sq_le a

/-- Jensen / concavity log-mean bound over `InfinitePlace K` (matching `ShortAtMeanLog`):
`(∑ v : InfinitePlace K, log (normAt b X v (y a) ^ 2)) / nPl K ≤ log (B / nPl K)`. -/
theorem mean_log_normAt_sq_le (S : ShortAtBasis K b X L B) (a : ι)
    (_hB : 0 < B) (hpos : ∀ v : InfinitePlace K, 0 < normAt b X v (S.y a)) :
    (∑ v : InfinitePlace K, Real.log (normAt b X v (S.y a) ^ 2)) /
        (Fintype.card (InfinitePlace K) : ℝ) ≤
      Real.log (B / (Fintype.card (InfinitePlace K) : ℝ)) := by
  have : Nonempty (InfinitePlace K) :=
    Fintype.card_pos_iff.mp (by
      have hfin : 0 < Module.finrank ℚ K := Module.finrank_pos
      have hcard : Fintype.card (InfinitePlace K) * 2 = Module.finrank ℚ K := by
        rw [NumberField.IsTotallyComplex.finrank,
          NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
          NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
        ring
      omega)
  let N : ℝ := (Fintype.card (InfinitePlace K) : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  let f : InfinitePlace K → ℝ := fun v => normAt b X v (S.y a) ^ 2
  have hf_pos : ∀ v, 0 < f v := fun v => sq_pos_of_pos (hpos v)
  have hsum_pos : 0 < ∑ v, f v := Finset.sum_pos (fun v _ => hf_pos v) Finset.univ_nonempty
  let M : ℝ := (∑ v, f v) / N
  have hM_pos : 0 < M := div_pos hsum_pos hN
  have hstep : ∀ v, Real.log (f v) - Real.log M ≤ f v / M - 1 := fun v => by
    rw [← Real.log_div (hf_pos v).ne' hM_pos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hf_pos v) hM_pos)
  have hsum_step : ∑ v, (Real.log (f v) - Real.log M) ≤ ∑ v, (f v / M - 1) :=
    Finset.sum_le_sum fun v _ => hstep v
  have hdiv_M : (∑ v, f v) / M = N := by
    dsimp only [M]
    field_simp [hsum_pos.ne', hN.ne']
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hdiv_M,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one]
    at hsum_step
  have hmean : (∑ v, Real.log (f v)) / N ≤ Real.log M := by
    rw [div_le_iff₀ hN]
    linarith
  have hM_le : M ≤ B / N := div_le_div_of_nonneg_right (S.arch_sum_normAt_sq_le a) hN.le
  exact hmean.trans (Real.log_le_log hM_pos hM_le)

end ShortAtBasis

/-- `realizeHLat` commutes with rational scalar multiplication `(q : K) • x ↦ (q : ℝ) • realizeHLat x`. -/
theorem realizeHLat_ratCast_smul
    {K : Type} [Field K]
    {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (q : ℚ) (x : V) :
    realizeHLat b X ((q : K) • x) = (q : ℝ) • realizeHLat b X x := by
  have hvec : ∀ v : InfinitePlace K, vecAt b v ((q : K) • x) = ((q : ℝ) : ℂ) • vecAt b v x := by
    intro v; funext i
    simp only [vecAt, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      map_ratCast, Complex.ofReal_ratCast]
  have hf : ∀ v : InfinitePlace K, fcoord b X v ((q : K) • x) = ((q : ℝ) : ℂ) • fcoord b X v x := by
    intro v
    unfold fcoord
    rw [hvec v, Matrix.mulVec_smul]
  ext p
  simp only [realizeHLat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, WithLp.ofLp_toLp,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hf p.1]
  split_ifs <;> simp [Complex.mul_re, Complex.mul_im]

section NumberFieldRealizationLemmas

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

/-- For a totally complex number field `K`, `2 * |InfinitePlace K| = [K : ℚ]`. -/
theorem nPl_mul_two_eq_finrank :
    Fintype.card (InfinitePlace K) * 2 = Module.finrank ℚ K := by
  rw [NumberField.IsTotallyComplex.finrank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  ring

theorem card_infinitePlace_pos : 0 < Fintype.card (InfinitePlace K) := by
  have h1 := nPl_mul_two_eq_finrank K
  have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

instance instNonemptyInfinitePlace : Nonempty (InfinitePlace K) :=
  Fintype.card_pos_iff.mp (card_infinitePlace_pos K)

/-- `realizeHLat b X` is injective whenever every `X v` is invertible. -/
theorem realizeHLat_injective
    {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    Function.Injective (realizeHLat b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨v₀⟩ := instNonemptyInfinitePlace K
  have hf0 : fcoord b X v₀ x = 0 := by
    funext i
    have hre : (fcoord b X v₀ x i).re = 0 := by
      have h := congrArg (fun z : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) =>
        z (v₀, i, (0 : Fin 2))) hx
      simpa [realizeHLat] using h
    have him : (fcoord b X v₀ x i).im = 0 := by
      have h := congrArg (fun z : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) =>
        z (v₀, i, (1 : Fin 2))) hx
      simpa [realizeHLat] using h
    exact Complex.ext hre him
  have hvec0 : vecAt b v₀ x = 0 := by
    have hmul : X v₀ * (X v₀)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v₀)
    calc vecAt b v₀ x = (1 : Matrix ι ι ℂ) *ᵥ vecAt b v₀ x := (Matrix.one_mulVec _).symm
      _ = (X v₀ * (X v₀)⁻¹) *ᵥ vecAt b v₀ x := by rw [hmul]
      _ = (X v₀) *ᵥ ((X v₀)⁻¹ *ᵥ vecAt b v₀ x) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = (X v₀) *ᵥ fcoord b X v₀ x := rfl
      _ = 0 := by rw [hf0, Matrix.mulVec_zero]
  apply b.repr.injective
  ext i
  have hi : v₀.embedding (b.repr x i) = 0 := congrFun hvec0 i
  exact v₀.embedding.injective (by simpa using hi)

variable {K}

/-- Exact `ℤ`-rank of `A.zRealize` for any `A : NumberFieldHLat K`:
`rk A.zRealize = Module.finrank ℚ K * Fintype.card A.ι`. -/
theorem rk_zRealize_eq [StarRing K] (A : NumberFieldHLat K) :
    rk A.zRealize = Module.finrank ℚ K * Fintype.card A.ι := by
  unfold rk
  rw [ZLattice.rank ℝ A.zRealize, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin, ← nPl_mul_two_eq_finrank K]
  ring

theorem zRealize_ne_bot [StarRing K] (A : NumberFieldHLat K) [Nonempty A.ι] :
    A.zRealize ≠ ⊥ := by
  intro hbot
  have hrk := rk_zRealize_eq A
  rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))) = 0 by
    simp [rk]] at hrk
  have hpos1 : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hpos2 : 0 < Fintype.card A.ι := Fintype.card_pos
  have hmul : 0 < Module.finrank ℚ K * Fintype.card A.ι := mul_pos hpos1 hpos2
  omega

end NumberFieldRealizationLemmas

/-- **Banaszczyk Transference Cover for Totally Complex Number-Field Lattices (`transference_cover_number_field`)**:
for any totally complex number field `K`, any `NumberFieldHLat K` `A` (`[Nonempty A.ι]`), and any
`lam > 0` with `∀ y ∈ dualLat A.zRealize, y ≠ 0 → lam ≤ ‖y‖`, every point
`x : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)` lies within distance
`(Module.finrank ℚ K * Fintype.card A.ι : ℝ) / (2 * lam)` of a lattice point `realizeHLat A.b A.X v`
with `v ∈ A.L`. -/
theorem transference_cover_number_field
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι]
    {lam : ℝ} (hlam_pos : 0 < lam)
    (hlam_le : ∀ y ∈ dualLat A.zRealize, y ≠ 0 → lam ≤ ‖y‖)
    (x : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) :
    ∃ v ∈ A.L,
      ‖x - realizeHLat A.b A.X v‖ * lam ≤
        ((Module.finrank ℚ K * Fintype.card A.ι : ℕ) : ℝ) / 2 := by
  have hne : A.zRealize ≠ ⊥ := zRealize_ne_bot A
  have hx : x ∈ Submodule.span ℝ (A.zRealize : Set _) := by
    rw [IsZLattice.span_top (K := ℝ) (L := A.zRealize)]
    trivial
  obtain ⟨l, hl, hdist⟩ := transference_cover_euclidean A.zRealize hne hlam_pos hlam_le hx
  rcases hl with ⟨v, hvL, rfl⟩
  refine ⟨v, hvL, ?_⟩
  rw [rk_zRealize_eq A] at hdist
  exact hdist

/-- Number-field transference cover stated with `lambda1 (dualLat A.zRealize)`. -/
theorem transference_cover_number_field_lambda1
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι]
    (x : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) :
    letI := discreteTopology_dualLat A.zRealize
    ∃ v ∈ A.L,
      ‖x - realizeHLat A.b A.X v‖ ≤
        ((Module.finrank ℚ K * Fintype.card A.ι : ℕ) : ℝ) /
          (2 * lambda1 (dualLat A.zRealize)) := by
  have := discreteTopology_dualLat A.zRealize
  have hne : A.zRealize ≠ ⊥ := zRealize_ne_bot A
  have hx : x ∈ Submodule.span ℝ (A.zRealize : Set _) := by
    rw [IsZLattice.span_top (K := ℝ) (L := A.zRealize)]
    trivial
  obtain ⟨l, hl, hdist⟩ := transference_cover_euclidean_lambda1 A.zRealize hne hx
  rcases hl with ⟨v, hvL, rfl⟩
  refine ⟨v, hvL, ?_⟩
  rw [rk_zRealize_eq A] at hdist
  exact hdist

/-- Banaszczyk successive-minima transference for `NumberFieldHLat K`:
`λ_{i+1}(A) * λ_{r-i}(A*) ≤ [K : ℚ] * card A.ι`. -/
theorem banaszczyk_transference_number_field
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι]
    (i : Fin (rk A.zRealize)) :
    letI := discreteTopology_dualLat A.zRealize
    succMin A.zRealize i *
      succMin (dualLat A.zRealize) ⟨rk A.zRealize - 1 - i.1, by rw [rk_dualLat]; omega⟩ ≤
      ((Module.finrank ℚ K * Fintype.card A.ι : ℕ) : ℝ) := by
  have h := banaszczyk_transference_succMin_general A.zRealize (zRealize_ne_bot A) i
  exact h.trans_eq (congrArg Nat.cast (rk_zRealize_eq A))

end NumberFieldShortBasisAndCover

/-! ## Section 3: Explicit `O(log r)` Short Basis via Banaszczyk + Minkowski II (ZERO LLL!) -/

section BanaszczykMinkowskiShortBasis

/-- **General Euclidean Short Basis via Banaszczyk + Minkowski II (`short_basis_of_banaszczyk_and_minkowski_general`)**:
for ANY nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`) in ANY finite-dimensional real inner
product space `E`, there exists a simultaneously-attaining short basis `S : ShortRealBasis L ((r : ℝ) / lambda1 (dualLat L))`
satisfying **exponentially sharper bounds than LLL** (with ZERO `2^{r/2}` blowup):
1. Pointwise Banaszczyk norm bound: `∀ i, ‖S.v i‖ ≤ succMin L i ≤ (r : ℝ) / lambda1 (dualLat L)`,
2. Pointwise log-norm bound via `muMin L`:
   `∀ i, Real.log ‖S.v i‖ ≤ Real.log (r : ℝ) - Real.log (lambda1 (dualLat L))` and
   `∀ i, Real.log ‖S.v i‖ ≤ Real.log (r : ℝ) - muMin L`,
3. Minkowski II product bound (`ω_r = (volume (closedBall 0 1)).toReal`):
   `∏ i : Fin r, ‖S.v i‖ ≤ ((2 : ℝ) ^ r / ω_r) * covol L`,
4. Explicit `O(log r)` orthogonality-defect bound (vs LLL's `O(r)`!):
   `(∑ i : Fin r, Real.log ‖S.v i‖) / (r : ℝ) + ArakelovCovolume.slope L ≤ (1 / 2) * Real.log (r : ℝ)`! -/
theorem short_basis_of_banaszczyk_and_minkowski_general
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    letI := discreteTopology_dualLat L
    let r := rk L
    let ω_r := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal
    ∃ S : ShortRealBasis L ((r : ℝ) / lambda1 (dualLat L)),
      (∀ i : Fin r, ‖S.v i‖ ≤ succMin L i) ∧
      (∀ i : Fin r, Real.log ‖S.v i‖ ≤ Real.log (r : ℝ) - Real.log (lambda1 (dualLat L))) ∧
      (∀ i : Fin r, Real.log ‖S.v i‖ ≤ Real.log (r : ℝ) - muMin L) ∧
      (∏ i : Fin r, ‖S.v i‖) ≤ ((2 : ℝ) ^ r / ω_r) * covol L ∧
      (∑ i : Fin r, Real.log ‖S.v i‖) / (r : ℝ) + ArakelovCovolume.slope L ≤
        (1 / 2) * Real.log (r : ℝ) := by
  intro r ω_r
  have := discreteTopology_dualLat L
  have hr : 0 < r := rk_pos_of_ne_bot L hL0
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    omega
  have hlamD_pos : 0 < lambda1 (dualLat L) := lambda1_pos (dualLat L) hDL0
  obtain ⟨v, hvL, hvli, _, hv_norm⟩ := exists_attaining_basis_general L hL0
  -- Banaszczyk upper bound on every `succMin L i`: `succMin L i ≤ succMin L (r - 1) ≤ r / λ₁(L*)`.
  have htr : succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ * lambda1 (dualLat L) ≤ (r : ℝ) := by
    have h := banaszczyk_transference_succMin_general L hL0 ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩
    dsimp only at h
    have hidx : (⟨r - 1 - (r - 1), by rw [rk_dualLat L]; omega⟩ : Fin (rk (dualLat L))) =
        ⟨0, rk_pos_of_ne_bot (dualLat L) hDL0⟩ := by ext; simp
    rwa [hidx, succMin_zero_eq_lambda1 (dualLat L) hDL0] at h
  have hlast_le : succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ ≤ (r : ℝ) / lambda1 (dualLat L) :=
    (le_div_iff₀ hlamD_pos).mpr htr
  have hle_B : ∀ i : Fin r, ‖v i‖ ≤ (r : ℝ) / lambda1 (dualLat L) := fun i => by
    have hi_le : i ≤ ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ := by
      show i.1 ≤ r - 1; have := i.2; omega
    exact (hv_norm i).trans ((succMin_mono L hi_le).trans hlast_le)
  let S : ShortRealBasis L ((r : ℝ) / lambda1 (dualLat L)) :=
    { v := v
      mem := hvL
      linIndep := hvli
      norm_le := hle_B }
  have hv_pos : ∀ i : Fin r, 0 < ‖S.v i‖ := fun i => norm_pos_iff.mpr (S.linIndep.ne_zero i)
  have hlog_pt1 : ∀ i : Fin r, Real.log ‖S.v i‖ ≤ Real.log (r : ℝ) - Real.log (lambda1 (dualLat L)) := by
    intro i
    have hlog := Real.log_le_log (hv_pos i) (hle_B i)
    rwa [Real.log_div hr_pos.ne' hlamD_pos.ne'] at hlog
  have hlog_pt2 : ∀ i : Fin r, Real.log ‖S.v i‖ ≤ Real.log (r : ℝ) - muMin L := by
    intro i
    have hmu := (muMin_dual_lambda1_bounds L hL0).2
    linarith [hlog_pt1 i]
  -- Minkowski II product bound.
  have hmink := (minkowski_second_theorem_general L hL0).2
  have hω_pos : 0 < ω_r := by
    change 0 < (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal
    rw [unitBallVolume_eq hr]
    have hG : 0 < Real.Gamma ((r : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have hprod_le_succ : (∏ i : Fin r, ‖S.v i‖) ≤ ∏ i : Fin r, succMin L i :=
    Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hv_norm i)
  have hsucc_prod_le : (∏ i : Fin r, succMin L i) ≤ ((2 : ℝ) ^ r / ω_r) * covol L := by
    have hdiv := div_le_div_of_nonneg_right hmink hω_pos.le
    rw [mul_div_cancel_right₀ _ hω_pos.ne'] at hdiv
    calc ∏ i : Fin r, succMin L i
        ≤ ((2 : ℝ) ^ r * covol L) / ω_r := hdiv
      _ = ((2 : ℝ) ^ r / ω_r) * covol L := by ring
  have hprod_bound : (∏ i : Fin r, ‖S.v i‖) ≤ ((2 : ℝ) ^ r / ω_r) * covol L :=
    hprod_le_succ.trans hsucc_prod_le
  -- Explicit `O(log r)` orthogonality-defect bound via `unitBallVolume_ge_cube_bound`.
  have hdefect : (∑ i : Fin r, Real.log ‖S.v i‖) / (r : ℝ) + ArakelovCovolume.slope L ≤
      (1 / 2) * Real.log (r : ℝ) := by
    have hprod_pos : 0 < ∏ i : Fin r, ‖S.v i‖ := Finset.prod_pos fun i _ => hv_pos i
    have hcov_pos : 0 < covol L := covol_pos L
    have hlog := Real.log_le_log hprod_pos hprod_bound
    rw [Real.log_prod (fun i _ => (hv_pos i).ne'),
      Real.log_mul (div_pos (pow_pos zero_lt_two r) hω_pos).ne' hcov_pos.ne',
      Real.log_div (pow_pos zero_lt_two r).ne' hω_pos.ne',
      Real.log_pow] at hlog
    have hcube := (unitBallVolume_ge_cube_bound hr).2
    have hsum_le : ∑ i : Fin r, Real.log ‖S.v i‖ ≤
        ((r : ℝ) / 2) * Real.log (r : ℝ) + Real.log (covol L) := by
      linarith
    have hdiv := div_le_div_of_nonneg_right hsum_le hr_pos.le
    have hslope_eq : ArakelovCovolume.slope L = -Real.log (covol L) / (r : ℝ) := by
      unfold ArakelovCovolume.slope degAr
      rfl
    rw [hslope_eq]
    have hsimp : (((r : ℝ) / 2) * Real.log (r : ℝ) + Real.log (covol L)) / (r : ℝ) +
        -Real.log (covol L) / (r : ℝ) = (1 / 2) * Real.log (r : ℝ) := by
      field_simp [hr_pos.ne']; ring
    linarith
  exact ⟨S, hv_norm, hlog_pt1, hlog_pt2, hprod_bound, hdefect⟩

/-- Helper: extracting a `K`-basis `ShortAtBasis` from a `ℚ`-spanning / `ℝ`-linearly independent
set of vectors in `A.zRealize` of Euclidean norm at most `R`. -/
private lemma shortAtBasis_of_realLinIndep_pullback
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K)
    {w : Fin (rk A.zRealize) → A.V}
    (hwL : ∀ j, w j ∈ A.L)
    (hw_li : LinearIndependent ℝ (fun j => realizeHLat A.b A.X (w j)))
    {R : ℝ} (_hR_nonneg : 0 ≤ R) (hw_norm : ∀ j, ‖realizeHLat A.b A.X (w j)‖ ≤ R) :
    Nonempty (ShortAtBasis K A.b A.X A.L (R ^ 2)) := by
  classical
  let W : Submodule K A.V := Submodule.span K (Set.range w)
  have hFinV : Module.Finite K A.V := Module.Finite.of_basis A.b
  have hW_top : W = ⊤ := by
    by_contra hne
    have hlt_dim : Module.finrank K W < Module.finrank K A.V :=
      Submodule.finrank_lt hne
    let m : ℕ := Module.finrank K W
    have hm_lt : m < Fintype.card A.ι := by
      rwa [Module.finrank_eq_card_basis A.b] at hlt_dim
    let bW : Module.Basis (Fin m) K W := Module.finBasis K W
    let dK : ℕ := Module.finrank ℚ K
    let bK : Module.Basis (Fin dK) ℚ K := Module.finBasis ℚ K
    let genFn : Fin dK × Fin m → EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) :=
      fun p => realizeHLat A.b A.X ((bK p.1 : K) • (bW p.2 : A.V))
    let genSet : Set (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) := Set.range genFn
    have hspan_le : Submodule.span ℝ (Set.range fun j => realizeHLat A.b A.X (w j)) ≤
        Submodule.span ℝ genSet := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      dsimp only
      have hjW : w j ∈ W := Submodule.subset_span ⟨j, rfl⟩
      let c : Fin m → K := fun b => bW.repr ⟨w j, hjW⟩ b
      have hw_eq : w j = ∑ b : Fin m, c b • (bW b : A.V) := by
        have h1 : (⟨w j, hjW⟩ : W) = ∑ b : Fin m, c b • bW b := (bW.sum_repr ⟨w j, hjW⟩).symm
        simpa using congrArg (Subtype.val : W → A.V) h1
      have hc_eq : ∀ b : Fin m, c b = ∑ a : Fin dK, (bK.repr (c b) a : ℚ) • bK a := fun b =>
        (bK.sum_repr (c b)).symm
      have hreal_eq : realizeHLat A.b A.X (w j) =
          ∑ b : Fin m, ∑ a : Fin dK,
            (bK.repr (c b) a : ℝ) • realizeHLat A.b A.X ((bK a : K) • (bW b : A.V)) := by
        rw [hw_eq, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hsmul : c b • (bW b : A.V) =
            ∑ a : Fin dK, ((bK.repr (c b) a : ℚ) : K) • ((bK a : K) • (bW b : A.V)) := by
          conv_lhs => rw [hc_eq b]
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Rat.smul_def, mul_smul]
        rw [hsmul, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [realizeHLat_ratCast_smul]
      rw [hreal_eq]
      refine Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun a _ => ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
    have hr_eq : rk A.zRealize = dK * Fintype.card A.ι := rk_zRealize_eq A
    have hdim_lhs : Module.finrank ℝ (Submodule.span ℝ (Set.range fun j =>
        realizeHLat A.b A.X (w j))) = rk A.zRealize := by
      rw [finrank_span_eq_card hw_li, Fintype.card_fin]
    have hdim_rhs : Module.finrank ℝ (Submodule.span ℝ genSet) ≤ dK * m := by
      have h1 : Module.finrank ℝ (Submodule.span ℝ genSet) ≤ genSet.toFinset.card :=
        finrank_span_le_card genSet
      have h2 : genSet.toFinset.card ≤ Fintype.card (Fin dK × Fin m) := by
        dsimp only [genSet]
        rw [Set.toFinset_range]
        exact Finset.card_image_le.trans (by simp)
      calc Module.finrank ℝ (Submodule.span ℝ genSet) ≤ genSet.toFinset.card := h1
        _ ≤ Fintype.card (Fin dK × Fin m) := h2
        _ = dK * m := by simp [Fintype.card_prod, Fintype.card_fin]
    have hle_dim := Submodule.finrank_mono hspan_le
    rw [hdim_lhs, hr_eq] at hle_dim
    have hdK_pos : 0 < dK := Module.finrank_pos
    have hstrict : dK * m < dK * Fintype.card A.ι := Nat.mul_lt_mul_of_pos_left hm_lt hdK_pos
    omega
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range w)
  have hs_fin : s.Finite := hs_li.setFinite
  have hsp_top : Submodule.span K (hs_fin.toFinset : Set A.V) = ⊤ := by
    rw [hs_fin.coe_toFinset, hs_span]
    exact hW_top
  have hli_finset : LinearIndependent K (Subtype.val : hs_fin.toFinset → A.V) := by
    have heq : (Subtype.val : hs_fin.toFinset → A.V) =
        (Subtype.val : s → A.V) ∘ Equiv.setCongr hs_fin.coe_toFinset := rfl
    rw [heq]
    exact hs_li.comp (Equiv.setCongr hs_fin.coe_toFinset) (Equiv.setCongr hs_fin.coe_toFinset).injective
  have hcard_finset : hs_fin.toFinset.card = Fintype.card A.ι := by
    have h1 := finrank_span_eq_card hli_finset
    have hrange : Set.range (Subtype.val : hs_fin.toFinset → A.V) = (hs_fin.toFinset : Set A.V) := by
      ext z; simp
    rw [hrange, hsp_top, finrank_top, Module.finrank_eq_card_basis A.b] at h1
    simpa only [Fintype.card_coe] using h1.symm
  let e : A.ι ≃ hs_fin.toFinset := (Fintype.equivOfCardEq (by simp [hcard_finset])).symm
  let y : A.ι → A.V := fun a => (e a : A.V)
  have hy_mem_s : ∀ a, y a ∈ s := fun a => hs_fin.mem_toFinset.mp (e a).2
  have hy_range : ∀ a, y a ∈ Set.range w := fun a => hs_sub (hy_mem_s a)
  have hy_mem : ∀ a, y a ∈ A.L := fun a => by
    obtain ⟨j, hj⟩ := hy_range a
    rw [← hj]
    exact hwL j
  have hy_li : LinearIndependent K y := hli_finset.comp e e.injective
  have hy_norm_sq : ∀ a, ‖realizeHLat A.b A.X (y a)‖ ^ 2 ≤ R ^ 2 := fun a => by
    obtain ⟨j, hj⟩ := hy_range a
    rw [← hj]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw_norm j) 2
  exact ⟨{ y := y, mem := hy_mem, linIndep := hy_li, norm_sq_le := hy_norm_sq }⟩

/-- **UNCONDITIONAL BANASZCZYK + MINKOWSKI II SHORT BASIS THEOREM (`short_basis_of_banaszczyk_and_minkowski`)**:
for EVERY totally complex number field `K` and EVERY `NumberFieldHLat K` `A` (`[Nonempty A.ι]`),
setting `r = [K : ℚ] * card A.ι` (`= rk A.zRealize`):
1. There exists a concrete `K`-basis `S : ShortAtBasis K A.b A.X A.L (((r : ℝ) / λ₁(A*)) ^ 2)`
   inside `A.L` (ZERO LLL — polynomial `r` instead of `2^{r/2}`!),
2. There exists a full `ℤ`-lattice short real basis `SR : ShortRealBasis A.zRealize ((r : ℝ) / λ₁(A*))`
   satisfying both Banaszczyk's pointwise bound `‖SR.v i‖ ≤ r / λ₁(A*)` AND Minkowski II's
   `O(log r)` orthogonality-defect bound `(∑ i, log ‖SR.v i‖) / r + slope A.zRealize ≤ (1 / 2) * log r`,
3. There exists a dual short real basis `SD : ShortRealBasis (dualLat A.zRealize) ((r : ℝ) / λ₁(A))`
   satisfying `(∑ i, log ‖SD.v i‖) / r - slope A.zRealize ≤ (1 / 2) * log r`! -/
theorem short_basis_of_banaszczyk_and_minkowski
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι] :
    letI := discreteTopology_dualLat A.zRealize
    let r := Module.finrank ℚ K * Fintype.card A.ι
    Nonempty (ShortAtBasis K A.b A.X A.L (((r : ℝ) / lambda1 (dualLat A.zRealize)) ^ 2)) ∧
    (∃ SR : ShortRealBasis A.zRealize ((r : ℝ) / lambda1 (dualLat A.zRealize)),
      (∀ i, Real.log ‖SR.v i‖ ≤ Real.log (r : ℝ) - muMin A.zRealize) ∧
      (∑ i, Real.log ‖SR.v i‖) / (r : ℝ) + ArakelovCovolume.slope A.zRealize ≤
        (1 / 2) * Real.log (r : ℝ)) ∧
    (∃ SD : ShortRealBasis (dualLat A.zRealize) ((r : ℝ) / lambda1 A.zRealize),
      (∀ i, Real.log ‖SD.v i‖ ≤ Real.log (r : ℝ) + ArakelovCovolume.muMax A.zRealize) ∧
      (∑ i, Real.log ‖SD.v i‖) / (r : ℝ) - ArakelovCovolume.slope A.zRealize ≤
        (1 / 2) * Real.log (r : ℝ)) := by
  have := discreteTopology_dualLat A.zRealize
  let r := Module.finrank ℚ K * Fintype.card A.ι
  have hrk : rk A.zRealize = r := rk_zRealize_eq A
  have hne : A.zRealize ≠ ⊥ := zRealize_ne_bot A
  have hDL0 : dualLat A.zRealize ≠ ⊥ := by
    intro h0
    have h1 : rk A.zRealize = rk (dualLat A.zRealize) := (rk_dualLat A.zRealize).symm
    rw [h0, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))) = 0 by
      simp [rk], hrk] at h1
    have : 0 < r := mul_pos Module.finrank_pos Fintype.card_pos
    omega
  obtain ⟨SR0, _, _, hSR_mu, _, hSR_def⟩ :=
    short_basis_of_banaszczyk_and_minkowski_general A.zRealize hne
  -- Transport `SR0` across `hrk : rk A.zRealize = r` for the `ShortAtBasis` pullback.
  have hmem_w : ∀ j : Fin (rk A.zRealize), ∃ x ∈ A.L, realizeHLat A.b A.X x = SR0.v j := fun j => by
    rcases SR0.mem j with ⟨x, hxL, hxeq⟩
    exact ⟨x, hxL, hxeq⟩
  choose w hwL hw_eq using hmem_w
  have hw_li : LinearIndependent ℝ (fun j => realizeHLat A.b A.X (w j)) := by
    simpa only [hw_eq] using SR0.linIndep
  have hlamD_pos : 0 < lambda1 (dualLat A.zRealize) := lambda1_pos (dualLat A.zRealize) hDL0
  have hB_nonneg : 0 ≤ (r : ℝ) / lambda1 (dualLat A.zRealize) :=
    div_nonneg (Nat.cast_nonneg _) hlamD_pos.le
  have hw_norm : ∀ j, ‖realizeHLat A.b A.X (w j)‖ ≤ (r : ℝ) / lambda1 (dualLat A.zRealize) := by
    intro j
    rw [hw_eq j]
    simpa [hrk] using SR0.norm_le j
  obtain ⟨S_at⟩ := shortAtBasis_of_realLinIndep_pullback A hwL hw_li hB_nonneg hw_norm
  -- Dual lattice short basis via `short_basis_of_banaszczyk_and_minkowski_general (dualLat A.zRealize)`.
  obtain ⟨SD0, _, _, hSD_mu, _, hSD_def⟩ :=
    short_basis_of_banaszczyk_and_minkowski_general (dualLat A.zRealize) hDL0
  have hrkD : rk (dualLat A.zRealize) = r := by rw [rk_dualLat, hrk]
  let vD := SD0.v
  let SR : ShortRealBasis A.zRealize ((r : ℝ) / lambda1 (dualLat A.zRealize)) :=
    { v := SR0.v
      mem := SR0.mem
      linIndep := SR0.linIndep
      norm_le := fun i => by exact (SR0.norm_le i).trans (by rw [hrk]) }
  let SD : ShortRealBasis (dualLat A.zRealize) ((r : ℝ) / lambda1 A.zRealize) :=
    { v := vD
      mem := SD0.mem
      linIndep := SD0.linIndep
      norm_le := fun i => by
        calc ‖vD i‖
            ≤ (rk (dualLat A.zRealize) : ℝ) / lambda1 (dualLat (dualLat A.zRealize)) := SD0.norm_le i
          _ = (r : ℝ) / lambda1 A.zRealize := by rw [dualLat_dualLat A.zRealize, hrkD] }
  have hsum_eq : ∑ i, Real.log ‖SR.v i‖ = ∑ i, Real.log ‖SR0.v i‖ := rfl
  have hsumD_eq : ∑ i, Real.log ‖SD.v i‖ = ∑ i, Real.log ‖vD i‖ := rfl
  have hr_cast : (r : ℝ) = (rk A.zRealize : ℝ) := congrArg Nat.cast hrk.symm
  have hrD_cast : (r : ℝ) = (rk (dualLat A.zRealize) : ℝ) := congrArg Nat.cast hrkD.symm
  refine ⟨⟨S_at⟩, ⟨SR, ?_, ?_⟩, ⟨SD, ?_, ?_⟩⟩
  · intro i
    calc Real.log ‖SR.v i‖
        ≤ Real.log (rk A.zRealize : ℝ) - muMin A.zRealize := hSR_mu i
      _ = Real.log (r : ℝ) - muMin A.zRealize := by rw [hrk]
  · rw [hsum_eq, hr_cast]
    exact hSR_def.trans_eq (by rw [hrk])
  · intro i
    calc Real.log ‖SD.v i‖
        ≤ Real.log (rk (dualLat A.zRealize) : ℝ) - muMin (dualLat A.zRealize) := hSD_mu i
      _ = Real.log (r : ℝ) + ArakelovCovolume.muMax A.zRealize := by
          rw [hrkD, muMin_dualLat A.zRealize hne]; ring
  · rw [hsumD_eq, hrD_cast]
    calc (∑ i, Real.log ‖vD i‖) / (rk (dualLat A.zRealize) : ℝ) - ArakelovCovolume.slope A.zRealize
        = (∑ i, Real.log ‖vD i‖) / (rk (dualLat A.zRealize) : ℝ) +
            ArakelovCovolume.slope (dualLat A.zRealize) := by
          rw [slope_dualLat A.zRealize]; ring
      _ ≤ (1 / 2) * Real.log (rk (dualLat A.zRealize) : ℝ) := hSD_def

end BanaszczykMinkowskiShortBasis

/-! ## Section 4: `banaszczyk_muMax_via_dual_lambda1` -/

section BanaszczykMuMaxViaDualLambda1

/-- **Banaszczyk `muMax` Bound via Dual First Minimum (`banaszczyk_muMax_via_dual_lambda1`)**:
for ANY nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`) in ANY finite-dimensional real inner
product space `E`:
1. `O(log r)` upper bound via `slope L` and `λ₁(L) * λ₁(L*)`:
   `muMax L ≤ slope L - log (λ₁(L) * λ₁(L*)) + log r`,
2. `O(log r)` spread bound `muMax L - muMin L ≤ -log (λ₁(L) * λ₁(L*)) + log r`,
3. Direct HN-decomposition upper bound in terms of `slope L` and `λ₁(L*)` alone:
   `muMax L ≤ r * slope L - (r - 1) * log (λ₁(L*)) + ((r - 1) / 2) * log r`,
4. Dual last-minimum equivalence:
   `log (λ_r(L*)) - log r ≤ muMax L ∧ muMax L ≤ log (λ_r(L*))`! -/
theorem banaszczyk_muMax_via_dual_lambda1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    letI := discreteTopology_dualLat L
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0
    have hrD : 0 < rk (dualLat L) := by rw [rk_dualLat L]; exact hr
    ArakelovCovolume.muMax L ≤ ArakelovCovolume.slope L -
        Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (r : ℝ) ∧
    ArakelovCovolume.muMax L - muMin L ≤
        -Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (r : ℝ) ∧
    ArakelovCovolume.muMax L ≤ (r : ℝ) * ArakelovCovolume.slope L -
        ((r : ℝ) - 1) * Real.log (lambda1 (dualLat L)) +
        (((r : ℝ) - 1) / 2) * Real.log (r : ℝ) ∧
    Real.log (succMin (dualLat L) ⟨rk (dualLat L) - 1, Nat.sub_lt hrD zero_lt_one⟩) -
        Real.log (r : ℝ) ≤ ArakelovCovolume.muMax L ∧
    ArakelovCovolume.muMax L ≤
        Real.log (succMin (dualLat L) ⟨rk (dualLat L) - 1, Nat.sub_lt hrD zero_lt_one⟩) := by
  intro r hr hrD
  have := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    omega
  have hS := banaszczyk_muMax_add_muMax_dual_sandwich L hL0
  have h1 : ArakelovCovolume.muMax L ≤ ArakelovCovolume.slope L -
      Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (r : ℝ) := by
    linarith [hS.2.2.2.2]
  have h2 : ArakelovCovolume.muMax L - muMin L ≤
      -Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (r : ℝ) := by
    linarith [hS.1, hS.2.2.2.1]
  -- Prove `muMax L ≤ r * slope L - (r - 1) * muMin L` via `M = maxDestab L` and `quotLat L M`!
  have hHN_bound : ArakelovCovolume.muMax L ≤
      (r : ℝ) * ArakelovCovolume.slope L - ((r : ℝ) - 1) * muMin L := by
    let M := maxDestab L
    have hMsat : Stage4ArakelovBost.IsSaturated L M := maxDestab_isSaturated L
    have hM0 : M ≠ ⊥ := maxDestab_ne_bot L hL0
    have hMslope : ArakelovCovolume.slope M = ArakelovCovolume.muMax L := slope_maxDestab L hL0
    have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
    have hgap_nn : 0 ≤ ArakelovCovolume.muMax L - muMin L := by
      have := muMin_le_slope_le_muMax L hL0; linarith
    by_cases hML : M = L
    · have hmu_eq : ArakelovCovolume.muMax L = ArakelovCovolume.slope L := by
        rw [← hMslope, hML]
      have hmin_le : muMin L ≤ ArakelovCovolume.slope L := (muMin_le_slope_le_muMax L hL0).1
      have hr1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        linarith
      nlinarith
    · have := discreteTopology_of_le hMsat.1
      have := discreteTopology_quotLat hMsat
      have hQ0 : quotLat L M ≠ ⊥ := quotLat_ne_bot_of_lt hMsat hML
      have hrM_pos : 0 < rk M := rk_pos_of_ne_bot M hM0
      have hrM_ge1 : (1 : ℝ) ≤ (rk M : ℝ) := by exact_mod_cast hrM_pos
      have hrk_add : (r : ℝ) = (rk M : ℝ) + (rk (quotLat L M) : ℝ) := by
        exact_mod_cast rk_add_quotLat hMsat
      have hdeg_add : degAr L = degAr M + degAr (quotLat L M) := degAr_eq_add_quotLat hMsat
      have hdegL : degAr L = (r : ℝ) * ArakelovCovolume.slope L := by
        unfold ArakelovCovolume.slope; exact (mul_div_cancel₀ _ hr_pos.ne').symm
      have hdegM : degAr M = (rk M : ℝ) * ArakelovCovolume.muMax L := by
        rw [← hMslope]; unfold ArakelovCovolume.slope
        have hrMp : (0 : ℝ) < (rk M : ℝ) := Nat.cast_pos.mpr hrM_pos
        exact (mul_div_cancel₀ _ hrMp.ne').symm
      have hrQ_pos : (0 : ℝ) < (rk (quotLat L M) : ℝ) :=
        Nat.cast_pos.mpr (rk_pos_of_ne_bot _ hQ0)
      have hdegQ : degAr (quotLat L M) =
          (rk (quotLat L M) : ℝ) * ArakelovCovolume.slope (quotLat L M) := by
        unfold ArakelovCovolume.slope; exact (mul_div_cancel₀ _ hrQ_pos.ne').symm
      have hQ_ge : muMin L ≤ ArakelovCovolume.slope (quotLat L M) :=
        muMin_le_slope_quotLat hMsat hML
      have hmulQ : (rk (quotLat L M) : ℝ) * muMin L ≤ degAr (quotLat L M) := by
        rw [hdegQ]; exact mul_le_mul_of_nonneg_left hQ_ge hrQ_pos.le
      have hprod_nn : 0 ≤ ((rk M : ℝ) - 1) * (ArakelovCovolume.muMax L - muMin L) :=
        mul_nonneg (by linarith) hgap_nn
      have hident : (rk M : ℝ) * ArakelovCovolume.muMax L +
          (rk (quotLat L M) : ℝ) * muMin L =
          ArakelovCovolume.muMax L + ((r : ℝ) - 1) * muMin L +
            ((rk M : ℝ) - 1) * (ArakelovCovolume.muMax L - muMin L) := by
        linear_combination -(muMin L) * hrk_add
      linarith
  have hmuMin_lo := (muMin_dual_lambda1_bounds L hL0).1
  have hr_ge1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hmul_lo := mul_le_mul_of_nonneg_left hmuMin_lo hr_ge1
  have h3 : ArakelovCovolume.muMax L ≤ (r : ℝ) * ArakelovCovolume.slope L -
      ((r : ℝ) - 1) * Real.log (lambda1 (dualLat L)) +
      (((r : ℝ) - 1) / 2) * Real.log (r : ℝ) := by
    linarith
  have hdual := banaszczyk_muMin_equiv_neg_log_succMin_last (dualLat L) hDL0
  dsimp only at hdual
  rw [muMin_dualLat L hL0] at hdual
  have hrD_cast : (rk (dualLat L) : ℝ) = (r : ℝ) := congrArg Nat.cast (rk_dualLat L)
  rw [hrD_cast] at hdual
  exact ⟨h1, h2, h3, by linarith [hdual.2], by linarith [hdual.1]⟩

/-- Any `ℝ`-linearly independent `r`-tuple in `dualLat L` of norm `≤ R` directly bounds
`muMax L ≤ Real.log R` (core ingredient for `ClassMapMuMax`). -/
theorem muMax_le_log_of_dual_short_basis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {R : ℝ} (hR : 0 < R)
    (y : Fin (rk L) → E)
    (hyD : ∀ i, y i ∈ dualLat L)
    (hyli : LinearIndependent ℝ y)
    (hyR : ∀ i, ‖y i‖ ≤ R) :
    ArakelovCovolume.muMax L ≤ Real.log R := by
  have := discreteTopology_dualLat L
  have hr : 0 < rk L := rk_pos_of_ne_bot L hL0
  have hrD : 0 < rk (dualLat L) := by rw [rk_dualLat L]; exact hr
  let ilast : Fin (rk (dualLat L)) := ⟨rk (dualLat L) - 1, Nat.sub_lt hrD zero_lt_one⟩
  let emb : Fin (ilast.1 + 1) → Fin (rk L) := fun i =>
    ⟨i.1, by have hi := i.2; have hk : rk (dualLat L) = rk L := rk_dualLat L; omega⟩
  have hemb_inj : Function.Injective emb := fun a b hab =>
    Fin.ext (by simpa [emb] using congrArg Fin.val hab)
  have hsucc_le : succMin (dualLat L) ilast ≤ R := by
    unfold succMin
    refine csInf_le ⟨0, fun _ ht => ht.1⟩ ?_
    exact ⟨hR.le, fun i => y (emb i), fun i => hyD _, hyli.comp emb hemb_inj, fun i => hyR _⟩
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    omega
  have hpos : 0 < succMin (dualLat L) ilast := succMin_pos (dualLat L) hDL0 ilast
  have hmu := (banaszczyk_muMax_via_dual_lambda1 L hL0).2.2.2.2
  exact hmu.trans (Real.log_le_log hpos hsucc_le)

/-- Normalized `NumberFieldHLat` version of `banaszczyk_muMax_via_dual_lambda1`:
`A.muMax ≤ A.mu - 2 * log (λ₁(A) * λ₁(A*)) + 2 * log ([K : ℚ] * card A.ι)`. -/
theorem banaszczyk_numberFieldHLat_muMax_via_dual_lambda1
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι] :
    letI := discreteTopology_dualLat A.zRealize
    let r := Module.finrank ℚ K * Fintype.card A.ι
    A.muMax ≤ A.mu - 2 * Real.log (lambda1 A.zRealize * lambda1 (dualLat A.zRealize)) +
      2 * Real.log (r : ℝ) ∧
    A.muMax - A.muMin ≤ -2 * Real.log (lambda1 A.zRealize * lambda1 (dualLat A.zRealize)) +
      2 * Real.log (r : ℝ) := by
  have := discreteTopology_dualLat A.zRealize
  have h := banaszczyk_muMax_via_dual_lambda1 A.zRealize (zRealize_ne_bot A)
  have h1 := h.1
  have h2 := h.2.1
  rw [rk_zRealize_eq A] at h1 h2
  unfold NumberFieldHLat.muMax NumberFieldHLat.mu NumberFieldHLat.muMin
  constructor <;> linarith

end BanaszczykMuMaxViaDualLambda1

/-! ## Section 5: `banaszczyk_hh_gap_le` (Ready for `ClassMapMuMax` & `RamifiedJointBost`) -/

section BanaszczykHHGapLe

/-- **Unconditional Banaszczyk `O(log r)` Arakelov Gap Bound (`banaszczyk_hh_gap_le`)**:
for ANY nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`) and ANY ceiling `HH : ℝ` satisfying
`-Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (rk L : ℝ) ≤ HH`:
1. `muMax L - muMin L ≤ HH` (`O(log r)`, exponentially beating LLL's `O(r)` and Minkowski's `O(r log r)`),
2. `muMax L - ArakelovCovolume.slope L ≤ HH`,
3. `ArakelovCovolume.slope L - muMin L ≤ HH`! -/
theorem banaszczyk_hh_gap_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {HH : ℝ}
    (hHH : -Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (rk L : ℝ) ≤ HH) :
    letI := discreteTopology_dualLat L
    ArakelovCovolume.muMax L - muMin L ≤ HH ∧
    ArakelovCovolume.muMax L - ArakelovCovolume.slope L ≤ HH ∧
    ArakelovCovolume.slope L - muMin L ≤ HH := by
  have := discreteTopology_dualLat L
  have hgap := (banaszczyk_muMax_via_dual_lambda1 L hL0).2.1
  have hsand := muMin_le_slope_le_muMax L hL0
  exact ⟨hgap.trans hHH, by linarith, by linarith⟩

/-- Specialized `banaszczyk_hh_gap_le` when `c ≤ lambda1 L * lambda1 (dualLat L)` (`0 < c`):
all three gaps (`muMax - muMin`, `muMax - slope`, `slope - muMin`) are `≤ log (rk L) - log c`! -/
theorem banaszczyk_hh_gap_le_of_lambda_prod
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {c : ℝ} (hc : 0 < c) (hprod : c ≤ lambda1 L * lambda1 (dualLat L)) :
    letI := discreteTopology_dualLat L
    ArakelovCovolume.muMax L - muMin L ≤ Real.log (rk L : ℝ) - Real.log c ∧
    ArakelovCovolume.muMax L - ArakelovCovolume.slope L ≤ Real.log (rk L : ℝ) - Real.log c ∧
    ArakelovCovolume.slope L - muMin L ≤ Real.log (rk L : ℝ) - Real.log c := by
  have := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    rw [h0, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  have hlog : Real.log c ≤ Real.log (lambda1 L * lambda1 (dualLat L)) :=
    Real.log_le_log hc hprod
  exact banaszczyk_hh_gap_le L hL0 (by linarith)

/-- **Banaszczyk Bost-Frame Family `HH` Ceiling Bound (`banaszczyk_hh_gap_le_of_family`)**:
direct `M2` Wave 2 bridge to `Stage12BanaszczykTransference.hhBanaszczyk` and
`Stage2ThetaWire.Stage2GramFrameFiber` (`RamifiedJointBost`!). -/
theorem banaszczyk_hh_gap_le_of_family
    {EN ECC : Type*} [NormedAddCommGroup EN] [InnerProductSpace ℝ EN] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup ECC] [InnerProductSpace ℝ ECC] [FiniteDimensional ℝ ECC]
    {W : Type*} [Fintype W] [Nonempty W]
    (latN : W → Submodule ℤ EN) [∀ u, DiscreteTopology (latN u)] (hN0 : ∀ u, latN u ≠ ⊥)
    (latCC : Submodule ℤ ECC) [DiscreteTopology latCC] (hCC0 : latCC ≠ ⊥)
    (ιCC : ∀ u : W, latN u →ₗ[ℤ] latCC) (hι_inj : ∀ u, Function.Injective (ιCC u))
    (cCC d h : W → ℝ) (hd : ∀ u, 0 < d u)
    (hι_norm : ∀ u (x : latN u), ‖((ιCC u x : latCC) : ECC)‖ ≤ Real.exp (cCC u) * ‖(x : EN)‖)
    {x cHH eps : ℝ} (hx1 : 1 < x) (hcHH : 0 ≤ cHH) (heps : 0 < eps)
    (hgap_le : -Real.log (lambda1 latCC * lambda1 (dualLat latCC)) + Real.log (rk latCC : ℝ) +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) ≤ x ^ cHH * Real.exp (x ^ eps)) :
    let HH := hhBanaszczyk latCC d cCC h
    RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) -
        muMin latCC ≤ HH ∧
    0 < HH ∧
    HH ≤ x ^ cHH * Real.exp (x ^ eps) :=
  hhBound_of_banaszczyk_transference latN hN0 latCC hCC0 ιCC hι_inj cCC d h hd hι_norm
    hx1 hcHH heps hgap_le

/-- Normalized `NumberFieldHLat` version of `banaszczyk_hh_gap_le`:
`A.muMax - A.muMin ≤ HH` whenever `-2 * log (λ₁(A) * λ₁(A*)) + 2 * log ([K : ℚ] * card A.ι) ≤ HH`. -/
theorem banaszczyk_numberFieldHLat_hh_gap_le
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι]
    {HH : ℝ}
    (hHH : -2 * Real.log (lambda1 A.zRealize * lambda1 (dualLat A.zRealize)) +
      2 * Real.log ((Module.finrank ℚ K * Fintype.card A.ι : ℕ) : ℝ) ≤ HH) :
    letI := discreteTopology_dualLat A.zRealize
    A.muMax - A.muMin ≤ HH ∧
    A.muMax - A.mu ≤ HH ∧
    A.mu - A.muMin ≤ HH := by
  have := discreteTopology_dualLat A.zRealize
  have h1 := (banaszczyk_numberFieldHLat_muMax_via_dual_lambda1 A).2
  have hsand := A.muMin_le_mu_le_muMax (zRealize_ne_bot A)
  exact ⟨h1.trans hHH, by linarith, by linarith⟩

end BanaszczykHHGapLe

end RHDirect.Stage14M2_BanaszczykShortBasis

end
