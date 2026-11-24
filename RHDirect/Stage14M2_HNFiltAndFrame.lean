import RHDirect.ArakelovCovolume
import RHDirect.Stage4ArakelovBost
import RHDirect.Stage11ArakelovFaltings
import RHDirect.Stage12SchurWeylLattices
import RHDirect.LatticeFrame
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# RHDirect.Stage14M2_HNFiltAndFrame

Field-2 Package M2 (Wave 1, Module 2 of 6): **Canonical Harder–Narasimhan Filtration on
Hermitian Lattices, Concave HN Polygon, Place-Splitting Twist Invariance, Layer-Cake
Integration, and Sharp Bost Frame-Slope Inequality (`FrameHerm`, `FrameHermSharp`,
`TheoremFSharp`)** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`, zero `opaque`.

## Contents

1. **`R`-Module Euclidean Lattices, Real Saturation, Supermodularity & Slope Characterization**:
   - Realized `ℤ`-lattice `zl ρ N`, lattice predicate `IsLat ρ L`, rank `rk ρ N`, Arakelov degree
     `deg ρ N`, slope `slope ρ N`, saturation `IsSat ρ L N`, extremal slopes `muMax ρ L` and
     `muMin ρ L`.
   - Real saturation for arbitrary rings `R` (`exists_real_saturation`): the `ℤ`-saturation of any
     `R`-submodule `N ≤ L` is automatically an `R`-submodule.
   - Grayson–Stuhler supermodularity (`deg_supermodular`), finiteness-driven maximal slope ratio
     (`exists_max_slope_ratio`), and complete slope characterization (`muMax_le_iff`, `le_muMin_iff`,
     `exists_isSat_slope_eq_muMax`, `muMin_le_slope_le_muMax`).

2. **Concrete Canonical Harder–Narasimhan Filtration `HLatHNFilt`, `hnSlopeList`, & `hnPoly_concave`**:
   - Threshold truncation `hnStep ρ L θ` and full specification `hnStep_spec`.
   - Concrete Harder–Narasimhan filtration `HLatHNFilt ρ L`, constructive existence
     `exists_hlatHNFilt` / `canonicalHLatHNFilt`, and exact identification
     `hnStep_eq_step_truncIdx`.
   - Descending slope vector `hnSlopeList ρ L`, antitone property, exact tail count
     `card_hnSlopeList_ge` / `card_hnSlopeList_lt`, sum identity `sum_hnSlopeList`, and extremal
     attainment `hnSlopeList_bounds` / `hnSlopeList_extremes`.
   - Concave HN polygon `hnPoly ρ L`, **`hnPoly_concave`**, upper envelope `deg_le_hnPoly`,
     vertex attainment `deg_hnStep_eq_hnPoly`, plus canonical bridges to
     `Stage11ArakelovFaltings.HermVectorBundle` and `Stage12SchurWeylLattices.NumberFieldHLat`.

3. **General Bost Morphism Slope Inequality & Shift Invariance**:
   - **`bost_slope_ineq_general`**: for every `R`-linear map `φ : L →ₗ[R] M` with
     `‖ρ' (φ x)‖ ≤ C * ‖ρ x‖` (`C > 0`), `φ ≠ 0 → muMin L - log C ≤ muMin (range φ) ∧
     muMin L ≤ muMax M + log C`, and `Injective φ → muMax L ≤ muMax M + log C`.
   - **`bost_hnStep_inclusion`** and **`shift_invariance`**.

4. **Totally Complex Number-Field Hermitian Lattices — Place Splitting, Twist Invariance &
   Mean Slope Inequality**:
   - Normalized invariants `nPl`, `logDisc`, `rkK`, `slopeNormalisingConstant`, `muDef`, `muMaxDef`,
     `muMinDef`, `opNormAt`, `htMap` grounded on `Stage12SchurWeylLattices.realizeHLat`.
   - **`place_lattice_structure`**, **`finrank_span_complex`**, **`gram_block_det_rescale`**,
     **`rescale_covolume_formula`**, **`twist_invariance`**, and **`slope_inequality_mean`**.

5. **Layer-Cake Integration, `FrameHerm`, `FrameHermSharp`, `TheoremFSharp` &
   `frame_herm_sharp_slope_ineq`**:
   - **`frameB_layer_cake_integral`**, `frameB_corank_share`, `frameB_count_lt`, `frameB_sum_sl`,
     and `thmF_place_corank` (reusing `RHDirect.LatticeFrame.frame_corank_density_bound`).
   - Unconditional proofs of **`TheoremFSharp`** (`theoremFSharp_holds`), **`TheoremF`**
     (`theoremF_holds`), **`FrameHermSharp`** (**`frame_herm_sharp_slope_ineq`**), **`FrameHerm`**
     (`frame_herm_slope_ineq`), and the direct bridge to `RHDirect.BostSlopeFiber.SlopeIneq`.
-/

open Module Submodule Finset Real Matrix MeasureTheory NumberField
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHDirect.Stage14M2_HNFiltAndFrame

open RHDirect.ArakelovCovolume (discreteTopology_of_le covol_eq_sqrt_det_gram
  finrank_int_eq_finrank_real_span linearIndependent_coe_basis covol_pos rk_pos_of_ne_bot
  covol_bot degAr_bot covol_le_of_le_same_rank gram_det_le norm_sum_smul_le_of_int
  bost_degree_inequality)
open RHDirect.Stage4ArakelovBost (IsSaturated saturation projOrth quotLat
  projOrth_mem_orthogonal sub_projOrth_mem_span projOrth_eq_zero_iff norm_projOrth_le
  projOrth_comp_of_le quotLat_exact_additivity discreteTopology_quotLat rk_add_quotLat
  covol_eq_mul_quotLat degAr_eq_add_quotLat isSaturated_bot isSaturated_self
  isSaturated_saturation saturation_le le_saturation rk_saturation covol_saturation_le
  eq_of_isSaturated_of_rk_eq finite_saturated_covol_le)
open RHDirect.Stage12SchurWeylLattices (vecAt fcoord normAt realizeHLat norm_sq_realizeHLat
  NumberFieldHLat)
open RHDirect.LatticeFrame (opFrameK opFrameQ opHsSq frame_corank_density_bound
  corank_share_bound layer_cake_bound integral_four_u_div)

/-! ## Section 1: `R`-Module Euclidean Lattices, Real Saturation, Supermodularity & Slope Characterization -/

section RModuleLattices

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Underlying realized `ℤ`-submodule `ρ(N) ⊂ E` of an `R`-submodule `N ≤ V`. -/
def zl (ρ : V →+ E) (N : Submodule R V) : Submodule ℤ E :=
  (N.restrictScalars ℤ).map ρ.toIntLinearMap

/-- Lattice predicate: `ρ` is injective on `L` and `ρ(L) ⊂ E` is discrete. -/
def IsLat (ρ : V →+ E) (L : Submodule R V) : Prop :=
  Set.InjOn ρ (L : Set V) ∧ DiscreteTopology (zl ρ L)

/-- Lattice rank `rk ρ N = rank_ℤ(ρ(N))`. -/
def rk (ρ : V →+ E) (N : Submodule R V) : ℕ :=
  RHDirect.ArakelovCovolume.rk (zl ρ N)

/-- Arakelov degree `deg ρ N = -log covol(ρ(N))`. -/
def deg (ρ : V →+ E) (N : Submodule R V) : ℝ :=
  RHDirect.ArakelovCovolume.degAr (zl ρ N)

/-- Arithmetic slope `slope ρ N = deg ρ N / rk ρ N`. -/
def slope (ρ : V →+ E) (N : Submodule R V) : ℝ :=
  RHDirect.ArakelovCovolume.slope (zl ρ N)

/-- `N` is saturated inside `L` relative to `ρ`. -/
def IsSat (ρ : V →+ E) (L N : Submodule R V) : Prop :=
  N ≤ L ∧ IsSaturated (zl ρ L) (zl ρ N)

/-- Maximal slope over nonzero `R`-submodules `N ≤ L`. -/
def muMax (ρ : V →+ E) (L : Submodule R V) : ℝ :=
  sSup {t : ℝ | ∃ N : Submodule R V, N ≤ L ∧ N ≠ ⊥ ∧ slope ρ N = t}

/-- Minimal slope over proper saturated `R`-submodules `N ⊂ L`. -/
def muMin (ρ : V →+ E) (L : Submodule R V) : ℝ :=
  sInf {t : ℝ | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧
    RHDirect.ArakelovCovolume.slope (quotLat (zl ρ L) (zl ρ N)) = t}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma mem_zl_iff (ρ : V →+ E) (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := by
  simp [zl]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma zl_mono (ρ : V →+ E) {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma zl_bot (ρ : V →+ E) : zl ρ (⊥ : Submodule R V) = ⊥ := by
  ext y
  simp [mem_zl_iff, eq_comm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma zl_sup (ρ : V →+ E) (A B : Submodule R V) :
    zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  ext y
  simp only [mem_zl_iff, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨ρ a, ⟨a, ha, rfl⟩, ρ b, ⟨b, hb, rfl⟩, (map_add ρ a b).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add ρ a b⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma zl_inf_of_injOn (ρ : V →+ E) {L A B : Submodule R V}
    (hinj : Set.InjOn ρ (L : Set V)) (hA : A ≤ L) (hB : B ≤ L) :
    zl ρ (A ⊓ B) = zl ρ A ⊓ zl ρ B := by
  apply le_antisymm
  · exact le_inf (zl_mono ρ inf_le_left) (zl_mono ρ inf_le_right)
  · rintro y ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx₂eq⟩⟩
    have h12 : x₁ = x₂ := hinj (hA hx₁) (hB hx₂) hx₂eq.symm
    subst h12
    exact ⟨x₁, ⟨hx₁, hx₂⟩, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma le_of_zl_le (ρ : V →+ E) {L A B : Submodule R V}
    (hinj : Set.InjOn ρ (L : Set V)) (hA : A ≤ L) (hB : B ≤ L) (h : zl ρ A ≤ zl ρ B) :
    A ≤ B := by
  intro x hx
  have hx' : ρ x ∈ zl ρ B := h ⟨x, hx, rfl⟩
  rcases hx' with ⟨y, hy, hyx⟩
  have hxy : y = x := hinj (hB hy) (hA hx) hyx
  rwa [← hxy]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isLat_of_le (ρ : V →+ E) {L N : Submodule R V} (hL : IsLat ρ L) (hNL : N ≤ L) :
    IsLat ρ N := by
  have : DiscreteTopology (zl ρ L) := hL.2
  exact ⟨hL.1.mono (fun _ hx => hNL hx), discreteTopology_of_le (zl_mono ρ hNL)⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma rk_bot (ρ : V →+ E) : rk ρ (⊥ : Submodule R V) = 0 := by
  unfold rk
  rw [zl_bot]
  simp [RHDirect.ArakelovCovolume.rk]

lemma deg_bot (ρ : V →+ E) : deg ρ (⊥ : Submodule R V) = 0 := by
  unfold deg
  rw [zl_bot]
  exact degAr_bot

omit [FiniteDimensional ℝ E] in
lemma isSat_bot (ρ : V →+ E) (L : Submodule R V) : IsSat ρ L ⊥ := by
  refine ⟨bot_le, ?_⟩
  rw [zl_bot]
  exact isSaturated_bot (zl ρ L)

omit [FiniteDimensional ℝ E] in
lemma isSat_self (ρ : V →+ E) (L : Submodule R V) : IsSat ρ L L :=
  ⟨le_rfl, isSaturated_self (zl ρ L)⟩

lemma rk_mono (ρ : V →+ E) {L A B : Submodule R V} (hL : IsLat ρ L)
    (hAB : A ≤ B) (hBL : B ≤ L) : rk ρ A ≤ rk ρ B := by
  have : DiscreteTopology (zl ρ B) := (isLat_of_le ρ hL hBL).2
  have : DiscreteTopology (zl ρ A) := (isLat_of_le ρ hL (hAB.trans hBL)).2
  unfold rk RHDirect.ArakelovCovolume.rk
  rw [finrank_int_eq_finrank_real_span (zl ρ A), finrank_int_eq_finrank_real_span (zl ρ B)]
  exact Submodule.finrank_mono
    (Submodule.span_mono (show (zl ρ A : Set E) ⊆ zl ρ B from zl_mono ρ hAB))

lemma deg_mono_of_rk_eq (ρ : V →+ E) {L A B : Submodule R V} (hL : IsLat ρ L)
    (hAB : A ≤ B) (hBL : B ≤ L) (hrk : rk ρ A = rk ρ B) : deg ρ A ≤ deg ρ B := by
  have : DiscreteTopology (zl ρ B) := (isLat_of_le ρ hL hBL).2
  exact (covol_le_of_le_same_rank (L := zl ρ B) (M := zl ρ A) (zl_mono ρ hAB) hrk).2

lemma rk_eq_zero_iff (ρ : V →+ E) {L N : Submodule R V} (hL : IsLat ρ L) (hNL : N ≤ L) :
    rk ρ N = 0 ↔ N = ⊥ := by
  have : DiscreteTopology (zl ρ N) := (isLat_of_le ρ hL hNL).2
  constructor
  · intro h0
    have hz : zl ρ N = ⊥ := by
      by_contra hne
      have hpos := rk_pos_of_ne_bot (zl ρ N) hne
      exact absurd h0 hpos.ne'
    rw [eq_bot_iff]
    intro x hx
    have hrx : ρ x = 0 := by
      have hm : ρ x ∈ zl ρ N := ⟨x, hx, rfl⟩
      rwa [hz, Submodule.mem_bot] at hm
    rw [Submodule.mem_bot]
    exact hL.1 (hNL hx) L.zero_mem (by rw [hrx, map_zero])
  · rintro rfl
    exact rk_bot ρ

lemma rk_pos_of_ne_bot' (ρ : V →+ E) {L N : Submodule R V} (hL : IsLat ρ L)
    (hNL : N ≤ L) (hN0 : N ≠ ⊥) : 0 < rk ρ N :=
  Nat.pos_of_ne_zero fun h0 => hN0 ((rk_eq_zero_iff ρ hL hNL).mp h0)

lemma eq_of_isSat_of_rk_eq (ρ : V →+ E) {L S N : Submodule R V} (hL : IsLat ρ L)
    (hS : IsSat ρ L S) (hSN : S ≤ N) (hNL : N ≤ L) (hrk : rk ρ S = rk ρ N) :
    S = N := by
  have : DiscreteTopology (zl ρ L) := hL.2
  have hzeq : zl ρ S = zl ρ N :=
    eq_of_isSaturated_of_rk_eq hS.2 (zl_mono ρ hNL) (zl_mono ρ hSN) hrk
  exact le_antisymm hSN (le_of_zl_le ρ hL.1 hNL hS.1 hzeq.ge)

lemma rk_lt_of_isSat_lt (ρ : V →+ E) {L S N : Submodule R V} (hL : IsLat ρ L)
    (hS : IsSat ρ L S) (hSN : S < N) (hNL : N ≤ L) : rk ρ S < rk ρ N := by
  have hle := rk_mono ρ hL hSN.le hNL
  exact lt_of_le_of_ne hle fun he => hSN.ne (eq_of_isSat_of_rk_eq ρ hL hS hSN.le hNL he)

lemma quot_invariants (ρ : V →+ E) {L S : Submodule R V} (hL : IsLat ρ L) (hS : IsSat ρ L S) :
    DiscreteTopology (quotLat (zl ρ L) (zl ρ S)) ∧
    RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ S)) = rk ρ L - rk ρ S ∧
    rk ρ S ≤ rk ρ L ∧
    RHDirect.ArakelovCovolume.degAr (quotLat (zl ρ L) (zl ρ S)) = deg ρ L - deg ρ S := by
  have : DiscreteTopology (zl ρ L) := hL.2
  obtain ⟨hD, hrk, _, hdeg⟩ := quotLat_exact_additivity hS.2
  refine ⟨hD, ?_, ?_, ?_⟩
  · change RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ S)) =
      RHDirect.ArakelovCovolume.rk (zl ρ L) - RHDirect.ArakelovCovolume.rk (zl ρ S)
    omega
  · change RHDirect.ArakelovCovolume.rk (zl ρ S) ≤ RHDirect.ArakelovCovolume.rk (zl ρ L)
    omega
  · unfold deg; linarith

/-- Any equal-rank sublattice `S ≤ M` of a discrete Euclidean `ℤ`-lattice `M` has a positive
integer annihilator `d > 0` with `∀ x ∈ M, d • x ∈ S`. -/
lemma exists_pos_nsmul_mem_of_rk_eq {M S : Submodule ℤ E} [DiscreteTopology M]
    (hSM : S ≤ M) (hrk : RHDirect.ArakelovCovolume.rk S = RHDirect.ArakelovCovolume.rk M) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ M, d • x ∈ S := by
  have : DiscreteTopology S := discreteTopology_of_le hSM
  let r := RHDirect.ArakelovCovolume.rk M
  let bM : Basis (Fin r) ℤ M := Module.finBasis ℤ M
  let bS : Basis (Fin r) ℤ S :=
    (Module.finBasis ℤ S).reindex (Fintype.equivOfCardEq (by simp only [Fintype.card_fin]; exact hrk))
  let A : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => bM.repr ⟨(bS j : E), hSM (bS j).2⟩ i
  have hA_col : ∀ j : Fin r, (bS j : E) = ∑ i : Fin r, (A i j : ℝ) • (bM i : E) := by
    intro j
    have h1 := congrArg Subtype.val (bM.sum_repr ⟨(bS j : E), hSM (bS j).2⟩)
    rw [Submodule.coe_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [A, Int.cast_smul_eq_zsmul]
  have hdet_ne : A.det ≠ 0 := by
    intro h0
    have hdetR : (A.map (Int.castRingHom ℝ)).det = 0 := by
      have hmap := ((Int.castRingHom ℝ).map_det A).symm
      rw [h0, map_zero] at hmap
      simpa [RingHom.mapMatrix_apply] using hmap
    obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetR
    have hlin : ∑ j : Fin r, v j • (bS j : E) = 0 := by
      simp_rw [hA_col, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv0 i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom,
        Pi.zero_apply] at hi
      have hsum : ∑ j : Fin r, v j • (A i j : ℝ) • (bM i : E) =
          (∑ j : Fin r, (A i j : ℝ) * v j) • (bM i : E) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, mul_comm]
      rw [hsum, hi, zero_smul]
    have hv_zero : v = 0 := funext fun j =>
      Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis S bS) v hlin j
    exact hv_ne hv_zero
  let d : ℕ := A.det.natAbs
  have hd_pos : 0 < d := Int.natAbs_pos.mpr hdet_ne
  refine ⟨d, hd_pos, fun x hxM => ?_⟩
  have hmul : A * A.adjugate = A.det • (1 : Matrix (Fin r) (Fin r) ℤ) := Matrix.mul_adjugate A
  have hbasis_mem : ∀ k : Fin r, A.det • (bM k : E) ∈ S := by
    intro k
    have heq : ∑ j : Fin r, A.adjugate j k • (bS j : E) = A.det • (bM k : E) := by
      have h1 : ∀ j : Fin r, (bS j : E) = ∑ i : Fin r, A i j • (bM i : E) := by
        intro j
        have h := hA_col j
        simpa only [Int.cast_smul_eq_zsmul] using h
      simp_rw [h1, Finset.smul_sum]
      rw [Finset.sum_comm]
      calc ∑ i : Fin r, ∑ j : Fin r, A.adjugate j k • A i j • (bM i : E)
          = ∑ i : Fin r, (∑ j : Fin r, A i j * A.adjugate j k) • (bM i : E) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, mul_comm]
        _ = ∑ i : Fin r, (A * A.adjugate) i k • (bM i : E) := rfl
        _ = ∑ i : Fin r, (A.det • (1 : Matrix (Fin r) (Fin r) ℤ)) i k • (bM i : E) := by rw [hmul]
        _ = A.det • (bM k : E) := by
            rw [Finset.sum_eq_single k]
            · simp
            · intro i _ hik; simp [Matrix.one_apply_ne hik]
            · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [← heq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bS j).2
  have hx_det : A.det • x ∈ S := by
    have h1 := congrArg Subtype.val (bM.sum_repr ⟨x, hxM⟩)
    rw [Submodule.coe_sum] at h1
    change _ = x at h1
    rw [← h1, smul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul, smul_comm]
    exact Submodule.smul_mem _ _ (hbasis_mem k)
  rcases Int.natAbs_eq A.det with hpos | hneg
  · have : (d : ℤ) • x ∈ S := by rwa [← hpos]
    simpa only [natCast_zsmul] using this
  · have h1 : -((d : ℤ) • x) ∈ S := by
      rw [← neg_smul]; change (-(A.det.natAbs : ℤ)) • x ∈ S; rw [← hneg]; exact hx_det
    have h2 : (d : ℤ) • x ∈ S := by simpa using S.neg_mem h1
    simpa only [natCast_zsmul] using h2

/-- **Real Saturation for Arbitrary Rings `R`**: for any `R`-submodule `N ≤ L` with `IsLat ρ L`,
the `ℤ`-saturation `saturation (zl ρ L) (zl ρ N)` is the `ρ`-image of a saturated `R`-submodule
`N' ≤ L` containing `N`. -/
theorem exists_real_saturation (ρ : V →+ E) {L N : Submodule R V}
    (hL : IsLat ρ L) (hNL : N ≤ L) :
    ∃ N' : Submodule R V, N ≤ N' ∧ N' ≤ L ∧ zl ρ N' = saturation (zl ρ L) (zl ρ N) := by
  have : DiscreteTopology (zl ρ L) := hL.2
  let S : Submodule ℤ E := saturation (zl ρ L) (zl ρ N)
  have hSL : S ≤ zl ρ L := saturation_le _ _
  have : DiscreteTopology S := discreteTopology_of_le hSL
  have hNS : zl ρ N ≤ S := le_saturation (zl_mono ρ hNL)
  have hrk : RHDirect.ArakelovCovolume.rk (zl ρ N) = RHDirect.ArakelovCovolume.rk S :=
    (rk_saturation (zl_mono ρ hNL)).symm
  obtain ⟨d, hd_pos, hd_mem⟩ := exists_pos_nsmul_mem_of_rk_eq hNS hrk
  let N' : Submodule R V :=
    { carrier := {x : V | x ∈ L ∧ ρ x ∈ S}
      zero_mem' := ⟨L.zero_mem, by rw [map_zero]; exact S.zero_mem⟩
      add_mem' := fun {x y} hx hy =>
        ⟨L.add_mem hx.1 hy.1, by rw [map_add]; exact S.add_mem hx.2 hy.2⟩
      smul_mem' := fun r {x} hx => by
        refine ⟨L.smul_mem r hx.1, ?_⟩
        have hdxS : d • ρ x ∈ zl ρ N := hd_mem (ρ x) hx.2
        rcases (mem_zl_iff ρ N _).mp hdxS with ⟨y, hyN, hyx⟩
        have hdx_eq : y = d • x := hL.1 (hNL hyN) (L.nsmul_mem hx.1 d) (by rw [hyx, map_nsmul])
        have hdxN : d • x ∈ N := hdx_eq ▸ hyN
        have hdrxN : d • (r • x) ∈ N := by
          have : d • (r • x) = r • (d • x) := by
            rw [← Nat.cast_smul_eq_nsmul R d (r • x), ← Nat.cast_smul_eq_nsmul R d x,
              smul_smul, smul_smul, Nat.cast_comm]
          rw [this]
          exact N.smul_mem r hdxN
        have hmem_span : ρ (r • x) ∈ Submodule.span ℝ ((zl ρ N : Submodule ℤ E) : Set E) := by
          have h1 : (d : ℝ) • ρ (r • x) ∈ Submodule.span ℝ ((zl ρ N : Submodule ℤ E) : Set E) := by
            have h2 : ρ (d • (r • x)) ∈ zl ρ N := ⟨d • (r • x), hdrxN, rfl⟩
            rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
            exact Submodule.subset_span h2
          have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
          have h3 := Submodule.smul_mem _ (d : ℝ)⁻¹ h1
          rwa [inv_smul_smul₀ hdR] at h3
        exact ⟨⟨r • x, L.smul_mem r hx.1, rfl⟩, hmem_span⟩ }
  refine ⟨N', fun x hx => ⟨hNL hx, hNS ⟨x, hx, rfl⟩⟩, fun _ hx => hx.1, ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hyS
    rcases hSL hyS with ⟨x, hxL, rfl⟩
    exact ⟨x, ⟨hxL, hyS⟩, rfl⟩

/-- Exact covolume-index formula for equal-rank `ℤ`-sublattices `N ≤ N'`. -/
lemma covol_eq_relIndex_mul_covol (N N' : Submodule ℤ E) [DiscreteTopology N']
    (hle : N ≤ N') (hrk : RHDirect.ArakelovCovolume.rk N = RHDirect.ArakelovCovolume.rk N') :
    RHDirect.ArakelovCovolume.covol N =
      (N.toAddSubgroup.relIndex N'.toAddSubgroup : ℝ) * RHDirect.ArakelovCovolume.covol N' := by
  classical
  have : DiscreteTopology N := discreteTopology_of_le hle
  let K : Submodule ℤ N' := N.comap N'.subtype
  let eK : K ≃ₗ[ℤ] N := Submodule.comapSubtypeEquivOfLe hle
  have hK : Module.finrank ℤ K = Module.finrank ℤ N' := by
    rw [eK.finrank_eq]; exact hrk
  let b : Basis (Fin (Module.finrank ℤ N')) ℤ N' := Module.finBasis ℤ N'
  let bK : Basis (Fin (Module.finrank ℤ N')) ℤ K := Module.finBasisOfFinrankEq ℤ K hK
  let A : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℤ :=
    Matrix.of fun i j => b.repr (bK j : N') i
  let Ar : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℝ :=
    Matrix.of fun i j => ((b.repr (bK j : N') i : ℤ) : ℝ)
  have hidx : N.toAddSubgroup.relIndex N'.toAddSubgroup = (b.det (Subtype.val ∘ bK)).natAbs := by
    rw [Submodule.natAbs_det_basis_change b K bK]
    rfl
  let v : Fin (Module.finrank ℤ N') → E := fun i => (b i : E)
  let w : Fin (Module.finrank ℤ N') → E := fun i => ((bK i : N') : E)
  have hw : ∀ j, w j = ∑ i, Ar i j • v i := by
    intro j
    have h := congrArg (fun x : N' => (x : E)) (b.sum_repr (bK j : N'))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    show ((bK j : N') : E) = _
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Ar, v, Int.cast_smul_eq_zsmul]
  have hgram : Matrix.gram ℝ w = Ar.transpose * (Matrix.gram ℝ v * Ar) := by
    ext i j
    simp only [Matrix.gram_apply, hw, Matrix.mul_apply, Matrix.transpose_apply,
      inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hA : Ar.det = (A.det : ℝ) := by
    have := ((Int.castRingHom ℝ).map_det A).symm
    simpa [Ar, A, RingHom.mapMatrix_apply, Matrix.map] using this
  have hdet : (Matrix.gram ℝ w).det = (A.det : ℝ) ^ 2 * (Matrix.gram ℝ v).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hA]; ring
  have hcw : (fun i => ((bK.map eK) i : E)) = w := funext fun _ => rfl
  have hbd : b.det (Subtype.val ∘ bK) = A.det := by rw [Basis.det_apply]; rfl
  rw [covol_eq_sqrt_det_gram N (bK.map eK), covol_eq_sqrt_det_gram N' b, hcw, hdet, hidx,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, hbd]
  simp [Nat.cast_natAbs, Int.cast_abs]
  exact Or.inl rfl

/-- **General Grayson–Stuhler Supermodularity for Arbitrary `ℤ`-Sublattices `A, B ≤ L`**. -/
theorem degAr_supermodular_general {L A B : Submodule ℤ E} [DiscreteTopology L]
    (hA : A ≤ L) (hB : B ≤ L) :
    RHDirect.ArakelovCovolume.rk (A ⊔ B) + RHDirect.ArakelovCovolume.rk (A ⊓ B) =
      RHDirect.ArakelovCovolume.rk A + RHDirect.ArakelovCovolume.rk B ∧
    RHDirect.ArakelovCovolume.degAr A + RHDirect.ArakelovCovolume.degAr B ≤
      RHDirect.ArakelovCovolume.degAr (A ⊔ B) + RHDirect.ArakelovCovolume.degAr (A ⊓ B) := by
  have hSL : A ⊔ B ≤ L := sup_le hA hB
  have : DiscreteTopology (A ⊔ B : Submodule ℤ E) := discreteTopology_of_le hSL
  have : DiscreteTopology A := discreteTopology_of_le hA
  have : DiscreteTopology B := discreteTopology_of_le hB
  have : DiscreteTopology (A ⊓ B : Submodule ℤ E) := discreteTopology_of_le (inf_le_left.trans hA)
  let As : Submodule ℤ E := saturation (A ⊔ B) A
  let Bs : Submodule ℤ E := saturation B (A ⊓ B)
  have hAs_sat : IsSaturated (A ⊔ B) As := isSaturated_saturation le_sup_left
  have hBs_sat : IsSaturated B Bs := isSaturated_saturation inf_le_right
  have hAAs : A ≤ As := le_saturation le_sup_left
  have hCBs : A ⊓ B ≤ Bs := le_saturation inf_le_right
  have hrkAs : RHDirect.ArakelovCovolume.rk As = RHDirect.ArakelovCovolume.rk A :=
    rk_saturation le_sup_left
  have hrkBs : RHDirect.ArakelovCovolume.rk Bs = RHDirect.ArakelovCovolume.rk (A ⊓ B) :=
    rk_saturation inf_le_right
  have : DiscreteTopology As := discreteTopology_of_le (saturation_le _ _)
  have : DiscreteTopology Bs := discreteTopology_of_le (saturation_le _ _)
  have : DiscreteTopology (quotLat (A ⊔ B) As) := discreteTopology_quotLat hAs_sat
  have : DiscreteTopology (quotLat B Bs) := discreteTopology_quotLat hBs_sat
  have hBsAs : Bs ≤ As := fun x hx =>
    ⟨(le_sup_right : B ≤ A ⊔ B) hx.1,
      Submodule.span_mono (show ((A ⊓ B : Submodule ℤ E) : Set E) ⊆ A from inf_le_left) hx.2⟩
  -- Contraction isomorphism `quotLat B Bs ≃ₗ[ℤ] quotLat (A ⊔ B) As` via `projOrth As`
  have himg : ∀ y ∈ quotLat B Bs, projOrth As y ∈ quotLat (A ⊔ B) As := by
    rintro _ ⟨b, hbB, rfl⟩
    change projOrth As (projOrth Bs b) ∈ quotLat (A ⊔ B) As
    rw [projOrth_comp_of_le hBsAs b]
    exact ⟨b, (le_sup_right : B ≤ A ⊔ B) hbB, rfl⟩
  let g : quotLat B Bs →ₗ[ℤ] quotLat (A ⊔ B) As :=
    { toFun := fun y => ⟨projOrth As y.1, himg y.1 y.2⟩
      map_add' := fun x y => Subtype.ext (map_add (projOrth As) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul (projOrth As) c x.1) }
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h0 : projOrth As (x.1 - y.1) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg (fun z : quotLat (A ⊔ B) As => (z : E)) hxy)
    obtain ⟨b, hbB, hbeq⟩ := (quotLat B Bs).sub_mem x.2 y.2
    have hbeq' : projOrth Bs b = x.1 - y.1 := hbeq
    have hbAs : projOrth As b = 0 := by rw [← projOrth_comp_of_le hBsAs b, hbeq', h0]
    have hb_mem_As : b ∈ As :=
      hAs_sat.2 b ((le_sup_right : B ≤ A ⊔ B) hbB) ((projOrth_eq_zero_iff As b).mp hbAs)
    obtain ⟨d, hd_pos, hd_mem⟩ := exists_pos_nsmul_mem_of_rk_eq hAAs hrkAs.symm
    have hdb : d • b ∈ A ⊓ B := ⟨hd_mem b hb_mem_As, B.nsmul_mem hbB d⟩
    have hb_span : b ∈ Submodule.span ℝ ((Bs : Submodule ℤ E) : Set E) := by
      have h1 : (d : ℝ) • b ∈ Submodule.span ℝ ((Bs : Submodule ℤ E) : Set E) := by
        rw [Nat.cast_smul_eq_nsmul]
        exact Submodule.subset_span (hCBs hdb)
      have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
      have h2 := Submodule.smul_mem _ (d : ℝ)⁻¹ h1
      rwa [inv_smul_smul₀ hdR] at h2
    have hsub0 : x.1 - y.1 = 0 := by
      rw [← hbeq']
      exact (projOrth_eq_zero_iff Bs b).mpr hb_span
    exact sub_eq_zero.mp hsub0
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, s, hs, rfl⟩
    have hs' : s ∈ A ⊔ B := hs
    rw [Submodule.mem_sup] at hs'
    rcases hs' with ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨projOrth Bs b, ⟨b, hb, rfl⟩⟩, Subtype.ext ?_⟩
    change projOrth As (projOrth Bs b) = projOrth As (a + b)
    rw [projOrth_comp_of_le hBsAs b, map_add,
      (projOrth_eq_zero_iff As a).mpr (Submodule.subset_span (hAAs ha)), zero_add]
  let φ : quotLat B Bs ≃ₗ[ℤ] quotLat (A ⊔ B) As := LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hrkQ : RHDirect.ArakelovCovolume.rk (quotLat (A ⊔ B) As) =
      RHDirect.ArakelovCovolume.rk (quotLat B Bs) := φ.finrank_eq.symm
  have hrk_eq : RHDirect.ArakelovCovolume.rk (A ⊔ B) + RHDirect.ArakelovCovolume.rk (A ⊓ B) =
      RHDirect.ArakelovCovolume.rk A + RHDirect.ArakelovCovolume.rk B := by
    have h1 := rk_add_quotLat hAs_sat
    have h2 := rk_add_quotLat hBs_sat
    omega
  refine ⟨hrk_eq, ?_⟩
  -- Contraction on quotients: `covol (quotLat (A ⊔ B) As) ≤ covol (quotLat B Bs)`
  let bQ := Module.finBasis ℤ (quotLat B Bs)
  have hcovQ : RHDirect.ArakelovCovolume.covol (quotLat (A ⊔ B) As) ≤
      RHDirect.ArakelovCovolume.covol (quotLat B Bs) := by
    rw [covol_eq_sqrt_det_gram _ (bQ.map φ), covol_eq_sqrt_det_gram _ bQ]
    have hlip : ∀ c : Fin (Module.finrank ℤ (quotLat B Bs)) → ℝ,
        ‖∑ i, c i • ((bQ.map φ i : quotLat (A ⊔ B) As) : E)‖ ≤
          1 * ‖∑ i, c i • (bQ i : E)‖ := by
      intro c
      rw [one_mul]
      have heq : ∑ i, c i • ((bQ.map φ i : quotLat (A ⊔ B) As) : E) =
          projOrth As (∑ i, c i • (bQ i : E)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
      rw [heq]
      exact norm_projOrth_le As _
    have hdet := gram_det_le (fun i => (bQ i : E))
      (fun i => ((bQ.map φ i : quotLat (A ⊔ B) As) : E)) 1 hlip
    rw [one_pow, one_mul] at hdet
    exact Real.sqrt_le_sqrt hdet
  -- Index comparison: `[Bs : A ⊓ B] ≤ [As : A]`
  have hcA := covol_eq_relIndex_mul_covol A As hAAs hrkAs.symm
  have hcC := covol_eq_relIndex_mul_covol (A ⊓ B) Bs hCBs hrkBs.symm
  have hiA : A.toAddSubgroup.relIndex As.toAddSubgroup ≠ 0 := by
    intro h0
    have hpos := covol_pos A
    rw [hcA, h0] at hpos
    simp at hpos
  have hiC : (A ⊓ B).toAddSubgroup.relIndex Bs.toAddSubgroup =
      A.toAddSubgroup.relIndex Bs.toAddSubgroup := by
    unfold AddSubgroup.relIndex
    congr 1
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.1⟩⟩
  have hle_idx : (A ⊓ B).toAddSubgroup.relIndex Bs.toAddSubgroup ≤
      A.toAddSubgroup.relIndex As.toAddSubgroup := by
    rw [hiC]
    exact AddSubgroup.relIndex_le_of_le_right hBsAs hiA
  have hii : RHDirect.ArakelovCovolume.covol As * RHDirect.ArakelovCovolume.covol (A ⊓ B) ≤
      RHDirect.ArakelovCovolume.covol A * RHDirect.ArakelovCovolume.covol Bs := by
    rw [hcA, hcC]
    have h3 : ((A ⊓ B).toAddSubgroup.relIndex Bs.toAddSubgroup : ℝ) ≤
        (A.toAddSubgroup.relIndex As.toAddSubgroup : ℝ) := by exact_mod_cast hle_idx
    have h4 := mul_le_mul_of_nonneg_right h3 (mul_pos (covol_pos As) (covol_pos Bs)).le
    nlinarith
  have hlogQ := Real.log_le_log (covol_pos _) hcovQ
  have hlogI := Real.log_le_log (mul_pos (covol_pos _) (covol_pos _)) hii
  rw [Real.log_mul (covol_pos _).ne' (covol_pos _).ne',
    Real.log_mul (covol_pos _).ne' (covol_pos _).ne'] at hlogI
  have hdS := degAr_eq_add_quotLat hAs_sat
  have hdB := degAr_eq_add_quotLat hBs_sat
  unfold RHDirect.ArakelovCovolume.degAr at hdS hdB ⊢
  linarith

/-- **Grayson–Stuhler Supermodularity for `R`-Submodules**:
for any `A, B ≤ L` with `IsLat ρ L`,
`rk ρ (A ⊔ B) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B` and
`deg ρ A + deg ρ B ≤ deg ρ (A ⊔ B) + deg ρ (A ⊓ B)`. -/
theorem deg_supermodular (ρ : V →+ E) {L A B : Submodule R V}
    (hL : IsLat ρ L) (hA : A ≤ L) (hB : B ≤ L) :
    rk ρ (A ⊔ B) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B ∧
    deg ρ A + deg ρ B ≤ deg ρ (A ⊔ B) + deg ρ (A ⊓ B) := by
  have : DiscreteTopology (zl ρ L) := hL.2
  have h := degAr_supermodular_general (L := zl ρ L) (zl_mono ρ hA) (zl_mono ρ hB)
  unfold rk deg
  rw [zl_sup ρ A B, zl_inf_of_injOn ρ hL.1 hA hB]
  exact h

/-- **Maximal Slope Ratio above a Saturated Sublattice**:
for any proper saturated `S ⊂ L` (`IsLat ρ L`), there exists a saturated `N` (`S < N ≤ L`)
maximizing the incremental slope `(deg ρ N - deg ρ S) / (rk ρ N - rk ρ S)` over all
`M` with `S < M ≤ L`, and moreover of maximal rank among all such maximizers! -/
theorem exists_max_slope_ratio (ρ : V →+ E) {L S : Submodule R V}
    (hL : IsLat ρ L) (hS : IsSat ρ L S) (hSL : S ≠ L) :
    ∃ N : Submodule R V, S < N ∧ IsSat ρ L N ∧
      (∀ M : Submodule R V, S < M → M ≤ L →
        (deg ρ M - deg ρ S) / ((rk ρ M : ℝ) - rk ρ S) ≤
          (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S)) ∧
      (∀ M : Submodule R V, S < M → M ≤ L →
        (deg ρ M - deg ρ S) / ((rk ρ M : ℝ) - rk ρ S) =
          (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S) →
        rk ρ M ≤ rk ρ N) := by
  have : DiscreteTopology (zl ρ L) := hL.2
  let f : Submodule R V → ℝ := fun M => (deg ρ M - deg ρ S) / ((rk ρ M : ℝ) - rk ρ S)
  have hgap : ∀ M : Submodule R V, S < M → M ≤ L → (0 : ℝ) < (rk ρ M : ℝ) - rk ρ S := by
    intro M hSM hML
    have hlt := rk_lt_of_isSat_lt ρ hL hS hSM hML
    have : (rk ρ S : ℝ) < rk ρ M := by exact_mod_cast hlt
    linarith
  have hdeg_lb : ∀ M : Submodule R V, S < M → M ≤ L → f L ≤ f M →
      deg ρ S - |f L| * (rk ρ L : ℝ) ≤ deg ρ M := by
    intro M hSM hML hfm
    have hpos := hgap M hSM hML
    have hrM : (rk ρ M : ℝ) - rk ρ S ≤ rk ρ L := by
      have hle : (rk ρ M : ℝ) ≤ rk ρ L := by exact_mod_cast rk_mono ρ hL hML le_rfl
      linarith [Nat.cast_nonneg (α := ℝ) (rk ρ S)]
    have h1 : f L * ((rk ρ M : ℝ) - rk ρ S) ≤ deg ρ M - deg ρ S := (le_div_iff₀ hpos).mp hfm
    have h2 : -|f L| * (rk ρ L : ℝ) ≤ f L * ((rk ρ M : ℝ) - rk ρ S) :=
      (mul_le_mul_of_nonpos_left hrM (neg_nonpos.mpr (abs_nonneg _))).trans
        (mul_le_mul_of_nonneg_right (neg_abs_le _) hpos.le)
    linarith
  let T : Set (Submodule R V) := {M | IsSat ρ L M ∧ S < M ∧ f L ≤ f M}
  have hfinE := finite_saturated_covol_le (L := zl ρ L)
    (Real.exp (-(deg ρ S - |f L| * (rk ρ L : ℝ))))
  have hT_fin : T.Finite := by
    refine Set.Finite.of_finite_image (f := zl ρ) (hfinE.subset ?_) ?_
    · rintro _ ⟨M, ⟨hMsat, hSM, hfm⟩, rfl⟩
      refine ⟨hMsat.2, ?_⟩
      have : DiscreteTopology (zl ρ M) := (isLat_of_le ρ hL hMsat.1).2
      have hcpos := covol_pos (zl ρ M)
      have hd := hdeg_lb M hSM hMsat.1 hfm
      rw [← Real.log_le_iff_le_exp hcpos]
      unfold deg RHDirect.ArakelovCovolume.degAr at hd ⊢
      linarith
    · intro A hA B hB hAB
      exact le_antisymm
        (le_of_zl_le ρ hL.1 hA.1.1 hB.1.1 hAB.le)
        (le_of_zl_le ρ hL.1 hB.1.1 hA.1.1 hAB.ge)
  have hLT : L ∈ T := ⟨isSat_self ρ L, lt_of_le_of_ne hS.1 hSL, le_rfl⟩
  obtain ⟨N₀, hN₀T, hN₀max⟩ := Set.exists_max_image T f hT_fin ⟨L, hLT⟩
  let Tmax : Set (Submodule R V) := {M ∈ T | f M = f N₀}
  have hTmax_fin : Tmax.Finite := hT_fin.subset (fun _ h => h.1)
  have hN₀_mem : N₀ ∈ Tmax := ⟨hN₀T, rfl⟩
  obtain ⟨N, hNTmax, hNrk_max⟩ := Set.exists_max_image Tmax (rk ρ) hTmax_fin ⟨N₀, hN₀_mem⟩
  have hNsat : IsSat ρ L N := hNTmax.1.1
  have hSN : S < N := hNTmax.1.2.1
  have hfN : f N = f N₀ := hNTmax.2
  have hmax_all : ∀ M : Submodule R V, S < M → M ≤ L → f M ≤ f N := by
    intro M hSM hML
    obtain ⟨M', hMM', hM'L, hzl⟩ := exists_real_saturation ρ hL hML
    have hM'sat : IsSat ρ L M' := ⟨hM'L, hzl ▸ isSaturated_saturation (zl_mono ρ hML)⟩
    have hrk' : rk ρ M' = rk ρ M := by
      unfold rk; rw [hzl]; exact rk_saturation (zl_mono ρ hML)
    have hdeg' : deg ρ M ≤ deg ρ M' := deg_mono_of_rk_eq ρ hL hMM' hM'L hrk'.symm
    have hSM' : S < M' := lt_of_lt_of_le hSM hMM'
    have hfMM' : f M ≤ f M' := by
      dsimp only [f]
      rw [hrk']
      exact div_le_div_of_nonneg_right (by linarith) (hgap M hSM hML).le
    by_cases hfl : f L ≤ f M'
    · rw [hfN]
      exact hfMM'.trans (hN₀max M' ⟨hM'sat, hSM', hfl⟩)
    · have h1 : f M' ≤ f L := (not_le.mp hfl).le
      exact hfMM'.trans (h1.trans (hfN ▸ hN₀max L hLT))
  refine ⟨N, hSN, hNsat, hmax_all, ?_⟩
  intro M hSM hML hfM
  obtain ⟨M', hMM', hM'L, hzl⟩ := exists_real_saturation ρ hL hML
  have hM'sat : IsSat ρ L M' := ⟨hM'L, hzl ▸ isSaturated_saturation (zl_mono ρ hML)⟩
  have hrk' : rk ρ M' = rk ρ M := by
    unfold rk; rw [hzl]; exact rk_saturation (zl_mono ρ hML)
  have hdeg' : deg ρ M ≤ deg ρ M' := deg_mono_of_rk_eq ρ hL hMM' hM'L hrk'.symm
  have hSM' : S < M' := lt_of_lt_of_le hSM hMM'
  have hfMM' : f M ≤ f M' := by
    dsimp only [f]
    rw [hrk']
    exact div_le_div_of_nonneg_right (by linarith) (hgap M hSM hML).le
  have hfM_eq : f M = f N := hfM
  have hfM'_eq : f M' = f N₀ :=
    le_antisymm (hfN ▸ hmax_all M' hSM' hM'L) (hfN ▸ hfM_eq ▸ hfMM')
  have hM'Tmax : M' ∈ Tmax := ⟨⟨hM'sat, hSM', hfM'_eq ▸ hN₀max L hLT⟩, hfM'_eq⟩
  rw [← hrk']
  exact hNrk_max M' hM'Tmax

/-- **Complete Slope Characterization (`MuChar`)** for `R`-module Euclidean lattices. -/
theorem muChar_spec (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (hL0 : L ≠ ⊥) :
    (∀ θ : ℝ, muMax ρ L ≤ θ ↔ ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N) ∧
    (∀ θ : ℝ, θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N) ∧
    (∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ ⊥ ∧ slope ρ N = muMax ρ L) ∧
    muMin ρ L ≤ slope ρ L ∧ slope ρ L ≤ muMax ρ L := by
  have : DiscreteTopology (zl ρ L) := hL.2
  have hrk_pos : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → (0 : ℝ) < (rk ρ N : ℝ) := fun N hNL hN0 =>
    Nat.cast_pos.mpr (rk_pos_of_ne_bot' ρ hL hNL hN0)
  obtain ⟨Nmax, hbN, hNsat, hNmax, -⟩ := exists_max_slope_ratio ρ hL (isSat_bot ρ L) hL0.symm
  have hNmax0 : Nmax ≠ ⊥ := hbN.ne'
  have hslope_max : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → slope ρ N ≤ slope ρ Nmax := by
    intro N hNL hN0
    have h := hNmax N (bot_lt_iff_ne_bot.mpr hN0) hNL
    rw [deg_bot, rk_bot] at h
    simpa only [sub_zero, Nat.cast_zero, slope, RHDirect.ArakelovCovolume.slope, deg, rk] using h
  have hmuMax_eq : muMax ρ L = slope ρ Nmax := by
    unfold muMax
    refine IsGreatest.csSup_eq ⟨⟨Nmax, hNsat.1, hNmax0, rfl⟩, ?_⟩
    rintro t ⟨N, hNL, hN0, rfl⟩
    exact hslope_max N hNL hN0
  have part1 : ∀ θ : ℝ, muMax ρ L ≤ θ ↔ ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N := by
    intro θ
    rw [hmuMax_eq]
    constructor
    · intro hθ N hNL
      by_cases hN0 : N = ⊥
      · rw [hN0, deg_bot, rk_bot]; simp
      · have hle := (hslope_max N hNL hN0).trans hθ
        have hpos := hrk_pos N hNL hN0
        exact (div_le_iff₀ hpos).mp hle
    · intro h
      have hpos := hrk_pos Nmax hNsat.1 hNmax0
      exact (div_le_iff₀ hpos).mpr (h Nmax hNsat.1)
  have hqslope : ∀ S : Submodule R V, IsSat ρ L S →
      RHDirect.ArakelovCovolume.slope (quotLat (zl ρ L) (zl ρ S)) =
        (deg ρ L - deg ρ S) / ((rk ρ L : ℝ) - rk ρ S) := by
    intro S hS
    obtain ⟨_, hr, hle, hd⟩ := quot_invariants ρ hL hS
    unfold RHDirect.ArakelovCovolume.slope
    rw [hr, hd, Nat.cast_sub hle]
  let U : Set ℝ := {t : ℝ | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧
    RHDirect.ArakelovCovolume.slope (quotLat (zl ρ L) (zl ρ N)) = t}
  have hUne : U.Nonempty := ⟨_, ⊥, isSat_bot ρ L, hL0.symm, rfl⟩
  have hUbdd : BddBelow U := by
    let c := max (muMax ρ L) 0
    refine ⟨min (deg ρ L - c * (rk ρ L : ℝ)) 0, ?_⟩
    rintro t ⟨S, hS, hSL, rfl⟩
    rw [hqslope S hS]
    have hlt : rk ρ S < rk ρ L := rk_lt_of_isSat_lt ρ hL hS (lt_of_le_of_ne hS.1 hSL) le_rfl
    have hdiff : (1 : ℝ) ≤ (rk ρ L : ℝ) - rk ρ S := by
      have : rk ρ S + 1 ≤ rk ρ L := hlt
      have : (rk ρ S : ℝ) + 1 ≤ rk ρ L := by exact_mod_cast this
      linarith
    have hdegS : deg ρ S ≤ c * (rk ρ L : ℝ) := by
      have h1 : deg ρ S ≤ muMax ρ L * rk ρ S := (part1 (muMax ρ L)).mp le_rfl S hS.1
      have h2 : muMax ρ L * rk ρ S ≤ c * rk ρ S :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      have h3 : c * rk ρ S ≤ c * rk ρ L :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast rk_mono ρ hL hS.1 le_rfl) (le_max_right _ _)
      linarith
    rw [le_div_iff₀ (by linarith)]
    have m1 := min_le_left (deg ρ L - c * (rk ρ L : ℝ)) 0
    have m2 := min_le_right (deg ρ L - c * (rk ρ L : ℝ)) 0
    have m3 := mul_le_mul_of_nonpos_left hdiff m2
    linarith
  have part2 : ∀ θ : ℝ, θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N := by
    intro θ
    change θ ≤ sInf U ↔ _
    constructor
    · intro h N hNL
      obtain ⟨N', hNN', hN'L, hzl⟩ := exists_real_saturation ρ hL hNL
      have hN'sat : IsSat ρ L N' := ⟨hN'L, hzl ▸ isSaturated_saturation (zl_mono ρ hNL)⟩
      have hrk' : rk ρ N' = rk ρ N := by
        unfold rk; rw [hzl]; exact rk_saturation (zl_mono ρ hNL)
      have hdeg' : deg ρ N ≤ deg ρ N' := deg_mono_of_rk_eq ρ hL hNN' hN'L hrk'.symm
      by_cases hN'L' : N' = L
      · have hr : rk ρ N = rk ρ L := by rw [← hrk', hN'L']
        have hdg : deg ρ N ≤ deg ρ L := hN'L' ▸ hdeg'
        rw [hr, sub_self, mul_zero]; linarith
      · have ht : θ ≤ RHDirect.ArakelovCovolume.slope (quotLat (zl ρ L) (zl ρ N')) :=
          h.trans (csInf_le hUbdd ⟨N', hN'sat, hN'L', rfl⟩)
        rw [hqslope N' hN'sat] at ht
        have hlt : rk ρ N' < rk ρ L := rk_lt_of_isSat_lt ρ hL hN'sat (lt_of_le_of_ne hN'L hN'L') le_rfl
        have hdiff : (0 : ℝ) < (rk ρ L : ℝ) - rk ρ N' := by
          have : (rk ρ N' : ℝ) < rk ρ L := by exact_mod_cast hlt
          linarith
        have hmul := (le_div_iff₀ hdiff).mp ht
        rw [← hrk']
        linarith
    · intro h
      refine le_csInf hUne ?_
      rintro t ⟨S, hS, hSL, rfl⟩
      rw [hqslope S hS]
      have hlt : rk ρ S < rk ρ L := rk_lt_of_isSat_lt ρ hL hS (lt_of_le_of_ne hS.1 hSL) le_rfl
      have hdiff : (0 : ℝ) < (rk ρ L : ℝ) - rk ρ S := by
        have : (rk ρ S : ℝ) < rk ρ L := by exact_mod_cast hlt
        linarith
      exact (le_div_iff₀ hdiff).mpr (h S hS.1)
  have hquot_bot : RHDirect.ArakelovCovolume.slope (quotLat (zl ρ L) (zl ρ (⊥ : Submodule R V))) =
      slope ρ L := by
    rw [hqslope ⊥ (isSat_bot ρ L), deg_bot, rk_bot]
    simp [slope, RHDirect.ArakelovCovolume.slope, deg, rk]
  refine ⟨part1, part2, ⟨Nmax, hNsat, hNmax0, hmuMax_eq.symm⟩, ?_, ?_⟩
  · change sInf U ≤ slope ρ L
    rw [← hquot_bot]
    exact csInf_le hUbdd ⟨⊥, isSat_bot ρ L, hL0.symm, rfl⟩
  · rw [hmuMax_eq]
    exact hslope_max L le_rfl hL0

lemma muMax_le_iff (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (hL0 : L ≠ ⊥) (θ : ℝ) :
    muMax ρ L ≤ θ ↔ ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N :=
  (muChar_spec ρ hL hL0).1 θ

lemma le_muMin_iff (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (hL0 : L ≠ ⊥) (θ : ℝ) :
    θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N :=
  (muChar_spec ρ hL hL0).2.1 θ

lemma muMin_le_slope_le_muMax' (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (hL0 : L ≠ ⊥) :
    muMin ρ L ≤ slope ρ L ∧ slope ρ L ≤ muMax ρ L :=
  (muChar_spec ρ hL hL0).2.2.2

end RModuleLattices

/-! ## Section 2: Concrete Canonical Harder–Narasimhan Filtration `HLatHNFilt`, `hnSlopeList` & `hnPoly_concave` -/

section CanonicalHNFilt

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Harder–Narasimhan Threshold Sublattice `hnStep ρ L θ`**:
the supremum of all nonzero `R`-submodules `N ≤ L` with `θ ≤ muMin ρ N`. -/
def hnStep (ρ : V →+ E) (L : Submodule R V) (θ : ℝ) : Submodule R V :=
  sSup {N : Submodule R V | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N}

/-- **Full Specification of `hnStep ρ L θ`** (`HNStep`):
1. `hnStep ρ L θ` is saturated in `L`,
2. if `hnStep ρ L θ ≠ ⊥`, then `θ ≤ muMin ρ (hnStep ρ L θ)`,
3. maximal property: every nonzero `N ≤ L` with `θ ≤ muMin ρ N` satisfies `N ≤ hnStep ρ L θ`,
4. strict slope drop above `hnStep ρ L θ`. -/
theorem hnStep_spec (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (θ : ℝ) :
    IsSat ρ L (hnStep ρ L θ) ∧
    (hnStep ρ L θ ≠ ⊥ → θ ≤ muMin ρ (hnStep ρ L θ)) ∧
    (∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N → N ≤ hnStep ρ L θ) ∧
    (∀ N : Submodule R V, hnStep ρ L θ < N → N ≤ L →
      deg ρ N - deg ρ (hnStep ρ L θ) < θ * ((rk ρ N : ℝ) - rk ρ (hnStep ρ L θ))) := by
  let g : Submodule R V → ℝ := fun M => deg ρ M - θ * (rk ρ M : ℝ)
  have charP : ∀ M : Submodule R V, M ≤ L → M ≠ ⊥ →
      (θ ≤ muMin ρ M ↔ ∀ N ≤ M, g N ≤ g M) := by
    intro M hML hM0
    rw [le_muMin_iff ρ (isLat_of_le ρ hL hML) hM0 θ]
    constructor <;> intro h N hNM <;> have h1 := h N hNM <;> dsimp only [g] at * <;> linarith
  have supP : ∀ A B : Submodule R V, A ≤ L → B ≤ L →
      (∀ N ≤ A, g N ≤ g A) → (∀ N ≤ B, g N ≤ g B) → ∀ N ≤ A ⊔ B, g N ≤ g (A ⊔ B) := by
    intro A B hA hB pA pB N hN
    have hNL : N ≤ L := hN.trans (sup_le hA hB)
    have hsm1 := deg_supermodular ρ hL hNL hA
    have hsm2 := deg_supermodular ρ hL hA hB
    have hNA : g (N ⊓ A) ≤ g A := pA (N ⊓ A) inf_le_right
    have hsm3 := deg_supermodular ρ hL (sup_le hNL hA) hB
    have h1 : (N ⊔ A) ⊔ B = A ⊔ B := by
      apply le_antisymm (sup_le (sup_le hN le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    have h2 : g ((N ⊔ A) ⊓ B) ≤ g B := pB _ inf_le_right
    have hg_sup : ∀ X Y : Submodule R V, X ≤ L → Y ≤ L →
        g X + g Y ≤ g (X ⊔ Y) + g (X ⊓ Y) := by
      intro X Y hX hY
      have hs := deg_supermodular ρ hL hX hY
      have hr : (rk ρ (X ⊔ Y) : ℝ) + rk ρ (X ⊓ Y) = (rk ρ X : ℝ) + rk ρ Y := by exact_mod_cast hs.1
      have hθr : θ * (rk ρ (X ⊔ Y) : ℝ) + θ * rk ρ (X ⊓ Y) = θ * rk ρ X + θ * rk ρ Y := by
        rw [← mul_add, ← mul_add, hr]
      dsimp only [g]
      linarith [hs.2]
    have e1 := hg_sup N A hNL hA
    have e2 := hg_sup (N ⊔ A) B (sup_le hNL hA) hB
    rw [h1] at e2
    linarith
  let Sset : Set (Submodule R V) := {N : Submodule R V | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N}
  have memS : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N → N ≤ hnStep ρ L θ :=
    fun N hNL hN0 hθ => le_sSup ⟨hNL, hN0, hθ⟩
  have : DiscreteTopology (zl ρ L) := hL.2
  -- Prove `hnStep ρ L θ` is saturated and satisfies `PF : ∀ N ≤ F, g N ≤ g F`
  have hF_prop : IsSat ρ L (hnStep ρ L θ) ∧ (∀ N ≤ hnStep ρ L θ, g N ≤ g (hnStep ρ L θ)) := by
    by_cases hSne : Sset.Nonempty
    · -- Pick `M₀ ∈ Sset` maximizing `rk ρ M₀ ≤ rk ρ L`!
      have hfin : (rk ρ '' Sset).Finite :=
        (Set.finite_Iic (rk ρ L)).subset (by rintro _ ⟨M, hM, rfl⟩; exact rk_mono ρ hL hM.1 le_rfl)
      obtain ⟨r₀, ⟨M₀, hM₀S, hr₀⟩, hrmax⟩ :=
        Set.exists_max_image (rk ρ '' Sset) id hfin (hSne.image (rk ρ))
      -- Replace `M₀` by its real saturation `M₁`!
      obtain ⟨M₁, hM₀M₁, hM₁L, hzl₁⟩ := exists_real_saturation ρ hL hM₀S.1
      have hM₁sat : IsSat ρ L M₁ := ⟨hM₁L, hzl₁ ▸ isSaturated_saturation (zl_mono ρ hM₀S.1)⟩
      have hrk₁ : rk ρ M₁ = rk ρ M₀ := by
        unfold rk; rw [hzl₁]; exact rk_saturation (zl_mono ρ hM₀S.1)
      have hM₁0 : M₁ ≠ ⊥ := fun h0 => hM₀S.2.1 (le_bot_iff.mp (hM₀M₁.trans h0.le))
      have PM₀ : ∀ N ≤ M₀, g N ≤ g M₀ := (charP M₀ hM₀S.1 hM₀S.2.1).mp hM₀S.2.2
      have PM₁ : ∀ N ≤ M₁, g N ≤ g M₁ := by
        intro N hNM₁
        have hNL := hNM₁.trans hM₁L
        have hs := deg_supermodular ρ hL hNL hM₀S.1
        have hr : (rk ρ (N ⊔ M₀) : ℝ) + rk ρ (N ⊓ M₀) = (rk ρ N : ℝ) + rk ρ M₀ := by
          exact_mod_cast hs.1
        have hX : N ⊔ M₀ ≤ M₁ := sup_le hNM₁ hM₀M₁
        have r1 := rk_mono ρ hL le_sup_right (hX.trans hM₁L)
        have r2 := rk_mono ρ hL hX hM₁L
        have hreq : rk ρ (N ⊔ M₀) = rk ρ M₁ := by omega
        have hd := deg_mono_of_rk_eq ρ hL hX hM₁L hreq
        have e2 := PM₀ (N ⊓ M₀) inf_le_right
        have hθr : θ * (rk ρ M₁ : ℝ) + θ * rk ρ (N ⊓ M₀) = θ * rk ρ N + θ * rk ρ M₀ := by
          rw [← hreq, ← mul_add, ← mul_add, hr]
        dsimp only [g] at e2 ⊢
        linarith [hs.2]
      have hM₁S : M₁ ∈ Sset := ⟨hM₁L, hM₁0, (charP M₁ hM₁L hM₁0).mpr PM₁⟩
      -- Show `M₁` is the GREATEST element of `Sset`!
      have hM₁_top : ∀ N ∈ Sset, N ≤ M₁ := by
        intro N hNS
        have hjoinL : M₁ ⊔ N ≤ L := sup_le hM₁L hNS.1
        have hjoin0 : M₁ ⊔ N ≠ ⊥ := fun h0 => hM₁0 (le_bot_iff.mp (le_sup_left.trans h0.le))
        have Pjoin := supP M₁ N hM₁L hNS.1 PM₁ ((charP N hNS.1 hNS.2.1).mp hNS.2.2)
        have hjoinS : M₁ ⊔ N ∈ Sset := ⟨hjoinL, hjoin0, (charP _ hjoinL hjoin0).mpr Pjoin⟩
        have hrk_le : rk ρ (M₁ ⊔ N) ≤ rk ρ M₁ := by
          have h1 := hrmax (rk ρ (M₁ ⊔ N)) ⟨M₁ ⊔ N, hjoinS, rfl⟩
          change rk ρ (M₁ ⊔ N) ≤ r₀ at h1
          omega
        have hrk_eq : rk ρ M₁ = rk ρ (M₁ ⊔ N) :=
          le_antisymm (rk_mono ρ hL le_sup_left hjoinL) hrk_le
        have heq := eq_of_isSat_of_rk_eq ρ hL hM₁sat le_sup_left hjoinL hrk_eq
        exact heq ▸ le_sup_right
      have hFeq : hnStep ρ L θ = M₁ :=
        le_antisymm (sSup_le hM₁_top) (le_sSup hM₁S)
      rw [hFeq]
      exact ⟨hM₁sat, PM₁⟩
    · have hSempty : Sset = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
      have hFeq : hnStep ρ L θ = ⊥ := by change sSup Sset = ⊥; rw [hSempty]; exact sSup_empty
      rw [hFeq]
      exact ⟨isSat_bot ρ L, fun N hN => by rw [le_bot_iff.mp hN]⟩
  obtain ⟨Fsat, PF⟩ := hF_prop
  refine ⟨Fsat, fun hF0 => (charP _ Fsat.1 hF0).mpr PF, memS, ?_⟩
  intro N hFN hNL
  by_contra hcon
  push Not at hcon
  have hFL : hnStep ρ L θ ≠ L := (lt_of_lt_of_le hFN hNL).ne
  obtain ⟨N₀, hFN₀, hN₀sat, hmax, -⟩ := exists_max_slope_ratio ρ hL Fsat hFL
  have hr₀ : (0 : ℝ) < (rk ρ N₀ : ℝ) - rk ρ (hnStep ρ L θ) := by
    have : (rk ρ (hnStep ρ L θ) : ℝ) < rk ρ N₀ := by
      exact_mod_cast rk_lt_of_isSat_lt ρ hL Fsat hFN₀ hN₀sat.1
    linarith
  have hrN : (0 : ℝ) < (rk ρ N : ℝ) - rk ρ (hnStep ρ L θ) := by
    have : (rk ρ (hnStep ρ L θ) : ℝ) < rk ρ N := by
      exact_mod_cast rk_lt_of_isSat_lt ρ hL Fsat hFN hNL
    linarith
  have hratio := hmax N hFN hNL
  have hθN : θ ≤ (deg ρ N - deg ρ (hnStep ρ L θ)) / ((rk ρ N : ℝ) - rk ρ (hnStep ρ L θ)) :=
    (le_div_iff₀ hrN).mpr hcon
  have hμ : θ * ((rk ρ N₀ : ℝ) - rk ρ (hnStep ρ L θ)) ≤ deg ρ N₀ - deg ρ (hnStep ρ L θ) :=
    (le_div_iff₀ hr₀).mp (hθN.trans hratio)
  have PN₀ : ∀ M ≤ N₀, g M ≤ g N₀ := by
    intro M hMN₀
    have hML := hMN₀.trans hN₀sat.1
    have hs := deg_supermodular ρ hL hML Fsat.1
    have hr : (rk ρ (M ⊔ hnStep ρ L θ) : ℝ) + rk ρ (M ⊓ hnStep ρ L θ) =
        (rk ρ M : ℝ) + rk ρ (hnStep ρ L θ) := by exact_mod_cast hs.1
    have hθr : θ * (rk ρ (M ⊔ hnStep ρ L θ) : ℝ) + θ * rk ρ (M ⊓ hnStep ρ L θ) =
        θ * rk ρ M + θ * rk ρ (hnStep ρ L θ) := by rw [← mul_add, ← mul_add, hr]
    have e2 := PF (M ⊓ hnStep ρ L θ) inf_le_right
    have hX : M ⊔ hnStep ρ L θ ≤ N₀ := sup_le hMN₀ hFN₀.le
    have hXN₀ : g (M ⊔ hnStep ρ L θ) ≤ g N₀ := by
      rcases (le_sup_right : hnStep ρ L θ ≤ M ⊔ hnStep ρ L θ).lt_or_eq with hlt | heq
      · have hrX : (0 : ℝ) < (rk ρ (M ⊔ hnStep ρ L θ) : ℝ) - rk ρ (hnStep ρ L θ) := by
          have : (rk ρ (hnStep ρ L θ) : ℝ) < rk ρ (M ⊔ hnStep ρ L θ) := by
            exact_mod_cast rk_lt_of_isSat_lt ρ hL Fsat hlt (hX.trans hN₀sat.1)
          linarith
        have hrX₀ : (rk ρ (M ⊔ hnStep ρ L θ) : ℝ) ≤ rk ρ N₀ := by
          exact_mod_cast rk_mono ρ hL hX hN₀sat.1
        have k2 := hmax (M ⊔ hnStep ρ L θ) hlt (hX.trans hN₀sat.1)
        have k2' : (deg ρ (M ⊔ hnStep ρ L θ) - deg ρ (hnStep ρ L θ)) *
            ((rk ρ N₀ : ℝ) - rk ρ (hnStep ρ L θ)) ≤
            (deg ρ N₀ - deg ρ (hnStep ρ L θ)) *
            ((rk ρ (M ⊔ hnStep ρ L θ) : ℝ) - rk ρ (hnStep ρ L θ)) := by
          exact (div_le_div_iff₀ hrX hr₀).mp k2
        have hpos_mul := mul_nonneg (sub_nonneg.mpr hμ) (sub_nonneg.mpr hrX₀)
        have hprod : ((rk ρ N₀ : ℝ) - rk ρ (hnStep ρ L θ)) * g (M ⊔ hnStep ρ L θ) ≤
            ((rk ρ N₀ : ℝ) - rk ρ (hnStep ρ L θ)) * g N₀ := by
          dsimp only [g]; nlinarith
        exact le_of_mul_le_mul_left hprod hr₀
      · rw [← heq]; dsimp only [g]; linarith
    dsimp only [g] at e2 hXN₀ ⊢
    linarith [hs.2]
  have hN₀0 : N₀ ≠ ⊥ := ne_bot_of_gt hFN₀
  have hle := memS N₀ hN₀sat.1 hN₀0 ((charP N₀ hN₀sat.1 hN₀0).mpr PN₀)
  exact hFN₀.not_ge hle

/-- **Concrete Canonical Harder–Narasimhan Filtration `HLatHNFilt ρ L`** of an `R`-module
Euclidean lattice `(ρ, L)`: a finite strictly increasing chain of saturated `R`-submodules
`0 = L_0 < L_1 < ... < L_k = L` whose consecutive incremental slopes `μ_0 > μ_1 > ... > μ_{k-1}`
are strictly decreasing and each `L_{i+1}` is the largest maximal-ratio extension of `L_i`. -/
structure HLatHNFilt (ρ : V →+ E) (L : Submodule R V) where
  /-- Number of Harder–Narasimhan filtration steps (`0` iff `L = ⊥`). -/
  len : ℕ
  /-- Filtration steps `0 = step 0 < step 1 < ... < step len = L`. -/
  step : Fin (len + 1) → Submodule R V
  step_zero : step 0 = ⊥
  step_last : step (Fin.last len) = L
  step_saturated : ∀ j, IsSat ρ L (step j)
  step_strictMono : StrictMono step
  /-- Consecutive Harder–Narasimhan slopes `μ_i = (deg L_{i+1} - deg L_i) / (rk L_{i+1} - rk L_i)`. -/
  quotSlope : Fin len → ℝ
  quotSlope_eq : ∀ i : Fin len,
    quotSlope i = (deg ρ (step i.succ) - deg ρ (step i.castSucc)) /
      ((rk ρ (step i.succ) : ℝ) - rk ρ (step i.castSucc))
  /-- Maximal incremental slope property at step `i`. -/
  step_maximal : ∀ (i : Fin len) (N : Submodule R V),
    step i.castSucc < N → N ≤ L →
    (deg ρ N - deg ρ (step i.castSucc)) / ((rk ρ N : ℝ) - rk ρ (step i.castSucc)) ≤ quotSlope i
  /-- Largest rank among maximal-ratio extensions at step `i`. -/
  step_largest : ∀ (i : Fin len) (N : Submodule R V),
    step i.castSucc < N → N ≤ L →
    (deg ρ N - deg ρ (step i.castSucc)) / ((rk ρ N : ℝ) - rk ρ (step i.castSucc)) = quotSlope i →
    rk ρ N ≤ rk ρ (step i.succ)
  /-- Strictly decreasing Harder–Narasimhan slopes `μ_0 > μ_1 > ... > μ_{len-1}`. -/
  slope_strictAnti : StrictAnti quotSlope

/-- Auxiliary recursive construction of a partial HN filtration from a saturated `S ≤ L` up to `L`. -/
private theorem exists_hlatHNFilt_from (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) :
    ∀ (m : ℕ) (S : Submodule R V), IsSat ρ L S → rk ρ L - rk ρ S ≤ m →
      ∃ (len : ℕ) (step : Fin (len + 1) → Submodule R V) (qs : Fin len → ℝ),
        step 0 = S ∧ step (Fin.last len) = L ∧
        (∀ j, IsSat ρ L (step j)) ∧ StrictMono step ∧
        (∀ i : Fin len, qs i = (deg ρ (step i.succ) - deg ρ (step i.castSucc)) /
          ((rk ρ (step i.succ) : ℝ) - rk ρ (step i.castSucc))) ∧
        (∀ (i : Fin len) (N : Submodule R V), step i.castSucc < N → N ≤ L →
          (deg ρ N - deg ρ (step i.castSucc)) / ((rk ρ N : ℝ) - rk ρ (step i.castSucc)) ≤ qs i) ∧
        (∀ (i : Fin len) (N : Submodule R V), step i.castSucc < N → N ≤ L →
          (deg ρ N - deg ρ (step i.castSucc)) / ((rk ρ N : ℝ) - rk ρ (step i.castSucc)) = qs i →
          rk ρ N ≤ rk ρ (step i.succ)) ∧
        StrictAnti qs := by
  intro m
  induction m with
  | zero =>
    intro S hS hdiff
    have hrk_le := rk_mono ρ hL hS.1 le_rfl
    have hSL : S = L := eq_of_isSat_of_rk_eq ρ hL hS hS.1 le_rfl (by omega)
    refine ⟨0, fun _ => S, Fin.elim0, rfl, hSL, fun _ => hS,
      fun a b h => absurd h (by omega), fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro S hS hdiff
    by_cases hSL : S = L
    · refine ⟨0, fun _ => S, Fin.elim0, rfl, hSL, fun _ => hS,
        fun a b h => absurd h (by omega), fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · obtain ⟨S₁, hSS₁, hS₁sat, hS₁max, hS₁large⟩ := exists_max_slope_ratio ρ hL hS hSL
      have hrk_lt := rk_lt_of_isSat_lt ρ hL hS hSS₁ hS₁sat.1
      have hrk_le := rk_mono ρ hL hS₁sat.1 le_rfl
      have hdiff' : rk ρ L - rk ρ S₁ ≤ m := by omega
      obtain ⟨len', step', qs', h0', hlast', hsat', hmono', hqseq', hmax', hlarge', hanti'⟩ :=
        ih S₁ hS₁sat hdiff'
      let step : Fin (len' + 1 + 1) → Submodule R V := Fin.cons S step'
      let μ₀ : ℝ := (deg ρ S₁ - deg ρ S) / ((rk ρ S₁ : ℝ) - rk ρ S)
      let qs : Fin (len' + 1) → ℝ := Fin.cons μ₀ qs'
      have hstep_succ : ∀ j : Fin (len' + 1), step j.succ = step' j :=
        fun j => Fin.cons_succ (α := fun _ => Submodule R V) S step' j
      have hmono : StrictMono step := by
        intro a b
        refine Fin.cases (fun b => ?_) (fun a' b => ?_) a b
        · refine Fin.cases (fun h => absurd h (lt_irrefl _)) (fun b' _ => ?_) b
          change S < step' b'
          have hle : step' 0 ≤ step' b' := hmono'.monotone (Fin.zero_le b')
          rw [h0'] at hle
          exact lt_of_lt_of_le hSS₁ hle
        · refine Fin.cases (fun h => absurd h (Fin.not_lt_zero _)) (fun b' h => ?_) b
          change step' a' < step' b'
          exact hmono' (Fin.succ_lt_succ_iff.mp h)
      have hanti : StrictAnti qs := by
        intro a b
        refine Fin.cases (fun b => ?_) (fun a' b => ?_) a b
        · refine Fin.cases (fun h => absurd h (lt_irrefl _)) (fun b' _ => ?_) b
          change qs' b' < μ₀
          -- Show `qs' 0 < μ₀` (then `qs' b' ≤ qs' 0 < μ₀`!)
          let i₀ : Fin len' := ⟨0, lt_of_le_of_lt (Nat.zero_le _) b'.2⟩
          have hb0 : qs' b' ≤ qs' i₀ := by
            rcases eq_or_lt_of_le (show i₀ ≤ b' from Nat.zero_le b'.1) with h | hlt
            · rw [h]
            · exact (hanti' hlt).le
          let S₂ := step' i₀.succ
          have hS₁S₂ : S₁ < S₂ := by
            have h := hmono' (Fin.castSucc_lt_succ (i := i₀))
            have hcast : i₀.castSucc = 0 := Fin.ext rfl
            rwa [hcast, h0'] at h
          have hS₂sat : IsSat ρ L S₂ := hsat' i₀.succ
          have hSS₂ : S < S₂ := lt_trans hSS₁ hS₁S₂
          have hr1 : (0 : ℝ) < (rk ρ S₁ : ℝ) - rk ρ S := by
            have : (rk ρ S : ℝ) < rk ρ S₁ := by exact_mod_cast hrk_lt
            linarith
          have hr2 : (0 : ℝ) < (rk ρ S₂ : ℝ) - rk ρ S₁ := by
            have : (rk ρ S₁ : ℝ) < rk ρ S₂ := by
              exact_mod_cast rk_lt_of_isSat_lt ρ hL hS₁sat hS₁S₂ hS₂sat.1
            linarith
          have hq0_eq : qs' i₀ = (deg ρ S₂ - deg ρ S₁) / ((rk ρ S₂ : ℝ) - rk ρ S₁) := by
            have h := hqseq' i₀
            have hcast : i₀.castSucc = 0 := Fin.ext rfl
            rwa [hcast, h0'] at h
          have hlt_S₂ : (deg ρ S₂ - deg ρ S) / ((rk ρ S₂ : ℝ) - rk ρ S) < μ₀ := by
            have hle_S₂ := hS₁max S₂ hSS₂ hS₂sat.1
            refine lt_of_le_of_ne hle_S₂ fun heq => ?_
            have hrle := hS₁large S₂ hSS₂ hS₂sat.1 heq
            have hrgt := rk_lt_of_isSat_lt ρ hL hS₁sat hS₁S₂ hS₂sat.1
            omega
          have hmul_S₂ : deg ρ S₂ - deg ρ S < μ₀ * ((rk ρ S₂ : ℝ) - rk ρ S) :=
            (div_lt_iff₀ (by linarith)).mp hlt_S₂
          have hmul_S₁ : deg ρ S₁ - deg ρ S = μ₀ * ((rk ρ S₁ : ℝ) - rk ρ S) :=
            (div_eq_iff hr1.ne').mp rfl
          have hq0_lt : qs' i₀ < μ₀ := by
            rw [hq0_eq, div_lt_iff₀ hr2]
            linarith
          exact lt_of_le_of_lt hb0 hq0_lt
        · refine Fin.cases (fun h => absurd h (Fin.not_lt_zero _)) (fun b' h => ?_) b
          change qs' b' < qs' a'
          exact hanti' (Fin.succ_lt_succ_iff.mp h)
      refine ⟨len' + 1, step, qs, Fin.cons_zero _ _, ?_, ?_, hmono, ?_, ?_, ?_, hanti⟩
      · change step (Fin.last len').succ = L
        rw [hstep_succ, hlast']
      · intro j
        refine Fin.cases hS hsat' j
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · change μ₀ = (deg ρ (step' 0) - deg ρ S) / ((rk ρ (step' 0) : ℝ) - rk ρ S)
          rw [h0']
        · change qs' i' = (deg ρ (step' i'.succ) - deg ρ (step' i'.castSucc)) /
            ((rk ρ (step' i'.succ) : ℝ) - rk ρ (step' i'.castSucc))
          exact hqseq' i'
      · intro i N hN hNL
        refine Fin.cases ?_ (fun i' => ?_) i hN
        · intro hSN
          change (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S) ≤ μ₀
          exact hS₁max N hSN hNL
        · intro hiN
          exact hmax' i' N hiN hNL
      · intro i N hN hNL heq
        refine Fin.cases ?_ (fun i' => ?_) i hN heq
        · intro hSN hSN_eq
          change rk ρ N ≤ rk ρ (step' 0)
          rw [h0']
          exact hS₁large N hSN hNL hSN_eq
        · intro hiN hiN_eq
          exact hlarge' i' N hiN hNL hiN_eq

/-- **Existence of the Concrete Canonical Harder–Narasimhan Filtration `HLatHNFilt ρ L`**. -/
theorem exists_hlatHNFilt (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) :
    Nonempty (HLatHNFilt ρ L) := by
  obtain ⟨len, step, qs, h0, hlast, hsat, hmono, hqseq, hmax, hlarge, hanti⟩ :=
    exists_hlatHNFilt_from ρ hL (rk ρ L) ⊥ (isSat_bot ρ L) (by simp [rk_bot])
  exact ⟨{
    len := len
    step := step
    step_zero := h0
    step_last := hlast
    step_saturated := hsat
    step_strictMono := hmono
    quotSlope := qs
    quotSlope_eq := hqseq
    step_maximal := hmax
    step_largest := hlarge
    slope_strictAnti := hanti
  }⟩

/-- Canonical Harder–Narasimhan filtration of `(ρ, L)`. -/
def canonicalHLatHNFilt (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) : HLatHNFilt ρ L :=
  Classical.choice (exists_hlatHNFilt ρ hL)

namespace HLatHNFilt

/-- Rank jump `Δr_i = rk (step (i+1)) - rk (step i) > 0` at step `i`. -/
def rkJump {ρ : V →+ E} {L : Submodule R V} (F : HLatHNFilt ρ L) (i : Fin F.len) : ℕ :=
  rk ρ (F.step i.succ) - rk ρ (F.step i.castSucc)

lemma rkJump_pos {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (i : Fin F.len) : 0 < F.rkJump i := by
  have hlt := rk_lt_of_isSat_lt ρ hL (F.step_saturated i.castSucc)
    (F.step_strictMono (Fin.castSucc_lt_succ (i := i))) (F.step_saturated i.succ).1
  unfold rkJump; omega

lemma deg_jump_eq {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (i : Fin F.len) :
    deg ρ (F.step i.succ) - deg ρ (F.step i.castSucc) = (F.rkJump i : ℝ) * F.quotSlope i := by
  have hlt := rk_lt_of_isSat_lt ρ hL (F.step_saturated i.castSucc)
    (F.step_strictMono (Fin.castSucc_lt_succ (i := i))) (F.step_saturated i.succ).1
  have hdiff : (rk ρ (F.step i.succ) : ℝ) - rk ρ (F.step i.castSucc) = (F.rkJump i : ℝ) := by
    unfold rkJump; rw [Nat.cast_sub hlt.le]
  have hpos : (0 : ℝ) < (F.rkJump i : ℝ) := Nat.cast_pos.mpr (F.rkJump_pos hL i)
  have hq := F.quotSlope_eq i
  rw [hdiff] at hq
  rw [hq, mul_div_cancel₀ _ hpos.ne']

/-- Truncation index `truncIdx F θ = #{i : Fin F.len | θ ≤ F.quotSlope i}`. -/
def truncIdx {ρ : V →+ E} {L : Submodule R V} (F : HLatHNFilt ρ L) (θ : ℝ) : Fin (F.len + 1) :=
  ⟨(Finset.univ.filter fun i : Fin F.len => θ ≤ F.quotSlope i).card,
    Nat.lt_succ_of_le (by
      calc (Finset.univ.filter fun i : Fin F.len => θ ≤ F.quotSlope i).card
          ≤ (Finset.univ : Finset (Fin F.len)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = F.len := by simp)⟩

lemma mem_filter_truncIdx_iff {ρ : V →+ E} {L : Submodule R V}
    (F : HLatHNFilt ρ L) (θ : ℝ) (i : Fin F.len) :
    θ ≤ F.quotSlope i ↔ i.1 < (F.truncIdx θ).1 := by
  classical
  let S := Finset.univ.filter fun j : Fin F.len => θ ≤ F.quotSlope j
  have hdown : ∀ a b : Fin F.len, a ≤ b → b ∈ S → a ∈ S := by
    intro a b hab hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ a, hb.2.trans ?_⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (F.slope_strictAnti hlt).le
  have hiff : θ ≤ F.quotSlope i ↔ i ∈ S := by simp [S]
  rw [hiff]
  change i ∈ S ↔ i.1 < S.card
  constructor
  · intro hi
    have hsub : Finset.univ.filter (fun j : Fin F.len => j.1 ≤ i.1) ⊆ S := fun j hj =>
      hdown j i (Finset.mem_filter.mp hj).2 hi
    have hcard : (Finset.univ.filter (fun j : Fin F.len => j.1 ≤ i.1)).card = i.1 + 1 := by
      have hbij : (Finset.univ.filter (fun j : Fin F.len => j.1 ≤ i.1)).card =
          (Finset.range (i.1 + 1)).card := by
        refine Finset.card_bij (fun j _ => j.1)
          (fun j hj => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2))
          (fun _ _ _ _ h => Fin.ext h)
          (fun k hk => ⟨⟨k, lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) i.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ (Finset.mem_range.mp hk)⟩, rfl⟩)
      rw [hbij, Finset.card_range]
    have := Finset.card_le_card hsub; omega
  · intro hlt
    by_contra hnot
    have hsub : S ⊆ Finset.univ.filter (fun j : Fin F.len => j.1 < i.1) := fun j hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, by
        by_contra hge; exact hnot (hdown i j (not_lt.mp hge) hj)⟩
    have hcard : (Finset.univ.filter (fun j : Fin F.len => j.1 < i.1)).card = i.1 := by
      have hbij : (Finset.univ.filter (fun j : Fin F.len => j.1 < i.1)).card =
          (Finset.range i.1).card := by
        refine Finset.card_bij (fun j _ => j.1)
          (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
          (fun _ _ _ _ h => Fin.ext h)
          (fun k hk => ⟨⟨k, lt_trans (Finset.mem_range.mp hk) i.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩, rfl⟩)
      rw [hbij, Finset.card_range]
    have := Finset.card_le_card hsub; omega

/-- Telescoping `rk` and `deg` along `F.step`. -/
lemma rk_step_eq_sum {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (j : Fin (F.len + 1)) :
    rk ρ (F.step j) = ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < j.1), F.rkJump i := by
  have hrec : ∀ m : ℕ, (hm : m ≤ F.len) →
      rk ρ (F.step ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), F.rkJump i := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ : Fin (F.len + 1)) = 0 := Fin.ext rfl
      rw [h0, F.step_zero, rk_bot]; simp
    | succ m ih =>
      intro hm
      let i_m : Fin F.len := ⟨m, hm⟩
      have hfilt : Finset.univ.filter (fun i : Fin F.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]; omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F.len => i.1 < m) := by simp [i_m]
      have hlt := rk_lt_of_isSat_lt ρ hL (F.step_saturated i_m.castSucc)
        (F.step_strictMono (Fin.castSucc_lt_succ (i := i_m))) (F.step_saturated i_m.succ).1
      rw [hfilt, Finset.sum_insert hnotmem, ← ih (Nat.le_of_succ_le hm)]
      unfold rkJump
      change rk ρ (F.step i_m.succ) = (rk ρ (F.step i_m.succ) - rk ρ (F.step i_m.castSucc)) +
        rk ρ (F.step i_m.castSucc)
      omega
  exact hrec j.1 (Nat.le_of_lt_succ j.2)

lemma deg_step_eq_sum {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (j : Fin (F.len + 1)) :
    deg ρ (F.step j) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < j.1),
        (F.rkJump i : ℝ) * F.quotSlope i := by
  have hrec : ∀ m : ℕ, (hm : m ≤ F.len) →
      deg ρ (F.step ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m),
          (F.rkJump i : ℝ) * F.quotSlope i := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ : Fin (F.len + 1)) = 0 := Fin.ext rfl
      rw [h0, F.step_zero, deg_bot]; simp
    | succ m ih =>
      intro hm
      let i_m : Fin F.len := ⟨m, hm⟩
      have hfilt : Finset.univ.filter (fun i : Fin F.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]; omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F.len => i.1 < m) := by simp [i_m]
      have hdj := F.deg_jump_eq hL i_m
      rw [hfilt, Finset.sum_insert hnotmem, ← ih (Nat.le_of_succ_le hm)]
      change deg ρ (F.step i_m.succ) = (F.rkJump i_m : ℝ) * F.quotSlope i_m +
        deg ρ (F.step i_m.castSucc)
      linarith
  exact hrec j.1 (Nat.le_of_lt_succ j.2)

/-- Step-by-step filtration bound for any sublattice `N ≤ L` intersected with `F.step`. -/
lemma sub_step_bound {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) {N : Submodule R V} (hNL : N ≤ L) (i : Fin F.len) :
    rk ρ (N ⊓ F.step i.castSucc) ≤ rk ρ (N ⊓ F.step i.succ) ∧
    rk ρ (N ⊓ F.step i.succ) - rk ρ (N ⊓ F.step i.castSucc) ≤ F.rkJump i ∧
    deg ρ (N ⊓ F.step i.succ) - deg ρ (N ⊓ F.step i.castSucc) ≤
      ((rk ρ (N ⊓ F.step i.succ) - rk ρ (N ⊓ F.step i.castSucc) : ℕ) : ℝ) * F.quotSlope i := by
  let A := N ⊓ F.step i.succ
  let B := F.step i.castSucc
  have hAL : A ≤ L := inf_le_left.trans hNL
  have hBL : B ≤ L := (F.step_saturated i.castSucc).1
  have hinf : A ⊓ B = N ⊓ F.step i.castSucc := by
    rw [inf_assoc, inf_eq_right.mpr (F.step_strictMono (Fin.castSucc_lt_succ (i := i))).le]
  have hsup_le : A ⊔ B ≤ F.step i.succ :=
    sup_le inf_le_right (F.step_strictMono (Fin.castSucc_lt_succ (i := i))).le
  have hsm := deg_supermodular ρ hL hAL hBL
  rw [hinf] at hsm
  have hr1 : rk ρ B ≤ rk ρ (A ⊔ B) := rk_mono ρ hL le_sup_right (sup_le hAL hBL)
  have hr2 : rk ρ (A ⊔ B) ≤ rk ρ (F.step i.succ) :=
    rk_mono ρ hL hsup_le (F.step_saturated i.succ).1
  have hrle : rk ρ (N ⊓ F.step i.castSucc) ≤ rk ρ A := by omega
  have hrjump : rk ρ A - rk ρ (N ⊓ F.step i.castSucc) ≤ F.rkJump i := by
    unfold rkJump; dsimp only [B] at hr1 hr2 hsm; omega
  refine ⟨hrle, hrjump, ?_⟩
  rcases (le_sup_right : B ≤ A ⊔ B).lt_or_eq with hlt | heq
  · have hmax := F.step_maximal i (A ⊔ B) hlt (sup_le hAL hBL)
    have hpos : (0 : ℝ) < (rk ρ (A ⊔ B) : ℝ) - rk ρ B := by
      have : (rk ρ B : ℝ) < rk ρ (A ⊔ B) := by
        exact_mod_cast rk_lt_of_isSat_lt ρ hL (F.step_saturated i.castSucc) hlt (sup_le hAL hBL)
      linarith
    have hmul := (div_le_iff₀ hpos).mp hmax
    have hcast : ((rk ρ A - rk ρ (N ⊓ F.step i.castSucc) : ℕ) : ℝ) =
        (rk ρ (A ⊔ B) : ℝ) - rk ρ B := by
      rw [Nat.cast_sub hrle]
      have : (rk ρ (A ⊔ B) : ℝ) + rk ρ (N ⊓ F.step i.castSucc) = (rk ρ A : ℝ) + rk ρ B := by
        exact_mod_cast hsm.1
      linarith
    rw [hcast]
    linarith [hsm.2]
  · have hr0 : rk ρ A - rk ρ (N ⊓ F.step i.castSucc) = 0 := by
      rw [← heq] at hsm; omega
    have hdeg0 : deg ρ A - deg ρ (N ⊓ F.step i.castSucc) ≤ 0 := by
      rw [← heq] at hsm; linarith [hsm.2]
    rw [hr0]; simp; dsimp only [A] at hdeg0; linarith

/-- Exact identification **`hnStep ρ L θ = F.step (F.truncIdx θ)`**! -/
theorem hnStep_eq_step_truncIdx {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (θ : ℝ) :
    hnStep ρ L θ = F.step (F.truncIdx θ) := by
  let j₀ := F.truncIdx θ
  let S := F.step j₀
  have hspec := hnStep_spec ρ hL θ
  -- First show `S ≤ hnStep ρ L θ`
  have hle1 : S ≤ hnStep ρ L θ := by
    by_cases hS0 : S = ⊥
    · rw [hS0]; exact bot_le
    · refine hspec.2.2.1 S (F.step_saturated j₀).1 hS0 ?_
      rw [le_muMin_iff ρ (isLat_of_le ρ hL (F.step_saturated j₀).1) hS0 θ]
      intro N hNS
      have hNL := hNS.trans (F.step_saturated j₀).1
      -- Telescope `(rk (F.step k) - rk (N ⊓ F.step k))` and `(deg (F.step k) - deg (N ⊓ F.step k))`
      have hrec : ∀ m : ℕ, (hm : m ≤ j₀.1) →
          θ * ((rk ρ (F.step ⟨m, lt_of_le_of_lt hm j₀.2⟩) : ℝ) -
              rk ρ (N ⊓ F.step ⟨m, lt_of_le_of_lt hm j₀.2⟩)) ≤
            deg ρ (F.step ⟨m, lt_of_le_of_lt hm j₀.2⟩) -
              deg ρ (N ⊓ F.step ⟨m, lt_of_le_of_lt hm j₀.2⟩) := by
        intro m
        induction m with
        | zero =>
          intro _
          have h0 : (⟨0, lt_of_le_of_lt (Nat.zero_le _) j₀.2⟩ : Fin (F.len + 1)) = 0 := Fin.ext rfl
          rw [h0, F.step_zero, inf_bot_eq, rk_bot, deg_bot]; simp
        | succ m ih =>
          intro hm
          let i_m : Fin F.len := ⟨m, by have := j₀.2; omega⟩
          have hθ_le : θ ≤ F.quotSlope i_m := (F.mem_filter_truncIdx_iff θ i_m).mpr hm
          obtain ⟨hrle, hrjump, hdeg_step⟩ := F.sub_step_bound hL hNL i_m
          have hdj := F.deg_jump_eq hL i_m
          have hprev := ih (Nat.le_of_succ_le hm)
          have hrk_gap : 0 ≤ (F.rkJump i_m : ℝ) -
              ((rk ρ (N ⊓ F.step i_m.succ) - rk ρ (N ⊓ F.step i_m.castSucc) : ℕ) : ℝ) := by
            have : ((rk ρ (N ⊓ F.step i_m.succ) - rk ρ (N ⊓ F.step i_m.castSucc) : ℕ) : ℝ) ≤
                (F.rkJump i_m : ℝ) := by exact_mod_cast hrjump
            linarith
          have hmul_θ := mul_le_mul_of_nonneg_right hθ_le hrk_gap
          have hcast_N : ((rk ρ (N ⊓ F.step i_m.succ) - rk ρ (N ⊓ F.step i_m.castSucc) : ℕ) : ℝ) =
              (rk ρ (N ⊓ F.step i_m.succ) : ℝ) - rk ρ (N ⊓ F.step i_m.castSucc) := Nat.cast_sub hrle
          have hlt_step := rk_lt_of_isSat_lt ρ hL (F.step_saturated i_m.castSucc)
            (F.step_strictMono (Fin.castSucc_lt_succ (i := i_m))) (F.step_saturated i_m.succ).1
          have hcast_S : (F.rkJump i_m : ℝ) =
              (rk ρ (F.step i_m.succ) : ℝ) - rk ρ (F.step i_m.castSucc) := by
            unfold rkJump; exact Nat.cast_sub hlt_step.le
          change θ * ((rk ρ (F.step i_m.succ) : ℝ) - rk ρ (N ⊓ F.step i_m.succ)) ≤
            deg ρ (F.step i_m.succ) - deg ρ (N ⊓ F.step i_m.succ)
          change θ * ((rk ρ (F.step i_m.castSucc) : ℝ) - rk ρ (N ⊓ F.step i_m.castSucc)) ≤
            deg ρ (F.step i_m.castSucc) - deg ρ (N ⊓ F.step i_m.castSucc) at hprev
          rw [hcast_N] at hmul_θ hdeg_step
          rw [hcast_S] at hmul_θ hdj
          linarith
      have hfinal := hrec j₀.1 le_rfl
      have hinfN : N ⊓ S = N := inf_eq_left.mpr hNS
      simpa only [Fin.eta, S, j₀, hinfN] using hfinal
  -- Next show `hnStep ρ L θ ≤ S`
  have hle2 : hnStep ρ L θ ≤ S := by
    by_contra hnot
    have hH0 : hnStep ρ L θ ≠ ⊥ := fun h0 => hnot (h0 ▸ bot_le)
    have hμH := hspec.2.1 hH0
    have hj₀_lt : j₀.1 < F.len := by
      by_contra hge
      have hlast : j₀ = Fin.last F.len := Fin.ext (by have := j₀.2; simp; omega)
      have hSL : S = L := by dsimp only [S]; rw [hlast, F.step_last]
      exact hnot (hSL ▸ hspec.1.1)
    let i₀ : Fin F.len := ⟨j₀.1, hj₀_lt⟩
    have hi₀_cast : i₀.castSucc = j₀ := Fin.ext rfl
    have hq_lt : F.quotSlope i₀ < θ := by
      by_contra hge
      push Not at hge
      have := (F.mem_filter_truncIdx_iff θ i₀).mp hge
      exact lt_irrefl j₀.1 this
    let M := hnStep ρ L θ ⊔ S
    have hSM : S < M := lt_of_le_of_ne le_sup_right fun heq => hnot (heq ▸ le_sup_left)
    have hML : M ≤ L := sup_le hspec.1.1 (F.step_saturated j₀).1
    have hmax := F.step_maximal i₀ M (hi₀_cast.symm ▸ hSM) hML
    rw [hi₀_cast] at hmax
    have hrpos : (0 : ℝ) < (rk ρ M : ℝ) - rk ρ S := by
      have : (rk ρ S : ℝ) < rk ρ M := by
        exact_mod_cast rk_lt_of_isSat_lt ρ hL (F.step_saturated j₀) hSM hML
      linarith
    have hdegM : deg ρ M - deg ρ S < θ * ((rk ρ M : ℝ) - rk ρ S) :=
      (div_lt_iff₀ hrpos).mp (lt_of_le_of_lt hmax hq_lt)
    have hsm := deg_supermodular ρ hL hspec.1.1 (F.step_saturated j₀).1
    have hr_eq : (rk ρ M : ℝ) - rk ρ S =
        (rk ρ (hnStep ρ L θ) : ℝ) - rk ρ (hnStep ρ L θ ⊓ S) := by
      have : (rk ρ M : ℝ) + rk ρ (hnStep ρ L θ ⊓ S) = (rk ρ (hnStep ρ L θ) : ℝ) + rk ρ S := by
        exact_mod_cast hsm.1
      linarith
    have hlow := (le_muMin_iff ρ (isLat_of_le ρ hL hspec.1.1) hH0 θ).mp hμH
      (hnStep ρ L θ ⊓ S) inf_le_left
    dsimp only [M, S] at hdegM hr_eq hlow
    rw [hr_eq] at hdegM
    linarith [hsm.2]
  exact le_antisymm hle2 hle1

/-- Descending list of `rk ρ L` Harder–Narasimhan slopes of `F`. -/
def slopesDesc {ρ : V →+ E} {L : Submodule R V} (F : HLatHNFilt ρ L) : List ℝ :=
  (List.finRange F.len).flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)

lemma slopesDesc_length {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) : F.slopesDesc.length = rk ρ L := by
  have hrk := F.rk_step_eq_sum hL (Fin.last F.len)
  rw [F.step_last] at hrk
  have hf : Finset.univ.filter (fun i : Fin F.len => i.1 < (Fin.last F.len).1) = Finset.univ := by
    ext i; simp
  rw [hf] at hrk
  rw [hrk]
  unfold slopesDesc
  rw [List.length_flatMap]
  have h1 : ((List.finRange F.len).map fun i => (List.replicate (F.rkJump i) (F.quotSlope i)).length).sum =
      ((List.finRange F.len).map fun i => F.rkJump i).sum := by
    congr 1; refine List.map_congr_left fun i _ => List.length_replicate
  rw [h1]
  exact (Fin.sum_univ_def F.rkJump).symm

lemma slopesDesc_pairwise_ge {ρ : V →+ E} {L : Submodule R V} (F : HLatHNFilt ρ L) :
    F.slopesDesc.Pairwise (· ≥ ·) := by
  unfold slopesDesc
  have hrec : ∀ (l : List (Fin F.len)), l.Pairwise (· < ·) →
      (l.flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)).Pairwise (· ≥ ·) := by
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
      exact (F.slope_strictAnti (hpair.1 b hb)).le
  exact hrec (List.finRange F.len) (List.pairwise_lt_finRange F.len)

lemma slopesDesc_sum {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) : F.slopesDesc.sum = deg ρ L := by
  have hdeg := F.deg_step_eq_sum hL (Fin.last F.len)
  rw [F.step_last] at hdeg
  have hf : Finset.univ.filter (fun i : Fin F.len => i.1 < (Fin.last F.len).1) = Finset.univ := by
    ext i; simp
  rw [hf] at hdeg
  rw [hdeg]
  have hsum_fm : ∀ (l : List (Fin F.len)),
      (l.flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)).sum =
      (l.map fun i => (F.rkJump i : ℝ) * F.quotSlope i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih, List.sum_replicate, nsmul_eq_mul]
  unfold slopesDesc
  rw [hsum_fm]
  exact (Fin.sum_univ_def fun i => (F.rkJump i : ℝ) * F.quotSlope i).symm

/-- `Fin (rk ρ L)`-indexed descending slope vector extracted from `F.slopesDesc`. -/
def slopeVec {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L) (F : HLatHNFilt ρ L) :
    Fin (rk ρ L) → ℝ :=
  fun j => F.slopesDesc[j.1]'(by rw [F.slopesDesc_length hL]; exact j.2)

lemma slopeVec_antitone {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L) (F : HLatHNFilt ρ L) :
    Antitone (F.slopeVec hL) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp F.slopesDesc_pairwise_ge a.1 b.1
      (by rw [F.slopesDesc_length hL]; exact a.2) (by rw [F.slopesDesc_length hL]; exact b.2) hlt

lemma sum_slopeVec {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L) (F : HLatHNFilt ρ L) :
    ∑ j : Fin (rk ρ L), F.slopeVec hL j = deg ρ L := by
  have hof : F.slopesDesc = List.ofFn (F.slopeVec hL) := by
    apply List.ext_getElem
    · rw [F.slopesDesc_length hL, List.length_ofFn]
    · intro i h1 h2; rw [List.getElem_ofFn]; rfl
  rw [← F.slopesDesc_sum hL, hof, List.sum_ofFn]

lemma card_slopeVec_ge {ρ : V →+ E} {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (θ : ℝ) :
    (Finset.univ.filter fun j : Fin (rk ρ L) => θ ≤ F.slopeVec hL j).card =
      rk ρ (hnStep ρ L θ) := by
  rw [F.hnStep_eq_step_truncIdx hL θ, F.rk_step_eq_sum hL (F.truncIdx θ)]
  have hlist_cnt : ∀ (l : List (Fin F.len)),
      ((l.flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)).countP (fun x => decide (θ ≤ x))) =
      ((l.filter fun i => decide (θ ≤ F.quotSlope i)).map fun i => F.rkJump i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, List.countP_append, ih, List.filter_cons]
      by_cases h : θ ≤ F.quotSlope a <;> simp [h, List.countP_replicate]
  have hofFn : F.slopesDesc = List.ofFn (F.slopeVec hL) := by
    apply List.ext_getElem
    · rw [F.slopesDesc_length hL, List.length_ofFn]
    · intro i h1 h2; rw [List.getElem_ofFn]; rfl
  have hcountP_fin : (Finset.univ.filter fun j : Fin (rk ρ L) => θ ≤ F.slopeVec hL j).card =
      F.slopesDesc.countP (fun x => decide (θ ≤ x)) := by
    rw [hofFn, List.countP_eq_length_filter]
    have hcp : ∀ (l : List ℝ) (p : ℝ → Bool), (l.filter p).length = (l.map p).count true := by
      intro l p
      induction l with
      | nil => simp
      | cons a l ih => cases hp : p a <;> simp [ih, hp]
    have hofBool : ∀ {n : ℕ} (p : Fin n → Bool),
        (List.ofFn p).count true = (Finset.univ.filter fun j : Fin n => p j = true).card := by
      intro n p
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.ofFn_succ, List.count_cons, ih]
        have hbij : (Finset.univ.filter fun j : Fin n => p j.succ = true).card =
            ((Finset.univ.filter fun j : Fin (n + 1) => p j = true).erase 0).card := by
          refine Finset.card_bij (fun j _ => j.succ)
            (fun j hj => Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩⟩)
            (fun _ _ _ _ h => Fin.succ_inj.mp h)
            (fun k hk => by
              rw [Finset.mem_erase, Finset.mem_filter] at hk
              refine ⟨k.pred hk.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.succ_pred k hk.1⟩
              rw [Fin.succ_pred]; exact hk.2.2)
        rw [hbij]
        cases hp0 : p 0
        · have hnot : (0 : Fin (n + 1)) ∉ Finset.univ.filter fun j : Fin (n + 1) => p j = true := by
            simp [hp0]
          rw [Finset.erase_eq_of_notMem hnot]; simp
        · have hmem : (0 : Fin (n + 1)) ∈ Finset.univ.filter fun j : Fin (n + 1) => p j = true :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ 0, hp0⟩
          have hpos := Finset.card_pos.mpr ⟨0, hmem⟩
          rw [Finset.card_erase_of_mem hmem]; simp; omega
    rw [hcp, List.map_ofFn]
    simpa only [Function.comp_def, decide_eq_true_eq] using
      (hofBool (fun j => decide (θ ≤ F.slopeVec hL j))).symm
  rw [hcountP_fin]
  unfold slopesDesc
  rw [hlist_cnt]
  have hnodup : ((List.finRange F.len).filter fun i => decide (θ ≤ F.quotSlope i)).Nodup :=
    (List.nodup_finRange F.len).filter _
  have htoFinset : ((List.finRange F.len).filter fun i => decide (θ ≤ F.quotSlope i)).toFinset =
      Finset.univ.filter fun i : Fin F.len => i.1 < (F.truncIdx θ).1 := by
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_filter, Finset.mem_univ]
    exact F.mem_filter_truncIdx_iff θ i
  rw [← List.sum_toFinset _ hnodup, htoFinset]

end HLatHNFilt

/-- **Canonical Harder–Narasimhan Slope List `hnSlopeList ρ L`**:
`hnSlopeList ρ L j = sSup {θ | j < rk ρ (hnStep ρ L θ)}` (matching `Formalism.HN.slopeList`). -/
def hnSlopeList (ρ : V →+ E) (L : Submodule R V) : Fin (rk ρ L) → ℝ :=
  fun j => sSup {θ : ℝ | (j : ℕ) < rk ρ (hnStep ρ L θ)}

/-- **Harder–Narasimhan Polygon `hnPoly ρ L k`**:
the sum of the first `k` Harder–Narasimhan slopes of `(ρ, L)`. -/
def hnPoly (ρ : V →+ E) (L : Submodule R V) (k : ℕ) : ℝ :=
  ∑ j : Fin (rk ρ L), if (j : ℕ) < k then hnSlopeList ρ L j else 0

private lemma lt_card_filter_le_iff_of_antitone {n : ℕ} {s : Fin n → ℝ}
    (hs : Antitone s) (j : Fin n) (θ : ℝ) :
    (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ s i)).card ↔ θ ≤ s j := by
  constructor
  · intro h
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hsub : Finset.univ.filter (fun i => θ ≤ s i) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hji
      have := hs (not_lt.mp hji)
      linarith
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega
  · intro h
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ s i) := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (hs (Finset.mem_Iic.mp hi))⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega

/-- Exact identification: `hnSlopeList ρ L = F.slopeVec hL` for any `F : HLatHNFilt ρ L`! -/
theorem hnSlopeList_eq_slopeVec (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) :
    hnSlopeList ρ L = F.slopeVec hL := by
  funext j
  unfold hnSlopeList
  have hset : {θ : ℝ | (j : ℕ) < rk ρ (hnStep ρ L θ)} = Set.Iic (F.slopeVec hL j) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← F.card_slopeVec_ge hL θ]
    exact lt_card_filter_le_iff_of_antitone (F.slopeVec_antitone hL) j θ
  rw [hset, csSup_Iic]

/-- `hnSlopeList ρ L` is antitone (non-increasing). -/
theorem hnSlopeList_antitone (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) :
    Antitone (hnSlopeList ρ L) := by
  let F := canonicalHLatHNFilt ρ hL
  rw [hnSlopeList_eq_slopeVec ρ hL F]
  exact F.slopeVec_antitone hL

/-- Exact count of HN slopes `≥ θ`: `#{j | θ ≤ hnSlopeList ρ L j} = rk ρ (hnStep ρ L θ)`. -/
theorem card_hnSlopeList_ge (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (θ : ℝ) :
    (Finset.univ.filter fun j : Fin (rk ρ L) => θ ≤ hnSlopeList ρ L j).card =
      rk ρ (hnStep ρ L θ) := by
  let F := canonicalHLatHNFilt ρ hL
  rw [hnSlopeList_eq_slopeVec ρ hL F]
  exact F.card_slopeVec_ge hL θ

/-- Exact count of HN slopes `< θ`: `#{j | hnSlopeList ρ L j < θ} = rk ρ L - rk ρ (hnStep ρ L θ)`. -/
theorem card_hnSlopeList_lt (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (θ : ℝ) :
    ((Finset.univ.filter fun j : Fin (rk ρ L) => hnSlopeList ρ L j < θ).card : ℝ) =
      (rk ρ L : ℝ) - rk ρ (hnStep ρ L θ) := by
  have h1 := card_hnSlopeList_ge ρ hL θ
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (rk ρ L))))
    (fun j => θ ≤ hnSlopeList ρ L j)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at h2
  have h3 : ((Finset.univ.filter fun j : Fin (rk ρ L) => θ ≤ hnSlopeList ρ L j).card : ℝ) +
      ((Finset.univ.filter fun j : Fin (rk ρ L) => hnSlopeList ρ L j < θ).card : ℝ) = (rk ρ L : ℝ) := by
    exact_mod_cast h2
  rw [h1] at h3
  linarith

/-- Sum of all Harder–Narasimhan slopes equals the Arakelov degree `deg ρ L`. -/
theorem sum_hnSlopeList (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) :
    ∑ j : Fin (rk ρ L), hnSlopeList ρ L j = deg ρ L := by
  let F := canonicalHLatHNFilt ρ hL
  rw [hnSlopeList_eq_slopeVec ρ hL F]
  exact F.sum_slopeVec hL

lemma hnPoly_zero (ρ : V →+ E) (L : Submodule R V) : hnPoly ρ L 0 = 0 := by
  simp [hnPoly]

lemma hnPoly_rk (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) :
    hnPoly ρ L (rk ρ L) = deg ρ L := by
  unfold hnPoly
  have h : ∑ j : Fin (rk ρ L), (if (j : ℕ) < rk ρ L then hnSlopeList ρ L j else 0) =
      ∑ j : Fin (rk ρ L), hnSlopeList ρ L j :=
    Finset.sum_congr rfl fun j _ => if_pos j.2
  rw [h, sum_hnSlopeList ρ hL]

lemma hnPoly_succ (ρ : V →+ E) (L : Submodule R V) {k : ℕ} (hk : k < rk ρ L) :
    hnPoly ρ L (k + 1) = hnPoly ρ L k + hnSlopeList ρ L ⟨k, hk⟩ := by
  unfold hnPoly
  have hdiff : ∀ j : Fin (rk ρ L),
      (if (j : ℕ) < k + 1 then hnSlopeList ρ L j else 0) =
      (if (j : ℕ) < k then hnSlopeList ρ L j else 0) +
      (if j = ⟨k, hk⟩ then hnSlopeList ρ L j else 0) := by
    intro j
    by_cases hjk : (j : ℕ) < k
    · have hne : j ≠ ⟨k, hk⟩ := fun h => by subst h; exact lt_irrefl k hjk
      simp [hjk, Nat.lt_succ_of_lt hjk, hne]
    · by_cases hjeq : j = ⟨k, hk⟩
      · subst hjeq; simp
      · have hjk_ge : k ≤ (j : ℕ) := not_lt.mp hjk
        have hgt : ¬ (j : ℕ) < k + 1 := by
          intro h; apply hjeq; exact Fin.ext (show (j : ℕ) = k by omega)
        simp [hjk, hjeq, hgt]
  simp_rw [hdiff, Finset.sum_add_distrib]
  simp

/-- **Concavity of the Harder–Narasimhan Polygon (`hnPoly_concave`)**:
for every `k` with `k + 1 < rk ρ L`, the successive polygon slopes are non-increasing:
`hnPoly ρ L (k + 2) - hnPoly ρ L (k + 1) ≤ hnPoly ρ L (k + 1) - hnPoly ρ L k`. -/
theorem hnPoly_concave (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L)
    {k : ℕ} (hk : k + 1 < rk ρ L) :
    hnPoly ρ L (k + 2) - hnPoly ρ L (k + 1) ≤ hnPoly ρ L (k + 1) - hnPoly ρ L k := by
  rw [hnPoly_succ ρ L hk, hnPoly_succ ρ L (Nat.lt_of_succ_lt hk)]
  have hanti := hnSlopeList_antitone ρ hL
    (show (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (rk ρ L)) ≤ ⟨k + 1, hk⟩ from Nat.le_succ k)
  linarith

/-- Clean Ky Fan bound using `List.Pairwise (· ≥ ·)` directly. -/
private lemma kyFan_sum_le_take {m : ℕ} (r d : Fin m → ℕ) (μ : Fin m → ℝ)
    (hpair : ((List.finRange m).flatMap fun i => List.replicate (r i) (μ i)).Pairwise (· ≥ ·))
    (hd_le : ∀ i, d i ≤ r i) :
    ∑ i, (d i : ℝ) * μ i ≤
      (((List.finRange m).flatMap fun i => List.replicate (r i) (μ i)).take (∑ i, d i)).sum := by
  have hky : ∀ (ls : List ℝ), ls.Pairwise (· ≥ ·) →
      ∀ (T : Multiset ℝ), T ≤ (ls : Multiset ℝ) → T.sum ≤ (ls.take T.card).sum := by
    intro ls
    induction ls with
    | nil => intro _ T hT; simp [Multiset.le_zero.mp hT]
    | cons a ls' ih =>
      intro hp T hT
      rw [List.pairwise_cons] at hp
      by_cases hT0 : T = 0
      · simp [hT0]
      · by_cases haT : a ∈ T
        · obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem haT
          have hT' : T' ≤ (ls' : Multiset ℝ) :=
            (Multiset.cons_le_cons_iff a).mp (by simpa using hT)
          have h := ih hp.2 T' hT'
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
          have hxa : x ≤ a := hp.1 x (by simpa using Multiset.mem_of_le hTls' hxT)
          have h := ih hp.2 T' (le_trans (Multiset.le_cons_self T' x) hTls')
          simp only [Multiset.card_cons, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
          linarith
  let T : Multiset ℝ := ∑ i : Fin m, Multiset.replicate (d i) (μ i)
  let ls := (List.finRange m).flatMap fun i => List.replicate (r i) (μ i)
  have hcoe : (ls : Multiset ℝ) = ∑ i : Fin m, Multiset.replicate (r i) (μ i) := by
    have h1 : ∀ (l : List (Fin m)),
        ((l.flatMap fun i => List.replicate (r i) (μ i) : List ℝ) : Multiset ℝ) =
        (l.map fun i => Multiset.replicate (r i) (μ i)).sum := by
      intro l; induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons,
          Multiset.coe_replicate]
    rw [h1]
    have h2 : (Finset.univ : Finset (Fin m)).val = (List.finRange m : Multiset (Fin m)) := by
      apply Multiset.ext.mpr; intro i
      rw [Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin m)).nodup (Finset.mem_univ i),
        Multiset.count_eq_one_of_mem (Multiset.coe_nodup.mpr (List.nodup_finRange m))
          (Multiset.mem_coe.mpr (List.mem_finRange i))]
    rw [Finset.sum_eq_multiset_sum]
    change ((List.map (fun i => Multiset.replicate (r i) (μ i)) (List.finRange m) :
      List (Multiset ℝ)) : Multiset (Multiset ℝ)).sum = _
    rw [← Multiset.map_coe, ← h2]
  have hTle : T ≤ (ls : Multiset ℝ) := by
    rw [hcoe]
    exact Finset.sum_le_sum fun i _ => Multiset.le_iff_count.mpr fun x => by
      simp only [Multiset.count_replicate]; split_ifs
      · exact hd_le i
      · exact le_rfl
  have hTcard : T.card = ∑ i, d i := by
    dsimp only [T]
    classical
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, ih]
  have hTsum : T.sum = ∑ i, (d i : ℝ) * μ i := by
    dsimp only [T]
    rw [Multiset.sum_sum]
    refine Finset.sum_congr rfl fun i _ => by simp [Multiset.sum_replicate, nsmul_eq_mul]
  have h := hky ls hpair T hTle
  rwa [hTcard, hTsum] at h

lemma hnPoly_eq_take_slopesDesc (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L)
    (F : HLatHNFilt ρ L) (k : ℕ) :
    hnPoly ρ L k = (F.slopesDesc.take k).sum := by
  induction k with
  | zero => simp [hnPoly]
  | succ k ih =>
    by_cases hk : k < rk ρ L
    · rw [hnPoly_succ ρ L hk, ih, hnSlopeList_eq_slopeVec ρ hL F]
      have hk' : k < F.slopesDesc.length := by rw [F.slopesDesc_length hL]; exact hk
      rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some,
        List.sum_append, List.sum_singleton]
      rfl
    · have hge : rk ρ L ≤ k := not_lt.mp hk
      have h1 : hnPoly ρ L (k + 1) = hnPoly ρ L k := by
        unfold hnPoly
        refine Finset.sum_congr rfl fun j _ => ?_
        have hlt1 : (j : ℕ) < k := lt_of_lt_of_le j.2 hge
        have hlt2 : (j : ℕ) < k + 1 := Nat.lt_succ_of_lt hlt1
        simp [hlt1, hlt2]
      have hlen : F.slopesDesc.length ≤ k := by rw [F.slopesDesc_length hL]; exact hge
      rw [h1, ih, List.take_of_length_le hlen, List.take_of_length_le (Nat.le_succ_of_le hlen)]

/-- **Upper Concave Envelope Theorem (`deg_le_hnPoly`)**:
for every `R`-submodule `N ≤ L`, `deg ρ N ≤ hnPoly ρ L (rk ρ N)`. -/
theorem deg_le_hnPoly (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L)
    {N : Submodule R V} (hNL : N ≤ L) :
    deg ρ N ≤ hnPoly ρ L (rk ρ N) := by
  let F := canonicalHLatHNFilt ρ hL
  let d : Fin F.len → ℕ := fun i =>
    rk ρ (N ⊓ F.step i.succ) - rk ρ (N ⊓ F.step i.castSucc)
  have htel : ∀ m : ℕ, (hm : m ≤ F.len) →
      rk ρ (N ⊓ F.step ⟨m, Nat.lt_succ_of_le hm⟩) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), d i ∧
      deg ρ (N ⊓ F.step ⟨m, Nat.lt_succ_of_le hm⟩) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), (d i : ℝ) * F.quotSlope i := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ : Fin (F.len + 1)) = 0 := Fin.ext rfl
      rw [h0, F.step_zero, inf_bot_eq, rk_bot, deg_bot]; simp
    | succ m ih =>
      intro hm
      let i_m : Fin F.len := ⟨m, hm⟩
      have hfilt : Finset.univ.filter (fun i : Fin F.len => i.1 < m + 1) =
          insert i_m (Finset.univ.filter (fun i : Fin F.len => i.1 < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, i_m]; omega
      have hnotmem : i_m ∉ Finset.univ.filter (fun i : Fin F.len => i.1 < m) := by simp [i_m]
      have hprev := ih (Nat.le_of_succ_le hm)
      have hprev1 : rk ρ (N ⊓ F.step i_m.castSucc) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), d i := hprev.1
      have hprev2 : deg ρ (N ⊓ F.step i_m.castSucc) ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin F.len => i.1 < m), (d i : ℝ) * F.quotSlope i := hprev.2
      obtain ⟨hrle, _, hdeg_step⟩ := F.sub_step_bound hL hNL i_m
      rw [hfilt, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
      refine ⟨?_, ?_⟩
      · change rk ρ (N ⊓ F.step i_m.succ) = d i_m + _
        dsimp only [d] at hprev1 ⊢; omega
      · change deg ρ (N ⊓ F.step i_m.succ) ≤ (d i_m : ℝ) * F.quotSlope i_m + _
        linarith
  have htot := htel F.len le_rfl
  have hf : Finset.univ.filter (fun i : Fin F.len => i.1 < F.len) = Finset.univ := by ext i; simp
  have hlast : N ⊓ F.step ⟨F.len, Nat.lt_succ_self _⟩ = N := by
    change N ⊓ F.step (Fin.last F.len) = N
    rw [F.step_last, inf_eq_left.mpr hNL]
  rw [hf, hlast] at htot
  rw [hnPoly_eq_take_slopesDesc ρ hL F (rk ρ N), htot.1]
  exact htot.2.trans (kyFan_sum_le_take F.rkJump d F.quotSlope F.slopesDesc_pairwise_ge
    (fun i => (F.sub_step_bound hL hNL i).2.1))

/-- **Vertex Attainment at Every Threshold `hnStep ρ L θ`**:
`deg ρ (hnStep ρ L θ) = hnPoly ρ L (rk ρ (hnStep ρ L θ))`. -/
theorem deg_hnStep_eq_hnPoly (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L) (θ : ℝ) :
    deg ρ (hnStep ρ L θ) = hnPoly ρ L (rk ρ (hnStep ρ L θ)) := by
  let F := canonicalHLatHNFilt ρ hL
  rw [F.hnStep_eq_step_truncIdx hL θ, hnPoly_eq_take_slopesDesc ρ hL F]
  let j := F.truncIdx θ
  have hsplit : List.finRange F.len = (List.finRange F.len).take j.1 ++ (List.finRange F.len).drop j.1 :=
    (List.take_append_drop j.1 _).symm
  let pref := ((List.finRange F.len).take j.1).flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)
  let suff := ((List.finRange F.len).drop j.1).flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)
  have hdesc : F.slopesDesc = pref ++ suff := by
    unfold HLatHNFilt.slopesDesc; conv_lhs => rw [hsplit, List.flatMap_append]
  have hnodup : ((List.finRange F.len).take j.1).Nodup :=
    (List.nodup_finRange F.len).sublist (List.take_sublist _ _)
  have htoFinset : ((List.finRange F.len).take j.1).toFinset =
      Finset.univ.filter fun i : Fin F.len => i.1 < j.1 := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hi
      rw [List.length_take] at hk
      rw [List.getElem_take, List.getElem_finRange] at hget
      rw [← hget]; exact lt_of_lt_of_le hk (min_le_left _ _)
    · intro hi
      have hlt : i.1 < ((List.finRange F.len).take j.1).length := by
        rw [List.length_take, List.length_finRange]; omega
      refine List.mem_iff_getElem.mpr ⟨i.1, hlt, ?_⟩
      rw [List.getElem_take, List.getElem_finRange]; ext; rfl
  have hpref_len : pref.length = rk ρ (F.step j) := by
    rw [F.rk_step_eq_sum hL j]
    dsimp only [pref]
    rw [List.length_flatMap]
    have h1 : (((List.finRange F.len).take j.1).map fun i =>
        (List.replicate (F.rkJump i) (F.quotSlope i)).length).sum =
        (((List.finRange F.len).take j.1).map F.rkJump).sum := by
      congr 1; refine List.map_congr_left fun i _ => List.length_replicate
    rw [h1, ← htoFinset, List.sum_toFinset _ hnodup]
  have hpref_sum : pref.sum = deg ρ (F.step j) := by
    rw [F.deg_step_eq_sum hL j]
    dsimp only [pref]
    have hsum_fm : ∀ (l : List (Fin F.len)),
        (l.flatMap fun i => List.replicate (F.rkJump i) (F.quotSlope i)).sum =
        (l.map fun i => (F.rkJump i : ℝ) * F.quotSlope i).sum := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih, List.sum_replicate, nsmul_eq_mul]
    rw [hsum_fm, ← htoFinset, List.sum_toFinset _ hnodup]
  rw [hdesc, ← hpref_len, List.take_left, hpref_sum]

/-- **Extremal Slopes (`HNExtreme`)**: every entry of `hnSlopeList ρ L` lies in
`[muMin ρ L, muMax ρ L]`, and both `muMax ρ L` and `muMin ρ L` are attained! -/
theorem hnSlopeList_extremes (ρ : V →+ E) {L : Submodule R V}
    (hL : IsLat ρ L) (hL0 : L ≠ ⊥) :
    (∀ j : Fin (rk ρ L), muMin ρ L ≤ hnSlopeList ρ L j ∧ hnSlopeList ρ L j ≤ muMax ρ L) ∧
    (∃ j : Fin (rk ρ L), hnSlopeList ρ L j = muMax ρ L) ∧
    (∃ j : Fin (rk ρ L), hnSlopeList ρ L j = muMin ρ L) := by
  have hrpos : 0 < rk ρ L := rk_pos_of_ne_bot' ρ hL le_rfl hL0
  have hanti := hnSlopeList_antitone ρ hL
  let j0 : Fin (rk ρ L) := ⟨0, hrpos⟩
  let jlast : Fin (rk ρ L) := ⟨rk ρ L - 1, Nat.sub_lt hrpos Nat.zero_lt_one⟩
  -- `hnSlopeList ρ L j0 = muMax ρ L`
  have hj0_eq : hnSlopeList ρ L j0 = muMax ρ L := by
    apply le_antisymm
    · -- `hnPoly ρ L 1 = hnSlopeList ρ L j0`, while `deg (hnStep θ) ≤ muMax * rk (hnStep θ)`
      have h1 : ∀ θ, (j0 : ℕ) < rk ρ (hnStep ρ L θ) → θ ≤ muMax ρ L := by
        intro θ hlt
        have hspec := hnStep_spec ρ hL θ
        have hne : hnStep ρ L θ ≠ ⊥ := fun h0 => by rw [h0, rk_bot] at hlt; omega
        have h1' := hspec.2.1 hne
        have h2' := (muMin_le_slope_le_muMax' ρ (isLat_of_le ρ hL hspec.1.1) hne).1
        have h3' : slope ρ (hnStep ρ L θ) ≤ muMax ρ L := by
          have := (muMax_le_iff ρ hL hL0 (muMax ρ L)).mp le_rfl (hnStep ρ L θ) hspec.1.1
          have hrp : (0 : ℝ) < rk ρ (hnStep ρ L θ) := Nat.cast_pos.mpr hlt
          exact (div_le_iff₀ hrp).mpr this
        linarith
      unfold hnSlopeList
      refine csSup_le ?_ h1
      refine ⟨muMin ρ L, ?_⟩
      have hL_le : L ≤ hnStep ρ L (muMin ρ L) := (hnStep_spec ρ hL (muMin ρ L)).2.2.1 L le_rfl hL0 le_rfl
      have heq : hnStep ρ L (muMin ρ L) = L := le_antisymm (hnStep_spec ρ hL _).1.1 hL_le
      show (j0 : ℕ) < rk ρ (hnStep ρ L (muMin ρ L))
      rw [heq]; exact hrpos
    · obtain ⟨N, hNsat, hN0, hNslope⟩ := (muChar_spec ρ hL hL0).2.2.1
      have h1 : deg ρ N ≤ hnPoly ρ L (rk ρ N) := deg_le_hnPoly ρ hL hNsat.1
      have h2 : hnPoly ρ L (rk ρ N) ≤ (rk ρ N : ℝ) * hnSlopeList ρ L j0 := by
        unfold hnPoly
        have hsum_le : ∑ j : Fin (rk ρ L), (if (j : ℕ) < rk ρ N then hnSlopeList ρ L j else 0) ≤
            ∑ j : Fin (rk ρ L), (if (j : ℕ) < rk ρ N then hnSlopeList ρ L j0 else 0) :=
          Finset.sum_le_sum fun j _ => by
            split_ifs
            · exact hanti (show j0 ≤ j from Nat.zero_le j.1)
            · exact le_rfl
        have hcard : (Finset.univ.filter fun j : Fin (rk ρ L) => (j : ℕ) < rk ρ N).card = rk ρ N := by
          have hrN : rk ρ N ≤ rk ρ L := rk_mono ρ hL hNsat.1 le_rfl
          have hbij : (Finset.univ.filter fun j : Fin (rk ρ L) => (j : ℕ) < rk ρ N).card =
              (Finset.range (rk ρ N)).card := by
            refine Finset.card_bij (fun j _ => j.1)
              (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
              (fun _ _ _ _ h => Fin.ext h)
              (fun k hk => ⟨⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk) hrN⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩, rfl⟩)
          rw [hbij, Finset.card_range]
        have hconst : ∑ j : Fin (rk ρ L), (if (j : ℕ) < rk ρ N then hnSlopeList ρ L j0 else 0) =
            (rk ρ N : ℝ) * hnSlopeList ρ L j0 := by
          rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]
        linarith
      have hrNpos : (0 : ℝ) < rk ρ N := Nat.cast_pos.mpr (rk_pos_of_ne_bot' ρ hL hNsat.1 hN0)
      rw [← hNslope]
      change deg ρ N / (rk ρ N : ℝ) ≤ hnSlopeList ρ L j0
      rw [div_le_iff₀ hrNpos]
      linarith
  -- `hnSlopeList ρ L jlast = muMin ρ L`
  have hjlast_eq : hnSlopeList ρ L jlast = muMin ρ L := by
    apply le_antisymm
    · -- `muMin ρ L` is bounded below by every `θ` with `jlast < rk (hnStep θ)`, i.e. `hnStep θ = L`!
      unfold hnSlopeList
      refine csSup_le ?_ ?_
      · refine ⟨muMin ρ L, ?_⟩
        have heq : hnStep ρ L (muMin ρ L) = L :=
          le_antisymm (hnStep_spec ρ hL _).1.1 ((hnStep_spec ρ hL _).2.2.1 L le_rfl hL0 le_rfl)
        show (jlast : ℕ) < rk ρ (hnStep ρ L (muMin ρ L))
        rw [heq]; exact Nat.sub_lt hrpos Nat.zero_lt_one
      · intro θ hlt
        have hspec := hnStep_spec ρ hL θ
        have hrle : rk ρ (hnStep ρ L θ) ≤ rk ρ L := rk_mono ρ hL hspec.1.1 le_rfl
        have hreq : rk ρ (hnStep ρ L θ) = rk ρ L := by
          change rk ρ L - 1 < rk ρ (hnStep ρ L θ) at hlt; omega
        have heq : hnStep ρ L θ = L := eq_of_isSat_of_rk_eq ρ hL hspec.1 hspec.1.1 le_rfl hreq
        exact heq ▸ hspec.2.1 (heq.symm ▸ hL0)
    · -- `muMin ρ L ≤ hnSlopeList ρ L jlast` because `hnStep (muMin ρ L) = L`!
      have hge := card_hnSlopeList_ge ρ hL (muMin ρ L)
      have heq : hnStep ρ L (muMin ρ L) = L :=
        le_antisymm (hnStep_spec ρ hL _).1.1 ((hnStep_spec ρ hL _).2.2.1 L le_rfl hL0 le_rfl)
      rw [heq] at hge
      exact (lt_card_filter_le_iff_of_antitone hanti jlast (muMin ρ L)).mp (hge.symm ▸ jlast.2)
  refine ⟨fun j => ⟨?_, ?_⟩, ⟨j0, hj0_eq⟩, ⟨jlast, hjlast_eq⟩⟩
  · rw [← hjlast_eq]
    exact hanti (show j ≤ jlast from by change j.1 ≤ rk ρ L - 1; have := j.2; omega)
  · rw [← hj0_eq]
    exact hanti (show j0 ≤ j from Nat.zero_le j.1)

end CanonicalHNFilt

/-! ## Section 2B: Concrete `HermVectorBundle` & `NumberFieldHLat` HN Filtration Bridges -/

section BundleAndNumberFieldBridges

/-- Canonical Harder–Narasimhan filtration of any concrete `Stage11ArakelovFaltings.HermVectorBundle`. -/
def hermBundleHNFilt (B : RHDirect.Stage11ArakelovFaltings.HermVectorBundle) :
    HLatHNFilt (AddMonoidHom.id (EuclideanSpace ℝ (Fin B.rk))) B.euclLat :=
  canonicalHLatHNFilt (AddMonoidHom.id _) ⟨Set.injOn_id _, by
    have h : zl (AddMonoidHom.id _) B.euclLat = B.euclLat := by ext x; simp [zl]
    rw [h]; exact B.discreteTopology_euclLat⟩

/-- Concavity of the HN polygon of any `Stage11ArakelovFaltings.HermVectorBundle`. -/
theorem hermBundle_hnPoly_concave (B : RHDirect.Stage11ArakelovFaltings.HermVectorBundle)
    {k : ℕ} (hk : k + 1 < rk (AddMonoidHom.id _) B.euclLat) :
    hnPoly (AddMonoidHom.id _) B.euclLat (k + 2) - hnPoly (AddMonoidHom.id _) B.euclLat (k + 1) ≤
      hnPoly (AddMonoidHom.id _) B.euclLat (k + 1) - hnPoly (AddMonoidHom.id _) B.euclLat k :=
  hnPoly_concave (AddMonoidHom.id _) ⟨Set.injOn_id _, by
    have h : zl (AddMonoidHom.id _) B.euclLat = B.euclLat := by ext x; simp [zl]
    rw [h]; exact B.discreteTopology_euclLat⟩ hk

/-- Realization `realizeHLat b X` is injective on all of `V` whenever `X v` is invertible. -/
lemma realizeHLat_injective {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Function.Injective (realizeHLat b X) := by
  intro x y hxy
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hf : fcoord b X v₀ x = fcoord b X v₀ y := by
    funext i
    have h0 := congrArg (fun w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) => w (v₀, i, 0)) hxy
    have h1 := congrArg (fun w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) => w (v₀, i, 1)) hxy
    exact Complex.ext (by simpa [realizeHLat] using h0) (by simpa [realizeHLat] using h1)
  have hv : vecAt b v₀ x = vecAt b v₀ y := by
    have h := congrArg (Matrix.mulVec (X v₀)) hf
    simpa only [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v₀), Matrix.one_mulVec] using h
  apply b.repr.injective
  ext i
  exact v₀.embedding.injective (congrFun hv i)

/-- Canonical Harder–Narasimhan filtration of any `Stage12SchurWeylLattices.NumberFieldHLat K`. -/
def numberFieldHLatHNFilt {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) :
    HLatHNFilt (realizeHLat A.b A.X) A.L :=
  canonicalHLatHNFilt (realizeHLat A.b A.X)
    ⟨(realizeHLat_injective A.b A.X A.hX).injOn, A.discReal⟩

/-- Concavity of the HN polygon of any `Stage12SchurWeylLattices.NumberFieldHLat K`. -/
theorem numberFieldHLat_hnPoly_concave {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : NumberFieldHLat K)
    {k : ℕ} (hk : k + 1 < rk (realizeHLat A.b A.X) A.L) :
    hnPoly (realizeHLat A.b A.X) A.L (k + 2) - hnPoly (realizeHLat A.b A.X) A.L (k + 1) ≤
      hnPoly (realizeHLat A.b A.X) A.L (k + 1) - hnPoly (realizeHLat A.b A.X) A.L k :=
  hnPoly_concave (realizeHLat A.b A.X)
    ⟨(realizeHLat_injective A.b A.X A.hX).injOn, A.discReal⟩ hk

end BundleAndNumberFieldBridges

/-! ## Section 3: General Bost Morphism Slope Inequality & Shift Invariance -/

section BostSlopeAndShift

variable {R V W E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Bounded `ℤ`-linear map between discrete Euclidean lattices induces a `C`-bounded map on
orthogonal quotients. -/
private lemma norm_projOrth_map_le {A : Submodule ℤ E} {B : Submodule ℤ F}
    [DiscreteTopology A] [DiscreteTopology B]
    (e : A →ₗ[ℤ] B) (C : ℝ) (hC : 0 ≤ C)
    (he : ∀ x : A, ‖((e x : B) : F)‖ ≤ C * ‖(x : E)‖)
    {S : Submodule ℤ E} {T : Submodule ℤ F} (hSA : S ≤ A)
    (hST : ∀ x : A, (x : E) ∈ S → ((e x : B) : F) ∈ T) (x : A) :
    ‖projOrth T ((e x : B) : F)‖ ≤ C * ‖projOrth S (x : E)‖ := by
  have : DiscreteTopology S := discreteTopology_of_le hSA
  let bS := Module.finBasis ℤ S
  let r := Module.finrank ℤ S
  have hspS : Submodule.span ℝ (S : Set E) = Submodule.span ℝ (Set.range fun i : Fin r => (bS i : E)) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr fun y hy => ?_
      have h1 := congrArg Subtype.val (bS.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h1
      change _ = y at h1
      rw [← h1]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (bS i).2)
  have hdiff : (x : E) - projOrth S (x : E) ∈ Submodule.span ℝ (Set.range fun i : Fin r => (bS i : E)) := by
    rw [← hspS]; exact sub_projOrth_mem_span S (x : E)
  rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hdiff
  obtain ⟨c, hc⟩ := hdiff
  -- Approximate `c` by `round (n * c i) / n` as `n → ∞`!
  let sA : Fin r → A := fun i => ⟨(bS i : E), hSA (bS i).2⟩
  have happrox : ∀ n : ℕ, 0 < n →
      (n : ℝ) * ‖projOrth T ((e x : B) : F)‖ ≤
        (n : ℝ) * (C * ‖projOrth S (x : E)‖) +
          (C * ∑ i : Fin r, ‖(bS i : E)‖ + ∑ i : Fin r, ‖((e (sA i) : B) : F)‖) := by
    intro n _
    let y : A := (n : ℤ) • x - ∑ i : Fin r, round ((n : ℝ) * c i) • sA i
    have hpy : projOrth T ((e y : B) : F) = (n : ℝ) • projOrth T ((e x : B) : F) := by
      have hey : ((e y : B) : F) = (n : ℝ) • ((e x : B) : F) -
          ∑ i : Fin r, (round ((n : ℝ) * c i) : ℝ) • ((e (sA i) : B) : F) := by
        simp only [y, map_sub, map_zsmul, map_sum, Submodule.coe_sub, Submodule.coe_smul,
          Submodule.coe_sum, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]
      rw [hey, map_sub, map_smul, map_sum]
      have hsum0 : ∑ i : Fin r, projOrth T ((round ((n : ℝ) * c i) : ℝ) • ((e (sA i) : B) : F)) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [map_smul, (projOrth_eq_zero_iff T _).mpr (Submodule.subset_span (hST (sA i) (bS i).2)),
            smul_zero]
      rw [hsum0, sub_zero]
    have hnorm_lhs : (n : ℝ) * ‖projOrth T ((e x : B) : F)‖ ≤ C * ‖(y : E)‖ := by
      have h1 : ‖(n : ℝ) • projOrth T ((e x : B) : F)‖ = (n : ℝ) * ‖projOrth T ((e x : B) : F)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
      rw [← h1, ← hpy]
      exact (norm_projOrth_le T _).trans (he y)
    have hy_decomp : (y : E) = (n : ℝ) • projOrth S (x : E) +
        ∑ i : Fin r, ((n : ℝ) * c i - (round ((n : ℝ) * c i) : ℝ)) • (bS i : E) := by
      have hx_eq' : (x : E) = projOrth S (x : E) + ∑ i : Fin r, c i • (bS i : E) := by
        rw [hc]; abel
      have hy_val : (y : E) = (n : ℝ) • (x : E) - ∑ i : Fin r, (round ((n : ℝ) * c i) : ℝ) • (bS i : E) := by
        simp only [y, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum,
          ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast, sA]
      conv_lhs => rw [hy_val, hx_eq', smul_add, Finset.smul_sum, add_sub_assoc]
      congr 1
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← sub_smul]
    have hy_norm : ‖(y : E)‖ ≤ (n : ℝ) * ‖projOrth S (x : E)‖ + ∑ i : Fin r, ‖(bS i : E)‖ := by
      rw [hy_decomp]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        have h1 := abs_sub_round ((n : ℝ) * c i)
        nlinarith [norm_nonneg (bS i : E), abs_nonneg ((n : ℝ) * c i - (round ((n : ℝ) * c i) : ℝ))]
    have hnn2 : 0 ≤ ∑ i : Fin r, ‖((e (sA i) : B) : F)‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hy_norm hC
    linarith
  by_contra hlt
  push Not at hlt
  let K : ℝ := C * ∑ i : Fin r, ‖(bS i : E)‖ + ∑ i : Fin r, ‖((e (sA i) : B) : F)‖
  have hpos : 0 < ‖projOrth T ((e x : B) : F)‖ - C * ‖projOrth S (x : E)‖ := sub_pos.mpr hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (K / (‖projOrth T ((e x : B) : F)‖ - C * ‖projOrth S (x : E)‖))
  have h1 := happrox (n + 1) (Nat.succ_pos n)
  push_cast at h1
  have h2 : ((n : ℝ) + 1) * (‖projOrth T ((e x : B) : F)‖ - C * ‖projOrth S (x : E)‖) ≤ K := by
    linarith
  have h3 := (le_div_iff₀ hpos).mpr h2
  linarith

/-- **General Bost Morphism Slope Inequality (`bost_slope_ineq_general`)** for `R`-module
Euclidean lattices (matching `Formalism.HN.SlopeIneq`):
for any `R`-linear map `φ : L →ₗ[R] M` with `‖ρ' (φ x)‖ ≤ C * ‖ρ x‖` (`C > 0`):
1. If `φ ≠ 0`, then `muMin ρ L - log C ≤ muMin ρ' (range φ)` and `muMin ρ L ≤ muMax ρ' M + log C`.
2. If `φ` is injective and `L ≠ ⊥`, then `muMax ρ L ≤ muMax ρ' M + log C`. -/
theorem bost_slope_ineq_general (ρ : V →+ E) (ρ' : W →+ F)
    {L : Submodule R V} {M : Submodule R W} (hL : IsLat ρ L) (hM : IsLat ρ' M)
    (φ : L →ₗ[R] M) (C : ℝ) (hC : 0 < C)
    (hφC : ∀ x : L, ‖ρ' (φ x : W)‖ ≤ C * ‖ρ (x : V)‖) :
    (φ ≠ 0 → muMin ρ L - Real.log C ≤ muMin ρ' ((LinearMap.range φ).map M.subtype) ∧
      muMin ρ L ≤ muMax ρ' M + Real.log C) ∧
    (Function.Injective φ → L ≠ ⊥ → muMax ρ L ≤ muMax ρ' M + Real.log C) := by
  have : DiscreteTopology (zl ρ L) := hL.2
  have : DiscreteTopology (zl ρ' M) := hM.2
  -- Build the induced `ℤ`-linear equivalence `toL : L ≃ₗ[ℤ] zl ρ L` and map `eφ : zl ρ L →ₗ[ℤ] zl ρ' M`
  let toLMap : L →ₗ[ℤ] zl ρ L :=
    { toFun := fun x => ⟨ρ x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add ρ a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul ρ c a.1) }
  have htoL_bij : Function.Bijective toLMap := by
    refine ⟨fun a b hab => Subtype.ext (hL.1 a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨y, x, hxL, rfl⟩
    exact ⟨⟨x, hxL⟩, rfl⟩
  let invL : zl ρ L ≃ₗ[ℤ] L := (LinearEquiv.ofBijective toLMap htoL_bij).symm
  have hinvL_apply : ∀ x : L, invL ⟨ρ x.1, ⟨x.1, x.2, rfl⟩⟩ = x := fun x =>
    (LinearEquiv.ofBijective toLMap htoL_bij).symm_apply_apply x
  let toM : M →ₗ[ℤ] zl ρ' M :=
    { toFun := fun w => ⟨ρ' w.1, ⟨w.1, w.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add ρ' a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul ρ' c a.1) }
  let eφ : zl ρ L →ₗ[ℤ] zl ρ' M := toM.comp ((φ.restrictScalars ℤ).comp invL.toLinearMap)
  have heφ_apply : ∀ x : L, ((eφ ⟨ρ x.1, ⟨x.1, x.2, rfl⟩⟩ : zl ρ' M) : F) = ρ' (φ x : W) := fun x => by
    change ρ' (φ (invL ⟨ρ x.1, ⟨x.1, x.2, rfl⟩⟩) : W) = ρ' (φ x : W)
    rw [hinvL_apply x]
  have heφ_lip : ∀ y : zl ρ L, ‖((eφ y : zl ρ' M) : F)‖ ≤ C * ‖(y : E)‖ := by
    intro y
    obtain ⟨x, rfl⟩ := invL.symm.surjective y
    change ‖((eφ ⟨ρ x.1, ⟨x.1, x.2, rfl⟩⟩ : zl ρ' M) : F)‖ ≤ C * ‖ρ x.1‖
    rw [heφ_apply x]
    exact hφC x
  constructor
  · intro hφ0
    have hL0 : L ≠ ⊥ := by
      intro h0; apply hφ0; ext x
      have : x = 0 := Subtype.ext ((Submodule.mem_bot R).mp (h0 ▸ x.2))
      rw [this, map_zero, LinearMap.zero_apply]
    let Im : Submodule R W := (LinearMap.range φ).map M.subtype
    have hImM : Im ≤ M := by rintro _ ⟨w, _, rfl⟩; exact w.2
    have hImLat : IsLat ρ' Im := isLat_of_le ρ' hM hImM
    have : DiscreteTopology (zl ρ' Im) := hImLat.2
    have hIm0 : Im ≠ ⊥ := by
      intro h0; apply hφ0; ext x
      have hmem : (φ x : W) ∈ Im := ⟨φ x, ⟨x, rfl⟩, rfl⟩
      rw [h0, Submodule.mem_bot] at hmem; exact hmem
    have hM0 : M ≠ ⊥ := fun h0 => hIm0 (le_bot_iff.mp (hImM.trans h0.le))
    have h1a : muMin ρ L - Real.log C ≤ muMin ρ' Im := by
      rw [le_muMin_iff ρ' hImLat hIm0]
      intro N' hN'
      obtain ⟨N'', hN'N'', hN''Im, hzl''⟩ := exists_real_saturation ρ' hImLat hN'
      have hN''sat : IsSat ρ' Im N'' := ⟨hN''Im, hzl'' ▸ isSaturated_saturation (zl_mono ρ' hN')⟩
      have hrk'' : rk ρ' N'' = rk ρ' N' := by
        unfold rk; rw [hzl'']; exact rk_saturation (zl_mono ρ' hN')
      have hdeg'' : deg ρ' N' ≤ deg ρ' N'' := deg_mono_of_rk_eq ρ' hImLat hN'N'' hN''Im hrk''.symm
      -- Pull `N''` back along `φ` to get `N ≤ L`!
      let N : Submodule R V := (N''.comap (M.subtype ∘ₗ φ)).map L.subtype
      have hNL : N ≤ L := by rintro _ ⟨x, _, rfl⟩; exact x.2
      have hNmem : ∀ x : L, (x : V) ∈ N ↔ (φ x : W) ∈ N'' := fun x => by
        constructor
        · rintro ⟨x', hx', hxx⟩; have : x' = x := Subtype.ext hxx; subst this; exact hx'
        · intro hx; exact ⟨x, hx, rfl⟩
      have hproj : ∀ x : L, ‖projOrth (zl ρ' N'') (ρ' (φ x : W))‖ ≤ C * ‖projOrth (zl ρ N) (ρ x.1)‖ := by
        intro x
        have h := norm_projOrth_map_le eφ C hC.le heφ_lip (zl_mono ρ hNL)
          (fun y hy => by
            obtain ⟨g, rfl⟩ := invL.symm.surjective y
            change ((eφ ⟨ρ g.1, ⟨g.1, g.2, rfl⟩⟩ : zl ρ' M) : F) ∈ zl ρ' N''
            rw [heφ_apply g]
            have hgN : (g : V) ∈ N := by
              rcases hy with ⟨v, hvN, hvg⟩
              have : v = g.1 := hL.1 (hNL hvN) g.2 hvg
              rwa [← this]
            exact ⟨(φ g : W), (hNmem g).mp hgN, rfl⟩)
          ⟨ρ x.1, ⟨x.1, x.2, rfl⟩⟩
        simpa only [heφ_apply x] using h
      have hNsat : IsSat ρ L N := by
        refine ⟨hNL, ⟨zl_mono ρ hNL, fun y hyL hysp => ?_⟩⟩
        rcases hyL with ⟨v, hvL, rfl⟩
        have h0 := hproj ⟨v, hvL⟩
        rw [(projOrth_eq_zero_iff (zl ρ N) (ρ v)).mpr hysp, norm_zero, mul_zero] at h0
        have h0' : projOrth (zl ρ' N'') (ρ' (φ ⟨v, hvL⟩ : W)) = 0 :=
          norm_le_zero_iff.mp h0
        have hsp'' := (projOrth_eq_zero_iff (zl ρ' N'') _).mp h0'
        have hmem_im : ρ' (φ ⟨v, hvL⟩ : W) ∈ zl ρ' Im := ⟨(φ ⟨v, hvL⟩ : W), ⟨φ ⟨v, hvL⟩, ⟨⟨v, hvL⟩, rfl⟩, rfl⟩, rfl⟩
        have hmem_z'' := hN''sat.2.2 _ hmem_im hsp''
        rcases hmem_z'' with ⟨w, hwN'', hweq⟩
        have hw_eq : w = (φ ⟨v, hvL⟩ : W) := hM.1 (hImM (hN''Im hwN'')) (φ ⟨v, hvL⟩).2 hweq
        exact ⟨v, (hNmem ⟨v, hvL⟩).mpr (hw_eq ▸ hwN''), rfl⟩
      -- Induced `ℤ`-linear isomorphism `quotLat (zl ρ L) (zl ρ N) ≃ₗ[ℤ] quotLat (zl ρ' Im) (zl ρ' N'')`
      have : DiscreteTopology (quotLat (zl ρ L) (zl ρ N)) := discreteTopology_quotLat hNsat.2
      have : DiscreteTopology (quotLat (zl ρ' Im) (zl ρ' N'')) := discreteTopology_quotLat hN''sat.2
      have hwell : ∀ a b : L, projOrth (zl ρ N) (ρ a.1) = projOrth (zl ρ N) (ρ b.1) →
          projOrth (zl ρ' N'') (ρ' (φ a : W)) = projOrth (zl ρ' N'') (ρ' (φ b : W)) := by
        intro a b hab
        have h0 : projOrth (zl ρ N) (ρ (a - b : L).1) = 0 := by
          change projOrth (zl ρ N) (ρ (a.1 - b.1)) = 0
          rw [map_sub, map_sub, hab, sub_self]
        have hle := hproj (a - b)
        rw [h0, norm_zero, mul_zero] at hle
        have h1 : projOrth (zl ρ' N'') (ρ' (φ (a - b) : W)) = 0 := norm_le_zero_iff.mp hle
        have h2 : ρ' (φ (a - b) : W) = ρ' (φ a : W) - ρ' (φ b : W) := by
          rw [map_sub, Submodule.coe_sub, map_sub]
        rw [h2, map_sub] at h1
        exact sub_eq_zero.mp h1
      have hchoose : ∀ y : quotLat (zl ρ L) (zl ρ N), ∃ x : L, projOrth (zl ρ N) (ρ x.1) = y.1 := by
        intro y
        rcases y.2 with ⟨z, ⟨x, hxL, rfl⟩, hzy⟩
        exact ⟨⟨x, hxL⟩, hzy⟩
      let qFun : quotLat (zl ρ L) (zl ρ N) → quotLat (zl ρ' Im) (zl ρ' N'') := fun y =>
        ⟨projOrth (zl ρ' N'') (ρ' (φ (hchoose y).choose : W)),
          ⟨ρ' (φ (hchoose y).choose : W), ⟨(φ (hchoose y).choose : W),
            ⟨φ (hchoose y).choose, ⟨(hchoose y).choose, rfl⟩, rfl⟩, rfl⟩, rfl⟩⟩
      have hqFun_eq : ∀ x : L,
          (qFun ⟨projOrth (zl ρ N) (ρ x.1), ⟨ρ x.1, ⟨x.1, x.2, rfl⟩, rfl⟩⟩ : quotLat (zl ρ' Im) (zl ρ' N'')).1 =
            projOrth (zl ρ' N'') (ρ' (φ x : W)) := fun x =>
        hwell _ x (hchoose _).choose_spec
      let qMap : quotLat (zl ρ L) (zl ρ N) →ₗ[ℤ] quotLat (zl ρ' Im) (zl ρ' N'') :=
        { toFun := qFun
          map_add' := fun y₁ y₂ => by
            apply Subtype.ext
            obtain ⟨x₁, hx₁⟩ := hchoose y₁
            obtain ⟨x₂, hx₂⟩ := hchoose y₂
            have hsum : y₁ + y₂ = ⟨projOrth (zl ρ N) (ρ (x₁ + x₂ : L).1),
                ⟨ρ (x₁ + x₂ : L).1, ⟨(x₁ + x₂ : L).1, (x₁ + x₂).2, rfl⟩, rfl⟩⟩ :=
              Subtype.ext (by
                change y₁.1 + y₂.1 = projOrth (zl ρ N) (ρ (x₁.1 + x₂.1))
                rw [map_add, map_add, hx₁, hx₂])
            have hy₁ : y₁ = ⟨projOrth (zl ρ N) (ρ x₁.1), ⟨ρ x₁.1, ⟨x₁.1, x₁.2, rfl⟩, rfl⟩⟩ :=
              Subtype.ext hx₁.symm
            have hy₂ : y₂ = ⟨projOrth (zl ρ N) (ρ x₂.1), ⟨ρ x₂.1, ⟨x₂.1, x₂.2, rfl⟩, rfl⟩⟩ :=
              Subtype.ext hx₂.symm
            rw [hsum, hqFun_eq (x₁ + x₂), hy₁, hy₂, Submodule.coe_add, hqFun_eq x₁, hqFun_eq x₂,
              map_add, Submodule.coe_add, map_add, map_add]
          map_smul' := fun c y => by
            apply Subtype.ext
            obtain ⟨x, hx⟩ := hchoose y
            have hsm : c • y = ⟨projOrth (zl ρ N) (ρ (c • x : L).1),
                ⟨ρ (c • x : L).1, ⟨(c • x : L).1, (c • x).2, rfl⟩, rfl⟩⟩ :=
              Subtype.ext (by
                change c • y.1 = projOrth (zl ρ N) (ρ (c • x.1))
                rw [map_zsmul, map_zsmul, hx])
            have hy : y = ⟨projOrth (zl ρ N) (ρ x.1), ⟨ρ x.1, ⟨x.1, x.2, rfl⟩, rfl⟩⟩ :=
              Subtype.ext hx.symm
            rw [hsm, hqFun_eq (c • x), hy, RingHom.id_apply, Submodule.coe_smul, hqFun_eq x,
              map_zsmul]
            change projOrth (zl ρ' N'') (ρ' (c • (φ x : W))) = c • projOrth (zl ρ' N'') (ρ' (φ x : W))
            rw [map_zsmul, map_zsmul] }
      have hqMap_inj : Function.Injective qMap := by
        intro y₁ y₂ h12
        obtain ⟨x₁, hx₁⟩ := hchoose y₁
        obtain ⟨x₂, hx₂⟩ := hchoose y₂
        have hy₁ : y₁ = ⟨projOrth (zl ρ N) (ρ x₁.1), ⟨ρ x₁.1, ⟨x₁.1, x₁.2, rfl⟩, rfl⟩⟩ :=
          Subtype.ext hx₁.symm
        have hy₂ : y₂ = ⟨projOrth (zl ρ N) (ρ x₂.1), ⟨ρ x₂.1, ⟨x₂.1, x₂.2, rfl⟩, rfl⟩⟩ :=
          Subtype.ext hx₂.symm
        have hval := congrArg (fun z : quotLat (zl ρ' Im) (zl ρ' N'') => (z : F)) h12
        change (qFun y₁).1 = (qFun y₂).1 at hval
        rw [hy₁, hy₂, hqFun_eq x₁, hqFun_eq x₂] at hval
        have h0 : projOrth (zl ρ' N'') (ρ' (φ (x₁ - x₂) : W)) = 0 := by
          rw [map_sub, Submodule.coe_sub, map_sub, map_sub, hval, sub_self]
        have hsp'' := (projOrth_eq_zero_iff (zl ρ' N'') _).mp h0
        have hmem_im : ρ' (φ (x₁ - x₂) : W) ∈ zl ρ' Im :=
          ⟨(φ (x₁ - x₂) : W), ⟨φ (x₁ - x₂), ⟨x₁ - x₂, rfl⟩, rfl⟩, rfl⟩
        rcases hN''sat.2.2 _ hmem_im hsp'' with ⟨w, hwN'', hweq⟩
        have hw_eq : w = (φ (x₁ - x₂) : W) := hM.1 (hImM (hN''Im hwN'')) (φ (x₁ - x₂)).2 hweq
        have hxN : (x₁ - x₂ : L).1 ∈ N := (hNmem (x₁ - x₂)).mpr (hw_eq ▸ hwN'')
        have hsub0 : projOrth (zl ρ N) (ρ x₁.1) - projOrth (zl ρ N) (ρ x₂.1) = 0 := by
          rw [← map_sub, ← map_sub]
          exact (projOrth_eq_zero_iff (zl ρ N) _).mpr (Submodule.subset_span ⟨(x₁ - x₂ : L).1, hxN, rfl⟩)
        rw [hy₁, hy₂]
        exact Subtype.ext (sub_eq_zero.mp hsub0)
      have hqMap_surj : Function.Surjective qMap := by
        rintro ⟨z, _, ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩, rfl⟩
        refine ⟨⟨projOrth (zl ρ N) (ρ x.1), ⟨ρ x.1, ⟨x.1, x.2, rfl⟩, rfl⟩⟩, Subtype.ext ?_⟩
        exact hqFun_eq x
      let qEquiv : quotLat (zl ρ L) (zl ρ N) ≃ₗ[ℤ] quotLat (zl ρ' Im) (zl ρ' N'') :=
        LinearEquiv.ofBijective qMap ⟨hqMap_inj, hqMap_surj⟩
      have hqMap_lip : ∀ y : quotLat (zl ρ L) (zl ρ N),
          ‖((qMap y : quotLat (zl ρ' Im) (zl ρ' N'')) : F)‖ ≤ C * ‖(y : E)‖ := by
        intro y
        obtain ⟨x, hx⟩ := hchoose y
        have hy : y = ⟨projOrth (zl ρ N) (ρ x.1), ⟨ρ x.1, ⟨x.1, x.2, rfl⟩, rfl⟩⟩ :=
          Subtype.ext hx.symm
        change ‖(qFun y).1‖ ≤ C * ‖y.1‖
        rw [hy, hqFun_eq x]
        exact hproj x
      have hdeg_q : RHDirect.ArakelovCovolume.degAr (quotLat (zl ρ L) (zl ρ N)) ≤
          RHDirect.ArakelovCovolume.degAr (quotLat (zl ρ' Im) (zl ρ' N'')) +
            (RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N)) : ℝ) * Real.log C := by
        have bQ := Module.finBasis ℤ (quotLat (zl ρ L) (zl ρ N))
        have hint : ∀ n : Fin (RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N))) → ℤ,
            ‖∑ i, (n i : ℝ) • ((bQ.map qEquiv i : quotLat (zl ρ' Im) (zl ρ' N'')) : F)‖ ≤
              C * ‖∑ i, (n i : ℝ) • (bQ i : E)‖ := by
          intro n
          have h1 := hqMap_lip (∑ i, n i • bQ i)
          simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul,
            Int.cast_smul_eq_zsmul] at h1 ⊢
          exact h1
        have hreal := norm_sum_smul_le_of_int (fun i => (bQ i : E))
          (fun i => ((bQ.map qEquiv i : quotLat (zl ρ' Im) (zl ρ' N'')) : F)) C hint
        have hdet := gram_det_le (fun i => (bQ i : E))
          (fun i => ((bQ.map qEquiv i : quotLat (zl ρ' Im) (zl ρ' N'')) : F)) C hreal
        have hcov : RHDirect.ArakelovCovolume.covol (quotLat (zl ρ' Im) (zl ρ' N'')) ≤
            C ^ RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N)) *
              RHDirect.ArakelovCovolume.covol (quotLat (zl ρ L) (zl ρ N)) := by
          rw [covol_eq_sqrt_det_gram _ (bQ.map qEquiv), covol_eq_sqrt_det_gram _ bQ]
          calc Real.sqrt (Matrix.gram ℝ (fun i => ((bQ.map qEquiv i : quotLat (zl ρ' Im) (zl ρ' N'')) : F))).det
              ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin (RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N))))) *
                  (Matrix.gram ℝ (fun i => (bQ i : E))).det) := Real.sqrt_le_sqrt hdet
            _ = C ^ RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N)) *
                  Real.sqrt (Matrix.gram ℝ (fun i => (bQ i : E))).det := by
                rw [Fintype.card_fin, show C ^ (2 * RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N))) =
                  (C ^ RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N))) ^ 2 by ring,
                  Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have hlog := Real.log_le_log (covol_pos _) hcov
        rw [Real.log_mul (pow_pos hC _).ne' (covol_pos _).ne', Real.log_pow] at hlog
        unfold RHDirect.ArakelovCovolume.degAr; linarith
      obtain ⟨_, hrq1, hle1, hdq1⟩ := quot_invariants ρ hL hNsat
      obtain ⟨_, hrq2, hle2, hdq2⟩ := quot_invariants ρ' hImLat hN''sat
      have hrk_eq_q : RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N)) =
          RHDirect.ArakelovCovolume.rk (quotLat (zl ρ' Im) (zl ρ' N'')) := qEquiv.finrank_eq
      have hMuL := (le_muMin_iff ρ hL hL0 (muMin ρ L)).mp le_rfl N hNL
      have c1 : (RHDirect.ArakelovCovolume.rk (quotLat (zl ρ L) (zl ρ N)) : ℝ) =
          (rk ρ L : ℝ) - rk ρ N := by rw [hrq1, Nat.cast_sub hle1]
      have c2 : (RHDirect.ArakelovCovolume.rk (quotLat (zl ρ' Im) (zl ρ' N'')) : ℝ) =
          (rk ρ' Im : ℝ) - rk ρ' N'' := by rw [hrq2, Nat.cast_sub hle2]
      have c3 : (rk ρ L : ℝ) - rk ρ N = (rk ρ' Im : ℝ) - rk ρ' N' := by
        rw [← hrk'', ← c2, ← c1]; exact_mod_cast hrk_eq_q
      rw [hdq1, hdq2, c1, c3] at hdeg_q
      rw [c3] at hMuL
      linarith
    refine ⟨h1a, ?_⟩
    have hImMax : muMax ρ' Im ≤ muMax ρ' M := by
      rw [muMax_le_iff ρ' hImLat hIm0]
      intro N hNIm
      exact (muMax_le_iff ρ' hM hM0 (muMax ρ' M)).mp le_rfl N (hNIm.trans hImM)
    have hord := muMin_le_slope_le_muMax' ρ' hImLat hIm0
    linarith
  · intro hinj hL0
    have hM0 : M ≠ ⊥ := by
      intro h0; apply hL0; rw [Submodule.eq_bot_iff]; intro v hv
      have h1 : φ ⟨v, hv⟩ = φ 0 := by
        rw [map_zero]; exact Subtype.ext ((Submodule.mem_bot R).mp (h0 ▸ (φ ⟨v, hv⟩).2))
      exact congrArg Subtype.val (hinj h1)
    rw [muMax_le_iff ρ hL hL0]
    intro N hNL
    let N' : Submodule R W := (N.comap L.subtype).map (M.subtype ∘ₗ φ)
    have hN'M : N' ≤ M := by rintro _ ⟨x, _, rfl⟩; exact (φ x).2
    have : DiscreteTopology (zl ρ N) := (isLat_of_le ρ hL hNL).2
    have : DiscreteTopology (zl ρ' N') := (isLat_of_le ρ' hM hN'M).2
    let eN : zl ρ N →ₗ[ℤ] zl ρ' N' :=
      { toFun := fun y =>
          ⟨((eφ ⟨y.1, zl_mono ρ hNL y.2⟩ : zl ρ' M) : F), by
            rcases (mem_zl_iff ρ N y.1).mp y.2 with ⟨v, hvN, hvy⟩
            have hy_eq : (⟨y.1, zl_mono ρ hNL y.2⟩ : zl ρ L) = ⟨ρ v, ⟨v, hNL hvN, rfl⟩⟩ :=
              Subtype.ext hvy.symm
            rw [hy_eq, heφ_apply ⟨v, hNL hvN⟩]
            exact ⟨(φ ⟨v, hNL hvN⟩ : W), ⟨⟨v, hNL hvN⟩, hvN, rfl⟩, rfl⟩⟩
        map_add' := fun a b => Subtype.ext (by
          have h : (⟨(a + b : zl ρ N).1, zl_mono ρ hNL (a + b).2⟩ : zl ρ L) =
              ⟨a.1, zl_mono ρ hNL a.2⟩ + ⟨b.1, zl_mono ρ hNL b.2⟩ := rfl
          change ((eφ ⟨(a + b : zl ρ N).1, zl_mono ρ hNL (a + b).2⟩ : zl ρ' M) : F) =
            ((eφ ⟨a.1, zl_mono ρ hNL a.2⟩ : zl ρ' M) : F) +
            ((eφ ⟨b.1, zl_mono ρ hNL b.2⟩ : zl ρ' M) : F)
          rw [h, map_add, Submodule.coe_add])
        map_smul' := fun c a => Subtype.ext (by
          have h : (⟨(c • a : zl ρ N).1, zl_mono ρ hNL (c • a).2⟩ : zl ρ L) =
              c • ⟨a.1, zl_mono ρ hNL a.2⟩ := rfl
          change ((eφ ⟨(c • a : zl ρ N).1, zl_mono ρ hNL (c • a).2⟩ : zl ρ' M) : F) =
            c • ((eφ ⟨a.1, zl_mono ρ hNL a.2⟩ : zl ρ' M) : F)
          rw [h, map_zsmul, Submodule.coe_smul]) }
    have heN_inj : Function.Injective eN := by
      intro a b hab
      apply Subtype.ext
      rcases (mem_zl_iff ρ N a.1).mp a.2 with ⟨va, hva, hya⟩
      rcases (mem_zl_iff ρ N b.1).mp b.2 with ⟨vb, hvb, hyb⟩
      have ha_eq : (⟨a.1, zl_mono ρ hNL a.2⟩ : zl ρ L) = ⟨ρ va, ⟨va, hNL hva, rfl⟩⟩ :=
        Subtype.ext hya.symm
      have hb_eq : (⟨b.1, zl_mono ρ hNL b.2⟩ : zl ρ L) = ⟨ρ vb, ⟨vb, hNL hvb, rfl⟩⟩ :=
        Subtype.ext hyb.symm
      have hval := congrArg (fun z : zl ρ' N' => (z : F)) hab
      change ((eφ ⟨a.1, zl_mono ρ hNL a.2⟩ : zl ρ' M) : F) =
        ((eφ ⟨b.1, zl_mono ρ hNL b.2⟩ : zl ρ' M) : F) at hval
      rw [ha_eq, hb_eq, heφ_apply ⟨va, hNL hva⟩, heφ_apply ⟨vb, hNL hvb⟩] at hval
      have hφeq : φ ⟨va, hNL hva⟩ = φ ⟨vb, hNL hvb⟩ :=
        Subtype.ext (hM.1 (φ ⟨va, hNL hva⟩).2 (φ ⟨vb, hNL hvb⟩).2 hval)
      have hv_eq : va = vb := congrArg Subtype.val (hinj hφeq)
      rw [← hya, ← hyb, hv_eq]
    have heN_surj : Function.Surjective eN := by
      rintro ⟨z, _, ⟨x, hxN, rfl⟩, rfl⟩
      refine ⟨⟨ρ x.1, ⟨x.1, hxN, rfl⟩⟩, Subtype.ext ?_⟩
      exact heφ_apply x
    let eqN : zl ρ N ≃ₗ[ℤ] zl ρ' N' := LinearEquiv.ofBijective eN ⟨heN_inj, heN_surj⟩
    have hrk_eq : rk ρ N = rk ρ' N' := eqN.finrank_eq
    have hdeg_le : deg ρ N ≤ deg ρ' N' + (rk ρ N : ℝ) * Real.log C := by
      let bN := Module.finBasis ℤ (zl ρ N)
      have hint : ∀ n : Fin (rk ρ N) → ℤ,
          ‖∑ i, (n i : ℝ) • ((bN.map eqN i : zl ρ' N') : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (bN i : E)‖ := by
        intro n
        have h1 := heφ_lip ⟨(∑ i, n i • bN i : zl ρ N).1, zl_mono ρ hNL (∑ i, n i • bN i).2⟩
        have h2 : ((eφ ⟨(∑ i, n i • bN i : zl ρ N).1, zl_mono ρ hNL (∑ i, n i • bN i).2⟩ : zl ρ' M) : F) =
            ((eN (∑ i, n i • bN i) : zl ρ' N') : F) := rfl
        rw [h2] at h1
        simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul,
          Int.cast_smul_eq_zsmul] at h1 ⊢
        exact h1
      have hreal := norm_sum_smul_le_of_int (fun i => (bN i : E))
        (fun i => ((bN.map eqN i : zl ρ' N') : F)) C hint
      have hdet := gram_det_le (fun i => (bN i : E))
        (fun i => ((bN.map eqN i : zl ρ' N') : F)) C hreal
      have hcov : RHDirect.ArakelovCovolume.covol (zl ρ' N') ≤
          C ^ rk ρ N * RHDirect.ArakelovCovolume.covol (zl ρ N) := by
        rw [covol_eq_sqrt_det_gram _ (bN.map eqN), covol_eq_sqrt_det_gram _ bN]
        calc Real.sqrt (Matrix.gram ℝ (fun i => ((bN.map eqN i : zl ρ' N') : F))).det
            ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin (rk ρ N))) *
                (Matrix.gram ℝ (fun i => (bN i : E))).det) := Real.sqrt_le_sqrt hdet
          _ = C ^ rk ρ N * Real.sqrt (Matrix.gram ℝ (fun i => (bN i : E))).det := by
              rw [Fintype.card_fin, show C ^ (2 * rk ρ N) = (C ^ rk ρ N) ^ 2 by ring,
                Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have hlog := Real.log_le_log (covol_pos _) hcov
      rw [Real.log_mul (pow_pos hC _).ne' (covol_pos _).ne', Real.log_pow] at hlog
      unfold deg RHDirect.ArakelovCovolume.degAr; linarith
    have hmuM := (muMax_le_iff ρ' hM hM0 (muMax ρ' M)).mp le_rfl N' hN'M
    rw [← hrk_eq] at hmuM
    linarith

/-- **Bost Truncation Inclusion for `R`-Modules**:
if `φ : L →ₗ[R] M` has norm `≤ C` (`C > 0`) and `θ + Real.log C ≤ muMin ρ L` (when `L ≠ ⊥`),
then `(LinearMap.range φ).map M.subtype ≤ hnStep ρ' M θ`. -/
theorem bost_hnStep_inclusion (ρ : V →+ E) (ρ' : W →+ F)
    {L : Submodule R V} {M : Submodule R W} (hL : IsLat ρ L) (hM : IsLat ρ' M)
    (φ : L →ₗ[R] M) (C θ : ℝ) (hC : 0 < C)
    (hφC : ∀ x : L, ‖ρ' (φ x : W)‖ ≤ C * ‖ρ (x : V)‖)
    (hmu : L ≠ ⊥ → θ + Real.log C ≤ muMin ρ L) :
    (LinearMap.range φ).map M.subtype ≤ hnStep ρ' M θ := by
  by_cases hφ0 : φ = 0
  · subst hφ0; simp
  · have hL0 : L ≠ ⊥ := by
      intro h0; apply hφ0; ext x
      have : x = 0 := Subtype.ext ((Submodule.mem_bot R).mp (h0 ▸ x.2))
      rw [this, map_zero, LinearMap.zero_apply]
    have hImM : (LinearMap.range φ).map M.subtype ≤ M := by rintro _ ⟨w, _, rfl⟩; exact w.2
    have hIm0 : (LinearMap.range φ).map M.subtype ≠ ⊥ := by
      intro h0; apply hφ0; ext x
      have hmem : (φ x : W) ∈ (LinearMap.range φ).map M.subtype := ⟨φ x, ⟨x, rfl⟩, rfl⟩
      rw [h0, Submodule.mem_bot] at hmem; exact hmem
    have hsi := ((bost_slope_ineq_general ρ ρ' hL hM φ C hC hφC).1 hφ0).1
    exact (hnStep_spec ρ' hM θ).2.2.1 _ hImM hIm0 (by linarith [hmu hL0])

private lemma isSat_iff_max_rk (ρ : V →+ E) {L : Submodule R V} (hL : IsLat ρ L)
    (N : Submodule R V) :
    IsSat ρ L N ↔
      N ≤ L ∧ ∀ N' : Submodule R V, N ≤ N' → N' ≤ L → rk ρ N' = rk ρ N → N' = N := by
  constructor
  · intro hN
    exact ⟨hN.1, fun N' hNN' hN'L hr => (eq_of_isSat_of_rk_eq ρ hL hN hNN' hN'L hr.symm).symm⟩
  · rintro ⟨hNL, hmax⟩
    obtain ⟨N', hNN', hN'L, hzl⟩ := exists_real_saturation ρ hL hNL
    have : DiscreteTopology (zl ρ L) := hL.2
    have hrk' : rk ρ N' = rk ρ N := by
      unfold rk; rw [hzl]; exact rk_saturation (zl_mono ρ hNL)
    have heq : N' = N := hmax N' hNN' hN'L hrk'
    exact ⟨hNL, heq ▸ (hzl ▸ isSaturated_saturation (zl_mono ρ hNL))⟩

/-- **Shift Invariance of HN Filtrations, Slopes, and Polygons** (`ShiftInvariance`):
if two realizations `ρ, ρ₂` of `L` satisfy `rk ρ₂ N = rk ρ N` and
`deg ρ₂ N = deg ρ N + c * rk ρ N` for all `N ≤ L`, then `IsSat`, `muMax`, `muMin`,
`hnStep`, `hnSlopeList`, and `hnPoly` all shift by `c`! -/
theorem shift_invariance {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [FiniteDimensional ℝ E₂] (ρ : V →+ E) (ρ₂ : V →+ E₂)
    {L : Submodule R V} (c : ℝ) (hL : IsLat ρ L) (hL₂ : IsLat ρ₂ L)
    (hsh : ∀ N : Submodule R V, N ≤ L → rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N + c * rk ρ N) :
    (∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N) ∧
    (L ≠ ⊥ → muMax ρ₂ L = muMax ρ L + c ∧ muMin ρ₂ L = muMin ρ L + c) ∧
    (∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ) ∧
    (∀ k : ℕ, hnPoly ρ₂ L k = hnPoly ρ L k + c * ((min k (rk ρ L) : ℕ) : ℝ)) := by
  have hmu_sub : ∀ M : Submodule R V, M ≤ L → M ≠ ⊥ →
      muMax ρ₂ M = muMax ρ M + c ∧ muMin ρ₂ M = muMin ρ M + c := by
    intro M hML hM0
    have hM := isLat_of_le ρ hL hML
    have hM₂ := isLat_of_le ρ₂ hL₂ hML
    constructor
    · apply le_antisymm
      · rw [muMax_le_iff ρ₂ hM₂ hM0]
        intro N hNM
        obtain ⟨hr, hd⟩ := hsh N (hNM.trans hML)
        have h1 := (muMax_le_iff ρ hM hM0 (muMax ρ M)).mp le_rfl N hNM
        rw [hr, hd]; linarith
      · have h2 : muMax ρ M ≤ muMax ρ₂ M - c := by
          rw [muMax_le_iff ρ hM hM0]
          intro N hNM
          obtain ⟨hr, hd⟩ := hsh N (hNM.trans hML)
          have h1 := (muMax_le_iff ρ₂ hM₂ hM0 (muMax ρ₂ M)).mp le_rfl N hNM
          rw [hr, hd] at h1; linarith
        linarith
    · apply le_antisymm
      · have h2 : muMin ρ₂ M - c ≤ muMin ρ M := by
          rw [le_muMin_iff ρ hM hM0]
          intro N hNM
          obtain ⟨hrM, hdM⟩ := hsh M hML
          obtain ⟨hrN, hdN⟩ := hsh N (hNM.trans hML)
          have h1 := (le_muMin_iff ρ₂ hM₂ hM0 (muMin ρ₂ M)).mp le_rfl N hNM
          rw [hrM, hdM, hrN, hdN] at h1; linarith
        linarith
      · rw [le_muMin_iff ρ₂ hM₂ hM0]
        intro N hNM
        obtain ⟨hrM, hdM⟩ := hsh M hML
        obtain ⟨hrN, hdN⟩ := hsh N (hNM.trans hML)
        have h1 := (le_muMin_iff ρ hM hM0 (muMin ρ M)).mp le_rfl N hNM
        rw [hrM, hdM, hrN, hdN]; linarith
  have hstep : ∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ := by
    intro θ
    unfold hnStep
    congr 1; ext N
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hNL, hN0, hθ⟩
      exact ⟨hNL, hN0, by linarith [(hmu_sub N hNL hN0).2]⟩
    · rintro ⟨hNL, hN0, hθ⟩
      exact ⟨hNL, hN0, by linarith [(hmu_sub N hNL hN0).2]⟩
  have hslope_eq : ∀ (j : ℕ) (hj₂ : j < rk ρ₂ L) (hj : j < rk ρ L),
      hnSlopeList ρ₂ L ⟨j, hj₂⟩ = hnSlopeList ρ L ⟨j, hj⟩ + c := by
    intro j hj₂ hj
    have hset : {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = Set.Iic (hnSlopeList ρ L ⟨j, hj⟩ + c) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      have hf : hnStep ρ₂ L θ = hnStep ρ L (θ - c) := by
        have := hstep (θ - c); rwa [sub_add_cancel] at this
      rw [hf, (hsh _ (hnStep_spec ρ hL (θ - c)).1.1).1, ← card_hnSlopeList_ge ρ hL (θ - c)]
      exact (lt_card_filter_le_iff_of_antitone (hnSlopeList_antitone ρ hL) ⟨j, hj⟩ (θ - c)).trans
        ⟨fun h => by linarith, fun h => by linarith⟩
    show sSup {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = hnSlopeList ρ L ⟨j, hj⟩ + c
    rw [hset, csSup_Iic]
  refine ⟨fun N => ?_, hmu_sub L le_rfl, hstep, fun k => ?_⟩
  · rw [isSat_iff_max_rk ρ₂ hL₂ N, isSat_iff_max_rk ρ hL N]
    constructor
    · rintro ⟨hNL, hm⟩
      exact ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L (by rw [(hsh N' hN'L).1, (hsh N hNL).1, hr])⟩
    · rintro ⟨hNL, hm⟩
      exact ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L (by rwa [(hsh N' hN'L).1, (hsh N hNL).1] at hr)⟩
  · have hrkL : rk ρ₂ L = rk ρ L := (hsh L le_rfl).1
    unfold hnPoly
    have hsum : ∀ {n m : ℕ} (h : m = n) (f : Fin n → ℝ) (g : Fin m → ℝ)
        (hfg : ∀ (j : ℕ) (h1 : j < m) (h2 : j < n), g ⟨j, h1⟩ = f ⟨j, h2⟩ + c),
        (∑ j : Fin m, if (j : ℕ) < k then g j else 0) =
          (∑ j : Fin n, if (j : ℕ) < k then f j else 0) + c * ((min k n : ℕ) : ℝ) := by
      intro n m h f g hfg
      subst h
      have hcnt : (∑ j : Fin m, if (j : ℕ) < k then c else 0) = c * ((min k m : ℕ) : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        have hbij : (Finset.univ.filter fun j : Fin m => (j : ℕ) < k).card =
            (Finset.range (min k m)).card := by
          refine Finset.card_bij (fun j _ => j.1)
            (fun j hj => Finset.mem_range.mpr (lt_min (Finset.mem_filter.mp hj).2 j.2))
            (fun _ _ _ _ h => Fin.ext h)
            (fun i hi => ⟨⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) (min_le_right k m)⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                lt_of_lt_of_le (Finset.mem_range.mp hi) (min_le_left k m)⟩, rfl⟩)
        rw [hbij, Finset.card_range]
      rw [← hcnt, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · exact hfg j.1 j.2 j.2
      · simp
    exact hsum hrkL (hnSlopeList ρ L) (hnSlopeList ρ₂ L) hslope_eq

end BostSlopeAndShift

/-! ## Section 4: Totally Complex Number-Field Hermitian Lattices — Place Splitting, Twist Invariance & Mean Slope Inequality -/

section NumberFieldPlaceSplitting

/-- Number of infinite places of a number field `K`. -/
def nPl (K : Type*) [Field K] [NumberField K] : ℕ :=
  Fintype.card (InfinitePlace K)

/-- Logarithmic discriminant `log |disc K|`. -/
def logDisc (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log |(NumberField.discr K : ℝ)|

/-- `K`-rank of an `𝓞 K`-submodule `L ≤ V`. -/
def rkK {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) : ℕ :=
  Module.finrank K (Submodule.span K (L : Set V))

/-- Standard Arakelov slope normalization constant `-log 2 + log |disc K| / [K : ℚ]`. -/
def slopeNormalisingConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  -Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)

section NFDefs

variable {K V W ι κ : Type*} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Normalized Arakelov slope `muDef b X L = 2 * slope (realizeHLat b X) L + c_K`. -/
def muDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * slope (realizeHLat b X) L + slopeNormalisingConstant K

/-- Normalized maximal Arakelov slope `muMaxDef b X L`. -/
def muMaxDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * muMax (realizeHLat b X) L + slopeNormalisingConstant K

/-- Normalized minimal Arakelov slope `muMinDef b X L`. -/
def muMinDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * muMin (realizeHLat b X) L + slopeNormalisingConstant K

/-- Operator norm of `φ : V →ₗ[K] W` at infinite place `v` in Hermitian frames `X, X'`. -/
def opNormAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (v : InfinitePlace K) (φ : V →ₗ[K] W) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))‖

/-- Logarithmic archimedean height of a `K`-linear morphism `φ : V →ₗ[K] W`. -/
def htMap (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, Real.log (opNormAt b X b' X' v φ ^ 2)

end NFDefs

/-- For a totally complex number field `K`, `[K : ℚ] = 2 * nPl K`. -/
theorem finrank_eq_two_mul_nPl (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * nPl K := by
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w.1)) w.2⟩
  have h3 : Nat.card {w : InfinitePlace K // w.IsComplex} = Nat.card (InfinitePlace K) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w)
  simp only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty, h3] at h1
  simp only [nPl, Fintype.card_eq_nat_card]
  omega

/-- Surjectivity of the real span of the integral basis onto `InfinitePlace K → ℂ`. -/
private theorem dense_comb (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (t : InfinitePlace K → ℂ) :
    ∃ r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ, ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = t u := by
  let y : mixedEmbedding.mixedSpace K := (0, fun w => t w.1)
  refine ⟨fun k => (mixedEmbedding.latticeBasis K).repr y k, fun u => ?_⟩
  have hu : u.IsComplex := IsTotallyComplex.isComplex u
  have hy := congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨u, hu⟩)
    ((mixedEmbedding.latticeBasis K).sum_repr y)
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, y] at hy
  rw [← hy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul]
  congr 1
  rw [NumberField.integralBasis_apply]
  rfl

/-- Coordinate subspace `placePart v` supported at a single infinite place `v`. -/
private def placePart {P ι : Type*} [Fintype P] [Fintype ι] (v : P) :
    Submodule ℝ (EuclideanSpace ℝ (P × ι × Fin 2)) where
  carrier := {w | ∀ p : P × ι × Fin 2, p.1 ≠ v → w p = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun ha hb p hp => by simp [ha p hp, hb p hp]
  smul_mem' := fun c _ hx p hp => by simp [hx p hp]

/-- Orthogonal projection onto `placePart v`. -/
private def prj {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι] (v : P) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun w := WithLp.toLp 2 fun p => if p.1 = v then w p else 0
  map_add' x y := by ext p; by_cases h : p.1 = v <;> simp [h]
  map_smul' c x := by ext p; by_cases h : p.1 = v <;> simp [h]

/-- Embedding `(ι → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2)` at place `v`. -/
private def psi {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι] (v : P) :
    (ι → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun z := WithLp.toLp 2 fun p =>
    if p.1 = v then (if p.2.2 = 0 then (z p.2.1).re else (z p.2.1).im) else 0
  map_add' x y := by ext p; by_cases h : p.1 = v <;> by_cases h' : p.2.2 = 0 <;> simp [h, h']
  map_smul' c x := by ext p; by_cases h : p.1 = v <;> by_cases h' : p.2.2 = 0 <;> simp [h, h']

private lemma psi_injective {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι] (v : P) :
    Function.Injective (psi (P := P) (ι := ι) v) := by
  intro z z' h
  funext k
  have h0 := congrArg (fun w => w (v, k, 0)) h
  have h1 := congrArg (fun w => w (v, k, 1)) h
  exact Complex.ext (by simpa [psi] using h0) (by simpa [psi] using h1)

private lemma placePart_orth {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (hvw : v ≠ w)
    {x y : EuclideanSpace ℝ (P × ι × Fin 2)} (hx : x ∈ placePart v) (hy : y ∈ placePart w) :
    inner ℝ x y = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : p.1 = v
  · rw [hy p (by rw [hp]; exact hvw), zero_mul]
  · rw [hx p hp, mul_zero]

private lemma fcoord_smul' {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x : V) :
    fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  unfold fcoord
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i; simp [vecAt, map_mul]
  rw [hv, Matrix.mulVec_smul]

private lemma fcoord_osmul' {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : 𝓞 K) (x : V) :
    fcoord b X v (a • x) = v.embedding (a : K) • fcoord b X v x := by
  rw [← algebraMap_smul K a x]
  exact fcoord_smul' b X v _ x

private lemma li_map_field {K L n m : Type*} [Field K] [Field L] (σ : K →+* L)
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (u : n → m → K) (hu : LinearIndependent K u) :
    LinearIndependent L (fun k i => σ (u k i)) := by
  let f : (n → K) →ₗ[K] (m → K) :=
    { toFun := fun c => ∑ k, c k • u k
      map_add' := fun a c => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hfinj : Function.Injective f := fun a c hac => funext fun k =>
    sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hu) (a - c) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.mpr hac) k)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hfinj)
  have hgu : ∀ k, g (u k) = Pi.single k 1 := fun k => by
    have h1 : f (Pi.single k 1) = u k := by
      show ∑ j, (Pi.single k (1 : K) : n → K) j • u j = u k; simp [Pi.single_apply]
    rw [← h1]; exact LinearMap.congr_fun hg _
  have hcoeff : ∀ k j, ∑ i, u k i * g (Pi.single i 1) j = if j = k then 1 else 0 := by
    intro k j
    have hx : u k = ∑ i, u k i • (Pi.single i (1 : K) : m → K) := by
      funext a; simp [Finset.sum_apply, Pi.single_apply]
    have h1 := congrFun (hgu k) j
    conv_lhs at h1 => rw [hx, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h1
    exact h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hsum : ∑ k, c k * (if j = k then (1 : L) else 0) = 0 := by
    have h1 : ∑ i, (∑ k, c k * σ (u k i)) * σ (g (Pi.single i 1) j) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      rw [hi, zero_mul]
    have h2 : ∑ k, c k * (if j = k then (1 : L) else 0) =
        ∑ i, (∑ k, c k * σ (u k i)) * σ (g (Pi.single i 1) j) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      have hm := congrArg σ (hcoeff k j)
      rw [map_sum] at hm
      simp only [map_mul, apply_ite σ, map_one, map_zero] at hm
      exact hm.symm
    rw [h2, h1]
  simpa [Finset.sum_ite_eq] using hsum

/-- **Complex Span Dimension at Any Infinite Place (`finrank_span_complex`)**:
`finrank ℂ (span ℂ (fcoord b X v '' N)) = rkK N`. -/
theorem finrank_span_complex {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    Module.finrank ℂ (Submodule.span ℂ (fcoord b X v '' (N : Set V))) = rkK N := by
  classical
  have hA : Function.Injective (Matrix.mulVecLin (X v)⁻¹) := fun a c h => by
    have h' := congrArg (Matrix.mulVec (X v)) h
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using h'
  have himg : fcoord b X v '' (N : Set V) = (Matrix.mulVecLin (X v)⁻¹) '' (vecAt b v '' (N : Set V)) := by
    rw [Set.image_image]; rfl
  rw [himg, ← Submodule.map_span, ← (Submodule.equivMapOfInjective _ hA _).finrank_eq]
  have : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨t, htN, hspan, hli⟩ := exists_linearIndependent K (N : Set V)
  have : Fintype t := hli.setFinite.fintype
  have hadd : ∀ x y : V, vecAt b v (x + y) = vecAt b v x + vecAt b v y := fun x y => by
    funext i; simp [vecAt]
  have hsmul : ∀ (a : K) (x : V), vecAt b v (a • x) = v.embedding a • vecAt b v x := fun a x => by
    funext i; simp [vecAt, map_mul]
  have hzero : vecAt b v 0 = 0 := by funext i; simp [vecAt]
  let y : t → ι → ℂ := fun j => vecAt b v (j : V)
  have hliC : LinearIndependent ℂ y := by
    have h1 : LinearIndependent K (fun j : t => b.equivFun (j : V)) :=
      hli.map' b.equivFun.toLinearMap b.equivFun.ker
    have h2 := li_map_field v.embedding (fun (j : t) (i : ι) => b.equivFun (j : V) i) h1
    have h3 : y = fun (j : t) (i : ι) => v.embedding (b.equivFun (j : V) i) := by
      funext j i; simp [y, vecAt, Basis.equivFun_apply]
    rwa [h3]
  have hsp : Submodule.span ℂ (vecAt b v '' (N : Set V)) = Submodule.span ℂ (Set.range y) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      let Q : Submodule K V :=
        { carrier := {x | vecAt b v x ∈ Submodule.span ℂ (Set.range y)}
          add_mem' := fun {a c} ha hc => by
            show vecAt b v (a + c) ∈ Submodule.span ℂ (Set.range y)
            rw [hadd]; exact Submodule.add_mem _ ha hc
          zero_mem' := by
            show vecAt b v 0 ∈ Submodule.span ℂ (Set.range y)
            rw [hzero]; exact Submodule.zero_mem _
          smul_mem' := fun a c hc => by
            show vecAt b v (a • c) ∈ Submodule.span ℂ (Set.range y)
            rw [hsmul]; exact Submodule.smul_mem _ _ hc }
      have hle : Submodule.span K t ≤ Q := Submodule.span_le.mpr fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      exact hle (hspan.symm ▸ Submodule.subset_span hx)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨(j : V), htN j.2, rfl⟩
  rw [hsp, finrank_span_eq_card hliC]
  unfold rkK
  rw [← hspan]
  have h3 := finrank_span_eq_card hli
  rw [Subtype.range_coe] at h3
  exact h3.symm

/-- **Place Decomposition of `span_ℝ (zl (realizeHLat b X) N)`**:
splits as the orthogonal direct sum over all infinite places `v` of `K`, with each block having
real dimension `2 * rkK N`. -/
theorem place_decomposition {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (N : Submodule (𝓞 K) V) :
    Submodule.span ℝ (zl (realizeHLat b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      ⨆ v : InfinitePlace K,
        Submodule.span ℝ (zl (realizeHLat b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓
          placePart v ∧
    ∀ v : InfinitePlace K,
      Module.finrank ℝ (Submodule.span ℝ (zl (realizeHLat b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v : Submodule ℝ _) =
        2 * rkK N := by
  classical
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  have hre_comb : ∀ (r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ)
      (c : Free.ChooseBasisIndex ℤ (𝓞 K) → ℂ) (f : ℂ),
      ∑ k, r k * (c k * f).re = ((∑ k, (r k : ℂ) * c k) * f).re := fun r c f => by
    rw [Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => by rw [mul_assoc, Complex.re_ofReal_mul]
  have him_comb : ∀ (r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ)
      (c : Free.ChooseBasisIndex ℤ (𝓞 K) → ℂ) (f : ℂ),
      ∑ k, r k * (c k * f).im = ((∑ k, (r k : ℂ) * c k) * f).im := fun r c f => by
    rw [Finset.sum_mul, Complex.im_sum]
    refine Finset.sum_congr rfl fun k _ => by rw [mul_assoc, Complex.im_ofReal_mul]
  have hprj_realize : ∀ (v : InfinitePlace K) (x : V),
      prj v (realizeHLat b X x) = psi v (fcoord b X v x) := fun v x => by
    ext p; simp only [prj, psi, realizeHLat, LinearMap.coe_mk, AddHom.coe_mk, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, WithLp.ofLp_toLp]; split_ifs with h1 h2 <;> (try subst h1) <;> rfl
  have hprj_comb : ∀ (v : InfinitePlace K) (r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ),
      (∀ u : InfinitePlace K, ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) =
        if u = v then 1 else 0) →
      ∀ x : V, prj v (realizeHLat b X x) =
        ∑ k, r k • realizeHLat b X ((RingOfIntegers.basis K k : 𝓞 K) • x) := by
    intro v r hr x
    ext p
    simp only [prj, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, WithLp.ofLp_sum,
      Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, realizeHLat,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, fcoord_osmul']
    by_cases h2 : p.2.2 = 0
    · simp only [h2, ↓reduceIte]
      rw [hre_comb r (fun k => p.1.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K))
        (fcoord b X p.1 x p.2.1), hr p.1]
      by_cases h1 : p.1 = v <;> simp [h1]
    · simp only [h2, ↓reduceIte]
      rw [him_comb r (fun k => p.1.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K))
        (fcoord b X p.1 x p.2.1), hr p.1]
      by_cases h1 : p.1 = v <;> simp [h1]
  have hprj_mem_span : ∀ (v : InfinitePlace K) (w : E),
      w ∈ Submodule.span ℝ (zl (realizeHLat b X) N : Set E) →
      prj v w ∈ Submodule.span ℝ (zl (realizeHLat b X) N : Set E) := by
    intro v w hw
    have key : Submodule.span ℝ (zl (realizeHLat b X) N : Set E) ≤
        (Submodule.span ℝ (zl (realizeHLat b X) N : Set E)).comap (prj v) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change prj v (realizeHLat b X x) ∈ Submodule.span ℝ (zl (realizeHLat b X) N : Set E)
      obtain ⟨r, hr⟩ := dense_comb K (fun u => if u = v then (1 : ℂ) else 0)
      rw [hprj_comb v r hr x]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, N.smul_mem _ hx, rfl⟩)
    exact key hw
  have hsplit : Submodule.span ℝ (zl (realizeHLat b X) N : Set E) =
      ⨆ v : InfinitePlace K, Submodule.span ℝ (zl (realizeHLat b X) N : Set E) ⊓ placePart v := by
    apply le_antisymm
    · intro w hw
      have hsum : ∑ v : InfinitePlace K, prj v w = w := by
        ext p; simp [prj, Finset.sum_ite_eq]
      rw [← hsum]
      exact Submodule.sum_mem _ fun v _ => Submodule.mem_iSup_of_mem v
        ⟨hprj_mem_span v w hw, fun p hp => by simp [prj, hp]⟩
    · exact iSup_le fun _ => inf_le_left
  refine ⟨hsplit, fun v => ?_⟩
  have hpiece : Submodule.span ℝ (zl (realizeHLat b X) N : Set E) ⊓ placePart v =
      (Submodule.span ℝ (fcoord b X v '' (N : Set V))).map (psi v) := by
    apply le_antisymm
    · rintro w ⟨hwS, hwP⟩
      have hpw : prj v w = w := by
        ext p; simp only [prj, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
        split_ifs with h
        · rfl
        · exact (hwP p h).symm
      rw [← hpw]
      have key : Submodule.span ℝ (zl (realizeHLat b X) N : Set E) ≤
          ((Submodule.span ℝ (fcoord b X v '' (N : Set V))).map (psi v)).comap (prj v) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap]
        change prj v (realizeHLat b X x) ∈ (Submodule.span ℝ (fcoord b X v '' (N : Set V))).map (psi v)
        rw [hprj_realize v x]
        exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)
      exact key hwS
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rw [← hprj_realize v x]
      exact ⟨hprj_mem_span v _ (Submodule.subset_span ⟨x, hx, rfl⟩), fun p hp => by simp [prj, hp]⟩
  have hspan_eq : (Submodule.span ℂ (fcoord b X v '' (N : Set V))).restrictScalars ℝ =
      Submodule.span ℝ (fcoord b X v '' (N : Set V)) := by
    have hmul : ∀ (c : 𝓞 K) (w : ι → ℂ), w ∈ Submodule.span ℝ (fcoord b X v '' (N : Set V)) →
        v.embedding (c : K) • w ∈ Submodule.span ℝ (fcoord b X v '' (N : Set V)) := by
      intro c w hw
      have key : Submodule.span ℝ (fcoord b X v '' (N : Set V)) ≤
          (Submodule.span ℝ (fcoord b X v '' (N : Set V))).comap
            (DistribSMul.toLinearMap ℝ (ι → ℂ) (v.embedding (c : K))) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap]
        change v.embedding (c : K) • fcoord b X v x ∈ Submodule.span ℝ (fcoord b X v '' (N : Set V))
        rw [← fcoord_osmul']; exact Submodule.subset_span ⟨c • x, N.smul_mem c hx, rfl⟩
      exact key hw
    let W : Submodule ℂ (ι → ℂ) :=
      { carrier := (Submodule.span ℝ (fcoord b X v '' (N : Set V)) : Set (ι → ℂ))
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun z w hw => by
          obtain ⟨r, hr⟩ := dense_comb K (fun _ => z)
          have hz := hr v
          rw [← hz, Finset.sum_smul]
          refine Submodule.sum_mem _ fun k _ => ?_
          rw [mul_smul, Complex.coe_smul]
          exact Submodule.smul_mem _ _ (hmul _ w hw) }
    have hle : Submodule.span ℂ (fcoord b X v '' (N : Set V)) ≤ W :=
      Submodule.span_le.mpr fun _ hx => Submodule.subset_span hx
    exact le_antisymm (fun _ hx => hle hx) (Submodule.span_le_restrictScalars ℝ ℂ _)
  rw [hpiece, ← (Submodule.equivMapOfInjective (psi v) (psi_injective v) _).finrank_eq,
    ← hspan_eq, ← finrank_span_complex b X hX N v]
  rw [← Complex.finrank_real_complex,
    Module.finrank_mul_finrank ℝ ℂ (Submodule.span ℂ (fcoord b X v '' (N : Set V)))]
  rfl

/-- **Place Lattice Structure Theorem (`place_lattice_structure`)**:
for any finitely generated `𝓞 K`-submodule `L ≤ V` and invertible archimedean frames `X v`,
`realizeHLat b X` realizes `L` as a discrete Euclidean lattice of exact rank `[K : ℚ] * rkK L`. -/
theorem place_lattice_structure {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    IsLat (realizeHLat b X) L ∧
    rk (realizeHLat b X) L = Module.finrank ℚ K * rkK L := by
  classical
  -- Step 1: Clear rational denominators of the finite generating set `s` of `L`!
  obtain ⟨s, hs⟩ := hL
  have hclear_elem : ∀ q : K, ∃ d : ℕ, 0 < d ∧ ∃ a : 𝓞 K, (a : K) = (d : K) * q := by
    intro q
    let bQ := NumberField.integralBasis K
    let d : ℕ := ∏ k, ((bQ.repr q k).den)
    have hd_pos : 0 < d := Finset.prod_pos fun k _ => (bQ.repr q k).pos
    have hcoeff : ∀ k, ∃ m : ℤ, ((d : ℚ) * bQ.repr q k) = (m : ℚ) := fun k => by
      have hdvd : (bQ.repr q k).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : ℤ) * (bQ.repr q k).num, ?_⟩
      have hden_ne : ((bQ.repr q k).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (bQ.repr q k).pos.ne'
      have hq : bQ.repr q k = ((bQ.repr q k).num : ℚ) / ((bQ.repr q k).den : ℚ) := (Rat.num_div_den _).symm
      conv_lhs => rw [hq, hc]
      push_cast; field_simp [hden_ne]
    choose m hm using hcoeff
    refine ⟨d, hd_pos, ∑ k, m k • RingOfIntegers.basis K k, ?_⟩
    have hq_eq := (bQ.sum_repr q).symm
    conv_rhs => rw [hq_eq, Finset.mul_sum]
    change algebraMap (𝓞 K) K (∑ k, m k • RingOfIntegers.basis K k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul K, smul_eq_mul,
      ← NumberField.integralBasis_apply K k]
    have hmk : ((m k : ℤ) : K) = (d : K) * ((bQ.repr q k : ℚ) : K) := by
      have h1 := congrArg (algebraMap ℚ K) (hm k).symm
      simpa [map_mul, map_intCast, map_natCast] using h1
    rw [hmk, Algebra.smul_def, mul_assoc]; rfl
  choose d_elt hd_pos ha_elt using fun p : s × ι => hclear_elem (b.repr p.1.1 p.2)
  let D : ℕ := ∏ p : s × ι, d_elt p
  have hD_pos : 0 < D := Finset.prod_pos fun p _ => hd_pos p
  have hD_L : ∀ x ∈ L, ∀ i : ι, ∃ a : 𝓞 K, (a : K) = (D : K) * b.repr x i := by
    intro x hxL
    rw [← hs] at hxL
    induction hxL using Submodule.span_induction with
    | mem g hg =>
      intro i
      have hdvd : d_elt (⟨g, hg⟩, i) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : 𝓞 K) * (ha_elt (⟨g, hg⟩, i)).choose, ?_⟩
      change algebraMap (𝓞 K) K ((c : 𝓞 K) * (ha_elt (⟨g, hg⟩, i)).choose) = _
      rw [map_mul, map_natCast]
      change (c : K) * ((ha_elt (⟨g, hg⟩, i)).choose : K) = _
      rw [(ha_elt (⟨g, hg⟩, i)).choose_spec, hc]
      push_cast; ring
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
      intro i
      obtain ⟨ax, hax⟩ := ihx i
      obtain ⟨ay, hay⟩ := ihy i
      refine ⟨ax + ay, ?_⟩
      change algebraMap (𝓞 K) K (ax + ay) = _
      rw [map_add]
      change (ax : K) + (ay : K) = _
      rw [hax, hay, map_add, Finsupp.add_apply, mul_add]
    | smul r x _ ihx =>
      intro i
      obtain ⟨ax, hax⟩ := ihx i
      refine ⟨r * ax, ?_⟩
      change algebraMap (𝓞 K) K (r * ax) = _
      rw [map_mul]
      change (r : K) * (ax : K) = _
      rw [hax, ← algebraMap_smul K r x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      change (r : K) * ((D : K) * b.repr x i) = (D : K) * ((r : K) * b.repr x i)
      ring
  -- Step 2: Continuous linear map `T : E →ₗ[ℝ] (ι → ChooseBasisIndex ℤ (𝓞 K) → ℝ)` landing in `ℤ` on `D • zl L`!
  let Tcoord : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      (ι → mixedEmbedding.mixedSpace K) :=
    { toFun := fun y i =>
        (0, fun w : {w : InfinitePlace K // w.IsComplex} =>
          (X w.1 *ᵥ fun j => (⟨y (w.1, j, 0), y (w.1, j, 1)⟩ : ℂ)) i)
      map_add' := fun y₁ y₂ => by
        funext i; apply Prod.ext; · simp
        · funext w
          have hvec : (fun j => (⟨(y₁ + y₂) (w.1, j, 0), (y₁ + y₂) (w.1, j, 1)⟩ : ℂ)) =
              (fun j => ⟨y₁ (w.1, j, 0), y₁ (w.1, j, 1)⟩) +
              (fun j => ⟨y₂ (w.1, j, 0), y₂ (w.1, j, 1)⟩) := by
            funext j; apply Complex.ext <;> simp
          simp only [Prod.snd_add, Pi.add_apply, hvec, Matrix.mulVec_add]
      map_smul' := fun r y => by
        funext i; apply Prod.ext; · simp
        · funext w
          have hvec : (fun j => (⟨(r • y) (w.1, j, 0), (r • y) (w.1, j, 1)⟩ : ℂ)) =
              ((r : ℂ)) • (fun j => ⟨y (w.1, j, 0), y (w.1, j, 1)⟩) := by
            funext j; apply Complex.ext <;> simp
          simp only [RingHom.id_apply, Prod.smul_snd, Pi.smul_apply, hvec, Matrix.mulVec_smul,
            Complex.real_smul, smul_eq_mul] }
  have hT_realize : ∀ (x : V) (i : ι), Tcoord (realizeHLat b X x) i = mixedEmbedding K (b.repr x i) := by
    intro x i
    apply Prod.ext
    · funext w; exact absurd w.2 (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w.1))
    · funext w
      have hf : (fun j => (⟨realizeHLat b X x (w.1, j, 0), realizeHLat b X x (w.1, j, 1)⟩ : ℂ)) =
          fcoord b X w.1 x := by
        funext j; apply Complex.ext <;> simp [realizeHLat]
      simp only [Tcoord, LinearMap.coe_mk, AddHom.coe_mk, hf, fcoord, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hX w.1), Matrix.one_mulVec]
      rfl
  let lb := mixedEmbedding.latticeBasis K
  let T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      (ι → Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) :=
    { toFun := fun y i k => (D : ℝ) * lb.repr (Tcoord y i) k
      map_add' := fun a c => by funext i k; simp [map_add, mul_add]
      map_smul' := fun r a => by funext i k; simp [map_smul]; ring }
  have hT_cont : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have hT_int : ∀ y : zl (realizeHLat b X) L, ∀ i k, ∃ n : ℤ, T y.1 i k = (n : ℝ) := by
    rintro ⟨_, x, hxL, rfl⟩ i k
    obtain ⟨a, ha⟩ := hD_L x hxL i
    refine ⟨(RingOfIntegers.basis K).repr a k, ?_⟩
    show (D : ℝ) * lb.repr (Tcoord (realizeHLat b X x) i) k = _
    rw [hT_realize x i]
    have hsmul : (D : ℝ) • mixedEmbedding K (b.repr x i) = mixedEmbedding K (a : K) := by
      have h1 : mixedEmbedding K (a : K) = mixedEmbedding K ((D : K) * b.repr x i) := by rw [ha]
      rw [h1, map_mul, show mixedEmbedding K (D : K) = (D : ℝ) • 1 from by
        rw [map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]]
      simp
    have hrepr : (D : ℝ) * lb.repr (mixedEmbedding K (b.repr x i)) k =
        lb.repr (mixedEmbedding K (a : K)) k := by
      rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, hsmul]
    rw [hrepr]
    have ha_sum := (RingOfIntegers.basis K).sum_repr a
    have hma : mixedEmbedding K (a : K) = ∑ j, ((RingOfIntegers.basis K).repr a j : ℝ) • lb j := by
      conv_lhs => rw [← ha_sum]
      change mixedEmbedding K (algebraMap (𝓞 K) K
        (∑ j, ((RingOfIntegers.basis K).repr a j) • RingOfIntegers.basis K j)) = _
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
      congr 1
      rw [← NumberField.integralBasis_apply K j]
      exact (mixedEmbedding.latticeBasis_apply K j).symm
    rw [hma, map_sum]
    simp [Finsupp.single_apply]
  choose nMap hnMap using hT_int
  have hDisc : DiscreteTopology (zl (realizeHLat b X) L) := by
    refine DiscreteTopology.of_continuous_injective (f := nMap) ?_ ?_
    · rw [continuous_pi_iff]; intro i; rw [continuous_pi_iff]; intro k
      have hcast : Continuous (fun y : zl (realizeHLat b X) L => ((nMap y i k : ℤ) : ℝ)) := by
        have hcomp : (fun y : zl (realizeHLat b X) L => ((nMap y i k : ℤ) : ℝ)) =
            fun y => T y.1 i k := funext fun y => (hnMap y i k).symm
        rw [hcomp]
        exact (continuous_apply k).comp ((continuous_apply i).comp (hT_cont.comp continuous_subtype_val))
      exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hcast
    · intro y₁ y₂ heq
      obtain ⟨x₁, hx₁, hy₁⟩ := (mem_zl_iff (realizeHLat b X) L y₁.1).mp y₁.2
      obtain ⟨x₂, hx₂, hy₂⟩ := (mem_zl_iff (realizeHLat b X) L y₂.1).mp y₂.2
      apply Subtype.ext
      have hTeq : ∀ i, lb.repr (mixedEmbedding K (b.repr x₁ i)) = lb.repr (mixedEmbedding K (b.repr x₂ i)) := by
        intro i; ext k
        have hk := congrFun (congrFun heq i) k
        have h1 := hnMap y₁ i k
        have h2 := hnMap y₂ i k
        have hDne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD_pos.ne'
        have heqR : (D : ℝ) * lb.repr (mixedEmbedding K (b.repr x₁ i)) k =
            (D : ℝ) * lb.repr (mixedEmbedding K (b.repr x₂ i)) k := by
          rw [← hT_realize x₁ i, ← hT_realize x₂ i, hy₁, hy₂]
          change T y₁.1 i k = T y₂.1 i k
          rw [h1, h2, hk]
        exact mul_left_cancel₀ hDne heqR
      have hx_eq : x₁ = x₂ := by
        apply b.repr.injective; ext i
        exact (mixedEmbedding K).injective (lb.repr.injective (hTeq i))
      rw [← hy₁, ← hy₂, hx_eq]
  have hLat : IsLat (realizeHLat b X) L := ⟨(realizeHLat_injective b X hX).injOn, hDisc⟩
  refine ⟨hLat, ?_⟩
  -- Step 3: Exact rank `rk = [K : ℚ] * rkK L` via orthogonal place decomposition!
  obtain ⟨hsplit, hdim⟩ := place_decomposition b X hX L
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  let W : Submodule ℝ E := Submodule.span ℝ (zl (realizeHLat b X) L : Set E)
  let k : InfinitePlace K → ℕ := fun v => Module.finrank ℝ (W ⊓ placePart v : Submodule ℝ E)
  let B : ∀ v, OrthonormalBasis (Fin (k v)) ℝ (W ⊓ placePart v : Submodule ℝ E) :=
    fun v => stdOrthonormalBasis ℝ _
  let f : (Σ v, Fin (k v)) → E := fun a => (B a.1 a.2 : E)
  have hfW : ∀ a, f a ∈ W ⊓ placePart a.1 := fun a => (B a.1 a.2).2
  have hfon : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, i⟩ ⟨w, j⟩
    by_cases hvw : v = w
    · subst hvw
      have h1 := orthonormal_iff_ite.mp (B v).orthonormal i j
      rw [Submodule.coe_inner] at h1
      by_cases hij : i = j
      · subst hij; simpa only [f, ↓reduceIte] using h1
      · rw [if_neg hij] at h1
        have hne : (⟨v, i⟩ : Σ v, Fin (k v)) ≠ ⟨v, j⟩ :=
          fun h => hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        rw [if_neg hne]
        exact h1
    · rw [if_neg (fun h => hvw (congrArg Sigma.fst h))]
      exact placePart_orth hvw (hfW ⟨v, i⟩).2 (hfW ⟨w, j⟩).2
  have hspanf : Submodule.span ℝ (Set.range f) = W := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact (hfW a).1)
    · conv_lhs => rw [show W = ⨆ v : InfinitePlace K, W ⊓ placePart v from hsplit]
      refine iSup_le fun v => fun x hx => ?_
      have key : ((∑ i, inner ℝ (B v i) (⟨x, hx⟩ : (W ⊓ placePart v : Submodule ℝ E)) • B v i :
          (W ⊓ placePart v : Submodule ℝ E)) : E) = x := by rw [(B v).sum_repr']
      rw [← key, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, i⟩, rfl⟩)
  unfold rk RHDirect.ArakelovCovolume.rk
  rw [finrank_int_eq_finrank_real_span (zl (realizeHLat b X) L)]
  change Module.finrank ℝ W = _
  rw [← hspanf, finrank_span_eq_card hfon.linearIndependent, Fintype.card_sigma]
  simp_rw [Fintype.card_fin]
  have hk_eq : ∀ v, k v = 2 * rkK L := hdim
  simp_rw [hk_eq]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, finrank_eq_two_mul_nPl K]
  unfold nPl
  ring

/-- Per-place rescaling linear map `rscMap c` multiplying place `v` by `(c v)⁻¹`. -/
private def rscMap {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun w := WithLp.toLp 2 fun p => (c p.1)⁻¹ * w p
  map_add' x y := by ext p; simp [mul_add]
  map_smul' r x := by ext p; simp; ring

/-- Exact Gram determinant scaling under a block-orthogonal scaling operator. -/
private theorem gram_block_det_rescale {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ]
    [DecidableEq P] [DecidableEq ι] [DecidableEq κ]
    (c : P → ℝ) (_hc : ∀ v, 0 < c v)
    (W : Submodule ℝ (EuclideanSpace ℝ (P × ι × Fin 2)))
    (u : κ → EuclideanSpace ℝ (P × ι × Fin 2))
    (hW : W = ⨆ v : P, W ⊓ placePart v)
    (hu : LinearIndependent ℝ u) (hspan : Submodule.span ℝ (Set.range u) = W) :
    (Matrix.gram ℝ (fun i => rscMap c (u i))).det =
      (∏ v : P, (c v)⁻¹ ^ (2 * Module.finrank ℝ (W ⊓ placePart v : Submodule ℝ _))) *
        (Matrix.gram ℝ u).det := by
  let k : P → ℕ := fun v => Module.finrank ℝ (W ⊓ placePart v : Submodule ℝ _)
  let B : ∀ v, OrthonormalBasis (Fin (k v)) ℝ (W ⊓ placePart v : Submodule ℝ _) :=
    fun v => stdOrthonormalBasis ℝ _
  let f : (Σ v, Fin (k v)) → EuclideanSpace ℝ (P × ι × Fin 2) := fun a => (B a.1 a.2 : _)
  have hfW : ∀ a, f a ∈ W ⊓ placePart a.1 := fun a => (B a.1 a.2).2
  have hfon : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, i⟩ ⟨w, j⟩
    by_cases hvw : v = w
    · subst hvw
      have h1 := orthonormal_iff_ite.mp (B v).orthonormal i j
      rw [Submodule.coe_inner] at h1
      by_cases hij : i = j
      · subst hij; simpa only [f, ↓reduceIte] using h1
      · rw [if_neg hij] at h1
        have hne : (⟨v, i⟩ : Σ v, Fin (k v)) ≠ ⟨v, j⟩ :=
          fun h => hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        rw [if_neg hne]
        exact h1
    · rw [if_neg (fun h => hvw (congrArg Sigma.fst h))]
      exact placePart_orth hvw (hfW ⟨v, i⟩).2 (hfW ⟨w, j⟩).2
  have hspanf : Submodule.span ℝ (Set.range f) = W := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact (hfW a).1)
    · conv_lhs => rw [hW]
      refine iSup_le fun v => fun x hx => ?_
      have key : ((∑ i, inner ℝ (B v i) (⟨x, hx⟩ : (W ⊓ placePart v : Submodule ℝ _)) • B v i :
          (W ⊓ placePart v : Submodule ℝ _)) : _) = x := by rw [(B v).sum_repr']
      rw [← key, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, i⟩, rfl⟩)
  have hcard : Fintype.card (Σ v, Fin (k v)) = Fintype.card κ := by
    have h1 := finrank_span_eq_card hfon.linearIndependent
    have h2 := finrank_span_eq_card hu
    rw [hspanf] at h1; rw [hspan] at h2; omega
  let e : κ ≃ Σ v, Fin (k v) := (Fintype.equivOfCardEq hcard).symm
  let f' : κ → EuclideanSpace ℝ (P × ι × Fin 2) := f ∘ e
  have hf'on : Orthonormal ℝ f' := hfon.comp e e.injective
  have hspan' : Submodule.span ℝ (Set.range f') = W := by
    rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]; exact hspanf
  have hex : ∀ j, ∃ a : κ → ℝ, ∑ i, a i • f' i = u j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan'.symm ▸ hspan.symm ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose a ha using hex
  let M : Matrix κ κ ℝ := fun i j => a j i
  have huM : u = fun j => ∑ i, M i j • f' i := funext fun j => (ha j).symm
  have hgram_comb : ∀ (T : EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2)),
      Matrix.gram ℝ (fun j => T (∑ i, M i j • f' i)) =
        M.transpose * Matrix.gram ℝ (fun i => T (f' i)) * M := by
    intro T; ext r s
    simp only [Matrix.gram_apply, map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm]; ring
  have hG1 : Matrix.gram ℝ f' = 1 := by
    ext i j; rw [Matrix.gram_apply, orthonormal_iff_ite.mp hf'on, Matrix.one_apply]
  have hGu : (Matrix.gram ℝ u).det = M.det ^ 2 := by
    have h := hgram_comb LinearMap.id
    simp only [LinearMap.id_apply, ← huM] at h
    rw [h, hG1, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose]; ring
  have hGT : (Matrix.gram ℝ (fun i => rscMap c (u i))).det =
      M.det ^ 2 * (Matrix.gram ℝ (fun i => rscMap c (f' i))).det := by
    have h := hgram_comb (rscMap c)
    have h' : (fun j => rscMap c (∑ i, M i j • f' i)) = fun j => rscMap c (u j) :=
      funext fun j => by rw [show ∑ i, M i j • f' i = u j from ha j]
    rw [h'] at h
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  have hreidx : (Matrix.gram ℝ (fun i => rscMap c (f' i))).det =
      (Matrix.gram ℝ (fun a => rscMap c (f a))).det := by
    have h1 : Matrix.gram ℝ (fun i => rscMap c (f' i)) =
        (Matrix.gram ℝ (fun a => rscMap c (f a))).submatrix e e := by ext i j; rfl
    rw [h1, Matrix.det_submatrix_equiv_self]
  have hdiag : Matrix.gram ℝ (fun a => rscMap c (f a)) =
      Matrix.diagonal (fun a : Σ v, Fin (k v) => (c a.1)⁻¹ ^ 2) := by
    ext a b
    rw [Matrix.gram_apply, Matrix.diagonal_apply]
    have hTinner : ∀ v, ∀ x ∈ placePart (ι := ι) v, ∀ y ∈ placePart (ι := ι) v,
        inner ℝ (rscMap c x) (rscMap c y) = (c v)⁻¹ ^ 2 * inner ℝ x y := by
      intro v x hx y hy
      rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      change ((c p.1)⁻¹ * y p) * ((c p.1)⁻¹ * x p) = (c v)⁻¹ ^ 2 * (y p * x p)
      by_cases hp : p.1 = v
      · rw [hp]; ring
      · rw [hx p hp]; ring
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, hTinner a.1 _ (hfW a).2 _ (hfW a).2, real_inner_self_eq_norm_sq,
        hfon.1 a, one_pow, mul_one]
    · rw [if_neg hab]
      by_cases hv : a.1 = b.1
      · have h2 : inner ℝ (f a) (f b) = 0 := by rw [orthonormal_iff_ite.mp hfon, if_neg hab]
        have hb' : f b ∈ placePart a.1 := hv ▸ (hfW b).2
        rw [hTinner a.1 _ (hfW a).2 _ hb', h2, mul_zero]
      · have ha' : rscMap c (f a) ∈ placePart a.1 := fun p hp => by
          change (c p.1)⁻¹ * f a p = 0; rw [(hfW a).2 p hp, mul_zero]
        have hb' : rscMap c (f b) ∈ placePart b.1 := fun p hp => by
          change (c p.1)⁻¹ * f b p = 0; rw [(hfW b).2 p hp, mul_zero]
        exact placePart_orth hv ha' hb'
  rw [hGT, hGu, hreidx, hdiag, Matrix.det_diagonal, Fintype.prod_sigma]
  have hprod : (∏ v : P, ∏ _i : Fin (k v), (c v)⁻¹ ^ 2) = ∏ v : P, (c v)⁻¹ ^ (2 * k v) := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hprod, mul_comm]

/-- **Per-Place Rescaling Covolume Formula (`rescale_covolume_formula`)**:
scaling `X v ↦ (c v : ℂ) • X v` (`c v > 0`) multiplies `covol (zl (realizeHLat b X) N)`
by `(∏ v, c v) ^ (-(2 * rkK N : ℝ))`. -/
theorem rescale_covolume_formula {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (c : InfinitePlace K → ℝ)
    (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v) (N : Submodule (𝓞 K) V) (hN : N.FG) :
    RHDirect.ArakelovCovolume.covol (zl (realizeHLat b fun v => ((c v : ℂ)) • X v) N) =
      (∏ v : InfinitePlace K, c v) ^ (-(2 * (rkK N : ℝ))) *
        RHDirect.ArakelovCovolume.covol (zl (realizeHLat b X) N) := by
  classical
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := fun v => by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)
  have hρ' : ∀ x : V, realizeHLat b (fun v => ((c v : ℂ)) • X v) x = rscMap c (realizeHLat b X x) := by
    intro x; ext p
    have hinv : (((c p.1 : ℂ)) • X p.1)⁻¹ = ((c p.1 : ℂ))⁻¹ • (X p.1)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      have hc0 : ((c p.1 : ℂ)) ≠ 0 := by exact_mod_cast (hc p.1).ne'
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.nonsing_inv_mul _ (hX p.1)]
    have hfc : fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x = ((c p.1 : ℂ))⁻¹ • fcoord b X p.1 x := by
      unfold fcoord; rw [hinv, Matrix.smul_mulVec]
    simp only [realizeHLat, rscMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, WithLp.ofLp_toLp, hfc, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [← Complex.ofReal_inv]
  have hL' : zl (realizeHLat b fun v => ((c v : ℂ)) • X v) N =
      (zl (realizeHLat b X) N).map ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    ext y; simp only [mem_zl_iff, Submodule.mem_map, LinearMap.coe_restrictScalars]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, (hρ' x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, hρ' x⟩
  have hinj : Function.Injective (rscMap (ι := ι) c) := fun x y hxy => by
    ext p
    have hp := congrArg (fun w => w p) hxy
    exact mul_left_cancel₀ (inv_ne_zero (hc p.1).ne') hp
  have hLd : DiscreteTopology (zl (realizeHLat b X) N) := (place_lattice_structure b X hX N hN).1.2
  have hL'd : DiscreteTopology (zl (realizeHLat b fun v => ((c v : ℂ)) • X v) N) :=
    (place_lattice_structure b _ hX' N hN).1.2
  rw [hL'] at hL'd ⊢
  let L := zl (realizeHLat b X) N
  let bL := Module.finBasis ℤ L
  let e := Submodule.equivMapOfInjective ((rscMap (ι := ι) c).restrictScalars ℤ) hinj L
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  let bM := bL.map e
  have hbM : (fun i => ((bM i : _) : E)) = fun i => rscMap (ι := ι) c (bL i) := funext fun _ => rfl
  rw [covol_eq_sqrt_det_gram _ bM, covol_eq_sqrt_det_gram L bL, hbM]
  obtain ⟨hsplit, hdim⟩ := place_decomposition b X hX N
  have hspan : Submodule.span ℝ (Set.range fun i => (bL i : E)) = Submodule.span ℝ (L : Set E) := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (bL i).2)
    · refine Submodule.span_le.mpr fun x hx => ?_
      have h1 := congrArg Subtype.val (bL.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h1; change _ = x at h1; rw [← h1]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hG := gram_block_det_rescale c hc (Submodule.span ℝ (L : Set E)) (fun i => (bL i : E))
    hsplit (linearIndependent_coe_basis L bL) hspan
  dsimp only [L, E] at hG
  simp only [hdim] at hG
  rw [hG, Real.sqrt_mul (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.mpr (hc v).le) _)]
  congr 1
  have hsq : (∏ v : InfinitePlace K, (c v)⁻¹ ^ (2 * (2 * rkK N))) =
      (∏ v : InfinitePlace K, (c v)⁻¹ ^ (2 * rkK N)) ^ 2 := by
    rw [← Finset.prod_pow]; refine Finset.prod_congr rfl fun v _ => by ring
  rw [hsq, Real.sqrt_sq (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.mpr (hc v).le) _),
    Real.rpow_neg (Finset.prod_nonneg fun v _ => (hc v).le),
    show (2 * (rkK N : ℝ)) = ((2 * rkK N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => inv_pow _ _

/-- **Twist Invariance (`twist_invariance`)**:
rescaling `X v ↦ (c v : ℂ) • X v` (`c v > 0`) shifts `muMax`, `muMin`, and `slope` by
`(1 / nPl K) * ∑ v, log (c v)` (in particular leaving them invariant when `∏ v, c v = 1`). -/
theorem twist_invariance {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (c : InfinitePlace K → ℝ)
    (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    let δ : ℝ := (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, Real.log (c v)
    muMax (realizeHLat b fun v => ((c v : ℂ)) • X v) L = muMax (realizeHLat b X) L + δ ∧
    muMin (realizeHLat b fun v => ((c v : ℂ)) • X v) L = muMin (realizeHLat b X) L + δ ∧
    slope (realizeHLat b fun v => ((c v : ℂ)) • X v) L = slope (realizeHLat b X) L + δ := by
  intro δ
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := fun v => by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)
  have hfg : ∀ N : Submodule (𝓞 K) V, N ≤ L → N.FG := fun N hN => by
    have := isNoetherian_of_fg_of_noetherian L hL
    have h1 : (N.comap L.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2
  have hnPl : (nPl K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfr : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by exact_mod_cast finrank_eq_two_mul_nPl K
  have hP : 0 < ∏ v : InfinitePlace K, c v := Finset.prod_pos fun v _ => hc v
  have hlogP : Real.log (∏ v : InfinitePlace K, c v) = ∑ v : InfinitePlace K, Real.log (c v) :=
    Real.log_prod fun v _ => (hc v).ne'
  have hkey : ∀ N : Submodule (𝓞 K) V, N ≤ L →
      rk (realizeHLat b fun v => ((c v : ℂ)) • X v) N = rk (realizeHLat b X) N ∧
      deg (realizeHLat b fun v => ((c v : ℂ)) • X v) N =
        deg (realizeHLat b X) N + δ * (rk (realizeHLat b X) N : ℝ) := by
    intro N hN
    have hNfg := hfg N hN
    obtain ⟨hlat, hrk⟩ := place_lattice_structure b X hX N hNfg
    obtain ⟨_, hrk₂⟩ := place_lattice_structure b _ hX' N hNfg
    refine ⟨by rw [hrk, hrk₂], ?_⟩
    have hcov := rescale_covolume_formula b X c hX hc N hNfg
    have : DiscreteTopology (zl (realizeHLat b X) N) := hlat.2
    have hC := covol_pos (zl (realizeHLat b X) N)
    unfold deg RHDirect.ArakelovCovolume.degAr
    rw [hcov, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hC.ne', Real.log_rpow hP, hlogP, hrk]
    push_cast; rw [hfr]; dsimp only [δ]; field_simp [hnPl]; ring
  obtain ⟨hlatL, hrkL⟩ := place_lattice_structure b X hX L hL
  obtain ⟨hlatL₂, _⟩ := place_lattice_structure b _ hX' L hL
  have hsh := shift_invariance (realizeHLat b X) (realizeHLat b fun v => ((c v : ℂ)) • X v)
    δ hlatL hlatL₂ hkey
  refine ⟨(hsh.2.1 hL0).1, (hsh.2.1 hL0).2, ?_⟩
  have hrpos : (0 : ℝ) < (rk (realizeHLat b X) L : ℝ) :=
    Nat.cast_pos.mpr (rk_pos_of_ne_bot' _ hlatL le_rfl hL0)
  obtain ⟨hr, hd⟩ := hkey L le_rfl
  unfold slope RHDirect.ArakelovCovolume.slope
  change deg (realizeHLat b fun v => ((c v : ℂ)) • X v) L /
      (rk (realizeHLat b fun v => ((c v : ℂ)) • X v) L : ℝ) =
    deg (realizeHLat b X) L / (rk (realizeHLat b X) L : ℝ) + δ
  rw [hr, hd]
  field_simp [hrpos.ne']

/-- Helper: `fcoord` transforms via `(X' v)⁻¹ * (toMatrix b b' φ).map v.embedding * X v`. -/
lemma fcoord_map_eq {K V W ι κ : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (φ : V →ₗ[K] W) (x : V) :
    fcoord b' X' v (φ x) =
      ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v).mulVec (fcoord b X v x) := by
  have hv : vecAt b' v (φ x) =
      ((LinearMap.toMatrix b b' φ).map v.embedding).mulVec (vecAt b v x) := by
    funext i
    simp only [vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b' φ x]
    simp [vecAt, Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v),
    Matrix.mul_one]

/-- **Mean Slope Inequality (`slope_inequality_mean`)** for morphisms of number-field Hermitian lattices:
for any `φ : V →ₗ[K] W` and finitely generated `A : Submodule (𝓞 K) V` with `A.map φ ≠ ⊥`,
1. `muMinDef b X A - htMap b X b' X' φ ≤ muMinDef b' X' (A.map (φ.restrictScalars (𝓞 K)))`,
2. for any `B.FG` with `A.map φ ≤ B`, `muMinDef b X A ≤ muMaxDef b' X' B + htMap b X b' X' φ`. -/
theorem slope_inequality_mean {K V W ι κ : Type*} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hφA : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥) :
    muMinDef b X A - htMap b X b' X' φ ≤ muMinDef b' X' (A.map (φ.restrictScalars (𝓞 K))) ∧
    ∀ B : Submodule (𝓞 K) W, B.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ B →
      muMinDef b X A ≤ muMaxDef b' X' B + htMap b X b' X' φ := by
  have hφ : φ ≠ 0 := by
    rintro rfl; apply hφA; rw [LinearMap.restrictScalars_zero, Submodule.map_zero]
  have hpos : ∀ v : InfinitePlace K, 0 < opNormAt b X b' X' v φ := by
    intro v
    rw [opNormAt, norm_pos_iff]
    intro h0; apply hφ
    have hA0 := Matrix.toEuclideanLin.map_eq_zero_iff.mp (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0)
    have hΦ : (LinearMap.toMatrix b b' φ).map v.embedding = 0 := by
      have e : (LinearMap.toMatrix b b' φ).map v.embedding =
          X' v * ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) * (X v)⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul]
      rw [e, hA0, Matrix.mul_zero, Matrix.zero_mul]
    exact (LinearMap.toMatrix b b').map_eq_zero_iff.mp (Matrix.ext fun i j =>
      v.embedding.injective (by simpa using congrFun (congrFun hΦ i) j))
  have hnf : (nPl K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let s : ℝ := htMap b X b' X' φ / 2
  have hs' : s = (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, Real.log (opNormAt b X b' X' v φ) := by
    dsimp only [s, htMap]
    rw [Finset.sum_congr rfl fun v _ => Real.log_pow (opNormAt b X b' X' v φ) 2,
      ← Finset.mul_sum]; push_cast; ring
  let c : InfinitePlace K → ℝ := fun v => opNormAt b X b' X' v φ * Real.exp (-s)
  have hc : ∀ v, 0 < c v := fun v => mul_pos (hpos v) (Real.exp_pos _)
  have hsum_log_c : ∑ v : InfinitePlace K, Real.log (c v) = 0 := by
    have h1 : ∑ v : InfinitePlace K, Real.log (c v) =
        (∑ v : InfinitePlace K, Real.log (opNormAt b X b' X' v φ)) - (nPl K : ℝ) * s := by
      simp_rw [c, Real.log_mul (hpos _).ne' (Real.exp_pos _).ne', Real.log_exp,
        Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]; unfold nPl; ring
    rw [h1, hs']; field_simp [hnf]; ring
  let X'' : InfinitePlace K → Matrix κ κ ℂ := fun v => ((c v : ℂ)) • X' v
  have hX'' : ∀ v, IsUnit (X'' v).det := fun v => by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX' v)
  -- At every place `v`, `opNormAt b X b' X'' v φ = exp s`, hence `‖realizeHLat b' X'' (φ x)‖ ≤ exp s * ‖realizeHLat b X x‖`!
  have hop_eq : ∀ v, opNormAt b X b' X'' v φ = Real.exp s := by
    intro v
    have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
    have hinv : (X'' v)⁻¹ = ((c v : ℂ))⁻¹ • (X' v)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.nonsing_inv_mul _ (hX' v)]
    have h1 : opNormAt b X b' X'' v φ = (c v)⁻¹ * opNormAt b X b' X' v φ := by
      simp only [opNormAt, hinv, Matrix.smul_mul, map_smul, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (hc v).le]
    rw [h1]; dsimp only [c]
    rw [mul_inv, Real.exp_neg, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hpos v).ne', one_mul]
  have hbound : ∀ x : V, ‖realizeHLat b' X'' (φ x)‖ ≤ Real.exp s * ‖realizeHLat b X x‖ := by
    intro x
    have hpl : ∀ v : InfinitePlace K, normAt b' X'' v (φ x) ≤ Real.exp s * normAt b X v x := by
      intro v
      have h1 : normAt b' X'' v (φ x) ≤ opNormAt b X b' X'' v φ * normAt b X v x := by
        unfold normAt opNormAt
        have hcnormκ : ∀ z : κ → ℂ, Real.sqrt (∑ i, ‖z i‖ ^ 2) = ‖WithLp.toLp 2 z‖ := fun z => by
          rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 z)), EuclideanSpace.norm_sq_eq]
        have hcnormι : ∀ z : ι → ℂ, Real.sqrt (∑ i, ‖z i‖ ^ 2) = ‖WithLp.toLp 2 z‖ := fun z => by
          rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 z)), EuclideanSpace.norm_sq_eq]
        rw [fcoord_map_eq b X b' X'' hX v φ x, hcnormκ, hcnormι]
        exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
          ((X'' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))).le_opNorm
          (WithLp.toLp 2 (fcoord b X v x))
      rwa [hop_eq v] at h1
    have hsq : ‖realizeHLat b' X'' (φ x)‖ ^ 2 ≤ (Real.exp s * ‖realizeHLat b X x‖) ^ 2 := by
      rw [mul_pow, norm_sq_realizeHLat, norm_sq_realizeHLat, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpl v) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hAlat := (place_lattice_structure b X hX A hA).1
  have hkey : ∀ M : Submodule (𝓞 K) W, M.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ M →
      muMin (realizeHLat b X) A - s ≤ muMin (realizeHLat b' X'') (A.map (φ.restrictScalars (𝓞 K))) ∧
      muMin (realizeHLat b X) A ≤ muMax (realizeHLat b' X'') M + s := by
    intro M hM hAM
    have hMlat := (place_lattice_structure b' X'' hX'' M hM).1
    let ψ : A →ₗ[𝓞 K] M := LinearMap.codRestrict M ((φ.restrictScalars (𝓞 K)).domRestrict A)
      (fun x => hAM (Submodule.mem_map_of_mem x.2))
    have hrange : (LinearMap.range ψ).map M.subtype = A.map (φ.restrictScalars (𝓞 K)) := by
      ext y; simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hψ0 : ψ ≠ 0 := by
      obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hφA
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      intro h; apply hy0
      exact congrArg (fun g : A →ₗ[𝓞 K] M => ((g ⟨x, hx⟩ : M) : W)) h
    have hS := (bost_slope_ineq_general (realizeHLat b X) (realizeHLat b' X'') hAlat hMlat
      ψ (Real.exp s) (Real.exp_pos s) (fun x => hbound x.1)).1 hψ0
    rw [Real.log_exp, hrange] at hS
    exact hS
  have hφA_fg : (A.map (φ.restrictScalars (𝓞 K))).FG := hA.map _
  have htw_im := twist_invariance b' X' c hX' hc _ hφA_fg hφA
  have hδ0 : (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, Real.log (c v) = 0 := by rw [hsum_log_c, mul_zero]
  simp only [hδ0, add_zero] at htw_im
  obtain ⟨k1, _⟩ := hkey _ hφA_fg le_rfl
  rw [htw_im.2.1] at k1
  refine ⟨by unfold muMinDef; dsimp only [s] at k1; linarith, fun B hB hAB => ?_⟩
  have hB0 : B ≠ ⊥ := fun h => hφA (le_bot_iff.mp (h ▸ hAB))
  have htw_B := twist_invariance b' X' c hX' hc B hB hB0
  simp only [hδ0, add_zero] at htw_B
  obtain ⟨_, k2⟩ := hkey B hB hAB
  rw [htw_B.1] at k2
  unfold muMinDef muMaxDef; dsimp only [s] at k2; linarith

end NumberFieldPlaceSplitting

/-! ## Section 5: Layer-Cake Integration, `FrameHerm`, `FrameHermSharp`, `TheoremFSharp` & `frame_herm_sharp_slope_ineq` -/

section FrameHermSharpSection

/-- Exact analytic evaluation of the corank-share integral (`frameB_integral`):
`∫ τ in 0..HH, 4 * (u / (u + τ)) = 4 * u * log (1 + HH / u)`. -/
theorem frameB_integral (u HH : ℝ) (hu : 0 < u) (hH : 0 ≤ HH) :
    ∫ τ in (0 : ℝ)..HH, 4 * (u / (u + τ)) = 4 * u * Real.log (1 + HH / u) := by
  have h := integral_four_u_div u HH 0 hu hH
  simp only [add_zero, zero_mul] at h
  convert h using 2
  ext τ; ring

/-- **Layer-Cake Profile Integral (`frameB_layer_cake_integral`)**:
for any `0 ≤ u`, `0 ≤ HH`, `δ < 1`, `η`, `e`, the profile
`w τ = (1 - δ)⁻¹ * (η + 4 * (u / (u + τ)) + 4 * √e)` is continuous on `[0, HH]` and satisfies:
`∫ τ in 0..HH, w τ = (1 - δ)⁻¹ * (4 * u * log (1 + HH / u) + (η + 4 * √e) * HH)`! -/
theorem frameB_layer_cake_integral (u HH η e δ : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ HH) :
    let w : ℝ → ℝ := fun τ => (1 - δ)⁻¹ * (η + 4 * (u / (u + τ)) + 4 * Real.sqrt e)
    ContinuousOn w (Set.uIcc 0 HH) ∧
    (∫ τ in (0 : ℝ)..HH, w τ) =
      (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) := by
  intro w
  rcases lt_or_eq_of_le hu with hu' | hu'
  · have h4cont : ContinuousOn (fun τ : ℝ => 4 * (u / (u + τ))) (Set.uIcc 0 HH) := by
      rw [Set.uIcc_of_le hH]
      refine continuousOn_const.mul (continuousOn_const.div (continuousOn_const.add continuousOn_id) ?_)
      intro τ hτ; exact (by linarith [hτ.1] : (0 : ℝ) < u + τ).ne'
    have hweq : w = fun τ => (1 - δ)⁻¹ * (η + 4 * Real.sqrt e) +
        (1 - δ)⁻¹ * (4 * (u / (u + τ))) := funext fun τ => by dsimp only [w]; ring
    rw [hweq]
    refine ⟨continuousOn_const.add (continuousOn_const.mul h4cont), ?_⟩
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (h4cont.intervalIntegrable.const_mul _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, frameB_integral u HH hu' hH, smul_eq_mul]
    ring
  · have hweq : w = fun _ => (1 - δ)⁻¹ * (η + 4 * Real.sqrt e) :=
      funext fun τ => by dsimp only [w]; rw [← hu']; simp
    rw [hweq]
    refine ⟨continuousOn_const, ?_⟩
    rw [intervalIntegral.integral_const, smul_eq_mul]
    simp only [← hu', mul_zero, zero_mul, zero_add, sub_zero]
    ring

/-- Sum identity for normalized HN slopes (`frameB_sum_sl`). -/
theorem frameB_sum_sl {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (L : Submodule R V) (hL : IsLat ρ L) (hr : rk ρ L ≠ 0) (a : ℝ) :
    ∑ j : Fin (rk ρ L), (2 * hnSlopeList ρ L j + a) = (rk ρ L : ℝ) * (2 * slope ρ L + a) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_hnSlopeList ρ hL,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr' : (rk ρ L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  unfold slope RHDirect.ArakelovCovolume.slope
  change 2 * deg ρ L + (rk ρ L : ℝ) * a = (rk ρ L : ℝ) * (2 * (deg ρ L / (rk ρ L : ℝ)) + a)
  field_simp [hr']

/-- **Place-Level Frame Corank Bound (`thmF_place_corank`)**:
connects `LatticeFrame.frame_corank_density_bound` to the `K`-rank of `⨆ i, (Nt i).map (B i)`
via `finrank_span_complex`! -/
theorem thmF_place_corank {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (b : ∀ i, Basis (ι i) K (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (c : I → ℝ)
    (e η ε : ℝ) (Nt : ∀ i, Submodule (𝓞 K) (V i))
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det) (hc : ∀ i, 0 < c i)
    (hpos : 0 < ∑ i, Fintype.card (ι i))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
    (hF2 : (∑ i, opHsSq (opFrameK (c i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hη : 0 ≤ η)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ))
    (hcor : (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) ≤ ε * ∑ i, (Fintype.card (ι i) : ℝ)) :
    (Fintype.card κ : ℝ) - rkK (⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))) ≤
      (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := by
  classical
  let Bv : ∀ i, EuclideanSpace ℂ (ι i) →ₗ[ℂ] EuclideanSpace ℂ κ := fun i => Matrix.toEuclideanLin
    (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)
  let Ba : ∀ i, EuclideanSpace ℂ (ι i) →ₗ[ℂ] EuclideanSpace ℂ (κ ⊕ κ₁) := fun i =>
    Matrix.toEuclideanLin (Ball i)
  let M : Submodule (𝓞 K) W := ⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))
  let eq : ∀ (α : Type) [Fintype α], (α → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ α :=
    fun α _ => (WithLp.linearEquiv 2 ℂ (α → ℂ)).symm
  let Nτ : ∀ i, Submodule ℂ (EuclideanSpace ℂ (ι i)) := fun i =>
    (Submodule.span ℂ (fcoord (b i) (fun _ => Y i) v '' (Nt i : Set (V i)))).map (eq (ι i)).toLinearMap
  have hNτ : ∀ i, Module.finrank ℂ (Nτ i) = rkK (Nt i) := fun i => by
    rw [LinearEquiv.finrank_map_eq]; exact finrank_span_complex (b i) (fun _ => Y i) (fun _ => hY i) (Nt i) v
  let T : Submodule ℂ (EuclideanSpace ℂ κ) :=
    (Submodule.span ℂ (fcoord b' (fun _ => Y') v '' (M : Set W))).map (eq κ).toLinearMap
  have hT : Module.finrank ℂ T = rkK M := by
    rw [LinearEquiv.finrank_map_eq]; exact finrank_span_complex b' (fun _ => Y') (fun _ => hY') M v
  have hST : (⨆ i, (Nτ i).map (Bv i)) ≤ T := by
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap]
    show Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Submodule.mem_comap, SetLike.mem_coe]
    refine Submodule.mem_map.mpr ⟨fcoord b' (fun _ => Y') v (B i x),
      Submodule.subset_span ⟨B i x, Submodule.mem_iSup_of_mem i
        (Submodule.mem_map_of_mem (f := (B i).restrictScalars (𝓞 K)) hx), rfl⟩, ?_⟩
    rw [fcoord_map_eq (b i) (fun _ => Y i) b' (fun _ => Y') (fun _ => hY i) v (B i) x]
    rfl
  let P : EuclideanSpace ℂ (κ ⊕ κ₁) →ₗ[ℂ] EuclideanSpace ℂ κ :=
    (eq κ).toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ Sum.inl ∘ₗ (eq (κ ⊕ κ₁)).symm.toLinearMap
  have hPB : ∀ i, P ∘ₗ Ba i = Bv i := fun i => by
    apply LinearMap.ext; intro x; ext k
    change (Ball i *ᵥ x.ofLp) (Sum.inl k) =
      ((Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) *ᵥ x.ofLp) k
    simp only [Matrix.mulVec, dotProduct, hBall]
  have hPsurj : LinearMap.range P = ⊤ :=
    LinearMap.range_eq_top.mpr fun y => ⟨eq (κ ⊕ κ₁) (Sum.elim ((eq κ).symm y) 0), by
      ext k; simp [P, eq, LinearMap.funLeft]⟩
  have hkerP : Module.finrank ℂ (LinearMap.ker P) = Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker P
    rw [hPsurj, finrank_top, finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum] at h
    omega
  let S : Submodule ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) := ⨆ i, (Nτ i).map (Ba i)
  have hPS : S.map P ≤ T := by
    have : S.map P = ⨆ i, (Nτ i).map (Bv i) := by
      simp only [S, Submodule.map_iSup, ← Submodule.map_comp, hPB]
    rw [this]; exact hST
  have hSdim : Module.finrank ℂ S ≤ Module.finrank ℂ (S.map P) + Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (P ∘ₗ S.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at h
    have hk : Module.finrank ℂ (LinearMap.ker (P ∘ₗ S.subtype)) ≤ Module.finrank ℂ (LinearMap.ker P) := by
      rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq]
      exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
    omega
  have hLA := frame_corank_density_bound Ba c Nτ e η ε hc
    (by simp only [finrank_euclideanSpace]; exact hpos)
    (by simp only [finrank_euclideanSpace]; exact hF2)
    he0 he1 hη
    (by simp only [finrank_euclideanSpace]; exact hF1)
    (by simp only [finrank_euclideanSpace, hNτ]; exact hcor)
  rw [finrank_euclideanSpace] at hLA
  have hsum := Submodule.finrank_add_finrank_orthogonal S
  rw [finrank_euclideanSpace, Fintype.card_sum] at hsum
  have hmono := Submodule.finrank_mono hPS
  rw [hT] at hmono
  have hsum' : (Module.finrank ℂ S : ℝ) + (Module.finrank ℂ Sᗮ : ℝ) =
      (Fintype.card κ : ℝ) + Fintype.card κ₁ := by exact_mod_cast hsum
  have hmono' : (Module.finrank ℂ (S.map P) : ℝ) ≤ (rkK M : ℝ) := by exact_mod_cast hmono
  have hSdim' : (Module.finrank ℂ S : ℝ) ≤ Module.finrank ℂ (S.map P) + Fintype.card κ₁ := by
    exact_mod_cast hSdim
  have hcard_sum : (Fintype.card (κ ⊕ κ₁) : ℝ) = (Fintype.card κ : ℝ) + Fintype.card κ₁ := by
    rw [Fintype.card_sum]; push_cast; rfl
  linarith

/-- **Projected Sharp Bost Frame-Slope Inequality Statement (`TheoremFSharp`)**
(matching `Formalism.HN.TheoremFSharp` in `StatementFrameF.lean`). -/
def TheoremFSharp : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, opHsSq (opFrameK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

/-- **Projected Bost Frame-Slope Inequality with `log |I|` (`TheoremF`)**
(matching `Formalism.HN.TheoremF`). -/
def TheoremF : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, opHsSq (opFrameK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

/-- **Sharp Hermitian-Lattice Frame-Slope Inequality (`FrameHermSharp`)**
(matching `Formalism.HN.FrameHermSharp` in `StatementFrame.lean`). -/
def FrameHermSharp : Prop :=
  ∀ (K W κ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ) (c : I → ℝ)
    (s u HH e η : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    (∀ i, B i ≠ 0) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i)) →
    0 < u → (∀ i, muMaxDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i) ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, 0 < c i) →
    (∑ i, opHsSq (opFrameK (c i) (Matrix.toEuclideanLin
        (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) ∘ₗ
         opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ^ 2 /
        (Fintype.card κ : ℝ) →
    0 ≤ η →
    s - 4 * u * Real.log (1 + HH / u) - (2 * η + 4 * Real.sqrt e) * HH ≤ muDef b' X' cc

/-- **Hermitian-Lattice Frame-Slope Inequality (`FrameHerm`)**
(matching `Formalism.HN.FrameHerm` in `StatementFrame.lean`). -/
def FrameHerm : Prop :=
  ∀ (K W κ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ) (c : I → ℝ)
    (s u HH e η : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    (∀ i, B i ≠ 0) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i)) →
    0 < u → (∀ i, muMaxDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i) ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, 0 < c i) →
    (∑ i, opHsSq (opFrameK (c i) (Matrix.toEuclideanLin
        (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) ∘ₗ
         opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ^ 2 /
        (Fintype.card κ : ℝ) →
    0 ≤ η →
    s - Real.log (Fintype.card I : ℝ) - u * (1 + 4 * Real.log (1 + HH / u)) -
        (2 * η + 4 * Real.sqrt e) * HH ≤ muDef b' X' cc

/-- **Main Unconditional Theorem (`theoremFSharp_holds`)**:
proves the sharp projected Bost frame-slope inequality (`TheoremFSharp`) on arbitrary totally
complex number-field Hermitian lattices via canonical HN filtration + mean slope inequality +
frame corank density + layer-cake integration! -/
theorem theoremFSharp_holds : TheoremFSharp := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ hX' hX hY hY' hccFG hccSpan hNFG hNSpan hR hBN hht hs hu hmax hHH hHH0
    hδ0 hδ1 hcard hBall hγ hF2 he0 he1 hF1 hη
  classical
  have : FiniteDimensional K W := Module.Finite.of_basis b'
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hnR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hn
  have hδ' : 0 < 1 - δ := by linarith
  have hRR : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by exact_mod_cast hR
  have hD : 0 < Fintype.card κ := by
    by_contra hD0
    have hκ0 : Fintype.card κ = 0 := by omega
    have hall : (Fintype.card (κ ⊕ κ₁) : ℝ) = 0 := by
      have h1 : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ 0 := by
        rw [hκ0, Nat.cast_zero] at hcard; exact hcard
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (κ ⊕ κ₁))]
    have hemp : IsEmpty (κ ⊕ κ₁) := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hall)
    have hz : ∀ i, Matrix.toEuclideanLin (Ball i) = 0 := fun i => by
      apply LinearMap.ext; intro x; ext k; exact isEmptyElim k
    have h0_hs : ∀ i, opHsSq (opFrameK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id) =
        (Fintype.card (ι i) : ℝ) := fun i => by
      rw [hz i]
      simp [opHsSq, opFrameK, LinearMap.trace_id, finrank_euclideanSpace]
    simp_rw [h0_hs] at hF2
    nlinarith
  have hLN : ∀ i, IsLat (realizeHLat (b i) (X i)) (N i) := fun i =>
    (place_lattice_structure (b i) (X i) (hX i) (N i) (hNFG i)).1
  have hrkK_top : ∀ {V' ι' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
      [IsScalarTower (𝓞 K) K V'] [Fintype ι'] [DecidableEq ι']
      (b₀ : Basis ι' K V') (L₀ : Submodule (𝓞 K) V'),
      Submodule.span K (L₀ : Set V') = ⊤ → rkK L₀ = Fintype.card ι' := by
    intro V' ι' _ _ _ _ _ _ b₀ L₀ hsp
    unfold rkK; rw [hsp, finrank_top, Module.finrank_eq_card_basis b₀]
  have hrkN : ∀ i, rk (realizeHLat (b i) (X i)) (N i) = Module.finrank ℚ K * Fintype.card (ι i) :=
    fun i => by
      rw [(place_lattice_structure (b i) (X i) (hX i) (N i) (hNFG i)).2,
        hrkK_top (b i) (N i) (hNSpan i)]
  have hLcc : IsLat (realizeHLat b' X') cc := (place_lattice_structure b' X' hX' cc hccFG).1
  have hrkcc : rk (realizeHLat b' X') cc = Module.finrank ℚ K * Fintype.card κ := by
    rw [(place_lattice_structure b' X' hX' cc hccFG).2, hrkK_top b' cc hccSpan]
  have hNne : ∀ i, Fintype.card (ι i) ≠ 0 → N i ≠ ⊥ := fun i hci h0 => by
    have hc := hrkK_top (b i) (N i) (hNSpan i)
    rw [h0] at hc
    have h00 : rkK (⊥ : Submodule (𝓞 K) (V i)) = 0 := by simp [rkK]
    omega
  have hccne : cc ≠ ⊥ := fun h0 => by
    have hc := hrkK_top b' cc hccSpan
    rw [h0] at hc
    have h00 : rkK (⊥ : Submodule (𝓞 K) W) = 0 := by simp [rkK]
    omega
  -- Threshold HN sublattices `Nt τ i ≤ N i` and `St τ ≤ cc`
  let θ : ℝ → I → ℝ := fun τ i => (s - τ + h i - slopeNormalisingConstant K) / 2
  let Nt : ℝ → ∀ i, Submodule (𝓞 K) (V i) := fun τ i =>
    hnStep (realizeHLat (b i) (X i)) (N i) (θ τ i)
  have hNtle : ∀ τ i, Nt τ i ≤ N i := fun τ i => (hnStep_spec _ (hLN i) (θ τ i)).1.1
  have hNtFG : ∀ τ i, (Nt τ i).FG := fun τ i => Submodule.FG.of_le (hNFG i) (hNtle τ i)
  have hrkNt : ∀ τ i, rk (realizeHLat (b i) (X i)) (Nt τ i) = Module.finrank ℚ K * rkK (Nt τ i) :=
    fun τ i => (place_lattice_structure (b i) (X i) (hX i) (Nt τ i) (hNtFG τ i)).2
  -- Corank-share bound on `Nt τ i`
  have hcor : ∀ τ, 0 ≤ τ →
      (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i))) ≤ (u / (u + τ)) * ∑ i, (Fintype.card (ι i) : ℝ) := by
    intro τ hτ
    have hsh := corank_share_bound (fun i => rk (realizeHLat (b i) (X i)) (N i))
      (fun i j => 2 * hnSlopeList (realizeHLat (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i)
      s u τ hu hτ ?_ ?_
    · have hfilt : ∀ i, ((Finset.univ.filter (fun j =>
          2 * hnSlopeList (realizeHLat (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i < s - τ)).card : ℝ) =
          (Module.finrank ℚ K : ℝ) * ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i)) := by
        intro i
        rw [Finset.filter_congr (q := fun j => hnSlopeList (realizeHLat (b i) (X i)) (N i) j < θ τ i)
          (fun j _ => by simp only [θ]; constructor <;> intro hj <;> linarith),
          card_hnSlopeList_lt _ (hLN i) (θ τ i)]
        change (rk (realizeHLat (b i) (X i)) (N i) : ℝ) - rk (realizeHLat (b i) (X i)) (Nt τ i) = _
        rw [hrkN i, hrkNt τ i]; push_cast; ring
      simp only [hfilt, hrkN] at hsh
      push_cast at hsh
      rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc] at hsh
      have := le_of_mul_le_mul_left hsh hnR
      linarith
    · have hx : ∀ i, ∑ j, (2 * hnSlopeList (realizeHLat (b i) (X i)) (N i) j +
          slopeNormalisingConstant K - h i) = (Module.finrank ℚ K : ℝ) *
          ((Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i)) := by
        intro i
        by_cases hci : Fintype.card (ι i) = 0
        · have h0 : rk (realizeHLat (b i) (X i)) (N i) = 0 := by rw [hrkN i, hci, mul_zero]
          have : IsEmpty (Fin (rk (realizeHLat (b i) (X i)) (N i))) := by rw [h0]; exact Fin.isEmpty'
          simp [hci]
        · simp_rw [add_sub_assoc]
          rw [frameB_sum_sl _ (N i) (hLN i) (by rw [hrkN i]; exact (Nat.mul_pos hn (Nat.pos_of_ne_zero hci)).ne'),
            hrkN i]; unfold muDef; push_cast; ring
      rw [Finset.sum_congr rfl fun i _ => hx i, ← Finset.mul_sum]
      simp only [hrkN]; push_cast
      rw [← Finset.mul_sum, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hs) hnR.le
    · intro i j
      by_cases hci : Fintype.card (ι i) = 0
      · exfalso
        have hj : (j : ℕ) < rk (realizeHLat (b i) (X i)) (N i) := j.isLt
        have h0 : rk (realizeHLat (b i) (X i)) (N i) = 0 := by rw [hrkN i, hci, mul_zero]
        omega
      · have hext := ((hnSlopeList_extremes _ (hLN i) (hNne i hci)).1 j).2
        have hm := hmax i; unfold muMaxDef at hm; linarith
  -- Image `M τ = ⨆ i, (Nt τ i).map (B i)` lands inside `St τ = hnStep cc (θ' τ)` via `slope_inequality_mean`!
  let θ' : ℝ → ℝ := fun τ => (s - τ - slopeNormalisingConstant K) / 2
  let St : ℝ → Submodule (𝓞 K) W := fun τ => hnStep (realizeHLat b' X') cc (θ' τ)
  let M : ℝ → Submodule (𝓞 K) W := fun τ => ⨆ i, (Nt τ i).map ((B i).restrictScalars (𝓞 K))
  have hMle : ∀ τ, M τ ≤ St τ := by
    intro τ
    refine iSup_le fun i => ?_
    by_cases h0 : (Nt τ i).map ((B i).restrictScalars (𝓞 K)) = ⊥
    · rw [h0]; exact bot_le
    · have hBi : B i ≠ 0 := fun hb => h0 (eq_bot_iff.mpr (by rintro _ ⟨y, _, rfl⟩; simp [hb]))
      have hNt0 : Nt τ i ≠ ⊥ := fun h' => h0 (by rw [h', Submodule.map_bot])
      have hsi := (slope_inequality_mean (b i) (X i) b' X' (hX i) hX' (B i) (Nt τ i) (hNtFG τ i) h0).1
      have hst := (hnStep_spec _ (hLN i) (θ τ i)).2.1 hNt0
      have hhi := hht i hBi
      refine (hnStep_spec _ hLcc (θ' τ)).2.2.1 _ ((Submodule.map_mono (hNtle τ i)).trans (hBN i)) h0 ?_
      unfold muMinDef at hsi; dsimp only [θ, θ'] at hst ⊢; linarith
  have hStle : ∀ τ, St τ ≤ cc := fun τ => (hnStep_spec _ hLcc (θ' τ)).1.1
  have hStFG : ∀ τ, (St τ).FG := fun τ => Submodule.FG.of_le hccFG (hStle τ)
  have hrkSt : ∀ τ, rk (realizeHLat b' X') (St τ) = Module.finrank ℚ K * rkK (St τ) :=
    fun τ => (place_lattice_structure b' X' hX' (St τ) (hStFG τ)).2
  have hrkM : ∀ τ, rkK (M τ) ≤ rkK (St τ) := fun τ =>
    Submodule.finrank_mono (Submodule.span_mono (SetLike.coe_subset_coe.mpr (hMle τ)))
  let w : ℝ → ℝ := fun τ => (1 - δ)⁻¹ * (η + 4 * (u / (u + τ)) + 4 * Real.sqrt e)
  have hplace : ∀ τ, 0 ≤ τ → (Fintype.card κ : ℝ) - rkK (M τ) ≤ w τ * Fintype.card κ := by
    intro τ hτ
    have h1 := thmF_place_corank b' b B v Y Y' Ball γ e η (u / (u + τ)) (Nt τ) hY hY' hγ hR hBall
      hF2 he0 he1 hη hF1 (hcor τ hτ)
    have hc0 : 0 ≤ η + 4 * (u / (u + τ)) + 4 * Real.sqrt e := by
      have := div_nonneg hu (by linarith : (0 : ℝ) ≤ u + τ)
      linarith [Real.sqrt_nonneg e]
    have hA : (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (1 - δ)⁻¹ * Fintype.card κ := by
      rw [le_inv_mul_iff₀ hδ']; exact hcard
    calc (Fintype.card κ : ℝ) - rkK (M τ)
        ≤ (η + 4 * (u / (u + τ)) + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := h1
      _ ≤ (η + 4 * (u / (u + τ)) + 4 * Real.sqrt e) * ((1 - δ)⁻¹ * Fintype.card κ) :=
          mul_le_mul_of_nonneg_left hA hc0
      _ = w τ * Fintype.card κ := by dsimp only [w]; ring
  -- Layer-cake integration!
  have hcnt : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => 2 * hnSlopeList (realizeHLat b' X') cc j +
          slopeNormalisingConstant K < s - τ)).card : ℝ) ≤
        w τ * (rk (realizeHLat b' X') cc : ℕ) := by
    intro τ hτ
    rw [Finset.filter_congr (q := fun j => hnSlopeList (realizeHLat b' X') cc j < θ' τ)
      (fun j _ => by simp only [θ']; constructor <;> intro hj <;> linarith),
      card_hnSlopeList_lt _ hLcc (θ' τ)]
    change (rk (realizeHLat b' X') cc : ℝ) - rk (realizeHLat b' X') (St τ) ≤ _
    rw [hrkcc, hrkSt τ]; push_cast
    have h1 := hplace τ hτ.1
    have h2 : (rkK (M τ) : ℝ) ≤ rkK (St τ) := by exact_mod_cast hrkM τ
    nlinarith
  have hlow : ∀ j, s - HH ≤ 2 * hnSlopeList (realizeHLat b' X') cc j + slopeNormalisingConstant K := by
    intro j
    have hext := ((hnSlopeList_extremes _ hLcc hccne).1 j).1
    unfold muMinDef at hHH; linarith
  have hwc := frameB_layer_cake_integral u HH η e δ hu hHH0
  have hwint : IntervalIntegrable w MeasureTheory.volume 0 HH := hwc.1.intervalIntegrable
  have hminint : IntervalIntegrable (fun τ => min 1 (w τ)) MeasureTheory.volume 0 HH :=
    (continuous_min.comp_continuousOn (continuousOn_const.prodMk hwc.1)).intervalIntegrable
  have hrkpos : 0 < rk (realizeHLat b' X') cc := by rw [hrkcc]; exact Nat.mul_pos hn hD
  have hLC := layer_cake_bound (rk (realizeHLat b' X') cc)
    (fun j => 2 * hnSlopeList (realizeHLat b' X') cc j + slopeNormalisingConstant K) s HH w
    hrkpos hHH0 hlow hminint hcnt
  have hmean : (∑ j, (2 * hnSlopeList (realizeHLat b' X') cc j + slopeNormalisingConstant K)) /
      (rk (realizeHLat b' X') cc : ℝ) = muDef b' X' cc := by
    rw [frameB_sum_sl _ cc hLcc hrkpos.ne']
    unfold muDef
    have : (rk (realizeHLat b' X') cc : ℝ) ≠ 0 := by exact_mod_cast hrkpos.ne'
    field_simp [this]
  rw [hmean] at hLC
  have hle := intervalIntegral.integral_mono_on hHH0 hminint hwint (fun τ _ => min_le_right 1 (w τ))
  linarith [hwc.2]

/-- **Projected Bost Frame-Slope Inequality (`theoremF_holds`)**: immediate corollary of
`theoremFSharp_holds` adding the non-negative `-log |I|` term. -/
theorem theoremF_holds : TheoremF := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
    h22 h23 h24 h25 h26
  have hsharp := theoremFSharp_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
  have hI : (1 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hI
  linarith

/-- **Sharp Bost Frame-Slope Inequality on Hermitian Lattices (`frame_herm_sharp_slope_ineq`)**:
unconditional proof of `FrameHermSharp` (zero `sorry`, zero `axiom`, zero `log |I|` penalty!)
deduced directly from `theoremFSharp_holds` at `κ₁ = PEmpty`, `δ = 0`! -/
theorem frame_herm_sharp_slope_ineq : FrameHermSharp := by
  intro K W κ I _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B v Y Y' c s u HH e η
    hX' hX hY hY' hccFG hccSpan hNFG hNSpan hBne hBN hs hu hmax hHH hHH0 hc hF2 he0 he1 hF1 hη
  classical
  -- Note `∑ i, Fintype.card (ι i) > 0` because `I` is nonempty and each `B i ≠ 0`!
  have hRpos : 0 < ∑ i : I, Fintype.card (ι i) := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
    have hci : 0 < Fintype.card (ι i₀) := by
      by_contra h0
      have hemp : IsEmpty (ι i₀) := Fintype.card_eq_zero_iff.mp (by omega)
      apply hBne i₀
      ext x
      have hx0 : x = 0 := by
        rw [← (b i₀).sum_repr x]; exact Finset.sum_eq_zero fun j _ => isEmptyElim j
      rw [hx0, map_zero, LinearMap.zero_apply]
    exact lt_of_lt_of_le hci (Finset.single_le_sum (f := fun i => Fintype.card (ι i))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀))
  let M : ∀ i, Matrix κ (ι i) ℂ := fun i =>
    Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i
  let Ball : ∀ i, Matrix (κ ⊕ PEmpty.{1}) (ι i) ℂ := fun i =>
    Matrix.of fun k j => Sum.elim (fun k' => M i k' j) PEmpty.elim k
  let iso : EuclideanSpace ℂ (κ ⊕ PEmpty.{1}) ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
    { toFun := fun y => WithLp.toLp 2 (fun k => y.ofLp (Sum.inl k))
      invFun := fun z => WithLp.toLp 2 (Sum.elim z.ofLp PEmpty.elim)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun y => by
        ext k
        cases k with
        | inl k' => rfl
        | inr k' => exact PEmpty.elim k'
      right_inv := fun _ => rfl
      norm_map' := fun y => by
        change ‖WithLp.toLp 2 (fun k => y.ofLp (Sum.inl k))‖ = ‖y‖
        have hsq : ‖WithLp.toLp 2 (fun k => y.ofLp (Sum.inl k))‖ ^ 2 = ‖y‖ ^ 2 := by
          simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Finset.univ_eq_empty,
            Finset.sum_empty, add_zero]
        nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => y.ofLp (Sum.inl k))), norm_nonneg y] }
  have hBa_eq : ∀ i, Matrix.toEuclideanLin (Ball i) =
      iso.symm.toLinearMap ∘ₗ Matrix.toEuclideanLin (M i) := fun i => by
    apply LinearMap.ext; intro x; ext k
    cases k with
    | inl k' =>
      change (Matrix.toLpLin 2 2 (Ball i) x).ofLp (Sum.inl k') =
        (iso.symm (Matrix.toLpLin 2 2 (M i) x)).ofLp (Sum.inl k')
      simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Ball, iso, Matrix.mulVec, dotProduct,
        Matrix.of_apply, Sum.elim_inl]
      rfl
    | inr k' => exact PEmpty.elim k'
  have hadj_symm : iso.symm.toLinearMap.adjoint = iso.toLinearMap := by
    apply LinearMap.ext; intro x; apply ext_inner_left ℂ; intro y
    rw [LinearMap.adjoint_inner_right]
    change inner ℂ (iso.symm y) x = inner ℂ y (iso x)
    rw [← iso.inner_map_map (iso.symm y) x, iso.apply_symm_apply]
  have hmid : iso.toLinearMap ∘ₗ iso.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext; intro x; exact iso.apply_symm_apply x
  have hK_eq : ∀ i, opFrameK (c i) (Matrix.toEuclideanLin (Ball i)) =
      opFrameK (c i) (Matrix.toEuclideanLin (M i)) := fun i => by
    unfold opFrameK
    rw [hBa_eq i, LinearMap.adjoint_comp, hadj_symm, LinearMap.comp_assoc]
    have hstep : iso.toLinearMap ∘ₗ iso.symm.toLinearMap ∘ₗ Matrix.toEuclideanLin (M i) =
        Matrix.toEuclideanLin (M i) := by
      rw [← LinearMap.comp_assoc, hmid, LinearMap.id_comp]
    rw [hstep]
  have hQ_eq : opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) =
      iso.symm.toLinearMap ∘ₗ opFrameQ c (fun i => Matrix.toEuclideanLin (M i)) ∘ₗ iso.toLinearMap := by
    unfold opFrameQ
    simp_rw [hBa_eq, LinearMap.adjoint_comp, hadj_symm]
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
  have htrace_conj : ∀ f : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ,
      LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ PEmpty.{1}))
        (iso.symm.toLinearMap ∘ₗ f ∘ₗ iso.toLinearMap) =
      LinearMap.trace ℂ (EuclideanSpace ℂ κ) f := fun f => by
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (κ ⊕ PEmpty.{1}) ℂ).toBasis,
      LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun κ ℂ).toBasis]
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero, LinearMap.toMatrix_apply, LinearMap.comp_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hb : iso ((EuclideanSpace.basisFun (κ ⊕ PEmpty.{1}) ℂ).toBasis (Sum.inl k)) =
        (EuclideanSpace.basisFun κ ℂ).toBasis k := by
      ext j
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      change (EuclideanSpace.single (Sum.inl k) (1 : ℂ)).ofLp (Sum.inl j) =
        (EuclideanSpace.single k (1 : ℂ)).ofLp j
      simp
    change (EuclideanSpace.basisFun (κ ⊕ PEmpty.{1}) ℂ).toBasis.repr
        (iso.symm (f (iso ((EuclideanSpace.basisFun (κ ⊕ PEmpty.{1}) ℂ).toBasis (Sum.inl k))))) (Sum.inl k) =
      (EuclideanSpace.basisFun κ ℂ).toBasis.repr (f ((EuclideanSpace.basisFun κ ℂ).toBasis k)) k
    rw [hb]
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    rfl
  have htr1 : LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ PEmpty.{1}))
      (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i))) =
      LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin (M i))) := by
    rw [hQ_eq, htrace_conj]
  have htr2 : LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ PEmpty.{1}))
      (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
        opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i))) =
      LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin (M i)) ∘ₗ
          opFrameQ c (fun i => Matrix.toEuclideanLin (M i))) := by
    have hcomp : opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
        opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) =
        iso.symm.toLinearMap ∘ₗ
          (opFrameQ c (fun i => Matrix.toEuclideanLin (M i)) ∘ₗ
            opFrameQ c (fun i => Matrix.toEuclideanLin (M i))) ∘ₗ iso.toLinearMap := by
      rw [hQ_eq]
      simp only [LinearMap.comp_assoc]
      have hstep : iso.toLinearMap ∘ₗ iso.symm.toLinearMap ∘ₗ
          (opFrameQ c (fun i => Matrix.toEuclideanLin (M i)) ∘ₗ iso.toLinearMap) =
          opFrameQ c (fun i => Matrix.toEuclideanLin (M i)) ∘ₗ iso.toLinearMap := by
        rw [← LinearMap.comp_assoc, hmid, LinearMap.id_comp]
      rw [hstep]
    rw [hcomp, htrace_conj]
  have hF2' : (∑ i, opHsSq (opFrameK (c i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) := by simp_rw [hK_eq]; exact hF2
  have hF1' : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ PEmpty.{1}))
      (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
       opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ PEmpty.{1}))
        (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ PEmpty.{1}) : ℝ) := by
    rw [htr1, htr2, Fintype.card_sum, Fintype.card_pempty, add_zero]; exact hF1
  have hres := theoremFSharp_holds K W κ PEmpty.{1} I V ι b' X' cc b X N B
    (fun i => htMap (b i) (X i) b' X' (B i)) v Y Y' Ball c s u HH e η 0
    hX' hX hY hY' hccFG hccSpan hNFG hNSpan hRpos hBN (fun _ _ => le_rfl) hs hu.le hmax hHH hHH0
    le_rfl (by norm_num) (by simp) (fun _ _ _ => rfl) hc hF2' he0 he1 hF1' hη
  simp only [sub_zero, inv_one, one_mul] at hres
  have hηH : η * HH ≤ 2 * η * HH := by nlinarith
  linarith

/-- **Bost Frame-Slope Inequality (`frame_herm_slope_ineq`)**: unconditional proof of `FrameHerm`. -/
theorem frame_herm_slope_ineq : FrameHerm := by
  intro K W κ I _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B v Y Y' c s u HH e η
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
  have hsharp := frame_herm_sharp_slope_ineq K W κ I V ι b' X' cc b X N B v Y Y' c s u HH e η
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
  have hI : (1 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hI
  linarith

/-- **Direct Bridge to `RHDirect.BostSlopeFiber.SlopeIneq` (`bostSlopeFiber_of_herm_frame`)**:
packages `theoremFSharp_holds` directly into `F.SlopeIneq` for Wave 2 `Stage14M2_RamifiedJointBost`
and `Stage14M2_FrameRealCompile`! -/
theorem bostSlopeFiber_of_herm_frame
    {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (F : RHDirect.BostSlopeFiber)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (hX' : ∀ w, IsUnit (X' w).det) (hX : ∀ i w, IsUnit (X i w).det)
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det)
    (hccFG : cc.FG) (hccSpan : Submodule.span K (cc : Set W) = ⊤)
    (hNFG : ∀ i, (N i).FG) (hNSpan : ∀ i, Submodule.span K (N i : Set (V i)) = ⊤)
    (hR : 0 < ∑ i, Fintype.card (ι i))
    (hBN : ∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc)
    (hht : ∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i)
    (hmuCC : muDef b' X' cc = F.muCC)
    (hmuMin : F.muMinCC ≤ muMinDef b' X' cc)
    (hs : F.s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i))
    (hu : 0 ≤ F.uF)
    (hmax : ∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ F.s + F.uF)
    (hcardW : 1 ≤ F.cardW)
    (hcard : (1 - F.del) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
    (hγ : ∀ i, 0 < γ i)
    (hF2 : (∑ i, opHsSq (opFrameK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      F.e * ∑ i, (Fintype.card (ι i) : ℝ))
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + F.η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ)) :
    F.SlopeIneq := by
  intro hdel0 hdel1 hη0 he0 he4 hHH_ge hHH_pos
  have hsharp := theoremFSharp_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ
    F.s F.uF F.HH F.e F.η F.del hX' hX hY hY' hccFG hccSpan hNFG hNSpan hR hBN hht hs hu hmax
    (by linarith) hHH_pos.le hdel0 hdel1 hcard hBall hγ hF2 he0 he4 hF1 hη0
  have hlogW : 0 ≤ Real.log (F.cardW : ℝ) := Real.log_nonneg (by exact_mod_cast hcardW)
  linarith

end FrameHermSharpSection

end RHDirect.Stage14M2_HNFiltAndFrame

end
