import RHDirect.Stage4ArakelovBost
import RHDirect.Stage10GeometryOfNumbers
import RHDirect.Stage3DworkFrobenius
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# RHDirect.Stage11BostDworkSqueeze

Stage 11 **Concrete Arakelov–Bost–Minkowski Quotient Slope Squeeze, Dwork `p`-Adic Divisibility
Bridge & Strictly Smaller `Stage11ThetaCoreInputs S` Compiler** in pure Mathlib `v4.33.1`
(0 `sorry`, 0 custom `axiom`s):

1. **Concrete Arakelov–Minkowski–Bost Morphism, Index & Exact-Sequence Slope Bounds (`0` Assumptions)**:
   - Exact finite-index covolume formula (`covol_eq_index_mul_covol`, `degAr_eq_degAr_sub_log_index`,
     `slope_eq_slope_sub_log_index_div_rk`): for any full-rank sublattice `N ≤ M` of a discrete
     Euclidean lattice `M ⊂ E`, `covol N = [M : N] * covol M`!
   - `muMax_le_of_bounded_injection` (and exponential / `ContinuousLinearMap` variants):
     for any injective `φ : L_N →ₗ[ℤ] L_M` with `‖φ x‖ ≤ C * ‖x‖`,
     `ArakelovCovolume.muMax L_N ≤ ArakelovCovolume.muMax L_M + Real.log C`.
   - `slope_ge_of_index_and_norm` (plus bounded reverse-injection & quotient exact-sequence forms):
     for any full-rank injective `φ : L_N →ₗ[ℤ] L_M` with coercivity `‖x‖ ≤ C_inv * ‖φ x‖` and
     cokernel index `I_φ = [L_M : im φ]`,
     `ArakelovCovolume.slope L_M - Real.log C_inv - Real.log I_φ / rk L_M ≤ ArakelovCovolume.slope L_N`.
   - Direct isometric bridge from arbitrary discrete Euclidean lattices `L ⊂ E` to
     `Stage10GeometryOfNumbers` (`minkowski_second_theorem_upper`, `minkowski_second_theorem_lower`,
     `hermite_minkowski_bound_all_dims`), yielding:
     * `minkowski_second_theorem_upper_general` & `minkowski_second_theorem_lower_general`,
     * `minkowski_second_theorem_slope_squeeze`,
     * `muMax_sub_muMin_le_of_successiveMinima` (`μ_max(L) - μ_min(L) ≤ log(λ_r / λ_1) + (1/2) log r`),
     * `muMax_sub_muMin_le_of_minkowski_second_theorem` (volume-only `O(r log r)` gap bound
       directly from `Stage10GeometryOfNumbers.minkowski_second_theorem_upper`!).

2. **Concrete Dwork `p`-Adic Divisibility Bridge (`dwork_divisibility_mul_m`)**:
   - Exact additive `p`-adic valuation `dworkVal p x = log ‖x‖ / log ‖p‖`, with
     `dworkVal p ϖ = 1 / (p - 1)` from `Stage2DworkExp.norm_dworkPi`.
   - Iterated `m`-step `p`-adic chain operator `chainOp` and **`dwork_divisibility_mul_m`**:
     exact `m`-fold `p`-adic valuation amplification
     `v_p(chainOp m v) - v_p(v) ≥ m * ∑_t a_t / (p - 1) - m * ∑'_l vvTerm S E t l`!
   - Concrete overconvergent Dwork `U_p` chain contraction (`dworkOp_chain_overconvNorm_le`) via
     `Stage3DworkFrobenius.dworkOp` and `Stage2DworkExp.dworkSplitting`.
   - Direct product-formula discharge of `Stage3ThetaSiegelFiberWitness.divLink`
     (`divLink_of_dwork_chain`).

3. **Strictly Smaller `Stage11ThetaFiberWitness` & `Stage11ThetaCoreInputs S` Compiler**:
   - Discharges BOTH `quotientSlopes` (from a concrete bounded finite-index lattice morphism
     `φ : latN → latM`) AND `hhBound` (from a concrete common-fiber lattice `latCC` + bounded
     embeddings `ιCC : latN → latCC` + Minkowski successive-minima gap via `Stage10GeometryOfNumbers`).
   - Compiles directly via `Stage11ThetaFiberWitness.toStage3ThetaSiegelFiberWitness`,
     `stage3ThetaCoreInputs_of_stage11`, `stage11_thetaSlopeContract : Stage11ThetaCoreInputs S → RHDirect.ThetaSlopeContract S`,
     and `stage11_allLevelsWindowBound`!
-/

open Module Submodule Finset Real MeasureTheory Filter
open scoped BigOperators Matrix ENNReal Pointwise InnerProductSpace

namespace RHDirect.Stage11BostDworkSqueeze

noncomputable section

open RHDirect.ArakelovCovolume (rk covol degAr slopes muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  covol_le_of_le_same_rank gram_det_le norm_sum_smul_le_of_int
  slope_le_muMax muMax_mono bost_slope_inequality)

open RHDirect.Stage2SiegelReduction (lambda1 lambda1_pos lambda1_le_norm
  succMin succMin_mono succMin_zero_eq_lambda1 succMin_pos)

open RHDirect.Stage4ArakelovBost (IsSaturated quotLat muMin
  rk_add_quotLat degAr_eq_add_quotLat discreteTopology_quotLat
  muMin_le_slope_le_muMax muMin_le_slope_quotLat
  bost_muMin_le_muMax_add_log neg_log_succMin_last_le_muMin)

open RHDirect.Stage10GeometryOfNumbers (basisOfZLattice covolume_eq_abs_det
  successiveMinimum successiveMinimum_pos successiveMinimum_mono
  minkowski_second_theorem_upper minkowski_second_theorem_lower
  hermite_minkowski_bound_all_dims unitBallVolume_eq)

/-! ## Section 1: Exact Sublattice Index Formula, Morphism Slope Bounds & Minkowski Gap Squeeze -/

section IndexAndMorphismBounds

variable {E EN EM : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EN] [InnerProductSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NormedAddCommGroup EM] [InnerProductSpace ℝ EM] [FiniteDimensional ℝ EM]

/-- The **index `[M : N]`** of a sublattice `N ≤ M` inside `M`, defined as the subgroup index of
`N.comap M.subtype` in `M`. -/
def latIndex (M N : Submodule ℤ E) : ℕ :=
  (N.comap M.subtype).toAddSubgroup.index

/-- For a full-rank sublattice `N ≤ M` (`rk N = rk M`), the quotient `M / N` is finite and
`0 < latIndex M N`. -/
theorem finite_quotient_of_le_same_rank {M N : Submodule ℤ E} [DiscreteTopology M]
    (hNM : N ≤ M) (hrk : rk N = rk M) :
    Finite (M ⧸ (N.comap M.subtype).toAddSubgroup) ∧ 0 < latIndex M N := by
  have : DiscreteTopology N := discreteTopology_of_le hNM
  let r := rk M
  let bM : Basis (Fin r) ℤ M := Module.finBasis ℤ M
  let bN : Basis (Fin r) ℤ N := (Module.finBasis ℤ N).reindex (finCongr hrk)
  let P : Matrix (Fin r) (Fin r) ℤ :=
    fun i j => bM.repr ⟨(bN j : E), hNM (bN j).2⟩ i
  have hPdet_ne : P.det ≠ 0 := by
    intro h0
    have hEq : (fun j => (bN j : E)) =
        fun j => ∑ i, (P.map (Int.cast : ℤ → ℝ)) i j • (bM i : E) := by
      funext j
      have h := congrArg Subtype.val (bM.sum_repr ⟨(bN j : E), hNM (bN j).2⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.map_apply, Int.cast_smul_eq_zsmul]
    have hdet : (Matrix.gram ℝ (fun j => (bN j : E))).det =
        ((P.det : ℤ) : ℝ) ^ 2 * (Matrix.gram ℝ (fun i => (bM i : E))).det := by
      rw [hEq, RHDirect.ArakelovCovolume.gram_sum_smul_eq_transpose_mul,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      have hcast : (P.map (Int.cast : ℤ → ℝ)).det = (P.det : ℝ) := (Int.cast_det P).symm
      rw [hcast]; ring
    rw [h0, Int.cast_zero, zero_pow two_ne_zero, zero_mul] at hdet
    exact (det_gram_basis_pos N bN).ne' hdet
  -- Every `x : M` satisfies `P.det • x ∈ N.comap M.subtype` via `P * P.adjugate = P.det • 1`.
  let d : ℕ := P.det.natAbs
  have hd_pos : 0 < d := Int.natAbs_pos.mpr hPdet_ne
  have : NeZero d := ⟨hd_pos.ne'⟩
  have hd_mem : ∀ i : Fin r, P.det • bM i ∈ N.comap M.subtype := by
    intro i
    have hmul : P * P.adjugate = P.det • (1 : Matrix (Fin r) (Fin r) ℤ) :=
      Matrix.mul_adjugate P
    have hcomb : ∑ j : Fin r, (P.adjugate j i) • (⟨(bN j : E), hNM (bN j).2⟩ : M) =
        P.det • bM i := by
      apply bM.repr.injective
      ext k
      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Basis.repr_self]
      have hEntry := congrFun (congrFun hmul k) i
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hEntry
      have hEqSum : ∑ j : Fin r, P.adjugate j i * bM.repr ⟨(bN j : E), hNM (bN j).2⟩ k =
          ∑ j : Fin r, P k j * P.adjugate j i := by
        refine Finset.sum_congr rfl fun j _ => by simp [P, mul_comm]
      rw [hEqSum, hEntry]
      by_cases hki : k = i
      · subst hki; simp
      · simp [hki]
    change ((P.det • bM i : M) : E) ∈ N
    rw [← hcomb, Submodule.coe_sum]
    exact Submodule.sum_mem N fun j _ => Submodule.smul_mem N _ (bN j).2
  have hd_nat_mem : ∀ x : M, (d : ℤ) • x ∈ N.comap M.subtype := by
    intro x
    have hx : x = ∑ i : Fin r, bM.repr x i • bM i := (bM.sum_repr x).symm
    have hP_x : P.det • x ∈ N.comap M.subtype := by
      rw [hx, Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_comm]
      exact Submodule.smul_mem _ _ (hd_mem i)
    rcases Int.natAbs_eq P.det with h | h
    · rwa [← h]
    · have hneg : (d : ℤ) • x = -(P.det • x) := by
        rw [← neg_smul]; congr 1; linarith
      rw [hneg]
      exact (N.comap M.subtype).neg_mem hP_x
  -- Surjection from the finite type `Fin r → ZMod d` onto `M ⧸ (N.comap M.subtype).toAddSubgroup`.
  let qMap : (Fin r → ZMod d) → (M ⧸ (N.comap M.subtype).toAddSubgroup) :=
    fun f => QuotientAddGroup.mk (∑ i : Fin r, ((f i).val : ℤ) • bM i)
  have hsurj : Function.Surjective qMap := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨fun i => (bM.repr x i : ZMod d), ?_⟩
    dsimp only [qMap]
    rw [QuotientAddGroup.eq]
    have hdiff : -(∑ i : Fin r, (((bM.repr x i : ZMod d).val : ℤ)) • bM i) + x =
        ∑ i : Fin r, (bM.repr x i - (((bM.repr x i : ZMod d).val : ℤ))) • bM i := by
      have hxsum : x = ∑ i : Fin r, bM.repr x i • bM i := (bM.sum_repr x).symm
      rw [← Finset.sum_neg_distrib]
      conv_lhs => rhs; rw [hxsum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by rw [sub_smul]; abel
    change -(∑ i : Fin r, (((bM.repr x i : ZMod d).val : ℤ)) • bM i) + x ∈ N.comap M.subtype
    rw [hdiff]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hdvd : (d : ℤ) ∣ (bM.repr x i - (((bM.repr x i : ZMod d).val : ℤ))) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, mul_comm, mul_smul]
    exact Submodule.smul_mem _ k (hd_nat_mem (bM i))
  have hfin : Finite (M ⧸ (N.comap M.subtype).toAddSubgroup) := Finite.of_surjective qMap hsurj
  refine ⟨hfin, ?_⟩
  unfold latIndex
  rw [AddSubgroup.index_eq_card]
  exact Nat.card_pos

/-- **Exact Full-Rank Sublattice Index–Covolume Formula (`covol_eq_index_mul_covol`)**:
for any discrete lattice `M ⊂ E` and full-rank sublattice `N ≤ M` (`rk N = rk M`),
`ArakelovCovolume.covol N = (latIndex M N : ℝ) * ArakelovCovolume.covol M`! -/
theorem covol_eq_index_mul_covol {M N : Submodule ℤ E} [DiscreteTopology M]
    (hNM : N ≤ M) (hrk : rk N = rk M) :
    covol N = (latIndex M N : ℝ) * covol M := by
  have : DiscreteTopology N := discreteTopology_of_le hNM
  let r := rk M
  let V := Submodule.span ℝ (M : Set E)
  have hdim : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span M).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdim]))
  -- Coordinate map `Φ : V →ₗ[ℝ] (Fin r → ℝ)` and inverse `Ψ`.
  let Φ : V →ₗ[ℝ] (Fin r → ℝ) :=
    { toFun := fun v i => inner ℝ (e i) v
      map_add' := fun u v => by funext i; exact inner_add_right _ _ _
      map_smul' := fun c v => by funext i; exact real_inner_smul_right _ _ _ }
  let Ψ : (Fin r → ℝ) →ₗ[ℝ] V :=
    { toFun := fun c => ∑ i : Fin r, c i • e i
      map_add' := fun c₁ c₂ => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hΨΦ : ∀ v : V, Ψ (Φ v) = v := fun v => e.sum_repr' v
  have hΦΨ : ∀ c : Fin r → ℝ, Φ (Ψ c) = c := fun c => by
    funext i
    change inner ℝ (e i) (∑ j : Fin r, c j • e j) = c i
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_right, orthonormal_iff_ite.mp e.orthonormal i i, if_pos rfl, mul_one]
    · intro j _ hji
      rw [real_inner_smul_right, orthonormal_iff_ite.mp e.orthonormal i j, if_neg hji.symm, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hspanN_eq : Submodule.span ℝ (N : Set E) = V := by
    have hle : Submodule.span ℝ (N : Set E) ≤ V :=
      Submodule.span_mono (show (N : Set E) ⊆ (M : Set E) from hNM)
    have hdimN : Module.finrank ℝ (Submodule.span ℝ (N : Set E)) = Module.finrank ℝ V := by
      rw [← finrank_int_eq_finrank_real_span N, ← finrank_int_eq_finrank_real_span M]
      exact hrk
    exact Submodule.eq_of_le_of_finrank_eq hle hdimN
  let M₀ : Submodule ℤ V := M.comap (V.subtype.restrictScalars ℤ)
  let N₀ : Submodule ℤ V := N.comap (V.subtype.restrictScalars ℤ)
  let M' : Submodule ℤ (Fin r → ℝ) := M₀.map (Φ.restrictScalars ℤ)
  let N' : Submodule ℤ (Fin r → ℝ) := N₀.map (Φ.restrictScalars ℤ)
  have hN'M' : N' ≤ M' := Submodule.map_mono (fun _ hx => hNM hx)
  let eM_iso : M ≃ₗ[ℤ] M' :=
    { toFun := fun x => ⟨Φ ⟨x.1, Submodule.subset_span x.2⟩,
        ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
      invFun := fun y => ⟨(Ψ y.1 : E), by
        rcases y.2 with ⟨v, hv, hvEq⟩
        have hvy : Ψ y.1 = v := by rw [← hvEq]; exact hΨΦ v
        rw [hvy]; exact hv⟩
      map_add' := fun x y => Subtype.ext (by funext i; exact inner_add_right _ _ _)
      map_smul' := fun n x => Subtype.ext (by
        funext i
        change inner ℝ (e i) (n • (⟨x.1, Submodule.subset_span x.2⟩ : V)) =
          n • inner ℝ (e i) (⟨x.1, Submodule.subset_span x.2⟩ : V)
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
          smul_eq_mul])
      left_inv := fun x => Subtype.ext (by change (Ψ (Φ _) : E) = x.1; rw [hΨΦ])
      right_inv := fun y => Subtype.ext (by change Φ (Ψ y.1) = y.1; exact hΦΨ y.1) }
  have hΨcont : Continuous Ψ := by
    change Continuous fun c : Fin r → ℝ => ∑ i : Fin r, c i • e i
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have : DiscreteTopology M' :=
    DiscreteTopology.of_continuous_injective (f := eM_iso.symm)
      (Continuous.subtype_mk (continuous_subtype_val.comp (hΨcont.comp continuous_subtype_val)) _)
      eM_iso.symm.injective
  have hM'_span : Submodule.span ℝ (M' : Set (Fin r → ℝ)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro c
    have hmem0 : Ψ c ∈ Submodule.span ℝ (M₀ : Set V) := by
      have h1 : Submodule.span ℝ (M₀ : Set V) = ⊤ := Submodule.span_span_coe_preimage
      rw [h1]; trivial
    have hmap : Submodule.map Φ (Submodule.span ℝ (M₀ : Set V)) =
        Submodule.span ℝ (M' : Set (Fin r → ℝ)) := by
      rw [Submodule.map_span]; rfl
    have : Φ (Ψ c) ∈ Submodule.span ℝ (M' : Set (Fin r → ℝ)) := by
      rw [← hmap]; exact ⟨Ψ c, hmem0, rfl⟩
    rwa [hΦΨ] at this
  have : IsZLattice ℝ M' := ⟨hM'_span⟩
  have hcovM' : ZLattice.covolume M' volume = covol M := by
    let bM : Basis (Fin r) ℤ M := Module.finBasis ℤ M
    let bM' : Basis (Fin r) ℤ M' := bM.map eM_iso
    have hcov_det : ZLattice.covolume M' volume = |(Matrix.of (Subtype.val ∘ bM')).det| :=
      ZLattice.covolume_eq_det M' bM'
    let A : Matrix (Fin r) (Fin r) ℝ := Matrix.of (Subtype.val ∘ bM')
    have hgram : Matrix.gram ℝ (fun j => (bM j : E)) = A * A.transpose := by
      ext j k
      rw [Matrix.gram_apply, Matrix.mul_apply]
      have hparseval : inner ℝ (⟨(bM j : E), Submodule.subset_span (bM j).2⟩ : V)
          (⟨(bM k : E), Submodule.subset_span (bM k).2⟩ : V) =
          ∑ i : Fin r, inner ℝ (e i) (⟨(bM j : E), Submodule.subset_span (bM j).2⟩ : V) *
            inner ℝ (e i) (⟨(bM k : E), Submodule.subset_span (bM k).2⟩ : V) := by
        have hj := (hΨΦ ⟨(bM j : E), Submodule.subset_span (bM j).2⟩).symm
        have hk := (hΨΦ ⟨(bM k : E), Submodule.subset_span (bM k).2⟩).symm
        conv_lhs => rw [hj, hk]
        simp only [Ψ, Φ, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
          real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
        refine Finset.sum_congr rfl fun i _ => by simp [mul_comm]
      change inner ℝ (⟨(bM j : E), Submodule.subset_span (bM j).2⟩ : V)
          (⟨(bM k : E), Submodule.subset_span (bM k).2⟩ : V) =
        ∑ i : Fin r, A j i * A.transpose i k
      rw [hparseval]
      rfl
    rw [covol_eq_sqrt_det_gram M bM, hgram, Matrix.det_mul, Matrix.det_transpose, ← sq,
      Real.sqrt_sq_eq_abs, hcov_det]
  have : DiscreteTopology N' := discreteTopology_of_le hN'M'
  have hN'_span : Submodule.span ℝ (N' : Set (Fin r → ℝ)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro c
    have hmemV : (Ψ c : E) ∈ Submodule.span ℝ (N : Set E) := hspanN_eq.symm ▸ (Ψ c).2
    have hmem0 : Ψ c ∈ Submodule.span ℝ (N₀ : Set V) := by
      have h1 : (Submodule.span ℝ (N₀ : Set V)).map V.subtype = Submodule.span ℝ (N : Set E) := by
        rw [Submodule.map_span]
        congr 1; ext x; constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx; exact ⟨⟨x, hspanN_eq ▸ Submodule.subset_span hx⟩, hx, rfl⟩
      rw [← h1] at hmemV
      rcases hmemV with ⟨y, hy, hyEq⟩
      have : y = Ψ c := Subtype.ext hyEq
      rwa [← this]
    have hmap : Submodule.map Φ (Submodule.span ℝ (N₀ : Set V)) =
        Submodule.span ℝ (N' : Set (Fin r → ℝ)) := by
      rw [Submodule.map_span]; rfl
    have : Φ (Ψ c) ∈ Submodule.span ℝ (N' : Set (Fin r → ℝ)) := by
      rw [← hmap]; exact ⟨Ψ c, hmem0, rfl⟩
    rwa [hΦΨ] at this
  have : IsZLattice ℝ N' := ⟨hN'_span⟩
  -- Check `ZLattice.covolume N' volume = covol N` via basis Gram matrix.
  let eN_iso : N ≃ₗ[ℤ] N' :=
    { toFun := fun x => ⟨Φ ⟨x.1, hspanN_eq ▸ Submodule.subset_span x.2⟩,
        ⟨⟨x.1, hspanN_eq ▸ Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
      invFun := fun y => ⟨(Ψ y.1 : E), by
        rcases y.2 with ⟨v, hv, hvEq⟩
        have hvy : Ψ y.1 = v := by rw [← hvEq]; exact hΨΦ v
        rw [hvy]; exact hv⟩
      map_add' := fun x y => Subtype.ext (by funext i; exact inner_add_right _ _ _)
      map_smul' := fun n x => Subtype.ext (by
        funext i
        change inner ℝ (e i) (n • (⟨x.1, hspanN_eq ▸ Submodule.subset_span x.2⟩ : V)) =
          n • inner ℝ (e i) (⟨x.1, hspanN_eq ▸ Submodule.subset_span x.2⟩ : V)
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
          smul_eq_mul])
      left_inv := fun x => Subtype.ext (by change (Ψ (Φ _) : E) = x.1; rw [hΨΦ])
      right_inv := fun y => Subtype.ext (by change Φ (Ψ y.1) = y.1; exact hΦΨ y.1) }
  have hcovN' : ZLattice.covolume N' volume = covol N := by
    let bN : Basis (Fin r) ℤ N := (Module.finBasis ℤ N).reindex (finCongr hrk)
    let bN' : Basis (Fin r) ℤ N' := bN.map eN_iso
    have hcov_det : ZLattice.covolume N' volume = |(Matrix.of (Subtype.val ∘ bN')).det| :=
      ZLattice.covolume_eq_det N' bN'
    let A : Matrix (Fin r) (Fin r) ℝ := Matrix.of (Subtype.val ∘ bN')
    have hgram : Matrix.gram ℝ (fun j => (bN j : E)) = A * A.transpose := by
      ext j k
      rw [Matrix.gram_apply, Matrix.mul_apply]
      have hparseval : inner ℝ (⟨(bN j : E), hspanN_eq ▸ Submodule.subset_span (bN j).2⟩ : V)
          (⟨(bN k : E), hspanN_eq ▸ Submodule.subset_span (bN k).2⟩ : V) =
          ∑ i : Fin r, inner ℝ (e i) (⟨(bN j : E), hspanN_eq ▸ Submodule.subset_span (bN j).2⟩ : V) *
            inner ℝ (e i) (⟨(bN k : E), hspanN_eq ▸ Submodule.subset_span (bN k).2⟩ : V) := by
        have hj := (hΨΦ ⟨(bN j : E), hspanN_eq ▸ Submodule.subset_span (bN j).2⟩).symm
        have hk := (hΨΦ ⟨(bN k : E), hspanN_eq ▸ Submodule.subset_span (bN k).2⟩).symm
        conv_lhs => rw [hj, hk]
        simp only [Ψ, Φ, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
          real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
        refine Finset.sum_congr rfl fun i _ => by simp [mul_comm]
      change inner ℝ (⟨(bN j : E), hspanN_eq ▸ Submodule.subset_span (bN j).2⟩ : V)
          (⟨(bN k : E), hspanN_eq ▸ Submodule.subset_span (bN k).2⟩ : V) =
        ∑ i : Fin r, A j i * A.transpose i k
      rw [hparseval]
      rfl
    rw [covol_eq_sqrt_det_gram N bN, hgram, Matrix.det_mul, Matrix.det_transpose, ← sq,
      Real.sqrt_sq_eq_abs, hcov_det]
  -- Compare `ZLattice.covolume N' volume` and `ZLattice.covolume M' volume` via coset tiling!
  let H : AddSubgroup M' := (N'.comap M'.subtype).toAddSubgroup
  have hQequiv : (M ⧸ (N.comap M.subtype).toAddSubgroup) ≃ (M' ⧸ H) := by
    refine (QuotientAddGroup.congr (N.comap M.subtype).toAddSubgroup H eM_iso.toAddEquiv ?_).toEquiv
    ext y
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      Submodule.coe_subtype, H]
    constructor
    · rintro ⟨x, hxN, rfl⟩
      exact ⟨⟨x.1, Submodule.subset_span (hNM hxN)⟩, hxN, rfl⟩
    · rintro ⟨v, hvN, hvEq⟩
      refine ⟨⟨v.1, hNM hvN⟩, hvN, Subtype.ext hvEq⟩
  have : Finite (M ⧸ (N.comap M.subtype).toAddSubgroup) :=
    (finite_quotient_of_le_same_rank hNM hrk).1
  have hFinQ : Finite (M' ⧸ H) :=
    Finite.of_equiv _ hQequiv
  let : Fintype (M' ⧸ H) := Fintype.ofFinite (M' ⧸ H)
  have hIndex_eq : latIndex M N = Fintype.card (M' ⧸ H) := by
    unfold latIndex
    rw [AddSubgroup.index_eq_card, Nat.card_congr hQequiv, Nat.card_eq_fintype_card]
  -- Build fundamental domain `F_N = ⋃ q : M' ⧸ H, (s q : Fin r → ℝ) +ᵥ F_M` for `N'`.
  let bM' : Basis (Fin r) ℤ M' := (Module.finBasis ℤ M).map eM_iso
  let F_M : Set (Fin r → ℝ) := ZSpan.fundamentalDomain (bM'.ofZLatticeBasis ℝ)
  have hFM_fund : IsAddFundamentalDomain M'.toAddSubgroup F_M volume :=
    ZLattice.isAddFundamentalDomain bM' volume
  have hFM_fin : volume F_M ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (bM'.ofZLatticeBasis ℝ)).measure_lt_top.ne
  let s : (M' ⧸ H) → M' := Quotient.out
  let F_N : Set (Fin r → ℝ) := ⋃ q : M' ⧸ H, ((s q : M') : Fin r → ℝ) +ᵥ F_M
  have hFN_meas : NullMeasurableSet F_N volume :=
    NullMeasurableSet.iUnion fun q => hFM_fund.nullMeasurableSet.vadd _
  have hFN_covers : ∀ᵐ x ∂volume, ∃ g : N'.toAddSubgroup, g +ᵥ x ∈ F_N := by
    filter_upwards [hFM_fund.ae_covers] with x hx
    rcases hx with ⟨m, hm⟩
    let q : M' ⧸ H := QuotientAddGroup.mk (-m)
    have hsum_H : s q + m ∈ H := by
      have h1 : QuotientAddGroup.mk (s := H) (s q) = QuotientAddGroup.mk (s := H) (-m) :=
        Quotient.out_eq q
      rw [QuotientAddGroup.eq] at h1
      have hneg : -(-(s q) + -m) ∈ H := H.neg_mem h1
      have heq : -(-(s q) + -m) = s q + m := by abel
      rwa [heq] at hneg
    have hsum_N : (s q : Fin r → ℝ) + (m : Fin r → ℝ) ∈ N' := hsum_H
    refine ⟨⟨(s q : Fin r → ℝ) + (m : Fin r → ℝ), hsum_N⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    have h1 : (⟨(s q : Fin r → ℝ) + (m : Fin r → ℝ), hsum_N⟩ : N'.toAddSubgroup) +ᵥ x =
        ((s q : M') : Fin r → ℝ) +ᵥ (m +ᵥ x) := by
      change ((s q : Fin r → ℝ) + (m : Fin r → ℝ)) + x = (s q : Fin r → ℝ) + ((m : Fin r → ℝ) + x)
      abel
    rw [h1]
    exact Set.vadd_mem_vadd_set hm
  have hFN_disj : Pairwise (Function.onFun (AEDisjoint volume) fun g : N'.toAddSubgroup => g +ᵥ F_N) := by
    intro g₁ g₂ hne
    change volume ((g₁ +ᵥ F_N) ∩ (g₂ +ᵥ F_N)) = 0
    have hsub : (g₁ +ᵥ F_N) ∩ (g₂ +ᵥ F_N) ⊆
        ⋃ q₁ : M' ⧸ H, ⋃ q₂ : M' ⧸ H,
          ((⟨(g₁ : Fin r → ℝ), hN'M' g₁.2⟩ + s q₁ : M'.toAddSubgroup) +ᵥ F_M) ∩
          ((⟨(g₂ : Fin r → ℝ), hN'M' g₂.2⟩ + s q₂ : M'.toAddSubgroup) +ᵥ F_M) := by
      intro x hx
      rcases hx with ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, hy₂eq⟩⟩
      rcases Set.mem_iUnion.mp hy₁ with ⟨q₁, ⟨z₁, hz₁, rfl⟩⟩
      rcases Set.mem_iUnion.mp hy₂ with ⟨q₂, ⟨z₂, hz₂, rfl⟩⟩
      refine Set.mem_iUnion.mpr ⟨q₁, Set.mem_iUnion.mpr ⟨q₂, ?_, ?_⟩⟩
      · refine ⟨z₁, hz₁, ?_⟩
        change ((g₁ : Fin r → ℝ) + (s q₁ : Fin r → ℝ)) + z₁ =
          (g₁ : Fin r → ℝ) + ((s q₁ : Fin r → ℝ) + z₁)
        abel
      · refine ⟨z₂, hz₂, ?_⟩
        have h2 : (g₂ : Fin r → ℝ) + ((s q₂ : Fin r → ℝ) + z₂) =
            (g₁ : Fin r → ℝ) + ((s q₁ : Fin r → ℝ) + z₁) := hy₂eq
        change ((g₂ : Fin r → ℝ) + (s q₂ : Fin r → ℝ)) + z₂ =
          (g₁ : Fin r → ℝ) + ((s q₁ : Fin r → ℝ) + z₁)
        rw [← h2]; abel
    refine measure_mono_null hsub ?_
    refine measure_iUnion_null fun q₁ => measure_iUnion_null fun q₂ => ?_
    have hneM : (⟨(g₁ : Fin r → ℝ), hN'M' g₁.2⟩ + s q₁ : M'.toAddSubgroup) ≠
        (⟨(g₂ : Fin r → ℝ), hN'M' g₂.2⟩ + s q₂ : M'.toAddSubgroup) := by
      intro heq
      have hq_eq : q₁ = q₂ := by
        have hmk : QuotientAddGroup.mk (s := H) (⟨(g₁ : Fin r → ℝ), hN'M' g₁.2⟩ + s q₁) =
            QuotientAddGroup.mk (s := H) (⟨(g₂ : Fin r → ℝ), hN'M' g₂.2⟩ + s q₂) :=
          congrArg (QuotientAddGroup.mk (s := H)) heq
        have hg1 : QuotientAddGroup.mk (s := H) ⟨(g₁ : Fin r → ℝ), hN'M' g₁.2⟩ = 0 :=
          (QuotientAddGroup.eq_zero_iff _).mpr g₁.2
        have hg2 : QuotientAddGroup.mk (s := H) ⟨(g₂ : Fin r → ℝ), hN'M' g₂.2⟩ = 0 :=
          (QuotientAddGroup.eq_zero_iff _).mpr g₂.2
        have hs1 : QuotientAddGroup.mk (s := H) (s q₁) = q₁ := Quotient.out_eq q₁
        have hs2 : QuotientAddGroup.mk (s := H) (s q₂) = q₂ := Quotient.out_eq q₂
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, hg1, hg2, zero_add, zero_add,
          hs1, hs2] at hmk
        exact hmk
      subst hq_eq
      have hg_eq : (g₁ : Fin r → ℝ) = (g₂ : Fin r → ℝ) := by
        have hval := congrArg Subtype.val heq
        change (g₁ : Fin r → ℝ) + (s q₁ : Fin r → ℝ) = (g₂ : Fin r → ℝ) + (s q₁ : Fin r → ℝ) at hval
        exact add_right_cancel hval
      exact hne (Subtype.ext hg_eq)
    exact hFM_fund.aedisjoint hneM
  have hFN_fund : IsAddFundamentalDomain N'.toAddSubgroup F_N volume :=
    ⟨hFN_meas, hFN_covers, hFN_disj⟩
  -- Compute `volume F_N = Fintype.card (M' ⧸ H) * volume F_M`.
  have hpair_disj : Pairwise (Function.onFun (AEDisjoint volume) fun q : M' ⧸ H => ((s q : M') : Fin r → ℝ) +ᵥ F_M) := by
    intro q₁ q₂ hq
    have hne : s q₁ ≠ s q₂ := fun h => hq (by
      have hs1 : QuotientAddGroup.mk (s := H) (s q₁) = q₁ := Quotient.out_eq q₁
      have hs2 : QuotientAddGroup.mk (s := H) (s q₂) = q₂ := Quotient.out_eq q₂
      rw [← hs1, ← hs2, h])
    exact hFM_fund.aedisjoint hne
  have hvol_FN : volume F_N = (Fintype.card (M' ⧸ H) : ℝ≥0∞) * volume F_M := by
    rw [show F_N = ⋃ q ∈ (Finset.univ : Finset (M' ⧸ H)), ((s q : M') : Fin r → ℝ) +ᵥ F_M by
      simp [F_N]]
    rw [measure_biUnion_finset₀ (fun q₁ _ q₂ _ h => hpair_disj h)
      (fun q _ => hFM_fund.nullMeasurableSet.vadd _)]
    have hterm : ∀ q : M' ⧸ H, volume (((s q : M') : Fin r → ℝ) +ᵥ F_M) = volume F_M :=
      fun q => measure_vadd volume _ F_M
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← hcovN', ← hcovM',
    ZLattice.covolume_eq_measure_fundamentalDomain N' volume hFN_fund,
    ZLattice.covolume_eq_measure_fundamentalDomain M' volume hFM_fund,
    Measure.real, Measure.real, hvol_FN, ENNReal.toReal_mul, ENNReal.toReal_natCast, hIndex_eq]

/-- **Exact Full-Rank Sublattice Index–Degree Formula**:
`degAr N = degAr M - Real.log (latIndex M N : ℝ)`. -/
theorem degAr_eq_degAr_sub_log_index {M N : Submodule ℤ E} [DiscreteTopology M]
    (hNM : N ≤ M) (hrk : rk N = rk M) :
    degAr N = degAr M - Real.log (latIndex M N : ℝ) := by
  have : DiscreteTopology N := discreteTopology_of_le hNM
  have hIdx_pos : (0 : ℝ) < (latIndex M N : ℝ) :=
    Nat.cast_pos.mpr (finite_quotient_of_le_same_rank hNM hrk).2
  unfold degAr
  rw [covol_eq_index_mul_covol hNM hrk, Real.log_mul hIdx_pos.ne' (covol_pos M).ne']
  ring

/-- **Exact Full-Rank Sublattice Index–Slope Formula**:
`slope N = slope M - Real.log (latIndex M N : ℝ) / rk M`. -/
theorem slope_eq_slope_sub_log_index_div_rk {M N : Submodule ℤ E} [DiscreteTopology M]
    (hNM : N ≤ M) (hrk : rk N = rk M) :
    ArakelovCovolume.slope N =
      ArakelovCovolume.slope M - Real.log (latIndex M N : ℝ) / (rk M : ℝ) := by
  unfold ArakelovCovolume.slope
  rw [hrk, degAr_eq_degAr_sub_log_index hNM hrk, sub_div]

/-- **Concrete Bost Maximal-Slope Morphism Bound (`muMax_le_of_bounded_injection`)**:
for ANY nonzero discrete lattice `L_N ⊂ EN`, discrete lattice `L_M ⊂ EM`, injective `ℤ`-linear
morphism `φ : L_N →ₗ[ℤ] L_M`, and Lipschitz bound `‖φ x‖ ≤ C * ‖x‖`:
`ArakelovCovolume.muMax L_N ≤ ArakelovCovolume.muMax L_M + Real.log C`! -/
theorem muMax_le_of_bounded_injection
    (L_N : Submodule ℤ EN) (L_M : Submodule ℤ EM)
    [DiscreteTopology L_N] [DiscreteTopology L_M] (hN0 : L_N ≠ ⊥)
    (φ : L_N →ₗ[ℤ] L_M) (C : ℝ) (hφ : Function.Injective φ)
    (hC : ∀ x : L_N, ‖((φ x : L_M) : EM)‖ ≤ C * ‖(x : EN)‖) :
    muMax L_N ≤ muMax L_M + Real.log C := by
  unfold muMax
  have hne : (slopes L_N).Nonempty := ⟨ArakelovCovolume.slope L_N, L_N, le_rfl, hN0, rfl⟩
  refine csSup_le hne ?_
  rintro _ ⟨K, hKN, hK0, rfl⟩
  have : DiscreteTopology K := discreteTopology_of_le hKN
  let φK : K →ₗ[ℤ] L_M := φ.comp (Submodule.inclusion hKN)
  have hφK_inj : Function.Injective φK := hφ.comp (Submodule.inclusion_injective hKN)
  have hφK_C : ∀ x : K, ‖((φK x : L_M) : EM)‖ ≤ C * ‖(x : EN)‖ := fun x =>
    hC ⟨(x : EN), hKN x.2⟩
  exact bost_slope_inequality K L_M hK0 φK C hφK_inj hφK_C

/-- **Exponential-Norm Form (`muMax_le_of_exp_bounded_injection`)**:
if `‖φ x‖ ≤ Real.exp C_φ * ‖x‖` for an injective `φ : L_N →ₗ[ℤ] L_M`, then
`muMax L_N ≤ muMax L_M + C_φ`. -/
theorem muMax_le_of_exp_bounded_injection
    (L_N : Submodule ℤ EN) (L_M : Submodule ℤ EM)
    [DiscreteTopology L_N] [DiscreteTopology L_M] (hN0 : L_N ≠ ⊥)
    (φ : L_N →ₗ[ℤ] L_M) (C_φ : ℝ) (hφ : Function.Injective φ)
    (hC : ∀ x : L_N, ‖((φ x : L_M) : EM)‖ ≤ Real.exp C_φ * ‖(x : EN)‖) :
    muMax L_N ≤ muMax L_M + C_φ := by
  simpa only [Real.log_exp] using
    muMax_le_of_bounded_injection L_N L_M hN0 φ (Real.exp C_φ) hφ hC

/-- **Operator-Norm `ContinuousLinearMap` Form (`muMax_le_of_continuousLinearMap_injection`)**:
if `φ : EN →L[ℝ] EM` maps `L_N` injectively into `L_M`, then
`muMax L_N ≤ muMax L_M + Real.log ‖φ‖`! -/
theorem muMax_le_of_continuousLinearMap_injection
    (L_N : Submodule ℤ EN) (L_M : Submodule ℤ EM)
    [DiscreteTopology L_N] [DiscreteTopology L_M] (hN0 : L_N ≠ ⊥)
    (φ : EN →L[ℝ] EM) (hmap : ∀ x ∈ L_N, φ x ∈ L_M)
    (hinj : ∀ x ∈ L_N, φ x = 0 → x = 0) :
    muMax L_N ≤ muMax L_M + Real.log ‖φ‖ := by
  let φZ : L_N →ₗ[ℤ] L_M :=
    { toFun := fun x => ⟨φ x.1, hmap x.1 x.2⟩
      map_add' := fun a b => Subtype.ext (map_add φ a.1 b.1)
      map_smul' := fun c a => Subtype.ext (map_zsmul φ c a.1) }
  have hφZ : Function.Injective φZ := by
    intro a b hab
    have h0 : φ (a.1 - b.1) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val hab
    exact Subtype.ext (sub_eq_zero.mp (hinj (a.1 - b.1) (L_N.sub_mem a.2 b.2) h0))
  exact muMax_le_of_bounded_injection L_N L_M hN0 φZ ‖φ‖ hφZ (fun x => φ.le_opNorm x.1)

/-- **Concrete Arakelov–Bost–Index Slope Lower Bound (`slope_ge_of_index_and_norm`)**:
for ANY injective full-rank morphism `φ : L_N →ₗ[ℤ] L_M` (`L_N ≠ ⊥`, `rk L_N = rk L_M`) with
coercivity bound `‖x‖ ≤ C_inv * ‖φ x‖` and finite cokernel index
`I_φ = latIndex L_M (LinearMap.range (L_M.subtype.comp φ))`:
1. `0 < I_φ`,
2. `ArakelovCovolume.slope L_M - Real.log C_inv - Real.log (I_φ : ℝ) / rk L_M ≤ ArakelovCovolume.slope L_N`! -/
theorem slope_ge_of_index_and_norm
    (L_N : Submodule ℤ EN) (L_M : Submodule ℤ EM)
    [DiscreteTopology L_N] [DiscreteTopology L_M] (hN0 : L_N ≠ ⊥)
    (φ : L_N →ₗ[ℤ] L_M) (C_inv : ℝ) (hφ : Function.Injective φ)
    (hrk : rk L_N = rk L_M)
    (hC_inv : ∀ x : L_N, ‖(x : EN)‖ ≤ C_inv * ‖((φ x : L_M) : EM)‖) :
    let imPhi : Submodule ℤ EM := LinearMap.range (L_M.subtype.comp φ)
    0 < latIndex L_M imPhi ∧
    ArakelovCovolume.slope L_M - Real.log C_inv -
        Real.log (latIndex L_M imPhi : ℝ) / (rk L_M : ℝ) ≤
      ArakelovCovolume.slope L_N := by
  intro imPhi
  let g : L_N →ₗ[ℤ] EM := L_M.subtype.comp φ
  have hginj : Function.Injective g := L_M.injective_subtype.comp hφ
  have him_le : imPhi ≤ L_M := by rintro _ ⟨x, rfl⟩; exact (φ x).2
  have : DiscreteTopology imPhi := discreteTopology_of_le him_le
  let e : L_N ≃ₗ[ℤ] imPhi := LinearEquiv.ofInjective g hginj
  have hrk_im : rk imPhi = rk L_M := e.finrank_eq.symm.trans hrk
  have hIdx_pos : 0 < latIndex L_M imPhi :=
    (finite_quotient_of_le_same_rank him_le hrk_im).2
  refine ⟨hIdx_pos, ?_⟩
  obtain ⟨x₀, hx₀N, hx₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hφx₀ : ((φ ⟨x₀, hx₀N⟩ : L_M) : EM) ≠ 0 := by
    intro h0
    apply hx₀ne
    have : φ ⟨x₀, hx₀N⟩ = φ 0 := by rw [map_zero]; exact Subtype.ext h0
    exact congrArg Subtype.val (hφ this)
  have hCpos : 0 < C_inv := by
    have h1 := hC_inv ⟨x₀, hx₀N⟩
    have h2 : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀ne
    have h3 : 0 < ‖((φ ⟨x₀, hx₀N⟩ : L_M) : EM)‖ := norm_pos_iff.mpr hφx₀
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  -- Apply `gram_det_le` to `e.symm : imPhi → L_N`!
  set r := rk L_N
  have hrpos : 0 < r := rk_pos_of_ne_bot L_N hN0
  let b := Module.finBasis ℤ L_N
  have hcN : covol L_N = Real.sqrt (Matrix.gram ℝ (fun i => (b i : EN))).det :=
    covol_eq_sqrt_det_gram L_N b
  have hcIm : covol imPhi = Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : L_M) : EM))).det :=
    covol_eq_sqrt_det_gram imPhi (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • (b i : EN)‖ ≤ C_inv * ‖∑ i, (n i : ℝ) • ((φ (b i) : L_M) : EM)‖ := by
    intro n
    have h2 := hC_inv (∑ i, n i • b i)
    simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => ((φ (b i) : L_M) : EM))
    (fun i => (b i : EN)) C_inv hint
  have hdet := gram_det_le (fun i => ((φ (b i) : L_M) : EM)) (fun i => (b i : EN)) C_inv hreal
  have hcov_le : covol L_N ≤ C_inv ^ r * covol imPhi := by
    rw [hcN, hcIm]
    calc Real.sqrt (Matrix.gram ℝ (fun i => (b i : EN))).det
        ≤ Real.sqrt (C_inv ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => ((φ (b i) : L_M) : EM))).det) := Real.sqrt_le_sqrt hdet
      _ = C_inv ^ r * Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : L_M) : EM))).det := by
        rw [Fintype.card_fin, show C_inv ^ (2 * r) = (C_inv ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hlog : Real.log (covol L_N) ≤ (r : ℝ) * Real.log C_inv + Real.log (covol imPhi) := by
    have h2 := Real.log_le_log (covol_pos L_N) hcov_le
    rwa [Real.log_mul (by positivity) (covol_pos imPhi).ne', Real.log_pow] at h2
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hrpos
  have hslope_im_le : ArakelovCovolume.slope imPhi - Real.log C_inv ≤ ArakelovCovolume.slope L_N := by
    unfold ArakelovCovolume.slope degAr
    rw [show rk imPhi = r from e.finrank_eq.symm, sub_eq_add_neg,
      div_add' _ _ _ hrR.ne', div_le_div_iff_of_pos_right hrR]
    linarith
  have hslope_im_eq := slope_eq_slope_sub_log_index_div_rk him_le hrk_im
  linarith

/-- **Reverse-Direction Bounded Injection Slope Lower Bound (`slope_ge_of_bounded_injection_to_target`)**:
if `ψ : L_M →ₗ[ℤ] L_N` is injective with `rk L_M = rk L_N` and `‖ψ y‖ ≤ C * ‖y‖`, then
`slope L_M - Real.log C + Real.log (latIndex L_N (im ψ)) / rk L_M ≤ slope L_N`
(and in particular `slope L_M - Real.log C ≤ slope L_N`)! -/
theorem slope_ge_of_bounded_injection_to_target
    (L_M : Submodule ℤ EM) (L_N : Submodule ℤ EN)
    [DiscreteTopology L_M] [DiscreteTopology L_N] (hM0 : L_M ≠ ⊥)
    (ψ : L_M →ₗ[ℤ] L_N) (C : ℝ) (hψ : Function.Injective ψ)
    (hrk : rk L_M = rk L_N)
    (hC : ∀ y : L_M, ‖((ψ y : L_N) : EN)‖ ≤ C * ‖(y : EM)‖) :
    let imPsi : Submodule ℤ EN := LinearMap.range (L_N.subtype.comp ψ)
    0 < latIndex L_N imPsi ∧
    ArakelovCovolume.slope L_M - Real.log C +
        Real.log (latIndex L_N imPsi : ℝ) / (rk L_M : ℝ) ≤
      ArakelovCovolume.slope L_N := by
  intro imPsi
  let g : L_M →ₗ[ℤ] EN := L_N.subtype.comp ψ
  have hginj : Function.Injective g := L_N.injective_subtype.comp hψ
  have him_le : imPsi ≤ L_N := by rintro _ ⟨y, rfl⟩; exact (ψ y).2
  have : DiscreteTopology imPsi := discreteTopology_of_le him_le
  let e : L_M ≃ₗ[ℤ] imPsi := LinearEquiv.ofInjective g hginj
  have hrk_im : rk imPsi = rk L_N := e.finrank_eq.symm.trans hrk
  have hIdx_pos : 0 < latIndex L_N imPsi :=
    (finite_quotient_of_le_same_rank him_le hrk_im).2
  refine ⟨hIdx_pos, ?_⟩
  obtain ⟨y₀, hy₀M, hy₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
  have hψy₀ : ((ψ ⟨y₀, hy₀M⟩ : L_N) : EN) ≠ 0 := by
    intro h0
    apply hy₀ne
    have : ψ ⟨y₀, hy₀M⟩ = ψ 0 := by rw [map_zero]; exact Subtype.ext h0
    exact congrArg Subtype.val (hψ this)
  have hCpos : 0 < C := by
    have h1 := hC ⟨y₀, hy₀M⟩
    have h2 : 0 < ‖y₀‖ := norm_pos_iff.mpr hy₀ne
    have h3 : 0 < ‖((ψ ⟨y₀, hy₀M⟩ : L_N) : EN)‖ := norm_pos_iff.mpr hψy₀
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h2.le]
  set r := rk L_M
  have hrpos : 0 < r := rk_pos_of_ne_bot L_M hM0
  let b := Module.finBasis ℤ L_M
  have hcM : covol L_M = Real.sqrt (Matrix.gram ℝ (fun i => (b i : EM))).det :=
    covol_eq_sqrt_det_gram L_M b
  have hcIm : covol imPsi = Real.sqrt (Matrix.gram ℝ (fun i => ((ψ (b i) : L_N) : EN))).det :=
    covol_eq_sqrt_det_gram imPsi (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((ψ (b i) : L_N) : EN)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : EM)‖ := by
    intro n
    have h2 := hC (∑ i, n i • b i)
    simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : EM))
    (fun i => ((ψ (b i) : L_N) : EN)) C hint
  have hdet := gram_det_le (fun i => (b i : EM)) (fun i => ((ψ (b i) : L_N) : EN)) C hreal
  have hcov_le : covol imPsi ≤ C ^ r * covol L_M := by
    rw [hcIm, hcM]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((ψ (b i) : L_N) : EN))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => (b i : EM))).det) := Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : EM))).det := by
        rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hlog : Real.log (covol imPsi) ≤ (r : ℝ) * Real.log C + Real.log (covol L_M) := by
    have h2 := Real.log_le_log (covol_pos imPsi) hcov_le
    rwa [Real.log_mul (by positivity) (covol_pos L_M).ne', Real.log_pow] at h2
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hrpos
  have hslope_le : ArakelovCovolume.slope L_M - Real.log C ≤ ArakelovCovolume.slope imPsi := by
    unfold ArakelovCovolume.slope degAr
    rw [show rk imPsi = r from e.finrank_eq.symm, sub_eq_add_neg,
      div_add' _ _ _ hrR.ne', div_le_div_iff_of_pos_right hrR]
    linarith
  have hslope_im_eq := slope_eq_slope_sub_log_index_div_rk him_le hrk_im
  rw [← hrk] at hslope_im_eq
  linarith

/-- **Arakelov Exact-Sequence Slope Bounds** for `0 → M → L → Q = quotLat L M → 0`:
for any saturated proper nonzero sublattice `M ⊂ L`:
1. `rk L = rk M + rk Q` and `degAr L = degAr M + degAr Q`,
2. `muMax M ≤ muMax L` and `muMin L ≤ muMin Q`,
3. `(rk M : ℝ) * muMin M + (rk Q : ℝ) * muMin Q ≤ degAr L ≤ (rk M : ℝ) * muMax M + (rk Q : ℝ) * muMax Q`! -/
theorem exact_seq_slope_bounds {L M : Submodule ℤ E} [DiscreteTopology L]
    (hM : IsSaturated L M) (hM0 : M ≠ ⊥) (hMne : M ≠ L) :
    let Q := quotLat L M
    rk L = rk M + rk Q ∧
    degAr L = degAr M + degAr Q ∧
    muMax M ≤ muMax L ∧
    muMin L ≤ muMin Q ∧
    (rk M : ℝ) * muMin M + (rk Q : ℝ) * muMin Q ≤ degAr L ∧
    degAr L ≤ (rk M : ℝ) * muMax M + (rk Q : ℝ) * muMax Q := by
  intro Q
  have : DiscreteTopology M := discreteTopology_of_le hM.1
  have : DiscreteTopology Q := discreteTopology_quotLat hM
  have hQ0 : Q ≠ ⊥ := RHDirect.Stage4ArakelovBost.quotLat_ne_bot_of_lt hM hMne
  have hrk_add := rk_add_quotLat hM
  have hdeg_add := degAr_eq_add_quotLat hM
  have hmuMax_le := muMax_mono L M hM.1 hM0
  have hmuMin_le : muMin L ≤ muMin Q := by
    -- Every saturated quotient of `Q` is a saturated quotient of `L` via `quotLat_quotLat`!
    let F_Q := RHDirect.Stage4ArakelovBost.canonicalHN Q
    have hpos := F_Q.len_pos_of_ne_bot hQ0
    let ilast : Fin F_Q.len := ⟨F_Q.len - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
    rw [F_Q.muMin_eq_last_hnSlope hQ0]
    let S := F_Q.step ilast.castSucc
    have hSsat : IsSaturated Q S := F_Q.step_saturated _
    have hlast_succ : ilast.succ = Fin.last F_Q.len := by ext; simp [ilast]; omega
    have hquot_last : F_Q.quot ilast = quotLat Q S := by
      unfold RHDirect.Stage4ArakelovBost.HNFiltration.quot
      rw [hlast_succ, F_Q.step_last]
    let N := RHDirect.Stage4ArakelovBost.liftSub L M S
    have hNsat : IsSaturated L N := RHDirect.Stage4ArakelovBost.isSaturated_liftSub hSsat
    have hMN : M ≤ N := fun x hx => ⟨hM.1 hx, by
      change RHDirect.Stage4ArakelovBost.projOrth M x ∈ S
      rw [(RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff M x).mpr (Submodule.subset_span hx)]
      exact S.zero_mem⟩
    have hQN : quotLat N M = S := RHDirect.Stage4ArakelovBost.quotLat_liftSub hSsat.1
    have hqq : quotLat Q S = quotLat L N := by
      rw [← hQN]; exact RHDirect.Stage4ArakelovBost.quotLat_quotLat hMN
    have hNne : N ≠ L := by
      intro hNL
      have hbot : quotLat L N = ⊥ := by rw [hNL]; exact RHDirect.Stage4ArakelovBost.quotLat_self L
      have hne0 : F_Q.quot ilast ≠ ⊥ := F_Q.quot_ne_bot ilast
      rw [hquot_last, hqq, hbot] at hne0
      exact hne0 rfl
    unfold RHDirect.Stage4ArakelovBost.HNFiltration.hnSlope
    rw [hquot_last, hqq]
    exact muMin_le_slope_quotLat hNsat hNne
  have hrM : (0 : ℝ) < (rk M : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot M hM0)
  have hrQ : (0 : ℝ) < (rk Q : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot Q hQ0)
  have hbM := muMin_le_slope_le_muMax M hM0
  have hbQ := muMin_le_slope_le_muMax Q hQ0
  have hM1 : (rk M : ℝ) * muMin M ≤ degAr M := by
    have h1 := (le_div_iff₀ hrM).mp hbM.1; linarith
  have hM2 : degAr M ≤ (rk M : ℝ) * muMax M := by
    have h1 := (div_le_iff₀ hrM).mp hbM.2; linarith
  have hQ1 : (rk Q : ℝ) * muMin Q ≤ degAr Q := by
    have h1 := (le_div_iff₀ hrQ).mp hbQ.1; linarith
  have hQ2 : degAr Q ≤ (rk Q : ℝ) * muMax Q := by
    have h1 := (div_le_iff₀ hrQ).mp hbQ.2; linarith
  exact ⟨hrk_add, hdeg_add, hmuMax_le, hmuMin_le, by linarith, by linarith⟩

end IndexAndMorphismBounds

/-! ## Section 2: `Stage10GeometryOfNumbers` Bridge & Minkowski Second Theorem Gap Squeeze -/

section MinkowskiSecondTheoremBridge

/-- Exact identification of `ArakelovCovolume.covol` and `ZLattice.covolume` on `EuclideanSpace ℝ (Fin n)`. -/
theorem covol_eq_zlattice_covolume_euclidean {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    covol Λ = ZLattice.covolume Λ volume := by
  let b : Basis (Fin n) ℤ Λ := basisOfZLattice Λ
  rw [covolume_eq_abs_det Λ b, covol_eq_sqrt_det_gram Λ b]
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n => (b i : EuclideanSpace ℝ (Fin n)) j
  have hgram : Matrix.gram ℝ (fun i => (b i : EuclideanSpace ℝ (Fin n))) = A * A.transpose := by
    ext i j
    rw [Matrix.gram_apply, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct, A, Matrix.of_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]

/-- Exact identification of `Stage2SiegelReduction.succMin` and
`Stage10GeometryOfNumbers.successiveMinimum (Metric.closedBall 0 1)` on `EuclideanSpace ℝ (Fin n)`. -/
theorem succMin_eq_stage10_successiveMinimum {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (k : Fin n) :
    have hrk : rk Λ = n := by
      unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
    succMin Λ (k.cast hrk.symm) =
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ k := by
  intro hrk
  unfold succMin successiveMinimum
  congr 1
  ext t
  simp only [Fin.val_cast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, v, hvL, hvli, hvn⟩
    have hv0 : 0 < ‖v 0‖ := norm_pos_iff.mpr (hvli.ne_zero 0)
    have ht_pos : 0 < t := lt_of_lt_of_le hv0 (hvn 0)
    refine ⟨ht_pos, v, hvL, hvli, fun j => ?_⟩
    refine ⟨t⁻¹ • v j, ?_, smul_inv_smul₀ ht_pos.ne' (v j)⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht_pos.le),
      inv_mul_le_iff₀ ht_pos, mul_one]
    exact hvn j
  · rintro ⟨ht_pos, v, hvL, hvli, hvball⟩
    refine ⟨ht_pos.le, v, hvL, hvli, fun j => ?_⟩
    rcases Set.mem_smul_set.mp (hvball j) with ⟨y, hyB, hyEq⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hyB
    rw [← hyEq, norm_smul, Real.norm_of_nonneg ht_pos.le]
    nlinarith

/-- Elementary cube-in-ball volume lower bound for the Euclidean unit ball in `ℝ^n` (`n ≥ 1`):
`(2 / √n)^n ≤ ω_n`, equivalently `n * log 2 - log ω_n ≤ (n / 2) * log n`! -/
theorem unitBallVolume_ge_cube_bound {n : ℕ} (hn : 0 < n) :
    ((2 : ℝ) / Real.sqrt (n : ℝ)) ^ n ≤
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ∧
    (n : ℝ) * Real.log 2 -
        Real.log (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ≤
      ((n : ℝ) / 2) * Real.log (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  let r : ℝ := 1 / Real.sqrt (n : ℝ)
  have hr_pos : 0 < r := div_pos one_pos hsq_pos
  let Q : Set (Fin n → ℝ) := Set.univ.pi fun _ : Fin n => Set.Icc (-r) r
  have hQ_sub : Q ⊆ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹'
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x hx
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i : Fin n, ‖x i‖ ^ 2
          ≤ ∑ _i : Fin n, r ^ 2 := Finset.sum_le_sum fun i _ => by
            have hi := hx i (Set.mem_univ i)
            have habs : |x i| ≤ r := abs_le.mpr hi
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = (n : ℝ) * r ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = 1 := by
          dsimp only [r]
          rw [div_pow, one_pow, Real.sq_sqrt hn_pos.le, mul_one_div, div_self hn_pos.ne']
    nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))]
  have hvol_Q : volume Q = ENNReal.ofReal ((2 * r) ^ n) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    have hterm : volume (Set.Icc (-r) r) = ENNReal.ofReal (2 * r) := by
      rw [Real.volume_Icc]; congr 1; ring
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hterm,
      ENNReal.ofReal_pow (by positivity)]
  have hmp := PiLp.volume_preserving_toLp (Fin n)
  have hle_enn : ENNReal.ofReal ((2 * r) ^ n) ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← hvol_Q, ← hmp.measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
    exact measure_mono hQ_sub
  have hball_fin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).measure_lt_top.ne
  have hle_real : ((2 : ℝ) / Real.sqrt (n : ℝ)) ^ n ≤
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    have h1 := ENNReal.toReal_mono hball_fin hle_enn
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    have h2r : 2 * r = (2 : ℝ) / Real.sqrt (n : ℝ) := by dsimp only [r]; ring
    rwa [h2r] at h1
  refine ⟨hle_real, ?_⟩
  have hlog := Real.log_le_log (pow_pos (div_pos zero_lt_two hsq_pos) n) hle_real
  rw [Real.log_pow, Real.log_div (by norm_num) hsq_pos.ne', Real.log_sqrt hn_pos.le] at hlog
  linarith

/-- **Minkowski's Second Theorem Two-Sided Slope Squeeze (`minkowski_second_theorem_slope_squeeze`)**:
directly invoking `Stage10GeometryOfNumbers.minkowski_second_theorem_upper`,
`Stage10GeometryOfNumbers.minkowski_second_theorem_lower`, and
`Stage10GeometryOfNumbers.hermite_minkowski_bound_all_dims`, for every full-rank lattice
`Λ ⊂ EuclideanSpace ℝ (Fin n)` (`n ≥ 1`):
1. `slope Λ ≤ -(∑ i, log λ_i) / n + log 2 - log ω_n / n`,
2. `-(∑ i, log λ_i) / n + log 2 - log ω_n / n - log (n!) / n ≤ slope Λ`,
3. `slope Λ ≤ -log λ_1 + log 2 - log ω_n / n`! -/
theorem minkowski_second_theorem_slope_squeeze {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
    let lam : Fin n → ℝ := fun i => successiveMinimum B Λ i
    let ω : ℝ := (volume B).toReal
    ArakelovCovolume.slope Λ ≤ -(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) +
      Real.log 2 - Real.log ω / (n : ℝ) ∧
    -(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) +
      Real.log 2 - Real.log ω / (n : ℝ) - Real.log (n.factorial : ℝ) / (n : ℝ) ≤
      ArakelovCovolume.slope Λ ∧
    ArakelovCovolume.slope Λ ≤ -Real.log (lam ⟨0, hn⟩) + Real.log 2 - Real.log ω / (n : ℝ) := by
  intro B lam ω
  have h0B : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior B := by
    rw [mem_interior_iff_mem_nhds]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hconv : Convex ℝ B := convex_closedBall 0 1
  have hsymm : ∀ x ∈ B, -x ∈ B := fun x hx => by
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hx
  have hcpt : IsCompact B := isCompact_closedBall 0 1
  have hlam_pos : ∀ i : Fin n, 0 < lam i := fun i => successiveMinimum_pos hcpt.isBounded h0B Λ i
  have hprod_pos : 0 < ∏ i : Fin n, lam i := Finset.prod_pos fun i _ => hlam_pos i
  have hω_pos : 0 < ω := by
    change 0 < (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
    rw [unitBallVolume_eq hn]
    have hG : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  have hcov_eq : covol Λ = ZLattice.covolume Λ volume := covol_eq_zlattice_covolume_euclidean Λ
  have hupper := minkowski_second_theorem_upper hn hconv hsymm hcpt h0B Λ
  have hlower := minkowski_second_theorem_lower hn hconv hsymm hcpt h0B Λ
  have hherm := hermite_minkowski_bound_all_dims hn Λ
  have hlog_prod : Real.log (∏ i : Fin n, lam i) = ∑ i : Fin n, Real.log (lam i) :=
    Real.log_prod fun i _ => (hlam_pos i).ne'
  have h1 : ArakelovCovolume.slope Λ ≤ -(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) +
      Real.log 2 - Real.log ω / (n : ℝ) := by
    have hlog := Real.log_le_log (mul_pos hprod_pos hω_pos) hupper
    rw [Real.log_mul hprod_pos.ne' hω_pos.ne', Real.log_mul (by positivity) hcov_pos.ne',
      Real.log_pow, hlog_prod] at hlog
    unfold ArakelovCovolume.slope degAr
    rw [hrk, hcov_eq]
    have hdiv := div_le_div_of_nonneg_right (show -Real.log (ZLattice.covolume Λ volume) ≤
      -(∑ i : Fin n, Real.log (lam i)) + (n : ℝ) * Real.log 2 - Real.log ω by linarith) hn_pos.le
    have hrhs : (-(∑ i : Fin n, Real.log (lam i)) + (n : ℝ) * Real.log 2 - Real.log ω) / (n : ℝ) =
        -(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) + Real.log 2 - Real.log ω / (n : ℝ) := by
      field_simp [hn_pos.ne']
    linarith
  have h2 : -(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) +
      Real.log 2 - Real.log ω / (n : ℝ) - Real.log (n.factorial : ℝ) / (n : ℝ) ≤
      ArakelovCovolume.slope Λ := by
    have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hlog := Real.log_le_log (mul_pos (div_pos (by positivity) hfac_pos) hcov_pos) hlower
    rw [Real.log_mul (div_pos (by positivity) hfac_pos).ne' hcov_pos.ne',
      Real.log_div (by positivity) hfac_pos.ne', Real.log_pow,
      Real.log_mul hprod_pos.ne' hω_pos.ne', hlog_prod] at hlog
    unfold ArakelovCovolume.slope degAr
    rw [hrk, hcov_eq]
    have hdiv := div_le_div_of_nonneg_right (show -(∑ i : Fin n, Real.log (lam i)) +
      (n : ℝ) * Real.log 2 - Real.log ω - Real.log (n.factorial : ℝ) ≤
      -Real.log (ZLattice.covolume Λ volume) by linarith) hn_pos.le
    have hlhs : (-(∑ i : Fin n, Real.log (lam i)) + (n : ℝ) * Real.log 2 - Real.log ω -
        Real.log (n.factorial : ℝ)) / (n : ℝ) =
        -(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) + Real.log 2 - Real.log ω / (n : ℝ) -
          Real.log (n.factorial : ℝ) / (n : ℝ) := by
      field_simp [hn_pos.ne']
    linarith
  have h3 : ArakelovCovolume.slope Λ ≤ -Real.log (lam ⟨0, hn⟩) + Real.log 2 - Real.log ω / (n : ℝ) := by
    have hlog := Real.log_le_log (sq_pos_of_pos (hlam_pos ⟨0, hn⟩)) hherm
    rw [Real.log_pow, Real.log_mul (div_pos (by norm_num) (Real.rpow_pos_of_pos hω_pos _)).ne'
      (Real.rpow_pos_of_pos hcov_pos _).ne',
      Real.log_div (by norm_num) (Real.rpow_pos_of_pos hω_pos _).ne',
      Real.log_rpow hω_pos, Real.log_rpow hcov_pos,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
    unfold ArakelovCovolume.slope degAr
    rw [hrk, hcov_eq]
    have hsimp : (2 : ℝ) / (n : ℝ) * Real.log (ZLattice.covolume Λ volume) =
        2 * (Real.log (ZLattice.covolume Λ volume) / (n : ℝ)) := by ring
    have hsimpω : (2 : ℝ) / (n : ℝ) * Real.log ω = 2 * (Real.log ω / (n : ℝ)) := by ring
    push_cast at hlog
    rw [hsimp, hsimpω] at hlog
    rw [neg_div]
    linarith
  exact ⟨h1, h2, h3⟩

/-- **Exact `μ_max(L) - μ_min(L)` Successive-Minima Gap Bound (`muMax_sub_muMin_le_of_successiveMinima`)**:
for ANY nonzero discrete Euclidean lattice `L ⊂ E` (`r = rk L > 0`):
`μ_max(L) - μ_min(L) ≤ log (λ_r(L) / λ_1(L)) + (1 / 2) * log r`! -/
theorem muMax_sub_muMin_le_of_successiveMinima
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0
    muMax L - muMin L ≤
      Real.log (succMin L ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ / lambda1 L) +
        (1 / 2) * Real.log (r : ℝ) := by
  intro r hr
  have hup := (RHDirect.Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1 L hL0).2
  have hlo := neg_log_succMin_last_le_muMin L hL0
  have hlam_pos : 0 < lambda1 L := lambda1_pos L hL0
  have hsucc_pos : 0 < succMin L ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ := succMin_pos L hL0 _
  rw [Real.log_div hsucc_pos.ne' hlam_pos.ne']
  linarith

/-- **Minkowski Second Theorem Volume-Only `μ_max - μ_min` Gap Bound
(`muMax_sub_muMin_le_of_minkowski_second_theorem`)**:
directly using `Stage10GeometryOfNumbers.minkowski_second_theorem_upper` (eliminating `λ_n`
entirely in favor of `covol(Λ)` and `λ_1(Λ)`!), for every full-rank lattice
`Λ ⊂ EuclideanSpace ℝ (Fin n)` (`n ≥ 1`):
1. `log (λ_n / λ_1) ≤ n * log 2 - log ω_n - n * (slope Λ + log λ_1) ≤ (n / 2) * log n - n * (slope Λ + log λ_1)`,
2. `μ_max(Λ) - μ_min(Λ) ≤ ((n + 1) / 2) * log n - n * (slope Λ + log λ_1)`! -/
theorem muMax_sub_muMin_le_of_minkowski_second_theorem {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
    let lam : Fin n → ℝ := fun i => successiveMinimum B Λ i
    let ω : ℝ := (volume B).toReal
    Real.log (lam ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ / lam ⟨0, hn⟩) ≤
      (n : ℝ) * Real.log 2 - Real.log ω -
        (n : ℝ) * (ArakelovCovolume.slope Λ + Real.log (lam ⟨0, hn⟩)) ∧
    muMax Λ - muMin Λ ≤
      ((n : ℝ) + 1) / 2 * Real.log (n : ℝ) -
        (n : ℝ) * (ArakelovCovolume.slope Λ + Real.log (lam ⟨0, hn⟩)) := by
  intro B lam ω
  have h0B : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior B := by
    rw [mem_interior_iff_mem_nhds]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hconv : Convex ℝ B := convex_closedBall 0 1
  have hsymm : ∀ x ∈ B, -x ∈ B := fun x hx => by
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hx
  have hcpt : IsCompact B := isCompact_closedBall 0 1
  have hlam_pos : ∀ i : Fin n, 0 < lam i := fun i => successiveMinimum_pos hcpt.isBounded h0B Λ i
  have hlam_mono : ∀ {i j : Fin n}, i ≤ j → lam i ≤ lam j := fun hij =>
    successiveMinimum_mono h0B Λ hij
  have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  have hΛ0 : Λ ≠ ⊥ := by
    intro h0
    have : rk Λ = 0 := by rw [h0]; simp [rk]
    omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsq := (minkowski_second_theorem_slope_squeeze hn Λ).1
  let ilast : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
  -- `∑ i, log (lam i) ≥ (n - 1) * log (lam 0) + log (lam ilast)`!
  have hsum_ge : ((n - 1 : ℕ) : ℝ) * Real.log (lam ⟨0, hn⟩) + Real.log (lam ilast) ≤
      ∑ i : Fin n, Real.log (lam i) := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => Real.log (lam i)) (Finset.mem_univ ilast)]
    have hrest : ((n - 1 : ℕ) : ℝ) * Real.log (lam ⟨0, hn⟩) ≤
        ∑ i ∈ Finset.univ.erase ilast, Real.log (lam i) := by
      calc ((n - 1 : ℕ) : ℝ) * Real.log (lam ⟨0, hn⟩)
          = ∑ _i ∈ Finset.univ.erase ilast, Real.log (lam ⟨0, hn⟩) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.univ.erase ilast, Real.log (lam i) :=
            Finset.sum_le_sum fun i _ =>
              Real.log_le_log (hlam_pos ⟨0, hn⟩) (hlam_mono (Nat.zero_le i.1))
    linarith
  have hmul_sq : (n : ℝ) * ArakelovCovolume.slope Λ ≤
      -(∑ i : Fin n, Real.log (lam i)) + (n : ℝ) * Real.log 2 - Real.log ω := by
    have h := mul_le_mul_of_nonneg_left hsq hn_pos.le
    have hrhs : (n : ℝ) * (-(∑ i : Fin n, Real.log (lam i)) / (n : ℝ) +
        Real.log 2 - Real.log ω / (n : ℝ)) =
        -(∑ i : Fin n, Real.log (lam i)) + (n : ℝ) * Real.log 2 - Real.log ω := by
      field_simp [hn_pos.ne']
    linarith
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hcast_sub] at hsum_ge
  have hratio_le : Real.log (lam ilast / lam ⟨0, hn⟩) ≤
      (n : ℝ) * Real.log 2 - Real.log ω -
        (n : ℝ) * (ArakelovCovolume.slope Λ + Real.log (lam ⟨0, hn⟩)) := by
    rw [Real.log_div (hlam_pos ilast).ne' (hlam_pos ⟨0, hn⟩).ne']
    linarith
  refine ⟨hratio_le, ?_⟩
  have hgap := muMax_sub_muMin_le_of_successiveMinima Λ hΛ0
  dsimp only at hgap
  have hsucc_last : succMin Λ ⟨rk Λ - 1, Nat.sub_lt (rk_pos_of_ne_bot Λ hΛ0) Nat.zero_lt_one⟩ =
      lam ilast := by
    have h := succMin_eq_stage10_successiveMinimum Λ ilast
    convert h using 2
    ext; simp [ilast, hrk]
  have hlam0_eq : lambda1 Λ = lam ⟨0, hn⟩ := by
    rw [← succMin_zero_eq_lambda1 Λ hΛ0]
    have h := succMin_eq_stage10_successiveMinimum Λ ⟨0, hn⟩
    convert h using 2
    ext; simp
  have hcube := (unitBallVolume_ge_cube_bound hn).2
  rw [hsucc_last, hlam0_eq, hrk] at hgap
  linarith

/-- **General Isometric Transfer of Minkowski's Second Theorem (`minkowski_second_theorem_general`)**:
for ANY nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`) in ANY finite-dimensional inner product
space `E`, letting `ω_r = (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal`:
`(2^r / r!) * covol L ≤ (∏ k, succMin L k) * ω_r ≤ 2^r * covol L`! -/
theorem minkowski_second_theorem_general
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let r := rk L
    let ω_r := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal
    ((2 : ℝ) ^ r / (r.factorial : ℝ)) * covol L ≤ (∏ k : Fin r, succMin L k) * ω_r ∧
    (∏ k : Fin r, succMin L k) * ω_r ≤ (2 : ℝ) ^ r * covol L := by
  intro r ω_r
  have hr : 0 < r := rk_pos_of_ne_bot L hL0
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
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp) }
  have : DiscreteTopology Λ :=
    DiscreteTopology.of_continuous_injective (f := eL.symm)
      (Continuous.subtype_mk (continuous_subtype_val.comp (iso.symm.continuous.comp continuous_subtype_val)) _)
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
  have : IsZLattice ℝ Λ := ⟨hspanΛ⟩
  have hcov_eq : covol L = ZLattice.covolume Λ volume := by
    rw [← covol_eq_zlattice_covolume_euclidean Λ]
    let bL := Module.finBasis ℤ L
    rw [covol_eq_sqrt_det_gram L bL, covol_eq_sqrt_det_gram Λ (bL.map eL)]
    congr 2
    ext i j
    simp only [Matrix.gram_apply, Basis.map_apply, eL, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact (iso.inner_map_map ⟨(bL i : E), Submodule.subset_span (bL i).2⟩
      ⟨(bL j : E), Submodule.subset_span (bL j).2⟩).symm
  have hrkΛ : rk Λ = r := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  have hsucc_eq : ∀ k : Fin r,
      succMin L k = successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1) Λ k := by
    intro k
    rw [← succMin_eq_stage10_successiveMinimum Λ k]
    unfold succMin
    congr 1
    ext R
    simp only [Fin.val_cast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hR0, v, hvL, hvli, hvn⟩
      refine ⟨hR0, fun i => iso ⟨v i, Submodule.subset_span (hvL i)⟩,
        fun i => ⟨⟨v i, Submodule.subset_span (hvL i)⟩, hvL i, rfl⟩, ?_,
        fun i => by rw [iso.norm_map]; exact hvn i⟩
      have hvliV : LinearIndependent ℝ (fun i => (⟨v i, Submodule.subset_span (hvL i)⟩ : V)) :=
        LinearIndependent.of_comp V.subtype hvli
      exact hvliV.map' iso.toLinearMap iso.toLinearEquiv.ker
    · rintro ⟨hR0, w, hwΛ, hwli, hwn⟩
      refine ⟨hR0, fun i => (iso.symm (w i) : E), fun i => ?_, ?_, fun i => ?_⟩
      · rcases hwΛ i with ⟨v, hv, hvEq⟩
        have : iso.symm (w i) = v := by rw [← hvEq]; simp
        dsimp only
        rw [this]; exact hv
      · exact (hwli.map' iso.symm.toLinearMap iso.symm.toLinearEquiv.ker).map'
          V.subtype (Submodule.ker_subtype V)
      · change ‖iso.symm (w i)‖ ≤ R
        rw [iso.symm.norm_map]; exact hwn i
  have h0B : (0 : EuclideanSpace ℝ (Fin r)) ∈ interior (Metric.closedBall 0 1) := by
    rw [mem_interior_iff_mem_nhds]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hlo := minkowski_second_theorem_lower hr (convex_closedBall 0 1)
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    (isCompact_closedBall 0 1) h0B Λ
  have hup := minkowski_second_theorem_upper hr (convex_closedBall 0 1)
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    (isCompact_closedBall 0 1) h0B Λ
  simp_rw [hsucc_eq, hcov_eq]
  exact ⟨hlo, hup⟩

end MinkowskiSecondTheoremBridge

/-! ## Section 3: Concrete Dwork `p`-Adic Divisibility Bridge (`dwork_divisibility_mul_m`) -/

section DworkDivisibilityBridge

/-- Exact real-valued additive `p`-adic valuation normalized by `v_p(p) = 1`:
`dworkVal p x = Real.log ‖x‖ / Real.log ‖(p : K)‖`. -/
def dworkVal {K : Type*} [NormedField K] (p : ℕ) (x : K) : ℝ :=
  Real.log ‖x‖ / Real.log ‖(p : K)‖

/-- Exact real-valued additive `p`-adic valuation on any normed space `V` relative to prime `p`
in an ultrametric field `K`: `dworkSpaceVal K p v = Real.log ‖v‖ / Real.log ‖(p : K)‖`. -/
def dworkSpaceVal (K : Type*) [NormedField K] (p : ℕ) {V : Type*} [SeminormedAddCommGroup V]
    (v : V) : ℝ :=
  Real.log ‖v‖ / Real.log ‖(p : K)‖

lemma log_norm_prime_neg {K : Type*} [NormedField K] [CharZero K] {p : ℕ}
    (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) :
    Real.log ‖(p : K)‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)) hlt

theorem dworkVal_prime {K : Type*} [NormedField K] [CharZero K] {p : ℕ}
    (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) :
    dworkVal p (p : K) = 1 :=
  div_self (log_norm_prime_neg hp hlt).ne

/-- **Exact Valuation of the Dwork Uniformizer `ϖ` (`ϖ^(p - 1) = -p`)**:
via `Stage2DworkExp.norm_dworkPi`, `dworkVal p ϖ = 1 / (p - 1)`! -/
theorem dworkVal_dworkPi {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    dworkVal p ϖ = 1 / ((p : ℝ) - 1) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlog_ne : Real.log ‖(p : K)‖ ≠ 0 := (log_norm_prime_neg hp hlt).ne
  unfold dworkVal
  rw [RHDirect.Stage2DworkExp.norm_dworkPi hp hϖ, RHDirect.Stage2DworkExp.expRadius,
    Real.log_rpow hpi0]
  field_simp [hlog_ne]

/-- Exact norm of a product of Dwork uniformizer powers `∏ t : Top, ϖ ^ (a_nat t)`:
`‖∏ t, ϖ ^ (a_nat t)‖ = ‖(p : K)‖ ^ (∑ t, (a_nat t : ℝ) / (p - 1))`! -/
theorem norm_prod_dworkPi_pow {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {Top : Type*} [Fintype Top] {p : ℕ} (hp : p.Prime) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K))
    (a_nat : Top → ℕ) :
    ‖∏ t : Top, ϖ ^ (a_nat t)‖ =
      ‖(p : K)‖ ^ (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1)) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [norm_prod]
  have hterm : ∀ t : Top, ‖ϖ ^ (a_nat t)‖ = ‖(p : K)‖ ^ ((a_nat t : ℝ) / ((p : ℝ) - 1)) := by
    intro t
    rw [norm_pow, RHDirect.Stage2DworkExp.norm_dworkPi hp hϖ, RHDirect.Stage2DworkExp.expRadius,
      ← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le]
    congr 1; ring
  simp_rw [hterm]
  rw [← Real.rpow_sum_of_pos hpi0]

/-- Iterated `m`-step chain operator `K_{m-1} ∘ ⋯ ∘ K_0 : V 0 → V m`. -/
def chainOp {V : ℕ → Type*} (Kstep : ∀ j, V j → V (j + 1)) : ∀ m : ℕ, V 0 → V m
  | 0, v => v
  | m + 1, v => Kstep m (chainOp Kstep m v)

/-- **`m`-Step Dwork Chain Norm Contraction (`chainOp_norm_le_dwork`)**:
if each step `j < m` contracts norms by `‖(p : K)‖ ^ (∑_t a_t / (p - 1) - loss j)`, then the
`m`-step chain `chainOp Kstep m` contracts norms by
`‖(p : K)‖ ^ (m * (∑_t a_t / (p - 1)) - ∑_{j < m} loss j)`! -/
theorem chainOp_norm_le_dwork {K : Type*} [NormedField K] [CharZero K]
    {Top : Type*} [Fintype Top] {p : ℕ} (hp : p.Prime)
    {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)]
    (Kstep : ∀ j, V j → V (j + 1))
    (aT : Top → ℝ) (loss : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ j, j < m → ∀ v : V j,
      ‖Kstep j v‖ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss j) * ‖v‖)
    (v : V 0) :
    ‖chainOp Kstep m v‖ ≤
      ‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) - ∑ j ∈ Finset.range m, loss j) *
        ‖v‖ := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  induction m with
  | zero =>
    simp [chainOp]
  | succ m ih =>
    have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have hcur := hstep m (Nat.lt_succ_self m) (chainOp Kstep m v)
    calc ‖chainOp Kstep (m + 1) v‖
        = ‖Kstep m (chainOp Kstep m v)‖ := rfl
      _ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss m) * ‖chainOp Kstep m v‖ := hcur
      _ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss m) *
            (‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
              ∑ j ∈ Finset.range m, loss j) * ‖v‖) :=
          mul_le_mul_of_nonneg_left hprev (Real.rpow_nonneg hpi0.le _)
      _ = (‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss m) *
            ‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
              ∑ j ∈ Finset.range m, loss j)) * ‖v‖ := by ring
      _ = ‖(p : K)‖ ^ (((m + 1 : ℕ) : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
            ∑ j ∈ Finset.range (m + 1), loss j) * ‖v‖ := by
          rw [← Real.rpow_add hpi0, Finset.sum_range_succ, Nat.cast_succ]
          congr 2; ring

/-- **EXACT `m`-FOLD DWORK `p`-ADIC VALUATION AMPLIFICATION (`dwork_divisibility_mul_m`)**:
for an `m`-step iterated `p`-adic chain operator `chainOp Kstep m` where each step multiplies by
Dwork Frobenius weight `p ^ (-∑_t a_t / (p - 1))` up to per-step Selmer/Vandiver loss
`loss j ≤ stepDefect + ∑'_l PAdicChainValuation.vvTerm S E_field t_val l`:
`m * (∑_t a_t / (p - 1)) - m * (stepDefect + ∑'_l vvTerm S E_field t_val l) ≤ v_p(chainOp m v) - v_p(v)`!
Setting `stepDefect = 0` gives the exact pure Selmer-loss amplification:
`m * (∑_t a_t / (p - 1)) - m * ∑'_l vvTerm S E_field t_val l ≤ v_p(chainOp m v) - v_p(v)`! -/
theorem dwork_divisibility_mul_m {K : Type*} [NormedField K] [CharZero K]
    {Top : Type*} [Fintype Top] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (S : RHDirect.SelmerSystem) (E_field : Type) [Field E_field] [NumberField E_field]
    (t_val : ℕ)
    {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)]
    (Kstep : ∀ j, V j → V (j + 1))
    (aT : Top → ℝ) (loss : ℕ → ℝ) (stepDefect : ℝ) (m : ℕ)
    (hstep : ∀ j, j < m → ∀ v : V j,
      ‖Kstep j v‖ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss j) * ‖v‖)
    (hloss : ∀ j, j < m →
      loss j ≤ stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)
    {v : V 0} (hchain_ne : chainOp Kstep m v ≠ 0) :
    (m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
        (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l) ≤
      dworkSpaceVal K p (chainOp Kstep m v) - dworkSpaceVal K p v := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlog_neg : Real.log ‖(p : K)‖ < 0 := log_norm_prime_neg hp hlt
  have hnorm_chain := chainOp_norm_le_dwork hp Kstep aT loss m hstep v
  have hchain_pos : 0 < ‖chainOp Kstep m v‖ := norm_pos_iff.mpr hchain_ne
  have hv_pos : 0 < ‖v‖ := by
    by_contra hle
    push Not at hle
    have hv0 : ‖v‖ = 0 := le_antisymm hle (norm_nonneg v)
    rw [hv0, mul_zero] at hnorm_chain
    linarith
  have hsum_loss : ∑ j ∈ Finset.range m, loss j ≤
      (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l) := by
    calc ∑ j ∈ Finset.range m, loss j
        ≤ ∑ _j ∈ Finset.range m,
            (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l) :=
          Finset.sum_le_sum fun j hj => hloss j (Finset.mem_range.mp hj)
      _ = (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hrpow_le : ‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
        ∑ j ∈ Finset.range m, loss j) ≤
      ‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
        (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)) :=
    Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by linarith)
  have hle_norm : ‖chainOp Kstep m v‖ ≤
      ‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1)) -
        (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)) * ‖v‖ :=
    hnorm_chain.trans (mul_le_mul_of_nonneg_right hrpow_le hv_pos.le)
  have hlog := Real.log_le_log hchain_pos hle_norm
  rw [Real.log_mul (Real.rpow_pos_of_pos hpi0 _).ne' hv_pos.ne', Real.log_rpow hpi0] at hlog
  -- Dividing by `Real.log ‖(p : K)‖ < 0` flips the inequality!
  unfold dworkSpaceVal
  rw [← sub_div, le_div_iff_of_neg hlog_neg]
  linarith

/-- **Concrete Overconvergent Dwork `U_p` Weighted Frobenius Chain (`dworkOp_chain_overconvNorm_le`)**:
iterating the Dwork splitting operator `f ↦ (∏ t, ϖ ^ a_nat t) • U_p (θ(X) * f)` `m` times on
the overconvergent Banach space `L(R_Dwork(K, p))` (via `Stage3DworkFrobenius.dworkOp` and
`Stage2DworkExp.dworkSplitting`) contracts the overconvergent norm by the EXACT `m`-fold Dwork
Frobenius weight `‖(p : K)‖ ^ (m * ∑ t, a_nat t / (p - 1))`! -/
def dworkWeightedStep {K : Type*} [NormedField K] [CharZero K] {Top : Type*} [Fintype Top]
    (ϖ : K) (p : ℕ) (a_nat : Top → ℕ) : PowerSeries K →ₗ[K] PowerSeries K :=
  (∏ t : Top, ϖ ^ (a_nat t)) •
    RHDirect.Stage3DworkFrobenius.dworkOp p (RHDirect.Stage2DworkExp.dworkSplitting ϖ p)

theorem dworkOp_chain_overconvNorm_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CharZero K] {Top : Type*} [Fintype Top] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) (a_nat : Top → ℕ) (m : ℕ)
    {f : PowerSeries K}
    (hf : RHDirect.Stage3DworkFrobenius.IsOverconvergent
      (RHDirect.Stage2DworkExp.dworkOverconvRadius K p) f) :
    let b := RHDirect.Stage2DworkExp.dworkOverconvRadius K p
    RHDirect.Stage3DworkFrobenius.IsOverconvergent b ((dworkWeightedStep ϖ p a_nat)^[m] f) ∧
    RHDirect.Stage3DworkFrobenius.overconvNorm b ((dworkWeightedStep ϖ p a_nat)^[m] f) ≤
      ‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1))) *
        RHDirect.Stage3DworkFrobenius.overconvNorm b f := by
  intro b
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hb1 : 1 < b := RHDirect.Stage2DworkExp.one_lt_dworkOverconvRadius hp hlt
  have hb0 : 0 ≤ b := (zero_lt_one.trans hb1).le
  have hbp_ge : b ≤ b ^ p := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ p := pow_le_pow_right₀ hb1.le hp.one_le
  have hθ := RHDirect.Stage3DworkFrobenius.dworkSplitting_isOverconvergent hp hlt hϖ
  -- One-step contraction on `L(b)`!
  have hstep1 : ∀ g : PowerSeries K,
      RHDirect.Stage3DworkFrobenius.IsOverconvergent b g →
      RHDirect.Stage3DworkFrobenius.IsOverconvergent b (dworkWeightedStep ϖ p a_nat g) ∧
      RHDirect.Stage3DworkFrobenius.overconvNorm b (dworkWeightedStep ϖ p a_nat g) ≤
        ‖(p : K)‖ ^ (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1)) *
          RHDirect.Stage3DworkFrobenius.overconvNorm b g := by
    intro g hg
    let u := RHDirect.Stage3DworkFrobenius.dworkOp p (RHDirect.Stage2DworkExp.dworkSplitting ϖ p) g
    have hu_bp : RHDirect.Stage3DworkFrobenius.IsOverconvergent (b ^ p) u :=
      RHDirect.Stage3DworkFrobenius.isOverconvergent_dworkUp p
        (RHDirect.Stage3DworkFrobenius.isOverconvergent_mul hb0 hθ.1 hg)
    have hu_norm_bp : RHDirect.Stage3DworkFrobenius.overconvNorm (b ^ p) u ≤
        RHDirect.Stage3DworkFrobenius.overconvNorm b g := by
      have h1 := RHDirect.Stage3DworkFrobenius.overconvNorm_dworkOp_le hb0 p hθ.1 hg
      rwa [hθ.2, one_mul] at h1
    have hu_b_le : ∀ n : ℕ, ‖PowerSeries.coeff n u‖ * b ^ n ≤
        RHDirect.Stage3DworkFrobenius.overconvNorm (b ^ p) u := fun n => by
      calc ‖PowerSeries.coeff n u‖ * b ^ n
          ≤ ‖PowerSeries.coeff n u‖ * (b ^ p) ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbp_ge n) (norm_nonneg _)
        _ ≤ RHDirect.Stage3DworkFrobenius.overconvNorm (b ^ p) u :=
            RHDirect.Stage3DworkFrobenius.norm_coeff_mul_pow_le_overconvNorm hu_bp n
    have hu_b : RHDirect.Stage3DworkFrobenius.IsOverconvergent b u :=
      RHDirect.Stage3DworkFrobenius.isOverconvergent_of_forall hu_b_le
    have hu_norm_b : RHDirect.Stage3DworkFrobenius.overconvNorm b u ≤
        RHDirect.Stage3DworkFrobenius.overconvNorm b g :=
      (RHDirect.Stage3DworkFrobenius.overconvNorm_le_of_forall hu_b_le).trans hu_norm_bp
    change RHDirect.Stage3DworkFrobenius.IsOverconvergent b ((∏ t : Top, ϖ ^ (a_nat t)) • u) ∧
      RHDirect.Stage3DworkFrobenius.overconvNorm b ((∏ t : Top, ϖ ^ (a_nat t)) • u) ≤ _
    refine ⟨RHDirect.Stage3DworkFrobenius.isOverconvergent_smul _ hu_b, ?_⟩
    rw [RHDirect.Stage3DworkFrobenius.overconvNorm_smul _ hu_b, norm_prod_dworkPi_pow hp hϖ a_nat]
    exact mul_le_mul_of_nonneg_left hu_norm_b (Real.rpow_nonneg hpi0.le _)
  induction m with
  | zero =>
    simpa using hf
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := hstep1 _ ih.1
    refine ⟨h1, h2.trans ?_⟩
    calc ‖(p : K)‖ ^ (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1)) *
            RHDirect.Stage3DworkFrobenius.overconvNorm b ((dworkWeightedStep ϖ p a_nat)^[m] f)
        ≤ ‖(p : K)‖ ^ (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1)) *
            (‖(p : K)‖ ^ ((m : ℝ) * (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1))) *
              RHDirect.Stage3DworkFrobenius.overconvNorm b f) :=
          mul_le_mul_of_nonneg_left ih.2 (Real.rpow_nonneg hpi0.le _)
      _ = ‖(p : K)‖ ^ (((m + 1 : ℕ) : ℝ) * (∑ t : Top, (a_nat t : ℝ) / ((p : ℝ) - 1))) *
            RHDirect.Stage3DworkFrobenius.overconvNorm b f := by
          rw [← mul_assoc, ← Real.rpow_add hpi0, Nat.cast_succ]
          congr 2; ring

/-- **Direct Product-Formula Discharge of `Stage3ThetaSiegelFiberWitness.divLink`**:
combining `dwork_divisibility_mul_m` with the archimedean–`p`-adic product-formula balance
`archLHS + (v_p(chainOp m v) - v_p(v)) ≤ m * ∑_t a_t / (p - 1)` directly produces the exact
`divLink` inequality with the `m`-factor breaking the `2/3` barrier! -/
theorem divLink_of_dwork_chain {K : Type*} [NormedField K] [CharZero K]
    {Top : Type*} [Fintype Top] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (S : RHDirect.SelmerSystem) (E_field : Type) [Field E_field] [NumberField E_field]
    (t_val m : ℕ) {archLHS stepDefect : ℝ}
    {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)]
    (Kstep : ∀ j, V j → V (j + 1))
    (aT : Top → ℝ) (loss : ℕ → ℝ)
    (hstep : ∀ j, j < m → ∀ v : V j,
      ‖Kstep j v‖ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT t / ((p : ℝ) - 1)) - loss j) * ‖v‖)
    (hloss : ∀ j, j < m →
      loss j ≤ stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)
    {v : V 0} (hchain_ne : chainOp Kstep m v ≠ 0)
    (hprod : archLHS + (dworkSpaceVal K p (chainOp Kstep m v) - dworkSpaceVal K p v) ≤
      (m : ℝ) * (∑ t : Top, aT t / ((p : ℝ) - 1))) :
    archLHS ≤
      (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l) := by
  have hdw := dwork_divisibility_mul_m hp hlt S E_field t_val Kstep aT loss stepDefect m
    hstep hloss hchain_ne
  linarith

end DworkDivisibilityBridge

/-! ## Section 4: Strictly Smaller `Stage11ThetaFiberWitness` & `Stage11ThetaCoreInputs S` Compiler -/

section Stage11FiberCompiler

/-- Concrete Minkowski successive-minima ceiling `HH` for a common-fiber lattice `L ⊂ ECC`
and weighted morphism-height offset `wmean d (fun u => cCC u - h u)`:
automatically positive (`≥ 1`) and automatically `≥ wmean d (slope (latN u) - h u) - muMin L`! -/
def hhMinkowski {ECC : Type*} [NormedAddCommGroup ECC] [InnerProductSpace ℝ ECC]
    [FiniteDimensional ℝ ECC]
    (L : Submodule ℤ ECC) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {W : Type*} [Fintype W] (d cCC h : W → ℝ) : ℝ :=
  max 1
    (Real.log (succMin L ⟨rk L - 1, Nat.sub_lt (rk_pos_of_ne_bot L hL0) Nat.zero_lt_one⟩ /
        lambda1 L) +
      (1 / 2) * Real.log (rk L : ℝ) +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u))

/-- Automatic discharge of all three `hhBound` inequalities from `hhMinkowski`,
`bost_slope_inequality`, and `muMax_sub_muMin_le_of_successiveMinima`! -/
theorem hhBound_of_minkowski_gap
    {EN ECC : Type*} [NormedAddCommGroup EN] [InnerProductSpace ℝ EN] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup ECC] [InnerProductSpace ℝ ECC] [FiniteDimensional ℝ ECC]
    {W : Type*} [Fintype W] [Nonempty W]
    (latN : W → Submodule ℤ EN) [∀ u, DiscreteTopology (latN u)] (hN0 : ∀ u, latN u ≠ ⊥)
    (latCC : Submodule ℤ ECC) [DiscreteTopology latCC] (hCC0 : latCC ≠ ⊥)
    (ιCC : ∀ u : W, latN u →ₗ[ℤ] latCC) (hι_inj : ∀ u, Function.Injective (ιCC u))
    (cCC d h : W → ℝ) (hd : ∀ u, 0 < d u)
    (hι_norm : ∀ u (x : latN u), ‖((ιCC u x : latCC) : ECC)‖ ≤ Real.exp (cCC u) * ‖(x : EN)‖)
    {x cHH eps : ℝ} (hx1 : 1 < x) (hcHH : 0 ≤ cHH) (_heps : 0 < eps)
    (hgap_le : Real.log (succMin latCC
        ⟨rk latCC - 1, Nat.sub_lt (rk_pos_of_ne_bot latCC hCC0) Nat.zero_lt_one⟩ / lambda1 latCC) +
      (1 / 2) * Real.log (rk latCC : ℝ) +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) ≤ x ^ cHH * Real.exp (x ^ eps)) :
    let HH := hhMinkowski latCC hCC0 d cCC h
    RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) -
        muMin latCC ≤ HH ∧
    0 < HH ∧
    HH ≤ x ^ cHH * Real.exp (x ^ eps) := by
  intro HH
  have h1 : RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) -
      muMin latCC ≤ HH := by
    have hpt : ∀ u : W, ArakelovCovolume.slope (latN u) - h u ≤
        muMax latCC + (cCC u - h u) := fun u => by
      have hb := bost_slope_inequality (latN u) latCC (hN0 u) (ιCC u) (Real.exp (cCC u))
        (hι_inj u) (hι_norm u)
      rw [Real.log_exp] at hb
      linarith
    have hsum_pos : 0 < ∑ u : W, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
    have hwmean_le : RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) ≤
        muMax latCC + RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) := by
      unfold RHDirect.SlopeInequality.wmean
      rw [← mul_div_cancel_left₀ (muMax latCC) hsum_pos.ne', mul_comm (∑ u : W, d u),
        ← add_div, div_le_div_iff_of_pos_right hsum_pos, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun u _ => ?_
      have hu := mul_le_mul_of_nonneg_left (hpt u) (hd u).le
      linarith
    have hgap := muMax_sub_muMin_le_of_successiveMinima latCC hCC0
    exact (show _ ≤ Real.log _ + (1 / 2) * Real.log _ +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) by linarith).trans (le_max_right 1 _)
  have h2 : 0 < HH := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have h3 : HH ≤ x ^ cHH * Real.exp (x ^ eps) := by
    refine max_le ?_ hgap_le
    have hx_ge : 1 ≤ x ^ cHH := Real.one_le_rpow hx1.le hcHH
    have hexp_ge : 1 ≤ Real.exp (x ^ eps) :=
      Real.one_le_exp (Real.rpow_nonneg (zero_lt_one.trans hx1).le eps)
    exact one_le_mul_of_one_le_of_one_le hx_ge hexp_ge
  exact ⟨h1, h2, h3⟩

/-- **Stage 11 Strictly Reduced Fiber Witness (`Stage11ThetaFiberWitness`)**:
strictly shrinks `Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness` by **discharging BOTH
`quotientSlopes` AND `hhBound`** (and eliminating abstract `muMinCC` and `HH`!):
- **`quotientSlopes`** is discharged from a concrete injective full-rank bounded lattice morphism
  `φ : latN u0 u →ₗ[ℤ] latM u0 u` via `muMax_le_of_bounded_injection` and `slope_ge_of_index_and_norm`.
- **`hhBound`** (all 3 inequalities!) is discharged from a concrete common-fiber lattice `latCC u0`
  (`muMinCC u0 := Stage4ArakelovBost.muMin (latCC u0)`) + bounded injective embeddings
  `ιCC u0 u : latN u0 u →ₗ[ℤ] latCC u0` + Minkowski successive-minima gap via
  `hhBound_of_minkowski_gap` and `muMax_sub_muMin_le_of_successiveMinima`! -/
structure Stage11ThetaFiberWitness (S : RHDirect.SelmerSystem) (ψ : RHDirect.PChar)
    (eL K cHH eps x : ℝ) (q d_aux e_page : ℕ)
    (hx1 : 1 < x) (hcHH : 0 ≤ cHH) (heps : 0 < eps) (heps52 : eps < 1 / 52) : Type 1 where
  -- Fiber index spaces & RankVal-constrained unitary chain ranks
  U0 : Type
  [finU0 : Fintype U0]
  [neU0 : Nonempty U0]
  W : U0 → Type
  [finW : ∀ u0, Fintype (W u0)]
  [neW : ∀ u0, Nonempty (W u0)]
  Top : Type
  [finTop : Fintype Top]
  R : RHDirect.ChainRanks
  f_eq : R.f = 2 * R.n
  m_ge_two : 2 ≤ R.m
  mk_le : R.m + 3 ≤ R.k
  r_eq : R.r = R.k + R.m - 1
  rankVal : RHDirect.RankVal (RHDirect.Stage2ThetaWire.stage2ScaleParams x eps hx1 heps heps52) R
  nT2 : ℕ
  nT2_le : nT2 ≤ R.n
  nT_ge_one : 1 ≤ (Fintype.card Top : ℝ)
  nT_ge_rest : x ^ (-(eps / 8)) * (R.n : ℝ) / 2 ≤ (Fintype.card Top : ℝ)
  nT2_ge_rest : x ^ (-eps) ≤ (nT2 : ℝ) / (R.n : ℝ)
  -- Concrete Euclidean inner product spaces & discrete Arakelov lattices `latN`, `latM`, `latCC`
  EN : Type
  [normEN : NormedAddCommGroup EN]
  [innerEN : InnerProductSpace ℝ EN]
  [fdEN : FiniteDimensional ℝ EN]
  EM : Type
  [normEM : NormedAddCommGroup EM]
  [innerEM : InnerProductSpace ℝ EM]
  [fdEM : FiniteDimensional ℝ EM]
  ECC : Type
  [normECC : NormedAddCommGroup ECC]
  [innerECC : InnerProductSpace ℝ ECC]
  [fdECC : FiniteDimensional ℝ ECC]
  latN : ∀ u0, W u0 → Submodule ℤ EN
  [discN : ∀ u0 u, DiscreteTopology (latN u0 u)]
  latN_ne_bot : ∀ u0 u, latN u0 u ≠ ⊥
  latM : ∀ u0, W u0 → Submodule ℤ EM
  [discM : ∀ u0 u, DiscreteTopology (latM u0 u)]
  latM_ne_bot : ∀ u0 u, latM u0 u ≠ ⊥
  latCC : U0 → Submodule ℤ ECC
  [discCC : ∀ u0, DiscreteTopology (latCC u0)]
  latCC_ne_bot : ∀ u0, latCC u0 ≠ ⊥
  -- Siegel-reduced basis on `latM`
  C_diag : ℝ
  C_unip : ℝ
  bM : ∀ u0 (u : W u0), Basis (Fin (rk (latM u0 u))) ℤ (latM u0 u)
  bM_siegel : ∀ u0 u, RHDirect.Stage2SiegelReduction.IsSiegelReduced (bM u0 u) C_diag C_unip
  -- Concrete bounded finite-index morphism `φ : latN → latM` (DISCHARGES `quotientSlopes`!)
  φ : ∀ u0 (u : W u0), latN u0 u →ₗ[ℤ] latM u0 u
  φ_inj : ∀ u0 u, Function.Injective (φ u0 u)
  φ_rk_eq : ∀ u0 u, rk (latN u0 u) = rk (latM u0 u)
  C_up : ∀ u0, W u0 → ℝ
  C_lo : ∀ u0, W u0 → ℝ
  φ_norm_up : ∀ u0 (u : W u0) (v : latN u0 u), ‖((φ u0 u v : latM u0 u) : EM)‖ ≤ C_up u0 u * ‖(v : EN)‖
  φ_norm_lo : ∀ u0 (u : W u0) (v : latN u0 u), ‖(v : EN)‖ ≤ C_lo u0 u * ‖((φ u0 u v : latM u0 u) : EM)‖
  -- Concrete bounded embeddings `ιCC : latN → latCC` (DISCHARGES `hhBound`!)
  ιCC : ∀ u0 (u : W u0), latN u0 u →ₗ[ℤ] latCC u0
  ιCC_inj : ∀ u0 u, Function.Injective (ιCC u0 u)
  cCC : ∀ u0, W u0 → ℝ
  ιCC_norm : ∀ u0 (u : W u0) (v : latN u0 u),
    ‖((ιCC u0 u v : latCC u0) : ECC)‖ ≤ Real.exp (cCC u0 u) * ‖(v : EN)‖
  -- Analytic slope-system scalars & constants
  a : ℝ
  b' : ℝ
  La : ℝ
  gam : ℝ
  LpL : ℝ
  Xpp : ℝ
  vE : ℝ
  g₁ : ℝ
  g₂ : ℝ
  cDiv : ℝ
  cE : ℝ
  cH : ℝ
  cCount : ℝ
  cSlope : ℝ
  cSl1 : ℝ
  cLoss : ℝ
  -- Siegel-reduced geometric norm bounds on `bM`
  bM_prod_norm_le : ∀ u0 (u : W u0),
    Real.log (∏ j : Fin (rk (latM u0 u)), ‖(bM u0 u j : EM)‖) / (rk (latM u0 u) : ℝ) ≤
      cSlope * (Fintype.card Top : ℝ) * a * La * (1 + (R.m : ℝ) / (R.k : ℝ))
  bM_first_vec_ge : ∀ u0 (u : W u0),
    (1 / 2) * Real.log (rk (latM u0 u) : ℝ) +
      ((rk (latM u0 u) - 1 : ℕ) : ℝ) * Real.log C_diag -
      Real.log ‖(bM u0 u ⟨0, rk_pos_of_ne_bot _ (latM_ne_bot u0 u)⟩ : EM)‖ ≤
      cSlope * (Fintype.card Top : ℝ) * a * La
  -- Fiber functions (`muMinCC` and `HH` ELIMINATED — computed from `latCC`!)
  aT : Top → ℝ
  w : U0 → Fin R.m → Fin R.f → ℝ
  d : ∀ u0, W u0 → ℝ
  T : ∀ u0, W u0 → ℝ
  h : ∀ u0, W u0 → ℝ
  Ee : ∀ u0, W u0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  -- Concrete morphism norm & cokernel index bounds (replace abstract `quotientSlopes`!)
  φ_log_up_le : ∀ u0 (u : W u0),
    Real.log (C_up u0 u) ≤
      Ga u0 + Fo u0 - Ee u0 u +
        cSl1 * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps)
  φ_log_lo_index_le : ∀ u0 (u : W u0),
    Real.log (C_lo u0 u) +
      Real.log (latIndex (latM u0 u) (LinearMap.range ((latM u0 u).subtype.comp (φ u0 u))) : ℝ) /
        (rk (latM u0 u) : ℝ) ≤
      -(Ga u0 + Fo u0 - Ee u0 u) +
        (cSl1 * IO u0 + cSl1 * (Fintype.card Top : ℝ) * (R.m : ℝ) * (a / (R.k : ℝ) + b') *
          Real.log (T u0 u) + cSl1 * Xpp + 1)
  -- Concrete Minkowski successive-minima gap bound on `latCC` (replaces abstract `hhBound`!)
  hh_minkowski_gap_le : ∀ u0,
    Real.log (succMin (latCC u0)
        ⟨rk (latCC u0) - 1, Nat.sub_lt (rk_pos_of_ne_bot _ (latCC_ne_bot u0)) Nat.zero_lt_one⟩ /
        lambda1 (latCC u0)) +
      (1 / 2) * Real.log (rk (latCC u0) : ℝ) +
      RHDirect.SlopeInequality.wmean (d u0) (fun u => cCC u0 u - h u0 u) ≤
      x ^ cHH * Real.exp (x ^ eps)
  -- Gram-frame fiber realization (using computed `hhMinkowski` and `muMin (latCC u0)`!)
  delBar : ℝ
  sgBar : ℝ
  deBar : ℝ
  e0Bar : ℝ
  delBar_le : delBar ≤ 1 / 2
  sgBar_le : sgBar ≤ 1 / 20
  deBar_le : deBar ≤ 1 / 4
  e0Bar_nonneg : 0 ≤ e0Bar
  sqrt_e0Bar_le : Real.sqrt e0Bar ≤ sgBar / 2
  gramFiber : ∀ u0,
    RHDirect.Stage2ThetaWire.Stage2GramFrameFiber
      (RHDirect.SlopeInequality.wmean (d u0)
        (fun u => ArakelovCovolume.slope (latN u0 u) - h u0 u))
      ((Finset.univ.sup' Finset.univ_nonempty
          (fun u : W u0 => muMax (latN u0 u) - h u0 u)) -
        RHDirect.SlopeInequality.wmean (d u0)
          (fun u => ArakelovCovolume.slope (latN u0 u) - h u0 u))
      (hhMinkowski (latCC u0) (latCC_ne_bot u0) (d u0) (cCC u0) (h u0))
      (muMin (latCC u0)) (Fintype.card (W u0)) delBar sgBar deBar e0Bar
  trace_le :
    (5 * sgBar + 3 * Real.sqrt deBar + 4 * Real.sqrt (2 * e0Bar)) *
        (x ^ cHH * Real.exp (x ^ eps))
      ≤ K * x ^ eps * ((Fintype.card Top : ℝ) * a)
  -- Host CM field & Selmer LinkN bound
  E_field : Type
  [fieldE : Field E_field]
  [nfE : NumberField E_field]
  isChi : RHDirect.IsChiField ψ e_page q d_aux E_field
  cLink : ℝ
  cDiv_ge_link : |cLink| + 1 ≤ cDiv
  Nc : ℝ
  Nc_nonneg : 0 ≤ Nc
  Nc_le : Nc ≤ (nT2 : ℝ) * (R.k : ℝ) * Real.exp (x ^ eps) * x ^ eps /
    ((R.n : ℝ) * ((R.n : ℝ) * x ^ (-eps)))
  divLink : ∀ u0 (u : W u0),
    ((gramFiber u0).muCC + h u0 u - Fo u0) -
      (∑ t : Top, ((R.m : ℝ) * (RHDirect.SlopeInequality.ph (aT t) -
          aT t * (gam + Real.log (Real.pi / vE) - LpL)) - aT t * Real.log (T u0 u))) -
      cDiv * (Fintype.card Top : ℝ) * a * La ≤
    (R.m : ℝ) * (cLink * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
      Real.log x ^ 2 * Nc) + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field R.t l)
  -- Unitary mass formula datum
  vE_ge_pi : Real.pi ≤ vE
  log_vE_le : Real.log vE ≤ x ^ eps
  g₁_ge_one : 1 ≤ g₁
  g₂_ge_one : 1 ≤ g₂
  four_le_cCount_La : 4 ≤ cCount * La
  massDatum : ∀ u0 (u : W u0),
    RHDirect.Stage2ThetaWire.Stage2MassRatioDatum R.f R.m R.k vE g₁ g₂ (x ^ eps) La cCount (w u0) (T u0 u)
  -- Remaining irreducible analytic inequalities
  xb_le_a : x * Real.exp (x ^ eps) ≤ a
  a_le_2xb : a ≤ 2 * x * Real.exp (x ^ eps)
  k_le_a : (R.k : ℝ) ≤ a
  b'_nonneg : 0 ≤ b'
  kb'_le_a : (R.k : ℝ) * b' ≤ a
  La_nonneg : 0 ≤ La
  La_le : La ≤ 2 * x ^ eps
  Xpp_nonneg : 0 ≤ Xpp
  Xpp_le_a : Xpp ≤ a
  aT_bounds : ∀ t, 0 ≤ aT t ∧ aT t ≤ 2 * a
  w_pos : ∀ u0 j ρ, 0 < w u0 j ρ
  d_pos : ∀ u0 u, 0 < d u0 u
  cardW_le : ∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ ((R.k : ℝ) - 3) * Real.log 2
  cDiv_le : cDiv ≤ K
  cE_bounds : 0 ≤ cE ∧ cE ≤ K
  cH_bounds : 0 ≤ cH ∧ cH ≤ K
  cCount_bounds : 0 ≤ cCount ∧ cCount ≤ K
  cSlope_bounds : 0 ≤ cSlope ∧ cSlope ≤ K
  cSl1_bounds : 0 ≤ cSl1 ∧ cSl1 ≤ K
  cLoss_bounds : 0 ≤ cLoss ∧ cLoss ≤ K
  eComp : ∀ u0 (u : W u0),
    |Ee u0 u - (R.m : ℝ) * (∑ t, aT t) * (Real.log g₁ + Real.log g₂)| ≤
      cE * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps)
  hComp : ∀ u0 (u u' : W u0),
    |(h u0 u + ∑ t, aT t * Real.log (T u0 u)) -
      (h u0 u' + ∑ t, aT t * Real.log (T u0 u'))| ≤
    cH * ((Fintype.card Top : ℝ) * a * La +
      (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps))
  count_upper_and_var : ∀ u0 (u : W u0),
    Real.log (T u0 u) ≤ cCount * (R.m : ℝ) * x ^ eps ∧
    ∀ u' : W u0, |Real.log (T u0 u) - Real.log (T u0 u')| ≤ cCount * Real.log (R.k : ℝ)
  losses :
    RHDirect.SlopeInequality.umean (fun u0 => ASK u0 - Ga u0) ≤
      cLoss * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ (eL * eps) ∧
    RHDirect.SlopeInequality.umean IO ≤
      cLoss * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ (eL * eps)
  mainBalance :
    (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (((nT2 : ℝ) / (R.n : ℝ)) / 2) *
        ((RHDirect.Level.cyc ψ).Gm x - 4 * x ^ ((1 : ℝ) / 2 + eps)) ≤
      (RHDirect.SlopeInequality.umean ASK - RHDirect.SlopeInequality.umean (fun u0 =>
        ∑ j : Fin R.m, ∑ t, aT t * (Real.log (aT t) - 1 - gam + LpL
          - (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w u0 j ρ)))) +
      2 * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) / x

attribute [instance] Stage11ThetaFiberWitness.finU0 Stage11ThetaFiberWitness.neU0
  Stage11ThetaFiberWitness.finW Stage11ThetaFiberWitness.neW
  Stage11ThetaFiberWitness.finTop Stage11ThetaFiberWitness.normEN
  Stage11ThetaFiberWitness.innerEN Stage11ThetaFiberWitness.fdEN
  Stage11ThetaFiberWitness.normEM Stage11ThetaFiberWitness.innerEM
  Stage11ThetaFiberWitness.fdEM Stage11ThetaFiberWitness.normECC
  Stage11ThetaFiberWitness.innerECC Stage11ThetaFiberWitness.fdECC
  Stage11ThetaFiberWitness.discN Stage11ThetaFiberWitness.discM
  Stage11ThetaFiberWitness.discCC Stage11ThetaFiberWitness.fieldE
  Stage11ThetaFiberWitness.nfE

/-- **Direct Compilation `Stage11ThetaFiberWitness → Stage3ThetaSiegelFiberWitness`**:
discharges `quotientSlopes` via `muMax_le_of_bounded_injection` and `slope_ge_of_index_and_norm`,
and discharges `hhBound` via `hhBound_of_minkowski_gap` (`bost_slope_inequality` +
`muMax_sub_muMin_le_of_successiveMinima`)! -/
def Stage11ThetaFiberWitness.toStage3ThetaSiegelFiberWitness
    {S : RHDirect.SelmerSystem} {ψ : RHDirect.PChar} {eL K cHH eps x : ℝ}
    {q d_aux e_page : ℕ} {hx1 : 1 < x} {hcHH : 0 ≤ cHH} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (W : Stage11ThetaFiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 hcHH heps heps52) :
    RHDirect.Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness
      S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52 where
  U0 := W.U0
  W := W.W
  Top := W.Top
  R := W.R
  f_eq := W.f_eq
  m_ge_two := W.m_ge_two
  mk_le := W.mk_le
  r_eq := W.r_eq
  rankVal := W.rankVal
  nT2 := W.nT2
  nT2_le := W.nT2_le
  nT_ge_one := W.nT_ge_one
  nT_ge_rest := W.nT_ge_rest
  nT2_ge_rest := W.nT2_ge_rest
  EN := W.EN
  EM := W.EM
  latN := W.latN
  latN_ne_bot := W.latN_ne_bot
  latM := W.latM
  latM_ne_bot := W.latM_ne_bot
  C_diag := W.C_diag
  C_unip := W.C_unip
  bM := W.bM
  bM_siegel := W.bM_siegel
  a := W.a
  b' := W.b'
  La := W.La
  gam := W.gam
  LpL := W.LpL
  Xpp := W.Xpp
  vE := W.vE
  g₁ := W.g₁
  g₂ := W.g₂
  cDiv := W.cDiv
  cE := W.cE
  cH := W.cH
  cCount := W.cCount
  cSlope := W.cSlope
  cSl1 := W.cSl1
  cLoss := W.cLoss
  bM_prod_norm_le := W.bM_prod_norm_le
  bM_first_vec_ge := W.bM_first_vec_ge
  aT := W.aT
  w := W.w
  d := W.d
  T := W.T
  h := W.h
  Ee := W.Ee
  muMinCC := fun u0 => muMin (W.latCC u0)
  Fo := W.Fo
  Ga := W.Ga
  ASK := W.ASK
  IO := W.IO
  HH := fun u0 => hhMinkowski (W.latCC u0) (W.latCC_ne_bot u0) (W.d u0) (W.cCC u0) (W.h u0)
  delBar := W.delBar
  sgBar := W.sgBar
  deBar := W.deBar
  e0Bar := W.e0Bar
  delBar_le := W.delBar_le
  sgBar_le := W.sgBar_le
  deBar_le := W.deBar_le
  e0Bar_nonneg := W.e0Bar_nonneg
  sqrt_e0Bar_le := W.sqrt_e0Bar_le
  gramFiber := W.gramFiber
  trace_le := W.trace_le
  E_field := W.E_field
  isChi := W.isChi
  cLink := W.cLink
  cDiv_ge_link := W.cDiv_ge_link
  Nc := W.Nc
  Nc_nonneg := W.Nc_nonneg
  Nc_le := W.Nc_le
  divLink := W.divLink
  vE_ge_pi := W.vE_ge_pi
  log_vE_le := W.log_vE_le
  g₁_ge_one := W.g₁_ge_one
  g₂_ge_one := W.g₂_ge_one
  four_le_cCount_La := W.four_le_cCount_La
  massDatum := W.massDatum
  xb_le_a := W.xb_le_a
  a_le_2xb := W.a_le_2xb
  k_le_a := W.k_le_a
  b'_nonneg := W.b'_nonneg
  kb'_le_a := W.kb'_le_a
  La_nonneg := W.La_nonneg
  La_le := W.La_le
  Xpp_nonneg := W.Xpp_nonneg
  Xpp_le_a := W.Xpp_le_a
  aT_bounds := W.aT_bounds
  w_pos := W.w_pos
  d_pos := W.d_pos
  cardW_le := W.cardW_le
  cDiv_le := W.cDiv_le
  cE_bounds := W.cE_bounds
  cH_bounds := W.cH_bounds
  cCount_bounds := W.cCount_bounds
  cSlope_bounds := W.cSlope_bounds
  cSl1_bounds := W.cSl1_bounds
  cLoss_bounds := W.cLoss_bounds
  eComp := W.eComp
  hComp := W.hComp
  count_upper_and_var := W.count_upper_and_var
  quotientSlopes := fun u0 u => by
    have hmu := muMax_le_of_bounded_injection (W.latN u0 u) (W.latM u0 u) (W.latN_ne_bot u0 u)
      (W.φ u0 u) (W.C_up u0 u) (W.φ_inj u0 u) (W.φ_norm_up u0 u)
    have hsl := (slope_ge_of_index_and_norm (W.latN u0 u) (W.latM u0 u) (W.latN_ne_bot u0 u)
      (W.φ u0 u) (W.C_lo u0 u) (W.φ_inj u0 u) (W.φ_rk_eq u0 u) (W.φ_norm_lo u0 u)).2
    have hup := W.φ_log_up_le u0 u
    have hlo := W.φ_log_lo_index_le u0 u
    exact ⟨by linarith, by linarith⟩
  losses := W.losses
  hhBound := fun u0 =>
    hhBound_of_minkowski_gap (W.latN u0) (W.latN_ne_bot u0) (W.latCC u0) (W.latCC_ne_bot u0)
      (W.ιCC u0) (W.ιCC_inj u0) (W.cCC u0) (W.d u0) (W.h u0) (W.d_pos u0) (W.ιCC_norm u0)
      hx1 hcHH heps (W.hh_minkowski_gap_le u0)
  mainBalance := W.mainBalance

/-- **Stage 11 Strictly Smaller Pillar-2 Core Input Bundle (`Stage11ThetaCoreInputs S`)**:
strictly reduces `Stage3ThetaSiegelBridge.Stage3ThetaSiegelCoreInputs S` by discharging
`quotientSlopes` and `hhBound` directly via Arakelov–Bost–Minkowski morphism/index/successive-minima
bounds! -/
structure Stage11ThetaCoreInputs (S : RHDirect.SelmerSystem) where
  eL : ℝ
  eL_nonneg : 0 ≤ eL
  pairEx : RHDirect.ThetaSlopeEngine.PairEx
  realizeStage11 : ∀ (ψ : RHDirect.PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52),
    1 ≤ J →
    ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ ∃ (hcHH : 0 ≤ cHH),
      ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
        RHDirect.ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
        Nonempty (Stage11ThetaFiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 hcHH heps heps52)

/-- **Stage 11 → Stage 3 Core Compilation (`stage3ThetaCoreInputs_of_stage11`)**. -/
def stage3ThetaCoreInputs_of_stage11 (S : RHDirect.SelmerSystem)
    (I : Stage11ThetaCoreInputs S) :
    RHDirect.Stage3ThetaSiegelBridge.Stage3ThetaSiegelCoreInputs S where
  eL := I.eL
  eL_nonneg := I.eL_nonneg
  pairEx := I.pairEx
  realizeStage3 := fun ψ eps J heps heps52 hJ => by
    obtain ⟨K, cHH, X0, hK0, hcHH, hCore⟩ := I.realizeStage11 ψ eps J heps heps52 hJ
    exact ⟨K, cHH, X0, hK0, hcHH, fun x Y q d_aux e_page hx1 hx hDat =>
      let ⟨W⟩ := hCore x Y q d_aux e_page hx1 hx hDat
      ⟨W.toStage3ThetaSiegelFiberWitness⟩⟩

/-- **Stage 11 Pillar-2 Master Contract Theorem (`stage11_thetaSlopeContract`)**:
compiles `Stage11ThetaCoreInputs S` directly into `RHDirect.ThetaSlopeContract S`! -/
theorem stage11_thetaSlopeContract (S : RHDirect.SelmerSystem)
    (I : Stage11ThetaCoreInputs S) :
    RHDirect.ThetaSlopeContract S :=
  RHDirect.Stage3ThetaSiegelBridge.stage3_thetaSlopeContract S
    (stage3ThetaCoreInputs_of_stage11 S I)

/-- **Stage 11 Direct Windowed Cesàro von Mangoldt Bound (`stage11_allLevelsWindowBound`)**:
`Stage11ThetaCoreInputs S → VWin S → AllLevelsWindowBound (3 / 2)`! -/
theorem stage11_allLevelsWindowBound (S : RHDirect.SelmerSystem)
    (I : Stage11ThetaCoreInputs S) (hV : RHDirect.VWin S) :
    RHDirect.AllLevelsWindowBound (3 / 2) :=
  (stage11_thetaSlopeContract S I).windows_of_vwin hV

end Stage11FiberCompiler

end

end RHDirect.Stage11BostDworkSqueeze
