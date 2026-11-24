import RHDirect.Stage14Contracts
import RHDirect.Stage14M2_HLatNumberField
import RHDirect.Stage14M2_BesselSchurBlock
import RHDirect.CapelliCore
import RHDirect.PAdicChainValuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# RHDirect.Stage14M2_BesselIntegrality

Field-2 Package M2 (Wave 2): **Concrete Target Dual Hermitian Lattice `RR^∨`, Iterated
Bessel/Theta Morphism `Bk` (`OneMapIntoCC`), Proved Congruence-Sublattice Integrality
(`bessel_map_maps_Nu_into_RRDual`), Unitary Block Factorization (`bessel_id_unitary_factorization`),
and Capelli Determinant Integrality (`capelli_determinant_integrality_on_RR`)** in pure Mathlib
`v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.

## Main Exports (Aligned with `Stage14Contracts` & Ready for `Stage14M2_FrameRealCompile`)

1. **`TargetDualHLatRR` (`RR^∨`) & `Stage14Contracts.HLatAnchor` Alignment (Section 1)**:
   - `toHLatAnchor`, `TargetDualHLatRR`, `TargetDualHLatRR.dual` (`dualHLat T.RR`),
     `TargetDualHLatRR.dualAnchor`, exact duality slope identities via
     `Stage14M2_HLatNumberField.hlat_duality_slope_neg`, `ZLattice.covolume` grounding,
     ideal-twist compatibility (`twistBase` / `twistDual`), and concrete 0-assumption
     canonical realization `TargetDualHLatRR.std`.
2. **Dedekind Local-to-Global Integrality & Congruence Sublattices `Nu` (Section 2)**:
   - `mem_ringOfIntegers_of_forall_valuation_le_one`,
     `mem_ringOfIntegers_of_denom_and_local_le_one`,
     `mem_ringOfIntegers_of_ideal_clearing_and_local_le_one`,
     `valuation_le_one_of_chain_quot` (connecting `PAdicChainValuation.ChainValuationSystem`
     to `HeightOneSpectrum (𝓞 K)` valuations), and concrete `CongruenceSublatticeNu` (`Nu u`,
     including `ofIdealTwist` via `twist_index` and `ofIdealAndSublattice`).
3. **`IteratedBesselMapBk` & `OneMapIntoCC` (Section 3)**:
   - Concrete iterated Bessel/theta linear map `Bk u : (Nu u).M.V →ₗ[K] Module.Dual K T.RR.V`
     with denominator-clearing / chain-valuation data, operator norm bounds `C_op u`,
     `ofChainValuationSystem` builder from `PAdicChainValuation.ChainValuationSystem`,
     concrete diagonal Bessel realization `ofIntegralBasisPairing`, and unified `OneMapIntoCC`
     (`oneMap` on `∀ u, (Nu u).M.V`).
4. **`bessel_map_maps_Nu_into_RRDual` & Ramified Bost Slope Bounds (Section 4)**:
   - `bessel_pairing_mem_ringOfIntegers`, **`bessel_map_maps_Nu_into_RRDual`** (both
     `Nu.map Bk ≤ dualLatO RR.L` and the `bridge_ccb_dual` `𝓞 K`-bilinear pairing),
     `oneMapIntoCC_maps_into_RRDual`, clean `LinearEquiv`-based `besselMapToAnchorHom`,
     and ramified Bost slope bounds (`bessel_map_ramified_bost_ineq`,
     `bessel_map_ramified_bost_ineq_normalized`, `bessel_map_rank_bound_of_divisible`,
     `bessel_map_vanishing_of_strict_divisible`) aligned with
     `Stage14Contracts.M2HLatBostContract.joint_a_ramified_holds`.
5. **`bessel_id_unitary_factorization` & `Stage2GramFrameFiber` Alignment (Section 5)**:
   - Concrete Bessel period matrix `besselPeriodMatrix`, **`bessel_id_unitary_factorization`**
     producing `Stage14M2_BesselSchurBlock.IsometryBlockFactorization`, Loewner domination &
     Hilbert–Schmidt contractions, top-block kernel projection (`bessel_factorization_top_block_kernel_proj`),
     and `bessel_integrality_to_stage2GramFrameFiber` discharging `BostSlopeFiber.SlopeIneq`.
6. **`capelli_determinant_integrality_on_RR` (Section 6)**:
   - Dual stabilization `dualOp_preserves_dualLatO`, `isIntegral_det_of_preserves_RR`,
     `capelli_isIntegral_det_of_integral_matrix`, `capelli_bilin_pres_det_sq_one_on_RR`,
     Capelli trace/Casimir/quantum-determinant integrality (`capelli_qdet_two_integral_on_RR`),
     Iwahori Newton-polygon valuations, archimedean determinant norm bounds, and
     **`capelli_determinant_integrality_on_RR`**.
7. **Wave 2 `FrameRealCompile` Handoff Pack (Section 7)**:
   - `BesselIntegralityCompilePack`, `bessel_integrality_for_frame_real_compile`, and
     `M2BesselIntegralityBridge` aligned with `Stage14Contracts.M2HLatBostContract` / `M2FiberCert`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Matrix NumberField IsDedekindDomain
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology ComplexOrder Pointwise

open RHDirect.ArakelovCovolume (rk covol degAr discreteTopology_of_le
  covol_pos rk_pos_of_ne_bot bost_slope_inequality bost_slope_inequality_divisible
  bost_degree_inequality_divisible bost_rank_bound_of_divisible bost_vanishing_criterion)
open RHDirect.Stage4ArakelovBost (IsSaturated dualLat)
open RHDirect.Stage11BostDworkSqueeze (latIndex covol_eq_index_mul_covol)
open RHDirect.Stage12SchurWeylLattices (euclideanSpaceCongr)
open RHDirect.Stage14Contracts (HLatAnchor M2HLatBostContract M2FiberCert)
open RHDirect.Stage14M2_HLatNumberField (vecAt fcoord normAt majAt realizeHLat zRealize
  rkK HLat discreteTopology_zRealize_of_fg isZLattice_zRealize_of_good rk_zRealize_eq
  realizeHLat_injective zRealize_ne_bot covolHLat_eq_zlattice_covolume twist_index
  logDiscDivDeg discShift degHLat slopeHLat muDef muMaxDef muMinDef muMaxDef_le_zMuMax
  zMuMin_le_muMinDef muDef_sublattice_index dualLatO annO dualFrame dualFrame_frameOK
  dualHLat bridge_ccb_dual dualLatO_fg dualLatO_span_top hlat_duality_slope_neg
  hlat_orthog_direct_sum_normalized)
open RHDirect.Stage14M2_BesselSchurBlock (IsIdOrConj isIdOrConj_id isIdOrConj_conj
  BesselBlockMatrix IsometryBlockFactorization MatKSpectralParams
  BesselGramSpectralBundle besselId_to_isometryBlockFactorization toStage2GramFrameFiber
  bost_slope_ineq_of_bessel_bundle)
open RHDirect.CapelliCore (GlRel capelliMatrix e_mul_sub_mul_capelliMatrix_pow
  e_comm_trace_capelliMatrix_pow casK casK_comm casC casC_eq_sum_shifted capelliTm
  qminor qdet qdet_two_holomorphic_eigenvalue det_norm_le det_sq_eq_one_of_preserves_bilin
  isIntegral_det_of_isIntegral isIntegral_det_of_preserves_lattice
  valuation_det_le_one_of_entries_le_one valuation_det_eq_one_iff_diag_eq_one
  charpoly_coeff_valuation)
open RHDirect.PAdicChainValuation (valSubring ChainValuationSystem)

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RHDirect.Stage14M2_BesselIntegrality

/-! ## Section 1: Concrete Dual Target Lattice `TargetDualHLatRR` (`RR^∨`) & `HLatAnchor` Alignment -/

section TargetDualHLatSection

/-- Convert any good, nonzero number-field Hermitian lattice `A : HLat K` into a
`Stage14Contracts.HLatAnchor` grounded on `ArakelovCovolume` (`zRealize`). -/
def toHLatAnchor {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) : HLatAnchor where
  E := EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)
  L := A.zRealize
  disc := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  ne_bot := zRealize_ne_bot A.b A.X hG.1 hL0

lemma toHLatAnchor_rk {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    (toHLatAnchor A hG hL0).rk = Module.finrank ℚ K * A.rank := by
  haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  unfold HLatAnchor.rk toHLatAnchor HLat.rank
  exact rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1

lemma toHLatAnchor_covol {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    (toHLatAnchor A hG hL0).covol = covol A.zRealize := rfl

lemma toHLatAnchor_degAr {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    (toHLatAnchor A hG hL0).degAr = degHLat A.b A.X A.L := rfl

lemma toHLatAnchor_slope {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    (toHLatAnchor A hG hL0).slope = slopeHLat A.b A.X A.L := rfl

lemma toHLatAnchor_muMax {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    (toHLatAnchor A hG hL0).muMax = ArakelovCovolume.muMax A.zRealize := rfl

lemma hlat_mu_eq_two_mul_anchor_slope {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    A.mu = 2 * (toHLatAnchor A hG hL0).slope - Real.log 2 + logDiscDivDeg K := rfl

lemma hlat_muMax_le_two_mul_anchor_muMax {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    A.muMax ≤ 2 * (toHLatAnchor A hG hL0).muMax - Real.log 2 + logDiscDivDeg K :=
  muMaxDef_le_zMuMax A.b A.X hG.1 A.L hG.2.1 hL0

lemma anchor_mu_of_zMuMin {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hL0 : A.L ≠ ⊥) :
    2 * RHDirect.Stage4ArakelovBost.muMin A.zRealize - Real.log 2 + logDiscDivDeg K ≤ A.muMin :=
  zMuMin_le_muMinDef A.b A.X hG.1 A.L hG.2.1 hL0

lemma hlat_ne_bot_of_rank_pos {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hr : 0 < A.rank) : A.L ≠ ⊥ := by
  intro hbot
  have h0 : A.rank = 0 := by unfold HLat.rank rkK; rw [hbot]; simp
  omega

/-- **Concrete Target Dual Hermitian Lattice `TargetDualHLatRR` (`RR^∨`)**:
packages a good, positive-rank base Hermitian lattice `RR : HLat K` over a totally complex
number field `K`, inducing the concrete dual Hermitian lattice `RR^∨ = dualHLat RR` with all
Arakelov/duality/anchor invariants. -/
structure TargetDualHLatRR (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] : Type 1 where
  RR : HLat K
  RR_good : RR.Good
  RR_rank_pos : 0 < RR.rank

namespace TargetDualHLatRR

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- The concrete dual Hermitian lattice `RR^∨ = dualHLat RR`. -/
abbrev dual (T : TargetDualHLatRR K) : HLat K :=
  dualHLat T.RR

lemma base_ne_bot (T : TargetDualHLatRR K) : T.RR.L ≠ ⊥ :=
  hlat_ne_bot_of_rank_pos T.RR T.RR_rank_pos

/-- The dual lattice `RR^∨` is `Good` (invertible frames, f.g. over `𝓞 K`, full `K`-span). -/
theorem dual_good (T : TargetDualHLatRR K) : T.dual.Good := by
  haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
  exact ⟨dualFrame_frameOK T.RR.X T.RR_good.1,
    dualLatO_fg T.RR.b T.RR.L T.RR_good.2.2,
    dualLatO_span_top T.RR.b T.RR.L T.RR_good.2.1⟩

/-- The dual lattice `RR^∨` is nonzero (`(RR^∨).L ≠ ⊥`). -/
theorem dual_ne_bot (T : TargetDualHLatRR K) : T.dual.L ≠ ⊥ := by
  haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
  intro h0
  have hsp := T.dual_good.2.2
  change Submodule.span K (T.dual.L : Set T.dual.V) = ⊤ at hsp
  rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hsp
  have hfin0 : Module.finrank K (Module.Dual K T.RR.V) = 0 := by
    change Module.finrank K T.dual.V = 0
    rw [← finrank_top K T.dual.V, ← hsp, finrank_bot]
  rw [Subspace.dual_finrank_eq] at hfin0
  have hle : T.RR.rank ≤ Module.finrank K T.RR.V := Submodule.finrank_le _
  have hr := T.RR_rank_pos
  omega

/-- Exact `K`-rank preservation under duality: `(RR^∨).rank = RR.rank`. -/
theorem dual_rank_eq (T : TargetDualHLatRR K) : T.dual.rank = T.RR.rank := by
  haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
  unfold HLat.rank rkK
  rw [T.dual_good.2.2, T.RR_good.2.2, finrank_top, finrank_top]
  exact Subspace.dual_finrank_eq

theorem dual_rank_pos (T : TargetDualHLatRR K) : 0 < T.dual.rank := by
  rw [T.dual_rank_eq]; exact T.RR_rank_pos

/-- `Stage14Contracts.HLatAnchor` for the base lattice `RR`. -/
def baseAnchor (T : TargetDualHLatRR K) : HLatAnchor :=
  toHLatAnchor T.RR T.RR_good T.base_ne_bot

/-- `Stage14Contracts.HLatAnchor` for the concrete target dual lattice `RR^∨`. -/
def dualAnchor (T : TargetDualHLatRR K) : HLatAnchor :=
  toHLatAnchor T.dual T.dual_good T.dual_ne_bot

theorem dualAnchor_rk_eq (T : TargetDualHLatRR K) :
    T.dualAnchor.rk = Module.finrank ℚ K * T.RR.rank := by
  rw [dualAnchor, toHLatAnchor_rk, T.dual_rank_eq]

theorem dualAnchor_rk_pos (T : TargetDualHLatRR K) : 0 < T.dualAnchor.rk := by
  rw [T.dualAnchor_rk_eq]
  exact Nat.mul_pos Module.finrank_pos T.RR_rank_pos

/-- Exact Arakelov slope duality on `RR^∨` (`hlat_duality_slope_neg`):
`(RR^∨).mu = -RR.mu`, `(RR^∨).muMax = -RR.muMin`, `(RR^∨).muMin = -RR.muMax`. -/
theorem dual_slope_duality (T : TargetDualHLatRR K) :
    T.dual.mu = -T.RR.mu ∧
    T.dual.muMax = -T.RR.muMin ∧
    T.dual.muMin = -T.RR.muMax :=
  hlat_duality_slope_neg T.RR T.RR_good T.RR_rank_pos

theorem dual_mu_eq_two_mul_anchor_slope (T : TargetDualHLatRR K) :
    T.dual.mu = 2 * T.dualAnchor.slope - Real.log 2 + logDiscDivDeg K :=
  hlat_mu_eq_two_mul_anchor_slope T.dual T.dual_good T.dual_ne_bot

theorem dual_muMax_le_two_mul_anchor_muMax (T : TargetDualHLatRR K) :
    T.dual.muMax ≤ 2 * T.dualAnchor.muMax - Real.log 2 + logDiscDivDeg K :=
  hlat_muMax_le_two_mul_anchor_muMax T.dual T.dual_good T.dual_ne_bot

/-- Grounding of `RR^∨`'s covolume on Mathlib's `ZLattice.covolume`. -/
theorem dual_covol_eq_zlattice_covolume (T : TargetDualHLatRR K) :
    let e : (InfinitePlace K × T.dual.ι × Fin 2) ≃
        Fin (Fintype.card (InfinitePlace K × T.dual.ι × Fin 2)) := Fintype.equivFin _
    let iso : EuclideanSpace ℝ (InfinitePlace K × T.dual.ι × Fin 2) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × T.dual.ι × Fin 2))) :=
      euclideanSpaceCongr e
    let Λ := T.dual.zRealize.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
    ∃ (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      covol T.dual.zRealize = ZLattice.covolume Λ volume :=
  covolHLat_eq_zlattice_covolume T.dual T.dual_good

/-- Ideal twist of the base lattice `RR` by a nonzero ideal `𝔞 ≤ 𝓞 K`: `𝔞 • RR.L`. -/
def twistBase (T : TargetDualHLatRR K) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    TargetDualHLatRR K where
  RR := T.RR.withL (𝔞 • T.RR.L)
  RR_good := by
    haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
    refine ⟨T.RR_good.1, Submodule.FG.smul (IsNoetherian.noetherian 𝔞) T.RR_good.2.1, ?_⟩
    change Submodule.span K ((𝔞 • T.RR.L : Submodule (𝓞 K) T.RR.V) : Set T.RR.V) = ⊤
    rw [Stage14M2_HLatNumberField.twist_span_smul T.RR.L 𝔞 h𝔞, T.RR_good.2.2]
  RR_rank_pos := by
    haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
    unfold HLat.rank rkK
    change 0 < Module.finrank K (Submodule.span K ((𝔞 • T.RR.L : Submodule (𝓞 K) T.RR.V) : Set T.RR.V))
    rw [Stage14M2_HLatNumberField.twist_span_smul T.RR.L 𝔞 h𝔞]
    exact T.RR_rank_pos

/-- Exact normalized slope shift of `(twistBase T 𝔞 h𝔞).dual` (`+ 2 * log(N(𝔞)) / [K : ℚ]`). -/
theorem twistDual_mu_eq (T : TargetDualHLatRR K) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    (T.twistBase 𝔞 h𝔞).dual.mu =
      T.dual.mu + 2 * Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
  have h1 := (T.twistBase 𝔞 h𝔞).dual_slope_duality.1
  have h2 := T.dual_slope_duality.1
  have hrk : rkK (K := K) (𝔞 • T.RR.L) = T.RR.rank := by
    unfold rkK HLat.rank
    rw [Stage14M2_HLatNumberField.twist_span_smul T.RR.L 𝔞 h𝔞]
    rfl
  have hsub := muDef_sublattice_index T.RR.b T.RR.X T.RR_good.1 T.RR_good.2.1 T.base_ne_bot
    (Submodule.smul_le_right : 𝔞 • T.RR.L ≤ T.RR.L) hrk
  have hidx := twist_index T.RR.L T.RR_good.2.1 𝔞 h𝔞
  have htw : (T.twistBase 𝔞 h𝔞).RR.mu =
      T.RR.mu - 2 * Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    change muDef T.RR.b T.RR.X (𝔞 • T.RR.L) = _
    rw [hsub, hidx, Nat.cast_pow, Real.log_pow]
    have hrk_pos : (0 : ℝ) < (T.RR.rank : ℝ) := Nat.cast_pos.mpr T.RR_rank_pos
    have hdeg_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    change muDef T.RR.b T.RR.X T.RR.L -
      2 * ((T.RR.rank : ℝ) * Real.log (Ideal.absNorm 𝔞 : ℝ)) /
        ((Module.finrank ℚ K : ℝ) * (T.RR.rank : ℝ)) =
      muDef T.RR.b T.RR.X T.RR.L -
        2 * Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)
    field_simp [hrk_pos.ne', hdeg_pos.ne']
  rw [h1, htw, h2]
  ring

/-- **Canonical 0-Assumption `TargetDualHLatRR` (`std`)** on `Fin n → K` (`n ≥ 1`) with the
standard `𝓞 K`-lattice `span_{𝓞 K}(e_i)` and unit archimedean frames `1`. -/
abbrev std (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (n : ℕ) (hn : 0 < n) : TargetDualHLatRR K where
  RR :=
    { V := Fin n → K
      ι := Fin n
      b := Pi.basisFun K (Fin n)
      X := fun _ => 1
      L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) }
  RR_good := by
    refine ⟨fun _ => by simp, Submodule.fg_span (Set.finite_range _), ?_⟩
    apply le_antisymm le_top
    intro x _
    rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩)
  RR_rank_pos := by
    unfold HLat.rank rkK
    have hsp : Submodule.span K ((Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) :
        Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤ := by
      apply le_antisymm le_top
      intro x _
      rw [← (Pi.basisFun K (Fin n)).sum_repr x]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩)
    rw [hsp, finrank_top, Module.finrank_fin_fun]
    exact hn

end TargetDualHLatRR

end TargetDualHLatSection

/-! ## Section 2: Dedekind Local-to-Global Integrality & Congruence Sublattices `Nu` -/

section DedekindIntegralityAndNu

variable {K : Type} [Field K] [NumberField K]

/-- **Dedekind Local-to-Global Integrality Criterion**:
an element `x : K` lies in `𝓞 K` iff `la.valuation K x ≤ 1` at every height-one prime `la`. -/
theorem mem_ringOfIntegers_of_forall_valuation_le_one (x : K) :
    (∀ la : HeightOneSpectrum (𝓞 K), la.valuation K x ≤ 1) ↔
      x ∈ Set.range (algebraMap (𝓞 K) K) := by
  constructor
  · intro h
    exact HeightOneSpectrum.mem_integers_of_valuation_le_one K x h
  · rintro ⟨r, rfl⟩ la
    exact la.valuation_le_one r

/-- **Denominator-Clearing + Prime-Local Integrality Criterion**:
if a nonzero natural number `D` clears the denominator of `x : K` (`(D : K) * x ∈ 𝓞 K`) AND
`la.valuation K x ≤ 1` at every height-one prime `la` dividing `D` (`(D : 𝓞 K) ∈ la.asIdeal`),
then `x ∈ 𝓞 K`. -/
theorem mem_ringOfIntegers_of_denom_and_local_le_one (D : ℕ) (_hD : 0 < D) (x : K)
    (hclear : (D : K) * x ∈ Set.range (algebraMap (𝓞 K) K))
    (hloc : ∀ la : HeightOneSpectrum (𝓞 K), (D : 𝓞 K) ∈ la.asIdeal → la.valuation K x ≤ 1) :
    x ∈ Set.range (algebraMap (𝓞 K) K) := by
  rw [← mem_ringOfIntegers_of_forall_valuation_le_one]
  intro la
  by_cases hmem : (D : 𝓞 K) ∈ la.asIdeal
  · exact hloc la hmem
  · have hvD : la.valuation K (algebraMap (𝓞 K) K (D : 𝓞 K)) = 1 :=
      (la.valuation_eq_one_iff_notMem (K := K)).mpr hmem
    have hvDx : la.valuation K ((D : K) * x) ≤ 1 := by
      obtain ⟨r, hr⟩ := hclear
      rw [← hr]
      exact la.valuation_le_one r
    rw [map_mul, show (D : K) = algebraMap (𝓞 K) K (D : 𝓞 K) from by simp, hvD, one_mul] at hvDx
    exact hvDx

/-- **Ideal-Element Clearing + Prime-Local Integrality Criterion**:
if `r : 𝓞 K` clears the denominator of `x : K` AND `la.valuation K x ≤ 1` at every
height-one prime `la` with `r ∈ la.asIdeal`, then `x ∈ 𝓞 K`. -/
theorem mem_ringOfIntegers_of_ideal_clearing_and_local_le_one (r : 𝓞 K) (x : K)
    (hclear : algebraMap (𝓞 K) K r * x ∈ Set.range (algebraMap (𝓞 K) K))
    (hloc : ∀ la : HeightOneSpectrum (𝓞 K), r ∈ la.asIdeal → la.valuation K x ≤ 1) :
    x ∈ Set.range (algebraMap (𝓞 K) K) := by
  rw [← mem_ringOfIntegers_of_forall_valuation_le_one]
  intro la
  by_cases hmem : r ∈ la.asIdeal
  · exact hloc la hmem
  · have hvr : la.valuation K (algebraMap (𝓞 K) K r) = 1 :=
      (la.valuation_eq_one_iff_notMem (K := K)).mpr hmem
    have hvrx : la.valuation K (algebraMap (𝓞 K) K r * x) ≤ 1 := by
      obtain ⟨s, hs⟩ := hclear
      rw [← hs]
      exact la.valuation_le_one s
    rw [map_mul, hvr, one_mul] at hvrx
    exact hvrx

/-- **Bridge from `PAdicChainValuation.valSubring` to `HeightOneSpectrum` Valuation**:
given an additive valuation `val : AddValuation LL (WithTop ℤ)` whose valuation subring maps into
`la`'s valuation unit ball via `embK : LL →+* K`, any sharp column-valuation quotient
`c * T^a * (T^b)⁻¹` from `ChainValuationSystem.quot_mem_valRing` automatically has
`la.valuation K (embK (c * T^a * (T^b)⁻¹)) ≤ 1`. -/
theorem valuation_le_one_of_chain_quot {LL ι : Type*} [Field LL]
    (X : ChainValuationSystem K LL ι) (la : HeightOneSpectrum (𝓞 K))
    (hcompat : ∀ z ∈ valSubring X.val, la.valuation K (X.embK z) ≤ 1)
    {c : LL} {n : ℤ} (hc : X.val c = (n : WithTop ℤ)) (a b : ℕ)
    (hn : ((X.ramIdx * b : ℕ) : ℤ) ≤ n) :
    la.valuation K (X.embK (c * (X.T : LL) ^ a * ((X.T : LL) ^ b)⁻¹)) ≤ 1 :=
  hcompat _ (X.quot_mem_valRing hc a b hn)

/-- Direct `AddValuation (𝓞 K)`-compatible bridge at a height-one prime `la` above `T`:
if `z : K` has `ord_la(z) ≥ 0`, then `la.valuation K z ≤ 1`. -/
theorem valuation_le_one_of_withTop_nonneg (la : HeightOneSpectrum (𝓞 K)) {z : K}
    (hz : z = 0 ∨ (0 : ℤ) ≤ -WithZero.log (la.valuation K z)) :
    la.valuation K z ≤ 1 := by
  rcases hz with rfl | hlog
  · simp
  · by_cases h0 : la.valuation K z = 0
    · rw [h0]; exact zero_le_one
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)

/-- **Concrete Congruence Sublattice `CongruenceSublatticeNu` (`Nu u`)**:
an `𝓞 K`-sublattice `Nu ≤ M.L` inside a good positive-rank ambient Hermitian lattice `M : HLat K`,
having full `K`-rank `rkK Nu = M.rank`. -/
structure CongruenceSublatticeNu (K : Type) [Field K] [NumberField K] [StarRing K] : Type 1 where
  M : HLat K
  M_good : M.Good
  M_rank_pos : 0 < M.rank
  Nu : Submodule (𝓞 K) M.V
  Nu_le : Nu ≤ M.L
  Nu_ne_bot : Nu ≠ ⊥
  Nu_rank_eq : rkK (K := K) Nu = M.rank

namespace CongruenceSublatticeNu

variable [StarRing K]

lemma M_ne_bot (C : CongruenceSublatticeNu K) : C.M.L ≠ ⊥ :=
  hlat_ne_bot_of_rank_pos C.M C.M_rank_pos

lemma Nu_fg (C : CongruenceSublatticeNu K) : C.Nu.FG :=
  Submodule.FG.of_le C.M_good.2.1 C.Nu_le

lemma Nu_span_top (C : CongruenceSublatticeNu K) :
    Submodule.span K (C.Nu : Set C.M.V) = ⊤ := by
  haveI : Module.Finite K C.M.V := Module.Finite.of_basis C.M.b
  have hfin : Module.finrank K (Submodule.span K (C.Nu : Set C.M.V)) =
      Module.finrank K C.M.V := by
    have hr := C.Nu_rank_eq
    unfold rkK HLat.rank at hr
    change Module.finrank K (Submodule.span K (C.Nu : Set C.M.V)) =
      Module.finrank K (Submodule.span K (C.M.L : Set C.M.V)) at hr
    rw [C.M_good.2.2, finrank_top] at hr
    exact hr
  exact Submodule.eq_top_of_finrank_eq hfin

/-- View `Nu` itself as a concrete `HLat K` (keeping `M`'s ambient space, basis, and frame). -/
def toHLat (C : CongruenceSublatticeNu K) : HLat K :=
  C.M.withL C.Nu

theorem toHLat_good (C : CongruenceSublatticeNu K) : C.toHLat.Good :=
  ⟨C.M_good.1, C.Nu_fg, C.Nu_span_top⟩

/-- Canonical `Stage14Contracts.HLatAnchor` for `Nu`. -/
def toHLatAnchor (C : CongruenceSublatticeNu K) : HLatAnchor :=
  RHDirect.Stage14M2_BesselIntegrality.toHLatAnchor C.toHLat C.toHLat_good C.Nu_ne_bot

theorem toHLatAnchor_rk (C : CongruenceSublatticeNu K) :
    C.toHLatAnchor.rk = Module.finrank ℚ K * C.M.rank := by
  have h1 := RHDirect.Stage14M2_BesselIntegrality.toHLatAnchor_rk C.toHLat C.toHLat_good C.Nu_ne_bot
  change C.toHLatAnchor.rk = Module.finrank ℚ K * C.toHLat.rank at h1
  rw [h1]
  unfold HLat.rank toHLat HLat.withL
  exact congrArg (Module.finrank ℚ K * ·) C.Nu_rank_eq

/-- Exact normalized slope index-shift identity for `Nu ≤ M.L`:
`C.toHLat.mu = C.M.mu - 2 * log [M.L : Nu] / ([K : ℚ] * M.rank)`. -/
theorem mu_eq_sub_index_log (C : CongruenceSublatticeNu K) :
    C.toHLat.mu = C.M.mu -
      2 * Real.log (C.Nu.toAddSubgroup.relIndex C.M.L.toAddSubgroup : ℝ) /
        ((Module.finrank ℚ K : ℝ) * (C.M.rank : ℝ)) :=
  muDef_sublattice_index C.M.b C.M.X C.M_good.1 C.M_good.2.1 C.M_ne_bot C.Nu_le C.Nu_rank_eq

/-- Concrete congruence sublattice `𝔞 • M.L` cut out by a nonzero ideal `𝔞 ≤ 𝓞 K`
(e.g., an inert-prime power or ramified level ideal). -/
abbrev ofIdealTwist (M : HLat K) (hG : M.Good) (hr : 0 < M.rank)
    (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) : CongruenceSublatticeNu K where
  M := M
  M_good := hG
  M_rank_pos := hr
  Nu := 𝔞 • M.L
  Nu_le := Submodule.smul_le_right
  Nu_ne_bot := by
    haveI : Module.Finite K M.V := Module.Finite.of_basis M.b
    intro hbot
    have hsp := Stage14M2_HLatNumberField.twist_span_smul M.L 𝔞 h𝔞
    rw [hbot, Submodule.bot_coe, Submodule.span_zero_singleton, hG.2.2] at hsp
    have hfin0 : Module.finrank K M.V = 0 := by rw [← finrank_top K M.V, ← hsp, finrank_bot]
    have hrk0 : M.rank = 0 := by
      unfold HLat.rank rkK
      rw [hG.2.2, finrank_top, hfin0]
    omega
  Nu_rank_eq := by
    haveI : Module.Finite K M.V := Module.Finite.of_basis M.b
    unfold rkK HLat.rank
    exact congrArg (fun S : Submodule K M.V => Module.finrank K S)
      (Stage14M2_HLatNumberField.twist_span_smul M.L 𝔞 h𝔞)

theorem ofIdealTwist_mu_eq (M : HLat K) (hG : M.Good) (hr : 0 < M.rank)
    (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    (ofIdealTwist M hG hr 𝔞 h𝔞).toHLat.mu =
      M.mu - 2 * Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  haveI : Module.Finite K M.V := Module.Finite.of_basis M.b
  have h1 := (ofIdealTwist M hG hr 𝔞 h𝔞).mu_eq_sub_index_log
  have hidx := twist_index M.L hG.2.1 𝔞 h𝔞
  change muDef M.b M.X (𝔞 • M.L) = muDef M.b M.X M.L -
    2 * Real.log (((𝔞 • M.L).toAddSubgroup.relIndex M.L.toAddSubgroup : ℕ) : ℝ) /
      ((Module.finrank ℚ K : ℝ) * (M.rank : ℝ)) at h1
  change (ofIdealTwist M hG hr 𝔞 h𝔞).toHLat.mu = _
  change muDef M.b M.X (𝔞 • M.L) = _
  rw [h1, hidx, Nat.cast_pow, Real.log_pow]
  have hr_pos : (0 : ℝ) < (M.rank : ℝ) := Nat.cast_pos.mpr hr
  have hdeg_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  unfold HLat.rank at hr_pos ⊢
  change muDef M.b M.X M.L -
    2 * ((rkK (K := K) M.L : ℝ) * Real.log (Ideal.absNorm 𝔞 : ℝ)) /
      ((Module.finrank ℚ K : ℝ) * (rkK (K := K) M.L : ℝ)) =
    muDef M.b M.X M.L - 2 * Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)
  field_simp [hr_pos.ne', hdeg_pos.ne']

/-- Congruence sublattice `(𝔞 • M.L) ⊓ K_sat` intersecting an ideal congruence condition with
any full-rank sublattice `K_sat ≤ M.L` (e.g. a `p`-adic chain-clearing sublattice). -/
def ofIdealAndSublattice (M : HLat K) (hG : M.Good) (hr : 0 < M.rank)
    (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (K_sat : Submodule (𝓞 K) M.V)
    (hK_le : K_sat ≤ M.L) (hK_rk : rkK (K := K) K_sat = M.rank) :
    CongruenceSublatticeNu K where
  M := M
  M_good := hG
  M_rank_pos := hr
  Nu := (𝔞 • M.L) ⊓ K_sat
  Nu_le := inf_le_right.trans hK_le
  Nu_ne_bot := by
    haveI : Module.Finite K M.V := Module.Finite.of_basis M.b
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
    have hK_sp : Submodule.span K (K_sat : Set M.V) = ⊤ := by
      unfold rkK HLat.rank at hK_rk
      change Module.finrank K (Submodule.span K (K_sat : Set M.V)) =
        Module.finrank K (Submodule.span K (M.L : Set M.V)) at hK_rk
      rw [hG.2.2, finrank_top] at hK_rk
      exact Submodule.eq_top_of_finrank_eq hK_rk
    have hK_ne : K_sat ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.bot_coe, Submodule.span_zero_singleton] at hK_sp
      have hfin0 : Module.finrank K M.V = 0 := by rw [← finrank_top K M.V, ← hK_sp, finrank_bot]
      have hr0 : M.rank = 0 := by unfold HLat.rank rkK; rw [hG.2.2, finrank_top, hfin0]
      omega
    obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK_ne
    have hmx0 : m • x ≠ 0 := by
      intro hz
      have h1 : (algebraMap (𝓞 K) K m) • x = 0 := by rwa [algebraMap_smul]
      rcases smul_eq_zero.mp h1 with hm0' | hx0'
      · exact hm0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (hm0'.trans (map_zero _).symm))
      · exact hx0 hx0'
    intro hbot
    apply hmx0
    have hmem : m • x ∈ (𝔞 • M.L) ⊓ K_sat :=
      ⟨Submodule.smul_mem_smul hm (hK_le hxK), K_sat.smul_mem m hxK⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  Nu_rank_eq := by
    haveI : Module.Finite K M.V := Module.Finite.of_basis M.b
    have hle : rkK (K := K) ((𝔞 • M.L) ⊓ K_sat) ≤ M.rank := by
      unfold rkK HLat.rank
      change Module.finrank K (Submodule.span K (((𝔞 • M.L ⊓ K_sat : Submodule (𝓞 K) M.V) : Set M.V))) ≤
        Module.finrank K (Submodule.span K (M.L : Set M.V))
      rw [hG.2.2, finrank_top]
      exact Submodule.finrank_le _
    have hge : M.rank ≤ rkK (K := K) ((𝔞 • M.L) ⊓ K_sat) := by
      obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
      have hmK : (algebraMap (𝓞 K) K m) ≠ 0 :=
        fun h => hm0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (h.trans (map_zero _).symm))
      have hsub : m • K_sat ≤ (𝔞 • M.L) ⊓ K_sat := by
        rintro _ ⟨x, hxK, rfl⟩
        exact ⟨Submodule.smul_mem_smul hm (hK_le hxK), K_sat.smul_mem m hxK⟩
      have hsp_sub : Submodule.span K (K_sat : Set M.V) ≤
          Submodule.span K ((((𝔞 • M.L) ⊓ K_sat : Submodule (𝓞 K) M.V) : Set M.V)) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          have hmy : m • y ∈ (𝔞 • M.L) ⊓ K_sat := hsub ⟨y, hy, rfl⟩
          have hsp := Submodule.subset_span (R := K) hmy
          have h1 : (algebraMap (𝓞 K) K m)⁻¹ • (algebraMap (𝓞 K) K m • y) = y := by
            rw [smul_smul, inv_mul_cancel₀ hmK, one_smul]
          rw [← h1]
          refine Submodule.smul_mem _ _ ?_
          simpa [algebraMap_smul] using hsp
        | zero => exact zero_mem _
        | add _ _ _ _ ha hb => exact add_mem ha hb
        | smul c _ _ ha => exact Submodule.smul_mem _ c ha
      rw [← hK_rk]
      exact Submodule.finrank_mono hsp_sub
    omega

end CongruenceSublatticeNu

end DedekindIntegralityAndNu

/-! ## Section 3: `IteratedBesselMapBk` & `OneMapIntoCC` -/

section IteratedBesselMapSection

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- **Concrete Iterated Bessel / Theta Morphism `IteratedBesselMapBk` (`D.div.Bk`)**:
packages a target dual Hermitian lattice `T : TargetDualHLatRR K` (`RR^∨`), a finite word family
`u : ι` with congruence sublattices `Nu u`, `K`-linear iterated Bessel/theta morphisms
`Bk u : (Nu u).M.V →ₗ[K] Module.Dual K T.RR.V`, archimedean operator bounds `C_op u > 0`, and
explicit chain-denominator clearing + prime-local valuation bounds ensuring integrality on `Nu u`. -/
structure IteratedBesselMapBk (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] : Type 1 where
  T : TargetDualHLatRR K
  Nu : ι → CongruenceSublatticeNu K
  Bk : ∀ u : ι, (Nu u).M.V →ₗ[K] Module.Dual K T.RR.V
  C_op : ι → ℝ
  C_op_pos : ∀ u : ι, 0 < C_op u
  arch_bound : ∀ u (x : (Nu u).M.V),
    ‖realizeHLat T.dual.b T.dual.X (Bk u x)‖ ≤
      C_op u * ‖realizeHLat (Nu u).M.b (Nu u).M.X x‖
  D_chain : ι → ℕ
  D_chain_pos : ∀ u : ι, 0 < D_chain u
  chain_clears : ∀ u (φ : (Nu u).M.V), φ ∈ (Nu u).Nu →
    ∀ F ∈ T.RR.L, ((D_chain u : ℕ) : K) * Bk u φ F ∈ Set.range (algebraMap (𝓞 K) K)
  local_val_le_one : ∀ u (φ : (Nu u).M.V), φ ∈ (Nu u).Nu →
    ∀ F ∈ T.RR.L, ∀ la : HeightOneSpectrum (𝓞 K),
      (D_chain u : 𝓞 K) ∈ la.asIdeal → la.valuation K (Bk u φ F) ≤ 1

namespace IteratedBesselMapBk

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Unified `OneMapIntoCC`**: sums the word-indexed Bessel morphisms `Bk u` into a single
`K`-linear morphism `(∀ u, (Nu u).M.V) →ₗ[K] Module.Dual K T.RR.V`. -/
def oneMap (B : IteratedBesselMapBk K ι) :
    (∀ u : ι, (B.Nu u).M.V) →ₗ[K] Module.Dual K B.T.RR.V where
  toFun x := ∑ u : ι, B.Bk u (x u)
  map_add' x y := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

lemma oneMap_apply (B : IteratedBesselMapBk K ι) (x : ∀ u : ι, (B.Nu u).M.V) :
    B.oneMap x = ∑ u : ι, B.Bk u (x u) := rfl

lemma oneMap_single (B : IteratedBesselMapBk K ι) (u : ι) (v : (B.Nu u).M.V) :
    B.oneMap (Pi.single u v) = B.Bk u v := by
  rw [oneMap_apply]
  refine (Finset.sum_eq_single u (fun u' _ hu' => ?_) (fun h => absurd (Finset.mem_univ u) h)).trans ?_
  · rw [Pi.single_eq_of_ne hu', map_zero]
  · rw [Pi.single_eq_same]

/-- Unified archimedean norm bound for `OneMapIntoCC` via Cauchy–Schwarz across `u : ι`. -/
theorem oneMap_arch_bound (B : IteratedBesselMapBk K ι) (x : ∀ u : ι, (B.Nu u).M.V) :
    ‖realizeHLat B.T.dual.b B.T.dual.X (B.oneMap x)‖ ≤
      Real.sqrt (∑ u : ι, B.C_op u ^ 2) *
        Real.sqrt (∑ u : ι, ‖realizeHLat (B.Nu u).M.b (B.Nu u).M.X (x u)‖ ^ 2) := by
  have hmap : realizeHLat B.T.dual.b B.T.dual.X (B.oneMap x) =
      ∑ u : ι, realizeHLat B.T.dual.b B.T.dual.X (B.Bk u (x u)) := by
    rw [oneMap_apply]
    exact map_sum (realizeHLat B.T.dual.b B.T.dual.X) (fun u => B.Bk u (x u)) Finset.univ
  rw [hmap]
  calc ‖∑ u : ι, realizeHLat B.T.dual.b B.T.dual.X (B.Bk u (x u))‖
      ≤ ∑ u : ι, ‖realizeHLat B.T.dual.b B.T.dual.X (B.Bk u (x u))‖ := norm_sum_le _ _
    _ ≤ ∑ u : ι, B.C_op u * ‖realizeHLat (B.Nu u).M.b (B.Nu u).M.X (x u)‖ :=
        Finset.sum_le_sum fun u _ => B.arch_bound u (x u)
    _ ≤ Real.sqrt (∑ u : ι, B.C_op u ^ 2) *
          Real.sqrt (∑ u : ι, ‖realizeHLat (B.Nu u).M.b (B.Nu u).M.X (x u)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun u => B.C_op u) (fun u => ‖realizeHLat (B.Nu u).M.b (B.Nu u).M.X (x u)‖)

/-- **Builder from `PAdicChainValuation.ChainValuationSystem` (`ofChainValuationSystem`)**:
given an `m`-step iterated theta-lift chain `X : ChainValuationSystem K K ι_u` (from `PAdicChainValuation`)
for each word `u`, together with a base Bessel pairing `pairAt : ∀ u, X.Fn X.m →ₗ[K] Module.Dual K T.RR.V`
that is integral on the level-`m` common lattice `X.embV X.m (X.S X.m)` and cleared along `m` steps
by `D_chain u`, builds a concrete `IteratedBesselMapBk K ι`! -/
def ofChainValuationSystem
    (T : TargetDualHLatRR K) (Nu : ι → CongruenceSublatticeNu K)
    {ι_op : ι → Type}
    (X : ∀ u : ι, ChainValuationSystem K K (ι_op u))
    (hEmb : ∀ u, (X u).embK = RingHom.id K)
    (hFormSt : ∀ u, (X u).FormsStable)
    {s : ι → ℕ} (hComm : ∀ u, (X u).UOpCommutes (s u))
    (A_list : ∀ u, List (ι_op u)) (e_step a_pow : ι → ℕ)
    (hU : ∀ u i, i < (X u).m →
      (X u).Into i (i + 1) (fun φ => ((X u).T : K) ^ e_step u • (X u).Uprod (i + 1) (A_list u) ((X u).KT i φ)))
    (iotaNu : ∀ u, (Nu u).M.V →ₗ[K] (X u).Fn 0)
    (hiotaNu_mem : ∀ u (φ : (Nu u).M.V), φ ∈ (Nu u).Nu →
      ∃ (D_den : ℕ) (x0 : (X u).Vl 0) (c : K) (n : ℤ),
        0 < D_den ∧ x0 ∈ (X u).S 0 ∧ (X u).val c = (n : WithTop ℤ) ∧
        ((X u).ramIdx * ((X u).m * e_step u + s u * (A_list u).length *
          ∑ j ∈ Finset.range ((X u).m + 1), j) : ℤ) ≤ n ∧
        (D_den : K) • ((X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) (iotaNu u φ))) =
          (c * ((X u).T : K) ^ a_pow u) •
            (X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) ((X u).embV 0 x0)))
    (pairAt : ∀ u, (X u).Fn (X u).m →ₗ[K] Module.Dual K T.RR.V)
    (hPairInt : ∀ u (z : (X u).Vl (X u).m), z ∈ (X u).S (X u).m →
      ∀ F ∈ T.RR.L, pairAt u ((X u).embV (X u).m z) F ∈ Set.range (algebraMap (𝓞 K) K))
    (D_chain : ι → ℕ) (hD_pos : ∀ u, 0 < D_chain u)
    (hD_clears : ∀ u (φ : (Nu u).M.V), φ ∈ (Nu u).Nu →
      ∀ F ∈ T.RR.L, (D_chain u : K) *
        pairAt u ((X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) (iotaNu u φ))) F ∈
          Set.range (algebraMap (𝓞 K) K))
    (hDenUnit : ∀ u (la : HeightOneSpectrum (𝓞 K)) (D_den : ℕ), 0 < D_den →
      (D_chain u : 𝓞 K) ∈ la.asIdeal → (D_den : 𝓞 K) ∉ la.asIdeal)
    (C_op : ι → ℝ) (hC_pos : ∀ u, 0 < C_op u)
    (hArch : ∀ u (x : (Nu u).M.V),
      ‖realizeHLat T.dual.b T.dual.X
        (pairAt u ((X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) (iotaNu u x))))‖ ≤
        C_op u * ‖realizeHLat (Nu u).M.b (Nu u).M.X x‖) :
    IteratedBesselMapBk K ι where
  T := T
  Nu := Nu
  Bk u :=
    { toFun := fun x => pairAt u ((X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) (iotaNu u x)))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => by simp only [map_smul, RingHom.id_apply] }
  C_op := C_op
  C_op_pos := hC_pos
  arch_bound := hArch
  D_chain := D_chain
  D_chain_pos := hD_pos
  chain_clears := hD_clears
  local_val_le_one := fun u φ hφ F hF la hla => by
    obtain ⟨D_den, x0, c, n, hD_den_pos, hx0, hc, hn, hrel⟩ := hiotaNu_mem u φ hφ
    have hsharp := (X u).levelChainSharpColumnValuation_of_stability
      (hFormSt u) (hComm u) (A_list u) (e_step u) (a_pow u) (hU u) hc hn hx0
    obtain ⟨z, hzS, hz_eq⟩ := hsharp
    have hEmbId : ∀ a : K, (X u).embK a = a := fun a => by rw [hEmb u]; rfl
    rw [hEmbId] at hz_eq
    have hscale : (D_den : K) *
        pairAt u ((X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) (iotaNu u φ))) F =
        pairAt u ((X u).embV (X u).m z) F := by
      rw [hz_eq, ← hrel, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hInt : pairAt u ((X u).embV (X u).m z) F ∈ Set.range (algebraMap (𝓞 K) K) :=
      hPairInt u z hzS F hF
    obtain ⟨r, hr⟩ := hInt
    have hv_prod : la.valuation K ((D_den : K) *
        pairAt u ((X u).colUp (X u).m (((X u).Uprod 0 (A_list u) ^ (X u).m) (iotaNu u φ))) F) ≤ 1 := by
      rw [hscale, ← hr]
      exact la.valuation_le_one r
    have hnot : (D_den : 𝓞 K) ∉ la.asIdeal := hDenUnit u la D_den hD_den_pos hla
    have hv_den : la.valuation K (D_den : K) = 1 := by
      simpa using (la.valuation_eq_one_iff_notMem (K := K)).mpr hnot
    rw [map_mul, hv_den, one_mul] at hv_prod
    exact hv_prod

end IteratedBesselMapBk

/-- Standalone alias for `IteratedBesselMapBk.oneMap`, matching `OneMapIntoCC`. -/
abbrev OneMapIntoCC {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : IteratedBesselMapBk K ι) :
    (∀ u : ι, (B.Nu u).M.V) →ₗ[K] Module.Dual K B.T.RR.V :=
  B.oneMap

end IteratedBesselMapSection

/-! ## Section 4: `bessel_map_maps_Nu_into_RRDual` & Ramified Bost Slope Bounds -/

section BesselMapsNuIntoRRDual

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For every word `u`, every `φ ∈ Nu u`, and every `F ∈ T.RR.L`, the iterated Bessel/theta pairing
`B.Bk u φ F` lies in the ring of integers `𝓞 K`. -/
theorem bessel_pairing_mem_ringOfIntegers (B : IteratedBesselMapBk K ι) (u : ι)
    {φ : (B.Nu u).M.V} (hφ : φ ∈ (B.Nu u).Nu) {F : B.T.RR.V} (hF : F ∈ B.T.RR.L) :
    B.Bk u φ F ∈ Set.range (algebraMap (𝓞 K) K) :=
  mem_ringOfIntegers_of_denom_and_local_le_one (B.D_chain u) (B.D_chain_pos u) (B.Bk u φ F)
    (B.chain_clears u φ hφ F hF) (fun la hla => B.local_val_le_one u φ hφ F hF la hla)

/-- **Main Bessel Integrality Theorem (`bessel_map_maps_Nu_into_RRDual`)**:
for every word `u : ι`, the iterated Bessel/theta morphism `B.Bk u` maps the congruence sublattice
`Nu u` into the dual integral lattice `(T.dual).L = dualLatO T.RR.L`, AND equivalently induces an
`𝓞 K`-bilinear pairing `Nu u →ₗ[𝓞 K] Module.Dual (𝓞 K) T.RR.L` (via `bridge_ccb_dual`). -/
theorem bessel_map_maps_Nu_into_RRDual (B : IteratedBesselMapBk K ι) (u : ι) :
    (B.Nu u).Nu.map ((B.Bk u).restrictScalars (𝓞 K)) ≤ B.T.dual.L ∧
      (∃ β : (B.Nu u).Nu →ₗ[𝓞 K] Module.Dual (𝓞 K) B.T.RR.L,
        ∀ (φ : (B.Nu u).Nu) (F : B.T.RR.L),
          algebraMap (𝓞 K) K (β φ F) = B.Bk u (φ : (B.Nu u).M.V) (F : B.T.RR.V)) := by
  have hmap : (B.Nu u).Nu.map ((B.Bk u).restrictScalars (𝓞 K)) ≤ B.T.dual.L := by
    rintro _ ⟨φ, hφ, rfl⟩ F hF
    exact bessel_pairing_mem_ringOfIntegers B u hφ hF
  exact ⟨hmap, (bridge_ccb_dual B.T.RR.L (B.Nu u).Nu (B.Bk u)).mpr hmap⟩

/-- Corollary for `OneMapIntoCC`: any family `x u ∈ (Nu u).Nu` maps into `RR^∨` under `oneMap`. -/
theorem oneMapIntoCC_maps_into_RRDual (B : IteratedBesselMapBk K ι)
    (x : ∀ u : ι, (B.Nu u).M.V) (hx : ∀ u : ι, x u ∈ (B.Nu u).Nu) :
    OneMapIntoCC B x ∈ B.T.dual.L := by
  rw [IteratedBesselMapBk.oneMap_apply]
  refine Submodule.sum_mem B.T.dual.L fun u _ => ?_
  exact (bessel_map_maps_Nu_into_RRDual B u).1 ⟨x u, hx u, rfl⟩

/-- Canonical `ℤ`-linear equivalence between `C.Nu` and `C.toHLatAnchor.L`. -/
private def nuRealizeEquiv (C : CongruenceSublatticeNu K) :
    C.Nu ≃ₗ[ℤ] C.toHLatAnchor.L :=
  let f : C.Nu →ₗ[ℤ] C.toHLatAnchor.L :=
    { toFun := fun x => ⟨realizeHLat C.M.b C.M.X x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add (realizeHLat C.M.b C.M.X) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul (realizeHLat C.M.b C.M.X) c x.1) }
  LinearEquiv.ofBijective f
    ⟨fun x y hxy => by
      apply Subtype.ext
      exact realizeHLat_injective C.M.b C.M.X C.M_good.1 (congrArg Subtype.val hxy),
     fun ⟨z, hz⟩ => by
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩⟩

private lemma nuRealizeEquiv_apply (C : CongruenceSublatticeNu K) (x : C.Nu) :
    ((nuRealizeEquiv C x : C.toHLatAnchor.L) : C.toHLatAnchor.E) =
      realizeHLat C.M.b C.M.X x.1 := rfl

/-- Canonical `ℤ`-linear equivalence between `T.dual.L` and `T.dualAnchor.L`. -/
private def dualRealizeEquiv (T : TargetDualHLatRR K) :
    T.dual.L ≃ₗ[ℤ] T.dualAnchor.L :=
  let f : T.dual.L →ₗ[ℤ] T.dualAnchor.L :=
    { toFun := fun x => ⟨realizeHLat T.dual.b T.dual.X x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add (realizeHLat T.dual.b T.dual.X) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul (realizeHLat T.dual.b T.dual.X) c x.1) }
  LinearEquiv.ofBijective f
    ⟨fun x y hxy => by
      apply Subtype.ext
      exact realizeHLat_injective T.dual.b T.dual.X T.dual_good.1 (congrArg Subtype.val hxy),
     fun ⟨z, hz⟩ => by
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩⟩

private lemma dualRealizeEquiv_apply (T : TargetDualHLatRR K) (y : T.dual.L) :
    ((dualRealizeEquiv T y : T.dualAnchor.L) : T.dualAnchor.E) =
      realizeHLat T.dual.b T.dual.X y.1 := rfl

/-- Concrete `ℤ`-linear lattice morphism `(Nu u).toHLatAnchor.L →ₗ[ℤ] T.dualAnchor.L`
induced by `B.Bk u` and realized via `realizeHLat`. -/
def besselMapToAnchorHom (B : IteratedBesselMapBk K ι) (u : ι) :
    (B.Nu u).toHLatAnchor.L →ₗ[ℤ] B.T.dualAnchor.L :=
  let bkZ : (B.Nu u).Nu →ₗ[ℤ] B.T.dual.L :=
    { toFun := fun x => ⟨B.Bk u x.1,
        (bessel_map_maps_Nu_into_RRDual B u).1 ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add (B.Bk u) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul (B.Bk u) c x.1) }
  ((dualRealizeEquiv B.T).toLinearMap.comp bkZ).comp (nuRealizeEquiv (B.Nu u)).symm.toLinearMap

lemma besselMapToAnchorHom_apply_realize (B : IteratedBesselMapBk K ι) (u : ι)
    (x : (B.Nu u).Nu) :
    ((besselMapToAnchorHom B u (nuRealizeEquiv (B.Nu u) x) : B.T.dualAnchor.L) :
        B.T.dualAnchor.E) =
      realizeHLat B.T.dual.b B.T.dual.X (B.Bk u x.1) := by
  dsimp only [besselMapToAnchorHom, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  rw [(nuRealizeEquiv (B.Nu u)).symm_apply_apply x]
  rfl

lemma besselMapToAnchorHom_injective (B : IteratedBesselMapBk K ι) (u : ι)
    (hinj : Set.InjOn (B.Bk u) ((B.Nu u).Nu : Set (B.Nu u).M.V)) :
    Function.Injective (besselMapToAnchorHom B u) := by
  intro z₁ z₂ heq
  let eSrc := nuRealizeEquiv (B.Nu u)
  let eDst := dualRealizeEquiv B.T
  have h1 : eDst ⟨B.Bk u (eSrc.symm z₁).1,
      (bessel_map_maps_Nu_into_RRDual B u).1 ⟨(eSrc.symm z₁).1, (eSrc.symm z₁).2, rfl⟩⟩ =
      eDst ⟨B.Bk u (eSrc.symm z₂).1,
        (bessel_map_maps_Nu_into_RRDual B u).1 ⟨(eSrc.symm z₂).1, (eSrc.symm z₂).2, rfl⟩⟩ := heq
  have h2 := congrArg (fun w : B.T.dual.L => w.1) (eDst.injective h1)
  have h3 := hinj (eSrc.symm z₁).2 (eSrc.symm z₂).2 h2
  exact eSrc.symm.injective (Subtype.ext h3)

lemma besselMapToAnchorHom_norm_le (B : IteratedBesselMapBk K ι) (u : ι)
    (z : (B.Nu u).toHLatAnchor.L) :
    ‖((besselMapToAnchorHom B u z : B.T.dualAnchor.L) : B.T.dualAnchor.E)‖ ≤
      B.C_op u * ‖(z : (B.Nu u).toHLatAnchor.E)‖ := by
  obtain ⟨x, rfl⟩ := (nuRealizeEquiv (B.Nu u)).surjective z
  rw [besselMapToAnchorHom_apply_realize B u x, nuRealizeEquiv_apply]
  exact B.arch_bound u x.1

/-- **Ramified Bost Slope Bound on `Nu u → RR^∨` (`bessel_map_ramified_bost_ineq`)**:
when `B.Bk u` is injective on `Nu u` and divisible by a positive integer `D_div` inside `RR^∨`,
`(Nu u).toHLatAnchor.slope + log D_div ≤ T.dualAnchor.muMax + log (C_op u)`
(matching `Stage14Contracts.M2HLatBostContract.joint_a_ramified_holds`). -/
theorem bessel_map_ramified_bost_ineq (B : IteratedBesselMapBk K ι) (u : ι)
    (hinj : Set.InjOn (B.Bk u) ((B.Nu u).Nu : Set (B.Nu u).M.V))
    (D_div : ℕ) (hD_div : 0 < D_div)
    (hDiv : ∀ x ∈ (B.Nu u).Nu, ∃ y ∈ B.T.dual.L, B.Bk u x = (D_div : ℤ) • y) :
    (B.Nu u).toHLatAnchor.slope + Real.log (D_div : ℝ) ≤
      B.T.dualAnchor.muMax + Real.log (B.C_op u) := by
  have hDivZ : ∀ z : (B.Nu u).toHLatAnchor.L,
      ∃ w : B.T.dualAnchor.L, besselMapToAnchorHom B u z = (D_div : ℤ) • w := by
    intro z
    obtain ⟨x, rfl⟩ := (nuRealizeEquiv (B.Nu u)).surjective z
    obtain ⟨y, hyL, hy⟩ := hDiv x.1 x.2
    refine ⟨dualRealizeEquiv B.T ⟨y, hyL⟩, ?_⟩
    apply Subtype.ext
    change ((besselMapToAnchorHom B u (nuRealizeEquiv (B.Nu u) x) : B.T.dualAnchor.L) :
        B.T.dualAnchor.E) =
      (D_div : ℤ) • ((dualRealizeEquiv B.T ⟨y, hyL⟩ : B.T.dualAnchor.L) : B.T.dualAnchor.E)
    rw [besselMapToAnchorHom_apply_realize B u x, dualRealizeEquiv_apply, hy, map_zsmul]
    rfl
  exact bost_slope_inequality_divisible (B.Nu u).toHLatAnchor.L B.T.dualAnchor.L
    (B.Nu u).toHLatAnchor.ne_bot (besselMapToAnchorHom B u) (B.C_op u) D_div hD_div
    (besselMapToAnchorHom_injective B u hinj) (besselMapToAnchorHom_norm_le B u) hDivZ

/-- **Normalized Number-Field Bost Slope Inequality for `Nu u → RR^∨`**:
`(Nu u).toHLat.mu + 2 * log D_div ≤ 2 * T.dualAnchor.muMax - log 2 + logDiscDivDeg K + 2 * log (C_op u)`. -/
theorem bessel_map_ramified_bost_ineq_normalized (B : IteratedBesselMapBk K ι) (u : ι)
    (hinj : Set.InjOn (B.Bk u) ((B.Nu u).Nu : Set (B.Nu u).M.V))
    (D_div : ℕ) (hD_div : 0 < D_div)
    (hDiv : ∀ x ∈ (B.Nu u).Nu, ∃ y ∈ B.T.dual.L, B.Bk u x = (D_div : ℤ) • y) :
    (B.Nu u).toHLat.mu + 2 * Real.log (D_div : ℝ) ≤
      2 * B.T.dualAnchor.muMax - Real.log 2 + logDiscDivDeg K + 2 * Real.log (B.C_op u) := by
  have hb := bessel_map_ramified_bost_ineq B u hinj D_div hD_div hDiv
  have hmu : (B.Nu u).toHLat.mu =
      2 * (B.Nu u).toHLatAnchor.slope - Real.log 2 + logDiscDivDeg K := rfl
  linarith

/-- **Rank Bound & Arakelov Vanishing for Divisible Bessel Morphisms**:
if `log D_div > M_max + log (C_op u)` with `T.dualAnchor.muMax ≤ M_max` and
`covol (Nu u) ≤ exp C_arch`, then `rk (Nu u) ≤ C_arch / (log D_div - M_max - log (C_op u))`. -/
theorem bessel_map_rank_bound_of_divisible (B : IteratedBesselMapBk K ι) (u : ι)
    (hinj : Set.InjOn (B.Bk u) ((B.Nu u).Nu : Set (B.Nu u).M.V))
    (D_div : ℕ) (hD_div : 0 < D_div)
    (hDiv : ∀ x ∈ (B.Nu u).Nu, ∃ y ∈ B.T.dual.L, B.Bk u x = (D_div : ℤ) • y)
    {M_max C_arch : ℝ} (hMmax : B.T.dualAnchor.muMax ≤ M_max)
    (hCov : (B.Nu u).toHLatAnchor.covol ≤ Real.exp C_arch)
    (hGap : 0 < Real.log (D_div : ℝ) - M_max - Real.log (B.C_op u)) :
    ((B.Nu u).toHLatAnchor.rk : ℝ) ≤
      C_arch / (Real.log (D_div : ℝ) - M_max - Real.log (B.C_op u)) := by
  have hDivZ : ∀ z : (B.Nu u).toHLatAnchor.L,
      ∃ w : B.T.dualAnchor.L, besselMapToAnchorHom B u z = (D_div : ℤ) • w := by
    intro z
    obtain ⟨x, rfl⟩ := (nuRealizeEquiv (B.Nu u)).surjective z
    obtain ⟨y, hyL, hy⟩ := hDiv x.1 x.2
    refine ⟨dualRealizeEquiv B.T ⟨y, hyL⟩, ?_⟩
    apply Subtype.ext
    change ((besselMapToAnchorHom B u (nuRealizeEquiv (B.Nu u) x) : B.T.dualAnchor.L) :
        B.T.dualAnchor.E) =
      (D_div : ℤ) • ((dualRealizeEquiv B.T ⟨y, hyL⟩ : B.T.dualAnchor.L) : B.T.dualAnchor.E)
    rw [besselMapToAnchorHom_apply_realize B u x, dualRealizeEquiv_apply, hy, map_zsmul]
    rfl
  exact bost_rank_bound_of_divisible (B.Nu u).toHLatAnchor.L B.T.dualAnchor.L
    (besselMapToAnchorHom B u) (B.C_op u) M_max C_arch D_div hD_div
    (besselMapToAnchorHom_injective B u hinj) (besselMapToAnchorHom_norm_le B u) hDivZ
    hMmax hCov hGap

/-- Alignment with `Stage14Contracts.M2HLatBostContract.joint_a_ramified_holds`:
the Bost contract's `joint_a_ramified_holds` field applies directly to `besselMapToAnchorHom B u`. -/
theorem bessel_map_discharges_contract_ramified (M2 : M2HLatBostContract)
    (B : IteratedBesselMapBk K ι) (u : ι)
    (hinj : Set.InjOn (B.Bk u) ((B.Nu u).Nu : Set (B.Nu u).M.V))
    (D_div : ℕ) (hD_div : 0 < D_div)
    (hDiv : ∀ x ∈ (B.Nu u).Nu, ∃ y ∈ B.T.dual.L, B.Bk u x = (D_div : ℤ) • y) :
    (B.Nu u).toHLatAnchor.slope + Real.log (D_div : ℝ) ≤
      B.T.dualAnchor.muMax + Real.log (B.C_op u) := by
  refine M2.joint_a_ramified_holds (B.Nu u).toHLatAnchor B.T.dualAnchor
    (besselMapToAnchorHom B u) (B.C_op u) D_div hD_div
    (besselMapToAnchorHom_injective B u hinj) (besselMapToAnchorHom_norm_le B u) ?_
  intro z
  obtain ⟨x, rfl⟩ := (nuRealizeEquiv (B.Nu u)).surjective z
  obtain ⟨y, hyL, hy⟩ := hDiv x.1 x.2
  refine ⟨dualRealizeEquiv B.T ⟨y, hyL⟩, ?_⟩
  apply Subtype.ext
  change ((besselMapToAnchorHom B u (nuRealizeEquiv (B.Nu u) x) : B.T.dualAnchor.L) :
      B.T.dualAnchor.E) =
    (D_div : ℤ) • ((dualRealizeEquiv B.T ⟨y, hyL⟩ : B.T.dualAnchor.L) : B.T.dualAnchor.E)
  rw [besselMapToAnchorHom_apply_realize B u x, dualRealizeEquiv_apply, hy, map_zsmul]
  rfl

end BesselMapsNuIntoRRDual

/-! ## Section 5: `bessel_id_unitary_factorization` & `Stage2GramFrameFiber` Alignment -/

section BesselUnitaryFactorizationSection

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Concrete Algebraic Bessel Period Matrix (`besselPeriodMatrix`)**:
at an infinite place `v₀ : InfinitePlace K`, the matrix `MBk u : Matrix T.RR.ι (Fin (r u)) ℂ`
whose `(k, j)` entry is `v₀.embedding (Bk u (bNu u j) (T.RR.b k))` for a `K`-basis `bNu u` of
`Nu u`'s ambient space (with `bNu u j ∈ (Nu u).Nu`). -/
def besselPeriodMatrix (B : IteratedBesselMapBk K ι) (v₀ : InfinitePlace K)
    (r : ι → ℕ) (bNu : ∀ u, Fin (r u) → (B.Nu u).M.V) :
    ∀ u : ι, Matrix B.T.RR.ι (Fin (r u)) ℂ :=
  fun u k j => v₀.embedding (B.Bk u (bNu u j) (B.T.RR.b k))

/-- Every entry of `besselPeriodMatrix` on integral basis elements `bNu u j ∈ (Nu u).Nu` and
`T.RR.b k ∈ T.RR.L` is the `v₀`-embedding of an algebraic integer in `𝓞 K`. -/
theorem besselPeriodMatrix_entries_integral (B : IteratedBesselMapBk K ι) (v₀ : InfinitePlace K)
    (r : ι → ℕ) (bNu : ∀ u, Fin (r u) → (B.Nu u).M.V)
    (hbNu : ∀ u j, bNu u j ∈ (B.Nu u).Nu) (hbRR : ∀ k, B.T.RR.b k ∈ B.T.RR.L)
    (u : ι) (k : B.T.RR.ι) (j : Fin (r u)) :
    ∃ a : 𝓞 K, besselPeriodMatrix B v₀ r bNu u k j = v₀.embedding (algebraMap (𝓞 K) K a) := by
  obtain ⟨a, ha⟩ := bessel_pairing_mem_ringOfIntegers B u (hbNu u j) (hbRR k)
  exact ⟨a, by simp [besselPeriodMatrix, ha]⟩

/-- **Unitary Block Factorization (`bessel_id_unitary_factorization`)**:
given an ambient Hilbert space `HH` of dimension `|(T.RR.ι) ⊕ κ₁|`, test-vector space `EE` with
orthonormal basis `oE : OrthonormalBasis T.RR.ι ℂ EE` and basis `bE : Module.Basis T.RR.ι ℂ EE`,
isometric conjugate-linear map `sEE : EE → HH`, Bessel/theta Hilbert spaces `Cu u` and `Mu u`
with isometric inclusions `iotaC u : Mu u →ₗ[ℂ] Cu u`, Bessel-theta operators `Pu u : Cu u →L[ℂ] HH`,
unitary intertwiners `V : EE ≃ₗᵢ[ℂ] EE` and `U u : Mu u ≃ₗᵢ[ℂ] Mu u`, and unfolding scalars
`a u ≠ 0` satisfying the Bessel intertwining identity against `besselPeriodMatrix B v₀ r bNu`,
constructs a concrete `Stage14M2_BesselSchurBlock.IsometryBlockFactorization ι B.T.RR.ι κ₁`! -/
theorem bessel_id_unitary_factorization
    (B : IteratedBesselMapBk K ι) (v₀ : InfinitePlace K)
    (r : ι → ℕ) (bNu : ∀ u, Fin (r u) → (B.Nu u).M.V)
    {κ₁ : Type} [Fintype κ₁] [DecidableEq κ₁]
    (HH : Type) [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [FiniteDimensional ℂ HH]
    (hHH_dim : Module.finrank ℂ HH = Fintype.card (B.T.RR.ι ⊕ κ₁))
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (oE : OrthonormalBasis B.T.RR.ι ℂ EE)
    (bE : Module.Basis B.T.RR.ι ℂ EE)
    (sEE : EE → HH)
    (hsEE_inner : ∀ x y : EE, ⟪sEE x, sEE y⟫_ℂ = ⟪y, x⟫_ℂ)
    (d : ι → ℕ)
    (Cu : ι → Type) [∀ u, NormedAddCommGroup (Cu u)] [∀ u, InnerProductSpace ℂ (Cu u)]
    [∀ u, FiniteDimensional ℂ (Cu u)]
    (eC : ∀ u, OrthonormalBasis (Fin (d u)) ℂ (Cu u))
    (Mu : ι → Type) [∀ u, NormedAddCommGroup (Mu u)] [∀ u, InnerProductSpace ℂ (Mu u)]
    [∀ u, FiniteDimensional ℂ (Mu u)]
    (oM : ∀ u, OrthonormalBasis (Fin (r u)) ℂ (Mu u))
    (bN : ∀ u, Module.Basis (Fin (r u)) ℂ (Mu u))
    (iotaC : ∀ u, Mu u →ₗ[ℂ] Cu u)
    (hiota : ∀ u (φ ψ : Mu u), ⟪iotaC u φ, iotaC u ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ)
    (Pu : ∀ u, Cu u →L[ℂ] HH)
    (c0 : ι → ℝ) (hc0 : ∀ u, 0 ≤ c0 u)
    (V : EE ≃ₗᵢ[ℂ] EE)
    (U : ∀ u, Mu u ≃ₗᵢ[ℂ] Mu u)
    (a : ι → ℂ) (ha : ∀ u, a u ≠ 0)
    (hIntertwine : ∀ u (k : B.T.RR.ι) (j : Fin (r u)),
      ⟪sEE (V (oE k)), Pu u (iotaC u (U u (oM u j)))⟫_ℂ =
        (a u)⁻¹ * ∑ k' : B.T.RR.ι, ∑ j' : Fin (r u),
          bE.repr (V (oE k)) k' * besselPeriodMatrix B v₀ r bNu u k' j' *
            (bN u).repr (U u (oM u j)) j')
    (ε : ℂ →+* ℂ) (hε : IsIdOrConj ε) :
    Nonempty (IsometryBlockFactorization ι B.T.RR.ι κ₁) :=
  besselId_to_isometryBlockFactorization HH hHH_dim EE oE bE sEE hsEE_inner
    d r Cu eC Mu oM bN iotaC hiota Pu c0 hc0 (besselPeriodMatrix B v₀ r bNu) V U a ha hIntertwine ε hε

/-- Exact top-block factorization, Loewner domination, and Hilbert–Schmidt defect contraction for
any `IsometryBlockFactorization ι B.T.RR.ι κ₁`. -/
theorem bessel_factorization_loewner_and_hsSq {κ₁ : Type} [Fintype κ₁]
    (_B : IteratedBesselMapBk K ι)
    (F : IsometryBlockFactorization ι _B.T.RR.ι κ₁)
    (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (∀ u (k : _B.T.RR.ι) (j : Fin (F.r u)),
      ((F.M.pmatConj F.ε u) * F.Vr u) (Sum.inl k) j =
        (F.Y'⁻¹ * (F.MBk u).map F.ε * F.Y u) k j) ∧
    ((LatticeFrame.frameOp F.compressedMat ga).PosSemidef ∧
      (LatticeFrame.frameOp (F.M.pmatFin F.ε) ga -
        LatticeFrame.frameOp F.compressedMat ga).PosSemidef) ∧
    (∀ u u', LatticeFrame.hsSq (LatticeFrame.gramCross F.compressedMat ga u u') ≤
      LatticeFrame.hsSq (LatticeFrame.gramCross (F.M.pmatFin F.ε) ga u u')) ∧
    (∀ u, LatticeFrame.hsSq (LatticeFrame.gramDiag F.compressedMat ga u - 1) ≤
      LatticeFrame.hsSq (LatticeFrame.gramDiag (F.M.pmatFin F.ε) ga u - 1)) :=
  ⟨F.factor_eq, F.frameOp_loewner ga hga, F.hsSq_gramCross_compress_le ga,
    F.hsSq_gramDiag_sub_one_compress_le ga⟩

/-- **Top-Block Kernel Projection (`T_proj` Bridge for `FrameRealCompile`)**:
every vector `v : EuclideanSpace ℂ (Fin (F.r u))` with `(F.Y u) *ᵥ v ∈ ker ((F.MBk u).map F.ε)`
has zero top `B.T.RR.ι`-projection under `F.compressedMat u`. -/
theorem bessel_factorization_top_block_kernel_proj {κ₁ : Type} [Fintype κ₁]
    (B : IteratedBesselMapBk K ι)
    (F : IsometryBlockFactorization ι B.T.RR.ι κ₁)
    (u : ι) (v : EuclideanSpace ℂ (Fin (F.r u)))
    (hker : ((F.MBk u).map F.ε) *ᵥ (F.Y u *ᵥ (fun j => v j)) = 0) (k : B.T.RR.ι) :
    (Matrix.toEuclideanLin (Matrix.reindex (Fintype.equivFin (B.T.RR.ι ⊕ κ₁)).symm (Equiv.refl _)
      (F.compressedMat u)) v) (Sum.inl k) = 0 := by
  rw [F.top_block_apply_eq u v k, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  simp

/-- **Direct Compilation to `Stage2ThetaWire.Stage2GramFrameFiber` & `SlopeIneq` Discharge**:
given a `BesselGramSpectralBundle` built over `B.T.RR.ι`, source HN slopes `y`, target `RR^∨`
slopes `x` bounded below by `muMinCC`, and filtration subspaces `Nτ`, `T_sub`, builds
`Stage2GramFrameFiber` and discharges `BostSlopeFiber.SlopeIneq` for `M2FiberCert.gramFiber`. -/
abbrev bessel_integrality_to_stage2GramFrameFiber {κ₁ : Type} [Fintype κ₁] [DecidableEq κ₁]
    (B_int : IteratedBesselMapBk K ι)
    (B_spec : BesselGramSpectralBundle ι B_int.T.RR.ι κ₁)
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (hsg_bar : B_spec.P.sg ≤ sgBar) (hsgBar_le : sgBar ≤ 1 / 20)
    (he0_bar : B_spec.P.e0 ≤ e0Bar)
    (hde_bar : B_spec.P.de ≤ deBar) (hdeBar_le : deBar ≤ 1 / 4)
    (hδ_bar : B_spec.P.δ ≤ delBar) (hdelBar_le : delBar ≤ 1 / 2)
    (hκ_pos : 0 < Fintype.card B_int.T.RR.ι) (hcardW : 1 ≤ cardW)
    (y : ∀ u, Fin (B_spec.F.r u) → ℝ)
    (hy_mean : (∑ u, (B_spec.F.r u : ℝ)) * s ≤ ∑ u, ∑ j, y u j)
    (hy_top : ∀ u j, y u j ≤ s + uF)
    (x : Fin (Fintype.card B_int.T.RR.ι) → ℝ)
    (hx_min : ∀ j, muMinCC ≤ x j)
    (Nτ : ℝ → ∀ u, Submodule ℂ (EuclideanSpace ℂ (Fin (B_spec.F.r u))))
    (T_sub : ℝ → Submodule ℂ (EuclideanSpace ℂ B_int.T.RR.ι))
    (hNτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u,
      (B_spec.F.r u : ℝ) - Module.finrank ℂ (Nτ τ u) ≤
        ((Finset.univ.filter (fun j => y u j < s - τ)).card : ℝ))
    (hT_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u (v : EuclideanSpace ℂ (Fin (B_spec.F.r u))),
      v ∈ Nτ τ u →
      (WithLp.linearEquiv 2 ℂ (B_int.T.RR.ι → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (B_int.T.RR.ι ⊕ κ₁)).symm (Equiv.refl _)
            (B_spec.F.compressedMat u)) v) (Sum.inl k)) ∈ T_sub τ)
    (hT_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => x j < s - Real.log (cardW : ℝ) - τ)).card : ℝ) ≤
        (Fintype.card B_int.T.RR.ι : ℝ) - Module.finrank ℂ (T_sub τ)) :
    Stage2ThetaWire.Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar :=
  toStage2GramFrameFiber B_spec hsg_bar hsgBar_le he0_bar hde_bar hdeBar_le hδ_bar hdelBar_le
    hκ_pos hcardW y hy_mean hy_top x hx_min Nτ T_sub hNτ_corank hT_proj hT_tail

theorem bessel_integrality_discharges_bost_slope {κ₁ : Type} [Fintype κ₁] [DecidableEq κ₁]
    (B_int : IteratedBesselMapBk K ι)
    (B_spec : BesselGramSpectralBundle ι B_int.T.RR.ι κ₁)
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (huF0 : 0 ≤ uF)
    (hsg_bar : B_spec.P.sg ≤ sgBar) (hsgBar_le : sgBar ≤ 1 / 20)
    (he0_bar : B_spec.P.e0 ≤ e0Bar)
    (hde_bar : B_spec.P.de ≤ deBar) (hdeBar_le : deBar ≤ 1 / 4)
    (hδ_bar : B_spec.P.δ ≤ delBar) (hdelBar_le : delBar ≤ 1 / 2)
    (hκ_pos : 0 < Fintype.card B_int.T.RR.ι) (hcardW : 1 ≤ cardW)
    (y : ∀ u, Fin (B_spec.F.r u) → ℝ)
    (hy_mean : (∑ u, (B_spec.F.r u : ℝ)) * s ≤ ∑ u, ∑ j, y u j)
    (hy_top : ∀ u j, y u j ≤ s + uF)
    (x : Fin (Fintype.card B_int.T.RR.ι) → ℝ)
    (hx_min : ∀ j, muMinCC ≤ x j)
    (Nτ : ℝ → ∀ u, Submodule ℂ (EuclideanSpace ℂ (Fin (B_spec.F.r u))))
    (T_sub : ℝ → Submodule ℂ (EuclideanSpace ℂ B_int.T.RR.ι))
    (hNτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u,
      (B_spec.F.r u : ℝ) - Module.finrank ℂ (Nτ τ u) ≤
        ((Finset.univ.filter (fun j => y u j < s - τ)).card : ℝ))
    (hT_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u (v : EuclideanSpace ℂ (Fin (B_spec.F.r u))),
      v ∈ Nτ τ u →
      (WithLp.linearEquiv 2 ℂ (B_int.T.RR.ι → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (B_int.T.RR.ι ⊕ κ₁)).symm (Equiv.refl _)
            (B_spec.F.compressedMat u)) v) (Sum.inl k)) ∈ T_sub τ)
    (hT_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => x j < s - Real.log (cardW : ℝ) - τ)).card : ℝ) ≤
        (Fintype.card B_int.T.RR.ι : ℝ) - Module.finrank ℂ (T_sub τ)) :
    (bessel_integrality_to_stage2GramFrameFiber B_int B_spec hsg_bar hsgBar_le he0_bar hde_bar
      hdeBar_le hδ_bar hdelBar_le hκ_pos hcardW y hy_mean hy_top x hx_min Nτ T_sub hNτ_corank
      hT_proj hT_tail).toBostFiber.SlopeIneq :=
  bost_slope_ineq_of_bessel_bundle B_spec huF0 hsg_bar hsgBar_le he0_bar hde_bar hdeBar_le
    hδ_bar hdelBar_le hκ_pos hcardW y hy_mean hy_top x hx_min Nτ T_sub hNτ_corank hT_proj hT_tail

end BesselUnitaryFactorizationSection

/-! ## Section 6: `capelli_determinant_integrality_on_RR` — Capelli Determinant Integrality -/

section CapelliDeterminantIntegralitySection

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- Any `K`-linear endomorphism `γ` stabilizing `T.RR.L` has dual map `γ.dualMap` stabilizing
`(T.dual).L = dualLatO T.RR.L`. -/
theorem dualOp_preserves_dualLatO (T : TargetDualHLatRR K)
    (γ : Module.End K T.RR.V) (hγ : ∀ x ∈ T.RR.L, γ x ∈ T.RR.L) :
    ∀ f ∈ T.dual.L, γ.dualMap f ∈ T.dual.L := by
  intro f hf x hx
  let f' : Module.Dual K T.RR.V := f
  change f' (γ x) ∈ Set.range (algebraMap (𝓞 K) K)
  exact hf (γ x) (hγ x hx)

/-- Matrix transpose identity for `γ.dualMap` in the dual basis `T.RR.b.dualBasis`. -/
theorem toMatrix_dualMap_eq_transpose (T : TargetDualHLatRR K) (γ : Module.End K T.RR.V) :
    LinearMap.toMatrix T.RR.b.dualBasis T.RR.b.dualBasis γ.dualMap =
      (LinearMap.toMatrix T.RR.b T.RR.b γ)ᵀ := by
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp [Basis.dualBasis_repr, LinearMap.dualMap_apply]

/-- Determinant invariance under duality: `LinearMap.det γ.dualMap = LinearMap.det γ`. -/
theorem det_dualMap_eq (T : TargetDualHLatRR K) (γ : Module.End K T.RR.V) :
    LinearMap.det γ.dualMap = LinearMap.det γ := by
  rw [← LinearMap.det_toMatrix T.RR.b.dualBasis, ← LinearMap.det_toMatrix T.RR.b,
    toMatrix_dualMap_eq_transpose, Matrix.det_transpose]

/-- Reindexing `V` to `Fin N → K` along a basis `b` and equivalence `e : ι ≃ Fin N`. -/
private def latticeToFinCoord {V ι : Type*} [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (e : ι ≃ Fin (Fintype.card ι)) :
    V ≃ₗ[K] (Fin (Fintype.card ι) → K) :=
  (b.repr.trans (Finsupp.linearEquivFunOnFinite K K ι)).trans
    (LinearEquiv.funCongrLeft K K e.symm)

private lemma latticeToFinCoord_apply {V ι : Type*} [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (e : ι ≃ Fin (Fintype.card ι)) (v : V) (j : Fin (Fintype.card ι)) :
    latticeToFinCoord (K := K) b e v j = b.repr v (e.symm j) := rfl

/-- **Capelli / Lattice-Stabilizing Determinant Integrality on `RR`**:
if `γ : Module.End K T.RR.V` stabilizes `T.RR.L`, then `IsIntegral ℤ (LinearMap.det γ)`,
`IsIntegral ℤ (LinearMap.det γ.dualMap)`, and `LinearMap.det γ ∈ 𝓞 K`. -/
theorem isIntegral_det_of_preserves_RR (T : TargetDualHLatRR K)
    (γ : Module.End K T.RR.V) (hγ : ∀ x ∈ T.RR.L, γ x ∈ T.RR.L) :
    IsIntegral ℤ (LinearMap.det γ) ∧
    IsIntegral ℤ (LinearMap.det γ.dualMap) ∧
    LinearMap.det γ ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  haveI : Module.Finite K T.RR.V := Module.Finite.of_basis T.RR.b
  let N := Fintype.card T.RR.ι
  let e : T.RR.ι ≃ Fin N := Fintype.equivFin T.RR.ι
  let Φ : T.RR.V ≃ₗ[K] (Fin N → K) := latticeToFinCoord T.RR.b e
  let ΦO : T.RR.V →ₗ[𝓞 K] (Fin N → K) := Φ.toLinearMap.restrictScalars (𝓞 K)
  let L_fin : Submodule (𝓞 K) (Fin N → K) := T.RR.L.map ΦO
  have hfg : L_fin.FG := T.RR_good.2.1.map ΦO
  have hspan : Submodule.span K (L_fin : Set (Fin N → K)) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hx : Φ.symm y ∈ Submodule.span K (T.RR.L : Set T.RR.V) := by
      rw [T.RR_good.2.2]; trivial
    have himg : Φ (Φ.symm y) ∈ (Submodule.span K (T.RR.L : Set T.RR.V)).map Φ.toLinearMap :=
      Submodule.mem_map_of_mem hx
    rw [LinearEquiv.apply_symm_apply, Submodule.map_span] at himg
    have hset : Φ.toLinearMap '' (T.RR.L : Set T.RR.V) = (L_fin : Set (Fin N → K)) := by
      ext z; simp [L_fin, ΦO]
    rwa [hset] at himg
  let M : Matrix (Fin N) (Fin N) K :=
    Matrix.reindex e e (LinearMap.toMatrix T.RR.b T.RR.b γ)
  have hM_mulVec : ∀ x : T.RR.V, M.mulVec (Φ x) = Φ (γ x) := by
    intro x
    ext j
    rw [Matrix.mulVec, dotProduct, latticeToFinCoord_apply]
    have hrepr : T.RR.b.repr (γ x) (e.symm j) =
        ∑ i : T.RR.ι, LinearMap.toMatrix T.RR.b T.RR.b γ (e.symm j) i * T.RR.b.repr x i := by
      rw [← LinearMap.toMatrix_mulVec_repr T.RR.b T.RR.b γ x]
      rfl
    have hLHS : (∑ k : Fin N, M j k * (Φ x) k) =
        ∑ k : Fin N, M j k * T.RR.b.repr x (e.symm k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [latticeToFinCoord_apply]
    rw [hLHS, hrepr]
    refine Fintype.sum_equiv e.symm _ _ fun k => ?_
    simp [M, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hM_pres : ∀ v ∈ L_fin, M.mulVec v ∈ L_fin := by
    rintro _ ⟨x, hx, rfl⟩
    change M.mulVec (Φ x) ∈ L_fin
    rw [hM_mulVec x]
    exact ⟨γ x, hγ x hx, rfl⟩
  have hM_int : IsIntegral ℤ M.det :=
    isIntegral_det_of_preserves_lattice L_fin hfg hspan M hM_pres
  have hdet_eq : M.det = LinearMap.det γ := by
    rw [Matrix.det_reindex_self, LinearMap.det_toMatrix]
  rw [hdet_eq] at hM_int
  have hOK_int : IsIntegral (𝓞 K) (LinearMap.det γ) := hM_int.tower_top
  have hmem : LinearMap.det γ ∈ Set.range (algebraMap (𝓞 K) K) :=
    (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 K) (K := K)).mp hOK_int
  refine ⟨hM_int, ?_, hmem⟩
  rwa [det_dualMap_eq T γ]

/-- Any matrix `γ : Matrix (Fin N) (Fin N) K` that is integral over `ℤ` (e.g. entries in `𝓞 K`
or integral representation) has `IsIntegral ℤ γ.det` and `γ.det ∈ 𝓞 K`. -/
theorem capelli_isIntegral_det_of_integral_matrix {N : ℕ}
    (γ : Matrix (Fin N) (Fin N) K) (h : IsIntegral ℤ γ) :
    IsIntegral ℤ γ.det ∧ γ.det ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hd : IsIntegral ℤ γ.det := isIntegral_det_of_isIntegral γ h
  have hdO : IsIntegral (𝓞 K) γ.det := hd.tower_top
  exact ⟨hd, (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 K) (K := K)).mp hdO⟩

/-- Any real linear operator preserving a nondegenerate bilinear form on the realification of
`RR` has `(det f)^2 = 1`, hence `IsIntegral ℤ (LinearMap.det f)`. -/
theorem capelli_bilin_pres_det_sq_one_on_RR
    {V_R : Type*} [AddCommGroup V_R] [Module ℝ V_R] [FiniteDimensional ℝ V_R]
    (B : LinearMap.BilinForm ℝ V_R) (hB : B.Nondegenerate)
    (f : V_R →ₗ[ℝ] V_R) (hf : ∀ x y : V_R, B (f x) (f y) = B x y) :
    (LinearMap.det f) ^ 2 = 1 ∧ IsIntegral ℤ (LinearMap.det f) := by
  have hsq : (LinearMap.det f) ^ 2 = 1 := det_sq_eq_one_of_preserves_bilin B hB f hf
  refine ⟨hsq, ?_⟩
  refine ⟨Polynomial.X ^ 2 - 1, Polynomial.monic_X_pow_sub_C 1 (by norm_num), ?_⟩
  simp [hsq]

/-- **2×2 Holomorphic Quantum-Determinant Integrality on `RR`**:
when a `𝔤𝔩₂(ℂ)` action `E` on a lowest-weight vector `φ` of integer weight `k : ℤ` satisfies the
holomorphic highest/lowest-weight relations of `CapelliCore.qdet_two_holomorphic_eigenvalue`
at an integer or half-integer parameter `u`, `qdet E (u + 1/2)` acts by a rational/integral scalar! -/
theorem capelli_qdet_two_integral_on_RR {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E : Fin 2 → Fin 2 → Module.End ℂ V) (hE : GlRel E) (k : ℤ) (hk_odd : Odd k) (φ : V)
    (h1 : E 0 0 φ + E 1 1 φ = 0)
    (h2 : E 0 1 φ - E 1 0 φ = (Complex.I * (k : ℂ)) • φ)
    (h3 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (m : ℤ) :
    ∃ z : ℤ, qdet E ((m : ℂ) + 1 / 2) φ = (z : ℂ) • φ := by
  obtain ⟨t, ht⟩ := hk_odd
  have hq := qdet_two_holomorphic_eigenvalue E hE (k : ℂ) φ h1 h2 h3 (m : ℂ)
  refine ⟨(m + t) * (m - t), ?_⟩
  rw [hq]
  congr 1
  have hkC : (k : ℂ) = 2 * (t : ℂ) + 1 := by exact_mod_cast ht
  rw [hkC]
  push_cast
  ring

/-- **Capelli Determinant Integrality on `RR` & `RR^∨` (`capelli_determinant_integrality_on_RR`)**:
unifies:
1. Integral determinant (`IsIntegral ℤ`, `∈ 𝓞 K`, `la.valuation ≤ 1` at all height-one primes)
   for any `RR`-stabilizing (and hence `RR^∨`-stabilizing) operator `γ` and its dual `γ.dualMap`,
2. Entrywise-integral matrix determinant valuation bound (`valuation_det_le_one_of_entries_le_one`),
3. Iwahori Newton-polygon charpoly coefficient valuation (`charpoly_coeff_valuation`) & unit
   determinant criterion (`valuation_det_eq_one_iff_diag_eq_one`),
4. Archimedean Capelli determinant norm bound (`det_norm_le`) at every infinite place `v`, and
5. Capelli trace centrality in `U(𝔤𝔩_N(ℂ))` (`e_comm_trace_capelliMatrix_pow`). -/
theorem capelli_determinant_integrality_on_RR
    (T : TargetDualHLatRR K) (γ : Module.End K T.RR.V)
    (hγ : ∀ x ∈ T.RR.L, γ x ∈ T.RR.L)
    {N : ℕ} (M_mat : Matrix (Fin N) (Fin N) K) (d_iw : Fin N → K)
    (la : HeightOneSpectrum (𝓞 K))
    (hM1 : ∀ i j, la.valuation K (M_mat i j) ≤ 1)
    (hM2 : ∀ i j, j < i → la.valuation K (M_mat i j) < 1)
    (hMdet : la.valuation K M_mat.det = 1)
    (hmono : StrictMono fun i => la.valuation K (d_iw i))
    (hd0 : ∀ i, d_iw i ≠ 0)
    {C_arch : ℝ} (v : InfinitePlace K)
    (hArch : ∀ i j, ‖v.embedding (LinearMap.toMatrix T.RR.b T.RR.b γ i j)‖ ≤ C_arch) :
    -- (1) `γ` and `γ.dualMap` stabilize `RR` and `RR^∨` with `ℤ`-integral / `𝓞 K` determinant
    ((∀ f ∈ T.dual.L, γ.dualMap f ∈ T.dual.L) ∧
     IsIntegral ℤ (LinearMap.det γ) ∧
     IsIntegral ℤ (LinearMap.det γ.dualMap) ∧
     LinearMap.det γ ∈ Set.range (algebraMap (𝓞 K) K) ∧
     (∀ la' : HeightOneSpectrum (𝓞 K), la'.valuation K (LinearMap.det γ) ≤ 1)) ∧
    -- (2) Iwahori / matrix valuation & Newton-polygon charpoly valuations
    (la.valuation K M_mat.det ≤ 1 ∧
     (la.valuation K M_mat.det = 1 ↔ ∀ i, la.valuation K (M_mat i i) = 1) ∧
     ∀ k ≤ N, la.valuation K ((Matrix.diagonal d_iw * M_mat).charpoly.coeff k) =
       ∏ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ i.val), la.valuation K (d_iw i)) ∧
    -- (3) Archimedean Capelli determinant norm bound at place `v`
    (‖v.embedding (LinearMap.det γ)‖ ≤
      ((Fintype.card T.RR.ι).factorial : ℝ) * C_arch ^ Fintype.card T.RR.ι) ∧
    -- (4) Capelli trace centrality in `U(𝔤𝔩_N(ℂ))`
    (∀ a b : Fin N, ∀ k : ℕ,
      CapelliCore.ueaGen a b * (capelliMatrix (n := N) ^ k).trace =
        (capelliMatrix (n := N) ^ k).trace * CapelliCore.ueaGen a b) := by
  obtain ⟨hInt, hIntDual, hmem⟩ := isIntegral_det_of_preserves_RR T γ hγ
  have hval_all : ∀ la' : HeightOneSpectrum (𝓞 K), la'.valuation K (LinearMap.det γ) ≤ 1 := by
    intro la'
    exact (mem_ringOfIntegers_of_forall_valuation_le_one (LinearMap.det γ)).mpr hmem la'
  have hArchDet : ‖v.embedding (LinearMap.det γ)‖ ≤
      ((Fintype.card T.RR.ι).factorial : ℝ) * C_arch ^ Fintype.card T.RR.ι := by
    rw [← LinearMap.det_toMatrix T.RR.b, RingHom.map_det]
    exact det_norm_le ((LinearMap.toMatrix T.RR.b T.RR.b γ).map v.embedding) hArch
  refine ⟨⟨dualOp_preserves_dualLatO T γ hγ, hInt, hIntDual, hmem, hval_all⟩,
    ⟨valuation_det_le_one_of_entries_le_one (la.valuation K) M_mat hM1,
     valuation_det_eq_one_iff_diag_eq_one (la.valuation K) M_mat hM1 hM2,
     fun k hk => charpoly_coeff_valuation (la.valuation K) N M_mat d_iw hM1 hM2 hMdet hmono hd0 hk⟩,
    hArchDet, fun a b k => e_comm_trace_capelliMatrix_pow a b k⟩

/-- **Capelli-Intertwining Bessel Stability**:
if a Capelli/Hecke operator `γ_RR` stabilizes `T.RR.L` and intertwines
`B.Bk u ∘ γ_Nu = γ_RR.dualMap ∘ B.Bk u`, then `B.Bk u (γ_Nu x) ∈ T.dual.L` for every
`x ∈ (B.Nu u).Nu`, and `LinearMap.det γ_RR ∈ 𝓞 K`. -/
theorem bessel_capelli_intertwine_integral
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : IteratedBesselMapBk K ι) (u : ι)
    (γ_RR : Module.End K B.T.RR.V) (hγ_RR : ∀ y ∈ B.T.RR.L, γ_RR y ∈ B.T.RR.L)
    (γ_Nu : (B.Nu u).M.V → (B.Nu u).M.V)
    (hInter : ∀ x, B.Bk u (γ_Nu x) = γ_RR.dualMap (B.Bk u x)) :
    (∀ x ∈ (B.Nu u).Nu, B.Bk u (γ_Nu x) ∈ B.T.dual.L) ∧
      LinearMap.det γ_RR ∈ Set.range (algebraMap (𝓞 K) K) := by
  refine ⟨fun x hx => ?_, (isIntegral_det_of_preserves_RR B.T γ_RR hγ_RR).2.2⟩
  rw [hInter x]
  exact dualOp_preserves_dualLatO B.T γ_RR hγ_RR _
    ((bessel_map_maps_Nu_into_RRDual B u).1 ⟨x, hx, rfl⟩)

end CapelliDeterminantIntegralitySection

/-! ## Section 7: Ready-for-`FrameRealCompile` Assembly & `Stage14Contracts` Alignment -/

section FrameRealCompileHandoff

/-- **Unified M2 Wave 2 `BesselIntegralityCompilePack`**:
collects the concrete target dual lattice `RR^∨`, iterated Bessel/theta morphisms `Bk` &
`OneMapIntoCC`, proved `Nu → RR^∨` integrality, unitary block factorization, `Stage2GramFrameFiber`
Bost-slope discharge, and Capelli determinant integrality ready for `Stage14M2_FrameRealCompile`. -/
structure BesselIntegralityCompilePack (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] (ι κ₁ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ₁] [DecidableEq κ₁] :
    Type 1 where
  bessel : IteratedBesselMapBk K ι
  factor : IsometryBlockFactorization ι bessel.T.RR.ι κ₁
  spectral : BesselGramSpectralBundle ι bessel.T.RR.ι κ₁
  spectral_F_eq : spectral.F = factor
  D_div : ι → ℕ
  D_div_pos : ∀ u, 0 < D_div u
  bk_inj : ∀ u, Set.InjOn (bessel.Bk u) ((bessel.Nu u).Nu : Set (bessel.Nu u).M.V)
  bk_divisible : ∀ u, ∀ x ∈ (bessel.Nu u).Nu,
    ∃ y ∈ bessel.T.dual.L, bessel.Bk u x = (D_div u : ℤ) • y

namespace BesselIntegralityCompilePack

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
  {ι κ₁ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ₁] [DecidableEq κ₁]

/-- Master verification theorem for `Stage14M2_FrameRealCompile` & `Stage14Contracts`:
from any `BesselIntegralityCompilePack`, proves simultaneously:
1. Exact duality slopes `(RR^∨).mu = -RR.mu`, `(RR^∨).muMax = -RR.muMin`, `(RR^∨).muMin = -RR.muMax`,
2. Proved `Nu u → RR^∨` integrality (`bessel_map_maps_Nu_into_RRDual`) and `OneMapIntoCC` integrality,
3. Ramified Bost slope inequality `(Nu u).toHLatAnchor.slope + log (D_div u) ≤ RR^∨.muMax + log (C_op u)`,
4. Unitary block factorization & Loewner/HS contractions for `ga u = (c0 u)⁻¹`, and
5. `FrameTraceRatio` and `FrameDiagDefect` bounds ready to construct `Stage2GramFrameFiber`. -/
theorem bessel_integrality_for_frame_real_compile
    (P : BesselIntegralityCompilePack K ι κ₁) :
    (P.bessel.T.dual.mu = -P.bessel.T.RR.mu ∧
     P.bessel.T.dual.muMax = -P.bessel.T.RR.muMin ∧
     P.bessel.T.dual.muMin = -P.bessel.T.RR.muMax) ∧
    (∀ u, (P.bessel.Nu u).Nu.map ((P.bessel.Bk u).restrictScalars (𝓞 K)) ≤
      P.bessel.T.dual.L) ∧
    (∀ x : ∀ u, (P.bessel.Nu u).M.V, (∀ u, x u ∈ (P.bessel.Nu u).Nu) →
      OneMapIntoCC P.bessel x ∈ P.bessel.T.dual.L) ∧
    (∀ u, (P.bessel.Nu u).toHLatAnchor.slope + Real.log (P.D_div u : ℝ) ≤
      P.bessel.T.dualAnchor.muMax + Real.log (P.bessel.C_op u)) ∧
    ((LatticeFrame.frameOp P.factor.compressedMat (fun u => (P.factor.M.c0 u)⁻¹)).PosSemidef ∧
     (LatticeFrame.frameOp (P.factor.M.pmatFin P.factor.ε) (fun u => (P.factor.M.c0 u)⁻¹) -
       LatticeFrame.frameOp P.factor.compressedMat (fun u => (P.factor.M.c0 u)⁻¹)).PosSemidef) ∧
    (LatticeFrame.FrameTraceRatio P.spectral.F.compressedMat
        (fun u => (P.spectral.F.M.c0 u)⁻¹) (5 * P.spectral.P.sg + 3 * Real.sqrt P.spectral.P.de) ∧
     LatticeFrame.FrameDiagDefect P.spectral.F.compressedMat
        (fun u => (P.spectral.F.M.c0 u)⁻¹) (2 * P.spectral.P.e0)) := by
  have hga : ∀ u, 0 ≤ (P.factor.M.c0 u)⁻¹ := fun u =>
    inv_nonneg.mpr (P.factor.M.c0_nonneg u)
  have hframe := P.spectral.frame_trace_and_diag_bounds
  refine ⟨P.bessel.T.dual_slope_duality,
    fun u => (bessel_map_maps_Nu_into_RRDual P.bessel u).1,
    oneMapIntoCC_maps_into_RRDual P.bessel,
    fun u => bessel_map_ramified_bost_ineq P.bessel u (P.bk_inj u) (P.D_div u)
      (P.D_div_pos u) (P.bk_divisible u),
    P.factor.frameOp_loewner (fun u => (P.factor.M.c0 u)⁻¹) hga,
    ⟨hframe.2.2.1, hframe.2.2.2⟩⟩

/-- Direct contract bridge: shows `P.bessel.T.dualAnchor` and `besselMapToAnchorHom P.bessel u`
satisfy `Stage14Contracts.M2HLatBostContract.joint_a_ramified_holds` for every `M2 : M2HLatBostContract`. -/
theorem discharges_m2Contract_ramified (P : BesselIntegralityCompilePack K ι κ₁)
    (M2 : M2HLatBostContract) (u : ι) :
    (P.bessel.Nu u).toHLatAnchor.slope + Real.log (P.D_div u : ℝ) ≤
      P.bessel.T.dualAnchor.muMax + Real.log (P.bessel.C_op u) :=
  bessel_map_discharges_contract_ramified M2 P.bessel u (P.bk_inj u) (P.D_div u)
    (P.D_div_pos u) (P.bk_divisible u)

end BesselIntegralityCompilePack

section CanonicalWitness

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- Dot-product pairing `(Fin n → K) →ₗ[K] Module.Dual K (Fin n → K)`. -/
private def stdDotDual (K : Type) [Field K] (n : ℕ) :
    (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K) where
  toFun x :=
    { toFun := fun y => ∑ i : Fin n, x i * y i
      map_add' := fun y₁ y₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  map_add' x₁ x₂ := LinearMap.ext fun y => by
    change (∑ i : Fin n, (x₁ i + x₂ i) * y i) =
      (∑ i : Fin n, x₁ i * y i) + ∑ i : Fin n, x₂ i * y i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := LinearMap.ext fun y => by
    change (∑ i : Fin n, (c * x i) * y i) = c * ∑ i : Fin n, x i * y i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

private lemma stdDotDual_apply (K : Type) [Field K] (n : ℕ) (x y : Fin n → K) :
    stdDotDual K n x y = ∑ i : Fin n, x i * y i := rfl

private lemma mem_std_lattice_iff {n : ℕ} (hn : 0 < n) (x : Fin n → K) :
    x ∈ (TargetDualHLatRR.std K n hn).RR.L ↔
      ∀ i : Fin n, x i ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  change x ∈ Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨j, rfl⟩
      intro i
      simp only [Pi.basisFun_apply, Pi.single_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add _ _ _ _ ha hb =>
      intro i
      obtain ⟨a, ha'⟩ := ha i
      obtain ⟨b, hb'⟩ := hb i
      exact ⟨a + b, by simp [ha', hb']⟩
    | smul c _ _ ha =>
      intro i
      obtain ⟨a, ha'⟩ := ha i
      exact ⟨c * a, by simp [ha', Algebra.smul_def]⟩
  · intro hx
    choose a ha using hx
    have hsum : x = ∑ i : Fin n, a i • Pi.basisFun K (Fin n) i := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_apply,
        Algebra.smul_def, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ↓reduceIte]
      exact (ha j).symm
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (a i) (Submodule.subset_span ⟨i, rfl⟩)

/-- **Concrete 0-Assumption `IteratedBesselMapBk.std` Witness**:
over any totally complex number field `K`, rank `n + 1`, and level divisor `D_div ≥ 1`,
constructs a concrete `IteratedBesselMapBk K Unit` with congruence sublattice
`Nu = (D_div) • RR.L` and Bessel map `stdDotDual` mapping `Nu` into `D_div • RR^∨`. -/
abbrev stdIteratedBesselMap (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (n D_div : ℕ) (hD_div : 0 < D_div) : IteratedBesselMapBk K Unit :=
  let T := TargetDualHLatRR.std K (n + 1) (Nat.succ_pos n)
  let 𝔞 : Ideal (𝓞 K) := Ideal.span {(D_div : 𝓞 K)}
  let h𝔞 : 𝔞 ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hD_div.ne'
  let Nu0 := CongruenceSublatticeNu.ofIdealTwist T.RR T.RR_good T.RR_rank_pos 𝔞 h𝔞
  { T := T
    Nu := fun _ => Nu0
    Bk := fun _ => stdDotDual K (n + 1)
    C_op := fun _ => 1
    C_op_pos := fun _ => zero_lt_one
    arch_bound := fun _ x => by
      rw [one_mul]
      have heq : realizeHLat T.dual.b T.dual.X (stdDotDual K (n + 1) x) =
          realizeHLat T.RR.b T.RR.X x := by
        ext ⟨v, i, r⟩
        have hdual : T.dual.X v = 1 := by
          change dualFrame T.RR.X v = 1
          change ((T.RR.X v).transpose)⁻¹ = 1
          have hX1 : T.RR.X v = 1 := rfl
          rw [hX1, Matrix.transpose_one, inv_one]
        have hvec : vecAt T.dual.b v (stdDotDual K (n + 1) x) i = vecAt T.RR.b v x i := by
          change v.embedding (T.dual.b.repr (stdDotDual K (n + 1) x) i) =
            v.embedding (T.RR.b.repr x i)
          have h1 : T.dual.b.repr (stdDotDual K (n + 1) x) i =
              stdDotDual K (n + 1) x (T.RR.b i) :=
            Basis.dualBasis_repr T.RR.b (stdDotDual K (n + 1) x) i
          have h2 : stdDotDual K (n + 1) x (T.RR.b i) = x i := by
            let i' : Fin (n + 1) := i
            rw [stdDotDual_apply]
            change ∑ j : Fin (n + 1), x j * (Pi.basisFun K (Fin (n + 1)) i') j = x i'
            simp [Pi.basisFun_apply, Pi.single_apply]
          have h3 : T.RR.b.repr x i = x i := rfl
          rw [h1, h2, h3]
        have hf : fcoord T.dual.b T.dual.X v (stdDotDual K (n + 1) x) i =
            fcoord T.RR.b T.RR.X v x i := by
          unfold fcoord RHDirect.Stage12SchurWeylLattices.fcoord
          have hRR : T.RR.X v = 1 := rfl
          have h1inv : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)⁻¹ = 1 := inv_one
          change (T.dual.X v)⁻¹.mulVec (vecAt T.dual.b v (stdDotDual K (n + 1) x)) i =
            (T.RR.X v)⁻¹.mulVec (vecAt T.RR.b v x) i
          rw [hdual, hRR]
          change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)⁻¹).mulVec
              (vecAt T.dual.b v (stdDotDual K (n + 1) x)) i =
            ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)⁻¹).mulVec (vecAt T.RR.b v x) i
          rw [h1inv, Matrix.one_mulVec, Matrix.one_mulVec]
          exact hvec
        fin_cases r
        · change (fcoord T.dual.b T.dual.X v (stdDotDual K (n + 1) x) i).re =
            (fcoord T.RR.b T.RR.X v x i).re
          rw [hf]
        · change (fcoord T.dual.b T.dual.X v (stdDotDual K (n + 1) x) i).im =
            (fcoord T.RR.b T.RR.X v x i).im
          rw [hf]
      rw [heq]
      rfl
    D_chain := fun _ => 1
    D_chain_pos := fun _ => zero_lt_one
    chain_clears := fun _ φ hφ F hF => by
      simp only [Nat.cast_one, one_mul]
      have hφL : φ ∈ T.RR.L := Submodule.smul_le_right hφ
      have hφ_int : ∀ i, φ i ∈ Set.range (algebraMap (𝓞 K) K) :=
        (mem_std_lattice_iff (Nat.succ_pos n) φ).mp hφL
      have hF_int : ∀ i, F i ∈ Set.range (algebraMap (𝓞 K) K) :=
        (mem_std_lattice_iff (Nat.succ_pos n) F).mp hF
      rw [stdDotDual_apply]
      choose a ha using hφ_int
      choose b hb using hF_int
      refine ⟨∑ i : Fin (n + 1), a i * b i, ?_⟩
      simp only [map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => by rw [ha i, hb i]
    local_val_le_one := fun _ _ _ _ _ la hla => by
      exfalso
      exact la.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem la.asIdeal (by simpa using hla) isUnit_one) }

/-- Non-vacuity theorem: `stdIteratedBesselMap` satisfies `bessel_map_maps_Nu_into_RRDual` and
the ramified Bost slope bound with divisibility `D_div` and operator constant `1`. -/
theorem stdIteratedBesselMap_verified (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] (n D_div : ℕ) (hD_div : 0 < D_div) :
    let B := stdIteratedBesselMap K n D_div hD_div
    ((B.Nu ()).Nu.map ((B.Bk ()).restrictScalars (𝓞 K)) ≤ B.T.dual.L) ∧
    ((B.Nu ()).toHLatAnchor.slope + Real.log (D_div : ℝ) ≤
      B.T.dualAnchor.muMax + Real.log 1) := by
  intro B
  refine ⟨(bessel_map_maps_Nu_into_RRDual B ()).1, ?_⟩
  refine bessel_map_ramified_bost_ineq B () ?_ D_div hD_div ?_
  · intro x _ y _ hxy
    ext i
    have h1 := LinearMap.congr_fun hxy (Pi.basisFun K (Fin (n + 1)) i)
    change stdDotDual K (n + 1) x (Pi.basisFun K (Fin (n + 1)) i) =
      stdDotDual K (n + 1) y (Pi.basisFun K (Fin (n + 1)) i) at h1
    simp only [stdDotDual_apply, Pi.basisFun_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h1
    exact h1
  · intro x hx
    change x ∈ Ideal.span {(D_div : 𝓞 K)} • B.T.RR.L at hx
    have hex : ∃ y ∈ B.T.RR.L, x = (D_div : K) • y := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr z hz
        rw [Ideal.mem_span_singleton] at hr
        obtain ⟨q, rfl⟩ := hr
        refine ⟨q • z, B.T.RR.L.smul_mem q hz, ?_⟩
        rw [mul_smul, ← algebraMap_smul K (D_div : 𝓞 K)]
        simp
      · rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ + y₂, add_mem hy₁ hy₂, (smul_add _ _ _).symm⟩
    obtain ⟨y, hyL, hy⟩ := hex
    refine ⟨stdDotDual K (n + 1) y, ?_, ?_⟩
    · intro F hF
      have hy_int : ∀ i, y i ∈ Set.range (algebraMap (𝓞 K) K) :=
        (mem_std_lattice_iff (Nat.succ_pos n) y).mp hyL
      have hF_int : ∀ i, F i ∈ Set.range (algebraMap (𝓞 K) K) :=
        (mem_std_lattice_iff (Nat.succ_pos n) F).mp hF
      change stdDotDual K (n + 1) y F ∈ Set.range (algebraMap (𝓞 K) K)
      rw [stdDotDual_apply]
      choose a ha using hy_int
      choose b hb using hF_int
      exact ⟨∑ i : Fin (n + 1), a i * b i, by
        simp only [map_sum, map_mul]
        refine Finset.sum_congr rfl fun i _ => by rw [ha i, hb i]⟩
    · change stdDotDual K (n + 1) x = (D_div : ℤ) • stdDotDual K (n + 1) y
      rw [hy, map_smul, ← Int.cast_smul_eq_zsmul K (D_div : ℤ), Int.cast_natCast]

end CanonicalWitness

end FrameRealCompileHandoff

end RHDirect.Stage14M2_BesselIntegrality

end
