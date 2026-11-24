import RHDirect.Stage14Contracts
import RHDirect.Stage14M2_HLatNumberField
import RHDirect.Stage14M2_HNFiltAndFrame
import RHDirect.Stage14M2_BanaszczykShortBasis
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# RHDirect.Stage14M2_RamifiedJointBost

Field-2 Package M2 (Wave 2): **Ramified Linear-Case Slope Geometry (`RamificationLinearCase`),
Flatness Bounds (`FlatLatticeTheorem`), Sharp Ramified Joint-Model Bost Frame Inequality
(`joint_a_ramified_holds`), and Non-Short-Circuited Bost Slope Lower Bound into Independent
`mu(RR^∨)` (`bost_slope_ineq_from_ramified_frame`)** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`, zero `opaque`.

## Architecture & Main Exports (Ready for `Stage14M2_FrameRealCompile`)

1. **Section 1 — Exact Adapter Bridge (`HLatNumberField` ↔ `HNFiltAndFrame` ↔ `HLatAnchor`)**:
   - Exact definitional/algebraic bridge identifying `Stage14M2_HLatNumberField.{muDef, muMaxDef,
     muMinDef}` with `Stage14M2_HNFiltAndFrame.{muDef, muMaxDef, muMinDef}` without editing any
     frozen upstream file.
   - Canonical `HLat.toHLatAnchor` embedding any good `HLat K` into `Stage14Contracts.HLatAnchor`,
     preserving `rk`, `covol`, `degAr`, `slope`, and `muMax`.

2. **Section 2 — Exact `K`-Rank Harder–Narasimhan Slope Vector (`hnSlopeListK`)**:
   - Proves `[K : ℚ]`-block constancy of `Stage14M2_HNFiltAndFrame.hnSlopeList` for any finitely
     generated `𝓞 K`-lattice (`hnSlopeList_block_const`).
   - Extracts the exact `K`-rank HN slope vector `hnSlopeListK : Fin (Fintype.card ι) → ℝ` with:
     * exact average `(∑ a, hnSlopeListK a) / |ι| = muDef b X L` (`hnSlopeListK_mean`),
     * exact extremal bounds `muMinDef ≤ hnSlopeListK a ≤ muMaxDef` (`hnSlopeListK_bounds`),
     * exact tail count `#{a | hnSlopeListK a < θ} = |ι| - rkK (hnStep ((θ - c_K) / 2))`
       (`card_hnSlopeListK_lt`).

3. **Section 3 — `RamificationLinearCase`**:
   - Exact Dedekind-domain fractional-ideal bijection `M ↦ 𝔟 • M` between submodules of `L` and
     submodules of `𝔟 • L` (`exists_ideal_quot_submodule`), yielding exact linear shifts of
     `muDef`, `muMaxDef`, `muMinDef`, `hnStep`, and `hnSlopeListK` by
     `-(2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)` (`ramified_ideal_twist_invariants`).
   - Prime-power ramification decomposition (`ramified_prime_prod_shift`) and simultaneous
     place-rescaling + ideal-twist formula (`ramified_twist_and_rescale_slope`).
   - `RamificationLinearCase` structure and theorems: ramified Bost morphism slope inequalities
     over `𝓞 K`, dual target `RR^∨` pairing inequality, and direct `Stage14Contracts.HLatAnchor`
     divisible Bost theorem (`ramificationLinearCase_anchor`).

4. **Section 4 — `FlatLatticeTheorem`**:
   - `IsFlatHLat` flatness predicate (`muMax - muMin ≤ H`) and exact sharp parabolic HN-polygon
     deviation bound `0 ≤ hnPoly k - k * slope ≤ (H / 2) * k * (r - k) / r`
     (`hnPoly_flat_parabolic_bound`).
   - Unconditional Banaszczyk `O(log r)` flatness (`flatLattice_of_banaszczyk`, zero LLL!) via
     `Stage14M2_BanaszczykShortBasis.banaszczyk_hh_gap_le` / `banaszczyk_numberFieldHLat_hh_gap_le`.
   - Exact invariance of flatness under duality `dualHLat` (`flatLattice_dual_invariance`), ideal
     twists (`flatLattice_ideal_twist_invariance`), and positive place rescalings
     (`flatLattice_place_rescale_invariance`), plus finite-index ramified sublattice flatness
     stability (`flatLattice_sublattice_spread`) and `FlatLatticeTheorem`.

5. **Section 5 — `joint_a_ramified_holds`**:
   - `joint_a_ramified_holds_contract`: exact discharge of the
     `Stage14Contracts.M2HLatBostContract.joint_a_ramified_holds` obligation.
   - `joint_a_ramified_sharp_unprojected`: ramified sharp Bost frame inequality combining
     `Stage14M2_HNFiltAndFrame.frame_herm_sharp_slope_ineq`, ramified ideal divisibility
     `(N i).map (B i) ≤ 𝔟 • cc`, and Banaszczyk's `O(log r)` gap ceiling
     `Stage14M2_BanaszczykShortBasis.banaszczyk_hh_gap_le`!
   - `joint_a_ramified_holds`: full projected ramified joint-model Bost frame inequality
     combining `Stage14M2_HNFiltAndFrame.theoremFSharp_holds` and
     `Stage14M2_BanaszczykShortBasis.banaszczyk_hh_gap_le` into an independent target lattice `cc`.

6. **Section 6 — `bost_slope_ineq_from_ramified_frame` (ZERO `F.muCC = s` Short-Circuit!)**:
   - `mkStage2GramFrameFiber_of_ramified_hlat`: constructs a genuine `Stage2GramFrameFiber`
     directly from a family of CM Hermitian lattices `Nu u` mapping into a ramified dual target
     `𝔟 • (dualHLat RR)` (`RR^∨`), with `F.muCC = (dualHLat RR).mu - (2 / [K : ℚ]) * log N(𝔟)`
     (strictly independent of `s`!).
   - `bost_slope_ineq_from_ramified_frame`: proves the sharp Bost slope lower bound
     `s - log |W| - (1 - δ)⁻¹ * (4 * uF * log (1 + HH / uF) + (η + 4 * √e) * HH) ≤ (dualHLat RR).mu`
     (with explicit ramification gain `+ (2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)`), aligned directly
     with `Stage14Contracts.M2HLatBostContract` and `Stage14Contracts.M2FiberCert` ready for
     `Stage14M2_FrameRealCompile`!
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Matrix NumberField IsDedekindDomain
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology ComplexOrder Pointwise

open RHDirect
open RHDirect.Stage14Contracts
open RHDirect.Stage12SchurWeylLattices (realizeHLat fcoord vecAt normAt)
open RHDirect.Stage14M2_HLatNumberField (HLat dualHLat dualLatO dualFrame dualFrame_frameOK
  directSumHLat directSumHLat_good directSumHLat_invariants
  zRealize rkK logDiscDivDeg discShift
  degHLat slopeHLat slopesO quotSlopesO muMaxO muMinO
  discreteTopology_zRealize_of_fg isZLattice_zRealize_of_good rk_zRealize_eq
  realizeHLat_injective zRealize_mono zRealize_bot twist_index twist_span_smul
  muDef_sublattice_index muMaxDef_mono muMinDef_le_muDef_le_muMaxDef
  muMaxO_char muMinO_char hlat_duality_slope_neg toNumberFieldHLat)
open RHDirect.Stage14M2_HNFiltAndFrame (zl IsLat IsSat hnStep hnStep_spec hnSlopeList
  hnSlopeList_antitone card_hnSlopeList_ge card_hnSlopeList_lt sum_hnSlopeList
  hnSlopeList_extremes hnPoly deg_le_hnPoly deg_hnStep_eq_hnPoly
  nPl logDisc slopeNormalisingConstant opNormAt htMap finrank_eq_two_mul_nPl
  finrank_span_complex place_lattice_structure twist_invariance fcoord_map_eq
  slope_inequality_mean theoremFSharp_holds theoremF_holds
  frame_herm_sharp_slope_ineq frame_herm_slope_ineq bostSlopeFiber_of_herm_frame)
open RHDirect.Stage14M2_BanaszczykShortBasis (banaszczyk_hh_gap_le
  banaszczyk_hh_gap_le_of_lambda_prod banaszczyk_numberFieldHLat_hh_gap_le
  banaszczyk_muMax_via_dual_lambda1 banaszczyk_numberFieldHLat_muMax_via_dual_lambda1
  short_basis_of_banaszczyk_and_minkowski)
open RHDirect.LatticeFrame (opFrameK opFrameQ opHsSq IsIsometryFamily GramInput
  compressFamily totalRank)
open RHDirect.Stage2ThetaWire (Stage2GramFrameFiber)

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RHDirect.Stage14M2_RamifiedJointBost

/-! ## Section 1: Exact Adapter Bridge (`HLatNumberField` ↔ `HNFiltAndFrame` ↔ `HLatAnchor`) -/

section AdapterBridge

variable {K V ι : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

/-- Realized `ℤ`-lattices in `HLatNumberField` and `HNFiltAndFrame` are definitionally equal. -/
lemma zRealize_eq_zl (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) :
    zRealize b X L = zl (realizeHLat b X) L := rfl

/-- `rkK` in `HLatNumberField` and `HNFiltAndFrame` are definitionally equal. -/
lemma rkK_eq_hnRkK (L : Submodule (𝓞 K) V) :
    rkK (K := K) L = Stage14M2_HNFiltAndFrame.rkK L := rfl

/-- Normalizing constants agree: `-log 2 + log |discr K| / [K : ℚ]`. -/
lemma slopeNormalisingConstant_eq (K : Type*) [Field K] [NumberField K] :
    slopeNormalisingConstant K = -Real.log 2 + logDiscDivDeg K := rfl

lemma discShift_eq_neg_normConst (K : Type*) [Field K] [NumberField K] :
    discShift K = -slopeNormalisingConstant K := by
  unfold discShift slopeNormalisingConstant logDiscDivDeg logDisc
  ring

/-- Exact agreement of normalized Arakelov slope `muDef` across Wave 1 modules. -/
theorem muDef_eq_hnMuDef [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) :
    Stage14M2_HLatNumberField.muDef b X L = Stage14M2_HNFiltAndFrame.muDef b X L := by
  unfold Stage14M2_HLatNumberField.muDef Stage14M2_HNFiltAndFrame.muDef
    slopeHLat Stage14M2_HNFiltAndFrame.slope slopeNormalisingConstant logDiscDivDeg logDisc
  change 2 * ArakelovCovolume.slope (zRealize b X L) - Real.log 2 +
      Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ) =
    2 * ArakelovCovolume.slope (zRealize b X L) +
      (-Real.log 2 + Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ))
  ring

/-- Exact agreement of maximal normalized slope `muMaxDef` across Wave 1 modules. -/
theorem muMaxDef_eq_hnMuMaxDef [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) :
    Stage14M2_HLatNumberField.muMaxDef b X L = Stage14M2_HNFiltAndFrame.muMaxDef b X L := by
  unfold Stage14M2_HLatNumberField.muMaxDef Stage14M2_HNFiltAndFrame.muMaxDef
    muMaxO Stage14M2_HNFiltAndFrame.muMax slopesO slopeHLat Stage14M2_HNFiltAndFrame.slope
    slopeNormalisingConstant logDiscDivDeg logDisc
  change 2 * sSup {t : ℝ | ∃ N : Submodule (𝓞 K) V, N ≤ L ∧ N ≠ ⊥ ∧
        ArakelovCovolume.slope (zRealize b X N) = t} - Real.log 2 +
      Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ) =
    2 * sSup {t : ℝ | ∃ N : Submodule (𝓞 K) V, N ≤ L ∧ N ≠ ⊥ ∧
        ArakelovCovolume.slope (zRealize b X N) = t} +
      (-Real.log 2 + Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ))
  ring

/-- Exact agreement of minimal normalized slope `muMinDef` across Wave 1 modules. -/
theorem muMinDef_eq_hnMuMinDef [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) :
    Stage14M2_HLatNumberField.muMinDef b X L = Stage14M2_HNFiltAndFrame.muMinDef b X L := by
  have hset : quotSlopesO b X L =
      {t : ℝ | ∃ N : Submodule (𝓞 K) V, IsSat (realizeHLat b X) L N ∧ N ≠ L ∧
        ArakelovCovolume.slope (Stage4ArakelovBost.quotLat (zl (realizeHLat b X) L)
          (zl (realizeHLat b X) N)) = t} := by
    ext t
    simp only [quotSlopesO, IsSat, zRealize_eq_zl, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N, hNL, hsat, hne, rfl⟩; exact ⟨N, ⟨hNL, hsat⟩, hne, rfl⟩
    · rintro ⟨N, ⟨hNL, hsat⟩, hne, rfl⟩; exact ⟨N, hNL, hsat, hne, rfl⟩
  unfold Stage14M2_HLatNumberField.muMinDef Stage14M2_HNFiltAndFrame.muMinDef
    muMinO Stage14M2_HNFiltAndFrame.muMin slopeNormalisingConstant logDiscDivDeg logDisc
  rw [hset]
  ring

/-- Comparison of `𝓞 K`-normalized `muMaxDef` with the underlying `ℤ`-lattice `muMax`. -/
theorem muMaxDef_le_two_mul_zMuMax [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    Stage14M2_HLatNumberField.muMaxDef b X L ≤
      2 * ArakelovCovolume.muMax (zRealize b X L) + slopeNormalisingConstant K := by
  haveI : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  have hsub : slopesO b X L ⊆ ArakelovCovolume.slopes (zRealize b X L) := by
    rintro t ⟨N, hNL, hN0, rfl⟩
    refine ⟨zRealize b X N, zRealize_mono b X hNL, ?_, rfl⟩
    intro hbot
    apply hN0
    rw [eq_bot_iff]
    intro x hx
    have hm : realizeHLat b X x ∈ zRealize b X N := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact realizeHLat_injective b X hX (hm.trans (map_zero _).symm)
  have hne : (slopesO b X L).Nonempty := ⟨slopeHLat b X L, L, le_rfl, hL0, rfl⟩
  have hle : muMaxO b X L ≤ ArakelovCovolume.muMax (zRealize b X L) :=
    csSup_le_csSup (ArakelovCovolume.slopes_bddAbove (zRealize b X L)) hne hsub
  unfold Stage14M2_HLatNumberField.muMaxDef slopeNormalisingConstant logDiscDivDeg logDisc
  linarith

/-- Comparison of `𝓞 K`-normalized `muMinDef` with the underlying `ℤ`-lattice `muMin`. -/
theorem two_mul_zMuMin_le_muMinDef [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    2 * Stage4ArakelovBost.muMin (zRealize b X L) + slopeNormalisingConstant K ≤
      Stage14M2_HLatNumberField.muMinDef b X L := by
  haveI : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  have hle : Stage4ArakelovBost.muMin (zRealize b X L) ≤ muMinO b X L := by
    refine le_csInf ⟨_, ⊥, bot_le, ?_, hL0.symm, rfl⟩ ?_
    · rw [zRealize_bot]; exact Stage4ArakelovBost.isSaturated_bot _
    · rintro t ⟨N, hNL, hsat, hne, rfl⟩
      have hZne : zRealize b X N ≠ zRealize b X L := by
        intro heq; apply hne; apply le_antisymm hNL
        intro x hxL
        have hm : realizeHLat b X x ∈ zRealize b X N := heq ▸ ⟨x, hxL, rfl⟩
        rcases hm with ⟨y, hyN, hyx⟩
        rwa [← realizeHLat_injective b X hX hyx]
      exact Stage4ArakelovBost.muMin_le_slope_quotLat hsat hZne
  unfold Stage14M2_HLatNumberField.muMinDef slopeNormalisingConstant logDiscDivDeg logDisc
  linarith

/-- Canonical `HLat K` spread is bounded above by twice the underlying `ℤ`-lattice spread. -/
theorem muMaxDef_sub_muMinDef_le_two_mul_zSpread [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    Stage14M2_HLatNumberField.muMaxDef b X L - Stage14M2_HLatNumberField.muMinDef b X L ≤
      2 * (ArakelovCovolume.muMax (zRealize b X L) - Stage4ArakelovBost.muMin (zRealize b X L)) := by
  have h1 := muMaxDef_le_two_mul_zMuMax b X hX L hL hL0
  have h2 := two_mul_zMuMin_le_muMinDef b X hX L hL hL0
  linarith

/-- Canonical bridge from any good nonzero `HLat K` to `Stage14Contracts.HLatAnchor`. -/
def hlatToAnchor {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) : HLatAnchor where
  E := EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)
  L := A.zRealize
  disc := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  ne_bot := by
    intro hbot
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : realizeHLat A.b A.X x ∈ A.zRealize := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact realizeHLat_injective A.b A.X hG.1 (hm.trans (map_zero _).symm)

theorem hlatToAnchor_rk {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    (hlatToAnchor A hG hA0).rk = Module.finrank ℚ K * A.rank := by
  unfold HLatAnchor.rk hlatToAnchor HLat.rank
  exact rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1

theorem hlatToAnchor_slope {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    2 * (hlatToAnchor A hG hA0).slope + slopeNormalisingConstant K = A.mu := by
  unfold HLatAnchor.slope hlatToAnchor HLat.mu Stage14M2_HLatNumberField.muDef
    slopeHLat slopeNormalisingConstant logDiscDivDeg logDisc
  ring

theorem hlatToAnchor_muMax_ge {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    A.muMax ≤ 2 * (hlatToAnchor A hG hA0).muMax + slopeNormalisingConstant K :=
  muMaxDef_le_two_mul_zMuMax A.b A.X hG.1 A.L hG.2.1 hA0

/-- Bridge from `NumberFieldHLat K` normalized slopes to `HLat K` normalized slopes. -/
theorem numberFieldHLat_mu_eq_hlat_mu {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) :
    (toNumberFieldHLat A hG).mu = A.mu := by
  rfl

end AdapterBridge

/-! ## Section 2: Exact `K`-Rank Harder–Narasimhan Slope Vector (`hnSlopeListK`) -/

section KRankHNSlopes

/-- **Block Constancy Lemma**: if `f : Fin (D * d) → ℝ` (`0 < d`) is antitone and every
upper level-set `{j | θ ≤ f j}` has cardinality divisible by `d`, then `f` is constant on
every consecutive block `[a * d, (a + 1) * d)` of length `d`! -/
theorem antitone_block_const_of_dvd_card_ge {D d : ℕ} (hd : 0 < d) (f : Fin (D * d) → ℝ)
    (hf : Antitone f)
    (hdvd : ∀ θ : ℝ, d ∣ (Finset.univ.filter (fun j : Fin (D * d) => θ ≤ f j)).card)
    (a : Fin D) (q : Fin d) :
    f ⟨a.1 * d + q.1, by nlinarith [a.2, q.2]⟩ =
      f ⟨a.1 * d, by nlinarith [a.2]⟩ := by
  let i₀ : Fin (D * d) := ⟨a.1 * d, by nlinarith [a.2]⟩
  let i : Fin (D * d) := ⟨a.1 * d + q.1, by nlinarith [a.2, q.2]⟩
  have hle1 : f i ≤ f i₀ := hf (show i₀ ≤ i by change a.1 * d ≤ a.1 * d + q.1; omega)
  apply le_antisymm hle1
  by_contra hlt
  push Not at hlt
  set S : Finset (Fin (D * d)) := Finset.univ.filter (fun j : Fin (D * d) => f i₀ ≤ f j)
  have hinit : Finset.univ.filter (fun j : Fin (D * d) => j.1 ≤ a.1 * d) ⊆ S := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ j, hf (show j ≤ i₀ from hj.2)⟩
  have hcard_init : (Finset.univ.filter (fun j : Fin (D * d) => j.1 ≤ a.1 * d)).card =
      a.1 * d + 1 := by
    have hbij : (Finset.univ.filter (fun j : Fin (D * d) => j.1 ≤ a.1 * d)).card =
        (Finset.range (a.1 * d + 1)).card := by
      refine Finset.card_bij (fun j _ => j.1)
        (fun j hj => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2))
        (fun _ _ _ _ h => Fin.ext h)
        (fun k hk => ⟨⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk) (by nlinarith [a.2])⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ (Finset.mem_range.mp hk)⟩, rfl⟩)
    rw [hbij, Finset.card_range]
  have hS_ge : a.1 * d + 1 ≤ S.card := by
    rw [← hcard_init]
    exact Finset.card_le_card hinit
  obtain ⟨m, hm⟩ := hdvd (f i₀)
  have hm_ge : a.1 + 1 ≤ m := by nlinarith
  have hS_ge2 : (a.1 + 1) * d ≤ S.card := by nlinarith
  have hS_sub : S ⊆ Finset.univ.filter (fun j : Fin (D * d) => j.1 < i.1) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ j, ?_⟩
    by_contra hge
    have hij : i ≤ j := Nat.le_of_not_lt hge
    have hfj : f j ≤ f i := hf hij
    linarith [hj.2]
  have hcard_lt : (Finset.univ.filter (fun j : Fin (D * d) => j.1 < i.1)).card = i.1 := by
    have hbij : (Finset.univ.filter (fun j : Fin (D * d) => j.1 < i.1)).card =
        (Finset.range i.1).card := by
      refine Finset.card_bij (fun j _ => j.1)
        (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun k hk => ⟨⟨k, lt_trans (Finset.mem_range.mp hk) i.2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩, rfl⟩)
    rw [hbij, Finset.card_range]
  have hS_le : S.card ≤ a.1 * d + q.1 := by
    calc S.card ≤ (Finset.univ.filter (fun j : Fin (D * d) => j.1 < i.1)).card :=
          Finset.card_le_card hS_sub
      _ = i.1 := hcard_lt
      _ = a.1 * d + q.1 := rfl
  have hq_lt : q.1 < d := q.2
  nlinarith

/-- Sum identity for a `d`-block-constant function on `Fin (D * d)`. -/
theorem sum_block_const {D d : ℕ} (hd : 0 < d) (f : Fin (D * d) → ℝ)
    (hconst : ∀ (a : Fin D) (q : Fin d),
      f ⟨a.1 * d + q.1, by nlinarith [a.2, q.2]⟩ = f ⟨a.1 * d, by nlinarith [a.2]⟩) :
    ∑ j : Fin (D * d), f j = (d : ℝ) * ∑ a : Fin D, f ⟨a.1 * d, by nlinarith [a.2]⟩ := by
  let e : Fin D × Fin d ≃ Fin (D * d) :=
    { toFun := fun p => ⟨p.1.1 * d + p.2.1, by nlinarith [p.1.2, p.2.2]⟩
      invFun := fun j => (⟨j.1 / d, Nat.div_lt_of_lt_mul (by have := j.2; nlinarith)⟩,
        ⟨j.1 % d, Nat.mod_lt j.1 hd⟩)
      left_inv := fun ⟨a, q⟩ => by
        ext
        · change (a.1 * d + q.1) / d = a.1
          rw [mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt q.2, add_zero]
        · change (a.1 * d + q.1) % d = q.1
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt q.2]
      right_inv := fun j => by
        ext
        change j.1 / d * d + j.1 % d = j.1
        rw [mul_comm, Nat.div_add_mod] }
  rw [← Fintype.sum_equiv e (fun p => f (e p)) f (fun _ => rfl), Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hinner : ∀ q : Fin d, f (e (a, q)) = f ⟨a.1 * d, by nlinarith [a.2]⟩ := fun q => hconst a q
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Exact filter-cardinality identity for a `d`-block-constant function on `Fin (D * d)`. -/
theorem card_filter_lt_block_const {D d : ℕ} (hd : 0 < d) (f : Fin (D * d) → ℝ)
    (hconst : ∀ (a : Fin D) (q : Fin d),
      f ⟨a.1 * d + q.1, by nlinarith [a.2, q.2]⟩ = f ⟨a.1 * d, by nlinarith [a.2]⟩)
    (θ : ℝ) :
    (Finset.univ.filter (fun j : Fin (D * d) => f j < θ)).card =
      d * (Finset.univ.filter (fun a : Fin D => f ⟨a.1 * d, by nlinarith [a.2]⟩ < θ)).card := by
  let g : Fin (D * d) → ℝ := fun j => if f j < θ then 1 else 0
  have hg : ∀ (a : Fin D) (q : Fin d),
      g ⟨a.1 * d + q.1, by nlinarith [a.2, q.2]⟩ = g ⟨a.1 * d, by nlinarith [a.2]⟩ := fun a q => by
    simp only [g, hconst a q]
  have hsum := sum_block_const hd g hg
  simp only [g, Finset.sum_boole] at hsum
  exact_mod_cast hsum

section HLatKRankHN

variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

/-- **Exact `K`-Rank Normalized HN Slope Vector (`hnSlopeListK`)**:
for any finitely generated `𝓞 K`-submodule `L ≤ V` with invertible frame `X` and `rkK L = D`,
extracts the `D`-length descending normalized HN slope vector `hnSlopeListK : Fin D → ℝ`
by sampling the `[K : ℚ]`-block-constant `hnSlopeList (realizeHLat b X) L` at every block start! -/
def hnSlopeListK (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    Fin (rkK (K := K) L) → ℝ :=
  fun a =>
    let dK := Module.finrank ℚ K
    let hrk : Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L = rkK (K := K) L * dK := by
      rw [(place_lattice_structure b X hX L hL).2, mul_comm]; rfl
    have hidx : a.1 * dK < Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L := by
      rw [hrk]; nlinarith [a.2, Module.finrank_pos (R := ℚ) (M := K)]
    2 * hnSlopeList (realizeHLat b X) L ⟨a.1 * dK, hidx⟩ + slopeNormalisingConstant K

/-- Underlying `[K : ℚ]`-block constancy of `hnSlopeList (realizeHLat b X) L`. -/
theorem hnSlopeList_block_const (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    let dK := Module.finrank ℚ K
    let hrk : Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L = rkK (K := K) L * dK := by
      rw [(place_lattice_structure b X hX L hL).2, mul_comm]; rfl
    ∀ (a : Fin (rkK (K := K) L)) (q : Fin dK),
      hnSlopeList (realizeHLat b X) L ⟨a.1 * dK + q.1, by rw [hrk]; nlinarith [a.2, q.2]⟩ =
        hnSlopeList (realizeHLat b X) L ⟨a.1 * dK, by rw [hrk]; nlinarith [a.2, Module.finrank_pos (R := ℚ) (M := K)]⟩ := by
  intro dK hrk a q
  let f : Fin (rkK (K := K) L * dK) → ℝ :=
    fun j => hnSlopeList (realizeHLat b X) L (Fin.cast hrk.symm j)
  have hLat : IsLat (realizeHLat b X) L := (place_lattice_structure b X hX L hL).1
  have hf_anti : Antitone f := fun i j hij =>
    hnSlopeList_antitone (realizeHLat b X) hLat (show Fin.cast hrk.symm i ≤ Fin.cast hrk.symm j from hij)
  have hf_dvd : ∀ θ : ℝ, dK ∣ (Finset.univ.filter (fun j : Fin (rkK (K := K) L * dK) => θ ≤ f j)).card := by
    intro θ
    have hcard : (Finset.univ.filter (fun j : Fin (rkK (K := K) L * dK) => θ ≤ f j)).card =
        (Finset.univ.filter (fun j : Fin (Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L) =>
          θ ≤ hnSlopeList (realizeHLat b X) L j)).card := by
      refine Finset.card_bij (fun j _ => Fin.cast hrk.symm j)
        (fun j hj => by
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨Finset.mem_univ _, hj.2⟩)
        (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun j hj => ⟨Fin.cast hrk j, by
          rw [Finset.mem_filter] at hj ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa [f] using hj.2, by ext; rfl⟩)
    rw [hcard]
    have hstep := card_hnSlopeList_ge (realizeHLat b X) hLat θ
    have hstep_fg : (hnStep (realizeHLat b X) L θ).FG :=
      Submodule.FG.of_le hL (hnStep_spec _ hLat θ).1.1
    have hstep_rk := (place_lattice_structure b X hX (hnStep (realizeHLat b X) L θ) hstep_fg).2
    have hnat : (Finset.univ.filter (fun j => θ ≤ hnSlopeList (realizeHLat b X) L j)).card =
        dK * Stage14M2_HNFiltAndFrame.rkK (hnStep (realizeHLat b X) L θ) := by
      have : ((Finset.univ.filter (fun j => θ ≤ hnSlopeList (realizeHLat b X) L j)).card : ℝ) =
          ((dK * Stage14M2_HNFiltAndFrame.rkK (hnStep (realizeHLat b X) L θ) : ℕ) : ℝ) := by
        rw [hstep, hstep_rk]
      exact_mod_cast this
    rw [hnat]
    exact dvd_mul_right dK _
  exact antitone_block_const_of_dvd_card_ge Module.finrank_pos f hf_anti hf_dvd a q

/-- `hnSlopeListK` is antitone (descending). -/
theorem hnSlopeListK_antitone (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    Antitone (hnSlopeListK b X hX L hL) := by
  intro a c hac
  have hLat := (place_lattice_structure b X hX L hL).1
  unfold hnSlopeListK
  dsimp only
  have hrk : Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L = rkK (K := K) L * Module.finrank ℚ K := by
    rw [(place_lattice_structure b X hX L hL).2, mul_comm]; rfl
  have hia : a.1 * Module.finrank ℚ K < Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L := by
    rw [hrk]; nlinarith [a.2, Module.finrank_pos (R := ℚ) (M := K)]
  have hic : c.1 * Module.finrank ℚ K < Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L := by
    rw [hrk]; nlinarith [c.2, Module.finrank_pos (R := ℚ) (M := K)]
  have h1 : hnSlopeList (realizeHLat b X) L ⟨c.1 * Module.finrank ℚ K, hic⟩ ≤
      hnSlopeList (realizeHLat b X) L ⟨a.1 * Module.finrank ℚ K, hia⟩ :=
    hnSlopeList_antitone (realizeHLat b X) hLat
      (show (⟨a.1 * Module.finrank ℚ K, hia⟩ : Fin _) ≤ ⟨c.1 * Module.finrank ℚ K, hic⟩ from
        Nat.mul_le_mul_right _ hac)
  linarith

/-- **Exact Sum Identity**: `∑ a, hnSlopeListK a = rkK L * muDef b X L`. -/
theorem sum_hnSlopeListK (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    ∑ a : Fin (rkK (K := K) L), hnSlopeListK b X hX L hL a =
      (rkK (K := K) L : ℝ) * Stage14M2_HLatNumberField.muDef b X L := by
  let dK := Module.finrank ℚ K
  have hdK : 0 < dK := Module.finrank_pos
  have hdKR : (0 : ℝ) < (dK : ℝ) := Nat.cast_pos.mpr hdK
  have hLat := (place_lattice_structure b X hX L hL).1
  have hrk : Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L = rkK (K := K) L * dK := by
    rw [(place_lattice_structure b X hX L hL).2, mul_comm]; rfl
  let f : Fin (rkK (K := K) L * dK) → ℝ :=
    fun j => hnSlopeList (realizeHLat b X) L (Fin.cast hrk.symm j)
  have hbc := hnSlopeList_block_const b X hX L hL
  have hsum_f : ∑ j : Fin (rkK (K := K) L * dK), f j =
      (dK : ℝ) * ∑ a : Fin (rkK (K := K) L), f ⟨a.1 * dK, by nlinarith [a.2]⟩ :=
    sum_block_const hdK f hbc
  have hsum_eq : ∑ j : Fin (rkK (K := K) L * dK), f j =
      Stage14M2_HNFiltAndFrame.deg (realizeHLat b X) L := by
    rw [← sum_hnSlopeList (realizeHLat b X) hLat]
    exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun _ => rfl)
  have hsum_K : (dK : ℝ) * ∑ a : Fin (rkK (K := K) L), hnSlopeListK b X hX L hL a =
      2 * Stage14M2_HNFiltAndFrame.deg (realizeHLat b X) L +
        (dK : ℝ) * (rkK (K := K) L : ℝ) * slopeNormalisingConstant K := by
    unfold hnSlopeListK
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_add]
    have hterm : (dK : ℝ) * (2 * ∑ a : Fin (rkK (K := K) L),
        hnSlopeList (realizeHLat b X) L ⟨a.1 * dK, by rw [hrk]; nlinarith [a.2, hdK]⟩) =
        2 * Stage14M2_HNFiltAndFrame.deg (realizeHLat b X) L := by
      have : ∑ a : Fin (rkK (K := K) L),
          hnSlopeList (realizeHLat b X) L ⟨a.1 * dK, by rw [hrk]; nlinarith [a.2, hdK]⟩ =
          ∑ a : Fin (rkK (K := K) L), f ⟨a.1 * dK, by nlinarith [a.2]⟩ := rfl
      rw [this]; linarith
    rw [hterm]; ring
  have hrk_pos : 0 < Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L := by
    haveI : DiscreteTopology (zRealize b X L) := hLat.2
    exact ArakelovCovolume.rk_pos_of_ne_bot (zRealize b X L) (by
      intro hbot; apply hL0; rw [eq_bot_iff]; intro x hx
      have hm : realizeHLat b X x ∈ zRealize b X L := ⟨x, hx, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact realizeHLat_injective b X hX (hm.trans (map_zero _).symm))
  have hrk_pos' : 0 < rkK (K := K) L := by
    rw [hrk] at hrk_pos; exact Nat.pos_of_mul_pos_right hrk_pos
  have hrk_R : (Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L : ℝ) =
      (rkK (K := K) L : ℝ) * (dK : ℝ) := by exact_mod_cast hrk
  rw [muDef_eq_hnMuDef]
  unfold Stage14M2_HNFiltAndFrame.muDef Stage14M2_HNFiltAndFrame.slope ArakelovCovolume.slope
  have hdeg_eq : Stage14M2_HNFiltAndFrame.deg (realizeHLat b X) L =
      ArakelovCovolume.degAr (zl (realizeHLat b X) L) := rfl
  rw [hdeg_eq] at hsum_K
  have hrk_ne : (Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hrk_pos.ne'
  have hgoal : (dK : ℝ) * ((rkK (K := K) L : ℝ) *
      (2 * (ArakelovCovolume.degAr (zl (realizeHLat b X) L) /
        (Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L : ℝ)) +
        slopeNormalisingConstant K)) =
      2 * ArakelovCovolume.degAr (zl (realizeHLat b X) L) +
        (dK : ℝ) * (rkK (K := K) L : ℝ) * slopeNormalisingConstant K := by
    rw [hrk_R] at hrk_ne ⊢
    field_simp [hrk_ne]
  exact mul_left_cancel₀ hdKR.ne' (hsum_K.trans hgoal.symm)

/-- **Exact Average Identity**: `(∑ a, hnSlopeListK a) / rkK L = muDef b X L`. -/
theorem mean_hnSlopeListK (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    (∑ a : Fin (rkK (K := K) L), hnSlopeListK b X hX L hL a) / (rkK (K := K) L : ℝ) =
      Stage14M2_HLatNumberField.muDef b X L := by
  have hLat := (place_lattice_structure b X hX L hL).1
  have hrk_pos : 0 < rkK (K := K) L := by
    haveI : DiscreteTopology (zRealize b X L) := hLat.2
    have h1 := ArakelovCovolume.rk_pos_of_ne_bot (zRealize b X L) (by
      intro hbot; apply hL0; rw [eq_bot_iff]; intro x hx
      have hm : realizeHLat b X x ∈ zRealize b X L := ⟨x, hx, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact realizeHLat_injective b X hX (hm.trans (map_zero _).symm))
    rw [rk_zRealize_eq b X hX L hL] at h1
    exact Nat.pos_of_mul_pos_left h1
  rw [sum_hnSlopeListK b X hX L hL hL0, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hrk_pos.ne')]

/-- **Exact Extremal Sandwich**: `muMinDef b X L ≤ hnSlopeListK a ≤ muMaxDef b X L`. -/
theorem hnSlopeListK_bounds (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥)
    (a : Fin (rkK (K := K) L)) :
    Stage14M2_HLatNumberField.muMinDef b X L ≤ hnSlopeListK b X hX L hL a ∧
    hnSlopeListK b X hX L hL a ≤ Stage14M2_HLatNumberField.muMaxDef b X L := by
  have hLat := (place_lattice_structure b X hX L hL).1
  have hext := (hnSlopeList_extremes (realizeHLat b X) hLat hL0).1
    ⟨a.1 * Module.finrank ℚ K, by
      rw [(place_lattice_structure b X hX L hL).2, ← rkK_eq_hnRkK]
      nlinarith [a.2, Module.finrank_pos (R := ℚ) (M := K)]⟩
  rw [muMinDef_eq_hnMuMinDef, muMaxDef_eq_hnMuMaxDef]
  unfold hnSlopeListK Stage14M2_HNFiltAndFrame.muMinDef Stage14M2_HNFiltAndFrame.muMaxDef
  dsimp only
  exact ⟨by linarith [hext.1], by linarith [hext.2]⟩

/-- **Exact Tail-Count Identity**:
`#{a : Fin (rkK L) | hnSlopeListK a < θ} = rkK L - rkK (hnStep L ((θ - c_K) / 2))`. -/
theorem card_hnSlopeListK_lt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (θ : ℝ) :
    ((Finset.univ.filter (fun a : Fin (rkK (K := K) L) =>
        hnSlopeListK b X hX L hL a < θ)).card : ℝ) =
      (rkK (K := K) L : ℝ) -
        (rkK (K := K) (hnStep (realizeHLat b X) L ((θ - slopeNormalisingConstant K) / 2)) : ℝ) := by
  let dK := Module.finrank ℚ K
  have hdK : 0 < dK := Module.finrank_pos
  have hdKR : (0 : ℝ) < (dK : ℝ) := Nat.cast_pos.mpr hdK
  have hLat := (place_lattice_structure b X hX L hL).1
  have hrk : Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L = rkK (K := K) L * dK := by
    rw [(place_lattice_structure b X hX L hL).2, mul_comm]; rfl
  let f : Fin (rkK (K := K) L * dK) → ℝ :=
    fun j => hnSlopeList (realizeHLat b X) L (Fin.cast hrk.symm j)
  have hbc := hnSlopeList_block_const b X hX L hL
  let θ₀ := (θ - slopeNormalisingConstant K) / 2
  have hflt : (Finset.univ.filter (fun a : Fin (rkK (K := K) L) =>
      hnSlopeListK b X hX L hL a < θ)).card =
      (Finset.univ.filter (fun a : Fin (rkK (K := K) L) =>
        f ⟨a.1 * dK, by nlinarith [a.2]⟩ < θ₀)).card := by
    refine congrArg Finset.card (Finset.filter_congr fun a _ => ?_)
    simp only [hnSlopeListK, f, θ₀, Fin.cast_mk, dK]
    constructor <;> intro h <;> linarith
  have hcard_all := card_filter_lt_block_const hdK f hbc θ₀
  have hbij : (Finset.univ.filter (fun j : Fin (rkK (K := K) L * dK) => f j < θ₀)).card =
      (Finset.univ.filter (fun j : Fin (Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L) =>
        hnSlopeList (realizeHLat b X) L j < θ₀)).card := by
    refine Finset.card_bij (fun j _ => Fin.cast hrk.symm j)
      (fun j hj => by rw [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, hj.2⟩)
      (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun j hj => ⟨Fin.cast hrk j, by
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_univ _, by simpa [f] using hj.2⟩, by ext; rfl⟩)
  have hclt := card_hnSlopeList_lt (realizeHLat b X) hLat θ₀
  have hstep_fg : (hnStep (realizeHLat b X) L θ₀).FG :=
    Submodule.FG.of_le hL (hnStep_spec _ hLat θ₀).1.1
  have hstep_rk := (place_lattice_structure b X hX (hnStep (realizeHLat b X) L θ₀) hstep_fg).2
  have hcast : (dK : ℝ) * ((Finset.univ.filter (fun a : Fin (rkK (K := K) L) =>
      hnSlopeListK b X hX L hL a < θ)).card : ℝ) =
      (dK : ℝ) * ((rkK (K := K) L : ℝ) -
        (rkK (K := K) (hnStep (realizeHLat b X) L θ₀) : ℝ)) := by
    rw [hflt]
    have h1 : (dK : ℝ) * ((Finset.univ.filter (fun a : Fin (rkK (K := K) L) =>
        f ⟨a.1 * dK, by nlinarith [a.2]⟩ < θ₀)).card : ℝ) =
        ((Finset.univ.filter (fun j : Fin (Stage14M2_HNFiltAndFrame.rk (realizeHLat b X) L) =>
          hnSlopeList (realizeHLat b X) L j < θ₀)).card : ℝ) := by
      rw [← hbij, hcard_all]; push_cast; rfl
    rw [h1, hclt, hrk, hstep_rk]
    change ((rkK (K := K) L * dK : ℕ) : ℝ) - ((dK * rkK (K := K) (hnStep (realizeHLat b X) L θ₀) : ℕ) : ℝ) = _
    push_cast; ring
  exact mul_left_cancel₀ hdKR.ne' hcast

end HLatKRankHN

end KRankHNSlopes

/-! ## Section 3: `RamificationLinearCase` — Ideal-Twist Geometry & Ramified Bost Slope Bounds -/

section RamificationLinearCaseSection

section IdealTwistExact

open nonZeroDivisors

variable {K V ι : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

/-- Nonzero ideal twist preserves non-triviality (`L ≠ ⊥ → 𝔟 ≠ ⊥ → 𝔟 • L ≠ ⊥`). -/
lemma ideal_smul_ne_bot {L : Submodule (𝓞 K) V} {𝔟 : Ideal (𝓞 K)}
    (hL0 : L ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) : 𝔟 • L ≠ ⊥ := by
  obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔟
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  intro hbot
  have hmem : α • x ∈ 𝔟 • L := Submodule.smul_mem_smul hα hx
  rw [hbot, Submodule.mem_bot] at hmem
  have hK : (algebraMap (𝓞 K) K α) • x = 0 := by rwa [algebraMap_smul]
  have hαK : algebraMap (𝓞 K) K α ≠ 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hα0
  exact hx0 ((smul_eq_zero.mp hK).resolve_left hαK)

/-- **Dedekind-Domain Ideal-Division Bijection (`exists_ideal_quot_submodule`)**:
for any nonzero ideal `𝔟 ≤ 𝓞 K` and any `𝓞 K`-submodules `N ≤ 𝔟 • L`, there exists a unique
`𝓞 K`-submodule `M ≤ L` such that `𝔟 • M = N`! -/
theorem exists_ideal_quot_submodule {L N : Submodule (𝓞 K) V} {𝔟 : Ideal (𝓞 K)}
    (h𝔟 : 𝔟 ≠ ⊥) (hN : N ≤ 𝔟 • L) :
    ∃ M : Submodule (𝓞 K) V, M ≤ L ∧ 𝔟 • M = N := by
  let 𝔟F : FractionalIdeal (𝓞 K)⁰ K := (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
  have h𝔟F0 : 𝔟F ≠ 0 := by
    intro h0; apply h𝔟
    exact (FractionalIdeal.coeIdeal_eq_zero (I := 𝔟)).mp h0
  let 𝔟Inv : FractionalIdeal (𝓞 K)⁰ K := 𝔟F⁻¹
  have hmul_one : 𝔟F * 𝔟Inv = 1 := mul_inv_cancel₀ h𝔟F0
  have hmul_one' : 𝔟Inv * 𝔟F = 1 := inv_mul_cancel₀ h𝔟F0
  let M : Submodule (𝓞 K) V :=
    { carrier := {x : V | ∀ r ∈ 𝔟, r • x ∈ N}
      zero_mem' := fun r _ => by simp
      add_mem' := fun {x y} hx hy r hr => by rw [smul_add]; exact N.add_mem (hx r hr) (hy r hr)
      smul_mem' := fun a {x} hx r hr => by
        rw [smul_comm]; exact N.smul_mem a (hx r hr) }
  have hML : M ≤ L := by
    intro x hxM
    have hkey : ∀ t ∈ (𝔟Inv * 𝔟F : FractionalIdeal (𝓞 K)⁰ K), t • x ∈ L := by
      intro t ht
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro η hη r hr
        obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hr
        have hr₀x : r₀ • x ∈ 𝔟 • L := hN (hxM r₀ hr₀)
        have h_eta_mem : ∀ y ∈ 𝔟 • L, η • y ∈ L := by
          intro y hy
          refine Submodule.smul_induction_on hy ?_ ?_
          · intro s hs z hz
            have hsF : (algebraMap (𝓞 K) K s) ∈ 𝔟F := (FractionalIdeal.mem_coeIdeal _).mpr ⟨s, hs, rfl⟩
            have hprod := FractionalIdeal.mul_mem_mul hη hsF
            rw [hmul_one'] at hprod
            obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
            have heq : η • (s • z) = c • z := by
              rw [← algebraMap_smul K s z, smul_smul, ← hc, algebraMap_smul]
            rw [heq]; exact L.smul_mem c hz
          · intro y₁ y₂ hy₁ hy₂; rw [smul_add]; exact L.add_mem hy₁ hy₂
        have heq : (η * algebraMap (𝓞 K) K r₀) • x = η • (r₀ • x) := by
          rw [mul_smul, algebraMap_smul]
        rw [heq]
        exact h_eta_mem (r₀ • x) hr₀x
      · intro t₁ t₂ ht₁ ht₂; rw [add_smul]; exact L.add_mem ht₁ ht₂
    have h1 : (1 : K) ∈ (𝔟Inv * 𝔟F : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hmul_one']; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, by simp⟩
    simpa using hkey 1 h1
  have h𝔟M : 𝔟 • M = N := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      intro r hr x hxM
      exact hxM r hr
    · intro y hyN
      have hkey : ∀ t ∈ (𝔟F * 𝔟Inv : FractionalIdeal (𝓞 K)⁰ K), t • y ∈ 𝔟 • M := by
        intro t ht
        rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
        refine Submodule.mul_induction_on ht ?_ ?_
        · intro r hr η hη
          obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hr
          have hηy : η • y ∈ M := by
            intro s hs
            have hsF : (algebraMap (𝓞 K) K s) ∈ 𝔟F := (FractionalIdeal.mem_coeIdeal _).mpr ⟨s, hs, rfl⟩
            have hprod := FractionalIdeal.mul_mem_mul hsF hη
            rw [hmul_one] at hprod
            obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
            have heq : s • (η • y) = c • y := by
              rw [← algebraMap_smul K s (η • y), smul_smul, ← hc, algebraMap_smul]
            rw [heq]; exact N.smul_mem c hyN
          have heq : (algebraMap (𝓞 K) K r₀ * η) • y = r₀ • (η • y) := by
            rw [mul_smul, algebraMap_smul]
          rw [heq]
          exact Submodule.smul_mem_smul hr₀ hηy
        · intro t₁ t₂ ht₁ ht₂; rw [add_smul]; exact (𝔟 • M).add_mem ht₁ ht₂
      have h1 : (1 : K) ∈ (𝔟F * 𝔟Inv : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [hmul_one]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, by simp⟩
      simpa using hkey 1 h1
  exact ⟨M, hML, h𝔟M⟩

/-- Exact `degHLat` and `rk` formula for an ideal twist `𝔟 • M`. -/
theorem degHLat_ideal_twist (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    ArakelovCovolume.rk (zRealize b X (𝔟 • M)) = ArakelovCovolume.rk (zRealize b X M) ∧
    degHLat b X (𝔟 • M) = degHLat b X M -
      (rkK (K := K) M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  have h𝔟M_fg : (𝔟 • M).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hM
  haveI : DiscreteTopology (zRealize b X M) := discreteTopology_zRealize_of_fg b X hX M hM
  have hrkK : rkK (K := K) (𝔟 • M) = rkK (K := K) M := by
    unfold rkK; rw [twist_span_smul M 𝔟 h𝔟]
  have hrkZ : ArakelovCovolume.rk (zRealize b X (𝔟 • M)) =
      ArakelovCovolume.rk (zRealize b X M) := by
    rw [rk_zRealize_eq b X hX (𝔟 • M) h𝔟M_fg, rk_zRealize_eq b X hX M hM, hrkK]
  refine ⟨hrkZ, ?_⟩
  have hdeg := Stage11BostDworkSqueeze.degAr_eq_degAr_sub_log_index
    (zRealize_mono b X (Submodule.smul_le_right : 𝔟 • M ≤ M)) hrkZ
  have hidx : Stage11BostDworkSqueeze.latIndex (zRealize b X M) (zRealize b X (𝔟 • M)) =
      (𝔟 • M).toAddSubgroup.relIndex M.toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective (𝔟 • M).toAddSubgroup M.toAddSubgroup
      (realizeHLat_injective b X hX)
  rw [hidx, twist_index M hM 𝔟 h𝔟, Nat.cast_pow, Real.log_pow] at hdeg
  exact hdeg

/-- **Exact Ideal-Twist Slope Shift (`ramified_ideal_twist_invariants`)**:
twisting any finitely generated nonzero `𝓞 K`-lattice `L` by a nonzero ideal `𝔟 ≤ 𝓞 K` shifts
ALL three normalized slopes (`muDef`, `muMaxDef`, `muMinDef`) identically by
`-(2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)`! -/
theorem ramified_ideal_twist_invariants [StarRing K] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    let δ𝔟 : ℝ := (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ)
    Stage14M2_HLatNumberField.muDef b X (𝔟 • L) = Stage14M2_HLatNumberField.muDef b X L - δ𝔟 ∧
    Stage14M2_HLatNumberField.muMaxDef b X (𝔟 • L) = Stage14M2_HLatNumberField.muMaxDef b X L - δ𝔟 ∧
    Stage14M2_HLatNumberField.muMinDef b X (𝔟 • L) = Stage14M2_HLatNumberField.muMinDef b X L - δ𝔟 := by
  intro δ𝔟
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  have h𝔟L_fg : (𝔟 • L).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hL
  have h𝔟L0 : 𝔟 • L ≠ ⊥ := ideal_smul_ne_bot hL0 h𝔟
  have hn_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hshift_sub : ∀ M : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ →
      slopeHLat b X (𝔟 • M) = slopeHLat b X M - Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    intro M hM hM0
    obtain ⟨hrk, hdeg⟩ := degHLat_ideal_twist b X hX M hM 𝔟 h𝔟
    haveI : DiscreteTopology (zRealize b X M) := discreteTopology_zRealize_of_fg b X hX M hM
    have hrk_pos : 0 < ArakelovCovolume.rk (zRealize b X M) :=
      ArakelovCovolume.rk_pos_of_ne_bot _ (by
        intro hbot; apply hM0; rw [eq_bot_iff]; intro x hx
        have hm : realizeHLat b X x ∈ zRealize b X M := ⟨x, hx, rfl⟩
        rw [hbot, Submodule.mem_bot] at hm
        exact realizeHLat_injective b X hX (hm.trans (map_zero _).symm))
    have hrk_eq : (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
        (Module.finrank ℚ K : ℝ) * (rkK (K := K) M : ℝ) := by
      rw [rk_zRealize_eq b X hX M hM]; push_cast; rfl
    have hrk_ne : (ArakelovCovolume.rk (zRealize b X M) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hrk_pos.ne'
    unfold slopeHLat ArakelovCovolume.slope
    change degHLat b X (𝔟 • M) / (ArakelovCovolume.rk (zRealize b X (𝔟 • M)) : ℝ) =
      degHLat b X M / (ArakelovCovolume.rk (zRealize b X M) : ℝ) -
        Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ)
    rw [hrk_eq] at hrk_ne
    have hrkM_ne : (rkK (K := K) M : ℝ) ≠ 0 := right_ne_zero_of_mul hrk_ne
    rw [hrk, hdeg, hrk_eq]
    field_simp [hrkM_ne, hn_pos.ne']
  -- 1. `muDef` shift
  have hmu : Stage14M2_HLatNumberField.muDef b X (𝔟 • L) =
      Stage14M2_HLatNumberField.muDef b X L - δ𝔟 := by
    unfold Stage14M2_HLatNumberField.muDef
    rw [hshift_sub L hL hL0]
    dsimp only [δ𝔟]; ring
  -- 2. `muMaxDef` shift
  have hmuMaxO : muMaxO b X (𝔟 • L) =
      muMaxO b X L - Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    apply le_antisymm
    · rw [muMaxO_char b X hX (𝔟 • L) h𝔟L_fg h𝔟L0]
      intro N hNL
      obtain ⟨M, hML, rfl⟩ := exists_ideal_quot_submodule h𝔟 hNL
      have hMfg : M.FG := Submodule.FG.of_le hL hML
      obtain ⟨hrk, hdeg⟩ := degHLat_ideal_twist b X hX M hMfg 𝔟 h𝔟
      have hmax := (muMaxO_char b X hX L hL hL0 (muMaxO b X L)).mp le_rfl M hML
      have hrk_eq : (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
          (Module.finrank ℚ K : ℝ) * (rkK (K := K) M : ℝ) := by
        rw [rk_zRealize_eq b X hX M hMfg]; push_cast; rfl
      rw [hrk, hdeg]
      have halg : (Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ)) *
          (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
          (rkK (K := K) M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
        rw [hrk_eq]; field_simp [hn_pos.ne']
      linarith
    · have hle : muMaxO b X L ≤ muMaxO b X (𝔟 • L) +
          Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ) := by
        rw [muMaxO_char b X hX L hL hL0]
        intro M hML
        have hMfg : M.FG := Submodule.FG.of_le hL hML
        obtain ⟨hrk, hdeg⟩ := degHLat_ideal_twist b X hX M hMfg 𝔟 h𝔟
        have hmax := (muMaxO_char b X hX (𝔟 • L) h𝔟L_fg h𝔟L0 (muMaxO b X (𝔟 • L))).mp
          le_rfl (𝔟 • M) (Submodule.smul_mono le_rfl hML)
        have hrk_eq : (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
            (Module.finrank ℚ K : ℝ) * (rkK (K := K) M : ℝ) := by
          rw [rk_zRealize_eq b X hX M hMfg]; push_cast; rfl
        rw [hrk, hdeg] at hmax
        have halg : (Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ)) *
            (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
            (rkK (K := K) M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
          rw [hrk_eq]; field_simp [hn_pos.ne']
        linarith
      linarith
  have hmuMax : Stage14M2_HLatNumberField.muMaxDef b X (𝔟 • L) =
      Stage14M2_HLatNumberField.muMaxDef b X L - δ𝔟 := by
    unfold Stage14M2_HLatNumberField.muMaxDef
    rw [hmuMaxO]; dsimp only [δ𝔟]; ring
  -- 3. `muMinDef` shift
  have hmuMinO : muMinO b X (𝔟 • L) =
      muMinO b X L - Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    obtain ⟨hrkL, hdegL⟩ := degHLat_ideal_twist b X hX L hL 𝔟 h𝔟
    have hrkL_eq : (ArakelovCovolume.rk (zRealize b X L) : ℝ) =
        (Module.finrank ℚ K : ℝ) * (rkK (K := K) L : ℝ) := by
      rw [rk_zRealize_eq b X hX L hL]; push_cast; rfl
    apply le_antisymm
    · have hle : muMinO b X (𝔟 • L) +
          Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ muMinO b X L := by
        rw [muMinO_char b X hX L hL hL0]
        intro M hML
        have hMfg : M.FG := Submodule.FG.of_le hL hML
        obtain ⟨hrkM, hdegM⟩ := degHLat_ideal_twist b X hX M hMfg 𝔟 h𝔟
        have hmin := (muMinO_char b X hX (𝔟 • L) h𝔟L_fg h𝔟L0 (muMinO b X (𝔟 • L))).mp
          le_rfl (𝔟 • M) (Submodule.smul_mono le_rfl hML)
        have hrkM_eq : (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
            (Module.finrank ℚ K : ℝ) * (rkK (K := K) M : ℝ) := by
          rw [rk_zRealize_eq b X hX M hMfg]; push_cast; rfl
        rw [hrkL, hdegL, hrkM, hdegM] at hmin
        have halg : (Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ)) *
            ((ArakelovCovolume.rk (zRealize b X L) : ℝ) - (ArakelovCovolume.rk (zRealize b X M) : ℝ)) =
            ((rkK (K := K) L : ℝ) - (rkK (K := K) M : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
          rw [hrkL_eq, hrkM_eq]; field_simp [hn_pos.ne']
        linarith
      linarith
    · rw [muMinO_char b X hX (𝔟 • L) h𝔟L_fg h𝔟L0]
      intro N hNL
      obtain ⟨M, hML, rfl⟩ := exists_ideal_quot_submodule h𝔟 hNL
      have hMfg : M.FG := Submodule.FG.of_le hL hML
      obtain ⟨hrkM, hdegM⟩ := degHLat_ideal_twist b X hX M hMfg 𝔟 h𝔟
      have hmin := (muMinO_char b X hX L hL hL0 (muMinO b X L)).mp le_rfl M hML
      have hrkM_eq : (ArakelovCovolume.rk (zRealize b X M) : ℝ) =
          (Module.finrank ℚ K : ℝ) * (rkK (K := K) M : ℝ) := by
        rw [rk_zRealize_eq b X hX M hMfg]; push_cast; rfl
      rw [hrkL, hdegL, hrkM, hdegM]
      have halg : (Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ)) *
          ((ArakelovCovolume.rk (zRealize b X L) : ℝ) - (ArakelovCovolume.rk (zRealize b X M) : ℝ)) =
          ((rkK (K := K) L : ℝ) - (rkK (K := K) M : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
        rw [hrkL_eq, hrkM_eq]; field_simp [hn_pos.ne']
      linarith
  have hmuMin : Stage14M2_HLatNumberField.muMinDef b X (𝔟 • L) =
      Stage14M2_HLatNumberField.muMinDef b X L - δ𝔟 := by
    unfold Stage14M2_HLatNumberField.muMinDef
    rw [hmuMinO]; dsimp only [δ𝔟]; ring
  exact ⟨hmu, hmuMax, hmuMin⟩

/-- **Prime-Power Ramification Decomposition (`ramified_prime_prod_shift`)**:
for a ramification divisor `𝔟 = ∏ j ∈ s, (𝔭 j) ^ (e j)` of nonzero ideals `𝔭 j ≤ 𝓞 K`,
the normalized slope shift decomposes linearly over the ramified primes:
`muDef (𝔟 • L) = muDef L - (2 / [K : ℚ]) * ∑ j ∈ s, (e j : ℝ) * log (Ideal.absNorm (𝔭 j))`. -/
theorem ramified_prime_prod_shift [StarRing K] {J : Type*} (s : Finset J)
    (𝔭 : J → Ideal (𝓞 K)) (e : J → ℕ) (h𝔭 : ∀ j ∈ s, 𝔭 j ≠ ⊥)
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    let 𝔟 : Ideal (𝓞 K) := ∏ j ∈ s, 𝔭 j ^ e j
    Stage14M2_HLatNumberField.muDef b X (𝔟 • L) =
      Stage14M2_HLatNumberField.muDef b X L -
        (2 / (Module.finrank ℚ K : ℝ)) *
          ∑ j ∈ s, (e j : ℝ) * Real.log (Ideal.absNorm (𝔭 j) : ℝ) := by
  intro 𝔟
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    change (∏ j ∈ s, 𝔭 j ^ e j : Ideal (𝓞 K)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero (e j) (show 𝔭 j ≠ 0 from h𝔭 j hj)
  have hinv := (ramified_ideal_twist_invariants b X hX L hL hL0 𝔟 h𝔟0).1
  have hnorm : (Ideal.absNorm 𝔟 : ℝ) = ∏ j ∈ s, (Ideal.absNorm (𝔭 j) : ℝ) ^ e j := by
    dsimp only [𝔟]
    rw [map_prod]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, Nat.cast_pow]
  have hpos : ∀ j ∈ s, (Ideal.absNorm (𝔭 j) : ℝ) ^ e j ≠ 0 := fun j hj =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr fun h0 => h𝔭 j hj (Ideal.absNorm_eq_zero_iff.mp h0))
  rw [hinv, hnorm, Real.log_prod hpos]
  congr 2
  refine Finset.sum_congr rfl fun j _ => Real.log_pow _ _

/-- **Combined Ramified Ideal Twist + Multi-Place Archimedean Rescaling Formula**:
over a totally complex number field `K`, simultaneously twisting `L ↦ 𝔟 • L` (`𝔟 ≠ ⊥`) and
rescaling archimedean frames `X v ↦ (c v : ℂ) • X v` (`c v > 0`) shifts all three slopes
`muDef`, `muMaxDef`, `muMinDef` linearly by
`(2 / nPl K) * ∑ v, log (c v) - (2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)`. -/
theorem ramified_twist_and_rescale_slope [IsTotallyComplex K] [StarRing K]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (c : InfinitePlace K → ℝ) (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    let shift : ℝ := (2 / (nPl K : ℝ)) * (∑ v : InfinitePlace K, Real.log (c v)) -
      (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ)
    Stage14M2_HLatNumberField.muDef b (fun v => (c v : ℂ) • X v) (𝔟 • L) =
      Stage14M2_HLatNumberField.muDef b X L + shift ∧
    Stage14M2_HLatNumberField.muMaxDef b (fun v => (c v : ℂ) • X v) (𝔟 • L) =
      Stage14M2_HLatNumberField.muMaxDef b X L + shift ∧
    Stage14M2_HLatNumberField.muMinDef b (fun v => (c v : ℂ) • X v) (𝔟 • L) =
      Stage14M2_HLatNumberField.muMinDef b X L + shift := by
  intro shift
  have hXc : ∀ v, IsUnit (((c v : ℂ)) • X v).det := fun v => by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : (c v : ℂ) ≠ 0)).pow _).mul (hX v)
  have h1 := ramified_ideal_twist_invariants b (fun v => (c v : ℂ) • X v) hXc L hL hL0 𝔟 h𝔟
  have h2 := twist_invariance b X c hX hc L hL hL0
  dsimp only at h2
  simp only [muDef_eq_hnMuDef, muMaxDef_eq_hnMuMaxDef, muMinDef_eq_hnMuMinDef] at h1 ⊢
  unfold Stage14M2_HNFiltAndFrame.muDef Stage14M2_HNFiltAndFrame.muMaxDef
    Stage14M2_HNFiltAndFrame.muMinDef at h1 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [h1.1, h2.2.2]; dsimp only [shift]; ring
  · rw [h1.2.1, h2.1]; dsimp only [shift]; ring
  · rw [h1.2.2, h2.2.1]; dsimp only [shift]; ring

end IdealTwistExact

/-- **Ramified Linear-Case Data (`RamificationLinearCase`)**:
packages a ramified `K`-linear morphism `φ : A.V →ₗ[K] B.V` between good CM Hermitian lattices
`A, B : HLat K` whose image lands in a ramified ideal twist `𝔟 • B.L` (`𝔟 ≠ ⊥`). -/
structure RamificationLinearCase (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] where
  src : HLat K
  dst : HLat K
  src_good : src.Good
  dst_good : dst.Good
  src_ne_bot : src.L ≠ ⊥
  dst_ne_bot : dst.L ≠ ⊥
  ramIdeal : Ideal (𝓞 K)
  ramIdeal_ne_bot : ramIdeal ≠ ⊥
  φ : src.V →ₗ[K] dst.V
  maps_into_ram : src.L.map (φ.restrictScalars (𝓞 K)) ≤ ramIdeal • dst.L

namespace RamificationLinearCase

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- Normalized ramification slope gain `(2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)`. -/
def ramGain (R : RamificationLinearCase K) : ℝ :=
  (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm R.ramIdeal : ℝ)

lemma ramGain_nonneg (R : RamificationLinearCase K) : 0 ≤ R.ramGain := by
  unfold ramGain
  have h1 : 1 ≤ Ideal.absNorm R.ramIdeal :=
    Nat.one_le_iff_ne_zero.mpr fun h => R.ramIdeal_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hlog : 0 ≤ Real.log (Ideal.absNorm R.ramIdeal : ℝ) :=
    Real.log_nonneg (by exact_mod_cast h1)
  positivity

/-- **Ramified Linear-Case Bost Slope Inequality (Nonzero Image)**:
if `φ(src.L) ≠ ⊥`, then `src.muMin + ramGain ≤ dst.muMax + htMap φ`! -/
theorem slope_ineq_of_ne_bot (R : RamificationLinearCase K)
    (hφ : R.src.L.map (R.φ.restrictScalars (𝓞 K)) ≠ ⊥) :
    R.src.muMin + R.ramGain ≤
      R.dst.muMax + htMap R.src.b R.src.X R.dst.b R.dst.X R.φ := by
  have h𝔟L_fg : (R.ramIdeal • R.dst.L).FG :=
    Submodule.FG.smul (IsNoetherian.noetherian R.ramIdeal) R.dst_good.2.1
  have hsi := (slope_inequality_mean R.src.b R.src.X R.dst.b R.dst.X R.src_good.1 R.dst_good.1
    R.φ R.src.L R.src_good.2.1 hφ).2 (R.ramIdeal • R.dst.L) h𝔟L_fg R.maps_into_ram
  have htw := (ramified_ideal_twist_invariants R.dst.b R.dst.X R.dst_good.1
    R.dst.L R.dst_good.2.1 R.dst_ne_bot R.ramIdeal R.ramIdeal_ne_bot).2.1
  change Stage14M2_HLatNumberField.muMinDef R.src.b R.src.X R.src.L + R.ramGain ≤
    Stage14M2_HLatNumberField.muMaxDef R.dst.b R.dst.X R.dst.L +
      htMap R.src.b R.src.X R.dst.b R.dst.X R.φ
  rw [muMinDef_eq_hnMuMinDef, muMaxDef_eq_hnMuMaxDef]
  rw [muMaxDef_eq_hnMuMaxDef, muMaxDef_eq_hnMuMaxDef] at htw
  unfold ramGain
  linarith

/-- **Ramified Linear-Case Bost Slope Inequality (Injective Morphism)**:
if `φ` is injective, then BOTH `src.mu + ramGain ≤ dst.muMax + htMap φ` AND
`src.muMax + ramGain ≤ dst.muMax + htMap φ`! -/
theorem slope_ineq_of_injective (R : RamificationLinearCase K)
    (hinj : Function.Injective R.φ) :
    R.src.mu + R.ramGain ≤ R.dst.muMax + htMap R.src.b R.src.X R.dst.b R.dst.X R.φ ∧
    R.src.muMax + R.ramGain ≤ R.dst.muMax + htMap R.src.b R.src.X R.dst.b R.dst.X R.φ := by
  have h𝔟L_fg : (R.ramIdeal • R.dst.L).FG :=
    Submodule.FG.smul (IsNoetherian.noetherian R.ramIdeal) R.dst_good.2.1
  have htw := (ramified_ideal_twist_invariants R.dst.b R.dst.X R.dst_good.1
    R.dst.L R.dst_good.2.1 R.dst_ne_bot R.ramIdeal R.ramIdeal_ne_bot).2.1
  -- Apply `slope_ineq_of_ne_bot` to the maximal destabilizing submodule of `src.L`!
  have hLat := (place_lattice_structure R.src.b R.src.X R.src_good.1 R.src.L R.src_good.2.1).1
  obtain ⟨Nmax, hNsat, hN0, hNslope⟩ :=
    (Stage14M2_HNFiltAndFrame.muChar_spec (realizeHLat R.src.b R.src.X) hLat R.src_ne_bot).2.2.1
  have hNfg : Nmax.FG := Submodule.FG.of_le R.src_good.2.1 hNsat.1
  have hNmap0 : Nmax.map (R.φ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0; apply hN0; rw [eq_bot_iff]; intro x hx
    have hm : R.φ x ∈ Nmax.map (R.φ.restrictScalars (𝓞 K)) := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact hinj (hm.trans (map_zero R.φ).symm)
  -- `Nmax` is semistable (its `muMin` equals its `slope = muMax L`)!
  have hNmuMin : Stage14M2_HNFiltAndFrame.muMin (realizeHLat R.src.b R.src.X) Nmax =
      Stage14M2_HNFiltAndFrame.muMax (realizeHLat R.src.b R.src.X) R.src.L := by
    have hLatN := (place_lattice_structure R.src.b R.src.X R.src_good.1 Nmax hNfg).1
    have hchar := Stage14M2_HNFiltAndFrame.muChar_spec (realizeHLat R.src.b R.src.X) hLatN hN0
    have hcharL := Stage14M2_HNFiltAndFrame.muChar_spec (realizeHLat R.src.b R.src.X) hLat R.src_ne_bot
    apply le_antisymm
    · calc Stage14M2_HNFiltAndFrame.muMin (realizeHLat R.src.b R.src.X) Nmax
          ≤ Stage14M2_HNFiltAndFrame.slope (realizeHLat R.src.b R.src.X) Nmax := hchar.2.2.2.1
        _ = Stage14M2_HNFiltAndFrame.muMax (realizeHLat R.src.b R.src.X) R.src.L := hNslope
    · rw [hchar.2.1]
      intro M hMN
      have hMdeg := (hcharL.1 (Stage14M2_HNFiltAndFrame.muMax (realizeHLat R.src.b R.src.X) R.src.L)).mp
        le_rfl M (hMN.trans hNsat.1)
      have hrkN_pos : (0 : ℝ) < (Stage14M2_HNFiltAndFrame.rk (realizeHLat R.src.b R.src.X) Nmax : ℝ) := by
        haveI : DiscreteTopology (zl (realizeHLat R.src.b R.src.X) Nmax) := hLatN.2
        exact Nat.cast_pos.mpr (ArakelovCovolume.rk_pos_of_ne_bot _ (by
          intro hbot; apply hN0; rw [eq_bot_iff]; intro x hx
          have hm : realizeHLat R.src.b R.src.X x ∈ zl (realizeHLat R.src.b R.src.X) Nmax := ⟨x, hx, rfl⟩
          rw [hbot, Submodule.mem_bot] at hm
          exact realizeHLat_injective R.src.b R.src.X R.src_good.1 (hm.trans (map_zero _).symm)))
      have hNdeg : Stage14M2_HNFiltAndFrame.deg (realizeHLat R.src.b R.src.X) Nmax =
          Stage14M2_HNFiltAndFrame.muMax (realizeHLat R.src.b R.src.X) R.src.L *
            (Stage14M2_HNFiltAndFrame.rk (realizeHLat R.src.b R.src.X) Nmax : ℝ) := by
        rw [← hNslope]
        unfold Stage14M2_HNFiltAndFrame.slope ArakelovCovolume.slope
        exact (div_mul_cancel₀ _ hrkN_pos.ne').symm
      linarith
  have hsi := (slope_inequality_mean R.src.b R.src.X R.dst.b R.dst.X R.src_good.1 R.dst_good.1
    R.φ Nmax hNfg hNmap0).2 (R.ramIdeal • R.dst.L) h𝔟L_fg
    ((Submodule.map_mono hNsat.1).trans R.maps_into_ram)
  have hmuMax_bound : R.src.muMax + R.ramGain ≤
      R.dst.muMax + htMap R.src.b R.src.X R.dst.b R.dst.X R.φ := by
    change Stage14M2_HLatNumberField.muMaxDef R.src.b R.src.X R.src.L + R.ramGain ≤
      Stage14M2_HLatNumberField.muMaxDef R.dst.b R.dst.X R.dst.L +
        htMap R.src.b R.src.X R.dst.b R.dst.X R.φ
    rw [muMaxDef_eq_hnMuMaxDef, muMaxDef_eq_hnMuMaxDef]
    rw [muMaxDef_eq_hnMuMaxDef, muMaxDef_eq_hnMuMaxDef] at htw
    unfold Stage14M2_HNFiltAndFrame.muMinDef at hsi
    rw [hNmuMin] at hsi
    unfold Stage14M2_HNFiltAndFrame.muMaxDef at hsi htw ⊢
    unfold ramGain
    linarith
  have hsand := (muMinDef_le_muDef_le_muMaxDef R.src.b R.src.X R.src_good.1 R.src.L
    R.src_good.2.1 R.src_ne_bot).2
  unfold HLat.mu HLat.muMax at hmuMax_bound ⊢
  exact ⟨by linarith, hmuMax_bound⟩

/-- **Ramified Dual-Target Pairing Inequality (`ramificationLinearCase_dual_RR`)**:
when `dst = dualHLat RR` (`RR^∨`), the ramified linear-case Bost inequality becomes
`src.muMin + ramGain ≤ -RR.muMin + htMap φ` (and `src.muMax + ramGain ≤ -RR.muMin + htMap φ`
for injective `φ`)! -/
theorem dual_target_slope_ineq (RR : HLat K) (hRR : RR.Good) (hRR_rk : 0 < RR.rank)
    (R : RamificationLinearCase K) (hdst : R.dst = dualHLat RR)
    (hinj : Function.Injective R.φ) :
    R.src.mu + R.ramGain ≤ -RR.muMin + htMap R.src.b R.src.X R.dst.b R.dst.X R.φ ∧
    R.src.muMax + R.ramGain ≤ -RR.muMin + htMap R.src.b R.src.X R.dst.b R.dst.X R.φ := by
  have h1 := R.slope_ineq_of_injective hinj
  have hdual : R.dst.muMax = -RR.muMin := by
    rw [hdst]; exact (hlat_duality_slope_neg RR hRR hRR_rk).2.1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

end RamificationLinearCase

/-- **Ramified Linear-Case Divisible Bost Inequality on `Stage14Contracts.HLatAnchor`**:
exact discharge of the `HLatAnchor` divisible slope inequality. -/
theorem ramificationLinearCase_anchor
    (L_N L_RR : HLatAnchor) (φ : L_N.L →ₗ[ℤ] L_RR.L) (C_op : ℝ) (D_div : ℕ)
    (hD : 0 < D_div) (hφ : Function.Injective φ)
    (hC : ∀ x : L_N.L, ‖((φ x : L_RR.L) : L_RR.E)‖ ≤ C_op * ‖(x : L_N.E)‖)
    (hDiv : ∀ x : L_N.L, ∃ y : L_RR.L, φ x = (D_div : ℤ) • y) :
    L_N.slope + Real.log (D_div : ℝ) ≤ L_RR.muMax + Real.log C_op :=
  ArakelovCovolume.bost_slope_inequality_divisible L_N.L L_RR.L L_N.ne_bot φ C_op D_div hD hφ hC hDiv

end RamificationLinearCaseSection

/-! ## Section 4: `FlatLatticeTheorem` — Flatness Bounds & Banaszczyk HN Geometry -/

section FlatLatticeSection

/-- A Hermitian lattice `A : HLat K` is **`H`-flat** if its normalized Harder–Narasimhan
slope spread satisfies `A.muMax - A.muMin ≤ H`. -/
def IsFlatHLat {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) (H : ℝ) : Prop :=
  A.muMax - A.muMin ≤ H

/-- **Parabolic Convexity Bound for Descending Lists (`antitone_partial_sum_parabolic_bound`)**:
for any antitone list `f : Fin r → ℝ` (`0 < r`) with average `μ = (∑ j, f j) / r` and spread
`f 0 - f (r - 1) ≤ Δ`, every partial sum `S_k = ∑_{j < k} f j` (`k ≤ r`) satisfies the sharp
parabolic envelope:
`0 ≤ S_k - k * μ ≤ Δ * (k * (r - k) / r)`! -/
theorem antitone_partial_sum_parabolic_bound {r : ℕ} (hr : 0 < r) (f : Fin r → ℝ)
    (hf : Antitone f) {Δ : ℝ} (hΔ : f ⟨0, hr⟩ - f ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ ≤ Δ)
    (k : ℕ) (hk : k ≤ r) :
    let μ : ℝ := (∑ j : Fin r, f j) / (r : ℝ)
    let Sk : ℝ := ∑ j : Fin r, if j.1 < k then f j else 0
    0 ≤ Sk - (k : ℝ) * μ ∧
    Sk - (k : ℝ) * μ ≤ Δ * ((k : ℝ) * ((r : ℝ) - (k : ℝ)) / (r : ℝ)) := by
  intro μ Sk
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  let A : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => j.1 < k)
  let B : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => ¬ j.1 < k)
  have hSk_eq : Sk = ∑ j ∈ A, f j := by simp [Sk, A, Finset.sum_filter]
  have hcardA : A.card = k := by
    have hbij : A.card = (Finset.range k).card := by
      refine Finset.card_bij (fun j _ => j.1)
        (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun i hi => ⟨⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hi⟩, rfl⟩)
    rw [hbij, Finset.card_range]
  have hdisj : Disjoint A B := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have hunion : A ∪ B = Finset.univ := by
    ext j; simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; exact iff_true_intro (em _)
  have hcardB : B.card = r - k := by
    have h1 : A.card + B.card = r := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  have hsum_split : ∑ j : Fin r, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) := by
    rw [← Finset.sum_union hdisj, hunion]
  have hrμ : (r : ℝ) * μ = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) := by
    dsimp only [μ]; rw [mul_div_cancel₀ _ hr_pos.ne', hsum_split]
  have hident : (r : ℝ) * (Sk - (k : ℝ) * μ) =
      ((r : ℝ) - (k : ℝ)) * (∑ j ∈ A, f j) - (k : ℝ) * (∑ j ∈ B, f j) := by
    rw [hSk_eq]
    linear_combination -((k : ℝ) * hrμ)
  have hcardB_R : (B.card : ℝ) = (r : ℝ) - (k : ℝ) := by rw [hcardB, Nat.cast_sub hk]
  constructor
  · -- Lower bound `0 ≤ Sk - k * μ`: `B.card * ∑_A f ≥ A.card * ∑_B f` since every `a ∈ A` has `a ≤ b` for `b ∈ B`!
    have hlow : (k : ℝ) * (∑ j ∈ B, f j) ≤ ((r : ℝ) - (k : ℝ)) * (∑ j ∈ A, f j) := by
      rw [← hcardB_R, ← hcardA]
      have h1 : (A.card : ℝ) * (∑ j ∈ B, f j) = ∑ _a ∈ A, ∑ b ∈ B, f b := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : (B.card : ℝ) * (∑ j ∈ A, f j) = ∑ a ∈ A, ∑ _b ∈ B, f a := by
        rw [Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]
      rw [h1, h2]
      refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact hf (show a ≤ b by change a.1 ≤ b.1; omega)
    nlinarith
  · -- Upper bound `Sk - k * μ ≤ Δ * (k * (r - k) / r)`!
    have hA_hi : ∑ j ∈ A, f j ≤ (k : ℝ) * f ⟨0, hr⟩ := by
      calc ∑ j ∈ A, f j ≤ ∑ _j ∈ A, f ⟨0, hr⟩ :=
            Finset.sum_le_sum fun j _ => hf (Nat.zero_le j.1)
        _ = (k : ℝ) * f ⟨0, hr⟩ := by rw [Finset.sum_const, hcardA, nsmul_eq_mul]
    have hB_lo : ((r : ℝ) - (k : ℝ)) * f ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ ≤ ∑ j ∈ B, f j := by
      calc ((r : ℝ) - (k : ℝ)) * f ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩
          = ∑ _j ∈ B, f ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardB_R]
        _ ≤ ∑ j ∈ B, f j := Finset.sum_le_sum fun j _ => hf (by change j.1 ≤ r - 1; omega)
    have hprod : ((r : ℝ) - (k : ℝ)) * (∑ j ∈ A, f j) - (k : ℝ) * (∑ j ∈ B, f j) ≤
        Δ * ((k : ℝ) * ((r : ℝ) - (k : ℝ))) := by
      have hrk_nn : 0 ≤ (r : ℝ) - (k : ℝ) := by
        have : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk
        linarith
      have h1 := mul_le_mul_of_nonneg_left hA_hi hrk_nn
      have h2 := mul_le_mul_of_nonneg_left hB_lo (Nat.cast_nonneg k)
      have h3 := mul_le_mul_of_nonneg_right hΔ (mul_nonneg (Nat.cast_nonneg k) hrk_nn)
      linarith
    have hdiv : (r : ℝ) * (Sk - (k : ℝ) * μ) ≤ (r : ℝ) * (Δ * ((k : ℝ) * ((r : ℝ) - (k : ℝ)) / (r : ℝ))) := by
      rw [hident]
      have heq : (r : ℝ) * (Δ * ((k : ℝ) * ((r : ℝ) - (k : ℝ)) / (r : ℝ))) =
          Δ * ((k : ℝ) * ((r : ℝ) - (k : ℝ))) := by field_simp [hr_pos.ne']
      linarith
    exact le_of_mul_le_mul_left hdiv hr_pos

/-- **Flat-Lattice Parabolic HN-Polygon Bound (`hnPoly_flat_parabolic_bound`)**:
if `A : HLat K` is `H`-flat (`A.muMax - A.muMin ≤ H`), then its Harder–Narasimhan polygon
`hnPoly` deviates from the straight line `k ↦ k * slope A` by at most `(H / 2) * k * (r - k) / r`! -/
theorem hnPoly_flat_parabolic_bound {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    {H : ℝ} (hflat : IsFlatHLat A H) (k : ℕ)
    (hk : k ≤ Stage14M2_HNFiltAndFrame.rk (realizeHLat A.b A.X) A.L) :
    let r := Stage14M2_HNFiltAndFrame.rk (realizeHLat A.b A.X) A.L
    0 ≤ hnPoly (realizeHLat A.b A.X) A.L k -
          (k : ℝ) * Stage14M2_HNFiltAndFrame.slope (realizeHLat A.b A.X) A.L ∧
    hnPoly (realizeHLat A.b A.X) A.L k -
          (k : ℝ) * Stage14M2_HNFiltAndFrame.slope (realizeHLat A.b A.X) A.L ≤
      (H / 2) * ((k : ℝ) * ((r : ℝ) - (k : ℝ)) / (r : ℝ)) := by
  intro r
  have hLat := (place_lattice_structure A.b A.X hG.1 A.L hG.2.1).1
  have hr_pos : 0 < r := by
    haveI : DiscreteTopology A.zRealize := hLat.2
    exact ArakelovCovolume.rk_pos_of_ne_bot A.zRealize (by
      intro hbot; apply hA0; rw [eq_bot_iff]; intro x hx
      have hm : realizeHLat A.b A.X x ∈ A.zRealize := ⟨x, hx, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact realizeHLat_injective A.b A.X hG.1 (hm.trans (map_zero _).symm))
  have hext := hnSlopeList_extremes (realizeHLat A.b A.X) hLat hA0
  have hΔ : hnSlopeList (realizeHLat A.b A.X) A.L ⟨0, hr_pos⟩ -
      hnSlopeList (realizeHLat A.b A.X) A.L ⟨r - 1, Nat.sub_lt hr_pos zero_lt_one⟩ ≤ H / 2 := by
    have h0 := (hext.1 ⟨0, hr_pos⟩).2
    have hlast := (hext.1 ⟨r - 1, Nat.sub_lt hr_pos zero_lt_one⟩).1
    unfold IsFlatHLat HLat.muMax HLat.muMin at hflat
    rw [muMaxDef_eq_hnMuMaxDef, muMinDef_eq_hnMuMinDef] at hflat
    unfold Stage14M2_HNFiltAndFrame.muMaxDef Stage14M2_HNFiltAndFrame.muMinDef at hflat
    linarith
  have hpar := antitone_partial_sum_parabolic_bound hr_pos (hnSlopeList (realizeHLat A.b A.X) A.L)
    (hnSlopeList_antitone (realizeHLat A.b A.X) hLat) hΔ k hk
  have hμ : (∑ j : Fin r, hnSlopeList (realizeHLat A.b A.X) A.L j) / (r : ℝ) =
      Stage14M2_HNFiltAndFrame.slope (realizeHLat A.b A.X) A.L := by
    rw [sum_hnSlopeList (realizeHLat A.b A.X) hLat]; rfl
  rw [hμ] at hpar
  exact hpar

/-- **Unconditional Banaszczyk `O(log r)` Flatness (`flatLattice_of_banaszczyk`)**:
every good nonzero CM Hermitian lattice `A : HLat K` is automatically `H`-flat with
`H = -2 * log (λ₁(A) * λ₁(A*)) + 2 * log ([K : ℚ] * A.rank)` (ZERO LLL!), proved directly via
`Stage14M2_BanaszczykShortBasis.banaszczyk_hh_gap_le`! -/
theorem flatLattice_of_banaszczyk {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    {HH : ℝ}
    (hHH : letI := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1;
      letI := Stage4ArakelovBost.discreteTopology_dualLat A.zRealize;
      -2 * Real.log (Stage2SiegelReduction.lambda1 A.zRealize *
        Stage2SiegelReduction.lambda1 (Stage4ArakelovBost.dualLat A.zRealize)) +
        2 * Real.log ((Module.finrank ℚ K * A.rank : ℕ) : ℝ) ≤ HH) :
    IsFlatHLat A HH := by
  haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  haveI : DiscreteTopology (Stage4ArakelovBost.dualLat A.zRealize) :=
    Stage4ArakelovBost.discreteTopology_dualLat A.zRealize
  have hZ0 : A.zRealize ≠ ⊥ := by
    intro hbot; apply hA0; rw [eq_bot_iff]; intro x hx
    have hm : realizeHLat A.b A.X x ∈ A.zRealize := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact realizeHLat_injective A.b A.X hG.1 (hm.trans (map_zero _).symm)
  have hrk : ArakelovCovolume.rk A.zRealize = Module.finrank ℚ K * A.rank :=
    rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1
  have hgap := (banaszczyk_hh_gap_le A.zRealize hZ0 (HH := HH / 2) (by
    rw [hrk]; linarith)).1
  have hsp := muMaxDef_sub_muMinDef_le_two_mul_zSpread A.b A.X hG.1 A.L hG.2.1 hA0
  unfold IsFlatHLat HLat.muMax HLat.muMin
  linarith

/-- Flatness is preserved identically under Hermitian duality `dualHLat`. -/
theorem flatLattice_dual_invariance {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) (hr : 0 < A.rank) {H : ℝ} :
    IsFlatHLat (dualHLat A) H ↔ IsFlatHLat A H := by
  obtain ⟨_, hmax, hmin⟩ := hlat_duality_slope_neg A hG hr
  unfold IsFlatHLat
  rw [hmax, hmin]
  constructor <;> intro h <;> linarith

/-- Flatness is preserved identically under any nonzero ideal twist `𝔟 • A.L`. -/
theorem flatLattice_ideal_twist_invariance {K : Type} [Field K] [NumberField K]
    [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) {H : ℝ} :
    IsFlatHLat (A.withL (𝔟 • A.L)) H ↔ IsFlatHLat A H := by
  obtain ⟨_, hmax, hmin⟩ := ramified_ideal_twist_invariants A.b A.X hG.1 A.L hG.2.1 hA0 𝔟 h𝔟
  unfold IsFlatHLat HLat.muMax HLat.muMin HLat.withL
  rw [hmax, hmin]
  constructor <;> intro h <;> linarith

/-- Flatness is preserved identically under arbitrary positive archimedean place rescalings. -/
theorem flatLattice_place_rescale_invariance {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v) {H : ℝ} :
    let A' : HLat K := { A with X := fun v => (c v : ℂ) • A.X v }
    IsFlatHLat A' H ↔ IsFlatHLat A H := by
  intro A'
  obtain ⟨hmax, hmin, _⟩ := twist_invariance A.b A.X c hG.1 hc A.L hG.2.1 hA0
  unfold IsFlatHLat HLat.muMax HLat.muMin
  change Stage14M2_HLatNumberField.muMaxDef A.b (fun v => (c v : ℂ) • A.X v) A.L -
      Stage14M2_HLatNumberField.muMinDef A.b (fun v => (c v : ℂ) • A.X v) A.L ≤ H ↔ _
  rw [muMaxDef_eq_hnMuMaxDef, muMinDef_eq_hnMuMinDef, muMaxDef_eq_hnMuMaxDef, muMinDef_eq_hnMuMinDef]
  unfold Stage14M2_HNFiltAndFrame.muMaxDef Stage14M2_HNFiltAndFrame.muMinDef
  rw [hmax, hmin]
  constructor <;> intro h <;> linarith

/-- **Finite-Index Ramified Sublattice Flatness Stability (`flatLattice_sublattice_spread`)**:
for any equal-rank sublattice `L' ≤ A.L`,
`muMax(L') - muMin(L') ≤ (muMax(A.L) - muMin(A.L)) + (2 / [K : ℚ]) * log [A.L : L']`! -/
theorem flatLattice_sublattice_spread {K : Type} [Field K] [NumberField K]
    [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    {L' : Submodule (𝓞 K) A.V} (hL'L : L' ≤ A.L)
    (hrk : rkK (K := K) L' = rkK (K := K) A.L) :
    Stage14M2_HLatNumberField.muMaxDef A.b A.X L' -
        Stage14M2_HLatNumberField.muMinDef A.b A.X L' ≤
      (A.muMax - A.muMin) +
        (2 / (Module.finrank ℚ K : ℝ)) *
          Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) := by
  have hL'fg : L'.FG := Submodule.FG.of_le hG.2.1 hL'L
  have hL'0 : L' ≠ ⊥ := by
    intro h0
    have h1 : rkK (K := K) A.L = 0 := by rw [← hrk, h0]; simp [rkK]
    haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
    have hrk_pos := ArakelovCovolume.rk_pos_of_ne_bot A.zRealize (by
      intro hbot; apply hA0; rw [eq_bot_iff]; intro x hx
      have hm : realizeHLat A.b A.X x ∈ A.zRealize := ⟨x, hx, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact realizeHLat_injective A.b A.X hG.1 (hm.trans (map_zero _).symm))
    rw [rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1, h1, mul_zero] at hrk_pos
    omega
  have hmax_le : Stage14M2_HLatNumberField.muMaxDef A.b A.X L' ≤ A.muMax :=
    muMaxDef_mono A.b A.X hG.1 hG.2.1 hL'0 hL'L
  haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  have hrkZ : ArakelovCovolume.rk (zRealize A.b A.X L') = ArakelovCovolume.rk A.zRealize := by
    rw [rk_zRealize_eq A.b A.X hG.1 L' hL'fg, rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1, hrk]
  have hdegL' := Stage11BostDworkSqueeze.degAr_eq_degAr_sub_log_index
    (zRealize_mono A.b A.X hL'L) hrkZ
  have hidx : Stage11BostDworkSqueeze.latIndex A.zRealize (zRealize A.b A.X L') =
      L'.toAddSubgroup.relIndex A.L.toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective L'.toAddSubgroup A.L.toAddSubgroup
      (realizeHLat_injective A.b A.X hG.1)
  rw [hidx] at hdegL'
  have hidx_ge1 : 1 ≤ L'.toAddSubgroup.relIndex A.L.toAddSubgroup := by
    by_contra h0
    have h0' : L'.toAddSubgroup.relIndex A.L.toAddSubgroup = 0 := by omega
    have hcov := Stage11BostDworkSqueeze.covol_eq_index_mul_covol (zRealize_mono A.b A.X hL'L) hrkZ
    rw [hidx, h0'] at hcov
    haveI : DiscreteTopology (zRealize A.b A.X L') := discreteTopology_zRealize_of_fg A.b A.X hG.1 L' hL'fg
    have hpos := ArakelovCovolume.covol_pos (zRealize A.b A.X L')
    simp at hcov
    linarith
  have hlog_nn : 0 ≤ Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hidx_ge1)
  have hn_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hmin_ge : muMinO A.b A.X A.L -
      Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) / (Module.finrank ℚ K : ℝ) ≤
      muMinO A.b A.X L' := by
    rw [muMinO_char A.b A.X hG.1 L' hL'fg hL'0]
    intro N hNL'
    have hNL : N ≤ A.L := hNL'.trans hL'L
    have hNfg : N.FG := Submodule.FG.of_le hL'fg hNL'
    have hminL := (muMinO_char A.b A.X hG.1 A.L hG.2.1 hA0 (muMinO A.b A.X A.L)).mp le_rfl N hNL
    rw [hrkZ]
    change _ ≤ ArakelovCovolume.degAr (zRealize A.b A.X L') - ArakelovCovolume.degAr (zRealize A.b A.X N)
    rw [hdegL']
    by_cases hgap0 : rkK (K := K) N = rkK (K := K) A.L
    · have hrkN_eq : ArakelovCovolume.rk (zRealize A.b A.X N) = ArakelovCovolume.rk A.zRealize := by
        rw [rk_zRealize_eq A.b A.X hG.1 N hNfg, rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1, hgap0]
      have hdegN_le : ArakelovCovolume.degAr (zRealize A.b A.X N) ≤
          ArakelovCovolume.degAr (zRealize A.b A.X L') := by
        haveI : DiscreteTopology (zRealize A.b A.X L') :=
          discreteTopology_zRealize_of_fg A.b A.X hG.1 L' hL'fg
        exact (ArakelovCovolume.covol_le_of_le_same_rank (zRealize_mono A.b A.X hNL')
          (by rw [hrkN_eq, hrkZ])).2
      rw [hrkN_eq, sub_self, mul_zero]
      linarith
    · haveI : Module.Finite K A.V := Module.Finite.of_basis A.b
      have hrk_le : rkK (K := K) N ≤ rkK (K := K) A.L :=
        Submodule.finrank_mono (Submodule.span_mono hNL)
      have hrk_lt : rkK (K := K) N + 1 ≤ rkK (K := K) A.L := by omega
      have hdiff_ge : (Module.finrank ℚ K : ℝ) ≤
          (ArakelovCovolume.rk A.zRealize : ℝ) - (ArakelovCovolume.rk (zRealize A.b A.X N) : ℝ) := by
        rw [rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1, rk_zRealize_eq A.b A.X hG.1 N hNfg]
        have : Module.finrank ℚ K * rkK (K := K) N + Module.finrank ℚ K ≤
            Module.finrank ℚ K * rkK (K := K) A.L := by nlinarith
        have hcast : (Module.finrank ℚ K * rkK (K := K) N : ℝ) + (Module.finrank ℚ K : ℝ) ≤
            (Module.finrank ℚ K * rkK (K := K) A.L : ℝ) := by exact_mod_cast this
        push_cast at hcast ⊢; linarith
      have hmul : Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) ≤
          (Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) / (Module.finrank ℚ K : ℝ)) *
            ((ArakelovCovolume.rk A.zRealize : ℝ) - (ArakelovCovolume.rk (zRealize A.b A.X N) : ℝ)) := by
        calc Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ)
            = (Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) / (Module.finrank ℚ K : ℝ)) *
                (Module.finrank ℚ K : ℝ) := by field_simp [hn_pos.ne']
          _ ≤ _ := mul_le_mul_of_nonneg_left hdiff_ge (div_nonneg hlog_nn hn_pos.le)
      unfold degHLat at hminL
      linarith
  unfold HLat.muMin Stage14M2_HLatNumberField.muMinDef
  have halg : (2 / (Module.finrank ℚ K : ℝ)) * Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) =
      2 * (Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) / (Module.finrank ℚ K : ℝ)) := by ring
  linarith

/-- **Flat Lattice Theorem (`FlatLatticeTheorem`)**:
comprehensive flatness theorem over a totally complex (CM) number field `K`, bundling:
1. Unconditional Banaszczyk `O(log rk)` flatness (`IsFlatHLat A HH_ban`),
2. Exact dual flatness `IsFlatHLat (dualHLat A) HH_ban`,
3. Exact ideal-twist flatness `IsFlatHLat (A.withL (𝔟 • A.L)) HH_ban` for every `𝔟 ≠ ⊥`,
4. Parabolic HN-polygon deviation bound `0 ≤ hnPoly k - k * slope ≤ (HH_ban / 2) * k * (r - k) / r`,
5. All `K`-rank HN slopes lie in `[A.mu - HH_ban, A.mu + HH_ban]`! -/
theorem FlatLatticeTheorem {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    {HH : ℝ}
    (hHH : letI := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1;
      letI := Stage4ArakelovBost.discreteTopology_dualLat A.zRealize;
      -2 * Real.log (Stage2SiegelReduction.lambda1 A.zRealize *
        Stage2SiegelReduction.lambda1 (Stage4ArakelovBost.dualLat A.zRealize)) +
        2 * Real.log ((Module.finrank ℚ K * A.rank : ℕ) : ℝ) ≤ HH) :
    let r := Stage14M2_HNFiltAndFrame.rk (realizeHLat A.b A.X) A.L
    IsFlatHLat A HH ∧
    IsFlatHLat (dualHLat A) HH ∧
    (∀ 𝔟 : Ideal (𝓞 K), 𝔟 ≠ ⊥ → IsFlatHLat (A.withL (𝔟 • A.L)) HH) ∧
    (∀ k ≤ r,
      0 ≤ hnPoly (realizeHLat A.b A.X) A.L k -
            (k : ℝ) * Stage14M2_HNFiltAndFrame.slope (realizeHLat A.b A.X) A.L ∧
      hnPoly (realizeHLat A.b A.X) A.L k -
            (k : ℝ) * Stage14M2_HNFiltAndFrame.slope (realizeHLat A.b A.X) A.L ≤
        (HH / 2) * ((k : ℝ) * ((r : ℝ) - (k : ℝ)) / (r : ℝ))) ∧
    (∀ a : Fin (rkK (K := K) A.L),
      A.mu - HH ≤ hnSlopeListK A.b A.X hG.1 A.L hG.2.1 a ∧
      hnSlopeListK A.b A.X hG.1 A.L hG.2.1 a ≤ A.mu + HH) := by
  intro r
  have hflat : IsFlatHLat A HH := flatLattice_of_banaszczyk A hG hA0 hHH
  have hrk_pos : 0 < A.rank := by
    haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
    have h1 := ArakelovCovolume.rk_pos_of_ne_bot A.zRealize (by
      intro hbot; apply hA0; rw [eq_bot_iff]; intro x hx
      have hm : realizeHLat A.b A.X x ∈ A.zRealize := ⟨x, hx, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact realizeHLat_injective A.b A.X hG.1 (hm.trans (map_zero _).symm))
    rw [rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1] at h1
    exact Nat.pos_of_mul_pos_left h1
  have hsand := muMinDef_le_muDef_le_muMaxDef A.b A.X hG.1 A.L hG.2.1 hA0
  refine ⟨hflat, (flatLattice_dual_invariance A hG hrk_pos).mpr hflat,
    fun 𝔟 h𝔟 => (flatLattice_ideal_twist_invariance A hG hA0 𝔟 h𝔟).mpr hflat,
    fun k hk => hnPoly_flat_parabolic_bound A hG hA0 hflat k hk, fun a => ?_⟩
  have hb := hnSlopeListK_bounds A.b A.X hG.1 A.L hG.2.1 hA0 a
  unfold IsFlatHLat HLat.muMax HLat.muMin at hflat
  unfold HLat.mu
  exact ⟨by linarith [hb.1, hsand.2], by linarith [hb.2, hsand.1]⟩

end FlatLatticeSection

/-! ## Section 5: `joint_a_ramified_holds` — Sharp Ramified Joint-Model Bost Frame Inequality -/

section JointARamified

/-- **Contract Discharge (`joint_a_ramified_holds_contract`)**:
matches `Stage14Contracts.M2HLatBostContract.joint_a_ramified_holds` verbatim! -/
theorem joint_a_ramified_holds_contract
    (L_N L_RR : HLatAnchor) (φ : L_N.L →ₗ[ℤ] L_RR.L) (C_op : ℝ) (D_div : ℕ)
    (hD : 0 < D_div) (hφ : Function.Injective φ)
    (hC : ∀ x : L_N.L, ‖((φ x : L_RR.L) : L_RR.E)‖ ≤ C_op * ‖(x : L_N.E)‖)
    (hDiv : ∀ x : L_N.L, ∃ y : L_RR.L, φ x = (D_div : ℤ) • y) :
    L_N.slope + Real.log (D_div : ℝ) ≤ L_RR.muMax + Real.log C_op :=
  ramificationLinearCase_anchor L_N L_RR φ C_op D_div hD hφ hC hDiv

/-- **Unprojected Ramified Sharp Bost Frame Inequality (`joint_a_ramified_sharp_unprojected`)**:
combines `Stage14M2_HNFiltAndFrame.frame_herm_sharp_slope_ineq`, exact ramified ideal-twist
geometry (`𝔟 • cc`), AND Banaszczyk's `O(log r)` gap ceiling
(`Stage14M2_BanaszczykShortBasis.banaszczyk_hh_gap_le`) to eliminate any a priori `muMin` guess
whenever `s + (2 / [K : ℚ]) * log (Ideal.absNorm 𝔟) ≤ muMaxDef b' X' cc`! -/
theorem joint_a_ramified_sharp_unprojected
    {K W κ I : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Nonempty I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ) (c : I → ℝ)
    (s u HH e η : ℝ)
    (hX' : ∀ w, IsUnit (X' w).det) (hX : ∀ i w, IsUnit (X i w).det)
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det)
    (hccFG : cc.FG) (hccSpan : Submodule.span K (cc : Set W) = ⊤) (hcc0 : cc ≠ ⊥)
    (hNFG : ∀ i, (N i).FG) (hNSpan : ∀ i, Submodule.span K (N i : Set (V i)) = ⊤)
    (hBne : ∀ i, B i ≠ 0)
    (hBN_ram : ∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ 𝔟 • cc)
    (hs : s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) *
        (Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i)))
    (hu : 0 < u)
    (hmax : ∀ i, Stage14M2_HLatNumberField.muMaxDef (b i) (X i) (N i) -
      htMap (b i) (X i) b' X' (B i) ≤ s + u)
    (hs_le_max : s + (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) ≤
      Stage14M2_HLatNumberField.muMaxDef b' X' cc)
    (hBan : letI := discreteTopology_zRealize_of_fg b' X' hX' cc hccFG;
      letI := Stage4ArakelovBost.discreteTopology_dualLat (zRealize b' X' cc);
      -2 * Real.log (Stage2SiegelReduction.lambda1 (zRealize b' X' cc) *
        Stage2SiegelReduction.lambda1 (Stage4ArakelovBost.dualLat (zRealize b' X' cc))) +
        2 * Real.log ((Module.finrank ℚ K * Fintype.card κ : ℕ) : ℝ) ≤ HH)
    (hHH0 : 0 ≤ HH)
    (hc : ∀ i, 0 < c i)
    (hF2 : (∑ i, opHsSq (opFrameK (c i) (Matrix.toEuclideanLin
        (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) ∘ₗ
         opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (opFrameQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ^ 2 /
        (Fintype.card κ : ℝ))
    (hη : 0 ≤ η) :
    s + (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) -
        4 * u * Real.log (1 + HH / u) - (2 * η + 4 * Real.sqrt e) * HH ≤
      Stage14M2_HLatNumberField.muDef b' X' cc := by
  haveI : FiniteDimensional K W := Module.Finite.of_basis b'
  haveI : DiscreteTopology (zRealize b' X' cc) := discreteTopology_zRealize_of_fg b' X' hX' cc hccFG
  haveI : DiscreteTopology (Stage4ArakelovBost.dualLat (zRealize b' X' cc)) :=
    Stage4ArakelovBost.discreteTopology_dualLat (zRealize b' X' cc)
  have h𝔟ccFG : (𝔟 • cc).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hccFG
  have h𝔟ccSpan : Submodule.span K ((𝔟 • cc : Submodule (𝓞 K) W) : Set W) = ⊤ := by
    rw [twist_span_smul cc 𝔟 h𝔟, hccSpan]
  -- Derive `s - muMinDef (𝔟 • cc) ≤ HH` via `banaszczyk_hh_gap_le`!
  have hZ0 : zRealize b' X' cc ≠ ⊥ := by
    intro hbot; apply hcc0; rw [eq_bot_iff]; intro x hx
    have hm : realizeHLat b' X' x ∈ zRealize b' X' cc := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact realizeHLat_injective b' X' hX' (hm.trans (map_zero _).symm)
  have hrk_cc : ArakelovCovolume.rk (zRealize b' X' cc) = Module.finrank ℚ K * Fintype.card κ := by
    rw [rk_zRealize_eq b' X' hX' cc hccFG]
    unfold rkK; rw [hccSpan, finrank_top, Module.finrank_eq_card_basis b']
  have hban_gap := (banaszczyk_hh_gap_le (zRealize b' X' cc) hZ0 (HH := HH / 2) (by
    rw [hrk_cc]; linarith)).1
  have hspread : Stage14M2_HLatNumberField.muMaxDef b' X' cc -
      Stage14M2_HLatNumberField.muMinDef b' X' cc ≤ HH := by
    have hsp := muMaxDef_sub_muMinDef_le_two_mul_zSpread b' X' hX' cc hccFG hcc0
    linarith
  have htw := ramified_ideal_twist_invariants b' X' hX' cc hccFG hcc0 𝔟 h𝔟
  have hHH_ram : s - Stage14M2_HNFiltAndFrame.muMinDef b' X' (𝔟 • cc) ≤ HH := by
    rw [← muMinDef_eq_hnMuMinDef, htw.2.2]
    linarith
  have hs' : s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) *
        (Stage14M2_HNFiltAndFrame.muDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i)) := by
    simpa only [muDef_eq_hnMuDef] using hs
  have hmax' : ∀ i, Stage14M2_HNFiltAndFrame.muMaxDef (b i) (X i) (N i) -
      htMap (b i) (X i) b' X' (B i) ≤ s + u := fun i => by
    simpa only [muMaxDef_eq_hnMuMaxDef] using hmax i
  have hframe := frame_herm_sharp_slope_ineq K W κ I V ι b' X' (𝔟 • cc) b X N B v Y Y' c
    s u HH e η hX' hX hY hY' h𝔟ccFG h𝔟ccSpan hNFG hNSpan hBne hBN_ram
    hs' hu hmax' hHH_ram hHH0 hc hF2 he0 he1 hF1 hη
  rw [← muDef_eq_hnMuDef, htw.1] at hframe
  linarith

/-- **Main Theorem (`joint_a_ramified_holds`)**:
Sharp projected ramified joint-model Bost frame-slope inequality combining
`Stage14M2_HNFiltAndFrame.theoremFSharp_holds` (the projected parent of
`frame_herm_sharp_slope_ineq`), exact ramified ideal-twist geometry (`𝔟 • cc`), and
`Stage14M2_BanaszczykShortBasis.banaszczyk_hh_gap_le` (eliminating LLL and yielding an explicit
Banaszczyk `O(log rk)` ceiling `HH`):
```
s + (2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)
  - (1 - δ)⁻¹ * (4 * u * log (1 + HH / u) + (η + 4 * √e) * HH)
  ≤ muDef b' X' cc
```
with an **independent** target slope `muDef b' X' cc`! -/
theorem joint_a_ramified_holds
    {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (s u HH e η δ : ℝ)
    (hX' : ∀ w, IsUnit (X' w).det) (hX : ∀ i w, IsUnit (X i w).det)
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det)
    (hccFG : cc.FG) (hccSpan : Submodule.span K (cc : Set W) = ⊤) (hcc0 : cc ≠ ⊥)
    (hNFG : ∀ i, (N i).FG) (hNSpan : ∀ i, Submodule.span K (N i : Set (V i)) = ⊤)
    (hR : 0 < ∑ i, Fintype.card (ι i))
    (hBN_ram : ∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ 𝔟 • cc)
    (hht : ∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i)
    (hs : s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) - h i))
    (hu : 0 ≤ u)
    (hmax : ∀ i, Stage14M2_HLatNumberField.muMaxDef (b i) (X i) (N i) - h i ≤ s + u)
    (hs_le_max : s + (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) ≤
      Stage14M2_HLatNumberField.muMaxDef b' X' cc)
    (hBan : letI := discreteTopology_zRealize_of_fg b' X' hX' cc hccFG;
      letI := Stage4ArakelovBost.discreteTopology_dualLat (zRealize b' X' cc);
      -2 * Real.log (Stage2SiegelReduction.lambda1 (zRealize b' X' cc) *
        Stage2SiegelReduction.lambda1 (Stage4ArakelovBost.dualLat (zRealize b' X' cc))) +
        2 * Real.log ((Module.finrank ℚ K * Fintype.card κ : ℕ) : ℝ) ≤ HH)
    (hHH0 : 0 ≤ HH)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcard : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
    (hγ : ∀ i, 0 < γ i)
    (hF2 : (∑ i, opHsSq (opFrameK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ))
    (hη : 0 ≤ η) :
    s + (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤
      Stage14M2_HLatNumberField.muDef b' X' cc := by
  haveI : FiniteDimensional K W := Module.Finite.of_basis b'
  haveI : DiscreteTopology (zRealize b' X' cc) := discreteTopology_zRealize_of_fg b' X' hX' cc hccFG
  haveI : DiscreteTopology (Stage4ArakelovBost.dualLat (zRealize b' X' cc)) :=
    Stage4ArakelovBost.discreteTopology_dualLat (zRealize b' X' cc)
  have h𝔟ccFG : (𝔟 • cc).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hccFG
  have h𝔟ccSpan : Submodule.span K ((𝔟 • cc : Submodule (𝓞 K) W) : Set W) = ⊤ := by
    rw [twist_span_smul cc 𝔟 h𝔟, hccSpan]
  have hZ0 : zRealize b' X' cc ≠ ⊥ := by
    intro hbot; apply hcc0; rw [eq_bot_iff]; intro x hx
    have hm : realizeHLat b' X' x ∈ zRealize b' X' cc := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact realizeHLat_injective b' X' hX' (hm.trans (map_zero _).symm)
  have hrk_cc : ArakelovCovolume.rk (zRealize b' X' cc) = Module.finrank ℚ K * Fintype.card κ := by
    rw [rk_zRealize_eq b' X' hX' cc hccFG]
    unfold rkK; rw [hccSpan, finrank_top, Module.finrank_eq_card_basis b']
  have hban_gap := (banaszczyk_hh_gap_le (zRealize b' X' cc) hZ0 (HH := HH / 2) (by
    rw [hrk_cc]; linarith)).1
  have hspread : Stage14M2_HLatNumberField.muMaxDef b' X' cc -
      Stage14M2_HLatNumberField.muMinDef b' X' cc ≤ HH := by
    have hsp := muMaxDef_sub_muMinDef_le_two_mul_zSpread b' X' hX' cc hccFG hcc0
    linarith
  have htw := ramified_ideal_twist_invariants b' X' hX' cc hccFG hcc0 𝔟 h𝔟
  have hHH_ram : s - Stage14M2_HNFiltAndFrame.muMinDef b' X' (𝔟 • cc) ≤ HH := by
    rw [← muMinDef_eq_hnMuMinDef, htw.2.2]
    linarith
  have hs' : s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (Stage14M2_HNFiltAndFrame.muDef (b i) (X i) (N i) - h i) := by
    simpa only [muDef_eq_hnMuDef] using hs
  have hmax' : ∀ i, Stage14M2_HNFiltAndFrame.muMaxDef (b i) (X i) (N i) - h i ≤ s + u := fun i => by
    simpa only [muMaxDef_eq_hnMuMaxDef] using hmax i
  have hsharp := theoremFSharp_holds K W κ κ₁ I V ι b' X' (𝔟 • cc) b X N B h v Y Y' Ball γ
    s u HH e η δ hX' hX hY hY' h𝔟ccFG h𝔟ccSpan hNFG hNSpan hR hBN_ram hht
    hs' hu hmax' hHH_ram hHH0 hδ0 hδ1 hcard hBall hγ hF2 he0 he1 hF1 hη
  rw [← muDef_eq_hnMuDef, htw.1] at hsharp
  linarith

/-- **Automatic `hs_le_max` Deduction when Every `B i` is Injective**:
when each `B i` is injective into `𝔟 • cc` and `s = wmean (|ι i|) (muDef (N i) - h i)`,
the upper comparison `s + (2 / [K : ℚ]) * log N(𝔟) ≤ muMaxDef cc` follows AUTOMATICALLY from
`RamificationLinearCase.slope_ineq_of_injective`! -/
theorem mean_ramified_slope_le_muMax_of_injective
    {K W κ I : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Nonempty I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ) (s : ℝ)
    (hX' : ∀ w, IsUnit (X' w).det) (hX : ∀ i w, IsUnit (X i w).det)
    (hccFG : cc.FG) (hccSpan : Submodule.span K (cc : Set W) = ⊤) (hcc0 : cc ≠ ⊥)
    (hNFG : ∀ i, (N i).FG) (hNSpan : ∀ i, Submodule.span K (N i : Set (V i)) = ⊤)
    (hR : 0 < ∑ i, Fintype.card (ι i))
    (hBinj : ∀ i, Function.Injective (B i))
    (hBN_ram : ∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ 𝔟 • cc)
    (hht : ∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i)
    (hmean_exact : s * (∑ i, (Fintype.card (ι i) : ℝ)) =
      ∑ i, (Fintype.card (ι i) : ℝ) *
        (Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) - h i)) :
    s + (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) ≤
      Stage14M2_HLatNumberField.muMaxDef b' X' cc := by
  have hRpos : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by exact_mod_cast hR
  have hterm : ∀ i : I,
      (Fintype.card (ι i) : ℝ) *
        (Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) - h i +
          (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ)) ≤
      (Fintype.card (ι i) : ℝ) * Stage14M2_HLatNumberField.muMaxDef b' X' cc := by
    intro i
    by_cases hci : Fintype.card (ι i) = 0
    · simp [hci]
    · have hN0 : N i ≠ ⊥ := by
        intro h0
        have h1 : Module.finrank K (V i) = 0 := by
          rw [← finrank_top K (V i), ← hNSpan i, h0, Submodule.bot_coe,
            Submodule.span_zero_singleton, finrank_bot]
        rw [Module.finrank_eq_card_basis (b i)] at h1
        exact hci h1
      have hBi0 : B i ≠ 0 := by
        intro hb0
        have hpos : 0 < Fintype.card (ι i) := Nat.pos_of_ne_zero hci
        obtain ⟨j₀⟩ := Fintype.card_pos_iff.mp hpos
        have hbne : b i j₀ ≠ 0 := (b i).ne_zero j₀
        have heq : B i (b i j₀) = B i 0 := by simp [hb0]
        exact hbne (hBinj i heq)
      let RL : RamificationLinearCase K :=
        { src := ⟨V i, ι i, b i, X i, N i⟩
          dst := ⟨W, κ, b', X', cc⟩
          src_good := ⟨hX i, hNFG i, hNSpan i⟩
          dst_good := ⟨hX', hccFG, hccSpan⟩
          src_ne_bot := hN0
          dst_ne_bot := hcc0
          ramIdeal := 𝔟
          ramIdeal_ne_bot := h𝔟
          φ := B i
          maps_into_ram := hBN_ram i }
      have hrl := (RL.slope_ineq_of_injective (hBinj i)).1
      have hhi := hht i hBi0
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      change Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) - h i +
          (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) ≤
        Stage14M2_HLatNumberField.muMaxDef b' X' cc
      have hrl' : Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) +
          (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ) ≤
          Stage14M2_HLatNumberField.muMaxDef b' X' cc + htMap (b i) (X i) b' X' (B i) := hrl
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  have hLHS : ∑ i, (Fintype.card (ι i) : ℝ) *
      (Stage14M2_HLatNumberField.muDef (b i) (X i) (N i) - h i +
        (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ)) =
      (∑ i, (Fintype.card (ι i) : ℝ)) *
        (s + (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm 𝔟 : ℝ)) := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ← hmean_exact]
    ring
  rw [hLHS, ← Finset.sum_mul] at hsum
  exact le_of_mul_le_mul_left hsum hRpos

end JointARamified

/-! ## Section 6: `bost_slope_ineq_from_ramified_frame` — Independent Target `mu(RR^∨)` & `Stage14Contracts` Alignment -/

section RamifiedFrameToBostFiber

/-- **Ramified Hermitian Lattice Gram-Frame Bundle (`RamifiedHLatGramFrame`)**:
packages an actual family of CM Hermitian source lattices `Nu u` (`u : W`), an **independent**
target Hermitian lattice `RR : HLat K` with dual `RR^∨ := dualHLat RR`, a ramification ideal
`𝔟 ≤ 𝓞 K` (`𝔟 ≠ ⊥`, with `𝔟 = ⊤` unramified), iterated Bessel/theta morphisms
`Bk u : (Nu u).V →ₗ[K] (dualHLat RR).V` mapping `(Nu u).L` into `𝔟 • (dualHLat RR).L`,
and a compressed Gram-frame realization `(Bf, Vr)` at an infinite place `v : InfinitePlace K`!

Crucially, `RR^∨` (`dualHLat RR`) is a **completely independent Hermitian lattice**: its slope
`mu(RR^∨) = -RR.mu` is NEVER short-circuited to `s`! -/
structure RamifiedHLatGramFrame (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] where
  W : Type
  [finW : Fintype W]
  [neW : Nonempty W]
  RR : HLat K
  RR_good : RR.Good
  RR_rk_pos : 0 < RR.rank
  ramIdeal : Ideal (𝓞 K)
  ramIdeal_ne_bot : ramIdeal ≠ ⊥
  Nu : W → HLat K
  Nu_good : ∀ u, (Nu u).Good
  Nu_rk_pos : ∀ u, 0 < (Nu u).rank
  Bk : ∀ u, (Nu u).V →ₗ[K] (dualHLat RR).V
  Bk_maps : ∀ u, (Nu u).L.map ((Bk u).restrictScalars (𝓞 K)) ≤ ramIdeal • (dualHLat RR).L
  h : W → ℝ
  Bk_ht : ∀ u, Bk u ≠ 0 → htMap (Nu u).b (Nu u).X (dualHLat RR).b (dualHLat RR).X (Bk u) ≤ h u
  -- Archimedean place & Gram-frame compression data
  v : InfinitePlace K
  κ₁ : Type
  [finκ₁ : Fintype κ₁]
  [decκ₁ : DecidableEq κ₁]
  Y : ∀ u, Matrix (Nu u).ι (Nu u).ι ℂ
  Y' : Matrix (dualHLat RR).ι (dualHLat RR).ι ℂ
  hY : ∀ u, IsUnit (Y u).det
  hY' : IsUnit Y'.det
  d : W → ℕ
  Bf : ∀ u, Matrix (Fin (Fintype.card ((dualHLat RR).ι ⊕ κ₁))) (Fin (d u)) ℂ
  Vr : ∀ u, Matrix (Fin (d u)) (Fin (Fintype.card (Nu u).ι)) ℂ
  ga : W → ℝ
  Dstar : ℝ
  sg : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ
  de : ℝ
  δ : ℝ
  delBar : ℝ
  sgBar : ℝ
  deBar : ℝ
  e0Bar : ℝ
  isIsom : IsIsometryFamily Vr
  ga_pos : ∀ u, 0 < ga u
  Dstar_pos : 0 < Dstar
  sg_pos : 0 < sg
  sg_le_bar : sg ≤ sgBar
  sgBar_le : sgBar ≤ 1 / 20
  rank_ge : Dstar / sg ≤ totalRank d
  η0_ge : -1 ≤ η0
  η0_le : η0 ≤ sg / 2
  η1_le : η1 ≤ sg / 2
  e0_nonneg : 0 ≤ e0
  e0_le_bar : e0 ≤ e0Bar
  sqrt_e0_le : Real.sqrt e0 ≤ sg / 2
  de_nonneg : 0 ≤ de
  de_le_bar : de ≤ deBar
  deBar_le : deBar ≤ 1 / 4
  corV : ∑ u, ((d u : ℝ) - (Fintype.card (Nu u).ι : ℝ)) ≤ de * totalRank d
  gramInput : GramInput Bf ga Dstar η0 η1 e0
  δ_nonneg : 0 ≤ δ
  δ_le_bar : δ ≤ delBar
  delBar_le : delBar ≤ 1 / 2
  card_ge : (1 - δ) * (Fintype.card ((dualHLat RR).ι ⊕ κ₁) : ℝ) ≤
    (Fintype.card (dualHLat RR).ι : ℝ)
  -- Exact compatibility: the `Sum.inl` block of `compressFamily Bf Vr u` IS the archimedean
  -- frame matrix of `Bk u` at infinite place `v`!
  compress_compat : ∀ u (k : (dualHLat RR).ι) (j : Fin (Fintype.card (Nu u).ι)),
    (Matrix.reindex (Fintype.equivFin ((dualHLat RR).ι ⊕ κ₁)).symm (Equiv.refl _)
        (compressFamily Bf Vr u)) (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (Nu u).b (dualHLat RR).b (Bk u)).map v.embedding * Y u)
        k ((Fintype.equivFin (Nu u).ι).symm j)

attribute [instance] RamifiedHLatGramFrame.finW RamifiedHLatGramFrame.neW
  RamifiedHLatGramFrame.finκ₁ RamifiedHLatGramFrame.decκ₁

namespace RamifiedHLatGramFrame

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]

/-- Target dual lattice `RR^∨ := dualHLat RR`. -/
abbrev RRDual (G : RamifiedHLatGramFrame K) : HLat K := dualHLat G.RR

/-- Ramified target sublattice `𝔟 • RR^∨`. -/
abbrev ramTarget (G : RamifiedHLatGramFrame K) : Submodule (𝓞 K) G.RRDual.V :=
  G.ramIdeal • G.RRDual.L

lemma RRDual_good (G : RamifiedHLatGramFrame K) : G.RRDual.Good := by
  haveI : Module.Finite K G.RR.V := Module.Finite.of_basis G.RR.b
  exact ⟨dualFrame_frameOK G.RR.X G.RR_good.1,
    Stage14M2_HLatNumberField.dualLatO_fg G.RR.b G.RR.L G.RR_good.2.2,
    Stage14M2_HLatNumberField.dualLatO_span_top G.RR.b G.RR.L G.RR_good.2.1⟩

lemma RRDual_card_pos (G : RamifiedHLatGramFrame K) : 0 < Fintype.card G.RRDual.ι := by
  have hrk : G.RR.rank = Fintype.card G.RR.ι := by
    unfold HLat.rank rkK
    rw [G.RR_good.2.2, finrank_top, Module.finrank_eq_card_basis G.RR.b]
  have hpos := G.RR_rk_pos
  change 0 < Fintype.card G.RR.ι
  omega

lemma RRDual_ne_bot (G : RamifiedHLatGramFrame K) : G.RRDual.L ≠ ⊥ := by
  intro h0
  have hsp := G.RRDual_good.2.2
  rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hsp
  have hdim : Module.finrank K G.RRDual.V = 0 := by
    rw [← finrank_top K G.RRDual.V, ← hsp, finrank_bot]
  rw [Module.finrank_eq_card_basis G.RRDual.b] at hdim
  have hpos := G.RRDual_card_pos
  omega

lemma ramTarget_fg (G : RamifiedHLatGramFrame K) : G.ramTarget.FG :=
  Submodule.FG.smul (IsNoetherian.noetherian G.ramIdeal) G.RRDual_good.2.1

lemma ramTarget_span_top (G : RamifiedHLatGramFrame K) :
    Submodule.span K (G.ramTarget : Set G.RRDual.V) = ⊤ := by
  haveI : FiniteDimensional K G.RRDual.V := Module.Finite.of_basis G.RRDual.b
  rw [twist_span_smul G.RRDual.L G.ramIdeal G.ramIdeal_ne_bot, G.RRDual_good.2.2]

lemma ramTarget_ne_bot (G : RamifiedHLatGramFrame K) : G.ramTarget ≠ ⊥ :=
  ideal_smul_ne_bot G.RRDual_ne_bot G.ramIdeal_ne_bot

lemma ramTarget_rkK (G : RamifiedHLatGramFrame K) :
    rkK (K := K) G.ramTarget = Fintype.card G.RRDual.ι := by
  unfold rkK
  rw [G.ramTarget_span_top, finrank_top, Module.finrank_eq_card_basis G.RRDual.b]

lemma Nu_ne_bot (G : RamifiedHLatGramFrame K) (u : G.W) : (G.Nu u).L ≠ ⊥ := by
  intro h0
  have h1 : (G.Nu u).rank = 0 := by unfold HLat.rank rkK; rw [h0]; simp
  have := G.Nu_rk_pos u
  omega

lemma Nu_rkK (G : RamifiedHLatGramFrame K) (u : G.W) :
    rkK (K := K) (G.Nu u).L = Fintype.card (G.Nu u).ι := by
  unfold rkK
  rw [(G.Nu_good u).2.2, finrank_top, Module.finrank_eq_card_basis (G.Nu u).b]

/-- Rank-weighted mean shifted slope `s` across the family `W`. -/
def meanSlope (G : RamifiedHLatGramFrame K) : ℝ :=
  SlopeInequality.wmean (fun u => (Fintype.card (G.Nu u).ι : ℝ))
    (fun u => (G.Nu u).mu - G.h u)

/-- Maximal slope excess `uF` across the family `W`. -/
def slopeExcess (G : RamifiedHLatGramFrame K) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun u : G.W => (G.Nu u).muMax - G.h u) - G.meanSlope

/-- Ramification slope gain `(2 / [K : ℚ]) * log (Ideal.absNorm 𝔟)`. -/
def ramGain (G : RamifiedHLatGramFrame K) : ℝ :=
  (2 / (Module.finrank ℚ K : ℝ)) * Real.log (Ideal.absNorm G.ramIdeal : ℝ)

lemma ramGain_nonneg (G : RamifiedHLatGramFrame K) : 0 ≤ G.ramGain := by
  unfold ramGain
  have h1 : 1 ≤ Ideal.absNorm G.ramIdeal :=
    Nat.one_le_iff_ne_zero.mpr fun h => G.ramIdeal_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast h1))

lemma Nu_card_pos (G : RamifiedHLatGramFrame K) (u : G.W) : 0 < Fintype.card (G.Nu u).ι := by
  rw [← G.Nu_rkK u]; exact G.Nu_rk_pos u

lemma slopeExcess_nonneg (G : RamifiedHLatGramFrame K) : 0 ≤ G.slopeExcess := by
  unfold slopeExcess meanSlope SlopeInequality.wmean
  have hden : 0 < ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) :=
    Finset.sum_pos (fun u _ => Nat.cast_pos.mpr (G.Nu_card_pos u)) Finset.univ_nonempty
  set M := Finset.univ.sup' Finset.univ_nonempty (fun u : G.W => (G.Nu u).muMax - G.h u)
  have hle : ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u) ≤
      (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) * M := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 := (muMinDef_le_muDef_le_muMaxDef (G.Nu u).b (G.Nu u).X (G.Nu_good u).1
      (G.Nu u).L (G.Nu_good u).2.1 (G.Nu_ne_bot u)).2
    have h2 : (G.Nu u).muMax - G.h u ≤ M :=
      Finset.le_sup' (f := fun u : G.W => (G.Nu u).muMax - G.h u) (Finset.mem_univ u)
    unfold HLat.muMax at h2
    unfold HLat.mu
    linarith
  have hdiv : (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u)) /
      (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) ≤ M := (div_le_iff₀ hden).mpr (by linarith)
  linarith

/-- **Genuine Non-Short-Circuited `Stage2GramFrameFiber` Compiler
(`mkStage2GramFrameFiber_of_ramified_hlat`)**:
builds a concrete `Stage2ThetaWire.Stage2GramFrameFiber` directly from `G : RamifiedHLatGramFrame K`
using the EXACT `K`-rank HN slope vectors `hnSlopeListK` of `Nu u` and `𝔟 • RR^∨` and the
complexified HN threshold subspaces at place `G.v`!

**ZERO SHORT-CIRCUIT**: `F.muCC = G.RRDual.mu - G.ramGain = -G.RR.mu - G.ramGain`, strictly
determined by the independent dual Hermitian lattice `RR^∨`! -/
def toStage2GramFrameFiber (G : RamifiedHLatGramFrame K)
    {s uF : ℝ} (HH : ℝ) {muMinCC : ℝ}
    (hs : s * (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) ≤
      ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u))
    (huF : ∀ u : G.W, (G.Nu u).muMax - G.h u ≤ s + uF)
    (hmuMin : muMinCC ≤ G.RRDual.muMin - G.ramGain) :
    Stage2GramFrameFiber s uF HH muMinCC (Fintype.card G.W)
      G.delBar G.sgBar G.deBar G.e0Bar := by
  classical
  let eqTarget : EuclideanSpace ℂ G.RRDual.ι ≃ₗ[ℂ] (G.RRDual.ι → ℂ) :=
    WithLp.linearEquiv 2 ℂ (G.RRDual.ι → ℂ)
  let eNu : ∀ u, (G.Nu u).ι ≃ Fin (Fintype.card (G.Nu u).ι) :=
    fun u => Fintype.equivFin (G.Nu u).ι
  let eqSrc : ∀ u, ((G.Nu u).ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card (G.Nu u).ι)) :=
    fun u => (LinearEquiv.funCongrLeft ℂ ℂ (eNu u).symm).trans
      (WithLp.linearEquiv 2 ℂ (Fin (Fintype.card (G.Nu u).ι) → ℂ)).symm
  -- Source `K`-rank HN slopes shifted by `-h u`
  let yFun : ∀ u : G.W, Fin (Fintype.card (G.Nu u).ι) → ℝ := fun u j =>
    hnSlopeListK (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L (G.Nu_good u).2.1
      (Fin.cast (G.Nu_rkK u).symm j) - G.h u
  -- Independent target `K`-rank HN slopes of `𝔟 • RR^∨`
  let xFun : Fin (Fintype.card G.RRDual.ι) → ℝ := fun j =>
    hnSlopeListK G.RRDual.b G.RRDual.X G.RRDual_good.1 G.ramTarget G.ramTarget_fg
      (Fin.cast G.ramTarget_rkK.symm j)
  -- HN threshold submodules at `τ`
  let θSrc : ℝ → G.W → ℝ := fun τ u => (s - τ + G.h u - slopeNormalisingConstant K) / 2
  let Nt : ℝ → ∀ u : G.W, Submodule (𝓞 K) (G.Nu u).V := fun τ u =>
    hnStep (realizeHLat (G.Nu u).b (G.Nu u).X) (G.Nu u).L (θSrc τ u)
  let θDst : ℝ → ℝ := fun τ =>
    (s - Real.log (Fintype.card G.W : ℝ) - τ - slopeNormalisingConstant K) / 2
  let St : ℝ → Submodule (𝓞 K) G.RRDual.V := fun τ =>
    hnStep (realizeHLat G.RRDual.b G.RRDual.X) G.ramTarget (θDst τ)
  -- Complexified subspaces at infinite place `G.v` using auxiliary frames `G.Y u`, `G.Y'`
  let Nτ : ℝ → ∀ u : G.W, Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card (G.Nu u).ι))) :=
    fun τ u =>
      (Submodule.span ℂ (fcoord (G.Nu u).b (fun _ => G.Y u) G.v '' (Nt τ u : Set (G.Nu u).V))).map
        (eqSrc u).toLinearMap
  let T : ℝ → Submodule ℂ (EuclideanSpace ℂ G.RRDual.ι) := fun τ =>
    (Submodule.span ℂ (fcoord G.RRDual.b (fun _ => G.Y') G.v '' (St τ : Set G.RRDual.V))).map
      eqTarget.symm.toLinearMap
  -- Verify `y_mean`
  have hy_mean : (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) * s ≤ ∑ u : G.W, ∑ j, yFun u j := by
    have hsum_u : ∀ u : G.W, ∑ j : Fin (Fintype.card (G.Nu u).ι), yFun u j =
        (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u) := by
      intro u
      simp only [yFun, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hre : ∑ j : Fin (Fintype.card (G.Nu u).ι),
          hnSlopeListK (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L (G.Nu_good u).2.1
            (Fin.cast (G.Nu_rkK u).symm j) =
          ∑ a : Fin (rkK (K := K) (G.Nu u).L),
            hnSlopeListK (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L (G.Nu_good u).2.1 a :=
        Fintype.sum_equiv (finCongr (G.Nu_rkK u).symm) _ _ (fun _ => rfl)
      rw [hre, sum_hnSlopeListK (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L
        (G.Nu_good u).2.1 (G.Nu_ne_bot u), G.Nu_rkK u]
      unfold HLat.mu; ring
    simp_rw [hsum_u]
    linarith
  -- Verify `y_top`
  have hy_top : ∀ u j, yFun u j ≤ s + uF := by
    intro u j
    have hb := (hnSlopeListK_bounds (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L
      (G.Nu_good u).2.1 (G.Nu_ne_bot u) (Fin.cast (G.Nu_rkK u).symm j)).2
    have hm := huF u
    dsimp only [yFun]; unfold HLat.muMax at hm; linarith
  -- Verify `x_min`
  have hx_min : ∀ j, muMinCC ≤ xFun j := by
    intro j
    have hb := (hnSlopeListK_bounds G.RRDual.b G.RRDual.X G.RRDual_good.1 G.ramTarget
      G.ramTarget_fg G.ramTarget_ne_bot (Fin.cast G.ramTarget_rkK.symm j)).1
    have htw := (ramified_ideal_twist_invariants G.RRDual.b G.RRDual.X G.RRDual_good.1
      G.RRDual.L G.RRDual_good.2.1 G.RRDual_ne_bot G.ramIdeal G.ramIdeal_ne_bot).2.2
    dsimp only [xFun]; unfold HLat.muMin ramGain at hmuMin; linarith
  -- Verify `Nτ_corank`
  have hNτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u,
      (Fintype.card (G.Nu u).ι : ℝ) - Module.finrank ℂ (Nτ τ u) ≤
        ((Finset.univ.filter (fun j => yFun u j < s - τ)).card : ℝ) := by
    intro τ _ u
    have hdim : Module.finrank ℂ (Nτ τ u) = rkK (K := K) (Nt τ u) := by
      dsimp only [Nτ]
      rw [LinearEquiv.finrank_map_eq]
      exact finrank_span_complex (G.Nu u).b (fun _ => G.Y u) (fun _ => G.hY u) (Nt τ u) G.v
    rw [hdim]
    have hflt : (Finset.univ.filter (fun j : Fin (Fintype.card (G.Nu u).ι) => yFun u j < s - τ)).card =
        (Finset.univ.filter (fun a : Fin (rkK (K := K) (G.Nu u).L) =>
          hnSlopeListK (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L (G.Nu_good u).2.1 a <
            s - τ + G.h u)).card := by
      refine Finset.card_bij (fun j _ => Fin.cast (G.Nu_rkK u).symm j)
        (fun j hj => by
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨Finset.mem_univ _, by dsimp only [yFun] at hj; linarith [hj.2]⟩)
        (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun a ha => ⟨Fin.cast (G.Nu_rkK u) a, by
          rw [Finset.mem_filter] at ha ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          dsimp only [yFun]; simp only [Fin.cast_cast, Fin.cast_refl, id_eq]; linarith [ha.2],
          by ext; rfl⟩)
    rw [hflt, card_hnSlopeListK_lt (G.Nu u).b (G.Nu u).X (G.Nu_good u).1 (G.Nu u).L
      (G.Nu_good u).2.1 (s - τ + G.h u), G.Nu_rkK u]
  -- Verify `T_proj`
  have hT_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ u
      (vVec : EuclideanSpace ℂ (Fin (Fintype.card (G.Nu u).ι))), vVec ∈ Nτ τ u →
      (WithLp.linearEquiv 2 ℂ (G.RRDual.ι → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (G.RRDual.ι ⊕ G.κ₁)).symm (Equiv.refl _)
            (compressFamily G.Bf G.Vr u)) vVec) (Sum.inl k)) ∈ T τ := by
    intro τ _ u vVec hvVec
    have hLNu := (place_lattice_structure (G.Nu u).b (G.Nu u).X (G.Nu_good u).1
      (G.Nu u).L (G.Nu_good u).2.1).1
    have hLram := (place_lattice_structure G.RRDual.b G.RRDual.X G.RRDual_good.1
      G.ramTarget G.ramTarget_fg).1
    have hNtle : Nt τ u ≤ (G.Nu u).L := (hnStep_spec _ hLNu (θSrc τ u)).1.1
    have hNtfg : (Nt τ u).FG := Submodule.FG.of_le (G.Nu_good u).2.1 hNtle
    -- Key Bost morphism inclusion: `(Nt τ u).map (Bk u) ≤ St τ`!
    have hmap_le : (Nt τ u).map ((G.Bk u).restrictScalars (𝓞 K)) ≤ St τ := by
      by_cases h0 : (Nt τ u).map ((G.Bk u).restrictScalars (𝓞 K)) = ⊥
      · rw [h0]; exact bot_le
      · have hBne : G.Bk u ≠ 0 := fun hb => h0 (eq_bot_iff.mpr (by rintro _ ⟨z, _, rfl⟩; simp [hb]))
        have hNt0 : Nt τ u ≠ ⊥ := fun h' => h0 (by rw [h', Submodule.map_bot])
        have hsi := (slope_inequality_mean (G.Nu u).b (G.Nu u).X G.RRDual.b G.RRDual.X
          (G.Nu_good u).1 G.RRDual_good.1 (G.Bk u) (Nt τ u) hNtfg h0).1
        have hst := (hnStep_spec _ hLNu (θSrc τ u)).2.1 hNt0
        have hhi := G.Bk_ht u hBne
        have hlogW : 0 ≤ Real.log (Fintype.card G.W : ℝ) :=
          Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := G.W))
        refine (hnStep_spec _ hLram (θDst τ)).2.2.1 _
          ((Submodule.map_mono hNtle).trans (G.Bk_maps u)) h0 ?_
        unfold Stage14M2_HNFiltAndFrame.muMinDef at hsi
        dsimp only [θSrc, θDst] at hst ⊢
        linarith
    -- Linear map projecting `compressFamily Bf Vr u` to `EuclideanSpace ℂ G.RRDual.ι`
    let Lproj : EuclideanSpace ℂ (Fin (Fintype.card (G.Nu u).ι)) →ₗ[ℂ]
        EuclideanSpace ℂ G.RRDual.ι :=
      { toFun := fun w => eqTarget.symm (fun k =>
          (Matrix.toEuclideanLin
            (Matrix.reindex (Fintype.equivFin (G.RRDual.ι ⊕ G.κ₁)).symm (Equiv.refl _)
              (compressFamily G.Bf G.Vr u)) w) (Sum.inl k))
        map_add' := fun w₁ w₂ => by
          ext k; simp [map_add, eqTarget]
        map_smul' := fun c w => by
          ext k; simp [map_smul, eqTarget] }
    have hLproj_le : (Nτ τ u).map Lproj ≤ T τ := by
      dsimp only [Nτ, T]
      rw [Submodule.map_le_iff_le_comap, Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_comap]
      change Lproj (eqSrc u (fcoord (G.Nu u).b (fun _ => G.Y u) G.v x)) ∈
        (Submodule.span ℂ (fcoord G.RRDual.b (fun _ => G.Y') G.v '' (St τ : Set G.RRDual.V))).map
          eqTarget.symm.toLinearMap
      have hvec_eq : Lproj (eqSrc u (fcoord (G.Nu u).b (fun _ => G.Y u) G.v x)) =
          eqTarget.symm (fcoord G.RRDual.b (fun _ => G.Y') G.v (G.Bk u x)) := by
        ext k
        change (Matrix.toLpLin 2 2
          (Matrix.reindex (Fintype.equivFin (G.RRDual.ι ⊕ G.κ₁)).symm (Equiv.refl _)
            (compressFamily G.Bf G.Vr u))
          (eqSrc u (fcoord (G.Nu u).b (fun _ => G.Y u) G.v x))).ofLp (Sum.inl k) =
          fcoord G.RRDual.b (fun _ => G.Y') G.v (G.Bk u x) k
        rw [fcoord_map_eq (G.Nu u).b (fun _ => G.Y u) G.RRDual.b (fun _ => G.Y')
          (fun _ => G.hY u) G.v (G.Bk u) x]
        simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
          G.compress_compat u k]
        refine Fintype.sum_equiv (eNu u).symm _ _ (fun j => ?_)
        rfl
      rw [hvec_eq]
      exact Submodule.mem_map_of_mem (Submodule.subset_span
        ⟨G.Bk u x, hmap_le (Submodule.mem_map_of_mem hx), rfl⟩)
    exact hLproj_le (Submodule.mem_map_of_mem hvVec)
  -- Verify `T_tail`
  have hT_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => xFun j < s - Real.log (Fintype.card G.W : ℝ) - τ)).card : ℝ) ≤
        (Fintype.card G.RRDual.ι : ℝ) - Module.finrank ℂ (T τ) := by
    intro τ _
    have hdim : Module.finrank ℂ (T τ) = rkK (K := K) (St τ) := by
      dsimp only [T]
      rw [LinearEquiv.finrank_map_eq]
      exact finrank_span_complex G.RRDual.b (fun _ => G.Y') (fun _ => G.hY') (St τ) G.v
    rw [hdim]
    have hflt : (Finset.univ.filter (fun j : Fin (Fintype.card G.RRDual.ι) =>
          xFun j < s - Real.log (Fintype.card G.W : ℝ) - τ)).card =
        (Finset.univ.filter (fun a : Fin (rkK (K := K) G.ramTarget) =>
          hnSlopeListK G.RRDual.b G.RRDual.X G.RRDual_good.1 G.ramTarget G.ramTarget_fg a <
            s - Real.log (Fintype.card G.W : ℝ) - τ)).card := by
      refine Finset.card_bij (fun j _ => Fin.cast G.ramTarget_rkK.symm j)
        (fun j hj => by rw [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, hj.2⟩)
        (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun a ha => ⟨Fin.cast G.ramTarget_rkK a, by
          rw [Finset.mem_filter] at ha ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          dsimp only [xFun]; simp only [Fin.cast_cast, Fin.cast_refl, id_eq]; exact ha.2,
          by ext; rfl⟩)
    rw [hflt, card_hnSlopeListK_lt G.RRDual.b G.RRDual.X G.RRDual_good.1 G.ramTarget
      G.ramTarget_fg (s - Real.log (Fintype.card G.W : ℝ) - τ), G.ramTarget_rkK]
  exact
    { ι := G.W
      κ := G.RRDual.ι
      κ₁ := G.κ₁
      d := G.d
      r := fun u => Fintype.card (G.Nu u).ι
      Bf := G.Bf
      Vr := G.Vr
      ga := G.ga
      Dstar := G.Dstar
      sg := G.sg
      η0 := G.η0
      η1 := G.η1
      e0 := G.e0
      de := G.de
      δ := G.δ
      isIsom := G.isIsom
      ga_pos := G.ga_pos
      Dstar_pos := G.Dstar_pos
      sg_pos := G.sg_pos
      sg_le_bar := G.sg_le_bar
      sgBar_le := G.sgBar_le
      rank_ge := G.rank_ge
      η0_ge := G.η0_ge
      η0_le := G.η0_le
      η1_le := G.η1_le
      e0_nonneg := G.e0_nonneg
      e0_le_bar := G.e0_le_bar
      sqrt_e0_le := G.sqrt_e0_le
      de_nonneg := G.de_nonneg
      de_le_bar := G.de_le_bar
      deBar_le := G.deBar_le
      corV := G.corV
      gramInput := G.gramInput
      δ_nonneg := G.δ_nonneg
      δ_le_bar := G.δ_le_bar
      delBar_le := G.delBar_le
      card_ge := G.card_ge
      κ_pos := G.RRDual_card_pos
      cardW_ge_one := Fintype.card_pos
      y := yFun
      y_mean := hy_mean
      y_top := hy_top
      x := xFun
      x_min := hx_min
      Nτ := Nτ
      T := T
      Nτ_corank := hNτ_corank
      T_proj := hT_proj
      T_tail := hT_tail }

/-- **Independent Target Slope Identity (`toStage2GramFrameFiber_muCC_eq`)**:
proves that the constructed `Stage2GramFrameFiber`'s ambient slope `F.muCC` is LITERALLY
`(dualHLat RR).mu - (2 / [K : ℚ]) * log (Ideal.absNorm 𝔟) = -RR.mu - ramGain`
— **ZERO `F.muCC = s` short-circuit**! -/
theorem toStage2GramFrameFiber_muCC_eq (G : RamifiedHLatGramFrame K)
    {s uF : ℝ} (HH : ℝ) {muMinCC : ℝ}
    (hs : s * (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) ≤
      ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u))
    (huF : ∀ u : G.W, (G.Nu u).muMax - G.h u ≤ s + uF)
    (hmuMin : muMinCC ≤ G.RRDual.muMin - G.ramGain) :
    (G.toStage2GramFrameFiber HH hs huF hmuMin).muCC = G.RRDual.mu - G.ramGain ∧
    (G.toStage2GramFrameFiber HH hs huF hmuMin).muCC = -G.RR.mu - G.ramGain := by
  have h1 : (G.toStage2GramFrameFiber HH hs huF hmuMin).muCC = G.RRDual.mu - G.ramGain := by
    unfold Stage2GramFrameFiber.muCC toStage2GramFrameFiber
    dsimp only
    have hre : ∑ j : Fin (Fintype.card G.RRDual.ι),
        hnSlopeListK G.RRDual.b G.RRDual.X G.RRDual_good.1 G.ramTarget G.ramTarget_fg
          (Fin.cast G.ramTarget_rkK.symm j) =
        ∑ a : Fin (rkK (K := K) G.ramTarget),
          hnSlopeListK G.RRDual.b G.RRDual.X G.RRDual_good.1 G.ramTarget G.ramTarget_fg a :=
      Fintype.sum_equiv (finCongr G.ramTarget_rkK.symm) _ _ (fun _ => rfl)
    rw [hre, ← G.ramTarget_rkK, mean_hnSlopeListK G.RRDual.b G.RRDual.X G.RRDual_good.1
      G.ramTarget G.ramTarget_fg G.ramTarget_ne_bot]
    exact (ramified_ideal_twist_invariants G.RRDual.b G.RRDual.X G.RRDual_good.1
      G.RRDual.L G.RRDual_good.2.1 G.RRDual_ne_bot G.ramIdeal G.ramIdeal_ne_bot).1
  have hdual := (hlat_duality_slope_neg G.RR G.RR_good G.RR_rk_pos).1
  exact ⟨h1, by rw [h1, hdual]⟩

/-- Unramified specialization (`G.ramIdeal = ⊤`): `F.muCC = (dualHLat RR).mu = -RR.mu` verbatim! -/
theorem toStage2GramFrameFiber_muCC_eq_unramified (G : RamifiedHLatGramFrame K)
    (hunram : G.ramIdeal = ⊤) {s uF : ℝ} (HH : ℝ) {muMinCC : ℝ}
    (hs : s * (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) ≤
      ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u))
    (huF : ∀ u : G.W, (G.Nu u).muMax - G.h u ≤ s + uF)
    (hmuMin : muMinCC ≤ G.RRDual.muMin) :
    let hmuMin' : muMinCC ≤ G.RRDual.muMin - G.ramGain := by
      unfold ramGain; rw [hunram, Ideal.absNorm_top]; simp; exact hmuMin
    (G.toStage2GramFrameFiber HH hs huF hmuMin').muCC = (dualHLat G.RR).mu := by
  intro hmuMin'
  have h := (G.toStage2GramFrameFiber_muCC_eq HH hs huF hmuMin').1
  have h0 : G.ramGain = 0 := by unfold ramGain; rw [hunram, Ideal.absNorm_top]; simp
  rw [h, h0, sub_zero]

end RamifiedHLatGramFrame

/-- **Main Deliverable 3 (`bost_slope_ineq_from_ramified_frame`)**:
Proves the sharp Bost slope inequality into the **independent** target slope `mu(RR^∨)`
(ZERO `F.muCC = s` short-circuit!), with both:
1. Full `Stage2GramFrameFiber.toBostFiber.SlopeIneq` discharge, AND
2. Explicit ramified sharp lower bound into `(dualHLat RR).mu = -RR.mu`:
```
s + (2 / [K : ℚ]) * log (Ideal.absNorm 𝔟) - log |W|
  - (1 - δ)⁻¹ * (4 * uF * log (1 + HH / uF) + ((5 * sg + 3 * √de) + 4 * √(2 * e0)) * HH)
  ≤ (dualHLat RR).mu
```
(and dropping the nonnegative ramification gain yields the exact target form
`s - log |W| - (1 - δ)⁻¹ * (...) ≤ (dualHLat RR).mu`!). -/
theorem bost_slope_ineq_from_ramified_frame
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (G : RamifiedHLatGramFrame K)
    {s uF HH muMinCC : ℝ}
    (huF0 : 0 ≤ uF)
    (hs : s * (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) ≤
      ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u))
    (huF : ∀ u : G.W, (G.Nu u).muMax - G.h u ≤ s + uF)
    (hmuMin : muMinCC ≤ G.RRDual.muMin - G.ramGain)
    (hHH_ge : s - muMinCC ≤ HH) (hHH_pos : 0 < HH) :
    let F := G.toStage2GramFrameFiber HH hs huF hmuMin
    F.toBostFiber.SlopeIneq ∧
    F.muCC = (dualHLat G.RR).mu - G.ramGain ∧
    s + G.ramGain - Real.log (Fintype.card G.W : ℝ) -
        (1 - G.δ)⁻¹ * (4 * uF * Real.log (1 + HH / uF) +
          ((5 * G.sg + 3 * Real.sqrt G.de) + 4 * Real.sqrt (2 * G.e0)) * HH) ≤
      (dualHLat G.RR).mu ∧
    s - Real.log (Fintype.card G.W : ℝ) -
        (1 - G.δ)⁻¹ * (4 * uF * Real.log (1 + HH / uF) +
          ((5 * G.sg + 3 * Real.sqrt G.de) + 4 * Real.sqrt (2 * G.e0)) * HH) ≤
      (dualHLat G.RR).mu := by
  intro F
  have hSlope : F.toBostFiber.SlopeIneq := F.toBostSlopeIneq huF0
  have hmuCC : F.muCC = (dualHLat G.RR).mu - G.ramGain :=
    (G.toStage2GramFrameFiber_muCC_eq HH hs huF hmuMin).1
  have hδ1 : G.δ < 1 := by linarith [G.δ_le_bar, G.delBar_le]
  have hη0 : 0 ≤ F.etaVal := F.etaVal_bounds.1
  have he0 : 0 ≤ F.eVal := F.eVal_bounds.1
  have he4 : F.eVal ≤ 1 / 4 := F.eVal_bounds.2.2
  have hineq := hSlope G.δ_nonneg hδ1 hη0 he0 he4 hHH_ge hHH_pos
  change s - Real.log (Fintype.card G.W : ℝ) -
      (1 - G.δ)⁻¹ * (4 * uF * Real.log (1 + HH / uF) +
        ((5 * G.sg + 3 * Real.sqrt G.de) + 4 * Real.sqrt (2 * G.e0)) * HH) ≤ F.muCC at hineq
  rw [hmuCC] at hineq
  have hgain_nn : 0 ≤ G.ramGain := G.ramGain_nonneg
  exact ⟨hSlope, hmuCC, by linarith, by linarith⟩

/-- **Banaszczyk-Powered Corollary of `bost_slope_ineq_from_ramified_frame`**:
when `s` and `uF` are the exact canonical `G.meanSlope` and `G.slopeExcess`, and `HH > 0`
satisfies the Banaszczyk `O(log rk)` gap bound on `RR^∨` alongside `s + ramGain ≤ (dualHLat RR).muMax`,
BOTH `s - muMinCC ≤ HH` AND the sharp Bost slope inequality into `(dualHLat RR).mu` hold
automatically with ZERO a priori `muMinCC` assumption! -/
theorem bost_slope_ineq_from_ramified_frame_banaszczyk
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (G : RamifiedHLatGramFrame K)
    {HH : ℝ} (hHH_pos : 0 < HH)
    (hs_le_max : G.meanSlope + G.ramGain ≤ (dualHLat G.RR).muMax)
    (hBan : letI := (discreteTopology_zRealize_of_fg G.RRDual.b G.RRDual.X G.RRDual_good.1
        G.RRDual.L G.RRDual_good.2.1);
      letI := Stage4ArakelovBost.discreteTopology_dualLat G.RRDual.zRealize;
      -2 * Real.log (Stage2SiegelReduction.lambda1 G.RRDual.zRealize *
        Stage2SiegelReduction.lambda1 (Stage4ArakelovBost.dualLat G.RRDual.zRealize)) +
        2 * Real.log ((Module.finrank ℚ K * G.RRDual.rank : ℕ) : ℝ) ≤ HH) :
    let s := G.meanSlope
    let uF := G.slopeExcess
    let muMinCC := G.RRDual.muMin - G.ramGain
    s - muMinCC ≤ HH ∧
    s + G.ramGain - Real.log (Fintype.card G.W : ℝ) -
        (1 - G.δ)⁻¹ * (4 * uF * Real.log (1 + HH / uF) +
          ((5 * G.sg + 3 * Real.sqrt G.de) + 4 * Real.sqrt (2 * G.e0)) * HH) ≤
      (dualHLat G.RR).mu := by
  intro s uF muMinCC
  have hflat : IsFlatHLat G.RRDual HH :=
    flatLattice_of_banaszczyk G.RRDual G.RRDual_good G.RRDual_ne_bot hBan
  have hHH_ge : s - muMinCC ≤ HH := by
    unfold IsFlatHLat at hflat
    dsimp only [s, muMinCC]
    linarith
  have hs : s * (∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ)) ≤
      ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) * ((G.Nu u).mu - G.h u) := by
    have hden : 0 < ∑ u : G.W, (Fintype.card (G.Nu u).ι : ℝ) :=
      Finset.sum_pos (fun u _ => Nat.cast_pos.mpr (G.Nu_card_pos u)) Finset.univ_nonempty
    dsimp only [s]; unfold RamifiedHLatGramFrame.meanSlope SlopeInequality.wmean
    rw [div_mul_cancel₀ _ hden.ne']
  have huF : ∀ u : G.W, (G.Nu u).muMax - G.h u ≤ s + uF := fun u => by
    dsimp only [s, uF]; unfold RamifiedHLatGramFrame.slopeExcess
    have hle := Finset.le_sup' (f := fun u : G.W => (G.Nu u).muMax - G.h u) (Finset.mem_univ u)
    linarith
  have hres := bost_slope_ineq_from_ramified_frame G G.slopeExcess_nonneg hs huF le_rfl hHH_ge hHH_pos
  exact ⟨hHH_ge, hres.2.2.1⟩

/-- **Direct Fiber Compiler into `Stage14Contracts.M2FiberCert` (`mkM2FiberCert_of_ramified_frames`)**:
given a `Field2FiberShell` `F` whose fibers `u0` are realized by `RamifiedHLatGramFrame` objects
`G u0` matching the fiber ranks `F.d u0`, slopes `F.muN u0`, `F.muMaxN u0`, `F.h u0`, and
independent target minimal slopes `F.muMinCC u0 ≤ (G u0).RRDual.muMin - (G u0).ramGain`,
compiles directly into `Stage14Contracts.M2FiberCert F` ready for `Stage14M2_FrameRealCompile`! -/
def mkM2FiberCert_of_ramified_frames
    {K_field : Type} [Field K_field] [NumberField K_field] [IsTotallyComplex K_field] [StarRing K_field]
    {ψ : PChar} {eL K cHH eps x : ℝ} {q d_aux e_page : ℕ}
    {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (F : Field2FiberShell ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)
    (G : F.U0 → RamifiedHLatGramFrame K_field)
    (hEquivW : ∀ u0, F.W u0 ≃ (G u0).W)
    (hBar : ∀ u0, (G u0).delBar = F.delBar ∧ (G u0).sgBar = F.sgBar ∧
      (G u0).deBar = F.deBar ∧ (G u0).e0Bar = F.e0Bar)
    (hd_eq : ∀ u0 (u : F.W u0), F.d u0 u = (Fintype.card ((G u0).Nu (hEquivW u0 u)).ι : ℝ))
    (hmuN_eq : ∀ u0 (u : F.W u0),
      F.muN u0 u - F.h u0 u = ((G u0).Nu (hEquivW u0 u)).mu - (G u0).h (hEquivW u0 u))
    (hmuMaxN_eq : ∀ u0 (u : F.W u0),
      F.muMaxN u0 u - F.h u0 u = ((G u0).Nu (hEquivW u0 u)).muMax - (G u0).h (hEquivW u0 u))
    (hmuMinCC : ∀ u0, F.muMinCC u0 ≤ (G u0).RRDual.muMin - (G u0).ramGain)
    (htrace_le : (5 * F.sgBar + 3 * Real.sqrt F.deBar + 4 * Real.sqrt (2 * F.e0Bar)) *
        (x ^ cHH * Real.exp (x ^ eps)) ≤ K * x ^ eps * ((Fintype.card F.Top : ℝ) * F.a))
    (hslopes : ∀ u0 (u : F.W u0),
      -(F.cSlope * (Fintype.card F.Top : ℝ) * F.a * F.La * (1 + (F.R.m : ℝ) / (F.R.k : ℝ))) ≤
        F.muM u0 u ∧
      F.muMaxM u0 u ≤ F.cSlope * (Fintype.card F.Top : ℝ) * F.a * F.La)
    (hHH : ∀ u0,
      SlopeInequality.wmean (F.d u0) (fun u => F.muN u0 u - F.h u0 u) - F.muMinCC u0 ≤ F.HH u0 ∧
      0 < F.HH u0 ∧ F.HH u0 ≤ x ^ cHH * Real.exp (x ^ eps)) :
    M2FiberCert F where
  gramFiber := fun u0 => by
    have hcardW : Fintype.card (G u0).W = Fintype.card (F.W u0) := (Fintype.card_congr (hEquivW u0)).symm
    obtain ⟨hdel, hsg, hde, he0⟩ := hBar u0
    let s := SlopeInequality.wmean (F.d u0) (fun u => F.muN u0 u - F.h u0 u)
    let uF := Finset.univ.sup' Finset.univ_nonempty (fun u : F.W u0 => F.muMaxN u0 u - F.h u0 u) - s
    have hden_eq : ∑ u : F.W u0, F.d u0 u =
        ∑ w : (G u0).W, (Fintype.card ((G u0).Nu w).ι : ℝ) := by
      refine Fintype.sum_equiv (hEquivW u0) _ _ (fun u => hd_eq u0 u)
    have hnum_eq : ∑ u : F.W u0, F.d u0 u * (F.muN u0 u - F.h u0 u) =
        ∑ w : (G u0).W, (Fintype.card ((G u0).Nu w).ι : ℝ) *
          (((G u0).Nu w).mu - (G u0).h w) := by
      refine Fintype.sum_equiv (hEquivW u0) _ _ (fun u => by rw [hd_eq u0 u, hmuN_eq u0 u])
    have hden_pos : 0 < ∑ w : (G u0).W, (Fintype.card ((G u0).Nu w).ι : ℝ) :=
      Finset.sum_pos (fun w _ => Nat.cast_pos.mpr ((G u0).Nu_card_pos w)) Finset.univ_nonempty
    have hs : s * (∑ w : (G u0).W, (Fintype.card ((G u0).Nu w).ι : ℝ)) ≤
        ∑ w : (G u0).W, (Fintype.card ((G u0).Nu w).ι : ℝ) *
          (((G u0).Nu w).mu - (G u0).h w) := by
      dsimp only [s]; unfold SlopeInequality.wmean
      rw [hden_eq, hnum_eq, div_mul_cancel₀ _ hden_pos.ne']
    have huF : ∀ w : (G u0).W, ((G u0).Nu w).muMax - (G u0).h w ≤ s + uF := by
      intro w
      let u := (hEquivW u0).symm w
      have hw : hEquivW u0 u = w := (hEquivW u0).apply_symm_apply w
      have h1 : ((G u0).Nu w).muMax - (G u0).h w = F.muMaxN u0 u - F.h u0 u := by
        rw [← hw, hmuMaxN_eq u0 u]
      have hle := Finset.le_sup' (f := fun u : F.W u0 => F.muMaxN u0 u - F.h u0 u) (Finset.mem_univ u)
      dsimp only [uF]; linarith
    have hfib := (G u0).toStage2GramFrameFiber (F.HH u0) hs huF (hmuMinCC u0)
    rw [hcardW, hdel, hsg, hde, he0] at hfib
    exact hfib
  trace_le := htrace_le
  slopes := hslopes
  hhBound := hHH

/-- Exact discharge of the `gramFrame_discharges_bost` field of
`Stage14Contracts.M2HLatBostContract`. -/
theorem gramFrame_discharges_bost_contract
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (G : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar)
    (huF : 0 ≤ uF) :
    G.toBostFiber.SlopeIneq :=
  G.toBostSlopeIneq huF

/-- **Verification Bridge for `Stage14Contracts.M2HLatBostContract`**:
packages the two ramified Bost fields (`joint_a_ramified_holds` and `gramFrame_discharges_bost`)
of `Stage14Contracts.M2HLatBostContract`, ready for `Stage14M2_FrameRealCompile`! -/
theorem m2_ramified_bost_contract_fields :
    (∀ (L_N L_RR : HLatAnchor) (φ : L_N.L →ₗ[ℤ] L_RR.L) (C_op : ℝ) (D_div : ℕ),
      0 < D_div → Function.Injective φ →
      (∀ x : L_N.L, ‖((φ x : L_RR.L) : L_RR.E)‖ ≤ C_op * ‖(x : L_N.E)‖) →
      (∀ x : L_N.L, ∃ y : L_RR.L, φ x = (D_div : ℤ) • y) →
      L_N.slope + Real.log (D_div : ℝ) ≤ L_RR.muMax + Real.log C_op) ∧
    (∀ {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
      (G : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar),
      0 ≤ uF → G.toBostFiber.SlopeIneq) :=
  ⟨joint_a_ramified_holds_contract, fun G huF => gramFrame_discharges_bost_contract G huF⟩

end RamifiedFrameToBostFiber

end RHDirect.Stage14M2_RamifiedJointBost

end
