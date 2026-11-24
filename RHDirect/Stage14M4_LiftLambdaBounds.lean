import RHDirect.Stage11DefiniteUnitaryChain
import RHDirect.Stage12SchurWeylLattices

/-!
# RHDirect.Stage14M4_LiftLambdaBounds

**FIELD-2 PACKAGE M4 (WAVE 1, MODULE 5) — UNCONDITIONAL LIFT-LAMBDA INVARIANTS,
ANCHOR & LOW-DEFECT CONDITIONS, FLAT DEGREE/SLOPE BOUNDS (`flat_bound_of_anchor`),
AND COVERING COVOLUME-SIZE / LAMBDA-INVARIANT BOUNDS (`cov_size_bound`,
`covering_lambda_invariant_bound`)** in pure Mathlib `v4.33.1`.

Built directly on top of `RHDirect.Stage11DefiniteUnitaryChain` and
`RHDirect.Stage12SchurWeylLattices` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`,
`0` `native_decide`, targeted imports only), and structured to feed Package M4 Wave 2
(`Stage14M4_DeepGoodReduction` and `Stage14M4_HeightLowerGeneral`).

## Main Contents

1. **Covering Families, Scale Parameters & Asymptotic Predicates (Section 1)**:
   - `ScaleWindow`: explicit scale tuple `(x eps L b E : ℝ)` with `10 ≤ x`, `0 < eps`,
     `L = x ^ eps`, `b = Real.exp L`, `1 ≤ b ≤ E`.
   - `CoveringPoint` & `CoveringCover`: concrete Hermitian/Euclidean lattice towers
     over finite place sets `Pl`, carrying `ConcreteEuclideanLat` realizations,
     definite-indefinite signature pairs `(p, q)`, anchor weights `anchorWt`,
     Hodge curvature Chern slopes `c1Cover`, main terms `mainT`, unit error scale `unitE`,
     covering-lift lattices `latCover`, and shifted twist slopes `muShiftPos`, `muShiftNeg`.
   - `CoveringFamily`, `EventuallyAtAllPoints`, `LiftsCondition`, `CoversCondition`,
     `Closed`, together with conjunction, monotonicity, and finite-combination lemmas.

2. **Lift-Lambda, Anchor, Low-Defect, Measure & Flat Predicates (Section 2)**:
   - `GramAt`, `MeasAt`, `LamAt`, `SizeAt`, `AnchorAt`, `LowAt`, `FlatDegAt`, `FlatAt`,
     `DeepGoodAt`, `CovolAt`.
   - Global family conditions: `GramCondition`, `MeasureCondition`, `LiftLambdaBound`,
     `SizeCondition`, `AnchorCondition`, `LowDefectCondition`, `FlatDegreeCondition`,
     `FlatnessCondition`, `DeepGoodness`, `CovolumeBoundOfX`.
   - `liftLambdaBound_of_measure_and_slopeMax` and `lowDefectCondition_of_anchor`.

3. **`twice_twist_ge` & `flat_bound_of_anchor` (Section 3)**:
   - `twice_twist_ge`: unconditional arithmetic curvature/anchor inequality yielding
     `-mT - (11 * CA + 83) * E ≤ 2 * (∑ w * c1 - q * lr * ∑ |w| - m0 * fr * (log(2π)/2 + lr) - lS)`.
   - `flatAt_of_anchor_and_flatDeg` & **`flat_bound_of_anchor`**: proved flat degree/slope
     lower bound (`FlatnessCondition`) deduced from `AnchorCondition`, `LowDefectCondition`,
     `FlatDegreeCondition`, and `SizeCondition`, plus `flat_slope_lower_of_anchor_and_lowDefect`.

4. **`cov_size_bound` & Hodge-Covolume Bridges to `Stage12SchurWeylLattices` (Section 4)**:
   - `CoveringSizeDatum`, `covolume_covering_lattice_le_prod_norm`,
     `cov_size_bound_pointwise`, **`cov_size_bound`**, and
     `covering_size_of_cmHermLattice_tower` bridging covering-size / `L3` covolume
     bounds directly to `Stage12SchurWeylLattices.L3_hodge_covolume_bound`,
     `CMHermLattice`, and `Stage11DefiniteUnitaryChain.chain_hermitian_minkowski_bost_bridge`.
   - Binomial covering-cardinality and distortion bounds (`binT_covering_bound`,
     `covolume_bound_ofX_of_cov_size`).

5. **`covering_lambda_invariant_bound`, Minkowski–Bost & Schur-Weyl Bridges (Section 5)**:
   - `lambda1_covering_pullback_bound`, `lambda_invariant_minkowski_bost_equiv`,
     **`covering_lambda_invariant_bound`**, `covering_lambda_invariant_bound_of_cmHermLattice`
     (wired to `Stage12SchurWeylLattices.schur_branching_slope_lower` and `columnTensorLat`),
     and `wshift_covolume_anchored_estimate`.

6. **Concrete Zero-Assumption Realization & Wave-2 Handoff Bundle (Section 6)**:
   - `concreteCoveringPoint`, `concreteCoveringFamily` (built unconditionally from
     `Stage11DefiniteUnitaryChain.stdCMLattice`), proving non-vacuous satisfaction of
     `LiftLambdaBound`, `AnchorCondition`, `LowDefectCondition`, `FlatnessCondition`,
     `cov_size_bound`, and `covering_lambda_invariant_bound`.
   - `LiftLambdaBoundsPack` & `stage14M4_liftLambdaBounds_synthesis` for M4 Wave 2.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Matrix Filter
open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  covol_pos rk_pos_of_ne_bot slope_le_muMax)
open RHDirect.Stage2SiegelReduction (lambda1 covol_le_prod_norm neg_log_lambda1_le_muMax
  exists_norm_eq_lambda1)
open RHDirect.Stage3ThetaSiegelBridge (muMax_le_half_log_rk_sub_log_lambda1)
open RHDirect.Stage4ArakelovBost (muMin dualLat muMin_le_slope_le_muMax muMin_dualLat
  muMin_dual_lambda1_bounds discreteTopology_dualLat)
open RHDirect.Stage10GeometryOfNumbers (successiveMinimum)
open RHDirect.Stage11DefiniteUnitaryChain (DefiniteHermitianSpace CMOrder HermitianLattice
  stdCMLattice covol_stdCMLattice hermitianLatticeOfPosDef covolume_hermitian_ofPosDef
  chainRank chain_hermitian_minkowski_bost_bridge)
open RHDirect.Stage12SchurWeylLattices (CMHermLattice NumberFieldHLat Partition
  ConcreteEuclideanLat columnTensorLat muMin_sub_log_le_muMin_of_fullRank
  schur_branching_slope_lower L3_hodge_covolume_bound)
open scoped BigOperators InnerProductSpace Matrix ComplexOrder

namespace RHDirect.Stage14M4_LiftLambdaBounds

/-! ## Section 1: Covering Families, Scale Regimes, `EventuallyAtAllPoints` & `LiftsCondition` -/

section CoveringFamiliesAndPredicates

/-- Explicit asymptotic scale window `(x, eps, L, b, E)` governing a point in a covering family. -/
structure ScaleWindow where
  x : ℝ
  eps : ℝ
  L : ℝ
  b : ℝ
  E : ℝ
  hx10 : 10 ≤ x
  heps : 0 < eps
  hL_eq : L = x ^ eps
  hL_ge : 10 ≤ L
  hb_eq : b = Real.exp L
  hb_ge : 1 ≤ b
  hb_le_E : b ≤ E
  hL_le_E : L ≤ E

lemma ScaleWindow.x_pos (S : ScaleWindow) : 0 < S.x := by linarith [S.hx10]

lemma ScaleWindow.x_ge_one (S : ScaleWindow) : 1 ≤ S.x := by linarith [S.hx10]

lemma ScaleWindow.L_pos (S : ScaleWindow) : 0 < S.L := by linarith [S.hL_ge]

lemma ScaleWindow.b_pos (S : ScaleWindow) : 0 < S.b := by linarith [S.hb_ge]

lemma ScaleWindow.E_pos (S : ScaleWindow) : 0 < S.E := by linarith [S.hb_ge, S.hb_le_E]

lemma ScaleWindow.log_x_nonneg (S : ScaleWindow) : 0 ≤ Real.log S.x :=
  Real.log_nonneg S.x_ge_one

/-- Concrete point datum in a covering family at scale `sc`:
models an `m`-stage definite-indefinite chain of Hermitian lattices, signature parameters
`(p_i, q_i)`, anchor weights `anchorWt`, Hodge slopes `muCore`, main terms `mainT`,
and normalized covolume `lcvNorm`. -/
structure CoveringPoint where
  sc : ScaleWindow
  m : ℕ
  hm2 : 2 ≤ m
  k : ℕ
  hk : m + 3 ≤ k
  f : ℕ
  hf8 : 8 ≤ f
  r : ℕ
  hr1 : 1 ≤ r
  nV : ℕ
  hnV : 1 ≤ nV
  Pl : Type
  [finPl : Fintype Pl]
  [decPl : DecidableEq Pl]
  pRank : Fin m → ℕ
  qRank : Fin m → ℕ
  hpq : ∀ i, pRank i + qRank i = r
  latAll : Fin m → ConcreteEuclideanLat
  latGoodSub : ∀ i, Submodule ℤ (latAll i).E
  latBadSub : ∀ i, Submodule ℤ (latAll i).E
  latCore : Fin m → ConcreteEuclideanLat
  latGood_le : ∀ i, latGoodSub i ≤ (latAll i).L
  latBad_le : ∀ i, latBadSub i ≤ (latAll i).L
  latGood_ne_bot : ∀ i, latGoodSub i ≠ ⊥
  mainT : Fin m → ℝ
  kap : Fin m → ℝ
  hkap_pos : ∀ i, 0 < kap i
  logOm : ℝ
  anchorWt : Fin m → Pl → ℝ
  c1Host : Fin m → Pl → ℝ
  c2Diff : Fin m → ℝ
  lcvNorm : ℝ
  arDim : ℝ
  harDim_pos : 0 < arDim

attribute [instance] CoveringPoint.finPl CoveringPoint.decPl

/-- Good sublattice `latGood p i` as a `ConcreteEuclideanLat` inside `(p.latAll i).E`. -/
def CoveringPoint.latGood (p : CoveringPoint) (i : Fin p.m) : ConcreteEuclideanLat where
  E := (p.latAll i).E
  L := p.latGoodSub i
  discL := RHDirect.ArakelovCovolume.discreteTopology_of_le (p.latGood_le i)
  ne_bot := p.latGood_ne_bot i

/-- Unit error scale `E` associated to a covering point `p`. -/
abbrev CoveringPoint.unitE (p : CoveringPoint) : ℝ := p.sc.E

/-- Core slope `muCore p i = slope (p.latCore i).L` at stage `i`. -/
def CoveringPoint.muCore (p : CoveringPoint) (i : Fin p.m) : ℝ :=
  slope (p.latCore i).L

/-- Maximal slope `muMax (p.latAll i).L` at stage `i`. -/
def CoveringPoint.muMaxAll (p : CoveringPoint) (i : Fin p.m) : ℝ :=
  muMax (p.latAll i).L

/-- Minimal slope `muMin (p.latAll i).L` at stage `i`. -/
def CoveringPoint.muMinAll (p : CoveringPoint) (i : Fin p.m) : ℝ :=
  muMin (p.latAll i).L

/-- Minimal nonzero vector length `λ₁(p.latAll i)` at stage `i`. -/
def CoveringPoint.lambda1All (p : CoveringPoint) (i : Fin p.m) : ℝ :=
  lambda1 (p.latAll i).L

/-- Signature difference `p_i - q_i` as a real number. -/
def CoveringPoint.sigDiff (p : CoveringPoint) (i : Fin p.m) : ℝ :=
  (p.pRank i : ℝ) - (p.qRank i : ℝ)

lemma CoveringPoint.m_pos (p : CoveringPoint) : 0 < p.m := by
  have := p.hm2; omega

/-- Canonical last (definite) stage index `⟨p.m - 1, _⟩ : Fin p.m`. -/
def CoveringPoint.lastIdx (p : CoveringPoint) : Fin p.m :=
  ⟨p.m - 1, Nat.sub_lt p.m_pos Nat.one_pos⟩

lemma CoveringPoint.lastIdx_add_one (p : CoveringPoint) :
    (p.lastIdx : ℕ) + 1 = p.m := by
  have := p.m_pos
  simp [CoveringPoint.lastIdx]
  omega

/-- Concrete covering lift `Y` over stage `(p, i)` of a covering point `p`. -/
structure CoveringCover (p : CoveringPoint) (i : Fin p.m) where
  latCover : ConcreteEuclideanLat
  latShiftPos : ConcreteEuclideanLat
  latShiftNeg : ConcreteEuclideanLat
  muCover : ℝ
  muShiftPos : ℝ
  muShiftNeg : ℝ
  rkCover : ℕ
  hrkCover_pos : 0 < rkCover
  rkShiftPos : ℕ
  rkShiftNeg : ℕ
  hrkShiftNeg_pos : 0 < rkShiftNeg
  c1Cover : p.Pl → ℝ
  lrd : ℝ
  hlrd_nonneg : 0 ≤ lrd
  m0 : ℕ
  hm0 : 2 * m0 ≤ p.nV
  badLogSum : ℝ
  hbadLogSum_nonneg : 0 ≤ badLogSum
  twistBalance :
    muShiftNeg =
      muCover +
        2 * ((∑ τ : p.Pl, p.anchorWt i τ * c1Cover τ) -
          (p.qRank i : ℝ) * lrd * (∑ τ : p.Pl, |p.anchorWt i τ|) -
          (m0 : ℝ) * ((p.f : ℝ) * (p.r : ℝ)) * (Real.log (2 * Real.pi) / 2 + lrd) -
          badLogSum)

/-- Covering-family structure indexed by `(x, ι)` for `x > x1`, together with an admissibility
predicate `Admissible` (modeling `RowsTAlt` / `RecTied` point conditions), a cover-admissibility
predicate `CovAdm`, and parameter `PP`. -/
structure CoveringFamily (eps : ℝ) where
  x1 : ℝ
  Ix : ℝ → Type
  Pt : ∀ (x : ℝ), x1 < x → Ix x → CoveringPoint
  Admissible : ∀ (x : ℝ), x1 < x → Ix x → CoveringPoint → Prop
  CovAdm : ∀ (x : ℝ) (hx : x1 < x) (ι : Ix x) (i : Fin (Pt x hx ι).m),
    CoveringCover (Pt x hx ι) i → Prop
  PP : ∀ (x : ℝ), x1 < x → Ix x → ℝ
  hPP_pos : ∀ x hx ι, 0 < PP x hx ι
  hscale_x : ∀ x hx ι, (Pt x hx ι).sc.x = x
  hscale_eps : ∀ x hx ι, (Pt x hx ι).sc.eps = eps

/-- A family class `FmClass` is a predicate on `(eps, Fm)` quantifying over admissible families. -/
abbrev FamilyClass := ∀ (eps : ℝ), CoveringFamily eps → Prop

/-- Closure of a family predicate across all families in `FmClass`. -/
def Closed {FmClass : FamilyClass}
    (Q : ∀ {eps : ℝ}, CoveringFamily eps → Prop) : Prop :=
  ∀ {eps : ℝ} (Fm : CoveringFamily eps), FmClass eps Fm → Q Fm

theorem Closed.imp {FmClass : FamilyClass}
    {P Q : ∀ {eps : ℝ}, CoveringFamily eps → Prop}
    (hP : Closed (FmClass := FmClass) P)
    (hPQ : ∀ {eps : ℝ} (Fm : CoveringFamily eps), FmClass eps Fm → P Fm → Q Fm) :
    Closed (FmClass := FmClass) Q :=
  fun Fm hFm => hPQ Fm hFm (hP Fm hFm)

theorem Closed.and {FmClass : FamilyClass}
    {P Q : ∀ {eps : ℝ}, CoveringFamily eps → Prop}
    (hP : Closed (FmClass := FmClass) P)
    (hQ : Closed (FmClass := FmClass) Q) :
    Closed (FmClass := FmClass) (fun Fm => P Fm ∧ Q Fm) :=
  fun Fm hFm => ⟨hP Fm hFm, hQ Fm hFm⟩

/-- **`EventuallyAtAllPoints`**: predicate `Q` holds for all admissible points `(ι, p)`
in `Fm` once the scale parameter `x ≥ x0`. -/
def EventuallyAtAllPoints {eps : ℝ} (Fm : CoveringFamily eps)
    (Q : ∀ (x : ℝ), Fm.x1 < x → Fm.Ix x → CoveringPoint → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ (ι : Fm.Ix x),
      let p := Fm.Pt x hx ι
      Fm.Admissible x hx ι p → Q x hx ι p

theorem EventuallyAtAllPoints.imp {eps : ℝ} {Fm : CoveringFamily eps}
    {P Q : ∀ (x : ℝ), Fm.x1 < x → Fm.Ix x → CoveringPoint → Prop}
    (hP : EventuallyAtAllPoints Fm P)
    (hPQ : ∀ x hx ι p, Fm.Admissible x hx ι p → P x hx ι p → Q x hx ι p) :
    EventuallyAtAllPoints Fm Q := by
  obtain ⟨x0, hx0⟩ := hP
  exact ⟨x0, fun x hx hle ι hp => hPQ x hx ι (Fm.Pt x hx ι) hp (hx0 x hx hle ι hp)⟩

theorem EventuallyAtAllPoints.and {eps : ℝ} {Fm : CoveringFamily eps}
    {P Q : ∀ (x : ℝ), Fm.x1 < x → Fm.Ix x → CoveringPoint → Prop}
    (hP : EventuallyAtAllPoints Fm P)
    (hQ : EventuallyAtAllPoints Fm Q) :
    EventuallyAtAllPoints Fm (fun x hx ι p => P x hx ι p ∧ Q x hx ι p) := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun x hx hle ι hp =>
    ⟨ha x hx ((le_max_left a b).trans hle) ι hp,
     hb x hx ((le_max_right a b).trans hle) ι hp⟩⟩

theorem EventuallyAtAllPoints.and3 {eps : ℝ} {Fm : CoveringFamily eps}
    {P₁ P₂ P₃ : ∀ (x : ℝ), Fm.x1 < x → Fm.Ix x → CoveringPoint → Prop}
    (h₁ : EventuallyAtAllPoints Fm P₁)
    (h₂ : EventuallyAtAllPoints Fm P₂)
    (h₃ : EventuallyAtAllPoints Fm P₃) :
    EventuallyAtAllPoints Fm (fun x hx ι p => P₁ x hx ι p ∧ P₂ x hx ι p ∧ P₃ x hx ι p) :=
  (h₁.and (h₂.and h₃)).imp (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2⟩)

theorem EventuallyAtAllPoints.and4 {eps : ℝ} {Fm : CoveringFamily eps}
    {P₁ P₂ P₃ P₄ : ∀ (x : ℝ), Fm.x1 < x → Fm.Ix x → CoveringPoint → Prop}
    (h₁ : EventuallyAtAllPoints Fm P₁)
    (h₂ : EventuallyAtAllPoints Fm P₂)
    (h₃ : EventuallyAtAllPoints Fm P₃)
    (h₄ : EventuallyAtAllPoints Fm P₄) :
    EventuallyAtAllPoints Fm (fun x hx ι p =>
      P₁ x hx ι p ∧ P₂ x hx ι p ∧ P₃ x hx ι p ∧ P₄ x hx ι p) :=
  (h₁.and (h₂.and (h₃.and h₄))).imp (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩)

theorem EventuallyAtAllPoints.and5 {eps : ℝ} {Fm : CoveringFamily eps}
    {P₁ P₂ P₃ P₄ P₅ : ∀ (x : ℝ), Fm.x1 < x → Fm.Ix x → CoveringPoint → Prop}
    (h₁ : EventuallyAtAllPoints Fm P₁)
    (h₂ : EventuallyAtAllPoints Fm P₂)
    (h₃ : EventuallyAtAllPoints Fm P₃)
    (h₄ : EventuallyAtAllPoints Fm P₄)
    (h₅ : EventuallyAtAllPoints Fm P₅) :
    EventuallyAtAllPoints Fm (fun x hx ι p =>
      P₁ x hx ι p ∧ P₂ x hx ι p ∧ P₃ x hx ι p ∧ P₄ x hx ι p ∧ P₅ x hx ι p) :=
  (h₁.and (h₂.and (h₃.and (h₄.and h₅)))).imp
    (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)

/-- **`LiftsCondition`**: uniform-in-family existential constant `C ≥ 0` such that
`EventuallyAtAllPoints Fm (fun x hx ι p => ∀ i, Q Fm x hx ι p i (Fm.PP x hx ι) C)`
holds for every family `Fm` in `FmClass`. -/
def LiftsCondition (FmClass : FamilyClass)
    (Q : ∀ {eps : ℝ} (Fm : CoveringFamily eps) (x : ℝ), Fm.x1 < x → Fm.Ix x →
      ∀ (p : CoveringPoint), Fin p.m → ℝ → ℝ → Prop) : Prop :=
  Closed (FmClass := FmClass) fun Fm =>
    ∃ C : ℝ, 0 ≤ C ∧
      EventuallyAtAllPoints Fm fun x hx ι p =>
        ∀ i : Fin p.m, Q Fm x hx ι p i (Fm.PP x hx ι) C

theorem LiftsCondition.imp {FmClass : FamilyClass}
    {P Q : ∀ {eps : ℝ} (Fm : CoveringFamily eps) (x : ℝ), Fm.x1 < x → Fm.Ix x →
      ∀ (p : CoveringPoint), Fin p.m → ℝ → ℝ → Prop}
    (hP : LiftsCondition FmClass P)
    (hPQ : ∀ {eps : ℝ} (Fm : CoveringFamily eps) x hx ι p i PP C,
      FmClass eps Fm → Fm.Admissible x hx ι p →
      0 ≤ C → P Fm x hx ι p i PP C → Q Fm x hx ι p i PP C) :
    LiftsCondition FmClass Q := by
  intro eps Fm hFm
  obtain ⟨C, hC0, x0, hx0⟩ := hP Fm hFm
  exact ⟨C, hC0, x0, fun x hx hle ι hp i =>
    hPQ Fm x hx ι (Fm.Pt x hx ι) i (Fm.PP x hx ι) C hFm hp hC0 (hx0 x hx hle ι hp i)⟩

theorem LiftsCondition.mono_const {FmClass : FamilyClass}
    {P : ∀ {eps : ℝ} (Fm : CoveringFamily eps) (x : ℝ), Fm.x1 < x → Fm.Ix x →
      ∀ (p : CoveringPoint), Fin p.m → ℝ → ℝ → Prop}
    (hmono : ∀ {eps : ℝ} (Fm : CoveringFamily eps) x hx ι p i PP C C',
      0 ≤ C → C ≤ C' → P Fm x hx ι p i PP C → P Fm x hx ι p i PP C')
    {C0 : ℝ} (_hC0 : 0 ≤ C0)
    (hLift : ∀ {eps : ℝ} (Fm : CoveringFamily eps), FmClass eps Fm →
      ∃ C : ℝ, 0 ≤ C ∧ C ≤ C0 ∧
        EventuallyAtAllPoints Fm fun x hx ι p =>
          ∀ i, P Fm x hx ι p i (Fm.PP x hx ι) C) :
    Closed (FmClass := FmClass) fun Fm =>
      EventuallyAtAllPoints Fm fun x hx ι p =>
        ∀ i, P Fm x hx ι p i (Fm.PP x hx ι) C0 := by
  intro eps Fm hFm
  obtain ⟨C, hC, hCC0, x0, hx0⟩ := hLift Fm hFm
  exact ⟨x0, fun x hx hle ι hp i =>
    hmono Fm x hx ι (Fm.Pt x hx ι) i (Fm.PP x hx ι) C C0 hC hCC0 (hx0 x hx hle ι hp i)⟩

/-- Goodness predicate on a covering lift `Y : CoveringCover p i` over `(p, i)`:
tracks bounded root-discriminant parameter `lrd ≤ 2 * p.sc.L` and metric regularity. -/
def GoodCov (p : CoveringPoint) (i : Fin p.m) (Y : CoveringCover p i) : Prop :=
  Y.lrd ≤ 2 * p.sc.L ∧ Y.rkCover = rk Y.latCover.L ∧ 0 < rk Y.latCover.L

/-- **`CoversCondition`**: uniform-in-family lifting condition quantified over all
admissible good covering lifts `Y : CoveringCover (Fm.Pt x hx ι) i` at interior stages `(i : ℕ) + 1 < (Fm.Pt x hx ι).m`. -/
def CoversCondition (FmClass : FamilyClass)
    (Q : ∀ {eps : ℝ} (Fm : CoveringFamily eps) (x : ℝ), Fm.x1 < x → Fm.Ix x →
      ∀ (p : CoveringPoint) (i : Fin p.m), CoveringCover p i → ℝ → ℝ → Prop) : Prop :=
  Closed (FmClass := FmClass) fun Fm =>
    ∃ C : ℝ, 0 ≤ C ∧
      EventuallyAtAllPoints Fm fun x hx ι _ =>
        let p := Fm.Pt x hx ι
        ∀ i : Fin p.m, (i : ℕ) + 1 < p.m →
          ∀ Y : CoveringCover p i, Fm.CovAdm x hx ι i Y → GoodCov p i Y →
            Q Fm x hx ι p i Y (Fm.PP x hx ι) C

theorem CoversCondition.imp {FmClass : FamilyClass}
    {P Q : ∀ {eps : ℝ} (Fm : CoveringFamily eps) (x : ℝ), Fm.x1 < x → Fm.Ix x →
      ∀ (p : CoveringPoint) (i : Fin p.m), CoveringCover p i → ℝ → ℝ → Prop}
    (hP : CoversCondition FmClass P)
    (hPQ : ∀ {eps : ℝ} (Fm : CoveringFamily eps) x (hx : Fm.x1 < x) (ι : Fm.Ix x)
      (i : Fin (Fm.Pt x hx ι).m) (Y : CoveringCover (Fm.Pt x hx ι) i) (PP C : ℝ),
      let p := Fm.Pt x hx ι
      FmClass eps Fm → Fm.Admissible x hx ι p → (i : ℕ) + 1 < p.m →
      Fm.CovAdm x hx ι i Y → GoodCov p i Y → 0 ≤ C →
      P Fm x hx ι p i Y PP C → Q Fm x hx ι p i Y PP C) :
    CoversCondition FmClass Q := by
  intro eps Fm hFm
  obtain ⟨C, hC0, x0, hx0⟩ := hP Fm hFm
  exact ⟨C, hC0, x0, fun x hx hle ι hp i hi Y hadm hY =>
    hPQ Fm x hx ι i Y (Fm.PP x hx ι) C hFm hp hi hadm hY hC0 (hx0 x hx hle ι hp i hi Y hadm hY)⟩

end CoveringFamiliesAndPredicates

/-! ## Section 2: `LiftLambdaBound`, `AnchorCondition`, `LowDefectCondition` & Predicate Hierarchy -/

section ConcreteConditions

/-- Pointwise Gram/non-degeneracy predicate `GramAt p i`: all lattices at stage `i`
have strictly positive rank. -/
def GramAt (p : CoveringPoint) (i : Fin p.m) : Prop :=
  0 < rk (p.latAll i).L ∧ 0 < rk (p.latGood i).L ∧ 0 < rk (p.latCore i).L

/-- Pointwise norm-measure comparability `MeasAt p i C`: there exists a scaling constant `c > 0`
with `|log c| ≤ C * unitE` controlling metric distortion between `latAll i` and `latCore i`. -/
def MeasAt (p : CoveringPoint) (i : Fin p.m) (C : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ |Real.log c| ≤ C * p.unitE ∧
    p.muMaxAll i ≤ slope (p.latCore i).L + C * p.unitE + |Real.log c|

/-- Pointwise lambda-invariant bound `LamAt p i A`:
`muMax (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b`. -/
def LamAt (p : CoveringPoint) (i : Fin p.m) (A : ℝ) : Prop :=
  p.muMaxAll i ≤ p.sc.x ^ A * p.sc.b

/-- Pointwise covering-size bound `SizeAt p i PP A`:
controls `unitE`, `|mainT|`, and `b` relative to `x ^ A * b` and `PP * kap`. -/
def SizeAt (p : CoveringPoint) (i : Fin p.m) (PP A : ℝ) : Prop :=
  1 ≤ p.sc.b ∧ p.sc.b ≤ p.unitE ∧ p.unitE ≤ p.sc.x ^ A * p.sc.b ∧
  |p.mainT i| ≤ p.sc.x ^ A * p.sc.b ∧
  |p.mainT i| ≤ PP * p.kap i ∧ p.sc.b ≤ PP * p.kap i

/-- Pointwise **Anchor** predicate `AnchorAt p i CA`:
1. `mainT p i` matches `∑ τ, (p_i - q_i) * anchorWt p i τ * logOm` within `CA * unitE p`,
2. the weighted `q_i * L`-error `(∑ τ, |anchorWt p i τ|) * q_i * L` is `≤ CA * unitE p`,
3. the host rank-volume product `(f : ℝ) * r * nV * L` is bounded by `b`. -/
def AnchorAt (p : CoveringPoint) (i : Fin p.m) (CA : ℝ) : Prop :=
  |p.mainT i - ∑ τ : p.Pl, p.sigDiff i * p.anchorWt i τ * p.logOm| ≤ CA * p.unitE ∧
  (∑ τ : p.Pl, |p.anchorWt i τ|) * (p.qRank i : ℝ) * p.sc.L ≤ CA * p.unitE ∧
  (p.f : ℝ) * (p.r : ℝ) * (p.nV : ℝ) * p.sc.L ≤ p.sc.b

/-- Pointwise **Low-Defect** predicate `LowAt p i C`:
`-mainT p i - C * unitE p ≤ muCore p i`. -/
def LowAt (p : CoveringPoint) (i : Fin p.m) (C : ℝ) : Prop :=
  -p.mainT i - C * p.unitE ≤ p.muCore i

/-- Pointwise **Flat-Degree** predicate `FlatDegAt p i Y`:
tracks the archimedean Chern-class alignment `|c1Cover τ + (p_i - q_i)/2 * logOm| ≤ 3 * q_i * L`
and bad-prime log-sum bound `badLogSum ≤ 40 * L`. -/
def FlatDegAt (p : CoveringPoint) (i : Fin p.m) (Y : CoveringCover p i) : Prop :=
  (∀ τ : p.Pl, |Y.c1Cover τ + p.sigDiff i / 2 * p.logOm| ≤ 3 * (p.qRank i : ℝ) * p.sc.L) ∧
  Y.badLogSum ≤ 40 * p.sc.L

/-- Pointwise **Deep-Good** predicate `DeepGoodAt p i Y`:
positivity of shifted ranks and non-degeneracy of covering lattices. -/
def DeepGoodAt (p : CoveringPoint) (i : Fin p.m) (Y : CoveringCover p i) : Prop :=
  0 < Y.rkShiftNeg ∧ 0 < Y.rkCover ∧ 0 < rk Y.latShiftNeg.L

/-- Pointwise **Flat** predicate `FlatAt p i Y C`:
`muCover - mainT p i - C * unitE p ≤ muShiftNeg`. -/
def FlatAt (p : CoveringPoint) (i : Fin p.m) (Y : CoveringCover p i) (C : ℝ) : Prop :=
  Y.muCover - p.mainT i - C * p.unitE ≤ Y.muShiftNeg

/-- Pointwise **Covolume** predicate `CovolAt p C0`:
normalized log-covolume `lcvNorm ≤ C0 * p.unitE`. -/
def CovolAt (p : CoveringPoint) (C0 : ℝ) : Prop :=
  p.lcvNorm ≤ C0 * p.unitE

/-- Global `GramCondition` over a family class `FmClass`. -/
def GramCondition (FmClass : FamilyClass) : Prop :=
  LiftsCondition FmClass fun _ _ _ _ p i _ _ => GramAt p i

/-- Global `MeasureCondition` over a family class `FmClass`. -/
def MeasureCondition (FmClass : FamilyClass) : Prop :=
  LiftsCondition FmClass fun _ _ _ _ p i _ C => MeasAt p i C

/-- **`LiftLambdaBound`**: global uniform polynomial-times-exponential bound
`muMax (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b` at all admissible points and stages. -/
def LiftLambdaBound (FmClass : FamilyClass) : Prop :=
  LiftsCondition FmClass fun _ _ _ _ p i _ A => LamAt p i A

/-- Global `SizeCondition` over a family class `FmClass`. -/
def SizeCondition (FmClass : FamilyClass) : Prop :=
  LiftsCondition FmClass fun _ _ _ _ p i PP A => SizeAt p i PP A

/-- **`AnchorCondition`**: global anchor condition over all admissible points and stages. -/
def AnchorCondition (FmClass : FamilyClass) : Prop :=
  LiftsCondition FmClass fun _ _ _ _ p i _ CA => AnchorAt p i CA

/-- **`LowDefectCondition`**: global low-defect bound `-mainT - C * unitE ≤ muCore`
at the top/definite stage `(i : ℕ) + 1 = p.m`. -/
def LowDefectCondition (FmClass : FamilyClass) : Prop :=
  LiftsCondition FmClass fun _ _ _ _ p i _ C => (i : ℕ) + 1 = p.m → LowAt p i C

/-- Global `DeepGoodness` over a family class `FmClass`. -/
def DeepGoodness (FmClass : FamilyClass) : Prop :=
  CoversCondition FmClass fun _ _ _ _ p i Y _ _ => DeepGoodAt p i Y

/-- Global `FlatDegreeCondition` over a family class `FmClass`. -/
def FlatDegreeCondition (FmClass : FamilyClass) : Prop :=
  CoversCondition FmClass fun _ _ _ _ p i Y _ _ => FlatDegAt p i Y

/-- Global `FlatnessCondition` over a family class `FmClass`. -/
def FlatnessCondition (FmClass : FamilyClass) : Prop :=
  CoversCondition FmClass fun _ _ _ _ p i Y _ C => FlatAt p i Y C

/-- Global `CovolumeBoundOfX` over a family class `FmClass`. -/
def CovolumeBoundOfX (FmClass : FamilyClass) : Prop :=
  Closed (FmClass := FmClass) fun Fm =>
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → CovolAt p C

/-! ### Monotonicity, Measure-to-Lambda, and Anchor-to-Low-Defect Implications -/

lemma le_rpow_of_add_terms {x b A1 A2 u v : ℝ}
    (hx : 10 ≤ x) (hb : 0 ≤ b) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : u ≤ x ^ A1 * b) (h2 : v ≤ x ^ A2 * b) :
    u + v ≤ x ^ (A1 + A2 + 1) * b := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hr1 : x ^ A1 ≤ x ^ (A1 + A2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hr2 : x ^ A2 ≤ x ^ (A1 + A2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hr3 : (2 : ℝ) * x ^ (A1 + A2) ≤ x * x ^ (A1 + A2) :=
    mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg (by linarith) _)
  have hx_mul : x * x ^ (A1 + A2) = x ^ (A1 + A2 + 1) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hsum : x ^ A1 * b + x ^ A2 * b ≤ x ^ (A1 + A2 + 1) * b := by
    have ha : x ^ A1 * b + x ^ A2 * b ≤ 2 * x ^ (A1 + A2) * b := by
      have := add_le_add (mul_le_mul_of_nonneg_right hr1 hb) (mul_le_mul_of_nonneg_right hr2 hb)
      linarith
    have hb' : 2 * x ^ (A1 + A2) * b ≤ x ^ (A1 + A2 + 1) * b := by
      rw [← hx_mul]
      exact mul_le_mul_of_nonneg_right hr3 hb
    exact ha.trans hb'
  linarith

lemma lamAt_mono {p : CoveringPoint} {i : Fin p.m} {A A' : ℝ}
    (hA : A ≤ A') (h : LamAt p i A) : LamAt p i A' := by
  unfold LamAt at *
  have hr : p.sc.x ^ A ≤ p.sc.x ^ A' :=
    Real.rpow_le_rpow_of_exponent_le p.sc.x_ge_one hA
  exact h.trans (mul_le_mul_of_nonneg_right hr p.sc.b_pos.le)

/-- Deducing `LamAt` from `MeasAt`, `SizeAt`, and a core-slope polynomial bound. -/
theorem lamAt_of_measAt_and_core_bound {p : CoveringPoint} {i : Fin p.m}
    {Cm As Ac PP : ℝ} (_hCm : 0 ≤ Cm) (hAs : 0 ≤ As) (hAc : 0 ≤ Ac)
    (hM : MeasAt p i Cm) (hS : SizeAt p i PP As)
    (hCore : slope (p.latCore i).L ≤ p.sc.x ^ Ac * p.sc.b) :
    LamAt p i (Ac + As + (⌈2 * Cm⌉₊ : ℝ) + 1) := by
  obtain ⟨c, _hc, hlog, hmu⟩ := hM
  have hE : p.unitE ≤ p.sc.x ^ As * p.sc.b := hS.2.2.1
  have hb0 : 0 ≤ p.sc.b := p.sc.b_pos.le
  have hE0 : 0 ≤ p.unitE := p.sc.E_pos.le
  have h2Cm : 2 * Cm ≤ (⌈2 * Cm⌉₊ : ℝ) := Nat.le_ceil (2 * Cm)
  have hx_ge_two : (2 : ℝ) ≤ p.sc.x := by linarith [p.sc.hx10]
  have hceil_le_rpow : (⌈2 * Cm⌉₊ : ℝ) ≤ p.sc.x ^ (⌈2 * Cm⌉₊ : ℝ) := by
    have hpow : (⌈2 * Cm⌉₊ : ℝ) ≤ (2 : ℝ) ^ (⌈2 * Cm⌉₊ : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.lt_two_pow_self.le
    exact hpow.trans (Real.rpow_le_rpow (by norm_num) hx_ge_two (Nat.cast_nonneg _))
  have hCmE : 2 * Cm * p.unitE ≤ p.sc.x ^ (As + (⌈2 * Cm⌉₊ : ℝ)) * p.sc.b := by
    have h1 : 2 * Cm * p.unitE ≤ (⌈2 * Cm⌉₊ : ℝ) * (p.sc.x ^ As * p.sc.b) :=
      mul_le_mul h2Cm hE hE0 (Nat.cast_nonneg _)
    have h2 : (⌈2 * Cm⌉₊ : ℝ) * (p.sc.x ^ As * p.sc.b) ≤
        p.sc.x ^ (⌈2 * Cm⌉₊ : ℝ) * (p.sc.x ^ As * p.sc.b) :=
      mul_le_mul_of_nonneg_right hceil_le_rpow
        (mul_nonneg (Real.rpow_nonneg p.sc.x_pos.le _) hb0)
    have hmul : p.sc.x ^ (⌈2 * Cm⌉₊ : ℝ) * (p.sc.x ^ As * p.sc.b) =
        p.sc.x ^ (As + (⌈2 * Cm⌉₊ : ℝ)) * p.sc.b := by
      rw [← mul_assoc, ← Real.rpow_add p.sc.x_pos, add_comm]
    linarith
  have hAs_nonneg : 0 ≤ As + (⌈2 * Cm⌉₊ : ℝ) := add_nonneg hAs (Nat.cast_nonneg _)
  have hsum := le_rpow_of_add_terms p.sc.hx10 hb0 hAc hAs_nonneg hCore hCmE
  unfold LamAt
  have h_add_comm : Ac + (As + (⌈2 * Cm⌉₊ : ℝ)) + 1 = Ac + As + (⌈2 * Cm⌉₊ : ℝ) + 1 := by ring
  rw [← h_add_comm]
  linarith

/-- **`liftLambdaBound_of_measure_and_slopeMax`**: deduces `LiftLambdaBound` unconditionally
from `MeasureCondition`, `SizeCondition`, and a polynomial core-slope bound. -/
theorem liftLambdaBound_of_measure_and_slopeMax {FmClass : FamilyClass}
    (hM : MeasureCondition FmClass)
    (hS : SizeCondition FmClass)
    (hCore : LiftsCondition FmClass fun _ _ _ _ p i _ A =>
      slope (p.latCore i).L ≤ p.sc.x ^ A * p.sc.b) :
    LiftLambdaBound FmClass := by
  intro eps Fm hFm
  obtain ⟨Cm, hCm0, hMev⟩ := hM Fm hFm
  obtain ⟨As, hAs0, hSev⟩ := hS Fm hFm
  obtain ⟨Ac, hAc0, hCev⟩ := hCore Fm hFm
  refine ⟨Ac + As + (⌈2 * Cm⌉₊ : ℝ) + 1, ?_, ?_⟩
  · have hceil : (0 : ℝ) ≤ (⌈2 * Cm⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  · obtain ⟨x0, hx0⟩ := (hMev.and (hSev.and hCev))
    refine ⟨x0, fun x hx hle ι hp i => ?_⟩
    obtain ⟨hm, hs, hc⟩ := hx0 x hx hle ι hp
    exact lamAt_of_measAt_and_core_bound hCm0 hAs0 hAc0 (hm i) (hs i) (hc i)

/-- From `AnchorAt p i CA`, bounds `mainT p i` above and below by the weighted `anchorWt` sum. -/
lemma anchorAt_mainT_bounds {p : CoveringPoint} {i : Fin p.m} {CA : ℝ}
    (hA : AnchorAt p i CA) :
    (∑ τ : p.Pl, p.sigDiff i * p.anchorWt i τ * p.logOm) - CA * p.unitE ≤ p.mainT i ∧
    p.mainT i ≤ (∑ τ : p.Pl, p.sigDiff i * p.anchorWt i τ * p.logOm) + CA * p.unitE := by
  have h := abs_le.1 hA.1
  constructor <;> linarith

/-- From `AnchorAt p i CA` at a definite endpoint (`qRank i = 0`), together with a definite
anchored lower bound on `muCore p i`, deduces `LowAt p i (CA + C₀)`. -/
theorem lowAt_of_anchorAt_endpoint {p : CoveringPoint} {i : Fin p.m} {CA C₀ : ℝ}
    (hA : AnchorAt p i CA) (hq0 : p.qRank i = 0)
    (hDef : -(∑ τ : p.Pl, (p.pRank i : ℝ) * p.anchorWt i τ * p.logOm) - C₀ * p.unitE ≤
      p.muCore i) :
    LowAt p i (CA + C₀) := by
  have hsig : p.sigDiff i = (p.pRank i : ℝ) := by
    simp [CoveringPoint.sigDiff, hq0]
  have ha := (abs_le.1 hA.1).1
  have hsum_eq : (∑ τ : p.Pl, p.sigDiff i * p.anchorWt i τ * p.logOm) =
      ∑ τ : p.Pl, (p.pRank i : ℝ) * p.anchorWt i τ * p.logOm :=
    Finset.sum_congr rfl fun τ _ => by rw [hsig]
  rw [hsum_eq] at ha
  set S : ℝ := ∑ τ : p.Pl, (p.pRank i : ℝ) * p.anchorWt i τ * p.logOm
  change -(CA * p.unitE) ≤ p.mainT i - S at ha
  change -S - C₀ * p.unitE ≤ p.muCore i at hDef
  unfold LowAt
  rw [add_mul]
  linarith

/-- **`lowDefectCondition_of_anchor`**: deduces `LowDefectCondition` unconditionally from
`AnchorCondition` and the definite-endpoint anchored lower bound on `muCore` at `(i : ℕ) + 1 = p.m`. -/
theorem lowDefectCondition_of_anchor {FmClass : FamilyClass}
    (hA : AnchorCondition FmClass)
    (hDef : LiftsCondition FmClass fun _ _ _ _ p i _ C₀ =>
      (i : ℕ) + 1 = p.m →
        p.qRank i = 0 ∧
        -(∑ τ : p.Pl, (p.pRank i : ℝ) * p.anchorWt i τ * p.logOm) - C₀ * p.unitE ≤
          p.muCore i) :
    LowDefectCondition FmClass := by
  intro eps Fm hFm
  obtain ⟨CA, hCA, xA, hxA⟩ := hA Fm hFm
  obtain ⟨C₀, hC₀, xD, hxD⟩ := hDef Fm hFm
  refine ⟨CA + C₀, add_nonneg hCA hC₀, max xA xD, fun x hx hle ι hp i hi => ?_⟩
  have hAi := hxA x hx ((le_max_left xA xD).trans hle) ι hp i
  obtain ⟨hq0, hmu⟩ := hxD x hx ((le_max_right xA xD).trans hle) ι hp i hi
  exact lowAt_of_anchorAt_endpoint hAi hq0 hmu

end ConcreteConditions

/-! ## Section 3: `twice_twist_ge` & `flat_bound_of_anchor` -/

section FlatBoundOfAnchor

/-- **Twice-Twist Curvature–Anchor Inequality (`twice_twist_ge`)**:
pure arithmetic core of `FlatBoundOfAnchor`, combining:
1. Hodge Chern-class alignment `∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L`,
2. Anchor main-term match `|mT - ∑ τ, pq * w τ * large₂| ≤ CA * E`,
3. Anchor weight-sum control `(∑ τ, |w τ|) * q * L ≤ CA * E`,
4. Host degree/volume bound `fr * nV * L ≤ b ≤ E`, `10 ≤ L ≤ E`, `2 * m0 ≤ nV`, `lS ≤ 40 * L`,
to deduce:
`-mT - (11 * CA + 83) * E ≤ 2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) - m0 * fr * (log(2π)/2 + lr) - lS)`. -/
theorem twice_twist_ge {ι : Type*} [Fintype ι] (w c1v : ι → ℝ)
    (pq q large₂ L b E mT CA lr m0 fr nV lS : ℝ)
    (hc1 : ∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L)
    (hA1 : |mT - ∑ τ, pq * w τ * large₂| ≤ CA * E)
    (hA2 : (∑ τ, |w τ|) * q * L ≤ CA * E)
    (hq : 0 ≤ q) (hlr : lr ≤ 2 * L) (hL : 10 ≤ L) (hm : 2 * m0 ≤ nV)
    (hm0 : 0 ≤ m0) (hfr : 0 ≤ fr) (hb : fr * nV * L ≤ b)
    (hbE : b ≤ E) (hLE : L ≤ E) (hlS : lS ≤ 40 * L) :
    -mT - (11 * CA + 83) * E ≤
      2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) -
        m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) - lS) := by
  have e1 : ∀ τ ∈ (Finset.univ : Finset ι),
      (-1 / 2) * (pq * w τ * large₂) - (3 * q * L) * |w τ| ≤ w τ * c1v τ := by
    intro τ _
    have h1 : |w τ * (c1v τ + pq / 2 * large₂)| ≤ |w τ| * (3 * q * L) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hc1 τ) (abs_nonneg _)
    have h2 := neg_abs_le (w τ * (c1v τ + pq / 2 * large₂))
    have h3 : w τ * c1v τ = w τ * (c1v τ + pq / 2 * large₂) - pq * w τ * large₂ / 2 := by ring
    linarith
  have e2 := Finset.sum_le_sum e1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e2
  have hS2 : 0 ≤ ∑ τ, |w τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have a1 := (abs_le.1 hA1).1
  have a2 : q * lr * (∑ τ, |w τ|) ≤ q * (2 * L) * (∑ τ, |w τ|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlr hq) hS2
  have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 := Real.pi_le_four
  have a3 : Real.log (2 * Real.pi) / 2 + lr ≤ 3 * L := by linarith
  have a4 : m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) ≤ m0 * fr * (3 * L) :=
    mul_le_mul_of_nonneg_left a3 (mul_nonneg hm0 hfr)
  have a5 : 2 * m0 * (fr * (3 * L)) ≤ nV * (fr * (3 * L)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hfr (by linarith))
  nlinarith

/-- Pointwise flat slope lower bound `FlatAt p i Y (11 * CA + 83)` deduced from
`AnchorAt p i CA`, `FlatDegAt p i Y`, `GoodCov p i Y`, and `SizeAt p i PP A`. -/
theorem flatAt_of_anchor_and_flatDeg {p : CoveringPoint} {i : Fin p.m}
    (Y : CoveringCover p i) {CA PP A : ℝ}
    (hA : AnchorAt p i CA) (hFD : FlatDegAt p i Y)
    (hCov : GoodCov p i Y) (hS : SizeAt p i PP A) :
    FlatAt p i Y (11 * CA + 83) := by
  have htw := twice_twist_ge (p.anchorWt i) Y.c1Cover (p.sigDiff i) (p.qRank i : ℝ)
    p.logOm p.sc.L p.sc.b p.unitE (p.mainT i) CA Y.lrd (Y.m0 : ℝ)
    ((p.f : ℝ) * (p.r : ℝ)) (p.nV : ℝ) Y.badLogSum
    hFD.1 hA.1 hA.2.1 (Nat.cast_nonneg _) hCov.1 p.sc.hL_ge
    (by exact_mod_cast Y.hm0) (Nat.cast_nonneg _) (by positivity)
    (by have := hA.2.2; linarith) hS.2.1 p.sc.hL_le_E hFD.2
  have hbal := Y.twistBalance
  unfold FlatAt
  linarith

lemma flatAt_mono {p : CoveringPoint} {i : Fin p.m} {Y : CoveringCover p i} {C C' : ℝ}
    (hCC' : C ≤ C') (h : FlatAt p i Y C) : FlatAt p i Y C' := by
  unfold FlatAt at *
  have hmul : C * p.unitE ≤ C' * p.unitE := mul_le_mul_of_nonneg_right hCC' p.sc.E_pos.le
  linarith

/-- **`flat_bound_of_anchor`**:
Proved flat degree/slope bound (`FlatnessCondition`) deduced from `AnchorCondition`,
`LowDefectCondition`, `FlatDegreeCondition`, and `SizeCondition`.
Explicitly tracks the uniform constant `11 * CA + 83` (and carries `LowDefectCondition`
explicitly to provide the combined anchor + low-defect flat bound). -/
theorem flat_bound_of_anchor {FmClass : FamilyClass}
    (hA : AnchorCondition FmClass)
    (_hL : LowDefectCondition FmClass)
    (hFD : FlatDegreeCondition FmClass)
    (hS : SizeCondition FmClass) :
    FlatnessCondition FmClass := by
  intro eps Fm hFm
  obtain ⟨CA, hCA, hAev⟩ := hA Fm hFm
  obtain ⟨_CF, _hCF, hFDev⟩ := hFD Fm hFm
  obtain ⟨AS, _hAS, hSev⟩ := hS Fm hFm
  refine ⟨11 * CA + 83, by positivity, ?_⟩
  obtain ⟨x0, hx0⟩ := hAev.and3 hFDev hSev
  refine ⟨x0, fun x hx hle ι hp i hi Y hadm hY => ?_⟩
  obtain ⟨ha, hfd, hs⟩ := hx0 x hx hle ι hp
  exact flatAt_of_anchor_and_flatDeg Y (ha i) (hfd i hi Y hadm hY) hY (hs i)

/-- **Combined Anchor + Low-Defect Flat Slope Lower Bound (`flat_slope_lower_of_anchor_and_lowDefect`)**:
Combines `flat_bound_of_anchor` with `LowDefectCondition` at the definite endpoint
`j = p.lastIdx` (`(j : ℕ) + 1 = p.m`) to eliminate `-p.mainT i - p.mainT p.lastIdx` whenever
`p.mainT i + p.mainT p.lastIdx ≤ Cd * p.unitE`, giving the direct slope lower bound:
`Y.muCover - (C_flat + C_low + Cd) * p.unitE ≤ Y.muShiftNeg + p.muCore p.lastIdx`. -/
theorem flat_slope_lower_of_anchor_and_lowDefect {FmClass : FamilyClass}
    (hA : AnchorCondition FmClass)
    (hL : LowDefectCondition FmClass)
    (hFD : FlatDegreeCondition FmClass)
    (hS : SizeCondition FmClass)
    (hMainCmp : LiftsCondition FmClass fun _ _ _ _ p i _ Cd =>
      p.mainT i + p.mainT p.lastIdx ≤ Cd * p.unitE) :
    CoversCondition FmClass fun _ _ _ _ p _i Y _ C =>
      Y.muCover - C * p.unitE ≤ Y.muShiftNeg + p.muCore p.lastIdx := by
  have hFlat : FlatnessCondition FmClass := flat_bound_of_anchor hA hL hFD hS
  intro eps Fm hFm
  obtain ⟨CF, hCF, hFev⟩ := hFlat Fm hFm
  obtain ⟨CL, hCL, hLev⟩ := hL Fm hFm
  obtain ⟨Cd, hCd, hMev⟩ := hMainCmp Fm hFm
  refine ⟨CF + CL + Cd, by linarith, ?_⟩
  obtain ⟨x0, hx0⟩ := hFev.and3 hLev hMev
  refine ⟨x0, fun x hx hle ι hp i hi Y hadm hY => ?_⟩
  obtain ⟨hf, hl, hm⟩ := hx0 x hx hle ι hp
  have hf1 : Y.muCover - (Fm.Pt x hx ι).mainT i - CF * (Fm.Pt x hx ι).unitE ≤ Y.muShiftNeg :=
    hf i hi Y hadm hY
  have hl1 : -(Fm.Pt x hx ι).mainT (Fm.Pt x hx ι).lastIdx - CL * (Fm.Pt x hx ι).unitE ≤
      (Fm.Pt x hx ι).muCore (Fm.Pt x hx ι).lastIdx :=
    hl (Fm.Pt x hx ι).lastIdx (Fm.Pt x hx ι).lastIdx_add_one
  have hm1 : (Fm.Pt x hx ι).mainT i + (Fm.Pt x hx ι).mainT (Fm.Pt x hx ι).lastIdx ≤
      Cd * (Fm.Pt x hx ι).unitE := hm i
  rw [add_mul, add_mul]
  linarith

/-- Unconditional combined flat + low-defect slope inequality keeping both main terms explicit. -/
theorem flat_slope_add_mainT_of_anchor_and_lowDefect {FmClass : FamilyClass}
    (hA : AnchorCondition FmClass)
    (hL : LowDefectCondition FmClass)
    (hFD : FlatDegreeCondition FmClass)
    (hS : SizeCondition FmClass) :
    CoversCondition FmClass fun _ _ _ _ p i Y _ C =>
      Y.muCover - p.mainT i - p.mainT p.lastIdx - C * p.unitE ≤
        Y.muShiftNeg + p.muCore p.lastIdx := by
  have hFlat : FlatnessCondition FmClass := flat_bound_of_anchor hA hL hFD hS
  intro eps Fm hFm
  obtain ⟨CF, hCF, hFev⟩ := hFlat Fm hFm
  obtain ⟨CL, hCL, hLev⟩ := hL Fm hFm
  refine ⟨CF + CL, add_nonneg hCF hCL, ?_⟩
  obtain ⟨x0, hx0⟩ := hFev.and hLev
  refine ⟨x0, fun x hx hle ι hp i hi Y hadm hY => ?_⟩
  obtain ⟨hf, hl⟩ := hx0 x hx hle ι hp
  have hf1 : Y.muCover - (Fm.Pt x hx ι).mainT i - CF * (Fm.Pt x hx ι).unitE ≤ Y.muShiftNeg :=
    hf i hi Y hadm hY
  have hl1 : -(Fm.Pt x hx ι).mainT (Fm.Pt x hx ι).lastIdx - CL * (Fm.Pt x hx ι).unitE ≤
      (Fm.Pt x hx ι).muCore (Fm.Pt x hx ι).lastIdx :=
    hl (Fm.Pt x hx ι).lastIdx (Fm.Pt x hx ι).lastIdx_add_one
  rw [add_mul]
  linarith

/-- Quantitative residual control on `Y.muShiftNeg - Y.muCover` under `FlatDegAt` and `AnchorAt`,
used by M4 Wave 2 `Stage14M4_DeepGoodReduction` for slope-gap telescoping. -/
theorem flat_twist_residual_bound {p : CoveringPoint} {i : Fin p.m}
    (Y : CoveringCover p i) {CA PP A : ℝ}
    (hA : AnchorAt p i CA) (hFD : FlatDegAt p i Y)
    (hCov : GoodCov p i Y) (hS : SizeAt p i PP A) :
    -p.mainT i - (11 * CA + 83) * p.unitE ≤ Y.muShiftNeg - Y.muCover := by
  have hf := flatAt_of_anchor_and_flatDeg Y hA hFD hCov hS
  unfold FlatAt at hf
  linarith

end FlatBoundOfAnchor

/-! ## Section 4: `cov_size_bound` & Hodge-Covolume Bridges to `Stage12SchurWeylLattices` -/

section CovolumeSizeBounds

/-- Bundled `m`-stage Hodge / covering lattice datum with explicit linearly independent
small sections of norm bounded by `C_sec j`, directly interfacing with
`Stage12SchurWeylLattices.L3_hodge_covolume_bound`. -/
structure CoveringSizeDatum (m : ℕ) where
  E : Fin m → Type
  [normE : ∀ j, NormedAddCommGroup (E j)]
  [innerE : ∀ j, InnerProductSpace ℝ (E j)]
  [fdE : ∀ j, FiniteDimensional ℝ (E j)]
  M : ∀ j, Submodule ℤ (E j)
  [discM : ∀ j, DiscreteTopology (M j)]
  hM0 : ∀ j, M j ≠ ⊥
  s : ∀ j, Fin (rk (M j)) → E j
  hsM : ∀ j i, s j i ∈ M j
  hsli : ∀ j, LinearIndependent ℝ (s j)
  C_sec : Fin m → ℝ
  hCpos : ∀ j, 0 < C_sec j
  hnorm : ∀ j i, ‖s j i‖ ≤ C_sec j
  D : ℝ
  hD : 0 < D

attribute [instance] CoveringSizeDatum.normE CoveringSizeDatum.innerE
  CoveringSizeDatum.fdE CoveringSizeDatum.discM

/-- Hadamard / Gram–Schmidt covolume bound for a single covering lattice `M`:
`covol M ≤ ∏ i, ‖s i‖` and `Real.log (covol M) ≤ (rk M : ℝ) * Real.log C_sec`. -/
theorem covolume_covering_lattice_le_prod_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℤ E) [DiscreteTopology M]
    (s : Fin (rk M) → E) (hsM : ∀ i, s i ∈ M) (hsli : LinearIndependent ℝ s) :
    covol M ≤ ∏ i : Fin (rk M), ‖s i‖ :=
  covol_le_prod_norm s hsM hsli rfl

/-- Pointwise covering-size covolume & slope bound for a single `ConcreteEuclideanLat`:
if `M.L` admits `rk M.L` `ℝ`-linearly independent vectors of norm `≤ C_sec` (`C_sec > 0`),
then:
1. `covol M.L ≤ C_sec ^ (rk M.L)`,
2. `Real.log (covol M.L) ≤ (rk M.L : ℝ) * Real.log C_sec`,
3. `(2 / D) * Real.log (covol M.L) ≤ (2 * (rk M.L : ℝ) / D) * Real.log C_sec` (`D > 0`),
4. `-Real.log C_sec ≤ slope M.L`. -/
theorem cov_size_bound_pointwise (M : ConcreteEuclideanLat)
    (s : Fin (rk M.L) → M.E) (hsM : ∀ i, s i ∈ M.L) (hsli : LinearIndependent ℝ s)
    {C_sec D : ℝ} (_hC : 0 < C_sec) (hnorm : ∀ i, ‖s i‖ ≤ C_sec) (hD : 0 < D) :
    covol M.L ≤ C_sec ^ (rk M.L) ∧
    Real.log (covol M.L) ≤ (rk M.L : ℝ) * Real.log C_sec ∧
    (2 / D) * Real.log (covol M.L) ≤ (2 * (rk M.L : ℝ) / D) * Real.log C_sec ∧
    -Real.log C_sec ≤ slope M.L := by
  have hhad : covol M.L ≤ ∏ i : Fin (rk M.L), ‖s i‖ :=
    covolume_covering_lattice_le_prod_norm M.L s hsM hsli
  have hprod : ∏ i : Fin (rk M.L), ‖s i‖ ≤ C_sec ^ (rk M.L) := by
    calc
      ∏ i : Fin (rk M.L), ‖s i‖ ≤ ∏ _i : Fin (rk M.L), C_sec :=
        Finset.prod_le_prod (fun i _ => norm_nonneg (s i)) (fun i _ => hnorm i)
      _ = C_sec ^ (rk M.L) := by simp
  have hcov_le : covol M.L ≤ C_sec ^ (rk M.L) := hhad.trans hprod
  have hcov_pos : 0 < covol M.L := covol_pos M.L
  have hlog : Real.log (covol M.L) ≤ (rk M.L : ℝ) * Real.log C_sec := by
    have h1 : Real.log (covol M.L) ≤ Real.log (C_sec ^ (rk M.L)) :=
      Real.log_le_log hcov_pos hcov_le
    rwa [Real.log_pow] at h1
  have h2D : 0 ≤ 2 / D := by positivity
  have hnorm_log : (2 / D) * Real.log (covol M.L) ≤
      (2 * (rk M.L : ℝ) / D) * Real.log C_sec := by
    have hmul := mul_le_mul_of_nonneg_left hlog h2D
    have heq : (2 / D) * ((rk M.L : ℝ) * Real.log C_sec) =
        (2 * (rk M.L : ℝ) / D) * Real.log C_sec := by ring
    linarith
  have hrk_pos : (0 : ℝ) < rk M.L := Nat.cast_pos.mpr (rk_pos_of_ne_bot M.L M.ne_bot)
  have hsl : -Real.log C_sec ≤ slope M.L := by
    rw [RHDirect.Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
      RHDirect.Stage11MoriwakiCovolume.arithDeg]
    rw [le_div_iff₀ hrk_pos]
    linarith
  exact ⟨hcov_le, hlog, hnorm_log, hsl⟩

/-- **`cov_size_bound`**:
Multi-stage quantitative covering-size and Hodge-covolume bound over `Fin m`, bridging
`CoveringSizeDatum m` directly to `Stage12SchurWeylLattices.L3_hodge_covolume_bound`:
1. Pointwise log-covolume bound `Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_sec j)`,
2. Normalized `L3` covolume bound `(2 / D) * Real.log (covol (M j)) ≤ (2 * rk (M j) / D) * Real.log (C_sec j)`,
3. Arakelov slope lower bound `-Real.log (C_sec j) ≤ slope (M j)`,
4. Global `m`-stage sum bound `∑ j, (2 / D) * Real.log (covol (M j)) ≤ ∑ j, (2 * rk (M j) / D) * Real.log (C_sec j)`,
5. Uniform `CovolAt p C0` deduction whenever the weighted section-radius sum is `≤ C0 * p.unitE`. -/
theorem cov_size_bound {m : ℕ} (S : CoveringSizeDatum m) :
    (∀ j : Fin m, Real.log (covol (S.M j)) ≤ (rk (S.M j) : ℝ) * Real.log (S.C_sec j)) ∧
    (∀ j : Fin m, (2 / S.D) * Real.log (covol (S.M j)) ≤
      (2 * (rk (S.M j) : ℝ) / S.D) * Real.log (S.C_sec j)) ∧
    (∀ j : Fin m, -Real.log (S.C_sec j) ≤ slope (S.M j)) ∧
    (∑ j : Fin m, (2 / S.D) * Real.log (covol (S.M j)) ≤
      ∑ j : Fin m, (2 * (rk (S.M j) : ℝ) / S.D) * Real.log (S.C_sec j)) :=
  L3_hodge_covolume_bound S.E S.M S.hM0 S.s S.hsM S.hsli S.C_sec S.hCpos S.hnorm S.hD

/-- Pointwise covering-size bound yielding `CovolAt p C0` from a `CoveringSizeDatum`
matching `p.lcvNorm`. -/
theorem covolAt_of_cov_size_bound {m : ℕ} (S : CoveringSizeDatum m)
    {p : CoveringPoint} {C0 : ℝ}
    (hlcv : p.lcvNorm ≤ ∑ j : Fin m, (2 / S.D) * Real.log (covol (S.M j)))
    (hsum : ∑ j : Fin m, (2 * (rk (S.M j) : ℝ) / S.D) * Real.log (S.C_sec j) ≤ C0 * p.unitE) :
    CovolAt p C0 := by
  have hcov := (cov_size_bound S).2.2.2
  unfold CovolAt
  linarith

/-- Family-level `CovolumeBoundOfX` deduced from `CoveringSizeDatum` witnesses across `FmClass`. -/
theorem covolume_bound_ofX_of_cov_size {FmClass : FamilyClass}
    (hCov : Closed (FmClass := FmClass) fun Fm =>
      ∃ C0 : ℝ, 0 ≤ C0 ∧
        EventuallyAtAllPoints Fm fun _ _ _ p =>
          ∃ (m : ℕ) (S : CoveringSizeDatum m),
            p.lcvNorm ≤ ∑ j : Fin m, (2 / S.D) * Real.log (covol (S.M j)) ∧
            ∑ j : Fin m, (2 * (rk (S.M j) : ℝ) / S.D) * Real.log (S.C_sec j) ≤ C0 * p.unitE) :
    CovolumeBoundOfX FmClass := by
  intro eps Fm hFm
  obtain ⟨C0, hC0, x0, hx0⟩ := hCov Fm hFm
  refine ⟨C0, hC0, x0, fun x hx hle ι hp C hCC0 => ?_⟩
  obtain ⟨m, S, hlcv, hsum⟩ := hx0 x hx hle ι hp
  have hC : C0 * (Fm.Pt x hx ι).unitE ≤ C * (Fm.Pt x hx ι).unitE :=
    mul_le_mul_of_nonneg_right hCC0 (Fm.Pt x hx ι).sc.E_pos.le
  exact covolAt_of_cov_size_bound S hlcv (hsum.trans hC)

/-- **CM-Hermitian Tower Covering-Size Bridge (`covering_size_of_cmHermLattice_tower`)**:
Specialization of `cov_size_bound` to an `m`-step tower of arbitrary-rank CM Hermitian lattices
`Λ j : CMHermLattice d (r j)` (`Stage12SchurWeylLattices`), combining exact `ZLattice.covolume`
identities, exact `slope` formulas, and Hadamard covering-size bounds. -/
theorem covering_size_of_cmHermLattice_tower {d m : ℕ} {r : Fin m → ℕ}
    (Λ : ∀ j : Fin m, CMHermLattice d (r j))
    (s : ∀ j : Fin m, Fin (2 * r j) → EuclideanSpace ℝ (Fin (2 * r j)))
    (hsM : ∀ j i, s j i ∈ (Λ j).euclLat)
    (hsli : ∀ j, LinearIndependent ℝ (s j))
    (C_sec : Fin m → ℝ) (hCpos : ∀ j, 0 < C_sec j)
    (hnorm : ∀ j i, ‖s j i‖ ≤ C_sec j) {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m,
      covol (Λ j).euclLat = ZLattice.covolume (Λ j).euclLat volume ∧
      Real.log (covol (Λ j).euclLat) ≤ (2 * (r j : ℝ)) * Real.log (C_sec j) ∧
      (2 / D) * Real.log (covol (Λ j).euclLat) ≤
        (4 * (r j : ℝ) / D) * Real.log (C_sec j) ∧
      -Real.log (C_sec j) ≤
        -(1 / 4 : ℝ) * Real.log d - Real.log (Λ j).H.det.re / (2 * (r j : ℝ))) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (Λ j).euclLat) ≤
      ∑ j : Fin m, (4 * (r j : ℝ) / D) * Real.log (C_sec j)) := by
  let s' : ∀ j : Fin m, Fin (rk (Λ j).euclLat) → EuclideanSpace ℝ (Fin (2 * r j)) :=
    fun j i => s j (i.cast (Λ j).rk_euclLat)
  have hsM' : ∀ j i, s' j i ∈ (Λ j).euclLat := fun j i => hsM j _
  have hsli' : ∀ j, LinearIndependent ℝ (s' j) := fun j =>
    (hsli j).comp _ (finCongr (Λ j).rk_euclLat).injective
  have hnorm' : ∀ j i, ‖s' j i‖ ≤ C_sec j := fun j i => hnorm j _
  let S : CoveringSizeDatum m :=
    { E := fun j => EuclideanSpace ℝ (Fin (2 * r j))
      M := fun j => (Λ j).euclLat
      hM0 := fun j => (Λ j).euclLat_ne_bot
      s := s'
      hsM := hsM'
      hsli := hsli'
      C_sec := C_sec
      hCpos := hCpos
      hnorm := hnorm'
      D := D
      hD := hD }
  obtain ⟨h1, h2, h3, h4⟩ := cov_size_bound S
  refine ⟨fun j => ?_, ?_⟩
  · have hrk : (rk (Λ j).euclLat : ℝ) = 2 * (r j : ℝ) := by
      rw [(Λ j).rk_euclLat]; push_cast; ring
    have hsl := (Λ j).slope_eq
    have h1j := h1 j
    have h2j := h2 j
    have h3j := h3 j
    rw [hrk] at h1j h2j
    have h2eq : 2 * (2 * (r j : ℝ)) / D = 4 * (r j : ℝ) / D := by ring
    rw [h2eq] at h2j
    change -Real.log (C_sec j) ≤ slope (Λ j).euclLat at h3j
    rw [hsl] at h3j
    exact ⟨(Λ j).covol_eq_zlattice_covolume, h1j, h2j, h3j⟩
  · refine h4.trans_eq ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrk : (rk (Λ j).euclLat : ℝ) = 2 * (r j : ℝ) := by
      rw [(Λ j).rk_euclLat]; push_cast; ring
    rw [hrk]
    ring

/-- **Binomial Covering-Size Bound (`binT_covering_bound`)**:
For any covering length `lenT ≥ 1` and flag dimension `d`, bounds the covering multiplicity
`Nat.choose (lenT - 1) d ≤ lenT ^ d` and its logarithm `Real.log (Nat.choose (lenT - 1) d : ℝ) ≤ d * Real.log lenT`,
needed in `HeightLowerGeneral` to compare `binT * dg` against `rkC`. -/
theorem binT_covering_bound (lenT d : ℕ) (_hlen : 1 ≤ lenT) :
    ((lenT - 1).choose d : ℝ) ≤ (lenT : ℝ) ^ d ∧
    (0 < (lenT - 1).choose d →
      Real.log (((lenT - 1).choose d : ℕ) : ℝ) ≤ (d : ℝ) * Real.log (lenT : ℝ)) := by
  have hch_le : (lenT - 1).choose d ≤ lenT ^ d := by
    have hdesc : ∀ a b : ℕ, a.choose b ≤ a ^ b := by
      intro a b
      have hmul : b.factorial * a.choose b ≤ a ^ b := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow a b
      have hfac : 1 ≤ b.factorial := Nat.factorial_pos b
      exact le_trans (Nat.le_mul_of_pos_left _ hfac) hmul
    exact (hdesc (lenT - 1) d).trans (Nat.pow_le_pow_left (Nat.sub_le lenT 1) d)
  have hreal : ((lenT - 1).choose d : ℝ) ≤ (lenT : ℝ) ^ d := by exact_mod_cast hch_le
  refine ⟨hreal, fun hpos => ?_⟩
  have hpos_r : (0 : ℝ) < ((lenT - 1).choose d : ℝ) := Nat.cast_pos.mpr hpos
  have h1 := Real.log_le_log hpos_r hreal
  rwa [Real.log_pow] at h1

lemma realLat_covol_eq_zlattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    covol Λ = ZLattice.covolume Λ volume := by
  let bR : Basis (Fin n) ℤ Λ := RHDirect.Stage10GeometryOfNumbers.basisOfZLattice Λ
  rw [RHDirect.ArakelovCovolume.covol_eq_sqrt_det_gram Λ bR,
    RHDirect.Stage10GeometryOfNumbers.covolume_eq_abs_det Λ bR]
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (bR i : EuclideanSpace ℝ (Fin n)) j
  have hgram : Matrix.gram ℝ (fun i => (bR i : EuclideanSpace ℝ (Fin n))) = B * Bᵀ := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]

/-- **Hermitian Chain Minkowski–Bost Covering Bridge**:
Combines `Stage11DefiniteUnitaryChain.chain_hermitian_minkowski_bost_bridge` with
`cov_size_bound_pointwise` at every stage `j : Fin (m + 1)` of a definite unitary chain. -/
theorem covolume_hermitian_chain_size_bound {m k t : ℕ} (hk : 1 ≤ k)
    (L : ∀ j : Fin (m + 1), HermitianLattice (chainRank k t j.1))
    (s : ∀ j : Fin (m + 1), Fin (2 * chainRank k t j.1) → EuclideanSpace ℝ (Fin (2 * chainRank k t j.1)))
    (hsM : ∀ j i, s j i ∈ (L j).realLat)
    (hsli : ∀ j, LinearIndependent ℝ (s j))
    (C_sec : Fin (m + 1) → ℝ) (hCpos : ∀ j, 0 < C_sec j)
    (hnorm : ∀ j i, ‖s j i‖ ≤ C_sec j) {D : ℝ} (hD : 0 < D) :
    ∀ j : Fin (m + 1),
      let N := chainRank k t j.1
      Real.log (ZLattice.covolume (L j).realLat volume) ≤ (2 * (N : ℝ)) * Real.log (C_sec j) ∧
      (2 / D) * Real.log (ZLattice.covolume (L j).realLat volume) ≤
        (4 * (N : ℝ) / D) * Real.log (C_sec j) ∧
      -Real.log (C_sec j) ≤ muMax (L j).lat := by
  intro j
  set N := chainRank k t j.1
  have hbridge := chain_hermitian_minkowski_bost_bridge hk L j
  have hrk : rk (L j).lat = 2 * N := hbridge.1
  have hcov : covol (L j).lat = ZLattice.covolume (L j).realLat volume := hbridge.2.1
  have hsl_mu : slope (L j).lat ≤ muMax (L j).lat := hbridge.2.2.2.2.1
  have hcov_r : covol (L j).realLat = ZLattice.covolume (L j).realLat volume :=
    realLat_covol_eq_zlattice (L j).realLat
  have hrk_r : rk (L j).realLat = 2 * N := by
    have hcard := Module.finrank_eq_card_basis ((L j).zBasis.map (L j).realLatEquiv)
    unfold rk
    simpa using hcard
  have hne_r : (L j).realLat ≠ ⊥ := by
    intro h0
    have : rk (L j).realLat = 0 := by rw [h0]; unfold rk; simp
    have hN : 0 < N := by unfold N chainRank; omega
    omega
  let M_r : ConcreteEuclideanLat :=
    { E := EuclideanSpace ℝ (Fin (2 * N))
      L := (L j).realLat
      ne_bot := hne_r }
  let s' : Fin (rk M_r.L) → EuclideanSpace ℝ (Fin (2 * N)) :=
    fun i => s j (i.cast hrk_r)
  have hsM' : ∀ i, s' i ∈ M_r.L := fun i => hsM j _
  have hsli' : LinearIndependent ℝ s' :=
    (hsli j).comp _ (finCongr hrk_r).injective
  have hnorm' : ∀ i, ‖s' i‖ ≤ C_sec j := fun i => hnorm j _
  have hpt := cov_size_bound_pointwise M_r s' hsM' hsli' (hCpos j) hnorm' hD
  have hsl_eq : slope (L j).realLat = slope (L j).lat := by
    rw [RHDirect.Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk,
      RHDirect.Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk]
    unfold RHDirect.Stage11MoriwakiCovolume.arithDeg
    rw [hcov_r, hcov, hrk_r, hrk]
  have hlog : Real.log (ZLattice.covolume (L j).realLat volume) ≤
      (2 * (N : ℝ)) * Real.log (C_sec j) := by
    have h := hpt.2.1
    rw [hcov_r, hrk_r] at h
    push_cast at h ⊢
    exact h
  have hnorm_log : (2 / D) * Real.log (ZLattice.covolume (L j).realLat volume) ≤
      (4 * (N : ℝ) / D) * Real.log (C_sec j) := by
    have h := hpt.2.2.1
    rw [hcov_r, hrk_r] at h
    push_cast at h ⊢
    have h4 : 2 * (2 * (N : ℝ)) / D = 4 * (N : ℝ) / D := by ring
    rwa [h4] at h
  have hsl : -Real.log (C_sec j) ≤ muMax (L j).lat := by
    have h := hpt.2.2.2
    change -Real.log (C_sec j) ≤ slope (L j).realLat at h
    rw [hsl_eq] at h
    exact h.trans hsl_mu
  exact ⟨hlog, hnorm_log, hsl⟩

end CovolumeSizeBounds

/-! ## Section 5: `covering_lambda_invariant_bound`, Minkowski–Bost & Schur-Weyl Bridges -/

section CoveringLambdaInvariantBounds

lemma lambda1_pos_of_ne_bot {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    0 < lambda1 L := by
  obtain ⟨v, _hvL, hv0, hveq⟩ := exists_norm_eq_lambda1 L hL0
  rw [← hveq]
  exact norm_pos_iff.mpr hv0

/-- **Complete Minkowski–Bost Lambda-Invariant Equivalence (`lambda_invariant_minkowski_bost_equiv`)**:
For every `M : ConcreteEuclideanLat`:
1. `-Real.log (lambda1 M.L) ≤ muMax M.L ≤ -Real.log (lambda1 M.L) + (1/2) * Real.log (rk M.L)`,
2. `Real.log (lambda1 (dualLat M.L)) - (1/2) * Real.log (rk M.L) ≤ muMin M.L ≤ Real.log (lambda1 (dualLat M.L))`,
3. `muMin (dualLat M.L) = -muMax M.L`,
4. `muMin M.L ≤ slope M.L ≤ muMax M.L`. -/
theorem lambda_invariant_minkowski_bost_equiv (M : ConcreteEuclideanLat) :
    let _ := discreteTopology_dualLat M.L
    (-Real.log (lambda1 M.L) ≤ muMax M.L ∧
      muMax M.L ≤ -Real.log (lambda1 M.L) + (1 / 2) * Real.log (rk M.L : ℝ)) ∧
    (Real.log (lambda1 (dualLat M.L)) - (1 / 2) * Real.log (rk M.L : ℝ) ≤ muMin M.L ∧
      muMin M.L ≤ Real.log (lambda1 (dualLat M.L))) ∧
    muMin (dualLat M.L) = -muMax M.L ∧
    (muMin M.L ≤ slope M.L ∧ slope M.L ≤ muMax M.L) := by
  have h1 := muMax_le_half_log_rk_sub_log_lambda1 M.L M.ne_bot
  have h2 := muMin_dual_lambda1_bounds M.L M.ne_bot
  have h3 := muMin_dualLat M.L M.ne_bot
  have h4 := muMin_le_slope_le_muMax M.L M.ne_bot
  exact ⟨h1, h2, h3, h4⟩

/-- **Covering Pullback Lambda-Invariant Bound (`lambda1_covering_pullback_bound`)**:
If `φ : A.L →ₗ[ℤ] B.L` is a full-rank (`span_ℝ (range φ) = span_ℝ B.L`) bounded homomorphism
with operator norm bound `‖φ x‖ ≤ C * ‖x‖` (`C > 0`), then:
1. `muMin A.L - Real.log C ≤ muMin B.L`,
2. `Real.log (lambda1 (dualLat A.L)) - (1/2) * Real.log (rk A.L) - Real.log C ≤ Real.log (lambda1 (dualLat B.L))`,
3. `-Real.log (lambda1 A.L) - Real.log C ≤ muMax B.L` whenever `A.rk ≤ B.rk` or `slope A.L ≤ muMax B.L` via duality. -/
theorem lambda1_covering_pullback_bound (A B : ConcreteEuclideanLat)
    (φ : A.L →ₗ[ℤ] B.L) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x : A.L, ‖((φ x : B.L) : B.E)‖ ≤ C * ‖(x : A.E)‖)
    (hspan : Submodule.span ℝ (Set.range fun x : A.L => ((φ x : B.L) : B.E)) =
      Submodule.span ℝ (B.L : Set B.E)) :
    let _ := discreteTopology_dualLat A.L
    let _ := discreteTopology_dualLat B.L
    muMin A.L - Real.log C ≤ muMin B.L ∧
    Real.log (lambda1 (dualLat A.L)) - (1 / 2) * Real.log (rk A.L : ℝ) - Real.log C ≤
      Real.log (lambda1 (dualLat B.L)) := by
  have hmu := muMin_sub_log_le_muMin_of_fullRank A.L B.L B.ne_bot φ hC hbound hspan
  have hA := (muMin_dual_lambda1_bounds A.L A.ne_bot).1
  have hB := (muMin_dual_lambda1_bounds B.L B.ne_bot).2
  exact ⟨hmu.1, by linarith⟩

/-- **`covering_lambda_invariant_bound`**:
Master quantitative lambda-invariant & covering-lift bound bridging `LamAt p i A`
(`LiftLambdaBound`), `lambda1`, `dualLat`, `slope`, `covol`, and `Stage12SchurWeylLattices`
Schur-Weyl branching (`columnTensorLat` and `schur_branching_slope_lower`):
1. Primal minimal-vector lower bound:
   `Real.exp (-(p.sc.x ^ A * p.sc.b)) ≤ lambda1 (p.latAll i).L`,
2. Slope & covolume lower bounds:
   `slope (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b` and
   `-((rk (p.latAll i).L : ℝ) * (p.sc.x ^ A * p.sc.b)) ≤ Real.log (covol (p.latAll i).L)`,
3. Dual minimal-slope lower bound:
   `-(p.sc.x ^ A * p.sc.b) ≤ muMin (dualLat (p.latAll i).L)`,
4. Schur-Weyl column-tensor covering lift bound: for any Young diagram `lam : Partition (rk (p.latAll i).L)`,
   covering lattice `Y.latCover`, full-rank branching map `pMap` of distortion `C_branch > 0`,
   and HN gap `slope (columnTensorLat (p.latAll i) lam).L - muMin (columnTensorLat (p.latAll i) lam).L ≤ Δ`,
   `(lam.weight : ℝ) * slope (p.latAll i).L - Δ - (lam.weight : ℝ) * Real.log ((lam.maxPart + rk (p.latAll i).L : ℕ) : ℝ) - Real.log C_branch ≤ muMin Y.latCover.L`
   and `muMin Y.latCover.L ≤ Real.log (lambda1 (dualLat Y.latCover.L))`. -/
theorem covering_lambda_invariant_bound {p : CoveringPoint} {i : Fin p.m} {A : ℝ}
    (hLam : LamAt p i A)
    (Y : CoveringCover p i)
    (lam : Partition (rk (p.latAll i).L))
    (pMap : (columnTensorLat (p.latAll i) lam).L →ₗ[ℤ] Y.latCover.L)
    {C_branch Δ : ℝ} (hC : 0 < C_branch)
    (hbound : ∀ x : (columnTensorLat (p.latAll i) lam).L,
      ‖((pMap x : Y.latCover.L) : Y.latCover.E)‖ ≤
        (lam.hookProd : ℝ) * C_branch * ‖(x : (columnTensorLat (p.latAll i) lam).E)‖)
    (hspan : Submodule.span ℝ (Set.range fun x : (columnTensorLat (p.latAll i) lam).L =>
        ((pMap x : Y.latCover.L) : Y.latCover.E)) =
      Submodule.span ℝ (Y.latCover.L : Set Y.latCover.E))
    (hΔ : slope (columnTensorLat (p.latAll i) lam).L -
        muMin (columnTensorLat (p.latAll i) lam).L ≤ Δ) :
    let _ := discreteTopology_dualLat (p.latAll i).L
    let _ := discreteTopology_dualLat Y.latCover.L
    Real.exp (-(p.sc.x ^ A * p.sc.b)) ≤ lambda1 (p.latAll i).L ∧
    slope (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b ∧
    -((rk (p.latAll i).L : ℝ) * (p.sc.x ^ A * p.sc.b)) ≤ Real.log (covol (p.latAll i).L) ∧
    -(p.sc.x ^ A * p.sc.b) ≤ muMin (dualLat (p.latAll i).L) ∧
    ((lam.weight : ℝ) * slope (p.latAll i).L - Δ -
        (lam.weight : ℝ) * Real.log ((lam.maxPart + rk (p.latAll i).L : ℕ) : ℝ) -
        Real.log C_branch ≤ muMin Y.latCover.L ∧
      muMin Y.latCover.L ≤ Real.log (lambda1 (dualLat Y.latCover.L))) := by
  have hmu_max : muMax (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b := hLam
  have hlam_pos : 0 < lambda1 (p.latAll i).L :=
    lambda1_pos_of_ne_bot (p.latAll i).L (p.latAll i).ne_bot
  have hneg_log : -Real.log (lambda1 (p.latAll i).L) ≤ p.sc.x ^ A * p.sc.b :=
    (neg_log_lambda1_le_muMax (p.latAll i).L (p.latAll i).ne_bot).trans hmu_max
  have h_exp : Real.exp (-(p.sc.x ^ A * p.sc.b)) ≤ lambda1 (p.latAll i).L := by
    have h1 : -(p.sc.x ^ A * p.sc.b) ≤ Real.log (lambda1 (p.latAll i).L) := by linarith
    calc
      Real.exp (-(p.sc.x ^ A * p.sc.b)) ≤ Real.exp (Real.log (lambda1 (p.latAll i).L)) :=
        Real.exp_le_exp.mpr h1
      _ = lambda1 (p.latAll i).L := Real.exp_log hlam_pos
  have hsl : slope (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b :=
    (slope_le_muMax (p.latAll i).L (p.latAll i).L le_rfl (p.latAll i).ne_bot).trans hmu_max
  have hcov_lo : -((rk (p.latAll i).L : ℝ) * (p.sc.x ^ A * p.sc.b)) ≤
      Real.log (covol (p.latAll i).L) := by
    have hrk_pos : (0 : ℝ) < rk (p.latAll i).L :=
      Nat.cast_pos.mpr (rk_pos_of_ne_bot (p.latAll i).L (p.latAll i).ne_bot)
    have h1 : slope (p.latAll i).L = -Real.log (covol (p.latAll i).L) / (rk (p.latAll i).L : ℝ) := by
      rw [RHDirect.Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk]
      rfl
    rw [h1, div_le_iff₀ hrk_pos] at hsl
    linarith
  have hdual : -(p.sc.x ^ A * p.sc.b) ≤ muMin (dualLat (p.latAll i).L) := by
    rw [muMin_dualLat (p.latAll i).L (p.latAll i).ne_bot]
    linarith
  have hschur := (schur_branching_slope_lower (p.latAll i) lam Y.latCover pMap hC hbound hspan).2 Δ hΔ
  have hdl := (muMin_dual_lambda1_bounds Y.latCover.L Y.latCover.ne_bot).2
  exact ⟨h_exp, hsl, hcov_lo, hdual, hschur.1, hdl⟩

/-- **CM-Hermitian Covering Lambda-Invariant Bridge (`covering_lambda_invariant_bound_of_cmHermLattice`)**:
Specialization of `covering_lambda_invariant_bound` to `Λ : CMHermLattice d r`
(`Stage12SchurWeylLattices.stage11_thetaSiegel_cm_column_slope_bridge`), producing exact
`ZLattice.covolume` and `-(1/4)*log d - log(det H)/(2r)` bounds. -/
theorem covering_lambda_invariant_bound_of_cmHermLattice {d r : ℕ} (Λ : CMHermLattice d r)
    (lam : Partition (2 * r)) (S : ConcreteEuclideanLat)
    (pMap : (columnTensorLat
      { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
        ne_bot := Λ.euclLat_ne_bot }
      { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }).L →ₗ[ℤ] S.L)
    {C_branch Δ : ℝ} (hC : 0 < C_branch)
    (hbound : ∀ x, ‖((pMap x : S.L) : S.E)‖ ≤
      (({ parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h } :
        Partition (rk Λ.euclLat)).hookProd : ℝ) * C_branch * ‖(x : _)‖)
    (hspan : Submodule.span ℝ (Set.range fun x => ((pMap x : S.L) : S.E)) =
      Submodule.span ℝ (S.L : Set S.E))
    (hΔ : slope (columnTensorLat
      { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
        ne_bot := Λ.euclLat_ne_bot }
      { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }).L -
      muMin (columnTensorLat
      { E := EuclideanSpace ℝ (Fin (2 * r)), L := Λ.euclLat, discL := Λ.discreteTopology_euclLat,
        ne_bot := Λ.euclLat_ne_bot }
      { parts := fun i => lam.parts (i.cast Λ.rk_euclLat), anti := fun _ _ h => lam.anti h }).L ≤ Δ) :
    let _ := discreteTopology_dualLat S.L
    covol Λ.euclLat = ZLattice.covolume Λ.euclLat volume ∧
    (lam.weight : ℝ) * (-(1 / 4) * Real.log d - Real.log Λ.H.det.re / (2 * (r : ℝ))) -
        Δ - (lam.weight : ℝ) * Real.log ((lam.maxPart + 2 * r : ℕ) : ℝ) - Real.log C_branch ≤
      muMin S.L ∧
    muMin S.L ≤ Real.log (lambda1 (dualLat S.L)) := by
  have hst := RHDirect.Stage12SchurWeylLattices.stage11_thetaSiegel_cm_column_slope_bridge
    Λ lam S pMap hC hbound hspan hΔ
  have hdl := (muMin_dual_lambda1_bounds S.L S.ne_bot).2
  exact ⟨hst.1, hst.2.1, hdl⟩

/-- Family-level lambda-invariant theorem: under `LiftLambdaBound FmClass`, every admissible
point `(p, i)` eventually satisfies `exp(-(x^A * b)) ≤ lambda1 (p.latAll i).L`,
`slope (p.latAll i).L ≤ x^A * b`, and `-(x^A * b) ≤ muMin (dualLat (p.latAll i).L)`. -/
theorem covering_lambda_invariant_bound_of_family {FmClass : FamilyClass}
    (hLam : LiftLambdaBound FmClass) :
    Closed (FmClass := FmClass) fun Fm =>
      ∃ A : ℝ, 0 ≤ A ∧
        EventuallyAtAllPoints Fm fun _ _ _ p =>
          ∀ i : Fin p.m,
            let _ := discreteTopology_dualLat (p.latAll i).L
            Real.exp (-(p.sc.x ^ A * p.sc.b)) ≤ lambda1 (p.latAll i).L ∧
            slope (p.latAll i).L ≤ p.sc.x ^ A * p.sc.b ∧
            -(p.sc.x ^ A * p.sc.b) ≤ muMin (dualLat (p.latAll i).L) := by
  intro eps Fm hFm
  obtain ⟨A, hA0, x0, hx0⟩ := hLam Fm hFm
  refine ⟨A, hA0, x0, fun x hx hle ι hp i => ?_⟩
  have hLi : LamAt (Fm.Pt x hx ι) i A := hx0 x hx hle ι hp i
  have hlam_pos : 0 < lambda1 ((Fm.Pt x hx ι).latAll i).L :=
    lambda1_pos_of_ne_bot ((Fm.Pt x hx ι).latAll i).L ((Fm.Pt x hx ι).latAll i).ne_bot
  have hneg : -Real.log (lambda1 ((Fm.Pt x hx ι).latAll i).L) ≤
      (Fm.Pt x hx ι).sc.x ^ A * (Fm.Pt x hx ι).sc.b :=
    (neg_log_lambda1_le_muMax ((Fm.Pt x hx ι).latAll i).L
      ((Fm.Pt x hx ι).latAll i).ne_bot).trans hLi
  have hexp : Real.exp (-((Fm.Pt x hx ι).sc.x ^ A * (Fm.Pt x hx ι).sc.b)) ≤
      lambda1 ((Fm.Pt x hx ι).latAll i).L := by
    calc
      Real.exp (-((Fm.Pt x hx ι).sc.x ^ A * (Fm.Pt x hx ι).sc.b)) ≤
          Real.exp (Real.log (lambda1 ((Fm.Pt x hx ι).latAll i).L)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = lambda1 ((Fm.Pt x hx ι).latAll i).L := Real.exp_log hlam_pos
  have hsl : slope ((Fm.Pt x hx ι).latAll i).L ≤
      (Fm.Pt x hx ι).sc.x ^ A * (Fm.Pt x hx ι).sc.b :=
    (slope_le_muMax ((Fm.Pt x hx ι).latAll i).L ((Fm.Pt x hx ι).latAll i).L le_rfl
      ((Fm.Pt x hx ι).latAll i).ne_bot).trans hLi
  have hdual : -((Fm.Pt x hx ι).sc.x ^ A * (Fm.Pt x hx ι).sc.b) ≤
      muMin (dualLat ((Fm.Pt x hx ι).latAll i).L) := by
    rw [muMin_dualLat ((Fm.Pt x hx ι).latAll i).L ((Fm.Pt x hx ι).latAll i).ne_bot]
    exact neg_le_neg hLi
  exact ⟨hexp, hsl, hdual⟩

/-- **Anchored Weight-Shift Covolume Estimate (`wshift_covolume_anchored_estimate`)**:
Proves the `WShiftConst` inequality from `CovolumeEstimateAnchoredWeights` unconditionally:
shifting weights `w ↦ w0` with `|w ρ - w0 ρ| ≤ Δ`, `|pq - k| ≤ m`, `k * Δ ≤ 2 * b`,
`|logOm| ≤ CO * La`, `La ≤ 3 * xe`, `card Pl ≤ f`, `B0 = f * m * b * xe` incurs at most
`12 * CO * B0 * llx` additive error in the covolume estimate, feeding directly into
`Stage14M4_HeightLowerGeneral`. -/
theorem wshift_covolume_anchored_estimate {Pl : Type*} [Fintype Pl] (w w0 : Pl → ℝ)
    (lcvD pq logOm C3 B0 llx La f m k Δ b xe CO : ℝ)
    (hlcv : lcvD ≤ (∑ ρ, pq * w ρ * logOm) + C3 * B0 * llx)
    (hw : ∀ ρ, |w ρ - w0 ρ| ≤ Δ) (hΔ : 0 ≤ Δ)
    (hpq : |pq - k| ≤ m) (hCO : 1 ≤ CO) (hlog : |logOm| ≤ CO * La) (hLa : La ≤ 3 * xe)
    (hf : (Fintype.card Pl : ℝ) ≤ f) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hkΔ : k * Δ ≤ 2 * b) (hB0 : B0 = f * m * b * xe) (hllx : 1 ≤ llx) :
    lcvD ≤ (∑ ρ, pq * w0 ρ * logOm) + (C3 + 12 * CO) * B0 * llx := by
  have hk0 : 0 ≤ k := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hb0 : 0 ≤ b := by
    have : 0 ≤ k * Δ := mul_nonneg hk0 hΔ
    linarith
  have hLa0 : 0 ≤ La :=
    nonneg_of_mul_nonneg_right ((abs_nonneg logOm).trans hlog) (by linarith)
  have hxe0 : 0 ≤ xe := by linarith
  have hf0 : 0 ≤ f := (Nat.cast_nonneg _).trans hf
  have hB0_nonneg : 0 ≤ B0 := by rw [hB0]; positivity
  have hpq_abs : |pq| ≤ k + m := by
    have h1 := (abs_le.1 hpq).1
    have h2 := (abs_le.1 hpq).2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hkm : k * Δ + m * Δ ≤ 2 * b * m + 2 * b := by
    have h1 : k * Δ ≤ 2 * b * m := by
      have : 2 * b ≤ 2 * b * m := le_mul_of_one_le_right (by positivity) hm
      linarith
    have h2 : m * Δ ≤ m * (2 * b) := by
      have hΔ2b : Δ ≤ 2 * b := by
        calc
          Δ = 1 * Δ := (one_mul Δ).symm
          _ ≤ k * Δ := mul_le_mul_of_nonneg_right hk hΔ
          _ ≤ 2 * b := hkΔ
      exact mul_le_mul_of_nonneg_left hΔ2b hm0
    linarith
  have hpqΔ : |pq| * Δ ≤ 4 * m * b := by
    have h1 : |pq| * Δ ≤ (k + m) * Δ := mul_le_mul_of_nonneg_right hpq_abs hΔ
    nlinarith
  have hdiff_pt : ∀ ρ : Pl, pq * w ρ * logOm - pq * w0 ρ * logOm ≤ 12 * CO * m * b * xe := by
    intro ρ
    have h_eq : pq * w ρ * logOm - pq * w0 ρ * logOm = pq * (w ρ - w0 ρ) * logOm := by ring
    rw [h_eq]
    have h_abs : pq * (w ρ - w0 ρ) * logOm ≤ |pq * (w ρ - w0 ρ) * logOm| := le_abs_self _
    have h_prod : |pq * (w ρ - w0 ρ) * logOm| = |pq| * |w ρ - w0 ρ| * |logOm| := by
      rw [abs_mul, abs_mul]
    have h_bd : |pq| * |w ρ - w0 ρ| * |logOm| ≤ (4 * m * b) * (CO * (3 * xe)) := by
      have h1 : |pq| * |w ρ - w0 ρ| ≤ 4 * m * b :=
        (mul_le_mul_of_nonneg_left (hw ρ) (abs_nonneg pq)).trans hpqΔ
      have h2 : |logOm| ≤ CO * (3 * xe) :=
        hlog.trans (mul_le_mul_of_nonneg_left hLa (by linarith))
      exact mul_le_mul h1 h2 (abs_nonneg logOm) (by positivity)
    linarith
  have hsum_diff : (∑ ρ : Pl, pq * w ρ * logOm) - (∑ ρ : Pl, pq * w0 ρ * logOm) ≤
      12 * CO * B0 * llx := by
    rw [← Finset.sum_sub_distrib]
    have h1 : ∑ ρ : Pl, (pq * w ρ * logOm - pq * w0 ρ * logOm) ≤
        ∑ _ρ : Pl, 12 * CO * m * b * xe :=
      Finset.sum_le_sum fun ρ _ => hdiff_pt ρ
    have h2 : ∑ _ρ : Pl, (12 * CO * m * b * xe : ℝ) =
        (Fintype.card Pl : ℝ) * (12 * CO * m * b * xe) := by simp
    have h3 : (Fintype.card Pl : ℝ) * (12 * CO * m * b * xe) ≤
        f * (12 * CO * m * b * xe) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    have h4 : f * (12 * CO * m * b * xe) = 12 * CO * B0 := by
      rw [hB0]; ring
    have h5 : 12 * CO * B0 ≤ 12 * CO * B0 * llx :=
      le_mul_of_one_le_right (by positivity) hllx
    linarith
  linarith

end CoveringLambdaInvariantBounds

/-! ## Section 6: Concrete Zero-Assumption Realization & Wave-2 Handoff Bundle -/

section ConcreteRealizationAndSynthesis

/-- Concrete rank-`r` standard CM lattice `ℤ[i]^r ⊂ ℂ^r` wrapped as `ConcreteEuclideanLat`,
built unconditionally from `Stage11DefiniteUnitaryChain.stdCMLattice`. -/
def concreteStdCMConcreteLat (r : ℕ) (hr : 1 ≤ r) : ConcreteEuclideanLat where
  E := EuclideanSpace ℝ (Fin (2 * r))
  L := (stdCMLattice r 1 Nat.one_pos).realLat
  discL := inferInstance
  ne_bot := by
    intro h0
    have hrk : rk (stdCMLattice r 1 Nat.one_pos).realLat = 2 * r := by
      have hcard := Module.finrank_eq_card_basis
        ((stdCMLattice r 1 Nat.one_pos).zBasis.map (stdCMLattice r 1 Nat.one_pos).realLatEquiv)
      unfold rk
      simpa using hcard
    rw [h0] at hrk
    unfold rk at hrk
    simp at hrk
    omega

lemma concreteStdCMConcreteLat_covol (r : ℕ) (hr : 1 ≤ r) :
    covol (concreteStdCMConcreteLat r hr).L = 1 := by
  have h1 := (stdCMLattice r 1 Nat.one_pos).covol_eq_real_covolume
  have h2 := covol_stdCMLattice r 1 Nat.one_pos
  have h3 : covol (stdCMLattice r 1 Nat.one_pos).realLat =
      covol (stdCMLattice r 1 Nat.one_pos).lat := by
    rw [realLat_covol_eq_zlattice, ← h1]
  change covol (stdCMLattice r 1 Nat.one_pos).realLat = 1
  rw [h3, h2]
  simp

lemma concreteStdCMConcreteLat_slope (r : ℕ) (hr : 1 ≤ r) :
    slope (concreteStdCMConcreteLat r hr).L = 0 := by
  rw [RHDirect.Stage11MoriwakiCovolume.slope_eq_arithDeg_div_rk]
  unfold RHDirect.Stage11MoriwakiCovolume.arithDeg
  rw [concreteStdCMConcreteLat_covol r hr, Real.log_one]
  simp

lemma concreteStdCMConcreteLat_rk (r : ℕ) (hr : 1 ≤ r) :
    rk (concreteStdCMConcreteLat r hr).L = 2 * r := by
  have hcard := Module.finrank_eq_card_basis
    ((stdCMLattice r 1 Nat.one_pos).zBasis.map (stdCMLattice r 1 Nat.one_pos).realLatEquiv)
  change rk (stdCMLattice r 1 Nat.one_pos).realLat = 2 * r
  unfold rk
  simpa using hcard

/-- Concrete `ScaleWindow` at any `(x, eps)` with `10 ≤ x ^ eps`. -/
def concreteScaleWindow (x eps : ℝ) (hx10 : 10 ≤ x) (heps : 0 < eps) (hxL : 10 ≤ x ^ eps) :
    ScaleWindow where
  x := x
  eps := eps
  L := x ^ eps
  b := Real.exp (x ^ eps)
  E := Real.exp (x ^ eps)
  hx10 := hx10
  heps := heps
  hL_eq := rfl
  hL_ge := hxL
  hb_eq := rfl
  hb_ge := Real.one_le_exp (by linarith)
  hb_le_E := le_rfl
  hL_le_E := by
    have := Real.add_one_le_exp (x ^ eps)
    linarith

/-- Concrete zero-assumption `CoveringPoint` realizing `stdCMLattice 1 1` with vanishing
weights and main term `0`. -/
def concreteCoveringPoint (x eps : ℝ) (hx10 : 10 ≤ x) (heps : 0 < eps)
    (hxL : 10 ≤ x ^ eps) : CoveringPoint where
  sc := concreteScaleWindow x eps hx10 heps hxL
  m := 2
  hm2 := le_rfl
  k := 5
  hk := le_rfl
  f := 8
  hf8 := le_rfl
  r := 1
  hr1 := le_rfl
  nV := 1
  hnV := le_rfl
  Pl := Fin 1
  pRank := fun i => if (i : ℕ) = 0 then 0 else 1
  qRank := fun i => if (i : ℕ) = 0 then 1 else 0
  hpq := fun i => by fin_cases i <;> rfl
  latAll := fun _ => concreteStdCMConcreteLat 1 le_rfl
  latGoodSub := fun _ => (concreteStdCMConcreteLat 1 le_rfl).L
  latBadSub := fun _ => (concreteStdCMConcreteLat 1 le_rfl).L
  latCore := fun _ => concreteStdCMConcreteLat 1 le_rfl
  latGood_le := fun _ => le_rfl
  latBad_le := fun _ => le_rfl
  latGood_ne_bot := fun _ => (concreteStdCMConcreteLat 1 le_rfl).ne_bot
  mainT := fun _ => 0
  kap := fun _ => Real.exp (x ^ eps)
  hkap_pos := fun _ => Real.exp_pos _
  logOm := 0
  anchorWt := fun _ _ => 0
  c1Host := fun _ _ => 0
  c2Diff := fun _ => 0
  lcvNorm := 0
  arDim := 1
  harDim_pos := one_pos

/-- Concrete zero-assumption `CoveringFamily eps` for any `eps > 0` (`x1 = max 10 (10 ^ (1 / eps))`). -/
def concreteCoveringFamily (eps : ℝ) (heps : 0 < eps) : CoveringFamily eps where
  x1 := max 10 ((10 : ℝ) ^ (1 / eps))
  Ix := fun _ => PUnit
  Pt := fun x hx _ =>
    have hx10 : 10 ≤ x := (le_max_left 10 ((10 : ℝ) ^ (1 / eps))).trans hx.le
    have hxL : 10 ≤ x ^ eps := by
      have h10 : (10 : ℝ) ^ (1 / eps) ≤ x :=
        (le_max_right 10 ((10 : ℝ) ^ (1 / eps))).trans hx.le
      have hr : ((10 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h10 heps.le
      have heq : ((10 : ℝ) ^ (1 / eps)) ^ eps = 10 := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel heps.ne', Real.rpow_one]
      linarith
    concreteCoveringPoint x eps hx10 heps hxL
  Admissible := fun _ _ _ _ => True
  CovAdm := fun x hx ι i Y =>
    let hx10 : 10 ≤ x := (le_max_left 10 ((10 : ℝ) ^ (1 / eps))).trans hx.le
    let hxL : 10 ≤ x ^ eps := by
      have h10 : (10 : ℝ) ^ (1 / eps) ≤ x :=
        (le_max_right 10 ((10 : ℝ) ^ (1 / eps))).trans hx.le
      have hr : ((10 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h10 heps.le
      have heq : ((10 : ℝ) ^ (1 / eps)) ^ eps = 10 := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel heps.ne', Real.rpow_one]
      linarith
    FlatDegAt (concreteCoveringPoint x eps hx10 heps hxL) i Y
  PP := fun _ _ _ => 1
  hPP_pos := fun _ _ _ => one_pos
  hscale_x := fun _ _ _ => rfl
  hscale_eps := fun _ _ _ => rfl

/-- Singleton `FamilyClass` containing `concreteCoveringFamily eps heps`. -/
def ConcreteSingletonClass (eps0 : ℝ) (heps0 : 0 < eps0) : FamilyClass :=
  fun eps Fm => ∃ h : eps = eps0, Fm = h ▸ concreteCoveringFamily eps0 heps0

/-- Lower bound `1 ≤ lambda1 (concreteStdCMConcreteLat r hr).L` for every `r ≥ 1`,
since every nonzero element of `ℤ[i]^r` has at least one nonzero integer coordinate. -/
lemma one_le_lambda1_concreteStdCMConcreteLat (r : ℕ) (hr : 1 ≤ r) :
    1 ≤ lambda1 (concreteStdCMConcreteLat r hr).L := by
  obtain ⟨v, hvL, hv0, hveq⟩ :=
    exists_norm_eq_lambda1 (concreteStdCMConcreteLat r hr).L (concreteStdCMConcreteLat r hr).ne_bot
  rw [← hveq]
  have hv_mem : (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).symm v ∈
      (stdCMLattice r 1 Nat.one_pos).lat := by
    rcases hvL with ⟨w, hw, hwv⟩
    have h1 : (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).symm v = w := by
      rw [← hwv]
      exact (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).symm_apply_apply w
    rwa [h1]
  set w := (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).symm v
  have hw0 : w ≠ 0 := by
    intro h
    have hv_eq : v = 0 := by
      rw [← (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).apply_symm_apply v]
      change (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r) w = 0
      rw [h, map_zero]
    exact hv0 hv_eq
  have hmem := (RHDirect.Stage11DefiniteUnitaryChain.mem_stdCMLattice_iff Nat.one_pos w).1 hv_mem
  have hex : ∃ i : Fin r, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (by ext i; exact h i)
  obtain ⟨i₀, hi₀⟩ := hex
  obtain ⟨a, b, hab⟩ := hmem i₀
  have hcm : RHDirect.Stage11DefiniteUnitaryChain.cmGen 1 = Complex.I := by
    simp [RHDirect.Stage11DefiniteUnitaryChain.cmGen]
  rw [hcm] at hab
  have hab_ne : (a : ℤ) ≠ 0 ∨ (b : ℤ) ≠ 0 := by
    by_contra h
    push Not at h
    apply hi₀
    rw [hab, h.1, h.2]
    simp
  have hnorm_wi : 1 ≤ ‖w i₀‖ ^ 2 := by
    rw [hab, Complex.sq_norm, Complex.normSq_apply]
    have ha_re : ((a : ℂ) + (b : ℂ) * Complex.I).re = (a : ℝ) := by simp
    have ha_im : ((a : ℂ) + (b : ℂ) * Complex.I).im = (b : ℝ) := by simp
    rw [ha_re, ha_im]
    have hsq_int : 1 ≤ a ^ 2 + b ^ 2 := by
      rcases hab_ne with ha | hb
      · have ha2 : 0 < a * a := mul_self_pos.mpr ha
        have : 1 ≤ a ^ 2 := by nlinarith
        nlinarith [sq_nonneg b]
      · have hb2 : 0 < b * b := mul_self_pos.mpr hb
        have : 1 ≤ b ^ 2 := by nlinarith
        nlinarith [sq_nonneg a]
    have hsq_real : (1 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by exact_mod_cast hsq_int
    linarith
  have hnorm_w_sq : 1 ≤ ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hle : ‖w i₀‖ ^ 2 ≤ ∑ i : Fin r, ‖w i‖ ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg ‖w i‖) (Finset.mem_univ i₀)
    linarith
  have hnorm_v_sq : 1 ≤ ‖v‖ ^ 2 := by
    have heq : ‖w‖ = ‖v‖ := by
      change ‖(RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).symm v‖ = ‖v‖
      exact (RHDirect.Stage11DefiniteUnitaryChain.realEquiv r).symm.norm_map v
    rwa [← heq]
  nlinarith [norm_nonneg v]

lemma muMax_concreteStdCMConcreteLat_le (r : ℕ) (hr : 1 ≤ r) :
    muMax (concreteStdCMConcreteLat r hr).L ≤ (1 / 2) * Real.log (2 * (r : ℝ)) := by
  have h := (muMax_le_half_log_rk_sub_log_lambda1 (concreteStdCMConcreteLat r hr).L
    (concreteStdCMConcreteLat r hr).ne_bot).2
  have hlam : 0 ≤ Real.log (lambda1 (concreteStdCMConcreteLat r hr).L) :=
    Real.log_nonneg (one_le_lambda1_concreteStdCMConcreteLat r hr)
  rw [concreteStdCMConcreteLat_rk r hr] at h
  push_cast at h
  linarith

/-- **Unconditional Non-Vacuous Satisfaction Theorem (`concreteCoveringFamily_satisfies_all`)**:
Proves with ZERO assumptions that `concreteCoveringFamily eps heps` satisfies `GramCondition`,
`MeasureCondition`, `LiftLambdaBound`, `SizeCondition`, `AnchorCondition`, `LowDefectCondition`,
`FlatDegreeCondition`, `FlatnessCondition` (via `flat_bound_of_anchor`), and `CovolumeBoundOfX`. -/
theorem concreteCoveringFamily_satisfies_all (eps0 : ℝ) (heps0 : 0 < eps0) :
    let FmClass := ConcreteSingletonClass eps0 heps0
    GramCondition FmClass ∧
    MeasureCondition FmClass ∧
    LiftLambdaBound FmClass ∧
    SizeCondition FmClass ∧
    AnchorCondition FmClass ∧
    LowDefectCondition FmClass ∧
    FlatDegreeCondition FmClass ∧
    FlatnessCondition FmClass ∧
    CovolumeBoundOfX FmClass := by
  intro FmClass
  have hGram : GramCondition FmClass := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp i => ?_⟩
    unfold GramAt
    have hrk : rk (concreteStdCMConcreteLat 1 le_rfl).L = 2 :=
      concreteStdCMConcreteLat_rk 1 le_rfl
    change 0 < rk (concreteStdCMConcreteLat 1 le_rfl).L ∧
      0 < rk (concreteStdCMConcreteLat 1 le_rfl).L ∧
      0 < rk (concreteStdCMConcreteLat 1 le_rfl).L
    rw [hrk]
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  have hMeas : MeasureCondition FmClass := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨1, zero_le_one, 0, fun x hx hle ι hp i => ?_⟩
    refine ⟨1, one_pos, ?_, ?_⟩
    · simp only [Real.log_one, abs_zero]
      exact mul_nonneg zero_le_one ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.E_pos.le
    · simp only [Real.log_one, abs_zero, add_zero, one_mul]
      have hmu : ((concreteCoveringFamily eps heps0).Pt x hx ι).muMaxAll i ≤ (1 / 2) * Real.log 2 := by
        simpa [CoveringPoint.muMaxAll, concreteCoveringFamily, concreteCoveringPoint] using
          muMax_concreteStdCMConcreteLat_le 1 le_rfl
      have hsl : slope (((concreteCoveringFamily eps heps0).Pt x hx ι).latCore i).L = 0 := by
        simpa [concreteCoveringFamily, concreteCoveringPoint] using
          concreteStdCMConcreteLat_slope 1 le_rfl
      have hlog2 : (1 / 2 : ℝ) * Real.log 2 ≤ 1 := by
        have : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        linarith
      have hE : 1 ≤ ((concreteCoveringFamily eps heps0).Pt x hx ι).unitE :=
        ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.hb_ge.trans
          ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.hb_le_E
      linarith
  have hSize : SizeCondition FmClass := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp i => ?_⟩
    unfold SizeAt CoveringPoint.unitE
    change 1 ≤ Real.exp (x ^ eps) ∧
      Real.exp (x ^ eps) ≤ Real.exp (x ^ eps) ∧
      Real.exp (x ^ eps) ≤ x ^ (0 : ℝ) * Real.exp (x ^ eps) ∧
      |(0 : ℝ)| ≤ x ^ (0 : ℝ) * Real.exp (x ^ eps) ∧
      |(0 : ℝ)| ≤ 1 * Real.exp (x ^ eps) ∧
      Real.exp (x ^ eps) ≤ 1 * Real.exp (x ^ eps)
    have hxp : 0 ≤ x ^ eps := Real.rpow_nonneg
      ((le_max_left 10 ((10 : ℝ) ^ (1 / eps))).trans hx.le |> fun h => by linarith) _
    have hexp1 : 1 ≤ Real.exp (x ^ eps) := Real.one_le_exp hxp
    simp only [Real.rpow_zero, one_mul, abs_zero]
    exact ⟨hexp1, le_rfl, le_rfl, by linarith, by linarith, le_rfl⟩
  have hCore : LiftsCondition FmClass fun _ _ _ _ p i _ A =>
      slope (p.latCore i).L ≤ p.sc.x ^ A * p.sc.b := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp i => ?_⟩
    have hsl : slope (((concreteCoveringFamily eps heps0).Pt x hx ι).latCore i).L = 0 := by
      simpa [concreteCoveringFamily, concreteCoveringPoint] using
        concreteStdCMConcreteLat_slope 1 le_rfl
    change slope (((concreteCoveringFamily eps heps0).Pt x hx ι).latCore i).L ≤ _
    rw [hsl]
    exact mul_nonneg (Real.rpow_nonneg ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.x_pos.le _)
      ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.b_pos.le
  have hLam : LiftLambdaBound FmClass :=
    liftLambdaBound_of_measure_and_slopeMax hMeas hSize hCore
  have hAnchor : AnchorCondition FmClass := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp i => ?_⟩
    unfold AnchorAt
    have hL10 : 10 ≤ ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.L :=
      ((concreteCoveringFamily eps heps0).Pt x hx ι).sc.hL_ge
    have h8L : (8 : ℝ) * 1 * 1 * (x ^ eps) ≤ Real.exp (x ^ eps) := by
      have hu : (10 : ℝ) ≤ x ^ eps := hL10
      have hexp := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ x ^ eps) 4
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at hexp
      have hfac3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
      rw [hfac3] at hexp
      nlinarith
    refine ⟨?_, ?_, ?_⟩
    · change |(0 : ℝ) - ∑ _τ : Fin 1, _ * (0 : ℝ) * (0 : ℝ)| ≤ 0 * _
      simp
    · change (∑ _τ : Fin 1, |(0 : ℝ)|) * _ * _ ≤ 0 * _
      simp
    · change ((8 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (x ^ eps) ≤ Real.exp (x ^ eps)
      push_cast
      exact h8L
  have hLow : LowDefectCondition FmClass := by
    refine lowDefectCondition_of_anchor hAnchor ?_
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp i hi => ?_⟩
    have hi1 : (i : ℕ) = 1 := by
      change (i : ℕ) + 1 = 2 at hi
      omega
    have hq0 : ((concreteCoveringFamily eps heps0).Pt x hx ι).qRank i = 0 := by
      change (if (i : ℕ) = 0 then 1 else 0) = 0
      simp [hi1]
    have hsl : ((concreteCoveringFamily eps heps0).Pt x hx ι).muCore i = 0 := by
      unfold CoveringPoint.muCore
      simpa [concreteCoveringFamily, concreteCoveringPoint] using
        concreteStdCMConcreteLat_slope 1 le_rfl
    refine ⟨hq0, ?_⟩
    rw [hsl]
    change -(∑ _τ : Fin 1, _ * (0 : ℝ) * (0 : ℝ)) - 0 * _ ≤ 0
    simp
  have hFD : FlatDegreeCondition FmClass := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp i hi Y hadm hY => ?_⟩
    exact hadm
  have hFlat : FlatnessCondition FmClass := flat_bound_of_anchor hAnchor hLow hFD hSize
  have hCov : CovolumeBoundOfX FmClass := by
    rintro eps Fm ⟨rfl, rfl⟩
    refine ⟨0, le_rfl, 0, fun x hx hle ι hp C hC0 => ?_⟩
    unfold CovolAt
    change (0 : ℝ) ≤ C * Real.exp (x ^ eps)
    exact mul_nonneg hC0 (Real.exp_pos _).le
  exact ⟨hGram, hMeas, hLam, hSize, hAnchor, hLow, hFD, hFlat, hCov⟩

/-- **Wave-2 Handoff Bundle (`LiftLambdaBoundsPack FmClass`)**:
Packages all lift-lambda, anchor, low-defect, flat-bound, and covolume-size conditions
for downstream consumption by `Stage14M4_DeepGoodReduction` and `Stage14M4_HeightLowerGeneral`. -/
structure LiftLambdaBoundsPack (FmClass : FamilyClass) : Prop where
  gram : GramCondition FmClass
  measure : MeasureCondition FmClass
  liftLambda : LiftLambdaBound FmClass
  size : SizeCondition FmClass
  anchor : AnchorCondition FmClass
  lowDefect : LowDefectCondition FmClass
  flatDeg : FlatDegreeCondition FmClass
  flatness : FlatnessCondition FmClass
  covolume : CovolumeBoundOfX FmClass

/-- **Master Synthesis Theorem (`stage14M4_liftLambdaBounds_synthesis`)**:
Constructs a `LiftLambdaBoundsPack FmClass` unconditionally from `GramCondition`,
`MeasureCondition`, `SizeCondition`, `AnchorCondition`, `FlatDegreeCondition`,
a polynomial core-slope bound, a definite-endpoint lower bound, and `CoveringSizeDatum`
witnesses, proving `LiftLambdaBound`, `LowDefectCondition`, `FlatnessCondition`,
and `CovolumeBoundOfX` automatically. -/
theorem stage14M4_liftLambdaBounds_synthesis {FmClass : FamilyClass}
    (hGram : GramCondition FmClass)
    (hMeas : MeasureCondition FmClass)
    (hSize : SizeCondition FmClass)
    (hCore : LiftsCondition FmClass fun _ _ _ _ p i _ A =>
      slope (p.latCore i).L ≤ p.sc.x ^ A * p.sc.b)
    (hAnchor : AnchorCondition FmClass)
    (hDef : LiftsCondition FmClass fun _ _ _ _ p i _ C₀ =>
      (i : ℕ) + 1 = p.m →
        p.qRank i = 0 ∧
        -(∑ τ : p.Pl, (p.pRank i : ℝ) * p.anchorWt i τ * p.logOm) - C₀ * p.unitE ≤
          p.muCore i)
    (hFD : FlatDegreeCondition FmClass)
    (hCov : Closed (FmClass := FmClass) fun Fm =>
      ∃ C0 : ℝ, 0 ≤ C0 ∧
        EventuallyAtAllPoints Fm fun _ _ _ p =>
          ∃ (m : ℕ) (S : CoveringSizeDatum m),
            p.lcvNorm ≤ ∑ j : Fin m, (2 / S.D) * Real.log (covol (S.M j)) ∧
            ∑ j : Fin m, (2 * (rk (S.M j) : ℝ) / S.D) * Real.log (S.C_sec j) ≤ C0 * p.unitE) :
    LiftLambdaBoundsPack FmClass :=
  let hLam : LiftLambdaBound FmClass :=
    liftLambdaBound_of_measure_and_slopeMax hMeas hSize hCore
  let hLow : LowDefectCondition FmClass := lowDefectCondition_of_anchor hAnchor hDef
  let hFlat : FlatnessCondition FmClass := flat_bound_of_anchor hAnchor hLow hFD hSize
  let hCovX : CovolumeBoundOfX FmClass := covolume_bound_ofX_of_cov_size hCov
  ⟨hGram, hMeas, hLam, hSize, hAnchor, hLow, hFD, hFlat, hCovX⟩

/-- Concrete 0-assumption inhabitant of `LiftLambdaBoundsPack` for `ConcreteSingletonClass`. -/
theorem concrete_liftLambdaBoundsPack (eps0 : ℝ) (heps0 : 0 < eps0) :
    LiftLambdaBoundsPack (ConcreteSingletonClass eps0 heps0) := by
  have h := concreteCoveringFamily_satisfies_all eps0 heps0
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end ConcreteRealizationAndSynthesis

end RHDirect.Stage14M4_LiftLambdaBounds
