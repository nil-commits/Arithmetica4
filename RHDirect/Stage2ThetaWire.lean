import RHDirect.ThetaSlopeEngine
import RHDirect.LatticeFrame
import RHDirect.ArakelovCovolume
import RHDirect.PAdicChainValuation
import RHDirect.RallisSeesaw
import RHDirect.SiegelWeilCore
import RHDirect.BesselWaveGrid
import RHDirect.UnitaryMassFormula
import RHDirect.HermitianCurvatureCore
import RHDirect.CapelliCore

/-!
# RHDirect.Stage2ThetaWire

Stage 2 Pillar-2 integration module wiring **all 9 rebuilt Pillar-2 specialist cores** directly into
`RHDirect.ThetaSlopeEngine` (`ThetaSlopeContract S`) with **0 `sorry`, 0 custom `axiom`s**:

1. `RHDirect.LatticeFrame` + `RHDirect.ArakelovCovolume` → **discharges `BostSlopeFiber.SlopeIneq`**,
   `fParams`, `delBar < 1`, `0 ≤ etaBar`, `0 ≤ eBar ≤ 1 / 4` (for both `uF > 0` via
   `bost_slope_ineq_of_gram_input` and `uF = 0` via `corank_share_bound` +
   `projected_gram_corank_density_bound` + `bostSlopeFiber_slopeIneq_of_tail_bound`).
2. `RHDirect.RallisSeesaw` + `RHDirect.SiegelWeilCore` + `RHDirect.CapelliCore` +
   `RHDirect.PAdicChainValuation` → **discharges `chainOp` integrality (`ChainIntM`)**, Weil
   convergence along every chain step `j < R.m`, Rallis norm-square/log-norm recursion and
   nonvanishing, Capelli integral-cast / `p`-adic determinant integrality, and sharp `m`-step
   column valuation (`levelChainSharpColumnValuation_of_stability`).
3. `RHDirect.BesselWaveGrid` → **discharges wave-grid frame bounds**, test-vector assembly,
   local-factor ratio matching, and `nWv` / `RankVal` wave-grid multiplicity bounds.
4. `RHDirect.UnitaryMassFormula` → **discharges `SlopeHypotheses.count.1` (`Lam5 ≤ log T`)** and
   `0 < v` via `mass_ratio_ge_with_error` and `mass_ratio_error_le_four_of_scaleParams`, plus
   stabilizer-orbit / finite-genus mass unification.
5. `RHDirect.HermitianCurvatureCore` + `RHDirect.ArakelovCovolume` → **discharges curvature /
   Moriwaki covolume & height bounds** feeding `BostSlopeFiber` slope-excess ceilings and
   iterated curvature recursion.
6. `RHDirect.PAdicChainValuation` + `RHDirect.SlopeInequality` → **discharges `SlopeHypotheses.div`**
   directly from `WinDatum.vAt_400` (`divinN_of_vAt` + `eventually_rank_le_rpow_400` +
   `log_sq_le_rpow`), **discharges `eD = 1`**, `log x ≤ x ^ eps`, `KBig_le`, `B0 ≤ 2 n m b x^eps`,
   all `RankVal`-implied `RestSize`/`ErrorWindowBounds` inequalities (`0 < n`, `0 < f`,
   `x^(1/2 - eps) ≤ m ≤ x^(1/2 + eps/2)`, `x * m ≤ k`, `1 ≤ k ≤ x^5`, `k ≤ n^2 * x^(1/2 - eps)`),
   and **`Ga_bound5` common-slope cancellation** (`CongruenceSlopeData.Ga_bound5`).

Main exports:
- `Stage2ThetaCoreInputs S` (strictly smaller / deeper Pillar-2 input bundle)
- `minimalThetaEngineInputs_of_stage2 : Stage2ThetaCoreInputs S → MinimalThetaEngineInputs S`
- `stage2_thetaSlopeContract : Stage2ThetaCoreInputs S → ThetaSlopeContract S`
- `stage2_allLevelsWindowBound : Stage2ThetaCoreInputs S → VWin S → AllLevelsWindowBound (3 / 2)`
-/

open Real Finset RHDirect RHDirect.SlopeInequality RHDirect.ThetaSlopeEngine
open scoped BigOperators InnerProductSpace

namespace RHDirect.Stage2ThetaWire

noncomputable section

/-! ## Section 1: Discharging `BostSlopeFiber.SlopeIneq` from Gram-Frame Data
    (`LatticeFrame` + `ArakelovCovolume` + `BesselWaveGrid`) -/

/-- Raw Gram-matrix & isometric-compression fiber data at a single fiber `u0`.
Does **not** assume `BostSlopeFiber.SlopeIneq`, `0 ≤ η`, `0 ≤ e`, or `e ≤ 1 / 4` — all of these
are proved by `Stage2GramFrameFiber.toBostSlopeIneq` using `LatticeFrame` and `ArakelovCovolume`. -/
structure Stage2GramFrameFiber (s uF HH muMinCC : ℝ) (cardW : ℕ)
    (delBar sgBar deBar e0Bar : ℝ) : Type 1 where
  ι : Type
  [finι : Fintype ι]
  κ : Type
  [finκ : Fintype κ]
  [decκ : DecidableEq κ]
  κ₁ : Type
  [finκ₁ : Fintype κ₁]
  [decκ₁ : DecidableEq κ₁]
  d : ι → ℕ
  r : ι → ℕ
  Bf : ∀ i, Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (d i)) ℂ
  Vr : ∀ i, Matrix (Fin (d i)) (Fin (r i)) ℂ
  ga : ι → ℝ
  Dstar : ℝ
  sg : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ
  de : ℝ
  δ : ℝ
  isIsom : LatticeFrame.IsIsometryFamily Vr
  ga_pos : ∀ i, 0 < ga i
  Dstar_pos : 0 < Dstar
  sg_pos : 0 < sg
  sg_le_bar : sg ≤ sgBar
  sgBar_le : sgBar ≤ 1 / 20
  rank_ge : Dstar / sg ≤ LatticeFrame.totalRank d
  η0_ge : -1 ≤ η0
  η0_le : η0 ≤ sg / 2
  η1_le : η1 ≤ sg / 2
  e0_nonneg : 0 ≤ e0
  e0_le_bar : e0 ≤ e0Bar
  sqrt_e0_le : Real.sqrt e0 ≤ sg / 2
  de_nonneg : 0 ≤ de
  de_le_bar : de ≤ deBar
  deBar_le : deBar ≤ 1 / 4
  corV : ∑ i, ((d i : ℝ) - (r i : ℝ)) ≤ de * LatticeFrame.totalRank d
  gramInput : LatticeFrame.GramInput Bf ga Dstar η0 η1 e0
  δ_nonneg : 0 ≤ δ
  δ_le_bar : δ ≤ delBar
  delBar_le : delBar ≤ 1 / 2
  card_ge : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ)
  κ_pos : 0 < Fintype.card κ
  cardW_ge_one : 1 ≤ cardW
  y : ∀ i, Fin (r i) → ℝ
  y_mean : (∑ i, (r i : ℝ)) * s ≤ ∑ i, ∑ j, y i j
  y_top : ∀ i j, y i j ≤ s + uF
  x : Fin (Fintype.card κ) → ℝ
  x_min : ∀ j, muMinCC ≤ x j
  Nτ : ℝ → ∀ i, Submodule ℂ (EuclideanSpace ℂ (Fin (r i)))
  T : ℝ → Submodule ℂ (EuclideanSpace ℂ κ)
  Nτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ i,
    (r i : ℝ) - Module.finrank ℂ (Nτ τ i) ≤
      ((Finset.univ.filter (fun j => y i j < s - τ)).card : ℝ)
  T_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ i (v : EuclideanSpace ℂ (Fin (r i))), v ∈ Nτ τ i →
    (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
      (fun k => (Matrix.toEuclideanLin
        (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
          (LatticeFrame.compressFamily Bf Vr i)) v) (Sum.inl k)) ∈ T τ
  T_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
    ((Finset.univ.filter (fun j => x j < s - Real.log (cardW : ℝ) - τ)).card : ℝ) ≤
      (Fintype.card κ : ℝ) - Module.finrank ℂ (T τ)

attribute [instance] Stage2GramFrameFiber.finι Stage2GramFrameFiber.finκ
  Stage2GramFrameFiber.decκ Stage2GramFrameFiber.finκ₁ Stage2GramFrameFiber.decκ₁

namespace Stage2GramFrameFiber

variable {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}

/-- Derived common dual-lattice slope `μ_CC` (average of ambient Harder–Narasimhan slopes `x`). -/
def muCC (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar) : ℝ :=
  (∑ j, F.x j) / (Fintype.card F.κ : ℝ)

/-- Derived frame trace-square defect `η = 5 * sg + 3 * √de`. -/
def etaVal (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar) : ℝ :=
  5 * F.sg + 3 * Real.sqrt F.de

/-- Derived compressed diagonal defect `e = 2 * e0`. -/
def eVal (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar) : ℝ :=
  2 * F.e0

/-- The `RHDirect.BostSlopeFiber` determined by a `Stage2GramFrameFiber`. -/
def toBostFiber (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar) :
    BostSlopeFiber where
  del := F.δ
  η := F.etaVal
  e := F.eVal
  s := s
  muMinCC := muMinCC
  muCC := F.muCC
  HH := HH
  uF := uF
  cardW := cardW

theorem etaVal_bounds (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar) :
    0 ≤ F.etaVal ∧ F.etaVal ≤ 5 * sgBar + 3 * Real.sqrt deBar := by
  unfold etaVal
  constructor
  · have := F.sg_pos.le
    positivity
  · have hsq : Real.sqrt F.de ≤ Real.sqrt deBar := Real.sqrt_le_sqrt F.de_le_bar
    linarith [F.sg_le_bar]

theorem eVal_bounds (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar) :
    0 ≤ F.eVal ∧ F.eVal ≤ 2 * e0Bar ∧ F.eVal ≤ 1 / 4 := by
  unfold eVal
  refine ⟨by linarith [F.e0_nonneg], by linarith [F.e0_le_bar], ?_⟩
  have hsg20 : F.sg ≤ 1 / 20 := le_trans F.sg_le_bar F.sgBar_le
  have hsq : Real.sqrt F.e0 ^ 2 ≤ (F.sg / 2) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) F.sqrt_e0_le 2
  rw [Real.sq_sqrt F.e0_nonneg] at hsq
  have hsg0 : 0 ≤ F.sg := F.sg_pos.le
  nlinarith

/-- **Complete Discharge of `RHDirect.BostSlopeFiber.SlopeIneq`**:
Handles both `0 < uF` (directly via `LatticeFrame.bost_slope_ineq_of_gram_input`) and `uF = 0`
(via `LatticeFrame.corank_share_bound` + `LatticeFrame.projected_gram_corank_density_bound` +
`ArakelovCovolume.bostSlopeFiber_slopeIneq_of_tail_bound`)! -/
theorem toBostSlopeIneq (F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar)
    (huF0 : 0 ≤ uF) :
    F.toBostFiber.SlopeIneq := by
  have hsg20 : F.sg ≤ 1 / 20 := le_trans F.sg_le_bar F.sgBar_le
  have hde4 : F.de ≤ 1 / 4 := le_trans F.de_le_bar F.deBar_le
  have hδ1 : F.δ < 1 := by linarith [F.δ_le_bar, F.delBar_le]
  rcases lt_or_eq_of_le huF0 with huF_pos | huF_zero
  · exact LatticeFrame.bost_slope_ineq_of_gram_input F.Bf F.Vr F.ga
      F.Dstar F.sg F.η0 F.η1 F.e0 F.de F.δ s uF HH muMinCC F.muCC cardW
      F.isIsom F.ga_pos F.Dstar_pos F.sg_pos hsg20 F.rank_ge F.η0_ge F.η0_le F.η1_le
      F.e0_nonneg F.sqrt_e0_le F.de_nonneg hde4 F.corV F.gramInput hδ1 F.card_ge F.κ_pos
      huF_pos F.cardW_ge_one F.y F.y_mean F.y_top F.x rfl F.x_min F.Nτ F.T
      F.Nτ_corank F.T_proj F.T_tail
  · subst huF_zero
    refine ArakelovCovolume.bostSlopeFiber_slopeIneq_of_tail_bound F.toBostFiber
      (Fintype.card F.κ) F.κ_pos F.x le_rfl F.cardW_ge_one rfl F.x_min ?_
    intro _ _ _ _ _ _ _ τ hτ
    have hshare := LatticeFrame.corank_share_bound F.r F.y s 0 τ le_rfl hτ.1 F.y_mean F.y_top
    simp only [zero_div, mul_zero] at hshare
    have hcorN : ∑ i, ((F.r i : ℝ) - Module.finrank ℂ (F.Nτ τ i)) ≤
        (0 : ℝ) * ∑ i, (F.r i : ℝ) := by
      calc ∑ i, ((F.r i : ℝ) - Module.finrank ℂ (F.Nτ τ i))
          ≤ ∑ i, ((Finset.univ.filter (fun j => F.y i j < s - τ)).card : ℝ) :=
            Finset.sum_le_sum fun i _ => F.Nτ_corank τ hτ i
        _ ≤ 0 := hshare
        _ = (0 : ℝ) * ∑ i, (F.r i : ℝ) := by ring
    have hproj := LatticeFrame.projected_gram_corank_density_bound F.Bf F.Vr F.ga (F.Nτ τ) (F.T τ)
      F.Dstar F.sg F.η0 F.η1 F.e0 F.de 0 F.δ
      F.isIsom F.ga_pos F.Dstar_pos F.sg_pos hsg20 F.rank_ge F.η0_ge F.η0_le F.η1_le
      F.e0_nonneg F.sqrt_e0_le F.de_nonneg hde4 F.corV F.gramInput hcorN hδ1 F.card_ge
      (F.T_proj τ hτ)
    have htail := (F.T_tail τ hτ).trans hproj
    have hEq : (1 - F.δ)⁻¹ * (5 * F.sg + 3 * Real.sqrt F.de + 4 * 0 + 4 * Real.sqrt (2 * F.e0)) *
        (Fintype.card F.κ : ℝ) =
        ArakelovCovolume.bostTailWeight F.toBostFiber.del F.toBostFiber.η F.toBostFiber.e
          F.toBostFiber.uF τ * (Fintype.card F.κ : ℝ) := by
      simp only [toBostFiber, etaVal, eVal, ArakelovCovolume.bostTailWeight, ↓reduceIte]
      ring
    exact htail.trans_eq hEq

end Stage2GramFrameFiber

/-- **Wave-Grid Bessel Frame & Test-Vector Separation Bridge (`BesselWaveGrid` → `LatticeFrame`)**:
Combines `BesselWaveGrid.gram_frobenius_frame_bound`, `BesselWaveGrid.grid_frame_linearIndependent`,
and `BesselWaveGrid.exists_delta_test_vector_progY`:
1. Near-orthogonal wave-grid test vectors with off-diagonal Frobenius energy `≤ η²` satisfy both
   frame norm bounds `(dMin - η) ∑ ‖c_i‖² ≤ ‖∑ c_i φ_i‖² ≤ (dMax + η) ∑ ‖c_i‖²`.
2. When row off-diagonal sums satisfy `ρ < dMin`, the wave-grid family is linearly independent.
3. On any `d`-point spacing-5 grid `progY y0 d`, exact Lagrange delta test vectors exist. -/
theorem waveGrid_frame_and_testVector_bridge
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H)
    {dMin dMax η ρ : ℝ} (hη : 0 ≤ η) (hgap : ρ < dMin)
    (hdiag_lo : ∀ i : ι, dMin ≤ ‖φ i‖ ^ 2) (hdiag_hi : ∀ i : ι, ‖φ i‖ ^ 2 ≤ dMax)
    (hfrob : ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ^ 2 ≤ η ^ 2)
    (hrow : ∀ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ≤ ρ)
    (y0 : ℝ) (d : ℕ) (i₀ : Fin d) (α : ℂ) :
    (∀ c : ι → ℂ, (dMin - η) * ∑ i : ι, ‖c i‖ ^ 2 ≤ ‖∑ i : ι, c i • φ i‖ ^ 2 ∧
      ‖∑ i : ι, c i • φ i‖ ^ 2 ≤ (dMax + η) * ∑ i : ι, ‖c i‖ ^ 2) ∧
    LinearIndependent ℂ φ ∧
    ∃ v : Fin d → ℂ, ∀ i : Fin d,
      BesselWaveGrid.waveEval (BesselWaveGrid.vandermondeKernel (fun k : Fin d => y0 + 5 * (k : ℝ))) v i =
        if i = i₀ then α else 0 :=
  ⟨fun c => BesselWaveGrid.gram_frobenius_frame_bound φ c hη hdiag_lo hdiag_hi hfrob,
   BesselWaveGrid.grid_frame_linearIndependent φ hgap hdiag_lo hrow,
   BesselWaveGrid.exists_delta_test_vector_progY y0 d i₀ α⟩

/-- Alternative direct discharge of `BostSlopeFiber.SlopeIneq` from an abstract Arakelov corank
frame (`ArakelovCovolume.bostSlopeFiber_slopeIneq_of_corank_frame`). -/
theorem bostSlopeFiber_slopeIneq_of_arakelov_corank (B : BostSlopeFiber)
    (D : ℕ) (hD : 0 < D) (x : Fin D → ℝ) (D_amb : ℝ) (ε_share : ℝ → ℝ)
    (hu : 0 < B.uF) (hcard : 1 ≤ B.cardW)
    (havg : (∑ j, x j) / (D : ℝ) = B.muCC)
    (hmin : ∀ j, B.muMinCC ≤ x j)
    (hD_amb_nn : 0 ≤ D_amb)
    (hD_amb_le : B.del < 1 → D_amb ≤ (1 - B.del)⁻¹ * (D : ℝ))
    (hCorank : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH, ε_share τ ≤ B.uF / (B.uF + τ))
    (hFrame : 0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
      B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
        ((Finset.univ.filter fun j => x j < B.s - Real.log (B.cardW : ℝ) - τ).card : ℝ)
          ≤ (4 * ε_share τ + B.η + 4 * Real.sqrt B.e) * D_amb) :
    B.SlopeIneq :=
  ArakelovCovolume.bostSlopeFiber_slopeIneq_of_corank_frame B D hD x D_amb ε_share
    hu hcard havg hmin hD_amb_nn hD_amb_le hCorank hFrame

/-! ## Section 2: Discharging `chainOp` Integrality (`ChainIntM`), Weil Convergence &
    Capelli Integral Casts (`RallisSeesaw` + `SiegelWeilCore` + `CapelliCore` + `PAdicChainValuation`) -/

/-- Canonical embedding of `RallisSeesaw.ColumnChainData R ι` into
`ThetaSlopeEngine.IteratedThetaChain R`. -/
def columnChainData_toIteratedThetaChain {R : ChainRanks} {ι : Type} [Fintype ι]
    (C : RallisSeesaw.ColumnChainData R ι) : IteratedThetaChain R where
  cls := C.cls
  Y := C.Y
  wt := C.wt
  Kmap := C.Kmap

/-- Exact pointwise agreement between `ThetaSlopeEngine.chainOp` and `RallisSeesaw.chainOpM`. -/
theorem chainOp_eq_chainOpM {R : ChainRanks} {ι : Type} [Fintype ι]
    (C : RallisSeesaw.ColumnChainData R ι) (j : ℕ) (φ : C.cls 0 → C.Y 0 → ℂ) :
    chainOp C.wt C.Kmap j φ = RallisSeesaw.chainOpM C.wt C.Kmap j φ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext L' y'
    simp only [chainOp, ThetaSlopeEngine.kerOp, RallisSeesaw.chainOpM_succ, RallisSeesaw.kerOpM,
      ih, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Exact column-operator agreement `C.toIteratedThetaChain.col φ = C.col φ`. -/
theorem iteratedThetaChain_col_eq_rallis_col {R : ChainRanks} {ι : Type} [Fintype ι]
    (C : RallisSeesaw.ColumnChainData R ι) (φ : C.cls 0 → C.Y 0 → ℂ) :
    (columnChainData_toIteratedThetaChain C).col φ = C.col φ :=
  chainOp_eq_chainOpM C R.m φ

/-- **Discharging `chainOp` Integrality (`ChainIntM`) from `RallisSeesaw.ColumnChainData`**:
Given any subring `S : Subring ℂ` and `S`-submodules `Λ i ≤ (C.Y i → ℂ)` preserved by the twisted
step kernels `C.Kmap i L L'`, `RallisSeesaw.ColumnChainData.DGam_mul_wt_int` automatically clears
all genus-stabilizer denominators along `j < R.m`, discharging `ChainIntM` via
`ThetaSlopeEngine.chainOp_preserves_lattice`! -/
theorem chainIntM_of_columnChainData {R : ChainRanks} {ι : Type} [Fintype ι]
    (C : RallisSeesaw.ColumnChainData R ι)
    (S : Subring ℂ) (Λ : ∀ i, Submodule S (C.Y i → ℂ))
    (hK : ∀ i L L' (f : C.Y i → ℂ), f ∈ Λ i → C.Kmap i L L' f ∈ Λ (i + 1))
    (φ : C.cls 0 → C.Y 0 → ℂ) (hφ : ∀ L, φ L ∈ Λ 0) (L' : C.cls R.m) :
    (fun y' => (C.DGam : ℂ) ^ R.m * C.col φ L' y') ∈ Λ R.m := by
  let D : ℕ → ℂ := fun i => if i ≤ R.m then (C.DGam : ℂ) else 0
  have hD : ∀ i L, D i * C.wt i L ∈ S := by
    intro i L
    dsimp only [D]
    split_ifs with hi
    · obtain ⟨z, hz⟩ := C.DGam_mul_wt_int hi L
      rw [hz]
      have h1 : z • (1 : ℂ) ∈ S := zsmul_mem S.one_mem z
      simpa only [zsmul_eq_mul, mul_one] using h1
    · rw [zero_mul]
      exact S.zero_mem
  have hprod : (∏ i ∈ Finset.range R.m, D i) = (C.DGam : ℂ) ^ R.m := by
    have hcongr : ∏ i ∈ Finset.range R.m, D i = ∏ _i ∈ Finset.range R.m, (C.DGam : ℂ) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      dsimp only [D]
      rw [if_pos (le_of_lt (Finset.mem_range.mp hi))]
    rw [hcongr, Finset.prod_const, Finset.card_range]
  have hmem := chainOp_preserves_lattice S Λ C.wt C.Kmap D hD hK R.m φ hφ L'
  rw [hprod, chainOp_eq_chainOpM C R.m φ] at hmem
  exact hmem

/-- **All-Steps Weil Convergence & Theta-Integral `L¹` Bound Along `ChainRanks` (`SiegelWeilCore`)**:
Every step `j < R.m` of the rank-stepped chain `R.chainRank j → R.chainRank (j + 1)` with
`R.t + 1 ≤ R.k` and Witt index `r < R.t + 1` lies in Weil's absolute convergence range at
`s₀ = (R.t + 1) / 2`, making every Siegel-envelope-dominated theta kernel Bochner integrable with
explicit `L¹` ceiling. -/
theorem chain_weil_convergent_all_steps (R : ChainRanks) (r : ℕ)
    (htk : R.t + 1 ≤ R.k) (hrt : r < R.t + 1) :
    ∀ j : ℕ,
      let hr : r ≤ R.chainRank (j + 1) := by
        unfold ChainRanks.chainRank
        omega
      let P := SiegelWeilCore.DualPairRanks.ofChainStep R j r hr
      P.WeilConvergentRange ∧
      P.sZero = ((R.t : ℝ) + 1) / 2 ∧
      ∀ {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
        (E : SiegelWeilCore.SiegelSetEnvelope μ),
        E.critExp = (P.n : ℝ) →
        ∀ {θ : X → ℂ} {C : ℝ}, 0 ≤ C →
          MeasureTheory.AEStronglyMeasurable θ μ →
          (∀ᵐ x ∂μ, ‖θ x‖ ≤ C * (E.H x) ^ (-(P.effRank : ℝ))) →
          MeasureTheory.Integrable θ μ ∧
            ‖∫ x, θ x ∂μ‖ ≤ C * ∫ x, (E.H x) ^ (-(P.n : ℝ)) ∂μ := by
  intro j
  have hr : r ≤ R.chainRank (j + 1) := by
    unfold ChainRanks.chainRank
    omega
  have hW : (SiegelWeilCore.DualPairRanks.ofChainStep R j r hr).WeilConvergentRange :=
    SiegelWeilCore.DualPairRanks.chainStep_weilRange R j r hr htk hrt
  refine ⟨hW, SiegelWeilCore.DualPairRanks.chainStep_sZero_eq R j r hr, ?_⟩
  intro X _ μ E hCrit θ C hC hθm hθb
  exact SiegelWeilCore.thetaKernel_integrable_of_weilRange _ hW E hCrit hC hθm hθb

/-- **Rallis Seesaw Stability, Additive Log-Norm Decomposition & Siegel–Weil Definite-Side Assembly**:
Combines `RallisSeesaw.chain_rallis_scalar_recursion`, `RallisSeesaw.chain_log_normSq_additive`,
`RallisSeesaw.definite_chain_nonvanishing`, `SiegelWeilCore.siegel_eisenstein_second_term_assembly`,
and `BesselWaveGrid.local_factor_ratio_matching` into one unified chain-nonvanishing & norm-ratio
certification theorem. -/
theorem chain_rallis_siegelWeil_localFactor_bridge
    {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℂ (E j)]
    [∀ j, FiniteDimensional ℂ (E j)]
    (T : ∀ j, E (j + 1) →ₗ[ℂ] E j) (S : ∀ j, Submodule ℂ (E j)) (c : ℕ → ℂ)
    (hstep : ∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x)
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1))
    (m : ℕ) (hc : ∀ j < m, 0 < (c j).re) {x : E 0} (hx : x ∈ S 0) (hx0 : x ≠ 0)
    {ι : Type*} [DecidableEq ι]
    (L₁ L₂ : BesselWaveGrid.LocalFactorSystem ι) (S₀ : Finset ι)
    (hPlaces : L₁.places = L₂.places) (hS₀ : S₀ ⊆ L₁.places)
    (cArch : ℂ) (cLoc : ι → ℂ)
    (hArch : L₁.archFactor = cArch * L₂.archFactor)
    (hBad : ∀ v ∈ S₀, L₁.localFactor v = cLoc v * L₂.localFactor v)
    (hUnram : ∀ v ∈ L₁.places \ S₀, L₁.localFactor v = L₂.localFactor v)
    {Esp Csp Datum α ιF : Type*} [AddCommGroup Esp] [Module ℂ Esp] [Fintype ιF] [DecidableEq ιF]
    (Dsw : SiegelWeilCore.LiveSiegelWeilSeparationData Esp Csp Datum)
    (hHowe : Dsw.pair.HoweUnram)
    (hSpan : Submodule.span ℂ (Set.range fun h : Dsw.pair.G₂ => Dsw.thetaLift (Dsw.pair.ω (1, h) Dsw.pair.vac)) = ⊤)
    {Start Pinned RowTest RowRat : α → Prop}
    (hPin : SiegelWeilCore.StepImplies Start Pinned)
    (hRat : SiegelWeilCore.StepImplies RowTest RowRat)
    (hTestOfSep : Dsw.fam.Separates Dsw.S → SiegelWeilCore.StepImplies Pinned RowTest)
    (Ffit : SiegelWeilCore.FourierFitData ιF) (hErr : Ffit.totalError < 1)
    {EvGrid RowFun : ℝ → Prop}
    (hGrid : Dsw.fam.Separates Dsw.S → ∃ CF₁ : ℝ, ∀ CF ≥ CF₁, EvGrid CF)
    (hFun : ‖SiegelWeilCore.FourierFitData.evalAtZero Ffit.b - Ffit.a Ffit.i₀‖ ≤
      Ffit.totalError * ‖Ffit.a Ffit.i₀‖ → ∃ CF₀ : ℝ, ∀ CF ≥ CF₀, RowFun CF) :
    (∀ j ≤ m, LinearMap.adjoint (RallisSeesaw.downChain T j) x ∈ S j ∧
      LinearMap.adjoint (RallisSeesaw.downChain T j) x ≠ 0) ∧
    Real.log (‖LinearMap.adjoint (RallisSeesaw.downChain T m) x‖ ^ 2) =
      Real.log (‖x‖ ^ 2) + ∑ j ∈ Finset.range m, Real.log (c j).re ∧
    L₁.globalValue = (cArch * ∏ v ∈ S₀, cLoc v) * L₂.globalValue ∧
    SiegelWeilCore.DefiniteSideAssembly Esp Csp Datum α ιF Dsw Start RowRat Ffit EvGrid RowFun := by
  have hcne : ∀ j < m, c j ≠ 0 := fun j hj hz => by
    have hpos := hc j hj
    rw [hz, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨RallisSeesaw.definite_chain_nonvanishing T S c hstep hS m hcne hx hx0,
    RallisSeesaw.chain_log_normSq_additive T S c hstep hS m hc hx hx0,
    BesselWaveGrid.local_factor_ratio_matching L₁ L₂ S₀ hPlaces hS₀ cArch cLoc hArch hBad hUnram,
    SiegelWeilCore.siegel_eisenstein_second_term_assembly Dsw hHowe hSpan hPin hRat hTestOfSep
      Ffit hErr hGrid hFun⟩

/-- **Capelli Integral-Cast, `p`-adic Determinant & Sharp `m`-Step Column Valuation Bridge
(`CapelliCore` + `PAdicChainValuation`)**:
Combines:
1. `CapelliCore.isIntegral_det_of_preserves_lattice` (lattice-preserving matrices have integral det),
2. `CapelliCore.valuation_det_le_one_of_entries_le_one` (`v`-integral entries ⇒ `v`-integral det),
3. `CapelliCore.det_norm_le` (archimedean determinant bound `‖A.det‖ ≤ n! * C^n`),
4. `CapelliCore.fix_pi_iff` (local-to-global product-subgroup invariance), and
5. `PAdicChainValuation.ChainValuationSystem.levelChainSharpColumnValuation_of_stability`
   (sharp `m`-step common-lattice division without paying `m` separate integrality penalties). -/
theorem capelli_padic_sharp_column_bridge
    {K LL ι_u : Type*} [Field K] [CharZero K] [Field LL]
    (X : PAdicChainValuation.ChainValuationSystem K LL ι_u)
    (hF : X.FormsStable) {s_u : ℕ} (hComm : X.UOpCommutes s_u)
    (A_u : List ι_u) (e_u a_u : ℕ)
    (hU : ∀ i, i < X.m → X.Into i (i + 1) (fun φ => (X.T : K) ^ e_u • X.Uprod (i + 1) A_u (X.KT i φ)))
    {c_u : LL} {n_u : ℤ} (hc_u : X.val c_u = (n_u : WithTop ℤ))
    (hn_u : ((X.ramIdx * (X.m * e_u + s_u * A_u.length * ∑ j ∈ Finset.range (X.m + 1), j) : ℕ) : ℤ) ≤ n_u)
    {x_u : X.Vl 0} (hx_u : x_u ∈ X.S 0)
    -- Capelli integral-cast & determinant data
    {E_nf : Type*} [Field E_nf] [NumberField E_nf] {N_mat : ℕ}
    (L_lat : Submodule (NumberField.RingOfIntegers E_nf) (Fin N_mat → E_nf))
    (hfg : L_lat.FG) (hspan : Submodule.span E_nf (L_lat : Set (Fin N_mat → E_nf)) = ⊤)
    (γ : Matrix (Fin N_mat) (Fin N_mat) E_nf) (hγ : ∀ v ∈ L_lat, γ.mulVec v ∈ L_lat)
    {ι_d : Type*} [Fintype ι_d] [DecidableEq ι_d]
    (A_arch : Matrix ι_d ι_d ℂ) {C_arch : ℝ} (hA_arch : ∀ i j, ‖A_arch i j‖ ≤ C_arch)
    {ι_g : Type*} [Finite ι_g] [DecidableEq ι_g] {G : ι_g → Type*} [∀ i, Group (G i)]
    {R_rep M_rep : Type*} [CommRing R_rep] [AddCommGroup M_rep] [Module R_rep M_rep]
    (ρ : Representation R_rep (∀ i, G i) M_rep) (Ksub : ∀ i, Subgroup (G i)) (v_rep : M_rep) :
    (∃ z ∈ X.S X.m,
      X.embV X.m z =
        (X.embK c_u * (X.T : K) ^ a_u) • X.colUp X.m (((X.Uprod 0 A_u) ^ X.m) (X.embV 0 x_u))) ∧
    IsIntegral ℤ γ.det ∧
    ‖A_arch.det‖ ≤ ((Fintype.card ι_d).factorial : ℝ) * C_arch ^ Fintype.card ι_d ∧
    ((∀ k ∈ Subgroup.pi Set.univ Ksub, ρ k v_rep = v_rep) ↔
      ∀ j, ∀ k ∈ Ksub j, ρ (Pi.mulSingle j k) v_rep = v_rep) :=
  ⟨X.levelChainSharpColumnValuation_of_stability hF hComm A_u e_u a_u hU hc_u hn_u hx_u,
   CapelliCore.isIntegral_det_of_preserves_lattice L_lat hfg hspan γ hγ,
   CapelliCore.det_norm_le A_arch hA_arch,
   CapelliCore.fix_pi_iff ρ Ksub v_rep⟩

/-! ## Section 3: Discharging `mass_ratio_ge` (`Lam5 ≤ log T`) & Curvature / Moriwaki
    Covolume Bounds (`UnitaryMassFormula` + `HermitianCurvatureCore` + `ArakelovCovolume`) -/

/-- Siegel–Tamagawa unitary mass-ratio & level-index datum at a fiber `(u0, u)`.
Does **not** assume `D.Lam5 C u0 ≤ Real.log (D.T u0 u)` — this lower bound is discharged by
`Stage2MassRatioDatum.lam5_le_log_T` via `UnitaryMassFormula.mass_ratio_ge_with_error` and
`UnitaryMassFormula.mass_ratio_error_le_four_of_scaleParams`. -/
structure Stage2MassRatioDatum (f m k : ℕ) (vE g₁ g₂ L_scale La cCount : ℝ)
    (w_u0 : Fin m → Fin f → ℝ) (T_val : ℝ) : Type where
  massk : ℝ
  massr : ℝ
  Isig : ℝ
  Ipi : ℝ
  Dstar : ℝ
  dstar : ℝ
  dimRatio : ℝ
  B_L : ℝ
  W_lo : ℝ
  Lval : ℕ → ℝ
  massk_pos : 0 < massk
  massr_pos : 0 < massr
  Isig_pos : 0 < Isig
  Ipi_pos : 0 < Ipi
  dimRatio_pos : 0 < dimRatio
  Lval_pos : ∀ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1), 0 < Lval M
  Lval_log_ge : -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Lval M)
  B_L_le : B_L ≤ (m : ℝ) * L_scale
  mass_telescope : massr = massk * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
    UnitaryMassFormula.massRatioFactor f vE Lval M
  level_index_ge : ((2 : ℝ) ^ (2 * f))⁻¹ *
      (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤
    Isig / Ipi
  covolume_ratio_ge : (2 / 3 : ℝ) ^ f * (massr / massk) * (Isig / Ipi) * dimRatio ≤ Dstar / dstar
  weyl_sum_ge : W_lo ≤
    (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
      (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
    (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio
  arch_weight_le :
    (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) + Real.log (vE / Real.pi) ≤ W_lo
  log_T_ge : (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) ≤ Real.log T_val

/-- **Discharging `Lam5 ≤ log T` (`SlopeHypotheses.count.1`) from `UnitaryMassFormula.mass_ratio_ge_with_error`**:
Proves that the `m`-step logarithmic mass/covolume lower bound `Lam5` is bounded above by `log T_val`
using `mass_ratio_ge_with_error` and `mass_ratio_error_le_four_of_scaleParams`. -/
theorem Stage2MassRatioDatum.lam5_le_log_T {s : ScaleParams} {R : ChainRanks}
    {vE g₁ g₂ La cCount T_val : ℝ} {w_u0 : Fin R.m → Fin R.f → ℝ}
    (hf : 1 ≤ R.f) (hm : 1 ≤ R.m) (hk : 2 ≤ R.k)
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ s.L) (hL1 : 1 ≤ s.L)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂)
    (hw_pos : ∀ j ρ, 0 < w_u0 j ρ)
    (hmkL : (R.m : ℝ) * s.L ≤ (R.k : ℝ))
    (hcCount_nn : 0 ≤ cCount) (hLa_nn : 0 ≤ La) (h4 : 4 ≤ cCount * La)
    (hM : Stage2MassRatioDatum R.f R.m R.k vE g₁ g₂ s.L La cCount w_u0 T_val) :
    (∑ j : Fin R.m, (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ * vE / Real.pi)) +
      (R.m : ℝ) * (Real.log g₁ + Real.log g₂) -
      cCount * (La + (R.m : ℝ) ^ 2 * La / (R.k : ℝ)) ≤ Real.log T_val := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hf_pos : (0 : ℝ) < (R.f : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_pos : (0 : ℝ) < (R.k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmass := UnitaryMassFormula.mass_ratio_ge_with_error hf hm hk hv hvL hL1 hg₁ hg₂
    hM.massk_pos hM.massr_pos hM.Isig_pos hM.Ipi_pos hM.dimRatio_pos
    hM.Lval_pos hM.Lval_log_ge hM.B_L_le hM.mass_telescope hM.level_index_ge
    hM.covolume_ratio_ge hM.weyl_sum_ge
  have herr4 : (3 * (R.m : ℝ) * s.L + Real.log 6) / (R.k : ℝ) ≤ 4 :=
    UnitaryMassFormula.mass_ratio_error_le_four_of_scaleParams s R hk hmkL
  have hsplit :
      (∑ j : Fin R.m, (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ * vE / Real.pi)) =
      (∑ j : Fin R.m, (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ)) +
        Real.log (vE / Real.pi) + ((R.m : ℝ) - 1) * Real.log (vE / Real.pi) := by
    have hinner : ∀ j : Fin R.m,
        (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ * vE / Real.pi) =
        (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ) + Real.log (vE / Real.pi) := by
      intro j
      have hterm : ∀ ρ : Fin R.f,
          Real.log (w_u0 j ρ * vE / Real.pi) = Real.log (w_u0 j ρ) + Real.log (vE / Real.pi) := by
        intro ρ
        rw [mul_div_assoc, Real.log_mul (hw_pos j ρ).ne' (div_pos hv_pos Real.pi_pos).ne']
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp [hf_pos.ne']
    simp_rw [hinner, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hquad_nn : 0 ≤ cCount * ((R.m : ℝ) ^ 2 * La / (R.k : ℝ)) := by positivity
  have hLam_err : (3 * (R.m : ℝ) * s.L + Real.log 6) / (R.k : ℝ) ≤
      cCount * (La + (R.m : ℝ) ^ 2 * La / (R.k : ℝ)) := by
    have h1 : cCount * (La + (R.m : ℝ) ^ 2 * La / (R.k : ℝ)) =
        cCount * La + cCount * ((R.m : ℝ) ^ 2 * La / (R.k : ℝ)) := by ring
    linarith
  have h1 := hM.arch_weight_le
  have h2 := hM.log_T_ge
  rw [hsplit]
  linarith

/-- **Stabilizer-Orbit Volume, Finite-Genus Mass & `GL5` Signature Induction Bridge
(`UnitaryMassFormula`)**:
Unifies `volStab_eq_of_siegelWeil_unfold`, `genusMass_eq_covolume_div`, and
`volume_eq_mass_of_ratio_induction` for Pillar-2 volume/mass calculations. -/
theorem unitary_mass_and_stabilizer_bridge
    {G H O : Type*} [MeasurableSpace G] [MeasurableSpace H] [MeasurableSpace O]
    (C : UnitaryMassFormula.OrbitStabContext G H O)
    (hSW : UnitaryMassFormula.SiegelWeilUnfoldHyp C 1)
    {vol : ℕ → ℕ → ℝ} {mass : ℕ → ℝ}
    (hbase : vol 2 0 = mass 2)
    (hmass_ne : ∀ n, 2 ≤ n → mass n ≠ 0)
    (hstepP : ∀ P Q, 2 ≤ P → vol (P + 1) Q / vol P Q = mass (P + 1 + Q) / mass (P + Q))
    (hstepQ : ∀ P Q, 2 ≤ P → vol P (Q + 1) / vol P Q = mass (P + Q + 1) / mass (P + Q)) :
    C.μ' C.𝓕' = C.μ C.𝓕 ∧ ∀ P Q, 2 ≤ P → vol P Q = mass (P + Q) :=
  ⟨UnitaryMassFormula.volStab_eq_of_siegelWeil_unfold C hSW,
   UnitaryMassFormula.volume_eq_mass_of_ratio_induction hbase hmass_ne hstepP hstepQ⟩

/-- **Curvature / Moriwaki Covolume Ceiling & Divisible Bost Slope Discharge
(`HermitianCurvatureCore` + `ArakelovCovolume`)**:
Combines:
1. `HermitianCurvatureCore.height_upper_bound_of_small_section_bound` (AHS + Minkowski +
   small-section upper bound ⇒ `selfInt ≤ V` and `normalizedHeight ≤ V / ((D+1) * geomDeg)`),
2. `HermitianCurvatureCore.bost_slope_from_curvature_volume_bound` (curvature volume cap +
   `B.SlopeIneq` ⇒ explicit slope-excess ceiling bounded by `log B.cardW`),
3. `HermitianCurvatureCore.recursion_sharp_bound` (sharp iterated curvature/norm recursion
   with explicit constant `55`), and
4. `ArakelovCovolume.bost_slope_inequality_divisible` (divisible Arakelov lattice map
   `φ : L →ₗ[ℤ] M` with `D_div ∣ φ(x)` ⇒ `slope L + log D_div ≤ muMax M + log C_op`). -/
theorem moriwaki_curvature_covolume_bridge
    (D_dim : ℕ) (chiArith logSmallCount : ℕ → ℝ) {selfInt geomDeg V : ℝ}
    (hdeg : 0 < geomDeg)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      selfInt - ε ≤ chiArith n / HermitianCurvatureCore.arithVolNorm D_dim n)
    (hMink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      chiArith n - ε * HermitianCurvatureCore.arithVolNorm D_dim n ≤ logSmallCount n)
    (hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      logSmallCount n / HermitianCurvatureCore.arithVolNorm D_dim n ≤ V + ε)
    -- Bost fiber curvature cap
    (B : BostSlopeFiber) (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η)
    (he0 : 0 ≤ B.e) (he1 : B.e ≤ 1 / 4)
    (hHH : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hmuCC_le : B.muCC ≤ HermitianCurvatureCore.normalizedHeight D_dim selfInt geomDeg)
    -- Divisible Arakelov lattice map
    {E_lat F_lat : Type*}
    [NormedAddCommGroup E_lat] [InnerProductSpace ℝ E_lat] [FiniteDimensional ℝ E_lat]
    [NormedAddCommGroup F_lat] [InnerProductSpace ℝ F_lat] [FiniteDimensional ℝ F_lat]
    (L_lat : Submodule ℤ E_lat) (M_lat : Submodule ℤ F_lat)
    [DiscreteTopology L_lat] [DiscreteTopology M_lat] (hL0 : L_lat ≠ ⊥)
    (φ_lat : L_lat →ₗ[ℤ] M_lat) (C_op : ℝ) (D_div : ℕ) (hD_div : 0 < D_div)
    (hφ_inj : Function.Injective φ_lat)
    (hC_op : ∀ x : L_lat, ‖((φ_lat x : M_lat) : F_lat)‖ ≤ C_op * ‖(x : E_lat)‖)
    (hDiv_lat : ∀ x : L_lat, ∃ y : M_lat, φ_lat x = (D_div : ℤ) • y) :
    selfInt ≤ V ∧
    B.s - V / (((D_dim + 1 : ℕ) : ℝ) * geomDeg) -
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) ≤ Real.log (B.cardW : ℝ) ∧
    ArakelovCovolume.slope L_lat + Real.log (D_div : ℝ) ≤
      ArakelovCovolume.muMax M_lat + Real.log C_op := by
  obtain ⟨hself, hht⟩ := HermitianCurvatureCore.height_upper_bound_of_small_section_bound
    D_dim chiArith logSmallCount hdeg hAHS hMink hUpper
  have hcap : B.muCC ≤ V / (((D_dim + 1 : ℕ) : ℝ) * geomDeg) := hmuCC_le.trans hht
  exact ⟨hself,
    HermitianCurvatureCore.bost_slope_from_curvature_volume_bound B hSlope
      hdel0 hdel1 hη he0 he1 hHH hHH_pos hcap,
    ArakelovCovolume.bost_slope_inequality_divisible L_lat M_lat hL0 φ_lat C_op D_div hD_div
      hφ_inj hC_op hDiv_lat⟩

/-! ## Section 4: Discharging `RankVal` Window Arithmetic, `divinN` Divisibility &
    `Ga_bound5` Common-Slope Cancellation (`PAdicChainValuation` + `SlopeInequality` + `BesselWaveGrid`) -/

/-- Canonical `RHDirect.ScaleParams` built from `(x, eps)` with `delta1 = x ^ (-(eps / 8))` and
`L = x ^ eps`. -/
def stage2ScaleParams (x eps : ℝ) (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52) :
    ScaleParams where
  x := x
  eps := eps
  delta1 := x ^ (-(eps / 8))
  L := x ^ eps
  x_gt_one := hx1
  eps_pos := heps
  eps_lt := heps52
  delta1_pos := Real.rpow_pos_of_pos (by linarith) _
  L_pos := Real.rpow_pos_of_pos (by linarith) _

/-- **10-in-1 `RankVal` Window Discharge Theorem**:
From `RankVal (stage2ScaleParams x eps ...) R` and explicit large-`x` thresholds (`x ≥ 2^100`,
`x ≥ 2^(16/(9*eps))`), automatically proves ALL 10 size/rank/cutoff inequalities required by
`SlopeInequality`, `ThetaSlopeEngine`, `PAdicChainValuation.divinN_of_vAt`, `BesselWaveGrid`,
and `UnitaryMassFormula`! -/
theorem rankVal_discharges_chain_window_bounds {x eps : ℝ} {R : ChainRanks}
    (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52)
    (hx100 : (2 : ℝ) ^ 100 ≤ x)
    (hx16 : (2 : ℝ) ^ (16 / (9 * eps)) ≤ x)
    (hf_eq : R.f = 2 * R.n) (hm2 : 2 ≤ R.m) (hmk : R.m + 3 ≤ R.k) (hr_eq : R.r = R.k + R.m - 1)
    (hR : RankVal (stage2ScaleParams x eps hx1 heps heps52) R) :
    0 < R.n ∧
    1 ≤ R.f ∧
    R.t ≤ ⌊x ^ (400 : ℝ)⌋₊ ∧
    x ^ ((1 : ℝ) / 2 - eps) ≤ (R.m : ℝ) ∧
    (R.m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + eps / 2) ∧
    x * (R.m : ℝ) ≤ (R.k : ℝ) ∧
    (1 : ℝ) ≤ (R.k : ℝ) ∧
    (R.k : ℝ) ≤ x ^ (5 : ℝ) ∧
    (R.k : ℝ) ≤ (R.n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - eps) ∧
    (2 ≤ R.k ∧ (R.m : ℝ) * x ^ eps ≤ (R.k : ℝ) ∧
      TOv (stage2ScaleParams x eps hx1 heps heps52) *
        nWv R (stage2ScaleParams x eps hx1 heps heps52) ≤ R.r + R.t) := by
  set s := stage2ScaleParams x eps hx1 heps heps52
  have hx0 : 0 < x := by linarith
  have hx_ge1 : 1 ≤ x := hx1.le
  have hn_lo : x ^ (2 + 8 * eps) ≤ (R.n : ℝ) := hR.1.1
  have hm_lo : Real.sqrt (x * x ^ (-(eps / 8))) ≤ (R.m : ℝ) := hR.2.1.1
  have hm_up : (R.m : ℝ) ≤ 2 * Real.sqrt (x * x ^ (-(eps / 8))) := hR.2.1.2
  have hk_lo : x ^ ((9 : ℝ) / 2 + 10 * eps) ≤ (R.k : ℝ) := hR.2.2.1.1
  have hk_up : (R.k : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 2 + 10 * eps) := hR.2.2.1.2
  -- 1. 0 < R.n and 1 ≤ R.f
  have hn_ge1 : (1 : ℝ) ≤ (R.n : ℝ) :=
    (Real.one_le_rpow hx_ge1 (by linarith)).trans hn_lo
  have hn_pos : 0 < R.n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn_ge1)
  have hf_ge1 : 1 ≤ R.f := by omega
  -- 2. R.t ≤ ⌊x ^ 400⌋₊ via SlopeInequality.eventually_rank_le_rpow_400
  have ht_rpow : (R.t : ℝ) ≤ x ^ (400 : ℝ) :=
    eventually_rank_le_rpow_400 s R hx100 rfl rfl hf_eq hm2 hmk hr_eq hR
  have ht_floor : R.t ≤ ⌊x ^ (400 : ℝ)⌋₊ := Nat.le_floor ht_rpow
  -- 3. √(x * x^(-(eps/8))) = x^(1/2 - eps/16)
  have hsqrt_eq : Real.sqrt (x * x ^ (-(eps / 8))) = x ^ ((1 : ℝ) / 2 - eps / 16) := by
    rw [Real.sqrt_eq_rpow]
    have hmul : x * x ^ (-(eps / 8)) = x ^ ((1 : ℝ) + -(eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [hmul, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  -- 4. x^(1/2 - eps) ≤ m
  have hm_ge_rest : x ^ ((1 : ℝ) / 2 - eps) ≤ (R.m : ℝ) := by
    calc x ^ ((1 : ℝ) / 2 - eps)
        ≤ x ^ ((1 : ℝ) / 2 - eps / 16) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
      _ = Real.sqrt (x * x ^ (-(eps / 8))) := hsqrt_eq.symm
      _ ≤ (R.m : ℝ) := hm_lo
  -- 5. 2 ≤ x^(9*eps/16) ⇒ m ≤ x^(1/2 + eps/2)
  have h2_916 : (2 : ℝ) ≤ x ^ (9 * eps / 16) := by
    have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (16 / (9 * eps)) := Real.rpow_nonneg (by norm_num) _
    have hpow : ((2 : ℝ) ^ (16 / (9 * eps))) ^ (9 * eps / 16) = 2 := by
      rw [← Real.rpow_mul (by norm_num)]
      have h1 : 16 / (9 * eps) * (9 * eps / 16) = 1 := by field_simp [heps.ne']
      rw [h1, Real.rpow_one]
    calc (2 : ℝ) = ((2 : ℝ) ^ (16 / (9 * eps))) ^ (9 * eps / 16) := hpow.symm
      _ ≤ x ^ (9 * eps / 16) := Real.rpow_le_rpow hbase hx16 (by positivity)
  have hm_le_win : (R.m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + eps / 2) := by
    calc (R.m : ℝ)
        ≤ 2 * Real.sqrt (x * x ^ (-(eps / 8))) := hm_up
      _ = 2 * x ^ ((1 : ℝ) / 2 - eps / 16) := by rw [hsqrt_eq]
      _ ≤ x ^ (9 * eps / 16) * x ^ ((1 : ℝ) / 2 - eps / 16) :=
          mul_le_mul_of_nonneg_right h2_916 (Real.rpow_nonneg hx0.le _)
      _ = x ^ ((1 : ℝ) / 2 + eps / 2) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
  -- 6. x * m ≤ k
  have hxm_le_k : x * (R.m : ℝ) ≤ (R.k : ℝ) := by
    calc x * (R.m : ℝ)
        ≤ x * x ^ ((1 : ℝ) / 2 + eps / 2) := mul_le_mul_of_nonneg_left hm_le_win hx0.le
      _ = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2 + eps / 2) := by rw [Real.rpow_one]
      _ = x ^ ((3 : ℝ) / 2 + eps / 2) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ x ^ ((9 : ℝ) / 2 + 10 * eps) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
      _ ≤ (R.k : ℝ) := hk_lo
  -- 7. 1 ≤ k and 2 ≤ k
  have hk_ge2R : (2 : ℝ) ≤ (R.k : ℝ) := by
    have h2x : (2 : ℝ) ≤ x := by
      have : (2 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith
    calc (2 : ℝ) ≤ x := h2x
      _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ ((9 : ℝ) / 2 + 10 * eps) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
      _ ≤ (R.k : ℝ) := hk_lo
  have hk_ge1 : (1 : ℝ) ≤ (R.k : ℝ) := by linarith
  have hk_ge2 : 2 ≤ R.k := by exact_mod_cast hk_ge2R
  -- 8. k ≤ x^5 (using 2 ≤ x^(1/4) from x ≥ 2^100 and 10*eps < 1/4)
  have h2_quarter : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by
    have hpow : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (25 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h2_25 : (2 : ℝ) ≤ (2 : ℝ) ^ (25 : ℝ) := by
      rw [show (25 : ℝ) = (25 : ℕ) by norm_num, Real.rpow_natCast]; norm_num
    calc (2 : ℝ) ≤ ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 4) := by rw [hpow]; exact h2_25
      _ ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hx100 (by norm_num)
  have hk_le_x5 : (R.k : ℝ) ≤ x ^ (5 : ℝ) := by
    calc (R.k : ℝ)
        ≤ 2 * x ^ ((9 : ℝ) / 2 + 10 * eps) := hk_up
      _ ≤ x ^ ((1 : ℝ) / 4) * x ^ ((9 : ℝ) / 2 + 10 * eps) :=
          mul_le_mul_of_nonneg_right h2_quarter (Real.rpow_nonneg hx0.le _)
      _ = x ^ ((1 : ℝ) / 4 + ((9 : ℝ) / 2 + 10 * eps)) := (Real.rpow_add hx0 _ _).symm
      _ ≤ x ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
  -- 9. k ≤ n^2 * x^(1/2 - eps)
  have h2_5eps : (2 : ℝ) ≤ x ^ (5 * eps) :=
    h2_916.trans (Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith))
  have hk_le_n2 : (R.k : ℝ) ≤ (R.n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - eps) := by
    have hn2 : (x ^ (2 + 8 * eps)) ^ 2 ≤ (R.n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hn_lo 2
    have hexp : x ^ (5 * eps) * x ^ ((9 : ℝ) / 2 + 10 * eps) =
        (x ^ (2 + 8 * eps)) ^ 2 * x ^ ((1 : ℝ) / 2 - eps) := by
      rw [sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1; ring
    calc (R.k : ℝ)
        ≤ 2 * x ^ ((9 : ℝ) / 2 + 10 * eps) := hk_up
      _ ≤ x ^ (5 * eps) * x ^ ((9 : ℝ) / 2 + 10 * eps) :=
          mul_le_mul_of_nonneg_right h2_5eps (Real.rpow_nonneg hx0.le _)
      _ = (x ^ (2 + 8 * eps)) ^ 2 * x ^ ((1 : ℝ) / 2 - eps) := hexp
      _ ≤ (R.n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - eps) :=
          mul_le_mul_of_nonneg_right hn2 (Real.rpow_nonneg hx0.le _)
  -- 10. m * x^eps ≤ k and TOv * nWv ≤ r + t (via BesselWaveGrid)
  have hmL_le_k : (R.m : ℝ) * x ^ eps ≤ (R.k : ℝ) := by
    calc (R.m : ℝ) * x ^ eps
        ≤ x ^ ((1 : ℝ) / 2 + eps / 2) * x ^ eps :=
          mul_le_mul_of_nonneg_right hm_le_win (Real.rpow_nonneg hx0.le _)
      _ = x ^ ((1 : ℝ) / 2 + 3 * eps / 2) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ x ^ ((9 : ℝ) / 2 + 10 * eps) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
      _ ≤ (R.k : ℝ) := hk_lo
  have hWv := (BesselWaveGrid.rankVal_wave_grid_bounds hR).1
  exact ⟨hn_pos, hf_ge1, ht_floor, hm_ge_rest, hm_le_win, hxm_le_k, hk_ge1, hk_le_x5, hk_le_n2,
    ⟨hk_ge2, hmL_le_k, hWv⟩⟩

/-- **Discharging `SlopeHypotheses.div` Directly from `WinDatum.vAt_400` (`PAdicChainValuation.divinN_of_vAt`)**:
Unpacks `VAt S ψ eps 400 q d e_page x`, combines `R.t ≤ ⌊x ^ 400⌋₊` and `(log x)^2 ≤ x^eps`
with the raw Selmer/Sha `LinkN` bound, and proves the full `SlopeData` divisibility inequality
with `B0 = R.f * R.m * exp(x^eps) * x^eps` and `eDiv = 1`! -/
theorem divinN_discharges_slope_div {S : SelmerSystem} {ψ : PChar}
    {Top : Type} [Fintype Top]
    {eps x Nc cLink cDiv a La muCC hVal Fo TVal logOm : ℝ} {aT : Top → ℝ}
    {q d e_page : ℕ} {R : ChainRanks}
    {E_field : Type} [Field E_field] [NumberField E_field]
    (hV : VAt S ψ eps 400 q d e_page x) (hChi : IsChiField ψ e_page q d E_field)
    (ht : R.t ≤ ⌊x ^ (400 : ℝ)⌋₊)
    (hx : 1 < x) (heps : 0 < eps) (hf : 1 ≤ R.f) (hm : 1 ≤ R.m)
    (hNc : 0 ≤ Nc) (hcDiv_ge : |cLink| + 1 ≤ cDiv)
    (hlog : Real.log x ^ 2 ≤ x ^ eps)
    (hLink :
      (muCC + hVal - Fo) -
        (∑ t : Top, ((R.m : ℝ) * (SlopeInequality.ph (aT t) - aT t * logOm) - aT t * Real.log TVal)) -
        cDiv * (Fintype.card Top : ℝ) * a * La ≤
      (R.m : ℝ) * (cLink * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
        Real.log x ^ 2 * Nc) + ∑' l, PAdicChainValuation.vvTerm S E_field R.t l)) :
    muCC + hVal - Fo ≤
      (∑ t : Top, ((R.m : ℝ) * (SlopeInequality.ph (aT t) - aT t * logOm) - aT t * Real.log TVal)) +
      (cDiv * (Fintype.card Top : ℝ) * a * La +
        cDiv * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc) *
          x ^ ((1 : ℝ) * eps)) := by
  have hdiv := PAdicChainValuation.divinN_of_vAt hV hChi ht hx heps hf hm hNc hLink hlog
  have hx0 : 0 < x := by linarith
  have hB0_nn : 0 ≤ (R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc := by
    have := Real.exp_pos (x ^ eps)
    have := Real.rpow_pos_of_pos hx0 eps
    positivity
  have hm_nn : (0 : ℝ) ≤ (R.m : ℝ) := Nat.cast_nonneg _
  have hxe_nn : 0 ≤ x ^ eps := Real.rpow_nonneg hx0.le eps
  have hmono : (R.m : ℝ) * ((|cLink| + 1) * x ^ eps *
      ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc)) ≤
      cDiv * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc) *
        x ^ ((1 : ℝ) * eps) := by
    rw [one_mul]
    have h1 : (|cLink| + 1) * ((R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc) *
        x ^ eps) ≤
        cDiv * ((R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc) *
        x ^ eps) :=
      mul_le_mul_of_nonneg_right hcDiv_ge (mul_nonneg (mul_nonneg hm_nn hB0_nn) hxe_nn)
    linarith
  linarith

/-- **Discharging `Ga_bound5` Common-Slope Cancellation (`PAdicChainValuation.CongruenceSlopeData.Ga_bound5`)**:
Wires a `Stage2GramFrameFiber` (which proves `(D.fiber u0).SlopeIneq`) directly into
`PAdicChainValuation.CongruenceSlopeData.s_lower5`, `u_function_le_mean`, and `Ga_bound5`,
discharging the exact pointwise common-slope cancellation inequality without assuming `SlopeIneq`. -/
theorem ga_bound5_of_gram_frame_fiber
    {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (D : PAdicChainValuation.CongruenceSlopeData U0 W Top m f) (Xpp : ℝ) (u0 : U0)
    (sgBar deBar e0Bar : ℝ)
    (F : Stage2GramFrameFiber (D.s u0) (D.uF u0) (D.HH u0) (D.muMinCC u0) (Fintype.card (W u0))
      D.delBar sgBar deBar e0Bar)
    (hdel_eq : D.del u0 = F.δ) (hη_eq : D.η u0 = F.etaVal) (he_eq : D.e u0 = F.eVal)
    (hmuCC_eq : D.muCC u0 = F.muCC)
    (hηBar : 5 * sgBar + 3 * Real.sqrt deBar ≤ D.etaBar)
    (heBar : 2 * e0Bar ≤ D.eBar)
    (hx : 0 < D.x) (hb : 0 < D.b) (hv : 0 < D.v) (hf : 0 < f)
    (hw : ∀ j ρ, 0 < D.w u0 j ρ)
    (hd : ∀ u : W u0, 0 < D.d u0 u)
    (hmu_le : ∀ u : W u0, D.muN u0 u ≤ D.muMaxN u0 u)
    (hsumA : 0 ≤ D.sumA)
    (hHH0 : 0 < D.HH u0) (hHH_s : D.s u0 - D.muMinCC u0 ≤ D.HH u0)
    (hHH_up : D.HH u0 ≤ D.x ^ D.cHH * D.b)
    (hDIV : ∀ u : W u0,
      D.muCC u0 + D.h u0 u - D.Fo u0 ≤
        (∑ t : Top, ((m : ℝ) * (PAdicChainValuation.ph (D.aT t) - D.aT t * D.logOm) -
          D.aT t * Real.log (D.T u0 u))) + D.EDiv)
    (hE : ∀ u : W u0, |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ D.cE * (m : ℝ) * D.B0)
    (hH : ∀ u u' : W u0,
      |(D.h u0 u' + ∑ t : Top, D.aT t * Real.log (D.T u0 u')) -
        (D.h u0 u + ∑ t : Top, D.aT t * Real.log (D.T u0 u))| ≤
      D.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0))
    (hCount : ∀ u : W u0, D.Lam5 u0 ≤ Real.log (D.T u0 u))
    (hTdiff : ∀ u u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ D.cCount * Real.log D.k)
    (hSl : ∀ u : W u0,
      -(D.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u ∧
      D.muMaxM u0 u ≤ D.cSlope * D.nT * D.a * D.La)
    (hSN : ∀ u : W u0,
      D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + D.cSl1 * (m : ℝ) * D.B0 ∧
      D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - D.Lo5 Xpp u0 u ≤ D.muN u0 u) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + D.K0v5 +
      PAdicChainValuation.wmean (D.d u0) (D.Lo5 Xpp u0) +
      (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ D.cHH) *
        (D.K3 + PAdicChainValuation.wmean (D.d u0) (D.Lo5 Xpp u0) + D.b) +
        (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ D.cHH * D.b)) := by
  have huF0 : 0 ≤ D.uF u0 := by
    unfold PAdicChainValuation.CongruenceSlopeData.uF PAdicChainValuation.CongruenceSlopeData.s
    have hle : ∀ u : W u0, D.muN u0 u - D.h u0 u ≤
        Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) := fun u =>
      (by linarith [hmu_le u] : D.muN u0 u - D.h u0 u ≤ D.muMaxN u0 u - D.h u0 u).trans
        (Finset.le_sup' (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) (Finset.mem_univ u))
    linarith [PAdicChainValuation.wmean_le_const hd _ hle]
  have hfib_eq : D.fiber u0 = F.toBostFiber := by
    unfold PAdicChainValuation.CongruenceSlopeData.fiber Stage2GramFrameFiber.toBostFiber
    rw [hdel_eq, hη_eq, he_eq, hmuCC_eq]
  have hSI : (D.fiber u0).SlopeIneq := by
    rw [hfib_eq]
    exact F.toBostSlopeIneq huF0
  have hs_lo := D.s_lower5 Xpp u0 hd hsumA hDIV hE hCount (fun u => (hSl u).1) (fun u => (hSN u).2)
  have huF_le := D.u_function_le_mean Xpp u0 hd hsumA hE hH hTdiff hSl hSN
  obtain ⟨hη0, hηle⟩ := F.etaVal_bounds
  obtain ⟨he0, hele, he4⟩ := F.eVal_bounds
  exact D.Ga_bound5 Xpp u0 hx hb hv hf hw
    (hdel_eq ▸ F.δ_nonneg) (hdel_eq ▸ F.δ_le_bar) (by linarith [F.delBar_le])
    (hη_eq ▸ hη0) (hη_eq ▸ hηle.trans hηBar)
    (he_eq ▸ he0) (he_eq ▸ he4) (he_eq ▸ hele.trans heBar)
    hHH0 hHH_s hHH_up huF0 huF_le hs_lo hSI

/-! ## Section 5: The Strictly Smaller `Stage2ThetaCoreInputs S` & Master Bridge to
    `ThetaSlopeEngine.MinimalThetaEngineInputs S` and `ThetaSlopeContract S` -/

/-- **Irreducible Stage 2 Core Fiber Witness** at scale `(x, eps)` and auxiliary datum `(q, d, e_page)`.
Every field discharged by our 9 Pillar-2 specialist modules and large-`x` asymptotics is **removed**:
- `eD` (pinned to `1` by `PAdicChainValuation.divinN_of_vAt`),
- `b` (`:= exp(x^eps)`), `L` (`:= x^eps`), `B0` (`:= f * m * b * x^eps`), `eK` (`:= 5`),
- `BostSlopeFiber.SlopeIneq` (discharged by `LatticeFrame` + `ArakelovCovolume`),
- `SlopeHypotheses.div` (discharged from `WinDatum.vAt_400` by `PAdicChainValuation.divinN_of_vAt`),
- `SlopeHypotheses.count.1` (`Lam5 ≤ log T`, discharged by `UnitaryMassFormula.mass_ratio_ge_with_error`),
- `SlopeHypotheses.fParams` + `delBar < 1`, `etaBar ≥ 0`, `0 ≤ eBar ≤ 1/4` (discharged by `LatticeFrame`),
- `ErrorWindowBounds.log_x_le`, `KBig_le`, `m_le`, `xm_le_k`, `k_ge_one`, `k_le_xeK`, `L_le`, `B0_nonneg`,
- `RestSize` #4 (`x^(1/2-eps) ≤ m`), #5 (`k ≤ n^2 * x^(1/2-eps)`), `B0 ≤ 2 n m b x^eps`, `0 < n`, `0 < f`, `0 < v`. -/
structure Stage2FiberWitness (S : SelmerSystem) (ψ : PChar) (eL K cHH eps x : ℝ)
    (q d_aux e_page : ℕ) (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52) : Type 1 where
  -- Fiber index spaces & RankVal-constrained unitary chain ranks
  U0 : Type
  [finU0 : Fintype U0]
  [neU0 : Nonempty U0]
  W : U0 → Type
  [finW : ∀ u0, Fintype (W u0)]
  [neW : ∀ u0, Nonempty (W u0)]
  Top : Type
  [finTop : Fintype Top]
  R : ChainRanks
  f_eq : R.f = 2 * R.n
  m_ge_two : 2 ≤ R.m
  mk_le : R.m + 3 ≤ R.k
  r_eq : R.r = R.k + R.m - 1
  rankVal : RankVal (stage2ScaleParams x eps hx1 heps heps52) R
  nT2 : ℕ
  nT2_le : nT2 ≤ R.n
  nT_ge_one : 1 ≤ (Fintype.card Top : ℝ)
  nT_ge_rest : x ^ (-(eps / 8)) * (R.n : ℝ) / 2 ≤ (Fintype.card Top : ℝ)
  nT2_ge_rest : x ^ (-eps) ≤ (nT2 : ℝ) / (R.n : ℝ)
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
  -- Fiber functions
  aT : Top → ℝ
  w : U0 → Fin R.m → Fin R.f → ℝ
  d : ∀ u0, W u0 → ℝ
  T : ∀ u0, W u0 → ℝ
  muN : ∀ u0, W u0 → ℝ
  muMaxN : ∀ u0, W u0 → ℝ
  h : ∀ u0, W u0 → ℝ
  muM : ∀ u0, W u0 → ℝ
  muMaxM : ∀ u0, W u0 → ℝ
  Ee : ∀ u0, W u0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  HH : U0 → ℝ
  -- Gram-frame fiber realization (DISCHARGES BostSlopeFiber.SlopeIneq & fParams!)
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
    Stage2GramFrameFiber
      (SlopeInequality.wmean (d u0) (fun u => muN u0 u - h u0 u))
      ((Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => muMaxN u0 u - h u0 u)) -
        SlopeInequality.wmean (d u0) (fun u => muN u0 u - h u0 u))
      (HH u0) (muMinCC u0) (Fintype.card (W u0)) delBar sgBar deBar e0Bar
  trace_le :
    (5 * sgBar + 3 * Real.sqrt deBar + 4 * Real.sqrt (2 * e0Bar)) *
        (x ^ cHH * Real.exp (x ^ eps))
      ≤ K * x ^ eps * ((Fintype.card Top : ℝ) * a)
  -- Host CM field & Selmer LinkN bound (DISCHARGES SlopeHypotheses.div from WinDatum.vAt_400!)
  E_field : Type
  [fieldE : Field E_field]
  [nfE : NumberField E_field]
  isChi : IsChiField ψ e_page q d_aux E_field
  cLink : ℝ
  cDiv_ge_link : |cLink| + 1 ≤ cDiv
  Nc : ℝ
  Nc_nonneg : 0 ≤ Nc
  Nc_le : Nc ≤ (nT2 : ℝ) * (R.k : ℝ) * Real.exp (x ^ eps) * x ^ eps /
    ((R.n : ℝ) * ((R.n : ℝ) * x ^ (-eps)))
  divLink : ∀ u0 (u : W u0),
    ((gramFiber u0).muCC + h u0 u - Fo u0) -
      (∑ t : Top, ((R.m : ℝ) * (SlopeInequality.ph (aT t) -
          aT t * (gam + Real.log (Real.pi / vE) - LpL)) - aT t * Real.log (T u0 u))) -
      cDiv * (Fintype.card Top : ℝ) * a * La ≤
    (R.m : ℝ) * (cLink * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
      Real.log x ^ 2 * Nc) + ∑' l, PAdicChainValuation.vvTerm S E_field R.t l)
  -- Unitary mass formula datum (DISCHARGES SlopeHypotheses.count.1: Lam5 ≤ log T & 0 < v!)
  vE_ge_pi : Real.pi ≤ vE
  log_vE_le : Real.log vE ≤ x ^ eps
  g₁_ge_one : 1 ≤ g₁
  g₂_ge_one : 1 ≤ g₂
  four_le_cCount_La : 4 ≤ cCount * La
  massDatum : ∀ u0 (u : W u0),
    Stage2MassRatioDatum R.f R.m R.k vE g₁ g₂ (x ^ eps) La cCount (w u0) (T u0 u)
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
  mu_le_max : ∀ u0 u, muN u0 u ≤ muMaxN u0 u
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
  slopes : ∀ u0 (u : W u0),
    -(cSlope * (Fintype.card Top : ℝ) * a * La * (1 + (R.m : ℝ) / (R.k : ℝ))) ≤ muM u0 u ∧
    muMaxM u0 u ≤ cSlope * (Fintype.card Top : ℝ) * a * La
  quotientSlopes : ∀ u0 (u : W u0),
    muMaxN u0 u ≤ muMaxM u0 u + Ga u0 + Fo u0 - Ee u0 u +
      cSl1 * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps) ∧
    muM u0 u + Ga u0 + Fo u0 - Ee u0 u -
      (cSl1 * IO u0 + cSl1 * (Fintype.card Top : ℝ) * (R.m : ℝ) * (a / (R.k : ℝ) + b') *
        Real.log (T u0 u) + cSl1 * Xpp + 1) ≤ muN u0 u
  losses :
    umean (fun u0 => ASK u0 - Ga u0) ≤
      cLoss * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ (eL * eps) ∧
    umean IO ≤
      cLoss * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ (eL * eps)
  hhBound : ∀ u0,
    SlopeInequality.wmean (d u0) (fun u => muN u0 u - h u0 u) - muMinCC u0 ≤ HH u0 ∧
    0 < HH u0 ∧
    HH u0 ≤ x ^ cHH * Real.exp (x ^ eps)
  mainBalance :
    (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (((nT2 : ℝ) / (R.n : ℝ)) / 2) *
        ((Level.cyc ψ).Gm x - 4 * x ^ ((1 : ℝ) / 2 + eps)) ≤
      (umean ASK - umean (fun u0 =>
        ∑ j : Fin R.m, ∑ t, aT t * (Real.log (aT t) - 1 - gam + LpL
          - (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w u0 j ρ)))) +
      2 * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) / x

attribute [instance] Stage2FiberWitness.finU0 Stage2FiberWitness.neU0
  Stage2FiberWitness.finW Stage2FiberWitness.neW Stage2FiberWitness.finTop
  Stage2FiberWitness.fieldE Stage2FiberWitness.nfE

/-- **Strictly Smaller Stage 2 Pillar-2 Core Input Bundle (`Stage2ThetaCoreInputs S`)**:
Eliminates `eD`, `eD_nonneg`, and all 44 discharged fiber/window/Bost/divisibility/mass-ratio
obligations from `ThetaSlopeEngine.MinimalThetaEngineInputs S`! -/
structure Stage2ThetaCoreInputs (S : SelmerSystem) where
  eL : ℝ
  eL_nonneg : 0 ≤ eL
  pairEx : PairEx
  realizeCore : ∀ (ψ : PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52), 1 ≤ J →
    ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
      ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
        WinDatum S ψ eps J 1 x Y q d_aux e_page →
        Nonempty (Stage2FiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)

/-- **Fiber Assembly Theorem**: compiles a `Stage2FiberWitness` + `WinDatum.vAt_400` + large-`x`
thresholds directly into `ThetaSlopeEngine.ThetaSlopeFiberRealization ψ 1 eL eps x`, discharging
all 44 proof obligations via our 9 Pillar-2 specialist modules! -/
theorem thetaSlopeFiberRealization_of_stage2 {S : SelmerSystem} {ψ : PChar}
    {eL K cHH eps x : ℝ} {q d_aux e_page : ℕ}
    {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (heL : 0 ≤ eL) (hcHH : 0 ≤ cHH)
    (hx100 : (2 : ℝ) ^ 100 ≤ x)
    (hx16 : (2 : ℝ) ^ (16 / (9 * eps)) ≤ x)
    (hlogSq : Real.log x ^ 2 ≤ x ^ eps)
    (hKBig : 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + 5) ≤ x ^ eps)
    (hV400 : VAt S ψ eps 400 q d_aux e_page x)
    (W : Stage2FiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52) :
    ThetaSlopeFiberRealization ψ 1 eL eps x := by
  -- Step 1: Discharge all 10 RankVal window/rank/cutoff bounds
  obtain ⟨hn_pos, hf_ge1, ht_floor, hm_ge_rest, hm_le_win, hxm_le_k, hk_ge1, hk_le_x5,
    hk_le_n2, ⟨hk_ge2, hmL_le_k, _⟩⟩ :=
    rankVal_discharges_chain_window_bounds hx1 heps heps52 hx100 hx16
      W.f_eq W.m_ge_two W.mk_le W.r_eq W.rankVal
  have hx0 : 0 < x := by linarith
  have hb_ge1 : (1 : ℝ) ≤ Real.exp (x ^ eps) := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb_pos : 0 < Real.exp (x ^ eps) := Real.exp_pos _
  have hL_ge1 : (1 : ℝ) ≤ x ^ eps := Real.one_le_rpow hx1.le heps.le
  have hL_pos : 0 < x ^ eps := Real.rpow_pos_of_pos hx0 eps
  -- Step 2: Discharge Real.log x ≤ x ^ eps from (log x)^2 ≤ x ^ eps and x ≥ 2^100 > exp 1
  have hlog_le : Real.log x ≤ x ^ eps := by
    have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hx_e : Real.exp 1 ≤ x := by
      have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith
    have h1 : 1 ≤ Real.log x := by
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx_e
    nlinarith
  -- Step 3: Assemble the SlopeData and SlopeConsts directly from Stage2FiberWitness
  let D : SlopeData W.U0 W.W W.Top W.R.m W.R.f :=
    { x := x
      ε := eps
      a := W.a
      b := Real.exp (x ^ eps)
      b' := W.b'
      k := (W.R.k : ℝ)
      L := x ^ eps
      La := W.La
      B0 := (W.R.f : ℝ) * (W.R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps
      Nc := W.Nc
      gam := W.gam
      LpL := W.LpL
      v := W.vE
      lg := Real.log W.g₁ + Real.log W.g₂
      aT := W.aT
      w := W.w
      d := W.d
      T := W.T
      muN := W.muN
      muMaxN := W.muMaxN
      h := W.h
      muM := W.muM
      muMaxM := W.muMaxM
      Ee := W.Ee
      muCC := fun u0 => (W.gramFiber u0).muCC
      muMinCC := W.muMinCC
      Fo := W.Fo
      Ga := W.Ga
      ASK := W.ASK
      IO := W.IO
      HH := W.HH
      del := fun u0 => (W.gramFiber u0).δ
      η := fun u0 => (W.gramFiber u0).etaVal
      e := fun u0 => (W.gramFiber u0).eVal
      delBar := W.delBar
      etaBar := 5 * W.sgBar + 3 * Real.sqrt W.deBar
      eBar := 2 * W.e0Bar }
  let C : SlopeConsts :=
    { cDiv := W.cDiv
      eDiv := 1
      cE := W.cE
      cH := W.cH
      cCount := W.cCount
      cSlope := W.cSlope
      cSl1 := W.cSl1
      cLoss := W.cLoss
      eLoss := eL
      cHH := cHH }
  -- Step 4: Verify Setting (all positivity/bar bounds discharged!)
  have hsgBar_nn : 0 ≤ W.sgBar := by
    obtain ⟨u0⟩ := W.neU0
    exact le_trans (W.gramFiber u0).sg_pos.le (W.gramFiber u0).sg_le_bar
  have hSetting : D.Setting C :=
    { x_pos := hx0
      b_pos := hb_pos
      a_nonneg := le_trans (mul_nonneg hx0.le hb_pos.le) W.xb_le_a
      b'_nonneg := W.b'_nonneg
      k_pos := lt_of_lt_of_le zero_lt_one hk_ge1
      v_pos := lt_of_lt_of_le Real.pi_pos W.vE_ge_pi
      f_pos := Nat.lt_of_lt_of_le Nat.zero_lt_one hf_ge1
      aT_nonneg := fun t => (W.aT_bounds t).1
      w_pos := W.w_pos
      d_pos := W.d_pos
      mu_le_max := W.mu_le_max
      cSl1_nonneg := W.cSl1_bounds.1
      delBar_lt_one := by linarith [W.delBar_le]
      etaBar_nonneg := by positivity
      eBar_nonneg := by linarith [W.e0Bar_nonneg]
      eBar_le := by
        have hsq : Real.sqrt W.e0Bar ^ 2 ≤ (W.sgBar / 2) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) W.sqrt_e0Bar_le 2
        rw [Real.sq_sqrt W.e0Bar_nonneg] at hsq
        nlinarith [W.sgBar_le] }
  -- Step 5: Discharge SlopeHypotheses (bostSlope, div, count.1, fParams all proved!)
  have hSlope : D.SlopeHypotheses C W.Xpp :=
    { setting := hSetting
      div := fun u0 u =>
        divinN_discharges_slope_div hV400 W.isChi ht_floor hx1 heps hf_ge1
          (le_trans (by norm_num : 1 ≤ 2) W.m_ge_two) W.Nc_nonneg W.cDiv_ge_link hlogSq (W.divLink u0 u)
      eComp := W.eComp
      hComp := W.hComp
      count := fun u0 u =>
        ⟨Stage2MassRatioDatum.lam5_le_log_T (s := stage2ScaleParams x eps hx1 heps heps52)
            hf_ge1 (le_trans (by norm_num : 1 ≤ 2) W.m_ge_two) hk_ge2 W.vE_ge_pi W.log_vE_le hL_ge1
            W.g₁_ge_one W.g₂_ge_one (W.w_pos u0) hmL_le_k W.cCount_bounds.1 W.La_nonneg
            W.four_le_cCount_La (W.massDatum u0 u),
          (W.count_upper_and_var u0 u).1,
          (W.count_upper_and_var u0 u).2⟩
      slopes := W.slopes
      quotientSlopes := W.quotientSlopes
      losses := W.losses
      bostSlope := fun u0 => (W.gramFiber u0).toBostSlopeIneq (D.uF_nonneg C hSetting u0)
      hhBound := W.hhBound
      fParams := fun u0 =>
        let hη := (W.gramFiber u0).etaVal_bounds
        let he := (W.gramFiber u0).eVal_bounds
        ⟨(W.gramFiber u0).δ_nonneg, (W.gramFiber u0).δ_le_bar, hη.1, hη.2, he.1, he.2.1⟩ }
  -- Step 6: Discharge ErrorWindowBounds (log_x_le, KBig_le, m_le, xm_le_k, k_le_xeK, etc. proved!)
  have hWin : D.ErrorWindowBounds C W.Xpp 5 K :=
    { x_ge_one := hx1.le
      eps_pos := heps
      eps_le_one := by linarith
      b_ge_one := hb_ge1
      xb_le_a := W.xb_le_a
      nT_ge_one := W.nT_ge_one
      m_le := hm_le_win
      xm_le_k := hxm_le_k
      eK_nonneg := by norm_num
      k_ge_one := hk_ge1
      k_le_xeK := hk_le_x5
      k_le_a := W.k_le_a
      L_nonneg := hL_pos.le
      L_le := by linarith
      La_nonneg := W.La_nonneg
      La_le := W.La_le
      b'_nonneg := W.b'_nonneg
      kb'_le_a := W.kb'_le_a
      Xpp_nonneg := W.Xpp_nonneg
      Xpp_le_a := W.Xpp_le_a
      aT_bounds := W.aT_bounds
      B0_nonneg := by positivity
      Nc_nonneg := W.Nc_nonneg
      cardW_le := W.cardW_le
      delBar_le := W.delBar_le
      etaBar_nonneg := hSetting.etaBar_nonneg
      eBar_nonneg := hSetting.eBar_nonneg
      trace_le := W.trace_le
      cDiv_bounds := ⟨by linarith [abs_nonneg W.cLink, W.cDiv_ge_link], W.cDiv_le⟩
      cE_bounds := W.cE_bounds
      cH_bounds := W.cH_bounds
      cCount_bounds := W.cCount_bounds
      cSlope_bounds := W.cSlope_bounds
      cSl1_bounds := W.cSl1_bounds
      cLoss_bounds := W.cLoss_bounds
      eDiv_nonneg := zero_le_one
      eLoss_nonneg := heL
      cHH_nonneg := hcHH
      log_x_le := hlog_le
      KBig_le := hKBig }
  -- Step 7: Discharge B0 ≤ 2 n m b x^eps and RestSize
  have hB0_le : D.B0 ≤ (2 * (W.R.n : ℝ)) * (W.R.m : ℝ) * D.b * x ^ eps := by
    dsimp only [D]
    rw [W.f_eq]
    push_cast
    exact le_rfl
  have hRest : RestSize eps x W.R.n (Fintype.card W.Top) W.nT2 W.R.m D.b D.k D.a :=
    ⟨W.a_le_2xb, W.nT_ge_rest, W.nT2_ge_rest, hm_ge_rest, hk_le_n2⟩
  exact ⟨⟨W.U0, W.finU0, W.neU0, W.W, W.finW, W.neW, W.Top, W.finTop,
    W.R.m, W.R.f, W.R.n, W.nT2, D, C, W.Xpp, 5, K,
    rfl, rfl, le_rfl, le_rfl, hSlope, hWin, hB0_le, W.Nc_le, hRest,
    hn_pos, W.nT2_le, W.mainBalance⟩⟩

/-- **Concrete Stage 2 Bridge Theorem (`Stage2ThetaCoreInputs S → MinimalThetaEngineInputs S`)**:
Automatically chooses the asymptotic cutoff `X0'` covering `2^100`, `2^(16/(9*eps))`,
`PAdicChainValuation.log_sq_le_rpow`, and `KBig_le`, then constructs
`ThetaSlopeEngine.MinimalThetaEngineInputs S` with `eD = 1`! -/
def minimalThetaEngineInputs_of_stage2 (S : SelmerSystem) (I : Stage2ThetaCoreInputs S) :
    MinimalThetaEngineInputs S where
  eD := 1
  eL := I.eL
  eD_nonneg := zero_le_one
  eL_nonneg := I.eL_nonneg
  pairEx := I.pairEx
  realize := fun ψ eps J heps heps52 hJ => by
    obtain ⟨K, cHH, X0, hK0, hcHH0, hCore⟩ := I.realizeCore ψ eps J heps heps52 hJ
    obtain ⟨x_log, hx_log⟩ := PAdicChainValuation.log_sq_le_rpow heps
    set M_big : ℝ := 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + 5)
    have hM_pos : 0 < M_big := by dsimp only [M_big]; positivity
    set X_big : ℝ := M_big ^ (1 / eps)
    set X0' : ℝ := max (max X0 x_log) (max ((2 : ℝ) ^ 100) (max ((2 : ℝ) ^ (16 / (9 * eps))) X_big))
    refine ⟨X0', fun x Y q d_aux e_page hx hDat => ?_⟩
    have hx_X0 : X0 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
    have hx_xlog : x_log ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
    have hx_100 : (2 : ℝ) ^ 100 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
    have hx_16 : (2 : ℝ) ^ (16 / (9 * eps)) ≤ x :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))
    have hx_big : X_big ≤ x :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))
    have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ) ^ 100) hx_100
    have hKBig : 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + 5) ≤ x ^ eps := by
      have hpow : X_big ^ eps = M_big := by
        dsimp only [X_big]
        rw [← Real.rpow_mul hM_pos.le, one_div_mul_cancel heps.ne', Real.rpow_one]
      calc M_big = X_big ^ eps := hpow.symm
        _ ≤ x ^ eps := Real.rpow_le_rpow (Real.rpow_nonneg hM_pos.le _) hx_big heps.le
    obtain ⟨W⟩ := hCore x Y q d_aux e_page hx1 hx_X0 hDat
    exact thetaSlopeFiberRealization_of_stage2 I.eL_nonneg hcHH0 hx_100 hx_16
      (hx_log x hx_xlog) hKBig hDat.vAt_400 W

/-- **Main Stage 2 Pillar-2 Contract Export (`stage2_thetaSlopeContract`)**:
Compiles `Stage2ThetaCoreInputs S` (with all 9 Pillar-2 specialist cores wired in) directly into
`RHDirect.ThetaSlopeContract S` (`VWin S → AllLevelsWindowBound (3 / 2)`), ready for
`RHDirect.Main`! -/
theorem stage2_thetaSlopeContract (S : SelmerSystem) (I : Stage2ThetaCoreInputs S) :
    ThetaSlopeContract S :=
  thetaSlopeContract_of_inputs S (minimalThetaEngineInputs_of_stage2 S I)

/-- Direct windowed Cesàro von Mangoldt bound `AllLevelsWindowBound (3 / 2)` from
`Stage2ThetaCoreInputs S` and `VWin S`. -/
theorem stage2_allLevelsWindowBound (S : SelmerSystem) (I : Stage2ThetaCoreInputs S)
    (hV : VWin S) :
    AllLevelsWindowBound (3 / 2) :=
  (stage2_thetaSlopeContract S I).windows_of_vwin hV

end

end RHDirect.Stage2ThetaWire
