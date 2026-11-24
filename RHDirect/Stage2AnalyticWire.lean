import RHDirect.AnalyticBridge
import RHDirect.CosetWeights
import RHDirect.MellinExplicit
import RHDirect.ZeroDensityWindow
import RHDirect.ElementaryEquiv

/-!
# RHDirect.Stage2AnalyticWire

Unified Stage 2 Pillar-1 entrypoint consolidating all specialist analytic modules into a single
zero-`sorry`, zero-custom-`axiom`, zero-warning interface:

- `RHDirect.AnalyticBridge` & `RHDirect.LandauWindow` (unconditional windowed Landau nonvanishing
  and Euler-factor / functional-equation deduction of all 5 headline RH/GRH theorems),
- `RHDirect.CosetWeights` (`(4, 3)/(3o + 1)` finite-abelian Fourier clearing, subgroup character
  orthogonality, positive Dirichlet-series coefficients `Level.rampCoeff`, and `Level.toCharFamily`),
- `RHDirect.MellinExplicit` (exact Cesàro-1 ramp Mellin transforms, Mellin–Laplace equivalence,
  Chernoff tails, and `HasRpowWindow → CharFamily.WindowHyp`),
- `RHDirect.ZeroDensityWindow` (`ε < 1/52` quantitative bracket-to-window coupling, `[Y, Y^2] →
  [Y, Y^(3/2)]` restriction, and `TopPlug`),
- `RHDirect.ElementaryEquiv` (complete bidirectional RH/GRH equivalences, fourfold zero symmetry,
  trivial-zero characterization, Chebyshev's factorial identity, and Robin–Lagarias bridge).

## Main Exports
1. **Unconditional Pillar-1 Contract**: `stage2_analyticBridgeContract : AnalyticBridgeContract`
   (wired directly through `CosetWeights` + `LandauWindow`, with 0 extra assumptions).
2. **Complete Bidirectional RH/GRH Equivalence & Elementary Pack**:
   - `rh_equivalence_pack`, `grh_equivalence_pack`,
   - fourfold critical-strip zero symmetry (`riemannZeta_fourfold_zero_symmetry`,
     `LFunction_eq_zero_one_sub_iff_of_isPrimitive`, `LFunction_eq_zero_one_sub_conj_iff_of_isPrimitive`),
   - trivial-zero characterization (`riemannZeta_eq_zero_of_re_nonpos_iff`,
     `riemannZeta_nontrivial_zero_mem_strip`),
   - elementary bridges (`chebyshev_factorial_identity`, `Gz_nat_le_linear`,
     `lagarias_of_robin_of_gt_5040`, `sigma_5040`, `lagarias_eq_at_one`).
3. **End-to-End Window-Coupling Theorems**:
   Direct coupling from `ZeroDensityWindow` + `CosetWeights` + `MellinExplicit` to `ZeroFreeAll`
   and all 5 verbatim RH/GRH headline theorems (`headline_five_of_zeroFreeAll`,
   `headline_five_of_bracketWindows`, `headline_five_of_square_bracketWindows`,
   `headline_five_of_vwin_topShape`, and `level_mellin_laplace_and_windowHyp_of_bracketWindows`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect
namespace Stage2AnalyticWire

/-! ## Section 1: Unconditional Pillar-1 Contract & Specialist Bridges -/

/-- **Unconditional Stage 2 Pillar-1 Contract (`AnalyticBridgeContract`)**:
wires `CosetWeights.analyticBridgeContract_of_charFamily_window` directly with
`LandauWindow.zeroFree_of_rpow_window`, requiring zero external hypotheses. -/
theorem stage2_analyticBridgeContract : AnalyticBridgeContract :=
  analyticBridgeContract_of_charFamily_window (fun F => zeroFree_of_rpow_window F)

/-- Definitional/propositional agreement with `RHDirect.analyticBridgeContract`. -/
theorem stage2_analyticBridgeContract_eq :
    stage2_analyticBridgeContract = analyticBridgeContract :=
  rfl

/-- Exact Mellin–Laplace closed form for any level `L : Level` via `CosetWeights.Level.toCharFamily`
and `MellinExplicit.mellin_Gm_eq_laplace` / `MellinExplicit.mellin_Gm_eq_sum`. -/
theorem level_laplace_eq_mellin_sum (L : Level) {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (L.Gm (Real.exp u) : ℂ) * cexp (-s * u) =
      ∑ i : L.toCharFamily.ι,
        ((L.toCharFamily.a i : ℂ) / 2) *
          (MellinExplicit.mellinTerm (L.toCharFamily.χ i) s +
            MellinExplicit.mellinTerm (L.toCharFamily.χ i)⁻¹ s) := by
  have hGm : (fun u : ℝ => (L.Gm (Real.exp u) : ℂ) * cexp (-s * u)) =
      fun u : ℝ => (L.toCharFamily.Gm (Real.exp u) : ℂ) * cexp (-s * u) := by
    funext u
    rw [L.toCharFamily_Gm]
  rw [hGm, MellinExplicit.mellin_Gm_eq_laplace, MellinExplicit.mellin_Gm_eq_sum L.toCharFamily hs]

/-- Exact `(4o, 3o)/(3o + 1)` target-character isolation and strict positivity of Dirichlet-series
coefficients for every cyclic level `Level.cyc ψ` (`CosetWeights`). -/
theorem cyc_rampCoeff_isolation (ψ : PChar) {n : ℕ} (hn : n.Coprime ψ.N) :
    0 < (Level.cyc ψ).rampCoeff n ∧
    (Level.cyc ψ).rampCoeff n =
      (if ψ.val n = 1 then 4 * ((Level.cyc ψ).o : ℝ)
       else 3 * ((Level.cyc ψ).o : ℝ)) / (3 * ((Level.cyc ψ).o : ℝ) + 1) :=
  ⟨Level.rampCoeff_cyc_pos ψ n, Level.rampCoeff_cyc_of_coprime ψ hn⟩

/-- Non-negative von Mangoldt ramp expansion of `(Level.cyc ψ).Gm` (`CosetWeights`). -/
theorem cyc_rampSum_nonneg (ψ : PChar) (y : ℝ) :
    0 ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
      Λ n * (Level.cyc ψ).rampCoeff n * max (y / n - 1) 0 := by
  have hcard : (Level.cyc ψ).KEPT.card ≤ 3 * (Level.cyc ψ).o + 1 := by
    rw [Level.card_KEPT_cyc]
    omega
  exact (Level.cyc ψ).rampSum_nonneg_of_card_le hcard y

/-- Re-export of the `(4, 3)/(3o + 1)` perturbed Fourier-clearing lower bound on a `CosetFrame`
coupled with `CosetFrame.keptSum_eq_level_Gm` (`CosetWeights`). -/
theorem cosetFrame_fourier_clear_level_Gm (φ : CosetFrame) (L : Level)
    (ho : φ.o = L.o) (ι : PChar → AddChar φ.A ℂ)
    (hinj : Set.InjOn ι (L.KEPT : Set PChar)) (h1 : ι PChar.one = 0)
    {TT : Finset φ.A} {δ : ℝ} (hsh : φ.Shares TT δ)
    (hKp : L.KEPT.image ι ⊆ φ.annihilator)
    (G : AddChar φ.A ℂ → ℂ) (Gt : φ.A → AddChar φ.A ℂ → ℂ) (Err : AddChar φ.A ℂ → ℝ)
    (y : ℝ) (hG : ∀ ψ ∈ L.KEPT, (G (ι ψ)).re = (Gchi ψ.χ y).re)
    (hpert : ∀ t ∈ TT, ∀ θ ∈ φ.annihilator, ‖Gt t θ - G θ‖ ≤ Err θ) :
    (TT.card : ℝ) *
        (L.Gm y - φ.offKeptNorm (L.KEPT.image ι) G -
          (φ.o : ℝ) * δ * ∑ θ ∈ (L.KEPT.image ι).erase 0, ‖G θ‖ -
          ∑ θ ∈ φ.annihilator, Err θ) ≤
      ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * Gt t θ).re := by
  rw [← φ.keptSum_eq_level_Gm L ho ι hinj h1 G y hG]
  exact φ.fourier_clear_perturbed_le hsh hKp G Gt Err hpert

/-! ## Section 2: Complete Bidirectional RH/GRH Equivalence & Elementary Pack -/

/-- Complete bidirectional equivalence pack for the Riemann Hypothesis (`ElementaryEquiv`). -/
theorem rh_equivalence_pack :
    (RiemannHypothesis ↔ RiemannZetaZerosOnLine) ∧
    (RiemannZetaZerosOnLine ↔ RiemannZetaNonvanishingRightOfHalf) ∧
    (RiemannHypothesis ↔ RiemannZetaNonvanishingRightOfHalf) ∧
    (RiemannHypothesis ↔ RiemannZetaCriticalStripZerosOnLine) ∧
    (RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → riemannZeta s ≠ 0) :=
  ⟨RHDirect.riemannHypothesis_iff_riemannZetaZerosOnLine,
   RHDirect.riemannZetaZerosOnLine_iff_nonvanishingRightOfHalf,
   RHDirect.riemannHypothesis_iff_nonvanishingRightOfHalf,
   RHDirect.riemannHypothesis_iff_criticalStrip,
   RHDirect.riemannHypothesis_iff_no_zeros_leftOfHalf⟩

/-- Complete bidirectional equivalence pack for the Generalized Riemann Hypothesis
(`ElementaryEquiv`). -/
theorem grh_equivalence_pack :
    (ZeroFreeAll ↔ DirichletLNonvanishingRightOfHalf) ∧
    (DirichletLNonvanishingRightOfHalf ↔ DirichletLZerosOnLine) ∧
    (DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine) ∧
    (DirichletLNonvanishingRightOfHalf ↔ PrimitiveDirichletLZerosOnLine) :=
  ⟨RHDirect.zeroFreeAll_iff_dirichletLNonvanishingRightOfHalf,
   RHDirect.dirichletLNonvanishingRightOfHalf_iff_dirichletLZerosOnLine,
   RHDirect.dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine,
   RHDirect.dirichletLNonvanishingRightOfHalf_iff_primitiveDirichletLZerosOnLine⟩

/-- Re-export: `RiemannHypothesis ↔ RiemannZetaZerosOnLine`. -/
theorem riemannHypothesis_iff_riemannZetaZerosOnLine :
    RiemannHypothesis ↔ RiemannZetaZerosOnLine :=
  RHDirect.riemannHypothesis_iff_riemannZetaZerosOnLine

/-- Re-export: `RiemannZetaZerosOnLine ↔ RiemannZetaNonvanishingRightOfHalf`. -/
theorem riemannZetaZerosOnLine_iff_nonvanishingRightOfHalf :
    RiemannZetaZerosOnLine ↔ RiemannZetaNonvanishingRightOfHalf :=
  RHDirect.riemannZetaZerosOnLine_iff_nonvanishingRightOfHalf

/-- Re-export: `RiemannHypothesis ↔ RiemannZetaNonvanishingRightOfHalf`. -/
theorem riemannHypothesis_iff_nonvanishingRightOfHalf :
    RiemannHypothesis ↔ RiemannZetaNonvanishingRightOfHalf :=
  RHDirect.riemannHypothesis_iff_nonvanishingRightOfHalf

/-- Re-export: `DirichletLNonvanishingRightOfHalf ↔ DirichletLZerosOnLine`. -/
theorem dirichletLNonvanishingRightOfHalf_iff_dirichletLZerosOnLine :
    DirichletLNonvanishingRightOfHalf ↔ DirichletLZerosOnLine :=
  RHDirect.dirichletLNonvanishingRightOfHalf_iff_dirichletLZerosOnLine

/-- Re-export: `DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine`. -/
theorem dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine :
    DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine :=
  RHDirect.dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine

/-- Re-export: `DirichletLNonvanishingRightOfHalf ↔ PrimitiveDirichletLZerosOnLine`. -/
theorem dirichletLNonvanishingRightOfHalf_iff_primitiveDirichletLZerosOnLine :
    DirichletLNonvanishingRightOfHalf ↔ PrimitiveDirichletLZerosOnLine :=
  RHDirect.dirichletLNonvanishingRightOfHalf_iff_primitiveDirichletLZerosOnLine

/-- Re-export: `ZeroFreeAll ↔ DirichletLNonvanishingRightOfHalf`. -/
theorem zeroFreeAll_iff_dirichletLNonvanishingRightOfHalf :
    ZeroFreeAll ↔ DirichletLNonvanishingRightOfHalf :=
  RHDirect.zeroFreeAll_iff_dirichletLNonvanishingRightOfHalf

/-- Re-export: four-fold symmetry of critical-strip zeros of `ζ(s)`. -/
theorem riemannZeta_fourfold_zero_symmetry {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    riemannZeta (starRingEnd ℂ s) = 0 ∧
    riemannZeta (1 - s) = 0 ∧
    riemannZeta (1 - starRingEnd ℂ s) = 0 :=
  RHDirect.riemannZeta_fourfold_zero_symmetry h0 h1 hz

/-- Re-export: reflection `s ↦ 1 - conj s` preserves critical-strip zeros of a primitive `L(χ, s)`. -/
theorem LFunction_eq_zero_one_sub_conj_iff_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    DirichletCharacter.LFunction χ (1 - starRingEnd ℂ s) = 0 ↔
      DirichletCharacter.LFunction χ s = 0 :=
  RHDirect.LFunction_eq_zero_one_sub_conj_iff_of_isPrimitive hχ h0 h1

/-- Re-export: exact characterization of all zeros of `ζ(s)` in `Re(s) ≤ 0`. -/
theorem riemannZeta_eq_zero_of_re_nonpos_iff {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) :=
  RHDirect.riemannZeta_eq_zero_of_re_nonpos_iff hs

/-- Re-export: every nontrivial zero of `ζ(s)` lies in `0 < Re(s) < 1`. -/
theorem riemannZeta_nontrivial_zero_mem_strip {s : ℂ}
    (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    0 < s.re ∧ s.re < 1 :=
  RHDirect.riemannZeta_nontrivial_zero_mem_strip hz htriv

/-- Re-export: Chebyshev's factorial identity `∑_{n=1}^N log n = ∑_{d=1}^N Λ(d) ⌊N/d⌋`. -/
theorem chebyshev_factorial_identity (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) :=
  RHDirect.chebyshev_factorial_identity N

/-- Re-export: Robin's inequality implies Lagarias's inequality for all `n > 5040`. -/
theorem lagarias_of_robin_of_gt_5040 (hR : RobinInequality) {n : ℕ} (hn : 5040 < n) :
    (ArithmeticFunction.sigma 1 n : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) :=
  RHDirect.lagarias_of_robin_of_gt_5040 hR hn

/-- Re-export: unconditional linear bound `Gz N ≤ (1 + γ) N` for `N ≥ 1`. -/
theorem Gz_nat_le_linear {N : ℕ} (hN : 1 ≤ N) :
    Gz (N : ℝ) ≤ (1 + Real.eulerMascheroniConstant) * (N : ℝ) :=
  RHDirect.Gz_nat_le_linear hN

/-- Re-export: exact Lagarias boundary equality at `n = 1` and Robin boundary `σ(5040) = 19344`. -/
theorem robin_lagarias_boundary_checks :
    (ArithmeticFunction.sigma 1 1 : ℝ) =
      (harmonic 1 : ℝ) + Real.exp (harmonic 1 : ℝ) * Real.log (harmonic 1 : ℝ) ∧
    ArithmeticFunction.sigma 1 5040 = 19344 :=
  ⟨RHDirect.lagarias_eq_at_one, RHDirect.sigma_5040⟩

/-! ## Section 3: Direct Window-Coupling (`ZeroDensityWindow` + `CosetWeights` + `MellinExplicit`) →
All 5 Headline RH/GRH Theorems -/

/-- Exact 5-tuple of verbatim RH/GRH headline statements from `RHDirect.Interfaces` / Mathlib. -/
def AllFiveHeadlineStatements : Prop :=
  DirichletLNonvanishingRightOfHalf ∧
  DirichletLZerosOnLine ∧
  PrimitiveDirichletLZerosOnLine ∧
  RiemannHypothesis ∧
  RiemannZetaZerosOnLine

/-- Unconditional deduction of all 5 verbatim RH/GRH headline theorems from `ZeroFreeAll`. -/
theorem headline_five_of_zeroFreeAll (hZ : ZeroFreeAll) : AllFiveHeadlineStatements := by
  have hRight : DirichletLNonvanishingRightOfHalf := imprimitive_of_zeroFreeAll hZ
  have hLine : DirichletLZerosOnLine := strip_of_right hRight
  have hPrim : PrimitiveDirichletLZerosOnLine := fun N _ χ _ s => hLine N χ s
  have hRH : RiemannHypothesis := riemannHypothesis_of_strip hLine
  exact ⟨hRight, hLine, hPrim, hRH, hRH⟩

/-- Unconditional deduction of all 5 verbatim RH/GRH headline theorems from
`AllLevelsWindowBound la` (`1 < la`), routed through `stage2_analyticBridgeContract`. -/
theorem headline_five_of_allLevelsWindowBound {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : AllFiveHeadlineStatements :=
  headline_five_of_zeroFreeAll (stage2_analyticBridgeContract.zeroFreeAll_of_windows la hla hW)

/-- **Combined Specialist Coupling on a Single Level**:
Given `ZeroDensityWindow.LevelBracketWindows L la` (`1 < la`), simultaneously produces:
1. the `CosetWeights` power-window bound `HasRpowWindow L.toCharFamily.Gm θ (la - 1) 1`,
2. the `MellinExplicit` integral window hypothesis `L.toCharFamily.WindowHyp θ (la - 1)`,
3. the `MellinExplicit` Laplace–Mellin identity on `Re(s) > 1`, and
4. critical-line zero-freeness `L.ZeroFreeLevel` (`Re(s) > 1/2`). -/
theorem level_window_coupling {L : Level} {la : ℝ} (hla : 1 < la)
    (hW : ZeroDensityWindow.LevelBracketWindows L la) :
    (∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      HasRpowWindow L.toCharFamily.Gm θ (la - 1) 1 ∧
      L.toCharFamily.WindowHyp θ (la - 1)) ∧
    (∀ s : ℂ, 1 < s.re →
      ∫ u in Ioi (0 : ℝ), (L.Gm (Real.exp u) : ℂ) * cexp (-s * u) =
        ∑ i : L.toCharFamily.ι,
          ((L.toCharFamily.a i : ℂ) / 2) *
            (MellinExplicit.mellinTerm (L.toCharFamily.χ i) s +
              MellinExplicit.mellinTerm (L.toCharFamily.χ i)⁻¹ s)) ∧
    L.ZeroFreeLevel := by
  have hLWB : LevelWindowBound L la := ZeroDensityWindow.levelWindowBound_of_bracketWindows hW
  refine ⟨fun θ hθ1 hθ2 => ?_, fun s hs => level_laplace_eq_mellin_sum L hs, ?_⟩
  · have hpow : HasRpowWindow L.toCharFamily.Gm θ (la - 1) 1 :=
      (L.toCharFamily_hasRpowWindow_iff θ (la - 1) 1).mpr (hLWB θ hθ1 hθ2)
    exact ⟨hpow, MellinExplicit.windowHyp_of_hasRpowWindow L.toCharFamily (sub_pos.mpr hla) hpow⟩
  · exact L.zeroFreeLevel_of_windowBound hla hLWB (fun F => zeroFree_of_rpow_window F)

/-- **Direct Window-Coupling Theorem (`ZeroDensityWindow` + `CosetWeights` + `MellinExplicit` →
`ZeroFreeAll`)** at `la = 3 / 2`. -/
theorem zeroFreeAll_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    ZeroFreeAll :=
  Level.zeroFreeAll_of_cyc fun ψ =>
    (level_window_coupling (la := 3 / 2) (by norm_num) (hAll ψ)).2.2

/-- **Direct Window-Coupling Theorem from Square `[Y, Y^2]` Bracket Windows → `ZeroFreeAll`**:
restricts `[Y, Y^2]` to `[Y, Y^(3/2)]` via `ZeroDensityWindow` and applies
`stage2_analyticBridgeContract`. -/
theorem zeroFreeAll_of_square_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) 2) :
    ZeroFreeAll :=
  stage2_analyticBridgeContract.zeroFreeAll_of_windows (3 / 2) (by norm_num)
    (ZeroDensityWindow.allLevelsWindowBound_three_halves_of_square_brackets hAll)

/-- **Direct Window-Coupling Theorem → All 5 Headline RH/GRH Theorems** from cyclic
`la = 3 / 2` bracket windows. -/
theorem headline_five_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    AllFiveHeadlineStatements :=
  headline_five_of_zeroFreeAll (zeroFreeAll_of_bracketWindows hAll)

/-- **Direct Window-Coupling Theorem → All 5 Headline RH/GRH Theorems** from cyclic
square `[Y, Y^2]` bracket windows. -/
theorem headline_five_of_square_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) 2) :
    AllFiveHeadlineStatements :=
  headline_five_of_zeroFreeAll (zeroFreeAll_of_square_bracketWindows hAll)

/-- **End-to-End `TopPlug` Window-Coupling (`VWin S` + `TopShape` → `ZeroFreeAll` and all 5
headline RH/GRH theorems)** via `ZeroDensityWindow.topPlug_zeroFreeAll` and
`stage2_analyticBridgeContract`. -/
theorem zeroFreeAll_of_vwin_topShape {S : SelmerSystem}
    (hV : VWin S)
    (hTopShape : ∀ ψ : PChar, VWinAt S ψ 401 →
      ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    ZeroFreeAll :=
  ZeroDensityWindow.topPlug_zeroFreeAll stage2_analyticBridgeContract hV hTopShape

theorem headline_five_of_vwin_topShape {S : SelmerSystem}
    (hV : VWin S)
    (hTopShape : ∀ ψ : PChar, VWinAt S ψ 401 →
      ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    AllFiveHeadlineStatements :=
  headline_five_of_zeroFreeAll (zeroFreeAll_of_vwin_topShape hV hTopShape)

/-- Individual headline projections from cyclic `la = 3 / 2` bracket windows. -/
theorem LFunction_ne_zero_of_half_lt_re_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    DirichletLNonvanishingRightOfHalf :=
  (headline_five_of_bracketWindows hAll).1

theorem LFunction_eq_zero_re_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    DirichletLZerosOnLine :=
  (headline_five_of_bracketWindows hAll).2.1

theorem LFunction_eq_zero_re_of_isPrimitive_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    PrimitiveDirichletLZerosOnLine :=
  (headline_five_of_bracketWindows hAll).2.2.1

theorem riemannHypothesis_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    RiemannHypothesis :=
  (headline_five_of_bracketWindows hAll).2.2.2.1

theorem riemannZeta_eq_zero_re_of_bracketWindows
    (hAll : ∀ ψ : PChar, ZeroDensityWindow.LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    RiemannZetaZerosOnLine :=
  (headline_five_of_bracketWindows hAll).2.2.2.2

end Stage2AnalyticWire
end RHDirect

end
