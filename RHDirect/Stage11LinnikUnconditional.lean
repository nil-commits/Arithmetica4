import RHDirect.Main
import RHDirect.Stage11DeuringHeilbronn
import RHDirect.Stage11LogFreeDensity
import RHDirect.Stage11LinnikBridge
import RHDirect.Stage11ThetaSiegelBridge
import RHDirect.Stage11WilesPatchingBridge

/-!
# RHDirect.Stage11LinnikUnconditional

**Phase B Crown Jewel — Unconditional Linnik's Theorem (1944), Complete Pillar-1 Elimination
(`0` Assumptions), and Exact `Stage3UnifiedInputs` Shrinkage (`3` Open Fields → `2` Open Fields)**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, targeted imports).

## Main Results

1. **Unconditional Discharge of Both Hypotheses of `Stage11LinnikBridge` (`0` Assumptions)**:
   - `deuringHeilbronnHypothesis_unconditional : Stage11LinnikBridge.DeuringHeilbronnHypothesis`
     proved directly from `Stage11DeuringHeilbronn.deuring_heilbronn_zero_repulsion`.
   - `dirichletZeroBoxCount_eq`: exact identity
     `Stage11LinnikBridge.dirichletZeroBoxCount m σ T = Stage11LogFreeDensity.dirichletZeroBoxCount m σ T`.
   - `logFreeZeroDensityHypothesis_unconditional : Stage11LinnikBridge.LogFreeZeroDensityHypothesis`
     proved directly from `Stage11LogFreeDensity.gallagher_logfree_zero_density_fixed_mod`.

2. **Unconditional Linnik's Theorem (1944) & Complete Pillar-1 Elimination (`0` Assumptions)**:
   - `linnikAPDyadic_unconditional : Stage2PrimePairs.LinnikAPDyadic`
   - `linnikAPInterval_unconditional : Stage2PrimePairs.LinnikAPInterval`
   - `pairSupply_unconditional : HostFieldSupply.PairSupply`
   - `pairEx_unconditional : ThetaSlopeEngine.PairEx`
   - `smallOne_unconditional : HostFieldSupply.SmallOne`
   - `linnik_least_prime_in_ap_unconditional`: textbook statement directly on Mathlib's
     `Nat.Prime` & `Nat.ModEq`:
     `∃ L > 0, ∃ C > 0, ∀ m a, 2 ≤ m → Nat.Coprime a m → ∃ p, p.Prime ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ C * (m : ℝ) ^ L`.
   - `linnik_least_prime_in_ap_unit_const_unconditional`: unit-constant form `p ≤ m ^ L`.

3. **Shrinking `RHDirect.Stage3UnifiedInputs S` from `3` Open Fields → `2` Open Fields**:
   - `Stage11UnifiedInputs S`: retains ONLY Pillar 3/4 (`patching`) and Pillar 2 (`realizeStage3`),
     permanently dropping `linnikAP` (discharged unconditionally by `linnikAPInterval_unconditional`)!
   - `Stage11UnifiedInputs.toStage3UnifiedInputs`, `assembly_of_stage11_two_field`, and ALL FIVE
     verbatim RH & GRH headline theorems (`riemannHypothesis_of_stage11_two_field`,
     `riemannZeta_eq_zero_re_of_stage11_two_field`,
     `LFunction_ne_zero_of_half_lt_re_of_stage11_two_field`,
     `LFunction_eq_zero_re_of_stage11_two_field`,
     `LFunction_eq_zero_re_of_isPrimitive_of_stage11_two_field`).
   - `Stage11TwoFieldMinimalInputs S`: combines Pillar 1 (`0` assumptions!) +
     Pillar 2 (`Stage11ThetaSiegelBridge.Stage11ThetaSiegelMinimalDatum`) +
     Pillar 3/4 (`Stage11WilesPatchingBridge.FerreroWashingtonTwoTowerSupply` +
     `StickelbergerRamifiedSupply` + `MinimalOddUnramifiedPatchingSupply`), proving
     `Stage11TwoFieldMinimalInputs.toStage11UnifiedInputs`, `assembly_of_stage11_minimal_two_field`,
     and all five verbatim RH & GRH headline theorems (including
     `riemannHypothesis_of_stage11_minimal_two_field`).
-/

noncomputable section

open Complex DirichletCharacter Finset
open scoped BigOperators Real

namespace RHDirect.Stage11LinnikUnconditional

open RHDirect
open RHDirect.Stage11DeuringHeilbronn
open RHDirect.Stage11LogFreeDensity
open RHDirect.Stage11LinnikBridge
open RHDirect.Stage11ThetaSiegelBridge
open RHDirect.Stage11WilesPatchingBridge

/-! ## Section 1: Unconditional Discharge of Both Hypotheses of `Stage11LinnikBridge` (`0` Assumptions) -/

/-- **UNCONDITIONAL DEURING–HEILBRONN HYPOTHESIS (`0` ASSUMPTIONS!)**:
discharges `Stage11LinnikBridge.DeuringHeilbronnHypothesis` directly from
`Stage11DeuringHeilbronn.deuring_heilbronn_zero_repulsion` by taking `Q = q * q₁` and
`c₂' = min c₂ c₃`. -/
theorem deuringHeilbronnHypothesis_unconditional :
    Stage11LinnikBridge.DeuringHeilbronnHypothesis := by
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hdh⟩ := deuring_heilbronn_zero_repulsion
  refine ⟨c₁, min c₂ c₃, hc₁, lt_min hc₂ hc₃,
    fun q₁ _ χ₁ hprim₁ hsq₁ hχ₁ β₁ hβ₁_lo hβ₁_hi hz₁ q _ χ _ ρ hre0 hre1 hzρ hne T hT hIm hsmall => ?_⟩
  have hq_pos : 0 < q := NeZero.pos q
  have hq₁_pos : 0 < q₁ := NeZero.pos q₁
  have hq₁_ge2 : 2 ≤ q₁ := by
    by_contra hlt
    have hq₁_eq1 : q₁ = 1 := by omega
    subst hq₁_eq1
    apply hχ₁
    ext a
    have ha : a = 1 := Subsingleton.elim a 1
    rw [ha]
    simp
  set Q : ℕ := q * q₁
  have hq₁_le_Q : q₁ ≤ Q := Nat.le_mul_of_pos_left q₁ hq_pos
  have hq_le_Q : q ≤ Q := Nat.le_mul_of_pos_right q hq₁_pos
  have hQ_ge2 : 2 ≤ Q := hq₁_ge2.trans hq₁_le_Q
  have hQ_cast : ((Q : ℕ) : ℝ) * T = (q : ℝ) * (q₁ : ℝ) * T := by
    dsimp only [Q]
    rw [Nat.cast_mul]
  have hQT_ge4 : (4 : ℝ) ≤ (q : ℝ) * (q₁ : ℝ) * T := by
    have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ_ge2
    rw [← hQ_cast]
    nlinarith
  have hlog_pos : 0 < Real.log ((q : ℝ) * (q₁ : ℝ) * T) :=
    Real.log_pos (by linarith)
  have h1mβ_pos : 0 < 1 - β₁ := by linarith
  have hprod_pos : 0 < (1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T) :=
    mul_pos h1mβ_pos hlog_pos
  have hprod_lt : (1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T) < min c₂ c₃ :=
    (lt_div_iff₀ hlog_pos).mp hsmall
  have hprod_le_c₃ : (1 - β₁) * Real.log ((Q : ℝ) * T) ≤ c₃ := by
    rw [hQ_cast]
    exact hprod_lt.le.trans (min_le_right c₂ c₃)
  have hrep := hdh Q T hQ_ge2 hT q₁ χ₁ hq₁_le_Q hprim₁ hsq₁ hχ₁ β₁ hβ₁_lo hβ₁_hi hz₁
    hprod_le_c₃ q χ ρ hq_le_Q hIm hre0 hre1 hzρ hne.symm
  rw [hQ_cast] at hrep
  have hratio_le :
      min c₂ c₃ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T)) ≤
        c₂ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T)) :=
    div_le_div_of_nonneg_right (min_le_left c₂ c₃) hprod_pos.le
  have hratio_pos : 0 < min c₂ c₃ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T)) :=
    div_pos (lt_min hc₂ hc₃) hprod_pos
  have hlog_le :
      Real.log (min c₂ c₃ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T))) ≤
        Real.log (c₂ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T))) :=
    Real.log_le_log hratio_pos hratio_le
  have hmono :
      c₁ * Real.log (min c₂ c₃ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T))) /
          Real.log ((q : ℝ) * (q₁ : ℝ) * T) ≤
        c₁ * Real.log (c₂ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T))) /
          Real.log ((q : ℝ) * (q₁ : ℝ) * T) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le hc₁.le) hlog_pos.le
  exact hmono.trans hrep

/-- Exact equality between the multiplicity-counted box zero counts in `Stage11LinnikBridge`
and `Stage11LogFreeDensity`. -/
theorem dirichletZeroBoxCount_eq (m : ℕ) [NeZero m] (σ T : ℝ) :
    Stage11LinnikBridge.dirichletZeroBoxCount m σ T =
      Stage11LogFreeDensity.dirichletZeroBoxCount m σ T := by
  classical
  unfold Stage11LinnikBridge.dirichletZeroBoxCount Stage11LogFreeDensity.dirichletZeroBoxCount
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Stage11LogFreeDensity.zerosOfLInBox_card_eq_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ρ
  simp only [Finset.mem_filter, Stage11LinnikBridge.mem_lZerosInBox,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

/-- **UNCONDITIONAL LOG-FREE ZERO-DENSITY HYPOTHESIS (`0` ASSUMPTIONS!)**:
discharges `Stage11LinnikBridge.LogFreeZeroDensityHypothesis` directly from
`Stage11LogFreeDensity.gallagher_logfree_zero_density_fixed_mod`. -/
theorem logFreeZeroDensityHypothesis_unconditional :
    Stage11LinnikBridge.LogFreeZeroDensityHypothesis := by
  obtain ⟨C, hC, A, _, hlf⟩ := gallagher_logfree_zero_density_fixed_mod
  refine ⟨C, max A 1, hC, le_max_right A 1, fun m _ hm σ T hσ_lo hσ_hi hT => ?_⟩
  rw [dirichletZeroBoxCount_eq m σ T]
  have h1 := hlf m hm T hT σ hσ_lo hσ_hi
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hbase_ge1 : (1 : ℝ) ≤ (m : ℝ) * (T + 2) := by nlinarith
  have hexp_le : A * (1 - σ) ≤ max A 1 * (1 - σ) :=
    mul_le_mul_of_nonneg_right (le_max_left A 1) (by linarith)
  have hpow_le : ((m : ℝ) * (T + 2)) ^ (A * (1 - σ)) ≤ ((m : ℝ) * (T + 2)) ^ (max A 1 * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge1 hexp_le
  exact h1.trans (mul_le_mul_of_nonneg_left hpow_le hC.le)

/-! ## Section 2: Unconditional Linnik's Theorem (1944) & Full Pillar-1 Elimination (`0` Assumptions) -/

/-- **UNCONDITIONAL DYADIC LINNIK–FOGELS–GALLAGHER THEOREM (`0` ASSUMPTIONS!)**:
there exists `L ≥ 1` such that for every `m ≥ 2`, every `a` coprime to `m`, and every `X ≥ m ^ L`,
there exists a prime `p ≡ a [MOD m]` with `X < p ≤ 2 * X`. -/
theorem linnikAPDyadic_unconditional : Stage2PrimePairs.LinnikAPDyadic :=
  linnikAPDyadic_of_dh_and_logfree
    deuringHeilbronnHypothesis_unconditional
    logFreeZeroDensityHypothesis_unconditional

/-- **UNCONDITIONAL LINNIK AP INTERVAL THEOREM (`0` ASSUMPTIONS!)**:
discharges `Stage2PrimePairs.LinnikAPInterval` (`X < p ≤ X ^ 2`) with zero external assumptions! -/
theorem linnikAPInterval_unconditional : Stage2PrimePairs.LinnikAPInterval :=
  linnikAPInterval_of_dh_and_logfree
    deuringHeilbronnHypothesis_unconditional
    logFreeZeroDensityHypothesis_unconditional

/-- **UNCONDITIONAL HOST-FIELD PRIME-PAIR SUPPLY (`0` ASSUMPTIONS!)**:
discharges `HostFieldSupply.PairSupply` completely unconditionally! -/
theorem pairSupply_unconditional : HostFieldSupply.PairSupply :=
  pairSupply_of_dh_and_logfree
    deuringHeilbronnHypothesis_unconditional
    logFreeZeroDensityHypothesis_unconditional

/-- **UNCONDITIONAL THETA-SLOPE PRIME-PAIR EXISTENCE (`0` ASSUMPTIONS!)**:
discharges `ThetaSlopeEngine.PairEx` completely unconditionally! -/
theorem pairEx_unconditional : ThetaSlopeEngine.PairEx :=
  pairEx_of_dh_and_logfree
    deuringHeilbronnHypothesis_unconditional
    logFreeZeroDensityHypothesis_unconditional

/-- **UNCONDITIONAL SMALL PRIME `p ≡ 1 (mod M)` BOUND (`0` ASSUMPTIONS!)**:
discharges `HostFieldSupply.SmallOne` completely unconditionally! -/
theorem smallOne_unconditional : HostFieldSupply.SmallOne :=
  smallOne_of_dh_and_logfree
    deuringHeilbronnHypothesis_unconditional
    logFreeZeroDensityHypothesis_unconditional

/-- **LINNIK'S THEOREM (1944) — TEXTBOOK STATEMENT ON MATHLIB `Nat.Prime` & `Nat.ModEq` (`0` ASSUMPTIONS!)**:
there exist absolute constants `L > 0` and `C > 0` such that for every modulus `m ≥ 2` and every
residue class `a` coprime to `m`, there exists a prime `p ≡ a [MOD m]` satisfying
`(p : ℝ) ≤ C * (m : ℝ) ^ L`. -/
theorem linnik_least_prime_in_ap_unconditional :
    ∃ L : ℝ, 0 < L ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
        ∃ p : ℕ, Nat.Prime p ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ C * (m : ℝ) ^ L := by
  obtain ⟨L, hL1, hL⟩ := linnikAPDyadic_unconditional
  refine ⟨L, by linarith, 2, by norm_num, fun m a hm hcop => ?_⟩
  obtain ⟨p, hp, hmod, _, hup⟩ := hL m a hm hcop ((m : ℝ) ^ L) le_rfl
  exact ⟨p, hp, hmod, hup⟩

/-- **LINNIK'S THEOREM (UNIT CONSTANT FORM, `0` ASSUMPTIONS!)**:
there exists `L ≥ 1` such that for every `m ≥ 2` and `Nat.Coprime a m`, there exists a prime
`p ≡ a [MOD m]` with `(p : ℝ) ≤ (m : ℝ) ^ L`. -/
theorem linnik_least_prime_in_ap_unit_const_unconditional :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
        ∃ p : ℕ, Nat.Prime p ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ (m : ℝ) ^ L := by
  obtain ⟨L, hL1, hL⟩ := linnikAPDyadic_unconditional
  refine ⟨L + 1, by linarith, fun m a hm hcop => ?_⟩
  obtain ⟨p, hp, hmod, _, hup⟩ := hL m a hm hcop ((m : ℝ) ^ L) le_rfl
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h2_le : 2 * (m : ℝ) ^ L ≤ (m : ℝ) ^ (L + 1) := by
    rw [Real.rpow_add hm_pos, Real.rpow_one, mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left hm2 (Real.rpow_nonneg hm_pos.le L)
  exact ⟨p, hp, hmod, hup.trans h2_le⟩

/-! ## Section 3: Shrinking `RHDirect.Stage3UnifiedInputs S` from `3` Open Fields → `2` Open Fields -/

/-- **Stage 11 Two-Field Unified Input Bundle (`Stage11UnifiedInputs S`)**:
shrinks `RHDirect.Stage3UnifiedInputs S` from `3` open fields to **ONLY `2` open fields**,
permanently eliminating the `linnikAP` field via `linnikAPInterval_unconditional` (`0` assumptions):
1. **Pillar 1 (Analytic Bridge + Linnik AP)**: **`0` open fields** (100% unconditional!).
2. **Pillar 3/4 (`patching`)**: `Stage3PatchingUnification.UnifiedPatchingWindowSupply S`.
3. **Pillar 2 (`realizeStage3`)**: Siegel-reduced lattice + Gaussian-theta fiber realization witness
   (identical to `RHDirect.Stage3UnifiedInputs.realizeStage3`). -/
structure Stage11UnifiedInputs (S : SelmerSystem) where
  /-- Open Field 1 (Pillar 3/4): unified `B_ram + B_unram` Taylor–Wiles patching supply. -/
  patching : Stage3PatchingUnification.UnifiedPatchingWindowSupply S
  /-- Pillar-2 loss exponent `eL ≥ 0`. -/
  eL : ℝ
  eL_nonneg : 0 ≤ eL
  /-- Open Field 2 (Pillar 2): Siegel-reduced lattice + Gaussian-theta fiber realization witness. -/
  realizeStage3 : ∀ (ψ : PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52), 1 ≤ J →
    ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
      ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
        ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
        Nonempty (Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)

/-- **Exact Two-Field → Three-Field Compiler (`Stage11UnifiedInputs S → RHDirect.Stage3UnifiedInputs S`)**:
automatically populates `Stage3UnifiedInputs.linnikAP` with `linnikAPInterval_unconditional`! -/
def Stage11UnifiedInputs.toStage3UnifiedInputs {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : RHDirect.Stage3UnifiedInputs S where
  patching := I.patching
  linnikAP := linnikAPInterval_unconditional
  eL := I.eL
  eL_nonneg := I.eL_nonneg
  realizeStage3 := I.realizeStage3

/-- **Master Two-Field Three-Pillar Assembly (`Stage11UnifiedInputs S → RHDirectAssembly S`)**. -/
theorem assembly_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : RHDirect.RHDirectAssembly S :=
  RHDirect.assembly_of_stage3_inputs I.toStage3UnifiedInputs

/-- Two-field `ZeroFreeAll` from `Stage11UnifiedInputs S`. -/
theorem zeroFreeAll_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : RHDirect.ZeroFreeAll :=
  RHDirect.zeroFreeAll_of_stage3_inputs I.toStage3UnifiedInputs

/-- Two-field simultaneous 5-tuple of all verbatim RH & GRH headline statements. -/
theorem headline_five_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : Stage2AnalyticWire.AllFiveHeadlineStatements :=
  RHDirect.headline_five_of_stage3_inputs I.toStage3UnifiedInputs

/-- Two-Field Headline 1: Nonvanishing of all Dirichlet `L`-functions in `Re(s) > 1/2`. -/
theorem LFunction_ne_zero_of_half_lt_re_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : DirichletLNonvanishingRightOfHalf :=
  RHDirect.LFunction_ne_zero_of_half_lt_re_of_stage3 I.toStage3UnifiedInputs

/-- Two-Field Headline 2: All critical-strip zeros of any Dirichlet `L`-function lie on `Re(s) = 1/2`. -/
theorem LFunction_eq_zero_re_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : DirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_stage3 I.toStage3UnifiedInputs

/-- Two-Field Headline 3: All critical-strip zeros of any primitive Dirichlet `L`-function lie on `Re(s) = 1/2`. -/
theorem LFunction_eq_zero_re_of_isPrimitive_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : PrimitiveDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_isPrimitive_of_stage3 I.toStage3UnifiedInputs

/-- Two-Field Headline 4: **The Riemann Hypothesis** (Mathlib's `RiemannHypothesis` verbatim). -/
theorem riemannHypothesis_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : RiemannHypothesis :=
  RHDirect.riemannHypothesis_of_stage3 I.toStage3UnifiedInputs

/-- Two-Field Headline 5: Explicit statement of the Riemann Hypothesis for nontrivial zeros of `ζ(s)`
(`src/Statements.lean` verbatim). -/
theorem riemannZeta_eq_zero_re_of_stage11_two_field {S : SelmerSystem}
    (I : Stage11UnifiedInputs S) : RiemannZetaZerosOnLine :=
  RHDirect.riemannZeta_eq_zero_re_of_stage3 I.toStage3UnifiedInputs

/-! ## Section 4: Deepest Phase-B Minimal Two-Field Synthesis (`Stage11TwoFieldMinimalInputs S`) -/

/-- **Deepest Phase-B Minimal Two-Field Input Bundle (`Stage11TwoFieldMinimalInputs S`)**:
unifies ALL Phase-B assumption reductions across all four pillars simultaneously:
- **Pillar 1 (Analytic Bridge + Linnik AP)**: **`0` assumptions** (`linnikAPInterval_unconditional`
  + `Stage2AnalyticWire.stage2_analyticBridgeContract`)!
- **Pillar 2 (Theta–Siegel–Bost)**: reduced from 83-field `Stage3ThetaSiegelFiberWitness` to the
  minimal geometric covolume datum `Stage11ThetaSiegelBridge.Stage11ThetaSiegelMinimalDatum`!
- **Pillar 3/4 (Wiles Patching + Iwasawa + Stickelberger)**: reduced from full
  `UnifiedPatchingWindowSupply S` to `FerreroWashingtonTwoTowerSupply S` +
  `StickelbergerRamifiedSupply S` (`Cb = 2` pinned) + `MinimalOddUnramifiedPatchingSupply S`! -/
structure Stage11TwoFieldMinimalInputs (S : SelmerSystem) where
  /-- Pillar 3/4 (`l = 2`): Ferrero–Washington (`μ = 0`) Iwasawa 2-tower supply. -/
  twoTower : FerreroWashingtonTwoTowerSupply S
  /-- Pillar 3/4 (odd ramified): cyclotomic Stickelberger supply (`Cb = 2` pinned). -/
  ramified : StickelbergerRamifiedSupply S
  /-- Pillar 3/4 (odd unramified): minimal Taylor–Wiles congruence-patching supply. -/
  oddUnramified : MinimalOddUnramifiedPatchingSupply S
  /-- Pillar-2 loss exponent `eL ≥ 0`. -/
  eL : ℝ
  eL_nonneg : 0 ≤ eL
  /-- Pillar 2: drastically shrunk `Stage11ThetaSiegelMinimalDatum` fiber realization witness. -/
  realizeStage11 : ∀ (ψ : PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52), 1 ≤ J →
    ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
      ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
        ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
        Nonempty (Stage11ThetaSiegelMinimalDatum S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)

/-- Compile Pillar 2 of `Stage11TwoFieldMinimalInputs S` into `Stage11ThetaSiegelCoreInputs S`
using `linnikAPInterval_unconditional` (`0` Linnik assumptions!). -/
def Stage11TwoFieldMinimalInputs.toStage11ThetaSiegelCoreInputs {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : Stage11ThetaSiegelCoreInputs S :=
  Stage11ThetaSiegelCoreInputs.ofLinnikAP S I.eL I.eL_nonneg
    linnikAPInterval_unconditional I.realizeStage11

/-- **Compile `Stage11TwoFieldMinimalInputs S` directly into the Two-Field `Stage11UnifiedInputs S`**! -/
def Stage11TwoFieldMinimalInputs.toStage11UnifiedInputs {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : Stage11UnifiedInputs S where
  patching := unifiedPatchingWindowSupply_of_minimal I.twoTower I.ramified I.oddUnramified
  eL := I.eL
  eL_nonneg := I.eL_nonneg
  realizeStage3 :=
    (stage3ThetaSiegelCoreInputs_of_stage11_minimal S I.toStage11ThetaSiegelCoreInputs).realizeStage3

/-- Compile `Stage11TwoFieldMinimalInputs S` into `RHDirect.Stage3UnifiedInputs S`. -/
def Stage11TwoFieldMinimalInputs.toStage3UnifiedInputs {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : RHDirect.Stage3UnifiedInputs S :=
  I.toStage11UnifiedInputs.toStage3UnifiedInputs

/-- **Master Minimal Two-Field Three-Pillar Assembly (`Stage11TwoFieldMinimalInputs S → RHDirectAssembly S`)**. -/
theorem assembly_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : RHDirect.RHDirectAssembly S :=
  assembly_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal two-field `ZeroFreeAll`. -/
theorem zeroFreeAll_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : RHDirect.ZeroFreeAll :=
  zeroFreeAll_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal two-field simultaneous 5-tuple of all verbatim RH & GRH headline statements. -/
theorem headline_five_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : Stage2AnalyticWire.AllFiveHeadlineStatements :=
  headline_five_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal Two-Field Headline 1: Nonvanishing of all Dirichlet `L`-functions in `Re(s) > 1/2`. -/
theorem LFunction_ne_zero_of_half_lt_re_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : DirichletLNonvanishingRightOfHalf :=
  LFunction_ne_zero_of_half_lt_re_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal Two-Field Headline 2: All critical-strip zeros of any Dirichlet `L`-function lie on `Re(s) = 1/2`. -/
theorem LFunction_eq_zero_re_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : DirichletLZerosOnLine :=
  LFunction_eq_zero_re_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal Two-Field Headline 3: All critical-strip zeros of any primitive Dirichlet `L`-function lie on `Re(s) = 1/2`. -/
theorem LFunction_eq_zero_re_of_isPrimitive_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : PrimitiveDirichletLZerosOnLine :=
  LFunction_eq_zero_re_of_isPrimitive_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal Two-Field Headline 4: **The Riemann Hypothesis** (Mathlib's `RiemannHypothesis` verbatim). -/
theorem riemannHypothesis_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : RiemannHypothesis :=
  riemannHypothesis_of_stage11_two_field I.toStage11UnifiedInputs

/-- Minimal Two-Field Headline 5: Explicit statement of the Riemann Hypothesis for nontrivial zeros
of `ζ(s)` (`src/Statements.lean` verbatim). -/
theorem riemannZeta_eq_zero_re_of_stage11_minimal_two_field {S : SelmerSystem}
    (I : Stage11TwoFieldMinimalInputs S) : RiemannZetaZerosOnLine :=
  riemannZeta_eq_zero_re_of_stage11_two_field I.toStage11UnifiedInputs

/-! ## Section 5: Master `0`-Assumption Pillar-1 Unconditional Certification -/

/-- **MASTER `0`-ASSUMPTION PILLAR-1 CERTIFICATION**:
simultaneously certifies every unconditional Pillar-1 theorem proved in Phase B:
1. `Stage11LinnikBridge.DeuringHeilbronnHypothesis` (Deuring–Heilbronn zero repulsion),
2. `Stage11LinnikBridge.LogFreeZeroDensityHypothesis` (Gallagher log-free zero density),
3. `Stage2PrimePairs.LinnikAPDyadic` & `Stage2PrimePairs.LinnikAPInterval`,
4. `HostFieldSupply.PairSupply`, `ThetaSlopeEngine.PairEx`, `HostFieldSupply.SmallOne`,
5. Textbook Linnik's Theorem (`∃ L > 0, ∃ C > 0, ∀ m ≥ 2, Coprime a m → ∃ p prime, p ≡ a [MOD m], p ≤ C m^L`),
6. `RHDirect.AnalyticBridgeContract` & `RHDirect.ConductorBounds`. -/
theorem stage11_pillar1_unconditional_master :
    Stage11LinnikBridge.DeuringHeilbronnHypothesis ∧
    Stage11LinnikBridge.LogFreeZeroDensityHypothesis ∧
    Stage2PrimePairs.LinnikAPDyadic ∧
    Stage2PrimePairs.LinnikAPInterval ∧
    HostFieldSupply.PairSupply ∧
    ThetaSlopeEngine.PairEx ∧
    HostFieldSupply.SmallOne ∧
    (∃ L : ℝ, 0 < L ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
        ∃ p : ℕ, Nat.Prime p ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ C * (m : ℝ) ^ L) ∧
    RHDirect.AnalyticBridgeContract ∧
    RHDirect.ConductorBounds :=
  ⟨deuringHeilbronnHypothesis_unconditional,
   logFreeZeroDensityHypothesis_unconditional,
   linnikAPDyadic_unconditional,
   linnikAPInterval_unconditional,
   pairSupply_unconditional,
   pairEx_unconditional,
   smallOne_unconditional,
   linnik_least_prime_in_ap_unconditional,
   Stage2AnalyticWire.stage2_analyticBridgeContract,
   Stage2GaloisWire.conductorBounds_unconditional⟩

end RHDirect.Stage11LinnikUnconditional

end
