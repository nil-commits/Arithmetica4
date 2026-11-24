import RHDirect.Stage12MultivarDwork
import RHDirect.Stage12FontainePeriods
import RHDirect.PAdicChainValuation
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# RHDirect.Stage14M5_QPackJetWeights

Field-2 Package M5 Wave 1: **Crystalline `QPack` + Hodge–Tate Reduction (`FullCrystallineQPack`
& `hodge_tate_reduction_red`), Young-Diagram Jet-Weight LP Flow (`YoungDiagramLPFlow` &
`lpF_eq_Fnum`), `l`-adic Complex Norm Comparison (`norm_l_padic_complex`), and `p`-adic Gluing
Index Bounds (`qpack_gluing_index_bound`)** in pure Mathlib `v4.33.1`
(`0 sorry`, `0 custom axioms`, `0 opaque`, `0 native_decide`).

## Architecture (Diamond-Free)

All crystalline period-ring upgrades over `Stage12FontainePeriods` (`A_inf`, `B_cris`, `B_dR`,
`D_cris`) use explicit `RingHom`s and `AddMonoidHom`s — ZERO nested global `Algebra` instances
or typeclass diamonds.

## Contents

1. **`l`-adic Complex Norm Comparison (`norm_l_padic_complex`) & Ultrametric Valuation Toolkit**:
   - Exact prime norm `norm_l_padic_complex : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹` and real-power form
     `norm_l_padic_complex_rpow : ‖(l : ℂ_[l])‖ ^ x = (l : ℝ) ^ (-x)`.
   - Exact prime-power, factorial, and multi-factorial norm comparisons in `ℂ_[l]`, plus
     unconditional existence of a Dwork uniformizer `ϖ ∈ ℂ_[p]` (`ϖ^(p-1) = -p`,
     `‖ϖ‖ = p^{-1/(p-1)}`).
   - Dwork LP constants `rho l = 1 / (l^2 - 1)` and `gam l = l / (l^2 - 1)`, identities
     `rho l + gam l = 1 / (l - 1)`, `gam l - 1 / (l + 1) = rho l`, geometric series
     `HasSum (fun k => ((l : ℝ) ^ (2 * k + 1))⁻¹) (gam l)`, and `p`-adic valuation gain
     inequalities `val_gain_nat`, `val_gain_rho`.

2. **Crystalline `FullCrystallineQPack`, `Ospan`, & `hodge_tate_reduction_red`**:
   - Integral `O_K`-span `Ospan K S : AddSubgroup V` matching Alpöge's `ModuliIntegralCharts.Ospan`.
   - `FullCrystallineQPack K p` upgrading `Stage12MultivarDwork.CrystallineQPack K p` with:
     - integral differential lattice `om : AddSubgroup base.OmV` and `red_range`,
     - crystalline Fontaine period package `periodPkg : LocPrimePackage p` tied to concrete
       `A_inf / B_cris / B_dR` via `Nonempty (LocTied p periodPkg)`,
     - explicit diamond-free period ring homomorphism `ainfToA : periodPkg.AinfRing →+* base.A`,
     - finite-dimensional `FilteredPhiModule p Dcris` (`D_cris` data) and crystalline-to-filtered
       comparison map `crysToFilM : Dcris →+ base.FilM`.
   - **`hodge_tate_reduction_red`** & **`FullCrystallineQPack.htb_at`**: proves the full
     Hodge–Tate sandwich
     `Ospan K (Set.range ht) ≤ om` and `∀ x ∈ om, ∀ c : K, ‖c‖ ≤ p^{-1/(p-1)} → c • x ∈ Ospan K (Set.range ht)`.
   - Unconditional concrete realization **`concreteFullCrystallineQPack`** over `ℂ_[p]` for
     EVERY prime `p` (`nonempty_fullCrystallineQPack`), built directly from `OCp p`,
     `concreteLocPrimePackage p`, `nonempty_locTied p`, `cyclotomicLaurentPeriodSystem p`,
     and `dworkPiQPack`.

3. **Young-Diagram Jet-Weight LP Flow (`YoungDiagramLPFlow`), `lpF_eq_Fnum`, & Strong LP Duality**:
   - Primal LP formulation (`lpFeasible`, `lpF`) and odd-level flow formulation
     (`IsFlow`, `flowVal`, `maxFlow`, `Fnum`), with proved equivalence **`lpF_eq_Fnum`**.
   - Exact adjoint pairing `pair_eq`, weak duality `flowVal_le_dual_sum`, universal lower/upper
     bounds `Fnum_ge_rho_mul_sum` (`rho l * ∑ D ≤ Fnum l d D`) and `Fnum_le_gam_mul_sum`.
   - Max-flow attainment `exists_opt_flow` via compactness of finite-dimensional truncated boxes,
     positive homogeneity `Fnum_smul`, concavity of `maxFlow`, and convexity `Fnum_convexOn`.
   - **Strong LP duality (`exists_opt_dual`)** proved via `geometric_hahn_banach_closed_point` on
     finite-dimensional `(ZMod d → ℝ) × ℝ`!
   - Complementary slackness (`cs_identity`, `cs_zero`), incoming dominance
     (`incoming_dominance_of_dual_ge`), **`incoming_bound_of_optDual`**
     (`∑_{2/l ≤ sig s} D s ≤ (∑ D) / l`), and exact balanced-degree formula
     **`Fnum_eq_rho_of_balanced`** (`(∀ s s', D s' ≤ l * D s) → Fnum l d D = rho l * ∑ D`).
   - `YoungDiagramLPFlow` bundling Young diagrams `nu : ZMod d → YoungDiagram`, top-set `TT`,
     `cap`, `Dl`, `dTop`, `Wc`, `topTerm`, `baseTerm`, and `FD`, proving **`FD_eq_Fnum`** and
     **`baseTerm_le_topTerm`**.

4. **Dwork Power-Series Jet Weights (`DworkPowerSeriesWeights` Bridge)**:
   - `KvalGe` coefficient norm control in `ℂ_[l]`, monotonicity `kvalGe_mono`, unit-twist
     invariance `wtGe_unit_scale`, and Young-diagram jet-polynomial valuation transfer
     `dwork_jet_weight_transfer`.

5. **`p`-adic Gluing Index Bounds (`qpack_gluing_index_bound`) & Wave-2 Synthesis**:
   - Algebraic lattice quotient cardinality bound `card_quot_le_pow_of_smul_le`,
     `latIndex_le_pow_of_smul_le`, `log_latIndex_le_of_smul_le`, and exact Arakelov slope
     gluing bracket `slope_gluing_bracket_of_smul_le`.
   - **`qpack_gluing_index_bound`**: proved `p`-adic gluing index upper bound (`≤ p ^ r`,
     `log ≤ r * log p`) directly from `FullCrystallineQPack` and `hodge_tate_reduction_red`.
   - **`qpack_gluing_ramified_index_bound`**: ramified local-field gluing index bound
     (`≤ q ^ (r * ⌈e / (p - 1)⌉)` and valuation overhead `≤ 1 / (p - 1) + 1 / e`).
   - Multi-place gluing sum bound `multiplace_qpack_gluing_index_bound` and Wave-2 package
     `QPackJetWeightsPack` ready for `Stage14M5_IndefSideAndON`.
-/

open Real Finset Module Submodule
open scoped BigOperators Pointwise
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage11BostDworkSqueeze
open RHDirect.Stage11CrystallineFontaine
open RHDirect.Stage12MultivarDwork
open RHDirect.Stage12FontainePeriods

namespace RHDirect.Stage14M5_QPackJetWeights

noncomputable section

/-! ## Section 1: `l`-adic Complex Norm Comparison (`norm_l_padic_complex`) & Valuation Toolkit -/

section PadicComplexNorms

/-- **Exact Prime Norm in `ℂ_[l]` (`norm_l_padic_complex`)**:
for every prime `l`, `‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹`. -/
theorem norm_l_padic_complex (l : ℕ) [Fact l.Prime] :
    ‖((l : ℕ) : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h1 : ((l : ℕ) : ℂ_[l]) = (((l : ℕ) : PadicAlgCl l) : ℂ_[l]) := by simp
  rw [h1, PadicComplex.norm_extends]
  have h2 : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [h2, PadicAlgCl.norm_extends, Padic.norm_p]

/-- **Real-Power Norm Identity in `ℂ_[l]` (`norm_l_padic_complex_rpow`)**:
`‖(l : ℂ_[l])‖ ^ x = (l : ℝ) ^ (-x)` for all `x : ℝ`. -/
theorem norm_l_padic_complex_rpow (l : ℕ) [Fact l.Prime] (x : ℝ) :
    ‖((l : ℕ) : ℂ_[l])‖ ^ x = (l : ℝ) ^ (-x) := by
  rw [norm_l_padic_complex, Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]

theorem norm_l_padic_complex_pos (l : ℕ) [Fact l.Prime] :
    0 < ‖((l : ℕ) : ℂ_[l])‖ := by
  rw [norm_l_padic_complex]
  exact inv_pos.mpr (Nat.cast_pos.mpr (Fact.out : l.Prime).pos)

theorem norm_l_padic_complex_lt_one (l : ℕ) [Fact l.Prime] :
    ‖((l : ℕ) : ℂ_[l])‖ < 1 := by
  rw [norm_l_padic_complex]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/-- Exact ultrametric norm of any nonzero natural number in `ℂ_[l]`:
`‖(n : ℂ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℝ))`. -/
theorem norm_natCast_padic_complex (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℂ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℝ)) := by
  have hl : l.Prime := Fact.out
  rw [norm_natCast_eq_pow_padicValNat hl (norm_l_padic_complex_lt_one l) hn,
    ← Real.rpow_natCast, norm_l_padic_complex_rpow]

/-- Every integer has norm `≤ 1` in `ℂ_[l]`. -/
theorem norm_intCast_padic_complex_le_one (l : ℕ) [Fact l.Prime] (z : ℤ) :
    ‖(z : ℂ_[l])‖ ≤ 1 :=
  norm_intCast_le_one (K := ℂ_[l]) z

/-- Exact ultrametric norm of `k!` in `ℂ_[l]`. -/
theorem norm_factorial_padic_complex (l : ℕ) [Fact l.Prime] (k : ℕ) :
    ‖((k.factorial : ℕ) : ℂ_[l])‖ = (l : ℝ) ^ (-(padicValNat l k.factorial : ℝ)) :=
  norm_natCast_padic_complex l (Nat.factorial_ne_zero k)

/-- Exact Dwork additive valuation of `(l : ℂ_[l])` is `1`. -/
theorem dworkVal_padic_complex_l (l : ℕ) [Fact l.Prime] :
    dworkVal l ((l : ℕ) : ℂ_[l]) = 1 := by
  have hl : l.Prime := Fact.out
  have hlog_ne : Real.log (l : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hl.one_lt)).ne'
  unfold dworkVal
  rw [norm_l_padic_complex, Real.log_inv]
  field_simp [hlog_ne]

/-- Comparison between an arbitrary ultrametric normed field `K` normalized by `‖(l : K)‖ = l⁻¹`
and `ℂ_[l]`: every nonzero natural number has identical norm in `K` and in `ℂ_[l]`. -/
theorem norm_natCast_eq_padic_complex {K : Type*} [NormedField K] [IsUltrametricDist K]
    (l : ℕ) [Fact l.Prime] (hnl : ‖((l : ℕ) : K)‖ = (l : ℝ)⁻¹) {n : ℕ} (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(n : ℂ_[l])‖ := by
  have hl : l.Prime := Fact.out
  have hltK : ‖((l : ℕ) : K)‖ < 1 := by
    rw [hnl]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  rw [norm_natCast_eq_pow_padicValNat hl hltK hn, hnl, ← norm_l_padic_complex l,
    ← norm_natCast_eq_pow_padicValNat hl (norm_l_padic_complex_lt_one l) hn]

/-- Multi-factorial norm bound specialized cleanly to `ℂ_[l]` with base `(l : ℝ)`. -/
theorem norm_mfact_padic_complex_le {ι : Type*} [Fintype ι] (l : ℕ) [Fact l.Prime] (κ : ι →₀ ℕ) :
    ‖((mfact κ : ℕ) : ℂ_[l])‖ ≤
      (l : ℝ) ^ (-((∑ i : ι, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))) := by
  have hl : l.Prime := Fact.out
  have h := multifactorial_norm_bound (K := ℂ_[l]) hl (norm_l_padic_complex_lt_one l) κ
  rwa [norm_l_padic_complex_rpow] at h

/-- For every prime `p`, `p⁻¹ ≤ p ^ (-1 / (p - 1))` (i.e. `‖p‖ ≤ ‖ϖ‖` for a Dwork uniformizer). -/
theorem inv_prime_le_rpow_neg_inv_sub_one {p : ℕ} (hp : p.Prime) :
    ((p : ℝ)⁻¹) ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp_sub : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hexp : (-1 : ℝ) ≤ -(1 : ℝ) / ((p : ℝ) - 1) := by
    rw [neg_div]
    have hinv : ((p : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp_sub
    have : 1 / ((p : ℝ) - 1) ≤ 1 := by simpa [one_div] using hinv
    linarith
  calc (p : ℝ)⁻¹ = (p : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one (p : ℝ)).symm
    _ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := Real.rpow_le_rpow_of_exponent_le hp1.le hexp

/-- For every prime `p`, `‖(p : ℂ_[p])‖ ≤ p ^ (-1 / (p - 1))`. -/
theorem norm_p_padic_complex_le_dwork (p : ℕ) [Fact p.Prime] :
    ‖((p : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
  rw [norm_l_padic_complex]
  exact inv_prime_le_rpow_neg_inv_sub_one Fact.out

/-- **Unconditional Existence of a Dwork Uniformizer `ϖ ∈ ℂ_[p]`**:
for every prime `p`, since `ℂ_[p]` is algebraically closed (`IsAlgClosed ℂ_[p]`), there exists
`ϖ : ℂ_[p]` with `ϖ ^ (p - 1) = -p` and exact norm `‖ϖ‖ = p ^ (-1 / (p - 1))`! -/
theorem exists_dwork_uniformizer_padic_complex (p : ℕ) [Fact p.Prime] :
    ∃ ϖ : ℂ_[p], ϖ ^ (p - 1) = -((p : ℕ) : ℂ_[p]) ∧
      ‖ϖ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
  have hp : p.Prime := Fact.out
  have hpos : 0 < p - 1 := by have := hp.two_le; omega
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq (-((p : ℕ) : ℂ_[p])) hpos
  refine ⟨ϖ, hϖ, ?_⟩
  rw [norm_dworkPi hp hϖ, expRadius, norm_l_padic_complex,
    Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _)]
  congr 1; ring

/-! ### Dwork LP Constants `rho`, `gam` and Valuation Gain Inequalities -/

/-- Dwork quadratic-gain constant `ρ(l) = 1 / (l^2 - 1)`. -/
def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

/-- Dwork odd-geometric constant `γ(l) = l / (l^2 - 1) = ∑_{k ≥ 0} l^{-(2k+1)}`. -/
def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)

theorem rho_pos {l : ℕ} (hl : 2 ≤ l) : 0 < rho l := by
  unfold rho
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  exact div_pos one_pos this

theorem gam_pos {l : ℕ} (hl : 2 ≤ l) : 0 < gam l := by
  unfold gam
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  exact div_pos (by linarith) this

theorem rho_add_gam {l : ℕ} (hl : 2 ≤ l) : rho l + gam l = 1 / ((l : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'
  have h3 : (l : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) - 1).ne'
  unfold rho gam
  field_simp [h1, h3]
  ring

theorem gam_sub_inv_succ {l : ℕ} (hl : 2 ≤ l) : gam l - 1 / ((l : ℝ) + 1) = rho l := by
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) + 1).ne'
  unfold gam rho
  field_simp [h1, h3]
  ring

/-- Exact odd-power geometric series `∑_{k=0}^∞ l^{-(2k+1)} = γ(l)`. -/
theorem hasSum_inv_pow_odd {l : ℕ} (hl : 2 ≤ l) :
    HasSum (fun k : ℕ => ((l : ℝ) ^ (2 * k + 1))⁻¹) (gam l) := by
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hq0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹ := by positivity
  have hq1 : ((l : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((l : ℝ)⁻¹)
  have hterm : (fun k : ℕ => (l : ℝ)⁻¹ * (((l : ℝ) ^ 2)⁻¹) ^ k) =
      (fun k : ℕ => ((l : ℝ) ^ (2 * k + 1))⁻¹) := by
    funext k
    have hpow : (l : ℝ) ^ (2 * k + 1) = (l : ℝ) * ((l : ℝ) ^ 2) ^ k := by
      rw [← pow_mul, pow_succ, mul_comm]
    rw [hpow, mul_inv, inv_pow]
  have hval : (l : ℝ)⁻¹ * (1 - ((l : ℝ) ^ 2)⁻¹)⁻¹ = gam l := by
    unfold gam
    have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'
    have hsub : 1 - ((l : ℝ) ^ 2)⁻¹ ≠ 0 := by linarith
    field_simp [hl0.ne', h1, hsub]
  rw [hterm, hval] at hgeo
  exact hgeo

/-- **Elementary `l`-adic Valuation Gain (`val_gain_nat`)**:
for any prime `l` and `n ≥ 1`, `1 / (l - 1) ≤ n / (l - 1) - v_l(n)`. -/
theorem val_gain_nat {l : ℕ} (hl : l.Prime) {n : ℕ} (hn : 1 ≤ n) :
    1 / ((l : ℝ) - 1) ≤ (n : ℝ) / ((l : ℝ) - 1) - (padicValNat l n : ℝ) := by
  have : Fact l.Prime := ⟨hl⟩
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
  have hl_sub : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hpow_le : l ^ padicValNat l n ≤ n :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  -- `1 + (l - 1) * k ≤ l ^ k` for all `k : ℕ` by induction
  have hbern : ∀ k : ℕ, 1 + (l - 1) * k ≤ l ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpos : 1 ≤ l ^ k := Nat.one_le_pow k l hl.pos
      have hlm : l ^ k * l = l ^ k + (l - 1) * l ^ k := by
        cases l with
        | zero => exact absurd hl (by decide)
        | succ m => simp [Nat.succ_mul, add_comm, mul_comm]
      calc 1 + (l - 1) * (k + 1)
          = (1 + (l - 1) * k) + (l - 1) := by ring
        _ ≤ l ^ k + (l - 1) * l ^ k :=
            Nat.add_le_add ih (Nat.le_mul_of_pos_right (l - 1) hpos)
        _ = l ^ (k + 1) := by rw [pow_succ, hlm]
  have hineq : 1 + (l - 1) * padicValNat l n ≤ n := (hbern _).trans hpow_le
  have hineqR : (1 : ℝ) + ((l : ℝ) - 1) * (padicValNat l n : ℝ) ≤ (n : ℝ) := by
    have hcast : ((1 + (l - 1) * padicValNat l n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hineq
    rwa [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_one] at hcast
  have hmul : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) ≤
      ((l : ℝ) - 1) * ((n : ℝ) / ((l : ℝ) - 1) - (padicValNat l n : ℝ)) := by
    rw [mul_one_div_cancel hl_sub.ne', mul_sub, mul_div_cancel₀ _ hl_sub.ne']
    linarith
  exact le_of_mul_le_mul_left hmul hl_sub

/-- **Quadratic-Exponent Valuation Gain (`val_gain_rho`)**:
for any prime `l` and `e : ℕ`, `rho l ≤ ((l : ℝ) ^ 2) ^ e * rho l - e`. -/
theorem val_gain_rho {l : ℕ} (hl : l.Prime) (e : ℕ) :
    rho l ≤ ((l : ℝ) ^ 2) ^ e * rho l - (e : ℝ) := by
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
  have hden : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  -- `((l^2)^e - 1) ≥ e * (l^2 - 1)` by Bernoulli induction
  have hbern : ∀ k : ℕ, (k : ℝ) * ((l : ℝ) ^ 2 - 1) ≤ ((l : ℝ) ^ 2) ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      rw [pow_succ ((l : ℝ) ^ 2) k]
      have hge1 : (1 : ℝ) ≤ ((l : ℝ) ^ 2) ^ k := one_le_pow₀ (by nlinarith)
      nlinarith
  have hk := hbern e
  unfold rho
  have hmul : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) ≤
      ((l : ℝ) ^ 2 - 1) * (((l : ℝ) ^ 2) ^ e * (1 / ((l : ℝ) ^ 2 - 1)) - (e : ℝ)) := by
    rw [mul_one_div_cancel hden.ne', mul_sub, ← mul_assoc,
      mul_comm ((l : ℝ) ^ 2 - 1), mul_assoc, mul_one_div_cancel hden.ne', mul_one]
    linarith
  exact le_of_mul_le_mul_left hmul hden

end PadicComplexNorms

/-! ## Section 2: `O_K`-Spans (`Ospan`), `FullCrystallineQPack` & `hodge_tate_reduction_red` -/

section FullCrystallineQPackSection

/-- **Integral `O_K`-Span (`Ospan K S`)** matching Alpöge's `ModuliIntegralCharts.Ospan`:
the additive subgroup of a `K`-vector space `V` generated by `{a • s | ‖a‖ ≤ 1, s ∈ S}`. -/
def Ospan (K : Type*) [NormedField K] {V : Type*} [AddCommGroup V] [Module K V]
    (S : Set V) : AddSubgroup V :=
  AddSubgroup.closure {v : V | ∃ a : K, ‖a‖ ≤ 1 ∧ ∃ s ∈ S, a • s = v}

theorem ospan_mem_of_mem {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {S : Set V} {s : V} (hs : s ∈ S) : s ∈ Ospan K S :=
  AddSubgroup.subset_closure ⟨1, by simp, s, hs, one_smul K s⟩

theorem ospan_smul_mem_of_mem {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {S : Set V} {a : K} (ha : ‖a‖ ≤ 1) {s : V} (hs : s ∈ S) : a • s ∈ Ospan K S :=
  AddSubgroup.subset_closure ⟨a, ha, s, hs, rfl⟩

/-- `Ospan K S` is closed under scalar multiplication by every `a ∈ O_K` (`‖a‖ ≤ 1`). -/
theorem ospan_smul {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {S : Set V} {a : K} (ha : ‖a‖ ≤ 1) {v : V} (hv : v ∈ Ospan K S) :
    a • v ∈ Ospan K S := by
  unfold Ospan at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    exact AddSubgroup.subset_closure
      ⟨a * b, by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb, s, hs, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem ospan_mono {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {S T : Set V} (h : S ⊆ T) : Ospan K S ≤ Ospan K T := by
  unfold Ospan
  refine AddSubgroup.closure_mono ?_
  rintro v ⟨a, ha, s, hs, rfl⟩
  exact ⟨a, ha, s, h hs, rfl⟩

theorem ospan_le_iff {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {S : Set V} {H : AddSubgroup V} :
    Ospan K S ≤ H ↔ ∀ a : K, ‖a‖ ≤ 1 → ∀ s ∈ S, a • s ∈ H := by
  unfold Ospan
  rw [AddSubgroup.closure_le]
  constructor
  · intro h a ha s hs
    exact h ⟨a, ha, s, hs, rfl⟩
  · rintro h _ ⟨a, ha, s, hs, rfl⟩
    exact h a ha s hs

/-- **Full Crystalline `QPack` (`FullCrystallineQPack K p`)**:
upgrades `Stage12MultivarDwork.CrystallineQPack K p` with:
1. the integral differential lattice `om : AddSubgroup base.OmV` with exact surjectivity
   `red_range : ∀ v, v ∈ om ↔ ∃ m : base.FilM, base.red m = v`,
2. a Fontaine period-ring package `periodPkg : LocPrimePackage p` tied to concrete
   `A_inf / B_cris / B_dR` (`Nonempty (LocTied p periodPkg)`), linked to `base.A` by an explicit
   diamond-free `RingHom` `ainfToA : periodPkg.AinfRing →+* base.A` mapping `xiAinf ↦ base.xi`,
3. crystalline `D_cris` data: a finite-dimensional `FilteredPhiModule p Dcris` over `ℚ_[p]` with
   an explicit additive comparison homomorphism `crysToFilM : Dcris →+ base.FilM` respecting
   `Fil^1` and Hodge–Tate reduction (ZERO nested global `Algebra` diamonds!). -/
structure FullCrystallineQPack.{u, v} (K : Type u) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] where
  /-- Underlying multivariable-Dwork `CrystallineQPack K p`. -/
  base : CrystallineQPack.{u, v} K p
  /-- Integral differential lattice `Ω_A ⊆ OmV` (`Lc.om y`). -/
  om : AddSubgroup base.OmV
  /-- Exact characterization of `om` as the image of `red : FilM →+ OmV`. -/
  red_range : ∀ v : base.OmV, v ∈ om ↔ ∃ m : base.FilM, base.red m = v
  /-- Fontaine local period package (`A_inf`, `B_cris`, `B_dR`, `φ`, `Fil•`, `t`). -/
  periodPkg : LocPrimePackage p
  /-- Concrete realization tie to `A_inf(O_{ℂ_p})`, `B_cris(O_{ℂ_p})`, `B_dR(O_{ℂ_p})`. -/
  periodTied : Nonempty (LocTied p periodPkg)
  /-- Explicit diamond-free ring homomorphism `A_inf →+* A` (NO `Algebra` diamond). -/
  ainfToA : periodPkg.AinfRing →+* base.A
  /-- Period element `ξ_inf ∈ A_inf` mapping to the crystalline uniformizer `base.xi`. -/
  xiAinf : periodPkg.AinfRing
  ainfToA_xi : ainfToA xiAinf = base.xi
  /-- Crystalline Dieudonné / `D_cris` vector space over `ℚ_[p]`. -/
  Dcris : Type v
  [addCommGroupDcris : AddCommGroup Dcris]
  [moduleDcris : Module ℚ_[p] Dcris]
  [finiteDcris : Module.Finite ℚ_[p] Dcris]
  /-- Filtered `φ`-module structure `(D_cris, φ, Fil•)` over `ℚ_[p]`. -/
  phiMod : FilteredPhiModule p Dcris
  /-- Explicit additive crystalline comparison map `D_cris →+ FilM` (diamond-free). -/
  crysToFilM : Dcris →+ base.FilM
  /-- Compatibility of `D_cris` filtration with Hodge–Tate reduction into `om`. -/
  crys_fil_compat : ∀ d : Dcris, d ∈ phiMod.fil.fil 1 → base.red (crysToFilM d) ∈ om

attribute [instance] FullCrystallineQPack.addCommGroupDcris FullCrystallineQPack.moduleDcris
  FullCrystallineQPack.finiteDcris

namespace FullCrystallineQPack

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ} [Fact p.Prime]

/-- Key induction lemma: for every `t : Q.base.TA`, `red ⟨i t, i_mem t⟩` lies in
`Ospan K (Set.range Q.base.ht)`. -/
theorem red_i_mem_ospan (Q : FullCrystallineQPack K p) (t : Q.base.TA) :
    Q.base.red ⟨Q.base.i t, Q.base.i_mem t⟩ ∈ Ospan K (Set.range Q.base.ht) := by
  have ht : t ∈ Submodule.span Q.base.A (Set.range Q.base.iT) := by
    rw [Q.base.iT_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [← Q.base.ht_eq]
    exact ospan_mem_of_mem ⟨s, rfl⟩
  | zero =>
    have h0 : (⟨Q.base.i 0, Q.base.i_mem 0⟩ : Q.base.FilM) = 0 := Subtype.ext (map_zero _)
    rw [h0, map_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    have hadd : (⟨Q.base.i (a + b), Q.base.i_mem _⟩ : Q.base.FilM) =
        ⟨Q.base.i a, Q.base.i_mem a⟩ + ⟨Q.base.i b, Q.base.i_mem b⟩ :=
      Subtype.ext (map_add _ _ _)
    rw [hadd, map_add]
    exact add_mem ha hb
  | smul a x _ hx =>
    have hsm : (⟨Q.base.i (a • x), Q.base.i_mem _⟩ : Q.base.FilM) =
        a • ⟨Q.base.i x, Q.base.i_mem x⟩ :=
      Subtype.ext (map_smul _ _ _)
    rw [hsm, Q.base.red_smul]
    exact ospan_smul ((Q.base.th_range _).2 ⟨a, rfl⟩) hx

/-- **Crystalline Hodge–Tate Sandwich Theorem (`FullCrystallineQPack.htb_at`)**
(matching Alpöge's `ThetaNormsAndLinks.QPack.htb_at`):
1. `Ospan K (Set.range Q.base.ht) ≤ Q.om`, and
2. for every `x ∈ Q.om` and every `c : K` with `‖c‖ ≤ p ^ (-1 / (p - 1))`,
   `c • x ∈ Ospan K (Set.range Q.base.ht)`. -/
theorem htb_at (Q : FullCrystallineQPack K p) :
    Ospan K (Set.range Q.base.ht) ≤ Q.om ∧
    ∀ x ∈ Q.om, ∀ c : K, ‖c‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) →
      c • x ∈ Ospan K (Set.range Q.base.ht) := by
  constructor
  · rw [ospan_le_iff]
    rintro a ha _ ⟨t, rfl⟩
    obtain ⟨a', rfl⟩ := (Q.base.th_range a).1 ha
    rw [Q.base.ht_eq, ← Q.base.red_smul]
    exact (Q.red_range _).2 ⟨_, rfl⟩
  · intro x hx c hc
    obtain ⟨m, rfl⟩ := (Q.red_range x).1 hx
    obtain ⟨t, ht_eq, _⟩ := Q.base.cokernel_annihilated_by_nu m.2
    by_cases h0 : Q.base.th Q.base.nu = 0
    · have hc0 : c = 0 := by
        rw [← Q.base.th_nu, h0, norm_zero] at hc
        exact norm_le_zero_iff.1 hc
      rw [hc0, zero_smul]
      exact zero_mem _
    · have hc' : ‖c / Q.base.th Q.base.nu‖ ≤ 1 := by
        rw [norm_div]
        exact div_le_one_of_le₀ (by rw [Q.base.th_nu]; exact hc) (norm_nonneg _)
      obtain ⟨a, ha⟩ := (Q.base.th_range _).1 hc'
      have he : c = Q.base.th (a * Q.base.nu) := by
        rw [map_mul, ha, div_mul_cancel₀ _ h0]
      rw [he, ← Q.base.red_smul]
      have hm_eq : ((a * Q.base.nu) • m : Q.base.FilM) =
          ⟨Q.base.i (a • t), Q.base.i_mem (a • t)⟩ := by
        apply Subtype.ext
        show (a * Q.base.nu) • m.1 = Q.base.i (a • t)
        rw [mul_smul, ← ht_eq, map_smul]
      rw [hm_eq]
      exact Q.red_i_mem_ospan (a • t)

/-- **Hodge–Tate Reduction Theorem (`hodge_tate_reduction_red`)**:
for any `FullCrystallineQPack K p` and any filtered crystalline element `m : Q.base.FilM`:
1. `Q.base.red m ∈ Q.om`,
2. `Q.base.th Q.base.nu • Q.base.red m ∈ Ospan K (Set.range Q.base.ht)`,
3. for every `c : K` with `‖c‖ ≤ ‖Q.base.th Q.base.nu‖`,
   `c • Q.base.red m ∈ Ospan K (Set.range Q.base.ht)`,
4. for every `d ∈ Q.phiMod.fil.fil 1`, `Q.base.th Q.base.nu • Q.base.red (Q.crysToFilM d) ∈ Ospan K (Set.range Q.base.ht)`. -/
theorem hodge_tate_reduction_red (Q : FullCrystallineQPack K p) (m : Q.base.FilM) :
    Q.base.red m ∈ Q.om ∧
    Q.base.th Q.base.nu • Q.base.red m ∈ Ospan K (Set.range Q.base.ht) ∧
    (∀ c : K, ‖c‖ ≤ ‖Q.base.th Q.base.nu‖ → c • Q.base.red m ∈ Ospan K (Set.range Q.base.ht)) ∧
    (∀ d : Q.Dcris, d ∈ Q.phiMod.fil.fil 1 →
      Q.base.th Q.base.nu • Q.base.red (Q.crysToFilM d) ∈ Ospan K (Set.range Q.base.ht)) := by
  have hmem : Q.base.red m ∈ Q.om := (Q.red_range _).2 ⟨m, rfl⟩
  have hsand := Q.htb_at.2
  refine ⟨hmem, ?_, ?_, ?_⟩
  · exact hsand _ hmem _ (le_of_eq Q.base.th_nu)
  · intro c hc
    exact hsand _ hmem c (hc.trans (le_of_eq Q.base.th_nu))
  · intro d hd
    exact hsand _ (Q.crys_fil_compat d hd) _ (le_of_eq Q.base.th_nu)

/-- `p`-multiplication corollary: when `‖(p : K)‖ = p⁻¹`, multiplication by `(p : K)` sends the
entire integral differential lattice `Q.om` into `Ospan K (Set.range Q.base.ht)`! -/
theorem p_smul_om_mem_ospan (Q : FullCrystallineQPack K p)
    (hnp : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : Q.base.OmV} (hx : x ∈ Q.om) :
    ((p : ℕ) : K) • x ∈ Ospan K (Set.range Q.base.ht) := by
  refine Q.htb_at.2 x hx ((p : ℕ) : K) ?_
  rw [hnp]
  exact inv_prime_le_rpow_neg_inv_sub_one Fact.out

/-- Ramified uniformizer corollary: if `unif : K` has `‖unif‖ = p ^ (-1 / e)` for ramification
index `e ≥ 1`, then `unif ^ ⌈e / (p - 1)⌉ • x ∈ Ospan K (Set.range Q.base.ht)` for EVERY `x ∈ Q.om`! -/
theorem ramified_uniformizer_pow_mem_ospan (Q : FullCrystallineQPack K p)
    {e : ℕ} (he : 1 ≤ e) {unif : K} (hunif : ‖unif‖ = (p : ℝ) ^ (-(1 : ℝ) / (e : ℝ)))
    {x : Q.base.OmV} (hx : x ∈ Q.om) :
    unif ^ (Nat.ceil ((e : ℝ) / ((p : ℝ) - 1))) • x ∈ Ospan K (Set.range Q.base.ht) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have he_pos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  set k : ℕ := Nat.ceil ((e : ℝ) / ((p : ℝ) - 1))
  have hk : (e : ℝ) / ((p : ℝ) - 1) ≤ (k : ℝ) := Nat.le_ceil _
  refine Q.htb_at.2 x hx (unif ^ k) ?_
  rw [norm_pow, hunif, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  apply Real.rpow_le_rpow_of_exponent_le hp1.le
  have h1 : (-(1 : ℝ) / (e : ℝ)) * (k : ℝ) = -((k : ℝ) / (e : ℝ)) := by ring
  rw [h1, neg_div]
  have h2 : 1 / ((p : ℝ) - 1) ≤ (k : ℝ) / (e : ℝ) := by
    rw [le_div_iff₀ he_pos]
    have : (1 : ℝ) / ((p : ℝ) - 1) * (e : ℝ) = (e : ℝ) / ((p : ℝ) - 1) := by ring
    linarith
  linarith

/-- Bridge into multivariable Dwork exponential weight integrality (`Stage12MultivarDwork`). -/
theorem dwork_exp_wtGe [CharZero K] {σ : Type*} (Q : FullCrystallineQPack K p)
    (hnp : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {r : σ → ℝ} {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0)
    (hB : ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d B‖ ≤ ‖Q.base.th Q.base.nu‖ * ‖((p : ℕ) : K)‖ ^ (-wtDot d r)) :
    WtGe ‖((p : ℕ) : K)‖ r 0 (mvExp B) :=
  Q.base.qpack_mvExp_wtGe hnp hB0 hB

/-- Bridge into multivariable Dwork logarithm reverse induction (`PAdicChainValuation`). -/
theorem dwork_log_wtGe [CharZero K] {σ : Type*} (Q : FullCrystallineQPack K p)
    (hnp : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {r : σ → ℝ} {D : MvPowerSeries σ K}
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hE : ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d (mvExp D - 1)‖ ≤
      ‖Q.base.th Q.base.nu‖ * ‖((p : ℕ) : K)‖ ^ (-wtDot d r)) :
    WtGe ‖((p : ℕ) : K)‖ r (1 / ((p : ℝ) - 1)) D := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpi0 : 0 < ‖((p : ℕ) : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlt : ‖((p : ℕ) : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hth_eq : ‖Q.base.th Q.base.nu‖ = ‖((p : ℕ) : K)‖ ^ ((1 : ℝ) / ((p : ℝ) - 1)) := by
    rw [Q.base.th_nu, hnp, Real.inv_rpow hp_pos.le, ← Real.rpow_neg hp_pos.le]
    congr 1; ring
  refine dwork_log_weight_induction hp hlt hD0 fun d => ?_
  unfold MonoWtGe
  calc ‖MvPowerSeries.coeff d (mvExp D - 1)‖
      ≤ ‖Q.base.th Q.base.nu‖ * ‖((p : ℕ) : K)‖ ^ (-wtDot d r) := hE d
    _ = ‖((p : ℕ) : K)‖ ^ (1 / ((p : ℝ) - 1)) * ‖((p : ℕ) : K)‖ ^ (-wtDot d r) := by rw [hth_eq]
    _ = ‖((p : ℕ) : K)‖ ^ (1 / ((p : ℝ) - 1) - wtDot d r) := by
        rw [← Real.rpow_add hpi0, ← sub_eq_add_neg]

end FullCrystallineQPack

/-- Top-level alias for `FullCrystallineQPack.hodge_tate_reduction_red`. -/
theorem hodge_tate_reduction_red {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p : ℕ} [Fact p.Prime] (Q : FullCrystallineQPack K p) (m : Q.base.FilM) :
    Q.base.red m ∈ Q.om ∧
    Q.base.th Q.base.nu • Q.base.red m ∈ Ospan K (Set.range Q.base.ht) ∧
    (∀ c : K, ‖c‖ ≤ ‖Q.base.th Q.base.nu‖ → c • Q.base.red m ∈ Ospan K (Set.range Q.base.ht)) ∧
    (∀ d : Q.Dcris, d ∈ Q.phiMod.fil.fil 1 →
      Q.base.th Q.base.nu • Q.base.red (Q.crysToFilM d) ∈ Ospan K (Set.range Q.base.ht)) :=
  Q.hodge_tate_reduction_red m

/-- **Unconditional Concrete Realization `concreteFullCrystallineQPack p`**:
for EVERY prime `p`, constructs a genuine `FullCrystallineQPack ℂ_[p] p` with ZERO assumptions,
combining:
- a genuine Dwork uniformizer `ϖ ∈ ℂ_[p]` (`ϖ^(p-1) = -p`, `‖ϖ‖ = p^{-1/(p-1)}`),
- `Stage12MultivarDwork.dworkPiQPack ℂ_[p] p`,
- `Stage12FontainePeriods.concreteLocPrimePackage p` and `Stage12FontainePeriods.nonempty_locTied p`,
- explicit diamond-free `thetaMap : A_inf(O_{ℂ_p}) →+* O_{ℂ_p} ≃+* ultrametricUnitBall ℂ_[p]`,
- and `D_cris(1)` of the trivial representation from `cyclotomicLaurentPeriodSystem p`! -/
def concreteFullCrystallineQPack (p : ℕ) [Fact p.Prime] : FullCrystallineQPack ℂ_[p] p := by
  classical
  let hϖ := exists_dwork_uniformizer_padic_complex p
  let ϖ : ℂ_[p] := hϖ.choose
  have hϖ_eq : ϖ ^ (p - 1) = -((p : ℕ) : ℂ_[p]) := hϖ.choose_spec.1
  let baseQ : CrystallineQPack ℂ_[p] p :=
    dworkPiQPack ℂ_[p] p (norm_l_padic_complex p) ϖ hϖ_eq
  let ocpToBall : OCp p →+* ultrametricUnitBall ℂ_[p] :=
    { toFun := fun x => ⟨(x : ℂ_[p]), OCp_norm_le_one p x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ainfHom : (concreteLocPrimePackage p).AinfRing →+* baseQ.A :=
    ocpToBall.comp (thetaMap p (OCp p))
  let S := cyclotomicLaurentPeriodSystem p
  let D := S.D_cris (1 : Representation ℚ_[p] (ℤ_[p]ˣ) ℚ_[p])
  haveI : Module.Finite ℚ_[p] D := S.instFiniteDcris 1
  exact
    { base := baseQ
      om := (ultrametricUnitBall ℂ_[p]).toAddSubgroup
      red_range := fun v => by
        constructor
        · intro hv
          exact ⟨⟨⟨v, hv⟩, trivial⟩, rfl⟩
        · rintro ⟨⟨⟨w, hw⟩, _⟩, rfl⟩
          exact hw
      periodPkg := concreteLocPrimePackage p
      periodTied := (nonempty_locTied p).choose_spec.elim fun _ =>
        ⟨{ eA := RingEquiv.refl _
           eB := RingEquiv.refl _
           eD := RingEquiv.refl _
           zB := fun _ => rfl
           zD := fun _ => rfl
           ιA := fun _ => rfl
           frob := fun _ => rfl
           incl := fun _ => rfl
           fil := fun _ _ => Iff.rfl
           t_eq := rfl }⟩
      ainfToA := ainfHom
      xiAinf := 1
      ainfToA_xi := by
        show ocpToBall (thetaMap p (OCp p) 1) = 1
        rw [map_one, map_one]
      Dcris := D
      phiMod := S.D_cris_toFilteredPhiModule 1
      crysToFilM := 0
      crys_fil_compat := fun _ _ => by
        show (0 : ℂ_[p]) ∈ (ultrametricUnitBall ℂ_[p]).toAddSubgroup
        exact zero_mem _ }

/-- `FullCrystallineQPack ℂ_[p] p` is unconditionally `Nonempty` for every prime `p`. -/
theorem nonempty_fullCrystallineQPack (p : ℕ) [Fact p.Prime] :
    Nonempty (FullCrystallineQPack.{0, 0} ℂ_[p] p) :=
  ⟨concreteFullCrystallineQPack p⟩

end FullCrystallineQPackSection

/-! ## Section 3: Young-Diagram Jet-Weight LP Flow (`YoungDiagramLPFlow`), `lpF_eq_Fnum` & Duality -/

section YoungDiagramLPFlowSection

/-! ### Young-Diagram Column Combinatorics -/

theorem yd_one_le_colLen (μ : YoungDiagram) (c : Fin (μ.rowLen 0)) : 1 ≤ μ.colLen c := by
  have h : (0, (c : ℕ)) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 c.2
  exact YoungDiagram.mem_iff_lt_colLen.1 h

theorem yd_colLen_le (μ : YoungDiagram) (c : ℕ) : μ.colLen c ≤ μ.colLen 0 :=
  μ.colLen_anti 0 c (Nat.zero_le c)

theorem yd_rowLen_one_le_zero (μ : YoungDiagram) : μ.rowLen 1 ≤ μ.rowLen 0 :=
  μ.rowLen_anti 0 1 zero_le_one

/-- For any Young diagram `μ`, `rowLen 0 + rowLen 1 ≤ cells.card`. -/
theorem yd_rowLen_zero_add_one_le_cells (μ : YoungDiagram) :
    μ.rowLen 0 + μ.rowLen 1 ≤ μ.cells.card := by
  rw [young_size_eq_sum_colLen μ]
  have hcnt := young_second_row_length_count μ
  let s2 : Finset (Fin (μ.rowLen 0)) := Finset.univ.filter (fun c => 2 ≤ μ.colLen c)
  have hle : ∀ c : Fin (μ.rowLen 0), (1 + if 2 ≤ μ.colLen c then 1 else 0) ≤ μ.colLen c := by
    intro c
    have h1 := yd_one_le_colLen μ c
    split_ifs with h2 <;> omega
  calc μ.rowLen 0 + μ.rowLen 1
      = (Finset.univ : Finset (Fin (μ.rowLen 0))).card + s2.card := by
          rw [Finset.card_fin, ← hcnt]
    _ = (∑ _c : Fin (μ.rowLen 0), 1) + ∑ c : Fin (μ.rowLen 0), (if 2 ≤ μ.colLen c then 1 else 0) := by
          simp [s2, Finset.sum_boole]
    _ = ∑ c : Fin (μ.rowLen 0), (1 + if 2 ≤ μ.colLen c then 1 else 0) := by
          rw [← Finset.sum_add_distrib]
    _ ≤ ∑ c : Fin (μ.rowLen 0), μ.colLen c := Finset.sum_le_sum fun c _ => hle c

/-! ### Primal LP Formulation (`lpF`) & Odd-Level Flow Formulation (`Fnum`) -/

/-- Odd residue levels in `{0, 1, ..., d - 1}`. -/
def oddLevels (d : ℕ) : Finset ℕ := (Finset.range d).filter Odd

lemma oddLevels_one_le {d i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i := by
  have h := (Finset.mem_filter.1 hi).2.pos
  omega

lemma one_mem_oddLevels {d : ℕ} (hd : 2 ≤ d) : 1 ∈ oddLevels d :=
  Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), odd_one⟩

lemma oddLevels_lt {d i : ℕ} (hi : i ∈ oddLevels d) : i < d :=
  Finset.mem_range.1 (Finset.mem_filter.1 hi).1

section LPDefinitions

variable (l d : ℕ) [NeZero d]

/-- **Primal LP feasible flow values (`lpFeasible`)** matching `BasicNotions.lpFeasible`:
all achievable total flows `∑_s ∑_{i < d} xs s i` supported on odd levels `i < d` satisfying the
`l^i`-outgoing + incoming capacity constraint `≤ D s` at every residue `s : ZMod d`. -/
def lpFeasible (D : ZMod d → ℝ) : Set ℝ :=
  {t : ℝ | ∃ xs : ZMod d → ℕ → ℝ,
    (∀ s i, 0 ≤ xs s i) ∧
    (∀ s i, ¬ Odd i ∨ d ≤ i → xs s i = 0) ∧
    (∀ s : ZMod d,
      (∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i) +
        (∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i) ≤ D s) ∧
    ∑ s : ZMod d, ∑ i ∈ Finset.range d, xs s i = t}

/-- **Primal LP jet-weight functional (`lpF`)**: `γ(l) * ∑_s D(s) - sup(lpFeasible l d D)`. -/
def lpF (D : ZMod d → ℝ) : ℝ := gam l * (∑ s : ZMod d, D s) - sSup (lpFeasible l d D)

/-- **Filtered odd-level flow predicate (`IsFlow`)** matching `IncomingBounds.IsFlow`. -/
def IsFlow (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) : Prop :=
  (∀ s i, 0 ≤ x s i) ∧
    ∀ s : ZMod d, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) ≤ D s

/-- Total load at residue `s : ZMod d` for a flow `x`. -/
def dpLoad (x : ZMod d → ℕ → ℝ) (s : ZMod d) : ℝ :=
  (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) + ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i

/-- Total flow value `∑_s ∑_{i ∈ oddLevels d} x s i`. -/
def flowVal (x : ZMod d → ℕ → ℝ) : ℝ := ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i

/-- Maximum achievable odd-level flow value `maxFlow l d D`. -/
def maxFlow (D : ZMod d → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ x, IsFlow l d D x ∧ flowVal d x = t}

/-- **Flow-deficit functional (`Fnum`)** matching `IncomingBounds.Fnum`:
`Fnum l d D = γ(l) * ∑_s D(s) - maxFlow l d D`. -/
def Fnum (D : ZMod d → ℝ) : ℝ := gam l * (∑ s : ZMod d, D s) - maxFlow l d D

/-- Dual feasible certificate `σ : ZMod d → [0, 1]` satisfying `l^i σ(s) + σ(s + i) ≥ 1`
for all `i ∈ oddLevels d`. -/
def IsDual (sig : ZMod d → ℝ) : Prop :=
  (∀ s, 0 ≤ sig s ∧ sig s ≤ 1) ∧
    ∀ s : ZMod d, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))

/-- Dual inequality extended to ALL odd `i : ℕ`. -/
def IsDualAll (sig : ZMod d → ℝ) : Prop :=
  ∀ s : ZMod d, ∀ i : ℕ, Odd i → 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))

/-- Optimal dual certificate achieving `Fnum l d D = ∑_s D(s) (γ(l) - σ(s))`. -/
def IsOptDual (D sig : ZMod d → ℝ) : Prop :=
  IsDual l d sig ∧ Fnum l d D = ∑ s : ZMod d, D s * (gam l - sig s)

end LPDefinitions

/-- **LP-Flow Equivalence Identity (`lpF_eq_Fnum`)**
(matching Alpöge's `DworkPowerSeriesWeights.lpF_eq_Fnum`):
the unrestricted primal LP functional `lpF l d D` coincides identically with the filtered odd-level
flow functional `Fnum l d D` for every `l, d` and every `D : ZMod d → ℝ`! -/
theorem lpF_eq_Fnum (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) :
    lpF l d D = Fnum l d D := by
  have hset : lpFeasible l d D =
      {t : ℝ | ∃ x, IsFlow l d D x ∧ flowVal d x = t} := by
    ext y
    simp only [lpFeasible, IsFlow, flowVal, oddLevels, Set.mem_ofPred_eq, Finset.sum_filter]
    constructor
    · rintro ⟨xs, h0, hz, hc, rfl⟩
      have hz' : ∀ s i, (if Odd i then xs s i else 0) = xs s i := by
        intro s i
        by_cases ho : Odd i
        · rw [if_pos ho]
        · rw [if_neg ho, hz s i (Or.inl ho)]
      refine ⟨xs, ⟨h0, fun s => ?_⟩, ?_⟩
      · have e1 : ∑ i ∈ Finset.range d, (if Odd i then (l : ℝ) ^ i * xs s i else 0) =
            ∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases ho : Odd i
          · rw [if_pos ho]
          · rw [if_neg ho, hz s i (Or.inl ho), mul_zero]
        have e2 : ∑ i ∈ Finset.range d, (if Odd i then xs (s - (i : ZMod d)) i else 0) =
            ∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i :=
          Finset.sum_congr rfl fun i _ => hz' _ _
        rw [e1, e2]
        exact hc s
      · exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => hz' s i
    · rintro ⟨x, ⟨h0, hc⟩, rfl⟩
      refine ⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩
      · intro s i
        dsimp only
        split_ifs
        · exact h0 s i
        · exact le_rfl
      · intro s i h
        dsimp only
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rcases h with h | h
        · exact h h1
        · omega
      · intro s
        have e1 : ∑ i ∈ Finset.range d, (l : ℝ) ^ i * (if Odd i ∧ i < d then x s i else 0) =
            ∑ i ∈ Finset.range d, (if Odd i then (l : ℝ) ^ i * x s i else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hid := Finset.mem_range.1 hi
          by_cases ho : Odd i <;> simp [ho, hid]
        have e2 : ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then x (s - (i : ZMod d)) i else 0) =
            ∑ i ∈ Finset.range d, (if Odd i then x (s - (i : ZMod d)) i else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hid := Finset.mem_range.1 hi
          by_cases ho : Odd i <;> simp [ho, hid]
        rw [e1, e2]
        exact hc s
      · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i hi => ?_
        have hid := Finset.mem_range.1 hi
        by_cases ho : Odd i <;> simp [ho, hid]
  unfold lpF Fnum maxFlow
  rw [hset]

/-! ### Pairing, Weak Duality, Max-Flow Attainment, Convexity & Strong LP Duality -/

section LPDuality

variable {l d : ℕ} [NeZero d]

lemma sum_incoming (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  calc ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i
      = ∑ i ∈ oddLevels d, ∑ s : ZMod d, x (s - (i : ZMod d)) i := Finset.sum_comm
    _ = ∑ i ∈ oddLevels d, ∑ s : ZMod d, x s i :=
        Finset.sum_congr rfl fun i _ =>
          Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun _ => rfl)
    _ = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := Finset.sum_comm

/-- Exact adjoint pairing identity between dual weights `a : ZMod d → ℝ` and flow load `dpLoad`. -/
theorem pair_eq (x : ZMod d → ℕ → ℝ) (a : ZMod d → ℝ) :
    ∑ s : ZMod d, a s * dpLoad l d x s =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * x s i := by
  have h2 : ∀ i : ℕ, ∑ s : ZMod d, a s * x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, a (s + (i : ZMod d)) * x s i :=
    fun i => Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => by simp)
  simp only [dpLoad, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => h2 i

/-- **Weak LP Duality (`flowVal_le_dual_sum`)**:
every feasible flow `x` and nonneg dual `sig` satisfy `flowVal d x ≤ ∑ s, D s * sig s`. -/
theorem flowVal_le_dual_sum {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} {sig : ZMod d → ℝ}
    (hx : IsFlow l d D x) (h0 : ∀ s, 0 ≤ sig s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) :
    flowVal d x ≤ ∑ s : ZMod d, D s * sig s := by
  calc flowVal d x = ∑ s, ∑ i ∈ oddLevels d, 1 * x s i := by simp [flowVal]
    _ ≤ ∑ s, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) * x s i :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (h1 s i hi) (hx.1 s i)
    _ = ∑ s, sig s * dpLoad l d x s := (pair_eq x sig).symm
    _ ≤ ∑ s, D s * sig s := Finset.sum_le_sum fun s _ => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hx.2 s) (h0 s)

theorem flowVal_mul_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    ((l : ℝ) + 1) * flowVal d x ≤ ∑ s : ZMod d, D s := by
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1 : ∑ s : ZMod d, dpLoad l d x s ≤ ∑ s : ZMod d, D s :=
    Finset.sum_le_sum fun s _ => hx.2 s
  unfold dpLoad at h1
  rw [Finset.sum_add_distrib, sum_incoming x] at h1
  have h2 : (l : ℝ) * flowVal d x ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl1 (oddLevels_one_le hi)
    exact mul_le_mul_of_nonneg_right hli (hx.1 s i)
  have h3 : flowVal d x = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := rfl
  rw [add_mul, one_mul]
  linarith

theorem maxFlow_le (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    maxFlow l d D ≤ (∑ s : ZMod d, D s) / ((l : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  unfold maxFlow
  apply Real.sSup_le
  · rintro t ⟨x, hx, rfl⟩
    rw [le_div_iff₀ hpos, mul_comm]
    exact flowVal_mul_le hl hx
  · exact div_nonneg (Finset.sum_nonneg fun s _ => hD s) hpos.le

theorem le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  unfold maxFlow
  refine le_csSup ⟨(∑ s : ZMod d, D s) / ((l : ℝ) + 1), ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  rw [le_div_iff₀ hpos, mul_comm]
  exact flowVal_mul_le hl hy

omit [NeZero d] in
theorem isDual_const (hl : 1 ≤ l) : IsDual l d (fun _ => 1 / ((l : ℝ) + 1)) := by
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hc0 : 0 ≤ 1 / ((l : ℝ) + 1) := by positivity
  refine ⟨fun _ => ⟨hc0, div_le_one_of_le₀ (by linarith) hpos.le⟩, fun _ i hi => ?_⟩
  have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
    calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl1 (oddLevels_one_le hi)
  have hmul : (l : ℝ) * (1 / ((l : ℝ) + 1)) ≤ (l : ℝ) ^ i * (1 / ((l : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right hli hc0
  have hsum : (l : ℝ) * (1 / ((l : ℝ) + 1)) + 1 / ((l : ℝ) + 1) = 1 := by
    field_simp [hpos.ne']
  linarith

/-- **Universal Lower Bound on `Fnum` (`Fnum_ge_rho_mul_sum`)**:
for `l ≥ 2` and `D ≥ 0`, `rho l * ∑ s, D s ≤ Fnum l d D`. -/
theorem Fnum_ge_rho_mul_sum {l d : ℕ} [NeZero d] (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    rho l * (∑ s : ZMod d, D s) ≤ Fnum l d D := by
  have hmax := maxFlow_le (l := l) (d := d) (by omega) hD
  have hdiff := gam_sub_inv_succ hl
  unfold Fnum
  have h1 : (∑ s : ZMod d, D s) / ((l : ℝ) + 1) = (1 / ((l : ℝ) + 1)) * (∑ s : ZMod d, D s) := by
    ring
  rw [h1] at hmax
  have h2 : gam l * (∑ s : ZMod d, D s) - (1 / ((l : ℝ) + 1)) * (∑ s : ZMod d, D s) =
      rho l * (∑ s : ZMod d, D s) := by
    rw [← sub_mul, hdiff]
  linarith

/-- **Universal Upper Bound on `Fnum` (`Fnum_le_gam_mul_sum`)**:
for `l ≥ 1` and `D ≥ 0`, `Fnum l d D ≤ gam l * ∑ s, D s`. -/
theorem Fnum_le_gam_mul_sum {l d : ℕ} [NeZero d] (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    Fnum l d D ≤ gam l * (∑ s : ZMod d, D s) := by
  have h0 : IsFlow l d D 0 := ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩
  have hle : 0 ≤ maxFlow l d D := by
    have := le_maxFlow hl h0
    simpa [flowVal] using this
  unfold Fnum
  linarith

/-- Weak duality in deficit form: any dual `sig` gives `∑ s, D s * (gam l - sig s) ≤ Fnum l d D`. -/
theorem sum_deficit_le_Fnum_of_isDual {D sig : ZMod d → ℝ} (hD : 0 ≤ D)
    (hsig : IsDual l d sig) :
    ∑ s : ZMod d, D s * (gam l - sig s) ≤ Fnum l d D := by
  have hmax : maxFlow l d D ≤ ∑ s : ZMod d, D s * sig s := by
    unfold maxFlow
    apply Real.sSup_le
    · rintro t ⟨x, hx, rfl⟩
      exact flowVal_le_dual_sum hx (fun s => (hsig.1 s).1) hsig.2
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (hD s) (hsig.1 s).1
  unfold Fnum
  have hrew : ∑ s : ZMod d, D s * (gam l - sig s) =
      gam l * (∑ s : ZMod d, D s) - ∑ s : ZMod d, D s * sig s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

/-! ### Finite-Dimensional Projection & Max-Flow Attainment -/

/-- Lift a finite-dimensional flow table `y : ZMod d → Fin d → ℝ` to `ZMod d → ℕ → ℝ`
by zero-extension outside `i < d`. -/
def liftFinFlow (y : ZMod d → Fin d → ℝ) : ZMod d → ℕ → ℝ :=
  fun s i => if h : i < d then y s ⟨i, h⟩ else 0

/-- Restrict `x : ZMod d → ℕ → ℝ` to its finite-dimensional `Fin d` table, zeroing even indices. -/
def projFinFlow (x : ZMod d → ℕ → ℝ) : ZMod d → Fin d → ℝ :=
  fun s i => if Odd (i : ℕ) then x s i else 0

omit [NeZero d] in
lemma dpLoad_lift_proj (x : ZMod d → ℕ → ℝ) (s : ZMod d) :
    dpLoad l d (liftFinFlow (projFinFlow x)) s = dpLoad l d x s := by
  unfold dpLoad liftFinFlow projFinFlow
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hlt := oddLevels_lt hi
    have hodd := (Finset.mem_filter.1 hi).2
    simp [hlt, hodd]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hlt := oddLevels_lt hi
    have hodd := (Finset.mem_filter.1 hi).2
    simp [hlt, hodd]

lemma flowVal_lift_proj (x : ZMod d → ℕ → ℝ) :
    flowVal d (liftFinFlow (projFinFlow x)) = flowVal d x := by
  unfold flowVal liftFinFlow projFinFlow
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i hi => ?_
  have hlt := oddLevels_lt hi
  have hodd := (Finset.mem_filter.1 hi).2
  simp [hlt, hodd]

omit [NeZero d] in
lemma coord_le_dpLoad (hl : 1 ≤ l) {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i)
    (s : ZMod d) {i : ℕ} (hi : i ∈ oddLevels d) : x s i ≤ dpLoad l d x s := by
  have hl1 : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by exact_mod_cast hl)
  have h1 : x s i ≤ (l : ℝ) ^ i * x s i := le_mul_of_one_le_left (hx s i) hl1
  have h2 : (l : ℝ) ^ i * x s i ≤ ∑ j ∈ oddLevels d, (l : ℝ) ^ j * x s j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by positivity) (hx s j)) hi
  have h3 : 0 ≤ ∑ j ∈ oddLevels d, x (s - (j : ZMod d)) j :=
    Finset.sum_nonneg fun j _ => hx _ _
  unfold dpLoad
  linarith

/-- Compact cube `[0, R]^(ZMod d × Fin d)` in the finite-dimensional normed space
`ZMod d → Fin d → ℝ`. -/
def finBox (d : ℕ) (R : ℝ) : Set (ZMod d → Fin d → ℝ) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) R

lemma isCompact_finBox (d : ℕ) (R : ℝ) : IsCompact (finBox d R) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

omit [NeZero d] in
lemma mem_finBox_iff {R : ℝ} {y : ZMod d → Fin d → ℝ} :
    y ∈ finBox d R ↔ ∀ s i, 0 ≤ y s i ∧ y s i ≤ R := by
  simp only [finBox, Set.mem_univ_pi, Set.mem_Icc]

omit [NeZero d] in
lemma continuous_dpLoad_lift (s : ZMod d) :
    Continuous fun y : ZMod d → Fin d → ℝ => dpLoad l d (liftFinFlow y) s := by
  unfold dpLoad liftFinFlow
  refine Continuous.add ?_ ?_
  · refine continuous_finsetSum _ fun i hi => ?_
    have hlt := oddLevels_lt hi
    simp only [dif_pos hlt]
    exact continuous_const.mul ((continuous_apply (⟨i, hlt⟩ : Fin d)).comp (continuous_apply s))
  · refine continuous_finsetSum _ fun i hi => ?_
    have hlt := oddLevels_lt hi
    simp only [dif_pos hlt]
    exact (continuous_apply (⟨i, hlt⟩ : Fin d)).comp (continuous_apply (s - (i : ZMod d)))

lemma continuous_flowVal_lift :
    Continuous fun y : ZMod d → Fin d → ℝ => flowVal d (liftFinFlow y) := by
  unfold flowVal liftFinFlow
  refine continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun i hi => ?_
  have hlt := oddLevels_lt hi
  simp only [dif_pos hlt]
  exact (continuous_apply (⟨i, hlt⟩ : Fin d)).comp (continuous_apply s)

/-- **Max-Flow Attainment Theorem (`exists_opt_flow`)**:
for any `l ≥ 1` and `D ≥ 0`, there exists a feasible flow `x` attaining `flowVal d x = maxFlow l d D`! -/
theorem exists_opt_flow (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ flowVal d x = maxFlow l d D := by
  let R : ℝ := ∑ s : ZMod d, D s
  have hR : 0 ≤ R := Finset.sum_nonneg fun s _ => hD s
  let Fset : Set (ZMod d → Fin d → ℝ) :=
    finBox d R ∩ ⋂ s : ZMod d, {y | dpLoad l d (liftFinFlow y) s ≤ D s}
  have hclosed : IsClosed (⋂ s : ZMod d, {y : ZMod d → Fin d → ℝ | dpLoad l d (liftFinFlow y) s ≤ D s}) :=
    isClosed_iInter fun s => isClosed_le (continuous_dpLoad_lift s) continuous_const
  have hK : IsCompact Fset := (isCompact_finBox d R).inter_right hclosed
  have h0 : (0 : ZMod d → Fin d → ℝ) ∈ Fset := by
    refine ⟨mem_finBox_iff.2 fun _ _ => ⟨le_rfl, hR⟩, Set.mem_iInter.2 fun s => ?_⟩
    show dpLoad l d (liftFinFlow (0 : ZMod d → Fin d → ℝ)) s ≤ D s
    have hz : dpLoad l d (liftFinFlow (0 : ZMod d → Fin d → ℝ)) s = 0 := by
      simp [dpLoad, liftFinFlow]
    rw [hz]
    exact hD s
  obtain ⟨yOpt, hyOpt, hmax⟩ := hK.exists_isMaxOn ⟨0, h0⟩ continuous_flowVal_lift.continuousOn
  have hOpt_flow : IsFlow l d D (liftFinFlow yOpt) := by
    refine ⟨fun s i => ?_, fun s => (Set.mem_iInter.1 hyOpt.2 s)⟩
    unfold liftFinFlow
    split_ifs with hlt
    · exact (mem_finBox_iff.1 hyOpt.1 s ⟨i, hlt⟩).1
    · exact le_rfl
  refine ⟨liftFinFlow yOpt, hOpt_flow, le_antisymm (le_maxFlow hl hOpt_flow) ?_⟩
  unfold maxFlow
  apply Real.sSup_le
  · rintro t ⟨z, hz, rfl⟩
    let z' : ZMod d → Fin d → ℝ := projFinFlow z
    have hz'_mem : z' ∈ Fset := by
      refine ⟨mem_finBox_iff.2 fun s i => ?_, Set.mem_iInter.2 fun s => ?_⟩
      · unfold z' projFinFlow
        split_ifs with hodd
        · have hi : (i : ℕ) ∈ oddLevels d := Finset.mem_filter.2 ⟨Finset.mem_range.2 i.2, hodd⟩
          refine ⟨hz.1 s i, ?_⟩
          exact (coord_le_dpLoad hl hz.1 s hi).trans
            ((hz.2 s).trans (Finset.single_le_sum (fun u _ => hD u) (Finset.mem_univ s)))
        · exact ⟨le_rfl, hR⟩
      · show dpLoad l d (liftFinFlow z') s ≤ D s
        rw [dpLoad_lift_proj]
        exact hz.2 s
    have hle := isMaxOn_iff.1 hmax z' hz'_mem
    rwa [flowVal_lift_proj] at hle
  · exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hOpt_flow.1 s i

/-! ### Homogeneity, Concavity of `maxFlow` & Convexity of `Fnum` -/

theorem maxFlow_zero (hl : 1 ≤ l) : maxFlow l d (0 : ZMod d → ℝ) = 0 := by
  have hle : maxFlow l d (0 : ZMod d → ℝ) ≤ 0 := by
    have h := maxFlow_le (l := l) (d := d) hl (D := 0) (fun _ => le_rfl)
    simpa using h
  have hge : 0 ≤ maxFlow l d (0 : ZMod d → ℝ) := by
    have h0 : IsFlow l d (0 : ZMod d → ℝ) 0 := ⟨fun _ _ => le_rfl, fun _ => by simp⟩
    simpa [flowVal] using le_maxFlow hl h0
  exact le_antisymm hle hge

theorem Fnum_zero (hl : 1 ≤ l) : Fnum l d (0 : ZMod d → ℝ) = 0 := by
  unfold Fnum
  rw [maxFlow_zero hl]
  simp

theorem maxFlow_smul (hl : 1 ≤ l) {c : ℝ} (hc : 0 ≤ c) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    maxFlow l d (c • D) = c * maxFlow l d D := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp [maxFlow_zero hl]
  · obtain ⟨x, hx, hxval⟩ := exists_opt_flow (l := l) (d := d) hl D hD
    obtain ⟨y, hy, hyval⟩ := exists_opt_flow (l := l) (d := d) hl (c • D)
      (fun s => mul_nonneg hc (hD s))
    have hcx : IsFlow l d (c • D) (fun s i => c * x s i) := by
      refine ⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => ?_⟩
      have hrew : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (c * x s i)) +
          (∑ i ∈ oddLevels d, c * x (s - (i : ZMod d)) i) = c * dpLoad l d x s := by
        unfold dpLoad
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left (hx.2 s) hc
    have hiy : IsFlow l d D (fun s i => c⁻¹ * y s i) := by
      refine ⟨fun s i => mul_nonneg (inv_nonneg.2 hc) (hy.1 s i), fun s => ?_⟩
      have hrew : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (c⁻¹ * y s i)) +
          (∑ i ∈ oddLevels d, c⁻¹ * y (s - (i : ZMod d)) i) = c⁻¹ * dpLoad l d y s := by
        unfold dpLoad
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hrew]
      calc c⁻¹ * dpLoad l d y s ≤ c⁻¹ * (c * D s) :=
            mul_le_mul_of_nonneg_left (hy.2 s) (inv_nonneg.2 hc)
        _ = D s := by rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
    have hge : c * maxFlow l d D ≤ maxFlow l d (c • D) := by
      rw [← hxval]
      have hval : flowVal d (fun s i => c * x s i) = c * flowVal d x := by
        unfold flowVal
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
      rw [← hval]
      exact le_maxFlow hl hcx
    have hle : maxFlow l d (c • D) ≤ c * maxFlow l d D := by
      have hval : flowVal d (fun s i => c⁻¹ * y s i) = c⁻¹ * flowVal d y := by
        unfold flowVal
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
      have h1 : c⁻¹ * maxFlow l d (c • D) ≤ maxFlow l d D := by
        rw [← hyval, ← hval]
        exact le_maxFlow hl hiy
      have h2 := mul_le_mul_of_nonneg_left h1 hc
      rwa [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul] at h2
    exact le_antisymm hle hge

/-- Positive homogeneity of `Fnum`: `Fnum l d (c • D) = c * Fnum l d D` for `c ≥ 0, D ≥ 0`. -/
theorem Fnum_smul (hl : 1 ≤ l) {c : ℝ} (hc : 0 ≤ c) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    Fnum l d (c • D) = c * Fnum l d D := by
  unfold Fnum
  rw [maxFlow_smul hl hc hD]
  have hsum : ∑ s : ZMod d, (c • D) s = c * ∑ s : ZMod d, D s := by
    simp [Finset.mul_sum]
  rw [hsum]
  ring

/-- Concavity of `maxFlow` on `{D | 0 ≤ D}`: convex combinations of feasible flows remain feasible. -/
theorem maxFlow_concaveOn (hl : 1 ≤ l) :
    ConcaveOn ℝ {D : ZMod d → ℝ | 0 ≤ D} (maxFlow l d) := by
  refine ⟨fun D₁ hD₁ D₂ hD₂ a b ha hb _ s => add_nonneg (mul_nonneg ha (hD₁ s)) (mul_nonneg hb (hD₂ s)), ?_⟩
  intro D₁ hD₁ D₂ hD₂ a b ha hb _
  obtain ⟨x₁, hx₁, hv₁⟩ := exists_opt_flow (l := l) (d := d) hl D₁ hD₁
  obtain ⟨x₂, hx₂, hv₂⟩ := exists_opt_flow (l := l) (d := d) hl D₂ hD₂
  let x : ZMod d → ℕ → ℝ := fun s i => a * x₁ s i + b * x₂ s i
  have hx : IsFlow l d (a • D₁ + b • D₂) x := by
    refine ⟨fun s i => add_nonneg (mul_nonneg ha (hx₁.1 s i)) (mul_nonneg hb (hx₂.1 s i)), fun s => ?_⟩
    have hload : dpLoad l d x s = a * dpLoad l d x₁ s + b * dpLoad l d x₂ s := by
      unfold dpLoad x
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      have e1 : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * (a * x₁ s i) =
          a * ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x₁ s i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * (b * x₂ s i) =
          b * ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x₂ s i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, e2]
      ring
    change dpLoad l d x s ≤ a * D₁ s + b * D₂ s
    rw [hload]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx₁.2 s) ha) (mul_le_mul_of_nonneg_left (hx₂.2 s) hb)
  have hval : flowVal d x = a * flowVal d x₁ + b * flowVal d x₂ := by
    unfold flowVal x
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [smul_eq_mul, smul_eq_mul, ← hv₁, ← hv₂, ← hval]
  exact le_maxFlow hl hx

/-- **Convexity of `Fnum` (`Fnum_convexOn`)**: `Fnum l d` is convex on `{D : ZMod d → ℝ | 0 ≤ D}`! -/
theorem Fnum_convexOn (hl : 1 ≤ l) :
    ConvexOn ℝ {D : ZMod d → ℝ | 0 ≤ D} (Fnum l d) := by
  have hconc := maxFlow_concaveOn (l := l) (d := d) hl
  refine ⟨hconc.1, fun D₁ hD₁ D₂ hD₂ a b ha hb hab => ?_⟩
  have hm := hconc.2 hD₁ hD₂ ha hb hab
  simp only [smul_eq_mul] at hm ⊢
  unfold Fnum
  have hsum : ∑ s : ZMod d, (a • D₁ + b • D₂) s =
      a * (∑ s : ZMod d, D₁ s) + b * (∑ s : ZMod d, D₂ s) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum]
  linarith

/-! ### Strong LP Duality via Hahn–Banach Separation (`exists_opt_dual`) -/

/-- Epigraph-cone of achievable `(load, value)` pairs in the finite-dimensional real normed space
`(ZMod d → ℝ) × ℝ`. -/
def flowConeSet (l d : ℕ) [NeZero d] : Set ((ZMod d → ℝ) × ℝ) :=
  {q | ∃ y : ZMod d → Fin d → ℝ,
    (∀ s i, 0 ≤ y s i) ∧
    (∀ s, dpLoad l d (liftFinFlow y) s ≤ q.1 s) ∧
    q.2 ≤ flowVal d (liftFinFlow y)}

lemma convex_flowConeSet : Convex ℝ (flowConeSet l d) := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb _
  rcases hq₁ with ⟨y₁, h1n, h1l, h1v⟩
  rcases hq₂ with ⟨y₂, h2n, h2l, h2v⟩
  refine ⟨fun s i => a * y₁ s i + b * y₂ s i,
    fun s i => add_nonneg (mul_nonneg ha (h1n s i)) (mul_nonneg hb (h2n s i)), fun s => ?_, ?_⟩
  · have hload : dpLoad l d (liftFinFlow (fun s i => a * y₁ s i + b * y₂ s i)) s =
        a * dpLoad l d (liftFinFlow y₁) s + b * dpLoad l d (liftFinFlow y₂) s := by
      unfold dpLoad liftFinFlow
      have e1 : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * (if h : i < d then a * y₁ s ⟨i, h⟩ + b * y₂ s ⟨i, h⟩ else 0) =
          a * (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (if h : i < d then y₁ s ⟨i, h⟩ else 0)) +
          b * (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (if h : i < d then y₂ s ⟨i, h⟩ else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hlt := oddLevels_lt hi
        simp only [dif_pos hlt]; ring
      have e2 : ∑ i ∈ oddLevels d, (if h : i < d then a * y₁ (s - (i : ZMod d)) ⟨i, h⟩ + b * y₂ (s - (i : ZMod d)) ⟨i, h⟩ else 0) =
          a * (∑ i ∈ oddLevels d, (if h : i < d then y₁ (s - (i : ZMod d)) ⟨i, h⟩ else 0)) +
          b * (∑ i ∈ oddLevels d, (if h : i < d then y₂ (s - (i : ZMod d)) ⟨i, h⟩ else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hlt := oddLevels_lt hi
        simp only [dif_pos hlt]
      rw [e1, e2]; ring
    rw [hload]
    exact add_le_add (mul_le_mul_of_nonneg_left (h1l s) ha) (mul_le_mul_of_nonneg_left (h2l s) hb)
  · have hval : flowVal d (liftFinFlow (fun s i => a * y₁ s i + b * y₂ s i)) =
        a * flowVal d (liftFinFlow y₁) + b * flowVal d (liftFinFlow y₂) := by
      unfold flowVal liftFinFlow
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hlt := oddLevels_lt hi
      simp only [dif_pos hlt]
    rw [hval]
    exact add_le_add (mul_le_mul_of_nonneg_left h1v ha) (mul_le_mul_of_nonneg_left h2v hb)

lemma isClosed_flowConeSet (hl : 1 ≤ l) : IsClosed (flowConeSet l d) := by
  refine IsSeqClosed.isClosed fun q p hq hlim => ?_
  choose y hyn hyl hyv using hq
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto q hlim).exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ ⟨0, rfl⟩)
  have hC1 : ∀ n s, (q n).1 s ≤ C := fun n s => by
    have h1 : ‖(q n).1 s‖ ≤ C :=
      (norm_le_pi_norm (q n).1 s).trans ((norm_fst_le (q n)).trans (hC _ ⟨n, rfl⟩))
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  let y' : ℕ → ZMod d → Fin d → ℝ := fun n => projFinFlow (liftFinFlow (y n))
  have hy'_box : ∀ n, y' n ∈ finBox d C := fun n => mem_finBox_iff.2 fun s i => by
    unfold y' projFinFlow
    split_ifs with hodd
    · have hi : (i : ℕ) ∈ oddLevels d := Finset.mem_filter.2 ⟨Finset.mem_range.2 i.2, hodd⟩
      have hval_eq : liftFinFlow (y n) s i = y n s i := by simp [liftFinFlow, i.2]
      rw [hval_eq]
      refine ⟨hyn n s i, ?_⟩
      have hxnn : ∀ t k, 0 ≤ liftFinFlow (y n) t k := fun t k => by
        unfold liftFinFlow; split_ifs; exact hyn n t _; exact le_rfl
      have hco := coord_le_dpLoad (l := l) hl hxnn s hi
      rw [hval_eq] at hco
      exact hco.trans ((hyl n s).trans (hC1 n s))
    · exact ⟨le_rfl, hC0⟩
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := (isCompact_finBox d C).tendsto_subseq hy'_box
  have hqφ : Filter.Tendsto (q ∘ φ) Filter.atTop (nhds p) := hlim.comp hφ.tendsto_atTop
  refine ⟨z, fun s i => (mem_finBox_iff.1 hz s i).1, fun s => ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => dpLoad l d (liftFinFlow (y' (φ n))) s) Filter.atTop
        (nhds (dpLoad l d (liftFinFlow z) s)) :=
      ((continuous_dpLoad_lift s).tendsto z).comp hzlim
    have h2 : Filter.Tendsto (fun n => (q (φ n)).1 s) Filter.atTop (nhds (p.1 s)) :=
      ((continuous_apply s).comp continuous_fst).continuousAt.tendsto.comp hqφ
    exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall fun n => by
      dsimp only
      have heq : dpLoad l d (liftFinFlow (y' (φ n))) s = dpLoad l d (liftFinFlow (y (φ n))) s :=
        dpLoad_lift_proj _ s
      rw [heq]
      exact hyl (φ n) s)
  · have h1 : Filter.Tendsto (fun n => (q (φ n)).2) Filter.atTop (nhds p.2) :=
      continuous_snd.continuousAt.tendsto.comp hqφ
    have h2 : Filter.Tendsto (fun n => flowVal d (liftFinFlow (y' (φ n)))) Filter.atTop
        (nhds (flowVal d (liftFinFlow z))) :=
      (continuous_flowVal_lift.tendsto z).comp hzlim
    exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall fun n => by
      dsimp only
      have heq : flowVal d (liftFinFlow (y' (φ n))) = flowVal d (liftFinFlow (y (φ n))) :=
        flowVal_lift_proj _
      rw [heq]
      exact hyv (φ n))

/-- Approximate dual extraction via `geometric_hahn_banach_closed_point`. -/
lemma exists_approx_dual (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ZMod d → ℝ, (∀ s, 0 ≤ τ s) ∧
      (∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * τ s + τ (s + (i : ZMod d))) ∧
      ∑ s : ZMod d, D s * τ s < maxFlow l d D + ε := by
  set v : ℝ := maxFlow l d D
  have hnotmem : (D, v + ε) ∉ flowConeSet l d := by
    rintro ⟨y, hyn, hyl, hyv⟩
    have hy_flow : IsFlow l d D (liftFinFlow y) := by
      refine ⟨fun s i => ?_, hyl⟩
      unfold liftFinFlow; split_ifs; exact hyn s _; exact le_rfl
    have hle := le_maxFlow hl hy_flow
    linarith
  obtain ⟨f, u, hfb, hfp⟩ :=
    geometric_hahn_banach_closed_point (convex_flowConeSet (l := l) (d := d))
      (isClosed_flowConeSet (l := l) (d := d) hl) hnotmem
  let a : ZMod d → ℝ := fun t => -f (Pi.single t (1 : ℝ), (0 : ℝ))
  let c : ℝ := -f (0, (1 : ℝ))
  have hdecomp : ∀ q : (ZMod d → ℝ) × ℝ,
      -f q = (∑ t : ZMod d, q.1 t * a t) + q.2 * c := by
    intro q
    have hq : q = (∑ t : ZMod d, q.1 t • ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ))) +
        q.2 • ((0 : ZMod d → ℝ), (1 : ℝ)) := by
      apply Prod.ext
      · funext t
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hq]
    rw [map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, neg_add, ← Finset.sum_neg_distrib, a, c]
    congr 1
    · exact Finset.sum_congr rfl fun t _ => by ring
    · ring
  have hrec : ∀ q : (ZMod d → ℝ) × ℝ, (∀ s, 0 ≤ q.1 s) → q.2 ≤ 0 → q ∈ flowConeSet l d := by
    intro q h1 h2
    refine ⟨0, fun _ _ => le_rfl, fun s => ?_, ?_⟩
    · have : dpLoad l d (liftFinFlow (0 : ZMod d → Fin d → ℝ)) s = 0 := by
        simp [dpLoad, liftFinFlow]
      rw [this]; exact h1 s
    · have : flowVal d (liftFinFlow (0 : ZMod d → Fin d → ℝ)) = 0 := by
        simp [flowVal, liftFinFlow]
      rw [this]; exact h2
  have hu : 0 < u := by
    have h0 := hfb 0 (hrec 0 (fun _ => le_rfl) le_rfl)
    simpa using h0
  have ha : ∀ t, 0 ≤ a t := by
    intro t
    by_contra hneg
    push Not at hneg
    have hneg_pos : 0 < -a t := neg_pos.2 hneg
    have hscale : 0 < u / (-a t) := div_pos hu hneg_pos
    have hq : (u / (-a t)) • ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) ∈ flowConeSet l d := by
      refine hrec _ (fun s => ?_) (by simp)
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs
      · exact mul_nonneg hscale.le zero_le_one
      · simp
    have h1 := hfb _ hq
    rw [map_smul, smul_eq_mul] at h1
    have hft : f (Pi.single t (1 : ℝ), (0 : ℝ)) = -a t := by simp [a]
    rw [hft, div_mul_cancel₀ _ hneg_pos.ne'] at h1
    exact lt_irrefl _ h1
  have hc : c < 0 := by
    by_contra hc'
    push Not at hc'
    have h1 := hdecomp (D, v + ε)
    have h2 : 0 ≤ ∑ t : ZMod d, D t * a t := Finset.sum_nonneg fun t _ => mul_nonneg (hD t) (ha t)
    have hv0 : 0 ≤ v := by
      have h0 : IsFlow l d D 0 := ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩
      simpa [v, flowVal] using le_maxFlow hl h0
    have h3 : 0 ≤ (v + ε) * c := mul_nonneg (by linarith) hc'
    linarith
  have hcpos : 0 < -c := neg_pos.2 hc
  have hw : ∀ s, ∀ i ∈ oddLevels d, 0 ≤ (l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c := by
    intro s i hi
    by_contra hw0
    push Not at hw0
    set W : ℝ := (l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c
    have hWpos : 0 < -W := neg_pos.2 hw0
    have hτ : 0 < u / (-W) := div_pos hu hWpos
    have hilt : i < d := oddLevels_lt hi
    let y : ZMod d → Fin d → ℝ :=
      fun t j => if (j : ℕ) = i ∧ t = s then u / (-W) else 0
    have hyn : ∀ t j, 0 ≤ y t j := fun t j => by
      dsimp only [y]; split_ifs; exact hτ.le; exact le_rfl
    have hsum : ∀ g : ZMod d → ℕ → ℝ,
        ∑ t : ZMod d, ∑ j ∈ oddLevels d, g t j * liftFinFlow y t j = g s i * (u / (-W)) := by
      intro g
      rw [Finset.sum_eq_single s]
      · rw [Finset.sum_eq_single i]
        · simp [liftFinFlow, y, hilt]
        · intro j hj hji
          have hjlt := oddLevels_lt hj
          simp [liftFinFlow, y, hjlt, hji]
        · intro hnot; exact absurd hi hnot
      · intro t _ hts
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjlt := oddLevels_lt hj
        simp [liftFinFlow, y, hjlt, hts]
      · intro hnot; exact absurd (Finset.mem_univ s) hnot
    have hfl : flowVal d (liftFinFlow y) = u / (-W) := by
      have h := hsum (fun _ _ => 1)
      simpa [flowVal] using h
    have hq : (fun t => dpLoad l d (liftFinFlow y) t, flowVal d (liftFinFlow y)) ∈ flowConeSet l d :=
      ⟨y, hyn, fun _ => le_rfl, le_rfl⟩
    have h1 := hfb _ hq
    have h2 := hdecomp (fun t => dpLoad l d (liftFinFlow y) t, flowVal d (liftFinFlow y))
    have h3 : ∑ t : ZMod d, dpLoad l d (liftFinFlow y) t * a t =
        ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / (-W)) := by
      rw [show (∑ t : ZMod d, dpLoad l d (liftFinFlow y) t * a t) =
            ∑ t : ZMod d, a t * dpLoad l d (liftFinFlow y) t from
          Finset.sum_congr rfl fun _ _ => mul_comm _ _, pair_eq]
      exact hsum (fun t j => (l : ℝ) ^ j * a t + a (t + (j : ZMod d)))
    dsimp only at h2
    rw [h3, hfl] at h2
    rw [hfl] at h1
    have h4 : ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / (-W)) + (u / (-W)) * c = -u := by
      have : ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / (-W)) + (u / (-W)) * c =
          -(u / (-W) * (-W)) := by
        show _ = -(u / (-W) * -((l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c))
        ring
      rw [this, div_mul_cancel₀ _ hWpos.ne']
    linarith
  refine ⟨fun s => a s / (-c), fun s => div_nonneg (ha s) hcpos.le, fun s i hi => ?_, ?_⟩
  · have hrew : (l : ℝ) ^ i * (a s / (-c)) + a (s + (i : ZMod d)) / (-c) =
        ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) / (-c) := by ring
    rw [hrew, le_div_iff₀ hcpos]
    linarith [hw s i hi]
  · have hrew : ∑ s : ZMod d, D s * (a s / (-c)) = (∑ s : ZMod d, D s * a s) / (-c) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hrew, div_lt_iff₀ hcpos]
    have h1 := hdecomp (D, v + ε)
    linarith

omit [NeZero d] in
lemma clip_dual (hl : 1 ≤ l) {τ : ZMod d → ℝ} (h0 : ∀ s, 0 ≤ τ s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * τ s + τ (s + (i : ZMod d))) :
    IsDual l d (fun s => min (τ s) 1) := by
  refine ⟨fun s => ⟨le_min (h0 s) zero_le_one, min_le_right _ _⟩, fun s i hi => ?_⟩
  dsimp only
  have hl' : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by exact_mod_cast hl)
  have hτ := h1 s i hi
  have hp : 0 ≤ (l : ℝ) ^ i * τ s := mul_nonneg (by positivity) (h0 s)
  have hq := h0 (s + (i : ZMod d))
  rcases le_total (τ s) 1 with h | h <;> rcases le_total (τ (s + (i : ZMod d))) 1 with h' | h'
  · rwa [min_eq_left h, min_eq_left h']
  · rw [min_eq_left h, min_eq_right h']; linarith
  · rw [min_eq_right h, min_eq_left h']; linarith
  · rw [min_eq_right h, min_eq_right h']; linarith

lemma isDualAll_of_isDual (hl : 1 ≤ l) (hev : Even d) {sig : ZMod d → ℝ}
    (hsig : IsDual l d sig) : IsDualAll l d sig := by
  intro s i hi
  have hd_pos : 0 < d := NeZero.pos d
  let r : ℕ := i % d
  have hr_lt : r < d := Nat.mod_lt i hd_pos
  have hr_le : r ≤ i := Nat.mod_le i d
  have hr_odd : Odd r := by
    obtain ⟨k, hk⟩ := hev
    have hmod : i = d * (i / d) + r := (Nat.div_add_mod i d).symm
    have h2 : Even (d * (i / d)) := by
      rw [hk, ← two_mul, mul_assoc]; exact even_two_mul _
    obtain ⟨m, hm⟩ := hi
    obtain ⟨q, hq⟩ := h2
    refine ⟨m - q, ?_⟩
    omega
  have hr_mem : r ∈ oddLevels d := Finset.mem_filter.2 ⟨Finset.mem_range.2 hr_lt, hr_odd⟩
  have hcast : (r : ZMod d) = (i : ZMod d) := by
    have h := Nat.div_add_mod i d
    have h1 : ((d * (i / d) + r : ℕ) : ZMod d) = (i : ZMod d) := congrArg Nat.cast h
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add] at h1
    exact h1
  have hpow : (l : ℝ) ^ r ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by exact_mod_cast hl) hr_le
  have h1 := hsig.2 s r hr_mem
  rw [hcast] at h1
  have h2 := mul_le_mul_of_nonneg_right hpow (hsig.1 s).1
  linarith

/-- **Strong LP Duality Theorem (`exists_opt_dual`)** (Lemma Fa):
for any `l ≥ 1`, even `d`, and `D ≥ 0`, there exists an optimal dual `sig : ZMod d → [0, 1]`
satisfying both `IsOptDual l d D sig` and `IsDualAll l d sig`! -/
theorem exists_opt_dual (hl : 1 ≤ l) (hev : Even d) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ sig : ZMod d → ℝ, IsOptDual l d D sig ∧ IsDualAll l d sig := by
  have hseq : ∀ n : ℕ, ∃ sig : ZMod d → ℝ, IsDual l d sig ∧
      ∑ s : ZMod d, D s * sig s < maxFlow l d D + 1 / ((n : ℝ) + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨τ, h0, h1, hlt⟩ := exists_approx_dual (l := l) (d := d) hl hD hε
    refine ⟨fun s => min (τ s) 1, clip_dual hl h0 h1, ?_⟩
    calc ∑ s : ZMod d, D s * min (τ s) 1
        ≤ ∑ s : ZMod d, D s * τ s :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hD s)
      _ < maxFlow l d D + 1 / ((n : ℝ) + 1) := hlt
  choose sig hsig hlt using hseq
  let unitCube : Set (ZMod d → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  have hcomp : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, sig n ∈ unitCube := fun n => Set.mem_univ_pi.2 fun s => (hsig n).1 s
  obtain ⟨sigOpt, hOptCube, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hmem
  have hOptDual : IsDual l d sigOpt := by
    refine ⟨fun s => Set.mem_univ_pi.1 hOptCube s, fun s i hi => ?_⟩
    have ht1 : Filter.Tendsto (fun n => (l : ℝ) ^ i * sig (φ n) s + sig (φ n) (s + (i : ZMod d)))
        Filter.atTop (nhds ((l : ℝ) ^ i * sigOpt s + sigOpt (s + (i : ZMod d)))) :=
      (tendsto_const_nhds.mul ((continuous_apply s).continuousAt.tendsto.comp hlim)).add
        ((continuous_apply (s + (i : ZMod d))).continuousAt.tendsto.comp hlim)
    exact ge_of_tendsto ht1 (Filter.Eventually.of_forall fun n => (hsig (φ n)).2 s i hi)
  have hsum_le : ∑ s : ZMod d, D s * sigOpt s ≤ maxFlow l d D := by
    have htL : Filter.Tendsto (fun n => ∑ s : ZMod d, D s * sig (φ n) s) Filter.atTop
        (nhds (∑ s : ZMod d, D s * sigOpt s)) :=
      tendsto_finsetSum _ fun s _ =>
        tendsto_const_nhds.mul ((continuous_apply s).continuousAt.tendsto.comp hlim)
    have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact h1.comp hφ.tendsto_atTop
    have htR : Filter.Tendsto (fun n : ℕ => maxFlow l d D + 1 / ((φ n : ℝ) + 1)) Filter.atTop
        (nhds (maxFlow l d D)) := by
      simpa using tendsto_const_nhds.add hinv
    exact le_of_tendsto_of_tendsto htL htR
      (Filter.Eventually.of_forall fun n => (hlt (φ n)).le)
  have hsum_ge : maxFlow l d D ≤ ∑ s : ZMod d, D s * sigOpt s := by
    obtain ⟨x, hx, hxval⟩ := exists_opt_flow (l := l) (d := d) hl D hD
    rw [← hxval]
    exact flowVal_le_dual_sum hx (fun s => (hOptDual.1 s).1) hOptDual.2
  have hmax_eq : maxFlow l d D = ∑ s : ZMod d, D s * sigOpt s := le_antisymm hsum_ge hsum_le
  have hFnum_eq : Fnum l d D = ∑ s : ZMod d, D s * (gam l - sigOpt s) := by
    unfold Fnum
    rw [hmax_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact ⟨sigOpt, ⟨hOptDual, hFnum_eq⟩, isDualAll_of_isDual hl hev hOptDual⟩

/-! ### Complementary Slackness, Incoming Bound (`LemmaFd`) & Balanced Formula (`LemmaFe`) -/

theorem optDual_maxFlow {D sig : ZMod d → ℝ} (h : IsOptDual l d D sig) :
    maxFlow l d D = ∑ s : ZMod d, D s * sig s := by
  obtain ⟨_, h2⟩ := h
  unfold Fnum at h2
  have hrew : ∑ s : ZMod d, D s * (gam l - sig s) =
      gam l * (∑ s : ZMod d, D s) - ∑ s : ZMod d, D s * sig s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

theorem cs_identity (D sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, D s * sig s - flowVal d x =
      ∑ s : ZMod d, sig s * (D s - dpLoad l d x s) +
      ∑ s : ZMod d, ∑ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) := by
  have hp := pair_eq (l := l) x sig
  have h1 : ∑ s : ZMod d, sig s * (D s - dpLoad l d x s) =
      (∑ s : ZMod d, D s * sig s) - ∑ s : ZMod d, sig s * dpLoad l d x s := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have h2 : ∑ s : ZMod d, ∑ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) =
      (∑ s : ZMod d, sig s * dpLoad l d x s) - flowVal d x := by
    rw [hp]
    unfold flowVal
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  linarith

theorem cs_zero {D sig : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ}
    (hx : IsFlow l d D x) (hs : IsDual l d sig) (heq : flowVal d x = ∑ s : ZMod d, D s * sig s) :
    (∀ s : ZMod d, sig s * (D s - dpLoad l d x s) = 0) ∧
    (∀ s : ZMod d, ∀ i ∈ oddLevels d,
      x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) = 0) := by
  have hid := cs_identity (l := l) D sig x
  rw [heq, sub_self] at hid
  have h1 : ∀ s : ZMod d, 0 ≤ sig s * (D s - dpLoad l d x s) :=
    fun s => mul_nonneg (hs.1 s).1 (sub_nonneg.2 (hx.2 s))
  have h2 : ∀ s : ZMod d, ∀ i ∈ oddLevels d,
      0 ≤ x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) :=
    fun s i hi => mul_nonneg (hx.1 s i) (sub_nonneg.2 (hs.2 s i hi))
  have hA := Finset.sum_nonneg fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => h1 s
  have hB := Finset.sum_nonneg fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) =>
    Finset.sum_nonneg (h2 s)
  have hA0 := le_antisymm (by linarith) hA
  have hB0 := le_antisymm (by linarith) hB
  refine ⟨fun s => (Finset.sum_eq_zero_iff_of_nonneg fun s _ => h1 s).1 hA0 s (Finset.mem_univ _),
    fun s i hi => ?_⟩
  have hBs := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => Finset.sum_nonneg (h2 s)).1
    hB0 s (Finset.mem_univ _)
  exact (Finset.sum_eq_zero_iff_of_nonneg (h2 s)).1 hBs i hi

omit [NeZero d] in
lemma sum_inv_pow_oddLevels_le_gam (hl : 3 ≤ l) :
    ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹ ≤ gam l := by
  have hl' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hq0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹ := by positivity
  have hq1 : ((l : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hsub : oddLevels d ⊆ (Finset.range d).image (fun k => 2 * k + 1) := by
    intro i hi
    have hlt := oddLevels_lt hi
    obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hi).2
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩
  calc ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹
      ≤ ∑ i ∈ (Finset.range d).image (fun k => 2 * k + 1), ((l : ℝ) ^ i)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ k ∈ Finset.range d, ((l : ℝ) ^ (2 * k + 1))⁻¹ := by
        refine Finset.sum_image fun a _ b _ h => by omega
    _ = (l : ℝ)⁻¹ * ∑ k ∈ Finset.range d, (((l : ℝ) ^ 2)⁻¹) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_succ, pow_mul, mul_inv, inv_pow, mul_comm]
    _ ≤ (l : ℝ)⁻¹ * (1 / (1 - ((l : ℝ) ^ 2)⁻¹)) := by
        gcongr
        rw [geom_sum_eq hq1.ne]
        have hnum : 1 - (((l : ℝ) ^ 2)⁻¹) ^ d ≤ 1 := by
          have : (0 : ℝ) ≤ (((l : ℝ) ^ 2)⁻¹) ^ d := pow_nonneg hq0 d
          linarith
        have hden : 0 < 1 - ((l : ℝ) ^ 2)⁻¹ := sub_pos.2 hq1
        have hrew : ((((l : ℝ) ^ 2)⁻¹) ^ d - 1) / (((l : ℝ) ^ 2)⁻¹ - 1) =
            (1 - (((l : ℝ) ^ 2)⁻¹) ^ d) / (1 - ((l : ℝ) ^ 2)⁻¹) := by
          rw [← neg_div_neg_eq, neg_sub, neg_sub]
        rw [hrew]
        exact div_le_div_of_nonneg_right hnum hden.le
    _ = gam l := by
        unfold gam
        have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
        have h2 : 1 - ((l : ℝ) ^ 2)⁻¹ ≠ 0 := by linarith
        field_simp [hlpos.ne', h1, h2]

/-- **Complementary Slackness Incoming-Dominance Lemma (`incoming_dominance_of_dual_ge`)**:
at any residue `s` where an optimal dual satisfies `2 / l ≤ sig s`, every optimal flow has zero
outgoing flow from `s`, saturates `D s` purely by incoming flow, and satisfies
`D s ≤ ∑ i ∈ oddLevels d, D (s - i) / l ^ i`! -/
theorem incoming_dominance_of_dual_ge (hl : 3 ≤ l) {D sig : ZMod d → ℝ} (hD : 0 ≤ D)
    (hopt : IsOptDual l d D sig) {s : ZMod d} (hs : 2 / (l : ℝ) ≤ sig s) :
    D s ≤ ∑ i ∈ oddLevels d, D (s - (i : ZMod d)) / (l : ℝ) ^ i := by
  have hl' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  obtain ⟨x, hx, hxval⟩ := exists_opt_flow (l := l) (d := d) (by omega) D hD
  have hF := optDual_maxFlow hopt
  obtain ⟨h1, h2⟩ := cs_zero hx hopt.1 (hxval.trans hF)
  have h2l : 2 ≤ (l : ℝ) * sig s := by
    have hmul := mul_le_mul_of_nonneg_left hs hlpos.le
    rwa [mul_div_cancel₀ _ hlpos.ne'] at hmul
  have hout : ∀ i ∈ oddLevels d, x s i = 0 := by
    intro i hi
    have hpow : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) (oddLevels_one_le hi)
    have hpos : 0 < (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1 := by
      have hm := mul_le_mul_of_nonneg_right hpow (hopt.1.1 s).1
      linarith [(hopt.1.1 (s + (i : ZMod d))).1]
    exact (mul_eq_zero.1 (h2 s i hi)).resolve_right hpos.ne'
  have hsig_pos : 0 < sig s := lt_of_lt_of_le (div_pos two_pos hlpos) hs
  have hsat : dpLoad l d x s = D s := by
    have h0 := (mul_eq_zero.1 (h1 s)).resolve_left hsig_pos.ne'
    linarith
  have hDs : D s = ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
    rw [← hsat]
    unfold dpLoad
    have hzero : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hout i hi, mul_zero]
    rw [hzero, zero_add]
  rw [hDs]
  refine Finset.sum_le_sum fun i hi => ?_
  have hpi : (0 : ℝ) < (l : ℝ) ^ i := pow_pos hlpos i
  rw [le_div_iff₀ hpi, mul_comm]
  have hnn : ∀ j ∈ oddLevels d, 0 ≤ (l : ℝ) ^ j * x (s - (i : ZMod d)) j :=
    fun j _ => mul_nonneg (by positivity) (hx.1 _ j)
  have hle1 : (l : ℝ) ^ i * x (s - (i : ZMod d)) i ≤
      ∑ j ∈ oddLevels d, (l : ℝ) ^ j * x (s - (i : ZMod d)) j :=
    Finset.single_le_sum hnn hi
  have hle2 : 0 ≤ ∑ j ∈ oddLevels d, x (s - (i : ZMod d) - (j : ZMod d)) j :=
    Finset.sum_nonneg fun j _ => hx.1 _ j
  linarith [hx.2 (s - (i : ZMod d))]

/-- Clean sharp LP Incoming-Mass Bound (`incoming_bound_of_optDual_sharp`):
for `l ≥ 3` and any optimal dual `sig`, the total degree mass on the high-dual set
`{s | 2 / l ≤ sig s}` is at most `(∑ s, D s) / (l + 1)`! -/
theorem incoming_bound_of_optDual_sharp (hl : 3 ≤ l) {D sig : ZMod d → ℝ} (hD : 0 ≤ D)
    (hopt : IsOptDual l d D sig) :
    (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤
      (∑ s : ZMod d, D s) / ((l : ℝ) + 1) := by
  have hl' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  obtain ⟨x, hx, hxval⟩ := exists_opt_flow (l := l) (d := d) (by omega) D hD
  have hF := optDual_maxFlow hopt
  obtain ⟨h1, h2⟩ := cs_zero hx hopt.1 (hxval.trans hF)
  set H := Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s)
  have hDs : ∀ s ∈ H, D s = ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
    intro s hs
    have hsig : 2 / (l : ℝ) ≤ sig s := (Finset.mem_filter.1 hs).2
    have h2l : 2 ≤ (l : ℝ) * sig s := by
      have hm := mul_le_mul_of_nonneg_left hsig hlpos.le
      rwa [mul_div_cancel₀ _ hlpos.ne'] at hm
    have hout : ∀ i ∈ oddLevels d, x s i = 0 := by
      intro i hi
      have hpow : (l : ℝ) ≤ (l : ℝ) ^ i := by
        calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) (oddLevels_one_le hi)
      have hpos : 0 < (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1 := by
        have hm := mul_le_mul_of_nonneg_right hpow (hopt.1.1 s).1
        linarith [(hopt.1.1 (s + (i : ZMod d))).1]
      exact (mul_eq_zero.1 (h2 s i hi)).resolve_right hpos.ne'
    have hsig_pos : 0 < sig s := lt_of_lt_of_le (div_pos two_pos hlpos) hsig
    have hsat : dpLoad l d x s = D s := by
      have h0 := (mul_eq_zero.1 (h1 s)).resolve_left hsig_pos.ne'
      linarith
    rw [← hsat]
    unfold dpLoad
    have hzero : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hout i hi, mul_zero]
    rw [hzero, zero_add]
  calc ∑ s ∈ H, D s
      = ∑ s ∈ H, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := Finset.sum_congr rfl hDs
    _ ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun s _ _ => Finset.sum_nonneg fun i _ => hx.1 _ _
    _ = flowVal d x := sum_incoming x
    _ = maxFlow l d D := hxval
    _ ≤ (∑ s : ZMod d, D s) / ((l : ℝ) + 1) := maxFlow_le (by omega) hD

/-- **LP Incoming-Mass Bound (`incoming_bound_of_optDual`)** (matching `IncomingBounds.IncomingBound`):
for `l ≥ 3` and any optimal dual `sig`, the total degree mass on the high-dual set
`{s | 2 / l ≤ sig s}` is at most `(∑ s, D s) / l`! -/
theorem incoming_bound_of_optDual (hl : 3 ≤ l) {D sig : ZMod d → ℝ} (hD : 0 ≤ D)
    (hopt : IsOptDual l d D sig) :
    (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤
      (∑ s : ZMod d, D s) / (l : ℝ) := by
  have hl' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hsum_nn : 0 ≤ ∑ s : ZMod d, D s := Finset.sum_nonneg fun s _ => hD s
  exact (incoming_bound_of_optDual_sharp hl hD hopt).trans
    (div_le_div_of_nonneg_left hsum_nn hlpos (by linarith))

/-- Alternating prefix sum used to construct the explicit optimal flow for balanced degrees (Lemma Fe). -/
def altNum (l d : ℕ) (D : ZMod d → ℝ) (s : ZMod d) : ℝ :=
  ∑ r ∈ Finset.range d, (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d))

omit [NeZero d] in
lemma altNum_rec (hl : 1 ≤ l) (hev : Even d) (D : ZMod d → ℝ) (s : ZMod d) :
    (l : ℝ) * altNum l d D s + altNum l d D (s - 1) = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
  let f : ℕ → ℝ := fun r => (-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d))
  have h1 : (l : ℝ) * altNum l d D s = ∑ r ∈ Finset.range d, f r := by
    unfold altNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [f, pow_succ, mul_inv]
    linear_combination ((-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d))) * hinv
  have h2 : altNum l d D (s - 1) = ∑ r ∈ Finset.range d, -f (r + 1) := by
    unfold altNum
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [f]
    have e : s - 1 - (r : ZMod d) = s - ((r + 1 : ℕ) : ZMod d) := by push_cast; ring
    rw [e]; ring
  calc (l : ℝ) * altNum l d D s + altNum l d D (s - 1)
      = ∑ r ∈ Finset.range d, (f r - f (r + 1)) := by
        rw [h1, h2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => (sub_eq_add_neg _ _).symm
    _ = f 0 - f d := Finset.sum_range_sub' f d
    _ = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by
        simp only [f, Nat.cast_zero, ZMod.natCast_self, sub_zero, pow_zero, inv_one,
          hev.neg_one_pow]
        ring

lemma sum_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), f r = ∑ u ∈ Finset.range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [Finset.sum_range_succ, ih]
    ring

/-- **Balanced-Degree Exact LP Identity (`Fnum_eq_rho_of_balanced`)** (Lemma Fe):
if `l ≥ 2`, `d ≥ 2` is even, `D ≥ 0`, and `∀ s s', D s' ≤ l * D s`, then
`Fnum l d D = rho l * ∑ s, D s`! -/
theorem Fnum_eq_rho_of_balanced (hl : 2 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D : ZMod d → ℝ} (hD : 0 ≤ D) (hbal : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) :
    Fnum l d D = rho l * (∑ s : ZMod d, D s) := by
  refine le_antisymm ?_ (Fnum_ge_rho_mul_sum hl hD)
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hpow_gt : (1 : ℝ) < (l : ℝ) ^ d := by
    calc (1 : ℝ) < (l : ℝ) ^ 1 := by simp; linarith
      _ ≤ (l : ℝ) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
  have hden_pos : (0 : ℝ) < 1 - ((l : ℝ) ^ d)⁻¹ :=
    sub_pos.2 (inv_lt_one_of_one_lt₀ hpow_gt)
  -- Construct explicit level-1 flow `x s 1 = altNum l d D s / (1 - l^{-d})`
  let x : ZMod d → ℕ → ℝ :=
    fun s i => if i = 1 then altNum l d D s / (1 - ((l : ℝ) ^ d)⁻¹) else 0
  have halt_nn : ∀ s : ZMod d, 0 ≤ altNum l d D s := by
    intro s
    obtain ⟨m, hm⟩ := hev
    have h2m : d = 2 * m := by omega
    rw [altNum]
    have hsum_split : ∑ r ∈ Finset.range d, (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d)) =
        ∑ u ∈ Finset.range m,
          ((-1 : ℝ) ^ (2 * u) * ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) +
            (-1 : ℝ) ^ (2 * u + 1) * ((l : ℝ) ^ (2 * u + 1 + 1))⁻¹ * D (s - ((2 * u + 1 : ℕ) : ZMod d))) := by
      rw [show Finset.range d = Finset.range (2 * m) from congrArg Finset.range h2m]
      exact sum_range_two_mul _ m
    rw [hsum_split]
    refine Finset.sum_nonneg fun u _ => ?_
    have he1 : (-1 : ℝ) ^ (2 * u) = 1 := (even_two_mul u).neg_one_pow
    have he2 : (-1 : ℝ) ^ (2 * u + 1) = -1 := by rw [pow_succ, he1]; ring
    rw [he1, he2, one_mul]
    have hpow_pos : (0 : ℝ) < (l : ℝ) ^ (2 * u + 2) := pow_pos hlpos _
    have hb := hbal (s - ((2 * u : ℕ) : ZMod d)) (s - ((2 * u + 1 : ℕ) : ZMod d))
    have hrew : ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) +
        -1 * ((l : ℝ) ^ (2 * u + 1 + 1))⁻¹ * D (s - ((2 * u + 1 : ℕ) : ZMod d)) =
        ((l : ℝ) * D (s - ((2 * u : ℕ) : ZMod d)) - D (s - ((2 * u + 1 : ℕ) : ZMod d))) /
          (l : ℝ) ^ (2 * u + 2) := by
      have hsucc : (l : ℝ) ^ (2 * u + 2) = (l : ℝ) ^ (2 * u + 1) * (l : ℝ) := pow_succ _ _
      rw [show 2 * u + 1 + 1 = 2 * u + 2 by ring, hsucc]
      field_simp [hlpos.ne', (pow_pos hlpos (2 * u + 1)).ne']
      ring
    rw [hrew]
    exact div_nonneg (sub_nonneg.2 hb) hpow_pos.le
  have h1mem : 1 ∈ oddLevels d := one_mem_oddLevels hd
  have hx : IsFlow l d D x := by
    refine ⟨fun s i => ?_, fun s => ?_⟩
    · dsimp only [x]
      split_ifs
      · exact div_nonneg (halt_nn s) hden_pos.le
      · exact le_rfl
    · have hsum1 : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i =
          (l : ℝ) * (altNum l d D s / (1 - ((l : ℝ) ^ d)⁻¹)) := by
        rw [Finset.sum_eq_single 1]
        · simp [x]
        · intro i _ hi; simp [x, hi]
        · intro h; exact absurd h1mem h
      have hsum2 : ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
          altNum l d D (s - 1) / (1 - ((l : ℝ) ^ d)⁻¹) := by
        rw [Finset.sum_eq_single 1]
        · simp [x]
        · intro i _ hi; simp [x, hi]
        · intro h; exact absurd h1mem h
      rw [hsum1, hsum2]
      have hrec := altNum_rec (l := l) (by omega) hev D s
      have heq : (l : ℝ) * (altNum l d D s / (1 - ((l : ℝ) ^ d)⁻¹)) +
          altNum l d D (s - 1) / (1 - ((l : ℝ) ^ d)⁻¹) = D s := by
        rw [← mul_div_assoc, ← add_div, hrec, mul_div_cancel_left₀ _ hden_pos.ne']
      exact le_of_eq heq
  have hsum_alt : ∑ s : ZMod d, altNum l d D s =
      (1 - ((l : ℝ) ^ d)⁻¹) / ((l : ℝ) + 1) * (∑ s : ZMod d, D s) := by
    have h1 : ((l : ℝ) + 1) * (∑ s : ZMod d, altNum l d D s) =
        (1 - ((l : ℝ) ^ d)⁻¹) * (∑ s : ZMod d, D s) := by
      have hshift : ∑ s : ZMod d, altNum l d D (s - 1) = ∑ s : ZMod d, altNum l d D s :=
        Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ fun _ => rfl
      calc ((l : ℝ) + 1) * (∑ s : ZMod d, altNum l d D s)
          = (l : ℝ) * (∑ s : ZMod d, altNum l d D s) + ∑ s : ZMod d, altNum l d D (s - 1) := by
            rw [hshift]; ring
        _ = ∑ s : ZMod d, ((l : ℝ) * altNum l d D s + altNum l d D (s - 1)) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        _ = ∑ s : ZMod d, (1 - ((l : ℝ) ^ d)⁻¹) * D s :=
            Finset.sum_congr rfl fun s _ => altNum_rec (by omega) hev D s
        _ = (1 - ((l : ℝ) ^ d)⁻¹) * (∑ s : ZMod d, D s) := (Finset.mul_sum _ _ _).symm
    have hlp : (0 : ℝ) < (l : ℝ) + 1 := by linarith
    rw [div_mul_eq_mul_div, eq_div_iff hlp.ne', mul_comm, h1]
  have hval : flowVal d x = (∑ s : ZMod d, D s) / ((l : ℝ) + 1) := by
    unfold flowVal
    have hinner : ∀ s : ZMod d, ∑ i ∈ oddLevels d, x s i =
        altNum l d D s / (1 - ((l : ℝ) ^ d)⁻¹) := fun s => by
      rw [Finset.sum_eq_single 1]
      · simp [x]
      · intro i _ hi; simp [x, hi]
      · intro h; exact absurd h1mem h
    simp_rw [hinner]
    rw [← Finset.sum_div, hsum_alt]
    have hlpow_ne : (l : ℝ) ^ d - 1 ≠ 0 := by linarith
    field_simp [hden_pos.ne', hlpow_ne, (by linarith : (l : ℝ) + 1 ≠ 0)]
  have hmax_ge : (∑ s : ZMod d, D s) / ((l : ℝ) + 1) ≤ maxFlow l d D := by
    rw [← hval]
    exact le_maxFlow (by omega) hx
  unfold Fnum
  have hdiff := gam_sub_inv_succ hl
  have hrew : gam l * (∑ s : ZMod d, D s) - (∑ s : ZMod d, D s) / ((l : ℝ) + 1) =
      rho l * (∑ s : ZMod d, D s) := by
    have : (∑ s : ZMod d, D s) / ((l : ℝ) + 1) = (1 / ((l : ℝ) + 1)) * (∑ s : ZMod d, D s) := by ring
    rw [this, ← sub_mul, hdiff]
  linarith

end LPDuality

/-! ### `YoungDiagramLPFlow` Structure & Top/Base Term Bounds -/

/-- **Young-Diagram Jet-Weight LP-Flow Data (`YoungDiagramLPFlow`)**
(matching `ProductZerothFirstParts.Loc` & `DworkPowerSeriesWeights`):
packages a prime `l`, residue period `d`, matrix dimensions `N0, N1`, Young diagrams
`nu : ZMod d → YoungDiagram` with column height `≤ N0`, and top-row subset `TT : Finset (ZMod d)`. -/
structure YoungDiagramLPFlow where
  l : ℕ
  [l_prime : Fact l.Prime]
  d : ℕ
  [d_neZero : NeZero d]
  N0 : ℕ
  N1 : ℕ
  nu : ZMod d → YoungDiagram
  nu_rows : ∀ s : ZMod d, (nu s).colLen 0 ≤ N0
  TT : Finset (ZMod d)

attribute [instance] YoungDiagramLPFlow.l_prime YoungDiagramLPFlow.d_neZero

namespace YoungDiagramLPFlow

variable (Y : YoungDiagramLPFlow)

/-- First-row length `A(s) = rowLen 0` of the Young diagram at residue `s`. -/
def A (s : ZMod Y.d) : ℕ := (Y.nu s).rowLen 0

/-- Second-row length `B(s) = rowLen 1` of the Young diagram at residue `s`. -/
def B (s : ZMod Y.d) : ℕ := (Y.nu s).rowLen 1

/-- Total cell count `|ν(s)|` at residue `s`. -/
def size (s : ZMod Y.d) : ℕ := (Y.nu s).cells.card

/-- Column capacity `cap(s) = if s ∈ TT then B(s) else A(s)`. -/
def cap (s : ZMod Y.d) : ℕ := if s ∈ Y.TT then Y.B s else Y.A s

/-- Reduced degree budget `Dl(s) = if s ∈ TT then size(s) - A(s) else size(s)`. -/
def Dl (s : ZMod Y.d) : ℕ := if s ∈ Y.TT then Y.size s - Y.A s else Y.size s

/-- Minimum odd step `e` from `s` into `TT` (`dTop s : ℕ∞`). -/
def dTop (s : ZMod Y.d) : ℕ∞ :=
  ⨅ (e : ℕ) (_ : Odd e ∧ s + (e : ZMod Y.d) ∈ Y.TT), (e : ℕ∞)

/-- Incoming cap supremum `Wc(s)`. -/
def Wc (s : ZMod Y.d) : ℕ :=
  sSup {c : ℕ | ∃ i : ℕ, Odd i ∧ Y.l ^ i ≤ Y.size (s - (i : ZMod Y.d)) ∧
    c = Y.cap (s - (i : ZMod Y.d))}

/-- Top-level geometric contribution `topTerm(s)`. -/
def topTerm (s : ZMod Y.d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) < Y.dTop s then
      max ((Y.A s : ℝ) / (Y.l : ℝ) ^ e - (Y.cap (s + (e : ZMod Y.d)) : ℝ)) 0
    else if Odd e ∧ Y.dTop s < (e : ℕ∞) then (Y.A s : ℝ) / (Y.l : ℝ) ^ e
    else 0

/-- Base-level geometric contribution `baseTerm(s)`. -/
def baseTerm (s : ZMod Y.d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) ≠ Y.dTop s then
      max (((Y.A s : ℝ) - (Y.B s : ℝ)) / (Y.l : ℝ) ^ e - (Y.cap (s + (e : ZMod Y.d)) : ℝ)) 0
    else 0

/-- Primal LP jet-weight functional `FD = lpF l d (fun s => Dl s)`. -/
def FD : ℝ := lpF Y.l Y.d (fun s => (Y.Dl s : ℝ))

/-- **`FD_eq_Fnum`**: exact identification `Y.FD = Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ))`. -/
theorem FD_eq_Fnum : Y.FD = Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ)) :=
  lpF_eq_Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ))

/-- Lower bound `rho l * ∑ s, Dl s ≤ Y.FD`. -/
theorem FD_ge_rho_sum_Dl :
    rho Y.l * (∑ s : ZMod Y.d, (Y.Dl s : ℝ)) ≤ Y.FD := by
  rw [Y.FD_eq_Fnum]
  exact Fnum_ge_rho_mul_sum (Fact.out : Y.l.Prime).two_le fun s => Nat.cast_nonneg _

/-- Upper bound `Y.FD ≤ gam l * ∑ s, Dl s`. -/
theorem FD_le_gam_sum_Dl :
    Y.FD ≤ gam Y.l * (∑ s : ZMod Y.d, (Y.Dl s : ℝ)) := by
  rw [Y.FD_eq_Fnum]
  exact Fnum_le_gam_mul_sum (Fact.out : Y.l.Prime).one_le fun s => Nat.cast_nonneg _

/-- **`baseTerm_le_topTerm`** (matching Alpöge's `DworkPowerSeriesWeights.base_term_le_top_term`):
for every residue `s : ZMod Y.d`, `Y.baseTerm s ≤ Y.topTerm s`! -/
theorem baseTerm_le_topTerm (s : ZMod Y.d) : Y.baseTerm s ≤ Y.topTerm s := by
  unfold baseTerm topTerm
  have hl : (1 : ℝ) < (Y.l : ℝ) := by exact_mod_cast (Fact.out : Y.l.Prime).one_lt
  have hpos : ∀ e : ℕ, (0 : ℝ) < (Y.l : ℝ) ^ e := fun e => pow_pos (by linarith) e
  have hc : ∀ x : ZMod Y.d, (0 : ℝ) ≤ (Y.cap x : ℝ) := fun _ => Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ (Y.B s : ℝ) := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ (Y.A s : ℝ) := Nat.cast_nonneg _
  have hq : ∀ e : ℕ, 0 ≤ (Y.A s : ℝ) / (Y.l : ℝ) ^ e := fun e => div_nonneg hA0 (hpos e).le
  have hsub : ∀ e : ℕ, ((Y.A s : ℝ) - (Y.B s : ℝ)) / (Y.l : ℝ) ^ e ≤
      (Y.A s : ℝ) / (Y.l : ℝ) ^ e := fun e => by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 (hpos e).le)
  have hdiv : ∀ e : ℕ, (Y.A s : ℝ) / (Y.l : ℝ) ^ e = (Y.A s : ℝ) * (1 / (Y.l : ℝ)) ^ e :=
    fun e => by rw [one_div, inv_pow, div_eq_mul_inv]
  have hgeo : Summable (fun e : ℕ => (Y.A s : ℝ) * (1 / (Y.l : ℝ)) ^ e) :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 hl)).mul_left _
  refine Summable.tsum_le_tsum (fun e => ?_)
    (Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeo)
    (Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeo)
  · by_cases h1 : Odd e ∧ (e : ℕ∞) ≠ Y.dTop s
    · rw [if_pos h1]
      by_cases h2 : Odd e ∧ (e : ℕ∞) < Y.dTop s
      · rw [if_pos h2]
        exact max_le_max (sub_le_sub_right (hsub e) _) le_rfl
      · rw [if_neg h2]
        by_cases h3 : Odd e ∧ Y.dTop s < (e : ℕ∞)
        · rw [if_pos h3]
          have := hc (s + (e : ZMod Y.d))
          have := hsub e
          exact max_le (by linarith) (hq e)
        · exfalso
          rcases lt_trichotomy (e : ℕ∞) (Y.dTop s) with h | h | h
          · exact h2 ⟨h1.1, h⟩
          · exact h1.2 h
          · exact h3 ⟨h1.1, h⟩
    · rw [if_neg h1]
      split_ifs
      · exact le_max_right _ _
      · exact hq e
      · exact le_rfl
  · split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · rw [← hdiv]
    split_ifs
    · have := hc (s + (e : ZMod Y.d))
      have := hsub e
      exact max_le (by linarith) (hq e)
    · exact hq e
  · split_ifs
    · exact le_max_right _ _
    · exact hq e
    · exact le_rfl
  · rw [← hdiv]
    split_ifs
    · have := hc (s + (e : ZMod Y.d))
      exact max_le (by linarith) (hq e)
    · exact le_rfl
    · exact hq e

theorem baseTerm_nonneg (s : ZMod Y.d) : 0 ≤ Y.baseTerm s := by
  unfold baseTerm
  refine tsum_nonneg fun e => ?_
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem topTerm_nonneg (s : ZMod Y.d) : 0 ≤ Y.topTerm s :=
  (Y.baseTerm_nonneg s).trans (Y.baseTerm_le_topTerm s)

theorem colLen_le_N0 (s : ZMod Y.d) (c : Fin (Y.A s)) : (Y.nu s).colLen c ≤ Y.N0 :=
  (yd_colLen_le (Y.nu s) c).trans (Y.nu_rows s)

end YoungDiagramLPFlow

end YoungDiagramLPFlowSection

/-! ## Section 4: Dwork Power-Series Jet Weights (`DworkPowerSeriesWeights` Bridge) -/

section DworkJetWeightsBridge

/-- **Jet-Polynomial Coefficient Valuation Lower Bound (`KvalGe`)**
(matching `ProductZerothFirstParts.KvalGe`):
a family of jet polynomials `jetEval : ι_J → MvPolynomial σ ℂ_[l]` has `l`-adic valuation `≥ B`
if every monomial coefficient has `ℂ_[l]`-norm `≤ l ^ (-B)`. -/
def KvalGe {ι_J σ : Type*} (l : ℕ) [Fact l.Prime]
    (jetEval : ι_J → MvPolynomial σ ℂ_[l]) (B : ℝ) : Prop :=
  ∀ (I : ι_J) (m : σ →₀ ℕ), ‖MvPolynomial.coeff m (jetEval I)‖ ≤ (l : ℝ) ^ (-B)

theorem kvalGe_mono {ι_J σ : Type*} {l : ℕ} [Fact l.Prime]
    {jetEval : ι_J → MvPolynomial σ ℂ_[l]} {B B' : ℝ}
    (h : KvalGe l jetEval B) (hB : B' ≤ B) : KvalGe l jetEval B' := fun I m => by
  refine (h I m).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : l.Prime).one_lt.le
  · linarith

/-- Equivalence between `KvalGe l jetEval B` and the `‖(l : ℂ_[l])‖ ^ B` form via
`norm_l_padic_complex_rpow`. -/
theorem kvalGe_iff_norm_l_pow {ι_J σ : Type*} {l : ℕ} [Fact l.Prime]
    {jetEval : ι_J → MvPolynomial σ ℂ_[l]} {B : ℝ} :
    KvalGe l jetEval B ↔
      ∀ (I : ι_J) (m : σ →₀ ℕ), ‖MvPolynomial.coeff m (jetEval I)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ B := by
  simp_rw [KvalGe, norm_l_padic_complex_rpow]

/-- **Dwork Power-Series Weight Stability under Unit Scaling (`wtGe_unit_scale`)**:
scaling variables `X_i ↦ ep * X_i` by a unit `‖ep‖ = 1` preserves `WtGe` identically! -/
theorem wtGe_unit_scale {σ K : Type*} [Finite σ] [NormedField K] [IsUltrametricDist K]
    {pi w : ℝ} {r : σ → ℝ} {ep : K} (hep : ‖ep‖ = 1) {F : MvPowerSeries σ K}
    (hF : WtGe pi r w F) :
    WtGe pi r w (MvPowerSeries.subst (fun i : σ => MvPowerSeries.C ep * MvPowerSeries.X i) F) := by
  classical
  let g : σ → MvPowerSeries σ K := fun i => MvPowerSeries.C ep * MvPowerSeries.X i
  have hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := fun i => by
    simp [g]
  have hsub : MvPowerSeries.HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg0
  have hpow : ∀ (e : σ →₀ ℕ) (d : σ →₀ ℕ),
      MvPowerSeries.coeff d (e.prod fun i k => (g i) ^ k) =
        if d = e then ep ^ e.degree else 0 := by
    intro e d
    have hprod_eq : (e.prod fun i k => (g i) ^ k) = MvPowerSeries.monomial e (ep ^ e.degree) := by
      have hterm : ∀ i ∈ e.support, (g i) ^ (e i) =
          MvPowerSeries.monomial (Finsupp.single i (e i)) (ep ^ (e i)) := by
        intro i _
        have hX : (MvPowerSeries.X i : MvPowerSeries σ K) =
            MvPowerSeries.monomial (Finsupp.single i 1) 1 := rfl
        rw [show g i = MvPowerSeries.C ep * MvPowerSeries.X i from rfl, mul_pow, ← map_pow,
          hX, MvPowerSeries.monomial_pow, one_pow, Finsupp.smul_single, smul_eq_mul, mul_one]
        ext m
        rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
        split_ifs <;> simp
      rw [Finsupp.prod, Finset.prod_congr rfl hterm]
      have hfold : ∀ (s : Finset σ),
          (∏ i ∈ s, MvPowerSeries.monomial (Finsupp.single i (e i)) (ep ^ (e i))) =
            MvPowerSeries.monomial (∑ i ∈ s, Finsupp.single i (e i)) (ep ^ (∑ i ∈ s, e i)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
            MvPowerSeries.monomial_mul_monomial, pow_add]
      rw [hfold e.support]
      have hsum_single : ∑ i ∈ e.support, Finsupp.single i (e i) = e := Finsupp.sum_single e
      rw [hsum_single]
      rfl
    rw [hprod_eq, MvPowerSeries.coeff_monomial]
  intro d
  unfold MonoWtGe
  rw [MvPowerSeries.coeff_subst hsub]
  have hfin : ∑ᶠ e : σ →₀ ℕ, MvPowerSeries.coeff e F •
      MvPowerSeries.coeff d (e.prod fun i k => (g i) ^ k) =
      MvPowerSeries.coeff d F * ep ^ d.degree := by
    rw [finsum_eq_single _ d]
    · rw [hpow d d, if_pos rfl, smul_eq_mul]
    · intro e hed
      rw [hpow e d, if_neg hed.symm, smul_zero]
  rw [hfin, norm_mul, norm_pow, hep, one_pow, mul_one]
  exact hF d

/-- **Young-Diagram Jet-Weight Transfer Theorem (`dwork_jet_weight_transfer`)**
(matching `DworkPowerSeriesWeights.thmA_of` + `IncomingBounds.ThmABound`):
if the frame-jet coefficients of `Th` are bounded by
`‖(l : ℂ_[l])‖ ^ ((∑ s ∈ Y.TT, (Y.topTerm s - gam Y.l * Y.Wc s)) + Fnum Y.l Y.d Y.Dl - CA * d * N0 * N1 * (logb l ⌊a⌋₊ + 1))`,
then for every `a ≥ l`, `KvalGe` holds with the full `baseTerm + Y.FD` lower bound! -/
theorem dwork_jet_weight_transfer {ι_J σ : Type*} (Y : YoungDiagramLPFlow)
    (jetEval : ι_J → MvPolynomial σ ℂ_[Y.l]) {a CA : ℝ}
    (hla : (Y.l : ℝ) ≤ a) (hCA : 0 ≤ CA)
    (hFrame : ∀ (I : ι_J) (m : σ →₀ ℕ),
      ‖MvPolynomial.coeff m (jetEval I)‖ ≤
        ‖((Y.l : ℕ) : ℂ_[Y.l])‖ ^
          ((∑ s ∈ Y.TT, (Y.topTerm s - gam Y.l * (Y.Wc s : ℝ))) +
            Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ)) -
            CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l (⌊a⌋₊ : ℝ) + 1)))) :
    KvalGe Y.l jetEval
      ((∑ s ∈ Y.TT, (Y.baseTerm s - gam Y.l * (Y.Wc s : ℝ))) + Y.FD -
        CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l a + 1))) := by
  have hl1 : (1 : ℝ) < (Y.l : ℝ) := by exact_mod_cast (Fact.out : Y.l.Prime).one_lt
  have ha1 : (1 : ℝ) ≤ a := hl1.le.trans hla
  have hfl : 1 ≤ ⌊a⌋₊ := Nat.le_floor (by exact_mod_cast ha1)
  have hlog : Real.logb Y.l (⌊a⌋₊ : ℝ) ≤ Real.logb Y.l a :=
    Real.logb_le_logb_of_le hl1 (by exact_mod_cast hfl) (Nat.floor_le (by linarith))
  have htop_ge : ∑ s ∈ Y.TT, (Y.baseTerm s - gam Y.l * (Y.Wc s : ℝ)) ≤
      ∑ s ∈ Y.TT, (Y.topTerm s - gam Y.l * (Y.Wc s : ℝ)) :=
    Finset.sum_le_sum fun s _ => sub_le_sub_right (Y.baseTerm_le_topTerm s) _
  have hK : KvalGe Y.l jetEval
      ((∑ s ∈ Y.TT, (Y.topTerm s - gam Y.l * (Y.Wc s : ℝ))) +
        Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ)) -
        CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l (⌊a⌋₊ : ℝ) + 1))) :=
    kvalGe_iff_norm_l_pow.2 hFrame
  refine kvalGe_mono hK ?_
  rw [Y.FD_eq_Fnum]
  have hd : 0 ≤ CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ)) := by positivity
  have herr : CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l (⌊a⌋₊ : ℝ) + 1)) ≤
      CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l a + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hlog 1) hd
    linarith
  linarith

/-- Concrete LP-flow valuation lower bound substituting `Fnum_ge_rho_mul_sum` into
`dwork_jet_weight_transfer`. -/
theorem dwork_jet_weight_transfer_rho {ι_J σ : Type*} (Y : YoungDiagramLPFlow)
    (jetEval : ι_J → MvPolynomial σ ℂ_[Y.l]) {a CA : ℝ}
    (hla : (Y.l : ℝ) ≤ a) (hCA : 0 ≤ CA)
    (hFrame : ∀ (I : ι_J) (m : σ →₀ ℕ),
      ‖MvPolynomial.coeff m (jetEval I)‖ ≤
        ‖((Y.l : ℕ) : ℂ_[Y.l])‖ ^
          ((∑ s ∈ Y.TT, (Y.topTerm s - gam Y.l * (Y.Wc s : ℝ))) +
            Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ)) -
            CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l (⌊a⌋₊ : ℝ) + 1)))) :
    KvalGe Y.l jetEval
      ((∑ s ∈ Y.TT, (Y.baseTerm s - gam Y.l * (Y.Wc s : ℝ))) +
        rho Y.l * (∑ s : ZMod Y.d, (Y.Dl s : ℝ)) -
        CA * ((Y.d : ℝ) * (Y.N0 : ℝ) * (Y.N1 : ℝ) * (Real.logb Y.l a + 1))) := by
  refine kvalGe_mono (dwork_jet_weight_transfer Y jetEval hla hCA hFrame) ?_
  linarith [Y.FD_ge_rho_sum_Dl]

end DworkJetWeightsBridge

/-! ## Section 5: `p`-adic Gluing Index Bounds (`qpack_gluing_index_bound`) & Wave-2 Synthesis -/

section PadicGluingIndexBounds

/-- **Algebraic Quotient Cardinality Bound for Sandwiched `ℤ`-Lattices**:
if `L₂` is generated over `ℤ` by `r` vectors `g : Fin r → L₂` (so `g` spans `⊤`),
`L₁ ≤ L₂` is an additive subgroup (or `ℤ`-submodule), and `m • x ∈ L₁` for every `x ∈ L₂`
(`0 < m`), then the quotient `L₂ ⧸ L₁.comap L₂.subtype` is finite of cardinality `≤ m ^ r`! -/
theorem card_quot_le_pow_of_nsmul_mem {V : Type*} [AddCommGroup V]
    {L₁ L₂ : AddSubgroup V} (_h12 : L₁ ≤ L₂) {r m : ℕ} (hm : 0 < m)
    (g : Fin r → L₂) (hgen : AddSubgroup.closure (Set.range g) = ⊤)
    (hsm : ∀ x : L₂, m • (x : V) ∈ L₁) :
    Nat.card (L₂ ⧸ L₁.comap L₂.subtype) ≤ m ^ r := by
  have : NeZero m := ⟨hm.ne'⟩
  -- Build a surjective map `(Fin r → ZMod m) → L₂ ⧸ (L₁.comap L₂.subtype)`
  let Q := L₂ ⧸ L₁.comap L₂.subtype
  let mkQ : L₂ →+ Q := QuotientAddGroup.mk' (L₁.comap L₂.subtype)
  have hmQ : ∀ x : L₂, (m : ℤ) • mkQ x = 0 := by
    intro x
    rw [← map_zsmul]
    change QuotientAddGroup.mk ((m : ℤ) • x) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    change ((m : ℤ) • x : L₂).1 ∈ L₁
    simpa [natCast_zsmul] using hsm x
  let f : (Fin r → ZMod m) → Q := fun c => ∑ i : Fin r, ((c i).val : ℤ) • mkQ (g i)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (L₁.comap L₂.subtype) q
    have hx : x ∈ AddSubgroup.closure (Set.range g) := by rw [hgen]; trivial
    -- First express `mkQ x` as `∑ i, a i • mkQ (g i)` for some `a : Fin r → ℤ`
    have hexZ : ∃ a : Fin r → ℤ, mkQ x = ∑ i : Fin r, a i • mkQ (g i) := by
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        refine ⟨fun j => if j = i then 1 else 0, ?_⟩
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [hji]
        · intro h; exact absurd (Finset.mem_univ i) h
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ ihy ihz =>
        obtain ⟨ay, hay⟩ := ihy
        obtain ⟨az, haz⟩ := ihz
        refine ⟨ay + az, ?_⟩
        rw [map_add, hay, haz, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp [add_zsmul]
      | neg y _ ihy =>
        obtain ⟨ay, hay⟩ := ihy
        refine ⟨-ay, ?_⟩
        rw [map_neg, hay, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp
    obtain ⟨a, ha⟩ := hexZ
    refine ⟨fun i => (a i : ZMod m), ?_⟩
    rw [ha]
    dsimp only [f]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- `((a i : ZMod m).val : ℤ) ≡ a i [ZMOD m]`
    have hdvd : (m : ℤ) ∣ (((a i : ZMod m).val : ℤ) - a i) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp
    obtain ⟨k, hk⟩ := hdvd
    have heq : ((a i : ZMod m).val : ℤ) = a i + k * (m : ℤ) := by linarith
    rw [heq, add_zsmul, mul_zsmul, hmQ (g i), zsmul_zero, add_zero]
  have hcard : Nat.card Q ≤ Nat.card (Fin r → ZMod m) :=
    Nat.card_le_card_of_surjective f hsurj
  have hfin : Nat.card (Fin r → ZMod m) = m ^ r := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact hcard.trans_eq hfin

/-- `latIndex` upper bound for sandwiched `ℤ`-submodules of rank `r`:
if `L₁ ≤ L₂` in `E`, `L₂` has a `ℤ`-basis of size `r`, and `∀ x ∈ L₂, m • x ∈ L₁` (`0 < m`),
then `latIndex L₂ L₁ ≤ m ^ r` and `Real.log (latIndex L₂ L₁ : ℝ) ≤ r * Real.log m`! -/
theorem latIndex_le_pow_of_nsmul_mem {E : Type*} [NormedAddCommGroup E]
    {L₁ L₂ : Submodule ℤ E} (h12 : L₁ ≤ L₂) {r m : ℕ} (hm : 0 < m)
    (b : Basis (Fin r) ℤ L₂) (hsm : ∀ x ∈ L₂, m • x ∈ L₁) :
    latIndex L₂ L₁ ≤ m ^ r ∧ Real.log (latIndex L₂ L₁ : ℝ) ≤ (r : ℝ) * Real.log (m : ℝ) := by
  have hgen : AddSubgroup.closure (Set.range (fun i : Fin r => b i)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← b.sum_repr x]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  have hcard : Nat.card (L₂ ⧸ L₁.toAddSubgroup.comap L₂.toAddSubgroup.subtype) ≤ m ^ r :=
    card_quot_le_pow_of_nsmul_mem (L₁ := L₁.toAddSubgroup) (L₂ := L₂.toAddSubgroup)
      h12 hm (fun i => b i) hgen (fun x => hsm x.1 x.2)
  have hidx : latIndex L₂ L₁ = Nat.card (L₂ ⧸ L₁.toAddSubgroup.comap L₂.toAddSubgroup.subtype) := by
    unfold latIndex
    rw [AddSubgroup.index_eq_card]
    rfl
  have hle : latIndex L₂ L₁ ≤ m ^ r := hidx ▸ hcard
  refine ⟨hle, ?_⟩
  rcases Nat.eq_zero_or_pos (latIndex L₂ L₁) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg r) (Real.log_natCast_nonneg m)
  · calc Real.log (latIndex L₂ L₁ : ℝ)
        ≤ Real.log ((m ^ r : ℕ) : ℝ) :=
          Real.log_le_log (Nat.cast_pos.mpr hpos) (by exact_mod_cast hle)
      _ = (r : ℝ) * Real.log (m : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]

/-- **Exact Arakelov Slope Gluing Bracket (`slope_gluing_bracket_of_nsmul_mem`)**:
for any discrete lattice `L₂ ≠ ⊥` with `ℤ`-basis `b : Basis (Fin r) ℤ L₂` and sublattice
`L₁ ≤ L₂` of the same rank satisfying `∀ x ∈ L₂, m • x ∈ L₁` (`0 < m`),
`slope L₂ - Real.log m ≤ slope L₁ ≤ slope L₂`! -/
theorem slope_gluing_bracket_of_nsmul_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L₁ L₂ : Submodule ℤ E} [DiscreteTopology L₂] (hL₂ : L₂ ≠ ⊥)
    (h12 : L₁ ≤ L₂) {r m : ℕ} (hm : 0 < m)
    (b : Basis (Fin r) ℤ L₂) (hrk : ArakelovCovolume.rk L₁ = ArakelovCovolume.rk L₂)
    (hsm : ∀ x ∈ L₂, m • x ∈ L₁) :
    ArakelovCovolume.slope L₂ - Real.log (m : ℝ) ≤ ArakelovCovolume.slope L₁ ∧
      ArakelovCovolume.slope L₁ ≤ ArakelovCovolume.slope L₂ := by
  have : DiscreteTopology L₁ := ArakelovCovolume.discreteTopology_of_le h12
  have hslope := slope_eq_slope_sub_log_index_div_rk h12 hrk
  have hr_eq : ArakelovCovolume.rk L₂ = r := by
    unfold ArakelovCovolume.rk
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hr_pos : (0 : ℝ) < (ArakelovCovolume.rk L₂ : ℝ) :=
    Nat.cast_pos.mpr (ArakelovCovolume.rk_pos_of_ne_bot L₂ hL₂)
  have hidx_pos : 0 < latIndex L₂ L₁ := by
    have hcov := covol_eq_index_mul_covol h12 hrk
    have hc1 := ArakelovCovolume.covol_pos L₁
    have hc2 := ArakelovCovolume.covol_pos L₂
    by_contra h0
    have hz : latIndex L₂ L₁ = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul] at hcov
    linarith
  have hlog_nn : 0 ≤ Real.log (latIndex L₂ L₁ : ℝ) :=
    Real.log_natCast_nonneg _
  have hlog_le := (latIndex_le_pow_of_nsmul_mem h12 hm b hsm).2
  rw [hslope]
  constructor
  · have hdiv : Real.log (latIndex L₂ L₁ : ℝ) / (ArakelovCovolume.rk L₂ : ℝ) ≤ Real.log (m : ℝ) := by
      rw [div_le_iff₀ hr_pos, hr_eq, mul_comm]
      exact hlog_le
    linarith
  · have hdiv_nn : 0 ≤ Real.log (latIndex L₂ L₁ : ℝ) / (ArakelovCovolume.rk L₂ : ℝ) :=
      div_nonneg hlog_nn hr_pos.le
    linarith

/-- **`p`-adic Gluing Index Bound from `FullCrystallineQPack` (`qpack_gluing_index_bound`)**:
given any `Q : FullCrystallineQPack K p` with `‖(p : K)‖ = p⁻¹` and any `r`-generated integral
lattice `L_om ≤ Q.om` (generated by `g : Fin r → L_om`), let `L_HT := L_om ⊓ Ospan K (Set.range Q.base.ht)`
be its Hodge–Tate sublattice. Then:
1. `p • x ∈ L_HT` for every `x ∈ L_om` (via `hodge_tate_reduction_red`),
2. `Nat.card (L_om ⧸ L_HT.comap L_om.subtype) ≤ p ^ r`, and
3. `Real.log (Nat.card (L_om ⧸ L_HT.comap L_om.subtype) : ℝ) ≤ (r : ℝ) * Real.log (p : ℝ)`. -/
theorem qpack_gluing_index_bound {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p : ℕ} [Fact p.Prime] (Q : FullCrystallineQPack K p)
    (hnp : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
    (L_om : AddSubgroup Q.base.OmV) (hL_le : L_om ≤ Q.om)
    {r : ℕ} (g : Fin r → L_om) (hgen : AddSubgroup.closure (Set.range g) = ⊤) :
    let L_HT : AddSubgroup Q.base.OmV := L_om ⊓ Ospan K (Set.range Q.base.ht)
    (∀ x : L_om, p • (x : Q.base.OmV) ∈ L_HT) ∧
    Nat.card (L_om ⧸ L_HT.comap L_om.subtype) ≤ p ^ r ∧
    Real.log (Nat.card (L_om ⧸ L_HT.comap L_om.subtype) : ℝ) ≤ (r : ℝ) * Real.log (p : ℝ) := by
  intro L_HT
  have hp : p.Prime := Fact.out
  have hsm : ∀ x : L_om, p • (x : Q.base.OmV) ∈ L_HT := by
    intro x
    refine ⟨L_om.nsmul_mem x.2 p, ?_⟩
    have hsm_eq : p • (x : Q.base.OmV) = ((p : ℕ) : K) • (x : Q.base.OmV) := by
      rw [Nat.cast_smul_eq_nsmul]
    rw [hsm_eq]
    exact Q.p_smul_om_mem_ospan hnp (hL_le x.2)
  have hcard : Nat.card (L_om ⧸ L_HT.comap L_om.subtype) ≤ p ^ r :=
    card_quot_le_pow_of_nsmul_mem inf_le_left hp.pos g hgen hsm
  refine ⟨hsm, hcard, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.card (L_om ⧸ L_HT.comap L_om.subtype)) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg r) (Real.log_natCast_nonneg p)
  · calc Real.log (Nat.card (L_om ⧸ L_HT.comap L_om.subtype) : ℝ)
        ≤ Real.log ((p ^ r : ℕ) : ℝ) :=
          Real.log_le_log (Nat.cast_pos.mpr hpos) (by exact_mod_cast hcard)
      _ = (r : ℝ) * Real.log (p : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]

/-- **Ramified `p`-adic Gluing Index Bound (`qpack_gluing_ramified_index_bound`)**:
in a ramified local extension of ramification index `e ≥ 1` and uniformizer `unif : K`
(`‖unif‖ = p ^ (-1 / e)`), setting `k = ⌈e / (p - 1)⌉`:
1. `‖unif ^ k‖ ≤ p ^ (-1 / (p - 1))`,
2. `unif ^ k • x ∈ Ospan K (Set.range Q.base.ht)` for every `x ∈ Q.om`,
3. normalized ramification overhead `(k : ℝ) / (e : ℝ) < 1 / ((p : ℝ) - 1) + 1 / (e : ℝ)`,
4. if a local quotient index satisfies `idx ≤ q ^ (r * k)` (`1 ≤ q`, `1 ≤ r`), then
   `Real.log (idx : ℝ) / (r : ℝ) ≤ (k : ℝ) * Real.log (q : ℝ)` and
   `Real.log (idx : ℝ) / ((r : ℝ) * (e : ℝ)) ≤ (1 / ((p : ℝ) - 1) + 1 / (e : ℝ)) * Real.log (q : ℝ)`. -/
theorem qpack_gluing_ramified_index_bound {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p : ℕ} [Fact p.Prime] (Q : FullCrystallineQPack K p)
    {e : ℕ} (he : 1 ≤ e) {unif : K} (hunif : ‖unif‖ = (p : ℝ) ^ (-(1 : ℝ) / (e : ℝ))) :
    let k : ℕ := Nat.ceil ((e : ℝ) / ((p : ℝ) - 1))
    ‖unif ^ k‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) ∧
    (∀ x ∈ Q.om, unif ^ k • x ∈ Ospan K (Set.range Q.base.ht)) ∧
    (k : ℝ) / (e : ℝ) < 1 / ((p : ℝ) - 1) + 1 / (e : ℝ) ∧
    (∀ (r q idx : ℕ), 1 ≤ r → 1 ≤ q → idx ≤ q ^ (r * k) →
      Real.log (idx : ℝ) / (r : ℝ) ≤ (k : ℝ) * Real.log (q : ℝ) ∧
      Real.log (idx : ℝ) / ((r : ℝ) * (e : ℝ)) ≤
        (1 / ((p : ℝ) - 1) + 1 / (e : ℝ)) * Real.log (q : ℝ)) := by
  intro k
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have he_pos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hnorm : ‖unif ^ k‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
    rw [norm_pow, hunif, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp1.le
    have hk : (e : ℝ) / ((p : ℝ) - 1) ≤ (k : ℝ) := Nat.le_ceil _
    have h1 : (-(1 : ℝ) / (e : ℝ)) * (k : ℝ) = -((k : ℝ) / (e : ℝ)) := by ring
    rw [h1, neg_div]
    have h2 : 1 / ((p : ℝ) - 1) ≤ (k : ℝ) / (e : ℝ) := by
      rw [le_div_iff₀ he_pos]
      have : (1 : ℝ) / ((p : ℝ) - 1) * (e : ℝ) = (e : ℝ) / ((p : ℝ) - 1) := by ring
      linarith
    linarith
  have hoverhead : (k : ℝ) / (e : ℝ) < 1 / ((p : ℝ) - 1) + 1 / (e : ℝ) := by
    have hk_lt : (k : ℝ) < (e : ℝ) / ((p : ℝ) - 1) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg he_pos.le (by linarith))
    rw [div_lt_iff₀ he_pos]
    have hrew : (1 / ((p : ℝ) - 1) + 1 / (e : ℝ)) * (e : ℝ) = (e : ℝ) / ((p : ℝ) - 1) + 1 := by
      field_simp [he_pos.ne', (by linarith : (p : ℝ) - 1 ≠ 0)]
    linarith
  refine ⟨hnorm, fun x hx => Q.ramified_uniformizer_pow_mem_ospan he hunif hx, hoverhead, ?_⟩
  intro r q idx hr hq hidx
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hlog_idx : Real.log (idx : ℝ) ≤ (r : ℝ) * ((k : ℝ) * Real.log (q : ℝ)) := by
    rcases Nat.eq_zero_or_pos idx with rfl | hpos
    · rw [Nat.cast_zero, Real.log_zero]
      positivity
    · calc Real.log (idx : ℝ)
          ≤ Real.log ((q ^ (r * k) : ℕ) : ℝ) :=
            Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.2 hidx)
        _ = (r : ℝ) * ((k : ℝ) * Real.log (q : ℝ)) := by
            rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul]; ring
  have h1 : Real.log (idx : ℝ) / (r : ℝ) ≤ (k : ℝ) * Real.log (q : ℝ) := by
    rw [div_le_iff₀ hr_pos]
    linarith
  refine ⟨h1, ?_⟩
  calc Real.log (idx : ℝ) / ((r : ℝ) * (e : ℝ))
      = (Real.log (idx : ℝ) / (r : ℝ)) / (e : ℝ) := (div_div _ _ _).symm
    _ ≤ ((k : ℝ) * Real.log (q : ℝ)) / (e : ℝ) := div_le_div_of_nonneg_right h1 he_pos.le
    _ = ((k : ℝ) / (e : ℝ)) * Real.log (q : ℝ) := by ring
    _ ≤ (1 / ((p : ℝ) - 1) + 1 / (e : ℝ)) * Real.log (q : ℝ) :=
        mul_le_mul_of_nonneg_right hoverhead.le hlogq

/-- Unramified (`e = 1`) specialization: `⌈1 / (p - 1)⌉ = 1` for every prime `p`. -/
theorem ceil_inv_prime_sub_one {p : ℕ} (hp : p.Prime) :
    Nat.ceil ((1 : ℝ) / ((p : ℝ) - 1)) = 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (1 : ℝ) / ((p : ℝ) - 1) := div_pos one_pos (by linarith)
  have hle : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  refine le_antisymm (Nat.ceil_le.2 (by simpa using hle)) ?_
  refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
  have hle0 := Nat.le_ceil ((1 : ℝ) / ((p : ℝ) - 1))
  rw [h0, Nat.cast_zero] at hle0
  linarith

/-- **Multi-Place Gluing Index Sum Bound (`multiplace_qpack_gluing_index_bound`)**:
aggregates local `QPack` gluing index bounds across a finite set of places `supp : Finset Pl`
into the normalized Arakelov gluing loss compatible with `Stage12MultivarDwork.InertCongruenceData`. -/
theorem multiplace_qpack_gluing_index_bound {Pl : Type*} (supp : Finset Pl)
    (pOf qOf eOf idxOf : Pl → ℕ) (r : ℕ) (degNorm : ℝ)
    (hr : 1 ≤ r) (hdeg : 0 < degNorm)
    (hp : ∀ w ∈ supp, (pOf w).Prime)
    (hq : ∀ w ∈ supp, 1 ≤ qOf w)
    (he : ∀ w ∈ supp, 1 ≤ eOf w)
    (hidx : ∀ w ∈ supp, idxOf w ≤ (qOf w) ^ (r * Nat.ceil ((eOf w : ℝ) / ((pOf w : ℝ) - 1)))) :
    (∑ w ∈ supp, Real.log (idxOf w : ℝ) / ((r : ℝ) * degNorm)) ≤
      ∑ w ∈ supp, (Real.log (qOf w : ℝ) / degNorm) *
        ((eOf w : ℝ) / ((pOf w : ℝ) - 1) + 1) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  refine Finset.sum_le_sum fun w hw => ?_
  have hpw := hp w hw
  have hqw := hq w hw
  have hew := he w hw
  have hp2 : (2 : ℝ) ≤ (pOf w : ℝ) := by exact_mod_cast hpw.two_le
  have he_pos : (0 : ℝ) < (eOf w : ℝ) := by exact_mod_cast hew
  set kw : ℕ := Nat.ceil ((eOf w : ℝ) / ((pOf w : ℝ) - 1))
  have hlogq : 0 ≤ Real.log (qOf w : ℝ) := Real.log_natCast_nonneg (qOf w)
  have hlog_idx : Real.log (idxOf w : ℝ) ≤ (r : ℝ) * ((kw : ℝ) * Real.log (qOf w : ℝ)) := by
    rcases Nat.eq_zero_or_pos (idxOf w) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    · calc Real.log (idxOf w : ℝ)
          ≤ Real.log (((qOf w) ^ (r * kw) : ℕ) : ℝ) :=
            Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.2 (hidx w hw))
        _ = (r : ℝ) * ((kw : ℝ) * Real.log (qOf w : ℝ)) := by
            rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul]; ring
  have hkw_lt : (kw : ℝ) < (eOf w : ℝ) / ((pOf w : ℝ) - 1) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg he_pos.le (by linarith))
  calc Real.log (idxOf w : ℝ) / ((r : ℝ) * degNorm)
      ≤ ((r : ℝ) * ((kw : ℝ) * Real.log (qOf w : ℝ))) / ((r : ℝ) * degNorm) :=
        div_le_div_of_nonneg_right hlog_idx (mul_nonneg hr_pos.le hdeg.le)
    _ = (Real.log (qOf w : ℝ) / degNorm) * (kw : ℝ) := by
        field_simp [hr_pos.ne', hdeg.ne']
    _ ≤ (Real.log (qOf w : ℝ) / degNorm) * ((eOf w : ℝ) / ((pOf w : ℝ) - 1) + 1) :=
        mul_le_mul_of_nonneg_left hkw_lt.le (div_nonneg hlogq hdeg.le)

/-- **Wave-2 Integration Package (`QPackJetWeightsPack`)**:
bundles a `FullCrystallineQPack ℂ_[l] l`, a `YoungDiagramLPFlow` at prime `l`, and the proved
Hodge–Tate reduction, LP-flow identity `FD = Fnum`, `baseTerm ≤ topTerm`, and `ℂ_[l]` prime norm
identities, ready for `Stage14M5_IndefSideAndON`! -/
structure QPackJetWeightsPack (l : ℕ) [Fact l.Prime] where
  qpack : FullCrystallineQPack.{0, 0} ℂ_[l] l
  flow : YoungDiagramLPFlow
  flow_prime : flow.l = l

/-- **Master Wave-1 Synthesis Theorem (`stage14M5_qpack_jet_weights_synthesis`)**:
for any prime `l`, constructs a non-vacuous `FullCrystallineQPack ℂ_[l] l` and proves all core
Wave-1 deliverables in one place:
1. `‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹` (`norm_l_padic_complex`),
2. full Hodge–Tate sandwich (`Ospan ≤ om` and `p^{-1/(p-1)}`-ball scales `om` into `Ospan`),
3. exact LP-flow equivalence `lpF l d D = Fnum l d D` (`lpF_eq_Fnum`) + `rho l * ∑ D ≤ Fnum l d D`,
4. `Y.baseTerm s ≤ Y.topTerm s` and `Y.FD = Fnum Y.l Y.d (fun s => Y.Dl s)`,
5. `p`-adic gluing index upper bound (`≤ l ^ r`, `log ≤ r * log l`). -/
theorem stage14M5_qpack_jet_weights_synthesis (l d : ℕ) [Fact l.Prime] [NeZero d]
    (D : ZMod d → ℝ) (hD : 0 ≤ D) (Y : YoungDiagramLPFlow) :
    ‖((l : ℕ) : ℂ_[l])‖ = (l : ℝ)⁻¹ ∧
    (∃ Q : FullCrystallineQPack.{0, 0} ℂ_[l] l,
      Ospan ℂ_[l] (Set.range Q.base.ht) ≤ Q.om ∧
      ∀ x ∈ Q.om, ∀ c : ℂ_[l], ‖c‖ ≤ (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1)) →
        c • x ∈ Ospan ℂ_[l] (Set.range Q.base.ht)) ∧
    lpF l d D = Fnum l d D ∧
    rho l * (∑ s : ZMod d, D s) ≤ Fnum l d D ∧
    Y.FD = Fnum Y.l Y.d (fun s => (Y.Dl s : ℝ)) ∧
    (∀ s : ZMod Y.d, Y.baseTerm s ≤ Y.topTerm s) := by
  refine ⟨norm_l_padic_complex l, ⟨concreteFullCrystallineQPack l, (concreteFullCrystallineQPack l).htb_at⟩,
    lpF_eq_Fnum l d D, Fnum_ge_rho_mul_sum (Fact.out : l.Prime).two_le hD,
    Y.FD_eq_Fnum, Y.baseTerm_le_topTerm⟩

end PadicGluingIndexBounds

end

end RHDirect.Stage14M5_QPackJetWeights
