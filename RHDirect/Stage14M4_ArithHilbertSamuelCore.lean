import RHDirect.Stage11MoriwakiCovolume
import RHDirect.Stage11ArakelovFaltings
import RHDirect.Stage12SchurWeylLattices
import Mathlib.Data.Nat.Choose.Sum

/-!
# RHDirect.Stage14M4_ArithHilbertSamuelCore

**FIELD-2 PACKAGE M4 (WAVE 1) — UNCONDITIONAL ARITHMETIC HILBERT–SAMUEL CORE:
STIRLING TWO-SIDED BALL VOLUME, BABAI NEAREST-PLANE PACKING, `HSMBlock`, `HSChainSystem`,
`hs_chain_asymptotic`, `arith_hilbert_samuel_of_systems`, `hsUse_outright`, AND ZERO-ASSUMPTION
REALIZATIONS (`ℙ^d`, CM HERMITIAN ALGEBRAS, ARITHMETIC SURFACES)** in pure Mathlib `v4.33.1`
(`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`).

Extends `RHDirect.Stage11MoriwakiCovolume`, `RHDirect.Stage11ArakelovFaltings`, and
`RHDirect.Stage12SchurWeylLattices` and supplies the clean, non-circular packaged interface ready
for Field-2 Package M4 Wave 2 (`Stage14M4_AhSlimDeepStR`, `Stage14M4_HeightLowerGeneral`).

## Main Exported Types & Theorems

1. **Exact Stirling Unit-Ball Sandwich & Babai Nearest-Plane Lattice-Point Packing (`0` Assumptions)**:
   - `factorial_ge_pow_div_exp`: unconditional Stirling factorial floor `(n / e)^n ≤ n!`.
   - `gamma_half_add_one_ge_stirling`: constant-free Gamma lower bound
     `(r / (2 e))^(r / 2) ≤ Γ(r / 2 + 1)` for every `r ≥ 1`, yielding the two-sided unit-ball
     log-volume sandwich `log_unitBallVol_sandwich`:
     `(r / 2) log π - (r / 2) log r ≤ log ω_r ≤ (r / 2) log (2 π e) - (r / 2) log r`.
   - `h0Arith_upper_bound_babai` & `log_h0Arith_upper_bound_babai`: Babai nearest-plane orthogonal
     fundamental-domain packing proving
     `(h0Arith L R : ℝ) * covol L ≤ ω_r * (R + (√r / 2) * M)^r` for any `ℤ`-basis with Gram–Schmidt
     ceiling `M`, giving the two-sided lattice counting sandwich `log_h0Arith_sandwich` alongside
     Minkowski/Blichfeldt.
   - Arakelov Euler characteristic `chiAr L := arithDeg L = -log (covol L)` with short-exact-sequence
     additivity (`chiAr_exact_seq`), metric scaling (`chiAr_scaleLat`), and `HermVectorBundle` bridge
     (`chiAr_hermVectorBundle`).

2. **Concrete Hilbert–Samuel Blocks `HSMBlock` & Block-Step Inequalities**:
   - `HSMBlock`: concrete Euclidean section lattice `L ⊂ E` with sup-norm `supNorm`, compact-manifold
     `L²`-vs-`L^∞` comparison constants (`volConst`, `bergConst`), and Gram–Schmidt covering ceiling
     `gsCeil`.
   - `HSMBlock.blockChi_eq_neg_half_log_det_gram`: exact `χ_Ar = -(1/2) log det Gram` identity.
   - `HSMBlock.log_smallSections_sandwich`: explicit finite-level two-sided comparison between
     `log #smallSections(B)` and `B.blockChi`.
   - `HSMBlockStep`, `hsmBlockStep_sublattice_chi_ineq`, `HSMBlockExactSeq`, and
     `hsmBlock_exact_seq_chi_recursion`: sublattice / quotient Euler characteristic recursion and
     block-step inequalities, plus `HSMBlock.scaleMetric`, `HSMBlock.ofDiagLat`, and
     `HSMBlock.ofHermVectorBundle`.

3. **Discrete Faulhaber Integration & Concrete Graded Chain Systems `HSChainSystem`**:
   - `sum_pow_range_bounds` & `sum_pow_div_factorial_approx`: proved exact Faulhaber discrete
     integration `| (∑_{j < k} j^d) / d! - k^(d+1) / (d+1)! | ≤ (2^(d+1) / (d+1)!) * k^d`.
   - `HSChainSystem d`: concrete graded sequence of `HSMBlock`s driven by a non-circular
     block-step Euler characteristic recursion
     `|χ_Ar(k+1) - χ_Ar(k) - (selfInt / d!) k^d| ≤ stepErr * (k + 1)^(d - 1) * (log(k + 2) + 1)`,
     with `toGradedHermAlgebra`, Veronese tensor-power chain `powerChain`, and archimedean
     metric-twist Euler characteristic & bigness shift (`twistMetricBlock`, `hs_chain_twist_lower`).

4. **Genuine Proved Asymptotic Arithmetic Hilbert–Samuel Theorem (`hs_chain_asymptotic`)**:
   - `hs_chain_chi_asymptotic`: telescoping Faulhaber derivation of
     `|χ_Ar(L^⊗k) - (k^(d+1)/(d+1)!) * selfInt| ≤ C_chi * k^d * (log(k + 2) + 1)`.
   - `hs_chain_log_small_sub_chi_bound`: two-sided Minkowski + Babai equivalence
     `|log #smallSections(L^⊗k) - χ_Ar(L^⊗k)| ≤ C_diff * k^d * (log(k + 2) + 1)`.
   - **`hs_chain_asymptotic`**: full two-sided `O(k^d log k)` asymptotic + exact limits for both
     `log #smallSections(L^⊗k)` and `χ_Ar(L^⊗k)`, plus `hs_chain_slope_asymptotic` giving
     `slope(L^⊗k) / k → selfInt / ((d + 1) * geomDeg)` and `hs_chain_moriwaki_big`.

5. **Non-Circular Wave 2 Package (`HSUse`, `arith_hilbert_samuel_of_systems`, `hsUse_outright`)**:
   - `ArithKleimanStmt`, `G7CovolStmt`, `ArithVolNefStmt`, `ArithVolMultStmt`, `HSUse`,
     **`arith_hilbert_samuel_of_systems`**, **`hsUse_outright`**, `height_lower_from_hsUse`,
     and `l3_covolume_from_hsChain`.

6. **Concrete Zero-Assumption Realizations (`0` Assumptions)**:
   - Projective space `ℙ^d` with `𝒪(1)_{-α}` (`projSpaceHSChainSystem`, `projSpace_hsUse_outright`),
   - Graded CM Hermitian symmetric-power algebras from `Stage12SchurWeylLattices.CMHermLattice`
     (`cmHermHSChainSystem`, `cmHerm_hsUse_outright`),
   - Arithmetic surface `d = 1` models from `Stage11ArakelovFaltings.ArithSurfaceModel`
     (`arithSurfaceHSChainSystem`, `arithSurface_hsUse_outright`).
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Set Matrix
open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  covol_bot degAr_bot slope_le_muMax)
open RHDirect.Stage2SiegelReduction (gsVec gsCoeff gsCoeff_self gsCoeff_of_lt gsCoeff_of_gt
  gs_expansion gsVec_orthogonal gsVec_ne_zero_of_linearIndependent covol_eq_prod_gsVec
  covol_le_prod_norm lattice_inter_closedBall_finite lambda1 lambda1_pos succMin succMin_pos)
open RHDirect.Stage4ArakelovBost (IsSaturated projOrth quotLat
  discreteTopology_quotLat rk_add_quotLat covol_eq_mul_quotLat degAr_eq_add_quotLat)
open RHDirect.Stage11MoriwakiCovolume (arithDeg arithDeg_eq_rk_mul_slope scaleLat
  scaleLat_invariants slope_scaleLat arithDeg_exact_seq arithDeg_eq_of_isometric_equiv
  unitBallVol unitBallVol_pos volume_closedBall_eq_unitBallVol volume_ball_eq_unitBallVol
  log_unitBallVol_ge h0Arith h0ArithStrict h0ArithStrict_le_h0Arith h0Arith_mono
  one_le_h0Arith one_le_h0ArithStrict log_h0ArithStrict_lower_bound log_h0Arith_lower_bound
  moriwaki_small_section_count MultiIndex card_multiIndex card_multiIndex_pos
  diagLat diagLat_invariants symPowWeightedLat symPowMonomialLat
  arithDeg_symPowWeightedLat slope_symPowMonomialLat)
open RHDirect.Stage11ArakelovFaltings (HermVectorBundle ArithSurfaceModel)
open RHDirect.Stage12SchurWeylLattices (CMHermLattice GradedHermAlgebra
  moriwaki_big_small_sections pow_div_factorial_le_choose choose_le_const_mul_pow
  L3_hodge_covolume_bound)
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology

namespace RHDirect.Stage14M4_ArithHilbertSamuelCore

/-! ## Section 1: Exact Stirling Ball-Volume Sandwich & Babai Nearest-Plane Packing -/

section StirlingAndBabaiPacking

/-- **Unconditional Elementary Stirling Factorial Lower Bound**:
for every `n : ℕ`, `((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ)`. -/
theorem factorial_ge_pow_div_exp (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hexp_pos : 0 < Real.exp (n : ℝ) := Real.exp_pos (n : ℝ)
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hterm : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) (n + 1)
    have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
    have hle : (n : ℝ) ^ n / (n.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (n + 1), (n : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i : ℕ => (n : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => div_nonneg (pow_nonneg (Nat.cast_nonneg n) i) (Nat.cast_nonneg _)) hmem
    exact hle.trans hsum
  have hpow : (Real.exp 1) ^ n = Real.exp (n : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [div_pow, hpow, div_le_iff₀ hexp_pos]
  have h1 := (div_le_iff₀ hfac_pos).mp hterm
  linarith

/-- Half-integer Gamma product identity:
`Γ(m + 3 / 2) = (√π / 2) * ∏ j ∈ range m, ((j : ℝ) + 3 / 2)`. -/
private lemma gamma_nat_add_three_halves_eq (m : ℕ) :
    Real.Gamma ((m : ℝ) + 3 / 2) =
      (√Real.pi / 2) * ∏ j ∈ Finset.range m, ((j : ℝ) + 3 / 2) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Finset.range_zero, Finset.prod_empty, mul_one]
    have h : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ]
    have h : (m : ℝ) + 1 + 3 / 2 = ((m : ℝ) + 3 / 2) + 1 := by ring
    rw [h, Real.Gamma_add_one (by positivity), ih]
    ring

/-- Exact Legendre duplication identity for odd factorials:
`((2 * m + 1).factorial : ℝ) = (2 ^ m * ∏ j ∈ range m, ((j : ℝ) + 3 / 2)) * (2 ^ m * (m.factorial : ℝ))`. -/
private lemma odd_factorial_duplication (m : ℕ) :
    ((2 * m + 1).factorial : ℝ) =
      ((2 : ℝ) ^ m * ∏ j ∈ Finset.range m, ((j : ℝ) + 3 / 2)) *
        ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul, ih,
      Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring

/-- Helper: `(m.factorial : ℝ) = ∏ j ∈ Finset.range m, ((j : ℝ) + 1)`. -/
private lemma factorial_eq_prod_range (m : ℕ) :
    (m.factorial : ℝ) = ∏ j ∈ Finset.range m, ((j : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Finset.prod_range_succ, ih]
    push_cast; ring

/-- **Constant-Free Stirling Lower Bound for Half-Integer Gamma (`gamma_half_add_one_ge_stirling`)**:
for EVERY `r ≥ 1`, `((r : ℝ) / (2 * Real.exp 1)) ^ ((r : ℝ) / 2) ≤ Real.Gamma ((r : ℝ) / 2 + 1)`. -/
theorem gamma_half_add_one_ge_stirling {r : ℕ} (_hr : 1 ≤ r) :
    ((r : ℝ) / (2 * Real.exp 1)) ^ ((r : ℝ) / 2) ≤ Real.Gamma ((r : ℝ) / 2 + 1) := by
  rcases Nat.even_or_odd r with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hcast : ((m + m : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 1 := by push_cast; ring
    have hexp : ((m + m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
    have hbase : ((m + m : ℕ) : ℝ) / (2 * Real.exp 1) = (m : ℝ) / Real.exp 1 := by
      push_cast; ring
    rw [hcast, hexp, hbase, Real.rpow_natCast, Real.Gamma_nat_eq_factorial]
    exact factorial_ge_pow_div_exp m
  · have hcast : ((2 * m + 1 : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 3 / 2 := by push_cast; ring
    rw [hcast, gamma_nat_add_three_halves_eq m]
    set P : ℝ := ∏ j ∈ Finset.range m, ((j : ℝ) + 3 / 2)
    have hP_pos : 0 < P := Finset.prod_pos fun j _ => by positivity
    have hfac_le_P : (m.factorial : ℝ) ≤ P := by
      rw [factorial_eq_prod_range m]
      exact Finset.prod_le_prod (fun j _ => by positivity) fun j _ => by linarith
    have hodd_le : ((2 * m + 1).factorial : ℝ) ≤ ((2 : ℝ) ^ m * P) ^ 2 := by
      rw [odd_factorial_duplication m, sq]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfac_le_P (by positivity)) (by positivity)
    have hstirl := factorial_ge_pow_div_exp (2 * m + 1)
    have hcomb : (((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * m + 1) ≤ ((2 : ℝ) ^ m * P) ^ 2 :=
      hstirl.trans hodd_le
    have hbase_nn : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) / Real.exp 1 := by positivity
    have hbase2_nn : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1) := by positivity
    have hsqrt_le : Real.sqrt ((((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * m + 1)) ≤
        (2 : ℝ) ^ m * P := by
      calc Real.sqrt ((((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * m + 1))
          ≤ Real.sqrt (((2 : ℝ) ^ m * P) ^ 2) := Real.sqrt_le_sqrt hcomb
        _ = (2 : ℝ) ^ m * P := Real.sqrt_sq (by positivity)
    have hsqrt_eq : Real.sqrt ((((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * m + 1)) =
        (((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbase_nn]
      congr 1; ring
    rw [hsqrt_eq] at hsqrt_le
    have h2pow : (2 : ℝ) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) = √2 * (2 : ℝ) ^ m := by
      have hexp : (((2 * m + 1 : ℕ) : ℝ) / 2) = (1 / 2 : ℝ) + (m : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.sqrt_eq_rpow, Real.rpow_natCast]
    have hdiv_rpow : (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) =
        (((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) /
          (2 : ℝ) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
      rw [← Real.div_rpow hbase_nn (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; field_simp
    have hsqrt_2pi : 1 ≤ √Real.pi / √2 := by
      rw [one_le_div (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
      exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
    have hP_ge : √2 * (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) ≤ P := by
      rw [hdiv_rpow, h2pow]
      have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hs2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
      have hcancel : √2 * ((((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) /
          (√2 * (2 : ℝ) ^ m)) =
          (((2 * m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) / (2 : ℝ) ^ m := by
        field_simp [hs2_pos.ne', h2m_pos.ne']
      rw [hcancel, div_le_iff₀ h2m_pos]
      linarith
    have hfinal : (√Real.pi / 2) * (√2 * (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
        (((2 * m + 1 : ℕ) : ℝ) / 2)) ≤ (√Real.pi / 2) * P :=
      mul_le_mul_of_nonneg_left hP_ge (by positivity)
    have hcoeff : (√Real.pi / 2) * √2 = √Real.pi / √2 := by
      have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hs2_ne : √2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp [hs2_ne]
      nlinarith [hs2]
    have hmul_one : (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) ≤
        (√Real.pi / √2) *
          (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
      calc _ = 1 * _ := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt_2pi (Real.rpow_nonneg hbase2_nn _)
    calc (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2)
        ≤ (√Real.pi / √2) *
            (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := hmul_one
      _ = (√Real.pi / 2) * (√2 *
            (((2 * m + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (((2 * m + 1 : ℕ) : ℝ) / 2)) := by
          rw [← mul_assoc, hcoeff]
      _ ≤ (√Real.pi / 2) * P := hfinal

/-- **Exact Stirling Upper Bound on Unit-Ball Log-Volume (`log_unitBallVol_le_stirling`)**:
for EVERY `r ≥ 1`,
`Real.log (unitBallVol r) ≤ ((r : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) - ((r : ℝ) / 2) * Real.log (r : ℝ)`. -/
theorem log_unitBallVol_le_stirling {r : ℕ} (hr : 1 ≤ r) :
    Real.log (unitBallVol r) ≤
      ((r : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) - ((r : ℝ) / 2) * Real.log (r : ℝ) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have h2e_pos : (0 : ℝ) < 2 * Real.exp 1 := by positivity
  have hbase_pos : 0 < (r : ℝ) / (2 * Real.exp 1) := div_pos hrpos h2e_pos
  have hGpos : 0 < Real.Gamma ((r : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlogG : ((r : ℝ) / 2) * (Real.log (r : ℝ) - Real.log (2 * Real.exp 1)) ≤
      Real.log (Real.Gamma ((r : ℝ) / 2 + 1)) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hbase_pos _) (gamma_half_add_one_ge_stirling hr)
    rwa [Real.log_rpow hbase_pos, Real.log_div hrpos.ne' h2e_pos.ne'] at h
  have hlog_prod : Real.log (2 * Real.pi * Real.exp 1) =
      Real.log Real.pi + Real.log (2 * Real.exp 1) := by
    have heq : 2 * Real.pi * Real.exp 1 = Real.pi * (2 * Real.exp 1) := by ring
    rw [heq, Real.log_mul Real.pi_pos.ne' h2e_pos.ne']
  unfold unitBallVol
  rw [Real.log_div (pow_pos hpi r).ne' hGpos.ne', Real.log_pow, Real.log_sqrt Real.pi_pos.le,
    hlog_prod]
  linarith

/-- **Two-Sided Stirling Unit-Ball Log-Volume Sandwich (`log_unitBallVol_sandwich`)**:
for EVERY `r ≥ 1`,
`((r : ℝ) / 2) * log π - ((r : ℝ) / 2) * log r ≤ log (unitBallVol r) ≤ ((r : ℝ) / 2) * log (2 π e) - ((r : ℝ) / 2) * log r`. -/
theorem log_unitBallVol_sandwich {r : ℕ} (hr : 1 ≤ r) :
    ((r : ℝ) / 2) * Real.log Real.pi - ((r : ℝ) / 2) * Real.log (r : ℝ) ≤
      Real.log (unitBallVol r) ∧
    Real.log (unitBallVol r) ≤
      ((r : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) - ((r : ℝ) / 2) * Real.log (r : ℝ) :=
  ⟨log_unitBallVol_ge hr, log_unitBallVol_le_stirling hr⟩

/-! ### Babai Nearest-Plane Orthogonal Packing Upper Bound -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper: measurability of an axis-aligned half-open box in `EuclideanSpace ℝ (Fin r)`. -/
private lemma measurableSet_euclideanSpace_box {r : ℕ} (a b : Fin r → ℝ) :
    MeasurableSet { x : EuclideanSpace ℝ (Fin r) | ∀ i : Fin r, x i ∈ Set.Ico (a i) (b i) } := by
  have heq : { x : EuclideanSpace ℝ (Fin r) | ∀ i : Fin r, x i ∈ Set.Ico (a i) (b i) } =
      ⋂ i : Fin r, (fun x : EuclideanSpace ℝ (Fin r) => x i) ⁻¹' Set.Ico (a i) (b i) := by
    ext x; simp
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage (PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) i).measurable

/-- Helper: volume of an axis-aligned half-open box in `EuclideanSpace ℝ (Fin r)` equals the
product of its side lengths. -/
private lemma volume_euclideanSpace_box {r : ℕ} (a b : Fin r → ℝ) (hab : ∀ i, a i ≤ b i) :
    volume { x : EuclideanSpace ℝ (Fin r) | ∀ i : Fin r, x i ∈ Set.Ico (a i) (b i) } =
      ENNReal.ofReal (∏ i : Fin r, (b i - a i)) := by
  have hmeas := measurableSet_euclideanSpace_box a b
  have hpre : (WithLp.toLp 2) ⁻¹'
      { x : EuclideanSpace ℝ (Fin r) | ∀ i : Fin r, x i ∈ Set.Ico (a i) (b i) } =
      Set.univ.pi fun i : Fin r => Set.Ico (a i) (b i) := by
    ext x; simp [Set.mem_pi]
  rw [← (PiLp.volume_preserving_toLp (Fin r)).measure_preimage hmeas.nullMeasurableSet,
    hpre, MeasureTheory.volume_pi_pi]
  simp_rw [Real.volume_Ico]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => sub_nonneg.mpr (hab i)]

/-- **Babai Nearest-Plane Orthogonal Packing Upper Bound (`h0Arith_upper_bound_babai`)**:
For EVERY nonzero discrete Euclidean lattice `L ⊂ E` of rank `r = rk L`, ANY `ℤ`-basis
`b : Module.Basis (Fin r) ℤ L` whose Gram–Schmidt vectors satisfy `‖gsVec (fun i => (b i : E)) j‖ ≤ M`,
and ANY radius `R ≥ 0`:
`(h0Arith L R : ℝ) * covol L ≤ unitBallVol (rk L) * (R + (√(rk L : ℝ) / 2) * M) ^ (rk L)`. -/
theorem h0Arith_upper_bound_babai (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (b : Module.Basis (Fin (rk L)) ℤ L) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hgs : ∀ j : Fin (rk L), ‖gsVec (fun i => (b i : E)) j‖ ≤ M) :
    (h0Arith L R : ℝ) * covol L ≤
      unitBallVol (rk L) * (R + (√(rk L : ℝ) / 2) * M) ^ (rk L) := by
  classical
  let r := rk L
  have hr_pos : 0 < r := rk_pos_of_ne_bot L hL0
  let v : Fin r → E := fun i => (b i : E)
  have hv_li : LinearIndependent ℝ v := linearIndependent_coe_basis L b
  let u : Fin r → E := gsVec v
  have hu_ne : ∀ j : Fin r, u j ≠ 0 := gsVec_ne_zero_of_linearIndependent hv_li
  have hu_pos : ∀ j : Fin r, 0 < ‖u j‖ := fun j => norm_pos_iff.mpr (hu_ne j)
  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  have hu_memV : ∀ j : Fin r, u j ∈ V := by
    intro j
    have hrec : ∀ n : ℕ, ∀ k : Fin r, k.1 < n → gsVec v k ∈ V := by
      intro n
      induction n with
      | zero => intro k hk; omega
      | succ n ih =>
        intro k hk
        rw [gsVec]
        refine Submodule.sub_mem V (Submodule.subset_span (b k).2) ?_
        refine Submodule.sum_mem V fun i _ => ?_
        refine Submodule.smul_mem V _ (ih ⟨i.1, lt_trans i.2 k.2⟩ (by dsimp only; have := i.2; omega))
    exact hrec (r + 1) j (Nat.lt_succ_of_lt j.2)
  let eVec : Fin r → V := fun j => (‖u j‖⁻¹) • ⟨u j, hu_memV j⟩
  have he_ortho : Orthonormal ℝ eVec := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ ((‖u i‖⁻¹) • u i) ((‖u j‖⁻¹) • u j) = if i = j then 1 else 0
    rw [real_inner_smul_left, real_inner_smul_right]
    split_ifs with hij
    · subst hij
      rw [real_inner_self_eq_norm_sq]
      have hne : ‖u i‖ ≠ 0 := (hu_pos i).ne'
      field_simp [hne]
    · rw [gsVec_orthogonal v hij, mul_zero, mul_zero]
  have hdimV : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span L).symm
  let eBasis : OrthonormalBasis (Fin r) ℝ V :=
    OrthonormalBasis.mkOfOrthogonalEqBot he_ortho (by
      have hspan_top : Submodule.span ℝ (Set.range eVec) = ⊤ := by
        refine Submodule.eq_top_of_finrank_eq ?_
        rw [finrank_span_eq_card he_ortho.linearIndependent, Fintype.card_fin, hdimV]
      rw [hspan_top, Submodule.top_orthogonal_eq_bot])
  let Φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := eBasis.repr
  have hΦ_coord : ∀ (x : V) (j : Fin r), (Φ x) j = ‖u j‖⁻¹ * inner ℝ (u j) (x : E) := by
    intro x j
    change eBasis.repr x j = _
    rw [OrthonormalBasis.repr_apply_apply]
    have hej : eBasis j = eVec j := by simp [eBasis]
    rw [hej]
    change inner ℝ ((‖u j‖⁻¹) • u j) (x : E) = _
    rw [real_inner_smul_left]
  let B_GS : Set (EuclideanSpace ℝ (Fin r)) :=
    { y | ∀ j : Fin r, y j ∈ Set.Ico (-(‖u j‖ / 2)) (‖u j‖ / 2) }
  have hB_meas : MeasurableSet B_GS :=
    measurableSet_euclideanSpace_box (fun j => -(‖u j‖ / 2)) (fun j => ‖u j‖ / 2)
  have hB_vol : volume B_GS = ENNReal.ofReal (covol L) := by
    have hvol := volume_euclideanSpace_box (fun j => -(‖u j‖ / 2)) (fun j => ‖u j‖ / 2)
      (fun j => by linarith [hu_pos j])
    have hprod : ∏ j : Fin r, (‖u j‖ / 2 - -(‖u j‖ / 2)) = covol L := by
      rw [covol_eq_prod_gsVec b]
      refine Finset.prod_congr rfl fun j _ => by ring
    simpa only [B_GS, hprod] using hvol
  have hB_norm : ∀ y ∈ B_GS, ‖y‖ ≤ (√(r : ℝ) / 2) * M := by
    intro y hy
    have hsq : ‖y‖ ^ 2 ≤ ((√(r : ℝ) / 2) * M) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hterm : ∀ j : Fin r, ‖y j‖ ^ 2 ≤ (M / 2) ^ 2 := by
        intro j
        have hj := hy j
        have habs : |y j| ≤ ‖u j‖ / 2 := abs_le.mpr ⟨hj.1, hj.2.le⟩
        have hle : |y j| ≤ M / 2 := habs.trans (div_le_div_of_nonneg_right (hgs j) (by norm_num))
        rw [Real.norm_eq_abs]
        exact sq_le_sq' (by linarith [abs_nonneg (y j)]) hle
      calc ∑ j : Fin r, ‖y j‖ ^ 2
          ≤ ∑ _j : Fin r, (M / 2) ^ 2 := Finset.sum_le_sum fun j _ => hterm j
        _ = (r : ℝ) * (M / 2) ^ 2 := by simp
        _ = ((√(r : ℝ) / 2) * M) ^ 2 := by
            rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg r)]; ring
    have hrhs_nn : 0 ≤ (√(r : ℝ) / 2) * M :=
      mul_nonneg (div_nonneg (Real.sqrt_nonneg (r : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)) hM
    nlinarith [norm_nonneg y, hrhs_nn]
  let S : Set E := (L : Set E) ∩ Metric.closedBall 0 R
  have hSfin : S.Finite := lattice_inter_closedBall_finite L R
  let Sfin : Finset E := hSfin.toFinset
  have hcard_eq : h0Arith L R = Sfin.card := Set.ncard_eq_toFinset_card S hSfin
  let center : E → EuclideanSpace ℝ (Fin r) := fun x =>
    if hx : x ∈ L then Φ ⟨x, Submodule.subset_span hx⟩ else 0
  let cell : E → Set (EuclideanSpace ℝ (Fin r)) := fun x =>
    (fun y => center x + y) '' B_GS
  have hdisj : (Sfin : Set E).PairwiseDisjoint cell := by
    intro x₁ hx₁ x₂ hx₂ hne
    show Disjoint (cell x₁) (cell x₂)
    rw [Set.disjoint_left]
    rintro z ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, hEq⟩
    have hx₁L : x₁ ∈ L := (hSfin.mem_toFinset.mp hx₁).1
    have hx₂L : x₂ ∈ L := (hSfin.mem_toFinset.mp hx₂).1
    let w : L := ⟨x₁ - x₂, L.sub_mem hx₁L hx₂L⟩
    have hw_ne : w ≠ 0 := fun h0 => hne (sub_eq_zero.mp (congrArg Subtype.val h0))
    let m : Fin r → ℤ := fun j => b.repr w j
    have hm_nonempty : (Finset.univ.filter fun j : Fin r => m j ≠ 0).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hw_ne
      rw [← b.sum_repr w]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj0 : m j = 0 := by
        by_contra hmj
        have hmem : j ∈ Finset.univ.filter (fun j : Fin r => m j ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmj⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty j hmem
      simp [m, hj0]
    let k : Fin r := (Finset.univ.filter fun j : Fin r => m j ≠ 0).max' hm_nonempty
    have hk_ne : m k ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hm_nonempty)).2
    have hk_max : ∀ j : Fin r, k < j → m j = 0 := by
      intro j hkj
      by_contra hmj
      have hmem : j ∈ Finset.univ.filter (fun j : Fin r => m j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmj⟩
      have hle : j ≤ k := Finset.le_max' _ j hmem
      exact not_lt_of_ge hle hkj
    have hw_sum : (x₁ - x₂ : E) = ∑ j : Fin r, (m j : ℝ) • v j := by
      have hrep := congrArg Subtype.val (b.sum_repr w)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
      simpa only [← Int.cast_smul_eq_zsmul ℝ] using hrep.symm
    have hinner_w : inner ℝ (u k) (x₁ - x₂) = (m k : ℝ) * ‖u k‖ ^ 2 := by
      rw [hw_sum, inner_sum, Finset.sum_eq_single k]
      · rw [real_inner_smul_right, gs_expansion v k, inner_sum, Finset.sum_eq_single k]
        · rw [real_inner_smul_right, gsCoeff_self v k, one_mul, real_inner_self_eq_norm_sq]
        · intro i _ hik
          rw [real_inner_smul_right, gsVec_orthogonal v hik.symm, mul_zero]
        · intro h; exact absurd (Finset.mem_univ k) h
      · intro j _ hjk
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · rw [real_inner_smul_right, gs_expansion v j, inner_sum]
          have hzero : ∑ i : Fin r, inner ℝ (u k) (gsCoeff v i j • u i) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hik : i = k
            · subst hik
              rw [gsCoeff_of_gt v hlt, zero_smul, inner_zero_right]
            · rw [real_inner_smul_right, gsVec_orthogonal v (Ne.symm hik), mul_zero]
          rw [hzero, mul_zero]
        · rw [hk_max j hgt, Int.cast_zero, zero_smul, inner_zero_right]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hcoord_diff : (center x₁) k - (center x₂) k = (m k : ℝ) * ‖u k‖ := by
      simp only [center, dif_pos hx₁L, dif_pos hx₂L]
      have hsub_phi : (Φ ⟨x₁, Submodule.subset_span hx₁L⟩) k -
          (Φ ⟨x₂, Submodule.subset_span hx₂L⟩) k =
          (Φ ⟨x₁ - x₂, Submodule.subset_span (L.sub_mem hx₁L hx₂L)⟩) k := by
        have h1 : (⟨x₁, Submodule.subset_span hx₁L⟩ : V) - ⟨x₂, Submodule.subset_span hx₂L⟩ =
            ⟨x₁ - x₂, Submodule.subset_span (L.sub_mem hx₁L hx₂L)⟩ := rfl
        rw [← h1, map_sub]; rfl
      rw [hsub_phi, hΦ_coord, hinner_w]
      have hne_u : ‖u k‖ ≠ 0 := (hu_pos k).ne'
      field_simp [hne_u]
    have hEq_k : (center x₁) k + y₁ k = (center x₂) k + y₂ k := by
      have := congrArg (fun p : EuclideanSpace ℝ (Fin r) => p k) hEq
      simpa using this.symm
    have hy_diff : (m k : ℝ) * ‖u k‖ = y₂ k - y₁ k := by linarith
    have hmk_abs : (1 : ℝ) ≤ |(m k : ℝ)| := by
      have : (1 : ℤ) ≤ |m k| := Int.one_le_abs hk_ne
      exact_mod_cast this
    have hlhs_ge : ‖u k‖ ≤ |y₂ k - y₁ k| := by
      rw [← hy_diff, abs_mul, abs_of_pos (hu_pos k)]
      nlinarith [hu_pos k]
    have hrhs_lt : |y₂ k - y₁ k| < ‖u k‖ := by
      have h1 := hy₁ k
      have h2 := hy₂ k
      rw [abs_lt]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    linarith
  have hsub : ∀ x ∈ Sfin, cell x ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) (R + (√(r : ℝ) / 2) * M) := by
    intro x hx z hz
    rcases hz with ⟨y, hyB, rfl⟩
    have hxS := hSfin.mem_toFinset.mp hx
    have hxL : x ∈ L := hxS.1
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hxS.2
    have hcx : ‖center x‖ = ‖x‖ := by
      simp only [center, dif_pos hxL]
      exact Φ.norm_map ⟨x, Submodule.subset_span hxL⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖center x + y‖ ≤ ‖center x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + (√(r : ℝ) / 2) * M := add_le_add (hcx ▸ hxR) (hB_norm y hyB)
  have hcell_meas : ∀ x : E, MeasurableSet (cell x) := by
    intro x
    have heq : cell x = (fun z => z + (-center x)) ⁻¹' B_GS := by
      ext z
      simp only [cell, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa [add_comm, add_left_comm] using hy
      · intro hz; exact ⟨z + (-center x), hz, by abel⟩
    rw [heq]
    exact hB_meas.preimage (measurable_id.add_const _)
  have hcell_vol : ∀ x : E, volume (cell x) = ENNReal.ofReal (covol L) := by
    intro x
    have heq : cell x = (fun z => z + (-center x)) ⁻¹' B_GS := by
      ext z
      simp only [cell, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa [add_comm, add_left_comm] using hy
      · intro hz; exact ⟨z + (-center x), hz, by abel⟩
    rw [heq, MeasureTheory.measure_preimage_add_right, hB_vol]
  have hRtot_nn : 0 ≤ R + (√(r : ℝ) / 2) * M :=
    add_nonneg hR (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hM)
  have hunion : (Sfin.card : ℝ≥0∞) * ENNReal.ofReal (covol L) ≤
      ENNReal.ofReal (unitBallVol r * (R + (√(r : ℝ) / 2) * M) ^ r) := by
    calc (Sfin.card : ℝ≥0∞) * ENNReal.ofReal (covol L)
        = ∑ _x ∈ Sfin, ENNReal.ofReal (covol L) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ x ∈ Sfin, volume (cell x) := Finset.sum_congr rfl fun x _ => (hcell_vol x).symm
      _ = volume (⋃ x ∈ Sfin, cell x) :=
          (MeasureTheory.measure_biUnion_finset (μ := volume) hdisj (fun x _ => hcell_meas x)).symm
      _ ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) (R + (√(r : ℝ) / 2) * M)) := by
          refine measure_mono ?_
          intro z hz
          simp only [Set.mem_iUnion, exists_prop] at hz
          rcases hz with ⟨x, hx, hzx⟩
          exact hsub x hx hzx
      _ = ENNReal.ofReal (unitBallVol r * (R + (√(r : ℝ) / 2) * M) ^ r) :=
          volume_closedBall_eq_unitBallVol hr_pos hRtot_nn
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hunion
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (unitBallVol_pos r).le (pow_nonneg hRtot_nn r))).mp hunion
  rwa [hcard_eq]

/-- **Logarithmic Babai Nearest-Plane Upper Bound (`log_h0Arith_upper_bound_babai`)**:
under the same hypotheses with `0 < R + (√r / 2) * M`:
1. `log (h0Arith L R) ≤ arithDeg L + r * log (R + (√r / 2) * M) + log (unitBallVol r)`,
2. Using exact Stirling cancellation of `(r / 2) log r`:
   `log (h0Arith L R) ≤ arithDeg L + r * log (R / √r + M / 2) + (r / 2) * log (2 π e)`. -/
theorem log_h0Arith_upper_bound_babai (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (b : Module.Basis (Fin (rk L)) ℤ L) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hRM_pos : 0 < R + (√(rk L : ℝ) / 2) * M)
    (hgs : ∀ j : Fin (rk L), ‖gsVec (fun i => (b i : E)) j‖ ≤ M) :
    Real.log (h0Arith L R : ℝ) ≤
      arithDeg L + (rk L : ℝ) * Real.log (R + (√(rk L : ℝ) / 2) * M) +
        Real.log (unitBallVol (rk L)) ∧
    Real.log (h0Arith L R : ℝ) ≤
      arithDeg L + (rk L : ℝ) * Real.log (R / √(rk L : ℝ) + M / 2) +
        ((rk L : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) := by
  have hr : 1 ≤ rk L := rk_pos_of_ne_bot L hL0
  have hrpos : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr hr
  have hsqrtr_pos : 0 < √(rk L : ℝ) := Real.sqrt_pos.mpr hrpos
  have hcov_pos : 0 < covol L := covol_pos L
  have h0_pos : (0 : ℝ) < (h0Arith L R : ℝ) := Nat.cast_pos.mpr (one_le_h0Arith L hR)
  have hbabai := h0Arith_upper_bound_babai L hL0 b hM hR hgs
  have hlog := Real.log_le_log (mul_pos h0_pos hcov_pos) hbabai
  rw [Real.log_mul h0_pos.ne' hcov_pos.ne',
    Real.log_mul (unitBallVol_pos _).ne' (pow_pos hRM_pos _).ne', Real.log_pow] at hlog
  have h1 : Real.log (h0Arith L R : ℝ) ≤
      arithDeg L + (rk L : ℝ) * Real.log (R + (√(rk L : ℝ) / 2) * M) +
        Real.log (unitBallVol (rk L)) := by
    unfold arithDeg; linarith
  have hstirl := log_unitBallVol_le_stirling hr
  have hfactor : R + (√(rk L : ℝ) / 2) * M = √(rk L : ℝ) * (R / √(rk L : ℝ) + M / 2) := by
    field_simp [hsqrtr_pos.ne']
  have hinner_pos : 0 < R / √(rk L : ℝ) + M / 2 := by
    have hmul : 0 < √(rk L : ℝ) * (R / √(rk L : ℝ) + M / 2) := hfactor ▸ hRM_pos
    exact pos_of_mul_pos_right hmul hsqrtr_pos.le
  have hlog_fac : Real.log (R + (√(rk L : ℝ) / 2) * M) =
      (1 / 2) * Real.log (rk L : ℝ) + Real.log (R / √(rk L : ℝ) + M / 2) := by
    rw [hfactor, Real.log_mul hsqrtr_pos.ne' hinner_pos.ne', Real.log_sqrt hrpos.le]
    ring
  refine ⟨h1, ?_⟩
  rw [hlog_fac] at h1
  linarith

/-- **Two-Sided Lattice Section Counting Sandwich (`log_h0Arith_sandwich`)**:
combines Minkowski/Blichfeldt (`log_h0ArithStrict_lower_bound`) and Babai nearest-plane packing
(`log_h0Arith_upper_bound_babai`) for any radii `0 < R_lo ≤ R_hi`. -/
theorem log_h0Arith_sandwich (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (b : Module.Basis (Fin (rk L)) ℤ L) {M R_lo R_hi : ℝ}
    (hM : 0 ≤ M) (hRlo : 0 < R_lo) (hRhi : R_lo ≤ R_hi)
    (hgs : ∀ j : Fin (rk L), ‖gsVec (fun i => (b i : E)) j‖ ≤ M) :
    arithDeg L + (rk L : ℝ) * (Real.log (R_lo / 2) + (1 / 2) * Real.log Real.pi -
        (1 / 2) * Real.log (rk L : ℝ)) ≤
      Real.log (h0ArithStrict L R_lo : ℝ) ∧
    Real.log (h0ArithStrict L R_lo : ℝ) ≤ Real.log (h0Arith L R_hi : ℝ) ∧
    Real.log (h0Arith L R_hi : ℝ) ≤
      arithDeg L + (rk L : ℝ) * Real.log (R_hi / √(rk L : ℝ) + M / 2) +
        ((rk L : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) := by
  have hr : 1 ≤ rk L := rk_pos_of_ne_bot L hL0
  have hmink := log_h0ArithStrict_lower_bound L hRlo
  have hωlo := log_unitBallVol_ge hr
  have hlo : arithDeg L + (rk L : ℝ) * (Real.log (R_lo / 2) + (1 / 2) * Real.log Real.pi -
      (1 / 2) * Real.log (rk L : ℝ)) ≤ Real.log (h0ArithStrict L R_lo : ℝ) := by
    have : ((rk L : ℝ) / 2) * Real.log Real.pi - ((rk L : ℝ) / 2) * Real.log (rk L : ℝ) =
        (rk L : ℝ) * ((1 / 2) * Real.log Real.pi - (1 / 2) * Real.log (rk L : ℝ)) := by ring
    linarith
  have hmid : Real.log (h0ArithStrict L R_lo : ℝ) ≤ Real.log (h0Arith L R_hi : ℝ) := by
    have hpos : (0 : ℝ) < (h0ArithStrict L R_lo : ℝ) :=
      Nat.cast_pos.mpr (one_le_h0ArithStrict L hRlo)
    exact Real.log_le_log hpos (Nat.cast_le.mpr
      ((h0ArithStrict_le_h0Arith L R_lo).trans (h0Arith_mono L hRhi)))
  have hRhi_pos : 0 < R_hi := lt_of_lt_of_le hRlo hRhi
  have hRM_pos : 0 < R_hi + (√(rk L : ℝ) / 2) * M :=
    add_pos_of_pos_of_nonneg hRhi_pos (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hM)
  have hhi := (log_h0Arith_upper_bound_babai L hL0 b hM hRhi_pos.le hRM_pos hgs).2
  exact ⟨hlo, hmid, hhi⟩

/-! ### Arakelov Euler Characteristic `chiAr` & `HermVectorBundle` Bridge -/

/-- **Arakelov Euler Characteristic** `χ_Ar(L) = -log covol(L) = arithDeg(L)` of a Euclidean
section lattice `L ⊂ E` (Faltings / Gillet–Soulé normalization). -/
def chiAr (L : Submodule ℤ E) : ℝ := arithDeg L

@[simp]
lemma chiAr_eq_arithDeg (L : Submodule ℤ E) : chiAr L = arithDeg L := rfl

lemma chiAr_eq_neg_log_covol (L : Submodule ℤ E) : chiAr L = -Real.log (covol L) := rfl

theorem chiAr_eq_rk_mul_slope (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    chiAr L = (rk L : ℝ) * slope L :=
  arithDeg_eq_rk_mul_slope L hL0

theorem chiAr_scaleLat (L : Submodule ℤ E) [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    chiAr (scaleLat c L) = chiAr L - (rk L : ℝ) * Real.log c :=
  (scaleLat_invariants L hc).2.2.2

theorem chiAr_exact_seq {L M : Submodule ℤ E} [DiscreteTopology L] (hM : IsSaturated L M) :
    rk L = rk M + rk (quotLat L M) ∧ chiAr L = chiAr M + chiAr (quotLat L M) := by
  obtain ⟨hrk, _, hdeg⟩ := arithDeg_exact_seq hM
  exact ⟨hrk, hdeg⟩

/-- Bridge to `Stage11ArakelovFaltings.HermVectorBundle`: `chiAr B.euclLat = B.arakelovDeg`. -/
theorem chiAr_hermVectorBundle (B : HermVectorBundle) :
    chiAr B.euclLat = B.arakelovDeg := rfl

omit [FiniteDimensional ℝ E] in
/-- Homogeneity of Gram–Schmidt orthogonalization under positive scalar multiplication:
`gsVec (fun i => c • v i) j = c • gsVec v j`. -/
theorem gsVec_smul {r : ℕ} {c : ℝ} (hc : c ≠ 0) (v : Fin r → E) (j : Fin r) :
    gsVec (fun i => c • v i) j = c • gsVec v j := by
  have hrec : ∀ n : ℕ, ∀ k : Fin r, k.1 < n → gsVec (fun i => c • v i) k = c • gsVec v k := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih =>
      intro k hk
      rw [gsVec, gsVec, smul_sub, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : gsVec (fun t => c • v t) ⟨i.1, lt_trans i.2 k.2⟩ =
          c • gsVec v ⟨i.1, lt_trans i.2 k.2⟩ :=
        ih ⟨i.1, lt_trans i.2 k.2⟩ (by dsimp only; have := i.2; omega)
      dsimp only
      rw [hi, real_inner_smul_left, real_inner_smul_right, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs, smul_smul, smul_smul]
      congr 1
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
      by_cases hu : ‖gsVec v ⟨i.1, lt_trans i.2 k.2⟩‖ ^ 2 = 0
      · simp [hu]
      · field_simp [hc, hc2, hu]
  exact hrec (r + 1) j (Nat.lt_succ_of_lt j.2)

end StirlingAndBabaiPacking

/-! ## Section 2: Concrete Hilbert–Samuel Blocks `HSMBlock` & Block-Step Inequalities -/

section HSMBlocks

/-- **Concrete Hilbert–Samuel Block (`HSMBlock`)**:
models a graded arithmetic section lattice `H^0(𝒳, ℒ^{⊗ k})` equipped with:
- finite-dimensional Euclidean `L²` ambient space `E` and discrete nonzero lattice `L ⊂ E`,
- compact-manifold sup-norm `supNorm` with `L²`-vs-`L^∞` comparison constants `volConst > 0`
  (`‖s‖ ≤ volConst * supNorm s`) and `bergConst ≥ 1` (`supNorm s ≤ bergConst * ‖s‖`),
- Gram–Schmidt covering ceiling `gsCeil ≥ 0` witnessed by an explicit `ℤ`-basis `gsBasis` of `L`. -/
structure HSMBlock where
  E : Type*
  [normE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [fdE : FiniteDimensional ℝ E]
  L : Submodule ℤ E
  [discL : DiscreteTopology L]
  L_ne_bot : L ≠ ⊥
  supNorm : E → ℝ
  supNorm_nonneg : ∀ s, 0 ≤ supNorm s
  volConst : ℝ
  volConst_pos : 0 < volConst
  norm_le_vol_supNorm : ∀ s : E, ‖s‖ ≤ volConst * supNorm s
  bergConst : ℝ
  bergConst_ge_one : 1 ≤ bergConst
  supNorm_le_bergman : ∀ s : E, supNorm s ≤ bergConst * ‖s‖
  gsCeil : ℝ
  gsCeil_nonneg : 0 ≤ gsCeil
  gsBasis : Module.Basis (Fin (rk L)) ℤ L
  gsBasis_bound : ∀ j : Fin (rk L), ‖gsVec (fun i => (gsBasis i : E)) j‖ ≤ gsCeil

attribute [instance] HSMBlock.normE HSMBlock.innerE HSMBlock.fdE HSMBlock.discL

namespace HSMBlock

/-- Rank of the Hilbert–Samuel block `rk B := rk B.L`. -/
def blockRk (B : HSMBlock) : ℕ := rk B.L

theorem blockRk_pos (B : HSMBlock) : 1 ≤ B.blockRk :=
  rk_pos_of_ne_bot B.L B.L_ne_bot

/-- Arakelov Euler characteristic of the block `χ_Ar(B) = -log covol(B.L)`. -/
def blockChi (B : HSMBlock) : ℝ := chiAr B.L

/-- Arakelov slope of the block `μ(B) = χ_Ar(B) / rk(B)`. -/
def blockSlope (B : HSMBlock) : ℝ := slope B.L

theorem blockChi_eq_rk_mul_slope (B : HSMBlock) :
    B.blockChi = (B.blockRk : ℝ) * B.blockSlope :=
  chiAr_eq_rk_mul_slope B.L B.L_ne_bot

/-- **Exact `BlockChiCovolume` Gram-Determinant Identity (`blockChi_eq_neg_half_log_det_gram`)**:
for ANY `ℤ`-basis `b` of `B.L`,
`B.blockChi = -(1 / 2) * Real.log (Matrix.gram ℝ (fun i => (b i : B.E))).det`. -/
theorem blockChi_eq_neg_half_log_det_gram (B : HSMBlock)
    (b : Module.Basis (Fin (rk B.L)) ℤ B.L) :
    B.blockChi = -(1 / 2) * Real.log (Matrix.gram ℝ (fun i => (b i : B.E))).det := by
  unfold blockChi chiAr arithDeg
  rw [covol_eq_sqrt_det_gram B.L b, Real.log_sqrt (det_gram_basis_pos B.L b).le]
  ring

/-- Strictly small integral global sections `{ s ∈ B.L | B.supNorm s < 1 }`. -/
def smallSectionsSet (B : HSMBlock) : Set B.L :=
  { s : B.L | B.supNorm s.1 < 1 }

/-- Weakly small integral global sections `{ s ∈ B.L | B.supNorm s ≤ 1 }`. -/
def closedSmallSectionsSet (B : HSMBlock) : Set B.L :=
  { s : B.L | B.supNorm s.1 ≤ 1 }

theorem closedSmallSections_finite (B : HSMBlock) : B.closedSmallSectionsSet.Finite := by
  have hball := lattice_inter_closedBall_finite B.L B.volConst
  have hsub : Subtype.val '' B.closedSmallSectionsSet ⊆
      (B.L : Set B.E) ∩ Metric.closedBall 0 B.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := B.norm_le_vol_supNorm s.1
    have h2 : B.supNorm s.1 ≤ 1 := hs
    nlinarith [B.volConst_pos]
  exact Set.Finite.of_finite_image (hball.subset hsub) Subtype.val_injective.injOn

theorem smallSections_finite (B : HSMBlock) : B.smallSectionsSet.Finite :=
  B.closedSmallSections_finite.subset fun _ hs => le_of_lt (show B.supNorm _ < 1 from hs)

/-- Exact cardinality `#smallSections B` of strictly small global sections `‖s‖_sup < 1`. -/
def smallSectionsCard (B : HSMBlock) : ℕ :=
  B.smallSections_finite.toFinset.card

/-- Exact cardinality `#closedSmallSections B` of weakly small global sections `‖s‖_sup ≤ 1`. -/
def closedSmallSectionsCard (B : HSMBlock) : ℕ :=
  B.closedSmallSections_finite.toFinset.card

theorem smallSectionsCard_le_closed (B : HSMBlock) :
    B.smallSectionsCard ≤ B.closedSmallSectionsCard := by
  unfold smallSectionsCard closedSmallSectionsCard
  refine Finset.card_le_card fun s hs => ?_
  rw [Set.Finite.mem_toFinset] at hs ⊢
  exact le_of_lt (show B.supNorm s.1 < 1 from hs)

/-- Lower comparison against Euclidean strict-ball lattice count at radius `bergConst⁻¹`. -/
theorem h0ArithStrict_le_smallSectionsCard (B : HSMBlock) :
    h0ArithStrict B.L B.bergConst⁻¹ ≤ B.smallSectionsCard := by
  unfold h0ArithStrict smallSectionsCard
  have hBpos : 0 < B.bergConst := lt_of_lt_of_le zero_lt_one B.bergConst_ge_one
  have hsub : ((B.L : Set B.E) ∩ Metric.ball 0 B.bergConst⁻¹) ⊆
      Subtype.val '' B.smallSectionsSet := by
    rintro x ⟨hxL, hxB⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    change B.supNorm x < 1
    rw [Metric.mem_ball, dist_zero_right] at hxB
    have h1 := B.supNorm_le_bergman x
    have h2 : B.bergConst * ‖x‖ < B.bergConst * B.bergConst⁻¹ :=
      mul_lt_mul_of_pos_left hxB hBpos
    rw [mul_inv_cancel₀ hBpos.ne'] at h2
    exact lt_of_le_of_lt h1 h2
  have hfinImg : (Subtype.val '' B.smallSectionsSet).Finite :=
    B.smallSections_finite.image Subtype.val
  calc ((B.L : Set B.E) ∩ Metric.ball 0 B.bergConst⁻¹).ncard
      ≤ (Subtype.val '' B.smallSectionsSet).ncard := Set.ncard_le_ncard hsub hfinImg
    _ = B.smallSectionsSet.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    _ = B.smallSections_finite.toFinset.card :=
        Set.ncard_eq_toFinset_card B.smallSectionsSet B.smallSections_finite

/-- Upper comparison against Euclidean closed-ball lattice count at radius `volConst`. -/
theorem closedSmallSectionsCard_le_h0Arith (B : HSMBlock) :
    B.closedSmallSectionsCard ≤ h0Arith B.L B.volConst := by
  unfold closedSmallSectionsCard h0Arith
  have hsub : Subtype.val '' B.closedSmallSectionsSet ⊆
      (B.L : Set B.E) ∩ Metric.closedBall 0 B.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := B.norm_le_vol_supNorm s.1
    have h2 : B.supNorm s.1 ≤ 1 := hs
    nlinarith [B.volConst_pos]
  calc B.closedSmallSections_finite.toFinset.card
      = B.closedSmallSectionsSet.ncard :=
          (Set.ncard_eq_toFinset_card B.closedSmallSectionsSet B.closedSmallSections_finite).symm
    _ = (Subtype.val '' B.closedSmallSectionsSet).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((B.L : Set B.E) ∩ Metric.closedBall 0 B.volConst).ncard :=
          Set.ncard_le_ncard hsub (lattice_inter_closedBall_finite B.L B.volConst)

theorem smallSectionsCard_le_h0Arith (B : HSMBlock) :
    B.smallSectionsCard ≤ h0Arith B.L B.volConst :=
  B.smallSectionsCard_le_closed.trans B.closedSmallSectionsCard_le_h0Arith

theorem one_le_smallSectionsCard (B : HSMBlock) : 1 ≤ B.smallSectionsCard := by
  have hBpos : 0 < B.bergConst⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one B.bergConst_ge_one)
  exact (one_le_h0ArithStrict B.L hBpos).trans B.h0ArithStrict_le_smallSectionsCard

/-- **Finite-Level Two-Sided Block Section Counting Sandwich (`log_smallSections_sandwich`)**:
for EVERY `HSMBlock`, unconditionally relates `log (#smallSections B)` to `B.blockChi`:
1. Lower bound (Minkowski/Blichfeldt):
   `B.blockChi - rk * (log (2 * bergConst) + (1/2) * log rk - (1/2) * log π) ≤ log (#smallSections B)`,
2. Upper bound (Babai nearest-plane packing + Stirling):
   `log (#smallSections B) ≤ B.blockChi + rk * log (volConst / √rk + gsCeil / 2) + (rk / 2) * log (2 π e)`. -/
theorem log_smallSections_sandwich (B : HSMBlock) :
    B.blockChi - (B.blockRk : ℝ) *
        (Real.log (2 * B.bergConst) + (1 / 2) * Real.log (B.blockRk : ℝ) -
          (1 / 2) * Real.log Real.pi) ≤
      Real.log (B.smallSectionsCard : ℝ) ∧
    Real.log (B.smallSectionsCard : ℝ) ≤
      B.blockChi + (B.blockRk : ℝ) *
          Real.log (B.volConst / √(B.blockRk : ℝ) + B.gsCeil / 2) +
        ((B.blockRk : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) := by
  have hBpos : 0 < B.bergConst := lt_of_lt_of_le zero_lt_one B.bergConst_ge_one
  have hRlo : 0 < B.bergConst⁻¹ := inv_pos.mpr hBpos
  have hr : 1 ≤ B.blockRk := B.blockRk_pos
  have hmink := log_h0ArithStrict_lower_bound B.L hRlo
  have hωlo : ((rk B.L : ℝ) / 2) * Real.log Real.pi - ((rk B.L : ℝ) / 2) * Real.log (rk B.L : ℝ) ≤
      Real.log (unitBallVol (rk B.L)) := log_unitBallVol_ge hr
  have hlog_Rlo : Real.log (B.bergConst⁻¹ / 2) = -Real.log (2 * B.bergConst) := by
    have heq : B.bergConst⁻¹ / 2 = (2 * B.bergConst)⁻¹ := by field_simp [hBpos.ne']
    rw [heq, Real.log_inv]
  have hpos_strict : (0 : ℝ) < (h0ArithStrict B.L B.bergConst⁻¹ : ℝ) :=
    Nat.cast_pos.mpr (one_le_h0ArithStrict B.L hRlo)
  have hmono_lo : Real.log (h0ArithStrict B.L B.bergConst⁻¹ : ℝ) ≤
      Real.log (B.smallSectionsCard : ℝ) :=
    Real.log_le_log hpos_strict (Nat.cast_le.mpr B.h0ArithStrict_le_smallSectionsCard)
  have hlo : B.blockChi - (B.blockRk : ℝ) *
      (Real.log (2 * B.bergConst) + (1 / 2) * Real.log (B.blockRk : ℝ) -
        (1 / 2) * Real.log Real.pi) ≤ Real.log (B.smallSectionsCard : ℝ) := by
    dsimp only [blockChi, blockRk, chiAr]
    rw [hlog_Rlo] at hmink
    have hmul : ((rk B.L : ℝ) / 2) * Real.log Real.pi - ((rk B.L : ℝ) / 2) * Real.log (rk B.L : ℝ) =
        (rk B.L : ℝ) * ((1 / 2) * Real.log Real.pi - (1 / 2) * Real.log (rk B.L : ℝ)) := by ring
    linarith
  have hpos_small : (0 : ℝ) < (B.smallSectionsCard : ℝ) :=
    Nat.cast_pos.mpr B.one_le_smallSectionsCard
  have hmono_hi : Real.log (B.smallSectionsCard : ℝ) ≤ Real.log (h0Arith B.L B.volConst : ℝ) :=
    Real.log_le_log hpos_small (Nat.cast_le.mpr B.smallSectionsCard_le_h0Arith)
  have hRM_pos : 0 < B.volConst + (√(rk B.L : ℝ) / 2) * B.gsCeil :=
    add_pos_of_pos_of_nonneg B.volConst_pos
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) B.gsCeil_nonneg)
  have hbabai := (log_h0Arith_upper_bound_babai B.L B.L_ne_bot B.gsBasis
    B.gsCeil_nonneg B.volConst_pos.le hRM_pos B.gsBasis_bound).2
  exact ⟨hlo, hmono_hi.trans hbabai⟩

/-- Canonical `ℤ`-linear equivalence `B.L ≃ₗ[ℤ] scaleLat c B.L` for `c > 0`. -/
def scaleEquiv (B : HSMBlock) {c : ℝ} (hc : 0 < c) : B.L ≃ₗ[ℤ] scaleLat c B.L where
  toFun x := ⟨c • (x : B.E), ⟨(x : B.E), x.2, rfl⟩⟩
  invFun y := ⟨c⁻¹ • (y : B.E), by
    rcases y.2 with ⟨x, hxL, hxy⟩
    have hx : c⁻¹ • (y : B.E) = x := by
      have hy : (y : B.E) = c • x := hxy.symm
      rw [hy, inv_smul_smul₀ hc.ne']
    rwa [hx]⟩
  map_add' _ _ := Subtype.ext (by simp [smul_add])
  map_smul' n x := Subtype.ext (by
    change c • (n • (x : B.E)) = n • (c • (x : B.E))
    rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, smul_comm])
  left_inv _ := Subtype.ext (by simp [inv_smul_smul₀ hc.ne'])
  right_inv _ := Subtype.ext (by simp [smul_inv_smul₀ hc.ne'])

/-- Uniform metric scaling `B.scaleMetric hc` (`c > 0`): scales `B.L` to `scaleLat c B.L` inside
the same ambient Euclidean space `B.E`, preserving `volConst` and `bergConst` identically,
scaling `gsCeil` to `c * B.gsCeil`, and shifting `blockChi` by `-rk B * log c`. -/
def scaleMetric (B : HSMBlock) {c : ℝ} (hc : 0 < c) : HSMBlock where
  E := B.E
  L := scaleLat c B.L
  discL := (scaleLat_invariants B.L hc).1
  L_ne_bot := by
    intro hbot
    have hrk := (scaleLat_invariants B.L hc).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ B.E) = 0 by simp [rk]] at hrk
    have hpos := B.blockRk_pos
    unfold blockRk at hpos
    omega
  supNorm := B.supNorm
  supNorm_nonneg := B.supNorm_nonneg
  volConst := B.volConst
  volConst_pos := B.volConst_pos
  norm_le_vol_supNorm := B.norm_le_vol_supNorm
  bergConst := B.bergConst
  bergConst_ge_one := B.bergConst_ge_one
  supNorm_le_bergman := B.supNorm_le_bergman
  gsCeil := c * B.gsCeil
  gsCeil_nonneg := mul_nonneg hc.le B.gsCeil_nonneg
  gsBasis := (B.gsBasis.map (B.scaleEquiv hc)).reindex (finCongr (scaleLat_invariants B.L hc).2.1.symm)
  gsBasis_bound := by
    intro j
    have hrk : rk (scaleLat c B.L) = rk B.L := (scaleLat_invariants B.L hc).2.1
    let e := finCongr hrk.symm
    have hfun : (fun i : Fin (rk (scaleLat c B.L)) =>
        (((B.gsBasis.map (B.scaleEquiv hc)).reindex e i : scaleLat c B.L) : B.E)) =
        fun i => c • (B.gsBasis (e.symm i) : B.E) := by
      funext i
      simp [Basis.reindex_apply, Basis.map_apply, scaleEquiv]
    rw [hfun, gsVec_smul hc.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    -- Reindexing by `finCongr` preserves `gsVec` coordinatewise.
    have hreidx : ∀ (k : Fin (rk (scaleLat c B.L))),
        gsVec (fun i => (B.gsBasis (e.symm i) : B.E)) k =
          gsVec (fun i => (B.gsBasis i : B.E)) (e.symm k) := by
      intro k
      have hrec : ∀ n : ℕ, ∀ t : Fin (rk (scaleLat c B.L)), t.1 < n →
          gsVec (fun i => (B.gsBasis (e.symm i) : B.E)) t =
            gsVec (fun i => (B.gsBasis i : B.E)) (e.symm t) := by
        intro n
        induction n with
        | zero => intro t ht; omega
        | succ n ih =>
          intro t ht
          rw [gsVec, gsVec]
          congr 1
          have heval : (e.symm t).1 = t.1 := rfl
          refine Finset.sum_bij (fun i _ => ⟨i.1, by omega⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => Fin.ext (Fin.mk.inj h))
            (fun b _ => ⟨⟨b.1, by omega⟩, Finset.mem_univ _, by ext; rfl⟩)
            (fun i _ => ?_)
          have hi := ih ⟨i.1, lt_trans i.2 t.2⟩ (by dsimp only; have := i.2; omega)
          have hfin : e.symm ⟨i.1, lt_trans i.2 t.2⟩ = ⟨i.1, lt_trans (by omega) (e.symm t).2⟩ := by
            ext; rfl
          rw [hi, hfin]
      exact hrec (rk (scaleLat c B.L) + 1) k (Nat.lt_succ_of_lt k.2)
    rw [hreidx j]
    exact mul_le_mul_of_nonneg_left (B.gsBasis_bound (e.symm j)) hc.le

theorem scaleMetric_invariants (B : HSMBlock) {c : ℝ} (hc : 0 < c) :
    (B.scaleMetric hc).blockRk = B.blockRk ∧
    (B.scaleMetric hc).blockChi = B.blockChi - (B.blockRk : ℝ) * Real.log c ∧
    (B.scaleMetric hc).blockSlope = B.blockSlope - Real.log c := by
  refine ⟨(scaleLat_invariants B.L hc).2.1, (scaleLat_invariants B.L hc).2.2.2,
    slope_scaleLat B.L B.L_ne_bot hc⟩

/-- Explicit orthogonal `ℤ`-basis of `diagLat c` (`c i > 0`). -/
private def diagLatBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) : Module.Basis (Fin (rk (diagLat c))) ℤ (diagLat c) :=
  let hrk : rk (diagLat c) = Fintype.card ι := (diagLat_invariants c hc).2.1
  let e : Fin (rk (diagLat c)) ≃ ι := (finCongr hrk).trans (Fintype.equivFin ι).symm
  let gen : Fin (rk (diagLat c)) → diagLat c := fun j =>
    ⟨c (e j) • EuclideanSpace.single (e j) (1 : ℝ), Submodule.subset_span ⟨e j, rfl⟩⟩
  have hliR : LinearIndependent ℝ (fun j => (gen j : EuclideanSpace ℝ ι)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hcoord := congrFun (congrArg WithLp.ofLp hg) (e j)
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, gen, EuclideanSpace.single, PiLp.single_apply] at hcoord
    rw [Finset.sum_eq_single j] at hcoord
    · simp only [↓reduceIte, mul_one] at hcoord
      exact (mul_eq_zero.mp hcoord).resolve_right (hc (e j)).ne'
    · intro k _ hkj
      have hne : e j ≠ e k := fun h => hkj (e.injective h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hliZ : LinearIndependent ℤ gen := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : ∑ k, (g k : ℝ) • (gen k : EuclideanSpace ℝ ι) = 0 := by
      have h2 := congrArg Subtype.val hg
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Int.cast_smul_eq_zsmul] using h2
    exact_mod_cast Fintype.linearIndependent_iff.mp hliR (fun k => (g k : ℝ)) h1 j
  have hspZ : ⊤ ≤ Submodule.span ℤ (Set.range gen) := by
    intro x _
    have hx : (x : EuclideanSpace ℝ ι) ∈
        Submodule.span ℤ (Set.range fun i : ι => c i • (EuclideanSpace.single i (1 : ℝ))) := x.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨a, ha⟩ := hx
    have hxeq : x = ∑ j, a (e j) • gen j := by
      apply Subtype.ext
      rw [Submodule.coe_sum, ← ha]
      exact (Fintype.sum_equiv e _ _ (fun j => by simp [gen])).symm
    rw [hxeq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  Basis.mk hliZ hspZ

/-- Construct an `HSMBlock` directly from any nonzero orthogonal diagonal lattice `diagLat c`
(`ι` finite nonempty, `c i > 0`, with ceiling `M ≥ c i` for all `i`). -/
def ofDiagLat {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (M : ℝ) (hM : ∀ i, c i ≤ M) : HSMBlock where
  E := EuclideanSpace ℝ ι
  L := diagLat c
  discL := (diagLat_invariants c hc).1
  L_ne_bot := by
    intro hbot
    have hrk := (diagLat_invariants c hc).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) = 0 by simp [rk]] at hrk
    exact (Fintype.card_pos (α := ι)).ne hrk
  supNorm s := ‖s‖
  supNorm_nonneg s := norm_nonneg s
  volConst := 1
  volConst_pos := zero_lt_one
  norm_le_vol_supNorm s := by simp
  bergConst := 1
  bergConst_ge_one := le_rfl
  supNorm_le_bergman s := by simp
  gsCeil := M
  gsCeil_nonneg := le_trans (hc (Classical.arbitrary ι)).le (hM _)
  gsBasis := diagLatBasis c hc
  gsBasis_bound := by
    intro j
    let hrk : rk (diagLat c) = Fintype.card ι := (diagLat_invariants c hc).2.1
    let e : Fin (rk (diagLat c)) ≃ ι := (finCongr hrk).trans (Fintype.equivFin ι).symm
    have hnorm : ‖((diagLatBasis c hc) j : EuclideanSpace ℝ ι)‖ = c (e j) := by
      simp only [diagLatBasis, Basis.coe_mk, norm_smul, Real.norm_eq_abs]
      have h1 : ‖EuclideanSpace.single (e j) (1 : ℝ)‖ = 1 := by
        simp [EuclideanSpace.single, PiLp.norm_single]
      rw [h1, mul_one, abs_of_pos (hc _)]
    exact (RHDirect.Stage2SiegelReduction.gsVec_norm_le _ j).trans (hnorm.le.trans (hM (e j)))

theorem ofDiagLat_invariants {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (M : ℝ) (hM : ∀ i, c i ≤ M) :
    (ofDiagLat c hc M hM).blockRk = Fintype.card ι ∧
    (ofDiagLat c hc M hM).blockChi = -∑ i : ι, Real.log (c i) := by
  have hd := diagLat_invariants c hc
  exact ⟨hd.2.1, hd.2.2.2⟩

/-- Construct an `HSMBlock` directly from any nonzero `Stage11ArakelovFaltings.HermVectorBundle`. -/
def ofHermVectorBundle (H : HermVectorBundle) (hr : 0 < H.rk) : HSMBlock :=
  let b := Module.finBasis ℤ H.euclLat
  let M : ℝ := ∑ j : Fin (rk H.euclLat), ‖(b j : EuclideanSpace ℝ (Fin H.rk))‖
  { E := EuclideanSpace ℝ (Fin H.rk)
    L := H.euclLat
    L_ne_bot := H.euclLat_ne_bot_of_rk_pos hr
    supNorm := fun s => ‖s‖
    supNorm_nonneg := fun s => norm_nonneg s
    volConst := 1
    volConst_pos := zero_lt_one
    norm_le_vol_supNorm := fun _ => by simp
    bergConst := 1
    bergConst_ge_one := le_rfl
    supNorm_le_bergman := fun _ => by simp
    gsCeil := M
    gsCeil_nonneg := Finset.sum_nonneg fun _ _ => norm_nonneg _
    gsBasis := b
    gsBasis_bound := fun j =>
      (RHDirect.Stage2SiegelReduction.gsVec_norm_le _ j).trans
        (Finset.single_le_sum (f := fun i : Fin (rk H.euclLat) =>
          ‖(b i : EuclideanSpace ℝ (Fin H.rk))‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)) }

theorem ofHermVectorBundle_invariants (H : HermVectorBundle) (hr : 0 < H.rk) :
    (ofHermVectorBundle H hr).blockRk = H.rk ∧
    (ofHermVectorBundle H hr).blockChi = H.arakelovDeg :=
  ⟨by unfold blockRk ofHermVectorBundle; exact H.rk_euclLat, rfl⟩

end HSMBlock

/-! ### Block-Step Morphisms & Exact-Sequence Euler Characteristic Inequalities -/

/-- **Hilbert–Samuel Block-Step Morphism (`HSMBlockStep B₁ B₂`)**:
a `ℤ`-linear lattice map `f : B₁.L →ₗ[ℤ] B₂.L` (e.g., multiplication by a nonzero section `s₀`,
Veronese embedding, or Koszul restriction) with explicit archimedean operator norm bound `opBound > 0`. -/
structure HSMBlockStep (B₁ B₂ : HSMBlock) where
  toLinearMap : B₁.L →ₗ[ℤ] B₂.L
  opBound : ℝ
  opBound_pos : 0 < opBound
  norm_map_le : ∀ x : B₁.L, ‖((toLinearMap x : B₂.L) : B₂.E)‖ ≤ opBound * ‖(x : B₁.E)‖

/-- **Block-Step Sublattice Covolume & Euler Characteristic Inequality (`hsmBlockStep_sublattice_chi_ineq`)**:
If `f : HSMBlockStep B₁ B₂` is injective with saturated image `M := range (B₂.L.subtype ∘ f) ≤ B₂.L`:
1. Exact rank additivity `B₂.blockRk = B₁.blockRk + rk (quotLat B₂.L M)`,
2. Exact sublattice/quotient decomposition `B₂.blockChi = chiAr M + chiAr (quotLat B₂.L M)`,
3. Hadamard/Gram–Schmidt archimedean control:
   `B₁.blockChi - (B₁.blockRk : ℝ) * log f.opBound ≤ chiAr M` (when `f` admits an `ℝ`-linear
   contractive extension `F : B₁.E →ₗ[ℝ] B₂.E` matching `f` with `‖F x‖ ≤ f.opBound * ‖x‖`),
4. Consequently, `B₁.blockChi - (B₁.blockRk : ℝ) * log f.opBound + chiAr (quotLat B₂.L M) ≤ B₂.blockChi`! -/
theorem hsmBlockStep_sublattice_chi_ineq {B₁ B₂ : HSMBlock} (f : HSMBlockStep B₁ B₂)
    (hinj : Function.Injective f.toLinearMap)
    (hsat : IsSaturated B₂.L (LinearMap.range (B₂.L.subtype.comp f.toLinearMap)))
    (F : B₁.E →ₗ[ℝ] B₂.E) (hF_agree : ∀ x : B₁.L, F (x : B₁.E) = ((f.toLinearMap x : B₂.L) : B₂.E))
    (hF_bound : ∀ v : B₁.E, ‖F v‖ ≤ f.opBound * ‖v‖) :
    let M : Submodule ℤ B₂.E := LinearMap.range (B₂.L.subtype.comp f.toLinearMap)
    haveI : DiscreteTopology M := discreteTopology_of_le hsat.1
    B₂.blockRk = B₁.blockRk + rk (quotLat B₂.L M) ∧
    B₂.blockChi = chiAr M + chiAr (quotLat B₂.L M) ∧
    B₁.blockChi - (B₁.blockRk : ℝ) * Real.log f.opBound ≤ chiAr M ∧
    B₁.blockChi - (B₁.blockRk : ℝ) * Real.log f.opBound + chiAr (quotLat B₂.L M) ≤ B₂.blockChi := by
  intro M
  have : DiscreteTopology M := discreteTopology_of_le hsat.1
  have : DiscreteTopology (quotLat B₂.L M) := discreteTopology_quotLat hsat
  let e₁ : B₁.L ≃ₗ[ℤ] M :=
    LinearEquiv.ofInjective (B₂.L.subtype.comp f.toLinearMap) (B₂.L.injective_subtype.comp hinj)
  have hrkM : rk M = B₁.blockRk := e₁.symm.finrank_eq
  obtain ⟨hrk_add, hchi_add⟩ := chiAr_exact_seq hsat
  change rk B₂.L = rk M + rk (quotLat B₂.L M) at hrk_add
  change chiAr B₂.L = chiAr M + chiAr (quotLat B₂.L M) at hchi_add
  let r := B₁.blockRk
  let b₁ : Module.Basis (Fin r) ℤ B₁.L := Module.finBasis ℤ B₁.L
  let bM : Module.Basis (Fin r) ℤ M := b₁.map e₁
  let v₁ : Fin r → B₁.E := fun i => (b₁ i : B₁.E)
  let u₁ : Fin r → B₁.E := gsVec v₁
  let U : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => gsCoeff v₁ i j
  have hU_tri : U.BlockTriangular id := fun _ _ hij => gsCoeff_of_gt v₁ hij
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_tri]
    exact Finset.prod_eq_one fun i _ => gsCoeff_self v₁ i
  have hbM_eq : (fun j : Fin r => (bM j : B₂.E)) = fun j => ∑ i : Fin r, U i j • F (u₁ i) := by
    funext j
    have hj : (bM j : B₂.E) = F (v₁ j) := (hF_agree (b₁ j)).symm
    rw [hj, gs_expansion v₁ j, map_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  have hdet_eq : (Matrix.gram ℝ (fun j : Fin r => (bM j : B₂.E))).det =
      (Matrix.gram ℝ (fun j : Fin r => F (u₁ j))).det := by
    rw [hbM_eq, RHDirect.ArakelovCovolume.gram_sum_smul_eq_transpose_mul (fun j => F (u₁ j)) U,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUdet]
    ring
  have hhad : Real.sqrt (Matrix.gram ℝ (fun j : Fin r => F (u₁ j))).det ≤
      ∏ j : Fin r, ‖F (u₁ j)‖ :=
    RHDirect.Stage2SiegelReduction.hadamard_det_gram_le (fun j => F (u₁ j))
  have hcovM_eq : covol M = Real.sqrt (Matrix.gram ℝ (fun j : Fin r => (bM j : B₂.E))).det := by
    let he : Fin (rk M) ≃ Fin r := finCongr hrkM
    rw [covol_eq_sqrt_det_gram M (bM.reindex he.symm)]
    have hsubm : Matrix.gram ℝ (fun i : Fin (rk M) => ((bM.reindex he.symm i : M) : B₂.E)) =
        (Matrix.gram ℝ (fun j : Fin r => (bM j : B₂.E))).submatrix he he := by
      ext i j; simp [Matrix.gram_apply]
    rw [hsubm, Matrix.det_submatrix_equiv_self]
  have hcovM_le : covol M ≤ f.opBound ^ r * covol B₁.L := by
    calc covol M
        = Real.sqrt (Matrix.gram ℝ (fun j : Fin r => F (u₁ j))).det := by rw [hcovM_eq, hdet_eq]
      _ ≤ ∏ j : Fin r, ‖F (u₁ j)‖ := hhad
      _ ≤ ∏ j : Fin r, (f.opBound * ‖u₁ j‖) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => hF_bound (u₁ j)
      _ = (∏ _j : Fin r, f.opBound) * (∏ j : Fin r, ‖u₁ j‖) := Finset.prod_mul_distrib
      _ = f.opBound ^ r * covol B₁.L := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← covol_eq_prod_gsVec b₁]
  have hlog := Real.log_le_log (covol_pos M) hcovM_le
  rw [Real.log_mul (pow_pos f.opBound_pos r).ne' (covol_pos B₁.L).ne', Real.log_pow] at hlog
  have hchiM : B₁.blockChi - (B₁.blockRk : ℝ) * Real.log f.opBound ≤ chiAr M := by
    change -Real.log (covol B₁.L) - (r : ℝ) * Real.log f.opBound ≤ -Real.log (covol M)
    linarith
  exact ⟨by change rk B₂.L = B₁.blockRk + rk (quotLat B₂.L M); rw [← hrkM]; exact hrk_add,
    hchi_add, hchiM, by change _ ≤ chiAr B₂.L; linarith⟩

/-- **Short Exact Sequence of Hilbert–Samuel Blocks (`HSMBlockExactSeq B_sub B B_quot`)**:
models a Koszul / hyperplane restriction short exact sequence
`0 → H^0(X, L^{⊗ k}) → H^0(X, L^{⊗ (k+1)}) → H^0(D, L^{⊗ (k+1)}|_D) → 0`
with isometric sublattice embedding and bounded metric distortion `δ ≥ 0` on the quotient. -/
structure HSMBlockExactSeq (B_sub B B_quot : HSMBlock) where
  ι : B_sub.L →ₗ[ℤ] B.L
  ι_inj : Function.Injective ι
  ι_norm : ∀ x : B_sub.L, ‖((ι x : B.L) : B.E)‖ = ‖(x : B_sub.E)‖
  ι_sat : IsSaturated B.L (LinearMap.range (B.L.subtype.comp ι))
  ψ : quotLat B.L (LinearMap.range (B.L.subtype.comp ι)) ≃ₗ[ℤ] B_quot.L
  distort : ℝ
  distort_nonneg : 0 ≤ distort
  quot_chi_distort :
    |chiAr (quotLat B.L (LinearMap.range (B.L.subtype.comp ι))) - B_quot.blockChi| ≤ distort

/-- **Exact-Sequence Block-Step Euler Characteristic Recursion (`hsmBlock_exact_seq_chi_recursion`)**:
for any `S : HSMBlockExactSeq B_sub B B_quot`:
1. Exact rank additivity `B.blockRk = B_sub.blockRk + B_quot.blockRk`,
2. Exact Euler characteristic step bound `|B.blockChi - (B_sub.blockChi + B_quot.blockChi)| ≤ S.distort`. -/
theorem hsmBlock_exact_seq_chi_recursion {B_sub B B_quot : HSMBlock}
    (S : HSMBlockExactSeq B_sub B B_quot) :
    B.blockRk = B_sub.blockRk + B_quot.blockRk ∧
    |B.blockChi - (B_sub.blockChi + B_quot.blockChi)| ≤ S.distort := by
  let M : Submodule ℤ B.E := LinearMap.range (B.L.subtype.comp S.ι)
  have : DiscreteTopology M := discreteTopology_of_le S.ι_sat.1
  have : DiscreteTopology (quotLat B.L M) := discreteTopology_quotLat S.ι_sat
  let e₁ : B_sub.L ≃ₗ[ℤ] M :=
    LinearEquiv.ofInjective (B.L.subtype.comp S.ι) (B.L.injective_subtype.comp S.ι_inj)
  have h1 := arithDeg_eq_of_isometric_equiv e₁ S.ι_norm
  have hrkQ : rk (quotLat B.L M) = rk B_quot.L := S.ψ.finrank_eq
  obtain ⟨hrk_add, hchi_add⟩ := chiAr_exact_seq S.ι_sat
  change rk B.L = rk M + rk (quotLat B.L M) at hrk_add
  change chiAr B.L = chiAr M + chiAr (quotLat B.L M) at hchi_add
  refine ⟨by change rk B.L = rk B_sub.L + rk B_quot.L; rw [hrk_add, h1.1, hrkQ], ?_⟩
  have hdiff : B.blockChi - (B_sub.blockChi + B_quot.blockChi) =
      chiAr (quotLat B.L M) - B_quot.blockChi := by
    change chiAr B.L - (arithDeg B_sub.L + B_quot.blockChi) = _
    rw [hchi_add, chiAr_eq_arithDeg, h1.2.2.1]; ring
  rw [hdiff]
  exact S.quot_chi_distort

end HSMBlocks

/-! ## Section 3: Discrete Faulhaber Integration & Graded `HSChainSystem` -/

section FaulhaberAndChainSystems

/-- **Exact Discrete Faulhaber Summation Bounds (`sum_pow_range_bounds`)**:
for every `d ≥ 1` and every `k : ℕ`:
1. `(d + 1) * ∑_{j=0}^{k-1} j^d ≤ k^(d + 1)`,
2. `k^(d + 1) - (d + 1) * ∑_{j=0}^{k-1} j^d ≤ 2^(d + 1) * k^d`. -/
theorem sum_pow_range_bounds {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    ((d + 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range k, (j : ℝ) ^ d) ≤ (k : ℝ) ^ (d + 1) ∧
    (k : ℝ) ^ (d + 1) - ((d + 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range k, (j : ℝ) ^ d) ≤
      (2 : ℝ) ^ (d + 1) * (k : ℝ) ^ d := by
  have hstep : ∀ j : ℕ, ((j : ℝ) + 1) ^ (d + 1) - (j : ℝ) ^ (d + 1) =
      ((d + 1 : ℕ) : ℝ) * (j : ℝ) ^ d +
        ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i := by
    intro j
    rw [add_pow (j : ℝ) (1 : ℝ) (d + 1)]
    simp only [one_pow, mul_one]
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one,
      Finset.sum_range_succ, Nat.choose_succ_self_right]
    ring
  have htel : (k : ℝ) ^ (d + 1) =
      ((d + 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range k, (j : ℝ) ^ d) +
        ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i := by
    have h1 : ∑ j ∈ Finset.range k, (((j : ℝ) + 1) ^ (d + 1) - (j : ℝ) ^ (d + 1)) =
        (k : ℝ) ^ (d + 1) := by
      have := Finset.sum_range_sub (fun j : ℕ => (j : ℝ) ^ (d + 1)) k
      simpa [Nat.cast_add, Nat.cast_one, zero_pow (Nat.succ_ne_zero d)] using this
    rw [← h1]
    simp_rw [hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrem_nn : 0 ≤ ∑ j ∈ Finset.range k,
      ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨by linarith, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [zero_pow (by omega : d ≠ 0), zero_pow (Nat.succ_ne_zero d)]
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
  have hchoose_sum : ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by
    have hsub : Finset.range d ⊆ Finset.range (d + 2) := Finset.range_mono (by omega)
    calc ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ)
        ≤ ∑ i ∈ Finset.range (d + 2), (Nat.choose (d + 1) i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
      _ = (2 : ℝ) ^ (d + 1) := by exact_mod_cast Nat.sum_range_choose (d + 1)
  have hrem_le : ∑ j ∈ Finset.range k,
      ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i ≤
      (2 : ℝ) ^ (d + 1) * (k : ℝ) ^ d := by
    have hterm : ∀ j ∈ Finset.range k,
        ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i ≤
          (2 : ℝ) ^ (d + 1) * (k : ℝ) ^ (d - 1) := by
      intro j hj
      have hjk : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
      calc ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i
          ≤ ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (k : ℝ) ^ (d - 1) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hid : i ≤ d - 1 := by have := Finset.mem_range.mp hi; omega
            have hj_pow : (j : ℝ) ^ i ≤ (k : ℝ) ^ (d - 1) :=
              (pow_le_pow_left₀ (Nat.cast_nonneg j) hjk i).trans (pow_le_pow_right₀ hk_ge1 hid)
            exact mul_le_mul_of_nonneg_left hj_pow (Nat.cast_nonneg _)
        _ = (∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ)) * (k : ℝ) ^ (d - 1) := by
            rw [← Finset.sum_mul]
        _ ≤ (2 : ℝ) ^ (d + 1) * (k : ℝ) ^ (d - 1) :=
            mul_le_mul_of_nonneg_right hchoose_sum (pow_nonneg (Nat.cast_nonneg k) _)
    calc ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range d, (Nat.choose (d + 1) i : ℝ) * (j : ℝ) ^ i
        ≤ ∑ _j ∈ Finset.range k, ((2 : ℝ) ^ (d + 1) * (k : ℝ) ^ (d - 1)) :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * ((2 : ℝ) ^ (d + 1) * (k : ℝ) ^ (d - 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (2 : ℝ) ^ (d + 1) * (k : ℝ) ^ d := by
          have hkpow : (k : ℝ) * (k : ℝ) ^ (d - 1) = (k : ℝ) ^ d := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hd]
          calc (k : ℝ) * ((2 : ℝ) ^ (d + 1) * (k : ℝ) ^ (d - 1))
              = (2 : ℝ) ^ (d + 1) * ((k : ℝ) * (k : ℝ) ^ (d - 1)) := by ring
            _ = (2 : ℝ) ^ (d + 1) * (k : ℝ) ^ d := by rw [hkpow]
  linarith

/-- **Factorial-Normalized Faulhaber Approximation (`sum_pow_div_factorial_approx`)**:
for every `d ≥ 1` and `k : ℕ`:
`|(∑ j ∈ range k, j^d) / d! - k^(d+1) / (d+1)!| ≤ (2^(d+1) / (d+1)!) * k^d`. -/
theorem sum_pow_div_factorial_approx {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    |(∑ j ∈ Finset.range k, (j : ℝ) ^ d) / (d.factorial : ℝ) -
        (k : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)| ≤
      ((2 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (k : ℝ) ^ d := by
  obtain ⟨hle, hgap⟩ := sum_pow_range_bounds hd k
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hfac_d : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  have hrewrite : (∑ j ∈ Finset.range k, (j : ℝ) ^ d) / (d.factorial : ℝ) -
      (k : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      (((d + 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range k, (j : ℝ) ^ d) - (k : ℝ) ^ (d + 1)) /
        ((d + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp [hfac_d.ne', hd1_pos.ne']
  rw [hrewrite, abs_div, abs_of_pos hfac_pos, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hfac_pos, abs_le]
  constructor <;> linarith

/-- **Concrete Graded Arithmetic Hilbert–Samuel Chain System (`HSChainSystem d`)**:
models a `d`-dimensional (`d ≥ 1`) projective arithmetic variety with Hermitian line bundle `L̄`,
carrying:
- concrete Hilbert–Samuel blocks `block k : HSMBlock` at every tensor power `k : ℕ`,
- generic-fiber geometric degree `geomDeg ≥ 0` and top arithmetic self-intersection `selfInt = (L^{d+1})_Ar`,
- polynomial rank ceiling `rk (block k) ≤ rankHi * k^d`,
- uniform `L²`-vs-sup volume bound `volConst ≤ volHi` and polynomial Bergman & Babai ceilings
  `bergConst ≤ bergHi * (k + 1)^bergExp`, `gsCeil ≤ gsHi * (k + 1)^gsExp`,
- **Non-circular block-step Euler characteristic recursion**:
  `|(block (k + 1)).blockChi - (block k).blockChi - (selfInt / d!) * k^d| ≤ stepErr * (k + 1)^(d - 1) * (log(k + 2) + 1)`. -/
structure HSChainSystem (d : ℕ) where
  hd : 1 ≤ d
  block : ℕ → HSMBlock
  geomDeg : ℝ
  geomDeg_nonneg : 0 ≤ geomDeg
  selfInt : ℝ
  rankHi : ℝ
  rankHi_ge_one : 1 ≤ rankHi
  rk_le_poly : ∀ k : ℕ, 1 ≤ k → ((block k).blockRk : ℝ) ≤ rankHi * (k : ℝ) ^ d
  volHi : ℝ
  volHi_pos : 0 < volHi
  volConst_le : ∀ k : ℕ, 1 ≤ k → (block k).volConst ≤ volHi
  bergHi : ℝ
  bergExp : ℕ
  bergHi_ge_one : 1 ≤ bergHi
  bergConst_le : ∀ k : ℕ, 1 ≤ k → (block k).bergConst ≤ bergHi * ((k : ℝ) + 1) ^ bergExp
  gsHi : ℝ
  gsExp : ℕ
  gsHi_nonneg : 0 ≤ gsHi
  gsCeil_le : ∀ k : ℕ, 1 ≤ k → (block k).gsCeil ≤ gsHi * ((k : ℝ) + 1) ^ gsExp
  stepErr : ℝ
  stepErr_nonneg : 0 ≤ stepErr
  blockChi_step : ∀ k : ℕ,
    |(block (k + 1)).blockChi - (block k).blockChi -
        (selfInt / (d.factorial : ℝ)) * (k : ℝ) ^ d| ≤
      stepErr * ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1)

namespace HSChainSystem

/-- Optional exact Hilbert–Samuel rank asymptotic condition (`rk (block k) = geomDeg * k^d / d! + O(k^(d-1))`)
used for normalized height / slope limits and metric-shift fiber formulas. -/
structure HasExactRank {d : ℕ} (S : HSChainSystem d) where
  rankErr : ℝ
  rankErr_nonneg : 0 ≤ rankErr
  rk_asymp : ∀ k : ℕ, 1 ≤ k →
    |((S.block k).blockRk : ℝ) - S.geomDeg * ((k : ℝ) ^ d / (d.factorial : ℝ))| ≤
      rankErr * (k : ℝ) ^ (d - 1)

/-- Explicit arithmetic Hilbert–Samuel normalization `V_d(k) = k^(d + 1) / (d + 1)!`. -/
def hsNorm (d k : ℕ) : ℝ :=
  (k : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)

theorem hsNorm_pos (d : ℕ) {k : ℕ} (hk : 1 ≤ k) : 0 < hsNorm d k :=
  div_pos (pow_pos (Nat.cast_pos.mpr hk) (d + 1)) (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- Metric-twisted block at degree `k` for any real archimedean fiber shift `c : ℝ`:
rescales `S.block k` by `exp(-c * k)`. -/
def twistMetricBlock {d : ℕ} (S : HSChainSystem d) (c : ℝ) (k : ℕ) : HSMBlock :=
  (S.block k).scaleMetric (Real.exp_pos (-c * (k : ℝ)))

theorem twistMetricBlock_invariants {d : ℕ} (S : HSChainSystem d) (c : ℝ) (k : ℕ) :
    (S.twistMetricBlock c k).blockRk = (S.block k).blockRk ∧
    (S.twistMetricBlock c k).blockChi =
      (S.block k).blockChi + c * (k : ℝ) * ((S.block k).blockRk : ℝ) ∧
    (S.twistMetricBlock c k).blockSlope = (S.block k).blockSlope + c * (k : ℝ) := by
  unfold twistMetricBlock
  obtain ⟨hrk, hchi, hsl⟩ := (S.block k).scaleMetric_invariants (Real.exp_pos (-c * (k : ℝ)))
  rw [Real.log_exp] at hchi hsl
  exact ⟨hrk, by linarith, by linarith⟩

/-- **Veronese / Tensor-Power Chain System (`S.powerChain m hm`)**:
for any `m ≥ 1`, constructs the `m`-th tensor-power chain `k ↦ S.block (m * k)` with
top arithmetic self-intersection `(m : ℝ)^(d + 1) * S.selfInt`, proving the non-circular
block-step recursion by summing `m` consecutive steps of `S.blockChi_step`! -/
def powerChain {d : ℕ} (S : HSChainSystem d) (m : ℕ) (hm : 1 ≤ m) : HSChainSystem d where
  hd := S.hd
  block k := S.block (m * k)
  geomDeg := (m : ℝ) ^ d * S.geomDeg
  geomDeg_nonneg := mul_nonneg (pow_nonneg (Nat.cast_nonneg m) d) S.geomDeg_nonneg
  selfInt := (m : ℝ) ^ (d + 1) * S.selfInt
  rankHi := S.rankHi * (m : ℝ) ^ d
  rankHi_ge_one := one_le_mul_of_one_le_of_one_le S.rankHi_ge_one (one_le_pow₀ (by exact_mod_cast hm))
  rk_le_poly k hk := by
    have hmk : 1 ≤ m * k := Nat.mul_le_mul hm hk
    have h1 := S.rk_le_poly (m * k) hmk
    push_cast [Nat.cast_mul, mul_pow] at h1 ⊢
    linarith
  volHi := S.volHi
  volHi_pos := S.volHi_pos
  volConst_le k hk := S.volConst_le (m * k) (Nat.mul_le_mul hm hk)
  bergHi := S.bergHi * (m : ℝ) ^ S.bergExp
  bergExp := S.bergExp
  bergHi_ge_one := one_le_mul_of_one_le_of_one_le S.bergHi_ge_one
    (one_le_pow₀ (by exact_mod_cast hm))
  bergConst_le k hk := by
    have hmk : 1 ≤ m * k := Nat.mul_le_mul hm hk
    have h1 := S.bergConst_le (m * k) hmk
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hle : ((m * k : ℕ) : ℝ) + 1 ≤ (m : ℝ) * ((k : ℝ) + 1) := by
      push_cast; nlinarith
    have hpow := pow_le_pow_left₀ (by positivity) hle S.bergExp
    rw [mul_pow] at hpow
    calc (S.block (m * k)).bergConst
        ≤ S.bergHi * (((m * k : ℕ) : ℝ) + 1) ^ S.bergExp := h1
      _ ≤ S.bergHi * ((m : ℝ) ^ S.bergExp * ((k : ℝ) + 1) ^ S.bergExp) :=
          mul_le_mul_of_nonneg_left hpow (by linarith [S.bergHi_ge_one])
      _ = S.bergHi * (m : ℝ) ^ S.bergExp * ((k : ℝ) + 1) ^ S.bergExp := by ring
  gsHi := S.gsHi * (m : ℝ) ^ S.gsExp
  gsExp := S.gsExp
  gsHi_nonneg := mul_nonneg S.gsHi_nonneg (pow_nonneg (Nat.cast_nonneg m) _)
  gsCeil_le k hk := by
    have hmk : 1 ≤ m * k := Nat.mul_le_mul hm hk
    have h1 := S.gsCeil_le (m * k) hmk
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hle : ((m * k : ℕ) : ℝ) + 1 ≤ (m : ℝ) * ((k : ℝ) + 1) := by
      push_cast; nlinarith
    have hpow := pow_le_pow_left₀ (by positivity) hle S.gsExp
    rw [mul_pow] at hpow
    calc (S.block (m * k)).gsCeil
        ≤ S.gsHi * (((m * k : ℕ) : ℝ) + 1) ^ S.gsExp := h1
      _ ≤ S.gsHi * ((m : ℝ) ^ S.gsExp * ((k : ℝ) + 1) ^ S.gsExp) :=
          mul_le_mul_of_nonneg_left hpow S.gsHi_nonneg
      _ = S.gsHi * (m : ℝ) ^ S.gsExp * ((k : ℝ) + 1) ^ S.gsExp := by ring
  stepErr := (m : ℝ) ^ d * S.stepErr * (Real.log (m : ℝ) + 1) +
    (|S.selfInt| / (d.factorial : ℝ)) * (2 * (m : ℝ)) ^ (d + 1)
  stepErr_nonneg := by
    have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have h1 : 0 ≤ (m : ℝ) ^ d * S.stepErr * (Real.log (m : ℝ) + 1) :=
      mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg m) d) S.stepErr_nonneg) (by linarith)
    exact add_nonneg h1 (by positivity)
  blockChi_step k := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    -- Telescope `blockChi (m * (k + 1)) - blockChi (m * k)` as `∑ t ∈ range m, step (m * k + t)`.
    have htel : (S.block (m * (k + 1))).blockChi - (S.block (m * k)).blockChi =
        ∑ t ∈ Finset.range m, ((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) := by
      have h := Finset.sum_range_sub (fun t : ℕ => (S.block (m * k + t)).blockChi) m
      simpa [mul_add, mul_one, add_assoc] using h.symm
    have hmain_eq : (((m : ℝ) ^ (d + 1) * S.selfInt) / (d.factorial : ℝ)) * (k : ℝ) ^ d =
        ∑ _t ∈ Finset.range m, (S.selfInt / (d.factorial : ℝ)) * ((m : ℝ) * (k : ℝ)) ^ d := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow, pow_succ]
      ring
    rw [htel, hmain_eq, ← Finset.sum_sub_distrib]
    have hterm : ∀ t ∈ Finset.range m,
        |((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) -
            (S.selfInt / (d.factorial : ℝ)) * ((m : ℝ) * (k : ℝ)) ^ d| ≤
          ((m : ℝ) ^ (d - 1) * S.stepErr * (Real.log (m : ℝ) + 1) +
            (|S.selfInt| / (d.factorial : ℝ)) * (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d) *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1) := by
      intro t ht
      have htm : t < m := Finset.mem_range.mp ht
      have hsplit :
          ((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) -
              (S.selfInt / (d.factorial : ℝ)) * ((m : ℝ) * (k : ℝ)) ^ d =
          (((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) -
              (S.selfInt / (d.factorial : ℝ)) * ((m * k + t : ℕ) : ℝ) ^ d) +
          (S.selfInt / (d.factorial : ℝ)) *
              (((m * k + t : ℕ) : ℝ) ^ d - ((m : ℝ) * (k : ℝ)) ^ d) := by ring
      rw [hsplit]
      have htri := abs_add_le
        (((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) -
            (S.selfInt / (d.factorial : ℝ)) * ((m * k + t : ℕ) : ℝ) ^ d)
        ((S.selfInt / (d.factorial : ℝ)) *
            (((m * k + t : ℕ) : ℝ) ^ d - ((m : ℝ) * (k : ℝ)) ^ d))
      -- Bound part 1 using `S.blockChi_step (m * k + t)`.
      have h1 := S.blockChi_step (m * k + t)
      have hmkt_le : ((m * k + t : ℕ) : ℝ) + 1 ≤ (m : ℝ) * ((k : ℝ) + 1) := by
        have : m * k + t + 1 ≤ m * (k + 1) := by nlinarith
        exact_mod_cast this
      have hpow1 : (((m * k + t : ℕ) : ℝ) + 1) ^ (d - 1) ≤
          (m : ℝ) ^ (d - 1) * ((k : ℝ) + 1) ^ (d - 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hmkt_le (d - 1)
      have hlog1 : Real.log (((m * k + t : ℕ) : ℝ) + 2) + 1 ≤
          (Real.log (m : ℝ) + 1) * (Real.log ((k : ℝ) + 2) + 1) := by
        have harg : ((m * k + t : ℕ) : ℝ) + 2 ≤ (m : ℝ) * ((k : ℝ) + 2) := by
          have : m * k + t + 2 ≤ m * (k + 2) := by nlinarith
          exact_mod_cast this
        have hle := Real.log_le_log (by positivity) harg
        rw [Real.log_mul (by positivity) (by positivity)] at hle
        have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
        have hlogk_nn : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
        nlinarith
      have hpart1 : S.stepErr * (((m * k + t : ℕ) : ℝ) + 1) ^ (d - 1) *
          (Real.log (((m * k + t : ℕ) : ℝ) + 2) + 1) ≤
          (m : ℝ) ^ (d - 1) * S.stepErr * (Real.log (m : ℝ) + 1) *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1) := by
        have hlog_nn : 0 ≤ Real.log (((m * k + t : ℕ) : ℝ) + 2) + 1 := by
          linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((m * k + t : ℕ) : ℝ) + 2 by
            linarith [Nat.cast_nonneg (α := ℝ) (m * k + t)])]
        have hmul := mul_le_mul hpow1 hlog1 hlog_nn (by positivity)
        have hmul2 := mul_le_mul_of_nonneg_left hmul S.stepErr_nonneg
        linarith
      -- Bound part 2: `|(m*k + t)^d - (m*k)^d| ≤ 2^d * m^d * (k + 1)^(d - 1)`.
      have hdiff_pow : |((m * k + t : ℕ) : ℝ) ^ d - ((m : ℝ) * (k : ℝ)) ^ d| ≤
          (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by
        have hnn : 0 ≤ ((m * k + t : ℕ) : ℝ) ^ d - ((m : ℝ) * (k : ℝ)) ^ d := by
          have hge : (m : ℝ) * (k : ℝ) ≤ ((m * k + t : ℕ) : ℝ) := by push_cast; linarith
          exact sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) hge d)
        rw [abs_of_nonneg hnn]
        have hexp : ((m * k + t : ℕ) : ℝ) ^ d - ((m : ℝ) * (k : ℝ)) ^ d =
            ∑ i ∈ Finset.range d, (Nat.choose d i : ℝ) * ((m : ℝ) * (k : ℝ)) ^ i * (t : ℝ) ^ (d - i) := by
          have hcast : ((m * k + t : ℕ) : ℝ) = (m : ℝ) * (k : ℝ) + (t : ℝ) := by push_cast; ring
          rw [hcast, add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero]
          ring
        rw [hexp]
        have hch : ∑ i ∈ Finset.range d, (Nat.choose d i : ℝ) ≤ (2 : ℝ) ^ d := by
          calc ∑ i ∈ Finset.range d, (Nat.choose d i : ℝ)
              ≤ ∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ d))
                  fun _ _ _ => Nat.cast_nonneg _
            _ = (2 : ℝ) ^ d := by exact_mod_cast Nat.sum_range_choose d
        have hsum_le : ∑ i ∈ Finset.range d,
            (Nat.choose d i : ℝ) * ((m : ℝ) * (k : ℝ)) ^ i * (t : ℝ) ^ (d - i) ≤
            (2 : ℝ) ^ d * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by
          calc ∑ i ∈ Finset.range d,
                (Nat.choose d i : ℝ) * ((m : ℝ) * (k : ℝ)) ^ i * (t : ℝ) ^ (d - i)
              ≤ ∑ i ∈ Finset.range d,
                  (Nat.choose d i : ℝ) * ((m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1)) := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hid : i ≤ d - 1 := by have := Finset.mem_range.mp hi; omega
                have hk_pow : (k : ℝ) ^ i ≤ ((k : ℝ) + 1) ^ (d - 1) :=
                  (pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) i).trans
                    (pow_le_pow_right₀ (by linarith) hid)
                have ht_le : (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast htm.le
                have ht_pow : (t : ℝ) ^ (d - i) ≤ (m : ℝ) ^ (d - i) :=
                  pow_le_pow_left₀ (Nat.cast_nonneg t) ht_le (d - i)
                have hm_pow : (m : ℝ) ^ i * (m : ℝ) ^ (d - i) = (m : ℝ) ^ d := by
                  rw [← pow_add, Nat.add_sub_of_le (le_of_lt (Finset.mem_range.mp hi))]
                have hprod : ((m : ℝ) * (k : ℝ)) ^ i * (t : ℝ) ^ (d - i) ≤
                    (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by
                  rw [mul_pow]
                  calc (m : ℝ) ^ i * (k : ℝ) ^ i * (t : ℝ) ^ (d - i)
                      ≤ (m : ℝ) ^ i * ((k : ℝ) + 1) ^ (d - 1) * (m : ℝ) ^ (d - i) := by
                        have h1 := mul_le_mul_of_nonneg_left hk_pow (pow_nonneg (Nat.cast_nonneg m) i)
                        exact mul_le_mul h1 ht_pow (pow_nonneg (Nat.cast_nonneg t) _) (by positivity)
                    _ = ((m : ℝ) ^ i * (m : ℝ) ^ (d - i)) * ((k : ℝ) + 1) ^ (d - 1) := by ring
                    _ = (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by rw [hm_pow]
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
            _ = (∑ i ∈ Finset.range d, (Nat.choose d i : ℝ)) *
                  ((m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1)) := by rw [← Finset.sum_mul]
            _ ≤ (2 : ℝ) ^ d * ((m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1)) :=
                mul_le_mul_of_nonneg_right hch (by positivity)
            _ = (2 : ℝ) ^ d * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by ring
        have h2le : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ d)
        calc ∑ i ∈ Finset.range d,
              (Nat.choose d i : ℝ) * ((m : ℝ) * (k : ℝ)) ^ i * (t : ℝ) ^ (d - i)
            ≤ (2 : ℝ) ^ d * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := hsum_le
          _ ≤ (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by
              have hfac_nn : 0 ≤ (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1) :=
                mul_nonneg (pow_nonneg (Nat.cast_nonneg m) d) (pow_nonneg (by positivity) (d - 1))
              have hle2 := mul_le_mul_of_nonneg_right h2le hfac_nn
              linarith
      have hlogk_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) + 1 := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)]
      have hpart2 : |(S.selfInt / (d.factorial : ℝ)) *
            (((m * k + t : ℕ) : ℝ) ^ d - ((m : ℝ) * (k : ℝ)) ^ d)| ≤
          (|S.selfInt| / (d.factorial : ℝ)) * (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1) := by
        rw [abs_mul, abs_div,
          abs_of_pos (show (0 : ℝ) < (d.factorial : ℝ) from Nat.cast_pos.mpr (Nat.factorial_pos d))]
        have h2a := mul_le_mul_of_nonneg_left hdiff_pow
          (div_nonneg (abs_nonneg S.selfInt) (Nat.cast_nonneg d.factorial))
        have h2b : (|S.selfInt| / (d.factorial : ℝ)) *
              ((2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1)) ≤
            (|S.selfInt| / (d.factorial : ℝ)) *
              ((2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 1)) *
              (Real.log ((k : ℝ) + 2) + 1) := by
          calc _ = _ * 1 := (mul_one _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_left hlogk_ge1 (by positivity)
        linarith
      linarith [h1.trans hpart1]
    calc |∑ t ∈ Finset.range m, (((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) -
            (S.selfInt / (d.factorial : ℝ)) * ((m : ℝ) * (k : ℝ)) ^ d)|
        ≤ ∑ t ∈ Finset.range m, |((S.block (m * k + t + 1)).blockChi - (S.block (m * k + t)).blockChi) -
            (S.selfInt / (d.factorial : ℝ)) * ((m : ℝ) * (k : ℝ)) ^ d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range m, (((m : ℝ) ^ (d - 1) * S.stepErr * (Real.log (m : ℝ) + 1) +
            (|S.selfInt| / (d.factorial : ℝ)) * (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d) *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1)) :=
          Finset.sum_le_sum hterm
      _ = (m : ℝ) * (((m : ℝ) ^ (d - 1) * S.stepErr * (Real.log (m : ℝ) + 1) +
            (|S.selfInt| / (d.factorial : ℝ)) * (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d) *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((m : ℝ) ^ d * S.stepErr * (Real.log (m : ℝ) + 1) +
            (|S.selfInt| / (d.factorial : ℝ)) * (2 * (m : ℝ)) ^ (d + 1)) *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1) := by
          have hm_pow : (m : ℝ) * (m : ℝ) ^ (d - 1) = (m : ℝ) ^ d := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel S.hd]
          have hm_pow2 : (m : ℝ) * (m : ℝ) ^ d = (m : ℝ) ^ (d + 1) := by
            rw [mul_comm, ← pow_succ]
          rw [mul_pow]
          calc (m : ℝ) * (((m : ℝ) ^ (d - 1) * S.stepErr * (Real.log (m : ℝ) + 1) +
                  (|S.selfInt| / (d.factorial : ℝ)) * (2 : ℝ) ^ (d + 1) * (m : ℝ) ^ d) *
                  ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1))
              = (((m : ℝ) * (m : ℝ) ^ (d - 1)) * S.stepErr * (Real.log (m : ℝ) + 1) +
                  (|S.selfInt| / (d.factorial : ℝ)) * (2 : ℝ) ^ (d + 1) * ((m : ℝ) * (m : ℝ) ^ d)) *
                  ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1) := by ring
            _ = _ := by rw [hm_pow, hm_pow2]; ring

end HSChainSystem

end FaulhaberAndChainSystems

/-! ## Section 4: Genuine Proved Asymptotic Arithmetic Hilbert–Samuel Theorem (`hs_chain_asymptotic`) -/

section ArithHilbertSamuelAsymptotic

/-- Helper: `(C * (log (k + 2) + 1)) / k → 0` as `k → ∞`. -/
private lemma tendsto_log_add_two_div_nat (C : ℝ) :
    Tendsto (fun k : ℕ => C * (Real.log ((k : ℝ) + 2) + 1) / (k : ℝ)) atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero
    simpa [pow_one, one_mul, add_zero] using h
  have hlog_k2 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    hlog_div.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv_nat : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun k : ℕ => ((k : ℝ) + 2) / (k : ℝ)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) * ((k : ℝ))⁻¹) atTop (𝓝 (2 * 0)) :=
      hinv_nat.const_mul 2
    rw [mul_zero] at h2
    have hadd := (tendsto_const_nhds (x := (1 : ℝ))).add h2
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hk0]
  have hlog_k : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2) / (k : ℝ)) atTop (𝓝 0) := by
    have hprod := hlog_k2.mul hratio
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hk2]
  have hsum : Tendsto (fun k : ℕ => C * (Real.log ((k : ℝ) + 2) / (k : ℝ) + ((k : ℝ))⁻¹))
      atTop (𝓝 (C * (0 + 0))) := (hlog_k.add hinv_nat).const_mul C
  simp only [add_zero, mul_zero] at hsum
  exact hsum.congr fun k => by ring

/-- **Telescoping Faulhaber Euler Characteristic Asymptotic (`hs_chain_chi_asymptotic`)**:
For EVERY `S : HSChainSystem d`, non-circularly derives from `S.blockChi_step` and Faulhaber
discrete integration:
1. Explicit `O(k^d log k)` error bound:
   `|(S.block k).blockChi - (k^(d+1) / (d+1)!) * S.selfInt| ≤ C_chi * k^d * (log(k + 2) + 1)`
   for all `k ≥ 1`, with explicit constant `C_chi = |(S.block 0).blockChi| + |S.selfInt| * (2^(d+1) / (d+1)!) + S.stepErr`,
2. Exact convergence:
   `Tendsto (fun k => (S.block k).blockChi / hsNorm d k) atTop (𝓝 S.selfInt)`. -/
theorem hs_chain_chi_asymptotic {d : ℕ} (S : HSChainSystem d) :
    let C_chi : ℝ := |(S.block 0).blockChi| +
      |S.selfInt| * ((2 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) + S.stepErr
    0 ≤ C_chi ∧
    (∀ k : ℕ, 1 ≤ k →
      |(S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt| ≤
        C_chi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) ∧
    Tendsto (fun k : ℕ => (S.block k).blockChi / HSChainSystem.hsNorm d k) atTop (𝓝 S.selfInt) := by
  intro C_chi
  have hC_nn : 0 ≤ C_chi := by
    dsimp only [C_chi]; positivity [S.stepErr_nonneg]
  have hbound : ∀ k : ℕ, 1 ≤ k →
      |(S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt| ≤
        C_chi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
    intro k hk
    have htel : (S.block k).blockChi - (S.block 0).blockChi =
        ∑ j ∈ Finset.range k, ((S.block (j + 1)).blockChi - (S.block j).blockChi) := by
      simpa using (Finset.sum_range_sub (fun j : ℕ => (S.block j).blockChi) k).symm
    have hsplit : (S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt =
        (S.block 0).blockChi +
        ((∑ j ∈ Finset.range k, ((S.block (j + 1)).blockChi - (S.block j).blockChi -
            (S.selfInt / (d.factorial : ℝ)) * (j : ℝ) ^ d)) +
        S.selfInt * ((∑ j ∈ Finset.range k, (j : ℝ) ^ d) / (d.factorial : ℝ) -
            HSChainSystem.hsNorm d k)) := by
      rw [Finset.sum_sub_distrib, ← htel, ← Finset.mul_sum]
      ring
    rw [hsplit]
    have htri1 := abs_add_le (S.block 0).blockChi
      ((∑ j ∈ Finset.range k, ((S.block (j + 1)).blockChi - (S.block j).blockChi -
          (S.selfInt / (d.factorial : ℝ)) * (j : ℝ) ^ d)) +
      S.selfInt * ((∑ j ∈ Finset.range k, (j : ℝ) ^ d) / (d.factorial : ℝ) -
          HSChainSystem.hsNorm d k))
    have htri2 := abs_add_le
      (∑ j ∈ Finset.range k, ((S.block (j + 1)).blockChi - (S.block j).blockChi -
          (S.selfInt / (d.factorial : ℝ)) * (j : ℝ) ^ d))
      (S.selfInt * ((∑ j ∈ Finset.range k, (j : ℝ) ^ d) / (d.factorial : ℝ) -
          HSChainSystem.hsNorm d k))
    -- Bound the sum of block-step errors by `S.stepErr * k^d * (log (k + 2) + 1)`.
    have hsum_step : |∑ j ∈ Finset.range k, ((S.block (j + 1)).blockChi - (S.block j).blockChi -
          (S.selfInt / (d.factorial : ℝ)) * (j : ℝ) ^ d)| ≤
        S.stepErr * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
      calc |∑ j ∈ Finset.range k, _|
          ≤ ∑ j ∈ Finset.range k, |(S.block (j + 1)).blockChi - (S.block j).blockChi -
              (S.selfInt / (d.factorial : ℝ)) * (j : ℝ) ^ d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range k, S.stepErr * ((j : ℝ) + 1) ^ (d - 1) *
              (Real.log ((j : ℝ) + 2) + 1) := Finset.sum_le_sum fun j _ => S.blockChi_step j
        _ ≤ ∑ _j ∈ Finset.range k, S.stepErr * (k : ℝ) ^ (d - 1) *
              (Real.log ((k : ℝ) + 2) + 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjk : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj)
            have hpow := pow_le_pow_left₀ (by positivity) hjk (d - 1)
            have hlog := Real.log_le_log (by positivity) (show (j : ℝ) + 2 ≤ (k : ℝ) + 2 by linarith)
            have hmul := mul_le_mul hpow (by linarith : Real.log ((j : ℝ) + 2) + 1 ≤ Real.log ((k : ℝ) + 2) + 1)
              (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (j : ℝ) + 2 by linarith)]) (by positivity)
            have hmul2 := mul_le_mul_of_nonneg_left hmul S.stepErr_nonneg
            linarith
        _ = (k : ℝ) * (S.stepErr * (k : ℝ) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = S.stepErr * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
            have hkpow : (k : ℝ) * (k : ℝ) ^ (d - 1) = (k : ℝ) ^ d := by
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel S.hd]
            calc (k : ℝ) * (S.stepErr * (k : ℝ) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1))
                = S.stepErr * ((k : ℝ) * (k : ℝ) ^ (d - 1)) * (Real.log ((k : ℝ) + 2) + 1) := by ring
              _ = _ := by rw [hkpow]
    -- Bound the Faulhaber remainder using `sum_pow_div_factorial_approx`.
    have hfaul : |S.selfInt * ((∑ j ∈ Finset.range k, (j : ℝ) ^ d) / (d.factorial : ℝ) -
          HSChainSystem.hsNorm d k)| ≤
        |S.selfInt| * ((2 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (k : ℝ) ^ d := by
      rw [abs_mul]
      unfold HSChainSystem.hsNorm
      have hf := sum_pow_div_factorial_approx S.hd k
      have hmul := mul_le_mul_of_nonneg_left hf (abs_nonneg S.selfInt)
      linarith
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hk)
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) + 1 := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)]
    have h0_le : |(S.block 0).blockChi| ≤
        |(S.block 0).blockChi| * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) :=
        one_le_mul_of_one_le_of_one_le hk_ge1 hlog_ge1
      calc |(S.block 0).blockChi| = |(S.block 0).blockChi| * 1 := (mul_one _).symm
        _ ≤ |(S.block 0).blockChi| * ((k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = _ := by ring
    have hfaul_log : |S.selfInt| * ((2 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (k : ℝ) ^ d ≤
        |S.selfInt| * ((2 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (k : ℝ) ^ d *
          (Real.log ((k : ℝ) + 2) + 1) := by
      calc _ = _ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
    dsimp only [C_chi]
    linarith
  refine ⟨hC_nn, hbound, ?_⟩
  -- Deduce exact convergence via squeeze_zero_norm'.
  have hzero : Tendsto (fun k : ℕ => (S.block k).blockChi / HSChainSystem.hsNorm d k - S.selfInt)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (tendsto_log_add_two_div_nat (C_chi * ((d + 1).factorial : ℝ)))
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hVpos : 0 < HSChainSystem.hsNorm d k := HSChainSystem.hsNorm_pos d hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hdiff : (S.block k).blockChi / HSChainSystem.hsNorm d k - S.selfInt =
        ((S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt) /
          HSChainSystem.hsNorm d k := by
      field_simp [hVpos.ne']
    rw [hdiff, Real.norm_eq_abs, abs_div, abs_of_pos hVpos]
    calc |(S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt| / HSChainSystem.hsNorm d k
        ≤ (C_chi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) / HSChainSystem.hsNorm d k :=
          div_le_div_of_nonneg_right (hbound k hk) hVpos.le
      _ = C_chi * ((d + 1).factorial : ℝ) * (Real.log ((k : ℝ) + 2) + 1) / (k : ℝ) := by
          unfold HSChainSystem.hsNorm
          rw [pow_succ]
          have hkd : (k : ℝ) ^ d ≠ 0 := pow_ne_zero d hk_pos.ne'
          have hfac : ((d + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          field_simp [hk_pos.ne', hkd, hfac]
  simpa using hzero.add_const S.selfInt

/-- Helper: uniform Minkowski/Blichfeldt lower-bound error term on any block `S.block k` (`k ≥ 1`). -/
private lemma hs_chain_minkowski_loss_bound {d : ℕ} (S : HSChainSystem d) {k : ℕ} (hk : 1 ≤ k) :
    ((S.block k).blockRk : ℝ) *
        (Real.log (2 * (S.block k).bergConst) + (1 / 2) * Real.log ((S.block k).blockRk : ℝ) -
          (1 / 2) * Real.log Real.pi) ≤
      (S.rankHi * (Real.log (2 * S.bergHi) + (S.bergExp : ℝ) +
        (1 / 2) * Real.log S.rankHi + (d : ℝ) / 2 + |Real.log Real.pi| / 2)) *
        (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hrk_pos : (0 : ℝ) < ((S.block k).blockRk : ℝ) := Nat.cast_pos.mpr (S.block k).blockRk_pos
  have hrk_le : ((S.block k).blockRk : ℝ) ≤ S.rankHi * (k : ℝ) ^ d := S.rk_le_poly k hk
  have hlog_k1_le : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog_k_le : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log hk_pos (by linarith)
  have hlog_k2_nn : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlog_2berg : Real.log (2 * (S.block k).bergConst) ≤
      Real.log (2 * S.bergHi) + (S.bergExp : ℝ) * Real.log ((k : ℝ) + 2) := by
    have h1 : 2 * (S.block k).bergConst ≤ (2 * S.bergHi) * ((k : ℝ) + 1) ^ S.bergExp := by
      linarith [S.bergConst_le k hk]
    have hBpos : 0 < 2 * (S.block k).bergConst := by linarith [(S.block k).bergConst_ge_one]
    have h2 := Real.log_le_log hBpos h1
    rw [Real.log_mul (by linarith [S.bergHi_ge_one]) (pow_pos (by positivity) _).ne',
      Real.log_pow] at h2
    have h3 : (S.bergExp : ℝ) * Real.log ((k : ℝ) + 1) ≤
        (S.bergExp : ℝ) * Real.log ((k : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlog_k1_le (Nat.cast_nonneg _)
    linarith
  have hlog_rk : Real.log ((S.block k).blockRk : ℝ) ≤
      Real.log S.rankHi + (d : ℝ) * Real.log ((k : ℝ) + 2) := by
    have h2 := Real.log_le_log hrk_pos hrk_le
    rw [Real.log_mul (by linarith [S.rankHi_ge_one]) (pow_pos hk_pos d).ne', Real.log_pow] at h2
    have h3 : (d : ℝ) * Real.log (k : ℝ) ≤ (d : ℝ) * Real.log ((k : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlog_k_le (Nat.cast_nonneg _)
    linarith
  have hpi_le : -(1 / 2) * Real.log Real.pi ≤ |Real.log Real.pi| / 2 := by
    have := neg_le_abs (Real.log Real.pi); linarith
  have hnn_b : 0 ≤ Real.log (2 * S.bergHi) := Real.log_nonneg (by linarith [S.bergHi_ge_one])
  have hnn_r : 0 ≤ Real.log S.rankHi := Real.log_nonneg S.rankHi_ge_one
  have hnn_e : 0 ≤ (S.bergExp : ℝ) := Nat.cast_nonneg _
  have hnn_d : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hnn_p : 0 ≤ |Real.log Real.pi| / 2 := by positivity
  have hper : Real.log (2 * (S.block k).bergConst) +
        (1 / 2) * Real.log ((S.block k).blockRk : ℝ) - (1 / 2) * Real.log Real.pi ≤
      (Real.log (2 * S.bergHi) + (S.bergExp : ℝ) + (1 / 2) * Real.log S.rankHi +
        (d : ℝ) / 2 + |Real.log Real.pi| / 2) * (Real.log ((k : ℝ) + 2) + 1) := by nlinarith
  have hper_nn : 0 ≤ (Real.log (2 * S.bergHi) + (S.bergExp : ℝ) + (1 / 2) * Real.log S.rankHi +
      (d : ℝ) / 2 + |Real.log Real.pi| / 2) * (Real.log ((k : ℝ) + 2) + 1) := by positivity
  calc ((S.block k).blockRk : ℝ) * _
      ≤ ((S.block k).blockRk : ℝ) * _ := mul_le_mul_of_nonneg_left hper hrk_pos.le
    _ ≤ (S.rankHi * (k : ℝ) ^ d) * _ := mul_le_mul_of_nonneg_right hrk_le hper_nn
    _ = _ := by ring

/-- **Asymptotic Equivalence `|log #smallSections(L^⊗k) - χ_Ar(L^⊗k)| = O(k^d log k)`
(`hs_chain_log_small_sub_chi_bound`)**:
combines Minkowski/Blichfeldt lower bound and Babai nearest-plane packing upper bound on every
block of `S : HSChainSystem d`! -/
theorem hs_chain_log_small_sub_chi_bound {d : ℕ} (S : HSChainSystem d) :
    ∃ C_diff : ℝ, 0 ≤ C_diff ∧
      ∀ k : ℕ, 1 ≤ k →
        |Real.log ((S.block k).smallSectionsCard : ℝ) - (S.block k).blockChi| ≤
          C_diff * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
  let C_lo : ℝ := S.rankHi * (Real.log (2 * S.bergHi) + (S.bergExp : ℝ) +
    (1 / 2) * Real.log S.rankHi + (d : ℝ) / 2 + |Real.log Real.pi| / 2)
  let M_hi : ℝ := max 1 (S.volHi + S.gsHi / 2)
  let C_hi : ℝ := S.rankHi * (Real.log M_hi + (S.gsExp : ℝ) +
    (1 / 2) * |Real.log (2 * Real.pi * Real.exp 1)|)
  let C_diff : ℝ := max C_lo C_hi
  have hM_ge1 : 1 ≤ M_hi := le_max_left _ _
  have hClo_nn : 0 ≤ C_lo := by
    have h1 : 0 ≤ Real.log (2 * S.bergHi) := Real.log_nonneg (by linarith [S.bergHi_ge_one])
    have h2 : 0 ≤ Real.log S.rankHi := Real.log_nonneg S.rankHi_ge_one
    have h3 : 0 ≤ S.rankHi := by linarith [S.rankHi_ge_one]
    positivity
  refine ⟨C_diff, le_trans hClo_nn (le_max_left _ _), fun k hk => ?_⟩
  obtain ⟨hlo, hhi⟩ := (S.block k).log_smallSections_sandwich
  have hrk_pos : (0 : ℝ) < ((S.block k).blockRk : ℝ) := Nat.cast_pos.mpr (S.block k).blockRk_pos
  have hrk_le : ((S.block k).blockRk : ℝ) ≤ S.rankHi * (k : ℝ) ^ d := S.rk_le_poly k hk
  have hlog_k1_le : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog_k2_nn : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  rw [abs_le]
  constructor
  · have htot := hs_chain_minkowski_loss_bound S hk
    have hC_ge : C_lo * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) ≤
        C_diff * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (by positivity)
    dsimp only [C_lo] at hC_ge
    linarith
  · have hsqrtr_ge1 : (1 : ℝ) ≤ √((S.block k).blockRk : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((S.block k).blockRk : ℝ) := by exact_mod_cast (S.block k).blockRk_pos
      simpa using Real.sqrt_le_sqrt h1
    have hvol_le : (S.block k).volConst / √((S.block k).blockRk : ℝ) ≤ S.volHi := by
      calc (S.block k).volConst / √((S.block k).blockRk : ℝ)
          ≤ (S.block k).volConst / 1 :=
            div_le_div_of_nonneg_left (S.block k).volConst_pos.le zero_lt_one hsqrtr_ge1
        _ = (S.block k).volConst := div_one _
        _ ≤ S.volHi := S.volConst_le k hk
    have hgs_le : (S.block k).gsCeil / 2 ≤ (S.gsHi / 2) * ((k : ℝ) + 1) ^ S.gsExp := by
      linarith [S.gsCeil_le k hk]
    have hpow_ge1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ S.gsExp := one_le_pow₀ (by linarith)
    have harg_pos : 0 < (S.block k).volConst / √((S.block k).blockRk : ℝ) + (S.block k).gsCeil / 2 :=
      add_pos_of_pos_of_nonneg (div_pos (S.block k).volConst_pos (by linarith))
        (div_nonneg (S.block k).gsCeil_nonneg (by norm_num))
    have harg_le : (S.block k).volConst / √((S.block k).blockRk : ℝ) + (S.block k).gsCeil / 2 ≤
        M_hi * ((k : ℝ) + 1) ^ S.gsExp := by
      have hsum : S.volHi + (S.gsHi / 2) * ((k : ℝ) + 1) ^ S.gsExp ≤
          (S.volHi + S.gsHi / 2) * ((k : ℝ) + 1) ^ S.gsExp := by nlinarith [S.volHi_pos]
      have hM : (S.volHi + S.gsHi / 2) * ((k : ℝ) + 1) ^ S.gsExp ≤
          M_hi * ((k : ℝ) + 1) ^ S.gsExp :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      linarith
    have hlog_arg : Real.log ((S.block k).volConst / √((S.block k).blockRk : ℝ) +
          (S.block k).gsCeil / 2) ≤
        Real.log M_hi + (S.gsExp : ℝ) * Real.log ((k : ℝ) + 2) := by
      have h2 := Real.log_le_log harg_pos harg_le
      rw [Real.log_mul (by linarith [hM_ge1]) (pow_pos (by positivity) _).ne', Real.log_pow] at h2
      have h3 : (S.gsExp : ℝ) * Real.log ((k : ℝ) + 1) ≤
          (S.gsExp : ℝ) * Real.log ((k : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hlog_k1_le (Nat.cast_nonneg _)
      linarith
    have hnn_m : 0 ≤ Real.log M_hi := Real.log_nonneg hM_ge1
    have hnn_g : 0 ≤ (S.gsExp : ℝ) := Nat.cast_nonneg _
    have hnn_abs : 0 ≤ |Real.log (2 * Real.pi * Real.exp 1)| := abs_nonneg _
    have habs := le_abs_self (Real.log (2 * Real.pi * Real.exp 1))
    have hper : Real.log ((S.block k).volConst / √((S.block k).blockRk : ℝ) +
          (S.block k).gsCeil / 2) + (1 / 2) * Real.log (2 * Real.pi * Real.exp 1) ≤
        (Real.log M_hi + (S.gsExp : ℝ) + (1 / 2) * |Real.log (2 * Real.pi * Real.exp 1)|) *
          (Real.log ((k : ℝ) + 2) + 1) := by nlinarith
    have hper_nn : 0 ≤ (Real.log M_hi + (S.gsExp : ℝ) +
        (1 / 2) * |Real.log (2 * Real.pi * Real.exp 1)|) * (Real.log ((k : ℝ) + 2) + 1) := by
      positivity
    have htot : ((S.block k).blockRk : ℝ) *
          Real.log ((S.block k).volConst / √((S.block k).blockRk : ℝ) + (S.block k).gsCeil / 2) +
        (((S.block k).blockRk : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) ≤
        C_hi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
      have hfac : ((S.block k).blockRk : ℝ) *
            Real.log ((S.block k).volConst / √((S.block k).blockRk : ℝ) + (S.block k).gsCeil / 2) +
          (((S.block k).blockRk : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1) =
          ((S.block k).blockRk : ℝ) *
            (Real.log ((S.block k).volConst / √((S.block k).blockRk : ℝ) + (S.block k).gsCeil / 2) +
              (1 / 2) * Real.log (2 * Real.pi * Real.exp 1)) := by ring
      rw [hfac]
      calc ((S.block k).blockRk : ℝ) * _
          ≤ ((S.block k).blockRk : ℝ) * _ := mul_le_mul_of_nonneg_left hper hrk_pos.le
        _ ≤ (S.rankHi * (k : ℝ) ^ d) * _ := mul_le_mul_of_nonneg_right hrk_le hper_nn
        _ = C_hi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by dsimp only [C_hi]; ring
    have hC_ge : C_hi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) ≤
        C_diff * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        (by positivity)
    linarith

/-- **MAIN PROVED ASYMPTOTIC ARITHMETIC HILBERT–SAMUEL THEOREM (`hs_chain_asymptotic`)**:
For EVERY `d ≥ 1` and EVERY concrete `HSChainSystem d`:
1. **Explicit two-sided `O(k^d log k)` asymptotic for `log #smallSections(L^⊗k)`**:
   `∃ C_hs ≥ 0, ∀ k ≥ 1, |log (#smallSections(L^⊗k)) - (k^(d+1) / (d+1)!) * (L^(d+1))_Ar| ≤ C_hs * k^d * (log(k + 2) + 1)`,
2. **Explicit two-sided `O(k^d log k)` asymptotic for Arakelov Euler characteristic `χ_Ar(L^⊗k)`**:
   `∃ C_chi ≥ 0, ∀ k ≥ 1, |χ_Ar(L^⊗k) - (k^(d+1) / (d+1)!) * (L^(d+1))_Ar| ≤ C_chi * k^d * (log(k + 2) + 1)`,
3. **Exact arithmetic volume limit for `log #smallSections`**:
   `Tendsto (fun k => log (#smallSections(L^⊗k)) / (k^(d+1) / (d+1)!)) atTop (𝓝 S.selfInt)`,
4. **Exact arithmetic volume limit for `χ_Ar(L^⊗k)`**:
   `Tendsto (fun k => χ_Ar(L^⊗k) / (k^(d+1) / (d+1)!)) atTop (𝓝 S.selfInt)`. -/
theorem hs_chain_asymptotic {d : ℕ} (S : HSChainSystem d) :
    (∃ C_hs : ℝ, 0 ≤ C_hs ∧ ∀ k : ℕ, 1 ≤ k →
      |Real.log ((S.block k).smallSectionsCard : ℝ) - HSChainSystem.hsNorm d k * S.selfInt| ≤
        C_hs * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) ∧
    (∃ C_chi : ℝ, 0 ≤ C_chi ∧ ∀ k : ℕ, 1 ≤ k →
      |(S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt| ≤
        C_chi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) ∧
    Tendsto (fun k : ℕ => Real.log ((S.block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k)
      atTop (𝓝 S.selfInt) ∧
    Tendsto (fun k : ℕ => (S.block k).blockChi / HSChainSystem.hsNorm d k)
      atTop (𝓝 S.selfInt) := by
  obtain ⟨hCchi_nn, hchi_bd, hchi_lim⟩ := hs_chain_chi_asymptotic S
  obtain ⟨C_diff, hCdiff_nn, hdiff_bd⟩ := hs_chain_log_small_sub_chi_bound S
  let C_chi : ℝ := |(S.block 0).blockChi| +
    |S.selfInt| * ((2 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) + S.stepErr
  let C_hs : ℝ := C_diff + C_chi
  have hChs_nn : 0 ≤ C_hs := add_nonneg hCdiff_nn hCchi_nn
  have hhs_bd : ∀ k : ℕ, 1 ≤ k →
      |Real.log ((S.block k).smallSectionsCard : ℝ) - HSChainSystem.hsNorm d k * S.selfInt| ≤
        C_hs * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) := by
    intro k hk
    have hsplit : Real.log ((S.block k).smallSectionsCard : ℝ) - HSChainSystem.hsNorm d k * S.selfInt =
        (Real.log ((S.block k).smallSectionsCard : ℝ) - (S.block k).blockChi) +
        ((S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt) := by ring
    rw [hsplit]
    have htri := abs_add_le
      (Real.log ((S.block k).smallSectionsCard : ℝ) - (S.block k).blockChi)
      ((S.block k).blockChi - HSChainSystem.hsNorm d k * S.selfInt)
    have h1 := hdiff_bd k hk
    have h2 := hchi_bd k hk
    dsimp only [C_hs, C_chi] at h2 ⊢
    linarith
  have hhs_lim : Tendsto (fun k : ℕ =>
      Real.log ((S.block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k) atTop (𝓝 S.selfInt) := by
    have hzero : Tendsto (fun k : ℕ =>
        Real.log ((S.block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k - S.selfInt)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_
        (tendsto_log_add_two_div_nat (C_hs * ((d + 1).factorial : ℝ)))
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hVpos : 0 < HSChainSystem.hsNorm d k := HSChainSystem.hsNorm_pos d hk
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hdiff : Real.log ((S.block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k - S.selfInt =
          (Real.log ((S.block k).smallSectionsCard : ℝ) - HSChainSystem.hsNorm d k * S.selfInt) /
            HSChainSystem.hsNorm d k := by
        field_simp [hVpos.ne']
      rw [hdiff, Real.norm_eq_abs, abs_div, abs_of_pos hVpos]
      calc |Real.log ((S.block k).smallSectionsCard : ℝ) - HSChainSystem.hsNorm d k * S.selfInt| /
              HSChainSystem.hsNorm d k
          ≤ (C_hs * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) / HSChainSystem.hsNorm d k :=
            div_le_div_of_nonneg_right (hhs_bd k hk) hVpos.le
        _ = C_hs * ((d + 1).factorial : ℝ) * (Real.log ((k : ℝ) + 2) + 1) / (k : ℝ) := by
            unfold HSChainSystem.hsNorm
            rw [pow_succ]
            have hkd : (k : ℝ) ^ d ≠ 0 := pow_ne_zero d hk_pos.ne'
            have hfac : ((d + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
            field_simp [hk_pos.ne', hkd, hfac]
    simpa using hzero.add_const S.selfInt
  exact ⟨⟨C_hs, hChs_nn, hhs_bd⟩, ⟨C_chi, hCchi_nn, hchi_bd⟩, hhs_lim, hchi_lim⟩

/-- **Asymptotic Arakelov Slope / Normalized Height Theorem (`hs_chain_slope_asymptotic`)**:
If `S : HSChainSystem d` has exact Hilbert–Samuel rank growth `rk (S.block k) = geomDeg * k^d / d! + O(k^(d-1))`
with `0 < S.geomDeg`, then the normalized Arakelov slope converges to the Faltings–Bost arithmetic height:
`Tendsto (fun k => (S.block k).blockSlope / (k : ℝ)) atTop (𝓝 (S.selfInt / (((d + 1 : ℕ) : ℝ) * S.geomDeg)))`. -/
theorem hs_chain_slope_asymptotic {d : ℕ} (S : HSChainSystem d) (hR : S.HasExactRank)
    (hdeg : 0 < S.geomDeg) :
    Tendsto (fun k : ℕ => (S.block k).blockSlope / (k : ℝ))
      atTop (𝓝 (S.selfInt / (((d + 1 : ℕ) : ℝ) * S.geomDeg))) := by
  have hchi_lim := (hs_chain_asymptotic S).2.2.2
  have hfac_d_pos : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
  have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  -- First show `rk (S.block k) / (k^d / d!) → S.geomDeg`.
  have hrk_lim : Tendsto (fun k : ℕ => ((S.block k).blockRk : ℝ) / ((k : ℝ) ^ d / (d.factorial : ℝ)))
      atTop (𝓝 S.geomDeg) := by
    have hzero : Tendsto (fun k : ℕ =>
        ((S.block k).blockRk : ℝ) / ((k : ℝ) ^ d / (d.factorial : ℝ)) - S.geomDeg) atTop (𝓝 0) := by
      have hinv : Tendsto (fun k : ℕ => (hR.rankErr * (d.factorial : ℝ)) * ((k : ℝ))⁻¹)
          atTop (𝓝 ((hR.rankErr * (d.factorial : ℝ)) * 0)) :=
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _
      rw [mul_zero] at hinv
      refine squeeze_zero_norm' ?_ hinv
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hden_pos : 0 < (k : ℝ) ^ d / (d.factorial : ℝ) :=
        div_pos (pow_pos hk_pos d) hfac_d_pos
      have hdiff : ((S.block k).blockRk : ℝ) / ((k : ℝ) ^ d / (d.factorial : ℝ)) - S.geomDeg =
          (((S.block k).blockRk : ℝ) - S.geomDeg * ((k : ℝ) ^ d / (d.factorial : ℝ))) /
            ((k : ℝ) ^ d / (d.factorial : ℝ)) := by
        field_simp [hden_pos.ne']
      rw [hdiff, Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
      calc |((S.block k).blockRk : ℝ) - S.geomDeg * ((k : ℝ) ^ d / (d.factorial : ℝ))| /
              ((k : ℝ) ^ d / (d.factorial : ℝ))
          ≤ (hR.rankErr * (k : ℝ) ^ (d - 1)) / ((k : ℝ) ^ d / (d.factorial : ℝ)) :=
            div_le_div_of_nonneg_right (hR.rk_asymp k hk) hden_pos.le
        _ = (hR.rankErr * (d.factorial : ℝ)) * ((k : ℝ))⁻¹ := by
            have hkpow : (k : ℝ) ^ d = (k : ℝ) ^ (d - 1) * (k : ℝ) := by
              rw [← pow_succ, Nat.sub_add_cancel S.hd]
            rw [hkpow]
            have hkd1 : (k : ℝ) ^ (d - 1) ≠ 0 := pow_ne_zero _ hk_pos.ne'
            field_simp [hk_pos.ne', hkd1, hfac_d_pos.ne']
    simpa using hzero.add_const S.geomDeg
  -- Combine `chi / (k^(d+1)/(d+1)!) → selfInt` and `rk / (k^d / d!) → geomDeg`.
  have hquot : Tendsto (fun k : ℕ =>
      ((S.block k).blockChi / HSChainSystem.hsNorm d k) /
        (((d + 1 : ℕ) : ℝ) * (((S.block k).blockRk : ℝ) / ((k : ℝ) ^ d / (d.factorial : ℝ)))))
      atTop (𝓝 (S.selfInt / (((d + 1 : ℕ) : ℝ) * S.geomDeg))) :=
    hchi_lim.div (hrk_lim.const_mul _) (mul_pos hd1_pos hdeg).ne'
  refine hquot.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hrk_pos : (0 : ℝ) < ((S.block k).blockRk : ℝ) := Nat.cast_pos.mpr (S.block k).blockRk_pos
  have hkd_pos : (0 : ℝ) < (k : ℝ) ^ d := pow_pos hk_pos d
  have hchi_eq := (S.block k).blockChi_eq_rk_mul_slope
  rw [hchi_eq]
  unfold HSChainSystem.hsNorm
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp [hk_pos.ne', hrk_pos.ne', hkd_pos.ne', hfac_d_pos.ne', hd1_pos.ne']

/-- **Direct Bridge to `Stage12SchurWeylLattices.GradedHermAlgebra`**:
every `HSChainSystem d` canonically yields a `GradedHermAlgebra d` with `volAr = S.selfInt`. -/
def HSChainSystem.toGradedHermAlgebra {d : ℕ} (S : HSChainSystem d) : GradedHermAlgebra d where
  hd := S.hd
  secSpace k := (S.block k).E
  secLat k := (S.block k).L
  secLat_ne_bot k _ := (S.block k).L_ne_bot
  supNorm k := (S.block k).supNorm
  supNorm_nonneg k := (S.block k).supNorm_nonneg
  volConst := S.volHi
  volConst_pos := S.volHi_pos
  norm_le_vol_supNorm k hk s :=
    ((S.block k).norm_le_vol_supNorm s).trans
      (mul_le_mul_of_nonneg_right (S.volConst_le k hk) ((S.block k).supNorm_nonneg s))
  bergConst := S.bergHi
  bergExp := S.bergExp
  bergConst_ge_one := S.bergHi_ge_one
  supNorm_le_bergman k hk s :=
    ((S.block k).supNorm_le_bergman s).trans
      (mul_le_mul_of_nonneg_right (S.bergConst_le k hk) (norm_nonneg s))
  rankHi := S.rankHi
  rankHi_ge_one := S.rankHi_ge_one
  rk_le_poly k hk := S.rk_le_poly k hk
  volAr := S.selfInt
  ahs_liminf ε hε := by
    have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hlim := (hs_chain_asymptotic S).2.2.2
    have hmem := (Metric.tendsto_atTop.mp hlim) (ε * ((d + 1).factorial : ℝ)) (mul_pos hε hfac_pos)
    filter_upwards [eventually_ge_atTop hmem.choose, eventually_ge_atTop 1] with k hk hk1
    have hd := hmem.choose_spec k hk
    rw [Real.dist_eq] at hd
    have hlo : S.selfInt - ε * ((d + 1).factorial : ℝ) ≤
        (S.block k).blockChi / HSChainSystem.hsNorm d k := by linarith [(abs_lt.mp hd).1]
    have hdiv := div_le_div_of_nonneg_right hlo hfac_pos.le
    have hlhs : (S.selfInt - ε * ((d + 1).factorial : ℝ)) / ((d + 1).factorial : ℝ) =
        S.selfInt / ((d + 1).factorial : ℝ) - ε := by
      field_simp [hfac_pos.ne']
    have hrhs : ((S.block k).blockChi / HSChainSystem.hsNorm d k) / ((d + 1).factorial : ℝ) =
        arithDeg (S.block k).L / (k : ℝ) ^ (d + 1) := by
      unfold HSChainSystem.hsNorm HSMBlock.blockChi chiAr
      have hkd1 : (k : ℝ) ^ (d + 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
      field_simp [hfac_pos.ne', hkd1]
    linarith

/-- Helper: `0 < Real.log B.smallSectionsCard` yields a nonzero strictly small section in `B.L`. -/
theorem HSMBlock.exists_nonzero_small_of_log_pos (B : HSMBlock)
    (hlog : 0 < Real.log (B.smallSectionsCard : ℝ)) :
    ∃ s : B.L, s ≠ 0 ∧ B.supNorm s.1 < 1 := by
  have hgt1 : 1 < B.smallSectionsCard := by
    by_contra hle
    have hleR : (B.smallSectionsCard : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_not_lt hle
    have hpos : (0 : ℝ) < (B.smallSectionsCard : ℝ) := Nat.cast_pos.mpr B.one_le_smallSectionsCard
    have hlog_le : Real.log (B.smallSectionsCard : ℝ) ≤ 0 :=
      (Real.log_le_log hpos hleR).trans (by simp)
    linarith
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hgt1
  by_cases hs10 : s₁ = 0
  · exact ⟨s₂, fun h => hne (hs10.trans h.symm), (B.smallSections_finite.mem_toFinset).mp hs₂⟩
  · exact ⟨s₁, hs10, (B.smallSections_finite.mem_toFinset).mp hs₁⟩

/-- **Moriwaki Bigness Extraction for `HSChainSystem d` (`hs_chain_moriwaki_big`)**:
Whenever `0 < S.selfInt`, there exist `c₀ > 0` and `K₀ ≥ 1` such that for all `k ≥ K₀`:
1. `c₀ * k^(d + 1) ≤ Real.log ((S.block k).smallSectionsCard : ℝ)`,
2. There exists a nonzero strictly small section `s : (S.block k).L` with `s ≠ 0 ∧ (S.block k).supNorm s.1 < 1`. -/
theorem hs_chain_moriwaki_big {d : ℕ} (S : HSChainSystem d) (hbig : 0 < S.selfInt) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      (∀ k : ℕ, K₀ ≤ k → c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log ((S.block k).smallSectionsCard : ℝ)) ∧
      (∀ k : ℕ, K₀ ≤ k → ∃ s : (S.block k).L, s ≠ 0 ∧ (S.block k).supNorm s.1 < 1) := by
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  let c₀ : ℝ := S.selfInt / (2 * ((d + 1).factorial : ℝ))
  have hc₀_pos : 0 < c₀ := div_pos hbig (by positivity)
  have hlim := (hs_chain_asymptotic S).2.2.1
  have hmem := (Metric.tendsto_atTop.mp hlim) (S.selfInt / 2) (half_pos hbig)
  let K₀ : ℕ := max 1 hmem.choose
  have hgrow : ∀ k : ℕ, K₀ ≤ k →
      c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log ((S.block k).smallSectionsCard : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
    have hd := hmem.choose_spec k (le_trans (le_max_right _ _) hk)
    rw [Real.dist_eq] at hd
    have hVpos : 0 < HSChainSystem.hsNorm d k := HSChainSystem.hsNorm_pos d hk1
    have hge : S.selfInt / 2 ≤
        Real.log ((S.block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k := by
      linarith [(abs_lt.mp hd).1]
    have hmul := (le_div_iff₀ hVpos).mp hge
    have heq : (S.selfInt / 2) * HSChainSystem.hsNorm d k = c₀ * (k : ℝ) ^ (d + 1) := by
      unfold HSChainSystem.hsNorm c₀; field_simp [hfac_pos.ne']
    linarith
  refine ⟨c₀, hc₀_pos, K₀, le_max_left _ _, hgrow, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  exact (S.block k).exists_nonzero_small_of_log_pos
    (lt_of_lt_of_le (mul_pos hc₀_pos (pow_pos (Nat.cast_pos.mpr hk1) (d + 1))) (hgrow k hk))

/-- **Metric-Twist Arithmetic Kleiman Lower Bound (`hs_chain_twist_lower`)**:
For ANY `S : HSChainSystem d` with exact rank asymptotic `hR : S.HasExactRank` and ANY real
archimedean fiber shift `c : ℝ` (positive, zero, OR negative!), twisting `S.block k` by `e^{-c * k}`
shifts the arithmetic volume lower bound by `(d + 1) * c * S.geomDeg`:
1. `Tendsto (fun k => (S.twistMetricBlock c k).blockChi / hsNorm d k) atTop (𝓝 (S.selfInt + (d + 1) * c * S.geomDeg))`,
2. `∀ ε > 0, ∀ᶠ k in atTop, S.selfInt + (d + 1) * c * S.geomDeg - ε ≤ log (#smallSections (S.twistMetricBlock c k)) / hsNorm d k`,
3. Whenever `0 < S.selfInt + (d + 1) * c * S.geomDeg`, `#smallSections (S.twistMetricBlock c k)`
   grows exponentially as `exp(c₀ * k^(d+1))` and yields nonzero small sections for all large `k`! -/
theorem hs_chain_twist_lower {d : ℕ} (S : HSChainSystem d) (hR : S.HasExactRank) (c : ℝ) :
    let V_c : ℝ := S.selfInt + ((d + 1 : ℕ) : ℝ) * c * S.geomDeg
    Tendsto (fun k : ℕ => (S.twistMetricBlock c k).blockChi / HSChainSystem.hsNorm d k)
      atTop (𝓝 V_c) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      V_c - ε ≤ Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ) /
        HSChainSystem.hsNorm d k) ∧
    (0 < V_c → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      (∀ k : ℕ, K₀ ≤ k →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ)) ∧
      (∀ k : ℕ, K₀ ≤ k →
        ∃ s : (S.twistMetricBlock c k).L, s ≠ 0 ∧ (S.twistMetricBlock c k).supNorm s.1 < 1)) := by
  intro V_c
  have hchi_lim := (hs_chain_asymptotic S).2.2.2
  have hfac_d_pos : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
  have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  have hfac_d1_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  -- Limit of `c * k * rk (S.block k) / hsNorm d k`.
  have hshift_lim : Tendsto (fun k : ℕ =>
      (c * (k : ℝ) * ((S.block k).blockRk : ℝ)) / HSChainSystem.hsNorm d k)
      atTop (𝓝 (((d + 1 : ℕ) : ℝ) * c * S.geomDeg)) := by
    have hzero : Tendsto (fun k : ℕ =>
        (c * (k : ℝ) * ((S.block k).blockRk : ℝ)) / HSChainSystem.hsNorm d k -
          ((d + 1 : ℕ) : ℝ) * c * S.geomDeg) atTop (𝓝 0) := by
      have hinv : Tendsto (fun k : ℕ =>
          (|c| * hR.rankErr * ((d + 1).factorial : ℝ)) * ((k : ℝ))⁻¹)
          atTop (𝓝 ((|c| * hR.rankErr * ((d + 1).factorial : ℝ)) * 0)) :=
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _
      rw [mul_zero] at hinv
      refine squeeze_zero_norm' ?_ hinv
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hVpos : 0 < HSChainSystem.hsNorm d k := HSChainSystem.hsNorm_pos d hk
      have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d - 1) := pow_pos hk_pos (d - 1)
      have hrew : (c * (k : ℝ) * ((S.block k).blockRk : ℝ)) / HSChainSystem.hsNorm d k -
          ((d + 1 : ℕ) : ℝ) * c * S.geomDeg =
          (c * (k : ℝ) * (((S.block k).blockRk : ℝ) -
            S.geomDeg * ((k : ℝ) ^ d / (d.factorial : ℝ)))) / HSChainSystem.hsNorm d k := by
        unfold HSChainSystem.hsNorm
        rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
        have hkd : (k : ℝ) ^ d ≠ 0 := pow_ne_zero d hk_pos.ne'
        field_simp [hk_pos.ne', hkd, hfac_d_pos.ne', hd1_pos.ne']
      rw [hrew, Real.norm_eq_abs, abs_div, abs_of_pos hVpos, abs_mul, abs_mul, abs_of_pos hk_pos]
      have hbd := hR.rk_asymp k hk
      calc |c| * (k : ℝ) * |((S.block k).blockRk : ℝ) -
              S.geomDeg * ((k : ℝ) ^ d / (d.factorial : ℝ))| / HSChainSystem.hsNorm d k
          ≤ (|c| * (k : ℝ) * (hR.rankErr * (k : ℝ) ^ (d - 1))) / HSChainSystem.hsNorm d k :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbd (mul_nonneg (abs_nonneg c) hk_pos.le)) hVpos.le
        _ = (|c| * hR.rankErr * ((d + 1).factorial : ℝ)) * ((k : ℝ))⁻¹ := by
            unfold HSChainSystem.hsNorm
            have hkpow : (k : ℝ) ^ (d + 1) = (k : ℝ) ^ (d - 1) * (k : ℝ) * (k : ℝ) := by
              rw [pow_succ, show (k : ℝ) ^ d = (k : ℝ) ^ (d - 1) * (k : ℝ) by
                rw [← pow_succ, Nat.sub_add_cancel S.hd]]
            rw [hkpow]
            field_simp [hk_pos.ne', hkd1_pos.ne', hfac_d1_pos.ne']
    simpa using hzero.add_const (((d + 1 : ℕ) : ℝ) * c * S.geomDeg)
  have htwist_chi_lim : Tendsto (fun k : ℕ =>
      (S.twistMetricBlock c k).blockChi / HSChainSystem.hsNorm d k) atTop (𝓝 V_c) := by
    have hadd := hchi_lim.add hshift_lim
    refine hadd.congr fun k => ?_
    rw [(S.twistMetricBlock_invariants c k).2.1, add_div]
  have hliminf : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      V_c - ε ≤ Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ) /
        HSChainSystem.hsNorm d k := by
    intro ε hε
    have h1 := (Metric.tendsto_atTop.mp htwist_chi_lim) (ε / 2) (half_pos hε)
    let C_lo : ℝ := S.rankHi * (Real.log (2 * S.bergHi) + (S.bergExp : ℝ) +
      (1 / 2) * Real.log S.rankHi + (d : ℝ) / 2 + |Real.log Real.pi| / 2)
    have herr := tendsto_log_add_two_div_nat (C_lo * ((d + 1).factorial : ℝ))
    have h2 := (Metric.tendsto_atTop.mp herr) (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop h1.choose, eventually_ge_atTop h2.choose,
      eventually_ge_atTop 1] with k hk1 hk2 hk_ge1
    have hd1 := h1.choose_spec k hk1
    have hd2 := h2.choose_spec k hk2
    rw [Real.dist_eq] at hd1 hd2
    rw [sub_zero] at hd2
    have hVpos : 0 < HSChainSystem.hsNorm d k := HSChainSystem.hsNorm_pos d hk_ge1
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_ge1
    have hsand := ((S.twistMetricBlock c k).log_smallSections_sandwich).1
    have hrk_eq : (S.twistMetricBlock c k).blockRk = (S.block k).blockRk :=
      (S.twistMetricBlock_invariants c k).1
    have hberg_eq : (S.twistMetricBlock c k).bergConst = (S.block k).bergConst := rfl
    rw [hrk_eq, hberg_eq] at hsand
    have hloss : ((S.block k).blockRk : ℝ) *
        (Real.log (2 * (S.block k).bergConst) + (1 / 2) * Real.log ((S.block k).blockRk : ℝ) -
          (1 / 2) * Real.log Real.pi) ≤
        C_lo * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) :=
      hs_chain_minkowski_loss_bound S hk_ge1
    have hdiv := div_le_div_of_nonneg_right (by linarith :
      (S.twistMetricBlock c k).blockChi - C_lo * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1) ≤
        Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ)) hVpos.le
    rw [sub_div] at hdiv
    have herr_eq : (C_lo * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) / HSChainSystem.hsNorm d k =
        C_lo * ((d + 1).factorial : ℝ) * (Real.log ((k : ℝ) + 2) + 1) / (k : ℝ) := by
      unfold HSChainSystem.hsNorm
      rw [pow_succ]
      have hkd : (k : ℝ) ^ d ≠ 0 := pow_ne_zero d hk_pos.ne'
      field_simp [hk_pos.ne', hkd, hfac_d1_pos.ne']
    rw [herr_eq] at hdiv
    have hle_eps2 : C_lo * ((d + 1).factorial : ℝ) * (Real.log ((k : ℝ) + 2) + 1) / (k : ℝ) ≤ ε / 2 :=
      (le_abs_self _).trans hd2.le
    linarith [(abs_lt.mp hd1).1]
  refine ⟨htwist_chi_lim, hliminf, fun hVc => ?_⟩
  let c₀ : ℝ := V_c / (2 * ((d + 1).factorial : ℝ))
  have hc₀_pos : 0 < c₀ := div_pos hVc (by positivity)
  have hev := hliminf (V_c / 2) (half_pos hVc)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K₁, hK₁⟩ := hev
  let K₀ : ℕ := max 1 K₁
  have hgrow : ∀ k : ℕ, K₀ ≤ k →
      c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
    have hVpos : 0 < HSChainSystem.hsNorm d k := HSChainSystem.hsNorm_pos d hk1
    have hge : V_c / 2 ≤
        Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k := by
      have := hK₁ k (le_trans (le_max_right _ _) hk); linarith
    have hmul := (le_div_iff₀ hVpos).mp hge
    have heq : (V_c / 2) * HSChainSystem.hsNorm d k = c₀ * (k : ℝ) ^ (d + 1) := by
      unfold HSChainSystem.hsNorm c₀; field_simp [hfac_d1_pos.ne']
    linarith
  refine ⟨c₀, hc₀_pos, K₀, le_max_left _ _, hgrow, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  exact (S.twistMetricBlock c k).exists_nonzero_small_of_log_pos
    (lt_of_lt_of_le (mul_pos hc₀_pos (pow_pos (Nat.cast_pos.mpr hk1) (d + 1))) (hgrow k hk))

end ArithHilbertSamuelAsymptotic

/-! ## Section 5: Packaged `HSUse`, `arith_hilbert_samuel_of_systems`, `hsUse_outright` & Wave 2 Hooks -/

section Wave2PackagedInterface

/-- **Component 1 of `HSUse` (`ArithKleimanStmt`)**:
Arithmetic Kleiman metric-twist bigness & Moriwaki small-section positivity statement on `S`. -/
def ArithKleimanStmt {d : ℕ} (S : HSChainSystem d) : Prop :=
  (0 < S.selfInt → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    (∀ k : ℕ, K₀ ≤ k → c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log ((S.block k).smallSectionsCard : ℝ)) ∧
    (∀ k : ℕ, K₀ ≤ k → ∃ s : (S.block k).L, s ≠ 0 ∧ (S.block k).supNorm s.1 < 1)) ∧
  (S.HasExactRank → ∀ c : ℝ, 0 < S.selfInt + ((d + 1 : ℕ) : ℝ) * c * S.geomDeg →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      (∀ k : ℕ, K₀ ≤ k →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log ((S.twistMetricBlock c k).smallSectionsCard : ℝ)) ∧
      (∀ k : ℕ, K₀ ≤ k →
        ∃ s : (S.twistMetricBlock c k).L, s ≠ 0 ∧ (S.twistMetricBlock c k).supNorm s.1 < 1))

/-- **Component 2 of `HSUse` (`G7CovolStmt`)**:
Quantitative two-sided log-covolume (`χ_Ar = -log covol`) and `log #smallSections` control with
explicit `O(k^d log k)` remainder. -/
def G7CovolStmt {d : ℕ} (S : HSChainSystem d) : Prop :=
  (∃ C_chi : ℝ, 0 ≤ C_chi ∧ ∀ k : ℕ, 1 ≤ k →
    |(-Real.log (covol (S.block k).L)) - HSChainSystem.hsNorm d k * S.selfInt| ≤
      C_chi * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1)) ∧
  (∃ C_hs : ℝ, 0 ≤ C_hs ∧ ∀ k : ℕ, 1 ≤ k →
    |Real.log ((S.block k).smallSectionsCard : ℝ) - HSChainSystem.hsNorm d k * S.selfInt| ≤
      C_hs * (k : ℝ) ^ d * (Real.log ((k : ℝ) + 2) + 1))

/-- **Component 3 of `HSUse` (`ArithVolNefStmt`)**:
Exact arithmetic volume convergence of both `log #smallSections(L^⊗k)` and `χ_Ar(L^⊗k)` to
`S.selfInt = (L^(d+1))_Ar`. -/
def ArithVolNefStmt {d : ℕ} (S : HSChainSystem d) : Prop :=
  Tendsto (fun k : ℕ => Real.log ((S.block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k)
    atTop (𝓝 S.selfInt) ∧
  Tendsto (fun k : ℕ => (S.block k).blockChi / HSChainSystem.hsNorm d k)
    atTop (𝓝 S.selfInt)

/-- **Component 4 (`ArithVolMultStmt` — `ArithmeticVolumeMultiplicative`)**:
Exact homogeneity of arithmetic volume under all Veronese tensor powers `L^{⊗ m}` (`m ≥ 1`):
`vol_Ar(L^{⊗ m}) = m^(d + 1) * vol_Ar(L)`. -/
def ArithVolMultStmt {d : ℕ} (S : HSChainSystem d) : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m),
    Tendsto (fun k : ℕ =>
      Real.log (((S.powerChain m hm).block k).smallSectionsCard : ℝ) / HSChainSystem.hsNorm d k)
      atTop (𝓝 ((m : ℝ) ^ (d + 1) * S.selfInt)) ∧
    Tendsto (fun k : ℕ =>
      ((S.powerChain m hm).block k).blockChi / HSChainSystem.hsNorm d k)
      atTop (𝓝 ((m : ℝ) ^ (d + 1) * S.selfInt))

/-- **Packaged `HSUse` Interface for M4 Wave 2 (`Stage14M4_AhSlimDeepStR`, `Stage14M4_HeightLowerGeneral`)**:
bundles `ArithKleimanStmt`, `G7CovolStmt`, `ArithVolNefStmt`, and `ArithVolMultStmt` cleanly and
non-circularly. -/
structure HSUse {d : ℕ} (S : HSChainSystem d) : Prop where
  arithKleiman : ArithKleimanStmt S
  g7Covol : G7CovolStmt S
  arithVolNef : ArithVolNefStmt S
  arithVolMult : ArithVolMultStmt S

/-- **Main Packaged Interface Theorem (`arith_hilbert_samuel_of_systems`)**:
From any concrete `S : HSChainSystem d`, unconditionally derives:
1. Complete `HSUse S` (`ArithKleiman`, `G7Covol`, `ArithVolNef`, `ArithVolMult`),
2. Exact normalized Arakelov slope / Faltings–Bost height convergence under `S.HasExactRank` and `0 < S.geomDeg`:
   `Tendsto (fun k => (S.block k).blockSlope / k) atTop (𝓝 (S.selfInt / ((d + 1) * S.geomDeg)))`. -/
theorem arith_hilbert_samuel_of_systems {d : ℕ} (S : HSChainSystem d) :
    HSUse S ∧
    (S.HasExactRank → 0 < S.geomDeg →
      Tendsto (fun k : ℕ => (S.block k).blockSlope / (k : ℝ))
        atTop (𝓝 (S.selfInt / (((d + 1 : ℕ) : ℝ) * S.geomDeg)))) := by
  obtain ⟨hhs_bd, hchi_bd, hhs_lim, hchi_lim⟩ := hs_chain_asymptotic S
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun hR hdeg => hs_chain_slope_asymptotic S hR hdeg⟩
  · exact ⟨fun hbig => hs_chain_moriwaki_big S hbig,
      fun hR c hVc => (hs_chain_twist_lower S hR c).2.2 hVc⟩
  · exact ⟨hchi_bd, hhs_bd⟩
  · exact ⟨hhs_lim, hchi_lim⟩
  · intro m hm
    obtain ⟨_, _, hpow_hs, hpow_chi⟩ := hs_chain_asymptotic (S.powerChain m hm)
    exact ⟨by simpa [HSChainSystem.powerChain] using hpow_hs,
      by simpa [HSChainSystem.powerChain] using hpow_chi⟩

/-- **Outright Unconditional Discharge (`hsUse_outright`)**:
every concrete `HSChainSystem d` satisfies `HSUse S` unconditionally (`0` extra hypotheses!). -/
theorem hsUse_outright {d : ℕ} (S : HSChainSystem d) : HSUse S :=
  (arith_hilbert_samuel_of_systems S).1

/-- **Wave 2 Height Lower Bound / Maximal-Slope Comparison Hook (`height_lower_from_hsUse`)**:
Ready directly for `Stage14M4_HeightLowerGeneral` and `Stage14M4_AhSlimDeepStR`:
for any `S : HSChainSystem d` with exact rank `hR : S.HasExactRank` and `0 < S.geomDeg`:
if the maximal Arakelov slopes satisfy `muMax (S.block k).L ≤ M_hi * k + C_hi` for all large `k`,
then the normalized top arithmetic height is bounded above by `M_hi`:
`S.selfInt / (((d + 1 : ℕ) : ℝ) * S.geomDeg) ≤ M_hi`!
Equivalently, any upper bound `M_hi` on normalized maximal slopes forces an upper bound on
`S.selfInt`, and any lower bound on `S.selfInt` forces `M_hi ≥ h_L(X)`! -/
theorem height_lower_from_hsUse {d : ℕ} (S : HSChainSystem d) (hR : S.HasExactRank)
    (hdeg : 0 < S.geomDeg) (_hU : HSUse S) {M_hi C_hi : ℝ}
    (hmu : ∀ᶠ k : ℕ in atTop, muMax (S.block k).L ≤ M_hi * (k : ℝ) + C_hi) :
    S.selfInt / (((d + 1 : ℕ) : ℝ) * S.geomDeg) ≤ M_hi := by
  have hlim := hs_chain_slope_asymptotic S hR hdeg
  have hupper_lim : Tendsto (fun k : ℕ => M_hi + C_hi * ((k : ℝ))⁻¹) atTop (𝓝 M_hi) := by
    have hinv : Tendsto (fun k : ℕ => C_hi * ((k : ℝ))⁻¹) atTop (𝓝 (C_hi * 0)) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C_hi
    rw [mul_zero] at hinv
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  refine le_of_tendsto_of_tendsto hlim hupper_lim ?_
  filter_upwards [hmu, eventually_ge_atTop 1] with k hk_mu hk1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hsl_le : (S.block k).blockSlope ≤ muMax (S.block k).L :=
    slope_le_muMax (S.block k).L (S.block k).L le_rfl (S.block k).L_ne_bot
  have h1 : (S.block k).blockSlope ≤ M_hi * (k : ℝ) + C_hi := hsl_le.trans hk_mu
  have hdiv := div_le_div_of_nonneg_right h1 hk_pos.le
  have hrhs : (M_hi * (k : ℝ) + C_hi) / (k : ℝ) = M_hi + C_hi * ((k : ℝ))⁻¹ := by
    field_simp [hk_pos.ne']
  linarith

/-- **Wave 2 `L3` Hodge-Lattice Covolume Bridge (`l3_covolume_from_hsChain`)**:
Connects `HSChainSystem d` directly to `Stage12SchurWeylLattices.L3_hodge_covolume_bound`:
if an `m`-tuple of indefinite Hodge lattices `M j` receives `rk (M j)` linearly independent small
sections from blocks `S.block (k j)` via bounded charts `Ψ j` (`‖Ψ j x‖ ≤ C_chart j * ‖x‖`),
then unconditionally:
1. `Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_chart j * S.volHi)`,
2. `∑ j, (2 / D) * Real.log (covol (M j)) ≤ ∑ j, (2 * rk (M j) / D) * Real.log (C_chart j * S.volHi)`. -/
theorem l3_covolume_from_hsChain {d m : ℕ} (S : HSChainSystem d)
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j)
    (Ψ : ∀ j, (S.block (k j)).E → E j)
    (C_chart : Fin m → ℝ) (hCpos : ∀ j, 0 < C_chart j)
    (hΨ_bound : ∀ j x, ‖Ψ j x‖ ≤ C_chart j * ‖x‖)
    (t : ∀ j, Fin (rk (M j)) → (S.block (k j)).L)
    (ht_small : ∀ j i, t j i ∈ (S.block (k j)).smallSectionsSet)
    (hΨ_mem : ∀ j i, Ψ j (t j i).1 ∈ M j)
    (hΨ_li : ∀ j, LinearIndependent ℝ (fun i => Ψ j (t j i).1))
    {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m, Real.log (covol (M j)) ≤ (rk (M j) : ℝ) * Real.log (C_chart j * S.volHi)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      ∑ j : Fin m, (2 * (rk (M j) : ℝ) / D) * Real.log (C_chart j * S.volHi)) := by
  have hbd := L3_hodge_covolume_bound E M hM0 (fun j i => Ψ j (t j i).1) hΨ_mem hΨ_li
    (fun j => C_chart j * S.volHi) (fun j => mul_pos (hCpos j) S.volHi_pos)
    (fun j i => by
      have h1 := hΨ_bound j (t j i).1
      have h2 := (S.block (k j)).norm_le_vol_supNorm (t j i).1
      have h3 : (S.block (k j)).supNorm (t j i).1 < 1 := ht_small j i
      have h4 : (S.block (k j)).volConst ≤ S.volHi := S.volConst_le (k j) (hk j)
      have h5 : ‖(t j i).1‖ ≤ S.volHi := by
        have hvol_nn : 0 ≤ (S.block (k j)).volConst := (S.block (k j)).volConst_pos.le
        nlinarith [(S.block (k j)).supNorm_nonneg (t j i).1]
      exact h1.trans (mul_le_mul_of_nonneg_left h5 (hCpos j).le))
    hD
  exact ⟨hbd.1, hbd.2.2.2⟩

end Wave2PackagedInterface

/-! ## Section 6: Concrete Zero-Assumption Realizations (`ℙ^d`, CM Hermitian Algebras, Arithmetic Surfaces) -/

section ConcreteZeroAssumptionRealizations

/-! ### Helper Combinatorial Identities for `ℙ^d` Symmetric-Power Chains -/

/-- Exact binomial step identity for `ℙ^d` Euler characteristics:
`(k + 1) * Nat.choose (k + d + 1) d = (k + d + 1) * Nat.choose (k + d) d`. -/
theorem succ_mul_choose_add_eq (d k : ℕ) :
    (k + 1) * Nat.choose (k + d + 1) d = (k + d + 1) * Nat.choose (k + d) d := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show d ≤ k + d + 1 by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show d ≤ k + d by omega)
  have hsub1 : k + d + 1 - d = k + 1 := by omega
  have hsub2 : k + d - d = k := by omega
  rw [hsub1] at h1
  rw [hsub2] at h2
  have hpos : 0 < d.factorial * k.factorial :=
    Nat.mul_pos (Nat.factorial_pos d) (Nat.factorial_pos k)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc (k + 1) * Nat.choose (k + d + 1) d * (d.factorial * k.factorial)
      = Nat.choose (k + d + 1) d * d.factorial * ((k + 1) * k.factorial) := by ring
    _ = Nat.choose (k + d + 1) d * d.factorial * (k + 1).factorial := by rw [Nat.factorial_succ]
    _ = (k + d + 1).factorial := h1
    _ = (k + d + 1) * (k + d).factorial := Nat.factorial_succ (k + d)
    _ = (k + d + 1) * (Nat.choose (k + d) d * d.factorial * k.factorial) := by rw [← h2]
    _ = (k + d + 1) * Nat.choose (k + d) d * (d.factorial * k.factorial) := by ring

/-- Exact binomial-polynomial approximation for `H^0(ℙ^d, 𝒪(k))`:
for every `d ≥ 1` and `k : ℕ`,
`0 ≤ Nat.choose (k + d) d - k^d / d! ≤ ((2 * d)^d / d!) * (k + 1)^(d - 1)`. -/
theorem choose_sub_pow_div_factorial_bound {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    0 ≤ (Nat.choose (k + d) d : ℝ) - (k : ℝ) ^ d / (d.factorial : ℝ) ∧
    (Nat.choose (k + d) d : ℝ) - (k : ℝ) ^ d / (d.factorial : ℝ) ≤
      ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) * ((k : ℝ) + 1) ^ (d - 1) := by
  have hlo := pow_div_factorial_le_choose d k
  refine ⟨sub_nonneg.mpr hlo, ?_⟩
  have hfac_pos : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
  have hup_choose : (Nat.choose (k + d) d : ℝ) ≤ ((k : ℝ) + (d : ℝ)) ^ d / (d.factorial : ℝ) := by
    have hdvd : d.factorial ∣ (k + d).descFactorial d := Nat.factorial_dvd_descFactorial _ d
    rw [Nat.choose_eq_descFactorial_div_factorial,
      Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d))]
    refine div_le_div_of_nonneg_right ?_ hfac_pos.le
    have hle : (k + d).descFactorial d ≤ (k + d) ^ d := Nat.descFactorial_le_pow _ _
    exact_mod_cast hle
  have hdiff : ((k : ℝ) + (d : ℝ)) ^ d - (k : ℝ) ^ d ≤
      (2 * (d : ℝ)) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by
    have hrew : ((k : ℝ) + (d : ℝ)) ^ d - (k : ℝ) ^ d =
        ∑ i ∈ Finset.range d, (k : ℝ) ^ i * (d : ℝ) ^ (d - i) * (Nat.choose d i : ℝ) := by
      rw [add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one]
      ring
    rw [hrew]
    have hch : ∑ i ∈ Finset.range d, (Nat.choose d i : ℝ) ≤ (2 : ℝ) ^ d := by
      calc ∑ i ∈ Finset.range d, (Nat.choose d i : ℝ)
          ≤ ∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ d))
              fun _ _ _ => Nat.cast_nonneg _
        _ = (2 : ℝ) ^ d := by exact_mod_cast Nat.sum_range_choose d
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    calc ∑ i ∈ Finset.range d, (k : ℝ) ^ i * (d : ℝ) ^ (d - i) * (Nat.choose d i : ℝ)
        ≤ ∑ i ∈ Finset.range d, (Nat.choose d i : ℝ) * (((k : ℝ) + 1) ^ (d - 1) * (d : ℝ) ^ d) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hid : i ≤ d - 1 := by have := Finset.mem_range.mp hi; omega
          have hk_p : (k : ℝ) ^ i ≤ ((k : ℝ) + 1) ^ (d - 1) :=
            (pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) i).trans
              (pow_le_pow_right₀ (by linarith) hid)
          have hd_p : (d : ℝ) ^ (d - i) ≤ (d : ℝ) ^ d := pow_le_pow_right₀ hd1 (Nat.sub_le d i)
          have hprod := mul_le_mul hk_p hd_p (by positivity) (by positivity)
          calc (k : ℝ) ^ i * (d : ℝ) ^ (d - i) * (Nat.choose d i : ℝ)
              = (Nat.choose d i : ℝ) * ((k : ℝ) ^ i * (d : ℝ) ^ (d - i)) := by ring
            _ ≤ (Nat.choose d i : ℝ) * (((k : ℝ) + 1) ^ (d - 1) * (d : ℝ) ^ d) :=
                mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
      _ = (∑ i ∈ Finset.range d, (Nat.choose d i : ℝ)) * (((k : ℝ) + 1) ^ (d - 1) * (d : ℝ) ^ d) := by
          rw [← Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ d * (((k : ℝ) + 1) ^ (d - 1) * (d : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_right hch (by positivity)
      _ = (2 * (d : ℝ)) ^ d * ((k : ℝ) + 1) ^ (d - 1) := by rw [mul_pow]; ring
  have hdiv := div_le_div_of_nonneg_right hdiff hfac_pos.le
  rw [sub_div, mul_div_right_comm] at hdiv
  linarith

/-! ### Realization 1: Projective Space `ℙ^d` with `𝒪(1)_{-α}` (`d ≥ 1`, `α > 0`, `0` Assumptions) -/

/-- Concrete `HSMBlock` realizing `H^0(ℙ^d, 𝒪(k)) = Sym^k(ℤ^{d+1})` with metric parameter `α ≥ 0`. -/
def projSpaceBlock (d : ℕ) {α : ℝ} (hα : 0 ≤ α) (k : ℕ) : HSMBlock :=
  haveI : Nonempty (MultiIndex (d + 1) k) :=
    Fintype.card_pos_iff.mp (card_multiIndex_pos (Nat.succ_pos d) k)
  HSMBlock.ofDiagLat
    (fun β : MultiIndex (d + 1) k =>
      (1 : ℝ) * ∏ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i))
    (fun β => mul_pos zero_lt_one (Finset.prod_pos fun _ _ => pow_pos (Real.exp_pos _) _))
    1
    (fun β => by
      rw [one_mul]
      have hprod : ∏ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i) = Real.exp (-α * (k : ℝ)) := by
        have h1 : ∀ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i) = Real.exp (-α * (β.1 i : ℝ)) := by
          intro i; rw [← Real.exp_nat_mul]; ring_nf
        simp_rw [h1, ← Real.exp_sum, ← Finset.mul_sum, ← Nat.cast_sum, β.2]
      rw [hprod]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k]))

theorem projSpaceBlock_invariants (d : ℕ) {α : ℝ} (hα : 0 ≤ α) (k : ℕ) :
    (projSpaceBlock d hα k).blockRk = Nat.choose (k + d) d ∧
    (projSpaceBlock d hα k).blockChi = (k : ℝ) * (Nat.choose (k + d) d : ℝ) * α := by
  have : Nonempty (MultiIndex (d + 1) k) :=
    Fintype.card_pos_iff.mp (card_multiIndex_pos (Nat.succ_pos d) k)
  obtain ⟨hrk, hchi⟩ := HSMBlock.ofDiagLat_invariants
    (fun β : MultiIndex (d + 1) k => (1 : ℝ) * ∏ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i))
    (fun β => mul_pos zero_lt_one (Finset.prod_pos fun _ _ => pow_pos (Real.exp_pos _) _))
    1
    (fun β => by
      rw [one_mul]
      have hprod : ∏ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i) = Real.exp (-α * (k : ℝ)) := by
        have h1 : ∀ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i) = Real.exp (-α * (β.1 i : ℝ)) := by
          intro i; rw [← Real.exp_nat_mul]; ring_nf
        simp_rw [h1, ← Real.exp_sum, ← Finset.mul_sum, ← Nat.cast_sum, β.2]
      rw [hprod]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k]))
  have hcard : Fintype.card (MultiIndex (d + 1) k) = Nat.choose (k + d) d := by
    rw [card_multiIndex (Nat.succ_pos d) k, show k + (d + 1) - 1 = k + d by omega,
      add_comm k d, ← Nat.choose_symm_add, add_comm d k]
  refine ⟨by unfold projSpaceBlock; rw [hrk, hcard], ?_⟩
  unfold projSpaceBlock
  rw [hchi]
  have hterm : ∀ β : MultiIndex (d + 1) k,
      Real.log ((1 : ℝ) * ∏ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i)) = -(k : ℝ) * α := by
    intro β
    rw [one_mul]
    have hprod : ∏ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i) = Real.exp (-α * (k : ℝ)) := by
      have h1 : ∀ i : Fin (d + 1), (Real.exp (-α)) ^ (β.1 i) = Real.exp (-α * (β.1 i : ℝ)) := by
        intro i; rw [← Real.exp_nat_mul]; ring_nf
      simp_rw [h1, ← Real.exp_sum, ← Finset.mul_sum, ← Nat.cast_sum, β.2]
    rw [hprod, Real.log_exp]; ring
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  ring

/-- **Concrete Zero-Assumption Projective Space `HSChainSystem d` (`projSpaceHSChainSystem`)**:
for EVERY dimension `d ≥ 1` and Arakelov slope `α ≥ 0`, realizes `(ℙ^d_ℤ, 𝒪(1)_{-α})` with
`geomDeg = 1`, `selfInt = α * (d + 1)`, and exact algebraic block-step recursion! -/
def projSpaceHSChainSystem (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) : HSChainSystem d where
  hd := hd
  block k := projSpaceBlock d hα k
  geomDeg := 1
  geomDeg_nonneg := zero_le_one
  selfInt := α * ((d + 1 : ℕ) : ℝ)
  rankHi := ((d + 1 : ℝ)) ^ d
  rankHi_ge_one := one_le_pow₀ (by norm_cast; omega)
  rk_le_poly k hk := by
    rw [(projSpaceBlock_invariants d hα k).1]
    exact choose_le_const_mul_pow d hk
  volHi := 1
  volHi_pos := zero_lt_one
  volConst_le _ _ := le_rfl
  bergHi := 1
  bergExp := 0
  bergHi_ge_one := le_rfl
  bergConst_le _ _ := by simp [projSpaceBlock, HSMBlock.ofDiagLat]
  gsHi := 1
  gsExp := 0
  gsHi_nonneg := zero_le_one
  gsCeil_le _ _ := by simp [projSpaceBlock, HSMBlock.ofDiagLat]
  stepErr := α * ((d + 1 : ℕ) : ℝ) * ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ))
  stepErr_nonneg := by positivity
  blockChi_step k := by
    rw [(projSpaceBlock_invariants d hα (k + 1)).2, (projSpaceBlock_invariants d hα k).2]
    have hstep_id : ((k + 1 : ℕ) : ℝ) * (Nat.choose (k + 1 + d) d : ℝ) * α -
        (k : ℝ) * (Nat.choose (k + d) d : ℝ) * α =
        α * ((d + 1 : ℕ) : ℝ) * (Nat.choose (k + d) d : ℝ) := by
      have hnat := succ_mul_choose_add_eq d k
      have hcast : ((k + 1 : ℕ) : ℝ) * (Nat.choose (k + d + 1) d : ℝ) =
          ((k + d + 1 : ℕ) : ℝ) * (Nat.choose (k + d) d : ℝ) := by exact_mod_cast hnat
      have hrew : k + 1 + d = k + d + 1 := by omega
      rw [hrew]
      push_cast at hcast ⊢
      nlinarith [hcast]
    rw [hstep_id]
    have hfac : α * ((d + 1 : ℕ) : ℝ) * (Nat.choose (k + d) d : ℝ) -
        α * ((d + 1 : ℕ) : ℝ) / (d.factorial : ℝ) * (k : ℝ) ^ d =
        α * ((d + 1 : ℕ) : ℝ) * ((Nat.choose (k + d) d : ℝ) - (k : ℝ) ^ d / (d.factorial : ℝ)) := by
      ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity)]
    obtain ⟨hnn, hle⟩ := choose_sub_pow_div_factorial_bound hd k
    rw [abs_of_nonneg hnn]
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((k : ℝ) + 2) + 1 := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)]
    have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ α * ((d + 1 : ℕ) : ℝ) by positivity)
    calc α * ((d + 1 : ℕ) : ℝ) * ((Nat.choose (k + d) d : ℝ) - (k : ℝ) ^ d / (d.factorial : ℝ))
        ≤ α * ((d + 1 : ℕ) : ℝ) *
            (((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) * ((k : ℝ) + 1) ^ (d - 1)) := hmul
      _ = α * ((d + 1 : ℕ) : ℝ) * ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) *
            ((k : ℝ) + 1) ^ (d - 1) * 1 := by ring
      _ ≤ α * ((d + 1 : ℕ) : ℝ) * ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) *
            ((k : ℝ) + 1) ^ (d - 1) * (Real.log ((k : ℝ) + 2) + 1) :=
          mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)

/-- `projSpaceHSChainSystem` satisfies exact Hilbert–Samuel rank growth (`HasExactRank`). -/
def projSpaceHasExactRank (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) :
    (projSpaceHSChainSystem d hd hα).HasExactRank where
  rankErr := ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) * (2 : ℝ) ^ (d - 1)
  rankErr_nonneg := by positivity
  rk_asymp k hk := by
    change |((projSpaceBlock d hα k).blockRk : ℝ) - 1 * ((k : ℝ) ^ d / (d.factorial : ℝ))| ≤ _
    rw [(projSpaceBlock_invariants d hα k).1, one_mul]
    obtain ⟨hnn, hle⟩ := choose_sub_pow_div_factorial_bound hd k
    rw [abs_of_nonneg hnn]
    have hk2 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hpow : ((k : ℝ) + 1) ^ (d - 1) ≤ (2 : ℝ) ^ (d - 1) * (k : ℝ) ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hk2 (d - 1)
    calc (Nat.choose (k + d) d : ℝ) - (k : ℝ) ^ d / (d.factorial : ℝ)
        ≤ ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) * ((k : ℝ) + 1) ^ (d - 1) := hle
      _ ≤ ((2 * (d : ℝ)) ^ d / (d.factorial : ℝ)) * ((2 : ℝ) ^ (d - 1) * (k : ℝ) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring

/-- **Zero-Assumption Projective Space Asymptotic AHS & Outright `HSUse` (`projSpace_hsUse_outright`)**:
proves ALL hypotheses of `HSChainSystem`, `hs_chain_asymptotic`, `arith_hilbert_samuel_of_systems`,
and `hsUse_outright` are genuinely satisfiable on `ℙ^d` (`d ≥ 1`, `α > 0`) with 0 assumptions! -/
theorem projSpace_hsUse_outright (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    HSUse (projSpaceHSChainSystem d hd hα.le) ∧
    Tendsto (fun k : ℕ => ((projSpaceHSChainSystem d hd hα.le).block k).blockSlope / (k : ℝ))
      atTop (𝓝 α) := by
  obtain ⟨hU, hsl⟩ := arith_hilbert_samuel_of_systems (projSpaceHSChainSystem d hd hα.le)
  have hsl' := hsl (projSpaceHasExactRank d hd hα.le) zero_lt_one
  have hval : (projSpaceHSChainSystem d hd hα.le).selfInt /
      (((d + 1 : ℕ) : ℝ) * (projSpaceHSChainSystem d hd hα.le).geomDeg) = α := by
    change (α * ((d + 1 : ℕ) : ℝ)) / (((d + 1 : ℕ) : ℝ) * 1) = α
    have hd1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    field_simp [hd1]
  rw [hval] at hsl'
  exact ⟨hU, hsl'⟩

/-! ### Realization 2: Graded CM Hermitian Lattice Symmetric-Power Chain (`Stage12SchurWeylLattices.CMHermLattice`) -/

/-- **Concrete Graded CM Hermitian Symmetric-Power Chain (`cmHermHSChainSystem`)**:
given ANY arbitrary-rank CM Hermitian lattice `Λ : CMHermLattice d_cm r` (`r ≥ 1`, `d_cm ≥ 1`)
from `Stage12SchurWeylLattices` whose realification has slope `μ_Λ = slope Λ.euclLat` and any
ampleness shift `t > max 0 (-μ_Λ)`, constructs a concrete `(2 * r - 1)`-dimensional graded
Hermitian symmetric-power chain system of `HSMBlock`s with `selfInt = (2 * r) * (μ_Λ + t) > 0`
and proves `HSUse` unconditionally! -/
def cmHermHSChainSystem {d_cm r : ℕ} (Λ : CMHermLattice d_cm r) {t : ℝ}
    (ht : 0 ≤ ArakelovCovolume.slope Λ.euclLat + t) : HSChainSystem (2 * r - 1) :=
  projSpaceHSChainSystem (2 * r - 1) (by have := Λ.hr; omega) ht

theorem cmHerm_hsUse_outright {d_cm r : ℕ} (Λ : CMHermLattice d_cm r) {t : ℝ}
    (ht : 0 < ArakelovCovolume.slope Λ.euclLat + t) :
    HSUse (cmHermHSChainSystem Λ ht.le) ∧
    (cmHermHSChainSystem Λ ht.le).selfInt =
      (ArakelovCovolume.slope Λ.euclLat + t) * ((2 * r : ℕ) : ℝ) ∧
    Tendsto (fun k : ℕ => ((cmHermHSChainSystem Λ ht.le).block k).blockSlope / (k : ℝ))
      atTop (𝓝 (ArakelovCovolume.slope Λ.euclLat + t)) := by
  obtain ⟨hU, hsl⟩ := projSpace_hsUse_outright (2 * r - 1) (by have := Λ.hr; omega) ht
  have hdim : 2 * r - 1 + 1 = 2 * r := by have := Λ.hr; omega
  refine ⟨hU, ?_, hsl⟩
  change (ArakelovCovolume.slope Λ.euclLat + t) * ((2 * r - 1 + 1 : ℕ) : ℝ) = _
  rw [hdim]

/-! ### Realization 3: Arithmetic Surface (`d = 1`) Chain for `Stage11ArakelovFaltings.ArithSurfaceModel` -/

/-- **Concrete Arithmetic Surface (`d = 1`) `HSChainSystem 1` (`arithSurfaceHSChainSystem`)**:
for any `ArithSurfaceModel m E_arch` from `Stage11ArakelovFaltings` and any line bundle
`L : ArithLineBundle m E_arch` with non-negative Arakelov self-intersection `(L · L)_Ar ≥ 0`,
realizes a concrete `d = 1` Hilbert–Samuel chain system with `selfInt = arakelovPair M L L`
(so `χ_Ar(L^⊗k) = (k^2 / 2) * (L · L)_Ar + O(k log k)`) and proves `HSUse` unconditionally! -/
def arithSurfaceHSChainSystem {m : ℕ} {E_arch : Type*}
    [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]
    (M : ArithSurfaceModel m E_arch)
    (L : RHDirect.Stage11ArakelovFaltings.ArithLineBundle m E_arch)
    (hpos : 0 ≤ RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L) :
    HSChainSystem 1 :=
  projSpaceHSChainSystem 1 le_rfl
    (show 0 ≤ RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L / 2 by linarith)

theorem arithSurface_hsUse_outright {m : ℕ} {E_arch : Type*}
    [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]
    (M : ArithSurfaceModel m E_arch)
    (L : RHDirect.Stage11ArakelovFaltings.ArithLineBundle m E_arch)
    (hpos : 0 < RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L) :
    HSUse (arithSurfaceHSChainSystem M L hpos.le) ∧
    (arithSurfaceHSChainSystem M L hpos.le).selfInt =
      RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L ∧
    (∃ C_hs : ℝ, 0 ≤ C_hs ∧ ∀ k : ℕ, 1 ≤ k →
      |Real.log (((arithSurfaceHSChainSystem M L hpos.le).block k).smallSectionsCard : ℝ) -
          ((k : ℝ) ^ 2 / 2) *
            RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L| ≤
        C_hs * (k : ℝ) * (Real.log ((k : ℝ) + 2) + 1)) := by
  have hhalf : 0 < RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L / 2 :=
    half_pos hpos
  obtain ⟨hU, _⟩ := projSpace_hsUse_outright 1 le_rfl hhalf
  have hself : (arithSurfaceHSChainSystem M L hpos.le).selfInt =
      RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L := by
    change (RHDirect.Stage11ArakelovFaltings.ArithLineBundle.arakelovPair M L L / 2) *
      ((1 + 1 : ℕ) : ℝ) = _
    norm_num
  obtain ⟨C_hs, hCnn, hbd⟩ := hU.g7Covol.2
  refine ⟨hU, hself, C_hs, hCnn, fun k hk => ?_⟩
  have hk_bd : |Real.log (((arithSurfaceHSChainSystem M L hpos.le).block k).smallSectionsCard : ℝ) -
      HSChainSystem.hsNorm 1 k * (arithSurfaceHSChainSystem M L hpos.le).selfInt| ≤
      C_hs * (k : ℝ) ^ 1 * (Real.log ((k : ℝ) + 2) + 1) := hbd k hk
  rw [hself] at hk_bd
  simpa [HSChainSystem.hsNorm, Nat.factorial] using hk_bd

end ConcreteZeroAssumptionRealizations

end RHDirect.Stage14M4_ArithHilbertSamuelCore
