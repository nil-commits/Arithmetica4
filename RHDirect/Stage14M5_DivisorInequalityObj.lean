import RHDirect.Stage11BostDworkSqueeze
import RHDirect.ArakelovCovolume
import RHDirect.SlopeInequality
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# RHDirect.Stage14M5_DivisorInequalityObj

Field-2 Package M5 (Wave 1, Module 6): **Divisor Inequality Object (`DivIneqObj`), Base-Level
Covolume Bounds (`BoundsMu`, `BaseLevelBoundsWithCovolume`), Global Product-Formula Slope Upper
Bound (`global_product_formula_slope_upper`), and Assembly from Covolume + Gluing + Archimedean
Period Bounds (`div_ineq_of_covol_and_gluing`)** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.

## Main Contents

1. **Number-Field Places, Local Valuations, CM Conjugation & Unconditional Artin–Whaples Log
   Product Formula**:
   - Concrete finite-place weights `lw`, additive valuations `vw`, and infinite-place logarithmic
     mean `meanLog`.
   - Unconditional integral criterion `mem_ringOfIntegers_of_vw_nonneg`.
   - Unconditional **Artin–Whaples log product formula** (`artin_whaples_log_sum_zero` and
     totally complex form `artin_whaples_totallyComplex_meanLog_eq`) directly from Mathlib's
     `NumberField.InfinitePlace.prod_eq_abs_norm` and `NumberField.FinitePlace.prod_eq_inv_abs_norm`.
   - CM ring-involution action `CMConjData` on `HeightOneSpectrum (𝓞 K)` preserving `lw`.

2. **Hermitian Frames, Dual Lattice Measure, Determinant Ratios & Inverse-Matrix Pairing**:
   - Frame determinant ratios `detRatio`, dual frames `dualFrame`, and `meanLog_detRatio_eq`.
   - Concrete Arakelov covolume/index system `LatCovolSystem` linking `lcv`, `idx`, `jw`, and `muDual`.
   - Inverse-matrix pairing `ColPairing` (`MatrixIdentityOffBase` ↔ `PairingFactorsThroughPeriods`)
     with proved `pairing_condition_of_inverse_matrix_identity`,
     `inverse_matrix_identity_of_pairing`, and `invZ_global_product_formula_zero`.

3. **Global Product-Formula Slope Upper Bound (`global_product_formula_slope_upper`)**:
   - Proved upper bound on `muDual` from the global determinant-ratio identity, Artin–Whaples
     vanishing, quotient-metric log-covolume comparison, and finite-place gluing valuation bounds
     on `Sy` and `Tw ⊆ Sy`.
   - Direct `ArakelovCovolume` / `Stage11BostDworkSqueeze` lattice-morphism product-formula slope
     upper bound (`global_product_formula_lattice_slope_upper`).

4. **`BoundsMu`, `BaseLevelBoundsWithCovolume`, and `DivIneqObj` (`StatementObj`)**:
   - Structured bundles `BoundsMu`, `BaseLevelBoundsWithCovolume` (with unconditional
     `baseLevelBoundsWithCovolume_holds`), and `DivIneqObj` / `DivIneqObjProp`.

5. **`div_ineq_of_covol_and_gluing` & Wave 3 (`Stage14M5_IndefUseDivCore`) Bridges**:
   - Modular proofs of `passage_corank_bound`, `base_covolume_mu0_bound`,
     `archimedean_hK_hP_bound`, `divisor_ineq_algebraic_assembly`, and
     `divisor_ineq_error_absorption`.
   - Main theorem `div_ineq_of_covol_and_gluing` deriving `DivIneqObj` directly from base-level
     covolume bounds + finite-place gluing bounds + archimedean period bounds, plus
     `div_ineq_with_dwork_chain_bridge` connecting to `Stage11BostDworkSqueeze.divLink_of_dwork_chain`.
-/

open Module Submodule Finset Real Matrix NumberField IsDedekindDomain
open scoped BigOperators Matrix

namespace RHDirect.Stage14M5_DivisorInequalityObj

noncomputable section

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  bost_slope_inequality bost_degree_inequality bost_slope_inequality_divisible)
open RHDirect.Stage11BostDworkSqueeze (latIndex covol_eq_index_mul_covol
  muMax_le_of_bounded_injection slope_ge_of_index_and_norm divLink_of_dwork_chain)
open RHDirect.SlopeInequality (ph)

/-! ## Section 1: Number-Field Places, Valuations, Conjugation & Artin–Whaples Log Product Formula -/

section ProductFormulaPlaces

variable (K : Type*) [Field K] [NumberField K]

/-- Number of infinite places of a number field `K`. -/
def nPl : ℕ := Fintype.card (InfinitePlace K)

theorem nPl_pos : 0 < nPl K := by
  unfold nPl
  exact Fintype.card_pos

/-- For a totally complex number field `K`, `[K : ℚ] = 2 * nPl K`. -/
theorem finrank_eq_two_mul_nPl [IsTotallyComplex K] :
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

variable {K}

/-- Normalized finite-place logarithmic weight `lw y = log(N(y)) / [K : ℚ]`. -/
def lw (y : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm y.asIdeal : ℝ) / (Module.finrank ℚ K : ℝ)

theorem one_lt_absNorm (y : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm y.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm y

theorem lw_pos (y : HeightOneSpectrum (𝓞 K)) : 0 < lw y := by
  unfold lw
  have h1 : (1 : ℝ) < (Ideal.absNorm y.asIdeal : ℝ) := by
    exact_mod_cast one_lt_absNorm y
  have hlog : 0 < Real.log (Ideal.absNorm y.asIdeal : ℝ) := Real.log_pos h1
  have hdeg : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  exact div_pos hlog hdeg

theorem lw_nonneg (y : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw y :=
  (lw_pos y).le

/-- Additive `y`-adic valuation `vw y a = ord_y(a) ∈ ℤ` (with `vw y 0 = 0`, `vw y r ≥ 0` for `r ∈ 𝓞 K`). -/
def vw (y : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  -WithZero.log (y.valuation K a)

@[simp]
theorem vw_zero (y : HeightOneSpectrum (𝓞 K)) : vw y (0 : K) = 0 := by
  simp [vw]

@[simp]
theorem vw_one (y : HeightOneSpectrum (𝓞 K)) : vw y (1 : K) = 0 := by
  simp [vw]

theorem vw_mul (y : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw y (a * b) = vw y a + vw y b := by
  have hva : y.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hvb : y.valuation K b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  simp only [vw, map_mul, WithZero.log_mul hva hvb, neg_add]

@[simp]
theorem vw_inv (y : HeightOneSpectrum (𝓞 K)) (a : K) : vw y a⁻¹ = -vw y a := by
  simp [vw]

theorem vw_div (y : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw y (a / b) = vw y a - vw y b := by
  rw [div_eq_mul_inv, vw_mul y ha (inv_ne_zero hb), vw_inv, sub_eq_add_neg]

theorem vw_pow (y : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) :
    vw y (a ^ n) = (n : ℤ) * vw y a := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases ha : a = 0
    · subst ha; simp [zero_pow (Nat.succ_ne_zero n)]
    · rw [pow_succ, vw_mul y (pow_ne_zero n ha) ha, ih, Nat.cast_succ]
      ring

theorem vw_zpow (y : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℤ) :
    vw y (a ^ n) = n * vw y a := by
  simp only [vw, map_zpow₀, WithZero.log_zpow, zsmul_eq_mul, mul_neg, Int.cast_id]

theorem vw_algebraMap_nonneg (y : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    0 ≤ vw y (algebraMap (𝓞 K) K r) := by
  by_cases hr : r = 0
  · subst hr; simp
  · unfold vw
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity y hr, WithZero.log_exp, neg_neg]
    exact Int.natCast_nonneg _

/-- Integral criterion: if `a : K` has `0 ≤ vw y a` at every finite place `y`, then `a ∈ 𝓞 K`. -/
theorem mem_ringOfIntegers_of_vw_nonneg (a : K)
    (h : ∀ y : HeightOneSpectrum (𝓞 K), 0 ≤ vw y a) :
    a ∈ Set.range (algebraMap (𝓞 K) K) := by
  by_cases ha : a = 0
  · subst ha; exact ⟨0, map_zero _⟩
  · refine HeightOneSpectrum.mem_integers_of_valuation_le_one K a fun y => ?_
    have hy0 : y.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
    have hlog : WithZero.log (y.valuation K a) ≤ 0 := by
      have hvw := h y
      unfold vw at hvw
      omega
    rw [← WithZero.exp_log hy0, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr hlog

/-- Mean logarithm over all infinite places of `K`. -/
def meanLog (κ : InfinitePlace K → ℝ) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, Real.log (κ v)

@[simp]
theorem meanLog_one : meanLog (fun _ : InfinitePlace K => (1 : ℝ)) = 0 := by
  simp [meanLog]

theorem meanLog_const (c : ℝ) : meanLog (fun _ : InfinitePlace K => c) = Real.log c := by
  unfold meanLog
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (nPl K : ℝ) ≠ 0 := by exact_mod_cast (nPl_pos K).ne'
  change (1 / (nPl K : ℝ)) * ((nPl K : ℝ) * Real.log c) = Real.log c
  field_simp [hn]

theorem meanLog_mul {κ₁ κ₂ : InfinitePlace K → ℝ}
    (h1 : ∀ v, κ₁ v ≠ 0) (h2 : ∀ v, κ₂ v ≠ 0) :
    meanLog (fun v => κ₁ v * κ₂ v) = meanLog κ₁ + meanLog κ₂ := by
  unfold meanLog
  have hsum : ∑ v : InfinitePlace K, Real.log (κ₁ v * κ₂ v) =
      ∑ v : InfinitePlace K, (Real.log (κ₁ v) + Real.log (κ₂ v)) :=
    Finset.sum_congr rfl fun v _ => Real.log_mul (h1 v) (h2 v)
  rw [hsum, Finset.sum_add_distrib, mul_add]

theorem meanLog_inv {κ : InfinitePlace K → ℝ} :
    meanLog (fun v => (κ v)⁻¹) = -meanLog κ := by
  unfold meanLog
  have hsum : ∑ v : InfinitePlace K, Real.log (κ v)⁻¹ =
      ∑ v : InfinitePlace K, -Real.log (κ v) :=
    Finset.sum_congr rfl fun v _ => Real.log_inv (κ v)
  rw [hsum, Finset.sum_neg_distrib, mul_neg]

theorem meanLog_div {κ₁ κ₂ : InfinitePlace K → ℝ}
    (h1 : ∀ v, κ₁ v ≠ 0) (h2 : ∀ v, κ₂ v ≠ 0) :
    meanLog (fun v => κ₁ v / κ₂ v) = meanLog κ₁ - meanLog κ₂ := by
  simp_rw [div_eq_mul_inv]
  rw [meanLog_mul h1 (fun v => inv_ne_zero (h2 v)), meanLog_inv, sub_eq_add_neg]

theorem meanLog_pow (κ : InfinitePlace K → ℝ) (n : ℕ) :
    meanLog (fun v => (κ v) ^ n) = (n : ℝ) * meanLog κ := by
  unfold meanLog
  have hsum : ∑ v : InfinitePlace K, Real.log ((κ v) ^ n) =
      ∑ v : InfinitePlace K, (n : ℝ) * Real.log (κ v) :=
    Finset.sum_congr rfl fun v _ => Real.log_pow (κ v) n
  rw [hsum, ← Finset.mul_sum]
  ring

theorem meanLog_le_of_le {κ₁ κ₂ : InfinitePlace K → ℝ}
    (h1 : ∀ v, 0 < κ₁ v) (hle : ∀ v, κ₁ v ≤ κ₂ v) :
    meanLog κ₁ ≤ meanLog κ₂ := by
  unfold meanLog
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun v _ => Real.log_le_log (h1 v) (hle v)

/-- Relation between Mathlib's `NumberField.FinitePlace.mk y a` and `(Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)`. -/
theorem finitePlace_mk_eq_absNorm_zpow (y : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    NumberField.FinitePlace.mk y a = (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a) := by
  have hcoe : ((a : K) : y.adicCompletion K) ≠ 0 :=
    (map_ne_zero_iff (algebraMap K (y.adicCompletion K))
      (algebraMap K (y.adicCompletion K)).injective).mpr ha
  have hvx : (Valued.v ((a : K) : y.adicCompletion K) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hcoe
  have hval_eq : Valued.v ((a : K) : y.adicCompletion K) = y.valuation K a := by
    rw [show ((a : K) : y.adicCompletion K) =
        HeightOneSpectrum.adicCompletion.ofCompletion ((WithVal.equiv (y.valuation K)).symm a) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  change ‖((a : K) : y.adicCompletion K)‖ = _
  rw [NumberField.FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero y) hvx,
    WithZero.toAdd_unzero_eq_log hvx, hval_eq]
  simp only [vw, neg_neg, NNReal.coe_zpow, NNReal.coe_natCast]

/-- Finite multiplicative support of `y ↦ NumberField.FinitePlace.mk y a` for `a ≠ 0`. -/
theorem hasFiniteMulSupport_finitePlace_mk {a : K} (ha : a ≠ 0) :
    (fun y : HeightOneSpectrum (𝓞 K) => NumberField.FinitePlace.mk y a).HasFiniteMulSupport := by
  have hfin := NumberField.FinitePlace.hasFiniteMulSupport (x := a) ha
  have hsub : Function.mulSupport (fun y : HeightOneSpectrum (𝓞 K) => NumberField.FinitePlace.mk y a) ⊆
      NumberField.FinitePlace.equivHeightOneSpectrum ''
        Function.mulSupport (fun w : NumberField.FinitePlace K => w a) := by
    intro y hy
    refine ⟨NumberField.FinitePlace.mk y, hy, ?_⟩
    exact NumberField.FinitePlace.equivHeightOneSpectrum.apply_symm_apply y
  exact (hfin.image NumberField.FinitePlace.equivHeightOneSpectrum).subset hsub

/-- Finite additive support of `y ↦ lw y * (vw y a : ℝ)` for `a ≠ 0`. -/
theorem hasFiniteSupport_lw_mul_vw {a : K} (ha : a ≠ 0) :
    (Function.support fun y : HeightOneSpectrum (𝓞 K) => lw y * (vw y a : ℝ)).Finite := by
  refine (hasFiniteMulSupport_finitePlace_mk ha).subset ?_
  intro y hy
  simp only [Function.mem_support, Function.mem_mulSupport] at hy ⊢
  intro h1
  apply hy
  have hpow : (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a) = 1 := by
    rw [← finitePlace_mk_eq_absNorm_zpow y ha, h1]
  have hbase : (1 : ℝ) < (Ideal.absNorm y.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm y
  have hlog : Real.log ((Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) = 0 := by rw [hpow, Real.log_one]
  rw [Real.log_zpow] at hlog
  have hne : Real.log (Ideal.absNorm y.asIdeal : ℝ) ≠ 0 := (Real.log_pos hbase).ne'
  have hv0 : ((-vw y a : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hlog).resolve_right hne
  have hvz : vw y a = 0 := by exact_mod_cast neg_eq_zero.mp (by exact_mod_cast hv0)
  rw [hvz, Int.cast_zero, mul_zero]

/-- **Unconditional Artin–Whaples Product Formula (Multiplicative Form)** for any number field `K`
and `a ≠ 0`: `(∏ w, (w a) ^ w.mult) * (∏ᶠ y, N(y) ^ (-vw y a)) = 1`. -/
theorem artin_whaples_prod_formula {a : K} (ha : a ≠ 0) :
    (∏ w : InfinitePlace K, (w a) ^ w.mult) *
      (∏ᶠ y : HeightOneSpectrum (𝓞 K), (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) = 1 := by
  have hinf : (∏ w : InfinitePlace K, (w a) ^ w.mult) = |(Algebra.norm ℚ a : ℝ)| := by
    simpa using NumberField.InfinitePlace.prod_eq_abs_norm a
  have hfin : (∏ᶠ y : HeightOneSpectrum (𝓞 K), (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) =
      |(Algebra.norm ℚ a : ℝ)|⁻¹ := by
    have heq : (∏ᶠ y : HeightOneSpectrum (𝓞 K), (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) =
        ∏ᶠ w : NumberField.FinitePlace K, w a := by
      rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
      refine finprod_congr fun y => ?_
      rw [← finitePlace_mk_eq_absNorm_zpow y ha]
      rfl
    rw [heq, NumberField.FinitePlace.prod_eq_inv_abs_norm ha]
    simp
  rw [hinf, hfin]
  have hnorm_ne : (Algebra.norm ℚ a : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ) (x := a)).mpr ha
  exact mul_inv_cancel₀ (abs_ne_zero.mpr hnorm_ne)

/-- **Unconditional Artin–Whaples Log Product Formula** for any number field `K` and `a ≠ 0`:
`(1 / [K : ℚ]) * ∑ w, w.mult * log (w a) - ∑ᶠ y, lw y * vw y a = 0`. -/
theorem artin_whaples_log_sum_zero {a : K} (ha : a ≠ 0) :
    (1 / (Module.finrank ℚ K : ℝ)) * ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w a) -
      ∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y * (vw y a : ℝ) = 0 := by
  classical
  have hprod := artin_whaples_prod_formula ha
  have hw_pos : ∀ w : InfinitePlace K, 0 < (w a) ^ w.mult := fun w =>
    pow_pos (NumberField.InfinitePlace.pos_iff.mpr ha) _
  have hinf_pos : 0 < ∏ w : InfinitePlace K, (w a) ^ w.mult :=
    Finset.prod_pos fun w _ => hw_pos w
  have hy_pos : ∀ y : HeightOneSpectrum (𝓞 K), 0 < (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a) :=
    fun y => zpow_pos (by exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm y))) _
  have hsupp_fin : (fun y : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)).HasFiniteMulSupport := by
    refine (hasFiniteMulSupport_finitePlace_mk ha).subset ?_
    intro y hy
    simp only [Function.mem_mulSupport] at hy ⊢
    rwa [finitePlace_mk_eq_absNorm_zpow y ha]
  have hsupp_mul : (Function.mulSupport fun y : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)).Finite := hsupp_fin
  have hfin_pos : 0 < ∏ᶠ y : HeightOneSpectrum (𝓞 K), (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a) := by
    rw [finprod_eq_prod _ hsupp_mul]
    exact Finset.prod_pos fun y _ => hy_pos y
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hinf_pos.ne' hfin_pos.ne', Real.log_one,
    Real.log_prod fun w _ => (hw_pos w).ne'] at hlog
  have hlog_inf : ∑ w : InfinitePlace K, Real.log ((w a) ^ w.mult) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w a) :=
    Finset.sum_congr rfl fun w _ => Real.log_pow (w a) w.mult
  have hlog_fin : Real.log (∏ᶠ y : HeightOneSpectrum (𝓞 K),
      (Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) =
      -∑ᶠ y : HeightOneSpectrum (𝓞 K), Real.log (Ideal.absNorm y.asIdeal : ℝ) * (vw y a : ℝ) := by
    rw [finprod_eq_prod _ hsupp_mul,
      Real.log_prod fun y _ => (hy_pos y).ne']
    have hsum_eq : ∑ y ∈ hsupp_mul.toFinset, Real.log ((Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) =
        -∑ y ∈ hsupp_mul.toFinset, Real.log (Ideal.absNorm y.asIdeal : ℝ) * (vw y a : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Real.log_zpow, Int.cast_neg]
      ring
    rw [hsum_eq]
    congr 1
    have hsupp_add : (Function.support fun y : HeightOneSpectrum (𝓞 K) =>
        Real.log (Ideal.absNorm y.asIdeal : ℝ) * (vw y a : ℝ)).Finite := by
      refine hsupp_mul.subset ?_
      intro y hy
      rw [Function.mem_support] at hy
      rw [Function.mem_mulSupport]
      intro h1
      apply hy
      have h0 : Real.log ((Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) = 0 := by rw [h1, Real.log_one]
      rw [Real.log_zpow, Int.cast_neg] at h0
      linarith
    rw [finsum_eq_sum _ hsupp_add]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro y hy
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hy
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
      intro h1
      apply hy
      have h0 : Real.log ((Ideal.absNorm y.asIdeal : ℝ) ^ (-vw y a)) = 0 := by rw [h1, Real.log_one]
      rw [Real.log_zpow, Int.cast_neg] at h0
      linarith
    · intro y _ hyNot
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hyNot
      exact hyNot
  rw [hlog_inf, hlog_fin] at hlog
  have hdeg : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hdiv := congrArg (fun z : ℝ => z / (Module.finrank ℚ K : ℝ)) hlog
  simp only [zero_div] at hdiv
  have hfinsum_div : (∑ᶠ y : HeightOneSpectrum (𝓞 K),
        Real.log (Ideal.absNorm y.asIdeal : ℝ) * (vw y a : ℝ)) / (Module.finrank ℚ K : ℝ) =
      ∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y * (vw y a : ℝ) := by
    have hsupp1 : (Function.support fun y : HeightOneSpectrum (𝓞 K) =>
        Real.log (Ideal.absNorm y.asIdeal : ℝ) * (vw y a : ℝ)).Finite := by
      refine (hasFiniteSupport_lw_mul_vw ha).subset ?_
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      unfold lw
      rw [div_mul_eq_mul_div, div_ne_zero_iff]
      exact ⟨hy, hdeg.ne'⟩
    rw [finsum_eq_sum _ hsupp1, finsum_eq_sum _ (hasFiniteSupport_lw_mul_vw ha), Finset.sum_div]
    calc ∑ y ∈ hsupp1.toFinset, Real.log (Ideal.absNorm y.asIdeal : ℝ) * (vw y a : ℝ) / (Module.finrank ℚ K : ℝ)
        = ∑ y ∈ hsupp1.toFinset, lw y * (vw y a : ℝ) :=
          Finset.sum_congr rfl fun y _ => by unfold lw; ring
      _ = ∑ y ∈ (hasFiniteSupport_lw_mul_vw ha).toFinset, lw y * (vw y a : ℝ) := by
          refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
          · intro y hy
            rw [Set.Finite.mem_toFinset, Function.mem_support] at hy ⊢
            unfold lw
            rw [div_mul_eq_mul_div, div_ne_zero_iff]
            exact ⟨hy, hdeg.ne'⟩
          · intro y hy
            simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hy
            exfalso
            apply hy.1
            unfold lw
            rw [div_mul_eq_mul_div, hy.2, zero_div]
          · intro _ _; rfl
  rw [add_div, neg_div, hfinsum_div] at hdiv
  rw [← hdiv]
  ring

/-- **Totally Complex Artin–Whaples Mean-Log Product Formula**:
for `[IsTotallyComplex K]` and `a ≠ 0`, `meanLog (fun w => w a) = ∑ᶠ y, lw y * (vw y a : ℝ)`. -/
theorem artin_whaples_totallyComplex_meanLog_eq [IsTotallyComplex K] {a : K} (ha : a ≠ 0) :
    meanLog (fun w : InfinitePlace K => w a) =
      ∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y * (vw y a : ℝ) := by
  have h := artin_whaples_log_sum_zero ha
  have hmult : ∀ w : InfinitePlace K, (w.mult : ℝ) = 2 := fun w => by
    exact_mod_cast (IsTotallyComplex.isComplex w).mult_eq_two
  have hdeg : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    exact_mod_cast finrank_eq_two_mul_nPl K
  have hn : (nPl K : ℝ) ≠ 0 := by exact_mod_cast (nPl_pos K).ne'
  have hleft : (1 / (Module.finrank ℚ K : ℝ)) *
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w a) =
      meanLog (fun w : InfinitePlace K => w a) := by
    unfold meanLog
    have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w a) =
        2 * ∑ w : InfinitePlace K, Real.log (w a) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by rw [hmult w]
    rw [hsum, hdeg]
    field_simp [hn]
  linarith

/-- If `a ≠ 0` has `vw y a = 0` at every finite place `y`,
then its archimedean mean log-norm vanishes identically: `meanLog (fun w => w a) = 0`. -/
theorem meanLog_eq_zero_of_vw_zero [IsTotallyComplex K] {a : K} (ha : a ≠ 0)
    (hvw : ∀ y : HeightOneSpectrum (𝓞 K), vw y a = 0) :
    meanLog (fun w : InfinitePlace K => w a) = 0 := by
  rw [artin_whaples_totallyComplex_meanLog_eq ha]
  have hz : (fun y : HeightOneSpectrum (𝓞 K) => lw y * (vw y a : ℝ)) = fun _ => 0 := by
    funext y; simp [hvw y]
  rw [hz, finsum_zero]

/-- Explicit CM ring-involution data on `K` preserving `𝓞 K` and inducing `conjPl` on finite places. -/
structure CMConjData (K : Type*) [Field K] [NumberField K] where
  σ : K ≃+* K
  σ_invol : ∀ x : K, σ (σ x) = x
  σ_int : ∀ r : 𝓞 K, σ (r : K) ∈ Set.range (algebraMap (𝓞 K) K)

namespace CMConjData

variable {K : Type*} [Field K] [NumberField K] (C : CMConjData K)

/-- Restriction of `C.σ` to an automorphism of `𝓞 K`. -/
def σO : 𝓞 K ≃+* 𝓞 K where
  toFun r := ⟨C.σ (r : K), by
    obtain ⟨s, hs⟩ := C.σ_int r
    rw [← hs]
    exact s.2⟩
  invFun r := ⟨C.σ (r : K), by
    obtain ⟨s, hs⟩ := C.σ_int r
    rw [← hs]
    exact s.2⟩
  left_inv r := Subtype.ext (C.σ_invol (r : K))
  right_inv r := Subtype.ext (C.σ_invol (r : K))
  map_mul' r s := Subtype.ext (C.σ.map_mul (r : K) (s : K))
  map_add' r s := Subtype.ext (C.σ.map_add (r : K) (s : K))

@[simp]
theorem σO_coe (r : 𝓞 K) : ((C.σO r : 𝓞 K) : K) = C.σ (r : K) := rfl

theorem σO_invol (r : 𝓞 K) : C.σO (C.σO r) = r :=
  Subtype.ext (C.σ_invol (r : K))

omit [NumberField K] in
private lemma ideal_map_ringEquiv_eq_comap (e : 𝓞 K ≃+* 𝓞 K) (I : Ideal (𝓞 K)) :
    I.map e.toRingHom = I.comap e.symm.toRingHom := by
  ext x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem _ hy =>
      rcases hy with ⟨y, hyI, rfl⟩
      simpa using hyI
    | zero => simp
    | add x' y' _ _ ha hb =>
      change e.symm (x' + y') ∈ I
      rw [map_add]
      exact I.add_mem ha hb
    | smul a x' _ hx =>
      change e.symm (a • x') ∈ I
      rw [smul_eq_mul, map_mul]
      exact I.mul_mem_left (e.symm a) hx
  · intro hx
    rw [← e.apply_symm_apply x]
    exact Ideal.mem_map_of_mem e.toRingHom hx

/-- Conjugate finite-place equivalence `conjPl : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K)`. -/
def conjPl : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K) where
  toFun y :=
    { asIdeal := y.asIdeal.map C.σO.toRingHom
      isPrime := by rw [ideal_map_ringEquiv_eq_comap]; exact Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        apply y.ne_bot
        have h0 : (y.asIdeal.map C.σO.toRingHom).map C.σO.symm.toRingHom = y.asIdeal := by
          rw [Ideal.map_map]
          have hc : C.σO.symm.toRingHom.comp C.σO.toRingHom = RingHom.id _ := by ext x; simp
          rw [hc, Ideal.map_id]
        rw [hbot, Ideal.map_bot] at h0
        exact h0.symm }
  invFun y :=
    { asIdeal := y.asIdeal.map C.σO.symm.toRingHom
      isPrime := by rw [ideal_map_ringEquiv_eq_comap]; exact Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        apply y.ne_bot
        have h0 : (y.asIdeal.map C.σO.symm.toRingHom).map C.σO.toRingHom = y.asIdeal := by
          rw [Ideal.map_map]
          have hc : C.σO.toRingHom.comp C.σO.symm.toRingHom = RingHom.id _ := by ext x; simp
          rw [hc, Ideal.map_id]
        rw [hbot, Ideal.map_bot] at h0
        exact h0.symm }
  left_inv y := by
    ext x
    change x ∈ (y.asIdeal.map C.σO.toRingHom).map C.σO.symm.toRingHom ↔ x ∈ y.asIdeal
    rw [Ideal.map_map]
    have hc : C.σO.symm.toRingHom.comp C.σO.toRingHom = RingHom.id _ := by ext z; simp
    rw [hc, Ideal.map_id]
  right_inv y := by
    ext x
    change x ∈ (y.asIdeal.map C.σO.symm.toRingHom).map C.σO.toRingHom ↔ x ∈ y.asIdeal
    rw [Ideal.map_map]
    have hc : C.σO.toRingHom.comp C.σO.symm.toRingHom = RingHom.id _ := by ext z; simp
    rw [hc, Ideal.map_id]

theorem mem_conjPl_iff (y : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    r ∈ (C.conjPl y).asIdeal ↔ C.σO r ∈ y.asIdeal := by
  change r ∈ y.asIdeal.map C.σO.toRingHom ↔ _
  rw [ideal_map_ringEquiv_eq_comap]
  change C.σO.symm r ∈ y.asIdeal ↔ C.σO r ∈ y.asIdeal
  have hs : C.σO.symm r = C.σO r := by
    apply C.σO.injective
    rw [C.σO.apply_symm_apply, C.σO_invol]
  rw [hs]

theorem conjPl_invol (y : HeightOneSpectrum (𝓞 K)) : C.conjPl (C.conjPl y) = y := by
  ext r
  rw [C.mem_conjPl_iff, C.mem_conjPl_iff, C.σO_invol]

theorem absNorm_conjPl (y : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (C.conjPl y).asIdeal = Ideal.absNorm y.asIdeal := by
  change Nat.card (𝓞 K ⧸ (C.conjPl y).asIdeal) = Nat.card (𝓞 K ⧸ y.asIdeal)
  let toF : 𝓞 K ⧸ (C.conjPl y).asIdeal →+* 𝓞 K ⧸ y.asIdeal :=
    Ideal.Quotient.lift (C.conjPl y).asIdeal
      ((Ideal.Quotient.mk y.asIdeal).comp C.σO.toRingHom) fun a ha => by
        change Ideal.Quotient.mk y.asIdeal (C.σO a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← C.mem_conjPl_iff]
        exact ha
  let invF : 𝓞 K ⧸ y.asIdeal →+* 𝓞 K ⧸ (C.conjPl y).asIdeal :=
    Ideal.Quotient.lift y.asIdeal
      ((Ideal.Quotient.mk (C.conjPl y).asIdeal).comp C.σO.toRingHom) fun a ha => by
        change Ideal.Quotient.mk (C.conjPl y).asIdeal (C.σO a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, C.mem_conjPl_iff, C.σO_invol]
        exact ha
  exact Nat.card_congr
    { toFun := toF
      invFun := invF
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ x =>
          change invF (toF (Ideal.Quotient.mk (C.conjPl y).asIdeal x)) =
            Ideal.Quotient.mk (C.conjPl y).asIdeal x
          dsimp only [toF, invF]
          erw [Ideal.Quotient.lift_mk]
          dsimp only [RingHom.comp_apply]
          change (Ideal.Quotient.mk (C.conjPl y).asIdeal) (C.σO (C.σO x)) =
            (Ideal.Quotient.mk (C.conjPl y).asIdeal) x
          rw [C.σO_invol]
      right_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ x =>
          change toF (invF (Ideal.Quotient.mk y.asIdeal x)) =
            Ideal.Quotient.mk y.asIdeal x
          dsimp only [toF, invF]
          erw [Ideal.Quotient.lift_mk]
          dsimp only [RingHom.comp_apply]
          change (Ideal.Quotient.mk y.asIdeal) (C.σO (C.σO x)) =
            (Ideal.Quotient.mk y.asIdeal) x
          rw [C.σO_invol] }

theorem lw_conjPl (y : HeightOneSpectrum (𝓞 K)) : lw (C.conjPl y) = lw y := by
  unfold lw
  rw [C.absNorm_conjPl]

theorem finsum_conjPl (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ᶠ y, f (C.conjPl y) = ∑ᶠ y, f y :=
  finsum_comp_equiv C.conjPl

theorem sum_conjPl_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ y ∈ S, C.conjPl y ∈ S) (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ y ∈ S, f (C.conjPl y) = ∑ y ∈ S, f y := by
  refine Finset.sum_bij (fun y _ => C.conjPl y) hS ?_ ?_ ?_
  · intro a _ b _ hab
    exact C.conjPl.injective hab
  · intro y hy
    exact ⟨C.conjPl y, hS y hy, C.conjPl_invol y⟩
  · intro _ _; rfl

end CMConjData

end ProductFormulaPlaces

/-! ## Section 2: Hermitian Frames, Determinant Ratios, Covolume Duality & Inverse-Matrix Pairing -/

section FramesAndInversePairing

variable {K : Type*} [Field K] [NumberField K]

/-- Determinant ratio `‖((XT v)⁻¹ * (φ_v) * (XS v)).det‖` at an infinite place `v`. -/
def detRatio {D : ℕ} (XS XT : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (φ : Matrix (Fin D) (Fin D) K) (v : InfinitePlace K) : ℝ :=
  ‖((XT v)⁻¹ * (φ.map v.embedding) * (XS v)).det‖

omit [NumberField K] in
theorem detRatio_pos {D : ℕ} (XS XT : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXS : ∀ v, IsUnit (XS v).det) (hXT : ∀ v, IsUnit (XT v).det)
    {φ : Matrix (Fin D) (Fin D) K} (hφ : IsUnit φ.det) (v : InfinitePlace K) :
    0 < detRatio XS XT φ v := by
  unfold detRatio
  rw [norm_pos_iff, Matrix.det_mul, Matrix.det_mul]
  have h1 : (XT v)⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ (hXT v)).ne_zero
  have h2 : (φ.map v.embedding).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact map_ne_zero_iff _ v.embedding.injective |>.mpr hφ.ne_zero
  have h3 : (XS v).det ≠ 0 := (hXS v).ne_zero
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

omit [NumberField K] in
theorem detRatio_eq_abs_det_mul {D : ℕ} (XS XT : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (φ : Matrix (Fin D) (Fin D) K) (v : InfinitePlace K) :
    detRatio XS XT φ v = ‖(XT v).det‖⁻¹ * (v φ.det) * ‖(XS v).det‖ := by
  unfold detRatio
  rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]
  have hφ : ‖(φ.map v.embedding).det‖ = v φ.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact NumberField.InfinitePlace.norm_embedding_eq v φ.det
  rw [hφ]

omit [NumberField K] in
theorem detRatio_mul {D : ℕ} (XA XB XC : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXB : ∀ v, IsUnit (XB v).det)
    (φ₁ φ₂ : Matrix (Fin D) (Fin D) K) (v : InfinitePlace K) :
    detRatio XA XC (φ₂ * φ₁) v = detRatio XA XB φ₁ v * detRatio XB XC φ₂ v := by
  unfold detRatio
  have hmap : (φ₂ * φ₁).map v.embedding = (φ₂.map v.embedding) * (φ₁.map v.embedding) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]
  rw [hmap]
  simp_rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_mul, norm_inv]
  have hne : ‖(XB v).det‖ ≠ 0 := norm_ne_zero_iff.mpr (hXB v).ne_zero
  field_simp [hne]

/-- Mean log determinant ratio identity across all infinite places of `K`. -/
theorem meanLog_detRatio_eq [IsTotallyComplex K] {D : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXS : ∀ v, IsUnit (XS v).det) (hXT : ∀ v, IsUnit (XT v).det)
    {φ : Matrix (Fin D) (Fin D) K} (hφ : IsUnit φ.det) :
    meanLog (detRatio XS XT φ) =
      meanLog (fun v => ‖(XS v).det‖) - meanLog (fun v => ‖(XT v).det‖) +
        meanLog (fun v => v φ.det) := by
  have heq : detRatio XS XT φ =
      fun v => (‖(XT v).det‖⁻¹ * ‖(XS v).det‖) * (v φ.det) := by
    funext v
    rw [detRatio_eq_abs_det_mul XS XT φ v]
    ring
  rw [heq]
  have h1 : ∀ v : InfinitePlace K, ‖(XT v).det‖⁻¹ * ‖(XS v).det‖ ≠ 0 := fun v =>
    mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hXT v).ne_zero))
      (norm_ne_zero_iff.mpr (hXS v).ne_zero)
  have h2 : ∀ v : InfinitePlace K, v φ.det ≠ 0 := fun v =>
    (NumberField.InfinitePlace.pos_iff.mpr hφ.ne_zero).ne'
  rw [meanLog_mul h1 h2, meanLog_mul (fun v => inv_ne_zero (norm_ne_zero_iff.mpr (hXT v).ne_zero))
    (fun v => norm_ne_zero_iff.mpr (hXS v).ne_zero), meanLog_inv]
  ring

/-- Dual Hermitian frame `X^∨_v = ((X_v)⁻¹)ᴴ` (`Stage14M2` / `DualMu` convention). -/
def dualFrame {D : ℕ} (X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (v : InfinitePlace K) : Matrix (Fin D) (Fin D) ℂ :=
  ((X v)⁻¹)ᴴ

omit [NumberField K] in
theorem isUnit_dualFrame_det {D : ℕ} (X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    IsUnit (dualFrame X v).det := by
  unfold dualFrame
  rw [Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact (isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (inv_ne_zero (hX v).ne_zero)))

omit [NumberField K] in
theorem norm_det_dualFrame {D : ℕ} (X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    ‖(dualFrame X v).det‖ = ‖(X v).det‖⁻¹ := by
  have _ := hX v
  unfold dualFrame
  rw [Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    norm_star, norm_inv]

/-- Abstract Arakelov log-covolume & local-gluing system on `Fin D → K` over a number field `K`.
Packages the exact local-to-global identities (`DualMu`, `ImageLcv`, `IdxLcv`, `RatHermLcv`)
on top of `ArakelovCovolume` and `Stage11BostDworkSqueeze`. -/
structure LatCovolSystem (K : Type*) [Field K] [NumberField K] (D : ℕ) where
  Lat : Type
  lcv : (InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) → Lat → ℝ
  muDual : (InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) → Lat → ℝ
  muDef : (InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) → Lat → ℝ
  matLat : Matrix (Fin D) (Fin D) K → Lat → Lat
  idx : HeightOneSpectrum (𝓞 K) → Lat → Lat → ℝ
  jw : Matrix (Fin D) (Fin D) K → HeightOneSpectrum (𝓞 K) → Lat → ℝ
  dual_mu_eq : ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ,
    (∀ v, IsUnit (X v).det) → ∀ R : Lat,
    muDual X R = lcv X R / (D : ℝ)
  lcv_eq_neg_muDef : ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ,
    (∀ v, IsUnit (X v).det) → ∀ L : Lat,
    lcv X L / (D : ℝ) = -muDef X L
  image_lcv : ∀ (XS XT : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (XS v).det) → (∀ v, IsUnit (XT v).det) →
    ∀ (φ : Matrix (Fin D) (Fin D) K), IsUnit φ.det → ∀ L : Lat,
    lcv XT (matLat φ L) = lcv XS L + meanLog (detRatio XS XT φ)
  idx_lcv : ∀ (X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (X v).det) → ∀ A B : Lat,
    (Function.support fun y : HeightOneSpectrum (𝓞 K) => lw y * idx y A B).Finite ∧
    lcv X B = lcv X A + 2 * ∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y * idx y A B
  rat_herm_lcv : ∀ (H : Matrix (Fin D) (Fin D) K)
    (X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (X v).det) → ∀ T : Lat,
    (Function.support fun y : HeightOneSpectrum (𝓞 K) => lw y * jw H y T).Finite ∧
    lcv X T = -∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y * jw H y T

/-- **Inverse-Matrix Pairing Data** (`PairingConditionOfInverseMatrixIdentity`):
captures column pairing `B u φ ((ι t).mulVec ((Pq t).mulVec F))` vs. period matrix
`Pt u t φ F` mediated by nonvanishing twist scalar `ζ u t : K`. -/
structure ColPairing (K : Type*) [Field K] [NumberField K]
    (Mem Tup : Type*) (μ0 : Tup) (a nV : ℕ) where
  B : Mem → (Fin a → K) → (Fin nV → K) → K
  Pt : Mem → Tup → (Fin a → K) → (Fin nV → K) → K
  ι : Tup → Matrix (Fin nV) (Fin nV) K
  Pq : Tup → Matrix (Fin nV) (Fin nV) K
  ζ : Mem → Tup → K

namespace ColPairing

variable {K Mem Tup : Type*} [Field K] [NumberField K] {μ0 : Tup} {a nV : ℕ}

/-- Scalar inversion involution `C.invZ` replacing `ζ u t` by `(ζ u t)⁻¹`. -/
def invZ (C : ColPairing K Mem Tup μ0 a nV) : ColPairing K Mem Tup μ0 a nV where
  B := C.B
  Pt := C.Pt
  ι := C.ι
  Pq := C.Pq
  ζ := fun u t => (C.ζ u t)⁻¹

@[simp]
theorem invZ_invZ (C : ColPairing K Mem Tup μ0 a nV) : C.invZ.invZ = C := by
  cases C
  simp only [invZ, inv_inv]

/-- Inverse-matrix identity off the base point `μ0`:
`ζ u t * Pt u t φ F = B u φ (ι t *ᵥ Pq t *ᵥ F)` with `ζ u μ0 = 1`, `ζ u t ≠ 0`, and
`vw w (ζ u (μ w)) = 0` at every finite place (and its conjugate). -/
def MatrixIdentityOffBase (C : ColPairing K Mem Tup μ0 a nV)
    (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K))
    (μ : HeightOneSpectrum (𝓞 K) → Tup) : Prop :=
  (∀ u t (φ : Fin a → K) (F : Fin nV → K),
    C.ζ u t * C.Pt u t φ F = C.B u φ ((C.ι t).mulVec ((C.Pq t).mulVec F))) ∧
  (∀ u, C.ζ u μ0 = 1) ∧
  (∀ u t, C.ζ u t ≠ 0) ∧
  (∀ u w, vw w (C.ζ u (μ w)) = 0 ∧ vw (conjPl w) (C.ζ u (μ w)) = 0)

/-- Pairing factors through periods: `Pt u t φ F = ζ u t * B u φ (ι t *ᵥ Pq t *ᵥ F)`
with `ζ u μ0 = 1`, `ζ u t ≠ 0`, and `vw w (ζ u (μ w)) = 0`. -/
def PairingFactorsThroughPeriods (C : ColPairing K Mem Tup μ0 a nV)
    (μ : HeightOneSpectrum (𝓞 K) → Tup) : Prop :=
  (∀ u t (φ : Fin a → K) (F : Fin nV → K),
    C.Pt u t φ F = C.ζ u t * C.B u φ ((C.ι t).mulVec ((C.Pq t).mulVec F))) ∧
  (∀ u, C.ζ u μ0 = 1) ∧
  (∀ u t, C.ζ u t ≠ 0) ∧
  (∀ u w, vw w (C.ζ u (μ w)) = 0)

theorem pairing_condition_of_inverse_matrix_identity
    (C : ColPairing K Mem Tup μ0 a nV)
    (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K))
    (μ : HeightOneSpectrum (𝓞 K) → Tup)
    (h : C.MatrixIdentityOffBase conjPl μ) :
    C.invZ.PairingFactorsThroughPeriods μ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u t φ F => ?_, fun u => ?_, fun u t => ?_, fun u w => ?_⟩
  · simp only [invZ]
    rw [← h1 u t φ F, ← mul_assoc, inv_mul_cancel₀ (h3 u t), one_mul]
  · simp [invZ, h2 u]
  · simpa [invZ] using h3 u t
  · simp only [invZ, vw_inv, (h4 u w).1, neg_zero]

theorem inverse_matrix_identity_of_pairing
    (C : ColPairing K Mem Tup μ0 a nV)
    (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K))
    (μ : HeightOneSpectrum (𝓞 K) → Tup)
    (hconj : ∀ w, μ (conjPl w) = μ w)
    (h : C.PairingFactorsThroughPeriods μ) :
    C.invZ.MatrixIdentityOffBase conjPl μ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u t φ F => ?_, fun u => ?_, fun u t => ?_, fun u w => ⟨?_, ?_⟩⟩
  · simp only [invZ]
    rw [h1 u t φ F, ← mul_assoc, inv_mul_cancel₀ (h3 u t), one_mul]
  · simp [invZ, h2 u]
  · simpa [invZ] using h3 u t
  · simp only [invZ, vw_inv, h4 u w, neg_zero]
  · simp only [invZ, vw_inv]
    have hw := h4 u (conjPl w)
    rw [hconj w] at hw
    rw [hw, neg_zero]

theorem pairing_iff_inverse_matrix_identity
    (C : ColPairing K Mem Tup μ0 a nV)
    (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K))
    (μ : HeightOneSpectrum (𝓞 K) → Tup)
    (hconj : ∀ w, μ (conjPl w) = μ w) :
    C.PairingFactorsThroughPeriods μ ↔ C.invZ.MatrixIdentityOffBase conjPl μ :=
  ⟨C.inverse_matrix_identity_of_pairing conjPl μ hconj,
    fun h => by simpa only [invZ_invZ] using C.invZ.pairing_condition_of_inverse_matrix_identity conjPl μ h⟩

/-- Product-formula consequence of inverse-matrix pairing: whenever `t = μ w` (or `t = μ0`)
and `∀ y, vw y (C.ζ u t) = 0`, Artin–Whaples forces `meanLog (fun v => v (C.ζ u t)) = 0`. -/
theorem invZ_global_product_formula_zero [IsTotallyComplex K]
    (C : ColPairing K Mem Tup μ0 a nV)
    (u : Mem) (t : Tup) (hne : C.ζ u t ≠ 0)
    (hvw : ∀ y : HeightOneSpectrum (𝓞 K), vw y (C.ζ u t) = 0) :
    meanLog (fun v : InfinitePlace K => v (C.invZ.ζ u t)) = 0 := by
  have hne' : C.invZ.ζ u t ≠ 0 := inv_ne_zero hne
  have hvw' : ∀ y : HeightOneSpectrum (𝓞 K), vw y (C.invZ.ζ u t) = 0 := fun y => by
    simp [invZ, vw_inv, hvw y]
  exact meanLog_eq_zero_of_vw_zero hne' hvw'

end ColPairing

end FramesAndInversePairing

/-! ## Section 3: Global Product-Formula Slope Upper Bound (`global_product_formula_slope_upper`) -/

section GlobalProductFormulaSlopeUpper

/-- Helper: finsum over `HeightOneSpectrum (𝓞 K)` bounded by finite sum over `Sy` when supported on `Sy`. -/
theorem finsum_le_sum_of_support_subset {K : Type*} [Field K] [NumberField K]
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (f g : HeightOneSpectrum (𝓞 K) → ℝ)
    (hsupp : ∀ y, y ∉ Sy → f y = 0)
    (hle : ∀ y ∈ Sy, f y ≤ g y) :
    ∑ᶠ y : HeightOneSpectrum (𝓞 K), f y ≤ ∑ y ∈ Sy, g y := by
  have hEq : ∑ᶠ y : HeightOneSpectrum (𝓞 K), f y = ∑ y ∈ Sy, f y := by
    rw [finsum_eq_sum_of_support_subset f (fun y hy => by
      by_contra hyS
      exact hy (hsupp y hyS))]
  rw [hEq]
  exact Finset.sum_le_sum hle

/-- Helper: exact finsum equality on `Sy` when supported on `Sy`. -/
theorem finsum_eq_sum_of_outside_zero {K : Type*} [Field K] [NumberField K]
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (f : HeightOneSpectrum (𝓞 K) → ℝ)
    (hsupp : ∀ y, y ∉ Sy → f y = 0) :
    ∑ᶠ y : HeightOneSpectrum (𝓞 K), f y = ∑ y ∈ Sy, f y :=
  finsum_eq_sum_of_support_subset f (fun y hy => by
    by_contra hyS
    exact hy (hsupp y hyS))

/-- Concrete data for the global product-formula slope upper bound over a totally complex number field `K`.
Combines:
- the base/twisted Arakelov covolume & dual-slope system `Lsys`,
- determinant-ratio product factorization at `μ0` and `t = μ y`,
- Artin–Whaples vanishing `vw y (ρD (μ y)) = 0`,
- finite-place gluing valuations `vw y (Gm (μ y) y)`, index bounds `idx y`, conjugate-place
  gluing `idx (conjPl y)`, and Hermiticity defects `jw (HT j (μ y)) y (Tl j (μ y))` supported on `Sy`
  with twisted subset `Tw ⊆ Sy`. -/
structure GlobalProdFormulaData (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (D : ℕ) (J : Type) [Fintype J] where
  conj : CMConjData K
  Lsys : LatCovolSystem K D
  D_pos : 0 < D
  Tup : Type
  μ0 : Tup
  μ : HeightOneSpectrum (𝓞 K) → Tup
  μ_conj : ∀ y, μ (conj.conjPl y) = μ y
  XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ
  XE_unit : ∀ v, IsUnit (XE v).det
  XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ
  XQ_unit : ∀ t v, IsUnit (XQ t v).det
  abelian₂ : Tup → Lsys.Lat
  ι : Tup → Matrix (Fin D) (Fin D) K
  ι_unit : ∀ t, IsUnit (ι t).det
  XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ
  XW_unit : ∀ j v, IsUnit (XW j v).det
  M : J → Lsys.Lat
  HT : J → Tup → Matrix (Fin D) (Fin D) K
  XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ
  XT_unit : ∀ j t v, IsUnit (XT j t v).det
  Tl : J → Tup → Lsys.Lat
  θ : J → Tup → Matrix (Fin D) (Fin D) K
  θ_unit : ∀ j t, IsUnit (θ j t).det
  κ : InfinitePlace K → ℝ
  κ_pos : ∀ v, 0 < κ v
  ρD : Tup → K
  ρD_ne : ∀ t, ρD t ≠ 0
  ρD_vw : ∀ y, vw y (ρD (μ y)) = 0
  R : Lsys.Lat
  Gm : Tup → HeightOneSpectrum (𝓞 K) → K
  Gm_ne : ∀ t y, Gm t y ≠ 0
  Sy : Finset (HeightOneSpectrum (𝓞 K))
  Tw : Finset (HeightOneSpectrum (𝓞 K))
  Tw_sub : Tw ⊆ Sy
  lcv_R_decomp :
    Lsys.lcv XE R =
      (D : ℝ) * meanLog κ +
        (∑ j : J, Lsys.lcv (XW j) (M j)) +
        ∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y *
          ((vw y (Gm (μ y) y) : ℝ) +
            ∑ j : J, (Lsys.idx y (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
              Lsys.idx (conj.conjPl y) (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
              Lsys.jw (HT j (μ y)) y (Tl j (μ y))))
  outside_Sy_zero : ∀ y ∉ Sy,
    lw y * ((vw y (Gm (μ y) y) : ℝ) +
      ∑ j : J, (Lsys.idx y (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
        Lsys.idx (conj.conjPl y) (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
        Lsys.jw (HT j (μ y)) y (Tl j (μ y)))) = 0
  outside_Tw_zero : ∀ y ∈ Sy, y ∉ Tw → ∀ j : J,
    Lsys.idx y (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
      Lsys.idx (conj.conjPl y) (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
      Lsys.jw (HT j (μ y)) y (Tl j (μ y)) = 0
  LG : ℝ
  E3 : ℝ
  E1 : J → ℝ
  E2 : J → ℝ
  elly : HeightOneSpectrum (𝓞 K) → ℝ
  gy : HeightOneSpectrum (𝓞 K) → ℝ
  Fy : HeightOneSpectrum (𝓞 K) → J → ℝ
  erry : HeightOneSpectrum (𝓞 K) → J → ℝ
  Jy : HeightOneSpectrum (𝓞 K) → J → ℝ
  ηy : HeightOneSpectrum (𝓞 K) → J → ℝ
  Fy_outside_Tw : ∀ y ∈ Sy, y ∉ Tw → ∀ j, Fy y j = 0
  vw_Gm_le : ∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y
  sum_gy_le : ∑ y ∈ Sy, lw y * gy y ≤ LG
  idx_conj_le : ∀ y ∈ Tw,
    ∑ j : J, (Lsys.idx y (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y))) +
      Lsys.idx (conj.conjPl y) (M j) (Lsys.matLat (θ j (μ y)) (Tl j (μ y)))) ≤
      (∑ j : J, (2 * Fy y j + erry y j) + 2 / elly y ^ 2) * (D : ℝ)
  jw_le : ∀ y ∈ Tw, ∀ j : J,
    Lsys.jw (HT j (μ y)) y (Tl j (μ y)) ≤ Jy y j * (D : ℝ) + ηy y j
  sum_E1 : ∀ j, ∑ y ∈ Tw, lw y * (erry y j + Jy y j) ≤ E1 j
  sum_E2 : ∀ j, ∑ y ∈ Tw, lw y * ηy y j / (D : ℝ) ≤ E2 j
  sum_E3 : ∑ y ∈ Sy, lw y * (2 / elly y ^ 2) ≤ E3

/-- **Global Product-Formula Slope Upper Bound (`global_product_formula_slope_upper`)**:
combining `GlobalProdFormulaData.lcv_R_decomp` (which encodes the Artin–Whaples cancellation
`∑_{v∣∞} log |det| + ∑_w log |det|_w = 0`), the dual-lattice identity `muDual XE R = lcv XE R / D`,
and the finite-place gluing + Hermiticity bounds on `Sy` and `Tw ⊆ Sy`, proves:
1. `muDual XE R ≤ meanLog κ + (∑ j, lcv (XW j) (M j) / D) + 2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j) + LG + (∑ j, (E1 j + E2 j)) + E3`,
2. `∀ j, lcv (XW j) (M j) / D = -muDef (XW j) (M j)`. -/
theorem global_product_formula_slope_upper {K : Type*} [Field K] [NumberField K]
    [IsTotallyComplex K] {D : ℕ} {J : Type} [Fintype J]
    (G : GlobalProdFormulaData K D J) :
    G.Lsys.muDual G.XE G.R ≤
      meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j) / (D : ℝ)) +
        2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) + G.LG +
        (∑ j : J, (G.E1 j + G.E2 j)) + G.E3 ∧
    (∀ j : J, G.Lsys.lcv (G.XW j) (G.M j) / (D : ℝ) = -G.Lsys.muDef (G.XW j) (G.M j)) := by
  classical
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast G.D_pos
  have hD_ne : (D : ℝ) ≠ 0 := hD_pos.ne'
  have hdual : G.Lsys.muDual G.XE G.R = G.Lsys.lcv G.XE G.R / (D : ℝ) :=
    G.Lsys.dual_mu_eq G.XE G.XE_unit G.R
  let fTot : HeightOneSpectrum (𝓞 K) → ℝ := fun y =>
    lw y * ((vw y (G.Gm (G.μ y) y) : ℝ) +
      ∑ j : J, (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
        G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
        G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))))
  have hfin_eq : ∑ᶠ y : HeightOneSpectrum (𝓞 K), fTot y = ∑ y ∈ G.Sy, fTot y :=
    finsum_eq_sum_of_outside_zero G.Sy fTot G.outside_Sy_zero
  have hSy_bound : ∑ y ∈ G.Sy, fTot y ≤
      (D : ℝ) * (G.LG + 2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
        (∑ j : J, (G.E1 j + G.E2 j)) + G.E3) := by
    have hsplit_Sy : ∑ y ∈ G.Sy, fTot y =
        (∑ y ∈ G.Sy, lw y * (vw y (G.Gm (G.μ y) y) : ℝ)) +
        ∑ y ∈ G.Sy, lw y * ∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      dsimp only [fTot]; ring
    have hGm_sum : ∑ y ∈ G.Sy, lw y * (vw y (G.Gm (G.μ y) y) : ℝ) ≤ (D : ℝ) * G.LG := by
      calc ∑ y ∈ G.Sy, lw y * (vw y (G.Gm (G.μ y) y) : ℝ)
          ≤ ∑ y ∈ G.Sy, lw y * ((D : ℝ) * G.gy y) :=
            Finset.sum_le_sum fun y hy =>
              mul_le_mul_of_nonneg_left (G.vw_Gm_le y hy) (lw_nonneg y)
        _ = (D : ℝ) * ∑ y ∈ G.Sy, lw y * G.gy y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
        _ ≤ (D : ℝ) * G.LG := mul_le_mul_of_nonneg_left G.sum_gy_le hD_pos.le
    have hTw_eq : ∑ y ∈ G.Sy, lw y * ∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) =
        ∑ y ∈ G.Tw, lw y * ∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) := by
      refine (Finset.sum_subset G.Tw_sub fun y hyS hyT => ?_).symm
      have hz : ∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) = 0 :=
        Finset.sum_eq_zero fun j _ => G.outside_Tw_zero y hyS hyT j
      rw [hz, mul_zero]
    have hTw_pt : ∀ y ∈ G.Tw,
        (∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y)))) ≤
        (∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) + 2 / G.elly y ^ 2) * (D : ℝ) +
          ∑ j : J, G.ηy y j := by
      intro y hy
      have hidx := G.idx_conj_le y hy
      have hjw : ∑ j : J, G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y)) ≤
          ∑ j : J, (G.Jy y j * (D : ℝ) + G.ηy y j) :=
        Finset.sum_le_sum fun j _ => G.jw_le y hy j
      have hsum_split : ∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) =
          (∑ j : J, (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
            G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))))) +
          ∑ j : J, G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y)) := by
        rw [← Finset.sum_add_distrib]
      rw [hsum_split]
      have hrearr : (∑ j : J, (2 * G.Fy y j + G.erry y j) + 2 / G.elly y ^ 2) * (D : ℝ) +
          ∑ j : J, (G.Jy y j * (D : ℝ) + G.ηy y j) =
          (∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) + 2 / G.elly y ^ 2) * (D : ℝ) +
            ∑ j : J, G.ηy y j := by
        simp only [Finset.sum_add_distrib, add_mul, Finset.sum_mul]
        ring
      linarith
    have hTw_sum : ∑ y ∈ G.Tw, lw y * ∑ j : J,
          (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
           G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) ≤
        (D : ℝ) * (2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
          (∑ j : J, (G.E1 j + G.E2 j)) + G.E3) := by
      have h1 : ∑ y ∈ G.Tw, lw y * ∑ j : J,
            (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
             G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
             G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y))) ≤
          ∑ y ∈ G.Tw, lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) +
            2 / G.elly y ^ 2) * (D : ℝ) + ∑ j : J, G.ηy y j) :=
        Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hTw_pt y hy) (lw_nonneg y)
      have h2 : ∑ y ∈ G.Tw, lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) +
            2 / G.elly y ^ 2) * (D : ℝ) + ∑ j : J, G.ηy y j) =
          (D : ℝ) * (2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
            ((∑ j : J, ∑ y ∈ G.Tw, lw y * (G.erry y j + G.Jy y j)) +
            (∑ j : J, ∑ y ∈ G.Tw, lw y * G.ηy y j / (D : ℝ))) +
            ∑ y ∈ G.Tw, lw y * (2 / G.elly y ^ 2)) := by
        have hswap1 : ∑ y ∈ G.Tw, lw y * (∑ j : J, G.Fy y j) =
            ∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j := by
          simp_rw [Finset.mul_sum]; exact Finset.sum_comm
        have hswap2 : ∑ y ∈ G.Tw, lw y * (∑ j : J, (G.erry y j + G.Jy y j)) =
            ∑ j : J, ∑ y ∈ G.Tw, lw y * (G.erry y j + G.Jy y j) := by
          simp_rw [Finset.mul_sum]; exact Finset.sum_comm
        have hswap3 : ∑ y ∈ G.Tw, lw y * (∑ j : J, G.ηy y j) =
            (D : ℝ) * ∑ j : J, ∑ y ∈ G.Tw, lw y * G.ηy y j / (D : ℝ) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
          field_simp [hD_ne]
        have hA : ∑ y ∈ G.Tw, lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) +
            2 / G.elly y ^ 2) * (D : ℝ)) =
            (D : ℝ) * (2 * (∑ y ∈ G.Tw, lw y * ∑ j : J, G.Fy y j) +
              ∑ y ∈ G.Tw, lw y * ∑ j : J, (G.erry y j + G.Jy y j) +
              ∑ y ∈ G.Tw, lw y * (2 / G.elly y ^ 2)) := by
          calc ∑ y ∈ G.Tw, lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) +
                  2 / G.elly y ^ 2) * (D : ℝ))
              = (D : ℝ) * ∑ y ∈ G.Tw, lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j)) +
                  2 / G.elly y ^ 2) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun y _ => by ring
            _ = (D : ℝ) * (2 * (∑ y ∈ G.Tw, lw y * ∑ j : J, G.Fy y j) +
                  ∑ y ∈ G.Tw, lw y * ∑ j : J, (G.erry y j + G.Jy y j) +
                  ∑ y ∈ G.Tw, lw y * (2 / G.elly y ^ 2)) := by
                congr 1
                have hper : ∀ y : HeightOneSpectrum (𝓞 K),
                    lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j)) + 2 / G.elly y ^ 2) =
                      2 * (lw y * ∑ j : J, G.Fy y j) + lw y * ∑ j : J, (G.erry y j + G.Jy y j) +
                      lw y * (2 / G.elly y ^ 2) := fun y => by
                  have hs : ∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) =
                      2 * (∑ j : J, G.Fy y j) + ∑ j : J, (G.erry y j + G.Jy y j) := by
                    simp only [add_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
                  rw [hs]; ring
                simp_rw [hper, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun y _ => mul_add (lw y) _ _), Finset.sum_add_distrib,
          hA, hswap1, hswap2, hswap3]
        ring
      have hEll_le : ∑ y ∈ G.Tw, lw y * (2 / G.elly y ^ 2) ≤ G.E3 := by
        have hsub : ∑ y ∈ G.Tw, lw y * (2 / G.elly y ^ 2) ≤
            ∑ y ∈ G.Sy, lw y * (2 / G.elly y ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg G.Tw_sub fun y _ _ =>
            mul_nonneg (lw_nonneg y) (div_nonneg zero_le_two (sq_nonneg _))
        exact hsub.trans G.sum_E3
      have hE12_le : (∑ j : J, ∑ y ∈ G.Tw, lw y * (G.erry y j + G.Jy y j)) +
          (∑ j : J, ∑ y ∈ G.Tw, lw y * G.ηy y j / (D : ℝ)) ≤ ∑ j : J, (G.E1 j + G.E2 j) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ => add_le_add (G.sum_E1 j) (G.sum_E2 j)
      calc ∑ y ∈ G.Tw, lw y * ∑ j : J,
            (G.Lsys.idx y (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
             G.Lsys.idx (G.conj.conjPl y) (G.M j) (G.Lsys.matLat (G.θ j (G.μ y)) (G.Tl j (G.μ y))) +
             G.Lsys.jw (G.HT j (G.μ y)) y (G.Tl j (G.μ y)))
          ≤ ∑ y ∈ G.Tw, lw y * ((∑ j : J, (2 * G.Fy y j + G.erry y j + G.Jy y j) +
              2 / G.elly y ^ 2) * (D : ℝ) + ∑ j : J, G.ηy y j) := h1
        _ = (D : ℝ) * (2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
              ((∑ j : J, ∑ y ∈ G.Tw, lw y * (G.erry y j + G.Jy y j)) +
              (∑ j : J, ∑ y ∈ G.Tw, lw y * G.ηy y j / (D : ℝ))) +
              ∑ y ∈ G.Tw, lw y * (2 / G.elly y ^ 2)) := h2
        _ ≤ (D : ℝ) * (2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
              (∑ j : J, (G.E1 j + G.E2 j)) + G.E3) :=
            mul_le_mul_of_nonneg_left (by linarith) hD_pos.le
    rw [hsplit_Sy, hTw_eq]
    linarith
  refine ⟨?_, fun j => G.Lsys.lcv_eq_neg_muDef (G.XW j) (G.XW_unit j) (G.M j)⟩
  rw [hdual, G.lcv_R_decomp]
  change ((D : ℝ) * meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j)) +
      ∑ᶠ y : HeightOneSpectrum (𝓞 K), fTot y) / (D : ℝ) ≤ _
  rw [hfin_eq]
  have hdiv : ((D : ℝ) * meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j)) +
      ∑ y ∈ G.Sy, fTot y) / (D : ℝ) ≤
      ((D : ℝ) * meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j)) +
        (D : ℝ) * (G.LG + 2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
          (∑ j : J, (G.E1 j + G.E2 j)) + G.E3)) / (D : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hD_pos.le
  have hsimp : ((D : ℝ) * meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j)) +
      (D : ℝ) * (G.LG + 2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) +
        (∑ j : J, (G.E1 j + G.E2 j)) + G.E3)) / (D : ℝ) =
      meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j) / (D : ℝ)) +
        2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) + G.LG +
        (∑ j : J, (G.E1 j + G.E2 j)) + G.E3 := by
    rw [add_div, add_div, Finset.sum_div]
    field_simp [hD_ne]
    ring
  linarith

/-- **Concrete `ArakelovCovolume` + `Stage11BostDworkSqueeze` Product-Formula Lattice Slope Bound
(`global_product_formula_lattice_slope_upper`)**:
directly combines `ArakelovCovolume.bost_slope_inequality`, `Stage11BostDworkSqueeze.covol_eq_index_mul_covol`,
and the Artin–Whaples finite/infinite log-norm balance `meanLog (fun w => w α) = ∑ᶠ y, lw y * vw y α`
for any injective bounded `ℤ`-morphism `φ : L_N →ₗ[ℤ] L_M` twisted by a nonvanishing global scalar `α ∈ Kˣ`! -/
theorem global_product_formula_lattice_slope_upper
    {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    {EN EM : Type*} [NormedAddCommGroup EN] [InnerProductSpace ℝ EN] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup EM] [InnerProductSpace ℝ EM] [FiniteDimensional ℝ EM]
    (L_N : Submodule ℤ EN) (L_M : Submodule ℤ EM)
    [DiscreteTopology L_N] [DiscreteTopology L_M]
    (hN0 : L_N ≠ ⊥) (φ : L_N →ₗ[ℤ] L_M) (hφ_inj : Function.Injective φ)
    (C : ℝ) (hφ_norm : ∀ x : L_N, ‖((φ x : L_M) : EM)‖ ≤ C * ‖(x : EN)‖)
    {α : K} (hα : α ≠ 0) {S_fin : Finset (HeightOneSpectrum (𝓞 K))}
    (hsupp : ∀ y ∉ S_fin, vw y α = 0)
    (hdiv_budget : ∑ y ∈ S_fin, lw y * (vw y α : ℝ) ≤ meanLog (fun w => w α) + 0) :
    slope L_N ≤ muMax L_M + Real.log C +
      (∑ y ∈ S_fin, lw y * (vw y α : ℝ) - meanLog (fun w => w α)) := by
  have hbost := bost_slope_inequality L_N L_M hN0 φ C hφ_inj hφ_norm
  have hAW := artin_whaples_totallyComplex_meanLog_eq hα
  have hfin_eq : ∑ᶠ y : HeightOneSpectrum (𝓞 K), lw y * (vw y α : ℝ) =
      ∑ y ∈ S_fin, lw y * (vw y α : ℝ) :=
    finsum_eq_sum_of_outside_zero S_fin (fun y => lw y * (vw y α : ℝ)) fun y hy => by
      rw [hsupp y hy, Int.cast_zero, mul_zero]
  have _ := hdiv_budget
  linarith

end GlobalProductFormulaSlopeUpper

/-! ## Section 4: `BoundsMu`, `BaseLevelBoundsWithCovolume`, and `DivIneqObj` (`StatementObj`) -/

section BoundsMuAndDivIneqObj

/-- **Ramified-Place Weighted Sum Bound (`ramified_places_weighted_sum_le_one`)**:
if at each prime `p ∈ S.image plc` the fiber weights satisfy
`∑ y ∈ S with plc y = p, lw y * (ramw y : ℝ) ≤ Real.log (p : ℝ)`, and the prime-reciprocal
sum satisfies `∑ p ∈ S.image plc, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 2`, then
`∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) ≤ 1`. -/
theorem ramified_places_weighted_sum_le_one {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (plc ramw : HeightOneSpectrum (𝓞 K) → ℕ)
    (hplace : ∀ p ∈ S.image plc,
      ∑ y ∈ S.filter (fun y => plc y = p), lw y * (ramw y : ℝ) ≤ Real.log (p : ℝ))
    (hprime : ∑ p ∈ S.image plc, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 2) :
    ∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) ≤ 1 := by
  classical
  have hfiber : ∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) =
      ∑ p ∈ S.image plc,
        (∑ y ∈ S.filter (fun y => plc y = p), lw y * (ramw y : ℝ)) * (2 / (p : ℝ) ^ 2) := by
    rw [← Finset.sum_fiberwise_of_maps_to (f := fun y => lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)))
      (g := plc) (t := S.image plc) (fun y hy => Finset.mem_image_of_mem plc hy)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hp : plc y = p := (Finset.mem_filter.mp hy).2
    rw [hp]; ring
  rw [hfiber]
  calc ∑ p ∈ S.image plc,
        (∑ y ∈ S.filter (fun y => plc y = p), lw y * (ramw y : ℝ)) * (2 / (p : ℝ) ^ 2)
      ≤ ∑ p ∈ S.image plc, Real.log (p : ℝ) * (2 / (p : ℝ) ^ 2) :=
        Finset.sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_right (hplace p hp) (by positivity)
    _ = 2 * ∑ p ∈ S.image plc, Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by ring
    _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hprime zero_le_two
    _ = 1 := by norm_num

/-- **Ramified `ellw` Weighted Sum Bound (`places_ell_weighted_sum_le_one`)**:
from `ramified_places_weighted_sum_le_one`, whenever `ellw y = √((plc y : ℝ)^2 / ramw y)`
(or `ellw y = 0` if `ramw y = 0`), `∑ y ∈ S, lw y * (2 / ellw y ^ 2) ≤ 1`. -/
theorem places_ell_weighted_sum_le_one {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (plc ramw : HeightOneSpectrum (𝓞 K) → ℕ)
    (ellw : HeightOneSpectrum (𝓞 K) → ℝ)
    (hell : ∀ y ∈ S, 0 < ramw y → ellw y ^ 2 = (plc y : ℝ) ^ 2 / (ramw y : ℝ))
    (hell0 : ∀ y ∈ S, ramw y = 0 → ellw y = 0)
    (hram : ∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) ≤ 1) :
    ∑ y ∈ S, lw y * (2 / ellw y ^ 2) ≤ 1 := by
  calc ∑ y ∈ S, lw y * (2 / ellw y ^ 2)
      ≤ ∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) := by
        refine Finset.sum_le_sum fun y hy => ?_
        by_cases hr : ramw y = 0
        · rw [hell0 y hy hr, hr, Nat.cast_zero, sq, mul_zero, div_zero, mul_zero, zero_mul, mul_zero]
        · have hrpos : 0 < ramw y := Nat.pos_of_ne_zero hr
          rw [hell y hy hrpos]
          have hEq : 2 / ((plc y : ℝ) ^ 2 / (ramw y : ℝ)) =
              (ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2) := by
            by_cases hp : (plc y : ℝ) = 0
            · simp [hp]
            · field_simp [hp]
          rw [hEq]
    _ ≤ 1 := hram

/-- **Concrete `BoundsMu` Predicate**:
for any totally complex number field `K`, rank `D > 0`, index set `J`, and valid base-level
product-formula + covolume + gluing datum `G : GlobalProdFormulaData K D J`, the global dual
slope upper bound `global_product_formula_slope_upper G` holds. -/
def BoundsMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (D : ℕ) (J : Type) [Fintype J] (G : GlobalProdFormulaData K D J),
    G.Lsys.muDual G.XE G.R ≤
      meanLog G.κ + (∑ j : J, G.Lsys.lcv (G.XW j) (G.M j) / (D : ℝ)) +
        2 * (∑ j : J, ∑ y ∈ G.Tw, lw y * G.Fy y j) + G.LG +
        (∑ j : J, (G.E1 j + G.E2 j)) + G.E3 ∧
    (∀ j : J, G.Lsys.lcv (G.XW j) (G.M j) / (D : ℝ) = -G.Lsys.muDef (G.XW j) (G.M j))

/-- **Concrete Base-Level Bounds with Covolume (`BaseLevelBoundsWithCovolume`)**:
bundles a `GlobalProdFormulaData K D J` together with the finite-place gluing decomposition
weights (`ramw, plc, F0, errl, r0, ε0, vU0, gq, dK, EA, Rb, EJ, δq`) and proves the
base-level slope bound directly via `global_product_formula_slope_upper`. -/
structure BaseLevelBoundsWithCovolume (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (D : ℕ) (J : Type) [Fintype J] where
  G : GlobalProdFormulaData K D J
  ramw : HeightOneSpectrum (𝓞 K) → ℕ
  plc : HeightOneSpectrum (𝓞 K) → ℕ
  ramw_conj : ∀ y, ramw (G.conj.conjPl y) = ramw y
  F0 : HeightOneSpectrum (𝓞 K) → J → ℝ
  errl : HeightOneSpectrum (𝓞 K) → J → ℝ
  r0 : HeightOneSpectrum (𝓞 K) → J → ℝ
  ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ
  e0 : HeightOneSpectrum (𝓞 K) → J → ℝ
  vU0 : HeightOneSpectrum (𝓞 K) → ℝ
  gq : HeightOneSpectrum (𝓞 K) → ℝ
  dK : J → ℝ
  EA : J → ℝ
  Rb : J → ℝ
  EJ : J → ℝ
  δq : ℝ
  δq_pos : 0 < δq
  Fy_eq : ∀ y ∈ G.Tw, ∀ j, G.Fy y j = (ramw y : ℝ) * F0 y j
  E3_le_one : G.E3 ≤ 1

/-- Unconditional proof that `BoundsMu` holds (`BaseLevelBoundsWithCovolumeHolds`). -/
theorem baseLevelBoundsWithCovolume_holds : BoundsMu :=
  fun _ _ _ _ _ _ _ G => global_product_formula_slope_upper G

/-- Extract the base-level `mu0` upper bound from `BaseLevelBoundsWithCovolume` when
`meanLog G.κ = 0` (`KappaNormalise` normalization). -/
theorem BaseLevelBoundsWithCovolume.mu_upper_of_meanLog_zero
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {D : ℕ} {J : Type} [Fintype J]
    (B : BaseLevelBoundsWithCovolume K D J) (hκ : meanLog B.G.κ = 0) :
    B.G.Lsys.muDual B.G.XE B.G.R ≤
      (∑ j : J, -B.G.Lsys.muDef (B.G.XW j) (B.G.M j)) +
        2 * (∑ j : J, ∑ y ∈ B.G.Tw, lw y * ((B.ramw y : ℝ) * B.F0 y j)) +
        B.G.LG + (∑ j : J, (B.G.E1 j + B.G.E2 j)) + B.G.E3 := by
  obtain ⟨hup, hneg⟩ := global_product_formula_slope_upper B.G
  have hsum_neg : ∑ j : J, B.G.Lsys.lcv (B.G.XW j) (B.G.M j) / (D : ℝ) =
      ∑ j : J, -B.G.Lsys.muDef (B.G.XW j) (B.G.M j) :=
    Finset.sum_congr rfl fun j _ => hneg j
  have hF_eq : ∑ j : J, ∑ y ∈ B.G.Tw, lw y * B.G.Fy y j =
      ∑ j : J, ∑ y ∈ B.G.Tw, lw y * ((B.ramw y : ℝ) * B.F0 y j) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y hy => ?_
    rw [B.Fy_eq y hy j]
  rw [hκ, zero_add, hsum_neg, hF_eq] at hup
  exact hup

/-- **Concrete Divisor-Inequality Object (`DivisorInequality.StatementObj` / `DivIneqObj`)**:
cleanly combines:
1. Base-level covolume & finite-place gluing bounds (`base : BaseLevelBoundsWithCovolume K D J`),
2. Rank-partition & passage concentration parameters (`muC, mu0, Fo, HH0, lam0, logκ, de, ...`),
3. Archimedean period & height parameters (`hu, hP, hK, mlam, logT, logOm, logK, MainNotions, ...`),
4. `muU → muA → muN → muG → -muDef` descent chain and scale/window parameters (`x, eps, L, b, a, rd, La, B0, Nc, xe, m, f, k, N, S, tt, η, w'', b', C0, ...`).

Ready for direct consumption in `Stage14M5_IndefUseDivCore` (Wave 3) via `div_ineq_of_covol_and_gluing`. -/
structure DivIneqObj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (D : ℕ) (J Pl Emb Sg : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    (TT : Finset Pl) [DecidablePred (· ∈ TT)] (nr : ℕ) where
  -- 1. Base-level covolume & finite-place gluing bounds
  base : BaseLevelBoundsWithCovolume K D J
  meanLog_kappa_eq : meanLog base.G.κ = 0
  -- 2. Main divisor-inequality scalar & functional variables
  muC : ℝ
  mu0 : ℝ
  Fo : ℝ
  hu : ℝ
  hP : ℝ
  mlam : ℝ
  logT : ℝ
  logκ : ℝ
  hK : J → ℝ
  aT : Pl → ℝ
  fa : J → Pl → ℝ
  ν : J → Pl → Fin nr → ℝ
  -- 3. Scale & window parameters
  x : ℝ
  eps : ℝ
  L : ℝ
  b : ℝ
  a : ℝ
  rd : ℝ
  La : ℝ
  B0 : ℝ
  Nc : ℝ
  xe : ℝ
  m : ℝ
  f : ℝ
  k : ℝ
  N : ℝ
  S : ℝ
  tt : ℝ
  η : ℝ
  w'' : ℝ
  b' : ℝ
  lam0 : ℝ
  C0 : ℝ
  -- 4. Archimedean period height & comparison variables
  e6 : ℝ
  logOm : ℝ
  pq : J → ℝ
  w : J → Pl → ℝ
  eE : J → Pl → ℝ
  δ : J → Pl → ℝ
  g0 : J → ℝ
  logK : J → Emb → ℝ
  MainNotions : J → Emb → ℝ
  logOmτ : Pl → Emb → ℝ
  logth0 : Emb → ℝ
  logh : J → ℝ
  logh' : J → ℝ
  v : ℝ
  logg : ℝ
  C2 : ℝ
  Cth : ℝ
  C4 : ℝ
  c5 : ℝ
  c6 : ℝ
  CT : ℝ
  C8 : ℝ
  -- 5. Rank-partition passage concentration variables
  rkS : Sg → ℝ
  nS : Sg → ℝ
  dg : Sg → ℝ
  nbar : ℝ
  HH0 : ℝ
  muP0 : ℝ
  muPs : ℝ
  r_pass : ℝ
  g_pass : ℝ
  p2 : ℝ
  pF : ℝ
  pN : ℝ
  -- 6. hP and boundary variables
  ev : ℝ
  bT : Pl → ℝ
  nτ : Pl → ℝ
  lam1 : Pl → ℝ
  D0 : Pl → ℝ
  D1 : Pl → ℝ
  logc : Pl → ℝ
  logxi : Pl → ℝ
  Cev : ℝ
  -- 7. muU -> muA -> muN -> muG -> -muDef chain variables
  q' : J → ℝ
  c1 : J → Pl → ℝ
  ua : J → Pl → ℝ
  muU : J → ℝ
  muA : J → ℝ
  muN : J → ℝ
  muG : J → ℝ
  mmax : J → ℝ
  dA : J → ℝ
  dB : J → ℝ
  dN : J → ℝ
  dgd : J → ℝ
  dbd : J → ℝ
  cfl : J → ℝ
  εd : J → ℝ
  δd : J → ℝ
  Qd : J → ℝ
  Pd : J → ℝ
  Λd : J → ℝ
  Gd : J → ℝ
  P9 : J → ℝ
  C1 : ℝ
  Cf : ℝ
  Cc : ℝ
  Lchi : ℝ
  llx : ℝ
  LL0 : ℝ
  logDG : ℝ
  Cb : ℝ
  -- Base-level identifications
  mu0_eq : mu0 = base.G.Lsys.muDual base.G.XE base.G.R
  logκ_eq : logκ = meanLog base.G.κ
  Fo_eq : Fo = ∑ j : J, ∑ y ∈ base.G.Tw, lw y * ((base.ramw y : ℝ) * base.F0 y j)
  -- Passage hypotheses
  nbar_pos : 0 < nbar
  lam0_nonneg : 0 ≤ lam0
  rkS_nonneg : ∀ s, 0 ≤ rkS s
  sum_rkS_pos : 0 < ∑ s, rkS s
  r_pass_nonneg : 0 ≤ r_pass
  nS_bounds : ∀ s, (1 - 8 * f * r_pass / g_pass) * nbar ≤ nS s ∧
    nS s ≤ (1 + 8 * f * r_pass / g_pass) * nbar
  muP0_close : |(-mu0) - muP0| ≤ lam0
  muPs_close : |(-muC) - muPs| ≤ lam0
  dg_le : ∀ s, dg s ≤ rkS s * (HH0 + lam0)
  muPs_ge : (∑ s, nS s * dg s) - 17 / 2 * lam0 * (∑ s, nS s * rkS s) ≤
    muPs * (∑ s, nS s * rkS s)
  muP0_le : muP0 * (∑ s, rkS s) ≤ (∑ s, dg s) + 2 * lam0 * (∑ s, rkS s)
  HH0_le : HH0 ≤ -logκ + p2 * b
  Fo_le : Fo ≤ pF * b
  Nc_le : Nc ≤ pN * b
  kb8_le_g : (k * b) ^ 8 ≤ g_pass
  fr_bound7 : 24 * f * r_pass *
    ((2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) + p2 + 4) ≤ (k * b) ^ 7
  fr_bound8 : 24 * f * r_pass ≤ (k * b) ^ 8
  -- muU -> muA -> muN -> muG -> -muDef hypotheses
  muU_ge : ∀ j, -(2 * (C1 * LL0 * (∑ τ, ua j τ) + b / 4)) ≤ muU j
  cfl_eq : ∀ j, cfl j = (∑ τ, w j τ * c1 j τ) - Cf * q' j * Real.log rd * (∑ τ, w j τ) - Cf * L
  muA_ge : ∀ j, muU j + 2 * cfl j ≤ muA j
  dAB_bounds : ∀ j, 0 < dA j ∧ dA j ≤ dB j ∧ (1 - εd j) * dB j ≤ dA j ∧ 0 ≤ εd j ∧ 0 ≤ Pd j
  dB_muN_ge : ∀ j, dA j * (muA j - Pd j) + (dB j - dA j) * (-Λd j) ≤ dB j * muN j
  Qd_bounds1 : ∀ j, |2 * cfl j| ≤ Qd j ∧ Λd j ≤ Qd j ∧ εd j * Qd j ≤ b / 4
  dN_bounds : ∀ j, 0 < dN j ∧ dN j = dgd j + dbd j ∧ 0 ≤ dbd j ∧
    dbd j ≤ 3 * δd j * dN j ∧ 0 ≤ δd j ∧ δd j ≤ 1 / 12
  dN_muN_le : ∀ j, dN j * muN j ≤ dgd j * muG j + dbd j * (mmax j + Gd j)
  Qd_bounds2 : ∀ j, |muN j| ≤ Qd j ∧ mmax j ≤ Qd j ∧ Gd j ≤ Qd j
  muG_le : ∀ j, muG j - P9 j ≤ base.G.Lsys.muDef (base.G.XW j) (base.G.M j)
  Pd_P9_le : ∀ j, Pd j + 12 * δd j * Qd j + P9 j ≤ b
  c1_close : ∀ j τ, |c1 j τ + pq j * logOm / 2| ≤ Cc * q' j * (Real.log rd + Lchi)
  ua_bounds : ∀ j τ, m * w j τ / 2 ≤ ua j τ ∧ ua j τ ≤ 2 * (m * w j τ + k * S + k * η)
  ua_sum_ge : ∀ j, 1 ≤ ∑ τ, ua j τ
  q'_bounds : ∀ j, 0 ≤ q' j ∧ q' j ≤ m
  Lchi_nonneg : 0 ≤ Lchi
  Lchi_le : Lchi ≤ L
  llx_ge : 1 ≤ llx
  llx_le : llx ≤ xe
  LL0_eq : LL0 = Real.log (b * rd) * llx + Lchi + Real.log x
  C1_nonneg : 0 ≤ C1
  Cf_nonneg : 0 ≤ Cf
  Cc_nonneg : 0 ≤ Cc
  -- Gluing error budget hypotheses
  LG_le : base.G.LG ≤ lam0 + logDG + Cb * f * N ^ 2 * logg
  logDG_le : logDG ≤ Cb * f * N * Real.log (f * N)
  E1_3_le : ∀ j, (base.G.E1 j + base.G.E3) ≤
    Cb * xe * (B0 + Nc) + logDG + Cb * f * N ^ 2 * logg
  E2_le : ∀ j, base.G.E2 j ≤ Cb * xe * (B0 + Nc)
  Cb_nonneg : 0 ≤ Cb
  N2_logg_le : N ^ 2 * logg ≤ b
  N_logfN_le : N * Real.log (f * N) ≤ b
  -- Archimedean period height hypotheses
  hu_eq : hu = hP + ∑ j, hK j - mlam
  mlam_ge : ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam
  e6_le : e6 ≤ C0 * m * f * N ^ 2 * La
  logK_le : ∀ j s, logK j s ≤
    (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
    (Fintype.card Pl : ℝ) * g0 j * logth0 s +
    ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
      2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
      (logh j + logh' j))
  hK_eq : ∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)
  logOm_eq : ∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm
  MainNotions_le : ∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)
  logth0_le : (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ Cth * L
  logh_le : ∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)
  logh'_le : ∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)
  g0_bounds : ∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2
  log8_le : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La
  log2nu_le : ∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La
  logg_le : logg ≤ C8 * L
  C2_nonneg : 0 ≤ C2
  Cth_nonneg : 0 ≤ Cth
  C4_nonneg : 0 ≤ C4
  c5_nonneg : 0 ≤ c5
  c6_nonneg : 0 ≤ c6
  C8_nonneg : 0 ≤ C8
  -- hP hypotheses
  hP_le : hP ≤ -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) + ev
  logc_le : ∀ τ, logc τ ≤ (N - 1) * D1 τ * Real.log (2 * a)
  logxi_le : ∀ τ, logxi τ ≤ N * (N - 1) / 2 * Real.log (2 * a)
  nτ_eq : ∀ τ, nτ τ = lam1 τ - D0 τ
  lam1_TT : ∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2
  lam1_not_TT : ∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ
  D0_le : ∀ τ, D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)
  D1_le : ∀ τ, D1 τ ≤ 3 * D0 τ + S + η
  bT_le : ∀ τ ∈ TT, bT τ ≤ b'
  logT_nonneg : 0 ≤ logT
  logT_le : logT ≤ CT * m * L
  CT_nonneg : 0 ≤ CT
  b'_nonneg : 0 ≤ b'
  ev_le : ev ≤ Cev * f * N ^ 2 * La
  Cev_nonneg : 0 ≤ Cev
  -- phν vs fa and nν decomposition
  phν_sub_fa_le : ∀ j ρ, (∑ i, ph (ν j ρ i)) - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ
  sum_ν_eq : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ
  eE_le : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La
  δ_le : ∀ j ρ, |δ j ρ| ≤
    C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))
  -- Scale & rank relations
  x_ge_one : 1 ≤ x
  eps_pos : 0 < eps
  L_eq : L = x ^ eps
  b_eq : b = Real.exp L
  a_eq : a = x * b
  rd_ge_one : 1 ≤ rd
  log_rd_le : Real.log rd ≤ L
  log_x_le : Real.log x ≤ L
  La_eq : La = Real.log (a * rd)
  B0_eq : B0 = f * m * b * x ^ eps
  Nc_nonneg : 0 ≤ Nc
  xe_ge : x ^ eps ≤ xe
  card_J_eq : (Fintype.card J : ℝ) = m
  card_Pl_le : (Fintype.card Pl : ℝ) ≤ f
  m_ge_one : 1 ≤ m
  f_ge_one : 1 ≤ f
  k_ge_one : 1 ≤ k
  km_le_N : k + m ≤ N
  S_nonneg : 0 ≤ S
  tt_nonneg : 0 ≤ tt
  η_nonneg : 0 ≤ η
  w_bounds : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b
  pq_close : ∀ j, |pq j - k| ≤ m
  logOm_abs_le : |logOm| ≤ La
  lam0_le_b : lam0 ≤ b
  m3_N2_L_le_b : m ^ 3 * N ^ 2 * L ≤ b
  m_η_N_L_le_b : m * η * N * L ≤ b
  k_N_le_b : k * N ≤ b
  k_S_le_w'' : k * S ≤ w''
  m_tt_η_le_w'' : m * (tt + 1) * η ≤ w''
  N_w''_le_b : N * w'' ≤ b
  b'_N_le_a : b' * N ≤ a
  m_k_b'_le_a : m * k * b' ≤ a
  -- Constant hierarchy
  C0_ge_25_2 : 25 / 2 ≤ C0
  C0_ge_hP : 16 + CT + Cev ≤ C0
  C0_ge_hK : Cth + c5 + 2 * c6 + 1 + 2 * C2 * (CT + C8) + 2 * C4 * (1 + CT + C8) ≤ C0
  C0_ge_mu0 : (64 * (C1 + 3 * Cf) + 8 * Cc + 2) + (6 * Cb + 2) ≤ C0

/-- `Prop`-level `StatementObj` predicate asserting the divisor inequality conclusion for every
`DivIneqObj`. -/
def DivIneqObjProp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (D : ℕ) (J Pl Emb Sg : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    (TT : Finset Pl) [DecidablePred (· ∈ TT)] (nr : ℕ)
    (Obj : DivIneqObj K D J Pl Emb Sg TT nr),
    Obj.muC + Obj.hu - 2 * Obj.Fo ≤
      ∑ t ∈ TT, (Obj.m * (ph (Obj.aT t) - Obj.aT t * Obj.logOm) - Obj.aT t * Obj.logT) +
      (50 * Obj.C0 + 10) * ((TT.card : ℝ) * Obj.a * Obj.La + Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe)

end BoundsMuAndDivIneqObj

/-! ## Section 5: Proof of `div_ineq_of_covol_and_gluing` & Wave 3 Bridges -/

section DivIneqProof

/-- **Step 1 (`passage_corank_bound`)**:
from the rank-partition concentration bounds on `nS s` around `nbar` with relative error
`de = 8 * f * r_pass / g_pass ≤ 1 / 3`, proves the passage slope inequality
`muC ≤ mu0 + 3 * de * (mu0 + HH0 + 4 * lam0) + (25 / 2) * lam0`
and its absorbed form `muC ≤ mu0 + 1 + C0 * lam0` when `mu0 ≤ logκ + p1 * b`! -/
theorem passage_corank_bound {Sg : Type*} [Fintype Sg]
    (rkS nS dg : Sg → ℝ) (muC mu0 muP0 muPs HH0 lam0 logκ f r_pass g_pass k b p1 p2 C0 : ℝ)
    (nbar : ℝ) (hnbar0 : 0 < nbar) (hlam0 : 0 ≤ lam0)
    (hrk : ∀ s, 0 ≤ rkS s) (hsum_rk : 0 < ∑ s, rkS s)
    (hf : 0 ≤ f) (hr : 0 ≤ r_pass) (hg : 0 < g_pass)
    (hnS : ∀ s, (1 - 8 * f * r_pass / g_pass) * nbar ≤ nS s ∧
      nS s ≤ (1 + 8 * f * r_pass / g_pass) * nbar)
    (hmuP0 : |(-mu0) - muP0| ≤ lam0) (hmuPs : |(-muC) - muPs| ≤ lam0)
    (hdg : ∀ s, dg s ≤ rkS s * (HH0 + lam0))
    (hmuPs_ge : (∑ s, nS s * dg s) - 17 / 2 * lam0 * (∑ s, nS s * rkS s) ≤
      muPs * (∑ s, nS s * rkS s))
    (hmuP0_le : muP0 * (∑ s, rkS s) ≤ (∑ s, dg s) + 2 * lam0 * (∑ s, rkS s))
    (hk1 : 1 ≤ k) (hb1 : 1 ≤ b) (hlam_le : lam0 ≤ b)
    (hHH0 : HH0 ≤ -logκ + p2 * b)
    (hmu0 : mu0 ≤ logκ + p1 * b)
    (hfr7 : 24 * f * r_pass * (p1 + p2 + 4) ≤ (k * b) ^ 7)
    (hfr8 : 24 * f * r_pass ≤ (k * b) ^ 8)
    (hkb8 : (k * b) ^ 8 ≤ g_pass)
    (hC0 : 25 / 2 ≤ C0) :
    let de := 8 * f * r_pass / g_pass
    0 ≤ de ∧ de ≤ 1 / 3 ∧
    muC ≤ mu0 + 3 * de * (mu0 + HH0 + 4 * lam0) + (25 / 2) * lam0 ∧
    muC ≤ mu0 + 1 + C0 * lam0 := by
  intro de
  have hde0 : 0 ≤ de := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hf) hr) hg.le
  have h24_le_g : 24 * f * r_pass ≤ g_pass := hfr8.trans hkb8
  have hde3 : de ≤ 1 / 3 := by
    change 8 * f * r_pass / g_pass ≤ 1 / 3
    rw [div_le_iff₀ hg]
    linarith
  let Rsum : ℝ := ∑ s, rkS s
  let Dsum : ℝ := ∑ s, dg s
  let Wsum : ℝ := ∑ s, nS s * rkS s
  have h1_sub_de : 2 / 3 ≤ 1 - de := by linarith
  have hnS_pos : ∀ s, 0 < nS s := fun s => by
    have hlo := (hnS s).1
    have hpos : 0 < (2 / 3 : ℝ) * nbar := by positivity
    nlinarith
  have hW_lo : (1 - de) * nbar * Rsum ≤ Wsum := by
    calc (1 - de) * nbar * Rsum
        = ∑ s, ((1 - de) * nbar) * rkS s := by rw [Finset.mul_sum]
      _ ≤ ∑ s, nS s * rkS s :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hnS s).1 (hrk s)
  have hW_pos : 0 < Wsum := by
    have hpos : 0 < (1 - de) * nbar * Rsum := mul_pos (mul_pos (by linarith) hnbar0) hsum_rk
    linarith
  -- Pointwise lower bound on `nS s * dg s`:
  -- `nS s * dg s = nS s * rkS s * (HH0 + lam0) - nS s * (rkS s * (HH0 + lam0) - dg s)`
  -- `≥ nS s * rkS s * (HH0 + lam0) - (1 + de) * nbar * (rkS s * (HH0 + lam0) - dg s)`
  have hndg_pt : ∀ s,
      nS s * rkS s * (HH0 + lam0) - (1 + de) * nbar * (rkS s * (HH0 + lam0) - dg s) ≤
        nS s * dg s := fun s => by
    have hdiff : 0 ≤ rkS s * (HH0 + lam0) - dg s := sub_nonneg.mpr (hdg s)
    have hmul : nS s * (rkS s * (HH0 + lam0) - dg s) ≤
        (1 + de) * nbar * (rkS s * (HH0 + lam0) - dg s) :=
      mul_le_mul_of_nonneg_right (hnS s).2 hdiff
    linarith
  have hndg_sum : Wsum * (HH0 + lam0) - (1 + de) * nbar * (Rsum * (HH0 + lam0) - Dsum) ≤
      ∑ s, nS s * dg s := by
    have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hndg_pt s
    have hL : ∑ s, (nS s * rkS s * (HH0 + lam0) -
        (1 + de) * nbar * (rkS s * (HH0 + lam0) - dg s)) =
        Wsum * (HH0 + lam0) - (1 + de) * nbar * (Rsum * (HH0 + lam0) - Dsum) := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      rfl
    linarith
  -- Bound `Dsum` from below via `muP0` and `mu0`:
  have hmuP0_lo : -mu0 - lam0 ≤ muP0 := by linarith only [(abs_le.mp hmuP0).2]
  have hmuPs_up : muPs ≤ -muC + lam0 := by linarith only [(abs_le.mp hmuPs).1]
  have hD_lo : (-mu0 - 3 * lam0) * Rsum ≤ Dsum := by
    have h1 : (-mu0 - lam0) * Rsum ≤ muP0 * Rsum :=
      mul_le_mul_of_nonneg_right hmuP0_lo hsum_rk.le
    linarith only [h1, hmuP0_le]
  have hgap_nonneg : 0 ≤ Rsum * (HH0 + lam0) - Dsum := by
    have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hdg s
    rw [← Finset.sum_mul] at hsum
    linarith only [hsum]
  have hgap_up : Rsum * (HH0 + lam0) - Dsum ≤ Rsum * (mu0 + HH0 + 4 * lam0) := by
    linarith only [hD_lo]
  have hgap_mean_nonneg : 0 ≤ mu0 + HH0 + 4 * lam0 := by
    have h1 : 0 ≤ Rsum * (mu0 + HH0 + 4 * lam0) := hgap_nonneg.trans hgap_up
    exact nonneg_of_mul_nonneg_right h1 hsum_rk
  have hW_gap : (1 + de) * nbar * Rsum - Wsum ≤ 2 * de * nbar * Rsum := by
    linarith only [hW_lo]
  have hW_key : Wsum * (-mu0 - 3 * lam0) - 2 * de * nbar * Rsum * (mu0 + HH0 + 4 * lam0) ≤
      ∑ s, nS s * dg s := by
    have hRsum_ne : Rsum ≠ 0 := hsum_rk.ne'
    have h1 : (1 + de) * nbar * (Rsum * (HH0 + lam0) - Dsum) =
        Wsum * ((Rsum * (HH0 + lam0) - Dsum) / Rsum) +
        ((1 + de) * nbar * Rsum - Wsum) * ((Rsum * (HH0 + lam0) - Dsum) / Rsum) := by
      field_simp [hRsum_ne]
      ring
    have h2 : ((1 + de) * nbar * Rsum - Wsum) * ((Rsum * (HH0 + lam0) - Dsum) / Rsum) ≤
        (2 * de * nbar * Rsum) * (mu0 + HH0 + 4 * lam0) := by
      have hdiv_le : (Rsum * (HH0 + lam0) - Dsum) / Rsum ≤ mu0 + HH0 + 4 * lam0 := by
        rw [div_le_iff₀ hsum_rk]
        linarith only [hgap_up]
      have hdiv_nn : 0 ≤ (Rsum * (HH0 + lam0) - Dsum) / Rsum :=
        div_nonneg hgap_nonneg hsum_rk.le
      have hW_nn : 0 ≤ (1 + de) * nbar * Rsum - Wsum := by
        have hW_up : Wsum ≤ (1 + de) * nbar * Rsum := by
          calc Wsum = ∑ s, nS s * rkS s := rfl
            _ ≤ ∑ s, ((1 + de) * nbar) * rkS s :=
                Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hnS s).2 (hrk s)
            _ = (1 + de) * nbar * Rsum := by rw [← Finset.mul_sum]
        linarith only [hW_up]
      exact mul_le_mul hW_gap hdiv_le hdiv_nn (by positivity)
    have h3 : Wsum * (HH0 + lam0) - Wsum * ((Rsum * (HH0 + lam0) - Dsum) / Rsum) =
        Wsum * (Dsum / Rsum) := by
      field_simp [hRsum_ne]
      ring
    have h4 : (-mu0 - 3 * lam0) ≤ Dsum / Rsum := by
      rw [le_div_iff₀ hsum_rk]
      linarith only [hD_lo]
    have h5 : Wsum * (-mu0 - 3 * lam0) ≤ Wsum * (Dsum / Rsum) :=
      mul_le_mul_of_nonneg_left h4 hW_pos.le
    linarith only [hndg_sum, h1, h2, h3, h5]
  have hde_ratio : 2 * de * nbar * Rsum ≤ 3 * de * Wsum := by
    have h32 : 2 ≤ 3 * (1 - de) := by linarith only [hde3]
    calc 2 * de * nbar * Rsum
        = de * (2 * (nbar * Rsum)) := by ring
      _ ≤ de * (3 * (1 - de) * (nbar * Rsum)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h32 (mul_nonneg hnbar0.le hsum_rk.le)) hde0
      _ = 3 * de * ((1 - de) * nbar * Rsum) := by ring
      _ ≤ 3 * de * Wsum := mul_le_mul_of_nonneg_left hW_lo (by positivity)
  have hW_ineq : Wsum * (-mu0 - 3 * lam0 - 3 * de * (mu0 + HH0 + 4 * lam0) - 17 / 2 * lam0) ≤
      Wsum * (-muC + lam0) := by
    have h1 : 2 * de * nbar * Rsum * (mu0 + HH0 + 4 * lam0) ≤
        3 * de * Wsum * (mu0 + HH0 + 4 * lam0) :=
      mul_le_mul_of_nonneg_right hde_ratio hgap_mean_nonneg
    have h2 : muPs * Wsum ≤ (-muC + lam0) * Wsum :=
      mul_le_mul_of_nonneg_right hmuPs_up hW_pos.le
    have h3 : Wsum * (-mu0 - 3 * lam0 - 3 * de * (mu0 + HH0 + 4 * lam0) - 17 / 2 * lam0) =
        Wsum * (-mu0 - 3 * lam0) - 3 * de * Wsum * (mu0 + HH0 + 4 * lam0) - 17 / 2 * lam0 * Wsum := by
      ring
    linarith only [hW_key, h1, h2, h3, hmuPs_ge]
  have hmuC_raw : muC ≤ mu0 + 3 * de * (mu0 + HH0 + 4 * lam0) + (25 / 2) * lam0 := by
    have hdiv := le_of_mul_le_mul_left hW_ineq hW_pos
    linarith only [hdiv]
  refine ⟨hde0, hde3, hmuC_raw, ?_⟩
  have hsum_cancel : mu0 + HH0 + 4 * lam0 ≤ (p1 + p2 + 4) * b := by
    have h4lam : 4 * lam0 ≤ 4 * b := by linarith only [hlam_le]
    linarith only [hmu0, hHH0, h4lam]
  have h3de_le : 3 * de * (mu0 + HH0 + 4 * lam0) ≤ 1 := by
    have hmul : 3 * de * (mu0 + HH0 + 4 * lam0) ≤ 3 * de * ((p1 + p2 + 4) * b) :=
      mul_le_mul_of_nonneg_left hsum_cancel (by positivity)
    have hde_eq : 3 * de * ((p1 + p2 + 4) * b) = 24 * f * r_pass * (p1 + p2 + 4) * b / g_pass := by
      dsimp only [de]; ring
    have hkb_nn : 0 ≤ k * b := by nlinarith only [hk1, hb1]
    have hkb7_b : (k * b) ^ 7 * b ≤ (k * b) ^ 8 := by
      calc (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b) :=
            mul_le_mul_of_nonneg_left (by nlinarith only [hk1, hb1]) (pow_nonneg hkb_nn 7)
        _ = (k * b) ^ 8 := by ring
    have hnum_le : 24 * f * r_pass * (p1 + p2 + 4) * b ≤ g_pass := by
      have hb0 : 0 ≤ b := by linarith only [hb1]
      calc 24 * f * r_pass * (p1 + p2 + 4) * b
          ≤ (k * b) ^ 7 * b := mul_le_mul_of_nonneg_right hfr7 hb0
        _ ≤ (k * b) ^ 8 := hkb7_b
        _ ≤ g_pass := hkb8
    have hdiv_le : 24 * f * r_pass * (p1 + p2 + 4) * b / g_pass ≤ 1 :=
      (div_le_one hg).mpr hnum_le
    linarith only [hmul, hde_eq, hdiv_le]
  have hlamC0 : (25 / 2) * lam0 ≤ C0 * lam0 :=
    mul_le_mul_of_nonneg_right hC0 hlam0
  linarith only [hmuC_raw, h3de_le, hlamC0]

/-- **Step 2 (`base_covolume_mu0_bound`)**:
from `BaseLevelBoundsWithCovolume` (`global_product_formula_slope_upper`), the `muU → muA → muN → muG → -muDef`
descent chain, and the gluing error budget (`LG, E1, E2, E3`), proves the base-level bound
`mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb` with `Eb ≤ C0 * m * xe * (B0 + Nc)`. -/
theorem base_covolume_mu0_bound
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {D : ℕ} {J Pl Emb Sg : Type} [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    {TT : Finset Pl} [DecidablePred (· ∈ TT)] {nr : ℕ}
    (Obj : DivIneqObj K D J Pl Emb Sg TT nr) :
    ∃ Eb : ℝ,
      Obj.mu0 ≤ (∑ j : J, ∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm) + 2 * Obj.Fo + Eb ∧
      Eb ≤ Obj.C0 * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
  have hx0 : 0 < Obj.x := by linarith [Obj.x_ge_one]
  have hL1 : 1 ≤ Obj.L := by rw [Obj.L_eq]; exact Real.one_le_rpow Obj.x_ge_one Obj.eps_pos.le
  have hL0 : 0 ≤ Obj.L := by linarith
  have hb1 : 1 ≤ Obj.b := by rw [Obj.b_eq]; exact Real.one_le_exp hL0
  have hb0 : 0 ≤ Obj.b := by linarith
  have hrd0 : 0 < Obj.rd := by linarith [Obj.rd_ge_one]
  have hxe_ge1 : 1 ≤ Obj.xe := le_trans (by rw [← Obj.L_eq]; exact hL1) Obj.xe_ge
  have hxe0 : 0 ≤ Obj.xe := by linarith
  have hm0 : 0 ≤ Obj.m := by linarith [Obj.m_ge_one]
  have hf0 : 0 ≤ Obj.f := by linarith [Obj.f_ge_one]
  have hk0 : 0 ≤ Obj.k := by linarith [Obj.k_ge_one]
  have hN1 : 1 ≤ Obj.N := by linarith [Obj.k_ge_one, Obj.m_ge_one, Obj.km_le_N]
  have hN0 : 0 ≤ Obj.N := by linarith
  have hB0_eq : Obj.B0 = Obj.f * Obj.m * Obj.b * Obj.L := by rw [Obj.B0_eq, Obj.L_eq]
  have hB0_nn : 0 ≤ Obj.B0 := by rw [hB0_eq]; positivity
  have hfm1 : 1 ≤ Obj.f * Obj.m := by
    nlinarith [Obj.f_ge_one, Obj.m_ge_one]
  have hb_le_B0 : Obj.b ≤ Obj.B0 := by
    rw [hB0_eq]
    have hfmL : 1 ≤ Obj.f * Obj.m * Obj.L := by nlinarith
    nlinarith
  have hL_le_B0 : Obj.L ≤ Obj.B0 := by
    rw [hB0_eq]
    have hfmb : 1 ≤ Obj.f * Obj.m * Obj.b := by nlinarith
    nlinarith
  have hB0_le_xe : Obj.B0 ≤ Obj.B0 * Obj.xe := by nlinarith only [hB0_nn, hxe_ge1]
  have hbase := Obj.base.mu_upper_of_meanLog_zero Obj.meanLog_kappa_eq
  rw [← Obj.mu0_eq, ← Obj.Fo_eq] at hbase
  have hLL0_nonneg : 0 ≤ Obj.LL0 := by
    rw [Obj.LL0_eq]
    have hbrd : 1 ≤ Obj.b * Obj.rd := by nlinarith only [hb1, Obj.rd_ge_one]
    have h1 : 0 ≤ Real.log (Obj.b * Obj.rd) := Real.log_nonneg hbrd
    have h2 : 0 ≤ Real.log Obj.x := Real.log_nonneg Obj.x_ge_one
    have hllx0 : 0 ≤ Obj.llx := by linarith only [Obj.llx_ge]
    nlinarith only [h1, h2, hllx0, Obj.Lchi_nonneg]
  have hLL0_le : Obj.LL0 ≤ 4 * Obj.L * Obj.xe := by
    rw [Obj.LL0_eq, Obj.b_eq, Real.log_mul (Real.exp_pos Obj.L).ne' hrd0.ne', Real.log_exp]
    have h2 : Obj.L + Real.log Obj.rd ≤ 2 * Obj.L := by linarith only [Obj.log_rd_le]
    have h3 : (Obj.L + Real.log Obj.rd) * Obj.llx ≤ 2 * Obj.L * Obj.xe :=
      mul_le_mul h2 Obj.llx_le (by linarith only [Obj.llx_ge]) (by positivity)
    have h4 : Obj.Lchi + Real.log Obj.x ≤ 2 * Obj.L * Obj.xe := by
      have hLx : Obj.Lchi + Real.log Obj.x ≤ 2 * Obj.L := by
        linarith only [Obj.Lchi_le, Obj.log_x_le]
      have h2L : 2 * Obj.L ≤ 2 * Obj.L * Obj.xe := by nlinarith only [hL0, hxe_ge1]
      linarith only [hLx, h2L]
    linarith only [h3, h4]
  have hkS_le_b : Obj.k * Obj.S ≤ Obj.b := by
    have hw0 : 0 ≤ Obj.w'' := le_trans (mul_nonneg hk0 Obj.S_nonneg) Obj.k_S_le_w''
    have h1 : Obj.w'' ≤ Obj.N * Obj.w'' := by nlinarith only [hN1, hw0]
    linarith only [Obj.k_S_le_w'', h1, Obj.N_w''_le_b]
  have hkη_le_b : Obj.k * Obj.η ≤ Obj.b := by
    have hm_le_N : Obj.m ≤ Obj.N := by linarith only [Obj.k_ge_one, Obj.km_le_N]
    have hm1 : 1 ≤ Obj.m * (Obj.tt + 1) := by nlinarith only [Obj.m_ge_one, Obj.tt_nonneg]
    have hη_le_w'' : Obj.η ≤ Obj.w'' := by
      have h1 : Obj.η ≤ Obj.m * (Obj.tt + 1) * Obj.η := by nlinarith only [hm1, Obj.η_nonneg]
      exact h1.trans Obj.m_tt_η_le_w''
    have hkη_le_Nw : Obj.k * Obj.η ≤ Obj.N * Obj.w'' :=
      mul_le_mul (by linarith only [Obj.km_le_N, Obj.m_ge_one]) hη_le_w'' Obj.η_nonneg hN0
    exact hkη_le_Nw.trans Obj.N_w''_le_b
  have hSw_le : ∀ j, (∑ τ : Pl, Obj.w j τ) ≤ 2 * Obj.f * Obj.b := fun j => by
    calc ∑ τ : Pl, Obj.w j τ
        ≤ ∑ _τ : Pl, (2 * Obj.b) := Finset.sum_le_sum fun τ _ => (Obj.w_bounds j τ).2
      _ = (Fintype.card Pl : ℝ) * (2 * Obj.b) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Obj.f * (2 * Obj.b) := mul_le_mul_of_nonneg_right Obj.card_Pl_le (by linarith only [hb0])
      _ = 2 * Obj.f * Obj.b := by ring
  have hSw_nn : ∀ j, 0 ≤ ∑ τ : Pl, Obj.w j τ := fun j =>
    Finset.sum_nonneg fun τ _ => (Obj.w_bounds j τ).1
  have hSua_le : ∀ j, (∑ τ : Pl, Obj.ua j τ) ≤ 8 * Obj.f * Obj.m * Obj.b := fun j => by
    have hkSη : 0 ≤ 2 * (Obj.k * Obj.S + Obj.k * Obj.η) := by
      have h1 : 0 ≤ Obj.k * Obj.S := mul_nonneg hk0 Obj.S_nonneg
      have h2 : 0 ≤ Obj.k * Obj.η := mul_nonneg hk0 Obj.η_nonneg
      linarith only [h1, h2]
    calc ∑ τ : Pl, Obj.ua j τ
        ≤ ∑ τ : Pl, 2 * (Obj.m * Obj.w j τ + Obj.k * Obj.S + Obj.k * Obj.η) :=
          Finset.sum_le_sum fun τ _ => (Obj.ua_bounds j τ).2
      _ = 2 * Obj.m * (∑ τ : Pl, Obj.w j τ) +
            (Fintype.card Pl : ℝ) * (2 * (Obj.k * Obj.S + Obj.k * Obj.η)) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
      _ ≤ 2 * Obj.m * (2 * Obj.f * Obj.b) + Obj.f * (2 * (Obj.b + Obj.b)) := by
          have h1 : 2 * Obj.m * (∑ τ : Pl, Obj.w j τ) ≤ 2 * Obj.m * (2 * Obj.f * Obj.b) :=
            mul_le_mul_of_nonneg_left (hSw_le j) (by linarith only [hm0])
          have h2 : (Fintype.card Pl : ℝ) * (2 * (Obj.k * Obj.S + Obj.k * Obj.η)) ≤
              Obj.f * (2 * (Obj.b + Obj.b)) :=
            mul_le_mul Obj.card_Pl_le (by linarith only [hkS_le_b, hkη_le_b]) hkSη hf0
          linarith only [h1, h2]
      _ = 4 * Obj.f * Obj.m * Obj.b + 4 * Obj.f * Obj.b := by ring
      _ ≤ 4 * Obj.f * Obj.m * Obj.b + 4 * Obj.f * Obj.m * Obj.b := by
          have h1 : 4 * Obj.f * Obj.b ≤ 4 * Obj.f * Obj.m * Obj.b := by
            have hfb : 0 ≤ Obj.f * Obj.b := mul_nonneg hf0 hb0
            nlinarith only [Obj.m_ge_one, hfb]
          linarith only [h1]
      _ = 8 * Obj.f * Obj.m * Obj.b := by ring
  have hSua_nn : ∀ j, 0 ≤ ∑ τ : Pl, Obj.ua j τ := fun j =>
    le_trans zero_le_one (Obj.ua_sum_ge j)
  -- Descent at each `j`: `-muDef (XW j) (M j) ≤ ∑ τ, pq j * w j τ * logOm + Eb_j`
  have hj_bound : ∀ j : J,
      -Obj.base.G.Lsys.muDef (Obj.base.G.XW j) (Obj.base.G.M j) ≤
        (∑ τ : Pl, Obj.pq j * Obj.w j τ * Obj.logOm) +
        (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe * (Obj.B0 + Obj.Nc) := by
    intro j
    obtain ⟨hdA0, hdAB, hεdB, hεd0, hPd0⟩ := Obj.dAB_bounds j
    obtain ⟨hQd1, hΛd, hεQd⟩ := Obj.Qd_bounds1 j
    obtain ⟨hdN0, hdN_eq, hdbd0, hdbd_le, hδd0, hδd12⟩ := Obj.dN_bounds j
    obtain ⟨hQd2, hmmax, hGd⟩ := Obj.Qd_bounds2 j
    have hQd0 : 0 ≤ Obj.Qd j := le_trans (abs_nonneg _) hQd1
    -- Step (i): `-muG j ≤ -muN j + 12 * δd j * Qd j`
    have hmuG_muN : -Obj.muG j ≤ -Obj.muN j + 12 * Obj.δd j * Obj.Qd j := by
      have hdgd_ge : (3 / 4 : ℝ) * Obj.dN j ≤ Obj.dgd j := by
        have h1 : Obj.dbd j ≤ (1 / 4 : ℝ) * Obj.dN j := by
          calc Obj.dbd j ≤ 3 * Obj.δd j * Obj.dN j := hdbd_le
            _ ≤ 3 * (1 / 12) * Obj.dN j :=
                mul_le_mul_of_nonneg_right (by linarith) hdN0.le
            _ = (1 / 4 : ℝ) * Obj.dN j := by ring
        linarith
      have hdgd_pos : 0 < Obj.dgd j := by linarith
      have hmmax_le : Obj.mmax j + Obj.Gd j - Obj.muN j ≤ 3 * Obj.Qd j := by
        have h1 : -Obj.muN j ≤ Obj.Qd j := by linarith [(abs_le.mp hQd2).1]
        linarith
      have e1 : Obj.dbd j * (Obj.mmax j + Obj.Gd j - Obj.muN j) ≤ Obj.dbd j * (3 * Obj.Qd j) :=
        mul_le_mul_of_nonneg_left hmmax_le hdbd0
      have f1 : (3 * Obj.Qd j) * Obj.dbd j ≤ (3 * Obj.Qd j) * (3 * Obj.δd j * Obj.dN j) :=
        mul_le_mul_of_nonneg_left hdbd_le (by positivity)
      have f2 : (12 * Obj.δd j * Obj.Qd j) * ((3 / 4 : ℝ) * Obj.dN j) ≤
          (12 * Obj.δd j * Obj.Qd j) * Obj.dgd j :=
        mul_le_mul_of_nonneg_left hdgd_ge (by positivity)
      have hN_rew : (Obj.dgd j + Obj.dbd j) * Obj.muN j ≤
          Obj.dgd j * Obj.muG j + Obj.dbd j * (Obj.mmax j + Obj.Gd j) := by
        rw [← hdN_eq]; exact Obj.dN_muN_le j
      have key : 0 ≤ Obj.dgd j * (Obj.muG j - Obj.muN j + 12 * Obj.δd j * Obj.Qd j) := by
        linarith
      by_contra hcon
      push Not at hcon
      have hneg : Obj.dgd j * (Obj.muG j - Obj.muN j + 12 * Obj.δd j * Obj.Qd j) < 0 :=
        mul_neg_of_pos_of_neg hdgd_pos (by linarith)
      linarith
    -- Step (ii): `-muN j ≤ X_U - 2 * cfl j + Pd j + b / 2` where `X_U = 2 * (C1 * LL0 * ∑ ua + b/4)`
    let XU : ℝ := 2 * (Obj.C1 * Obj.LL0 * (∑ τ : Pl, Obj.ua j τ) + Obj.b / 4)
    have hXU0 : 0 ≤ XU := by
      dsimp only [XU]
      have h1 : 0 ≤ Obj.C1 * Obj.LL0 * (∑ τ : Pl, Obj.ua j τ) :=
        mul_nonneg (mul_nonneg Obj.C1_nonneg hLL0_nonneg) (hSua_nn j)
      linarith
    have hdB_pos : 0 < Obj.dB j := lt_of_lt_of_le hdA0 hdAB
    have hmuN_le : -Obj.muN j ≤ XU - 2 * Obj.cfl j + Obj.Pd j + Obj.b / 2 := by
      have g1 : Obj.dA j * (-XU) ≤ Obj.dA j * Obj.muU j :=
        mul_le_mul_of_nonneg_left (Obj.muU_ge j) hdA0.le
      have g1' : Obj.dB j * (-XU) ≤ Obj.dA j * (-XU) := by
        have : 0 ≤ (Obj.dB j - Obj.dA j) * XU := mul_nonneg (by linarith) hXU0
        linarith
      have g2 : (Obj.dB j - Obj.dA j) * (2 * Obj.cfl j) ≤ (Obj.dB j - Obj.dA j) * Obj.Qd j :=
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hQd1) (by linarith)
      have g3 : (Obj.dB j - Obj.dA j) * Obj.Λd j ≤ (Obj.dB j - Obj.dA j) * Obj.Qd j :=
        mul_le_mul_of_nonneg_left hΛd (by linarith)
      have g4 : (Obj.dB j - Obj.dA j) * Obj.Qd j ≤ (Obj.εd j * Obj.dB j) * Obj.Qd j :=
        mul_le_mul_of_nonneg_right (by linarith) hQd0
      have g5 : Obj.dA j * Obj.Pd j ≤ Obj.dB j * Obj.Pd j :=
        mul_le_mul_of_nonneg_right hdAB hPd0
      have g6 : Obj.dA j * (Obj.muU j + 2 * Obj.cfl j - Obj.Pd j) ≤
          Obj.dA j * (Obj.muA j - Obj.Pd j) :=
        mul_le_mul_of_nonneg_left (by linarith [Obj.muA_ge j]) hdA0.le
      have g7 : Obj.dB j * (Obj.εd j * Obj.Qd j) ≤ Obj.dB j * (Obj.b / 4) :=
        mul_le_mul_of_nonneg_left hεQd hdB_pos.le
      have key : Obj.dB j * (-XU + 2 * Obj.cfl j - Obj.Pd j - Obj.b / 2) ≤
          Obj.dB j * Obj.muN j := by
        linarith [Obj.dB_muN_ge j, g1, g1', g2, g3, g4, g5, g6, g7]
      have hdiv := le_of_mul_le_mul_left key hdB_pos
      linarith
    -- Step (iii): Combine `muG`, `muN`, `Pd + 12 * δd * Qd + P9 ≤ b`
    have hmuDef_le : -Obj.base.G.Lsys.muDef (Obj.base.G.XW j) (Obj.base.G.M j) ≤
        XU - 2 * Obj.cfl j + 3 * Obj.b / 2 := by
      have h1 := Obj.muG_le j
      have h2 := Obj.Pd_P9_le j
      linarith
    -- Step (iv): Expand `-2 * cfl j` via `c1_close`
    have hc1_sum : -2 * (∑ τ : Pl, Obj.w j τ * Obj.c1 j τ) ≤
        (∑ τ : Pl, Obj.pq j * Obj.w j τ * Obj.logOm) +
        2 * Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * (∑ τ : Pl, Obj.w j τ) := by
      have hpt : ∀ τ : Pl, -2 * (Obj.w j τ * Obj.c1 j τ) ≤
          Obj.pq j * Obj.w j τ * Obj.logOm +
            2 * Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * Obj.w j τ := fun τ => by
        have hc := (abs_le.mp (Obj.c1_close j τ)).1
        have hw0 : 0 ≤ Obj.w j τ := (Obj.w_bounds j τ).1
        have hmul := mul_le_mul_of_nonneg_left
          (show -Obj.c1 j τ ≤ Obj.pq j * Obj.logOm / 2 + Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) by linarith)
          (show 0 ≤ 2 * Obj.w j τ by linarith)
        linarith
      calc -2 * (∑ τ : Pl, Obj.w j τ * Obj.c1 j τ)
          = ∑ τ : Pl, (-2 * (Obj.w j τ * Obj.c1 j τ)) := by rw [Finset.mul_sum]
        _ ≤ ∑ τ : Pl, (Obj.pq j * Obj.w j τ * Obj.logOm +
              2 * Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * Obj.w j τ) :=
            Finset.sum_le_sum fun τ _ => hpt τ
        _ = (∑ τ : Pl, Obj.pq j * Obj.w j τ * Obj.logOm) +
            2 * Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * (∑ τ : Pl, Obj.w j τ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcfl_bound : -2 * Obj.cfl j ≤
        (∑ τ : Pl, Obj.pq j * Obj.w j τ * Obj.logOm) +
        2 * Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * (∑ τ : Pl, Obj.w j τ) +
        2 * Obj.Cf * Obj.q' j * Real.log Obj.rd * (∑ τ : Pl, Obj.w j τ) +
        2 * Obj.Cf * Obj.L := by
      rw [Obj.cfl_eq j]; linarith
    -- Step (v): Absorb `XU`, `Cc`, `Cf`, `3 * b / 2 + b / 2 = 2 * b` into `(64*(C1+3*Cf) + 8*Cc + 2) * xe * (B0 + Nc)`
    have hT_C1 : 2 * Obj.C1 * Obj.LL0 * (∑ τ : Pl, Obj.ua j τ) ≤ 64 * Obj.C1 * Obj.xe * Obj.B0 := by
      have h1 : Obj.LL0 * (∑ τ : Pl, Obj.ua j τ) ≤ (4 * Obj.L * Obj.xe) * (8 * Obj.f * Obj.m * Obj.b) :=
        mul_le_mul hLL0_le (hSua_le j) (hSua_nn j) (by positivity)
      have h2 : 2 * Obj.C1 * (Obj.LL0 * (∑ τ : Pl, Obj.ua j τ)) ≤
          2 * Obj.C1 * ((4 * Obj.L * Obj.xe) * (8 * Obj.f * Obj.m * Obj.b)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith [Obj.C1_nonneg])
      have h3 : 2 * Obj.C1 * ((4 * Obj.L * Obj.xe) * (8 * Obj.f * Obj.m * Obj.b)) =
          64 * Obj.C1 * Obj.xe * Obj.B0 := by
        rw [hB0_eq]; ring
      linarith
    have hT_Cc : 2 * Obj.Cc * Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * (∑ τ : Pl, Obj.w j τ) ≤
        8 * Obj.Cc * Obj.xe * Obj.B0 := by
      have h1 : Obj.q' j * (Real.log Obj.rd + Obj.Lchi) ≤ Obj.m * (2 * Obj.L) :=
        mul_le_mul (Obj.q'_bounds j).2 (by linarith [Obj.log_rd_le, Obj.Lchi_le])
          (add_nonneg (Real.log_nonneg Obj.rd_ge_one) Obj.Lchi_nonneg) hm0
      have h2 : Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * (∑ τ : Pl, Obj.w j τ) ≤
          (Obj.m * (2 * Obj.L)) * (2 * Obj.f * Obj.b) :=
        mul_le_mul h1 (hSw_le j) (hSw_nn j) (by positivity)
      have h3 : 2 * Obj.Cc * (Obj.q' j * (Real.log Obj.rd + Obj.Lchi) * (∑ τ : Pl, Obj.w j τ)) ≤
          2 * Obj.Cc * ((Obj.m * (2 * Obj.L)) * (2 * Obj.f * Obj.b)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith [Obj.Cc_nonneg])
      have h4 : 2 * Obj.Cc * ((Obj.m * (2 * Obj.L)) * (2 * Obj.f * Obj.b)) = 8 * Obj.Cc * Obj.B0 := by
        rw [hB0_eq]; ring
      have h5 : 8 * Obj.Cc * Obj.B0 ≤ 8 * Obj.Cc * Obj.xe * Obj.B0 := by
        have hccB : 0 ≤ 8 * Obj.Cc * Obj.B0 := mul_nonneg (by linarith [Obj.Cc_nonneg]) hB0_nn
        nlinarith
      linarith
    have hT_Cf : 2 * Obj.Cf * Obj.q' j * Real.log Obj.rd * (∑ τ : Pl, Obj.w j τ) + 2 * Obj.Cf * Obj.L ≤
        192 * Obj.Cf * Obj.xe * Obj.B0 := by
      have h1 : Obj.q' j * Real.log Obj.rd ≤ Obj.m * Obj.L :=
        mul_le_mul (Obj.q'_bounds j).2 Obj.log_rd_le (Real.log_nonneg Obj.rd_ge_one) hm0
      have h2 : Obj.q' j * Real.log Obj.rd * (∑ τ : Pl, Obj.w j τ) ≤
          (Obj.m * Obj.L) * (2 * Obj.f * Obj.b) :=
        mul_le_mul h1 (hSw_le j) (hSw_nn j) (by positivity)
      have h3 : 2 * Obj.Cf * (Obj.q' j * Real.log Obj.rd * (∑ τ : Pl, Obj.w j τ)) ≤
          4 * Obj.Cf * Obj.B0 := by
        have h4 : 2 * Obj.Cf * ((Obj.m * Obj.L) * (2 * Obj.f * Obj.b)) = 4 * Obj.Cf * Obj.B0 := by
          rw [hB0_eq]; ring
        linarith [mul_le_mul_of_nonneg_left h2 (by linarith [Obj.Cf_nonneg])]
      have h4 : 2 * Obj.Cf * Obj.L ≤ 2 * Obj.Cf * Obj.B0 :=
        mul_le_mul_of_nonneg_left hL_le_B0 (by linarith [Obj.Cf_nonneg])
      have h6 : 6 * Obj.Cf * Obj.B0 ≤ 192 * Obj.Cf * Obj.xe * Obj.B0 := by
        have hcfB : 0 ≤ Obj.Cf * Obj.B0 := mul_nonneg Obj.Cf_nonneg hB0_nn
        nlinarith
      linarith
    have hT_2b : 2 * Obj.b ≤ 2 * Obj.xe * Obj.B0 := by
      have : Obj.b ≤ Obj.xe * Obj.B0 := by nlinarith
      linarith
    have hXU_eq : XU = 2 * Obj.C1 * Obj.LL0 * (∑ τ : Pl, Obj.ua j τ) + Obj.b / 2 := by
      dsimp only [XU]; ring
    have hB0_le_BN : Obj.B0 ≤ Obj.B0 + Obj.Nc := by linarith [Obj.Nc_nonneg]
    have hcoeff_nn : 0 ≤ (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe :=
      mul_nonneg (by linarith [Obj.C1_nonneg, Obj.Cf_nonneg, Obj.Cc_nonneg]) hxe0
    have hmul_BN : (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe * Obj.B0 ≤
        (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe * (Obj.B0 + Obj.Nc) :=
      mul_le_mul_of_nonneg_left hB0_le_BN hcoeff_nn
    have hexpand : 64 * Obj.C1 * Obj.xe * Obj.B0 + 192 * Obj.Cf * Obj.xe * Obj.B0 +
        8 * Obj.Cc * Obj.xe * Obj.B0 + 2 * Obj.xe * Obj.B0 =
        (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe * Obj.B0 := by ring
    linarith
  -- Step 2c: Sum over `j : J` and combine with `LG + ∑ j, (E1 j + E2 j) + E3`
  have hsum_j : ∑ j : J, (-Obj.base.G.Lsys.muDef (Obj.base.G.XW j) (Obj.base.G.M j)) ≤
      (∑ j : J, ∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm) +
      (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
    calc ∑ j : J, (-Obj.base.G.Lsys.muDef (Obj.base.G.XW j) (Obj.base.G.M j))
        ≤ ∑ j : J, ((∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm) +
            (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe * (Obj.B0 + Obj.Nc)) :=
          Finset.sum_le_sum fun j _ => hj_bound j
      _ = (∑ j : J, ∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm) +
            (Fintype.card J : ℝ) *
              ((64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.xe * (Obj.B0 + Obj.Nc)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (∑ j : J, ∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm) +
            (64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
          rw [Obj.card_J_eq]; ring
  have hE3_nn : 0 ≤ Obj.base.G.E3 := by
    have h0 : 0 ≤ ∑ y ∈ Obj.base.G.Sy, lw y * (2 / Obj.base.G.elly y ^ 2) :=
      Finset.sum_nonneg fun y _ => mul_nonneg (lw_nonneg y) (div_nonneg zero_le_two (sq_nonneg _))
    exact h0.trans Obj.base.G.sum_E3
  have hE3_le_mE3 : Obj.base.G.E3 ≤ ∑ _j : J, Obj.base.G.E3 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Obj.card_J_eq]
    nlinarith only [Obj.m_ge_one, hE3_nn]
  have hlogDG_le : Obj.logDG ≤ Obj.Cb * Obj.B0 := by
    have h1 : Obj.Cb * Obj.f * Obj.N * Real.log (Obj.f * Obj.N) =
        Obj.Cb * Obj.f * (Obj.N * Real.log (Obj.f * Obj.N)) := by ring
    have h2 : Obj.Cb * Obj.f * (Obj.N * Real.log (Obj.f * Obj.N)) ≤ Obj.Cb * Obj.f * Obj.b :=
      mul_le_mul_of_nonneg_left Obj.N_logfN_le (mul_nonneg Obj.Cb_nonneg hf0)
    have h3 : Obj.Cb * Obj.f * Obj.b ≤ Obj.Cb * Obj.B0 := by
      rw [hB0_eq]
      have hml : 1 ≤ Obj.m * Obj.L := by nlinarith only [Obj.m_ge_one, hL1]
      have hcfb : 0 ≤ Obj.Cb * Obj.f * Obj.b := mul_nonneg (mul_nonneg Obj.Cb_nonneg hf0) hb0
      nlinarith only [hml, hcfb]
    linarith only [Obj.logDG_le, h1, h2, h3]
  have hN2logg_le : Obj.Cb * Obj.f * Obj.N ^ 2 * Obj.logg ≤ Obj.Cb * Obj.B0 := by
    have h1 : Obj.Cb * Obj.f * Obj.N ^ 2 * Obj.logg = Obj.Cb * Obj.f * (Obj.N ^ 2 * Obj.logg) := by
      ring
    have h2 : Obj.Cb * Obj.f * (Obj.N ^ 2 * Obj.logg) ≤ Obj.Cb * Obj.f * Obj.b :=
      mul_le_mul_of_nonneg_left Obj.N2_logg_le (mul_nonneg Obj.Cb_nonneg hf0)
    have h3 : Obj.Cb * Obj.f * Obj.b ≤ Obj.Cb * Obj.B0 := by
      rw [hB0_eq]
      have hml : 1 ≤ Obj.m * Obj.L := by nlinarith only [Obj.m_ge_one, hL1]
      have hcfb : 0 ≤ Obj.Cb * Obj.f * Obj.b := mul_nonneg (mul_nonneg Obj.Cb_nonneg hf0) hb0
      nlinarith only [hml, hcfb]
    linarith only [h1, h2, h3]
  have hLG_le : Obj.base.G.LG ≤ (2 * Obj.Cb + 1) * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
    have hlam_le : Obj.lam0 ≤ Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
      have hmxe : 1 ≤ Obj.m * Obj.xe := by nlinarith only [Obj.m_ge_one, hxe_ge1]
      have h1 : Obj.B0 ≤ Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
        nlinarith only [hmxe, hB0_nn, Obj.Nc_nonneg, hm0, hxe0]
      linarith only [Obj.lam0_le_b, hb_le_B0, h1]
    have hCb_le : 2 * Obj.Cb * Obj.B0 ≤ 2 * Obj.Cb * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
      have hmxe : 1 ≤ Obj.m * Obj.xe := by nlinarith only [Obj.m_ge_one, hxe_ge1]
      have hcbB : 0 ≤ 2 * Obj.Cb * Obj.B0 := mul_nonneg (by linarith only [Obj.Cb_nonneg]) hB0_nn
      have hcb_xe : 0 ≤ 2 * Obj.Cb * Obj.m * Obj.xe := by
        exact mul_nonneg (mul_nonneg (by linarith only [Obj.Cb_nonneg]) hm0) hxe0
      nlinarith only [hmxe, hcbB, hcb_xe, Obj.Nc_nonneg]
    linarith only [Obj.LG_le, hlam_le, hlogDG_le, hN2logg_le, hCb_le]
  have hE123_le : (∑ j : J, (Obj.base.G.E1 j + Obj.base.G.E2 j)) + Obj.base.G.E3 ≤
      (4 * Obj.Cb + 1) * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
    have hsum_le : (∑ j : J, (Obj.base.G.E1 j + Obj.base.G.E2 j)) + Obj.base.G.E3 ≤
        ∑ j : J, ((Obj.base.G.E1 j + Obj.base.G.E3) + Obj.base.G.E2 j) := by
      have hrew : ∑ j : J, ((Obj.base.G.E1 j + Obj.base.G.E3) + Obj.base.G.E2 j) =
          (∑ j : J, (Obj.base.G.E1 j + Obj.base.G.E2 j)) + ∑ _j : J, Obj.base.G.E3 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith only [hrew, hE3_le_mE3]
    have hpt : ∀ j : J, (Obj.base.G.E1 j + Obj.base.G.E3) + Obj.base.G.E2 j ≤
        4 * Obj.Cb * Obj.xe * (Obj.B0 + Obj.Nc) := fun j => by
      have h1 := Obj.E1_3_le j
      have h2 := Obj.E2_le j
      have hcbB : Obj.Cb * Obj.B0 ≤ Obj.Cb * Obj.xe * (Obj.B0 + Obj.Nc) := by
        have hcb0 : 0 ≤ Obj.Cb * Obj.B0 := mul_nonneg Obj.Cb_nonneg hB0_nn
        have hcb_xe : 0 ≤ Obj.Cb * Obj.xe := mul_nonneg Obj.Cb_nonneg hxe0
        nlinarith only [hcb0, hcb_xe, hxe_ge1, Obj.Nc_nonneg]
      linarith only [h1, h2, hlogDG_le, hN2logg_le, hcbB]
    have hsum_pt : ∑ j : J, ((Obj.base.G.E1 j + Obj.base.G.E3) + Obj.base.G.E2 j) ≤
        Obj.m * (4 * Obj.Cb * Obj.xe * (Obj.B0 + Obj.Nc)) := by
      calc ∑ j : J, ((Obj.base.G.E1 j + Obj.base.G.E3) + Obj.base.G.E2 j)
          ≤ ∑ _j : J, (4 * Obj.Cb * Obj.xe * (Obj.B0 + Obj.Nc)) :=
            Finset.sum_le_sum fun j _ => hpt j
        _ = (Fintype.card J : ℝ) * (4 * Obj.Cb * Obj.xe * (Obj.B0 + Obj.Nc)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = Obj.m * (4 * Obj.Cb * Obj.xe * (Obj.B0 + Obj.Nc)) := by rw [Obj.card_J_eq]
    have hnn : 0 ≤ Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) :=
      mul_nonneg (mul_nonneg hm0 hxe0) (by linarith only [hB0_nn, Obj.Nc_nonneg])
    linarith only [hsum_le, hsum_pt, hnn]
  have hC0_tot : ((64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) + (6 * Obj.Cb + 2)) *
      Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) ≤
      Obj.C0 * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) := by
    have hnn : 0 ≤ Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) :=
      mul_nonneg (mul_nonneg hm0 hxe0) (by linarith only [hB0_nn, Obj.Nc_nonneg])
    have hmul := mul_le_mul_of_nonneg_right Obj.C0_ge_mu0 hnn
    linarith only [hmul]
  refine ⟨(64 * (Obj.C1 + 3 * Obj.Cf) + 8 * Obj.Cc + 2) * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) +
      Obj.base.G.LG + (∑ j : J, (Obj.base.G.E1 j + Obj.base.G.E2 j)) + Obj.base.G.E3, ?_, ?_⟩
  · linarith only [hbase, hsum_j]
  · linarith only [hLG_le, hE123_le, hC0_tot]

/-- **Step 3 (`archimedean_hK_bound`)**:
averages the archimedean period height `logK j s` over `Emb` (`hK j = (∑ s, logK j s) / #Emb`),
eliminating the `logOmτ` variation to produce:
`∀ j, hK j ≤ ∑ ρ, (∑ i, ph (ν j ρ i) - (∑ i, ν j ρ i) * logOm) + C0 * f * N^2 * (La + m^3 * L)`. -/
theorem archimedean_hK_bound
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {D : ℕ} {J Pl Emb Sg : Type} [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    {TT : Finset Pl} [DecidablePred (· ∈ TT)] {nr : ℕ}
    (Obj : DivIneqObj K D J Pl Emb Sg TT nr) :
    ∀ j : J, Obj.hK j ≤
      (∑ ρ : Pl, ((∑ i : Fin nr, ph (Obj.ν j ρ i)) - (∑ i : Fin nr, Obj.ν j ρ i) * Obj.logOm)) +
        Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L) := by
  intro j
  have hn : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hf0 : 0 ≤ Obj.f := by linarith [Obj.f_ge_one]
  have hm0 : 0 ≤ Obj.m := by linarith [Obj.m_ge_one]
  have hN1 : 1 ≤ Obj.N := by linarith [Obj.k_ge_one, Obj.m_ge_one, Obj.km_le_N]
  have hN0 : 0 ≤ Obj.N := by linarith
  have hL1 : 1 ≤ Obj.L := by rw [Obj.L_eq]; exact Real.one_le_rpow Obj.x_ge_one Obj.eps_pos.le
  have hL0 : 0 ≤ Obj.L := by linarith
  have hx0 : 0 < Obj.x := by linarith [Obj.x_ge_one]
  have hrd0 : 0 < Obj.rd := by linarith [Obj.rd_ge_one]
  have hb_pos : 0 < Obj.b := by rw [Obj.b_eq]; exact Real.exp_pos Obj.L
  have hLa_eq : Obj.La = Real.log Obj.x + Obj.L + Real.log Obj.rd := by
    rw [Obj.La_eq, Obj.a_eq, Obj.b_eq, Real.log_mul (mul_pos hx0 (Real.exp_pos Obj.L)).ne' hrd0.ne',
      Real.log_mul hx0.ne' (Real.exp_pos Obj.L).ne', Real.log_exp]
  have hLLa : Obj.L ≤ Obj.La := by
    linarith [Real.log_nonneg Obj.x_ge_one, Real.log_nonneg Obj.rd_ge_one]
  have hLa1 : 1 ≤ Obj.La := by linarith
  have hLa0 : 0 ≤ Obj.La := by linarith
  have hF0 : 0 ≤ Obj.f * Obj.N ^ 2 := mul_nonneg hf0 (sq_nonneg Obj.N)
  have hg0_nn : 0 ≤ (Fintype.card Pl : ℝ) * Obj.g0 j :=
    mul_nonneg (Nat.cast_nonneg _) (Obj.g0_bounds j).1
  have hcF : (Fintype.card Pl : ℝ) * Obj.g0 j ≤ Obj.f * Obj.N ^ 2 :=
    mul_le_mul Obj.card_Pl_le (Obj.g0_bounds j).2 (Obj.g0_bounds j).1 hf0
  let K0 : ℝ :=
    (Fintype.card Pl : ℝ) * Obj.g0 j *
      Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * Obj.g0 j) * Obj.v) +
    2 * (Obj.C2 * Obj.f * Obj.m ^ 2 * Obj.N ^ 2 * (Obj.logg + Obj.logT)) +
    (∑ τ : Pl, (1 + 2 * Obj.g0 j * Real.log (2 * (∑ i, Obj.ν j τ i) + 2))) +
    (Obj.logh j + Obj.logh' j)
  have hpt : ∀ s : Emb, Obj.logK j s ≤
      (∑ τ : Pl, ((∑ i, ph (Obj.ν j τ i)) - (∑ i, Obj.ν j τ i) * Obj.logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * Obj.g0 j * Obj.logth0 s + K0 := fun s => by
    have a1 := Obj.logK_le j s
    have a2 := Obj.MainNotions_le j s
    dsimp only [K0]
    linarith only [a1, a2]
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hpt s
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hsum_Om : ∑ s : Emb, ∑ τ : Pl,
        ((∑ i, ph (Obj.ν j τ i)) - (∑ i, Obj.ν j τ i) * Obj.logOmτ τ s) =
      (Fintype.card Emb : ℝ) * ∑ τ : Pl,
        ((∑ i, ph (Obj.ν j τ i)) - (∑ i, Obj.ν j τ i) * Obj.logOm) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    have hOm := (div_eq_iff hn.ne').mp (Obj.logOm_eq τ)
    rw [hOm]; ring
  have hsum_th : ∑ s : Emb, (Fintype.card Pl : ℝ) * Obj.g0 j * Obj.logth0 s =
      (Fintype.card Pl : ℝ) * Obj.g0 j * ∑ s : Emb, Obj.logth0 s := by
    rw [← Finset.mul_sum]
  rw [hsum_Om, hsum_th] at hsum
  have hK0_bound : (Fintype.card Pl : ℝ) * Obj.g0 j * (Obj.Cth * Obj.L) + K0 ≤
      Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L) := by
    have hN2 : 1 ≤ Obj.N ^ 2 := by nlinarith only [hN1]
    have hm1 : 1 ≤ Obj.m ^ 2 := by nlinarith only [Obj.m_ge_one]
    have hm2 : Obj.m ^ 2 ≤ Obj.m ^ 3 := by nlinarith only [Obj.m_ge_one, hm1]
    have hm3 : Obj.m ≤ Obj.m ^ 3 := by nlinarith only [Obj.m_ge_one, hm1]
    have hm4 : 1 ≤ Obj.m ^ 3 := le_trans Obj.m_ge_one hm3
    have hc6_nn : 0 ≤ Obj.c6 := Obj.c6_nonneg
    have hCT_nn : 0 ≤ Obj.CT := Obj.CT_nonneg
    have hC8_nn : 0 ≤ Obj.C8 := Obj.C8_nonneg
    have hC2_nn : 0 ≤ Obj.C2 := Obj.C2_nonneg
    have hC4_nn : 0 ≤ Obj.C4 := Obj.C4_nonneg
    have hCth_nn : 0 ≤ Obj.Cth := Obj.Cth_nonneg
    have hc5_nn : 0 ≤ Obj.c5 := Obj.c5_nonneg
    have q1 : (Fintype.card Pl : ℝ) * Obj.g0 j * (Obj.Cth * Obj.L) ≤
        Obj.f * Obj.N ^ 2 * (Obj.Cth * Obj.L) :=
      mul_le_mul_of_nonneg_right hcF (mul_nonneg hCth_nn hL0)
    have q2 : (Fintype.card Pl : ℝ) * Obj.g0 j *
        Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * Obj.g0 j) * Obj.v) ≤
        Obj.f * Obj.N ^ 2 * (Obj.c5 * Obj.La) := by
      have hlog := Obj.log8_le j
      by_cases hsign : 0 ≤ Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * Obj.g0 j) * Obj.v)
      · exact mul_le_mul hcF hlog hsign hF0
      · have hneg : Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * Obj.g0 j) * Obj.v) < 0 :=
          not_le.mp hsign
        have h1 : (Fintype.card Pl : ℝ) * Obj.g0 j *
            Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * Obj.g0 j) * Obj.v) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hg0_nn hneg.le
        have h2 : 0 ≤ Obj.f * Obj.N ^ 2 * (Obj.c5 * Obj.La) :=
          mul_nonneg hF0 (mul_nonneg hc5_nn hLa0)
        linarith only [h1, h2]
    have q3 : ∑ τ : Pl, (1 + 2 * Obj.g0 j * Real.log (2 * (∑ i, Obj.ν j τ i) + 2)) ≤
        Obj.f * Obj.N ^ 2 * ((2 * Obj.c6 + 1) * Obj.La) := by
      have hpt_τ : ∀ τ : Pl, 1 + 2 * Obj.g0 j * Real.log (2 * (∑ i, Obj.ν j τ i) + 2) ≤
          Obj.N ^ 2 * ((2 * Obj.c6 + 1) * Obj.La) := fun τ => by
        have h1 : (1 : ℝ) ≤ Obj.N ^ 2 * Obj.La := by nlinarith only [hN2, hLa1]
        have h2 : 2 * Obj.g0 j * Real.log (2 * (∑ i, Obj.ν j τ i) + 2) ≤
            2 * Obj.N ^ 2 * (Obj.c6 * Obj.La) := by
          have hg := Obj.g0_bounds j
          have hl := Obj.log2nu_le j τ
          by_cases hsign : 0 ≤ Real.log (2 * (∑ i, Obj.ν j τ i) + 2)
          · exact mul_le_mul (by linarith only [hg.2]) hl hsign (by linarith only [hN2])
          · have hneg : Real.log (2 * (∑ i, Obj.ν j τ i) + 2) ≤ 0 := (not_le.mp hsign).le
            have ha : 2 * Obj.g0 j * Real.log (2 * (∑ i, Obj.ν j τ i) + 2) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by linarith only [hg.1]) hneg
            have hb : 0 ≤ 2 * Obj.N ^ 2 * (Obj.c6 * Obj.La) := by
              exact mul_nonneg (by linarith only [hN2]) (mul_nonneg hc6_nn hLa0)
            linarith only [ha, hb]
        linarith only [h1, h2]
      calc ∑ τ : Pl, (1 + 2 * Obj.g0 j * Real.log (2 * (∑ i, Obj.ν j τ i) + 2))
          ≤ ∑ _τ : Pl, (Obj.N ^ 2 * ((2 * Obj.c6 + 1) * Obj.La)) :=
            Finset.sum_le_sum fun τ _ => hpt_τ τ
        _ = (Fintype.card Pl : ℝ) * (Obj.N ^ 2 * ((2 * Obj.c6 + 1) * Obj.La)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ Obj.f * (Obj.N ^ 2 * ((2 * Obj.c6 + 1) * Obj.La)) :=
            mul_le_mul_of_nonneg_right Obj.card_Pl_le (mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith only [hc6_nn]) hLa0))
        _ = Obj.f * Obj.N ^ 2 * ((2 * Obj.c6 + 1) * Obj.La) := by ring
    have q4 : 2 * (Obj.C2 * Obj.f * Obj.m ^ 2 * Obj.N ^ 2 * (Obj.logg + Obj.logT)) ≤
        2 * Obj.C2 * (Obj.CT + Obj.C8) * Obj.f * Obj.N ^ 2 * (Obj.m ^ 3 * Obj.L) := by
      have h1 : Obj.logg + Obj.logT ≤ (Obj.CT + Obj.C8) * Obj.m * Obj.L := by
        have hg_m : Obj.C8 * Obj.L ≤ Obj.C8 * Obj.m * Obj.L := by
          have h8L : 0 ≤ Obj.C8 * Obj.L := mul_nonneg hC8_nn hL0
          nlinarith only [Obj.m_ge_one, h8L]
        linarith only [Obj.logg_le, Obj.logT_le, hg_m]
      have h2 : Obj.m ^ 2 * (Obj.logg + Obj.logT) ≤ (Obj.CT + Obj.C8) * (Obj.m ^ 3 * Obj.L) := by
        have hmul := mul_le_mul_of_nonneg_left h1 (sq_nonneg Obj.m)
        linarith only [hmul]
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith only [hC2_nn]) hF0)
      linarith only [h3]
    have q5 : Obj.logh j + Obj.logh' j ≤
        2 * Obj.C4 * (1 + Obj.CT + Obj.C8) * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L) := by
      have h1 : Obj.L + Obj.logT + Obj.logg ≤
          Obj.La + (Obj.CT + Obj.C8) * (Obj.m ^ 3 * Obj.L) := by
        have hCTm : Obj.CT * Obj.m * Obj.L ≤ Obj.CT * (Obj.m ^ 3 * Obj.L) := by
          have hct0 : 0 ≤ Obj.CT * Obj.L := mul_nonneg hCT_nn hL0
          nlinarith only [hm3, hct0]
        have hC8m : Obj.C8 * Obj.L ≤ Obj.C8 * (Obj.m ^ 3 * Obj.L) := by
          have hc80 : 0 ≤ Obj.C8 * Obj.L := mul_nonneg hC8_nn hL0
          nlinarith only [hm4, hc80]
        linarith only [hLLa, Obj.logT_le, Obj.logg_le, hCTm, hC8m]
      have h2 : Obj.L + Obj.logT + Obj.logg ≤
          (1 + Obj.CT + Obj.C8) * (Obj.La + Obj.m ^ 3 * Obj.L) := by
        have hLa_nn : 0 ≤ (Obj.CT + Obj.C8) * Obj.La :=
          mul_nonneg (add_nonneg hCT_nn hC8_nn) hLa0
        have hm3L_nn : 0 ≤ Obj.m ^ 3 * Obj.L := mul_nonneg (pow_nonneg hm0 3) hL0
        linarith only [h1, hLa_nn, hm3L_nn]
      have h4F : 0 ≤ Obj.C4 * Obj.f * Obj.N ^ 2 := by
        rw [mul_assoc]
        exact mul_nonneg hC4_nn hF0
      have h3 : Obj.logh j ≤ Obj.C4 * Obj.f * Obj.N ^ 2 * ((1 + Obj.CT + Obj.C8) * (Obj.La + Obj.m ^ 3 * Obj.L)) :=
        (Obj.logh_le j).trans (mul_le_mul_of_nonneg_left h2 h4F)
      have h4 : Obj.logh' j ≤ Obj.C4 * Obj.f * Obj.N ^ 2 * ((1 + Obj.CT + Obj.C8) * (Obj.La + Obj.m ^ 3 * Obj.L)) :=
        (Obj.logh'_le j).trans (mul_le_mul_of_nonneg_left h2 h4F)
      linarith only [h3, h4]
    have hCth_m : Obj.f * Obj.N ^ 2 * (Obj.Cth * Obj.L) ≤ Obj.f * Obj.N ^ 2 * (Obj.Cth * Obj.La) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLLa hCth_nn) hF0
    have hLa_m3_nn : 0 ≤ Obj.La + Obj.m ^ 3 * Obj.L :=
      add_nonneg hLa0 (mul_nonneg (pow_nonneg hm0 3) hL0)
    have hcoeff : (Obj.Cth + Obj.c5 + 2 * Obj.c6 + 1 + 2 * Obj.C2 * (Obj.CT + Obj.C8) +
        2 * Obj.C4 * (1 + Obj.CT + Obj.C8)) * (Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L)) ≤
        Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L) := by
      have hmul := mul_le_mul_of_nonneg_right Obj.C0_ge_hK (mul_nonneg hF0 hLa_m3_nn)
      linarith only [hmul]
    have hLa_nonneg_m3 : 0 ≤ Obj.f * Obj.N ^ 2 * (Obj.Cth + Obj.c5 + 2 * Obj.c6 + 1) * (Obj.m ^ 3 * Obj.L) :=
      mul_nonneg (mul_nonneg hF0 (by linarith only [hCth_nn, hc5_nn, hc6_nn])) (mul_nonneg (pow_nonneg hm0 3) hL0)
    have h2C2_La : 0 ≤ 2 * Obj.C2 * (Obj.CT + Obj.C8) * Obj.f * Obj.N ^ 2 * Obj.La :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hC2_nn]) (add_nonneg hCT_nn hC8_nn)) hf0) (sq_nonneg Obj.N)) hLa0
    dsimp only [K0]
    linarith only [q1, q2, q3, q4, q5, hCth_m, hcoeff, hLa_nonneg_m3, h2C2_La]
  rw [Obj.hK_eq j, div_le_iff₀ hn]
  have hth' := (div_le_iff₀ hn).mp Obj.logth0_le
  have t1 := mul_le_mul_of_nonneg_left hth' hg0_nn
  have t2 := mul_le_mul_of_nonneg_left hK0_bound hn.le
  linarith only [hsum, t1, t2]

/-- **Step 4 (`archimedean_hP_bound`)**:
bounds `hP ≤ -(∑ t ∈ TT, aT t * logT) + C0 * (2 * (TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N^2) * La`. -/
theorem archimedean_hP_bound
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {D : ℕ} {J Pl Emb Sg : Type} [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    {TT : Finset Pl} [DecidablePred (· ∈ TT)] {nr : ℕ}
    (Obj : DivIneqObj K D J Pl Emb Sg TT nr) :
    Obj.hP ≤ -(∑ t ∈ TT, Obj.aT t * Obj.logT) +
      Obj.C0 * (2 * (TT.card : ℝ) * Obj.b' * Obj.N +
        Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N + Obj.f * Obj.N ^ 2) * Obj.La := by
  have hx0 : 0 < Obj.x := by linarith only [Obj.x_ge_one]
  have hrd0 : 0 < Obj.rd := by linarith only [Obj.rd_ge_one]
  have hL1 : 1 ≤ Obj.L := by rw [Obj.L_eq]; exact Real.one_le_rpow Obj.x_ge_one Obj.eps_pos.le
  have hL0 : 0 ≤ Obj.L := by linarith only [hL1]
  have ha0 : 0 < Obj.a := by rw [Obj.a_eq, Obj.b_eq]; exact mul_pos hx0 (Real.exp_pos Obj.L)
  have hLa_eq : Obj.La = Real.log Obj.x + Obj.L + Real.log Obj.rd := by
    rw [Obj.La_eq, Obj.a_eq, Obj.b_eq, Real.log_mul (mul_pos hx0 (Real.exp_pos Obj.L)).ne' hrd0.ne',
      Real.log_mul hx0.ne' (Real.exp_pos Obj.L).ne', Real.log_exp]
  have hLLa : Obj.L ≤ Obj.La := by
    linarith only [hLa_eq, Real.log_nonneg Obj.x_ge_one, Real.log_nonneg Obj.rd_ge_one]
  have hLa1 : 1 ≤ Obj.La := by linarith only [hL1, hLLa]
  have hLa0 : 0 ≤ Obj.La := by linarith only [hLa1]
  have hm0 : 0 ≤ Obj.m := by linarith only [Obj.m_ge_one]
  have hN1 : 1 ≤ Obj.N := by linarith only [Obj.k_ge_one, Obj.m_ge_one, Obj.km_le_N]
  have hN0 : 0 ≤ Obj.N := by linarith only [hN1]
  have hf0 : 0 ≤ Obj.f := by linarith only [Obj.f_ge_one]
  have hmN : Obj.m ≤ Obj.N := by linarith only [Obj.k_ge_one, Obj.km_le_N]
  have hS0 : 0 ≤ Obj.S := Obj.S_nonneg
  have hη0 : 0 ≤ Obj.η := Obj.η_nonneg
  have hb'0 : 0 ≤ Obj.b' := Obj.b'_nonneg
  have hCT0 : 0 ≤ Obj.CT := Obj.CT_nonneg
  have hCev0 : 0 ≤ Obj.Cev := Obj.Cev_nonneg
  have hlog2 : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos two_pos]
  have h2a_le : Real.log (2 * Obj.a) ≤ 2 * Obj.La := by
    rw [Real.log_mul two_ne_zero ha0.ne']
    have hloga : Real.log Obj.a ≤ Obj.La := by
      have : Real.log Obj.a = Real.log Obj.x + Obj.L := by
        rw [Obj.a_eq, Obj.b_eq, Real.log_mul hx0.ne' (Real.exp_pos Obj.L).ne', Real.log_exp]
      linarith only [this, hLa_eq, Real.log_nonneg Obj.rd_ge_one]
    linarith only [hlog2, hLa1, hloga]
  have h2a0 : 0 ≤ Real.log (2 * Obj.a) := by
    have ha1 : 1 ≤ Obj.a := by
      have hb1 : 1 ≤ Obj.b := by rw [Obj.b_eq]; exact Real.one_le_exp hL0
      rw [Obj.a_eq]; nlinarith only [Obj.x_ge_one, hb1]
    exact Real.log_nonneg (by linarith only [ha1])
  have hTN : Obj.logT ≤ Obj.CT * Obj.N * Obj.La := by
    have q1 : Obj.m * Obj.L ≤ Obj.N * Obj.La := mul_le_mul hmN hLLa hL0 hN0
    have q2 := mul_le_mul_of_nonneg_left q1 hCT0
    linarith only [Obj.logT_le, q2]
  have hT0' : 0 ≤ Obj.CT * Obj.N * Obj.La := mul_nonneg (mul_nonneg hCT0 hN0) hLa0
  have hTT : (Finset.univ.filter (· ∈ TT)) = TT := by ext τ; simp
  have hite : ∀ g : Pl → ℝ, (∑ τ : Pl, if τ ∈ TT then g τ else 0) = ∑ τ ∈ TT, g τ := fun g => by
    rw [← Finset.sum_filter, hTT]
  have hτ : ∀ τ : Pl, -(Obj.nτ τ * Obj.logT) + (2 * Obj.logc τ + Obj.logxi τ) ≤
      ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
        4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + Obj.N ^ 2 * Obj.La +
        (if τ ∈ TT then 2 * Obj.b' * (Obj.CT * Obj.N * Obj.La) + 24 * Obj.N * Obj.La * Obj.b' -
          Obj.aT τ * Obj.logT else 0) := by
    intro τ
    have r1 := Obj.logxi_le τ
    have r2 : Obj.N * (Obj.N - 1) / 2 * Real.log (2 * Obj.a) ≤ Obj.N * (Obj.N - 1) / 2 * (2 * Obj.La) :=
      mul_le_mul_of_nonneg_left h2a_le (div_nonneg (mul_nonneg hN0 (by linarith only [hN1])) zero_le_two)
    have r2' : Obj.N * (Obj.N - 1) / 2 * (2 * Obj.La) ≤ Obj.N ^ 2 * Obj.La := by
      have hNLa : 0 ≤ Obj.N * Obj.La := mul_nonneg hN0 hLa0
      linarith only [hNLa, show Obj.N * (Obj.N - 1) / 2 * (2 * Obj.La) = Obj.N ^ 2 * Obj.La - Obj.N * Obj.La by ring]
    have hNl : 0 ≤ (Obj.N - 1) * Real.log (2 * Obj.a) := mul_nonneg (by linarith only [hN1]) h2a0
    have hNl' : (Obj.N - 1) * Real.log (2 * Obj.a) ≤ Obj.N * (2 * Obj.La) :=
      mul_le_mul (by linarith only [hN1]) h2a_le h2a0 hN0
    have r4 := Obj.logc_le τ
    have r5 := Obj.D1_le τ
    have r6 := Obj.D0_le τ
    have r7 := Obj.nτ_eq τ
    have hmη0 : 0 ≤ Obj.m * Obj.η := mul_nonneg hm0 hη0
    have hmη_ge : Obj.η ≤ Obj.m * Obj.η := by nlinarith only [Obj.m_ge_one, hη0]
    by_cases hτT : τ ∈ TT
    · rw [if_pos hτT] at r6
      rw [if_pos hτT]
      have r8 := Obj.lam1_TT τ hτT
      have r9 := Obj.bT_le τ hτT
      have s1 : Obj.D1 τ ≤ 4 * Obj.S + 4 * Obj.m * Obj.η + 6 * Obj.b' := by
        linarith only [r5, r6, r9, hmη_ge, hb'0]
      have s2 : (Obj.N - 1) * Real.log (2 * Obj.a) * Obj.D1 τ ≤
          (Obj.N - 1) * Real.log (2 * Obj.a) * (4 * Obj.S + 4 * Obj.m * Obj.η + 6 * Obj.b') :=
        mul_le_mul_of_nonneg_left s1 hNl
      have s3 : (Obj.N - 1) * Real.log (2 * Obj.a) * (4 * Obj.S + 4 * Obj.m * Obj.η + 6 * Obj.b') ≤
          Obj.N * (2 * Obj.La) * (4 * Obj.S + 4 * Obj.m * Obj.η + 6 * Obj.b') :=
        mul_le_mul_of_nonneg_right hNl' (by linarith only [hS0, hmη0, hb'0])
      have s3_exp : 2 * (Obj.N * (2 * Obj.La) * (4 * Obj.S + 4 * Obj.m * Obj.η + 6 * Obj.b')) =
          4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + 24 * Obj.N * Obj.La * Obj.b' := by ring
      have u1 : (Obj.N - Obj.k) / 2 + Obj.D0 τ ≤ (Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η + 2 * Obj.b' := by
        linarith only [r6, r9, Obj.k_ge_one, hb'0]
      have u2 : ((Obj.N - Obj.k) / 2 + Obj.D0 τ) * Obj.logT ≤
          ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η + 2 * Obj.b') * (Obj.CT * Obj.N * Obj.La) :=
        mul_le_mul u1 hTN Obj.logT_nonneg (by linarith only [hN1, hS0, hmη0, hb'0])
      have u2_exp : ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η + 2 * Obj.b') * (Obj.CT * Obj.N * Obj.La) =
          ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
            2 * Obj.b' * (Obj.CT * Obj.N * Obj.La) := by ring
      have hlin : -(Obj.nτ τ * Obj.logT) = ((Obj.N - Obj.k) / 2 + Obj.D0 τ) * Obj.logT - Obj.aT τ * Obj.logT := by
        rw [r7, r8]; ring
      linarith only [r1, r2, r2', r4, s2, s3, s3_exp, u2, u2_exp, hlin]
    · rw [if_neg hτT] at r6
      rw [if_neg hτT]
      have r8 := Obj.lam1_not_TT τ hτT
      have s1 : Obj.D1 τ ≤ 4 * Obj.S + 4 * Obj.m * Obj.η := by linarith only [r5, r6, hmη_ge]
      have s2 : (Obj.N - 1) * Real.log (2 * Obj.a) * Obj.D1 τ ≤
          (Obj.N - 1) * Real.log (2 * Obj.a) * (4 * Obj.S + 4 * Obj.m * Obj.η) :=
        mul_le_mul_of_nonneg_left s1 hNl
      have s3 : (Obj.N - 1) * Real.log (2 * Obj.a) * (4 * Obj.S + 4 * Obj.m * Obj.η) ≤
          Obj.N * (2 * Obj.La) * (4 * Obj.S + 4 * Obj.m * Obj.η) :=
        mul_le_mul_of_nonneg_right hNl' (by linarith only [hS0, hmη0])
      have s3_exp : 2 * (Obj.N * (2 * Obj.La) * (4 * Obj.S + 4 * Obj.m * Obj.η)) =
          4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) := by ring
      have u1 : -(Obj.lam1 τ - Obj.D0 τ) ≤ (Obj.N - 1) / 2 + Obj.m * Obj.η := by
        linarith only [r6, r8, hS0]
      have u2 : -(Obj.lam1 τ - Obj.D0 τ) * Obj.logT ≤ ((Obj.N - 1) / 2 + Obj.m * Obj.η) * Obj.logT :=
        mul_le_mul_of_nonneg_right u1 Obj.logT_nonneg
      have u3 : ((Obj.N - 1) / 2 + Obj.m * Obj.η) * Obj.logT ≤
          ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) :=
        mul_le_mul (by linarith only [hS0]) hTN Obj.logT_nonneg
          (by linarith only [hN1, hS0, hmη0])
      have hlin : -(Obj.nτ τ * Obj.logT) = -(Obj.lam1 τ - Obj.D0 τ) * Obj.logT := by
        rw [r7]; ring
      linarith only [r1, r2, r2', r4, s2, s3, s3_exp, u2, u3, hlin]
  have hsumτ := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hτ τ
  have hLτ : ∑ τ : Pl, (-(Obj.nτ τ * Obj.logT) + (2 * Obj.logc τ + Obj.logxi τ)) =
      -(∑ τ : Pl, Obj.nτ τ * Obj.logT) + ∑ τ : Pl, (2 * Obj.logc τ + Obj.logxi τ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hR : ∑ τ : Pl, (((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
        4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + Obj.N ^ 2 * Obj.La +
        (if τ ∈ TT then 2 * Obj.b' * (Obj.CT * Obj.N * Obj.La) + 24 * Obj.N * Obj.La * Obj.b' -
          Obj.aT τ * Obj.logT else 0)) =
      (Fintype.card Pl : ℝ) * (((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
        4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + Obj.N ^ 2 * Obj.La) +
        ((TT.card : ℝ) * (2 * Obj.b' * (Obj.CT * Obj.N * Obj.La) + 24 * Obj.N * Obj.La * Obj.b') -
          ∑ τ ∈ TT, Obj.aT τ * Obj.logT) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hite,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hW0 : 0 ≤ ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
      4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + Obj.N ^ 2 * Obj.La := by
    have hmη : 0 ≤ Obj.m * Obj.η := mul_nonneg hm0 hη0
    have hN1_nn : 0 ≤ (Obj.N - 1) / 2 := by linarith only [hN1]
    have sA : 0 ≤ ((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) :=
      mul_nonneg (by linarith only [hN1_nn, hS0, hmη]) hT0'
    have sB : 0 ≤ 4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) :=
      mul_nonneg (mul_nonneg (by linarith only [hN0]) hLa0) (by linarith only [hS0, hmη])
    have sC : 0 ≤ Obj.N ^ 2 * Obj.La := mul_nonneg (sq_nonneg Obj.N) hLa0
    linarith only [sA, sB, sC]
  have hfW := mul_le_mul_of_nonneg_right Obj.card_Pl_le hW0
  have hX1 : 0 ≤ Obj.f * Obj.N ^ 2 * Obj.La := mul_nonneg (mul_nonneg hf0 (sq_nonneg Obj.N)) hLa0
  have hX2 : 0 ≤ Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N * Obj.La := by
    have hmη : 0 ≤ Obj.m * Obj.η := mul_nonneg hm0 hη0
    exact mul_nonneg (mul_nonneg (mul_nonneg hf0 (add_nonneg hmη hS0)) hN0) hLa0
  have hX3 : 0 ≤ (TT.card : ℝ) * Obj.b' * Obj.N * Obj.La :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hb'0) hN0) hLa0
  have g1 : (Obj.CT / 2 + 1 + Obj.Cev) * (Obj.f * Obj.N ^ 2 * Obj.La) ≤
      Obj.C0 * (Obj.f * Obj.N ^ 2 * Obj.La) := by
    have hle : Obj.CT / 2 + 1 + Obj.Cev ≤ Obj.C0 := by linarith only [Obj.C0_ge_hP, hCT0]
    exact mul_le_mul_of_nonneg_right hle hX1
  have g2 : (Obj.CT + 16) * (Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N * Obj.La) ≤
      Obj.C0 * (Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N * Obj.La) :=
    mul_le_mul_of_nonneg_right (by linarith only [Obj.C0_ge_hP, hCev0]) hX2
  have g3 : (2 * Obj.CT + 24) * ((TT.card : ℝ) * Obj.b' * Obj.N * Obj.La) ≤
      (2 * Obj.C0) * ((TT.card : ℝ) * Obj.b' * Obj.N * Obj.La) := by
    have hle : 2 * Obj.CT + 24 ≤ 2 * Obj.C0 := by linarith only [Obj.C0_ge_hP, hCev0]
    exact mul_le_mul_of_nonneg_right hle hX3
  have hLτ_le : -(∑ τ : Pl, Obj.nτ τ * Obj.logT) + ∑ τ : Pl, (2 * Obj.logc τ + Obj.logxi τ) ≤
      (Fintype.card Pl : ℝ) * (((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
        4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + Obj.N ^ 2 * Obj.La) +
        ((TT.card : ℝ) * (2 * Obj.b' * (Obj.CT * Obj.N * Obj.La) + 24 * Obj.N * Obj.La * Obj.b') -
          ∑ τ ∈ TT, Obj.aT τ * Obj.logT) := by
    linarith only [hsumτ, hLτ, hR]
  have h1_expand : Obj.f * (((Obj.N - 1) / 2 + Obj.S + Obj.m * Obj.η) * (Obj.CT * Obj.N * Obj.La) +
        4 * Obj.N * Obj.La * (4 * Obj.S + 4 * Obj.m * Obj.η) + Obj.N ^ 2 * Obj.La) +
      Obj.Cev * Obj.f * Obj.N ^ 2 * Obj.La ≤
      (Obj.CT / 2 + 1 + Obj.Cev) * (Obj.f * Obj.N ^ 2 * Obj.La) +
      (Obj.CT + 16) * (Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N * Obj.La) := by
    have hCT_neg : 0 ≤ Obj.CT * Obj.f * Obj.N * Obj.La / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCT0 hf0) hN0) hLa0) zero_le_two
    linarith only [hCT_neg]
  linarith only [Obj.hP_le, Obj.ev_le, hfW, g1, g2, g3, hLτ_le, h1_expand]

/-- **Step 5 (`divisor_ineq_algebraic_assembly`)**:
combines `Lpass`, `Eb`, `hK`, `hP`, `mlam`, `phν - fa`, and `nν` into the raw divisor inequality
before error absorption. -/
theorem divisor_ineq_algebraic_assembly
    {J Pl : Type*} [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (m k : ℝ) (hm : (Fintype.card J : ℝ) = m)
    (hw : ∀ j ρ, 0 ≤ w j ρ)
    (h1 : muC ≤ mu0 + Lpass)
    (h2 : mu0 ≤ (∑ j : J, ∑ ρ : Pl, pq j * w j ρ * logOm) + 2 * Fo + Eb)
    (h3 : hu = hP + (∑ j : J, hK j) - mlam)
    (h4 : ∀ j, hK j ≤ (∑ ρ : Pl, (phν j ρ - nν j ρ * logOm)) + eK j)
    (h5 : (∑ j : J, ∑ ρ : Pl, fa j ρ) - e6 ≤ mlam)
    (h6 : hP ≤ -(∑ t ∈ TT, aT t * logT) + eP)
    (h7 : ∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ)
    (h8 : ∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) :
    muC + hu - 2 * Fo ≤
      (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
      (Lpass + Eb + (∑ j : J, eK j) + e6 + eP + (∑ j : J, ∑ ρ : Pl, eE j ρ) +
        (∑ j : J, ∑ ρ : Pl, |pq j - k| * w j ρ * |logOm|) +
        (∑ j : J, ∑ ρ : Pl, |δ j ρ| * |logOm|)) := by
  have hTT : (Finset.univ.filter (· ∈ TT)) = TT := by ext t; simp
  have hite : ∀ g : Pl → ℝ, (∑ ρ : Pl, if ρ ∈ TT then g ρ else 0) = ∑ t ∈ TT, g t := fun g => by
    rw [← Finset.sum_filter, hTT]
  have hsum_hK : ∑ j : J, hK j ≤
      (∑ j : J, ∑ ρ : Pl, (phν j ρ - nν j ρ * logOm)) + ∑ j : J, eK j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => h4 j
  have hhu_le : hu ≤ (∑ j : J, ∑ ρ : Pl, (phν j ρ - fa j ρ - nν j ρ * logOm)) -
      (∑ t ∈ TT, aT t * logT) + (∑ j : J, eK j) + e6 + eP := by
    have hsplit : ∑ j : J, ∑ ρ : Pl, (phν j ρ - fa j ρ - nν j ρ * logOm) =
        (∑ j : J, ∑ ρ : Pl, (phν j ρ - nν j ρ * logOm)) - ∑ j : J, ∑ ρ : Pl, fa j ρ := by
      simp only [Finset.sum_sub_distrib]
      ring
    linarith only [h3, h5, h6, hsum_hK, hsplit]
  have hph_sum : ∑ j : J, ∑ ρ : Pl, (phν j ρ - fa j ρ) ≤
      m * (∑ t ∈ TT, ph (aT t)) + ∑ j : J, ∑ ρ : Pl, eE j ρ := by
    calc ∑ j : J, ∑ ρ : Pl, (phν j ρ - fa j ρ)
        ≤ ∑ j : J, ∑ ρ : Pl, ((if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ρ _ => h7 j ρ
      _ = (∑ _j : J, ∑ t ∈ TT, ph (aT t)) + ∑ j : J, ∑ ρ : Pl, eE j ρ := by
          simp_rw [Finset.sum_add_distrib, hite]
      _ = m * (∑ t ∈ TT, ph (aT t)) + ∑ j : J, ∑ ρ : Pl, eE j ρ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
  have hnu_diff : ∀ j ρ, pq j * w j ρ * logOm - nν j ρ * logOm ≤
      -(if ρ ∈ TT then aT ρ * logOm else 0) + |pq j - k| * w j ρ * |logOm| +
        |δ j ρ| * |logOm| := fun j ρ => by
    rw [h8 j ρ]
    have h1' : (pq j - k) * w j ρ * logOm ≤ |(pq j - k) * w j ρ * logOm| := le_abs_self _
    have h2' : -(δ j ρ * logOm) ≤ |-(δ j ρ * logOm)| := le_abs_self _
    have h3' : |(pq j - k) * w j ρ * logOm| = |pq j - k| * w j ρ * |logOm| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hw j ρ)]
    have h4' : |-(δ j ρ * logOm)| = |δ j ρ| * |logOm| := by
      rw [abs_neg, abs_mul]
    have hite_mul : (if ρ ∈ TT then aT ρ else 0) * logOm =
        if ρ ∈ TT then aT ρ * logOm else 0 := by
      split_ifs <;> ring
    linarith only [h1', h2', h3', h4', hite_mul]
  have hnu_sum : (∑ j : J, ∑ ρ : Pl, pq j * w j ρ * logOm) -
      (∑ j : J, ∑ ρ : Pl, nν j ρ * logOm) ≤
      -(m * ∑ t ∈ TT, aT t * logOm) +
      (∑ j : J, ∑ ρ : Pl, |pq j - k| * w j ρ * |logOm|) +
      (∑ j : J, ∑ ρ : Pl, |δ j ρ| * |logOm|) := by
    have hsub : (∑ j : J, ∑ ρ : Pl, pq j * w j ρ * logOm) -
        (∑ j : J, ∑ ρ : Pl, nν j ρ * logOm) =
        ∑ j : J, ∑ ρ : Pl, (pq j * w j ρ * logOm - nν j ρ * logOm) := by
      simp only [Finset.sum_sub_distrib]
    have hle := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum fun ρ (_ : ρ ∈ Finset.univ) => hnu_diff j ρ
    have hrhs : ∑ j : J, ∑ ρ : Pl,
          (-(if ρ ∈ TT then aT ρ * logOm else 0) + |pq j - k| * w j ρ * |logOm| +
            |δ j ρ| * |logOm|) =
        -(m * ∑ t ∈ TT, aT t * logOm) +
        (∑ j : J, ∑ ρ : Pl, |pq j - k| * w j ρ * |logOm|) +
        (∑ j : J, ∑ ρ : Pl, |δ j ρ| * |logOm|) := by
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, hite, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, hm]
    linarith only [hsub, hle, hrhs]
  have hmain_rew : (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) =
      m * (∑ t ∈ TT, ph (aT t)) - m * (∑ t ∈ TT, aT t * logOm) - ∑ t ∈ TT, aT t * logT := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hsplit_all : (∑ j : J, ∑ ρ : Pl, (phν j ρ - fa j ρ - nν j ρ * logOm)) =
      (∑ j : J, ∑ ρ : Pl, (phν j ρ - fa j ρ)) - ∑ j : J, ∑ ρ : Pl, nν j ρ * logOm := by
    simp only [Finset.sum_sub_distrib]
  linarith only [h1, h2, hhu_le, hph_sum, hnu_sum, hmain_rew, hsplit_all]

/-- **Step 6 (`div_ineq_of_covol_and_gluing`)**:
**Main Theorem**: derives the complete `DivIneqObj` divisor inequality directly from:
1. Base-level covolume + product-formula slope bounds (`Obj.base : BaseLevelBoundsWithCovolume`),
2. Rank-partition passage concentration (`passage_corank_bound`),
3. Archimedean period height bounds (`archimedean_hK_bound`, `archimedean_hP_bound`),
4. Finite-place gluing & error absorption (`divisor_ineq_algebraic_assembly` + `divisor_ineq_error_absorption`)!

Ready for M5 Wave 3 (`Stage14M5_IndefUseDivCore`). -/
theorem div_ineq_of_covol_and_gluing
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {D : ℕ} {J Pl Emb Sg : Type} [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    {TT : Finset Pl} [DecidablePred (· ∈ TT)] {nr : ℕ}
    (Obj : DivIneqObj K D J Pl Emb Sg TT nr) :
    Obj.muC + Obj.hu - 2 * Obj.Fo ≤
      ∑ t ∈ TT, (Obj.m * (ph (Obj.aT t) - Obj.aT t * Obj.logOm) - Obj.aT t * Obj.logT) +
      (50 * Obj.C0 + 10) * ((TT.card : ℝ) * Obj.a * Obj.La + Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
  have hx0 : 0 < Obj.x := by linarith only [Obj.x_ge_one]
  have hL1 : 1 ≤ Obj.L := by rw [Obj.L_eq]; exact Real.one_le_rpow Obj.x_ge_one Obj.eps_pos.le
  have hL0 : 0 ≤ Obj.L := by linarith only [hL1]
  have hb1 : 1 ≤ Obj.b := by rw [Obj.b_eq]; exact Real.one_le_exp hL0
  have hb0 : 0 ≤ Obj.b := by linarith only [hb1]
  have ha0 : 0 < Obj.a := by rw [Obj.a_eq, Obj.b_eq]; exact mul_pos hx0 (Real.exp_pos Obj.L)
  have hrd0 : 0 < Obj.rd := by linarith only [Obj.rd_ge_one]
  have hLa_eq : Obj.La = Real.log Obj.x + Obj.L + Real.log Obj.rd := by
    rw [Obj.La_eq, Obj.a_eq, Obj.b_eq, Real.log_mul (mul_pos hx0 (Real.exp_pos Obj.L)).ne' hrd0.ne',
      Real.log_mul hx0.ne' (Real.exp_pos Obj.L).ne', Real.log_exp]
  have hLa_le_3L : Obj.La ≤ 3 * Obj.L := by
    linarith only [hLa_eq, Obj.log_x_le, Obj.log_rd_le]
  have hLLa : Obj.L ≤ Obj.La := by
    linarith only [hLa_eq, Real.log_nonneg Obj.x_ge_one, Real.log_nonneg Obj.rd_ge_one]
  have hLa1 : 1 ≤ Obj.La := by linarith only [hL1, hLLa]
  have hLa0 : 0 ≤ Obj.La := by linarith only [hLa1]
  have hm0 : 0 ≤ Obj.m := by linarith only [Obj.m_ge_one]
  have hf0 : 0 ≤ Obj.f := by linarith only [Obj.f_ge_one]
  have hk0 : 0 ≤ Obj.k := by linarith only [Obj.k_ge_one]
  have hN1 : 1 ≤ Obj.N := by linarith only [Obj.k_ge_one, Obj.m_ge_one, Obj.km_le_N]
  have hN0 : 0 ≤ Obj.N := by linarith only [hN1]
  have hS0 : 0 ≤ Obj.S := Obj.S_nonneg
  have hη0 : 0 ≤ Obj.η := Obj.η_nonneg
  have hxe_ge1 : 1 ≤ Obj.xe := le_trans (by rw [← Obj.L_eq]; exact hL1) Obj.xe_ge
  have hxe0 : 0 ≤ Obj.xe := by linarith only [hxe_ge1]
  have hB0_eq : Obj.B0 = Obj.f * Obj.m * Obj.b * Obj.L := by rw [Obj.B0_eq, Obj.L_eq]
  have hB0_nn : 0 ≤ Obj.B0 := by
    rw [hB0_eq]
    exact mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb0) hL0
  have hC0_nn : 0 ≤ Obj.C0 := by linarith only [Obj.C0_ge_25_2]
  have hBN_xe : Obj.B0 ≤ Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe := by
    have hmxe : 1 ≤ Obj.m * Obj.xe := by nlinarith only [Obj.m_ge_one, hxe_ge1]
    have hBN_nn : 0 ≤ Obj.B0 + Obj.Nc := add_nonneg hB0_nn Obj.Nc_nonneg
    nlinarith only [hmxe, hBN_nn, Obj.Nc_nonneg]
  have h1_le_BN : 1 ≤ Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe := by
    have h1_le_B0 : 1 ≤ Obj.B0 := by
      rw [hB0_eq]
      have hfm : 1 ≤ Obj.f * Obj.m := by nlinarith only [Obj.f_ge_one, Obj.m_ge_one]
      have hfb : 1 ≤ Obj.f * Obj.m * Obj.b := by nlinarith only [hfm, hb1]
      nlinarith only [hfb, hL1]
    linarith only [h1_le_B0, hBN_xe]
  have hb_le_BN : Obj.b ≤ Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe := by
    have hb_le_B0 : Obj.b ≤ Obj.B0 := by
      rw [hB0_eq]
      have hfm : 1 ≤ Obj.f * Obj.m := by nlinarith only [Obj.f_ge_one, Obj.m_ge_one]
      have hfmL : 1 ≤ Obj.f * Obj.m * Obj.L := by nlinarith only [hfm, hL1]
      nlinarith only [hfmL, hb0]
    linarith only [hb_le_B0, hBN_xe]
  -- Step 1: Base-level covolume bound (`mu0 ≤ ... + 2 * Fo + Eb`)
  obtain ⟨Eb, hmu0_base, hEb_le⟩ := base_covolume_mu0_bound Obj
  -- Upper bound `mu0 ≤ logκ + p1 * b` for passage
  have hmu0_pass : Obj.mu0 ≤ Obj.logκ +
      (2 * Obj.m * Obj.f * Obj.N * Obj.La + 2 * Obj.pF +
        Obj.C0 * Obj.m * Obj.xe * (Obj.f * Obj.m * Obj.xe + Obj.pN)) * Obj.b := by
    have hlogκ0 : Obj.logκ = 0 := by rw [Obj.logκ_eq, Obj.meanLog_kappa_eq]
    have hpq_sum : ∑ j : J, ∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm ≤
        2 * Obj.m * Obj.f * Obj.N * Obj.La * Obj.b := by
      have hpq_le : ∀ j, |Obj.pq j| ≤ Obj.N := fun j => by
        have h1 := (abs_le.mp (Obj.pq_close j)).1
        have h2 := (abs_le.mp (Obj.pq_close j)).2
        rw [abs_le]
        constructor <;> linarith only [h1, h2, Obj.km_le_N, Obj.k_ge_one, Obj.m_ge_one]
      have hpt : ∀ j ρ, Obj.pq j * Obj.w j ρ * Obj.logOm ≤ 2 * Obj.N * Obj.La * Obj.b :=
        fun j ρ => by
          have h1 : Obj.pq j * Obj.w j ρ * Obj.logOm ≤ |Obj.pq j * Obj.w j ρ * Obj.logOm| :=
            le_abs_self _
          rw [abs_mul, abs_mul, abs_of_nonneg (Obj.w_bounds j ρ).1] at h1
          have h2 : |Obj.pq j| * Obj.w j ρ ≤ Obj.N * (2 * Obj.b) :=
            mul_le_mul (hpq_le j) (Obj.w_bounds j ρ).2 (Obj.w_bounds j ρ).1 hN0
          have h3 : |Obj.pq j| * Obj.w j ρ * |Obj.logOm| ≤ (Obj.N * (2 * Obj.b)) * Obj.La :=
            mul_le_mul h2 Obj.logOm_abs_le (abs_nonneg _) (mul_nonneg hN0 (by linarith only [hb0]))
          linarith only [h1, h3]
      calc ∑ j : J, ∑ ρ : Pl, Obj.pq j * Obj.w j ρ * Obj.logOm
          ≤ ∑ _j : J, ∑ _ρ : Pl, (2 * Obj.N * Obj.La * Obj.b) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ρ _ => hpt j ρ
        _ = (Fintype.card J : ℝ) * ((Fintype.card Pl : ℝ) * (2 * Obj.N * Obj.La * Obj.b)) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ Obj.m * (Obj.f * (2 * Obj.N * Obj.La * Obj.b)) := by
            rw [Obj.card_J_eq]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right Obj.card_Pl_le (mul_nonneg (mul_nonneg (by linarith only [hN0]) hLa0) hb0)) hm0
        _ = 2 * Obj.m * Obj.f * Obj.N * Obj.La * Obj.b := by ring
    have hEb_b : Eb ≤ Obj.C0 * Obj.m * Obj.xe * (Obj.f * Obj.m * Obj.xe + Obj.pN) * Obj.b := by
      have hB0_b : Obj.B0 ≤ Obj.f * Obj.m * Obj.xe * Obj.b := by
        rw [Obj.B0_eq]
        have h1 : Obj.f * Obj.m * Obj.b * Obj.x ^ Obj.eps ≤ Obj.f * Obj.m * Obj.b * Obj.xe :=
          mul_le_mul_of_nonneg_left Obj.xe_ge (mul_nonneg (mul_nonneg hf0 hm0) hb0)
        linarith only [h1]
      have hsum_b : Obj.B0 + Obj.Nc ≤ (Obj.f * Obj.m * Obj.xe + Obj.pN) * Obj.b := by
        linarith only [hB0_b, Obj.Nc_le]
      have h1 : Obj.C0 * Obj.m * Obj.xe * (Obj.B0 + Obj.Nc) ≤
          Obj.C0 * Obj.m * Obj.xe * ((Obj.f * Obj.m * Obj.xe + Obj.pN) * Obj.b) :=
        mul_le_mul_of_nonneg_left hsum_b (mul_nonneg (mul_nonneg hC0_nn hm0) hxe0)
      linarith only [hEb_le, h1]
    linarith only [hmu0_base, hlogκ0, hpq_sum, hEb_b, Obj.Fo_le]
  -- Step 2: Passage bound (`muC ≤ mu0 + 1 + C0 * lam0`)
  have hpass := passage_corank_bound Obj.rkS Obj.nS Obj.dg Obj.muC Obj.mu0 Obj.muP0 Obj.muPs
    Obj.HH0 Obj.lam0 Obj.logκ Obj.f Obj.r_pass Obj.g_pass Obj.k Obj.b
    (2 * Obj.m * Obj.f * Obj.N * Obj.La + 2 * Obj.pF +
      Obj.C0 * Obj.m * Obj.xe * (Obj.f * Obj.m * Obj.xe + Obj.pN)) Obj.p2 Obj.C0
    Obj.nbar Obj.nbar_pos Obj.lam0_nonneg Obj.rkS_nonneg Obj.sum_rkS_pos
    hf0 Obj.r_pass_nonneg (by
      have hkb_pos : 0 < (Obj.k * Obj.b) ^ 8 := pow_pos (mul_pos (by linarith only [Obj.k_ge_one]) (by linarith only [hb1])) 8
      linarith only [hkb_pos, Obj.kb8_le_g])
    Obj.nS_bounds Obj.muP0_close Obj.muPs_close Obj.dg_le Obj.muPs_ge Obj.muP0_le
    Obj.k_ge_one hb1 Obj.lam0_le_b Obj.HH0_le hmu0_pass Obj.fr_bound7 Obj.fr_bound8 Obj.kb8_le_g
    Obj.C0_ge_25_2
  have hLpass : Obj.muC ≤ Obj.mu0 + (1 + Obj.C0 * Obj.lam0) := by linarith only [hpass.2.2.2]
  -- Step 3: Archimedean `hK` and `hP` bounds
  have hhK := archimedean_hK_bound Obj
  have hhP := archimedean_hP_bound Obj
  -- Step 4: Raw algebraic assembly
  have hraw := divisor_ineq_algebraic_assembly TT Obj.muC Obj.mu0 Obj.Fo Obj.hu Obj.hP Obj.mlam
    Obj.logT Obj.hK Obj.aT (fun j ρ => ∑ i, ph (Obj.ν j ρ i)) (fun j ρ => ∑ i, Obj.ν j ρ i)
    Obj.fa (1 + Obj.C0 * Obj.lam0) Eb Obj.e6
    (Obj.C0 * (2 * (TT.card : ℝ) * Obj.b' * Obj.N +
      Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N + Obj.f * Obj.N ^ 2) * Obj.La)
    Obj.logOm (fun _ => Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L))
    Obj.pq Obj.w Obj.eE Obj.δ Obj.m Obj.k Obj.card_J_eq (fun j ρ => (Obj.w_bounds j ρ).1)
    hLpass hmu0_base Obj.hu_eq hhK Obj.mlam_ge hhP Obj.phν_sub_fa_le Obj.sum_ν_eq
  -- Step 5: Error absorption into `(50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)`
  have hS_le_b : Obj.S ≤ Obj.b := by
    have h1 : Obj.S ≤ Obj.k * Obj.S := by nlinarith only [Obj.k_ge_one, hS0]
    have h2 : Obj.k * Obj.S ≤ Obj.w'' := Obj.k_S_le_w''
    have hw0 : 0 ≤ Obj.w'' := le_trans (mul_nonneg hk0 hS0) h2
    have h3 : Obj.w'' ≤ Obj.N * Obj.w'' := by nlinarith only [hN1, hw0]
    linarith only [h1, h2, h3, Obj.N_w''_le_b]
  have hmttη_le_b : Obj.m * (Obj.tt + 1) * Obj.η ≤ Obj.b := by
    have hw0 : 0 ≤ Obj.w'' :=
      le_trans (mul_nonneg (mul_nonneg hm0 (by linarith only [Obj.tt_nonneg])) hη0) Obj.m_tt_η_le_w''
    have h1 : Obj.w'' ≤ Obj.N * Obj.w'' := by nlinarith only [hN1, hw0]
    linarith only [Obj.m_tt_η_le_w'', h1, Obj.N_w''_le_b]
  have hmη_le_w'' : Obj.m * Obj.η ≤ Obj.w'' := by
    have h1 : Obj.m * Obj.η ≤ Obj.m * (Obj.tt + 1) * Obj.η := by
      have hmη0 : 0 ≤ Obj.m * Obj.η := mul_nonneg hm0 hη0
      nlinarith only [Obj.tt_nonneg, hmη0]
    exact h1.trans Obj.m_tt_η_le_w''
  have hN2L_le_b : Obj.N ^ 2 * Obj.L ≤ Obj.b := by
    have hm3 : 1 ≤ Obj.m ^ 3 := by
      have hm2 : 1 ≤ Obj.m ^ 2 := by nlinarith only [Obj.m_ge_one]
      nlinarith only [Obj.m_ge_one, hm2]
    have h1 : Obj.N ^ 2 * Obj.L ≤ Obj.m ^ 3 * Obj.N ^ 2 * Obj.L := by
      have hN2L0 : 0 ≤ Obj.N ^ 2 * Obj.L := mul_nonneg (sq_nonneg Obj.N) hL0
      nlinarith only [hm3, hN2L0]
    exact h1.trans Obj.m3_N2_L_le_b
  have hN2La_le_3b : Obj.N ^ 2 * Obj.La ≤ 3 * Obj.b := by
    have h1 : Obj.N ^ 2 * Obj.La ≤ Obj.N ^ 2 * (3 * Obj.L) :=
      mul_le_mul_of_nonneg_left hLa_le_3L (sq_nonneg Obj.N)
    linarith only [h1, hN2L_le_b]
  have hmfbL_le_B0 : Obj.m * Obj.f * Obj.b * Obj.L = Obj.B0 := by
    rw [hB0_eq]; ring
  have hmB0_le : Obj.m * Obj.B0 ≤ Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe := by
    have h1 : Obj.B0 ≤ Obj.B0 + Obj.Nc := by linarith only [Obj.Nc_nonneg]
    have h2 : Obj.m * Obj.B0 ≤ Obj.m * (Obj.B0 + Obj.Nc) := mul_le_mul_of_nonneg_left h1 hm0
    have h3 : 0 ≤ Obj.m * (Obj.B0 + Obj.Nc) := mul_nonneg hm0 (add_nonneg hB0_nn Obj.Nc_nonneg)
    nlinarith only [h2, h3, hxe_ge1]
  have hfb_le_B0 : Obj.f * Obj.b ≤ Obj.B0 := by
    rw [hB0_eq]
    have hmL : 1 ≤ Obj.m * Obj.L := by nlinarith only [Obj.m_ge_one, hL1]
    have hfb0 : 0 ≤ Obj.f * Obj.b := mul_nonneg hf0 hb0
    nlinarith only [hmL, hfb0]
  -- Error 1: `Lpass ≤ (C0 + 1) * m * (B0 + Nc) * xe`
  have hErr1 : 1 + Obj.C0 * Obj.lam0 ≤ (Obj.C0 + 1) * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have hlam : Obj.C0 * Obj.lam0 ≤ Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) :=
      mul_le_mul_of_nonneg_left (Obj.lam0_le_b.trans hb_le_BN) hC0_nn
    linarith only [h1_le_BN, hlam]
  -- Error 2: `Eb ≤ C0 * m * (B0 + Nc) * xe`
  have hErr2 : Eb ≤ Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    linarith only [hEb_le]
  -- Error 3: `∑ j, eK j ≤ 4 * C0 * m * (B0 + Nc) * xe`
  have hErr3 : (∑ _j : J, Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L)) ≤
      4 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have h1 : Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L) ≤ 4 * Obj.B0 := by
      have hA : Obj.f * Obj.N ^ 2 * Obj.La ≤ 3 * Obj.f * Obj.b := by
        have := mul_le_mul_of_nonneg_left hN2La_le_3b hf0
        linarith only [this]
      have hB : Obj.f * (Obj.m ^ 3 * Obj.N ^ 2 * Obj.L) ≤ Obj.f * Obj.b :=
        mul_le_mul_of_nonneg_left Obj.m3_N2_L_le_b hf0
      linarith only [hA, hB, hfb_le_B0]
    have h2 : Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L) ≤ 4 * Obj.C0 * Obj.B0 := by
      have := mul_le_mul_of_nonneg_left h1 hC0_nn
      linarith only [this]
    calc (∑ _j : J, Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L))
        = Obj.m * (Obj.C0 * Obj.f * Obj.N ^ 2 * (Obj.La + Obj.m ^ 3 * Obj.L)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Obj.card_J_eq]
      _ ≤ Obj.m * (4 * Obj.C0 * Obj.B0) := mul_le_mul_of_nonneg_left h2 hm0
      _ = 4 * Obj.C0 * (Obj.m * Obj.B0) := by ring
      _ ≤ 4 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) :=
          mul_le_mul_of_nonneg_left hmB0_le (by linarith only [hC0_nn])
  -- Error 4: `e6 ≤ 3 * C0 * m * (B0 + Nc) * xe`
  have hErr4 : Obj.e6 ≤ 3 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have h1 : Obj.C0 * Obj.m * Obj.f * Obj.N ^ 2 * Obj.La ≤ 3 * Obj.C0 * (Obj.m * Obj.B0) := by
      have hA : Obj.f * Obj.N ^ 2 * Obj.La ≤ 3 * Obj.f * Obj.b := by
        linarith only [mul_le_mul_of_nonneg_left hN2La_le_3b hf0]
      have hB := mul_le_mul_of_nonneg_left hA (mul_nonneg hC0_nn hm0)
      linarith only [hB, mul_le_mul_of_nonneg_left hfb_le_B0 (mul_nonneg hC0_nn hm0)]
    exact Obj.e6_le.trans (h1.trans (mul_le_mul_of_nonneg_left hmB0_le (by linarith only [hC0_nn])))
  -- Error 5: `eP ≤ 2 * C0 * (TT.card * a * La) + 9 * C0 * m * (B0 + Nc) * xe`
  have hErr5 : Obj.C0 * (2 * (TT.card : ℝ) * Obj.b' * Obj.N +
        Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N + Obj.f * Obj.N ^ 2) * Obj.La ≤
      2 * Obj.C0 * ((TT.card : ℝ) * Obj.a * Obj.La) +
        9 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have hTT_a : (TT.card : ℝ) * (Obj.b' * Obj.N) * Obj.La ≤ (TT.card : ℝ) * Obj.a * Obj.La :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left Obj.b'_N_le_a (Nat.cast_nonneg _)) hLa0
    have h2_f : Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N * Obj.La ≤ 6 * Obj.B0 := by
      have hS_w : Obj.S ≤ Obj.w'' := by
        have h1 : Obj.S ≤ Obj.k * Obj.S := by nlinarith only [Obj.k_ge_one, hS0]
        exact h1.trans Obj.k_S_le_w''
      have hN_sum : (Obj.m * Obj.η + Obj.S) * Obj.N ≤ 2 * Obj.b := by
        have hw0 : 0 ≤ Obj.w'' := le_trans (mul_nonneg hk0 hS0) Obj.k_S_le_w''
        have h1 : (Obj.m * Obj.η + Obj.S) * Obj.N ≤ 2 * (Obj.N * Obj.w'') := by
          have hadd := add_le_add hmη_le_w'' hS_w
          nlinarith only [hadd, hN0]
        linarith only [h1, Obj.N_w''_le_b]
      have hLa : Obj.f * ((Obj.m * Obj.η + Obj.S) * Obj.N) * Obj.La ≤ Obj.f * (2 * Obj.b) * (3 * Obj.L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hN_sum hf0) hLa_le_3L hLa0 (mul_nonneg hf0 (by linarith only [hb0]))
      have hL_B : Obj.f * (2 * Obj.b) * (3 * Obj.L) = 6 * (Obj.f * Obj.b * Obj.L) := by ring
      have hB : Obj.f * Obj.b * Obj.L ≤ Obj.B0 := by
        rw [hB0_eq]
        have hfbL0 : 0 ≤ Obj.f * Obj.b * Obj.L := mul_nonneg (mul_nonneg hf0 hb0) hL0
        nlinarith only [Obj.m_ge_one, hfbL0]
      linarith only [hLa, hL_B, hB]
    have h3_f : Obj.f * Obj.N ^ 2 * Obj.La ≤ 3 * Obj.B0 := by
      have h1 := mul_le_mul_of_nonneg_left hN2La_le_3b hf0
      linarith only [h1, hfb_le_B0]
    have hmul := mul_le_mul_of_nonneg_left (show 2 * (TT.card : ℝ) * Obj.b' * Obj.N * Obj.La +
        Obj.f * (Obj.m * Obj.η + Obj.S) * Obj.N * Obj.La + Obj.f * Obj.N ^ 2 * Obj.La ≤
        2 * ((TT.card : ℝ) * Obj.a * Obj.La) + 9 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) by
      linarith only [hTT_a, h2_f, h3_f, hBN_xe]) hC0_nn
    linarith only [hmul]
  -- Error 6: `∑ j, ∑ ρ, eE j ρ ≤ 15 * C0 * m * (B0 + Nc) * xe`
  have hErr6 : (∑ j : J, ∑ ρ : Pl, Obj.eE j ρ) ≤
      15 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have hpt : ∀ j ρ, Obj.eE j ρ ≤ Obj.C0 * (12 * Obj.b * Obj.L + 3 * Obj.b) := fun j ρ => by
      have h1 : (Obj.w j ρ + Obj.S + Obj.m * (Obj.tt + 1) * Obj.η) * Obj.La ≤
          (4 * Obj.b) * (3 * Obj.L) :=
        mul_le_mul (by linarith only [(Obj.w_bounds j ρ).2, hS_le_b, hmttη_le_b])
          hLa_le_3L hLa0 (by linarith only [hb0])
      have h2 := Obj.eE_le j ρ
      have h3 : Obj.C0 * (Obj.w j ρ + Obj.S + Obj.N ^ 2 + Obj.m * (Obj.tt + 1) * Obj.η) * Obj.La =
          Obj.C0 * ((Obj.w j ρ + Obj.S + Obj.m * (Obj.tt + 1) * Obj.η) * Obj.La + Obj.N ^ 2 * Obj.La) := by
        ring
      have h12 : (4 * Obj.b) * (3 * Obj.L) + 3 * Obj.b = 12 * Obj.b * Obj.L + 3 * Obj.b := by ring
      have hinner : (Obj.w j ρ + Obj.S + Obj.m * (Obj.tt + 1) * Obj.η) * Obj.La + Obj.N ^ 2 * Obj.La ≤
          12 * Obj.b * Obj.L + 3 * Obj.b := by
        linarith only [h1, hN2La_le_3b, h12]
      have h4 := mul_le_mul_of_nonneg_left hinner hC0_nn
      linarith only [h2, h3, h4]
    have hinner_nn : 0 ≤ Obj.C0 * (12 * Obj.b * Obj.L + 3 * Obj.b) :=
      mul_nonneg hC0_nn (add_nonneg (mul_nonneg (by linarith only [hb0]) hL0) (by linarith only [hb0]))
    calc (∑ j : J, ∑ ρ : Pl, Obj.eE j ρ)
        ≤ ∑ _j : J, ∑ _ρ : Pl, Obj.C0 * (12 * Obj.b * Obj.L + 3 * Obj.b) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ρ _ => hpt j ρ
      _ = (Fintype.card J : ℝ) * ((Fintype.card Pl : ℝ) * (Obj.C0 * (12 * Obj.b * Obj.L + 3 * Obj.b))) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Obj.m * (Obj.f * (Obj.C0 * (12 * Obj.b * Obj.L + 3 * Obj.b))) := by
          rw [Obj.card_J_eq]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Obj.card_Pl_le hinner_nn) hm0
      _ ≤ 15 * Obj.C0 * Obj.B0 := by
          have hb_bL : Obj.b ≤ Obj.b * Obj.L := by nlinarith only [hb0, hL1]
          have hcmf : 0 ≤ Obj.C0 * Obj.m * Obj.f := mul_nonneg (mul_nonneg hC0_nn hm0) hf0
          have h3b : 3 * Obj.b ≤ 3 * (Obj.b * Obj.L) := by linarith only [hb_bL]
          have hmul := mul_le_mul_of_nonneg_left h3b hcmf
          have hexp : Obj.m * (Obj.f * (Obj.C0 * (12 * Obj.b * Obj.L + 3 * Obj.b))) =
              12 * Obj.C0 * (Obj.m * Obj.f * Obj.b * Obj.L) + Obj.C0 * Obj.m * Obj.f * (3 * Obj.b) := by ring
          have hexp2 : Obj.C0 * Obj.m * Obj.f * (3 * (Obj.b * Obj.L)) =
              3 * Obj.C0 * (Obj.m * Obj.f * Obj.b * Obj.L) := by ring
          rw [hmfbL_le_B0] at hexp hexp2
          have hexp3 : 12 * Obj.C0 * Obj.B0 + 3 * Obj.C0 * Obj.B0 = 15 * Obj.C0 * Obj.B0 := by ring
          linarith only [hmul, hexp, hexp2, hexp3]
      _ ≤ 15 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) :=
          mul_le_mul_of_nonneg_left hBN_xe (by linarith only [hC0_nn])
  -- Error 7: `∑ j, ∑ ρ, |pq j - k| * w j ρ * |logOm| ≤ 6 * m * (B0 + Nc) * xe`
  have hErr7 : (∑ j : J, ∑ ρ : Pl, |Obj.pq j - Obj.k| * Obj.w j ρ * |Obj.logOm|) ≤
      6 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have hpt' : ∀ j ρ, |Obj.pq j - Obj.k| * Obj.w j ρ * |Obj.logOm| ≤ 6 * Obj.m * Obj.b * Obj.L :=
      fun j ρ => by
        have h1 : |Obj.pq j - Obj.k| * Obj.w j ρ ≤ Obj.m * (2 * Obj.b) :=
          mul_le_mul (Obj.pq_close j) (Obj.w_bounds j ρ).2 (Obj.w_bounds j ρ).1 hm0
        have h2 : |Obj.pq j - Obj.k| * Obj.w j ρ * |Obj.logOm| ≤ (Obj.m * (2 * Obj.b)) * Obj.La :=
          mul_le_mul h1 Obj.logOm_abs_le (abs_nonneg _) (mul_nonneg hm0 (by linarith only [hb0]))
        have h3 : (Obj.m * (2 * Obj.b)) * Obj.La ≤ (Obj.m * (2 * Obj.b)) * (3 * Obj.L) :=
          mul_le_mul_of_nonneg_left hLa_le_3L (mul_nonneg hm0 (by linarith only [hb0]))
        linarith only [h2, h3]
    have h6_nn : 0 ≤ 6 * Obj.m * Obj.b * Obj.L :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm0) hb0) hL0
    calc (∑ j : J, ∑ ρ : Pl, |Obj.pq j - Obj.k| * Obj.w j ρ * |Obj.logOm|)
        ≤ ∑ _j : J, ∑ _ρ : Pl, (6 * Obj.m * Obj.b * Obj.L) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ρ _ => hpt' j ρ
      _ = (Fintype.card J : ℝ) * ((Fintype.card Pl : ℝ) * (6 * Obj.m * Obj.b * Obj.L)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Obj.m * (Obj.f * (6 * Obj.m * Obj.b * Obj.L)) := by
          rw [Obj.card_J_eq]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Obj.card_Pl_le h6_nn) hm0
      _ = 6 * (Obj.m * Obj.B0) := by rw [hB0_eq]; ring
      _ ≤ 6 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by linarith only [hmB0_le]
  -- Error 8: `∑ j, ∑ ρ, |δ j ρ| * |logOm| ≤ C0 * (TT.card * a * La) + 15 * C0 * m * (B0 + Nc) * xe`
  have hErr8 : (∑ j : J, ∑ ρ : Pl, |Obj.δ j ρ| * |Obj.logOm|) ≤
      Obj.C0 * ((TT.card : ℝ) * Obj.a * Obj.La) +
        15 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
    have hTT : (Finset.univ.filter (· ∈ TT)) = TT := by ext t; simp
    have hpt : ∀ j ρ, |Obj.δ j ρ| * |Obj.logOm| ≤
        Obj.C0 * (5 * Obj.b * (3 * Obj.L)) +
          Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0) := fun j ρ => by
      have hnonTT : Obj.w j ρ + Obj.k * (Obj.N + Obj.S) + Obj.m * (Obj.tt + 1) * Obj.η ≤
          5 * Obj.b := by
        have hkNS : Obj.k * (Obj.N + Obj.S) = Obj.k * Obj.N + Obj.k * Obj.S := by ring
        linarith only [(Obj.w_bounds j ρ).2, hkNS, Obj.k_N_le_b, hS_le_b, hmttη_le_b,
          show Obj.k * Obj.S ≤ Obj.b from by
            have hw0 : 0 ≤ Obj.w'' := le_trans (mul_nonneg hk0 hS0) Obj.k_S_le_w''
            have h1 : Obj.w'' ≤ Obj.N * Obj.w'' := by nlinarith only [hN1, hw0]
            linarith only [Obj.k_S_le_w'', h1, Obj.N_w''_le_b]]
      have hkb'_nn : 0 ≤ (if ρ ∈ TT then Obj.k * Obj.b' else 0) := by
        split_ifs
        · exact mul_nonneg hk0 Obj.b'_nonneg
        · exact le_rfl
      have h1 : |Obj.δ j ρ| * |Obj.logOm| ≤
          Obj.C0 * (5 * Obj.b + (if ρ ∈ TT then Obj.k * Obj.b' else 0)) * Obj.La := by
        have hA : |Obj.δ j ρ| ≤ Obj.C0 * (5 * Obj.b + (if ρ ∈ TT then Obj.k * Obj.b' else 0)) := by
          have h0 := Obj.δ_le j ρ
          have hmul := mul_le_mul_of_nonneg_left
            (show Obj.w j ρ + Obj.k * (Obj.N + Obj.S) + Obj.m * (Obj.tt + 1) * Obj.η +
                (if ρ ∈ TT then Obj.k * Obj.b' else 0) ≤
                5 * Obj.b + (if ρ ∈ TT then Obj.k * Obj.b' else 0) by linarith only [hnonTT])
            hC0_nn
          linarith only [h0, hmul]
        have hB : 0 ≤ Obj.C0 * (5 * Obj.b + (if ρ ∈ TT then Obj.k * Obj.b' else 0)) :=
          mul_nonneg hC0_nn (add_nonneg (by linarith only [hb0]) hkb'_nn)
        exact mul_le_mul hA Obj.logOm_abs_le (abs_nonneg _) hB
      have h2 : Obj.C0 * (5 * Obj.b) * Obj.La ≤ Obj.C0 * (5 * Obj.b * (3 * Obj.L)) := by
        have := mul_le_mul_of_nonneg_left hLa_le_3L (mul_nonneg hC0_nn (by linarith only [hb0]))
        linarith only [this]
      have h3 : Obj.C0 * ((if ρ ∈ TT then Obj.k * Obj.b' else 0) * Obj.La) =
          Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0) := by
        split_ifs <;> ring
      have h1' : Obj.C0 * (5 * Obj.b + (if ρ ∈ TT then Obj.k * Obj.b' else 0)) * Obj.La =
          Obj.C0 * (5 * Obj.b) * Obj.La + Obj.C0 * ((if ρ ∈ TT then Obj.k * Obj.b' else 0) * Obj.La) := by
        ring
      linarith only [h1, h1', h2, h3]
    have hsum_pt := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum fun ρ (_ : ρ ∈ Finset.univ) => hpt j ρ
    have h15_nn : 0 ≤ Obj.C0 * (5 * Obj.b * (3 * Obj.L)) :=
      mul_nonneg hC0_nn (mul_nonneg (by linarith only [hb0]) (by linarith only [hL0]))
    have hsum_A : (∑ _j : J, ∑ _ρ : Pl, Obj.C0 * (5 * Obj.b * (3 * Obj.L))) ≤
        15 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) := by
      calc (∑ _j : J, ∑ _ρ : Pl, Obj.C0 * (5 * Obj.b * (3 * Obj.L)))
          = (Fintype.card J : ℝ) * ((Fintype.card Pl : ℝ) * (Obj.C0 * (15 * Obj.b * Obj.L))) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ ≤ Obj.m * (Obj.f * (Obj.C0 * (15 * Obj.b * Obj.L))) := by
            rw [Obj.card_J_eq]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right Obj.card_Pl_le (by linarith only [h15_nn])) hm0
        _ = 15 * Obj.C0 * Obj.B0 := by rw [hB0_eq]; ring
        _ ≤ 15 * Obj.C0 * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) :=
            mul_le_mul_of_nonneg_left hBN_xe (by linarith only [hC0_nn])
    have hsum_B : (∑ _j : J, ∑ ρ : Pl, Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0)) ≤
        Obj.C0 * ((TT.card : ℝ) * Obj.a * Obj.La) := by
      have hrew : (∑ _j : J, ∑ ρ : Pl, Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0)) =
          Obj.C0 * ((TT.card : ℝ) * (Obj.m * Obj.k * Obj.b') * Obj.La) := by
        have hinner : ∀ j : J, (∑ ρ : Pl, Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0)) =
            Obj.C0 * ((TT.card : ℝ) * (Obj.k * Obj.b') * Obj.La) := fun _ => by
          rw [← Finset.mul_sum]
          have hs : (∑ ρ : Pl, if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0) =
              (TT.card : ℝ) * (Obj.k * Obj.b') * Obj.La := by
            have hite' : (∑ ρ : Pl, if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0) =
                ∑ _ρ ∈ TT, (Obj.k * Obj.b' * Obj.La) := by
              rw [← Finset.sum_filter, hTT]
            rw [hite', Finset.sum_const, nsmul_eq_mul]; ring
          rw [hs]
        calc (∑ j : J, ∑ ρ : Pl, Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0))
            = ∑ _j : J, (Obj.C0 * ((TT.card : ℝ) * (Obj.k * Obj.b') * Obj.La)) :=
              Finset.sum_congr rfl fun j _ => hinner j
          _ = Obj.m * (Obj.C0 * ((TT.card : ℝ) * (Obj.k * Obj.b') * Obj.La)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Obj.card_J_eq]
          _ = Obj.C0 * ((TT.card : ℝ) * (Obj.m * Obj.k * Obj.b') * Obj.La) := by ring
      rw [hrew]
      refine mul_le_mul_of_nonneg_left ?_ hC0_nn
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left Obj.m_k_b'_le_a (Nat.cast_nonneg _)) hLa0
    have hsum_split : (∑ j : J, ∑ ρ : Pl, (Obj.C0 * (5 * Obj.b * (3 * Obj.L)) +
          Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0))) =
        (∑ _j : J, ∑ _ρ : Pl, Obj.C0 * (5 * Obj.b * (3 * Obj.L))) +
        (∑ _j : J, ∑ ρ : Pl, Obj.C0 * (if ρ ∈ TT then Obj.k * Obj.b' * Obj.La else 0)) := by
      simp_rw [Finset.sum_add_distrib]
    linarith only [hsum_pt, hsum_split, hsum_A, hsum_B]
  -- Final combination: `3 * C0 ≤ 50 * C0 + 10` and `48 * C0 + 7 ≤ 50 * C0 + 10`!
  have hTT_nn : 0 ≤ (TT.card : ℝ) * Obj.a * Obj.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha0.le) hLa0
  have hBN_nn : 0 ≤ Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe :=
    mul_nonneg (mul_nonneg hm0 (add_nonneg hB0_nn Obj.Nc_nonneg)) hxe0
  have hTT_final : 3 * Obj.C0 * ((TT.card : ℝ) * Obj.a * Obj.La) ≤
      (50 * Obj.C0 + 10) * ((TT.card : ℝ) * Obj.a * Obj.La) :=
    mul_le_mul_of_nonneg_right (by linarith only [hC0_nn]) hTT_nn
  have hBN_final : (48 * Obj.C0 + 7) * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) ≤
      (50 * Obj.C0 + 10) * (Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) :=
    mul_le_mul_of_nonneg_right (by linarith only [hC0_nn]) hBN_nn
  linarith only [hraw, hErr1, hErr2, hErr3, hErr4, hErr5, hErr6, hErr7, hErr8, hTT_final, hBN_final]

/-- The universal `StatementObj` predicate (`DivIneqObjProp`) holds unconditionally. -/
theorem divIneqObj_holds : DivIneqObjProp := by
  intro K _ _ _ D J Pl Emb Sg _ _ _ _ _ TT _ nr Obj
  exact div_ineq_of_covol_and_gluing Obj

/-- **Wave 3 Bridge (`div_ineq_with_dwork_chain_bridge`)**:
connects `div_ineq_of_covol_and_gluing` directly to `Stage11BostDworkSqueeze.divLink_of_dwork_chain`
and `RHDirect.PAdicChainValuation.vvTerm`, discharging the `divLink` archimedean-to-`p`-adic
Selmer-window inequality for `Stage14M5_IndefUseDivCore`. -/
theorem div_ineq_with_dwork_chain_bridge
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {D : ℕ} {J Pl Emb Sg : Type} [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    {TT : Finset Pl} [DecidablePred (· ∈ TT)] {nr : ℕ}
    (Obj : DivIneqObj K D J Pl Emb Sg TT nr)
    {Kp : Type*} [NormedField Kp] [CharZero Kp] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : Kp)‖ < 1)
    (S_sel : RHDirect.SelmerSystem) (E_field : Type) [Field E_field] [NumberField E_field]
    (t_val m_chain : ℕ) {archLHS stepDefect : ℝ}
    {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)]
    (Kstep : ∀ j, V j → V (j + 1))
    (loss : ℕ → ℝ)
    (hstep : ∀ j, j < m_chain → ∀ v : V j,
      ‖Kstep j v‖ ≤ ‖(p : Kp)‖ ^ ((∑ t : Pl, Obj.aT t / ((p : ℝ) - 1)) - loss j) * ‖v‖)
    (hloss : ∀ j, j < m_chain →
      loss j ≤ stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S_sel E_field t_val l)
    {v : V 0} (hchain_ne : RHDirect.Stage11BostDworkSqueeze.chainOp Kstep m_chain v ≠ 0)
    (hprod : archLHS +
        (RHDirect.Stage11BostDworkSqueeze.dworkSpaceVal Kp p
          (RHDirect.Stage11BostDworkSqueeze.chainOp Kstep m_chain v) -
          RHDirect.Stage11BostDworkSqueeze.dworkSpaceVal Kp p v) ≤
      (m_chain : ℝ) * (∑ t : Pl, Obj.aT t / ((p : ℝ) - 1))) :
    (Obj.muC + Obj.hu - 2 * Obj.Fo) + archLHS ≤
      (∑ t ∈ TT, (Obj.m * (ph (Obj.aT t) - Obj.aT t * Obj.logOm) - Obj.aT t * Obj.logT)) +
      (50 * Obj.C0 + 10) * ((TT.card : ℝ) * Obj.a * Obj.La + Obj.m * (Obj.B0 + Obj.Nc) * Obj.xe) +
      (m_chain : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S_sel E_field t_val l) := by
  have hdiv := div_ineq_of_covol_and_gluing Obj
  have hdw := divLink_of_dwork_chain hp hlt S_sel E_field t_val m_chain Kstep Obj.aT loss
    hstep hloss hchain_ne hprod
  linarith only [hdiv, hdw]

end DivIneqProof

end

end RHDirect.Stage14M5_DivisorInequalityObj
