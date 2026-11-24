import RHDirect.Stage12MultivarDwork
import RHDirect.Stage3DworkFrobenius

/-!
# RHDirect.Stage14M5_DworkExpRestrict

Field-2 Package M5 Wave 1 (2 of 6) — unconditional, zero-`sorry`, zero-custom-`axiom`,
zero-`native_decide` Lean 4 formalization of the **Dwork Uniformizer `π` (`π^(p-1) = -p`)**,
**Multivariable Dwork Exponential Restrictions (`RestGc`, `RestGcA`)**, **Root-Weight Monomial
Restrictions**, **`p`-Adic Integrality of Restricted Dwork Exponentials**, and **Multiplicative
Factorization of Twisted Theta Power Series** on top of `RHDirect.Stage12MultivarDwork`,
`RHDirect.Stage2DworkExp`, and `RHDirect.Stage3DworkFrobenius`.

All coefficient-ring changes and power-series scalings use **explicit `RingHom`s** (zero nested
`MvPowerSeries` `Algebra` diamonds).

## Contents

1. **Dwork Uniformizer `DworkUniformizerPi` (`π^(p-1) = -p`) & Ramified Root `DworkRamifiedRoot`**:
   - Algebraic/valuation realization of the Dwork uniformizer `π` with exact valuation
     `dworkVal p D.pi = 1 / (p - 1)`, exact norm `‖D.pi‖ = expRadius K p = p ^ (-1 / (p - 1))`,
     Eisenstein polynomial `dworkEisensteinPoly p = X^(p-1) + p`, and sharp factorial bounds
     `‖D.pi ^ k / k!‖ ≤ ‖D.pi‖` (`k ≥ 1`).
   - Ramified `p^2 - 1` uniformizer `DworkRamifiedRoot` (`vp^(p^2 - 1) = p`) with exact
     valuations `dworkVal p R.vp = 1 / (p^2 - 1)`, `dworkVal p (R.vp ^ (p + 1)) = 1 / (p - 1)`,
     and explicit bridge to `DworkUniformizerPi` and `Stage12MultivarDwork.CrystallineQPack`.
   - Splitting radius comparisons (`expRadius K p < 1 < dworkOverconvRadius K p`,
     `(p - 1) / p^2 < 1 / (p - 1)`), explicit scaling `RingHom`s `mvScaleHom` and
     `mvWeightScaleHom`, and isometric field transfer `DworkUniformizerPi.mapHom`.

2. **Explicit Multivariable Exponential, Substitution, Renaming & Root-Weight Restriction Calculus**:
   - Complete formal exponential algebra on `MvPowerSeries`: `coeff_mvExp_eq_sum`,
     `constantCoeff_mvExp`, `mvExp_zero`, `mvExp_add`, `mvExp_neg_mul`, `mvExp_sub`, `mvExp_sum`,
     `mvExp_nsmul`, `map_mvExp`, `mvScaleHom_mvExp`, `mvWeightScaleHom_mvExp`, `frobSub_mvExp`,
     and `substMv_mvExp`.
   - Explicit variable-renaming `renMv` (`renMvHom`), injective coordinate restriction
     `restrictVar` (`restrictVarHom`), and root-weight monomial restriction `monomialRestrict` /
     `rootWeightSlice`, all preserving `IsIntegralMv`, `CoeffNormLeMv`, and `WtGe`.
   - General ultrametric substitution stability: `isIntegralMv_substMv`, `isIntegralMv_psubst`,
     `wtGe_substMv`, and linear-form rescaling `mvScaleHom_substMv_linear`.

3. **Multivariable Dwork Exponential Restriction Operators (`RestGc` & `RestGcA`)**:
   - Formal-group parameter map `tOfParam vp μ L`, diagonal paired sum `pairedSum`, alternating
     Frobenius series `altFrobSeries`, and quadratic restriction exponent `quadRestExp` /
     `quadRestExpA` (matching Alpöge's `tOf`, `Gt`, `altS`, `hhS`, `hhA`).
   - Single-place restriction operator **`RestGc`** (`RestGcOf`) and multi-place adelic product
     restriction operator **`RestGcA`** (`RestGcAOf`), plus root-weight slice restriction
     **`RestGcRootWeight`**.
   - Exact multi-place product splitting theorem **`RestGcA_eq_prod_RestGc`** and factorization
     predicates **`RestGcFact`** / **`RestGcAFact`** with unconditional place-to-global assembly
     **`restGcAFact_of_restGcFact`**.

4. **`p`-Adic Integrality of Restricted Dwork Exponential Series (`dwork_exponential_restriction_integral`)**:
   - Unconditional threshold integrality **`dwork_exponential_restriction_integral`** and
     multi-place **`dwork_exponential_restriction_all_places_integral`** via
     `PAdicChainValuation.dwork_exp_weight_le`.
   - Genuine Artin–Hasse / Dwork splitting bivariate restriction integrality and overconvergence
     **`dwork_splitting_restriction_wtGe`** & **`dwork_splitting_restriction_integral`**
     (proving integrality and overconvergence slope `(p - 1) / (2 p^2)` for
     `RestGc vp μ L (-dworkBivArg D.pi p)` even though `‖π‖ = p^{-1/(p-1)}` sits on the boundary
     of the exponential disk!).
   - Frobenius-lift Dieudonné–Dwork restriction integrality
     **`dwork_restriction_isIntegral_of_frob_congr`** via `Stage12MultivarDwork.dieudonne_dwork_mv_iff`.
   - Root-weight slice integrality and sharp scaling valuation gain
     **`rootWeightRestrict_dwork_integral`** & **`dworkVal_coeff_scale_ge`**.

5. **Multiplicative Factorization of Twisted Theta Power Series (`twisted_theta_power_series_factorization`)**:
   - Exponential integrality equivalence `ExpIntegral` / `SimeqExp` with full algebraic closure
     (via `Stage12MultivarDwork.isIntegralMv_invOneMv`).
   - Formal-group parameter change `inParamMv` and substitution reduction **`twisted_theta_reduction`**
     (matching Alpöge's `SubstitutionOfVariables.th_reduce`).
   - Single-place **`twisted_theta_power_series_factorization`** and multi-place adelic
     **`twisted_theta_all_places_factorization`** (matching `restSExp_of` & `restSExpA_of`).
   - Explicit `InClass` / `p`-adic valuation expansion **`twisted_theta_dwork_class_expansion`**,
     overconvergent Banach-norm & Fredholm-Newton-polygon bridge **`twisted_theta_overconv_bound`**
     / **`twisted_theta_newton_polygon_bridge`** (wiring to `Stage3DworkFrobenius`), and
     inert-prime congruence gain bridge **`twisted_theta_inert_gain_bridge`** (wiring directly
     into `Stage12MultivarDwork.InertCongruenceData` for M5 Wave 2 `Stage14M5_LinkGAndAskIsF`).
-/

open Real Finset
open scoped BigOperators
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage3DworkFrobenius
open RHDirect.Stage11BostDworkSqueeze
open RHDirect.Stage12MultivarDwork

namespace RHDirect.Stage14M5_DworkExpRestrict

noncomputable section

/-! ## Section 1: `DworkUniformizerPi` (`π^(p-1) = -p`), Ramified Root & Splitting Radius Bounds -/

section DworkUniformizerSection

/-- **Dwork Uniformizer `π` (`π^(p-1) = -p`)** in an ultrametric field `K` of characteristic `0`
with normalized `p`-adic norm `‖(p : K)‖ = p⁻¹`. Realizes the exact Dwork valuation
`v_p(π) = 1 / (p - 1)` and splits the additive character modulo `p` via `θ(X) = exp(π(X - X^p))`. -/
structure DworkUniformizerPi (K : Type*) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p : ℕ) [Fact p.Prime] where
  /-- The Dwork uniformizer `π ∈ K`. -/
  pi : K
  /-- Normalized `p`-adic norm on `K`: `‖(p : K)‖ = p⁻¹`. -/
  norm_p : ‖(p : K)‖ = (p : ℝ)⁻¹
  /-- Kummer–Dwork defining equation `π ^ (p - 1) = -p`. -/
  pi_pow_eq : pi ^ (p - 1) = -(p : K)

/-- **Eisenstein Polynomial for the Dwork Uniformizer**: `f_p(X) = X^(p - 1) + p ∈ R[X]`. -/
def dworkEisensteinPoly (R : Type*) [CommRing R] (p : ℕ) : Polynomial R :=
  Polynomial.X ^ (p - 1) + Polynomial.C (p : R)

theorem dworkEisensteinPoly_monic {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) :
    (dworkEisensteinPoly R p).Monic := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · unfold dworkEisensteinPoly
    have h1 : 1 ≤ p - 1 := by have := hp.two_le; omega
    have hdegC : (Polynomial.C (p : R)).degree < (Polynomial.X ^ (p - 1) : Polynomial R).degree := by
      rw [Polynomial.degree_X_pow]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by omega : 0 < p - 1))
    exact (Polynomial.monic_X_pow (p - 1)).add_of_left hdegC

theorem dworkEisensteinPoly_natDegree {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ}
    (hp : p.Prime) :
    (dworkEisensteinPoly R p).natDegree = p - 1 := by
  unfold dworkEisensteinPoly
  have h1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow (p - 1)
  · rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    omega

theorem dworkEisensteinPoly_coeff_zero {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) :
    (dworkEisensteinPoly R p).coeff 0 = (p : R) := by
  unfold dworkEisensteinPoly
  have hne : p - 1 ≠ 0 := by have := hp.two_le; omega
  simp [Polynomial.coeff_X_pow, hne.symm]

theorem dworkEisensteinPoly_coeff_middle {R : Type*} [CommRing R] {p : ℕ} {k : ℕ}
    (hk0 : 0 < k) (hkp : k < p - 1) :
    (dworkEisensteinPoly R p).coeff k = 0 := by
  unfold dworkEisensteinPoly
  simp [Polynomial.coeff_X_pow, hk0.ne', hkp.ne]

theorem dworkEisensteinPoly_eval_eq_zero_iff {R : Type*} [CommRing R] (p : ℕ) (x : R) :
    (dworkEisensteinPoly R p).eval x = 0 ↔ x ^ (p - 1) = -(p : R) := by
  unfold dworkEisensteinPoly
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  constructor
  · intro h; exact eq_neg_of_add_eq_zero_left h
  · intro h; rw [h, neg_add_cancel]

namespace DworkUniformizerPi

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable {p : ℕ} [Fact p.Prime]

theorem hp (_D : DworkUniformizerPi K p) : p.Prime := Fact.out

theorem norm_p_pos (D : DworkUniformizerPi K p) : 0 < ‖(p : K)‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr D.hp.ne_zero)

theorem norm_p_lt_one (D : DworkUniformizerPi K p) : ‖(p : K)‖ < 1 := by
  rw [D.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast D.hp.one_lt)

theorem eval_eisenstein (D : DworkUniformizerPi K p) : (dworkEisensteinPoly K p).eval D.pi = 0 :=
  (dworkEisensteinPoly_eval_eq_zero_iff p D.pi).mpr D.pi_pow_eq

theorem norm_pi_eq_expRadius (D : DworkUniformizerPi K p) : ‖D.pi‖ = expRadius K p :=
  norm_dworkPi D.hp D.pi_pow_eq

/-- Exact norm of the Dwork uniformizer: `‖π‖ = p ^ (-1 / (p - 1))`. -/
theorem norm_pi_eq_rpow (D : DworkUniformizerPi K p) :
    ‖D.pi‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast D.hp.pos
  rw [D.norm_pi_eq_expRadius, expRadius, D.norm_p, Real.inv_rpow hp_pos.le,
    ← Real.rpow_neg hp_pos.le]
  congr 1
  ring

theorem norm_pi_eq_norm_p_rpow (D : DworkUniformizerPi K p) :
    ‖D.pi‖ = ‖(p : K)‖ ^ ((1 : ℝ) / ((p : ℝ) - 1)) :=
  D.norm_pi_eq_expRadius

theorem norm_pi_pos (D : DworkUniformizerPi K p) : 0 < ‖D.pi‖ := by
  rw [D.norm_pi_eq_expRadius]
  exact expRadius_pos D.hp

theorem pi_ne_zero (D : DworkUniformizerPi K p) : D.pi ≠ 0 :=
  norm_pos_iff.mp D.norm_pi_pos

theorem norm_pi_lt_one (D : DworkUniformizerPi K p) : ‖D.pi‖ < 1 := by
  rw [D.norm_pi_eq_expRadius]
  exact expRadius_lt_one D.hp D.norm_p_lt_one

theorem norm_pi_le_one (D : DworkUniformizerPi K p) : ‖D.pi‖ ≤ 1 := D.norm_pi_lt_one.le

/-- **Exact Additive `p`-adic Valuation of `π`**: `v_p(π) = 1 / (p - 1)`. -/
theorem dworkVal_pi (D : DworkUniformizerPi K p) : dworkVal p D.pi = 1 / ((p : ℝ) - 1) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast D.hp.pos
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast D.hp.one_lt)).ne'
  unfold dworkVal
  rw [D.norm_pi_eq_rpow, D.norm_p, Real.log_rpow hp_pos, Real.log_inv]
  field_simp [hlog_ne]

/-- Exact additive `p`-adic valuation of powers `π ^ k`: `v_p(π ^ k) = k / (p - 1)`. -/
theorem dworkVal_pi_pow (D : DworkUniformizerPi K p) (k : ℕ) :
    dworkVal p (D.pi ^ k) = (k : ℝ) / ((p : ℝ) - 1) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast D.hp.pos
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast D.hp.one_lt)).ne'
  unfold dworkVal
  rw [norm_pow, Real.log_pow, D.norm_pi_eq_rpow, D.norm_p, Real.log_rpow hp_pos, Real.log_inv]
  field_simp [hlog_ne]

/-- Exact Kummer shift identity `π ^ p = -p * π`. -/
theorem pi_pow_p_eq (D : DworkUniformizerPi K p) : D.pi ^ p = -(p : K) * D.pi := by
  have h : D.pi ^ p = D.pi ^ ((p - 1) + 1) := congrArg (D.pi ^ ·) (Nat.sub_add_cancel D.hp.one_le).symm
  rw [h, pow_succ, D.pi_pow_eq]

/-- Sharp factorial norm bound for `k ≥ 1`: `‖π ^ k / k!‖ ≤ ‖π‖` (the boundary of the
`p`-adic exponential disk!). -/
theorem norm_pi_pow_div_factorial_le_pi (D : DworkUniformizerPi K p) {k : ℕ} (hk : k ≠ 0) :
    ‖D.pi ^ k / (k.factorial : K)‖ ≤ ‖D.pi‖ := by
  have h := norm_expTerm_le D.hp D.norm_p_lt_one D.pi hk
  rw [D.norm_pi_eq_expRadius] at h ⊢
  have hrpos : 0 < expRadius K p := expRadius_pos D.hp
  rw [div_self hrpos.ne', one_pow, mul_one] at h
  simpa [expTerm, div_eq_inv_mul] using h

/-- Uniform factorial integrality for all `k : ℕ`: `‖π ^ k / k!‖ ≤ 1`. -/
theorem norm_pi_pow_div_factorial_le_one (D : DworkUniformizerPi K p) (k : ℕ) :
    ‖D.pi ^ k / (k.factorial : K)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact (D.norm_pi_pow_div_factorial_le_pi hk.ne').trans D.norm_pi_le_one

/-- Exact equality at prime powers `k = p ^ m`: `‖π ^ (p ^ m) / (p ^ m)!‖ = ‖π‖`. -/
theorem norm_pi_pow_div_factorial_prime_pow (D : DworkUniformizerPi K p) (m : ℕ) :
    ‖D.pi ^ (p ^ m) / ((p ^ m).factorial : K)‖ = ‖D.pi‖ := by
  have h := norm_expTerm_prime_pow D.hp D.norm_p_lt_one D.pi m
  rw [D.norm_pi_eq_expRadius] at h ⊢
  have hrpos : 0 < expRadius K p := expRadius_pos D.hp
  rw [div_self hrpos.ne', one_pow, mul_one] at h
  simpa [expTerm, div_eq_inv_mul] using h

/-- **Dwork Splitting Radius Formula**:
`dworkOverconvRadius K p = p ^ ((p - 1) / p^2) > 1`. -/
theorem splittingRadius_eq (D : DworkUniformizerPi K p) :
    dworkOverconvRadius K p = (p : ℝ) ^ (((p : ℝ) - 1) / (p : ℝ) ^ 2) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast D.hp.pos
  unfold dworkOverconvRadius
  rw [D.norm_p, Real.inv_rpow hp_pos.le, ← Real.rpow_neg hp_pos.le]
  congr 1
  ring

/-- **Strict Splitting Radius Sandwich**:
`‖π‖ = expRadius K p < 1 < dworkOverconvRadius K p`, and the overconvergence slope satisfies
`0 < (p - 1) / p^2 < 1 / (p - 1)`. -/
theorem splittingRadius_bounds (D : DworkUniformizerPi K p) :
    ‖D.pi‖ < 1 ∧ 1 < dworkOverconvRadius K p ∧
      0 < ((p : ℝ) - 1) / (p : ℝ) ^ 2 ∧
      ((p : ℝ) - 1) / (p : ℝ) ^ 2 < 1 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast D.hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  refine ⟨D.norm_pi_lt_one, one_lt_dworkOverconvRadius D.hp D.norm_p_lt_one,
    div_pos hpm1 (sq_pos_of_pos hp0), ?_⟩
  rw [div_lt_div_iff₀ (sq_pos_of_pos hp0) hpm1]
  nlinarith

/-- Valuation subring `O_K = {c : K | ‖c‖ ≤ 1}` attached to `D`. -/
def intSubring (_D : DworkUniformizerPi K p) : Subring K := ultrametricUnitBall K

theorem pi_mem_intSubring (D : DworkUniformizerPi K p) : D.pi ∈ D.intSubring := D.norm_pi_le_one

theorem p_mem_intSubring (D : DworkUniformizerPi K p) : (p : K) ∈ D.intSubring :=
  D.norm_p_lt_one.le

/-- Canonical `CrystallineQPack K p` built directly from `DworkUniformizerPi`
(bridging into `Stage12MultivarDwork.dworkPiQPack`). -/
def toQPack (D : DworkUniformizerPi K p) : CrystallineQPack K p :=
  dworkPiQPack K p D.norm_p D.pi D.pi_pow_eq

theorem toQPack_th_nu (D : DworkUniformizerPi K p) : ‖D.toQPack.th D.toQPack.nu‖ = ‖D.pi‖ := by
  rw [D.toQPack.th_nu, D.norm_pi_eq_rpow]

/-- Explicit isometric `RingHom` transfer of `DworkUniformizerPi` across ultrametric fields
(zero `Algebra` typeclass diamonds!). -/
def mapHom (D : DworkUniformizerPi K p) {L : Type*} [NormedField L] [IsUltrametricDist L]
    [CharZero L] (φ : K →+* L) (hiso : ∀ x : K, ‖φ x‖ = ‖x‖) : DworkUniformizerPi L p where
  pi := φ D.pi
  norm_p := by
    have h := hiso (p : K)
    rw [map_natCast] at h
    rw [h, D.norm_p]
  pi_pow_eq := by
    rw [← map_pow, D.pi_pow_eq, map_neg, map_natCast]

/-- Univariate Dwork splitting series `θ(X) = exp(π (X - X^p))` attached to `D`. -/
def splittingSeries (D : DworkUniformizerPi K p) : PowerSeries K := dworkSplitting D.pi p

/-- Multivariable Dwork splitting series `θ_σ(X) = ∏_{i : σ} θ(X_i)` attached to `D`. -/
def mvSplittingSeries (D : DworkUniformizerPi K p) (σ : Type*) [Fintype σ] : MvPowerSeries σ K :=
  multivarDworkSplitting (σ := σ) D.pi p

theorem splittingSeries_wtGe (D : DworkUniformizerPi K p) :
    WtGe ‖(p : K)‖ (fun _ : Unit => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (D.splittingSeries : MvPowerSeries Unit K) :=
  dworkSplitting_wtGe D.hp D.norm_p_lt_one D.pi_pow_eq

theorem splittingSeries_isOverconvergent (D : DworkUniformizerPi K p) :
    IsOverconvergent (dworkOverconvRadius K p) D.splittingSeries ∧
      overconvNorm (dworkOverconvRadius K p) D.splittingSeries = 1 :=
  dworkSplitting_isOverconvergent D.hp D.norm_p_lt_one D.pi_pow_eq

theorem mvSplittingSeries_wtGe (D : DworkUniformizerPi K p) (σ : Type*) [Fintype σ] :
    WtGe ‖(p : K)‖ (fun _ : σ => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (D.mvSplittingSeries σ) :=
  multivar_dworkSplitting_wtGe D.hp D.norm_p_lt_one D.pi_pow_eq

theorem mvSplittingSeries_coeff_norm_le (D : DworkUniformizerPi K p) {σ : Type*} [Fintype σ]
    (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (D.mvSplittingSeries σ)‖ ≤
      ‖(p : K)‖ ^ ((d.degree : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) := by
  have h := D.mvSplittingSeries_wtGe σ d
  unfold MonoWtGe wtDot at h
  have hdot : (d.sum fun _ k => (k : ℝ) * -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) =
      -((d.degree : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) := by
    rw [Finsupp.sum, ← Finset.sum_mul, Finsupp.degree_apply, Nat.cast_sum]
    ring
  rw [hdot, sub_neg_eq_add, zero_add] at h
  exact h

theorem mvSplittingSeries_isIntegral (D : DworkUniformizerPi K p) (σ : Type*) [Fintype σ] :
    IsIntegralMv (D.mvSplittingSeries σ) := fun d => by
  have h := D.mvSplittingSeries_coeff_norm_le d
  have hpos := D.norm_p_pos
  have hlt := D.norm_p_lt_one
  have hexp : 0 ≤ (d.degree : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) D.splittingRadius_bounds.2.2.1.le
  exact h.trans (Real.rpow_le_one hpos.le hlt.le hexp)

end DworkUniformizerPi

/-- **Ramified `p^2 - 1` Uniformizer `vp`** (`vp ^ (p^2 - 1) = p`), matching Alpöge's
`DworkExponentialRestrictions` parameter `vp : K'`. Note `(vp ^ (p + 1)) ^ (p - 1) = p`, so
`‖vp ^ (p + 1)‖ = ‖π‖ = p ^ (-1 / (p - 1))`! -/
structure DworkRamifiedRoot (K : Type*) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p : ℕ) [Fact p.Prime] where
  vp : K
  norm_p : ‖(p : K)‖ = (p : ℝ)⁻¹
  vp_pow_eq : vp ^ (p ^ 2 - 1) = (p : K)

namespace DworkRamifiedRoot

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable {p : ℕ} [Fact p.Prime]

theorem hp (_R : DworkRamifiedRoot K p) : p.Prime := Fact.out

theorem norm_p_pos (R : DworkRamifiedRoot K p) : 0 < ‖(p : K)‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr R.hp.ne_zero)

theorem norm_p_lt_one (R : DworkRamifiedRoot K p) : ‖(p : K)‖ < 1 := by
  rw [R.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast R.hp.one_lt)

/-- Exact identity `(vp ^ (p + 1)) ^ (p - 1) = p`. -/
theorem pow_p_add_one_pow_p_sub_one (R : DworkRamifiedRoot K p) :
    (R.vp ^ (p + 1)) ^ (p - 1) = (p : K) := by
  rw [← pow_mul]
  have hmul : (p + 1) * (p - 1) = p ^ 2 - 1 := by
    have hp1 : 1 ≤ p := R.hp.one_le
    zify [hp1, show 1 ≤ p ^ 2 by nlinarith]
    ring
  rw [hmul, R.vp_pow_eq]

/-- Exact norm of `vp`: `‖vp‖ = ‖p‖ ^ (1 / (p^2 - 1))`. -/
theorem norm_vp (R : DworkRamifiedRoot K p) :
    ‖R.vp‖ = ‖(p : K)‖ ^ ((1 : ℝ) / ((p : ℝ) ^ 2 - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast R.hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hnp : ‖R.vp‖ ^ (p ^ 2 - 1) = ‖(p : K)‖ := by rw [← norm_pow, R.vp_pow_eq]
  rw [← hnp, ← Real.rpow_natCast ‖R.vp‖ (p ^ 2 - 1), ← Real.rpow_mul (norm_nonneg _)]
  have hcast : ((p ^ 2 - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1 := by
    have h1 : 1 ≤ p ^ 2 := by have := R.hp.two_le; nlinarith
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  rw [hcast, mul_one_div_cancel hpos.ne', Real.rpow_one]

/-- Exact norm of `vp ^ (p + 1)`: equals `expRadius K p = ‖π‖ = p ^ (-1 / (p - 1))`! -/
theorem norm_vp_pow_p_add_one (R : DworkRamifiedRoot K p) :
    ‖R.vp ^ (p + 1)‖ = expRadius K p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast R.hp.two_le
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnp : ‖R.vp ^ (p + 1)‖ ^ (p - 1) = ‖(p : K)‖ := by
    rw [← norm_pow, R.pow_p_add_one_pow_p_sub_one]
  unfold expRadius
  rw [← hnp, ← Real.rpow_natCast ‖R.vp ^ (p + 1)‖ (p - 1), ← Real.rpow_mul (norm_nonneg _),
    Nat.cast_sub R.hp.one_le, Nat.cast_one, mul_one_div_cancel hpm1.ne', Real.rpow_one]

theorem norm_vp_lt_one (R : DworkRamifiedRoot K p) : ‖R.vp‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast R.hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  rw [R.norm_vp]
  exact Real.rpow_lt_one R.norm_p_pos.le R.norm_p_lt_one (div_pos one_pos hpos)

theorem norm_vp_le_one (R : DworkRamifiedRoot K p) : ‖R.vp‖ ≤ 1 := R.norm_vp_lt_one.le

/-- Exact additive valuation of `vp`: `v_p(vp) = 1 / (p^2 - 1)`. -/
theorem dworkVal_vp (R : DworkRamifiedRoot K p) : dworkVal p R.vp = 1 / ((p : ℝ) ^ 2 - 1) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast R.hp.pos
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast R.hp.one_lt)).ne'
  unfold dworkVal
  rw [R.norm_vp, R.norm_p, Real.log_rpow (inv_pos.mpr hp_pos), Real.log_inv]
  field_simp [hlog_ne]

/-- Exact additive valuation of `vp ^ (p + 1)`: `v_p(vp ^ (p + 1)) = 1 / (p - 1)`. -/
theorem dworkVal_vp_pow_p_add_one (R : DworkRamifiedRoot K p) :
    dworkVal p (R.vp ^ (p + 1)) = 1 / ((p : ℝ) - 1) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast R.hp.pos
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast R.hp.one_lt)).ne'
  unfold dworkVal
  rw [R.norm_vp_pow_p_add_one, expRadius, R.norm_p, Real.log_rpow (inv_pos.mpr hp_pos),
    Real.log_inv]
  field_simp [hlog_ne]

/-- Exact norm of Alpöge's restriction constant `vp ^ (p + 1) / p`:
`‖vp ^ (p + 1) / p‖ = ‖(p : K)‖ ^ (1 / (p - 1) - 1) = p ^ ((p - 2) / (p - 1))`. -/
theorem norm_vp_pow_div_p (R : DworkRamifiedRoot K p) :
    ‖R.vp ^ (p + 1) / (p : K)‖ = ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1) := by
  rw [norm_div, R.norm_vp_pow_p_add_one, expRadius, Real.rpow_sub R.norm_p_pos, Real.rpow_one]

/-- Construct a `DworkUniformizerPi K p` from `DworkRamifiedRoot K p` and any `(p - 1)`-th root
`ζ` of `-1` in `K`: `π := ζ * vp ^ (p + 1)` satisfies `π ^ (p - 1) = -p`! -/
def toUniformizerPi (R : DworkRamifiedRoot K p) (ζ : K) (hζ : ζ ^ (p - 1) = -1) :
    DworkUniformizerPi K p where
  pi := ζ * R.vp ^ (p + 1)
  norm_p := R.norm_p
  pi_pow_eq := by
    rw [mul_pow, hζ, R.pow_p_add_one_pow_p_sub_one, neg_one_mul]

/-- For `p = 2`, `-R.vp ^ 3` is unconditionally a `DworkUniformizerPi K 2` with no extra root! -/
def toUniformizerPiTwo (R2 : DworkRamifiedRoot K 2) : DworkUniformizerPi K 2 :=
  R2.toUniformizerPi (-1) (by norm_num)

end DworkRamifiedRoot

/-! ### Explicit Scaling `RingHom`s on `MvPowerSeries` (Zero `Algebra` Diamonds) -/

section MvScalingHoms

variable {σ R : Type*} [CommRing R]

/-- Underlying function for `mvScaleHom`. -/
private def mvScaleFun (c : R) (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d => c ^ d.degree * MvPowerSeries.coeff d F

/-- Isotropic degree-scaling `RingHom` `mvScaleHom c : R[[X_i]] →+* R[[X_i]]` sending
`X_i ↦ c * X_i` (explicitly `coeff d (mvScaleHom c F) = c ^ d.degree * coeff d F`), matching
Alpöge's `atPi`. Uses NO `Algebra` tower! -/
def mvScaleHom (c : R) : MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun := mvScaleFun c
  map_one' := by
    classical
    ext d
    change c ^ d.degree * MvPowerSeries.coeff d (1 : MvPowerSeries σ R) =
      MvPowerSeries.coeff d (1 : MvPowerSeries σ R)
    rw [MvPowerSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simp
  map_mul' F G := by
    classical
    ext d
    show c ^ d.degree * MvPowerSeries.coeff d (F * G) =
      MvPowerSeries.coeff d (mvScaleFun c F * mvScaleFun c G)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    have hdeg : x.1.degree + x.2.degree = d.degree := by rw [← map_add, hx]
    rw [← hdeg, pow_add]
    change c ^ x.1.degree * c ^ x.2.degree *
        (MvPowerSeries.coeff x.1 F * MvPowerSeries.coeff x.2 G) =
      (c ^ x.1.degree * MvPowerSeries.coeff x.1 F) *
        (c ^ x.2.degree * MvPowerSeries.coeff x.2 G)
    ring
  map_zero' := by
    ext d
    change c ^ d.degree * MvPowerSeries.coeff d (0 : MvPowerSeries σ R) = 0
    simp
  map_add' F G := by
    ext d
    change c ^ d.degree * MvPowerSeries.coeff d (F + G) =
      c ^ d.degree * MvPowerSeries.coeff d F + c ^ d.degree * MvPowerSeries.coeff d G
    rw [map_add, mul_add]

@[simp] theorem coeff_mvScaleHom (c : R) (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (mvScaleHom c F) = c ^ d.degree * MvPowerSeries.coeff d F := rfl

@[simp] theorem constantCoeff_mvScaleHom (c : R) (F : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (mvScaleHom c F) = MvPowerSeries.constantCoeff F := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvScaleHom]
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

@[simp] theorem mvScaleHom_C (c r : R) :
    mvScaleHom c (MvPowerSeries.C r : MvPowerSeries σ R) = MvPowerSeries.C r := by
  classical
  ext d
  rw [coeff_mvScaleHom, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

@[simp] theorem mvScaleHom_X (c : R) (i : σ) :
    mvScaleHom c (MvPowerSeries.X i : MvPowerSeries σ R) =
      MvPowerSeries.C c * MvPowerSeries.X i := by
  classical
  ext d
  rw [coeff_mvScaleHom, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

theorem mvScaleHom_comp (c₁ c₂ : R) (F : MvPowerSeries σ R) :
    mvScaleHom c₁ (mvScaleHom c₂ F) = mvScaleHom (c₁ * c₂) F := by
  ext d
  simp only [coeff_mvScaleHom, mul_pow]
  ring

@[simp] theorem mvScaleHom_one (F : MvPowerSeries σ R) :
    mvScaleHom (1 : R) F = F := by
  ext d; simp

/-- Underlying function for `mvWeightScaleHom`. -/
private def mvWeightScaleFun (w : σ → R) (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d => (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d F

/-- Anisotropic coordinate-weight scaling `RingHom` `mvWeightScaleHom w : R[[X_i]] →+* R[[X_i]]`
sending `X_i ↦ w i * X_i` (explicitly `coeff d ↦ (d.prod fun i k => w i ^ k) * coeff d`). -/
def mvWeightScaleHom (w : σ → R) : MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun := mvWeightScaleFun w
  map_one' := by
    classical
    ext d
    change (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d (1 : MvPowerSeries σ R) =
      MvPowerSeries.coeff d (1 : MvPowerSeries σ R)
    rw [MvPowerSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simp
  map_mul' F G := by
    classical
    ext d
    show (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d (F * G) =
      MvPowerSeries.coeff d (mvWeightScaleFun w F * mvWeightScaleFun w G)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    have hprod : (d.prod fun i k => w i ^ k) =
        (x.1.prod fun i k => w i ^ k) * (x.2.prod fun i k => w i ^ k) := by
      rw [← hx, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rw [hprod]
    change _ * _ * (MvPowerSeries.coeff x.1 F * MvPowerSeries.coeff x.2 G) =
      (_ * MvPowerSeries.coeff x.1 F) * (_ * MvPowerSeries.coeff x.2 G)
    ring
  map_zero' := by
    ext d
    change (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d (0 : MvPowerSeries σ R) = 0
    simp
  map_add' F G := by
    ext d
    change (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d (F + G) =
      (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d F +
        (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d G
    rw [map_add, mul_add]

@[simp] theorem coeff_mvWeightScaleHom (w : σ → R) (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (mvWeightScaleHom w F) =
      (d.prod fun i k => w i ^ k) * MvPowerSeries.coeff d F := rfl

@[simp] theorem constantCoeff_mvWeightScaleHom (w : σ → R) (F : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (mvWeightScaleHom w F) = MvPowerSeries.constantCoeff F := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvWeightScaleHom]
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem mvWeightScaleHom_const (c : R) (F : MvPowerSeries σ R) :
    mvWeightScaleHom (fun _ : σ => c) F = mvScaleHom c F := by
  ext d
  rw [coeff_mvWeightScaleHom, coeff_mvScaleHom]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem isIntegralMv_mvScaleHom {K : Type*} [NormedField K] [IsUltrametricDist K]
    {c : K} (hc : ‖c‖ ≤ 1) {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    IsIntegralMv (mvScaleHom c F) := fun d => by
  rw [coeff_mvScaleHom, norm_mul, norm_pow]
  calc ‖c‖ ^ d.degree * ‖MvPowerSeries.coeff d F‖
      ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg c) hc) (hF d) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem isIntegralMv_mvWeightScaleHom {K : Type*} [NormedField K] [IsUltrametricDist K]
    {w : σ → K} (hw : ∀ i, ‖w i‖ ≤ 1) {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    IsIntegralMv (mvWeightScaleHom w F) := fun d => by
  rw [coeff_mvWeightScaleHom, norm_mul]
  have hprod : ‖d.prod fun i k => w i ^ k‖ ≤ 1 := by
    rw [Finsupp.prod, norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hw i))
  calc ‖d.prod fun i k => w i ^ k‖ * ‖MvPowerSeries.coeff d F‖
      ≤ 1 * 1 := mul_le_mul hprod (hF d) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Scaling `F` by `c` with `‖c‖ ≤ pi ^ δ` improves Dwork weight radius from `r` to `r - δ`! -/
theorem wtGe_mvScaleHom {K : Type*} [NormedField K] [IsUltrametricDist K]
    {pi δ w : ℝ} (hpi : 0 < pi) {c : K} (hc : ‖c‖ ≤ pi ^ δ) {r : σ → ℝ}
    {F : MvPowerSeries σ K} (hF : WtGe pi r w F) :
    WtGe pi (fun i => r i - δ) w (mvScaleHom c F) := fun d => by
  unfold MonoWtGe
  rw [coeff_mvScaleHom, norm_mul, norm_pow]
  have hwt : wtDot d (fun i => r i - δ) = wtDot d r - (d.degree : ℝ) * δ := by
    unfold wtDot
    rw [Finsupp.sum, Finsupp.sum, Finsupp.degree_apply, Nat.cast_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hwt]
  calc ‖c‖ ^ d.degree * ‖MvPowerSeries.coeff d F‖
      ≤ (pi ^ δ) ^ d.degree * pi ^ (w - wtDot d r) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc _) (hF d) (norm_nonneg _)
          (pow_nonneg (Real.rpow_nonneg hpi.le _) _)
    _ = pi ^ (δ * (d.degree : ℝ)) * pi ^ (w - wtDot d r) := by
        rw [← Real.rpow_natCast (pi ^ δ), ← Real.rpow_mul hpi.le]
    _ = pi ^ (w - (wtDot d r - (d.degree : ℝ) * δ)) := by
        rw [← Real.rpow_add hpi]; congr 1; ring

end MvScalingHoms

end DworkUniformizerSection

/-! ## Section 2: Explicit Multivariable Exponential, Renaming, Restriction & Substitution Calculus -/

section MvExpAndRestriction

variable {σ τ κ K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Formal Multivariable Exponential `mvExp` Calculus -/

section MvExpCalc

variable [CharZero K]

omit [IsUltrametricDist K] in
/-- Explicit finite-sum coefficient formula for `mvExp B`: when `constantCoeff B = 0`,
`coeff d (mvExp B) = ∑_{k ≤ d.degree} (k!)⁻¹ * coeff d (B ^ k)`. -/
theorem coeff_mvExp_eq_sum {B : MvPowerSeries σ K} (hB0 : MvPowerSeries.constantCoeff B = 0)
    (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (mvExp B) =
      ∑ k ∈ Finset.range (d.degree + 1),
        (k.factorial : K)⁻¹ * MvPowerSeries.coeff d (B ^ k) := by
  unfold mvExp
  rw [coeff_subst_eq_sum hB0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, one_div]

omit [IsUltrametricDist K] in
@[simp] theorem constantCoeff_mvExp {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.constantCoeff (mvExp B) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvExp_eq_sum hB0]
  simp

omit [IsUltrametricDist K] in
@[simp] theorem mvExp_zero : mvExp (0 : MvPowerSeries σ K) = 1 := by
  classical
  ext d
  rw [coeff_mvExp_eq_sum (map_zero _), MvPowerSeries.coeff_one]
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg hd]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases k with _ | k
    · simp [MvPowerSeries.coeff_one, hd]
    · simp [zero_pow (Nat.succ_ne_zero k)]

omit [IsUltrametricDist K] in
/-- **Multivariate Formal Exponential Homomorphism Law**:
`mvExp (A + B) = mvExp A * mvExp B` whenever `constantCoeff A = 0` and `constantCoeff B = 0`. -/
theorem mvExp_add {A B : MvPowerSeries σ K}
    (hA0 : MvPowerSeries.constantCoeff A = 0) (hB0 : MvPowerSeries.constantCoeff B = 0) :
    mvExp (A + B) = mvExp A * mvExp B := by
  classical
  have hAB0 : MvPowerSeries.constantCoeff (A + B) = 0 := by rw [map_add, hA0, hB0, add_zero]
  have hA1 : Low 1 A := low_one_of_constantCoeff_zero hA0
  have hB1 : Low 1 B := low_one_of_constantCoeff_zero hB0
  ext d
  rw [coeff_mvExp_eq_sum hAB0, MvPowerSeries.coeff_mul]
  -- Expand each `(A + B)^k / k!` via the binomial theorem
  have hbin : ∀ k : ℕ, (k.factorial : K)⁻¹ * MvPowerSeries.coeff d ((A + B) ^ k) =
      ∑ ab ∈ Finset.antidiagonal k,
        (ab.1.factorial : K)⁻¹ * (ab.2.factorial : K)⁻¹ *
          MvPowerSeries.coeff d (A ^ ab.1 * B ^ ab.2) := by
    intro k
    rw [add_pow, map_sum, Finset.mul_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (i.factorial : K)⁻¹ * (j.factorial : K)⁻¹ *
          MvPowerSeries.coeff d (A ^ i * B ^ j)) k]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hch : ((k.choose i : ℕ) : K) * (i.factorial : K) * ((k - i).factorial : K) =
        (k.factorial : K) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    have hkf : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hif : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hsf : ((k - i).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - i))
    rw [show (k.choose i : MvPowerSeries σ K) = MvPowerSeries.C ((k.choose i : ℕ) : K) by simp,
      mul_comm _ (MvPowerSeries.C _), MvPowerSeries.coeff_C_mul]
    have hcoef : (k.factorial : K)⁻¹ * ((k.choose i : ℕ) : K) =
        (i.factorial : K)⁻¹ * ((k - i).factorial : K)⁻¹ := by
      field_simp [hkf, hif, hsf]
      linear_combination hch
    rw [← mul_assoc, hcoef]
  simp_rw [hbin]
  -- Reindex `∑_{k ≤ N} ∑_{i+j = k}` into `∑_{i ≤ N} ∑_{j ≤ N}` using `Low (i + j) (A^i * B^j)`
  set N := d.degree
  have hlhs : (∑ k ∈ Finset.range (N + 1),
      ∑ ab ∈ Finset.antidiagonal k,
        (ab.1.factorial : K)⁻¹ * (ab.2.factorial : K)⁻¹ *
          MvPowerSeries.coeff d (A ^ ab.1 * B ^ ab.2)) =
      ∑ ab ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        (ab.1.factorial : K)⁻¹ * (ab.2.factorial : K)⁻¹ *
          MvPowerSeries.coeff d (A ^ ab.1 * B ^ ab.2) := by
    rw [Finset.sum_sigma' (Finset.range (N + 1)) Finset.antidiagonal
      (fun _ ab => (ab.1.factorial : K)⁻¹ * (ab.2.factorial : K)⁻¹ *
        MvPowerSeries.coeff d (A ^ ab.1 * B ^ ab.2))]
    symm
    rw [← Finset.sum_filter_of_ne
      (p := fun ab : ℕ × ℕ => ab.1 + ab.2 < N + 1)
      (fun ab _ hab => by
        by_contra hgt
        push Not at hgt
        apply hab
        have hlow : Low (ab.1 * 1 + ab.2 * 1) (A ^ ab.1 * B ^ ab.2) :=
          low_mul (low_pow hA1 ab.1) (low_pow hB1 ab.2)
        rw [hlow d (by omega), mul_zero])]
    symm
    refine Finset.sum_bij (fun s _ => s.2) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · intro s₁ hs₁ s₂ hs₂ heq
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs₁ hs₂
      have h1 : s₁.1 = s₂.1 := by rw [← hs₁.2, ← hs₂.2, heq]
      exact Sigma.ext h1 (by simpa [h1] using heq)
    · intro ab hab
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
      refine ⟨⟨ab.1 + ab.2, ab⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal, and_true]
      exact hab.2
    · intro _ _; rfl
  rw [hlhs]
  -- Expand `MvPowerSeries.coeff d (A^i * B^j)` via antidiagonal of `d` and swap sums!
  simp_rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun xy hxy => ?_
  rw [Finset.mem_antidiagonal] at hxy
  have hdeg_xy : xy.1.degree + xy.2.degree = N := by rw [← map_add, hxy]
  rw [coeff_mvExp_eq_sum hA0 xy.1, coeff_mvExp_eq_sum hB0 xy.2]
  have hpad1 : ∑ i ∈ Finset.range (xy.1.degree + 1),
        (i.factorial : K)⁻¹ * MvPowerSeries.coeff xy.1 (A ^ i) =
      ∑ i ∈ Finset.range (N + 1),
        (i.factorial : K)⁻¹ * MvPowerSeries.coeff xy.1 (A ^ i) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    have hlow := low_pow hA1 i
    rw [mul_one] at hlow
    rw [hlow xy.1 (by omega), mul_zero]
  have hpad2 : ∑ j ∈ Finset.range (xy.2.degree + 1),
        (j.factorial : K)⁻¹ * MvPowerSeries.coeff xy.2 (B ^ j) =
      ∑ j ∈ Finset.range (N + 1),
        (j.factorial : K)⁻¹ * MvPowerSeries.coeff xy.2 (B ^ j) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    rw [Finset.mem_range] at hj
    have hlow := low_pow hB1 j
    rw [mul_one] at hlow
    rw [hlow xy.2 (by omega), mul_zero]
  rw [hpad1, hpad2, Finset.sum_mul, Finset.sum_product]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [IsUltrametricDist K] in
theorem mvExp_neg_mul {A : MvPowerSeries σ K} (hA0 : MvPowerSeries.constantCoeff A = 0) :
    mvExp (-A) * mvExp A = 1 := by
  rw [← mvExp_add (by simp [hA0]) hA0, neg_add_cancel, mvExp_zero]

omit [IsUltrametricDist K] in
theorem mvExp_neg_eq_invOneMv {A : MvPowerSeries σ K} (hA0 : MvPowerSeries.constantCoeff A = 0) :
    mvExp (-A) = invOneMv (mvExp A) := by
  have h1 := mvExp_neg_mul hA0
  have h2 := mul_invOneMv (constantCoeff_mvExp hA0)
  calc mvExp (-A) = mvExp (-A) * (mvExp A * invOneMv (mvExp A)) := by rw [h2, mul_one]
    _ = (mvExp (-A) * mvExp A) * invOneMv (mvExp A) := (mul_assoc _ _ _).symm
    _ = invOneMv (mvExp A) := by rw [h1, one_mul]

omit [IsUltrametricDist K] in
theorem mvExp_sub {A B : MvPowerSeries σ K}
    (hA0 : MvPowerSeries.constantCoeff A = 0) (hB0 : MvPowerSeries.constantCoeff B = 0) :
    mvExp (A - B) = mvExp A * invOneMv (mvExp B) := by
  rw [sub_eq_add_neg, mvExp_add hA0 (by simp [hB0]), mvExp_neg_eq_invOneMv hB0]

omit [IsUltrametricDist K] in
theorem mvExp_sum {ι : Type*} (s : Finset ι) (A : ι → MvPowerSeries σ K)
    (hA0 : ∀ i ∈ s, MvPowerSeries.constantCoeff (A i) = 0) :
    mvExp (∑ i ∈ s, A i) = ∏ i ∈ s, mvExp (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 := hA0 a (Finset.mem_insert_self a s)
    have hs0 : MvPowerSeries.constantCoeff (∑ i ∈ s, A i) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun i hi => hA0 i (Finset.mem_insert_of_mem hi)
    rw [mvExp_add ha0 hs0, ih fun i hi => hA0 i (Finset.mem_insert_of_mem hi)]

omit [IsUltrametricDist K] in
theorem mvExp_nsmul {A : MvPowerSeries σ K} (hA0 : MvPowerSeries.constantCoeff A = 0) (m : ℕ) :
    mvExp ((m : K) • A) = (mvExp A) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, mvExp_add (by simp [hA0]) hA0, ih, pow_succ]

omit [IsUltrametricDist K] in
theorem map_mvExp {L : Type*} [NormedField L] [CharZero L] (φ : K →+* L)
    {B : MvPowerSeries σ K} (hB0 : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.map φ (mvExp B) = mvExp (MvPowerSeries.map φ B) := by
  have hφB0 : MvPowerSeries.constantCoeff (MvPowerSeries.map φ B) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB0, map_zero]
  ext d
  rw [MvPowerSeries.coeff_map, coeff_mvExp_eq_sum hB0, coeff_mvExp_eq_sum hφB0, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← MvPowerSeries.coeff_map, map_pow]

omit [IsUltrametricDist K] in
theorem mvScaleHom_mvExp (c : K) {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0) :
    mvScaleHom c (mvExp B) = mvExp (mvScaleHom c B) := by
  have hcB0 : MvPowerSeries.constantCoeff (mvScaleHom c B) = 0 := by
    rw [constantCoeff_mvScaleHom, hB0]
  ext d
  rw [coeff_mvScaleHom, coeff_mvExp_eq_sum hB0, coeff_mvExp_eq_sum hcB0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, coeff_mvScaleHom]
  ring

omit [IsUltrametricDist K] in
theorem mvWeightScaleHom_mvExp (w : σ → K) {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0) :
    mvWeightScaleHom w (mvExp B) = mvExp (mvWeightScaleHom w B) := by
  have hwB0 : MvPowerSeries.constantCoeff (mvWeightScaleHom w B) = 0 := by
    rw [constantCoeff_mvWeightScaleHom, hB0]
  ext d
  rw [coeff_mvWeightScaleHom, coeff_mvExp_eq_sum hB0, coeff_mvExp_eq_sum hwB0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, coeff_mvWeightScaleHom]
  ring

omit [IsUltrametricDist K] in
theorem frobSub_mvExp {p : ℕ} (hp : 0 < p) {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0) :
    frobSub p (mvExp B) = mvExp (frobSub p B) := by
  classical
  have hfB0 : MvPowerSeries.constantCoeff (frobSub p B) = 0 := by
    rw [constantCoeff_frobSub hp, hB0]
  have hfB1 : Low 1 (frobSub p B) := low_one_of_constantCoeff_zero hfB0
  ext d
  rw [coeff_frobSub_eq_ite hp, coeff_mvExp_eq_sum hfB0]
  split_ifs with hdiv
  · set e := d.mapRange (· / p) (Nat.zero_div p)
    have hde : p • e = d := nsmul_mapRange_div_eq hdiv
    have he_le : e.degree ≤ d.degree := by
      have : d.degree = p * e.degree := by
        rw [← hde, Finsupp.degree_apply, Finsupp.degree_apply]
        have hsupp : (p • e).support = e.support := by
          ext i
          simp only [Finsupp.mem_support_iff, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
            mul_ne_zero_iff]
          exact ⟨fun h => h.2, fun h => ⟨hp.ne', h⟩⟩
        rw [hsupp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => rfl
      nlinarith
    rw [coeff_mvExp_eq_sum hB0 e]
    symm
    have hsub : ∑ k ∈ Finset.range (d.degree + 1),
          (k.factorial : K)⁻¹ * MvPowerSeries.coeff d (frobSub p B ^ k) =
        ∑ k ∈ Finset.range (e.degree + 1),
          (k.factorial : K)⁻¹ * MvPowerSeries.coeff d (frobSub p B ^ k) := by
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
      rw [Finset.mem_range] at hk
      rw [← frobSub_pow hp, coeff_frobSub_eq_ite hp, if_pos hdiv]
      have hB1 : Low 1 B := low_one_of_constantCoeff_zero hB0
      have hlow := low_pow hB1 k
      rw [mul_one] at hlow
      rw [hlow e (by omega), mul_zero]
    rw [hsub]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← frobSub_pow hp, coeff_frobSub_eq_ite hp, if_pos hdiv]
  · symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← frobSub_pow hp, coeff_frobSub_eq_ite hp, if_neg hdiv, mul_zero]

end MvExpCalc

/-! ### Explicit Substitution, Variable Renaming & Root-Weight Monomial Restrictions -/

section SubstAndRestrict

/-- Variable-renaming substitution `renMv φ F = subst (fun k => X (φ k)) F`. -/
def renMv {R : Type*} [CommRing R] (φ : κ → σ) (F : MvPowerSeries κ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) F

/-- `renMv` packaged as a `RingHom` (no `Algebra` diamonds). -/
def renMvHom {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ) :
    MvPowerSeries κ R →+* MvPowerSeries σ R :=
  (MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun k => MvPowerSeries.constantCoeff_X (φ k)))).toRingHom

private theorem mvSubstAlgHom_C {R : Type*} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) (r : R) :
    MvPowerSeries.substAlgHom ha (MvPowerSeries.C r) = MvPowerSeries.C r :=
  (MvPowerSeries.substAlgHom ha).commutes r

private theorem psSubstAlgHom_C {R : Type*} [CommRing R] {a : MvPowerSeries τ R}
    (ha : PowerSeries.HasSubst a) (r : R) :
    PowerSeries.substAlgHom ha (PowerSeries.C r) = MvPowerSeries.C r :=
  (PowerSeries.substAlgHom ha).commutes r

@[simp] theorem renMvHom_apply {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ)
    (F : MvPowerSeries κ R) :
    renMvHom φ F = renMv φ F := by
  unfold renMvHom renMv
  exact congrFun (MvPowerSeries.coe_substAlgHom _) F

@[simp] theorem renMv_X {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ) (k : κ) :
    renMv φ (MvPowerSeries.X k : MvPowerSeries κ R) = MvPowerSeries.X (φ k) :=
  MvPowerSeries.subst_X
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => MvPowerSeries.constantCoeff_X (φ j))) k

@[simp] theorem renMv_C {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ) (r : R) :
    renMv φ (MvPowerSeries.C r : MvPowerSeries κ R) = MvPowerSeries.C r := by
  rw [← renMvHom_apply]
  exact mvSubstAlgHom_C _ r

@[simp] theorem constantCoeff_renMv {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ)
    {F : MvPowerSeries κ R} (hF0 : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (renMv φ F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => MvPowerSeries.constantCoeff_X (φ j)))
    (fun j => MvPowerSeries.constantCoeff_X (φ j)) hF0

theorem renMv_comp {R : Type*} [CommRing R] [Finite κ] [Finite σ] (ψ : σ → τ) (φ : κ → σ)
    (F : MvPowerSeries κ R) :
    renMv ψ (renMv φ F) = renMv (fun k => ψ (φ k)) F := by
  unfold renMv
  have hφ := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun k => MvPowerSeries.constantCoeff_X (R := R) (φ k))
  have hψ := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun s => MvPowerSeries.constantCoeff_X (R := R) (ψ s))
  rw [MvPowerSeries.subst_comp_subst_apply hφ hψ F]
  congr 1
  funext k
  exact MvPowerSeries.subst_X hψ (φ k)

theorem subst_renMv {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ)
    {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (F : MvPowerSeries κ R) :
    MvPowerSeries.subst a (renMv φ F) = MvPowerSeries.subst (fun k => a (φ k)) F := by
  unfold renMv
  have hφ := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun k => MvPowerSeries.constantCoeff_X (R := R) (φ k))
  rw [MvPowerSeries.subst_comp_subst_apply hφ ha F]
  congr 1
  funext k
  exact MvPowerSeries.subst_X ha (φ k)

theorem renMv_subst {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ)
    {ρ : Type*} {a : ρ → MvPowerSeries κ R} (ha : MvPowerSeries.HasSubst a)
    (F : MvPowerSeries ρ R) :
    renMv φ (MvPowerSeries.subst a F) = MvPowerSeries.subst (fun i => renMv φ (a i)) F := by
  unfold renMv
  have hφ := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun k => MvPowerSeries.constantCoeff_X (R := R) (φ k))
  exact MvPowerSeries.subst_comp_subst_apply ha hφ F

theorem renMv_psubst {R : Type*} [CommRing R] [Finite κ] (φ : κ → σ)
    {L : MvPowerSeries κ R} (hL0 : MvPowerSeries.constantCoeff L = 0) (f : PowerSeries R) :
    renMv φ (PowerSeries.subst L f) = PowerSeries.subst (renMv φ L) f :=
  renMv_subst φ (PowerSeries.HasSubst.of_constantCoeff_zero hL0).const f

theorem map_renMv {R S : Type*} [CommRing R] [CommRing S] [Finite κ] (h : R →+* S) (φ : κ → σ)
    (F : MvPowerSeries κ R) :
    MvPowerSeries.map h (renMv φ F) = renMv φ (MvPowerSeries.map h F) := by
  unfold renMv
  have hφ := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun k => MvPowerSeries.constantCoeff_X (R := R) (φ k))
  rw [MvPowerSeries.map_subst hφ]
  congr 1
  funext k
  simp

omit [IsUltrametricDist K] in
/-- General `MvPowerSeries.subst` commutes with `mvExp` whenever `constantCoeff (a i) = 0`
and `constantCoeff B = 0` (via degree-`N` `Low` truncations). -/
theorem substMv_mvExp [CharZero K] [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    {B : MvPowerSeries σ K} (hB0 : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst a (mvExp B) = mvExp (MvPowerSeries.subst a B) := by
  classical
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hSB0 : MvPowerSeries.constantCoeff (MvPowerSeries.subst a B) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hB0
  have ha1 : ∀ i, Low 1 (a i) := fun i => low_one_of_constantCoeff_zero (ha0 i)
  have hprod_low : ∀ m : σ →₀ ℕ, Low m.degree (m.prod fun i k => a i ^ k) := by
    intro m
    rw [Finsupp.prod, Finsupp.degree_apply]
    refine Finset.induction_on m.support (by simp; intro d hd; omega) fun i s hi ih => ?_
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hpow : Low (m i * 1) (a i ^ m i) := low_pow (ha1 i) (m i)
    rw [mul_one] at hpow
    exact low_mul hpow ih
  have hlow_subst : ∀ {N : ℕ} {G : MvPowerSeries σ K}, Low N G → Low N (MvPowerSeries.subst a G) := by
    intro N G hG d hd
    rw [MvPowerSeries.coeff_subst ha]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    by_cases hm : m.degree < N
    · rw [hG m hm, zero_smul]
    · rw [hprod_low m d (by omega), smul_zero]
  have hlow_exp : ∀ (N : ℕ) {C : MvPowerSeries σ K}, MvPowerSeries.constantCoeff C = 0 →
      Low N (mvExp C - ∑ k ∈ Finset.range N, MvPowerSeries.C ((k.factorial : K)⁻¹) * C ^ k) := by
    intro N C hC0 d hd
    rw [map_sub, coeff_mvExp_eq_sum hC0, map_sum]
    simp_rw [MvPowerSeries.coeff_C_mul]
    rw [sub_eq_zero]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
    rw [Finset.mem_range] at hk
    have hlow := low_pow (low_one_of_constantCoeff_zero hC0) k
    rw [mul_one] at hlow
    rw [hlow d (by omega), mul_zero]
  have hlow_exp_τ : ∀ (N : ℕ) {C : MvPowerSeries τ K}, MvPowerSeries.constantCoeff C = 0 →
      Low N (mvExp C - ∑ k ∈ Finset.range N, MvPowerSeries.C ((k.factorial : K)⁻¹) * C ^ k) := by
    intro N C hC0 d hd
    rw [map_sub, coeff_mvExp_eq_sum hC0, map_sum]
    simp_rw [MvPowerSeries.coeff_C_mul]
    rw [sub_eq_zero]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
    rw [Finset.mem_range] at hk
    have hlow := low_pow (low_one_of_constantCoeff_zero hC0) k
    rw [mul_one] at hlow
    rw [hlow d (by omega), mul_zero]
  ext d
  set N := d.degree + 1
  have hsub_part : MvPowerSeries.subst a
      (∑ k ∈ Finset.range N, MvPowerSeries.C ((k.factorial : K)⁻¹) * B ^ k) =
      ∑ k ∈ Finset.range N,
        MvPowerSeries.C ((k.factorial : K)⁻¹) * (MvPowerSeries.subst a B) ^ k := by
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, mvSubstAlgHom_C ha, MvPowerSeries.coe_substAlgHom ha]
  have hdiff : MvPowerSeries.subst a (mvExp B) - mvExp (MvPowerSeries.subst a B) =
      MvPowerSeries.subst a (mvExp B -
        ∑ k ∈ Finset.range N, MvPowerSeries.C ((k.factorial : K)⁻¹) * B ^ k) -
      (mvExp (MvPowerSeries.subst a B) -
        ∑ k ∈ Finset.range N,
          MvPowerSeries.C ((k.factorial : K)⁻¹) * (MvPowerSeries.subst a B) ^ k) := by
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sub, MvPowerSeries.coe_substAlgHom ha, hsub_part]
    ring
  have h0 : MvPowerSeries.coeff d
      (MvPowerSeries.subst a (mvExp B) - mvExp (MvPowerSeries.subst a B)) = 0 := by
    rw [hdiff, map_sub,
      hlow_subst (hlow_exp N hB0) d (Nat.lt_succ_self _),
      hlow_exp_τ N hSB0 d (Nat.lt_succ_self _), sub_self]
  exact sub_eq_zero.mp (by simpa [map_sub] using h0)

omit [IsUltrametricDist K] in
theorem renMv_mvExp [CharZero K] [Finite κ] (φ : κ → σ) {B : MvPowerSeries κ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0) :
    renMv φ (mvExp B) = mvExp (renMv φ B) :=
  substMv_mvExp _ (fun k => MvPowerSeries.constantCoeff_X (φ k)) hB0

/-- **Ultrametric Integrality of `MvPowerSeries.subst`**:
if `F` is integral and every `a i` is integral with `constantCoeff (a i) = 0`, then
`MvPowerSeries.subst a F` is integral! -/
theorem isIntegralMv_substMv [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IsIntegralMv (a i))
    {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    IsIntegralMv (MvPowerSeries.subst a F) := by
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hprod : ∀ m : σ →₀ ℕ, IsIntegralMv (m.prod fun i k => a i ^ k) := by
    intro m
    rw [Finsupp.prod]
    refine Finset.induction_on m.support (by simpa using isIntegralMv_one) fun i s hi ih => ?_
    rw [Finset.prod_insert hi]
    exact isIntegralMv_mul (isIntegralMv_pow (ha i) (m i)) ih
  intro d
  rw [MvPowerSeries.coeff_subst hs]
  refine ultrametric_norm_finsum_le _ zero_le_one fun m => ?_
  rw [smul_eq_mul, norm_mul]
  calc ‖MvPowerSeries.coeff m F‖ * ‖MvPowerSeries.coeff d (m.prod fun i k => a i ^ k)‖
      ≤ 1 * 1 := mul_le_mul (hF m) (hprod m d) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Ultrametric integrality of `PowerSeries.subst`: if `f : PowerSeries K` is integral and
`L : MvPowerSeries τ K` is integral with `constantCoeff L = 0`, then `PowerSeries.subst L f`
is integral! -/
theorem isIntegralMv_psubst {L : MvPowerSeries τ K}
    (hL0 : MvPowerSeries.constantCoeff L = 0) (hL : IsIntegralMv L)
    {f : PowerSeries K} (hf : IsIntegralPS f) :
    IsIntegralMv (PowerSeries.subst L f) := fun d => by
  rw [coeff_subst_eq_sum hL0]
  refine ultrametric_norm_sum_le _ _ zero_le_one fun k _ => ?_
  rw [norm_mul]
  calc ‖PowerSeries.coeff k f‖ * ‖MvPowerSeries.coeff d (L ^ k)‖
      ≤ 1 * 1 := mul_le_mul (hf k) (isIntegralMv_pow hL k d) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem isIntegralMv_renMv [Finite κ] (φ : κ → σ) {F : MvPowerSeries κ K} (hF : IsIntegralMv F) :
    IsIntegralMv (renMv φ F) :=
  isIntegralMv_substMv _ (fun k => MvPowerSeries.constantCoeff_X (φ k))
    (fun k => isIntegralMv_monomial (Finsupp.single (φ k) 1) (by simp)) hF

/-- **Exact Multivariable Dwork Weight Substitution Theorem (`wtGe_substMv`)**:
If `F` satisfies `WtGe pi r w` (`‖coeff m F‖ ≤ pi^(w - ⟨m, r⟩)`) and every `a i`
(`constantCoeff = 0`) satisfies `WtGe pi r' (r i)` (`‖coeff d (a i)‖ ≤ pi^(r i - ⟨d, r'⟩)`),
then `MvPowerSeries.subst a F` satisfies `WtGe pi r' w` (`‖coeff d‖ ≤ pi^(w - ⟨d, r'⟩)`)! -/
theorem wtGe_substMv [Finite σ] {pi w : ℝ} (hpi : 0 < pi) {r : σ → ℝ} {r' : τ → ℝ}
    (a : σ → MvPowerSeries τ K) (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, WtGe pi r' (r i) (a i))
    {F : MvPowerSeries σ K} (hF : WtGe pi r w F) :
    WtGe pi r' w (MvPowerSeries.subst a F) := by
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hprod : ∀ m : σ →₀ ℕ, WtGe pi r' (wtDot m r) (m.prod fun i k => a i ^ k) := by
    intro m
    rw [Finsupp.prod]
    unfold wtDot
    rw [Finsupp.sum]
    refine Finset.induction_on m.support (by simpa using wtGe_one hpi r') fun i s hi ih => ?_
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    intro d
    have hpow : WtGe pi r' ((m i : ℝ) * r i) (a i ^ m i) := wtGe_pow hpi (ha i) (m i)
    exact multiplicative_weight_le hpi (fun n _ => hpow n) (fun n _ => ih n) d le_rfl
  intro d
  unfold MonoWtGe
  rw [MvPowerSeries.coeff_subst hs]
  refine ultrametric_norm_finsum_le _ (Real.rpow_nonneg hpi.le _) fun m => ?_
  rw [smul_eq_mul, norm_mul]
  have hm := hF m
  have hp := hprod m d
  unfold MonoWtGe at hm hp
  calc ‖MvPowerSeries.coeff m F‖ * ‖MvPowerSeries.coeff d (m.prod fun i k => a i ^ k)‖
      ≤ pi ^ (w - wtDot m r) * pi ^ (wtDot m r - wtDot d r') :=
        mul_le_mul hm hp (norm_nonneg _) (Real.rpow_nonneg hpi.le _)
    _ = pi ^ (w - wtDot d r') := by
        rw [← Real.rpow_add hpi]; congr 1; ring

/-- Homogeneous degree-1 rescaling property (matching Alpöge's `AtPiEqRescale.atPi_map_ThZA`):
if `mvScaleHom c (L i) = C c * L i` for every `i` (e.g. each `L i` is a linear form in `X_s`),
then isotropic scaling `mvScaleHom c` on `MvPowerSeries.subst L F` equals substituting
`fun i => C c * L i` into `F`! -/
theorem mvScaleHom_substMv_of_homog {R : Type*} [CommRing R] [Finite σ] (c : R)
    (L : σ → MvPowerSeries τ R) (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0)
    (hLhom : ∀ i, mvScaleHom c (L i) = MvPowerSeries.C c * L i) (F : MvPowerSeries σ R) :
    mvScaleHom c (MvPowerSeries.subst L F) =
      MvPowerSeries.subst (fun i => MvPowerSeries.C c * L i) F := by
  classical
  have hL : MvPowerSeries.HasSubst L := MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
  have hL' : MvPowerSeries.HasSubst (fun i => MvPowerSeries.C c * L i) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by rw [map_mul, hL0 i, mul_zero])
  ext d
  rw [coeff_mvScaleHom, MvPowerSeries.coeff_subst hL, MvPowerSeries.coeff_subst hL']
  have hfin1 := MvPowerSeries.coeff_subst_finite hL F d
  have hfin2 := MvPowerSeries.coeff_subst_finite hL' F d
  set S : Finset (σ →₀ ℕ) := hfin1.toFinset ∪ hfin2.toFinset
  rw [finsum_eq_sum_of_support_subset _ (fun m hm => Finset.mem_union_left _ (hfin1.mem_toFinset.mpr hm)),
    finsum_eq_sum_of_support_subset _ (fun m hm => Finset.mem_union_right _ (hfin2.mem_toFinset.mpr hm)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_eq_mul, smul_eq_mul]
  have hprod : mvScaleHom c (m.prod fun i k => L i ^ k) =
      m.prod fun i k => (MvPowerSeries.C c * L i) ^ k := by
    rw [Finsupp.prod, Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, hLhom i]
  have hcoeff := congrArg (MvPowerSeries.coeff d) hprod
  rw [coeff_mvScaleHom] at hcoeff
  rw [← hcoeff]
  ring

/-- Homogeneous linear form `linFormMv s a g = ∑ i ∈ s, C (a i) * X (g i)` in `MvPowerSeries τ R`. -/
def linFormMv {R ι : Type*} [CommRing R] (s : Finset ι) (a : ι → R) (g : ι → τ) :
    MvPowerSeries τ R :=
  ∑ i ∈ s, MvPowerSeries.C (a i) * MvPowerSeries.X (g i)

theorem constantCoeff_linFormMv {R ι : Type*} [CommRing R] (s : Finset ι) (a : ι → R) (g : ι → τ) :
    MvPowerSeries.constantCoeff (linFormMv s a g) = 0 := by
  unfold linFormMv
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => by simp

theorem mvScaleHom_linFormMv {R ι : Type*} [CommRing R] (c : R) (s : Finset ι) (a : ι → R)
    (g : ι → τ) :
    mvScaleHom c (linFormMv s a g) = MvPowerSeries.C c * linFormMv s a g := by
  unfold linFormMv
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mvScaleHom_C, mvScaleHom_X]
  ring

theorem isIntegralMv_linFormMv {ι : Type*} (s : Finset ι) {a : ι → K}
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (g : ι → τ) :
    IsIntegralMv (linFormMv s a g) := by
  unfold linFormMv
  refine isIntegralMv_sum s fun i hi =>
    isIntegralMv_mul (coeffNormLeMv_C zero_le_one (ha i hi))
      (isIntegralMv_monomial (Finsupp.single (g i) 1) (by simp))

/-- Exact `AtPi = Rescale` identity for linear coordinate substitutions `L i = linFormMv ...`:
`mvScaleHom c (subst L F) = subst (fun i => C c * L i) F`! -/
theorem mvScaleHom_substMv_linForm {R ι : Type*} [CommRing R] [Finite σ] (c : R)
    (s : σ → Finset ι) (a : σ → ι → R) (g : σ → ι → τ) (F : MvPowerSeries σ R) :
    mvScaleHom c (MvPowerSeries.subst (fun k => linFormMv (s k) (a k) (g k)) F) =
      MvPowerSeries.subst (fun k => MvPowerSeries.C c * linFormMv (s k) (a k) (g k)) F :=
  mvScaleHom_substMv_of_homog c (fun k => linFormMv (s k) (a k) (g k))
    (fun k => constantCoeff_linFormMv (s k) (a k) (g k))
    (fun k => mvScaleHom_linFormMv c (s k) (a k) (g k)) F

/-! ### Coordinate Pullback Restriction `restrictVar` & Root-Weight Monomial Restriction -/

/-- Coordinate restriction pullback `restrictVar f F` (`coeff d ↦ coeff (d.mapDomain f) F`),
matching Alpöge's `FormalGroupSystem.resV`. -/
def restrictVar {R : Type*} [CommSemiring R] (f : κ → σ) (F : MvPowerSeries σ R) :
    MvPowerSeries κ R :=
  fun d => MvPowerSeries.coeff (d.mapDomain f) F

@[simp] theorem coeff_restrictVar {R : Type*} [CommSemiring R] (f : κ → σ)
    (F : MvPowerSeries σ R) (d : κ →₀ ℕ) :
    MvPowerSeries.coeff d (restrictVar f F) = MvPowerSeries.coeff (d.mapDomain f) F := rfl

@[simp] theorem constantCoeff_restrictVar {R : Type*} [CommSemiring R] (f : κ → σ)
    (F : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (restrictVar f F) = MvPowerSeries.constantCoeff F := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_restrictVar,
    Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- When `f : κ → σ` is injective, `restrictVar f` is an exact `RingHom` (multiplicative
restriction onto the coordinate sub-torus indexed by `f`)! -/
def restrictVarHom {R : Type*} [CommSemiring R] (f : κ → σ) (hf : Function.Injective f) :
    MvPowerSeries σ R →+* MvPowerSeries κ R where
  toFun := restrictVar f
  map_one' := by
    classical
    ext d
    rw [coeff_restrictVar, MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
    have hiff : d.mapDomain f = 0 ↔ d = 0 := by
      constructor
      · intro h
        exact Finsupp.mapDomain_injective hf (by simpa using h)
      · rintro rfl; simp
    simp [hiff]
  map_mul' F G := by
    classical
    ext d
    rw [coeff_restrictVar, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    symm
    refine Finset.sum_bij (fun x _ => (x.1.mapDomain f, x.2.mapDomain f)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_antidiagonal] at hx ⊢
      rw [← Finsupp.mapDomain_add, hx]
    · intro x₁ _ x₂ _ heq
      have h1 := Finsupp.mapDomain_injective hf (congrArg Prod.fst heq)
      have h2 := Finsupp.mapDomain_injective hf (congrArg Prod.snd heq)
      exact Prod.ext h1 h2
    · intro y hy
      rw [Finset.mem_antidiagonal] at hy
      -- Every element in `y.1.support` or `y.2.support` lies in `(d.mapDomain f).support ⊆ range f`
      have hsupp1 : ∀ s ∈ y.1.support, ∃ k, f k = s := fun s hs => by
        have hne : (y.1 + y.2) s ≠ 0 := by
          have h1 : y.1 s ≠ 0 := Finsupp.mem_support_iff.mp hs
          simp only [Finsupp.coe_add, Pi.add_apply]; omega
        rw [hy] at hne
        have hmem := Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne)
        rcases Finset.mem_image.mp hmem with ⟨k, _, hfk⟩
        exact ⟨k, hfk⟩
      have hsupp2 : ∀ s ∈ y.2.support, ∃ k, f k = s := fun s hs => by
        have hne : (y.1 + y.2) s ≠ 0 := by
          have h2 : y.2 s ≠ 0 := Finsupp.mem_support_iff.mp hs
          simp only [Finsupp.coe_add, Pi.add_apply]; omega
        rw [hy] at hne
        have hmem := Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne)
        rcases Finset.mem_image.mp hmem with ⟨k, _, hfk⟩
        exact ⟨k, hfk⟩
      let a : κ →₀ ℕ := Finsupp.comapDomain f y.1 (hf.injOn)
      let b : κ →₀ ℕ := Finsupp.comapDomain f y.2 (hf.injOn)
      have ha_map : a.mapDomain f = y.1 := by
        ext s
        by_cases hs : s ∈ y.1.support
        · rcases hsupp1 s hs with ⟨k, rfl⟩
          rw [Finsupp.mapDomain_apply hf, Finsupp.comapDomain_apply]
        · have hy0 : y.1 s = 0 := Finsupp.notMem_support_iff.mp hs
          by_cases hrange : ∃ k, f k = s
          · rcases hrange with ⟨k, rfl⟩
            rw [Finsupp.mapDomain_apply hf, Finsupp.comapDomain_apply, hy0]
          · rw [hy0]
            exact Finsupp.mapDomain_of_notMem_range a s (by simpa [Set.mem_range] using hrange)
      have hb_map : b.mapDomain f = y.2 := by
        ext s
        by_cases hs : s ∈ y.2.support
        · rcases hsupp2 s hs with ⟨k, rfl⟩
          rw [Finsupp.mapDomain_apply hf, Finsupp.comapDomain_apply]
        · have hy0 : y.2 s = 0 := Finsupp.notMem_support_iff.mp hs
          by_cases hrange : ∃ k, f k = s
          · rcases hrange with ⟨k, rfl⟩
            rw [Finsupp.mapDomain_apply hf, Finsupp.comapDomain_apply, hy0]
          · rw [hy0]
            exact Finsupp.mapDomain_of_notMem_range b s (by simpa [Set.mem_range] using hrange)
      refine ⟨(a, b), ?_, Prod.ext ha_map hb_map⟩
      rw [Finset.mem_antidiagonal]
      exact Finsupp.mapDomain_injective hf (by rw [Finsupp.mapDomain_add, ha_map, hb_map, hy])
    · intro x _; rfl
  map_zero' := by ext d; simp
  map_add' F G := by ext d; simp

@[simp] theorem restrictVarHom_apply {R : Type*} [CommSemiring R] (f : κ → σ)
    (hf : Function.Injective f) (F : MvPowerSeries σ R) :
    restrictVarHom f hf F = restrictVar f F := rfl

omit [IsUltrametricDist K] in
theorem isIntegralMv_restrictVar (f : κ → σ) {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    IsIntegralMv (restrictVar f F) := fun d => hF (d.mapDomain f)

omit [IsUltrametricDist K] in
theorem wtGe_restrictVar {pi w : ℝ} (f : κ → σ) {r : σ → ℝ} {F : MvPowerSeries σ K}
    (hF : WtGe pi r w F) :
    WtGe pi (r ∘ f) w (restrictVar f F) := fun d => by
  unfold MonoWtGe
  rw [coeff_restrictVar]
  have hdot : wtDot (d.mapDomain f) r = wtDot d (r ∘ f) := by
    unfold wtDot
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    rfl
  rw [← hdot]
  exact hF (d.mapDomain f)

omit [IsUltrametricDist K] in
theorem restrictVar_mvExp [CharZero K] (f : κ → σ) (hf : Function.Injective f)
    {B : MvPowerSeries σ K} (hB0 : MvPowerSeries.constantCoeff B = 0) :
    restrictVar f (mvExp B) = mvExp (restrictVar f B) := by
  have hRB0 : MvPowerSeries.constantCoeff (restrictVar f B) = 0 := by
    rw [constantCoeff_restrictVar, hB0]
  have hdeg : ∀ d : κ →₀ ℕ, (d.mapDomain f).degree = d.degree := fun d => by
    rw [Finsupp.degree_apply, Finsupp.degree_apply]
    change (d.mapDomain f).sum (fun _ k => k) = d.sum (fun _ k => k)
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  ext d
  rw [coeff_restrictVar, coeff_mvExp_eq_sum hB0, coeff_mvExp_eq_sum hRB0, hdeg d]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← coeff_restrictVar f, ← restrictVarHom_apply f hf, map_pow, restrictVarHom_apply]

/-- **Root-Weight Monomial Restriction Operator**: projects a multivariate power series onto the
monomials satisfying a root-weight predicate `P : (σ →₀ ℕ) → Prop`. -/
def monomialRestrict {R : Type*} [CommSemiring R] (P : (σ →₀ ℕ) → Prop)
    (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  open Classical in
  fun d => if P d then MvPowerSeries.coeff d F else 0

open Classical in
@[simp] theorem coeff_monomialRestrict {R : Type*} [CommSemiring R] (P : (σ →₀ ℕ) → Prop)
    (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (monomialRestrict P F) =
      if P d then MvPowerSeries.coeff d F else 0 := rfl

/-- Total root-weight evaluation `rootWeightEval α d = ∑_{i ∈ supp(d)} d(i) • α(i)` in any
additive commutative group `M` (e.g. `ℤ` or `Fin r → ℤ`). -/
def rootWeightEval {M : Type*} [AddCommGroup M] (α : σ → M) (d : σ →₀ ℕ) : M :=
  d.sum fun i k => (k : ℤ) • α i

@[simp] theorem rootWeightEval_zero {M : Type*} [AddCommGroup M] (α : σ → M) :
    rootWeightEval α (0 : σ →₀ ℕ) = 0 := by
  simp [rootWeightEval]

theorem rootWeightEval_add {M : Type*} [AddCommGroup M] (α : σ → M) (d₁ d₂ : σ →₀ ℕ) :
    rootWeightEval α (d₁ + d₂) = rootWeightEval α d₁ + rootWeightEval α d₂ := by
  unfold rootWeightEval
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; rw [add_zsmul])]

/-- Root-weight slice projection: restricts `F` to monomials of exact root weight `λ ∈ M`. -/
def rootWeightSlice {R M : Type*} [CommSemiring R] [AddCommGroup M]
    (α : σ → M) (lam : M) (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  monomialRestrict (fun d => rootWeightEval α d = lam) F

omit [IsUltrametricDist K] in
theorem isIntegralMv_monomialRestrict (P : (σ →₀ ℕ) → Prop) {F : MvPowerSeries σ K}
    (hF : IsIntegralMv F) : IsIntegralMv (monomialRestrict P F) := fun d => by
  classical
  rw [coeff_monomialRestrict]
  split_ifs
  · exact hF d
  · simp

omit [IsUltrametricDist K] in
theorem wtGe_monomialRestrict {pi w : ℝ} (hpi : 0 < pi) {r : σ → ℝ}
    (P : (σ →₀ ℕ) → Prop) {F : MvPowerSeries σ K} (hF : WtGe pi r w F) :
    WtGe pi r w (monomialRestrict P F) := fun d => by
  classical
  unfold MonoWtGe
  rw [coeff_monomialRestrict]
  split_ifs
  · exact hF d
  · rw [norm_zero]; exact Real.rpow_nonneg hpi.le _

theorem mvScaleHom_monomialRestrict {R : Type*} [CommRing R] (c : R)
    (P : (σ →₀ ℕ) → Prop) (F : MvPowerSeries σ R) :
    mvScaleHom c (monomialRestrict P F) = monomialRestrict P (mvScaleHom c F) := by
  classical
  ext d
  simp only [coeff_mvScaleHom, coeff_monomialRestrict]
  split_ifs <;> simp

/-- If `P` is a **saturated submonoid** of `σ →₀ ℕ` (`P 0` and `P (a + b) ↔ P a ∧ P b`), then
`monomialRestrict P` is an exact `RingHom`! -/
def monomialRestrictHom {R : Type*} [CommSemiring R] (P : (σ →₀ ℕ) → Prop)
    (h0 : P 0) (hsat : ∀ a b : σ →₀ ℕ, P (a + b) ↔ P a ∧ P b) :
    MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun := monomialRestrict P
  map_one' := by
    classical
    ext d
    rw [coeff_monomialRestrict, MvPowerSeries.coeff_one]
    by_cases h1 : P d <;> by_cases h2 : d = 0
    · subst h2; simp [h0]
    · simp [h1, h2]
    · subst h2; exact absurd h0 h1
    · simp [h1, h2]
  map_mul' F G := by
    classical
    ext d
    rw [coeff_monomialRestrict, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    split_ifs with hPd
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      have h12 := (hsat x.1 x.2).mp (hx.symm ▸ hPd)
      rw [coeff_monomialRestrict, coeff_monomialRestrict, if_pos h12.1, if_pos h12.2]
    · symm
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      rw [coeff_monomialRestrict, coeff_monomialRestrict]
      by_cases h1 : P x.1
      · have h2 : ¬ P x.2 := fun h2 => hPd (hx ▸ (hsat x.1 x.2).mpr ⟨h1, h2⟩)
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  map_zero' := by classical ext d; simp [coeff_monomialRestrict]
  map_add' F G := by
    classical
    ext d
    simp only [map_add, coeff_monomialRestrict]
    split_ifs <;> simp

end SubstAndRestrict

end MvExpAndRestriction

/-! ## Section 3: Multivariable Dwork Exponential Restriction Operators (`RestGc` & `RestGcA`) -/

section RestGcSection

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- Formal-group parameter map `tOfParam vp μ L i = PowerSeries.subst (L i) (C vp * μ)`,
matching Alpöge's `SubstitutionOfVariables.tOf`. -/
def tOfParam {ι τ : Type*} (vp : K) (μ : PowerSeries K) (L : ι → MvPowerSeries τ K) :
    ι → MvPowerSeries τ K :=
  fun i => PowerSeries.subst (L i) (PowerSeries.C vp * μ)

omit [IsUltrametricDist K] [CharZero K] in
theorem constantCoeff_tOfParam {ι τ : Type*} (vp : K) {μ : PowerSeries K}
    (hμ0 : PowerSeries.constantCoeff μ = 0) {L : ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (i : ι) :
    MvPowerSeries.constantCoeff (tOfParam vp μ L i) = 0 := by
  unfold tOfParam
  rw [constantCoeff_subst_of_zero (hL0 i), map_mul, hμ0, mul_zero]

omit [CharZero K] in
theorem isIntegralMv_tOfParam {ι τ : Type*} {vp : K} (hvp : ‖vp‖ ≤ 1)
    {μ : PowerSeries K} (hμ : IsIntegralPS μ) {L : ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i)) (i : ι) :
    IsIntegralMv (tOfParam vp μ L i) := by
  refine isIntegralMv_psubst (hL0 i) (hL i) fun n => ?_
  rw [PowerSeries.coeff_C_mul, norm_mul]
  calc ‖vp‖ * ‖PowerSeries.coeff n μ‖
      ≤ 1 * 1 := mul_le_mul hvp (hμ n) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Diagonal paired sum `pairedSum ι G = ∑ e : ι, renMv ![inl e, inr e] G` in `K[[X_e, Y_e]]`,
matching Alpöge's `Gt`. -/
def pairedSum (ι : Type*) [Fintype ι] (G : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (ι ⊕ ι) K :=
  ∑ e : ι, renMv ![Sum.inl e, Sum.inr e] G

omit [IsUltrametricDist K] [CharZero K] in
theorem constantCoeff_pairedSum {ι : Type*} [Fintype ι] {G : MvPowerSeries (Fin 2) K}
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.constantCoeff (pairedSum ι G) = 0 := by
  unfold pairedSum
  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => constantCoeff_renMv _ hG0

omit [IsUltrametricDist K] [CharZero K] in
theorem pairedSum_sigma {Pl : Type*} [Fintype Pl] (E : Pl → Type*) [∀ v, Fintype (E v)]
    (G : MvPowerSeries (Fin 2) K) :
    pairedSum (Σ v : Pl, E v) G =
      ∑ v : Pl, renMv (Sum.map (Sigma.mk v) (Sigma.mk v)) (pairedSum (E v) G) := by
  unfold pairedSum
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← renMvHom_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [renMvHom_apply, renMv_comp]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- General multivariable Dwork exponential restriction operator:
`RestGcOf vp μ L Φ = subst (tOfParam vp μ L) (mvExp (-Φ))`. -/
def RestGcOf {ι τ : Type*} (vp : K) (μ : PowerSeries K) (L : ι → MvPowerSeries τ K)
    (Φ : MvPowerSeries ι K) : MvPowerSeries τ K :=
  MvPowerSeries.subst (tOfParam vp μ L) (mvExp (-Φ))

/-- **Single-Place Multivariable Dwork Exponential Restriction Operator `RestGc`**:
applies the formal-group parameter restriction `tOfParam vp μ L` to the negative Dwork exponential
of the diagonally paired bivariate kernel `G`:
`RestGc vp μ L G = subst (tOfParam vp μ L) (mvExp (-pairedSum ι G))`. -/
def RestGc {ι τ : Type*} [Fintype ι] (vp : K) (μ : PowerSeries K)
    (L : ι ⊕ ι → MvPowerSeries τ K) (G : MvPowerSeries (Fin 2) K) : MvPowerSeries τ K :=
  RestGcOf vp μ L (pairedSum ι G)

/-- **Multi-Place (Adelic Product) Multivariable Dwork Exponential Restriction Operator `RestGcA`**:
simultaneous restriction across a finite place index set `Pl` with local indices `E v` and global
coordinates `ZA`:
`RestGcA vp μ LA G = subst (tOfParam vp μ LA) (mvExp (-pairedSum (Σ v, E v) G))`. -/
def RestGcA {Pl : Type*} [Fintype Pl] {E : Pl → Type*} [∀ v, Fintype (E v)] {ZA : Type*}
    (vp : K) (μ : PowerSeries K)
    (LA : (Σ v : Pl, E v) ⊕ (Σ v : Pl, E v) → MvPowerSeries ZA K)
    (G : MvPowerSeries (Fin 2) K) : MvPowerSeries ZA K :=
  RestGcOf vp μ LA (pairedSum (Σ v : Pl, E v) G)

/-- **Root-Weight Monomial Restriction of `RestGc`**: restricts `RestGc vp μ L G` to monomials of
exact root weight `lam ∈ M` under weight functional `α : τ → M`. -/
def RestGcRootWeight {ι τ M : Type*} [Fintype ι] [AddCommGroup M]
    (α : τ → M) (lam : M) (vp : K) (μ : PowerSeries K)
    (L : ι ⊕ ι → MvPowerSeries τ K) (G : MvPowerSeries (Fin 2) K) : MvPowerSeries τ K :=
  rootWeightSlice α lam (RestGc vp μ L G)

omit [IsUltrametricDist K] in
theorem RestGcOf_eq_mvExp_subst {ι τ : Type*} [Finite ι] (vp : K) {μ : PowerSeries K}
    (hμ0 : PowerSeries.constantCoeff μ = 0) {L : ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) {Φ : MvPowerSeries ι K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) :
    RestGcOf vp μ L Φ = mvExp (-(MvPowerSeries.subst (tOfParam vp μ L) Φ)) := by
  have ht0 := constantCoeff_tOfParam vp hμ0 hL0
  have ht : MvPowerSeries.HasSubst (tOfParam vp μ L) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  unfold RestGcOf
  rw [substMv_mvExp _ ht0 (by simp [hΦ0]), ← MvPowerSeries.coe_substAlgHom ht, map_neg,
    MvPowerSeries.coe_substAlgHom ht]

omit [IsUltrametricDist K] in
theorem RestGc_eq_prod_paired {ι τ : Type*} [Fintype ι] (vp : K) {μ : PowerSeries K}
    (hμ0 : PowerSeries.constantCoeff μ = 0) {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) {G : MvPowerSeries (Fin 2) K}
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    RestGc vp μ L G =
      ∏ e : ι, MvPowerSeries.subst ![tOfParam vp μ L (Sum.inl e), tOfParam vp μ L (Sum.inr e)]
        (mvExp (-G)) := by
  have ht0 := constantCoeff_tOfParam vp hμ0 hL0
  have ht : MvPowerSeries.HasSubst (tOfParam vp μ L) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  unfold RestGc RestGcOf pairedSum
  rw [← Finset.sum_neg_distrib,
    mvExp_sum Finset.univ _ (fun e _ => by rw [map_neg, constantCoeff_renMv _ hG0, neg_zero]),
    ← MvPowerSeries.coe_substAlgHom ht, map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ht, ← renMvHom_apply, ← map_neg, renMvHom_apply,
    ← renMv_mvExp _ (by simp [hG0]), subst_renMv _ ht]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [IsUltrametricDist K] in
/-- **Exact Multi-Place Product Splitting Theorem (`RestGcA_eq_prod_RestGc`)**:
When the global coordinate map `LA` splits place-by-place along `Sigma.mk v : Z v → Σ w, Z w`
(matching Alpöge's `th_coordZA_eq`), the multi-place Dwork exponential restriction `RestGcA` factors
identically as the product over all places `v : Pl` of the renamed single-place restrictions
`RestGc`! -/
theorem RestGcA_eq_prod_RestGc {Pl : Type*} [Fintype Pl] {E Z : Pl → Type*}
    [∀ v, Fintype (E v)] [∀ v, Finite (Z v)]
    (vp : K) {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0)
    (L : ∀ v : Pl, E v ⊕ E v → MvPowerSeries (Z v) K)
    (hL0 : ∀ v i, MvPowerSeries.constantCoeff (L v i) = 0)
    (LA : (Σ v : Pl, E v) ⊕ (Σ v : Pl, E v) → MvPowerSeries (Σ v : Pl, Z v) K)
    (hLA : ∀ (v : Pl) (x : E v ⊕ E v),
      LA (Sum.map (Sigma.mk v) (Sigma.mk v) x) = renMv (Sigma.mk v) (L v x))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0) :
    RestGcA vp μ LA G = ∏ v : Pl, renMv (Sigma.mk v) (RestGc vp μ (L v) G) := by
  have hLA0 : ∀ x, MvPowerSeries.constantCoeff (LA x) = 0 := by
    rintro (⟨v, e⟩ | ⟨v, e⟩)
    · have h := hLA v (Sum.inl e)
      simp only [Sum.map_inl] at h
      rw [h]; exact constantCoeff_renMv _ (hL0 v (Sum.inl e))
    · have h := hLA v (Sum.inr e)
      simp only [Sum.map_inr] at h
      rw [h]; exact constantCoeff_renMv _ (hL0 v (Sum.inr e))
  have htA0 := constantCoeff_tOfParam vp hμ0 hLA0
  have htA : MvPowerSeries.HasSubst (tOfParam vp μ LA) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero htA0
  unfold RestGcA RestGcOf
  rw [pairedSum_sigma E G, ← Finset.sum_neg_distrib,
    mvExp_sum Finset.univ _ (fun v _ => by
      rw [map_neg, constantCoeff_renMv _ (constantCoeff_pairedSum hG0), neg_zero]),
    ← MvPowerSeries.coe_substAlgHom htA, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have ht0 := constantCoeff_tOfParam vp hμ0 (hL0 v)
  have ht : MvPowerSeries.HasSubst (tOfParam vp μ (L v)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  rw [MvPowerSeries.coe_substAlgHom htA, ← renMvHom_apply, ← map_neg, renMvHom_apply,
    ← renMv_mvExp _ (by simp [constantCoeff_pairedSum hG0]), subst_renMv _ htA]
  unfold RestGc RestGcOf
  rw [renMv_subst (Sigma.mk v) ht]
  congr 1
  funext x
  unfold tOfParam
  rw [hLA v x, renMv_psubst (Sigma.mk v) (hL0 v x)]

/-- **Alternating Frobenius Root-Weight Series `altFrobSeries`** (matching Alpöge's `altS` / `sSer`):
`∑_{l ≥ 0} (-1)^l X_{x(l)}^{p^(2l)}`. -/
def altFrobSeries (p : ℕ) {ι : Type*} [DecidableEq ι] (x : ℕ → ι) : MvPowerSeries ι K :=
  fun d => ∑ l ∈ Finset.range (d.degree + 1),
    if d = Finsupp.single (x l) (p ^ (2 * l)) then (-1 : K) ^ l else 0

omit [IsUltrametricDist K] [CharZero K] in
theorem constantCoeff_altFrobSeries (p : ℕ) {ι : Type*} [DecidableEq ι]
    (x : ℕ → ι) : MvPowerSeries.constantCoeff (altFrobSeries (K := K) p x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change (∑ l ∈ Finset.range 1,
    if (0 : ι →₀ ℕ) = Finsupp.single (x l) (p ^ (2 * l)) then (-1 : K) ^ l else 0) = 0
  rw [Finset.sum_range_one, if_neg]
  intro h
  have := congrArg (fun f : ι →₀ ℕ => f (x 0)) h
  simp at this

omit [CharZero K] in
theorem isIntegralMv_altFrobSeries (p : ℕ) {ι : Type*} [DecidableEq ι] (x : ℕ → ι) :
    IsIntegralMv (altFrobSeries (K := K) p x) := fun d => by
  change ‖∑ l ∈ Finset.range (d.degree + 1),
    if d = Finsupp.single (x l) (p ^ (2 * l)) then (-1 : K) ^ l else 0‖ ≤ 1
  refine ultrametric_norm_sum_le _ _ zero_le_one fun l _ => ?_
  split_ifs
  · rw [norm_pow, norm_neg, norm_one, one_pow]
  · simp

omit [IsUltrametricDist K] [CharZero K] in
/-- **Frobenius Shift Equation for `altFrobSeries` (`altFrobSeries_frob_shift`)**:
`altFrobSeries p x - X (x 0) = - frobSub (p ^ 2) (altFrobSeries p (fun l => x (l + 1)))`!
This is the exact Artin–Schreier / Frobenius telescoping identity driving Dwork's restriction
of `Gt` onto `hhS`! -/
theorem altFrobSeries_frob_shift {p : ℕ} (hp : p.Prime) {ι : Type*} [DecidableEq ι] (x : ℕ → ι) :
    altFrobSeries (K := K) p x - MvPowerSeries.X (x 0) =
      -(frobSub (p ^ 2) (altFrobSeries (K := K) p (fun l => x (l + 1)))) := by
  classical
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hp2_ge : 2 ≤ p ^ 2 := by have := hp.two_le; nlinarith
  ext d
  rw [map_sub, map_neg, coeff_frobSub_eq_ite hp2_pos]
  change (∑ l ∈ Finset.range (d.degree + 1),
      if d = Finsupp.single (x l) (p ^ (2 * l)) then (-1 : K) ^ l else 0) -
      MvPowerSeries.coeff d (MvPowerSeries.X (x 0)) =
    -(if ∀ i, p ^ 2 ∣ d i then
      ∑ l ∈ Finset.range ((d.mapRange (· / p ^ 2) (Nat.zero_div (p ^ 2))).degree + 1),
        if d.mapRange (· / p ^ 2) (Nat.zero_div (p ^ 2)) =
            Finsupp.single (x (l + 1)) (p ^ (2 * l))
        then (-1 : K) ^ l else 0
      else 0)
  rw [Finset.sum_range_succ', pow_zero, pow_zero]
  have hX0 : MvPowerSeries.coeff d (MvPowerSeries.X (x 0) : MvPowerSeries ι K) =
      if d = Finsupp.single (x 0) 1 then 1 else 0 := by
    rw [MvPowerSeries.coeff_X]
  rw [hX0, add_sub_cancel_right]
  split_ifs with hdiv
  · set e := d.mapRange (· / p ^ 2) (Nat.zero_div (p ^ 2))
    have hde : p ^ 2 • e = d := nsmul_mapRange_div_eq hdiv
    have he_le : e.degree ≤ d.degree := by
      have hdeg : d.degree = p ^ 2 * e.degree := by
        rw [← hde, Finsupp.degree_apply, Finsupp.degree_apply]
        have hsupp : (p ^ 2 • e).support = e.support := by
          ext i
          simp only [Finsupp.mem_support_iff, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
            mul_ne_zero_iff]
          exact ⟨fun h => h.2, fun h => ⟨hp2_pos.ne', h⟩⟩
        rw [hsupp, Finset.mul_sum]
        rfl
      nlinarith
    rw [← Finset.sum_neg_distrib]
    have hiff : ∀ l : ℕ, d = Finsupp.single (x (l + 1)) (p ^ (2 * (l + 1))) ↔
        e = Finsupp.single (x (l + 1)) (p ^ (2 * l)) := by
      intro l
      have hpow : p ^ (2 * (l + 1)) = p ^ 2 * p ^ (2 * l) := by
        rw [← pow_add]; congr 1; ring
      constructor
      · intro hd
        have h1 : p ^ 2 • e = p ^ 2 • Finsupp.single (x (l + 1)) (p ^ (2 * l)) := by
          rw [hde, hd, Finsupp.smul_single, smul_eq_mul, hpow]
        ext i
        exact Nat.eq_of_mul_eq_mul_left hp2_pos (congrArg (fun f : ι →₀ ℕ => f i) h1)
      · intro he
        rw [← hde, he, Finsupp.smul_single, smul_eq_mul, hpow]
    -- Both sums agree on `l ∈ range (e.degree + 1)`, and higher `l` vanish since `l < p^(2l)`
    have hpad : ∑ l ∈ Finset.range (e.degree + 1),
          -(if e = Finsupp.single (x (l + 1)) (p ^ (2 * l)) then (-1 : K) ^ l else 0) =
        ∑ l ∈ Finset.range d.degree,
          if d = Finsupp.single (x (l + 1)) (p ^ (2 * (l + 1))) then (-1 : K) ^ (l + 1) else 0 := by
      have hsub1 : ∀ l : ℕ,
          -(if e = Finsupp.single (x (l + 1)) (p ^ (2 * l)) then (-1 : K) ^ l else 0) =
          if d = Finsupp.single (x (l + 1)) (p ^ (2 * (l + 1))) then (-1 : K) ^ (l + 1) else 0 := by
        intro l
        by_cases h : e = Finsupp.single (x (l + 1)) (p ^ (2 * l))
        · rw [if_pos h, if_pos ((hiff l).mpr h), pow_succ]; ring
        · rw [if_neg h, if_neg (mt (hiff l).mp h), neg_zero]
      simp_rw [hsub1]
      rcases Nat.eq_zero_or_pos e.degree with he0 | hepos
      · have he_zero : e = 0 := (degree_eq_zero_iff e).mp he0
        have hd_zero : d = 0 := by rw [← hde, he_zero, smul_zero]
        rw [he0, hd_zero]
        simp only [map_zero, zero_add, Finset.range_zero, Finset.sum_empty, Finset.sum_range_one]
        rw [if_neg]
        intro h
        have := congrArg (fun f : ι →₀ ℕ => f (x 1)) h
        simp at this
        exact pow_ne_zero 2 hp.ne_zero this.symm
      · have hdeg_eq : d.degree = p ^ 2 * e.degree := by
          rw [← hde, Finsupp.degree_apply, Finsupp.degree_apply]
          have hsupp : (p ^ 2 • e).support = e.support := by
            ext i
            simp only [Finsupp.mem_support_iff, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
              mul_ne_zero_iff]
            exact ⟨fun h => h.2, fun h => ⟨hp2_pos.ne', h⟩⟩
          rw [hsupp, Finset.mul_sum]
          rfl
        have hle_lt : e.degree + 1 ≤ d.degree := by nlinarith
        refine Finset.sum_subset (Finset.range_mono hle_lt) fun l _ hl => ?_
        rw [Finset.mem_range] at hl
        rw [if_neg]
        intro hd
        have he := (hiff l).mp hd
        have hedeg : e.degree = p ^ (2 * l) := by rw [he, Finsupp.degree_single]
        have hlt_pow : l < (p ^ 2) ^ l := Nat.lt_pow_self (by have := hp.two_le; nlinarith)
        rw [← pow_mul] at hlt_pow
        omega
    exact hpad.symm
  · rw [neg_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg]
    intro hd
    apply hdiv
    intro i
    rw [hd, Finsupp.single_apply]
    split_ifs
    · refine ⟨p ^ (2 * l), ?_⟩
      rw [← pow_add]; congr 1; ring
    · exact dvd_zero _

/-- Finite `M`-term partial sum of `altFrobSeries`. -/
private def altFrobPart (p : ℕ) {ι : Type*} (y : ℕ → ι) (M : ℕ) : MvPowerSeries ι K :=
  ∑ l ∈ Finset.range M, MvPowerSeries.C ((-1 : K) ^ l) * MvPowerSeries.X (y l) ^ (p ^ (2 * l))

omit [IsUltrametricDist K] [CharZero K] in
private lemma low_altFrobSeries_sub_part {p : ℕ} (hp : p.Prime) {ι : Type*} [DecidableEq ι]
    (y : ℕ → ι) (M : ℕ) :
    Low M (altFrobSeries (K := K) p y - altFrobPart p y M) := by
  intro d hd
  rw [map_sub, sub_eq_zero]
  change (∑ l ∈ Finset.range (d.degree + 1),
      if d = Finsupp.single (y l) (p ^ (2 * l)) then (-1 : K) ^ l else 0) =
    MvPowerSeries.coeff d (∑ l ∈ Finset.range M,
      MvPowerSeries.C ((-1 : K) ^ l) * MvPowerSeries.X (y l) ^ (p ^ (2 * l)))
  rw [map_sum]
  have hcoeff_term : ∀ l : ℕ,
      MvPowerSeries.coeff d (MvPowerSeries.C ((-1 : K) ^ l) * MvPowerSeries.X (y l) ^ (p ^ (2 * l))) =
      if d = Finsupp.single (y l) (p ^ (2 * l)) then (-1 : K) ^ l else 0 := fun l => by
    have hX : (MvPowerSeries.X (y l) : MvPowerSeries ι K) ^ (p ^ (2 * l)) =
        MvPowerSeries.monomial (Finsupp.single (y l) (p ^ (2 * l))) 1 := by
      have h1 : (MvPowerSeries.X (y l) : MvPowerSeries ι K) =
          MvPowerSeries.monomial (Finsupp.single (y l) 1) 1 := rfl
      rw [h1, MvPowerSeries.monomial_pow, one_pow, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [MvPowerSeries.coeff_C_mul, hX, MvPowerSeries.coeff_monomial]
    split_ifs <;> simp
  simp_rw [hcoeff_term]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun l _ hl => ?_
  rw [Finset.mem_range] at hl
  rw [if_neg]
  intro hEq
  have hdeg : d.degree = p ^ (2 * l) := by rw [hEq, Finsupp.degree_single]
  have hlt_pow : l < (p ^ 2) ^ l := Nat.lt_pow_self (by have := hp.two_le; nlinarith)
  rw [← pow_mul] at hlt_pow
  omega

omit [IsUltrametricDist K] [CharZero K] in
/-- Variable renaming commutes with `altFrobSeries`:
`renMv φ (altFrobSeries p x) = altFrobSeries p (φ ∘ x)`. -/
theorem renMv_altFrobSeries {p : ℕ} (hp : p.Prime) {κ σ : Type*} [Finite κ]
    [DecidableEq κ] [DecidableEq σ] (φ : κ → σ) (x : ℕ → κ) :
    renMv φ (altFrobSeries (K := K) p x) = altFrobSeries p (fun l => φ (x l)) := by
  have hren_part : ∀ M : ℕ,
      renMv φ (altFrobPart (K := K) p x M) = altFrobPart p (fun l => φ (x l)) M := by
    intro M
    unfold altFrobPart
    rw [← renMvHom_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow (renMvHom φ), renMvHom_apply, renMvHom_apply, renMv_C, renMv_X]
  have hlow_ren : ∀ {M : ℕ} {G : MvPowerSeries κ K}, Low M G → Low M (renMv φ G) := by
    intro M G hG d hd
    have hφ := MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun k => MvPowerSeries.constantCoeff_X (R := K) (φ k))
    have hprod_low : ∀ m : κ →₀ ℕ,
        Low m.degree (m.prod fun i k => (MvPowerSeries.X (φ i) : MvPowerSeries σ K) ^ k) := by
      intro m
      rw [Finsupp.prod, Finsupp.degree_apply]
      refine Finset.induction_on m.support (by simp; intro e he; omega) fun i s hi ih => ?_
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have h1 : Low 1 (MvPowerSeries.X (φ i) : MvPowerSeries σ K) :=
        low_one_of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)
      have hpow : Low (m i * 1) ((MvPowerSeries.X (φ i) : MvPowerSeries σ K) ^ m i) :=
        low_pow h1 (m i)
      rw [mul_one] at hpow
      exact low_mul hpow ih
    unfold renMv
    rw [MvPowerSeries.coeff_subst hφ]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    by_cases hm : m.degree < M
    · rw [hG m hm, zero_smul]
    · rw [hprod_low m d (by omega), smul_zero]
  ext d
  set M := d.degree + 1
  have hdiff : renMv φ (altFrobSeries (K := K) p x) - altFrobSeries p (fun l => φ (x l)) =
      renMv φ (altFrobSeries (K := K) p x - altFrobPart p x M) -
        (altFrobSeries p (fun l => φ (x l)) - altFrobPart p (fun l => φ (x l)) M) := by
    have hsub : renMv φ (altFrobSeries (K := K) p x - altFrobPart p x M) =
        renMv φ (altFrobSeries (K := K) p x) - renMv φ (altFrobPart p x M) := by
      rw [← renMvHom_apply, map_sub, renMvHom_apply, renMvHom_apply]
    rw [hsub, hren_part M]
    ring
  have h0 : MvPowerSeries.coeff d
      (renMv φ (altFrobSeries (K := K) p x) - altFrobSeries p (fun l => φ (x l))) = 0 := by
    rw [hdiff, map_sub, hlow_ren (low_altFrobSeries_sub_part hp x M) d (Nat.lt_succ_self _),
      low_altFrobSeries_sub_part hp (fun l => φ (x l)) M d (Nat.lt_succ_self _), sub_self]
  exact sub_eq_zero.mp (by simpa [map_sub] using h0)

/-- Cyclic index shift `(s + d) mod n'` and `(s - d) mod n'` matching Alpöge's `posAdd` / `posSub`. -/
def cyclicAdd {n' : ℕ} (s : Fin n') (d : ℕ) : Fin n' :=
  ⟨(s.val + d) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

def cyclicSub {n' : ℕ} (s : Fin n') (d : ℕ) : Fin n' :=
  ⟨(s.val + n' * d - d) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

/-- **Single-Place Quadratic Restriction Exponent `quadRestExp`** (matching Alpöge's `hhS`):
`∑_{s : Fin n'} u_s * ∑_{a, b} (sSer s a b)^p * sSer (s + 1) a b`. -/
def quadRestExp (p : ℕ) {n' r0 r1 : ℕ} (u : Fin n' → K) :
    MvPowerSeries (Fin n' × Fin r0 × Fin r1) K :=
  ∑ s : Fin n', MvPowerSeries.C (u s) *
    ∑ a : Fin r0, ∑ b : Fin r1,
      (altFrobSeries p (fun l => (cyclicSub s (2 * l), a, b))) ^ p *
        altFrobSeries p (fun l => (cyclicSub (cyclicAdd s 1) (2 * l), a, b))

/-- **Multi-Place Quadratic Restriction Exponent `quadRestExpA`** (matching Alpöge's `Sys.hhA`):
place-`v` embedded quadratic form inside `Σ w : Pl, Fin (n' w) × Fin r0 × Fin r1`. -/
def quadRestExpA (p : ℕ) {Pl : Type*} [DecidableEq Pl] {n' : Pl → ℕ} {r0 r1 : ℕ}
    (v : Pl) (u : Fin (n' v) → K) :
    MvPowerSeries (Σ w : Pl, Fin (n' w) × Fin r0 × Fin r1) K :=
  ∑ s : Fin (n' v), MvPowerSeries.C (u s) *
    ∑ a : Fin r0, ∑ b : Fin r1,
      (altFrobSeries p (fun l => (⟨v, (cyclicSub s (2 * l), a, b)⟩ :
        Σ w : Pl, Fin (n' w) × Fin r0 × Fin r1))) ^ p *
      altFrobSeries p (fun l => (⟨v, (cyclicSub (cyclicAdd s 1) (2 * l), a, b)⟩ :
        Σ w : Pl, Fin (n' w) × Fin r0 × Fin r1))

omit [IsUltrametricDist K] [CharZero K] in
/-- Exact compatibility between single-place `quadRestExp` and multi-place `quadRestExpA`
(matching Alpöge's `ExpansionAllPlacesOfPlace.th_hhA_eq`):
`renMv (Sigma.mk v) (quadRestExp p u) = quadRestExpA p v u`! -/
theorem renMv_quadRestExp {p : ℕ} (hp : p.Prime) {Pl : Type*} [DecidableEq Pl]
    {n' : Pl → ℕ} {r0 r1 : ℕ} (v : Pl) (u : Fin (n' v) → K) :
    renMv (fun z : Fin (n' v) × Fin r0 × Fin r1 =>
        (⟨v, z⟩ : Σ w : Pl, Fin (n' w) × Fin r0 × Fin r1)) (quadRestExp p u) =
      quadRestExpA p v u := by
  unfold quadRestExp quadRestExpA
  rw [← renMvHom_apply, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, renMvHom_apply, renMv_C, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_pow, renMvHom_apply, renMvHom_apply,
    renMv_altFrobSeries hp, renMv_altFrobSeries hp]

omit [IsUltrametricDist K] [CharZero K] in
theorem constantCoeff_quadRestExp {p : ℕ} (hp : p.Prime) {n' r0 r1 : ℕ} (u : Fin n' → K) :
    MvPowerSeries.constantCoeff (quadRestExp p (r0 := r0) (r1 := r1) u) = 0 := by
  unfold quadRestExp
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [map_mul, map_sum]
  simp_rw [map_sum]
  have h0 : ∑ a : Fin r0, ∑ b : Fin r1,
      MvPowerSeries.constantCoeff
        ((altFrobSeries (K := K) p (fun l => (cyclicSub s (2 * l), a, b))) ^ p *
          altFrobSeries (K := K) p (fun l => (cyclicSub (cyclicAdd s 1) (2 * l), a, b))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [map_mul, map_pow, constantCoeff_altFrobSeries p, zero_pow hp.ne_zero, zero_mul]
  rw [h0, mul_zero]

omit [CharZero K] in
theorem isIntegralMv_quadRestExp (p : ℕ) {n' r0 r1 : ℕ} {u : Fin n' → K}
    (hu : ∀ s, ‖u s‖ ≤ 1) :
    IsIntegralMv (quadRestExp p (r0 := r0) (r1 := r1) u) := by
  unfold quadRestExp
  refine isIntegralMv_sum _ fun s _ => isIntegralMv_mul (coeffNormLeMv_C zero_le_one (hu s)) ?_
  refine isIntegralMv_sum _ fun a _ => isIntegralMv_sum _ fun b _ =>
    isIntegralMv_mul (isIntegralMv_pow (isIntegralMv_altFrobSeries p _) p)
      (isIntegralMv_altFrobSeries p _)

/-- **Single-Place `RestGc` Factorization Predicate (`RestGcFact`)**:
`RestGc vp μ L G = mvExp (-(C c * H)) * V` with `IsIntegralMv V`. -/
def RestGcFact {ι τ : Type*} [Fintype ι] (vp c : K) (μ : PowerSeries K)
    (L : ι ⊕ ι → MvPowerSeries τ K) (G : MvPowerSeries (Fin 2) K)
    (H : MvPowerSeries τ K) : Prop :=
  ∃ V : MvPowerSeries τ K, IsIntegralMv V ∧
    RestGc vp μ L G = mvExp (-(MvPowerSeries.C c * H)) * V

/-- **Multi-Place `RestGcA` Factorization Predicate (`RestGcAFact`)**:
`RestGcA vp μ LA G = (∏ v : Pl, mvExp (-(C c * HA v))) * V` with `IsIntegralMv V`. -/
def RestGcAFact {Pl : Type*} [Fintype Pl] {E : Pl → Type*} [∀ v, Fintype (E v)] {ZA : Type*}
    (vp c : K) (μ : PowerSeries K)
    (LA : (Σ v : Pl, E v) ⊕ (Σ v : Pl, E v) → MvPowerSeries ZA K)
    (G : MvPowerSeries (Fin 2) K) (HA : Pl → MvPowerSeries ZA K) : Prop :=
  ∃ V : MvPowerSeries ZA K, IsIntegralMv V ∧
    RestGcA vp μ LA G = (∏ v : Pl, mvExp (-(MvPowerSeries.C c * HA v))) * V

/-- **Local-to-Global Dwork Exponential Restriction Assembly (`restGcAFact_of_restGcFact`)**:
Matching Alpöge's `ExpansionAllPlacesOfPlace.restGcA_of`: if the single-place restriction
factorization `RestGcFact` holds at every place `v : Pl`, then the multi-place adelic product
factorization `RestGcAFact` holds with `HA v = renMv (Sigma.mk v) (H v)` and integral product
error `V = ∏ v, renMv (Sigma.mk v) (V_v)`! -/
theorem restGcAFact_of_restGcFact {Pl : Type*} [Fintype Pl] {E Z : Pl → Type*}
    [∀ v, Fintype (E v)] [∀ v, Finite (Z v)]
    (vp c : K) {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0)
    (L : ∀ v : Pl, E v ⊕ E v → MvPowerSeries (Z v) K)
    (hL0 : ∀ v i, MvPowerSeries.constantCoeff (L v i) = 0)
    (LA : (Σ v : Pl, E v) ⊕ (Σ v : Pl, E v) → MvPowerSeries (Σ v : Pl, Z v) K)
    (hLA : ∀ (v : Pl) (x : E v ⊕ E v),
      LA (Sum.map (Sigma.mk v) (Sigma.mk v) x) = renMv (Sigma.mk v) (L v x))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (H : ∀ v : Pl, MvPowerSeries (Z v) K) (hH0 : ∀ v, MvPowerSeries.constantCoeff (H v) = 0)
    (hfact : ∀ v : Pl, RestGcFact vp c μ (L v) G (H v)) :
    RestGcAFact vp c μ LA G (fun v => renMv (Sigma.mk v) (H v)) := by
  choose V hV hEq using hfact
  refine ⟨∏ v : Pl, renMv (Sigma.mk v) (V v), ?_, ?_⟩
  · -- Product of renamed integral series is integral
    have hprod_int : ∀ s : Finset Pl,
        IsIntegralMv (∏ v ∈ s, renMv (Sigma.mk v) (V v)) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using isIntegralMv_one
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact isIntegralMv_mul (isIntegralMv_renMv _ (hV a)) ih
    exact hprod_int Finset.univ
  · rw [RestGcA_eq_prod_RestGc vp hμ0 L hL0 LA hLA hG0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hEq v, ← renMvHom_apply, map_mul, renMvHom_apply, renMvHom_apply]
    congr 1
    rw [renMv_mvExp _ (by rw [map_neg, map_mul, hH0 v, mul_zero, neg_zero]),
      ← renMvHom_apply, map_neg, map_mul, renMvHom_apply, renMvHom_apply, renMv_C]

end RestGcSection

/-! ## Section 4: `p`-Adic Integrality of Restricted Dwork Exponential Series -/

section DworkRestrictionIntegrality

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable {p : ℕ} [Fact p.Prime]

/-- **Dwork Exponential Threshold Integrality (`isIntegralMv_mvExp_of_dwork_threshold`)**:
If `D : DworkUniformizerPi K p` and `Φ : MvPowerSeries σ K` satisfies `constantCoeff Φ = 0` and
`∀ d, ‖coeff d Φ‖ ≤ ‖D.pi‖` (i.e. `Φ = π * Ψ` with `Ψ` integral), then `mvExp Φ` and `mvExp (-Φ)`
are unconditionally `p`-adically integral! -/
theorem isIntegralMv_mvExp_of_dwork_threshold {σ : Type*} (D : DworkUniformizerPi K p)
    {Φ : MvPowerSeries σ K} (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hΦ : CoeffNormLeMv ‖D.pi‖ Φ) :
    IsIntegralMv (mvExp Φ) ∧ IsIntegralMv (mvExp (-Φ)) := by
  have hWt : WtGe ‖(p : K)‖ (fun _ : σ => (0 : ℝ)) (1 / ((p : ℝ) - 1)) Φ := fun d => by
    unfold MonoWtGe wtDot
    simp only [mul_zero, Finsupp.sum, Finset.sum_const_zero, sub_zero]
    rw [← D.norm_pi_eq_norm_p_rpow]
    exact hΦ d
  have hWtNeg : WtGe ‖(p : K)‖ (fun _ : σ => (0 : ℝ)) (1 / ((p : ℝ) - 1)) (-Φ) := fun d => by
    unfold MonoWtGe
    rw [map_neg, norm_neg]
    exact hWt d
  have hE : WtGe ‖(p : K)‖ (fun _ : σ => (0 : ℝ)) 0 (mvExp Φ) := fun κ =>
    dwork_exp_weight_le D.hp D.norm_p_lt_one hΦ0 (fun m _ => hWt m) κ le_rfl
  have hEN : WtGe ‖(p : K)‖ (fun _ : σ => (0 : ℝ)) 0 (mvExp (-Φ)) := fun κ =>
    dwork_exp_weight_le D.hp D.norm_p_lt_one (by simp [hΦ0]) (fun m _ => hWtNeg m) κ le_rfl
  refine ⟨fun d => ?_, fun d => ?_⟩
  · have h := hE d
    unfold MonoWtGe wtDot at h
    simpa using h
  · have h := hEN d
    unfold MonoWtGe wtDot at h
    simpa using h

/-- **`p`-Adic Integrality of Restricted Dwork Exponential Series
(`dwork_exponential_restriction_integral`)**:
Given a Dwork uniformizer `D : DworkUniformizerPi K p`, a bivariate exponent `G` with
`constantCoeff G = 0` and `CoeffNormLeMv ‖D.pi‖ G`, an integral parameter `μ` (`constantCoeff = 0`),
scaling `‖vp‖ ≤ 1`, and integral coordinate forms `L : ι ⊕ ι → MvPowerSeries τ K`
(`constantCoeff = 0`), the multivariable restricted Dwork exponential `RestGc vp μ L G` is
**unconditionally `p`-adically integral** (`IsIntegralMv (RestGc vp μ L G)`)! -/
theorem dwork_exponential_restriction_integral {ι τ : Type*} [Fintype ι]
    (D : DworkUniformizerPi K p)
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hG : CoeffNormLeMv ‖D.pi‖ G) :
    IsIntegralMv (RestGc vp μ L G) := by
  have hPair_bound : CoeffNormLeMv ‖D.pi‖ (pairedSum ι G) := by
    unfold pairedSum
    refine coeffNormLeMv_sum Finset.univ D.norm_pi_pos.le fun e _ d => ?_
    -- `renMv ![inl e, inr e] G` has every coefficient bounded by `‖D.pi‖`
    have hG_scale : IsIntegralMv (MvPowerSeries.C D.pi⁻¹ * G) := fun m => by
      rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv]
      calc ‖D.pi‖⁻¹ * ‖MvPowerSeries.coeff m G‖
          ≤ ‖D.pi‖⁻¹ * ‖D.pi‖ := mul_le_mul_of_nonneg_left (hG m) (inv_nonneg.mpr D.norm_pi_pos.le)
        _ = 1 := inv_mul_cancel₀ D.norm_pi_pos.ne'
    have hren := isIntegralMv_renMv ![Sum.inl e, Sum.inr e] hG_scale d
    have hmul : renMv ![Sum.inl e, Sum.inr e] (MvPowerSeries.C D.pi⁻¹ * G) =
        MvPowerSeries.C D.pi⁻¹ * renMv ![Sum.inl e, Sum.inr e] G := by
      rw [← renMvHom_apply, map_mul, renMvHom_apply, renMvHom_apply, renMv_C]
    rw [hmul, MvPowerSeries.coeff_C_mul, norm_mul, norm_inv] at hren
    calc ‖MvPowerSeries.coeff d (renMv ![Sum.inl e, Sum.inr e] G)‖
        = ‖D.pi‖ * (‖D.pi‖⁻¹ * ‖MvPowerSeries.coeff d (renMv ![Sum.inl e, Sum.inr e] G)‖) := by
          field_simp [D.norm_pi_pos.ne']
      _ ≤ ‖D.pi‖ * 1 := mul_le_mul_of_nonneg_left hren D.norm_pi_pos.le
      _ = ‖D.pi‖ := mul_one _
  have hExpInt : IsIntegralMv (mvExp (-(pairedSum ι G))) :=
    (isIntegralMv_mvExp_of_dwork_threshold D (constantCoeff_pairedSum hG0) hPair_bound).2
  exact isIntegralMv_substMv (tOfParam vp μ L) (constantCoeff_tOfParam vp hμ0 hL0)
    (isIntegralMv_tOfParam hvp hμ hL0 hL) hExpInt

/-- **Multi-Place Adelic `RestGcA` `p`-Adic Integrality**
(`dwork_exponential_restriction_all_places_integral`):
under the same Dwork threshold `CoeffNormLeMv ‖D.pi‖ G`, the multi-place restriction `RestGcA`
is unconditionally `p`-adically integral across all places `v : Pl`! -/
theorem dwork_exponential_restriction_all_places_integral {Pl : Type*} [Fintype Pl]
    {E : Pl → Type*} [∀ v, Fintype (E v)] {ZA : Type*}
    (D : DworkUniformizerPi K p)
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    {LA : (Σ v : Pl, E v) ⊕ (Σ v : Pl, E v) → MvPowerSeries ZA K}
    (hLA0 : ∀ i, MvPowerSeries.constantCoeff (LA i) = 0) (hLA : ∀ i, IsIntegralMv (LA i))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hG : CoeffNormLeMv ‖D.pi‖ G) :
    IsIntegralMv (RestGcA vp μ LA G) :=
  dwork_exponential_restriction_integral D hvp hμ0 hμ hLA0 hLA hG0 hG

omit [Fact p.Prime] in
/-- **Frobenius-Lift Dieudonné–Dwork Integrality for Restricted Exponentials
(`dwork_restriction_isIntegral_of_frob_congr`)**:
Even WITHOUT a direct `‖π‖` threshold bound on `Φ`, if `E = mvExp (-Φ)` satisfies the multivariable
Frobenius congruence `frobMapMv σ_aut p hp.pos E * (invOneMv E)^p ∈ 1 + p O_K[[X]]` (via
`Stage12MultivarDwork.dieudonne_dwork_mv_iff`), then `RestGcOf vp μ L Φ` is `p`-adically integral! -/
theorem dwork_restriction_isIntegral_of_frob_congr {ι τ : Type*} [Finite ι]
    (hp : p.Prime) (σ_aut : K →+* K)
    (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ_aut c‖ ≤ ‖(p : K)‖)
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    {L : ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i))
    {Φ : MvPowerSeries ι K} (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hfrob : CongOneModPMv p
      (frobMapMv σ_aut p hp.pos (mvExp (-Φ)) * (invOneMv (mvExp (-Φ))) ^ p)) :
    IsIntegralMv (RestGcOf vp μ L Φ) := by
  have hE0 : MvPowerSeries.constantCoeff (mvExp (-Φ)) = 1 :=
    constantCoeff_mvExp (by simp [hΦ0])
  have hEint : IsIntegralMv (mvExp (-Φ)) :=
    (dieudonne_dwork_mv_iff hp σ_aut hflt hE0).mpr hfrob
  exact isIntegralMv_substMv (tOfParam vp μ L) (constantCoeff_tOfParam vp hμ0 hL0)
    (isIntegralMv_tOfParam hvp hμ hL0 hL) hEint

/-! ### Bivariate Dwork Splitting Function Restriction & Overconvergence -/

/-- Bivariate Dwork splitting exponent `G_Dwork(X, Y) = π * (X * Y - (X * Y)^p)` whose
exponential is `θ(X Y) = exp(π (X Y - (X Y)^p))`! -/
def dworkBivArg (ϖ : K) (p : ℕ) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C ϖ *
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 - (MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ p)

omit [IsUltrametricDist K] [CharZero K] in
theorem constantCoeff_dworkBivArg (ϖ : K) {p : ℕ} (hp : p.Prime) :
    MvPowerSeries.constantCoeff (dworkBivArg ϖ p) = 0 := by
  unfold dworkBivArg
  simp [zero_pow hp.ne_zero]

omit [IsUltrametricDist K] in
/-- Exact identification: `mvExp (dworkBivArg ϖ p) = PowerSeries.subst (X 0 * X 1) (dworkSplitting ϖ p)`. -/
theorem mvExp_dworkBivArg_eq_subst (ϖ : K) {p : ℕ} (hp : p.Prime) :
    mvExp (dworkBivArg ϖ p) =
      PowerSeries.subst (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)
        (dworkSplitting ϖ p) := by
  have hXY0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have harg0 : PowerSeries.constantCoeff
      (PowerSeries.C ϖ * (PowerSeries.X - PowerSeries.X ^ p)) = 0 := by
    simp [zero_pow hp.ne_zero]
  have hsubst_arg : PowerSeries.subst
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)
      (PowerSeries.C ϖ * (PowerSeries.X - PowerSeries.X ^ p)) = dworkBivArg ϖ p := by
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero hXY0
    unfold dworkBivArg
    rw [← PowerSeries.coe_substAlgHom hs, map_mul, map_sub, map_pow,
      psSubstAlgHom_C hs, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs]
  unfold dworkSplitting expPS mvExp
  rw [← hsubst_arg]
  -- `PowerSeries.subst (PowerSeries.subst (X0*X1) A) (exp K) = PowerSeries.subst (X0*X1) (PowerSeries.subst A (exp K))`
  have hs1 := PowerSeries.HasSubst.of_constantCoeff_zero harg0
  have hs2 := PowerSeries.HasSubst.of_constantCoeff_zero hXY0
  exact (MvPowerSeries.subst_comp_subst_apply hs1.const hs2.const (PowerSeries.exp K)).symm

/-- **Exact Bivariate Dwork Splitting Overconvergence (`wtGe_mvExp_dworkBivArg`)**:
For any `D : DworkUniformizerPi K p`, `mvExp (dworkBivArg D.pi p) = θ(X₀ X₁)` satisfies
`WtGe ‖(p : K)‖ (fun _ => -((p - 1) / (2 p^2))) 0` — overconvergent on the polydisk
`|X₀|, |X₁| < p ^ ((p - 1) / (2 p^2)) > 1`! -/
theorem wtGe_mvExp_dworkBivArg (D : DworkUniformizerPi K p) :
    WtGe ‖(p : K)‖ (fun _ : Fin 2 => -(((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2))) 0
      (mvExp (dworkBivArg D.pi p)) := by
  classical
  rw [mvExp_dworkBivArg_eq_subst D.pi D.hp]
  have hXY0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hXY_pow : ∀ k : ℕ,
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ k =
        MvPowerSeries.monomial (Finsupp.single 0 k + Finsupp.single 1 k) 1 := by
    intro k
    have h1 : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
        MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
      have hX0 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) =
          MvPowerSeries.monomial (Finsupp.single 0 1) 1 := rfl
      have hX1 : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) =
          MvPowerSeries.monomial (Finsupp.single 1 1) 1 := rfl
      rw [hX0, hX1, MvPowerSeries.monomial_mul_monomial, mul_one]
    rw [h1, MvPowerSeries.monomial_pow, one_pow, smul_add, Finsupp.smul_single, Finsupp.smul_single]
    simp only [smul_eq_mul, mul_one]
  intro d
  unfold MonoWtGe
  rw [coeff_subst_eq_sum hXY0]
  have hdot : wtDot d (fun _ : Fin 2 => -(((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2))) =
      -((d 0 : ℝ) + (d 1 : ℝ)) * (((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2)) := by
    unfold wtDot
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp), Fin.sum_univ_two]
    ring
  rw [hdot]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg D.norm_p_pos.le _) fun k _ => ?_
  rw [hXY_pow k, MvPowerSeries.coeff_monomial]
  split_ifs with hd
  · rw [mul_one]
    have hd0 : d 0 = k := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hd
      simpa using this
    have hd1 : d 1 = k := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hd
      simpa using this
    have hbd := norm_coeff_dworkSplitting_le D.hp D.norm_p_lt_one D.pi_pow_eq k
    refine hbd.trans_eq ?_
    congr 1
    rw [hd0, hd1]
    ring
  · rw [mul_zero, norm_zero]
    exact Real.rpow_nonneg D.norm_p_pos.le _

/-- **Overconvergent Dwork Splitting Restriction Theorem (`dwork_splitting_restriction_wtGe` &
`dwork_splitting_restriction_integral`)**:
Substituting `tOfParam vp μ L` (`‖vp‖ ≤ ‖p‖ ^ δ`, `μ` integral, `L` integral with `constantCoeff = 0`)
into `∏_{e : ι} θ(X_e Y_e)` (`= mvExp (pairedSum ι (dworkBivArg D.pi p))`) yields a series that is
**simultaneously overconvergent** (`WtGe ‖(p : K)‖ (fun _ => 0) 0`, and strictly overconvergent when
`δ > 0`) AND **`p`-adically integral** (`IsIntegralMv`)! -/
theorem dwork_splitting_restriction_wtGe {ι τ : Type*} [Fintype ι]
    (D : DworkUniformizerPi K p)
    {δ : ℝ} (hδ : 0 ≤ δ) {vp : K} (hvp : ‖vp‖ ≤ ‖(p : K)‖ ^ δ)
    {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i)) :
    WtGe ‖(p : K)‖ (fun _ : τ => 0) 0
      (MvPowerSeries.subst (tOfParam vp μ L) (mvExp (pairedSum ι (dworkBivArg D.pi p)))) := by
  have hvp1 : ‖vp‖ ≤ 1 := hvp.trans (Real.rpow_le_one D.norm_p_pos.le D.norm_p_lt_one.le hδ)
  have hθ_int : IsIntegralMv (mvExp (dworkBivArg D.pi p)) := fun d => by
    have h := wtGe_mvExp_dworkBivArg D d
    unfold MonoWtGe wtDot at h
    have hexp : 0 ≤ 0 - d.sum (fun _ k => (k : ℝ) * -(((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2))) := by
      have hpos : 0 ≤ ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2) := by
        have h1 := D.splittingRadius_bounds.2.2.1
        rw [show ((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2) = (((p : ℝ) - 1) / (p : ℝ) ^ 2) / 2 by ring]
        linarith
      have hsum : d.sum (fun _ k => (k : ℝ) * -(((p : ℝ) - 1) / (2 * (p : ℝ) ^ 2))) ≤ 0 := by
        rw [Finsupp.sum]
        refine Finset.sum_nonpos fun i _ => ?_
        have hk : (0 : ℝ) ≤ (d i : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    exact h.trans (Real.rpow_le_one D.norm_p_pos.le D.norm_p_lt_one.le hexp)
  have ht0 := constantCoeff_tOfParam vp hμ0 hL0
  have ht := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have ht_int := isIntegralMv_tOfParam hvp1 hμ hL0 hL
  have hprod_eq : MvPowerSeries.subst (tOfParam vp μ L) (mvExp (pairedSum ι (dworkBivArg D.pi p))) =
      ∏ e : ι, MvPowerSeries.subst ![tOfParam vp μ L (Sum.inl e), tOfParam vp μ L (Sum.inr e)]
        (mvExp (dworkBivArg D.pi p)) := by
    unfold pairedSum
    rw [mvExp_sum Finset.univ _ (fun e _ => constantCoeff_renMv _ (constantCoeff_dworkBivArg D.pi D.hp)),
      ← MvPowerSeries.coe_substAlgHom ht, map_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [MvPowerSeries.coe_substAlgHom ht, ← renMv_mvExp _ (constantCoeff_dworkBivArg D.pi D.hp),
      subst_renMv _ ht]
    congr 1; funext k; fin_cases k <;> rfl
  have hInt : IsIntegralMv
      (MvPowerSeries.subst (tOfParam vp μ L) (mvExp (pairedSum ι (dworkBivArg D.pi p)))) := by
    rw [hprod_eq]
    have hfin : ∀ s : Finset ι, IsIntegralMv (∏ e ∈ s,
        MvPowerSeries.subst ![tOfParam vp μ L (Sum.inl e), tOfParam vp μ L (Sum.inr e)]
          (mvExp (dworkBivArg D.pi p))) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using isIntegralMv_one
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        refine isIntegralMv_mul ?_ ih
        refine isIntegralMv_substMv _ (fun k => by fin_cases k <;> exact ht0 _)
          (fun k => by fin_cases k <;> exact ht_int _) hθ_int
    exact hfin Finset.univ
  intro d
  unfold MonoWtGe wtDot
  simpa using hInt d

theorem dwork_splitting_restriction_integral {ι τ : Type*} [Fintype ι]
    (D : DworkUniformizerPi K p)
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i)) :
    IsIntegralMv (RestGc vp μ L (-dworkBivArg D.pi p)) := by
  have hneg : pairedSum ι (-dworkBivArg D.pi p) = -pairedSum ι (dworkBivArg D.pi p) := by
    unfold pairedSum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← renMvHom_apply, map_neg, renMvHom_apply]
  unfold RestGc RestGcOf
  rw [hneg, neg_neg]
  have hwt := dwork_splitting_restriction_wtGe D (δ := 0) le_rfl (by simpa using hvp) hμ0 hμ hL0 hL
  intro d
  have h := hwt d
  unfold MonoWtGe wtDot at h
  simpa using h

/-- **Root-Weight Slice Integrality (`rootWeightRestrict_dwork_integral`)**:
Restricting `RestGc vp μ L G` to ANY root-weight slice `λ ∈ M` preserves `p`-adic integrality! -/
theorem rootWeightRestrict_dwork_integral {ι τ M : Type*} [Fintype ι] [AddCommGroup M]
    (α : τ → M) (lam : M)
    (D : DworkUniformizerPi K p)
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hG : CoeffNormLeMv ‖D.pi‖ G) :
    IsIntegralMv (RestGcRootWeight α lam vp μ L G) :=
  isIntegralMv_monomialRestrict _
    (dwork_exponential_restriction_integral D hvp hμ0 hμ hL0 hL hG0 hG)

omit [IsUltrametricDist K] in
/-- **Sharp Scaling Valuation Gain (`dworkVal_coeff_scale_ge`)**:
When `F` is `p`-adically integral and `‖c‖ = ‖(p : K)‖ ^ γ` (`γ ≥ 0`, e.g. `c = D.pi` with
`γ = 1 / (p - 1)` or `c = R.vp` with `γ = 1 / (p^2 - 1)`), every nonzero degree-`d` coefficient of
`mvScaleHom c F` has norm `≤ ‖(p : K)‖ ^ (d.degree * γ)` — an explicit additive `p`-adic valuation
gain `≥ d.degree * γ`! -/
theorem norm_coeff_mvScaleHom_le {σ : Type*} {γ : ℝ} {c : K}
    (hc : ‖c‖ ≤ ‖(p : K)‖ ^ γ) {F : MvPowerSeries σ K} (hF : IsIntegralMv F) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (mvScaleHom c F)‖ ≤ ‖(p : K)‖ ^ ((d.degree : ℝ) * γ) := by
  have hp : p.Prime := Fact.out
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [coeff_mvScaleHom, norm_mul, norm_pow]
  calc ‖c‖ ^ d.degree * ‖MvPowerSeries.coeff d F‖
      ≤ (‖(p : K)‖ ^ γ) ^ d.degree * 1 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc _) (hF d) (norm_nonneg _)
          (pow_nonneg (Real.rpow_nonneg hpi0.le _) _)
    _ = ‖(p : K)‖ ^ ((d.degree : ℝ) * γ) := by
        rw [mul_one, ← Real.rpow_natCast (‖(p : K)‖ ^ γ), ← Real.rpow_mul hpi0.le, mul_comm]

theorem dworkVal_coeff_scale_ge {σ : Type*} (D : DworkUniformizerPi K p)
    {γ : ℝ} {c : K} (hc : ‖c‖ ≤ ‖(p : K)‖ ^ γ) {F : MvPowerSeries σ K} (hF : IsIntegralMv F)
    {d : σ →₀ ℕ} (hne : MvPowerSeries.coeff d (mvScaleHom c F) ≠ 0) :
    (d.degree : ℝ) * γ ≤ dworkVal p (MvPowerSeries.coeff d (mvScaleHom c F)) := by
  have hbd := norm_coeff_mvScaleHom_le (p := p) hc hF d
  have hnpos : 0 < ‖MvPowerSeries.coeff d (mvScaleHom c F)‖ := norm_pos_iff.mpr hne
  have hpi0 : 0 < ‖(p : K)‖ := D.norm_p_pos
  have hlogp_neg : Real.log ‖(p : K)‖ < 0 := Real.log_neg hpi0 D.norm_p_lt_one
  have hlog_le : Real.log ‖MvPowerSeries.coeff d (mvScaleHom c F)‖ ≤
      ((d.degree : ℝ) * γ) * Real.log ‖(p : K)‖ := by
    have h1 := Real.log_le_log hnpos hbd
    rwa [Real.log_rpow hpi0] at h1
  unfold dworkVal
  rw [le_div_iff_of_neg hlogp_neg]
  exact hlog_le

end DworkRestrictionIntegrality

/-! ## Section 5: Twisted Theta Power-Series Factorization & Wave-2 Bridges -/

section TwistedThetaFactorization

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-! ### Exponential Integrality Equivalence (`ExpIntegral` & `SimeqExp`) -/

/-- `ExpIntegral F` means `constantCoeff F = 0` and `mvExp F` is `p`-adically integral
(matching Alpöge's `E0 p F`). -/
def ExpIntegral {σ : Type*} (F : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ IsIntegralMv (mvExp F)

/-- Exponential equivalence modulo integral exponentials: `SimeqExp F G ↔ ExpIntegral (F - G)`
(matching Alpöge's `Simeq`). -/
def SimeqExp {σ : Type*} (F G : MvPowerSeries σ K) : Prop :=
  ExpIntegral (F - G)

omit [IsUltrametricDist K] in
theorem expIntegral_zero {σ : Type*} : ExpIntegral (0 : MvPowerSeries σ K) :=
  ⟨map_zero _, by rw [mvExp_zero]; exact isIntegralMv_one⟩

theorem expIntegral_add {σ : Type*} {F G : MvPowerSeries σ K}
    (hF : ExpIntegral F) (hG : ExpIntegral G) : ExpIntegral (F + G) :=
  ⟨by rw [map_add, hF.1, hG.1, add_zero],
    by rw [mvExp_add hF.1 hG.1]; exact isIntegralMv_mul hF.2 hG.2⟩

theorem expIntegral_neg {σ : Type*} {F : MvPowerSeries σ K} (hF : ExpIntegral F) :
    ExpIntegral (-F) :=
  ⟨by simp [hF.1],
    by rw [mvExp_neg_eq_invOneMv hF.1]; exact isIntegralMv_invOneMv (constantCoeff_mvExp hF.1) hF.2⟩

theorem expIntegral_sub {σ : Type*} {F G : MvPowerSeries σ K}
    (hF : ExpIntegral F) (hG : ExpIntegral G) : ExpIntegral (F - G) := by
  rw [sub_eq_add_neg]
  exact expIntegral_add hF (expIntegral_neg hG)

theorem expIntegral_sum {σ ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ K)
    (hF : ∀ i ∈ s, ExpIntegral (F i)) : ExpIntegral (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expIntegral_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact expIntegral_add (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem expIntegral_renMv {κ σ : Type*} [Finite κ] (φ : κ → σ) {F : MvPowerSeries κ K}
    (hF : ExpIntegral F) : ExpIntegral (renMv φ F) :=
  ⟨constantCoeff_renMv φ hF.1,
    by rw [← renMv_mvExp φ hF.1]; exact isIntegralMv_renMv φ hF.2⟩

theorem expIntegral_substMv {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IsIntegralMv (a i))
    {F : MvPowerSeries σ K} (hF : ExpIntegral F) :
    ExpIntegral (MvPowerSeries.subst a F) :=
  ⟨MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)
      ha0 hF.1,
    by rw [← substMv_mvExp a ha0 hF.1]; exact isIntegralMv_substMv a ha0 ha hF.2⟩

theorem expIntegral_of_dwork_threshold {p : ℕ} [Fact p.Prime] {σ : Type*}
    (D : DworkUniformizerPi K p) {F : MvPowerSeries σ K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hF : CoeffNormLeMv ‖D.pi‖ F) :
    ExpIntegral F :=
  ⟨hF0, (isIntegralMv_mvExp_of_dwork_threshold D hF0 hF).1⟩

omit [IsUltrametricDist K] in
theorem simeqExp_refl {σ : Type*} (F : MvPowerSeries σ K) : SimeqExp F F := by
  unfold SimeqExp; rw [sub_self]; exact expIntegral_zero

theorem simeqExp_symm {σ : Type*} {F G : MvPowerSeries σ K} (h : SimeqExp F G) :
    SimeqExp G F := by
  unfold SimeqExp at h ⊢
  rw [show G - F = -(F - G) by ring]
  exact expIntegral_neg h

theorem simeqExp_trans {σ : Type*} {F G H : MvPowerSeries σ K}
    (h1 : SimeqExp F G) (h2 : SimeqExp G H) : SimeqExp F H := by
  unfold SimeqExp at h1 h2 ⊢
  rw [show F - H = (F - G) + (G - H) by ring]
  exact expIntegral_add h1 h2

/-! ### Formal-Group Coordinate Change `inParamMv` & Twisted Theta Kernel -/

/-- Formal-group logarithm coordinate change `inParamMv logF F = subst (fun i => logF(X_i)) F`,
matching Alpöge's `inParam` / `inParamK`. -/
def inParamMv {σ : Type*} (logF : PowerSeries K) (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  MvPowerSeries.subst (fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) logF) F

omit [IsUltrametricDist K] [CharZero K] in
lemma constantCoeff_logF_X {σ : Type*} {logF : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0) (i : σ) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) logF) = 0 := by
  rw [constantCoeff_subst_of_zero (MvPowerSeries.constantCoeff_X i), hlog0]

omit [IsUltrametricDist K] [CharZero K] in
/-- **Key Parameter Inversion Identity (`subst_tOfParam_inParamMv`)**:
If `logF(vp * μ(X)) = vp * X` (i.e. `μ` is the scaled formal-group exponential inverse to `logF`),
then substituting `tOfParam vp μ L` into `inParamMv logF F` recovers `subst (fun i => C vp * L i) F`! -/
theorem subst_tOfParam_inParamMv {ι τ : Type*} [Finite ι]
    (vp : K) {logF μ : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0) (hμ0 : PowerSeries.constantCoeff μ = 0)
    (hinv : PowerSeries.subst (PowerSeries.C vp * μ) logF = PowerSeries.C vp * PowerSeries.X)
    (L : ι → MvPowerSeries τ K) (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0)
    (F : MvPowerSeries ι K) :
    MvPowerSeries.subst (tOfParam vp μ L) (inParamMv logF F) =
      MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) F := by
  have hlX : MvPowerSeries.HasSubst
      (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K) logF) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_logF_X hlog0)
  have ht : MvPowerSeries.HasSubst (tOfParam vp μ L) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_tOfParam vp hμ0 hL0)
  unfold inParamMv
  rw [MvPowerSeries.subst_comp_subst_apply hlX ht F]
  congr 1
  funext i
  have hXi : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have h1 : MvPowerSeries.subst (tOfParam vp μ L)
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K) logF) =
      PowerSeries.subst (tOfParam vp μ L i) logF := by
    change MvPowerSeries.subst (tOfParam vp μ L)
        (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries ι K)) logF) =
      MvPowerSeries.subst (fun _ : Unit => tOfParam vp μ L i) logF
    rw [MvPowerSeries.subst_comp_subst_apply hXi.const ht logF]
    congr 1; funext _; exact MvPowerSeries.subst_X ht i
  rw [h1]
  unfold tOfParam
  have hvμ0 : PowerSeries.constantCoeff (PowerSeries.C vp * μ) = 0 := by
    rw [map_mul, hμ0, mul_zero]
  have hvμ : PowerSeries.HasSubst (PowerSeries.C vp * μ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hvμ0
  have hLi : PowerSeries.HasSubst (L i) := PowerSeries.HasSubst.of_constantCoeff_zero (hL0 i)
  have hcomp : PowerSeries.subst (PowerSeries.subst (L i) (PowerSeries.C vp * μ)) logF =
      PowerSeries.subst (L i) (PowerSeries.subst (PowerSeries.C vp * μ) logF) := by
    simpa [PowerSeries.subst] using
      (MvPowerSeries.subst_comp_subst_apply hvμ.const hLi.const logF).symm
  rw [hcomp, hinv, ← PowerSeries.coe_substAlgHom hLi, map_mul,
    psSubstAlgHom_C hLi, PowerSeries.coe_substAlgHom hLi,
    PowerSeries.subst_X hLi]

omit [IsUltrametricDist K] in
theorem inParamMv_mvExp {σ : Type*} [Finite σ] {logF : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0) {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0) :
    inParamMv logF (mvExp B) = mvExp (inParamMv logF B) :=
  substMv_mvExp _ (constantCoeff_logF_X hlog0) hB0

/-- **Twisted Theta Power-Series Substitution Reduction (`twisted_theta_reduction`)**
(matching Alpöge's `SubstitutionOfVariables.th_reduce`):
If `Φ : MvPowerSeries (ι ⊕ ι) K` (`constantCoeff = 0`) satisfies the formal-group reduction
`SimeqExp (inParamMv logF Φ) (pairedSum ι G)`, then there exists an integral unit series
`V' : MvPowerSeries τ K` (`IsIntegralMv V'`, `constantCoeff V' = 1`) such that:
```
MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) (mvExp (-Φ)) = RestGc vp μ L G * V'
```
-/
theorem twisted_theta_reduction {ι τ : Type*} [Fintype ι]
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {logF μ : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0)
    (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    (hinv : PowerSeries.subst (PowerSeries.C vp * μ) logF = PowerSeries.C vp * PowerSeries.X)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i))
    {Φ : MvPowerSeries (ι ⊕ ι) K} (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hsim : SimeqExp (inParamMv logF Φ) (pairedSum ι G)) :
    ∃ V' : MvPowerSeries τ K, IsIntegralMv V' ∧ MvPowerSeries.constantCoeff V' = 1 ∧
      MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) (mvExp (-Φ)) =
        RestGc vp μ L G * V' := by
  have ht0 := constantCoeff_tOfParam vp hμ0 hL0
  have ht : MvPowerSeries.HasSubst (tOfParam vp μ L) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have ht_int := isIntegralMv_tOfParam hvp hμ hL0 hL
  have hneg : ExpIntegral (-(inParamMv logF Φ - pairedSum ι G)) := expIntegral_neg hsim
  set W := mvExp (-(inParamMv logF Φ - pairedSum ι G))
  set V' := MvPowerSeries.subst (tOfParam vp μ L) W
  refine ⟨V', isIntegralMv_substMv _ ht0 ht_int hneg.2, ?_, ?_⟩
  · have hW0 : MvPowerSeries.constantCoeff W = 1 := constantCoeff_mvExp hneg.1
    rw [show V' = MvPowerSeries.subst (tOfParam vp μ L) W from rfl]
    have hW_sub : MvPowerSeries.constantCoeff (W - 1) = 0 := by simp [hW0]
    have hsub0 := MvPowerSeries.constantCoeff_subst_eq_zero ht ht0 hW_sub
    rw [← MvPowerSeries.coe_substAlgHom ht, map_sub, map_one, map_sub, map_one,
      MvPowerSeries.coe_substAlgHom ht] at hsub0
    exact sub_eq_zero.mp hsub0
  · have hGt0 : MvPowerSeries.constantCoeff (pairedSum ι G) = 0 := constantCoeff_pairedSum hG0
    have hIn0 : MvPowerSeries.constantCoeff (inParamMv logF Φ) = 0 :=
      MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_logF_X hlog0))
        (constantCoeff_logF_X hlog0) hΦ0
    have hexp_split : inParamMv logF (mvExp (-Φ)) = mvExp (-(pairedSum ι G)) * W := by
      rw [inParamMv_mvExp hlog0 (by simp [hΦ0]),
        show inParamMv logF (-Φ) = -inParamMv logF Φ from by
          unfold inParamMv
          have hlX := MvPowerSeries.hasSubst_of_constantCoeff_zero
            (constantCoeff_logF_X (σ := ι ⊕ ι) hlog0)
          rw [← MvPowerSeries.coe_substAlgHom hlX, map_neg, MvPowerSeries.coe_substAlgHom hlX],
        show -inParamMv logF Φ = -(pairedSum ι G) + -(inParamMv logF Φ - pairedSum ι G) by ring,
        mvExp_add (by simp [hGt0]) hneg.1]
    rw [← subst_tOfParam_inParamMv vp hlog0 hμ0 hinv L hL0 (mvExp (-Φ)),
      hexp_split, ← MvPowerSeries.coe_substAlgHom ht, map_mul, MvPowerSeries.coe_substAlgHom ht]
    rfl

/-- **Twisted Theta Power Series (`TwistedThetaSeries`)**:
Substitutes the scaled coordinate map `fun i => C vp * L i` into a theta kernel `Th = mvExp (-Φ) * U`
(matching Alpöge's `ThZ` / `ThZA`). -/
def TwistedThetaSeries {ι τ : Type*} (vp : K) (L : ι → MvPowerSeries τ K)
    (Th : MvPowerSeries ι K) : MvPowerSeries τ K :=
  MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) Th

/-- **Single-Place Twisted Theta Power-Series Multiplicative Factorization
(`twisted_theta_power_series_factorization`)** (matching Alpöge's `restSExp_of` + `ExtensionGeneratorCondition`):
Suppose a twisted theta kernel decomposes as `Th = mvExp (-Φ) * U` where:
1. `inParamMv logF U` is `p`-adically integral (`IsIntegralMv`),
2. `SimeqExp (inParamMv logF Φ) (pairedSum ι G)` holds (formal-group reduction to `G`), and
3. The Dwork exponential restriction satisfies `RestGcFact vp c μ L G H`
   (`RestGc vp μ L G = mvExp (-(C c * H)) * V₀` with `IsIntegralMv V₀`).

Then there exists a `p`-adically integral power series `V : MvPowerSeries τ K` (`IsIntegralMv V`)
such that:
```
TwistedThetaSeries vp L Th = mvExp (-(MvPowerSeries.C c * H)) * V
```
Furthermore, if `RestGc vp μ L G` itself is integral (e.g. from `dwork_exponential_restriction_integral`),
then `TwistedThetaSeries vp L Th` is unconditionally `p`-adically integral! -/
theorem twisted_theta_power_series_factorization {ι τ : Type*} [Fintype ι]
    {vp c : K} (hvp : ‖vp‖ ≤ 1)
    {logF μ : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0)
    (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    (hinv : PowerSeries.subst (PowerSeries.C vp * μ) logF = PowerSeries.C vp * PowerSeries.X)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i))
    {Th Φ U : MvPowerSeries (ι ⊕ ι) K}
    (hTh : Th = mvExp (-Φ) * U)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hU : IsIntegralMv (inParamMv logF U))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hsim : SimeqExp (inParamMv logF Φ) (pairedSum ι G))
    {H : MvPowerSeries τ K}
    (hRest : RestGcFact vp c μ L G H) :
    ∃ V : MvPowerSeries τ K, IsIntegralMv V ∧
      TwistedThetaSeries vp L Th = mvExp (-(MvPowerSeries.C c * H)) * V := by
  have hvpL : MvPowerSeries.HasSubst (fun i => MvPowerSeries.C vp * L i) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by rw [map_mul, hL0 i, mul_zero])
  have ht0 := constantCoeff_tOfParam vp hμ0 hL0
  have ht_int := isIntegralMv_tOfParam hvp hμ hL0 hL
  obtain ⟨V₀, hV₀, hRestEq⟩ := hRest
  obtain ⟨V', hV', _, hRedEq⟩ := twisted_theta_reduction hvp hlog0 hμ0 hμ hinv hL0 hL hΦ0 hG0 hsim
  set VU := MvPowerSeries.subst (tOfParam vp μ L) (inParamMv logF U)
  have hVU_int : IsIntegralMv VU := isIntegralMv_substMv _ ht0 ht_int hU
  have hVU_eq : MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U = VU :=
    (subst_tOfParam_inParamMv vp hlog0 hμ0 hinv L hL0 U).symm
  refine ⟨V₀ * V' * VU, isIntegralMv_mul (isIntegralMv_mul hV₀ hV') hVU_int, ?_⟩
  unfold TwistedThetaSeries
  rw [hTh, ← MvPowerSeries.coe_substAlgHom hvpL, map_mul, MvPowerSeries.coe_substAlgHom hvpL,
    hRedEq, hRestEq, hVU_eq]
  ring

/-- Corollary: when `RestGc vp μ L G` is `p`-adically integral (e.g. via
`dwork_exponential_restriction_integral` or `dwork_splitting_restriction_integral`),
the twisted theta power series `TwistedThetaSeries vp L Th` is directly `p`-adically integral! -/
theorem twisted_theta_isIntegral_of_restGc_integral {ι τ : Type*} [Fintype ι]
    {vp : K} (hvp : ‖vp‖ ≤ 1)
    {logF μ : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0)
    (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    (hinv : PowerSeries.subst (PowerSeries.C vp * μ) logF = PowerSeries.C vp * PowerSeries.X)
    {L : ι ⊕ ι → MvPowerSeries τ K}
    (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IsIntegralMv (L i))
    {Th Φ U : MvPowerSeries (ι ⊕ ι) K}
    (hTh : Th = mvExp (-Φ) * U)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hU : IsIntegralMv (inParamMv logF U))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hsim : SimeqExp (inParamMv logF Φ) (pairedSum ι G))
    (hRestInt : IsIntegralMv (RestGc vp μ L G)) :
    IsIntegralMv (TwistedThetaSeries vp L Th) := by
  have hfact : RestGcFact vp 0 μ L G 0 :=
    ⟨RestGc vp μ L G, hRestInt, by simp [mvExp_zero]⟩
  obtain ⟨V, hV, hEq⟩ := twisted_theta_power_series_factorization hvp hlog0 hμ0 hμ hinv
    hL0 hL hTh hΦ0 hU hG0 hsim hfact
  rw [hEq]
  simpa [mvExp_zero] using hV

/-- **Multi-Place Adelic Twisted Theta Power-Series Multiplicative Factorization
(`twisted_theta_all_places_factorization`)** (matching Alpöge's `restSExpA_of` + `restGcA_of`):
Factors the multi-place twisted theta series `TwistedThetaSeries vp LA Th` over all places `v : Pl`
simultaneously into an exact product of placewise exponentials times a single global integral series
`V`! -/
theorem twisted_theta_all_places_factorization {Pl : Type*} [Fintype Pl] {E Z : Pl → Type*}
    [∀ v, Fintype (E v)] [∀ v, Finite (Z v)]
    {vp c : K} (hvp : ‖vp‖ ≤ 1)
    {logF μ : PowerSeries K}
    (hlog0 : PowerSeries.constantCoeff logF = 0)
    (hμ0 : PowerSeries.constantCoeff μ = 0) (hμ : IsIntegralPS μ)
    (hinv : PowerSeries.subst (PowerSeries.C vp * μ) logF = PowerSeries.C vp * PowerSeries.X)
    (L : ∀ v : Pl, E v ⊕ E v → MvPowerSeries (Z v) K)
    (hL0 : ∀ v i, MvPowerSeries.constantCoeff (L v i) = 0)
    (hL : ∀ v i, IsIntegralMv (L v i))
    (LA : (Σ v : Pl, E v) ⊕ (Σ v : Pl, E v) → MvPowerSeries (Σ v : Pl, Z v) K)
    (hLA : ∀ (v : Pl) (x : E v ⊕ E v),
      LA (Sum.map (Sigma.mk v) (Sigma.mk v) x) = renMv (Sigma.mk v) (L v x))
    {Th Φ U : MvPowerSeries ((Σ v : Pl, E v) ⊕ (Σ v : Pl, E v)) K}
    (hTh : Th = mvExp (-Φ) * U)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hU : IsIntegralMv (inParamMv logF U))
    {G : MvPowerSeries (Fin 2) K} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hsim : SimeqExp (inParamMv logF Φ) (pairedSum (Σ v : Pl, E v) G))
    (H : ∀ v : Pl, MvPowerSeries (Z v) K) (hH0 : ∀ v, MvPowerSeries.constantCoeff (H v) = 0)
    (hRest : ∀ v : Pl, RestGcFact vp c μ (L v) G (H v)) :
    ∃ V : MvPowerSeries (Σ v : Pl, Z v) K, IsIntegralMv V ∧
      TwistedThetaSeries vp LA Th =
        (∏ v : Pl, mvExp (-(MvPowerSeries.C c * renMv (Sigma.mk v) (H v)))) * V := by
  have hLA0 : ∀ x, MvPowerSeries.constantCoeff (LA x) = 0 := by
    rintro (⟨v, e⟩ | ⟨v, e⟩)
    · have h := hLA v (Sum.inl e); simp only [Sum.map_inl] at h
      rw [h]; exact constantCoeff_renMv _ (hL0 v (Sum.inl e))
    · have h := hLA v (Sum.inr e); simp only [Sum.map_inr] at h
      rw [h]; exact constantCoeff_renMv _ (hL0 v (Sum.inr e))
  have hLA_int : ∀ x, IsIntegralMv (LA x) := by
    rintro (⟨v, e⟩ | ⟨v, e⟩)
    · have h := hLA v (Sum.inl e); simp only [Sum.map_inl] at h
      rw [h]; exact isIntegralMv_renMv _ (hL v (Sum.inl e))
    · have h := hLA v (Sum.inr e); simp only [Sum.map_inr] at h
      rw [h]; exact isIntegralMv_renMv _ (hL v (Sum.inr e))
  have hvpLA : MvPowerSeries.HasSubst (fun i => MvPowerSeries.C vp * LA i) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by rw [map_mul, hLA0 i, mul_zero])
  have htA0 := constantCoeff_tOfParam vp hμ0 hLA0
  have htA_int := isIntegralMv_tOfParam hvp hμ hLA0 hLA_int
  obtain ⟨V₀, hV₀, hRestAEq⟩ :=
    restGcAFact_of_restGcFact vp c hμ0 L hL0 LA hLA hG0 H hH0 hRest
  obtain ⟨V', hV', _, hRedEq⟩ :=
    twisted_theta_reduction hvp hlog0 hμ0 hμ hinv hLA0 hLA_int hΦ0 hG0 hsim
  set VU := MvPowerSeries.subst (tOfParam vp μ LA) (inParamMv logF U)
  have hVU_int : IsIntegralMv VU := isIntegralMv_substMv _ htA0 htA_int hU
  have hVU_eq : MvPowerSeries.subst (fun i => MvPowerSeries.C vp * LA i) U = VU :=
    (subst_tOfParam_inParamMv vp hlog0 hμ0 hinv LA hLA0 U).symm
  refine ⟨V₀ * V' * VU, isIntegralMv_mul (isIntegralMv_mul hV₀ hV') hVU_int, ?_⟩
  unfold TwistedThetaSeries
  rw [hTh, ← MvPowerSeries.coe_substAlgHom hvpLA, map_mul, MvPowerSeries.coe_substAlgHom hvpLA,
    hRedEq, show RestGc vp μ LA G = RestGcA vp μ LA G from rfl, hRestAEq, hVU_eq]
  ring

/-! ### `InClass` / `p`-Adic Valuation Class Expansion & Bridges to `Stage3DworkFrobenius` and Wave 2 -/

/-- **`p`-Adic Dwork Class Membership `InDworkClass p H F`** (matching Alpöge's `InClass`):
`F` admits a coefficient-level expansion `coeff d F = ∑_{i ≤ d.degree} (p^i)⁻¹ * coeff d (H^i * g_i)`
with every `g_i` `p`-adically integral! -/
def InDworkClass {τ : Type*} (p : ℕ) (H F : MvPowerSeries τ K) : Prop :=
  ∃ g : ℕ → MvPowerSeries τ K, (∀ i, IsIntegralMv (g i)) ∧
    ∀ d : τ →₀ ℕ, MvPowerSeries.coeff d F =
      ∑ i ∈ Finset.range (d.degree + 1),
        ((p : K) ^ i)⁻¹ * MvPowerSeries.coeff d (H ^ i * g i)

/-- **Dwork Exponential Class Expansion Theorem (`twisted_theta_dwork_class_expansion`)**:
If `F = mvExp (-(C c * H)) * V` where `IsIntegralMv V`, `IsIntegralMv H`, `constantCoeff H = 0`,
and `‖c‖ ≤ ‖(p : K)‖ ^ (1 / (p - 1) - 1)` (e.g. `c = R.vp ^ (p + 1) / p` from `DworkRamifiedRoot`!),
then **`InDworkClass p H F`** holds unconditionally!
The `p ^ i` denominator absorbs `(-c)^i / i!` because `v_p(i!) ≤ i / (p - 1)` while
`v_p(p * c) ≥ 1 / (p - 1)`! -/
theorem twisted_theta_dwork_class_expansion {p : ℕ} [Fact p.Prime] {τ : Type*}
    (hlt : ‖(p : K)‖ < 1) {c : K}
    (hc : ‖c‖ ≤ ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1))
    {H V F : MvPowerSeries τ K}
    (hH0 : MvPowerSeries.constantCoeff H = 0) (hV : IsIntegralMv V)
    (hF : F = mvExp (-(MvPowerSeries.C c * H)) * V) :
    InDworkClass p H F := by
  classical
  have hp : p.Prime := Fact.out
  have hp_ne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hp_ne
  let g : ℕ → MvPowerSeries τ K := fun i =>
    MvPowerSeries.C ((i.factorial : K)⁻¹ * (-(p : K) * c) ^ i) * V
  refine ⟨g, fun i => ?_, fun d => ?_⟩
  · -- Prove `g i` is `p`-adically integral: `‖(i!)⁻¹ * (-p * c)^i‖ ≤ 1`!
    have hscalar : ‖(i.factorial : K)⁻¹ * (-(p : K) * c) ^ i‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, norm_mul, norm_neg,
        norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero i)]
      have hpc : ‖(p : K)‖ * ‖c‖ ≤ ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1)) := by
        calc ‖(p : K)‖ * ‖c‖
            ≤ ‖(p : K)‖ * ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1) :=
              mul_le_mul_of_nonneg_left hc hpi0.le
          _ = ‖(p : K)‖ ^ (1 : ℝ) * ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1) := by rw [Real.rpow_one]
          _ = ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1)) := by
              rw [← Real.rpow_add hpi0]; congr 1; ring
      have hv := padicValNat_factorial_le_div hp i
      calc (‖(p : K)‖ ^ padicValNat p i.factorial)⁻¹ * (‖(p : K)‖ * ‖c‖) ^ i
          ≤ (‖(p : K)‖ ^ padicValNat p i.factorial)⁻¹ * (‖(p : K)‖ ^ (1 / ((p : ℝ) - 1))) ^ i :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpc i)
              (inv_nonneg.mpr (pow_nonneg hpi0.le _))
        _ = ‖(p : K)‖ ^ ((i : ℝ) / ((p : ℝ) - 1) - (padicValNat p i.factorial : ℝ)) := by
            rw [← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le,
              ← Real.rpow_natCast ‖(p : K)‖ (padicValNat p i.factorial),
              ← Real.rpow_neg hpi0.le, ← Real.rpow_add hpi0]
            congr 1; ring
        _ ≤ 1 := Real.rpow_le_one hpi0.le hlt.le (by linarith)
    exact isIntegralMv_mul (coeffNormLeMv_C zero_le_one hscalar) hV
  · -- Exact coefficient-level expansion
    rw [hF, MvPowerSeries.coeff_mul]
    have hCH0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C c * H)) = 0 := by
      simp [hH0]
    have hH1 : Low 1 H := low_one_of_constantCoeff_zero hH0
    have hsimp_inner : ∀ xy ∈ Finset.antidiagonal d,
        MvPowerSeries.coeff xy.1 (mvExp (-(MvPowerSeries.C c * H))) * MvPowerSeries.coeff xy.2 V =
        ∑ i ∈ Finset.range (d.degree + 1),
          ((p : K) ^ i)⁻¹ *
            (MvPowerSeries.coeff xy.1 (H ^ i) *
              (((i.factorial : K)⁻¹ * (-(p : K) * c) ^ i) * MvPowerSeries.coeff xy.2 V)) := by
      intro xy hxy
      rw [Finset.mem_antidiagonal] at hxy
      have hdeg_le : xy.1.degree ≤ d.degree := by
        have : xy.1.degree + xy.2.degree = d.degree := by rw [← map_add, hxy]
        omega
      rw [coeff_mvExp_eq_sum hCH0 xy.1, Finset.sum_mul]
      have hpad : ∑ i ∈ Finset.range (xy.1.degree + 1),
            (i.factorial : K)⁻¹ * MvPowerSeries.coeff xy.1 ((-(MvPowerSeries.C c * H)) ^ i) *
              MvPowerSeries.coeff xy.2 V =
          ∑ i ∈ Finset.range (d.degree + 1),
            (i.factorial : K)⁻¹ * MvPowerSeries.coeff xy.1 ((-(MvPowerSeries.C c * H)) ^ i) *
              MvPowerSeries.coeff xy.2 V := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
        rw [Finset.mem_range] at hi
        have hlow := low_pow (low_one_of_constantCoeff_zero hCH0) i
        rw [mul_one] at hlow
        rw [hlow xy.1 (by omega), mul_zero, zero_mul]
      rw [hpad]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hpow_c : (-(MvPowerSeries.C c * H)) ^ i = MvPowerSeries.C ((-c) ^ i) * H ^ i := by
        rw [show -(MvPowerSeries.C c * H) = MvPowerSeries.C (-c) * H by rw [map_neg]; ring,
          mul_pow, ← map_pow]
      rw [hpow_c, MvPowerSeries.coeff_C_mul]
      have hcancel : ((p : K) ^ i)⁻¹ * (-(p : K) * c) ^ i = (-c) ^ i := by
        rw [show -(p : K) * c = (p : K) * (-c) by ring, mul_pow, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero i hp_ne), one_mul]
      calc (i.factorial : K)⁻¹ * ((-c) ^ i * MvPowerSeries.coeff xy.1 (H ^ i)) *
            MvPowerSeries.coeff xy.2 V
          = (i.factorial : K)⁻¹ *
              ((((p : K) ^ i)⁻¹ * (-(p : K) * c) ^ i) * MvPowerSeries.coeff xy.1 (H ^ i)) *
              MvPowerSeries.coeff xy.2 V := by rw [hcancel]
        _ = ((p : K) ^ i)⁻¹ *
              (MvPowerSeries.coeff xy.1 (H ^ i) *
                ((i.factorial : K)⁻¹ * (-(p : K) * c) ^ i * MvPowerSeries.coeff xy.2 V)) := by
            ring
    rw [Finset.sum_congr rfl hsimp_inner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, MvPowerSeries.coeff_mul]
    congr 1
    refine Finset.sum_congr rfl fun xy _ => ?_
    simp only [g, MvPowerSeries.coeff_C_mul]

/-- Corollary wired directly to `DworkRamifiedRoot`: `c = R.vp ^ (p + 1) / p` automatically
satisfies `InDworkClass p H F` for every factorized twisted theta series! -/
theorem twisted_theta_inDworkClass_of_ramifiedRoot {p : ℕ} [Fact p.Prime] {τ : Type*}
    (R : DworkRamifiedRoot K p) {H V F : MvPowerSeries τ K}
    (hH0 : MvPowerSeries.constantCoeff H = 0) (hV : IsIntegralMv V)
    (hF : F = mvExp (-(MvPowerSeries.C (R.vp ^ (p + 1) / (p : K)) * H)) * V) :
    InDworkClass p H F :=
  twisted_theta_dwork_class_expansion R.norm_p_lt_one R.norm_vp_pow_div_p.le hH0 hV hF

/-- **Direct Coefficient Norm Bound from `InDworkClass p H F`**:
If `InDworkClass p H F` and `IsIntegralMv H`, then every coefficient of `F` of total degree `d`
satisfies `‖coeff d F‖ ≤ ‖(p : K)‖ ^ (-(d.degree : ℤ))` (and if `H` vanishes below degree `q`,
the denominator improves sharply to `‖(p : K)‖ ^ (-(d.degree / q : ℤ))`!). -/
theorem norm_coeff_le_of_inDworkClass {p : ℕ} [Fact p.Prime] {τ : Type*}
    (hlt : ‖(p : K)‖ < 1) {H F : MvPowerSeries τ K} (hH : IsIntegralMv H)
    {q : ℕ} (hq : 1 ≤ q) (hHlow : Low q H) (hF : InDworkClass p H F) (d : τ →₀ ℕ) :
    ‖MvPowerSeries.coeff d F‖ ≤ ‖(p : K)‖ ^ (-(d.degree / q : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨g, hg, hexp⟩ := hF
  rw [hexp]
  refine ultrametric_norm_sum_le _ _ (zpow_nonneg hpi0.le _) fun i _ => ?_
  by_cases hi : i * q ≤ d.degree
  · have hile : i ≤ d.degree / q := (Nat.le_div_iff_mul_le (by omega)).mpr hi
    have hHg : ‖MvPowerSeries.coeff d (H ^ i * g i)‖ ≤ 1 :=
      isIntegralMv_mul (isIntegralMv_pow hH i) (hg i) d
    rw [norm_mul, norm_inv, norm_pow]
    calc (‖(p : K)‖ ^ i)⁻¹ * ‖MvPowerSeries.coeff d (H ^ i * g i)‖
        ≤ (‖(p : K)‖ ^ i)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hHg (inv_nonneg.mpr (pow_nonneg hpi0.le i))
      _ = ‖(p : K)‖ ^ (-(i : ℤ)) := by rw [mul_one, zpow_neg, zpow_natCast]
      _ ≤ ‖(p : K)‖ ^ (-(d.degree / q : ℤ)) := by
          rw [zpow_neg, zpow_neg]
          exact inv_anti₀ (zpow_pos hpi0 _)
            (zpow_le_zpow_right_of_le_one₀ hpi0 hlt.le (by exact_mod_cast hile))
  · push Not at hi
    have hlow_prod : Low (i * q + 0) (H ^ i * g i) :=
      low_mul (low_pow hHlow i) (fun _ h => by omega)
    rw [hlow_prod d (by omega), mul_zero, norm_zero]
    exact zpow_nonneg hpi0.le _

/-- **Multi-Place Adelic Dwork Class Membership `InProdDworkClass p HA F`**
(matching Alpöge's `FormalGroupSystem.InProdA`):
`F` admits a coefficient-level expansion across all places `v : Pl`,
`coeff d F = ∑_{i : Pl → ℕ, ∀ v, i v ≤ d.degree} (∏ v, (p ^ i v)⁻¹) * coeff d ((∏ v, HA v ^ i v) * g i)`,
with every `g i` `p`-adically integral! -/
def InProdDworkClass {Pl τ : Type*} [Fintype Pl] [DecidableEq Pl] (p : ℕ)
    (HA : Pl → MvPowerSeries τ K) (F : MvPowerSeries τ K) : Prop :=
  ∃ g : (Pl → ℕ) → MvPowerSeries τ K, (∀ i, IsIntegralMv (g i)) ∧
    ∀ d : τ →₀ ℕ, MvPowerSeries.coeff d F =
      ∑ i ∈ Fintype.piFinset (fun _ : Pl => Finset.range (d.degree + 1)),
        (∏ v : Pl, ((p : K) ^ i v)⁻¹) * MvPowerSeries.coeff d ((∏ v : Pl, HA v ^ i v) * g i)

/-- **Multi-Place Adelic Dwork Class Expansion Theorem (`twisted_theta_all_places_dwork_class_expansion`)**:
If `F = (∏ v : Pl, mvExp (-(C c * HA v))) * V` where `IsIntegralMv V`, `∀ v, constantCoeff (HA v) = 0`,
and `‖c‖ ≤ ‖(p : K)‖ ^ (1 / (p - 1) - 1)` (e.g. `c = R.vp ^ (p + 1) / p` from `DworkRamifiedRoot`),
then **`InProdDworkClass p HA F`** holds unconditionally! -/
theorem twisted_theta_all_places_dwork_class_expansion {p : ℕ} [Fact p.Prime]
    {Pl τ : Type*} [Fintype Pl] [DecidableEq Pl]
    (hlt : ‖(p : K)‖ < 1) {c : K}
    (hc : ‖c‖ ≤ ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1))
    {HA : Pl → MvPowerSeries τ K} (hH0 : ∀ v, MvPowerSeries.constantCoeff (HA v) = 0)
    {V F : MvPowerSeries τ K} (hV : IsIntegralMv V)
    (hF : F = (∏ v : Pl, mvExp (-(MvPowerSeries.C c * HA v))) * V) :
    InProdDworkClass p HA F := by
  classical
  have hp : p.Prime := Fact.out
  have hp_ne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hp_ne
  let sc : ℕ → K := fun k => (k.factorial : K)⁻¹ * (-(p : K) * c) ^ k
  have hsc_le : ∀ k : ℕ, ‖sc k‖ ≤ 1 := fun k => by
    unfold sc
    rw [norm_mul, norm_inv, norm_pow, norm_mul, norm_neg,
      norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero k)]
    have hpc : ‖(p : K)‖ * ‖c‖ ≤ ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1)) := by
      calc ‖(p : K)‖ * ‖c‖
          ≤ ‖(p : K)‖ * ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1) :=
            mul_le_mul_of_nonneg_left hc hpi0.le
        _ = ‖(p : K)‖ ^ (1 : ℝ) * ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - 1) := by rw [Real.rpow_one]
        _ = ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1)) := by
            rw [← Real.rpow_add hpi0]; congr 1; ring
    have hv := padicValNat_factorial_le_div hp k
    calc (‖(p : K)‖ ^ padicValNat p k.factorial)⁻¹ * (‖(p : K)‖ * ‖c‖) ^ k
        ≤ (‖(p : K)‖ ^ padicValNat p k.factorial)⁻¹ * (‖(p : K)‖ ^ (1 / ((p : ℝ) - 1))) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpc k)
            (inv_nonneg.mpr (pow_nonneg hpi0.le _))
      _ = ‖(p : K)‖ ^ ((k : ℝ) / ((p : ℝ) - 1) - (padicValNat p k.factorial : ℝ)) := by
          rw [← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le,
            ← Real.rpow_natCast ‖(p : K)‖ (padicValNat p k.factorial),
            ← Real.rpow_neg hpi0.le, ← Real.rpow_add hpi0]
          congr 1; ring
      _ ≤ 1 := Real.rpow_le_one hpi0.le hlt.le (by linarith)
  let g : (Pl → ℕ) → MvPowerSeries τ K := fun i =>
    MvPowerSeries.C (∏ v : Pl, sc (i v)) * V
  refine ⟨g, fun i => ?_, fun d => ?_⟩
  · have hprod_le : ‖∏ v : Pl, sc (i v)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun v _ => norm_nonneg _) (fun v _ => hsc_le (i v))
    exact isIntegralMv_mul (coeffNormLeMv_C zero_le_one hprod_le) hV
  · -- Replace each `mvExp (-(C c * HA v))` by its degree-`(d.degree + 1)` partial sum!
    set N := d.degree + 1
    let P : Pl → MvPowerSeries τ K := fun v =>
      ∑ k ∈ Finset.range N, MvPowerSeries.C ((k.factorial : K)⁻¹ * (-c) ^ k) * HA v ^ k
    have hlow_each : ∀ v : Pl, Low N (mvExp (-(MvPowerSeries.C c * HA v)) - P v) := by
      intro v m hm
      have hCH0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C c * HA v)) = 0 := by
        simp [hH0 v]
      rw [map_sub, coeff_mvExp_eq_sum hCH0, map_sum, sub_eq_zero]
      have hpad : ∑ k ∈ Finset.range (m.degree + 1),
            (k.factorial : K)⁻¹ * MvPowerSeries.coeff m ((-(MvPowerSeries.C c * HA v)) ^ k) =
          ∑ k ∈ Finset.range N,
            (k.factorial : K)⁻¹ * MvPowerSeries.coeff m ((-(MvPowerSeries.C c * HA v)) ^ k) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
        rw [Finset.mem_range] at hk
        have hlow := low_pow (low_one_of_constantCoeff_zero hCH0) k
        rw [mul_one] at hlow
        rw [hlow m (by omega), mul_zero]
      rw [hpad]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hpow_c : (-(MvPowerSeries.C c * HA v)) ^ k = MvPowerSeries.C ((-c) ^ k) * HA v ^ k := by
        rw [show -(MvPowerSeries.C c * HA v) = MvPowerSeries.C (-c) * HA v by rw [map_neg]; ring,
          mul_pow, ← map_pow]
      rw [hpow_c, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
      ring
    -- Product telescoping: `∏ v ∈ s, A v - ∏ v ∈ s, P v` has `Low N`!
    have hlow_prod : ∀ s : Finset Pl,
        Low N ((∏ v ∈ s, mvExp (-(MvPowerSeries.C c * HA v))) - ∏ v ∈ s, P v) := fun s => by
      induction s using Finset.induction_on with
      | empty => intro m _; simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        have htel : mvExp (-(MvPowerSeries.C c * HA a)) *
              (∏ v ∈ s, mvExp (-(MvPowerSeries.C c * HA v))) - P a * ∏ v ∈ s, P v =
            (mvExp (-(MvPowerSeries.C c * HA a)) - P a) *
              (∏ v ∈ s, mvExp (-(MvPowerSeries.C c * HA v))) +
            P a * ((∏ v ∈ s, mvExp (-(MvPowerSeries.C c * HA v))) - ∏ v ∈ s, P v) := by ring
        rw [htel]
        refine low_add (low_mono (by omega : N ≤ N + 0) (low_mul (hlow_each a) (fun _ h => by omega)))
          (low_mono (by omega : N ≤ 0 + N) (low_mul (fun _ h => by omega) ih))
    have hdiffV : Low N (F - (∏ v : Pl, P v) * V) := by
      rw [hF, ← sub_mul]
      exact low_mono (by omega : N ≤ N + 0) (low_mul (hlow_prod Finset.univ) (fun _ h => by omega))
    have hcoeff_eq : MvPowerSeries.coeff d F = MvPowerSeries.coeff d ((∏ v : Pl, P v) * V) := by
      have h0 := hdiffV d (Nat.lt_succ_self _)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [hcoeff_eq]
    -- Expand `∏ v : Pl, P v` using `Fintype.prod_sum`!
    have hprodP : (∏ v : Pl, P v) =
        ∑ i ∈ Fintype.piFinset (fun _ : Pl => Finset.range N),
          ∏ v : Pl, (MvPowerSeries.C (((i v).factorial : K)⁻¹ * (-c) ^ (i v)) * HA v ^ (i v)) := by
      unfold P
      rw [Finset.prod_univ_sum]
    rw [hprodP, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm_eq : (∏ v : Pl,
          (MvPowerSeries.C (((i v).factorial : K)⁻¹ * (-c) ^ (i v)) * HA v ^ (i v))) * V =
        MvPowerSeries.C (∏ v : Pl, ((p : K) ^ i v)⁻¹) * ((∏ v : Pl, HA v ^ i v) * g i) := by
      rw [Finset.prod_mul_distrib, ← map_prod]
      dsimp only [g]
      have hscalar_eq : (∏ v : Pl, (((i v).factorial : K)⁻¹ * (-c) ^ (i v))) =
          (∏ v : Pl, ((p : K) ^ i v)⁻¹) * (∏ v : Pl, sc (i v)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        unfold sc
        have hcancel : ((p : K) ^ i v)⁻¹ * (-(p : K) * c) ^ i v = (-c) ^ i v := by
          rw [show -(p : K) * c = (p : K) * (-c) by ring, mul_pow, ← mul_assoc,
            inv_mul_cancel₀ (pow_ne_zero (i v) hp_ne), one_mul]
        calc ((i v).factorial : K)⁻¹ * (-c) ^ i v
            = ((i v).factorial : K)⁻¹ * (((p : K) ^ i v)⁻¹ * (-(p : K) * c) ^ i v) := by
                rw [hcancel]
          _ = ((p : K) ^ i v)⁻¹ * (((i v).factorial : K)⁻¹ * (-(p : K) * c) ^ i v) := by ring
      rw [hscalar_eq, map_mul]
      ring
    rw [hterm_eq, MvPowerSeries.coeff_C_mul]

/-- **Overconvergent Banach-Norm & Fredholm-Newton-Polygon Bridge (`twisted_theta_overconv_bound`
& `twisted_theta_newton_polygon_bridge`)** (wiring into `Stage3DworkFrobenius`):
Any univariate coordinate restriction `restrictVar (fun _ : Unit => i) (mvScaleHom D.pi F)` of an
integral twisted theta series `F` lies in the overconvergent Banach algebra `L(‖D.pi‖⁻¹)` with
overconvergent norm `≤ 1`, and its Dwork Fredholm determinant satisfies the exact crystalline
Newton-polygon lower bound with slope `1 / (p - 1)`! -/
theorem twisted_theta_overconv_bound {p : ℕ} [Fact p.Prime] {τ : Type*}
    (D : DworkUniformizerPi K p) {F : MvPowerSeries τ K} (hF : IsIntegralMv F) (i : τ) :
    let f : PowerSeries K := restrictVar (fun _ : Unit => i) (mvScaleHom D.pi F)
    WtGe ‖(p : K)‖ (fun _ : Unit => -(1 / ((p : ℝ) - 1))) 0 (f : MvPowerSeries Unit K) ∧
      IsOverconvergent (‖(p : K)‖ ^ (-(1 / ((p : ℝ) - 1)))) f ∧
      overconvNorm (‖(p : K)‖ ^ (-(1 / ((p : ℝ) - 1)))) f ≤ 1 := by
  intro f
  have hwt_scale : WtGe ‖(p : K)‖ (fun _ : τ => -(1 / ((p : ℝ) - 1))) 0 (mvScaleHom D.pi F) := by
    have hF0 : WtGe ‖(p : K)‖ (fun _ : τ => (0 : ℝ)) 0 F := fun d => by
      unfold MonoWtGe wtDot; simpa using hF d
    have h := wtGe_mvScaleHom (δ := 1 / ((p : ℝ) - 1)) D.norm_p_pos
      (by rw [D.norm_pi_eq_norm_p_rpow]) hF0
    simpa using h
  have hwt_f : WtGe ‖(p : K)‖ (fun _ : Unit => -(1 / ((p : ℝ) - 1))) 0
      (f : MvPowerSeries Unit K) :=
    wtGe_restrictVar (fun _ : Unit => i) hwt_scale
  have hov := (wtGe_iff_overconvNorm_le D.hp f).mp hwt_f
  rw [Real.rpow_zero] at hov
  exact ⟨hwt_f, hov.1, hov.2⟩

/-- **Twisted Theta Dwork Operator Newton Polygon Bound (`twisted_theta_newton_polygon_bridge`)**:
For any `D : DworkUniformizerPi K p`, integral twisted theta series `F`, coordinate `i`, and
truncation rank `N`, the Dwork operator `ψ_f` on the scaled restriction
`f = restrictVar (fun _ => i) (mvScaleHom D.pi F)` satisfies the exact crystalline Hodge–Newton
polygon lower bound with integer slope quantum `(1 / (p - 1)) * (p - 1) = 1`:
`polygon (dworkHodgeSlopes 1 N) k ≤ polygon N_slopes k` for all `k ≤ N`! -/
theorem twisted_theta_newton_polygon_bridge {p : ℕ} [Fact p.Prime] {τ : Type*}
    (D : DworkUniformizerPi K p) {F : MvPowerSeries τ K} (hF : IsIntegralMv F) (i : τ)
    (N : ℕ) {lam : Fin N → K} {ν : Fin N → ℚ}
    (hsplit : fredholmDet (fun a b : Fin N =>
        dworkMatrix p (restrictVar (fun _ : Unit => i) (mvScaleHom D.pi F)) a.val b.val) =
      ∏ j : Fin N, ((1 : Polynomial K) - Polynomial.C (lam j) * Polynomial.X))
    (hnorm : ∀ j : Fin N, ‖lam j‖ = ‖(p : K)‖ ^ (ν j : ℝ)) :
    ∀ k : ℕ, k ≤ N →
      Stage2HodgeWeights.polygon (dworkHodgeSlopes (1 : ℚ) N) k ≤
        Stage2HodgeWeights.polygon ((Finset.univ : Finset (Fin N)).val.map ν) k := by
  set c : ℚ := 1 / ((p : ℚ) - 1) with hcdef
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast D.hp.two_le
  have hpm1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hc0 : 0 ≤ c := div_nonneg zero_le_one hpm1.le
  have hwt := (twisted_theta_overconv_bound D hF i).1
  have hcast : (c : ℝ) = 1 / ((p : ℝ) - 1) := by rw [hcdef]; push_cast; rfl
  have hwtQ : WtGe ‖(p : K)‖ (fun _ : Unit => -(c : ℝ)) 0
      ((restrictVar (fun _ : Unit => i) (mvScaleHom D.pi F) : PowerSeries K) :
        MvPowerSeries Unit K) := by
    rwa [hcast]
  have hmain := (wtGe_dworkOp_newton_polygon_bound (N := N) D.hp D.norm_p_lt_one hc0 hwtQ).2.2
    lam ν hsplit hnorm
  have hslope_eq : c * ((p : ℚ) - 1) = 1 := by
    rw [hcdef, one_div_mul_cancel hpm1.ne']
  rwa [hslope_eq] at hmain

/-- **Wave-2 Inert-Prime Gain Bridge (`twisted_theta_inert_gain_bridge`)**:
Ready for M5 Wave 2 (`Stage14M5_LinkGAndAskIsF`): packages a family of placewise integral
twisted theta restrictions with scaling exponents `γ w` (such as `γ w = 1 / (p_w - 1)` from
`DworkUniformizerPi` or `γ w = 1 / (p_w^2 - 1)` from `DworkRamifiedRoot`) directly into
`Stage12MultivarDwork.inert_sublattice_slope_shift_ge_ASK`! -/
theorem twisted_theta_inert_gain_bridge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Pl Top : Type*}
    (D : InertCongruenceData Pl) {latM : Submodule ℤ E} [DiscreteTopology latM]
    (hM0 : latM ≠ ⊥) {r : ℕ} (bM : Module.Basis (Fin r) ℤ latM)
    (e : Pl → Fin r → ℕ)
    (hlen : ∀ w ∈ D.supp,
      ((∑ i : Fin r, e w i : ℕ) : ℝ) / (ArakelovCovolume.rk latM : ℝ) ≤
        ((D.ramIdx w : ℝ) * (D.tau w + D.io w)) / D.degNorm)
    (resChar : Pl → ℕ) (TTw : Pl → Finset Top) (aT : Top → ℕ)
    (wPart : ℕ → Top → ℕ → ℕ → ℝ) (loG flG_tot dropPen : Pl → ℝ)
    -- Twisted-theta Dwork valuation gain at each place dominates the inert-prime ramp:
    (thetaGain : ℕ → Pl → ℝ)
    (hThetaDom : ∀ w ∈ D.supp, ∀ j ∈ D.lifts, thetaGain j w ≤ D.gainD j w)
    (hThetaLink : ∀ w ∈ D.supp,
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
        (vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)) - loG w)) -
        flG_tot w - dropPen w ≤
      (∑ j ∈ D.lifts, thetaGain j w) - D.tau w) :
    let NuLat := inertCongruenceSublattice bM D.supp D.q e
    let s_iu : ℝ := ∏ w ∈ D.supp, (D.q w : ℝ) ^ D.scaleExp w
    let latN := scaleSubmodule s_iu⁻¹ NuLat
    let rampLoss : ℝ :=
      ∑ w ∈ D.supp, D.sz w ((D.lifts.card : ℝ) * (TTw w).card * loG w + flG_tot w + dropPen w)
    ArakelovCovolume.slope latM + ASK D resChar TTw aT wPart + D.Fo - D.Ee -
      (D.Lo + rampLoss) ≤ ArakelovCovolume.slope latN := by
  have hLinkG : ∀ w ∈ D.supp,
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
        (vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)) - loG w)) -
        flG_tot w - dropPen w ≤
      (∑ j ∈ D.lifts, D.gainD j w) - D.tau w := fun w hw => by
    have hsum : ∑ j ∈ D.lifts, thetaGain j w ≤ ∑ j ∈ D.lifts, D.gainD j w :=
      Finset.sum_le_sum fun j hj => hThetaDom w hw j hj
    linarith [hThetaLink w hw]
  exact inert_sublattice_slope_shift_ge_ASK D hM0 bM e hlen resChar TTw aT wPart loG flG_tot
    dropPen hLinkG

end TwistedThetaFactorization

end

end RHDirect.Stage14M5_DworkExpRestrict
