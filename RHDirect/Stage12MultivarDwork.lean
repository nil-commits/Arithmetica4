import RHDirect.Stage2DworkExp
import RHDirect.Stage11BostDworkSqueeze
import Mathlib.Data.Nat.Log

/-!
# RHDirect.Stage12MultivarDwork

Phase C / Stage 12 **Multivariable Dwork Integrality Lemma, Artin–Hasse Exponential,
Honda / Lubin–Tate Formal Group Integrality, Crystalline `QPack` Valuation, and
Inert-Prime Congruence Sublattice Slope Shift (`LinkG: Ga ≈ ASK`)** in pure Mathlib `v4.33.1`
(0 `sorry`, 0 custom `axiom`s, 0 `native_decide`).

## Contents

1. **Explicit `MvPowerSeries` Norm Calculus, Frobenius Substitution `frobSub`, & Inverse `invOneMv`**:
   - Explicit coefficient-level Frobenius power substitution `frobSub p F` sending `X_i ↦ X_i^p`
     (exact formula `coeff (p • d) (frobSub p F) = coeff d F`, `0` otherwise), proved to be a
     `RingHom` agreeing with `MvPowerSeries.subst (fun i => (MvPowerSeries.X i) ^ p)` with
     zero `Algebra` diamonds.
   - Twisted crystalline Frobenius `frobMapMv σ_aut p F := MvPowerSeries.map σ_aut (frobSub p F)`.
   - Unit inverse `invOneMv F := MvPowerSeries.invOfUnit F 1` with integrality preservation
     `isIntegralMv_invOneMv` by strong induction on total degree `d.degree`.

2. **Unconditional Multivariable Dwork Integrality Lemma (`dwork_lemma_mvPowerSeries`)**:
   - Arbitrary index type `σ : Type*` (finite or infinite!), proved using finite downward-closed
     multi-index truncations `downSet n := (Finset.antidiagonal n).image Prod.fst` and
     `p ∣ Nat.choose p k` (`0 < k < p`).
   - General ultrametric field + Frobenius lift version `dieudonne_dwork_mv_iff`, and exact
     `ℚ_[p]` specialization **`dwork_lemma_mvPowerSeries`**:
     for any `F : MvPowerSeries σ ℚ_[p]` with `constantCoeff F = 1`,
     `(∀ d, ‖coeff d F‖ ≤ 1) ↔ (∀ d ≠ 0, ‖coeff d (frobSub p F * (invOneMv F) ^ p)‖ ≤ ‖(p : ℚ_[p])‖)`.

3. **Artin–Hasse Exponential `E_p(X) ∈ ℤ_[p][[X]]` & Honda / Lubin–Tate Formal Group Integrality**:
   - `artinHasseExp p : PowerSeries ℚ_[p]` (`exp(∑_{m ≥ 0} X^{p^m} / p^m)`), with
     **`artinHasseExp_isIntegral`** proved as an immediate corollary of `dwork_lemma_mvPowerSeries`.
   - Hazewinkel's Functional Equation Lemma (**`honda_formal_group_subst_isIntegral`**):
     for any Honda logarithm `f ∈ ℚ_[p][[X]]` (`f(X) - p⁻¹ f(X^p) ∈ ℤ_[p][[X]]`, `coeff 1 f = 1`)
     and any multivariate `g` of Honda type (`g - p⁻¹ g(X^p) ∈ ℤ_[p][[X]]`), the unique formal
     solution `h = solveSubst f g` of `f(h) = g` is integral (`h ∈ ℤ_[p][[X]]`)!
   - Concrete specializations: **`honda_formal_group_law_isIntegral`** (`F(X, Y) = f⁻¹(f(X) + f(Y))`),
     **`lubinTate_formal_group_isIntegral`** (`log_{LT}(X) = ∑_{m ≥ 0} X^{p^m} / p^m`), and
     **`lubinTate_gm_iso_isIntegral`** (`E_p(X) - 1` is an integral isomorphism `F_{LT} ≅ 𝔾_m`).

4. **Crystalline `QPack` Valuation (`‖th nu‖ = p^{-1/(p-1)}`) & Multivariable Dwork Splitting Weights**:
   - `CrystallineQPack K p` matching Alpöge's `ThetaNormsAndLinks.QPack`, proving the Hodge–Tate
     cokernel annihilator lemma **`CrystallineQPack.cokernel_annihilated_by_nu`** and exact
     valuation `dworkVal p (Q.th Q.nu) = 1 / (p - 1)`.
   - Unconditional concrete instance **`dworkPiQPack`** from any Dwork uniformizer `ϖ^(p-1) = -p`
     (via `Stage2DworkExp.norm_dworkPi`).
   - Multivariable weight theorems **`qpack_mvExp_wtGe`** and **`multivar_dworkSplitting_wtGe`**
     (exact overconvergence slope `(p - 1) / p^2` for `∏_{i} θ(X_i)`).

5. **Inert-Prime Congruence Sublattice Slope Shift (`slope latN - slope latM = Ga + Fo - Ee - Lo`)
   & `linkG_inert_ramp_shift` (`Ga ≈ ASK`)**:
   - Concrete construction of `inertCongruenceSublattice` (`NuLat ≤ latM`, differing ONLY at inert
     primes) and fractional-ideal rescaling `latN = scaleSubmodule s_iu⁻¹ NuLat`, with exact index
     `latIndex latM NuLat = ∏_{w inert} q_w^{∑_i e_w i}` (via `ZMod` quotient isomorphism) and
     exact covolume via `Stage11BostDworkSqueeze.covol_eq_index_mul_covol`.
   - Exact Arakelov slope shift **`slope_shift_eq_Ga_add_Fo_sub_Ee_sub_Lo`** and
     **`slope_shift_ge_Ga_add_Fo_sub_Ee_sub_Lo`**.
   - Von Mangoldt inert-prime ramp bounds (**`vonMangoldtRamp_le_odd_floor_sum`**,
     **`odd_floor_sum_le_padicValNat_factorial`**), **`linkG_inert_ramp_shift`** (`ASK - rampLoss ≤ Ga`),
     and the culminating **`inert_sublattice_slope_shift_ge_ASK`**.
-/

open Real Finset Module Submodule
open scoped BigOperators Pointwise
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage11BostDworkSqueeze

namespace RHDirect.Stage12MultivarDwork

noncomputable section

/-! ## Section 1: Explicit `MvPowerSeries` Norm Calculus, Frobenius Substitution & Unit Inverse -/

section MvPowerSeriesCore

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- A multivariate power series `F ∈ K[[X_i]]` is **integral** (`F ∈ O_K[[X_i]]`) if every
monomial coefficient has ultrametric norm `≤ 1`. -/
def IsIntegralMv (F : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ 1

/-- Every monomial coefficient of `F` has ultrametric norm `≤ B`. -/
def CoeffNormLeMv (B : ℝ) (F : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ B

/-- `F ∈ 1 + p O_K[[X_i]]`: constant term `1` and all nonzero-multi-index coefficients of norm
`≤ ‖(p : K)‖`. -/
def CongOneModPMv (p : ℕ) (F : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff F = 1 ∧
    ∀ d : σ →₀ ℕ, d ≠ 0 → ‖MvPowerSeries.coeff d F‖ ≤ ‖(p : K)‖

lemma coeffNormLeMv_add {B : ℝ} {F G : MvPowerSeries σ K}
    (hF : CoeffNormLeMv B F) (hG : CoeffNormLeMv B G) :
    CoeffNormLeMv B (F + G) := fun d => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))

omit [IsUltrametricDist K] in
lemma coeffNormLeMv_neg {B : ℝ} {F : MvPowerSeries σ K} (hF : CoeffNormLeMv B F) :
    CoeffNormLeMv B (-F) := fun d => by
  rw [map_neg, norm_neg]
  exact hF d

lemma coeffNormLeMv_sub {B : ℝ} {F G : MvPowerSeries σ K}
    (hF : CoeffNormLeMv B F) (hG : CoeffNormLeMv B G) :
    CoeffNormLeMv B (F - G) := by
  rw [sub_eq_add_neg]
  exact coeffNormLeMv_add hF (coeffNormLeMv_neg hG)

lemma coeffNormLeMv_mul {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    {F G : MvPowerSeries σ K} (hF : CoeffNormLeMv B₁ F) (hG : CoeffNormLeMv B₂ G) :
    CoeffNormLeMv (B₁ * B₂) (F * G) := fun d => by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine ultrametric_norm_sum_le _ _ (mul_nonneg hB₁ hB₂) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF x.1) (hG x.2) (norm_nonneg _) hB₁

lemma coeffNormLeMv_sum {ι : Type*} (s : Finset ι) {B : ℝ} (hB : 0 ≤ B)
    {F : ι → MvPowerSeries σ K} (hF : ∀ i ∈ s, CoeffNormLeMv B (F i)) :
    CoeffNormLeMv B (∑ i ∈ s, F i) := fun d => by
  rw [map_sum]
  exact ultrametric_norm_sum_le s _ hB fun i hi => hF i hi d

omit [IsUltrametricDist K] in
lemma coeffNormLeMv_monomial {B : ℝ} (hB : 0 ≤ B) (d : σ →₀ ℕ) {c : K} (hc : ‖c‖ ≤ B) :
    CoeffNormLeMv B (MvPowerSeries.monomial d c) := fun m => by
  classical
  rw [MvPowerSeries.coeff_monomial]
  split_ifs
  · exact hc
  · simpa using hB

omit [IsUltrametricDist K] in
lemma coeffNormLeMv_C {B : ℝ} (hB : 0 ≤ B) {c : K} (hc : ‖c‖ ≤ B) :
    CoeffNormLeMv B (MvPowerSeries.C c : MvPowerSeries σ K) := fun m => by
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · simpa using hB

omit [IsUltrametricDist K] in
lemma isIntegralMv_zero : IsIntegralMv (0 : MvPowerSeries σ K) := fun d => by simp

omit [IsUltrametricDist K] in
lemma isIntegralMv_one : IsIntegralMv (1 : MvPowerSeries σ K) := fun d => by
  classical
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

lemma isIntegralMv_add {F G : MvPowerSeries σ K}
    (hF : IsIntegralMv F) (hG : IsIntegralMv G) : IsIntegralMv (F + G) :=
  coeffNormLeMv_add hF hG

lemma isIntegralMv_sub {F G : MvPowerSeries σ K}
    (hF : IsIntegralMv F) (hG : IsIntegralMv G) : IsIntegralMv (F - G) :=
  coeffNormLeMv_sub hF hG

lemma isIntegralMv_mul {F G : MvPowerSeries σ K}
    (hF : IsIntegralMv F) (hG : IsIntegralMv G) : IsIntegralMv (F * G) := by
  simpa [IsIntegralMv, CoeffNormLeMv] using coeffNormLeMv_mul zero_le_one zero_le_one hF hG

lemma isIntegralMv_pow {F : MvPowerSeries σ K} (hF : IsIntegralMv F) (k : ℕ) :
    IsIntegralMv (F ^ k) := by
  induction k with
  | zero => simpa using isIntegralMv_one (σ := σ) (K := K)
  | succ k ih => rw [pow_succ]; exact isIntegralMv_mul ih hF

omit [IsUltrametricDist K] in
lemma isIntegralMv_monomial (d : σ →₀ ℕ) {c : K} (hc : ‖c‖ ≤ 1) :
    IsIntegralMv (MvPowerSeries.monomial d c) :=
  coeffNormLeMv_monomial zero_le_one d hc

lemma isIntegralMv_sum {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries σ K}
    (hF : ∀ i ∈ s, IsIntegralMv (F i)) : IsIntegralMv (∑ i ∈ s, F i) :=
  coeffNormLeMv_sum s zero_le_one hF

omit [IsUltrametricDist K] in
lemma isIntegralMv_truncBelow (N : ℕ) {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    IsIntegralMv (truncBelow N F) := fun d => by
  rw [coeff_truncBelow]
  split_ifs
  · exact hF d
  · simp

omit [IsUltrametricDist K] in
lemma degree_eq_zero_iff (d : σ →₀ ℕ) : d.degree = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext i
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hi
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
    have hle : d i ≤ d.degree := by
      rw [Finsupp.degree_apply]
      exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) hmem
    omega
  · rintro rfl; simp

omit [IsUltrametricDist K] in
lemma degree_pos_of_ne_zero {d : σ →₀ ℕ} (hd : d ≠ 0) : 0 < d.degree := by
  have hne : d.degree ≠ 0 := mt (degree_eq_zero_iff d).mp hd
  omega

omit [IsUltrametricDist K] in
lemma low_sub_truncBelow (N : ℕ) (F : MvPowerSeries σ K) : Low N (F - truncBelow N F) := by
  intro d hd
  rw [map_sub, coeff_truncBelow, if_pos hd, sub_self]

omit [IsUltrametricDist K] in
lemma low_one_of_constantCoeff_zero {F : MvPowerSeries σ K}
    (hF : MvPowerSeries.constantCoeff F = 0) : Low 1 F := by
  intro d hd
  have hd0 : d = 0 := (degree_eq_zero_iff d).mp (by omega)
  subst hd0
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hF

omit [IsUltrametricDist K] in
lemma low_sub_one_of_constantCoeff_one {F : MvPowerSeries σ K}
    (hF : MvPowerSeries.constantCoeff F = 1) : Low 1 (F - 1) :=
  low_one_of_constantCoeff_zero (by simp [hF])

/-! ### Explicit Multiplicative Inverse `invOneMv` for Constant Term `1` -/

/-- Multiplicative inverse of a multivariate power series `F` with `constantCoeff F = 1`. -/
def invOneMv {R : Type*} [CommRing R] (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  MvPowerSeries.invOfUnit F 1

omit [IsUltrametricDist K] in
theorem mul_invOneMv {F : MvPowerSeries σ K} (hF : MvPowerSeries.constantCoeff F = 1) :
    F * invOneMv F = 1 :=
  MvPowerSeries.mul_invOfUnit F 1 (by simpa using hF)

omit [IsUltrametricDist K] in
theorem invOneMv_mul {F : MvPowerSeries σ K} (hF : MvPowerSeries.constantCoeff F = 1) :
    invOneMv F * F = 1 := by
  rw [mul_comm]
  exact mul_invOneMv hF

omit [IsUltrametricDist K] in
theorem constantCoeff_invOneMv {F : MvPowerSeries σ K} (hF : MvPowerSeries.constantCoeff F = 1) :
    MvPowerSeries.constantCoeff (invOneMv F) = 1 := by
  have h := congrArg MvPowerSeries.constantCoeff (mul_invOneMv hF)
  simp only [map_mul, hF, one_mul, map_one] at h
  exact h

/-- The inverse of an integral multivariate power series with constant term `1` is integral
(proved by strong induction on total degree `d.degree`). -/
theorem isIntegralMv_invOneMv {F : MvPowerSeries σ K}
    (hF0 : MvPowerSeries.constantCoeff F = 1) (hF : IsIntegralMv F) :
    IsIntegralMv (invOneMv F) := by
  classical
  suffices H : ∀ N : ℕ, ∀ d : σ →₀ ℕ, d.degree = N →
      ‖MvPowerSeries.coeff d (invOneMv F)‖ ≤ 1 from fun d => H _ d rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro d hd
    by_cases hd0 : d = 0
    · subst hd0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_invOneMv hF0, norm_one]
    · have hmul : MvPowerSeries.coeff d (F * invOneMv F) = 0 := by
        rw [mul_invOneMv hF0, MvPowerSeries.coeff_one, if_neg hd0]
      rw [MvPowerSeries.coeff_mul] at hmul
      have h0mem : ((0 : σ →₀ ℕ), d) ∈ Finset.antidiagonal d := by
        rw [Finset.mem_antidiagonal, zero_add]
      rw [← Finset.add_sum_erase _ _ h0mem] at hmul
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0, one_mul] at hmul
      have hsolve : MvPowerSeries.coeff d (invOneMv F) =
          -(∑ x ∈ (Finset.antidiagonal d).erase (0, d),
            MvPowerSeries.coeff x.1 F * MvPowerSeries.coeff x.2 (invOneMv F)) :=
        eq_neg_of_add_eq_zero_left hmul
      rw [hsolve, norm_neg]
      refine ultrametric_norm_sum_le _ _ zero_le_one fun x hx => ?_
      rw [Finset.mem_erase, Finset.mem_antidiagonal] at hx
      have hx1_ne : x.1 ≠ 0 := by
        intro h1
        apply hx.1
        exact Prod.ext h1 (by simpa [h1] using hx.2)
      have hdeg_add : x.1.degree + x.2.degree = N := by
        rw [← map_add, hx.2, hd]
      have hx1_pos : 0 < x.1.degree := degree_pos_of_ne_zero hx1_ne
      have hx2_lt : x.2.degree < N := by omega
      rw [norm_mul]
      calc ‖MvPowerSeries.coeff x.1 F‖ * ‖MvPowerSeries.coeff x.2 (invOneMv F)‖
          ≤ 1 * 1 := mul_le_mul (hF x.1) (ih _ hx2_lt x.2 rfl) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-! ### Explicit Multivariable Frobenius Substitution `frobSub p F` (`X_i ↦ X_i^p`) -/

section FrobSubDef

variable {R : Type*} [CommSemiring R]

/-- Explicit Frobenius power-substitution `frobSub p F` sending `X_i ↦ X_i^p` on
`MvPowerSeries σ R`: `coeff (p • d) (frobSub p F) = coeff d F`, and `0` for multi-indices not
divisible by `p`. Zero `Algebra` instances or diamonds! -/
def frobSub (p : ℕ) (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  open Classical in
  fun d => if 0 < p ∧ ∀ i, p ∣ d i then
    MvPowerSeries.coeff (d.mapRange (· / p) (Nat.zero_div p)) F
  else 0

lemma nsmul_div_cancel_mapRange {p : ℕ} (hp : 0 < p) (d : σ →₀ ℕ) :
    (p • d).mapRange (· / p) (Nat.zero_div p) = d := by
  ext i
  simp [Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    Nat.mul_div_cancel_left _ hp]

lemma nsmul_mapRange_div_eq {p : ℕ} {d : σ →₀ ℕ} (hd : ∀ i, p ∣ d i) :
    p • d.mapRange (· / p) (Nat.zero_div p) = d := by
  ext i
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
  exact Nat.mul_div_cancel' (hd i)

lemma exists_nsmul_iff_forall_dvd {p : ℕ} (d : σ →₀ ℕ) :
    (∃ e : σ →₀ ℕ, d = p • e) ↔ ∀ i, p ∣ d i := by
  constructor
  · rintro ⟨e, rfl⟩ i
    exact ⟨e i, rfl⟩
  · intro hd
    exact ⟨d.mapRange (· / p) (Nat.zero_div p), (nsmul_mapRange_div_eq hd).symm⟩

@[simp] theorem coeff_frobSub_nsmul {p : ℕ} (hp : 0 < p) (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (p • d) (frobSub p F) = MvPowerSeries.coeff d F := by
  classical
  change (if 0 < p ∧ ∀ i, p ∣ (p • d) i then
    MvPowerSeries.coeff ((p • d).mapRange (· / p) (Nat.zero_div p)) F else 0) = _
  rw [if_pos ⟨hp, fun i => ⟨d i, rfl⟩⟩, nsmul_div_cancel_mapRange hp d]

theorem coeff_frobSub_of_not_nsmul {p : ℕ} (F : MvPowerSeries σ R) {d : σ →₀ ℕ}
    (hd : ¬ ∃ e : σ →₀ ℕ, d = p • e) :
    MvPowerSeries.coeff d (frobSub p F) = 0 := by
  classical
  change (if 0 < p ∧ ∀ i, p ∣ d i then _ else 0) = 0
  rw [if_neg]
  intro h
  exact hd ((exists_nsmul_iff_forall_dvd d).mpr h.2)

open Classical in
theorem coeff_frobSub_eq_ite {p : ℕ} (hp : 0 < p) (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (frobSub p F) =
      if ∀ i, p ∣ d i then MvPowerSeries.coeff (d.mapRange (· / p) (Nat.zero_div p)) F else 0 := by
  change (if 0 < p ∧ ∀ i, p ∣ d i then _ else 0) = _
  simp [hp]

@[simp] theorem constantCoeff_frobSub {p : ℕ} (hp : 0 < p) (F : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (frobSub p F) = MvPowerSeries.constantCoeff F := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : σ →₀ ℕ) = p • (0 : σ →₀ ℕ) by simp,
    coeff_frobSub_nsmul hp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

@[simp] theorem frobSub_zero (p : ℕ) : frobSub p (0 : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  change (if 0 < p ∧ ∀ i, p ∣ d i then _ else 0) = 0
  simp

@[simp] theorem frobSub_one {p : ℕ} (hp : 0 < p) : frobSub p (1 : MvPowerSeries σ R) = 1 := by
  classical
  ext d
  rw [coeff_frobSub_eq_ite hp, MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
  by_cases hd0 : d = 0
  · subst hd0
    simp
  · rw [if_neg hd0]
    split_ifs with hdiv hmap
    · exfalso
      apply hd0
      rw [← nsmul_mapRange_div_eq hdiv, hmap, smul_zero]
    · rfl
    · rfl

theorem frobSub_add {p : ℕ} (hp : 0 < p) (F G : MvPowerSeries σ R) :
    frobSub p (F + G) = frobSub p F + frobSub p G := by
  classical
  ext d
  simp only [map_add, coeff_frobSub_eq_ite hp]
  split_ifs <;> simp

theorem frobSub_mul {p : ℕ} (hp : 0 < p) (F G : MvPowerSeries σ R) :
    frobSub p (F * G) = frobSub p F * frobSub p G := by
  classical
  ext d
  rw [coeff_frobSub_eq_ite hp, MvPowerSeries.coeff_mul]
  split_ifs with hdiv
  · set e : σ →₀ ℕ := d.mapRange (· / p) (Nat.zero_div p)
    have hde : p • e = d := nsmul_mapRange_div_eq hdiv
    rw [MvPowerSeries.coeff_mul]
    symm
    rw [← Finset.sum_filter_of_ne (p := fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => ∀ i, p ∣ x.1 i)
      (fun x _ hx => by
        by_contra h1
        apply hx
        rw [coeff_frobSub_eq_ite hp, if_neg h1, zero_mul])]
    refine Finset.sum_bij (fun x _ =>
      (x.1.mapRange (· / p) (Nat.zero_div p), x.2.mapRange (· / p) (Nat.zero_div p))) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      have h2div : ∀ i, p ∣ x.2 i := fun i => by
        have hsum : x.1 i + x.2 i = d i := congrArg (fun f => f i) hx.1
        exact (Nat.dvd_add_right (hx.2 i)).mp (hsum ▸ hdiv i)
      rw [Finset.mem_antidiagonal]
      ext i
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.mapRange_apply]
      have hmul : p * (x.1 i / p + x.2 i / p) = p * (d i / p) := by
        rw [mul_add, Nat.mul_div_cancel' (hx.2 i), Nat.mul_div_cancel' (h2div i),
          Nat.mul_div_cancel' (hdiv i)]
        exact congrArg (fun f => f i) hx.1
      exact Nat.eq_of_mul_eq_mul_left hp hmul
    · intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
      have h12 : ∀ i, p ∣ x₁.2 i := fun i => by
        have hsum : x₁.1 i + x₁.2 i = d i := congrArg (fun f => f i) hx₁.1
        exact (Nat.dvd_add_right (hx₁.2 i)).mp (hsum ▸ hdiv i)
      have h22 : ∀ i, p ∣ x₂.2 i := fun i => by
        have hsum : x₂.1 i + x₂.2 i = d i := congrArg (fun f => f i) hx₂.1
        exact (Nat.dvd_add_right (hx₂.2 i)).mp (hsum ▸ hdiv i)
      have hfst : x₁.1.mapRange (· / p) (Nat.zero_div p) =
          x₂.1.mapRange (· / p) (Nat.zero_div p) := congrArg Prod.fst heq
      have hsnd : x₁.2.mapRange (· / p) (Nat.zero_div p) =
          x₂.2.mapRange (· / p) (Nat.zero_div p) := congrArg Prod.snd heq
      refine Prod.ext ?_ ?_
      · rw [← nsmul_mapRange_div_eq hx₁.2, hfst, nsmul_mapRange_div_eq hx₂.2]
      · rw [← nsmul_mapRange_div_eq h12, hsnd, nsmul_mapRange_div_eq h22]
    · intro y hy
      rw [Finset.mem_antidiagonal] at hy
      refine ⟨(p • y.1, p • y.2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_antidiagonal]
        refine ⟨?_, fun i => ⟨y.1 i, rfl⟩⟩
        rw [← smul_add, hy, hde]
      · ext i <;> simp [nsmul_div_cancel_mapRange hp]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      have h2div : ∀ i, p ∣ x.2 i := fun i => by
        have hsum : x.1 i + x.2 i = d i := congrArg (fun f => f i) hx.1
        exact (Nat.dvd_add_right (hx.2 i)).mp (hsum ▸ hdiv i)
      rw [coeff_frobSub_eq_ite hp, coeff_frobSub_eq_ite hp, if_pos hx.2, if_pos h2div]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    by_cases h1 : ∀ i, p ∣ x.1 i
    · have h2 : ¬ ∀ i, p ∣ x.2 i := by
        intro h2
        apply hdiv
        intro i
        have hsum : x.1 i + x.2 i = d i := congrArg (fun f => f i) hx
        rw [← hsum]
        exact dvd_add (h1 i) (h2 i)
      rw [coeff_frobSub_eq_ite hp G, if_neg h2, mul_zero]
    · rw [coeff_frobSub_eq_ite hp F, if_neg h1, zero_mul]

/-- `frobSub` packaged as a `RingHom`. -/
def frobSubHom (p : ℕ) (hp : 0 < p) : MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun := frobSub p
  map_one' := frobSub_one hp
  map_mul' := frobSub_mul hp
  map_zero' := frobSub_zero p
  map_add' := frobSub_add hp

@[simp] theorem frobSubHom_apply {p : ℕ} (hp : 0 < p) (F : MvPowerSeries σ R) :
    frobSubHom p hp F = frobSub p F := rfl

@[simp] theorem frobSub_pow {p : ℕ} (hp : 0 < p) (F : MvPowerSeries σ R) (k : ℕ) :
    frobSub p (F ^ k) = (frobSub p F) ^ k :=
  map_pow (frobSubHom p hp) F k

@[simp] theorem frobSub_monomial {p : ℕ} (hp : 0 < p) (d : σ →₀ ℕ) (c : R) :
    frobSub p (MvPowerSeries.monomial d c) = MvPowerSeries.monomial (p • d) c := by
  classical
  ext m
  rw [coeff_frobSub_eq_ite hp, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  by_cases hm : m = p • d
  · subst hm
    rw [if_pos (fun i => ⟨d i, rfl⟩), nsmul_div_cancel_mapRange hp, if_pos rfl, if_pos rfl]
  · rw [if_neg hm]
    split_ifs with hdiv heq
    · exfalso
      apply hm
      rw [← heq, nsmul_mapRange_div_eq hdiv]
    · rfl
    · rfl

@[simp] theorem frobSub_C {p : ℕ} (hp : 0 < p) (c : R) :
    frobSub p (MvPowerSeries.C c : MvPowerSeries σ R) = MvPowerSeries.C c := by
  simpa using frobSub_monomial hp (0 : σ →₀ ℕ) c

@[simp] theorem frobSub_X {p : ℕ} (hp : 0 < p) (i : σ) :
    frobSub p (MvPowerSeries.X i : MvPowerSeries σ R) = (MvPowerSeries.X i) ^ p := by
  have h1 : (MvPowerSeries.X i : MvPowerSeries σ R) = MvPowerSeries.monomial (Finsupp.single i 1) 1 := by
    rfl
  have h2 : ((MvPowerSeries.X i : MvPowerSeries σ R) ^ p) =
      MvPowerSeries.monomial (p • Finsupp.single i 1) 1 := by
    rw [h1, MvPowerSeries.monomial_pow, one_pow]
  rw [h1, frobSub_monomial hp, ← h2, h1]

/-- Twisted crystalline Frobenius `frobMapMv σ_aut p F = F^{σ_aut}(X^p)` as a `RingHom`. -/
def frobMapMv (σ_aut : R →+* R) (p : ℕ) (hp : 0 < p) :
    MvPowerSeries σ R →+* MvPowerSeries σ R :=
  (MvPowerSeries.map σ_aut).comp (frobSubHom p hp)

@[simp] theorem frobMapMv_id {p : ℕ} (hp : 0 < p) (F : MvPowerSeries σ R) :
    frobMapMv (RingHom.id R) p hp F = frobSub p F := by
  ext d
  simp [frobMapMv]

@[simp] theorem coeff_frobMapMv_nsmul (σ_aut : R →+* R) {p : ℕ} (hp : 0 < p)
    (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (p • d) (frobMapMv σ_aut p hp F) = σ_aut (MvPowerSeries.coeff d F) := by
  simp [frobMapMv, coeff_frobSub_nsmul hp]

open Classical in
theorem coeff_frobMapMv_eq_ite (σ_aut : R →+* R) {p : ℕ} (hp : 0 < p)
    (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (frobMapMv σ_aut p hp F) =
      if ∀ i, p ∣ d i then
        σ_aut (MvPowerSeries.coeff (d.mapRange (· / p) (Nat.zero_div p)) F)
      else 0 := by
  simp only [frobMapMv, RingHom.comp_apply, MvPowerSeries.coeff_map, frobSubHom_apply,
    coeff_frobSub_eq_ite hp]
  split_ifs <;> simp

@[simp] theorem frobMapMv_monomial (σ_aut : R →+* R) {p : ℕ} (hp : 0 < p)
    (d : σ →₀ ℕ) (c : R) :
    frobMapMv σ_aut p hp (MvPowerSeries.monomial d c) =
      MvPowerSeries.monomial (p • d) (σ_aut c) := by
  simp [frobMapMv, frobSub_monomial hp]

theorem frobSub_unit_eq_frobPS {p : ℕ} (hp : 0 < p) (F : PowerSeries R) :
    (frobSub p (F : MvPowerSeries Unit R) : PowerSeries R) = frobPS p hp F := by
  classical
  ext n
  rw [coeff_frobPS]
  change MvPowerSeries.coeff (Finsupp.single () n) (frobSub p (F : MvPowerSeries Unit R)) = _
  rw [coeff_frobSub_eq_ite hp]
  have hiff : (∀ i : Unit, p ∣ Finsupp.single () n i) ↔ p ∣ n := by
    constructor
    · intro h; simpa using h ()
    · intro h i; cases i; simpa using h
  by_cases hdiv : p ∣ n
  · rw [if_pos (hiff.mpr hdiv), if_pos hdiv]
    have hmap : (Finsupp.single () n).mapRange (· / p) (Nat.zero_div p) =
        Finsupp.single () (n / p) := by
      ext; simp
    rw [hmap]
    rfl
  · rw [if_neg (mt hiff.mp hdiv), if_neg hdiv]

end FrobSubDef

end MvPowerSeriesCore

/-! ## Section 2: Unconditional Multivariable Dwork Integrality Lemma (`dwork_lemma_mvPowerSeries`) -/

section MultivarDworkLemma

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Finite downward-closed set `{m : σ →₀ ℕ | m ≤ n}` constructed directly from
`Finset.antidiagonal n` — requires NO `[Finite σ]` assumption! -/
def downSet (n : σ →₀ ℕ) : Finset (σ →₀ ℕ) :=
  open Classical in
  (Finset.antidiagonal n).image Prod.fst

omit [NormedField K] [IsUltrametricDist K] in
lemma mem_downSet_iff {n m : σ →₀ ℕ} : m ∈ downSet n ↔ m ≤ n := by
  classical
  unfold downSet
  simp only [Finset.mem_image, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact hab ▸ le_self_add
  · intro hmn
    refine ⟨(m, n - m), add_tsub_cancel_of_le hmn, rfl⟩

/-- Finite truncation of `F` onto the downward-closed cone `{m | m ≤ n}`. -/
def truncLe (n : σ →₀ ℕ) (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  ∑ m ∈ downSet n, MvPowerSeries.monomial m (MvPowerSeries.coeff m F)

omit [IsUltrametricDist K] in
@[simp] theorem coeff_truncLe (n : σ →₀ ℕ) (F : MvPowerSeries σ K) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (truncLe n F) = if m ≤ n then MvPowerSeries.coeff m F else 0 := by
  classical
  unfold truncLe
  rw [map_sum]
  simp only [MvPowerSeries.coeff_monomial]
  rw [Finset.sum_ite_eq]
  simp [mem_downSet_iff]

omit [IsUltrametricDist K] in
lemma coeff_pow_eq_of_coeff_eq_le {F G : MvPowerSeries σ K} {n : σ →₀ ℕ}
    (h : ∀ m ≤ n, MvPowerSeries.coeff m F = MvPowerSeries.coeff m G) (k : ℕ) :
    ∀ m ≤ n, MvPowerSeries.coeff m (F ^ k) = MvPowerSeries.coeff m (G ^ k) := by
  classical
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    intro m hm
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    have h1 : x.1 ≤ n := le_trans (hx ▸ le_self_add) hm
    have h2 : x.2 ≤ n := le_trans (hx ▸ le_add_self) hm
    rw [ih x.1 h1, h x.2 h2]

/-- Binomial Frobenius congruence on finite sums of integral monomials (via `p ∣ Nat.choose p j`
for `0 < j < p`). -/
lemma frobMapMv_pow_sub_finset_norm_le {p : ℕ} (hp : p.Prime)
    (σ_aut : K →+* K) (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ_aut c‖ ≤ ‖(p : K)‖)
    (c : (σ →₀ ℕ) → K) (hc : ∀ m, ‖c m‖ ≤ 1) (s : Finset (σ →₀ ℕ)) :
    IsIntegralMv (∑ m ∈ s, MvPowerSeries.monomial m (c m)) ∧
    CoeffNormLeMv ‖(p : K)‖
      ((∑ m ∈ s, MvPowerSeries.monomial m (c m)) ^ p -
        frobMapMv σ_aut p hp.pos (∑ m ∈ s, MvPowerSeries.monomial m (c m))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using isIntegralMv_zero, ?_⟩
    intro d
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    set A := MvPowerSeries.monomial a (c a)
    set B := ∑ m ∈ s, MvPowerSeries.monomial m (c m)
    have hAint : IsIntegralMv A := isIntegralMv_monomial a (hc a)
    have hBint : IsIntegralMv B := ih.1
    refine ⟨isIntegralMv_add hAint hBint, ?_⟩
    have hsplit : (A + B) ^ p - frobMapMv σ_aut p hp.pos (A + B) =
        ((A + B) ^ p - A ^ p - B ^ p) + (A ^ p - frobMapMv σ_aut p hp.pos A) +
          (B ^ p - frobMapMv σ_aut p hp.pos B) := by
      rw [map_add]
      ring
    rw [hsplit]
    refine coeffNormLeMv_add (coeffNormLeMv_add ?_ ?_) ih.2
    · -- Cross binomial terms `∑_{0 < j < p} choose(p, j) * A^j * B^(p-j)` have norm `≤ ‖p‖`!
      have hbin : (A + B) ^ p - A ^ p - B ^ p =
          ∑ j ∈ Finset.Ioo 0 p, A ^ j * B ^ (p - j) * (p.choose j : MvPowerSeries σ K) := by
        rw [add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, mul_one,
          Nat.cast_one, mul_one]
        have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
        rw [← Finset.add_sum_erase _ _ h0]
        simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
        have herase : (Finset.range p).erase 0 = Finset.Ioo 0 p := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]
          omega
        rw [herase]
        ring
      rw [hbin]
      refine coeffNormLeMv_sum _ (norm_nonneg _) fun j hj => ?_
      rw [Finset.mem_Ioo] at hj
      have hdvd : p ∣ p.choose j := hp.dvd_choose_self hj.1.ne' hj.2
      have hch : ‖((p.choose j : ℕ) : K)‖ ≤ ‖(p : K)‖ := by
        obtain ⟨q, hq⟩ := hdvd
        rw [hq, Nat.cast_mul, norm_mul]
        calc ‖(p : K)‖ * ‖(q : K)‖ ≤ ‖(p : K)‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_natCast_le_one q) (norm_nonneg _)
          _ = ‖(p : K)‖ := mul_one _
      intro d
      have hint := isIntegralMv_mul (isIntegralMv_pow hAint j) (isIntegralMv_pow hBint (p - j)) d
      rw [show (p.choose j : MvPowerSeries σ K) = MvPowerSeries.C ((p.choose j : ℕ) : K) by simp,
        mul_comm, MvPowerSeries.coeff_C_mul, norm_mul]
      calc ‖((p.choose j : ℕ) : K)‖ * ‖MvPowerSeries.coeff d (A ^ j * B ^ (p - j))‖
          ≤ ‖(p : K)‖ * 1 := mul_le_mul hch hint (norm_nonneg _) (norm_nonneg _)
        _ = ‖(p : K)‖ := mul_one _
    · -- Single monomial term: `(c_a X^a)^p - σ_aut(c_a) X^{p a} = (c_a^p - σ_aut c_a) X^{p a}`
      have hmon : A ^ p - frobMapMv σ_aut p hp.pos A =
          MvPowerSeries.monomial (p • a) (c a ^ p - σ_aut (c a)) := by
        rw [show A = MvPowerSeries.monomial a (c a) from rfl, MvPowerSeries.monomial_pow,
          frobMapMv_monomial, map_sub]
      rw [hmon]
      exact coeffNormLeMv_monomial (norm_nonneg _) (p • a) (hflt (c a) (hc a))

/-- **Multivariable Frobenius Congruence (Arbitrary Index Type `σ`)**:
For ANY integral `F ∈ O_K[[X_i]]` and Frobenius lift `σ_aut` (`‖c^p - σ_aut c‖ ≤ ‖p‖` on `O_K`),
`F(X)^p ≡ F^{σ_aut}(X^p) (mod p O_K[[X_i]])`. -/
theorem frobMapMv_pow_sub_norm_le {p : ℕ} (hp : p.Prime)
    (σ_aut : K →+* K) (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ_aut c‖ ≤ ‖(p : K)‖)
    {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    CoeffNormLeMv ‖(p : K)‖ (F ^ p - frobMapMv σ_aut p hp.pos F) := by
  intro d
  have hpow : MvPowerSeries.coeff d (F ^ p) = MvPowerSeries.coeff d ((truncLe d F) ^ p) :=
    coeff_pow_eq_of_coeff_eq_le (fun m hm => by rw [coeff_truncLe, if_pos hm]) p d le_rfl
  have hfrob : MvPowerSeries.coeff d (frobMapMv σ_aut p hp.pos F) =
      MvPowerSeries.coeff d (frobMapMv σ_aut p hp.pos (truncLe d F)) := by
    classical
    rw [coeff_frobMapMv_eq_ite, coeff_frobMapMv_eq_ite]
    split_ifs with hdiv
    · have hle : d.mapRange (· / p) (Nat.zero_div p) ≤ d := fun i => Nat.div_le_self (d i) p
      rw [coeff_truncLe, if_pos hle]
    · rfl
  rw [map_sub, hpow, hfrob, ← map_sub]
  exact (frobMapMv_pow_sub_finset_norm_le hp σ_aut hflt (fun m => MvPowerSeries.coeff m F) hF
    (downSet d)).2 d

omit [IsUltrametricDist K] in
/-- Degree-`N` splitting identity for `F ^ p` in arbitrary variables `σ`:
if `constantCoeff F = 1`, `N ≥ 1`, and `F₀ := truncBelow N F`, then:
1. `coeff m (F ^ p) = coeff m (F₀ ^ p)` for all `m` with `m.degree < N`, and
2. `coeff d (F ^ p) = coeff d (F₀ ^ p) + p * coeff d F` for all `d` with `d.degree = N`. -/
lemma coeff_pow_prime_split_mv {p : ℕ} (hp : p.Prime) {F : MvPowerSeries σ K}
    (hF0 : MvPowerSeries.constantCoeff F = 1) {N : ℕ} (hN : 1 ≤ N) :
    (∀ m : σ →₀ ℕ, m.degree < N →
      MvPowerSeries.coeff m (F ^ p) = MvPowerSeries.coeff m ((truncBelow N F) ^ p)) ∧
    (∀ d : σ →₀ ℕ, d.degree = N →
      MvPowerSeries.coeff d (F ^ p) =
        MvPowerSeries.coeff d ((truncBelow N F) ^ p) + (p : K) * MvPowerSeries.coeff d F) := by
  classical
  set F₀ := truncBelow N F
  set H := F - F₀
  have hHlow : Low N H := low_sub_truncBelow N F
  have hF_eq : F = F₀ + H := (add_sub_cancel F₀ F).symm
  have hcf0 : MvPowerSeries.constantCoeff F₀ = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_truncBelow,
      if_pos (by simp; omega), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0]
  have hexp : F ^ p = F₀ ^ p + (p : MvPowerSeries σ K) * F₀ ^ (p - 1) * H +
      ∑ j ∈ Finset.Icc 2 p, H ^ j * F₀ ^ (p - j) * (p.choose j : MvPowerSeries σ K) := by
    rw [hF_eq, add_comm F₀ H, add_pow]
    have hp2 : 2 ≤ p := hp.two_le
    have hsplit : Finset.range (p + 1) = {0, 1} ∪ Finset.Icc 2 p := by
      ext j
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Icc]
      omega
    have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 p) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj1
      simp only [Finset.mem_Icc] at hj2
      omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      pow_one, Nat.choose_one_right]
    ring
  have htail_zero : ∀ m : σ →₀ ℕ, m.degree ≤ N →
      MvPowerSeries.coeff m
        (∑ j ∈ Finset.Icc 2 p, H ^ j * F₀ ^ (p - j) * (p.choose j : MvPowerSeries σ K)) = 0 := by
    intro m hm
    rw [map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hlow_j : Low (j * N) (H ^ j) := low_pow hHlow j
    have hlow_prod : Low (j * N + 0) (H ^ j * (F₀ ^ (p - j) * (p.choose j : MvPowerSeries σ K))) :=
      low_mul hlow_j (fun _ h => by omega)
    rw [mul_assoc]
    exact hlow_prod m (by nlinarith)
  have hmid : ∀ m : σ →₀ ℕ, m.degree ≤ N →
      MvPowerSeries.coeff m ((p : MvPowerSeries σ K) * F₀ ^ (p - 1) * H) =
        if m.degree = N then (p : K) * MvPowerSeries.coeff m F else 0 := by
    intro m hm
    rw [show (p : MvPowerSeries σ K) = MvPowerSeries.C (p : K) by simp, mul_assoc,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul]
    split_ifs with heq
    · have h0mem : ((0 : σ →₀ ℕ), m) ∈ Finset.antidiagonal m := by
        rw [Finset.mem_antidiagonal, zero_add]
      rw [Finset.sum_eq_single ((0 : σ →₀ ℕ), m)]
      · dsimp only
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hcf0, one_pow, one_mul]
        rw [show H = F - F₀ from rfl, map_sub, coeff_truncBelow, if_neg (by omega), sub_zero]
      · intro x hx hne
        rw [Finset.mem_antidiagonal] at hx
        have hx1_ne : x.1 ≠ 0 := by
          intro h1; apply hne; exact Prod.ext h1 (by simpa [h1] using hx)
        have hx1_pos : 0 < x.1.degree := degree_pos_of_ne_zero hx1_ne
        have hdeg_add : x.1.degree + x.2.degree = N := by rw [← map_add, hx, heq]
        rw [hHlow x.2 (by omega), mul_zero]
      · intro h; exact absurd h0mem h
    · have hlt : m.degree < N := by omega
      have hzero : ∑ x ∈ Finset.antidiagonal m,
          MvPowerSeries.coeff x.1 (F₀ ^ (p - 1)) * MvPowerSeries.coeff x.2 H = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        have hdeg_add : x.1.degree + x.2.degree = m.degree := by rw [← map_add, hx]
        rw [hHlow x.2 (by omega), mul_zero]
      rw [hzero, mul_zero]
  constructor
  · intro m hm
    rw [hexp, map_add, map_add, htail_zero m hm.le, add_zero, hmid m hm.le, if_neg hm.ne, add_zero]
  · intro d hd
    rw [hexp, map_add, map_add, htail_zero d hd.le, add_zero, hmid d hd.le, if_pos hd]

/-- **General Multivariable Dieudonné–Dwork Lemma (`dieudonne_dwork_mv_iff`)**:
For ANY index type `σ`, ultrametric normed field `K` of characteristic `0`, prime `p`, Frobenius
lift `σ_aut : K →+* K` (`‖c^p - σ_aut c‖ ≤ ‖p‖` on `O_K`), and `F : MvPowerSeries σ K` with
`constantCoeff F = 1`:
`F ∈ O_K[[X_i]]  ↔  F^{σ_aut}(X^p) / F(X)^p ∈ 1 + p O_K[[X_i]]`! -/
theorem dieudonne_dwork_mv_iff [CharZero K] {p : ℕ} (hp : p.Prime)
    (σ_aut : K →+* K) (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ_aut c‖ ≤ ‖(p : K)‖)
    {F : MvPowerSeries σ K} (hF0 : MvPowerSeries.constantCoeff F = 1) :
    IsIntegralMv F ↔ CongOneModPMv p (frobMapMv σ_aut p hp.pos F * (invOneMv F) ^ p) := by
  classical
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  constructor
  · intro hF
    set G := frobMapMv σ_aut p hp.pos F * (invOneMv F) ^ p
    have hG0 : MvPowerSeries.constantCoeff G = 1 := by
      simp [G, frobMapMv, constantCoeff_invOneMv hF0, hF0, constantCoeff_frobSub hp.pos]
    refine ⟨hG0, fun d hd => ?_⟩
    have hdiff : G - 1 = (frobMapMv σ_aut p hp.pos F - F ^ p) * (invOneMv F) ^ p := by
      rw [show G = frobMapMv σ_aut p hp.pos F * (invOneMv F) ^ p from rfl,
        sub_mul, ← mul_pow, mul_invOneMv hF0, one_pow]
    have hcong : CoeffNormLeMv ‖(p : K)‖ (frobMapMv σ_aut p hp.pos F - F ^ p) := by
      rw [show frobMapMv σ_aut p hp.pos F - F ^ p = -(F ^ p - frobMapMv σ_aut p hp.pos F) by ring]
      exact coeffNormLeMv_neg (frobMapMv_pow_sub_norm_le hp σ_aut hflt hF)
    have hinvp : IsIntegralMv ((invOneMv F) ^ p) :=
      isIntegralMv_pow (isIntegralMv_invOneMv hF0 hF) p
    have hprod := coeffNormLeMv_mul hpi0.le zero_le_one hcong hinvp d
    rw [mul_one, ← hdiff, map_sub, MvPowerSeries.coeff_one, if_neg hd, sub_zero] at hprod
    exact hprod
  · intro hG
    set G := frobMapMv σ_aut p hp.pos F * (invOneMv F) ^ p
    have heq : frobMapMv σ_aut p hp.pos F = G * F ^ p := by
      rw [show G = frobMapMv σ_aut p hp.pos F * (invOneMv F) ^ p from rfl,
        mul_assoc, ← mul_pow, invOneMv_mul hF0, one_pow, mul_one]
    suffices H : ∀ N : ℕ, ∀ d : σ →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d F‖ ≤ 1 from
      fun d => H _ d rfl
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro d hd
      rcases N with _ | n
      · have hd0 : d = 0 := (degree_eq_zero_iff d).mp hd
        subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0, norm_one]
      · set M := n + 1
        set F₀ := truncBelow M F
        have hF₀_int : IsIntegralMv F₀ := fun m => by
          rw [coeff_truncBelow]
          split_ifs with hm
          · exact ih _ hm m rfl
          · simp
        have hsplit := coeff_pow_prime_split_mv hp hF0 (by omega : 1 ≤ M)
        have hfrob_eq : MvPowerSeries.coeff d (frobMapMv σ_aut p hp.pos F) =
            MvPowerSeries.coeff d (frobMapMv σ_aut p hp.pos F₀) := by
          rw [coeff_frobMapMv_eq_ite, coeff_frobMapMv_eq_ite]
          split_ifs with hdiv
          · set e := d.mapRange (· / p) (Nat.zero_div p)
            have hde : p • e = d := nsmul_mapRange_div_eq hdiv
            have hdeg_e : p * e.degree = M := by
              rw [← hd, ← hde, map_nsmul, smul_eq_mul]
            have hMpos : 0 < M := Nat.succ_pos n
            have hlt : e.degree < M := by nlinarith [hp.two_le, hMpos]
            rw [coeff_truncBelow, if_pos hlt]
          · rfl
        have hmul_eq : MvPowerSeries.coeff d (G * F ^ p) =
            MvPowerSeries.coeff d (G * F₀ ^ p) + (p : K) * MvPowerSeries.coeff d F := by
          rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
          have h0mem : ((0 : σ →₀ ℕ), d) ∈ Finset.antidiagonal d := by
            rw [Finset.mem_antidiagonal, zero_add]
          rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ h0mem]
          simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG.1, one_mul]
          have hsum_eq : ∑ x ∈ (Finset.antidiagonal d).erase (0, d),
              MvPowerSeries.coeff x.1 G * MvPowerSeries.coeff x.2 (F ^ p) =
              ∑ x ∈ (Finset.antidiagonal d).erase (0, d),
              MvPowerSeries.coeff x.1 G * MvPowerSeries.coeff x.2 (F₀ ^ p) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [Finset.mem_erase, Finset.mem_antidiagonal] at hx
            have hx1_ne : x.1 ≠ 0 := by
              intro h1; apply hx.1; exact Prod.ext h1 (by simpa [h1] using hx.2)
            have hx1_pos : 0 < x.1.degree := degree_pos_of_ne_zero hx1_ne
            have hdeg_add : x.1.degree + x.2.degree = M := by rw [← map_add, hx.2, hd]
            rw [hsplit.1 x.2 (by omega)]
          rw [hsum_eq, hsplit.2 d hd]
          ring
        have hpa : (p : K) * MvPowerSeries.coeff d F =
            MvPowerSeries.coeff d (frobMapMv σ_aut p hp.pos F₀ - F₀ ^ p) -
              MvPowerSeries.coeff d ((G - 1) * F₀ ^ p) := by
          have hc := congrArg (MvPowerSeries.coeff d) heq
          rw [hfrob_eq, hmul_eq] at hc
          have hsub : frobMapMv σ_aut p hp.pos F₀ - F₀ ^ p - (G - 1) * F₀ ^ p =
              frobMapMv σ_aut p hp.pos F₀ - G * F₀ ^ p := by ring
          rw [← map_sub, hsub, map_sub]
          linear_combination -hc
        have hterm1 : ‖MvPowerSeries.coeff d (frobMapMv σ_aut p hp.pos F₀ - F₀ ^ p)‖ ≤ ‖(p : K)‖ := by
          rw [show frobMapMv σ_aut p hp.pos F₀ - F₀ ^ p =
            -(F₀ ^ p - frobMapMv σ_aut p hp.pos F₀) by ring, map_neg, norm_neg]
          exact frobMapMv_pow_sub_norm_le hp σ_aut hflt hF₀_int d
        have hG1 : CoeffNormLeMv ‖(p : K)‖ (G - 1) := fun m => by
          rw [map_sub, MvPowerSeries.coeff_one]
          by_cases hm0 : m = 0
          · subst hm0
            rw [if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG.1, sub_self,
              norm_zero]
            exact hpi0.le
          · rw [if_neg hm0, sub_zero]
            exact hG.2 m hm0
        have hterm2 : ‖MvPowerSeries.coeff d ((G - 1) * F₀ ^ p)‖ ≤ ‖(p : K)‖ := by
          simpa using coeffNormLeMv_mul hpi0.le zero_le_one hG1 (isIntegralMv_pow hF₀_int p) d
        have hbd : ‖(p : K)‖ * ‖MvPowerSeries.coeff d F‖ ≤ ‖(p : K)‖ := by
          rw [← norm_mul, hpa, sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hterm1 ?_)
          rwa [norm_neg]
        exact le_of_mul_le_mul_left (by simpa using hbd) hpi0

/-- **Unconditional Multivariable Dwork Integrality Lemma over `ℚ_[p]` (`dwork_lemma_mvPowerSeries`)**:
For ANY index type `σ`, prime `p`, and `F : MvPowerSeries σ ℚ_[p]` with `constantCoeff F = 1`:
`(∀ d, ‖coeff d F‖ ≤ 1) ↔ (∀ d ≠ 0, ‖coeff d (frobSub p F * (invOneMv F) ^ p)‖ ≤ ‖(p : ℚ_[p])‖)`! -/
theorem dwork_lemma_mvPowerSeries (p : ℕ) [Fact p.Prime] {F : MvPowerSeries σ ℚ_[p]}
    (hF0 : MvPowerSeries.constantCoeff F = 1) :
    (∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ 1) ↔
      (∀ d : σ →₀ ℕ, d ≠ 0 →
        ‖MvPowerSeries.coeff d (frobSub p F * (invOneMv F) ^ p)‖ ≤ ‖(p : ℚ_[p])‖) := by
  have hp : p.Prime := Fact.out
  have h := dieudonne_dwork_mv_iff (σ := σ) (K := ℚ_[p]) hp (RingHom.id ℚ_[p])
    (fun c hc => padic_pow_prime_sub_le p hc) hF0
  simp only [IsIntegralMv, CongOneModPMv, frobMapMv_id] at h
  have hG0 : MvPowerSeries.constantCoeff (frobSub p F * (invOneMv F) ^ p) = 1 := by
    rw [map_mul, map_pow, constantCoeff_frobSub hp.pos, constantCoeff_invOneMv hF0, hF0, one_pow,
      one_mul]
  rw [h]
  exact ⟨fun h1 => h1.2, fun h2 => ⟨hG0, h2⟩⟩

/-- Division-free form of `dwork_lemma_mvPowerSeries`:
`F ∈ ℤ_[p][[X_i]] ↔ ∃ G ∈ 1 + p ℤ_[p][[X_i]], frobSub p F = G * F ^ p`. -/
theorem dwork_lemma_mvPowerSeries_exists (p : ℕ) [Fact p.Prime] {F : MvPowerSeries σ ℚ_[p]}
    (hF0 : MvPowerSeries.constantCoeff F = 1) :
    IsIntegralMv F ↔
      ∃ G : MvPowerSeries σ ℚ_[p], CongOneModPMv p G ∧ frobSub p F = G * F ^ p := by
  have hp : p.Prime := Fact.out
  rw [IsIntegralMv, dwork_lemma_mvPowerSeries p hF0]
  constructor
  · intro hG
    have hG0 : MvPowerSeries.constantCoeff (frobSub p F * (invOneMv F) ^ p) = 1 := by
      rw [map_mul, map_pow, constantCoeff_frobSub hp.pos, constantCoeff_invOneMv hF0, hF0, one_pow,
        one_mul]
    refine ⟨frobSub p F * (invOneMv F) ^ p, ⟨hG0, hG⟩, ?_⟩
    rw [mul_assoc, ← mul_pow, invOneMv_mul hF0, one_pow, mul_one]
  · rintro ⟨G, hG, heq⟩
    have hGeq : frobSub p F * (invOneMv F) ^ p = G := by
      rw [heq, mul_assoc, ← mul_pow, mul_invOneMv hF0, one_pow, mul_one]
    rw [hGeq]
    exact hG.2

end MultivarDworkLemma

/-! ## Section 3: Artin–Hasse Exponential & Honda / Lubin–Tate Formal Group Integrality -/

section ArtinHasseAndFormalGroups

/-- **Artin–Hasse Exponential** `E_p(X) = exp(∑_{m ≥ 0} X^{p^m} / p^m) ∈ ℚ_[p][[X]]`. -/
def artinHasseExp (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] :=
  Stage2DworkExp.artinHasseExp ℚ_[p] p

/-- **Artin–Hasse Integrality (`artinHasseExp_isIntegral`)**:
EVERY coefficient of `E_p(X)` lies in `ℤ_[p]` (`‖coeff n (artinHasseExp p)‖ ≤ 1`),
deduced immediately as a corollary of `dwork_lemma_mvPowerSeries` on `σ = Unit`! -/
theorem artinHasseExp_isIntegral (p : ℕ) [Fact p.Prime] :
    ∀ n : ℕ, ‖PowerSeries.coeff n (artinHasseExp p)‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hlt : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hF0 : MvPowerSeries.constantCoeff (artinHasseExp p : MvPowerSeries Unit ℚ_[p]) = 1 :=
    constantCoeff_artinHasseExp hp
  have hint := (dwork_lemma_mvPowerSeries (σ := Unit) p hF0).mpr ?_
  · intro n; exact hint (Finsupp.single () n)
  · intro d hd
    have hEq : frobSub p (artinHasseExp p : MvPowerSeries Unit ℚ_[p]) *
        (invOneMv (artinHasseExp p : MvPowerSeries Unit ℚ_[p])) ^ p =
        (expPS (PowerSeries.C (-(p : ℚ_[p])) * PowerSeries.X) : MvPowerSeries Unit ℚ_[p]) := by
      change (frobSub p (artinHasseExp p : MvPowerSeries Unit ℚ_[p]) : PowerSeries ℚ_[p]) *
        (invOnePS (artinHasseExp p)) ^ p = _
      rw [frobSub_unit_eq_frobPS hp.pos]
      exact artinHasseExp_frob_ratio hp
    rw [hEq]
    have hd_pos : 1 ≤ d () := by
      by_contra h0
      have hd0 : d () = 0 := by omega
      apply hd; ext; simpa using hd0
    have hsingle : d = Finsupp.single () (d ()) := by ext; simp
    rw [hsingle]
    exact (congOneModP_expPS_neg_p_mul_X hp hlt).2 (d ()) hd_pos

/-! ### Explicit Finite-Sum Substitution & Degree-Recursive Inversion for Formal Groups -/

section FormalGroupSubst

variable {σ K : Type*} [NormedField K]

/-- Finite-sum coefficient formula for univariate-into-multivariate formal substitution
`PowerSeries.subst h f` when `constantCoeff h = 0`: only powers `k ≤ d.degree` contribute! -/
lemma coeff_subst_eq_sum {h : MvPowerSeries σ K} (hh0 : MvPowerSeries.constantCoeff h = 0)
    (f : PowerSeries K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.subst h f) =
      ∑ k ∈ Finset.range (d.degree + 1),
        PowerSeries.coeff k f * MvPowerSeries.coeff d (h ^ k) := by
  classical
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero hh0
  have hlow1 : Low 1 h := low_one_of_constantCoeff_zero hh0
  rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.range (d.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hge
    apply hk
    have hpow : Low (k * 1) (h ^ k) := low_pow hlow1 k
    rw [mul_one] at hpow
    rw [hpow d (by omega), smul_zero]

lemma constantCoeff_subst_of_zero {h : MvPowerSeries σ K}
    (hh0 : MvPowerSeries.constantCoeff h = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst h f) = PowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum hh0 f 0]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

lemma subst_sub_left {h : MvPowerSeries σ K} (hh0 : MvPowerSeries.constantCoeff h = 0)
    (f₁ f₂ : PowerSeries K) :
    PowerSeries.subst h (f₁ - f₂) = PowerSeries.subst h f₁ - PowerSeries.subst h f₂ := by
  ext d
  rw [map_sub, coeff_subst_eq_sum hh0, coeff_subst_eq_sum hh0, coeff_subst_eq_sum hh0,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => by rw [map_sub, sub_mul]

lemma subst_smul_left {h : MvPowerSeries σ K} (hh0 : MvPowerSeries.constantCoeff h = 0)
    (c : K) (f : PowerSeries K) :
    PowerSeries.subst h (c • f) = c • PowerSeries.subst h f := by
  ext d
  rw [MvPowerSeries.coeff_smul, coeff_subst_eq_sum hh0, coeff_subst_eq_sum hh0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by rw [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc]

/-- Commutation of `frobSub p` with formal substitution:
`frobSub p (f(h)) = f(frobSub p h)`. -/
theorem frobSub_subst {p : ℕ} (hp : 0 < p) {h : MvPowerSeries σ K}
    (hh0 : MvPowerSeries.constantCoeff h = 0) (f : PowerSeries K) :
    frobSub p (PowerSeries.subst h f) = PowerSeries.subst (frobSub p h) f := by
  classical
  have hfh0 : MvPowerSeries.constantCoeff (frobSub p h) = 0 := by
    rw [constantCoeff_frobSub hp, hh0]
  have hlow1 : Low 1 h := low_one_of_constantCoeff_zero hh0
  ext d
  rw [coeff_frobSub_eq_ite hp, coeff_subst_eq_sum hfh0]
  split_ifs with hdiv
  · set e := d.mapRange (· / p) (Nat.zero_div p)
    have hde : p • e = d := nsmul_mapRange_div_eq hdiv
    have he_le : e.degree ≤ d.degree := by
      rw [← hde, map_nsmul, smul_eq_mul]
      exact Nat.le_mul_of_pos_left e.degree hp
    rw [coeff_subst_eq_sum hh0 f e]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ he_le))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← frobSub_pow hp, coeff_frobSub_eq_ite hp, if_pos hdiv]
    · intro k _ hk
      rw [Finset.mem_range] at hk
      rw [← frobSub_pow hp, coeff_frobSub_eq_ite hp, if_pos hdiv]
      have hpow : Low (k * 1) (h ^ k) := low_pow hlow1 k
      rw [mul_one] at hpow
      rw [hpow e (by omega), mul_zero]
  · symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← frobSub_pow hp, coeff_frobSub_eq_ite hp, if_neg hdiv, mul_zero]

/-- Substitution into `frobSub p f`:
`PowerSeries.subst h (frobSub p f) = PowerSeries.subst (h ^ p) f`. -/
theorem subst_frobSub {p : ℕ} (hp : 0 < p) {h : MvPowerSeries σ K}
    (hh0 : MvPowerSeries.constantCoeff h = 0) (f : PowerSeries K) :
    PowerSeries.subst h (frobSub p (f : MvPowerSeries Unit K) : PowerSeries K) =
      PowerSeries.subst (h ^ p) f := by
  classical
  have hhp0 : MvPowerSeries.constantCoeff (h ^ p) = 0 := by
    rw [map_pow, hh0, zero_pow hp.ne']
  have hlow1 : Low 1 h := low_one_of_constantCoeff_zero hh0
  ext d
  rw [frobSub_unit_eq_frobPS hp, coeff_subst_eq_sum hh0, coeff_subst_eq_sum hhp0]
  simp_rw [coeff_frobPS]
  rw [← Finset.sum_filter_of_ne (p := fun k : ℕ => p ∣ k)
    (fun k _ hk => by by_contra hnd; exact hk (by simp [hnd]))]
  symm
  rw [← Finset.sum_filter_of_ne (p := fun k : ℕ => p * k ≤ d.degree)
    (fun k _ hk => by
      by_contra hgt
      push Not at hgt
      apply hk
      rw [← pow_mul]
      have hpow : Low (p * k * 1) (h ^ (p * k)) := low_pow hlow1 (p * k)
      rw [mul_one] at hpow
      rw [hpow d (by omega), mul_zero])]
  symm
  refine Finset.sum_bij (fun k _ => k / p) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨Nat.lt_succ_of_le (Nat.div_le_self k p |>.trans (Nat.le_of_lt_succ hk.1)), ?_⟩
    rw [Nat.mul_div_cancel' hk.2]
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_filter] at hk₁ hk₂
    rw [← Nat.mul_div_cancel' hk₁.2, heq, Nat.mul_div_cancel' hk₂.2]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨p * m, ?_, Nat.mul_div_cancel_left m hp⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hm.2, dvd_mul_right p m⟩
  · intro k hk
    simp only [Finset.mem_filter] at hk
    rw [if_pos hk.2, ← pow_mul, Nat.mul_div_cancel' hk.2]

/-- Difference of `k`-th powers (`k ≥ 2`) of two zero-constant-term series agreeing below degree `N`
vanishes up to degree `N` (i.e., has `Low (N + 1)`). -/
lemma low_pow_sub_of_low {h₁ h₂ : MvPowerSeries σ K} {N : ℕ}
    (h1 : Low 1 h₁) (h2 : Low 1 h₂) (hdiff : Low N (h₁ - h₂)) {k : ℕ} (hk : 2 ≤ k) :
    Low (N + 1) (h₁ ^ k - h₂ ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero =>
    have heq : h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) := by ring
    rw [add_zero, heq]
    exact low_mul hdiff (low_add h1 h2)
  | succ m ih =>
    have heq : h₁ ^ (2 + (m + 1)) - h₂ ^ (2 + (m + 1)) =
        (h₁ ^ (2 + m) - h₂ ^ (2 + m)) * h₁ + h₂ ^ (2 + m) * (h₁ - h₂) := by ring
    rw [heq]
    refine low_add ?_ ?_
    · exact low_mono (by omega : N + 1 ≤ (N + 1) + 1) (low_mul (ih (by omega)) h1)
    · have hp2 : Low ((2 + m) * 1) (h₂ ^ (2 + m)) := low_pow h2 (2 + m)
      exact low_mono (by omega : N + 1 ≤ (2 + m) * 1 + N) (low_mul hp2 hdiff)

/-- Linearization of `PowerSeries.subst h f` at degree `N` when `h - h₀` has `Low N`:
`coeff d (f(h)) = coeff d (f(h₀)) + coeff 1 f * coeff d (h - h₀)` for `d.degree = N ≥ 1`,
and `coeff m (f(h)) = coeff m (f(h₀))` for `m.degree < N`. -/
lemma coeff_subst_split {h h₀ : MvPowerSeries σ K} {N : ℕ} (hN : 1 ≤ N)
    (hh0 : MvPowerSeries.constantCoeff h = 0) (hh₀0 : MvPowerSeries.constantCoeff h₀ = 0)
    (hdiff : Low N (h - h₀)) (f : PowerSeries K) :
    (∀ m : σ →₀ ℕ, m.degree < N →
      MvPowerSeries.coeff m (PowerSeries.subst h f) =
        MvPowerSeries.coeff m (PowerSeries.subst h₀ f)) ∧
    (∀ d : σ →₀ ℕ, d.degree = N →
      MvPowerSeries.coeff d (PowerSeries.subst h f) =
        MvPowerSeries.coeff d (PowerSeries.subst h₀ f) +
          PowerSeries.coeff 1 f * MvPowerSeries.coeff d (h - h₀)) := by
  have h1 : Low 1 h := low_one_of_constantCoeff_zero hh0
  have h2 : Low 1 h₀ := low_one_of_constantCoeff_zero hh₀0
  constructor
  · intro m hm
    rw [coeff_subst_eq_sum hh0, coeff_subst_eq_sum hh₀0]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rcases k with _ | _ | k
    · simp
    · rw [pow_one, pow_one]
      have h0 := hdiff m hm
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    · have h0 := low_pow_sub_of_low h1 h2 hdiff (by omega : 2 ≤ k + 2) m (by omega)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  · intro d hd
    rw [coeff_subst_eq_sum hh0, coeff_subst_eq_sum hh₀0, hd]
    have hsplit : Finset.range (N + 1) = {0, 1} ∪ Finset.Icc 2 N := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Icc]
      omega
    have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 N) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk1
      simp only [Finset.mem_Icc] at hk2
      omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj,
      Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    have htail : ∑ k ∈ Finset.Icc 2 N, PowerSeries.coeff k f * MvPowerSeries.coeff d (h ^ k) =
        ∑ k ∈ Finset.Icc 2 N, PowerSeries.coeff k f * MvPowerSeries.coeff d (h₀ ^ k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have h0 := low_pow_sub_of_low h1 h2 hdiff hk.1 d (by omega)
      rw [map_sub, sub_eq_zero] at h0
      rw [h0]
    rw [htail]
    simp only [pow_zero, pow_one, map_sub]
    ring

/-- Explicit degree-by-degree recursive construction of the formal solution `h` to `f(h) = g`
(when `constantCoeff f = 0`, `coeff 1 f = 1`, `constantCoeff g = 0`). -/
def solveSubstLayer (f : PowerSeries K) (g : MvPowerSeries σ K) : ℕ → MvPowerSeries σ K
  | 0 => 0
  | N + 1 => fun d =>
      if d.degree ≤ N then MvPowerSeries.coeff d (solveSubstLayer f g N)
      else if d.degree = N + 1 then
        MvPowerSeries.coeff d g - MvPowerSeries.coeff d (PowerSeries.subst (solveSubstLayer f g N) f)
      else 0

lemma coeff_solveSubstLayer_succ (f : PowerSeries K) (g : MvPowerSeries σ K) (N : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (solveSubstLayer f g (N + 1)) =
      if d.degree ≤ N then MvPowerSeries.coeff d (solveSubstLayer f g N)
      else if d.degree = N + 1 then
        MvPowerSeries.coeff d g - MvPowerSeries.coeff d (PowerSeries.subst (solveSubstLayer f g N) f)
      else 0 := rfl

lemma solveSubstLayer_constantCoeff (f : PowerSeries K) (g : MvPowerSeries σ K) (N : ℕ) :
    MvPowerSeries.constantCoeff (solveSubstLayer f g N) = 0 := by
  induction N with
  | zero => simp [solveSubstLayer]
  | succ N ih =>
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_solveSubstLayer_succ,
      if_pos (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ih

lemma solveSubstLayer_eq_of_le (f : PowerSeries K) (g : MvPowerSeries σ K) {N M : ℕ} (hNM : N ≤ M)
    {d : σ →₀ ℕ} (hd : d.degree ≤ N) :
    MvPowerSeries.coeff d (solveSubstLayer f g M) =
      MvPowerSeries.coeff d (solveSubstLayer f g N) := by
  induction M with
  | zero =>
    have hN0 : N = 0 := by omega
    subst hN0; rfl
  | succ M ih =>
    by_cases hle : N ≤ M
    · change (if d.degree ≤ M then MvPowerSeries.coeff d (solveSubstLayer f g M) else _) = _
      rw [if_pos (hd.trans hle)]
      exact ih hle
    · have hEq : N = M + 1 := by omega
      subst hEq; rfl

lemma solveSubstLayer_subst_eq (f : PowerSeries K) (g : MvPowerSeries σ K)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = 1)
    (hg0 : MvPowerSeries.constantCoeff g = 0) (N : ℕ) :
    ∀ d : σ →₀ ℕ, d.degree ≤ N →
      MvPowerSeries.coeff d (PowerSeries.subst (solveSubstLayer f g N) f) =
        MvPowerSeries.coeff d g := by
  induction N with
  | zero =>
    intro d hd
    have hd0 : d = 0 := (degree_eq_zero_iff d).mp (by omega)
    subst hd0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_subst_of_zero (solveSubstLayer_constantCoeff f g 0), hf0, hg0]
  | succ N ih =>
    have hdiff : Low (N + 1) (solveSubstLayer f g (N + 1) - solveSubstLayer f g N) := by
      intro m hm
      rw [map_sub]
      change (if m.degree ≤ N then MvPowerSeries.coeff m (solveSubstLayer f g N) else _) - _ = 0
      rw [if_pos (by omega), sub_self]
    have hsp := coeff_subst_split (by omega : 1 ≤ N + 1)
      (solveSubstLayer_constantCoeff f g (N + 1)) (solveSubstLayer_constantCoeff f g N) hdiff f
    intro d hd
    by_cases hlt : d.degree ≤ N
    · rw [hsp.1 d (by omega)]
      exact ih d hlt
    · have heq : d.degree = N + 1 := by omega
      rw [hsp.2 d heq, hf1, one_mul, map_sub]
      have h1 : MvPowerSeries.coeff d (solveSubstLayer f g (N + 1)) =
          MvPowerSeries.coeff d g -
            MvPowerSeries.coeff d (PowerSeries.subst (solveSubstLayer f g N) f) := by
        change (if d.degree ≤ N then _ else if d.degree = N + 1 then _ else 0) = _
        rw [if_neg (by omega), if_pos heq]
      have h2 : MvPowerSeries.coeff d (solveSubstLayer f g N) = 0 := by
        clear h1 hsp hdiff ih
        induction N with
        | zero => simp [solveSubstLayer]
        | succ M _ =>
          change (if d.degree ≤ M then _ else if d.degree = M + 1 then _ else 0) = 0
          rw [if_neg (by omega), if_neg (by omega)]
      rw [h1, h2, sub_zero, add_sub_cancel]

/-- Explicit formal solution `h = solveSubst f g` to `PowerSeries.subst h f = g`. -/
def solveSubst (f : PowerSeries K) (g : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun d => MvPowerSeries.coeff d (solveSubstLayer f g d.degree)

theorem constantCoeff_solveSubst (f : PowerSeries K) (g : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (solveSubst f g) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change MvPowerSeries.coeff (0 : σ →₀ ℕ) (solveSubstLayer f g (0 : σ →₀ ℕ).degree) = 0
  simp [solveSubstLayer]

theorem subst_solveSubst (f : PowerSeries K) (g : MvPowerSeries σ K)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = 1)
    (hg0 : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (solveSubst f g) f = g := by
  ext d
  set N := d.degree
  have hdiff : Low (N + 1) (solveSubst f g - solveSubstLayer f g N) := by
    intro m hm
    rw [map_sub]
    change MvPowerSeries.coeff m (solveSubstLayer f g m.degree) -
      MvPowerSeries.coeff m (solveSubstLayer f g N) = 0
    rw [solveSubstLayer_eq_of_le f g (by omega : m.degree ≤ N) le_rfl, sub_self]
  have hsp := coeff_subst_split (by omega : 1 ≤ N + 1)
    (constantCoeff_solveSubst f g) (solveSubstLayer_constantCoeff f g N) hdiff f
  rw [hsp.1 d (Nat.lt_succ_self N)]
  exact solveSubstLayer_subst_eq f g hf0 hf1 hg0 N d le_rfl

/-- Explicit compositional inverse `f⁻¹(X)` of a formal logarithm `f ∈ X + X^2 K[[X]]`. -/
def formalLogInv (f : PowerSeries K) : PowerSeries K :=
  solveSubst f (PowerSeries.X : PowerSeries K)

theorem subst_formalLogInv (f : PowerSeries K)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = 1) :
    PowerSeries.subst (formalLogInv f) f = PowerSeries.X :=
  subst_solveSubst f PowerSeries.X hf0 hf1 PowerSeries.constantCoeff_X

end FormalGroupSubst

/-! ### Honda / Lubin–Tate Formal Group Integrality (Hazewinkel's Functional Equation Lemma) -/

section HondaLubinTate

variable {σ : Type*}

/-- **Honda Functional Equation Predicate** over `ℚ_[p]`:
`f ∈ X + X^2 ℚ_[p][[X]]` satisfies `f(X) - p⁻¹ f(X^p) ∈ ℤ_[p][[X]]`. -/
def IsHondaLog (p : ℕ) [Fact p.Prime] (f : PowerSeries ℚ_[p]) : Prop :=
  PowerSeries.constantCoeff f = 0 ∧
  PowerSeries.coeff 1 f = 1 ∧
  ∀ n : ℕ, ‖PowerSeries.coeff n (f - (p : ℚ_[p])⁻¹ • (frobSub p (f : MvPowerSeries Unit ℚ_[p]) : PowerSeries ℚ_[p]))‖ ≤ 1

/-- Multivariate Honda-type series over `ℚ_[p]`:
`constantCoeff g = 0` and `g(X) - p⁻¹ g(X^p) ∈ ℤ_[p][[X_i]]`. -/
def IsHondaTypeMv (p : ℕ) [Fact p.Prime] (g : MvPowerSeries σ ℚ_[p]) : Prop :=
  MvPowerSeries.constantCoeff g = 0 ∧
  IsIntegralMv (g - (p : ℚ_[p])⁻¹ • frobSub p g)

/-- Key `p`-adic binomial valuation lemma (valid for ALL primes `p`, including `p = 2`!):
for every `1 ≤ j ≤ k`, `v_p(k) + 1 ≤ v_p(k.choose j) + j`. -/
theorem padicValNat_choose_add_ge {p : ℕ} (hp : p.Prime) {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    padicValNat p k + 1 ≤ padicValNat p (k.choose j) + j := by
  have : Fact p.Prime := ⟨hp⟩
  have hk_pos : 0 < k := lt_of_lt_of_le hj1 hjk
  have hj_ne : j ≠ 0 := by omega
  have hch_pos : 0 < k.choose j := Nat.choose_pos hjk
  have hmul : k * (k - 1).choose (j - 1) = j * k.choose j := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk_pos
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj1
    simp only [Nat.add_sub_cancel_left]
    rw [add_comm 1 k', add_comm 1 j', Nat.add_one_mul_choose_eq, mul_comm]
  have hch1_pos : 0 < (k - 1).choose (j - 1) := Nat.choose_pos (by omega)
  have hval_eq : padicValNat p k + padicValNat p ((k - 1).choose (j - 1)) =
      padicValNat p j + padicValNat p (k.choose j) := by
    rw [← padicValNat.mul hk_pos.ne' hch1_pos.ne', hmul,
      padicValNat.mul hj_ne hch_pos.ne']
  have hj_gt : padicValNat p j < j := by
    have hpow_le : p ^ padicValNat p j ≤ j := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hlt_pow : padicValNat p j < p ^ padicValNat p j := Nat.lt_pow_self hp.one_lt
    omega
  omega

/-- **Honda Logarithm Coefficient Bound**:
every `k`-th coefficient (`k ≥ 1`) of a Honda logarithm `f` satisfies
`‖(p : ℚ_[p]) ^ (padicValNat p k) * coeff k f‖ ≤ 1`, i.e., `‖coeff k f‖ ≤ ‖p‖ ^ (-v_p(k))`. -/
theorem honda_log_coeff_bound (p : ℕ) [Fact p.Prime] {f : PowerSeries ℚ_[p]}
    (hf : IsHondaLog p f) (k : ℕ) :
    ‖(p : ℚ_[p]) ^ padicValNat p k * PowerSeries.coeff k f‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hp_norm_le : ‖(p : ℚ_[p])‖ ≤ 1 := by
    rw [Padic.norm_p]
    exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)).le
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k'
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, hf.1, mul_zero, norm_zero]; exact zero_le_one
    · set k := k' + 1
      have hphi := hf.2.2 k
      rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, frobSub_unit_eq_frobPS hp.pos,
        coeff_frobPS] at hphi
      by_cases hdiv : p ∣ k
      · obtain ⟨m, hm⟩ := hdiv
        have hm_pos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · simp at hm
          · exact hpos
        have hm_lt : m < k := by nlinarith [hp.two_le]
        have hval : padicValNat p k = padicValNat p m + 1 := by
          rw [hm, padicValNat.mul hp.ne_zero hm_pos.ne', padicValNat.self hp.one_lt, add_comm]
        have hquot : k / p = m := by rw [hm, Nat.mul_div_cancel_left m hp.pos]
        rw [if_pos ⟨m, hm⟩, hquot] at hphi
        have hdecomp : (p : ℚ_[p]) ^ padicValNat p k * PowerSeries.coeff k f =
            (p : ℚ_[p]) ^ padicValNat p k *
              (PowerSeries.coeff k f - (p : ℚ_[p])⁻¹ * PowerSeries.coeff m f) +
            (p : ℚ_[p]) ^ padicValNat p m * PowerSeries.coeff m f := by
          rw [hval, pow_succ]
          field_simp [hp_ne]
          ring
        rw [hdecomp]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (ih m hm_lt))
        rw [norm_mul, norm_pow]
        calc ‖(p : ℚ_[p])‖ ^ padicValNat p k *
              ‖PowerSeries.coeff k f - (p : ℚ_[p])⁻¹ * PowerSeries.coeff m f‖
            ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg _) hp_norm_le) hphi (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
      · rw [if_neg hdiv, mul_zero, sub_zero] at hphi
        have hv0 : padicValNat p k = 0 := padicValNat.eq_zero_of_not_dvd hdiv
        rw [hv0, pow_zero, one_mul]
        exact hphi

/-- **Key Crystalline Integrality Step for Hazewinkel's Functional Equation**:
If `IsHondaLog p f` and `h₀ : MvPowerSeries σ ℚ_[p]` is integral with `constantCoeff h₀ = 0`,
then `(p : ℚ_[p])⁻¹ • (f(h₀ ^ p) - f(frobSub p h₀))` is INTEGRAL! -/
theorem honda_frob_diff_isIntegral (p : ℕ) [Fact p.Prime] {f : PowerSeries ℚ_[p]}
    (hf : IsHondaLog p f) {h₀ : MvPowerSeries σ ℚ_[p]}
    (hh₀0 : MvPowerSeries.constantCoeff h₀ = 0) (hh₀ : IsIntegralMv h₀) :
    IsIntegralMv ((p : ℚ_[p])⁻¹ •
      (PowerSeries.subst (h₀ ^ p) f - PowerSeries.subst (frobSub p h₀) f)) := by
  have hp : p.Prime := Fact.out
  have hpi0 : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlt : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hA0 : MvPowerSeries.constantCoeff (frobSub p h₀) = 0 := by
    rw [constantCoeff_frobSub hp.pos, hh₀0]
  have hB0 : MvPowerSeries.constantCoeff (h₀ ^ p) = 0 := by
    rw [map_pow, hh₀0, zero_pow hp.ne_zero]
  set A := frobSub p h₀
  have hA_int : IsIntegralMv A := fun d => by
    classical
    rw [coeff_frobSub_eq_ite hp.pos]
    split_ifs
    · exact hh₀ _
    · simp
  -- `h₀ ^ p - A = p • U` with `U` integral (from our multivariable Frobenius congruence!)
  set U := (p : ℚ_[p])⁻¹ • (h₀ ^ p - A)
  have hU_int : IsIntegralMv U := fun d => by
    have hcong := frobMapMv_pow_sub_norm_le hp (RingHom.id ℚ_[p])
      (fun c hc => padic_pow_prime_sub_le p hc) hh₀ d
    rw [frobMapMv_id] at hcong
    rw [MvPowerSeries.coeff_smul, norm_mul, norm_inv]
    calc ‖(p : ℚ_[p])‖⁻¹ * ‖MvPowerSeries.coeff d (h₀ ^ p - A)‖
        ≤ ‖(p : ℚ_[p])‖⁻¹ * ‖(p : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_left hcong (inv_nonneg.mpr hpi0.le)
      _ = 1 := inv_mul_cancel₀ hpi0.ne'
  have hhp_eq : h₀ ^ p = A + MvPowerSeries.C (p : ℚ_[p]) * U := by
    ext d
    simp only [U, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_smul, map_sub]
    field_simp [hp_ne]
    ring
  intro d
  rw [MvPowerSeries.coeff_smul, map_sub, coeff_subst_eq_sum hB0,
    coeff_subst_eq_sum hA0, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine ultrametric_norm_sum_le _ _ zero_le_one fun k _ => ?_
  rcases k with _ | k'
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, hf.1]
  · set k := k' + 1
    -- Expand `(A + p U)^k - A^k = ∑_{j=1}^k choose(k, j) * p^j * A^(k-j) * U^j`
    have hexp : (h₀ ^ p) ^ k - A ^ k =
        ∑ j ∈ Finset.Icc 1 k,
          MvPowerSeries.C (((k.choose j : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ j) *
            (U ^ j * A ^ (k - j)) := by
      rw [hhp_eq, add_comm A, add_pow]
      have h0 : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ h0]
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      have herase : (Finset.range (k + 1)).erase 0 = Finset.Icc 1 k := by
        ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
      rw [herase, add_sub_cancel_left]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, ← map_pow, map_mul,
        show (k.choose j : MvPowerSeries σ ℚ_[p]) = MvPowerSeries.C ((k.choose j : ℕ) : ℚ_[p]) by simp]
      ring
    have hterm_eq : (p : ℚ_[p])⁻¹ *
        (PowerSeries.coeff k f * MvPowerSeries.coeff d ((h₀ ^ p) ^ k) -
          PowerSeries.coeff k f * MvPowerSeries.coeff d (A ^ k)) =
        ∑ j ∈ Finset.Icc 1 k,
          ((p : ℚ_[p])⁻¹ * PowerSeries.coeff k f * (((k.choose j : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ j)) *
            MvPowerSeries.coeff d (U ^ j * A ^ (k - j)) := by
      rw [← mul_sub, ← map_sub, hexp, map_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPowerSeries.coeff_C_mul]
      ring
    rw [hterm_eq]
    refine ultrametric_norm_sum_le _ _ zero_le_one fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hUA : ‖MvPowerSeries.coeff d (U ^ j * A ^ (k - j))‖ ≤ 1 :=
      isIntegralMv_mul (isIntegralMv_pow hU_int j) (isIntegralMv_pow hA_int (k - j)) d
    have hval_ge : padicValNat p k + 1 ≤ padicValNat p (k.choose j) + j :=
      padicValNat_choose_add_ge hp hj.1 hj.2
    have hch_ne : k.choose j ≠ 0 := (Nat.choose_pos hj.2).ne'
    have hscalar : ‖(p : ℚ_[p])⁻¹ * PowerSeries.coeff k f *
        (((k.choose j : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ j)‖ ≤ 1 := by
      have hkf := honda_log_coeff_bound p hf k
      rw [norm_mul, norm_pow] at hkf
      rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_pow,
        norm_natCast_eq_pow_padicValNat hp hlt hch_ne]
      have hpow_le : ‖(p : ℚ_[p])‖ ^ (padicValNat p (k.choose j) + j) ≤
          ‖(p : ℚ_[p])‖ ^ (padicValNat p k + 1) :=
        pow_le_pow_of_le_one hpi0.le hlt.le hval_ge
      calc ‖(p : ℚ_[p])‖⁻¹ * ‖PowerSeries.coeff k f‖ *
            (‖(p : ℚ_[p])‖ ^ padicValNat p (k.choose j) * ‖(p : ℚ_[p])‖ ^ j)
          = ‖(p : ℚ_[p])‖⁻¹ * ‖PowerSeries.coeff k f‖ *
              ‖(p : ℚ_[p])‖ ^ (padicValNat p (k.choose j) + j) := by rw [pow_add]
        _ ≤ ‖(p : ℚ_[p])‖⁻¹ * ‖PowerSeries.coeff k f‖ *
              ‖(p : ℚ_[p])‖ ^ (padicValNat p k + 1) :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ = ‖(p : ℚ_[p])‖ ^ padicValNat p k * ‖PowerSeries.coeff k f‖ := by
            rw [pow_succ]; field_simp [hpi0.ne']
        _ ≤ 1 := hkf
    rw [norm_mul]
    calc ‖(p : ℚ_[p])⁻¹ * PowerSeries.coeff k f *
          (((k.choose j : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ j)‖ *
          ‖MvPowerSeries.coeff d (U ^ j * A ^ (k - j))‖
        ≤ 1 * 1 := mul_le_mul hscalar hUA (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- **Hazewinkel's Functional Equation Lemma (`honda_formal_group_subst_isIntegral`)**:
Let `f ∈ ℚ_[p][[X]]` be a Honda formal-group logarithm (`IsHondaLog p f`), and let
`g : MvPowerSeries σ ℚ_[p]` be any multivariate series of Honda type (`IsHondaTypeMv p g`).
Then any `h : MvPowerSeries σ ℚ_[p]` with `constantCoeff h = 0` and `f(h) = g` is
**INTEGRAL**: `∀ d, ‖coeff d h‖ ≤ 1`! -/
theorem honda_formal_group_subst_isIntegral (p : ℕ) [Fact p.Prime] {f : PowerSeries ℚ_[p]}
    (hf : IsHondaLog p f) {g h : MvPowerSeries σ ℚ_[p]} (hg : IsHondaTypeMv p g)
    (hh0 : MvPowerSeries.constantCoeff h = 0) (heq : PowerSeries.subst h f = g) :
    IsIntegralMv h := by
  have hp : p.Prime := Fact.out
  set φ : PowerSeries ℚ_[p] :=
    f - (p : ℚ_[p])⁻¹ • (frobSub p (f : MvPowerSeries Unit ℚ_[p]) : PowerSeries ℚ_[p])
  set ψ : MvPowerSeries σ ℚ_[p] := g - (p : ℚ_[p])⁻¹ • frobSub p g
  have hφ_int : ∀ n, ‖PowerSeries.coeff n φ‖ ≤ 1 := hf.2.2
  have hψ_int : IsIntegralMv ψ := hg.2
  have hφ1 : PowerSeries.coeff 1 φ = 1 := by
    change PowerSeries.coeff 1 (f - (p : ℚ_[p])⁻¹ • _) = 1
    rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, frobSub_unit_eq_frobPS hp.pos, coeff_frobPS]
    have hnd : ¬ p ∣ 1 := by
      intro hd; have := Nat.le_of_dvd one_pos hd; have := hp.two_le; omega
    rw [if_neg hnd, mul_zero, sub_zero, hf.2.1]
  -- Core identity: `φ(h) + p⁻¹ (f(h^p) - f(frobSub p h)) = ψ`!
  have hcore : PowerSeries.subst h φ +
      (p : ℚ_[p])⁻¹ • (PowerSeries.subst (h ^ p) f - PowerSeries.subst (frobSub p h) f) = ψ := by
    rw [show φ = f - (p : ℚ_[p])⁻¹ • (frobSub p (f : MvPowerSeries Unit ℚ_[p]) : PowerSeries ℚ_[p])
      from rfl, subst_sub_left hh0, subst_smul_left hh0, subst_frobSub hp.pos hh0,
      ← frobSub_subst hp.pos hh0, heq]
    simp only [ψ, smul_sub]
    abel
  suffices H : ∀ N : ℕ, ∀ d : σ →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d h‖ ≤ 1 from
    fun d => H _ d rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro d hd
    rcases N with _ | n
    · have hd0 : d = 0 := (degree_eq_zero_iff d).mp hd
      subst hd0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, norm_zero]
      exact zero_le_one
    · set M := n + 1
      set h₀ := truncBelow M h
      have hh₀0 : MvPowerSeries.constantCoeff h₀ = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_truncBelow,
          if_pos (by simp; omega), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0]
      have hh₀_int : IsIntegralMv h₀ := fun m => by
        rw [coeff_truncBelow]
        split_ifs with hm
        · exact ih _ hm m rfl
        · simp
      have hdiff : Low M (h - h₀) := low_sub_truncBelow M h
      -- 1) `coeff d (φ(h)) = coeff d (φ(h₀)) + coeff d h`
      have hφ_split : MvPowerSeries.coeff d (PowerSeries.subst h φ) =
          MvPowerSeries.coeff d (PowerSeries.subst h₀ φ) + MvPowerSeries.coeff d h := by
        have hsp := (coeff_subst_split (by omega : 1 ≤ M) hh0 hh₀0 hdiff φ).2 d hd
        rw [hφ1, one_mul, map_sub, coeff_truncBelow, if_neg (by omega), sub_zero] at hsp
        exact hsp
      -- 2) `h^p` and `h₀^p` agree on degrees `≤ M` (since `p ≥ 2` and `Low 1 h`, `Low 1 h₀`)
      have hhp_low : Low (M + 1) (h ^ p - h₀ ^ p) :=
        low_pow_sub_of_low (low_one_of_constantCoeff_zero hh0)
          (low_one_of_constantCoeff_zero hh₀0) hdiff hp.two_le
      have hfp_eq : MvPowerSeries.coeff d (PowerSeries.subst (h ^ p) f) =
          MvPowerSeries.coeff d (PowerSeries.subst (h₀ ^ p) f) := by
        have hhp0 : MvPowerSeries.constantCoeff (h ^ p) = 0 := by
          rw [map_pow, hh0, zero_pow hp.ne_zero]
        have hh₀p0 : MvPowerSeries.constantCoeff (h₀ ^ p) = 0 := by
          rw [map_pow, hh₀0, zero_pow hp.ne_zero]
        exact (coeff_subst_split (by omega : 1 ≤ M + 1) hhp0 hh₀p0 hhp_low f).1 d (by omega)
      -- 3) `frobSub p h` and `frobSub p h₀` agree on degrees `≤ M`
      have hfh_low : Low (M + 1) (frobSub p h - frobSub p h₀) := by
        intro m hm
        rw [map_sub, coeff_frobSub_eq_ite hp.pos, coeff_frobSub_eq_ite hp.pos]
        split_ifs with hdiv
        · set e := m.mapRange (· / p) (Nat.zero_div p)
          have hme : p • e = m := nsmul_mapRange_div_eq hdiv
          have hdeg_e : p * e.degree = m.degree := by rw [← hme, map_nsmul, smul_eq_mul]
          have hMpos : 0 < M := Nat.succ_pos n
          have hlt : e.degree < M := by nlinarith [hp.two_le, hMpos]
          rw [coeff_truncBelow, if_pos hlt, sub_self]
        · exact sub_self 0
      have hff_eq : MvPowerSeries.coeff d (PowerSeries.subst (frobSub p h) f) =
          MvPowerSeries.coeff d (PowerSeries.subst (frobSub p h₀) f) := by
        have hfh0 : MvPowerSeries.constantCoeff (frobSub p h) = 0 := by
          rw [constantCoeff_frobSub hp.pos, hh0]
        have hfh₀0 : MvPowerSeries.constantCoeff (frobSub p h₀) = 0 := by
          rw [constantCoeff_frobSub hp.pos, hh₀0]
        exact (coeff_subst_split (by omega : 1 ≤ M + 1) hfh0 hfh₀0 hfh_low f).1 d (by omega)
      -- 4) Solve for `coeff d h` and bound all three integral pieces!
      have hsolve : MvPowerSeries.coeff d h =
          MvPowerSeries.coeff d ψ - MvPowerSeries.coeff d (PowerSeries.subst h₀ φ) -
            MvPowerSeries.coeff d ((p : ℚ_[p])⁻¹ •
              (PowerSeries.subst (h₀ ^ p) f - PowerSeries.subst (frobSub p h₀) f)) := by
        have hc := congrArg (MvPowerSeries.coeff d) hcore
        rw [map_add, hφ_split, MvPowerSeries.coeff_smul, map_sub, hfp_eq, hff_eq,
          ← map_sub, ← MvPowerSeries.coeff_smul] at hc
        linear_combination hc
      have hφh₀_int : ‖MvPowerSeries.coeff d (PowerSeries.subst h₀ φ)‖ ≤ 1 := by
        rw [coeff_subst_eq_sum hh₀0]
        refine ultrametric_norm_sum_le _ _ zero_le_one fun k _ => ?_
        rw [norm_mul]
        calc ‖PowerSeries.coeff k φ‖ * ‖MvPowerSeries.coeff d (h₀ ^ k)‖
            ≤ 1 * 1 := mul_le_mul (hφ_int k) (isIntegralMv_pow hh₀_int k d) (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
      have hfdiff_int := honda_frob_diff_isIntegral p hf hh₀0 hh₀_int d
      rw [hsolve, sub_eq_add_neg, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (hψ_int d) (by rwa [norm_neg]))

/-- **Honda Formal Group Law Integrality (`honda_formal_group_law_isIntegral`)**:
For ANY Honda logarithm `f ∈ ℚ_[p][[X]]`, the formal group law
`F(X, Y) = f⁻¹(f(X) + f(Y)) ∈ MvPowerSeries (Fin 2) ℚ_[p]` satisfies
`f(F(X, Y)) = f(X) + f(Y)` AND EVERY coefficient of `F(X, Y)` lies in `ℤ_[p]`! -/
theorem honda_formal_group_law_isIntegral (p : ℕ) [Fact p.Prime] {f : PowerSeries ℚ_[p]}
    (hf : IsHondaLog p f) :
    let g : MvPowerSeries (Fin 2) ℚ_[p] :=
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) f +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) f
    let F : MvPowerSeries (Fin 2) ℚ_[p] := solveSubst f g
    MvPowerSeries.constantCoeff F = 0 ∧
    PowerSeries.subst F f = g ∧
    IsIntegralMv F := by
  have hp : p.Prime := Fact.out
  intro g F
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℚ_[p]) = 0 := by
    simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℚ_[p]) = 0 := by
    simp
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    simp [g, constantCoeff_subst_of_zero hX0, constantCoeff_subst_of_zero hX1, hf.1]
  have hsubst_var : ∀ i : Fin 2,
      IsHondaTypeMv p (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[p]) f) := by
    intro i
    have hXi0 : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[p]) = 0 :=
      MvPowerSeries.constantCoeff_X i
    refine ⟨by rw [constantCoeff_subst_of_zero hXi0, hf.1], ?_⟩
    have heq : PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[p]) f -
        (p : ℚ_[p])⁻¹ • frobSub p (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[p]) f) =
        PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[p])
          (f - (p : ℚ_[p])⁻¹ • (frobSub p (f : MvPowerSeries Unit ℚ_[p]) : PowerSeries ℚ_[p])) := by
      rw [subst_sub_left hXi0, subst_smul_left hXi0, subst_frobSub hp.pos hXi0,
        frobSub_subst hp.pos hXi0, frobSub_X hp.pos]
    rw [heq]
    intro d
    rw [coeff_subst_eq_sum hXi0]
    refine ultrametric_norm_sum_le _ _ zero_le_one fun k _ => ?_
    rw [norm_mul]
    have hXint : IsIntegralMv (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[p]) := by
      intro m
      classical
      rw [MvPowerSeries.coeff_X]
      split_ifs <;> simp
    calc ‖PowerSeries.coeff k _‖ * ‖MvPowerSeries.coeff d ((MvPowerSeries.X i) ^ k)‖
        ≤ 1 * 1 := mul_le_mul (hf.2.2 k) (isIntegralMv_pow hXint k d) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hg_type : IsHondaTypeMv p g := by
    refine ⟨hg0, ?_⟩
    have hsplit : g - (p : ℚ_[p])⁻¹ • frobSub p g =
        (PowerSeries.subst (MvPowerSeries.X 0) f -
          (p : ℚ_[p])⁻¹ • frobSub p (PowerSeries.subst (MvPowerSeries.X 0) f)) +
        (PowerSeries.subst (MvPowerSeries.X 1) f -
          (p : ℚ_[p])⁻¹ • frobSub p (PowerSeries.subst (MvPowerSeries.X 1) f)) := by
      simp only [g, frobSub_add hp.pos, smul_add]
      abel
    rw [hsplit]
    exact isIntegralMv_add (hsubst_var 0).2 (hsubst_var 1).2
  have hF0 : MvPowerSeries.constantCoeff F = 0 := constantCoeff_solveSubst f g
  have hFeq : PowerSeries.subst F f = g := subst_solveSubst f g hf.1 hf.2.1 hg0
  exact ⟨hF0, hFeq, honda_formal_group_subst_isIntegral p hf hg_type hF0 hFeq⟩

/-- **Lubin–Tate Logarithm** `log_{LT}(X) = ∑_{m ≥ 0} X^{p^m} / p^m` satisfies `IsHondaLog p`! -/
theorem lubinTate_log_isHondaLog (p : ℕ) [Fact p.Prime] :
    IsHondaLog p (artinHasseArg ℚ_[p] p) := by
  have hp : p.Prime := Fact.out
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨constantCoeff_artinHasseArg hp, ?_, ?_⟩
  · classical
    simp only [artinHasseArg, PowerSeries.coeff_mk]
    rw [if_pos ⟨0, (pow_zero p).symm⟩]
    simp
  · have hid := frobPS_artinHasseArg_sub (R := ℚ_[p]) hp
    have hsub : artinHasseArg ℚ_[p] p -
        (p : ℚ_[p])⁻¹ • (frobSub p (artinHasseArg ℚ_[p] p : MvPowerSeries Unit ℚ_[p]) : PowerSeries ℚ_[p]) =
        PowerSeries.X := by
      rw [frobSub_unit_eq_frobPS hp.pos]
      ext n
      have h1 := congrArg (PowerSeries.coeff n) hid
      rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_C_mul] at h1
      rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul]
      field_simp [hp_ne]
      linear_combination -h1
    rw [hsub]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs <;> simp

/-- **Lubin–Tate Formal Group Integrality (`lubinTate_formal_group_isIntegral`)**:
The Lubin–Tate formal group law `F_{LT}(X, Y) = log_{LT}⁻¹(log_{LT}(X) + log_{LT}(Y))` over `ℚ_[p]`
has ALL coefficients in `ℤ_[p]`! -/
theorem lubinTate_formal_group_isIntegral (p : ℕ) [Fact p.Prime] :
    let logLT := artinHasseArg ℚ_[p] p
    let g : MvPowerSeries (Fin 2) ℚ_[p] :=
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) logLT +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) logLT
    let F_LT : MvPowerSeries (Fin 2) ℚ_[p] := solveSubst logLT g
    PowerSeries.subst F_LT logLT = g ∧ IsIntegralMv F_LT := by
  have h := honda_formal_group_law_isIntegral p (lubinTate_log_isHondaLog p)
  exact ⟨h.2.1, h.2.2⟩

/-- Formal logarithm of the multiplicative formal group `𝔾_m`:
`log_{𝔾_m}(X) = ∑_{n ≥ 1} (-1)^(n-1) X^n / n`. -/
def gmLog (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1 : ℚ_[p]) ^ (n - 1) * (n : ℚ_[p])⁻¹

/-- `log(1 + X)` satisfies Honda's functional equation `log(1+X) - p⁻¹ log(1+X^p) ∈ ℤ_[p][[X]]`
for EVERY prime `p` (including `p = 2`!). -/
theorem gm_log_isHondaLog (p : ℕ) [Fact p.Prime] : IsHondaLog p (gmLog p) := by
  have hp : p.Prime := Fact.out
  have hlt : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [gmLog], by simp [gmLog], ?_⟩
  intro n
  rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, frobSub_unit_eq_frobPS hp.pos, coeff_frobPS]
  simp only [gmLog, PowerSeries.coeff_mk]
  rcases n with _ | n'
  · simp
  · set n := n' + 1
    rw [if_neg (Nat.succ_ne_zero n')]
    by_cases hdiv : p ∣ n
    · obtain ⟨m, hm⟩ := hdiv
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hm
        · exact hpos
      have hquot : n / p = m := by rw [hm, Nat.mul_div_cancel_left m hp.pos]
      rw [if_pos ⟨m, hm⟩, hquot, if_neg hm_pos.ne']
      rcases hp.eq_two_or_odd with rfl | hodd
      · -- `p = 2`: `(-1)^(2m-1) = -1`; if `m` even both signs `-1` cancel; if `m` odd diff is `-1/m ∈ ℤ_2`
        have hm_sign : (-1 : ℚ_[2]) ^ (2 * m - 1) = -1 := by
          have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
          rw [this, pow_succ, pow_mul]; norm_num
        rw [hm, hm_sign]
        rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
        · have hms : (-1 : ℚ_[2]) ^ (m - 1) = -1 := by
            have : m - 1 = 2 * (k - 1) + 1 := by omega
            rw [this, pow_succ, pow_mul]; norm_num
          rw [hms, Nat.cast_mul, mul_inv]
          push_cast
          have h0 : (-1 : ℚ_[2]) * ((2 : ℚ_[2])⁻¹ * (m : ℚ_[2])⁻¹) -
              (2 : ℚ_[2])⁻¹ * ((-1 : ℚ_[2]) * (m : ℚ_[2])⁻¹) = 0 := by ring
          rw [h0, norm_zero]; exact zero_le_one
        · have hms : (-1 : ℚ_[2]) ^ (m - 1) = 1 := by
            have : m - 1 = 2 * k := by omega
            rw [this, pow_mul]; norm_num
          rw [hms, Nat.cast_mul, mul_inv]
          push_cast
          have hsimp : (-1 : ℚ_[2]) * ((2 : ℚ_[2])⁻¹ * (m : ℚ_[2])⁻¹) -
              (2 : ℚ_[2])⁻¹ * ((1 : ℚ_[2]) * (m : ℚ_[2])⁻¹) = -((m : ℚ_[2])⁻¹) := by
            have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
            field_simp [h2]
            ring
          rw [hsimp, norm_neg, norm_inv]
          have hnd : ¬ 2 ∣ m := by omega
          rw [norm_natCast_eq_one_of_not_dvd hp hlt hnd, inv_one]
      · -- Odd prime `p`: `p * m - 1` and `m - 1` have the same parity, so the term vanishes identically!
        have hpar : Even (p * m - 1 + (m - 1)) := by
          have hpm : (p + 1) * m = p * m + m := by ring
          have h1 : 1 ≤ p * m := Nat.mul_pos hp.pos hm_pos
          have h2 : 1 ≤ m := hm_pos
          have heq_sub : p * m - 1 + (m - 1) = (p + 1) * m - 2 := by omega
          rw [heq_sub]
          obtain ⟨k, hk⟩ := Nat.odd_iff.mpr hodd
          have hpm2 : (p + 1) * m = 2 * ((k + 1) * m) := by rw [hk]; ring
          have hkm : 1 ≤ (k + 1) * m := Nat.mul_pos (by omega) hm_pos
          refine ⟨(k + 1) * m - 1, ?_⟩
          omega
        have hsign : (-1 : ℚ_[p]) ^ (p * m - 1) = (-1 : ℚ_[p]) ^ (m - 1) := by
          have hprod : (-1 : ℚ_[p]) ^ (p * m - 1) * (-1 : ℚ_[p]) ^ (m - 1) = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow hpar
          have hsq : ((-1 : ℚ_[p]) ^ (m - 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          calc (-1 : ℚ_[p]) ^ (p * m - 1)
              = (-1 : ℚ_[p]) ^ (p * m - 1) * 1 := (mul_one _).symm
            _ = (-1 : ℚ_[p]) ^ (p * m - 1) * (((-1 : ℚ_[p]) ^ (m - 1)) * (-1 : ℚ_[p]) ^ (m - 1)) := by
                rw [← sq, hsq]
            _ = ((-1 : ℚ_[p]) ^ (p * m - 1) * (-1 : ℚ_[p]) ^ (m - 1)) * (-1 : ℚ_[p]) ^ (m - 1) := by
                ring
            _ = (-1 : ℚ_[p]) ^ (m - 1) := by rw [hprod, one_mul]
        rw [hm, hsign, Nat.cast_mul, mul_inv]
        have h0 : (-1 : ℚ_[p]) ^ (m - 1) * ((p : ℚ_[p])⁻¹ * (m : ℚ_[p])⁻¹) -
            (p : ℚ_[p])⁻¹ * ((-1 : ℚ_[p]) ^ (m - 1) * (m : ℚ_[p])⁻¹) = 0 := by ring
        rw [h0, norm_zero]; exact zero_le_one
    · rw [if_neg hdiv, mul_zero, sub_zero, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, norm_inv, norm_natCast_eq_one_of_not_dvd hp hlt hdiv, inv_one]

/-- **Integral Formal Isomorphism between Lubin–Tate and `𝔾_m` (`lubinTate_gm_iso_isIntegral`)**:
The unique formal isomorphism `h = log_{𝔾_m}⁻¹(log_{LT}(X))` (`= E_p(X) - 1`) sending the
Lubin–Tate formal group to `𝔾_m` is integral over `ℤ_[p]`! -/
theorem lubinTate_gm_iso_isIntegral (p : ℕ) [Fact p.Prime] :
    let h : PowerSeries ℚ_[p] := solveSubst (gmLog p) (artinHasseArg ℚ_[p] p)
    PowerSeries.constantCoeff h = 0 ∧
    PowerSeries.subst h (gmLog p) = artinHasseArg ℚ_[p] p ∧
    ∀ n : ℕ, ‖PowerSeries.coeff n h‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hgm := gm_log_isHondaLog p
  have hlt := lubinTate_log_isHondaLog p
  set h : PowerSeries ℚ_[p] := solveSubst (gmLog p) (artinHasseArg ℚ_[p] p)
  have hh0 : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℚ_[p]) = 0 :=
    constantCoeff_solveSubst (gmLog p) (artinHasseArg ℚ_[p] p)
  have heq : PowerSeries.subst (h : MvPowerSeries Unit ℚ_[p]) (gmLog p) =
      (artinHasseArg ℚ_[p] p : MvPowerSeries Unit ℚ_[p]) :=
    subst_solveSubst (gmLog p) (artinHasseArg ℚ_[p] p) hgm.1 hgm.2.1 hlt.1
  have hlt_mv : IsHondaTypeMv (σ := Unit) p (artinHasseArg ℚ_[p] p : MvPowerSeries Unit ℚ_[p]) := by
    refine ⟨hlt.1, fun d => ?_⟩
    have hd : d = Finsupp.single () (d ()) := by ext; simp
    rw [hd]
    exact hlt.2.2 (d ())
  have hint := honda_formal_group_subst_isIntegral (σ := Unit) p hgm hlt_mv hh0 heq
  exact ⟨hh0, heq, fun n => hint (Finsupp.single () n)⟩

end HondaLubinTate

end ArtinHasseAndFormalGroups

/-! ## Section 4: Crystalline `QPack` Valuation (`‖th nu‖ = p^{-1/(p-1)}`) & Multivariable Dwork Weights -/

section CrystallineQPackSection

/-- **Crystalline / Hodge–Tate `QPack` Structure** (matching Alpöge's `ThetaNormsAndLinks.QPack`):
packages an integral base ring `A` mapping onto the unit ball `O_K` via `th : A →+* K`, elements
`xi, nu : A` with **exact Dwork valuation `‖th nu‖ = p^{-1/(p-1)}`**, `A`-modules `TA, M` linked by
`i : TA →ₗ[A] M` and `k : M →ₗ[A] TA` with `i ∘ k = k ∘ i = (xi * nu) • id`, `xi`-torsion-free `M`,
and a Hodge–Tate reduction `red : FilM →+ OmV` compatible with `th`. -/
structure CrystallineQPack.{u, v} (K : Type u) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] where
  A : Type v
  [rA : CommRing A]
  th : A →+* K
  th_range : ∀ c : K, ‖c‖ ≤ 1 ↔ c ∈ th.range
  xi : A
  nu : A
  th_nu : ‖th nu‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1))
  Tp : Type v
  [aTp : AddCommGroup Tp]
  OmV : Type v
  [aOmV : AddCommGroup OmV]
  [mOmV : Module K OmV]
  TA : Type v
  [aTA : AddCommGroup TA]
  [mTA : Module A TA]
  M : Type v
  [aM : AddCommGroup M]
  [mM : Module A M]
  iT : Tp →+ TA
  iT_span : Submodule.span A (Set.range iT) = ⊤
  i : TA →ₗ[A] M
  k : M →ₗ[A] TA
  ik : ∀ m : M, i (k m) = (xi * nu) • m
  ki : ∀ t : TA, k (i t) = (xi * nu) • t
  tf : ∀ m : M, xi • m = 0 → m = 0
  FilM : Submodule A M
  red : FilM →+ OmV
  red_smul : ∀ (a : A) (m : FilM), red (a • m) = th a • red m
  i_mem : ∀ t : TA, i t ∈ FilM
  ht : Tp →+ OmV
  ht_eq : ∀ t : Tp, ht t = red ⟨i (iT t), i_mem (iT t)⟩
  k_Fil : ∀ m ∈ FilM, ∃ t : TA, k m = xi • t

attribute [instance] CrystallineQPack.rA CrystallineQPack.aTp CrystallineQPack.aOmV
  CrystallineQPack.mOmV CrystallineQPack.aTA CrystallineQPack.mTA CrystallineQPack.aM
  CrystallineQPack.mM

namespace CrystallineQPack

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ} [Fact p.Prime]

/-- **Crystalline Hodge–Tate Cokernel Annihilator Lemma (`cokernel_annihilated_by_nu`)**:
For every filtered crystalline element `m ∈ FilM`, there exists `t ∈ TA` such that
`i t = nu • m`, and consequently `th nu • red ⟨m, hm⟩ = red ⟨i t, i_mem t⟩` — i.e., multiplication
by `th nu` (of exact norm `p^{-1/(p-1)}`) annihilates the Hodge–Tate cokernel! -/
theorem cokernel_annihilated_by_nu (Q : CrystallineQPack K p) {m : Q.M} (hm : m ∈ Q.FilM) :
    ∃ t : Q.TA, Q.i t = Q.nu • m ∧
      Q.th Q.nu • Q.red ⟨m, hm⟩ = Q.red ⟨Q.i t, Q.i_mem t⟩ := by
  obtain ⟨t, ht⟩ := Q.k_Fil m hm
  have hxi : Q.xi • (Q.i t - Q.nu • m) = 0 := by
    rw [smul_sub, ← map_smul, ← ht, Q.ik, mul_smul, sub_self]
  have heq : Q.i t = Q.nu • m := sub_eq_zero.mp (Q.tf _ hxi)
  refine ⟨t, heq, ?_⟩
  rw [← Q.red_smul Q.nu ⟨m, hm⟩]
  congr 1
  exact Subtype.ext heq.symm

/-- Exact additive `p`-adic valuation of `Q.th Q.nu`:
when `‖(p : K)‖ = p⁻¹`, `dworkVal p (Q.th Q.nu) = 1 / (p - 1)`! -/
theorem val_th_nu [CharZero K] (Q : CrystallineQPack K p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) :
    dworkVal p (Q.th Q.nu) = 1 / ((p : ℝ) - 1) := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  unfold dworkVal
  rw [Q.th_nu, hnp, Real.log_rpow hp_pos, Real.log_inv]
  field_simp [hlog_ne]

/-- **Multivariable Dwork Exponential Integrality via `QPack` (`qpack_mvExp_wtGe`)**:
If `B : MvPowerSeries σ K` has `constantCoeff B = 0` and every coefficient is bounded by
`‖Q.th Q.nu‖ * ‖(p : K)‖ ^ (-wtDot d r)`, then `mvExp B` has Dwork weight `≥ 0` at radius `r`! -/
theorem qpack_mvExp_wtGe [CharZero K] {σ : Type*} (Q : CrystallineQPack K p)
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {r : σ → ℝ} {B : MvPowerSeries σ K}
    (hB0 : MvPowerSeries.constantCoeff B = 0)
    (hB : ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d B‖ ≤ ‖Q.th Q.nu‖ * ‖(p : K)‖ ^ (-wtDot d r)) :
    WtGe ‖(p : K)‖ r 0 (mvExp B) := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hth_eq : ‖Q.th Q.nu‖ = ‖(p : K)‖ ^ ((1 : ℝ) / ((p : ℝ) - 1)) := by
    rw [Q.th_nu, hnp, Real.inv_rpow hp_pos.le, ← Real.rpow_neg hp_pos.le]
    congr 1; ring
  have hWtB : WtGe ‖(p : K)‖ r (1 / ((p : ℝ) - 1)) B := fun d => by
    unfold MonoWtGe
    calc ‖MvPowerSeries.coeff d B‖
        ≤ ‖Q.th Q.nu‖ * ‖(p : K)‖ ^ (-wtDot d r) := hB d
      _ = ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1)) * ‖(p : K)‖ ^ (-wtDot d r) := by rw [hth_eq]
      _ = ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) - wtDot d r) := by
          rw [← Real.rpow_add hpi0, ← sub_eq_add_neg]
  intro κ
  exact dwork_exp_weight_le hp hlt hB0 (fun m _ => hWtB m) κ le_rfl

end CrystallineQPack

/-- Valuation subring `O_K = {c : K | ‖c‖ ≤ 1}` of an ultrametric normed field `K`. -/
def ultrametricUnitBall (K : Type*) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {c : K | ‖c‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    calc ‖a‖ * ‖b‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg b) zero_le_one
      _ = 1 := one_mul 1
  one_mem' := by show ‖(1 : K)‖ ≤ 1; simp
  add_mem' {a b} ha hb := by
    show ‖a + b‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : K)‖ ≤ 1; simp
  neg_mem' {a} ha := by show ‖-a‖ ≤ 1; rwa [norm_neg]

/-- **Unconditional Concrete `CrystallineQPack` from a Dwork Uniformizer (`dworkPiQPack`)**:
Given ANY ultrametric field `K` (`CharZero K`, `‖(p : K)‖ = p⁻¹`) containing a Dwork uniformizer
`ϖ : K` satisfying `ϖ ^ (p - 1) = -(p : K)` (from `Stage2DworkExp.norm_dworkPi`), constructs a
genuine `CrystallineQPack K p` with `A = O_K`, `nu = ϖ`, and exact norm
`‖th nu‖ = p ^ (-1 / (p - 1))`! -/
def dworkPiQPack (K : Type*) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p : ℕ) [Fact p.Prime] (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (ϖ : K) (hϖ : ϖ ^ (p - 1) = -(p : K)) : CrystallineQPack K p := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hϖ_norm : ‖ϖ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
    rw [norm_dworkPi hp hϖ, expRadius, hnp, Real.inv_rpow hp_pos.le, ← Real.rpow_neg hp_pos.le]
    congr 1; ring
  have hϖ_le : ‖ϖ‖ ≤ 1 := by
    rw [norm_dworkPi hp hϖ]
    exact (expRadius_lt_one hp hlt).le
  let A := ultrametricUnitBall K
  let nuA : A := ⟨ϖ, hϖ_le⟩
  exact
    { A := A
      th := A.subtype
      th_range := fun c => by
        constructor
        · intro hc; exact ⟨⟨c, hc⟩, rfl⟩
        · rintro ⟨⟨a, ha⟩, rfl⟩; exact ha
      xi := 1
      nu := nuA
      th_nu := hϖ_norm
      Tp := A
      OmV := K
      TA := A
      M := A
      iT := AddMonoidHom.id A
      iT_span := by
        rw [AddMonoidHom.coe_id, Set.range_id, Submodule.span_univ]
      i := nuA • LinearMap.id
      k := LinearMap.id
      ik := fun m => by simp [one_mul]
      ki := fun t => by simp [one_mul]
      tf := fun m hm => by simpa using hm
      FilM := ⊤
      red :=
        { toFun := fun m => A.subtype m.1
          map_zero' := by simp
          map_add' := fun x y => by simp }
      red_smul := fun a m => by simp [smul_eq_mul]
      i_mem := fun _ => trivial
      ht :=
        { toFun := fun t => A.subtype (nuA * t)
          map_zero' := by simp
          map_add' := fun x y => by simp [mul_add] }
      ht_eq := fun t => by simp [smul_eq_mul]
      k_Fil := fun m _ => ⟨m, by simp⟩ }

/-- **Multivariable Dwork Splitting Function**:
`θ_σ(X) = ∏_{i : σ} θ(X_i)` embedded into `MvPowerSeries σ K`, where `θ(t) = exp(ϖ (t - t^p))`. -/
def multivarDworkSplitting {σ K : Type*} [Fintype σ] [NormedField K] [CharZero K]
    (ϖ : K) (p : ℕ) : MvPowerSeries σ K :=
  ∏ i : σ, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) (dworkSplitting ϖ p)

/-- Coordinate embedding preserves Dwork weight bounds: if `f : PowerSeries K` satisfies
univariate `WtGe pi (fun _ => -α) w f`, then `f(X_i) : MvPowerSeries σ K` satisfies
multivariate `WtGe pi (fun _ => -α) w (f(X_i))`! -/
theorem wtGe_subst_X {σ K : Type*} [NormedField K] [IsUltrametricDist K]
    {pi α w : ℝ} (hpi : 0 < pi) {f : PowerSeries K}
    (hf : WtGe pi (fun _ : Unit => -α) w (f : MvPowerSeries Unit K)) (i : σ) :
    WtGe pi (fun _ : σ => -α) w (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) f) := by
  classical
  have hXi0 : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries σ K) = 0 :=
    MvPowerSeries.constantCoeff_X i
  intro d
  unfold MonoWtGe
  rw [coeff_subst_eq_sum hXi0]
  have hXpow : ∀ k : ℕ, MvPowerSeries.coeff d ((MvPowerSeries.X i : MvPowerSeries σ K) ^ k) =
      if d = Finsupp.single i k then 1 else 0 := by
    intro k
    have h1 : (MvPowerSeries.X i : MvPowerSeries σ K) ^ k =
        MvPowerSeries.monomial (Finsupp.single i k) 1 := by
      have hX : (MvPowerSeries.X i : MvPowerSeries σ K) =
          MvPowerSeries.monomial (Finsupp.single i 1) 1 := rfl
      rw [hX, MvPowerSeries.monomial_pow, one_pow, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, MvPowerSeries.coeff_monomial]
  simp_rw [hXpow]
  by_cases hsing : d = Finsupp.single i (d i)
  · have hdeg : d.degree = d i := by
      conv_lhs => rw [hsing]
      simp
    rw [Finset.sum_eq_single (d i)]
    · rw [if_pos hsing, mul_one]
      have hwt_d : wtDot d (fun _ : σ => -α) = (d i : ℝ) * (-α) := by
        conv_lhs => rw [hsing]
        unfold wtDot
        rw [Finsupp.sum_single_index (by simp)]
      have hhf := hf (Finsupp.single () (d i))
      unfold MonoWtGe at hhf
      rw [wtDot_unit, Finsupp.single_eq_same] at hhf
      rw [hwt_d]
      exact hhf
    · intro k _ hk
      rw [if_neg, mul_zero]
      intro hEq
      apply hk
      have := congrArg (fun f : σ →₀ ℕ => f i) (hsing.symm.trans hEq)
      simpa using this.symm
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_range, hdeg]; exact Nat.lt_succ_self _
  · have hzero : ∑ k ∈ Finset.range (d.degree + 1),
        PowerSeries.coeff k f * (if d = Finsupp.single i k then (1 : K) else 0) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg, mul_zero]
      intro hEq
      apply hsing
      have hk : d i = k := by
        have := congrArg (fun f : σ →₀ ℕ => f i) hEq
        simpa using this
      rwa [hk]
    rw [hzero, norm_zero]
    exact Real.rpow_nonneg hpi.le _

/-- **Multivariable Dwork Splitting Overconvergence Theorem (`multivar_dworkSplitting_wtGe`)**:
For any finite variable set `σ`, prime `p` (`‖(p : K)‖ < 1`), and Dwork uniformizer `ϖ^(p-1) = -p`,
`θ_σ(X) = ∏_{i : σ} θ(X_i)` satisfies `WtGe ‖(p : K)‖ (fun _ => -(p - 1) / p^2) 0`, i.e.
`‖coeff d (θ_σ)‖ ≤ ‖(p : K)‖ ^ (d.degree * (p - 1) / p^2)` for EVERY multi-index `d : σ →₀ ℕ`! -/
theorem multivar_dworkSplitting_wtGe {σ K : Type*} [Fintype σ] [NormedField K]
    [IsUltrametricDist K] [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    WtGe ‖(p : K)‖ (fun _ : σ => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (multivarDworkSplitting (σ := σ) ϖ p) := by
  classical
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have h1 : ∀ i : σ, WtGe ‖(p : K)‖ (fun _ : σ => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) (dworkSplitting ϖ p)) := fun i =>
    wtGe_subst_X hpi0 (dworkSplitting_wtGe hp hlt hϖ) i
  unfold multivarDworkSplitting
  have hfin : ∀ s : Finset σ,
      WtGe ‖(p : K)‖ (fun _ : σ => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
        (∏ i ∈ s, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K) (dworkSplitting ϖ p)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty]
      exact wtGe_one hpi0 _
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro d
      simpa using multiplicative_weight_le hpi0 (fun m _ => h1 a m) (fun m _ => ih m) d le_rfl
  exact hfin Finset.univ

end CrystallineQPackSection

/-! ## Section 5: Inert-Prime Congruence Sublattice Slope Shift & `LinkG` (`Ga ≈ ASK`) -/

section InertCongruenceSlopeShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open RHDirect.ArakelovCovolume (rk covol degAr slope discreteTopology_of_le covol_eq_sqrt_det_gram
  covol_pos rk_pos_of_ne_bot)

/-- Scalar rescaling `c • L` of a `ℤ`-submodule `L ⊂ E` (modelling fractional ideal scaling
`latN = Iu • NuLat u` in real archimedean coordinates). -/
def scaleSubmodule (c : ℝ) (L : Submodule ℤ E) : Submodule ℤ E :=
  L.map ((c • LinearMap.id : E →ₗ[ℝ] E).restrictScalars ℤ)

omit [FiniteDimensional ℝ E] in
def scaleSubmodule_equiv {c : ℝ} (hc : c ≠ 0) (L : Submodule ℤ E) :
    L ≃ₗ[ℤ] scaleSubmodule c L :=
  { toFun := fun x => ⟨c • (x : E), ⟨(x : E), x.2, rfl⟩⟩
    invFun := fun y => ⟨c⁻¹ • (y : E), by
      rcases y.2 with ⟨x, hx, hxy⟩
      change c • x = (y : E) at hxy
      rwa [← hxy, inv_smul_smul₀ hc]⟩
    map_add' := fun x y => Subtype.ext (smul_add c (x : E) (y : E))
    map_smul' := fun n x => Subtype.ext (by
      change c • (n • (x : E)) = n • (c • (x : E))
      rw [smul_comm])
    left_inv := fun x => Subtype.ext (inv_smul_smul₀ hc (x : E))
    right_inv := fun y => Subtype.ext (smul_inv_smul₀ hc (y : E)) }

omit [FiniteDimensional ℝ E] in
theorem discreteTopology_scaleSubmodule {c : ℝ} (hc : c ≠ 0) (L : Submodule ℤ E)
    [DiscreteTopology L] : DiscreteTopology (scaleSubmodule c L) := by
  let e := scaleSubmodule_equiv hc L
  refine DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.smul continuous_subtype_val

omit [FiniteDimensional ℝ E] in
theorem rk_scaleSubmodule {c : ℝ} (hc : c ≠ 0) (L : Submodule ℤ E) :
    rk (scaleSubmodule c L) = rk L :=
  (scaleSubmodule_equiv hc L).symm.finrank_eq

/-- Exact covolume scaling formula: `covol (c • L) = |c| ^ (rk L) * covol L`. -/
theorem covol_scaleSubmodule {c : ℝ} (hc : c ≠ 0) (L : Submodule ℤ E) [DiscreteTopology L] :
    covol (scaleSubmodule c L) = |c| ^ rk L * covol L := by
  have : DiscreteTopology (scaleSubmodule c L) := discreteTopology_scaleSubmodule hc L
  let r := rk L
  let bL : Basis (Fin r) ℤ L := Module.finBasis ℤ L
  let e := scaleSubmodule_equiv hc L
  let bS : Basis (Fin r) ℤ (scaleSubmodule c L) := bL.map e
  rw [covol_eq_sqrt_det_gram (scaleSubmodule c L) bS, covol_eq_sqrt_det_gram L bL]
  have hgram : Matrix.gram ℝ (fun i => (bS i : E)) = (c ^ 2) • Matrix.gram ℝ (fun i => (bL i : E)) := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.smul_apply, smul_eq_mul, bS, Basis.map_apply,
      e, scaleSubmodule_equiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hgram, Matrix.det_smul, Fintype.card_fin, Real.sqrt_mul (by positivity)]
  congr 1
  rw [show (c ^ 2) ^ r = (|c| ^ r) ^ 2 by rw [← sq_abs c, ← pow_mul, ← pow_mul, mul_comm],
    Real.sqrt_sq (by positivity)]

/-- Exact slope scaling formula: for `L ≠ ⊥` and `0 < c`,
`slope (c • L) = slope L - Real.log c`. -/
theorem slope_scaleSubmodule {c : ℝ} (hc : 0 < c) (L : Submodule ℤ E) [DiscreteTopology L]
    (hL0 : L ≠ ⊥) :
    ArakelovCovolume.slope (scaleSubmodule c L) = ArakelovCovolume.slope L - Real.log c := by
  have : DiscreteTopology (scaleSubmodule c L) := discreteTopology_scaleSubmodule hc.ne' L
  have hrpos : (0 : ℝ) < (rk L : ℝ) := Nat.cast_pos.mpr (rk_pos_of_ne_bot L hL0)
  unfold ArakelovCovolume.slope degAr
  rw [rk_scaleSubmodule hc.ne', covol_scaleSubmodule hc.ne', abs_of_pos hc,
    Real.log_mul (pow_pos hc _).ne' (covol_pos L).ne', Real.log_pow]
  field_simp [hrpos.ne']
  ring

/-! ### Concrete Inert-Prime Congruence Sublattice `NuLat ≤ latM` -/

section ConcreteInertSublattice

variable {Pl : Type*}

/-- Coordinate modulus `M_i = ∏_{w ∈ supp} q_w^{e_w i}` (differing ONLY at inert places when
`e w i = 0` for non-inert `w`). -/
def inertCoordMod (supp : Finset Pl) (q : Pl → ℕ) {r : ℕ} (e : Pl → Fin r → ℕ) (i : Fin r) : ℕ :=
  ∏ w ∈ supp, q w ^ e w i

lemma inertCoordMod_pos (supp : Finset Pl) {q : Pl → ℕ} (hq : ∀ w ∈ supp, 0 < q w)
    {r : ℕ} (e : Pl → Fin r → ℕ) (i : Fin r) : 0 < inertCoordMod supp q e i :=
  Finset.prod_pos fun w hw => pow_pos (hq w hw) _

/-- **Concrete Inert-Prime Congruence Sublattice `NuLat ≤ latM`**:
given a discrete lattice `latM ⊂ E` with `ℤ`-basis `bM : Basis (Fin r) ℤ latM`, finite place support
`supp`, local residue cardinalities `q w`, and local inert-prime congruence exponents `e w i`
(`e w i = 0` at all non-inert places `w`), `NuLat` is the `ℤ`-sublattice spanned by
`{ (∏_{w ∈ supp} q_w^{e_w i}) • bM i | i : Fin r }`. -/
def inertCongruenceSublattice {latM : Submodule ℤ E} {r : ℕ} (bM : Basis (Fin r) ℤ latM)
    (supp : Finset Pl) (q : Pl → ℕ) (e : Pl → Fin r → ℕ) : Submodule ℤ E :=
  Submodule.span ℤ (Set.range fun i : Fin r => ((inertCoordMod supp q e i : ℤ)) • (bM i : E))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem inertCongruenceSublattice_le {latM : Submodule ℤ E} {r : ℕ} (bM : Basis (Fin r) ℤ latM)
    (supp : Finset Pl) (q : Pl → ℕ) (e : Pl → Fin r → ℕ) :
    inertCongruenceSublattice bM supp q e ≤ latM := by
  rw [inertCongruenceSublattice, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact latM.smul_mem _ (bM i).2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Membership characterization: `x ∈ latM` lies in `NuLat` iff every basis coordinate `bM.repr x i`
is divisible by `inertCoordMod supp q e i = ∏_{w ∈ supp} q_w^{e_w i}`! -/
theorem mem_inertCongruenceSublattice_iff {latM : Submodule ℤ E} {r : ℕ}
    (bM : Basis (Fin r) ℤ latM) (supp : Finset Pl) (q : Pl → ℕ) (e : Pl → Fin r → ℕ)
    (x : latM) :
    (x : E) ∈ inertCongruenceSublattice bM supp q e ↔
      ∀ i : Fin r, (inertCoordMod supp q e i : ℤ) ∣ bM.repr x i := by
  let Nu := inertCongruenceSublattice bM supp q e
  constructor
  · intro hx
    -- Show `Nu ⊆ { y ∈ latM | ∀ i, M_i ∣ bM.repr y i }`
    let S : Submodule ℤ E :=
      { carrier := { v : E | ∃ y : latM, (y : E) = v ∧
          ∀ i : Fin r, (inertCoordMod supp q e i : ℤ) ∣ bM.repr y i }
        add_mem' := by
          rintro _ _ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
          exact ⟨y₁ + y₂, rfl, fun i => by rw [map_add]; exact dvd_add (h₁ i) (h₂ i)⟩
        zero_mem' := ⟨0, rfl, fun i => by simp⟩
        smul_mem' := by
          rintro c _ ⟨y, rfl, hy⟩
          exact ⟨c • y, rfl, fun i => by
            rw [map_zsmul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
            exact dvd_mul_of_dvd_right (hy i) c⟩ }
    have hNuS : Nu ≤ S := by
      change inertCongruenceSublattice bM supp q e ≤ S
      rw [inertCongruenceSublattice, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨(inertCoordMod supp q e j : ℤ) • bM j, rfl, fun i => ?_⟩
      rw [map_zsmul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Basis.repr_self]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
    obtain ⟨y, hyEq, hy⟩ := hNuS hx
    have hxy : y = x := Subtype.ext hyEq
    rwa [← hxy]
  · intro hdvd
    have hxsum : (x : E) = ∑ i : Fin r, bM.repr x i • (bM i : E) := by
      have h := congrArg Subtype.val (bM.sum_repr x)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h.symm
    rw [hxsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hdvd i
    rw [hk, mul_comm, mul_smul]
    exact Submodule.smul_mem _ k (Submodule.subset_span ⟨i, rfl⟩)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Full rank of the inert-prime congruence sublattice: `rk NuLat = rk latM`. -/
theorem rk_inertCongruenceSublattice {latM : Submodule ℤ E} [DiscreteTopology latM]
    {r : ℕ} (bM : Basis (Fin r) ℤ latM) (supp : Finset Pl) {q : Pl → ℕ}
    (hq : ∀ w ∈ supp, 0 < q w) (e : Pl → Fin r → ℕ) :
    rk (inertCongruenceSublattice bM supp q e) = rk latM := by
  let Nu := inertCongruenceSublattice bM supp q e
  have hNu_le : Nu ≤ latM := inertCongruenceSublattice_le bM supp q e
  have : DiscreteTopology Nu := discreteTopology_of_le hNu_le
  -- Explicit `ℤ`-linear equivalence `latM ≃ₗ[ℤ] Nu` scaling basis vector `i` by `M_i > 0`
  let φ : latM →ₗ[ℤ] Nu :=
    bM.constr ℤ fun i =>
      ⟨(inertCoordMod supp q e i : ℤ) • (bM i : E), Submodule.subset_span ⟨i, rfl⟩⟩
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply bM.repr.injective
    ext i
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have hval : ((φ x : Nu) : E) = ∑ j : Fin r, (bM.repr x j * (inertCoordMod supp q e j : ℤ)) • (bM j : E) := by
      conv_lhs => rw [← bM.sum_repr x]
      simp only [map_sum, map_zsmul, φ, Basis.constr_basis, Submodule.coe_sum, Submodule.coe_smul,
        mul_smul]
    have hx0 : ((φ x : Nu) : E) = 0 := congrArg Subtype.val hx
    rw [hx0] at hval
    have hM0 : (∑ j : Fin r, (bM.repr x j * (inertCoordMod supp q e j : ℤ)) • bM j : latM) = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum, Submodule.coe_smul] using hval.symm
    have hcoord := congrArg (fun y : latM => bM.repr y i) hM0
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Basis.repr_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
    rw [Finset.sum_eq_single i] at hcoord
    · simp only [Finsupp.single_eq_same, mul_one] at hcoord
      have hne : (inertCoordMod supp q e i : ℤ) ≠ 0 :=
        Int.natCast_ne_zero.mpr (inertCoordMod_pos supp hq e i).ne'
      exact (mul_eq_zero.mp hcoord).resolve_right hne
    · intro j _ hji; simp [Finsupp.single_eq_of_ne (Ne.symm hji)]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hφ_surj : Function.Surjective φ := by
    intro y
    have hyM : (y : E) ∈ latM := hNu_le y.2
    have hdvd := (mem_inertCongruenceSublattice_iff bM supp q e ⟨y.1, hyM⟩).mp y.2
    let c : Fin r → ℤ := fun i => bM.repr ⟨y.1, hyM⟩ i / (inertCoordMod supp q e i : ℤ)
    refine ⟨∑ i : Fin r, c i • bM i, ?_⟩
    apply Subtype.ext
    simp only [map_sum, map_zsmul, φ, Basis.constr_basis, Submodule.coe_sum, Submodule.coe_smul]
    have hySum : (y : E) = ∑ i : Fin r, bM.repr ⟨y.1, hyM⟩ i • (bM i : E) := by
      have h := congrArg Subtype.val (bM.sum_repr ⟨y.1, hyM⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h.symm
    rw [hySum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, Int.ediv_mul_cancel (hdvd i)]
  exact (LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).symm.finrank_eq

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exact Local Product Index Formula (`latIndex_inertCongruenceSublattice`)**:
`latIndex latM NuLat = ∏ w ∈ supp, q w ^ (∑ i : Fin r, e w i)`!
Proved unconditionally via the explicit quotient isomorphism
`latM ⧸ NuLat ≃ Π i : Fin r, ZMod (inertCoordMod supp q e i)`. -/
theorem latIndex_inertCongruenceSublattice {latM : Submodule ℤ E}
    {r : ℕ} (bM : Basis (Fin r) ℤ latM) (supp : Finset Pl) {q : Pl → ℕ}
    (hq : ∀ w ∈ supp, 0 < q w) (e : Pl → Fin r → ℕ) :
    latIndex latM (inertCongruenceSublattice bM supp q e) =
      ∏ w ∈ supp, q w ^ (∑ i : Fin r, e w i) := by
  let Nu := inertCongruenceSublattice bM supp q e
  let M : Fin r → ℕ := inertCoordMod supp q e
  have hMpos : ∀ i, 0 < M i := fun i => inertCoordMod_pos supp hq e i
  have : ∀ i, NeZero (M i) := fun i => ⟨(hMpos i).ne'⟩
  -- Build explicit surjective additive homomorphism `qHom : latM →+ Π i, ZMod (M i)` with kernel `Nu`!
  let qHom : latM →+ (∀ i : Fin r, ZMod (M i)) :=
    { toFun := fun x i => (bM.repr x i : ZMod (M i))
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp }
  have hker : qHom.ker = (Nu.comap latM.subtype).toAddSubgroup := by
    ext x
    change qHom x = 0 ↔ (x : E) ∈ inertCongruenceSublattice bM supp q e
    rw [mem_inertCongruenceSublattice_iff]
    constructor
    · intro hx i
      have hi : (bM.repr x i : ZMod (M i)) = 0 := congrFun hx i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (bM.repr x i) (M i)).mp hi
    · intro hdvd
      funext i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (bM.repr x i) (M i)).mpr (hdvd i)
  have hsurj : Function.Surjective qHom := by
    intro f
    refine ⟨∑ i : Fin r, ((f i).val : ℤ) • bM i, ?_⟩
    funext i
    simp only [qHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, map_zsmul,
      Finset.sum_apply, Pi.smul_apply, Basis.repr_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Finsupp.single_eq_of_ne (Ne.symm hji)]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hEquiv : (latM ⧸ (Nu.comap latM.subtype).toAddSubgroup) ≃ (∀ i : Fin r, ZMod (M i)) := by
    rw [← hker]
    exact (QuotientAddGroup.quotientKerEquivOfSurjective qHom hsurj).toEquiv
  unfold latIndex
  rw [AddSubgroup.index_eq_card, Nat.card_congr hEquiv, Nat.card_eq_fintype_card,
    Fintype.card_pi]
  simp_rw [ZMod.card, M, inertCoordMod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]

/-- **Exact Covolume of `NuLat` via `Stage11BostDworkSqueeze.covol_eq_index_mul_covol`**:
`covol NuLat = (∏ w ∈ supp, (q w : ℝ) ^ (∑ i, e w i)) * covol latM`! -/
theorem covol_inertCongruenceSublattice {latM : Submodule ℤ E} [DiscreteTopology latM]
    {r : ℕ} (bM : Basis (Fin r) ℤ latM) (supp : Finset Pl) {q : Pl → ℕ}
    (hq : ∀ w ∈ supp, 0 < q w) (e : Pl → Fin r → ℕ) :
    covol (inertCongruenceSublattice bM supp q e) =
      (∏ w ∈ supp, (q w : ℝ) ^ (∑ i : Fin r, e w i)) * covol latM := by
  have hle := inertCongruenceSublattice_le bM supp q e
  have hrk := rk_inertCongruenceSublattice bM supp hq e
  rw [covol_eq_index_mul_covol hle hrk, latIndex_inertCongruenceSublattice bM supp hq e]
  push_cast
  rfl

/-- **Exact Arakelov Slope Shift of the Rescaled Inert-Prime Congruence Lattice `latN = s_iu⁻¹ • NuLat`**:
for `latM ≠ ⊥` (`rk latM = r`) and fractional-ideal scaling factor `s_iu = ∏ w ∈ supp, q_w^(scaleExp w)`:
`slope latN - slope latM = (∑ w ∈ supp, scaleExp w * log q_w) - (∑ w ∈ supp, (∑ i, e w i) * log q_w) / r`! -/
theorem slope_shift_inertCongruence {latM : Submodule ℤ E} [DiscreteTopology latM]
    (hM0 : latM ≠ ⊥) {r : ℕ} (bM : Basis (Fin r) ℤ latM) (supp : Finset Pl) {q : Pl → ℕ}
    (hq : ∀ w ∈ supp, 0 < q w) (e : Pl → Fin r → ℕ) (scaleExp : Pl → ℝ) :
    let NuLat := inertCongruenceSublattice bM supp q e
    let s_iu : ℝ := ∏ w ∈ supp, (q w : ℝ) ^ scaleExp w
    let latN := scaleSubmodule s_iu⁻¹ NuLat
    slope latN - slope latM =
      (∑ w ∈ supp, scaleExp w * Real.log (q w : ℝ)) -
        (∑ w ∈ supp, ((∑ i : Fin r, e w i : ℕ) : ℝ) * Real.log (q w : ℝ)) / (rk latM : ℝ) := by
  intro NuLat s_iu latN
  have hle : NuLat ≤ latM := inertCongruenceSublattice_le bM supp q e
  have hrk : rk NuLat = rk latM := rk_inertCongruenceSublattice bM supp hq e
  have : DiscreteTopology NuLat := discreteTopology_of_le hle
  have hNu0 : NuLat ≠ ⊥ := by
    intro h0
    have hr0 : rk NuLat = 0 := by rw [h0]; simp [rk]
    have hrpos := rk_pos_of_ne_bot latM hM0
    omega
  have hs_pos : 0 < s_iu := Finset.prod_pos fun w hw =>
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hq w hw)) _
  have hlog_s : Real.log s_iu = ∑ w ∈ supp, scaleExp w * Real.log (q w : ℝ) := by
    unfold s_iu
    rw [Real.log_prod (fun w hw => (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hq w hw)) _).ne')]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Real.log_rpow (Nat.cast_pos.mpr (hq w hw))]
  have hlog_idx : Real.log (latIndex latM NuLat : ℝ) =
      ∑ w ∈ supp, ((∑ i : Fin r, e w i : ℕ) : ℝ) * Real.log (q w : ℝ) := by
    rw [latIndex_inertCongruenceSublattice bM supp hq e]
    push_cast
    rw [Real.log_prod (fun w hw => (pow_pos (Nat.cast_pos.mpr (hq w hw)) _).ne')]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow, Nat.cast_sum]
  have hslope_N : slope latN = slope NuLat + Real.log s_iu := by
    rw [show latN = scaleSubmodule s_iu⁻¹ NuLat from rfl,
      slope_scaleSubmodule (inv_pos.mpr hs_pos) NuLat hNu0, Real.log_inv]
    ring
  have hslope_Nu := slope_eq_slope_sub_log_index_div_rk hle hrk
  rw [hslope_N, hslope_Nu, hlog_s, hlog_idx]
  ring

end ConcreteInertSublattice

/-! ### Exact Arakelov Slope Decomposition (`slope latN - slope latM = Ga + Fo - Ee - Lo`) & `LinkG` -/

/-- **Inert-Prime Arakelov Congruence Package** (matching Alpöge's `DataDIVDefs` + `DataParams₂`):
bundles the finite set of places `supp`, inert-prime predicate `isInert`, local residue sizes `q w`,
ramification indices `ramIdx w`, lift range `lifts`, local gains `gainD`, indefinite/archimedean
terms `F`, `E`, local torsion/length offsets `tau`, `io`, and rounding losses `fracLoss`. -/
structure InertCongruenceData (Pl : Type*) where
  supp : Finset Pl
  isInert : Pl → Prop
  q : Pl → ℕ
  q_pos : ∀ w ∈ supp, 0 < q w
  q_ge_one : ∀ w ∈ supp, 1 ≤ q w
  ramIdx : Pl → ℕ
  degNorm : ℝ
  degNorm_pos : 0 < degNorm
  lifts : Finset ℕ
  gainD : ℕ → Pl → ℝ
  F : ℕ → Pl → ℝ
  E : ℕ → Pl → ℝ
  tau : Pl → ℝ
  io : Pl → ℝ
  fracLoss : Pl → ℝ

namespace InertCongruenceData

variable {Pl : Type*} (D : InertCongruenceData Pl)

/-- Local logarithmic place weight `lwP w = log q_w / degNorm ≥ 0`. -/
def lwP (w : Pl) : ℝ := Real.log (D.q w : ℝ) / D.degNorm

lemma lwP_nonneg {w : Pl} (hw : w ∈ D.supp) : 0 ≤ D.lwP w :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast D.q_ge_one w hw)) D.degNorm_pos.le

/-- Weighted local size `sz w y = lwP w * (ramIdx w * y)`. -/
def sz (w : Pl) (y : ℝ) : ℝ := D.lwP w * ((D.ramIdx w : ℝ) * y)

/-- Total local fractional-ideal exponent `sg w = ∑_{j ∈ lifts} (gainD j w + F j w - E j w)`. -/
def sg (w : Pl) : ℝ := ∑ j ∈ D.lifts, (D.gainD j w + D.F j w - D.E j w)

/-- Total inert-prime Dwork gain `Ga = ∑_{w ∈ supp} sz w ((∑_{j ∈ lifts} gainD j w) - tau w)`. -/
def Ga : ℝ := ∑ w ∈ D.supp, D.sz w ((∑ j ∈ D.lifts, D.gainD j w) - D.tau w)

/-- Total `F`-contribution `Fo = ∑_{j ∈ lifts} ∑_{w ∈ supp} sz w (F j w)`. -/
def Fo : ℝ := ∑ j ∈ D.lifts, ∑ w ∈ D.supp, D.sz w (D.F j w)

/-- Total `E`-contribution `Ee = ∑_{j ∈ lifts} ∑_{w ∈ supp} sz w (E j w)`. -/
def Ee : ℝ := ∑ j ∈ D.lifts, ∑ w ∈ D.supp, D.sz w (D.E j w)

/-- Total local index + rounding loss `Lo = ∑_{w ∈ supp} (sz w (io w) + lwP w * fracLoss w)`. -/
def Lo : ℝ := ∑ w ∈ D.supp, (D.sz w (D.io w) + D.lwP w * D.fracLoss w)

/-- Fractional-ideal rescaling exponent `scaleExp w = (ramIdx w * sg w - fracLoss w) / degNorm`. -/
def scaleExp (w : Pl) : ℝ := ((D.ramIdx w : ℝ) * D.sg w - D.fracLoss w) / D.degNorm

/-- **Exact Arakelov Slope Shift Identity (`slope_shift_eq_Ga_add_Fo_sub_Ee_sub_Lo`)**:
When the inert-prime congruence sublattice `NuLat ≤ latM` differs ONLY at inert places (`e w i = 0`
at non-inert places) with exact local length `(∑ i, e w i) / rk = (ramIdx w / degNorm) * (tau w + io w)`
and `latN = scaleSubmodule (∏ w, q_w^(scaleExp w))⁻¹ NuLat`:
**`slope latN - slope latM = D.Ga + D.Fo - D.Ee - D.Lo`** (with `tau w` cancelling identically!). -/
theorem slope_shift_eq_Ga_add_Fo_sub_Ee_sub_Lo {latM : Submodule ℤ E} [DiscreteTopology latM]
    (hM0 : latM ≠ ⊥) {r : ℕ} (bM : Basis (Fin r) ℤ latM)
    (e : Pl → Fin r → ℕ)
    (hlen : ∀ w ∈ D.supp,
      ((∑ i : Fin r, e w i : ℕ) : ℝ) / (rk latM : ℝ) =
        ((D.ramIdx w : ℝ) * (D.tau w + D.io w)) / D.degNorm) :
    let NuLat := inertCongruenceSublattice bM D.supp D.q e
    let s_iu : ℝ := ∏ w ∈ D.supp, (D.q w : ℝ) ^ D.scaleExp w
    let latN := scaleSubmodule s_iu⁻¹ NuLat
    slope latN - slope latM = D.Ga + D.Fo - D.Ee - D.Lo := by
  intro NuLat s_iu latN
  have hshift := slope_shift_inertCongruence hM0 bM D.supp D.q_pos e D.scaleExp
  rw [hshift]
  have hFo : D.Fo = ∑ w ∈ D.supp, D.sz w (∑ j ∈ D.lifts, D.F j w) := by
    unfold Fo sz
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hEe : D.Ee = ∑ w ∈ D.supp, D.sz w (∑ j ∈ D.lifts, D.E j w) := by
    unfold Ee sz
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hFo, hEe, Ga, Lo, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hsg : D.sg w = (∑ j ∈ D.lifts, D.gainD j w) + (∑ j ∈ D.lifts, D.F j w) -
      (∑ j ∈ D.lifts, D.E j w) := by
    unfold sg
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [mul_div_right_comm, hlen w hw]
  unfold scaleExp sz lwP
  rw [hsg]
  have hd : D.degNorm ≠ 0 := D.degNorm_pos.ne'
  field_simp [hd]
  ring

/-- **One-Sided Arakelov Slope Shift Bound (`slope_shift_ge_Ga_add_Fo_sub_Ee_sub_Lo`)**:
Matching Alpöge's `LinkG_at` (`lenMN u w ≤ duS u * (tau w + io w)`): whenever
`(∑ i, e w i) / rk ≤ (ramIdx w / degNorm) * (tau w + io w)` at every `w ∈ supp`,
**`slope latM + D.Ga + D.Fo - D.Ee - D.Lo ≤ slope latN`**! -/
theorem slope_shift_ge_Ga_add_Fo_sub_Ee_sub_Lo {latM : Submodule ℤ E} [DiscreteTopology latM]
    (hM0 : latM ≠ ⊥) {r : ℕ} (bM : Basis (Fin r) ℤ latM)
    (e : Pl → Fin r → ℕ)
    (hlen : ∀ w ∈ D.supp,
      ((∑ i : Fin r, e w i : ℕ) : ℝ) / (rk latM : ℝ) ≤
        ((D.ramIdx w : ℝ) * (D.tau w + D.io w)) / D.degNorm) :
    let NuLat := inertCongruenceSublattice bM D.supp D.q e
    let s_iu : ℝ := ∏ w ∈ D.supp, (D.q w : ℝ) ^ D.scaleExp w
    let latN := scaleSubmodule s_iu⁻¹ NuLat
    slope latM + D.Ga + D.Fo - D.Ee - D.Lo ≤ slope latN := by
  intro NuLat s_iu latN
  have hshift := slope_shift_inertCongruence hM0 bM D.supp D.q_pos e D.scaleExp
  have hFo : D.Fo = ∑ w ∈ D.supp, D.sz w (∑ j ∈ D.lifts, D.F j w) := by
    unfold Fo sz
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hEe : D.Ee = ∑ w ∈ D.supp, D.sz w (∑ j ∈ D.lifts, D.E j w) := by
    unfold Ee sz
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hle_sum :
      D.Ga + D.Fo - D.Ee - D.Lo ≤
        (∑ w ∈ D.supp, D.scaleExp w * Real.log (D.q w : ℝ)) -
          (∑ w ∈ D.supp, ((∑ i : Fin r, e w i : ℕ) : ℝ) * Real.log (D.q w : ℝ)) / (rk latM : ℝ) := by
    rw [hFo, hEe, Ga, Lo, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have hlog_nn : 0 ≤ Real.log (D.q w : ℝ) := Real.log_nonneg (by exact_mod_cast D.q_ge_one w hw)
    have hterm_le := mul_le_mul_of_nonneg_right (hlen w hw) hlog_nn
    have hsg : D.sg w = (∑ j ∈ D.lifts, D.gainD j w) + (∑ j ∈ D.lifts, D.F j w) -
        (∑ j ∈ D.lifts, D.E j w) := by
      unfold sg
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have heq : D.sz w ((∑ j ∈ D.lifts, D.gainD j w) - D.tau w) +
          D.sz w (∑ j ∈ D.lifts, D.F j w) - D.sz w (∑ j ∈ D.lifts, D.E j w) -
          (D.sz w (D.io w) + D.lwP w * D.fracLoss w) =
        D.scaleExp w * Real.log (D.q w : ℝ) -
          (((D.ramIdx w : ℝ) * (D.tau w + D.io w)) / D.degNorm) * Real.log (D.q w : ℝ) := by
      unfold scaleExp sz lwP
      rw [hsg]
      have hd : D.degNorm ≠ 0 := D.degNorm_pos.ne'
      field_simp [hd]
      ring
    rw [heq]
    have hmul_div : ((∑ i : Fin r, e w i : ℕ) : ℝ) * Real.log (D.q w : ℝ) / (rk latM : ℝ) =
        ((∑ i : Fin r, e w i : ℕ) : ℝ) / (rk latM : ℝ) * Real.log (D.q w : ℝ) := by ring
    rw [hmul_div]
    linarith
  linarith

end InertCongruenceData

/-! ### Von Mangoldt Prime-Power Ramp `ASK` & `linkG_inert_ramp_shift` -/

/-- **Inert-Prime Von Mangoldt Class Ramp** (matching Alpöge's `SizeData₂.vonMangoldtClassSum`):
`∑_{i < log_p(aT) + 2, Odd i} max(0, aT / p^i - wPart i)`. -/
def vonMangoldtRamp (p aT : ℕ) (wPart : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Nat.log p aT + 2),
    if Odd i then max 0 ((aT : ℝ) / (p : ℝ) ^ i - wPart i) else 0

/-- **Ramp-to-Integer-Floor Comparison (`vonMangoldtRamp_le_odd_floor_sum`)**:
Whenever `1 ≤ wPart i` (matching `SizeData₂.wPart_ge`), every odd-power term of `vonMangoldtRamp`
is bounded above by the exact Euclidean floor `⌊aT / p^i⌋ = aT / p^i`! -/
theorem vonMangoldtRamp_le_odd_floor_sum {p : ℕ} (hp : p.Prime) (aT : ℕ) (wPart : ℕ → ℝ)
    (hw : ∀ i, 1 ≤ wPart i) :
    vonMangoldtRamp p aT wPart ≤
      ∑ i ∈ Finset.range (Nat.log p aT + 2),
        if Odd i then ((aT / p ^ i : ℕ) : ℝ) else 0 := by
  unfold vonMangoldtRamp
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with ho
  · refine max_le (Nat.cast_nonneg _) ?_
    have hpow_pos : (0 : ℝ) < (p : ℝ) ^ i := pow_pos (by exact_mod_cast hp.pos) i
    have hdiv_lt : (aT : ℝ) / (p : ℝ) ^ i < ((aT / p ^ i : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hpow_pos]
      have hmod : aT % p ^ i < p ^ i := Nat.mod_lt aT (pow_pos hp.pos i)
      have heuclid : aT = p ^ i * (aT / p ^ i) + aT % p ^ i := (Nat.div_add_mod aT (p ^ i)).symm
      have hlt_nat : aT < p ^ i * (aT / p ^ i) + p ^ i := by omega
      have hlt_R : (aT : ℝ) < ((p ^ i * (aT / p ^ i) + p ^ i : ℕ) : ℝ) := by exact_mod_cast hlt_nat
      push_cast at hlt_R
      linarith
    linarith [hw i]
  · exact le_rfl

/-- **Odd-Power Floor Sum ≤ Legendre Factorial Valuation (`odd_floor_sum_le_padicValNat_factorial`)**:
The odd-`i` inert-prime floor sum is bounded above by the exact `p`-adic valuation `v_p(aT!)`! -/
theorem odd_floor_sum_le_padicValNat_factorial {p : ℕ} (hp : p.Prime) (aT : ℕ) :
    (∑ i ∈ Finset.range (Nat.log p aT + 2), if Odd i then ((aT / p ^ i : ℕ) : ℝ) else 0) ≤
      (padicValNat p aT.factorial : ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg := padicValNat_factorial (p := p) (n := aT) (b := Nat.log p aT + 2)
    (by omega : Nat.log p aT < Nat.log p aT + 2)
  have hlegR : (padicValNat p aT.factorial : ℝ) =
      ∑ i ∈ Finset.Ico 1 (Nat.log p aT + 2), ((aT / p ^ i : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hleg
    simpa [Nat.cast_sum] using h
  rw [hlegR]
  have hsplit : Finset.range (Nat.log p aT + 2) =
      insert 0 (Finset.Ico 1 (Nat.log p aT + 2)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hnot0 : ¬ Odd (0 : ℕ) := by decide
  rw [if_neg hnot0, zero_add]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _

/-- **Global Inert-Prime Von Mangoldt Ramp Sum `ASK`** (matching Alpöge's `LocalQuadraticParts.ASK`):
summed over inert places `w ∈ supp`, lifts `j ∈ lifts`, and top weights `t ∈ TTw w`. -/
def ASK {Pl Top : Type*} (D : InertCongruenceData Pl)
    (resChar : Pl → ℕ) (TTw : Pl → Finset Top) (aT : Top → ℕ)
    (wPart : ℕ → Top → ℕ → ℕ → ℝ) : ℝ :=
  ∑ w ∈ D.supp, D.sz w (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
    vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)))

/-- **LinkG Inert-Prime Ramp Shift (`linkG_inert_ramp_shift`)**:
If at every place `w ∈ supp` (inert or dropped), the `m`-step Dwork `p`-adic divisibility bound
(`LinkG_at`) gives
`(∑_{j ∈ lifts} ∑_{t ∈ TTw w} (vonMangoldtRamp j t p - loG w)) - flG_tot w - dropPen w ≤ (∑_{j ∈ lifts} gainD j w) - tau w`,
then summing over `w ∈ supp` weighted by `sz w ≥ 0` yields **`ASK - rampLoss ≤ Ga`**! -/
theorem linkG_inert_ramp_shift {Pl Top : Type*} (D : InertCongruenceData Pl)
    (resChar : Pl → ℕ) (TTw : Pl → Finset Top) (aT : Top → ℕ)
    (wPart : ℕ → Top → ℕ → ℕ → ℝ) (loG flG_tot dropPen : Pl → ℝ)
    (hLinkG : ∀ w ∈ D.supp,
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
        (vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)) - loG w)) -
        flG_tot w - dropPen w ≤
      (∑ j ∈ D.lifts, D.gainD j w) - D.tau w) :
    let rampLoss : ℝ :=
      ∑ w ∈ D.supp, D.sz w ((D.lifts.card : ℝ) * (TTw w).card * loG w + flG_tot w + dropPen w)
    ASK D resChar TTw aT wPart - rampLoss ≤ D.Ga := by
  intro rampLoss
  unfold ASK InertCongruenceData.Ga
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have hsz_nn : 0 ≤ D.lwP w * (D.ramIdx w : ℝ) :=
    mul_nonneg (D.lwP_nonneg hw) (Nat.cast_nonneg _)
  have h1 := hLinkG w hw
  have hsum_lo : ∑ j ∈ D.lifts, ∑ t ∈ TTw w,
      (vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)) - loG w) =
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w, vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w))) -
        (D.lifts.card : ℝ) * (TTw w).card * loG w := by
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum_lo] at h1
  unfold InertCongruenceData.sz
  have hmul := mul_le_mul_of_nonneg_left h1 hsz_nn
  linarith

/-- **Culminating Stage 12 Bridge (`inert_sublattice_slope_shift_ge_ASK`)**:
Combining the concrete inert-prime congruence sublattice `latN = Iu • NuLat ≤ latM` (via
`Stage11BostDworkSqueeze.covol_eq_index_mul_covol`) with `linkG_inert_ramp_shift` yields the
complete non-circular Arakelov slope shift driven directly by the inert-prime von Mangoldt ramp sum:
**`slope latM + ASK + Fo - Ee - (Lo + rampLoss) ≤ slope latN`**! -/
theorem inert_sublattice_slope_shift_ge_ASK {Pl Top : Type*}
    (D : InertCongruenceData Pl) {latM : Submodule ℤ E} [DiscreteTopology latM]
    (hM0 : latM ≠ ⊥) {r : ℕ} (bM : Basis (Fin r) ℤ latM)
    (e : Pl → Fin r → ℕ)
    (hlen : ∀ w ∈ D.supp,
      ((∑ i : Fin r, e w i : ℕ) : ℝ) / (rk latM : ℝ) ≤
        ((D.ramIdx w : ℝ) * (D.tau w + D.io w)) / D.degNorm)
    (resChar : Pl → ℕ) (TTw : Pl → Finset Top) (aT : Top → ℕ)
    (wPart : ℕ → Top → ℕ → ℕ → ℝ) (loG flG_tot dropPen : Pl → ℝ)
    (hLinkG : ∀ w ∈ D.supp,
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
        (vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)) - loG w)) -
        flG_tot w - dropPen w ≤
      (∑ j ∈ D.lifts, D.gainD j w) - D.tau w) :
    let NuLat := inertCongruenceSublattice bM D.supp D.q e
    let s_iu : ℝ := ∏ w ∈ D.supp, (D.q w : ℝ) ^ D.scaleExp w
    let latN := scaleSubmodule s_iu⁻¹ NuLat
    let rampLoss : ℝ :=
      ∑ w ∈ D.supp, D.sz w ((D.lifts.card : ℝ) * (TTw w).card * loG w + flG_tot w + dropPen w)
    slope latM + ASK D resChar TTw aT wPart + D.Fo - D.Ee - (D.Lo + rampLoss) ≤ slope latN := by
  intro NuLat s_iu latN rampLoss
  have hslope := D.slope_shift_ge_Ga_add_Fo_sub_Ee_sub_Lo hM0 bM e hlen
  have hlink := linkG_inert_ramp_shift D resChar TTw aT wPart loG flG_tot dropPen hLinkG
  linarith

end InertCongruenceSlopeShift

end

end RHDirect.Stage12MultivarDwork
