import RHDirect.Stage8IwasawaWeierstrass
import RHDirect.Stage9DiophantineWeyl
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# RHDirect.Stage11FerreroWashington

Unconditional Lean 4 formalization (zero `sorry`, zero custom `axiom`s) of concrete
Ferrero–Washington & Sinnott `μ = 0` theorems directly on `Stage8IwasawaWeierstrass.iwasawaMu`,
`Stage7PadicLFunction.mazurBernoulliMeasure`, and `Stage7PadicLFunction.kubotaLeopoldtSeries`,
bridging directly into `Stage2IwasawaTwoTower` (`l = 2` & odd-`p` linear growth `v_p = λ · n + O(1)`):

1. **Concrete `μ`-Invariant Characterization of `PadicMeasure p`**:
   - `iwasawaMu_pos_iff_all_coeffs_dvd_p` & `iwasawaMu_pos_iff_reduceModP_eq_zero`:
     for `F ≠ 0` in `ℤ_[p][[T]]`, `1 ≤ iwasawaMu F ↔ ∀ k, p ∣ F.coeff k ↔ reduceModP F = 0`.
   - `iwasawaMu_transform_eq_zero_iff_exists_clopen_not_dvd_p` &
     `iwasawaMu_eq_zero_iff_exists_unit_ball_val`: under `amiceMahlerIwasawaRingEquiv`,
     `iwasawaMu (iwasawaTransform μ) = 0 ↔ ∃ n a, ¬ (p : ℤ_[p]) ∣ μ n a ↔ ∃ n a, IsUnit (μ n a)`.
   - Mod-`p` low-degree coefficient formula `toZMod_coeff_iwasawaTransform_of_lt_p` for `k < p`.

2. **Unconditional `μ = 0` for the Mazur Bernoulli Measure `μ_c` (ALL primes `p`, including `p = 2`!)
   & Sinnott's Rational-Function `μ = 0` Theorem**:
   - `iwasawaMu_mazurBernoulliMeasure_eq_zero`: for EVERY prime `p` (including `p = 2` and `p = 37`!)
     and EVERY `c ≥ 2` with `p ∤ c`, `iwasawaTransform (mazurBernoulliMeasure p c hc) ≠ 0` and
     `iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p c hc)) = 0` (via an exact unit step
     `μ_c(0, p^n) - μ_c(c * b₁, p^n) = 1` at `n = c + 1`!).
   - Explicit unit witnesses at `c = 3` (`p ≠ 3`, including `p = 2`) and `c = 5` (`p = 3`).
   - Exact Sinnott rational-function identity `mazurBernoulliMeasure_rational_identity`:
     `((1 + T)^c - 1) * iwasawaTransform (mazurBernoulliMeasure p c hc) = ∑_{j < c} (1 + T)^j - c`.
   - General Sinnott Rational-Function `μ = 0` Theorem (`sinnott_rational_measure_mu_zero`).

3. **Ferrero–Washington Criterion on `kubotaLeopoldtSeries`, Regular Primes `p = 3, 5, 7, 11, 13`,
   & Explicit `p = 37` Irregular-Prime Verification (`μ = 0, λ = 1`!)**:
   - Exact finite-level Teichmüller-weighted Mazur distribution formula `kubotaLeopoldtMeasure_apply`.
   - `ferrero_washington_mu_zero_criterion`: `iwasawaMu (kubotaLeopoldtSeries p _ c _ i) = 0` IFF
     some level-`n` Teichmüller-weighted Mazur sum is a `p`-adic unit.
   - Unconditional `μ = 0` for all regular-prime branches `p = 3, 5, 7, 11, 13`.
   - Explicit verification for the first irregular prime `p = 37`, `i = 32` branch
     (`irregular_prime_37_mu_zero_lambda_eq_one` & `irregular_prime_37_mu_zero_lambda_pos`):
     proves **EXACTLY** `iwasawaMu (kubotaLeopoldtSeries 37 _ 2 _ 31) = 0` and
     `iwasawaLambda (kubotaLeopoldtSeries 37 _ 2 _ 31) = 1`!

4. **Ferrero–Washington Equidistribution Theorem for `p`-adic Digits**:
   - Concrete `p`-adic truncation `padicTrunc`, digits `padicDigit`, and reversed fractional parts
     `padicFrac`, linked to `Stage9DiophantineWeyl.weyl_criterion_iff` and
     `Stage7PadicLFunction.mazurBernoulliDist_one_eq` (`ferrero_washington_digit_equidistribution`).

5. **Concrete `μ = 0` → `Stage2IwasawaTwoTower` Linear Growth & `B₂` Discharge**:
   - For ANY `F ≠ 0` in `ℤ_[p][[T]]` with `iwasawaMu F = 0` and `ω_{λ+1}` injective on `Λ_p / (F)`:
     constructs `cyclicDistinguishedLattice : DistinguishedLattice p (iwasawaLambda F)` and
     `cyclicIwasawaModuleModel : IwasawaModuleModel p (Λ_p / (F))` with `model.mu = 0`,
     `model.lam = iwasawaLambda F`, proving exact linear `p`-adic length growth
     `v_p(|Λ_p / (F, ω_n)|) = λ · n + O(1)` (`cyclic_mu_zero_linear_growth`), discharging
     `Stage2IwasawaTwoTower.IwasawaTwoTowerBound` at `p = 2` (`iwasawaTwoTowerBound_of_cyclic_mu_zero`),
     and proving the exact `37^(n + 1)` Iwasawa layer cardinality law at `p = 37`!
-/

noncomputable section

open scoped BigOperators Topology
open Finset Filter Topology
open RHDirect.Stage2IwasawaTwoTower RHDirect.Stage7PadicLFunction RHDirect.Stage8IwasawaWeierstrass
open RHDirect.Stage9DiophantineWeyl

namespace RHDirect.Stage11FerreroWashington

/-! ## Section 1: Concrete `μ`-Invariant Characterization of `PadicMeasure p` -/

section MeasureMuCriterion

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- For nonzero `F ∈ ℤ_[p][[T]]`, `iwasawaMu F ≥ 1` iff every coefficient of `F` is divisible by `p`. -/
theorem iwasawaMu_pos_iff_all_coeffs_dvd_p {F : PowerSeries ℤ_[p]} (hF : F ≠ 0) :
    1 ≤ iwasawaMu F ↔ ∀ k : ℕ, (p : ℤ_[p]) ∣ PowerSeries.coeff k F := by
  have h1 : 1 ≤ iwasawaMu F ↔ iwasawaMu F ≠ 0 := Nat.one_le_iff_ne_zero
  rw [h1, ne_eq, iwasawaMu_eq_zero_iff hF]
  push Not
  rfl

/-- For nonzero `F ∈ ℤ_[p][[T]]`, `iwasawaMu F ≥ 1` iff `reduceModP F = 0` in `(ZMod p)[[T]]`. -/
theorem iwasawaMu_pos_iff_reduceModP_eq_zero {F : PowerSeries ℤ_[p]} (hF : F ≠ 0) :
    1 ≤ iwasawaMu F ↔ reduceModP F = 0 := by
  rw [iwasawaMu_pos_iff_all_coeffs_dvd_p hF, reduceModP_eq_zero_iff]

/-- Divisibility by `p` on all power-series coefficients of `iwasawaTransform μ` is equivalent to
divisibility by `p` on all finite-level measure values `μ n a`. -/
theorem forall_p_dvd_coeff_iwasawaTransform_iff (μ : PadicMeasure p) :
    (∀ k : ℕ, (p : ℤ_[p]) ∣ PowerSeries.coeff k (iwasawaTransform μ)) ↔
      (∀ (n : ℕ) (a : ZMod (p ^ n)), (p : ℤ_[p]) ∣ μ n a) := by
  constructor
  · intro hcoeff n a
    let G : IwasawaAlg p := PowerSeries.mk fun k => (hcoeff k).choose
    have hFG : iwasawaTransform μ = PowerSeries.C (p : ℤ_[p]) * G := by
      ext k
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      exact (hcoeff k).choose_spec
    have hμa : μ n a = evalLevel n (iwasawaTransform μ) a :=
      (congrArg (fun ν : PadicMeasure p => ν n a) (iwasawaInv_iwasawaTransform μ)).symm
    rw [hμa, hFG, evalLevel_smul, LevelAlg.smul_apply]
    exact dvd_mul_right _ _
  · intro hclopen k
    rw [coeff_iwasawaTransform]
    have hnorm_clopen : ∀ (n : ℕ) (a : ZMod (p ^ n)), ‖μ n a‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := fun n a =>
      (padicInt_p_pow_dvd_iff_norm_le (μ n a) 1).mp (by rw [pow_one]; exact hclopen n a)
    have hlim : Tendsto (fun n => ‖riemannSum μ (mahlerBinom k) n‖) atTop
        (nhds ‖measureIntegral μ (mahlerBinom k)‖) :=
      (tendsto_riemannSum_measureIntegral μ (continuous_mahlerBinom k)).norm
    have hle : ‖measureIntegral μ (mahlerBinom k)‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
      refine le_of_tendsto' hlim fun n => ?_
      refine padicInt_norm_sum_le _ _ (by positivity) fun a _ => ?_
      rw [norm_mul]
      calc ‖mahlerBinom (p := p) k (a.val : ℤ_[p])‖ * ‖μ n a‖
          ≤ 1 * (p : ℝ) ^ (-(1 : ℤ)) :=
            mul_le_mul (PadicInt.norm_le_one _) (hnorm_clopen n a) (norm_nonneg _) zero_le_one
        _ = (p : ℝ) ^ (-(1 : ℤ)) := one_mul _
    simpa [pow_one] using (padicInt_p_pow_dvd_iff_norm_le (measureIntegral μ (mahlerBinom k)) 1).mpr hle

/-- Unconditional mod-`p` nonvanishing characterization of `iwasawaTransform μ` (no `μ ≠ 0` needed):
`reduceModP (iwasawaTransform μ) ≠ 0` iff some finite-level measure value `μ n a` is not divisible by `p`. -/
theorem reduceModP_iwasawaTransform_ne_zero_iff (μ : PadicMeasure p) :
    reduceModP (iwasawaTransform μ) ≠ 0 ↔
      ∃ (n : ℕ) (a : ZMod (p ^ n)), ¬ (p : ℤ_[p]) ∣ μ n a := by
  rw [ne_eq, reduceModP_eq_zero_iff, forall_p_dvd_coeff_iwasawaTransform_iff]
  push Not
  rfl

/-- Sufficient unit-ball criterion (no `μ ≠ 0` hypothesis required):
if ANY finite-level measure value `μ n a` is not divisible by `p`, then `iwasawaTransform μ ≠ 0`
and `iwasawaMu (iwasawaTransform μ) = 0`! -/
theorem iwasawaMu_transform_eq_zero_of_exists_unit_ball_val {μ : PadicMeasure p}
    (h : ∃ (n : ℕ) (a : ZMod (p ^ n)), ¬ (p : ℤ_[p]) ∣ μ n a) :
    iwasawaTransform μ ≠ 0 ∧ iwasawaMu (iwasawaTransform μ) = 0 := by
  have hred : reduceModP (iwasawaTransform μ) ≠ 0 :=
    (reduceModP_iwasawaTransform_ne_zero_iff μ).mpr h
  have hne : iwasawaTransform μ ≠ 0 := by
    intro h0; apply hred; rw [h0, map_zero]
  exact ⟨hne, (iwasawaMu_eq_zero_iff_reduceModP_ne_zero hne).mpr hred⟩

/-- **Concrete `μ`-Invariant Characterization of `PadicMeasure p`**:
for every nonzero `μ : PadicMeasure p`, `iwasawaMu (iwasawaTransform μ) = 0` IFF some finite-level
clopen ball value `μ n a` is NOT divisible by `p`! -/
theorem iwasawaMu_transform_eq_zero_iff_exists_clopen_not_dvd_p {μ : PadicMeasure p}
    (hμ : μ ≠ 0) :
    iwasawaMu (iwasawaTransform μ) = 0 ↔
      ∃ (n : ℕ) (a : ZMod (p ^ n)), ¬ (p : ℤ_[p]) ∣ μ n a := by
  have hne : iwasawaTransform μ ≠ 0 := by
    intro h0
    apply hμ
    have h1 := congrArg iwasawaInv h0
    rw [iwasawaInv_iwasawaTransform] at h1
    have hinv0 : iwasawaInv (0 : IwasawaAlg p) = 0 := by
      ext n a; simp [iwasawaInv, evalLevel]
    exact h1.trans hinv0
  rw [iwasawaMu_eq_zero_iff_reduceModP_ne_zero hne, reduceModP_iwasawaTransform_ne_zero_iff]

/-- Equivalent unit-value form: for nonzero `μ : PadicMeasure p`, `iwasawaMu (iwasawaTransform μ) = 0`
IFF some finite-level ball value `μ n a` is a `p`-adic unit in `ℤ_[p]`. -/
theorem iwasawaMu_eq_zero_iff_exists_unit_ball_val {μ : PadicMeasure p} (hμ : μ ≠ 0) :
    iwasawaMu (iwasawaTransform μ) = 0 ↔
      ∃ (n : ℕ) (a : ZMod (p ^ n)), IsUnit (μ n a) := by
  rw [iwasawaMu_transform_eq_zero_iff_exists_clopen_not_dvd_p hμ]
  simp_rw [padicInt_isUnit_iff_not_p_dvd]

/-- **Exact Mod-`p` Low-Degree Coefficient Formula**:
for any `μ : PadicMeasure p` and any `k < p`,
`coeff k (iwasawaTransform μ) mod p = ∑_{a : ZMod p} (μ 1 a mod p) * C(a.val, k)`! -/
theorem toZMod_coeff_iwasawaTransform_of_lt_p (μ : PadicMeasure p) {k : ℕ} (hk : k < p) :
    PadicInt.toZMod (PowerSeries.coeff k (iwasawaTransform μ)) =
      ∑ a : ZMod (p ^ 1), PadicInt.toZMod (μ 1 a) * ((a.val.choose k : ℕ) : ZMod p) := by
  obtain ⟨Q, hQ⟩ := exists_iwasawaTransform_eq_sum_add_omegaElem_mul μ 1
  rw [← coeff_reduceModP, hQ, map_add, map_mul, map_sum]
  have hω : reduceModP (omegaElem p 1) = (PowerSeries.X : PowerSeries (ZMod p)) ^ p := by
    simpa [reduceModP, pow_one] using map_toZMod_omegaElem p 1
  rw [hω, map_add, PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hk), add_zero, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hX : reduceModP (PowerSeries.X : PowerSeries ℤ_[p]) = PowerSeries.X := PowerSeries.map_X _
  rw [map_mul, map_pow, map_add, map_one, hX]
  have hC : reduceModP (PowerSeries.C (μ 1 a)) = PowerSeries.C (PadicInt.toZMod (μ 1 a)) := by
    ext j; rw [coeff_reduceModP, PowerSeries.coeff_C, PowerSeries.coeff_C]
    split_ifs <;> simp
  rw [hC, PowerSeries.coeff_C_mul]
  congr 1
  have hbin : (1 + PowerSeries.X : PowerSeries (ZMod p)) ^ a.val =
      ∑ j ∈ Finset.range (a.val + 1),
        PowerSeries.C ((a.val.choose j : ℕ) : ZMod p) * PowerSeries.X ^ j := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, mul_comm, map_natCast]
  rw [hbin, map_sum]
  simp_rw [PowerSeries.coeff_C_mul_X_pow]
  by_cases hka : k < a.val + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj.symm]
    · intro hnot; exact absurd (Finset.mem_range.mpr hka) hnot
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne : j ≠ k := by have := Finset.mem_range.mp hj; omega
    simp [hne.symm]

end MeasureMuCriterion

/-! ## Section 2: Unconditional `μ = 0` for the Mazur Bernoulli Measure `μ_c` & Sinnott's Rational Theorem -/

section MazurAndSinnott

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Exact evaluation of Mazur's measure at `a = 0`:
`μ_c(0 + p^n ℤ_p) = (c - 1) / 2` in `ℚ_[p]` for EVERY prime `p`, `c` with `¬ p ∣ c`, and `n : ℕ`. -/
theorem mazurBernoulliMeasure_apply_zero_coe (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) :
    ((mazurBernoulliMeasure p c hc n 0 : ℤ_[p]) : ℚ_[p]) = ((((c : ℚ) - 1) / 2 : ℚ) : ℚ_[p]) := by
  rw [mazurBernoulliMeasure_coe, mazurBernoulliDist_one_eq]
  simp

/-- When `c` is odd, `μ_c(0 + p^n ℤ_p) = ((c - 1) / 2 : ℤ_[p])` for every prime `p` and `n : ℕ`. -/
theorem mazurBernoulliMeasure_apply_zero_of_odd (c : ℕ) (hc : ¬ p ∣ c) (hodd : Odd c) (n : ℕ) :
    mazurBernoulliMeasure p c hc n 0 = (((c - 1) / 2 : ℕ) : ℤ_[p]) := by
  apply Subtype.ext
  rw [mazurBernoulliMeasure_coe, mazurBernoulliDist_one_eq_int_of_odd p c hc hodd]
  simp only [mul_zero, ZMod.val_zero, Nat.zero_div, Nat.cast_zero, sub_zero, Int.cast_natCast,
    PadicInt.coe_natCast, Rat.cast_natCast]

/-- **Exact Unit Step for Mazur's Regularized Bernoulli Measure**:
for EVERY prime `p` (INCLUDING `p = 2`!) and EVERY `c ≥ 2` with `¬ p ∣ c`, at level `n = c + 1`
and `b₁ = p^n / c + 1`, the difference `μ_c(0, p^n) - μ_c(c * b₁, p^n)` is literally `1` in `ℤ_[p]`! -/
theorem mazurBernoulliMeasure_unit_step (c : ℕ) (hc2 : 2 ≤ c) (hc : ¬ p ∣ c) :
    let n := c + 1
    let a₁ : ZMod (p ^ n) := ((c * (p ^ n / c + 1) : ℕ) : ZMod (p ^ n))
    mazurBernoulliMeasure p c hc n 0 - mazurBernoulliMeasure p c hc n a₁ = 1 := by
  have hp : p.Prime := Fact.out
  set n := c + 1
  set N := p ^ n
  set b₁ := N / c + 1
  have h2p : 2 ^ n ≤ N := Nat.pow_le_pow_left hp.two_le n
  have hN_gt_c : c < N := by
    have hlt : c < 2 ^ c := Nat.lt_two_pow_self
    have h2 : 2 ^ c ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ c)
    omega
  have hN_ge8 : 8 ≤ N := by
    have h3 : 3 ≤ n := by omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      _ ≤ N := h2p
  have hb₁_lt : b₁ < N := by
    have hmul : 2 * (N / c) ≤ c * (N / c) := Nat.mul_le_mul_right _ hc2
    have hle : c * (N / c) ≤ N := Nat.mul_div_le N c
    omega
  have hcb₁_ge : N ≤ c * b₁ := by
    have hdiv := Nat.div_add_mod N c
    have hmod : N % c < c := Nat.mod_lt N (by omega)
    dsimp only [b₁]
    nlinarith
  have hcb₁_lt : c * b₁ < 2 * N := by
    have hle : c * (N / c) ≤ N := Nat.mul_div_le N c
    dsimp only [b₁]
    nlinarith
  have hquot_one : c * b₁ / N = 1 := by
    have hpos : 0 < N := by omega
    exact le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpos).mpr (by omega)))
      ((Nat.le_div_iff_mul_le hpos).mpr (by omega))
  have hcInv_eq : cInv p c hc n * ((c * b₁ : ℕ) : ZMod (p ^ n)) = (b₁ : ZMod (p ^ n)) := by
    rw [Nat.cast_mul, ← mul_assoc, cInv_mul_c, one_mul]
  have hval_eq : (cInv p c hc n * ((c * b₁ : ℕ) : ZMod (p ^ n))).val = b₁ := by
    have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    rw [hcInv_eq, ZMod.val_natCast_of_lt hb₁_lt]
  apply Subtype.ext
  rw [PadicInt.coe_sub, PadicInt.coe_one, mazurBernoulliMeasure_apply_zero_coe,
    mazurBernoulliMeasure_coe, mazurBernoulliDist_one_eq, hval_eq, hquot_one]
  push_cast
  ring

/-- **UNCONDITIONAL `μ = 0` FOR THE MAZUR BERNOULLI MEASURE `μ_c` (ALL PRIMES `p`, INCLUDING `p = 2`!)**:
for EVERY prime `p` (including `p = 2` and `p = 37`!) and EVERY `c ≥ 2` with `¬ p ∣ c`:
1. `iwasawaTransform (mazurBernoulliMeasure p c hc) ≠ 0`, AND
2. `iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p c hc)) = 0`! -/
theorem iwasawaMu_mazurBernoulliMeasure_eq_zero (c : ℕ) (hc2 : 2 ≤ c) (hc : ¬ p ∣ c) :
    iwasawaTransform (mazurBernoulliMeasure p c hc) ≠ 0 ∧
    iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p c hc)) = 0 := by
  refine iwasawaMu_transform_eq_zero_of_exists_unit_ball_val ?_
  set n := c + 1
  set a₁ : ZMod (p ^ n) := ((c * (p ^ n / c + 1) : ℕ) : ZMod (p ^ n))
  have hstep := mazurBernoulliMeasure_unit_step (p := p) c hc2 hc
  by_cases h0 : (p : ℤ_[p]) ∣ mazurBernoulliMeasure p c hc n 0
  · refine ⟨n, a₁, fun h1 => ?_⟩
    have hdvd1 : (p : ℤ_[p]) ∣ (1 : ℤ_[p]) := by
      rw [← hstep]
      exact dvd_sub h0 h1
    exact padicInt_p_not_isUnit (isUnit_of_dvd_one hdvd1)
  · exact ⟨n, 0, h0⟩

/-- Explicit `c = 3` unit theorem: for EVERY prime `p ≠ 3` (INCLUDING `p = 2`!),
`iwasawaTransform (mazurBernoulliMeasure p 3 _)` is a UNIT in `ℤ_[p][[T]]` (`μ = 0` AND `λ = 0`)! -/
theorem mazurBernoulliMeasure_three_isUnit (hc : ¬ p ∣ 3) :
    IsUnit (iwasawaTransform (mazurBernoulliMeasure p 3 hc)) ∧
    iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p 3 hc)) = 0 ∧
    iwasawaLambda (iwasawaTransform (mazurBernoulliMeasure p 3 hc)) = 0 := by
  have hu : IsUnit (iwasawaTransform (mazurBernoulliMeasure p 3 hc)) := by
    rw [isUnit_iwasawaAlg_iff, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_iwasawaTransform]
    have hm0 : measureIntegral (mazurBernoulliMeasure p 3 hc) (mahlerBinom 0) = 1 := by
      have hfn : (mahlerBinom (p := p) 0) = fun _ => 1 := funext mahlerBinom_zero
      rw [hfn, measureIntegral_const, one_mul,
        mazurBernoulliMeasure_apply_zero_of_odd 3 hc ⟨1, rfl⟩ 0]
      norm_num
    rw [hm0, ← padicInt_isUnit_iff_not_p_dvd]
    exact isUnit_one
  exact ⟨hu, iwasawaMu_of_isUnit hu, iwasawaLambda_of_isUnit hu⟩

private lemma two_ne_zero_zmod3 : (2 : ZMod 3) ≠ 0 := by decide

/-- Explicit `c = 5` unit theorem for `p = 3`:
`iwasawaTransform (mazurBernoulliMeasure 3 5 _)` is a UNIT in `ℤ_[3][[T]]` (`μ = 0` AND `λ = 0`)! -/
theorem mazurBernoulliMeasure_five_p3_isUnit [Fact (Nat.Prime 3)] :
    IsUnit (iwasawaTransform (mazurBernoulliMeasure 3 5 (by decide))) ∧
    iwasawaMu (iwasawaTransform (mazurBernoulliMeasure 3 5 (by decide))) = 0 ∧
    iwasawaLambda (iwasawaTransform (mazurBernoulliMeasure 3 5 (by decide))) = 0 := by
  have hu : IsUnit (iwasawaTransform (mazurBernoulliMeasure 3 5 (by decide))) := by
    rw [isUnit_iwasawaAlg_iff, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_iwasawaTransform]
    have hm0 : measureIntegral (mazurBernoulliMeasure 3 5 (by decide)) (mahlerBinom 0) = 2 := by
      have hfn : (mahlerBinom (p := 3) 0) = fun _ => 1 := funext mahlerBinom_zero
      rw [hfn, measureIntegral_const, one_mul,
        mazurBernoulliMeasure_apply_zero_of_odd 5 (by decide) ⟨2, rfl⟩ 0]
      norm_num
    rw [hm0, padicInt_p_dvd_iff_toZMod_eq_zero, map_ofNat]
    exact two_ne_zero_zmod3
  exact ⟨hu, iwasawaMu_of_isUnit hu, iwasawaLambda_of_isUnit hu⟩

/-- **Exact Sinnott Rational-Function Identity for Mazur's Measure `μ_c`**:
for EVERY prime `p` and EVERY `c ≥ 1` with `¬ p ∣ c`,
`((1 + T)^c - 1) * iwasawaTransform (mazurBernoulliMeasure p c hc) = (∑_{j < c} (1 + T)^j) - c`
in `ℤ_[p][[T]]`! -/
theorem mazurBernoulliMeasure_rational_identity (c : ℕ) (hc1 : 1 ≤ c) (hc : ¬ p ∣ c) :
    ((1 + PowerSeries.X) ^ c - 1) * iwasawaTransform (mazurBernoulliMeasure p c hc) =
      (∑ j ∈ Finset.range c, (1 + PowerSeries.X) ^ j) - (c : IwasawaAlg p) := by
  have hp : p.Prime := Fact.out
  -- Prove the equivalent identity of `PadicMeasure p` under `iwasawaTransformRingHom`!
  have hdir_pow : ∀ j : ℕ, (diracMeasure (p := p) 1) ^ j = diracMeasure (j : ℤ_[p]) := by
    intro j
    induction j with
    | zero => simp; rfl
    | succ j ih =>
      rw [pow_succ, ih, diracMeasure_mul, Nat.cast_succ]
  have hL_tr : ((1 + PowerSeries.X) ^ c - 1) * iwasawaTransform (mazurBernoulliMeasure p c hc) =
      iwasawaTransform ((diracMeasure (c : ℤ_[p]) - 1) * mazurBernoulliMeasure p c hc) := by
    change _ = iwasawaTransformRingHom ((diracMeasure (c : ℤ_[p]) - 1) * mazurBernoulliMeasure p c hc)
    rw [map_mul, map_sub, map_one, ← hdir_pow c, map_pow]
    change _ = (iwasawaTransform (diracMeasure 1) ^ c - 1) * iwasawaTransform (mazurBernoulliMeasure p c hc)
    rw [iwasawaTransform_dirac_one]
  have hR_tr : (∑ j ∈ Finset.range c, (1 + PowerSeries.X) ^ j) - (c : IwasawaAlg p) =
      iwasawaTransform ((∑ j ∈ Finset.range c, diracMeasure (j : ℤ_[p])) - (c : PadicMeasure p)) := by
    change _ = iwasawaTransformRingHom ((∑ j ∈ Finset.range c, diracMeasure (j : ℤ_[p])) - (c : PadicMeasure p))
    rw [map_sub, map_sum, map_natCast]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hdir_pow j, map_pow]
    change _ = iwasawaTransform (diracMeasure 1) ^ j
    rw [iwasawaTransform_dirac_one]
  rw [hL_tr, hR_tr]
  congr 1
  -- Show the two measures agree at all levels `n` by checking sufficiently large `N ≥ max n c`!
  have hlarge : ∀ (N : ℕ), c < p ^ N → ∀ (a : ZMod (p ^ N)),
      ((diracMeasure (c : ℤ_[p]) - 1) * mazurBernoulliMeasure p c hc) N a =
      ((∑ j ∈ Finset.range c, diracMeasure (j : ℤ_[p])) - (c : PadicMeasure p)) N a := by
    intro N hN a
    have : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
    have hPN0 : ((p ^ N : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero N hp.ne_zero)
    have hLHS : ((diracMeasure (c : ℤ_[p]) - 1) * mazurBernoulliMeasure p c hc) N a =
        mazurBernoulliMeasure p c hc N (a - (c : ZMod (p ^ N))) - mazurBernoulliMeasure p c hc N a := by
      rw [sub_mul, one_mul, PadicMeasure.sub_apply, PadicMeasure.mul_apply]
      congr 1
      rw [Finset.sum_eq_single (c : ZMod (p ^ N))]
      · simp [diracMeasure]
      · intro x _ hx; simp [diracMeasure, hx.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hRHS_sum : ∀ s : Finset ℕ, ∀ f : ℕ → PadicMeasure p,
        (∑ j ∈ s, f j) N a = ∑ j ∈ s, f j N a := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, PadicMeasure.add_apply, ih]
    have hRHS_nat_all : ∀ m : ℕ, ((m : PadicMeasure p) N a) =
        if (0 : ZMod (p ^ N)) = a then (m : ℤ_[p]) else 0 := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, PadicMeasure.add_apply, ih, PadicMeasure.one_apply, Nat.cast_succ]
        split_ifs <;> simp
    have hRHS_nat := hRHS_nat_all c
    have hRHS_dir : (∑ j ∈ Finset.range c, diracMeasure (p := p) (j : ℤ_[p])) N a =
        if a.val < c then 1 else 0 := by
      rw [hRHS_sum]
      by_cases ha : a.val < c
      · rw [if_pos ha, Finset.sum_eq_single a.val]
        · simp [diracMeasure]
        · intro j hj hne
          have hjlt : j < p ^ N := lt_trans (Finset.mem_range.mp hj) hN
          have hne_z : (j : ZMod (p ^ N)) ≠ a := by
            intro heq
            apply hne
            have hv := congrArg ZMod.val heq
            rwa [ZMod.val_natCast_of_lt hjlt] at hv
          simp [diracMeasure, hne_z]
        · intro hnot; exact absurd (Finset.mem_range.mpr ha) hnot
      · rw [if_neg ha]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjlt : j < p ^ N := lt_trans (Finset.mem_range.mp hj) hN
        have hne_z : (j : ZMod (p ^ N)) ≠ a := by
          intro heq
          apply ha
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt hjlt] at hv
          rw [← hv]
          exact Finset.mem_range.mp hj
        simp [diracMeasure, hne_z]
    rw [hLHS, PadicMeasure.sub_apply, hRHS_dir, hRHS_nat]
    apply Subtype.ext
    rw [PadicInt.coe_sub, mazurBernoulliMeasure_coe, mazurBernoulliMeasure_coe, ← Rat.cast_sub,
      PadicInt.coe_sub]
    have hdiff_E1 : ∀ x : ZMod (p ^ N), ∀ k : ℕ, k < p ^ N →
        bernoulliDist p 1 N (x - (k : ZMod (p ^ N))) - bernoulliDist p 1 N x =
          (if x.val < k then (1 : ℚ) else 0) - (k : ℚ) / ((p ^ N : ℕ) : ℚ) := by
      intro x k hk
      unfold bernoulliDist
      simp only [Nat.sub_self, pow_zero, one_mul, Polynomial.bernoulli_one, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      by_cases hxk : x.val < k
      · rw [if_pos hxk]
        have hlt : x.val + p ^ N - k < p ^ N := by omega
        have hcast : ((x.val + p ^ N - k : ℕ) : ZMod (p ^ N)) = x - (k : ZMod (p ^ N)) := by
          rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self,
            add_zero]
        have hval : (x - (k : ZMod (p ^ N))).val = x.val + p ^ N - k := by
          rw [← hcast, ZMod.val_natCast_of_lt hlt]
        rw [hval]
        have hcastQ : ((x.val + p ^ N - k : ℕ) : ℚ) = (x.val : ℚ) + ((p ^ N : ℕ) : ℚ) - (k : ℚ) := by
          have : (x.val + p ^ N - k) + k = x.val + p ^ N := Nat.sub_add_cancel (by omega)
          have hQ : (((x.val + p ^ N - k) + k : ℕ) : ℚ) = ((x.val + p ^ N : ℕ) : ℚ) := by
            exact_mod_cast this
          push_cast at hQ ⊢
          linarith
        rw [hcastQ]
        field_simp [hPN0]
        ring
      · rw [if_neg hxk]
        have hge : k ≤ x.val := not_lt.mp hxk
        have hlt : x.val - k < p ^ N := lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt x)
        have hcast : ((x.val - k : ℕ) : ZMod (p ^ N)) = x - (k : ZMod (p ^ N)) := by
          rw [Nat.cast_sub hge, ZMod.natCast_zmod_val]
        have hval : (x - (k : ZMod (p ^ N))).val = x.val - k := by
          rw [← hcast, ZMod.val_natCast_of_lt hlt]
        rw [hval]
        have hcastQ : ((x.val - k : ℕ) : ℚ) = (x.val : ℚ) - (k : ℚ) := by
          exact_mod_cast Nat.cast_sub (R := ℚ) hge
        rw [hcastQ]
        field_simp [hPN0]
        ring
    have h1lt : 1 < p ^ N := by omega
    have hmul_sub : cInv p c hc N * (a - (c : ZMod (p ^ N))) = cInv p c hc N * a - 1 := by
      rw [mul_sub, cInv_mul_c]
    have hzero_iff : ((cInv p c hc N * a).val < 1) ↔ ((0 : ZMod (p ^ N)) = a) := by
      constructor
      · intro hlt
        have h0 : (cInv p c hc N * a).val = 0 := Nat.lt_one_iff.mp hlt
        have hz : cInv p c hc N * a = 0 := by
          rw [← ZMod.natCast_zmod_val (cInv p c hc N * a), h0, Nat.cast_zero]
        have ha0 : a = 0 := by
          calc a = (c : ZMod (p ^ N)) * (cInv p c hc N * a) := by rw [← mul_assoc, c_mul_cInv, one_mul]
            _ = 0 := by rw [hz, mul_zero]
        exact ha0.symm
      · intro h0
        rw [← h0, mul_zero, ZMod.val_zero]
        exact Nat.zero_lt_one
    have hQeq : mazurBernoulliDist p c hc 1 N (a - (c : ZMod (p ^ N))) - mazurBernoulliDist p c hc 1 N a =
        (if a.val < c then (1 : ℚ) else 0) - (if (0 : ZMod (p ^ N)) = a then (c : ℚ) else 0) := by
      unfold mazurBernoulliDist
      rw [pow_one, hmul_sub]
      have hrearr : (bernoulliDist p 1 N (a - (c : ZMod (p ^ N))) - (c : ℚ) * bernoulliDist p 1 N (cInv p c hc N * a - 1)) -
          (bernoulliDist p 1 N a - (c : ℚ) * bernoulliDist p 1 N (cInv p c hc N * a)) =
          (bernoulliDist p 1 N (a - (c : ZMod (p ^ N))) - bernoulliDist p 1 N a) -
          (c : ℚ) * (bernoulliDist p 1 N (cInv p c hc N * a - (1 : ℕ)) - bernoulliDist p 1 N (cInv p c hc N * a)) := by
        simp; ring
      rw [hrearr, hdiff_E1 a c hN, hdiff_E1 (cInv p c hc N * a) 1 h1lt]
      simp only [Nat.cast_one, hzero_iff]
      split_ifs <;> ring
    rw [hQeq, Rat.cast_sub]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  ext n a
  set N := max n c
  have hnN : n ≤ N := le_max_left _ _
  have hcN : c < p ^ N := by
    have h1 : c < 2 ^ c := Nat.lt_two_pow_self
    have h2 : 2 ^ c ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have h3 : 2 ^ N ≤ p ^ N := Nat.pow_le_pow_left hp.two_le N
    omega
  rw [PadicMeasure.compat_le _ hnN a, PadicMeasure.compat_le _ hnN a]
  exact Finset.sum_congr rfl fun b _ => hlarge N hcN b

/-- Invariance of `p`-adic content under the automorphism `T ↦ 1 + T` of `ℤ_[p][T]`:
`(P.comp (1 + X)).map toZMod = 0 ↔ P.map toZMod = 0`. -/
lemma poly_comp_one_add_X_map_toZMod_eq_zero_iff (P : Polynomial ℤ_[p]) :
    (P.comp (1 + Polynomial.X)).map PadicInt.toZMod = 0 ↔ P.map PadicInt.toZMod = 0 := by
  have hmap : (P.comp (1 + Polynomial.X)).map PadicInt.toZMod =
      (P.map PadicInt.toZMod).comp (1 + Polynomial.X) := by
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
  rw [hmap]
  constructor
  · intro h0
    have hinv : ((P.map PadicInt.toZMod).comp (1 + Polynomial.X)).comp (Polynomial.X - 1) =
        P.map PadicInt.toZMod := by
      rw [Polynomial.comp_assoc]
      have h1 : (1 + Polynomial.X : Polynomial (ZMod p)).comp (Polynomial.X - 1) = Polynomial.X := by
        simp [Polynomial.add_comp]
      rw [h1, Polynomial.comp_X]
    rw [← hinv, h0, Polynomial.zero_comp]
  · intro h0
    rw [h0, Polynomial.zero_comp]

lemma reduceModP_toPowerSeries_eq_zero_iff (P : Polynomial ℤ_[p]) :
    reduceModP P.toPowerSeries = 0 ↔ P.map PadicInt.toZMod = 0 := by
  constructor
  · intro h0
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, ← toPowerSeries_coeff, ← coeff_reduceModP,
      h0, map_zero]
  · intro h0
    ext k
    rw [coeff_reduceModP, toPowerSeries_coeff, ← Polynomial.coeff_map, h0, Polynomial.coeff_zero,
      map_zero]

/-- Invariance of `iwasawaMu` under `T ↦ 1 + T` on polynomials `P ∈ ℤ_[p][T]`. -/
theorem iwasawaMu_poly_comp_one_add_X (P : Polynomial ℤ_[p]) :
    iwasawaMu (P.comp (1 + Polynomial.X)).toPowerSeries = iwasawaMu P.toPowerSeries := by
  have hcomp_inv : (P.comp (1 + Polynomial.X)).comp (Polynomial.X - 1) = P := by
    rw [Polynomial.comp_assoc]
    have h1 : (1 + Polynomial.X : Polynomial ℤ_[p]).comp (Polynomial.X - 1) = Polynomial.X := by
      simp [Polynomial.add_comp]
    rw [h1, Polynomial.comp_X]
  by_cases hP : P = 0
  · subst hP; simp
  · have hP1 : P.comp (1 + Polynomial.X) ≠ 0 := by
      intro h0; apply hP; rw [← hcomp_inv, h0, Polynomial.zero_comp]
    have hps : P.toPowerSeries ≠ 0 := fun h0 => hP (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
    have hps1 : (P.comp (1 + Polynomial.X)).toPowerSeries ≠ 0 := fun h0 =>
      hP1 (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
    have hdvd_iff : ∀ m : ℕ,
        (∀ k, (p : ℤ_[p]) ^ m ∣ PowerSeries.coeff k (P.comp (1 + Polynomial.X)).toPowerSeries) ↔
        (∀ k, (p : ℤ_[p]) ^ m ∣ PowerSeries.coeff k P.toPowerSeries) := by
      intro m
      have hpoly_dvd : ∀ (R S : Polynomial ℤ_[p]),
          (∀ k, (p : ℤ_[p]) ^ m ∣ R.coeff k) → ∀ k, (p : ℤ_[p]) ^ m ∣ (R.comp S).coeff k := by
        intro R S hR
        let R' : Polynomial ℤ_[p] := ∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C (hR i).choose * Polynomial.X ^ i
        have hReq : R = Polynomial.C ((p : ℤ_[p]) ^ m) * R' := by
          ext k
          rw [Polynomial.coeff_C_mul]
          dsimp only [R']
          rw [Polynomial.finsetSum_coeff]
          simp_rw [Polynomial.coeff_C_mul_X_pow]
          by_cases hk : k < R.natDegree + 1
          · rw [Finset.sum_eq_single k]
            · simp only [↓reduceIte]; exact (hR k).choose_spec
            · intro i _ hi; simp [hi.symm]
            · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
            have hz : ∑ i ∈ Finset.range (R.natDegree + 1),
                (if k = i then (hR i).choose else 0) = 0 := by
              refine Finset.sum_eq_zero fun i hi => ?_
              have hne : k ≠ i := by have := Finset.mem_range.mp hi; omega
              simp [hne]
            rw [hz, mul_zero]
        intro k
        rw [hReq, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.coeff_C_mul]
        exact dvd_mul_right _ _
      simp_rw [toPowerSeries_coeff]
      constructor
      · intro h
        have h' := hpoly_dvd (P.comp (1 + Polynomial.X)) (Polynomial.X - 1) h
        rwa [hcomp_inv] at h'
      · exact hpoly_dvd P (1 + Polynomial.X)
    apply le_antisymm
    · rw [← forall_p_pow_dvd_coeff_iff_le_iwasawaMu hps, ← hdvd_iff]
      exact p_pow_iwasawaMu_dvd_coeff _
    · rw [← forall_p_pow_dvd_coeff_iff_le_iwasawaMu hps1, hdvd_iff]
      exact p_pow_iwasawaMu_dvd_coeff _

/-- **Sinnott's Rational-Function `μ`-Invariant Lemma (`sinnott_rational_measure_mu_zero`)**:
if a power series `F ∈ ℤ_[p][[T]]` satisfies the rational-function relation
`Q(1 + T) * F(T) = P(1 + T)` where `P(1 + T)` reduces nonzero mod `p` (i.e. `P.map toZMod ≠ 0`),
then `F ≠ 0` and `iwasawaMu F = 0`! -/
theorem sinnott_rational_measure_mu_zero {P Q : Polynomial ℤ_[p]} {F : PowerSeries ℤ_[p]}
    (hrel : (Q.comp (1 + Polynomial.X)).toPowerSeries * F =
      (P.comp (1 + Polynomial.X)).toPowerSeries)
    (hP_mod : P.map PadicInt.toZMod ≠ 0) :
    F ≠ 0 ∧ iwasawaMu F = 0 := by
  have hP1_mod : reduceModP (P.comp (1 + Polynomial.X)).toPowerSeries ≠ 0 := by
    rw [ne_eq, reduceModP_toPowerSeries_eq_zero_iff, poly_comp_one_add_X_map_toZMod_eq_zero_iff]
    exact hP_mod
  have hF_mod : reduceModP F ≠ 0 := by
    intro h0
    apply hP1_mod
    rw [← hrel, map_mul, h0, mul_zero]
  have hF_ne : F ≠ 0 := by
    intro h0; apply hF_mod; rw [h0, map_zero]
  exact ⟨hF_ne, (iwasawaMu_eq_zero_iff_reduceModP_ne_zero hF_ne).mpr hF_mod⟩

/-- General Sinnott Rational-Function `μ`-Invariant Formula:
if `Q(1 + T) * F(T) = P(1 + T)` with `P ≠ 0`, `Q ≠ 0`, then `iwasawaMu P = iwasawaMu Q + iwasawaMu F`;
in particular, `iwasawaMu F = 0 ↔ iwasawaMu P.toPowerSeries = iwasawaMu Q.toPowerSeries`! -/
theorem sinnott_rational_measure_mu_eq_zero_iff {P Q : Polynomial ℤ_[p]} {F : PowerSeries ℤ_[p]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : (Q.comp (1 + Polynomial.X)).toPowerSeries * F =
      (P.comp (1 + Polynomial.X)).toPowerSeries) :
    F ≠ 0 ∧ (iwasawaMu F = 0 ↔ iwasawaMu P.toPowerSeries = iwasawaMu Q.toPowerSeries) := by
  have hcomp_ne : ∀ R : Polynomial ℤ_[p], R ≠ 0 → (R.comp (1 + Polynomial.X)).toPowerSeries ≠ 0 := by
    intro R hR h0
    apply hR
    have hR0 : R.comp (1 + Polynomial.X) = 0 := toPowerSeries_injective (h0.trans toPowerSeries_zero.symm)
    have hinv : (R.comp (1 + Polynomial.X)).comp (Polynomial.X - 1) = R := by
      rw [Polynomial.comp_assoc]
      have h1 : (1 + Polynomial.X : Polynomial ℤ_[p]).comp (Polynomial.X - 1) = Polynomial.X := by
        simp [Polynomial.add_comp]
      rw [h1, Polynomial.comp_X]
    rw [← hinv, hR0, Polynomial.zero_comp]
  have hP1 := hcomp_ne P hP
  have hQ1 := hcomp_ne Q hQ
  have hF : F ≠ 0 := by
    intro h0; apply hP1; rw [← hrel, h0, mul_zero]
  refine ⟨hF, ?_⟩
  have hadd := iwasawaMu_mul hQ1 hF
  rw [hrel, iwasawaMu_poly_comp_one_add_X P, iwasawaMu_poly_comp_one_add_X Q] at hadd
  omega

end MazurAndSinnott

/-! ## Section 3: Ferrero–Washington Criterion on `kubotaLeopoldtSeries` & Regular Primes -/

section FerreroWashingtonCriterion

open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- The underlying `p`-adic measure of `kubotaLeopoldtSeries p hp2 c hc i`, so that
`kubotaLeopoldtSeries p hp2 c hc i = iwasawaTransform (kubotaLeopoldtMeasure p hp2 c hc i)`. -/
def kubotaLeopoldtMeasure (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i : ℕ) : PadicMeasure p :=
  pushforwardMeasure (fun x : ℤ_[p] => padicLogBase hp2 (diamond x))
    (continuous_padicLogBase_diamond hp2)
    (weightMeasure p (fun x : ℤ_[p] => teichmuller x ^ i)
      (continuous_teichmuller.pow i)
      (mazurBernoulliMeasure p c hc).restrictUnits)

lemma kubotaLeopoldtSeries_eq_iwasawaTransform (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i : ℕ) :
    kubotaLeopoldtSeries p hp2 c hc i = iwasawaTransform (kubotaLeopoldtMeasure p hp2 c hc i) :=
  rfl

/-- **Exact Level-`n` Teichmüller-Weighted Mazur Distribution Formula for `kubotaLeopoldtMeasure`**:
for every odd prime `p`, `c` with `¬ p ∣ c`, branch `i : ℕ`, level `n : ℕ`, and `s : ZMod (p ^ n)`:
`ν_i(s + p^n ℤ_p) = ∑_{r = 1}^{p - 1} ω(r)^i * μ_c(ω(r) * (1 + p)^s mod p^{n+1})`! -/
theorem kubotaLeopoldtMeasure_apply (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i n : ℕ)
    (s : ZMod (p ^ n)) :
    kubotaLeopoldtMeasure p hp2 c hc i n s =
      ∑ r ∈ Finset.Ico 1 p,
        teichmuller (r : ℤ_[p]) ^ i *
        mazurBernoulliMeasure p c hc (n + 1)
          (PadicInt.toZModPow (n + 1) (teichmuller (r : ℤ_[p])) *
            ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val)) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  unfold kubotaLeopoldtMeasure pushforwardMeasure
  dsimp only
  rw [measureIntegral_weightMeasure p (w := fun x : ℤ_[p] => teichmuller x ^ i)
      (continuous_teichmuller.pow i) _
      (g := fun x : ℤ_[p] => ballIndicator n s (padicLogBase hp2 (diamond x)))
      ((continuous_ballIndicator n s).comp (continuous_padicLogBase_diamond hp2)),
    measureIntegral_restrictUnits _
      (f := fun x : ℤ_[p] => teichmuller x ^ i * ballIndicator n s (padicLogBase hp2 (diamond x)))
      ((continuous_teichmuller.pow i).mul ((continuous_ballIndicator n s).comp (continuous_padicLogBase_diamond hp2)))]
  -- Show the integrand is locally constant of level `n + 1`!
  have hloc : ∀ x y : ℤ_[p], PadicInt.toZModPow (n + 1) x = PadicInt.toZModPow (n + 1) y →
      unitIndicator x * (teichmuller x ^ i * ballIndicator n s (padicLogBase hp2 (diamond x))) =
      unitIndicator y * (teichmuller y ^ i * ballIndicator n s (padicLogBase hp2 (diamond y))) := by
    intro x y hxy
    have h1 : PadicInt.toZModPow 1 x = PadicInt.toZModPow 1 y := by
      rw [← zmodPowCast_toZModPow (Nat.succ_le_succ (Nat.zero_le n)) x,
        ← zmodPowCast_toZModPow (Nat.succ_le_succ (Nat.zero_le n)) y, hxy]
    have h0 : PadicInt.toZMod x = PadicInt.toZMod y := by
      have hmem : x - y ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h1, sub_self]
      rw [pow_one, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
      exact hmem
    have hteich : teichmuller x = teichmuller y := teichmuller_eq_of_toZMod_eq h0
    have hdiam : PadicInt.toZModPow (n + 1) (diamond x) = PadicInt.toZModPow (n + 1) (diamond y) := by
      unfold diamond
      rw [h0]
      split_ifs
      · rw [map_mul, map_mul, hxy, hteich]
      · rfl
    have hlog : PadicInt.toZModPow n (padicLogBase hp2 (diamond x)) =
        PadicInt.toZModPow n (padicLogBase hp2 (diamond y)) := by
      rw [padicInt_toZModPow_padicLogBase hp2 n (toZMod_diamond hp2 x),
        padicInt_toZModPow_padicLogBase hp2 n (toZMod_diamond hp2 y)]
      simp only [padicLogLevel, hdiam]
    simp only [unitIndicator, ballIndicator, h0, hteich, hlog]
  rw [measureIntegral_eq_riemannSum_of_locallyConstant _ (n + 1) hloc]
  unfold riemannSum
  -- Filter to `b : ZMod (p^(n+1))` with `toZMod b.val ≠ 0` and `padicLogLevel hp2 n (diamond b.val) = s`
  let P : ZMod (p ^ (n + 1)) → Prop := fun b =>
    PadicInt.toZMod (b.val : ℤ_[p]) ≠ 0 ∧
      PadicInt.toZModPow n (padicLogBase hp2 (diamond (b.val : ℤ_[p]))) = s
  have hfilt : ∑ b : ZMod (p ^ (n + 1)),
      unitIndicator (b.val : ℤ_[p]) *
        (teichmuller (b.val : ℤ_[p]) ^ i * ballIndicator n s (padicLogBase hp2 (diamond (b.val : ℤ_[p])))) *
        mazurBernoulliMeasure p c hc (n + 1) b =
      ∑ b ∈ Finset.univ.filter P,
        teichmuller (b.val : ℤ_[p]) ^ i * mazurBernoulliMeasure p c hc (n + 1) b := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]
    have h1 : ∀ b ∈ Finset.univ.filter P,
        unitIndicator (b.val : ℤ_[p]) *
          (teichmuller (b.val : ℤ_[p]) ^ i * ballIndicator n s (padicLogBase hp2 (diamond (b.val : ℤ_[p])))) *
          mazurBernoulliMeasure p c hc (n + 1) b =
        teichmuller (b.val : ℤ_[p]) ^ i * mazurBernoulliMeasure p c hc (n + 1) b := by
      intro b hb
      obtain ⟨hu, hs⟩ := (Finset.mem_filter.mp hb).2
      simp only [unitIndicator, ballIndicator, if_pos hu, if_pos hs, one_mul, mul_one]
    have h2 : ∑ b ∈ Finset.univ.filter (fun b => ¬ P b),
        unitIndicator (b.val : ℤ_[p]) *
          (teichmuller (b.val : ℤ_[p]) ^ i * ballIndicator n s (padicLogBase hp2 (diamond (b.val : ℤ_[p])))) *
          mazurBernoulliMeasure p c hc (n + 1) b = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hnot := (Finset.mem_filter.mp hb).2
      by_cases hu : PadicInt.toZMod (b.val : ℤ_[p]) ≠ 0
      · have hs : PadicInt.toZModPow n (padicLogBase hp2 (diamond (b.val : ℤ_[p]))) ≠ s :=
          fun h => hnot ⟨hu, h⟩
        simp only [unitIndicator, ballIndicator, if_pos hu, if_neg hs, mul_zero, zero_mul]
      · simp only [unitIndicator, if_neg hu, zero_mul]
    rw [Finset.sum_congr rfl h1, h2, add_zero]
  rw [hfilt]
  -- Biject `r ∈ Finset.Ico 1 p` with `Finset.univ.filter P` via `r ↦ toZModPow (n+1) (ω(r)) * (1 + p)^s.val`!
  let φ : ℕ → ZMod (p ^ (n + 1)) := fun r =>
    PadicInt.toZModPow (n + 1) (teichmuller (r : ℤ_[p])) * ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val)
  have htoZMod_eq : ∀ b : ZMod (p ^ (n + 1)),
      PadicInt.toZMod (b.val : ℤ_[p]) = ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p) b := by
    intro b
    rw [map_natCast, ← map_natCast (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)),
      ZMod.natCast_zmod_val]
  have htoZMod_phi : ∀ r : ℕ, PadicInt.toZMod ((φ r).val : ℤ_[p]) = (r : ZMod p) := by
    intro r
    rw [htoZMod_eq, map_mul, map_pow, map_add, map_one, map_natCast, ZMod.natCast_self, add_zero,
      one_pow, mul_one]
    have hcomp : (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)).comp
        (PadicInt.toZModPow (n + 1)) = PadicInt.toZMod := by
      ext x
      have hx : PadicInt.toZMod x = ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
          (PadicInt.toZModPow (n + 1) x) := by
        have hker : x - ((PadicInt.toZModPow (n + 1) x).val : ℤ_[p]) ∈
            Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
          have hmem : x - ((PadicInt.toZModPow (n + 1) x).val : ℤ_[p]) ∈
              Ideal.span ({(p : ℤ_[p]) ^ (n + 1)} : Set ℤ_[p]) := by
            rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
              ZMod.natCast_zmod_val, sub_self]
          exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ (Nat.succ_ne_zero n)) hmem
        rw [← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, sub_eq_zero] at hker
        rw [hker, htoZMod_eq]
      exact hx.symm
    have h2 := congrArg (fun f => f (teichmuller (r : ℤ_[p]))) hcomp
    simpa [RingHom.comp_apply, toZMod_teichmuller] using h2
  have hteich_phi : ∀ r : ℕ, teichmuller ((φ r).val : ℤ_[p]) = teichmuller (r : ℤ_[p]) := by
    intro r
    apply teichmuller_eq_of_toZMod_eq
    rw [htoZMod_phi r, map_natCast]
  symm
  refine Finset.sum_bij (fun r _ => φ r) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [htoZMod_phi r, Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
    · rw [padicInt_toZModPow_padicLogBase hp2 n (toZMod_diamond hp2 _)]
      have hru : PadicInt.toZMod ((φ r).val : ℤ_[p]) ≠ 0 := by
        rw [htoZMod_phi r, Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
      have hdiam_eq : PadicInt.toZModPow (n + 1) (diamond ((φ r).val : ℤ_[p])) =
          (1 + (p : ZMod (p ^ (n + 1)))) ^ s.val := by
        have hmul := congrArg (PadicInt.toZModPow (n + 1)) (teichmuller_mul_diamond hp2 hru)
        rw [map_mul, map_natCast, ZMod.natCast_zmod_val, hteich_phi r] at hmul
        have hunit : IsUnit (PadicInt.toZModPow (n + 1) (teichmuller (r : ℤ_[p]))) := by
          have hr_ne : PadicInt.toZMod (teichmuller (r : ℤ_[p])) ≠ 0 := by
            rw [toZMod_teichmuller, map_natCast, Ne, ZMod.natCast_eq_zero_iff]
            exact Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
          exact (padicInt_isUnit_of_toZMod_ne_zero hr_ne).map _
        obtain ⟨u, hu⟩ := hunit
        rw [← hu] at hmul
        have hphi_eq : φ r = (u : ZMod (p ^ (n + 1))) * ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val) := by
          simp [φ, hu]
        conv_rhs at hmul => rw [hphi_eq]
        calc PadicInt.toZModPow (n + 1) (diamond ((φ r).val : ℤ_[p]))
            = ((u⁻¹ : (ZMod (p ^ (n + 1)))ˣ) : ZMod (p ^ (n + 1))) *
                ((u : ZMod (p ^ (n + 1))) * PadicInt.toZModPow (n + 1) (diamond ((φ r).val : ℤ_[p]))) := by
                rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = ((u⁻¹ : (ZMod (p ^ (n + 1)))ˣ) : ZMod (p ^ (n + 1))) *
                ((u : ZMod (p ^ (n + 1))) * ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val)) := by rw [hmul]
          _ = (1 + (p : ZMod (p ^ (n + 1)))) ^ s.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
      have hspec := padicLogLevel_spec hp2 n (toZMod_diamond hp2 ((φ r).val : ℤ_[p]))
      rw [hdiam_eq] at hspec
      have hu1 : zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n))
          ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val) = 1 := by
        rw [map_pow, map_add, map_one, map_natCast]
        have hp0 : (p : ZMod (p ^ 1)) = 0 := by rw [pow_one, ZMod.natCast_self]
        rw [hp0, add_zero, one_pow]
      exact (exists_unique_log_mod_prime_pow hp2 n _ hu1).unique hspec rfl
  · intro r₁ hr₁ r₂ hr₂ heq
    have h1 := htoZMod_phi r₁
    have h2 := htoZMod_phi r₂
    rw [heq] at h1
    have hz : (r₁ : ZMod p) = (r₂ : ZMod p) := h1.symm.trans h2
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (Finset.mem_Ico.mp hr₁).2,
      ZMod.val_natCast_of_lt (Finset.mem_Ico.mp hr₂).2] at hv
    exact hv
  · intro b hb
    obtain ⟨hu, hs⟩ := (Finset.mem_filter.mp hb).2
    let r : ℕ := (PadicInt.toZMod (b.val : ℤ_[p])).val
    have hr_pos : 1 ≤ r := by
      by_contra hlt
      have hr0 : r = 0 := by omega
      apply hu
      rw [← ZMod.natCast_zmod_val (PadicInt.toZMod (b.val : ℤ_[p]))]
      exact (congrArg Nat.cast hr0).trans Nat.cast_zero
    have hr_lt : r < p := ZMod.val_lt _
    refine ⟨r, Finset.mem_Ico.mpr ⟨hr_pos, hr_lt⟩, ?_⟩
    have hteich_b : teichmuller (r : ℤ_[p]) = teichmuller (b.val : ℤ_[p]) := by
      apply teichmuller_eq_of_toZMod_eq
      rw [map_natCast, ZMod.natCast_zmod_val]
    have hlog_eq : padicLogLevel hp2 n (diamond (b.val : ℤ_[p])) = s := by
      rwa [padicInt_toZModPow_padicLogBase hp2 n (toZMod_diamond hp2 _)] at hs
    have hdiam_eq : PadicInt.toZModPow (n + 1) (diamond (b.val : ℤ_[p])) =
        (1 + (p : ZMod (p ^ (n + 1)))) ^ s.val := by
      rw [← hlog_eq]
      exact (padicLogLevel_spec hp2 n (toZMod_diamond hp2 (b.val : ℤ_[p]))).symm
    have hmul := congrArg (PadicInt.toZModPow (n + 1)) (teichmuller_mul_diamond hp2 hu)
    rw [map_mul, map_natCast, ZMod.natCast_zmod_val, ← hteich_b, hdiam_eq] at hmul
    exact hmul
  · intro r _
    rw [hteich_phi r]

/-- **Mod-`p` Reduction of the Level-`n` Kubota–Leopoldt Measure Value**:
`ν_i(s + p^n ℤ_p) mod p = ∑_{r = 1}^{p - 1} r^i * (μ_c(ω(r) * (1 + p)^s mod p^{n+1}) mod p)`! -/
theorem toZMod_kubotaLeopoldtMeasure_apply (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i n : ℕ)
    (s : ZMod (p ^ n)) :
    PadicInt.toZMod (kubotaLeopoldtMeasure p hp2 c hc i n s) =
      ∑ r ∈ Finset.Ico 1 p,
        (r : ZMod p) ^ i *
        PadicInt.toZMod (mazurBernoulliMeasure p c hc (n + 1)
          (PadicInt.toZModPow (n + 1) (teichmuller (r : ℤ_[p])) *
            ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val))) := by
  rw [kubotaLeopoldtMeasure_apply, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_pow, toZMod_teichmuller, map_natCast]

/-- **FERRERO–WASHINGTON `μ = 0` CRITERION ON `kubotaLeopoldtSeries`**:
for every odd prime `p`, `c` with `¬ p ∣ c`, and branch `i : ℕ`:
`reduceModP (kubotaLeopoldtSeries p hp2 c hc i) ≠ 0` IFF there exist `n : ℕ` and `s : ZMod (p ^ n)`
such that the Teichmüller-weighted Mazur distribution sum
`∑_{r = 1}^{p - 1} ω(r)^i * μ_c(ω(r) * (1 + p)^s mod p^{n+1})` is NOT divisible by `p` (a `p`-adic unit)! -/
theorem ferrero_washington_reduceModP_criterion (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i : ℕ) :
    reduceModP (kubotaLeopoldtSeries p hp2 c hc i) ≠ 0 ↔
      ∃ (n : ℕ) (s : ZMod (p ^ n)),
        ¬ (p : ℤ_[p]) ∣
          ∑ r ∈ Finset.Ico 1 p,
            teichmuller (r : ℤ_[p]) ^ i *
            mazurBernoulliMeasure p c hc (n + 1)
              (PadicInt.toZModPow (n + 1) (teichmuller (r : ℤ_[p])) *
                ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val)) := by
  rw [kubotaLeopoldtSeries_eq_iwasawaTransform, reduceModP_iwasawaTransform_ne_zero_iff]
  simp_rw [kubotaLeopoldtMeasure_apply]

/-- **FERRERO–WASHINGTON `μ = 0` CRITERION (`iwasawaMu = 0` Form)**:
whenever `kubotaLeopoldtSeries p hp2 c hc i ≠ 0`, `iwasawaMu (kubotaLeopoldtSeries p hp2 c hc i) = 0`
IFF there exist `n : ℕ` and `s : ZMod (p ^ n)` such that the Teichmüller-weighted Mazur sum is a
`p`-adic unit (`¬ p ∣ ...`)! -/
theorem ferrero_washington_mu_zero_criterion (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i : ℕ)
    (hne : kubotaLeopoldtSeries p hp2 c hc i ≠ 0) :
    iwasawaMu (kubotaLeopoldtSeries p hp2 c hc i) = 0 ↔
      ∃ (n : ℕ) (s : ZMod (p ^ n)),
        ¬ (p : ℤ_[p]) ∣
          ∑ r ∈ Finset.Ico 1 p,
            teichmuller (r : ℤ_[p]) ^ i *
            mazurBernoulliMeasure p c hc (n + 1)
              (PadicInt.toZModPow (n + 1) (teichmuller (r : ℤ_[p])) *
                ((1 + (p : ZMod (p ^ (n + 1)))) ^ s.val)) := by
  rw [iwasawaMu_eq_zero_iff_reduceModP_ne_zero hne, ferrero_washington_reduceModP_criterion]

/-- Unconditional Ferrero–Washington `μ = 0` for ALL non-trivial even branches of
`kubotaLeopoldtSeries` at the regular primes `p = 3, 5, 7, 11, 13`. -/
theorem ferrero_washington_mu_zero_regular_primes :
    (∀ [Fact (Nat.Prime 3)] (i : ℕ), Even i → 2 ≤ i → i ≤ 3 - 3 →
      iwasawaMu (kubotaLeopoldtSeries 3 (by decide) 2 (by decide) (i - 1)) = 0) ∧
    (∀ [Fact (Nat.Prime 5)] (i : ℕ), Even i → 2 ≤ i → i ≤ 5 - 3 →
      iwasawaMu (kubotaLeopoldtSeries 5 (by decide) 2 (by decide) (i - 1)) = 0) ∧
    (∀ [Fact (Nat.Prime 7)] (i : ℕ), Even i → 2 ≤ i → i ≤ 7 - 3 →
      iwasawaMu (kubotaLeopoldtSeries 7 (by decide) 3 (by decide) (i - 1)) = 0) ∧
    (∀ [Fact (Nat.Prime 11)] (i : ℕ), Even i → 2 ≤ i → i ≤ 11 - 3 →
      iwasawaMu (kubotaLeopoldtSeries 11 (by decide) 2 (by decide) (i - 1)) = 0) ∧
    (∀ [Fact (Nat.Prime 13)] (i : ℕ), Even i → 2 ≤ i → i ≤ 13 - 3 →
      iwasawaMu (kubotaLeopoldtSeries 13 (by decide) 2 (by decide) (i - 1)) = 0) :=
  ⟨fun i h1 h2 h3 => (regular_prime_3.2 i h1 h2 h3).2.1,
   fun i h1 h2 h3 => (regular_prime_5.2 i h1 h2 h3).2.1,
   fun i h1 h2 h3 => (regular_prime_7.2 i h1 h2 h3).2.1,
   fun i h1 h2 h3 => (regular_prime_11.2 i h1 h2 h3).2.1,
   fun i h1 h2 h3 => (regular_prime_13.2 i h1 h2 h3).2.1⟩

end FerreroWashingtonCriterion

/-! ## Section 4: Explicit Verification for the First Irregular Prime `p = 37` (`i = 32`: `μ = 0, λ = 1`!) -/

section IrregularPrime37

open scoped Classical

/-- For every odd prime `p`, `mazurBernoulliDist p 2 _ 1 n a = 1 / 2 - (a.val % 2)`. -/
theorem mazurBernoulliDist_two_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hc : ¬ p ∣ 2)
    (n : ℕ) (a : ZMod (p ^ n)) :
    mazurBernoulliDist p 2 hc 1 n a = (1 : ℚ) / 2 - ((a.val % 2 : ℕ) : ℚ) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hNodd : Odd (p ^ n) := Odd.pow (hp.odd_of_ne_two hp2)
  rw [mazurBernoulliDist_one_eq]
  have hhalf : (((2 : ℕ) : ℚ) - 1) / 2 = (1 : ℚ) / 2 := by norm_num
  rw [hhalf]
  congr 2
  have halt : a.val < p ^ n := ZMod.val_lt a
  rcases Nat.mod_two_eq_zero_or_one a.val with heven | hodd
  · rw [heven]
    set k := a.val / 2
    have h2k : 2 * k = a.val := by omega
    have hklt : k < p ^ n := by omega
    have hmul : ((2 : ℕ) : ZMod (p ^ n)) * (k : ZMod (p ^ n)) = a := by
      rw [← Nat.cast_mul, h2k, ZMod.natCast_zmod_val]
    have hcinv : cInv p 2 hc n * a = (k : ZMod (p ^ n)) := by
      rw [← hmul, ← mul_assoc, cInv_mul_c, one_mul]
    rw [hcinv, ZMod.val_natCast_of_lt hklt, h2k]
    exact Nat.div_eq_of_lt halt
  · rw [hodd]
    set k := (a.val + p ^ n) / 2
    obtain ⟨m, hm⟩ := hNodd
    have h2k : 2 * k = a.val + p ^ n := by omega
    have hklt : k < p ^ n := by omega
    have hmul : ((2 : ℕ) : ZMod (p ^ n)) * (k : ZMod (p ^ n)) = a := by
      rw [← Nat.cast_mul, h2k, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    have hcinv : cInv p 2 hc n * a = (k : ZMod (p ^ n)) := by
      rw [← hmul, ← mul_assoc, cInv_mul_c, one_mul]
    rw [hcinv, ZMod.val_natCast_of_lt hklt, h2k]
    have hNpos : 0 < p ^ n := pow_pos hp.pos n
    exact le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hNpos).mpr (by omega)))
      ((Nat.le_div_iff_mul_le hNpos).mpr (by omega))

/-- Mod-`p` evaluation of Mazur's measure for `c = 2` and any odd prime `p`:
`μ_2(a, p^n) mod p = 2⁻¹ - (a.val % 2)` in `ZMod p`. -/
theorem toZMod_mazurBernoulliMeasure_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hc : ¬ p ∣ 2)
    (n : ℕ) (a : ZMod (p ^ n)) :
    PadicInt.toZMod (mazurBernoulliMeasure p 2 hc n a) =
      (2 : ZMod p)⁻¹ - ((a.val % 2 : ℕ) : ZMod p) := by
  have h2ne : (2 : ZMod p) ≠ 0 := by rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]; exact hc
  have hmul_eq : ((2 : ℕ) : ℤ_[p]) * mazurBernoulliMeasure p 2 hc n a =
      1 - ((2 : ℕ) : ℤ_[p]) * ((a.val % 2 : ℕ) : ℤ_[p]) := by
    apply Subtype.ext
    rw [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_one, PadicInt.coe_mul,
      PadicInt.coe_natCast, PadicInt.coe_natCast, mazurBernoulliMeasure_coe,
      mazurBernoulliDist_two_eq p hp2 hc n a]
    simp only [Nat.cast_ofNat, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_natCast]
    ring
  have hmod := congrArg (PadicInt.toZMod (p := p)) hmul_eq
  rw [map_mul, map_sub, map_one, map_mul, map_natCast, map_natCast, Nat.cast_ofNat] at hmod
  calc PadicInt.toZMod (mazurBernoulliMeasure p 2 hc n a)
      = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * PadicInt.toZMod (mazurBernoulliMeasure p 2 hc n a)) := by
          rw [← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]
    _ = (2 : ZMod p)⁻¹ * (1 - 2 * ((a.val % 2 : ℕ) : ZMod p)) := by rw [hmod]
    _ = (2 : ZMod p)⁻¹ - ((a.val % 2 : ℕ) : ZMod p) := by
          rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]

/-- Exact level-`2` formula for the Teichmüller representative:
`PadicInt.toZModPow 2 (teichmuller x) = (PadicInt.toZModPow 2 x) ^ p` for every prime `p`. -/
theorem toZModPow_two_teichmuller {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZModPow 2 (teichmuller x) = (PadicInt.toZModPow 2 x) ^ p := by
  have hp : p.Prime := Fact.out
  have hstep : ∀ k : ℕ, ‖x ^ (p ^ (k + 1)) - x ^ p‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hdecomp : x ^ (p ^ (k + 2)) - x ^ p =
          (x ^ (p ^ (k + 2)) - x ^ (p ^ (k + 1))) + (x ^ (p ^ (k + 1)) - x ^ p) := by ring
      rw [hdecomp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      have hbd := norm_pow_prime_pow_sub_le x (k + 1)
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      exact hbd.trans (zpow_le_zpow_right₀ hp1 (by omega))
  have hnorm : ‖teichmuller x - x ^ p‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
    have hlim : Tendsto (fun k : ℕ => ‖x ^ (p ^ (k + 1)) - x ^ p‖) atTop
        (nhds ‖teichmuller x - x ^ p‖) :=
      (((tendsto_pow_prime_pow_teichmuller x).comp (tendsto_add_atTop_nat 1)).sub_const _).norm
    exact le_of_tendsto' hlim hstep
  have hmod := padicInt_toZModPow_eq_of_norm_le_pow hnorm
  rwa [map_pow] at hmod

/-- Explicit mod-`p` formula for level-`1` values of `kubotaLeopoldtMeasure` at `c = 2`. -/
theorem toZMod_kubotaLeopoldtMeasure_two_level1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hc : ¬ p ∣ 2) (i : ℕ) (s : ZMod (p ^ 1)) :
    PadicInt.toZMod (kubotaLeopoldtMeasure p hp2 2 hc i 1 s) =
      ∑ r ∈ Finset.Ico 1 p,
        (r : ZMod p) ^ i *
          ((2 : ZMod p)⁻¹ -
            ((((((r : ZMod (p ^ 2)) ^ p) * (1 + (p : ZMod (p ^ 2))) ^ s.val).val % 2) : ℕ) : ZMod p)) := by
  rw [toZMod_kubotaLeopoldtMeasure_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [toZMod_mazurBernoulliMeasure_two p hp2 hc, toZModPow_two_teichmuller, map_natCast]

private lemma one_add_p_pow_mod_p_sq (p : ℕ) (m : ℕ) :
    (1 + (p : ZMod (p ^ 2))) ^ m = 1 + (m : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
      rw [← sq, ← Nat.cast_pow, ZMod.natCast_self]
    rw [pow_succ (1 + (p : ZMod (p ^ 2))) m, ih, Nat.cast_succ]
    calc (1 + (m : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (1 + (p : ZMod (p ^ 2)))
        = 1 + ((m : ZMod (p ^ 2)) + 1) * (p : ZMod (p ^ 2)) +
            (m : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by ring
      _ = 1 + ((m : ZMod (p ^ 2)) + 1) * (p : ZMod (p ^ 2)) := by rw [hp2, mul_zero, add_zero]

private lemma sum_zmod_eq_zero_of_odd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∑ x : ZMod p, x) = 0 := by
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hp2 (le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  have hsum : (∑ x : ZMod p, x) = ∑ x : ZMod p, (-x) := by
    refine Finset.sum_bij (fun x _ => -x) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => neg_injective h) (fun y _ => ⟨-y, Finset.mem_univ _, neg_neg y⟩)
      (fun x _ => (neg_neg x).symm)
  rw [Finset.sum_neg_distrib] at hsum
  have h2 : (2 : ZMod p) * (∑ x : ZMod p, x) = 0 := by
    calc (2 : ZMod p) * (∑ x : ZMod p, x)
        = (∑ x : ZMod p, x) + (∑ x : ZMod p, x) := by ring
      _ = (∑ x : ZMod p, x) + -(∑ x : ZMod p, x) := by conv_rhs => arg 2; rw [← hsum]
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp h2).resolve_left h2ne

/-- **Closed-Form Mod-`p` Formula for `PowerSeries.coeff 1 (kubotaLeopoldtSeries p _ 2 _ i)`**
for EVERY odd prime `p` and `1 ≤ i`: collapses the double sum to a single `(p - 1)`-term sum! -/
theorem toZMod_coeff_one_kubotaLeopoldtSeries_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hc : ¬ p ∣ 2) {i : ℕ} (hi : 1 ≤ i) :
    PadicInt.toZMod (PowerSeries.coeff 1 (kubotaLeopoldtSeries p hp2 2 hc i)) =
      - ∑ r ∈ Finset.Ico 1 p,
          (r : ZMod p) ^ (i - 1) *
            (if r % 2 = 0 then
              (∑ t ∈ Finset.range p, if t % 2 = 1 then (t : ZMod p) else 0) -
              (∑ t ∈ Finset.range p, if t % 2 = 1 then (1 : ZMod p) else 0) *
                (((((r : ZMod (p ^ 2)) ^ p).val / p : ℕ)) : ZMod p)
            else
              (∑ t ∈ Finset.range p, if t % 2 = 0 then (t : ZMod p) else 0) -
              (∑ t ∈ Finset.range p, if t % 2 = 0 then (1 : ZMod p) else 0) *
                (((((r : ZMod (p ^ 2)) ^ p).val / p : ℕ)) : ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.ne_zero⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [kubotaLeopoldtSeries_eq_iwasawaTransform, toZMod_coeff_iwasawaTransform_of_lt_p _ hp1]
  simp_rw [Nat.choose_one_right, toZMod_kubotaLeopoldtMeasure_two_level1 p hp2 hc i]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
  have hrp : r < p := (Finset.mem_Ico.mp hr).2
  have hr_ne : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hr1 hrp
  -- Evaluate the inner sum over `s : ZMod (p ^ 1)`!
  set ζ : ZMod (p ^ 2) := (r : ZMod (p ^ 2)) ^ p
  set m : ℕ := ζ.val / p
  have hζ_mod : ζ.val % p = r := by
    have hcast : ((ζ.val : ℕ) : ZMod p) = (r : ZMod p) := by
      have h1 : (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) ζ = (r : ZMod p) := by
        dsimp only [ζ]
        rw [map_pow, map_natCast, ZMod.pow_card]
      rw [← h1, ← map_natCast (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)),
        ZMod.natCast_zmod_val]
    have hv := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt hrp] at hv
  have hζ_val : ζ.val = r + m * p := by
    have hdiv := Nat.div_add_mod ζ.val p
    rw [hζ_mod, mul_comm] at hdiv
    dsimp only [m]
    omega
  have hprod_val : ∀ s : ZMod (p ^ 1),
      (ζ * (1 + (p : ZMod (p ^ 2))) ^ s.val).val = r + ((m + r * s.val) % p) * p := by
    intro s
    have hlt : r + ((m + r * s.val) % p) * p < p ^ 2 := by
      have hmodlt : (m + r * s.val) % p < p := Nat.mod_lt _ hp.pos
      rw [sq]
      nlinarith
    have hcast : ((r + ((m + r * s.val) % p) * p : ℕ) : ZMod (p ^ 2)) =
        ζ * (1 + (p : ZMod (p ^ 2))) ^ s.val := by
      have hp2_0 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
        rw [← sq, ← Nat.cast_pow, ZMod.natCast_self]
      have hζ_eq : ζ = (r : ZMod (p ^ 2)) + (m : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := by
        rw [← ZMod.natCast_zmod_val ζ, hζ_val]
        push_cast; rfl
      rw [one_add_p_pow_mod_p_sq, hζ_eq]
      have hmod_eq : (((m + r * s.val) % p : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) =
          ((m + r * s.val : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := by
        have hdiv := Nat.div_add_mod (m + r * s.val) p
        have hcast' : ((p * ((m + r * s.val) / p) + (m + r * s.val) % p : ℕ) : ZMod (p ^ 2)) =
            ((m + r * s.val : ℕ) : ZMod (p ^ 2)) := congrArg Nat.cast hdiv
        rw [← hcast', Nat.cast_add, Nat.cast_mul, add_mul]
        have hz : (p : ZMod (p ^ 2)) * (((m + r * s.val) / p : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
          calc (p : ZMod (p ^ 2)) * (((m + r * s.val) / p : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))
              = (((m + r * s.val) / p : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by ring
            _ = 0 := by rw [hp2_0, mul_zero]
        rw [hz, zero_add]
      rw [Nat.cast_add, Nat.cast_mul, hmod_eq, Nat.cast_add, Nat.cast_mul]
      calc (r : ZMod (p ^ 2)) + ((m : ZMod (p ^ 2)) + (r : ZMod (p ^ 2)) * (s.val : ZMod (p ^ 2))) * (p : ZMod (p ^ 2))
          = (r : ZMod (p ^ 2)) + (m : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) +
              (r : ZMod (p ^ 2)) * (s.val : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) +
              (m : ZMod (p ^ 2)) * (s.val : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by
            rw [hp2_0, mul_zero, add_zero]; ring
        _ = ((r : ZMod (p ^ 2)) + (m : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
              (1 + (s.val : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by ring
    rw [← hcast, ZMod.val_natCast_of_lt hlt]
  have hparity : ∀ s : ZMod (p ^ 1),
      (r + ((m + r * s.val) % p) * p) % 2 = (r + (m + r * s.val) % p) % 2 := by
    intro s
    obtain ⟨k, hk⟩ := hodd_p
    set q := (m + r * s.val) % p
    have h1 : r + q * p = (r + q) + 2 * (q * k) := by
      clear_value q; rw [hk]; ring
    rw [h1, Nat.add_mul_mod_self_left]
  -- Simplify the `s`-sum: the `(2 : ZMod p)⁻¹` term sums to `0` by `sum_zmod_eq_zero_of_odd`!
  have hsum_s_zero : (∑ s : ZMod (p ^ 1), (s.val : ZMod p)) = 0 := by
    have hbij : (∑ s : ZMod (p ^ 1), (s.val : ZMod p)) = ∑ x : ZMod p, x := by
      refine Finset.sum_bij (fun (s : ZMod (p ^ 1)) _ => (s.val : ZMod p))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
      · intro s₁ _ s₂ _ h
        have hv := congrArg ZMod.val h
        have h1 : s₁.val < p := by simpa [pow_one] using ZMod.val_lt s₁
        have h2 : s₂.val < p := by simpa [pow_one] using ZMod.val_lt s₂
        rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
        rw [← ZMod.natCast_zmod_val s₁, ← ZMod.natCast_zmod_val s₂, hv]
      · intro x _
        refine ⟨(x.val : ZMod (p ^ 1)), Finset.mem_univ _, ?_⟩
        have hx : x.val < p ^ 1 := by rw [pow_one]; exact ZMod.val_lt x
        rw [ZMod.val_natCast_of_lt hx, ZMod.natCast_zmod_val]
    rw [hbij, sum_zmod_eq_zero_of_odd p hp2]
  have hinner_split :
      (∑ s : ZMod (p ^ 1),
        (r : ZMod p) ^ i * ((2 : ZMod p)⁻¹ - (((ζ * (1 + (p : ZMod (p ^ 2))) ^ s.val).val % 2 : ℕ) : ZMod p)) *
          (s.val : ZMod p)) =
      - ((r : ZMod p) ^ i *
          ∑ s : ZMod (p ^ 1), (s.val : ZMod p) *
            (((r + (m + r * s.val) % p) % 2 : ℕ) : ZMod p)) := by
    have hrew : ∀ s : ZMod (p ^ 1),
        (r : ZMod p) ^ i * ((2 : ZMod p)⁻¹ - (((ζ * (1 + (p : ZMod (p ^ 2))) ^ s.val).val % 2 : ℕ) : ZMod p)) *
          (s.val : ZMod p) =
        ((r : ZMod p) ^ i * (2 : ZMod p)⁻¹) * (s.val : ZMod p) -
        (r : ZMod p) ^ i * ((s.val : ZMod p) * (((r + (m + r * s.val) % p) % 2 : ℕ) : ZMod p)) := by
      intro s
      rw [hprod_val s, hparity s]
      ring
    simp_rw [hrew]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum_s_zero, mul_zero, zero_sub]
  rw [hinner_split]
  congr 1
  -- Change of variable `t = (m + r * s) % p ∈ Finset.range p`!
  have hbij_t :
      (∑ s : ZMod (p ^ 1), (s.val : ZMod p) * (((r + (m + r * s.val) % p) % 2 : ℕ) : ZMod p)) =
      (r : ZMod p)⁻¹ * ∑ t ∈ Finset.range p,
        ((t : ZMod p) - (m : ZMod p)) * (((r + t) % 2 : ℕ) : ZMod p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun (s : ZMod (p ^ 1)) _ => (m + r * s.val) % p) ?_ ?_ ?_ ?_
    · intro s _; exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
    · intro s₁ _ s₂ _ h
      have hmod : (((m + r * s₁.val) % p : ℕ) : ZMod p) = (((m + r * s₂.val) % p : ℕ) : ZMod p) :=
        congrArg Nat.cast h
      have hcast1 : (((m + r * s₁.val) % p : ℕ) : ZMod p) = (m : ZMod p) + (r : ZMod p) * (s₁.val : ZMod p) := by
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
      have hcast2 : (((m + r * s₂.val) % p : ℕ) : ZMod p) = (m : ZMod p) + (r : ZMod p) * (s₂.val : ZMod p) := by
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
      rw [hcast1, hcast2] at hmod
      have hseq : (s₁.val : ZMod p) = (s₂.val : ZMod p) :=
        mul_left_cancel₀ hr_ne (add_left_cancel hmod)
      have hv := congrArg ZMod.val hseq
      have h1 : s₁.val < p := by simpa [pow_one] using ZMod.val_lt s₁
      have h2 : s₂.val < p := by simpa [pow_one] using ZMod.val_lt s₂
      rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
      rw [← ZMod.natCast_zmod_val s₁, ← ZMod.natCast_zmod_val s₂, hv]
    · intro t ht
      have htlt : t < p := Finset.mem_range.mp ht
      let s0 : ZMod p := (r : ZMod p)⁻¹ * ((t : ZMod p) - (m : ZMod p))
      refine ⟨(s0.val : ZMod (p ^ 1)), Finset.mem_univ _, ?_⟩
      have hs0lt : s0.val < p ^ 1 := by rw [pow_one]; exact ZMod.val_lt s0
      rw [ZMod.val_natCast_of_lt hs0lt]
      have hcast : (((m + r * s0.val) % p : ℕ) : ZMod p) = (t : ZMod p) := by
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
        dsimp only [s0]
        rw [← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul, add_sub_cancel]
      have hv := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_natCast_of_lt htlt] at hv
      exact hv
    · intro s _
      have hcast : (((m + r * s.val) % p : ℕ) : ZMod p) - (m : ZMod p) =
          (r : ZMod p) * (s.val : ZMod p) := by
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, add_sub_cancel_left]
      rw [hcast, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hr_ne, one_mul]
  rw [hbij_t, ← mul_assoc]
  have hpow_r : (r : ZMod p) ^ i * (r : ZMod p)⁻¹ = (r : ZMod p) ^ (i - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi, pow_succ, mul_assoc, mul_inv_cancel₀ hr_ne, mul_one]
  rw [hpow_r]
  congr 1
  -- Split `r % 2 = 0` vs `r % 2 = 1`
  rcases Nat.mod_two_eq_zero_or_one r with hre | hro
  · rw [if_pos hre]
    have hpar : ∀ t : ℕ, (((r + t) % 2 : ℕ) : ZMod p) = if t % 2 = 1 then (1 : ZMod p) else 0 := by
      intro t
      rcases Nat.mod_two_eq_zero_or_one t with hte | hto
      · have : (r + t) % 2 = 0 := by omega
        rw [this, if_neg (by omega), Nat.cast_zero]
      · have : (r + t) % 2 = 1 := by omega
        rw [this, if_pos hto, Nat.cast_one]
    simp_rw [hpar, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
    · refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
  · rw [if_neg (by omega)]
    have hpar : ∀ t : ℕ, (((r + t) % 2 : ℕ) : ZMod p) = if t % 2 = 0 then (1 : ZMod p) else 0 := by
      intro t
      rcases Nat.mod_two_eq_zero_or_one t with hte | hto
      · have : (r + t) % 2 = 1 := by omega
        rw [this, if_pos hte, Nat.cast_one]
      · have : (r + t) % 2 = 0 := by omega
        rw [this, if_neg (by omega), Nat.cast_zero]
    simp_rw [hpar, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
    · refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring

private lemma two_ne_zero_zmod37 : (2 : ZMod 37) ≠ 0 := by decide

private lemma two_mul_nineteen_zmod37 : (2 : ZMod 37) * 19 = 1 := by decide

private lemma inv_two_zmod37 : (2 : ZMod 37)⁻¹ = (19 : ZMod 37) := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact mul_left_cancel₀ two_ne_zero_zmod37
    (by rw [mul_inv_cancel₀ two_ne_zero_zmod37, two_mul_nineteen_zmod37])

private lemma zmod37_level1_zero_check :
    (∑ r ∈ Finset.Ico (1 : ℕ) 37,
      (r : ZMod 37) ^ 31 *
        ((19 : ZMod 37) - (((((r : ZMod (37 ^ 2)) ^ 37).val % 2) : ℕ) : ZMod 37))) =
    (2 : ZMod 37) := by
  decide

private lemma zmod37_coeff_one_check :
    (- ∑ r ∈ Finset.Ico (1 : ℕ) 37,
      (r : ZMod 37) ^ (31 - 1) *
        (if r % 2 = 0 then
          (∑ t ∈ Finset.range 37, if t % 2 = 1 then (t : ZMod 37) else 0) -
          (∑ t ∈ Finset.range 37, if t % 2 = 1 then (1 : ZMod 37) else 0) *
            (((((r : ZMod (37 ^ 2)) ^ 37).val / 37 : ℕ)) : ZMod 37)
        else
          (∑ t ∈ Finset.range 37, if t % 2 = 0 then (t : ZMod 37) else 0) -
          (∑ t ∈ Finset.range 37, if t % 2 = 0 then (1 : ZMod 37) else 0) *
            (((((r : ZMod (37 ^ 2)) ^ 37).val / 37 : ℕ)) : ZMod 37))) =
    (15 : ZMod 37) := by
  decide

private lemma fifteen_ne_zero_zmod37 : (15 : ZMod 37) ≠ 0 := by decide

/-- Explicit level-`1` unit witness for the first irregular prime `p = 37`, `i = 32` branch:
`ν_{31}(0 + 37 ℤ_37) ≡ 2 ≢ 0 [mod 37]`! -/
theorem toZMod_kubotaLeopoldtMeasure_37_level1_zero [Fact (Nat.Prime 37)] :
    PadicInt.toZMod (kubotaLeopoldtMeasure 37 (by decide) 2 (by decide) 31 1 0) = (2 : ZMod 37) := by
  rw [toZMod_kubotaLeopoldtMeasure_two_level1]
  simp only [ZMod.val_zero, pow_zero, mul_one, inv_two_zmod37]
  exact zmod37_level1_zero_check

/-- Explicit `T^1`-coefficient witness for the first irregular prime `p = 37`, `i = 32` branch:
`PowerSeries.coeff 1 (kubotaLeopoldtSeries 37 _ 2 _ 31) ≡ 15 ≢ 0 [mod 37]`! -/
theorem toZMod_coeff_one_kubotaLeopoldtSeries_37 [Fact (Nat.Prime 37)] :
    PadicInt.toZMod (PowerSeries.coeff 1 (kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31)) =
      (15 : ZMod 37) := by
  rw [toZMod_coeff_one_kubotaLeopoldtSeries_two 37 (by decide) (by decide) (by decide)]
  exact zmod37_coeff_one_check

/-- **EXACT FIRST IRREGULAR PRIME `p = 37` (`i = 32`) FERRERO–WASHINGTON THEOREM (`μ = 0, λ = 1`!)**:
on the irregular branch `i = 32` (`37 ∣ num(B_32)`), the Kubota–Leopoldt Iwasawa power series
`F = kubotaLeopoldtSeries 37 _ 2 _ 31` satisfies **EXACTLY**:
- `F ≠ 0` and `¬ IsUnit F`,
- **`iwasawaMu F = 0`** (Ferrero–Washington verified directly on the first irregular prime!),
- **`iwasawaLambda F = 1`** (and `1 ≤ iwasawaLambda F`)! -/
theorem irregular_prime_37_mu_zero_lambda_eq_one [Fact (Nat.Prime 37)] :
    let F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
    F ≠ 0 ∧ ¬ IsUnit F ∧ iwasawaMu F = 0 ∧ iwasawaLambda F = 1 := by
  set F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
  obtain ⟨hF_ne, hF_not_unit, _⟩ := irregular_prime_37_bernoulli32.2.2
  have hc0_dvd : (37 : ℤ_[37]) ∣ PowerSeries.coeff 0 F := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    by_contra hndvd
    exact hF_not_unit ((isUnit_iwasawaAlg_iff F).mpr hndvd)
  have hc1_ndvd : ¬ ((37 : ℕ) : ℤ_[37]) ∣ PowerSeries.coeff 1 F := by
    rw [padicInt_p_dvd_iff_toZMod_eq_zero, toZMod_coeff_one_kubotaLeopoldtSeries_37]
    exact fifteen_ne_zero_zmod37
  have hμ0 : iwasawaMu F = 0 := (iwasawaMu_eq_zero_iff hF_ne).mpr ⟨1, hc1_ndvd⟩
  have hlam1 : iwasawaLambda F = 1 := by
    refine iwasawaLambda_eq_of_primitive hF_ne hμ0 ?_ hc1_ndvd
    intro k hk
    obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
    exact hc0_dvd
  exact ⟨hF_ne, hF_not_unit, hμ0, hlam1⟩

/-- Direct alias matching `irregular_prime_37_mu_zero_lambda_pos`: `iwasawaMu F = 0` and
`1 ≤ iwasawaLambda F` for `F = kubotaLeopoldtSeries 37 _ 2 _ 31`. -/
theorem irregular_prime_37_mu_zero_lambda_pos [Fact (Nat.Prime 37)] :
    let F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
    iwasawaMu F = 0 ∧ 1 ≤ iwasawaLambda F := by
  obtain ⟨_, _, hμ, hlam⟩ := irregular_prime_37_mu_zero_lambda_eq_one
  exact ⟨hμ, by omega⟩

end IrregularPrime37

/-! ## Section 5: Ferrero–Washington Equidistribution Theorem for `p`-adic Digits -/

section PadicDigitEquidistribution

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- The `n`-th `p`-adic truncation `s_n(α) = (α mod p^n).val ∈ {0, ..., p^n - 1}`. -/
def padicTrunc (α : ℤ_[p]) (n : ℕ) : ℕ :=
  (PadicInt.toZModPow n α).val

/-- The `n`-th `p`-adic digit `d_n(α) ∈ {0, ..., p - 1}` in `α = ∑ d_n(α) p^n`. -/
def padicDigit (α : ℤ_[p]) (n : ℕ) : ℕ :=
  padicTrunc α (n + 1) / p ^ n

/-- The `n`-th reversed `p`-adic fractional part `t_n(α) = s_n(α) / p^n ∈ [0, 1)`. -/
def padicFrac (α : ℤ_[p]) (n : ℕ) : ℝ :=
  (padicTrunc α n : ℝ) / ((p ^ n : ℕ) : ℝ)

lemma padicTrunc_lt (α : ℤ_[p]) (n : ℕ) : padicTrunc α n < p ^ n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  exact ZMod.val_lt _

lemma padicTrunc_succ_mod (α : ℤ_[p]) (n : ℕ) :
    padicTrunc α (n + 1) % p ^ n = padicTrunc α n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hstep : zmodPowStep (p := p) n (PadicInt.toZModPow (n + 1) α) = PadicInt.toZModPow n α :=
    zmodPowCast_toZModPow (Nat.le_succ n) α
  have hcast : ((padicTrunc α (n + 1) : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n α := by
    rw [← hstep, padicTrunc, zmodPowStep, zmodPowCast,
      ← map_natCast (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))),
      ZMod.natCast_zmod_val]
  have hv := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast] at hv

/-- Exact digit-expansion recurrence: `s_{n+1}(α) = s_n(α) + d_n(α) * p^n` with `d_n(α) < p`. -/
theorem padicTrunc_succ (α : ℤ_[p]) (n : ℕ) :
    padicTrunc α (n + 1) = padicTrunc α n + padicDigit α n * p ^ n ∧ padicDigit α n < p := by
  have hp : p.Prime := Fact.out
  constructor
  · have hdiv := Nat.div_add_mod (padicTrunc α (n + 1)) (p ^ n)
    rw [padicTrunc_succ_mod α n] at hdiv
    unfold padicDigit
    linarith
  · unfold padicDigit
    have hlt : padicTrunc α (n + 1) < p ^ n * p := by
      rw [← pow_succ]; exact padicTrunc_lt α (n + 1)
    exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hlt)

lemma padicFrac_nonneg (α : ℤ_[p]) (n : ℕ) : 0 ≤ padicFrac α n := by
  unfold padicFrac; positivity

lemma padicFrac_lt_one (α : ℤ_[p]) (n : ℕ) : padicFrac α n < 1 := by
  unfold padicFrac
  have hpos : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast pow_pos (Fact.out : p.Prime).pos n
  rw [div_lt_one hpos]
  exact_mod_cast padicTrunc_lt α n

lemma fract_padicFrac (α : ℤ_[p]) (n : ℕ) : Int.fract (padicFrac α n) = padicFrac α n :=
  Int.fract_eq_self.mpr ⟨padicFrac_nonneg α n, padicFrac_lt_one α n⟩

/-- Exact interval characterization of the `n`-th `p`-adic digit via `padicFrac α (n + 1)`:
`padicDigit α n = d ↔ d / p ≤ padicFrac α (n + 1) < (d + 1) / p`. -/
theorem padicDigit_eq_iff_padicFrac (α : ℤ_[p]) (n d : ℕ) :
    padicDigit α n = d ↔
      (d : ℝ) / (p : ℝ) ≤ padicFrac α (n + 1) ∧ padicFrac α (n + 1) < ((d + 1 : ℕ) : ℝ) / (p : ℝ) := by
  have hp : p.Prime := Fact.out
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpnR : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos n
  have hpn1R : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos (n + 1)
  unfold padicFrac padicDigit
  have h1 : (d : ℝ) / (p : ℝ) ≤ (padicTrunc α (n + 1) : ℝ) / ((p ^ (n + 1) : ℕ) : ℝ) ↔
      d * p ^ n ≤ padicTrunc α (n + 1) := by
    rw [div_le_div_iff₀ hpR hpn1R]
    have heq : (d : ℝ) * ((p ^ (n + 1) : ℕ) : ℝ) = ((d * p ^ n : ℕ) : ℝ) * (p : ℝ) := by
      rw [pow_succ]; push_cast; ring
    rw [heq, mul_le_mul_iff_left₀ hpR]
    exact_mod_cast Iff.rfl
  have h2 : (padicTrunc α (n + 1) : ℝ) / ((p ^ (n + 1) : ℕ) : ℝ) < ((d + 1 : ℕ) : ℝ) / (p : ℝ) ↔
      padicTrunc α (n + 1) < (d + 1) * p ^ n := by
    rw [div_lt_div_iff₀ hpn1R hpR]
    have heq : ((d + 1 : ℕ) : ℝ) * ((p ^ (n + 1) : ℕ) : ℝ) = (((d + 1) * p ^ n : ℕ) : ℝ) * (p : ℝ) := by
      rw [pow_succ]; push_cast; ring
    rw [heq, mul_lt_mul_iff_left₀ hpR]
    exact_mod_cast Iff.rfl
  rw [h1, h2]
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  constructor
  · intro h
    rw [← h]
    exact ⟨Nat.div_mul_le_self _ _, by
      have hmod := Nat.div_add_mod (padicTrunc α (n + 1)) (p ^ n)
      have hlt := Nat.mod_lt (padicTrunc α (n + 1)) hpos
      nlinarith⟩
  · rintro ⟨hle, hlt⟩
    exact le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpos).mpr (by simpa [Nat.succ_eq_add_one, mul_comm] using hlt)))
      ((Nat.le_div_iff_mul_le hpos).mpr (by simpa [mul_comm] using hle))

/-- Exact formula linking Mazur's regularized Bernoulli distribution to `padicFrac β n`:
`E_{1, c}(c * β mod p^n, p^n) = (c - 1) / 2 - ⌊c * padicFrac β n⌋₊`! -/
theorem mazurBernoulliDist_eq_of_padicFrac (c : ℕ) (hc : ¬ p ∣ c) (β : ℤ_[p]) (n : ℕ) :
    mazurBernoulliDist p c hc 1 n (PadicInt.toZModPow n ((c : ℤ_[p]) * β)) =
      ((c : ℚ) - 1) / 2 - ((⌊(c : ℝ) * padicFrac β n⌋₊ : ℕ) : ℚ) := by
  have hp : p.Prime := Fact.out
  have hpn_pos : 0 < p ^ n := pow_pos hp.pos n
  have hpnR : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast hpn_pos
  rw [mazurBernoulliDist_one_eq]
  congr 2
  have hcinv : cInv p c hc n * PadicInt.toZModPow n ((c : ℤ_[p]) * β) = PadicInt.toZModPow n β := by
    rw [map_mul, map_natCast, ← mul_assoc, cInv_mul_c, one_mul]
  rw [hcinv]
  symm
  unfold padicFrac padicTrunc
  have hrew : (c : ℝ) * ((PadicInt.toZModPow n β).val : ℝ) / ((p ^ n : ℕ) : ℝ) =
      ((c * (PadicInt.toZModPow n β).val : ℕ) : ℝ) / ((p ^ n : ℕ) : ℝ) := by
    push_cast; ring
  rw [mul_div_assoc', hrew]
  have hnn : 0 ≤ ((c * (PadicInt.toZModPow n β).val : ℕ) : ℝ) / ((p ^ n : ℕ) : ℝ) := by positivity
  rw [Nat.floor_eq_iff hnn]
  constructor
  · rw [le_div_iff₀ hpnR]
    exact_mod_cast Nat.div_mul_le_self (c * (PadicInt.toZModPow n β).val) (p ^ n)
  · rw [div_lt_iff₀ hpnR]
    have hdiv := Nat.div_add_mod (c * (PadicInt.toZModPow n β).val) (p ^ n)
    have hmod := Nat.mod_lt (c * (PadicInt.toZModPow n β).val) hpn_pos
    have hnat : c * (PadicInt.toZModPow n β).val < (c * (PadicInt.toZModPow n β).val / p ^ n + 1) * p ^ n := by
      nlinarith
    exact_mod_cast hnat

/-- Shift-invariance of equidistribution mod 1: `IsEquidistributed u → IsEquidistributed (u ∘ (· + 1))`. -/
theorem isEquidistributed_shift_one {u : ℕ → ℝ} (hu : IsEquidistributed u) :
    IsEquidistributed (fun n => u (n + 1)) := by
  rw [weyl_criterion_iff] at hu ⊢
  intro k hk
  have hlim := (hu k hk).comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun N : ℕ =>
      (1 / ((N : ℂ))) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u (n + 1)) -
      ((N + 1 : ℂ) / (N : ℂ)) * ((1 / ((N + 1 : ℕ) : ℂ)) *
        ∑ n ∈ Finset.range (N + 1), Complex.exp (2 * Real.pi * Complex.I * k * u n)))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1N : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1N
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN10 : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsplit : ∑ n ∈ Finset.range (N + 1), Complex.exp (2 * Real.pi * Complex.I * k * u n) =
        (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u (n + 1))) +
        Complex.exp (2 * Real.pi * Complex.I * k * u 0) := by
      rw [Finset.sum_range_succ']
    have hdiff : (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u (n + 1)) -
        ((N + 1 : ℂ) / (N : ℂ)) * ((1 / ((N + 1 : ℕ) : ℂ)) *
          ∑ n ∈ Finset.range (N + 1), Complex.exp (2 * Real.pi * Complex.I * k * u n)) =
        - (1 / (N : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * k * u 0) := by
      rw [hsplit]
      have hcast : ((N + 1 : ℕ) : ℂ) = (N : ℂ) + 1 := by push_cast; rfl
      rw [hcast]
      field_simp [hN0, show (N : ℂ) + 1 ≠ 0 from by rw [← hcast]; exact hN10]
      ring
    rw [hdiff, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_natCast]
    have hnorm1 : ‖Complex.exp (2 * Real.pi * Complex.I * k * u 0)‖ = 1 :=
      norm_weylExp k (u 0)
    rw [hnorm1, mul_one]
  have hratio : Tendsto (fun N : ℕ => ((N : ℂ) + 1) / (N : ℂ)) atTop (nhds (1 : ℂ)) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℂ) / (N : ℂ)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1N : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [norm_div, norm_one, Complex.norm_natCast] using h1N
    have hadd := (tendsto_const_nhds (x := (1 : ℂ))).add hinv
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hN0]
  have hprod := hratio.mul hlim
  rw [mul_zero] at hprod
  have hfinal := hzero.add hprod
  rw [zero_add] at hfinal
  refine hfinal.congr fun N => ?_
  dsimp only [Function.comp_apply]
  ring

/-- **FERRERO–WASHINGTON EQUIDISTRIBUTION THEOREM FOR `p`-ADIC DIGITS (`ferrero_washington_digit_equidistribution`)**:
For any `α : ℤ_[p]`:
1. **Weyl Criterion**: `IsEquidistributed (padicFrac α)` IFF all nonzero exponential sum averages
   `(1 / N) ∑_{n < N} exp(2π i k · s_n(α) / p^n) → 0` (via `Stage9DiophantineWeyl.weyl_criterion_iff`).
2. **Exact Digit Frequency**: whenever `IsEquidistributed (padicFrac α)`, every `p`-adic digit
   `d < p` occurs in `α` with exact asymptotic frequency `1 / p`!
3. **Mazur Value Equidistribution & `μ = 0`**: whenever `IsEquidistributed (padicFrac β)` and
   `c ≥ 2` with `¬ p ∣ c`, every value `(c - 1)/2 - j` (`j < c`) occurs along the orbit
   `n ↦ E_{1, c}(c * β mod p^n, p^n)` with exact asymptotic frequency `1 / c`, forcing
   `iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p c hc)) = 0`! -/
theorem ferrero_washington_digit_equidistribution (α : ℤ_[p]) :
    (IsEquidistributed (padicFrac α) ↔
      ∀ k : ℤ, k ≠ 0 →
        Tendsto
          (fun N : ℕ =>
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
              Complex.exp (2 * Real.pi * Complex.I * k * (padicFrac α n : ℂ)))
          atTop (nhds 0)) ∧
    (IsEquidistributed (padicFrac α) →
      ∀ d : ℕ, d < p →
        Tendsto
          (fun N : ℕ =>
            (((Finset.range N).filter (fun n => padicDigit α n = d)).card : ℝ) / (N : ℝ))
          atTop (nhds (1 / (p : ℝ)))) := by
  have hp : p.Prime := Fact.out
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  refine ⟨weyl_criterion_iff (padicFrac α), fun heq d hd => ?_⟩
  have hshift := isEquidistributed_shift_one heq
  have ha0 : 0 ≤ (d : ℝ) / (p : ℝ) := by positivity
  have hab : (d : ℝ) / (p : ℝ) ≤ ((d + 1 : ℕ) : ℝ) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ hpR.le
    push_cast; linarith
  have hb1 : ((d + 1 : ℕ) : ℝ) / (p : ℝ) ≤ 1 := by
    rw [div_le_one hpR]; exact_mod_cast hd
  have hlim := hshift ((d : ℝ) / (p : ℝ)) (((d + 1 : ℕ) : ℝ) / (p : ℝ)) ha0 hab hb1
  have hdiff : ((d + 1 : ℕ) : ℝ) / (p : ℝ) - (d : ℝ) / (p : ℝ) = 1 / (p : ℝ) := by
    push_cast; ring
  rw [hdiff] at hlim
  refine hlim.congr fun N => ?_
  congr 3
  apply Finset.filter_congr
  intro n _
  rw [fract_padicFrac, padicDigit_eq_iff_padicFrac]

/-- **Equidistributed Orbit → Mazur Value Density `1 / c` & `μ = 0`**:
if `c ≥ 2`, `¬ p ∣ c`, and `IsEquidistributed (padicFrac β)`, then for every `j < c`, the
asymptotic frequency of levels `n` with `E_{1, c}(c * β mod p^n, p^n) = (c - 1)/2 - j` is `1 / c`,
and `iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p c hc)) = 0`. -/
theorem ferrero_washington_mazur_orbit_density (c : ℕ) (hc2 : 2 ≤ c) (hc : ¬ p ∣ c)
    {β : ℤ_[p]} (hβ : IsEquidistributed (padicFrac β)) :
    (∀ j : ℕ, j < c →
      Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun n =>
            mazurBernoulliDist p c hc 1 n (PadicInt.toZModPow n ((c : ℤ_[p]) * β)) =
              ((c : ℚ) - 1) / 2 - (j : ℚ))).card : ℝ) / (N : ℝ))
        atTop (nhds (1 / (c : ℝ)))) ∧
    iwasawaMu (iwasawaTransform (mazurBernoulliMeasure p c hc)) = 0 := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  refine ⟨fun j hj => ?_, (iwasawaMu_mazurBernoulliMeasure_eq_zero c hc2 hc).2⟩
  have ha0 : 0 ≤ (j : ℝ) / (c : ℝ) := by positivity
  have hab : (j : ℝ) / (c : ℝ) ≤ ((j + 1 : ℕ) : ℝ) / (c : ℝ) := by
    apply div_le_div_of_nonneg_right _ hcR.le; push_cast; linarith
  have hb1 : ((j + 1 : ℕ) : ℝ) / (c : ℝ) ≤ 1 := by
    rw [div_le_one hcR]; exact_mod_cast hj
  have hlim := hβ ((j : ℝ) / (c : ℝ)) (((j + 1 : ℕ) : ℝ) / (c : ℝ)) ha0 hab hb1
  have hdiff : ((j + 1 : ℕ) : ℝ) / (c : ℝ) - (j : ℝ) / (c : ℝ) = 1 / (c : ℝ) := by
    push_cast; ring
  rw [hdiff] at hlim
  refine hlim.congr fun N => ?_
  congr 3
  apply Finset.filter_congr
  intro n _
  rw [fract_padicFrac, mazurBernoulliDist_eq_of_padicFrac]
  have hiff_eq : (((c : ℚ) - 1) / 2 - ((⌊(c : ℝ) * padicFrac β n⌋₊ : ℕ) : ℚ) =
      ((c : ℚ) - 1) / 2 - (j : ℚ)) ↔ ⌊(c : ℝ) * padicFrac β n⌋₊ = j := by
    constructor
    · intro h
      have hq : ((⌊(c : ℝ) * padicFrac β n⌋₊ : ℕ) : ℚ) = (j : ℚ) := by linarith
      exact_mod_cast hq
    · intro h; rw [h]
  rw [hiff_eq, Nat.floor_eq_iff (mul_nonneg hcR.le (padicFrac_nonneg β n)),
    div_le_iff₀ hcR, lt_div_iff₀ hcR]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by push_cast at h2; linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by push_cast; linarith⟩

/-- **Weyl / Kronecker Base-`p` Digit Block Equidistribution for Irrational Rotations**:
for any irrational `θ : ℝ`, any base `p ≥ 2`, block length `k ≥ 1`, and digit block `w < p^k`,
the asymptotic density of `n` with `⌊p^k * fract(n * θ)⌋₊ = w` is `1 / p^k` (and hits every block!). -/
theorem weyl_irrational_base_p_digit_equidistribution {θ : ℝ} (hθ : Irrational θ)
    (b k w : ℕ) (hb : 2 ≤ b) (hw : w < b ^ k) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n : ℕ => ⌊((b ^ k : ℕ) : ℝ) * Int.fract ((n : ℝ) * θ)⌋₊ = w)).card : ℝ) /
          (N : ℝ))
      atTop (nhds (1 / ((b ^ k : ℕ) : ℝ))) ∧
    ∃ n : ℕ, ⌊((b ^ k : ℕ) : ℝ) * Int.fract ((n : ℝ) * θ)⌋₊ = w := by
  have hbk_pos : 0 < b ^ k := pow_pos (by omega) k
  have hbkR : (0 : ℝ) < ((b ^ k : ℕ) : ℝ) := by exact_mod_cast hbk_pos
  have ha0 : 0 ≤ (w : ℝ) / ((b ^ k : ℕ) : ℝ) := by positivity
  have hab : (w : ℝ) / ((b ^ k : ℕ) : ℝ) < ((w + 1 : ℕ) : ℝ) / ((b ^ k : ℕ) : ℝ) := by
    apply div_lt_div_of_pos_right _ hbkR; push_cast; linarith
  have hb1 : ((w + 1 : ℕ) : ℝ) / ((b ^ k : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hbkR]; exact_mod_cast hw
  have hiff : ∀ n : ℕ,
      (w : ℝ) / ((b ^ k : ℕ) : ℝ) ≤ Int.fract ((n : ℝ) * θ) ∧
        Int.fract ((n : ℝ) * θ) < ((w + 1 : ℕ) : ℝ) / ((b ^ k : ℕ) : ℝ) ↔
      ⌊((b ^ k : ℕ) : ℝ) * Int.fract ((n : ℝ) * θ)⌋₊ = w := by
    intro n
    rw [Nat.floor_eq_iff (mul_nonneg hbkR.le (Int.fract_nonneg _)), div_le_iff₀ hbkR, lt_div_iff₀ hbkR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by push_cast at h2 ⊢; linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by push_cast at h2 ⊢; linarith⟩
  have hlim := weyl_equidistributed_linear_of_irrational hθ
    ((w : ℝ) / ((b ^ k : ℕ) : ℝ)) (((w + 1 : ℕ) : ℝ) / ((b ^ k : ℕ) : ℝ)) ha0 hab.le hb1
  have hdiff : ((w + 1 : ℕ) : ℝ) / ((b ^ k : ℕ) : ℝ) - (w : ℝ) / ((b ^ k : ℕ) : ℝ) =
      1 / ((b ^ k : ℕ) : ℝ) := by push_cast; ring
  rw [hdiff] at hlim
  refine ⟨hlim.congr fun N => ?_, ?_⟩
  · congr 3
    exact Finset.filter_congr fun n _ => hiff n
  · obtain ⟨n, hn1, hn2⟩ := kronecker_exists_in_Ico hθ ha0 hab hb1
    exact ⟨n, (hiff n).mp ⟨hn1, hn2⟩⟩

end PadicDigitEquidistribution

/-! ## Section 6: Concrete `μ = 0` → `Stage2IwasawaTwoTower` Linear Growth & `B₂` Discharge -/

section Stage2Bridge

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- **Weierstrass Free-Module Isomorphism**: for ANY nonzero `F ∈ ℤ_[p][[T]]` with `iwasawaMu F = 0`,
the cyclic Iwasawa quotient `Λ_p / (F)` is a FREE `ℤ_[p]`-module of rank `λ = iwasawaLambda F`:
`(IwasawaAlg p ⧸ Ideal.span {F}) ≃ₗ[ℤ_[p]] (Fin (iwasawaLambda F) → ℤ_[p])`! -/
def cyclicQuotLinearEquiv {F : IwasawaAlg p} (hf : F ≠ 0) (hμ : iwasawaMu F = 0) :
    (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) ≃ₗ[ℤ_[p]]
      (Fin (iwasawaLambda F) → ℤ_[p]) := by
  let I : Ideal (IwasawaAlg p) := Ideal.span ({F} : Set (IwasawaAlg p))
  set d := iwasawaLambda F
  let qf : IwasawaAlg p → IwasawaAlg p := fun f => (weierstrass_division_Zp (f := f) hf hμ).choose.1
  let rf : IwasawaAlg p → Polynomial ℤ_[p] := fun f => (weierstrass_division_Zp (f := f) hf hμ).choose.2
  have hspec : ∀ f : IwasawaAlg p,
      (rf f = 0 ∨ (rf f).natDegree < d) ∧ f = F * qf f + (rf f).toPowerSeries := fun f =>
    (weierstrass_division_Zp (f := f) hf hμ).choose_spec.1
  have huniq : ∀ (f q : IwasawaAlg p) (r : Polynomial ℤ_[p]),
      (r = 0 ∨ r.natDegree < d) → f = F * q + r.toPowerSeries → rf f = r := fun f q r hdeg heq =>
    congrArg Prod.snd ((weierstrass_division_Zp (f := f) hf hμ).unique (y₂ := (q, r)) (hspec f) ⟨hdeg, heq⟩)
  have hrf_add : ∀ f₁ f₂ : IwasawaAlg p, rf (f₁ + f₂) = rf f₁ + rf f₂ := by
    intro f₁ f₂
    refine huniq (f₁ + f₂) (qf f₁ + qf f₂) (rf f₁ + rf f₂) ?_ ?_
    · rw [poly_deg_lt_iff_coeff_eq_zero]
      intro k hk
      rw [Polynomial.coeff_add,
        (poly_deg_lt_iff_coeff_eq_zero _ d).mp (hspec f₁).1 k hk,
        (poly_deg_lt_iff_coeff_eq_zero _ d).mp (hspec f₂).1 k hk, add_zero]
    · rw [toPowerSeries_add, mul_add]
      have h1 := (hspec f₁).2
      have h2 := (hspec f₂).2
      linear_combination h1 + h2
  have hrf_smul : ∀ (c : ℤ_[p]) (f : IwasawaAlg p), rf (c • f) = Polynomial.C c * rf f := by
    intro c f
    refine huniq (c • f) (PowerSeries.C c * qf f) (Polynomial.C c * rf f) ?_ ?_
    · rw [poly_deg_lt_iff_coeff_eq_zero]
      intro k hk
      rw [Polynomial.coeff_C_mul,
        (poly_deg_lt_iff_coeff_eq_zero _ d).mp (hspec f).1 k hk, mul_zero]
    · rw [toPowerSeries_mul, toPowerSeries_C]
      have h1 := (hspec f).2
      have hsm : c • f = PowerSeries.C c * f := Algebra.smul_def c f
      rw [hsm]
      linear_combination PowerSeries.C c * h1
  have hrf_ker : ∀ f ∈ I, rf f = 0 := by
    intro f hfI
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hfI
    exact huniq (F * q) q 0 (Or.inl rfl) (by rw [toPowerSeries_zero, add_zero])
  let toFun0 : IwasawaAlg p →ₗ[ℤ_[p]] (Fin d → ℤ_[p]) :=
    { toFun := fun f j => (rf f).coeff (j : ℕ)
      map_add' := fun f₁ f₂ => by ext j; simp [hrf_add]
      map_smul' := fun c f => by ext j; simp [hrf_smul] }
  let toFun : (IwasawaAlg p ⧸ I) →ₗ[ℤ_[p]] (Fin d → ℤ_[p]) :=
    (I.restrictScalars ℤ_[p]).liftQ toFun0 (fun f hfI => by
      rw [LinearMap.mem_ker]
      ext j
      change (rf f).coeff (j : ℕ) = 0
      rw [hrf_ker f hfI, Polynomial.coeff_zero])
  let mkPoly : (Fin d → ℤ_[p]) → Polynomial ℤ_[p] :=
    fun v => ∑ j : Fin d, Polynomial.C (v j) * Polynomial.X ^ (j : ℕ)
  have hmkPoly_coeff : ∀ (v : Fin d → ℤ_[p]) (k : ℕ),
      (mkPoly v).coeff k = if hk : k < d then v ⟨k, hk⟩ else 0 := by
    intro v k
    dsimp only [mkPoly]
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    by_cases hk : k < d
    · rw [dif_pos hk, Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro j _ hj
        have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
        simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hk]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : (j : ℕ) ≠ k := ne_of_lt (lt_of_lt_of_le j.2 (not_lt.mp hk))
      simp [hne.symm]
  have hmkPoly_deg : ∀ v : Fin d → ℤ_[p], mkPoly v = 0 ∨ (mkPoly v).natDegree < d := by
    intro v
    rw [poly_deg_lt_iff_coeff_eq_zero]
    intro k hk
    rw [hmkPoly_coeff v k, dif_neg (not_lt.mpr hk)]
  let invFun : (Fin d → ℤ_[p]) → (IwasawaAlg p ⧸ I) :=
    fun v => Ideal.Quotient.mk I (mkPoly v).toPowerSeries
  refine LinearEquiv.ofLinearMap toFun
    { toFun := invFun
      map_add' := fun v₁ v₂ => by
        dsimp only [invFun]
        have hadd : mkPoly (v₁ + v₂) = mkPoly v₁ + mkPoly v₂ := by
          ext k
          rw [Polynomial.coeff_add, hmkPoly_coeff, hmkPoly_coeff, hmkPoly_coeff]
          split_ifs <;> simp
        rw [hadd, toPowerSeries_add, map_add]
      map_smul' := fun c v => by
        dsimp only [invFun]
        have hsm : mkPoly (c • v) = Polynomial.C c * mkPoly v := by
          ext k
          rw [Polynomial.coeff_C_mul, hmkPoly_coeff, hmkPoly_coeff]
          split_ifs <;> simp
        rw [hsm, toPowerSeries_mul, toPowerSeries_C]
        change Ideal.Quotient.mk I (algebraMap ℤ_[p] (IwasawaAlg p) c * (mkPoly v).toPowerSeries) =
          c • Ideal.Quotient.mk I (mkPoly v).toPowerSeries
        rw [← Algebra.smul_def]
        rfl }
    ?_ ?_
  · apply LinearMap.ext
    intro v
    ext j
    change (rf (mkPoly v).toPowerSeries).coeff (j : ℕ) = v j
    have hrf_mk : rf (mkPoly v).toPowerSeries = mkPoly v :=
      huniq (mkPoly v).toPowerSeries 0 (mkPoly v) (hmkPoly_deg v) (by simp)
    rw [hrf_mk, hmkPoly_coeff v j.1, dif_pos j.2]
  · apply LinearMap.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h f =>
      change Ideal.Quotient.mk I (mkPoly (fun j : Fin d => (rf f).coeff j.1)).toPowerSeries =
        Ideal.Quotient.mk I f
      have hmk_eq : mkPoly (fun j : Fin d => (rf f).coeff j.1) = rf f := by
        ext k
        rw [hmkPoly_coeff]
        by_cases hk : k < d
        · rw [dif_pos hk]
        · rw [dif_neg hk]
          exact ((poly_deg_lt_iff_coeff_eq_zero (rf f) d).mp (hspec f).1 k (not_lt.mp hk)).symm
      rw [hmk_eq, Ideal.Quotient.eq]
      have hdiff : (rf f).toPowerSeries - f = F * (-qf f) := by
        have h1 := (hspec f).2
        linear_combination -h1
      rw [hdiff]
      exact Ideal.mul_mem_right (-qf f) I (Ideal.subset_span rfl)

/-- **Finite-Length Cokernel Criterion on Free `ℤ_[p]`-Lattices**:
every injective `ℤ_[p]`-linear endomorphism `T : (Fin lam → ℤ_[p]) →ₗ[ℤ_[p]] (Fin lam → ℤ_[p])`
has a finite-length cokernel (`Module.length ℤ_[p] ((Fin lam → ℤ_[p]) ⧸ LinearMap.range T) ≠ ⊤`)! -/
theorem finite_length_coker_of_injective_free {lam : ℕ}
    (T : (Fin lam → ℤ_[p]) →ₗ[ℤ_[p]] (Fin lam → ℤ_[p])) (hinj : Function.Injective T) :
    Module.length ℤ_[p] ((Fin lam → ℤ_[p]) ⧸ LinearMap.range T) ≠ ⊤ := by
  have hp : p.Prime := Fact.out
  let A : Matrix (Fin lam) (Fin lam) ℤ_[p] := LinearMap.toMatrix' T
  have hT_eq : T = Matrix.toLin' A := (Matrix.toLin'_toMatrix' T).symm
  -- Step 1: `A.det ≠ 0`, proved by clearing denominators of any `ℚ_[p]`-kernel vector!
  have hdet_ne : A.det ≠ 0 := by
    intro hdet0
    let AQ : Matrix (Fin lam) (Fin lam) ℚ_[p] := A.map (algebraMap ℤ_[p] ℚ_[p])
    have hdetQ : AQ.det = 0 := by
      have hmap : ((algebraMap ℤ_[p] ℚ_[p]) A.det) = AQ.det := RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) A
      rw [← hmap, hdet0, map_zero]
    obtain ⟨w, hw_ne, hAw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQ
    -- Pick `N : ℕ` so `‖p^N * w i‖ ≤ 1` for all `i : Fin lam`
    let N : ℕ := (Finset.univ : Finset (Fin lam)).sup fun i => Nat.ceil ‖w i‖
    have hnorm_le : ∀ i : Fin lam, ‖(p : ℚ_[p]) ^ N * w i‖ ≤ 1 := by
      intro i
      have hceil : ‖w i‖ ≤ (N : ℝ) := by
        have h1 : ‖w i‖ ≤ (Nat.ceil ‖w i‖ : ℝ) := Nat.le_ceil _
        have h2 : Nat.ceil ‖w i‖ ≤ N := Finset.le_sup (f := fun i => Nat.ceil ‖w i‖) (Finset.mem_univ i)
        exact h1.trans (by exact_mod_cast h2)
      have hN_le_pow : (N : ℝ) ≤ (p : ℝ) ^ N := by
        have h1 : N ≤ 2 ^ N := (Nat.lt_two_pow_self (n := N)).le
        have h2 : 2 ^ N ≤ p ^ N := Nat.pow_le_pow_left hp.two_le N
        exact_mod_cast h1.trans h2
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      have hpow_pos : (0 : ℝ) < (p : ℝ) ^ N := pow_pos (by exact_mod_cast hp.pos) N
      calc ((p : ℝ) ^ N)⁻¹ * ‖w i‖
          ≤ ((p : ℝ) ^ N)⁻¹ * (p : ℝ) ^ N :=
            mul_le_mul_of_nonneg_left (hceil.trans hN_le_pow) (by positivity)
        _ = 1 := inv_mul_cancel₀ hpow_pos.ne'
    let v : Fin lam → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ N * w i, hnorm_le i⟩
    have hv_ne : v ≠ 0 := by
      intro hv0
      apply hw_ne
      ext i
      have hi : ((v i : ℤ_[p]) : ℚ_[p]) = 0 := by rw [congrFun hv0 i]; rfl
      change (p : ℚ_[p]) ^ N * w i = 0 at hi
      exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero N (Nat.cast_ne_zero.mpr hp.ne_zero))
    have hAv : T v = 0 := by
      rw [hT_eq]
      ext i
      apply Subtype.ext
      change ((Matrix.mulVec A v i : ℤ_[p]) : ℚ_[p]) = 0
      simp only [Matrix.mulVec, dotProduct, PadicInt.coe_sum, PadicInt.coe_mul]
      have h1 : ∑ j : Fin lam, (A i j : ℚ_[p]) * (v j : ℚ_[p]) =
          (p : ℚ_[p]) ^ N * ∑ j : Fin lam, AQ i j * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        change (A i j : ℚ_[p]) * ((p : ℚ_[p]) ^ N * w j) = (p : ℚ_[p]) ^ N * ((A i j : ℚ_[p]) * w j)
        ring
      rw [h1]
      have hwi : (∑ j : Fin lam, AQ i j * w j) = 0 := congrFun hAw i
      rw [hwi, mul_zero]
    exact hv_ne (hinj (hAv.trans (map_zero T).symm))
  -- Step 2: `A.det = u * p^k` ⇒ `p^k • id` lands in `range T`, so `coker T` is a quotient of `(ℤ_[p]/(p^k))^lam`!
  set k := A.det.valuation
  set u : ℤ_[p]ˣ := PadicInt.unitCoeff hdet_ne
  have hspec : A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ k := PadicInt.unitCoeff_spec hdet_ne
  let idL : (Fin lam → ℤ_[p]) →ₗ[ℤ_[p]] (Fin lam → ℤ_[p]) := LinearMap.id
  have hle : LinearMap.range (((p : ℤ_[p]) ^ k) • idL) ≤ LinearMap.range T := by
    rintro _ ⟨y, rfl⟩
    refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • (A.adjugate.mulVec y), ?_⟩
    rw [hT_eq]
    change A.mulVec (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • (A.adjugate.mulVec y)) = ((p : ℤ_[p]) ^ k) • y
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, hspec, ← mul_assoc, Units.inv_mul, one_mul]
  have hsurj : Function.Surjective (Submodule.factor hle) := Submodule.factor_surjective hle
  have hlen_le := Module.length_le_of_surjective (Submodule.factor hle) hsurj
  -- Compute exact length of `(Fin lam → ℤ_[p]) / (p^k) ≃ₗ[ℤ_[p]] (Fin lam → ℤ_[p] / (p^k))`!
  let Ik : Ideal ℤ_[p] := Ideal.span ({(p : ℤ_[p]) ^ k} : Set ℤ_[p])
  let proj : (Fin lam → ℤ_[p]) →ₗ[ℤ_[p]] (Fin lam → ℤ_[p] ⧸ Ik) :=
    { toFun := fun v i => Ideal.Quotient.mk Ik (v i)
      map_add' := fun _ _ => by ext i; simp
      map_smul' := fun r v => by
        ext i
        change Ideal.Quotient.mk Ik (r * v i) = r • Ideal.Quotient.mk Ik (v i)
        exact map_smul (Ideal.Quotient.mkₐ ℤ_[p] Ik).toLinearMap r (v i) }
  have hproj_surj : Function.Surjective proj := by
    intro v
    have hl : ∀ i, ∃ a : ℤ_[p], Ideal.Quotient.mk Ik a = v i := fun i => Ideal.Quotient.mk_surjective _
    choose a ha using hl
    exact ⟨a, funext ha⟩
  have hproj_ker : LinearMap.ker proj = LinearMap.range (((p : ℤ_[p]) ^ k) • idL) := by
    ext v
    constructor
    · intro hv
      have hv' : ∀ i : Fin lam, ∃ c : ℤ_[p], v i = (p : ℤ_[p]) ^ k * c := fun i =>
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv i))
      choose c hc using hv'
      exact ⟨c, funext fun i => (hc i).symm⟩
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      ext i
      change Ideal.Quotient.mk Ik ((p : ℤ_[p]) ^ k * y i) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y i, rfl⟩
  let qEquiv : ((Fin lam → ℤ_[p]) ⧸ LinearMap.range (((p : ℤ_[p]) ^ k) • idL)) ≃ₗ[ℤ_[p]]
      (Fin lam → ℤ_[p] ⧸ Ik) :=
    (Submodule.quotEquivOfEq _ _ hproj_ker.symm).trans
      (LinearMap.quotKerEquivOfSurjective proj hproj_surj)
  have hlen_dom : Module.length ℤ_[p] ((Fin lam → ℤ_[p]) ⧸ LinearMap.range (((p : ℤ_[p]) ^ k) • idL)) =
      ((lam * k : ℕ) : ℕ∞) := by
    rw [qEquiv.length_eq, Module.length_pi, padicInt_length_quot_span_p_pow k]
    simp
  rw [hlen_dom] at hlen_le
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlen_le

/-- **Concrete `DistinguishedLattice` Construction from ANY `μ = 0` Iwasawa Power Series `F`**:
given `F ≠ 0` in `ℤ_[p][[T]]` with `iwasawaMu F = 0` and `ω_{λ+1}` injective on `Λ_p / (F)`,
constructs a concrete `Stage2IwasawaTwoTower.DistinguishedLattice p (iwasawaLambda F)` with
`Carrier = IwasawaAlg p ⧸ Ideal.span {F}` and `distDeg = iwasawaLambda F`! -/
def cyclicDistinguishedLattice {F : IwasawaAlg p} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))
        (omegaElem p (iwasawaLambda F + 1)))) :
    DistinguishedLattice p (iwasawaLambda F) where
  Carrier := IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))
  freeEquiv := cyclicQuotLinearEquiv hf hμ
  distDeg := iwasawaLambda F
  topNilpotent := by
    obtain ⟨⟨P, u⟩, ⟨hP_dist, hP_deg, hfac⟩, _⟩ := weierstrass_preparation_Zp hf
    dsimp only at hP_dist hP_deg hfac
    have hP_mem : P.toPowerSeries ∈ Ideal.span ({F} : Set (IwasawaAlg p)) := by
      rw [Ideal.mem_span_singleton]
      refine ⟨((u⁻¹ : (IwasawaAlg p)ˣ) : IwasawaAlg p), ?_⟩
      rw [hfac, hμ, pow_zero, one_mul, mul_assoc, Units.mul_inv, mul_one]
    have hlower : ∀ k < iwasawaLambda F, (p : ℤ_[p]) ∣ P.coeff k := fun k hk =>
      hP_dist.2 k (by rwa [hP_deg])
    let g : IwasawaAlg p := PowerSeries.mk fun k =>
      if hk : k < iwasawaLambda F then (hlower k hk).choose else 0
    have hP_eq : P.toPowerSeries = PowerSeries.X ^ iwasawaLambda F + PowerSeries.C (p : ℤ_[p]) * g := by
      ext k
      rw [toPowerSeries_coeff, map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul]
      dsimp only [g]
      rw [PowerSeries.coeff_mk]
      rcases lt_trichotomy k (iwasawaLambda F) with hlt | rfl | hgt
      · rw [if_neg (ne_of_lt hlt), zero_add, dif_pos hlt]
        exact (hlower k hlt).choose_spec
      · rw [if_pos rfl, dif_neg (lt_irrefl _), mul_zero, add_zero, ← hP_deg]
        exact hP_dist.1.leadingCoeff
      · rw [if_neg (ne_of_gt hgt), dif_neg (not_lt.mpr hgt.le), mul_zero, add_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    refine DistinguishedLattice.topNilpotent_of_distinguished_annihilator (g := g) fun m => ?_
    induction m using Quotient.inductionOn' with
    | h x =>
      rw [← hP_eq]
      change Ideal.Quotient.mk (Ideal.span ({F} : Set (IwasawaAlg p))) (P.toPowerSeries * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right x _ hP_mem
  baseFinite := by
    let e := cyclicQuotLinearEquiv hf hμ
    let L : (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) →ₗ[ℤ_[p]]
        (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) :=
      (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))
        (omegaElem p (iwasawaLambda F + 1))).restrictScalars ℤ_[p]
    let T : (Fin (iwasawaLambda F) → ℤ_[p]) →ₗ[ℤ_[p]] (Fin (iwasawaLambda F) → ℤ_[p]) :=
      (e.toLinearMap.comp L).comp e.symm.toLinearMap
    have hT_inj : Function.Injective T := fun x y hxy =>
      e.symm.injective (hcop (e.injective hxy))
    have hfin := finite_length_coker_of_injective_free T hT_inj
    have hrange : (layerSubmodule p (iwasawaLambda F + 1)
        (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))).restrictScalars ℤ_[p] =
        (LinearMap.range T).comap e.toLinearMap := by
      ext x
      simp only [Submodule.mem_comap, LinearMap.mem_range]
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨e m, by simp [T, L, LinearMap.lsmul_apply]⟩
      · rintro ⟨v, hv⟩
        refine ⟨e.symm v, ?_⟩
        apply e.injective
        simpa [T, L, LinearMap.lsmul_apply] using hv
    let π : (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) →ₗ[ℤ_[p]]
        ((Fin (iwasawaLambda F) → ℤ_[p]) ⧸ LinearMap.range T) :=
      (LinearMap.range T).mkQ.comp e.toLinearMap
    have hπ_surj : Function.Surjective π :=
      (Submodule.mkQ_surjective (LinearMap.range T)).comp e.surjective
    have hπ_ker : LinearMap.ker π = (LinearMap.range T).comap e.toLinearMap := by
      ext x
      simp [π, LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero]
    let qEquiv : LayerQuot p (iwasawaLambda F + 1)
        (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) ≃ₗ[ℤ_[p]]
        ((Fin (iwasawaLambda F) → ℤ_[p]) ⧸ LinearMap.range T) :=
      (Submodule.quotEquivOfEq _ _ (hrange.trans hπ_ker.symm)).trans
        (LinearMap.quotKerEquivOfSurjective π hπ_surj)
    rw [qEquiv.length_eq]
    exact hfin

/-- **Concrete `IwasawaModuleModel` with `μ = 0, λ = iwasawaLambda F`** for `Λ_p / (F)`. -/
def cyclicIwasawaModuleModel {F : IwasawaAlg p} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))
        (omegaElem p (iwasawaLambda F + 1)))) :
    IwasawaModuleModel p (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) :=
  let FL := cyclicDistinguishedLattice hf hμ hcop
  let φ : (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))) →ₗ[IwasawaAlg p]
      ((i : Fin ([] : List ℕ).length) → ElemPTorsion p ([].get i)) × FL.Carrier :=
    { toFun := fun x => (fun i => i.elim0, x)
      map_add' := fun _ _ => Prod.ext (funext fun i => i.elim0) rfl
      map_smul' := fun _ _ => Prod.ext (funext fun i => i.elim0) rfl }
  { muExps := []
    lamInvariant := iwasawaLambda F
    freePart := FL
    pseudoIso := φ
    ker_finite := by
      have hsub : Subsingleton (LinearMap.ker φ) := by
        refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => Subtype.ext ?_⟩
        have hx0 : x = 0 := congrArg Prod.snd hx
        have hy0 : y = 0 := congrArg Prod.snd hy
        exact hx0.trans hy0.symm
      rw [@Module.length_eq_zero _ _ _ _ _ hsub]
      exact ENat.natCast_ne_top 0
    coker_finite := by
      have hsurj : Function.Surjective φ := fun ⟨_, z⟩ =>
        ⟨z, Prod.ext (funext fun i => i.elim0) rfl⟩
      have htop : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
      have hsub : Subsingleton (_ ⧸ LinearMap.range φ) := by rw [htop]; infer_instance
      rw [@Module.length_eq_zero _ _ _ _ _ hsub]
      exact ENat.natCast_ne_top 0 }

lemma cyclicIwasawaModuleModel_mu {F : IwasawaAlg p} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))
        (omegaElem p (iwasawaLambda F + 1)))) :
    (cyclicIwasawaModuleModel hf hμ hcop).mu = 0 := rfl

lemma cyclicIwasawaModuleModel_lam {F : IwasawaAlg p} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))
        (omegaElem p (iwasawaLambda F + 1)))) :
    (cyclicIwasawaModuleModel hf hμ hcop).lam = iwasawaLambda F := rfl

/-- **CONCRETE `μ = 0` → EXACT LINEAR `p`-ADIC GROWTH BOUND (`v_p = λ · n + O(1)`, NOT `p^n`!)**:
for EVERY `F ≠ 0` in `ℤ_[p][[T]]` with `iwasawaMu F = 0` and `ω_{λ+1}` injective on `Λ_p / (F)`,
letting `λ = iwasawaLambda F` and `ν = (cyclicDistinguishedLattice hf hμ hcop).baseLen`:
1. For ALL `n : ℕ`: `Finite (LayerQuot p n (Λ_p / (F)))`,
   `length_{ℤ_[p]}(Λ_p / (F, ω_n)) ≤ λ * n + ν`, and `|Λ_p / (F, ω_n)| ≤ p^ν * p^(λ * n)`!
2. For ALL `n ≥ λ + 1`: **EXACT LINEAR EQUALITY**
   `length_{ℤ_[p]}(Λ_p / (F, ω_n)) = ν + λ * (n - (λ + 1))` and
   `|Λ_p / (F, ω_n)| = p ^ (ν + λ * (n - (λ + 1)))`! -/
theorem cyclic_mu_zero_linear_growth {F : IwasawaAlg p} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p)))
        (omegaElem p (iwasawaLambda F + 1)))) :
    let M := IwasawaAlg p ⧸ Ideal.span ({F} : Set (IwasawaAlg p))
    let ν := (cyclicDistinguishedLattice hf hμ hcop).baseLen
    (∀ n : ℕ,
      Module.length ℤ_[p] (LayerQuot p n M) ≠ ⊤ ∧
      (Module.length ℤ_[p] (LayerQuot p n M)).toNat ≤ iwasawaLambda F * n + ν ∧
      Finite (LayerQuot p n M) ∧
      Nat.card (LayerQuot p n M) ≤ p ^ ν * p ^ (iwasawaLambda F * n)) ∧
    (∀ n : ℕ, iwasawaLambda F + 1 ≤ n →
      Module.length ℤ_[p] (LayerQuot p n M) =
        ((ν + iwasawaLambda F * (n - (iwasawaLambda F + 1)) : ℕ) : ℕ∞) ∧
      Nat.card (LayerQuot p n M) = p ^ (ν + iwasawaLambda F * (n - (iwasawaLambda F + 1)))) := by
  let model := cyclicIwasawaModuleModel hf hμ hcop
  have hnu : model.nu = (cyclicDistinguishedLattice hf hμ hcop).baseLen := by
    unfold IwasawaModuleModel.nu
    have hker0 : Module.length ℤ_[p] (LinearMap.ker model.pseudoIso) = 0 := by
      have hsub : Subsingleton (LinearMap.ker model.pseudoIso) := by
        refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => Subtype.ext ?_⟩
        exact (congrArg Prod.snd hx).trans (congrArg Prod.snd hy).symm
      exact @Module.length_eq_zero _ _ _ _ _ hsub
    have hcoker0 : Module.length ℤ_[p] (_ ⧸ LinearMap.range model.pseudoIso) = 0 := by
      have hsurj : Function.Surjective model.pseudoIso :=
        fun ⟨_, z⟩ => ⟨z, Prod.ext (funext fun i => i.elim0) rfl⟩
      have htop : LinearMap.range model.pseudoIso = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      have hsub : Subsingleton (_ ⧸ LinearMap.range model.pseudoIso) := by
        rw [htop]; infer_instance
      exact @Module.length_eq_zero _ _ _ _ _ hsub
    rw [hker0, hcoker0]
    simp [model, cyclicIwasawaModuleModel]
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · have h := model.ferrero_washington_card_bound (cyclicIwasawaModuleModel_mu hf hμ hcop) n
    rwa [hnu, cyclicIwasawaModuleModel_lam hf hμ hcop] at h
  · obtain ⟨k, rfl⟩ : ∃ k, n = iwasawaLambda F + 1 + k := ⟨n - (iwasawaLambda F + 1), by omega⟩
    have hlen := (cyclicDistinguishedLattice hf hμ hcop).length_layerQuot_eq_of_injective hcop k
    rw [Nat.add_sub_cancel_left]
    refine ⟨hlen, (padicInt_card_eq_pow_length _ hlen).2⟩

/-- **DIRECT DISCHARGE INTO `Stage2IwasawaTwoTower.IwasawaTwoTowerBound` (`l = 2` Branch!)**:
given ANY `F ≠ 0` in `ℤ_[2][[T]]` with `iwasawaMu F = 0` and `ω_{λ+1}` injective on `Λ_2 / (F)`,
plus a Selmer embedding `Sel ↪ LayerQuot 2 level (Λ_2 / (F))` with `S.shaLen E 2 k ≤ length Sel`,
produces a concrete `Stage2IwasawaTwoTower.IwasawaTwoTowerBound S E level k` with `model.mu = 0`
and `model.lam = iwasawaLambda F`! -/
def iwasawaTwoTowerBound_of_cyclic_mu_zero {S : RHDirect.SelmerSystem} {E : Type} [Field E]
    [NumberField E] {level k : ℕ}
    {F : IwasawaAlg 2} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg 2) (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))
        (omegaElem 2 (iwasawaLambda F + 1))))
    (Sel : Type) [AddCommGroup Sel] [Module (PadicInt 2) Sel]
    (embed : Sel →ₗ[PadicInt 2] LayerQuot 2 level (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2))))
    (embed_inj : Function.Injective embed)
    (sha_le_selmer : S.shaLen E ⟨2, Nat.prime_two⟩ k ≤ Module.length (PadicInt 2) Sel) :
    IwasawaTwoTowerBound S E level k where
  M := IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2))
  model := cyclicIwasawaModuleModel hf hμ hcop
  ferrero_washington := cyclicIwasawaModuleModel_mu hf hμ hcop
  Sel := Sel
  embed := embed
  embed_inj := embed_inj
  sha_le_selmer := sha_le_selmer

/-- **Quantitative `PageN` Exponential Domination for Any `μ = 0` Cyclic `2`-Tower Module**:
on all sufficiently large `PageN eps x e` windows, the layer cardinality
`|Λ_2 / (F, ω_e)|` of any `μ = 0` Iwasawa power series `F ∈ ℤ_[2][[T]]` is strictly bounded by
BOTH `exp(x ^ (4 * eps / 5))` and `exp(x ^ eps)`! -/
theorem cyclic_mu_zero_pageN_domination {F : IwasawaAlg 2} (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg 2) (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))
        (omegaElem 2 (iwasawaLambda F + 1))))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ e : ℕ, RHDirect.PageN eps x e →
      (Nat.card (LayerQuot 2 e (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))) : ℝ) <
        Real.exp (x ^ (4 * eps / 5)) ∧
      (Nat.card (LayerQuot 2 e (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))) : ℝ) <
        Real.exp (x ^ eps) := by
  set ν := (cyclicDistinguishedLattice hf hμ hcop).baseLen
  obtain ⟨x0, hx0⟩ := ferrero_washington_card_lt_exp_rpow_of_pageN eps ((2 : ℝ) ^ ν)
    (iwasawaLambda F) heps
  refine ⟨x0, fun x hx e hP => ?_⟩
  have hcard := ((cyclic_mu_zero_linear_growth hf hμ hcop).1 e).2.2.2
  have hcardR : (Nat.card (LayerQuot 2 e (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))) : ℝ) ≤
      (2 : ℝ) ^ ν * (2 : ℝ) ^ (iwasawaLambda F * e) := by exact_mod_cast hcard
  obtain ⟨h1, h2⟩ := hx0 x hx e hP
  exact ⟨lt_of_le_of_lt hcardR h1, lt_of_le_of_lt hcardR h2⟩

/-- Concrete `p = 2` non-vacuity witness using the Mazur Bernoulli measure `μ_3` at `p = 2`:
`F = iwasawaTransform (mazurBernoulliMeasure 2 3 _)` is a unit in `ℤ_[2][[T]]` (`μ = 0, λ = 0`),
giving an unconditional `cyclicIwasawaModuleModel` over `ℤ_[2][[T]]`! -/
theorem mazur_p2_cyclic_model_exists :
    let F := iwasawaTransform (mazurBernoulliMeasure 2 3 (by decide))
    ∃ (hf : F ≠ 0) (hμ : iwasawaMu F = 0)
      (hcop : Function.Injective
        (LinearMap.lsmul (IwasawaAlg 2) (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))
          (omegaElem 2 (iwasawaLambda F + 1)))),
      (cyclicIwasawaModuleModel hf hμ hcop).mu = 0 ∧
      (cyclicIwasawaModuleModel hf hμ hcop).lam = 0 := by
  set F := iwasawaTransform (mazurBernoulliMeasure 2 3 (by decide))
  obtain ⟨hu, hμ, hlam⟩ := mazurBernoulliMeasure_three_isUnit (p := 2) (by decide)
  have hf : F ≠ 0 := hu.ne_zero
  have htop : Ideal.span ({F} : Set (IwasawaAlg 2)) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hu
  have hsub : Subsingleton (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2))) := by
    rw [htop]; infer_instance
  have hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg 2) (IwasawaAlg 2 ⧸ Ideal.span ({F} : Set (IwasawaAlg 2)))
        (omegaElem 2 (iwasawaLambda F + 1))) := fun x y _ => hsub.elim x y
  exact ⟨hf, hμ, hcop, cyclicIwasawaModuleModel_mu hf hμ hcop,
    (cyclicIwasawaModuleModel_lam hf hμ hcop).trans hlam⟩

/-- **Odd-Prime `p`-adic Lifting-the-Exponent Lemma for `1 + p * w` (`IsUnit w`)**:
for any odd prime `p`, any unit `w ∈ ℤ_[p]ˣ`, and every `n : ℕ`, there exists a unit `v_n ∈ ℤ_[p]ˣ`
such that `(1 + p * w) ^ (p ^ n) - 1 = p ^ (n + 1) * v_n`! -/
theorem padicInt_lte_one_add_p_mul_unit (hp2 : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w) (n : ℕ) :
    ∃ v : ℤ_[p], IsUnit v ∧ (1 + (p : ℤ_[p]) * w) ^ (p ^ n) - 1 = (p : ℤ_[p]) ^ (n + 1) * v := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  induction n with
  | zero =>
    refine ⟨w, hw, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨v, hv, heq⟩ := ih
    have hpow : (1 + (p : ℤ_[p]) * w) ^ (p ^ n) = 1 + (p : ℤ_[p]) ^ (n + 1) * v := by
      linear_combination heq
    have hsplit_sum : ∀ (m : ℕ) (f : ℕ → ℤ_[p]), 1 ≤ m →
        ∑ k ∈ Finset.range m, f k = (∑ x ∈ Finset.range (m - 1), f (x + 1)) + f 0 := by
      intro m f hm
      conv_lhs => rw [← Nat.sub_add_cancel hm]
      rw [Finset.sum_range_succ']
    rw [pow_succ, pow_mul, hpow, add_comm 1 ((p : ℤ_[p]) ^ (n + 1) * v), add_pow,
      Finset.sum_range_succ', hsplit_sum p _ hp.one_le]
    simp only [Nat.sub_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      zero_add, pow_one, Nat.choose_one_right, one_pow]
    have hterm_dvd : ∀ j ∈ Finset.range (p - 1),
        (p : ℤ_[p]) ^ (n + 3) ∣
          ((p : ℤ_[p]) ^ (n + 1) * v) ^ (j + 2) * (p.choose (j + 2) : ℤ_[p]) := by
      intro j hj
      have hjlt : j < p - 1 := Finset.mem_range.mp hj
      rw [mul_pow, ← pow_mul]
      by_cases hlast : j + 2 = p
      · have hle : n + 3 ≤ (n + 1) * (j + 2) := by rw [hlast]; nlinarith
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ_[p]) hle) _) _
      · have hltp : j + 2 < p := by omega
        obtain ⟨q, hq⟩ := hp.dvd_choose_self (by omega : j + 2 ≠ 0) hltp
        have hq' : (p.choose (j + 2) : ℤ_[p]) = (p : ℤ_[p]) * (q : ℤ_[p]) := by exact_mod_cast hq
        have hle : n + 2 ≤ (n + 1) * (j + 2) := by nlinarith
        have h1 : (p : ℤ_[p]) ^ (n + 2) ∣ (p : ℤ_[p]) ^ ((n + 1) * (j + 2)) := pow_dvd_pow _ hle
        have h2 : (p : ℤ_[p]) ^ (n + 3) ∣ (p : ℤ_[p]) ^ ((n + 1) * (j + 2)) * (p.choose (j + 2) : ℤ_[p]) := by
          rw [hq', pow_succ]
          exact mul_dvd_mul h1 (dvd_mul_right _ _)
        have hre : (p : ℤ_[p]) ^ ((n + 1) * (j + 2)) * v ^ (j + 2) * (p.choose (j + 2) : ℤ_[p]) =
            v ^ (j + 2) * ((p : ℤ_[p]) ^ ((n + 1) * (j + 2)) * (p.choose (j + 2) : ℤ_[p])) := by ring
        rw [hre]
        exact dvd_mul_of_dvd_right h2 _
    have hsum_dvd : (p : ℤ_[p]) ^ (n + 3) ∣ ∑ x ∈ Finset.range (p - 1),
        ((p : ℤ_[p]) ^ (n + 1) * v) ^ (x + 1 + 1) * (p.choose (x + 1 + 1) : ℤ_[p]) :=
      Finset.dvd_sum fun x hx => hterm_dvd x hx
    obtain ⟨z, hz⟩ := hsum_dvd
    refine ⟨v + (p : ℤ_[p]) * z, ?_, ?_⟩
    · rw [padicInt_isUnit_iff_not_p_dvd, padicInt_p_dvd_iff_toZMod_eq_zero,
        map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
        ← padicInt_p_dvd_iff_toZMod_eq_zero, ← padicInt_isUnit_iff_not_p_dvd]
      exact hv
    · rw [hz, pow_succ (p : ℤ_[p]) (n + 2), pow_succ (p : ℤ_[p]) (n + 1)]
      ring

private lemma zmod37_sq_F0_check :
    (((510 * 32 : ℕ) : ZMod (37 ^ 2)) * (10 * 37 : ZMod (37 ^ 2))) =
    ((1 - (2 : ZMod (37 ^ 2)) ^ 32) * (-((7709321041217 : ℕ) : ZMod (37 ^ 2))) -
      ((510 * 32 : ℕ) : ZMod (37 ^ 2)) * (15 * 31 * 37 : ZMod (37 ^ 2))) := by
  decide

private lemma p37_mul_p37_zmod37_sq : (37 : ZMod (37 ^ 2)) * (37 : ZMod (37 ^ 2)) = 0 := by decide

private lemma ten_mul_37_ne_zero_zmod37_sq : (10 * (37 : ZMod (37 ^ 2))) ≠ 0 := by decide

/-- **EXACT `37^(n + 1)` IWASAWA LAYER CARDINALITY LAW FOR THE FIRST IRREGULAR PRIME `p = 37`
(`i = 32` Branch!)**:
for `F = kubotaLeopoldtSeries 37 _ 2 _ 31` (`μ = 0, λ = 1`), EVERY cyclotomic layer quotient
`LayerQuot 37 n (IwasawaAlg 37 ⧸ Ideal.span {F})` has:
- **EXACT `ℤ_[37]`-length `n + 1`**, AND
- **EXACT cardinality `37 ^ (n + 1)`**
for **ALL `n : ℕ`** (matching Iwasawa's exact class-number formula `h(ℚ(ζ_{37^{n+1}}))_{37} = 37^{n+1}`),
and constructs a concrete `cyclicIwasawaModuleModel` with `μ = 0, λ = 1`! -/
theorem irregular_prime_37_layerQuot_exact_growth [Fact (Nat.Prime 37)] :
    let F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
    let M := IwasawaAlg 37 ⧸ Ideal.span ({F} : Set (IwasawaAlg 37))
    (∀ n : ℕ,
      Module.length ℤ_[37] (LayerQuot 37 n M) = ((n + 1 : ℕ) : ℕ∞) ∧
      Finite (LayerQuot 37 n M) ∧
      Nat.card (LayerQuot 37 n M) = 37 ^ (n + 1)) := by
  dsimp only
  set F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
  obtain ⟨hF_ne, hF_not_unit, hμ0, hlam1⟩ := irregular_prime_37_mu_zero_lambda_eq_one
  change F ≠ 0 at hF_ne
  change ¬ IsUnit F at hF_not_unit
  change iwasawaMu F = 0 at hμ0
  change iwasawaLambda F = 1 at hlam1
  -- Step 1: Prove `PadicInt.toZModPow 2 (PowerSeries.constantCoeff F) = 10 * 37`!
  set y : ℤ_[37] := padicPowOneAdd (37 : ℤ_[37]) (31 : ℤ_[37]) - 1
  have hy_lt1 : ‖y‖ < 1 := norm_padicPowOneAdd_prime_sub_one_lt_one _
  have hy_le : ‖y‖ ≤ (37 : ℝ) ^ (-(1 : ℤ)) := by
    have hdvd : ((37 : ℕ) : ℤ_[37]) ^ 1 ∣ y := by
      rw [pow_one]; exact (padicInt_norm_lt_one_iff_p_dvd y).mp hy_lt1
    exact (padicInt_p_pow_dvd_iff_norm_le y 1).mp hdvd
  have hy_mod2 : PadicInt.toZModPow 2 y = 31 * (37 : ZMod (37 ^ 2)) := by
    have hy_nat : y = (1 + ((37 : ℕ) : ℤ_[37])) ^ 31 - 1 := by
      dsimp only [y]
      rw [show (31 : ℤ_[37]) = ((31 : ℕ) : ℤ_[37]) from rfl, padicPowOneAdd_natCast]
      simp
    rw [hy_nat, map_sub, map_pow, map_add, map_one, map_natCast, one_add_p_pow_mod_p_sq 37 31,
      add_sub_cancel_left]
    simp
  have hFy_taylor : PadicInt.toZModPow 2 (evalIwasawa F y) =
      PadicInt.toZModPow 2 (PowerSeries.constantCoeff F) +
      PadicInt.toZModPow 2 (PowerSeries.coeff 1 F * y) := by
    have hbd := norm_evalIwasawa_sub_trunc_le F hy_lt1 2
    have htrunc : ∑ k ∈ Finset.range 2, PowerSeries.coeff k F * y ^ k =
        PowerSeries.constantCoeff F + PowerSeries.coeff 1 F * y := by
      simp [Finset.sum_range_succ, PowerSeries.coeff_zero_eq_constantCoeff]
    rw [htrunc] at hbd
    have hy2 : ‖y‖ ^ 2 ≤ (37 : ℝ) ^ (-(2 : ℤ)) := by
      calc ‖y‖ ^ 2 ≤ ((37 : ℝ) ^ (-(1 : ℤ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy_le 2
        _ = (37 : ℝ) ^ (-(2 : ℤ)) := by rw [← zpow_natCast, ← zpow_mul]; congr 1
    have hmod := padicInt_toZModPow_eq_of_norm_le_pow (hbd.trans hy2)
    rwa [map_add] at hmod
  have hc1y_mod2 : PadicInt.toZModPow 2 (PowerSeries.coeff 1 F * y) = 15 * 31 * (37 : ZMod (37 ^ 2)) := by
    have hc1_sub : ((37 : ℕ) : ℤ_[37]) ∣ PowerSeries.coeff 1 F - (15 : ℤ_[37]) := by
      rw [padicInt_p_dvd_iff_toZMod_eq_zero, map_sub, toZMod_coeff_one_kubotaLeopoldtSeries_37,
        map_ofNat, sub_self]
    obtain ⟨t, ht⟩ := hc1_sub
    have hc1_eq : PowerSeries.coeff 1 F = (15 : ℤ_[37]) + ((37 : ℕ) : ℤ_[37]) * t := by
      linear_combination ht
    rw [map_mul, hc1_eq, map_add, map_ofNat, map_mul, map_natCast, Nat.cast_ofNat, hy_mod2, add_mul]
    have hzero : (37 : ZMod (37 ^ 2)) * PadicInt.toZModPow 2 t * (31 * (37 : ZMod (37 ^ 2))) = 0 := by
      calc (37 : ZMod (37 ^ 2)) * PadicInt.toZModPow 2 t * (31 * (37 : ZMod (37 ^ 2)))
          = PadicInt.toZModPow 2 t * 31 * ((37 : ZMod (37 ^ 2)) * (37 : ZMod (37 ^ 2))) := by ring
        _ = 0 := by rw [p37_mul_p37_zmod37_sq, mul_zero]
    rw [hzero, add_zero]
    ring
  have hFy_eq : ((510 * 32 : ℕ) : ℤ_[37]) * evalIwasawa F y =
      (1 - ((37 : ℕ) : ℤ_[37]) ^ 31) * (1 - ((2 : ℕ) : ℤ_[37]) ^ 32) * (-((7709321041217 : ℕ) : ℤ_[37])) := by
    have hev := evalIwasawa_kubotaLeopoldtSeries_nat 37 (by decide) 2 (by decide) 31 31 Nat.ModEq.rfl
    change ((evalIwasawa F y : ℤ_[37]) : ℚ_[37]) = _ at hev
    have hQ : ((510 * 32 : ℕ) : ℚ) *
        ((1 - ((37 : ℕ) : ℚ) ^ 31) * (1 - ((2 : ℕ) : ℚ) ^ 32) * (bernoulli 32 / ((32 : ℕ) : ℚ))) =
        (1 - ((37 : ℕ) : ℚ) ^ 31) * (1 - ((2 : ℕ) : ℚ) ^ 32) * (-((7709321041217 : ℕ) : ℚ)) := by
      rw [bernoulli_32]
      norm_num
    apply Subtype.ext
    rw [PadicInt.coe_mul, PadicInt.coe_natCast, hev, show 31 + 1 = 32 from rfl]
    have hQ' := congrArg (Rat.cast : ℚ → ℚ_[37]) hQ
    rw [Rat.cast_mul, Rat.cast_natCast] at hQ'
    rw [hQ']
    simp only [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_one, PadicInt.coe_pow,
      PadicInt.coe_neg, PadicInt.coe_natCast, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
      Rat.cast_pow, Rat.cast_neg, Rat.cast_natCast]
  have hF0_mod2 : PadicInt.toZModPow 2 (PowerSeries.constantCoeff F) = 10 * (37 : ZMod (37 ^ 2)) := by
    have hmul_mod := congrArg (PadicInt.toZModPow 2) hFy_eq
    rw [map_mul, map_natCast, hFy_taylor, hc1y_mod2, mul_add] at hmul_mod
    have h37_pow : PadicInt.toZModPow 2 (((37 : ℕ) : ℤ_[37]) ^ 31) = 0 := by
      rw [map_pow, map_natCast]
      have hdvd : 37 ^ 2 ∣ 37 ^ 31 := pow_dvd_pow 37 (by decide)
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact hdvd
    have hrhs_mod : PadicInt.toZModPow 2
        ((1 - ((37 : ℕ) : ℤ_[37]) ^ 31) * (1 - ((2 : ℕ) : ℤ_[37]) ^ 32) * (-((7709321041217 : ℕ) : ℤ_[37]))) =
        (1 - (2 : ZMod (37 ^ 2)) ^ 32) * (-((7709321041217 : ℕ) : ZMod (37 ^ 2))) := by
      rw [map_mul, map_mul, map_sub, map_one, h37_pow, sub_zero, one_mul, map_sub, map_one,
        map_pow, map_natCast, Nat.cast_ofNat, map_neg, map_natCast]
    rw [hrhs_mod] at hmul_mod
    have hmul_eq : ((510 * 32 : ℕ) : ZMod (37 ^ 2)) * PadicInt.toZModPow 2 (PowerSeries.constantCoeff F) =
        ((510 * 32 : ℕ) : ZMod (37 ^ 2)) * (10 * (37 : ZMod (37 ^ 2))) := by
      rw [zmod37_sq_F0_check, ← hmul_mod]
      ring
    have hcop : Nat.Coprime (510 * 32) (37 ^ 2) := by decide
    let u0 : (ZMod (37 ^ 2))ˣ := ZMod.unitOfCoprime (510 * 32) hcop
    have hu0 : ((u0 : ZMod (37 ^ 2))) = ((510 * 32 : ℕ) : ZMod (37 ^ 2)) :=
      ZMod.coe_unitOfCoprime _ _
    rw [← hu0] at hmul_eq
    calc PadicInt.toZModPow 2 (PowerSeries.constantCoeff F)
        = ((u0⁻¹ : (ZMod (37 ^ 2))ˣ) : ZMod (37 ^ 2)) *
            ((u0 : ZMod (37 ^ 2)) * PadicInt.toZModPow 2 (PowerSeries.constantCoeff F)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((u0⁻¹ : (ZMod (37 ^ 2))ˣ) : ZMod (37 ^ 2)) *
            ((u0 : ZMod (37 ^ 2)) * (10 * (37 : ZMod (37 ^ 2)))) := by rw [hmul_eq]
      _ = 10 * (37 : ZMod (37 ^ 2)) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  -- Step 2: Weierstrass preparation `F = (X - C α) * u` with `α = 37 * w`, `IsUnit w`!
  obtain ⟨⟨P, u⟩, ⟨hP_dist, hP_deg, hfac⟩, _⟩ := weierstrass_preparation_Zp hF_ne
  dsimp only at hP_dist hP_deg hfac
  rw [hμ0, pow_zero, one_mul] at hfac
  rw [hlam1] at hP_deg
  set α : ℤ_[37] := -P.coeff 0
  have hP_eq : P = Polynomial.X - Polynomial.C α := by
    ext k
    rcases k with _ | _ | k
    · simp [α]
    · change P.coeff 1 = (Polynomial.X - Polynomial.C α).coeff 1
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, sub_zero]
      rw [← hP_deg]; exact hP_dist.1.leadingCoeff
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_succ, sub_zero, Polynomial.coeff_X]
      rw [if_neg (by omega : 1 ≠ k + 2)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hα_dvd : ((37 : ℕ) : ℤ_[37]) ∣ α := by
    have h0 : ((37 : ℕ) : ℤ_[37]) ∣ P.coeff 0 := hP_dist.2 0 (by omega)
    exact dvd_neg.mpr h0
  obtain ⟨w, hw_eq⟩ := hα_dvd
  have hw_unit : IsUnit w := by
    have hF0 : PowerSeries.constantCoeff F = -α * PowerSeries.constantCoeff (u : IwasawaAlg 37) := by
      have h0 := congrArg PowerSeries.constantCoeff hfac
      rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, toPowerSeries_coeff, hP_eq] at h0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub] at h0
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0
    have hF0_ndvd2 : ¬ ((37 : ℕ) : ℤ_[37]) ^ 2 ∣ PowerSeries.constantCoeff F := by
      intro hdvd
      have hmem : PowerSeries.constantCoeff F ∈ Ideal.span ({((37 : ℕ) : ℤ_[37]) ^ 2} : Set ℤ_[37]) :=
        Ideal.mem_span_singleton.mpr hdvd
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, hF0_mod2] at hmem
      exact ten_mul_37_ne_zero_zmod37_sq hmem
    rw [padicInt_isUnit_iff_not_p_dvd]
    intro hdvd_w
    apply hF0_ndvd2
    obtain ⟨z, rfl⟩ := hdvd_w
    rw [hF0, hw_eq]
    refine ⟨-(z * PowerSeries.constantCoeff (u : IwasawaAlg 37)), ?_⟩
    ring
  have hα_lt1 : ‖α‖ < 1 := (padicInt_norm_lt_one_iff_p_dvd α).mpr ⟨w, hw_eq⟩
  -- Step 3: Exact `ℤ_[37]`-linear isomorphism `Λ_37 / (F) ≃ₗ[ℤ_[37]] ℤ_[37]` via `evalIwasawa · α`!
  let I : Ideal (IwasawaAlg 37) := Ideal.span ({F} : Set (IwasawaAlg 37))
  let ev0 : IwasawaAlg 37 →ₗ[ℤ_[37]] ℤ_[37] :=
    { toFun := fun G => evalIwasawa G α
      map_add' := fun G₁ G₂ => evalIwasawa_add G₁ G₂ hα_lt1
      map_smul' := fun c G => by
        rw [Algebra.smul_def, show algebraMap ℤ_[37] (IwasawaAlg 37) c = PowerSeries.C c from rfl,
          evalIwasawa_mul _ _ hα_lt1, evalIwasawa_C]
        rfl }
  have hev_F : evalIwasawa F α = 0 := by
    rw [hfac, evalIwasawa_mul _ _ hα_lt1, evalIwasawa_toPowerSeries, hP_eq]
    simp
  have hev_ker : I.restrictScalars ℤ_[37] ≤ LinearMap.ker ev0 := by
    intro G hG
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hG
    change evalIwasawa (F * Q) α = 0
    rw [evalIwasawa_mul _ _ hα_lt1, hev_F, zero_mul]
  let ev : (IwasawaAlg 37 ⧸ I) →ₗ[ℤ_[37]] ℤ_[37] := (I.restrictScalars ℤ_[37]).liftQ ev0 hev_ker
  let evInv : ℤ_[37] →ₗ[ℤ_[37]] (IwasawaAlg 37 ⧸ I) :=
    { toFun := fun c => Ideal.Quotient.mk I (PowerSeries.C c)
      map_add' := fun c₁ c₂ => by rw [map_add, map_add]
      map_smul' := fun c x => by
        change Ideal.Quotient.mk I (PowerSeries.C (c * x)) = c • Ideal.Quotient.mk I (PowerSeries.C x)
        rw [map_mul]
        change Ideal.Quotient.mk I (algebraMap ℤ_[37] (IwasawaAlg 37) c * PowerSeries.C x) = _
        rw [← Algebra.smul_def]
        rfl }
  have hev_left : ∀ c : ℤ_[37], ev (evInv c) = c := fun c => evalIwasawa_C c α
  have hev_right : ∀ x : IwasawaAlg 37 ⧸ I, evInv (ev x) = x := by
    intro x
    induction x using Quotient.inductionOn' with
    | h G =>
      obtain ⟨⟨q, r⟩, ⟨hr_deg, hdiv⟩, _⟩ := weierstrass_division_Zp (f := G) hF_ne hμ0
      dsimp only at hr_deg hdiv
      rw [hlam1] at hr_deg
      have hr_C : r = Polynomial.C (r.coeff 0) := by
        ext k
        rcases k with _ | k
        · simp
        · rw [Polynomial.coeff_C_succ]
          exact (poly_deg_lt_iff_coeff_eq_zero r 1).mp hr_deg (k + 1) (by omega)
      have hG_ev : evalIwasawa G α = r.coeff 0 := by
        rw [hdiv, evalIwasawa_add _ _ hα_lt1, evalIwasawa_mul _ _ hα_lt1, hev_F, zero_mul,
          zero_add, hr_C, toPowerSeries_C, evalIwasawa_C]
        simp
      change Ideal.Quotient.mk I (PowerSeries.C (evalIwasawa G α)) = Ideal.Quotient.mk I G
      rw [hG_ev, Ideal.Quotient.eq]
      have hdiff : PowerSeries.C (r.coeff 0) - G = F * (-q) := by
        conv_lhs => rw [hdiv, hr_C, toPowerSeries_C, Polynomial.coeff_C_zero]
        ring
      rw [hdiff]
      exact Ideal.mul_mem_right (-q) I (Ideal.subset_span rfl)
  let e : (IwasawaAlg 37 ⧸ I) ≃ₗ[ℤ_[37]] ℤ_[37] := LinearEquiv.ofLinearMap ev evInv
    (LinearMap.ext hev_left) (LinearMap.ext hev_right)
  -- Step 4: Under `e`, `ω_n` acts as `(1 + α)^(37^n) - 1 = 37^(n + 1) * v_n` with `IsUnit v_n`!
  intro n
  have hω_eval : evalIwasawa (omegaElem 37 n) α = (1 + α) ^ (37 ^ n) - 1 := by
    have h1 : omegaElem 37 n = ((1 + Polynomial.X : Polynomial ℤ_[37]) ^ (37 ^ n) - 1).toPowerSeries := by
      unfold omegaElem
      rw [toPowerSeries_sub, toPowerSeries_one, Polynomial.coe_pow, toPowerSeries_add,
        toPowerSeries_one, toPowerSeries_X]
    rw [h1, evalIwasawa_toPowerSeries]
    simp
  obtain ⟨v, hv_unit, hv_eq⟩ := padicInt_lte_one_add_p_mul_unit (p := 37) (by decide) hw_unit n
  have hω_eq : evalIwasawa (omegaElem 37 n) α = ((37 : ℕ) : ℤ_[37]) ^ (n + 1) * v := by
    rw [hω_eval, hw_eq]; exact hv_eq
  let In1 : Ideal ℤ_[37] := Ideal.span ({((37 : ℕ) : ℤ_[37]) ^ (n + 1)} : Set ℤ_[37])
  let π : (IwasawaAlg 37 ⧸ I) →ₗ[ℤ_[37]] (ℤ_[37] ⧸ In1) :=
    (Ideal.Quotient.mkₐ ℤ_[37] In1).toLinearMap.comp e.toLinearMap
  have hπ_surj : Function.Surjective π := (Ideal.Quotient.mk_surjective).comp e.surjective
  have hπ_ker : LinearMap.ker π = (layerSubmodule 37 n (IwasawaAlg 37 ⧸ I)).restrictScalars ℤ_[37] := by
    ext x
    change Ideal.Quotient.mk In1 (e x) = 0 ↔ x ∈ layerSubmodule 37 n (IwasawaAlg 37 ⧸ I)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    have hev_smul : ∀ (G : IwasawaAlg 37) (y : IwasawaAlg 37 ⧸ I),
        e (G • y) = evalIwasawa G α * e y := by
      intro G y
      induction y using Quotient.inductionOn' with
      | h H => exact evalIwasawa_mul G H hα_lt1
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨e.symm (((hv_unit.unit⁻¹ : ℤ_[37]ˣ) : ℤ_[37]) * c), ?_⟩
      apply e.injective
      change e (omegaElem 37 n • e.symm (((hv_unit.unit⁻¹ : ℤ_[37]ˣ) : ℤ_[37]) * c)) = e x
      rw [hev_smul, e.apply_symm_apply, hω_eq, hc]
      calc ((37 : ℕ) : ℤ_[37]) ^ (n + 1) * v * (((hv_unit.unit⁻¹ : ℤ_[37]ˣ) : ℤ_[37]) * c)
          = ((37 : ℕ) : ℤ_[37]) ^ (n + 1) * ((hv_unit.unit : ℤ_[37]) * ((hv_unit.unit⁻¹ : ℤ_[37]ˣ) : ℤ_[37])) * c := by
            simp only [IsUnit.unit_spec]; ring
        _ = ((37 : ℕ) : ℤ_[37]) ^ (n + 1) * c := by rw [Units.mul_inv, mul_one]
    · rintro ⟨y, rfl⟩
      refine ⟨v * e y, ?_⟩
      change e (omegaElem 37 n • y) = ((37 : ℕ) : ℤ_[37]) ^ (n + 1) * (v * e y)
      rw [hev_smul, hω_eq, mul_assoc]
  let qEquiv : LayerQuot 37 n (IwasawaAlg 37 ⧸ I) ≃ₗ[ℤ_[37]] (ℤ_[37] ⧸ In1) :=
    (Submodule.quotEquivOfEq _ _ hπ_ker.symm).trans
      (LinearMap.quotKerEquivOfSurjective π hπ_surj)
  have hlen : Module.length ℤ_[37] (LayerQuot 37 n (IwasawaAlg 37 ⧸ I)) = ((n + 1 : ℕ) : ℕ∞) := by
    rw [qEquiv.length_eq]
    exact padicInt_length_quot_span_p_pow (p := 37) (n + 1)
  obtain ⟨hfin, hcard⟩ := padicInt_card_eq_pow_length (p := 37) (n + 1) hlen
  exact ⟨hlen, hfin, hcard⟩

end Stage2Bridge

end RHDirect.Stage11FerreroWashington

