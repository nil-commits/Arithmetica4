import RHDirect.Stage5ThetaModular
import RHDirect.Stage7EisensteinSeries
import RHDirect.Stage8RamanujanDelta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# RHDirect.Stage8RamanujanCongruences

**UNCONDITIONAL RAMANUJAN CONGRUENCES FOR `τ(n)` (`mod 691, 2, 3, 5, 7, 9, 36`),
RAMANUJAN'S DIFFERENTIAL EQUATIONS FOR `E₂, E₄, E₆, Δ`, AND EXACT HIGHER-DIMENSIONAL
`E₈²` & `E₈³` LATTICE THETA / REPRESENTATION-NUMBER / EPSTEIN ZETA FORMULAS**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Exact Weight-12 Eisenstein Series `E₁₂` & Unconditional Ramanujan `691`-Congruence**:
   - `bernoulli_ten` (`5 / 66`) and `bernoulli_twelve` (`-691 / 2730`).
   - Normalized weight-12 Eisenstein series
     `E12(τ) = 1 + (65520 / 691) ∑_{n ≥ 1} σ₁₁(n) q^n` (`E12_eq_modularForm_E12`, `E12_qExpansion_coeff`).
   - Exact weight-12 identity:
     `E4 τ ^ 3 - E12 τ = (432000 / 691 : ℂ) * ramanujanDelta τ`
     (`E4CubeModularForm_sub_E12_eq_smul_delta`, `E4_cube_sub_E12_eq`).
   - Exact integer `q`-expansion identity for all `n ≥ 1`:
     `691 * coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) = 65520 * σ₁₁(n) + 432000 * τ(n)`.
   - **Ramanujan's `691`-Congruence (`ramanujanTau_mod_691`)**:
     `∀ n : ℕ, ramanujanTau n ≡ (ArithmeticFunction.sigma 11 n : ℤ) [ZMOD 691]`.

2. **Exact Higher-Dimensional Even Unimodular Lattice Identities (`E₈²` & `E₈³`)**:
   - Weight-8 `E₈² = E₈ ⊕ E₈` (rank 16):
     `Θ_{E₈²}(τ) = E₄(τ)² = E₈(τ) = 1 + 480 ∑_{n ≥ 1} σ₇(n) q^n`,
     `r_{E₈²}(2n) = 480 * σ₇(n)` for all `n ≥ 1` (`r_{E₈²}(2) = 480`, `r_{E₈²}(4) = 61920`),
     and exact Epstein zeta factorization for `Re(s) > 16`:
     `Z_{E₈²}(s) = 480 · 2^{-s/2} · ζ(s/2) · ζ(s/2 - 7)`.
   - Weight-12 `E₈³ = E₈ ⊕ E₈ ⊕ E₈` (rank 24):
     `Θ_{E₈³}(τ) = E₄(τ)³ = E₁₂(τ) + (432000 / 691) · Δ(τ)`,
     `691 * r_{E₈³}(2n) = 65520 * σ₁₁(n) + 432000 * τ(n)` for all `n ≥ 1`
     (`r_{E₈³}(2) = 720`, `r_{E₈³}(4) = 179280`).

3. **Ramanujan's Three Differential Equations & Classical Congruences Mod `2, 3, 5, 7, 9, 36`**:
   - Formal operator `θ = q d/dq` on `ℤ⟦q⟧` (`thetaOp`) satisfying:
     `12 θ E₂ = E₂² - E₄`, `3 θ E₄ = E₂ E₄ - E₆`, `2 θ E₆ = E₂ E₆ - E₄²`, and `θ Δ = E₂ Δ`.
   - Exact convolution identity `12 ∑_{k=1}^{n-1} σ₁(k) σ₁(n - k) = 5 σ₃(n) + (1 - 6n) σ₁(n)`
     and `24 ∣ (n - 1) * τ(n)`.
   - `ramanujanTau_mod_5`: `∀ n, τ(n) ≡ n * σ₁(n) [ZMOD 5]` (and `5 ∣ τ(5k)`).
   - `ramanujanTau_mod_7`: `∀ n, τ(n) ≡ n * σ₃(n) [ZMOD 7]` (and `7 ∣ τ(7k)`).
   - `ramanujanTau_mod_36`, `ramanujanTau_mod_9`, `ramanujanTau_mod_3`:
     `τ(n) ≡ n² σ₁(n) [ZMOD 36]`, `τ(n) ≡ n² σ₁(n) [ZMOD 9]`, and `τ(n) ≡ n σ₁(n) [ZMOD 3]`
     (and `3 ∣ τ(3k)`).
   - **Exact Parity Characterization (`odd_ramanujanTau_iff`)**:
     `Odd (ramanujanTau n) ↔ ∃ k : ℕ, n = (2 * k + 1) ^ 2`
     (with `even_ramanujanTau_of_prime : ∀ p, p.Prime → Even (ramanujanTau p)`).
-/

open Complex Real Filter Module Submodule Finset
open RHDirect.ArakelovCovolume RHDirect.Stage3ThetaSiegelBridge
open RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries RHDirect.Stage8RamanujanDelta
open scoped BigOperators UpperHalfPlane ModularForm Topology Manifold

namespace RHDirect.Stage8RamanujanCongruences

noncomputable section

/-! ## Section 1: Exact Weight-12 Eisenstein Series `E₁₂` & UNCONDITIONAL RAMANUJAN `691`-CONGRUENCE -/

section WeightTwelveAndMod691

/-- Exact Bernoulli number `B₁₀ = 5 / 66`. -/
theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  have hb6 : bernoulli' 6 = 1 / 42 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli_six]
  have hb8 : bernoulli' 8 = -1 / 30 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli_eight]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by decide : 1 < 5), hb6,
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by decide : 1 < 7), hb8,
    bernoulli'_eq_zero_of_odd (by decide : Odd 9) (by decide : 1 < 9)]
  norm_num

/-- Exact Bernoulli number `B₁₂ = -691 / 2730`. -/
theorem bernoulli_twelve : bernoulli 12 = -691 / 2730 := by
  have hb6 : bernoulli' 6 = 1 / 42 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli_six]
  have hb8 : bernoulli' 8 = -1 / 30 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli_eight]
  have hb10 : bernoulli' 10 = 5 / 66 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli_ten]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by decide : 1 < 5), hb6,
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by decide : 1 < 7), hb8,
    bernoulli'_eq_zero_of_odd (by decide : Odd 9) (by decide : 1 < 9), hb10,
    bernoulli'_eq_zero_of_odd (by decide : Odd 11) (by decide : 1 < 11)]
  norm_num

/-- **Normalized Weight-12 Holomorphic Eisenstein Series** on `UpperHalfPlane`:
$$E_{12}(\tau) = 1 + \frac{65520}{691} \sum_{n \ge 1} \sigma_{11}(n)\, e^{2\pi i n \tau}.$$ -/
def E12 (τ : UpperHalfPlane) : ℂ :=
  1 + (65520 / 691 : ℂ) * ∑' n : ℕ+, (ArithmeticFunction.sigma 11 (n : ℕ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ))

private lemma cexp_two_pi_I_zpow_pnat' (n : ℕ+) (τ : UpperHalfPlane) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
  rw [zpow_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Exact identification of `E12` with Mathlib's weight-12 Eisenstein series `ModularForm.E`. -/
theorem E12_eq_modularForm_E12 (τ : UpperHalfPlane) :
    E12 τ = ModularForm.E (k := 12) (by norm_num) τ := by
  have hq := EisensteinSeries.q_expansion_bernoulli (k := 12) (by norm_num) (by decide) τ
  rw [hq, bernoulli_twelve]
  unfold E12
  have htsum :
      (∑' n : ℕ+, (ArithmeticFunction.sigma (12 - 1) (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ)) =
      ∑' n : ℕ+, (ArithmeticFunction.sigma 11 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) :=
    tsum_congr fun n => by rw [show (12 - 1 : ℕ) = 11 by rfl, cexp_two_pi_I_zpow_pnat']
  rw [htsum]
  push_cast
  ring

lemma E12_eq_coe :
    E12 = (ModularForm.E (k := 12) (by norm_num) : UpperHalfPlane → ℂ) :=
  funext E12_eq_modularForm_E12

/-- Exact `q`-expansion coefficients of `E12`:
`coeff 0 = 1`, and `coeff m = (65520 / 691) * σ₁₁(m)` for `m ≥ 1`. -/
theorem E12_qExpansion_coeff (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 E12) =
      if m = 0 then 1 else (65520 / 691 : ℂ) * (ArithmeticFunction.sigma 11 m : ℂ) := by
  rw [E12_eq_coe]
  have h := EisensteinSeries.E_qExpansion_coeff (k := 12) (by norm_num) (by decide) m
  rw [h, bernoulli_twelve]
  split_ifs with hm
  · rfl
  · push_cast; ring

/-- The weight-12 modular form `E₄³ ∈ M₁₂(SL₂(ℤ))`. -/
def E4CubeModularForm : ModularForm SL2ZRange 12 :=
  ModularForm.mcast (by norm_num : (8 : ℤ) + 4 = 12)
    ((ModularForm.mcast (by norm_num : (4 : ℤ) + 4 = 8)
      (ModularForm.E₄.mul ModularForm.E₄) rfl).mul ModularForm.E₄) rfl

@[simp]
theorem E4CubeModularForm_apply (τ : UpperHalfPlane) :
    E4CubeModularForm τ = E4 τ ^ 3 := by
  change ModularForm.E₄ τ * ModularForm.E₄ τ * ModularForm.E₄ τ = E4 τ ^ 3
  rw [← E4_eq_modularForm_E4 τ]
  ring

/-- Exact `q`-expansion of `E₄³`: `qExpansion 1 E4CubeModularForm = (qExpansion 1 E4) ^ 3`. -/
theorem E4CubeModularForm_qExpansion :
    UpperHalfPlane.qExpansion 1 (E4CubeModularForm : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 E4 ^ 3 := by
  let e4sq : ModularForm SL2ZRange 8 :=
    ModularForm.mcast (by norm_num : (4 : ℤ) + 4 = 8) (ModularForm.E₄.mul ModularForm.E₄) rfl
  have he4sq_coe : (e4sq : UpperHalfPlane → ℂ) =
      (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := rfl
  have he4cube_coe : (E4CubeModularForm : UpperHalfPlane → ℂ) =
      (e4sq : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := rfl
  rw [he4cube_coe,
    ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL e4sq ModularForm.E₄,
    he4sq_coe,
    ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL ModularForm.E₄ ModularForm.E₄,
    ← E4_eq_coe]
  ring

private lemma coeff_natCast_mul' {R : Type*} [CommRing R] (c : ℕ) (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((c : PowerSeries R) * φ) = (c : R) * PowerSeries.coeff n φ := by
  rw [← map_natCast (PowerSeries.C (R := R)) c, PowerSeries.coeff_C_mul]

private lemma coeff_ofNat_mul {R : Type*} [CommRing R] (c : ℕ) [c.AtLeastTwo]
    (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (OfNat.ofNat c * φ) = OfNat.ofNat c * PowerSeries.coeff n φ := by
  rw [← map_ofNat (PowerSeries.C (R := R)) c, PowerSeries.coeff_C_mul]

private lemma int_modEq_sum {ι : Type*} {s : Finset ι} {m : ℤ} {f g : ι → ℤ}
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD m]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD m] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma map_intCast_E4_series :
    PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * sigma3SeriesZ) =
      UpperHalfPlane.qExpansion 1 E4 := by
  ext n
  rw [PowerSeries.coeff_map, E4_qExpansion_coeff]
  rw [map_add, coeff_ofNat_mul]
  simp only [sigma3SeriesZ, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs <;> simp

private lemma coeff_E4_cube_zero :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 E4 ^ 3) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
    E4_qExpansion_coeff 0, if_pos rfl, one_pow]

private lemma coeff_E4_cube_one :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 E4 ^ 3) = 720 := by
  have h1 : PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 E4 ^ 2) = 480 := by
    rw [sq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (UpperHalfPlane.qExpansion 1 E4) *
          PowerSeries.coeff b (UpperHalfPlane.qExpansion 1 E4)) 1]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_zero, Nat.sub_self,
      E4_qExpansion_coeff]
    norm_num
  rw [pow_succ, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (UpperHalfPlane.qExpansion 1 E4 ^ 2) *
        PowerSeries.coeff b (UpperHalfPlane.qExpansion 1 E4)) 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_zero, Nat.sub_self, h1]
  have h0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 E4 ^ 2) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      E4_qExpansion_coeff 0, if_pos rfl, one_pow]
  rw [h0, E4_qExpansion_coeff 0, E4_qExpansion_coeff 1]
  norm_num

/-- **EXACT WEIGHT-12 IDENTITY IN `M₁₂(SL₂(ℤ))`**:
`E₄³ - E₁₂ = (432000 / 691) • Δ`. -/
theorem E4CubeModularForm_sub_E12_eq_smul_delta :
    E4CubeModularForm - ModularForm.E (k := 12) (by norm_num) =
      (432000 / 691 : ℂ) • (ramanujanDelta : ModularForm SL2ZRange 12) := by
  let e12Mod : ModularForm SL2ZRange 12 := ModularForm.E (k := 12) (by norm_num)
  let diff : ModularForm SL2ZRange 12 := E4CubeModularForm - e12Mod
  have hq_diff : UpperHalfPlane.qExpansion 1 (diff : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 E4 ^ 3 - UpperHalfPlane.qExpansion 1 E12 := by
    change UpperHalfPlane.qExpansion 1 ((E4CubeModularForm - e12Mod : ModularForm SL2ZRange 12) :
      UpperHalfPlane → ℂ) = _
    rw [FunLike.coe_sub,
      ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL E4CubeModularForm e12Mod,
      E4CubeModularForm_qExpansion, ← E12_eq_coe]
  have h0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (diff : UpperHalfPlane → ℂ)) = 0 := by
    rw [hq_diff, map_sub, coeff_E4_cube_zero, E12_qExpansion_coeff 0, if_pos rfl, sub_self]
  let diffCusp : CuspForm SL2ZRange 12 := diff.toCuspForm h0
  have hsmul := cuspForm_SL2Z_weight_twelve_eq_smul_delta diffCusp
  have hc1 : PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (diffCusp : UpperHalfPlane → ℂ)) =
      (432000 / 691 : ℂ) := by
    change PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (diff : UpperHalfPlane → ℂ)) = _
    rw [hq_diff, map_sub, coeff_E4_cube_one, E12_qExpansion_coeff 1]
    simp only [one_ne_zero, ↓reduceIte, ArithmeticFunction.sigma_one, Nat.cast_one, mul_one]
    norm_num
  rw [hc1] at hsmul
  ext τ
  have hτ := congrArg (fun g : CuspForm SL2ZRange 12 => g τ) hsmul
  simpa [diffCusp, diff, e12Mod] using hτ

/-- **Pointwise Weight-12 Identity on `UpperHalfPlane`**:
`E₄(τ)³ - E₁₂(τ) = (432000 / 691) · Δ(τ)`. -/
theorem E4_cube_sub_E12_eq (τ : UpperHalfPlane) :
    E4 τ ^ 3 - E12 τ = (432000 / 691 : ℂ) * ramanujanDelta τ := by
  have h := congrArg (fun g : ModularForm SL2ZRange 12 => g τ) E4CubeModularForm_sub_E12_eq_smul_delta
  simpa [E12_eq_modularForm_E12 τ] using h

/-- **Exact Integer `q`-Expansion Identity of `E₄³ = E₁₂ + (432000 / 691) Δ`** for EVERY `n ≥ 1`:
$$691 \cdot [q^n]\, E_4(q)^3 = 65520 \cdot \sigma_{11}(n) + 432000 \cdot \tau(n).$$ -/
theorem mul_691_coeff_E4_cube_eq (n : ℕ) (hn : 1 ≤ n) :
    691 * PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) =
      65520 * (ArithmeticFunction.sigma 11 n : ℤ) + 432000 * ramanujanTau n := by
  have hn0 : n ≠ 0 := by omega
  have hq : UpperHalfPlane.qExpansion 1 E4 ^ 3 - UpperHalfPlane.qExpansion 1 E12 =
      (432000 / 691 : ℂ) • UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ) := by
    have h := congrArg (fun g : ModularForm SL2ZRange 12 =>
      UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ)) E4CubeModularForm_sub_E12_eq_smul_delta
    rw [FunLike.coe_sub,
      ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL E4CubeModularForm
        (ModularForm.E (k := 12) (by norm_num)),
      E4CubeModularForm_qExpansion, ← E12_eq_coe,
      FunLike.coe_smul,
      ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL (432000 / 691 : ℂ)
        (ramanujanDelta : ModularForm SL2ZRange 12)] at h
    exact h
  have hc := congrArg (PowerSeries.coeff n) hq
  rw [map_sub, map_smul, smul_eq_mul, E12_qExpansion_coeff n, if_neg hn0,
    ← ramanujanTau_cast_eq_qExpansion_coeff n] at hc
  have hE4Z : PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 E4 ^ 3) =
      ((PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) : ℤ) : ℂ) := by
    rw [← map_intCast_E4_series, ← map_pow, PowerSeries.coeff_map]
    rfl
  rw [hE4Z] at hc
  have hC : ((691 * PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) : ℤ) : ℂ) =
      ((65520 * (ArithmeticFunction.sigma 11 n : ℤ) + 432000 * ramanujanTau n : ℤ) : ℂ) := by
    push_cast
    linear_combination 691 * hc
  exact Int.cast_injective hC

/-- **UNCONDITIONAL RAMANUJAN'S `691`-CONGRUENCE (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$\tau(n) \equiv \sigma_{11}(n) \pmod{691}.$$ -/
theorem ramanujanTau_mod_691 (n : ℕ) :
    ramanujanTau n ≡ (ArithmeticFunction.sigma 11 n : ℤ) [ZMOD 691] := by
  by_cases hn : n = 0
  · subst hn
    simp [ramanujanTau_zero]
  · have h := mul_691_coeff_E4_cube_eq n (Nat.pos_of_ne_zero hn)
    have hdvd_mul : (691 : ℤ) ∣ 65520 * ((ArithmeticFunction.sigma 11 n : ℤ) - ramanujanTau n) := by
      refine ⟨PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) - 720 * ramanujanTau n, ?_⟩
      linarith
    have hcop : IsCoprime (691 : ℤ) 65520 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      decide
    have hdvd : (691 : ℤ) ∣ (ArithmeticFunction.sigma 11 n : ℤ) - ramanujanTau n :=
      hcop.dvd_of_dvd_mul_left hdvd_mul
    exact (Int.modEq_iff_dvd.mpr hdvd)

end WeightTwelveAndMod691

/-! ## Section 2: Exact `E₈^k` Shells, `Θ_{E₈²} = E₄² = E₈`, `Θ_{E₈³} = E₄³ = E₁₂ + (432000/691) Δ`, & `Z_{E₈²}(s)` -/

section HigherE8Powers

/-- The `n`-th norm shell of the `k`-fold direct-sum lattice `E₈^k`: `{v ∈ E₈^k | ‖v‖² = 2n}`. -/
abbrev E8PowShell (k n : ℕ) : Type :=
  {v : E8PowLattice k // ‖(v : EuclideanSpace ℝ (Fin k × Fin 8))‖ ^ 2 = 2 * (n : ℝ)}

/-- Every vector in `E₈^k` has squared norm `2 * n` for a unique natural number `n : ℕ`. -/
lemma exists_nat_norm_sq_eq_two_mul_E8Pow (k : ℕ) (v : E8PowLattice k) :
    ∃ n : ℕ, ‖(v : EuclideanSpace ℝ (Fin k × Fin 8))‖ ^ 2 = 2 * (n : ℝ) := by
  obtain ⟨m, hm⟩ := isEvenLattice_E8PowLattice k (v : EuclideanSpace ℝ (Fin k × Fin 8)) v.2
  have hm_nonneg : (0 : ℤ) ≤ m := by
    have hnn : (0 : ℝ) ≤ 2 * (m : ℝ) := hm ▸ sq_nonneg _
    have hmR : (0 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast hmR
  refine ⟨m.toNat, ?_⟩
  rw [hm]
  have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm_nonneg
  rw [hcast]

/-- Every norm shell `E8PowShell k n = {v ∈ E₈^k | ‖v‖² = 2n}` is finite! -/
instance finite_E8PowShell (k n : ℕ) : Finite (E8PowShell k n) := by
  let M : ℤ := 2 * (n : ℤ) + 2
  let box : Finset (Fin k × Fin 8 → ℤ) :=
    Fintype.piFinset (fun _ : Fin k × Fin 8 => Finset.Icc (-M) M)
  let toBox : E8PowShell k n → box := fun v =>
    ⟨fun ji => Classical.choose ((v.1.2 ji.1).1 ji.2), by
      rw [Fintype.mem_piFinset]
      intro ji
      rw [Finset.mem_Icc]
      set c : ℤ := Classical.choose ((v.1.2 ji.1).1 ji.2)
      have hc : 2 * (v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji = (c : ℝ) :=
        Classical.choose_spec ((v.1.2 ji.1).1 ji.2)
      have hv_sq : ((v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji) ^ 2 ≤ 2 * (n : ℝ) := by
        calc ((v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji) ^ 2
            = ‖(v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji‖ ^ 2 := by simp [Real.norm_eq_abs]
          _ ≤ ∑ p : Fin k × Fin 8, ‖(v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) p‖ ^ 2 :=
              Finset.single_le_sum
                (f := fun p : Fin k × Fin 8 => ‖(v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) p‖ ^ 2)
                (fun p _ => sq_nonneg _) (Finset.mem_univ ji)
          _ = ‖(v.1 : EuclideanSpace ℝ (Fin k × Fin 8))‖ ^ 2 := (EuclideanSpace.norm_sq_eq _).symm
          _ = 2 * (n : ℝ) := v.2
      have hc_sq : (c : ℝ) ^ 2 ≤ 8 * (n : ℝ) := by
        have h1 : (c : ℝ) ^ 2 = 4 * ((v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji) ^ 2 := by
          rw [← hc]; ring
        linarith
      have hM_ge : (8 * (n : ℝ)) ≤ (M : ℝ) ^ 2 := by
        dsimp only [M]; push_cast; nlinarith
      have hc_abs : |(c : ℝ)| ≤ (M : ℝ) := by
        have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := by dsimp only [M]; positivity
        exact abs_le_of_sq_le_sq (hc_sq.trans hM_ge) hM_nonneg
      have ⟨hlo, hhi⟩ := abs_le.mp hc_abs
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩⟩
  have hinj : Function.Injective toBox := by
    intro u w h
    apply Subtype.ext
    apply Subtype.ext
    ext ji
    have hci : Classical.choose ((u.1.2 ji.1).1 ji.2) = Classical.choose ((w.1.2 ji.1).1 ji.2) :=
      congrFun (congrArg Subtype.val h) ji
    have hu : 2 * (u.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji =
        ((Classical.choose ((u.1.2 ji.1).1 ji.2) : ℤ) : ℝ) :=
      Classical.choose_spec ((u.1.2 ji.1).1 ji.2)
    have hw : 2 * (w.1 : EuclideanSpace ℝ (Fin k × Fin 8)) ji =
        ((Classical.choose ((w.1.2 ji.1).1 ji.2) : ℤ) : ℝ) :=
      Classical.choose_spec ((w.1.2 ji.1).1 ji.2)
    have hciR : ((Classical.choose ((u.1.2 ji.1).1 ji.2) : ℤ) : ℝ) =
        ((Classical.choose ((w.1.2 ji.1).1 ji.2) : ℤ) : ℝ) := by
      exact_mod_cast hci
    linarith
  exact Finite.of_injective toBox hinj

/-- Canonical shell decomposition `E8PowLattice k ≃ Σ n : ℕ, E8PowShell k n`. -/
def E8PowLatticeEquivSigmaShell (k : ℕ) : E8PowLattice k ≃ Σ n : ℕ, E8PowShell k n where
  toFun v :=
    ⟨Classical.choose (exists_nat_norm_sq_eq_two_mul_E8Pow k v),
     ⟨v, Classical.choose_spec (exists_nat_norm_sq_eq_two_mul_E8Pow k v)⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨n, ⟨v, hv⟩⟩
    dsimp only
    have hn : Classical.choose (exists_nat_norm_sq_eq_two_mul_E8Pow k v) = n := by
      have hspec := Classical.choose_spec (exists_nat_norm_sq_eq_two_mul_E8Pow k v)
      have hR : ((Classical.choose (exists_nat_norm_sq_eq_two_mul_E8Pow k v) : ℕ) : ℝ) = (n : ℝ) := by
        linarith
      exact_mod_cast hR
    cases hn
    rfl

/-- Exact `q`-series expansion of `Θ_{E₈^k}(τ)` for every `k : ℕ`. -/
theorem complexLatticeTheta_E8PowLattice_hasSum_qParam (k : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      (Nat.card (E8PowShell k n) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n)
      (complexLatticeTheta (E8PowLattice k) τ) := by
  have hsum_L : HasSum
      (fun v : E8PowLattice k =>
        complexGaussianTerm (τ : ℂ) (v : EuclideanSpace ℝ (Fin k × Fin 8)))
      (complexLatticeTheta (E8PowLattice k) τ) :=
    (summable_complexGaussianTerm (E8PowLattice k) τ.im_pos).hasSum
  have hsum_sig : HasSum
      (fun p : Σ n : ℕ, E8PowShell k n =>
        complexGaussianTerm (τ : ℂ) (p.2.1 : EuclideanSpace ℝ (Fin k × Fin 8)))
      (complexLatticeTheta (E8PowLattice k) τ) :=
    ((E8PowLatticeEquivSigmaShell k).symm.hasSum_iff).mpr hsum_L
  have hinner : ∀ n : ℕ,
      HasSum (fun v : E8PowShell k n =>
        complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin k × Fin 8)))
        ((Nat.card (E8PowShell k n) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) := by
    intro n
    cases nonempty_fintype (E8PowShell k n)
    have hterm : ∀ v : E8PowShell k n,
        complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin k × Fin 8)) =
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n := by
      intro v
      unfold complexGaussianTerm Function.Periodic.qParam
      rw [v.2, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hfin := hasSum_fintype (fun v : E8PowShell k n =>
      complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin k × Fin 8)))
    have hsum_eq : (∑ v : E8PowShell k n,
        complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin k × Fin 8))) =
        (Nat.card (E8PowShell k n) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n := by
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    rwa [hsum_eq] at hfin
  exact hsum_sig.sigma hinner

/-- Boundedness of `complexLatticeTheta (E8PowLattice k)` at `i∞`. -/
theorem isBoundedAtImInfty_complexLatticeTheta_E8PowLattice (k : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (complexLatticeTheta (E8PowLattice k)) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨latticeTheta (E8PowLattice k) 1, 1, fun τ hτ => ?_⟩
  have h1 := norm_complexLatticeTheta_le (E8PowLattice k) τ
  refine h1.trans ?_
  unfold latticeTheta
  refine Summable.tsum_le_tsum (fun v => ?_) (summable_gaussianTerm (E8PowLattice k) τ.im_pos)
    (summable_gaussianTerm (E8PowLattice k) zero_lt_one)
  unfold gaussianTerm
  apply Real.exp_le_exp.mpr
  have hnn : 0 ≤ Real.pi * ‖(v : EuclideanSpace ℝ (Fin k × Fin 8))‖ ^ 2 :=
    mul_nonneg Real.pi_pos.le (sq_nonneg _)
  nlinarith

/-- **`Θ_{E₈^k}` Packaged as a Genuine Level-1 Weight-`4k` Modular Form** for EVERY `k : ℕ`! -/
def E8PowThetaModularForm (k : ℕ) : ModularForm SL2ZRange ((4 * k : ℕ) : ℤ) where
  toFun := complexLatticeTheta (E8PowLattice k)
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    simpa [sl2ZToGL2R_eq_mapGL] using E8PowLattice_slash_SL2Z_invariant k γ
  holo' := mdifferentiable_complexLatticeTheta (E8PowLattice k)
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map ((4 * k : ℕ) : ℤ) γ (complexLatticeTheta (E8PowLattice k)) =
        complexLatticeTheta (E8PowLattice k) := by
      rw [ModularForm.SL_slash]
      exact E8PowLattice_slash_SL2Z_invariant k γ
    rw [hinv]
    exact isBoundedAtImInfty_complexLatticeTheta_E8PowLattice k

@[simp]
lemma E8PowThetaModularForm_apply (k : ℕ) (τ : UpperHalfPlane) :
    E8PowThetaModularForm k τ = complexLatticeTheta (E8PowLattice k) τ := rfl

/-- Exact `n`-th `q`-expansion coefficient of `E8PowThetaModularForm k` equals
`Nat.card (E8PowShell k n)` for EVERY `k, n : ℕ`. -/
theorem E8PowThetaModularForm_qExpansion_coeff (k n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (E8PowThetaModularForm k : UpperHalfPlane → ℂ)) =
      (Nat.card (E8PowShell k n) : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
    (f := E8PowThetaModularForm k) (complexLatticeTheta_E8PowLattice_hasSum_qParam k) n).symm

/-- **Exact Weight-8 `E₈²` Theta Identity (`Θ_{E₈²}(τ) = E₄(τ)² = E₈(τ)`)**. -/
theorem theta_E8_sq_eq_E4_sq (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice 2) τ = E4 τ ^ 2 := by
  rw [complexLatticeTheta_E8PowLattice 2 τ, complexLatticeTheta_E8Lattice_eq_E4 τ]

theorem theta_E8_sq_eq_eisenstein8 (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice 2) τ = E8Eisenstein τ :=
  complexLatticeTheta_E8PowLattice_two_eq_E8Eisenstein τ

/-- **EXACT `E₈²` (16-DIMENSIONAL) REPRESENTATION-NUMBER FORMULA**:
for EVERY `n ≥ 1`, `r_{E₈²}(2n) = 480 · σ₇(n)`! -/
theorem rep_E8_sq_eq (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (E8PowShell 2 n) = 480 * ArithmeticFunction.sigma 7 n := by
  have hn0 : n ≠ 0 := by omega
  have hfun : (E8PowThetaModularForm 2 : UpperHalfPlane → ℂ) = E8Eisenstein :=
    funext theta_E8_sq_eq_eisenstein8
  have hC : (Nat.card (E8PowShell 2 n) : ℂ) = ((480 * ArithmeticFunction.sigma 7 n : ℕ) : ℂ) := by
    calc (Nat.card (E8PowShell 2 n) : ℂ)
        = PowerSeries.coeff n
            (UpperHalfPlane.qExpansion 1 (E8PowThetaModularForm 2 : UpperHalfPlane → ℂ)) :=
            (E8PowThetaModularForm_qExpansion_coeff 2 n).symm
      _ = PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 E8Eisenstein) := by rw [hfun]
      _ = 480 * (ArithmeticFunction.sigma 7 n : ℂ) := by
            rw [E8Eisenstein_qExpansion_coeff n, if_neg hn0]
      _ = ((480 * ArithmeticFunction.sigma 7 n : ℕ) : ℂ) := by push_cast; rfl
  exact Nat.cast_injective hC

/-- Verified first shell of `E₈²`: `r_{E₈²}(2) = 480`. -/
theorem E8_sq_kissing_number : Nat.card (E8PowShell 2 1) = 480 := by
  simpa using rep_E8_sq_eq 1 le_rfl

/-- Verified second shell of `E₈²`: `r_{E₈²}(4) = 61920`. -/
theorem E8_sq_shell_two_card : Nat.card (E8PowShell 2 2) = 61920 := by
  have h := rep_E8_sq_eq 2 (by decide)
  have hsig : ArithmeticFunction.sigma 7 2 = 129 := by decide
  rw [hsig] at h
  norm_num at h
  exact h

/-- `ℤ`-linear equivalence `E8PowLattice k ≃ₗ[ℤ] (Fin k → E8Lattice)`. -/
def E8PowLatticeLinearEquiv (k : ℕ) : E8PowLattice k ≃ₗ[ℤ] (Fin k → E8Lattice) where
  toFun v j := ⟨WithLp.toLp 2 (fun i : Fin 8 => (v : EuclideanSpace ℝ (Fin k × Fin 8)) (j, i)), v.2 j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    ⟨WithLp.toLp 2 (fun ji : Fin k × Fin 8 => (f ji.1 : EuclideanSpace ℝ (Fin 8)) ji.2),
      fun j => (f j).2⟩
  left_inv v := by
    apply Subtype.ext; ext ⟨j, i⟩; rfl
  right_inv f := by
    funext j; apply Subtype.ext; ext i; rfl

/-- Exact rank of the `k`-fold direct sum `E₈^k`: `rk (E8PowLattice k) = 8 * k`. -/
theorem rk_E8PowLattice (k : ℕ) : rk (E8PowLattice k) = 8 * k := by
  unfold rk
  let b : Basis (Σ _ : Fin k, Fin 8) ℤ (E8PowLattice k) :=
    (Pi.basis (fun _ : Fin k => E8Basis)).map (E8PowLatticeLinearEquiv k).symm
  rw [Module.finrank_eq_card_basis b, Fintype.card_sigma]
  simp [mul_comm]

/-- Canonical nonzero shell decomposition `{v : E₈^k // v ≠ 0} ≃ Σ n : ℕ+, E8PowShell k n`. -/
def E8PowNonzeroEquivSigmaShell (k : ℕ) :
    {v : E8PowLattice k // (v : EuclideanSpace ℝ (Fin k × Fin 8)) ≠ 0} ≃
      Σ n : ℕ+, E8PowShell k (n : ℕ) :=
  (Equiv.ofBijective
    (fun p : Σ n : ℕ+, E8PowShell k (n : ℕ) =>
      (⟨p.2.1, by
        intro h0
        have h2 := p.2.2
        rw [h0, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h2
        have hp : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.1.pos
        linarith⟩ : {v : E8PowLattice k // (v : EuclideanSpace ℝ (Fin k × Fin 8)) ≠ 0}))
    (by
      constructor
      · rintro ⟨n₁, ⟨v₁, hv₁⟩⟩ ⟨n₂, ⟨v₂, hv₂⟩⟩ h
        have hv : v₁ = v₂ := congrArg Subtype.val h
        subst hv
        have hn : n₁ = n₂ := by
          have hR : ((n₁ : ℕ) : ℝ) = ((n₂ : ℕ) : ℝ) := by linarith
          exact_mod_cast hR
        subst hn
        rfl
      · rintro ⟨v, hv0⟩
        obtain ⟨m, hm⟩ := exists_nat_norm_sq_eq_two_mul_E8Pow k v
        have hm_pos : 0 < m := by
          by_contra h0
          have hm0 : m = 0 := by omega
          rw [hm0, Nat.cast_zero, mul_zero] at hm
          exact hv0 (norm_eq_zero.mp (sq_eq_zero_iff.mp hm))
        exact ⟨⟨⟨m, hm_pos⟩, ⟨v, hm⟩⟩, Subtype.ext rfl⟩)).symm

private lemma norm_cpow_neg_of_norm_sq_eq_two_mul' {x : ℝ} {n : ℕ+}
    (hx : 0 ≤ x) (hsq : x ^ 2 = 2 * ((n : ℕ) : ℝ)) (s : ℂ) :
    (x : ℂ) ^ (-s) = (2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2) := by
  have hn_pos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have hx_pos : 0 < x := by
    by_contra h
    have hx0 : x = 0 := le_antisymm (not_lt.mp h) hx
    rw [hx0] at hsq
    norm_num at hsq
  have hstep1 : (x : ℂ) ^ (-s) = ((x ^ 2 : ℝ) : ℂ) ^ (-s / 2) := by
    rw [Complex.ofReal_pow, ← Complex.cpow_natCast (x : ℂ) 2,
      ← Complex.cpow_mul (x := (x : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := -s / 2)]
    · congr 1; push_cast; ring
    · rw [← Complex.ofReal_log hx_pos.le]; simp [Real.pi_pos]
    · rw [← Complex.ofReal_log hx_pos.le]; simp [Real.pi_pos.le]
  rw [hstep1, hsq, Complex.ofReal_mul]
  have h2re : 0 < ((2 : ℝ) : ℂ).re := by norm_num
  simpa using cpow_mul_ofReal_pos h2re hn_pos (-s / 2)

/-- **EXACT EPSTEIN–EISENSTEIN ZETA FACTORIZATION FOR `E₈²` (16D, ZERO ASSUMPTIONS!)**:
for EVERY `s : ℂ` with `Re(s) > 16`,
$$Z_{E_8^2}(s) = 480 \cdot 2^{-s/2} \cdot \zeta(s/2) \cdot \zeta(s/2 - 7).$$ -/
theorem epsteinZeta_E8_sq_eq {s : ℂ} (hs : (16 : ℝ) < s.re) :
    epsteinZeta (E8PowLattice 2) s =
      480 * (2 : ℂ) ^ (-s / 2) * riemannZeta (s / 2) * riemannZeta (s / 2 - 7) := by
  have hsum_ep : Summable (fun v : {v : E8PowLattice 2 //
      (v : EuclideanSpace ℝ (Fin 2 × Fin 8)) ≠ 0} =>
      ((‖(v.1 : EuclideanSpace ℝ (Fin 2 × Fin 8))‖ : ℝ) : ℂ) ^ (-s)) :=
    summable_epsteinZeta (E8PowLattice 2) (by rw [rk_E8PowLattice]; norm_num; exact hs)
  have hsum_sig : HasSum
      (fun p : Σ n : ℕ+, E8PowShell 2 (n : ℕ) =>
        ((‖(p.2.1 : EuclideanSpace ℝ (Fin 2 × Fin 8))‖ : ℝ) : ℂ) ^ (-s))
      (epsteinZeta (E8PowLattice 2) s) :=
    ((E8PowNonzeroEquivSigmaShell 2).symm.hasSum_iff).mpr hsum_ep.hasSum
  have hinner : ∀ n : ℕ+,
      HasSum (fun v : E8PowShell 2 (n : ℕ) =>
        ((‖(v.1 : EuclideanSpace ℝ (Fin 2 × Fin 8))‖ : ℝ) : ℂ) ^ (-s))
        ((Nat.card (E8PowShell 2 (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2))) := by
    intro n
    cases nonempty_fintype (E8PowShell 2 (n : ℕ))
    have hterm : ∀ v : E8PowShell 2 (n : ℕ),
        ((‖(v.1 : EuclideanSpace ℝ (Fin 2 × Fin 8))‖ : ℝ) : ℂ) ^ (-s) =
          (2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2) := fun v =>
      norm_cpow_neg_of_norm_sq_eq_two_mul' (norm_nonneg _) v.2 s
    have hfin := hasSum_fintype (fun v : E8PowShell 2 (n : ℕ) =>
      ((‖(v.1 : EuclideanSpace ℝ (Fin 2 × Fin 8))‖ : ℝ) : ℂ) ^ (-s))
    have hsum_eq : (∑ v : E8PowShell 2 (n : ℕ),
        ((‖(v.1 : EuclideanSpace ℝ (Fin 2 × Fin 8))‖ : ℝ) : ℂ) ^ (-s)) =
        (Nat.card (E8PowShell 2 (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2)) := by
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    rwa [hsum_eq] at hfin
  have houter_eq : epsteinZeta (E8PowLattice 2) s =
      ∑' n : ℕ+, (Nat.card (E8PowShell 2 (n : ℕ)) : ℂ) *
        ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2)) :=
    (hsum_sig.sigma hinner).tsum_eq.symm
  rw [houter_eq]
  have hrew : (fun n : ℕ+ =>
      (Nat.card (E8PowShell 2 (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2))) =
      fun n : ℕ+ =>
        (480 * (2 : ℂ) ^ (-s / 2)) *
          ((ArithmeticFunction.sigma 7 (n : ℕ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(s / 2))) := by
    funext n
    rw [rep_E8_sq_eq (n : ℕ) n.pos]
    have hneg : -s / 2 = -(s / 2) := by ring
    rw [hneg]
    push_cast
    ring
  rw [hrew, tsum_mul_left]
  have hw : ((7 : ℕ) : ℝ) + 1 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    push_cast
    linarith
  rw [tsum_pnat_sigma_mul_cpow 7 hw]
  push_cast
  ring

/-- **EXACT `E₈³` (24-DIMENSIONAL) THETA IDENTITY**:
`Θ_{E₈³}(τ) = E₄(τ)³ = E₁₂(τ) + (432000 / 691) · Δ(τ)`. -/
theorem theta_E8_cube_eq (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice 3) τ = E4 τ ^ 3 := by
  rw [complexLatticeTheta_E8PowLattice 3 τ, complexLatticeTheta_E8Lattice_eq_E4 τ]

theorem theta_E8_cube_eq_E12_add_delta (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice 3) τ = E12 τ + (432000 / 691 : ℂ) * ramanujanDelta τ := by
  rw [theta_E8_cube_eq τ]
  linear_combination E4_cube_sub_E12_eq τ

/-- **EXACT `E₈³` (24-DIMENSIONAL) REPRESENTATION-NUMBER FORMULA (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n ≥ 1`,
$$691 \cdot r_{E_8^3}(2n) = 65520 \cdot \sigma_{11}(n) + 432000 \cdot \tau(n).$$ -/
theorem rep_E8_cube_eq (n : ℕ) (hn : 1 ≤ n) :
    691 * (Nat.card (E8PowShell 3 n) : ℤ) =
      65520 * (ArithmeticFunction.sigma 11 n : ℤ) + 432000 * ramanujanTau n := by
  have hfun : (E8PowThetaModularForm 3 : UpperHalfPlane → ℂ) =
      (E4CubeModularForm : UpperHalfPlane → ℂ) := by
    funext τ
    rw [E8PowThetaModularForm_apply, E4CubeModularForm_apply, theta_E8_cube_eq]
  have hcard : (Nat.card (E8PowShell 3 n) : ℤ) =
      PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) := by
    have hC : ((Nat.card (E8PowShell 3 n) : ℤ) : ℂ) =
        ((PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) : ℤ) : ℂ) := by
      calc ((Nat.card (E8PowShell 3 n) : ℤ) : ℂ)
          = (Nat.card (E8PowShell 3 n) : ℂ) := by push_cast; rfl
        _ = PowerSeries.coeff n
              (UpperHalfPlane.qExpansion 1 (E8PowThetaModularForm 3 : UpperHalfPlane → ℂ)) :=
              (E8PowThetaModularForm_qExpansion_coeff 3 n).symm
        _ = PowerSeries.coeff n
              (UpperHalfPlane.qExpansion 1 (E4CubeModularForm : UpperHalfPlane → ℂ)) := by
              rw [hfun]
        _ = PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 E4 ^ 3) := by
              rw [E4CubeModularForm_qExpansion]
        _ = ((PowerSeries.coeff n ((1 + 240 * sigma3SeriesZ) ^ 3) : ℤ) : ℂ) := by
              rw [← map_intCast_E4_series, ← map_pow, PowerSeries.coeff_map]; rfl
    exact Int.cast_injective hC
  rw [hcard]
  exact mul_691_coeff_E4_cube_eq n hn

/-- Verified kissing number of `E₈³` (`r_{E₈³}(2) = 720`). -/
theorem E8_cube_kissing_number : Nat.card (E8PowShell 3 1) = 720 := by
  have h := rep_E8_cube_eq 1 le_rfl
  simp only [ArithmeticFunction.sigma_one, Nat.cast_one, mul_one, ramanujanTau_one] at h
  omega

/-- Verified second shell of `E₈³` (`r_{E₈³}(4) = 179280`). -/
theorem E8_cube_shell_two_card : Nat.card (E8PowShell 3 2) = 179280 := by
  have h := rep_E8_cube_eq 2 (by decide)
  have hsig : ArithmeticFunction.sigma 11 2 = 2049 := by decide
  rw [hsig, ramanujanTau_two] at h
  omega

end HigherE8Powers

/-! ## Section 3: Ramanujan's Differential Equations (`12 θ E₂ = E₂² - E₄`, `3 θ E₄ = E₂ E₄ - E₆`, `2 θ E₆ = E₂ E₆ - E₄²`) & `θ Δ = E₂ Δ` -/

section RamanujanODEs

/-- Formal Ramanujan differential operator `θ = q d/dq` on `PowerSeries R`:
`(thetaOp φ)_n = n * φ_n`. -/
def thetaOp {R : Type*} [CommRing R] (φ : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n φ

@[simp]
lemma coeff_thetaOp {R : Type*} [CommRing R] (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (thetaOp φ) = (n : R) * PowerSeries.coeff n φ :=
  PowerSeries.coeff_mk n _

lemma thetaOp_one {R : Type*} [CommRing R] : thetaOp (1 : PowerSeries R) = 0 := by
  ext n
  rw [coeff_thetaOp, map_zero, PowerSeries.coeff_one]
  split_ifs with hn
  · subst hn; simp
  · simp

lemma thetaOp_add {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    thetaOp (φ + ψ) = thetaOp φ + thetaOp ψ := by
  ext n
  simp only [coeff_thetaOp, map_add]
  ring

lemma thetaOp_sub {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    thetaOp (φ - ψ) = thetaOp φ - thetaOp ψ := by
  ext n
  simp only [coeff_thetaOp, map_sub]
  ring

lemma thetaOp_natCast_mul {R : Type*} [CommRing R] (c : ℕ) (φ : PowerSeries R) :
    thetaOp ((c : PowerSeries R) * φ) = (c : PowerSeries R) * thetaOp φ := by
  ext n
  rw [coeff_thetaOp, coeff_natCast_mul', coeff_natCast_mul', coeff_thetaOp]
  ring

lemma thetaOp_ofNat_mul {R : Type*} [CommRing R] (c : ℕ) [c.AtLeastTwo] (φ : PowerSeries R) :
    thetaOp (OfNat.ofNat c * φ) = OfNat.ofNat c * thetaOp φ := by
  ext n
  rw [coeff_thetaOp, coeff_ofNat_mul, coeff_ofNat_mul, coeff_thetaOp]
  ring

lemma thetaOp_mul {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    thetaOp (φ * ψ) = thetaOp φ * ψ + φ * thetaOp ψ := by
  ext n
  rw [coeff_thetaOp, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_thetaOp, coeff_thetaOp]
  have hp_eq : ((p.1 : R) + (p.2 : R)) = (n : R) := by
    rw [← Nat.cast_add, Finset.mem_antidiagonal.mp hp]
  rw [← hp_eq]
  ring

lemma thetaOp_sq {R : Type*} [CommRing R] (φ : PowerSeries R) :
    thetaOp (φ ^ 2) = 2 * φ * thetaOp φ := by
  rw [sq, thetaOp_mul]
  ring

lemma thetaOp_cube {R : Type*} [CommRing R] (φ : PowerSeries R) :
    thetaOp (φ ^ 3) = 3 * φ ^ 2 * thetaOp φ := by
  rw [pow_succ, thetaOp_mul, thetaOp_sq]
  ring

lemma map_thetaOp {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (φ : PowerSeries R) :
    PowerSeries.map f (thetaOp φ) = thetaOp (PowerSeries.map f φ) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_thetaOp, map_mul, map_natCast]

/-- Formal integer power series `A₁(q) = ∑_{n ≥ 1} σ₁(n) q^n ∈ ℤ⟦q⟧`. -/
def sigma1SeriesZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (ArithmeticFunction.sigma 1 n : ℤ)

/-- Formal integer `q`-series of `E₂(q) = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n ∈ ℤ⟦q⟧`. -/
def E2SeriesZ : PowerSeries ℤ := 1 - 24 * sigma1SeriesZ

/-- Formal integer `q`-series of `E₄(q) = 1 + 240 ∑_{n ≥ 1} σ₃(n) q^n ∈ ℤ⟦q⟧`. -/
def E4SeriesZ : PowerSeries ℤ := 1 + 240 * sigma3SeriesZ

/-- Formal integer `q`-series of `E₆(q) = 1 - 504 ∑_{n ≥ 1} σ₅(n) q^n ∈ ℤ⟦q⟧`. -/
def E6SeriesZ : PowerSeries ℤ := 1 - 504 * sigma5SeriesZ

/-- Elementary divisor-sum bound: `σ_k(n) ≤ n^(k + 1)` for every `k, n : ℕ`. -/
private lemma sigma_le_pow_succ (k n : ℕ) :
    ArithmeticFunction.sigma k n ≤ n ^ (k + 1) := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [ArithmeticFunction.sigma_apply]
    calc ∑ d ∈ n.divisors, d ^ k
        ≤ ∑ _d ∈ n.divisors, n ^ k :=
          Finset.sum_le_sum fun d hd =>
            Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)) k
      _ = n.divisors.card * n ^ k := by simp
      _ ≤ n * n ^ k := by
          refine Nat.mul_le_mul_right _ ?_
          have hsub : n.divisors ⊆ Finset.Icc 1 n := fun d hd =>
            Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
              (Nat.pos_of_ne_zero hn), Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)⟩
          calc n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
            _ = n := by simp
      _ = n ^ (k + 1) := by rw [pow_succ']

private lemma norm_qParam_one (w : ℂ) :
    ‖Function.Periodic.qParam (1 : ℝ) w‖ = Real.exp (-2 * Real.pi * w.im) := by
  unfold Function.Periodic.qParam
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.ofReal_one, div_one, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

private lemma summable_poly_mul_geom {C : ℝ} {d : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℕ => C * ((m : ℝ) ^ d) * r ^ m) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one d (r := r) (by rwa [Real.norm_of_nonneg hr0])
  simpa [mul_assoc] using h.mul_left C

/-- Clean summability for `(m + 1)^d * r^m` when `0 ≤ C`, `0 ≤ r < 1`. -/
private lemma summable_C_mul_succ_pow_geom {C : ℝ} (hC : 0 ≤ C) (d : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℕ => C * (((m : ℝ) + 1) ^ d) * r ^ m) := by
  have h1 : Summable (fun m : ℕ => (C * (2 : ℝ) ^ d) * ((m : ℝ) ^ d) * r ^ m) :=
    summable_poly_mul_geom hr0 hr1
  have h2 : Summable (fun m : ℕ => (C * (2 : ℝ) ^ d) * r ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (h1.add h2)
  have hpow : ((m : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ d * ((m : ℝ) ^ d + 1) := by
    by_cases hm : m = 0
    · subst hm
      simp only [Nat.cast_zero, zero_add, one_pow]
      have h2d : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have h0d : (0 : ℝ) ≤ (0 : ℝ) ^ d := pow_nonneg le_rfl d
      nlinarith
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
      calc ((m : ℝ) + 1) ^ d ≤ (2 * (m : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) hle d
        _ = (2 : ℝ) ^ d * (m : ℝ) ^ d := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ d * ((m : ℝ) ^ d + 1) := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hrpow : 0 ≤ r ^ m := pow_nonneg hr0 m
  calc C * (((m : ℝ) + 1) ^ d) * r ^ m
      ≤ C * ((2 : ℝ) ^ d * ((m : ℝ) ^ d + 1)) * r ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hrpow
    _ = C * (2 : ℝ) ^ d * (m : ℝ) ^ d * r ^ m + C * (2 : ℝ) ^ d * r ^ m := by ring

/-- **Term-by-Term `normalizedDerivOfComplex` and Boundedness at `i∞`** for any `q`-series
`F(τ) = ∑' m, c m • q^m` with polynomially bounded coefficients `‖c m‖ ≤ C * (m + 1)^d`:
1. `HasSum (fun m => ((m : ℂ) * c m) • qParam 1 τ ^ m) (normalizedDerivOfComplex F τ)`,
2. `UpperHalfPlane.IsBoundedAtImInfty (normalizedDerivOfComplex F)`. -/
private lemma normalizedDerivOfComplex_hasSum_and_bounded
    {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C) (d : ℕ)
    (hc_bound : ∀ m : ℕ, ‖c m‖ ≤ C * (((m : ℝ) + 1) ^ d))
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) (F τ)) :
    (∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => ((m : ℂ) * c m) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
        (Derivative.normalizedDerivOfComplex F τ)) ∧
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex F) := by
  have hhas : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => ((m : ℂ) * c m) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
        (Derivative.normalizedDerivOfComplex F τ) := by
    intro τ
    let δ : ℝ := τ.im / 2
    have hδ : 0 < δ := half_pos τ.im_pos
    let U : Set ℂ := {w : ℂ | δ < w.im}
    have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
    have hτU : (τ : ℂ) ∈ U := by change τ.im / 2 < τ.im; linarith [τ.im_pos]
    let r : ℝ := Real.exp (-2 * Real.pi * δ)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    let G : ℕ → ℂ → ℂ := fun m w => c m • Function.Periodic.qParam (1 : ℝ) w ^ m
    have hG_diff : ∀ m : ℕ, DifferentiableOn ℂ (G m) U := fun m => by
      refine Differentiable.differentiableOn ?_
      dsimp only [G, Function.Periodic.qParam]
      fun_prop
    have hG_bound : ∀ m : ℕ, ∀ w ∈ U, ‖G m w‖ ≤ C * (((m : ℝ) + 1) ^ d) * r ^ m := by
      intro m w hw
      have hw' : δ < w.im := hw
      dsimp only [G]
      rw [smul_eq_mul, norm_mul, norm_pow, norm_qParam_one]
      have hq_le : Real.exp (-2 * Real.pi * w.im) ≤ r :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      exact mul_le_mul (hc_bound m) (pow_le_pow_left₀ (Real.exp_pos _).le hq_le m)
        (pow_nonneg (Real.exp_pos _).le m) (by positivity)
    have hsum_deriv := Complex.hasSum_deriv_of_summable_norm
      (summable_C_mul_succ_pow_geom hC d hr0 hr1) hG_diff hU_open hG_bound hτU
    have heq_on : (F ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) =ᶠ[nhds (τ : ℂ)]
        fun w => ∑' m : ℕ, G m w := by
      filter_upwards [hU_open.mem_nhds hτU] with w hw
      have hw_pos : 0 < w.im := lt_trans hδ hw
      have hof : UpperHalfPlane.ofComplex w = ⟨w, hw_pos⟩ :=
        UpperHalfPlane.ofComplex_apply_of_im_pos hw_pos
      simp only [Function.comp_apply, hof]
      exact (hF ⟨w, hw_pos⟩).tsum_eq.symm
    have hderiv_eq : deriv (F ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (τ : ℂ) =
        deriv (fun w => ∑' m : ℕ, G m w) (τ : ℂ) := heq_on.deriv_eq
    have hterm_deriv : ∀ m : ℕ, deriv (G m) (τ : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((m : ℂ) * c m) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) := by
      intro m
      have hGm_eq : G m = fun w => c m * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * w) := by
        funext w
        dsimp only [G, Function.Periodic.qParam]
        rw [smul_eq_mul, ← Complex.exp_nat_mul]
        congr 2
        simp only [Complex.ofReal_one, div_one]
        ring
      rw [hGm_eq]
      have h1 : HasDerivAt (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * w)
          (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) (τ : ℂ) := by
        simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
      have h2 := (h1.cexp).const_mul (c m)
      rw [h2.deriv, smul_eq_mul]
      unfold Function.Periodic.qParam
      rw [← Complex.exp_nat_mul]
      simp only [Complex.ofReal_one, div_one]
      have hexp_eq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ : ℂ)) =
          Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ))) := by
        congr 1; ring
      rw [hexp_eq]
      ring
    have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hscaled := hsum_deriv.mul_left (2 * (Real.pi : ℂ) * Complex.I)⁻¹
    rw [← hderiv_eq] at hscaled
    change HasSum _ (Derivative.normalizedDerivOfComplex F τ) at hscaled
    refine hscaled.congr_fun fun m => ?_
    rw [hterm_deriv m, ← mul_assoc, inv_mul_cancel₀ h2piI, one_mul]
  refine ⟨hhas, ?_⟩
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  let r₀ : ℝ := Real.exp (-2 * Real.pi)
  have hr₀0 : 0 ≤ r₀ := (Real.exp_pos _).le
  have hr₀1 : r₀ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hsum_r₀ : Summable (fun m : ℕ => C * (((m : ℝ) + 1) ^ (d + 1)) * r₀ ^ m) :=
    summable_C_mul_succ_pow_geom hC (d + 1) hr₀0 hr₀1
  refine ⟨∑' m : ℕ, C * (((m : ℝ) + 1) ^ (d + 1)) * r₀ ^ m, 1, fun τ hτ => ?_⟩
  have hbound_term : ∀ m : ℕ,
      ‖((m : ℂ) * c m) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m‖ ≤
        C * (((m : ℝ) + 1) ^ (d + 1)) * r₀ ^ m := by
    intro m
    rw [smul_eq_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_qParam_one]
    have hq_le : Real.exp (-2 * Real.pi * τ.im) ≤ r₀ :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hm_le : (m : ℝ) * ‖c m‖ ≤ C * (((m : ℝ) + 1) ^ (d + 1)) := by
      calc (m : ℝ) * ‖c m‖
          ≤ ((m : ℝ) + 1) * (C * (((m : ℝ) + 1) ^ d)) :=
            mul_le_mul (by linarith) (hc_bound m) (norm_nonneg _) (by positivity)
        _ = C * (((m : ℝ) + 1) ^ (d + 1)) := by rw [pow_succ']; ring
    exact mul_le_mul hm_le (pow_le_pow_left₀ (Real.exp_pos _).le hq_le m)
      (pow_nonneg (Real.exp_pos _).le m) (by positivity)
  have hnorm_sum : Summable (fun m : ℕ =>
      ‖((m : ℂ) * c m) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound_term hsum_r₀
  rw [← (hhas τ).tsum_eq]
  exact (norm_tsum_le_tsum_norm hnorm_sum).trans
    (Summable.tsum_le_tsum hbound_term hnorm_sum hsum_r₀)

private lemma isBoundedAtImInfty_add {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (hg : UpperHalfPlane.IsBoundedAtImInfty g) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ => f τ + g τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf hg ⊢
  obtain ⟨M₁, A₁, h₁⟩ := hf
  obtain ⟨M₂, A₂, h₂⟩ := hg
  refine ⟨M₁ + M₂, max A₁ A₂, fun τ hτ => ?_⟩
  exact (norm_add_le _ _).trans
    (add_le_add (h₁ τ ((le_max_left A₁ A₂).trans hτ)) (h₂ τ ((le_max_right A₁ A₂).trans hτ)))

private lemma isBoundedAtImInfty_sub {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (hg : UpperHalfPlane.IsBoundedAtImInfty g) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ => f τ - g τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf hg ⊢
  obtain ⟨M₁, A₁, h₁⟩ := hf
  obtain ⟨M₂, A₂, h₂⟩ := hg
  refine ⟨M₁ + M₂, max A₁ A₂, fun τ hτ => ?_⟩
  exact (norm_sub_le _ _).trans
    (add_le_add (h₁ τ ((le_max_left A₁ A₂).trans hτ)) (h₂ τ ((le_max_right A₁ A₂).trans hτ)))

private lemma isBoundedAtImInfty_mul {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (hg : UpperHalfPlane.IsBoundedAtImInfty g) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ => f τ * g τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf hg ⊢
  obtain ⟨M₁, A₁, h₁⟩ := hf
  obtain ⟨M₂, A₂, h₂⟩ := hg
  refine ⟨max M₁ 0 * max M₂ 0, max A₁ A₂, fun τ hτ => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((h₁ τ ((le_max_left A₁ A₂).trans hτ)).trans (le_max_left _ _))
    ((h₂ τ ((le_max_right A₁ A₂).trans hτ)).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private lemma isBoundedAtImInfty_const_mul (c : ℂ) {f : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ => c * f τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf ⊢
  obtain ⟨M, A, h⟩ := hf
  refine ⟨‖c‖ * M, A, fun τ hτ => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h τ hτ) (norm_nonneg c)

/-- Helper: Cauchy product of two absolutely convergent `q`-series on `UpperHalfPlane`. -/
private lemma hasSum_qSeries_mul {f g : UpperHalfPlane → ℂ} {a b : ℕ → ℂ} {Ca Cb : ℝ}
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (da db : ℕ)
    (ha_b : ∀ m, ‖a m‖ ≤ Ca * (((m : ℝ) + 1) ^ da))
    (hb_b : ∀ m, ‖b m‖ ≤ Cb * (((m : ℝ) + 1) ^ db))
    (hf : ∀ τ : UpperHalfPlane, HasSum (fun m => a m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) (f τ))
    (hg : ∀ τ : UpperHalfPlane, HasSum (fun m => b m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) (g τ))
    (τ : UpperHalfPlane) :
    HasSum (fun m => (∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) •
        Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      (f τ * g τ) := by
  let q := Function.Periodic.qParam (1 : ℝ) (τ : ℂ)
  have hq_lt : ‖q‖ < 1 := by
    rw [norm_qParam_one]
    have him : 0 < (τ : ℂ).im := τ.im_pos
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, him])
  have hsum_a : Summable (fun m => ‖a m • q ^ m‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_C_mul_succ_pow_geom hCa da (norm_nonneg q) hq_lt)
    rw [smul_eq_mul, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (ha_b m) (pow_nonneg (norm_nonneg q) m)
  have hsum_b : Summable (fun m => ‖b m • q ^ m‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_C_mul_succ_pow_geom hCb db (norm_nonneg q) hq_lt)
    rw [smul_eq_mul, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hb_b m) (pow_nonneg (norm_nonneg q) m)
  have hprod_norm : Summable (fun p : ℕ × ℕ => ‖(a p.1 • q ^ p.1) * (b p.2 • q ^ p.2)‖) := by
    refine (Summable.mul_of_nonneg hsum_a hsum_b (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr ?_
    intro p; exact (norm_mul _ _).symm
  have hprod_sum : HasSum (fun p : ℕ × ℕ => (a p.1 • q ^ p.1) * (b p.2 • q ^ p.2)) (f τ * g τ) := by
    have hts := hsum_a.of_norm.tsum_mul_tsum hsum_b.of_norm hprod_norm.of_norm
    rw [(hf τ).tsum_eq, (hg τ).tsum_eq] at hts
    rw [hts]
    exact hprod_norm.of_norm.hasSum
  let e : (Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}) ≃ (ℕ × ℕ) :=
    { toFun := fun x => x.2.1
      invFun := fun p => ⟨p.1 + p.2, ⟨p, Finset.mem_antidiagonal.mpr rfl⟩⟩
      left_inv := fun ⟨m, ⟨p, hp⟩⟩ => by
        have hm : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
        subst hm; rfl
      right_inv := fun _ => rfl }
  have hsig : HasSum
      (fun x : Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
        (a x.2.1.1 • q ^ x.2.1.1) * (b x.2.1.2 • q ^ x.2.1.2))
      (f τ * g τ) :=
    (e.hasSum_iff).mpr hprod_sum
  have hinner : ∀ m : ℕ,
      HasSum (fun p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
          (a p.1.1 • q ^ p.1.1) * (b p.1.2 • q ^ p.1.2))
        ((∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) • q ^ m) := by
    intro m
    have hfin := hasSum_fintype (fun p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      (a p.1.1 • q ^ p.1.1) * (b p.1.2 • q ^ p.1.2))
    have heq : (∑ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m},
        (a p.1.1 • q ^ p.1.1) * (b p.1.2 • q ^ p.1.2)) =
        (∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) • q ^ m := by
      rw [Finset.univ_eq_attach, Finset.sum_attach (Finset.antidiagonal m)
        (fun p => (a p.1 • q ^ p.1) * (b p.2 • q ^ p.2)), smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [smul_eq_mul, smul_eq_mul, ← (Finset.mem_antidiagonal.mp hp), pow_add]
      ring
    rwa [heq] at hfin
  exact hsig.sigma hinner

/-- Helper: `HasSum` for `E₂` with `qParam 1`. -/
private lemma hasSum_E2_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      ((PowerSeries.coeff m E2SeriesZ : ℤ) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      (EisensteinSeries.E2 τ) := by
  have h := EisensteinSeries.hasSum_qExpansion_E2 τ
  refine h.congr_fun fun m => ?_
  have hq : Function.Periodic.qParam (1 : ℝ) (τ : ℂ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) := by
    unfold Function.Periodic.qParam; simp
  rw [hq]
  congr 1
  unfold E2SeriesZ
  rw [map_sub, coeff_ofNat_mul, PowerSeries.coeff_one, sigma1SeriesZ, PowerSeries.coeff_mk]
  split_ifs <;> push_cast <;> ring

private lemma E2SeriesZ_coeff_bound (m : ℕ) :
    ‖((PowerSeries.coeff m E2SeriesZ : ℤ) : ℂ)‖ ≤ 25 * (((m : ℝ) + 1) ^ 2) := by
  unfold E2SeriesZ
  rw [map_sub, coeff_ofNat_mul, PowerSeries.coeff_one, sigma1SeriesZ, PowerSeries.coeff_mk]
  split_ifs with hm
  · subst hm; norm_num
  · simp only [zero_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    have hs : (ArithmeticFunction.sigma 1 m : ℝ) ≤ (m : ℝ) ^ 2 := by
      exact_mod_cast sigma_le_pow_succ 1 m
    have hpow : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) 2
    nlinarith

/-- Helper: `HasSum` for `E₄` with `qParam 1`. -/
private lemma hasSum_E4_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      ((PowerSeries.coeff m E4SeriesZ : ℤ) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      (E4 τ) := by
  have h := ModularForm.hasSum_qExpansion ModularForm.E₄ zero_lt_one one_mem_strictPeriods_SL τ
  rw [← E4_eq_coe] at h
  refine h.congr_fun fun m => ?_
  rw [smul_eq_mul]
  congr 1
  unfold E4SeriesZ
  rw [← map_intCast_E4_series, PowerSeries.coeff_map]
  rfl

private lemma E4SeriesZ_coeff_bound (m : ℕ) :
    ‖((PowerSeries.coeff m E4SeriesZ : ℤ) : ℂ)‖ ≤ 241 * (((m : ℝ) + 1) ^ 4) := by
  unfold E4SeriesZ
  rw [map_add, coeff_ofNat_mul, PowerSeries.coeff_one, sigma3SeriesZ, PowerSeries.coeff_mk]
  split_ifs with hm
  · subst hm; norm_num
  · simp only [zero_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    have hs : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
      exact_mod_cast sigma_le_pow_succ 3 m
    have hpow : (m : ℝ) ^ 4 ≤ ((m : ℝ) + 1) ^ 4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) 4
    nlinarith

private lemma map_intCast_E6_series :
    PowerSeries.map (Int.castRingHom ℂ) E6SeriesZ = UpperHalfPlane.qExpansion 1 E6 := by
  ext n
  rw [PowerSeries.coeff_map, E6_qExpansion_coeff]
  unfold E6SeriesZ
  rw [map_sub, coeff_ofNat_mul, PowerSeries.coeff_one, sigma5SeriesZ, PowerSeries.coeff_mk]
  split_ifs <;> simp

/-- Helper: `HasSum` for `E₆` with `qParam 1`. -/
private lemma hasSum_E6_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      ((PowerSeries.coeff m E6SeriesZ : ℤ) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      (E6 τ) := by
  have h := ModularForm.hasSum_qExpansion ModularForm.E₆ zero_lt_one one_mem_strictPeriods_SL τ
  rw [← E6_eq_coe] at h
  refine h.congr_fun fun m => ?_
  rw [smul_eq_mul]
  congr 1
  rw [← map_intCast_E6_series, PowerSeries.coeff_map]
  rfl

private lemma E6SeriesZ_coeff_bound (m : ℕ) :
    ‖((PowerSeries.coeff m E6SeriesZ : ℤ) : ℂ)‖ ≤ 505 * (((m : ℝ) + 1) ^ 6) := by
  unfold E6SeriesZ
  rw [map_sub, coeff_ofNat_mul, PowerSeries.coeff_one, sigma5SeriesZ, PowerSeries.coeff_mk]
  split_ifs with hm
  · subst hm; norm_num
  · simp only [zero_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    have hs : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
      exact_mod_cast sigma_le_pow_succ 5 m
    have hpow : (m : ℝ) ^ 6 ≤ ((m : ℝ) + 1) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) 6
    nlinarith

/-- Helper: `serreDerivative 4 E₄` packaged as a weight-6 `SL₂(ℤ)` modular form. -/
private def serreDerivE4ModularForm : ModularForm SL2ZRange 6 where
  toFun := Derivative.serreDerivative (4 : ℂ) E4
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    have hinv : SlashAction.map (4 : ℤ) γ E4 = E4 := by
      rw [ModularForm.SL_slash]
      exact E4_slash_SL2Z_invariant γ
    have hs := Derivative.serreDerivative_slash_invariant mdifferentiable_E4 hinv
    have hs6 : SlashAction.map (6 : ℤ) γ (Derivative.serreDerivative (4 : ℂ) E4) =
        Derivative.serreDerivative (4 : ℂ) E4 := by
      simpa using hs
    rw [ModularForm.SL_slash] at hs6
    exact hs6
  holo' := Derivative.serreDerivative_mdifferentiable 4 mdifferentiable_E4
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map (4 : ℤ) γ E4 = E4 := by
      rw [ModularForm.SL_slash]
      exact E4_slash_SL2Z_invariant γ
    have hs := Derivative.serreDerivative_slash_invariant mdifferentiable_E4 hinv
    have hs6 : SlashAction.map (6 : ℤ) γ (Derivative.serreDerivative (4 : ℂ) E4) =
        Derivative.serreDerivative (4 : ℂ) E4 := by
      simpa using hs
    rw [hs6, Derivative.serreDerivative_eq]
    have hbd_d := (normalizedDerivOfComplex_hasSum_and_bounded (by norm_num) 4
      E4SeriesZ_coeff_bound hasSum_E4_qParam).2
    refine isBoundedAtImInfty_sub hbd_d ?_
    have hrew : (fun z => (4 : ℂ) * (12 : ℂ)⁻¹ * EisensteinSeries.E2 z * E4 z) =
        fun z => ((4 : ℂ) * (12 : ℂ)⁻¹) * (EisensteinSeries.E2 z * E4 z) := by
      funext z; ring
    rw [hrew]
    exact isBoundedAtImInfty_const_mul _
      (isBoundedAtImInfty_mul EisensteinSeries.isBoundedAtImInfty_E2 isBoundedAtImInfty_E4)

/-- **RAMANUJAN'S SECOND DIFFERENTIAL EQUATION (`3 θ E₄ = E₂ E₄ - E₆`)** in `ℤ⟦q⟧`! -/
theorem ramanujan_ode_E4 :
    3 * thetaOp E4SeriesZ = E2SeriesZ * E4SeriesZ - E6SeriesZ := by
  have hhas_d := (normalizedDerivOfComplex_hasSum_and_bounded (by norm_num) 4
    E4SeriesZ_coeff_bound hasSum_E4_qParam).1
  have hhas_serre : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ =>
        (((PowerSeries.coeff m (thetaOp E4SeriesZ) : ℤ) : ℂ) -
          (1 / 3 : ℂ) * ((PowerSeries.coeff m (E2SeriesZ * E4SeriesZ) : ℤ) : ℂ)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
        (serreDerivE4ModularForm τ) := by
    intro τ
    have hprod := hasSum_qSeries_mul (by norm_num) (by norm_num) 2 4
      E2SeriesZ_coeff_bound E4SeriesZ_coeff_bound hasSum_E2_qParam hasSum_E4_qParam τ
    have hscaled := hprod.mul_left ((4 : ℂ) * (12 : ℂ)⁻¹)
    have hsub := (hhas_d τ).sub hscaled
    have hval : Derivative.normalizedDerivOfComplex E4 τ -
        (4 : ℂ) * (12 : ℂ)⁻¹ * (EisensteinSeries.E2 τ * E4 τ) =
        serreDerivE4ModularForm τ := by
      change _ = Derivative.serreDerivative (4 : ℂ) E4 τ
      rw [Derivative.serreDerivative_eq]
      ring
    rw [hval] at hsub
    refine hsub.congr_fun fun m => ?_
    simp only [smul_eq_mul, coeff_thetaOp, PowerSeries.coeff_mul, Int.cast_mul, Int.cast_natCast,
      Int.cast_sum]
    ring
  have hcoeff : ∀ m : ℕ,
      PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (serreDerivE4ModularForm : UpperHalfPlane → ℂ)) =
        ((PowerSeries.coeff m (thetaOp E4SeriesZ) : ℤ) : ℂ) -
          (1 / 3 : ℂ) * ((PowerSeries.coeff m (E2SeriesZ * E4SeriesZ) : ℤ) : ℂ) := fun m =>
    (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
      (f := serreDerivE4ModularForm) hhas_serre m).symm
  have h0 : PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 (serreDerivE4ModularForm : UpperHalfPlane → ℂ)) = -(1 / 3 : ℂ) := by
    rw [hcoeff 0, coeff_thetaOp, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    have hE20 : PowerSeries.coeff 0 E2SeriesZ = 1 := by
      simp [E2SeriesZ, sigma1SeriesZ]
    have hE40 : PowerSeries.coeff 0 E4SeriesZ = 1 := by
      simp [E4SeriesZ, sigma3SeriesZ]
    rw [hE20, hE40]
    norm_num
  have hmod := modularForm_SL2Z_weight_six_eq_smul_E6 serreDerivE4ModularForm
  rw [h0] at hmod
  ext m
  have hm := congrArg (fun g : ModularForm SL2ZRange 6 =>
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ))) hmod
  rw [hcoeff m, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL (-(1 / 3 : ℂ)) ModularForm.E₆,
    map_smul, smul_eq_mul, ← E6_eq_coe, ← map_intCast_E6_series, PowerSeries.coeff_map] at hm
  have hC : ((PowerSeries.coeff m (3 * thetaOp E4SeriesZ) : ℤ) : ℂ) =
      ((PowerSeries.coeff m (E2SeriesZ * E4SeriesZ - E6SeriesZ) : ℤ) : ℂ) := by
    rw [coeff_ofNat_mul, map_sub]
    push_cast
    change _ = -(1 / 3 : ℂ) * ((PowerSeries.coeff m E6SeriesZ : ℤ) : ℂ) at hm
    linear_combination 3 * hm
  exact Int.cast_injective hC

/-- Helper: `serreDerivative 6 E₆` packaged as a weight-8 `SL₂(ℤ)` modular form. -/
private def serreDerivE6ModularForm : ModularForm SL2ZRange 8 where
  toFun := Derivative.serreDerivative (6 : ℂ) E6
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    have hinv : SlashAction.map (6 : ℤ) γ E6 = E6 := by
      rw [ModularForm.SL_slash]
      exact E6_slash_SL2Z_invariant γ
    have hs := Derivative.serreDerivative_slash_invariant mdifferentiable_E6 hinv
    have hs8 : SlashAction.map (8 : ℤ) γ (Derivative.serreDerivative (6 : ℂ) E6) =
        Derivative.serreDerivative (6 : ℂ) E6 := by
      simpa using hs
    rw [ModularForm.SL_slash] at hs8
    exact hs8
  holo' := Derivative.serreDerivative_mdifferentiable 6 mdifferentiable_E6
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map (6 : ℤ) γ E6 = E6 := by
      rw [ModularForm.SL_slash]
      exact E6_slash_SL2Z_invariant γ
    have hs := Derivative.serreDerivative_slash_invariant mdifferentiable_E6 hinv
    have hs8 : SlashAction.map (8 : ℤ) γ (Derivative.serreDerivative (6 : ℂ) E6) =
        Derivative.serreDerivative (6 : ℂ) E6 := by
      simpa using hs
    rw [hs8, Derivative.serreDerivative_eq]
    have hbd_d := (normalizedDerivOfComplex_hasSum_and_bounded (by norm_num) 6
      E6SeriesZ_coeff_bound hasSum_E6_qParam).2
    refine isBoundedAtImInfty_sub hbd_d ?_
    have hrew : (fun z => (6 : ℂ) * (12 : ℂ)⁻¹ * EisensteinSeries.E2 z * E6 z) =
        fun z => ((6 : ℂ) * (12 : ℂ)⁻¹) * (EisensteinSeries.E2 z * E6 z) := by
      funext z; ring
    rw [hrew]
    exact isBoundedAtImInfty_const_mul _
      (isBoundedAtImInfty_mul EisensteinSeries.isBoundedAtImInfty_E2 isBoundedAtImInfty_E6)

/-- **RAMANUJAN'S THIRD DIFFERENTIAL EQUATION (`2 θ E₆ = E₂ E₆ - E₄²`)** in `ℤ⟦q⟧`! -/
theorem ramanujan_ode_E6 :
    2 * thetaOp E6SeriesZ = E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2 := by
  have hhas_d := (normalizedDerivOfComplex_hasSum_and_bounded (by norm_num) 6
    E6SeriesZ_coeff_bound hasSum_E6_qParam).1
  have hhas_serre : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ =>
        (((PowerSeries.coeff m (thetaOp E6SeriesZ) : ℤ) : ℂ) -
          (1 / 2 : ℂ) * ((PowerSeries.coeff m (E2SeriesZ * E6SeriesZ) : ℤ) : ℂ)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
        (serreDerivE6ModularForm τ) := by
    intro τ
    have hprod := hasSum_qSeries_mul (by norm_num) (by norm_num) 2 6
      E2SeriesZ_coeff_bound E6SeriesZ_coeff_bound hasSum_E2_qParam hasSum_E6_qParam τ
    have hscaled := hprod.mul_left ((6 : ℂ) * (12 : ℂ)⁻¹)
    have hsub := (hhas_d τ).sub hscaled
    have hval : Derivative.normalizedDerivOfComplex E6 τ -
        (6 : ℂ) * (12 : ℂ)⁻¹ * (EisensteinSeries.E2 τ * E6 τ) =
        serreDerivE6ModularForm τ := by
      change _ = Derivative.serreDerivative (6 : ℂ) E6 τ
      rw [Derivative.serreDerivative_eq]
      ring
    rw [hval] at hsub
    refine hsub.congr_fun fun m => ?_
    simp only [smul_eq_mul, coeff_thetaOp, PowerSeries.coeff_mul, Int.cast_mul, Int.cast_natCast,
      Int.cast_sum]
    ring
  have hcoeff : ∀ m : ℕ,
      PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (serreDerivE6ModularForm : UpperHalfPlane → ℂ)) =
        ((PowerSeries.coeff m (thetaOp E6SeriesZ) : ℤ) : ℂ) -
          (1 / 2 : ℂ) * ((PowerSeries.coeff m (E2SeriesZ * E6SeriesZ) : ℤ) : ℂ) := fun m =>
    (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
      (f := serreDerivE6ModularForm) hhas_serre m).symm
  have h0 : PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 (serreDerivE6ModularForm : UpperHalfPlane → ℂ)) = -(1 / 2 : ℂ) := by
    rw [hcoeff 0, coeff_thetaOp, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    have hE20 : PowerSeries.coeff 0 E2SeriesZ = 1 := by
      simp [E2SeriesZ, sigma1SeriesZ]
    have hE60 : PowerSeries.coeff 0 E6SeriesZ = 1 := by
      simp [E6SeriesZ, sigma5SeriesZ]
    rw [hE20, hE60]
    norm_num
  have hmod := modularForm_SL2Z_weight_eight_eq_smul_E8 serreDerivE6ModularForm
  rw [h0] at hmod
  have hE8_q : UpperHalfPlane.qExpansion 1 (ModularForm.E (k := 8) (by norm_num) : UpperHalfPlane → ℂ) =
      PowerSeries.map (Int.castRingHom ℂ) (E4SeriesZ ^ 2) := by
    have hfun : (ModularForm.E (k := 8) (by norm_num) : UpperHalfPlane → ℂ) =
        (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
      funext τ
      rw [← E8Eisenstein_eq_modularForm_E8 τ, ← E4_sq_eq_E8Eisenstein τ, sq, E4_eq_modularForm_E4 τ]
      rfl
    rw [hfun, ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL ModularForm.E₄ ModularForm.E₄,
      ← E4_eq_coe, map_pow, sq, E4SeriesZ, map_intCast_E4_series]
  ext m
  have hm := congrArg (fun g : ModularForm SL2ZRange 8 =>
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ))) hmod
  rw [hcoeff m, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL (-(1 / 2 : ℂ))
      (ModularForm.E (k := 8) (by norm_num)),
    map_smul, smul_eq_mul, hE8_q, PowerSeries.coeff_map] at hm
  have hC : ((PowerSeries.coeff m (2 * thetaOp E6SeriesZ) : ℤ) : ℂ) =
      ((PowerSeries.coeff m (E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2) : ℤ) : ℂ) := by
    rw [coeff_ofNat_mul, map_sub]
    push_cast
    change _ = -(1 / 2 : ℂ) * ((PowerSeries.coeff m (E4SeriesZ ^ 2) : ℤ) : ℂ) at hm
    linear_combination 2 * hm
  exact Int.cast_injective hC

/-- Helper: `normalizedDerivOfComplex` of the `E₂` cocycle term
`u_γ(z) = (2 π i)⁻¹ * (c / (c z + d))` satisfies `θ(u_γ) = -u_γ²`. -/
private lemma normalizedDerivOfComplex_cocycle (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex
        (fun z : UpperHalfPlane =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ((γ 1 0 : ℂ) / UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ))) τ =
      -((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((γ 1 0 : ℂ) / UpperHalfPlane.denom (sl2ZToGL2R γ) (τ : ℂ))) ^ 2 := by
  let c : ℂ := (γ 1 0 : ℂ)
  let d : ℂ := (γ 1 1 : ℂ)
  let κ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  have hdenom_eq : ∀ z : UpperHalfPlane, UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ) = c * (z : ℂ) + d := by
    intro z
    simp [UpperHalfPlane.denom, sl2ZToGL2R, c, d]
  have hdenom_ne : c * (τ : ℂ) + d ≠ 0 := by
    rw [← hdenom_eq τ]
    exact UpperHalfPlane.denom_ne_zero (sl2ZToGL2R γ) τ
  have hev : (fun w : ℂ =>
      κ * (c / UpperHalfPlane.denom (sl2ZToGL2R γ) ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)))
      =ᶠ[nhds (τ : ℂ)] fun w : ℂ => κ * (c / (c * w + d)) := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds τ.im_pos] with w hw
    have hof : UpperHalfPlane.ofComplex w = ⟨w, hw⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hw
    rw [hof, hdenom_eq ⟨w, hw⟩]
  have hderiv_lin : HasDerivAt (fun w : ℂ => c * w + d) c (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
  have hderiv_inv : HasDerivAt (fun w : ℂ => (c * w + d)⁻¹) (-c / (c * (τ : ℂ) + d) ^ 2) (τ : ℂ) :=
    hderiv_lin.inv hdenom_ne
  have hderiv_full : HasDerivAt (fun w : ℂ => κ * (c / (c * w + d)))
      (κ * (c * (-c / (c * (τ : ℂ) + d) ^ 2))) (τ : ℂ) := by
    have hrew : (fun w : ℂ => κ * (c / (c * w + d))) = fun w : ℂ => κ * (c * (c * w + d)⁻¹) := by
      funext w; rw [div_eq_mul_inv]
    rw [hrew]
    exact (hderiv_inv.const_mul c).const_mul κ
  unfold Derivative.normalizedDerivOfComplex
  change κ * deriv (fun w : ℂ =>
    κ * (c / UpperHalfPlane.denom (sl2ZToGL2R γ) ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ))) (τ : ℂ) = _
  rw [hev.deriv_eq, hderiv_full.deriv, hdenom_eq τ]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp only [κ, c, d]
  field_simp [hdenom_ne, hpi, Complex.I_ne_zero]

/-- **Weight-4 `SL₂(ℤ)` Slash-Invariance of `θ E₂ - (1/12) E₂²`**! -/
private theorem ramanujanE2Deriv_slash_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (4 : ℤ) (sl2ZToGL2R γ)
        (fun z => Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z -
          (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2) =
      fun z => Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z -
        (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2 := by
  let u : UpperHalfPlane → ℂ := fun z =>
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((γ 1 0 : ℂ) / UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ))
  have hE2_slash : SlashAction.map (2 : ℤ) γ EisensteinSeries.E2 =
      fun z => EisensteinSeries.E2 z + 12 * u z := by
    have h := EisensteinSeries.E2_slash_action γ
    funext z
    have hz := congrFun h z
    rw [hz]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, EisensteinSeries.D2, riemannZeta_two, u]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hd : UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ) ≠ 0 :=
      UpperHalfPlane.denom_ne_zero (sl2ZToGL2R γ) z
    have hdenom_id :
        UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
          (z : ℂ) = UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ) := rfl
    rw [hdenom_id]
    field_simp [hpi, hI, hd]
    linear_combination -12 * (γ 1 0 : ℂ) * Complex.I_mul_I
  have hdiff_u : MDiff u := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro w hw
    have hdenom_ne : ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ≠ 0 := by
      have h0 := UpperHalfPlane.denom_ne_zero (sl2ZToGL2R γ) ⟨w, hw⟩
      simpa [UpperHalfPlane.denom, sl2ZToGL2R] using h0
    have hev : (u ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) =ᶠ[nhds w]
        fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ((γ 1 0 : ℂ) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))) := by
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds hw] with z hz
      have hof : UpperHalfPlane.ofComplex z = ⟨z, hz⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hz
      simp [Function.comp_apply, hof, u, UpperHalfPlane.denom, sl2ZToGL2R]
    have hd_lin : DifferentiableAt ℂ (fun z : ℂ => (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) w :=
      (differentiableAt_id.const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
    have hd : DifferentiableAt ℂ
        (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ((γ 1 0 : ℂ) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)))) w :=
      ((differentiableAt_const (γ 1 0 : ℂ)).div hd_lin hdenom_ne).const_mul _
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  have hderiv_slash := Derivative.normalizedDerivOfComplex_SL_slash (k := 2) E2_mdifferentiable (γ := γ)
  have hderiv_lhs : Derivative.normalizedDerivOfComplex (SlashAction.map (2 : ℤ) γ EisensteinSeries.E2) =
      fun z => Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z - 12 * u z ^ 2 := by
    rw [hE2_slash]
    have hadd := Derivative.normalizedDerivOfComplex_add EisensteinSeries.E2 ((12 : ℂ) • u)
      E2_mdifferentiable (hdiff_u.const_smul (12 : ℂ))
    have hsmul := Derivative.normalizedDerivOfComplex_smul (12 : ℂ) u hdiff_u
    funext z
    have hz := congrFun hadd z
    have hsz := congrFun hsmul z
    have h12u : (fun w => EisensteinSeries.E2 w + 12 * u w) =
        EisensteinSeries.E2 + (12 : ℂ) • u := by
      funext w; simp [smul_eq_mul]
    rw [h12u, hz, Pi.add_apply, hsz, Pi.smul_apply, smul_eq_mul, normalizedDerivOfComplex_cocycle γ z]
    ring
  have hderiv_E2_slash : ∀ z : UpperHalfPlane,
      SlashAction.map (4 : ℤ) γ (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) z =
        Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z +
          2 * u z * EisensteinSeries.E2 z + 12 * u z ^ 2 := by
    intro z
    have hz := congrFun hderiv_slash z
    rw [hderiv_lhs] at hz
    simp only [Pi.sub_apply] at hz
    have hE2z : SlashAction.map (2 : ℤ) γ EisensteinSeries.E2 z =
        EisensteinSeries.E2 z + 12 * u z := congrFun hE2_slash z
    have h4 : (2 + 2 : ℤ) = 4 := by norm_num
    rw [h4, hE2z] at hz
    have hdenom_id :
        UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
          (z : ℂ) = UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ) := rfl
    have huz : ((2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((γ 1 0 : ℂ) /
          UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
            (z : ℂ)) = 2 * u z := by
      rw [hdenom_id]
      dsimp only [u]
      push_cast
      ring
    rw [huz] at hz
    linear_combination -hz
  funext z
  rw [slash_sl2Z_apply]
  have hE2_sq_slash :
      (EisensteinSeries.E2 (γ • z) ^ 2) * (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(4 : ℤ)) =
        (EisensteinSeries.E2 z + 12 * u z) ^ 2 := by
    have h2 : EisensteinSeries.E2 (γ • z) * (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(2 : ℤ)) =
        EisensteinSeries.E2 z + 12 * u z := by
      have h := congrFun hE2_slash z
      rw [ModularForm.SL_slash] at h
      change SlashAction.map (2 : ℤ) (sl2ZToGL2R γ) EisensteinSeries.E2 z = _ at h
      rwa [slash_sl2Z_apply] at h
    calc EisensteinSeries.E2 (γ • z) ^ 2 * (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(4 : ℤ))
        = (EisensteinSeries.E2 (γ • z) * (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(2 : ℤ))) ^ 2 := by
            rw [mul_pow, ← zpow_natCast (_ ^ (-(2 : ℤ))), ← zpow_mul]
            congr 2
      _ = (EisensteinSeries.E2 z + 12 * u z) ^ 2 := by rw [h2]
  have hd4 : Derivative.normalizedDerivOfComplex EisensteinSeries.E2 (γ • z) *
      (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(4 : ℤ)) =
      Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z +
        2 * u z * EisensteinSeries.E2 z + 12 * u z ^ 2 := by
    have h := hderiv_E2_slash z
    rw [ModularForm.SL_slash] at h
    change SlashAction.map (4 : ℤ) (sl2ZToGL2R γ)
      (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) z = _ at h
    rwa [slash_sl2Z_apply] at h
  calc (Derivative.normalizedDerivOfComplex EisensteinSeries.E2 (γ • z) -
          (1 / 12 : ℂ) * EisensteinSeries.E2 (γ • z) ^ 2) *
          (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(4 : ℤ))
      = Derivative.normalizedDerivOfComplex EisensteinSeries.E2 (γ • z) *
            (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(4 : ℤ)) -
          (1 / 12 : ℂ) * (EisensteinSeries.E2 (γ • z) ^ 2 *
            (UpperHalfPlane.denom (sl2ZToGL2R γ) (z : ℂ)) ^ (-(4 : ℤ))) := by ring
    _ = (Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z +
            2 * u z * EisensteinSeries.E2 z + 12 * u z ^ 2) -
          (1 / 12 : ℂ) * (EisensteinSeries.E2 z + 12 * u z) ^ 2 := by rw [hd4, hE2_sq_slash]
    _ = Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z -
          (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2 := by ring

/-- Helper: `θ E₂ - (1/12) E₂²` packaged as a weight-4 `SL₂(ℤ)` modular form. -/
private def ramanujanE2DerivModularForm : ModularForm SL2ZRange 4 where
  toFun z := Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z -
    (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    simpa [sl2ZToGL2R_eq_mapGL] using ramanujanE2Deriv_slash_invariant γ
  holo' := by
    have h1 := Derivative.normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable
    have h2 : MDiff (fun z => (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2) := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have hE2 := UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
      exact (hE2.pow 2).const_mul (1 / 12 : ℂ)
    exact h1.sub h2
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map (4 : ℤ) γ
        (fun z => Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z -
          (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2) =
        fun z => Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z -
          (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2 := by
      rw [ModularForm.SL_slash]
      exact ramanujanE2Deriv_slash_invariant γ
    rw [hinv]
    have hbd_d := (normalizedDerivOfComplex_hasSum_and_bounded (by norm_num) 2
      E2SeriesZ_coeff_bound hasSum_E2_qParam).2
    refine isBoundedAtImInfty_sub hbd_d ?_
    have hsq : (fun z => (1 / 12 : ℂ) * EisensteinSeries.E2 z ^ 2) =
        fun z => (1 / 12 : ℂ) * (EisensteinSeries.E2 z * EisensteinSeries.E2 z) := by
      funext z; rw [sq]
    rw [hsq]
    exact isBoundedAtImInfty_const_mul _
      (isBoundedAtImInfty_mul EisensteinSeries.isBoundedAtImInfty_E2
        EisensteinSeries.isBoundedAtImInfty_E2)

/-- **RAMANUJAN'S FIRST DIFFERENTIAL EQUATION (`12 θ E₂ = E₂² - E₄`)** in `ℤ⟦q⟧`! -/
theorem ramanujan_ode_E2 :
    12 * thetaOp E2SeriesZ = E2SeriesZ ^ 2 - E4SeriesZ := by
  have hhas_d := (normalizedDerivOfComplex_hasSum_and_bounded (by norm_num) 2
    E2SeriesZ_coeff_bound hasSum_E2_qParam).1
  have hhas_f : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ =>
        (((PowerSeries.coeff m (thetaOp E2SeriesZ) : ℤ) : ℂ) -
          (1 / 12 : ℂ) * ((PowerSeries.coeff m (E2SeriesZ ^ 2) : ℤ) : ℂ)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
        (ramanujanE2DerivModularForm τ) := by
    intro τ
    have hprod := hasSum_qSeries_mul (by norm_num) (by norm_num) 2 2
      E2SeriesZ_coeff_bound E2SeriesZ_coeff_bound hasSum_E2_qParam hasSum_E2_qParam τ
    have hscaled := hprod.mul_left (1 / 12 : ℂ)
    have hsub := (hhas_d τ).sub hscaled
    have hval : Derivative.normalizedDerivOfComplex EisensteinSeries.E2 τ -
        (1 / 12 : ℂ) * (EisensteinSeries.E2 τ * EisensteinSeries.E2 τ) =
        ramanujanE2DerivModularForm τ := by
      change _ = Derivative.normalizedDerivOfComplex EisensteinSeries.E2 τ -
        (1 / 12 : ℂ) * EisensteinSeries.E2 τ ^ 2
      ring
    rw [hval] at hsub
    refine hsub.congr_fun fun m => ?_
    simp only [smul_eq_mul, coeff_thetaOp, sq, PowerSeries.coeff_mul, Int.cast_mul, Int.cast_natCast,
      Int.cast_sum]
    ring
  have hcoeff : ∀ m : ℕ,
      PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (ramanujanE2DerivModularForm : UpperHalfPlane → ℂ)) =
        ((PowerSeries.coeff m (thetaOp E2SeriesZ) : ℤ) : ℂ) -
          (1 / 12 : ℂ) * ((PowerSeries.coeff m (E2SeriesZ ^ 2) : ℤ) : ℂ) := fun m =>
    (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
      (f := ramanujanE2DerivModularForm) hhas_f m).symm
  have h0 : PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 (ramanujanE2DerivModularForm : UpperHalfPlane → ℂ)) = -(1 / 12 : ℂ) := by
    rw [hcoeff 0, coeff_thetaOp, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    have hE20 : PowerSeries.coeff 0 E2SeriesZ = 1 := by
      simp [E2SeriesZ, sigma1SeriesZ]
    rw [hE20]
    norm_num
  have hmod := modularForm_SL2Z_weight_four_eq_smul_E4 ramanujanE2DerivModularForm
  rw [h0] at hmod
  ext m
  have hm := congrArg (fun g : ModularForm SL2ZRange 4 =>
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ))) hmod
  rw [hcoeff m, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL (-(1 / 12 : ℂ)) ModularForm.E₄,
    map_smul, smul_eq_mul, ← E4_eq_coe, ← map_intCast_E4_series, PowerSeries.coeff_map] at hm
  have hC : ((PowerSeries.coeff m (12 * thetaOp E2SeriesZ) : ℤ) : ℂ) =
      ((PowerSeries.coeff m (E2SeriesZ ^ 2 - E4SeriesZ) : ℤ) : ℂ) := by
    rw [coeff_ofNat_mul, map_sub]
    push_cast
    change _ = -(1 / 12 : ℂ) * ((PowerSeries.coeff m E4SeriesZ : ℤ) : ℂ) at hm
    linear_combination 12 * hm
  exact Int.cast_injective hC

/-- **Exact `σ₁` Self-Convolution Identity (from `12 θ E₂ = E₂² - E₄`)**:
`12 * sigma1SeriesZ ^ 2 = 5 * sigma3SeriesZ + sigma1SeriesZ - 6 * thetaOp sigma1SeriesZ` in `ℤ⟦q⟧`. -/
theorem sigma1SeriesZ_sq_identity :
    12 * sigma1SeriesZ ^ 2 =
      5 * sigma3SeriesZ + sigma1SeriesZ - 6 * thetaOp sigma1SeriesZ := by
  have h := ramanujan_ode_E2
  unfold E2SeriesZ E4SeriesZ at h
  rw [thetaOp_sub, thetaOp_one, zero_sub, thetaOp_ofNat_mul] at h
  ext n
  have hn := congrArg (PowerSeries.coeff n) h
  have hmul : PowerSeries.coeff n ((48 : PowerSeries ℤ) * (12 * sigma1SeriesZ ^ 2)) =
      PowerSeries.coeff n ((48 : PowerSeries ℤ) *
        (5 * sigma3SeriesZ + sigma1SeriesZ - 6 * thetaOp sigma1SeriesZ)) := by
    have hring : (48 : PowerSeries ℤ) * (12 * sigma1SeriesZ ^ 2) -
        (48 : PowerSeries ℤ) * (5 * sigma3SeriesZ + sigma1SeriesZ - 6 * thetaOp sigma1SeriesZ) =
        ((1 - 24 * sigma1SeriesZ) ^ 2 - (1 + 240 * sigma3SeriesZ)) -
          12 * -(24 * thetaOp sigma1SeriesZ) := by ring
    have hz := congrArg (PowerSeries.coeff n) hring
    rw [map_sub, map_sub, ← hn, sub_self] at hz
    exact sub_eq_zero.mp hz
  rw [coeff_ofNat_mul 48, coeff_ofNat_mul 48] at hmul
  exact mul_left_cancel₀ (by norm_num : (48 : ℤ) ≠ 0) hmul

/-- **Classical Divisor-Sum Convolution Identity**:
for every `n ≥ 1`,
$$12 \sum_{k=1}^{n-1} \sigma_1(k)\,\sigma_1(n - k) = 5\,\sigma_3(n) + (1 - 6n)\,\sigma_1(n).$$ -/
theorem ramanujan_sigma1_convolution (n : ℕ) (hn : 1 ≤ n) :
    12 * (∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * (ArithmeticFunction.sigma 1 (n - k) : ℤ)) =
      5 * (ArithmeticFunction.sigma 3 n : ℤ) + (1 - 6 * (n : ℤ)) * (ArithmeticFunction.sigma 1 n : ℤ) := by
  have hn0 : n ≠ 0 := by omega
  have h := congrArg (PowerSeries.coeff n) sigma1SeriesZ_sq_identity
  rw [coeff_ofNat_mul, map_sub, map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_thetaOp] at h
  have hsq : PowerSeries.coeff n (sigma1SeriesZ ^ 2) =
      ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * (ArithmeticFunction.sigma 1 (n - k) : ℤ) := by
    rw [sq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a sigma1SeriesZ * PowerSeries.coeff b sigma1SeriesZ) n,
      Finset.sum_range_succ, Nat.sub_self]
    have h0 : PowerSeries.coeff 0 sigma1SeriesZ = 0 := by simp [sigma1SeriesZ]
    rw [h0, mul_zero, add_zero]
    have hrange : Finset.range n = Finset.range ((n - 1) + 1) := by congr 1; omega
    rw [hrange, Finset.sum_range_succ', h0, zero_mul, add_zero]
    refine Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk; exact Finset.mem_Ioo.mpr ⟨Nat.succ_pos k, by have := Finset.mem_range.mp hk; omega⟩
    · intro j hj; exact Finset.mem_range.mpr (by rcases Finset.mem_Ioo.mp hj with ⟨h1, h2⟩; omega)
    · intro k _; exact Nat.add_sub_cancel k 1
    · intro j hj; exact Nat.sub_add_cancel (Finset.mem_Ioo.mp hj).1
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      simp [sigma1SeriesZ, show n - (k + 1) ≠ 0 by omega]
  rw [hsq] at h
  simp only [sigma3SeriesZ, sigma1SeriesZ, PowerSeries.coeff_mk, hn0, ↓reduceIte] at h
  linarith

/-- **EXACT DIFFERENTIAL EQUATION FOR RAMANUJAN'S `Δ`**:
`θ Δ_ℤ = E₂_ℤ · Δ_ℤ` in `ℤ⟦q⟧`! -/
theorem ramanujan_ode_delta :
    thetaOp ramanujanDeltaPowerSeriesZ = E2SeriesZ * ramanujanDeltaPowerSeriesZ := by
  have h1728 : (1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ =
      E4SeriesZ ^ 3 - E6SeriesZ ^ 2 := mul_1728_ramanujanDeltaPowerSeriesZ
  have hth := congrArg thetaOp h1728
  rw [thetaOp_ofNat_mul, thetaOp_sub, thetaOp_cube, thetaOp_sq] at hth
  have hcalc : (1728 : PowerSeries ℤ) * thetaOp ramanujanDeltaPowerSeriesZ =
      (1728 : PowerSeries ℤ) * (E2SeriesZ * ramanujanDeltaPowerSeriesZ) := by
    calc (1728 : PowerSeries ℤ) * thetaOp ramanujanDeltaPowerSeriesZ
        = E4SeriesZ ^ 2 * (3 * thetaOp E4SeriesZ) - E6SeriesZ * (2 * thetaOp E6SeriesZ) := by
            rw [hth]; ring
      _ = E4SeriesZ ^ 2 * (E2SeriesZ * E4SeriesZ - E6SeriesZ) -
            E6SeriesZ * (E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2) := by
            rw [ramanujan_ode_E4, ramanujan_ode_E6]
      _ = E2SeriesZ * (E4SeriesZ ^ 3 - E6SeriesZ ^ 2) := by ring
      _ = E2SeriesZ * ((1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ) := by rw [← h1728]
      _ = (1728 : PowerSeries ℤ) * (E2SeriesZ * ramanujanDeltaPowerSeriesZ) := by ring
  ext n
  have hn := congrArg (PowerSeries.coeff n) hcalc
  rw [coeff_ofNat_mul, coeff_ofNat_mul] at hn
  omega

/-- **Exact `24`-Divisibility Identity (from `θ Δ = E₂ Δ`)**:
for EVERY `n : ℕ`, `24 ∣ (n - 1) * τ(n)`! -/
theorem twentyfour_dvd_pred_mul_ramanujanTau (n : ℕ) :
    (24 : ℤ) ∣ ((n : ℤ) - 1) * ramanujanTau n := by
  have h := congrArg (PowerSeries.coeff n) ramanujan_ode_delta
  rw [coeff_thetaOp] at h
  have hsub : E2SeriesZ * ramanujanDeltaPowerSeriesZ =
      ramanujanDeltaPowerSeriesZ - (24 : PowerSeries ℤ) * (sigma1SeriesZ * ramanujanDeltaPowerSeriesZ) := by
    unfold E2SeriesZ; ring
  rw [hsub, map_sub, coeff_ofNat_mul] at h
  refine ⟨-(PowerSeries.coeff n (sigma1SeriesZ * ramanujanDeltaPowerSeriesZ)), ?_⟩
  unfold ramanujanTau
  linarith

end RamanujanODEs

/-! ## Section 4: UNCONDITIONAL CLASSICAL RAMANUJAN CONGRUENCES MOD `5`, `7`, `36`, `9`, `3` -/

section ClassicalCongruences

/-- **UNCONDITIONAL RAMANUJAN CONGRUENCE MODULO `5` (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$\tau(n) \equiv n \cdot \sigma_1(n) \pmod{5}.$$ -/
theorem ramanujanTau_mod_5 (n : ℕ) :
    ramanujanTau n ≡ (n : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ) [ZMOD 5] := by
  by_cases hn : n = 0
  · subst hn; simp [ramanujanTau_zero]
  · -- Step 1: σ₅(m) ≡ σ₁(m) [ZMOD 5] for all m (by Fermat's Little Theorem d^5 ≡ d mod 5).
    have hB_eq_A1 : ∀ m : ℕ, PowerSeries.coeff m sigma5SeriesZ ≡ PowerSeries.coeff m sigma1SeriesZ [ZMOD 5] := by
      intro m
      simp only [sigma5SeriesZ, sigma1SeriesZ, PowerSeries.coeff_mk]
      split_ifs with hm
      · rfl
      · simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]
        refine int_modEq_sum fun d _ => ?_
        have hnat : d ^ 5 ≡ d [MOD 5] := by
          rw [Nat.ModEq, Nat.pow_mod]
          have hlt : d % 5 < 5 := Nat.mod_lt d (by decide)
          interval_cases (d % 5) <;> decide
        simpa [pow_one] using (Int.natCast_modEq_iff.mpr hnat)
    -- Step 2: coeff n (B^2) ≡ coeff n (A1^2) [ZMOD 5].
    have hB2_eq_A12 : PowerSeries.coeff n (sigma5SeriesZ ^ 2) ≡
        PowerSeries.coeff n (sigma1SeriesZ ^ 2) [ZMOD 5] := by
      rw [sq, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine int_modEq_sum fun p _ => (hB_eq_A1 p.1).mul (hB_eq_A1 p.2)
    -- Step 3: coeff n linearDeltaSeriesZ ≡ coeff n sigma1SeriesZ [ZMOD 5].
    have hC_eq_A1 : PowerSeries.coeff n linearDeltaSeriesZ ≡ PowerSeries.coeff n sigma1SeriesZ [ZMOD 5] := by
      have h12 : 12 * PowerSeries.coeff n linearDeltaSeriesZ =
          5 * PowerSeries.coeff n sigma3SeriesZ + 7 * PowerSeries.coeff n sigma5SeriesZ := by
        simp only [linearDeltaSeriesZ, sigma3SeriesZ, sigma5SeriesZ, PowerSeries.coeff_mk, hn, ↓reduceIte]
        have hdvd := twelve_dvd_five_sigma3_add_seven_sigma5 n
        have hnat := Nat.mul_div_cancel' hdvd
        exact_mod_cast hnat
      have hB := hB_eq_A1 n
      rw [Int.modEq_iff_dvd] at hB ⊢
      obtain ⟨k, hk⟩ := hB
      refine ⟨k + 7 * PowerSeries.coeff n linearDeltaSeriesZ -
          4 * PowerSeries.coeff n sigma5SeriesZ - 3 * PowerSeries.coeff n sigma3SeriesZ, ?_⟩
      linarith
    -- Step 4: Expand ramanujanTau n mod 5 using sigma1SeriesZ_sq_identity.
    have hsq := congrArg (PowerSeries.coeff n) sigma1SeriesZ_sq_identity
    rw [coeff_ofNat_mul, map_sub, map_add, coeff_ofNat_mul, coeff_ofNat_mul,
      coeff_thetaOp] at hsq
    have htau : ramanujanTau n =
        PowerSeries.coeff n linearDeltaSeriesZ +
          100 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) +
          8000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) -
          147 * PowerSeries.coeff n (sigma5SeriesZ ^ 2) := by
      unfold ramanujanTau ramanujanDeltaPowerSeriesZ
      rw [map_sub, map_add, map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_ofNat_mul]
    rw [Int.modEq_iff_dvd] at hB2_eq_A12 hC_eq_A1 ⊢
    obtain ⟨k1, hk1⟩ := hB2_eq_A12
    obtain ⟨k2, hk2⟩ := hC_eq_A1
    have hA1n : PowerSeries.coeff n sigma1SeriesZ = (ArithmeticFunction.sigma 1 n : ℤ) := by
      simp [sigma1SeriesZ, hn]
    rw [hA1n] at hsq hk2
    -- From hsq: 12 A1² = 5 A3 + A1 - 6 n A1
    -- We want 5 ∣ n A1 - τ(n).
    -- Note: τ(n) - n A1 = (C - A1) + 100 A3² + 8000 A3³ - 147 (B² - A1²)
    --   + (A1 - 147 A1² - n A1)
    -- And 12 * (-147) = ... wait: -147 ≡ 3 (mod 5), and 4 * (12 A1² - 5 A3 - A1 + 6 n A1) = 0
    -- => 48 A1² - 20 A3 - 4 A1 + 24 n A1 = 0
    -- => (-147 A1² + A1 - n A1) + 3 * (12 A1² - 5 A3 - A1 + 6 n A1)? No:
    -- 12 * 12 = 144, wait: -147 + 4 * 12 = -99? No: -147 + 12 * 12 = -3;
    -- -147 + 12 * 1 = -135 = -27 * 5!!
    -- CHECK: 1 * (12 A1² - 5 A3 - A1 + 6 n A1) = 0!
    -- Add to (A1 - 147 A1² - n A1):
    -- (-147 + 12) A1² + (1 - 1) A1 + (-1 + 6) n A1 - 5 A3 = -135 A1² + 5 n A1 - 5 A3
    -- = 5 * (-27 A1² + n A1 - A3)!!
    -- AMAZING!
    refine ⟨k2 - 20 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) -
        1600 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) - 147 * k1 +
        27 * PowerSeries.coeff n (sigma1SeriesZ ^ 2) -
        (n : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ) +
        PowerSeries.coeff n sigma3SeriesZ, ?_⟩
    linarith

/-- Immediate corollary of `ramanujanTau_mod_5`: `5 ∣ τ(5 k)` for every `k : ℕ`. -/
theorem five_dvd_ramanujanTau_five_mul (k : ℕ) : (5 : ℤ) ∣ ramanujanTau (5 * k) := by
  have h := ramanujanTau_mod_5 (5 * k)
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨(k : ℤ) * (ArithmeticFunction.sigma 1 (5 * k) : ℤ) - m, ?_⟩
  push_cast at hm
  linarith

/-- **UNCONDITIONAL RAMANUJAN CONGRUENCE MODULO `7` (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$\tau(n) \equiv n \cdot \sigma_3(n) \pmod{7}.$$ -/
theorem ramanujanTau_mod_7 (n : ℕ) :
    ramanujanTau n ≡ (n : ℤ) * (ArithmeticFunction.sigma 3 n : ℤ) [ZMOD 7] := by
  by_cases hn : n = 0
  · subst hn; simp [ramanujanTau_zero]
  · -- From E₆ = 1 - 504 B ≡ 1 (mod 7) and 2 θ E₆ = E₂ E₆ - E₄², we get E₂ ≡ E₄² (mod 7).
    have hE6_mod7 : ∀ m : ℕ, PowerSeries.coeff m (E6SeriesZ - 1) ≡ 0 [ZMOD 7] := by
      intro m
      have h : E6SeriesZ - 1 = -((504 : PowerSeries ℤ) * sigma5SeriesZ) := by
        unfold E6SeriesZ; ring
      rw [h, map_neg, coeff_ofNat_mul, Int.modEq_zero_iff_dvd]
      exact ⟨-72 * PowerSeries.coeff m sigma5SeriesZ, by ring⟩
    have hE2_mod7 : ∀ m : ℕ, PowerSeries.coeff m (E2SeriesZ - E4SeriesZ ^ 2) ≡ 0 [ZMOD 7] := by
      intro m
      have hrew : E2SeriesZ - E4SeriesZ ^ 2 =
          2 * thetaOp E6SeriesZ - E2SeriesZ * (E6SeriesZ - 1) := by
        have h := ramanujan_ode_E6
        calc E2SeriesZ - E4SeriesZ ^ 2
            = (E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2) - E2SeriesZ * (E6SeriesZ - 1) := by ring
          _ = 2 * thetaOp E6SeriesZ - E2SeriesZ * (E6SeriesZ - 1) := by rw [← h]
      rw [hrew, map_sub, coeff_ofNat_mul, coeff_thetaOp, PowerSeries.coeff_mul]
      have h1 : (2 : ℤ) * ((m : ℤ) * PowerSeries.coeff m E6SeriesZ) ≡ 0 [ZMOD 7] := by
        have hE6' : PowerSeries.coeff m E6SeriesZ =
            PowerSeries.coeff m (1 : PowerSeries ℤ) - 504 * PowerSeries.coeff m sigma5SeriesZ := by
          unfold E6SeriesZ; rw [map_sub, coeff_ofNat_mul]
        rw [hE6', PowerSeries.coeff_one, Int.modEq_zero_iff_dvd]
        split_ifs with hm
        · subst hm; simp
        · exact ⟨-144 * (m : ℤ) * PowerSeries.coeff m sigma5SeriesZ, by ring⟩
      have h2 : (∑ p ∈ Finset.antidiagonal m,
          PowerSeries.coeff p.1 E2SeriesZ * PowerSeries.coeff p.2 (E6SeriesZ - 1)) ≡ 0 [ZMOD 7] := by
        have hz : (0 : ℤ) = ∑ _p ∈ Finset.antidiagonal m, (0 : ℤ) := by simp
        rw [hz]
        refine int_modEq_sum fun p _ => ?_
        simpa using (Int.ModEq.refl (PowerSeries.coeff p.1 E2SeriesZ)).mul (hE6_mod7 p.2)
      simpa using h1.sub h2
    -- Plug E₂ ≡ E₄² (mod 7) and E₆ ≡ 1 (mod 7) into 3 θ E₄ = E₂ E₄ - E₆:
    -- 3 θ E₄ - (E₄³ - 1) = (E₂ - E₄²) E₄ - (E₆ - 1) ≡ 0 (mod 7)!
    have hode4_mod7 : PowerSeries.coeff n (3 * thetaOp E4SeriesZ - (E4SeriesZ ^ 3 - 1)) ≡ 0 [ZMOD 7] := by
      have hrew : 3 * thetaOp E4SeriesZ - (E4SeriesZ ^ 3 - 1) =
          (E2SeriesZ - E4SeriesZ ^ 2) * E4SeriesZ - (E6SeriesZ - 1) := by
        rw [ramanujan_ode_E4]; ring
      rw [hrew, map_sub, PowerSeries.coeff_mul]
      have h1 : (∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff p.1 (E2SeriesZ - E4SeriesZ ^ 2) * PowerSeries.coeff p.2 E4SeriesZ) ≡ 0 [ZMOD 7] := by
        have hz : (0 : ℤ) = ∑ _p ∈ Finset.antidiagonal n, (0 : ℤ) := by simp
        rw [hz]
        refine int_modEq_sum fun p _ => ?_
        simpa using (hE2_mod7 p.1).mul (Int.ModEq.refl (PowerSeries.coeff p.2 E4SeriesZ))
      simpa using h1.sub (hE6_mod7 n)
    -- Expand 3 θ E₄ - (E₄³ - 1) in terms of sigma3SeriesZ (using E4SeriesZ = 1 + 240 A₃):
    -- 3 θ E₄ = 720 θ A₃, E₄³ - 1 = 720 A₃ + 172800 A₃² + 13824000 A₃³.
    have hexpand : 3 * thetaOp E4SeriesZ - (E4SeriesZ ^ 3 - 1) =
        720 * thetaOp sigma3SeriesZ -
          (720 * sigma3SeriesZ + 172800 * sigma3SeriesZ ^ 2 + 13824000 * sigma3SeriesZ ^ 3) := by
      unfold E4SeriesZ
      rw [thetaOp_add, thetaOp_one, zero_add, thetaOp_ofNat_mul]
      ring
    rw [hexpand, map_sub, map_add, map_add, coeff_ofNat_mul, coeff_ofNat_mul,
      coeff_ofNat_mul, coeff_ofNat_mul, coeff_thetaOp,
      Int.modEq_zero_iff_dvd] at hode4_mod7
    obtain ⟨k0, hk0⟩ := hode4_mod7
    -- Also from 12 C = 5 A₃ + 7 B and Δ = C + 100 A₃² + 8000 A₃³ - 147 B²:
    have h12C : 12 * PowerSeries.coeff n linearDeltaSeriesZ =
        5 * PowerSeries.coeff n sigma3SeriesZ + 7 * PowerSeries.coeff n sigma5SeriesZ := by
      simp only [linearDeltaSeriesZ, sigma3SeriesZ, sigma5SeriesZ, PowerSeries.coeff_mk, hn, ↓reduceIte]
      exact_mod_cast Nat.mul_div_cancel' (twelve_dvd_five_sigma3_add_seven_sigma5 n)
    have htau : ramanujanTau n =
        PowerSeries.coeff n linearDeltaSeriesZ +
          100 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) +
          8000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) -
          147 * PowerSeries.coeff n (sigma5SeriesZ ^ 2) := by
      unfold ramanujanTau ramanujanDeltaPowerSeriesZ
      rw [map_sub, map_add, map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_ofNat_mul]
    have hA3n : PowerSeries.coeff n sigma3SeriesZ = (ArithmeticFunction.sigma 3 n : ℤ) := by
      simp [sigma3SeriesZ, hn]
    rw [hA3n] at hk0 h12C
    -- Notice: 720 = 7*103 - 1, 172800 = 7*24686 - 2, 13824000 = 7*1974857 + 1!
    -- So hk0 says: 7 ∣ (-n A₃ + A₃ + 2 A₃² - A₃³)!
    -- And 12 C = 5 A₃ + 7 B => 3*(12 C - 5 A₃ - 7 B) = 0 => C - A₃ = 7*(3 B + 2 A₃ - 5 C)!
    -- Wait: 3*12 = 36 = 35 + 1, 3*5 = 15 = 14 + 1! YES! C - A₃ = 7*(3 B + 2 A₃ - 5 C)!
    -- And τ(n) - (A₃ + 2 A₃² - A₃³) = (C - A₃) + 98 A₃² + 8001 A₃³ - 147 B²
    -- = 7 * (3 B + 2 A₃ - 5 C + 14 A₃² + 1143 A₃³ - 21 B²)!
    rw [Int.modEq_iff_dvd]
    refine ⟨-k0 + 103 * ((n : ℤ) * (ArithmeticFunction.sigma 3 n : ℤ)) -
        105 * (ArithmeticFunction.sigma 3 n : ℤ) -
        24700 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) -
        1976000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) +
        5 * PowerSeries.coeff n linearDeltaSeriesZ -
        3 * PowerSeries.coeff n sigma5SeriesZ +
        21 * PowerSeries.coeff n (sigma5SeriesZ ^ 2), ?_⟩
    linarith

/-- Immediate corollary of `ramanujanTau_mod_7`: `7 ∣ τ(7 k)` for every `k : ℕ`. -/
theorem seven_dvd_ramanujanTau_seven_mul (k : ℕ) : (7 : ℤ) ∣ ramanujanTau (7 * k) := by
  have h := ramanujanTau_mod_7 (7 * k)
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨(k : ℤ) * (ArithmeticFunction.sigma 3 (7 * k) : ℤ) - m, ?_⟩
  push_cast at hm
  linarith

/-- **EXACT UNIVERSAL IDENTITY FOR `Δ_ℤ` IN TERMS OF `E₂` AND `θ A₁, θ² A₁`** (in `ℤ⟦q⟧`!):
$$\Delta_{\mathbb{Z}} = E_2^3 (\theta^2 A_1) + 36 E_2^2 (\theta A_1)^2
  + 432 E_2 (\theta A_1)(\theta^2 A_1) - 432 (\theta^2 A_1)^2 + 13824 (\theta A_1)^3.$$ -/
theorem ramanujanDeltaPowerSeriesZ_eq_theta_sigma1 :
    ramanujanDeltaPowerSeriesZ =
      E2SeriesZ ^ 3 * thetaOp (thetaOp sigma1SeriesZ) +
        36 * E2SeriesZ ^ 2 * thetaOp sigma1SeriesZ ^ 2 +
        432 * E2SeriesZ * thetaOp sigma1SeriesZ * thetaOp (thetaOp sigma1SeriesZ) -
        432 * thetaOp (thetaOp sigma1SeriesZ) ^ 2 +
        13824 * thetaOp sigma1SeriesZ ^ 3 := by
  let X : PowerSeries ℤ := thetaOp E2SeriesZ
  have hX : X = -((24 : PowerSeries ℤ) * thetaOp sigma1SeriesZ) := by
    dsimp only [X]
    unfold E2SeriesZ
    rw [thetaOp_sub, thetaOp_one, zero_sub, thetaOp_ofNat_mul]
  have hthX : thetaOp X = -((24 : PowerSeries ℤ) * thetaOp (thetaOp sigma1SeriesZ)) := by
    rw [hX]
    have hneg : -((24 : PowerSeries ℤ) * thetaOp sigma1SeriesZ) =
        0 - (24 : PowerSeries ℤ) * thetaOp sigma1SeriesZ := by ring
    rw [hneg, thetaOp_sub]
    have h0 : thetaOp (0 : PowerSeries ℤ) = 0 := by ext n; simp [coeff_thetaOp]
    rw [h0, zero_sub, thetaOp_ofNat_mul]
  have hE4 : E4SeriesZ = E2SeriesZ ^ 2 - 12 * X := by
    have h := ramanujan_ode_E2
    change 12 * X = E2SeriesZ ^ 2 - E4SeriesZ at h
    linear_combination h
  have hthE4 : thetaOp E4SeriesZ = 2 * E2SeriesZ * X - 12 * thetaOp X := by
    rw [hE4, thetaOp_sub, thetaOp_sq, thetaOp_ofNat_mul]
  have hE6 : E6SeriesZ = E2SeriesZ ^ 3 - 18 * E2SeriesZ * X + 36 * thetaOp X := by
    have h := ramanujan_ode_E4
    rw [hthE4, hE4] at h
    linear_combination h
  have h1728 : (1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ =
      (1728 : PowerSeries ℤ) *
        (E2SeriesZ ^ 3 * thetaOp (thetaOp sigma1SeriesZ) +
          36 * E2SeriesZ ^ 2 * thetaOp sigma1SeriesZ ^ 2 +
          432 * E2SeriesZ * thetaOp sigma1SeriesZ * thetaOp (thetaOp sigma1SeriesZ) -
          432 * thetaOp (thetaOp sigma1SeriesZ) ^ 2 +
          13824 * thetaOp sigma1SeriesZ ^ 3) := by
    calc (1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ
        = E4SeriesZ ^ 3 - E6SeriesZ ^ 2 := mul_1728_ramanujanDeltaPowerSeriesZ
      _ = (E2SeriesZ ^ 2 - 12 * X) ^ 3 - (E2SeriesZ ^ 3 - 18 * E2SeriesZ * X + 36 * thetaOp X) ^ 2 := by
            rw [hE4, hE6]
      _ = -72 * E2SeriesZ ^ 3 * thetaOp X + 108 * E2SeriesZ ^ 2 * X ^ 2 +
            1296 * E2SeriesZ * X * thetaOp X - 1296 * thetaOp X ^ 2 - 1728 * X ^ 3 := by ring
      _ = (1728 : PowerSeries ℤ) *
            (E2SeriesZ ^ 3 * thetaOp (thetaOp sigma1SeriesZ) +
              36 * E2SeriesZ ^ 2 * thetaOp sigma1SeriesZ ^ 2 +
              432 * E2SeriesZ * thetaOp sigma1SeriesZ * thetaOp (thetaOp sigma1SeriesZ) -
              432 * thetaOp (thetaOp sigma1SeriesZ) ^ 2 +
              13824 * thetaOp sigma1SeriesZ ^ 3) := by
            rw [hthX, hX]; ring
  ext n
  have hn := congrArg (PowerSeries.coeff n) h1728
  rw [coeff_ofNat_mul, coeff_ofNat_mul] at hn
  omega

/-- **UNCONDITIONAL RAMANUJAN CONGRUENCE MODULO `36` (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$\tau(n) \equiv n^2 \cdot \sigma_1(n) \pmod{36}.$$ -/
theorem ramanujanTau_mod_36 (n : ℕ) :
    ramanujanTau n ≡ (n : ℤ) ^ 2 * (ArithmeticFunction.sigma 1 n : ℤ) [ZMOD 36] := by
  by_cases hn : n = 0
  · subst hn; simp [ramanujanTau_zero]
  · -- Write E2SeriesZ^3 = 1 - 72 * P where P = A₁ - 24 A₁² + 192 A₁³.
    let P : PowerSeries ℤ := sigma1SeriesZ - 24 * sigma1SeriesZ ^ 2 + 192 * sigma1SeriesZ ^ 3
    have hE2cube : E2SeriesZ ^ 3 = 1 - (72 : PowerSeries ℤ) * P := by
      unfold E2SeriesZ; dsimp only [P]; ring
    have hrew : ramanujanDeltaPowerSeriesZ =
        thetaOp (thetaOp sigma1SeriesZ) +
          (36 : PowerSeries ℤ) *
            (-(2 * P * thetaOp (thetaOp sigma1SeriesZ)) +
              E2SeriesZ ^ 2 * thetaOp sigma1SeriesZ ^ 2 +
              12 * E2SeriesZ * thetaOp sigma1SeriesZ * thetaOp (thetaOp sigma1SeriesZ) -
              12 * thetaOp (thetaOp sigma1SeriesZ) ^ 2 +
              384 * thetaOp sigma1SeriesZ ^ 3) := by
      rw [ramanujanDeltaPowerSeriesZ_eq_theta_sigma1, hE2cube]
      ring
    have hn' := congrArg (PowerSeries.coeff n) hrew
    rw [map_add, coeff_thetaOp, coeff_thetaOp, coeff_ofNat_mul] at hn'
    have hA1n : PowerSeries.coeff n sigma1SeriesZ = (ArithmeticFunction.sigma 1 n : ℤ) := by
      simp [sigma1SeriesZ, hn]
    rw [hA1n] at hn'
    rw [Int.modEq_iff_dvd]
    refine ⟨-(PowerSeries.coeff n (-(2 * P * thetaOp (thetaOp sigma1SeriesZ)) +
        E2SeriesZ ^ 2 * thetaOp sigma1SeriesZ ^ 2 +
        12 * E2SeriesZ * thetaOp sigma1SeriesZ * thetaOp (thetaOp sigma1SeriesZ) -
        12 * thetaOp (thetaOp sigma1SeriesZ) ^ 2 +
        384 * thetaOp sigma1SeriesZ ^ 3)), ?_⟩
    unfold ramanujanTau
    linarith

/-- **UNCONDITIONAL RAMANUJAN CONGRUENCE MODULO `9`**:
`∀ n : ℕ, ramanujanTau n ≡ n² * σ₁(n) [ZMOD 9]`. -/
theorem ramanujanTau_mod_9 (n : ℕ) :
    ramanujanTau n ≡ (n : ℤ) ^ 2 * (ArithmeticFunction.sigma 1 n : ℤ) [ZMOD 9] :=
  (ramanujanTau_mod_36 n).of_dvd (by decide)

/-- Elementary arithmetic lemma: if `n % 3 = 2`, then `3 ∣ σ₁(n)`. -/
private lemma three_dvd_sigma1_of_mod_three_eq_two {n : ℕ} (hn : n % 3 = 2) :
    3 ∣ ArithmeticFunction.sigma 1 n := by
  have hn0 : n ≠ 0 := by omega
  have h2 : 2 * ArithmeticFunction.sigma 1 n =
      ∑ d ∈ n.divisors, (d + n / d) := by
    rw [ArithmeticFunction.sigma_apply, Finset.sum_add_distrib, two_mul]
    congr 1
    · simp
    · simp only [pow_one]
      refine (Finset.sum_nbij' (fun d => n / d) (fun d => n / d) ?_ ?_ ?_ ?_ ?_).symm
      · intro d hd; exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn0⟩
      · intro d hd; exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn0⟩
      · intro d hd; exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn0
      · intro d hd; exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn0
      · intro _ _; rfl
  have hdvd2 : 3 ∣ 2 * ArithmeticFunction.sigma 1 n := by
    rw [h2]
    refine Finset.dvd_sum fun d hd => ?_
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have hmod : (d % 3 * ((n / d) % 3)) % 3 = 2 := by
      rw [← Nat.mul_mod, hmul, hn]
    have hlt1 : d % 3 < 3 := Nat.mod_lt d (by decide)
    have hlt2 : (n / d) % 3 < 3 := Nat.mod_lt (n / d) (by decide)
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    interval_cases (d % 3) <;> interval_cases ((n / d) % 3) <;> omega
  exact (show Nat.Coprime 3 2 by decide).dvd_of_dvd_mul_left hdvd2

/-- **UNCONDITIONAL RAMANUJAN CONGRUENCE MODULO `3` (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$\tau(n) \equiv n \cdot \sigma_1(n) \pmod{3}.$$ -/
theorem ramanujanTau_mod_3 (n : ℕ) :
    ramanujanTau n ≡ (n : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ) [ZMOD 3] := by
  have h3 := (ramanujanTau_mod_36 n).of_dvd (by decide : (3 : ℤ) ∣ 36)
  refine h3.trans ?_
  rw [Int.modEq_iff_dvd]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  interval_cases hmod : n % 3
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hmod
    refine ⟨(k : ℤ) * (ArithmeticFunction.sigma 1 (3 * k) : ℤ) * (1 - 3 * (k : ℤ)), ?_⟩
    push_cast; ring
  · have h3_dvd : (3 : ℤ) ∣ (n : ℤ) - 1 := by omega
    obtain ⟨k, hk⟩ := h3_dvd
    refine ⟨-(k * (n : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ)), ?_⟩
    have hn1 : (n : ℤ) = 3 * k + 1 := by linarith
    rw [hn1]; ring
  · obtain ⟨k, hk⟩ := three_dvd_sigma1_of_mod_three_eq_two hmod
    refine ⟨((n : ℤ) - (n : ℤ) ^ 2) * (k : ℤ), ?_⟩
    rw [hk]; push_cast; ring

/-- Immediate corollary of `ramanujanTau_mod_3`: `3 ∣ τ(3 k)` for every `k : ℕ`. -/
theorem three_dvd_ramanujanTau_three_mul (k : ℕ) : (3 : ℤ) ∣ ramanujanTau (3 * k) := by
  have h := ramanujanTau_mod_3 (3 * k)
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨(k : ℤ) * (ArithmeticFunction.sigma 1 (3 * k) : ℤ) - m, ?_⟩
  push_cast at hm
  linarith

end ClassicalCongruences

/-! ## Section 5: EXACT PARITY CHARACTERIZATION OF `τ(n)` (`Odd (τ n) ↔ ∃ k, n = (2k + 1)²`) -/

section ParityCharacterization

/-- Elementary arithmetic lemma: for EVERY odd natural number `d`,
`(5 * d^3 + 7 * d^5) / 12` is ODD! -/
private lemma odd_div_twelve_five_cube_add_seven_pow_five {d : ℕ} (hd : Odd d) :
    Odd ((5 * d ^ 3 + 7 * d ^ 5) / 12) := by
  have hmod24 : (5 * d ^ 3 + 7 * d ^ 5) % 24 = 12 := by
    have h1 : (5 * d ^ 3 + 7 * d ^ 5) % 24 =
        (5 * (d % 24) ^ 3 + 7 * (d % 24) ^ 5) % 24 := by
      simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    rw [h1]
    have hodd : (d % 24) % 2 = 1 := by
      have : (d % 24) % 2 = d % 2 := by omega
      rw [this]
      exact Nat.odd_iff.mp hd
    have hlt : d % 24 < 24 := Nat.mod_lt d (by decide)
    interval_cases (d % 24) <;> omega
  rw [Nat.odd_iff]
  omega

/-- For EVERY odd `n : ℕ` and ANY integer power series `φ`, `coeff n (φ ^ 2)` is EVEN! -/
private lemma even_coeff_sq_of_odd (φ : PowerSeries ℤ) {n : ℕ} (hn : Odd n) :
    Even (PowerSeries.coeff n (φ ^ 2)) := by
  rw [sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a φ * PowerSeries.coeff b φ) n]
  rcases hn with ⟨m, rfl⟩
  have hsplit : (∑ k ∈ Finset.range (2 * m + 1 + 1),
      PowerSeries.coeff k φ * PowerSeries.coeff (2 * m + 1 - k) φ) =
      (∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k φ * PowerSeries.coeff (2 * m + 1 - k) φ) +
      (∑ k ∈ Finset.range (m + 1),
        PowerSeries.coeff (m + 1 + k) φ * PowerSeries.coeff (2 * m + 1 - (m + 1 + k)) φ) := by
    have hlen : 2 * m + 1 + 1 = (m + 1) + (m + 1) := by omega
    rw [hlen, Finset.sum_range_add]
  have hsym : (∑ k ∈ Finset.range (m + 1),
      PowerSeries.coeff (m + 1 + k) φ * PowerSeries.coeff (2 * m + 1 - (m + 1 + k)) φ) =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k φ * PowerSeries.coeff (2 * m + 1 - k) φ := by
    refine Finset.sum_nbij' (fun k => m - k) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
    · intro k hk; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
    · intro j hj; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
    · intro k hk; have := Finset.mem_range.mp hk; omega
    · intro j hj; have := Finset.mem_range.mp hj; omega
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      have h1 : 2 * m + 1 - (m + 1 + k) = m - k := by omega
      have h2 : 2 * m + 1 - (m - k) = m + 1 + k := by omega
      rw [h1, h2, mul_comm]
  rw [hsplit, hsym]
  exact ⟨∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k φ * PowerSeries.coeff (2 * m + 1 - k) φ, rfl⟩

/-- For EVERY odd `n : ℕ`, `ramanujanTau n` has the SAME parity as `n.divisors.card`! -/
private lemma ramanujanTau_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    ramanujanTau n ≡ (n.divisors.card : ℤ) [ZMOD 2] := by
  have hn0 : n ≠ 0 := by rcases hn with ⟨m, rfl⟩; omega
  have htau : ramanujanTau n =
      PowerSeries.coeff n linearDeltaSeriesZ +
        100 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) +
        8000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) -
        147 * PowerSeries.coeff n (sigma5SeriesZ ^ 2) := by
    unfold ramanujanTau ramanujanDeltaPowerSeriesZ
    rw [map_sub, map_add, map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_ofNat_mul]
  obtain ⟨r, hr⟩ := even_coeff_sq_of_odd sigma5SeriesZ hn
  have hlin_sum : ((5 * ArithmeticFunction.sigma 3 n + 7 * ArithmeticFunction.sigma 5 n) / 12) =
      ∑ d ∈ n.divisors, (5 * d ^ 3 + 7 * d ^ 5) / 12 := by
    have hmul : 12 * ((5 * ArithmeticFunction.sigma 3 n + 7 * ArithmeticFunction.sigma 5 n) / 12) =
        12 * (∑ d ∈ n.divisors, (5 * d ^ 3 + 7 * d ^ 5) / 12) := by
      rw [Nat.mul_div_cancel' (twelve_dvd_five_sigma3_add_seven_sigma5 n), Finset.mul_sum]
      simp only [ArithmeticFunction.sigma_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hdvd : 12 ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
        have hmod : (5 * d ^ 3 + 7 * d ^ 5) % 12 = (5 * (d % 12) ^ 3 + 7 * (d % 12) ^ 5) % 12 := by
          simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
        rw [Nat.dvd_iff_mod_eq_zero, hmod]
        have hlt : d % 12 < 12 := Nat.mod_lt d (by decide)
        interval_cases (d % 12) <;> decide
      exact (Nat.mul_div_cancel' hdvd).symm
    omega
  have hlin_mod : PowerSeries.coeff n linearDeltaSeriesZ ≡ (n.divisors.card : ℤ) [ZMOD 2] := by
    simp only [linearDeltaSeriesZ, PowerSeries.coeff_mk, hn0, ↓reduceIte, hlin_sum, Nat.cast_sum]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine int_modEq_sum fun d hd => ?_
    have hd_odd : Odd d := by
      rcases Nat.dvd_of_mem_divisors hd with ⟨e, he⟩
      rw [he] at hn
      exact (Nat.odd_mul.mp hn).1
    have hodd := odd_div_twelve_five_cube_add_seven_pow_five hd_odd
    rw [Nat.odd_iff] at hodd
    rw [Int.modEq_iff_dvd]
    exact ⟨-((5 * d ^ 3 + 7 * d ^ 5) / 12 / 2 : ℕ), by omega⟩
  rw [Int.modEq_iff_dvd] at hlin_mod ⊢
  obtain ⟨k, hk⟩ := hlin_mod
  refine ⟨k - 50 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) -
      4000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) + 147 * r, ?_⟩
  linarith

/-- Elementary number theory: for any `n ≥ 1`, `Odd n.divisors.card ↔ IsSquare n`. -/
private lemma odd_card_divisors_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  -- Pair each divisor d ≠ n / d with n / d; the fixed points are precisely d with d * d = n!
  let S := n.divisors.filter (fun d => d * d < n)
  let T := n.divisors.filter (fun d => n < d * d)
  let F := n.divisors.filter (fun d => d * d = n)
  have hbij : S.card = T.card := by
    refine Finset.card_nbij' (fun d => n / d) (fun d => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd_div, hlt⟩
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd_div), hn⟩, ?_⟩
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd_div)
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd_div) (Nat.pos_of_ne_zero hn)
      have hdn : d < n / d := by nlinarith
      nlinarith
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd_div, hgt⟩
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd_div), hn⟩, ?_⟩
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd_div)
      have hdn : n / d < d := by nlinarith
      have hnd_pos : 0 < n / d :=
        Nat.pos_of_ne_zero (fun h0 => hn (by rw [← hmul, h0, mul_zero]))
      dsimp only
      nlinarith
    · intro d hd; exact Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hn
    · intro d hd; exact Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hn
  have hpart : n.divisors.card = S.card + T.card + F.card := by
    have hunion : n.divisors = S ∪ T ∪ F := by
      ext d
      simp only [Finset.mem_union, Finset.mem_filter, S, T, F]
      constructor
      · intro hd
        rcases lt_trichotomy (d * d) n with h | h | h
        · exact Or.inl (Or.inl ⟨hd, h⟩)
        · exact Or.inr ⟨hd, h⟩
        · exact Or.inl (Or.inr ⟨hd, h⟩)
      · rintro ((⟨hd, _⟩ | ⟨hd, _⟩) | ⟨hd, _⟩) <;> exact hd
    have hd1 : Disjoint S T := Finset.disjoint_filter.mpr fun _ _ h1 h2 => not_lt.mpr h1.le h2
    have hd2 : Disjoint (S ∪ T) F := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_filter.mpr fun _ _ h1 h2 => ne_of_lt h1 h2,
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => ne_of_gt h1 h2⟩
    rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  rw [hpart, hbij]
  constructor
  · intro hodd
    have hFne : F.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.card_empty, add_zero] at hodd
      exact (Nat.not_odd_iff_even.mpr ⟨T.card, rfl⟩) hodd
    obtain ⟨d, hd⟩ := hFne
    exact ⟨d, (Finset.mem_filter.mp hd).2.symm⟩
  · rintro ⟨d, rfl⟩
    have hFcard : F.card = 1 := by
      have hFeq : F = {d} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton, F]
        constructor
        · rintro ⟨_, hx⟩
          nlinarith
        · rintro rfl
          exact ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right x x, hn⟩, rfl⟩
      rw [hFeq, Finset.card_singleton]
    rw [hFcard]
    exact ⟨T.card, by ring⟩

/-- **Every Prime Value `τ(p)` is Even**:
`∀ p : ℕ, p.Prime → Even (ramanujanTau p)`! -/
theorem even_ramanujanTau_of_prime {p : ℕ} (hp : p.Prime) :
    Even (ramanujanTau p) := by
  by_cases hp2 : p = 2
  · subst hp2; rw [ramanujanTau_two]; exact ⟨-12, by norm_num⟩
  · have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have hmod := ramanujanTau_mod_two_of_odd hp_odd
    have hcard : p.divisors.card = 2 := by
      rw [hp.divisors, Finset.card_pair hp.one_lt.ne]
    rw [hcard, Int.modEq_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hmod
    norm_num at hk
    exact ⟨1 - k, by linarith⟩

/-- For every `e ≥ 1`, `τ(2^e)` is EVEN (by `ramanujanTau_prime_pow_recurrence` at `p = 2`). -/
private lemma even_ramanujanTau_two_pow : ∀ e : ℕ, 1 ≤ e → Even (ramanujanTau (2 ^ e))
  | 0, h => by omega
  | 1, _ => by rw [pow_one, ramanujanTau_two]; exact ⟨-12, by norm_num⟩
  | r + 2, _ => by
      rw [ramanujanTau_prime_pow_recurrence Nat.prime_two r, ramanujanTau_two]
      exact ⟨-12 * ramanujanTau (2 ^ (r + 1)) - 2 ^ 10 * ramanujanTau (2 ^ r), by ring⟩

/-- **EXACT PARITY CHARACTERIZATION OF RAMANUJAN'S `τ(n)` (UNCONDITIONAL, `0` ASSUMPTIONS!)**:
$$\operatorname{Odd}(\tau(n)) \iff \exists k : \mathbb{N},\; n = (2k + 1)^2.$$ -/
theorem odd_ramanujanTau_iff (n : ℕ) :
    Odd (ramanujanTau n) ↔ ∃ k : ℕ, n = (2 * k + 1) ^ 2 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp only [ramanujanTau_zero, Int.not_odd_zero, false_iff, not_exists]
    intro k hk
    have hpos : 0 < (2 * k + 1) ^ 2 := by positivity
    omega
  · by_cases hodd : Odd n
    · -- Odd n: τ(n) ≡ d(n) [ZMOD 2], and Odd d(n) ↔ IsSquare n ↔ ∃ k, n = (2k + 1)^2!
      have hmod := ramanujanTau_mod_two_of_odd hodd
      have hodd_iff : Odd (ramanujanTau n) ↔ Odd n.divisors.card := by
        rw [Int.odd_iff, Nat.odd_iff]
        rw [Int.modEq_iff_dvd] at hmod
        obtain ⟨k, hk⟩ := hmod
        omega
      rw [hodd_iff, odd_card_divisors_iff_isSquare hn0]
      constructor
      · rintro ⟨m, hm⟩
        have hm_odd : Odd m := by
          rw [hm] at hodd
          exact (Nat.odd_mul.mp hodd).1
        rcases hm_odd with ⟨k, rfl⟩
        exact ⟨k, by rw [hm, sq]⟩
      · rintro ⟨k, rfl⟩
        exact ⟨2 * k + 1, sq _⟩
    · -- Even n > 0: write n = 2^e * m with e ≥ 1 and m odd; then τ(n) = τ(2^e) * τ(m) is EVEN!
      have heven : Even n := Nat.not_odd_iff_even.mp hodd
      have h2_dvd : 2 ∣ n := even_iff_two_dvd.mp heven
      let e : ℕ := n.factorization 2
      let m : ℕ := n / 2 ^ e
      have he_pos : 1 ≤ e := by
        have hne : n.factorization 2 ≠ 0 :=
          Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 h2_dvd |>.ne'
        omega
      have hpow_dvd : 2 ^ e ∣ n := Nat.ordProj_dvd n 2
      have hnm : 2 ^ e * m = n := Nat.mul_div_cancel' hpow_dvd
      have hcop : Nat.Coprime (2 ^ e) m := by
        have hnot2 : ¬ 2 ∣ m := by
          intro h2m
          have hpow1 : 2 ^ (e + 1) ∣ n := by
            rcases h2m with ⟨q, hq⟩
            exact ⟨q, by rw [← hnm, hq, pow_succ]; ring⟩
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mp hpow1
          omega
        exact (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2).pow_left e
      have htau_even : Even (ramanujanTau n) := by
        rw [← hnm, ramanujanTau_mul_of_coprime hcop]
        exact (even_ramanujanTau_two_pow e he_pos).mul_right _
      constructor
      · intro ho
        exact absurd ho (Int.not_odd_iff_even.mpr htau_even)
      · rintro ⟨k, rfl⟩
        have ho : Odd ((2 * k + 1) ^ 2) := Odd.pow (⟨k, rfl⟩ : Odd (2 * k + 1))
        exact absurd ho hodd

end ParityCharacterization

end

end RHDirect.Stage8RamanujanCongruences
