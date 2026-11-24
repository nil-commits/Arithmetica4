import RHDirect.Stage5ModularHecke
import RHDirect.Stage7EisensteinSeries
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# RHDirect.Stage8RamanujanDelta

**UNCONDITIONAL PROOF OF MORDELL'S 1917 THEOREM & RAMANUJAN'S CONJECTURES ON `Δ(τ)` AND `τ(n)`**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Concrete Ramanujan Discriminant Cusp Form `Δ(τ) = (E₄(τ)³ - E₆(τ)²) / 1728`, Exact Integer
   `q`-Expansion `τ(n) ∈ ℤ`, and `dim S₁₂(SL₂(ℤ)) = 1`**:
   - `ramanujanDelta : CuspForm SL2ZRange 12` (with `SL2ZRange = Subgroup.map (mapGL ℝ) (Gamma 1)`),
     satisfying `ramanujanDelta τ = (E4 τ ^ 3 - E6 τ ^ 2) / 1728` and
     `qExpansion 1 ramanujanDelta = (1 / 1728) • (qExpansion 1 E4 ^ 3 - qExpansion 1 E6 ^ 2)`.
   - Exact integer power series `ramanujanDeltaPowerSeriesZ : PowerSeries ℤ` (constructed directly
     from `E₄ = 1 + 240 A`, `E₆ = 1 - 504 B` via the congruence `12 ∣ 5 σ₃(n) + 7 σ₅(n)`) and
     exact integer Ramanujan tau function `ramanujanTau : ℕ → ℤ`, proving:
     - `ramanujanTau_cast_eq_qExpansion_coeff`: `∀ n, (ramanujanTau n : ℂ) = coeff n (qExpansion 1 Δ)`
     - `ramanujanTau_zero` (`0`), `ramanujanTau_one` (`1`), `ramanujanTau_two` (`-24`),
       `ramanujanTau_three` (`252`), `ramanujanTau_four` (`-1472`)
   - `rank_cuspForm_SL2Z_weight_twelve : Module.rank ℂ (CuspForm SL2ZRange 12) = 1` and
     `cuspForm_SL2Z_weight_twelve_eq_smul_delta : ∀ f ∈ S₁₂(SL₂(ℤ)), f = a₁(f) • Δ`.

2. **Full `SL₂(ℤ)` Hermite Normal Form Coset Action & Unconditional Proof of Mordell's Theorem
   (`T_n Δ = τ(n) Δ`)**:
   - Constructive `2 × 2` Hermite Normal Form (`hermiteNormalForm_exists`, `hermiteNormalForm_unique`)
     producing a canonical right-coset permutation `SL₂(ℤ) \ M₂⁺(ℤ)_n` for every `n ≥ 1` and
     `γ ∈ SL₂(ℤ)`.
   - Unconditional theorem that the slash-action Hecke operator `slashHeckeOp k 1 n` preserves
     `CuspForm SL2ZRange k` for EVERY weight `k ≥ 1` and `n ≥ 1` (`heckeCuspForm`).
   - By `dim S₁₂(SL₂(ℤ)) = 1`, unconditional proof of **Mordell's 1917 Theorem**:
     - `slashHeckeOp_ramanujanDelta : slashHeckeOp 12 1 n Δ = (ramanujanTau n : ℂ) • Δ`
     - `heckeCuspForm_ramanujanDelta : heckeCuspForm 12 _ n _ Δ = (ramanujanTau n : ℂ) • Δ`
     - `isNormalizedHeckeEigenform_ramanujanTau : IsNormalizedHeckeEigenform 12 1 (τ : ℕ → ℂ) (τ : ℕ → ℂ)`

3. **Unconditional Ramanujan Multiplicativity, Prime-Power Recurrence & `L(Δ, s)` Degree-2 Euler
   Product (`0` Assumptions!)**:
   - `ramanujanTau_mul_of_coprime : ∀ m n, Nat.Coprime m n → τ(m * n) = τ(m) * τ(n)`
   - `ramanujanTau_prime_pow_recurrence : ∀ p, p.Prime → ∀ r, τ(p^(r+2)) = τ(p) τ(p^(r+1)) - p^11 τ(p^r)`
   - Verified consequences `ramanujanTau_six` (`-6048`), `ramanujanTau_eight` (`84480`),
     `ramanujanTau_nine` (`-113643`).
   - `ramanujanDelta_LSeries_eulerProduct` (and `ramanujanDelta_modularL_eulerProduct`): for all
     `s : ℂ` with `7 < s.re`,
     `LSeries (fun n => (ramanujanTau n : ℂ)) s = ∏' p : Nat.Primes, (1 - τ(p) p^{-s} + p^{11 - 2s})⁻¹`.
-/

open Complex Real Filter Module Submodule Finset Matrix
open RHDirect.Stage5ModularHecke RHDirect.Stage7EisensteinSeries
open scoped BigOperators UpperHalfPlane ModularForm Topology Manifold

namespace RHDirect.Stage8RamanujanDelta

noncomputable section

/-! ## Section 1: Concrete Ramanujan Discriminant `Δ`, Exact Integer `τ(n)` & `dim S₁₂(SL₂(ℤ)) = 1` -/

section RamanujanDeltaAndTau

/-- Identification of the level-1 modular group `SL2ZRange` with the image of
`CongruenceSubgroup.Gamma 1` inside `GL₂(ℝ)`. -/
theorem SL2ZRange_eq_map_Gamma_one :
    SL2ZRange = Subgroup.map (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) (CongruenceSubgroup.Gamma 1) := by
  ext g
  simp only [SL2ZRange, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ, ?_, rfl⟩
    rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · rintro ⟨γ, _, rfl⟩
    exact ⟨γ, rfl⟩

/-- **The Concrete Ramanujan Discriminant Cusp Form `Δ ∈ S₁₂(SL₂(ℤ))`**. -/
def ramanujanDelta : CuspForm SL2ZRange 12 :=
  CuspForm.discriminant

@[simp]
theorem ramanujanDelta_coe :
    (ramanujanDelta : UpperHalfPlane → ℂ) = ModularForm.discriminant :=
  CuspForm.coe_discriminant

/-- Explicit identity `Δ(τ) = (E₄(τ)³ - E₆(τ)²) / 1728` everywhere on the upper half-plane. -/
theorem ramanujanDelta_apply (τ : UpperHalfPlane) :
    ramanujanDelta τ = (E4 τ ^ 3 - E6 τ ^ 2) / 1728 := by
  rw [ramanujanDelta_coe]
  exact discriminant_eq_E4_cube_sub_E6_sq τ

/-- Exact `q`-expansion identity for `Δ` in terms of the `q`-expansions of `E₄` and `E₆`:
`qExpansion 1 Δ = (1 / 1728) • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2)`. -/
theorem ramanujanDelta_qExpansion_eq :
    UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ) =
      (1 / 1728 : ℂ) •
        (UpperHalfPlane.qExpansion 1 E4 ^ 3 - UpperHalfPlane.qExpansion 1 E6 ^ 2) := by
  let e4sq : ModularForm SL2ZRange 8 :=
    ModularForm.mcast (by norm_num : (4 : ℤ) + 4 = 8) (ModularForm.E₄.mul ModularForm.E₄) rfl
  let e4cube : ModularForm SL2ZRange 12 :=
    ModularForm.mcast (by norm_num : (8 : ℤ) + 4 = 12) (e4sq.mul ModularForm.E₄) rfl
  let e6sq : ModularForm SL2ZRange 12 :=
    ModularForm.mcast (by norm_num : (6 : ℤ) + 6 = 12) (ModularForm.E₆.mul ModularForm.E₆) rfl
  have he4sq_coe : (e4sq : UpperHalfPlane → ℂ) =
      (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := rfl
  have he4cube_coe : (e4cube : UpperHalfPlane → ℂ) =
      (e4sq : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := rfl
  have he6sq_coe : (e6sq : UpperHalfPlane → ℂ) =
      (ModularForm.E₆ : UpperHalfPlane → ℂ) * (ModularForm.E₆ : UpperHalfPlane → ℂ) := rfl
  have hdelta_coe : (ramanujanDelta : UpperHalfPlane → ℂ) =
      (1 / 1728 : ℂ) • ((e4cube - e6sq : ModularForm SL2ZRange 12) : UpperHalfPlane → ℂ) := by
    funext τ
    rw [ramanujanDelta_apply τ]
    simp only [Pi.smul_apply, smul_eq_mul, FunLike.coe_sub, Pi.sub_apply]
    have h1 : e4cube τ = E4 τ ^ 3 := by
      change ModularForm.E₄ τ * ModularForm.E₄ τ * ModularForm.E₄ τ = E4 τ ^ 3
      rw [← E4_eq_modularForm_E4 τ]
      ring
    have h2 : e6sq τ = E6 τ ^ 2 := by
      change ModularForm.E₆ τ * ModularForm.E₆ τ = E6 τ ^ 2
      rw [← E6_eq_modularForm_E6 τ]
      ring
    rw [h1, h2]
    ring
  rw [hdelta_coe,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL (1 / 1728 : ℂ) (e4cube - e6sq),
    FunLike.coe_sub,
    ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL e4cube e6sq,
    he4cube_coe,
    ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL e4sq ModularForm.E₄,
    he4sq_coe,
    ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL ModularForm.E₄ ModularForm.E₄,
    he6sq_coe,
    ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL ModularForm.E₆ ModularForm.E₆,
    ← E4_eq_coe, ← E6_eq_coe]
  congr 1
  ring

/-- Elementary arithmetic congruence: `12 ∣ 5 d^3 + 7 d^5` for every natural number `d`. -/
private lemma twelve_dvd_five_cube_add_seven_pow_five (d : ℕ) :
    12 ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have hmod : (5 * d ^ 3 + 7 * d ^ 5) % 12 = (5 * (d % 12) ^ 3 + 7 * (d % 12) ^ 5) % 12 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  have hlt : d % 12 < 12 := Nat.mod_lt d (by decide)
  interval_cases (d % 12) <;> decide

/-- Exact divisor-sum congruence: `12 ∣ 5 σ₃(n) + 7 σ₅(n)` for every `n : ℕ`. -/
theorem twelve_dvd_five_sigma3_add_seven_sigma5 (n : ℕ) :
    12 ∣ 5 * ArithmeticFunction.sigma 3 n + 7 * ArithmeticFunction.sigma 5 n := by
  simp only [ArithmeticFunction.sigma_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_cube_add_seven_pow_five d

/-- Formal integer power series `A(q) = ∑_{n ≥ 1} σ₃(n) q^n ∈ ℤ⟦q⟧`. -/
def sigma3SeriesZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (ArithmeticFunction.sigma 3 n : ℤ)

/-- Formal integer power series `B(q) = ∑_{n ≥ 1} σ₅(n) q^n ∈ ℤ⟦q⟧`. -/
def sigma5SeriesZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (ArithmeticFunction.sigma 5 n : ℤ)

/-- Formal integer power series `C(q) = ∑_{n ≥ 1} ((5 σ₃(n) + 7 σ₅(n)) / 12) q^n ∈ ℤ⟦q⟧`. -/
def linearDeltaSeriesZ : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else (((5 * ArithmeticFunction.sigma 3 n + 7 * ArithmeticFunction.sigma 5 n) / 12 : ℕ) : ℤ)

/-- **Exact Integer Power Series of Ramanujan's Discriminant `Δ(q) = ∑_{n ≥ 1} τ(n) q^n ∈ ℤ⟦q⟧`**,
constructed directly from `(1 + 240 A)³ - (1 - 504 B)² = 1728 (C + 100 A² + 8000 A³ - 147 B²)`. -/
def ramanujanDeltaPowerSeriesZ : PowerSeries ℤ :=
  linearDeltaSeriesZ + 100 * sigma3SeriesZ ^ 2 + 8000 * sigma3SeriesZ ^ 3 - 147 * sigma5SeriesZ ^ 2

/-- **The Exact Integer Ramanujan Tau Function `τ : ℕ → ℤ`**. -/
def ramanujanTau (n : ℕ) : ℤ :=
  PowerSeries.coeff n ramanujanDeltaPowerSeriesZ

private lemma coeff_natCast_mul {R : Type*} [CommRing R] (c : ℕ) (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((c : PowerSeries R) * φ) = (c : R) * PowerSeries.coeff n φ := by
  rw [← map_natCast (PowerSeries.C (R := R)) c, PowerSeries.coeff_C_mul]

/-- Exact integer identity `1728 · Δ_ℤ(q) = (1 + 240 A(q))³ - (1 - 504 B(q))²` in `ℤ⟦q⟧`. -/
theorem mul_1728_ramanujanDeltaPowerSeriesZ :
    (1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ =
      (1 + 240 * sigma3SeriesZ) ^ 3 - (1 - 504 * sigma5SeriesZ) ^ 2 := by
  have h12C : (12 : PowerSeries ℤ) * linearDeltaSeriesZ =
      5 * sigma3SeriesZ + 7 * sigma5SeriesZ := by
    ext n
    have h12 : PowerSeries.coeff n ((12 : PowerSeries ℤ) * linearDeltaSeriesZ) =
        12 * PowerSeries.coeff n linearDeltaSeriesZ := by
      simpa using coeff_natCast_mul 12 linearDeltaSeriesZ n
    have h5 : PowerSeries.coeff n ((5 : PowerSeries ℤ) * sigma3SeriesZ) =
        5 * PowerSeries.coeff n sigma3SeriesZ := by
      simpa using coeff_natCast_mul 5 sigma3SeriesZ n
    have h7 : PowerSeries.coeff n ((7 : PowerSeries ℤ) * sigma5SeriesZ) =
        7 * PowerSeries.coeff n sigma5SeriesZ := by
      simpa using coeff_natCast_mul 7 sigma5SeriesZ n
    rw [map_add, h12, h5, h7]
    simp only [linearDeltaSeriesZ, sigma3SeriesZ, sigma5SeriesZ, PowerSeries.coeff_mk]
    split_ifs with hn
    · ring
    · have hdvd := twelve_dvd_five_sigma3_add_seven_sigma5 n
      have hnat : 12 * ((5 * ArithmeticFunction.sigma 3 n + 7 * ArithmeticFunction.sigma 5 n) / 12) =
          5 * ArithmeticFunction.sigma 3 n + 7 * ArithmeticFunction.sigma 5 n :=
        Nat.mul_div_cancel' hdvd
      exact_mod_cast hnat
  unfold ramanujanDeltaPowerSeriesZ
  have h1728 : (1728 : PowerSeries ℤ) * linearDeltaSeriesZ =
      144 * ((12 : PowerSeries ℤ) * linearDeltaSeriesZ) := by ring
  calc (1728 : PowerSeries ℤ) *
          (linearDeltaSeriesZ + 100 * sigma3SeriesZ ^ 2 +
            8000 * sigma3SeriesZ ^ 3 - 147 * sigma5SeriesZ ^ 2)
      = (1728 : PowerSeries ℤ) * linearDeltaSeriesZ +
          172800 * sigma3SeriesZ ^ 2 + 13824000 * sigma3SeriesZ ^ 3 -
          254016 * sigma5SeriesZ ^ 2 := by ring
    _ = 144 * (5 * sigma3SeriesZ + 7 * sigma5SeriesZ) +
          172800 * sigma3SeriesZ ^ 2 + 13824000 * sigma3SeriesZ ^ 3 -
          254016 * sigma5SeriesZ ^ 2 := by rw [h1728, h12C]
    _ = (1 + 240 * sigma3SeriesZ) ^ 3 - (1 - 504 * sigma5SeriesZ) ^ 2 := by ring

private lemma map_intCast_E4 :
    PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * sigma3SeriesZ) =
      UpperHalfPlane.qExpansion 1 E4 := by
  ext n
  rw [PowerSeries.coeff_map, E4_qExpansion_coeff]
  have h240 : PowerSeries.coeff n ((240 : PowerSeries ℤ) * sigma3SeriesZ) =
      240 * PowerSeries.coeff n sigma3SeriesZ := by
    simpa using coeff_natCast_mul 240 sigma3SeriesZ n
  rw [map_add, h240]
  simp only [sigma3SeriesZ, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs with hn
  · simp
  · simp

private lemma map_intCast_E6 :
    PowerSeries.map (Int.castRingHom ℂ) (1 - 504 * sigma5SeriesZ) =
      UpperHalfPlane.qExpansion 1 E6 := by
  ext n
  rw [PowerSeries.coeff_map, E6_qExpansion_coeff]
  have h504 : PowerSeries.coeff n ((504 : PowerSeries ℤ) * sigma5SeriesZ) =
      504 * PowerSeries.coeff n sigma5SeriesZ := by
    simpa using coeff_natCast_mul 504 sigma5SeriesZ n
  rw [map_sub, h504]
  simp only [sigma5SeriesZ, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs with hn
  · simp
  · simp

/-- Exact `q`-expansion identification in `ℂ⟦q⟧`:
`PowerSeries.map (Int.castRingHom ℂ) ramanujanDeltaPowerSeriesZ = qExpansion 1 Δ`. -/
theorem ramanujanDeltaPowerSeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) ramanujanDeltaPowerSeriesZ =
      UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ) := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℂ)) mul_1728_ramanujanDeltaPowerSeriesZ
  rw [map_mul, map_ofNat, map_sub, map_pow, map_pow, map_intCast_E4, map_intCast_E6] at hmap
  rw [ramanujanDelta_qExpansion_eq]
  ext n
  have h1728 : PowerSeries.coeff n
      ((1728 : PowerSeries ℂ) * PowerSeries.map (Int.castRingHom ℂ) ramanujanDeltaPowerSeriesZ) =
      1728 * PowerSeries.coeff n (PowerSeries.map (Int.castRingHom ℂ) ramanujanDeltaPowerSeriesZ) := by
    simpa using coeff_natCast_mul 1728
      (PowerSeries.map (Int.castRingHom ℂ) ramanujanDeltaPowerSeriesZ) n
  have hcoeff := congrArg (PowerSeries.coeff n) hmap
  rw [h1728] at hcoeff
  rw [map_smul, smul_eq_mul, ← hcoeff]
  ring

/-- **Exact Integrality of Every Fourier Coefficient of `Δ(τ)`**:
for EVERY `n : ℕ`, `(ramanujanTau n : ℂ) = PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 Δ)`. -/
theorem ramanujanTau_cast_eq_qExpansion_coeff (n : ℕ) :
    (ramanujanTau n : ℂ) =
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) := by
  rw [← ramanujanDeltaPowerSeriesZ_map_eq, PowerSeries.coeff_map]
  rfl

private lemma sigma_three_two : ArithmeticFunction.sigma 3 2 = 9 := by decide
private lemma sigma_three_three : ArithmeticFunction.sigma 3 3 = 28 := by decide
private lemma sigma_three_four : ArithmeticFunction.sigma 3 4 = 73 := by decide
private lemma sigma_five_two : ArithmeticFunction.sigma 5 2 = 33 := by decide
private lemma sigma_five_three : ArithmeticFunction.sigma 5 3 = 244 := by decide
private lemma sigma_five_four : ArithmeticFunction.sigma 5 4 = 1057 := by decide

private lemma coeff_sigma3_vals :
    PowerSeries.coeff 0 sigma3SeriesZ = 0 ∧
    PowerSeries.coeff 1 sigma3SeriesZ = 1 ∧
    PowerSeries.coeff 2 sigma3SeriesZ = 9 ∧
    PowerSeries.coeff 3 sigma3SeriesZ = 28 ∧
    PowerSeries.coeff 4 sigma3SeriesZ = 73 := by
  simp [sigma3SeriesZ, sigma_three_two, sigma_three_three, sigma_three_four]

private lemma coeff_sigma5_vals :
    PowerSeries.coeff 0 sigma5SeriesZ = 0 ∧
    PowerSeries.coeff 1 sigma5SeriesZ = 1 ∧
    PowerSeries.coeff 2 sigma5SeriesZ = 33 ∧
    PowerSeries.coeff 3 sigma5SeriesZ = 244 ∧
    PowerSeries.coeff 4 sigma5SeriesZ = 1057 := by
  simp [sigma5SeriesZ, sigma_five_two, sigma_five_three, sigma_five_four]

private lemma coeff_linearDelta_vals :
    PowerSeries.coeff 0 linearDeltaSeriesZ = 0 ∧
    PowerSeries.coeff 1 linearDeltaSeriesZ = 1 ∧
    PowerSeries.coeff 2 linearDeltaSeriesZ = 23 ∧
    PowerSeries.coeff 3 linearDeltaSeriesZ = 154 ∧
    PowerSeries.coeff 4 linearDeltaSeriesZ = 647 := by
  simp [linearDeltaSeriesZ, sigma_three_two, sigma_three_three, sigma_three_four,
    sigma_five_two, sigma_five_three, sigma_five_four]

private lemma coeff_ramanujanTau_expand (n : ℕ) :
    ramanujanTau n =
      PowerSeries.coeff n linearDeltaSeriesZ +
        100 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) +
        8000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) -
        147 * PowerSeries.coeff n (sigma5SeriesZ ^ 2) := by
  unfold ramanujanTau ramanujanDeltaPowerSeriesZ
  have h100 : PowerSeries.coeff n ((100 : PowerSeries ℤ) * sigma3SeriesZ ^ 2) =
      100 * PowerSeries.coeff n (sigma3SeriesZ ^ 2) := by
    simpa using coeff_natCast_mul 100 (sigma3SeriesZ ^ 2) n
  have h8000 : PowerSeries.coeff n ((8000 : PowerSeries ℤ) * sigma3SeriesZ ^ 3) =
      8000 * PowerSeries.coeff n (sigma3SeriesZ ^ 3) := by
    simpa using coeff_natCast_mul 8000 (sigma3SeriesZ ^ 3) n
  have h147 : PowerSeries.coeff n ((147 : PowerSeries ℤ) * sigma5SeriesZ ^ 2) =
      147 * PowerSeries.coeff n (sigma5SeriesZ ^ 2) := by
    simpa using coeff_natCast_mul 147 (sigma5SeriesZ ^ 2) n
  rw [map_sub, map_add, map_add, h100, h8000, h147]

private lemma coeff_sq_expand (φ : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (φ ^ 2) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k φ * PowerSeries.coeff (n - k) φ := by
  rw [sq, PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a φ * PowerSeries.coeff b φ) n

private lemma coeff_cube_expand (φ : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (φ ^ 3) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k (φ ^ 2) * PowerSeries.coeff (n - k) φ := by
  rw [pow_succ, PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (φ ^ 2) * PowerSeries.coeff b φ) n

/-- `τ(0) = 0`. -/
@[simp]
theorem ramanujanTau_zero : ramanujanTau 0 = 0 := by
  have ⟨a0, _, _, _, _⟩ := coeff_sigma3_vals
  have ⟨b0, _, _, _, _⟩ := coeff_sigma5_vals
  have ⟨c0, _, _, _, _⟩ := coeff_linearDelta_vals
  rw [coeff_ramanujanTau_expand, coeff_cube_expand, coeff_sq_expand, coeff_sq_expand]
  simp [a0, b0, c0]

/-- `τ(1) = 1`. -/
@[simp]
theorem ramanujanTau_one : ramanujanTau 1 = 1 := by
  have ⟨a0, a1, _, _, _⟩ := coeff_sigma3_vals
  have ⟨b0, b1, _, _, _⟩ := coeff_sigma5_vals
  have ⟨_, c1, _, _, _⟩ := coeff_linearDelta_vals
  rw [coeff_ramanujanTau_expand, coeff_cube_expand]
  simp only [coeff_sq_expand, Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, b0, b1, c1]
  norm_num

/-- `τ(2) = -24`. -/
theorem ramanujanTau_two : ramanujanTau 2 = -24 := by
  have ⟨a0, a1, a2, _, _⟩ := coeff_sigma3_vals
  have ⟨b0, b1, b2, _, _⟩ := coeff_sigma5_vals
  have ⟨_, _, c2, _, _⟩ := coeff_linearDelta_vals
  rw [coeff_ramanujanTau_expand, coeff_cube_expand]
  simp only [coeff_sq_expand, Finset.sum_range_succ, Finset.sum_range_zero,
    a0, a1, a2, b0, b1, b2, c2]
  norm_num

/-- `τ(3) = 252`. -/
theorem ramanujanTau_three : ramanujanTau 3 = 252 := by
  have ⟨a0, a1, a2, a3, _⟩ := coeff_sigma3_vals
  have ⟨b0, b1, b2, b3, _⟩ := coeff_sigma5_vals
  have ⟨_, _, _, c3, _⟩ := coeff_linearDelta_vals
  rw [coeff_ramanujanTau_expand, coeff_cube_expand]
  simp only [coeff_sq_expand, Finset.sum_range_succ, Finset.sum_range_zero,
    a0, a1, a2, a3, b0, b1, b2, b3, c3]
  norm_num

/-- `τ(4) = -1472`. -/
theorem ramanujanTau_four : ramanujanTau 4 = -1472 := by
  have ⟨a0, a1, a2, a3, a4⟩ := coeff_sigma3_vals
  have ⟨b0, b1, b2, b3, b4⟩ := coeff_sigma5_vals
  have ⟨_, _, _, _, c4⟩ := coeff_linearDelta_vals
  rw [coeff_ramanujanTau_expand, coeff_cube_expand]
  simp only [coeff_sq_expand, Finset.sum_range_succ, Finset.sum_range_zero,
    a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, c4]
  norm_num

/-- Direct `q`-expansion coefficients `a_0(Δ) = 0, a_1(Δ) = 1, a_2(Δ) = -24, a_3(Δ) = 252, a_4(Δ) = -1472`. -/
theorem ramanujanDelta_qExpansion_coeff_zero :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) = 0 := by
  rw [← ramanujanTau_cast_eq_qExpansion_coeff, ramanujanTau_zero]; norm_num

theorem ramanujanDelta_qExpansion_coeff_one :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) = 1 := by
  rw [← ramanujanTau_cast_eq_qExpansion_coeff, ramanujanTau_one]; norm_num

theorem ramanujanDelta_qExpansion_coeff_two :
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) = -24 := by
  rw [← ramanujanTau_cast_eq_qExpansion_coeff, ramanujanTau_two]; norm_num

theorem ramanujanDelta_qExpansion_coeff_three :
    PowerSeries.coeff 3 (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) = 252 := by
  rw [← ramanujanTau_cast_eq_qExpansion_coeff, ramanujanTau_three]; norm_num

theorem ramanujanDelta_qExpansion_coeff_four :
    PowerSeries.coeff 4 (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) = -1472 := by
  rw [← ramanujanTau_cast_eq_qExpansion_coeff, ramanujanTau_four]; norm_num

/-- **`dim S₁₂(SL₂(ℤ)) = 1`**. -/
theorem rank_cuspForm_SL2Z_weight_twelve :
    Module.rank ℂ (CuspForm SL2ZRange 12) = 1 :=
  CuspForm.rank_eq_one_of_weight_eq_twelve

/-- **1-Dimensionality Characterization of `S₁₂(SL₂(ℤ))`**:
every weight-12 `SL₂(ℤ)` cusp form `f` equals `a₁(f) • Δ`! -/
theorem cuspForm_SL2Z_weight_twelve_eq_smul_delta (f : CuspForm SL2ZRange 12) :
    f = (PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) •
      ramanujanDelta := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve f
  have hq : UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ) =
      c • UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ) := by
    rw [← hc]
    change UpperHalfPlane.qExpansion 1 ((c • ramanujanDelta : CuspForm SL2ZRange 12) : UpperHalfPlane → ℂ) = _
    rw [FunLike.coe_smul]
    exact ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL c ramanujanDelta
  have hc_eq : PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) = c := by
    rw [hq, map_smul, smul_eq_mul, ramanujanDelta_qExpansion_coeff_one, mul_one]
  rw [hc_eq]
  exact hc.symm

end RamanujanDeltaAndTau

/-! ## Section 2: Constructive `2 × 2` Hermite Normal Form & Hecke Invariance of `S_k(SL₂(ℤ))` -/

section HermiteNormalFormAndHeckeAction

/-- Integer upper-triangular Hecke matrix `[[a, b], [0, d]] ∈ M₂(ℤ)`. -/
def heckeMatZ (a b d : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(a : ℤ), (b : ℤ); 0, (d : ℤ)]

/-- **Existence of `2 × 2` Hermite Normal Form**:
Every integer `2 × 2` matrix `M` of positive determinant `n > 0` factors as
`M = σ · [[a, b], [0, d]]` with `σ ∈ SL₂(ℤ)`, `a > 0`, `d > 0`, `a * d = n`, and `b < d`. -/
theorem hermiteNormalForm_exists {n : ℕ} (hn : 0 < n) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = (n : ℤ)) :
    ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℕ),
      0 < a ∧ 0 < d ∧ a * d = n ∧ b < d ∧ (σ : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ a b d = M := by
  set p : ℤ := M 0 0
  set q : ℤ := M 0 1
  set r : ℤ := M 1 0
  set s : ℤ := M 1 1
  have hdet' : p * s - q * r = (n : ℤ) := by
    simpa [Matrix.det_fin_two, p, q, r, s] using hdet
  set a : ℕ := Int.gcd p r
  have ha_pos : 0 < a := by
    by_contra h
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos h
    have hpr : p = 0 ∧ r = 0 := Int.gcd_eq_zero_iff.mp ha0
    have hnZ : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
    rw [hpr.1, hpr.2] at hdet'
    linarith
  have ha_ne : (a : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt ha_pos)
  set u : ℤ := p / (a : ℤ)
  set v : ℤ := r / (a : ℤ)
  have hu : (a : ℤ) * u = p := Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)
  have hv : (a : ℤ) * v = r := Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)
  set x : ℤ := Int.gcdA p r
  set y : ℤ := Int.gcdB p r
  have hbez : u * x + v * y = 1 := by
    have h1 : (a : ℤ) = p * x + r * y := Int.gcd_eq_gcd_ab p r
    have h2 : (a : ℤ) * (u * x + v * y) = (a : ℤ) * 1 := by
      calc (a : ℤ) * (u * x + v * y) = ((a : ℤ) * u) * x + ((a : ℤ) * v) * y := by ring
        _ = p * x + r * y := by rw [hu, hv]
        _ = (a : ℤ) := h1.symm
        _ = (a : ℤ) * 1 := (mul_one _).symm
    exact mul_left_cancel₀ ha_ne h2
  let σ₀ : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![u, -y; v, x], by
      simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith⟩
  set b' : ℤ := x * q + y * s
  set d' : ℤ := -v * q + u * s
  have hσ0M : (σ₀ : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b'; 0, d'] = M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σ₀, Matrix.mul_apply, Fin.sum_univ_two]
    · change u * (a : ℤ) = p; linarith
    · change u * b' + -(y * d') = q
      calc u * (x * q + y * s) + -(y * (-v * q + u * s)) = (u * x + v * y) * q := by ring
        _ = 1 * q := by rw [hbez]
        _ = q := one_mul q
    · change v * (a : ℤ) = r; linarith
    · change v * b' + x * d' = s
      calc v * (x * q + y * s) + x * (-v * q + u * s) = (u * x + v * y) * s := by ring
        _ = 1 * s := by rw [hbez]
        _ = s := one_mul s
  have had' : (a : ℤ) * d' = (n : ℤ) := by
    have hdet_mul := congrArg Matrix.det hσ0M
    rw [Matrix.det_mul, σ₀.prop, one_mul, hdet] at hdet_mul
    simpa [Matrix.det_fin_two] using hdet_mul
  have hd'_pos : 0 < d' := by
    have haZ : (0 : ℤ) < (a : ℤ) := Int.natCast_pos.mpr ha_pos
    have hnZ : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
    nlinarith
  set d : ℕ := d'.toNat
  have hd_cast : (d : ℤ) = d' := Int.toNat_of_nonneg hd'_pos.le
  have hd_pos : 0 < d := by
    have : (0 : ℤ) < (d : ℤ) := by rw [hd_cast]; exact hd'_pos
    exact_mod_cast this
  have had : a * d = n := by
    have : ((a * d : ℕ) : ℤ) = (n : ℤ) := by rw [Nat.cast_mul, hd_cast]; exact had'
    exact_mod_cast this
  set k : ℤ := b' / (d : ℤ)
  set bZ : ℤ := b' % (d : ℤ)
  have hdZ_pos : (0 : ℤ) < (d : ℤ) := Int.natCast_pos.mpr hd_pos
  have hbZ_nonneg : 0 ≤ bZ := Int.emod_nonneg b' (ne_of_gt hdZ_pos)
  have hbZ_lt : bZ < (d : ℤ) := Int.emod_lt_of_pos b' hdZ_pos
  have hb'_eq : (d : ℤ) * k + bZ = b' := Int.mul_ediv_add_emod b' (d : ℤ)
  set b : ℕ := bZ.toNat
  have hb_cast : (b : ℤ) = bZ := Int.toNat_of_nonneg hbZ_nonneg
  have hb_lt : b < d := by
    have : (b : ℤ) < (d : ℤ) := by rw [hb_cast]; exact hbZ_lt
    exact_mod_cast this
  let Tk : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨σ₀ * Tk, a, b, d, ha_pos, hd_pos, had, hb_lt, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
  have hTk : (Tk : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ a b d = !![(a : ℤ), b'; 0, d'] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Tk, heckeMatZ, Matrix.mul_apply, Fin.sum_univ_two]
    · linarith
    · exact hd_cast
  rw [hTk, hσ0M]

/-- **Uniqueness of `2 × 2` Hermite Normal Form**:
if `σ · [[a₁, b₁], [0, d₁]] = [[a₂, b₂], [0, d₂]]` with `σ ∈ SL₂(ℤ)`, `a_i, d_i > 0`, `b_i < d_i`,
then `a₁ = a₂`, `b₁ = b₂`, and `d₁ = d₂`. -/
theorem hermiteNormalForm_unique
    {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {a₁ b₁ d₁ a₂ b₂ d₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : b₁ < d₁) (hb₂ : b₂ < d₂)
    (heq : (σ : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ a₁ b₁ d₁ = heckeMatZ a₂ b₂ d₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ d₁ = d₂ := by
  set α : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set β : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set γ : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set δ : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h10 : γ * (a₁ : ℤ) = 0 := by
    have h := congrFun (congrFun heq 1) 0
    simpa [heckeMatZ, Matrix.mul_apply, Fin.sum_univ_two, γ] using h
  have hγ : γ = 0 := (mul_eq_zero.mp h10).resolve_right (Int.natCast_ne_zero.mpr (ne_of_gt ha₁))
  have hdet : α * δ = 1 := by
    have h := σ.prop
    rw [Matrix.det_fin_two] at h
    change α * δ - β * γ = 1 at h
    rw [hγ, mul_zero, sub_zero] at h
    exact h
  have h00 : α * (a₁ : ℤ) = (a₂ : ℤ) := by
    have h := congrFun (congrFun heq 0) 0
    simpa [heckeMatZ, Matrix.mul_apply, Fin.sum_univ_two, α] using h
  have hα_pos : 0 < α := by
    have ha₁Z : (0 : ℤ) < (a₁ : ℤ) := Int.natCast_pos.mpr ha₁
    have ha₂Z : (0 : ℤ) < (a₂ : ℤ) := Int.natCast_pos.mpr ha₂
    nlinarith
  have hα : α = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · omega
  have hδ : δ = 1 := by rw [hα, one_mul] at hdet; exact hdet
  have ha_eq : a₁ = a₂ := by
    rw [hα, one_mul] at h00
    exact_mod_cast h00
  have h11 : δ * (d₁ : ℤ) = (d₂ : ℤ) := by
    have h := congrFun (congrFun heq 1) 1
    simpa [heckeMatZ, Matrix.mul_apply, Fin.sum_univ_two, γ, hγ, δ] using h
  have hd_eq : d₁ = d₂ := by
    rw [hδ, one_mul] at h11
    exact_mod_cast h11
  have h01 : α * (b₁ : ℤ) + β * (d₁ : ℤ) = (b₂ : ℤ) := by
    have h := congrFun (congrFun heq 0) 1
    simpa [heckeMatZ, Matrix.mul_apply, Fin.sum_univ_two, α, β] using h
  rw [hα, one_mul] at h01
  have hb₁Z : (b₁ : ℤ) < (d₁ : ℤ) := by exact_mod_cast hb₁
  have hb₂Z : (b₂ : ℤ) < (d₁ : ℤ) := by exact_mod_cast (hd_eq ▸ hb₂)
  have hβ0 : β = 0 := by nlinarith
  have hb_eq : b₁ = b₂ := by
    rw [hβ0, zero_mul, add_zero] at h01
    exact_mod_cast h01
  exact ⟨ha_eq, hb_eq, hd_eq⟩

/-- The finite index set of level-1 Hecke coset representatives `{(a, b) | a ∣ n, 0 ≤ b < n / a}`. -/
def heckeCosets (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  n.divisors.sigma fun a => Finset.range (n / a)

private lemma heckeCosets_spec {n : ℕ} (hn : 1 ≤ n) {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets n) :
    0 < x.1 ∧ 0 < n / x.1 ∧ x.1 * (n / x.1) = n ∧ x.2 < n / x.1 := by
  rcases Finset.mem_sigma.mp hx with ⟨ha, hb⟩
  have ha_dvd : x.1 ∣ n := (Nat.mem_divisors.mp ha).1
  have ha_pos : 0 < x.1 := Nat.pos_of_dvd_of_pos ha_dvd (by omega)
  have hd_pos : 0 < n / x.1 := Nat.div_pos (Nat.le_of_dvd (by omega) ha_dvd) ha_pos
  exact ⟨ha_pos, hd_pos, Nat.mul_div_cancel' ha_dvd, Finset.mem_range.mp hb⟩

private lemma map_heckeMatZ_eq_heckeMat (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (heckeMatZ a b d).map (Int.cast : ℤ → ℝ) =
      (heckeMat a b d ha hd : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeMatZ, heckeMat]

private lemma gl2R_eq_of_int_mat_eq
    (σ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (a b d a' b' d' : ℕ) (ha : 0 < a) (hd : 0 < d) (ha' : 0 < a') (hd' : 0 < d')
    (heq : (σ : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ a' b' d' =
      heckeMatZ a b d * (γ : Matrix (Fin 2) (Fin 2) ℤ)) :
    Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ σ * heckeMat a' b' d' ha' hd' =
      heckeMat a b d ha hd * Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ := by
  apply Units.ext
  have hmap := congrArg (RingHom.mapMatrix (Int.castRingHom ℝ)) heq
  simp only [map_mul, RingHom.mapMatrix_apply] at hmap
  have hcoe_σ : ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ σ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl
  have hcoe_γ : ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl
  change ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (heckeMat a' b' d' ha' hd' : Matrix (Fin 2) (Fin 2) ℝ) =
    (heckeMat a b d ha hd : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [hcoe_σ, hcoe_γ, ← map_heckeMatZ_eq_heckeMat a' b' d' ha' hd',
    ← map_heckeMatZ_eq_heckeMat a b d ha hd]
  exact hmap

private lemma heckeCoset_right_mul_exists {n : ℕ} (hn : 1 ≤ n)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets n) :
    ∃ (y : Σ _ : ℕ, ℕ) (_hy : y ∈ heckeCosets n) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      (σ : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ y.1 y.2 (n / y.1) =
        heckeMatZ x.1 x.2 (n / x.1) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨ha, hd, had, _⟩ := heckeCosets_spec hn hx
  have hdet : (heckeMatZ x.1 x.2 (n / x.1) * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = (n : ℤ) := by
    rw [Matrix.det_mul, γ.prop, mul_one]
    simp only [heckeMatZ, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, sub_zero]
    exact_mod_cast had
  obtain ⟨σ, a', b', d', ha', hd', had', hb', hfact⟩ :=
    hermiteNormalForm_exists (by omega : 0 < n) _ hdet
  have hd'_eq : n / a' = d' := by
    rw [← had', Nat.mul_div_cancel_left d' ha']
  have hy_mem : (⟨a', b'⟩ : Σ _ : ℕ, ℕ) ∈ heckeCosets n := by
    rw [heckeCosets, Finset.mem_sigma]
    refine ⟨Nat.mem_divisors.mpr ⟨⟨d', had'.symm⟩, by omega⟩, ?_⟩
    rw [Finset.mem_range, hd'_eq]
    exact hb'
  refine ⟨⟨a', b'⟩, hy_mem, σ, ?_⟩
  rw [hd'_eq]
  exact hfact

private def cosetAct (n : ℕ) (hn : 1 ≤ n) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  if hx : x ∈ heckeCosets n then
    Classical.choose (heckeCoset_right_mul_exists hn γ hx)
  else x

private lemma cosetAct_mem {n : ℕ} (hn : 1 ≤ n) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets n) :
    cosetAct n hn γ x ∈ heckeCosets n := by
  unfold cosetAct
  rw [dif_pos hx]
  exact Classical.choose (Classical.choose_spec (heckeCoset_right_mul_exists hn γ hx))

private lemma cosetAct_spec {n : ℕ} (hn : 1 ≤ n) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets n) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (σ : Matrix (Fin 2) (Fin 2) ℤ) *
          heckeMatZ (cosetAct n hn γ x).1 (cosetAct n hn γ x).2 (n / (cosetAct n hn γ x).1) =
        heckeMatZ x.1 x.2 (n / x.1) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  unfold cosetAct
  rw [dif_pos hx]
  exact Classical.choose_spec (Classical.choose_spec (heckeCoset_right_mul_exists hn γ hx))

private lemma cosetAct_inv_cancel {n : ℕ} (hn : 1 ≤ n) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets n) :
    cosetAct n hn γ⁻¹ (cosetAct n hn γ x) = x := by
  set y := cosetAct n hn γ x
  have hy : y ∈ heckeCosets n := cosetAct_mem hn γ hx
  set z := cosetAct n hn γ⁻¹ y
  have hz : z ∈ heckeCosets n := cosetAct_mem hn γ⁻¹ hy
  obtain ⟨σ₁, hσ₁⟩ := cosetAct_spec hn γ hx
  obtain ⟨σ₂, hσ₂⟩ := cosetAct_spec hn γ⁻¹ hy
  have hcomb : ((σ₁ * σ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      heckeMatZ z.1 z.2 (n / z.1) = heckeMatZ x.1 x.2 (n / x.1) := by
    calc ((σ₁ * σ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
            heckeMatZ z.1 z.2 (n / z.1)
        = (σ₁ : Matrix (Fin 2) (Fin 2) ℤ) *
            ((σ₂ : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ z.1 z.2 (n / z.1)) := by
            rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
      _ = (σ₁ : Matrix (Fin 2) (Fin 2) ℤ) *
            (heckeMatZ y.1 y.2 (n / y.1) *
              ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) := by
            rw [hσ₂]
      _ = ((σ₁ : Matrix (Fin 2) (Fin 2) ℤ) * heckeMatZ y.1 y.2 (n / y.1)) *
            ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
            rw [Matrix.mul_assoc]
      _ = (heckeMatZ x.1 x.2 (n / x.1) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) *
            ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
            rw [hσ₁]
      _ = heckeMatZ x.1 x.2 (n / x.1) *
            ((γ * γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
            rw [Matrix.mul_assoc, Matrix.SpecialLinearGroup.coe_mul]
      _ = heckeMatZ x.1 x.2 (n / x.1) := by simp
  obtain ⟨hz1, _, _, hz4⟩ := heckeCosets_spec hn hz
  obtain ⟨hx1, _, _, hx4⟩ := heckeCosets_spec hn hx
  obtain ⟨h1, h2, _⟩ := hermiteNormalForm_unique hz1 hx1 hz4 hx4 hcomb
  rcases z with ⟨z1, z2⟩
  rcases x with ⟨x1, x2⟩
  dsimp only at h1 h2
  subst h1; subst h2; rfl

/-- Evaluating the trivial modulus-1 Dirichlet character on any `a : ℕ` yields `1`. -/
@[simp]
theorem trivialChar_one_apply (a : ℕ) :
    (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1 := by
  have h : (a : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h, map_one]

/-- Rewriting `slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f` as a single sum over `heckeCosets n`. -/
theorem slashHeckeOp_levelOne_eq_sum_cosets (k n : ℕ)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f τ =
      ∑ x ∈ heckeCosets n,
        if h : 0 < x.1 ∧ 0 < n / x.1 then
          (SlashAction.map (k : ℤ) (heckeMat x.1 x.2 (n / x.1) h.1 h.2) f) τ
        else 0 := by
  unfold slashHeckeOp heckeCosets
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [trivialChar_one_apply, one_mul]

private lemma slashAction_finset_sum {ι : Type*} (s : Finset ι) (k : ℤ) (g : GL (Fin 2) ℝ)
    (F : ι → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    SlashAction.map k g (fun z => ∑ i ∈ s, F i z) τ =
      ∑ i ∈ s, SlashAction.map k g (F i) τ := by
  simp only [ModularForm.slash_def, map_sum, Finset.sum_mul]

/-- **Unconditional `SL₂(ℤ)` Slash-Invariance of the Level-1 Hecke Operator**:
for EVERY weight `k : ℕ`, EVERY `n ≥ 1`, and EVERY `SL₂(ℤ)`-invariant function `f`,
`slashHeckeOp k 1 n f` is again `SL₂(ℤ)`-invariant of weight `k`! -/
theorem slashHeckeOp_levelOne_slash_invariant (k : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      SlashAction.map (k : ℤ) (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) f = f)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (k : ℤ) (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ)
      (slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f) =
      slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f := by
  funext τ
  have hfun : slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f =
      fun z => ∑ x ∈ heckeCosets n,
        (if h : 0 < x.1 ∧ 0 < n / x.1 then
          SlashAction.map (k : ℤ) (heckeMat x.1 x.2 (n / x.1) h.1 h.2) f
        else 0) z := by
    funext z
    rw [slashHeckeOp_levelOne_eq_sum_cosets k n f z]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> rfl
  rw [hfun, slashAction_finset_sum]
  refine Finset.sum_nbij' (cosetAct n hn γ) (cosetAct n hn γ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact cosetAct_mem hn γ hx
  · intro y hy; exact cosetAct_mem hn γ⁻¹ hy
  · intro x hx; exact cosetAct_inv_cancel hn γ hx
  · intro y hy
    simpa [inv_inv] using cosetAct_inv_cancel hn γ⁻¹ hy
  · intro x hx
    set y := cosetAct n hn γ x
    have hy : y ∈ heckeCosets n := cosetAct_mem hn γ hx
    obtain ⟨hx1, hx2, _, _⟩ := heckeCosets_spec hn hx
    obtain ⟨hy1, hy2, _, _⟩ := heckeCosets_spec hn hy
    have hxp : 0 < x.1 ∧ 0 < n / x.1 := ⟨hx1, hx2⟩
    have hyp : 0 < y.1 ∧ 0 < n / y.1 := ⟨hy1, hy2⟩
    rw [dif_pos hxp, dif_pos hyp]
    obtain ⟨σ, hσ⟩ := cosetAct_spec hn γ hx
    have hgl := gl2R_eq_of_int_mat_eq σ γ x.1 x.2 (n / x.1) y.1 y.2 (n / y.1) hx1 hx2 hy1 hy2 hσ
    have hslash : SlashAction.map (k : ℤ) (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ)
        (SlashAction.map (k : ℤ) (heckeMat x.1 x.2 (n / x.1) hx1 hx2) f) =
        SlashAction.map (k : ℤ) (heckeMat y.1 y.2 (n / y.1) hy1 hy2) f := by
      calc SlashAction.map (k : ℤ) (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ)
              (SlashAction.map (k : ℤ) (heckeMat x.1 x.2 (n / x.1) hx1 hx2) f)
          = SlashAction.map (k : ℤ)
              (heckeMat x.1 x.2 (n / x.1) hx1 hx2 * Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) f :=
              (SlashAction.slash_mul (k : ℤ) _ _ f).symm
        _ = SlashAction.map (k : ℤ)
              (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ σ * heckeMat y.1 y.2 (n / y.1) hy1 hy2) f := by
              rw [hgl]
        _ = SlashAction.map (k : ℤ) (heckeMat y.1 y.2 (n / y.1) hy1 hy2)
              (SlashAction.map (k : ℤ) (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ σ) f) :=
              SlashAction.slash_mul (k : ℤ) _ _ f
        _ = SlashAction.map (k : ℤ) (heckeMat y.1 y.2 (n / y.1) hy1 hy2) f := by
              rw [hf σ]
    exact congrFun hslash τ

/-- Holomorphicity (`MDiff`) of `slashHeckeOp k 1 n f` whenever `f` is holomorphic (`MDiff`). -/
theorem slashHeckeOp_levelOne_mdifferentiable {k : ℕ} (hk : 1 ≤ k) (n : ℕ)
    {f : UpperHalfPlane → ℂ} (hf : MDiff f) :
    MDiff (slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f) := by
  have hfun : slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f =
      fun τ => ∑ x ∈ heckeCosets n,
        if h : 0 < x.1 ∧ 0 < n / x.1 then
          f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ) *
            ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
        else 0 := by
    funext τ
    rw [slashHeckeOp_levelOne_eq_sum_cosets k n f τ]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · exact heckeMat_slash_apply hk x.1 x.2 (n / x.1) h.1 h.2 f τ
    · rfl
  rw [hfun, UpperHalfPlane.mdifferentiable_iff]
  have hcomp :
      (fun τ : UpperHalfPlane => ∑ x ∈ heckeCosets n,
        if h : 0 < x.1 ∧ 0 < n / x.1 then
          f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ) *
            ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
        else 0) ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane) =
      fun z : ℂ => ∑ x ∈ heckeCosets n,
        ((fun τ : UpperHalfPlane =>
          if h : 0 < x.1 ∧ 0 < n / x.1 then
            f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ) *
              ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
          else 0) ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) z := rfl
  rw [hcomp]
  refine DifferentiableOn.fun_sum fun x _ => ?_
  by_cases h : 0 < x.1 ∧ 0 < n / x.1
  · have hterm :
        (fun τ : UpperHalfPlane =>
          if h' : 0 < x.1 ∧ 0 < n / x.1 then
            f (heckeMat x.1 x.2 (n / x.1) h'.1 h'.2 • τ) *
              ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
          else 0) =
        fun τ : UpperHalfPlane =>
          f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ) *
            ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ)) := by
      funext τ; exact dif_pos h
    rw [hterm]
    have hmd : MDiff (fun τ : UpperHalfPlane => f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ)) :=
      hf.comp (UpperHalfPlane.mdifferentiable_smul (heckeMat_det_pos x.1 x.2 (n / x.1) h.1 h.2))
    have hdiff := UpperHalfPlane.mdifferentiable_iff.mp hmd
    exact hdiff.mul_const ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
  · have hterm :
        (fun τ : UpperHalfPlane =>
          if h' : 0 < x.1 ∧ 0 < n / x.1 then
            f (heckeMat x.1 x.2 (n / x.1) h'.1 h'.2 • τ) *
              ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
          else 0) = fun _ => (0 : ℂ) := by
      funext τ; exact dif_neg h
    rw [hterm]
    exact differentiableOn_const (0 : ℂ)

/-- Imaginary part scaling under an upper-triangular Hecke matrix:
`Im(heckeMat a b d • τ) = (a / d) * Im(τ)`. -/
private lemma im_heckeMat_smul (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : UpperHalfPlane) :
    (heckeMat a b d ha hd • τ).im = ((a : ℝ) / (d : ℝ)) * τ.im := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq, heckeMat_det,
    abs_of_pos (by positivity : (0 : ℝ) < (a : ℝ) * (d : ℝ))]
  have hdenom : UpperHalfPlane.denom (heckeMat a b d ha hd) (τ : ℂ) = (d : ℂ) := by
    simp [UpperHalfPlane.denom, heckeMat]
  rw [hdenom, Complex.normSq_natCast]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  field_simp [hd0]

private lemma isZeroAtImInfty_zero :
    UpperHalfPlane.IsZeroAtImInfty (fun _ : UpperHalfPlane => (0 : ℂ)) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  exact ⟨0, fun _ _ => by simpa using hε.le⟩

private lemma isZeroAtImInfty_add {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsZeroAtImInfty f) (hg : UpperHalfPlane.IsZeroAtImInfty g) :
    UpperHalfPlane.IsZeroAtImInfty (fun τ => f τ + g τ) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨A₁, hA₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨A₂, hA₂⟩ := hg (ε / 2) (by linarith)
  refine ⟨max A₁ A₂, fun z hz => ?_⟩
  have h1 := hA₁ z (le_trans (le_max_left A₁ A₂) hz)
  have h2 := hA₂ z (le_trans (le_max_right A₁ A₂) hz)
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

private lemma isZeroAtImInfty_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i ∈ s, UpperHalfPlane.IsZeroAtImInfty (F i)) :
    UpperHalfPlane.IsZeroAtImInfty (fun τ => ∑ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isZeroAtImInfty_zero
  | @insert a s ha ih =>
    have h1 : UpperHalfPlane.IsZeroAtImInfty (F a) := hF a (Finset.mem_insert_self a s)
    have h2 : UpperHalfPlane.IsZeroAtImInfty (fun τ => ∑ i ∈ s, F i τ) :=
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using isZeroAtImInfty_add h1 h2

/-- Vanishing at `i∞` of `slashHeckeOp k 1 n f` whenever `f` vanishes at `i∞`. -/
theorem slashHeckeOp_levelOne_isZeroAtImInfty {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n)
    {f : UpperHalfPlane → ℂ} (hf : UpperHalfPlane.IsZeroAtImInfty f) :
    UpperHalfPlane.IsZeroAtImInfty (slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f) := by
  have hfun : slashHeckeOp k (1 : DirichletCharacter ℂ 1) n f =
      fun τ => ∑ x ∈ heckeCosets n,
        if h : 0 < x.1 ∧ 0 < n / x.1 then
          f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ) *
            ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
        else 0 := by
    funext τ
    rw [slashHeckeOp_levelOne_eq_sum_cosets k n f τ]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · exact heckeMat_slash_apply hk x.1 x.2 (n / x.1) h.1 h.2 f τ
    · rfl
  rw [hfun]
  refine isZeroAtImInfty_finset_sum (heckeCosets n) _ fun x hx => ?_
  obtain ⟨ha, hd, _, _⟩ := heckeCosets_spec hn hx
  have hboth : 0 < x.1 ∧ 0 < n / x.1 := ⟨ha, hd⟩
  have hterm :
      (fun τ : UpperHalfPlane =>
        if h : 0 < x.1 ∧ 0 < n / x.1 then
          f (heckeMat x.1 x.2 (n / x.1) h.1 h.2 • τ) *
            ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ))
        else 0) =
      fun τ : UpperHalfPlane =>
        f (heckeMat x.1 x.2 (n / x.1) ha hd • τ) *
          ((x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ)) := by
    funext τ; exact dif_pos hboth
  rw [hterm, UpperHalfPlane.isZeroAtImInfty_iff]
  set c : ℂ := (x.1 : ℂ) ^ (k - 1) / ((n / x.1 : ℕ) : ℂ)
  have hc_pos : 0 < ‖c‖ := by
    apply norm_pos_iff.mpr
    exact div_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (ne_of_gt ha)))
      (Nat.cast_ne_zero.mpr (ne_of_gt hd))
  intro ε hε
  obtain ⟨A, hA⟩ := (UpperHalfPlane.isZeroAtImInfty_iff.mp hf) (ε / ‖c‖) (div_pos hε hc_pos)
  have haR : (0 : ℝ) < (x.1 : ℝ) := Nat.cast_pos.mpr ha
  have hdR : (0 : ℝ) < ((n / x.1 : ℕ) : ℝ) := Nat.cast_pos.mpr hd
  refine ⟨A * ((n / x.1 : ℕ) : ℝ) / (x.1 : ℝ), fun z hz => ?_⟩
  have him_ge : A ≤ (heckeMat x.1 x.2 (n / x.1) ha hd • z).im := by
    rw [im_heckeMat_smul]
    have hmul : A * ((n / x.1 : ℕ) : ℝ) / (x.1 : ℝ) * ((x.1 : ℝ) / ((n / x.1 : ℕ) : ℝ)) = A := by
      field_simp [ne_of_gt haR, ne_of_gt hdR]
    calc A = A * ((n / x.1 : ℕ) : ℝ) / (x.1 : ℝ) * ((x.1 : ℝ) / ((n / x.1 : ℕ) : ℝ)) := hmul.symm
      _ ≤ z.im * ((x.1 : ℝ) / ((n / x.1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hz (div_nonneg haR.le hdR.le)
      _ = ((x.1 : ℝ) / ((n / x.1 : ℕ) : ℝ)) * z.im := mul_comm _ _
  have hfz := hA (heckeMat x.1 x.2 (n / x.1) ha hd • z) him_ge
  rw [norm_mul]
  calc ‖f (heckeMat x.1 x.2 (n / x.1) ha hd • z)‖ * ‖c‖
      ≤ (ε / ‖c‖) * ‖c‖ := mul_le_mul_of_nonneg_right hfz (norm_nonneg c)
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hc_pos)

/-- Every level-1 cusp form `f : CuspForm SL2ZRange k` vanishes at `i∞`. -/
private lemma cuspForm_SL2Z_isZeroAtImInfty {k : ℤ} (f : CuspForm SL2ZRange k) :
    UpperHalfPlane.IsZeroAtImInfty (f : UpperHalfPlane → ℂ) := by
  have hcusp : IsCusp OnePoint.infty SL2ZRange :=
    (inferInstance : Fact (IsCusp OnePoint.infty SL2ZRange)).out
  have hzero := f.zero_at_cusps' hcusp
  have hall := (OnePoint.isZeroAt_iff_forall_SL2Z hcusp).mp hzero
  have h1 := hall 1 (by simp)
  simpa using h1

/-- **Unconditional Level-1 Hecke Endomorphism on `CuspForm SL2ZRange k`**:
for EVERY weight `k ≥ 1`, EVERY `n ≥ 1`, and EVERY level-1 cusp form `f ∈ S_k(SL₂(ℤ))`,
`slashHeckeOp k 1 n f` is again a genuine weight-`k` `SL₂(ℤ)` cusp form! -/
def heckeCuspForm (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (f : CuspForm SL2ZRange (k : ℤ)) : CuspForm SL2ZRange (k : ℤ) where
  toSlashInvariantForm :=
    { toFun := slashHeckeOp k (1 : DirichletCharacter ℂ 1) n (f : UpperHalfPlane → ℂ)
      slash_action_eq' := by
        intro g hg
        rcases hg with ⟨γ, rfl⟩
        exact slashHeckeOp_levelOne_slash_invariant k hn (f : UpperHalfPlane → ℂ)
          (fun σ => f.slash_action_eq' _ ⟨σ, rfl⟩) γ }
  holo' := slashHeckeOp_levelOne_mdifferentiable hk n f.holo'
  zero_at_cusps' := by
    intro c hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv := slashHeckeOp_levelOne_slash_invariant k hn (f : UpperHalfPlane → ℂ)
      (fun σ => f.slash_action_eq' _ ⟨σ, rfl⟩) γ
    change UpperHalfPlane.IsZeroAtImInfty
      (SlashAction.map (k : ℤ) (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ)
        (slashHeckeOp k (1 : DirichletCharacter ℂ 1) n (f : UpperHalfPlane → ℂ)))
    rw [hinv]
    exact slashHeckeOp_levelOne_isZeroAtImInfty hk hn (cuspForm_SL2Z_isZeroAtImInfty f)

@[simp]
theorem heckeCuspForm_coe (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (f : CuspForm SL2ZRange (k : ℤ)) :
    (heckeCuspForm k hk n hn f : UpperHalfPlane → ℂ) =
      slashHeckeOp k (1 : DirichletCharacter ℂ 1) n (f : UpperHalfPlane → ℂ) :=
  rfl

/-- Exact Fourier coefficients of `heckeCuspForm k hk n hn f`:
`coeff m (qExpansion 1 (T_n f)) = heckeOp k 1 n (coeff · (qExpansion 1 f)) m`. -/
theorem heckeCuspForm_qExpansion_coeff (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (f : CuspForm SL2ZRange (k : ℤ)) (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (heckeCuspForm k hk n hn f : UpperHalfPlane → ℂ)) =
      heckeOp k (1 : DirichletCharacter ℂ 1) n
        (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) m := by
  have hhas : ∀ τ : UpperHalfPlane,
      HasSum (fun M : ℕ =>
        heckeOp k (1 : DirichletCharacter ℂ 1) n
          (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) M •
          Function.Periodic.qParam 1 (τ : ℂ) ^ M)
        (heckeCuspForm k hk n hn f τ) := by
    intro τ
    simpa [smul_eq_mul, heckeCuspForm_coe] using
      modularForm_slashHeckeOp_hasSum_qExpansion hk one_mem_strictPeriods_SL
        (1 : DirichletCharacter ℂ 1) hn f τ
  exact (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL hhas m).symm

end HermiteNormalFormAndHeckeAction

/-! ## Section 3: UNCONDITIONAL PROOF OF MORDELL'S 1917 THEOREM (`T_n Δ = τ(n) Δ`) -/

section MordellTheorem

/-- **MORDELL'S 1917 THEOREM (CuspForm Form)**:
for EVERY `n ≥ 1`, `T_n Δ = τ(n) • Δ` in `CuspForm SL2ZRange 12`! -/
theorem heckeCuspForm_ramanujanDelta {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm 12 (by norm_num) n hn ramanujanDelta =
      (ramanujanTau n : ℂ) • ramanujanDelta := by
  have h1 := cuspForm_SL2Z_weight_twelve_eq_smul_delta
    (heckeCuspForm 12 (by norm_num) n hn ramanujanDelta)
  have hc1 :
      PowerSeries.coeff 1
        (UpperHalfPlane.qExpansion 1
          (heckeCuspForm 12 (by norm_num) n hn ramanujanDelta : UpperHalfPlane → ℂ)) =
        (ramanujanTau n : ℂ) := by
    rw [heckeCuspForm_qExpansion_coeff 12 (by norm_num) n hn ramanujanDelta 1,
      heckeOp_apply_one 12 (1 : DirichletCharacter ℂ 1) hn,
      ← ramanujanTau_cast_eq_qExpansion_coeff n]
  rw [hc1] at h1
  exact h1

/-- **MORDELL'S 1917 THEOREM (Slash-Hecke Form)**:
for EVERY `n ≥ 1`, `slashHeckeOp 12 1 n Δ = (ramanujanTau n : ℂ) • Δ` as functions on `ℍ`! -/
theorem slashHeckeOp_ramanujanDelta {n : ℕ} (hn : 1 ≤ n) :
    slashHeckeOp 12 (1 : DirichletCharacter ℂ 1) n (ramanujanDelta : UpperHalfPlane → ℂ) =
      (ramanujanTau n : ℂ) • (ramanujanDelta : UpperHalfPlane → ℂ) := by
  rw [← heckeCuspForm_coe 12 (by norm_num) n hn ramanujanDelta,
    heckeCuspForm_ramanujanDelta hn, FunLike.coe_smul]

/-- **UNCONDITIONAL NORMALIZED HECKE EIGENFORM THEOREM FOR RAMANUJAN'S `Δ`**:
`(fun n => (ramanujanTau n : ℂ))` is unconditionally a normalized simultaneous Hecke eigenform of
weight `12` and trivial Nebentypus `(1 : DirichletCharacter ℂ 1)` with eigenvalues `τ(n)`! -/
theorem isNormalizedHeckeEigenform_ramanujanTau :
    IsNormalizedHeckeEigenform 12 (1 : DirichletCharacter ℂ 1)
      (fun n => (ramanujanTau n : ℂ)) (fun n => (ramanujanTau n : ℂ)) := by
  refine ⟨by simp [ramanujanTau_one], fun n hn => ?_⟩
  funext m
  have hcoeff_fun :
      (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ))) =
        fun j => (ramanujanTau j : ℂ) := by
    funext j; exact (ramanujanTau_cast_eq_qExpansion_coeff j).symm
  have h1 := heckeCuspForm_qExpansion_coeff 12 (by norm_num) n hn ramanujanDelta m
  rw [hcoeff_fun, heckeCuspForm_ramanujanDelta hn, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL
      (ramanujanTau n : ℂ) ramanujanDelta,
    map_smul, smul_eq_mul, ← ramanujanTau_cast_eq_qExpansion_coeff m] at h1
  simpa [Pi.smul_apply, smul_eq_mul] using h1.symm

end MordellTheorem

/-! ## Section 4: UNCONDITIONAL RAMANUJAN MULTIPLICATIVITY, RECURRENCE & `L(Δ, s)` EULER PRODUCT -/

section RamanujanConjecturesAndEulerProduct

/-- **UNCONDITIONAL RAMANUJAN MULTIPLICATIVITY (Mordell 1917)**:
for ALL `m, n : ℕ` with `Nat.Coprime m n`, `τ(m * n) = τ(m) * τ(n)` (`0` assumptions!). -/
theorem ramanujanTau_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    ramanujanTau (m * n) = ramanujanTau m * ramanujanTau n := by
  by_cases hm : m = 0
  · subst hm; simp [ramanujanTau_zero]
  by_cases hn : n = 0
  · subst hn; simp [ramanujanTau_zero]
  have hC := eigenform_isMultiplicative isNormalizedHeckeEigenform_ramanujanTau
    (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop
  exact Int.cast_injective (α := ℂ) (by simpa using hC)

/-- **UNCONDITIONAL RAMANUJAN PRIME-POWER RECURRENCE (Mordell 1917)**:
for EVERY prime `p` and EVERY `r : ℕ`,
`τ(p^(r + 2)) = τ(p) * τ(p^(r + 1)) - p^11 * τ(p^r)` (`0` assumptions!). -/
theorem ramanujanTau_prime_pow_recurrence {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ramanujanTau (p ^ (r + 2)) =
      ramanujanTau p * ramanujanTau (p ^ (r + 1)) - (p : ℤ) ^ 11 * ramanujanTau (p ^ r) := by
  have hC := eigenform_prime_pow_recurrence isNormalizedHeckeEigenform_ramanujanTau hp r
  rw [trivialChar_one_apply, one_mul] at hC
  exact Int.cast_injective (α := ℂ) (by simpa using hC)

/-- Immediate verification of higher Ramanujan tau values from Mordell's theorem:
`τ(6) = τ(2) * τ(3) = -6048`, `τ(8) = 84480`, `τ(9) = -113643`. -/
theorem ramanujanTau_six : ramanujanTau 6 = -6048 := by
  have h := ramanujanTau_mul_of_coprime (m := 2) (n := 3) (by decide)
  rw [show 2 * 3 = 6 by norm_num, ramanujanTau_two, ramanujanTau_three] at h
  norm_num at h
  exact h

theorem ramanujanTau_eight : ramanujanTau 8 = 84480 := by
  have h := ramanujanTau_prime_pow_recurrence (p := 2) Nat.prime_two 1
  norm_num [ramanujanTau_two, ramanujanTau_four] at h
  exact h

theorem ramanujanTau_nine : ramanujanTau 9 = -113643 := by
  have h := ramanujanTau_prime_pow_recurrence (p := 3) Nat.prime_three 0
  norm_num [ramanujanTau_one, ramanujanTau_three] at h
  exact h

/-- Unconditional absolute convergence of `L(Δ, s) = ∑_{n ≥ 1} τ(n) n^{-s}` on `Re(s) > 7`
(from Hecke's cusp-form bound `|τ(n)| = O(n^6)`). -/
theorem LSeriesSummable_ramanujanTau {s : ℂ} (hs : 7 < s.re) :
    LSeriesSummable (fun n => (ramanujanTau n : ℂ)) s := by
  have hfun : (fun n : ℕ => (ramanujanTau n : ℂ)) =
      fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)) := by
    funext n; exact ramanujanTau_cast_eq_qExpansion_coeff n
  rw [hfun]
  have hbigO :
      (fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ))) =O[Filter.atTop]
        fun n : ℕ => ((n : ℝ) ^ ((12 : ℝ) / 2)) := by
    have h := CuspFormClass.qExpansion_isBigO ramanujanDelta
    rw [Subgroup.strictWidthInfty_SL2Z] at h
    exact h
  refine LSeriesSummable_of_isBigO_rpow (x := (12 : ℝ) / 2 + 1) (by linarith) ?_
  simpa [add_sub_cancel_right] using hbigO

private lemma degree2EulerFactor_ramanujanDelta (p : ℕ) (s : ℂ) :
    degree2EulerFactor 12 (1 : DirichletCharacter ℂ 1) (ramanujanTau p : ℂ) p s =
      (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹ := by
  simp only [degree2EulerFactor, trivialChar_one_apply, one_mul]
  norm_num

/-- **UNCONDITIONAL DEGREE-2 EULER PRODUCT FOR `L(Δ, s)` (Mordell 1917, `0` Assumptions!)**:
for EVERY `s : ℂ` with `7 < s.re`:
$$L(\Delta, s) = \sum_{n=1}^{\infty} \frac{\tau(n)}{n^s} =
  \prod_{p} \left(1 - \tau(p)\, p^{-s} + p^{11 - 2s}\right)^{-1}.$$ -/
theorem ramanujanDelta_LSeries_eulerProduct {s : ℂ} (hs : 7 < s.re) :
    LSeries (fun n => (ramanujanTau n : ℂ)) s =
      ∏' p : Nat.Primes,
        (1 - (ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ := by
  have h := eigenform_LSeries_eulerProduct isNormalizedHeckeEigenform_ramanujanTau
    (LSeriesSummable_ramanujanTau hs)
  rw [← h]
  refine tprod_congr fun p => ?_
  exact degree2EulerFactor_ramanujanDelta p.1 s

/-- Finite-prime-product convergence (`Filter.Tendsto`) form of the `L(Δ, s)` Euler product on
`Re(s) > 7`. -/
theorem ramanujanDelta_LSeries_eulerProduct_tendsto {s : ℂ} (hs : 7 < s.re) :
    Filter.Tendsto
      (fun B : ℕ => ∏ p ∈ B.primesBelow,
        (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹)
      Filter.atTop (nhds (LSeries (fun n => (ramanujanTau n : ℂ)) s)) := by
  have h := eigenform_LSeries_eulerProduct_tendsto isNormalizedHeckeEigenform_ramanujanTau
    (LSeriesSummable_ramanujanTau hs)
  refine h.congr fun B => ?_
  refine Finset.prod_congr rfl fun p _ => ?_
  exact degree2EulerFactor_ramanujanDelta p s

/-- **UNCONDITIONAL DEGREE-2 EULER PRODUCT DIRECTLY ON MATHLIB'S `ModularForm.L`** for `Δ`:
for EVERY `s : ℂ` with `7 < s.re`,
`ModularForm.L (0 < 12) ramanujanDelta s = ∏' p, (1 - τ(p) p^{-s} + p^{11 - 2s})⁻¹`. -/
theorem ramanujanDelta_modularL_eulerProduct {s : ℂ} (hs : 7 < s.re) :
    ModularForm.L (by norm_num : (0 : ℤ) < 12) ramanujanDelta s =
      ∏' p : Nat.Primes,
        (1 - (ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ := by
  have heig : IsNormalizedHeckeEigenform (12 : ℤ).toNat (1 : DirichletCharacter ℂ 1)
      (fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ)))
      (fun n => (ramanujanTau n : ℂ)) := by
    have hfun : (fun n => PowerSeries.coeff n
        (UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ))) =
        fun n => (ramanujanTau n : ℂ) := by
      funext n; exact (ramanujanTau_cast_eq_qExpansion_coeff n).symm
    rw [hfun]
    exact isNormalizedHeckeEigenform_ramanujanTau
  have h := cuspForm_eigenform_L_eulerProduct Subgroup.strictWidthInfty_SL2Z
    (by norm_num : (0 : ℤ) < 12) ramanujanDelta (1 : DirichletCharacter ℂ 1)
    (fun n => (ramanujanTau n : ℂ)) heig (by norm_num; linarith)
  rw [← h]
  refine tprod_congr fun p => ?_
  rw [← ramanujanTau_cast_eq_qExpansion_coeff p.1]
  exact degree2EulerFactor_ramanujanDelta p.1 s

/-- Exact identity `LSeries (fun n => (ramanujanTau n : ℂ)) s = ModularForm.L _ ramanujanDelta s`
for all `s` with `7 < s.re`. -/
theorem ramanujanDelta_LSeries_eq_modularL {s : ℂ} (hs : 7 < s.re) :
    LSeries (fun n => (ramanujanTau n : ℂ)) s =
      ModularForm.L (by norm_num : (0 : ℤ) < 12) ramanujanDelta s := by
  rw [ramanujanDelta_LSeries_eulerProduct hs, ramanujanDelta_modularL_eulerProduct hs]

end RamanujanConjecturesAndEulerProduct

end

end RHDirect.Stage8RamanujanDelta
