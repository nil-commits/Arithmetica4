import RHDirect.Stage7EisensteinSeries
import RHDirect.Stage8RamanujanDelta
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# RHDirect.Stage9ModularDerivatives

**UNCONDITIONAL RAMANUJAN QUASI-MODULAR DIFFERENTIAL EQUATIONS FOR `E₂, E₄, E₆`, THE SERRE
DERIVATIVE `∂_k : M_k(SL₂(ℤ)) → M_{k+2}(SL₂(ℤ))`, THE LOGARITHMIC DERIVATIVE `q d/dq Δ = E₂ · Δ`,
THE `τ(n)` CONVOLUTION RECURRENCE, AND THE DEDEKIND–JACOBI PRODUCT FORMULA
`Δ(τ) = q ∏_{n ≥ 1} (1 - q^n)^24`** in pure Mathlib `v4.33.1`
(`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Formal Power Series `E₂, E₄, E₆` & Euler Derivation `thetaDeriv` (`q d/dq`)**:
   - `thetaDeriv f := PowerSeries.X * PowerSeries.derivative R f` with exact coefficient action
     `coeff n (thetaDeriv f) = n * coeff n f`, Leibniz product rule, power rule, ring-hom
     compatibility, and uniqueness of first-order formal ODE solutions (`eq_of_thetaDeriv_eq_mul`).
   - Exact integer and rational `q`-series `E2SeriesZ`, `E4SeriesZ`, `E6SeriesZ : PowerSeries ℤ`
     and `E2Series`, `E4Series`, `E6Series : PowerSeries ℚ`, together with
     `ramanujanDeltaPowerSeriesQ : PowerSeries ℚ`.

2. **Analytic `E₂(τ)`, Quasi-Modular Transformation, & `q`-Expansion Action of `1/(2πi) d/dτ`**:
   - `E2_S_smul : E2 (ModularGroup.S • τ) = τ² * E2 τ + 6 * τ / (π * I)` and `E2_T_smul`,
     plus the elliptic special value `E2_at_I : E2 UpperHalfPlane.I = 3 / π`.
   - `qExpansion_normalizedDerivOfComplex`: for EVERY `1`-periodic holomorphic function `f`
     bounded at `i∞` (covering both modular forms and quasi-modular `E₂`),
     `UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex f) = thetaDeriv (qExpansion 1 f)`.

3. **Serre Derivative `serreDeriv : M_k(SL₂(ℤ)) → M_{k+2}(SL₂(ℤ))` & Ramanujan's Three
   Differential Equations (1916!)**:
   - `serreDeriv k f : ModularForm SL2ZRange (k + 2)` implementing `(1/(2πi)) f' - (k/12) E₂ f`.
   - `ramanujan_diff_E4`: `thetaDeriv E4Series = (1 / 3 : ℚ) • (E2Series * E4Series - E6Series)`
     (and integer form `3 * thetaDeriv E4SeriesZ = E2SeriesZ * E4SeriesZ - E6SeriesZ`).
   - `ramanujan_diff_E6`: `thetaDeriv E6Series = (1 / 2 : ℚ) • (E2Series * E6Series - E4Series ^ 2)`
     (and integer form `2 * thetaDeriv E6SeriesZ = E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2`).
   - `ramanujan_diff_E2`: `thetaDeriv E2Series = (1 / 12 : ℚ) • (E2Series ^ 2 - E4Series)`
     (and integer form `12 * thetaDeriv E2SeriesZ = E2SeriesZ ^ 2 - E4SeriesZ`).
   - Explicit divisor-sum convolution identities (`sigma1_convolution`,
     `sigma3_sigma1_convolution`, `sigma5_sigma1_convolution`).

4. **Logarithmic Derivative `q d/dq Δ = E₂ · Δ`, `τ(n)` Recurrence, & Unconditional Dedekind–Jacobi
   Infinite Product Formula (`Δ = q ∏_{n ≥ 1} (1 - q^n)^24`)**:
   - `thetaDeriv_deltaZ_eq_E2_mul_deltaZ` & `thetaDeriv_delta_eq_E2_mul_delta`:
     `thetaDeriv ramanujanDeltaPowerSeriesQ = E2Series * ramanujanDeltaPowerSeriesQ`.
   - `serreDeriv_ramanujanDelta_eq_zero` & `normalizedDerivOfComplex_delta_eq_E2_mul_delta`.
   - `ramanujanTau_recurrence_sigma1`: for every `n ≥ 1`,
     `(n - 1) * τ(n) = -24 * ∑_{k = 1}^{n - 1} σ₁(k) * τ(n - k)` (plus `ramanujanTau_five = 4830`).
   - `eulerProd24 : PowerSeries ℤ` (stabilized formal product `X * ∏_{n ≥ 1} (1 - X^n)^24`),
     `thetaDeriv_eulerProd24 : thetaDeriv eulerProd24 = E2SeriesZ * eulerProd24`,
     **`ramanujanDelta_eq_q_mul_prod_one_sub_pow_24 : ramanujanDeltaPowerSeriesZ = eulerProd24`**,
     and the analytic product **`delta_eq_euler_product_24`**:
     `ramanujanDelta τ = q * ∏' n : ℕ+, (1 - q ^ (n : ℕ)) ^ 24`.
-/

open Complex Real Filter Module Submodule Finset
open RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries RHDirect.Stage8RamanujanDelta
open scoped BigOperators UpperHalfPlane ModularForm Topology Manifold

namespace RHDirect.Stage9ModularDerivatives

noncomputable section

/-! ## Section 1: Formal Euler Operator `thetaDeriv`, ODE Uniqueness, & Formal `E₂, E₄, E₆` Series -/

section FormalPowerSeriesAndThetaDeriv

/-- **Formal Euler Derivation `θ = q d/dq`** on `PowerSeries R`:
`thetaDeriv f = X * f'`, acting on coefficients as `a_n ↦ n * a_n`. -/
def thetaDeriv {R : Type*} [CommRing R] (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.X * PowerSeries.derivative R f

/-- Exact coefficient action of `thetaDeriv`: `coeff n (thetaDeriv f) = n * coeff n f`. -/
theorem coeff_thetaDeriv {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (thetaDeriv f) = (n : R) * PowerSeries.coeff n f := by
  unfold thetaDeriv
  cases n with
  | zero =>
    simp [PowerSeries.coeff_zero_X_mul]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

@[simp]
theorem coeff_zero_thetaDeriv {R : Type*} [CommRing R] (f : PowerSeries R) :
    PowerSeries.coeff 0 (thetaDeriv f) = 0 := by
  rw [coeff_thetaDeriv]
  simp

theorem thetaDeriv_add {R : Type*} [CommRing R] (f g : PowerSeries R) :
    thetaDeriv (f + g) = thetaDeriv f + thetaDeriv g := by
  ext n
  simp only [map_add, coeff_thetaDeriv]
  ring

theorem thetaDeriv_sub {R : Type*} [CommRing R] (f g : PowerSeries R) :
    thetaDeriv (f - g) = thetaDeriv f - thetaDeriv g := by
  ext n
  simp only [map_sub, coeff_thetaDeriv]
  ring

theorem thetaDeriv_neg {R : Type*} [CommRing R] (f : PowerSeries R) :
    thetaDeriv (-f) = -thetaDeriv f := by
  ext n
  simp only [map_neg, coeff_thetaDeriv]
  ring

theorem thetaDeriv_smul {R : Type*} [CommRing R] (c : R) (f : PowerSeries R) :
    thetaDeriv (c • f) = c • thetaDeriv f := by
  ext n
  simp only [map_smul, smul_eq_mul, coeff_thetaDeriv]
  ring

theorem thetaDeriv_C {R : Type*} [CommRing R] (c : R) :
    thetaDeriv (PowerSeries.C c) = 0 := by
  unfold thetaDeriv
  rw [PowerSeries.derivative_C, mul_zero]

@[simp]
theorem thetaDeriv_one {R : Type*} [CommRing R] :
    thetaDeriv (1 : PowerSeries R) = 0 := by
  unfold thetaDeriv
  rw [PowerSeries.derivative_one, mul_zero]

@[simp]
theorem thetaDeriv_X {R : Type*} [CommRing R] :
    thetaDeriv (PowerSeries.X : PowerSeries R) = PowerSeries.X := by
  unfold thetaDeriv
  rw [PowerSeries.derivative_X, mul_one]

/-- Leibniz product rule for `thetaDeriv`: `θ(f * g) = θ(f) * g + f * θ(g)`. -/
theorem thetaDeriv_mul {R : Type*} [CommRing R] (f g : PowerSeries R) :
    thetaDeriv (f * g) = thetaDeriv f * g + f * thetaDeriv g := by
  unfold thetaDeriv
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Power rule for `thetaDeriv`: `θ(f^n) = n * f^(n-1) * θ(f)`. -/
theorem thetaDeriv_pow {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    thetaDeriv (f ^ n) = (n : PowerSeries R) * f ^ (n - 1) * thetaDeriv f := by
  unfold thetaDeriv
  rw [PowerSeries.derivative_pow]
  ring

/-- `thetaDeriv` commutes with `PowerSeries.map` for every ring homomorphism `φ : R →+* S`. -/
theorem thetaDeriv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : PowerSeries R) :
    thetaDeriv (PowerSeries.map φ f) = PowerSeries.map φ (thetaDeriv f) := by
  ext n
  rw [coeff_thetaDeriv, PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_thetaDeriv,
    map_mul, map_natCast]

/-- **Uniqueness of Formal ODE Solutions to `θ(f) = E · f`**:
over any characteristic-zero integral domain `R`, if `coeff 0 E = 1` and
`f, g ∈ R⟦q⟧` both satisfy `thetaDeriv f = E * f` with `coeff 0 f = coeff 0 g = 0` and
`coeff 1 f = coeff 1 g`, then `f = g`. -/
theorem eq_of_thetaDeriv_eq_mul {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {E f g : PowerSeries R} (hE0 : PowerSeries.coeff 0 E = 1)
    (hf : thetaDeriv f = E * f) (hg : thetaDeriv g = E * g)
    (hf0 : PowerSeries.coeff 0 f = 0) (hg0 : PowerSeries.coeff 0 g = 0)
    (h1 : PowerSeries.coeff 1 f = PowerSeries.coeff 1 g) :
    f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | m
    · rw [hf0, hg0]
    · exact h1
    · set N : ℕ := m + 2
      have hrec : ∀ u : PowerSeries R, thetaDeriv u = E * u →
          ((m + 1 : ℕ) : R) * PowerSeries.coeff N u =
            ∑ k ∈ Finset.range N,
              PowerSeries.coeff (k + 1) E * PowerSeries.coeff (N - (k + 1)) u := by
        intro u hu
        have hcf := congrArg (PowerSeries.coeff N) hu
        rw [coeff_thetaDeriv, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a E * PowerSeries.coeff b u) N] at hcf
        have hsplit : (∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k E * PowerSeries.coeff (N - k) u) =
            PowerSeries.coeff 0 E * PowerSeries.coeff N u +
              ∑ k ∈ Finset.range N, PowerSeries.coeff (k + 1) E * PowerSeries.coeff (N - (k + 1)) u := by
          rw [Finset.sum_range_succ']
          simp [add_comm]
        rw [hsplit, hE0, one_mul] at hcf
        have hNcast : (N : R) = ((m + 1 : ℕ) : R) + 1 := by
          dsimp only [N]; push_cast; ring
        rw [hNcast] at hcf
        linear_combination hcf
      have hsum : (∑ k ∈ Finset.range N,
            PowerSeries.coeff (k + 1) E * PowerSeries.coeff (N - (k + 1)) f) =
          ∑ k ∈ Finset.range N,
            PowerSeries.coeff (k + 1) E * PowerSeries.coeff (N - (k + 1)) g := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hlt : N - (k + 1) < N := by
          have hk' := Finset.mem_range.mp hk
          omega
        rw [ih (N - (k + 1)) hlt]
      have hmul : ((m + 1 : ℕ) : R) * PowerSeries.coeff N f =
          ((m + 1 : ℕ) : R) * PowerSeries.coeff N g := by
        rw [hrec f hf, hrec g hg, hsum]
      have hne : ((m + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      exact mul_left_cancel₀ hne hmul

private lemma coeff_natCast_mul' {R : Type*} [CommRing R] (c : ℕ) (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((c : PowerSeries R) * φ) = (c : R) * PowerSeries.coeff n φ := by
  rw [← map_natCast (PowerSeries.C (R := R)) c, PowerSeries.coeff_C_mul]

private lemma coeff_ofNat_mul {R : Type*} [CommRing R] (c : ℕ) [c.AtLeastTwo]
    (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((OfNat.ofNat c : PowerSeries R) * φ) =
      (OfNat.ofNat c : R) * PowerSeries.coeff n φ := by
  rw [← map_ofNat (PowerSeries.C (R := R)) c, PowerSeries.coeff_C_mul]

/-- Formal integer power series `∑_{n ≥ 1} σ₁(n) q^n ∈ ℤ⟦q⟧`. -/
def sigma1SeriesZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (ArithmeticFunction.sigma 1 n : ℤ)

/-- Formal integer power series `E₂(q) = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n ∈ ℤ⟦q⟧`. -/
def E2SeriesZ : PowerSeries ℤ :=
  1 - 24 * sigma1SeriesZ

/-- Formal integer power series `E₄(q) = 1 + 240 ∑_{n ≥ 1} σ₃(n) q^n ∈ ℤ⟦q⟧`. -/
def E4SeriesZ : PowerSeries ℤ :=
  1 + 240 * sigma3SeriesZ

/-- Formal integer power series `E₆(q) = 1 - 504 ∑_{n ≥ 1} σ₅(n) q^n ∈ ℤ⟦q⟧`. -/
def E6SeriesZ : PowerSeries ℤ :=
  1 - 504 * sigma5SeriesZ

/-- Formal rational power series `E₂(q) = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n ∈ ℚ⟦q⟧`. -/
def E2Series : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) E2SeriesZ

/-- Formal rational power series `E₄(q) = 1 + 240 ∑_{n ≥ 1} σ₃(n) q^n ∈ ℚ⟦q⟧`. -/
def E4Series : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) E4SeriesZ

/-- Formal rational power series `E₆(q) = 1 - 504 ∑_{n ≥ 1} σ₅(n) q^n ∈ ℚ⟦q⟧`. -/
def E6Series : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) E6SeriesZ

/-- Formal rational power series `Δ(q) = ∑_{n ≥ 1} τ(n) q^n ∈ ℚ⟦q⟧`. -/
def ramanujanDeltaPowerSeriesQ : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) ramanujanDeltaPowerSeriesZ

theorem coeff_E2SeriesZ (n : ℕ) :
    PowerSeries.coeff n E2SeriesZ =
      if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℤ) := by
  unfold E2SeriesZ
  rw [map_sub, PowerSeries.coeff_one, coeff_ofNat_mul]
  simp only [sigma1SeriesZ, PowerSeries.coeff_mk]
  split_ifs with hn <;> ring

theorem coeff_E4SeriesZ (n : ℕ) :
    PowerSeries.coeff n E4SeriesZ =
      if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ) := by
  unfold E4SeriesZ
  rw [map_add, PowerSeries.coeff_one, coeff_ofNat_mul]
  simp only [sigma3SeriesZ, PowerSeries.coeff_mk]
  split_ifs with hn <;> ring

theorem coeff_E6SeriesZ (n : ℕ) :
    PowerSeries.coeff n E6SeriesZ =
      if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  unfold E6SeriesZ
  rw [map_sub, PowerSeries.coeff_one, coeff_ofNat_mul]
  simp only [sigma5SeriesZ, PowerSeries.coeff_mk]
  split_ifs with hn <;> ring

theorem coeff_E2Series (n : ℕ) :
    PowerSeries.coeff n E2Series =
      if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℚ) := by
  unfold E2Series
  rw [PowerSeries.coeff_map, coeff_E2SeriesZ]
  split_ifs <;> simp

theorem coeff_E4Series (n : ℕ) :
    PowerSeries.coeff n E4Series =
      if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℚ) := by
  unfold E4Series
  rw [PowerSeries.coeff_map, coeff_E4SeriesZ]
  split_ifs <;> simp

theorem coeff_E6Series (n : ℕ) :
    PowerSeries.coeff n E6Series =
      if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℚ) := by
  unfold E6Series
  rw [PowerSeries.coeff_map, coeff_E6SeriesZ]
  split_ifs <;> simp

theorem ramanujanDeltaPowerSeriesQ_eq :
    ramanujanDeltaPowerSeriesQ = (1 / 1728 : ℚ) • (E4Series ^ 3 - E6Series ^ 2) := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) mul_1728_ramanujanDeltaPowerSeriesZ
  rw [map_mul, map_ofNat, map_sub, map_pow, map_pow] at hmap
  change (1728 : PowerSeries ℚ) * ramanujanDeltaPowerSeriesQ = E4Series ^ 3 - E6Series ^ 2 at hmap
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hmap
  rw [coeff_ofNat_mul] at hcf
  rw [map_smul, smul_eq_mul, ← hcf]
  ring

end FormalPowerSeriesAndThetaDeriv

/-! ## Section 2: Analytic `E₂(τ)`, Quasi-Modular Transformation, & `q`-Expansion Action of `1/(2πi) d/dτ` -/

section AnalyticE2AndNormalizedDerivative

/-- **Analytic Quasi-Modular Eisenstein Series `E₂(τ) = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n`**
on the upper half-plane (directly from Mathlib's `EisensteinSeries.E2`). -/
abbrev E2 : UpperHalfPlane → ℂ := EisensteinSeries.E2

/-- Exact `q`-series expansion of analytic `E₂(τ)` on `UpperHalfPlane`. -/
theorem E2_eq_tsum (τ : UpperHalfPlane) :
    E2 τ = 1 - 24 * ∑' n : ℕ+,
      (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (n : ℕ) :=
  EisensteinSeries.E2_eq_tsum_cexp τ

/-- Holomorphicity (`MDiff`) of `E₂` on `UpperHalfPlane`. -/
theorem mdifferentiable_E2 : MDiff E2 := E2_mdifferentiable

/-- Boundedness of `E₂` at `i∞`. -/
theorem isBoundedAtImInfty_E2 : UpperHalfPlane.IsBoundedAtImInfty E2 :=
  EisensteinSeries.isBoundedAtImInfty_E2

/-- Exact `T`-periodicity of `E₂`: `E₂(T • τ) = E₂(τ)`. -/
theorem E2_T_smul (τ : UpperHalfPlane) : E2 (ModularGroup.T • τ) = E2 τ := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) τ
  rw [EisensteinSeries.D2_T, smul_zero, sub_zero] at h
  have hT : SlashAction.map (2 : ℤ) ModularGroup.T E2 τ = E2 (ModularGroup.T • τ) := by
    rw [ModularForm.SL_slash]
    exact slash_T_apply 2 E2 τ
  rwa [hT] at h

/-- `E₂ ∘ ofComplex` is `1`-periodic on `ℂ`. -/
theorem E2_periodic :
    Function.Periodic (E2 ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    have hof1 : UpperHalfPlane.ofComplex (z + 1) = ModularGroup.T • UpperHalfPlane.ofComplex z := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
        show ((ModularGroup.T • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) =
          (UpperHalfPlane.ofComplex z : ℂ) + 1 by
          simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq (UpperHalfPlane.ofComplex z) (n := 1),
        UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    simp only [Function.comp_apply, Complex.ofReal_one, hof1]
    exact E2_T_smul (UpperHalfPlane.ofComplex z)
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, Complex.ofReal_one,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz1),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz)]

/-- **Quasi-Modular `S`-Transformation of `E₂`**:
for every `τ : UpperHalfPlane`,
$$E_2(-1/\tau) = \tau^2 E_2(\tau) + \frac{6\tau}{\pi i}.$$ -/
theorem E2_S_smul (τ : UpperHalfPlane) :
    E2 (ModularGroup.S • τ) =
      (τ : ℂ) ^ 2 * E2 τ + 6 * (τ : ℂ) / ((Real.pi : ℂ) * Complex.I) := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) τ
  have hS : SlashAction.map (2 : ℤ) ModularGroup.S E2 τ =
      E2 (ModularGroup.S • τ) * (τ : ℂ) ^ (-(2 : ℤ)) := by
    rw [ModularForm.SL_slash]
    exact slash_S_apply 2 E2 τ
  rw [hS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, EisensteinSeries.D2_S, riemannZeta_two] at h
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hmul : E2 (ModularGroup.S • τ) =
      (E2 (ModularGroup.S • τ) * (τ : ℂ) ^ (-(2 : ℤ))) * (τ : ℂ) ^ 2 := by
    have hz2 : (τ : ℂ) ^ 2 = (τ : ℂ) ^ (2 : ℤ) := (zpow_natCast (τ : ℂ) 2).symm
    rw [hz2, mul_assoc, ← zpow_add₀ hτ, neg_add_cancel, zpow_zero, mul_one]
  rw [hmul, h]
  field_simp [hτ, hpi, hI]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Exact Elliptic Special Value `E₂(i) = 3 / π`** (direct corollary of `E2_S_smul` at `τ = i`). -/
theorem E2_at_I : E2 UpperHalfPlane.I = 3 / (Real.pi : ℂ) := by
  have h := E2_S_smul UpperHalfPlane.I
  have hSI : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    simp
  rw [hSI] at h
  change E2 UpperHalfPlane.I = Complex.I ^ 2 * E2 UpperHalfPlane.I +
    6 * Complex.I / ((Real.pi : ℂ) * Complex.I) at h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [Complex.I_sq] at h
  have h6 : 6 * Complex.I / ((Real.pi : ℂ) * Complex.I) = 6 / (Real.pi : ℂ) := by
    field_simp [hpi, hI]
  rw [h6] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Exact `q`-expansion coefficients of analytic `E₂`:
`coeff 0 = 1`, and `coeff m = -24 * σ₁(m)` for `m ≥ 1`. -/
theorem E2_qExpansion_coeff (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 E2) =
      if m = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 m : ℂ) := by
  let c : ℕ → ℂ := fun n => if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℂ)
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one E2_periodic
      mdifferentiable_E2 isBoundedAtImInfty_E2
  have hsum1 : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => c n • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) (E2 τ) := by
    intro τ
    have hq : Function.Periodic.qParam (1 : ℝ) (τ : ℂ) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) := by
      unfold Function.Periodic.qParam
      rw [Complex.ofReal_one, div_one]
    simp_rw [hq]
    exact EisensteinSeries.hasSum_qExpansion_E2 τ
  have hsum2 : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 E2) •
        Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) (E2 τ) :=
    UpperHalfPlane.hasSum_qExpansion zero_lt_one E2_periodic mdifferentiable_E2 isBoundedAtImInfty_E2
  have hball1 := UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction zero_lt_one hana hsum1
  have hball2 := UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction zero_lt_one hana hsum2
  have heq := hball2.hasFPowerSeriesAt.eq_formalMultilinearSeries hball1.hasFPowerSeriesAt
  have hval := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p m (fun _ => (1 : ℂ))) heq
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, c] using hval

/-- Identification of `E2SeriesZ`, `E4SeriesZ`, `E6SeriesZ` with `qExpansion 1` in `ℂ⟦q⟧`. -/
theorem E2SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) E2SeriesZ = UpperHalfPlane.qExpansion 1 E2 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E2SeriesZ, E2_qExpansion_coeff]
  split_ifs <;> simp

theorem E4SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) E4SeriesZ = UpperHalfPlane.qExpansion 1 E4 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E4SeriesZ, E4_qExpansion_coeff]
  split_ifs <;> simp

theorem E6SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) E6SeriesZ = UpperHalfPlane.qExpansion 1 E6 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E6SeriesZ, E6_qExpansion_coeff]
  split_ifs <;> simp

theorem E2Series_map_eq :
    PowerSeries.map (Rat.castHom ℂ) E2Series = UpperHalfPlane.qExpansion 1 E2 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E2Series, E2_qExpansion_coeff]
  split_ifs <;> simp

theorem E4Series_map_eq :
    PowerSeries.map (Rat.castHom ℂ) E4Series = UpperHalfPlane.qExpansion 1 E4 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E4Series, E4_qExpansion_coeff]
  split_ifs <;> simp

theorem E6Series_map_eq :
    PowerSeries.map (Rat.castHom ℂ) E6Series = UpperHalfPlane.qExpansion 1 E6 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E6Series, E6_qExpansion_coeff]
  split_ifs <;> simp

theorem ramanujanDeltaPowerSeriesQ_map_eq :
    PowerSeries.map (Rat.castHom ℂ) ramanujanDeltaPowerSeriesQ =
      UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ) := by
  rw [← ramanujanDeltaPowerSeriesZ_map_eq]
  ext n
  unfold ramanujanDeltaPowerSeriesQ
  simp

/-! ### Boundedness-at-`i∞` closure lemmas & exact `q`-expansion of `normalizedDerivOfComplex` -/

private lemma isBoundedAtImInfty_add' {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (hg : UpperHalfPlane.IsBoundedAtImInfty g) :
    UpperHalfPlane.IsBoundedAtImInfty (f + g) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf hg ⊢
  rcases hf with ⟨M₁, A₁, h₁⟩
  rcases hg with ⟨M₂, A₂, h₂⟩
  refine ⟨M₁ + M₂, max A₁ A₂, fun τ hτ => ?_⟩
  calc ‖(f + g) τ‖ = ‖f τ + g τ‖ := rfl
    _ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ M₁ + M₂ := add_le_add (h₁ τ (le_of_max_le_left hτ)) (h₂ τ (le_of_max_le_right hτ))

private lemma isBoundedAtImInfty_sub' {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (hg : UpperHalfPlane.IsBoundedAtImInfty g) :
    UpperHalfPlane.IsBoundedAtImInfty (f - g) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf hg ⊢
  rcases hf with ⟨M₁, A₁, h₁⟩
  rcases hg with ⟨M₂, A₂, h₂⟩
  refine ⟨M₁ + M₂, max A₁ A₂, fun τ hτ => ?_⟩
  calc ‖(f - g) τ‖ = ‖f τ - g τ‖ := rfl
    _ ≤ ‖f τ‖ + ‖g τ‖ := norm_sub_le _ _
    _ ≤ M₁ + M₂ := add_le_add (h₁ τ (le_of_max_le_left hτ)) (h₂ τ (le_of_max_le_right hτ))

private lemma isBoundedAtImInfty_mul' {f g : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (hg : UpperHalfPlane.IsBoundedAtImInfty g) :
    UpperHalfPlane.IsBoundedAtImInfty (f * g) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf hg ⊢
  rcases hf with ⟨M₁, A₁, h₁⟩
  rcases hg with ⟨M₂, A₂, h₂⟩
  refine ⟨max M₁ 0 * max M₂ 0, max A₁ A₂, fun τ hτ => ?_⟩
  calc ‖(f * g) τ‖ = ‖f τ‖ * ‖g τ‖ := norm_mul _ _
    _ ≤ max M₁ 0 * max M₂ 0 :=
      mul_le_mul ((h₁ τ (le_of_max_le_left hτ)).trans (le_max_left _ _))
        ((h₂ τ (le_of_max_le_right hτ)).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

private lemma isBoundedAtImInfty_smul' (c : ℂ) {f : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.IsBoundedAtImInfty (c • f) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hf ⊢
  rcases hf with ⟨M, A, h⟩
  refine ⟨‖c‖ * max M 0, A, fun τ hτ => ?_⟩
  calc ‖(c • f) τ‖ = ‖c‖ * ‖f τ‖ := norm_mul _ _
    _ ≤ ‖c‖ * max M 0 := mul_le_mul_of_nonneg_left ((h τ hτ).trans (le_max_left _ _)) (norm_nonneg _)

private lemma isBoundedAtImInfty_of_tendsto_zero {f : UpperHalfPlane → ℂ}
    (hf : Filter.Tendsto f UpperHalfPlane.atImInfty (nhds 0)) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hev : ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty, ‖f τ‖ ≤ 1 := by
    filter_upwards [hf.eventually (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with τ hτ
    rw [dist_zero_right] at hτ
    exact hτ.le
  rw [UpperHalfPlane.atImInfty, Filter.eventually_comap] at hev
  rcases Filter.eventually_atTop.mp hev with ⟨A, hA⟩
  exact ⟨1, A, fun τ hτ => hA τ.im hτ τ rfl⟩

private lemma norm_qParam_one_lt_one (τ : UpperHalfPlane) :
    ‖Function.Periodic.qParam (1 : ℝ) (τ : ℂ)‖ < 1 := by
  unfold Function.Periodic.qParam
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / ((1 : ℝ) : ℂ)).re =
      -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_lt_one_iff]
  have hpi : 0 < Real.pi := Real.pi_pos
  have him : 0 < τ.im := τ.im_pos
  nlinarith

private lemma hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam (1 : ℝ))
      (2 * (Real.pi : ℂ) * Complex.I * Function.Periodic.qParam (1 : ℝ) z) z := by
  have hfun : Function.Periodic.qParam (1 : ℝ) =
      fun w : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
    funext w
    unfold Function.Periodic.qParam
    simp
  rw [hfun]
  have hlin : HasDerivAt (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * w)
      (2 * (Real.pi : ℂ) * Complex.I) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)
  simpa [mul_comm] using hlin.cexp

/-- **Exact Chain-Rule Formula for `Derivative.normalizedDerivOfComplex` in Terms of `cuspFunction`**:
for every `1`-periodic holomorphic function `f` bounded at `i∞`,
$$\frac{1}{2\pi i} f'(\tau) = q \cdot (\mathrm{cuspFunction}\ 1\ f)'(q), \quad q = e^{2\pi i \tau}.$$ -/
theorem normalizedDerivOfComplex_eq_qParam_mul_deriv_cuspFunction
    {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ))
    (hmdiff : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex f τ =
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) *
        deriv (UpperHalfPlane.cuspFunction 1 f) (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) := by
  set g : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 f
  have hg_diff : DifferentiableAt ℂ g (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) :=
    UpperHalfPlane.differentiableAt_cuspFunction zero_lt_one hper hmdiff hbdd
      (norm_qParam_one_lt_one τ)
  have hcomp : HasDerivAt (g ∘ Function.Periodic.qParam (1 : ℝ))
      (deriv g (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * Function.Periodic.qParam (1 : ℝ) (τ : ℂ))) (τ : ℂ) :=
    hg_diff.hasDerivAt.comp (τ : ℂ) (hasDerivAt_qParam_one (τ : ℂ))
  have hev : (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) =ᶠ[nhds (τ : ℂ)]
      (g ∘ Function.Periodic.qParam (1 : ℝ)) := by
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply]
    have hof : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have heq := UpperHalfPlane.eq_cuspFunction (h := 1) (f := f) (UpperHalfPlane.ofComplex z)
      one_ne_zero hper
    rw [hof] at heq
    exact heq.symm
  have hderiv : deriv (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (τ : ℂ) =
      deriv g (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) :=
    (hev.deriv_eq).trans hcomp.deriv
  unfold Derivative.normalizedDerivOfComplex
  rw [hderiv]
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp [h2piI]

/-- `normalizedDerivOfComplex f` is `1`-periodic whenever `f` is `1`-periodic, holomorphic, and bounded at `i∞`. -/
theorem periodic_normalizedDerivOfComplex
    {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ))
    (hmdiff : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    Function.Periodic
      (Derivative.normalizedDerivOfComplex f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane))
      (1 : ℝ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, Complex.ofReal_one]
    rw [normalizedDerivOfComplex_eq_qParam_mul_deriv_cuspFunction hper hmdiff hbdd,
      normalizedDerivOfComplex_eq_qParam_mul_deriv_cuspFunction hper hmdiff hbdd]
    have hof1 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ) = z + 1 := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
    have hof0 : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hq : Function.Periodic.qParam (1 : ℝ) (z + 1) = Function.Periodic.qParam (1 : ℝ) z := by
      unfold Function.Periodic.qParam
      simp only [Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add,
        Complex.exp_two_pi_mul_I, mul_one]
    rw [hof1, hof0, hq]
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, Complex.ofReal_one,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz1),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz)]

/-- `normalizedDerivOfComplex f` vanishes at `i∞` (`IsZeroAtImInfty`). -/
theorem tendsto_normalizedDerivOfComplex_atImInfty
    {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ))
    (hmdiff : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    Filter.Tendsto (Derivative.normalizedDerivOfComplex f) UpperHalfPlane.atImInfty (nhds 0) := by
  set g : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 f
  have hana : AnalyticAt ℂ g 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one hper hmdiff hbdd
  have hcont_deriv : ContinuousAt (deriv g) 0 := hana.deriv.continuousAt
  have hcont_mul : ContinuousAt (fun q : ℂ => q * deriv g q) 0 :=
    continuousAt_id.mul hcont_deriv
  have hzero : (fun q : ℂ => q * deriv g q) 0 = 0 := by simp
  have hcomp : Filter.Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) *
        deriv g (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds 0) := by
    rw [← hzero]
    exact hcont_mul.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)
  refine hcomp.congr fun τ => ?_
  exact (normalizedDerivOfComplex_eq_qParam_mul_deriv_cuspFunction hper hmdiff hbdd τ).symm

/-- `normalizedDerivOfComplex f` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_normalizedDerivOfComplex
    {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ))
    (hmdiff : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex f) :=
  isBoundedAtImInfty_of_tendsto_zero (tendsto_normalizedDerivOfComplex_atImInfty hper hmdiff hbdd)

/-- On the open unit disk `Metric.ball 0 1`, `cuspFunction 1 (normalizedDerivOfComplex f)` agrees
identically with `q ↦ q * deriv (cuspFunction 1 f) q`. -/
theorem cuspFunction_normalizedDerivOfComplex_eqOn
    {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ))
    (hmdiff : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    Set.EqOn (UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f))
      (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction 1 f) q) (Metric.ball 0 1) := by
  intro q hq
  rw [Metric.mem_ball, dist_zero_right] at hq
  by_cases hq0 : q = 0
  · subst hq0
    have hzero : UpperHalfPlane.IsZeroAtImInfty (Derivative.normalizedDerivOfComplex f) :=
      tendsto_normalizedDerivOfComplex_atImInfty hper hmdiff hbdd
    rw [hzero.cuspFunction_apply_zero zero_lt_one]
    simp
  · have hnorm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hlog_neg : Real.log ‖q‖ < 0 := Real.log_neg hnorm_pos hq
    set z : ℂ := Complex.log q / (2 * (Real.pi : ℂ) * Complex.I)
    have hz_im : 0 < z.im := by
      have hz_eq : z = -(Complex.I * Complex.log q) / (2 * (Real.pi : ℂ)) := by
        dsimp only [z]
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hI : Complex.I ≠ 0 := Complex.I_ne_zero
        field_simp [hpi, hI]
        rw [Complex.I_sq]
        ring
      have hre_log : (Complex.log q).re = Real.log ‖q‖ := Complex.log_re q
      have him_calc : z.im = -Real.log ‖q‖ / (2 * Real.pi) := by
        rw [hz_eq]
        have h2pi : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; rfl
        rw [← h2pi, Complex.div_ofReal_im]
        simp [Complex.mul_im, hre_log]
      rw [him_calc]
      exact div_pos (neg_pos.mpr hlog_neg) (by positivity)
    let τ : UpperHalfPlane := ⟨z, hz_im⟩
    have hqparam : Function.Periodic.qParam (1 : ℝ) (τ : ℂ) = q := by
      change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / ((1 : ℝ) : ℂ)) = q
      dsimp only [z]
      have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      rw [Complex.ofReal_one, div_one, mul_div_cancel₀ _ h2piI, Complex.exp_log hq0]
    have hper' := periodic_normalizedDerivOfComplex hper hmdiff hbdd
    rw [← hqparam, UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper']
    exact normalizedDerivOfComplex_eq_qParam_mul_deriv_cuspFunction hper hmdiff hbdd τ

/-- **Exact `q`-Expansion Theorem for `1/(2πi) d/dτ`**:
for EVERY `1`-periodic holomorphic function `f` bounded at `i∞` (including both modular forms and
quasi-modular `E₂`),
$$\mathrm{qExpansion}\ 1\ \Bigl(\frac{1}{2\pi i} f'\Bigr) = \theta\bigl(\mathrm{qExpansion}\ 1\ f\bigr).$$ -/
theorem qExpansion_normalizedDerivOfComplex
    {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ))
    (hmdiff : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex f) =
      thetaDeriv (UpperHalfPlane.qExpansion 1 f) := by
  set g : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 f
  have hana : AnalyticAt ℂ g 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one hper hmdiff hbdd
  have hana_deriv : AnalyticAt ℂ (deriv g) 0 := hana.deriv
  have hev : UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) =ᶠ[nhds 0]
      (fun q : ℂ => q * deriv g q) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
      (cuspFunction_normalizedDerivOfComplex_eqOn hper hmdiff hbdd)
  ext m
  rw [UpperHalfPlane.qExpansion_coeff, coeff_thetaDeriv, UpperHalfPlane.qExpansion_coeff]
  have hiter_eq : iteratedDeriv m
      (UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f)) 0 =
      iteratedDeriv m (fun q : ℂ => q * deriv g q) 0 :=
    hev.iteratedDeriv_eq m
  rw [hiter_eq]
  have hcd_id : ContDiffAt ℂ (m : WithTop ℕ∞) (id : ℂ → ℂ) 0 := contDiffAt_id
  have hcd_dg : ContDiffAt ℂ (m : WithTop ℕ∞) (deriv g) 0 :=
    hana_deriv.contDiffAt.of_le le_top
  have hmul_iter : iteratedDeriv m (fun q : ℂ => q * deriv g q) 0 =
      (m : ℂ) * iteratedDeriv m g 0 := by
    have hfun : (fun q : ℂ => q * deriv g q) = (id : ℂ → ℂ) * deriv g := rfl
    rw [hfun, iteratedDeriv_mul hcd_id hcd_dg]
    cases m with
    | zero =>
      simp
    | succ n =>
      rw [Finset.sum_eq_single 1]
      · simp only [iteratedDeriv_id, one_ne_zero, ↓reduceIte,
          Nat.choose_one_right, Nat.add_sub_cancel]
        rw [← iteratedDeriv_succ' (n := n) (f := g)]
        push_cast
        ring
      · intro i hi hi1
        rw [iteratedDeriv_id]
        by_cases hi0 : i = 0
        · simp [hi0]
        · simp [hi0, hi1]
      · intro h1
        exfalso
        exact h1 (Finset.mem_range.mpr (by omega))
  rw [hmul_iter]
  ring

end AnalyticE2AndNormalizedDerivative

/-! ## Section 3: Serre Derivative `serreDeriv`, Ramanujan's Three Differential Equations, & Convolutions -/

section SerreDerivativeAndRamanujanEquations

/-- Helper: every level-1 modular form `f` is `1`-periodic on `ℂ` via `ofComplex`. -/
private lemma modularForm_SL2Z_periodic {k : ℤ} (f : ModularForm SL2ZRange k) :
    Function.Periodic ((f : UpperHalfPlane → ℂ) ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane))
      (1 : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL

/-- Helper: every level-1 modular form `f` is bounded at `i∞`. -/
private lemma modularForm_SL2Z_isBoundedAtImInfty {k : ℤ} (f : ModularForm SL2ZRange k) :
    UpperHalfPlane.IsBoundedAtImInfty (f : UpperHalfPlane → ℂ) := by
  have hcusp : IsCusp OnePoint.infty SL2ZRange :=
    (inferInstance : Fact (IsCusp OnePoint.infty SL2ZRange)).out
  exact OnePoint.isBoundedAt_infty_iff.mp (f.bdd_at_cusps' hcusp)

/-- **The Serre Derivative `∂_k : M_k(SL₂(ℤ)) → M_{k+2}(SL₂(ℤ))`**:
$$\partial_k f(\tau) = \frac{1}{2\pi i} f'(\tau) - \frac{k}{12} E_2(\tau)\, f(\tau).$$ -/
def serreDeriv (k : ℤ) (f : ModularForm SL2ZRange k) : ModularForm SL2ZRange (k + 2) where
  toFun := Derivative.serreDerivative (k : ℂ) (f : UpperHalfPlane → ℂ)
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    have hinv : SlashAction.map k γ (f : UpperHalfPlane → ℂ) = (f : UpperHalfPlane → ℂ) := by
      rw [ModularForm.SL_slash]
      exact f.slash_action_eq' _ ⟨γ, rfl⟩
    have hserre := Derivative.serreDerivative_slash_invariant f.holo' hinv
    rwa [ModularForm.SL_slash] at hserre
  holo' := Derivative.serreDerivative_mdifferentiable (k : ℂ) f.holo'
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map k γ (f : UpperHalfPlane → ℂ) = (f : UpperHalfPlane → ℂ) := by
      rw [ModularForm.SL_slash]
      exact f.slash_action_eq' _ ⟨γ, rfl⟩
    have hserre : SlashAction.map (k + 2) γ (Derivative.serreDerivative (k : ℂ) (f : UpperHalfPlane → ℂ)) =
        Derivative.serreDerivative (k : ℂ) (f : UpperHalfPlane → ℂ) :=
      Derivative.serreDerivative_slash_invariant f.holo' hinv
    rw [hserre]
    have hfun : Derivative.serreDerivative (k : ℂ) (f : UpperHalfPlane → ℂ) =
        Derivative.normalizedDerivOfComplex (f : UpperHalfPlane → ℂ) -
          ((k : ℂ) * (12 : ℂ)⁻¹) • (E2 * (f : UpperHalfPlane → ℂ)) := by
      funext τ
      rw [Derivative.serreDerivative_apply]
      simp [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc]
    rw [hfun]
    exact isBoundedAtImInfty_sub'
      (isBoundedAtImInfty_normalizedDerivOfComplex (modularForm_SL2Z_periodic f) f.holo'
        (modularForm_SL2Z_isBoundedAtImInfty f))
      (isBoundedAtImInfty_smul' _ (isBoundedAtImInfty_mul' isBoundedAtImInfty_E2
        (modularForm_SL2Z_isBoundedAtImInfty f)))

@[simp]
theorem serreDeriv_apply (k : ℤ) (f : ModularForm SL2ZRange k) (τ : UpperHalfPlane) :
    serreDeriv k f τ =
      Derivative.normalizedDerivOfComplex (f : UpperHalfPlane → ℂ) τ -
        (k : ℂ) / 12 * E2 τ * f τ := by
  change Derivative.serreDerivative (k : ℂ) (f : UpperHalfPlane → ℂ) τ = _
  rw [Derivative.serreDerivative_apply]
  ring

/-- Exact `q`-expansion of `serreDeriv k f`:
$$\mathrm{qExpansion}\ 1\ (\partial_k f) = \theta(\mathrm{qExpansion}\ 1\ f) - \frac{k}{12} \cdot \mathrm{qExpansion}\ 1\ E_2 \cdot \mathrm{qExpansion}\ 1\ f.$$ -/
theorem serreDeriv_qExpansion (k : ℤ) (f : ModularForm SL2ZRange k) :
    UpperHalfPlane.qExpansion 1 (serreDeriv k f : UpperHalfPlane → ℂ) =
      thetaDeriv (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) -
        ((k : ℂ) / 12) •
          (UpperHalfPlane.qExpansion 1 E2 *
            UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) := by
  have hper_f := modularForm_SL2Z_periodic f
  have hbdd_f := modularForm_SL2Z_isBoundedAtImInfty f
  have hana_df : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex (f : UpperHalfPlane → ℂ))) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one
      (periodic_normalizedDerivOfComplex hper_f f.holo' hbdd_f)
      (Derivative.normalizedDerivOfComplex_mdifferentiable f.holo')
      (isBoundedAtImInfty_normalizedDerivOfComplex hper_f f.holo' hbdd_f)
  have hana_E2 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one E2_periodic
      mdifferentiable_E2 isBoundedAtImInfty_E2
  have hana_f : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (f : UpperHalfPlane → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one one_mem_strictPeriods_SL
  have hana_prod : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (E2 * (f : UpperHalfPlane → ℂ))) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hana_E2.continuousAt hana_f.continuousAt]
    exact hana_E2.mul hana_f
  have hana_smul : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (((k : ℂ) / 12) • (E2 * (f : UpperHalfPlane → ℂ)))) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hana_prod.continuousAt]
    exact hana_prod.const_smul
  have hcoe : (serreDeriv k f : UpperHalfPlane → ℂ) =
      Derivative.normalizedDerivOfComplex (f : UpperHalfPlane → ℂ) -
        ((k : ℂ) / 12) • (E2 * (f : UpperHalfPlane → ℂ)) := by
    funext τ
    rw [serreDeriv_apply]
    simp [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc]
  rw [hcoe, UpperHalfPlane.qExpansion_sub hana_df hana_smul,
    UpperHalfPlane.qExpansion_smul hana_prod,
    UpperHalfPlane.qExpansion_mul hana_E2 hana_f,
    qExpansion_normalizedDerivOfComplex hper_f f.holo' hbdd_f]

/-- Constant term of `serreDeriv k f` at `i∞`: `a₀(∂_k f) = -(k / 12) * a₀(f)`. -/
theorem serreDeriv_qExpansion_coeff_zero (k : ℤ) (f : ModularForm SL2ZRange k) :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (serreDeriv k f : UpperHalfPlane → ℂ)) =
      -((k : ℂ) / 12) * PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) := by
  rw [serreDeriv_qExpansion, map_sub, coeff_zero_thetaDeriv, zero_sub, map_smul, smul_eq_mul,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
    E2_qExpansion_coeff 0, if_pos rfl, one_mul]
  ring

/-! ### Ramanujan's Differential Equation for `E₄` (`∂_4 E₄ = -(1/3) E₆`) -/

/-- **Serre Derivative of `E₄`**: `∂₄(E₄) = -(1 / 3) • E₆` in `M₆(SL₂(ℤ))`. -/
theorem serreDeriv_E4_eq :
    serreDeriv 4 ModularForm.E₄ = (-(1 / 3 : ℂ)) • ModularForm.E₆ := by
  have h := modularForm_SL2Z_weight_six_eq_smul_E6 (serreDeriv 4 ModularForm.E₄)
  rw [serreDeriv_qExpansion_coeff_zero,
    EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide)] at h
  rw [h]
  congr 1
  push_cast
  norm_num

/-- **Analytic Ramanujan Differential Equation for `E₄`**:
$$\frac{1}{2\pi i} E_4'(\tau) = \frac{E_2(\tau) E_4(\tau) - E_6(\tau)}{3}.$$ -/
theorem normalizedDerivOfComplex_E4 (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex E4 τ = (E2 τ * E4 τ - E6 τ) / 3 := by
  have h := congrArg (fun u : ModularForm SL2ZRange 6 => u τ) serreDeriv_E4_eq
  rw [serreDeriv_apply, smul_apply, smul_eq_mul, ← E4_eq_coe,
    ← E6_eq_modularForm_E6 τ] at h
  linear_combination h

/-- **Formal Integer Ramanujan Differential Equation for `E₄`** in `ℤ⟦q⟧`:
`3 * θ(E₄) = E₂ * E₄ - E₆`. -/
theorem ramanujan_diff_E4_Z :
    (3 : PowerSeries ℤ) * thetaDeriv E4SeriesZ = E2SeriesZ * E4SeriesZ - E6SeriesZ := by
  have hq := congrArg (fun u : ModularForm SL2ZRange 6 =>
      UpperHalfPlane.qExpansion 1 (u : UpperHalfPlane → ℂ)) serreDeriv_E4_eq
  rw [serreDeriv_qExpansion, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL,
    ← E4_eq_coe, ← E6_eq_coe, ← E2SeriesZ_map_eq, ← E4SeriesZ_map_eq, ← E6SeriesZ_map_eq,
    thetaDeriv_map] at hq
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hq
  simp only [map_sub, map_smul, smul_eq_mul, PowerSeries.coeff_map, PowerSeries.coeff_mul] at hcf
  have hC : ((PowerSeries.coeff n ((3 : PowerSeries ℤ) * thetaDeriv E4SeriesZ) : ℤ) : ℂ) =
      ((PowerSeries.coeff n (E2SeriesZ * E4SeriesZ - E6SeriesZ) : ℤ) : ℂ) := by
    rw [coeff_ofNat_mul, map_sub, PowerSeries.coeff_mul]
    push_cast
    have hcast : ∀ z : ℤ, Int.castRingHom ℂ z = (z : ℂ) := fun _ => rfl
    simp only [hcast] at hcf
    linear_combination 3 * hcf
  exact Int.cast_injective hC

/-- **Formal Rational Ramanujan Differential Equation for `E₄`** in `ℚ⟦q⟧`:
`θ(E₄) = (1 / 3) • (E₂ * E₄ - E₆)`. -/
theorem ramanujan_diff_E4 :
    thetaDeriv E4Series = (1 / 3 : ℚ) • (E2Series * E4Series - E6Series) := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) ramanujan_diff_E4_Z
  rw [map_mul, map_ofNat, ← thetaDeriv_map, map_sub, map_mul] at hmap
  change (3 : PowerSeries ℚ) * thetaDeriv E4Series = E2Series * E4Series - E6Series at hmap
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hmap
  rw [coeff_ofNat_mul] at hcf
  rw [map_smul, smul_eq_mul, ← hcf]
  ring

/-! ### Ramanujan's Differential Equation for `E₆` (`∂_6 E₆ = -(1/2) E₄²`) -/

/-- **Serre Derivative of `E₆`**: `∂₆(E₆) = -(1 / 2) • E₈` in `M₈(SL₂(ℤ))`. -/
theorem serreDeriv_E6_eq :
    serreDeriv 6 ModularForm.E₆ = (-(1 / 2 : ℂ)) • ModularForm.E (k := 8) (by norm_num) := by
  have h := modularForm_SL2Z_weight_eight_eq_smul_E8 (serreDeriv 6 ModularForm.E₆)
  rw [serreDeriv_qExpansion_coeff_zero,
    EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) (by decide)] at h
  rw [h]
  congr 1
  push_cast
  norm_num

/-- **Analytic Ramanujan Differential Equation for `E₆`**:
$$\frac{1}{2\pi i} E_6'(\tau) = \frac{E_2(\tau) E_6(\tau) - E_4(\tau)^2}{2}.$$ -/
theorem normalizedDerivOfComplex_E6 (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex E6 τ = (E2 τ * E6 τ - E4 τ ^ 2) / 2 := by
  have h := congrArg (fun u : ModularForm SL2ZRange 8 => u τ) serreDeriv_E6_eq
  rw [serreDeriv_apply, smul_apply, smul_eq_mul, ← E6_eq_coe,
    ← E8Eisenstein_eq_modularForm_E8 τ, ← E4_sq_eq_E8Eisenstein τ] at h
  linear_combination h

/-- **Formal Integer Ramanujan Differential Equation for `E₆`** in `ℤ⟦q⟧`:
`2 * θ(E₆) = E₂ * E₆ - E₄²`. -/
theorem ramanujan_diff_E6_Z :
    (2 : PowerSeries ℤ) * thetaDeriv E6SeriesZ = E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2 := by
  have hE8_eq : UpperHalfPlane.qExpansion 1 (ModularForm.E (k := 8) (by norm_num) : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 E4 ^ 2 := by
    have hfun : (ModularForm.E (k := 8) (by norm_num) : UpperHalfPlane → ℂ) =
        (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
      funext τ
      rw [← E8Eisenstein_eq_modularForm_E8 τ, ← E4_sq_eq_E8Eisenstein τ, sq,
        E4_eq_modularForm_E4 τ]
      rfl
    rw [hfun, ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL
      ModularForm.E₄ ModularForm.E₄, ← E4_eq_coe, sq]
  have hq := congrArg (fun u : ModularForm SL2ZRange 8 =>
      UpperHalfPlane.qExpansion 1 (u : UpperHalfPlane → ℂ)) serreDeriv_E6_eq
  rw [serreDeriv_qExpansion, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL, hE8_eq,
    ← E6_eq_coe, ← E2SeriesZ_map_eq, ← E4SeriesZ_map_eq, ← E6SeriesZ_map_eq,
    thetaDeriv_map, ← map_mul, ← map_pow] at hq
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hq
  simp only [map_sub, map_smul, smul_eq_mul, PowerSeries.coeff_map] at hcf
  have hC : ((PowerSeries.coeff n ((2 : PowerSeries ℤ) * thetaDeriv E6SeriesZ) : ℤ) : ℂ) =
      ((PowerSeries.coeff n (E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2) : ℤ) : ℂ) := by
    rw [coeff_ofNat_mul, map_sub]
    push_cast
    have hcast : ∀ z : ℤ, Int.castRingHom ℂ z = (z : ℂ) := fun _ => rfl
    simp only [hcast] at hcf
    linear_combination 2 * hcf
  exact Int.cast_injective hC

/-- **Formal Rational Ramanujan Differential Equation for `E₆`** in `ℚ⟦q⟧`:
`θ(E₆) = (1 / 2) • (E₂ * E₆ - E₄²)`. -/
theorem ramanujan_diff_E6 :
    thetaDeriv E6Series = (1 / 2 : ℚ) • (E2Series * E6Series - E4Series ^ 2) := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) ramanujan_diff_E6_Z
  rw [map_mul, map_ofNat, ← thetaDeriv_map, map_sub, map_mul, map_pow] at hmap
  change (2 : PowerSeries ℚ) * thetaDeriv E6Series = E2Series * E6Series - E4Series ^ 2 at hmap
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hmap
  rw [coeff_ofNat_mul] at hcf
  rw [map_smul, smul_eq_mul, ← hcf]
  ring

/-! ### Ramanujan's Differential Equation for `E₂` (`(1/(2πi)) E₂' - (1/12) E₂² = -(1/12) E₄`) -/

/-- The weight-4 combination `F₂(τ) = (1/(2πi)) E₂'(τ) - (1/12) E₂(τ)²`. -/
def ramanujanE2Fun (τ : UpperHalfPlane) : ℂ :=
  Derivative.normalizedDerivOfComplex E2 τ - (1 / 12 : ℂ) * E2 τ ^ 2

private lemma normalizedDerivOfComplex_inv_coe (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex (fun w : UpperHalfPlane => ((w : ℂ))⁻¹) τ =
      -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (τ : ℂ) ^ (-(2 : ℤ)) := by
  have hev : ((fun w : UpperHalfPlane => ((w : ℂ))⁻¹) ∘
      (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) =ᶠ[nhds (τ : ℂ)] (fun z : ℂ => z⁻¹) := by
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hderiv : deriv ((fun w : UpperHalfPlane => ((w : ℂ))⁻¹) ∘
      (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (τ : ℂ) = -((τ : ℂ) ^ 2)⁻¹ := by
    rw [hev.deriv_eq]
    exact (hasDerivAt_inv τ.ne_zero).deriv
  unfold Derivative.normalizedDerivOfComplex
  rw [hderiv, zpow_neg]
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * -((τ : ℂ) ^ 2)⁻¹ =
      -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ((τ : ℂ) ^ 2)⁻¹
  rw [mul_neg, neg_mul]
  rfl

/-- `F₂(τ) = (1/(2πi)) E₂'(τ) - (1/12) E₂(τ)²` is invariant under `T`: `F₂(T • τ) = F₂(τ)`. -/
theorem ramanujanE2Fun_T_smul (τ : UpperHalfPlane) :
    ramanujanE2Fun (ModularGroup.T • τ) = ramanujanE2Fun τ := by
  have hslash := Derivative.normalizedDerivOfComplex_SL_slash (k := 2) mdifferentiable_E2
    (γ := ModularGroup.T)
  have hT_E2 : SlashAction.map (2 : ℤ) ModularGroup.T E2 = E2 := by
    funext z
    rw [ModularForm.SL_slash]
    change SlashAction.map (2 : ℤ) (sl2ZToGL2R ModularGroup.T) E2 z = E2 z
    rw [slash_T_apply, E2_T_smul]
  have hT10 : ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = 0 := by
    simp [ModularGroup.T]
  have hcf := congrFun hslash τ
  rw [hT_E2, Pi.sub_apply, hT10] at hcf
  simp only [Int.cast_zero, zero_div, mul_zero, zero_mul, sub_zero] at hcf
  have hT4 : SlashAction.map ((2 : ℤ) + 2) ModularGroup.T
      (Derivative.normalizedDerivOfComplex E2) τ =
      Derivative.normalizedDerivOfComplex E2 (ModularGroup.T • τ) := by
    rw [ModularForm.SL_slash]
    exact slash_T_apply 4 (Derivative.normalizedDerivOfComplex E2) τ
  rw [hT4] at hcf
  unfold ramanujanE2Fun
  rw [← hcf, E2_T_smul]

/-- `F₂(τ) = (1/(2πi)) E₂'(τ) - (1/12) E₂(τ)²` transforms with weight `4` under `S`:
`F₂(S • τ) = τ⁴ · F₂(τ)`. -/
theorem ramanujanE2Fun_S_smul (τ : UpperHalfPlane) :
    ramanujanE2Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * ramanujanE2Fun τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  -- Express `SlashAction.map 2 S E2` explicitly as `E2 - (6*I/π) • (w ↦ w⁻¹)`.
  set c : ℂ := 6 * Complex.I / (Real.pi : ℂ)
  have hSE2 : SlashAction.map (2 : ℤ) ModularGroup.S E2 =
      E2 - c • (fun w : UpperHalfPlane => ((w : ℂ))⁻¹) := by
    funext w
    have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) w
    rw [h, Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      EisensteinSeries.D2_S, riemannZeta_two]
    dsimp only [c]
    have hw : (w : ℂ) ≠ 0 := w.ne_zero
    field_simp [hpi, hI, hw]
  have hmdiff_inv : MDiff (fun w : UpperHalfPlane => ((w : ℂ))⁻¹) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    change 0 < z.im at hz
    have hne : z ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_im] at hz
      exact lt_irrefl 0 hz
    have hev : ((fun w : UpperHalfPlane => ((w : ℂ))⁻¹) ∘
        (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) =ᶠ[nhds z] (fun w : ℂ => w⁻¹) := by
      have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds hz] with w hw
      simp only [Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    exact ((differentiableAt_inv hne).congr_of_eventuallyEq hev).differentiableWithinAt
  have hLHS : Derivative.normalizedDerivOfComplex (SlashAction.map (2 : ℤ) ModularGroup.S E2) τ =
      Derivative.normalizedDerivOfComplex E2 τ +
        (3 / ((Real.pi : ℂ) ^ 2)) * (τ : ℂ) ^ (-(2 : ℤ)) := by
    rw [hSE2,
      Derivative.normalizedDerivOfComplex_sub _ _ mdifferentiable_E2 (hmdiff_inv.const_smul c),
      Derivative.normalizedDerivOfComplex_smul c _ hmdiff_inv]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [normalizedDerivOfComplex_inv_coe τ]
    dsimp only [c]
    field_simp [hpi, hI]
    ring
  have hRHS := congrFun
    (Derivative.normalizedDerivOfComplex_SL_slash (k := 2) mdifferentiable_E2 (γ := ModularGroup.S)) τ
  rw [hLHS] at hRHS
  have hS10 : ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = 1 := by
    simp [ModularGroup.S]
  have hSdenom : UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S))
      (τ : ℂ) = (τ : ℂ) := by
    change (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℂ) * (τ : ℂ) +
        (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℂ) = (τ : ℂ)
    simp [ModularGroup.S]
  have hS4 : SlashAction.map ((2 : ℤ) + 2) ModularGroup.S
      (Derivative.normalizedDerivOfComplex E2) τ =
      Derivative.normalizedDerivOfComplex E2 (ModularGroup.S • τ) * (τ : ℂ) ^ (-(4 : ℤ)) := by
    rw [ModularForm.SL_slash]
    exact slash_S_apply 4 (Derivative.normalizedDerivOfComplex E2) τ
  have hSE2_val : SlashAction.map (2 : ℤ) ModularGroup.S E2 τ = E2 τ - c * (τ : ℂ)⁻¹ := by
    rw [hSE2]; simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Pi.sub_apply, hS4, hS10, hSdenom, hSE2_val] at hRHS
  -- Solve `hRHS` for `D E2 (S • τ)` and combine with `E2_S_smul`.
  have hD_S : Derivative.normalizedDerivOfComplex E2 (ModularGroup.S • τ) =
      (τ : ℂ) ^ 4 * Derivative.normalizedDerivOfComplex E2 τ +
        (τ : ℂ) ^ 3 * E2 τ / ((Real.pi : ℂ) * Complex.I) -
        3 * (τ : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2 := by
    have hpow4 : (τ : ℂ) ^ (-(4 : ℤ)) = ((τ : ℂ) ^ 4)⁻¹ := by rw [zpow_neg]; rfl
    have hpow2 : (τ : ℂ) ^ (-(2 : ℤ)) = ((τ : ℂ) ^ 2)⁻¹ := by rw [zpow_neg]; rfl
    rw [hpow4, hpow2] at hRHS
    dsimp only [c] at hRHS
    have hmul := congrArg (fun x : ℂ => x * (τ : ℂ) ^ 4) hRHS
    have hclean : Derivative.normalizedDerivOfComplex E2 (ModularGroup.S • τ) =
        (Derivative.normalizedDerivOfComplex E2 τ + 3 / (Real.pi : ℂ) ^ 2 * ((τ : ℂ) ^ 2)⁻¹) * (τ : ℂ) ^ 4 +
          (↑(2 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (↑(1 : ℤ) / (τ : ℂ)) *
            (E2 τ - 6 * Complex.I / (Real.pi : ℂ) * (τ : ℂ)⁻¹)) * (τ : ℂ) ^ 4 := by
      have hsub : Derivative.normalizedDerivOfComplex E2 (ModularGroup.S • τ) * ((τ : ℂ) ^ 4)⁻¹ * (τ : ℂ) ^ 4 =
          Derivative.normalizedDerivOfComplex E2 (ModularGroup.S • τ) := by
        field_simp [hτ]
      linear_combination -hmul - hsub
    rw [hclean]
    field_simp [hτ, hpi, hI]
    ring_nf
  unfold ramanujanE2Fun
  rw [hD_S, E2_S_smul τ]
  field_simp [hpi, hI]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Packaging `F₂ = (1/(2πi)) E₂' - (1/12) E₂²` as a Concrete Weight-4 Level-1 Modular Form**
`ramanujanE2Form : ModularForm SL2ZRange 4`! -/
def ramanujanE2Form : ModularForm SL2ZRange 4 where
  toFun := ramanujanE2Fun
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    exact slash_SL2Z_invariant_of_S_T 4 ramanujanE2Fun
      (fun τ => by simpa [zpow_natCast] using ramanujanE2Fun_S_smul τ)
      ramanujanE2Fun_T_smul γ
  holo' := by
    change MDiff ramanujanE2Fun
    have hfun : ramanujanE2Fun =
        Derivative.normalizedDerivOfComplex E2 - (1 / 12 : ℂ) • (E2 * E2) := by
      funext τ
      unfold ramanujanE2Fun
      simp [sq, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [hfun]
    exact (Derivative.normalizedDerivOfComplex_mdifferentiable mdifferentiable_E2).sub
      ((mdifferentiable_E2.mul mdifferentiable_E2).const_smul (1 / 12 : ℂ))
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map (4 : ℤ) γ ramanujanE2Fun = ramanujanE2Fun := by
      rw [ModularForm.SL_slash]
      exact slash_SL2Z_invariant_of_S_T 4 ramanujanE2Fun
        (fun τ => by simpa [zpow_natCast] using ramanujanE2Fun_S_smul τ)
        ramanujanE2Fun_T_smul γ
    rw [hinv]
    have hfun : ramanujanE2Fun =
        Derivative.normalizedDerivOfComplex E2 - (1 / 12 : ℂ) • (E2 * E2) := by
      funext τ
      unfold ramanujanE2Fun
      simp [sq, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [hfun]
    exact isBoundedAtImInfty_sub'
      (isBoundedAtImInfty_normalizedDerivOfComplex E2_periodic mdifferentiable_E2
        isBoundedAtImInfty_E2)
      (isBoundedAtImInfty_smul' _ (isBoundedAtImInfty_mul' isBoundedAtImInfty_E2
        isBoundedAtImInfty_E2))

/-- Exact `q`-expansion of `ramanujanE2Form`. -/
theorem ramanujanE2Form_qExpansion :
    UpperHalfPlane.qExpansion 1 (ramanujanE2Form : UpperHalfPlane → ℂ) =
      thetaDeriv (UpperHalfPlane.qExpansion 1 E2) -
        (1 / 12 : ℂ) • (UpperHalfPlane.qExpansion 1 E2 ^ 2) := by
  have hana_dE2 : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex E2)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one
      (periodic_normalizedDerivOfComplex E2_periodic mdifferentiable_E2 isBoundedAtImInfty_E2)
      (Derivative.normalizedDerivOfComplex_mdifferentiable mdifferentiable_E2)
      (isBoundedAtImInfty_normalizedDerivOfComplex E2_periodic mdifferentiable_E2
        isBoundedAtImInfty_E2)
  have hana_E2 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one E2_periodic
      mdifferentiable_E2 isBoundedAtImInfty_E2
  have hana_sq : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (E2 * E2)) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hana_E2.continuousAt hana_E2.continuousAt]
    exact hana_E2.mul hana_E2
  have hana_smul : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 ((1 / 12 : ℂ) • (E2 * E2))) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hana_sq.continuousAt]
    exact hana_sq.const_smul
  have hcoe : (ramanujanE2Form : UpperHalfPlane → ℂ) =
      Derivative.normalizedDerivOfComplex E2 - (1 / 12 : ℂ) • (E2 * E2) := by
    funext τ
    change ramanujanE2Fun τ = _
    unfold ramanujanE2Fun
    simp [sq, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [hcoe, UpperHalfPlane.qExpansion_sub hana_dE2 hana_smul,
    UpperHalfPlane.qExpansion_smul hana_sq,
    UpperHalfPlane.qExpansion_mul hana_E2 hana_E2,
    qExpansion_normalizedDerivOfComplex E2_periodic mdifferentiable_E2 isBoundedAtImInfty_E2, sq]

/-- **Identity in `M₄(SL₂(ℤ))`**: `ramanujanE2Form = -(1 / 12) • E₄`. -/
theorem ramanujanE2Form_eq :
    ramanujanE2Form = (-(1 / 12 : ℂ)) • ModularForm.E₄ := by
  have h := modularForm_SL2Z_weight_four_eq_smul_E4 ramanujanE2Form
  have h0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (ramanujanE2Form : UpperHalfPlane → ℂ)) =
      -(1 / 12 : ℂ) := by
    rw [ramanujanE2Form_qExpansion, map_sub, coeff_zero_thetaDeriv, zero_sub, map_smul, smul_eq_mul,
      PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      E2_qExpansion_coeff 0, if_pos rfl]
    norm_num
  rwa [h0] at h

/-- **Analytic Ramanujan Differential Equation for `E₂`**:
$$\frac{1}{2\pi i} E_2'(\tau) = \frac{E_2(\tau)^2 - E_4(\tau)}{12}.$$ -/
theorem normalizedDerivOfComplex_E2 (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex E2 τ = (E2 τ ^ 2 - E4 τ) / 12 := by
  have h := congrArg (fun u : ModularForm SL2ZRange 4 => u τ) ramanujanE2Form_eq
  change ramanujanE2Fun τ = -(1 / 12 : ℂ) * ModularForm.E₄ τ at h
  unfold ramanujanE2Fun at h
  rw [← E4_eq_modularForm_E4 τ] at h
  linear_combination h

/-- **Formal Integer Ramanujan Differential Equation for `E₂`** in `ℤ⟦q⟧`:
`12 * θ(E₂) = E₂² - E₄`. -/
theorem ramanujan_diff_E2_Z :
    (12 : PowerSeries ℤ) * thetaDeriv E2SeriesZ = E2SeriesZ ^ 2 - E4SeriesZ := by
  have hq := congrArg (fun u : ModularForm SL2ZRange 4 =>
      UpperHalfPlane.qExpansion 1 (u : UpperHalfPlane → ℂ)) ramanujanE2Form_eq
  rw [ramanujanE2Form_qExpansion, FunLike.coe_smul,
    ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL,
    ← E4_eq_coe, ← E2SeriesZ_map_eq, ← E4SeriesZ_map_eq, thetaDeriv_map, ← map_pow] at hq
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hq
  simp only [map_sub, map_smul, smul_eq_mul, PowerSeries.coeff_map] at hcf
  have hC : ((PowerSeries.coeff n ((12 : PowerSeries ℤ) * thetaDeriv E2SeriesZ) : ℤ) : ℂ) =
      ((PowerSeries.coeff n (E2SeriesZ ^ 2 - E4SeriesZ) : ℤ) : ℂ) := by
    rw [coeff_ofNat_mul, map_sub]
    push_cast
    have hcast : ∀ z : ℤ, Int.castRingHom ℂ z = (z : ℂ) := fun _ => rfl
    simp only [hcast] at hcf
    linear_combination 12 * hcf
  exact Int.cast_injective hC

/-- **Formal Rational Ramanujan Differential Equation for `E₂`** in `ℚ⟦q⟧`:
`θ(E₂) = (1 / 12) • (E₂² - E₄)`. -/
theorem ramanujan_diff_E2 :
    thetaDeriv E2Series = (1 / 12 : ℚ) • (E2Series ^ 2 - E4Series) := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) ramanujan_diff_E2_Z
  rw [map_mul, map_ofNat, ← thetaDeriv_map, map_sub, map_pow] at hmap
  change (12 : PowerSeries ℚ) * thetaDeriv E2Series = E2Series ^ 2 - E4Series at hmap
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hmap
  rw [coeff_ofNat_mul] at hcf
  rw [map_smul, smul_eq_mul, ← hcf]
  ring

/-! ### Explicit Divisor-Sum Convolution Identities Extracted from Ramanujan's Differential Equations -/

/-- Helper rewriting `coeff n (f * g)` as `a₀ b_n + a_n b₀ + ∑_{k ∈ Ioo 0 n} a_k b_{n - k}` for `n ≥ 1`. -/
private lemma coeff_mul_split_Ioo {R : Type*} [CommRing R] (f g : PowerSeries R) {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff n g +
        PowerSeries.coeff n f * PowerSeries.coeff 0 g +
        ∑ k ∈ Finset.Ioo 0 n, PowerSeries.coeff k f * PowerSeries.coeff (n - k) g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g) n,
    Finset.sum_range_succ, Nat.sub_self]
  have hrange : Finset.range n = Finset.range ((n - 1) + 1) := by congr 1; omega
  rw [hrange, Finset.sum_range_succ', Nat.sub_zero]
  have hmid : (∑ k ∈ Finset.range (n - 1),
        PowerSeries.coeff (k + 1) f * PowerSeries.coeff (n - (k + 1)) g) =
      ∑ k ∈ Finset.Ioo 0 n, PowerSeries.coeff k f * PowerSeries.coeff (n - k) g := by
    refine Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      exact Finset.mem_Ioo.mpr ⟨Nat.succ_pos k, by omega⟩
    · intro j hj
      rcases Finset.mem_Ioo.mp hj with ⟨hj0, hjn⟩
      exact Finset.mem_range.mpr (by omega)
    · intro k _; exact Nat.add_sub_cancel k 1
    · intro j hj
      rcases Finset.mem_Ioo.mp hj with ⟨hj0, _⟩
      exact Nat.sub_add_cancel hj0
    · intro k _; rfl
  rw [hmid]
  ring

/-- **Besge–Glaisher–Ramanujan `σ₁`-Convolution Identity** (from `12 θ(E₂) = E₂² - E₄`):
for every `n ≥ 1`,
$$5\,\sigma_3(n) = (6n - 1)\,\sigma_1(n) + 12 \sum_{k = 1}^{n - 1} \sigma_1(k)\,\sigma_1(n - k).$$ -/
theorem sigma1_convolution (n : ℕ) (hn : 1 ≤ n) :
    5 * ArithmeticFunction.sigma 3 n =
      (6 * n - 1) * ArithmeticFunction.sigma 1 n +
        12 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 1 k * ArithmeticFunction.sigma 1 (n - k) := by
  have hn0 : n ≠ 0 := by omega
  have hcf := congrArg (PowerSeries.coeff n) ramanujan_diff_E2_Z
  rw [coeff_ofNat_mul, coeff_thetaDeriv, map_sub, sq, coeff_mul_split_Ioo _ _ hn,
    coeff_E2SeriesZ 0, if_pos rfl, coeff_E2SeriesZ n, if_neg hn0,
    coeff_E4SeriesZ n, if_neg hn0] at hcf
  have hsum : (∑ k ∈ Finset.Ioo 0 n,
        PowerSeries.coeff k E2SeriesZ * PowerSeries.coeff (n - k) E2SeriesZ) =
      576 * ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * (ArithmeticFunction.sigma 1 (n - k) : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_Ioo.mp hk with ⟨hk0, hkn⟩
    rw [coeff_E2SeriesZ k, if_neg (by omega), coeff_E2SeriesZ (n - k), if_neg (by omega)]
    ring
  rw [hsum] at hcf
  have hZ : ((5 * ArithmeticFunction.sigma 3 n : ℕ) : ℤ) =
      (((6 * n - 1) * ArithmeticFunction.sigma 1 n +
        12 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 1 k * ArithmeticFunction.sigma 1 (n - k) : ℕ) : ℤ) := by
    push_cast
    have h6n : ((6 * n - 1 : ℕ) : ℤ) = 6 * (n : ℤ) - 1 := by omega
    rw [h6n]
    linarith
  exact Int.ofNat.inj hZ

/-- **Ramanujan's `σ₃`–`σ₁` Convolution Identity** (from `3 θ(E₄) = E₂ E₄ - E₆`):
for every `n ≥ 1`,
$$21\,\sigma_5(n) = (30 n - 10)\,\sigma_3(n) + \sigma_1(n) + 240 \sum_{k = 1}^{n - 1} \sigma_1(k)\,\sigma_3(n - k).$$ -/
theorem sigma3_sigma1_convolution (n : ℕ) (hn : 1 ≤ n) :
    21 * ArithmeticFunction.sigma 5 n =
      (30 * n - 10) * ArithmeticFunction.sigma 3 n + ArithmeticFunction.sigma 1 n +
        240 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 1 k * ArithmeticFunction.sigma 3 (n - k) := by
  have hn0 : n ≠ 0 := by omega
  have hcf := congrArg (PowerSeries.coeff n) ramanujan_diff_E4_Z
  rw [coeff_ofNat_mul, coeff_thetaDeriv, map_sub, coeff_mul_split_Ioo _ _ hn,
    coeff_E2SeriesZ 0, if_pos rfl, coeff_E2SeriesZ n, if_neg hn0,
    coeff_E4SeriesZ 0, if_pos rfl, coeff_E4SeriesZ n, if_neg hn0,
    coeff_E6SeriesZ n, if_neg hn0] at hcf
  have hsum : (∑ k ∈ Finset.Ioo 0 n,
        PowerSeries.coeff k E2SeriesZ * PowerSeries.coeff (n - k) E4SeriesZ) =
      -5760 * ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * (ArithmeticFunction.sigma 3 (n - k) : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_Ioo.mp hk with ⟨hk0, hkn⟩
    rw [coeff_E2SeriesZ k, if_neg (by omega), coeff_E4SeriesZ (n - k), if_neg (by omega)]
    ring
  rw [hsum] at hcf
  have hZ : ((21 * ArithmeticFunction.sigma 5 n : ℕ) : ℤ) =
      (((30 * n - 10) * ArithmeticFunction.sigma 3 n + ArithmeticFunction.sigma 1 n +
        240 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 1 k * ArithmeticFunction.sigma 3 (n - k) : ℕ) : ℤ) := by
    push_cast
    have h30n : ((30 * n - 10 : ℕ) : ℤ) = 30 * (n : ℤ) - 10 := by omega
    rw [h30n]
    linarith
  exact Int.ofNat.inj hZ

/-- **Ramanujan's `σ₅`–`σ₁` Convolution Identity** (from `2 θ(E₆) = E₂ E₆ - E₄²` and `E₄² = E₈`):
for every `n ≥ 1`,
$$20\,\sigma_7(n) + \sigma_1(n) = (42 n - 21)\,\sigma_5(n) + 504 \sum_{k = 1}^{n - 1} \sigma_1(k)\,\sigma_5(n - k).$$ -/
theorem sigma5_sigma1_convolution (n : ℕ) (hn : 1 ≤ n) :
    20 * ArithmeticFunction.sigma 7 n + ArithmeticFunction.sigma 1 n =
      (42 * n - 21) * ArithmeticFunction.sigma 5 n +
        504 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 1 k * ArithmeticFunction.sigma 5 (n - k) := by
  have hn0 : n ≠ 0 := by omega
  have hE4sq_coeff : PowerSeries.coeff n (E4SeriesZ ^ 2) =
      480 * (ArithmeticFunction.sigma 7 n : ℤ) := by
    have hC : ((PowerSeries.coeff n (E4SeriesZ ^ 2) : ℤ) : ℂ) =
        ((480 * (ArithmeticFunction.sigma 7 n : ℤ) : ℤ) : ℂ) := by
      have hfun : (E8Eisenstein : UpperHalfPlane → ℂ) =
          (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
        funext τ
        rw [← E4_sq_eq_E8Eisenstein τ, sq, E4_eq_modularForm_E4 τ]
        rfl
      have hq : UpperHalfPlane.qExpansion 1 E8Eisenstein =
          PowerSeries.map (Int.castRingHom ℂ) (E4SeriesZ ^ 2) := by
        rw [hfun, ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL
          ModularForm.E₄ ModularForm.E₄, ← E4_eq_coe, ← E4SeriesZ_map_eq, ← sq, map_pow]
      have hcf := congrArg (PowerSeries.coeff n) hq
      rw [E8Eisenstein_qExpansion_coeff n, if_neg hn0, PowerSeries.coeff_map] at hcf
      push_cast
      exact hcf.symm
    exact Int.cast_injective hC
  have hcf := congrArg (PowerSeries.coeff n) ramanujan_diff_E6_Z
  rw [coeff_ofNat_mul, coeff_thetaDeriv, map_sub, coeff_mul_split_Ioo _ _ hn,
    coeff_E2SeriesZ 0, if_pos rfl, coeff_E2SeriesZ n, if_neg hn0,
    coeff_E6SeriesZ 0, if_pos rfl, coeff_E6SeriesZ n, if_neg hn0, hE4sq_coeff] at hcf
  have hsum : (∑ k ∈ Finset.Ioo 0 n,
        PowerSeries.coeff k E2SeriesZ * PowerSeries.coeff (n - k) E6SeriesZ) =
      12096 * ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * (ArithmeticFunction.sigma 5 (n - k) : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_Ioo.mp hk with ⟨hk0, hkn⟩
    rw [coeff_E2SeriesZ k, if_neg (by omega), coeff_E6SeriesZ (n - k), if_neg (by omega)]
    ring
  rw [hsum] at hcf
  have hZ : ((20 * ArithmeticFunction.sigma 7 n + ArithmeticFunction.sigma 1 n : ℕ) : ℤ) =
      (((42 * n - 21) * ArithmeticFunction.sigma 5 n +
        504 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 1 k * ArithmeticFunction.sigma 5 (n - k) : ℕ) : ℤ) := by
    push_cast
    have h42n : ((42 * n - 21 : ℕ) : ℤ) = 42 * (n : ℤ) - 21 := by omega
    rw [h42n]
    linarith
  exact Int.ofNat.inj hZ

end SerreDerivativeAndRamanujanEquations

/-! ## Section 4: Logarithmic Derivative `θ(Δ) = E₂ · Δ`, `τ(n)` Recurrence, & Dedekind–Jacobi Product Formula -/

section LogarithmicDerivativeAndEulerProduct

/-- **Exact Integer Logarithmic Derivative of `Δ(q)`**:
$$\theta(\Delta_{\mathbb{Z}}) = E_2 \cdot \Delta_{\mathbb{Z}} \quad \text{in } \mathbb{Z}\llbracket q \rrbracket.$$ -/
theorem thetaDeriv_deltaZ_eq_E2_mul_deltaZ :
    thetaDeriv ramanujanDeltaPowerSeriesZ = E2SeriesZ * ramanujanDeltaPowerSeriesZ := by
  have h1728 : (1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ =
      E4SeriesZ ^ 3 - E6SeriesZ ^ 2 := mul_1728_ramanujanDeltaPowerSeriesZ
  have hderiv := congrArg thetaDeriv h1728
  rw [thetaDeriv_mul, show thetaDeriv (1728 : PowerSeries ℤ) = 0 by
      simpa using thetaDeriv_C (1728 : ℤ),
    zero_mul, zero_add, thetaDeriv_sub, thetaDeriv_pow, thetaDeriv_pow] at hderiv
  have hcalc : (1728 : PowerSeries ℤ) * thetaDeriv ramanujanDeltaPowerSeriesZ =
      (1728 : PowerSeries ℤ) * (E2SeriesZ * ramanujanDeltaPowerSeriesZ) := by
    calc (1728 : PowerSeries ℤ) * thetaDeriv ramanujanDeltaPowerSeriesZ
        = E4SeriesZ ^ 2 * ((3 : PowerSeries ℤ) * thetaDeriv E4SeriesZ) -
            E6SeriesZ * ((2 : PowerSeries ℤ) * thetaDeriv E6SeriesZ) := by
          rw [hderiv]; norm_num; ring
      _ = E4SeriesZ ^ 2 * (E2SeriesZ * E4SeriesZ - E6SeriesZ) -
            E6SeriesZ * (E2SeriesZ * E6SeriesZ - E4SeriesZ ^ 2) := by
          rw [ramanujan_diff_E4_Z, ramanujan_diff_E6_Z]
      _ = E2SeriesZ * (E4SeriesZ ^ 3 - E6SeriesZ ^ 2) := by ring
      _ = E2SeriesZ * ((1728 : PowerSeries ℤ) * ramanujanDeltaPowerSeriesZ) := by rw [h1728]
      _ = (1728 : PowerSeries ℤ) * (E2SeriesZ * ramanujanDeltaPowerSeriesZ) := by ring
  ext n
  have hcf := congrArg (PowerSeries.coeff n) hcalc
  rw [coeff_ofNat_mul, coeff_ofNat_mul] at hcf
  exact mul_left_cancel₀ (by norm_num : (1728 : ℤ) ≠ 0) hcf

/-- **Exact Rational Logarithmic Derivative of `Δ(q)`**:
$$\theta(\Delta_{\mathbb{Q}}) = E_2 \cdot \Delta_{\mathbb{Q}} \quad \text{in } \mathbb{Q}\llbracket q \rrbracket.$$ -/
theorem thetaDeriv_delta_eq_E2_mul_delta :
    thetaDeriv ramanujanDeltaPowerSeriesQ = E2Series * ramanujanDeltaPowerSeriesQ := by
  unfold ramanujanDeltaPowerSeriesQ E2Series
  rw [thetaDeriv_map, thetaDeriv_deltaZ_eq_E2_mul_deltaZ, map_mul]

/-- **Analytic Logarithmic Derivative of `Δ(τ)`**:
$$\frac{1}{2\pi i} \Delta'(\tau) = E_2(\tau)\,\Delta(\tau) \qquad (\forall \tau \in \mathbb{H}).$$ -/
theorem normalizedDerivOfComplex_delta_eq_E2_mul_delta (τ : UpperHalfPlane) :
    Derivative.normalizedDerivOfComplex (ramanujanDelta : UpperHalfPlane → ℂ) τ =
      E2 τ * ramanujanDelta τ := by
  have hserre : serreDeriv 12 (CuspForm.toModularFormₗ ramanujanDelta) = 0 := by
    rw [← ModularForm.qExpansion_eq_zero_iff zero_lt_one one_mem_strictPeriods_SL]
    rw [serreDeriv_qExpansion]
    have hcoe : ((CuspForm.toModularFormₗ ramanujanDelta : ModularForm SL2ZRange 12) :
        UpperHalfPlane → ℂ) = (ramanujanDelta : UpperHalfPlane → ℂ) := rfl
    rw [hcoe, ← ramanujanDeltaPowerSeriesZ_map_eq, ← E2SeriesZ_map_eq,
      thetaDeriv_map, thetaDeriv_deltaZ_eq_E2_mul_deltaZ, map_mul]
    norm_num
  have hτ := congrArg (fun u : ModularForm SL2ZRange 14 => u τ) hserre
  rw [serreDeriv_apply, zero_apply] at hτ
  change Derivative.normalizedDerivOfComplex (ramanujanDelta : UpperHalfPlane → ℂ) τ -
      (12 : ℂ) / 12 * E2 τ * ramanujanDelta τ = 0 at hτ
  linear_combination hτ

/-- **Vanishing of the Weight-12 Serre Derivative of `Δ`**: `∂₁₂(Δ) = 0` in `M₁₄(SL₂(ℤ))`. -/
theorem serreDeriv_ramanujanDelta_eq_zero :
    serreDeriv 12 (CuspForm.toModularFormₗ ramanujanDelta) = 0 := by
  ext τ
  rw [serreDeriv_apply, zero_apply]
  change Derivative.normalizedDerivOfComplex (ramanujanDelta : UpperHalfPlane → ℂ) τ -
      (12 : ℂ) / 12 * E2 τ * ramanujanDelta τ = 0
  rw [normalizedDerivOfComplex_delta_eq_E2_mul_delta τ]
  ring

/-- **Exact Recurrence for Ramanujan's `τ(n)` via `σ₁`** (`0` assumptions!):
for every `n ≥ 1`,
$$(n - 1)\,\tau(n) = -24 \sum_{k = 1}^{n - 1} \sigma_1(k)\,\tau(n - k).$$ -/
theorem ramanujanTau_recurrence_sigma1 (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℤ) - 1) * ramanujanTau n =
      -24 * ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * ramanujanTau (n - k) := by
  have hcf := congrArg (PowerSeries.coeff n) thetaDeriv_deltaZ_eq_E2_mul_deltaZ
  rw [coeff_thetaDeriv, coeff_mul_split_Ioo _ _ hn,
    coeff_E2SeriesZ 0, if_pos rfl, one_mul] at hcf
  have htau0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  rw [htau0, mul_zero, add_zero] at hcf
  have hsum : (∑ k ∈ Finset.Ioo 0 n,
        PowerSeries.coeff k E2SeriesZ * PowerSeries.coeff (n - k) ramanujanDeltaPowerSeriesZ) =
      -24 * ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * ramanujanTau (n - k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_Ioo.mp hk with ⟨hk0, _⟩
    rw [coeff_E2SeriesZ k, if_neg (by omega)]
    change (-24 * (ArithmeticFunction.sigma 1 k : ℤ)) * ramanujanTau (n - k) = _
    ring
  rw [hsum] at hcf
  change (n : ℤ) * ramanujanTau n = ramanujanTau n +
      -24 * ∑ k ∈ Finset.Ioo 0 n,
        (ArithmeticFunction.sigma 1 k : ℤ) * ramanujanTau (n - k) at hcf
  linear_combination hcf

/-- Instant verification via `ramanujanTau_recurrence_sigma1`: `τ(5) = 4830`. -/
theorem ramanujanTau_five : ramanujanTau 5 = 4830 := by
  have h := ramanujanTau_recurrence_sigma1 5 (by decide)
  have hIoo : Finset.Ioo 0 5 = {1, 2, 3, 4} := by decide
  have hs1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
  have hs2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
  have hs3 : ArithmeticFunction.sigma 1 3 = 4 := by decide
  have hs4 : ArithmeticFunction.sigma 1 4 = 7 := by decide
  rw [hIoo] at h
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, OfNat.one_ne_ofNat,
    Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton, hs1, hs2, hs3, hs4] at h
  norm_num [ramanujanTau_one, ramanujanTau_two, ramanujanTau_three, ramanujanTau_four] at h
  linarith

/-! ### Formal Infinite Product `eulerProd24 = X · ∏_{n ≥ 1} (1 - X^n)^24` & Dedekind–Jacobi Formula -/

/-- Finite partial Euler product `X · ∏_{m = 1}^N (1 - X^m)^24 ∈ ℤ⟦X⟧`. -/
def eulerProd24Trunc (N : ℕ) : PowerSeries ℤ :=
  PowerSeries.X * ∏ m ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ m) ^ 24

/-- Multiplying by a power series `g` with `g₀ = 1` and `g_k = 0` for `1 ≤ k ≤ n` preserves
all coefficients up to degree `n`. -/
private lemma coeff_mul_eq_of_coeff_zero_one {R : Type*} [CommRing R]
    (f g : PowerSeries R) {n : ℕ}
    (hg0 : PowerSeries.coeff 0 g = 1)
    (hgk : ∀ k, 1 ≤ k → k ≤ n → PowerSeries.coeff k g = 0) :
    PowerSeries.coeff n (f * g) = PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g) n,
    Finset.sum_eq_single n]
  · rw [Nat.sub_self, hg0, mul_one]
  · intro k hk hkn
    have hlt : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn
    rw [hgk (n - k) (by omega) (by omega), mul_zero]
  · intro hn; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn

/-- For `m > n`, `(1 - X^m)^24` has constant term `1` and vanishing coefficients in degrees `1..n`. -/
private lemma coeff_one_sub_X_pow_24 {m n : ℕ} (hmn : n < m) :
    PowerSeries.coeff 0 ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24) = 1 ∧
      ∀ k, 1 ≤ k → k ≤ n → PowerSeries.coeff k ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24) = 0 := by
  have hm0 : m ≠ 0 := by omega
  have hbase0 : PowerSeries.coeff 0 (1 - PowerSeries.X ^ m : PowerSeries ℤ) = 1 := by
    rw [map_sub, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_X_pow, if_neg hm0.symm,
      sub_zero]
  have hbasek : ∀ k, 1 ≤ k → k ≤ n →
      PowerSeries.coeff k (1 - PowerSeries.X ^ m : PowerSeries ℤ) = 0 := by
    intro k hk1 hkn
    rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_X_pow,
      if_neg (by omega), sub_zero]
  have hpow : ∀ r : ℕ,
      PowerSeries.coeff 0 ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ r) = 1 ∧
      ∀ k, 1 ≤ k → k ≤ n → PowerSeries.coeff k ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ r) = 0 := by
    intro r
    induction r with
    | zero =>
      refine ⟨by simp, fun k hk1 _ => ?_⟩
      rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
    | succ r ih =>
      rw [pow_succ]
      refine ⟨?_, fun k hk1 hkn => ?_⟩
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff,
          ih.1, hbase0, mul_one]
      · rw [coeff_mul_eq_of_coeff_zero_one _ _ hbase0 (fun j hj1 hjk => hbasek j hj1 (hjk.trans hkn))]
        exact ih.2 k hk1 hkn
  exact hpow 24

/-- Exact coefficient stabilization of `eulerProd24Trunc`:
for every `N ≥ n`, `coeff n (eulerProd24Trunc N) = coeff n (eulerProd24Trunc n)`. -/
theorem coeff_eulerProd24Trunc_eq {n N : ℕ} (h : n ≤ N) :
    PowerSeries.coeff n (eulerProd24Trunc N) = PowerSeries.coeff n (eulerProd24Trunc n) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N hle ih =>
    have hsucc : eulerProd24Trunc (N + 1) =
        eulerProd24Trunc N * (1 - PowerSeries.X ^ (N + 1)) ^ 24 := by
      unfold eulerProd24Trunc
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp)]
      ring
    have ⟨h0, hk⟩ := coeff_one_sub_X_pow_24 (m := N + 1) (n := n) (by omega)
    rw [hsucc, coeff_mul_eq_of_coeff_zero_one _ _ h0 hk, ih]

/-- **The Exact Formal Dedekind–Jacobi Infinite Product `X · ∏_{n ≥ 1} (1 - X^n)^24 ∈ ℤ⟦X⟧`**,
defined via exact coefficient stabilization of `eulerProd24Trunc`. -/
def eulerProd24 : PowerSeries ℤ :=
  PowerSeries.mk fun n => PowerSeries.coeff n (eulerProd24Trunc n)

/-- Every coefficient `k ≤ N` of `eulerProd24` agrees with `eulerProd24Trunc N`. -/
theorem coeff_eulerProd24_eq_trunc {k N : ℕ} (h : k ≤ N) :
    PowerSeries.coeff k eulerProd24 = PowerSeries.coeff k (eulerProd24Trunc N) := by
  unfold eulerProd24
  rw [PowerSeries.coeff_mk, coeff_eulerProd24Trunc_eq h]

@[simp]
theorem coeff_zero_eulerProd24 : PowerSeries.coeff 0 eulerProd24 = 0 := by
  rw [coeff_eulerProd24_eq_trunc (le_refl 0)]
  unfold eulerProd24Trunc
  simp

@[simp]
theorem coeff_one_eulerProd24 : PowerSeries.coeff 1 eulerProd24 = 1 := by
  rw [coeff_eulerProd24_eq_trunc (le_refl 1)]
  unfold eulerProd24Trunc
  have hIcc : Finset.Icc 1 1 = {1} := by decide
  rw [hIcc, Finset.prod_singleton, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_sub, map_one, pow_one,
    PowerSeries.constantCoeff_X]
  norm_num

/-- Formal geometric series `G_m(X) = ∑_{j ≥ 0} X^{m j} = (1 - X^m)⁻¹ ∈ ℤ⟦X⟧` for `m ≥ 1`. -/
private def geomSeriesZ (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if m ∣ k then 1 else 0

private lemma one_sub_X_pow_mul_geomSeriesZ {m : ℕ} (hm : 1 ≤ m) :
    (1 - PowerSeries.X ^ m : PowerSeries ℤ) * geomSeriesZ m = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  by_cases hkm : k < m
  · have hX : PowerSeries.coeff k (PowerSeries.X ^ m * geomSeriesZ m) = 0 := by
      rw [PowerSeries.coeff_X_pow_mul']
      simp [not_le.mpr hkm]
    rw [hX, sub_zero, geomSeriesZ, PowerSeries.coeff_mk]
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hndvd : ¬ m ∣ k := fun hdvd =>
        not_le.mpr hkm (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd)
      simp [hk0, hndvd]
  · have hge : m ≤ k := le_of_not_gt hkm
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0, PowerSeries.coeff_X_pow_mul', if_pos hge,
      geomSeriesZ, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have hdvd_iff : m ∣ k ↔ m ∣ k - m := by
      constructor
      · intro h; exact Nat.dvd_sub h (dvd_refl m)
      · intro h
        have hsum : k = (k - m) + m := (Nat.sub_add_cancel hge).symm
        rw [hsum]
        exact dvd_add h (dvd_refl m)
    by_cases hd : m ∣ k
    · rw [if_pos hd, if_pos (hdvd_iff.mp hd), sub_self]
    · rw [if_neg hd, if_neg (mt hdvd_iff.mpr hd), sub_self]

/-- Exact formal logarithmic derivative of any finite subproduct `X · ∏_{m ∈ s} (1 - X^m)^24`. -/
private lemma thetaDeriv_finset_eulerProd (s : Finset ℕ) (hs : ∀ m ∈ s, 1 ≤ m) :
    thetaDeriv (PowerSeries.X * ∏ m ∈ s, (1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24) =
      (1 - 24 * ∑ m ∈ s, (m : PowerSeries ℤ) * PowerSeries.X ^ m * geomSeriesZ m) *
        (PowerSeries.X * ∏ m ∈ s, (1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert m s hms ih =>
    have hm : 1 ≤ m := hs m (Finset.mem_insert_self m s)
    have hs' : ∀ j ∈ s, 1 ≤ j := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hih := ih hs'
    rw [Finset.prod_insert hms, Finset.sum_insert hms]
    set Q : PowerSeries ℤ := PowerSeries.X * ∏ j ∈ s, (1 - PowerSeries.X ^ j : PowerSeries ℤ) ^ 24
    set L : PowerSeries ℤ := 1 - 24 * ∑ j ∈ s, (j : PowerSeries ℤ) * PowerSeries.X ^ j * geomSeriesZ j
    have hXQ : PowerSeries.X * ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24 *
        ∏ j ∈ s, (1 - PowerSeries.X ^ j : PowerSeries ℤ) ^ 24) =
        (1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24 * Q := by
      dsimp only [Q]; ring
    rw [hXQ, thetaDeriv_mul, hih]
    have hfactor : thetaDeriv ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24) =
        (-(24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ m * geomSeriesZ m)) *
          (1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 24 := by
      have hsub : thetaDeriv (1 - PowerSeries.X ^ m : PowerSeries ℤ) =
          -(m : PowerSeries ℤ) * PowerSeries.X ^ m := by
        rw [thetaDeriv_sub, thetaDeriv_one, thetaDeriv_pow, thetaDeriv_X, zero_sub]
        have hpow : PowerSeries.X ^ (m - 1) * (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X ^ m := by
          rw [← pow_succ, Nat.sub_add_cancel hm]
        calc -((m : PowerSeries ℤ) * PowerSeries.X ^ (m - 1) * PowerSeries.X)
            = -(m : PowerSeries ℤ) * (PowerSeries.X ^ (m - 1) * PowerSeries.X) := by ring
          _ = -(m : PowerSeries ℤ) * PowerSeries.X ^ m := by rw [hpow]
      rw [thetaDeriv_pow, hsub]
      have hinv := one_sub_X_pow_mul_geomSeriesZ hm
      calc ((24 : ℕ) : PowerSeries ℤ) * (1 - PowerSeries.X ^ m) ^ (24 - 1) *
              (-(m : PowerSeries ℤ) * PowerSeries.X ^ m)
          = (-(24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) *
              (1 - PowerSeries.X ^ m) ^ 23 * 1 := by norm_num; ring
        _ = (-(24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) *
              (1 - PowerSeries.X ^ m) ^ 23 *
              ((1 - PowerSeries.X ^ m) * geomSeriesZ m) := by rw [hinv]
        _ = (-(24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ m * geomSeriesZ m)) *
              (1 - PowerSeries.X ^ m) ^ 24 := by ring
    rw [hfactor]
    dsimp only [L]
    ring

/-- **Exact Formal Differential Equation for the Infinite Euler Product**:
$$\theta\Bigl(q \prod_{n \ge 1} (1 - q^n)^{24}\Bigr) = E_2(q) \cdot \Bigl(q \prod_{n \ge 1} (1 - q^n)^{24}\Bigr).$$ -/
theorem thetaDeriv_eulerProd24 :
    thetaDeriv eulerProd24 = E2SeriesZ * eulerProd24 := by
  ext n
  set P : PowerSeries ℤ := eulerProd24Trunc n
  set L : PowerSeries ℤ :=
    1 - 24 * ∑ m ∈ Finset.Icc 1 n, (m : PowerSeries ℤ) * PowerSeries.X ^ m * geomSeriesZ m
  have hP_deriv : thetaDeriv P = L * P := by
    unfold P eulerProd24Trunc L
    exact thetaDeriv_finset_eulerProd (Finset.Icc 1 n) fun m hm => (Finset.mem_Icc.mp hm).1
  have hL_coeff : ∀ k ≤ n, PowerSeries.coeff k L = PowerSeries.coeff k E2SeriesZ := by
    intro k hkn
    rw [coeff_E2SeriesZ k]
    unfold L
    rw [map_sub, PowerSeries.coeff_one, coeff_ofNat_mul, map_sum]
    have hterm : ∀ m ∈ Finset.Icc 1 n,
        PowerSeries.coeff k ((m : PowerSeries ℤ) * PowerSeries.X ^ m * geomSeriesZ m) =
          if m ∣ k ∧ 1 ≤ k then (m : ℤ) else 0 := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      rw [mul_assoc, coeff_natCast_mul', PowerSeries.coeff_X_pow_mul']
      by_cases hmk : m ≤ k
      · rw [if_pos hmk, geomSeriesZ, PowerSeries.coeff_mk]
        have hk1 : 1 ≤ k := le_trans hm1 hmk
        have hdvd_iff : m ∣ k - m ↔ m ∣ k := by
          constructor
          · intro h
            have hsum : k = (k - m) + m := (Nat.sub_add_cancel hmk).symm
            rw [hsum]
            exact dvd_add h (dvd_refl m)
          · intro h; exact Nat.dvd_sub h (dvd_refl m)
        by_cases hd : m ∣ k
        · rw [if_pos (hdvd_iff.mpr hd), if_pos ⟨hd, hk1⟩, mul_one]
        · rw [if_neg (mt hdvd_iff.mp hd), if_neg (fun h => hd h.1), mul_zero]
      · rw [if_neg hmk, mul_zero]
        have hnot : ¬ (m ∣ k ∧ 1 ≤ k) := by
          rintro ⟨hd, hk1⟩
          exact hmk (Nat.le_of_dvd hk1 hd)
        rw [if_neg hnot]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · rw [if_neg hk0, if_neg hk0]
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have hdiv_sum : (∑ m ∈ Finset.Icc 1 n, if m ∣ k ∧ 1 ≤ k then (m : ℤ) else 0) =
          (ArithmeticFunction.sigma 1 k : ℤ) := by
        simp only [hk1, and_true, ArithmeticFunction.sigma_apply, pow_one, Nat.cast_sum]
        rw [← Finset.sum_filter]
        have hfilt : (Finset.Icc 1 n).filter (fun m => m ∣ k) = k.divisors := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨hm1, _⟩, hd⟩
            exact ⟨hd, hk0⟩
          · rintro ⟨hd, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk1, (Nat.le_of_dvd hk1 hd).trans hkn⟩, hd⟩
        rw [hfilt]
      rw [hdiv_sum]
      ring
  have hLHS : PowerSeries.coeff n (thetaDeriv eulerProd24) = PowerSeries.coeff n (thetaDeriv P) := by
    rw [coeff_thetaDeriv, coeff_thetaDeriv, coeff_eulerProd24_eq_trunc (le_refl n)]
  have hRHS : PowerSeries.coeff n (L * P) = PowerSeries.coeff n (E2SeriesZ * eulerProd24) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p.1 ≤ n := by
      have hadd := Finset.mem_antidiagonal.mp hp
      omega
    have hp2 : p.2 ≤ n := by
      have hadd := Finset.mem_antidiagonal.mp hp
      omega
    rw [hL_coeff p.1 hp1, coeff_eulerProd24_eq_trunc hp2]
  rw [hLHS, hP_deriv, hRHS]

/-- **UNCONDITIONAL FORMAL DEDEKIND–JACOBI PRODUCT FORMULA (`0` Assumptions!)**:
in `ℤ⟦q⟧`,
$$\Delta(q) = \sum_{n \ge 1} \tau(n)\, q^n = q \prod_{n \ge 1} (1 - q^n)^{24}.$$ -/
theorem ramanujanDelta_eq_q_mul_prod_one_sub_pow_24 :
    ramanujanDeltaPowerSeriesZ = eulerProd24 :=
  eq_of_thetaDeriv_eq_mul
    (by rw [coeff_E2SeriesZ 0, if_pos rfl])
    thetaDeriv_deltaZ_eq_E2_mul_deltaZ
    thetaDeriv_eulerProd24
    ramanujanTau_zero
    coeff_zero_eulerProd24
    (by
      change ramanujanTau 1 = PowerSeries.coeff 1 eulerProd24
      rw [ramanujanTau_one, coeff_one_eulerProd24])

/-- **UNCONDITIONAL ANALYTIC DEDEKIND–JACOBI INFINITE PRODUCT FORMULA (`0` Assumptions!)**:
for EVERY `τ : UpperHalfPlane`, setting `q = e^{2πiτ} = Function.Periodic.qParam 1 τ`,
$$\Delta(\tau) = q \prod_{n \in \mathbb{N}_+} (1 - q^n)^{24}.$$ -/
theorem delta_eq_euler_product_24 (τ : UpperHalfPlane) :
    ramanujanDelta τ =
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) *
        ∏' n : ℕ+, (1 - Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ (n : ℕ)) ^ 24 := by
  rw [ramanujanDelta_coe, ModularForm.discriminant_eq_q_prod τ]
  congr 1
  let e : ℕ ≃ ℕ+ :=
    { toFun := fun n => ⟨n + 1, Nat.succ_pos n⟩
      invFun := fun n => (n : ℕ) - 1
      left_inv := fun n => Nat.add_sub_cancel n 1
      right_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos) }
  rw [← e.tprod_eq (fun n : ℕ+ => (1 - Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ (n : ℕ)) ^ 24)]
  refine tprod_congr fun n => ?_
  rw [ModularForm.eta_q_eq_pow]
  unfold Function.Periodic.qParam
  simp only [Complex.ofReal_one, div_one]
  rfl

end LogarithmicDerivativeAndEulerProduct

end

end RHDirect.Stage9ModularDerivatives
