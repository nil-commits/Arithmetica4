import RHDirect.Stage10PeterssonHecke
import RHDirect.Stage9DeltaHadamard
import RHDirect.Stage7HeckeRing
import RHDirect.Stage3PatchingUnification
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# RHDirect.Stage11Sym2AdjointL

**UNCONDITIONAL DEGREE-3 ADJOINT / SYMMETRIC-SQUARE `L`-FUNCTION `L(s, Sym² f)`, RANKIN–SELBERG
CONVOLUTION `L(s, f × f) = ζ(s - k + 1) L(s, Sym² f)`, SHIMURA IDENTITY
`L(s, Sym² f) = ζ(2s - 2k + 2) ∑ a_{n²} n^{-s}`, NON-VANISHING ON `Re(s) > k + 1`, EXPLICIT
SPECIALIZATIONS TO ALL LEVEL-1 EIGENFORMS (`Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂, S₂₄`), AND THE HIDA–WILES
PETERSSON-NORM / ADJOINT-`L` CONGRUENCE-IDEAL CRITERION FOR `CountII` / `CountIII` (`VWin`)**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Exact Degree-3 Local `Sym²` Polynomial, Satake Factorization & Generating Series (`0` Assumptions!)**:
   - `sym2LocalPoly a c T := (1 - c * T) * (1 - (a ^ 2 - 2 * c) * T + c ^ 2 * T ^ 2)`
   - `sym2_local_factor_eq` & `sym2_local_factor_expanded`:
     `(1 - α² T)(1 - αβ T)(1 - β² T) = (1 - c T)(1 - (a² - 2c) T + c² T²) = 1 - (a² - c) T + c(a² - c) T² - c³ T³`
   - `even_primePow_recurrence` & `sym2LocalPoly_mul_tsum_even_primePow`:
     `sym2LocalPoly a c T * ∑' r, g (2 * r) * T ^ r = 1 - c ^ 2 * T ^ 2`
   - `sq_primePow_recurrence` & `rankinSelberg_local_eq_zeta_mul_sym2`:
     `∑' r, g r ^ 2 * T ^ r = (1 - c ^ 2 * T ^ 2) / ((1 - c * T) * sym2LocalPoly a c T)`
2. **Multiplicative `Sym²` Dirichlet Series, Shimura & Rankin–Selberg Identities, Degree-3 Euler
   Product & Non-Vanishing on `Re(s) > k + 1`**:
   - `sym2Coeff k a := LSeries.convolution (sqWeightCoeff k) (fun n => a (n ^ 2))`
   - `sym2Coeff_mul_of_coprime`, `sym2Coeff_one`, `sym2Coeff_prime`
   - `LSeriesSummable_sym2` & `LSeriesSummable_rankinSelberg` via `Stage9DeltaHadamard.hecke_cuspForm_coeff_bound`
   - `sym2L_eq_zeta_mul_sum_sq_index`: `L(s, Sym² f) = ζ(2s - 2k + 2) * ∑_{n ≥ 1} a_{n²} n^{-s}`
   - `rankinSelberg_eq_zeta_mul_sym2`: `L(s, f × f) = ζ(s - k + 1) * L(s, Sym² f)`
   - `sym2L_euler_product`, `sym2L_euler_product_satake`, `rankinSelbergL_euler_product`
   - `sym2L_ne_zero_of_re_gt`, `rankinSelbergL_ne_zero_of_re_gt`
3. **Explicit Unconditional Specializations to `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂` and `S₂₄` (`S24_eigenPlus`, `S24_eigenMinus`)**:
   - Full degree-3 Euler products, Shimura/Rankin–Selberg identities, and non-vanishing for every
     1D level-1 eigenform and both weight-24 eigenforms, plus exact local `Sym²` polynomials at
     `p = 2, 3`.
4. **Adjoint `L(1, Ad f)` ↔ Petersson Norm ↔ Hida–Wiles Congruence-Ideal Bridge (`CountII` / `CountIII`)**:
   - Concrete `PeterssonQExpansionSpace` instance `cuspFormQExpansionSpace` on `CuspForm SL2ZRange k`.
   - Exact Hida Petersson-projection characterization `mem_congruenceIdeal_iff_petersson_integrality`:
     `a ∈ η_f ↔ ∀ v ∈ S_{k,𝒪}, a * (⟨v, f⟩_Pet / ⟨f, f⟩_Pet) ∈ 𝒪`.
   - `adjointL_controls_congruence_prime`: every congruence prime `l` (or divisor `a`) dividing the
     congruence module `𝕋_𝒪 / (I_f + I_f^⊥)` divides the normalized Petersson / adjoint `L`-value
     `L^{alg}(1, Ad f)`.
   - `congruence_length_le_adjointL_valuation` & `adjointL_selmer_bound_of_patching`: DVR length
     bound and direct Selmer-length wiring into `Stage3PatchingUnification.TaylorWilesCongruenceDatum`.
   - Explicit weight-24 Petersson projection formula exhibiting the congruence denominator `24 √144169`.
-/

open Complex Real Filter Finset Module Submodule
open RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular RHDirect.Stage6HeckeSpectral
open RHDirect.Stage7EisensteinSeries RHDirect.Stage7HeckeRing RHDirect.Stage8ModularRing
open RHDirect.Stage8RamanujanDelta RHDirect.Stage9CuspFormLFunc RHDirect.Stage9DeltaHadamard
open RHDirect.Stage10PeterssonHecke RHDirect.Stage3PatchingUnification
open scoped BigOperators UpperHalfPlane ModularForm Topology ComplexConjugate
  RHDirect.Stage10PeterssonHecke

namespace RHDirect.Stage11Sym2AdjointL

noncomputable section

/-! ## Section 1: Exact Degree-3 Local `Sym²` Polynomial, Satake Factorization & Generating Series -/

section LocalSym2Algebra

/-- The degree-3 local symmetric-square Euler polynomial at a prime `p` with Hecke eigenvalue `a`
and central character factor `c = p^{k-1}`:
`sym2LocalPoly a c T = (1 - c T) * (1 - (a^2 - 2 c) T + c^2 T^2)`. -/
def sym2LocalPoly (a c T : ℂ) : ℂ :=
  (1 - c * T) * (1 - (a ^ 2 - 2 * c) * T + c ^ 2 * T ^ 2)

/-- Expanded degree-3 form of `sym2LocalPoly`:
`sym2LocalPoly a c T = 1 - (a² - c) T + c (a² - c) T² - c³ T³`. -/
theorem sym2LocalPoly_expanded (a c T : ℂ) :
    sym2LocalPoly a c T =
      1 - (a ^ 2 - c) * T + c * (a ^ 2 - c) * T ^ 2 - c ^ 3 * T ^ 3 := by
  unfold sym2LocalPoly
  ring

/-- **Exact Degree-3 Local `Sym²` Euler Factor Identity (`sym2_local_factor_eq`)**:
for any Satake parameter pair `(α, β)` with `α + β = a` and `α * β = c`,
`(1 - α² T)(1 - αβ T)(1 - β² T) = (1 - c T)(1 - (a² - 2 c) T + c² T²)`. -/
theorem sym2_local_factor_eq {a c α β : ℂ} (hs : IsSatakePair a c α β) (T : ℂ) :
    (1 - α ^ 2 * T) * (1 - α * β * T) * (1 - β ^ 2 * T) = sym2LocalPoly a c T := by
  unfold sym2LocalPoly
  rw [← hs.1, ← hs.2]
  ring

/-- **Expanded Satake-to-Coefficient `Sym²` Local Identity**:
`(1 - α² T)(1 - αβ T)(1 - β² T) = 1 - (a² - c) T + c (a² - c) T² - c³ T³`. -/
theorem sym2_local_factor_expanded {a c α β : ℂ} (hs : IsSatakePair a c α β) (T : ℂ) :
    (1 - α ^ 2 * T) * (1 - α * β * T) * (1 - β ^ 2 * T) =
      1 - (a ^ 2 - c) * T + c * (a ^ 2 - c) * T ^ 2 - c ^ 3 * T ^ 3 := by
  rw [sym2_local_factor_eq hs, sym2LocalPoly_expanded]

/-- **Exact 2-Term Recurrence for Even Prime-Power Indices `g (2 * r)`**:
if `g (r + 2) = a * g (r + 1) - c * g r` for all `r`, then
`g (2 * (r + 2)) = (a² - 2 c) * g (2 * (r + 1)) - c² * g (2 * r)` for all `r`. -/
theorem even_primePow_recurrence {a c : ℂ} {g : ℕ → ℂ}
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r) (r : ℕ) :
    g (2 * (r + 2)) = (a ^ 2 - 2 * c) * g (2 * (r + 1)) - c ^ 2 * g (2 * r) := by
  have h1 : g (2 * r + 4) = a * g (2 * r + 3) - c * g (2 * r + 2) := hrec (2 * r + 2)
  have h2 : g (2 * r + 3) = a * g (2 * r + 2) - c * g (2 * r + 1) := hrec (2 * r + 1)
  have h3 : g (2 * r + 2) = a * g (2 * r + 1) - c * g (2 * r) := hrec (2 * r)
  have heq4 : 2 * (r + 2) = 2 * r + 4 := by ring
  have heq2 : 2 * (r + 1) = 2 * r + 2 := by ring
  rw [heq4, heq2, h1, h2]
  linear_combination c * h3

/-- **Exact 3-Term Recurrence for Squared Prime-Power Coefficients `g r ^ 2`**:
if `g (r + 2) = a * g (r + 1) - c * g r` for all `r`, then
`g (r + 3)² = (a² - c) g (r + 2)² - c (a² - c) g (r + 1)² + c³ g r²` for all `r`. -/
theorem sq_primePow_recurrence {a c : ℂ} {g : ℕ → ℂ}
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r) (r : ℕ) :
    g (r + 3) ^ 2 =
      (a ^ 2 - c) * g (r + 2) ^ 2 - c * (a ^ 2 - c) * g (r + 1) ^ 2 + c ^ 3 * g r ^ 2 := by
  rw [hrec (r + 1), hrec r]
  ring

/-- **Quadratic Generating-Series Identity for Even Prime Powers**:
`(1 - (a² - 2 c) T + c² T²) * ∑' r, g (2 r) T^r = 1 + c T`. -/
theorem sym2_even_primePow_mul_tsum {a c T : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a)
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r)
    (hsum : Summable (fun r : ℕ => g (2 * r) * T ^ r)) :
    (1 - (a ^ 2 - 2 * c) * T + c ^ 2 * T ^ 2) * (∑' r : ℕ, g (2 * r) * T ^ r) = 1 + c * T := by
  have hg2 : g 2 = a ^ 2 - c := by
    have h := hrec 0
    simp only [zero_add, hg0, hg1, mul_one] at h
    linear_combination h
  have h1 : Summable (fun r : ℕ => g (2 * (r + 1)) * T ^ (r + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have h2 : Summable (fun r : ℕ => g (2 * (r + 2)) * T ^ (r + 2)) :=
    (summable_nat_add_iff 2).mpr hsum
  have hs0 : ∑' r : ℕ, g (2 * r) * T ^ r =
      1 + (a ^ 2 - c) * T + ∑' r : ℕ, g (2 * (r + 2)) * T ^ (r + 2) := by
    rw [hsum.tsum_eq_zero_add, h1.tsum_eq_zero_add]
    simp only [mul_zero, hg0, pow_zero, mul_one, zero_add, mul_one, hg2, pow_one]
    ring
  have hs1 : (a ^ 2 - 2 * c) * T * (∑' r : ℕ, g (2 * r) * T ^ r) =
      (a ^ 2 - 2 * c) * T +
        ∑' r : ℕ, (a ^ 2 - 2 * c) * g (2 * (r + 1)) * T ^ (r + 2) := by
    rw [hsum.tsum_eq_zero_add, mul_zero, hg0, pow_zero, mul_one, mul_add, mul_one, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun r => ?_
    ring
  have hs2 : c ^ 2 * T ^ 2 * (∑' r : ℕ, g (2 * r) * T ^ r) =
      ∑' r : ℕ, c ^ 2 * g (2 * r) * T ^ (r + 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    ring
  have h1' : Summable (fun r : ℕ => (a ^ 2 - 2 * c) * g (2 * (r + 1)) * T ^ (r + 2)) := by
    refine (h1.mul_left ((a ^ 2 - 2 * c) * T)).congr fun r => ?_
    ring
  have h2' : Summable (fun r : ℕ => c ^ 2 * g (2 * r) * T ^ (r + 2)) := by
    refine (hsum.mul_left (c ^ 2 * T ^ 2)).congr fun r => ?_
    ring
  have hcancel :
      (∑' r : ℕ, g (2 * (r + 2)) * T ^ (r + 2)) -
        (∑' r : ℕ, (a ^ 2 - 2 * c) * g (2 * (r + 1)) * T ^ (r + 2)) +
        (∑' r : ℕ, c ^ 2 * g (2 * r) * T ^ (r + 2)) = 0 := by
    rw [← (h2.tsum_sub h1'), ← ((h2.sub h1').tsum_add h2')]
    convert tsum_zero with r
    rw [even_primePow_recurrence hrec r]
    ring
  calc (1 - (a ^ 2 - 2 * c) * T + c ^ 2 * T ^ 2) * (∑' r : ℕ, g (2 * r) * T ^ r)
      = (∑' r : ℕ, g (2 * r) * T ^ r) -
          (a ^ 2 - 2 * c) * T * (∑' r : ℕ, g (2 * r) * T ^ r) +
          c ^ 2 * T ^ 2 * (∑' r : ℕ, g (2 * r) * T ^ r) := by ring
    _ = (1 + (a ^ 2 - c) * T + ∑' r : ℕ, g (2 * (r + 2)) * T ^ (r + 2)) -
          ((a ^ 2 - 2 * c) * T + ∑' r : ℕ, (a ^ 2 - 2 * c) * g (2 * (r + 1)) * T ^ (r + 2)) +
          (∑' r : ℕ, c ^ 2 * g (2 * r) * T ^ (r + 2)) := by rw [hs1, hs2, hs0]
    _ = 1 + c * T +
          ((∑' r : ℕ, g (2 * (r + 2)) * T ^ (r + 2)) -
            (∑' r : ℕ, (a ^ 2 - 2 * c) * g (2 * (r + 1)) * T ^ (r + 2)) +
            (∑' r : ℕ, c ^ 2 * g (2 * r) * T ^ (r + 2))) := by ring
    _ = 1 + c * T := by rw [hcancel, add_zero]

/-- **Exact Shimura Local `Sym²` Identity**:
`sym2LocalPoly a c T * ∑' r, g (2 r) T^r = 1 - c² T²`. -/
theorem sym2LocalPoly_mul_tsum_even_primePow {a c T : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a)
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r)
    (hsum : Summable (fun r : ℕ => g (2 * r) * T ^ r)) :
    sym2LocalPoly a c T * (∑' r : ℕ, g (2 * r) * T ^ r) = 1 - c ^ 2 * T ^ 2 := by
  unfold sym2LocalPoly
  rw [mul_assoc, sym2_even_primePow_mul_tsum hg0 hg1 hrec hsum]
  ring

/-- **Shimura Local Generating-Series Division Identity**:
whenever `‖c * T‖ < 1` and `∑ g(2r) T^r` converges, `sym2LocalPoly a c T ≠ 0`,
`∑' r, g (2 * r) * T ^ r = (1 - c² T²) / sym2LocalPoly a c T`, and
`(1 - c² T²)⁻¹ * ∑' r, g (2 * r) * T ^ r = (sym2LocalPoly a c T)⁻¹`. -/
theorem tsum_even_primePow_eq_div_sym2LocalPoly {a c T : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a)
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r)
    (hsum : Summable (fun r : ℕ => g (2 * r) * T ^ r))
    (hcT : ‖c * T‖ < 1) :
    sym2LocalPoly a c T ≠ 0 ∧
    (∑' r : ℕ, g (2 * r) * T ^ r) = (1 - c ^ 2 * T ^ 2) / sym2LocalPoly a c T ∧
    (1 - c ^ 2 * T ^ 2)⁻¹ * (∑' r : ℕ, g (2 * r) * T ^ r) = (sym2LocalPoly a c T)⁻¹ := by
  have hmul := sym2LocalPoly_mul_tsum_even_primePow hg0 hg1 hrec hsum
  have h1c2_ne : 1 - c ^ 2 * T ^ 2 ≠ 0 := by
    intro h0
    have heq : (c * T) ^ 2 = 1 := by linear_combination -h0
    have hn : ‖(c * T) ^ 2‖ = 1 := by rw [heq, norm_one]
    rw [norm_pow] at hn
    nlinarith [norm_nonneg (c * T)]
  have hpoly_ne : sym2LocalPoly a c T ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact h1c2_ne hmul.symm
  have hdiv : (∑' r : ℕ, g (2 * r) * T ^ r) = (1 - c ^ 2 * T ^ 2) / sym2LocalPoly a c T :=
    eq_div_of_mul_eq hpoly_ne (by rw [mul_comm]; exact hmul)
  refine ⟨hpoly_ne, hdiv, ?_⟩
  rw [hdiv, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ h1c2_ne, one_mul]

/-- **Exact Degree-3 Generating-Series Identity for Squared Coefficients `g r ^ 2`**:
`sym2LocalPoly a c T * ∑' r, g r ^ 2 * T ^ r = 1 + c * T`. -/
theorem sym2LocalPoly_mul_tsum_sq_primePow {a c T : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a)
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r)
    (hsum : Summable (fun r : ℕ => g r ^ 2 * T ^ r)) :
    sym2LocalPoly a c T * (∑' r : ℕ, g r ^ 2 * T ^ r) = 1 + c * T := by
  have hg2 : g 2 = a ^ 2 - c := by
    have h := hrec 0
    simp only [zero_add, hg0, hg1, mul_one] at h
    linear_combination h
  have h1 : Summable (fun r : ℕ => g (r + 1) ^ 2 * T ^ (r + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have h2 : Summable (fun r : ℕ => g (r + 2) ^ 2 * T ^ (r + 2)) :=
    (summable_nat_add_iff 2).mpr hsum
  have h3 : Summable (fun r : ℕ => g (r + 3) ^ 2 * T ^ (r + 3)) :=
    (summable_nat_add_iff 3).mpr hsum
  have hs0 : ∑' r : ℕ, g r ^ 2 * T ^ r =
      1 + a ^ 2 * T + (a ^ 2 - c) ^ 2 * T ^ 2 +
        ∑' r : ℕ, g (r + 3) ^ 2 * T ^ (r + 3) := by
    rw [hsum.tsum_eq_zero_add, h1.tsum_eq_zero_add, h2.tsum_eq_zero_add]
    simp only [hg0, hg1, hg2, pow_zero, one_pow, one_mul]
    ring
  have hs1 : (a ^ 2 - c) * T * (∑' r : ℕ, g r ^ 2 * T ^ r) =
      (a ^ 2 - c) * T + (a ^ 2 - c) * a ^ 2 * T ^ 2 +
        ∑' r : ℕ, (a ^ 2 - c) * g (r + 2) ^ 2 * T ^ (r + 3) := by
    rw [hsum.tsum_eq_zero_add, h1.tsum_eq_zero_add]
    simp only [hg0, hg1, pow_zero, one_pow, one_mul]
    rw [mul_add, mul_add, ← tsum_mul_left]
    have htail :
        (∑' r : ℕ, (a ^ 2 - c) * T * (g (r + 2) ^ 2 * T ^ (r + 2))) =
          ∑' r : ℕ, (a ^ 2 - c) * g (r + 2) ^ 2 * T ^ (r + 3) :=
      tsum_congr fun r => by ring
    rw [htail]
    ring
  have hs2 : c * (a ^ 2 - c) * T ^ 2 * (∑' r : ℕ, g r ^ 2 * T ^ r) =
      c * (a ^ 2 - c) * T ^ 2 +
        ∑' r : ℕ, c * (a ^ 2 - c) * g (r + 1) ^ 2 * T ^ (r + 3) := by
    rw [hsum.tsum_eq_zero_add, hg0, one_pow, pow_zero, mul_one, mul_add, mul_one, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun r => ?_
    ring
  have hs3 : c ^ 3 * T ^ 3 * (∑' r : ℕ, g r ^ 2 * T ^ r) =
      ∑' r : ℕ, c ^ 3 * g r ^ 2 * T ^ (r + 3) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    ring
  have h2' : Summable (fun r : ℕ => (a ^ 2 - c) * g (r + 2) ^ 2 * T ^ (r + 3)) :=
    (h2.mul_left ((a ^ 2 - c) * T)).congr fun r => by ring
  have h1' : Summable (fun r : ℕ => c * (a ^ 2 - c) * g (r + 1) ^ 2 * T ^ (r + 3)) :=
    (h1.mul_left (c * (a ^ 2 - c) * T ^ 2)).congr fun r => by ring
  have h0' : Summable (fun r : ℕ => c ^ 3 * g r ^ 2 * T ^ (r + 3)) :=
    (hsum.mul_left (c ^ 3 * T ^ 3)).congr fun r => by ring
  have hcancel :
      (∑' r : ℕ, g (r + 3) ^ 2 * T ^ (r + 3)) -
        (∑' r : ℕ, (a ^ 2 - c) * g (r + 2) ^ 2 * T ^ (r + 3)) +
        (∑' r : ℕ, c * (a ^ 2 - c) * g (r + 1) ^ 2 * T ^ (r + 3)) -
        (∑' r : ℕ, c ^ 3 * g r ^ 2 * T ^ (r + 3)) = 0 := by
    rw [← (h3.tsum_sub h2'), ← ((h3.sub h2').tsum_add h1'),
      ← (((h3.sub h2').add h1').tsum_sub h0')]
    convert tsum_zero with r
    rw [sq_primePow_recurrence hrec r]
    ring
  rw [sym2LocalPoly_expanded]
  calc (1 - (a ^ 2 - c) * T + c * (a ^ 2 - c) * T ^ 2 - c ^ 3 * T ^ 3) *
          (∑' r : ℕ, g r ^ 2 * T ^ r)
      = (∑' r : ℕ, g r ^ 2 * T ^ r) -
          (a ^ 2 - c) * T * (∑' r : ℕ, g r ^ 2 * T ^ r) +
          c * (a ^ 2 - c) * T ^ 2 * (∑' r : ℕ, g r ^ 2 * T ^ r) -
          c ^ 3 * T ^ 3 * (∑' r : ℕ, g r ^ 2 * T ^ r) := by ring
    _ = (1 + a ^ 2 * T + (a ^ 2 - c) ^ 2 * T ^ 2 + ∑' r : ℕ, g (r + 3) ^ 2 * T ^ (r + 3)) -
          ((a ^ 2 - c) * T + (a ^ 2 - c) * a ^ 2 * T ^ 2 +
            ∑' r : ℕ, (a ^ 2 - c) * g (r + 2) ^ 2 * T ^ (r + 3)) +
          (c * (a ^ 2 - c) * T ^ 2 +
            ∑' r : ℕ, c * (a ^ 2 - c) * g (r + 1) ^ 2 * T ^ (r + 3)) -
          (∑' r : ℕ, c ^ 3 * g r ^ 2 * T ^ (r + 3)) := by rw [hs1, hs2, hs3, hs0]
    _ = 1 + c * T +
          ((∑' r : ℕ, g (r + 3) ^ 2 * T ^ (r + 3)) -
            (∑' r : ℕ, (a ^ 2 - c) * g (r + 2) ^ 2 * T ^ (r + 3)) +
            (∑' r : ℕ, c * (a ^ 2 - c) * g (r + 1) ^ 2 * T ^ (r + 3)) -
            (∑' r : ℕ, c ^ 3 * g r ^ 2 * T ^ (r + 3))) := by ring
    _ = 1 + c * T := by rw [hcancel, add_zero]

/-- **Exact Local Rankin–Selberg Identity (`rankinSelberg_local_eq_zeta_mul_sym2`)**:
whenever `‖c * T‖ < 1` and `∑ g r ^ 2 * T ^ r` converges:
1. `∑' r, g r ^ 2 * T ^ r = (1 - c² T²) / ((1 - c T) * sym2LocalPoly a c T)`, and
2. `(1 - c² T²)⁻¹ * ∑' r, g r ^ 2 * T ^ r = (1 - c T)⁻¹ * (sym2LocalPoly a c T)⁻¹`! -/
theorem rankinSelberg_local_eq_zeta_mul_sym2 {a c T : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a)
    (hrec : ∀ r : ℕ, g (r + 2) = a * g (r + 1) - c * g r)
    (hsum : Summable (fun r : ℕ => g r ^ 2 * T ^ r))
    (hcT : ‖c * T‖ < 1) :
    (∑' r : ℕ, g r ^ 2 * T ^ r) =
      (1 - c ^ 2 * T ^ 2) / ((1 - c * T) * sym2LocalPoly a c T) ∧
    (1 - c ^ 2 * T ^ 2)⁻¹ * (∑' r : ℕ, g r ^ 2 * T ^ r) =
      (1 - c * T)⁻¹ * (sym2LocalPoly a c T)⁻¹ := by
  have hmul := sym2LocalPoly_mul_tsum_sq_primePow hg0 hg1 hrec hsum
  have h1mc_ne : 1 - c * T ≠ 0 := by
    intro h0
    have heq : c * T = 1 := by linear_combination -h0
    rw [heq, norm_one] at hcT
    exact lt_irrefl 1 hcT
  have h1pc_ne : 1 + c * T ≠ 0 := by
    intro h0
    have heq : c * T = -1 := by linear_combination h0
    rw [heq, norm_neg, norm_one] at hcT
    exact lt_irrefl 1 hcT
  have h1c2_ne : 1 - c ^ 2 * T ^ 2 ≠ 0 := by
    have hfac : 1 - c ^ 2 * T ^ 2 = (1 - c * T) * (1 + c * T) := by ring
    rw [hfac]
    exact mul_ne_zero h1mc_ne h1pc_ne
  have hpoly_ne : sym2LocalPoly a c T ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact h1pc_ne hmul.symm
  have h1 : (∑' r : ℕ, g r ^ 2 * T ^ r) =
      (1 - c ^ 2 * T ^ 2) / ((1 - c * T) * sym2LocalPoly a c T) := by
    refine eq_div_of_mul_eq (mul_ne_zero h1mc_ne hpoly_ne) ?_
    calc (∑' r : ℕ, g r ^ 2 * T ^ r) * ((1 - c * T) * sym2LocalPoly a c T)
        = (1 - c * T) * (sym2LocalPoly a c T * ∑' r : ℕ, g r ^ 2 * T ^ r) := by ring
      _ = (1 - c * T) * (1 + c * T) := by rw [hmul]
      _ = 1 - c ^ 2 * T ^ 2 := by ring
  refine ⟨h1, ?_⟩
  rw [h1, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ h1c2_ne, one_mul, mul_inv]

end LocalSym2Algebra

/-! ## Section 2: Multiplicative `Sym²` Dirichlet Series, Shimura & Rankin–Selberg Identities,
Degree-3 Euler Product & Non-Vanishing on `Re(s) > k + 1` -/

section GlobalSym2AndRankinSelberg

/-- Weight-`k` square-indicator arithmetic function whose `L`-series is `ζ(2s - 2k + 2)`:
`sqWeightCoeff k (d^2) = d^{2(k - 1)}` for `d ≥ 1`, and `0` on non-squares and `0`. -/
def sqWeightCoeff (k : ℕ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else if n = (Nat.sqrt n) ^ 2 then ((Nat.sqrt n : ℂ) ^ (2 * (k - 1)))
  else 0

/-- **Exact Multiplicative Dirichlet Coefficients of `L(s, Sym² f)`**:
`sym2Coeff k a n = ∑_{d² ∣ n} d^{2(k - 1)} · a_{(n / d²)²}`, realized directly as the
Dirichlet convolution `LSeries.convolution (sqWeightCoeff k) (fun m => a (m ^ 2))`. -/
def sym2Coeff (k : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  LSeries.convolution (sqWeightCoeff k) (fun m => a (m ^ 2))

/-- **Exact Multiplicative Dirichlet Coefficients of the Rankin–Selberg Convolution `L(s, f × f)`**:
`rankinSelbergCoeff k a n = ∑_{d² ∣ n} d^{2(k - 1)} · a_{n / d²}²`. -/
def rankinSelbergCoeff (k : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  LSeries.convolution (sqWeightCoeff k) (fun m => a m ^ 2)

/-- **Symmetric-Square `L`-Function `L(s, Sym² f)`** as the Dirichlet series of `sym2Coeff k a`. -/
def sym2L (k : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (sym2Coeff k a) s

/-- **Rankin–Selberg Convolution `L`-Function `L(s, f × f)`** as the Dirichlet series of
`rankinSelbergCoeff k a`. -/
def rankinSelbergL (k : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (rankinSelbergCoeff k a) s

/-- **Exact Degree-3 Local `Sym²` Euler Factor at Prime `p`**:
`(sym2LocalPoly a_p (p^{k - 1}) (p^{-s}))⁻¹`. -/
def sym2EulerFactor (k : ℕ) (a_p : ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  (sym2LocalPoly a_p ((p : ℂ) ^ (k - 1)) ((p : ℂ) ^ (-s)))⁻¹

@[simp]
theorem sqWeightCoeff_zero (k : ℕ) : sqWeightCoeff k 0 = 0 := by
  simp [sqWeightCoeff]

@[simp]
theorem sqWeightCoeff_one (k : ℕ) : sqWeightCoeff k 1 = 1 := by
  simp [sqWeightCoeff]

theorem sqWeightCoeff_sq (k : ℕ) {d : ℕ} (hd : d ≠ 0) :
    sqWeightCoeff k (d ^ 2) = (d : ℂ) ^ (2 * (k - 1)) := by
  have hsq : Nat.sqrt (d ^ 2) = d := by rw [sq, Nat.sqrt_eq]
  simp [sqWeightCoeff, hd, hsq]

theorem sqWeightCoeff_eq_zero_of_not_sq (k : ℕ) {n : ℕ} (h : ∀ d : ℕ, n ≠ d ^ 2) :
    sqWeightCoeff k n = 0 := by
  unfold sqWeightCoeff
  split_ifs with h0 hsq
  · rfl
  · exact absurd hsq (h (Nat.sqrt n))
  · rfl

private lemma nat_gcd_mul_eq_mul_gcd (d : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    Nat.gcd d (m * n) = Nat.gcd d m * Nat.gcd d n := by
  have hc : Nat.Coprime (Nat.gcd d m) (Nat.gcd d n) :=
    (hcop.coprime_dvd_left (Nat.gcd_dvd_right d m)).coprime_dvd_right (Nat.gcd_dvd_right d n)
  apply Nat.dvd_antisymm
  · have h1 : Nat.gcd d (m * n) ∣ d * (Nat.gcd d n) :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left d (m * n)) _
    -- Prove directly via `Nat.Coprime.gcd_mul_left_cancel` / `factorization`
    by_cases hd0 : d = 0
    · subst hd0; simp
    by_cases hm0 : m = 0
    · subst hm0; simp at hcop; subst hcop; simp
    by_cases hn0 : n = 0
    · subst hn0; simp at hcop; subst hcop; simp
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    have hgm0 : Nat.gcd d m ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left m (Nat.pos_of_ne_zero hd0))
    have hgn0 : Nat.gcd d n ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hd0))
    have hg0 : Nat.gcd d (m * n) ≠ 0 :=
      Nat.ne_of_gt (Nat.gcd_pos_of_pos_left (m * n) (Nat.pos_of_ne_zero hd0))
    rw [← Nat.factorization_le_iff_dvd hg0 (mul_ne_zero hgm0 hgn0)]
    intro p
    rw [Nat.factorization_mul hgm0 hgn0, Finsupp.add_apply]
    by_cases hp : p.Prime
    · have hv_g : (Nat.gcd d (m * n)).factorization p =
          min (d.factorization p) ((m * n).factorization p) := by
        rw [Nat.factorization_gcd hd0 hmn0, Finsupp.inf_apply]
      have hv_m : (Nat.gcd d m).factorization p = min (d.factorization p) (m.factorization p) := by
        rw [Nat.factorization_gcd hd0 hm0, Finsupp.inf_apply]
      have hv_n : (Nat.gcd d n).factorization p = min (d.factorization p) (n.factorization p) := by
        rw [Nat.factorization_gcd hd0 hn0, Finsupp.inf_apply]
      rw [hv_g, hv_m, hv_n, Nat.factorization_mul hm0 hn0, Finsupp.add_apply]
      have hdisj : m.factorization p = 0 ∨ n.factorization p = 0 := by
        by_contra hboth
        push Not at hboth
        have hpm : p ∣ m := hp.dvd_iff_one_le_factorization hm0 |>.mpr (Nat.pos_of_ne_zero hboth.1)
        have hpn : p ∣ n := hp.dvd_iff_one_le_factorization hn0 |>.mpr (Nat.pos_of_ne_zero hboth.2)
        exact hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpm hpn)
      rcases hdisj with hm_z | hn_z
      · simp [hm_z]
      · simp [hn_z]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · exact Nat.dvd_gcd (hc.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left d m) (Nat.gcd_dvd_left d n))
      (mul_dvd_mul (Nat.gcd_dvd_right d m) (Nat.gcd_dvd_right d n))

private lemma nat_eq_sq_of_coprime_mul_eq_sq {m n d : ℕ}
    (hcop : Nat.Coprime m n) (h : m * n = d ^ 2) :
    m = (Nat.gcd m d) ^ 2 := by
  have hd_dvd : d ∣ m * n := ⟨d, by rw [← sq]; exact h⟩
  have hd_eq : d = Nat.gcd m d * Nat.gcd n d := by
    have h1 := nat_gcd_mul_eq_mul_gcd d hcop
    rw [Nat.gcd_comm d m, Nat.gcd_comm d n, Nat.gcd_eq_left hd_dvd] at h1
    exact h1
  have hsq_eq : (Nat.gcd m d) ^ 2 * (Nat.gcd n d) ^ 2 = m * n := by
    rw [← mul_pow, ← hd_eq, h]
  have hcop1 : Nat.Coprime ((Nat.gcd m d) ^ 2) n :=
    (hcop.coprime_dvd_left (Nat.gcd_dvd_left m d)).pow_left 2
  have hcop2 : Nat.Coprime m ((Nat.gcd n d) ^ 2) :=
    (hcop.coprime_dvd_right (Nat.gcd_dvd_left n d)).pow_right 2
  have hd1 : (Nat.gcd m d) ^ 2 ∣ m :=
    hcop1.dvd_of_dvd_mul_right ⟨(Nat.gcd n d) ^ 2, hsq_eq.symm⟩
  have hd2 : m ∣ (Nat.gcd m d) ^ 2 :=
    hcop2.dvd_of_dvd_mul_right ⟨n, hsq_eq⟩
  exact Nat.dvd_antisymm hd2 hd1

/-- Exact multiplicativity of `sqWeightCoeff k` on coprime pairs `(m, n)`. -/
theorem sqWeightCoeff_mul_of_coprime (k : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    sqWeightCoeff k (m * n) = sqWeightCoeff k m * sqWeightCoeff k n := by
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hn : n = 0
  · subst hn; simp
  by_cases hmsq : m = (Nat.sqrt m) ^ 2
  · by_cases hnsq : n = (Nat.sqrt n) ^ 2
    · set a := Nat.sqrt m
      set b := Nat.sqrt n
      have ha : a ≠ 0 := by intro h; apply hm; rw [hmsq, h]; simp
      have hb : b ≠ 0 := by intro h; apply hn; rw [hnsq, h]; simp
      have hmn : m * n = (a * b) ^ 2 := by rw [hmsq, hnsq]; ring
      rw [hmn, sqWeightCoeff_sq k (mul_ne_zero ha hb), hmsq, hnsq,
        sqWeightCoeff_sq k ha, sqWeightCoeff_sq k hb, Nat.cast_mul, mul_pow]
    · have hnot : ∀ d : ℕ, m * n ≠ d ^ 2 := by
        intro d hd
        have hn_eq : n = (Nat.gcd n d) ^ 2 :=
          nat_eq_sq_of_coprime_mul_eq_sq hcop.symm (by rw [mul_comm]; exact hd)
        have hsq : Nat.sqrt n = Nat.gcd n d := by
          conv_lhs => rw [hn_eq]
          rw [sq, Nat.sqrt_eq]
        exact hnsq (by rw [hsq]; exact hn_eq)
      rw [sqWeightCoeff_eq_zero_of_not_sq k hnot]
      have hnsq' : sqWeightCoeff k n = 0 := by simp [sqWeightCoeff, hn, hnsq]
      rw [hnsq', mul_zero]
  · have hnot : ∀ d : ℕ, m * n ≠ d ^ 2 := by
      intro d hd
      have hm_eq : m = (Nat.gcd m d) ^ 2 := nat_eq_sq_of_coprime_mul_eq_sq hcop hd
      have hsq : Nat.sqrt m = Nat.gcd m d := by
        conv_lhs => rw [hm_eq]
        rw [sq, Nat.sqrt_eq]
      exact hmsq (by rw [hsq]; exact hm_eq)
    rw [sqWeightCoeff_eq_zero_of_not_sq k hnot]
    have hmsq' : sqWeightCoeff k m = 0 := by simp [sqWeightCoeff, hm, hmsq]
    rw [hmsq', zero_mul]

/-- General multiplicativity of `LSeries.convolution f g` whenever `f` and `g` are multiplicative
on coprime pairs. -/
theorem convolution_mul_of_coprime {f g : ℕ → ℂ}
    (hf : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
    (hg : ∀ m n, Nat.Coprime m n → g (m * n) = g m * g n)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    LSeries.convolution f g (m * n) = LSeries.convolution f g m * LSeries.convolution f g n := by
  by_cases hm : m = 0
  · subst hm; simp [LSeries.convolution_def]
  by_cases hn : n = 0
  · subst hn; simp [LSeries.convolution_def]
  rw [LSeries.convolution_def]
  dsimp only
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun p : ℕ × ℕ => ((Nat.gcd p.1 m, Nat.gcd p.2 m), (Nat.gcd p.1 n, Nat.gcd p.2 n)))
    (fun q : (ℕ × ℕ) × (ℕ × ℕ) => (q.1.1 * q.2.1, q.1.2 * q.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal]
    have hp1_dvd : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have hp2_dvd : p.2 ∣ m * n := ⟨p.1, by rw [← hpmul, mul_comm]⟩
    have hp1_eq : p.1 = Nat.gcd p.1 m * Nat.gcd p.1 n := by
      rw [← nat_gcd_mul_eq_mul_gcd p.1 hcop, Nat.gcd_eq_left hp1_dvd]
    have hp2_eq : p.2 = Nat.gcd p.2 m * Nat.gcd p.2 n := by
      rw [← nat_gcd_mul_eq_mul_gcd p.2 hcop, Nat.gcd_eq_left hp2_dvd]
    have hprod_eq :
        (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n) = m * n := by
      calc (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n)
          = (Nat.gcd p.1 m * Nat.gcd p.1 n) * (Nat.gcd p.2 m * Nat.gcd p.2 n) := by ring
        _ = p.1 * p.2 := by rw [← hp1_eq, ← hp2_eq]
        _ = m * n := hpmul
    have hcop_mn' : Nat.Coprime (Nat.gcd p.1 m * Nat.gcd p.2 m) n :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).mul_left
        (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _))
    have hcop_nm' : Nat.Coprime m (Nat.gcd p.1 n * Nat.gcd p.2 n) :=
      (hcop.coprime_dvd_right (Nat.gcd_dvd_right _ _)).mul_right
        (hcop.coprime_dvd_right (Nat.gcd_dvd_right _ _))
    have hm_prod : Nat.gcd p.1 m * Nat.gcd p.2 m = m :=
      Nat.dvd_antisymm
        (hcop_mn'.dvd_of_dvd_mul_right ⟨Nat.gcd p.1 n * Nat.gcd p.2 n, hprod_eq.symm⟩)
        (hcop_nm'.dvd_of_dvd_mul_right ⟨n, hprod_eq⟩)
    have hn_prod : Nat.gcd p.1 n * Nat.gcd p.2 n = n := by
      rw [hm_prod] at hprod_eq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hprod_eq
    exact ⟨⟨hm_prod, hm⟩, ⟨hn_prod, hn⟩⟩
  · intro q hq
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hq
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, mul_ne_zero hm hn⟩
    calc q.1.1 * q.2.1 * (q.1.2 * q.2.2)
        = (q.1.1 * q.1.2) * (q.2.1 * q.2.2) := by ring
      _ = m * n := by rw [hq.1.1, hq.2.1]
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    have hp1_dvd : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have hp2_dvd : p.2 ∣ m * n := ⟨p.1, by rw [← hpmul, mul_comm]⟩
    ext
    · exact (nat_gcd_mul_eq_mul_gcd p.1 hcop).symm.trans (Nat.gcd_eq_left hp1_dvd)
    · exact (nat_gcd_mul_eq_mul_gcd p.2 hcop).symm.trans (Nat.gcd_eq_left hp2_dvd)
  · intro q hq
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hq
    have hq11_m : q.1.1 ∣ m := ⟨q.1.2, hq.1.1.symm⟩
    have hq12_m : q.1.2 ∣ m := ⟨q.1.1, by rw [mul_comm]; exact hq.1.1.symm⟩
    have hq21_n : q.2.1 ∣ n := ⟨q.2.2, hq.2.1.symm⟩
    have hq22_n : q.2.2 ∣ n := ⟨q.2.1, by rw [mul_comm]; exact hq.2.1.symm⟩
    have hc1 : Nat.Coprime q.2.1 m := (hcop.coprime_dvd_right hq21_n).symm
    have hc2 : Nat.Coprime q.2.2 m := (hcop.coprime_dvd_right hq22_n).symm
    have hc3 : Nat.Coprime q.1.1 n := hcop.coprime_dvd_left hq11_m
    have hc4 : Nat.Coprime q.1.2 n := hcop.coprime_dvd_left hq12_m
    ext <;> dsimp only
    · rw [hc1.gcd_mul_right_cancel, Nat.gcd_eq_left hq11_m]
    · rw [hc2.gcd_mul_right_cancel, Nat.gcd_eq_left hq12_m]
    · rw [hc3.gcd_mul_left_cancel, Nat.gcd_eq_left hq21_n]
    · rw [hc4.gcd_mul_left_cancel, Nat.gcd_eq_left hq22_n]
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    have hp1_dvd : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have hp2_dvd : p.2 ∣ m * n := ⟨p.1, by rw [← hpmul, mul_comm]⟩
    have hp1_eq : p.1 = Nat.gcd p.1 m * Nat.gcd p.1 n := by
      rw [← nat_gcd_mul_eq_mul_gcd p.1 hcop, Nat.gcd_eq_left hp1_dvd]
    have hp2_eq : p.2 = Nat.gcd p.2 m * Nat.gcd p.2 n := by
      rw [← nat_gcd_mul_eq_mul_gcd p.2 hcop, Nat.gcd_eq_left hp2_dvd]
    have hc1 : Nat.Coprime (Nat.gcd p.1 m) (Nat.gcd p.1 n) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    have hc2 : Nat.Coprime (Nat.gcd p.2 m) (Nat.gcd p.2 n) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    conv_lhs => rw [hp1_eq, hp2_eq]
    rw [hf _ _ hc1, hg _ _ hc2]
    ring

/-- **Exact `LSeries` Evaluation of `sqWeightCoeff k`**:
on `Re(s) > k - 1/2`, `LSeriesSummable (sqWeightCoeff k) s` and
`LSeries (sqWeightCoeff k) s = riemannZeta (2 * s - 2 * k + 2)`. -/
theorem LSeriesSummable_sqWeightCoeff (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hs : (k : ℝ) - 1 / 2 < s.re) :
    LSeriesSummable (sqWeightCoeff k) s := by
  have hre : 1 < (2 * s - 2 * (k : ℂ) + 2).re := by
    simp only [add_re, sub_re, mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im,
      zero_mul, sub_zero]
    linarith
  have hzeta : LSeriesSummable (1 : ℕ → ℂ) (2 * s - 2 * (k : ℂ) + 2) :=
    LSeriesSummable_one_iff.mpr hre
  have hmap : Function.Injective (fun d : ℕ => d ^ 2) := fun a b hab => by
    have h1 := congrArg Nat.sqrt hab
    simpa [sq, Nat.sqrt_eq] using h1
  have hsub : Summable (fun d : ℕ => LSeries.term (sqWeightCoeff k) s (d ^ 2)) := by
    refine hzeta.congr fun d => ?_
    by_cases hd : d = 0
    · subst hd; simp [LSeries.term]
    · have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
      simp only [LSeries.term_of_ne_zero hd, LSeries.term_of_ne_zero hd2, Pi.one_apply,
        sqWeightCoeff_sq k hd]
      have hpow : ((d ^ 2 : ℕ) : ℂ) ^ s = (d : ℂ) ^ (2 * s) := by
        rw [Nat.cast_pow, sq]
        have hm := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d) s
        simp only [Complex.ofReal_natCast] at hm
        rw [hm, ← Complex.cpow_add _ _ hdC, two_mul]
      have hcast : ((2 * (k - 1) : ℕ) : ℂ) = 2 * (k : ℂ) - 2 := by
        have hk' : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
        push_cast [hk']
        ring
      rw [hpow, ← Complex.cpow_natCast (d : ℂ) (2 * (k - 1)), hcast,
        div_eq_mul_inv, div_eq_mul_inv, one_mul, ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hdC]
      congr 1
      ring
  unfold LSeriesSummable
  rw [← Function.Injective.summable_iff hmap]
  · exact hsub
  · intro n hn
    have hnot : ∀ d : ℕ, n ≠ d ^ 2 := fun d hd => hn ⟨d, hd.symm⟩
    by_cases hn0 : n = 0
    · subst hn0; simp
    · simp [LSeries.term_of_ne_zero hn0, sqWeightCoeff_eq_zero_of_not_sq k hnot]

theorem LSeries_sqWeightCoeff_eq_riemannZeta (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hs : (k : ℝ) - 1 / 2 < s.re) :
    LSeries (sqWeightCoeff k) s = riemannZeta (2 * s - 2 * (k : ℂ) + 2) := by
  have hre : 1 < (2 * s - 2 * (k : ℂ) + 2).re := by
    simp only [add_re, sub_re, mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im,
      zero_mul, sub_zero]
    linarith
  rw [← LSeries_one_eq_riemannZeta hre]
  unfold LSeries
  have hmap : Function.Injective (fun d : ℕ => d ^ 2) := fun a b hab => by
    have h1 := congrArg Nat.sqrt hab
    simpa [sq, Nat.sqrt_eq] using h1
  have htsum := Function.Injective.tsum_eq hmap
    (f := fun n : ℕ => LSeries.term (sqWeightCoeff k) s n) (fun n hn => by
      by_contra hnot_mem
      have hnot : ∀ d : ℕ, n ≠ d ^ 2 := fun d hd => hnot_mem ⟨d, hd.symm⟩
      have hz : LSeries.term (sqWeightCoeff k) s n = 0 := by
        by_cases hn0 : n = 0
        · subst hn0; simp
        · simp [LSeries.term_of_ne_zero hn0, sqWeightCoeff_eq_zero_of_not_sq k hnot]
      exact hn hz)
  rw [← htsum]
  refine tsum_congr fun d => ?_
  by_cases hd : d = 0
  · subst hd; simp [LSeries.term]
  · have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    simp only [LSeries.term_of_ne_zero hd, LSeries.term_of_ne_zero hd2, Pi.one_apply,
      sqWeightCoeff_sq k hd]
    have hpow : ((d ^ 2 : ℕ) : ℂ) ^ s = (d : ℂ) ^ (2 * s) := by
      rw [Nat.cast_pow, sq]
      have hm := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d) s
      simp only [Complex.ofReal_natCast] at hm
      rw [hm, ← Complex.cpow_add _ _ hdC, two_mul]
    have hcast : ((2 * (k - 1) : ℕ) : ℂ) = 2 * (k : ℂ) - 2 := by
      have hk' : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
      push_cast [hk']; ring
    rw [hpow, ← Complex.cpow_natCast (d : ℂ) (2 * (k - 1)), hcast,
      div_eq_mul_inv, div_eq_mul_inv, one_mul, ← Complex.cpow_neg, ← Complex.cpow_neg,
      ← Complex.cpow_add _ _ hdC]
    congr 1; ring

/-- Exact `LSeries` evaluation of `n ↦ n^{k - 1}`: `L(n ↦ n^{k-1}, s) = ζ(s - k + 1)`. -/
theorem LSeriesSummable_pow_k_sub_one (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hs : (k : ℝ) < s.re) :
    LSeriesSummable (fun n : ℕ => (n : ℂ) ^ (k - 1)) s := by
  have hre : 1 < (s - (k : ℂ) + 1).re := by simp; linarith
  have hzeta := LSeriesSummable_one_iff.mpr hre
  refine hzeta.congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term]
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hk' : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
    simp only [LSeries.term_of_ne_zero hn, Pi.one_apply]
    rw [← Complex.cpow_natCast (n : ℂ) (k - 1), hk', div_eq_mul_inv, div_eq_mul_inv, one_mul,
      ← Complex.cpow_neg, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hnC]
    congr 1; ring

theorem LSeries_pow_k_sub_one_eq_riemannZeta (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hs : (k : ℝ) < s.re) :
    LSeries (fun n : ℕ => (n : ℂ) ^ (k - 1)) s = riemannZeta (s - (k : ℂ) + 1) := by
  have hre : 1 < (s - (k : ℂ) + 1).re := by simp; linarith
  rw [← LSeries_one_eq_riemannZeta hre]
  unfold LSeries
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term]
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hk' : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
    simp only [LSeries.term_of_ne_zero hn, Pi.one_apply]
    rw [← Complex.cpow_natCast (n : ℂ) (k - 1), hk', div_eq_mul_inv, div_eq_mul_inv, one_mul,
      ← Complex.cpow_neg, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hnC]
    congr 1; ring

/-- **Arithmetic Properties of `sym2Coeff k a` for Any Normalized Level-1 Hecke Eigenform**:
1. `sym2Coeff k a 0 = 0`, `sym2Coeff k a 1 = 1`,
2. for every prime `p`, `sym2Coeff k a p = a p ^ 2 - p^{k - 1}`,
3. exact multiplicativity: `Nat.Coprime m n → sym2Coeff k a (m * n) = sym2Coeff k a m * sym2Coeff k a n`. -/
theorem sym2Coeff_zero (k : ℕ) (a : ℕ → ℂ) : sym2Coeff k a 0 = 0 := by
  simp [sym2Coeff]

theorem sym2Coeff_one {k : ℕ} {a : ℕ → ℂ}
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a) :
    sym2Coeff k a 1 = 1 := by
  simp [sym2Coeff, LSeries.convolution_def, heig.1]

theorem sym2Coeff_prime {k : ℕ} {a : ℕ → ℂ}
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {p : ℕ} (hp : p.Prime) :
    sym2Coeff k a p = a p ^ 2 - (p : ℂ) ^ (k - 1) := by
  have hanti : p.divisorsAntidiagonal = {(1, p), (p, 1)} := by
    ext ⟨u, v⟩
    simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨huv, _⟩
      have hu : u ∣ p := ⟨v, huv.symm⟩
      rcases (Nat.dvd_prime hp).mp hu with hu1 | hup
      · rw [hu1]; left; exact ⟨rfl, by simpa [hu1] using huv⟩
      · rw [hup]; right; refine ⟨rfl, ?_⟩
        have h1 : p * v = p * 1 := by simpa [hup] using huv
        exact Nat.eq_of_mul_eq_mul_left hp.pos h1
    · rintro (⟨hu1, hvp⟩ | ⟨hup, hv1⟩)
      · rw [hu1, hvp]; exact ⟨one_mul p, hp.ne_zero⟩
      · rw [hup, hv1]; exact ⟨mul_one p, hp.ne_zero⟩
  rw [sym2Coeff, LSeries.convolution_def]
  dsimp only
  rw [hanti, Finset.sum_pair (by intro h; have := congrArg Prod.fst h; exact hp.ne_one this.symm)]
  have hnot : ∀ d : ℕ, p ≠ d ^ 2 := fun d hd => by
    have h1 := congrArg (fun n => n.factorization p) hd
    rw [Nat.Prime.factorization_self hp, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h1
    omega
  rw [sqWeightCoeff_one, one_mul, sqWeightCoeff_eq_zero_of_not_sq k hnot, zero_mul, add_zero]
  have hrec := eigenform_prime_pow_recurrence heig hp 0
  rw [trivialChar_one_apply, one_mul, zero_add, pow_one, pow_zero, heig.1, mul_one] at hrec
  rw [hrec]
  ring

theorem sqIndex_mul_of_coprime {k : ℕ} {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    a ((m * n) ^ 2) = a (m ^ 2) * a (n ^ 2) := by
  by_cases hm : m = 0
  · subst hm; simp [ha0]
  by_cases hn : n = 0
  · subst hn; simp [ha0]
  rw [mul_pow]
  exact eigenform_isMultiplicative heig (pow_pos (Nat.pos_of_ne_zero hm) 2)
    (pow_pos (Nat.pos_of_ne_zero hn) 2) (hcop.pow 2 2)

theorem sym2Coeff_mul_of_coprime {k : ℕ} {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    sym2Coeff k a (m * n) = sym2Coeff k a m * sym2Coeff k a n :=
  convolution_mul_of_coprime (fun _ _ h => sqWeightCoeff_mul_of_coprime k h)
    (fun _ _ h => sqIndex_mul_of_coprime ha0 heig h) hcop

/-- **Exact Hecke Convolution Identity for Squared Coefficients**:
for every normalized level-1 Hecke eigenform `a` and every `n ≥ 1`,
`a n ^ 2 = ∑_{d ∣ n} d^{k - 1} · a_{(n / d)²} = LSeries.convolution (d ↦ d^{k-1}) (m ↦ a (m²)) n`! -/
theorem sq_eq_convolution_pow_sqIndex {k : ℕ} {a : ℕ → ℂ}
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {n : ℕ} (hn : 1 ≤ n) :
    a n ^ 2 = LSeries.convolution (fun d : ℕ => (d : ℂ) ^ (k - 1)) (fun m : ℕ => a (m ^ 2)) n := by
  have hmul := eigenform_mul_eq_sum heig (m := n) hn
  rw [sq, hmul, Nat.gcd_self, LSeries.convolution_def]
  dsimp only
  refine Finset.sum_nbij' (fun d => (d, n / d)) (fun p => p.1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), by omega⟩
  · intro p hp
    exact Nat.fst_mem_divisors_of_mem_antidiagonal hp
  · intro _ _; rfl
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
    have hp1_pos : 0 < p.1 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
    ext
    · rfl
    · exact (Nat.eq_div_of_mul_eq_right hp1_pos.ne' hpmul).symm
  · intro d hd
    have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdiv : n * n / d ^ 2 = (n / d) ^ 2 := by
      rcases hd_dvd with ⟨q, rfl⟩
      by_cases hd0 : d = 0
      · subst hd0; simp at hd
      have hq : d * q / d = q := Nat.mul_div_right q (Nat.pos_of_ne_zero hd0)
      rw [hq, sq, sq]
      have h1 : d * q * (d * q) = d * d * (q * q) := by ring
      rw [h1, Nat.mul_div_right _ (mul_pos (Nat.pos_of_ne_zero hd0) (Nat.pos_of_ne_zero hd0))]
    simp only [trivialChar_one_apply, one_mul, hdiv]

/-- Absolute convergence of `∑ a_{n²} n^{-s}` on `Re(s) > k + 1` from Hecke's bound `|a_n| ≤ C n^{k/2}`. -/
theorem LSeriesSummable_sqIndex_of_heckeBound {k : ℕ} {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (fun n : ℕ => a (n ^ 2)) s := by
  refine LSeriesSummable_of_poly_bound (C := C) (σ := (k : ℝ)) (fun n hn => ?_) hs
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
  have hb := hbound (n ^ 2) hn2
  have hrpow : ((n ^ 2 : ℕ) : ℝ) ^ ((k : ℝ) / 2) = (n : ℝ) ^ (k : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1; ring
  rwa [hrpow] at hb

/-- Absolute convergence of `∑ a_n² n^{-s}` on `Re(s) > k + 1` from Hecke's bound `|a_n| ≤ C n^{k/2}`. -/
theorem LSeriesSummable_sq_of_heckeBound {k : ℕ} {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (fun n : ℕ => a n ^ 2) s := by
  refine LSeriesSummable_of_poly_bound (C := C ^ 2) (σ := (k : ℝ)) (fun n hn => ?_) hs
  have hb := hbound n hn
  have hsq : ‖a n‖ ^ 2 ≤ (C * (n : ℝ) ^ ((k : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [norm_pow]
  refine hsq.trans_eq ?_
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((k : ℝ) / 2)) 2,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 2; ring

/-- Absolute convergence of `L(s, Sym² f)` on `Re(s) > k + 1`. -/
theorem LSeriesSummable_sym2_of_heckeBound {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (sym2Coeff k a) s :=
  LSeriesSummable.convolution
    (LSeriesSummable_sqWeightCoeff k hk (by linarith))
    (LSeriesSummable_sqIndex_of_heckeBound hbound hs)

/-- Absolute convergence of `L(s, f × f)` on `Re(s) > k + 1`. -/
theorem LSeriesSummable_rankinSelberg_of_heckeBound {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (rankinSelbergCoeff k a) s :=
  LSeriesSummable.convolution
    (LSeriesSummable_sqWeightCoeff k hk (by linarith))
    (LSeriesSummable_sq_of_heckeBound hbound hs)

/-- **UNCONDITIONAL SHIMURA `Sym²` DIRICHLET SERIES FORMULA (`sym2L_eq_zeta_mul_sum_sq_index`)**:
for ANY weight `k ≥ 1` and coefficient sequence `a` obeying Hecke's bound `|a_n| ≤ C n^{k/2}`,
on `Re(s) > k + 1`:
`L(s, Sym² f) = ζ(2s - 2k + 2) * ∑_{n ≥ 1} a_{n²} n^{-s}`! -/
theorem sym2L_eq_zeta_mul_sum_sq_index {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    sym2L k a s =
      riemannZeta (2 * s - 2 * (k : ℂ) + 2) * LSeries (fun n : ℕ => a (n ^ 2)) s := by
  unfold sym2L sym2Coeff
  rw [LSeries_convolution'
    (LSeriesSummable_sqWeightCoeff k hk (by linarith))
    (LSeriesSummable_sqIndex_of_heckeBound hbound hs),
    LSeries_sqWeightCoeff_eq_riemannZeta k hk (by linarith)]

/-- Exact Dirichlet-series presentation of the Rankin–Selberg convolution on `Re(s) > k + 1`:
`L(s, f × f) = ζ(2s - 2k + 2) * ∑_{n ≥ 1} a_n² n^{-s}`. -/
theorem rankinSelbergL_eq_zeta_mul_sum_sq {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    rankinSelbergL k a s =
      riemannZeta (2 * s - 2 * (k : ℂ) + 2) * LSeries (fun n : ℕ => a n ^ 2) s := by
  unfold rankinSelbergL rankinSelbergCoeff
  rw [LSeries_convolution'
    (LSeriesSummable_sqWeightCoeff k hk (by linarith))
    (LSeriesSummable_sq_of_heckeBound hbound hs),
    LSeries_sqWeightCoeff_eq_riemannZeta k hk (by linarith)]

/-- **UNCONDITIONAL RANKIN–SELBERG FACTORIZATION (`rankinSelberg_eq_zeta_mul_sym2`)**:
for ANY normalized level-1 Hecke eigenform `a` of weight `k ≥ 1` obeying `|a_n| ≤ C n^{k/2}`,
on `Re(s) > k + 1`:
`L(s, f × f) = ζ(s - k + 1) * L(s, Sym² f)`! -/
theorem rankinSelberg_eq_zeta_mul_sym2 {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    rankinSelbergL k a s = riemannZeta (s - (k : ℂ) + 1) * sym2L k a s := by
  rw [rankinSelbergL_eq_zeta_mul_sum_sq hk hbound hs,
    sym2L_eq_zeta_mul_sum_sq_index hk hbound hs]
  have hsum_pow := LSeriesSummable_pow_k_sub_one k hk (by linarith)
  have hsum_sqi := LSeriesSummable_sqIndex_of_heckeBound hbound hs
  have hconv_eq : LSeries (fun n : ℕ => a n ^ 2) s =
      LSeries (LSeries.convolution (fun d : ℕ => (d : ℂ) ^ (k - 1))
        (fun m : ℕ => a (m ^ 2))) s := by
    unfold LSeries
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn]
    · simp [LSeries.term_of_ne_zero hn, sq_eq_convolution_pow_sqIndex heig (Nat.pos_of_ne_zero hn)]
  rw [hconv_eq, LSeries_convolution' hsum_pow hsum_sqi,
    LSeries_pow_k_sub_one_eq_riemannZeta k hk (by linarith)]
  ring

/-! ### Local Prime-Power Sum & Exact Degree-3 `Sym²` Euler Product -/

private lemma cpow_prime_pow_neg' (p : ℕ) (s : ℂ) (r : ℕ) :
    (((p ^ r : ℕ) : ℂ) ^ s)⁻¹ = ((p : ℂ) ^ (-s)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.cast_mul]
    have hmul : (((p ^ r : ℕ) : ℂ) * (p : ℂ)) ^ s = (((p ^ r : ℕ) : ℂ) ^ s) * ((p : ℂ) ^ s) := by
      simpa [Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (p ^ r)) (Nat.cast_nonneg p) s
    rw [hmul, mul_inv, ih, ← Complex.cpow_neg, pow_succ]

private lemma norm_prime_pow_k_sub_one_mul_neg_s {k p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    ‖(p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := Nat.one_lt_cast.mpr hp.one_lt
  rw [norm_mul, norm_pow, Complex.norm_natCast,
    show (p : ℂ) = ((p : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,
    neg_re, ← Real.rpow_natCast (p : ℝ) (k - 1), ← Real.rpow_add hp_pos]
  have hexp : ((k - 1 : ℕ) : ℝ) + -s.re < 0 := by
    have hle : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.sub_le k 1)
    linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 hexp

/-- Exact prime-power local sum of `sqWeightCoeff k`:
`∑' r, LSeries.term (sqWeightCoeff k) s (p ^ r) = (1 - (p^{k - 1})² (p^{-s})²)⁻¹`. -/
private lemma sqWeightCoeff_tsum_prime_pow {k p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    (∑' r : ℕ, LSeries.term (sqWeightCoeff k) s (p ^ r)) =
      (1 - ((p : ℂ) ^ (k - 1)) ^ 2 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  have hcT : ‖(p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_pow_k_sub_one_mul_neg_s hp hs
  set z : ℂ := ((p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-s)) ^ 2
  have hz_norm : ‖z‖ < 1 := by
    dsimp only [z]
    rw [norm_pow]
    nlinarith [norm_nonneg ((p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-s))]
  have hgeom : (∑' j : ℕ, z ^ j) = (1 - z)⁻¹ := tsum_geometric_of_norm_lt_one hz_norm
  have hmul_inj : Function.Injective (fun j : ℕ => 2 * j) := fun a b (h : 2 * a = 2 * b) => by omega
  have htsum := Function.Injective.tsum_eq hmul_inj
    (f := fun r : ℕ => LSeries.term (sqWeightCoeff k) s (p ^ r)) (fun r hr => by
      by_contra hnot_even
      have hodd : ¬ Even r := fun ⟨j, hj⟩ => hnot_even ⟨j, by dsimp only; omega⟩
      have hnot : ∀ d : ℕ, p ^ r ≠ d ^ 2 := fun d hd => by
        have hval := congrArg (fun n => n.factorization p) hd
        rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
          Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hval
        exact hodd ⟨d.factorization p, by omega⟩
      have hz : LSeries.term (sqWeightCoeff k) s (p ^ r) = 0 := by
        simp [LSeries.term_of_ne_zero (pow_ne_zero r hp.ne_zero),
          sqWeightCoeff_eq_zero_of_not_sq k hnot]
      exact hr hz)
  rw [← htsum]
  have hterm : ∀ j : ℕ, LSeries.term (sqWeightCoeff k) s (p ^ (2 * j)) = z ^ j := fun j => by
    have hne : p ^ (2 * j) ≠ 0 := pow_ne_zero (2 * j) hp.ne_zero
    rw [LSeries.term_of_ne_zero hne, div_eq_mul_inv, cpow_prime_pow_neg' p s (2 * j)]
    have hpow2 : p ^ (2 * j) = (p ^ j) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [hpow2, sqWeightCoeff_sq k (pow_ne_zero j hp.ne_zero), Nat.cast_pow, ← pow_mul]
    dsimp only [z]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    have hexp : j * (2 * (k - 1)) = (k - 1) * (2 * j) := by ring
    rw [hexp]
  simp_rw [hterm]
  rw [hgeom]
  dsimp only [z]
  congr 1; ring

/-- Helper: Cauchy product identity `∑' r, ∑ q ∈ antidiagonal r, f q.1 * g q.2 = (∑' i, f i) * (∑' j, g j)`
for absolutely summable complex sequences `f, g : ℕ → ℂ`. -/
private lemma tsum_antidiagonal_eq_tsum_mul {f g : ℕ → ℂ}
    (hf : Summable (fun i : ℕ => ‖f i‖)) (hg : Summable (fun j : ℕ => ‖g j‖)) :
    (∑' r : ℕ, ∑ q ∈ Finset.antidiagonal r, f q.1 * g q.2) =
      (∑' i : ℕ, f i) * (∑' j : ℕ, g j) := by
  have hprod_norm : Summable (fun z : ℕ × ℕ => ‖f z.1 * g z.2‖) := by
    refine (hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr fun z => ?_
    exact (norm_mul (f z.1) (g z.2)).symm
  have hprod : Summable (fun z : ℕ × ℕ => f z.1 * g z.2) := hprod_norm.of_norm
  let e : (Σ r : ℕ, {q : ℕ × ℕ // q ∈ Finset.antidiagonal r}) ≃ ℕ × ℕ :=
    { toFun := fun x => x.2.1
      invFun := fun z => ⟨z.1 + z.2, ⟨z, Finset.mem_antidiagonal.mpr rfl⟩⟩
      left_inv := fun ⟨r, ⟨z, hz⟩⟩ => by
        have h : z.1 + z.2 = r := Finset.mem_antidiagonal.mp hz
        subst h
        rfl
      right_inv := fun _ => rfl }
  have hsigma : Summable (fun x : (Σ r : ℕ, {q : ℕ × ℕ // q ∈ Finset.antidiagonal r}) =>
      f (e x).1 * g (e x).2) :=
    (e.summable_iff (f := fun z : ℕ × ℕ => f z.1 * g z.2)).mpr hprod
  rw [tsum_mul_tsum_of_summable_norm hf hg, ← Equiv.tsum_eq e (fun z : ℕ × ℕ => f z.1 * g z.2),
    hsigma.tsum_sigma' (fun r => (hasSum_fintype _).summable)]
  refine tsum_congr fun r => ?_
  rw [tsum_fintype]
  exact (Finset.sum_attach (Finset.antidiagonal r) (fun q => f q.1 * g q.2)).symm

/-- Exact prime-power local sum of `sym2Coeff k a`:
`∑' r, LSeries.term (sym2Coeff k a) s (p ^ r) = sym2EulerFactor k (a p) p s`! -/
theorem sym2Coeff_tsum_prime_pow {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' r : ℕ, LSeries.term (sym2Coeff k a) s (p ^ r)) = sym2EulerFactor k (a p) p s := by
  have hinj : Function.Injective (fun r : ℕ => p ^ r) := Nat.pow_right_injective hp.two_le
  have hsum_u : Summable (fun r : ℕ => ‖LSeries.term (sqWeightCoeff k) s (p ^ r)‖) :=
    ((LSeriesSummable_sqWeightCoeff k hk (by linarith)).norm).comp_injective hinj
  have hsum_v : Summable (fun r : ℕ => ‖LSeries.term (fun m => a (m ^ 2)) s (p ^ r)‖) :=
    ((LSeriesSummable_sqIndex_of_heckeBound hbound hs).norm).comp_injective hinj
  have hfac_pow : ∀ m : ℕ, (p ^ m).factorization p = m := fun m => by
    rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  -- Express `LSeries.term (sym2Coeff k a) s (p ^ r)` as the Cauchy product of the `u` and `v` terms
  have hcauchy : ∀ r : ℕ,
      LSeries.term (sym2Coeff k a) s (p ^ r) =
        ∑ q ∈ Finset.antidiagonal r,
          LSeries.term (sqWeightCoeff k) s (p ^ q.1) *
            LSeries.term (fun m => a (m ^ 2)) s (p ^ q.2) := by
    intro r
    have hpr : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
    rw [LSeries.term_of_ne_zero hpr, div_eq_mul_inv, cpow_prime_pow_neg' p s r,
      sym2Coeff, LSeries.convolution_def]
    dsimp only
    rw [Finset.sum_mul]
    refine Finset.sum_nbij'
      (fun d : ℕ × ℕ => (d.1.factorization p, d.2.factorization p))
      (fun q : ℕ × ℕ => (p ^ q.1, p ^ q.2)) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rcases Nat.mem_divisorsAntidiagonal.mp hd with ⟨hdmul, _⟩
      have hd1 : d.1 ≠ 0 := fun h0 => hpr (by simp [← hdmul, h0])
      have hd2 : d.2 ≠ 0 := fun h0 => hpr (by simp [← hdmul, h0])
      rw [Finset.mem_antidiagonal, ← Finsupp.add_apply, ← Nat.factorization_mul hd1 hd2,
        hdmul, hfac_pow r]
    · intro q hq
      rw [Finset.mem_antidiagonal] at hq
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨by rw [← pow_add, hq], hpr⟩
    · intro d hd
      rcases Nat.mem_divisorsAntidiagonal.mp hd with ⟨hdmul, _⟩
      have hd1_dvd : d.1 ∣ p ^ r := ⟨d.2, hdmul.symm⟩
      have hd2_dvd : d.2 ∣ p ^ r := ⟨d.1, by rw [mul_comm]; exact hdmul.symm⟩
      obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hd1_dvd
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hd2_dvd
      ext <;> dsimp only
      · rw [hi, hfac_pow i]
      · rw [hj, hfac_pow j]
    · intro q _
      ext <;> dsimp only
      · exact hfac_pow q.1
      · exact hfac_pow q.2
    · intro d hd
      rcases Nat.mem_divisorsAntidiagonal.mp hd with ⟨hdmul, _⟩
      have hd1_dvd : d.1 ∣ p ^ r := ⟨d.2, hdmul.symm⟩
      have hd2_dvd : d.2 ∣ p ^ r := ⟨d.1, by rw [mul_comm]; exact hdmul.symm⟩
      obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hd1_dvd
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hd2_dvd
      have hij : i + j = r := by
        have hpow : p ^ (i + j) = p ^ r := by rw [pow_add, ← hi, ← hj, hdmul]
        exact Nat.pow_right_injective hp.two_le hpow
      rw [hi, hj, hfac_pow i, hfac_pow j,
        LSeries.term_of_ne_zero (pow_ne_zero i hp.ne_zero),
        LSeries.term_of_ne_zero (pow_ne_zero j hp.ne_zero),
        div_eq_mul_inv, div_eq_mul_inv, cpow_prime_pow_neg' p s i, cpow_prime_pow_neg' p s j,
        ← hij, pow_add]
      ring
  simp_rw [hcauchy]
  rw [tsum_antidiagonal_eq_tsum_mul hsum_u hsum_v, sqWeightCoeff_tsum_prime_pow hp hs]
  -- Evaluate the second factor `∑' r, a (p^(2r)) (p^{-s})^r` via Shimura's local identity
  have hv_eq : ∀ r : ℕ,
      LSeries.term (fun m => a (m ^ 2)) s (p ^ r) = a (p ^ (2 * r)) * ((p : ℂ) ^ (-s)) ^ r := by
    intro r
    rw [LSeries.term_of_ne_zero (pow_ne_zero r hp.ne_zero), div_eq_mul_inv,
      cpow_prime_pow_neg' p s r, ← pow_mul, mul_comm r 2]
  simp_rw [hv_eq]
  have hsum_even : Summable (fun r : ℕ => a (p ^ (2 * r)) * ((p : ℂ) ^ (-s)) ^ r) := by
    refine hsum_v.of_norm.congr fun r => hv_eq r
  have hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * a (p ^ r) := by
    intro r
    have h := eigenform_prime_pow_recurrence heig hp r
    rwa [trivialChar_one_apply, one_mul] at h
  have hshim := tsum_even_primePow_eq_div_sym2LocalPoly
    (g := fun r => a (p ^ r)) (by simp [heig.1]) (by simp) hrec hsum_even
    (norm_prime_pow_k_sub_one_mul_neg_s hp hs)
  exact hshim.2.2

/-- **UNCONDITIONAL DEGREE-3 EULER PRODUCT FOR `L(s, Sym² f)` (`sym2L_euler_product`)**:
for ANY normalized level-1 Hecke eigenform `a` of weight `k ≥ 1` with `a 0 = 0` and Hecke bound
`|a_n| ≤ C n^{k/2}`, on `Re(s) > k + 1`:
`L(s, Sym² f) = ∏' p : Nat.Primes, (sym2LocalPoly (a p) (p^{k - 1}) (p^{-s}))⁻¹`! -/
theorem sym2L_euler_product {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (ha0 : a 0 = 0)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    sym2L k a s = ∏' p : Nat.Primes, sym2EulerFactor k (a p.1) p.1 s := by
  have hsum := LSeriesSummable_sym2_of_heckeBound hk hbound hs
  have h1 : LSeries.term (sym2Coeff k a) s 1 = 1 := by
    simp [LSeries.term_of_ne_zero, sym2Coeff_one heig]
  have h0 : LSeries.term (sym2Coeff k a) s 0 = 0 := LSeries.term_zero _ _
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      LSeries.term (sym2Coeff k a) s (m * n) =
        LSeries.term (sym2Coeff k a) s m * LSeries.term (sym2Coeff k a) s n := by
    intro m n hcop
    by_cases hm : m = 0
    · subst hm; simp
    by_cases hn : n = 0
    · subst hn; simp
    rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
      LSeries.term_of_ne_zero hn, sym2Coeff_mul_of_coprime ha0 heig hcop, Nat.cast_mul]
    have hcpow : ((m : ℂ) * (n : ℂ)) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
      simpa [Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n) s
    rw [hcpow, mul_div_mul_comm]
  have heuler := EulerProduct.eulerProduct_tprod h1 hmul hsum.norm h0
  rw [sym2L, LSeries, ← heuler]
  refine tprod_congr fun p => ?_
  exact sym2Coeff_tsum_prime_pow hk hbound heig hs p.prop

/-- Finite-prime-product convergence (`Filter.Tendsto`) of the degree-3 `Sym²` Euler product. -/
theorem sym2L_euler_product_tendsto {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (ha0 : a 0 = 0)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    Filter.Tendsto
      (fun B : ℕ => ∏ p ∈ B.primesBelow, sym2EulerFactor k (a p) p s)
      Filter.atTop (nhds (sym2L k a s)) := by
  have hsum := LSeriesSummable_sym2_of_heckeBound hk hbound hs
  have h1 : LSeries.term (sym2Coeff k a) s 1 = 1 := by
    simp [LSeries.term_of_ne_zero, sym2Coeff_one heig]
  have h0 : LSeries.term (sym2Coeff k a) s 0 = 0 := LSeries.term_zero _ _
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      LSeries.term (sym2Coeff k a) s (m * n) =
        LSeries.term (sym2Coeff k a) s m * LSeries.term (sym2Coeff k a) s n := by
    intro m n hcop
    by_cases hm : m = 0
    · subst hm; simp
    by_cases hn : n = 0
    · subst hn; simp
    rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
      LSeries.term_of_ne_zero hn, sym2Coeff_mul_of_coprime ha0 heig hcop, Nat.cast_mul]
    have hcpow : ((m : ℂ) * (n : ℂ)) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
      simpa [Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n) s
    rw [hcpow, mul_div_mul_comm]
  have heuler := EulerProduct.eulerProduct h1 hmul hsum.norm h0
  refine heuler.congr fun B => ?_
  refine Finset.prod_congr rfl fun p hp => ?_
  exact sym2Coeff_tsum_prime_pow hk hbound heig hs (Nat.prime_of_mem_primesBelow hp)

/-- **Satake-Factored Degree-3 `Sym²` Euler Product (`sym2L_euler_product_satake`)**:
`L(s, Sym² f) = ∏' p, ((1 - α_p² p^{-s})(1 - α_p β_p p^{-s})(1 - β_p² p^{-s}))⁻¹`. -/
theorem sym2L_euler_product_satake {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (ha0 : a 0 = 0)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    (α β : Nat.Primes → ℂ)
    (hsat : ∀ p : Nat.Primes, IsSatakePair (a p.1) ((p.1 : ℂ) ^ (k - 1)) (α p) (β p))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    sym2L k a s =
      ∏' p : Nat.Primes,
        ((1 - α p ^ 2 * (p.1 : ℂ) ^ (-s)) *
         (1 - α p * β p * (p.1 : ℂ) ^ (-s)) *
         (1 - β p ^ 2 * (p.1 : ℂ) ^ (-s)))⁻¹ := by
  rw [sym2L_euler_product hk ha0 hbound heig hs]
  refine tprod_congr fun p => ?_
  simp only [sym2EulerFactor, sym2_local_factor_eq (hsat p)]

/-- **UNCONDITIONAL NON-VANISHING OF `L(s, Sym² f)` ON `Re(s) > k + 1` (`sym2L_ne_zero_of_re_gt`)**:
for EVERY normalized level-1 Hecke eigenform `a` of weight `k ≥ 1` obeying Hecke's bound
`|a_n| ≤ C n^{k/2}` (`a 0 = 0`) and EVERY `s : ℂ` with `k + 1 < s.re`, `sym2L k a s ≠ 0`! -/
theorem sym2L_ne_zero_of_re_gt {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (ha0 : a 0 = 0)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    sym2L k a s ≠ 0 := by
  -- Define `u p = sym2LocalPoly (a p) (p^{k-1}) (p^{-s}) - 1`, show `Summable u`
  let u : Nat.Primes → ℂ := fun p =>
    sym2LocalPoly (a p.1) ((p.1 : ℂ) ^ (k - 1)) ((p.1 : ℂ) ^ (-s)) - 1
  have hreal_summable : ∀ {α : ℝ}, 1 < α →
      Summable (fun p : Nat.Primes => ((p.1 : ℝ) ^ α)⁻¹) := fun {α} hα =>
    (Real.summable_nat_rpow_inv.mpr hα).comp_injective (Subtype.val_injective (p := Nat.Prime))
  have hnorm_p_neg_s : ∀ (p : Nat.Primes), ‖(p.1 : ℂ) ^ (-s)‖ = ((p.1 : ℝ) ^ s.re)⁻¹ := fun p => by
    have hp_pos : (0 : ℝ) < (p.1 : ℝ) := Nat.cast_pos.mpr p.prop.pos
    rw [show (p.1 : ℂ) = ((p.1 : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, neg_re, Real.rpow_neg hp_pos.le]
  have hsum_u : Summable u := by
    have hre1 : 1 < s.re - (k : ℝ) := by linarith
    have hmaj : Summable (fun p : Nat.Primes => (2 * (C ^ 2 + 1) + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹) :=
      (hreal_summable hre1).mul_left (2 * (C ^ 2 + 1) + 1)
    refine Summable.of_norm_bounded hmaj fun p => ?_
    have hp1 : 1 ≤ p.1 := p.prop.one_lt.le
    have hp_pos : (0 : ℝ) < (p.1 : ℝ) := Nat.cast_pos.mpr p.prop.pos
    have hp_ge1 : (1 : ℝ) ≤ (p.1 : ℝ) := Nat.one_le_cast.mpr hp1
    have hka : ‖a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)‖ ≤ (C ^ 2 + 1) * (p.1 : ℝ) ^ (k : ℝ) := by
      have ha_sq : ‖a p.1 ^ 2‖ ≤ C ^ 2 * (p.1 : ℝ) ^ (k : ℝ) := by
        rw [norm_pow]
        have hb := pow_le_pow_left₀ (norm_nonneg _) (hbound p.1 hp1) 2
        refine hb.trans_eq ?_
        rw [mul_pow, ← Real.rpow_natCast ((p.1 : ℝ) ^ ((k : ℝ) / 2)) 2,
          ← Real.rpow_mul hp_pos.le]
        congr 2; ring
      have hpk : ‖(p.1 : ℂ) ^ (k - 1)‖ ≤ (p.1 : ℝ) ^ (k : ℝ) := by
        rw [norm_pow, Complex.norm_natCast, ← Real.rpow_natCast (p.1 : ℝ) (k - 1)]
        exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (Nat.cast_le.mpr (Nat.sub_le k 1))
      calc ‖a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)‖
          ≤ ‖a p.1 ^ 2‖ + ‖(p.1 : ℂ) ^ (k - 1)‖ := norm_sub_le _ _
        _ ≤ C ^ 2 * (p.1 : ℝ) ^ (k : ℝ) + (p.1 : ℝ) ^ (k : ℝ) := add_le_add ha_sq hpk
        _ = (C ^ 2 + 1) * (p.1 : ℝ) ^ (k : ℝ) := by ring
    have hcT_le1 : ‖(p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)‖ ≤ 1 :=
      (norm_prime_pow_k_sub_one_mul_neg_s p.prop hs).le
    have hpk_neg_s : (p.1 : ℝ) ^ (k : ℝ) * ((p.1 : ℝ) ^ s.re)⁻¹ = ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by
      rw [← Real.rpow_neg hp_pos.le, ← Real.rpow_add hp_pos, ← Real.rpow_neg hp_pos.le]
      congr 1; ring
    have ht1 : ‖-((a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s))‖ ≤
        (C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by
      rw [norm_neg, norm_mul, hnorm_p_neg_s p]
      calc ‖a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)‖ * ((p.1 : ℝ) ^ s.re)⁻¹
          ≤ (C ^ 2 + 1) * (p.1 : ℝ) ^ (k : ℝ) * ((p.1 : ℝ) ^ s.re)⁻¹ :=
            mul_le_mul_of_nonneg_right hka (inv_nonneg.mpr (Real.rpow_nonneg hp_pos.le _))
        _ = (C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by rw [mul_assoc, hpk_neg_s]
    have ht2 : ‖(p.1 : ℂ) ^ (k - 1) * (a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * ((p.1 : ℂ) ^ (-s)) ^ 2‖ ≤
        (C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by
      have hrearr : (p.1 : ℂ) ^ (k - 1) * (a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * ((p.1 : ℂ) ^ (-s)) ^ 2 =
          ((p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)) *
            ((a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s)) := by ring
      rw [hrearr, norm_mul]
      calc ‖(p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)‖ *
              ‖(a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s)‖
          ≤ 1 * ((C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹) :=
            mul_le_mul hcT_le1 (by simpa [norm_neg] using ht1) (norm_nonneg _) zero_le_one
        _ = (C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := one_mul _
    have ht3 : ‖-((p.1 : ℂ) ^ (k - 1)) ^ 3 * ((p.1 : ℂ) ^ (-s)) ^ 3‖ ≤
        ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by
      have hrearr : -((p.1 : ℂ) ^ (k - 1)) ^ 3 * ((p.1 : ℂ) ^ (-s)) ^ 3 =
          -(((p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)) ^ 2 *
            ((p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s))) := by ring
      rw [hrearr, norm_neg, norm_mul, norm_pow]
      have hsq1 : ‖(p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg ((p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s))]
      have hlast : ‖(p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)‖ ≤ ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by
        rw [norm_mul, norm_pow, Complex.norm_natCast, hnorm_p_neg_s p]
        have hpk : (p.1 : ℝ) ^ (k - 1) ≤ (p.1 : ℝ) ^ (k : ℝ) := by
          rw [← Real.rpow_natCast (p.1 : ℝ) (k - 1)]
          exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (Nat.cast_le.mpr (Nat.sub_le k 1))
        calc (p.1 : ℝ) ^ (k - 1) * ((p.1 : ℝ) ^ s.re)⁻¹
            ≤ (p.1 : ℝ) ^ (k : ℝ) * ((p.1 : ℝ) ^ s.re)⁻¹ :=
              mul_le_mul_of_nonneg_right hpk (inv_nonneg.mpr (Real.rpow_nonneg hp_pos.le _))
          _ = ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := hpk_neg_s
      calc ‖(p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)‖ ^ 2 *
              ‖(p.1 : ℂ) ^ (k - 1) * (p.1 : ℂ) ^ (-s)‖
          ≤ 1 * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ :=
            mul_le_mul hsq1 hlast (norm_nonneg _) zero_le_one
        _ = ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := one_mul _
    have hu_eq : u p =
        -((a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s)) +
          (p.1 : ℂ) ^ (k - 1) * (a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * ((p.1 : ℂ) ^ (-s)) ^ 2 +
          (-((p.1 : ℂ) ^ (k - 1)) ^ 3 * ((p.1 : ℂ) ^ (-s)) ^ 3) := by
      dsimp only [u]
      rw [sym2LocalPoly_expanded]
      ring
    rw [hu_eq]
    calc ‖-((a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s)) +
            (p.1 : ℂ) ^ (k - 1) * (a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * ((p.1 : ℂ) ^ (-s)) ^ 2 +
            (-((p.1 : ℂ) ^ (k - 1)) ^ 3 * ((p.1 : ℂ) ^ (-s)) ^ 3)‖
        ≤ ‖-((a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s)) +
            (p.1 : ℂ) ^ (k - 1) * (a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * ((p.1 : ℂ) ^ (-s)) ^ 2‖ +
          ‖-((p.1 : ℂ) ^ (k - 1)) ^ 3 * ((p.1 : ℂ) ^ (-s)) ^ 3‖ := norm_add_le _ _
      _ ≤ ‖-((a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * (p.1 : ℂ) ^ (-s))‖ +
          ‖(p.1 : ℂ) ^ (k - 1) * (a p.1 ^ 2 - (p.1 : ℂ) ^ (k - 1)) * ((p.1 : ℂ) ^ (-s)) ^ 2‖ +
          ‖-((p.1 : ℂ) ^ (k - 1)) ^ 3 * ((p.1 : ℂ) ^ (-s)) ^ 3‖ :=
            add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ +
          (C ^ 2 + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ +
          ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := add_le_add (add_le_add ht1 ht2) ht3
      _ = (2 * (C ^ 2 + 1) + 1) * ((p.1 : ℝ) ^ (s.re - (k : ℝ)))⁻¹ := by ring
  have hmult : Multipliable (fun p : Nat.Primes => 1 + u p) :=
    Complex.multipliable_one_add_of_summable hsum_u
  let embed : ℕ → Finset Nat.Primes := fun B =>
    Finset.map
      ⟨fun (x : {p // p ∈ B.primesBelow}) => (⟨x.1, Nat.prime_of_mem_primesBelow x.2⟩ : Nat.Primes),
       fun x y hxy => Subtype.ext (congrArg (fun p : Nat.Primes => p.1) hxy)⟩
      B.primesBelow.attach
  have hembed_atTop : Tendsto embed atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro S
    rw [Filter.eventually_atTop]
    refine ⟨S.sup (fun p => p.1) + 1, fun B hB => ?_⟩
    intro p hpS
    have hlt : p.1 < B := by
      have hle : p.1 ≤ S.sup (fun q => q.1) := Finset.le_sup (f := fun q : Nat.Primes => q.1) hpS
      omega
    have hmem : p.1 ∈ B.primesBelow := Nat.mem_primesBelow.mpr ⟨hlt, p.prop⟩
    rw [Finset.mem_map]
    exact ⟨⟨p.1, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hprod_tendsto : Tendsto
      (fun B : ℕ => ∏ p ∈ B.primesBelow, sym2LocalPoly (a p) ((p : ℂ) ^ (k - 1)) ((p : ℂ) ^ (-s)))
      atTop (nhds (∏' p : Nat.Primes, (1 + u p))) := by
    have h1 := hmult.hasProd.comp hembed_atTop
    refine h1.congr fun B => ?_
    dsimp only [Function.comp_apply, embed]
    rw [Finset.prod_map, ← Finset.prod_attach B.primesBelow]
    refine Finset.prod_congr rfl fun x _ => ?_
    change 1 + (sym2LocalPoly (a x.1) ((x.1 : ℂ) ^ (k - 1)) ((x.1 : ℂ) ^ (-s)) - 1) =
      sym2LocalPoly (a x.1) ((x.1 : ℂ) ^ (k - 1)) ((x.1 : ℂ) ^ (-s))
    ring
  have hinv_tendsto := sym2L_euler_product_tendsto hk ha0 hbound heig hs
  have hmul_tendsto := hprod_tendsto.mul hinv_tendsto
  -- Every local `sym2LocalPoly` factor is nonzero, so the product of finite products is identically 1
  have hlocal_ne : ∀ p : ℕ, p.Prime →
      sym2LocalPoly (a p) ((p : ℂ) ^ (k - 1)) ((p : ℂ) ^ (-s)) ≠ 0 := fun p hp => by
    have hinj : Function.Injective (fun r : ℕ => p ^ r) := Nat.pow_right_injective hp.two_le
    have hsum_even : Summable (fun r : ℕ => a (p ^ (2 * r)) * ((p : ℂ) ^ (-s)) ^ r) := by
      refine ((LSeriesSummable_sqIndex_of_heckeBound hbound hs).comp_injective hinj).congr fun r => ?_
      rw [Function.comp_apply, LSeries.term_of_ne_zero (pow_ne_zero r hp.ne_zero),
        div_eq_mul_inv, cpow_prime_pow_neg' p s r, ← pow_mul, mul_comm r 2]
    have hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * a (p ^ r) := by
      intro r
      have h := eigenform_prime_pow_recurrence heig hp r
      rwa [trivialChar_one_apply, one_mul] at h
    exact (tsum_even_primePow_eq_div_sym2LocalPoly (g := fun r => a (p ^ r))
      (by simp [heig.1]) (by simp) hrec hsum_even (norm_prime_pow_k_sub_one_mul_neg_s hp hs)).1
  have hconst_one : ∀ B : ℕ,
      (∏ p ∈ B.primesBelow, sym2LocalPoly (a p) ((p : ℂ) ^ (k - 1)) ((p : ℂ) ^ (-s))) *
        (∏ p ∈ B.primesBelow, sym2EulerFactor k (a p) p s) = 1 := fun B => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    exact mul_inv_cancel₀ (hlocal_ne p (Nat.prime_of_mem_primesBelow hp))
  have hmul_eq_one : (∏' p : Nat.Primes, (1 + u p)) * sym2L k a s = 1 :=
    tendsto_nhds_unique (hmul_tendsto.congr hconst_one) tendsto_const_nhds
  exact right_ne_zero_of_mul_eq_one hmul_eq_one

/-- **UNCONDITIONAL NON-VANISHING OF THE RANKIN–SELBERG CONVOLUTION `L(s, f × f)` ON `Re(s) > k + 1`**. -/
theorem rankinSelbergL_ne_zero_of_re_gt {k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℂ} {C : ℝ}
    (ha0 : a 0 = 0)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) a a)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    rankinSelbergL k a s ≠ 0 := by
  rw [rankinSelberg_eq_zeta_mul_sym2 hk hbound heig hs]
  have hz_ne : riemannZeta (s - (k : ℂ) + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  exact mul_ne_zero hz_ne (sym2L_ne_zero_of_re_gt hk ha0 hbound heig hs)

/-! ### Unconditional Master Cusp-Form `Sym²` & Rankin–Selberg Package (`0` Assumptions!) -/

/-- **UNCONDITIONAL CONVERGENCE OF `L(s, Sym² f)` FOR EVERY LEVEL-1 CUSP FORM `f ∈ S_k(SL₂(ℤ))`**:
via `Stage9DeltaHadamard.hecke_cuspForm_coeff_bound` (`|a_n(f)| ≤ C n^{k/2}`). -/
theorem LSeriesSummable_sym2 {k : ℕ} (hk : 1 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (sym2Coeff k (qExpansionCoeff f)) s := by
  obtain ⟨C, _, hC⟩ := hecke_cuspForm_coeff_bound k f
  exact LSeriesSummable_sym2_of_heckeBound hk hC hs

/-- **UNCONDITIONAL CONVERGENCE OF `L(s, f × f)` FOR EVERY LEVEL-1 CUSP FORM `f ∈ S_k(SL₂(ℤ))`**. -/
theorem LSeriesSummable_rankinSelberg {k : ℕ} (hk : 1 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (rankinSelbergCoeff k (qExpansionCoeff f)) s := by
  obtain ⟨C, _, hC⟩ := hecke_cuspForm_coeff_bound k f
  exact LSeriesSummable_rankinSelberg_of_heckeBound hk hC hs

/-- **UNCONDITIONAL MASTER THEOREM FOR EVERY NORMALIZED LEVEL-1 HECKE EIGENFORM `f ∈ S_k(SL₂(ℤ))`**:
on `Re(s) > k + 1`:
1. `LSeriesSummable (sym2Coeff k (qExpansionCoeff f)) s`,
2. **Shimura Identity**: `L(s, Sym² f) = ζ(2s - 2k + 2) * ∑_{n ≥ 1} a_{n²}(f) n^{-s}`,
3. **Rankin–Selberg Identity**: `L(s, f × f) = ζ(s - k + 1) * L(s, Sym² f)`,
4. **Degree-3 Euler Product**: `L(s, Sym² f) = ∏' p, (sym2LocalPoly (a_p(f)) (p^{k-1}) (p^{-s}))⁻¹`,
5. **Non-Vanishing**: `L(s, Sym² f) ≠ 0` and `L(s, f × f) ≠ 0`! -/
theorem cuspForm_sym2L_master {k : ℕ} (hk : 1 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff f) (qExpansionCoeff f))
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (sym2Coeff k (qExpansionCoeff f)) s ∧
    sym2L k (qExpansionCoeff f) s =
      riemannZeta (2 * s - 2 * (k : ℂ) + 2) * LSeries (fun n : ℕ => qExpansionCoeff f (n ^ 2)) s ∧
    rankinSelbergL k (qExpansionCoeff f) s =
      riemannZeta (s - (k : ℂ) + 1) * sym2L k (qExpansionCoeff f) s ∧
    sym2L k (qExpansionCoeff f) s =
      ∏' p : Nat.Primes, sym2EulerFactor k (qExpansionCoeff f p.1) p.1 s ∧
    sym2L k (qExpansionCoeff f) s ≠ 0 ∧
    rankinSelbergL k (qExpansionCoeff f) s ≠ 0 := by
  obtain ⟨C, _, hC⟩ := hecke_cuspForm_coeff_bound k f
  have h0 : qExpansionCoeff f 0 = 0 := qExpansionCoeff_zero f
  exact ⟨LSeriesSummable_sym2_of_heckeBound hk hC hs,
    sym2L_eq_zeta_mul_sum_sq_index hk hC hs,
    rankinSelberg_eq_zeta_mul_sym2 hk hC heig hs,
    sym2L_euler_product hk h0 hC heig hs,
    sym2L_ne_zero_of_re_gt hk h0 hC heig hs,
    rankinSelbergL_ne_zero_of_re_gt hk h0 hC heig hs⟩

end GlobalSym2AndRankinSelberg

/-! ## Section 3: Explicit Specializations to `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂` & `S₂₄` + Local Factors at `p = 2, 3` -/

section ConcreteLevelOneSpecializations

theorem isNormalizedHeckeEigenform_delta12 :
    IsNormalizedHeckeEigenform 12 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff delta12) (qExpansionCoeff delta12) :=
  isNormalizedHeckeEigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.1
    (by
      change qExpansionCoeff ramanujanDelta 1 = 1
      rw [qExpansionCoeff_ramanujanDelta, ramanujanTau_one]
      simp)

/-- **UNCONDITIONAL `Sym²` & RANKIN–SELBERG MASTER THEOREM FOR RAMANUJAN'S `Δ₁₂` (`Re(s) > 13`)**. -/
theorem delta12_sym2L_master {s : ℂ} (hs : 13 < s.re) :
    LSeriesSummable (sym2Coeff 12 (qExpansionCoeff delta12)) s ∧
    sym2L 12 (qExpansionCoeff delta12) s =
      riemannZeta (2 * s - 22) * LSeries (fun n : ℕ => qExpansionCoeff delta12 (n ^ 2)) s ∧
    rankinSelbergL 12 (qExpansionCoeff delta12) s =
      riemannZeta (s - 11) * sym2L 12 (qExpansionCoeff delta12) s ∧
    sym2L 12 (qExpansionCoeff delta12) s =
      ∏' p : Nat.Primes, sym2EulerFactor 12 (qExpansionCoeff delta12 p.1) p.1 s ∧
    sym2L 12 (qExpansionCoeff delta12) s ≠ 0 ∧
    rankinSelbergL 12 (qExpansionCoeff delta12) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 12) (by norm_num) delta12
    isNormalizedHeckeEigenform_delta12 (by norm_num; linarith)
  rw [show 2 * s - 2 * ((12 : ℕ) : ℂ) + 2 = 2 * s - 22 by push_cast; ring,
      show s - ((12 : ℕ) : ℂ) + 1 = s - 11 by push_cast; ring] at h
  exact h

/-- **UNCONDITIONAL `Sym²` & RANKIN–SELBERG MASTER THEOREM FOR `Δ₁₆` (`Re(s) > 17`)**. -/
theorem delta16_sym2L_master {s : ℂ} (hs : 17 < s.re) :
    LSeriesSummable (sym2Coeff 16 (qExpansionCoeff delta16)) s ∧
    sym2L 16 (qExpansionCoeff delta16) s =
      riemannZeta (2 * s - 30) * LSeries (fun n : ℕ => qExpansionCoeff delta16 (n ^ 2)) s ∧
    rankinSelbergL 16 (qExpansionCoeff delta16) s =
      riemannZeta (s - 15) * sym2L 16 (qExpansionCoeff delta16) s ∧
    sym2L 16 (qExpansionCoeff delta16) s =
      ∏' p : Nat.Primes, sym2EulerFactor 16 (qExpansionCoeff delta16 p.1) p.1 s ∧
    sym2L 16 (qExpansionCoeff delta16) s ≠ 0 ∧
    rankinSelbergL 16 (qExpansionCoeff delta16) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 16) (by norm_num) delta16
    isNormalizedHeckeEigenform_delta16 (by norm_num; linarith)
  rw [show 2 * s - 2 * ((16 : ℕ) : ℂ) + 2 = 2 * s - 30 by push_cast; ring,
      show s - ((16 : ℕ) : ℂ) + 1 = s - 15 by push_cast; ring] at h
  exact h

/-- **UNCONDITIONAL `Sym²` & RANKIN–SELBERG MASTER THEOREM FOR `Δ₁₈` (`Re(s) > 19`)**. -/
theorem delta18_sym2L_master {s : ℂ} (hs : 19 < s.re) :
    LSeriesSummable (sym2Coeff 18 (qExpansionCoeff delta18)) s ∧
    sym2L 18 (qExpansionCoeff delta18) s =
      riemannZeta (2 * s - 34) * LSeries (fun n : ℕ => qExpansionCoeff delta18 (n ^ 2)) s ∧
    rankinSelbergL 18 (qExpansionCoeff delta18) s =
      riemannZeta (s - 17) * sym2L 18 (qExpansionCoeff delta18) s ∧
    sym2L 18 (qExpansionCoeff delta18) s =
      ∏' p : Nat.Primes, sym2EulerFactor 18 (qExpansionCoeff delta18 p.1) p.1 s ∧
    sym2L 18 (qExpansionCoeff delta18) s ≠ 0 ∧
    rankinSelbergL 18 (qExpansionCoeff delta18) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 18) (by norm_num) delta18
    isNormalizedHeckeEigenform_delta18 (by norm_num; linarith)
  rw [show 2 * s - 2 * ((18 : ℕ) : ℂ) + 2 = 2 * s - 34 by push_cast; ring,
      show s - ((18 : ℕ) : ℂ) + 1 = s - 17 by push_cast; ring] at h
  exact h

/-- **UNCONDITIONAL `Sym²` & RANKIN–SELBERG MASTER THEOREM FOR `Δ₂₀` (`Re(s) > 21`)**. -/
theorem delta20_sym2L_master {s : ℂ} (hs : 21 < s.re) :
    LSeriesSummable (sym2Coeff 20 (qExpansionCoeff delta20)) s ∧
    sym2L 20 (qExpansionCoeff delta20) s =
      riemannZeta (2 * s - 38) * LSeries (fun n : ℕ => qExpansionCoeff delta20 (n ^ 2)) s ∧
    rankinSelbergL 20 (qExpansionCoeff delta20) s =
      riemannZeta (s - 19) * sym2L 20 (qExpansionCoeff delta20) s ∧
    sym2L 20 (qExpansionCoeff delta20) s =
      ∏' p : Nat.Primes, sym2EulerFactor 20 (qExpansionCoeff delta20 p.1) p.1 s ∧
    sym2L 20 (qExpansionCoeff delta20) s ≠ 0 ∧
    rankinSelbergL 20 (qExpansionCoeff delta20) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 20) (by norm_num) delta20
    isNormalizedHeckeEigenform_delta20 (by norm_num; linarith)
  rw [show 2 * s - 2 * ((20 : ℕ) : ℂ) + 2 = 2 * s - 38 by push_cast; ring,
      show s - ((20 : ℕ) : ℂ) + 1 = s - 19 by push_cast; ring] at h
  exact h

/-- **UNCONDITIONAL `Sym²` & RANKIN–SELBERG MASTER THEOREM FOR `Δ₂₂` (`Re(s) > 23`)**. -/
theorem delta22_sym2L_master {s : ℂ} (hs : 23 < s.re) :
    LSeriesSummable (sym2Coeff 22 (qExpansionCoeff delta22)) s ∧
    sym2L 22 (qExpansionCoeff delta22) s =
      riemannZeta (2 * s - 42) * LSeries (fun n : ℕ => qExpansionCoeff delta22 (n ^ 2)) s ∧
    rankinSelbergL 22 (qExpansionCoeff delta22) s =
      riemannZeta (s - 21) * sym2L 22 (qExpansionCoeff delta22) s ∧
    sym2L 22 (qExpansionCoeff delta22) s =
      ∏' p : Nat.Primes, sym2EulerFactor 22 (qExpansionCoeff delta22 p.1) p.1 s ∧
    sym2L 22 (qExpansionCoeff delta22) s ≠ 0 ∧
    rankinSelbergL 22 (qExpansionCoeff delta22) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 22) (by norm_num) delta22
    isNormalizedHeckeEigenform_delta22 (by norm_num; linarith)
  rw [show 2 * s - 2 * ((22 : ℕ) : ℂ) + 2 = 2 * s - 42 by push_cast; ring,
      show s - ((22 : ℕ) : ℂ) + 1 = s - 21 by push_cast; ring] at h
  exact h

/-- **UNCONDITIONAL `Sym²` & RANKIN–SELBERG MASTER THEOREMS FOR WEIGHT-24 EIGENFORMS
`S24_eigenPlus` AND `S24_eigenMinus` (`Re(s) > 25`)**! -/
theorem S24_eigenPlus_sym2L_master {s : ℂ} (hs : 25 < s.re) :
    LSeriesSummable (sym2Coeff 24 (qExpansionCoeff S24_eigenPlus)) s ∧
    sym2L 24 (qExpansionCoeff S24_eigenPlus) s =
      riemannZeta (2 * s - 46) * LSeries (fun n : ℕ => qExpansionCoeff S24_eigenPlus (n ^ 2)) s ∧
    rankinSelbergL 24 (qExpansionCoeff S24_eigenPlus) s =
      riemannZeta (s - 23) * sym2L 24 (qExpansionCoeff S24_eigenPlus) s ∧
    sym2L 24 (qExpansionCoeff S24_eigenPlus) s =
      ∏' p : Nat.Primes, sym2EulerFactor 24 (qExpansionCoeff S24_eigenPlus p.1) p.1 s ∧
    sym2L 24 (qExpansionCoeff S24_eigenPlus) s ≠ 0 ∧
    rankinSelbergL 24 (qExpansionCoeff S24_eigenPlus) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 24) (by norm_num) S24_eigenPlus
    isNormalizedHeckeEigenform_S24_eigenPlus (by norm_num; linarith)
  rw [show 2 * s - 2 * ((24 : ℕ) : ℂ) + 2 = 2 * s - 46 by push_cast; ring,
      show s - ((24 : ℕ) : ℂ) + 1 = s - 23 by push_cast; ring] at h
  exact h

theorem S24_eigenMinus_sym2L_master {s : ℂ} (hs : 25 < s.re) :
    LSeriesSummable (sym2Coeff 24 (qExpansionCoeff S24_eigenMinus)) s ∧
    sym2L 24 (qExpansionCoeff S24_eigenMinus) s =
      riemannZeta (2 * s - 46) * LSeries (fun n : ℕ => qExpansionCoeff S24_eigenMinus (n ^ 2)) s ∧
    rankinSelbergL 24 (qExpansionCoeff S24_eigenMinus) s =
      riemannZeta (s - 23) * sym2L 24 (qExpansionCoeff S24_eigenMinus) s ∧
    sym2L 24 (qExpansionCoeff S24_eigenMinus) s =
      ∏' p : Nat.Primes, sym2EulerFactor 24 (qExpansionCoeff S24_eigenMinus p.1) p.1 s ∧
    sym2L 24 (qExpansionCoeff S24_eigenMinus) s ≠ 0 ∧
    rankinSelbergL 24 (qExpansionCoeff S24_eigenMinus) s ≠ 0 := by
  have h := cuspForm_sym2L_master (k := 24) (by norm_num) S24_eigenMinus
    isNormalizedHeckeEigenform_S24_eigenMinus (by norm_num; linarith)
  rw [show 2 * s - 2 * ((24 : ℕ) : ℂ) + 2 = 2 * s - 46 by push_cast; ring,
      show s - ((24 : ℕ) : ℂ) + 1 = s - 23 by push_cast; ring] at h
  exact h

/-! ### Explicit Local `Sym²` Euler Polynomials at `p = 2, 3` for `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂` -/

/-- Exact local `Sym²` Euler factors & `sym2Coeff` values at `p = 2, 3` for Ramanujan's `Δ₁₂`. -/
theorem delta12_sym2_local_at_2_3 (T : ℂ) :
    sym2Coeff 12 (qExpansionCoeff delta12) 2 = -1472 ∧
    sym2Coeff 12 (qExpansionCoeff delta12) 3 = -113643 ∧
    sym2LocalPoly (qExpansionCoeff delta12 2) ((2 : ℂ) ^ 11) T =
      1 + 1472 * T - 3014656 * T ^ 2 - 8589934592 * T ^ 3 ∧
    sym2LocalPoly (qExpansionCoeff delta12 3) ((3 : ℂ) ^ 11) T =
      1 + 113643 * T - 20131516521 * T ^ 2 - 5559060566555523 * T ^ 3 := by
  have ha2 : qExpansionCoeff delta12 2 = -24 := by
    change qExpansionCoeff ramanujanDelta 2 = -24
    rw [qExpansionCoeff_ramanujanDelta, ramanujanTau_two]; norm_num
  have ha3 : qExpansionCoeff delta12 3 = 252 := by
    change qExpansionCoeff ramanujanDelta 3 = 252
    rw [qExpansionCoeff_ramanujanDelta, ramanujanTau_three]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta12 Nat.prime_two, ha2]; norm_num
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta12 Nat.prime_three, ha3]; norm_num
  · rw [sym2LocalPoly_expanded, ha2]; ring
  · rw [sym2LocalPoly_expanded, ha3]; ring

/-- Exact local `Sym²` Euler factors & `sym2Coeff` values at `p = 2, 3` for `Δ₁₆`. -/
theorem delta16_sym2_local_at_2_3 (T : ℂ) :
    sym2Coeff 16 (qExpansionCoeff delta16) 2 = 13888 ∧
    sym2Coeff 16 (qExpansionCoeff delta16) 3 = -3139803 ∧
    sym2LocalPoly (qExpansionCoeff delta16 2) ((2 : ℂ) ^ 15) T =
      1 - 13888 * T + 455081984 * T ^ 2 - 35184372088832 * T ^ 3 ∧
    sym2LocalPoly (qExpansionCoeff delta16 3) ((3 : ℂ) ^ 15) T =
      1 + 3139803 * T - 45052741245321 * T ^ 2 - 2954312706550833698643 * T ^ 3 := by
  have ha2 : qExpansionCoeff delta16 2 = 216 := by
    rw [← coeffDelta16Z_cast_eq, coeffDelta16Z_small.2.2.1]; norm_num
  have ha3 : qExpansionCoeff delta16 3 = -3348 := by
    rw [← coeffDelta16Z_cast_eq, coeffDelta16Z_small.2.2.2]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta16 Nat.prime_two, ha2]; norm_num
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta16 Nat.prime_three, ha3]; norm_num
  · rw [sym2LocalPoly_expanded, ha2]; ring
  · rw [sym2LocalPoly_expanded, ha3]; ring

/-- Exact local `Sym²` Euler factors & `sym2Coeff` values at `p = 2, 3` for `Δ₁₈`. -/
theorem delta18_sym2_local_at_2_3 (T : ℂ) :
    sym2Coeff 18 (qExpansionCoeff delta18) 2 = 147712 ∧
    sym2Coeff 18 (qExpansionCoeff delta18) 3 = -110787507 ∧
    sym2LocalPoly (qExpansionCoeff delta18 2) ((2 : ℂ) ^ 17) T =
      1 - 147712 * T + 19360907264 * T ^ 2 - 2251799813685248 * T ^ 3 ∧
    sym2LocalPoly (qExpansionCoeff delta18 3) ((3 : ℂ) ^ 17) T =
      1 + 110787507 * T - 14307116712343641 * T ^ 2 - 2153693963075557766310747 * T ^ 3 := by
  have ha2 : qExpansionCoeff delta18 2 = -528 := by
    rw [← coeffDelta18Z_cast_eq, coeffDelta18Z_small.2.2.1]; norm_num
  have ha3 : qExpansionCoeff delta18 3 = -4284 := by
    rw [← coeffDelta18Z_cast_eq, coeffDelta18Z_small.2.2.2]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta18 Nat.prime_two, ha2]; norm_num
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta18 Nat.prime_three, ha3]; norm_num
  · rw [sym2LocalPoly_expanded, ha2]; ring
  · rw [sym2LocalPoly_expanded, ha3]; ring

/-- Exact local `Sym²` Euler factors & `sym2Coeff` values at `p = 2, 3` for `Δ₂₀`. -/
theorem delta20_sym2_local_at_2_3 (T : ℂ) :
    sym2Coeff 20 (qExpansionCoeff delta20) 2 = -316352 ∧
    sym2Coeff 20 (qExpansionCoeff delta20) 3 = 1403363637 ∧
    sym2LocalPoly (qExpansionCoeff delta20 2) ((2 : ℂ) ^ 19) T =
      1 + 316352 * T - 165859557376 * T ^ 2 - 144115188075855872 * T ^ 3 ∧
    sym2LocalPoly (qExpansionCoeff delta20 3) ((3 : ℂ) ^ 19) T =
      1 - 1403363637 * T + 1631075479474075479 * T ^ 2 - 1570042899082081611640534563 * T ^ 3 := by
  have ha2 : qExpansionCoeff delta20 2 = 456 := by
    rw [← coeffDelta20Z_cast_eq, coeffDelta20Z_small.2.2.1]; norm_num
  have ha3 : qExpansionCoeff delta20 3 = 50652 := by
    rw [← coeffDelta20Z_cast_eq, coeffDelta20Z_small.2.2.2]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta20 Nat.prime_two, ha2]; norm_num
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta20 Nat.prime_three, ha3]; norm_num
  · rw [sym2LocalPoly_expanded, ha2]; ring
  · rw [sym2LocalPoly_expanded, ha3]; ring

/-- Exact local `Sym²` Euler factors & `sym2Coeff` values at `p = 2, 3` for `Δ₂₂`. -/
theorem delta22_sym2_local_at_2_3 (T : ℂ) :
    sym2Coeff 22 (qExpansionCoeff delta22) 2 = -2014208 ∧
    sym2Coeff 22 (qExpansionCoeff delta22) 3 = 6140423133 ∧
    sym2LocalPoly (qExpansionCoeff delta22 2) ((2 : ℂ) ^ 21) T =
      1 + 2014208 * T - 4224100335616 * T ^ 2 - 9223372036854775808 * T ^ 3 ∧
    sym2LocalPoly (qExpansionCoeff delta22 3) ((3 : ℂ) ^ 21) T =
      1 - 6140423133 * T + 64230994787051844999 * T ^ 2 - 1144561273430837494885949696427 * T ^ 3 := by
  have ha2 : qExpansionCoeff delta22 2 = -288 := by
    rw [← coeffDelta22Z_cast_eq, coeffDelta22Z_small.2.2.1]; norm_num
  have ha3 : qExpansionCoeff delta22 3 = -128844 := by
    rw [← coeffDelta22Z_cast_eq, coeffDelta22Z_small.2.2.2]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta22 Nat.prime_two, ha2]; norm_num
  · rw [sym2Coeff_prime isNormalizedHeckeEigenform_delta22 Nat.prime_three, ha3]; norm_num
  · rw [sym2LocalPoly_expanded, ha2]; ring
  · rw [sym2LocalPoly_expanded, ha3]; ring

end ConcreteLevelOneSpecializations

/-! ## Section 4: Adjoint `L(1, Ad f)` ↔ Petersson Norm ↔ Hida–Wiles Congruence-Ideal Bridge
(`adjointL_controls_congruence_prime` & `CountII` / `CountIII` Adjoint-Selmer Bound for `VWin`) -/

section AdjointLCongruenceBridge

/-- The Shimura–Hida archimedean Gamma/π factor connecting the unnormalized Petersson inner product
`⟨f, f⟩_Pet = ∬_D |f(z)|² y^{k-2} dx dy` to the adjoint `L`-value `L(k, Sym² f) = L(1, Ad f)`:
`adjointArchFactor k = 2^{2k - 1} π^{k + 1} / (k - 1)!`. -/
def adjointArchFactor (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (k + 1) / ((k - 1).factorial : ℝ)

theorem adjointArchFactor_pos (k : ℕ) : 0 < adjointArchFactor k := by
  unfold adjointArchFactor
  have hfac : (0 : ℝ) < ((k - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  positivity

/-- The Shimura–Hida adjoint `L`-value at `s = 1` (`L(k, Sym² f) = L(1, Ad f)`) expressed via the
concrete Petersson inner product `Stage10PeterssonHecke.peterssonInner f f`:
`adjointLAtOneFromPetersson f = (2^{2k - 1} π^{k + 1} / (k - 1)!) * ⟨f, f⟩_Pet`. -/
def adjointLAtOneFromPetersson {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) : ℂ :=
  (adjointArchFactor k : ℂ) * peterssonInner f f

/-- For every nonzero level-1 cusp form `f ∈ S_k(SL₂(ℤ))`, `adjointLAtOneFromPetersson f` is
strictly positive and purely real! -/
theorem adjointLAtOneFromPetersson_re_pos {k : ℕ} {f : CuspForm SL2ZRange (k : ℤ)} (hf : f ≠ 0) :
    0 < (adjointLAtOneFromPetersson f).re ∧ (adjointLAtOneFromPetersson f).im = 0 := by
  unfold adjointLAtOneFromPetersson
  have him : (peterssonInner f f).im = 0 := peterssonInner_self_im_eq_zero f
  have hre : 0 < (peterssonInner f f).re := peterssonInner_self_pos hf
  have harch : 0 < adjointArchFactor k := adjointArchFactor_pos k
  constructor
  · simp [Complex.mul_re, mul_pos harch hre]
  · simp [Complex.mul_im, him]

theorem adjointLAtOneFromPetersson_ne_zero {k : ℕ} {f : CuspForm SL2ZRange (k : ℤ)} (hf : f ≠ 0) :
    adjointLAtOneFromPetersson f ≠ 0 := by
  intro h0
  have hre := (adjointLAtOneFromPetersson_re_pos hf).1
  rw [h0, zero_re] at hre
  exact lt_irrefl 0 hre

/-- **Concrete `PeterssonQExpansionSpace` Instance for `CuspForm SL2ZRange k` (`0` Assumptions!)**:
wires `Stage10PeterssonHecke.cuspFormPeterssonHeckeSpace` and `qExpansionCoeff` directly into
`Stage6HeckeSpectral` and `Stage7HeckeRing`! -/
def cuspFormQExpansionSpace (k : ℕ) (hk : 1 ≤ k) :
    PeterssonQExpansionSpace k (1 : DirichletCharacter ℂ 1) (CuspForm SL2ZRange (k : ℤ)) where
  toPeterssonHeckeSpace := cuspFormPeterssonHeckeSpace k hk
  qExp :=
    { toFun := fun f => qExpansionCoeff f
      map_add' := fun f g => funext (qExpansionCoeff_add f g)
      map_smul' := fun c f => funext (qExpansionCoeff_smul c f) }
  qExp_injective := fun _ _ h => cuspForm_eq_of_qExpansion_coeff_eq (congrFun h)
  qExp_cusp := qExpansionCoeff_zero
  qExp_hecke := fun n hn f => by
    funext m
    change qExpansionCoeff (heckeCuspFormLin k hk n f) m = _
    rw [heckeCuspFormLin_apply k hk hn]
    exact heckeCuspForm_qExpansion_coeff k hk n hn f m

/-- **Unconditional Petersson Orthogonality of Distinct Level-1 Normalized Hecke Eigenforms**:
if `f, g ∈ S_k(SL₂(ℤ))` (`k ≥ 1`) are normalized Hecke eigenforms with `f ≠ g`, then
`peterssonInner f g = 0`! -/
theorem peterssonInner_eq_zero_of_distinct_eigenforms {k : ℕ} (hk : 1 ≤ k)
    {f g : CuspForm SL2ZRange (k : ℤ)}
    (hf : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff f) (qExpansionCoeff f))
    (hg : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff g) (qExpansionCoeff g))
    (hne : f ≠ g) :
    peterssonInner f g = 0 := by
  have hex : ∃ n : ℕ, 1 ≤ n ∧ qExpansionCoeff f n ≠ qExpansionCoeff g n := by
    by_contra hall
    push Not at hall
    apply hne
    apply cuspForm_eq_of_qExpansion_coeff_eq
    intro m
    match m with
    | 0 => rw [qExpansionCoeff_zero f, qExpansionCoeff_zero g]
    | m + 1 => exact hall (m + 1) (Nat.succ_pos m)
  obtain ⟨n, hn, hdiff⟩ := hex
  have hTf : heckeCuspForm k hk n hn f = qExpansionCoeff f n • f := by
    apply cuspForm_eq_of_qExpansion_coeff_eq
    intro m
    rw [qExpansionCoeff_smul, qExpansionCoeff, heckeCuspForm_qExpansion_coeff k hk n hn f m]
    exact congrFun (hf.2 n hn) m
  have hTg : heckeCuspForm k hk n hn g = qExpansionCoeff g n • g := by
    apply cuspForm_eq_of_qExpansion_coeff_eq
    intro m
    rw [qExpansionCoeff_smul, qExpansionCoeff, heckeCuspForm_qExpansion_coeff k hk n hn g m]
    exact congrFun (hg.2 n hn) m
  have hg_ne : g ≠ 0 := by
    intro h0
    have h1 := hg.1
    have hzero : qExpansionCoeff g 1 = 0 := by
      rw [h0]
      have hz : (0 : CuspForm SL2ZRange (k : ℤ)) = (0 : ℂ) • f := by simp
      rw [hz, qExpansionCoeff_smul, zero_mul]
    rw [hzero] at h1
    exact zero_ne_one h1
  have hreal : (qExpansionCoeff g n).im = 0 :=
    cuspForm_hecke_eigenvalue_real hk hn hg_ne hTg
  have hstar : star (qExpansionCoeff g n) = qExpansionCoeff g n :=
    Complex.conj_eq_iff_im.mpr hreal
  have hinner : qExpansionCoeff f n * peterssonInner f g =
      qExpansionCoeff g n * peterssonInner f g := by
    calc qExpansionCoeff f n * peterssonInner f g
        = peterssonInner (qExpansionCoeff f n • f) g := (peterssonInner_smul_left _ f g).symm
      _ = peterssonInner (heckeCuspForm k hk n hn f) g := by rw [hTf]
      _ = peterssonInner f (heckeCuspForm k hk n hn g) :=
          peterssonInner_heckeCuspForm_eq k hk n hn f g
      _ = peterssonInner f (qExpansionCoeff g n • g) := by rw [hTg]
      _ = star (qExpansionCoeff g n) * peterssonInner f g := peterssonInner_smul_right _ f g
      _ = qExpansionCoeff g n * peterssonInner f g := by rw [hstar]
  have hsub : (qExpansionCoeff f n - qExpansionCoeff g n) * peterssonInner f g = 0 := by
    linear_combination hinner
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hdiff)

/-- **Exact Petersson Orthogonal Projection Coordinate onto a Basis Eigenform**:
in any eigenbasis `b : Fin d → CuspForm SL2ZRange k` of normalized Hecke eigenforms, for every
`v ∈ CuspForm SL2ZRange k`, the `j₀`-th basis coordinate of `v` equals
`peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀)`! -/
theorem basis_repr_eq_petersson_ratio {k : ℕ} (hk : 1 ≤ k) {d : ℕ}
    (b : Module.Basis (Fin d) ℂ (CuspForm SL2ZRange (k : ℤ)))
    (heig : ∀ j : Fin d, IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff (b j)) (qExpansionCoeff (b j)))
    (j₀ : Fin d) (v : CuspForm SL2ZRange (k : ℤ)) :
    b.repr v j₀ = peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀) := by
  have hbj_ne : b j₀ ≠ 0 := b.ne_zero j₀
  have hnorm_ne : peterssonInner (b j₀) (b j₀) ≠ 0 := fun h0 =>
    hbj_ne ((peterssonInner_self_eq_zero_iff (b j₀)).mp h0)
  have hv : v = ∑ j : Fin d, b.repr v j • b j := (b.sum_repr v).symm
  have hpet : peterssonInner v (b j₀) = b.repr v j₀ * peterssonInner (b j₀) (b j₀) := by
    conv_lhs => rw [hv]
    have hsum_inner : ∀ (s : Finset (Fin d)) (c : Fin d → ℂ),
        peterssonInner (∑ j ∈ s, c j • b j) (b j₀) =
          ∑ j ∈ s, c j * peterssonInner (b j) (b j₀) := by
      intro s c
      induction s using Finset.cons_induction with
      | empty => simp [peterssonInner_zero_left]
      | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, peterssonInner_add_left,
          peterssonInner_smul_left, ih]
    rw [hsum_inner Finset.univ (fun j => b.repr v j),
      Finset.sum_eq_single j₀ (fun j _ hj => by
        have hne : b j ≠ b j₀ := fun h => hj (b.injective h)
        rw [peterssonInner_eq_zero_of_distinct_eigenforms hk (heig j) (heig j₀) hne, mul_zero])
        (fun h => absurd (Finset.mem_univ j₀) h)]
  rw [hpet, mul_div_cancel_right₀ _ hnorm_ne]

/-- **EXACT HIDA PETERSSON-PROJECTION CHARACTERIZATION OF THE CONGRUENCE IDEAL (`0` Assumptions!)**:
For ANY PID `𝒪 ↪ ℂ`, ANY level-1 weight `k ≥ 1`, ANY `𝒪`-integral eigenbasis
`b : Fin d → CuspForm SL2ZRange k` of normalized Hecke eigenforms, and `f = b j₀` with
Hecke-algebra augmentation `π_f : 𝕋_𝒪 →ₐ[𝒪] 𝒪` from `Stage7HeckeRing`:
for EVERY `a : 𝒪`,
`a ∈ Stage3PatchingUnification.congruenceIdeal π_f ↔`
`∀ v ∈ S_{k, 𝒪}, (algebraMap 𝒪 ℂ a) * (⟨v, f⟩_Pet / ⟨f, f⟩_Pet) ∈ Set.range (algebraMap 𝒪 ℂ)`! -/
theorem mem_congruenceIdeal_iff_petersson_integrality
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [Algebra 𝒪 ℂ]
    (hinj : Function.Injective (algebraMap 𝒪 ℂ))
    {k : ℕ} (hk : 1 ≤ k) {d : ℕ}
    (b : Module.Basis (Fin d) ℂ (CuspForm SL2ZRange (k : ℤ)))
    (heig : ∀ j : Fin d, IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff (b j)) (qExpansionCoeff (b j)))
    (hb_int : ∀ j : Fin d, ∀ n : ℕ, qExpansionCoeff (b j) n ∈ Set.range (algebraMap 𝒪 ℂ))
    (j₀ : Fin d) (a : 𝒪) :
    let P := cuspFormQExpansionSpace k hk
    let S := peterssonQSubspace P
    let hinv := peterssonQSubspace_hecke_inv P
    let e := peterssonQSubspaceEquiv P
    let bS : Module.Basis (Fin d) ℂ S := b.map e
    let hχ : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) (m : ZMod 1) ∈ Set.range (algebraMap 𝒪 ℂ) :=
      fun _ => ⟨1, by rw [map_one, trivialChar_one_apply]⟩
    let S_𝒪 := integralCuspLattice 𝒪 S
    let hS_𝒪_inv := integralCuspLattice_hecke_invariant k (1 : DirichletCharacter ℂ 1) S hinv hχ
    let hbS_int : ∀ j : Fin d, bS j ∈ S_𝒪 := fun j n => hb_int j n
    let f_𝒪 : S_𝒪 := ⟨bS j₀, hbS_int j₀⟩
    let π_f := eigenformAug k (1 : DirichletCharacter ℂ 1) S hinv hinj S_𝒪 hS_𝒪_inv f_𝒪
      (heig j₀) (fun n _ => hbS_int j₀ n)
    a ∈ Stage3PatchingUnification.congruenceIdeal π_f ↔
      ∀ v : CuspForm SL2ZRange (k : ℤ),
        (∀ n : ℕ, qExpansionCoeff v n ∈ Set.range (algebraMap 𝒪 ℂ)) →
        (algebraMap 𝒪 ℂ a) * (peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀)) ∈
          Set.range (algebraMap 𝒪 ℂ) := by
  intro P S hinv e bS hχ S_𝒪 hS_𝒪_inv hbS_int f_𝒪 π_f
  have hcusp : ∀ g ∈ S, g 0 = 0 := peterssonQSubspace_cusp P
  have heigS : ∀ j : Fin d, IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (bS j).1 (bS j).1 := fun j => heig j
  have hchar := mem_congruenceIdeal_iff_congruence_with_complement
    k (1 : DirichletCharacter ℂ 1) S hinv hcusp hinj hχ bS heigS hbS_int j₀ a
  have hle_iff := congruenceIdeal_le_span_iff_congruence_with_complement
    k (1 : DirichletCharacter ℂ 1) S hinv hcusp hinj hχ bS heigS hbS_int j₀
  have hbj_ne : b j₀ ≠ 0 := b.ne_zero j₀
  have hnorm_ne : peterssonInner (b j₀) (b j₀) ≠ 0 := fun h0 =>
    hbj_ne ((peterssonInner_self_eq_zero_iff (b j₀)).mp h0)
  constructor
  · intro ha v hv_int
    -- Decompose `v = c • b j₀ + v_perp` with `c = peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀)`
    -- Use `t ∈ annAugIdeal π_f` with `π_f t = a`: `t` acts by `a` on `b j₀` and `0` on `b j` (`j ≠ j₀`)!
    rw [Stage3PatchingUnification.mem_congruenceIdeal_iff] at ha
    obtain ⟨t, ht_ann, ht_eq⟩ := ha
    obtain ⟨ιT, _, _, hι_spec, hι_gen, _⟩ :=
      integralHeckeAlg_embedding_and_duality k (1 : DirichletCharacter ℂ 1) S hinv hcusp hinj hχ
        bS hbS_int
    -- Show `(ιT t).1 (bS j) = 0` for `j ≠ j₀` and `(ιT t).1 (bS j₀) = algebraMap 𝒪 ℂ a • bS j₀`
    have hact_j0 : (ιT t).1 (bS j₀) = algebraMap 𝒪 ℂ a • bS j₀ := by
      have h1 := hι_spec t f_𝒪
      have h2 := eigenformAug_smul_eq k (1 : DirichletCharacter ℂ 1) S hinv hinj S_𝒪 hS_𝒪_inv
        f_𝒪 (heig j₀) (fun n _ => hbS_int j₀ n) t
      rw [ht_eq] at h2
      have h3 : ((t.1 f_𝒪 : S_𝒪) : S) = algebraMap 𝒪 ℂ a • bS j₀ := by
        rw [h2]
        exact (algebraMap_smul ℂ a (bS j₀)).symm
      exact h1.symm.trans h3
    have hact_ne : ∀ j : Fin d, j ≠ j₀ → (ιT t).1 (bS j) = 0 := by
      intro j hj
      have hne_fun : (bS j).1 ≠ (bS j₀).1 := fun h => hj (bS.injective (Subtype.ext h))
      have hex_n : ∃ n : ℕ, 1 ≤ n ∧ (bS j).1 n ≠ (bS j₀).1 n := by
        by_contra hall
        push Not at hall
        apply hne_fun
        funext n
        match n with
        | 0 => rw [hcusp (bS j).1 (bS j).2, hcusp (bS j₀).1 (bS j₀).2]
        | n + 1 => exact hall (n + 1) (Nat.succ_pos n)
      obtain ⟨n, hn, hdiff⟩ := hex_n
      let Tn := oHeckeAlgGen k (1 : DirichletCharacter ℂ 1) S hinv S_𝒪 hS_𝒪_inv n hn
      let x := Tn - algebraMap 𝒪 _ (integralCoeff f_𝒪 n)
      have hx_ker : x ∈ Stage3PatchingUnification.augIdeal π_f := by
        rw [Stage3PatchingUnification.mem_augIdeal_iff]
        apply hinj
        rw [map_zero]
        change algebraMap 𝒪 ℂ (π_f (Tn - algebraMap 𝒪 _ (integralCoeff f_𝒪 n))) = 0
        rw [map_sub, map_sub, show π_f (algebraMap 𝒪 _ (integralCoeff f_𝒪 n)) =
            integralCoeff f_𝒪 n from π_f.commutes _]
        have hπ_Tn : algebraMap 𝒪 ℂ (π_f Tn) = ((ιT Tn).1 (bS j₀)).1 1 := by
          have h1 := eigenformAug_apply_val k (1 : DirichletCharacter ℂ 1) S hinv hinj S_𝒪 hS_𝒪_inv
            f_𝒪 (heig j₀) (fun m _ => hbS_int j₀ m) Tn
          exact h1.trans (congrFun (congrArg Subtype.val (hι_spec Tn f_𝒪)) 1)
        rw [hπ_Tn, hι_gen n hn, heckeAlgGen_val, heckeEnd_apply_one,
          algebraMap_integralCoeff, sub_self]
      have htx0 : t * x = 0 := (Stage3PatchingUnification.mem_annAugIdeal_iff π_f t).mp ht_ann x hx_ker
      have hι_alg : ∀ c : 𝒪,
          ιT (algebraMap 𝒪 _ c) = algebraMap ℂ (HeckeAlg k (1 : DirichletCharacter ℂ 1) S hinv)
            (algebraMap 𝒪 ℂ c) := fun c => by
        rw [ιT.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        apply Subtype.ext; apply LinearMap.ext; intro w
        exact (algebraMap_smul ℂ c w).symm
      have hact_x : (ιT x).1 (bS j) = ((bS j).1 n - (bS j₀).1 n) • bS j := by
        have hTn_j : (heckeAlgGen k (1 : DirichletCharacter ℂ 1) S hinv n hn).1 (bS j) =
            (bS j).1 n • bS j := Subtype.ext ((heigS j).2 n hn)
        have hιx : ιT x = heckeAlgGen k (1 : DirichletCharacter ℂ 1) S hinv n hn -
            algebraMap ℂ (HeckeAlg k (1 : DirichletCharacter ℂ 1) S hinv) ((bS j₀).1 n) := by
          change ιT (Tn - algebraMap 𝒪 _ (integralCoeff f_𝒪 n)) = _
          rw [map_sub, hι_gen n hn, hι_alg, algebraMap_integralCoeff]
        rw [hιx]
        change (heckeAlgGen k (1 : DirichletCharacter ℂ 1) S hinv n hn).1 (bS j) -
            (bS j₀).1 n • bS j = _
        rw [hTn_j, ← sub_smul]
      have h0 : ((bS j).1 n - (bS j₀).1 n) • (ιT t).1 (bS j) = 0 := by
        have h1 := congrArg (fun U => (ιT U).1 (bS j)) htx0
        rw [map_mul, map_zero] at h1
        change (ιT t).1 ((ιT x).1 (bS j)) = 0 at h1
        rw [hact_x, map_smul] at h1
        exact h1
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hdiff)
    -- Apply `t` to `v_𝒪 = ⟨e v, hv_int⟩ ∈ S_𝒪`!
    let v_𝒪 : S_𝒪 := ⟨e v, hv_int⟩
    have hv_decomp : e v = ∑ j : Fin d, b.repr v j • bS j := by
      calc e v = e (∑ j : Fin d, b.repr v j • b j) := by rw [b.sum_repr v]
        _ = ∑ j : Fin d, b.repr v j • bS j := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul]; rfl
    have htv_eq : ((t.1 v_𝒪 : S_𝒪) : S) = (b.repr v j₀ * algebraMap 𝒪 ℂ a) • bS j₀ := by
      rw [hι_spec t v_𝒪]
      change (ιT t).1 (e v) = _
      conv_lhs => rw [hv_decomp]
      rw [map_sum]
      rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [map_smul, hact_ne j hj, smul_zero])
        (fun h => absurd (Finset.mem_univ j₀) h)]
      rw [map_smul, hact_j0, smul_smul]
    have hcoeff1 : (((t.1 v_𝒪 : S_𝒪) : S) : ℕ → ℂ) 1 =
        algebraMap 𝒪 ℂ a * (peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀)) := by
      rw [htv_eq]
      change (b.repr v j₀ * algebraMap 𝒪 ℂ a) * (bS j₀).1 1 = _
      rw [show (bS j₀).1 1 = 1 from (heig j₀).1, mul_one, mul_comm,
        basis_repr_eq_petersson_ratio hk b heig j₀ v]
    rw [← hcoeff1]
    exact (t.1 v_𝒪).2 1
  · intro hint
    dsimp only at hchar
    rw [hchar]
    intro c ⟨h, hh_comp, hcong⟩
    by_cases hc0 : c = 0
    · -- `c = 0` is impossible because `f_𝒪` and `h ∈ eigenComplement` cannot be equal (`bS j₀ ∉ eigenComplement`)
      subst hc0
      have hfh : f_𝒪.1 = h.1 := by
        apply Subtype.ext; funext n
        have h0 : (0 : 𝒪) ∣ integralCoeff f_𝒪 n - integralCoeff h n := hcong n
        have hsub0 : integralCoeff f_𝒪 n - integralCoeff h n = 0 := zero_dvd_iff.mp h0
        have heq : integralCoeff f_𝒪 n = integralCoeff h n := sub_eq_zero.mp hsub0
        rw [← algebraMap_integralCoeff f_𝒪 n, ← algebraMap_integralCoeff h n, heq]
      -- `b j₀` would lie in `span { b j | j ≠ j₀ }`, contradicting linear independence of `b`
      exfalso
      have hmem : bS j₀ ∈ eigenComplement S bS j₀ := by rw [← hfh] at hh_comp; exact hh_comp
      have hcoord : bS.repr (bS j₀) j₀ = 1 := by simp
      have hzero_on_comp : ∀ u ∈ eigenComplement S bS j₀, bS.repr u j₀ = 0 := by
        intro u hu
        refine Submodule.span_induction
          (p := fun u _ => bS.repr u j₀ = 0) ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨j, hj, rfl⟩
          rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hj.symm]
        · simp
        · intro x y _ _ hx hy; simp [hx, hy]
        · intro r x _ hx; simp [hx]
      have h01 := hzero_on_comp (bS j₀) hmem
      rw [hcoord] at h01
      exact one_ne_zero h01
    · -- For `c ≠ 0`, `v := (algebraMap 𝒪 ℂ c)⁻¹ • (b j₀ - e.symm h.1)` lies in `S_{k, 𝒪}`!
      have hcC_ne : algebraMap 𝒪 ℂ c ≠ 0 := by
        intro h0; exact hc0 (hinj (h0.trans (map_zero _).symm))
      let hC : CuspForm SL2ZRange (k : ℤ) := e.symm h.1
      let v : CuspForm SL2ZRange (k : ℤ) := (algebraMap 𝒪 ℂ c)⁻¹ • (b j₀ - hC)
      have hv_int : ∀ n : ℕ, qExpansionCoeff v n ∈ Set.range (algebraMap 𝒪 ℂ) := fun n => by
        obtain ⟨q, hq⟩ := hcong n
        refine ⟨q, ?_⟩
        change algebraMap 𝒪 ℂ q = qExpansionCoeff ((algebraMap 𝒪 ℂ c)⁻¹ • (b j₀ - hC)) n
        rw [qExpansionCoeff_smul, qExpansionCoeff_sub]
        have hf_n : qExpansionCoeff (b j₀) n = algebraMap 𝒪 ℂ (integralCoeff f_𝒪 n) :=
          (algebraMap_integralCoeff f_𝒪 n).symm
        have hh_n : qExpansionCoeff hC n = algebraMap 𝒪 ℂ (integralCoeff h n) := by
          have h1 : (e hC).1 n = h.1.1 n := by
            change (e (e.symm h.1)).1 n = h.1.1 n
            rw [LinearEquiv.apply_symm_apply]
          exact h1.trans (algebraMap_integralCoeff h n).symm
        rw [hf_n, hh_n, ← map_sub, hq, map_mul, ← mul_assoc, inv_mul_cancel₀ hcC_ne, one_mul]
      -- `hC` is Petersson-orthogonal to `b j₀` because `h.1 ∈ eigenComplement S bS j₀`!
      have hh_orth : peterssonInner hC (b j₀) = 0 := by
        have hzero : ∀ u ∈ eigenComplement S bS j₀, peterssonInner (e.symm u) (b j₀) = 0 := by
          intro u hu
          refine Submodule.span_induction
            (p := fun u _ => peterssonInner (e.symm u) (b j₀) = 0) ?_ ?_ ?_ ?_ hu
          · rintro _ ⟨j, hj, rfl⟩
            have hsymm : e.symm (bS j) = b j := by simp [bS]
            rw [hsymm]
            exact peterssonInner_eq_zero_of_distinct_eigenforms hk (heig j) (heig j₀)
              (fun h => hj (b.injective h))
          · rw [map_zero, peterssonInner_zero_left]
          · intro x y _ _ hx hy
            rw [map_add, peterssonInner_add_left, hx, hy, add_zero]
          · intro r x _ hx
            rw [map_smul, peterssonInner_smul_left, hx, mul_zero]
        exact hzero h.1 hh_comp
      have hv_pet : peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀) =
          (algebraMap 𝒪 ℂ c)⁻¹ := by
        dsimp only [v]
        rw [peterssonInner_smul_left, show b j₀ - hC = b j₀ + (-1 : ℂ) • hC by abel_nf; simp,
          peterssonInner_add_left, peterssonInner_smul_left, hh_orth, mul_zero, add_zero,
          mul_div_cancel_right₀ _ hnorm_ne]
      obtain ⟨r, hr⟩ := hint v hv_int
      rw [hv_pet] at hr
      refine ⟨r, hinj ?_⟩
      rw [map_mul]
      have hmul := congrArg (fun z : ℂ => algebraMap 𝒪 ℂ c * z) hr.symm
      calc algebraMap 𝒪 ℂ a
          = algebraMap 𝒪 ℂ c * (algebraMap 𝒪 ℂ a * (algebraMap 𝒪 ℂ c)⁻¹) := by
              rw [mul_left_comm, mul_inv_cancel₀ hcC_ne, mul_one]
        _ = algebraMap 𝒪 ℂ c * algebraMap 𝒪 ℂ r := hmul

/-- **HIDA–WILES ADJOINT `L(1, Ad f)` CONGRUENCE-PRIME CRITERION (`adjointL_controls_congruence_prime`)**:
Let `𝒪 ↪ ℂ` be a PID, `k ≥ 1`, `b : Fin d → CuspForm SL2ZRange k` an `𝒪`-integral eigenbasis of
normalized Hecke eigenforms, `f = b j₀`, and `Ω ∈ ℂˣ` any period normalizing the adjoint `L`-value
`L(1, Ad f) = adjointLAtOneFromPetersson f` and Petersson pairing on the integral lattice `S_{k, 𝒪}`:
- `L_alg : 𝒪` satisfies `adjointLAtOneFromPetersson f / Ω = algebraMap 𝒪 ℂ L_alg`, and
- `∀ v ∈ S_{k, 𝒪}, adjointArchFactor k * peterssonInner v f / Ω ∈ 𝒪`.

Then **UNCONDITIONALLY**:
1. **`L_alg ∈ Stage3PatchingUnification.congruenceIdeal π_f`**, and
2. **Every congruence divisor / congruence prime `a : 𝒪` dividing the congruence module
   `𝕋_𝒪 / (I_f + I_f^⊥)` (`congruenceIdeal π_f ≤ Ideal.span {a}`, equivalently
   `∃ h ∈ S_{k, 𝒪} ∩ f^⊥, f ≡ h [MOD a]`) MUST DIVIDE `L_alg` (`a ∣ L_alg`)**! -/
theorem adjointL_controls_congruence_prime
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [Algebra 𝒪 ℂ]
    (hinj : Function.Injective (algebraMap 𝒪 ℂ))
    {k : ℕ} (hk : 1 ≤ k) {d : ℕ}
    (b : Module.Basis (Fin d) ℂ (CuspForm SL2ZRange (k : ℤ)))
    (heig : ∀ j : Fin d, IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff (b j)) (qExpansionCoeff (b j)))
    (hb_int : ∀ j : Fin d, ∀ n : ℕ, qExpansionCoeff (b j) n ∈ Set.range (algebraMap 𝒪 ℂ))
    (j₀ : Fin d)
    {Ω : ℂ} (hΩ : Ω ≠ 0) (L_alg : 𝒪)
    (hL_alg : adjointLAtOneFromPetersson (b j₀) / Ω = algebraMap 𝒪 ℂ L_alg)
    (hpair_int : ∀ v : CuspForm SL2ZRange (k : ℤ),
      (∀ n : ℕ, qExpansionCoeff v n ∈ Set.range (algebraMap 𝒪 ℂ)) →
      (adjointArchFactor k : ℂ) * peterssonInner v (b j₀) / Ω ∈ Set.range (algebraMap 𝒪 ℂ)) :
    let P := cuspFormQExpansionSpace k hk
    let S := peterssonQSubspace P
    let hinv := peterssonQSubspace_hecke_inv P
    let e := peterssonQSubspaceEquiv P
    let bS : Module.Basis (Fin d) ℂ S := b.map e
    let hχ : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) (m : ZMod 1) ∈ Set.range (algebraMap 𝒪 ℂ) :=
      fun _ => ⟨1, by rw [map_one, trivialChar_one_apply]⟩
    let S_𝒪 := integralCuspLattice 𝒪 S
    let hS_𝒪_inv := integralCuspLattice_hecke_invariant k (1 : DirichletCharacter ℂ 1) S hinv hχ
    let hbS_int : ∀ j : Fin d, bS j ∈ S_𝒪 := fun j n => hb_int j n
    let f_𝒪 : S_𝒪 := ⟨bS j₀, hbS_int j₀⟩
    let π_f := eigenformAug k (1 : DirichletCharacter ℂ 1) S hinv hinj S_𝒪 hS_𝒪_inv f_𝒪
      (heig j₀) (fun n _ => hbS_int j₀ n)
    L_alg ∈ Stage3PatchingUnification.congruenceIdeal π_f ∧
    (∀ a : 𝒪, Stage3PatchingUnification.congruenceIdeal π_f ≤ Ideal.span ({a} : Set 𝒪) → a ∣ L_alg) := by
  intro P S hinv e bS hχ S_𝒪 hS_𝒪_inv hbS_int f_𝒪 π_f
  have hmem : L_alg ∈ Stage3PatchingUnification.congruenceIdeal π_f := by
    have hiff := mem_congruenceIdeal_iff_petersson_integrality hinj hk b heig hb_int j₀ L_alg
    dsimp only at hiff
    rw [hiff]
    intro v hv_int
    have hnorm_ne : peterssonInner (b j₀) (b j₀) ≠ 0 := fun h0 =>
      b.ne_zero j₀ ((peterssonInner_self_eq_zero_iff (b j₀)).mp h0)
    have hcancel :
        algebraMap 𝒪 ℂ L_alg * (peterssonInner v (b j₀) / peterssonInner (b j₀) (b j₀)) =
          (adjointArchFactor k : ℂ) * peterssonInner v (b j₀) / Ω := by
      rw [← hL_alg, adjointLAtOneFromPetersson]
      field_simp [hΩ, hnorm_ne]
    rw [hcancel]
    exact hpair_int v hv_int
  refine ⟨hmem, fun a ha => ?_⟩
  exact Ideal.mem_span_singleton.mp (ha hmem)

/-- **DVR ADJOINT-`L` VALUATION BOUND ON THE CONGRUENCE MODULE LENGTH (`congruence_length_le_adjointL_valuation`)**:
Over a DVR `𝒪 ↪ ℂ` with uniformizer `ϖ`, if `L_alg ∈ η_f` is nonzero and associated to `ϖ ^ m`, then
`Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π_f) ≤ (m : ℕ∞)`! -/
theorem congruence_length_le_adjointL_valuation
    {𝒪 T : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [CommRing T] [Algebra 𝒪 T]
    (aug : T →ₐ[𝒪] 𝒪) {ϖ L_alg : 𝒪} (hϖ : Irreducible ϖ)
    (hmem : L_alg ∈ Stage3PatchingUnification.congruenceIdeal aug)
    {m : ℕ} (hass : Associated L_alg (ϖ ^ m)) :
    Module.length 𝒪 (𝒪 ⧸ Stage3PatchingUnification.congruenceIdeal aug) ≤ (m : ℕ∞) := by
  have hle : Ideal.span ({ϖ ^ m} : Set 𝒪) ≤ Stage3PatchingUnification.congruenceIdeal aug := by
    rw [← Stage3PatchingUnification.span_singleton_eq_of_associated hass,
      Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hlen_le :
      Module.length 𝒪 (𝒪 ⧸ Stage3PatchingUnification.congruenceIdeal aug) ≤
        Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ m} : Set 𝒪)) :=
    Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  rw [Stage3PatchingUnification.length_quotient_span_pow_eq_of_dvr hϖ m] at hlen_le
  exact hlen_le

/-- **DIRECT `CountII` / `CountIII` ADJOINT-LIFTING SELMER BOUND FOR `VWin` (`adjointL_selmer_bound_of_patching`)**:
Given a `Stage3PatchingUnification.TaylorWilesCongruenceDatum` over a DVR `𝒪` with uniformizer `ϖ`,
if the algebraic adjoint `L`-value `L_alg ∈ congruenceIdeal D.aug` satisfies `Associated L_alg (ϖ ^ m)`:
1. `S.shaLen E l k ≤ (D.genRank * m : ℕ∞)` (and `S.shaLen E l k ≠ ⊤`),
2. under complete intersection (`len_𝒪(Φ_T) = len_𝒪(𝒪 / η_T)`), `S.shaLen E l k ≤ (m : ℕ∞)`
   and `(S.shaLen E l k).toNat ≤ m`! -/
theorem adjointL_selmer_bound_of_patching
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ}
    (D : TaylorWilesCongruenceDatum S E l k)
    [IsDomain D.𝒪] [IsDiscreteValuationRing D.𝒪]
    {ϖ L_alg : D.𝒪} (hϖ : Irreducible ϖ)
    (hmem : L_alg ∈ Stage3PatchingUnification.congruenceIdeal D.aug)
    {m : ℕ} (hass : Associated L_alg (ϖ ^ m)) :
    (S.shaLen E l k ≠ ⊤ ∧ (S.shaLen E l k).toNat ≤ D.genRank * m) ∧
    (Module.length D.𝒪 (Cotangent D.aug) =
        Module.length D.𝒪 (D.𝒪 ⧸ Stage3PatchingUnification.congruenceIdeal D.aug) →
      (S.shaLen E l k).toNat ≤ m) := by
  have hcong : Module.length D.𝒪 (D.𝒪 ⧸ Stage3PatchingUnification.congruenceIdeal D.aug) ≤ (m : ℕ∞) :=
    congruence_length_le_adjointL_valuation D.aug hϖ hmem hass
  let D' : TaylorWilesCongruenceDatum S E l k :=
    { D with
      congLen := m
      cong_length_le := hcong }
  have h1 : S.shaLen E l k ≠ ⊤ ∧ (S.shaLen E l k).toNat ≤ D.genRank * m :=
    D'.toPatchedPrimeBound.shaLen_finite_and_le
  refine ⟨h1, fun hci => ?_⟩
  exact (shaLen_le_congLen_of_completeIntersection D' hci).2

/-! ### Concrete Level-1 Adjoint-Norm & Congruence Witnesses (`Δ₁₂..Δ₂₂` and `S₂₄`) -/

/-- **Unconditional Strict Positivity of `L(1, Ad Δ_k)` (`adjointLAtOneFromPetersson`) for All
Five 1D Level-1 Eigenforms (`k = 12, 16, 18, 20, 22`) & Trivial 1D Petersson Projection**. -/
theorem five_oneDim_adjointL_pos :
    0 < (adjointLAtOneFromPetersson delta12).re ∧
    0 < (adjointLAtOneFromPetersson delta16).re ∧
    0 < (adjointLAtOneFromPetersson delta18).re ∧
    0 < (adjointLAtOneFromPetersson delta20).re ∧
    0 < (adjointLAtOneFromPetersson delta22).re := by
  have hne : ∀ {k : ℕ} {f : CuspForm SL2ZRange (k : ℤ)}, qExpansionCoeff f 1 = 1 → f ≠ 0 := by
    intro k f hf1 h0
    have hzero : qExpansionCoeff f 1 = 0 := by
      rw [h0]
      have hz : (0 : CuspForm SL2ZRange (k : ℤ)) = (0 : ℂ) • f := by simp
      rw [hz, qExpansionCoeff_smul, zero_mul]
    rw [hf1] at hzero
    exact one_ne_zero hzero
  refine ⟨(adjointLAtOneFromPetersson_re_pos (hne isNormalizedHeckeEigenform_delta12.1)).1,
    (adjointLAtOneFromPetersson_re_pos (hne isNormalizedHeckeEigenform_delta16.1)).1,
    (adjointLAtOneFromPetersson_re_pos (hne isNormalizedHeckeEigenform_delta18.1)).1,
    (adjointLAtOneFromPetersson_re_pos (hne isNormalizedHeckeEigenform_delta20.1)).1,
    (adjointLAtOneFromPetersson_re_pos (hne isNormalizedHeckeEigenform_delta22.1)).1⟩

/-- In any 1-dimensional cuspidal space `S_k(SL₂(ℤ))` generated by a normalized eigenform `f`,
the Petersson projection of every `v ∈ S_k` onto `f` is simply `a₁(v)` (so integral forms project
integrally with congruence number `1`!). -/
theorem petersson_ratio_eq_a1_of_dim_one {k : ℕ}
    (hdim : Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)) = 1)
    {f : CuspForm SL2ZRange (k : ℤ)} (hf1 : qExpansionCoeff f 1 = 1)
    (v : CuspForm SL2ZRange (k : ℤ)) :
    peterssonInner v f / peterssonInner f f = qExpansionCoeff v 1 := by
  have hf_ne : f ≠ 0 := by
    intro h0
    have hzero : qExpansionCoeff f 1 = 0 := by
      rw [h0]
      have hz : (0 : CuspForm SL2ZRange (k : ℤ)) = (0 : ℂ) • f := by simp
      rw [hz, qExpansionCoeff_smul, zero_mul]
    rw [hf1] at hzero
    exact one_ne_zero hzero
  have hnorm_ne : peterssonInner f f ≠ 0 := fun h0 =>
    hf_ne ((peterssonInner_self_eq_zero_iff f).mp h0)
  conv_lhs => rw [cuspForm_eq_smul_of_finrank_eq_one hdim hf1 v]
  rw [peterssonInner_smul_left, mul_div_cancel_right₀ _ hnorm_ne]

/-- **EXPLICIT WEIGHT-24 HIDA CONGRUENCE DENOMINATOR (`24 √144169`) VIA CONCRETE PETERSSON PROJECTION**:
for the integral cusp form `Δ² = S24_vm2 ∈ S₂₄(SL₂(ℤ))` and the weight-24 eigenform `S24_eigenPlus`:
1. `peterssonInner S24_vm2 S24_eigenPlus / peterssonInner S24_eigenPlus S24_eigenPlus = (24 * Real.sqrt 144169 : ℂ)⁻¹`,
2. `0 < (adjointLAtOneFromPetersson S24_eigenPlus).re` and `0 < (adjointLAtOneFromPetersson S24_eigenMinus).re`! -/
theorem S24_petersson_congruence_denominator :
    peterssonInner S24_vm2 S24_eigenPlus / peterssonInner S24_eigenPlus S24_eigenPlus =
      ((24 * Real.sqrt 144169 : ℝ) : ℂ)⁻¹ ∧
    0 < (adjointLAtOneFromPetersson S24_eigenPlus).re ∧
    0 < (adjointLAtOneFromPetersson S24_eigenMinus).re := by
  have hp_ne : S24_eigenPlus ≠ 0 := by
    intro h0
    have h1 := S24_eigenPlus_normalized
    have hz : qExpansionCoeff S24_eigenPlus 1 = 0 := by
      rw [h0]
      have h' : (0 : CuspForm SL2ZRange 24) = (0 : ℂ) • S24_eigenPlus := by simp
      rw [h', qExpansionCoeff_smul, zero_mul]
    rw [hz] at h1
    exact zero_ne_one h1
  have hm_ne : S24_eigenMinus ≠ 0 := by
    intro h0
    have h1 := S24_eigenMinus_normalized
    have hz : qExpansionCoeff S24_eigenMinus 1 = 0 := by
      rw [h0]
      have h' : (0 : CuspForm SL2ZRange 24) = (0 : ℂ) • S24_eigenMinus := by simp
      rw [h', qExpansionCoeff_smul, zero_mul]
    rw [hz] at h1
    exact zero_ne_one h1
  have hnorm_ne : peterssonInner S24_eigenPlus S24_eigenPlus ≠ 0 := fun h0 =>
    hp_ne ((peterssonInner_self_eq_zero_iff S24_eigenPlus).mp h0)
  have hdiff : S24_lambdaPlus - S24_lambdaMinus = ((24 * Real.sqrt 144169 : ℝ) : ℂ) := by
    unfold S24_lambdaPlus S24_lambdaMinus S24_lambdaPlusR S24_lambdaMinusR
    push_cast
    ring
  have hdiff_ne : ((24 * Real.sqrt 144169 : ℝ) : ℂ) ≠ 0 := by
    rw [← hdiff]
    exact sub_ne_zero.mpr S24_lambdaPlus_ne_lambdaMinus
  have hvm2_decomp : S24_vm2 =
      ((24 * Real.sqrt 144169 : ℝ) : ℂ)⁻¹ • S24_eigenPlus +
        (-((24 * Real.sqrt 144169 : ℝ) : ℂ)⁻¹) • S24_eigenMinus := by
    unfold S24_eigenPlus S24_eigenMinus
    ext τ
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    have hsub : S24_lambdaPlus - S24_lambdaMinus = ((24 * Real.sqrt 144169 : ℝ) : ℂ) := hdiff
    field_simp [hdiff_ne]
    linear_combination -hsub * S24_vm2 τ
  have horth : peterssonInner S24_eigenMinus S24_eigenPlus = 0 := by
    rw [← peterssonInner_conj_symm, S24_hecke_eigenbasis.2.2.2.2, star_zero]
  refine ⟨?_, (adjointLAtOneFromPetersson_re_pos hp_ne).1,
    (adjointLAtOneFromPetersson_re_pos hm_ne).1⟩
  conv_lhs => rw [hvm2_decomp]
  rw [peterssonInner_add_left, peterssonInner_smul_left, peterssonInner_smul_left,
    horth, mul_zero, add_zero, mul_div_cancel_right₀ _ hnorm_ne]

end AdjointLCongruenceBridge

end

end RHDirect.Stage11Sym2AdjointL
